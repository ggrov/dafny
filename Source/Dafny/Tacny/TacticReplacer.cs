using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.IO;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

namespace Microsoft.Dafny.Tacny {

  internal static class RefactoringUtil {
    public static DefaultClassDecl GetTld(Program p) =>
      (from tld in p?.DefaultModuleDef.TopLevelDecls
       let test = tld as DefaultClassDecl
       where test != null
       select test).FirstOrDefault();
    
    public static TacticReplaceStatus GetMemberFromPosition(DefaultClassDecl tld, int position, out MemberDecl member) {
      Contract.Requires(tld != null);
      member = GetMemberFromPosition(tld, position);
      return member == null ? TacticReplaceStatus.NoTactic : TacticReplaceStatus.Success;
    }

    public static MemberDecl GetMemberFromPosition(DefaultClassDecl tld, int position) =>
      (from m in tld.Members where m.tok.pos <= position && position <= m.BodyEndTok.pos + 1 select m).FirstOrDefault();

    public static string StripExtraContentFromExpanded(string expandedTactic) {
      var words = new[] { "ghost ", "lemma ", "method ", "function ", "tactic " };
      return words.Aggregate(expandedTactic, RazeFringe);
    }

    public static string RazeFringe(string body, string fringe) {
      Contract.Requires(body.Length > fringe.Length);
      return body.Substring(0, fringe.Length) == fringe ? body.Substring(fringe.Length) : body;
    }

    public static bool TokenEquals(Microsoft.Boogie.IToken t, Microsoft.Boogie.IToken u) {
      return t.IsValid == u.IsValid && t.col == u.col && t.filename == u.filename
             && t.kind == u.kind && t.line == u.line && t.pos == u.pos && t.val == u.val;
    }

    public static TacticReplaceStatus GetTacticCallAtPosition(Method m, int p, out Tuple<Statement, int, int> us) {
      try {
        us = (from stmt in m?.Body?.Body
              let u = stmt as UpdateStmt
              let rhs = u?.Rhss[0] as ExprRhs
              let expr = rhs?.Expr as ApplySuffix
              let name = expr?.Lhs as NameSegment
              where name != null
              let start = expr.tok.pos - name.Name.Length
              let end = stmt.EndTok.pos + 1
              where start <= p && p <= end
              select new Tuple<Statement, int, int>(stmt, start, end))
          .FirstOrDefault();
      } catch (ArgumentNullException) {
        us = null;
        return TacticReplaceStatus.NoTactic;
      }

      if (us == null) {
        us = (from stmt in m?.Body?.Body
              where stmt is InlineTacticBlockStmt
              let start = stmt.Tok.pos
              let end = stmt.EndTok.pos + 1
              where start <= p && p <= end
              select new Tuple<Statement, int, int>(stmt, start, end))
          .FirstOrDefault();
      }

      return us != null ? TacticReplaceStatus.Success : TacticReplaceStatus.NoTactic;
    }

    public static IEnumerator<Tuple<Statement, int, int>> GetTacticCallsInMember(Method m) {
      if (m?.Body.Body == null) yield break;
      foreach (var stmt in m.Body.Body) {
        if (!(stmt is InlineTacticBlockStmt) &&
          ((stmt as UpdateStmt) == null || (stmt as UpdateStmt).Lhss.Count != 0 || !(stmt as UpdateStmt).IsGhost))
          continue;
        if (GetTacticCallAtPosition(m, stmt.Tok.pos, out Tuple<Statement, int, int> current) != TacticReplaceStatus.Success) continue;
        yield return current;
      }
    }
  }

  public enum TacticReplaceStatus {
    Success,
    NoTactic,
    NotResolved,
    TranslatorFail
  }

  public class TacticReplacer{
    private readonly DefaultClassDecl _tld;
    private readonly IEnumerator<MemberDecl> _tldMembers;
    private MemberDecl _member;
    private Tuple<Statement, int, int> _tacticCall;
    private IEnumerator<Tuple<Statement, int, int>> _tacticCalls;

    public int MemberBodyStart => _member.BodyStartTok.pos;
    public int MemberNameStart => _member.tok.pos;
    public string MemberName => _member.CompileName;
    public bool MemberReady => _member != null && _member.CallsTactic != 0;

    public string GetActiveTacticName() {
      if (_tacticCall == null) return null;
      if (_tacticCall.Item1 is UpdateStmt) {
        var rightHandSide = (_tacticCall.Item1 as UpdateStmt).Rhss[0] as ExprRhs;
        var suffix = rightHandSide?.Expr as ApplySuffix;
        var nameseg = suffix?.Lhs as NameSegment;
        return nameseg?.Name;
      } else return "inline tactic";
    }

    public readonly TacticReplaceStatus LoadStatus;
    
    public TacticReplacer(Program p, int position = -1) {
      _tld = RefactoringUtil.GetTld(p);
      _tldMembers = _tld?.Members.GetEnumerator();
      LoadStatus = _tld != null ? TacticReplaceStatus.Success : TacticReplaceStatus.NotResolved;
      if (LoadStatus != TacticReplaceStatus.Success) return;
      if (position == -1) return;
      SetMember(position);
      SetTacticCall(position);
    }

    public TacticReplaceStatus SetMember(int position) {
      var status = RefactoringUtil.GetMemberFromPosition(_tld, position, out _member);
      _tacticCalls = RefactoringUtil.GetTacticCallsInMember(_member as Method);
      return status;
    }

    public TacticReplaceStatus SetTacticCall(int position) {
      return RefactoringUtil.GetTacticCallAtPosition(_member as Method, position, out _tacticCall);
    }

    public bool NextMemberInTld() {
      var isMore = _tldMembers.MoveNext();
      if (!isMore) return false;
      _member = _tldMembers.Current;
      _tacticCalls = RefactoringUtil.GetTacticCallsInMember(_member as Method);
      return true;
    }

    public bool NextTacticCallInMember() {
      var isMore = _tacticCalls.MoveNext();
      if (isMore) _tacticCall = _tacticCalls.Current;
      return isMore;
    }
    
    public TacticReplaceStatus ExpandSingleTacticCall(int tacticCallPos, out string expanded) {
      expanded = "";
      var status = RefactoringUtil.GetTacticCallAtPosition(_member as Method, tacticCallPos, out Tuple<Statement, int, int> us);
      return status == TacticReplaceStatus.Success ? ExpandSingleTacticCall(us.Item1, out expanded) : status;
    }

    private TacticReplaceStatus ExpandSingleTacticCall(Statement us, out string expanded) {
      expanded = "";
      var l = Microsoft.Dafny.Tacny.TacnyDriver.GetTacticResultList();
      var result = l.FirstOrDefault(pair => RefactoringUtil.TokenEquals(pair.Key, us.Tok));
      if (result.Value == null) return TacticReplaceStatus.NoTactic;
      var sr = new StringWriter();
      var printer = new Printer(sr);
      foreach (var stmt in result.Value) {
        printer.PrintStatement(stmt, 4);
        sr.Write("\n");
      }
      expanded = sr.ToString();
      return !string.IsNullOrEmpty(expanded) ? TacticReplaceStatus.Success : TacticReplaceStatus.NoTactic;
    }

    public TacticReplaceStatus ExpandTacticByMember(out string expandedTactic) {
      expandedTactic = "";
      var l = Microsoft.Dafny.Tacny.TacnyDriver.GetTacticResultList();
      var x = _member as Method;
      if (x == null) return TacticReplaceStatus.NoTactic;
      var sr = new StringWriter();
      var printer = new Printer(sr);
      var hasTactic = false;
      foreach (var stmt in x.Body.SubStatements) {
        var result = l.FirstOrDefault(pair => RefactoringUtil.TokenEquals(pair.Key, stmt.Tok));
        if (result.Key == null) {
          printer.PrintStatement(stmt, 0);
        } else {
          hasTactic = true;
          result.Value.ForEach(foundStmt => printer.PrintStatement(foundStmt, 0));
        }
        sr.Write("\n");
      }
      expandedTactic = hasTactic ? sr.ToString() : "";
      return TacticReplaceStatus.Success;
    }
  }
}
