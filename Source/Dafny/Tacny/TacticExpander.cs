using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.IO;
using System.Linq;
using System.Runtime.Serialization;
using System.Text;
using System.Threading.Tasks;

namespace Microsoft.Dafny.Tacny {

  internal class NoTacticException : Exception { }
  internal class NotResolvedException : Exception { }
  
  /**
    * Represent the possible outcomes of a tactic replacement
    */
  public enum TacticExpandStatus {
    Success,
    NoTactic,
    NotResolved
  }

  /**
   * Represent a call to a tactic
   **/
  internal struct TacticCall {
    public readonly Statement statement;
    public readonly int startPos;
    public readonly int endPos;

    public TacticCall(Statement statement, int startPos, int endPos) {
      this.statement = statement;
      this.startPos = startPos;
      this.endPos = endPos;
    }
  }

  /**
   * Represent a Replacement in source text of a tactic call
   */
  [DataContract]
  public class TacticExpansion {
    [DataMember]
    public string expansion;
    [DataMember]
    public string status;
    [DataMember]
    public int startPos;
    [DataMember]
    public int endPos;

    public TacticExpansion(string expansion, TacticExpandStatus status, int startPos, int endPos) {
      this.expansion = expansion;
      this.status = StatusToString(status);
      this.startPos = startPos;
      this.endPos = endPos;
    }

    public TacticExpansion(TacticExpandStatus status) {
      this.expansion = "";
      this.status = StatusToString(status);
      this.startPos = -1;
      this.endPos = -1;
    }

    /**
     * Convert the enum to a string, for interoperability
     */
    private static string StatusToString(TacticExpandStatus status) {
      switch (status) {
        case TacticExpandStatus.Success:
        return "SUCCESS";
        case TacticExpandStatus.NoTactic:
        return "NO_TACTIC";
        case TacticExpandStatus.NotResolved:
        return "UNRESOLVED";
      }
      throw new Exception("Invalid StatusToString call");
    }
  }

  /**
   * Tactic Expander
   */
  public class TacticExpander {
    /**
     * Expand a single call in the program at the position
     */
    public static TacticExpansion Expand(Program program, int position) {
      try {
        var tr = new Microsoft.Dafny.Tacny.TacticExpander(program);
        tr.SetExpansionPosition(position);
        return tr.ExpandCurrentTacticCall();
      } catch (NoTacticException) {
        return new TacticExpansion(TacticExpandStatus.NoTactic);
      }
    }

    /**
     * Expand all calls in the program
     */
    public static List<TacticExpansion> ExpandAll(Program program) {
      List<TacticExpansion> expansions = new List<TacticExpansion>();
      var tr = new Microsoft.Dafny.Tacny.TacticExpander(program);
      try {
        while (tr.NextMemberInTld()) {
          while (tr.NextTacticCallInMember()) {
            try {
              expansions.Add(tr.ExpandTacticsInCurrentMember());
            } catch (NoTacticException) { }
          }
        }
      } catch (NotResolvedException) {
        return new List<TacticExpansion> {
          new TacticExpansion(TacticExpandStatus.NotResolved)
        };
      }
      return expansions;
    }
    
    private readonly DefaultClassDecl _tld;
    private readonly IEnumerator<MemberDecl> _tldMembers;
    private MemberDecl _member;
    private TacticCall _tacticCall;
    private IEnumerator<TacticCall> _tacticCalls;
    
    public TacticExpander(Program p) {
      _tld = GetTld(p);
      if (_tld == null) throw new NotResolvedException();
      _tldMembers = _tld.Members.GetEnumerator();
    }

    public void SetExpansionPosition(int position) {
      SetMember(position);
      SetTacticCall(position);
    }

    private void SetMember(int position) {
      var member = GetMemberFromPosition(_tld, position);
      _member = member ?? throw new NoTacticException();
      _tacticCalls = GetTacticCallsInMember(_member as Method);
    }

    private void SetTacticCall(int position) {
      var call = GetTacticCallAtPosition(_member as Method, position);
      if(call.statement == null) {
        throw new NoTacticException();
      }
      _tacticCall = (TacticCall)call;
    }

    public bool NextMemberInTld() {
      var isMore = _tldMembers.MoveNext();
      if (!isMore) return false;
      _member = _tldMembers.Current;
      _tacticCalls = GetTacticCallsInMember(_member as Method);
      return true;
    }

    public bool NextTacticCallInMember() {
      var isMore = _tacticCalls.MoveNext();
      if (isMore) _tacticCall = _tacticCalls.Current;
      return isMore;
    }
        
    public TacticExpansion ExpandCurrentTacticCall() {
      var expanded = "";
      var l = Microsoft.Dafny.Tacny.TacnyDriver.GetTacticResultList();
      var result = l.FirstOrDefault(pair => TokenEquals(pair.Key, _tacticCall.statement.Tok));
      if (result.Value == null) throw new NoTacticException();
      var sr = new StringWriter();
      var printer = new Printer(sr);
      foreach (var stmt in result.Value) {
        printer.PrintStatement(stmt, 4);
        sr.Write("\n");
      }
      expanded = sr.ToString();
      if (string.IsNullOrEmpty(expanded)) {
        throw new NoTacticException();
      }
      return new TacticExpansion(expanded, TacticExpandStatus.Success, _tacticCall.startPos, _tacticCall.endPos);
    }
    
    public TacticExpansion ExpandTacticsInCurrentMember() {
      if (!(_member is Method x)) throw new NoTacticException();
      var sr = new StringWriter();
      var printer = new Printer(sr);
      var l = Microsoft.Dafny.Tacny.TacnyDriver.GetTacticResultList();
      var hasTactic = false;
      sr.Write("\n");
      foreach (var stmt in x.Body.SubStatements) {
        var result = l.FirstOrDefault(pair => TokenEquals(pair.Key, stmt.Tok));
        if (result.Key == null) {
          printer.PrintStatement(stmt, 0);
        } else {
          hasTactic = true;
          result.Value.ForEach(foundStmt => printer.PrintStatement(foundStmt, 0));
        }
        sr.Write("\n");
      }
      var expanded = hasTactic ? sr.ToString() : "";
      if (string.IsNullOrEmpty(expanded)) {
        throw new NoTacticException();
      }
      return new TacticExpansion(expanded, TacticExpandStatus.Success, x.BodyStartTok.pos+1, x.BodyEndTok.pos);
    }

    private static DefaultClassDecl GetTld(Program p) =>
      (from tld in p?.DefaultModuleDef.TopLevelDecls
       let test = tld as DefaultClassDecl
       where test != null
       select test).FirstOrDefault();

    private static MemberDecl GetMemberFromPosition(DefaultClassDecl tld, int position) =>
      (from m in tld.Members where m.tok.pos <= position && position <= m.BodyEndTok.pos + 1 select m).FirstOrDefault();

    private static bool IsNotPotentialTacticCall(Statement stmt) {
      return !(stmt is InlineTacticBlockStmt) &&
          ((stmt as UpdateStmt) == null || (stmt as UpdateStmt).Lhss.Count != 0 || !(stmt as UpdateStmt).IsGhost);
    }

    private static IEnumerator<TacticCall> GetTacticCallsInMember(Method m) {
      if (m?.Body.Body == null) yield break;
      foreach (var stmt in m.Body.Body) {
        if (IsNotPotentialTacticCall(stmt))
          continue;
        TacticCall nextCall = GetTacticCallAtPosition(m, stmt.Tok.pos);
        if (nextCall.statement == null) {
          continue;
        }
        yield return (TacticCall)nextCall;
      }
    }

    private static TacticCall GetTacticCallAtPosition(Method m, int p) {
      TacticCall tc;
      try {
        tc = (from stmt in m?.Body?.Body
              let u = stmt as UpdateStmt
              let rhs = u?.Rhss[0] as ExprRhs
              let expr = rhs?.Expr as ApplySuffix
              let name = expr?.Lhs as NameSegment
              where name != null
              let start = expr.tok.pos - name.Name.Length
              let end = stmt.EndTok.pos + 1
              where start <= p && p <= end
              select new TacticCall(stmt, start, end))
          .FirstOrDefault();
      } catch (ArgumentNullException) {
        return new TacticCall();
      }

      if (tc.statement == null) {
        tc = (from stmt in m?.Body?.Body
              where stmt is InlineTacticBlockStmt
              let start = stmt.Tok.pos
              let end = stmt.EndTok.pos + 1
              where start <= p && p <= end
              select new TacticCall(stmt, start, end))
          .FirstOrDefault();
      }
      return tc;
    }

    private static bool TokenEquals(Microsoft.Boogie.IToken t, Microsoft.Boogie.IToken u) {
      return t.IsValid == u.IsValid && t.col == u.col && t.filename == u.filename
             && t.kind == u.kind && t.line == u.line && t.pos == u.pos && t.val == u.val;
    }
  }
}
