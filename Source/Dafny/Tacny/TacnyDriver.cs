using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Diagnostics.Contracts;
using System.Globalization;
using System.Linq;
using System.Reflection;
using System.Security.AccessControl;
using Microsoft.Boogie;
using Microsoft.Dafny.Tacny.Expr;

namespace Microsoft.Dafny.Tacny
{
  public class TacnyDriver
  {
    public static int TacticCodeTokLine = -1;
    public static bool IfEvalTac { get; set; } = true;

    private static TacnyDriver _driver;
    private static ErrorReporterDelegate _errorReporterDelegate;
    private static Dictionary<Statement, List<Statement>> _resultList;
    private static List<IEnumerable<ProofState>> _branches;
    private static Stopwatch _timer;
    private readonly ProofState _state;
    private static int _tacticCalls;

    private static Dictionary<Statement, List<Statement>> GetResultList(){
      if (_resultList == null)
        _resultList = new Dictionary<Statement, List<Statement>>();
      return _resultList;
    }

    private static void SetResultList(Dictionary<Statement, List<Statement>> rl){
      _resultList = rl;
    }

    private static void RemoveFromResultList(Statement stmt)
    {
      var newrl = GetResultList().Where(kvp => kvp.Key.Tok.pos != stmt.Tok.pos).ToDictionary(i => i.Key, i => i.Value);
      SetResultList(newrl);
    }

    private static void UpdateResultList(Statement stmt, List<Statement> result) {
      //note that this will override generated code for the same tactic call
      var newrl = GetResultList().Where(kvp => kvp.Key.Tok.pos != stmt.Tok.pos).ToDictionary(i => i.Key, i => i.Value);
      SetResultList(newrl);
      GetResultList().Add(stmt.Copy(), result != null ? result : new List<Statement>());
    }
   
    public static Stopwatch GetTimer () {
      if (_timer == null){
        _timer = new Stopwatch();
      }
      return _timer;
    }

    public static Dictionary<IToken, List<Statement>> GetTacticResultList()
    {
      Dictionary<IToken, List<Statement>> bufferList = new Dictionary<IToken, List<Statement>>();
      foreach (var e in GetResultList()) {
        bufferList.Add(e.Key.Tok, e.Value);
      }
      return bufferList;
    }

    private TacnyDriver(Program program, ErrorReporterDelegate erd)
    {
      Contract.Requires(Tcce.NonNull(program));
      // initialize state
      GetTimer().Restart();
      _state = new ProofState(program);
      _errorReporterDelegate = erd;
      _branches = new List<IEnumerable<ProofState>>();
      _tacticCalls = 0;
    }

    public static MemberDecl ApplyTacticInMethod(Program program, MemberDecl target, ErrorReporterDelegate erd,
      Resolver r = null, Program raw = null)
    {
      Contract.Requires(program != null);
      Contract.Requires(target != null);
      Stopwatch watch = new Stopwatch();
      watch.Start();

      _driver = new TacnyDriver(program, erd);
      // backup datatype info, as this will be reset by the internal resolving process in tacny.
      // this contains datatype obj instance for comparing types
      Type.BackupScopes(); 
      var result = _driver.InterpretAndUnfoldTactic(target, r);
      Type.RestoreScopes();
      var p = new Printer(Console.Out);
      p.PrintMembers(new List<MemberDecl>() {result}, 0, "");

      watch.Stop();
      Console.WriteLine("Time Used: " + watch.Elapsed.TotalSeconds);
      _errorReporterDelegate = null;
      return result;
    }

    private static bool GenerateResultCode()
    {
      return GenerateResultCode0(_branches);
    }

    private static bool GenerateResultCode0 (List<IEnumerable<ProofState>> branches)
    {
      if (branches != null && branches.Count > 0 && branches[0] != null) {
        var result = branches[0].FirstOrDefault();
        if (result != null) {
          UpdateResultList(result.TopLevelTacApp,
            result.GetGeneratedCode().Copy());
          branches[0] = branches[0].Skip(1);
        }

        if (branches.Count == 1) {
          return result == null ? false : true;
        } else if (GenerateResultCode0(branches.GetRange(1, branches.Count - 1))) {
          return true;
        } else
          return GenerateResultCode0(branches);
      }
      return false;
    }

    private MemberDecl InterpretAndUnfoldTactic(MemberDecl target, Resolver r)
    {
      Contract.Requires(Tcce.NonNull(target));
      // initialize new stack for variables
      var frame = new Stack<Dictionary<IVariable, Type>>();

      var method = target as Method;
      if (method != null) {
        _state.SetTopLevelClass(method.EnclosingClass?.Name);
        _state.TargetMethod = target;
        var dict = method.Ins.Concat(method.Outs)
          .ToDictionary<IVariable, IVariable, Type>(item => item, item => item.Type);

        frame.Push(dict);
        var preRes = GetResultList().Keys.Copy();

        InterpertBlockStmt(method.Body, frame);
        GenerateResultCode();
        // sanity check
        Contract.Assert(frame.Count == 0);

        var newRets = 
          GetResultList().Where(kvp => !preRes.Contains(kvp.Key)).ToDictionary(i => i.Key, i => i.Value);

        Contract.Assert(newRets.Count != 0);
        var body = Util.InsertCode(_state, newRets);
        method.Body.Body.Clear();
        if (newRets.Count != 0 && body != null)
          method.Body.Body.AddRange(body.Body);

        // use the original resolver of the resoved program, as it contains all the necessary type info
        method.CallsTactic = 0; 
        // set the current class in the resolver, so that it can refer to the memberdecl correctly
        r.SetCurClass(method.EnclosingClass as ClassDecl);
        //asssume the defualt module is the current module, this needs to be improved.
        r.ResolveMethodBody(method, _state.GetDafnyProgram().DefaultModuleDef.Name);
        //Console.WriteLine("Errors: " + _program.reporter.Count(ErrorLevel.Error));

      }
      return method;
    }

    private void InterpertBlockStmt(List<Statement> body, Stack<Dictionary<IVariable, Type>> frame)
    {
      frame.Push(new Dictionary<IVariable, Type>());
      foreach (var stmt in body) {
        if (stmt is VarDeclStmt) {

          var vds = stmt as VarDeclStmt;

          // register local variable declarations
          foreach (var local in vds.Locals) {
            try {
              frame.Peek().Add(local, local.Type);
            } catch (Exception e) {
              //TODO: some error handling when target is not resolved
              Console.Out.WriteLine(e.Message);
            }
          }
        } else if (stmt is IfStmt) {
          var ifStmt = stmt as IfStmt;
          InterpretIfStmt(ifStmt, frame);
        } else if (stmt is WhileStmt) {
          var whileStmt = stmt as WhileStmt;
          InterpretWhileStmt(whileStmt, frame);
        } else if (stmt is UpdateStmt) {
          if (_state.IsTacticCall(stmt as UpdateStmt)) {
            UndfoldTacticCall(stmt, Util.GetTacticAppExpr(stmt as UpdateStmt), StackToDict(frame));
          }
          var expr = TacticAppExprFinder.GetTacticAppExpr(_state, stmt);
          if(expr != null) {
            UndfoldTacticCall(stmt, expr, StackToDict(frame));
          }
        } else if (stmt is InlineTacticBlockStmt) {
          UndfoldTacticCall(stmt, null, StackToDict(frame));
        } else if (stmt is MatchStmt) {
          foreach (var caseStmt in (stmt as MatchStmt).Cases) {
            InterpretCaseStmt(caseStmt, frame);            
          }
        } else if (stmt is ForallStmt) {
          //TODO
        } else if (stmt is AssertStmt) {
          if ((stmt as AssertStmt).Proof != null) {
            InterpretAssertStmt(stmt as AssertStmt, frame);
          }
        } else if (stmt is CalcStmt) {
        } else if (stmt is BlockStmt) {
          InterpertBlockStmt((stmt as BlockStmt), frame);
        } else {
          var expr = TacticAppExprFinder.GetTacticAppExpr(_state, stmt);
          if(expr != null) {
            UndfoldTacticCall(stmt, expr, StackToDict(frame));
          }
        }
      }
      frame.Pop();
    }
    // Find tactic application and resolve it
    private void InterpertBlockStmt(BlockStmt body, Stack<Dictionary<IVariable, Type>> frame)
    {
      Contract.Requires(Tcce.NonNull(body));
      InterpertBlockStmt(body.Body, frame);
    }

    private void InterpretWhileStmt(WhileStmt stmt, Stack<Dictionary<IVariable, Type>> frame)
    {
      //TODO: need to check inv
      /*
      if (stmt.TInvariants != null && stmt.TInvariants.Count > 0) {
        foreach (var tinv in stmt.TInvariants) {
          if (tinv is UpdateStmt) {
            var list = StackToDict(frame);

            if (IfEvalTac) {
              _branches.Add(
                TacnyInterpreter.EvalTopLevelTactic(_state.Copy(), list, tinv as UpdateStmt, _errorReporterDelegate,
                 _state.TargetMethod.CallsTactic != _tacticCalls + 1));
              _tacticCalls++;
            }

          }
        }
      }*/
      InterpertBlockStmt(stmt.Body, frame);
    }

    private void InterpretIfStmt(IfStmt ifStmt, Stack<Dictionary<IVariable, Type>> frame)
    {
      Contract.Requires(Tcce.NonNull(ifStmt));
      //throw new NotImplementedException();

      InterpertBlockStmt(ifStmt.Thn, frame);
      if (ifStmt.Els == null)
        return;
      var els = ifStmt.Els as BlockStmt;
      if (els != null) {
        InterpertBlockStmt(els, frame);
      } else if (ifStmt.Els is IfStmt) {
        InterpretIfStmt((IfStmt) ifStmt.Els, frame);
      }
    }

    private void InterpretCaseStmt(MatchCaseStmt stmt, Stack<Dictionary<IVariable, Type>> frame)
    {
      frame.Push(new Dictionary<IVariable, Type>());
      foreach (var var in stmt.Ctor.Formals) {
        try {
          frame.Peek().Add(var, var.Type);
        } catch (Exception e) {
          Console.Out.WriteLine(e.Message);
        }
      }
      InterpertBlockStmt(stmt.Body, frame);
      frame.Pop();
    }

    private void InterpretAssertStmt(AssertStmt stmt, Stack<Dictionary<IVariable, Type>> frame)
    {
      InterpertBlockStmt(stmt.Proof, frame);
    }


    private void InterpretCalcStmt(CalcStmt stmt) {
      //InterpertBlockStmt(stmt.);
    }

    private void UndfoldTacticCall(Statement stmt, ApplySuffix aps, Dictionary<IVariable, Type> varList) {
      // this is a top level tactic call
      if (IfEvalTac) {
        _branches.Add(
          TacnyInterpreter.EvalTopLevelTactic(_state.Copy(), varList, stmt, aps,  _errorReporterDelegate, 
          _state.TargetMethod.CallsTactic != _tacticCalls + 1));
        _tacticCalls++;
      }
    }

    private static Dictionary<IVariable, Type> StackToDict(Stack<Dictionary<IVariable, Type>> stack)
    {
      Contract.Requires(stack != null);
      Contract.Ensures(Contract.Result<Dictionary<IVariable, Type>>() != null);
      var result = new Dictionary<IVariable, Type>();
      foreach (var dict in stack) {
        dict.ToList().ForEach(x => result.Add(x.Key, x.Value));
      }
      return result;
    }

  }
}
