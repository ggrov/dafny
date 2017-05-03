﻿#define TACNY_DEBUG

using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Diagnostics.Contracts;
using System.Globalization;
using System.Linq;
using System.Reflection;
using Microsoft.Boogie;
using Microsoft.Dafny.Tacny.Expr;

namespace Microsoft.Dafny.Tacny {
  public class Interpreter {
    public static int TacticCodeTokLine = -1;
    public static bool IfEvalTac { get; set; } = true;

    private static Interpreter _i;
    private static ErrorReporterDelegate _errorReporterDelegate;
    private static Dictionary<UpdateStmt, List<Statement>> _resultList;

    private Stack<Dictionary<IVariable, Type>> _frame;

    private readonly ProofState _state;

    public static Stopwatch Timer;

    public static void ResetTacticResultList(){
      if (Timer == null)
        Timer = new Stopwatch();

      if(_resultList == null)
        _resultList = new Dictionary<UpdateStmt, List<Statement>>();
      else
        _resultList.Clear();

      EAtomic.EAtomic.InitEAtomicSigList();
    }

    public static Dictionary<IToken, List<Statement>> GetTacticResultList() {
      Dictionary<IToken, List<Statement>> bufferList = new Dictionary<IToken, List<Statement>>();

      foreach(var e in _resultList) {
        bufferList.Add(e.Key.Tok, e.Value);
      }
      return bufferList;
    }

    private Interpreter(Program program) {
      Contract.Requires(Tcce.NonNull(program));
      // initialize state
      _state = new ProofState(program);
      _frame = new Stack<Dictionary<IVariable, Type>>();
      //_resultList = new Dictionary<UpdateStmt, List<Statement>>();
    }

    /// <summary>
    /// 
    /// </summary>
    /// <param name="program"></param>
    /// <param name="target"></param>
    /// <param name="erd"></param>
    ///  only used this to report error, local errors which are genereaed during searching should not use this

    /// <param name="r"></param>
    /// <returns></returns>
    public static MemberDecl ResolveMethod(Program program, MemberDecl target, ErrorReporterDelegate erd, Resolver r = null) {
      Contract.Requires(program != null);
      Contract.Requires(target != null);
      Stopwatch watch = new Stopwatch();
      watch.Start();
      Timer.Restart();
      _i = new Interpreter(program);
      _errorReporterDelegate = erd;
      Type.BackupScopes();
      var result = _i.ResolveAndUnfoldTactic(target, r);
      Type.RestoreScopes();
      var p = new Printer(Console.Out);
      p.PrintMembers(new List<MemberDecl>() { result }, 0, "");

      watch.Stop();
      Console.WriteLine("Time Used: " + watch.Elapsed.TotalSeconds);

      _errorReporterDelegate = null;
      return result;
    }


    private MemberDecl ResolveAndUnfoldTactic(MemberDecl target, Resolver r) {
      Contract.Requires(Tcce.NonNull(target));
      // initialize new stack for variables
      _frame = new Stack<Dictionary<IVariable, Type>>();

      var method = target as Method;
      if(method != null) {
        _state.SetTopLevelClass(method.EnclosingClass?.Name);
        _state.TargetMethod = target;
        var dict = method.Ins.Concat(method.Outs)
          .ToDictionary<IVariable, IVariable, Type>(item => item, item => item.Type);
        _frame.Push(dict);

        var preRes = _resultList.Keys.Copy();

        ResolveBlockStmt(method.Body);
        dict = _frame.Pop();
        // sanity check
        Contract.Assert(_frame.Count == 0);

        var newRets = _resultList.Where(kvp => !preRes.Contains(kvp.Key)).ToDictionary(i => i.Key, i => i.Value);
        Contract.Assert(newRets.Count != 0);
        var body = Util.InsertCode(_state, newRets);
        method.Body.Body.Clear();
        if(body != null)
          method.Body.Body.AddRange(body.Body);

        
        // use the original resolver of the resoved program, as it contains all the necessary type info
        method.CallsTactic = false; // set the tactic call lable to be false, no actual consequence
        // set the current class in the resolver, so that it can refer to the memberdecl correctly
        r.SetCurClass(method.EnclosingClass as ClassDecl);
        //asssume the defualt module is the current module, this needs to be improved.
        r.ResolveMethodBody(method, _state.GetDafnyProgram().DefaultModuleDef.Name);
        //Console.WriteLine("Errors: " + _program.reporter.Count(ErrorLevel.Error));

      }
      return method;
    }

    // Find tactic application and resolve it
    private void ResolveBlockStmt(BlockStmt body) {
      Contract.Requires(Tcce.NonNull(body));

      // BaseSearchStrategy.ResetProofList();
      _frame.Push(new Dictionary<IVariable, Type>());
      foreach(var stmt in body.Body) {
        if(stmt is VarDeclStmt) {
          var vds = stmt as VarDeclStmt;
          // register local variable declarations
          foreach(var local in vds.Locals) {
            try {
              _frame.Peek().Add(local, local.Type);
            } catch(Exception e) {
              //TODO: some error handling when target is not resolved
              Console.Out.WriteLine(e.Message);
            }
          }
        } else if(stmt is IfStmt) {
          var ifStmt = stmt as IfStmt;
          ResolveIfStmt(ifStmt);

        } else if(stmt is WhileStmt) {
          var whileStmt = stmt as WhileStmt;
          ResolveWhileStmt(whileStmt);
        } else if(stmt is UpdateStmt) {
          ResolveTacticCall(stmt as UpdateStmt);
        } else if(stmt is BlockStmt) {
          //TODO:
        }
      }
      _frame.Pop();
    }

    private void ResolveTacticCall(UpdateStmt stmt) {
      var us = stmt as UpdateStmt;
      if(_state.IsTacticCall(us)) {
        var list = StackToDict(_frame);
        // this is a top level tactic call
        ProofState result = null;
        if (IfEvalTac){
          result = EvalTopLevelTactic(_state, list, us);
        }
        _resultList.Add(us.Copy(), result != null ? result.GetGeneratedCode().Copy() : new List<Statement>());
      }
    }

    private void ResolveWhileStmt(WhileStmt stmt) {
      if(stmt.TInvariants != null && stmt.TInvariants.Count > 0) {
        foreach(var tinv in stmt.TInvariants) {
          if(tinv is UpdateStmt) {
            var list = StackToDict(_frame);
            // this is a top level tactic call
            ProofState result = null;
            if (IfEvalTac){
              result = EvalTopLevelTactic(_state, list, tinv as UpdateStmt);
            }
            if(result != null)
              _resultList.Add(tinv as UpdateStmt, result.GetGeneratedCode().Copy());
          }
        }
      }
      ResolveBlockStmt(stmt.Body);
    }

    private void ResolveIfStmt(IfStmt ifStmt) {
      Contract.Requires(Tcce.NonNull(ifStmt));
      //throw new NotImplementedException();

      ResolveBlockStmt(ifStmt.Thn);
      if(ifStmt.Els == null)
        return;
      var els = ifStmt.Els as BlockStmt;
      if(els != null) {
        ResolveBlockStmt(els);
      } else if(ifStmt.Els is IfStmt) {
        ResolveIfStmt((IfStmt)ifStmt.Els);
      }
    }

    private static Dictionary<IVariable, Type> StackToDict(Stack<Dictionary<IVariable, Type>> stack) {
      Contract.Requires(stack != null);
      Contract.Ensures(Contract.Result<Dictionary<IVariable, Type>>() != null);
      var result = new Dictionary<IVariable, Type>();
      foreach(var dict in stack) {
        dict.ToList().ForEach(x => result.Add(x.Key, x.Value));
      }
      return result;
    }

    public static ProofState EvalTopLevelTactic(ProofState state, Dictionary<IVariable, Type> variables,
      UpdateStmt tacticApplication) {
      Contract.Requires<ArgumentNullException>(Tcce.NonNull(variables));
      Contract.Requires<ArgumentNullException>(Tcce.NonNull(tacticApplication));
      Contract.Requires<ArgumentNullException>(state != null, "state");
      state.InitState(tacticApplication, variables);

      var search = new BaseSearchStrategy(state.GetSearchStrategy());
      ProofState ret;
#if !TACNY_DEBUG
      try
      {
#endif
        if (state.GetErrHandler().Reporter.Count(ErrorLevel.Error) != 0) {
          var errs = CompoundErrorInformation.GenerateErrorInfoList(state);
          if (_errorReporterDelegate != null) {
            lock (_errorReporterDelegate) {
              foreach (var err in errs) {
                _errorReporterDelegate(err);
              }
            }
          }

          return null;
        }
        ret = search.Search(state, _errorReporterDelegate).FirstOrDefault();
#if !TACNY_DEBUG
      } catch (Exception e){
        String msg;
        List<CompoundErrorInformation> errs;
        try
        {
          msg = "Tactic exception: " + e.Message;
          errs = CompoundErrorInformation.GenerateErrorInfoList(state, msg);
        }
        catch (Exception){
          msg = "Tactic exception";
          errs = new List<CompoundErrorInformation>();
        }

        if(_errorReporterDelegate != null)
        {
          lock (_errorReporterDelegate)
          {
            foreach(var err in errs) {
              _errorReporterDelegate(err);
            }
          }
        }
        ret = null;
      }
#endif
      return ret;
    }


    public static IEnumerable<ProofState> EvalStmt(Statement stmt, ProofState state) {
      Contract.Requires<ArgumentNullException>(state != null, "state");

      IEnumerable<ProofState> enumerable = null;

      var flowctrls = Assembly.GetAssembly(typeof(Language.TacticFrameCtrl))
     .GetTypes().Where(t => t.IsSubclassOf(typeof(Language.TacticFrameCtrl)));
      foreach(var ctrl in flowctrls) {
        var porjInst = Activator.CreateInstance(ctrl) as Language.TacticFrameCtrl;
        if(porjInst?.MatchStmt(stmt, state) == true) {
          //TODO: validate input countx
          enumerable = porjInst.EvalInit(stmt, state);
        }
      }
      // no frame control is triggered
      if(enumerable == null)
      {
        var declaration = stmt as TacticVarDeclStmt;
        if(declaration != null) {
          enumerable = RegisterVariable(declaration, state);
        }  else if(stmt is AssignSuchThatStmt) {
          enumerable = EvalSuchThatStmt((AssignSuchThatStmt)stmt, state);
        } else if(stmt is PredicateStmt) {
          enumerable = EvalPredicateStmt((PredicateStmt)stmt, state);
        } else {
          var updateStmt = stmt as UpdateStmt;
          if(updateStmt != null) {
            var us = updateStmt;
            if(state.IsLocalAssignment(us)) {
              enumerable = UpdateLocalValue(us, state);
            } else if(state.IsArgumentApplication(us)) {
              //TODO: argument application ??
            } else {
              // apply atomic
              string sig = Util.GetSignature(us);
              //Firstly, check if this is a projection function
              var types =
                Assembly.GetAssembly(typeof(Atomic.Atomic))
                  .GetTypes()
                  .Where(t => t.IsSubclassOf(typeof(Atomic.Atomic)));
              foreach(var fType in types) {
                var porjInst = Activator.CreateInstance(fType) as Atomic.Atomic;
                if(sig == porjInst?.Signature) {
                  //TODO: validate input countx
                  enumerable = porjInst?.Generate(us, state);
                }
              }
            }
          }
          if (enumerable == null) {// default action as macro
            enumerable = DefaultAction(stmt, state);
          }
        }
      }
      return enumerable;
    }

    public static IEnumerable<ProofState> EvalPredicateStmt(PredicateStmt predicate, ProofState state) {
      Contract.Requires<ArgumentNullException>(predicate != null, "predicate");

      var newPredicate = SimpExpr.SimpTacticExpr(state, predicate);
      var copy = state.Copy();
      copy.AddStatement(newPredicate);
      copy.NeedVerify = true;
      yield return copy;
    }

    public static IEnumerable<ProofState> EvalSuchThatStmt(AssignSuchThatStmt stmt, ProofState state) {
      var evaluator = new Atomic.SuchThatAtomic();
      return evaluator.Generate(stmt, state);
    }

    public static IEnumerable<ProofState> RegisterVariable(TacticVarDeclStmt declaration, ProofState state) {
      if (declaration.Update == null)
        yield break;
      var rhs = declaration.Update as UpdateStmt;
      if(rhs == null)
      {
        // check if rhs is SuchThatStmt
        var stmt = declaration.Update as AssignSuchThatStmt;
        if(stmt != null) {
          foreach(var item in declaration.Locals)
            state.AddTacnyVar(item, null);
          foreach(var item in EvalSuchThatStmt(stmt, state)) {
            yield return item;
          }
          yield break;
        } else {
          foreach(var item in declaration.Locals)
            state.AddTacnyVar(item, null);
        }
      } else {
        foreach(var item in rhs.Rhss) {
          int index = rhs.Rhss.IndexOf(item);
          Contract.Assert(declaration.Locals.ElementAtOrDefault(index) != null, "register var err");
          var exprRhs = item as ExprRhs;
          if(exprRhs?.Expr is ApplySuffix) {
            var aps = (ApplySuffix)exprRhs.Expr;
            var result = SimpExpr.UnfoldTacticProjection(state, aps); 
            state.AddTacnyVar(declaration.Locals[index], result);
          } else if(exprRhs?.Expr is Microsoft.Dafny.LiteralExpr) {
            state.AddTacnyVar(declaration.Locals[index], (Microsoft.Dafny.LiteralExpr)exprRhs?.Expr);
          } else if(exprRhs?.Expr is Microsoft.Dafny.NameSegment) {
            var name = ((Microsoft.Dafny.NameSegment)exprRhs.Expr).Name;
            if(state.ContainTVal(name))
              // in the case that referring to an exisiting tvar, dereference it
              state.AddTacnyVar(declaration.Locals[index], state.GetTVarValue(name));
          } else {
            state.AddTacnyVar(declaration.Locals[index], EvalExpr.EvalTacticExpression(state, exprRhs?.Expr));
          }
        }
      }
      yield return state.Copy();
    }

    [Pure]
    private static IEnumerable<ProofState> UpdateLocalValue(UpdateStmt us, ProofState state) {
      Contract.Requires<ArgumentNullException>(us != null, "stmt");
      Contract.Requires<ArgumentNullException>(state != null, "state");
      Contract.Requires<ArgumentException>(state.IsLocalAssignment(us), "stmt");

      foreach(var item in us.Rhss) {
        int index = us.Rhss.IndexOf(item);
        Contract.Assert(us.Lhss.ElementAtOrDefault(index) != null, "register var err");
        var exprRhs = item as ExprRhs;
        if(exprRhs?.Expr is ApplySuffix) {
          var aps = (ApplySuffix)exprRhs.Expr;
          var result = SimpExpr.UnfoldTacticProjection(state, aps);
           state.UpdateTacticVar(((NameSegment)us.Lhss[index]).Name, result);
        } else if(exprRhs?.Expr is Microsoft.Dafny.LiteralExpr) {
          state.UpdateTacticVar(((NameSegment)us.Lhss[index]).Name, (Microsoft.Dafny.LiteralExpr)exprRhs?.Expr);
        } else {
          throw new NotSupportedException("Not supported update statement");
        }
      }
      yield return state.Copy();
    }

    /// <summary>
    /// Insert the statement as is into the state
    /// </summary>
    /// <param name="stmt"></param>
    /// <param name="state"></param>
    /// <returns></returns>
    private static IEnumerable<ProofState> DefaultAction(Statement stmt, ProofState state) {
      Contract.Requires<ArgumentNullException>(stmt != null, "stmt");
      Contract.Requires<ArgumentNullException>(state != null, "state");
      state.AddStatement(stmt);
      yield return state.Copy();
    }
  }
}

