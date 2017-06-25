#define TACNY_DEBUG

using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;
using System.Reflection;
using Microsoft.Boogie;
using Microsoft.Dafny.Tacny.Expr;

namespace Microsoft.Dafny.Tacny
{
  public class TacnyInterpreter
  {
    public const int VerifyNProofState = 5;
    public enum VerifyResult
    {
      Unresolved, // failed to resolve
      Verified,
      Failed, // resoved but cannot be proved
      Backtracked,
    }

    public static IEnumerable<ProofState> EvalTopLevelTactic(ProofState state, Dictionary<IVariable, Type> variables,
      Statement tacticApplication, ErrorReporterDelegate errorDelegate, bool ifPartial) {
      Contract.Requires<ArgumentNullException>(Tcce.NonNull(variables));
      Contract.Requires<ArgumentNullException>(Tcce.NonNull(tacticApplication));
      Contract.Requires<ArgumentNullException>(state != null, "state");
      Contract.Requires(tacticApplication is UpdateStmt || tacticApplication is InlineTacticBlockStmt);

      IEnumerable<ProofState> branches;

      if (state.InitState(tacticApplication, variables, ifPartial) == false)
        return null;

#if !TACNY_DEBUG
      try {
#endif
      if (state.GetErrHandler().Reporter.Count(ErrorLevel.Error) != 0) {
        var errs = CompoundErrorInformation.GenerateErrorInfoList(state);
        if (errorDelegate != null) {
           foreach (var err in errs) {
             errorDelegate(err);
          }
        }

        return null;
      }
      branches = GenerateSolution(state, errorDelegate);

      #if !TACNY_DEBUG
      } catch (Exception e) {
        String msg;
        List<CompoundErrorInformation> errs;
        try {
          msg = "Tactic unknown exception: " + e.Message;
          errs = CompoundErrorInformation.GenerateErrorInfoList(state, msg);
        } catch (Exception) {
          msg = "Tactic exception";
          errs = new List<CompoundErrorInformation>();
        }

        if (errorDelegate != null) {
            foreach (var err in errs) {
              errorDelegate(err);
            }
          }
        return null;
      }
#endif

      return branches;
    }

    public static IEnumerable<ProofState> EvalStmt(Statement stmt, ProofState state) {
      Contract.Requires<ArgumentNullException>(state != null, "state");

      IEnumerable<ProofState> enumerable = null;

      var flowctrls = Assembly.GetAssembly(typeof(Language.TacticFrameCtrl))
        .GetTypes().Where(t => t.IsSubclassOf(typeof(Language.TacticFrameCtrl)));
      foreach (var ctrl in flowctrls) {
        var porjInst = Activator.CreateInstance(ctrl) as Language.TacticFrameCtrl;
        if (porjInst?.MatchStmt(stmt, state) == true) {
          //TODO: validate input countx
          enumerable = porjInst.EvalInit(stmt, state);
        }
      }
      // no frame control is triggered
      if (enumerable == null) {
        var declaration = stmt as TacticVarDeclStmt;
        if (declaration != null) {
          enumerable = RegisterVariable(declaration, state);
        } else if (stmt is AssignSuchThatStmt) {
          enumerable = EvalSuchThatStmt((AssignSuchThatStmt)stmt, state);
        } else if (stmt is PredicateStmt) {
          enumerable = EvalPredicateStmt((PredicateStmt)stmt, state);
        } else {
          var updateStmt = stmt as UpdateStmt;
          if (updateStmt != null) {
            var us = updateStmt;
            if (state.IsLocalAssignment(us)) {
              enumerable = UpdateLocalValue(us, state);
            } else if (state.IsArgumentApplication(us)) {
              //TODO: argument application ??
            } else {
              // apply atomic
              string sig = Util.GetSignature(us);
              //Firstly, check if this is a projection function
              var types =
                Assembly.GetAssembly(typeof(Atomic.Atomic))
                  .GetTypes()
                  .Where(t => t.IsSubclassOf(typeof(Atomic.Atomic)));
              foreach (var fType in types) {
                var porjInst = Activator.CreateInstance(fType) as Atomic.Atomic;
                if (sig == porjInst?.Signature) {
                  //TODO: validate input countx
                  enumerable = porjInst?.Generate(us, state);
                }
              }
            }
          }
          if (enumerable == null) {
            // default action as macro
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
      if (rhs == null) {
        // check if rhs is SuchThatStmt
        var stmt = declaration.Update as AssignSuchThatStmt;
        if (stmt != null) {
          foreach (var item in declaration.Locals)
            state.AddTacnyVar(item, null);
          foreach (var item in EvalSuchThatStmt(stmt, state)) {
            yield return item;
          }
          yield break;
        } else {
          foreach (var item in declaration.Locals)
            state.AddTacnyVar(item, null);
        }
      } else {
        foreach (var item in rhs.Rhss) {
          int index = rhs.Rhss.IndexOf(item);
          Contract.Assert(declaration.Locals.ElementAtOrDefault(index) != null, "register var err");
          var exprRhs = item as ExprRhs;
          if (exprRhs?.Expr is ApplySuffix) {
            var aps = (ApplySuffix)exprRhs.Expr;
            var result = SimpExpr.UnfoldTacticProjection(state, aps);
            state.AddTacnyVar(declaration.Locals[index], result);
          } else if (exprRhs?.Expr is Microsoft.Dafny.LiteralExpr) {
            state.AddTacnyVar(declaration.Locals[index], (Microsoft.Dafny.LiteralExpr)exprRhs?.Expr);
          } else if (exprRhs?.Expr is Microsoft.Dafny.NameSegment) {
            var name = ((Microsoft.Dafny.NameSegment)exprRhs.Expr).Name;
            if (state.ContainTVal(name))
              // in the case that referring to an exisiting tvar, dereference it
              state.AddTacnyVar(declaration.Locals[index], state.GetTVarValue(name));
          } else {
            var res = EvalExpr.EvalTacticExpression(state, exprRhs?.Expr);
            if (res == null)
              yield break;
            state.AddTacnyVar(declaration.Locals[index], res);
          }
        }
      }
      yield return state;
    }

    [Pure]
    private static IEnumerable<ProofState> UpdateLocalValue(UpdateStmt us, ProofState state) {
      Contract.Requires<ArgumentNullException>(us != null, "stmt");
      Contract.Requires<ArgumentNullException>(state != null, "state");
      Contract.Requires<ArgumentException>(state.IsLocalAssignment(us), "stmt");

      foreach (var item in us.Rhss) {
        int index = us.Rhss.IndexOf(item);
        Contract.Assert(us.Lhss.ElementAtOrDefault(index) != null, "register var err");
        var exprRhs = item as ExprRhs;
        if (exprRhs?.Expr is ApplySuffix) {
          var aps = (ApplySuffix)exprRhs.Expr;
          var result = SimpExpr.UnfoldTacticProjection(state, aps);
          state.UpdateTacticVar(((NameSegment)us.Lhss[index]).Name, result);
        } else if (exprRhs?.Expr is Microsoft.Dafny.LiteralExpr) {
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

    private static int _branchCount = 0;
    public static List<VerifyResult> VerifyState(List<ProofState> states) {

      _branchCount += states.Count;
      Console.WriteLine("Branch Count: " + _branchCount);

      List<VerifyResult> res = new List<VerifyResult>();
      List<int> idxs = new List<int>();
      List<ProofState> newStateList = new List<ProofState>();

      for(var i = 0; i < states.Count; i++) {
        var state = states[i];
        if (state.IsTimeOut()){
          state.GetErrHandler().ErrType = TacticBasicErr.ErrorType.Timeout;
          res.Add(VerifyResult.Failed);
        } else {
          var prog0 = Util.GenerateResolvedProg(state);
          if (prog0 == null || state.GetErrHandler().Reporter.Count(ErrorLevel.Error) != 0){
            res.Add(VerifyResult.Unresolved);
          } else{
            //set as verified just for now, will be updated later
            res.Add(VerifyResult.Verified);
            idxs.Add(i);
            newStateList.Add(state);
          }
        }
      }

      if (newStateList.Count == 0)
        return res;

      var prog = Util.GenerateResolvedProg(newStateList);

      Util.VerifyResolvedProg(states[0], prog, res, idxs, null);
      return res;
    }

    /// <summary>
    /// 
    /// </summary>
    /// <param name="rootState"></param>
    /// <param name="errDelegate"></param> to report err back to GUI
    /// <returns></returns>
    internal static IEnumerable<ProofState> GenerateSolution(ProofState rootState, ErrorReporterDelegate errDelegate) {
      var stack = new Stack<IEnumerator<ProofState>>();
      ProofState lastSucc = null; // the last verified state, for recovering over-backtracking
      var discarded = new List<Tuple<ProofState, VerifyResult>>(); // failed ps and its verified status
      List<ProofState> proofState = new List <ProofState> () {rootState};
      var rootBranches = rootState.EvalStep();
      if (rootBranches == null) {
        yield break;
      }
      stack.Push(rootBranches.GetEnumerator());

      IEnumerator<ProofState> enumerator = null;

      List<int> backtrackList = null;

      while (stack.Count > 0) {
        bool wasNull = false;
        if (enumerator != null) {
          try {
            if (enumerator.Current == null) {
              wasNull = true;
            }
          } catch {
            wasNull = true;
          }
        }

        if (enumerator == null || !enumerator.MoveNext()) {
          // check if current is valid, and the enumerator is empty when current is invalid and MoveNext is null
          if (enumerator != null && wasNull) {
            //Console.WriteLine("Null eval result is detected !");
            foreach (var state in proofState){
              discarded.Add(new Tuple<ProofState, VerifyResult>(state, VerifyResult.Unresolved));
            }
          }

          enumerator = stack.Pop();
          if (!enumerator.MoveNext()) {
            continue;
          }
        }

        var stateCount = 0;
        proofState.Clear();
        while (stateCount < VerifyNProofState){
          var current = enumerator.Current;
          proofState.Add(current);
          stateCount++;
          if(backtrackList != null)
            current.SetBackTrackCount(backtrackList);
          if(current.NeedVerify && proofState[0].GetVerifyN() > 1) {
            current.DecreaseVerifyN();
            current.NeedVerify = false;
          }
          if(!enumerator.MoveNext())
            break;
        }

        //should at alease one state in the list, use [0] as a typical state;
        var rep = proofState[0];
        backtrackList = rep.GetBackTrackCount();

        List<VerifyResult> ress = null;
        List<bool> returned = null;

        //check if any new added coded reuqires to call verifier, or reach the last line of code
        if ((rep.NeedVerify && rep.GetVerifyN() == 1)|| rep.IsCurFrameEvaluated()) {
          foreach(var s in proofState) {
            s.ResetVerifyN();
            s.NeedVerify = false;
          }

          bool backtracked = false;
          ress = VerifyState(proofState);
          returned = new List<bool>();

          for(var i = 0; i < ress.Count; i++) {
            var res = ress[i];
            var ret = false;
            switch(res) {
              case VerifyResult.Verified:
                //check if the frame are evaluated, as well as requiests for backtraking 
                proofState[i].MarkCurFrameAsTerminated(true, out backtracked);
                if(backtracked) {
                  lastSucc = proofState[i];
                  discarded.Add(new Tuple<ProofState, VerifyResult>(proofState[i], VerifyResult.Backtracked));
                }

                if(proofState[i].IsTerminated()) {
                  ret = true;
                  yield return proofState[i];
                }
                returned.Add(ret);
                break;
              case VerifyResult.Failed:
                if(proofState[i].IsCurFrameEvaluated()) {
                  proofState[i].MarkCurFrameAsTerminated(false, out backtracked);
                  if(backtracked) {
                    lastSucc = proofState[i];
                    discarded.Add(new Tuple<ProofState, VerifyResult>(proofState[i], VerifyResult.Backtracked));
                  }
                  if(proofState[i].IsTerminated()) {
                    ret = true;
                    yield return proofState[i];
                  }
                }
                returned.Add(ret);
                break;
              case VerifyResult.Unresolved:
                //Console.WriteLine("in unresolved");
                discarded.Add(new Tuple<ProofState, VerifyResult>(proofState[i], VerifyResult.Unresolved));
                //discard current branch if fails to resolve
                returned.Add(false);
                continue;
              default:
                throw new ArgumentOutOfRangeException();
            }
          }
        }
        /*
     * when failed, check if this method is evaluated , i.e. all tstmt are evalauted,
     * if so, do nothing will dischard this branch and continue with the next one
     * otherwise, continue to evaluate the next stmt
     */

        rep = proofState[0];

        if(!rep.IsCurFrameEvaluated()) {
          //push the current one to the stack
          stack.Push(enumerator);
          //move to the next stmt
          for(var i = 0; i < proofState.Count ; i++) {
            if(returned == null || !returned[i]) {
              stack.Push(proofState[i].EvalStep().GetEnumerator());
            }
          }
          enumerator = stack.Pop();
        } else {
          backtrackList = rep.GetBackTrackCount(); // update the current bc count to the list
          for(var i = 0; i < proofState.Count; i++) {
            if(returned == null || !returned[i]) {
              if(proofState[i].InAsserstion) {
                proofState[i].GetErrHandler().ErrType = TacticBasicErr.ErrorType.Assertion;
                var patchRes = proofState[i].ApplyPatch();
                if(patchRes != null) {
                  stack.Push(enumerator);
                  enumerator = patchRes.GetEnumerator();
                }
              } else
              proofState[i].GetErrHandler().ErrType = TacticBasicErr.ErrorType.NotProved;
              discarded.Add(new Tuple<ProofState, VerifyResult>(proofState[i], VerifyResult.Failed));
            }
          }
        }
      }
      //check if over-backchecked
      if (backtrackList != null && backtrackList.Exists(x => x > 0)) {
        if (lastSucc == null)
          Console.WriteLine("!!! No more branch for the request of " + (backtrackList.Last() + 1) +
                            "backtracking, and no branch.");
        else {
          Console.WriteLine("!!! No more branch for the request of " + lastSucc.GetOrignalTopBacktrack() +
                            ", remaining " +
                            (backtrackList.Last() + 1 > lastSucc.GetOrignalTopBacktrack()
                              ? lastSucc.GetOrignalTopBacktrack()
                              : backtrackList.Last() + 1) + " requests, return the last one.");
          yield return lastSucc;
        }
      } else {
        // no result is successful
        ProofState s0;
        if (discarded.Count > 0) {
          s0 = discarded[discarded.Count - 1].Item1;
          //s0.GetErrHandler().ExceptionReport();
        } else {
          s0 = rootState;
        }
        s0.ReportTacticError(s0.TopLevelTacApp.Tok,
          "No solution is found. \n The error message from the last failed branch: ");
        var errs = CompoundErrorInformation.GenerateErrorInfoList(s0);
        if (errDelegate != null) {
          foreach (var err in errs) {
            errDelegate(err);
          }
        }
      }

    }
  }
}

