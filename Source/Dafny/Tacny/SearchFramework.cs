﻿using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;
using Microsoft.Boogie;


namespace Microsoft.Dafny.Tacny {
  
  [ContractClass(typeof(BaseSearchContract))]
  public interface ISearch {
    IEnumerable<ProofState> Search(ProofState state, ErrorReporterDelegate er);
  }

  public enum Strategy {
    Undefined = 0,
    Bfs,
    Dfs
  }

  public enum VerifyResult {
    Unresolved, // failed to resolve
    Verified,
    Failed, // resoved but cannot be proved
    Backtracked,
    Partial, //TODO: partial when tactic and dafny succeed, but boogie fails
  }


  [ContractClassFor(typeof(ISearch))]
  // Validate the input before execution
  public abstract class BaseSearchContract : ISearch {
    public IEnumerable<ProofState> Search(ProofState state, ErrorReporterDelegate er) {
      Contract.Requires(state != null);
      return default(IEnumerable<ProofState>);
    }
  }

  public class BaseSearchStrategy : ISearch{
    protected Strategy ActiveStrategy;
    public BaseSearchStrategy(Strategy strategy) {
      ActiveStrategy = strategy;
    }

    protected BaseSearchStrategy() {
    }
    
    public IEnumerable<ProofState> Search(ProofState state, ErrorReporterDelegate er) {
      Contract.Requires<ArgumentNullException>(state != null, "rootState");
	  
	  IEnumerable<ProofState> enumerable;      
      switch (ActiveStrategy) {
        case Strategy.Bfs:
          throw new NotSupportedException("Breath first search has not been supported ");
          //enumerable = BreadthFirstSeach.Search(state, er);
          break;
        case Strategy.Dfs:
          enumerable = DepthFirstSeach.Search(state, er);
          break;
        case Strategy.Undefined:
          throw new Tcce.UnreachableException();
        default:
          enumerable = DepthFirstSeach.Search(state, er);
          break;
      }
      return enumerable;
    }

    public static VerifyResult VerifyState(ProofState state, ErrorReporterDelegate er) {
      
      if (state.IsTimeOut()){
        return VerifyResult.Failed;
      }
      var prog =  Util.GenerateResolvedProg(state);
      if (prog == null)
        return VerifyResult.Unresolved;

      var result = Util.VerifyResolvedProg(state, prog, null);

      if(result)
        return VerifyResult.Verified;
      else {
        return VerifyResult.Failed;
      }
    }


    internal class DepthFirstSeach : BaseSearchStrategy{

      internal new static IEnumerable<ProofState> Search(ProofState rootState, ErrorReporterDelegate er){
        var stack = new Stack<IEnumerator<ProofState>>(); 
        ProofState lastSucc = null; // last verfied state, for recoveingr over-backtracked
        var discarded = new List<Tuple<ProofState, VerifyResult>>(); //failed branchesa and its status

        stack.Push(rootState.EvalStep().GetEnumerator());

        IEnumerator<ProofState> enumerator = Enumerable.Empty<ProofState>().GetEnumerator();

        List<int> backtackList = null;

        while (stack.Count > 0){
          if (!enumerator.MoveNext()){
            enumerator = stack.Pop();
            if (!enumerator.MoveNext())
              continue;
          }
          var proofState = enumerator.Current;
          //set the backtrack list back to the frame, this will udpate the backtrack count for the parent one.
          if (backtackList != null)
            proofState.SetBackTrackCount(backtackList);
          backtackList = proofState.GetBackTrackCount();

          //check if any new added coded reuqires to call verifier, or reach the last line of code
          if (proofState.NeedVerify || proofState.IsEvaluated()){
            proofState.NeedVerify = false;
            bool backtracked = false;

            switch (VerifyState(proofState, er)){
              case VerifyResult.Verified:
                //check if the frame are evaluated, as well as requiests for backtraking 
                proofState.MarkCurFrameAsTerminated(true, out backtracked);
                if (backtracked){
                  lastSucc = proofState;
                  discarded.Add(new Tuple<ProofState, VerifyResult>(proofState, VerifyResult.Backtracked));
                }

                if (proofState.IsTerminated()){
                  yield return proofState;
                  yield break;
                }

                break;
              case VerifyResult.Failed:
                if (proofState.IsEvaluated()){
                  proofState.MarkCurFrameAsTerminated(false, out backtracked);
                  if (backtracked){
                    lastSucc = proofState;
                    discarded.Add(new Tuple<ProofState, VerifyResult>(proofState, VerifyResult.Backtracked));
                  }
                  if (proofState.IsTerminated()){
                    yield return proofState;
                    yield break;
                  }
                }
                break;
              case VerifyResult.Unresolved:
                discarded.Add(new Tuple<ProofState, VerifyResult>(proofState, VerifyResult.Unresolved));
                //discard current branch if fails to resolve
                continue;
              default:
                throw new ArgumentOutOfRangeException();
            }
          }
          /*
       * when failed, check if this method is evaluated , i.e. all tstmt are evalauted,
       * if so, do nothing will dischard this branch and continue with the next one
       * otherwise, continue to evaluate the next stmt
       */
          if (!proofState.IsEvaluated()){
            //push the current one to the stack
            stack.Push(enumerator);
            //move to the next stmt
            enumerator = (proofState.EvalStep().GetEnumerator());
          }
          else{
            backtackList = proofState.GetBackTrackCount(); // update the current bc count to the list
            discarded.Add(new Tuple<ProofState, VerifyResult>(proofState, VerifyResult.Failed));
          }

        }
        //check if over-backchecked
        if (backtackList != null && backtackList.Exists(x => x > 0)){
          if (lastSucc == null)
            Console.WriteLine("!!! No more branch for the request of " + (backtackList.Last() + 1) +
                              "backtracking, and no branch.");
          else{
            Console.WriteLine("!!! No more branch for the request of " + lastSucc.GetOrignalTopBacktrack() +
                              ", remaining " +
                              (backtackList.Last() + 1 > lastSucc.GetOrignalTopBacktrack()
                                ? lastSucc.GetOrignalTopBacktrack()
                                : backtackList.Last() + 1) + " requests, return the last one.");
            yield return lastSucc;
          }

        }
        else{
          // no result is successful
          if (discarded.Count > 0)
            discarded[discarded.Count - 1].Item1.GetErrHandler().ExceptionReport();
        }
      }
    }
  }
}


