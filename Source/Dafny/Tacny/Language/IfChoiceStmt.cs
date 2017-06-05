using System;
using System.Collections.Generic;
using System.Linq;
using Microsoft.Dafny.Tacny.Expr;
using System.Diagnostics.Contracts;

namespace Microsoft.Dafny.Tacny.Language{
  public class IfChoiceStmt : TacticFrameCtrl{

    public override bool MatchStmt(Statement stmt, ProofState state){
      if (stmt is Dafny.IfStmt || stmt is Dafny.AlternativeStmt)
        return (new OrChoiceStmt().MatchStmt(stmt, state) == false);
      return false;
    }

    public override IEnumerable<ProofState> EvalStep(ProofState state0){
      var statement = GetStmt();
      return TacnyInterpreter.EvalStmt(statement, state0);
    }

    private List<Tuple<Expression, List<Statement>>> GetGuadBodyList(Statement stmt,
      List<Tuple<Expression, List<Statement>>> resList)
    {
      var ifStmt = stmt as IfStmt;
      if (ifStmt != null){
        return GetGuadBodyList(ifStmt, resList);
      }
      else{
        return GetGuadBodyList(stmt as AlternativeStmt, resList);
      }
    }

    private List<Tuple<Expression, List<Statement>>> GetGuadBodyList(IfStmt stmt,
      List<Tuple<Expression, List<Statement>>> resList){
      // the else stmt will have expression true as the guard
      resList.Add(new Tuple<Expression, List<Statement>>(stmt.Guard, stmt.Thn.Body));
      if (stmt.Els == null)
        return resList;
      else
      {
        var blockStmt = stmt.Els as BlockStmt;
        if (blockStmt != null){
          // else
          var body = blockStmt;
          resList.Add(new Tuple<Expression, List<Statement>>(null, body.Body));
          return resList;
        }
        else{
          // else if
          return GetGuadBodyList(stmt.Els, resList);
        }
      }
    }

    private List<Tuple<Expression, List<Statement>>> GetGuadBodyList(AlternativeStmt stmt,
      List<Tuple<Expression, List<Statement>>> resList){
      //for each cases, add guards and body into the list
      foreach (var item in stmt.Alternatives){
        resList.Add(new Tuple<Expression, List<Statement>>(item.Guard, item.Body));
      }
      return resList;
    }

    public override IEnumerable<ProofState> EvalInit(Statement statement, ProofState state0){
      bool partial = true;
      List<Tuple<Expression, List<Statement>>> guardBodyList = new List<Tuple<Expression, List<Statement>>>();

      int counter = 0;

      guardBodyList = GetGuadBodyList(statement, guardBodyList);
      Contract.Assert(guardBodyList.Count > 0);

      var tryEval = EvalExpr.EvalTacticExpression(state0, guardBodyList[0].Item1);
      if (tryEval == null)
        yield break;
      //check whether the top level of the first guard is tactic level or object level
      if (!(tryEval is LiteralExpr && (tryEval as LiteralExpr).Value is bool)) {
        var state = state0.Copy();
        var st = SimpExpr.SimpTacticExpr(state, statement);
        state.NeedVerify = true;
        state.AddStatement(st);
        yield return state;
        yield break;
      } else{
        // tactic if
        foreach (var item in guardBodyList){
          if (item.Item1 == null && counter == 0) //else branch and no other branch is satisfied.
          {
            counter++;
            var state = state0.Copy();
            var ifChoice = this.Copy();
            ifChoice.InitBasicFrameCtrl(item.Item2, partial, null, VerifyN);
            state.AddNewFrame(ifChoice);

            yield return state;
          }
          else{
            var res = EvalExpr.EvalTacticExpression(state0, item.Item1);
            if (res == null)
              yield break;
            if (res is LiteralExpr && 
              (res as LiteralExpr).Value is bool && 
              (bool)(res as LiteralExpr).Value){
              counter++;
              var state = state0.Copy();
              var ifChoice = this.Copy();
              ifChoice.InitBasicFrameCtrl(item.Item2, partial, null, VerifyN);
              state.AddNewFrame(ifChoice);
              yield return state;
            }
          }
        }
        //no condition can be found, then do nothing
        if (counter == 0)
          yield return state0.Copy();
      }
    }
  }
}