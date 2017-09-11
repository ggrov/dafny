using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.IO.Pipes;
using System.Linq;
using Microsoft.Boogie;
using Microsoft.Dafny.Tacny.Expr;


namespace Microsoft.Dafny.Tacny.Atomic {
  class SuchThatAtomic : Atomic{
    public override string Signature => ":|";
    public override int ArgsCount => -1;
    private string name;
    public override IEnumerable<ProofState> Generate(Statement statement, ProofState state){
      AssignSuchThatStmt suchThat = null;

      if (statement is AssignSuchThatStmt){
        suchThat = (AssignSuchThatStmt) statement;
      } else {
        state.ReportTacticError(statement.Tok, "Unexpected statement for suchthat(:|)");
        yield break;
      }

      var nameExpr = suchThat.Lhss[0]; 
      if (nameExpr is IdentifierExpr) {
          var id = nameExpr as IdentifierExpr;
          name = id.Name;
        } else if (nameExpr is NameSegment) {
        var id = nameExpr as NameSegment;
        if (!state.ContainTVal(id.Name)) {
          state.ReportTacticError(statement.Tok, "Fail to register variable " + id.Name);
          yield break;
        } else {
          name = id.Name;
        }
      } else {
        state.ReportTacticError(statement.Tok, "Fail to register variable.");
        yield break;
      }

      string errInfo;
      //  var expr = Expr.SimpExpr.SimpTacticExpr(state, suchThat.Expr);
      var expr = suchThat.Expr;
      /*
      if (!CheckExpr(expr, out errInfo)) {
        state.ReportTacticError(statement.Tok, "Unexpceted expression in suchthat statement: " + errInfo);
        yield break;
      }*/
      Expression pos, neg, pred;
      if (!RewriteExpr(expr as BinaryExpr, out pos, out neg, out pred)){
        state.ReportTacticError(expr.tok, "Syntax error in Suchthat expression.");
        yield break;
      }
      if (pos != null) {
        pos = EvalExpr.EvalTacticExpression(state, pos);
        if (pos == null)
          yield break;
      }

      if (neg != null) {
        neg = EvalExpr.EvalTacticExpression(state, neg);
        if (neg == null)
          yield break;
      }

      if (pos == null) {
        state.ReportTacticError(statement.Tok, "Suchthat expression is evaluated as an empty sequence.");
        yield break;
      }
      if (pos is SeqDisplayExpr) {
        if (neg != null && !(neg is SeqDisplayExpr)) {
          state.ReportTacticError(statement.Tok, "Unexpceted expression in suchthat statement.");
          yield break;
        }
        var eles = EvalExpr.RemoveDup((pos as SeqDisplayExpr).Elements);
        if(eles.Count == 0) {
          state.ReportTacticError(statement.Tok, "The expression is evaluated as an empty set.");
          yield break;
        }
      
        foreach (var item in eles) {
          var copy = state.Copy();
          copy.UpdateTacticVar(name, item);

          if (neg != null) {
            var inNeg = EvalExpr.EvalTacticExpression(state,
              new BinaryExpr(new Token(TacnyDriver.TacticCodeTokLine, 0),
                BinaryExpr.Opcode.In, item, neg));
            if (inNeg is LiteralExpr && (inNeg as LiteralExpr).Value is bool) {
              if ((bool) (inNeg as LiteralExpr).Value) continue;
            } else {
              throw new Exception("A unhandled error orrurs when evaluating a suchtaht statement");
            }
          }
          if (pred != null){
            var value = new BinaryExpr(new Token(TacnyDriver.TacticCodeTokLine, 0), 
              BinaryExpr.Opcode.Eq, suchThat.Lhss[0].Copy(), item);
            var candidate = new BinaryExpr(new Token(TacnyDriver.TacticCodeTokLine, 0), BinaryExpr.Opcode.Add, value, pred);
            var res = EvalExpr.EvalTacticExpression(copy, pred);
            Console.WriteLine(Printer.ExprToString(res));
            if(res is LiteralExpr && (res as LiteralExpr).Value is bool) {
              if(!(bool)(res as LiteralExpr).Value)
                continue;
            } else {
              throw new Exception("A unhandled error orrurs when evaluating a suchtaht statement");
            }
          }
          
          yield return copy;
        }
      } else {
        state.ReportTacticError(statement.Tok, "Unexpceted expression in suchthat statement.");
        yield break;
      }  
    }

    internal void IntersectSetExpr(Expression e1, Expression e2, out Expression expr) {
      if (e1 != null && e2 != null)
        expr = new BinaryExpr(new Token(TacnyDriver.TacticCodeTokLine, 0),
              BinaryExpr.Opcode.Mul, e1, e2);
      else if (e1 == null && e2 == null)
        expr = null;
      else {
        expr = e1 ?? e2;
      }
    }
    internal void UnionExpr(Expression e1, Expression e2, out Expression expr)
    {
      if (e1 != null && e2 != null)
        expr = new BinaryExpr(new Token(TacnyDriver.TacticCodeTokLine, 0),
              BinaryExpr.Opcode.Add, e1, e2);
      else if (e1 == null && e2 == null)
        expr =  null;
      else {
        expr = e1 ?? e2;
      }
    }
    
    /// <summary>
    /// remove &&, and change in --> union, notin --> setminus
    /// </summary>
    /// <returns></returns>
    internal bool RewriteExpr(BinaryExpr destExpr, out Expression posExpr, out Expression negExpr, 
      out Expression pred)
    {
      if (destExpr == null){
        posExpr = null;
        negExpr = null;
        pred = null;

        return false;
      }
      else{
        switch (destExpr.Op){
          case BinaryExpr.Opcode.And:
            Expression posExpr1, posExpr2, negExpr1, negExpr2, pred1, pred2;
            if (RewriteExpr(destExpr.E0 as BinaryExpr, out posExpr1, out negExpr1, out pred1)){
              if (RewriteExpr(destExpr.E1 as BinaryExpr, out posExpr2, out negExpr2, out pred2)){
                IntersectSetExpr(posExpr1, posExpr2, out posExpr);
                UnionExpr(negExpr1, negExpr2, out negExpr);
                UnionExpr(pred1, pred2, out pred);
                break;
              }
            }
            posExpr = null;
            negExpr = null;
            pred = null;
            return false;
          case BinaryExpr.Opcode.In:
            posExpr = destExpr.E1;
            negExpr = null;
            pred = null;
            break;
          case BinaryExpr.Opcode.NotIn:
            negExpr = destExpr.E1;
            posExpr = null;
            pred = null;
            break;
          default:
            negExpr = null;
            posExpr = null;
            pred = destExpr;
            break;
          //throw new Exception("suchthat error: not supported expression");
        }
        return true;
      }
    }
    internal bool CheckExpr(Expression expr, out string err)
    {
      if (expr is BinaryExpr) {
        var destExpr = expr as BinaryExpr;
        string op1, op2;
        switch (destExpr.Op) {
          case BinaryExpr.Opcode.And:
            var ret1 = CheckExpr(destExpr.E0, out op1);
            var ret2 = CheckExpr(destExpr.E1, out op2);
            err = op1 + " " + op2;
            return ret1 && ret2;
          case BinaryExpr.Opcode.In:
          case BinaryExpr.Opcode.NotIn:
            if (name.Equals(Printer.ExprToString(destExpr.E0))) {
              err = "";
              return true;
            } else {
             
              err = Printer.ExprToString(destExpr.E0);
              return false;
            }
          default:
            err = destExpr.Op.ToString();
            return false;
        }
      } else {
        err = Printer.ExprToString(expr);
        return false;
      }
    }
    }
}

