using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
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

      //expr should be in the shape of x in|notin set [&& ...]
      string errInfo;
      if (!CheckExpr(suchThat.Expr, out errInfo)) {
        state.ReportTacticError(statement.Tok, "Unexpceted expression in suchthat statement: " + errInfo);
        yield break;
      }
      Expression pos, neg;
      RewriteExpr(suchThat.Expr as BinaryExpr, out pos, out neg);

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
          var copy = state.Copy();
          copy.UpdateTacticVar(name, item);
          Console.WriteLine(Printer.ExprToString(item));
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
    internal void UnionSetExpr(Expression e1, Expression e2, out Expression expr)
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
    internal void RewriteExpr(BinaryExpr destExpr, out Expression posExpr, out Expression negExpr)
    {

      switch (destExpr.Op) {
        case BinaryExpr.Opcode.And:
          Expression posExpr1, posExpr2, negExpr1, negExpr2;
          RewriteExpr(destExpr.E0 as BinaryExpr, out posExpr1, out negExpr1);
          RewriteExpr(destExpr.E1 as BinaryExpr, out posExpr2, out negExpr2);
          IntersectSetExpr(posExpr1, posExpr2, out posExpr);
          UnionSetExpr(negExpr1,negExpr2, out negExpr);
          break;
        case BinaryExpr.Opcode.In:
          posExpr = destExpr.E1;
          negExpr = null;
          break;
        case BinaryExpr.Opcode.NotIn:
          negExpr = destExpr.E1;
          posExpr = null;
          break;
        default:
          throw new Exception("suchthat error: not supported expression");
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

