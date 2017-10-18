using System.Collections.Generic;
using System.Linq;
using Microsoft.Dafny.Tacny.Expr;

namespace Microsoft.Dafny.Tacny.EAtomic {
  
  class Operator : EAtomic {
    public override string Signature => "operator";
    public override int ArgsCount => 0;

    internal string GetOp(Expression expr, ProofState state) {
      if(expr is UnaryOpExpr) {
        var unaryExpr = expr as UnaryOpExpr;
        switch(unaryExpr.Op) {
          case UnaryOpExpr.Opcode.Not:
            return "!";
          case UnaryOpExpr.Opcode.Cardinality:
            return "|_|";
          default:
            return null;
        }
      } else if(expr is BinaryExpr) {
        var binExpr = expr as BinaryExpr;
        switch(binExpr.Op) {
          case BinaryExpr.Opcode.And:
            return "&&";
          case BinaryExpr.Opcode.Or:
            return "||";
          case BinaryExpr.Opcode.Le:
            return "<=";
          case BinaryExpr.Opcode.Lt:
            return "<";
          case BinaryExpr.Opcode.Ge:
            return ">=";
          case BinaryExpr.Opcode.Gt:
            return ">";
          case BinaryExpr.Opcode.Add:
            return "+";
          case BinaryExpr.Opcode.Sub:
            return "1";
          case BinaryExpr.Opcode.Mul:
            return "*";
          case BinaryExpr.Opcode.In:
            return "in";
          case BinaryExpr.Opcode.NotIn:
            return "!in";
          default:
            break;
        }
      }
      state.ReportTacticError(expr.tok, "Can not get the opertor: unsupported operator.");
      return null;
    }

    public override Expression Generate(Expression expr, ProofState proofState) {
      if(expr is ExprDotName) {
        var src = Expr.SimpExpr.SimpTacticExpr(proofState, (expr as ExprDotName).Lhs);
        var ret = GetOp(src, proofState);
        return ret != null ?
          new StringLiteralExpr(new Boogie.Token(TacnyDriver.TacticCodeTokLine, 0), ret, false) :
          null;
      } else {
        proofState.ReportTacticError(expr.tok, "Illform for \"operator\", expect form in the shape of *.operator");
        return null;
      }
    }
  }
  class Args : EAtomic {
    public override string Signature => "args";
    public override int ArgsCount => 0;

    internal List<Expression> GetArgs(Expression expr, ProofState state) {
      if(expr is UnaryOpExpr) {
        var uExpr = expr as UnaryExpr;
        return new List<Expression>() { uExpr.E };

      } else if(expr is BinaryExpr) {
        var binExpr = expr as BinaryExpr;
        var ret = new List<Expression>();
        ret.Add(binExpr.E0);
        ret.Add(binExpr.E1);
        return ret;
      } else if(expr is TernaryExpr) {
        var tExpr = expr as TernaryExpr;
        var ret = new List<Expression>();
        ret.Add(tExpr.E0);
        ret.Add(tExpr.E1);
        ret.Add(tExpr.E2);
        return ret;
      }
      state.ReportTacticError(expr.tok, "Can not get the args: unsupported operator.");
      return null;
    }

    public override Expression Generate(Expression expr, ProofState proofState) {
      if(expr is ExprDotName) {
        var src = Expr.SimpExpr.SimpTacticExpr(proofState, (expr as ExprDotName).Lhs);
        var ret = GetArgs(src, proofState);
        return ret != null ?
          GenerateEAtomExprAsSeq(ret): null;
      } else {
        proofState.ReportTacticError(expr.tok, "Illform for \"args\", expect form in the shape of *.args");
        return null;
      }
    }
  }
  class Subterms : EAtomic {
    public override string Signature => "subterms";
    public override int ArgsCount => 0;

    internal void GetSubterms(IEnumerable<Expression> src, List<Expression> dest) {
      foreach(var expr in src) {
        dest.Add(expr);
        GetSubterms(expr.SubExpressions, dest);
      }
    }
    public override Expression Generate(Expression expr, ProofState proofState) {
      if(expr is ExprDotName) {
        var src = Expr.SimpExpr.SimpTacticExpr(proofState, (expr as ExprDotName).Lhs);
        var el = new List<Expression>();
        GetSubterms(src.SubExpressions, el);
        return GenerateEAtomExprAsSeq(el);
      } else {
        proofState.ReportTacticError(expr.tok, "Illform for \"subterms\", expect form in the shape of *.subterms");
        return null;
      }
    }
  }

  class Consts : EAtomic {
    public override string Signature => "consts";
    public override int ArgsCount => 0;

    internal void GetConsts(IEnumerable<Expression> src, List<Expression> dest) {
      foreach(var expr in src) {
        if(expr is Dafny.LiteralExpr)
          dest.Add(expr);
        GetConsts(expr.SubExpressions, dest);
      }
    }
    public override Expression Generate(Expression expr, ProofState proofState) {
      if(expr is ExprDotName) {
        var src = Expr.SimpExpr.SimpTacticExpr(proofState, (expr as ExprDotName).Lhs);
        var el = new List<Expression>();
        GetConsts(src.SubExpressions, el);
        return GenerateEAtomExprAsSeq(el);
      } else {
        proofState.ReportTacticError(expr.tok, "Illform for \"consts\", expect form in the shape of *.consts");
        return null;
      }
    }
  }


  class IfConst : EAtomic {
    public override string Signature => "const?";
    public override int ArgsCount => 0;

    internal void GetConsts(IEnumerable<Expression> src, List<Expression> dest) {
      foreach(var expr in src) {
        if(expr is Dafny.LiteralExpr)
          dest.Add(expr);
        GetConsts(expr.SubExpressions, dest);
      }
    }
    public override Expression Generate(Expression expr, ProofState proofState) {
      if(expr is ExprDotName) {
        var src = Expr.SimpExpr.SimpTacticExpr(proofState, (expr as ExprDotName).Lhs);
        var el = new List<Expression>();
        GetConsts(src.SubExpressions, el);
        if(el.Capacity > 0)
          return new LiteralExpr(new Boogie.Token(TacnyDriver.TacticCodeTokLine, 0), true);
        else
          return new LiteralExpr(new Boogie.Token(TacnyDriver.TacticCodeTokLine, 0), false);
      } else {
        proofState.ReportTacticError(expr.tok, "Illform for \"const?\", expect form in the shape of *.const?");
        return null;
      }
    }
  }
  class IfOperator : EAtomic {
    public override string Signature => "operator?";
    public override int ArgsCount => 0;
    
    public override Expression Generate(Expression expr, ProofState proofState) {
      if(expr is ExprDotName) {
        var src = Expr.SimpExpr.SimpTacticExpr(proofState, (expr as ExprDotName).Lhs);

        if(src is TernaryExpr || src is BinaryExpr || src is UnaryExpr)
          return new LiteralExpr(new Boogie.Token(TacnyDriver.TacticCodeTokLine, 0), true);
        else
          return new LiteralExpr(new Boogie.Token(TacnyDriver.TacticCodeTokLine, 0), false);
      } else {
        proofState.ReportTacticError(expr.tok, "Illform for \"const?\", expect form in the shape of *.const?");
        return null;
      }
    }
  }
  class IfDatatype : EAtomic {
    public override string Signature => "datatype?";
    public override int ArgsCount => 0;

    public override Expression Generate(Expression expr, ProofState proofState) {
      if(expr is ExprDotName) {
        var src = Expr.SimpExpr.SimpTacticExpr(proofState, (expr as ExprDotName).Lhs);

        if(src is NameSegment && proofState.ContainDafnyVar(src as NameSegment)) {
          var type = proofState.GetDafnyVarType((src as NameSegment).Name);
          if (type is UserDefinedType)
            return new LiteralExpr(new Boogie.Token(TacnyDriver.TacticCodeTokLine, 0), true);
        }
        return new LiteralExpr(new Boogie.Token(TacnyDriver.TacticCodeTokLine, 0), false);
      } else {
        proofState.ReportTacticError(expr.tok, "Illform for \"const?\", expect form in the shape of *.const?");
        return null;
      }
    }
  }
/*
  class IfRecursive : EAtomic {
    public override string Signature => "recursive?";
    public override int ArgsCount => 0;

    public override Expression Generate(Expression expr, ProofState proofState) {
      if(expr is ExprDotName){
        var src = Expr.SimpExpr.SimpTacticExpr(proofState, (expr as ExprDotName).Lhs);
          return new LiteralExpr(new Boogie.Token(TacnyDriver.TacticCodeTokLine, 0), true);
          //return new LiteralExpr(new Boogie.Token(TacnyDriver.TacticCodeTokLine, 0), false);
      } else {
        proofState.ReportTacticError(expr.tok, "Illform for \"const?\", expect form in the shape of *.const?");
        return null;
      }
    }
  }
  */

  class IfUnfold : EAtomic {
    public override string Signature => "unfold?";
    public override int ArgsCount => 0;

    public override Expression Generate(Expression expr, ProofState proofState) {
      if(expr is ExprDotName) {
        //ApplySurffix and E0 lhs is NameSegment and string is a function
        var src = Expr.SimpExpr.SimpTacticExpr(proofState, (expr as ExprDotName).Lhs);
        if (src is ApplySuffix){
          var aps = src as ApplySuffix;
          if (aps.Lhs is NameSegment &&
             proofState.Members.ContainsKey((aps.Lhs as NameSegment).Name) &&
             proofState.Members[(aps.Lhs as NameSegment).Name] is Function)

            return new LiteralExpr(new Boogie.Token(TacnyDriver.TacticCodeTokLine, 0), true);
        }
        return new LiteralExpr(new Boogie.Token(TacnyDriver.TacticCodeTokLine, 0), false);

      } else {
        proofState.ReportTacticError(expr.tok, "Illform for \"unfold?\", expect form in the shape of *.unfold?");
        return null;
      }
    }
  }

  class Unfold : EAtomic {
    public override string Signature => "unfold";
    public override int ArgsCount => 0;

    public override Expression Generate(Expression expr, ProofState proofState) {
      if(expr is ExprDotName) {
        //ApplySurffix and E0 lhs is NameSegment and string is a function
        var src = Expr.SimpExpr.SimpTacticExpr(proofState, (expr as ExprDotName).Lhs);
        if(src is ApplySuffix) {
          var aps = src as ApplySuffix;
          if (aps.Lhs is NameSegment &&
              proofState.Members.ContainsKey((aps.Lhs as NameSegment).Name) &&
              proofState.Members[(aps.Lhs as NameSegment).Name] is Function){
            return InstVar.UnfoldFunction(src as ApplySuffix, proofState);
          }
        }
        proofState.ReportTacticError(expr.tok, "Expression can not be unfolded.");
        return null;

      } else {
        proofState.ReportTacticError(expr.tok, "Illform for \"unfold\", expect form in the shape of *.unfold");
        return null;
      }
    }
  }

}
