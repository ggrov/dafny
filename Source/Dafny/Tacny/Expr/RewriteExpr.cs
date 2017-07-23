using Microsoft.Boogie;
using System;
using System.Collections.Generic;
using System.Linq;
using System.Numerics;
using System.Reflection;
using System.Security.Policy;


namespace Microsoft.Dafny.Tacny.Expr {

  public class IllFormedExpr : Exception
  {
    public IllFormedExpr(string message) : base(message) {
    }
  }


  class EvalExpr : SimpExpr{
    protected EvalExpr(ProofState state) : base(state){}

    internal static bool EqLiteralExprs(LiteralExpr e0, LiteralExpr e1){
      if (e0.Value is bool && e1.Value is bool){
        return ((bool)e0.Value) == ((bool)e1.Value);
      } else if (e0.Value is int && e1.Value is int){
        return ((int) e0.Value) == ((int) e1.Value);
      } else if (e0.Value is BigInteger && e1.Value is BigInteger){
         return BigInteger.Compare((BigInteger)e0.Value, (BigInteger)e1.Value) == 0;
      } else if (e0.Value is string && e1.Value is string){
        return ((string) e0.Value).Equals((string)e1.Value);
      }
      
      return false;
    }

    internal static bool EqExpr(Expression e0, Expression e1){
      if (e0 is LiteralExpr && e1 is LiteralExpr){
        return EqLiteralExprs((LiteralExpr) e0, (LiteralExpr) e1);
      }
      
      return false;
    }

    public static List<Expression> SetSubstract(List<Expression> l, List<Expression> r) {
      var ret = new List<Expression>();
      var newL = SetNormalise(l);

      foreach(var item in newL) {
        if(r.Find(y => EqExpr(item, y)) == null)
          ret.Add(item);
      }
      return ret;
    }

    public static List<Expression> SetIntersect(List<Expression> l, List<Expression> r) {
      var ret = new List<Expression>();
      var newL = SetNormalise(l);

      foreach (var item in newL) {
        if (r.Find(y => EqExpr(item, y)) != null)
          ret.Add(item);
      }
      return ret;
    }

    public static List<Expression> SetNormalise(List<Expression> l){
      var newL = new List<Expression>();
      foreach (var item in l){
        if(newL.Find(y => EqExpr(item, y)) == null)
          newL.Add(item);
      }
      return newL;
    }

    internal bool ContainsExprList(List<Expression> l, Expression e)
    {
      var ret = l.Find(x => EqExpr(e, x));
      return ret != null;
    }

    public static List<Expression> RemoveDup(List<Expression> l) {
      var newL = new List<Expression>();
      var dupL = new List<Expression>();
      foreach (var item in l) {
        if (l.FindAll(y => EqExpr(item, y)).Count <= 1)
          newL.Add(item);
        else {
          if (dupL.Find(y => EqExpr(item, y)) == null) {
            newL.Add(item);
            dupL.Add(item);
          }
        }
      }
      return newL;
    }

 
    public override Expression CloneExpr(Expression expr){
      if (expr is UnaryOpExpr){
        var unaryExpr = expr as UnaryOpExpr;
        var e = CloneExpr(unaryExpr.E);
        switch(unaryExpr.Op) {
          case UnaryOpExpr.Opcode.Not:
            if(e is LiteralExpr && (e as LiteralExpr).Value is bool ) {
              var value = !(bool)(e as LiteralExpr).Value;
              return new LiteralExpr(new Token(TacnyDriver.TacticCodeTokLine, 0), value);
            }
            break;
          case UnaryOpExpr.Opcode.Cardinality:
            if (e is SeqDisplayExpr) {
              var value = (e as SeqDisplayExpr).Elements.Count;
              return new LiteralExpr(new Token(TacnyDriver.TacticCodeTokLine, 0), value);
            }
            break;
          default:
            break;
        }
        return new UnaryOpExpr(new Token(TacnyDriver.TacticCodeTokLine,0),
          unaryExpr.Op, e);
      } else if (expr is BinaryExpr){
        var binExpr = expr as BinaryExpr;
        var e0 = CloneExpr(binExpr.E0);
        var e1 = CloneExpr(binExpr.E1);

        switch(binExpr.Op) {
          case BinaryExpr.Opcode.And:
            if (e0 is LiteralExpr && e1 is LiteralExpr &&
                (e0 as LiteralExpr).Value is bool &&
                (e1 as LiteralExpr).Value is bool){
              var value =
                (bool)(e0 as LiteralExpr).Value && (bool)(e1 as LiteralExpr).Value;
              return new LiteralExpr(new Token(TacnyDriver.TacticCodeTokLine, 0), value);
            }
            break;
          case BinaryExpr.Opcode.Or:
            if(e0 is LiteralExpr && e1 is LiteralExpr &&
                (e0 as LiteralExpr).Value is bool &&
                (e1 as LiteralExpr).Value is bool) {
              var value =
                (bool)(e0 as LiteralExpr).Value || (bool)(e1 as LiteralExpr).Value;
              return new LiteralExpr(new Token(TacnyDriver.TacticCodeTokLine, 0), value);
            }
            break;
          case BinaryExpr.Opcode.Le:
            if(e0 is LiteralExpr && e1 is LiteralExpr &&
               (e0 as LiteralExpr).Value is BigInteger &&
               (e1 as LiteralExpr).Value is BigInteger ) {
              var value =
                (BigInteger) (e0 as LiteralExpr).Value <
                (BigInteger) (e1 as LiteralExpr).Value;
                
              return new LiteralExpr(new Token(TacnyDriver.TacticCodeTokLine, 0), value);
            }
            break;
          case BinaryExpr.Opcode.Lt:
            if(e0 is LiteralExpr && e1 is LiteralExpr &&
              (e0 as LiteralExpr).Value is BigInteger &&
              (e1 as LiteralExpr).Value is BigInteger) {
              var value =
                (BigInteger)(e0 as LiteralExpr).Value <=
                (BigInteger)(e1 as LiteralExpr).Value;

              return new LiteralExpr(new Token(TacnyDriver.TacticCodeTokLine, 0), value);
            }
            break;
          case BinaryExpr.Opcode.Ge:
            if(e0 is LiteralExpr && e1 is LiteralExpr &&
              (e0 as LiteralExpr).Value is BigInteger &&
              (e1 as LiteralExpr).Value is BigInteger) {
              var value =
                (BigInteger)(e0 as LiteralExpr).Value >
                (BigInteger)(e1 as LiteralExpr).Value;

              return new LiteralExpr(new Token(TacnyDriver.TacticCodeTokLine, 0), value);
            }
            break;
          case BinaryExpr.Opcode.Gt:
            if(e0 is LiteralExpr && e1 is LiteralExpr &&
              (e0 as LiteralExpr).Value is BigInteger &&
              (e1 as LiteralExpr).Value is BigInteger) {
              var value =
                (BigInteger)(e0 as LiteralExpr).Value >=
                (BigInteger)(e1 as LiteralExpr).Value;

              return new LiteralExpr(new Token(TacnyDriver.TacticCodeTokLine, 0), value);
            }
            break;
          case BinaryExpr.Opcode.Add:
            if (e0 is LiteralExpr && e1 is LiteralExpr &&
              (e0 as LiteralExpr).Value is BigInteger &&
              (e1 as LiteralExpr).Value is BigInteger){
              var value =  BigInteger.Add(
                (BigInteger) (e0 as LiteralExpr).Value,
                (BigInteger) (e1 as LiteralExpr).Value
                );
              return new LiteralExpr(new Token(TacnyDriver.TacticCodeTokLine,0), value);
            } else if (e0 is SeqDisplayExpr && e1 is SeqDisplayExpr) {

              var newEles = new List<Expression>();
              newEles.AddRange((e0 as SeqDisplayExpr).Elements);
              newEles.AddRange((e1 as SeqDisplayExpr).Elements);
               
              return new SeqDisplayExpr(new Token(TacnyDriver.TacticCodeTokLine,0), newEles);
            }
            break;
          case BinaryExpr.Opcode.Sub:
            if (e0 is LiteralExpr && e1 is LiteralExpr &&
             (e0 as LiteralExpr).Value is BigInteger &&
             (e1 as LiteralExpr).Value is BigInteger) {
              var value = BigInteger.Subtract(
                (BigInteger)(e0 as LiteralExpr).Value,
                (BigInteger)(e1 as LiteralExpr).Value
                );
              return new LiteralExpr(new Token(TacnyDriver.TacticCodeTokLine, 0), value);
            } 
            break;
          case BinaryExpr.Opcode.Mul:
             if (e0 is SeqDisplayExpr && e1 is SeqDisplayExpr) {
              var newEles = SetIntersect((e0 as SeqDisplayExpr).Elements, (e1 as SeqDisplayExpr).Elements);
              return new SeqDisplayExpr(new Token(TacnyDriver.TacticCodeTokLine, 0), newEles);
            }
            break;
          case BinaryExpr.Opcode.In:
            if (e0 is LiteralExpr && e1 is SeqDisplayExpr) {
             var value = ContainsExprList((e1 as SeqDisplayExpr).Elements, e0);
              return new LiteralExpr(new Token(TacnyDriver.TacticCodeTokLine, 0), value);
            }
            break;
          case BinaryExpr.Opcode.NotIn:
            if (e0 is LiteralExpr && e1 is SeqDisplayExpr) {
              var value = ContainsExprList((e1 as SeqDisplayExpr).Elements, e0);
              return new LiteralExpr(new Token(TacnyDriver.TacticCodeTokLine, 0), !value);
            }
            break;
          case BinaryExpr.Opcode.Eq:
            if(e0 is StringLiteralExpr && e1 is StringLiteralExpr &&
              ((e0 as StringLiteralExpr).Value is String)){
              var s = (e0 as StringLiteralExpr).Value as String;
              return new LiteralExpr(new Token(TacnyDriver.TacticCodeTokLine, 0),
                s != null && s.Equals((e1 as StringLiteralExpr).Value as string)
                );
            }
            break;
          default:
            break;
        }
        return new BinaryExpr(new Token(TacnyDriver.TacticCodeTokLine, 0),
               binExpr.Op, e0, e1);
      } else if (expr is SeqSelectExpr) {
        var selExpr = expr as SeqSelectExpr;
        var seq = CloneExpr(selExpr.Seq);
        var e0 = CloneExpr(selExpr.E0);
        var e1 = CloneExpr(selExpr.E1);

        if (seq is LiteralExpr)
          throw new IllFormedExpr("Syntax Error: Expect sequence in sequence selector.");
        if (e0 is LiteralExpr) {
          if (!((e0 as LiteralExpr).Value is BigInteger))
            throw new IllFormedExpr("Syntax Error: Expect lower bound to be int.");
          if (seq is SeqDisplayExpr) {
            if ((BigInteger)(e0 as LiteralExpr).Value >= (seq as SeqDisplayExpr).Elements.Count)
              throw new IllFormedExpr("Syntax Error: lower bound is out of scope.");

            if (e1 == null) {
              var value = (seq as SeqDisplayExpr).Elements[(int)((BigInteger)(e0 as LiteralExpr).Value)];
              return value;
            } else if (e1 is LiteralExpr) {
              if (!((e1 as LiteralExpr).Value is BigInteger))
                throw new IllFormedExpr("Syntax Error: Expect upper bound to be int.");
              if ((BigInteger)(e1 as LiteralExpr).Value > (seq as SeqDisplayExpr).Elements.Count ||
                (BigInteger)(e1 as LiteralExpr).Value < (BigInteger)(e0 as LiteralExpr).Value)
                throw new IllFormedExpr("Syntax Error: upper bound is out of scope.");
               var cnt = (BigInteger) (e1 as LiteralExpr).Value - (BigInteger) (e0 as LiteralExpr).Value;
               var value = (seq as SeqDisplayExpr).Elements.GetRange((int)((BigInteger)(e1 as LiteralExpr).Value), (int)cnt);
              return new SeqDisplayExpr(new Token(TacnyDriver.TacticCodeTokLine, 0), value);
            }

          }
        }
        //if(e1 is LiteralExpr && e1.Type.)
      }

      return base.CloneExpr(expr);
    }

    public static Expression EvalTacticExpression(ProofState state, Expression expr){
      try {
        var rewriter = new EvalExpr(state);
        return rewriter.CloneExpr(expr);
      } catch (IllFormedExpr e) {
        state.ReportTacticError(expr.tok, e.Message);
        return null;
      }
    }
  }

  /// <summary>
  /// only simplify tactic expression
  /// </summary>
  class SimpExpr : Cloner {
    private readonly ProofState _state;

    protected SimpExpr(ProofState state) {
      _state = state;
    }


    internal bool IsTVar(Expression expr) {
      string key = null;
      if(expr is TacticLiteralExpr)
        key = (string)((TacticLiteralExpr)expr).Value;
      else if(expr is NameSegment)
        key = (expr as NameSegment).Name;

      return key == null ? false : _state.ContainTVal(key);
    }

    internal Expression EvalTVar(Expression expr, bool deref) {

      string key = null;
      if(expr is TacticLiteralExpr)
        key = (string)((TacticLiteralExpr)expr).Value;
      else if(expr is NameSegment)
        key = (expr as NameSegment).Name;

      if(key == null) {
        throw new Exception("expression for TVar can only be TacticLiteralExpr or NameSegment: " + expr);
      }

      var value = _state.GetTVarValue(key);
      if(deref && value is TacticLiteralExpr && IsTVar(value as TacticLiteralExpr))
        return EvalTVar(value as TacticLiteralExpr, true);
      else
        return value;
    }

    internal bool IsEAtmoicCall(ExprDotName aps) {
      return EAtomic.EAtomic.IsEAtomicSig(Util.GetSignature(aps));
    }

    internal bool IsEAtmoicCall(ApplySuffix aps) {
      return EAtomic.EAtomic.IsEAtomicSig(Util.GetSignature(aps));
    }

    internal Expression EvalEAtomExpr(Expression expr) {
      string sig = null;
      if(expr is ExprDotName) {
        sig = Util.GetSignature(expr as ExprDotName);
      } else if(expr is ApplySuffix) {
        sig = Util.GetSignature(expr as ApplySuffix);
      }
      if(sig != null) {
        var types = Assembly.GetAssembly(typeof(EAtomic.EAtomic)).GetTypes()
          .Where(t => t.IsSubclassOf(typeof(EAtomic.EAtomic)));
        foreach(var eType in types) {
          var eatomInst = Activator.CreateInstance(eType) as EAtomic.EAtomic;
          if(sig == eatomInst?.Signature) {
            //TODO: validate input countx
            return eatomInst?.Generate(expr, _state);
          }
        }
        return null;
      }
      return null;
    }
  

    internal bool IsETacticCall(ApplySuffix aps){
      //TODO: this is for expression tactic call, e.g. funtion tactic
      return false;
    }

    internal Expression EvalETacticCall(ApplySuffix aps){
      //fucntion expression call, yet to be supported
      throw new NotImplementedException();
    }

    public static Expression UnfoldTacticProjection(ProofState state, Expression expr){
      var e = new SimpExpr(state);
      if (e.IsTVar(expr))
        return e.EvalTVar(expr, true);
      else{
        var suffix = expr as ApplySuffix;
        if (suffix != null){
          var aps = suffix;
          if (e.IsEAtmoicCall(aps))
            return e.EvalEAtomExpr(aps);
          else if (e.IsETacticCall(aps))
            throw new NotImplementedException();
        }
      }
      //TODO: evaluate expr as boolean and return as BooleanRet
      return null;
    }

    public static Statement SimpTacticExpr(ProofState state, Statement stmt){
      var simplifier = new SimpExpr(state);
      return simplifier.CloneStmt(stmt);
    }

    public static Expression SimpTacticExpr(ProofState state, Expression expr){
      var simplifier = new SimpExpr(state);
      var ret = simplifier.CloneExpr(expr);
      return ret;
    }

    public override Expression CloneApplySuffix(ApplySuffix e){
      if (IsEAtmoicCall(e)){
        return EvalEAtomExpr(e);
      }
      else if (IsETacticCall(e)){
        return (EvalETacticCall(e) as Expression);
      }
      else
        return base.CloneApplySuffix(e);
    }


    public override Expression CloneExpr(Expression expr){
      if (IsTVar(expr)){
        var ret =  EvalTVar(expr, true);
        return ret != null ? ret : base.CloneExpr(expr);
      } else if (expr is ExprDotName){
        if (IsEAtmoicCall(expr as ExprDotName)){
          return EvalEAtomExpr(expr as ExprDotName);
        }
        else
          return base.CloneExpr(expr);
      }
      else if (expr is ApplySuffix){
        var suffix = expr as ApplySuffix;
        return CloneApplySuffix(suffix);
      }
      else
        return base.CloneExpr(expr);
    }
  }

  class TacticAppUnfolder : Cloner {
    private ProofState _state;
    private ApplySuffix _aps;
    private Expression _destExpr;

    private TacticAppUnfolder(ProofState ps, ApplySuffix aps, Expression code) {
      _state = ps;
      _aps = aps;
      _destExpr = code;
    }

    public override Expression CloneApplySuffix(ApplySuffix e) {
      if(e.tok.pos == _aps.tok.pos) {
        return _destExpr;
      }
      return base.CloneApplySuffix(e);
    }


    public override Expression CloneExpr(Expression expr) {
      var suffix = expr as ApplySuffix;
      if(suffix != null)
        return CloneApplySuffix(suffix);

      return base.CloneExpr(expr);
    }

    public static Statement UnfoldTacticExprInStmt(ProofState ps, Statement stmt, 
      ApplySuffix aps, Expression code) {
      var unfolder = new TacticAppUnfolder(ps, aps, code);
      return unfolder.CloneStmt(stmt);
    }
  }
  class TacticAppExprFinder : Cloner {
    private ProofState _state;
    private ApplySuffix _aps;

    private TacticAppExprFinder(ProofState ps) {
      _state = ps;
    }

    public override Expression CloneApplySuffix(ApplySuffix e) {
      if(_state.IsTacticCall(e)) {
        _aps = base.CloneApplySuffix(e) as ApplySuffix;
        return _aps;
      }
       return base.CloneApplySuffix(e);
    }


    public override Expression CloneExpr(Expression expr) {
      var suffix = expr as ApplySuffix;
      if(suffix != null)
        return CloneApplySuffix(suffix);

        return base.CloneExpr(expr);
    }
 
    public static ApplySuffix GetTacticAppExpr(ProofState ps, Statement stmt) {
      var finder = new TacticAppExprFinder(ps);
      finder.CloneStmt(stmt);
      return finder._aps;
    }

    public static ApplySuffix GetTacticAppExpr(ProofState ps, Expression expr) {
      var finder = new TacticAppExprFinder(ps);
      finder.CloneExpr(expr);
      return finder._aps;
    }
  }

  class RenameVar : Cloner {

    private readonly Dictionary<string, string> _renames;

    public RenameVar() {
      _renames = new Dictionary<string, string>();
    }

    public void AddRename(String before, String after) {
      _renames.Add(before,after);
    }

    
    public override BoundVar CloneBoundVar(BoundVar bv) {
      String nm;
      var name = _renames.TryGetValue(bv.Name, out nm) ? nm : bv.Name;
      var bvNew = new BoundVar(Tok(bv.tok), name, CloneType(bv.Type)) {IsGhost = bv.IsGhost};
      return bvNew;
    }
 
    public override Expression CloneNameSegment(Expression expr) {
      var e = (NameSegment) expr;
      String nm;
      var name = _renames.TryGetValue(e.Name, out nm) ? nm : e.Name;
      return new NameSegment(Tok(e.tok), name,
        e.OptTypeArguments?.ConvertAll(CloneType));
    }
  }

}