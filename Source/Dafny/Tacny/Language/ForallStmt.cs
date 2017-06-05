using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;
using Microsoft.Boogie;
using Microsoft.Dafny.Tacny.Expr;


namespace Microsoft.Dafny.Tacny.Language {

  class ForallStmt : TacticFrameCtrl {

    private TacticForallStmt _stmt;
    private List<BoundVar> _vars;
    private Expression _range;
    private List<MaybeFreeExpression> _ens;


    public override IEnumerable<ProofState> EvalInit(Statement statement, ProofState state) {
      Contract.Assume(statement != null);
      Contract.Assume(statement is TacticForallStmt);

      _stmt = statement as TacticForallStmt;
 
      Contract.Assert(_stmt != null);

      // do basic simplification
      // maybe do a check and throw an error instead?  
      // fixme: error returns null!
      //var e = (ForallExpr) SimpTacticExpr.SimpTacExpr(state0, _stmt.Spec);
      var e = (ForallExpr) SimpExpr.SimpTacticExpr(state, _stmt.Spec);

      // var e = _stmt.Spec as ForallExpr;
      // to rename expressions
      RenameVar rn = new RenameVar();
      // to rename in the body of statement
      RenameVar rnBody = new RenameVar();
      List<String> usedVars = state.GetAllDafnyVars().Keys.ToList();
      usedVars.AddRange(state.GetAllTVars().Keys.ToList());
 
      //List<String> tmp = new List<string>();
      AllVars.DeclaredVars(_stmt.Body.Body[0],ref usedVars);

 
      
      if (_stmt.Attributes!= null&&_stmt.Attributes.Name.Equals("vars")) {
        var attrs = _stmt.Attributes.Args;
        for (int i = 0; i < attrs.Count; i++) {
          // todo: should really report an errors if first condition does not hold
          var segment = attrs[i] as NameSegment;
          if (segment != null && i < e.BoundVars.Count) {
            NameSegment ns = segment;
            String fv;
            if(GenFreeVar(ns.Name, usedVars, out fv))
            {
              rnBody.AddRename(ns.Name, fv);
            }
            rn.AddRename(e.BoundVars[i].Name, fv);
          } // else we should have an error
          _vars = new List<BoundVar>();
          foreach (BoundVar bv in e.BoundVars) {
            _vars.Add(rn.CloneBoundVar(bv));
          }
        }

      }else {
        _vars = e.BoundVars;
      }

      foreach(var tmp in _vars) {
        state.AddDafnyVar(tmp.Name, new ProofState.VariableData { Variable = tmp, Type = tmp.Type });
      }


      // we could even break  _ens into a set of all conjunctions?
      // what about forall x (forall y) x
      var expr = e.Term as BinaryExpr;
      if (expr != null && (expr.Op.Equals(BinaryExpr.Opcode.Imp))) {
        var be = expr;
        _range = rn.CloneExpr(be.E0);
        var t = new MaybeFreeExpression(rn.CloneExpr(be.E1));
        var l = new List<MaybeFreeExpression> {t};
        _ens = l;
      }else {
        _range = new LiteralExpr(_stmt.Tok, true);
        var t = new MaybeFreeExpression(rn.CloneExpr(e.Term));
        var l = new List<MaybeFreeExpression> {t};
        _ens = l;
      }

      // Note that we do not need to rename variables in the body (unless the variables in vars is changed)
      InitBasicFrameCtrl(new List<Statement>(), state.IsCurFramePartial(), null, VerifyN);

      state.AddNewFrame(this);

      var bodyFrame = new DefaultTacticFrameCtrl();

      var newBody = rnBody.CloneBlockStmt(_stmt.Body);
      bodyFrame.InitBasicFrameCtrl(newBody.Body, state.IsCurFramePartial(), null, VerifyN);
      bodyFrame.IsPartial = IsPartial;
      state.AddNewFrame(bodyFrame);

      yield return state;
    }


    // not sure about this?
    public override bool EvalTerminated(bool childFrameRes, ProofState state) {
      return RawCodeList.Count == 1;
    }

    public override List<Statement> AssembleStmts(List<List<Statement>> raw) {
      Contract.Assume(raw.Count == 1);

      IToken start = TokenGenerator.NextToken(_stmt.Tok, _stmt.Tok);
      IToken end = TokenGenerator.NextToken(_stmt.EndTok, _stmt.EndTok);

      var stmts = (List<Statement>)raw.First();
      //FIXME: update tokens
      var body = new Dafny.BlockStmt(start, end, stmts);
      var stmt = new Dafny.ForallStmt(start, end, _vars, null, _range, _ens, body);
      var list = new List<Statement> {stmt};
      return list;
    }


    // List functions should be moved somewhere else...

    [Pure]
    public String NextString(String v) {
      char last = v.ElementAt(v.Length - 1);
      if (Char.IsNumber(last)) {
        double n = Char.GetNumericValue(last) + 1;
        return v.Substring(0, v.Length - 1) + n;
      } else {
        return v + "0";
      }
    }
    
    [Pure]
    public bool GenFreeVar(String var, ICollection<String> allvars, out String res) {
      res = var;
      // not been changed 
      if (!allvars.Contains(var))
        return false;
      while(allvars.Contains(res))
        res = NextString(res);
      return true;
    }










  /*
   *  TODO: generalise: this could also be a meta-level variable or tactic application
   *  FIXME: doesn't have to be an implication
   */

  [Pure]
    public static bool IsForallShape(Expression e) {
      Contract.Requires(e != null);

    var fall = e as Microsoft.Dafny.ForallExpr;
    if (fall?.LogicalBody() is BinaryExpr) {
      var body = fall.LogicalBody() as BinaryExpr;
      if (body?.Op == BinaryExpr.Opcode.Imp) {
        return true;
      }
      else {
        return false;
      }
    }
    return false;
    }

    public static IEnumerable<ProofState> EvalNext(Statement statement, ProofState state0) {

      yield break;
    }



    /*
     * Term work:
     *  - check free vars
     *  - instantiate var (possible rename)
     *  - rename all instances in program text (body)
     *  - 
     */

    public Dafny.ForallStmt GenerateForallStmt(Statement body) {
      //  Contract.Requires(_stmt != null);
      IToken start = TokenGenerator.NextToken(_stmt.Tok, _stmt.Tok);
      IToken end = TokenGenerator.NextToken(_stmt.EndTok, _stmt.EndTok);

      return new Dafny.ForallStmt(start, end, _vars, null, _range, _ens, body);
    }

    private int FreeVars() {
      return 0;
    }


    public override bool MatchStmt(Statement stmt, ProofState state) {
      Contract.Assume(stmt != null);

      return stmt is TacticForallStmt;
    }

  }

}

