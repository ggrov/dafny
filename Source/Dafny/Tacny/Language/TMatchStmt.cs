//YUHUI: this implemntation is over complicated, use raw[0][0] implicitly as staus data, need to be simplified
using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Diagnostics.Contracts;
using Microsoft.Boogie;
using Microsoft.Dafny.Tacny.Expr;


namespace Microsoft.Dafny.Tacny.Language
{
  class TMatchStmt : TacticFrameCtrl
  {

    public new bool IsEvaluated => false;
    //the match case stmt with assume false for each case
    private MatchStmt _matchStmt;


    public override bool MatchStmt(Statement stmt, ProofState state) {
      return stmt is TacticCasesBlockStmt;
    }

    public override bool EvalTerminated(bool childFrameRes, ProofState ps) {
      //_matchStmt is the match case stmt with assume false for each case
      //raw the actual code to be inserted in the case statement

      return _matchStmt != null && _matchStmt.Cases.Count == RawCodeList.Count;
    }

    public override List<Statement> AssembleStmts(List<List<Statement>> raw) {
      //Contract.Requires(IsTerminated(raw));

      for (int i = 0; i < raw.Count; i++) {
        if (_matchStmt != null) {
          _matchStmt.Cases[i].Body.Clear();
          _matchStmt.Cases[i].Body.AddRange(raw[i]);
        }
      }
      var ret = new List<Statement> { _matchStmt };
      return ret;
    }

    internal int GetNthCaseIdx(List<List<Statement>> raw) {
      Contract.Requires(raw != null);
      return raw.Count;

    }
    public override IEnumerable<ProofState> EvalStep(ProofState state0) {
      var state = state0.Copy();

      var stmt = GetStmt() as TacticCasesBlockStmt;
      var framectrl = new DefaultTacticFrameCtrl();
      if (stmt != null) framectrl.InitBasicFrameCtrl(stmt.Body.Body, state0.IsCurFramePartial(), null);
      state.AddNewFrame(framectrl);

      var idx = GetNthCaseIdx(RawCodeList);
      if (_matchStmt != null)
        foreach (var tmp in _matchStmt.Cases[idx].CasePatterns) {
          state.AddDafnyVar(tmp.Var.Name, new ProofState.VariableData { Variable = tmp.Var, Type = tmp.Var.Type });
        }
      //with this flag set to true, dafny will check the case branch before evaluates any tacny code
      state.NeedVerify = true;
      yield return state;

    }

    public override IEnumerable<ProofState> EvalInit(Statement statement, ProofState state) {
      Contract.Assume(statement != null);
      Contract.Assume(statement is TacticCasesBlockStmt);

      var stmt = statement as TacticCasesBlockStmt;
      NameSegment caseVar;

      //get guards
      Debug.Assert(stmt != null, "stmt != null");
      var guard = stmt.Guard as ParensExpression;

      if (guard == null)
        caseVar = stmt.Guard as NameSegment;
      else
        caseVar = guard.E as NameSegment;

      //TODO: need to check the datatype of caseGuard, 
      // also need to consider the case that caseVar is a tac var
      var srcVar = SimpExpr.SimpTacticExpr(state, caseVar) as NameSegment;
      if (srcVar == null) {
        state.ReportTacticError(statement.Tok, Printer.ExprToString(caseVar) + " is not a valid variable.");
        yield break;
      }

      var datatype = state.GetDafnyVarType(srcVar.Name).AsDatatype;
      if (datatype == null) {
        state.ReportTacticError(statement.Tok, Printer.ExprToString(caseVar) + " is not an inductive dataype variable.");
        yield break;
      }


      //generate a test program to check which cases need to apply tacny
      bool[] ctorFlags;
      InitCtorFlags(datatype, out ctorFlags);

      List<Func<int, List<Statement>>> fList = new List<Func<int, List<Statement>>>();

      int i;
      for (i = 0; i < datatype.Ctors.Count; i++) {
        fList.Add(GenerateAssumeFalseStmtAsStmtList);
      }

      //var matchStmt = GenerateMatchStmt(state.TacticApplication.Tok.line, srcVar.Copy(), datatype, fList);
      var matchStmt = GenerateMatchStmt(TacnyDriver.TacticCodeTokLine, srcVar.Copy(), datatype, fList);
      _matchStmt = matchStmt;
      var matchCtrl = this;

      //use a dummystmt to creat a frame for match, note that this stmts is never be evaluated
      var dummystmt = new List<Statement>();
      dummystmt.Add(stmt);
      dummystmt.Add(stmt);

      _matchStmt = matchStmt;
      matchCtrl.InitBasicFrameCtrl(dummystmt, state.IsCurFramePartial(), null);
      state.AddNewFrame(matchCtrl);

      //push a frame for the first case
      //TODO: add case variable to frame, so that variable () can refer to it
      var caseCtrl = new DefaultTacticFrameCtrl();
      caseCtrl.InitBasicFrameCtrl(stmt.Body.Body, state.IsCurFramePartial(), null);
      state.AddNewFrame(caseCtrl);

      foreach (var tmp in matchStmt.Cases[0].CasePatterns) {
        state.AddDafnyVar(tmp.Var.Name, new ProofState.VariableData { Variable = tmp.Var, Type = tmp.Var.Type });
      }

      //with this flag set to true, dafny will check the case brnach before evaluates any tacny code
      state.NeedVerify = true;
      yield return state;
    }


    private static void InitCtorFlags(DatatypeDecl datatype, out bool[] flags, bool value = false) {
      flags = new bool[datatype.Ctors.Count];
      for (int i = 0; i < flags.Length; i++) {
        flags[i] = value;
      }
    }

    /// <summary>
    /// 
    /// </summary>
    /// <param name="line"></param>
    /// <param name="ns"></param>
    /// <param name="datatype"></param>
    /// <param name="fL"></param>a function list which contains a function to generate stetment list with given line number
    /// <returns></returns>
    private MatchStmt GenerateMatchStmt(int line, NameSegment ns, DatatypeDecl datatype, List<Func<int, List<Statement>>> fL) {
      Contract.Requires(ns != null);
      Contract.Requires(datatype != null);
      Contract.Ensures(Contract.Result<MatchStmt>() != null);
      List<MatchCaseStmt> cases = new List<MatchCaseStmt>();
      int index = TacnyDriver.TacticCodeTokLine;//line + 1;


      for (int j = 0; j < datatype.Ctors.Count; j++) {
        var dc = datatype.Ctors[j];
        Func<int, List<Statement>> f = _ => new List<Statement>();
        if (j < fL.Count) f = fL[j];

        MatchCaseStmt mcs = GenerateMatchCaseStmt(index, dc, f);

        cases.Add(mcs);
        line += mcs.Body.Count + 1;
      }

      return new MatchStmt(new Token(index, 0) { val = "match" },
        new Token(index, 0) { val = "=>" },
        ns, cases, false);
    }

    /// <summary>
    /// 
    /// </summary>
    /// <param name="line"></param>
    /// <param name="dtc"></param>
    /// <param name="f"></param>
    /// <returns></returns>
    private MatchCaseStmt GenerateMatchCaseStmt(int line, DatatypeCtor dtc, Func<int, List<Statement>> f) {
      Contract.Requires(dtc != null);
      List<CasePattern> casePatterns = new List<CasePattern>();
      dtc = new DatatypeCtor(dtc.tok, dtc.Name, dtc.Formals, dtc.Attributes);

      foreach (var formal in dtc.Formals) {
        var cp = GenerateCasePattern(line, formal);
        casePatterns.Add(cp);
      }

      //List<Statement> body = new List<Statement>();
      //body.Add(GenerateAssumeFalseStmt(line));
      var mcs = new MatchCaseStmt(new Token(line, 0) { val = "cases" },
        dtc.CompileName, casePatterns, f(line));
      return mcs;
    }

    private List<Statement> GenerateAssumeFalseStmtAsStmtList(int line) {
      var l = new List<Statement> { GenerateAssumeFalseStmt(line) };
      return l;
    }

    private AssumeStmt GenerateAssumeFalseStmt(int line) {
      return new AssumeStmt(new Token(line, 0) { val = "assume" },
        new Token(line, 0) { val = ";" },
        new Microsoft.Dafny.LiteralExpr(new Token(line, 0) { val = "false" }, false),
        null);

    }

    private CasePattern GenerateCasePattern(int line, Formal formal) {
      Contract.Requires(formal != null);
      /*      var name = PopCaseName();
            if (name == null) name = formal.Name; 
       */
      formal = new Formal(formal.tok, formal.Name, formal.Type, formal.InParam, formal.IsGhost);
      CasePattern cp = new CasePattern(new Token(line, 0) { val = formal.Name },
        new BoundVar(new Token(line, 0) { val = formal.Name }, formal.Name, new InferredTypeProxy()));
      return cp;
    }
  }
}