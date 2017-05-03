﻿using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Diagnostics.Contracts;
using System.Linq;

namespace Microsoft.Dafny.Tacny.Language{
  public abstract class TacticFrameCtrl{
    public List<Statement> Body;
    private int _bodyCounter;
    public Statement CurStmt => _bodyCounter >= Body.Count ? null : Body[_bodyCounter];
    public Statement LastStmt => _bodyCounter == 0 ? null: Body[_bodyCounter - 1];
    public bool IsEvaluated => _bodyCounter >= Body.Count;

    public Strategy SearchStrategy { get; set; } = Strategy.Dfs;
    public bool IsPartial;
    public int OriginalBk = -1;
    public int Backtrack;
    public int TimeStamp = 0;

    //a funtion with the right kind will be able to th generated code to List of statment
    protected List<Statement> GeneratedCode;
    //store the tempratry code to be combined, e.g. case statments for match, wit a boolean tag indicating whether is verified
    //private readonly List<Tuple<bool, List<Statement>>> _rawCodeList;
    protected List<List<Statement>> RawCodeList;
    
    public bool IncCounter() {
      _bodyCounter++;
      return _bodyCounter + 1 < Body.Count;
    }

    protected void ParseTacticAttributes(Attributes attr) {
      if (attr == null){
        return;
      }
      Expression arg;
      LiteralExpr literalExpr;
      switch(attr.Name) {
        case "search":
          var expr = attr.Args.FirstOrDefault();
          string stratName = (expr as NameSegment)?.Name;
          Contract.Assert(stratName != null);
          try {
            SearchStrategy = (Strategy)Enum.Parse(typeof(Strategy), stratName, true); // TODO: change to ENUM
          } catch {
            SearchStrategy = Strategy.Dfs;
          }
          break;
        case "partial":
          IsPartial = true;
          break;
        case "backtrack":
          arg = attr.Args.FirstOrDefault();
          if (arg == null)
            Backtrack = Backtrack + 1;
          else{
            try{
              literalExpr = arg as LiteralExpr;
              if (literalExpr != null)
              {
                var input = literalExpr.Value.ToString();
                Backtrack = Backtrack + Int32.Parse(input);
              }
            }
            catch (Exception){
              Backtrack = Backtrack + 1;
            }
          }
          break;
        case "timeout":
          int timeout = 0;
          arg = attr.Args.FirstOrDefault();
          if (arg == null)
            timeout = 10;
          else{
            try{
              literalExpr = arg as LiteralExpr;
              if (literalExpr != null){
                var input = literalExpr.Value.ToString();
                timeout = Int32.Parse(input);
              }
            }
            catch (Exception){
              timeout = 0;
            }
          }
          if (timeout != 0){
            TimeStamp = Interpreter.Timer.Elapsed.Seconds + timeout;
          }
          break;
        default:
          //_reporter.Warning(MessageSource.Tactic, ((MemberDecl)ActiveTactic).tok, $"Unrecognized attribute {attr.Name}");
          break;
      }

      if(attr.Prev != null)
        ParseTacticAttributes(attr.Prev);
    }

    public void InitBasicFrameCtrl(List<Statement> body, bool parentPartial, Attributes attrs, Tactic tactic = null){
      IsPartial = parentPartial;
      if (tactic != null)
        ParseTacticAttributes(tactic.Attributes);
      Body = body;
      ParseTacticAttributes(attrs);
      OriginalBk = Backtrack;
      GeneratedCode = null;
      RawCodeList = new List<List<Statement>>();
    }

    public void AddGeneratedCode(Statement newStmt) {
      var l = new List<Statement> {newStmt};
      RawCodeList.Add(l);
    }
    public void AddGeneratedCode(List<Statement> newStmt) {
      RawCodeList.Add(newStmt);
    }

    /// <summary>
    /// this will assemble the raw code if the raw code can be verified or parital is allowed,
    /// </summary>
    public void MarkAsEvaluated(bool curFrameProved, out bool backtraced) {
      backtraced = false;
      // only to assmeble code when the current frame is proved, 
      // or the current frame is partial and the all the stmts have been evaluated 
      if(curFrameProved || IsPartial) {
        if(Backtrack > 0) {
          Console.WriteLine(" ----- Backtrack ---- ");
          Backtrack -= 1;
          backtraced = true;
          return;
        }
        Assemble();
      }
    }

    public List<List<Statement>> GetRawCode() {
      return RawCodeList;
    }
    public List<Statement> GetFinalCode() {
      return GeneratedCode;
    }

    /// <summary>
    /// should only be called from proof state !!
    /// </summary>
    /// <returns></returns>
    public Statement GetStmt() {
      var stmt = CurStmt;
      IncCounter();
      return stmt;
    }

    public Statement GetLastStmt(){
      return LastStmt;
    }

    public void Assemble(){
      GeneratedCode = AssembleStmts(RawCodeList);
    }

    public abstract bool MatchStmt(Statement stmt, ProofState state);
       
    public abstract IEnumerable <ProofState> EvalInit(Statement statement, ProofState state0);
    public abstract IEnumerable<ProofState> EvalStep(ProofState state0);
    public abstract bool EvalTerminated(bool childFrameRes, ProofState state);
    public abstract List<Statement> AssembleStmts(List<List<Statement>> raw);

  }

  class DefaultTacticFrameCtrl : TacticFrameCtrl {

    public override bool MatchStmt(Statement stmt, ProofState state){
      /* the default one always returns false, as we don't need this to judge if a stmt belongs to this type.
       * One stmt would be considered as the default one when all other matches fail. */
      return false;
    }

    public override IEnumerable<ProofState> EvalStep(ProofState state0){
      var statement = GetStmt();
      state0.TopTokenTracer().Increase();
      return Interpreter.EvalStmt(statement, state0);
    }

    public override IEnumerable<ProofState> EvalInit(Statement statement, ProofState state0){
      // not supposed to be called, for the deault frame, no need to init
      Contract.Assert(false);
      return null;
    }

    public override bool EvalTerminated(bool latestChildFrameRes, ProofState state) {
        return latestChildFrameRes;
    }

    public override List<Statement> AssembleStmts(List<List<Statement>> raw){
      return raw.SelectMany(x => x).ToList();
    }
  }
}
