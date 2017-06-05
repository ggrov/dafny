using System.Collections.Generic;
using System.Linq;
using Microsoft.Boogie;

namespace Microsoft.Dafny.Tacny.Language {
  public class TryBlockStmt : TacticFrameCtrl
  {

    private ProofState _oriState;
    private TacticTryBlockStmt _stmt;
    public override bool MatchStmt(Statement stmt, ProofState state){
      var us = stmt as TacticTryBlockStmt;
      return us != null;
    }

    public override IEnumerable<ProofState> EvalInit(Statement statement, ProofState state0) {
      var tryBlockStmt = statement as TacticTryBlockStmt;
      if(tryBlockStmt != null) {
        _stmt = tryBlockStmt;
        _oriState = state0;
        this.InitBasicFrameCtrl(tryBlockStmt.Body.Body, true, null, VerifyN);

        var state = state0.Copy();
        state.AddNewFrame(this);
        yield return state;
      }
    }

    public override IEnumerable<ProofState> ApplyPatch(ProofState state0)
    {
      if (_stmt.Catch != null) {
        var frame = new DefaultTacticFrameCtrl();
        frame.InitBasicFrameCtrl(_stmt.Catch.Body, true, null, VerifyN);
        _oriState.AddNewFrame(frame);
      } 
      yield return _oriState;
    }
  }
}