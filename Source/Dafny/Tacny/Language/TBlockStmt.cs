using System.Collections.Generic;
using System.Linq;
using Microsoft.Boogie;

namespace Microsoft.Dafny.Tacny.Language {
  public class TBlockStmt : TacticFrameCtrl {
    public override bool MatchStmt(Statement stmt, ProofState state) {
      var us = stmt as BlockStmt;
      return us != null ;
    }

    public override IEnumerable<ProofState> EvalInit(Statement statement, ProofState state0) {
      var state = state0.Copy();
      var blockStmt = statement as Dafny.BlockStmt;
      if(blockStmt != null) {
        var frameCtrl = new DefaultTacticFrameCtrl();
        frameCtrl.InitBasicFrameCtrl(blockStmt.Body, true, null, VerifyN);
        state.AddNewFrame(frameCtrl);
        yield return state;
      }
    }
  }
}