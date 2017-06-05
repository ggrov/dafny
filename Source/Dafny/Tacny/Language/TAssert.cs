using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;
using Microsoft.Boogie;
using Microsoft.Dafny.Tacny.Expr;

namespace Microsoft.Dafny.Tacny.Language
{
  class TAssert : TacticFrameCtrl
  {
    /// <summary>
    /// tactic assert is implemented by introducing two frames: assertion control and assertion statement.
    /// the assertion statement frame is just a default frame with body of a asssertion followed by assume fasle. 
    /// The partial attribute will be set to false. It means the assertion has to be true before the evalaution can 
    /// continue. Note that the assume false is used to make sure the following vcs after the assertion can't affect 
    /// the verificaton.
    /// </summary>
    private bool _pass = false;
    public override bool MatchStmt(Statement stmt, ProofState state)
    {
      return stmt is TacticAssertStmt;
    }

    public override IEnumerable<ProofState> EvalInit(Statement statement, ProofState state0)
    {

      state0.InAsserstion = true;
      Func<ProofState, IEnumerable<ProofState>> tassertFramePatch =
        ps => {
          bool dummy;
          //set partial so that the assert-assume frame can be popped
          this.IsPartial = true;
          this._pass = true;
          ps.MarkCurFrameAsTerminated(false, out dummy);
          return ps.ApplyPatch();// this will call the parent patch handler
        };

      var dummyBody = new List<Statement> { statement };
      InitBasicFrameCtrl(dummyBody, false, null, VerifyN, tassertFramePatch);
      state0.AddNewFrame(this);


      var assertFrame = new DefaultTacticFrameCtrl();
      Func<ProofState,IEnumerable<ProofState>> assertFramePatch = 
        ps =>
        {
          bool dummy;
          //set partial so that the assert-assume frame can be popped
          assertFrame.IsPartial = true;
          ps.MarkCurFrameAsTerminated(false, out dummy);
          return ps.ApplyPatch();// this will call the patch handler in tassert
        };
      assertFrame.InitBasicFrameCtrl(dummyBody, false, null, VerifyN, tassertFramePatch);
      assertFrame.IncCounter();
      state0.AddNewFrame(assertFrame);

      var st = SimpExpr.SimpTacticExpr(state0, (statement as TacticAssertStmt).Expr);
      // insert the simplified assert, followed by assume false so that the prover don't need to worry about the 
      // upcoming vcs.

      var asserts = new List<Statement>();
      asserts.Add(
       new AssertStmt(new Token(TacnyDriver.TacticCodeTokLine, 0) { val = "assert" },
         new Token(TacnyDriver.TacticCodeTokLine, 0) { val = ";" }, st, null, null));
      asserts.Add(
      new AssumeStmt(new Token(TacnyDriver.TacticCodeTokLine, 0) { val = "assume" },
       new Token(TacnyDriver.TacticCodeTokLine, 0) { val = ";" },
       new Microsoft.Dafny.LiteralExpr(new Token(TacnyDriver.TacticCodeTokLine, 0) { val = "false" }, false),
       null));

      state0.AddStatements(asserts);

      state0.NeedVerify = true;

      yield return state0;
    }

    public override IEnumerable<ProofState> EvalStep(ProofState state0)
    {
      _pass = true;
      RawCodeList = new List<List<Statement>>();
      GeneratedCode = new List<Statement>();
      //inc counter to finish the evaluation of the current fram, note that there is only one statement.
      // so one is enough
      IncCounter();
      state0.InAsserstion = false;
      yield return state0;
    }

    public override bool EvalTerminated(bool childFrameRes, ProofState state) {
      return _pass;
    }

  }
}
