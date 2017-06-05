using System.Collections.Generic;
using System.Linq;
using Microsoft.Boogie;

namespace Microsoft.Dafny.Tacny.Language
{
  public class InlineTacticStmt : TacticFrameCtrl
  {
    public override bool MatchStmt(Statement stmt, ProofState state)
    {
      return false;
      /* if (stmt is InlineTacticBlockStmt)
         return true;
       else if (stmt is UpdateStmt) {
         var us = stmt as UpdateStmt;
         return state.IsInlineTacticCall(us);
       } else {
         return false;
       }
       */
    }

    public override IEnumerable<ProofState> EvalInit(Statement statement, ProofState state) {

      if (statement is InlineTacticBlockStmt) {
        var inline = statement as InlineTacticBlockStmt;
        //check whether the tactic name is fresh
        bool isFresh = !(state.Tactics.ContainsKey(inline.name) ||
                         state.ContainInlineTactic(inline.name) ||
                         state.Members.ContainsKey(inline.name));
        if (isFresh) {
          state.AddInlineTactic(inline.name, inline);
          var frameCtrl = new DefaultTacticFrameCtrl();
          frameCtrl.InitBasicFrameCtrl(inline.Body.Body, state.IsCurFramePartial(), null, VerifyN);
          state.AddNewFrame(frameCtrl);
          yield return state;
        } else {
          state.ReportTacticError(statement.Tok, "Duplicated inline tactic name.");
        }
      } else if (statement is UpdateStmt) {
        var aps = ((ExprRhs) ((UpdateStmt) statement).Rhss[0]).Expr as ApplySuffix;
        //inline tactic is not supposed to have any args
        if (aps.Args == null || aps.Args.Count == 0) {
          var inline = state.GetInlineTactic(Util.GetSignature(aps));
          var frameCtrl = new DefaultTacticFrameCtrl();
          frameCtrl.InitBasicFrameCtrl(inline.Body.Body, state.IsCurFramePartial(), null, VerifyN);
          state.AddNewFrame(frameCtrl);
          yield return state;
        } else {
          state.ReportTacticError(statement.Tok, "No argument is allowed in inline tactics.");
        }
      }
    }

  }
}