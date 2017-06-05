using System.Collections.Generic;
using Microsoft.Dafny.Tacny.Expr;

namespace Microsoft.Dafny.Tacny.Atomic{
  class TacticInv : Atomic{
    public override string Signature => "invariant";
    public override int ArgsCount => 1;

    public override IEnumerable<ProofState> Generate(Statement statement, ProofState state){

      List<Expression> callArguments;
      InitArgs(state, statement, out callArguments);

      var expr = SimpExpr.SimpTacticExpr(state, callArguments[0]);
        if (expr != null){
          var destStmt = new AssumeStmt(null, null, expr, null);
          var state0 = state.Copy();
          state0.AddStatement(destStmt);

          yield return state0;
        }
    }
  }
}
