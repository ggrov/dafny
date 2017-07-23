using System.Collections.Generic;
using System.Linq;


namespace Microsoft.Dafny.Tacny.EAtomic {
  class Caller : EAtomic {
    public override string Signature => "caller";
    public override int ArgsCount => 0;

    public override Expression Generate(Expression expression, ProofState proofState) {
      if(proofState.TargetMethod != null)
        return new TacticLiteralExpr(proofState.TargetMethod.Name);
      else
        return null;

    }
  }
}