using System.Collections.Generic;
using System.Linq;

// Project the all dafny variables in the current scope of the calling method/function

namespace Microsoft.Dafny.Tacny.EAtomic { 
  class Variables : EAtomic {

    public override string Signature => "vars";
    public override int ArgsCount => 0;

    public override Expression Generate(Expression expression, ProofState proofState) {
      var vars = proofState.GetAllDafnyVars().Values.ToList()
        .Where(x => !Params.IsParam(x)); //exclude inputs

      var ret = new List<Expression>();

      foreach (var x in vars) {
        ret.Add(new TacticLiteralExpr(x.Variable.Name));
      }
      return GenerateEAtomExprAsSeq(ret);
    }
  }
}
