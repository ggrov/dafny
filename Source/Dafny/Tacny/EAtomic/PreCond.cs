using System.Collections.Generic;
using System.Linq;

namespace Microsoft.Dafny.Tacny.EAtomic {
  class PreCond : EAtomic {
    public override string Signature => "requires";
    public override int ArgsCount => 0;

    public override Expression Generate(Expression expression, ProofState proofState) {

      //need to get postconds from unresolved prog
      var prog = proofState.GetDafnyProgram();

      var tld = prog.DefaultModuleDef.TopLevelDecls.FirstOrDefault(x => x.Name == proofState.ActiveClass.Name) as ClassDecl;
      if(tld != null) {
        var member = tld.Members.FirstOrDefault(x => x.Name == proofState.TargetMethod.Name) as Method;

        var posts = new List<Expression>();
        if(member != null)
          foreach(var post in member.Req) {
            posts.Add(post.E);
          }
        return GenerateEAtomExprAsSeq(posts);
      }
      return GenerateEAtomExprAsSeq(new List<Expression>());
    }
  }
}

