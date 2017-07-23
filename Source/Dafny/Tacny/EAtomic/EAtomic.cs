using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;
using System.Reflection;
using Microsoft.Boogie;

namespace Microsoft.Dafny.Tacny.EAtomic {

  /// <summary>
  ///   Abstact class for Atomic Expressions
  /// </summary>
  public abstract class EAtomic  {
    public static List<string> EATomicSigList;

    public static bool IsEAtomicSig(string sig){
      if (EATomicSigList == null){
        InitEAtomicSigList();
      }
      return EATomicSigList.Exists(sig.Equals);
    }

    private static void InitEAtomicSigList() {
      EATomicSigList = new List<string>();
      var types =
            Assembly.GetAssembly(typeof(EAtomic))
              .GetTypes()
              .Where(t => t.IsSubclassOf(typeof(EAtomic)));
      foreach(var eType in types)
      {
        var eatomInst = Activator.CreateInstance(eType) as EAtomic;
        if (eatomInst != null) EATomicSigList.Add(eatomInst.Signature);
      }
    }

    public static Expression GenerateEAtomExprAsSeq(List<Expression> es)
    {
      return new SeqDisplayExpr(new Token(TacnyDriver.TacticCodeTokLine, 0), es);
    }

    public abstract string Signature { get; }
    public abstract int ArgsCount { get; }


    // TypeOf (Expression expression, ProofState proofState); 
    // next step will be to implement proer typing, perhaps in F#

    /// <summary>
    ///   Common entry point for each atomic
    /// </summary>
    /// <param name="expression">Expression to be resolved</param>
    /// <param name="proofState">Current tactic ProofState</param>
    /// <returns>Lazily returns generated objects one at a time</returns>
    public abstract Expression Generate(Expression expression, ProofState proofState);
  }
 
}