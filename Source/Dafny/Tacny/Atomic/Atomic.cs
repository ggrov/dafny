﻿using System.Collections.Generic;
using System.Diagnostics.Contracts;

namespace Microsoft.Dafny.Tacny.Atomic
{
  /// <summary>
  ///   Abstract class for Atomic Statement
  /// </summary>
  public abstract class Atomic 
  {
    public abstract string Signature { get; }
    public abstract int ArgsCount { get; }

    /// <summary>
    /// </summary>
    /// <param name="statement"></param>
    /// <param name="state"></param>
    /// <returns></returns>
    public abstract IEnumerable<ProofState> Generate(Statement statement, ProofState state);

    protected static List<Expression> GetCallArguments(UpdateStmt us)
    {
      Contract.Requires(us != null);
      var er = (ExprRhs) us.Rhss[0];
      return ((ApplySuffix) er.Expr).Args;
    }

    protected static void InitArgs(ProofState ps, Statement st, out IVariable lv, out List<Expression> callArguments)
    {
      Contract.Requires(st != null);
      Contract.Ensures(Contract.ValueAtReturn(out callArguments) != null);
      lv = null;
      callArguments = null;
      TacticBlockStmt tbs;

      // tacny variables should be declared as tvar or tactic var
      //if(st is VarDeclStmt)
      //  Contract.Assert(false, Error.MkErr(st, 13));

      var stmt = st as TacticVarDeclStmt;
      if (stmt != null) {
        var tvds = stmt;
        lv = tvds.Locals[0];
        callArguments = GetCallArguments(tvds.Update as UpdateStmt);

      } else {
        var updateStmt = st as UpdateStmt;
        if (updateStmt != null) {
          var us = updateStmt;
          if (us.Lhss.Count == 0)
            callArguments = GetCallArguments(us);
          else {
            var ns = (NameSegment) us.Lhss[0];
            if (ps.ContainTVal(ns)) {
              //TODO: need to doubel check this
              lv = ps.GetTVarValue(ns) as IVariable;
              callArguments = GetCallArguments(us);
            }
          }
        } else if ((tbs = st as TacticBlockStmt) != null) {
          var pe = tbs.Guard as ParensExpression;
          callArguments = pe != null ? new List<Expression> {pe.E} : new List<Expression> {tbs.Guard};
        }
      }
    }
  }
}