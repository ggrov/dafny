#define _TACTIC_DEBUG_L1
//#define _TACTIC_DEBUG_L2


using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;
using System.Reflection;
using Bpl = Microsoft.Boogie;
using Microsoft.Boogie;
using Microsoft.Dafny.Tacny.ArrayExtensions;

namespace Microsoft.Dafny.Tacny {

  public static class Util {
    public static bool IsTacticTypes(string typeN) {
      var ret = false;
      switch (typeN) {
        case "bool":
        case "int":
        case "term":
        case "tac":
          ret = true;
          break;
        default:
          break;
      }
      return ret;
    }
    public static bool CheckTacticDef(ITactic tac, out string errMsg) {
      Contract.Requires(tac != null);
      foreach (var arg in tac.Ins) {
        var name = arg.Type is UserDefinedType ? (arg.Type as UserDefinedType).Name : arg.Type.ToString();
        if (!IsTacticTypes(name)) {
          errMsg = name +
                   " is a valid type for tactic arguments.";
          return false;
        }
      }
      foreach (var arg in tac.Outs) {
        var name = arg.Type is UserDefinedType ? (arg.Type as UserDefinedType).Name : arg.Type.ToString();
        if (!IsTacticTypes(name)) {
          errMsg = name +
                   " is a valid type for tactic return variables.";
          return false;
        }
      }

      errMsg = "";
      return true;
    }

    public static bool CheckTacticArgsCount(ClassDecl curDecl, ApplySuffix e, out string errMsg) {
      Contract.Requires(curDecl != null);
      if(curDecl != null)
        foreach(var member in curDecl.Members) {
          var tac = member as ITactic;
          if(tac != null && tac.Name == GetSignature(e)) {
            if(e.Args.Count != tac.Ins.Count) {
              errMsg = "The number of args doesn't match the tactic definition for "
                 + Printer.ExprToString(e);
              return false;
            }
            errMsg = "";
            return true;
          }
        }
      errMsg = "Can't find the tactic for " + Printer.ExprToString(e);
      return false;
    }

    public static bool CheckTacticArgsCount(ClassDecl curDecl, UpdateStmt stmt, out string errMsg) {
      Contract.Requires(curDecl != null);
      if (curDecl != null)
        foreach (var member in curDecl.Members) {
          var tac = member as ITactic;
          if (tac != null && tac.Name == GetSignature(stmt)) {
            var aps = ((ExprRhs)stmt.Rhss[0]).Expr as ApplySuffix;
            if (aps.Args.Count != tac.Ins.Count) {
              errMsg = "The number of args doesn't match the tactic definition for "
                 + Printer.StatementToString(stmt);
              return false;
            }
            errMsg = "";
            return true;
          }
        }
      errMsg = "Can't find the tactic for " + Printer.StatementToString(stmt);
      return false;
    }

    public static bool CheckTypeTac(UserDefinedType type, string tacName, ProofState state, out string errMsg)
    {
      if (state.Tactics.ContainsKey(tacName)) {
        var tac = state.Tactics[tacName];
        if (type.TypeArgs.Count != tac.Ins.Count) {
          errMsg = "The number of args doesn't match the tactic typ " + type;
          return false;
        }

        for (var i = 0; i < tac.Ins.Count; i++) {
          var name = tac.Ins[i].Type.ToString();

          if (tac.Ins[i].Type.ToString() != type.TypeArgs[i].ToString()) {
            errMsg = tacName + " doesn't match the tactic typ " + type;
            return false;
             
          }
        }
        errMsg = "";
        return true;

      } else {
        errMsg = tacName + " is not a tactic.";
        return false;
      }

    }

    public static bool CheckTacticArgs(ITactic tac, ApplySuffix aps, ProofState state, out string errMsg)
    {
      Contract.Requires(tac != null);
      Contract.Requires(aps != null);

      if (aps.Args.Count != tac.Ins.Count) {
        errMsg = "The number of args doesn't match the tactic definition for "
            + Printer.ExprToString(aps);
        return false;
      }

      for (var i = 0; i < tac.Ins.Count; i++)
     {
        var name = tac.Ins[i].Type is UserDefinedType ? 
          (tac.Ins[i].Type as UserDefinedType).Name : tac.Ins[i].Type.ToString();

        switch (name) {
          case "bool":
          case "int":
            if (!(aps.Args[i] is NameSegment) ||
              tac.Ins[i].Type.ToString() != aps.Args[i].Type.ToString()) {
            errMsg = "In arg[" + i + "], expect " + tac.Ins[i].Type + " but " + aps.Args[i] +
                       " is found";
              return false;
            }
            break;
          case "term":
            break;
          case "tac":
            if (!CheckTypeTac(tac.Ins[i].Type as UserDefinedType, 
              (aps.Args[i] as NameSegment).Name, state, out errMsg)) {
              return false;
            }
            break;
          default:
            break;
        }
      }
      errMsg = "";
      return true;
    }

    public static Expression VariableToExpression(IVariable variable) {
      Contract.Requires(variable != null);
      return new NameSegment(variable.Tok, variable.Name, null);
    }

    public static NameSegment GetNameSegment(UpdateStmt us) {
      Contract.Requires(us != null);
      var rhs = us.Rhss[0] as ExprRhs;
      return rhs == null ? null : GetNameSegment(rhs.Expr as ApplySuffix);
    }

    [Pure]
    public static NameSegment GetNameSegment(ApplySuffix aps) {
      Contract.Requires<ArgumentNullException>(aps != null, "aps");
      var lhs = aps.Lhs as ExprDotName;
      if(lhs == null)
        return aps?.Lhs as NameSegment;
      var edn = lhs;
      return edn.Lhs as NameSegment;
    }

    public static ApplySuffix GetTacticAppExpr (UpdateStmt us) {
      var er = us.Rhss[0] as ExprRhs;
      Contract.Assert(er != null);
      return er.Expr as ApplySuffix;
    }
    /// <summary>
    ///   Return the string signature of an UpdateStmt
    /// </summary>
    /// <param name="us"></param>
    /// <returns></returns>
    public static string GetSignature(UpdateStmt us) {
      Contract.Requires<ArgumentNullException>(Tcce.NonNull(us));
      Contract.Ensures(Contract.Result<string>() != null);
      var er = us.Rhss[0] as ExprRhs;
      Contract.Assert(er != null);
      return GetSignature(er.Expr as ApplySuffix);
    }

    /// <summary>
    ///   Return the string signature of an ApplySuffix
    /// </summary>
    /// <param name="aps"></param>
    /// <returns></returns>
    [Pure]
    public static string GetSignature(ApplySuffix aps) {
      Contract.Requires<ArgumentNullException>(Tcce.NonNull(aps));
      Contract.Ensures(Contract.Result<string>() != null);
      return aps?.Lhs.tok.val;
    }
   
    /// <summary>
    /// Insert generated code into a method
    /// </summary>
    /// <param name="state"></param>
    /// <param name="code"></param>
    /// <returns></returns>
    public static BlockStmt InsertCode(ProofState state, Dictionary<Statement, List<Statement>> code) {
      Contract.Requires<ArgumentNullException>(state != null, "state");
      Contract.Requires<ArgumentNullException>(code != null, "code");


      var prog = state.GetDafnyProgram();
      var tld = prog.DefaultModuleDef.TopLevelDecls.FirstOrDefault(x => x.Name == state.ActiveClass.Name) as ClassDecl;
      Contract.Assert(tld != null);
      var member = tld.Members.FirstOrDefault(x => x.Name == state.TargetMethod.Name) as Method;
      var body = member?.Body;

      //subst tactic call with generated code
      foreach(var kvp in code) {
        InsertCodeInternal(body.Body, kvp.Value, kvp.Key);
      }

      //clean up unfolded tactic call
      RemoveUnfoldedTacticCalls(body.Body, state);
      return body;
    }

    private static void RemoveUnfoldedTacticCalls(List<Statement> body, ProofState state)
    {
      Contract.Requires<ArgumentNullException>(body != null, "body ");
      for(var i = 0; i < body.Count; i++) {
        var stmt = body[i];
        if(stmt is BlockStmt)
          RemoveUnfoldedTacticCalls((stmt as BlockStmt).Body, state);
        else {
          var aps = Expr.TacticAppExprFinder.GetTacticAppExpr(state, stmt);
          if(aps != null)
            body.RemoveAt(i);
        }
      }
    }
    private static void InsertCodeInternal(List<Statement> body, List<Statement> code, Statement tacticCall) {
      Contract.Requires<ArgumentNullException>(body != null, "body ");
      Contract.Requires<ArgumentNullException>(tacticCall != null, "'tacticCall");

      for(var i = 0; i < body.Count; i++) {
        var stmt = body[i];
        if(stmt.Tok.pos == tacticCall.Tok.pos){
            body.RemoveAt(i);
            body.InsertRange(i, code);
            return;
        } else if ((stmt as AssertStmt)?.Proof != null) {
          InsertCodeInternal((stmt as AssertStmt).Proof.Body, code, tacticCall);
        } else if(stmt is WhileStmt) {
          /*
          var whileStmt = stmt as WhileStmt;
          for(var j = 0; j < whileStmt.TInvariants.Count; j++) {
            var item = whileStmt.TInvariants[j];
            if(Compare(tacticCall.Tok, item.Tok)) {
              foreach(var genCode in code) {
                //each inviariant are assmebled as assume statement
                var assumeStmt = genCode as AssumeStmt;
                if(assumeStmt != null) {
                  var expr = assumeStmt.Expr;
                  whileStmt.Invariants.Insert(0, (new MaybeFreeExpression(expr)));
                }
                whileStmt.TInvariants.Remove(item);
              }
            }
          }
          ((WhileStmt)stmt).Body = InsertCodeInternal(((WhileStmt)stmt).Body, code, tacticCall);
          */
        } else if(stmt is IfStmt) { //InsertCodeIfStmt
        } else if(stmt is MatchStmt) {
          foreach (var caseStmt in (stmt as MatchStmt).Cases) {
            InsertCodeInternal(caseStmt.Body, code, tacticCall);
          }
          
        } else if(stmt is CalcStmt) {
          //TODO:
        } else if (stmt is BlockStmt) {
          InsertCodeInternal((stmt as BlockStmt).Body, code, tacticCall);

        }
      }
      return;
    }
    /*
        private static IfStmt InsertCodeIfStmt(IfStmt stmt, List<Statement> code, UpdateStmt tacticCall) {
          Contract.Requires<ArgumentNullException>(stmt != null, "stmt");
          Contract.Requires<ArgumentNullException>(code != null, "code");
          Contract.Requires<ArgumentNullException>(tacticCall != null, "tacticCall");

          stmt.Thn = InsertCodeInternal(stmt.Thn, code, tacticCall);
          if (stmt.Els is BlockStmt) {
            stmt.Els = InsertCodeInternal((BlockStmt)stmt.Els, code, tacticCall);
          } else if (stmt.Els is IfStmt) {
            stmt.Els = InsertCodeIfStmt((IfStmt)stmt.Els, code, tacticCall);
          }
          return stmt;
        }
    */
    public static bool Compare(IToken a, IToken b) {
      Contract.Requires<ArgumentNullException>(a != null, "a");
      Contract.Requires<ArgumentNullException>(b != null, "b");
      return a.col == b.col && a.line == b.line && a.filename == b.filename;
    }



    public static Dictionary<ProofState, MemberDecl> GenerateMembers(ProofState state, Dictionary<ProofState, BlockStmt> bodies) {
      Contract.Requires<ArgumentNullException>(state != null, "state");
      Contract.Requires<ArgumentNullException>(bodies != null, "bodies");
      var result = new Dictionary<ProofState, MemberDecl>();
      var cl = new Cloner();
      foreach(var body in bodies) {
        var md = cl.CloneMember(state.TargetMethod) as Method;
        if(md != null) {
          md.Body.Body.Clear();
          md.Body.Body.AddRange(body.Value.Body);
          if(result.Values.All(x => x.Name != md.Name))
            result.Add(body.Key, md);
          else {
            md = new Method(md.tok, FreshMemberName(md, result.Values.ToList()), md.HasStaticKeyword, md.IsGhost, md.TypeArgs, md.Ins,
              md.Outs, md.Req, md.Mod, md.Ens, md.Decreases, md.Body, md.Attributes, md.SignatureEllipsis);
            result.Add(body.Key, md);
          }
        }
      }
      return result;
    }
    /*
       public static Program GenerateDafnyProgram(ProofState state, List<MemberDecl> newMembers) {
         var prog = state.GetDafnyProgram();
         var tld = prog.DefaultModuleDef.TopLevelDecls.FirstOrDefault(x => x.Name == state.TargetMethod.EnclosingClass.Name) as ClassDecl;
         Contract.Assert(tld != null);
         var member = tld.Members.FirstOrDefault(x => x.Name == state.TargetMethod.Name);
         Contract.Assert(member != null);
         // we can safely remove the tactics
         tld.Members.RemoveAll(x => x is Tactic); //remove before else index will be wrong
         int index = tld.Members.IndexOf(member);
         tld.Members.RemoveAt(index);
         tld.Members.InsertRange(index, newMembers);
         var filePath = Path.Combine(Path.GetTempPath(), Path.GetTempFileName());
         var tw = new StreamWriter(filePath);
         var printer = new Printer(tw);
         printer.PrintTopLevelDecls(prog.DefaultModuleDef.TopLevelDecls, 0, filePath);
         tw.Close();
         string err = Parse(files, programName, prog.reporter, out program);

         Parser.ParseOnly(new List<string>() { filePath}, prog.Name, out prog);
         return prog;
       }
   */
    public static string FreshMemberName(MemberDecl original, List<MemberDecl> context) {
      Contract.Requires<ArgumentNullException>(original != null, "original");
      Contract.Requires<ArgumentNullException>(context != null, "context");
      int count = context.Count(m => m.Name == original.Name);
      string name = $"{original.Name}_{count}";
      while(count != 0) {
        name = $"{original.Name}_{count}";
        count = context.Count(m => m.Name == name);
      }

      return name;
    }



    public static void SetVerifyFalseAttr(MemberDecl memb) {
      var args = new List<Expression>();
      var f = new Microsoft.Dafny.LiteralExpr(new Token(TacnyDriver.TacticCodeTokLine, 0) { val = "false" }, false);
      args.Add(f);
      Attributes newattr = new Attributes("verify", args, memb.Attributes);
      memb.Attributes = newattr;
    }

    private static void SetStatementTokLine(int line, Statement s) {
      if(s is BlockStmt) {
        var s0 = s as BlockStmt;
        s0.Tok.line = line;
        foreach(var ss in s0.Body)
          SetStatementTokLine(line, ss);
      } else if(s is MatchStmt) {
        var s0 = s as MatchStmt;
        foreach(var ss in s0.Cases) {
          ss.tok.line = line;
          foreach(var body in ss.Body)
            SetStatementTokLine(line, body);
        }
      } else
        s.Tok.line = line;
    }

    private static void SetStatementName(Statement s, string oriName, string newName) {
      if(s is BlockStmt) {
        var s0 = s as BlockStmt;
        foreach(var ss in s0.Body)
          SetStatementName(ss, oriName, newName);
      } else if(s is MatchStmt) {
        var s0 = s as MatchStmt;
        foreach(var ss in s0.Cases) {
          foreach(var body in ss.Body)
            SetStatementName(body, oriName, newName);
        }
      } else if(s is UpdateStmt) {
        var ss = s as UpdateStmt;
        if(ss.Rhss != null) {
          foreach(var rhs in ss.Rhss) {
            Console.WriteLine("s");
            if(rhs is ExprRhs && (rhs as ExprRhs).Expr is ApplySuffix
              && ((rhs as ExprRhs).Expr as ApplySuffix).Lhs is NameSegment
              && (((rhs as ExprRhs).Expr as ApplySuffix).Lhs as NameSegment).Name == oriName) {
              var oldAps = (rhs as ExprRhs).Expr as ApplySuffix;
              ApplySuffix aps = new ApplySuffix(oldAps.tok,
                new NameSegment(oldAps.tok, newName, null), oldAps.Args);
              (rhs as ExprRhs).Expr = aps;

            }
          }
        }

      }
    }

    /// <summary>
    /// an optimised version for verifying prog
    /// </summary>
    /// <param name="states"></param>
    /// <returns></returns>
    public static Program GenerateResolvedProg(List<ProofState> states){
      var state = states[0];
      var prog = states[0].GetDafnyProgram();
      
      List<BlockStmt> bodies = new List<BlockStmt>();
      for(var i = 0; i < states.Count; i++) {
        var state0 = states[i];
        var result = new Dictionary<Statement, List<Statement>>
        {
          { state0.TopLevelTacApp, state0.GetGeneratedCode().Copy()}
        };
        var body0 = InsertCode(state0, result);
        SetStatementTokLine(TacnyDriver.TacticCodeTokLine - i - 1, body0);
        SetStatementName(body0, state0.TargetMethod.Name, state0.TargetMethod.Name + "_tacny_code_" + i);
        bodies.Add(body0);
      }

      Method destMd = null;
      DefaultClassDecl defaultClassDecl = null;
      var body = bodies[0];
      foreach(var m in prog.DefaultModuleDef.TopLevelDecls) {
        if(m.WhatKind == "class") {
          var classDecl = m as DefaultClassDecl;
          if (classDecl != null){
            foreach (var method in classDecl.Members){
              if (method.Name == state.TargetMethod.Name){
                destMd = (method as Method);
                defaultClassDecl = classDecl;
              } else if(!(method is Tactic)) {
                method.CallsTactic = 0;
                var o = method as Method;
                if(o != null && o.Body != null)
                  o?.Body.Body.Clear();
                SetVerifyFalseAttr(method);
              } 
            }
          }
        }
      }

      for (var i = 0; i < bodies.Count-1; i++){
        var dest = destMd.Copy();
        dest.CallsTactic = 0;
        dest.Body.Body.Clear();
        dest.Body.Body.AddRange(bodies[i].Body);
        dest.Name = dest.Name + "_tacny_code_" + i;
        defaultClassDecl.Members.Add(dest);
        dest.Body.Tok.line = TacnyDriver.TacticCodeTokLine - i - 1;
      }
      destMd.CallsTactic = 0;
      destMd.Body.Body.Clear();
      destMd.Body.Body.AddRange(bodies[bodies.Count-1].Body);
      destMd.Name = destMd.Name + "_tacny_code_" + (bodies.Count - 1);
      destMd.Body.Tok.line = TacnyDriver.TacticCodeTokLine - bodies.Count;

      var r = new Resolver(prog);
      r.ResolveProgram(prog);

      return prog;
    }

    public static Program GenerateResolvedProg(ProofState state) {

      var prog = state.GetDafnyProgram();


        var result = new Dictionary<Statement, List<Statement>>
        {
          { state.TopLevelTacApp, state.GetGeneratedCode().Copy()}
        };
        var body = InsertCode(state, result);

      Method destMd = null;
      DefaultClassDecl defaultClassDecl = null;

      foreach(var m in prog.DefaultModuleDef.TopLevelDecls) {
        if(m.WhatKind == "class") {
          var classDecl = m as DefaultClassDecl;
          if(classDecl != null) {
            foreach(var method in classDecl.Members) {
              if(method.Name == state.TargetMethod.Name) {
                destMd = (method as Method);
                defaultClassDecl = classDecl;
              } else if(!(method is Tactic)) {
                method.CallsTactic = 0;
                var o = method as Method;
                if(o != null && o.Body != null)
                  o?.Body.Body.Clear();
                SetVerifyFalseAttr(method);
              }
            }
          }
        }
      }


      destMd.CallsTactic = 0;
      destMd.Body.Body.Clear();
      destMd.Body.Body.AddRange(body.Body);

      var r = new Resolver(prog);
      r.ResolveProgram(prog);

      if(prog.reporter.Count(ErrorLevel.Error) != 0) {
        state.GetErrHandler().Reporter = prog.reporter;
#if _TACTIC_DEBUG_L1
        Console.Write("Fail to resolve prog, skip verifier ! \n");
#endif
        return null;
      } else
        return prog;
    }

    public static Program GenerateResolvedProg0(ProofState state) {
      var prog = state.GetDafnyProgram();
      var r = new Resolver(prog);
      r.ResolveProgram(prog);
      //get the generated code
      var results = new Dictionary<Statement, List<Statement>>
      {
        {state.TopLevelTacApp, state.GetGeneratedCode().Copy()}
      };
      var body = InsertCode(state, results);
      // find the membcl in the resoved prog
      Method destMd = null;
      foreach(var m in prog.DefaultModuleDef.TopLevelDecls) {
        if(m.WhatKind == "class") {
          var defaultClassDecl = m as DefaultClassDecl;
          if(defaultClassDecl != null)
            foreach(var method in defaultClassDecl.Members) {
              if(method.FullName == state.TargetMethod.FullName) {
                destMd = (method as Method);
                if(destMd != null) {
                  destMd.CallsTactic = 0;
                  destMd.Body.Body.Clear();
                  destMd.Body.Body.AddRange(body.Body);
                }
              }// if some other method has tactic call, then empty the body
              else if(method.CallsTactic != 0) {
                method.CallsTactic = 0;
                var o = method as Method;
                o?.Body.Body.Clear();
                SetVerifyFalseAttr(method);

              } else {
                //set other memberdecl as verify false
                SetVerifyFalseAttr(method);
              }
            }
        }
      }
      //
#if _TACTIC_DEBUG_L1
      Console.WriteLine("********************* Tactic in : " + destMd + " *****************");
      var printer = new Printer(Console.Out);
      //printer.PrintProgram(prog, false);
      foreach(var stmt in state.GetGeneratedCode()) {
        printer.PrintStatement(stmt, 0);
        Console.WriteLine("");
      }
      Console.WriteLine("********************* Stmts END *****************");
#endif
      //

      if(destMd != null) {
        destMd.CallsTactic = 0;
        r.SetCurClass(destMd.EnclosingClass as ClassDecl);
        r.ResolveMethodBody(destMd, state.GetDafnyProgram().DefaultModuleDef.Name);
      }


      if(prog.reporter.Count(ErrorLevel.Error) != 0) {
        state.GetErrHandler().Reporter = prog.reporter;
#if _TACTIC_DEBUG_L1
        Console.Write("Fail to resolve prog, skip verifier ! \n");
#endif
        return null;
      } else
        return prog;
    }

    private static int _verificationCount = 0;
    public static void VerifyResolvedProg(ProofState state, Program program,
      List<TacnyInterpreter.VerifyResult> res, List<int> idx,
      ErrorReporterDelegate er) {
      Contract.Requires<ArgumentNullException>(program != null);

#if _TACTIC_DEBUG_L1
      var printer = new Printer(Console.Out);
      Console.WriteLine("*********************Verifying Tactic Generated Prog*****************");
      printer.PrintProgram(program, true);
      Console.WriteLine("\n*********************Prog END*****************");
#endif


      _verificationCount++;
      Console.WriteLine("Verfication Count: " + _verificationCount);

      IEnumerable<Tuple<string, Bpl.Program>> boogieProg;

   //   try {
        boogieProg = Translator.Translate(program, program.reporter, null);

        foreach(var prog in boogieProg) {
          PipelineStatistics stats;
          List<ErrorInformation> errorList;
          PipelineOutcome tmp = BoogiePipeline(prog.Item2,
            new List<string> { program.Name }, program.Name, er,
            out stats, out errorList, program);

          var curIdx = -1;
          for(var i = 0; i < errorList.Count; i++) {
            var err = errorList[i];
            if(err.Tok.line < TacnyDriver.TacticCodeTokLine) {
              curIdx = 0 - err.Tok.line - 2;
              res[idx[curIdx]] = TacnyInterpreter.VerifyResult.Failed;
            }
          }
        }
    /*  } catch {
        Console.WriteLine("execption: set verify result as failed.");
        for(var i = 0; i < res.Count; i++) {
            res[i] = TacnyInterpreter.VerifyResult.Failed;
          }
        }*/

    }

    /// <summary>
    /// Pipeline the boogie program to Dafny where it is valid
    /// </summary>
    /// <returns>Exit value</returns>
    public static PipelineOutcome BoogiePipeline(Bpl.Program program, IList<string> fileNames, string programId, ErrorReporterDelegate er, out PipelineStatistics stats, out List<ErrorInformation> errorList, Program tmpDafnyProgram = null) {
      Contract.Requires(program != null);
      Contract.Ensures(0 <= Contract.ValueAtReturn(out stats).InconclusiveCount && 0 <= Contract.ValueAtReturn(out stats).TimeoutCount);

      LinearTypeChecker ltc;
      CivlTypeChecker ctc;
      string baseName = cce.NonNull(System.IO.Path.GetFileName(fileNames[fileNames.Count - 1]));
      baseName = cce.NonNull(System.IO.Path.ChangeExtension(baseName, "bpl"));
      string bplFileName = System.IO.Path.Combine(System.IO.Path.GetTempPath(), baseName);

      errorList = new List<ErrorInformation>();
      stats = new PipelineStatistics();



      PipelineOutcome oc = ExecutionEngine.ResolveAndTypecheck(program, bplFileName, out ltc, out ctc);
      switch(oc) {
        case PipelineOutcome.ResolvedAndTypeChecked:
          ExecutionEngine.EliminateDeadVariables(program);
          ExecutionEngine.CollectModSets(program);
          ExecutionEngine.CoalesceBlocks(program);
          ExecutionEngine.Inline(program);
          errorList = new List<ErrorInformation>();
          var tmp = new List<ErrorInformation>();

          oc = ExecutionEngine.InferAndVerify(program, stats, programId, errorInfo => {
            tmp.Add(errorInfo);
          });
          errorList.AddRange(tmp);

          return oc;
        default:
          Contract.Assert(false);
          throw new cce.UnreachableException();  // unexpected outcome
      }
    }

  }

  public static class ObjectExtensions {
    private static readonly MethodInfo CloneMethod = typeof(Object).GetMethod("MemberwiseClone", BindingFlags.NonPublic | BindingFlags.Instance);

    public static bool IsPrimitive(this System.Type type) {
      if(type == typeof(String))
        return true;
      return (type.IsValueType & type.IsPrimitive);
    }

    public static object Copy(this object originalObject) {
      return InternalCopy(originalObject, new Dictionary<Object, Object>(new ReferenceEqualityComparer()));
    }
    private static object InternalCopy(Object originalObject, IDictionary<Object, Object> visited) {
      if(originalObject == null)
        return null;
      System.Type typeToReflect = originalObject.GetType();
      if(IsPrimitive(typeToReflect))
        return originalObject;
      if(visited.ContainsKey(originalObject))
        return visited[originalObject];
      if(typeof(Delegate).IsAssignableFrom(typeToReflect))
        return null;
      var cloneObject = CloneMethod.Invoke(originalObject, null);
      if(typeToReflect.IsArray) {
        var arrayType = typeToReflect.GetElementType();
        if(IsPrimitive(arrayType) == false) {
          Array clonedArray = (Array)cloneObject;
          clonedArray.ForEach((array, indices) => array.SetValue(InternalCopy(clonedArray.GetValue(indices), visited), indices));
        }

      }
      visited.Add(originalObject, cloneObject);
      CopyFields(originalObject, visited, cloneObject, typeToReflect);
      RecursiveCopyBaseTypePrivateFields(originalObject, visited, cloneObject, typeToReflect);
      return cloneObject;
    }

    private static void RecursiveCopyBaseTypePrivateFields(object originalObject, IDictionary<object, object> visited, object cloneObject, System.Type typeToReflect) {
      if(typeToReflect.BaseType != null) {
        RecursiveCopyBaseTypePrivateFields(originalObject, visited, cloneObject, typeToReflect.BaseType);
        CopyFields(originalObject, visited, cloneObject, typeToReflect.BaseType, BindingFlags.Instance | BindingFlags.NonPublic, info => info.IsPrivate);
      }
    }

    private static void CopyFields(object originalObject, IDictionary<object, object> visited, object cloneObject, System.Type typeToReflect, BindingFlags bindingFlags = BindingFlags.Instance | BindingFlags.NonPublic | BindingFlags.Public | BindingFlags.FlattenHierarchy, Func<FieldInfo, bool> filter = null) {
      foreach(FieldInfo fieldInfo in typeToReflect.GetFields(bindingFlags)) {
        if(filter != null && filter(fieldInfo) == false)
          continue;
        if(IsPrimitive(fieldInfo.FieldType))
          continue;
        var originalFieldValue = fieldInfo.GetValue(originalObject);
        var clonedFieldValue = InternalCopy(originalFieldValue, visited);
        fieldInfo.SetValue(cloneObject, clonedFieldValue);
      }
    }
    public static T Copy<T>(this T original) {
      return (T)Copy((Object)original);
    }
  }

  public class ReferenceEqualityComparer : EqualityComparer<Object> {
    public override bool Equals(object x, object y) {
      return ReferenceEquals(x, y);
    }
    public override int GetHashCode(object obj) {
      if(obj == null)
        return 0;
      return obj.GetHashCode();
    }
  }

  namespace ArrayExtensions {
    public static class ArrayExtensions {
      public static void ForEach(this Array array, Action<Array, int[]> action) {
        if(array.LongLength == 0)
          return;
        ArrayTraverse walker = new ArrayTraverse(array);
        do
          action(array, walker.Position);
        while(walker.Step());
      }
    }

    internal class ArrayTraverse {
      public int[] Position;
      private readonly int[] _maxLengths;

      public ArrayTraverse(Array array) {
        _maxLengths = new int[array.Rank];
        for(int i = 0; i < array.Rank; ++i) {
          _maxLengths[i] = array.GetLength(i) - 1;
        }
        Position = new int[array.Rank];
      }

      public bool Step() {
        for(int i = 0; i < Position.Length; ++i) {
          if(Position[i] < _maxLengths[i]) {
            Position[i]++;
            for(int j = 0; j < i; j++) {
              Position[j] = 0;
            }
            return true;
          }
        }
        return false;
      }
    }
  }

}

