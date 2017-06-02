#define _TACTIC_DEBUG_L1
///#define _TACTIC_DEBUG_L2


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

    public static bool CheckTacticArgs(ClassDecl curDecl, UpdateStmt stmt) {
      if(curDecl != null) {
        foreach(var member in curDecl.Members) {
          var tac = member as ITactic;
          if(tac != null && tac.Name == GetSignature(stmt)) {
            var aps = ((ExprRhs)stmt.Rhss[0]).Expr as ApplySuffix;
            return aps.Args.Count == tac.Ins.Count;
          }
        }
      }
      return false;
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

      foreach(var kvp in code) {
        InsertCodeInternal(body.Body, kvp.Value, kvp.Key);
      }

      return body;
    }

    private static void InsertCodeInternal(List<Statement> body, List<Statement> code, Statement tacticCall) {
      Contract.Requires<ArgumentNullException>(body != null, "body ");
      Contract.Requires<ArgumentNullException>(tacticCall != null, "'tacticCall");

      for(var i = 0; i < body.Count; i++) {
        var stmt = body[i];
        if ((stmt as AssertStmt)?.Proof != null) {
          InsertCodeInternal((stmt as AssertStmt).Proof.Body, code, tacticCall);
        } else if(stmt is UpdateStmt || stmt is InlineTacticBlockStmt) {
          // compare tokens
          if(Compare(tacticCall.Tok, stmt.Tok)) {
            body.RemoveAt(i);
            body.InsertRange(i, code);
            return;
          }
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


    public static Program GenerateResolvedProg(ProofState state) {
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
    public static bool VerifyResolvedProg(ProofState state, Program program, ErrorReporterDelegate er) {
      Contract.Requires<ArgumentNullException>(program != null);
      
     #if _TACTIC_DEBUG_L2
            var printer = new Printer(Console.Out);
            Console.WriteLine("*********************Verifying Tactic Generated Prog*****************");
            printer.PrintProgram(program, true);
            Console.WriteLine("\n*********************Prog END*****************");
     #endif

      _verificationCount++;
      Console.WriteLine("Verfication Count: " + _verificationCount);

      var boogieProg = Translator.Translate(program, program.reporter, null);

      foreach(var prog in boogieProg) {
        PipelineStatistics stats;
        List<ErrorInformation> errorList;
        PipelineOutcome tmp = BoogiePipeline(prog.Item2,
          new List<string> { program.Name }, program.Name, er,
          out stats, out errorList, program);
        if(errorList.Count != 0) {
          foreach (var err in errorList) {
            // exists an error byond the current tactic, so the current tactic goes through
            if (err.Tok.pos > state.TopLevelTacApp.Tok.pos) {
              state.GetErrHandler().ErrorList = errorList;
              return true;
            }
          }
          return false;
        }
      }
      return true;
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

