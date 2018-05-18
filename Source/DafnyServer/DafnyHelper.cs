using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Runtime.Serialization.Json;
using System.Text;
using Microsoft.Boogie;
using DafnyServer;
using Bpl = Microsoft.Boogie;
using Dare;

namespace Microsoft.Dafny {
  // FIXME: This should not be duplicated here
  class DafnyConsolePrinter : ConsolePrinter {
    public override void ReportBplError(IToken tok, string message, bool error, TextWriter tw, string category = null) {
      // Dafny has 0-indexed columns, but Boogie counts from 1
      var realigned_tok = new Token(tok.line, tok.col - 1);
      realigned_tok.kind = tok.kind;
      realigned_tok.pos = tok.pos;
      realigned_tok.val = tok.val;
      realigned_tok.filename = tok.filename;
      base.ReportBplError(realigned_tok, message, error, tw, category);

      if (tok is Dafny.NestedToken) {
        var nt = (Dafny.NestedToken)tok;
        ReportBplError(nt.Inner, "Related location", false, tw);
      }
    }
  }

  class TacticsConsolePrinter {
    private readonly List<ErrorInformation> tacticErrors;

    public TacticsConsolePrinter() {
      this.tacticErrors = new List<ErrorInformation>();
    }

    public void ReporterDelegate(ErrorInformation errInfo) {
      this.tacticErrors.Add(errInfo);
    }

    public void ReportAll() {
      if(tacticErrors.Count == 0) {
        Console.WriteLine("TACTICS_START [] TACTICS_END");
      } else {
        Console.WriteLine("TACTICS_START " + ConvertToJson(this.tacticErrors) + " TACTICS_END");
      }
    }

    private static string ConvertToJson<T>(T data) {
      var serializer = new DataContractJsonSerializer(typeof(T));
      using (var ms = new MemoryStream())
      {
        serializer.WriteObject(ms, data);
        return Encoding.Default.GetString(ms.ToArray());
      }
    }
  }

  class DafnyHelper {
    private string fname;
    private string source;
    private string[] args;
    
    private Resolver resolver;
    private readonly TacticsConsolePrinter tacticsReporter;
    private readonly Dafny.ErrorReporter reporter;
    private Dafny.Program dafnyProgram;
    private IEnumerable<Tuple<string, Bpl.Program>> boogiePrograms;

    public static bool TacticVerificationEnabled {
      get {
        return Microsoft.Dafny.Tacny.TacnyDriver.IfEvalTac;
      }
      set {
        Microsoft.Dafny.Tacny.TacnyDriver.IfEvalTac = value;
        Console.WriteLine("tacticVerificationEnabled=" + (value ? "T" : "F"));
      }
    }

    private static string UnresolvedResponse() {
      var unresolvedError = new Microsoft.Dafny.Tacny.TacticExpansion(
        Microsoft.Dafny.Tacny.TacticExpandStatus.NotResolved
      );
      return ConvertToJson(unresolvedError);
    }

    public void ExpandAll() {
      if (Parse() && Resolve()) {
        var replacements = Microsoft.Dafny.Tacny.TacticExpander.ExpandAll(this.dafnyProgram);
        Console.WriteLine("EXPANDED_TACTIC " +
          ConvertToJson(replacements) +
          " EXPANDED_TACTIC_END");
      } else {
        Console.WriteLine("EXPANDED_TACTIC " + UnresolvedResponse() + " EXPANDED_TACTIC_END");
      }
    }

    public void Expand() {
      if (Parse() && Resolve()) {
        var position = Int32.Parse(this.args[0]);
        var replacement = Microsoft.Dafny.Tacny.TacticExpander.Expand(this.dafnyProgram, position);
        Console.WriteLine("EXPANDED_TACTIC " +
          ConvertToJson(replacement) +
          " EXPANDED_TACTIC_END");
      } else {
        Console.WriteLine("EXPANDED_TACTIC " + UnresolvedResponse() + " EXPANDED_TACTIC_END");
      }
    }

    public void CheckForDeadAnnotations() {
      if (Parse() && Resolve()) {
        var stopper = new Dare.StopChecker();
        var dare = new Dare.Dare(stopper);
        var results = dare.ProcessProgram(dafnyProgram);
        if(results.Count == 0) {
          Console.WriteLine("DEAD_ANNOTATIONS [] DEAD_ANNOTATIONS_END");
        } else {
          var output = "DEAD_ANNOTATIONS [";
          for(var i = 0; i < results.Count - 1; i++) {
            output += results[i].asJson() + ",";
          }
          output += results[results.Count-1].asJson() + "] DEAD_ANNOTATIONS_END";
          Console.WriteLine(output);
        }
      } else {
        Console.WriteLine("DEAD_ANNOTATIONS [] DEAD_ANNOTATIONS_END");
      };
    }

    public DafnyHelper(string[] args, string fname, string source) {
      this.args = args;
      this.fname = fname;
      this.source = source;
      this.reporter = new Dafny.ConsoleErrorReporter();
      this.tacticsReporter = new TacticsConsolePrinter();
      Console.WriteLine("tacticVerificationEnabled=" + (DafnyHelper.TacticVerificationEnabled ? "T" : "F"));
    }

    public bool Verify() {
      ServerUtils.ApplyArgs(args, reporter);
      return Parse() && Resolve() && Translate() && Boogie();
    }

    private bool Parse() {
      Dafny.ModuleDecl module = new Dafny.LiteralModuleDecl(new Dafny.DefaultModuleDecl(), null);
      Dafny.BuiltIns builtIns = new Dafny.BuiltIns();
      var success = (Dafny.Parser.Parse(source, fname, fname, null, module, builtIns, new Dafny.Errors(reporter)) == 0 &&
                     Dafny.Main.ParseIncludes(module, builtIns, new List<string>(), new Dafny.Errors(reporter)) == null);
      if (success) {
        dafnyProgram = new Dafny.Program(fname, module, builtIns, reporter) {
          Raw = source
        };
      }
      return success;
    }

    private bool Resolve() {
      resolver = new Dafny.Resolver(dafnyProgram);
      resolver.ResolveProgram(dafnyProgram);
      return reporter.Count(ErrorLevel.Error) == 0;
    }

    private bool Translate() {
      boogiePrograms = Translator.Translate(dafnyProgram,reporter, resolver,
          new Translator.TranslatorFlags() { InsertChecksums = true, UniqueIdPrefix = fname },
          tacticsReporter.ReporterDelegate); // FIXME how are translation errors reported?
      tacticsReporter.ReportAll();
      return true;
    }

    private bool BoogieOnce(string moduleName, Bpl.Program boogieProgram) {
      if (boogieProgram.Resolve() == 0 && boogieProgram.Typecheck() == 0) { //FIXME ResolveAndTypecheck?
        ExecutionEngine.EliminateDeadVariables(boogieProgram);
        ExecutionEngine.CollectModSets(boogieProgram);
        ExecutionEngine.CoalesceBlocks(boogieProgram);
        ExecutionEngine.Inline(boogieProgram);

        //NOTE: We could capture errors instead of printing them (pass a delegate instead of null)
        switch (ExecutionEngine.InferAndVerify(boogieProgram, new PipelineStatistics(), "ServerProgram_" + moduleName, null, DateTime.UtcNow.Ticks.ToString())) {
          case PipelineOutcome.Done:
          case PipelineOutcome.VerificationCompleted:
            return true;
        }
      }

      return false;
    }

    private bool Boogie() {
      var isVerified = true;
      foreach (var boogieProgram in boogiePrograms) {
        isVerified = isVerified && BoogieOnce(boogieProgram.Item1, boogieProgram.Item2);
      }
      return isVerified;
    }

    public void Symbols() {
      ServerUtils.ApplyArgs(args, reporter);
      if (Parse() && Resolve()) {
        var symbolTable = new SymbolTable(dafnyProgram);
        var symbols = symbolTable.CalculateSymbols();
        Console.WriteLine("SYMBOLS_START " + ConvertToJson(symbols) + " SYMBOLS_END");
      } else {
        Console.WriteLine("SYMBOLS_START [] SYMBOLS_END");
      }
    }

    public void CounterExample() {
      var listArgs = args.ToList();
      listArgs.Add("/mv:" + CounterExampleProvider.ModelBvd);
      ServerUtils.ApplyArgs(listArgs.ToArray(), reporter);
      try {
        if (Parse() && Resolve() && Translate()) {
          var counterExampleProvider = new CounterExampleProvider();
          foreach (var boogieProgram in boogiePrograms) {
            RemoveExistingModel();
            BoogieOnce(boogieProgram.Item1, boogieProgram.Item2);
            var model = counterExampleProvider.LoadCounterModel();
            Console.WriteLine("COUNTEREXAMPLE_START " + ConvertToJson(model) + " COUNTEREXAMPLE_END");
          }
        }
      } catch (Exception e) {
        Console.WriteLine("Error collection models: " + e.Message);
      }
    }

    private void RemoveExistingModel() {
      if (File.Exists(CounterExampleProvider.ModelBvd)) {
        File.Delete(CounterExampleProvider.ModelBvd);
      }
    }

    public void DotGraph() {
      ServerUtils.ApplyArgs(args, reporter);

      if (Parse() && Resolve() && Translate()) {
        foreach (var boogieProgram in boogiePrograms) {
          BoogieOnce(boogieProgram.Item1, boogieProgram.Item2);

          foreach (var impl in boogieProgram.Item2.Implementations) {
            using (StreamWriter sw = new StreamWriter(fname + impl.Name + ".dot")) {
              sw.Write(boogieProgram.Item2.ProcessLoops(impl).ToDot());
            }
          }
        }
      }
    }

    private static string ConvertToJson<T>(T data) {
      var serializer = new DataContractJsonSerializer(typeof(T));
      using (var ms = new MemoryStream()) {
        serializer.WriteObject(ms, data);
        return Encoding.Default.GetString(ms.ToArray());
      }
    }
  }
}
