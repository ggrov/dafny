using System;
using System.Collections.Generic;
using Microsoft.Dafny;
using NUnit.Framework;
using System.IO;
using System.Linq;
using System.Numerics;

namespace Quicky
{

  [TestFixture]
  class Tests
  {
    public static Quicky GetQuicky(string filename) {
      QuickyMain.SetupEnvironment();
      Program dafnyProgram =
        QuickyMain.CreateProgramFromFileName(Directory.GetParent(QuickyMain.BinariesDirectory()) + @"\Test\quicky\"+filename);
      
      Resolver resolver = new Resolver(dafnyProgram);
      resolver.ResolveProgram(dafnyProgram);
      
      return new Quicky(dafnyProgram, 100, true);
    }
    
    [Test]
    public void TestCompiler() {
      QuickyMain.PrintCompiledCode = "C:\\Users\\Duncan\\Documents\\Test.cs";
      GetQuicky("VariousFails.dfy");
//      GetQuicky("Zip.dfy");
      //if no exception is thrown, the program successfully compiled something.
    }


    //Runs a file and ensures that the program finds the right errors - the dictionary should contain counts for types of errors
    public void TestForNErrors(string filename, Dictionary<QuickyError.ErrorType, int> expectedErrors) {
      var quicky = GetQuicky(filename);
      quicky.PerformTesting();

      Dictionary<QuickyError.ErrorType, int> foundErrors = new Dictionary<QuickyError.ErrorType, int>();
      foreach (var quickyError in quicky.FoundErrors.Values) {
        Console.WriteLine("Exception on line " + quickyError.Line + ": ");
        Console.WriteLine(quickyError.Message+"\n");
        if (foundErrors.ContainsKey(quickyError.TypeOfError))
          foundErrors[quickyError.TypeOfError]++;
        else
          foundErrors.Add(quickyError.TypeOfError, 1);
      }

      Assert.AreEqual(expectedErrors.Count, foundErrors.Count, "Incorrect number of different types of errors found");
      foreach (var error in expectedErrors.Keys)
        Assert.AreEqual(expectedErrors[error], foundErrors[error], "Incorrect number of errors of type "+error);
    }

    [Test]
    public void TestPostConditionFail() {
      string filename = "PostConditionFail.dfy";
      var errorCounts = new Dictionary<QuickyError.ErrorType, int>() {
        {QuickyError.ErrorType.Postcondition, 1}
      };
      TestForNErrors(filename, errorCounts);
    }

    [Test]
    public void TestAssertFail() {
      string filename = "AssertFail.dfy";
      var errorCounts = new Dictionary<QuickyError.ErrorType, int>() {
        {QuickyError.ErrorType.Assert, 1}
      };
      TestForNErrors(filename, errorCounts);
    }

    [Test]
    public void LoopInvariantEntryFail() {
      string filename = "LoopEntryFail.dfy";
      var errorCounts = new Dictionary<QuickyError.ErrorType, int>() {
        {QuickyError.ErrorType.InvariantEntry, 1}
      };
      TestForNErrors(filename, errorCounts);
    }

    [Test]
    public void TestLoopInvariantEndFail() {
      string filename = "LoopEndFail.dfy";
//      QuickyMain.PrintCompiledCode = "C:\\Users\\Duncan\\Documents\\Test.cs";
      var errorCounts = new Dictionary<QuickyError.ErrorType, int>() {
        {QuickyError.ErrorType.InvariantEnd, 1}
      };
      TestForNErrors(filename, errorCounts);
    }

    [Test]
    public void TestVariantFail() {
      string filename = "Variants.dfy";
      var errorCounts = new Dictionary<QuickyError.ErrorType, int>() {
        {QuickyError.ErrorType.Variant, 1}
      };
      TestForNErrors(filename, errorCounts);
    }

    [Test]
    public void TestSetsAndSequences() {
      string filename = "SetsSequences.dfy";
//      QuickyMain.PrintCompiledCode = "C:\\Users\\Duncan\\Documents\\Test.cs";
      var errorCounts = new Dictionary<QuickyError.ErrorType, int>() {
        {QuickyError.ErrorType.Assert, 2}
      };
      TestForNErrors(filename, errorCounts);
    }

    [Test]
    public void TestVariousFailures() {
      string fileName = "VariousFails.dfy";
//      QuickyMain.PrintCompiledCode = "C:\\Users\\Duncan\\Documents\\Test.cs";
      var errorCounts = new Dictionary<QuickyError.ErrorType, int>() {
        {QuickyError.ErrorType.Postcondition, 2},
        {QuickyError.ErrorType.Assert, 3},
        {QuickyError.ErrorType.InvariantEntry, 1},
        {QuickyError.ErrorType.InvariantEnd, 1},
        {QuickyError.ErrorType.PreconditionCall, 1}
      };
      TestForNErrors(fileName, errorCounts);
    }

    [Test]
    public void TestModules() {
      string filename = "modules.dfy";
      var errorCounts = new Dictionary<QuickyError.ErrorType, int>() {
        {QuickyError.ErrorType.Assert, 2} //ignores non-static method
      };
      TestForNErrors(filename, errorCounts);
    }

    [Test]
    public void TestLemmaCalls() {
      string filename = "LemmaCall.dfy";
//      QuickyMain.PrintCompiledCode = "C:\\Users\\Duncan\\Documents\\Test.cs";

      var errorCounts = new Dictionary<QuickyError.ErrorType, int>() {
        {QuickyError.ErrorType.PreconditionCall, 1 }
      };
      TestForNErrors(filename, errorCounts);

    }

    [Test]
    public void TestDataTypes() {
      string filename = "DataTypes.dfy";
//      QuickyMain.PrintCompiledCode = "C:\\Users\\Duncan\\Documents\\Test.cs";

      var errorCounts = new Dictionary<QuickyError.ErrorType, int>() {
        
      };
      TestForNErrors(filename, errorCounts);

    }
  }

  [TestFixture]
  class ParamterGenerationTests
  {
    public static Method GetProgramMethod(Program dafnyProgram) {
      return ((ClassDecl) dafnyProgram.DefaultModuleDef.TopLevelDecls[0]).Members[0] as Method;
    }

    public static Program GetProgram(string filename) {
      QuickyMain.SetupEnvironment();
      Program dafnyProgram =
        QuickyMain.CreateProgramFromFileName(Directory.GetParent(QuickyMain.BinariesDirectory()) + @"\Test\quicky\param\" + filename);

      Resolver resolver = new Resolver(dafnyProgram);
      resolver.ResolveProgram(dafnyProgram);

      return dafnyProgram;
    }

    public static ParameterSetGenerator GetParameterSetGenerator(string filename) {
      Program program = GetProgram(filename);
      Method method = GetProgramMethod(program);
      Quicky quicky = new Quicky(program);
      return new ParameterSetGenerator(quicky, method);
    }

    [Test]
    public void TestGettingGenerator() {
      var paramterSetGenerator = GetParameterSetGenerator("SingleInt.dfy");
      Assert.NotNull(paramterSetGenerator);
    }

    private void TestNextArrayInputSimple(object[] expected, ParameterSetGenerator generator) {
      //convert ints to big ints!
      for (int i = 0; i < expected.Length; i++) {
        if(expected[i] is int)
          expected[i] = new BigInteger((int)expected[i]);
      }
      Assert.AreEqual(expected, generator.GetNextParameterSet().Skip(1).ToArray()); // skip is to skip quickyChecker

    }

    private void TestNextArraySum(int expectedTotal, ParameterSetGenerator generator) {
      
      var array = generator.GetNextParameterSet().Skip(1).ToArray(); // skip is to skip quickyChecker
      int[] intArray = new int[array.Length];
      Console.Write("{");
      for (int i = 0; i < array.Length; i++) {
        if(i>0) Console.Write(", ");
        int origIndex = RevertToIndex((int)(BigInteger)array[i]); //need to revert index to determine simplicity total
        intArray[i] = origIndex;
        Console.Write(intArray[i]);
      }
      Console.WriteLine("}");
      int actualTotal = intArray.Sum();
      Assert.AreEqual(expectedTotal, actualTotal);
    }

    private int RevertToIndex(int n) {
      switch (n) {
        case 0:
          return 1;
        case 1:
          return 0;
        case -1:
          return 2;
        case 10:
          return 3;
        default: throw new Exception("(Testing) Cannot revert the index of "+n);
      }
    }

    [Test]
    public void TestSingleInts() {
      var generator = GetParameterSetGenerator("SingleInt.dfy");
      TestNextArrayInputSimple(new object[] {1}, generator);
      TestNextArrayInputSimple(new object[] {0}, generator);
      TestNextArrayInputSimple(new object[] {-1}, generator);
      //TODO something with ranges?
    }

    [Test]
    public void TestTwoInts() {
      var generator = GetParameterSetGenerator("TwoInts.dfy");
      TestNextArrayInputSimple(new object[] {1, 1}, generator);
      TestNextArraySum(1, generator); //{0,1}, {1,0}
      TestNextArraySum(1, generator);
      TestNextArraySum(2, generator); //{1,1}{2,0}{0,2}, 
      TestNextArraySum(2, generator);
      TestNextArraySum(2, generator);
      TestNextArraySum(3, generator); // {1,2}{2,1}{3,0}{0,3}
      TestNextArraySum(3, generator);
      TestNextArraySum(3, generator);
      TestNextArraySum(3, generator);
      }
   }
}