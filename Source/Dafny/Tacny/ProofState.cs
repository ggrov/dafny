using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Diagnostics.Contracts;
using System.Linq;
using Microsoft.Boogie;
using Dfy = Microsoft.Dafny;
using Microsoft.Dafny.Tacny.Language;

namespace Microsoft.Dafny.Tacny{
  public class ProofState{
    // Static State
    public readonly Dictionary<string, DatatypeDecl> Datatypes;
    public TopLevelClassDeclaration ActiveClass;
    private readonly List<TopLevelClassDeclaration> _topLevelClasses;
    private readonly Program _original;

    private TacticBasicErr _errHandler;
    private int _verifyNCount = 1;
    // Dynamic State
    public MemberDecl TargetMethod;

    //not all the eval step requires to be verified, e.g. var decl
    public bool NeedVerify { set; get; } = false;

    public bool InAsserstion { set; get; } = false;
    public Statement TopLevelTacApp;
    private Stack<Frame> _scope;

    public ProofState(Program program){
      Contract.Requires(program != null);
      // get a new program instance
      Datatypes = new Dictionary<string, DatatypeDecl>();
      _topLevelClasses = new List<TopLevelClassDeclaration>();
      var files = new List<DafnyFile> {new DafnyFile(program.FullName)};

      
      if (program.Raw == null)
        Main.Parse(files, program.Name, new ConsoleErrorReporter(), out _original);
      else {
        /*
        System.IO.StreamReader reader = new System.IO.StreamReader(program.FullName);
         var s = Microsoft.Boogie.ParserHelper.Fill(reader, new List<string>());
        program.Raw = s;
        */
          var reporter = new ConsoleErrorReporter();
        ModuleDecl module = new LiteralModuleDecl(new DefaultModuleDecl(), null);
        BuiltIns builtIns = new BuiltIns();
        Parser.Parse(program.Raw, program.FullName, program.FullName, module, builtIns, reporter);

        _original = new Program(program.FullName, module, builtIns, reporter);
      }

      // fill state
      FillStaticState(program);
    }

    //get the unresoved version of this tactic application stmt
    internal UpdateStmt GetTacticAppStmt(UpdateStmt tacAps) {
      var prog = this._original;
      Method destMd = null;
      foreach(var m in prog.DefaultModuleDef.TopLevelDecls) {
        if(m.WhatKind == "class") {
          var classDecl = m as DefaultClassDecl;
          if(classDecl != null) {
            foreach(var method in classDecl.Members) {
              if(method.Name == TargetMethod.Name) {
                destMd = (method as Method);
                break;
              }
            }
            if (destMd != null){
              break;
            }
          }
        }
      }

      return GetTacticAppStmt(tacAps.Tok.pos, destMd.Body);
    }

    internal UpdateStmt GetTacticAppStmt(int pos, BlockStmt stmts) {
      if(stmts.Body == null)
        return null;
      return GetTacticAppStmt(pos, stmts.Body);
    }
    internal UpdateStmt GetTacticAppStmt(int pos, List<Statement> stmts) {
      UpdateStmt ret = null;
      foreach(var stmt in stmts) {
        if(stmt is UpdateStmt && stmt.Tok.pos == pos)
          return stmt as UpdateStmt;
        else if(stmt is BlockStmt) {
          ret = GetTacticAppStmt(pos, stmt as BlockStmt);
        } else if(stmt is MatchStmt) {
          var match = stmt as MatchStmt;
          foreach(var cases in match.Cases) {
            ret = GetTacticAppStmt(pos, cases.Body);
            if(ret != null)
              break;
          }
        } else if(stmt is ForallStmt) {
          //TODO
        }
        else if (stmt is AssertStmt && (stmt as AssertStmt).Proof != null) {
            ret = GetTacticAppStmt(pos, (stmt as AssertStmt).Proof);
          }
        if(ret != null)
          break;
      }

      return ret;
    }
    /// <summary>
    /// Initialize a new tactic state
    /// </summary>
    /// <param name="tacAps">Tactic application</param>
    /// <param name="variables">Dafny variables</param>
    public bool InitState(Statement tacAps, Dictionary<IVariable, Dfy.Type> variables,  bool ifPartial){
      // clear the scope  
      _scope = new Stack<Frame>();

      List<Statement> body = new List<Statement>();
      Attributes attrs, tacticAttrs; // attrs from tactic call, and the attrs from tactic definitions.
      ApplySuffix aps = null;
      Tactic tactic = null;
      string errMsg;

      if (tacAps is UpdateStmt) {
        tactic = GetTactic(tacAps as UpdateStmt) as Tactic;
        aps  = ((ExprRhs)((UpdateStmt)tacAps).Rhss[0]).Expr as ApplySuffix;
        if (!Util.CheckTacticArgs(tactic, aps, this, out errMsg)) {
          ReportTacticError(tacAps.Tok, errMsg);
        }
        //get the unresoved stmt
        tacAps = GetTacticAppStmt((UpdateStmt)tacAps);
        aps = ((ExprRhs)((UpdateStmt)tacAps).Rhss[0]).Expr as ApplySuffix;


        tacticAttrs = tactic.Attributes;
        attrs = (tacAps as UpdateStmt).Rhss[0].Attributes;
        if (tactic.Req != null) {
          foreach (var expr in tactic.Req) {
            body.Add(
              new TacticAssertStmt(
                new Token(TacnyDriver.TacticCodeTokLine, 0) { val = "tassert" },
                new Token(TacnyDriver.TacticCodeTokLine, 0) { val = ";" },
                expr.E,
                null, false));
          }
        }
        body.AddRange(tactic.Body.Body);
        if (tactic.Ens != null) {
          foreach (var expr in tactic.Ens) {
            body.Add(
              new TacticAssertStmt(
                new Token(TacnyDriver.TacticCodeTokLine, 0) { val = "tassert" },
                new Token(TacnyDriver.TacticCodeTokLine, 0) { val = ";" },
                expr.E,
                null, false));
          }
        }
      } else if (tacAps is InlineTacticBlockStmt) {
        body = (tacAps as InlineTacticBlockStmt).Body.Body;
        attrs = (tacAps as InlineTacticBlockStmt).Attributes;
        tacticAttrs = null;
      } else {
        throw new Exception("Unexpceted tactic applciation statement.");
      }


      var frame = new Frame(body, ifPartial, attrs, tacticAttrs);

      foreach (var item in variables){
        if (!frame.ContainDafnyVar(item.Key.Name))
          frame.AddDafnyVar(item.Key.Name, new VariableData{Variable = item.Key, Type = item.Value});
        else
          throw new ArgumentException($"Dafny variable {item.Key.Name} is already declared in the current context");
      }
      if (aps != null) {
        for (int index = 0; index < aps.Args.Count; index++) {
          var arg = aps.Args[index];
          if (tactic != null) frame.AddTVar(tactic.Ins[index].Name, arg);
        }
      }
      _scope.Push(frame);
      ResetVerifyN();
      TopLevelTacApp = tacAps.Copy();

      if (tactic != null && (aps != null && aps.Args.Count != tactic.Ins.Count))
        ReportTacticError(tacAps.Tok,
          $"Wrong number of method arguments (got {aps.Args.Count}, expected {tactic.Ins.Count})");

      return _scope.Peek().FrameCtrl.enabled;

    }

    public void ReportTacticError(IToken t, string msg)
    {
      GetErrHandler().Reporter.Error(MessageSource.Tactic, t, msg);
    }

    // Permanent state information
    public Dictionary<string, ITactic> Tactics => ActiveClass.Tactics;
    public Dictionary<string, MemberDecl> Members => ActiveClass.Members;

    public TacticBasicErr GetErrHandler()
    {
      return _errHandler ?? (_errHandler = new TacticBasicErr());
    }
    public Program GetDafnyProgram(){
      //Contract.Requires(_original != null, "_original");
      Contract.Ensures(Contract.Result<Program>() != null);
      var copy = _original.Copy();
      return copy;
    }


    /// <summary>
    ///   Set active the enclosing TopLevelClass
    /// </summary>
    /// <param name="name"></param>
    public void SetTopLevelClass(string name){
      ActiveClass = _topLevelClasses.FirstOrDefault(x => x.Name == name);
    }

    /// <summary>
    ///   Fill permanent state information, which will be common across all tactics
    /// </summary>
    /// <param name="program">fresh Dafny program</param>
    private void FillStaticState(Program program){
      Contract.Requires<ArgumentNullException>(program != null);


      foreach (var item in program.DefaultModuleDef.TopLevelDecls){
        var curDecl = item as ClassDecl;
        if (curDecl != null){
          var temp = new TopLevelClassDeclaration(curDecl.Name);

          foreach (var member in curDecl.Members){
            var tac = member as ITactic;
            if (tac != null)
              temp.Tactics.Add(tac.Name, tac);
            else{
              temp.Members.Add(member.Name, member);
            }
          }
          _topLevelClasses.Add(temp);
        }
        else{
          var dd = item as DatatypeDecl;
          if (dd != null)
            Datatypes.Add(dd.Name, dd);
        }
      }
    }

    public bool IsTimeOut(){
      var top = _scope.Peek();
      if(top.FrameCtrl.TimeStamp != 0 && top.FrameCtrl.TimeStamp <= TacnyDriver.GetTimer().Elapsed.Seconds) 
        return true;

      return false;
    }

    public void AddNewFrame(TacticFrameCtrl ctrl){
      var parent = _scope.Peek();
      if (parent.FrameCtrl.TimeStamp != 0){
        if (ctrl.TimeStamp == 0 || parent.FrameCtrl.TimeStamp < ctrl.TimeStamp)
          ctrl.TimeStamp = parent.FrameCtrl.TimeStamp;
      }
      _scope.Push(new Frame(parent, ctrl));
      ResetVerifyN();
    }
    // note that this function would only be called when either a frame is proved or isEvaluated.
    public void MarkCurFrameAsTerminated(bool curFrameProved, out bool backtracked){

      //assemble code in the top frame. the stata that code is null after this call, indicates
      // the current branches has been backtrackee.
      // 
      bool ifbacktracked, ifbacktrackedInRecurCall = false;
      _scope.Peek().FrameCtrl.MarkAsEvaluated(curFrameProved, out ifbacktracked);

      var code = _scope.Peek().FrameCtrl.GetFinalCode();

      // add the assembled code to the parent frame
      if (code != null && _scope.Peek().Parent != null){
        _scope.Peek().Parent.FrameCtrl.AddGeneratedCode(code);
        _scope.Pop();
        if (_scope.Peek().FrameCtrl.EvalTerminated(curFrameProved, this) || IsEvaluated())
           MarkCurFrameAsTerminated(curFrameProved, out ifbacktrackedInRecurCall);
      }
      backtracked = ifbacktracked || ifbacktrackedInRecurCall;
    }

    public IEnumerable<ProofState> EvalStep(){
      //clear previous error messages before moving onto the next stmt
      GetErrHandler().ClearErrMsg();
      return _scope.Peek().FrameCtrl.EvalStep(this);
    }

    public IEnumerable<ProofState> ApplyPatch() {
      return _scope.Peek().FrameCtrl.ApplyPatch(this);
    }



    public Statement GetLastStmt() {
      var stmt =  _scope.Peek().FrameCtrl.GetLastStmt();
      return stmt ?? TopLevelTacApp;
     
    }

    public bool IsCurFramePartial(){
      return _scope.Peek().FrameCtrl.IsPartial;
    }

    public List<int> GetBackTrackCount(){
      var frame = _scope.Peek();
      var backtrack = new List<int> {frame.FrameCtrl.Backtrack};

      while (frame.Parent != null){
        frame = frame.Parent;
        backtrack.Add(frame.FrameCtrl.Backtrack);
      }

      return backtrack;
    }

    public int GetVerifyN() {
      return _verifyNCount;
    }


    public void DecreaseVerifyN()
    {
      if (_verifyNCount > 1)
        _verifyNCount--;
    }

    public int ResetVerifyN() {
      return _verifyNCount = _scope.Peek().FrameCtrl.VerifyN;
    }

    public int GetOrignalTopBacktrack(){
      return _scope.Peek().FrameCtrl.OriginalBk;
    }

    public void SetBackTrackCount(List<int> cnt){
      var cur = GetBackTrackCount();
      //restore from the root
      cur.Reverse();
      List<int> tmp = cnt.Copy();
      tmp.Reverse();

      for (int j = 0; j < cur.Count; j++){
        int count;
        count = j >= tmp.Count ? cur[j] : tmp[j];
        cur[j] = count;
      }

      cur.Reverse();

      var frame = _scope.Peek();
      frame.FrameCtrl.Backtrack = cur[0];
      cur.RemoveAt(0);

      while(frame.Parent != null) {
        frame = frame.Parent;
        frame.FrameCtrl.Backtrack = cur[0];
        cur.RemoveAt(0);
      }
    }
    /// <summary>
    /// a proof state is verified if there is only one frame in the stack and _genratedCode is not null (raw code are assembled)
    /// </summary>
    /// <returns></returns>
    public bool IsTerminated(){
      return _scope.Count == 1 && _scope.Peek().FrameCtrl.GetFinalCode() != null;
    }

    /// <summary>
    /// Check if the current frame is fully interpreted by tracking counts of stmts
    /// </summary>
    /// <returns></returns>
    public bool IsCurFrameEvaluated(){
      return _scope.Peek().FrameCtrl.IsEvaluated;
    }

    public bool IsEvaluated()
    {
      return _scope.Count == 1 && IsCurFrameEvaluated();
    }


    public List<Statement> GetGeneratedCode(){
      // Contract.Ensures(Contract.Result<List<Statement>>() != null);
      return _scope.Peek().GetGeneratedCode();
    }

    /// <summary>
    ///   Check if Dafny key exists in the current context
    /// </summary>
    /// <param name="key">Variable name</param>
    /// <returns>bool</returns>
    public bool ContainDafnyVar(string key){
      Contract.Requires<ArgumentNullException>(Tcce.NonNull(key));
      return _scope.Peek().ContainDafnyVar(key);
    }


    /// <summary>
    ///   Check if Dafny key exists in the current context
    /// </summary>
    /// <param name="key">Variable</param>
    /// <returns>bool</returns>

    public bool ContainDafnyVar(NameSegment key){
      Contract.Requires<ArgumentNullException>(Tcce.NonNull(key));
      return ContainDafnyVar(key.Name);
    }

    /// <summary>
    ///   Return Dafny key
    /// </summary>
    /// <param name="key">Variable name</param>
    /// <returns>bool</returns>
    /// <exception cref="KeyNotFoundException">Variable does not exist in the current context</exception>
    public IVariable GetDafnyVar(string key){
      Contract.Requires<ArgumentNullException>(Tcce.NonNull(key));
      Contract.Ensures(Contract.Result<IVariable>() != null);
      if (ContainDafnyVar(key))
        return _scope.Peek().GetDafnyVariableData(key).Variable;
      throw new KeyNotFoundException($"Dafny variable {key} does not exist in the current context");
    }

    /// <summary>
    ///   Return Dafny key
    /// </summary>
    /// <param name="key">Variable name</param>
    /// <returns>bool</returns>
    /// <exception cref="KeyNotFoundException">Variable does not exist in the current context</exception>
    public IVariable GetDafnyVar(NameSegment key){
      Contract.Requires<ArgumentNullException>(Tcce.NonNull(key));
      Contract.Ensures(Contract.Result<IVariable>() != null);
      return GetDafnyVar(key.Name);
    }

    /// <summary>
    /// get a dictionary containing all the dafny variable in current scope, including all the frame. If the variable will be ignore, if it confilts with some other top frames
    /// </summary>
    /// <returns></returns>
    public Dictionary<string, VariableData> GetAllDafnyVars(){
      return _scope.Peek().GetAllDafnyVars(new Dictionary<string, VariableData>());
    }

    /// <summary>
    ///   Return the type of the key
    /// </summary>
    /// <param name="variable">key</param>
    /// <returns>null if type is not known</returns>
    /// <exception cref="KeyNotFoundException">Variable does not exist in the current context</exception>
    public Dfy.Type GetDafnyVarType(IVariable variable){
      Contract.Requires<ArgumentNullException>(Tcce.NonNull(variable));
      Contract.Ensures(Contract.Result<Dfy.Type>() != null);
      return GetDafnyVarType(variable.Name);
    }

    /// <summary>
    ///   Return the type of the key
    /// </summary>
    /// <param name="key">name of the key</param>
    /// <returns>null if type is not known</returns>
    /// <exception cref="KeyNotFoundException">Variable does not exist in the current context</exception>
    public Dfy.Type GetDafnyVarType(string key){
      Contract.Requires<ArgumentNullException>(Tcce.NonNull(key));
      Contract.Ensures(Contract.Result<Dfy.Type>() != null);
      if (ContainDafnyVar(key))
        return GetDafnyVar(key).Type;
      throw new KeyNotFoundException($"Dafny variable {key} does not exist in the current context");
    }

    /// <summary>
    /// Get the value of local variable
    /// </summary>
    /// <param name="key"></param>
    /// <returns></returns>
    public Expression GetTVarValue(NameSegment key){
      Contract.Requires<ArgumentNullException>(key != null, "key");
      Contract.Ensures(Contract.Result<Expression>() != null);
      return GetTVarValue(key.Name);
    }

    /// <summary>
    /// Get the value of local variable
    /// </summary>
    /// <param name="key"></param>
    /// <returns></returns>
    public Expression GetTVarValue(string key){
      Contract.Requires<ArgumentNullException>(key != null, "key");
      Contract.Ensures(Contract.Result<Expression>() != null);
      return _scope.Peek().GetTValData(key);
    }

    public bool ContainTVal(NameSegment key){
      Contract.Requires<ArgumentNullException>(key != null, "key");
      return ContainTVal(key.Name);
    }

    public Dictionary<string, Expression> GetAllTVars() {
      return _scope.Peek().GetAllTVars(new Dictionary<string, Expression>());
    }

    /// <summary>
    /// Check if Tactic variable has been declared
    /// </summary>
    /// <param name="key"></param>
    /// <returns></returns>
    public bool ContainTVal(string key){
      Contract.Requires<ArgumentNullException>(!string.IsNullOrEmpty(key), "key");
      if (_scope == null || _scope.Count == 0) return false;
      return _scope.Peek().ContainTVars(key);
    }

    /// <summary>
    /// Get inline tactic
    /// </summary>
    /// <param name="key"></param>
    /// <returns></returns>
    public InlineTacticBlockStmt GetInlineTactic(string key) {
      Contract.Requires<ArgumentNullException>(key != null, "key");
      Contract.Ensures(Contract.Result<object>() != null);
      return _scope.Peek().GetInlineTactic(key);
    }

    public bool ContainInlineTactic(string key) {
      Contract.Requires<ArgumentNullException>(!string.IsNullOrEmpty(key), "key");
      if (_scope == null || _scope.Count == 0) return false;
      return _scope.Peek().ContainInlineTactic(key);
    }

    private ITactic GetTactic(string name){
      Contract.Requires<ArgumentNullException>(name != null);
      Contract.Requires<ArgumentNullException>(Tactics.ContainsKey(name), "Tactic does not exist in the current context");
      Contract.Ensures(Contract.Result<ITactic>() != null);

      return Tactics[name];
    }

    /// <summary>
    /// Get called tactic
    /// </summary>
    /// <param name="us"></param>
    /// <returns></returns>
    /// <exception cref="ArgumentNullException"> </exception>
    /// /// <exception cref="ArgumentException"> Provided UpdateStmt is not a tactic application</exception>
    public ITactic GetTactic(UpdateStmt us){
      Contract.Requires(us != null);
      Contract.Requires<ArgumentException>(IsTacticCall(us));
      Contract.Ensures(Contract.Result<ITactic>() != null);

      var name = Util.GetSignature(us);
      if(ContainTVal(name)) {
        var nameSegment = GetTVarValue(name) as NameSegment;
        if(nameSegment != null)
          name = nameSegment.Name;
      }

      return GetTactic(name);
    }

    /// <summary>
    /// Get called tactic
    /// </summary>
    /// <param name="aps"></param>
    /// <returns></returns>
    /// <exception cref="ArgumentNullException"> </exception>
    /// <exception cref="ArgumentException"> Provided ApplySuffix is not a tactic application</exception>
    [Pure]
    public ITactic GetTactic(ApplySuffix aps){
      Contract.Requires(aps != null);
      Contract.Requires(IsTacticCall(aps));
      Contract.Ensures(Contract.Result<ITactic>() != null);
      var name = Util.GetSignature(aps);
      if(ContainTVal(name)) {
        var nameSegment = GetTVarValue(name) as NameSegment;
        if(nameSegment != null)
          name = nameSegment.Name;
      }
      return GetTactic(name);
    }

    /// <summary>
    ///   Check if an UpdateStmt is a tactic call
    /// </summary>
    /// <param name="us"></param>
    /// <returns></returns>
    [Pure]
    public bool IsTacticCall(UpdateStmt us){
      Contract.Requires(us != null);
      var name = Util.GetSignature(us);
      if (ContainTVal(name)){
        var nameSegment = GetTVarValue(name) as NameSegment;
        if (nameSegment != null) name = nameSegment.Name;
      }
      return IsTacticCall(name);
    }

    /// <summary>
    ///   Check if an ApplySuffix is a tactic call
    /// </summary>
    /// <param name="aps"></param>
    /// <returns></returns>
    [Pure]
    public bool IsTacticCall(ApplySuffix aps){
      Contract.Requires(aps != null);
      return IsTacticCall(Util.GetSignature(aps));
    }

    private bool IsTacticCall(string name){
      Contract.Requires(Tcce.NonNull(name));
      if (name == null) return false;
      return Tactics.ContainsKey(name);
    }

    public bool IsInlineTacticCall(UpdateStmt us) {
      Contract.Requires(us != null);
      var name = Util.GetSignature(us);
      if (ContainTVal(name)) {
        var nameSegment = GetTVarValue(name) as NameSegment;
        if (nameSegment != null) name = nameSegment.Name;
      }
      if (name == null) return false;
      return ContainInlineTactic(name);
    }

    public bool IsInlineTacticCall(ApplySuffix aps)
    {
      Contract.Requires(aps != null);
      var name = Util.GetSignature(aps);
      if (name == null) return false;
      return ContainInlineTactic(name);
    }



    /// <summary>
    /// Check in an updateStmt is local assignment
    /// </summary>
    /// <param name="us"></param>
    /// <returns></returns>
    [Pure]
    public bool IsLocalAssignment(UpdateStmt us){
      if (us.Lhss.Count == 0)
        return false;
      foreach (var lhs in us.Lhss){
        if (!(lhs is NameSegment))
          return false;
        if (!_scope.Peek().ContainTVars((lhs as NameSegment).Name))
          return false;
      }

      return true;
    }

    public bool IsArgumentApplication(UpdateStmt us){
      Contract.Requires<ArgumentNullException>(us != null, "us");
      var ns = Util.GetNameSegment(us);
      return _scope.Peek().ContainTVars(ns.Name);
    }

    /// <summary>
    /// Add a varialbe to the top level frame
    /// </summary>
    /// <param name="key"></param>
    /// <param name="value"></param>
    public void AddTacnyVar(IVariable key, Expression value){
      Contract.Requires<ArgumentNullException>(key != null, "key");
      if (ContainTVal(key.Name))
        throw new Exception("tactic variable " + key.Name + " has already been defined !");
      AddTacnyVar(key.Name, value);
    }

    /// <summary>
    /// Add a varialbe to the top level frame
    /// </summary>
    /// <param name="key"></param>
    /// <param name="value"></param>
    public void AddTacnyVar(string key, Expression value){
      Contract.Requires<ArgumentNullException>(key != null, "key");
      if(ContainTVal(key))
        throw new Exception("tactic variable " + key + " has already been defined !");
      _scope.Peek().AddTVar(key, value);
    }


    /// <summary>
    /// Add an inline tactic to the top level frame
    /// </summary>
    /// <param name="key"></param>
    /// <param name="value"></param>
    public void AddInlineTactic(string key, InlineTacticBlockStmt stmt) {
      Contract.Requires<ArgumentNullException>(key != null, "key");
      if (ContainTVal(key))
        throw new Exception("tactic variable " + key + " has already been defined !");
      _scope.Peek().AddInlineTactic(key, stmt);
    }


    /// <summary>
    /// Update a local variable
    /// </summary>
    /// <param name="key"></param>
    /// <param name="value"></param>
    public void UpdateTacticVar(IVariable key, Expression value){
      Contract.Requires<ArgumentNullException>(key != null, "key");
      UpdateTacticVar(key.Name, value);
    }

    /// <summary>
    /// Update a local variable
    /// </summary>
    /// <param name="key"></param>
    /// <param name="value"></param>
    public void UpdateTacticVar(string key, Expression value){
      Contract.Requires<ArgumentNullException>(key != null, "key");
      _scope.Peek().UpdateLocalTVar(key, value);
    }

    /// <summary>
    /// add a dafny variable to the top frame
    /// </summary>
    /// <param name="name"></param>
    /// <param name="var"></param>
    public void AddDafnyVar(string name, VariableData var){
      _scope.Peek().AddDafnyVar(name, var);
    }

    /// <summary>
    /// Add new dafny stmt to the top frame
    /// </summary>
    /// <param name="stmt"></param>
    public void AddStatement(Statement stmt){
      Contract.Requires<ArgumentNullException>(stmt != null, "stmt");
      _scope.Peek().FrameCtrl.AddGeneratedCode(stmt);
    }

    /// <summary>
    /// Add new dafny stmt to the top frame
    /// </summary>
    /// <param name="stmtList"></param>
    public void AddStatements(List<Statement> stmtList){
      Contract.Requires<ArgumentNullException>(Tcce.NonNullElements(stmtList));
      _scope.Peek().FrameCtrl.AddGeneratedCode(stmtList);
    }

    /// <summary>
    /// Return the latest unevalauted statement from the top frame
    /// </summary>
    /// <returns></returns>

    public class TopLevelClassDeclaration{
      public readonly Dictionary<string, MemberDecl> Members;
      public readonly string Name;
      public readonly Dictionary<string, ITactic> Tactics;

      public TopLevelClassDeclaration(string name){
        Contract.Requires(name != null);
        Tactics = new Dictionary<string, ITactic>();
        Members = new Dictionary<string, MemberDecl>();
        Name = name;
      }
    }

    internal class Frame{
      public readonly Frame Parent;
      private readonly Dictionary<string, Expression> _declaredVariables; // tactic variables
      private readonly Dictionary<string, VariableData> _dafnyVariables; // dafny variables
      private readonly Dictionary<string, InlineTacticBlockStmt> _inlineTactics;
      public TacticFrameCtrl FrameCtrl;

      /// <summary>
      /// Initialize the top level frame
      /// </summary>
      public Frame( List<Statement> body, bool ifPartial,  Attributes attr, Attributes tacticDefAttrs){
        Parent = null;
        FrameCtrl = new DefaultTacticFrameCtrl();
        FrameCtrl.InitBasicFrameCtrl(body, ifPartial, attr, 1, null, tacticDefAttrs);

        _declaredVariables = new Dictionary<string, Expression>();
        _dafnyVariables = new Dictionary<string, VariableData>();
        _inlineTactics = new Dictionary<string, InlineTacticBlockStmt>();

      }

      public Frame(Frame parent, TacticFrameCtrl ctrl){
        Contract.Requires<ArgumentNullException>(parent != null);
        // carry over the tactic info
        _declaredVariables = new Dictionary<string, Expression>();
        _dafnyVariables = new Dictionary<string, VariableData>();
        _inlineTactics = new Dictionary<string, InlineTacticBlockStmt>();
        Parent = parent;
        FrameCtrl = ctrl;
      }

      // dafny variables
      internal VariableData GetLocalDafnyVar(string name){
        //Contract.Requires(_DafnyVariables.ContainsKey(name));
        return _dafnyVariables[name];
      }

      internal void AddDafnyVar(string name, VariableData var){
        Contract.Requires<ArgumentNullException>(name != null, "key");
        if (_dafnyVariables.All(v => v.Key != name)){
          _dafnyVariables.Add(name, var);
        }
        else{
          throw new ArgumentException($"dafny var {name} is already declared in the scope");
        }
      }

      internal bool ContainDafnyVar(string name){
        Contract.Requires<ArgumentNullException>(name != null, "name");
        // base case
        if (Parent == null)
          return _dafnyVariables.Any(kvp => kvp.Key == name);
        return _dafnyVariables.Any(kvp => kvp.Key == name) || Parent.ContainDafnyVar(name);
      }


      internal VariableData GetDafnyVariableData(string name){
//     Contract.Requires(ContainDafnyVars(name));
        if (_dafnyVariables.ContainsKey(name))
          return _dafnyVariables[name];
        else{
          return Parent.GetDafnyVariableData(name);
        }
      }

      internal Dictionary<string, VariableData> GetAllDafnyVars(Dictionary<string, VariableData> toDict){
        _dafnyVariables.Where(x => !toDict.ContainsKey(x.Key)).ToList().ForEach(x => toDict.Add(x.Key, x.Value));
        if (Parent == null)
          return toDict;
        else{
          return Parent.GetAllDafnyVars(toDict);
        }
      }

      //tactic variables
      [Pure]
      internal bool ContainTVars(string name){
        Contract.Requires<ArgumentNullException>(name != null, "name");
        // base case
        if (Parent == null)
          return _declaredVariables.Any(kvp => kvp.Key == name);
        return _declaredVariables.Any(kvp => kvp.Key == name) || Parent.ContainTVars(name);
      }

      internal void AddTVar(string variable, Expression value){
        Contract.Requires<ArgumentNullException>(variable != null, "key");
        if (_declaredVariables.All(v => v.Key != variable)){
          _declaredVariables.Add(variable, value);
        }
        else{
          throw new ArgumentException($"tacny var {variable} is already declared in the scope");
        }
      }

      internal void UpdateLocalTVar(IVariable key, Expression value){
        Contract.Requires<ArgumentNullException>(key != null, "key");
        Contract.Requires<ArgumentException>(ContainTVars(key.Name));
        //, $"{key} is not declared in the current scope".ToString());
        UpdateLocalTVar(key.Name, value);
      }

      internal void UpdateLocalTVar(string key, Expression value){
        Contract.Requires<ArgumentNullException>(key != null, "key");
        //Contract.Requires<ArgumentException>(_declaredVariables.ContainsKey(key));
        if (_declaredVariables.ContainsKey(key))
          _declaredVariables[key] = value;
        else{
          Parent.UpdateLocalTVar(key, value);
        }
      }

      internal Expression GetTValData(string name){
        Contract.Requires<ArgumentNullException>(name != null, "key");
        if (_declaredVariables.ContainsKey(name))
          return _declaredVariables[name];
        else{
          return Parent.GetTValData(name);
        }
      }
      internal Dictionary<string, Expression> GetAllTVars(Dictionary<string, Expression> toDict) {
        _declaredVariables.Where(x => !toDict.ContainsKey(x.Key)).ToList().ForEach(x => toDict.Add(x.Key, x.Value));
        if (Parent == null)
          return toDict;
        else {
          return Parent.GetAllTVars(toDict);
        }
      }

      //inline tactics
      internal InlineTacticBlockStmt GetLocalInlineTactic(string name) {
        return _inlineTactics[name];
      }

      internal void AddInlineTactic(string name, InlineTacticBlockStmt stmt) {
        Contract.Requires<ArgumentNullException>(name != null, "key");
        if (_inlineTactics.All(v => v.Key != name)) {
          _inlineTactics.Add(name, stmt);
        } else {
          throw new ArgumentException($"inline tactic {name} is already declared in the scope");
        }
      }

      internal bool ContainInlineTactic(string name) {
        Contract.Requires<ArgumentNullException>(name != null, "name");
        // base case
        if (Parent == null)
          return _inlineTactics.Any(kvp => kvp.Key == name);
        return _inlineTactics.Any(kvp => kvp.Key == name) || Parent.ContainInlineTactic(name);
      }


      internal InlineTacticBlockStmt GetInlineTactic(string name) {
        //     Contract.Requires(ContainDafnyVars(name));
        if (_inlineTactics.ContainsKey(name))
          return _inlineTactics[name];
        else {
          return Parent.GetInlineTactic(name);
        }
      }

      internal List<Statement> GetGeneratedCode(){
        var code = GetGeneratedCode0();
        return code;
      }

      internal List<Statement> GetGeneratedCode0(List<Statement> stmts = null){
        Contract.Ensures(Contract.Result<List<Statement>>() != null);
        //try to get the generated code from the current framectrl
        List<Statement> code = FrameCtrl.GetFinalCode();
        if (code != null){
          // there exists the generated code in the current framectrl. It means
          // the frame is terminated, so continue the process. The following action to assemble 
          // the code depents on whether the current frame is the root. If root, just return code, otherwise, forward 
          // the generated code the parent frame to coniue assemble the code.
        }
        else if (stmts != null){
          // this is the case when the child frame has assmeble the code with both the child and parent's raw code
          // and then forwards its the generated code through stmt. see the else branch for (Parent == null)
          code = stmts;
        }
        else{
          // no generated code: it is the case when the current frame is not terminated, so
          // just use the raw code as the generated code 
          code = FrameCtrl.AssembleStmts(FrameCtrl.GetRawCode());
        }

        if (Parent == null)
          return code.Copy();
        else{
          // parent is not terminated, so assmeble the parent's code together with the child code, 
          // and then foward the generated code to the parent
          var parRawCode = Parent.FrameCtrl.GetRawCode().Copy();
          parRawCode.Add(code);
          var parCode = Parent.FrameCtrl.AssembleStmts(parRawCode);
          return Parent.GetGeneratedCode0(parCode);
        }
      }
    }


    public class VariableData{
      private Dfy.Type _type;

      private IVariable _variable;

      public IVariable Variable{
        get { return _variable; }
        set{
          Contract.Assume(_variable == null); // key value should be only set once
          Contract.Assert(Tcce.NonNull(value));
          _variable = value;
        }
      }

      public Dfy.Type Type{
        get { return _type; }
        set{
          Contract.Assume(_type == null);
          _type = value;
        }
      }
    }
  }
}