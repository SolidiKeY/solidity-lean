import Solidity.Yul.OpenComposition
/-! Additive machine execution with retained word-evaluator compatibility.
The compatibility entries keep their existing pure profiles. Runtime execution
is not gas accounting or a theorem of external EVM agreement. -/
namespace Solidity.Yul.StatefulRun
open Closed
/-- Byte-addressed memory and word-addressed storage. Calldata is immutable input;
return data and revert status describe the current execution, not a call oracle. -/
structure Machine where
  storage : Word → Word
  memory : Nat → UInt8
  calldata : ByteArray
  returnData : ByteArray
  reverted : Bool
  callValue : Word := word 0
/-- A fresh invocation with empty storage, memory and output. -/
def Machine.empty (calldata : ByteArray := ByteArray.empty) : Machine :=
  ⟨fun _ => word 0, fun _ => 0, calldata, ByteArray.empty, false, word 0⟩
structure Result (α : Type) where
  value : α
  machine : Machine
/-- Fuel and erased word-profile evidence are passed unchanged to ClosedRun.
`none` means fuel exhaustion, never a revert or an unsupported operation. -/
def runClosed (fuel : Nat) {F c n} (environment : FunctionEnv F)
    (he : EnvWordP environment) (code : Stmt F [] c n) (hc : StmtWordP code)
    (vars : Values n) (machine : Machine) : Option (Result (Outcome c n)) :=
  (evalStmt fuel environment he code hc vars).map (fun value => ⟨value, machine⟩)
/-- Open Solidity cells keep OpenRun's original tier-A policy and lexical
function environment. The EVM machine is separate from those external cells. -/
def runOpen (fuel : Nat) {F X c n} (environment : OpenFunctions.PureEnvironment F)
    (code : Stmt F X c n) (policy : Policy.StmtP .A code)
    (state : WordState X n) (machine : Machine) :
    Option (Result (WordAdapter.Outcome X c n)) :=
  (OpenRun.statement fuel environment code policy state).map (fun value => ⟨value, machine⟩)
/-- Exact agreement includes exhaustion and the complete control-flow result. -/
theorem runClosed_agrees (fuel : Nat) {F c n} (environment : FunctionEnv F)
    (he : EnvWordP environment) (code : Stmt F [] c n) (hc : StmtWordP code)
    (vars : Values n) (machine : Machine) :
    (runClosed fuel environment he code hc vars machine).map Result.value =
      evalStmt fuel environment he code hc vars := by
  unfold runClosed
  cases evalStmt fuel environment he code hc vars <;> rfl
/-- Pure execution preserves all machine components, on every completed run. -/
theorem runClosed_machine (fuel : Nat) {F c n} (environment : FunctionEnv F)
    (he : EnvWordP environment) (code : Stmt F [] c n) (hc : StmtWordP code)
    (vars : Values n) (machine : Machine) (result : Result (Outcome c n))
    (done : runClosed fuel environment he code hc vars machine = some result) :
    result.machine = machine := by
  unfold runClosed at done
  cases h : evalStmt fuel environment he code hc vars with
  | none => simp only [h, Option.map_none] at done; cases done
  | some value =>
    simp only [h, Option.map_some, Option.some.injEq] at done
    cases done
    rfl
/-- Reuse the established OpenRun correspondence, including its coordinate map;
no new simulation assumption is introduced. -/
theorem runOpen_agrees (fuel : Nat) {F X c n m} (coordinates : Coordinates X n m)
    (environment : OpenFunctions.PureEnvironment F) (code : Stmt F X c n)
    (policy : Policy.StmtP .A code) (state : WordState X n) (machine : Machine) :
    (runOpen fuel environment code policy state machine).map
        (fun result => Coordinates.encodeOutcome coordinates result.value) =
      evalStmt fuel (OpenFunctions.lower environment) (OpenFunctions.lower_words environment)
        (WordAdapter.statement code policy coordinates.locals coordinates.cells).code
        (WordAdapter.statement code policy coordinates.locals coordinates.cells).words
        (coordinates.pack state) := by
  simp only [runOpen, Option.map_map, Function.comp_def]
  exact OpenRun.statement_agrees fuel coordinates environment code policy state
/-- Failures are distinct from both ordinary completion and EVM termination.
The output bound is a host resource limit, not an EVM gas model. -/
inductive Signal where
  | exhausted
  | unsupported (name : String)
  | outputLimit
  | returndataBounds
  | invalid
  | halted (machine : Machine)
abbrev Exec (α : Type) := StateT Machine (Except Signal) α
def readWord (bytes : Nat → UInt8) (offset : Nat) : Word :=
  word ((List.range 32).foldl (fun acc i => acc * 256 + (bytes (offset + i)).toNat) 0)
def slice (bytes : Nat → UInt8) (offset size : Nat) : ByteArray :=
  ⟨((List.range size).map (fun i => bytes (offset + i))).toArray⟩
def byteAt (bytes : ByteArray) (i : Nat) : UInt8 := bytes.data[i]?.getD 0
/-- Copy from the pre-operation source, so overlapping mcopy is correct. -/
def copyBytes (memory source : Nat → UInt8) (dst src size : Nat) : Nat → UInt8 :=
  fun i => if dst ≤ i ∧ i < dst + size then source (src + (i - dst)) else memory i
def builtin (outputLimit : Nat) {a r} (op : Builtin a r) (args : Values a) : Exec (Values r) := by
  revert args
  apply Builtin.casesOn (motive := fun a r _ => Values a → Exec (Values r)) op
  case pure => intro a op args; exact pure (fun _ => op.eval args)
  case pop => intro _; exact pure Fin.elim0
  case stop => intro _; exact do throw (.halted (← get))
  case invalid => intro _; exact throw .invalid
  case callvalue => intro _; exact do let s ← get; pure (fun _ => s.callValue)
  case sload => intro args; exact do let s ← get; pure (fun _ => s.storage (args 0))
  case sstore => intro args; exact do
    modify fun s => { s with storage := fun key => if key = args 0 then args 1 else s.storage key }
    pure Fin.elim0
  case mload => intro args; exact do let s ← get; pure (fun _ => readWord s.memory (args 0).val)
  case mstore => intro args; exact do
    modify fun s => { s with memory := copyBytes s.memory (fun i => UInt8.ofNat ((args 1).val / 256 ^ (31 - i) % 256)) (args 0).val 0 32 }
    pure Fin.elim0
  case mstore8 => intro args; exact do
    modify fun s => { s with memory := fun i => if i = (args 0).val then UInt8.ofNat (args 1).val else s.memory i }
    pure Fin.elim0
  case calldatasize => intro _; exact do let s ← get; pure (fun _ => word s.calldata.size)
  case calldataload => intro args; exact do let s ← get; pure (fun _ => readWord (byteAt s.calldata) (args 0).val)
  case returndatasize => intro _; exact do let s ← get; pure (fun _ => word s.returnData.size)
  case calldatacopy => intro args; exact do
    modify fun s => { s with memory := copyBytes s.memory (byteAt s.calldata) (args 0).val (args 1).val (args 2).val }
    pure Fin.elim0
  case returndatacopy => intro args; exact do
    let s ← get
    if (args 1).val + (args 2).val > s.returnData.size then throw .returndataBounds
    set { s with memory := copyBytes s.memory (byteAt s.returnData) (args 0).val (args 1).val (args 2).val }
    pure Fin.elim0
  case mcopy => intro args; exact do
    modify fun s => { s with memory := copyBytes s.memory s.memory (args 0).val (args 1).val (args 2).val }
    pure Fin.elim0
  case «return» => intro args; exact do
    if (args 1).val > outputLimit then throw .outputLimit
    let s ← get
    throw (.halted { s with returnData := slice s.memory (args 0).val (args 1).val, reverted := false })
  case revert => intro args; exact do
    if (args 1).val > outputLimit then throw .outputLimit
    let s ← get
    throw (.halted { s with returnData := slice s.memory (args 0).val (args 1).val, reverted := true })
  all_goals intros; exact throw (.unsupported op.name)
/-- Right-to-left operand evaluation, matching Yul and collectValues. -/
def collect : (a : Nat) → (Fin a → Exec Word) → Exec (Values a)
  | 0, _ => pure Fin.elim0
  | a + 1, getValue => do
    let last ← getValue (Fin.last a)
    let rest ← collect a (fun i => getValue i.castSucc)
    pure (Fin.lastCases last rest)
def StmtResult (F : List Sig) (X : List ExternalType) (c : Control) (n : Nat) : Type :=
  match X with
  | [] => FunctionEnv F → Values n → Exec (Outcome c n)
  | _ :: _ => Unit
def CasesResult (F : List Sig) (X : List ExternalType) (c : Control) (n : Nat) : Type :=
  match X with
  | [] => FunctionEnv F → Word → Values n → Exec (Option (Outcome c n))
  | _ :: _ => Unit
@[noinline] def applyStmt {F c n} (f : FunctionEnv F → Values n → Exec (Outcome c n))
    (env : FunctionEnv F) (vars : Values n) : Exec (Outcome c n) := f env vars
@[noinline] def applyCases {F c n} (f : FunctionEnv F → Word → Values n → Exec (Option (Outcome c n)))
    (env : FunctionEnv F) (value : Word) (vars : Values n) : Exec (Option (Outcome c n)) := f env value vars
mutual
def expression (limit fuel : Nat) {F n r} (env : FunctionEnv F)
    (code : Expr F [] n r) (vars : Values n) : Exec (Values r) :=
  match fuel with
  | 0 => throw .exhausted
  | k + 1 => by
    apply Expr.casesOn (motive := fun r _ => Exec (Values r)) code
    case literal => intro w; exact pure (fun _ => w)
    case «local» => intro i; exact pure (fun _ => vars i)
    case external => intro ref; exact False.elim (by cases ref.index)
    case builtin => intro a r op args; exact do
      let inputs ← collect a (fun i => do pure ((← expression limit k env (args i) vars) 0))
      builtin limit op inputs
    case call => intro sig f args; exact do
      let inputs ← collect sig.args (fun i => do pure ((← expression limit k env (args i) vars) 0))
      let closure := lookup env f
      let result ← applyStmt (statementNode limit k closure.body) closure.environment
        (extendValues inputs (fun _ : Fin sig.rets => word 0))
      pure (dropValues sig.args result.vars)
termination_by structural fuel
def statementNode (limit fuel : Nat) {F X c n} (code : Stmt F X c n) : StmtResult F X c n :=
  match fuel with
  | 0 => by cases X with
    | nil => exact fun _ _ => throw .exhausted
    | cons _ _ => exact ()
  | k + 1 => by
    apply Stmt.casesOn (motive_1 := fun F X c n _ => StmtResult F X c n) code
    case skip => intro F X c n; cases X with
      | nil => exact fun _ vars => pure ⟨vars, .normal⟩
      | cons _ _ => exact ()
    case seq => intro F X c n first second; cases X with
      | nil => exact fun env vars => do
        let result ← applyStmt (statementNode limit k first) env vars
        match result.flow with
        | .normal => applyStmt (statementNode limit k second) env result.vars
        | _ => pure result
      | cons _ _ => exact ()
    case assign => intro F X c n r targets rhs; cases X with
      | nil => exact fun env vars => do
        let values ← expression limit k env rhs vars
        pure ⟨writeValues r targets values vars, .normal⟩
      | cons _ _ => exact ()
    case discard => intro F X c n rhs; cases X with
      | nil => exact fun env vars => do
        let _ ← expression limit k env rhs vars
        pure ⟨vars, .normal⟩
      | cons _ _ => exact ()
    case let_ => intro F X c n r rhs body; cases X with
      | nil => exact fun env vars => do
        let values ← expression limit k env rhs vars
        let result ← applyStmt (statementNode limit k body) env (extendValues values vars)
        pure ⟨dropValues r result.vars, result.flow⟩
      | cons _ _ => exact ()
    case zero => intro F X c n r body; cases X with
      | nil => exact fun env vars => do
        let result ← applyStmt (statementNode limit k body) env (extendValues (fun _ : Fin r => word 0) vars)
        pure ⟨dropValues r result.vars, result.flow⟩
      | cons _ _ => exact ()
    case if_ => intro F X c n cond body; cases X with
      | nil => exact fun env vars => do
        let value ← expression limit k env cond vars
        if (value 0).val = 0 then pure ⟨vars, .normal⟩ else applyStmt (statementNode limit k body) env vars
      | cons _ _ => exact ()
    case switch => intro F X c n cond arms fallback; cases X with
      | nil => exact fun env vars => do
        let value ← expression limit k env cond vars
        match ← applyCases (casesNode limit k arms) env (value 0) vars with
        | some result => pure result
        | none => applyStmt (statementNode limit k fallback) env vars
      | cons _ _ => exact ()
    case for_ => intro F X c n pre cond post body; cases X with
      | nil => exact fun env vars => do
        let result ← applyStmt (statementNode limit k pre) env vars
        match result.flow with
        | .normal => loop limit k env cond post body result.vars
        | .leave_ h => pure ⟨result.vars, .leave_ h⟩
        | .break_ h | .continue_ h => False.elim (by cases h)
      | cons _ _ => exact ()
    case leave => intro F X loop n; cases X with
      | nil => exact fun _ vars => pure ⟨vars, .leave_ rfl⟩
      | cons _ _ => exact ()
    case break_ => intro F X function n; cases X with
      | nil => exact fun _ vars => pure ⟨vars, .break_ rfl⟩
      | cons _ _ => exact ()
    case continue_ => intro F X function n; cases X with
      | nil => exact fun _ vars => pure ⟨vars, .continue_ rfl⟩
      | cons _ _ => exact ()
    case functions => intro F X c n sigs bodies rest; cases X with
      | nil => exact fun env vars => applyStmt (statementNode limit k rest) (.group sigs env bodies) vars
      | cons _ _ => exact ()
termination_by structural fuel
def casesNode (limit fuel : Nat) {F X c n} (code : Cases F X c n) : CasesResult F X c n :=
  match fuel with
  | 0 => by cases X with
    | nil => exact fun _ _ _ => throw .exhausted
    | cons _ _ => exact ()
  | k + 1 => by
    apply Cases.casesOn (motive_2 := fun F X c n _ => CasesResult F X c n) code
    case nil => intro F X c n; cases X with
      | nil => exact fun _ _ _ => pure none
      | cons _ _ => exact ()
    case cons => intro F X c n value body rest; cases X with
      | nil => exact fun env selector vars =>
        if selector = value then some <$> applyStmt (statementNode limit k body) env vars
        else applyCases (casesNode limit k rest) env selector vars
      | cons _ _ => exact ()
termination_by structural fuel
def loop (limit fuel : Nat) {F c n} (env : FunctionEnv F) (cond : Expr F [] n 1)
    (post : Stmt F [] ⟨c.function, false⟩ n) (body : Stmt F [] ⟨c.function, true⟩ n)
    (vars : Values n) : Exec (Outcome c n) :=
  match fuel with
  | 0 => throw .exhausted
  | k + 1 => do
    let value ← expression limit k env cond vars
    if (value 0).val = 0 then pure ⟨vars, .normal⟩ else
      let afterBody := fun vars => do
        let result ← applyStmt (statementNode limit k post) env vars
        match result.flow with
        | .normal => loop limit k env cond post body result.vars
        | .leave_ h => pure ⟨result.vars, .leave_ h⟩
        | .break_ h | .continue_ h => False.elim (by cases h)
      let result ← applyStmt (statementNode limit k body) env vars
      match result.flow with
      | .normal | .continue_ _ => afterBody result.vars
      | .break_ _ => pure ⟨result.vars, .normal⟩
      | .leave_ h => pure ⟨result.vars, .leave_ h⟩
termination_by structural fuel
end
/-- One invocation clears prior output/revert status. The supplied storage,
memory and calldata are the initial state. Revert rolls storage back; memory
is retained for observation. Failures expose no committed state. Pure roots
use ClosedRun verbatim; effects use the additive intrinsic evaluator above. Unsupported operations
are rejected when reached; whole-code admission is StatefulImport.parse. -/
def run (outputLimit fuel : Nat) (code : Stmt [] [] ⟨false, false⟩ 0)
    (initial : Machine) : Except Signal Machine :=
  let start := { initial with returnData := ByteArray.empty, reverted := false }
  match h : Policy.checkStmt .A code with
  | .ok () =>
    match runClosed fuel .nil True.intro code
        (stmt_policy_words code (fun _ i => by cases i) ((Policy.stmt_iff .A code).mp h))
        Fin.elim0 start with
    | none => .error .exhausted
    | some result => .ok result.machine
  | .error _ =>
    match applyStmt (statementNode outputLimit fuel code) .nil Fin.elim0 start with
    | .ok (_, machine) => .ok machine
    | .error (.halted machine) =>
      .ok (if machine.reverted then { machine with storage := initial.storage } else machine)
    | .error failure => .error failure
theorem run_pure (limit fuel : Nat) (code : Stmt [] [] ⟨false, false⟩ 0)
    (policy : Policy.StmtP .A code) (initial : Machine) :
    run limit fuel code initial =
      match evalStmt fuel .nil True.intro code
          (stmt_policy_words code (fun _ i => by cases i) policy) Fin.elim0 with
      | none => .error .exhausted
      | some _ => .ok { initial with returnData := ByteArray.empty, reverted := false } := by
  unfold run
  dsimp only
  split
  · unfold runClosed
    cases evalStmt fuel FunctionEnv.nil True.intro code
      (stmt_policy_words code (fun _ i => by cases i) policy) Fin.elim0 <;> rfl
  · next reason h =>
    have bad := h.symm.trans ((Policy.stmt_iff .A code).mpr policy)
    cases bad
end Solidity.Yul.StatefulRun
