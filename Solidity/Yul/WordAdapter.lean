import Solidity.Yul.WordInputs
import Solidity.Yul.WordPolicy
import Solidity.Yul.WordLogic

/-! Actual pure-word execution for intrinsic Yul with raw Solidity value cells.
A structural adapter replaces cells with real packed Fin locals and constants
with their actual words; all original control/function/arity constructors are
retained. The existing interpreter executes the resulting intrinsic AST.
This is not the clean Source S02/S03 embedding, JSON admission, compiler or
physical-state correspondence. -/
namespace Solidity.Yul.WordAdapter
open Solidity.Yul.Closed


def tabulate {α : Type} : (a : Nat) → (Fin a → α) → Fin a → α
  | 0, _ => Fin.elim0
  | a+1, get => Fin.cases (get 0) (tabulate a (fun i => get i.succ))

theorem tabulate_get {α : Type} (a : Nat) (get : Fin a → α) (i : Fin a) :
    tabulate a get i = get i := by
  induction a with
  | zero => exact Fin.elim0 i
  | succ a ih =>
    exact Fin.cases rfl (fun j => ih (fun k => get k.succ) j) i

theorem tabulate_eq {α : Type} (a : Nat) (get : Fin a → α) :
    tabulate a get = get := funext (tabulate_get a get)

theorem builtin_tabulate {F X n a r} (builtin : Builtin a r)
    (args : Fin a → Expr F X n 1) :
    Expr.builtin builtin (tabulate a args) = Expr.builtin builtin args :=
  congrArg (fun operands : Fin a → Expr F X n 1 => Expr.builtin builtin operands)
    (tabulate_eq a args)

theorem call_tabulate {F X n sig} (function : Member F sig)
    (args : Fin sig.args → Expr F X n 1) :
    Expr.call function (tabulate sig.args args) = Expr.call function args :=
  congrArg (fun operands : Fin sig.args → Expr F X n 1 => Expr.call function operands)
    (tabulate_eq sig.args args)

theorem assignment_tabulate {F X c n r} (targets : Fin r → Target X n)
    (rhs : Expr F X n r) :
    Stmt.assign (tabulate r targets) rhs = (Stmt.assign targets rhs : Stmt F X c n) :=
  congrArg (fun writes : Fin r → Target X n => (Stmt.assign writes rhs : Stmt F X c n))
    (tabulate_eq r targets)

theorem operand_words {F X n} (operand : WordRead X) (cells : WordCell X → Fin n) :
    ExprWordP (operand.expression (F := F) cells) := by
  cases operand <;> exact True.intro

def expression {F X n r} (code : Expr F X n r) :
    Policy.ExprP .A code → {m : Nat} → (Fin n → Fin m) →
      (WordCell X → Fin m) → Logic.Term F m r := by
  apply Expr.casesOn (motive := fun r code =>
    Policy.ExprP .A code → {m : Nat} → (Fin n → Fin m) →
      (WordCell X → Fin m) → Logic.Term F m r) code
  case literal =>
    intro value
    exact fun _ {_} _ _ => ⟨.literal value,True.intro⟩
  case «local» =>
    intro position
    exact fun _ {_} locals _ => ⟨.local (locals position),True.intro⟩
  case external =>
    intro ref
    exact fun policy {_} _ cells =>
      ⟨(ref.wordRead policy).expression cells,operand_words _ cells⟩
  case builtin =>
    intro a r builtin args
    exact fun policy {_} locals cells =>
      let operands := fun i => expression (args i) (policy.2 i) locals cells
      ⟨.builtin builtin (tabulate a (fun i => (operands i).code)),
       ⟨(checkWordBuiltin_iff builtin).mpr
          ((Policy.builtin_iff .A builtin).mpr policy.1),fun i => by rw [tabulate_get]; exact (operands i).words⟩⟩
  case call =>
    intro sig function args
    exact fun policy {_} locals cells =>
      let operands := fun i => expression (args i) (policy i) locals cells
      ⟨.call function (tabulate sig.args (fun i => (operands i).code)),
       fun i => by rw [tabulate_get]; exact (operands i).words⟩
termination_by structural code

def target {X n m} (code : Target X n) (policy : Policy.TargetP .A code)
    (locals : Fin n → Fin m) (cells : WordCell X → Fin m) : Target [] m :=
  match code with
  | .local position => .local (locals position)
  | .external ref => .local (cells (ref.wordWrite policy))

theorem target_words {X n m} (code : Target X n) (policy : Policy.TargetP .A code)
    (locals : Fin n → Fin m) (cells : WordCell X → Fin m) :
    TargetWordP (target code policy locals cells) := by
  cases code <;> exact True.intro

def bindLocals {n m} (r : Nat) (locals : Fin n → Fin m) : Fin (r+n) → Fin (r+m) :=
  Fin.addCases (motive := fun _ => Fin (r+m)) (Fin.castAdd m)
    (fun index => Fin.natAdd r (locals index))

structure Arms (F : List Sig) (control : Control) (n : Nat) where
  code : Cases F [] control n
  words : CasesWordP code

structure Definitions (F : List Sig) (signatures : List Sig) where
  code : Bodies F [] signatures
  words : BodiesWordP code

mutual
def statement {F X c n} (code : Stmt F X c n) :
    Policy.StmtP .A code → {m : Nat} → (Fin n → Fin m) →
      (WordCell X → Fin m) → Logic.Program F c m := by
  apply Stmt.casesOn (motive_1 := fun F X c n code =>
    Policy.StmtP .A code → {m : Nat} → (Fin n → Fin m) →
      (WordCell X → Fin m) → Logic.Program F c m) code
  case skip =>
    intros
    exact ⟨.skip,True.intro⟩
  case seq =>
    intro F X c n first rest
    exact fun policy {_} locals cells =>
      let a := statement first policy.1 locals cells
      let b := statement rest policy.2 locals cells
      ⟨.seq a.code b.code,⟨a.words,b.words⟩⟩
  case assign =>
    intro F X c n r targets rhs
    exact fun policy {_} locals cells =>
      let value := expression rhs policy.2 locals cells
      ⟨.assign (tabulate r (fun i => target (targets i) (policy.1 i) locals cells)) value.code,
       ⟨fun i => by rw [tabulate_get]; exact target_words (targets i) (policy.1 i) locals cells,
        value.words⟩⟩
  case discard =>
    intro F X c n rhs
    exact fun policy {_} locals cells =>
      let value := expression rhs policy locals cells
      ⟨.discard value.code,value.words⟩
  case let_ =>
    intro F X c n r rhs body
    exact fun policy {m} locals cells =>
      let value := expression rhs policy.1 locals cells
      let rest := statement body policy.2 (bindLocals r locals)
        (fun cell => Fin.natAdd r (cells cell))
      ⟨.let_ r value.code rest.code,⟨value.words,rest.words⟩⟩
  case zero =>
    intro F X c n r body
    exact fun policy {m} locals cells =>
      let rest := statement body policy (bindLocals r locals)
        (fun cell => Fin.natAdd r (cells cell))
      ⟨.zero r rest.code,rest.words⟩
  case if_ =>
    intro F X c n condition body
    exact fun policy {_} locals cells =>
      let test := expression condition policy.1 locals cells
      let rest := statement body policy.2 locals cells
      ⟨.if_ test.code rest.code,⟨test.words,rest.words⟩⟩
  case switch =>
    intro F X c n selector arms fallback
    exact fun policy {_} locals cells =>
      let test := expression selector policy.1 locals cells
      let options := cases arms policy.2.1 locals cells
      let rest := statement fallback policy.2.2 locals cells
      ⟨.switch test.code options.code rest.code,⟨test.words,options.words,rest.words⟩⟩
  case for_ =>
    intro F X c n pre condition post body
    exact fun policy {_} locals cells =>
      let init := statement pre policy.1 locals cells
      let test := expression condition policy.2.1 locals cells
      let step := statement post policy.2.2.1 locals cells
      let work := statement body policy.2.2.2 locals cells
      ⟨.for_ init.code test.code step.code work.code,
       ⟨init.words,test.words,step.words,work.words⟩⟩
  case leave =>
    intros
    exact ⟨.leave,True.intro⟩
  case break_ =>
    intros
    exact ⟨.break_,True.intro⟩
  case continue_ =>
    intros
    exact ⟨.continue_,True.intro⟩
  case functions =>
    intro F X c n signatures bodies rest
    exact fun policy {_} locals cells =>
      let definitions := functions bodies policy.1 (fun cell => cell.not_globals)
      let work := statement rest policy.2 locals cells
      ⟨.functions signatures definitions.code work.code,⟨definitions.words,work.words⟩⟩
termination_by structural code

def cases {F X c n} (code : Cases F X c n) :
    Policy.CasesP .A code → {m : Nat} → (Fin n → Fin m) →
      (WordCell X → Fin m) → Arms F c m := by
  apply Cases.casesOn (motive_2 := fun F X c n code =>
    Policy.CasesP .A code → {m : Nat} → (Fin n → Fin m) →
      (WordCell X → Fin m) → Arms F c m) code
  case nil =>
    intros
    exact ⟨.nil,True.intro⟩
  case cons =>
    intro F X c n label body rest
    exact fun policy {_} locals cells =>
      let work := statement body policy.1 locals cells
      let remaining := cases rest policy.2 locals cells
      ⟨.cons label work.code remaining.code,⟨work.words,remaining.words⟩⟩
termination_by structural code

def functions {F X signatures} (code : Bodies F X signatures) :
    Policy.BodiesP .A code → (WordCell X → False) → Definitions F signatures := by
  apply Bodies.casesOn (motive_3 := fun F X signatures code =>
    Policy.BodiesP .A code → (WordCell X → False) → Definitions F signatures) code
  case nil =>
    intros
    exact ⟨.nil,True.intro⟩
  case cons =>
    intro F X sig signatures body rest
    exact fun policy empty =>
      let work := statement body policy.1 (fun index => index)
        (fun cell => False.elim (empty cell))
      let remaining := functions rest policy.2 empty
      ⟨.cons work.code remaining.code,⟨work.words,remaining.words⟩⟩
termination_by structural code
end

def program {X c n} (code : Stmt [] X c n) (policy : Policy.StmtP .A code) :
    Logic.Program [] c (n + wordCellCount X) :=
  statement code policy (Fin.castAdd (wordCellCount X))
    (fun cell => Fin.natAdd n cell.slot)

def model : Logic.Model [] := ⟨.nil,True.intro⟩

structure Outcome (X : List ExternalType) (control : Control) (n : Nat) where
  state : WordState X n
  flow : Flow control

def run {X c n} (code : Stmt [] X c n) (policy : Policy.StmtP .A code)
    (fuel : Nat) (state : WordState X n) : Option (Outcome X c n) :=
  let prepared := program code policy
  (evalStmt fuel model.environment model.words prepared.code prepared.words state.pack).map
    (fun result => ⟨WordState.unpack result.vars,result.flow⟩)

def Outcome.encode {X c n} (result : Outcome X c n) :
    Closed.Outcome c (n + wordCellCount X) := ⟨result.state.pack,result.flow⟩

def Outcome.decode {X c n} (result : Closed.Outcome c (n + wordCellCount X)) :
    Outcome X c n := ⟨WordState.unpack result.vars,result.flow⟩

theorem Outcome.encode_decode {X c n}
    (result : Closed.Outcome c (n + wordCellCount X)) : (Outcome.decode result).encode = result := by
  cases result with
  | mk vars flow =>
    change Closed.Outcome.mk (WordState.unpack vars).pack flow = Closed.Outcome.mk vars flow
    rw [WordState.pack_unpack]

theorem Outcome.decode_encode {X c n} (result : Outcome X c n) :
    Outcome.decode result.encode = result := by
  cases result with
  | mk state flow =>
    change Outcome.mk (WordState.unpack state.pack) flow = Outcome.mk state flow
    rw [WordState.unpack_pack]

theorem run_zero {X c n} (code : Stmt [] X c n) (policy : Policy.StmtP .A code)
    (state : WordState X n) : run code policy 0 state = none := rfl

theorem run_some_iff {X c n} (code : Stmt [] X c n) (policy : Policy.StmtP .A code)
    (fuel : Nat) (state : WordState X n) (result : Outcome X c n) :
    run code policy fuel state = some result ↔
      ∃ packed, evalStmt fuel model.environment model.words
        (program code policy).code (program code policy).words state.pack = some packed ∧
        Outcome.decode packed = result := Option.map_eq_some_iff

/-- For every fuel, encoding the ACTUAL raw result recovers the complete
interpreter result exactly. This is a concrete bijection, not a refinement
premise or a source/target compiler theorem. -/
theorem run_encode {X c n} (code : Stmt [] X c n) (policy : Policy.StmtP .A code)
    (fuel : Nat) (state : WordState X n) :
    (run code policy fuel state).map Outcome.encode =
      evalStmt fuel model.environment model.words
        (program code policy).code (program code policy).words state.pack := by
  change ((evalStmt fuel model.environment model.words
    (program code policy).code (program code policy).words state.pack).map Outcome.decode).map
      Outcome.encode = _
  cases execution : evalStmt fuel model.environment model.words
      (program code policy).code (program code policy).words state.pack with
  | none => rfl
  | some result =>
    change some (Outcome.encode (Outcome.decode result)) = some result
    rw [Outcome.encode_decode]

theorem run_stable {X c n} (code : Stmt [] X c n) (policy : Policy.StmtP .A code)
    (state : WordState X n) {lo hi : Nat} (increasing : lo ≤ hi)
    {result : Outcome X c n} (done : run code policy lo state = some result) :
    run code policy hi state = some result := by
  obtain ⟨packed,finished,decoded⟩ := (run_some_iff code policy lo state result).mp done
  exact (run_some_iff code policy hi state result).mpr
    ⟨packed,evalStmt_stable increasing model.environment model.words
      (program code policy).code (program code policy).words state.pack finished,decoded⟩

theorem run_completed_unique {X c n} (code : Stmt [] X c n)
    (policy : Policy.StmtP .A code) (state : WordState X n) {lo hi}
    {first second : Outcome X c n}
    (one : run code policy lo state = some first)
    (two : run code policy hi state = some second) : first = second := by
  rcases Nat.le_total lo hi with lower | higher
  · exact Option.some.inj ((run_stable code policy state lower one).symm.trans two)
  · exact Option.some.inj (one.symm.trans (run_stable code policy state higher two))


end Solidity.Yul.WordAdapter
