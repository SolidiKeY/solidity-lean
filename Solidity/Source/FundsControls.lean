import Solidity.Source.Funds
import Solidity.Source.SemanticsExamples

/-! Actual typed Source controls for request admission, not a compiler/EVM or
real-ledger specification proof. Fixed fixture ledgers are explicit below. -/
namespace Solidity.Source.FundsControls
open Solidity.Roadmap (Address Word Bytes Request Outcome Event SessionEnv Action Pipeline)
open Solidity.Source.SemanticsExamples (word addr toyFixed selOf answerOnly)

/-- Fixture-only decidable structural equality; no execution oracle. -/
private instance : DecidableEq (Except Halt Outcome) := fun a b =>
  match a, b with
  | .error x, .error y => decidable_of_iff (x = y) (by constructor <;> intro h <;> cases h <;> rfl)
  | .ok x, .ok y => decidable_of_iff (x = y) (by constructor <;> intro h <;> cases h <;> rfl)
  | .error _, .ok _ => isFalse (by intro h; cases h)
  | .ok _, .error _ => isFalse (by intro h; cases h)
private instance : DecidableEq (Roadmap.Prefix Event Outcome) := fun a b =>
  decidable_of_iff (a.events = b.events ∧ a.final = b.final) (by
    cases a; cases b
    simp only [Roadmap.Prefix.mk.injEq])

def declaration : Syn (.part false) :=
  .function (.ident "pay") .nil (some .pub) (some .payable) .nil false none .nil (.some (.block .nil))
def unit : Syn .unit := .unit (.cons (.contract false "Funds" .none .nil (.cons declaration .nil)) .nil)
def E : Env := unit.env
def body : RBody E := ⟨[], [], false, [], [], .nil, []⟩
def program : Program E where
  body d := if d.name = "pay" then some body else none
  consts _ := none
  inits _ := []
  ctor _ := none
  ctorLocals _ := []
  baseArgs _ := []
  contracts := ["Funds"]
def target : Address := addr 11
def sender : Address := addr 17
def other : Address := addr 19

def opening (amount : Word) : Address → Word := fun a => if a = sender then amount else word 0
def request (amount : Word) : Request := ⟨sender, target, amount, word 5, selOf "pay()"⟩

def account : Account E.layout (E.lay target) :=
  { balance := word 0, nonce := 1, code := some 0, storage := Storage.empty }
def initial : St E :=
  { St.init E with ex := ⟨(St.init E).ex.world.set target account,
      (St.init E).ex.transient, []⟩ }

def env (amount : Word) (actions : List Action) : SessionEnv where
  deployer := sender
  deployNonce := ⟨0, by decide⟩
  deployValue := word 0
  deployArgs := []
  balance := opening amount
  hasCode := fun _ _ => false
  requests := fun _ i => actions[i]?
  callee := answerOnly

def prog (p : Pipeline) : SrcProg E := ⟨program, p, toyFixed, "Funds"⟩
def glob (p : Pipeline) (amount : Word) : Glob E := (prog p).glob (env amount [])
def last : Outcome := .success [0xCA, 0xFE]

def stressSeed : St E :=
  { initial with
    events := [.credit other (word 3)]
    logs := [(target, [0xAA, 0xBB])]
    ex := initial.ex.apply (.account target fun a => { a with nonce := 9 }) }
def allocated : St E :=
  ((allocRef (Data.bytes (D := E.layout) (l := .memory) [0xDE, 0xAD]) : EM E [] _).run
    (L0 E, stressSeed)).2.2
def before : St E :=
  { allocated with fnLocals := ⟨[.bytes .memory], .cons (.memRef rfl 0) .nil⟩ }

theorem rejected_whole_state (p : Pipeline) (n : Nat) :
    runCheckedTx (glob p (word 8)) n (request (word 9)) before = (none, before) :=
  runCheckedTx_invalid _ _ _ _ rfl

theorem rejected_stress_fields (p : Pipeline) :
    let s := (runCheckedTx (glob p (word 8)) 0 (request (word 9)) before).2
    s.heap.next = 1 ∧ s.ex.journal.length = 1 ∧ s.logs = [(target, [0xAA, 0xBB])] ∧
    (heapBytes (E := E) (Γ := []) 0).run (L0 E, s) = (.ok [0xDE, 0xAD], (L0 E, s)) := by
  rw [rejected_whole_state]
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem exact_balance_runs (p : Pipeline) :
    let r := runCheckedTx (glob p (word 9)) 20 (request (word 9)) initial
    r.1 = some (.ok (.success [])) ∧
    (r.2.ex.world.accounts target).balance = word 9 ∧
    r.2.events = [.tx sender target (word 9) (word 5) (selOf "pay()") (.success [])] := by
  cases p <;> decide +kernel

theorem wrong_recipient_balance :
    requestFunded toyFixed (fun a => if a = target then word 100 else word 0) []
      (request (word 9)) = false := by decide

theorem zero_value_runs (p : Pipeline) :
    (runCheckedTx (glob p (word 0)) 20 (request (word 0)) initial).1 = some (.ok (.success [])) := by
  cases p <;> decide +kernel

theorem invalid_then_end (p : Pipeline) (n : Nat) :
    sessionGo (prog p) (env (word 8) [.request (request (word 9))]) n 2 0 before last =
      ⟨before.events, some last⟩ ∧
    sessionGoEvents (prog p) (env (word 8) [.request (request (word 9))]) n 2 0 before last =
      ⟨before.events, some last⟩ :=
  dropped_then_end _ _ _ 0 0 _ _ _ rfl rfl rfl

theorem funded_timeout_is_not_drop (p : Pipeline) :
    (runCheckedTx (glob p (word 9)) 0 (request (word 9)) initial).1 = some (.error .timeout) := by
  cases p <;> decide +kernel

/-- A funded request with missing receiver code executes and reverts; it must
not be confused with an invalid dropped request. -/
def missingCode : St E := St.init E
theorem funded_revert_is_not_drop (p : Pipeline) :
    let r := runCheckedTx (glob p (word 9)) 20 (request (word 9)) missingCode
    r.1 = some (.ok (.revert [])) ∧
    r.2.events = [.tx sender target (word 9) (word 5) (selOf "pay()") (.revert [])] := by
  cases p <;> decide +kernel

theorem invalid_advances_to_valid (p : Pipeline) :
    let e := env (word 8) [.request (request (word 9)), .request (request (word 8))]
    let events := [.tx sender target (word 8) (word 5) (selOf "pay()") (.success [])]
    sessionGo (prog p) e 20 3 0 initial last = ⟨events, some (.success [])⟩ ∧
    sessionGoEvents (prog p) e 20 3 0 initial last = ⟨events, some (.success [])⟩ := by
  cases p <;> decide +kernel

/-- Control ledger: successful transactions debit the sender from the actual
prior event history. This fixture does not implement the full external ledger. -/
def debit (old : Word) (events : List Event) (who : Address) : Word :=
  events.foldl (fun balance event => match event with
    | .tx s _ v _ _ (.success _) => if s = who then
        ⟨balance.val - v.val, Nat.lt_of_le_of_lt (Nat.sub_le _ _) balance.isLt⟩ else balance
    | _ => balance) old

def debitFixed : Roadmap.Fixed := { toyFixed with ledger := fun b h a => debit (b a) h a }
def debitProg (p : Pipeline) : SrcProg E := { prog p with fixed := debitFixed }

theorem earlier_tx_debits (p : Pipeline) :
    let e := env (word 9) [.request (request (word 9)), .request (request (word 9))]
    let events := [.tx sender target (word 9) (word 5) (selOf "pay()") (.success [])]
    sessionGo (debitProg p) e 20 3 0 initial last = ⟨events, some (.success [])⟩ ∧
    sessionGoEvents (debitProg p) e 20 3 0 initial last = ⟨events, some (.success [])⟩ := by
  cases p <;> decide +kernel

/-- Control ledger: a recorded credit to the sender makes nine available. -/
def credited (b : Address → Word) (h : List Event) (a : Address) : Word :=
  if h.any (fun e => match e with | .credit t _ => t == a | _ => false) then word 9 else b a
def creditFixed : Roadmap.Fixed := { toyFixed with ledger := credited }

def creditProg (p : Pipeline) : SrcProg E := { prog p with fixed := creditFixed }

theorem prior_credit_funds (p : Pipeline) :
    let e := env (word 0) [.credit sender (word 9), .request (request (word 9))]
    let events := [.credit sender (word 9), .tx sender target (word 9) (word 5) (selOf "pay()") (.success [])]
    sessionGo (creditProg p) e 20 3 0 initial last = ⟨events, some (.success [])⟩ ∧
    sessionGoEvents (creditProg p) e 20 3 0 initial last = ⟨events, some (.success [])⟩ := by
  cases p <;> decide +kernel
end Solidity.Source.FundsControls


/-- info: 'Solidity.Source.requestFunded_true_iff' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.requestFunded_true_iff

/-- info: 'Solidity.Source.requestFunded_false_iff' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.requestFunded_false_iff

/-- info: 'Solidity.Source.runCheckedTx_invalid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.runCheckedTx_invalid

/-- info: 'Solidity.Source.runCheckedTx_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.runCheckedTx_valid

/-- info: 'Solidity.Source.runCheckedTx_result_funded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.runCheckedTx_result_funded

/-- info: 'Solidity.Source.runCheckedTx_invalid_state' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.runCheckedTx_invalid_state

/-- info: 'Solidity.Source.runCheckedTx_stable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.runCheckedTx_stable

/-- info: 'Solidity.Source.sessionGo_drop_unfunded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.sessionGo_drop_unfunded

/-- info: 'Solidity.Source.sessionGoEvents_drop_unfunded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.sessionGoEvents_drop_unfunded

/-- info: 'Solidity.Source.dropped_then_end' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.dropped_then_end

/-- info: 'Solidity.Source.FundsControls.rejected_whole_state' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.FundsControls.rejected_whole_state

/-- info: 'Solidity.Source.FundsControls.rejected_stress_fields' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.FundsControls.rejected_stress_fields

/-- info: 'Solidity.Source.FundsControls.exact_balance_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.FundsControls.exact_balance_runs

/-- info: 'Solidity.Source.FundsControls.wrong_recipient_balance' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.FundsControls.wrong_recipient_balance

/-- info: 'Solidity.Source.FundsControls.zero_value_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.FundsControls.zero_value_runs

/-- info: 'Solidity.Source.FundsControls.invalid_then_end' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.FundsControls.invalid_then_end

/-- info: 'Solidity.Source.FundsControls.funded_timeout_is_not_drop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.FundsControls.funded_timeout_is_not_drop

/-- info: 'Solidity.Source.FundsControls.funded_revert_is_not_drop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.FundsControls.funded_revert_is_not_drop

/-- info: 'Solidity.Source.FundsControls.invalid_advances_to_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.FundsControls.invalid_advances_to_valid

/-- info: 'Solidity.Source.FundsControls.earlier_tx_debits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.FundsControls.earlier_tx_debits

/-- info: 'Solidity.Source.FundsControls.prior_credit_funds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.FundsControls.prior_credit_funds
