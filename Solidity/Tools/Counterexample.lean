import Solidity.Calculus.Spec
import Solidity.Tools.Common
import Solidity.Theory.Bridge.Denote

/-!
# Counterexamples: formulas evaluated in a state

`holds σ φ` is a `Prop`: a quantifier ranges over `2^256` values and
`{havoc}` over every storage, so it cannot be computed.  `Fml.eval3` is its
three-valued shadow, which evaluates everything else (terms, updates, the
programs under a modality) with the interpreter itself: a quantifier is
tried on a finite domain, `ff` as soon as one instance is `ff`, `tt` only
where the domain is the whole type (`bool`), `unknown` otherwise, and the
connectives are Kleene's.  An equation is decided where both sides
return (`Term.holdsEq_of_eval`) and `unknown` where one halts: `holds`
reads it through `denote`, where two halting sides may agree (`eqD` puts
the halt in its `defined` conjuncts, which are decided).  So an answer is
never wrong, only sometimes missing: `eval3_tt` and `eval3_ff` say that
`tt` implies `holds σ φ` and `ff` implies `¬ holds σ φ`.

A counterexample to a specification (`refuteSpec`) is a state in
which the stated premises (`I ∧ requires`) evaluate to `tt` and a
conjunct after the call to `ff`.  The premises that are true by
construction (`R`, `L`, `msg.value`, `Calculus/Spec.lean`) are not
evaluated but made true by the generator: arguments are drawn in their
type's range, storages are canonical (`Typing/Reachability.lean`: every
struct member present in order, a mapping's keys unique and its default the
type's), their words in range, and `msg.value` is `0` for a function that
is not `payable`.

The search is testing: small pools of values per primitive type (the
bounds, `0`, `1`, `2`, and the spec's own literals), all-default storages
over every combination of arguments first, then random states
(`GenSpec.sval` of `Tools/Common.lean` over the pools, seeded, so the result
is the same on every run).  A witness found
is shrunk before it is shown (Shrinking, below).

A witness is **certified** when the kernel checks `¬ ⊨ φ` from it:
`eval3_ff` applied to `φ.eval3 dom σ₀ = .ff`, which the kernel decides by
evaluating `eval3` on the closed terms (`certifyRefl`).  That needs every
premise to evaluate to `tt` in `σ₀`, and so fails when one is quantified
over a `uint`, as the layout premise of a mapping is; the witness is then
only **tested**.
-/

namespace Solidity.Tools

open Semantics

/-! ## Three truth values -/

/-- Kleene's truth values: `unknown` where a finite evaluation cannot
decide. -/
inductive Tri where
  | tt
  | ff
  | unknown
  deriving DecidableEq, Repr, Inhabited

namespace Tri

/-- Negation. -/
def not : Tri → Tri
  | tt => ff
  | ff => tt
  | unknown => unknown

/-- Conjunction: `ff` wins over `unknown`. -/
def and : Tri → Tri → Tri
  | ff, _ => ff
  | _, ff => ff
  | tt, tt => tt
  | _, _ => unknown

/-- Implication: `ff → _` and `_ → tt` are `tt` whatever the other side. -/
def imp : Tri → Tri → Tri
  | ff, _ => tt
  | _, tt => tt
  | tt, ff => ff
  | _, _ => unknown

/-- What a modality says of a run, as `Modality.after` says it. -/
def after (m : Modality) (k : State → Tri) : Res State → Tri
  | .ok τ => k τ
  | .error _ => match m with
    | .box => tt
    | .diamond => ff

end Tri

/-- `PrimTy.admits`, decided. -/
def _root_.Solidity.PrimTy.admitsB : PrimTy → Value → Bool
  | .bool, .bool _ => true
  | .uint, .int n => decide (0 ≤ n ∧ n < uintBound)
  | .int, .int n => decide (-intBound ≤ n ∧ n < intBound)
  | _, _ => false

theorem _root_.Solidity.PrimTy.admitsB_iff :
    (p : PrimTy) → (v : Value) → PrimTy.admitsB p v = true ↔ p.admits v
  | .bool, .bool _ | .uint, .int _ | .int, .int _
  | .bool, .int _ | .uint, .bool _ | .int, .bool _ => by
    simp only [PrimTy.admitsB, PrimTy.admits, Bool.decide_and, Bool.and_eq_true, decide_eq_true_eq,
      Bool.false_eq_true]

/-- The callee states `{havoc} φ` is tried at: none, and an emptied
ledger. -/
def havocSamples (σ : State) : List (List (Name × SVal) × List (Int × Int)) :=
  [(σ.storage, σ.net), (σ.storage, [])]

variable {C : Contract}

/-- **`holds`, evaluated**: `dom p` is the finite domain a quantifier over
`p` is tried on (only its values of type `p` are). -/
def _root_.Solidity.Fml.eval3 (dom : PrimTy → List Value) (σ : State) : Fml C → Tri
  | .tt => .tt
  | .eq a b =>
    match a.eval σ, b.eval σ with
    | .ok x, .ok y => if x = y then .tt else .ff
    | _, _ => .unknown
  | .defined t =>
    match t.eval σ with
    | .ok _ => .tt
    | .error _ => .ff
  | .not φ => (φ.eval3 dom σ).not
  | .and φ ψ => (φ.eval3 dom σ).and (ψ.eval3 dom σ)
  | .imp φ ψ => (φ.eval3 dom σ).imp (ψ.eval3 dom σ)
  | .upd m U φ => Tri.after m (fun τ => φ.eval3 dom τ) (U.apply σ)
  | .modal m P φ => Tri.after m (fun τ => φ.eval3 dom τ) (Prog.run σ P)
  | .havoc φ =>
    if (havocSamples σ).any fun (st, nt) => φ.eval3 dom (σ.havoc st nt) = .ff then .ff
    else .unknown
  | .all x p φ =>
    let rs := ((dom p).filter p.admitsB).map fun v => (v, φ.eval3 dom (σ.setEnv x (.val v)))
    if rs.any (·.2 = .ff) then .ff
    else if p = .bool && rs.any (·.1 = .bool true) && rs.any (·.1 = .bool false) &&
        rs.all (·.2 = .tt) then .tt
    else .unknown

theorem _root_.Solidity.Fml.eval3_sound (dom : PrimTy → List Value) : (φ : Fml C) → ∀ σ : State,
    (φ.eval3 dom σ = .tt → holds σ φ) ∧ (φ.eval3 dom σ = .ff → ¬ holds σ φ)
  | .tt, σ => ⟨fun _ => trivial, nofun⟩
  | .eq a b, σ => by
    simp only [Fml.eval3, holds]
    split
    · rename_i x y ha hb
      rw [Term.holdsEq_of_eval ha hb]
      by_cases hxy : x = y <;> simp only [hxy, if_true, if_false, reduceCtorEq, imp_false,
        not_true_eq_false, not_false_eq_true, implies_true, and_self]
    · simp only [reduceCtorEq, false_implies, and_self]
  | .defined t, σ => by
    simp only [Fml.eval3, holds]
    split <;> rename_i h <;> simp only [h, Except.ok.injEq, exists_eq', exists_false, imp_self,
      reduceCtorEq, not_true_eq_false, not_false_eq_true, and_self]
  | .not φ, σ => by
    have ih := Fml.eval3_sound dom φ σ
    simp only [Fml.eval3, holds]
    cases h : φ.eval3 dom σ <;> simp_all only [Tri.not, reduceCtorEq, false_implies, forall_const,
      true_and, and_true, and_self, implies_true, not_true_eq_false, not_false_eq_true,
      Classical.not_not]
  | .and φ ψ, σ => by
    have ih₁ := Fml.eval3_sound dom φ σ
    have ih₂ := Fml.eval3_sound dom ψ σ
    simp only [Fml.eval3, holds]
    cases h₁ : φ.eval3 dom σ <;> cases h₂ : ψ.eval3 dom σ <;>
      simp_all only [Tri.and, reduceCtorEq, false_implies, forall_const, true_and, and_true,
        and_false, false_and, and_self, implies_true, not_true_eq_false, not_false_eq_true, not_and]
  | .imp φ ψ, σ => by
    have ih₁ := Fml.eval3_sound dom φ σ
    have ih₂ := Fml.eval3_sound dom ψ σ
    simp only [Fml.eval3, holds]
    cases h₁ : φ.eval3 dom σ <;> cases h₂ : ψ.eval3 dom σ <;>
      simp_all only [Tri.imp, reduceCtorEq, false_implies, forall_const, true_and, and_true,
        and_self, implies_true, not_true_eq_false, not_false_eq_true, not_imp]
  | .upd m U φ, σ => by
    simp only [Fml.eval3, holds]
    cases U.apply σ with
    | ok τ => exact Fml.eval3_sound dom φ τ
    | error _ => cases m <;> simp only [Tri.after, Modality.after, Modality.onHalt,
      reduceCtorEq, imp_self, not_true_eq_false, not_false_eq_true, and_self]
  | .modal m P φ, σ => by
    simp only [Fml.eval3, holds]
    cases Prog.run σ P with
    | ok τ => exact Fml.eval3_sound dom φ τ
    | error _ => cases m <;> simp only [Tri.after, Modality.after, Modality.onHalt,
      reduceCtorEq, imp_self, not_true_eq_false, not_false_eq_true, and_self]
  | .havoc φ, σ => by
    simp only [Fml.eval3, holds]
    split
    · rename_i h
      obtain ⟨⟨st, nt⟩, _, hff⟩ := List.any_eq_true.mp h
      exact ⟨nofun, fun _ hall =>
        (Fml.eval3_sound dom φ _).2 (of_decide_eq_true hff) (hall st nt)⟩
    · exact ⟨nofun, nofun⟩
  | .all x p φ, σ => by
    simp only [Fml.eval3, holds]
    split
    · rename_i h
      obtain ⟨_, hmem, hff⟩ := List.any_eq_true.mp h
      obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hmem
      have hff : φ.eval3 dom (σ.setEnv x (.val v)) = .ff := of_decide_eq_true hff
      obtain ⟨_, hadm⟩ := List.mem_filter.mp hv
      exact ⟨nofun, fun _ hall =>
        (Fml.eval3_sound dom φ _).2 hff (hall v ((PrimTy.admitsB_iff p v).mp hadm))⟩
    · split
      · rename_i h
        simp only [Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true, List.all_eq_true,
          List.mem_map] at h
        obtain ⟨⟨⟨hp, ⟨_, ⟨t, htm, rfl⟩, htv⟩⟩, ⟨_, ⟨f, hfm, rfl⟩, hfv⟩⟩, hall⟩ := h
        subst hp
        refine ⟨fun _ v hv => ?_, nofun⟩
        cases v with
        | int _ => exact hv.elim
        | bool b =>
          cases b
          · exact (Fml.eval3_sound dom φ _).1 (by simpa only [← hfv] using hall _ ⟨f, hfm, rfl⟩)
          · exact (Fml.eval3_sound dom φ _).1 (by simpa only [← htv] using hall _ ⟨t, htm, rfl⟩)
      · exact ⟨nofun, nofun⟩

/-- **A `tt` is a truth**: `φ` holds in `σ`. -/
theorem _root_.Solidity.Fml.eval3_tt {dom : PrimTy → List Value} {σ : State} {φ : Fml C}
    (h : φ.eval3 dom σ = .tt) : holds σ φ :=
  (Fml.eval3_sound dom φ σ).1 h

/-- **An `ff` is a counterexample**: `φ` does not hold in `σ`, so `φ` is not
valid. -/
theorem _root_.Solidity.Fml.eval3_ff {dom : PrimTy → List Value} {σ : State} {φ : Fml C}
    (h : φ.eval3 dom σ = .ff) : ¬ holds σ φ :=
  (Fml.eval3_sound dom φ σ).2 h

/-- A state where `φ` evaluates to `ff` refutes `⊨ φ`: the statement a
certificate proves. -/
theorem _root_.Solidity.Fml.not_valid_of_eval3 {dom : PrimTy → List Value} (σ : State) {φ : Fml C}
    (h : φ.eval3 dom σ = .ff) : ¬ Valid φ :=
  fun hv => Fml.eval3_ff h (hv σ)

/-! ## The values tried -/

/-- The integer literals a clause mentions. -/
def specNums : SpecExpr → List Int
  | .num n => [n]
  | .old e | .net e | .field e _ | .unop _ e | .all _ _ e | .ex _ _ e => specNums e
  | .index a b | .binop _ a b | .imp a b | .iff a b => specNums a ++ specNums b
  | .bool _ | .name _ | .result => []

/-- The integer literals a location's keys mention. -/
def locNums : SpecLoc → List Int
  | .root _ => []
  | .field l _ | .all l => locNums l
  | .index l e => locNums l ++ specNums e

/-- The `uint`s tried: `0`, `1`, `2`, each literal `n` of the specification
with `n ± 1`, and the two largest, in that order: a combination of small
arguments is tried first. -/
def uintPool (lits : List Int) : List Int :=
  (([0, 1, 2] ++ lits.flatMap (fun n => [n, n + 1, n - 1]) ++ [uintBound - 1, uintBound - 2]).filter
    fun n => decide (0 ≤ n ∧ n < uintBound)).eraseDups

/-- The `int`s tried: `0`, `±1`, the bounds, and each literal with its
negation and neighbours. -/
def intPool (lits : List Int) : List Int :=
  (([0, 1, -1] ++ lits.flatMap (fun n => [n, -n, n + 1, n - 1]) ++ [-intBound, intBound - 1]).filter
    fun n => decide (-intBound ≤ n ∧ n < intBound)).eraseDups

/-- The domain a quantifier is tried on, and the pool arguments and stored
words are drawn from. -/
def poolDom (lits : List Int) : PrimTy → List Value
  | .bool => [.bool true, .bool false]
  | .uint => (uintPool lits).map .int
  | .int => (intPool lits).map .int

/-! ## Random states -/

/-- How a search draws a storage: every word from `vals`, a mapping's keys
from `keys`, up to `3` entries, arrays of fewer than `3` elements. -/
def pooledGen (vals : PrimTy → List Value) (keys : PrimTy → List Int) : GenSpec where
  prim p := pickD (PrimTy.default p) (vals p)
  key K := some (pickD 0 (keys K))
  entries := 4
  length := 3

/-- Every combination, the first list's element first. -/
def products {α : Type} : List (List α) → List (List α)
  | [] => [[]]
  | xs :: rest => xs.flatMap fun x => (products rest).map (x :: ·)

/-- A candidate: the storage, the arguments, the transaction, the ledger
and the funds a call starts from. -/
structure Cand where
  st : List (Name × SVal)
  args : List (String × Value)
  tx : TxEnv := { msgSender := 1 }
  net : List (Int × Int) := []
  bal : Int := 0

/-- The state a candidate starts in: the arguments bound as locals. -/
def Cand.state [FreshNames] (c : Cand) : State :=
  { storage := c.st, env := c.args.map fun (n, v) => (Var.ofName n, .val v), tx := c.tx,
    net := c.net, selfBalance := c.bal }

/-- A random candidate: arguments of the types `ps`, a sender, a storage of
`C`'s layout whose mapping keys include the arguments and the sender. -/
def genCandidate (C : Contract) (lits : List Int) (ps : List (String × PrimTy))
    (payable : Bool) : Gen Cand := do
  let dom := poolDom lits
  let args ← ps.mapM fun (n, p) => do pure (n, ← pickD (PrimTy.default p) (dom p))
  let sender ← pickD 1 ([1, 2] ++ uintPool lits)
  let argInts := args.filterMap fun (_, v) => match v with
    | .int n => some n
    | .bool _ => none
  let keys : PrimTy → List Int := fun
    | .bool => [0, 1]
    | .uint => (uintPool lits ++ (sender :: argInts).filter (0 ≤ ·)).eraseDups
    | .int => (intPool lits ++ sender :: argInts).eraseDups
  let st ← (pooledGen dom keys).storage C
  let value ← if payable then pickD 0 (uintPool lits) else pure 0
  let time ← pickD 0 (uintPool lits)
  let paid ← pickD 0 (uintPool lits)
  let net ← pickD [] [[], [(sender, paid)]]
  let bal ← pickD 0 [0, 1, uintBound - 1]
  pure { st, args, tx := { msgSender := sender, msgValue := value, timestamp := time }, net, bal }

/-! ## Shrinking

A witness found at random is shrunk before it is shown: the ledger emptied,
the funds and the timestamp zeroed, the sender `1`, a state variable reset to its default,
a mapping entry dropped, and a large number renamed to a small one unused
elsewhere, everywhere it occurs (arguments, sender, keys, words), so that
the equalities the witness relies on survive.  A step is kept when the
candidate is still a counterexample. -/

/-- The integers a storage value holds, keys included. -/
partial def SVal.ints : SVal → List Int
  | .prim (.int n) => [n]
  | .prim (.bool _) => []
  | .struct fs => fs.flatMap fun (_, v) => SVal.ints v
  | .array es sh _ => (es ++ sh).flatMap SVal.ints
  | .map es d => es.flatMap (fun (k, v) => k :: SVal.ints v) ++ SVal.ints d

/-- `v` renamed `s`, keys and words alike. -/
partial def SVal.rename (v s : Int) : SVal → SVal
  | .prim (.int n) => .prim (.int (if n = v then s else n))
  | .prim (.bool b) => .prim (.bool b)
  | .struct fs => .struct (fs.map fun (f, x) => (f, SVal.rename v s x))
  | .array es sh fx => .array (es.map (SVal.rename v s)) (sh.map (SVal.rename v s)) fx
  | .map es d => .map (es.map fun (k, x) => (if k = v then s else k, SVal.rename v s x))
    (SVal.rename v s d)

/-- The integers a candidate mentions. -/
def Cand.ints (c : Cand) : List Int :=
  (c.args.filterMap (fun (_, v) => match v with | .int n => some n | .bool _ => none) ++
    c.tx.msgSender :: c.st.flatMap (fun (_, v) => SVal.ints v)).eraseDups

/-- `v` renamed `s` everywhere in a candidate. -/
def Cand.rename (c : Cand) (v s : Int) : Cand :=
  let r (n : Int) : Int := if n = v then s else n
  { c with
    st := c.st.map fun (x, sv) => (x, SVal.rename v s sv)
    args := c.args.map fun (x, a) => (x, match a with | .int n => .int (r n) | .bool b => .bool b)
    tx := { c.tx with msgSender := r c.tx.msgSender }
    net := c.net.map fun (a, b) => (r a, b) }

/-- The candidates one shrinking step away, simplest first. -/
def Cand.shrinks (C : Contract) (c : Cand) : List Cand :=
  let small : List Int := [0, 1, 2, 3]
  let ints := c.ints
  let renames := (ints.filter (fun v => !small.contains v)).flatMap fun v =>
    (small.filter (!ints.contains ·)).map (c.rename v)
  let resets := C.vars.filterMap fun (r, T) =>
    if lookupBy r c.st == some (defaultForTy T) then none
    else some { c with st := setBy r (defaultForTy T) c.st }
  let drops := c.st.flatMap fun (r, v) => match v with
    | .map es d => (List.range es.length).map fun i =>
      { c with st := setBy r (.map (es.eraseIdx i) d) c.st }
    | _ => []
  (if c.net.isEmpty then [] else [{ c with net := [] }]) ++
  (if c.bal = 0 then [] else [{ c with bal := 0 }]) ++
  (if c.tx.timestamp = 0 then [] else [{ c with tx := { c.tx with timestamp := 0 } }]) ++
  (if c.tx.msgValue = 0 then [] else [{ c with tx := { c.tx with msgValue := 0 } }]) ++
  (if c.tx.msgSender = 1 then [] else [{ c with tx := { c.tx with msgSender := 1 } }]) ++
  resets ++ drops ++ renames

/-- **Shrink** `c` while `ok` holds of it, one step at a time, at most
`fuel` steps. -/
def Cand.shrink (C : Contract) (ok : Cand → Bool) : Nat → Cand → Cand
  | 0, c => c
  | fuel + 1, c =>
    match (c.shrinks C).find? ok with
    | some c' => Cand.shrink C ok fuel c'
    | none => c

/-! ## The search -/

/-- **A counterexample**: the state the call starts in (its storage, the
arguments bound as locals, the transaction, the ledger), the arguments, the
run's outcome (`none` for a formula with no run in front), and the indices
of the conjuncts after the call that evaluate to `ff`. -/
structure Witness where
  state : State
  args : List (String × Value)
  outcome : Option (Res State)
  failing : List Nat

/-- What a search found, among how many candidates, of which how many met
the stated premises. -/
structure Search where
  witness : Option Witness
  tried : Nat
  admitted : Nat

section Search

variable [FreshNames]

/-- The obligation of `f` in pieces, and what the search needs of `f`: its
declaration, its parameters of value type, the literals of the clauses. -/
structure SpecProblem (C : Contract) where
  decl : FunDecl
  checked : List (Fml C)
  upd : Upd C
  prog : Prog C
  posts : List (Fml C)
  params : List (String × PrimTy)
  payable : Bool
  lits : List Int

/-- The problem of `f`: `specPieces`, the parameters, the literals. -/
def SpecProblem.of (C : Contract) (f : String) : Except String (SpecProblem C) := do
  let (_, checked, upd, prog, posts) ← specPieces C f
  let some d := lookupBy f C.funs | throw s!"{f} is not a function of the contract"
  let params := d.params.filterMap fun (n, T) => match T with
    | .prim p => some (n, p)
    | _ => none
  let lits := (C.inv ++ d.spec.requires ++ d.spec.ensures).flatMap specNums ++
    (d.spec.assignable.getD []).flatMap locNums
  pure { decl := d, checked, upd, prog, posts, params, payable := d.payable, lits }

/-- A candidate tried: `none` unless the stated premises evaluate to `tt`;
then the conjuncts that evaluate to `ff`, if any. -/
def SpecProblem.try (P : SpecProblem C) (c : Cand) : Option (Option Witness) :=
  let dom := poolDom P.lits
  let σ := c.state
  if !P.checked.all (fun φ => φ.eval3 dom σ = .tt) then none else
  let failing := ((List.range P.posts.length).zip P.posts).filterMap fun (i, φ) =>
    if (specBody C P.upd P.prog [φ]).eval3 dom σ = .ff then some i else none
  if failing.isEmpty then some none else
  some (some { state := σ, args := c.args, failing,
               outcome := some (P.upd.apply σ >>= fun τ => Prog.run τ P.prog) })

/-- Whether a candidate is a counterexample. -/
def SpecProblem.refutes (P : SpecProblem C) (c : Cand) : Bool :=
  match P.try c with
  | some (some _) => true
  | _ => false

/-- **The search for a counterexample to `f`'s specification**: the
all-default storage with every combination of pooled arguments first (when
there are at most half the budget of them), then random candidates up to
`budget`; what is found is shrunk. -/
def SpecProblem.search (P : SpecProblem C) (budget : Nat) : Search := Id.run do
  let dom := poolDom P.lits
  let combos := products (P.params.map fun (_, p) => dom p)
  let combos := if combos.length * 2 ≤ budget then combos else []
  let cands := combos.map fun vs =>
    ({ st := C.initStorage, args := P.params.map (·.1) |>.zip vs } : Cand)
  let mut admitted := 0
  let mut tried := 0
  let mut g := mkStdGen 2026
  let mut found : Option Cand := none
  for c in cands do
    tried := tried + 1
    match P.try c with
    | none => pure ()
    | some none => admitted := admitted + 1
    | some (some _) => found := some c; break
  if found.isNone then
    for _ in [0:budget - tried] do
      let (c, g') := (genCandidate C P.lits P.params P.payable).run g
      g := g'
      tried := tried + 1
      match P.try c with
      | none => pure ()
      | some none => admitted := admitted + 1
      | some (some _) => found := some c; break
  let some c := found | return { witness := none, tried, admitted }
  let c := c.shrink C P.refutes 64
  return { witness := (P.try c).join, tried, admitted := admitted + 1 }

/-- The run in front of a formula: `{U} [ P ]`, `[ P ]`, `{U}`, under
implications. -/
def _root_.Solidity.Fml.runOf (σ : State) : Fml C → Option (Res State)
  | .imp _ ψ => Fml.runOf σ ψ
  | .upd _ U (.modal _ P _) => some (U.apply σ >>= fun τ => Prog.run τ P)
  | .modal _ P _ => some (Prog.run σ P)
  | .upd _ U _ => some (U.apply σ)
  | _ => none

/-- **A counterexample to a closed formula**: its user-named variables bound
to pooled `uint`s (every combination first), the storage all-default, then
random storages of `C`'s layout; what is found is shrunk. -/
def searchFml (C : Contract) (φ : Fml C) (budget : Nat := 2000) : Search := Id.run do
  let xs := (φ.vars.filterMap fun | .user n => some n | .fresh .. => none).eraseDups
  let dom := poolDom []
  let refutes (c : Cand) : Bool := φ.eval3 dom c.state = .ff
  let combos := products (xs.map fun _ => dom .uint)
  let combos := if combos.length * 2 ≤ budget then combos else []
  let mut tried := 0
  let mut g := mkStdGen 2026
  let mut found : Option Cand := none
  for vs in combos do
    tried := tried + 1
    let c : Cand := { st := C.initStorage, args := xs.zip vs }
    if refutes c then found := some c; break
  if found.isNone then
    for _ in [0:budget - tried] do
      let (c, g') := (genCandidate C [] (xs.map (·, .uint)) true).run g
      g := g'
      tried := tried + 1
      if refutes c then found := some c; break
  let some c := found | return { witness := none, tried, admitted := tried }
  let c := c.shrink C refutes 64
  let σ := c.state
  return { witness := some { state := σ, args := c.args, failing := [], outcome := φ.runOf σ },
           tried, admitted := tried }

/-! ## Printing a witness -/

/-- A witness, one fact per line: the arguments and the transaction
(`fmtTx`), the storage before, and after the run (or how it halted). -/
def Witness.lines (C : Contract) (w : Witness) : List String :=
  let σ := w.state
  let args := w.args.map fun (n, v) => s!"{n} = {Value.fmt v}"
  let after := match w.outcome with
    | none => []
    | some (.error h) => [s!"after: {fmtHalt h}"]
    | some (.ok τ) =>
      let res := ((τ.valueOf resultVar).map fun v => s!"\\result = {Value.fmt v}").toList
      ["after: " ++ "; ".intercalate (fmtStorage C τ.storage ++ res)]
  [", ".intercalate (args ++ fmtTx σ), "before: " ++ fmtStorageLine C σ.storage] ++ after

/-! ## Certificates -/

section Meta

open Lean Meta

deriving instance ToExpr for Semantics.SVal
deriving instance ToExpr for Semantics.MVal
deriving instance ToExpr for Semantics.MObj
deriving instance ToExpr for Semantics.Seg
deriving instance ToExpr for Semantics.Binding
deriving instance ToExpr for Semantics.ExtKey
deriving instance ToExpr for Semantics.ExtResult
deriving instance ToExpr for Semantics.TxEnv
deriving instance ToExpr for Semantics.State

/-- **The certificate**: the kernel checks `¬ ⊨ φ` as `Fml.not_valid_of_eval3`
at `σ`, deciding `φ.eval3 (poolDom lits) σ = .ff` by evaluation.  The
kernel runs under `heartbeats` (thousands), below the default, and the
declaration is checked, never added. -/
def certifyRefl (cE φE : Expr) (lits : List Int) (σ : Semantics.State)
    (heartbeats : Nat := 100000) :
    MetaM Bool := do
  let domE := mkApp (mkConst ``poolDom) (toExpr lits)
  let σE := toExpr σ
  let eq ← mkEq (mkAppN (mkConst ``Fml.eval3) #[cE, domE, σE, φE]) (mkConst ``Tri.ff)
  let h ← mkDecideProof eq
  let decl := Declaration.thmDecl {
    name := `_counterexample_certificate, levelParams := []
    type := mkNot (mkApp2 (mkConst ``Valid) cE φE)
    value := mkAppN (mkConst ``Fml.not_valid_of_eval3) #[cE, domE, σE, φE, h] }
  let opts := maxHeartbeats.set (← getOptions) heartbeats
  match Kernel.Environment.addDecl (← getEnv).toKernelEnv opts decl with
  | .ok _ => pure true
  | .error _ => pure false

/-- A refutation: the witness, whether the kernel certified it, and the
conjuncts it fails, as the specification writes them. -/
structure Refutation where
  witness : Witness
  certified : Bool
  fails : List MessageData

/-- The `i`-th conjunct owed after the call of `d`, `φ`: an invariant or an
`ensures` as written, a conjunct of the frame of `assignable` as the
formula it is (quoted against the contract `cE`). -/
def postLabel (C : Contract) (d : FunDecl) (cE : Expr) (i : Nat) (φ : Fml C) : MessageData :=
  if h : i < C.inv.length then m!"invariant {SpecExpr.fmt C.inv[i]}"
  else if h' : i - C.inv.length < d.spec.ensures.length then
    m!"ensures {SpecExpr.fmt d.spec.ensures[i - C.inv.length]}"
  else
    let locs := (d.spec.assignable.getD []).map SpecLoc.fmt
    m!"assignable {if locs.isEmpty then "\\nothing" else ", ".intercalate locs}: {Fml.quote cE φ}"

/-- **Refute `f`'s specification**: search, then certify what was found.
`n` names the contract `C`. -/
def refuteSpec (n : Lean.Name) (C : Contract) (f : String) (budget : Nat := 2000) :
    MetaM (Except String (Search × Option Refutation)) := do
  match SpecProblem.of C f, specObligation C f with
  | .error e, _ | _, .error e => pure (.error e)
  | .ok P, .ok φ =>
    let s := P.search budget
    let some w := s.witness | pure (.ok (s, none))
    let cE := mkConst n
    -- the kernel is asked only what the evaluator already answered
    let certified ← if φ.eval3 (poolDom P.lits) w.state = .ff then
        certifyRefl cE (Fml.quote cE φ) P.lits w.state
      else pure false
    let fails := w.failing.map fun i => postLabel C P.decl cE i (P.posts.getD i .tt)
    pure (.ok (s, some { witness := w, certified, fails }))

/-- The report of a refutation: the witness and the conjuncts it fails. -/
def Refutation.lines (C : Contract) (r : Refutation) : List MessageData :=
  (r.witness.lines C).map toMessageData ++ r.fails.map fun l => m!"fails: {l}"

/-- The head line of a refutation of `f`, as `#verify` and
`#counterexample` print it: `✗ f (certified):`. -/
def Refutation.head (f : String) (r : Refutation) : MessageData :=
  m!"✗ {f} ({if r.certified then "certified" else "tested"}):"

/-- The report of the search for a counterexample to `f`'s specification. -/
def searchReport (C : Contract) (f : String) : Search × Option Refutation → MessageData
  | (_, some r) => reportMsg (r.head f) (r.lines C)
  | (s, none) =>
    m!"no counterexample to {f} found in {s.tried} candidates ({s.admitted} met the premises)"

end Meta

end Search

/-! ## `#counterexample` -/

/-- `#counterexample C.f`: a counterexample to the specification of the
function `f` of the contract `C`; `#counterexample C`: to each of its
functions with an obligation; `#counterexample φ`: to the closed formula
`φ : Fml C`. -/
syntax (name := counterexampleCmd) "#counterexample " term : command

open Lean Elab Command Term Meta in
/-- `#counterexample`: a function's specification, a contract's, or a
formula. -/
@[command_elab counterexampleCmd]
def elabCounterexample : Lean.Elab.Command.CommandElab := fun stx => liftTermElabM do
  let t := stx[1]
  let target ← if t.isIdent then resolveTarget? "#counterexample" t.getId else pure none
  let one (c : Lean.Name) (C : Contract) (f : String) : TermElabM Unit := do
    match ← refuteSpec c C f with
    | .error e => throwError "#counterexample: {e}"
    | .ok r => logInfo (searchReport C f r)
  match target with
  | some (.function c C f) => one c C f
  | some (.contract c C) =>
    let fs := C.funs.filter fun (_, d) => hasObligation C d
    if fs.isEmpty then logInfo m!"{c} has no function with a specification"
    for (f, _) in fs do one c C f
  | none =>
    let (φE, cE, _) ← elabFormula "#counterexample" ⟨t⟩
    let C ← unsafe evalExpr Contract (Lean.mkConst ``Contract) cE
    let φ ← unsafe evalExpr (Fml C) (← inferType φE) φE
    let s := searchFml C φ
    let some w := s.witness
      | logInfo m!"no counterexample found in {s.tried} candidates"
    let certified ← if φ.eval3 (poolDom []) w.state = .ff then certifyRefl cE φE [] w.state
      else pure false
    logReport m!"counterexample ({if certified then "certified" else "tested"}):"
      ((w.lines C).map toMessageData)

end Solidity.Tools
