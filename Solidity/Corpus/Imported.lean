import Solidity.Corpus.Basic
import Solidity.Calculus.Problem
import Solidity.Calculus.Core.Sound
import Solidity.Calculus.Core.Spec
import Solidity.Calculus.Core.HoldsErase
import Solidity.Calculus.Core.Close
import Solidity.Solkey.TestSuite

/-!
# The corpus's `TestSuite` is the imported one

solkey's `TestSuite.sol` reaches Lean twice: as the hand-written contract
`TestSuite` (`Syntax.lean`), which the examples write `sol[TestSuite]{ … }`
against, and as `Solkey.TestSuite`, which `solc_import` reads from solc's
AST (`Solidity/Solkey/TestSuite.lean`) and whose obligations are derived by
`⊢` (`Solidity/TestSuite/`).  The corpus now takes its `TestSuite` rows from
the second: `scripts/solkey-port.mjs` no longer translates the source, it
reads `TestSuite/Report.lean`'s pin, and `Corpus/TestSuite.lean` states each
derived obligation at the initial storage as a corollary of its theorem.

**Why the initial storage, and not `State.testSuiteStore`.**  The
corollaries need `wt(storage)` at the store, and `wt` is read over the
imported contract's roots: `testSuiteStore` is the hand-written contract's
store, which has neither `fixedByKey` nor `boolKeyed` and names two roots
differently, so it is no storage of `Solkey.TestSuite`.  Its own initial
state is (`Solkey.TestSuite.initState_wt`).

**The two contracts agree** where they overlap: every root of the
hand-written contract is a root of the imported one, at the same type, up
to two renames (`people` is `folks` and `a` is `aux` there, since those
names mean other things in other contracts).  Struct members need no check:
both contracts read `Semantics.structDef`, and both name solkey's `Triple`
`FixedTriple`.  The imported contract has two roots more (below); `tree`,
the struct recursive through a mapping, is in neither.
-/

namespace Solidity.Corpus

open Semantics

/-- The hand-written `TestSuite`'s names for two of solkey's roots. -/
def testSuiteRenames : List (Name × Name) := [("folks", "people"), ("aux", "a")]

/-- Every root of the hand-written `TestSuite` is a root of the imported
contract, at the same type, after `testSuiteRenames`. -/
theorem testSuite_agrees :
    TestSuite.vars.all (fun (n, T) =>
      lookupBy ((lookupBy n testSuiteRenames).getD n) Solkey.TestSuite.vars == some T) = true := by
  decide +kernel

/-! The roots only the imported contract has: `fixedByKey`, and the
bool-keyed mapping, its key read as a `uint` (solc encodes a bool key as
`0` or `1`). -/

/--
info: [fixedByKey, boolKeyed]
-/
#guard_msgs in
#eval IO.println ((Solkey.TestSuite.vars.filter fun (n, _) =>
  ((testSuiteRenames.map fun (a, b) => (b, a)).lookup n |>.getD n |>
    (lookupBy · TestSuite.vars)).isNone).map (·.1))

end Solidity.Corpus

/-! ## Obligations at a store, from `⊢`

The `TestSuite` obligations are derived by the scoped `⊢`
(`Core.Proves`, `docs/intrinsic.md`, W3c): `N.f.proved : ⊢ N.f.problem`, the
program resolved (`Core.Prog`).  Its corollary at the initial storage is
stated over the untyped run of the program's erasure, as every other corpus
row is.  The typed reading accepts a run that diverges or is exhausted (a
push at the bound, decision 15), against which the untyped run may do
anything, so the corollary also asks the typed run from the initial state to
end, and the program to be fresh (what `Core.Prog.run_erase` reads the
erasure by): `Core.scopedRunsB`, which the kernel evaluates
(`decide +kernel`), as `corpus_decide` runs the other rows. -/

namespace Solidity.Core

variable {C : Contract}

/-- No name of `ys` is in scope (`ns`) or in an enclosing frame (`out`). -/
def namesFreshB (out ns ys : List Var) : Bool := ys.all fun y => !ns.contains y && !out.contains y

theorem namesFreshB_sound {out ns ys : List Var} (h : namesFreshB out ns ys = true) :
    ∀ y ∈ ys, y ∉ ns ∧ y ∉ out := by
  intro y hy
  have h' := List.all_eq_true.1 h y hy
  simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at h'
  refine ⟨fun hm => ?_, fun hm => ?_⟩
  · rw [List.contains_iff_mem.2 hm] at h'; cases h'.1
  · rw [List.contains_iff_mem.2 hm] at h'; cases h'.2

mutual

/-- `Stmt.Fresh`, decided. -/
def Stmt.freshB (out : List Var) : {Γ Γ' : Ctx} → List Var → Stmt C Γ Γ' → Bool
  | _, _, ns, .declLocal _ x _ => namesFreshB out ns [x]
  | _, _, ns, .declStorage _ x _ => namesFreshB out ns [x]
  | _, _, ns, .declMem _ x .. => namesFreshB out ns [x]
  | _, _, ns, .ite _ thn els => Prog.freshB out ns thn && Prog.freshB out ns els
  | _, _, ns, .call _ args ret body =>
    decide (ret.names ++ args.names).Nodup && namesFreshB out ns (ret.names ++ args.names) &&
      Arg.separatedFrom [] (args.erase ns) && Prog.freshB (ns ++ out) (ret.names ++ args.names) body
  | _, _, ns, .tryCall _ rets ok err code pnc other =>
    decide rets.names.Nodup && namesFreshB out ns rets.names &&
      Prog.freshB out (rets.names ++ ns) ok && Prog.freshB out ns err &&
      namesFreshB out ns code.names && Prog.freshB out (code.names ++ ns) pnc &&
      Prog.freshB out ns other
  | _, _, ns, .loop _ _ body => Prog.freshB out ns body
  | _, _, ns, .block body => Prog.freshB out ns body
  | _, _, _, .assign .. | _, _, _, .rebind .. | _, _, _, .assignLocal .. | _, _, _, .opAssign ..
  | _, _, _, .incDec .. | _, _, _, .assignIncDec .. | _, _, _, .push .. | _, _, _, .pop ..
  | _, _, _, .transfer .. | _, _, _, .send .. | _, _, _, .rebindMem .. | _, _, _, .assignFromMem ..
  | _, _, _, .assignMem .. | _, _, _, .delete .. | _, _, _, .deleteMem .. | _, _, _, .assignNew ..
  | _, _, _, .require .. | _, _, _, .assert .. | _, _, _, .revert => true

/-- `Prog.Fresh`, decided. -/
def Prog.freshB (out : List Var) : {Γ Γ' : Ctx} → List Var → Prog C Γ Γ' → Bool
  | _, _, _, .nil => true
  | _, _, ns, .cons s P => Stmt.freshB out ns s && Prog.freshB out (s.outNames ns) P

end

mutual

theorem Stmt.fresh_of_freshB (out : List Var) : {Γ Γ' : Ctx} → (ns : List Var) →
    (s : Stmt C Γ Γ') → s.freshB out ns = true → s.Fresh out ns
  | _, _, ns, .declLocal _ x _, h | _, _, ns, .declStorage _ x _, h
  | _, _, ns, .declMem _ x .., h => by
    simp only [Stmt.freshB] at h
    exact namesFreshB_sound h x (List.mem_singleton_self x)
  | _, _, ns, .ite _ thn els, h => by
    simp only [Stmt.freshB, Bool.and_eq_true] at h
    exact ⟨Prog.fresh_of_freshB out ns thn h.1, Prog.fresh_of_freshB out ns els h.2⟩
  | _, _, ns, .call _ args ret body, h => by
    simp only [Stmt.freshB, Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨h.1.1.1, namesFreshB_sound h.1.1.2, h.1.2, Prog.fresh_of_freshB _ _ body h.2⟩
  | _, _, ns, .tryCall _ rets ok err code pnc other, h => by
    simp only [Stmt.freshB, Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨h.1.1.1.1.1.1, namesFreshB_sound h.1.1.1.1.1.2,
      Prog.fresh_of_freshB _ _ ok h.1.1.1.1.2, Prog.fresh_of_freshB _ _ err h.1.1.1.2,
      namesFreshB_sound h.1.1.2, Prog.fresh_of_freshB _ _ pnc h.1.2,
      Prog.fresh_of_freshB _ _ other h.2⟩
  | _, _, ns, .loop _ _ body, h => Prog.fresh_of_freshB out ns body h
  | _, _, ns, .block body, h => Prog.fresh_of_freshB out ns body h
  | _, _, _, .assign .., _ | _, _, _, .rebind .., _ | _, _, _, .assignLocal .., _
  | _, _, _, .opAssign .., _ | _, _, _, .incDec .., _ | _, _, _, .assignIncDec .., _
  | _, _, _, .push .., _ | _, _, _, .pop .., _ | _, _, _, .transfer .., _ | _, _, _, .send .., _
  | _, _, _, .rebindMem .., _ | _, _, _, .assignFromMem .., _ | _, _, _, .assignMem .., _
  | _, _, _, .delete .., _ | _, _, _, .deleteMem .., _ | _, _, _, .assignNew .., _
  | _, _, _, .require .., _ | _, _, _, .assert .., _ | _, _, _, .revert, _ => trivial

theorem Prog.fresh_of_freshB (out : List Var) : {Γ Γ' : Ctx} → (ns : List Var) →
    (P : Prog C Γ Γ') → P.freshB out ns = true → P.Fresh out ns
  | _, _, _, .nil, _ => trivial
  | _, _, ns, .cons s P, h => by
    simp only [Prog.freshB, Bool.and_eq_true] at h
    exact ⟨Stmt.fresh_of_freshB out ns s h.1, Prog.fresh_of_freshB out _ P h.2⟩

end

/-- `TRes.Ends`, decided. -/
def TRes.endsB {α : Type} : TRes α → Bool
  | .error .diverge | .error .exhausted => false
  | _ => true

theorem TRes.ends_of_endsB {α : Type} {t : TRes α} (h : t.endsB = true) : t.Ends := by
  match t, h with
  | .ok _, _ => exact ⟨nofun, nofun⟩
  | .error .revert, _ | .error .panic, _ => exact ⟨nofun, nofun⟩

/-- What a corpus corollary of a scoped obligation asks of its program: it
is fresh, and its typed run from the initial state ends. -/
def scopedRunsB {Γ' : Ctx} (Q : Prog C [] Γ') : Bool :=
  Q.freshB [] [] && (Q.trun (TState.init C)).endsB

/-- **A derived scoped obligation of no parameters holds at the initial
storage**, of the untyped run of its program's erasure, where the program is
fresh and its typed run from there ends (`scopedRunsB`). -/
theorem modal_of_proved {m : Modality} {Γ' : Ctx} {Q : Prog C [] Γ'}
    (h : Proves C .all [] .nil (Problem.fml m [] Q))
    (hw : Solidity.holds C.initState (Solidity.Fml.wt C)) (hc : scopedRunsB Q = true) :
    Solidity.holds C.initState (.modal m (Q.erase []) .tt) := by
  simp only [scopedRunsB, Bool.and_eq_true] at hc
  have hF : Q.Fresh [] [] := Prog.fresh_of_freshB [] [] Q hc.1
  have hX := TRes.ends_of_endsB hc.2
  have he : (TState.init C).erase.erase [] = C.initState := by
    rw [TState.init_erase]; rfl
  have hwt : holds (TState.init C) (Fml.wt C) :=
    (holds_erase_fo (ns := []) (Fml.wt C) (by simp only [Fml.wt, Fml.Plain]) rfl (Agree.nil (TState.init C).erase)).2
      (by rw [show withLocals (TState.init C).erase.glob [] = C.initState by
        rw [TState.init_erase]; rfl]; exact hw)
  have hm : m.afterRunTR (fun _ => True) (Prog.trunFrames (TState.init C) Q .nil) :=
    h.valid (TState.init C) hwt
  have h2 := Prog.run_erase Q hF List.nodup_nil rfl (TState.init C).erase
  rw [he] at h2
  show m.afterRun _ (Solidity.Prog.run C.initState (Q.erase []))
  cases ht : Q.trun (TState.init C) with
  | ok o =>
    rw [Prog.run_of_trun ht] at h2
    cases hr : Solidity.Prog.run C.initState (Q.erase []) with
    | ok _ => exact ⟨by cases m <;> trivial, nofun⟩
    | error _ => rw [hr] at h2; exact h2.elim
  | error e =>
    have hm' : m.afterRunTR (fun _ => True) (.error e : TRes (TState C Γ')) := by
      simpa only [Prog.trunFrames, ht] using hm
    rw [ht] at hX
    cases e with
    | diverge => exact absurd rfl hX.1
    | exhausted => exact absurd rfl hX.2
    | panic => exact absurd rfl hm'.2
    | revert =>
      rw [Prog.run_halt_of_trun (e := .revert) nofun nofun ht] at h2
      cases hr : Solidity.Prog.run C.initState (Q.erase []) with
      | ok _ => rw [hr] at h2; exact h2.elim
      | error e' =>
        rw [hr] at h2
        have h3 : e' = THalt.revert.erase := h2
        subst h3
        cases m with
        | box => exact ⟨trivial, nofun⟩
        | diamond => exact absurd hm'.1 nofun

end Solidity.Core

namespace Solidity.Corpus

open Semantics

/-- solkey's `\[{ f(); }\](true)` at the store `σ`: `σ ⊨ [ P ] true`. -/
abbrev Box {C : Contract} (σ : State) (P : Prog C) : Prop :=
  holds σ (.modal .box P .tt)

/-- A derived diamond obligation with no parameters holds at the initial
storage (`Core.modal_of_proved`). -/
theorem diamond_of_proved {C : Contract} {Γ' : Core.Ctx} {Q : Core.Prog C [] Γ'}
    (h : Core.Proves C .all [] .nil (Core.Problem.fml .diamond [] Q))
    (hw : holds C.initState (Fml.wt C)) (hc : Core.scopedRunsB Q = true) :
    Diamond C.initState (Q.erase []) :=
  Core.modal_of_proved h hw hc

/-- A derived box obligation with no parameters holds at the initial
storage (`Core.modal_of_proved`). -/
theorem box_of_proved {C : Contract} {Γ' : Core.Ctx} {Q : Core.Prog C [] Γ'}
    (h : Core.Proves C .all [] .nil (Core.Problem.fml .box [] Q))
    (hw : holds C.initState (Fml.wt C)) (hc : Core.scopedRunsB Q = true) :
    Box C.initState (Q.erase []) :=
  Core.modal_of_proved h hw hc

/-! A corollary of `Corpus/TestSuite.lean` uses the axioms of its `⊢`
theorem, which `TestSuite/Report.lean`'s pin checks, of `initState_wt`,
pinned there on one corollary, and of these two, through `Proves.valid`. -/

/--
info: 'Solidity.Corpus.diamond_of_proved' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms diamond_of_proved

/--
info: 'Solidity.Corpus.box_of_proved' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms box_of_proved

end Solidity.Corpus
