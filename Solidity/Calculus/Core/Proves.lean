import Solidity.Calculus.Core.Taclet
import Solidity.Calculus.Core.Closable
import Solidity.Calculus.Logic

/-!
# Sequents on scoped formulas: the skeleton

`Logic.lean`'s judgement `Γ ⊢ φ` over the scoped formulas of
`Calculus/Core/Fml.lean` (`docs/intrinsic.md`, M6a): the context is a
telescope (`Hyps C Γ₀ Γ`), each entry read where the ones before it leave,
so an update that declares a local, a `∀` and the hidden binder extend the
scope of what follows them, and the goal is a formula of the last scope.

The rules are stated, one per kind of premise, as `Proves` has them today,
under solkey's names where solkey has the rule:

* `intro` (`impRight`), `allIntro` (`allRight`), `updIntro`, `bindIntro`
  (the hidden binder, Lean only: it puts the local of `T v = e;` in scope);
* `update`, `unfold`, `bind`, `split`, `check`, `done`, `branches`,
  `cases`, `inv`, `inline`: a taclet's premise in front of the rest `ω` and
  the frames `κ` (`Premise.fml`, its parts apart), one goal per conjunct.
  `split` has KeY's two goals, under either modality: the diamond reads
  from states whose `bool` locals hold `bool`s (`State.BoolOK`), where one
  of a branch's conditions holds, so no third goal covers a stuck one;
* `empty` (`emptyModality`): a finished program goes through its frames
  (`Frames.exit`), a scope end a popping update, which `updIntro` takes;
* `closeTrue`, behind a context with no diamond update but scope ends
  (`Hyps.boxOnly`);
* `close`: a leaf whose erasure is valid (`Calculus/Core/CloseErase.lean`),
  as today's `Proves.close`, behind a context with no diamond update.

A program rule fires the rule the strategy fires (`Stmt.step`, one per
statement): its premise is `s.step k m = some p`, which `rfl` proves and
`Taclet.step_eq` gives from a named taclet (`Calculus/Core/Taclet.lean`).
The fresh index `k` is one above every index in the sequent
(`Hyps.fresh`), as `Hyp.fresh` numbers it.  `Hyps.wrap` is written with
`casesOn` (Gate G0, condition 1): the kernel evaluates it when it checks
that index.

Soundness is `Calculus/Core/ProvesSound.lean`.
-/

namespace Solidity.Core

open Solidity (Modality RuleSet)

variable {C : Contract}

/-- The context of a sequent, from the scope `Γ₀` of the whole goal to the
scope `Γ` of its last formula. -/
inductive Hyps (C : Contract) (Γ₀ : Ctx) : Ctx → Type where
  | nil : Hyps C Γ₀ Γ₀
  /-- `a → …` -/
  | pre {Γ : Ctx} (H : Hyps C Γ₀ Γ) (a : Fml C Γ) : Hyps C Γ₀ Γ
  /-- `{U} …`, produced under the modality `m`: its declarations extend
  the scope. -/
  | upd {Γ Δ : Ctx} (H : Hyps C Γ₀ Γ) (m : Modality) (U : Upd C Γ Δ) : Hyps C Γ₀ Δ
  /-- `{havoc} …` -/
  | havoc {Γ : Ctx} (H : Hyps C Γ₀ Γ) : Hyps C Γ₀ Γ
  /-- `∀ p x. …`, KeY's skolem constant for `x`. -/
  | all {Γ : Ctx} (H : Hyps C Γ₀ Γ) (x : Var) (p : PrimTy) : Hyps C Γ₀ (.val p :: Γ)
  /-- The hidden binder: the local `x` a declaration put in scope, any value
  of its type. -/
  | bind {Γ : Ctx} (H : Hyps C Γ₀ Γ) (x : Var) (t : LTy) : Hyps C Γ₀ (t :: Γ)
  /-- `{anon(xs)} …` -/
  | anon {Γ : Ctx} (H : Hyps C Γ₀ Γ) (xs : List ((t : LTy) × Idx Γ t)) : Hyps C Γ₀ Γ

/-- The context put back in front of a formula. -/
def Hyps.wrap {Γ₀ : Ctx} : {Γ : Ctx} → Hyps C Γ₀ Γ → Fml C Γ → Fml C Γ₀
  | _, H, φ => Hyps.casesOn (motive := fun Γ _ => Fml C Γ → Fml C Γ₀) H
      (fun φ => φ)
      (fun H a φ => Hyps.wrap H (.imp a φ))
      (fun H m U φ => Hyps.wrap H (.upd m U φ))
      (fun H φ => Hyps.wrap H (.havoc φ))
      (fun H x p φ => Hyps.wrap H (.all x p φ))
      (fun H x t φ => Hyps.wrap H (.bind x t φ))
      (fun H xs φ => Hyps.wrap H (.anon xs φ)) φ
  termination_by structural _ H => H

/-- The fresh index of a step on the goal `φ`: one above every index in the
sequent. -/
def Hyps.fresh {Γ₀ Γ : Ctx} (H : Hyps C Γ₀ Γ) (φ : Fml C Γ) : Nat := (H.wrap φ).fresh

/-- The update only pops: scope ends, which always terminate. -/
def Upd.popsOnly {Γ : Ctx} : {Δ : Ctx} → Upd C Γ Δ → Bool
  | _, U => Upd.casesOn (motive := fun _ _ => Bool) U true
      (fun _ _ => false) (fun _ _ _ => false) (fun U _ => Upd.popsOnly U)
      (fun U _ => Upd.popsOnly U)
  termination_by structural _ U => U

/-- No update of the context was produced under the diamond, but scope
ends (`Upd.popsOnly`). -/
def Hyps.boxOnly {Γ₀ : Ctx} : {Γ : Ctx} → Hyps C Γ₀ Γ → Bool
  | _, H => Hyps.casesOn (motive := fun _ _ => Bool) H true
      (fun H _ => Hyps.boxOnly H)
      (fun H m U => match m with
        | .diamond => U.popsOnly && Hyps.boxOnly H
        | .box => Hyps.boxOnly H)
      (fun H => Hyps.boxOnly H) (fun H _ _ => Hyps.boxOnly H) (fun H _ _ => Hyps.boxOnly H)
      (fun H _ => Hyps.boxOnly H)
  termination_by structural _ H => H

/-- `{anon(xs)}`, and `{anon(xs)} {havoc}` when the loop's frame writes the
storage too (`Fml.anonHavoc`), joined to the context. -/
def Hyps.anonHavoc {Γ₀ Γ : Ctx} (H : Hyps C Γ₀ Γ) (xs : List ((t : LTy) × Idx Γ t)) (hv : Bool) :
    Hyps C Γ₀ Γ :=
  if hv then (H.anon xs).havoc else H.anon xs

/-- `H ⊢ φ`: the calculus proves `φ` in the context `H` (with `R`, solkey's
rules alone or all of them). -/
inductive Proves (C : Contract) (R : RuleSet) (Γ₀ : Ctx) :
    {Γ : Ctx} → Hyps C Γ₀ Γ → Fml C Γ → Prop where
  /-- `impRight`: the precondition moves into the context. -/
  | intro {Γ : Ctx} {H : Hyps C Γ₀ Γ} {a φ : Fml C Γ} (h : Proves C R Γ₀ (H.pre a) φ) :
      Proves C R Γ₀ H (.imp a φ)
  /-- `allRight`: a quantified local joins the context. -/
  | allIntro {Γ : Ctx} {H : Hyps C Γ₀ Γ} {x : Var} {p : PrimTy} {φ : Fml C (.val p :: Γ)}
      (h : Proves C R Γ₀ (H.all x p) φ) : Proves C R Γ₀ H (.all x p φ)
  /-- An update in front of the formula joins the context. -/
  | updIntro {Γ Δ : Ctx} {H : Hyps C Γ₀ Γ} {m : Modality} {U : Upd C Γ Δ} {φ : Fml C Δ}
      (h : Proves C R Γ₀ (H.upd m U) φ) : Proves C R Γ₀ H (.upd m U φ)
  /-- The hidden binder joins the context (Lean only). -/
  | bindIntro {Γ : Ctx} {H : Hyps C Γ₀ Γ} {x : Var} {t : LTy} {φ : Fml C (t :: Γ)}
      (h : Proves C R Γ₀ (H.bind x t) φ) : Proves C R Γ₀ H (.bind x t φ)
  /-- A taclet that produces an update: the update joins the context, the
  rest of the program goes on. -/
  | update {Γ Γ' Γ₁ Γ₂ : Ctx} {H : Hyps C Γ₀ Γ} {m : Modality} {s : Stmt C Γ Γ'}
      {ω : Prog C Γ' Γ₁} {κ : Frames C Γ₁ Γ₂} {φ : Fml C Γ₂} {U : Upd C Γ Γ'}
      (d : s.step (H.fresh (.modal m (.cons s ω) κ φ)) m = some (.update U))
      (h : Proves C R Γ₀ (H.upd m U) (.modalK m ω κ φ)) :
      Proves C R Γ₀ H (.modal m (.cons s ω) κ φ)
  /-- A taclet that produces statements: they replace the first one, their
  fresh locals popped after them (`pop .capture`). -/
  | unfold {Γ Γ' Γ'' Γ₁ Γ₂ : Ctx} {H : Hyps C Γ₀ Γ} {m : Modality} {s : Stmt C Γ Γ'}
      {ω : Prog C Γ' Γ₁} {κ : Frames C Γ₁ Γ₂} {φ : Fml C Γ₂} {P : Prog C Γ Γ''} {e : Ext Γ' Γ''}
      (d : s.step (H.fresh (.modal m (.cons s ω) κ φ)) m = some (.unfold P e))
      (h : Proves C R Γ₀ H (.modal m P (.pop .capture e (.seq ω κ)) φ)) :
      Proves C R Γ₀ H (.modal m (.cons s ω) κ φ)
  /-- A declaration with its initializer dropped (`localValueDeclInitDrop`):
  the local joins the context, the assignment replaces the declaration. -/
  | bind {Γ Γ' Γ₁ Γ₂ : Ctx} {H : Hyps C Γ₀ Γ} {m : Modality} {s : Stmt C Γ Γ'}
      {ω : Prog C Γ' Γ₁} {κ : Frames C Γ₁ Γ₂} {φ : Fml C Γ₂} {x : Var} {t : LTy}
      {P : Prog C (t :: Γ) Γ'}
      (d : s.step (H.fresh (.modal m (.cons s ω) κ φ)) m = some (.bind x t P))
      (h : Proves C R Γ₀ (H.bind x t) (.modal m P (.seq ω κ) φ)) :
      Proves C R Γ₀ H (.modal m (.cons s ω) κ φ)
  /-- A taclet that branches: two goals, KeY's, each branch a block ended
  as the premise says (`}` for an `if`). -/
  | split {Γ Γ₁ Γ₂ Δ₁ Δ₂ : Ctx} {H : Hyps C Γ₀ Γ} {m : Modality} {s : Stmt C Γ Γ}
      {ω : Prog C Γ Γ₁} {κ : Frames C Γ₁ Γ₂} {φ : Fml C Γ₂} {b : BlockKind} {c c' : Fml C Γ}
      {P : Prog C Γ Δ₁} {Q : Prog C Γ Δ₂}
      (d : s.step (H.fresh (.modal m (.cons s ω) κ φ)) m = some (.split b c c' P Q))
      (thn : Proves C R Γ₀ (H.pre c) (.modalK m P (.pop b P.ext (.seq ω κ)) φ))
      (els : Proves C R Γ₀ (H.pre c') (.modalK m Q (.pop b Q.ext (.seq ω κ)) φ)) :
      Proves C R Γ₀ H (.modal m (.cons s ω) κ φ)
  /-- A taclet that checks (`assertSimple`): the goal with the condition
  assumed ("Holds"), and the condition ("Violated"). -/
  | check {Γ Γ₁ Γ₂ : Ctx} {H : Hyps C Γ₀ Γ} {m : Modality} {s : Stmt C Γ Γ}
      {ω : Prog C Γ Γ₁} {κ : Frames C Γ₁ Γ₂} {φ : Fml C Γ₂} {c : Fml C Γ}
      (d : s.step (H.fresh (.modal m (.cons s ω) κ φ)) m = some (.check c))
      (thn : Proves C R Γ₀ (H.pre c) (.modalK m ω κ φ)) (els : Proves C R Γ₀ H c) :
      Proves C R Γ₀ H (.modal m (.cons s ω) κ φ)
  /-- A taclet that closes the modality (`revertBox`, `revertDiamond`). -/
  | done {Γ Γ' Γ₁ Γ₂ : Ctx} {H : Hyps C Γ₀ Γ} {m : Modality} {s : Stmt C Γ Γ'}
      {ω : Prog C Γ' Γ₁} {κ : Frames C Γ₁ Γ₂} {φ : Fml C Γ₂} {b : Bool}
      (d : s.step (H.fresh (.modal m (.cons s ω) κ φ)) m = some (.done b))
      (h : Proves C R Γ₀ H (if b then .tt else .ff)) :
      Proves C R Γ₀ H (.modal m (.cons s ω) κ φ)
  /-- A taclet with a goal per way an external call may end
  (`tryCallNoCallbackBox`): each clause's block in the statement's place,
  for every value of the locals its outcome binds, its scope ended (`}`).
  There is at least one clause: a rule with no goal would prove its
  statement behind any context. -/
  | branches {Γ Γ₁ Γ₂ : Ctx} {H : Hyps C Γ₀ Γ} {m : Modality} {s : Stmt C Γ Γ}
      {ω : Prog C Γ Γ₁} {κ : Frames C Γ₁ Γ₂} {φ : Fml C Γ₂} {bs : List (Branch C Γ)}
      (d : s.step (H.fresh (.modal m (.cons s ω) κ φ)) m = some (.branches bs))
      (hne : bs.isEmpty = false)
      (h : ∀ b ∈ bs, Proves C R Γ₀ H
        (b.bs.all (.modalK m b.P (.pop .block ((Ext.append Γ b.ρ).trans b.P.ext) (.seq ω κ)) φ))) :
      Proves C R Γ₀ H (.modal m (.cons s ω) κ φ)
  /-- A taclet with labelled goals (`sendNoCallbackBox`): each formula, then
  the rest after each update, one per way the statement may end. -/
  | cases {Γ Γ₁ Γ₂ : Ctx} {H : Hyps C Γ₀ Γ} {m : Modality} {s : Stmt C Γ Γ}
      {ω : Prog C Γ Γ₁} {κ : Frames C Γ₁ Γ₂} {φ : Fml C Γ₂} {fs : List (Fml C Γ)}
      {us : List (Upd C Γ Γ)}
      (d : s.step (H.fresh (.modal m (.cons s ω) κ φ)) m = some (.cases fs us))
      (hne : (fs.isEmpty && us.isEmpty) = false)
      (fml : ∀ f ∈ fs, Proves C R Γ₀ H f)
      (upd : ∀ U ∈ us, Proves C R Γ₀ (H.upd m U) (.modalK m ω κ φ)) :
      Proves C R Γ₀ H (.modal m (.cons s ω) κ φ)
  /-- A loop's invariant (`whileInvariantBox`, `whileInvariantDiamond`): the
  invariant now ("invariant initially valid"), and past the frame's
  anonymising update, the invariant and the condition's update, the body to
  its postcondition where the condition holds ("body preserves
  invariant"), the rest where it does not ("use case"). -/
  | inv {Γ Γ₁ Γ₂ Δ₀ Δ Γ₃ : Ctx} {H : Hyps C Γ₀ Γ} {m : Modality} {s : Stmt C Γ Γ}
      {ω : Prog C Γ Γ₁} {κ : Frames C Γ₁ Γ₂} {φ : Fml C Γ₂} {I : Fml C Γ}
      {xs : List ((t : LTy) × Idx Γ t)} {hv : Bool} {U : Upd C Γ Δ} {c c' : Fml C Δ}
      {hu : Ext Γ Δ₀} {hb : Ext Δ₀ Δ} {P : Prog C Δ₀ Γ₃} {post : Fml C Δ₀}
      (d : s.step (H.fresh (.modal m (.cons s ω) κ φ)) m =
        some (.inv I xs hv U c c' hu hb P post))
      (init : Proves C R Γ₀ H I)
      (thn : Proves C R Γ₀ ((((H.anonHavoc xs hv).pre I).upd m U).pre c)
        (.upd m (Upd.nil.pop hb) (.modalK m P (.pop .block P.ext .nil) post)))
      (els : Proves C R Γ₀ ((((H.anonHavoc xs hv).pre I).upd m U).pre c')
        (.upd m (Upd.nil.pop (hu.trans hb)) (.modalK m ω κ φ))) :
      Proves C R Γ₀ H (.modal m (.cons s ω) κ φ)
  /-- A taclet that produces a block whose end drops a frame from under the
  locals it keeps (`expand_function_body` of a call that leaves its return
  variables): the block replaces the statement. -/
  | inline {Γ Γ' Γ'' Γ₁ Γ₂ : Ctx} {H : Hyps C Γ₀ Γ} {m : Modality} {s : Stmt C Γ Γ'}
      {ω : Prog C Γ' Γ₁} {κ : Frames C Γ₁ Γ₂} {φ : Fml C Γ₂} {P : Prog C Γ Γ''} {e : Thin Γ' Γ''}
      (d : s.step (H.fresh (.modal m (.cons s ω) κ φ)) m = some (.inline P e))
      (h : Proves C R Γ₀ H (.modal m P (.drop e (.seq ω κ)) φ)) :
      Proves C R Γ₀ H (.modal m (.cons s ω) κ φ)
  /-- `emptyModality`: a finished program goes through its frames, the rest
  of the program next, a scope end a popping update. -/
  | empty {Γ Γ₂ : Ctx} {H : Hyps C Γ₀ Γ} {m : Modality} {κ : Frames C Γ Γ₂} {φ : Fml C Γ₂}
      (h : Proves C R Γ₀ H (κ.exit m φ)) : Proves C R Γ₀ H (.modal m .nil κ φ)
  /-- `closeTrue`, behind a context with no diamond update. -/
  | closeTrue {Γ : Ctx} {H : Hyps C Γ₀ Γ} (h : H.boxOnly = true) : Proves C R Γ₀ H .tt
  /-- Leave the calculus: the sequent, its context in front, erased
  (`Fml.erase`, the outer locals named `ns`) and proved in the logic, where
  its erasure gives it, with no modality left (`Fml.closableB`: `Fml.Closable`
  and `Fml.Leaf`, as today's `close` asks `modalFree`).  The kernel decides
  both side conditions (`rfl`, `decide`).  Box contexts only: over M3's
  states the erasure's diamond does not give `State.BoolOK` of the state it
  ends in, so a leaf behind a diamond update closes only over the typed
  state (`Fml.TClosable`, `Calculus/Core/TCloseErase.lean`), at the flip. -/
  | close {Γ : Ctx} {H : Hyps C Γ₀ Γ} {φ : Fml C Γ} (ns : List Var)
      (hlen : ns.length = Γ₀.length) (hnd : ns.Nodup)
      (h : Solidity.Valid ((H.wrap φ).erase ns))
      (hc : (H.wrap φ).closableB ns = true := by first | rfl | decide)
      (hB : Solidity.Avoids (H.wrap φ).bindNames ns := by decide) : Proves C R Γ₀ H φ

/-! ## A derivation

`[ if (b) { } else { } ] true`, `b` a `bool` local: `ifElseSplit`, then in
each goal the block's end (an update that pops nothing, taken into the
context) and `closeTrue`. -/

example : Proves StandardExample .all [.val .bool] .nil
    (.modal .box (.cons (.ite (.simple (.local .here)) .nil .nil) .nil) .nil .tt) :=
  .split (Taclet.step_eq .ifElseSplit) (.updIntro (.closeTrue rfl)) (.updIntro (.closeTrue rfl))

/-- The diamond twin: a scope end pops, so `closeTrue` still fires in the two
branches, and there is no third goal. -/
example : Proves StandardExample .all [.val .bool] .nil
    (.modal .diamond (.cons (.ite (.simple (.local .here)) .nil .nil) .nil) .nil .tt) :=
  .split rfl (.updIntro (.closeTrue rfl)) (.updIntro (.closeTrue rfl))

/-- `close` on a leaf behind a box update and a hidden binder,
`x = x` after `x := 1` with `x` any `uint`: the kernel decides
`Fml.closableB` and the binder's `Avoids` (the defaults), and the erasure
`{x := 1} x = x` is valid by `rfl`. -/
example : Proves StandardExample .all [] (((Hyps.nil.bind (.user "x") (.val .uint)).upd .box
      (Upd.nil.snoc (.local .here (.val (.app0 (.lit (.int 1))))))))
    (.eq (.pvV .here) (.pvV .here)) :=
  .close [] rfl List.nodup_nil fun _ _ => rfl

end Solidity.Core
