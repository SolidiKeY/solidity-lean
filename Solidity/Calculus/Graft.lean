import Solidity.Calculus.Logic
import Solidity.Calculus.FirstOrder
import Solidity.Semantics.StateErase
import Solidity.Calculus.StateFacts

/-!
# One update for two: `sequentialToParallel`'s side conditions on scoped updates

KeY's `sequentialToParallel2` (`{u}{u2}φ ⇝ {u ‖ {u}u2}φ`) on the scoped
updates of `Calculus/Fml.lean`: what the sequent's `merge`
(`Calculus/Proves.lean`) and the chains' `~[sequentialToParallel]~>`
(`Calculus/Merge.lean`) compute, and why it is sound.

`{U}{V}φ` becomes `{W}φ`, `W` the elements of `U` and then those of `V`, each
right-hand side of `V` read in `U`'s state (`Upd.seqPar`): its locals
replaced by what `U` leaves in them (`Upd.held`: a local of the state `U` is
applied in, or the right-hand side `U` last wrote to it), and `storage` by
the storage `U` last wrote, where `U` writes no other global part
(`Upd.lastSt`, solkey's `{storage := s}{x := find(storage, p)}` ⇝
`{storage := s ‖ x := find(s, p)}`).  Any other symbol of `V` that reads
the global part (`memory`, the ledger, a bounds check against the storage)
is read the same only where `U` writes no global part (`Upd.envOnly`); any
other merge is refused (`none`), never wrong.

**Typed sorts** (W9.8.3c).  A term's value depends on the heap typing of the
state it is read in only at the sort `mem` (a `Grown` heap), so a term of
`V` read in the state `U` lands on and its substitute read in the state
before are compared up to that typing (`Srt.SameO`: a memory by its grown
heap, any other sort equal).  A symbol that touches the memory counts as
reading the global part (`Op1.globFree` …: `alloc`, `addM`, `read`, `mlen`,
`copyMem`, `iread`, `copy`, `copySt`, `write`), as every memory term starts
at `memory`, which does.

**Soundness reads `holds`' typed clause** (`Upd.afterT`, `Calculus/Lands.lean`):
`V` substituted (`Tm.substH`) reads in the state before what `V` reads in
every typed state `U` lands on (`Tm.eval_substH`), so the grafted update
computes `V`'s global part there and leaves `V`'s locals
(`Upd.globT_graft`, `Upd.held_graft`), and gives `U` then `V`
(`holds_upd_graft`).

An update moves under a hidden binder when it declares nothing
(`Upd.lift?`), the binder not at a memory type or the update allocating
nothing (`LTy.notMem`, `Upd.keepsNext`): `Fml.upd_bind_of_lift`.

The last box update's right-hand sides rewritten by a term taclet
(`Upd.rwC`, `Proves.updRw`) is `Calculus/SeqRewrite.lean`'s.

The functions use `match` on the indexed families, against Gate G0's first
condition: an exemption (`docs/intrinsic.md`, W3b's merge, extended to the
sequent's update rules in W3c `tactics`, both timed), since they run once a
rule and not once a step.
-/

namespace Solidity

open Solidity (Srt Op0 Op1 Op2 Op3 Modality)

variable {C : Contract}

/-! ## One value over two heap typings -/

/-- A value of a sort with its heap typing forgotten: a memory as the heap
it grew to, any other sort as it is (its values do not depend on the heap
typing). -/
@[reducible] def Srt.DenF (C : Contract) : Srt → Type
  | .mem => (H' : HTy) × Heap H'
  | .val p => p.Denote
  | .path T => SRef C T
  | .st => Storage C
  | .sv T => SVal T
  | .ident _ => Nat
  | .addr T => MAddrT T
  | .mv T => MvT T
  | .sts s => Storage (Contract.ofStruct s)
  | .spath s T => SRef (Contract.ofStruct s) T

/-- The heap typing forgotten. -/
def Srt.forget {H : HTy} : (k : Srt) → k.Den C H → k.DenF C
  | .mem, m => ⟨m.H', m.heap⟩
  | .val _, x => x
  | .path _, x => x
  | .st, x => x
  | .sv _, x => x
  | .ident _, x => x
  | .addr _, x => x
  | .mv _, x => x
  | .sts _, x => x
  | .spath _ _, x => x

/-- Two readings of the sort `k`, over two heap typings, are one. -/
def Srt.SameO {H₀ H₁ : HTy} (k : Srt) (x : Option (k.Den C H₀)) (y : Option (k.Den C H₁)) :
    Prop :=
  x.map (Srt.forget k) = y.map (Srt.forget k)

theorem Srt.forget_injective {H : HTy} : (k : Srt) → {x y : k.Den C H} →
    Srt.forget k x = Srt.forget k y → x = y
  | .mem, x, y, h => by
    rcases x with ⟨ex, hx, ⟨⟩⟩
    rcases y with ⟨ey, hy, ⟨⟩⟩
    simp only [Srt.forget, Sigma.mk.injEq] at h
    obtain ⟨rfl, h⟩ := h
    cases h
    rfl
  | .val _, _, _, h | .path _, _, _, h | .st, _, _, h | .sv _, _, _, h | .ident _, _, _, h
  | .addr _, _, _, h | .mv _, _, _, h | .sts _, _, _, h | .spath _ _, _, _, h => h

/-- Over one heap typing, the same reading is equal. -/
theorem Srt.SameO.eq {H : HTy} {k : Srt} {x y : Option (k.Den C H)} (h : Srt.SameO k x y) :
    x = y := by
  cases x <;> cases y
  · rfl
  · exact Option.noConfusion h
  · exact Option.noConfusion h
  · exact congrArg some (Srt.forget_injective k (Option.some.inj h))

theorem Srt.SameO.refl {H : HTy} (k : Srt) (x : Option (k.Den C H)) : Srt.SameO k x x := rfl

/-- `Srt.SameO k x y` at a sort whose values do not depend on the heap
typing: `y` rewritten to `x`. -/
local macro "same_eq " h:ident x:ident y:ident : tactic =>
  `(tactic| (cases $x:ident <;> cases $y:ident <;>
      first | rfl | exact Option.noConfusion $h | exact congrArg some (Option.some.inj $h)))

local macro "same_subst " h:ident x:ident y:ident : tactic =>
  `(tactic| (have hxy : $x = $y := (by same_eq $h $x $y); rw [← hxy]; clear hxy))

theorem Srt.sameO_val {H₀ H₁ : HTy} {p : PrimTy} {x : Option ((Srt.val p).Den C H₀)}
    {y : Option ((Srt.val p).Den C H₁)} : Srt.SameO (.val p) x y ↔ x = y :=
  ⟨fun h => by
    cases x <;> cases y <;>
      first | rfl | exact Option.noConfusion h | exact congrArg some (Option.some.inj h),
   fun h => by rw [h]; rfl⟩

theorem Srt.sameO_path {H₀ H₁ : HTy} {T : Ty} {x : Option ((Srt.path T).Den C H₀)}
    {y : Option ((Srt.path T).Den C H₁)} : Srt.SameO (.path T) x y ↔ x = y :=
  ⟨fun h => by
    cases x <;> cases y <;>
      first | rfl | exact Option.noConfusion h | exact congrArg some (Option.some.inj h),
   fun h => by rw [h]; rfl⟩

theorem Srt.sameO_st {H₀ H₁ : HTy} {x : Option (Srt.st.Den C H₀)}
    {y : Option (Srt.st.Den C H₁)} : Srt.SameO .st x y ↔ x = y :=
  ⟨fun h => by
    cases x <;> cases y <;>
      first | rfl | exact Option.noConfusion h | exact congrArg some (Option.some.inj h),
   fun h => by rw [h]; rfl⟩

theorem Srt.sameO_ident {H₀ H₁ : HTy} {R : RefTy} {x : Option ((Srt.ident R).Den C H₀)}
    {y : Option ((Srt.ident R).Den C H₁)} : Srt.SameO (.ident R) x y ↔ x = y :=
  ⟨fun h => by
    cases x <;> cases y <;>
      first | rfl | exact Option.noConfusion h | exact congrArg some (Option.some.inj h),
   fun h => by rw [h]; rfl⟩

/-! ## Symbols that read no global part -/

/-- A constant that reads nothing of the state. -/
def _root_.Solidity.Op0.globFree {s : Srt} : Op0 C s → Bool
  | .lit _ | .root .. | .mtSt | .member .. => true
  | _ => false

/-- A unary symbol that reads nothing of the state but its argument, and
touches no memory. -/
def _root_.Solidity.Op1.globFree {a s : Srt} : Op1 C a s → Bool
  | .net | .next | .alloc .. | .addM .. => false
  | _ => true

/-- A binary symbol that reads nothing of the state but its arguments, and
touches no memory. -/
def _root_.Solidity.Op2.globFree {a b s : Srt} : Op2 C a b s → Bool
  | .at _ | .read | .mlen | .copyMem | .iread | .copy _ | .copySt _ => false
  | _ => true

/-- A ternary symbol that touches no memory. -/
def _root_.Solidity.Op3.globFree {a b c s : Srt} : Op3 C a b c s → Bool
  | .write => false
  | _ => true

section EvalSame

variable {g₀ g₁ : State C []}

theorem _root_.Solidity.Op0.eval_same {s : Srt} (o : Op0 C s)
    (hc : g₀ = g₁ ∨ o.globFree = true) : Srt.SameO s (o.eval g₀) (o.eval g₁) := by
  rcases hc with rfl | hf
  · exact Srt.SameO.refl _ _
  · cases o <;> first | exact absurd hf Bool.false_ne_true | rfl

theorem _root_.Solidity.Op1.eval_same {a s : Srt} (o : Op1 C a s)
    (hc : g₀ = g₁ ∨ o.globFree = true) {x : Option (a.Den C g₀.H)} {y : Option (a.Den C g₁.H)}
    (h : Srt.SameO a x y) : Srt.SameO s (o.eval g₀ x) (o.eval g₁ y) := by
  rcases hc with rfl | hf
  · rw [Srt.SameO.eq h]; exact Srt.SameO.refl _ _
  · cases o <;>
      first
      | exact absurd hf Bool.false_ne_true
      | (same_subst h x y; rfl)

theorem _root_.Solidity.Op2.eval_same {a b s : Srt} (o : Op2 C a b s)
    (hc : g₀ = g₁ ∨ o.globFree = true) {x : Option (a.Den C g₀.H)} {x' : Option (a.Den C g₁.H)}
    {y : Option (b.Den C g₀.H)} {y' : Option (b.Den C g₁.H)}
    (hx : Srt.SameO a x x') (hy : Srt.SameO b y y') :
    Srt.SameO s (o.eval g₀ x y) (o.eval g₁ x' y') := by
  rcases hc with rfl | hf
  · rw [Srt.SameO.eq hx, Srt.SameO.eq hy]; exact Srt.SameO.refl _ _
  · cases o <;>
      first
      | exact absurd hf Bool.false_ne_true
      | (same_subst hx x x'; same_subst hy y y'; rfl)

theorem _root_.Solidity.Op3.eval_same {a b c s : Srt} (o : Op3 C a b c s)
    (hc : g₀ = g₁ ∨ o.globFree = true) {x : Option (a.Den C g₀.H)} {x' : Option (a.Den C g₁.H)}
    {y : Option (b.Den C g₀.H)} {y' : Option (b.Den C g₁.H)}
    {z : Option (c.Den C g₀.H)} {z' : Option (c.Den C g₁.H)}
    (hx : Srt.SameO a x x') (hy : Srt.SameO b y y') (hz : Srt.SameO c z z') :
    Srt.SameO s (o.eval g₀ x y z) (o.eval g₁ x' y' z') := by
  rcases hc with rfl | hf
  · rw [Srt.SameO.eq hx, Srt.SameO.eq hy, Srt.SameO.eq hz]; exact Srt.SameO.refl _ _
  · cases o <;>
      first
      | exact absurd hf Bool.false_ne_true
      | (same_subst hx x x'; same_subst hy y y'; same_subst hz z z'; rfl)

end EvalSame

/-- An update that writes locals only: the global part of the state it is
applied in is the one it leaves. -/
def Upd.envOnly {Γ : Ctx} : {Δ : Ctx} → Upd C Γ Δ → Bool
  | _, .nil => true
  | _, .snoc U (.local _ _) => Upd.envOnly U
  | _, .snoc _ _ => false
  | _, .decl U _ _ => Upd.envOnly U
  | _, .pop U _ | _, .drop U _ => Upd.envOnly U

/-! ## Reading in the state before -/

/-- `storage` read before an update that last wrote the storage `st` (and no
other global part): `st` itself. -/
def Tm.storageAs {Γ : Ctx} (st : Option (Tm C Γ .st)) : {k : Srt} → Op0 C k → Option (Tm C Γ k)
  | _, .storage => st
  | _, _ => none

section Subst

variable {Γ Δ : Ctx} (s : Subst C Γ Δ) (g : Bool) (st : Option (Tm C Γ .st))

/-- A term of `Δ` read in `Γ`: its locals replaced by what they hold; a
symbol that reads the global part only where `g` (the update wrote none). -/
def Tm.substH : {k : Srt} → Tm C Δ k → Option (Tm C Γ k)
  | _, .pvV i => match s i with
    | .pos j => some (.pvV j)
    | .rhs (.val t) => some t
  | _, .pvP i => match s i with
    | .pos j => some (.pvP j)
    | .rhs (.path p) => some p
    | .rhs .unset => none
  | _, .pvS i => match s i with
    | .pos j => some (.pvS j)
    | .rhs _ => none
  | _, .pvI i => match s i with
    | .pos j => some (.pvI j)
    | .rhs (.mref t) => some t
  | _, .netOf i a => match s i with
    | .pos j => (Tm.substH a).map (.netOf j)
    | .rhs _ => none
  | _, .app0 o => if g || o.globFree then some (.app0 o) else Tm.storageAs st o
  | _, .app1 o x => if g || o.globFree then (Tm.substH x).map (.app1 o) else none
  | _, .app2 o x y =>
    if g || o.globFree then do pure (.app2 o (← Tm.substH x) (← Tm.substH y)) else none
  | _, .app3 o x y z =>
    if g || o.globFree then
      do pure (.app3 o (← Tm.substH x) (← Tm.substH y) (← Tm.substH z))
    else none

/-- A right-hand side of `Δ` read in `Γ`. -/
def Rhs.substH : {t : LTy} → Rhs C Δ t → Option (Rhs C Γ t)
  | _, .val t => (t.substH s g st).map .val
  | _, .path p => (p.substH s g st).map .path
  | _, .unset => some .unset
  | _, .mref i => (i.substH s g st).map .mref
  | _, .store x => (x.substH s g st).map .store
  | _, .saveNet => if g then some .saveNet else none
  | _, .saveNetMt => some .saveNetMt

/-- An element whose right-hand sides are read in `Δ`, read in `Γ`. -/
def UpdElem.substH {Ε : Ctx} : UpdElem C Δ Ε → Option (UpdElem C Γ Ε)
  | .local i r => (r.substH s g st).map (.local i)
  | .storage x => (x.substH s g st).map .storage
  | .memory m => (m.substH s g st).map .memory
  | .selfBalance op a => if g then (a.substH s g st).map (.selfBalance op) else none
  | .net r op a => do pure (.net (← r.substH s g st) op (← a.substH s g st))
  | .pay r a => if g then do pure (.pay (← r.substH s g st) (← a.substH s g st)) else none
  | .netMt r a => do pure (.netMt (← r.substH s g st) (← a.substH s g st))
  | .setBalance a => (a.substH s g st).map .setBalance

end Subst

/-- `V` applied after `U`, as one update from `U`'s state: `U`'s elements,
then `V`'s, each read in `U`'s state (`s`, `g`: `U.held`, `U.envOnly`). -/
def Upd.graft {Γ Δ₁ : Ctx} (U : Upd C Γ Δ₁) (s : Subst C Γ Δ₁) (g : Bool)
    (st : Option (Tm C Γ .st)) :
    {Δ₂ : Ctx} → Upd C Δ₁ Δ₂ → Option (Upd C Γ Δ₂)
  | _, .nil => some U
  | _, .snoc V e => do pure (.snoc (← Upd.graft U s g st V) (← e.substH s g st))
  | _, .decl V x r => do pure (.decl (← Upd.graft U s g st V) x (← r.substH s g st))
  | _, .pop V h => (Upd.graft U s g st V).map (.pop · h)
  | _, .drop V h => (Upd.graft U s g st V).map (.drop · h)


/-! ## The merge is sound, on the typed state

`V` read in a typed state `U` lands on is `V` substituted (`Tm.substH`),
read in the state before: what `U` leaves in a local is what `Upd.held`
says (`Upd.Lands`), and the global part only where `U` writes none
(`Upd.envOnly_globT`). -/

section SoundT

variable {Γ : Ctx}

/-- An update of locals only leaves the global part it is applied in. -/
theorem Upd.envOnly_globT {σ₀ : State C Γ} : {Δ : Ctx} → (U : Upd C Γ Δ) → U.envOnly = true →
    {g : GlobT C σ₀.H} → U.globT σ₀ = some g → g = σ₀.globG
  | _, .nil, _, _, h => (Option.some.inj h).symm
  | _, .snoc U e, hU, g, h => by
    change (U.globT σ₀).bind (e.globT σ₀) = some g at h
    rw [Option.bind_eq_some_iff] at h
    obtain ⟨g', hg', h⟩ := h
    cases e with
    | «local» k r =>
      rw [UpdElem.globT_eq_globTM] at h
      simp only [UpdElem.globTM, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨_, _, rfl⟩ := h
      exact Upd.envOnly_globT U hU hg'
    | _ => exact absurd hU Bool.false_ne_true
  | _, .decl U _ r, hU, g, h => by
    change (U.globT σ₀).bind (fun g => (r.eval σ₀).bind fun _ => some g) = some g at h
    simp only [Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨g', hg', _, _, rfl⟩ := h
    exact Upd.envOnly_globT U hU hg'
  | _, .pop U _, hU, _, h => Upd.envOnly_globT U hU h
  | _, .drop U _, hU, _, h => Upd.envOnly_globT U hU h

variable {Δ : Ctx} {σ₀ : State C Γ} {σ₁ : State C Δ}
variable {U : Upd C Γ Δ} {g : GlobT C σ₀.H} {st : Option (Tm C Γ .st)}

/-- Where `U` lands, a global part it leaves unwritten is the one before. -/
theorem Upd.Lands.glob_of_envOnly (hL : U.Lands σ₀ g σ₁) (h : U.envOnly = true) :
    σ₁.glob = σ₀.glob :=
  hL.2.1.trans (congrArg Subtype.val (Upd.envOnly_globT U h hL.1))

/-- Where a symbol reads the global part, the update wrote none. -/
theorem Upd.Lands.glob_or (hL : U.Lands σ₀ g σ₁) {b : Bool} (hc : (U.envOnly || b) = true) :
    σ₀.glob = σ₁.glob ∨ b = true := by
  rcases Bool.or_eq_true_iff.mp hc with hg | hb
  · exact .inl (hL.glob_of_envOnly hg).symm
  · exact .inr hb

/-- **A term read in the state before is the term read in every typed
state the update lands on**, up to the heap typing of a memory. -/
theorem Tm.eval_substH (hL : U.Lands σ₀ g σ₁)
    (hst : ∀ x, st = some x → x.eval σ₀ = some σ₁.storage) :
    {k : Srt} → (t : Tm C Δ k) → {t' : Tm C Γ k} → t.substH U.held U.envOnly st = some t' →
      Srt.SameO k (t'.eval σ₀) (t.eval σ₁)
  | _, .pvV i, t', h => by
    have hx := hL.2.2 i
    have h : (match U.held i with
        | .pos j => some (Tm.pvV j) | .rhs (.val t) => some t) = some t' := h
    generalize U.held i = x at h hx
    rw [Srt.sameO_val]
    match x, hx, h with
    | .pos j, hx, h =>
      cases h
      have hx : TEnv.get i σ₁.env = TEnv.get j σ₀.env := hx
      show some (TEnv.get j σ₀.env) = some (TEnv.get i σ₁.env)
      rw [hx]
    | .rhs (.val t), hx, h =>
      cases h
      exact hx
  | _, .pvP i, t', h => by
    have hx := hL.2.2 i
    have h : (match U.held i with
        | .pos j => some (Tm.pvP j) | .rhs (.path p) => some p | .rhs .unset => none) =
          some t' := h
    generalize U.held i = x at h hx
    rw [Srt.sameO_path]
    match x, hx, h with
    | .pos j, hx, h =>
      cases h
      have hx : TEnv.get i σ₁.env = TEnv.get j σ₀.env := hx
      show TEnv.get j σ₀.env = TEnv.get i σ₁.env
      rw [hx]
    | .rhs (.path p), hx, h =>
      cases h
      have hx : (t'.eval σ₀).bind (fun r => some (some r)) = some (TEnv.get i σ₁.env) := hx
      show t'.eval σ₀ = TEnv.get i σ₁.env
      cases hp : t'.eval σ₀ with
      | none => rw [hp] at hx; cases hx
      | some q =>
        rw [hp] at hx
        exact (Option.some.inj hx)
  | _, .pvS i, t', h => by
    have hx := hL.2.2 i
    have h : (match U.held i with
        | .pos j => some (Tm.pvS j) | .rhs _ => none) = some t' := h
    generalize U.held i = x at h hx
    rw [Srt.sameO_st]
    match x, hx, h with
    | .pos j, hx, h =>
      cases h
      have hx : TEnv.get i σ₁.env = TEnv.get j σ₀.env := hx
      show some (TEnv.get j σ₀.env) = some (TEnv.get i σ₁.env)
      rw [hx]
    | .rhs _, _, h => cases h
  | _, .pvI i, t', h => by
    have hx := hL.2.2 i
    have h : (match U.held i with
        | .pos j => some (Tm.pvI j) | .rhs (.mref t) => some t) = some t' := h
    generalize U.held i = x at h hx
    rw [Srt.sameO_ident]
    match x, hx, h with
    | .pos j, hx, h =>
      cases h
      exact hx.symm
    | .rhs (.mref t), hx, h =>
      cases h
      have hx : (t'.eval σ₀).bind (fun id => some (some id)) = some (σ₁.getV i) := hx
      show t'.eval σ₀ = σ₁.getV i
      cases hp : t'.eval σ₀ with
      | none => rw [hp] at hx; cases hx
      | some q =>
        rw [hp] at hx
        exact (Option.some.inj hx)
  | _, .netOf i a, t', h => by
    have hx := hL.2.2 i
    have h : (match U.held i with
        | .pos j => (a.substH U.held U.envOnly st).map (Tm.netOf j) | .rhs _ => none) =
          some t' := h
    generalize U.held i = x at h hx
    rw [Srt.sameO_val]
    match x, hx, h with
    | .rhs _, _, h => cases h
    | .pos j, hx, h =>
      obtain ⟨a', ha, rfl⟩ := Option.map_eq_some_iff.1 h
      have hx : TEnv.get i σ₁.env = TEnv.get j σ₀.env := hx
      have ha' : a'.eval σ₀ = a.eval σ₁ := Srt.sameO_val.1 (Tm.eval_substH hL hst a ha)
      show (a'.eval σ₀).bind _ = (a.eval σ₁).bind _
      rw [ha', hx]
  | _, .app0 o, t', h => by
    simp only [Tm.substH] at h
    split at h
    · rename_i hc
      cases h
      exact Op0.eval_same o (hL.glob_or hc)
    · revert h
      cases o with
      | storage =>
        intro h
        rw [Srt.sameO_st]
        exact hst t' h
      | _ => exact fun h => nomatch h
  | _, .app1 o x, t', h => by
    simp only [Tm.substH] at h
    split at h
    · rename_i hc
      obtain ⟨x', hx, rfl⟩ := Option.map_eq_some_iff.1 h
      exact Op1.eval_same o (hL.glob_or hc) (Tm.eval_substH hL hst x hx)
    · cases h
  | _, .app2 o x y, t', h => by
    simp only [Tm.substH] at h
    split at h
    · rename_i hc
      obtain ⟨x', hx, h⟩ := Option.bind_eq_some_iff.1 h
      obtain ⟨y', hy, h⟩ := Option.bind_eq_some_iff.1 h
      cases h
      exact Op2.eval_same o (hL.glob_or hc) (Tm.eval_substH hL hst x hx)
        (Tm.eval_substH hL hst y hy)
    · cases h
  | _, .app3 o x y z, t', h => by
    simp only [Tm.substH] at h
    split at h
    · rename_i hc
      obtain ⟨x', hx, h⟩ := Option.bind_eq_some_iff.1 h
      obtain ⟨y', hy, h⟩ := Option.bind_eq_some_iff.1 h
      obtain ⟨z', hz, h⟩ := Option.bind_eq_some_iff.1 h
      cases h
      exact Op3.eval_same o (hL.glob_or hc) (Tm.eval_substH hL hst x hx)
        (Tm.eval_substH hL hst y hy) (Tm.eval_substH hL hst z hz)
    · cases h

theorem Rhs.eval_substH (hL : U.Lands σ₀ g σ₁)
    (hst : ∀ x, st = some x → x.eval σ₀ = some σ₁.storage) :
    {t : LTy} → (r : Rhs C Δ t) → {r' : Rhs C Γ t} → r.substH U.held U.envOnly st = some r' →
      r'.eval σ₀ = r.eval σ₁
  | _, .val t, r', h => by
    obtain ⟨t', ht, rfl⟩ := Option.map_eq_some_iff.1 h
    exact Srt.sameO_val.1 (Tm.eval_substH hL hst t ht)
  | _, .path p, r', h => by
    obtain ⟨p', hp, rfl⟩ := Option.map_eq_some_iff.1 h
    show (p'.eval σ₀).bind _ = (p.eval σ₁).bind _
    rw [Srt.sameO_path.1 (Tm.eval_substH hL hst p hp)]
  | _, .unset, r', h => by cases h; rfl
  | _, .mref i, r', h => by
    obtain ⟨i', hi, rfl⟩ := Option.map_eq_some_iff.1 h
    show (i'.eval σ₀).bind _ = (i.eval σ₁).bind _
    rw [Srt.sameO_ident.1 (Tm.eval_substH hL hst i hi)]
  | _, .store x, r', h => by
    obtain ⟨x', hx, rfl⟩ := Option.map_eq_some_iff.1 h
    show (x'.eval σ₀).bind _ = (x.eval σ₁).bind _
    rw [Srt.sameO_st.1 (Tm.eval_substH hL hst x hx)]
  | _, .saveNet, r', h => by
    simp only [Rhs.substH] at h
    split at h
    · rename_i hg
      cases h
      show some σ₀.net = some σ₁.net
      rw [show σ₁.net = σ₀.net from congrArg State.net (hL.glob_of_envOnly hg)]
    · cases h
  | _, .saveNetMt, r', h => by cases h; rfl

/-- Two typed global parts over two heap typings, one state. -/
theorem GlobT.map_val_bind {H₀ H₁ : HTy} {o₀ : Option (GlobT C H₀)} {o₁ : Option (GlobT C H₁)}
    (h : o₀.map (·.1) = o₁.map (·.1)) {f₀ : GlobT C H₀ → Option (GlobT C H₀)}
    {f₁ : GlobT C H₁ → Option (GlobT C H₁)}
    (hf : ∀ G₀ G₁, G₀.1 = G₁.1 → (f₀ G₀).map (·.1) = (f₁ G₁).map (·.1)) :
    (o₀.bind f₀).map (·.1) = (o₁.bind f₁).map (·.1) := by
  cases o₀ <;> cases o₁
  · rfl
  · exact Option.noConfusion h
  · exact Option.noConfusion h
  · exact hf _ _ (Option.some.inj h)

section GlobCongr

variable {H₀ H₁ : HTy} {G₀ : GlobT C H₀} {G₁ : GlobT C H₁}

theorem GlobT.withStorage_congr (h : G₀.1 = G₁.1) (st : Storage C) :
    (G₀.withStorage st).1 = (G₁.withStorage st).1 := by
  rcases G₀ with ⟨G₀, _⟩; rcases G₁ with ⟨G₁, _⟩; dsimp only at h; subst h; rfl

theorem GlobT.withNet_congr (h : G₀.1 = G₁.1) (nt : List (Int × Int)) :
    (G₀.withNet nt).1 = (G₁.withNet nt).1 := by
  rcases G₀ with ⟨G₀, _⟩; rcases G₁ with ⟨G₁, _⟩; dsimp only at h; subst h; rfl

theorem GlobT.withBalance_congr (h : G₀.1 = G₁.1) (b : PrimTy.uint.Denote) :
    (G₀.withBalance b).1 = (G₁.withBalance b).1 := by
  rcases G₀ with ⟨G₀, _⟩; rcases G₁ with ⟨G₁, _⟩; dsimp only at h; subst h; rfl

theorem GlobT.withMem_congr (h : G₀.1 = G₁.1) {μ₀ : Grown H₀ (fun _ => Unit)}
    {μ₁ : Grown H₁ (fun _ => Unit)} (hμ : Srt.forget (C := C) .mem μ₀ = Srt.forget .mem μ₁) :
    (G₀.withMem μ₀).1 = (G₁.withMem μ₁).1 := by
  rcases G₀ with ⟨G₀, _⟩; rcases G₁ with ⟨G₁, _⟩; dsimp only at h; subst h
  rcases μ₀ with ⟨e₀, h₀, ⟨⟩⟩
  rcases μ₁ with ⟨e₁, h₁, ⟨⟩⟩
  simp only [Srt.forget, Sigma.mk.injEq] at hμ
  obtain ⟨rfl, hμ⟩ := hμ
  cases hμ
  rfl

end GlobCongr

/-- An element substituted computes the global part the element does, read
where `U` lands, from one global part. -/
theorem UpdElem.globT_substH (hL : U.Lands σ₀ g σ₁)
    (hst : ∀ x, st = some x → x.eval σ₀ = some σ₁.storage) {Ε : Ctx} (e : UpdElem C Δ Ε)
    {e' : UpdElem C Γ Ε} (h : e.substH U.held U.envOnly st = some e') (G₀ : GlobT C σ₀.H)
    (G₁ : GlobT C σ₁.H) (hG : G₀.1 = G₁.1) :
    (e'.globT σ₀ G₀).map (·.1) = (e.globT σ₁ G₁).map (·.1) := by
  cases e with
  | «local» i r =>
    obtain ⟨r', hr, rfl⟩ := Option.map_eq_some_iff.1 h
    show ((r'.eval σ₀).bind fun _ => some G₀).map (·.1) =
      ((r.eval σ₁).bind fun _ => some G₁).map (·.1)
    rw [Rhs.eval_substH hL hst r hr]
    cases r.eval σ₁ <;> simp only [Option.bind_none, Option.bind_some, Option.map_some, hG,
      Option.map_none]
  | storage x =>
    obtain ⟨x', hx, rfl⟩ := Option.map_eq_some_iff.1 h
    show ((x'.eval σ₀).bind fun st => some (G₀.withStorage st)).map (·.1) =
      ((x.eval σ₁).bind fun st => some (G₁.withStorage st)).map (·.1)
    rw [Srt.sameO_st.1 (Tm.eval_substH hL hst x hx)]
    cases x.eval σ₁ with
    | none => rfl
    | some st => exact congrArg some (GlobT.withStorage_congr hG st)
  | memory x =>
    obtain ⟨x', hx, rfl⟩ := Option.map_eq_some_iff.1 h
    have hm := Tm.eval_substH hL hst x hx
    show ((x'.eval σ₀).bind fun μ => some (G₀.withMem μ)).map (·.1) =
      ((x.eval σ₁).bind fun μ => some (G₁.withMem μ)).map (·.1)
    revert hm
    cases x'.eval σ₀ <;> cases x.eval σ₁ <;> intro hm
    · rfl
    · exact Option.noConfusion hm
    · exact Option.noConfusion hm
    · exact congrArg some (GlobT.withMem_congr hG (Option.some.inj hm))
  | selfBalance op a =>
    simp only [UpdElem.substH] at h
    split at h
    · rename_i hg
      obtain ⟨a', ha, rfl⟩ := Option.map_eq_some_iff.1 h
      have hb : σ₁.selfBalance = σ₀.selfBalance :=
        congrArg State.selfBalance (hL.glob_of_envOnly hg)
      show ((a'.eval σ₀).bind fun amt =>
          (PrimTy.uint.ofInt? (op.apply σ₀.selfBalance.1 amt.1)).bind fun b =>
            some (G₀.withBalance b)).map (·.1) =
        ((a.eval σ₁).bind fun amt =>
          (PrimTy.uint.ofInt? (op.apply σ₁.selfBalance.1 amt.1)).bind fun b =>
            some (G₁.withBalance b)).map (·.1)
      rw [Srt.sameO_val.1 (Tm.eval_substH hL hst a ha), hb]
      cases a.eval σ₁ with
      | none => rfl
      | some amt =>
        simp only [Option.bind_some]
        cases PrimTy.uint.ofInt? (op.apply σ₀.selfBalance.1 amt.1) with
        | none => rfl
        | some b => exact congrArg some (GlobT.withBalance_congr hG b)
    · cases h
  | net r op a =>
    simp only [UpdElem.substH] at h
    obtain ⟨r', hr, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨a', ha, h⟩ := Option.bind_eq_some_iff.1 h
    cases h
    show ((r'.eval σ₀).bind fun addr => (a'.eval σ₀).bind fun amt =>
        some (G₀.withNet (Semantics.setBy addr.1
          (op.apply ((Semantics.lookupBy addr.1 G₀.1.net).getD 0) amt.1) G₀.1.net))).map (·.1) =
      ((r.eval σ₁).bind fun addr => (a.eval σ₁).bind fun amt =>
        some (G₁.withNet (Semantics.setBy addr.1
          (op.apply ((Semantics.lookupBy addr.1 G₁.1.net).getD 0) amt.1) G₁.1.net))).map (·.1)
    rw [Srt.sameO_val.1 (Tm.eval_substH hL hst r hr), Srt.sameO_val.1 (Tm.eval_substH hL hst a ha),
      hG]
    cases r.eval σ₁ <;> cases a.eval σ₁ <;>
      first | rfl | exact congrArg some (GlobT.withNet_congr hG _)
  | pay r a =>
    simp only [UpdElem.substH] at h
    split at h
    · rename_i hg
      obtain ⟨r', hr, h⟩ := Option.bind_eq_some_iff.1 h
      obtain ⟨a', ha, h⟩ := Option.bind_eq_some_iff.1 h
      cases h
      have ht : σ₁.tx = σ₀.tx := congrArg State.tx (hL.glob_of_envOnly hg)
      show ((r'.eval σ₀).bind fun addr => (a'.eval σ₀).bind fun amt =>
          some (G₀.withNet (if addr.1 = σ₀.tx.selfAddress.1 then G₀.1.net
            else Semantics.setBy addr.1 ((Semantics.lookupBy addr.1 G₀.1.net).getD 0 - amt.1)
              G₀.1.net))).map (·.1) =
        ((r.eval σ₁).bind fun addr => (a.eval σ₁).bind fun amt =>
          some (G₁.withNet (if addr.1 = σ₁.tx.selfAddress.1 then G₁.1.net
            else Semantics.setBy addr.1 ((Semantics.lookupBy addr.1 G₁.1.net).getD 0 - amt.1)
              G₁.1.net))).map (·.1)
      rw [Srt.sameO_val.1 (Tm.eval_substH hL hst r hr),
        Srt.sameO_val.1 (Tm.eval_substH hL hst a ha), ht, hG]
      cases r.eval σ₁ <;> cases a.eval σ₁ <;>
        first | rfl | exact congrArg some (GlobT.withNet_congr hG _)
    · cases h
  | netMt r a =>
    simp only [UpdElem.substH] at h
    obtain ⟨r', hr, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨a', ha, h⟩ := Option.bind_eq_some_iff.1 h
    cases h
    show ((r'.eval σ₀).bind fun addr => (a'.eval σ₀).bind fun amt =>
        some (G₀.withNet [(addr.1, amt.1)])).map (·.1) =
      ((r.eval σ₁).bind fun addr => (a.eval σ₁).bind fun amt =>
        some (G₁.withNet [(addr.1, amt.1)])).map (·.1)
    rw [Srt.sameO_val.1 (Tm.eval_substH hL hst r hr), Srt.sameO_val.1 (Tm.eval_substH hL hst a ha)]
    cases r.eval σ₁ <;> cases a.eval σ₁ <;>
      first | rfl | exact congrArg some (GlobT.withNet_congr hG _)
  | setBalance a =>
    obtain ⟨a', ha, rfl⟩ := Option.map_eq_some_iff.1 h
    show ((a'.eval σ₀).bind fun amt => some (G₀.withBalance amt)).map (·.1) =
      ((a.eval σ₁).bind fun amt => some (G₁.withBalance amt)).map (·.1)
    rw [Srt.sameO_val.1 (Tm.eval_substH hL hst a ha)]
    cases a.eval σ₁ <;> first | rfl | exact congrArg some (GlobT.withBalance_congr hG _)

end SoundT

section GraftT

variable {Γ Δ₁ : Ctx} {σ₀ : State C Γ} {U : Upd C Γ Δ₁} {st : Option (Tm C Γ .st)}

/-- The grafted update halts where `U` does. -/
theorem Upd.globT_graft_none (hU : U.globT σ₀ = none) :
    {Δ₂ : Ctx} → (V : Upd C Δ₁ Δ₂) → {W : Upd C Γ Δ₂} → U.graft U.held U.envOnly st V = some W →
      W.globT σ₀ = none
  | _, .nil, W, h => by cases h; exact hU
  | _, .snoc V e', W, h => by
    simp only [Upd.graft] at h
    obtain ⟨W', hW, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨e'', -, h⟩ := Option.bind_eq_some_iff.1 h
    cases h
    show (W'.globT σ₀).bind _ = none
    rw [Upd.globT_graft_none hU V hW]
    rfl
  | _, .decl V x r, W, h => by
    simp only [Upd.graft] at h
    obtain ⟨W', hW, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨r', -, h⟩ := Option.bind_eq_some_iff.1 h
    cases h
    show (W'.globT σ₀).bind _ = none
    rw [Upd.globT_graft_none hU V hW]
    rfl
  | _, .pop V _, W, h => by
    obtain ⟨W', hW, rfl⟩ := Option.map_eq_some_iff.1 h
    exact Upd.globT_graft_none hU V hW
  | _, .drop V _, W, h => by
    obtain ⟨W', hW, rfl⟩ := Option.map_eq_some_iff.1 h
    exact Upd.globT_graft_none hU V hW

variable {σ₁ : State C Δ₁} {g₁ : GlobT C σ₀.H}

/-- **The grafted update computes the global part `V` does** in a state `U`
lands on. -/
theorem Upd.globT_graft (hL : U.Lands σ₀ g₁ σ₁)
    (hst : ∀ x, st = some x → x.eval σ₀ = some σ₁.storage) :
    {Δ₂ : Ctx} → (V : Upd C Δ₁ Δ₂) → {W : Upd C Γ Δ₂} → U.graft U.held U.envOnly st V = some W →
      (W.globT σ₀).map (·.1) = (V.globT σ₁).map (·.1)
  | _, .nil, W, h => by
    cases h
    rw [hL.1]
    show some g₁.1 = some σ₁.glob
    rw [hL.2.1]
  | _, .snoc V e, W, h => by
    simp only [Upd.graft] at h
    obtain ⟨W', hW, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨e', he, h⟩ := Option.bind_eq_some_iff.1 h
    cases h
    exact GlobT.map_val_bind (Upd.globT_graft hL hst V hW)
      fun G₀ G₁ hG => UpdElem.globT_substH hL hst e he G₀ G₁ hG
  | _, .decl V x r, W, h => by
    simp only [Upd.graft] at h
    obtain ⟨W', hW, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨r', hr, h⟩ := Option.bind_eq_some_iff.1 h
    cases h
    refine GlobT.map_val_bind (Upd.globT_graft hL hst V hW) fun G₀ G₁ hG => ?_
    show ((r'.eval σ₀).bind fun _ => some G₀).map (·.1) =
      ((r.eval σ₁).bind fun _ => some G₁).map (·.1)
    rw [Rhs.eval_substH hL hst r hr]
    cases r.eval σ₁ <;> simp only [Option.bind_none, Option.bind_some, Option.map_some, hG,
      Option.map_none]
  | _, .pop V _, W, h => by
    obtain ⟨W', hW, rfl⟩ := Option.map_eq_some_iff.1 h
    exact Upd.globT_graft hL hst V hW
  | _, .drop V _, W, h => by
    obtain ⟨W', hW, rfl⟩ := Option.map_eq_some_iff.1 h
    exact Upd.globT_graft hL hst V hW

/-- **The grafted update leaves in each local what `V` does**, read in a
state `U` lands on. -/
theorem Upd.held_graft (hL : U.Lands σ₀ g₁ σ₁)
    (hst : ∀ x, st = some x → x.eval σ₀ = some σ₁.storage) :
    {Δ₂ : Ctx} → (V : Upd C Δ₁ Δ₂) → {W : Upd C Γ Δ₂} → U.graft U.held U.envOnly st V = some W →
      ∀ {t : LTy} (i : Idx Δ₂ t) (v : t.VDen C), Held.OKV σ₁ v (V.held i) →
        Held.OKV σ₀ v (W.held i)
  | _, .nil, W, h, t, i, v, hv => by
    cases h
    have hi := (Held.OK_iff_OKV σ₀ σ₁ i _).1 (hL.2.2 i)
    show Held.OKV σ₀ v (U.held i)
    have hv : v = σ₁.getV i := hv
    rw [hv]
    exact hi
  | _, .snoc V e, W, h, t, i, v, hv => by
    simp only [Upd.graft] at h
    obtain ⟨W', hW, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨e', he, h⟩ := Option.bind_eq_some_iff.1 h
    cases h
    cases e with
    | «local» k r =>
      obtain ⟨r', hr, rfl⟩ := Option.map_eq_some_iff.1 he
      show Held.OKV σ₀ v (Subst.set (Upd.held W') k r' i)
      have hv : Held.OKV σ₁ v (Subst.set (Upd.held V) k r i) := hv
      unfold Subst.set at hv ⊢
      split
      · rename_i hki
        rw [dif_pos hki] at hv
        obtain rfl := Idx.ty_eq_of_toNat hki
        obtain rfl := Idx.toNat_inj k i hki
        show r'.eval σ₀ = some v
        rw [Rhs.eval_substH hL hst r hr]
        exact hv
      · rename_i hki
        rw [dif_neg hki] at hv
        exact Upd.held_graft hL hst V hW i v hv
    | storage x | memory x | setBalance x =>
      obtain ⟨_, -, rfl⟩ := Option.map_eq_some_iff.1 he
      exact Upd.held_graft hL hst V hW i v hv
    | selfBalance op a =>
      simp only [UpdElem.substH] at he
      split at he
      · obtain ⟨_, -, rfl⟩ := Option.map_eq_some_iff.1 he
        exact Upd.held_graft hL hst V hW i v hv
      · cases he
    | net r op a | netMt r a =>
      simp only [UpdElem.substH] at he
      obtain ⟨_, -, he⟩ := Option.bind_eq_some_iff.1 he
      obtain ⟨_, -, he⟩ := Option.bind_eq_some_iff.1 he
      cases he
      exact Upd.held_graft hL hst V hW i v hv
    | pay r a =>
      simp only [UpdElem.substH] at he
      split at he
      · obtain ⟨_, -, he⟩ := Option.bind_eq_some_iff.1 he
        obtain ⟨_, -, he⟩ := Option.bind_eq_some_iff.1 he
        cases he
        exact Upd.held_graft hL hst V hW i v hv
      · cases he
  | _, .decl V x r, W, h, t, i, v, hv => by
    simp only [Upd.graft] at h
    obtain ⟨W', hW, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨r', hr, h⟩ := Option.bind_eq_some_iff.1 h
    cases h
    cases i with
    | here =>
      show r'.eval σ₀ = some v
      rw [Rhs.eval_substH hL hst r hr]
      exact hv
    | there j => exact Upd.held_graft hL hst V hW j v hv
  | _, .pop V e, W, h, t, i, v, hv => by
    obtain ⟨W', hW, rfl⟩ := Option.map_eq_some_iff.1 h
    exact Upd.held_graft hL hst V hW (i.ext e) v hv
  | _, .drop V e, W, h, t, i, v, hv => by
    obtain ⟨W', hW, rfl⟩ := Option.map_eq_some_iff.1 h
    exact Upd.held_graft hL hst V hW (i.wk e) v hv

end GraftT

/-! ## An update moved under a hidden binder

`{U} ∀x. {V} ψ` (the binder `memoryLocalDeclInitDrop` leaves between a
stack and the rest, decision 12) merges as `∀x. {U ‖ V} ψ` when `U` declares
nothing: `U` reads none of `x`, so it is `U` with every position one deeper
(`Upd.lift?`), applied in a state with `x` on top. -/

/-- The update that drops the top local: a state with one more local read in
the one before (`Tm.substH` of it shifts a term up). -/
abbrev Upd.dropTop (Γ : Ctx) (t : LTy) : Upd C (t :: Γ) Γ := .drop .nil up

/-- An element moved under a pushed local: a local's, the storage's or the
memory's (the ledger's is not needed). -/
def UpdElem.lift? {Γ Δ : Ctx} {t : LTy} : UpdElem C Γ Δ → Option (UpdElem C (t :: Γ) (t :: Δ))
  | .local i r => (r.substH (Upd.dropTop (C := C) Γ t).held true none).map (.local i.there)
  | .storage x => (x.substH (Upd.dropTop (C := C) Γ t).held true none).map .storage
  | .memory x => (x.substH (Upd.dropTop (C := C) Γ t).held true none).map .memory
  | _ => none

/-- An update that declares nothing, moved under a pushed local. -/
def Upd.lift? {Γ : Ctx} {t : LTy} : {Δ : Ctx} → Upd C Γ Δ → Option (Upd C (t :: Γ) (t :: Δ))
  | _, .nil => some .nil
  | _, .snoc U e => do pure (.snoc (← Upd.lift? U) (← e.lift?))
  | _, .decl .. | _, .pop .. | _, .drop .. => none

/-- An update moved under a pushed local, its scope ends too: a pop or a
drop below the local is a thinning that keeps it (the sequent's merge; a
chain's moves `Upd.lift?`'s). -/
def Upd.liftG? {Γ : Ctx} {t : LTy} : {Δ : Ctx} → Upd C Γ Δ → Option (Upd C (t :: Γ) (t :: Δ))
  | _, .nil => some .nil
  | _, .snoc U e => do pure (.snoc (← Upd.liftG? U) (← e.lift?))
  | _, .pop U h => (Upd.liftG? U).map (.drop · (.keep (Thin.ofExt h)))
  | _, .drop U h => (Upd.liftG? U).map (.drop · (.keep h))
  | _, .decl .. => none

section Lift

variable {Γ : Ctx} {t : LTy}

theorem Upd.dropTop_envOnly : (Upd.dropTop (C := C) Γ t).envOnly = true := rfl

/-- Dropping the top local lands on the state below it. -/
theorem Upd.lands_dropTop (σ : State C Γ) (v : t.TDenote C σ.H) :
    (Upd.dropTop (C := C) Γ t).Lands (σ.push v) (σ.push v).globG σ :=
  ⟨rfl, rfl, fun _ => rfl⟩

theorem Tm.eval_dropTop (σ : State C Γ) (v : t.TDenote C σ.H) {k : Srt} (x : Tm C Γ k)
    {x' : Tm C (t :: Γ) k} (hx : x.substH (Upd.dropTop (C := C) Γ t).held true none = some x') :
    x'.eval (σ.push v) = x.eval σ :=
  Srt.SameO.eq (Tm.eval_substH (Upd.lands_dropTop σ v) (fun _ h => Option.noConfusion h) x hx)

theorem Rhs.eval_dropTop (σ : State C Γ) (v : t.TDenote C σ.H) {u : LTy} (r : Rhs C Γ u)
    {r' : Rhs C (t :: Γ) u} (hr : r.substH (Upd.dropTop (C := C) Γ t).held true none = some r') :
    r'.eval (σ.push v) = r.eval σ :=
  Rhs.eval_substH (Upd.lands_dropTop σ v) (fun _ h => Option.noConfusion h) r hr

theorem UpdElem.globT_lift? {Δ : Ctx} (σ : State C Γ) (v : t.TDenote C σ.H) (e : UpdElem C Γ Δ)
    {e' : UpdElem C (t :: Γ) (t :: Δ)} (h : e.lift? = some e') (G : GlobT C σ.H) :
    e'.globT (σ.push v) G = e.globT σ G := by
  cases e with
  | «local» i r =>
    obtain ⟨r', hr, rfl⟩ := Option.map_eq_some_iff.1 h
    show ((r'.eval (σ.push v)).bind fun _ => some G) = (r.eval σ).bind fun _ => some G
    rw [Rhs.eval_dropTop σ v r hr]
  | storage x =>
    obtain ⟨x', hx, rfl⟩ := Option.map_eq_some_iff.1 h
    show ((x'.eval (σ.push v)).bind fun st => some (G.withStorage st)) =
      (x.eval σ).bind fun st => some (G.withStorage st)
    rw [Tm.eval_dropTop σ v x hx]
  | memory x =>
    obtain ⟨x', hx, rfl⟩ := Option.map_eq_some_iff.1 h
    show ((x'.eval (σ.push v)).bind fun μ => some (G.withMem μ)) =
      (x.eval σ).bind fun μ => some (G.withMem μ)
    rw [Tm.eval_dropTop σ v x hx]
    exact rfl
  | selfBalance _ _ | net _ _ _ | pay _ _ | netMt _ _ | setBalance _ => cases h

/-- **The moved update computes the update's global part.** -/
theorem Upd.globT_liftG? (σ : State C Γ) (v : t.TDenote C σ.H) : {Δ : Ctx} → (U : Upd C Γ Δ) →
    {U' : Upd C (t :: Γ) (t :: Δ)} → U.liftG? = some U' → U'.globT (σ.push v) = U.globT σ
  | _, .nil, _, h => by cases h; rfl
  | _, .snoc U e, _, h => by
    simp only [Upd.liftG?] at h
    obtain ⟨U', hU, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨e', he, h⟩ := Option.bind_eq_some_iff.1 h
    cases h
    show (U'.globT (σ.push v)).bind (e'.globT (σ.push v)) = (U.globT σ).bind (e.globT σ)
    rw [Upd.globT_liftG? σ v U hU]
    cases U.globT σ with
    | none => rfl
    | some G => exact UpdElem.globT_lift? σ v e he G
  | _, .pop U _, _, hh => by
    obtain ⟨U', hU, rfl⟩ := Option.map_eq_some_iff.1 hh
    exact Upd.globT_liftG? σ v U hU
  | _, .drop U _, _, hh => by
    obtain ⟨U', hU, rfl⟩ := Option.map_eq_some_iff.1 hh
    exact Upd.globT_liftG? σ v U hU
  | _, .decl .., _, h => by cases h

/-- The moved update keeps the top local. -/
theorem Upd.held_liftG?_here : {Δ : Ctx} → (U : Upd C Γ Δ) → {U' : Upd C (t :: Γ) (t :: Δ)} →
    U.liftG? = some U' → U'.held .here = .pos .here
  | _, .nil, _, h => by cases h; rfl
  | _, .snoc U e, _, h => by
    simp only [Upd.liftG?] at h
    obtain ⟨U', hU, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨e', he, h⟩ := Option.bind_eq_some_iff.1 h
    cases h
    cases e with
    | «local» i r =>
      obtain ⟨r', -, rfl⟩ := Option.map_eq_some_iff.1 he
      show Subst.set (Upd.held U') i.there r' .here = _
      unfold Subst.set
      rw [dif_neg (show ¬ (i.there.toNat = (Idx.here : Idx (t :: _) t).toNat) by
        simp only [Idx.toNat]; omega)]
      exact Upd.held_liftG?_here U hU
    | storage x | memory x =>
      obtain ⟨_, -, rfl⟩ := Option.map_eq_some_iff.1 he
      show Upd.held U' .here = _
      exact Upd.held_liftG?_here U hU
    | selfBalance _ _ | net _ _ _ | pay _ _ | netMt _ _ | setBalance _ => cases he
  | _, .pop U _, _, hh => by
    obtain ⟨U', hU, rfl⟩ := Option.map_eq_some_iff.1 hh
    exact Upd.held_liftG?_here U hU
  | _, .drop U _, _, hh => by
    obtain ⟨U', hU, rfl⟩ := Option.map_eq_some_iff.1 hh
    exact Upd.held_liftG?_here U hU
  | _, .decl .., _, h => by cases h

/-- The moved update leaves in each local below the top what the update
does, read one local deeper. -/
theorem Upd.held_liftG?_there (σ : State C Γ) (v : t.TDenote C σ.H) :
    {Δ : Ctx} → (U : Upd C Γ Δ) → {U' : Upd C (t :: Γ) (t :: Δ)} → U.liftG? = some U' →
      ∀ {u : LTy} (i : Idx Δ u) (w : u.VDen C), Held.OKV σ w (U.held i) →
        Held.OKV (σ.push v) w (U'.held i.there)
  | _, .nil, _, h, _, i, w, hw => by cases h; exact hw
  | _, .snoc U e, _, h, u, i, w, hw => by
    simp only [Upd.liftG?] at h
    obtain ⟨U', hU, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨e', he, h⟩ := Option.bind_eq_some_iff.1 h
    cases h
    cases e with
    | «local» k r =>
      obtain ⟨r', hr, rfl⟩ := Option.map_eq_some_iff.1 he
      show Held.OKV (σ.push v) w (Subst.set (Upd.held U') k.there r' i.there)
      have hw : Held.OKV σ w (Subst.set (Upd.held U) k r i) := hw
      unfold Subst.set at hw ⊢
      by_cases hki : k.toNat = i.toNat
      · obtain rfl := Idx.ty_eq_of_toNat hki
        obtain rfl := Idx.toNat_inj k i hki
        rw [dif_pos rfl] at hw ⊢
        show r'.eval (σ.push v) = some w
        rw [Rhs.eval_dropTop σ v r hr]
        exact hw
      · rw [dif_neg hki] at hw
        rw [dif_neg (show ¬ (k.there.toNat = i.there.toNat) by
          simp only [Idx.toNat]; omega)]
        exact Upd.held_liftG?_there σ v U hU i w hw
    | storage x | memory x =>
      obtain ⟨_, -, rfl⟩ := Option.map_eq_some_iff.1 he
      show Held.OKV (σ.push v) w (Upd.held U' i.there)
      exact Upd.held_liftG?_there σ v U hU i w hw
    | selfBalance _ _ | net _ _ _ | pay _ _ | netMt _ _ | setBalance _ => cases he
  | _, .pop U e, _, hh, u, i, w, hw => by
    obtain ⟨U', hU, rfl⟩ := Option.map_eq_some_iff.1 hh
    have hw : Held.OKV σ w (U.held (i.ext e)) := hw
    show Held.OKV (σ.push v) w (U'.held (i.wk (Thin.ofExt e)).there)
    rw [Idx.wk_ofExt]
    exact Upd.held_liftG?_there σ v U hU (i.ext e) w hw
  | _, .drop U e, _, hh, u, i, w, hw => by
    obtain ⟨U', hU, rfl⟩ := Option.map_eq_some_iff.1 hh
    exact Upd.held_liftG?_there σ v U hU (i.wk e) w hw
  | _, .decl .., _, h, _, _, _, _ => by cases h

/-- **The moved update lands on the state the update lands on, the local
kept on top.** -/
theorem Upd.lands_liftG? {Δ : Ctx} {U : Upd C Γ Δ} {U' : Upd C (t :: Γ) (t :: Δ)}
    (hU : U.liftG? = some U') {σ : State C Γ} {g : GlobT C σ.H} {σ' : State C Δ}
    (hL : U.Lands σ g σ') (v : t.TDenote C σ.H) (v' : t.TDenote C σ'.H)
    (hv : LTy.VDen.ofT t v' = LTy.VDen.ofT t v) :
    U'.Lands (σ.push v) g (σ'.push v') := by
  refine ⟨(Upd.globT_liftG? σ v U hU).trans hL.1, hL.2.1, fun i => ?_⟩
  cases i with
  | here =>
    rw [Upd.held_liftG?_here U hU]
    exact hv
  | there j =>
    rw [Held.OK_iff_OKV]
    exact Upd.held_liftG?_there σ v U hU j _ ((Held.OK_iff_OKV _ _ _ _).1 (hL.2.2 j))

/-- An update that declares nothing moves as one that ends no scope. -/
theorem Upd.liftG?_of_lift? : {Δ : Ctx} → (U : Upd C Γ Δ) → {U' : Upd C (t :: Γ) (t :: Δ)} →
    U.lift? = some U' → U.liftG? = some U'
  | _, .nil, _, h => h
  | _, .snoc U e, _, h => by
    simp only [Upd.lift?] at h
    obtain ⟨U', hU, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨e', he, h⟩ := Option.bind_eq_some_iff.1 h
    cases h
    simp only [Upd.liftG?, Upd.liftG?_of_lift? U hU, he]
    rfl
  | _, .decl .., _, h | _, .pop .., _, h | _, .drop .., _, h => by cases h

end Lift

/-! ## Merging in a line -/

/-- A local's type other than a memory one: its typed values do not depend
on the heap, so a binder over it reads the same values from any typed
state. -/
def LTy.notMem : LTy → Bool
  | .mem _ => false
  | _ => true

/-- A local's value of a type other than a memory one, in one heap, is one
in any other. -/
theorem LTy.vden_of_notMem {t : LTy} (ht : t.notMem = true) {H H' : HTy} (v' : t.TDenote C H') :
    ∃ v : t.TDenote C H, LTy.VDen.ofT t v = LTy.VDen.ofT t v' := by
  cases t with
  | mem => cases ht
  | val | alias | old | oldNet => exact ⟨v', rfl⟩

/-- An element that allocates nothing: a local or the storage set. -/
def UpdElem.keepsNext {Γ Δ : Ctx} : UpdElem C Γ Δ → Bool
  | .local .. | .storage _ => true
  | _ => false

/-- An update that allocates nothing: the heap typing it leaves is the one
of the state it is applied in. -/
def Upd.keepsNext {Γ : Ctx} : {Δ : Ctx} → Upd C Γ Δ → Bool
  | _, .nil => true
  | _, .snoc U e => U.keepsNext && e.keepsNext
  | _, .decl U _ _ | _, .pop U _ | _, .drop U _ => U.keepsNext

/-- An update that allocates nothing leaves the heap typing it found. -/
theorem Upd.keepsNext_globT {Γ : Ctx} {σ₀ : State C Γ} : {Δ : Ctx} → (U : Upd C Γ Δ) →
    U.keepsNext = true → ∀ {g : GlobT C σ₀.H}, U.globT σ₀ = some g → g.1.H = σ₀.H
  | _, .nil, _, _, h => by cases h; rfl
  | _, .snoc U e, hk, g, h => by
    have hk' : U.keepsNext = true ∧ e.keepsNext = true := Bool.and_eq_true_iff.mp hk
    change (U.globT σ₀).bind (e.globT σ₀) = some g at h
    rw [Option.bind_eq_some_iff] at h
    obtain ⟨g', h₁, h₂⟩ := h
    have ih := Upd.keepsNext_globT U hk'.1 h₁
    rw [UpdElem.globT_eq_globTM] at h₂
    cases e with
    | «local» i r =>
      simp only [UpdElem.globTM, Option.bind_eq_some_iff, Option.some.injEq] at h₂
      obtain ⟨_, -, rfl⟩ := h₂
      exact ih
    | storage s =>
      simp only [UpdElem.globTM, Option.bind_eq_some_iff, Option.some.injEq] at h₂
      obtain ⟨_, -, rfl⟩ := h₂
      exact ih
    | _ => cases hk'.2
  | _, .decl U _ r, hk, g, h => by
    change (U.globT σ₀).bind (fun g => (r.eval σ₀).bind fun _ => some g) = some g at h
    simp only [Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨g', h₁, _, _, rfl⟩ := h
    exact Upd.keepsNext_globT U hk h₁
  | _, .pop U _, hk, _, h => Upd.keepsNext_globT U hk h
  | _, .drop U _, hk, _, h => Upd.keepsNext_globT U hk h

/-- A local's value, cast along an equal heap typing, reads as it did. -/
theorem LTy.VDen.ofT_rec {H H' : HTy} (h : H' = H) (t : LTy) (v' : t.TDenote C H') :
    LTy.VDen.ofT t (h ▸ v' : t.TDenote C H) = LTy.VDen.ofT t v' := by
  subst h; rfl

/-- `{U} ∀x. ψ` from `∀x. {U↑} ψ`, `U↑` the update moved under the binder
(`Upd.liftG?`).  A value of the binder after `U` is one before it: its type
is not a memory one, or `U` allocates nothing, so the heap typing after it
is the one before. -/
theorem Fml.upd_bind_of_liftG {m m' : Modality} {Γ Δ : Ctx} {U : Upd C Γ Δ} {t : LTy} {x : Var}
    {U' : Upd C (t :: Γ) (t :: Δ)} (hU' : U.liftG? = some U')
    (ht : (t.notMem || U.keepsNext) = true)
    {ψ : Fml C (t :: Δ)} (σ : State C Γ)
    (hψ : m'.forallB fun v : t.TDenote C σ.H => holds (σ.push v) (.upd m U' ψ)) :
    holds σ (.upd m U (.bind m' x t ψ)) := by
  obtain ⟨v₀⟩ := LTy.tdenote_nonempty (C := C) (H := σ.H) t
  refine Upd.afterT_intro (fun he => ?_) fun g σ' hL => ?_
  · have h₀ : U'.afterT m (σ.push v₀) (holds · ψ) := Modality.forallB_all hψ v₀
    exact h₀.of_none ((Upd.globT_liftG? σ v₀ U hU').trans he)
  · refine Modality.forallB_intro fun v' => ?_
    have hv : ∃ v : t.TDenote C σ.H, LTy.VDen.ofT t v = LTy.VDen.ofT t v' := by
      rcases Bool.or_eq_true_iff.mp ht with ht | hk
      · exact LTy.vden_of_notMem ht v'
      · have hH : σ'.H = σ.H := by
          have h₁ := Upd.keepsNext_globT U hk hL.1
          rw [← hL.2.1] at h₁
          exact h₁
        exact ⟨hH ▸ v', LTy.VDen.ofT_rec hH t v'⟩
    obtain ⟨v, hv⟩ := hv
    have h : U'.afterT m (σ.push v) (holds · ψ) := Modality.forallB_all hψ v
    exact h.of_lands (Upd.lands_liftG? hU' hL v v' hv.symm)

theorem Fml.upd_bind_of_lift {m m' : Modality} {Γ Δ : Ctx} {U : Upd C Γ Δ} {t : LTy} {x : Var}
    {U' : Upd C (t :: Γ) (t :: Δ)} (hU' : U.lift? = some U') (ht : (t.notMem || U.keepsNext) = true)
    {ψ : Fml C (t :: Δ)} (σ : State C Γ)
    (hψ : m'.forallB fun v : t.TDenote C σ.H => holds (σ.push v) (.upd m U' ψ)) :
    holds σ (.upd m U (.bind m' x t ψ)) :=
  Fml.upd_bind_of_liftG (Upd.liftG?_of_lift? U hU') ht σ hψ

/-! ## The storage an update leaves

`{storage := s}{x := find(storage, p)}` is `{storage := s ‖ x := find(s, p)}`:
`storage` after an update that writes no global part but the storage is the
storage it last wrote (`Upd.lastSt`), read before it (`Upd.lastSt_eval`). -/

/-- An element that writes no global part but the storage. -/
def UpdElem.stOnly {Γ Δ : Ctx} : UpdElem C Γ Δ → Bool
  | .local .. | .storage _ => true
  | _ => false

/-- An update that writes no global part but the storage. -/
def Upd.stOnly {Γ : Ctx} : {Δ : Ctx} → Upd C Γ Δ → Bool
  | _, .nil => true
  | _, .snoc U e => Upd.stOnly U && e.stOnly
  | _, .decl U _ _ | _, .pop U _ | _, .drop U _ => Upd.stOnly U

/-- The storage an update last writes, read in the state it is applied in,
where it writes no other global part. -/
def Upd.lastSt {Γ : Ctx} : {Δ : Ctx} → Upd C Γ Δ → Option (Tm C Γ .st)
  | _, .nil => none
  | _, .snoc U (.storage x) => if Upd.stOnly U then some x else none
  | _, .snoc U (.local _ _) => Upd.lastSt U
  | _, .snoc _ (.memory _) | _, .snoc _ (.selfBalance ..) | _, .snoc _ (.net ..)
  | _, .snoc _ (.pay ..) | _, .snoc _ (.netMt ..) | _, .snoc _ (.setBalance _) => none
  | _, .decl U _ _ | _, .pop U _ | _, .drop U _ => Upd.lastSt U

/-- **`sequentialToParallel`**: `{U}{V}` as one update, `V` read in `U`'s
state; `none` where a symbol of `V` reads a global part `U` writes. -/
def Upd.seqPar {Γ Δ₁ Δ₂ : Ctx} (U : Upd C Γ Δ₁) (V : Upd C Δ₁ Δ₂) : Option (Upd C Γ Δ₂) :=
  U.graft U.held U.envOnly U.lastSt V

/-- **The storage an update last wrote, read before it, is the storage of
the global part it leaves.** -/
theorem Upd.lastSt_eval {Γ : Ctx} {σ₀ : State C Γ} : {Δ : Ctx} → (U : Upd C Γ Δ) →
    {g : GlobT C σ₀.H} → U.globT σ₀ = some g → ∀ x, U.lastSt = some x →
      x.eval σ₀ = some g.1.storage
  | _, .nil, _, _, _, h => by cases h
  | _, .snoc U e, g, h, x, hx => by
    change (U.globT σ₀).bind (e.globT σ₀) = some g at h
    rw [Option.bind_eq_some_iff] at h
    obtain ⟨τ, hτ, h⟩ := h
    rw [UpdElem.globT_eq_globTM] at h
    cases e with
    | «local» k r =>
      simp only [UpdElem.globTM, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨_, -, rfl⟩ := h
      exact Upd.lastSt_eval U hτ x hx
    | storage y =>
      simp only [Upd.lastSt] at hx
      split at hx
      · cases hx
        simp only [UpdElem.globTM, Option.bind_eq_some_iff, Option.some.injEq] at h
        obtain ⟨st, hst, rfl⟩ := h
        exact hst
      · cases hx
    | _ => cases hx
  | _, .decl U _ r, g, h, x, hx => by
    change (U.globT σ₀).bind (fun g => (r.eval σ₀).bind fun _ => some g) = some g at h
    simp only [Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨τ, hτ, _, _, rfl⟩ := h
    exact Upd.lastSt_eval U hτ x hx
  | _, .pop U _, _, h, x, hx => Upd.lastSt_eval U h x hx
  | _, .drop U _, _, h, x, hx => Upd.lastSt_eval U h x hx

/-- **The merged update gives the two**: `{U ‖ {U}V} φ` gives `{U}{V} φ`
under the modality of both, `st` the storage `U` leaves where any. -/
theorem holds_upd_graft {m : Modality} {Γ Δ₁ Δ₂ : Ctx} {U : Upd C Γ Δ₁} {V : Upd C Δ₁ Δ₂}
    {W : Upd C Γ Δ₂} {st : Option (Tm C Γ .st)}
    (hst : ∀ (σ₀ : State C Γ) (g : GlobT C σ₀.H), U.globT σ₀ = some g → ∀ x, st = some x →
      x.eval σ₀ = some g.1.storage)
    (hW : U.graft U.held U.envOnly st V = some W) {φ : Fml C Δ₂} (σ : State C Γ)
    (h : holds σ (.upd m W φ)) : holds σ (.upd m U (.upd m V φ)) := by
  have h : W.afterT m σ (holds · φ) := h
  refine Upd.afterT_intro (fun hU => h.of_none (Upd.globT_graft_none hU V hW)) fun g₁ σ₁ hL => ?_
  have hst' : ∀ x, st = some x → x.eval σ = some σ₁.storage := fun x hx => by
    rw [hst σ g₁ hL.1 x hx, ← hL.2.1]
    rfl
  have hG := Upd.globT_graft hL hst' V hW
  refine Upd.afterT_intro (fun hV => h.of_none ?_) fun g₂ σ₂ hL₂ => ?_
  · rw [hV] at hG
    cases hw : W.globT σ with
    | none => rfl
    | some _ => rw [hw] at hG; exact Option.noConfusion hG
  · rw [hL₂.1] at hG
    cases hw : W.globT σ with
    | none => rw [hw] at hG; exact Option.noConfusion hG
    | some g₂' =>
      rw [hw] at hG
      have hg : g₂'.1 = g₂.1 := Option.some.inj hG
      exact h.of_lands ⟨hw, hL₂.2.1.trans hg.symm, fun i => (Held.OK_iff_OKV _ _ _ _).2
        (Upd.held_graft hL hst' V hW i _ ((Held.OK_iff_OKV _ _ _ _).1 (hL₂.2.2 i)))⟩

/-! ## Hidden binders between two updates

A declaration's hidden binder sits between the update before it and the
one its assignment leaves (`{U} ∀x. {x := e} …`), so the two merge with
`U` moved under the binders between (`Upd.liftBinds?`). -/

/-- The scope past the hidden binders `bs`, the first one innermost. -/
def Binds.ctx : List (Modality × Var × LTy) → Ctx → Ctx
  | [], Γ => Γ
  | (_, _, t) :: bs, Γ => Binds.ctx bs (t :: Γ)

/-- The hidden binders `bs` in front of a formula, the first one outermost. -/
def Fml.binds {Γ : Ctx} : (bs : List (Modality × Var × LTy)) → Fml C (Binds.ctx bs Γ) → Fml C Γ
  | [], φ => φ
  | (m, x, t) :: bs, φ => .bind m x t (Fml.binds (Γ := t :: Γ) bs φ)

/-- An update moved under the hidden binders `bs`, each at a type other
than a memory one or the update allocating nothing. -/
def Upd.liftBinds? {Γ Δ : Ctx} : (bs : List (Modality × Var × LTy)) → Upd C Γ Δ →
    Option (Upd C (Binds.ctx bs Γ) (Binds.ctx bs Δ))
  | [], U => some U
  | (_, _, t) :: bs, U =>
    if (t.notMem || U.keepsNext) = true then (U.liftG? (t := t)).bind (Upd.liftBinds? bs) else none

/-- **An update moved under hidden binders reads as the update in front of
them.** -/
theorem holds_liftBinds {m : Modality} : {Γ Δ : Ctx} → (bs : List (Modality × Var × LTy)) →
    {U : Upd C Γ Δ} → {U' : Upd C (Binds.ctx bs Γ) (Binds.ctx bs Δ)} → U.liftBinds? bs = some U' →
    {ψ : Fml C (Binds.ctx bs Δ)} → ∀ σ : State C Γ,
      holds σ (Fml.binds bs (.upd m U' ψ)) → holds σ (.upd m U (Fml.binds bs ψ))
  | _, _, [], _, _, h, _, _, hσ => by cases h; exact hσ
  | _, _, (m', x, t) :: bs, U, U', h, ψ, σ, hσ => by
    simp only [Upd.liftBinds?] at h
    split at h
    · rename_i ht
      obtain ⟨U₁, hU₁, h⟩ := Option.bind_eq_some_iff.1 h
      exact Fml.upd_bind_of_liftG hU₁ ht σ
        (Modality.forallB_imp (fun v hv => holds_liftBinds bs h _ hv) hσ)
    · cases h

/-- `holds_upd_graft` for `sequentialToParallel`. -/
theorem holds_upd_seqPar {m : Modality} {Γ Δ₁ Δ₂ : Ctx} {U : Upd C Γ Δ₁} {V : Upd C Δ₁ Δ₂}
    {W : Upd C Γ Δ₂} (hW : U.seqPar V = some W) {φ : Fml C Δ₂} (σ : State C Γ)
    (h : holds σ (.upd m W φ)) : holds σ (.upd m U (.upd m V φ)) :=
  holds_upd_graft (fun _ _ hU x hx => Upd.lastSt_eval U hU x hx) hW σ h

end Solidity
