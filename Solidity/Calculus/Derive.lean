import Solidity.Calculus.DecideComplete
import Solidity.Calculus.Closer
import Solidity.Calculus.TheoryRewrite
import Solidity.Calculus.Spec
import Solidity.Calculus.ProofTree

/-!
# The strategy as one kernel evaluation: `sol_prove`

`sol_derive` (`Symex.lean`) builds a `⊢` derivation one `apply` at a time,
each an elaborator unification over the whole sequent.  `Derive.residue`
runs the same walk as a function: on a sequent `Γ ⟹ φ` it drops an empty
modality, fires the rule `Stmt.step` picks (as `update`, `unfold`, `split`,
`check`, `done`, or `branches` with any number of outcomes), or moves a precondition,
a quantified local or an update into the context, in `sol_derive`'s order;
a sequent none of these fits is a leaf, dropped when the closer accepts it.
What is left is the residue.  `Proves.of_residue` says once that a residue
whose leaves are proved proves the sequent, so a derivation is one
evaluation the kernel checks, not hundreds of elaborated steps.

The fresh names are numbered per goal, above every index of the goal's own
sequent (`Hyp.fresh Γ φ`), as the `Proves` constructors ask; `symex`
numbers them over the whole formula, sibling branches included, so the two
part ways after the first branch.

The default closer (`Derive.synClose`) is `LFml.close` on the reduction
(`Calculus/Closer.lean`): it closes a leaf inside the `Bool`, reading an
obligation's `wt(storage)` premise as the layout the storage holds
(`Derive.topWt`).  A parallel update is split first (`Fml.seqUpd`), and a
leaf past `Derive.closeSize` nodes is not attempted, by the closer nor by
`sol_prove?`'s reducing steps.  A leaf it does not close is left for a
tactic.

Neither the compiled run nor the kernel check heeds `maxHeartbeats`, so
the walk carries its own budget, the steps of the whole derivation
(`Derive.budget`), handed from each goal to its next sibling: a program
whose `if`s double its paths stops there, with an error.

* `sol_prove` computes the residue by compiled code, checks it in the
  kernel (`Derive.proves` when nothing is left,
  `Derive.residue … = some (ls, b)` otherwise, each an auxiliary lemma as
  `decide +kernel` makes one), and
  leaves one goal per residual leaf, `leaf1`, `leaf2`, … .  It searches
  nothing, so it is its own replay.  The statement is never unfolded by the
  elaborator: `Proves` is an inductive, and the proof term is assembled
  directly.
* `sol_prove?` runs `sol_prove`, tries `sol_decide`'s steps after
  `LFml.syn` (which the closer subsumes), then `sol_close`, then
  `sol_spec_close` (`omega`, `grind`) on each leaf, each try with its own
  heartbeats, and suggests the replay: `sol_prove` and one `case` per leaf.
  A leaf none of them closes stays a goal and is reported.
-/

namespace Solidity

open Semantics

variable {C : Contract}

namespace Derive

/-- A goal left over: a context and a formula. -/
abbrev Leaf (C : Contract) := List (Hyp C) × Fml C

/-- Every goal of `gs` by `r`, the leaves in order, the budget `b` handed
from one goal to the next; `none` when one fails. -/
def allRes (r : Nat → List (Hyp C) → Fml C → Option (List (Leaf C) × Nat)) :
    Nat → List (Leaf C) → Option (List (Leaf C) × Nat)
  | b, [] => some ([], b)
  | b, g :: gs =>
    match r b g.1 g.2 with
    | some (a, b') =>
      match allRes r b' gs with
      | some (c, b'') => some (a ++ c, b'')
      | none => none
    | none => none

/-- The goals of a rule's premise, fired on `⟨[ s; ω ]⟩ ψ` in the context `Γ`,
handed to `r` with the budget `b`: the goals of `Proves.updateRule`,
`unfoldRule`, `splitRule` (`thn`, `els`, `cov`), `checkRule` (`thn`, `els`),
`doneRule`, `branchesRule` (one per outcome). -/
def premiseRes (r : Nat → List (Hyp C) → Fml C → Option (List (Leaf C) × Nat)) (b : Nat)
    (Γ : List (Hyp C)) (m : Modality) (ω : Prog C) (ψ : Fml C) :
    Premise C → Option (List (Leaf C) × Nat)
  | .update U => r b (Γ ++ [.upd m U]) (.modal m ω ψ)
  | .unfold P => r b Γ (.modal m (P ++ ω) ψ)
  | .split c c' P Q =>
    allRes r b [(Γ ++ [.pre c], .modal m (P ++ ω) ψ), (Γ ++ [.pre c'], .modal m (Q ++ ω) ψ),
      (Γ, Premise.cover m c c')]
  | .check c P => allRes r b [(Γ ++ [.pre c], .modal m (P ++ ω) ψ), (Γ, c)]
  | .done d => r b Γ ((Premise.done d).fml m ω ψ)
  | .branches bs => allRes r b (bs.map fun o => (Γ, .alls o.1 (.modal m (o.2 ++ ω) ψ)))

/-- **The residue** of `Γ ⟹ φ`: the strategy run as `sol_derive` runs it,
the leaves `close` accepts dropped, and the budget left.  `n` bounds the
steps down any one path, so that the recursion is structural; `b` bounds
the steps of the whole derivation, every branch included, and is handed
from a goal to its next sibling.  `none` when either runs out. -/
def residue : Nat → (List (Hyp C) → Fml C → Bool) → Nat → List (Hyp C) → Fml C →
    Option (List (Leaf C) × Nat)
  | 0, _, _, _, _ => none
  | _ + 1, _, 0, _, _ => none
  | n + 1, close, b + 1, Γ, .modal _ [] ψ => residue n close b Γ ψ
  | n + 1, close, b + 1, Γ, .modal m (s :: ω) ψ =>
    premiseRes (residue n close) b Γ m ω ψ
      (s.step (Hyp.fresh Γ (.modal m (s :: ω) ψ)) m).premise
  | n + 1, close, b + 1, Γ, .imp a ψ => residue n close b (Γ ++ [.pre a]) ψ
  | n + 1, close, b + 1, Γ, .all x p ψ => residue n close b (Γ ++ [.all x p]) ψ
  | n + 1, close, b + 1, Γ, .upd m U ψ => residue n close b (Γ ++ [.upd m U]) ψ
  | _ + 1, close, b + 1, Γ, ψ => if close Γ ψ then some ([], b) else some ([(Γ, ψ)], b)

/-- Nothing is left. -/
def closes (n : Nat) (close : List (Hyp C) → Fml C → Bool) (b : Nat) (Γ : List (Hyp C))
    (φ : Fml C) : Bool :=
  match residue n close b Γ φ with
  | some ([], _) => true
  | _ => false

/-- A precondition the closer sets aside as a formula: `wt(storage)`, an
obligation's premise (`Calculus/Problem.lean`), which the fragment does not
read (the closer reads it as a layout, `Derive.topWt`).  Dropping a
precondition only weakens what is to be shown (`Derive.wrap_dropWt`). -/
def isWt : Hyp C → Bool
  | .pre (.defined (.app1 (.wt _) _)) => true
  | _ => false

/-- The context without its `wt` premises. -/
def dropWt (Γ : List (Hyp C)) : List (Hyp C) := Γ.filter (!isWt ·)

/-! ### Parallel updates, one element at a time

A rule may leave a parallel update, `{ x := x + 1 ‖ r := x + 1 }` of
`r = ++x;`, which `Fml.toL` does not read.  Where its last element binds a
local the others neither read nor write, it is the same as that element
first and the others after it (KeY's `sequentialToParallel`, read
backwards): `{ r := x + 1 }{ x := x + 1 }`.  `Fml.seqUpd` splits every such
update before the closer runs; it only has to imply the leaf. -/

/-- The local an update element binds, for the two kinds the split moves. -/
def _root_.Solidity.UpdElem.target? : UpdElem C → Option Var
  | .val x _ | .path x _ => some x
  | _ => none

/-- A parallel update, its elements reversed (`rs`), as one update per
element from the last, while the last binds a local the rest does not
mention; the rest as one parallel update. -/
def seqRev (m : Modality) (ψ : Fml C) : List (UpdElem C) → Fml C
  | [] => .upd m [] ψ
  | [e] => .upd m [e] ψ
  | e :: rest =>
    match e.target? with
    | some x => if x ∈ Upd.vars rest.reverse then .upd m (e :: rest).reverse ψ
      else .upd m [e] (seqRev m ψ rest)
    | none => .upd m (e :: rest).reverse ψ

/-- Every parallel update split where `seqRev` can, in the positions a leaf
proves (not in a premise). -/
def _root_.Solidity.Fml.seqUpd : Fml C → Fml C
  | .upd m U φ => seqRev m φ.seqUpd U.reverse
  | .imp a φ => .imp a φ.seqUpd
  | .and φ ψ => .and φ.seqUpd ψ.seqUpd
  | .all x p φ => .all x p φ.seqUpd
  | φ => φ

theorem UpdElem.write_lookup {σ₀ τ τ' : State} {x : Var} :
    (e : UpdElem C) → x ∉ e.vars → e.write σ₀ τ = .ok τ' → lookupBy x τ'.env = lookupBy x τ.env
  | .val y t, hx, h | .path y t, hx, h | .mref y t, hx, h | .store y t, hx, h => by
    have hy : x ≠ y := fun e => hx (by simp only [UpdElem.vars, e, List.mem_cons, true_or])
    simp only [UpdElem.write, bind, Except.bind, pure, Except.pure] at h
    repeat' split at h
    all_goals first
      | (cases h; simp only [State.setEnv, SemanticsProperties.lookupBy_setBy_ne hy])
      | cases h
  | .saveNet y, hx, h => by
    have hy : x ≠ y := fun e => hx (by simp only [UpdElem.vars, e, List.mem_cons,
      List.not_mem_nil, or_false])
    simp only [UpdElem.write, pure, Except.pure] at h
    cases h; simp only [State.setEnv, SemanticsProperties.lookupBy_setBy_ne hy]
  | .storage s, _, h | .memory s, _, h | .selfBalance _ s, _, h | .net _ _ s, _, h
  | .pay _ s, _, h => by
    simp only [UpdElem.write, bind, Except.bind, pure, Except.pure] at h
    repeat' split at h
    all_goals first | (cases h; rfl) | cases h

theorem Upd.foldl_lookup {σ₀ : State} {x : Var} :
    (U : Upd C) → x ∉ Upd.vars U → ∀ {τ ρ : State},
      U.foldlM (fun τ e => e.write σ₀ τ) τ = .ok ρ → lookupBy x ρ.env = lookupBy x τ.env
  | [], _, _, _, h => by cases h; rfl
  | e :: U, hx, τ, ρ, h => by
    simp only [Upd.vars, List.mem_append, not_or] at hx
    simp only [List.foldlM_cons] at h
    obtain ⟨τ', h₁, h₂⟩ := SemanticsProperties.Res.bind_eq_ok.1 h
    rw [Upd.foldl_lookup U hx.2 h₂, UpdElem.write_lookup e hx.1 h₁]

theorem afterImp {m : Modality} {p q : State → Prop} {r : Res State} (h : ∀ τ, p τ → q τ) :
    m.after p r → m.after q r := by
  cases r with
  | ok τ => exact h τ
  | error _ => exact id

theorem Upd.apply_single (e : UpdElem C) (σ : State) : Upd.apply [e] σ = e.write σ σ := by
  simp only [Upd.apply, List.foldlM_cons, List.foldlM_nil, bind_pure]

theorem Upd.apply_append_single (P : Upd C) (e : UpdElem C) (σ : State) :
    Upd.apply (P ++ [e]) σ = Upd.apply P σ >>= fun ρ => e.write σ ρ := by
  simp only [Upd.apply, List.foldlM_append, List.foldlM_cons, List.foldlM_nil, bind_pure]

/-- **The last element first**: `{e}{P}ψ` implies `{P ‖ e}ψ` where `e`
binds a local `P` does not mention. -/
theorem peel_sound {m : Modality} {P : Upd C} {e : UpdElem C} {x : Var}
    (he : e.target? = some x) (hx : x ∉ Upd.vars P) {ψ : Fml C} {σ : State}
    (h : holds σ (.upd m [e] (.upd m P ψ))) : holds σ (.upd m (P ++ [e]) ψ) := by
  -- the element writes `x := b`, `b` read in the state it starts from
  obtain ⟨bnd, hw⟩ : ∃ bnd : State → Res Binding, ∀ σ₀ τ,
      e.write σ₀ τ = bnd σ₀ >>= fun b => .ok (τ.setEnv x b) := by
    unfold UpdElem.target? at he
    split at he
    · rename_i y t
      cases he
      exact ⟨fun σ₀ => t.eval σ₀ >>= fun v => .ok (.val v), fun σ₀ τ => by
        simp only [UpdElem.write, bind, Except.bind, pure, Except.pure]
        split <;> rfl⟩
    · rename_i y p
      cases he
      exact ⟨fun σ₀ => p.eval σ₀ >>= fun rs => .ok (.spath rs.1 rs.2), fun σ₀ τ => by
        simp only [UpdElem.write, bind, Except.bind, pure, Except.pure]
        split <;> rfl⟩
    · cases he
  have h' : m.after (fun τ => m.after (fun ρ => holds ρ ψ) (Upd.apply P τ)) (Upd.apply [e] σ) := h
  change m.after (fun ρ => holds ρ ψ) (Upd.apply (P ++ [e]) σ)
  rw [Upd.apply_single, hw] at h'
  rw [Upd.apply_append_single]
  simp only [hw]
  cases hb : bnd σ with
  | error eb =>
    rw [hb] at h'
    cases Upd.apply P σ with
    | error _ => exact h'
    | ok _ => exact h'
  | ok b =>
    rw [hb] at h'
    have h'' : m.after (fun ρ => holds ρ ψ) (Upd.apply P (σ.setEnv x b)) := h'
    have hag : EnvAgreeExcept [x] σ (σ.setEnv x b) :=
      EnvAgreeExcept.setEnv_right ⟨rfl, rfl, rfl, rfl, fun _ _ => rfl, rfl, rfl⟩
        (List.mem_singleton_self x) b
    have hr := Upd.apply_frame hag P (fun y hy hm => by
      rw [List.mem_singleton] at hm; subst hm; exact hx hy)
    have hl : ∀ ρ₁, Upd.apply P (σ.setEnv x b) = .ok ρ₁ →
        lookupBy x ρ₁.env = lookupBy x (σ.setEnv x b).env :=
      fun ρ₁ h₁ => Upd.foldl_lookup P hx h₁
    revert h'' hr hl
    generalize Upd.apply P σ = r₀
    generalize Upd.apply P (σ.setEnv x b) = r₁
    intro h'' hr hl
    match r₀, r₁, hr with
    | .error _, .error _, _ => exact h''
    | .ok _, .error _, hr | .error _, .ok _, hr => exact (nomatch hr)
    | .ok ρ₀, .ok ρ₁, hr =>
      have hl₁ := hl ρ₁ rfl
      have hag' : EnvAgreeExcept [] ρ₁ (ρ₀.setEnv x b) :=
        ⟨hr.storage.symm, hr.heap.symm, hr.nextId.symm, hr.net.symm, fun n _ => by
          by_cases hn : n = x
          · subst hn
            simp only [hl₁, State.setEnv, SemanticsProperties.lookupBy_setBy_self]
          · simp only [State.setEnv, SemanticsProperties.lookupBy_setBy_ne hn]
            exact (hr.env n (by
              simpa only [List.mem_cons, List.not_mem_nil, or_false] using hn)).symm,
          hr.selfBalance.symm, hr.tx.symm⟩
      exact (holds_frame ψ (by intro _ _ hm; simp only [List.not_mem_nil] at hm) hag').1 h''

theorem seqRev_sound {m : Modality} {ψ ψ' : Fml C} (hψ : ∀ σ, holds σ ψ' → holds σ ψ) :
    (rs : List (UpdElem C)) → ∀ σ, holds σ (seqRev m ψ' rs) → holds σ (.upd m rs.reverse ψ)
  | [], σ, h => by
    simp only [seqRev, holds, Upd.apply, List.reverse_nil, List.foldlM_nil] at h ⊢
    exact hψ σ h
  | [e], σ, h => by
    simp only [seqRev, holds, List.reverse_cons, List.reverse_nil, List.nil_append] at h ⊢
    exact afterImp (fun τ => hψ τ) h
  | e :: e' :: rest, σ, h => by
    simp only [seqRev] at h
    split at h
    · rename_i x hx
      split at h
      · exact Hyp.wrap_mono hψ [.upd m _] σ h
      · rename_i hm
        rw [List.reverse_cons]
        refine peel_sound hx hm ?_
        simp only [holds] at h ⊢
        exact afterImp (fun τ hτ => seqRev_sound hψ (e' :: rest) τ hτ) h
    · exact Hyp.wrap_mono hψ [.upd m _] σ h

theorem Fml.seqUpd_sound : (φ : Fml C) → ∀ σ, holds σ φ.seqUpd → holds σ φ
  | .upd m U φ, σ, h => by
    have := seqRev_sound (m := m) (fun τ => Fml.seqUpd_sound φ τ) U.reverse σ h
    rwa [List.reverse_reverse] at this
  | .imp a φ, σ, h => fun ha => Fml.seqUpd_sound φ σ (h ha)
  | .and φ ψ, σ, h => ⟨Fml.seqUpd_sound φ σ h.1, Fml.seqUpd_sound ψ σ h.2⟩
  | .all x p φ, σ, h => fun v hv => Fml.seqUpd_sound φ _ (h v hv)
  | .tt, _, h | .eq .., _, h | .defined _, _, h | .not _, _, h | .modal .., _, h
  | .havoc _, _, h => h

/-- The roots `wt(storage)` names. -/
def wtRoots? : Fml C → Option (List (Name × Ty))
  | .defined (.wt vs .storage) => some vs
  | _ => none

/-- The roots a leaf's first `wt(storage)` premise holds, where only
quantifiers and preconditions come before it (so it speaks of the storage
the leaf starts from); none otherwise. -/
def topWt : List (Hyp C) → List (Name × Ty)
  | [] => []
  | .pre a :: Γ =>
    match wtRoots? a with
    | some vs => vs
    | none => topWt Γ
  | .all _ _ :: Γ => topWt Γ
  | .upd _ _ :: _ | .havoc :: _ => []

/-- The most nodes the closer takes in a leaf's formula with its updates
pushed in, counted as a tree (`LFml.fits`).  A storage written from a read
of the one before it appears twice in the next, so the tree, and the
reduction after it, double with each such write: a leaf of four `count +=
1;` has 1374 nodes and closes in 0.8 s, one of six 5678 nodes; the largest
leaf of solkey's `TestSuite` has 950. -/
def closeSize : Nat := 2000

/-- The default closer: no modality left, in `sol_decide`'s fragment,
parallel updates split (`Fml.seqUpd`), at most `closeSize` nodes, and its
reduction closed by `LFml.close` (`Calculus/Closer.lean`), the `wt`
premises set aside as formulas and read as the layout their storage holds
(`topWt`).  A leaf past the bound is left open, not attempted. -/
def synClose (Γ : List (Hyp C)) (φ : Fml C) : Bool :=
  let w := (Hyp.wrap (dropWt Γ) φ).seqUpd
  let l := w.toL Decide.Sym.empty
  (Hyp.wrap (dropWt Γ) φ).modalFree && w.inL Decide.Sym.empty &&
    (l.fits closeSize).isSome && Decide.LFml.close (topWt Γ) l.elim

/-- The leaf is within `closeSize`, counted as `synClose` counts it: what
`sol_prove?` asks before it tries a step that reduces the leaf, since the
reduction, its quoting and its kernel check heed no heartbeats. -/
def leafFits (Γ : List (Hyp C)) (φ : Fml C) : Bool :=
  ((Hyp.wrap (dropWt Γ) φ).seqUpd.toL Decide.Sym.empty |>.fits closeSize).isSome

/-- The steps `sol_prove` allows, over the whole derivation and so down any
one path: a runaway (a program whose `if`s double the paths) stops here, in
compiled code, before the kernel sees it. -/
def budget : Nat := 20000

/-- `sol_prove`'s check when nothing is left. -/
def proves (Γ : List (Hyp C)) (φ : Fml C) : Bool := closes budget synClose budget Γ φ

/-- The residue quoted, for the tactic: each leaf's context and formula as
the expressions that build them, the contract named by `c`; and the budget
left. -/
def residueQuote (c : Lean.Expr) (Γ : List (Hyp C)) (φ : Fml C) :
    Option (List (Lean.Expr × Lean.Expr) × Nat) :=
  (residue budget synClose budget Γ φ).map fun (ls, b) =>
    (ls.map fun l => (Hyp.quoteList c l.1, Fml.quote c l.2), b)

/-! ## Soundness -/

theorem leaves_nil : ∀ l ∈ ([] : List (Leaf C)), Proves .all l.1 l.2 :=
  fun _ h => nomatch h

theorem leaves_cons {Γ : List (Hyp C)} {φ : Fml C} {ls : List (Leaf C)} (h : Proves .all Γ φ)
    (t : ∀ l ∈ ls, Proves .all l.1 l.2) : ∀ l ∈ (Γ, φ) :: ls, Proves .all l.1 l.2 := by
  intro l hl
  rcases List.mem_cons.1 hl with rfl | hl
  · exact h
  · exact t l hl

/-- Setting the `wt` premises aside keeps a formula modal-free and only
weakens it. -/
theorem wrap_dropWt {φ : Fml C} : (Γ : List (Hyp C)) →
    ((Hyp.wrap (dropWt Γ) φ).modalFree = true → (Hyp.wrap Γ φ).modalFree = true) ∧
      ∀ σ, holds σ (Hyp.wrap (dropWt Γ) φ) → holds σ (Hyp.wrap Γ φ)
  | [] => ⟨id, fun _ => id⟩
  | h :: Γ => by
    obtain ⟨ihm, ihh⟩ := wrap_dropWt (φ := φ) Γ
    cases hw : isWt h with
    | true =>
      have hd : dropWt (h :: Γ) = dropWt Γ := by
        simp only [dropWt, List.filter_cons, hw, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      rw [hd]
      match h, hw with
      | .pre (.defined (.app1 (.wt _) _)), _ =>
        exact ⟨fun hm => by simp only [Hyp.wrap, Fml.modalFree, ihm hm, Bool.and_self],
          fun σ hs _ => ihh σ hs⟩
    | false =>
      have hd : dropWt (h :: Γ) = h :: dropWt Γ := by
        simp only [dropWt, List.filter_cons, hw, Bool.not_false, ↓reduceIte]
      rw [hd]
      cases h with
      | pre a =>
        exact ⟨fun hm => by
            simp only [Hyp.wrap, Fml.modalFree, Bool.and_eq_true] at hm ⊢
            exact ⟨hm.1, ihm hm.2⟩,
          fun σ hs ha => ihh σ (hs ha)⟩
      | upd m U =>
        exact ⟨fun hm => by simpa only [Hyp.wrap, Fml.modalFree] using ihm hm,
          fun σ hs => Hyp.wrap_mono ihh [.upd m U] σ hs⟩
      | havoc =>
        exact ⟨fun hm => by simpa only [Hyp.wrap, Fml.modalFree] using ihm hm,
          fun σ hs => Hyp.wrap_mono ihh [.havoc] σ hs⟩
      | all x p =>
        exact ⟨fun hm => by simpa only [Hyp.wrap, Fml.modalFree] using ihm hm,
          fun σ hs => Hyp.wrap_mono ihh [.all x p] σ hs⟩

/-- `Proves.close` with the `wt` premises set aside: a leaf of an
obligation, closed by a tactic that does not read `wt`. -/
theorem _root_.Solidity.Proves.close_dropWt {R : RuleSet} {Γ : List (Hyp C)} {φ : Fml C}
    (h : Valid (Hyp.wrap (dropWt Γ) φ))
    (hφ : (Hyp.wrap (dropWt Γ) φ).modalFree = true := by first | rfl | decide) :
    Proves R Γ φ :=
  Proves.close (fun σ => (wrap_dropWt Γ).2 σ (h σ)) ((wrap_dropWt Γ).1 hφ)

/-- A `wt(storage)` premise holds of a storage that holds its layout. -/
theorem layoutOk_of_wt {σ : State} {vs : List (Name × Ty)}
    (h : holds σ (.defined (Term.wt vs (C := C) .storage))) : Decide.LayoutOk vs σ := by
  have hw : storageWtB vs σ.storage = true := by
    simp only [holds, Tm.eval, Op1.eval, Op0.eval, pure, Except.pure, bind, Except.bind] at h
    revert h
    cases storageWtB vs σ.storage with
    | true => exact fun _ => rfl
    | false => exact fun ⟨_, h⟩ => (nomatch h)
  simp only [storageWtB, storageShapeB, Bool.and_eq_true, List.all_eq_true] at hw
  intro r T hT
  have := hw.1.2 (r, T) (SemanticsProperties.lookupBy_eq_some_mem hT)
  revert this
  split
  · rename_i v hv
    simp only [Bool.and_eq_true]
    exact fun h => ⟨v, hv, h.1⟩
  · exact fun h => nomatch h

theorem wtRoots?_isWt {a : Fml C} {vs : List (Name × Ty)} (h : wtRoots? a = some vs) :
    isWt (C := C) (.pre a) = true := by
  unfold wtRoots? at h
  split at h
  · rfl
  · cases h

theorem wtRoots?_layout {a : Fml C} {vs : List (Name × Ty)} (h : wtRoots? a = some vs) {σ : State}
    (ha : holds σ a) : Decide.LayoutOk vs σ := by
  unfold wtRoots? at h
  split at h
  · cases h; exact layoutOk_of_wt ha
  · cases h

/-- Reading the `wt` premise as a layout: a leaf whose context without them
holds wherever the storage holds the layout holds. -/
theorem wrap_topWt {φ : Fml C} : (Γ : List (Hyp C)) → ∀ σ,
    (Decide.LayoutOk (topWt Γ) σ → holds σ (Hyp.wrap (dropWt Γ) φ)) → holds σ (Hyp.wrap Γ φ)
  | [], σ, h => h fun _ _ hT => nomatch hT
  | .pre a :: Γ, σ, h => by
    simp only [topWt] at h
    cases hr : wtRoots? a with
    | some vs =>
      have hd : dropWt (.pre a :: Γ) = dropWt Γ := by
        simp only [dropWt, List.filter_cons, wtRoots?_isWt hr, Bool.not_true,
          Bool.false_eq_true, ↓reduceIte]
      rw [hr, hd] at h
      exact fun ha => (wrap_dropWt Γ).2 σ (h (wtRoots?_layout hr ha))
    | none =>
      rw [hr] at h
      cases hw : isWt (C := C) (.pre a) with
      | true =>
        have hd : dropWt (.pre a :: Γ) = dropWt Γ := by
          simp only [dropWt, List.filter_cons, hw, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        rw [hd] at h
        exact fun _ => wrap_topWt Γ σ h
      | false =>
        have hd : dropWt (.pre a :: Γ) = .pre a :: dropWt Γ := by
          simp only [dropWt, List.filter_cons, hw, Bool.not_false, ↓reduceIte]
        rw [hd] at h
        exact fun ha => wrap_topWt Γ σ fun hL => h hL ha
  | .all x p :: Γ, σ, h => fun v hv => wrap_topWt Γ _ fun hL => h hL v hv
  | .upd m U :: Γ, σ, h => (wrap_dropWt (.upd m U :: Γ)).2 σ (h fun _ _ hT => nomatch hT)
  | .havoc :: Γ, σ, h => (wrap_dropWt (.havoc :: Γ)).2 σ (h fun _ _ hT => nomatch hT)

/-- The default closer is sound: what it accepts, `Proves.close` proves. -/
theorem synClose_sound {Γ : List (Hyp C)} {φ : Fml C} (h : synClose Γ φ = true) :
    Proves .all Γ φ := by
  simp only [synClose, Bool.and_eq_true] at h
  obtain ⟨⟨⟨hm, hf⟩, -⟩, hs⟩ := h
  refine Proves.close (fun σ => wrap_topWt Γ σ fun hL => Fml.seqUpd_sound _ σ ?_)
    ((wrap_dropWt Γ).1 hm)
  rw [Decide.Fml.toL_holds _ (Decide.Rel.empty σ) hf, ← Decide.LFml.elim_holds σ]
  exact Decide.LFml.close_holds hL hs

section
variable {r : Nat → List (Hyp C) → Fml C → Option (List (Leaf C) × Nat)}
  (hr : ∀ b Γ φ ls b', r b Γ φ = some (ls, b') → (∀ l ∈ ls, Proves .all l.1 l.2) →
    Proves .all Γ φ)
include hr

theorem allRes_sound : ∀ {b : Nat} {gs ls : List (Leaf C)} {b' : Nat},
    allRes r b gs = some (ls, b') → (∀ l ∈ ls, Proves .all l.1 l.2) →
    ∀ g ∈ gs, Proves .all g.1 g.2
  | _, [], _, _, _, _, _, hg => nomatch hg
  | b, g :: gs, ls, b', h, hl, g', hg' => by
    simp only [allRes] at h
    split at h
    · rename_i a b₁ ha
      split at h
      · rename_i c b₂ hc
        cases h
        rcases List.mem_cons.1 hg' with rfl | hg'
        · exact hr _ _ _ _ _ ha fun l hl' => hl l (List.mem_append_left _ hl')
        · exact allRes_sound hc (fun l hl' => hl l (List.mem_append_right _ hl')) g' hg'
      · cases h
    · cases h

theorem premiseRes_sound {b : Nat} {Γ : List (Hyp C)} {m : Modality} {s : Stmt C}
    {ω : Prog C} {ψ : Fml C} {pr : Premise C} {ls : List (Leaf C)} {b' : Nat}
    (d : Rule C (Hyp.fresh Γ (.modal m (s :: ω) ψ)) m s pr)
    (h : premiseRes r b Γ m ω ψ pr = some (ls, b')) (hl : ∀ l ∈ ls, Proves .all l.1 l.2) :
    Proves .all Γ (.modal m (s :: ω) ψ) := by
  cases pr with
  | update U => exact Proves.updateRule d (hr _ _ _ _ _ h hl)
  | unfold P => exact Proves.unfoldRule d (hr _ _ _ _ _ h hl)
  | split c c' P Q =>
    have hg := allRes_sound hr h hl
    exact Proves.splitRule d (hg _ (.head _)) (hg _ (.tail _ (.head _)))
      (hg _ (.tail _ (.tail _ (.head _))))
  | check c P =>
    have hg := allRes_sound hr h hl
    exact Proves.checkRule d (hg _ (.head _)) (hg _ (.tail _ (.head _)))
  | done e => exact Proves.doneRule d (hr _ _ _ _ _ h hl)
  | branches bs =>
    have hg := allRes_sound hr h hl
    exact Proves.branchesRule d fun o ho => hg (Γ, _) (List.mem_map_of_mem ho)

end

end Derive

open Derive in
/-- **A residue whose leaves are proved proves the sequent.** -/
theorem Proves.of_residue {close : List (Hyp C) → Fml C → Bool}
    (hclose : ∀ Γ φ, close Γ φ = true → Proves .all Γ φ) :
    ∀ {n b : Nat} {Γ : List (Hyp C)} {φ : Fml C} {ls : List (Leaf C)} {b' : Nat},
      residue n close b Γ φ = some (ls, b') → (∀ l ∈ ls, Proves .all l.1 l.2) →
      Proves .all Γ φ
  | 0, _, _, _, _, _, h, _ => nomatch h
  | _ + 1, 0, _, _, _, _, h, _ => nomatch h
  | n + 1, b + 1, Γ, φ, ls, b', h, hl => by
    have ih : ∀ b Γ φ ls b', residue n close b Γ φ = some (ls, b') →
        (∀ l ∈ ls, Proves .all l.1 l.2) → Proves .all Γ φ :=
      fun _ _ _ _ _ h' hl' => Proves.of_residue hclose h' hl'
    match φ, h with
    | .modal _ [] ψ, h => exact .empty (ih _ _ _ _ _ h hl)
    | .modal m (s :: ω) ψ, h =>
      exact premiseRes_sound ih (s.step (Hyp.fresh Γ (.modal m (s :: ω) ψ)) m).rule h hl
    | .imp a ψ, h => exact .intro (ih _ _ _ _ _ h hl)
    | .all x p ψ, h => exact .allIntro (ih _ _ _ _ _ h hl)
    | .upd m U ψ, h => exact .updIntro (ih _ _ _ _ _ h hl)
    | .tt, h | .eq _ _, h | .defined _, h | .not _, h | .and _ _, h | .havoc _, h =>
      simp only [residue] at h
      split at h
      · exact hclose _ _ ‹_›
      · cases h
        exact hl _ (List.mem_singleton_self _)

open Derive in
/-- Nothing left: the strategy and the closer prove the sequent. -/
theorem Proves.of_closes {n : Nat} {close : List (Hyp C) → Fml C → Bool}
    (hclose : ∀ Γ φ, close Γ φ = true → Proves .all Γ φ) {b : Nat} {Γ : List (Hyp C)}
    {φ : Fml C} (h : closes n close b Γ φ = true) : Proves .all Γ φ := by
  simp only [closes] at h
  split at h
  · exact Proves.of_residue hclose ‹_› leaves_nil
  · cases h

/-- `sol_prove`'s proof when nothing is left. -/
theorem Proves.of_proves {Γ : List (Hyp C)} {φ : Fml C} (h : Derive.proves Γ φ = true) :
    Proves .all Γ φ :=
  Proves.of_closes (fun _ _ => Derive.synClose_sound) h

/-- `sol_prove`'s proof when leaves are left. -/
theorem Proves.of_synResidue {Γ : List (Hyp C)} {φ : Fml C} {ls : List (Derive.Leaf C)}
    {b' : Nat} (h : Derive.residue Derive.budget Derive.synClose Derive.budget Γ φ = some (ls, b'))
    (hl : ∀ l ∈ ls, Proves .all l.1 l.2) : Proves .all Γ φ :=
  Proves.of_residue (fun _ _ => Derive.synClose_sound) h hl

/-! ## The tactics -/

namespace Derive

open Lean Elab Tactic Meta

/-- A lemma `type` proved by `value`, checked by the kernel now, as
`decide +kernel` checks one. -/
def kernelLemma (type value : Expr) : MetaM Expr := do
  let n ← withOptions (Elab.async.set · false) <| mkAuxLemma [] type value
  return mkConst n

/-- `sol_prove` on the goal `g`: the goals it leaves, one per residual leaf. -/
def prove (g : MVarId) : MetaM (List MVarId) := do
  let ty ← instantiateMVars (← g.getType)
  let (g, ty) ← match_expr ty with
    | Valid C φ =>
      let ty' := mkAppN (mkConst ``Proves) #[C, mkConst ``RuleSet.all,
        mkApp (mkConst ``List.nil [0]) (mkApp (mkConst ``Hyp) C), φ]
      let g' ← mkFreshExprSyntheticOpaqueMVar ty' (← g.getTag)
      g.assign (mkApp3 (mkConst ``Proves.valid) C φ g')
      pure (g'.mvarId!, ty')
    | _ => pure (g, ty)
  let_expr Proves C R Γ φ := ty | throwError "sol_prove: expected a goal `Γ ⊢ φ` or `⊨ φ`"
  unless R.isConstOf ``RuleSet.all do throwError "sol_prove: proves `⊢`, not `⊢ₖ`"
  let some n := C.constName? | throwError "sol_prove: the contract is not a named constant"
  if Γ.hasFVar || Γ.hasMVar || φ.hasFVar || φ.hasMVar then
    throwError "sol_prove: the sequent mentions a local hypothesis or a metavariable"
  let resTy := mkApp (mkConst ``Option [0]) (mkApp2 (mkConst ``Prod [0, 0])
    (mkApp (mkConst ``List [0])
      (mkApp2 (mkConst ``Prod [0, 0]) (mkConst ``Expr) (mkConst ``Expr)))
    (mkConst ``Nat))
  let some (leaves, left) ← unsafe evalExpr (Option (List (Expr × Expr) × Nat)) resTy
      (mkAppN (mkConst ``residueQuote) #[C, quoteConstName n, Γ, φ])
    | throwError "sol_prove: the derivation takes more than {budget} steps \
        (`Derive.budget`); `sol_derive` builds it one step at a time"
  let bool := mkConst ``Bool
  if leaves.isEmpty then
    let type := mkApp3 (mkConst ``Eq [1]) bool (mkApp3 (mkConst ``proves) C Γ φ)
      (mkConst ``Bool.true)
    let h ← try kernelLemma type (mkApp2 (mkConst ``Eq.refl [1]) bool (mkConst ``Bool.true))
      catch e => throwError "sol_prove: the kernel rejects the derivation:{indentD e.toMessageData}"
    g.assign (mkApp4 (mkConst ``Proves.of_proves) C Γ φ h)
    return []
  let hyp := mkApp (mkConst ``Hyp) C
  let leafTy := mkApp2 (mkConst ``Prod [0, 0]) (mkApp (mkConst ``List [0]) hyp)
    (mkApp (mkConst ``Fml) C)
  let pairs := leaves.map fun (Γ', φ') =>
    mkAppN (mkConst ``Prod.mk [0, 0]) #[mkApp (mkConst ``List [0]) hyp, mkApp (mkConst ``Fml) C,
      Γ', φ']
  let ls ← mkListLit leafTy pairs
  let resTy := mkApp2 (mkConst ``Prod [0, 0]) (mkApp (mkConst ``List [0]) leafTy) (mkConst ``Nat)
  let optTy := mkApp (mkConst ``Option [0]) resTy
  let someLs := mkApp2 (mkConst ``Option.some [0]) resTy
    (mkAppN (mkConst ``Prod.mk [0, 0]) #[mkApp (mkConst ``List [0]) leafTy, mkConst ``Nat, ls,
      mkRawNatLit left])
  let type := mkApp3 (mkConst ``Eq [1]) optTy
    (mkAppN (mkConst ``residue)
      #[C, mkConst ``budget, mkApp (mkConst ``synClose) C, mkConst ``budget, Γ, φ]) someLs
  let h ← try kernelLemma type (mkApp2 (mkConst ``Eq.refl [1]) optTy someLs)
    catch e => throwError "sol_prove: the kernel rejects the residue:{indentD e.toMessageData}"
  let mut goals : Array MVarId := #[]
  let mut proofs : Array Expr := #[]
  for (Γ', φ') in leaves, i in [1:leaves.length + 1] do
    let gi ← mkFreshExprSyntheticOpaqueMVar
      (mkAppN (mkConst ``Proves) #[C, mkConst ``RuleSet.all, Γ', φ']) (Name.mkSimple s!"leaf{i}")
    goals := goals.push gi.mvarId!
    proofs := proofs.push gi
  let mut hl := mkApp (mkConst ``leaves_nil) C
  let mut rest := mkApp (mkConst ``List.nil [0]) leafTy
  for (Γ', φ') in leaves.reverse, p in proofs.reverse do
    hl := mkAppN (mkConst ``leaves_cons) #[C, Γ', φ', rest, p, hl]
    rest := mkAppN (mkConst ``List.cons [0]) #[leafTy,
      mkAppN (mkConst ``Prod.mk [0, 0]) #[mkApp (mkConst ``List [0]) hyp, mkApp (mkConst ``Fml) C,
        Γ', φ'], rest]
  g.assign (mkAppN (mkConst ``Proves.of_synResidue) #[C, Γ, φ, ls, mkRawNatLit left, h, hl])
  return goals.toList

/-- The tactics `sol_prove?` tries on a leaf, in order, each a sequence of
lines: `sol_decide`'s two steps after its `LFml.syn` try, which the closer
subsumes, each on its own so that the replay does not try the other; then
`sol_close` and `sol_spec_close` (`omega`, `grind`).  A leaf past
`closeSize` (`small = false`) gets only the last two, whose `simp`,
`omega` and `grind` heed heartbeats. -/
def leafTacs (wt : Bool := false) (small : Bool := true) : Array (Array String) :=
  let pre := #[if wt then "refine Proves.close_dropWt ?_" else "refine Proves.close ?_",
    "sol_symex"]
  let red := pre ++ #["refine (Fml.valid_iff_reduce _ (by decide +kernel)).2 ?_", "sol_reduce"]
  (if small then #[red.push "sol_decide_cons", red.push "sol_decide_heuristic"] else #[]) ++
    #[pre.push "sol_close", pre.push "sol_spec_close"]

open Lean Meta in
/-- `leafFits` on the leaf goal `l`, run as compiled code; `true` on a goal
that is not a closed `Γ ⊢ φ`. -/
def goalFits (l : MVarId) : MetaM Bool := do
  let ty ← instantiateMVars (← l.getType)
  let_expr Proves C _ Γ φ := ty | return true
  if ty.hasFVar || ty.hasMVar then return true
  unsafe evalExpr Bool (mkConst ``Bool) (mkAppN (mkConst ``leafFits) #[C, Γ, φ])

end Derive

open Lean Elab Tactic Meta in
/-- `sol_prove`: the strategy as one kernel evaluation (`Proves.of_residue`),
on a goal `Γ ⊢ φ` or `⊨ φ`; one goal `leafᵢ` per leaf the closer leaves. -/
elab "sol_prove" : tactic => withMainContext do
  let g ← getMainGoal
  let rest ← getUnsolvedGoals
  let leaves ← Derive.prove g
  setGoals (leaves ++ rest.erase g)

namespace Derive

open Lean Elab Tactic Meta

/-- The first of `leafTacs` that closes the leaf `l`, each try with its own
heartbeats and its state rolled back when it fails; `none` when none does.
A leaf under a `wt` premise is closed with it set aside
(`Proves.close_dropWt`); one past `closeSize` is not reduced (`goalFits`). -/
def searchLeaf (l : MVarId) : TacticM (Option (Array String)) := do
  let env ← getEnv
  let wt := ((← instantiateMVars (← l.getType)).find? fun e =>
    e.isConstOf ``Term.wt || e.isConstOf ``Op1.wt).isSome
  for src in leafTacs wt (← goalFits l) do
    let t ← src.mapM fun line =>
      match Parser.runParserCategory env `tactic line with
      | .ok stx => pure (⟨stx⟩ : TSyntax `tactic)
      | .error e => throwError "sol_prove?: {e}"
    let s ← saveState
    let ok ← tryCatchRuntimeEx
      (withCurrHeartbeats do
        setGoals [l]
        for x in t do Term.withoutErrToSorry (evalTactic x)
        pure (← getUnsolvedGoals).isEmpty)
      fun _ => pure false
    if ok then return some src
    s.restore
  return none

/-- The replay of a `sol_prove` whose leaves are closed by `found`:
`sol_prove`, then each leaf's lines, under `case leafᵢ =>` when there are
several. -/
def replayLines (found : List (Lean.Name × Array String)) : Array String :=
  match found with
  | [(_, body)] => #["sol_prove"] ++ body
  | _ => found.foldl (fun ls (n, body) =>
      (ls.push s!"case {n} =>") ++ body.map ("  " ++ ·)) #["sol_prove"]

end Derive

open Lean Elab Tactic Meta in
/-- `sol_prove?`: `sol_prove`, each leaf closed by the first of
`Derive.leafTacs` that closes it (`Derive.searchLeaf`); suggests the
replay.  A leaf none closes stays a goal, and the first is reported. -/
elab tk:"sol_prove?" : tactic => withMainContext do
  let g ← getMainGoal
  let rest ← getUnsolvedGoals
  let leaves ← Derive.prove g
  let mut found : List (Lean.Name × Array String) := []
  let mut open_ : List MVarId := []
  for l in leaves do
    let name ← l.getTag
    match ← Derive.searchLeaf l with
    | some t => found := found ++ [(name, t)]
    | none =>
      if open_.isEmpty then
        logInfo m!"sol_prove?: no tactic closes {name}:{indentExpr (← l.getType)}"
      open_ := open_ ++ [l]
      found := found ++ [(name, #["sorry"])]
  setGoals (open_ ++ rest.erase g)
  ProofTree.suggest tk (Derive.replayLines found)

end Solidity
