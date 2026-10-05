import Solidity.Calculus.DecideComplete
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

The default closer (`Derive.synClose`) is `sol_decide`'s first try,
`LFml.syn` on the reduction (`Calculus/DecideSyn.lean`): it closes a leaf
inside the `Bool`.  A leaf it does not close is left for a tactic.

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
  `LFml.syn` (which the closer has already tried), then `sol_close`, then
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

/-- A precondition the closer sets aside: `wt(storage)`, a diamond
obligation's premise (`Calculus/Problem.lean`), which `LFml.syn` does not
read.  Dropping a precondition only weakens what is to be shown
(`Derive.wrap_dropWt`). -/
def isWt : Hyp C → Bool
  | .pre (.defined (.app1 (.wt _) _)) => true
  | _ => false

/-- The context without its `wt` premises. -/
def dropWt (Γ : List (Hyp C)) : List (Hyp C) := Γ.filter (!isWt ·)

/-- The default closer: no modality left, in `sol_decide`'s fragment, and
its reduction closed by its terms (`LFml.syn`), the `wt` premises set
aside. -/
def synClose (Γ : List (Hyp C)) (φ : Fml C) : Bool :=
  let w := Hyp.wrap (dropWt Γ) φ
  w.modalFree && w.inL Decide.Sym.empty && w.reduce.syn [] []

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

/-- `Proves.close` with the `wt` premises set aside: a leaf of a diamond
obligation, closed by a tactic that does not read `wt`. -/
theorem _root_.Solidity.Proves.close_dropWt {R : RuleSet} {Γ : List (Hyp C)} {φ : Fml C}
    (h : Valid (Hyp.wrap (dropWt Γ) φ))
    (hφ : (Hyp.wrap (dropWt Γ) φ).modalFree = true := by first | rfl | decide) :
    Proves R Γ φ :=
  Proves.close (fun σ => (wrap_dropWt Γ).2 σ (h σ)) ((wrap_dropWt Γ).1 hφ)

/-- The default closer is sound: what it accepts, `Proves.close` proves. -/
theorem synClose_sound {Γ : List (Hyp C)} {φ : Fml C} (h : synClose Γ φ = true) :
    Proves .all Γ φ := by
  simp only [synClose, Bool.and_eq_true] at h
  obtain ⟨⟨hm, hf⟩, hs⟩ := h
  have hv : Valid (Hyp.wrap (dropWt Γ) φ) :=
    (Fml.valid_iff_reduce _ hf).2 (Decide.LFml.syn_valid _ hs)
  exact Proves.close (fun σ => (wrap_dropWt Γ).2 σ (hv σ)) ((wrap_dropWt Γ).1 hm)

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
has already made, each on its own so that the replay does not try the
other; then `sol_close` and `sol_spec_close` (`omega`, `grind`). -/
def leafTacs (wt : Bool := false) : Array (Array String) :=
  let pre := #[if wt then "refine Proves.close_dropWt ?_" else "refine Proves.close ?_",
    "sol_symex"]
  let red := pre ++ #["refine (Fml.valid_iff_reduce _ (by decide +kernel)).2 ?_", "sol_reduce"]
  #[red.push "sol_decide_cons", red.push "sol_decide_heuristic", pre.push "sol_close",
    pre.push "sol_spec_close"]

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
(`Proves.close_dropWt`). -/
def searchLeaf (l : MVarId) : TacticM (Option (Array String)) := do
  let env ← getEnv
  let wt := ((← instantiateMVars (← l.getType)).find? fun e =>
    e.isConstOf ``Term.wt || e.isConstOf ``Op1.wt).isSome
  for src in leafTacs wt do
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
