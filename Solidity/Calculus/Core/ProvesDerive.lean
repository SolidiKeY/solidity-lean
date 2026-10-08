import Solidity.Calculus.Core.Derive

/-!
# `sol_prove` on a scoped sequent: `⊢ φ` as one kernel evaluation

`Calculus/Core/Derive.lean`'s `sol_prove` proves `Core.Valid φ`; under
`open scoped Solidity.Core.Surface` an obligation is stated `⊢ φ`, the
scoped sequent `Core.Proves C .all [] .nil φ` (`Calculus/Core/Surface.lean`),
so the strategy has to build a derivation, as today's `Proves.of_residue`
does (`Calculus/Derive.lean`).

`Seq.run` walks the sequent as `Proves` has its rules: `intro`,
`allIntro`, `updIntro`, `bindIntro` take the formula's head into the
context, a modality fires the rule of its first statement (`Stmt.step` at
`Hyps.fresh`, the index the rules ask) and walks each goal its premise
leaves, `empty` goes through the frames, `closeTrue` ends a `true` behind a
box context.  Every other leaf goes to `Proves.close`: `Fml.closableB` of
the sequent, and today's residue of its erasure (`Derive.residue`,
`Calculus/Derive.lean`), each leaf of which is a goal of today's calculus.
`Seq.run_sound` reads the walk back as the derivation; the kernel checks
it as one evaluation (`Seq.residue H φ = some ls`), and the tactic leaves
one goal `leafᵢ` per leaf, as `sol_prove` on `Core.Valid` does.

The walk is generic in what a leaf is (`α`), so the compiled run that
quotes the leaves for the tactic (`Seq.leafQuote`) and the kernel's
(`Seq.leafRes`) are one function.  It is written with `casesOn` (Gate G0,
condition 1); `n` bounds the steps down a path, `b` the steps of the whole
walk, handed from a goal to the next.

**Box contexts only**, as `Proves.close` is: a leaf behind a diamond
update is not `closableB` until `close` reads the typed state
(`docs/intrinsic.md`, W2 `sound`, "Also left, at the flip"), so a diamond
obligation fails here where the `Core.Valid` route proves it.
-/

namespace Solidity.Core

open Solidity (Modality RuleSet)

variable {C : Contract}

namespace Seq

variable {α : Type}

/-- Two goals in turn, the budget the first leaves handed to the second, the
leaves appended. -/
def both (r r' : Nat → Option (List α × Nat)) (b : Nat) : Option (List α × Nat) :=
  match r b with
  | some (l, b') => match r' b' with
    | some (l', b'') => some (l ++ l', b'')
    | none => none
  | none => none

/-- A goal per element, in turn (`both`). -/
def each {β : Type} (f : β → Nat → Option (List α × Nat)) : List β → Nat → Option (List α × Nat)
  | [], b => some ([], b)
  | x :: xs, b => both (f x) (each f xs) b

/-- The goals of a rule's premise, as the `Proves` rule of its kind has
them; `r` walks a goal. -/
def premise (r : {Γ : Ctx} → Hyps C [] Γ → Fml C Γ → Nat → Option (List α × Nat))
    {Γ Γ' Γ₁ Γ₂ : Ctx} (H : Hyps C [] Γ) (m : Modality) (ω : Prog C Γ' Γ₁)
    (κ : Frames C Γ₁ Γ₂) (φ : Fml C Γ₂) (p : Premise C Γ Γ') (b : Nat) :
    Option (List α × Nat) :=
  Premise.casesOn (motive := fun Γ' _ => Prog C Γ' Γ₁ → Option (List α × Nat)) p
    (fun U ω => r (H.upd m U) (.modalK m ω κ φ) b)
    (fun P e ω => r H (.modal m P (.pop .capture e (.seq ω κ)) φ) b)
    (fun x t P ω => r (H.bind m x t) (.modal m P (.seq ω κ) φ) b)
    (fun bk c c' P Q ω => both (r (H.pre c) (.modalK m P (.pop bk P.ext (.seq ω κ)) φ))
      (r (H.pre c') (.modalK m Q (.pop bk Q.ext (.seq ω κ)) φ)) b)
    (fun c ω => both (r (H.pre c) (.modalK m ω κ φ)) (r H c) b)
    (fun bo _ => r H (if bo then .tt else .ff) b)
    (fun bs ω => cond bs.isEmpty none (each (fun br => r H (br.bs.all
      (.modalK m br.P (.pop .block ((Ext.append Γ br.ρ).trans br.P.ext) (.seq ω κ)) φ))) bs b))
    (fun fs us ω => cond (fs.isEmpty && us.isEmpty) none
      (both (each (fun f => r H f) fs) (each (fun U => r (H.upd m U) (.modalK m ω κ φ)) us) b))
    (fun I xs hv U c c' hu hb P post ω => both (r H I)
      (both (r ((((H.anonHavoc xs hv).pre I).upd m U).pre c)
          (.upd m (Upd.nil.pop hb) (.modalK m P (.pop .block P.ext .nil) post)))
        (r ((((H.anonHavoc xs hv).pre I).upd m U).pre c')
          (.upd m (Upd.nil.pop (hu.trans hb)) (.modalK m ω κ φ)))) b)
    (fun P e ω => r H (.modal m P (.drop e (.seq ω κ)) φ) b) ω

/-- A modality: the frames when the program is done (`empty`), else the rule
of the first statement and its premise's goals. -/
def modal (r : {Γ : Ctx} → Hyps C [] Γ → Fml C Γ → Nat → Option (List α × Nat))
    (m : Modality) {Γ Γ₁ Γ₀ : Ctx} (H : Hyps C [] Γ) (P : Prog C Γ Γ₁) (κ : Frames C Γ₁ Γ₀)
    (φ : Fml C Γ₀) (b : Nat) : Option (List α × Nat) :=
  Prog.casesOn (motive_2 := fun Γ Γ₁ _ => Frames C Γ₁ Γ₀ → Hyps C [] Γ → Option (List α × Nat)) P
    (fun κ H => r H (κ.exit m φ) b)
    (fun s ω κ H => match s.step (H.fresh (.modal m (.cons s ω) κ φ)) m with
      | some p => premise r H m ω κ φ p b
      | none => none) κ H

/-- The walk of the sequent `H ⊢ φ`: the leaves `leaf` leaves, or `none`
when a step has no rule, a leaf does not close, or `n` or `b` runs out. -/
def run (leaf : {Γ : Ctx} → Hyps C [] Γ → Fml C Γ → Option (List α)) :
    Nat → {Γ : Ctx} → Hyps C [] Γ → Fml C Γ → Nat → Option (List α × Nat)
  | 0, _, _, _, _ => none
  | _ + 1, _, _, _, 0 => none
  | n + 1, _, H, φ, b + 1 =>
    Fml.casesOn (motive := fun Γ _ => Hyps C [] Γ → Option (List α × Nat)) φ
      (tt := fun H => cond H.boxOnly (some ([], b)) ((leaf H .tt).map (·, b)))
      (eq := fun t u H => (leaf H (.eq t u)).map (·, b))
      (defined := fun t H => (leaf H (.defined t)).map (·, b))
      (not := fun ψ H => (leaf H (.not ψ)).map (·, b))
      (and := fun ψ χ H => (leaf H (.and ψ χ)).map (·, b))
      (imp := fun a ψ H => run leaf n (H.pre a) ψ b)
      (upd := fun m U ψ H => run leaf n (H.upd m U) ψ b)
      (modal := fun m P κ ψ H => modal (fun H φ b => run leaf n H φ b) m H P κ ψ b)
      (havoc := fun ψ H => (leaf H (.havoc ψ)).map (·, b))
      (all := fun x p ψ H => run leaf n (H.all x p) ψ b)
      (bind := fun m x t ψ H => run leaf n (H.bind m x t) ψ b)
      (anon := fun xs ψ H => (leaf H (.anon xs ψ)).map (·, b)) H

/-- A leaf for the kernel: `Proves.close`'s side condition, and today's
residue of its erasure. -/
def leafRes {Γ : Ctx} (H : Hyps C [] Γ) (φ : Fml C Γ) : Option (List (Solidity.Derive.Leaf C)) :=
  cond ((H.wrap φ).closableB [])
    ((Solidity.Derive.residue Solidity.Derive.budget Solidity.Derive.synClose
      Solidity.Derive.budget [] ((H.wrap φ).erase [])).map (·.1)) none

/-- The same leaf quoted, for the tactic (`Derive.residueQuote`), the
contract named by `c`. -/
def leafQuote (c : Lean.Expr) {Γ : Ctx} (H : Hyps C [] Γ) (φ : Fml C Γ) :
    Option (List (Lean.Expr × Lean.Expr)) :=
  cond ((H.wrap φ).closableB [])
    ((Solidity.Derive.residueQuote c [] ((H.wrap φ).erase [])).map (·.1)) none

/-- The steps the walk is given, down a path and in all (today's
`Derive.budget`). -/
def fuel : Nat := Solidity.Derive.budget

/-- **`sol_prove`'s check**: the leaves of today's calculus the walk leaves,
none when every leaf closes. -/
def residue {Γ : Ctx} (H : Hyps C [] Γ) (φ : Fml C Γ) : Option (List (Solidity.Derive.Leaf C)) :=
  (run leafRes fuel H φ fuel).map (·.1)

/-- `residue`, the leaves quoted. -/
def residueQuote (c : Lean.Expr) {Γ : Ctx} (H : Hyps C [] Γ) (φ : Fml C Γ) :
    Option (List (Lean.Expr × Lean.Expr)) :=
  (run (leafQuote c) fuel H φ fuel).map (·.1)

/-! ## Soundness -/

section Sound

variable {P : α → Prop}

theorem both_sound {r r' : Nat → Option (List α × Nat)} {A B : Prop}
    {b : Nat} {ls : List α} {b' : Nat} (h : both r r' b = some (ls, b'))
    (hl : ∀ l ∈ ls, P l)
    (hr : ∀ b ls b', r b = some (ls, b') → (∀ l ∈ ls, P l) → A)
    (hr' : ∀ b ls b', r' b = some (ls, b') → (∀ l ∈ ls, P l) → B) : A ∧ B := by
  unfold both at h
  split at h
  · rename_i l b₁ h₁
    split at h
    · rename_i l' b₂ h₂
      cases h
      exact ⟨hr _ _ _ h₁ fun x hx => hl x (List.mem_append_left _ hx),
        hr' _ _ _ h₂ fun x hx => hl x (List.mem_append_right _ hx)⟩
    · cases h
  · cases h

theorem each_sound {β : Type} {f : β → Nat → Option (List α × Nat)} {Q : β → Prop} :
    ∀ {xs : List β} {b : Nat} {ls : List α} {b' : Nat}, each f xs b = some (ls, b') →
      (∀ l ∈ ls, P l) → (∀ x b ls b', f x b = some (ls, b') → (∀ l ∈ ls, P l) → Q x) →
      ∀ x ∈ xs, Q x
  | [], _, _, _, _, _, _ => fun _ h => nomatch h
  | x :: xs, _, _, _, h, hl, hf => by
    have := both_sound h hl (hf x) (fun _ _ _ h' hl' => each_sound (xs := xs) h' hl' hf)
    intro y hy
    rcases List.mem_cons.1 hy with rfl | hy
    · exact this.1
    · exact this.2 y hy

variable {R : RuleSet}

theorem premise_sound {r : {Γ : Ctx} → Hyps C [] Γ → Fml C Γ → Nat → Option (List α × Nat)}
    (hr : ∀ {Γ : Ctx} (H : Hyps C [] Γ) (φ : Fml C Γ) b ls b', r H φ b = some (ls, b') →
      (∀ l ∈ ls, P l) → Proves C R [] H φ)
    {Γ Γ' Γ₁ Γ₂ : Ctx} (H : Hyps C [] Γ) (m : Modality) (s : Stmt C Γ Γ') (ω : Prog C Γ' Γ₁)
    (κ : Frames C Γ₁ Γ₂) (φ : Fml C Γ₂) (p : Premise C Γ Γ')
    (d : s.step (H.fresh (.modal m (.cons s ω) κ φ)) m = some p) {b : Nat} {ls : List α}
    {b' : Nat} (h : premise r H m ω κ φ p b = some (ls, b')) (hl : ∀ l ∈ ls, P l) :
    Proves C R [] H (.modal m (.cons s ω) κ φ) := by
  cases p with
  | update U => exact .update d (hr _ _ _ _ _ h hl)
  | unfold P e => exact .unfold d (hr _ _ _ _ _ h hl)
  | bind x t P => exact .bind d (hr _ _ _ _ _ h hl)
  | split bk c c' P Q =>
    have := both_sound h hl (hr _ _) (hr _ _)
    exact .split d this.1 this.2
  | check c =>
    have := both_sound h hl (hr _ _) (hr _ _)
    exact .check d this.1 this.2
  | done bo => exact .done d (hr _ _ _ _ _ h hl)
  | branches bs =>
    cases hb : bs.isEmpty
    · simp only [premise, hb, cond_false] at h
      exact .branches d hb (each_sound h hl fun _ _ _ _ => hr _ _ _ _ _)
    · simp only [premise, hb, cond_true, reduceCtorEq] at h
  | cases fs us =>
    cases hb : (fs.isEmpty && us.isEmpty)
    · simp only [premise, hb, cond_false] at h
      have := both_sound h hl
        (fun _ _ _ h₁ hl₁ => each_sound h₁ hl₁ fun _ _ _ _ => hr _ _ _ _ _)
        (fun _ _ _ h₁ hl₁ => each_sound h₁ hl₁ fun _ _ _ _ => hr _ _ _ _ _)
      exact .cases d hb this.1 this.2
    · simp only [premise, hb, cond_true, reduceCtorEq] at h
  | inv I xs hv U c c' hu hb P post =>
    have := both_sound h hl (hr _ _)
      (fun _ _ _ h₁ hl₁ => both_sound h₁ hl₁ (hr _ _) (hr _ _))
    exact .inv d this.1 this.2.1 this.2.2
  | inline P e => exact .inline d (hr _ _ _ _ _ h hl)

variable {leaf : {Γ : Ctx} → Hyps C [] Γ → Fml C Γ → Option (List α)}
  (hleaf : ∀ {Γ : Ctx} (H : Hyps C [] Γ) (φ : Fml C Γ) ls, leaf H φ = some ls →
    (∀ l ∈ ls, P l) → Proves C R [] H φ)
include hleaf

theorem leaf_sound {Γ : Ctx} {H : Hyps C [] Γ} {φ : Fml C Γ} {b : Nat} {ls : List α} {b' : Nat}
    (h : (leaf H φ).map (·, b) = some (ls, b')) (hl : ∀ l ∈ ls, P l) : Proves C R [] H φ := by
  obtain ⟨ls', h', he⟩ := Option.map_eq_some_iff.1 h
  cases he
  exact hleaf H φ _ h' hl

/-- **The walk is a derivation.** -/
theorem run_sound : ∀ (n : Nat) {Γ : Ctx} (H : Hyps C [] Γ) (φ : Fml C Γ) (b : Nat)
    (ls : List α) (b' : Nat), run leaf n H φ b = some (ls, b') → (∀ l ∈ ls, P l) →
    Proves C R [] H φ
  | 0, _, _, _, _, _, _, h, _ => by simp only [run, reduceCtorEq] at h
  | _ + 1, _, _, _, 0, _, _, h, _ => by simp only [run, reduceCtorEq] at h
  | n + 1, _, H, φ, b + 1, ls, b', h, hl => by
    have ih : ∀ {Γ : Ctx} (H : Hyps C [] Γ) (φ : Fml C Γ) b ls b', run leaf n H φ b = some (ls, b') →
        (∀ l ∈ ls, P l) → Proves C R [] H φ :=
      fun H φ b ls b' h hl => run_sound n H φ b ls b' h hl
    cases φ with
    | tt =>
      cases hb : H.boxOnly
      · exact leaf_sound hleaf (b := b) (by simpa only [run, hb, cond_false] using h) hl
      · exact .closeTrue hb
    | eq => exact leaf_sound hleaf h hl
    | defined => exact leaf_sound hleaf h hl
    | not => exact leaf_sound hleaf h hl
    | and => exact leaf_sound hleaf h hl
    | imp a ψ => exact .intro (ih _ _ _ _ _ h hl)
    | upd m U ψ => exact .updIntro (ih _ _ _ _ _ h hl)
    | modal m P κ ψ =>
      cases P with
      | nil => exact .empty (ih _ _ _ _ _ h hl)
      | cons s ω =>
        change (match s.step (H.fresh (.modal m (.cons s ω) κ ψ)) m with
          | some p => premise (fun H φ b => run leaf n H φ b) H m ω κ ψ p b
          | none => none) = some (ls, b') at h
        split at h
        · rename_i p hp
          exact premise_sound ih H m s ω κ ψ p hp h hl
        · cases h
    | havoc => exact leaf_sound hleaf h hl
    | all x p ψ => exact .allIntro (ih _ _ _ _ _ h hl)
    | bind m x t ψ => exact .bindIntro (ih _ _ _ _ _ h hl)
    | anon => exact leaf_sound hleaf h hl

end Sound

/-- A leaf `leafRes` takes is proved once today's leaves are. -/
theorem leafRes_sound {R : RuleSet} {Γ : Ctx} (H : Hyps C [] Γ) (φ : Fml C Γ)
    (ls : List (Solidity.Derive.Leaf C)) (h : leafRes H φ = some ls)
    (hl : ∀ l ∈ ls, Solidity.Proves .all l.1 l.2) : Proves C R [] H φ := by
  unfold leafRes at h
  cases hc : (H.wrap φ).closableB [] with
  | false => simp only [hc, cond_false, reduceCtorEq] at h
  | true =>
    simp only [hc, cond_true] at h
    obtain ⟨⟨ls', b'⟩, hr, he⟩ := Option.map_eq_some_iff.1 h
    cases he
    exact Proves.close [] rfl List.nodup_nil
      (Solidity.Proves.valid (Solidity.Proves.of_synResidue hr hl)) hc
      (fun _ _ h => nomatch h)

end Seq

/-- **`sol_prove`'s proof of a sequent**: the walk's residue, each of
today's leaves proved. -/
theorem Proves.of_residue {R : RuleSet} {Γ : Ctx} {H : Hyps C [] Γ} {φ : Fml C Γ}
    {ls : List (Solidity.Derive.Leaf C)} (h : Seq.residue H φ = some ls)
    (hl : ∀ l ∈ ls, Solidity.Proves .all l.1 l.2) : Proves C R [] H φ := by
  obtain ⟨⟨ls', b'⟩, hr, he⟩ := Option.map_eq_some_iff.1 h
  cases he
  exact Seq.run_sound (P := fun l => Solidity.Proves .all l.1 l.2)
    (fun H φ ls h hl => Seq.leafRes_sound H φ ls h hl) _ H φ _ _ _ hr hl

/-! ## The tactic -/

namespace Seq

open Lean Elab Tactic Meta

/-- `sol_prove` on the goal `g`, `Core.Proves C R [] H φ`: the goals it
leaves, one per leaf of today's residue. -/
def prove (g : MVarId) (C R Γ H φ : Expr) : MetaM (List MVarId) := do
  let some n := C.constName? | throwError "sol_prove: the contract is not a named constant"
  if H.hasFVar || H.hasMVar || φ.hasFVar || φ.hasMVar then
    throwError "sol_prove: the sequent mentions a local hypothesis or a metavariable"
  let hyp := mkApp (mkConst ``Solidity.Hyp) C
  let leafTy := mkApp2 (mkConst ``Prod [0, 0]) (mkApp (mkConst ``List [0]) hyp)
    (mkApp (mkConst ``Solidity.Fml) C)
  let resTy := mkApp (mkConst ``Option [0]) (mkApp (mkConst ``List [0]) leafTy)
  let lemmaFor (ls : Expr) : MetaM Expr := do
    let someLs := mkApp2 (mkConst ``Option.some [0]) (mkApp (mkConst ``List [0]) leafTy) ls
    let type := mkApp3 (mkConst ``Eq [1]) resTy (mkAppN (mkConst ``residue) #[C, Γ, H, φ]) someLs
    Solidity.Derive.kernelLemma type (mkApp2 (mkConst ``Eq.refl [1]) resTy someLs)
  let assignWith (ls h : Expr) (hl : Expr) : MetaM Unit :=
    g.assign (mkAppN (mkConst ``Proves.of_residue) #[C, R, Γ, H, φ, ls, h, hl])
  -- the kernel first: most obligations leave nothing
  let nil := mkApp (mkConst ``List.nil [0]) leafTy
  if let some h ← (some <$> lemmaFor nil) <|> pure none then
    assignWith nil h (mkApp (mkConst ``Solidity.Derive.leaves_nil) C)
    return []
  let qTy := mkApp (mkConst ``Option [0]) (mkApp (mkConst ``List [0])
    (mkApp2 (mkConst ``Prod [0, 0]) (mkConst ``Expr) (mkConst ``Expr)))
  let some leaves ← unsafe evalExpr (Option (List (Expr × Expr))) qTy
      (mkAppN (mkConst ``residueQuote) #[C, quoteConstName n, Γ, H, ← Symex.evaluable φ])
    | throwError "sol_prove: the walk does not reach the end of the sequent: a step with no \
        rule, a leaf `Proves.close` does not take (`Fml.closableB`: a leaf behind a diamond \
        update), or more than {fuel} steps"
  let mkLeaf (Γ' φ' : Expr) : Expr :=
    mkAppN (mkConst ``Prod.mk [0, 0]) #[mkApp (mkConst ``List [0]) hyp,
      mkApp (mkConst ``Solidity.Fml) C, Γ', φ']
  let ls ← mkListLit leafTy (leaves.map fun (Γ', φ') => mkLeaf Γ' φ')
  let h ← try lemmaFor ls
    catch e => throwError "sol_prove: the kernel rejects the residue:{indentD e.toMessageData}"
  let mut goals : Array MVarId := #[]
  let mut proofs : Array Expr := #[]
  for (Γ', φ') in leaves, i in [1:leaves.length + 1] do
    let gi ← mkFreshExprSyntheticOpaqueMVar
      (mkAppN (mkConst ``Solidity.Proves) #[C, mkConst ``RuleSet.all, Γ', φ'])
      (Name.mkSimple s!"leaf{i}")
    goals := goals.push gi.mvarId!
    proofs := proofs.push gi
  let mut hl := mkApp (mkConst ``Solidity.Derive.leaves_nil) C
  let mut rest := nil
  for (Γ', φ') in leaves.reverse, p in proofs.reverse do
    hl := mkAppN (mkConst ``Solidity.Derive.leaves_cons) #[C, Γ', φ', rest, p, hl]
    rest := mkAppN (mkConst ``List.cons [0]) #[leafTy, mkLeaf Γ' φ', rest]
  assignWith ls h hl
  return goals.toList

end Seq

open Lean Elab Tactic Meta in
/-- `sol_prove` on a scoped sequent `H ⊢ φ` (`Core.Proves C R [] H φ`,
`⊢ φ` under `open scoped Solidity.Core.Surface`): the walk as one kernel
evaluation (`Proves.of_residue`), one goal `leafᵢ` per leaf today's closer
leaves. -/
@[tactic Solidity.tacticSol_prove]
def evalSolProveSeq : Tactic := fun _ => withMainContext do
  let g ← getMainGoal
  let ty ← instantiateMVars (← g.getType)
  let_expr Core.Proves C R Γ₀ Γ H φ := ty | throwUnsupportedSyntax
  unless (← whnfR Γ₀).isAppOf ``List.nil do throwUnsupportedSyntax
  let rest := (← getUnsolvedGoals).erase g
  Symex.reporting g do
    let leaves ← Seq.prove g C R Γ H φ
    setGoals (leaves ++ rest)

end Solidity.Core
