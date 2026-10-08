import Solidity.Calculus.Core.Derive

/-!
# `sol_prove` on a scoped sequent, as one kernel evaluation

`⊢ φ` under `open scoped Solidity.Core.Surface` is the scoped sequent
`Core.Proves C .all [] .nil φ`.  `sol_prove` proves it as `Derive.lean`'s
`sol_prove` proves today's `⊢ φ`: a Boolean run of the derivation, checked by
the kernel (`Eq.refl`), and a theorem that a run that succeeds is a
derivation (`Proves.of_seqRes`).

The run (`Derive.seqRes`) takes the walk's steps (`Calculus/Core/Derive.lean`,
`Walk.movesAt`): a precondition, a quantifier, an update or a hidden binder
into the context, an empty modality through its frames, the statement's rule
(`Stmt.step`, the one rule there is, by its premise's kind:
`Derive.premRes`), `closeTrue` behind a box context.  Any other goal is a
leaf, closed by `Proves.close` on its erasure where `Fml.closableB` takes it,
the parameters' quantifiers stripped (`Fml.stripAlls`, so a leaf reads as
today's, its parameters free), and handed to today's closer
(`Solidity.Derive.residue`).  What today's closer leaves is left as goals
`leaf1`, `leaf2`, … of today's calculus, as today's `sol_prove` leaves them.
-/

namespace Solidity

variable {C : Contract}

/-- Today's formula without its leading quantifiers. -/
def Fml.stripAlls : Fml C → Fml C
  | .all _ _ φ => φ.stripAlls
  | φ => φ

/-- A formula is valid where it is with its leading quantifiers' locals free. -/
theorem Valid.of_stripAlls : {φ : Fml C} → Valid φ.stripAlls → Valid φ
  | .all x p φ, h => Valid.all_of_free x p (Valid.of_stripAlls (φ := φ) h)
  | .tt, h | .eq _ _, h | .not _, h | .and _ _, h | .imp _ _, h
  | .modal _ _ _, h | .upd _ _ _, h | .havoc _, h | .anon _ _, h | .defined _, h => h

end Solidity

namespace Solidity.Core

open Solidity (Modality RuleSet)

variable {C : Contract}

namespace Derive

/-- The leaves left of a list of runs, `none` when one fails. -/
def allOf : List (Option (List (Solidity.Derive.Leaf C))) → Option (List (Solidity.Derive.Leaf C))
  | [] => some []
  | none :: _ => none
  | some l :: os => (allOf os).map (l ++ ·)

/-- A leaf: closed by `Proves.close` where its erasure gives it, today's
closer on the erasure, its parameters free. -/
def leafRes {Γ : Ctx} (H : Hyps C [] Γ) (φ : Fml C Γ) :
    Option (List (Solidity.Derive.Leaf C)) :=
  if (H.wrap φ).closableB [] then
    (Solidity.Derive.residue Solidity.Derive.budget Solidity.Derive.synClose
      Solidity.Derive.budget [] ((H.wrap φ).erase []).stripAlls).map (·.1)
  else none

/-- The goals a premise leaves, each run by `r`: `Proves`' rule of its kind. -/
def premRes (r : {Γ : Ctx} → Hyps C [] Γ → Fml C Γ → Option (List (Solidity.Derive.Leaf C)))
    {Γ : Ctx} (H : Hyps C [] Γ) (m : Modality) :
    {Γ' Γ₁ Γ₂ : Ctx} → Premise C Γ Γ' → Prog C Γ' Γ₁ → Frames C Γ₁ Γ₂ → Fml C Γ₂ →
      Option (List (Solidity.Derive.Leaf C))
  | _, _, _, .update U, ω, κ, φ => r (H.upd m U) (.modalK m ω κ φ)
  | _, _, _, .unfold P e, ω, κ, φ => r H (.modal m P (.pop .capture e (.seq ω κ)) φ)
  | _, _, _, .bind x t P, ω, κ, φ => r (H.bind m x t) (.modal m P (.seq ω κ) φ)
  | _, _, _, .split b c c' P Q, ω, κ, φ =>
    allOf [r (H.pre c) (.modalK m P (.pop b P.ext (.seq ω κ)) φ),
      r (H.pre c') (.modalK m Q (.pop b Q.ext (.seq ω κ)) φ)]
  | _, _, _, .check c, ω, κ, φ => allOf [r (H.pre c) (.modalK m ω κ φ), r H c]
  | _, _, _, .done b, _, _, _ => r H (if b then .tt else .ff)
  | _, _, _, .branches bs, ω, κ, φ =>
    if bs.isEmpty then none else
      allOf (bs.map fun b =>
        r H (b.bs.all (.modalK m b.P (.pop .block ((Ext.append Γ b.ρ).trans b.P.ext)
          (.seq ω κ)) φ)))
  | _, _, _, .cases fs us, ω, κ, φ =>
    if fs.isEmpty && us.isEmpty then none else
      allOf (fs.map (r H ·) ++ us.map fun U => r (H.upd m U) (.modalK m ω κ φ))
  | _, _, _, .inv I xs hv U c c' hu hb P post, ω, κ, φ =>
    allOf [r H I,
      r ((((H.anonHavoc xs hv).pre I).upd m U).pre c)
        (.upd m (Upd.nil.pop hb) (.modalK m P (.pop .block P.ext .nil) post)),
      r ((((H.anonHavoc xs hv).pre I).upd m U).pre c')
        (.upd m (Upd.nil.pop (hu.trans hb)) (.modalK m ω κ φ))]
  | _, _, _, .inline P e, ω, κ, φ => r H (.modal m P (.drop e (.seq ω κ)) φ)

/-- **The run of `H ⊢ φ`**: the walk's steps, `n` of them down any path, the
leaves today's closer leaves of the erasures; `none` where a leaf is not
closable or the steps run out. -/
def seqRes : Nat → {Γ : Ctx} → Hyps C [] Γ → Fml C Γ → Option (List (Solidity.Derive.Leaf C))
  | 0, _, _, _ => none
  | n + 1, _, H, .imp a ψ => seqRes n (H.pre a) ψ
  | n + 1, _, H, .all x p ψ => seqRes n (H.all x p) ψ
  | n + 1, _, H, .upd m U ψ => seqRes n (H.upd m U) ψ
  | n + 1, _, H, .bind m x t ψ => seqRes n (H.bind m x t) ψ
  | _ + 1, _, H, .tt => if H.boxOnly then some [] else leafRes H .tt
  | n + 1, _, H, .modal m .nil κ ψ => seqRes n H (κ.exit m ψ)
  | n + 1, _, H, .modal m (.cons s ω) κ ψ =>
    match s.step (H.fresh (.modal m (.cons s ω) κ ψ)) m with
    | some p => premRes (seqRes n) H m p ω κ ψ
    | none => none
  | _ + 1, _, H, ψ => leafRes H ψ

/-- The quoted leaves of the run, for the tactic (`Hyp.quoteList`,
`Fml.quote`), the contract named by `c`. -/
def seqResQuote (c : Lean.Expr) (φ : Fml C []) : Option (List (Lean.Expr × Lean.Expr)) :=
  (seqRes fuel .nil φ).map fun ls =>
    ls.map fun l => (Solidity.Hyp.quoteList c l.1, Solidity.Fml.quote c l.2)

/-! ## Soundness -/

theorem allOf_sub : {os : List (Option (List (Solidity.Derive.Leaf C)))} →
    {ls : List (Solidity.Derive.Leaf C)} → allOf os = some ls →
    ∀ o ∈ os, ∃ l, o = some l ∧ ∀ x ∈ l, x ∈ ls
  | [], _, _, _, h => nomatch h
  | none :: _, _, h, _, _ => nomatch h
  | some l :: os, ls, h, o, ho => by
    simp only [allOf, Option.map_eq_some_iff] at h
    obtain ⟨ls', hs, rfl⟩ := h
    rcases List.mem_cons.1 ho with rfl | ho
    · exact ⟨l, rfl, fun x hx => List.mem_append_left _ hx⟩
    · obtain ⟨l', rfl, hl'⟩ := allOf_sub hs o ho
      exact ⟨l', rfl, fun x hx => List.mem_append_right _ (hl' x hx)⟩

/-- What the leaves of a run give. -/
abbrev LeavesOk (ls : List (Solidity.Derive.Leaf C)) : Prop :=
  ∀ l ∈ ls, Solidity.Proves .all l.1 l.2

theorem LeavesOk.sub {ls ls' : List (Solidity.Derive.Leaf C)} (h : LeavesOk ls')
    (hs : ∀ x ∈ ls, x ∈ ls') : LeavesOk ls := fun l hl => h l (hs l hl)

/-- Each run of a list that `allOf` takes, its leaves proved. -/
theorem allOf_ok {os : List (Option (List (Solidity.Derive.Leaf C)))}
    {ls : List (Solidity.Derive.Leaf C)} (h : allOf os = some ls) (hl : LeavesOk ls) :
    ∀ o ∈ os, ∃ l, o = some l ∧ LeavesOk l := fun o ho => by
  obtain ⟨l, rfl, hs⟩ := allOf_sub h o ho
  exact ⟨l, rfl, hl.sub hs⟩

theorem leafRes_sound {R : RuleSet} {Γ : Ctx} {H : Hyps C [] Γ} {φ : Fml C Γ}
    {ls : List (Solidity.Derive.Leaf C)} (h : leafRes H φ = some ls) (hl : LeavesOk ls) :
    Proves C R [] H φ := by
  unfold leafRes at h
  split at h
  · obtain ⟨⟨ls', b'⟩, hr, rfl⟩ := Option.map_eq_some_iff.1 h
    exact .close [] rfl List.nodup_nil
      (Valid.of_stripAlls (Solidity.Proves.valid (Solidity.Proves.of_synResidue hr hl)))
      ‹_› (fun _ _ => List.not_mem_nil)
  · cases h

/-- The run of a goal, sound. -/
abbrev RunSound (r : {Γ : Ctx} → Hyps C [] Γ → Fml C Γ → Option (List (Solidity.Derive.Leaf C)))
    (R : RuleSet) : Prop :=
  ∀ {Γ : Ctx} {H : Hyps C [] Γ} {φ : Fml C Γ} {ls : List (Solidity.Derive.Leaf C)},
    r H φ = some ls → LeavesOk ls → Proves C R [] H φ

theorem premRes_sound {R : RuleSet}
    {r : {Γ : Ctx} → Hyps C [] Γ → Fml C Γ → Option (List (Solidity.Derive.Leaf C))}
    (hr : RunSound r R) {Γ : Ctx} {H : Hyps C [] Γ} {m : Modality} :
    {Γ' Γ₁ Γ₂ : Ctx} → (p : Premise C Γ Γ') → {s : Stmt C Γ Γ'} → (ω : Prog C Γ' Γ₁) →
    (κ : Frames C Γ₁ Γ₂) → (φ : Fml C Γ₂) →
    s.step (H.fresh (.modal m (.cons s ω) κ φ)) m = some p →
    {ls : List (Solidity.Derive.Leaf C)} → premRes r H m p ω κ φ = some ls → LeavesOk ls →
    Proves C R [] H (.modal m (.cons s ω) κ φ)
  | _, _, _, .update U, _, ω, κ, φ, d, _, h, hl => .update d (hr (by simpa only [premRes] using h) hl)
  | _, _, _, .unfold P e, _, ω, κ, φ, d, _, h, hl => .unfold d (hr (by simpa only [premRes] using h) hl)
  | _, _, _, .bind x t P, _, ω, κ, φ, d, _, h, hl => .bind d (hr (by simpa only [premRes] using h) hl)
  | _, _, _, .split b c c' P Q, _, ω, κ, φ, d, _, h, hl => by
    simp only [premRes] at h
    have ho := allOf_ok h hl
    obtain ⟨l₁, h₁, k₁⟩ := ho _ (List.mem_cons_self ..)
    obtain ⟨l₂, h₂, k₂⟩ := ho _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    exact .split d (hr h₁ k₁) (hr h₂ k₂)
  | _, _, _, .check c, _, ω, κ, φ, d, _, h, hl => by
    simp only [premRes] at h
    have ho := allOf_ok h hl
    obtain ⟨l₁, h₁, k₁⟩ := ho _ (List.mem_cons_self ..)
    obtain ⟨l₂, h₂, k₂⟩ := ho _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    exact .check d (hr h₁ k₁) (hr h₂ k₂)
  | _, _, _, .done b, _, ω, κ, φ, d, _, h, hl => .done d (hr (by simpa only [premRes] using h) hl)
  | _, _, _, .branches bs, _, ω, κ, φ, d, _, h, hl => by
    simp only [premRes] at h
    split at h
    · cases h
    · refine .branches d (by simpa using ‹¬bs.isEmpty = true›) fun b hb => ?_
      obtain ⟨l, hb', k⟩ := allOf_ok h hl _ (List.mem_map_of_mem hb)
      exact hr hb' k
  | _, _, _, .cases fs us, _, ω, κ, φ, d, _, h, hl => by
    simp only [premRes] at h
    split at h
    · cases h
    · refine .cases d (by simpa using ‹¬(fs.isEmpty && us.isEmpty) = true›)
        (fun f hf => ?_) (fun U hU => ?_)
      · obtain ⟨l, hb', k⟩ := allOf_ok h hl _
          (List.mem_append_left _ (List.mem_map_of_mem (f := (r H ·)) hf))
        exact hr hb' k
      · obtain ⟨l, hb', k⟩ := allOf_ok h hl _ (List.mem_append_right _
          (List.mem_map_of_mem (f := fun U => r (H.upd m U) (.modalK m ω κ φ)) hU))
        exact hr hb' k
  | _, _, _, .inv I xs hv U c c' hu hb P post, _, ω, κ, φ, d, _, h, hl => by
    simp only [premRes] at h
    have ho := allOf_ok h hl
    obtain ⟨l₁, h₁, k₁⟩ := ho _ (List.mem_cons_self ..)
    obtain ⟨l₂, h₂, k₂⟩ := ho _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    obtain ⟨l₃, h₃, k₃⟩ :=
      ho _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
    exact .inv d (hr h₁ k₁) (hr h₂ k₂) (hr h₃ k₃)
  | _, _, _, .inline P e, _, ω, κ, φ, d, _, h, hl => .inline d (hr (by simpa only [premRes] using h) hl)

/-- **A run that succeeds is a derivation**, its leaves proved. -/
theorem seqRes_sound {R : RuleSet} : (n : Nat) → RunSound (seqRes (C := C) n) R
  | 0, _, _, _, _, h, _ => nomatch h
  | n + 1, _, H, φ, ls, h, hl => by
    cases φ with
    | imp a ψ => exact .intro (seqRes_sound n h hl)
    | all x p ψ => exact .allIntro (seqRes_sound n h hl)
    | upd m U ψ => exact .updIntro (seqRes_sound n h hl)
    | bind m x t ψ => exact .bindIntro (seqRes_sound n h hl)
    | tt =>
      simp only [seqRes] at h
      split at h
      · exact .closeTrue ‹_›
      · exact leafRes_sound h hl
    | modal m P κ ψ =>
      cases P with
      | nil => exact .empty (seqRes_sound n h hl)
      | cons s ω =>
        simp only [seqRes] at h
        split at h
        · exact premRes_sound (seqRes_sound n) _ ω κ ψ ‹_› h hl
        · cases h
    | _ => exact leafRes_sound h hl

end Derive

/-- **`sol_prove`'s proof of a scoped sequent**: the run, its leaves proved. -/
theorem Proves.of_seqRes {R : RuleSet} {φ : Fml C []} {ls : List (Solidity.Derive.Leaf C)}
    (h : Derive.seqRes Derive.fuel .nil φ = some ls)
    (hl : ∀ l ∈ ls, Solidity.Proves .all l.1 l.2) : Proves C R [] .nil φ :=
  Derive.seqRes_sound Derive.fuel h hl

/-! ## The tactic -/

namespace Derive

open Lean Elab Tactic Meta

/-- `sol_prove` on the scoped sequent `g`, `Core.Proves C R [] .nil φ`: the
goals it leaves, one per leaf of today's residues. -/
def proveSeq (g : MVarId) (C R φ : Expr) : MetaM (List MVarId) := do
  let some n := C.constName? | throwError "sol_prove: the contract is not a named constant"
  if φ.hasFVar || φ.hasMVar then
    throwError "sol_prove: the formula mentions a local hypothesis or a metavariable"
  let φe ← Symex.evaluable φ
  let hyp := mkApp (mkConst ``Solidity.Hyp) C
  let leafTy := mkApp2 (mkConst ``Prod [0, 0]) (mkApp (mkConst ``List [0]) hyp)
    (mkApp (mkConst ``Solidity.Fml) C)
  let resTy := mkApp (mkConst ``Option [0]) (mkApp (mkConst ``List [0])
    (mkApp2 (mkConst ``Prod [0, 0]) (mkConst ``Expr) (mkConst ``Expr)))
  let some leaves ← unsafe evalExpr (Option (List (Expr × Expr))) resTy
      (mkAppN (mkConst ``seqResQuote) #[C, quoteConstName n, φe])
    | throwError "sol_prove: the walk ends at a goal its erasure does not close \
        (`Fml.closableB`: a modality left, a diamond update in the context), or takes more \
        than {fuel} steps down a path, or today's closer more than {Solidity.Derive.budget}"
  let mkLeaf (Γ' φ' : Expr) : Expr :=
    mkAppN (mkConst ``Prod.mk [0, 0]) #[mkApp (mkConst ``List [0]) hyp,
      mkApp (mkConst ``Solidity.Fml) C, Γ', φ']
  let ls ← mkListLit leafTy (leaves.map fun (Γ', φ') => mkLeaf Γ' φ')
  let optTy := mkApp (mkConst ``Option [0]) (mkApp (mkConst ``List [0]) leafTy)
  let someLs := mkApp2 (mkConst ``Option.some [0]) (mkApp (mkConst ``List [0]) leafTy) ls
  let nilCtx := mkApp (mkConst ``List.nil [0]) (mkConst ``LTy)
  let type := mkApp3 (mkConst ``Eq [1]) optTy
    (mkAppN (mkConst ``seqRes) #[C, mkConst ``fuel, nilCtx,
      mkApp2 (mkConst ``Hyps.nil) C nilCtx, φ]) someLs
  let h ← try Solidity.Derive.kernelLemma type (mkApp2 (mkConst ``Eq.refl [1]) optTy someLs)
    catch e => throwError "sol_prove: the kernel rejects the run:{indentD e.toMessageData}"
  let mut goals : Array MVarId := #[]
  let mut proofs : Array Expr := #[]
  for (Γ', φ') in leaves, i in [1:leaves.length + 1] do
    let gi ← mkFreshExprSyntheticOpaqueMVar
      (mkAppN (mkConst ``Solidity.Proves) #[C, mkConst ``RuleSet.all, Γ', φ'])
      (Name.mkSimple s!"leaf{i}")
    goals := goals.push gi.mvarId!
    proofs := proofs.push gi
  let mut hl := mkApp (mkConst ``Solidity.Derive.leaves_nil) C
  let mut rest := mkApp (mkConst ``List.nil [0]) leafTy
  for (Γ', φ') in leaves.reverse, p in proofs.reverse do
    hl := mkAppN (mkConst ``Solidity.Derive.leaves_cons) #[C, Γ', φ', rest, p, hl]
    rest := mkAppN (mkConst ``List.cons [0]) #[leafTy, mkLeaf Γ' φ', rest]
  g.assign (mkAppN (mkConst ``Proves.of_seqRes) #[C, R, φ, ls, h, hl])
  return goals.toList

end Derive

open Lean Elab Tactic Meta in
/-- `sol_prove` on a scoped sequent with nothing assumed, `⊢ φ` under
`open scoped Solidity.Core.Surface` (`Core.Proves C R [] .nil φ`): the walk
as one kernel evaluation (`Proves.of_seqRes`); one goal `leafᵢ` of today's
calculus per leaf today's closer leaves. -/
@[tactic Solidity.tacticSol_prove]
def evalSolProveSeq : Tactic := fun _ => withMainContext do
  let g ← getMainGoal
  let ty ← instantiateMVars (← g.getType)
  let_expr Proves C R Γ₀ _ H φ := ty | throwUnsupportedSyntax
  unless (← whnfR Γ₀).isAppOf ``List.nil && (← whnfR H).isAppOf ``Hyps.nil do
    throwUnsupportedSyntax
  let rest := (← getUnsolvedGoals).erase g
  Symex.reporting g do
    let leaves ← Derive.proveSeq g C R φ
    setGoals (leaves ++ rest)

end Solidity.Core
