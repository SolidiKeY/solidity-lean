import Solidity.Calculus.LeafDerive

/-!
# `sol_prove` on a scoped sequent: `⊢ φ` as one kernel evaluation

Under `open scoped Solidity.Scoped` an obligation is stated `⊢ φ`, the
scoped sequent `Proves C .all [] .nil φ` (`Calculus/Surface.lean`),
so the strategy has to build a derivation.  A goal `Valid φ` (`⊨ φ`) goes the
same way: `Proves.valid`, then this walk (decision 89 extended), so its
leaves are scoped sequents too.

`Seq.run` walks the sequent as `Proves` has its rules: `intro`,
`allIntro`, `updIntro`, `bindIntro` take the formula's head into the
context, a modality fires the rule of its first statement (`Stmt.stepIn R`
at `Hyps.fresh`, the index the rules ask: under `⊢ₖ` solkey's rules alone) and walks each goal its premise
leaves, `empty` goes through the frames, `closeTrue` ends a `true` behind a
box context.  Every other leaf is closed on its scoped form
(`Seq.leafCheckS`, `Calculus/LeafDerive.lean`): the sequent wrapped, its
updates pushed in by position and the reduction closed by `LFml.close`,
sound by `Proves.closeHolds`.
A leaf that closer does not read (outside its fragment: the classes
`docs/intrinsic.md`'s "W9.3 `walk` record" lists), or reads and does not
close, stays the walk's own sequent `H ⊢ φ` (`Seq.SLeaf`, `Seq.leafS`; M6c
6c, decision 89), a goal of the scoped calculus: `sol_leaf` leaves it as
`⊨ ψ` (`Proves.closeValid`) for a closer, the scoped `sol_close` among
them.  Since W9.4 there is no erased fallback, in the walk or after it
(`Proves.close_leaf`, `core_leaf_close` are gone).
`Seq.run_sound` reads the walk back as the derivation; the kernel checks
it as one evaluation (`Seq.residue R H φ = some ls`), and the tactic
leaves one goal `leafᵢ` per leaf, as `sol_prove` on `Valid` does.

The walk is generic in what a leaf is (`α`), so the compiled run that
quotes the leaves for the tactic (`Seq.leafQuoteS`) and the kernel's
(`Seq.leafS`) are one function.  It is written with `casesOn` (Gate G0,
condition 1); `n` bounds the steps down a path, `b` the steps of the whole
walk, handed from a goal to the next.

A leaf behind updates of either modality is read: an update's reading asks
only of the typed states it may end in.

A split whose branch the bounded scoped closer refutes keeps only the other branch,
the refuted one closed by `Proves.closeFalse` (`refutes`): `returnEarly`
runs one path of its callee, not 27.  The scoped closer keeps the
parameters bound, its reduction reading each at its type.  An explicit
`∀ uint x;` is marked on a leaf left (decision 28): the tactic counts the
parameters, the leading `∀`s up to the first one `cdl!` marked explicit
(`Symex.paramCount`), and hands the count to the quoting (`np`).
-/

namespace Solidity

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
them; `r` walks a goal.  A split's branch whose context `x` refutes is
closed by `closeFalse` and not walked (`refutes`). -/
def premise (r : {Γ : Ctx} → Hyps C [] Γ → Fml C Γ → Nat → Option (List α × Nat))
    (x : {Γ : Ctx} → Hyps C [] Γ → Fml C Γ → Bool) {Γ Γ' Γ₁ Γ₂ : Ctx} (H : Hyps C [] Γ) (m : Modality) (ω : Prog C Γ' Γ₁)
    (κ : Frames C Γ₁ Γ₂) (φ : Fml C Γ₂) (p : Premise C Γ Γ') (b : Nat) :
    Option (List α × Nat) :=
  Premise.casesOn (motive := fun Γ' _ => Prog C Γ' Γ₁ → Option (List α × Nat)) p
    (fun U ω => r (H.upd m U) (.modalK m ω κ φ) b)
    (fun U V ω => r ((H.upd m U).upd m V) (.modalK m ω κ φ) b)
    (fun P e ω => r H (.modal m P (.pop .capture e (.seq ω κ)) φ) b)
    (fun x t P ω => r (H.bind m x t) (.modal m P (.seq ω κ) φ) b)
    (fun bk c c' P Q ω => cond (x H c) (r (H.pre c') (.modalK m Q (.pop bk Q.ext (.seq ω κ)) φ) b)
      (cond (x H c') (r (H.pre c) (.modalK m P (.pop bk P.ext (.seq ω κ)) φ) b)
        (both (r (H.pre c) (.modalK m P (.pop bk P.ext (.seq ω κ)) φ))
          (r (H.pre c') (.modalK m Q (.pop bk Q.ext (.seq ω κ)) φ)) b)))
    (fun c ω => both (r (H.pre c) (.modalK m ω κ φ)) (r H c) b)
    (fun bo _ => r H (if bo then .tt else .ff) b)
    (fun bs ω => cond bs.isEmpty none (each (fun br => r H (br.bs.all
      (.modalK m br.P (.pop .block ((Ext.append Γ br.ρ).trans br.P.ext) (.seq ω κ)) φ))) bs b))
    (fun fs us ω => cond (fs.isEmpty && us.isEmpty) none
      (both (each (fun f => r H f) fs) (each (fun U => r (H.upd m U) (.modalK m ω κ φ)) us) b))
    (fun I B xs hv U c c' hu hb P post ω => both (r H (I.invHyp B))
      (both (r ((((H.anonHavoc xs hv).pre (I.invHyp B)).upd m U).pre c)
          (.upd m (Upd.nil.pop hb) (.modalK m P (.pop .block P.ext .nil)
            (Fml.invPost m hu ω κ φ post B))))
        (r ((((H.anonHavoc xs hv).pre (I.invHyp B)).upd m U).pre c')
          (.upd m (Upd.nil.pop (hu.trans hb)) (.modalK m ω κ φ)))) b)
    (fun P e ω => r H (.modal m P (.drop e (.seq ω κ)) φ) b)
    (fun c U V ω =>
      cond (x H c) (r (H.pre (.not c)) (.modal m (.cons .revert ω) κ φ) b)
        (cond (x H (.not c)) (r (H.pre c) (.upd m U (.upd m V (.modalK m ω κ φ))) b)
          (both (r (H.pre c) (.upd m U (.upd m V (.modalK m ω κ φ))))
            (r (H.pre (.not c)) (.modal m (.cons .revert ω) κ φ)) b))) ω

/-- A modality: the frames when the program is done (`empty`), else the rule
of the first statement and its premise's goals. -/
def modal (R : RuleSet) (r : {Γ : Ctx} → Hyps C [] Γ → Fml C Γ → Nat → Option (List α × Nat))
    (x : {Γ : Ctx} → Hyps C [] Γ → Fml C Γ → Bool) (m : Modality) {Γ Γ₁ Γ₀ : Ctx} (H : Hyps C [] Γ) (P : Prog C Γ Γ₁) (κ : Frames C Γ₁ Γ₀)
    (φ : Fml C Γ₀) (b : Nat) : Option (List α × Nat) :=
  Prog.casesOn (motive_2 := fun Γ Γ₁ _ => Frames C Γ₁ Γ₀ → Hyps C [] Γ → Option (List α × Nat)) P
    (fun κ H => r H (κ.exit m φ) b)
    (fun s ω κ H => match s.stepIn R (H.fresh (.modal m (.cons s ω) κ φ)) m with
      | some p => premise r x H m ω κ φ p b
      | none => none) κ H

/-- Whether `H, c ⟹ false` closes with nothing left. Literal-bound locals and
symbolic facts such as `values.length == 3` can both refute a branch; the same
scoped closer and its existing size bounds check the refutation. -/
def refutes (leaf : {Γ : Ctx} → Hyps C [] Γ → Fml C Γ → Option (List α)) {Γ : Ctx}
    (H : Hyps C [] Γ) (c : Fml C Γ) : Bool :=
  match leaf (H.pre c) .ff with
    | some [] => true
    | _ => false

/-- The walk of the sequent `H ⊢ φ`: the leaves `leaf` leaves, or `none`
when a step has no rule, a leaf does not close, or `n` or `b` runs out; `rf`
says which of a split's branches is refuted (`refutes`). -/
def run (R : RuleSet) (leaf : {Γ : Ctx} → Hyps C [] Γ → Fml C Γ → Option (List α))
    (rf : {Γ : Ctx} → Hyps C [] Γ → Fml C Γ → Bool) :
    Nat → {Γ : Ctx} → Hyps C [] Γ → Fml C Γ → Nat → Option (List α × Nat)
  | 0, _, _, _, _ => none
  | _ + 1, _, _, _, 0 => none
  | n + 1, _, H, φ, b + 1 =>
    Fml.casesOn (motive := fun Γ _ => Hyps C [] Γ → Option (List α × Nat)) φ
      (tt := fun H => cond H.boxOnly (some ([], b)) ((leaf H .tt).map (·, b)))
      (eq := fun t u H => (leaf H (.eq t u)).map (·, b))
      (defined := fun t H => (leaf H (.defined t)).map (·, b))
      (not := fun ψ H => (leaf H (.not ψ)).map (·, b))
      (and := fun ψ χ H => cond (Fml.and ψ χ).modalFree ((leaf H (.and ψ χ)).map (·, b))
        (both (run R leaf rf n H ψ) (run R leaf rf n H χ) b))
      (imp := fun a ψ H => run R leaf rf n (H.pre a) ψ b)
      (upd := fun m U ψ H => run R leaf rf n (H.upd m U) ψ b)
      (modal := fun m P κ ψ H => modal R (fun H φ b => run R leaf rf n H φ b) rf m H P κ ψ b)
      (havoc := fun ψ H => (leaf H (.havoc ψ)).map (·, b))
      (all := fun x p ψ H => run R leaf rf n (H.all x p) ψ b)
      (bind := fun m x t ψ H => run R leaf rf n (H.bind m x t) ψ b)
      (anon := fun xs ψ H => (leaf H (.anon xs ψ)).map (·, b)) H

/-! ### The leaves left: scoped sequents

A leaf the closer does not close stays the walk's own sequent `H ⊢ φ`
(`SLeaf`, decision 89), a goal of the scoped calculus, which `sol_leaf`
leaves as `⊨ ψ` for a closer. -/

/-- A leaf the walk leaves: a sequent of the outer scope `[]`. -/
abbrev SLeaf (C : Contract) := (Γ : Ctx) × Hyps C [] Γ × Fml C Γ

/-- A leaf for the kernel, read by the scoped closer (`leafCheckS`,
`Calculus/LeafDerive.lean`): closed (`[]`) where it closes it, else the
sequent itself, whether the closer reads it and does not close it or does
not read it (a class it has no clause for: `docs/intrinsic.md`, "W9.3
`walk` record"; since W9.4 no erased fallback). -/
def leafS {Γ : Ctx} (H : Hyps C [] Γ) (φ : Fml C Γ) : Option (List (SLeaf C)) :=
  match leafCheckS H φ with
  | some true => some []
  | _ => some [⟨_, H, φ⟩]

/-- Whether every entry of a context is a `∀` or a hidden binder, and how
many `∀`s it has. -/
def _root_.Solidity.Hyps.leadAlls {Γ₀ : Ctx} : {Γ : Ctx} → Hyps C Γ₀ Γ → Option Nat
  | _, .nil => some 0
  | _, .all H _ _ => (Hyps.leadAlls H).map (· + 1)
  | _, .bind H _ _ _ => Hyps.leadAlls H
  | _, _ => none

end Seq

namespace Quote

/-- A context, quoted; a leading `∀` past the first `np` marked explicit
(`Fml.markExplicitVar`), so that `Seq.paramCount` reads `np` off the
quoted leaf again. -/
partial def qHyps (Γ₀ : Ctx) (np : Option Nat) : (Γ : Ctx) → Hyps C Γ₀ Γ → QM Lean.Expr
  | _, .nil => do
    return Lean.mkApp2 (Lean.mkConst ``Hyps.nil) (← contract) (← qCtx Γ₀)
  | Γ, .pre H a => do
    let args := #[← contract, ← qCtx Γ₀, ← qCtx Γ, ← qHyps Γ₀ np Γ H, ← qFml Γ a]
    return Lean.mkAppN (Lean.mkConst ``Hyps.pre) args
  | Δ, @Hyps.upd _ _ Γ _ H m U => do
    let args := #[← contract, ← qCtx Γ₀, ← qCtx Γ, ← qCtx Δ, ← qHyps Γ₀ np Γ H,
      Lean.toExpr m, ← qUpd Γ Δ U]
    return Lean.mkAppN (Lean.mkConst ``Hyps.upd) args
  | Γ, .havoc H => do
    let args := #[← contract, ← qCtx Γ₀, ← qCtx Γ, ← qHyps Γ₀ np Γ H]
    return Lean.mkAppN (Lean.mkConst ``Hyps.havoc) args
  | _, @Hyps.all _ _ Γ H x p => do
    let explicit := match np, H.leadAlls with
      | some n, some k => decide (n ≤ k)
      | _, _ => false
    let xe := if explicit then Fml.markExplicitVar (Lean.toExpr x) else Lean.toExpr x
    let args := #[← contract, ← qCtx Γ₀, ← qCtx Γ, ← qHyps Γ₀ np Γ H, xe, Lean.toExpr p]
    return Lean.mkAppN (Lean.mkConst ``Hyps.all) args
  | _, @Hyps.bind _ _ Γ H m x t => do
    let args := #[← contract, ← qCtx Γ₀, ← qCtx Γ, ← qHyps Γ₀ np Γ H, Lean.toExpr m,
      Lean.toExpr x, qLTy t]
    return Lean.mkAppN (Lean.mkConst ``Hyps.bind) args
  | Γ, .anon H xs => do
    let args := #[← contract, ← qCtx Γ₀, ← qCtx Γ, ← qHyps Γ₀ np Γ H, ← qIdxList Γ xs]
    return Lean.mkAppN (Lean.mkConst ``Hyps.anon) args

end Quote

/-- A context, quoted and hash-consed, the contract named by `c`. -/
def _root_.Solidity.Hyps.quote (c : Lean.Expr) {Γ₀ Γ : Ctx} (H : Hyps C Γ₀ Γ) : Lean.Expr :=
  Lean.ShareCommon.shareCommon ((Quote.qHyps Γ₀ none Γ H).run c)

namespace Seq

/-- The leaf `⟨Γ, H, φ⟩ : SLeaf C` quoted, hash-consed, the contract named
by `c` (`Quote.qHyps` for the marks). -/
def SLeaf.quote (c : Lean.Expr) (np : Option Nat) {Γ : Ctx} (H : Hyps C [] Γ) (φ : Fml C Γ) :
    Lean.Expr :=
  Lean.ShareCommon.shareCommon <| Id.run <| ReaderT.run (r := c) do
    let ctxE := Lean.mkConst ``Ctx
    let nilE ← Quote.qCtx []
    let Γe ← Quote.qCtx Γ
    let hyps (g : Lean.Expr) := Lean.mkAppN (Lean.mkConst ``Hyps) #[c, nilE, g]
    let fml (g : Lean.Expr) := Lean.mkAppN (Lean.mkConst ``Fml) #[c, g]
    let prodE (g : Lean.Expr) := Lean.mkApp2 (Lean.mkConst ``Prod [.zero, .zero]) (hyps g) (fml g)
    let β := Lean.Expr.lam `Γ ctxE (prodE (.bvar 0)) .default
    let pair := Lean.mkAppN (Lean.mkConst ``Prod.mk [.zero, .zero])
      #[hyps Γe, fml Γe, ← Quote.qHyps [] np Γ H, ← Quote.qFml Γ φ]
    return Lean.mkAppN (Lean.mkConst ``Sigma.mk [.zero, .zero]) #[ctxE, β, Γe, pair]

/-- `leafS` for the tactic: the leaf quoted (`SLeaf.quote`) where it is
left. -/
def leafQuoteS (c : Lean.Expr) (np : Option Nat) {Γ : Ctx} (H : Hyps C [] Γ) (φ : Fml C Γ) :
    Option (List Lean.Expr) :=
  match leafCheckS H φ with
  | some true => some []
  | _ => some [SLeaf.quote c np H φ]

/-- The steps the walk is given, down a path and in all
(`Derive.budget`). -/
def fuel : Nat := Derive.budget

/-- **`sol_prove`'s check**: the leaves the walk leaves, none when every
leaf closes.  A split's branch is refuted as its leaf is read. -/
def residueWithin (steps : Nat) (R : RuleSet) {Γ : Ctx} (H : Hyps C [] Γ)
    (φ : Fml C Γ) : Option (List (SLeaf C)) :=
  (run R leafS (refutes leafS) steps H φ steps).map (·.1)

def residue (R : RuleSet) {Γ : Ctx} (H : Hyps C [] Γ) (φ : Fml C Γ) : Option (List (SLeaf C)) :=
  residueWithin fuel R H φ

/-- How many storage writes an update holds. -/
def _root_.Solidity.Upd.storageWrites {Γ : Ctx} : {Δ : Ctx} → Upd C Γ Δ → Nat
  | _, .nil => 0
  | _, .snoc U (.storage _) => U.storageWrites + 1
  | _, .snoc U _ | _, .decl U _ _ | _, .pop U _ | _, .drop U _ => U.storageWrites

/-- How many storage writes a context's updates hold. -/
def _root_.Solidity.Hyps.storageWrites {Γ₀ : Ctx} : {Γ : Ctx} → Hyps C Γ₀ Γ → Nat
  | _, .nil => 0
  | _, .upd H _ U => H.storageWrites + U.storageWrites
  | _, .pre H _ | _, .havoc H | _, .all H _ _ | _, .bind H _ _ _ | _, .anon H _ => H.storageWrites

/-- `#solkey_scan`'s view of `⊢ φ` (`Frontend/Problems.lean`): how many
leaves the walk leaves, closed by `sol_prove`'s closer (`leafS`) or
(`walk`) not, and the most storage writes in one leaf's context
(`Hyps.storageWrites`); `none` when the walk runs out or a step has no
rule. -/
def scanLeaves (walk : Bool) (φ : Fml C []) : Option (Nat × Nat) :=
  let leaf : {Γ : Ctx} → Hyps C [] Γ → Fml C Γ → Option (List (SLeaf C)) :=
    fun H φ => if walk then some [⟨_, H, φ⟩] else leafS H φ
  (run .all leaf (refutes leafS) fuel .nil φ fuel).map fun (ls, _) =>
    (ls.length, ls.foldl (fun m l => max m l.2.1.storageWrites) 0)

/-- `residue`, the leaves quoted (`leafQuoteS`), `np` the sequent's
parameters (their marks, `Quote.qHyps`). -/
def residueQuoteWithin (steps : Nat) (R : RuleSet) (c : Lean.Expr) (np : Option Nat)
    {Γ : Ctx} (H : Hyps C [] Γ)
    (φ : Fml C Γ) : Option (List Lean.Expr) :=
  (run R (leafQuoteS c np) (refutes leafS) steps H φ steps).map (·.1)

/-- The closer's bounds on a leaf, which `sol_prove?` asks before it
reduces it: the scoped closer's (`leafFitsOn`) on a leaf it reads; a leaf it
does not read fits (the reducing tries fail on it). -/
def leafFitsS {Γ : Ctx} (H : Hyps C [] Γ) (φ : Fml C Γ) : Bool :=
  match leafCheckS H φ with
  | some _ => leafFitsOn (H.wrap φ)
  | none => true

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
    {x : {Γ : Ctx} → Hyps C [] Γ → Fml C Γ → Bool}
    (hx : ∀ {Γ : Ctx} (H : Hyps C [] Γ) (c : Fml C Γ), x H c = true → Proves C R [] (H.pre c) .ff)
    {Γ Γ' Γ₁ Γ₂ : Ctx} (H : Hyps C [] Γ) (m : Modality) (s : Stmt C Γ Γ') (ω : Prog C Γ' Γ₁)
    (κ : Frames C Γ₁ Γ₂) (φ : Fml C Γ₂) (p : Premise C Γ Γ')
    (d : s.stepIn R (H.fresh (.modal m (.cons s ω) κ φ)) m = some p) {b : Nat} {ls : List α}
    {b' : Nat} (h : premise r x H m ω κ φ p b = some (ls, b')) (hl : ∀ l ∈ ls, P l) :
    Proves C R [] H (.modal m (.cons s ω) κ φ) := by
  have hd := Stmt.step_of_stepIn d
  have hR := Stmt.admits_of_stepIn d
  cases p with
  | update U => exact .update (hR := hR) hd (hr _ _ _ _ _ h hl)
  | updates U V => exact .updates (hR := hR) hd (hr _ _ _ _ _ h hl)
  | guardedUpdates c U V =>
    cases h1 : x H c
    · cases h2 : x H (.not c)
      · simp only [premise, h1, h2, cond_false] at h
        have := both_sound h hl (hr _ _) (hr _ _)
        exact .guardedUpdates (hR := hR) hd this.1 this.2
      · simp only [premise, h1, h2, cond_false, cond_true] at h
        exact .guardedUpdates (hR := hR) hd (hr _ _ _ _ _ h hl)
          (.closeFalse (hx H (.not c) h2))
    · simp only [premise, h1, cond_true] at h
      exact .guardedUpdates (hR := hR) hd (.closeFalse (hx H c h1)) (hr _ _ _ _ _ h hl)
  | unfold P e => exact .unfold (hR := hR) hd (hr _ _ _ _ _ h hl)
  | bind x t P => exact .bind (hR := hR) hd (hr _ _ _ _ _ h hl)
  | split bk c c' P Q =>
    cases h1 : x H c
    · cases h2 : x H c'
      · simp only [premise, h1, h2, cond_false] at h
        have := both_sound h hl (hr _ _) (hr _ _)
        exact .split (hR := hR) hd this.1 this.2
      · simp only [premise, h1, h2, cond_false, cond_true] at h
        exact .split (hR := hR) hd (hr _ _ _ _ _ h hl) (.closeFalse (hx H c' h2))
    · simp only [premise, h1, cond_true] at h
      exact .split (hR := hR) hd (.closeFalse (hx H c h1)) (hr _ _ _ _ _ h hl)
  | check c =>
    have := both_sound h hl (hr _ _) (hr _ _)
    exact .check (hR := hR) hd this.1 this.2
  | done bo => exact .done (hR := hR) hd (hr _ _ _ _ _ h hl)
  | branches bs =>
    cases hb : bs.isEmpty
    · simp only [premise, hb, cond_false] at h
      exact .branches (hR := hR) hd hb (each_sound h hl fun _ _ _ _ => hr _ _ _ _ _)
    · simp only [premise, hb, cond_true, reduceCtorEq] at h
  | cases fs us =>
    cases hb : (fs.isEmpty && us.isEmpty)
    · simp only [premise, hb, cond_false] at h
      have := both_sound h hl
        (fun _ _ _ h₁ hl₁ => each_sound h₁ hl₁ fun _ _ _ _ => hr _ _ _ _ _)
        (fun _ _ _ h₁ hl₁ => each_sound h₁ hl₁ fun _ _ _ _ => hr _ _ _ _ _)
      exact .cases (hR := hR) hd hb this.1 this.2
    · simp only [premise, hb, cond_true, reduceCtorEq] at h
  | inv I B xs hv U c c' hu hb P post =>
    have := both_sound h hl (hr _ _)
      (fun _ _ _ h₁ hl₁ => both_sound h₁ hl₁ (hr _ _) (hr _ _))
    exact .inv (hR := hR) hd this.1 this.2.1 this.2.2
  | inline P e => exact .inline (hR := hR) hd (hr _ _ _ _ _ h hl)

variable {leaf : {Γ : Ctx} → Hyps C [] Γ → Fml C Γ → Option (List α)}
  (hleaf : ∀ {Γ : Ctx} (H : Hyps C [] Γ) (φ : Fml C Γ) ls, leaf H φ = some ls →
    (∀ l ∈ ls, P l) → Proves C R [] H φ)
include hleaf

theorem leaf_sound {Γ : Ctx} {H : Hyps C [] Γ} {φ : Fml C Γ} {b : Nat} {ls : List α} {b' : Nat}
    (h : (leaf H φ).map (·, b) = some (ls, b')) (hl : ∀ l ∈ ls, P l) : Proves C R [] H φ := by
  obtain ⟨ls', h', he⟩ := Option.map_eq_some_iff.1 h
  cases he
  exact hleaf H φ _ h' hl

theorem refutes_sound {Γ : Ctx} (H : Hyps C [] Γ) (c : Fml C Γ)
    (h : refutes leaf H c = true) : Proves C R [] (H.pre c) .ff := by
  unfold refutes at h
  cases hl : leaf (H.pre c) .ff with
  | none => simp only [hl, reduceCtorEq] at h
  | some ls =>
    cases ls with
    | nil => exact hleaf _ _ [] hl fun _ h => nomatch h
    | cons _ _ => simp only [hl, reduceCtorEq] at h

variable {rf : {Γ : Ctx} → Hyps C [] Γ → Fml C Γ → Bool}
  (hrf : ∀ {Γ : Ctx} (H : Hyps C [] Γ) (c : Fml C Γ), rf H c = true → Proves C R [] (H.pre c) .ff)
include hrf in
/-- **The walk is a derivation.** -/
theorem run_sound : ∀ (n : Nat) {Γ : Ctx} (H : Hyps C [] Γ) (φ : Fml C Γ) (b : Nat)
    (ls : List α) (b' : Nat), run R leaf rf n H φ b = some (ls, b') → (∀ l ∈ ls, P l) →
    Proves C R [] H φ
  | 0, _, _, _, _, _, _, h, _ => by simp only [run, reduceCtorEq] at h
  | _ + 1, _, _, _, 0, _, _, h, _ => by simp only [run, reduceCtorEq] at h
  | n + 1, _, H, φ, b + 1, ls, b', h, hl => by
    have ih : ∀ {Γ : Ctx} (H : Hyps C [] Γ) (φ : Fml C Γ) b ls b', run R leaf rf n H φ b = some (ls, b') →
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
    | and ψ χ =>
      cases hm : (Fml.and ψ χ).modalFree
      · simp only [run, hm, cond_false] at h
        have := both_sound h hl (ih _ _) (ih _ _)
        exact .andIntro this.1 this.2
      · exact leaf_sound hleaf (b := b) (by simpa only [run, hm, cond_true] using h) hl
    | imp a ψ => exact .intro (ih _ _ _ _ _ h hl)
    | upd m U ψ => exact .updIntro (ih _ _ _ _ _ h hl)
    | modal m P κ ψ =>
      cases P with
      | nil => exact .empty (ih _ _ _ _ _ h hl)
      | cons s ω =>
        change (match s.stepIn R (H.fresh (.modal m (.cons s ω) κ ψ)) m with
          | some p => premise (fun H φ b => run R leaf rf n H φ b) rf H m ω κ ψ p b
          | none => none) = some (ls, b') at h
        split at h
        · rename_i p hp
          exact premise_sound ih hrf H m s ω κ ψ p hp h hl
        · cases h
    | havoc => exact leaf_sound hleaf h hl
    | all x p ψ => exact .allIntro (ih _ _ _ _ _ h hl)
    | bind m x t ψ => exact .bindIntro (ih _ _ _ _ _ h hl)
    | anon => exact leaf_sound hleaf h hl

end Sound

/-- A leaf `leafS` takes is proved once the sequent it leaves is. -/
theorem leafS_sound {R : RuleSet} {Γ : Ctx} (H : Hyps C [] Γ) (φ : Fml C Γ) (ls : List (SLeaf C))
    (h : leafS H φ = some ls) (hl : ∀ l ∈ ls, Proves C R [] l.2.1 l.2.2) : Proves C R [] H φ := by
  unfold leafS at h
  split at h
  · exact leafCheckS_sound ‹_›
  · cases h
    exact hl ⟨_, H, φ⟩ (List.mem_singleton_self _)

theorem SLeaf.nil {R : RuleSet} : ∀ l ∈ ([] : List (SLeaf C)), Proves C R [] l.2.1 l.2.2 :=
  fun _ h => nomatch h

theorem SLeaf.cons {R : RuleSet} {Γ : Ctx} {H : Hyps C [] Γ} {φ : Fml C Γ} {ls : List (SLeaf C)}
    (h : Proves C R [] H φ) (t : ∀ l ∈ ls, Proves C R [] l.2.1 l.2.2) :
    ∀ l ∈ (⟨Γ, H, φ⟩ :: ls : List (SLeaf C)), Proves C R [] l.2.1 l.2.2 := by
  intro l hl
  rcases List.mem_cons.1 hl with rfl | hl
  · exact h
  · exact t l hl

end Seq

/-- **`sol_prove`'s proof of a sequent**: the walk's residue, each leaf it
leaves proved. -/
theorem Proves.of_residueWithin (steps : Nat) {R : RuleSet} {Γ : Ctx} {H : Hyps C [] Γ}
    {φ : Fml C Γ} {ls : List (Seq.SLeaf C)}
    (h : Seq.residueWithin steps R H φ = some ls)
    (hl : ∀ l ∈ ls, Proves C R [] l.2.1 l.2.2) : Proves C R [] H φ := by
  obtain ⟨⟨ls', b'⟩, hr, he⟩ := Option.map_eq_some_iff.1 h
  cases he
  exact Seq.run_sound (P := fun l : Seq.SLeaf C => Proves C R [] l.2.1 l.2.2)
    Seq.leafS_sound
    (Seq.refutes_sound (P := fun l : Seq.SLeaf C => Proves C R [] l.2.1 l.2.2) Seq.leafS_sound)
    _ H φ _ _ _ hr hl

/-- `Proves.of_residueWithin` at the walk's full fuel. -/
theorem Proves.of_residue {R : RuleSet} {Γ : Ctx} {H : Hyps C [] Γ}
    {φ : Fml C Γ} {ls : List (Seq.SLeaf C)}
    (h : Seq.residue R H φ = some ls)
    (hl : ∀ l ∈ ls, Proves C R [] l.2.1 l.2.2) : Proves C R [] H φ :=
  Proves.of_residueWithin Seq.fuel h hl

/-! ## The tactic -/

namespace Seq

open Lean Elab Tactic Meta

/-- The parameters of the sequent `H ⊢ φ` (decision 28): the context's
leading `∀`s and then the formula's (`Symex.paramCount`), up to the first
one `cdl!` marked explicit; `none` where they are not written out. -/
partial def paramCount (H φ : Expr) : MetaM (Option Nat) := do
  -- the context's entries, outermost first, down to `Hyps.nil`: a
  -- precondition or an update is kept as the counting loop's stop
  let rec entries (H : Expr) (acc : List Expr) : MetaM (Option (List Expr)) := do
    let H ← whnfR (← instantiateMVars H)
    if H.isAppOf ``Hyps.nil then return some acc
    if H.isAppOfArity ``Hyps.all 6 || H.isAppOfArity ``Hyps.bind 7
        || H.isAppOfArity ``Hyps.pre 5 || H.isAppOfArity ``Hyps.havoc 4
        || H.isAppOfArity ``Hyps.anon 5 then
      return ← entries (H.getArg! 3) (H :: acc)
    if H.isAppOfArity ``Hyps.upd 7 then
      return ← entries (H.getArg! 4) (H :: acc)
    return none
  let some es ← entries H [] | return none
  let mut n := 0
  for e in es do
    if e.isAppOfArity ``Hyps.all 6 then
      match e.getArg! 4 with
      | .mdata d _ => if d.getBool Fml.explicitKey then return some n
      | _ => pure ()
      n := n + 1
    else unless e.isAppOfArity ``Hyps.bind 7 do return some n
  return (← Symex.paramCount φ).map (n + ·)

/-- `sol_prove` on the goal `g`, `Proves C R [] H φ`: the goals it
leaves, one per leaf the closer leaves, each the walk's own sequent. -/
def prove (g : MVarId) (C R Γ H φ : Expr) (steps? : Option Nat := none) : MetaM (List MVarId) := do
  if let some steps := steps? then
    unless 0 < steps && steps ≤ fuel do
      throwError "sol_prove: steps must be between 1 and {fuel}"
  let some n := C.constName? | throwError "sol_prove: the contract is not a named constant"
  if H.hasFVar || H.hasMVar || φ.hasFVar || φ.hasMVar || R.hasFVar || R.hasMVar then
    throwError "sol_prove: the sequent mentions a local hypothesis or a metavariable"
  let φe ← Symex.evaluable φ
  let npV ← paramCount H φe
  let np := toExpr npV
  let leafTy := mkApp (mkConst ``SLeaf) C
  let resTy := mkApp (mkConst ``Option [0]) (mkApp (mkConst ``List [0]) leafTy)
  let lemmaFor (steps : Nat) (ls : Expr) : MetaM Expr := do
    let someLs := mkApp2 (mkConst ``Option.some [0]) (mkApp (mkConst ``List [0]) leafTy) ls
    let type := mkApp3 (mkConst ``Eq [1]) resTy
      (mkAppN (mkConst ``residueWithin) #[C, toExpr steps, R, Γ, H, φ]) someLs
    Derive.kernelLemma type (mkApp2 (mkConst ``Eq.refl [1]) resTy someLs)
  let assignWith (steps : Nat) (ls h : Expr) (hl : Expr) : MetaM Unit :=
    g.assign (mkAppN (mkConst ``Proves.of_residueWithin) #[C, toExpr steps, R, Γ, H, φ, ls, h, hl])
  let nil := mkApp (mkConst ``List.nil [0]) leafTy
  -- the compiled walk first, then one kernel check of its leaves, as
  -- today's `sol_prove` (`Derive.prove`): a kernel try at no leaves costs a
  -- second evaluation where the closer leaves some, in the declaration's
  -- heartbeats
  let qTy := mkApp (mkConst ``Option [0]) (mkApp (mkConst ``List [0]) (mkConst ``Expr))
  let stages := match steps? with
    | some steps => [steps]
    | none => ([128, 256, 512, 1024, 2048, 4096, 8192, 16384].filter (· < fuel)) ++ [fuel]
  let mut chosen : Option (Nat × List Expr) := none
  for steps in stages do
    let result ← unsafe evalExpr (Option (List Expr)) qTy
      (mkAppN (mkConst ``residueQuoteWithin) #[C, toExpr steps, R, quoteConstName n, np, Γ, H, φe])
    if let some leaves := result then
      chosen := some (steps, leaves)
      break
  let some (steps, leaves) := chosen
    | throwError "sol_prove: the walk does not reach the end of the sequent: a step with no \
        rule, or more than {steps?.getD fuel} steps"
  if leaves.isEmpty then
    let h ← try lemmaFor steps nil
      catch e => throwError "sol_prove: the kernel rejects the walk:{indentD e.toMessageData}"
    assignWith steps nil h (mkApp2 (mkConst ``SLeaf.nil) C R)
    return []
  let ls ← mkListLit leafTy leaves
  let h ← try lemmaFor steps ls
    catch e => throwError "sol_prove: the kernel rejects the residue:{indentD e.toMessageData}"
  -- a leaf `⟨Γ', (H', φ')⟩`: its goal `H' ⊢ φ'`
  let parts (l : Expr) : Expr × Expr × Expr :=
    let pr := l.getArg! 3
    (l.getArg! 2, pr.getArg! 2, pr.getArg! 3)
  let nilCtx := ctxE []
  let mut goals : Array MVarId := #[]
  let mut proofs : Array Expr := #[]
  for l in leaves, i in [1:leaves.length + 1] do
    let (Γ', H', φ') := parts l
    let gi ← mkFreshExprSyntheticOpaqueMVar
      (mkAppN (mkConst ``Proves) #[C, R, nilCtx, Γ', H', φ']) (Name.mkSimple s!"leaf{i}")
    goals := goals.push gi.mvarId!
    proofs := proofs.push gi
  let mut hl := mkApp2 (mkConst ``SLeaf.nil) C R
  let mut rest := nil
  for l in leaves.reverse, p in proofs.reverse do
    let (Γ', H', φ') := parts l
    hl := mkAppN (mkConst ``SLeaf.cons) #[C, R, Γ', H', φ', rest, p, hl]
    rest := mkAppN (mkConst ``List.cons [0]) #[leafTy, l, rest]
  assignWith steps ls h hl
  return goals.toList

/-- `leafFitsS` on a leaf goal `H ⊢ φ` the walk left, run as compiled
code; `true` on any other goal. -/
def goalFits (l : MVarId) : MetaM Bool := do
  let ty ← instantiateMVars (← l.getType)
  let_expr Proves C _ Γ₀ Γ H φ := ty | return true
  if ty.hasFVar || ty.hasMVar || !(← whnfR Γ₀).isAppOf ``List.nil then return true
  let φe ← Symex.evaluable φ
  unsafe evalExpr Bool (mkConst ``Bool) (mkAppN (mkConst ``leafFitsS) #[C, Γ, H, φe])

end Seq

/-- **A leaf closed over the typed reading**: `Proves.closeHolds`, the
sequent wrapped (`Hyps.wrap`) and valid. -/
theorem Proves.closeValid {R : RuleSet} {Γ : Ctx} {H : Hyps C [] Γ} {φ : Fml C Γ}
    (h : Valid (H.wrap φ)) (hm : (H.wrap φ).modalFree = true) : Proves C R [] H φ :=
  .closeHolds h hm

namespace Seq

open Lean Elab Tactic Meta

/-- `sol_leaf` on the main goal, a leaf `H ⊢ φ` of the outer scope:
`Proves.closeValid`, the goal left `⊨ ψ` with `ψ` the wrapped sequent
computed and quoted (`Symex.normValid`); no modality left
(`Fml.modalFree`, checked by the kernel). -/
def leafValid : TacticM Unit := withMainContext do
  let g ← getMainGoal
  let ty ← instantiateMVars (← g.getType)
  let_expr Proves C R Γ₀ Γ H φ := ty | throwError "sol_leaf: not a scoped sequent"
  unless (← whnfR Γ₀).isAppOf ``List.nil do throwError "sol_leaf: not a sequent of the outer scope"
  if ty.hasFVar || ty.hasMVar then throwError "sol_leaf: the sequent mentions a local or a metavariable"
  let nilCtx := ctxE []
  let ψ := mkAppN (mkConst ``Hyps.wrap) #[C, nilCtx, Γ, H, φ]
  let hm ← try Decide.trueLemma (mkApp3 (mkConst ``Fml.modalFree) C nilCtx ψ)
    catch _ => throwError "sol_leaf: a modality is left in the leaf"
  let g' ← mkFreshExprSyntheticOpaqueMVar (mkApp2 (mkConst ``Valid) C ψ) (← g.getTag)
  g.assign (mkAppN (mkConst ``Proves.closeValid) #[C, R, Γ, H, φ, g', hm])
  replaceMainGoal [← Symex.normValid g'.mvarId!]

end Seq

/-- `sol_leaf` (declared in `Calculus/ProofTree.lean`, whose tree closes a
leaf by it): `Seq.leafValid`. -/
elab_rules : tactic
  | `(tactic| sol_leaf) => Seq.leafValid
  | `(tactic| sol_leaf_wt) => Seq.leafValid

open Lean Elab Tactic Meta in
/-- `sol_prove` on a scoped sequent `H ⊢ φ` (`Proves C R [] H φ`,
`⊢ φ` under `open scoped Solidity.Scoped`): the walk as one kernel
evaluation (`Proves.of_residue`), one goal `leafᵢ` per leaf the closer
leaves. -/
@[tactic Solidity.tacticSol_prove]
def evalSolProveSeq : Tactic := fun stx => withMainContext do
  let `(tactic| sol_prove $[(steps := $n:num)]?) := stx | throwUnsupportedSyntax
  let g ← getMainGoal
  let ty ← instantiateMVars (← g.getType)
  let_expr Proves C R Γ₀ Γ H φ := ty | throwUnsupportedSyntax
  unless (← whnfR Γ₀).isAppOf ``List.nil do throwUnsupportedSyntax
  let rest := (← getUnsolvedGoals).erase g
  Symex.reporting g do
    let leaves ← Seq.prove g C R Γ H φ (n.map (·.getNat))
    setGoals (leaves ++ rest)

open Lean Elab Tactic Meta in
/-- `sol_prove` on a scoped goal `Valid φ` (`⊨ φ`): `Proves.valid` at the
rule set `.all`, then the walk on `⊢ φ` (`Seq.prove`), one goal `leafᵢ` per
leaf the closer leaves, each the walk's own sequent `H ⊢ ψ` (decision 89
extended to the `⊨` route). -/
@[tactic Solidity.tacticSol_prove]
def evalSolProveValid : Tactic := fun stx => withMainContext do
  let `(tactic| sol_prove $[(steps := $n:num)]?) := stx | throwUnsupportedSyntax
  let g ← getMainGoal
  let some (C, φ) ← Symex.validGoal? g | throwUnsupportedSyntax
  let rest := (← getUnsolvedGoals).erase g
  Symex.reporting g do
    let R := mkConst ``RuleSet.all
    let g' ← mkFreshExprSyntheticOpaqueMVar (ProofTree.provesE C φ) (← g.getTag)
    g.assign (mkAppN (mkConst ``Proves.valid) #[C, R, φ, g'])
    let leaves ← Seq.prove g'.mvarId! C R (ctxE []) (mkApp2 (mkConst ``Hyps.nil) C (ctxE [])) φ
      (n.map (·.getNat))
    setGoals (leaves ++ rest)

end Solidity
