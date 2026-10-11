import Solidity.Calculus.Derive

/-!
# `sol_prove` on a scoped sequent: `⊢ φ` as one kernel evaluation

Under `open scoped Solidity.Scoped` an obligation is stated `⊢ φ`, the
scoped sequent `Proves C .all [] .nil φ` (`Calculus/Surface.lean`),
so the strategy has to build a derivation, as today's `Proves.of_residue`
does (`Calculus/NFmlDerive.lean`).  A goal `Valid φ` (`⊨ φ`) goes the
same way: `Proves.valid`, then this walk (decision 89 extended), so its
leaves are scoped sequents too.

`Seq.run` walks the sequent as `Proves` has its rules: `intro`,
`allIntro`, `updIntro`, `bindIntro` take the formula's head into the
context, a modality fires the rule of its first statement (`Stmt.stepIn R`
at `Hyps.fresh`, the index the rules ask: under `⊢ₖ` solkey's rules alone) and walks each goal its premise
leaves, `empty` goes through the frames, `closeTrue` ends a `true` behind a
box context.  Every other leaf goes to `Proves.close`: `Fml.closableB` of
the sequent, and today's closer on its erasure (`Derive.residue`,
`Derive.synClose`, `Calculus/NFmlDerive.lean`, the decision procedure's
IR).  The kernel walks the leaf's context once for both (`Fml.closeErase`,
`Calculus/Closable.lean`).  A leaf the closer does not close stays the
walk's own sequent `H ⊢ φ` (`Seq.SLeaf`, `Seq.leafS`; M6c 6c, decision
89), a goal of the scoped calculus: `Proves.close_leaf` erases it to the
goal of today's calculus that today's leaf was, its first line spelled as
today's (`refine NFml.Proves.close_dropWt ?_`, `core_leaf_close_wt`).
`Seq.run_sound` reads the walk back as the derivation; the kernel checks
it as one evaluation (`Seq.residue R np full H φ = some ls`, where `full` only
orders `pick`'s two residues: `Seq.pickH`, `pickH_eq`), and the tactic
leaves one goal `leafᵢ` per leaf, as `sol_prove` on `Valid` does.

The walk is generic in what a leaf is (`α`), so the compiled run that
quotes the leaves for the tactic (`Seq.leafQuoteS`, which marks the residue
that closed each leaf) and the kernel's
(`Seq.leafS`) are one function.  It is written with `casesOn` (Gate G0,
condition 1); `n` bounds the steps down a path, `b` the steps of the whole
walk, handed from a goal to the next.

A leaf behind updates of either modality is `closableB`: an update's
reading asks only of the typed states it may end in, as the `Valid`
route's `Fml.posB` takes it too.

Two steps follow the closer's `sol_prove` (`Calculus/NFmlDerive.lean`).  A
split whose condition is ground under the context (`ground`,
`NFml.Derive.groundCond` on the erasure) and whose branch the closer
refutes keeps only the other branch, the refuted one closed by
`Proves.closeFalse` (`refutes`): `returnEarly` runs one path of its
callee, not 27.  A leaf's erasure goes to today's residue with the
parameters free, as today's leaves have them (`Fml.stripN`); where that
leaves goals and the leaf with the parameters' `∀` kept closes, that one
(`pick`, decision 27): a diamond that reads a parameter's range closes only
so.  An explicit `∀ uint x;` is never stripped (decision 28): the tactic
counts the parameters, the leading `∀`s up to the first one `cdl!` marked
explicit (`Symex.paramCount`), and hands the count to the walk (`np`).
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
    (fun I xs hv U c c' hu hb P post ω => both (r H I)
      (both (r ((((H.anonHavoc xs hv).pre I).upd m U).pre c)
          (.upd m (Upd.nil.pop hb) (.modalK m P (.pop .block P.ext .nil) post)))
        (r ((((H.anonHavoc xs hv).pre I).upd m U).pre c')
          (.upd m (Upd.nil.pop (hu.trans hb)) (.modalK m ω κ φ)))) b)
    (fun P e ω => r H (.modal m P (.drop e (.seq ω κ)) φ) b) ω

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

/-- Today's context and goal of an erased sequent: its implications, `∀`s
and updates taken in, as today's residue takes them (`Derive.residue`). -/
def peel : List (Solidity.Hyp C) → Solidity.NFml C → List (Solidity.Hyp C) × Solidity.NFml C
  | Γ, .imp a ψ => peel (Γ ++ [.pre a]) ψ
  | Γ, .all x p ψ => peel (Γ ++ [.all x p]) ψ
  | Γ, .upd m U ψ => peel (Γ ++ [.upd m U]) ψ
  | Γ, ψ => (Γ, ψ)

/-- Whether a split's condition `c` is ground in the context `H`: the
closer's test (`NFml.Derive.groundCond`) on the erasure of
`H, c ⟹ false`.  It only decides when to ask the closer to refute the
branch (`refutes`). -/
def ground {Γ : Ctx} (H : Hyps C [] Γ) (c : Fml C Γ) : Bool :=
  match peel [] (((H.pre c).wrap .ff).eraseR []) with
  | (Γ', .not .tt) => match Γ'.getLast? with
    | some (.pre c') => NFml.Derive.groundCond Γ' c'
    | _ => false
  | _ => false

/-- Whether the leaf `H ⟹ false` closes with nothing left: the branch of a
split whose condition `c` is ground and refuted by the closer
(`Proves.closeFalse`), as today's `Derive.splitRes` prunes it. -/
def refutes (leaf : {Γ : Ctx} → Hyps C [] Γ → Fml C Γ → Option (List α)) {Γ : Ctx}
    (H : Hyps C [] Γ) (c : Fml C Γ) : Bool :=
  ground H c && match leaf (H.pre c) .ff with
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
      (and := fun ψ χ H => (leaf H (.and ψ χ)).map (·, b))
      (imp := fun a ψ H => run R leaf rf n (H.pre a) ψ b)
      (upd := fun m U ψ H => run R leaf rf n (H.upd m U) ψ b)
      (modal := fun m P κ ψ H => modal R (fun H φ b => run R leaf rf n H φ b) rf m H P κ ψ b)
      (havoc := fun ψ H => (leaf H (.havoc ψ)).map (·, b))
      (all := fun x p ψ H => run R leaf rf n (H.all x p) ψ b)
      (bind := fun m x t ψ H => run R leaf rf n (H.bind m x t) ψ b)
      (anon := fun xs ψ H => (leaf H (.anon xs ψ)).map (·, b)) H

/-- Today's formula without its first `n` leading quantifiers, every one
where `n` is `none`. -/
def _root_.Solidity.NFml.stripN : Option Nat → Solidity.NFml C → Solidity.NFml C
  | none, φ => φ.stripAlls
  | some 0, φ => φ
  | some (n + 1), .all _ _ φ => Solidity.NFml.stripN (some n) φ
  | some (_ + 1), φ => φ

/-- A formula is valid where it is with its first leading quantifiers'
locals free. -/
theorem _root_.Solidity.NFml.Valid.of_stripN : {n : Option Nat} → {φ : Solidity.NFml C} →
    NFml.Valid (φ.stripN n) → NFml.Valid φ
  | none, _, h => NFml.Valid.of_stripAlls (by rwa [Solidity.NFml.stripN] at h)
  | some (n + 1), .all x p φ, h =>
    NFml.Valid.all_of_free x p (NFml.Valid.of_stripN (n := some n) (φ := φ) h)
  | some 0, _, h => by rwa [Solidity.NFml.stripN] at h
  | some (_ + 1), .tt, h | some (_ + 1), .eq _ _, h | some (_ + 1), .not _, h
  | some (_ + 1), .and _ _, h | some (_ + 1), .imp _ _, h
  | some (_ + 1), .upd _ _ _, h | some (_ + 1), .havoc _, h | some (_ + 1), .anon _ _, h
  | some (_ + 1), .defined _, h => h

/-- Today's residue `r` of an erased leaf `e`, with the `np` parameters'
quantifiers stripped (`Fml.stripN`), as today's leaves have them free;
where that leaves goals but the quantified leaf, its parameters in the
context (`.all`), leaves none, nothing: a diamond's leaf that reads a
parameter's range (a mapping's key, an interval) closes only so.  An
explicit `∀` past the parameters is kept either way. -/
def pick {β : Type} (np : Option Nat) (r : Solidity.NFml C → Option (List β × Nat))
    (e : Solidity.NFml C) : Option (List β) :=
  match r (e.stripN np) with
  | some ([], _) => some []
  | r₁ => match np, e with
    | some 0, _ => r₁.map (·.1)
    | _, .all .. =>
      match r e with
      | some ([], _) => some []
      | _ => r₁.map (·.1)
    | _, _ => r₁.map (·.1)

/-- `pick`, the quantified leaf tried first when `full` says so: the same
leaves (`pickH_eq`), with one residue where `pick` would run two.  The
tactic sets `full` when the compiled walk's leaves close only with their
parameters (`leafQuoteI`), so that the kernel does not run the stripped
residue there first. -/
def pickH {β : Type} (full : Bool) (np : Option Nat) (r : Solidity.NFml C → Option (List β × Nat))
    (e : Solidity.NFml C) : Option (List β) :=
  bif full then
    (match e with
    | .all .. =>
      match r e with
      | some ([], _) => some []
      | _ => pick np r e
    | _ => pick np r e)
  else pick np r e

theorem pickH_eq {β : Type} (full : Bool) (np : Option Nat)
    (r : Solidity.NFml C → Option (List β × Nat)) (e : Solidity.NFml C) :
    pickH full np r e = pick np r e := by
  cases full
  · rfl
  · simp only [pickH, cond_true]
    split
    · split
      · rename_i b h
        unfold pick
        split
        · rfl
        · rename_i r₁ hr₁
          split
          · exact absurd (by simpa only [Solidity.NFml.stripN] using h) (hr₁ b)
          · simp only [h]
          · rename_i hne; exact absurd rfl (hne _ _ _)
      · rfl
    · rfl

/-- A leaf: `Proves.close`'s side condition and the erasure in one pass
(`Fml.closeErase`, which is `Fml.closableB` beside `Fml.erase`), and the
residue `r` of the erasure (`pick`, by `pickH`). -/
def leafWith {β : Type} (full : Bool) (np : Option Nat)
    (r : Solidity.NFml C → Option (List β × Nat)) {Γ : Ctx}
    (H : Hyps C [] Γ) (φ : Fml C Γ) : Option (List β) :=
  match (H.wrap φ).closeErase [] with
  | some e => pickH full np r e.2
  | none => none

/-- A leaf for the kernel: today's residue (`Derive.residue`). -/
def leafRes (np : Option Nat) (full : Bool) {Γ : Ctx} (H : Hyps C [] Γ) (φ : Fml C Γ) :
    Option (List (NFml.Derive.Leaf C)) :=
  leafWith full np (NFml.Derive.residue NFml.Derive.budget NFml.Derive.synClose
    NFml.Derive.budget []) H φ

/-- The same leaf quoted, for the tactic (`Derive.residueQuote`), the
contract named by `c`. -/
def leafQuote (c : Lean.Expr) (np : Option Nat) {Γ : Ctx} (H : Hyps C [] Γ) (φ : Fml C Γ) :
    Option (List (Lean.Expr × Lean.Expr)) :=
  leafWith false np (NFml.Derive.residueQuote c []) H φ

/-! ### The leaves left: scoped sequents

A leaf the closer does not close stays the walk's own sequent `H ⊢ φ`
(`SLeaf`, decision 89), not today's sequent of its erasure: the closer
reads the erasure (`leafRes`, today's residue and `synClose`), and the
goal it leaves is scoped.  A tactic that closes it erases it first
(`Proves.close_leaf`, `Seq.leafErase`): the same goal of today's calculus
that today's leaf had. -/

/-- A leaf the walk leaves: a sequent of the outer scope `[]`. -/
abbrev SLeaf (C : Contract) := (Γ : Ctx) × Hyps C [] Γ × Fml C Γ

/-- A leaf for the kernel: closed (`[]`) where today's residue of its
erasure leaves nothing (`leafRes`), the sequent itself where it leaves a
goal.  Today's residue leaves at most one goal of a leaf: it only moves
the connectives in front into the context (`Derive.residue`). -/
def leafS (np : Option Nat) (full : Bool) {Γ : Ctx} (H : Hyps C [] Γ) (φ : Fml C Γ) :
    Option (List (SLeaf C)) :=
  (leafRes np full H φ).map fun ls => bif ls.isEmpty then [] else [⟨_, H, φ⟩]

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

/-- `leafS` for the tactic, and which of `pick`'s residues closed the leaf:
`.inr true` when only the quantified one did, `.inr false` otherwise, then
the leaf quoted (`.inl`, `SLeaf.quote`) where it is left. -/
def leafQuoteS (c : Lean.Expr) (np : Option Nat) {Γ : Ctx} (H : Hyps C [] Γ) (φ : Fml C Γ) :
    Option (List (Lean.Expr ⊕ Bool)) :=
  match (H.wrap φ).closeErase [] with
  | some e =>
    let r := NFml.Derive.residue (C := C) NFml.Derive.budget NFml.Derive.synClose
      NFml.Derive.budget []
    match r (e.2.stripN np) with
    | some ([], _) => some [.inr false]
    | r₁ =>
      let rest : Option (List (Lean.Expr ⊕ Bool)) :=
        r₁.map fun _ => [.inr false, .inl (SLeaf.quote c np H φ)]
      match np, e.2 with
      | some 0, _ => rest
      | _, .all .. =>
        match r e.2 with
        | some ([], _) => some [.inr true]
        | _ => rest
      | _, _ => rest
  | none => none

/-- The steps the walk is given, down a path and in all (today's
`Derive.budget`). -/
def fuel : Nat := NFml.Derive.budget

/-- **`sol_prove`'s check**: the leaves the walk leaves, none when every
leaf closes; `np` the sequent's parameters (`pick`); `full` only orders
`pick`'s two residues (`pickH`).  A split's branch is refuted as `pick`
reads its leaf. -/
def residue (R : RuleSet) (np : Option Nat) (full : Bool) {Γ : Ctx} (H : Hyps C [] Γ)
    (φ : Fml C Γ) : Option (List (SLeaf C)) :=
  (run R (leafS np full) (refutes (leafRes np false)) fuel H φ fuel).map (·.1)

/-- `#solkey_scan`'s view of `⊢ φ` (`Frontend/Problems.lean`): how many
leaves the walk leaves, closed by `synClose` or (`walk`) not, and the most
storage writes in one leaf's context (`Derive.storageWrites`); `none` when
the walk runs out or a step has no rule. -/
def scanLeaves (walk : Bool) (φ : Fml C []) : Option (Nat × Nat) :=
  let r := NFml.Derive.residue NFml.Derive.budget
    (if walk then fun _ _ => false else NFml.Derive.synClose) NFml.Derive.budget []
  (run .all (leafWith false none r) (refutes (leafRes none false)) fuel .nil φ fuel).map fun (ls, _) =>
    (ls.length, ls.foldl (fun m l => max m (NFml.Derive.storageWrites l.1)) 0)

/-- `residue`, the leaves quoted, each walk leaf marked by the residue that
closed it (`leafQuoteS`). -/
def residueQuote (R : RuleSet) (c : Lean.Expr) (np : Option Nat) {Γ : Ctx} (H : Hyps C [] Γ)
    (φ : Fml C Γ) : Option (List (Lean.Expr ⊕ Bool)) :=
  (run R (leafQuoteS c np) (refutes (leafQuote c np)) fuel H φ fuel).map (·.1)

/-! ### A leaf erased

`Proves.close` on a leaf left by `sol_prove`, with the goal today's leaf
had: the erasure, its parameters free (`NFml.stripN`), and the connectives
in front moved into today's context (`peel`). -/

/-- The erased leaf of `H ⊢ φ`, today's context and goal. -/
def leafErase (np : Option Nat) {Γ : Ctx} (H : Hyps C [] Γ) (φ : Fml C Γ) :
    Option (List (Solidity.Hyp C) × Solidity.NFml C) :=
  ((H.wrap φ).closeErase []).map fun e => peel [] (e.2.stripN np)

/-- `leafErase`, quoted (`Hyp.quoteList`, `NFml.quote`). -/
def leafEraseQuote (c : Lean.Expr) (np : Option Nat) {Γ : Ctx} (H : Hyps C [] Γ)
    (φ : Fml C Γ) : Option (Lean.Expr × Lean.Expr) :=
  (leafErase np H φ).map fun l => (Solidity.Hyp.quoteList c l.1, Solidity.NFml.quote c l.2)

/-- `leafFits` of the erased leaf: `synClose`'s bounds, which `sol_prove?`
asks before it reduces a leaf. -/
def leafFitsS (np : Option Nat) {Γ : Ctx} (H : Hyps C [] Γ) (φ : Fml C Γ) : Bool :=
  match leafErase np H φ with
  | some l => NFml.Derive.leafFits l.1 l.2
  | none => true

/-- What `peel` takes in front stays in front. -/
theorem peel_wrap : (Γ : List (Solidity.Hyp C)) → (φ : Solidity.NFml C) →
    Hyp.wrap (peel Γ φ).1 (peel Γ φ).2 = Hyp.wrap Γ φ
  | Γ, .imp a ψ => by
    simp only [peel]; rw [peel_wrap, Hyp.wrap_append]; rfl
  | Γ, .all x p ψ => by
    simp only [peel]; rw [peel_wrap, Hyp.wrap_append]; rfl
  | Γ, .upd m U ψ => by
    simp only [peel]; rw [peel_wrap, Hyp.wrap_append]; rfl
  | _, .tt | _, .eq _ _ | _, .defined _ | _, .not _ | _, .and _ _ | _, .havoc _
  | _, .anon _ _ => rfl

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
  | inv I xs hv U c c' hu hb P post =>
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
  | none => simp only [hl, Bool.and_false, reduceCtorEq] at h
  | some ls =>
    cases ls with
    | nil => exact hleaf _ _ [] hl fun _ h => nomatch h
    | cons _ _ => simp only [hl, Bool.and_false, reduceCtorEq] at h

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
    | and => exact leaf_sound hleaf h hl
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

/-- What `pick` leaves of today's residue is valid once its leaves are
proved. -/
theorem pick_valid {np : Option Nat} {e : Solidity.NFml C} {ls : List (NFml.Derive.Leaf C)}
    (h : pick np (NFml.Derive.residue NFml.Derive.budget NFml.Derive.synClose
      NFml.Derive.budget []) e = some ls)
    (hl : ∀ l ∈ ls, NFml.Proves .all l.1 l.2) : NFml.Valid e := by
  have hv : ∀ {e' : Solidity.NFml C} {ls' : List (NFml.Derive.Leaf C)} {b : Nat},
      NFml.Derive.residue NFml.Derive.budget NFml.Derive.synClose
        NFml.Derive.budget [] e' = some (ls', b) →
      (∀ l ∈ ls', NFml.Proves .all l.1 l.2) → NFml.Valid e' :=
    fun hr hl' => NFml.Proves.valid (NFml.Proves.of_synResidue hr hl')
  have hs : ∀ {r : Option (List (NFml.Derive.Leaf C) × Nat)},
      NFml.Derive.residue NFml.Derive.budget NFml.Derive.synClose
        NFml.Derive.budget [] (e.stripN np) = r → r.map (·.1) = some ls →
      NFml.Valid e := fun hr h => by
    obtain ⟨⟨ls', b'⟩, hr', he⟩ := Option.map_eq_some_iff.1 h
    cases he
    exact NFml.Valid.of_stripN (hv (hr.trans hr') hl)
  unfold pick at h
  split at h
  · rename_i b h1
    exact NFml.Valid.of_stripN (hv h1 NFml.Derive.leaves_nil)
  · split at h
    · exact hs rfl h
    · split at h
      · rename_i b h2
        exact hv h2 NFml.Derive.leaves_nil
      · exact hs rfl h
    · exact hs rfl h

/-- A leaf `leafRes` takes is proved once today's leaves are. -/
theorem leafRes_sound {R : RuleSet} (np : Option Nat) (full : Bool) {Γ : Ctx} (H : Hyps C [] Γ)
    (φ : Fml C Γ) (ls : List (NFml.Derive.Leaf C)) (h : leafRes np full H φ = some ls)
    (hl : ∀ l ∈ ls, NFml.Proves .all l.1 l.2) : Proves C R [] H φ := by
  unfold leafRes leafWith at h
  split at h
  · rename_i e he
    rw [pickH_eq] at h
    rw [Fml.closeErase_eq] at he
    obtain ⟨B, hB, rfl⟩ := Option.map_eq_some_iff.1 he
    have hc : (H.wrap φ).closableB [] = true := by
      simp only [Fml.closableB, hB, Option.isSome_some]
    exact Proves.close [] rfl List.nodup_nil (pick_valid h hl) hc (fun _ _ h => nomatch h)
  · cases h

/-- A leaf `leafS` takes is proved once the sequent it leaves is. -/
theorem leafS_sound {R : RuleSet} (np : Option Nat) (full : Bool) {Γ : Ctx} (H : Hyps C [] Γ)
    (φ : Fml C Γ) (ls : List (SLeaf C)) (h : leafS np full H φ = some ls)
    (hl : ∀ l ∈ ls, Proves C R [] l.2.1 l.2.2) : Proves C R [] H φ := by
  obtain ⟨ls', h', rfl⟩ := Option.map_eq_some_iff.1 h
  cases hls : ls'.isEmpty
  · exact hl ⟨_, H, φ⟩ (by simp only [hls, cond_false, List.mem_singleton])
  · exact leafRes_sound np full H φ ls' h' (by
      rw [List.isEmpty_iff.1 hls]; exact fun _ h => nomatch h)

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

/-- **A leaf closed on its erasure**, as today's leaf was: `Proves.close`,
the erasure with its first `np` quantifiers' locals free and the
connectives in front in today's context (`Seq.leafErase`). -/
theorem Proves.close_leaf {R : RuleSet} {np : Option Nat} {Γ : Ctx} {H : Hyps C [] Γ}
    {φ : Fml C Γ} {Γ' : List (Solidity.Hyp C)} {φ' : Solidity.NFml C}
    (he : Seq.leafErase np H φ = some (Γ', φ')) (h : NFml.Valid (Hyp.wrap Γ' φ')) :
    Proves C R [] H φ := by
  unfold Seq.leafErase at he
  obtain ⟨e, hce, hp⟩ := Option.map_eq_some_iff.1 he
  rw [Fml.closeErase_eq] at hce
  obtain ⟨B, hB, rfl⟩ := Option.map_eq_some_iff.1 hce
  have hc : (H.wrap φ).closableB [] = true := by
    simp only [Fml.closableB, hB, Option.isSome_some]
  refine Proves.close [] rfl List.nodup_nil (NFml.Valid.of_stripN (n := np) ?_) hc
    (fun _ _ h => nomatch h)
  have hw := Seq.peel_wrap [] (((H.wrap φ).erase []).stripN np)
  rw [hp] at hw
  have hw' : Hyp.wrap Γ' φ' = ((H.wrap φ).erase []).stripN np := hw
  rw [← hw']
  exact h

/-- `Proves.close_leaf` with the `wt` premises set aside, as
`NFml.Proves.close_dropWt` sets them aside on today's leaf. -/
theorem Proves.close_leaf_dropWt {R : RuleSet} {np : Option Nat} {Γ : Ctx} {H : Hyps C [] Γ}
    {φ : Fml C Γ} {Γ' : List (Solidity.Hyp C)} {φ' : Solidity.NFml C}
    (he : Seq.leafErase np H φ = some (Γ', φ'))
    (h : NFml.Valid (Hyp.wrap (NFml.Derive.dropWt Γ') φ')) : Proves C R [] H φ :=
  Proves.close_leaf he fun σ => NFml.Derive.wrap_dropWt Γ' σ (h σ)

/-- **`sol_prove`'s proof of a sequent**: the walk's residue, each leaf it
leaves proved. -/
theorem Proves.of_residue {R : RuleSet} {np : Option Nat} {Γ : Ctx} {H : Hyps C [] Γ}
    {φ : Fml C Γ} {full : Bool} {ls : List (Seq.SLeaf C)}
    (h : Seq.residue R np full H φ = some ls)
    (hl : ∀ l ∈ ls, Proves C R [] l.2.1 l.2.2) : Proves C R [] H φ := by
  obtain ⟨⟨ls', b'⟩, hr, he⟩ := Option.map_eq_some_iff.1 h
  cases he
  exact Seq.run_sound (P := fun l : Seq.SLeaf C => Proves C R [] l.2.1 l.2.2)
    (fun H φ ls h hl => Seq.leafS_sound np full H φ ls h hl)
    (Seq.refutes_sound (P := fun l : NFml.Derive.Leaf C => NFml.Proves .all l.1 l.2)
      (fun H φ ls h hl => Seq.leafRes_sound np false H φ ls h hl))
    _ H φ _ _ _ hr hl

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
def prove (g : MVarId) (C R Γ H φ : Expr) : MetaM (List MVarId) := do
  let some n := C.constName? | throwError "sol_prove: the contract is not a named constant"
  if H.hasFVar || H.hasMVar || φ.hasFVar || φ.hasMVar || R.hasFVar || R.hasMVar then
    throwError "sol_prove: the sequent mentions a local hypothesis or a metavariable"
  let φe ← Symex.evaluable φ
  let npV ← paramCount H φe
  let np := toExpr npV
  let leafTy := mkApp (mkConst ``SLeaf) C
  let resTy := mkApp (mkConst ``Option [0]) (mkApp (mkConst ``List [0]) leafTy)
  let mut full := false
  let lemmaFor (full : Bool) (ls : Expr) : MetaM Expr := do
    let someLs := mkApp2 (mkConst ``Option.some [0]) (mkApp (mkConst ``List [0]) leafTy) ls
    let type := mkApp3 (mkConst ``Eq [1]) resTy
      (mkAppN (mkConst ``residue) #[C, R, np, toExpr full, Γ, H, φ]) someLs
    NFml.Derive.kernelLemma type (mkApp2 (mkConst ``Eq.refl [1]) resTy someLs)
  let assignWith (full : Bool) (ls h : Expr) (hl : Expr) : MetaM Unit :=
    g.assign (mkAppN (mkConst ``Proves.of_residue) #[C, R, np, Γ, H, φ, toExpr full, ls, h, hl])
  let nil := mkApp (mkConst ``List.nil [0]) leafTy
  -- the compiled walk first, then one kernel check of its leaves, as
  -- today's `sol_prove` (`Derive.prove`): a kernel try at no leaves costs a
  -- second evaluation where the closer leaves some, in the declaration's
  -- heartbeats
  let qTy := mkApp (mkConst ``Option [0]) (mkApp (mkConst ``List [0])
    (mkApp2 (mkConst ``Sum [0, 0]) (mkConst ``Expr) (mkConst ``Bool)))
  let some marked ← unsafe evalExpr (Option (List (Expr ⊕ Bool))) qTy
      (mkAppN (mkConst ``residueQuote) #[C, R, quoteConstName n, np, Γ, H, φe])
    | throwError "sol_prove: the walk does not reach the end of the sequent: a step with no \
        rule, a leaf `Proves.close` does not take (`Fml.closableB`: a modality left, a negated \
        or assumed part not first-order, or a hidden binder's name reused), or more than \
        {fuel} steps"
  let leaves := marked.filterMap fun | .inl l => some l | .inr _ => none
  -- the quantified residue first where more of the walk's leaves close
  -- only with their parameters than not (`pickH`): the same leaves
  let marks := marked.filterMap fun | .inr b => some b | .inl _ => none
  full := 2 * (marks.filter id).length > marks.length
  if leaves.isEmpty then
    let h ← try lemmaFor full nil
      catch e => throwError "sol_prove: the kernel rejects the walk:{indentD e.toMessageData}"
    assignWith full nil h (mkApp2 (mkConst ``SLeaf.nil) C R)
    return []
  let ls ← mkListLit leafTy leaves
  let h ← try lemmaFor full ls
    catch e => throwError "sol_prove: the kernel rejects the residue:{indentD e.toMessageData}"
  -- a leaf `⟨Γ', (H', φ')⟩`: its goal `H' ⊢ φ'`
  let parts (l : Expr) : Expr × Expr × Expr :=
    let pr := l.getArg! 3
    (l.getArg! 2, pr.getArg! 2, pr.getArg! 3)
  let nilCtx := mkApp (mkConst ``List.nil [0]) (mkConst ``LTy)
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
  assignWith full ls h hl
  return goals.toList

/-- `leafFitsS` on a leaf goal `H ⊢ φ` the walk left, run as compiled
code; today's `goalFits` on any other goal. -/
def goalFits (l : MVarId) : MetaM Bool := do
  let ty ← instantiateMVars (← l.getType)
  let_expr Proves C _ Γ₀ Γ H φ := ty | NFml.Derive.goalFits l
  if ty.hasFVar || ty.hasMVar || !(← whnfR Γ₀).isAppOf ``List.nil then return true
  let φe ← Symex.evaluable φ
  let np := toExpr (← paramCount H φe)
  unsafe evalExpr Bool (mkConst ``Bool) (mkAppN (mkConst ``leafFitsS) #[C, np, Γ, H, φe])

/-- `Proves.close_leaf` (with `wt`, `Proves.close_leaf_dropWt`) on the main
goal, a leaf `H ⊢ φ` of the outer scope: its erasure computed and quoted
(`leafEraseQuote`), checked by the kernel, and the goal today's leaf had,
`NFml.Valid (Hyp.wrap Γ' φ')`, left. -/
def closeLeaf (wt : Bool) : TacticM Unit := withMainContext do
  let g ← getMainGoal
  let ty ← instantiateMVars (← g.getType)
  let_expr Proves C R Γ₀ Γ H φ := ty | throwError "not a scoped sequent"
  unless (← whnfR Γ₀).isAppOf ``List.nil do throwError "not a sequent of the outer scope"
  let some n := C.constName? | throwError "the contract is not a named constant"
  if ty.hasFVar || ty.hasMVar then throwError "the sequent mentions a local or a metavariable"
  let φe ← Symex.evaluable φ
  let np := toExpr (← paramCount H φe)
  let pairTy := mkApp2 (mkConst ``Prod [0, 0]) (mkApp (mkConst ``List [0]) (mkApp (mkConst ``Solidity.Hyp) C))
    (mkApp (mkConst ``Solidity.NFml) C)
  let some (Γ', φ') ← unsafe evalExpr (Option (Expr × Expr))
      (mkApp (mkConst ``Option [0]) (mkApp2 (mkConst ``Prod [0, 0]) (mkConst ``Expr) (mkConst ``Expr)))
      (mkAppN (mkConst ``leafEraseQuote) #[C, quoteConstName n, np, Γ, H, φe])
    | throwError "the leaf is not one `Proves.close` takes (`Fml.closableB`)"
  let some' := mkApp2 (mkConst ``Option.some [0]) pairTy
    (mkAppN (mkConst ``Prod.mk [0, 0]) #[mkApp (mkConst ``List [0]) (mkApp (mkConst ``Solidity.Hyp) C),
      mkApp (mkConst ``Solidity.NFml) C, Γ', φ'])
  let optTy := mkApp (mkConst ``Option [0]) pairTy
  let he ← NFml.Derive.kernelLemma
    (mkApp3 (mkConst ``Eq [1]) optTy (mkAppN (mkConst ``leafErase) #[C, np, Γ, H, φ]) some')
    (mkApp2 (mkConst ``Eq.refl [1]) optTy some')
  let Γ'' ← if wt then mkAppM ``NFml.Derive.dropWt #[Γ'] else pure Γ'
  let goal ← mkAppM ``NFml.Valid #[← mkAppM ``Solidity.Hyp.wrap #[Γ'', φ']]
  let g' ← mkFreshExprSyntheticOpaqueMVar goal (← g.getTag)
  g.assign (mkAppN (mkConst (if wt then ``Proves.close_leaf_dropWt else ``Proves.close_leaf))
    #[C, R, np, Γ, H, φ, Γ', φ', he, g'])
  replaceMainGoal [g'.mvarId!]

end Seq

/-- `core_leaf_close`: `Proves.close_leaf` on a leaf `sol_prove` left
(`core_leaf_close_wt`: `Proves.close_leaf_dropWt`), the goal today's leaf
had left. -/
syntax "core_leaf_close" : tactic
/-- `core_leaf_close` with the `wt` premises set aside. -/
syntax "core_leaf_close_wt" : tactic

elab_rules : tactic
  | `(tactic| core_leaf_close) => Seq.closeLeaf false
  | `(tactic| core_leaf_close_wt) => Seq.closeLeaf true

/-- Today's first line of a leaf, read on a leaf the scoped `sol_prove`
left: `refine NFml.Proves.close_dropWt ?_` and `refine NFml.Proves.close ?_`
are `Proves.close_leaf_dropWt` and `Proves.close_leaf` there (decision 89),
today's rules on today's sequent. -/
macro_rules
  | `(tactic| refine NFml.Proves.close_dropWt ?_) =>
    `(tactic| first | core_leaf_close_wt | refine Solidity.NFml.Proves.close_dropWt ?_)
  | `(tactic| refine NFml.Proves.close ?_) =>
    `(tactic| first | core_leaf_close | refine Solidity.NFml.Proves.close ?_)

open Lean Elab Tactic Meta in
/-- `sol_prove` on a scoped sequent `H ⊢ φ` (`Proves C R [] H φ`,
`⊢ φ` under `open scoped Solidity.Scoped`): the walk as one kernel
evaluation (`Proves.of_residue`), one goal `leafᵢ` per leaf the closer
leaves. -/
@[tactic Solidity.tacticSol_prove]
def evalSolProveSeq : Tactic := fun _ => withMainContext do
  let g ← getMainGoal
  let ty ← instantiateMVars (← g.getType)
  let_expr Proves C R Γ₀ Γ H φ := ty | throwUnsupportedSyntax
  unless (← whnfR Γ₀).isAppOf ``List.nil do throwUnsupportedSyntax
  let rest := (← getUnsolvedGoals).erase g
  Symex.reporting g do
    let leaves ← Seq.prove g C R Γ H φ
    setGoals (leaves ++ rest)

open Lean Elab Tactic Meta in
/-- `sol_prove` on a scoped goal `Valid φ` (`⊨ φ`): `Proves.valid` at the
rule set `.all`, then the walk on `⊢ φ` (`Seq.prove`), one goal `leafᵢ` per
leaf the closer leaves, each the walk's own sequent `H ⊢ ψ` (decision 89
extended to the `⊨` route). -/
@[tactic Solidity.tacticSol_prove]
def evalSolProveValid : Tactic := fun _ => withMainContext do
  let g ← getMainGoal
  let some (C, φ) ← Symex.validGoal? g | throwUnsupportedSyntax
  let rest := (← getUnsolvedGoals).erase g
  Symex.reporting g do
    let R := mkConst ``RuleSet.all
    let nilCtx := mkApp (mkConst ``List.nil [0]) (mkConst ``LTy)
    let H := mkApp2 (mkConst ``Hyps.nil) C nilCtx
    let g' ← mkFreshExprSyntheticOpaqueMVar
      (mkAppN (mkConst ``Proves) #[C, R, nilCtx, nilCtx, H, φ]) (← g.getTag)
    g.assign (mkAppN (mkConst ``Proves.valid) #[C, R, φ, g'])
    let leaves ← Seq.prove g'.mvarId! C R nilCtx H φ
    setGoals (leaves ++ rest)

end Solidity
