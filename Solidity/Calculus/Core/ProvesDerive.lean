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
The kernel walks the leaf's context once for both (`Fml.closeErase`,
`Calculus/Core/Closable.lean`).
`Seq.run_sound` reads the walk back as the derivation; the kernel checks
it as one evaluation (`Seq.residue np full H φ = some ls`, where `full` only
orders `pick`'s two residues: `Seq.pickH`, `pickH_eq`), and the tactic
leaves one goal `leafᵢ` per leaf, as `sol_prove` on `Core.Valid` does.

The walk is generic in what a leaf is (`α`), so the compiled run that
quotes the leaves for the tactic (`Seq.leafQuoteI`, which marks the residue
that closed each leaf) and the kernel's
(`Seq.leafRes`) are one function.  It is written with `casesOn` (Gate G0,
condition 1); `n` bounds the steps down a path, `b` the steps of the whole
walk, handed from a goal to the next.

A leaf behind updates of either modality is `closableB`: an update's
reading asks only of the typed states it may end in, as the `Core.Valid`
route's `Fml.posB` takes it too.

Two steps follow today's `sol_prove` (`Calculus/Derive.lean`).  A split
whose condition is ground under the context (`ground`, today's
`Derive.groundCond` on the erasure) and whose branch the closer refutes
keeps only the other branch, the refuted one closed by `Proves.closeFalse`
(`refutes`, today's `Derive.splitRes`): `returnEarly` runs one path of its
callee, not 27.  A leaf's erasure goes to today's residue with the
parameters free, as today's leaves have them (`Fml.stripN`); where that
leaves goals and the leaf with the parameters' `∀` kept closes, that one
(`pick`, decision 27): a diamond that reads a parameter's range closes only
so.  An explicit `∀ uint x;` is never stripped (decision 28): the tactic
counts the parameters, the leading `∀`s up to the first one `cdl!` marked
explicit (`Symex.paramCount`), and hands the count to the walk (`np`).
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
def modal (r : {Γ : Ctx} → Hyps C [] Γ → Fml C Γ → Nat → Option (List α × Nat))
    (x : {Γ : Ctx} → Hyps C [] Γ → Fml C Γ → Bool) (m : Modality) {Γ Γ₁ Γ₀ : Ctx} (H : Hyps C [] Γ) (P : Prog C Γ Γ₁) (κ : Frames C Γ₁ Γ₀)
    (φ : Fml C Γ₀) (b : Nat) : Option (List α × Nat) :=
  Prog.casesOn (motive_2 := fun Γ Γ₁ _ => Frames C Γ₁ Γ₀ → Hyps C [] Γ → Option (List α × Nat)) P
    (fun κ H => r H (κ.exit m φ) b)
    (fun s ω κ H => match s.step (H.fresh (.modal m (.cons s ω) κ φ)) m with
      | some p => premise r x H m ω κ φ p b
      | none => none) κ H

/-- Today's context and goal of an erased sequent: its implications, `∀`s
and updates taken in, as today's residue takes them (`Derive.residue`). -/
def peel : List (Solidity.Hyp C) → Solidity.Fml C → List (Solidity.Hyp C) × Solidity.Fml C
  | Γ, .imp a ψ => peel (Γ ++ [.pre a]) ψ
  | Γ, .all x p ψ => peel (Γ ++ [.all x p]) ψ
  | Γ, .upd m U ψ => peel (Γ ++ [.upd m U]) ψ
  | Γ, ψ => (Γ, ψ)

/-- Whether a split's condition `c` is ground in the context `H`: today's
test (`Derive.groundCond`) on the erasure of `H, c ⟹ false`.  It only
decides when to ask the closer to refute the branch (`refutes`), as today's
`Derive.splitRes` asks it. -/
def ground {Γ : Ctx} (H : Hyps C [] Γ) (c : Fml C Γ) : Bool :=
  match peel [] (((H.pre c).wrap .ff).eraseR []) with
  | (Γ', .not .tt) => match Γ'.getLast? with
    | some (.pre c') => Solidity.Derive.groundCond Γ' c'
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
def run (leaf : {Γ : Ctx} → Hyps C [] Γ → Fml C Γ → Option (List α))
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
      (imp := fun a ψ H => run leaf rf n (H.pre a) ψ b)
      (upd := fun m U ψ H => run leaf rf n (H.upd m U) ψ b)
      (modal := fun m P κ ψ H => modal (fun H φ b => run leaf rf n H φ b) rf m H P κ ψ b)
      (havoc := fun ψ H => (leaf H (.havoc ψ)).map (·, b))
      (all := fun x p ψ H => run leaf rf n (H.all x p) ψ b)
      (bind := fun m x t ψ H => run leaf rf n (H.bind m x t) ψ b)
      (anon := fun xs ψ H => (leaf H (.anon xs ψ)).map (·, b)) H

/-- Today's formula without its first `n` leading quantifiers, every one
where `n` is `none`. -/
def _root_.Solidity.Fml.stripN : Option Nat → Solidity.Fml C → Solidity.Fml C
  | none, φ => φ.stripAlls
  | some 0, φ => φ
  | some (n + 1), .all _ _ φ => Solidity.Fml.stripN (some n) φ
  | some (_ + 1), φ => φ

/-- A formula is valid where it is with its first leading quantifiers'
locals free. -/
theorem _root_.Solidity.Valid.of_stripN : {n : Option Nat} → {φ : Solidity.Fml C} →
    Solidity.Valid (φ.stripN n) → Solidity.Valid φ
  | none, _, h => Solidity.Valid.of_stripAlls (by rwa [Solidity.Fml.stripN] at h)
  | some (n + 1), .all x p φ, h =>
    Solidity.Valid.all_of_free x p (Solidity.Valid.of_stripN (n := some n) (φ := φ) h)
  | some 0, _, h => by rwa [Solidity.Fml.stripN] at h
  | some (_ + 1), .tt, h | some (_ + 1), .eq _ _, h | some (_ + 1), .not _, h
  | some (_ + 1), .and _ _, h | some (_ + 1), .imp _ _, h | some (_ + 1), .modal _ _ _, h
  | some (_ + 1), .upd _ _ _, h | some (_ + 1), .havoc _, h | some (_ + 1), .anon _ _, h
  | some (_ + 1), .defined _, h => h

/-- Today's residue `r` of an erased leaf `e`, with the `np` parameters'
quantifiers stripped (`Fml.stripN`), as today's leaves have them free;
where that leaves goals but the quantified leaf, its parameters in the
context (`.all`), leaves none, nothing: a diamond's leaf that reads a
parameter's range (a mapping's key, an interval) closes only so.  An
explicit `∀` past the parameters is kept either way. -/
def pick {β : Type} (np : Option Nat) (r : Solidity.Fml C → Option (List β × Nat))
    (e : Solidity.Fml C) : Option (List β) :=
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
def pickH {β : Type} (full : Bool) (np : Option Nat) (r : Solidity.Fml C → Option (List β × Nat))
    (e : Solidity.Fml C) : Option (List β) :=
  bif full then
    (match e with
    | .all .. =>
      match r e with
      | some ([], _) => some []
      | _ => pick np r e
    | _ => pick np r e)
  else pick np r e

theorem pickH_eq {β : Type} (full : Bool) (np : Option Nat)
    (r : Solidity.Fml C → Option (List β × Nat)) (e : Solidity.Fml C) :
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
          · exact absurd (by simpa only [Solidity.Fml.stripN] using h) (hr₁ b)
          · simp only [h]
          · rename_i hne; exact absurd rfl (hne _ _ _)
      · rfl
    · rfl

/-- A leaf: `Proves.close`'s side condition and the erasure in one pass
(`Fml.closeErase`, which is `Fml.closableB` beside `Fml.erase`), and the
residue `r` of the erasure (`pick`, by `pickH`). -/
def leafWith {β : Type} (full : Bool) (np : Option Nat)
    (r : Solidity.Fml C → Option (List β × Nat)) {Γ : Ctx}
    (H : Hyps C [] Γ) (φ : Fml C Γ) : Option (List β) :=
  match (H.wrap φ).closeErase [] with
  | some e => pickH full np r e.2
  | none => none

/-- A leaf for the kernel: today's residue (`Derive.residue`). -/
def leafRes (np : Option Nat) (full : Bool) {Γ : Ctx} (H : Hyps C [] Γ) (φ : Fml C Γ) :
    Option (List (Solidity.Derive.Leaf C)) :=
  leafWith full np (Solidity.Derive.residue Solidity.Derive.budget Solidity.Derive.synClose
    Solidity.Derive.budget []) H φ

/-- The same leaf quoted, for the tactic (`Derive.residueQuote`), the
contract named by `c`. -/
def leafQuote (c : Lean.Expr) (np : Option Nat) {Γ : Ctx} (H : Hyps C [] Γ) (φ : Fml C Γ) :
    Option (List (Lean.Expr × Lean.Expr)) :=
  leafWith false np (Solidity.Derive.residueQuote c []) H φ

/-- `leafQuote`, and which of `pick`'s residues closed the leaf: `.inr true`
when only the quantified one did, `.inr false` otherwise, then the quoted
leaves (`.inl`), as `pick` leaves them. -/
def leafQuoteI (c : Lean.Expr) (np : Option Nat) {Γ : Ctx} (H : Hyps C [] Γ) (φ : Fml C Γ) :
    Option (List ((Lean.Expr × Lean.Expr) ⊕ Bool)) :=
  match (H.wrap φ).closeErase [] with
  | some e =>
    let r := Solidity.Derive.residueQuote (C := C) c []
    match r (e.2.stripN np) with
    | some ([], _) => some [.inr false]
    | r₁ =>
      let rest : Option (List ((Lean.Expr × Lean.Expr) ⊕ Bool)) :=
        r₁.map fun q => .inr false :: q.1.map .inl
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
def fuel : Nat := Solidity.Derive.budget

/-- **`sol_prove`'s check**: the leaves of today's calculus the walk leaves,
none when every leaf closes; `np` the sequent's parameters (`pick`);
`full` only orders `pick`'s two residues (`pickH`).  A split's branch is
refuted as `pick` reads its leaf. -/
def residue (np : Option Nat) (full : Bool) {Γ : Ctx} (H : Hyps C [] Γ) (φ : Fml C Γ) :
    Option (List (Solidity.Derive.Leaf C)) :=
  (run (leafRes np full) (refutes (leafRes np false)) fuel H φ fuel).map (·.1)

/-- `#solkey_scan`'s view of `⊢ φ` (`Frontend/Problems.lean`): how many
leaves the walk leaves, closed by `synClose` or (`walk`) not, and the most
storage writes in one leaf's context (`Derive.storageWrites`); `none` when
the walk runs out or a step has no rule. -/
def scanLeaves (walk : Bool) (φ : Fml C []) : Option (Nat × Nat) :=
  let r := Solidity.Derive.residue Solidity.Derive.budget
    (if walk then fun _ _ => false else Solidity.Derive.synClose) Solidity.Derive.budget []
  (run (leafWith false none r) (refutes (leafRes none false)) fuel .nil φ fuel).map fun (ls, _) =>
    (ls.length, ls.foldl (fun m l => max m (Solidity.Derive.storageWrites l.1)) 0)

/-- `residue`, the leaves quoted, each walk leaf marked by the residue that
closed it (`leafQuoteI`). -/
def residueQuote (c : Lean.Expr) (np : Option Nat) {Γ : Ctx} (H : Hyps C [] Γ) (φ : Fml C Γ) :
    Option (List ((Lean.Expr × Lean.Expr) ⊕ Bool)) :=
  (run (leafQuoteI c np) (refutes (leafQuote c np)) fuel H φ fuel).map (·.1)

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
    (d : s.step (H.fresh (.modal m (.cons s ω) κ φ)) m = some p) {b : Nat} {ls : List α}
    {b' : Nat} (h : premise r x H m ω κ φ p b = some (ls, b')) (hl : ∀ l ∈ ls, P l) :
    Proves C R [] H (.modal m (.cons s ω) κ φ) := by
  cases p with
  | update U => exact .update d (hr _ _ _ _ _ h hl)
  | unfold P e => exact .unfold d (hr _ _ _ _ _ h hl)
  | bind x t P => exact .bind d (hr _ _ _ _ _ h hl)
  | split bk c c' P Q =>
    cases h1 : x H c
    · cases h2 : x H c'
      · simp only [premise, h1, h2, cond_false] at h
        have := both_sound h hl (hr _ _) (hr _ _)
        exact .split d this.1 this.2
      · simp only [premise, h1, h2, cond_false, cond_true] at h
        exact .split d (hr _ _ _ _ _ h hl) (.closeFalse (hx H c' h2))
    · simp only [premise, h1, cond_true] at h
      exact .split d (.closeFalse (hx H c h1)) (hr _ _ _ _ _ h hl)
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
    (ls : List α) (b' : Nat), run leaf rf n H φ b = some (ls, b') → (∀ l ∈ ls, P l) →
    Proves C R [] H φ
  | 0, _, _, _, _, _, _, h, _ => by simp only [run, reduceCtorEq] at h
  | _ + 1, _, _, _, 0, _, _, h, _ => by simp only [run, reduceCtorEq] at h
  | n + 1, _, H, φ, b + 1, ls, b', h, hl => by
    have ih : ∀ {Γ : Ctx} (H : Hyps C [] Γ) (φ : Fml C Γ) b ls b', run leaf rf n H φ b = some (ls, b') →
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
          | some p => premise (fun H φ b => run leaf rf n H φ b) rf H m ω κ ψ p b
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
theorem pick_valid {np : Option Nat} {e : Solidity.Fml C} {ls : List (Solidity.Derive.Leaf C)}
    (h : pick np (Solidity.Derive.residue Solidity.Derive.budget Solidity.Derive.synClose
      Solidity.Derive.budget []) e = some ls)
    (hl : ∀ l ∈ ls, Solidity.Proves .all l.1 l.2) : Solidity.Valid e := by
  have hv : ∀ {e' : Solidity.Fml C} {ls' : List (Solidity.Derive.Leaf C)} {b : Nat},
      Solidity.Derive.residue Solidity.Derive.budget Solidity.Derive.synClose
        Solidity.Derive.budget [] e' = some (ls', b) →
      (∀ l ∈ ls', Solidity.Proves .all l.1 l.2) → Solidity.Valid e' :=
    fun hr hl' => Solidity.Proves.valid (Solidity.Proves.of_synResidue hr hl')
  have hs : ∀ {r : Option (List (Solidity.Derive.Leaf C) × Nat)},
      Solidity.Derive.residue Solidity.Derive.budget Solidity.Derive.synClose
        Solidity.Derive.budget [] (e.stripN np) = r → r.map (·.1) = some ls →
      Solidity.Valid e := fun hr h => by
    obtain ⟨⟨ls', b'⟩, hr', he⟩ := Option.map_eq_some_iff.1 h
    cases he
    exact Solidity.Valid.of_stripN (hv (hr.trans hr') hl)
  unfold pick at h
  split at h
  · rename_i b h1
    exact Solidity.Valid.of_stripN (hv h1 Solidity.Derive.leaves_nil)
  · split at h
    · exact hs rfl h
    · split at h
      · rename_i b h2
        exact hv h2 Solidity.Derive.leaves_nil
      · exact hs rfl h
    · exact hs rfl h

/-- A leaf `leafRes` takes is proved once today's leaves are. -/
theorem leafRes_sound {R : RuleSet} (np : Option Nat) (full : Bool) {Γ : Ctx} (H : Hyps C [] Γ)
    (φ : Fml C Γ) (ls : List (Solidity.Derive.Leaf C)) (h : leafRes np full H φ = some ls)
    (hl : ∀ l ∈ ls, Solidity.Proves .all l.1 l.2) : Proves C R [] H φ := by
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

end Seq

/-- **`sol_prove`'s proof of a sequent**: the walk's residue, each of
today's leaves proved. -/
theorem Proves.of_residue {R : RuleSet} {np : Option Nat} {Γ : Ctx} {H : Hyps C [] Γ}
    {φ : Fml C Γ} {full : Bool} {ls : List (Solidity.Derive.Leaf C)}
    (h : Seq.residue np full H φ = some ls)
    (hl : ∀ l ∈ ls, Solidity.Proves .all l.1 l.2) : Proves C R [] H φ := by
  obtain ⟨⟨ls', b'⟩, hr, he⟩ := Option.map_eq_some_iff.1 h
  cases he
  exact Seq.run_sound (P := fun l => Solidity.Proves .all l.1 l.2)
    (fun H φ ls h hl => Seq.leafRes_sound np full H φ ls h hl)
    (Seq.refutes_sound (fun H φ ls h hl => Seq.leafRes_sound np false H φ ls h hl))
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

/-- `sol_prove` on the goal `g`, `Core.Proves C R [] H φ`: the goals it
leaves, one per leaf of today's residue. -/
def prove (g : MVarId) (C R Γ H φ : Expr) : MetaM (List MVarId) := do
  let some n := C.constName? | throwError "sol_prove: the contract is not a named constant"
  if H.hasFVar || H.hasMVar || φ.hasFVar || φ.hasMVar then
    throwError "sol_prove: the sequent mentions a local hypothesis or a metavariable"
  let φe ← Symex.evaluable φ
  let np := toExpr (← paramCount H φe)
  let hyp := mkApp (mkConst ``Solidity.Hyp) C
  let leafTy := mkApp2 (mkConst ``Prod [0, 0]) (mkApp (mkConst ``List [0]) hyp)
    (mkApp (mkConst ``Solidity.Fml) C)
  let resTy := mkApp (mkConst ``Option [0]) (mkApp (mkConst ``List [0]) leafTy)
  let mut full := false
  let lemmaFor (full : Bool) (ls : Expr) : MetaM Expr := do
    let someLs := mkApp2 (mkConst ``Option.some [0]) (mkApp (mkConst ``List [0]) leafTy) ls
    let type := mkApp3 (mkConst ``Eq [1]) resTy
      (mkAppN (mkConst ``residue) #[C, np, toExpr full, Γ, H, φ]) someLs
    Solidity.Derive.kernelLemma type (mkApp2 (mkConst ``Eq.refl [1]) resTy someLs)
  let assignWith (full : Bool) (ls h : Expr) (hl : Expr) : MetaM Unit :=
    g.assign (mkAppN (mkConst ``Proves.of_residue) #[C, R, np, Γ, H, φ, toExpr full, ls, h, hl])
  let nil := mkApp (mkConst ``List.nil [0]) leafTy
  -- the compiled walk first, then one kernel check of its leaves, as
  -- today's `sol_prove` (`Derive.prove`): a kernel try at no leaves costs a
  -- second evaluation where the closer leaves some, in the declaration's
  -- heartbeats
  let qTy := mkApp (mkConst ``Option [0]) (mkApp (mkConst ``List [0])
    (mkApp2 (mkConst ``Sum [0, 0])
      (mkApp2 (mkConst ``Prod [0, 0]) (mkConst ``Expr) (mkConst ``Expr)) (mkConst ``Bool)))
  let some marked ← unsafe evalExpr (Option (List ((Expr × Expr) ⊕ Bool))) qTy
      (mkAppN (mkConst ``residueQuote) #[C, quoteConstName n, np, Γ, H, φe])
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
    assignWith full nil h (mkApp (mkConst ``Solidity.Derive.leaves_nil) C)
    return []
  let mkLeaf (Γ' φ' : Expr) : Expr :=
    mkAppN (mkConst ``Prod.mk [0, 0]) #[mkApp (mkConst ``List [0]) hyp,
      mkApp (mkConst ``Solidity.Fml) C, Γ', φ']
  let ls ← mkListLit leafTy (leaves.map fun (Γ', φ') => mkLeaf Γ' φ')
  let h ← try lemmaFor full ls
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
  assignWith full ls h hl
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
