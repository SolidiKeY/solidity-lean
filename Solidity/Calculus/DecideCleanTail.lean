import Solidity.Calculus.DecideTyped
import Solidity.Calculus.MemRead
import Solidity.Calculus.TailMode

/-!
# The closer under clean tails (`docs/options.md`, O6)

A leaf proved under `ValidTail .clean` has the premise
`cleanTail(storage) = true` (`Fml.cleanTail`, `Calculus/TailMode.lean`) in
its antecedent, read at the starting storage.  The reduction leaves the
starting storage's reads as atoms (`LTm.obsW`, `obsL`), and a read past an
array's live end reads the shadow slot as it is (`Storage.obs`).  Under the
premise the starting storage shows clean tails (`TSto.CleanTails`): a read
that enters a dynamic array at an index at or past its live length, and
goes on along no mapping key, reads the default word and the length `0`.

**The clause** (Lean only: solkey has no shadow slots).  `LTm.ctGuards`
collects, along a path, `i < obsL(q)` for each unchecked index step
`q[i]` into a dynamic array with no mapping key step after it (a member and
a checked index pass, a key step stops the fold); `LTm.ctFold` rewrites each
atom `obsW(p)` to `p; (c₁ ? … (cₙ ? obsW(p) : 0) … : 0)` over them, each
test a key comparison `cᵢ = true` the closer splits on (`LTm.pick`), and
`obsL(p)` the same with `0` (`guardWith`), leaving the atom alone where
there is no guard.  It keeps what a term reads under the premise
(`LTm.ctFold_eval`).

**Where.**  `Seq.checkCore` (`Calculus/DecideComplete.lean`), which
`sol_decide` and `sol_prove`'s leaves run, folds the eliminated reduction so
(`LFml.decideMemCT`) where the leaf assumes the premise
(`Fml.assumesCT`: a premise of its spine of implications, conjunctions
and quantifiers); a state without clean tails makes such a leaf true
(`Fml.assumesCT_holds`).  Without the premise nothing changes.

The functions the kernel evaluates on the reduction are written with the
recursors (Gate G0), each with a `match` twin and a link theorem.
-/

namespace Solidity

namespace Decide

open Semantics

variable {C : Contract}

/-! ## The premise -/

/-- `cleanTail(storage)`. -/
abbrev _root_.Solidity.Tm.cleanTailSt {Γ : Ctx} : Tm C Γ (.val .bool) :=
  .app1 .cleanTail (.app0 .storage)

/-- `Fml.isCTPrem`'s compiled twin. -/
def _root_.Solidity.Fml.isCTPremM {Γ : Ctx} : Fml C Γ → Bool
  | .eq a b => a.beqR (Tm.cleanTailSt (C := C) (Γ := Γ)) &&
      b.beqR (Tm.app0 (.lit (p := .bool) true) : Tm C Γ (.val .bool))
  | .and φ ψ => φ.isCTPremM || ψ.isCTPremM
  | _ => false

/-- The formula is the premise `cleanTail(storage) = true`, or a
conjunction with it.  By the recursor (Gate G0): `Seq.checkCore` runs it in
the kernel. -/
@[implemented_by Fml.isCTPremM]
def _root_.Solidity.Fml.isCTPrem : {Γ : Ctx} → Fml C Γ → Bool
  | _, φ => Fml.casesOn (motive := fun _ _ => Bool) φ
    (tt := false)
    (eq := fun {Γ'} {_} a b => a.beqR (Tm.cleanTailSt (C := C) (Γ := Γ')) &&
      b.beqR (Tm.app0 (.lit (p := .bool) true) : Tm C Γ' (.val .bool)))
    (wellFormed := fun _ => false) (not := fun _ => false)
    (and := fun φ ψ => Fml.isCTPrem φ || Fml.isCTPrem ψ)
    (imp := fun _ _ => false) (upd := fun _ _ _ => false)
    (modal := fun _ _ _ _ => false) (havoc := fun _ => false)
    (all := fun _ _ _ => false) (bind := fun _ _ _ _ => false)
    (anon := fun _ _ => false) (allocAll := fun _ _ _ => false)
  termination_by structural _ φ => φ

theorem _root_.Solidity.Fml.isCTPrem_eq_isCTPremM {Γ : Ctx} (φ : Fml C Γ) :
    φ.isCTPrem = φ.isCTPremM := by
  induction φ with
  | and φ ψ ihφ ihψ => rw [Fml.isCTPremM, ← ihφ, ← ihψ]; rfl
  | _ => rfl

/-- `Fml.assumesCT`'s compiled twin. -/
def _root_.Solidity.Fml.assumesCTM {Γ : Ctx} : Fml C Γ → Bool
  | .imp φ ψ => φ.isCTPremM || ψ.assumesCTM
  | .and φ ψ => φ.assumesCTM && ψ.assumesCTM
  | .all _ _ φ => φ.assumesCTM
  | _ => false

/-- **The leaf assumes clean tails**: the premise is a premise of its spine
of implications (each of a conjunction's sides, under a quantifier).  By
the recursor (Gate G0). -/
@[implemented_by Fml.assumesCTM]
def _root_.Solidity.Fml.assumesCT : {Γ : Ctx} → Fml C Γ → Bool
  | _, φ => Fml.casesOn (motive := fun _ _ => Bool) φ
    (tt := false) (eq := fun _ _ => false)
    (wellFormed := fun _ => false) (not := fun _ => false)
    (and := fun φ ψ => Fml.assumesCT φ && Fml.assumesCT ψ)
    (imp := fun φ ψ => Fml.isCTPrem φ || Fml.assumesCT ψ) (upd := fun _ _ _ => false)
    (modal := fun _ _ _ _ => false) (havoc := fun _ => false)
    (all := fun _ _ φ => Fml.assumesCT φ) (bind := fun _ _ _ _ => false)
    (anon := fun _ _ => false) (allocAll := fun _ _ _ => false)
  termination_by structural _ φ => φ

theorem _root_.Solidity.Fml.assumesCT_eq_assumesCTM {Γ : Ctx} (φ : Fml C Γ) :
    φ.assumesCT = φ.assumesCTM := by
  induction φ with
  | imp φ ψ _ ihψ => rw [Fml.assumesCTM, ← Fml.isCTPrem_eq_isCTPremM φ, ← ihψ]; rfl
  | and φ ψ ihφ ihψ => rw [Fml.assumesCTM, ← ihφ, ← ihψ]; rfl
  | all x p φ ih => rw [Fml.assumesCTM, ← ih]; rfl
  | _ => rfl

theorem _root_.Solidity.Fml.isCTPrem_holds {Γ : Ctx} (φ : Fml C Γ) :
    φ.isCTPrem = true → ∀ σ : State C Γ, holds σ φ → TSto.CleanTails σ.storage.obs := by
  rw [Fml.isCTPrem_eq_isCTPremM]
  induction φ with
  | eq a b =>
    intro h σ hφ
    simp only [Fml.isCTPremM, Bool.and_eq_true] at h
    have ea := Tm.sigma_eq_of_beqR h.1
    have eb := Tm.sigma_eq_of_beqR h.2
    cases ea
    cases eb
    exact holds_cleanTail.1 hφ
  | and φ ψ ihφ ihψ =>
    intro h σ hφ
    simp only [Fml.isCTPremM, Bool.or_eq_true] at h
    rcases h with h | h
    · exact ihφ h σ hφ.1
    · exact ihψ h σ hφ.2
  | _ => intro h; simp only [Fml.isCTPremM, Bool.false_eq_true] at h

/-- **Vacuity**: a leaf that assumes clean tails holds where they are not. -/
theorem _root_.Solidity.Fml.assumesCT_holds {Γ : Ctx} (φ : Fml C Γ) :
    φ.assumesCT = true → ∀ σ : State C Γ, ¬ TSto.CleanTails σ.storage.obs → holds σ φ := by
  rw [Fml.assumesCT_eq_assumesCTM]
  induction φ with
  | imp φ ψ _ ihψ =>
    intro h σ hn hφ
    simp only [Fml.assumesCTM, Bool.or_eq_true] at h
    rcases h with h | h
    · exact absurd (Fml.isCTPrem_holds φ ((Fml.isCTPrem_eq_isCTPremM φ).trans h) σ hφ) hn
    · exact ihψ h σ hn
  | and φ ψ ihφ ihψ =>
    intro h σ hn
    simp only [Fml.assumesCTM, Bool.and_eq_true] at h
    exact ⟨ihφ h.1 σ hn, ihψ h.2 σ hn⟩
  | all x p φ ih =>
    intro h σ hn v
    exact ih h _ hn
  | _ => intro h; simp only [Fml.assumesCTM, Bool.false_eq_true] at h

/-! ## The guards of a path -/

/-- The binary symbol is an operator. -/
def _root_.Solidity.Op2.isBinop {a b s : Srt} (o : Op2 C a b s) : Bool :=
  Op2.casesOn (motive := fun _ _ _ _ => Bool) o
    (binop := fun _ {_} _ => true) (find := false) (len := false) (read := false)
    (mlen := false) («at» := fun _ => false)
    (nextIn := false) (delAt := false) (pushSlot := false) (pop := false)
    (shrink := false) (extend := false) (sfind := false)
    (copyMem := false) (iread := false) (copy := fun _ => false)
    (mat := fun _ => false) (copySt := fun _ => false) (findIn := false)
    (delAtIn := false) (sfindIn := false) (zbin := fun _ _ => false)
    (zcmp := fun _ _ => false) (keccak := false)

/-- `LTm.dropSeq`'s compiled twin. -/
def LTm.dropSeqM : {s : Srt} → LTm C s → LTm C s
  | _, .app2 o x y => bif o.isBinop then .app2 o x.dropSeqM y.dropSeqM else .app2 o x y
  | _, .seq _ a => a.dropSeqM
  | _, t => t

/-- A term with its guards dropped, through operators: where the term
returns, it returns the same (`LTm.dropSeq_eval`).  By the recursor. -/
@[implemented_by LTm.dropSeqM]
def LTm.dropSeq {s : Srt} (t : LTm C s) : LTm C s :=
  @LTm.rec C (fun s _ => LTm C s)
    (@fun _ k => .var k) (@fun _ o => .app0 o)
    (@fun _ _ o x _ => .app1 o x)
    (@fun _ _ _ o x y ihx ihy => bif o.isBinop then .app2 o ihx ihy else .app2 o x y)
    (@fun _ _ _ _ o x y z _ _ _ => .app3 o x y z)
    (@fun _ _ _ it q i _ _ => .index it q i)
    (@fun _ q _ => .obsW q) (@fun _ q _ => .obsL q) (@fun _ q _ => .obsH q)
    (@fun _ _ _ _ _ iha => iha)
    (@fun _ a b _ _ => .orElse a b)
    (@fun _ _ a b t e _ _ _ _ => .kite a b t e)
    (@fun _ => .err) s t

theorem LTm.dropSeq_eq_dropSeqM {s : Srt} (t : LTm C s) : t.dropSeq = t.dropSeqM := by
  induction t with
  | app2 o x y ihx ihy => rw [LTm.dropSeqM, ← ihx, ← ihy]; rfl
  | seq d a _ iha => rw [LTm.dropSeqM, ← iha]; rfl
  | _ => rfl

/-- The index reads the live length of `q` wherever it returns: `obsL(q)`,
or `obsL(q) + 1 - 1` (a `push` then `length - 1`), its guards dropped. -/
def lenOf {E : Ty} (q : LTm C (.path (.ref (.array E)))) (i : LTm C (.val .uint)) : Bool :=
  i.dropSeq.beqR (LTm.obsL q) ||
    i.dropSeq.beqR (LTm.app2 (.binop .sub rfl) (LTm.app2 (.binop .add rfl) (LTm.obsL q) (LTm.nat 1))
      (LTm.nat 1) : LTm C (.val .uint))

/-- `i < obsL(q)`: the index `i` within the live elements of `q`; `false`
where `i` reads the live length (`lenOf`). -/
def ltLen {E : Ty} (q : LTm C (.path (.ref (.array E)))) (i : LTm C (.val .uint)) :
    LTm C (.val .bool) :=
  bif lenOf q i then .lit (p := .bool) false else .app2 (.binop .lt rfl) i (.obsL q)

/-- An unchecked index step's guards: a dynamic array's adds `i < obsL(q)`,
a fixed array's passes, a mapping's stops the fold. -/
def indexGuards {R : RefTy} {k : PrimTy} {V : Ty} (it : IndexTy R k V) :
    LTm C (.path (.ref R)) → LTm C (.val k) → List (LTm C (.val .bool)) →
      List (LTm C (.val .bool)) :=
  @IndexTy.casesOn (fun R k _ _ => LTm C (.path (.ref R)) → LTm C (.val k) →
      List (LTm C (.val .bool)) → List (LTm C (.val .bool))) R k V it
    (fun {_} {_} _ _ _ => [])
    (fun {_} {_} a => @ArrTy.casesOn (fun R _ _ => LTm C (.path (.ref R)) → LTm C (.val .uint) →
        List (LTm C (.val .bool)) → List (LTm C (.val .bool))) _ _ a
      (fun {_} q i l => ltLen q i :: l)
      (fun {_} {_} _ _ l => l))

/-- A checked index step into an array: it passes the guards (a mapping's
stops them). -/
def _root_.Solidity.Op2.ctPass {a b s : Srt} (o : Op2 C a b s) : Bool :=
  Op2.casesOn (motive := fun _ _ _ _ => Bool) o
    (binop := fun _ {_} _ => false) (find := false) (len := false) (read := false)
    (mlen := false)
    («at» := fun it => @IndexTy.casesOn (fun _ _ _ _ => Bool) _ _ _ it false (fun _ => true))
    (nextIn := false) (delAt := false) (pushSlot := false) (pop := false)
    (shrink := false) (extend := false) (sfind := false)
    (copyMem := false) (iread := false) (copy := fun _ => false)
    (mat := fun _ => false) (copySt := fun _ => false) (findIn := false)
    (delAtIn := false) (sfindIn := false) (zbin := fun _ _ => false)
    (zcmp := fun _ _ => false) (keccak := false)

/-- `LTm.ctGuards`' compiled twin. -/
def LTm.ctGuardsM : {s : Srt} → LTm C s → List (LTm C (.val .bool))
  | _, .app1 o x => bif o.retsStep then x.ctGuardsM else []
  | _, .app2 o x _ => bif o.ctPass then x.ctGuardsM else []
  | _, .index it q i => indexGuards it q i q.ctGuardsM
  | _, _ => []

/-- **The guards of a path**: each `i < obsL(q)` of an unchecked index step
into a dynamic array, along members and array steps, with no mapping key
step after it.  Where one is `false`, the path reads past a live end
(`LTm.ctGuards_ok`).  By the recursor. -/
@[implemented_by LTm.ctGuardsM]
def LTm.ctGuards {s : Srt} (t : LTm C s) : List (LTm C (.val .bool)) :=
  @LTm.rec C (fun _ _ => List (LTm C (.val .bool)))
    (@fun _ _ => []) (@fun _ _ => [])
    (@fun _ _ o _ ihx => bif o.retsStep then ihx else [])
    (@fun _ _ _ o _ _ ihx _ => bif o.ctPass then ihx else [])
    (@fun _ _ _ _ _ _ _ _ _ _ _ => [])
    (@fun _ _ _ it q i ihq _ => indexGuards it q i ihq)
    (@fun _ _ _ => []) (@fun _ _ _ => []) (@fun _ _ _ => [])
    (@fun _ _ _ _ _ _ => []) (@fun _ _ _ _ _ => [])
    (@fun _ _ _ _ _ _ _ _ _ _ => []) (@fun _ => []) s t

theorem LTm.ctGuards_eq_ctGuardsM {s : Srt} (t : LTm C s) : t.ctGuards = t.ctGuardsM := by
  induction t with
  | app1 o x ihx => rw [LTm.ctGuardsM, ← ihx]; rfl
  | app2 o x y ihx => rw [LTm.ctGuardsM, ← ihx]; rfl
  | index it q i ihq => rw [LTm.ctGuardsM, ← ihq]; rfl
  | _ => rfl

/-! ## The fold -/

/-- The tests known on the way to a subterm: each the test of an `ite`
whose branch it is in, and its value there. -/
abbrev CTKnown (C : Contract) : Type := List (LTm C (.val .bool) × Bool)

/-- The test `c` is known to read `b`. -/
def knownAs (K : CTKnown C) (c : LTm C (.val .bool)) (b : Bool) : Bool :=
  K.any fun e => e.1.beqR c && e.2 == b

/-- `a`, guarded: `q; (c₁ ? … (cₙ ? a : d) … : d)`; `q; d` where a guard is
`false` or known to be; a guard known `true` dropped; `a` with no guard left. -/
def guardWith {T : Ty} {p : PrimTy} (K : CTKnown C) (cs : List (LTm C (.val .bool)))
    (q : LTm C (.path T)) (a d : LTm C (.val p)) : LTm C (.val p) :=
  let cs' := cs.filter fun c => !knownAs K c true
  bif cs'.isEmpty then a
  else bif cs'.any (fun c => c.isFF || knownAs K c false) then .seq q d
  else .seq q (cs'.foldr (fun c acc => .kite c (.lit (p := .bool) true) acc d) a)

/-- The test of an `ite`, at any sort of its first operand. -/
def _root_.Solidity.Op3.iteTest {a b c s : Srt} (o : Op3 C a b c s) :
    LTm C a → Option (LTm C (.val .bool)) :=
  Op3.casesOn (motive := fun a _ _ _ _ => LTm C a → Option (LTm C (.val .bool))) o
    (fun x => some x) (fun _ => none) (fun _ => none) (fun _ _ => none) (fun _ => none)
    (fun _ => none) (fun _ _ => none)

/-- The known tests below an operand of an `ite`: its test, `true` in the
first branch, `false` in the second. -/
def CTKnown.branch (K : CTKnown C) (t : Option (LTm C (.val .bool))) (b : Bool) : CTKnown C :=
  match t with
  | some c => (c, b) :: K
  | none => K

/-- `LTm.ctFoldK`'s compiled twin. -/
def LTm.ctFoldKM : {s : Srt} → LTm C s → CTKnown C → LTm C s
  | _, .var k, _ => .var k
  | _, .app0 o, _ => .app0 o
  | _, .app1 o x, K => .app1 o (x.ctFoldKM K)
  | _, .app2 o x y, K => .app2 o (x.ctFoldKM K) (y.ctFoldKM K)
  | _, .app3 o x y z, K => .app3 o (x.ctFoldKM K) (y.ctFoldKM (K.branch (o.iteTest x) true))
      (z.ctFoldKM (K.branch (o.iteTest x) false))
  | _, .index it q i, K => .index it (q.ctFoldKM K) (i.ctFoldKM K)
  | _, .obsW q, K => guardWith K q.ctGuardsM q (.obsW q) (.lit (PrimTy.dflt _))
  | _, .obsL q, K => guardWith K q.ctGuardsM q (.obsL q) (LTm.nat 0)
  | _, .obsH q, _ => .obsH q
  | _, .seq d a, K => .seq (d.ctFoldKM K) (a.ctFoldKM K)
  | _, .orElse a b, K => .orElse (a.ctFoldKM K) (b.ctFoldKM K)
  | _, .kite a b t e, K => .kite (a.ctFoldKM K) (b.ctFoldKM K) (t.ctFoldKM K) (e.ctFoldKM K)
  | _, .err, _ => .err

/-- **The clause**, under the tests `K` known on the way: every observation
of the starting storage past a live end read as the default (`guardWith`),
a guard an enclosing `ite` decides dropped.  By the recursor. -/
@[implemented_by LTm.ctFoldKM]
def LTm.ctFoldK {s : Srt} (t : LTm C s) : CTKnown C → LTm C s :=
  @LTm.rec C (fun s _ => CTKnown C → LTm C s)
    (@fun _ k _ => .var k) (@fun _ o _ => .app0 o)
    (@fun _ _ o _ ihx K => .app1 o (ihx K))
    (@fun _ _ _ o _ _ ihx ihy K => .app2 o (ihx K) (ihy K))
    (@fun _ _ _ _ o x _ _ ihx ihy ihz K => .app3 o (ihx K) (ihy (K.branch (o.iteTest x) true))
      (ihz (K.branch (o.iteTest x) false)))
    (@fun _ _ _ it _ _ ihq ihi K => .index it (ihq K) (ihi K))
    (@fun _ q _ K => guardWith K q.ctGuards q (.obsW q) (.lit (PrimTy.dflt _)))
    (@fun _ q _ K => guardWith K q.ctGuards q (.obsL q) (LTm.nat 0))
    (@fun _ q _ _ => .obsH q)
    (@fun _ _ _ _ ihd iha K => .seq (ihd K) (iha K))
    (@fun _ _ _ iha ihb K => .orElse (iha K) (ihb K))
    (@fun _ _ _ _ _ _ iha ihb iht ihe K => .kite (iha K) (ihb K) (iht K) (ihe K))
    (@fun _ _ => .err) s t

theorem LTm.ctFoldK_eq_ctFoldKM {s : Srt} (t : LTm C s) (K : CTKnown C) :
    t.ctFoldK K = t.ctFoldKM K := by
  induction t generalizing K with
  | var | app0 | obsH | err => rfl
  | app1 o x ihx => rw [LTm.ctFoldKM, ← ihx]; rfl
  | app2 o x y ihx ihy => rw [LTm.ctFoldKM, ← ihx, ← ihy]; rfl
  | app3 o x y z ihx ihy ihz => rw [LTm.ctFoldKM, ← ihx, ← ihy, ← ihz]; rfl
  | index it q i ihq ihi => rw [LTm.ctFoldKM, ← ihq, ← ihi]; rfl
  | obsW q => rw [LTm.ctFoldKM, ← LTm.ctGuards_eq_ctGuardsM]; rfl
  | obsL q => rw [LTm.ctFoldKM, ← LTm.ctGuards_eq_ctGuardsM]; rfl
  | seq d a ihd iha => rw [LTm.ctFoldKM, ← ihd, ← iha]; rfl
  | orElse a b iha ihb => rw [LTm.ctFoldKM, ← iha, ← ihb]; rfl
  | kite a b t e iha ihb iht ihe => rw [LTm.ctFoldKM, ← iha, ← ihb, ← iht, ← ihe]; rfl

/-- **The clause** on a term, with nothing known. -/
abbrev LTm.ctFold {s : Srt} (t : LTm C s) : LTm C s := t.ctFoldK []

/-- `LFml.ctFold`'s compiled twin. -/
def LFml.ctFoldM : LFml C → LFml C
  | .tt => .tt
  | .eq a b => .eq a.ctFold b.ctFold
  | .not φ => .not φ.ctFoldM
  | .and φ ψ => .and φ.ctFoldM ψ.ctFoldM
  | .imp φ ψ => .imp φ.ctFoldM ψ.ctFoldM
  | .all k p φ => .all k p φ.ctFoldM

/-- The clause on every term of a formula.  By the recursor. -/
@[implemented_by LFml.ctFoldM]
def LFml.ctFold (φ : LFml C) : LFml C :=
  @LFml.rec C (fun _ => LFml C) .tt (fun a b => .eq a.ctFold b.ctFold)
    (fun _ ih => .not ih) (fun _ _ ihφ ihψ => .and ihφ ihψ) (fun _ _ ihφ ihψ => .imp ihφ ihψ)
    (fun k p _ ih => .all k p ih) φ

theorem LFml.ctFold_eq_ctFoldM (φ : LFml C) : φ.ctFold = φ.ctFoldM := by
  induction φ with
  | tt | eq => rfl
  | not φ ih | all k p φ ih => simp only [LFml.ctFoldM, ← ih]; rfl
  | and φ ψ ihφ ihψ | imp φ ψ ihφ ihψ => simp only [LFml.ctFoldM, ← ihφ, ← ihψ]; rfl

/-! ## Soundness -/

section Sound

variable {g : State C []} {ν : AEnv}

/-- What a path's guards promise: where the path returns `r`, each guard
returns, and where one is `false`, `r` reads past a live end. -/
def GuardsOK (g : State C []) (ν : AEnv) : (s : Srt) → LTm C s → List (LTm C (.val .bool)) → Prop
  | .path T, q, cs => ∀ r : SRef C T, (q.eval g ν : Option (SRef C T)) = some r →
      ∀ c ∈ cs, ∃ b, (c.eval g ν : Option Bool) = some b ∧ (b = false → r.Shadowed g.storage.obs)
  | _, _, _ => True

theorem GuardsOK.nil : (s : Srt) → (t : LTm C s) → GuardsOK g ν s t []
  | .path _, _ => fun _ _ _ h => nomatch h
  | .val _, _ | .st, _ | .sv _, _ | .ident _, _ | .addr _, _ | .mem, _ | .mv _, _ | .sts _, _
  | .spath _ _, _ | .kint, _ => trivial

/-- A guard that passes on along path steps with no mapping key. -/
theorem GuardsOK.step {T U : Ty} {q : LTm C (.path T)} {cs : List (LTm C (.val .bool))}
    (h : GuardsOK g ν _ q cs) (q' : LTm C (.path U))
    (hq' : ∀ r', (q'.eval g ν : Option (SRef C U)) = some r' →
      ∃ (r : SRef C T) (st : Path T U), st.KeyFree ∧ (q.eval g ν : Option (SRef C T)) = some r ∧
        r' = r.append st) :
    GuardsOK g ν _ q' cs := by
  intro r' hr' c hc
  obtain ⟨r, st, hst, hr, rfl⟩ := hq' r' hr'
  obtain ⟨b, hb, hsh⟩ := h r hr c hc
  exact ⟨b, hb, fun hf => (hsh hf).append st hst⟩

theorem Path.keyFree_index_arr {R : RefTy} {E : Ty} (a : ArrTy R E) (i : PrimTy.uint.Denote) :
    (Path.index (.arr a) i).KeyFree := by
  cases a
  · rw [Path.index_dyn]; trivial
  · rw [Path.index_fixed]; trivial

/-- The live length the observations show is a `uint`. -/
theorem Storage.obs_len_lt {st : Storage C} {E : Ty} (r : SRef C (.ref (.array E))) :
    st.obs.len (.ref r) < 2 ^ 256 := by
  show SVal.lenOf ((st.get r.hroot).findM r.path) < 2 ^ 256
  cases (st.get r.hroot).findM r.path with
  | none => show 0 < 2 ^ 256; decide
  | some w =>
    cases w with
    | array e sh hn => exact hn


theorem LTm.dropSeq_eval {s : Srt} (t : LTm C s) :
    ∀ {k : s.Den C g.H}, t.eval g ν = some k → t.dropSeq.eval g ν = some k := by
  induction t with
  | app2 o x y ihx ihy =>
    cases o
    case binop op p h =>
      intro k hk
      show (LTm.app2 (.binop op h) x.dropSeq y.dropSeq).eval g ν = some k
      rw [LTm.eval_app2, Op2.eval_eq_evalM] at hk ⊢
      simp only [Op2.evalM] at hk ⊢
      cases hx : (x.eval g ν : Option p.Denote) with
      | none => rw [hx] at hk; cases hk
      | some a =>
        rw [hx, Option.bind_some] at hk
        rw [ihx hx, Option.bind_some]
        cases hy : (y.eval g ν : Option p.Denote) with
        | none =>
          rw [hy] at hk
          unfold binopT at hk ⊢
          cases hs : op.shortT a with
          | some r => rw [hs] at hk; exact hk
          | none => rw [hs] at hk; cases hk
        | some b => rw [hy] at hk; rw [ihy hy]; exact hk
    all_goals exact id
  | seq d a _ iha =>
    intro k hk
    rw [LTm.eval_seq, Option.bind_eq_some_iff] at hk
    obtain ⟨_, _, hk⟩ := hk
    exact iha hk
  | _ => exact id

theorem lenOf_eval {E : Ty} {q : LTm C (.path (.ref (.array E)))} {i : LTm C (.val .uint)}
    (h : lenOf q i = true) {k : PrimTy.uint.Denote} (hk : (i.eval g ν : Option _) = some k) :
    ((LTm.obsL q).eval g ν : Option PrimTy.uint.Denote) = some k := by
  have hj := i.dropSeq_eval hk
  simp only [lenOf, Bool.or_eq_true] at h
  rcases h with h | h
  · rw [LTm.eq_of_beqR h] at hj; exact hj
  · rw [LTm.eq_of_beqR h] at hj
    cases hL : ((LTm.obsL q).eval g ν : Option PrimTy.uint.Denote) with
    | none =>
      rw [LTm.eval_app2, LTm.eval_app2, hL, Op2.eval_eq_evalM, Op2.eval_eq_evalM] at hj
      simp only [Op2.evalM, Option.bind_none] at hj
      cases hj
    | some x =>
      rw [LTm.eval_app2, LTm.eval_app2, hL, Op2.eval_eq_evalM, Op2.eval_eq_evalM] at hj
      simp only [Op2.evalM, Option.bind_some, binopT, BinOp.shortT] at hj
      have h1 : (LTm.eval g ν (LTm.nat 1) : Option PrimTy.uint.Denote) = some (uintOfNat 1) := rfl
      have h1v : (uintOfNat 1).1 = 1 := uintOfNat_val (by decide)
      rw [h1, Option.bind_some] at hj
      simp only [BinOp.evalT, BinOp.evalNum, BinOp.arithInt, h1v, Option.bind_some,
        PrimTy.ofInt?] at hj
      split at hj
      · simp only [Option.bind_some] at hj
        split at hj
        · cases hj
          exact congrArg some (Subtype.ext (by simp only [Int.add_sub_cancel]))
        · cases hj
      · cases hj

/-- **The guards keep their promise.** -/
theorem LTm.ctGuards_ok {s : Srt} (t : LTm C s) : GuardsOK g ν s t t.ctGuards := by
  induction t with
  | app1 o x ihx =>
    cases o
    case field s f T h =>
      refine GuardsOK.step ihx _ fun r' hr' => ?_
      rw [LTm.eval_app1] at hr'
      cases hx : (x.eval g ν : Option (SRef C (.ref (.struct s)))) with
      | none => rw [hx] at hr'; cases hr'
      | some r =>
        rw [hx] at hr'
        exact ⟨r, .field h .nil, trivial, rfl, (Option.some.inj hr').symm⟩
    all_goals exact GuardsOK.nil _ _
  | app2 o x y ihx ihy =>
    cases o
    case «at» R k V it =>
      cases it
      case map => exact GuardsOK.nil _ _
      case arr a =>
        refine GuardsOK.step ihx _ fun r' hr' => ?_
        rw [LTm.eval_app2, Op2.eval_eq_evalM] at hr'
        simp only [Op2.evalM, Storage.atT, Option.bind_eq_bind, Option.bind_eq_some_iff] at hr'
        obtain ⟨r, hr, k, hk, u, hu, h⟩ := hr'
        exact ⟨r, _, Path.keyFree_index_arr a k, hr, (Option.some.inj h).symm⟩
    all_goals exact GuardsOK.nil _ _
  | index it q i ihq ihi =>
    cases it
    case map => exact (GuardsOK.nil _ _ : GuardsOK g ν _ _ [])
    case arr a =>
      have hstep : ∀ r', ((LTm.index (.arr a) q i).eval g ν : Option (SRef C _)) = some r' →
          ∃ (r : SRef C _) (k : PrimTy.uint.Denote), (q.eval g ν : Option (SRef C _)) = some r ∧
            (i.eval g ν : Option PrimTy.uint.Denote) = some k ∧ r' = r.index (.arr a) k := by
        intro r' hr'
        rw [LTm.eval_index] at hr'
        simp only [Option.bind_eq_some_iff] at hr'
        obtain ⟨r, hr, k, hk, h⟩ := hr'
        exact ⟨r, k, hr, hk, (Option.some.inj h).symm⟩
      have htail : GuardsOK g ν _ (LTm.index (.arr a) q i) q.ctGuards :=
        GuardsOK.step ihq _ fun r' hr' => by
          obtain ⟨r, k, hr, -, rfl⟩ := hstep r' hr'
          exact ⟨r, _, Path.keyFree_index_arr a k, hr, rfl⟩
      cases a
      case fixed => exact htail
      case dyn =>
        intro r' hr' c hc
        rcases List.mem_cons.1 hc with rfl | hc
        · obtain ⟨r, k, hr, hk, rfl⟩ := hstep r' hr'
          have hlt := Storage.obs_len_lt (st := g.storage) r
          unfold ltLen
          cases hlen : lenOf q i
          · rw [cond_false]
            refine ⟨decide (k.1 < (uintOfNat (g.storage.obs.len (.ref r))).1), ?_, fun hb => ?_⟩
            · show Op2.eval g (.binop .lt rfl) (i.eval g ν) ((LTm.obsL q).eval g ν) = _
              rw [hk, LTm.eval_obsL, hr]
              rfl
            · apply SRef.shadowed_index
              rw [uintOfNat_val hlt] at hb
              have hb' := of_decide_eq_false hb
              omega
          · rw [cond_true]
            refine ⟨false, rfl, fun _ => SRef.shadowed_index _ _ ?_⟩
            have hL := lenOf_eval hlen hk
            rw [LTm.eval_obsL, hr, Option.bind_some, Option.some.injEq] at hL
            rw [← hL, uintOfNat_val hlt]
            omega
        · exact htail r' hr' c hc
  | _ => exact GuardsOK.nil _ _

/-- A test known to read `b` reads `b`. -/
theorem knownAs_eval {K : CTKnown C} (hK : ∀ e ∈ K, (e.1.eval g ν : Option Bool) = some e.2)
    {c : LTm C (.val .bool)} {b : Bool} (h : knownAs K c b = true) :
    (c.eval g ν : Option Bool) = some b := by
  obtain ⟨e, he, h⟩ := List.any_eq_true.1 h
  rw [Bool.and_eq_true, beq_iff_eq] at h
  rw [← LTm.eq_of_beqR h.1, ← h.2]
  exact hK e he

/-- A guarded term reads what the term does: where the path halts the term
does, and a guard that is `false` makes it read the default. -/
theorem guardWith_eval {T : Ty} {p : PrimTy} (K : CTKnown C)
    (hK : ∀ e ∈ K, (e.1.eval g ν : Option Bool) = some e.2) (cs : List (LTm C (.val .bool)))
    (q : LTm C (.path T)) (a d : LTm C (.val p))
    (hnone : (q.eval g ν : Option (SRef C T)) = none → (a.eval g ν : Option p.Denote) = none)
    (hc : ∀ r : SRef C T, (q.eval g ν : Option (SRef C T)) = some r → ∀ c ∈ cs,
      ∃ b, (c.eval g ν : Option Bool) = some b ∧
        (b = false → (a.eval g ν : Option p.Denote) = d.eval g ν)) :
    ((guardWith K cs q a d).eval g ν : Option p.Denote) = a.eval g ν := by
  have key : ∀ cs' : List (LTm C (.val .bool)), (∀ c ∈ cs', ∃ b, (c.eval g ν : Option Bool) = some b ∧
      (b = false → (a.eval g ν : Option p.Denote) = d.eval g ν)) →
      ((cs'.foldr (fun c acc => .kite c (.lit (p := .bool) true) acc d) a).eval g ν :
        Option p.Denote) = a.eval g ν := by
    intro cs'
    induction cs' with
    | nil => intro _; rfl
    | cons c cs' ih =>
      intro h
      obtain ⟨b, hb, hf⟩ := h c List.mem_cons_self
      rw [List.foldr_cons, LTm.eval_kite, hb]
      cases b
      · exact (hf rfl).symm
      · exact ih fun c' h' => h c' (List.mem_cons_of_mem _ h')
  have hc' : ∀ r : SRef C T, (q.eval g ν : Option (SRef C T)) = some r →
      ∀ c ∈ cs.filter (fun c => !knownAs K c true), ∃ b, (c.eval g ν : Option Bool) = some b ∧
        (b = false → (a.eval g ν : Option p.Denote) = d.eval g ν) :=
    fun r hr c hcm => hc r hr c (List.mem_filter.1 hcm).1
  unfold guardWith
  dsimp only
  cases hcs : (cs.filter fun c => !knownAs K c true).isEmpty
  · rw [cond_false]
    cases hff : (cs.filter fun c => !knownAs K c true).any
        (fun c => c.isFF || knownAs K c false)
    · rw [cond_false, LTm.eval_seq]
      cases hq : (q.eval g ν : Option (SRef C T)) with
      | none => rw [hnone hq]; rfl
      | some r => exact key _ (hc' r hq)
    · rw [cond_true, LTm.eval_seq]
      cases hq : (q.eval g ν : Option (SRef C T)) with
      | none => rw [hnone hq]; rfl
      | some r =>
        obtain ⟨c, hcm, hcf⟩ := List.any_eq_true.1 hff
        obtain ⟨b, hb, hf⟩ := hc' r hq c hcm
        have hfalse : (c.eval g ν : Option Bool) = some false := by
          rcases Bool.or_eq_true_iff.1 hcf with h | h
          · exact LTm.isFF_eval h
          · exact knownAs_eval hK h
        rw [hfalse] at hb
        exact (hf (Option.some.inj hb).symm).symm
  · rfl

/-- **The clause keeps what a term reads**, where the starting storage shows
clean tails and the tests known on the way read as known. -/
theorem LTm.ctFoldK_eval (hg : TSto.CleanTails g.storage.obs) {s : Srt} (t : LTm C s) :
    ∀ K : CTKnown C, (∀ e ∈ K, (e.1.eval g ν : Option Bool) = some e.2) →
      (t.ctFoldK K).eval g ν = t.eval g ν := by
  induction t with
  | var | app0 | obsH | err => intro _ _; rfl
  | app1 o x ihx =>
    intro K hK
    show (LTm.app1 o (x.ctFoldK K)).eval g ν = _
    rw [LTm.eval_app1, LTm.eval_app1, ihx K hK]
  | app2 o x y ihx ihy =>
    intro K hK
    show (LTm.app2 o (x.ctFoldK K) (y.ctFoldK K)).eval g ν = _
    rw [LTm.eval_app2, LTm.eval_app2, ihx K hK, ihy K hK]
  | app3 o x y z ihx ihy ihz =>
    intro K hK
    have gen : ∀ Ky Kz : CTKnown C, (∀ e ∈ Ky, (e.1.eval g ν : Option Bool) = some e.2) →
        (∀ e ∈ Kz, (e.1.eval g ν : Option Bool) = some e.2) →
        (LTm.app3 o (x.ctFoldK K) (y.ctFoldK Ky) (z.ctFoldK Kz)).eval g ν =
          (LTm.app3 o x y z).eval g ν := by
      intro Ky Kz hy hz
      rw [LTm.eval_app3, LTm.eval_app3, ihx K hK, ihy Ky hy, ihz Kz hz]
    cases o
    case ite p =>
      show (LTm.app3 .ite (x.ctFoldK K) (y.ctFoldK ((x, true) :: K))
        (z.ctFoldK ((x, false) :: K))).eval g ν = _
      rw [LTm.eval_app3, LTm.eval_app3, ihx K hK]
      cases hx : (x.eval g ν : Option Bool) with
      | none => rfl
      | some v =>
        cases v
        · rw [ihz _ (List.forall_mem_cons.2 ⟨hx, hK⟩)]; rfl
        · rw [ihy _ (List.forall_mem_cons.2 ⟨hx, hK⟩)]; rfl
    all_goals exact gen K K hK hK
  | index it q i ihq ihi =>
    intro K hK
    show (LTm.index it (q.ctFoldK K) (i.ctFoldK K)).eval g ν = _
    rw [LTm.eval_index, LTm.eval_index, ihq K hK, ihi K hK]
  | obsW q =>
    intro K hK
    show (guardWith K q.ctGuards q (.obsW q) (.lit (PrimTy.dflt _))).eval g ν = _
    refine guardWith_eval K hK _ _ _ _ (fun hq => by rw [LTm.eval_obsW, hq]; rfl)
      fun r hr c hc => ?_
    obtain ⟨b, hb, hsh⟩ := LTm.ctGuards_ok q r hr c hc
    refine ⟨b, hb, fun hf => ?_⟩
    rw [LTm.eval_obsW, hr, Option.bind_some, hg.1 r (hsh hf)]
    rfl
  | obsL q =>
    intro K hK
    show (guardWith K q.ctGuards q (.obsL q) (LTm.nat 0)).eval g ν = _
    refine guardWith_eval K hK _ _ _ _ (fun hq => by rw [LTm.eval_obsL, hq]; rfl)
      fun r hr c hc => ?_
    obtain ⟨b, hb, hsh⟩ := LTm.ctGuards_ok q r hr c hc
    refine ⟨b, hb, fun hf => ?_⟩
    rw [LTm.eval_obsL, hr, Option.bind_some, hg.2 r (hsh hf)]
    rfl
  | seq d a ihd iha =>
    intro K hK
    show (LTm.seq (d.ctFoldK K) (a.ctFoldK K)).eval g ν = _
    rw [LTm.eval_seq, LTm.eval_seq, ihd K hK, iha K hK]
  | orElse a b iha ihb =>
    intro K hK
    show (LTm.orElse (a.ctFoldK K) (b.ctFoldK K)).eval g ν = _
    rw [LTm.eval_orElse, LTm.eval_orElse, iha K hK, ihb K hK]
  | kite a b t e iha ihb iht ihe =>
    intro K hK
    show (LTm.kite (a.ctFoldK K) (b.ctFoldK K) (t.ctFoldK K) (e.ctFoldK K)).eval g ν = _
    rw [LTm.eval_kite, LTm.eval_kite, iha K hK, ihb K hK, iht K hK, ihe K hK]

theorem LTm.ctFold_eval (hg : TSto.CleanTails g.storage.obs) {s : Srt} (t : LTm C s) :
    t.ctFold.eval g ν = t.eval g ν :=
  t.ctFoldK_eval hg [] fun _ h => nomatch h

theorem LFml.ctFold_holds (hg : TSto.CleanTails g.storage.obs) (φ : LFml C) :
    ∀ ν : AEnv, φ.ctFold.holds g ν ↔ φ.holds g ν := by
  induction φ with
  | tt => intro ν; exact Iff.rfl
  | eq a b =>
    intro ν
    show (LFml.eq a.ctFold b.ctFold).holds g ν ↔ _
    rw [LFml.holds_eq_iff, LFml.holds_eq_iff, LTm.ctFold_eval hg, LTm.ctFold_eval hg]
  | not φ ih => intro ν; exact not_congr (ih ν)
  | and φ ψ ihφ ihψ => intro ν; exact and_congr (ihφ ν) (ihψ ν)
  | imp φ ψ ihφ ihψ => intro ν; exact imp_congr (ihφ ν) (ihψ ν)
  | all k p φ ih => intro ν; exact forall_congr' fun v => ih _

end Sound

/-- **`sol_decide` under clean tails**: `LFml.decideMem` with the clause on
the eliminated reduction. -/
def LFml.decideMemCT (φ : LFml C) : Bool := (φ.nfE.elimF {}).ctFold.closeMem

theorem LFml.decideMemCT_holds {φ : LFml C} (h : φ.decideMemCT = true) (g : State C [])
    (ν : AEnv) (hg : TSto.CleanTails g.storage.obs) : φ.holds g ν :=
  (LFml.nfE_holds φ ν).1 ((LFml.elimF_holds g φ.nfE {} ν (Facts.ok_empty ν)).1
    ((LFml.ctFold_holds hg _ ν).1 (LFml.closeMem_valid h g ν)))

end Decide

end Solidity
