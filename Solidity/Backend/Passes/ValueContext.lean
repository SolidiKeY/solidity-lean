import Solidity.Backend.Passes.ValueContextCode
import Solidity.Semantics.RunWk

/-! Fresh-local adapters over the existing pointer/value certificates.
The exact original code and every original fragment premise are retained. -/
namespace Solidity.Backend.Passes
open Solidity.Evm Solidity.Evm.Memory
variable {C : Contract} {Γ : Ctx} {b : Nat} {F : Frag Γ}

theorem ptr_fresh_cert (fresh : LTy) {R : RefTy} {path : MPath C Γ (.ref R)}
    {code : List Instr} (h : Memory.PtrFrag b path code) :
    Memory.PtrFrag b (path.wk (Thin.drop (t := fresh) .refl)) code := by
  induction h with
  | «local» src hm =>
    simpa only [MPath.wk, Idx.wk, cellOf, lvl_there] using
      (Memory.PtrFrag.local (b := b) (Idx.there (u := fresh) src) hm)
  | field src hf code hs ih =>
    simpa only [MPath.wk, MLoc.wk] using
      (Memory.PtrFrag.field (src.wk (Thin.drop (t := fresh) .refl)) hf code ih)

theorem val_fresh_cert (fresh : LTy) {p : PrimTy} {e : Val C Γ p} {code : List Instr}
    (h : Memory.ValFrag b F e code) :
    Memory.ValFrag b (F.push fresh .ok) (e.wk (Thin.drop (t := fresh) .refl)) code := by
  induction h with
  | core e he =>
    have he' : valIn (F.push fresh .ok) (e.wk (Thin.drop (t := fresh) .refl)) = true := by
      rw [core_val_fresh_in]
      exact he
    simpa only [core_val_fresh_code] using Memory.ValFrag.core (b := b)
      (e.wk (Thin.drop (t := fresh) .refl)) he'
  | read src hm i index hi ih =>
    simpa only [Val.wk, MLoc.wk, MPath.wk, Idx.wk, readLocalValueCode, cellOf, lvl_there]
      using Memory.ValFrag.read (Idx.there (u := fresh) src) hm
        (i.wk (Thin.drop (t := fresh) .refl)) index ih
  | length src hm =>
    simpa only [Val.wk, MPath.wk, Idx.wk, lengthLocalCode, cellOf, lvl_there]
      using Memory.ValFrag.length (b := b) (Idx.there (u := fresh) src) hm
  | field src hm hf =>
    simpa only [Val.wk, MLoc.wk, MPath.wk, Idx.wk, readLocalFieldCode, cellOf, lvl_there]
      using Memory.ValFrag.field (b := b) (Idx.there (u := fresh) src) hm hf
  | pathRead src pointer hp i index hi ih =>
    simpa only [Val.wk, MLoc.wk] using Memory.ValFrag.pathRead
      (src.wk (Thin.drop (t := fresh) .refl)) pointer (ptr_fresh_cert fresh hp)
      (i.wk (Thin.drop (t := fresh) .refl)) index ih
  | pathLength src pointer hp =>
    simpa only [Val.wk] using Memory.ValFrag.pathLength
      (src.wk (Thin.drop (t := fresh) .refl)) pointer (ptr_fresh_cert fresh hp)
  | pathField src hf pointer hp =>
    simpa only [Val.wk, MLoc.wk] using Memory.ValFrag.pathField
      (src.wk (Thin.drop (t := fresh) .refl)) hf pointer (ptr_fresh_cert fresh hp)
  | binary op hop hacc x y left right hx hy ihx ihy =>
    simpa only [Val.wk] using Memory.ValFrag.binary op hop hacc
      (x.wk (Thin.drop (t := fresh) .refl)) (y.wk (Thin.drop (t := fresh) .refl))
      left right ihx ihy
  | unary op hop hacc x code hx ih =>
    simpa only [Val.wk] using Memory.ValFrag.unary op hop hacc
      (x.wk (Thin.drop (t := fresh) .refl)) code ih
  | conditional c x y cond left right hc hx hy ihc ihx ihy =>
    simpa only [Val.wk] using Memory.ValFrag.conditional
      (c.wk (Thin.drop (t := fresh) .refl)) (x.wk (Thin.drop (t := fresh) .refl))
      (y.wk (Thin.drop (t := fresh) .refl)) cond left right ihc ihx ihy

/-- Certificate-only adapter; the code projection is definitionally identical. -/
def value_fresh (fresh : LTy) {p : PrimTy} {e : Val C Γ p} (result : CompiledVal b F e) :
    CompiledVal b (F.push fresh .ok) (e.wk (Thin.drop (t := fresh) .refl)) :=
  ⟨result.code, val_fresh_cert fresh result.cert⟩

theorem value_fresh_code (fresh : LTy) {p : PrimTy} {e : Val C Γ p}
    (result : CompiledVal b F e) : (value_fresh fresh result).code = result.code := rfl


/-- Independent existing source weakening, specialized to actual push. -/
theorem value_fresh_eval {fresh : LTy} (σ : State C Γ) (newValue : fresh.TDenote C σ.H)
    {p : PrimTy} (e : Val C Γ p) :
    (e.wk (Thin.drop (t := fresh) .refl)).evalT (σ.push newValue) = e.evalT σ := by
  have hs := Val.evalT_wk (Thin.drop (t := fresh) .refl) σ (newValue, σ.env) e
  exact hs

variable {L frame frame' : Nat} {σ : State C Γ} {base : Nat → Fin W} {m : Machine}

/-- Frame extension for a real old reference alias retains exact pointer
identity and all old source/heap facts. Separation is NOT discarded. -/
theorem memory_extend_reference (h : StateRepr L b frame F σ base m)
    {R : RefTy} (r : HRef σ.H R)
    (capacity : b + (Γ.length + 1) ≤ frame')
    (arrays : ∀ {q : PrimTy} (a : HRef σ.H (.array (.prim q))), frame' ≤ (base a.id).val)
    (structs : ∀ {s : Name} (a : HRef σ.H (.struct s)), frame' ≤ (base a.id).val)
    (tail : List Word) :
    StateRepr L b frame' (F.push (.mem R) .ok) (σ.push (t := .mem R) (some r)) base
      (writeMachine {m with stack := tail} (cell (b + Γ.length)) (.val (base r.id))) := by
  have hl : b + Γ.length ≤ frame' := by omega
  exact ((memory_frame h hl arrays structs).stack tail).consMem r capacity

/-- Original emitted code reads the same value after declaring a fresh
scalar. Source correspondence comes from weakening, target Input from consVal. -/
theorem value_after_fresh_scalar {p q : PrimTy} {e : Val C Γ p}
    (result : CompiledVal b F e) (h : StateRepr L b frame F σ base m)
    (newValue : q.Denote) (newWord : Word) (hw : ReprV q newValue newWord)
    (capacity : b + (Γ.length + 1) ≤ frame')
    (arrays : ∀ {r : PrimTy} (a : HRef σ.H (.array (.prim r))), frame' ≤ (base a.id).val)
    (structs : ∀ {s : Name} (a : HRef σ.H (.struct s)), frame' ≤ (base a.id).val)
    {v : p.Denote} (hs : e.evalT σ = .ok v) (tail : List Word) :
    ∃ word, ReprV p v word ∧
      run result.code (writeMachine {m with stack := tail} (cell (b + Γ.length)) newWord) =
        .ok ((writeMachine {m with stack := tail} (cell (b + Γ.length)) newWord).push word) 0 := by
  have hi := memory_extend_value h newValue newWord hw capacity arrays structs tail
  have he : (e.wk (Thin.drop (t := .val q) .refl)).evalT (σ.push newValue) = .ok v :=
    (value_fresh_eval (fresh := .val q) σ newValue e).trans hs
  exact value_success_tail (value_fresh (.val q) result) hi he tail

theorem value_after_fresh_reference {p : PrimTy} {e : Val C Γ p}
    (result : CompiledVal b F e) (h : StateRepr L b frame F σ base m)
    {R : RefTy} (r : HRef σ.H R)
    (capacity : b + (Γ.length + 1) ≤ frame')
    (arrays : ∀ {q : PrimTy} (a : HRef σ.H (.array (.prim q))), frame' ≤ (base a.id).val)
    (structs : ∀ {s : Name} (a : HRef σ.H (.struct s)), frame' ≤ (base a.id).val)
    {v : p.Denote} (hs : e.evalT σ = .ok v) (tail : List Word) :
    ∃ word, ReprV p v word ∧
      run result.code (writeMachine {m with stack := tail} (cell (b + Γ.length)) (.val (base r.id))) =
        .ok ((writeMachine {m with stack := tail} (cell (b + Γ.length)) (.val (base r.id))).push word) 0 := by
  have hi := memory_extend_reference h r capacity arrays structs tail
  have he : (e.wk (Thin.drop (t := .mem R) .refl)).evalT (σ.push (some r)) = .ok v :=
    (value_fresh_eval (fresh := .mem R) σ (some r) e).trans hs
  exact value_success_tail (value_fresh (.mem R) result) hi he tail

theorem value_fresh_scalar_revert_iff {p q : PrimTy} {e : Val C Γ p}
    (result : CompiledVal b F e) (h : StateRepr L b frame F σ base m)
    (newValue : q.Denote) (newWord : Word) (hw : ReprV q newValue newWord)
    (capacity : b + (Γ.length + 1) ≤ frame')
    (arrays : ∀ {r : PrimTy} (a : HRef σ.H (.array (.prim r))), frame' ≤ (base a.id).val)
    (structs : ∀ {s : Name} (a : HRef σ.H (.struct s)), frame' ≤ (base a.id).val)
    (tail : List Word) :
    run result.code (writeMachine {m with stack := tail} (cell (b + Γ.length)) newWord) = .revert ↔
      e.evalT σ = .error .revert := by
  have hi := memory_extend_value h newValue newWord hw capacity arrays structs tail
  have ht := value_revert_iff (value_fresh (.val q) result) hi tail
  simpa only [value_fresh_eval] using ht

theorem value_fresh_reference_revert_iff {p : PrimTy} {e : Val C Γ p}
    (result : CompiledVal b F e) (h : StateRepr L b frame F σ base m)
    {R : RefTy} (r : HRef σ.H R)
    (capacity : b + (Γ.length + 1) ≤ frame')
    (arrays : ∀ {q : PrimTy} (a : HRef σ.H (.array (.prim q))), frame' ≤ (base a.id).val)
    (structs : ∀ {s : Name} (a : HRef σ.H (.struct s)), frame' ≤ (base a.id).val)
    (tail : List Word) :
    run result.code (writeMachine {m with stack := tail} (cell (b + Γ.length)) (.val (base r.id))) = .revert ↔
      e.evalT σ = .error .revert := by
  have hi := memory_extend_reference h r capacity arrays structs tail
  have ht := value_revert_iff (value_fresh (.mem R) result) hi tail
  simpa only [value_fresh_eval] using ht

end Solidity.Backend.Passes
