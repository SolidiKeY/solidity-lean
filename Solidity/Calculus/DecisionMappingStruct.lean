import Solidity.Calculus.MemStructCut

/-!
# Fresh memory objects of a type no heap can hold

A memory mapping object is uninhabited (`MObj H (.mapping K T)` is `Empty`),
so no heap typing that has a heap lists a mapping, and no reference to a
mapping exists. A struct with a direct mapping member (`Wallet`, `Ledger`),
a nonempty fixed array of mapping references, or a mapping itself therefore
has no memory object in any state: `∀ fresh R x; φ` holds vacuously for every
body `φ`, and its negation is false in every state. This matches solc, which
rejects `new`/memory construction of such structs.

The class (`RefTy.memVoid`) is syntactic and decidable; it consults no
coverage or verdict function. The certificate is the vacuity proof itself,
not a sample of heaps. Arrays of mapping references stay outside: the empty
dynamic array is an object, so the class does not claim them.
-/
namespace Solidity.Decide.MappingStruct
open Semantics (structDef)
variable {C : Contract}

/-- A field type is a reference to a mapping. -/
def mapRef : Ty → Bool
  | .ref (.mapping _ _) => true
  | _ => false

/-- A syntactic subset of the memory types with no object in any heap: a mapping, a
struct with a direct mapping-reference member, a nonempty fixed array of mapping
references. A struct whose member is a void struct is void too, but not recognized. -/
def _root_.Solidity.RefTy.memVoid : RefTy → Bool
  | .mapping _ _ => true
  | .struct s => (structDef s).any (fun fT => mapRef fT.2)
  | .fixed E n => mapRef E && decide (0 < n)
  | .array _ => false

/-- No position of a realized object list has mapping type. -/
theorem objs_noMapping {H : HTy} : (Rs : List RefTy) → Objs H Rs →
    ∀ {i : Nat} {K : PrimTy} {T : Ty}, Rs[i]? = some (.mapping K T) → False
  | [], _, i, _, _, h => by simp only [List.getElem?_nil, reduceCtorEq] at h
  | R :: Rs, os, 0, K, T, h => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    exact (os.1 : Empty).elim
  | _ :: Rs, os, i + 1, _, _, h => by
    simp only [List.getElem?_cons_succ] at h
    exact objs_noMapping Rs os.2 h

/-- Given a heap, no reference to a mapping object exists. -/
theorem hRef_noMapping {H : HTy} (hp : Heap H) {K : PrimTy} {T : Ty}
    (r : HRef H (.mapping K T)) : False :=
  objs_noMapping H hp r.get?

/-- A memory slot of mapping-reference type is uninhabited, given a heap. -/
theorem mVal_noMapRef {H : HTy} (hp : Heap H) : (T : Ty) → mapRef T = true → MVal H T → False
  | .ref (.mapping _ _), _, v => hRef_noMapping hp v
  | .prim _, h, _ => by cases h
  | .ref (.struct _), h, _ => by cases h
  | .ref (.array _), h, _ => by cases h
  | .ref (.fixed _ _), h, _ => by cases h

/-- A field list with a mapping member has no object, given a heap. -/
theorem mFields_void {H : HTy} (hp : Heap H) : (fs : List (Name × Ty)) →
    fs.any (fun fT => mapRef fT.2) = true → MFields H fs → False
  | [], h, _ => by cases h
  | (_, T) :: fs, h, o => by
    cases hT : mapRef T with
    | true => exact mVal_noMapRef hp T hT o.1
    | false =>
      simp only [List.any_cons, hT, Bool.false_or] at h
      exact mFields_void hp fs h o.2

/-- **No object of a void type** exists in any heap. -/
theorem mObj_void {H : HTy} (hp : Heap H) : (R : RefTy) → R.memVoid = true → MObj H R → False
  | .mapping _ _, _, o => (o : Empty).elim
  | .struct s, h, o => mFields_void hp (structDef s) h o
  | .fixed E n, h, o => by
    simp only [RefTy.memVoid, Bool.and_eq_true, decide_eq_true_eq] at h
    let l : {l : List (MVal H E) // l.length = n} := o
    obtain ⟨xs, hn⟩ := l
    cases xs with
    | nil => simp only [List.length_nil] at hn; omega
    | cons v _ => exact mVal_noMapRef hp E h.1 v
  | .array _, h, _ => by cases h

/-- **Vacuity**: a fresh binder of a void type holds in every state, whatever its body. -/
theorem allocAll_void_holds {Γ : Ctx} (σ : State C Γ) (x : Var) (R : RefTy)
    (h : R.memVoid = true) (body : Fml C (.mem R :: Γ)) : holds σ (.allocAll x R body) :=
  fun o => (mObj_void σ.heap R h o).elim

/-- The exact recognized source: a fresh void binder or its negation. -/
inductive VoidSource {Γ : Ctx} : Fml C Γ → Type where
  | pos (x : Var) (R : RefTy) (h : R.memVoid = true) (body : Fml C (.mem R :: Γ)) :
      VoidSource (.allocAll x R body)
  | neg (x : Var) (R : RefTy) (h : R.memVoid = true) (body : Fml C (.mem R :: Γ)) :
      VoidSource (.not (.allocAll x R body))

/-- Recognize a void binder at the root, or under one negation. -/
def voidBinder? {Γ : Ctx} (φ : Fml C Γ) : Option (VoidSource φ) := do
  let v ← MemoryWitness.allocView φ
  if h : v.R.memVoid = true then
    return v.eqn ▸ VoidSource.pos v.x v.R h v.body
  else none

/-- Recognize the source family. -/
def voidSource? {Γ : Ctx} : (φ : Fml C Γ) → Option (VoidSource φ)
  | .not ψ => (voidBinder? ψ).bind fun w =>
      match ψ, w with
      | _, .pos x R h body => some (.neg x R h body)
      | _, .neg .. => none
  | φ => voidBinder? φ

/-- Decidable source classification, independent of target, coverage and verdict. -/
def _root_.Solidity.Fml.freshVoidBinder {Γ : Ctx} (φ : Fml C Γ) : Bool :=
  (voidSource? φ).isSome

/-- The positive polarity is proved, the negative refuted at the given state itself. -/
def VoidSource.answer {Γ : Ctx} {φ : Fml C Γ} : VoidSource φ → MemoryWitness.Answer φ
  | .pos x R h body => .proved fun σ => allocAll_void_holds σ x R h body
  | .neg x R h body => .refuted id fun σ hn => hn (allocAll_void_holds σ x R h body)

/-- The answer for a recognized source. -/
def voidAnswer? {Γ : Ctx} (φ : Fml C Γ) : Option (MemoryWitness.Answer φ) :=
  (voidSource? φ).map VoidSource.answer

/-- Every recognized source is answered. -/
theorem voidAnswer_isSome {Γ : Ctx} {φ : Fml C Γ} (h : φ.freshVoidBinder = true) :
    (voidAnswer? φ).isSome = true := by
  unfold voidAnswer?
  simpa only [Option.isSome_map] using h

/-- The one-line reason this family was a gap and why it is decided. -/
def voidReason : String :=
  "A struct with a mapping member, a mapping or a nonempty fixed array of mapping references has no memory object; the fresh binder is vacuous."

end Solidity.Decide.MappingStruct
