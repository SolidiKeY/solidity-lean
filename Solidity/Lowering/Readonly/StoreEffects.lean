import Solidity.Lowering.Readonly.LoadEffects
import Solidity.Lowering.Readonly.DeleteEffects

/-! Actual Source storage-copy history steps. Smaller-bound copy histories
are explicit until the mutual induction closes; the dynamic static guard and
storage-reference self-copy no-op are unchanged. -/
namespace Solidity.Lowering.Readonly.SourceHistory
open Solidity.Source
variable {E : Env} {Γ : RCtx}

theorem storeVal_step (F : Fr) (n : Nat)
    (data : ∀ τ p {σ} (x : Data E.layout σ),
      Effect F.static (storeData (Γ := Γ) F n τ p x)) :
    ∀ τ p {σ} (v : Val E.layout σ),
      Effect F.static (storeVal (Γ := Γ) F (n+1) τ p v) := by
  intro τ p σ value
  cases value
  case memRef a h =>
    apply Effect.bind
    · exact heapObj_effect F.static a
    · rintro ⟨σ, x⟩
      exact data τ p x
  case storRef q h =>
    simp only [storeVal]
    split
    · exact Effect.pure F.static ()
    · exact Effect.bind _ _ _ ((load_histories F.static F n).1 (τ.withLoc .memory) q)
        (fun x => data τ p x)
  all_goals exact writeAt_effect F p _


theorem storeData_bytes_step : ∀ {E : Solidity.Source.Env} {Γ : Solidity.Source.RCtx} (F : Solidity.Source.Fr) (n : Nat),
 (∀ p i bs, Solidity.Lowering.Readonly.SourceHistory.Effect F.static (Solidity.Source.storeBytes (E := E) (Γ := Γ) F n p i bs)) →
 ∀ (loc : Solidity.Source.DataLoc) (bs : List UInt8) τ p,
 Solidity.Lowering.Readonly.SourceHistory.Effect F.static (Solidity.Source.storeData (E := E) (Γ := Γ) F (n+1) τ p (Solidity.Source.Data.bytes (l := loc) bs)) := by
  intro E Γ F n bytes loc bs τ p
  have deletes : ∀ σ p i k, Solidity.Lowering.Readonly.SourceHistory.Effect F.static (Solidity.Source.deleteRange (E := E) (Γ := Γ) F n σ p i k) :=
    (Solidity.Lowering.Readonly.SourceHistory.delete_histories F n).2.1
  cases τ
  case bytes l => exact Solidity.Lowering.Readonly.SourceHistory.Effect.bind _ _ _ (Solidity.Lowering.Readonly.SourceHistory.readLen_effect F.static F p) (fun old =>
      Solidity.Lowering.Readonly.SourceHistory.Effect.bind _ _ _ (bytes p 0 bs) (fun _ =>
        Solidity.Lowering.Readonly.SourceHistory.Effect.bind _ _ _ (deletes _ p bs.length (old - bs.length)) (fun _ =>
          Solidity.Lowering.Readonly.SourceHistory.writeAt_effect F p _)))
  case string l => exact Solidity.Lowering.Readonly.SourceHistory.Effect.bind _ _ _ (Solidity.Lowering.Readonly.SourceHistory.readLen_effect F.static F p) (fun old =>
      Solidity.Lowering.Readonly.SourceHistory.Effect.bind _ _ _ (bytes p 0 bs) (fun _ =>
        Solidity.Lowering.Readonly.SourceHistory.Effect.bind _ _ _ (deletes _ p bs.length (old - bs.length)) (fun _ =>
          Solidity.Lowering.Readonly.SourceHistory.writeAt_effect F p _)))
  case array l σ size => cases size <;> exact Solidity.Lowering.Readonly.SourceHistory.Effect.halt F.static _
  all_goals exact Solidity.Lowering.Readonly.SourceHistory.Effect.halt F.static _

theorem storeData_string_step : ∀ {E : Solidity.Source.Env} {Γ : Solidity.Source.RCtx} (F : Solidity.Source.Fr) (n : Nat),
 (∀ p i bs, Solidity.Lowering.Readonly.SourceHistory.Effect F.static (Solidity.Source.storeBytes (E := E) (Γ := Γ) F n p i bs)) →
 ∀ (loc : Solidity.Source.DataLoc) (bs : List UInt8) τ p,
 Solidity.Lowering.Readonly.SourceHistory.Effect F.static (Solidity.Source.storeData (E := E) (Γ := Γ) F (n+1) τ p (Solidity.Source.Data.string (l := loc) bs)) := by
  intro E Γ F n bytes loc bs τ p
  have deletes : ∀ σ p i k, Solidity.Lowering.Readonly.SourceHistory.Effect F.static (Solidity.Source.deleteRange (E := E) (Γ := Γ) F n σ p i k) :=
    (Solidity.Lowering.Readonly.SourceHistory.delete_histories F n).2.1
  cases τ
  case bytes l => exact Solidity.Lowering.Readonly.SourceHistory.Effect.bind _ _ _ (Solidity.Lowering.Readonly.SourceHistory.readLen_effect F.static F p) (fun old =>
      Solidity.Lowering.Readonly.SourceHistory.Effect.bind _ _ _ (bytes p 0 bs) (fun _ =>
        Solidity.Lowering.Readonly.SourceHistory.Effect.bind _ _ _ (deletes _ p bs.length (old - bs.length)) (fun _ =>
          Solidity.Lowering.Readonly.SourceHistory.writeAt_effect F p _)))
  case string l => exact Solidity.Lowering.Readonly.SourceHistory.Effect.bind _ _ _ (Solidity.Lowering.Readonly.SourceHistory.readLen_effect F.static F p) (fun old =>
      Solidity.Lowering.Readonly.SourceHistory.Effect.bind _ _ _ (bytes p 0 bs) (fun _ =>
        Solidity.Lowering.Readonly.SourceHistory.Effect.bind _ _ _ (deletes _ p bs.length (old - bs.length)) (fun _ =>
          Solidity.Lowering.Readonly.SourceHistory.writeAt_effect F p _)))
  case array l σ size => cases size <;> exact Solidity.Lowering.Readonly.SourceHistory.Effect.halt F.static _
  all_goals exact Solidity.Lowering.Readonly.SourceHistory.Effect.halt F.static _

theorem storeData_array_step : ∀ {E : Solidity.Source.Env} {Γ : Solidity.Source.RCtx} (F : Solidity.Source.Fr) (n : Nat),
 (∀ τ p i len {σ} (xs : Fin len → Solidity.Source.Data E.layout σ), Solidity.Lowering.Readonly.SourceHistory.Effect F.static (Solidity.Source.storeElems (Γ := Γ) F n τ p i len xs)) →
 ∀ (loc : Solidity.Source.DataLoc) (σ : Solidity.Source.STy) (size : Option Nat) (len : Nat)
 (hl : ∀ m, size = some m → m = len) (xs : Fin len → Solidity.Source.Data E.layout σ) τ p,
 Solidity.Lowering.Readonly.SourceHistory.Effect F.static (Solidity.Source.storeData (E := E) (Γ := Γ) F (n+1) τ p (Solidity.Source.Data.array (l := loc) (n := size) len hl xs)) := by
  intro E Γ F n elems loc σ size len hl xs τ p
  have deletes : ∀ σ p i k, Solidity.Lowering.Readonly.SourceHistory.Effect F.static (Solidity.Source.deleteRange (E := E) (Γ := Γ) F n σ p i k) :=
    (Solidity.Lowering.Readonly.SourceHistory.delete_histories F n).2.1
  cases τ
  case array l t target =>
    cases target with
    | none => exact Solidity.Lowering.Readonly.SourceHistory.Effect.bind _ _ _ (Solidity.Lowering.Readonly.SourceHistory.readLen_effect F.static F p) (fun old =>
        Solidity.Lowering.Readonly.SourceHistory.Effect.bind _ _ _ (elems t p 0 len xs) (fun _ =>
          Solidity.Lowering.Readonly.SourceHistory.Effect.bind _ _ _ (deletes t p len (old - len)) (fun _ => Solidity.Lowering.Readonly.SourceHistory.writeAt_effect F p _)))
    | some m => exact elems t p 0 len xs
  all_goals exact Solidity.Lowering.Readonly.SourceHistory.Effect.halt F.static _

theorem storeData_struct_step : ∀ {E : Solidity.Source.Env} {Γ : Solidity.Source.RCtx} (F : Solidity.Source.Fr) (n : Nat),
 (∀ τs p i {σs} (xs : Solidity.Source.DataList E.layout σs), Solidity.Lowering.Readonly.SourceHistory.Effect F.static (Solidity.Source.storeFields (Γ := Γ) F n τs p i xs)) →
 ∀ (loc : Solidity.Source.DataLoc) (d : Solidity.Source.DeclName) (fs : Solidity.Source.DataList E.layout (E.layout.fields d)) τ p,
 Solidity.Lowering.Readonly.SourceHistory.Effect F.static (Solidity.Source.storeData (E := E) (Γ := Γ) F (n+1) τ p (Solidity.Source.Data.struct (l := loc) (d := d) fs)) := by
  intro E Γ F n fields loc d fs τ p
  cases τ
  case struct l target => exact fields _ p 0 fs
  case array l σ size => cases size <;> exact Solidity.Lowering.Readonly.SourceHistory.Effect.halt F.static _
  all_goals exact Solidity.Lowering.Readonly.SourceHistory.Effect.halt F.static _

theorem storeData_value_step : ∀ {E : Solidity.Source.Env} {Γ : Solidity.Source.RCtx} (F : Solidity.Source.Fr) (n : Nat),
 (∀ τ p {σ} (v : Solidity.Source.Val E.layout σ), Solidity.Lowering.Readonly.SourceHistory.Effect F.static (Solidity.Source.storeVal (Γ := Γ) F n τ p v)) →
 ∀ {σ} (v : Solidity.Source.Val E.layout σ) τ p,
 Solidity.Lowering.Readonly.SourceHistory.Effect F.static (Solidity.Source.storeData (E := E) (Γ := Γ) F (n+1) τ p (Solidity.Source.Data.val v)) := by
  intro E Γ F n values σ v τ p
  cases τ
  case array l t size => cases size <;> exact values _ p v
  all_goals exact values _ p v

theorem storeData_mapping_step : ∀ {E : Solidity.Source.Env} {Γ : Solidity.Source.RCtx} (F : Solidity.Source.Fr) (n : Nat)
 (k v : Solidity.Source.STy) (map : Solidity.Source.KeyOf E.layout k → Solidity.Source.Data E.layout v) τ p,
 Solidity.Lowering.Readonly.SourceHistory.Effect F.static (Solidity.Source.storeData (E := E) (Γ := Γ) F (n+1) τ p (Solidity.Source.Data.mapping map)) := by
  intro E Γ F n k v map τ p
  cases τ
  case array l t size => cases size <;> exact Solidity.Lowering.Readonly.SourceHistory.Effect.halt F.static _
  all_goals exact Solidity.Lowering.Readonly.SourceHistory.Effect.halt F.static _


theorem storeData_step : ∀ {E : Solidity.Source.Env} {Γ : Solidity.Source.RCtx} (F : Solidity.Source.Fr) (n : Nat),
 (∀ τ p {σ} (v : Solidity.Source.Val E.layout σ), Solidity.Lowering.Readonly.SourceHistory.Effect F.static (Solidity.Source.storeVal (Γ := Γ) F n τ p v)) →
 (∀ τ p i len {σ} (xs : Fin len → Solidity.Source.Data E.layout σ), Solidity.Lowering.Readonly.SourceHistory.Effect F.static (Solidity.Source.storeElems (Γ := Γ) F n τ p i len xs)) →
 (∀ τs p i {σs} (xs : Solidity.Source.DataList E.layout σs), Solidity.Lowering.Readonly.SourceHistory.Effect F.static (Solidity.Source.storeFields (Γ := Γ) F n τs p i xs)) →
 (∀ p i bs, Solidity.Lowering.Readonly.SourceHistory.Effect F.static (Solidity.Source.storeBytes (E := E) (Γ := Γ) F n p i bs)) →
 ∀ τ p {σ} (x : Solidity.Source.Data E.layout σ), Solidity.Lowering.Readonly.SourceHistory.Effect F.static (Solidity.Source.storeData (Γ := Γ) F (n+1) τ p x) := by
  intro E Γ F n values elems fields bytes τ p σ x
  cases x
  case val => exact Solidity.Lowering.Readonly.SourceHistory.storeData_value_step (E := E) (Γ := Γ) F n values _ τ p
  case bytes => exact Solidity.Lowering.Readonly.SourceHistory.storeData_bytes_step (E := E) (Γ := Γ) F n bytes _ _ τ p
  case string => exact Solidity.Lowering.Readonly.SourceHistory.storeData_string_step (E := E) (Γ := Γ) F n bytes _ _ τ p
  case array => exact Solidity.Lowering.Readonly.SourceHistory.storeData_array_step (E := E) (Γ := Γ) F n elems _ _ _ _ _ _ τ p
  case struct => exact Solidity.Lowering.Readonly.SourceHistory.storeData_struct_step (E := E) (Γ := Γ) F n fields _ _ _ τ p
  case mapping => exact Solidity.Lowering.Readonly.SourceHistory.storeData_mapping_step (E := E) (Γ := Γ) F n _ _ _ τ p


/-- Closed mutual induction for every actual Source storage-copy helper.
Success, refusal, no-op and exhausted executions retain their histories. -/
theorem store_histories (F : Fr) (n : Nat) :
    (∀ τ p {σ} (x : Data E.layout σ), Effect F.static (storeData (Γ := Γ) F n τ p x)) ∧
    (∀ τ p {σ} (v : Val E.layout σ), Effect F.static (storeVal (Γ := Γ) F n τ p v)) ∧
    (∀ τ p i len {σ} (xs : Fin len → Data E.layout σ), Effect F.static (storeElems (Γ := Γ) F n τ p i len xs)) ∧
    (∀ τs p i {σs} (xs : DataList E.layout σs), Effect F.static (storeFields (Γ := Γ) F n τs p i xs)) ∧
    (∀ p i bs, Effect F.static (storeBytes (E := E) (Γ := Γ) F n p i bs)) := by
  induction n with
  | zero =>
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro τ p σ x; exact Effect.halt F.static _
    · intro τ p σ v; exact Effect.halt F.static _
    · intro τ p i len σ xs; cases len <;> exact Effect.halt F.static _
    · intro τs p i σs xs; cases τs <;> cases xs <;> exact Effect.halt F.static _
    · intro p i bs; cases bs <;> exact Effect.halt F.static _
  | succ n ih =>
    rcases ih with ⟨data, values, elems, fields, bytes⟩
    refine ⟨storeData_step F n values elems fields bytes, storeVal_step F n data, ?_, ?_, ?_⟩
    · intro τ p i len σ xs
      cases len with
      | zero => exact Effect.pure F.static ()
      | succ len =>
        exact Effect.bind _ _ _ (data τ _ _) (fun _ => elems τ p (i+1) len _)
    · intro τs p i σs xs
      cases τs
      case nil => exact Effect.pure F.static ()
      case cons τ τs =>
        cases xs
        case nil => exact Effect.pure F.static ()
        case cons => exact Effect.bind _ _ _ (data τ _ _) (fun _ => fields τs p (i+1) _)
    · intro p i bs
      cases bs with
      | nil => exact Effect.pure F.static ()
      | cons b bs => exact Effect.bind _ _ _ (writeAt_effect F _ _) (fun _ => bytes p (i+1) bs)

end Solidity.Lowering.Readonly.SourceHistory
