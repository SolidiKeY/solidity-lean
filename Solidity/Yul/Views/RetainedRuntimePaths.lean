import Solidity.Yul.Views.RetainedExpressionCapture

namespace Solidity.Yul.Views

mutual
  def runtimeStoragePathsM {D : Source.Layout} {σ : Source.STy} (value : Source.RVal D σ) : List Source.SPath := by
    cases value with
    | val v => exact valueStoragePaths v
    | const | strLit | hex => exact []
    | tuple values => exact runtimeValuesPathsM values
  termination_by structural value

  def runtimeValuesPathsM {D : Source.Layout} {types : List Source.STy} (values : Source.RVals D types) : List Source.SPath := by
    cases values with
    | nil => exact []
    | cons value rest => exact runtimeStoragePathsM value ++ runtimeValuesPathsM rest
  termination_by structural values
end

/-- Capture before getV: a tuple is not a plain Val, but each of its actual
indexed constituents may hold a retained storage reference. No conversion,
current-length test, formation witness or owner representation change. -/
@[implemented_by runtimeStoragePathsM]
def runtimeStoragePaths {D : Source.Layout} {σ : Source.STy} (value : Source.RVal D σ) : List Source.SPath :=
  Source.RVal.rec (motive_1 := fun _ _ => List Source.SPath) (motive_2 := fun _ _ => List Source.SPath)
    (fun v => valueStoragePaths v) (fun _ => []) (fun _ => []) (fun _ _ => [])
    (fun _ paths => paths) [] (fun _ _ head tail => head++tail) value

@[implemented_by runtimeValuesPathsM]
def runtimeValuesPaths {D : Source.Layout} {types : List Source.STy} (values : Source.RVals D types) : List Source.SPath :=
  Source.RVals.rec (motive_1 := fun _ _ => List Source.SPath) (motive_2 := fun _ _ => List Source.SPath)
    (fun v => valueStoragePaths v) (fun _ => []) (fun _ => []) (fun _ _ => [])
    (fun _ paths => paths) [] (fun _ _ head tail => head++tail) values

theorem runtimeStoragePaths_eq_M {D σ} (value : Source.RVal D σ) : runtimeStoragePaths value=runtimeStoragePathsM value :=
  Source.RVal.rec
    (motive_1 := fun _ v => runtimeStoragePaths v=runtimeStoragePathsM v)
    (motive_2 := fun _ vs => runtimeValuesPaths vs=runtimeValuesPathsM vs)
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ ih => ih) rfl (fun v vs head tail => (congrArg (fun xs => xs ++ runtimeValuesPaths vs) head).trans
      (congrArg (fun xs => runtimeStoragePathsM v ++ xs) tail)) value

theorem runtimeValuesPaths_eq_M {D types} (values : Source.RVals D types) : runtimeValuesPaths values=runtimeValuesPathsM values :=
  Source.RVals.rec
    (motive_1 := fun _ v => runtimeStoragePaths v=runtimeStoragePathsM v)
    (motive_2 := fun _ vs => runtimeValuesPaths vs=runtimeValuesPathsM vs)
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ ih => ih) rfl (fun v vs head tail => (congrArg (fun xs => xs ++ runtimeValuesPaths vs) head).trans
      (congrArg (fun xs => runtimeStoragePathsM v ++ xs) tail)) values

theorem runtime_tuple_paths {D types} (values : Source.RVals D types) :
    runtimeStoragePaths (.tuple values)=runtimeValuesPaths values := rfl

theorem runtime_cons_member {D σ types} (value : Source.RVal D σ) (rest : Source.RVals D types) (p) :
    p ∈ runtimeValuesPaths (.cons value rest) ↔ p ∈ runtimeStoragePaths value ∨ p ∈ runtimeValuesPaths rest := List.mem_append

/-- Exact owner return packaging at every arity, including singleton unwrapping. -/
theorem runtime_mkRet_paths {D} (types : List Source.STy) (values : Source.RVals D types) :
    runtimeStoragePaths (Source.mkRet types values)=runtimeValuesPaths values := by
  cases types with
  | nil => rfl
  | cons first rest =>
    cases rest with
    | nil => cases values with | cons value tail => cases tail; exact (List.append_nil _).symm
    | cons next rest => rfl

def runtimeScope {E σ} (F : Source.Fr) (value : Source.RVal E.layout σ) : EntryReferenceScope E :=
  ⟨F.this,runtimeStoragePaths value⟩
def runtimeValuesScope {E types} (F : Source.Fr) (values : Source.RVals E.layout types) : EntryReferenceScope E :=
  ⟨F.this,runtimeValuesPaths values⟩

end Solidity.Yul.Views
