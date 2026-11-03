import Solidity.Yul.Views.FixedDeclarationSpec

namespace Solidity.Yul.Views

def fixedElementPaths (child : Source.SPath → List Source.SPath) (path : Source.SPath) (index count : Nat) : List Source.SPath :=
  match count with
  | 0 => []
  | n+1 => child (path.go (.index index)) ++ fixedElementPaths child path (index+1) n

mutual
def FixedDeclaration.paths {E τ} (d : FixedDeclaration E τ) : Source.SPath → List Source.SPath := by
  cases d with
  | scalar _ _ => exact fun path => [path]
  | array count _ child => exact fun path => fixedElementPaths child.paths path 0 count
  | strct _ _ _ fields => exact fields.paths 0

def FixedDeclarationFields.paths {E τs} (d : FixedDeclarationFields E τs) : Nat → Source.SPath → List Source.SPath := by
  cases d with
  | nil => exact fun _ _ => []
  | cons head tail => exact fun index path => head.paths (path.go (.field index)) ++ tail.paths (index+1) path
end

/-- Exact enumeration, not a supplied coverage premise. -/
def FixedPackPaths {E} (pack : FixedPackFn E) (paths : Source.SPath → List Source.SPath) : Prop :=
  ∀ path a cursor cs stop, pack path a cursor = .ok (cs,stop) → cs.map ScalarPath.path = paths path

theorem alignFixedPack_paths {E} (body : FixedPackFn E) (paths : Source.SPath → List Source.SPath)
    (good : FixedPackPaths body paths) : FixedPackPaths (alignFixedPack body) paths := by
  intro path a cursor cs stop success
  unfold alignFixedPack at success
  cases encoded : body path a (roundSlot cursor) with
  | error reason => simp only [encoded,Except.map] at success; cases success
  | ok result =>
    rcases result with ⟨out,last⟩
    simp only [encoded,Except.map,Except.ok.injEq,Prod.mk.injEq] at success
    obtain ⟨rfl,rfl⟩ := success
    exact good _ _ _ _ _ encoded

theorem packFixedRow_paths {E} (step : Nat → Source.Step) (head : FixedPackFn E) (tail : Nat → FixedPackFn E)
    (hp : Source.SPath → List Source.SPath) (tp : Nat → Source.SPath → List Source.SPath)
    (headGood : FixedPackPaths head hp) (tailGood : ∀ i, FixedPackPaths (tail i) (tp i)) (index : Nat) :
    FixedPackPaths (packFixedRow step head tail index) (fun path => hp (path.go (step index)) ++ tp (index+1) path) := by
  intro path a cursor cs stop success
  unfold packFixedRow at success
  cases first : head (path.go (step index)) a cursor with
  | error reason => simp only [first,Except.bind] at success; cases success
  | ok result =>
    rcases result with ⟨left,middle⟩
    cases second : tail (index+1) path a middle with
    | error reason => simp only [first,second,Except.bind,Except.map] at success; cases success
    | ok result =>
      rcases result with ⟨right,last⟩
      simp only [first,second,Except.bind,Except.map,Except.ok.injEq,Prod.mk.injEq] at success
      obtain ⟨rfl,rfl⟩ := success
      rw [List.map_append,headGood _ _ _ _ _ first,tailGood _ _ _ _ _ _ second]

theorem fixedScalar_paths (E : Source.Env) (τ : Source.STy) :
    FixedPackPaths (fun path a cursor => packDeclarationPaths E (fun _ => path) a 0 [("",τ)] cursor) (fun path => [path]) := by
  intro path a cursor cs stop success
  have complete := packDeclarationPaths_paths E (fun _ => path) a [("",τ)] 0 cursor cs stop success
  exact complete

theorem packFixedElements_paths {E} (child : FixedPackFn E) (paths : Source.SPath → List Source.SPath)
    (good : FixedPackPaths child paths) (count index : Nat) :
    FixedPackPaths (fun path a cursor => packFixedElements child path a index count cursor)
      (fun path => fixedElementPaths paths path index count) := by
  induction count generalizing index with
  | zero => intro path a cursor cs stop success; cases success; rfl
  | succ n ih => exact packFixedRow_paths Source.Step.index child _ paths _ good ih index

mutual
theorem FixedDeclaration.pack_paths {E τ} (d : FixedDeclaration E τ) : FixedPackPaths d.pack d.paths := by
  cases d with
  | scalar τ _ => exact fixedScalar_paths E τ
  | array count _ child => exact alignFixedPack_paths _ _ (packFixedElements_paths child.pack child.paths child.pack_paths count 0)
  | strct _ _ _ fields => exact alignFixedPack_paths _ _ (fields.pack_paths 0)

theorem FixedDeclarationFields.pack_paths {E τs} (d : FixedDeclarationFields E τs) (index : Nat) :
    FixedPackPaths (d.pack index) (d.paths index) := by
  cases d with
  | nil => intro path a cursor cs stop success; cases success; rfl
  | cons head tail => exact packFixedRow_paths Source.Step.field head.pack tail.pack head.paths tail.paths head.pack_paths tail.pack_paths index
end

end Solidity.Yul.Views
