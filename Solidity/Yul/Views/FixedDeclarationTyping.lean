import Solidity.Yul.Views.FixedDeclarationChecked

namespace Solidity.Yul.Views

/-- Owner path typing transports through the actual appended source step. -/
theorem fixedPathTy_go (E : Source.Env) (p : Source.SPath) (step : Source.Step) :
    E.pathTy (p.go step) = (E.pathTy p).bind (E.stepTy · step) := by
  simp only [Source.Env.pathTy,Source.SPath.go,List.foldl_append,List.foldl_cons,List.foldl_nil]

theorem fixedElementPaths_typed {E : Source.Env} {τ : Source.STy}
    (paths : Source.SPath → List Source.SPath)
    (good : ∀ p, E.pathTy p = some τ → ∀ q ∈ paths p, (E.pathTy q).isSome)
    (p : Source.SPath) (children : ∀ i, E.pathTy (p.go (.index i)) = some τ) (count index : Nat) :
    ∀ q ∈ fixedElementPaths paths p index count, (E.pathTy q).isSome := by
  induction count generalizing index with
  | zero => intro q member; cases member
  | succ n ih =>
    intro q member
    rcases List.mem_append.mp member with first | rest
    · exact good _ (children index) q first
    · exact ih (index+1) q rest

mutual
theorem FixedDeclaration.paths_typed {E τ} (d : FixedDeclaration E τ) (p : Source.SPath)
    (typed : E.pathTy p = some τ) : ∀ q ∈ d.paths p, (E.pathTy q).isSome := by
  cases d with
  | scalar τ supported =>
    intro q member
    have same := List.mem_singleton.mp member
    subst q
    rw [typed]
    rfl
  | array count positive child =>
    apply fixedElementPaths_typed child.paths child.paths_typed p _ count 0
    intro i
    rw [fixedPathTy_go,typed]
    rfl
  | strct name fields found members =>
    apply members.paths_typed 0 p
    intro j σ member
    rw [fixedPathTy_go,typed]
    change E.fieldTy? name .storage (0+j) = some σ
    simpa only [Source.Env.fieldTy?,found,Option.bind_some,List.getElem?_map,Nat.zero_add] using member

theorem FixedDeclarationFields.paths_typed {E τs} (d : FixedDeclarationFields E τs) (index : Nat) (p : Source.SPath)
    (typed : ∀ j σ, τs[j]? = some σ → E.pathTy (p.go (.field (index+j))) = some σ) :
    ∀ q ∈ d.paths index p, (E.pathTy q).isSome := by
  cases d with
  | nil => intro q member; cases member
  | cons head tail =>
    intro q member
    rcases List.mem_append.mp member with first | rest
    · exact head.paths_typed _ (typed 0 _ rfl) q first
    · apply tail.paths_typed (index+1) p _ q rest
      intro j σ member
      have previous := typed (j+1) σ (by simpa only [List.getElem?_cons_succ] using member)
      have arithmetic : (index+1)+j = index+(j+1) := by omega
      rw [arithmetic]
      exact previous
end

/-- No generated leaf relies on Env.cellTy's fallback for a missing path. -/
theorem CheckedFixedDeclaration.paths_typed {E τ d root a base} (r : @CheckedFixedDeclaration E τ d root a base)
    (c : ScalarPath E.layout (E.lay a)) (member : c ∈ r.registrations) : (E.pathTy c.path).isSome := by
  have enumerated : c.path ∈ r.registrations.map ScalarPath.path := List.mem_map.mpr ⟨c,member,rfl⟩
  rw [r.coverage] at enumerated
  apply d.paths_typed ⟨root,[]⟩ _ c.path enumerated
  exact r.rootFound

end Solidity.Yul.Views
