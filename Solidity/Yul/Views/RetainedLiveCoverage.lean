import Solidity.Yul.Views.RetainedCallerHeaders

/-! Successful source traversal derives actual header lengths and includes all
live primitive registrations they generate. No final inventory-coverage theorem
or raw/source agreement is accepted as an input. Canonical preparation, layout
and physical separation remain distinct checked obligations. -/
namespace Solidity.Yul.Views.RetainedLiveCoverage

theorem live {E τ b child p a cursor Γ} (pack : @RetainedChildPack E τ b child p a cursor)
    (fixed : Roadmap.Evm.Fixed) (F : Source.Fr) (source : Source.EMState E Γ) (account : F.this=a)
    (entries : List {entry // entry ∈ child.headers p cursor}) (inventory)
    (computed : pack.sourceLive? fixed F source account entries=some inventory)
    (entry) (present : entry ∈ entries) :
    ∃ length, aggregateSourceLengths F source (account.symm ▸ (pack.header entry).registration a)=some length ∧
      ∀ c ∈ (pack.header entry).elements fixed a length, c ∈ inventory := by
  first | (simp only;done) | skip
  induction entries generalizing inventory with
  | nil => cases present
  | cons head tail ih =>
    obtain ⟨length,lengthRead,next⟩ := Option.bind_eq_some_iff.mp computed
    obtain ⟨rest,tailRead,same⟩ := Option.bind_eq_some_iff.mp next
    cases same
    rcases List.mem_cons.mp present with same | later
    · subst entry
      exact ⟨length,lengthRead,fun c member => List.mem_append_left _ member⟩
    · obtain ⟨n,read,covered⟩ := ih rest tailRead later
      exact ⟨n,read,fun c member => List.mem_append_right _ (covered c member)⟩

theorem child {E τ b declaration p a cursor Γ} (pack : @RetainedChildPack E τ b declaration p a cursor)
    (fixed : Roadmap.Evm.Fixed) (F : Source.Fr) (source : Source.EMState E Γ) (account : F.this=a)
    (inventory) (computed : pack.sourceInventory? fixed F source account=some inventory)
    (entry : {entry // entry ∈ declaration.headers p cursor}) :
    ∃ length, aggregateSourceLengths F source (account.symm ▸ (pack.header entry).registration a)=some length ∧
      ∀ c ∈ (pack.header entry).elements fixed a length, c ∈ inventory := by
  first | (simp only;done) | skip
  obtain ⟨tail,found,same⟩ := Option.map_eq_some_iff.mp computed
  obtain ⟨n,read,covered⟩ := live pack fixed F source account _ tail found entry (List.mem_attach _ _)
  refine ⟨n,read,?_⟩
  intro c member
  rw [←same]
  exact List.mem_append_right _ (covered c member)

theorem children {E τ b declaration active Γ} {F : Source.Fr}
    {layout : @RetainedArrayLayout E τ b declaration active F.this}
    (fixed : Roadmap.Evm.Fixed) (source : Source.EMState E Γ)
    (elements : List (RetainedElementPack layout fixed)) (inventory)
    (computed : retainedChildrenSource? fixed source elements=some inventory)
    (element) (present : element ∈ elements) :
    ∃ childInventory, element.2.sourceInventory? fixed F source rfl=some childInventory ∧
      ∀ c ∈ childInventory, c ∈ inventory := by
  first | (simp only;done) | skip
  induction elements generalizing inventory with
  | nil => cases present
  | cons head tail ih =>
    obtain ⟨first,headRead,next⟩ := Option.bind_eq_some_iff.mp computed
    obtain ⟨rest,tailRead,same⟩ := Option.bind_eq_some_iff.mp next
    cases same
    rcases List.mem_cons.mp present with same | later
    · subst element
      exact ⟨first,headRead,fun c member => List.mem_append_left _ member⟩
    · obtain ⟨found,read,covered⟩ := ih rest tailRead later
      exact ⟨found,read,fun c member => List.mem_append_right _ (covered c member)⟩

theorem image {E τ b declaration active Γ} {F : Source.Fr}
    {layout : @RetainedArrayLayout E τ b declaration active F.this} {fixed history scopes length}
    (image : CapturedArrayImage layout fixed history scopes length) (source : Source.EMState E Γ)
    (inventory) (computed : image.sourceInventory? (F:=F) source=some inventory)
    (element) (present : element ∈ image.elements)
    (entry : {entry // entry ∈ declaration.headers (layout.path.go (.index element.1)) (layout.childCursor fixed element.1)}) :
    ∃ n, aggregateSourceLengths F source (element.2.header entry |>.registration F.this)=some n ∧
      ∀ c ∈ (element.2.header entry).elements fixed F.this n, c ∈ inventory := by
  first | (simp only;done) | skip
  obtain ⟨tail,found,same⟩ := Option.map_eq_some_iff.mp computed
  obtain ⟨part,read,covered⟩ := children fixed source image.elements tail found element present
  obtain ⟨n,lengthRead,members⟩ := child element.2 fixed F source rfl part read entry
  refine ⟨n,lengthRead,?_⟩
  intro c member
  rw [←same]
  exact List.mem_cons_of_mem _ (covered c (members c member))
end Solidity.Yul.Views.RetainedLiveCoverage
