import Solidity.Yul.Views.RecursiveOwnershipResidual
import Solidity.Yul.Views.MemberSourceInventory

namespace Solidity.Yul.Views

def RootMemberDeclarations.recursiveRoots {E ds} (d : RootMemberDeclarations E ds) : RecursiveRootDeclarations E ds :=
  RootMemberDeclarations.casesOn (motive := fun ds _ => RecursiveRootDeclarations E ds) d
    .nil (fun head tail => .cons head.toRecursive tail.recursiveRoots)

theorem RootMemberDeclarations.recursiveRoots_pack {E ds} (d : RootMemberDeclarations E ds) : d.recursiveRoots.pack = d.pack := by
  induction d with
  | nil => rfl
  | @cons root τ rest head tail ih =>
    funext a cursor
    change (if E.rootTy root = some τ then (head.toRecursive.pack ⟨root,[]⟩ a cursor).bind
      (fun first => (tail.recursiveRoots.pack a first.2).map (fun out => (first.1++out.1,out.2))) else .error .missingRoot) = _
    rw [head.toRecursive_pack,ih]
    rfl

theorem RootMemberDeclarations.recursiveRoots_paths {E ds} (d : RootMemberDeclarations E ds) : d.recursiveRoots.paths = d.paths := by
  induction d with
  | nil => rfl
  | @cons root τ rest head tail ih =>
    change head.toRecursive.paths ⟨root,[]⟩ ++ tail.recursiveRoots.paths = _
    rw [head.toRecursive_paths,ih]
    rfl

theorem RootMemberDeclarations.recursiveRoots_end {E ds} (d : RootMemberDeclarations E ds) : d.recursiveRoots.endByte = d.endByte := by
  induction d with
  | nil => rfl
  | cons head tail ih =>
    funext cursor
    change tail.recursiveRoots.endByte (head.toRecursive.endByte cursor) = _
    rw [head.toRecursive_end,ih]
    rfl

theorem RootMemberDeclarations.recursiveRoots_headers {E ds} (d : RootMemberDeclarations E ds) : d.recursiveRoots.headers = d.headers := by
  induction d with
  | nil => rfl
  | @cons root τ rest head tail ih =>
    funext cursor
    change head.toRecursive.headers ⟨root,[]⟩ cursor ++ tail.recursiveRoots.headers (head.toRecursive.endByte cursor) = _
    rw [head.toRecursive_headers,head.toRecursive_end,ih]
    rfl

def MemberComputedStorage.toRecursive {E ds d active a} (r : @MemberComputedStorage E ds d active a) : RecursiveComputedStorage d.recursiveRoots active a :=
  ⟨r.origin,r.ordered,r.sourceDistinct,r.distinct,r.registrations,r.endByte,
    by rw [RootMemberDeclarations.recursiveRoots_pack]; exact r.packed⟩

theorem MemberComputedStorage.toRecursive_trace {E ds d active a} (r : @MemberComputedStorage E ds d active a) :
    r.toRecursive.headerTrace = r.headerTrace := congrFun d.recursiveRoots_headers _

theorem attach_flatMap_compatible {α β} (xs ys : List α)
    (f : {x // x ∈ xs} → List β) (g : {y // y ∈ ys} → List β)
    (same : xs = ys) (pointwise : ∀ x y, x.val = y.val → f x = g y) : xs.attach.flatMap f = ys.attach.flatMap g := by
  cases same
  have functions : f = g := funext (fun x => pointwise x x rfl)
  rw [functions]

theorem MemberComputedStorage.toRecursive_snapshot {E ds d active a} (r : @MemberComputedStorage E ds d active a)
    (fixed : Roadmap.Evm.Fixed) (m : SlotView) : r.toRecursive.snapshot fixed m = r.snapshot fixed m := by
  unfold RecursiveComputedStorage.snapshot MemberComputedStorage.snapshot
  apply congrArg (r.registrations ++ ·)
  apply attach_flatMap_compatible _ _ _ _ r.toRecursive_trace
  intro x y same
  cases x with
  | mk x hx =>
    cases y with
    | mk y hy =>
      dsimp only at same
      subst y
      have headers := PathPrimitiveHeader.proof_irrel (r.toRecursive.header ⟨x,hx⟩) (r.header ⟨x,hy⟩)
      rw [headers]

/-- Actual source-length computations agree under the concrete represented
input view; no output inventory or readback law is assumed. -/
theorem MemberComputedStorage.toRecursive_source {E ds d active Γ} (F : Source.Fr)
    (r : @MemberComputedStorage E ds d active F.this) (fixed : Roadmap.Evm.Fixed)
    (s : Source.EMState E Γ) (m : SlotView)
    (view : finiteView r.registrations (s.2.ex.world.accounts F.this).storage m) :
    r.toRecursive.sourceInventory? F fixed s = r.sourceInventory? F fixed s := by
  rw [r.toRecursive.sourceInventory_view F fixed s m view,r.sourceInventory_view F fixed s m view,r.toRecursive_snapshot]

end Solidity.Yul.Views
