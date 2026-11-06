import Solidity.Yul.Views.RetainedArrayLayout

namespace Solidity.Yul.Views

/-- Only actual checked packing computation and source typing are inputs.
No final read/view/inverse law is a certificate field. -/
structure RetainedChildPack {E τ b} (child : RecursiveStorageDeclaration E τ b)
    (p : Source.SPath) (a : Roadmap.Address) (cursor : Nat) where
  typed : E.pathTy p = some τ
  registrations : List (ScalarPath E.layout (E.lay a))
  stop : Nat
  packed : child.pack p a cursor = .ok (registrations,stop)

def prepareRetainedChild? {E τ b} (child : RecursiveStorageDeclaration E τ b)
    (p : Source.SPath) (a : Roadmap.Address) (cursor : Nat) : Option (RetainedChildPack child p a cursor) :=
  if typed : E.pathTy p = some τ then
    match packed : child.pack p a cursor with
    | .error _ => none
    | .ok (cs,stop) => some ⟨typed,cs,stop,packed⟩
  else none

def RetainedChildPack.header {E τ b child p a cursor} (r : @RetainedChildPack E τ b child p a cursor)
    (entry : {entry // entry ∈ child.headers p cursor}) : PathPrimitiveHeader E entry.val.1 entry.val.2.1 entry.val.2.2 := by
  obtain ⟨h,_⟩ := child.headers_sound _ _ _ _ _ r.typed r.packed entry.val entry.property
  exact h

theorem RetainedChildPack.header_member {E τ b child p a cursor} (r : @RetainedChildPack E τ b child p a cursor)
    (entry : {entry // entry ∈ child.headers p cursor}) : (r.header entry).registration a ∈ r.registrations := by
  obtain ⟨h,member⟩ := child.headers_sound _ _ _ _ _ r.typed r.packed entry.val entry.property
  rw [h.proof_irrel (r.header entry)] at member
  exact member

theorem RetainedChildPack.bank {E τ b child p a cursor} (r : @RetainedChildPack E τ b child p a cursor)
    (bank : E.transientRoot p=false) (c) (member : c ∈ r.registrations) : E.transientRoot c.path=false := by
  obtain ⟨suffix,below⟩ := (child.pack_good _ _ _ _ _ r.packed).2.2.2 c member |>.2.2
  unfold Source.Env.transientRoot
  rw [below]
  exact bank

def RetainedChildPack.snapshot {E τ b child p a cursor} (r : @RetainedChildPack E τ b child p a cursor)
    (fixed : Roadmap.Evm.Fixed) (m : SlotView) :=
  r.registrations ++ (child.headers p cursor).attach.flatMap (fun entry => (r.header entry).elements fixed a (m ((r.header entry).registration a).slot))

def RetainedChildPack.sourceLive? {E τ b child p a cursor Γ} (r : @RetainedChildPack E τ b child p a cursor)
    (fixed : Roadmap.Evm.Fixed) (F : Source.Fr) (s : Source.EMState E Γ) (account : F.this=a) :
    List {entry // entry ∈ child.headers p cursor} → Option (List (ScalarPath E.layout (E.lay a)))
  | [] => some []
  | entry::rest => do
    let n ← aggregateSourceLengths F s (account.symm ▸ (r.header entry).registration a)
    let tail ← r.sourceLive? fixed F s account rest
    pure ((r.header entry).elements fixed a n ++ tail)

def RetainedChildPack.sourceInventory? {E τ b child p a cursor Γ} (r : @RetainedChildPack E τ b child p a cursor)
    (fixed : Roadmap.Evm.Fixed) (F : Source.Fr) (s : Source.EMState E Γ) (account : F.this=a) :=
  (r.sourceLive? fixed F s account (child.headers p cursor).attach).map (r.registrations++·)

theorem RetainedChildPack.source_roots {E τ b child p a cursor Γ} (r : @RetainedChildPack E τ b child p a cursor)
    (fixed F) (s : Source.EMState E Γ) (account : F.this=a) (old)
    (computed : r.sourceInventory? fixed F s account = some old) (c) (member : c ∈ r.registrations) : c ∈ old := by
  obtain ⟨tail,_,same⟩ := Option.map_eq_some_iff.mp computed
  rw [←same]
  exact List.mem_append_left _ member

theorem RetainedChildPack.sourceLive_view {E τ b child p a cursor Γ} (r : @RetainedChildPack E τ b child p a cursor)
    (fixed : Roadmap.Evm.Fixed) (F : Source.Fr) (s : Source.EMState E Γ) (account : F.this=a) (m : SlotView)
    (bank : E.transientRoot p=false) (view : finiteView r.registrations (s.2.ex.world.accounts a).storage m)
    (entries : List {entry // entry ∈ child.headers p cursor}) :
    r.sourceLive? fixed F s account entries = some (entries.flatMap (fun entry => (r.header entry).elements fixed a (m ((r.header entry).registration a).slot))) := by
  subst a
  induction entries with
  | nil => rfl
  | cons entry entries ih =>
    let h := r.header entry
    have hb := r.bank bank _ (r.header_member entry)
    rw [PathPrimitiveHeader.registration_path] at hb
    have read := h.readLen_view F s m hb (view _ (r.header_member entry))
    unfold sourceLive?
    rw [show aggregateSourceLengths F s (h.registration F.this) = some (m (h.registration F.this).slot) from by
      unfold aggregateSourceLengths
      rw [PathPrimitiveHeader.registration_path,read]
      dsimp only [Except.toOption,Bind.bind,Option.bind]
      rw [dif_pos (m (h.registration F.this).slot).isLt]]
    rw [ih]
    rfl

theorem RetainedChildPack.source_view {E τ b child p a cursor Γ} (r : @RetainedChildPack E τ b child p a cursor)
    (fixed F) (s : Source.EMState E Γ) (account : F.this=a) (m : SlotView)
    (bank : E.transientRoot p=false) (view : finiteView r.registrations (s.2.ex.world.accounts a).storage m) :
    r.sourceInventory? fixed F s account = some (r.snapshot fixed m) := by
  unfold sourceInventory?
  rw [r.sourceLive_view fixed F s account m bank view]
  rfl

end Solidity.Yul.Views
