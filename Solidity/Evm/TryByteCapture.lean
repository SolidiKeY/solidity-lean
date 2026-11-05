import Solidity.Evm.TryByteImage
import Solidity.Semantics.AllocBytes
import Solidity.Semantics.RevertMemory
import Solidity.Theory.Typed.Mem

/-!
# Computed image snapshots materialized in the intrinsic heap

This is ghost witness materialization, not an extra physical EVM allocation.
No expected/reference bytes are arguments to the producer. Reuse existing
allocation, weakening and raw-memory revert semantics without modifying them.
-/
namespace Solidity.Evm.TryByteImage

variable {C : Contract} {Γ : Ctx}

/-- The existing typed allocation consumer; old locals are weakened, not lost. -/
def captureBytes (bs : List UInt8) (hn : bs.length < 2 ^ 256) :
    TStep C Γ (.mem bytesR :: Γ) := fun σ =>
  .ok ⟨σ.allocPush (bytesObj σ.H bs hn), List.prefix_append σ.H [bytesR]⟩

/-- A computed byte snapshot supplies the object, never an external oracle. -/
def captureSnapshot (μ : FrameMem C Γ) (s : ByteSpan μ.capacity)
    (hn : (snapshot μ s).length < 2 ^ 256) : State C (.mem bytesR :: Γ) :=
  μ.st.allocPush (bytesObj μ.st.H (snapshot μ s) hn)

/-- A materialized byte word reads back as the same byte. -/
theorem byteWord_roundtrip (b : UInt8) : UInt8.ofNat (byteWord b).val.toNat = b := by
  change UInt8.ofNat (Int.toNat (Int.ofNat b.toNat)) = b
  exact UInt8.ofNat_toNat

/-- The actual fresh object, read through its real HRef, is the supplied list. -/
theorem captureBytes_read (σ : State C Γ) (bs : List UInt8) (hn : bs.length < 2 ^ 256) :
    ((σ.allocPush (bytesObj σ.H bs hn)).heap.get (σ.alloc (bytesObj σ.H bs hn)).2).1.map
      (fun v => UInt8.ofNat v.val.toNat) = bs := by
  rw [State.allocPush_get]
  change ((bs.map byteWord).map id).map (fun v => UInt8.ofNat v.val.toNat) = bs
  rw [List.map_id]
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    simp only [List.map_cons, byteWord_roundtrip,
      ih (by have h := hn; simp only [List.length_cons] at h; omega)]

/-- One fresh identity is appended; it cannot alias an old object. -/
theorem capture_fresh (σ : State C Γ) (bs : List UInt8) (hn : bs.length < 2 ^ 256) :
    (σ.alloc (bytesObj σ.H bs hn)).2.id = σ.H.length := rfl

/-- All old heap objects and their alias identities are preserved. -/
theorem capture_keeps (σ : State C Γ) (bs : List UInt8) (hn : bs.length < 2 ^ 256) :
    Heap.Keeps (List.prefix_append σ.H [bytesR]) σ.heap
      (σ.allocPush (bytesObj σ.H bs hn)).heap := Heap.keeps_alloc _ _

/-- Existing local values are weakened along precisely that heap extension. -/
theorem capture_env (σ : State C Γ) (bs : List UInt8) (hn : bs.length < 2 ^ 256)
    {t : LTy} (i : Idx Γ t) :
    TEnv.get (.there i) (σ.allocPush (bytesObj σ.H bs hn)).env =
      LTy.TDenote.wk (List.prefix_append σ.H [bytesR]) t (TEnv.get i σ.env) :=
  TEnv.get_wk _ i _

/-- Ghost materialization preserves the entire caller global frame. -/
theorem capture_globals (σ : State C Γ) (bs : List UInt8) (hn : bs.length < 2 ^ 256) :
    let τ := σ.allocPush (bytesObj σ.H bs hn)
    τ.storage = σ.storage ∧ τ.net = σ.net ∧ τ.tx = σ.tx ∧ τ.selfBalance = σ.selfBalance :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Allocate the computed bytes, then run the existing memory-revert step. -/
def bytesHalt (bs : List UInt8) (hn : bs.length < 2 ^ 256) :
    TStep C Γ (.mem bytesR :: Γ) :=
  TRun.seq (captureBytes bs hn) (TRun.revertData [.mem .raw .here])

/-- The full typed result is an actual raw halt, including empty normalization. -/
theorem bytesHalt_exact (σ : State C Γ) (bs : List UInt8) (hn : bs.length < 2 ^ 256) :
    bytesHalt bs hn σ = .error (THalt.ofData bs) := by
  unfold bytesHalt
  rw [TRun.seq]
  change (TRun.revertData [.mem .raw .here]
    (σ.allocPush (bytesObj σ.H bs hn))).map _ = _
  rw [TRun.revertData_mem (σ.allocPush (bytesObj σ.H bs hn)) .raw .here
      (σ.alloc (bytesObj σ.H bs hn)).2 rfl,
    captureBytes_read]
  rfl

/-- Computation-to-halt interface: the input is a typed image/span, not bytes
or a desired execution equation. This is not an original-source callee run. -/
theorem snapshot_halt (μ : FrameMem C Γ) (s : ByteSpan μ.capacity)
    (hn : (snapshot μ s).length < 2 ^ 256) :
    bytesHalt (snapshot μ s) hn μ.st = .error (THalt.ofData (snapshot μ s)) :=
  bytesHalt_exact _ _ _

/-- Typed bytes elements really lie below256; they are not arbitrary uints
silently treated as packed bytes. -/
theorem byteWord_bounded (b : UInt8) : (byteWord b).val.toNat < 256 := b.toNat_lt

/-- Fresh capture cannot alias any previously allocated object. -/
theorem capture_not_old (σ : State C Γ) (bs : List UInt8) (hn : bs.length < 2 ^ 256)
    {R : RefTy} (r : HRef σ.H R) :
    (σ.alloc (bytesObj σ.H bs hn)).2.id ≠ (r.wk (List.prefix_append σ.H [bytesR])).id := by
  have hr : r.id < σ.H.length := (List.getElem?_eq_some_iff.mp r.get?).1
  change σ.H.length ≠ r.id
  omega

/-- The appended identity has bytes type; a boolean array cannot name it. -/
theorem capture_not_bool (σ : State C Γ) (bs : List UInt8) (hn : bs.length < 2 ^ 256)
    (r : HRef (σ.H ++ [bytesR]) (.array (.prim .bool))) :
    r.id ≠ (σ.alloc (bytesObj σ.H bs hn)).2.id := by
  intro h
  have hr := r.get?
  change r.id = σ.H.length at h
  rw [h, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self,
    List.getElem?_cons_zero] at hr
  cases hr

end Solidity.Evm.TryByteImage
