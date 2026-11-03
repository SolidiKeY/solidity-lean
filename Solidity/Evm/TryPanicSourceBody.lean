import Solidity.Evm.TryPanicSourceBytes

/-! Concrete generic-length proof-only body syntax. Existing allocation,
conditional writes and raw memory revert are used without changing Stmt or its
interpreter. This is NOT original source/compiled-code association. -/
namespace Solidity.Evm.TryPanicSourceBody
open TryByteImage TryPanicProducer
variable {C : Contract}

abbrev Buffer := LTy.mem bytesR :: Input

def within (i : Fin 96) : Val C Buffer .bool :=
  .binop .lt rfl rfl
    (.simple (.lit (i.val : Int) (PrimTy.inRange_uint_of_lt (by have hi : i.val < 96 := i.isLt; omega))))
    (.simple (.local (.there sizeSlot)))

/-- Exactly the existing guarded byte assignment; short outputs skip it. -/
def put (i : Fin 96) (b : UInt8) : Stmt C Buffer Buffer :=
  .ite (within i)
    (.cons (litWrite i.val (by have hi : i.val < 96 := i.isLt; omega) b) .nil) .nil

/-- Fixed source-plan projection. The generic allocation length is read from
parameter2; the six writes cover all nonzero bytes of the proved image. -/
def contents : Prog C Buffer Buffer :=
  .cons (put ⟨0, by decide⟩ 0x4e)
  (.cons (put ⟨1, by decide⟩ 0x48)
  (.cons (put ⟨2, by decide⟩ 0x7b)
  (.cons (put ⟨3, by decide⟩ 0x71)
  (.cons (put ⟨35, by decide⟩ 0x43)
  (.cons (put ⟨95, by decide⟩ 0x80)
  (.cons (.revertData [.mem .raw .here]) .nil))))))

def allocated : Prog C Input Buffer :=
  .cons (.declMem bytesR (.user "image") (some (.newArr (.local sizeSlot) rfl)) rfl rfl)
    contents

def body : Prog C Input Input := .cons (.block allocated) .nil

/-- The condition reads the SAME parameter after the buffer allocation. -/
theorem within_eval (σ : State C Input) (o : MObj σ.H bytesR) (i : Fin 96) :
    (within i).evalT (σ.allocPush o) =
      .ok (decide (i.val < (TEnv.get sizeSlot σ.env).val.toNat)) := by
  change Except.ok (decide ((i.val : Int) < (TEnv.get sizeSlot σ.env).val)) = _
  have nonneg : 0 ≤ (TEnv.get sizeSlot σ.env).val := by
    have range : PrimTy.uint.inRange (TEnv.get sizeSlot σ.env).val = true :=
      (TEnv.get sizeSlot σ.env).property
    simp only [PrimTy.inRange, decide_eq_true_eq] at range
    exact range.1
  have eq : ((i.val : Int) < (TEnv.get sizeSlot σ.env).val) ↔
      i.val < (TEnv.get sizeSlot σ.env).val.toNat := by omega
  simp only [eq]

/-- Every short/long condition is classified from the actual parameter. The
object-length equality is a local invariant of the upcoming allocation client. -/
theorem put_run (σ : State C Input) (o : MObj σ.H bytesR) (i : Fin 96) (b : UInt8)
    (length : o.1.length = (TEnv.get sizeSlot σ.env).val.toNat) :
    (put i b).runR (σ.allocPush o) =
      .ok ⟨σ.allocPush (if i.val < o.1.length
        then MObj.setElem .dyn o i.val (byteWord b) else o), List.prefix_refl _⟩ := by
  change TRun.ite (within i) .refl
    (TRun.seq (TRun.assignMem (litLoc i.val _) (litSrc b)) TRun.nil)
    .refl TRun.nil (σ.allocPush o) = _
  rw [TRun.ite, within_eval]
  by_cases hit : i.val < o.1.length
  · have test : i.val < (TEnv.get sizeSlot σ.env).val.toNat := by rw [← length]; exact hit
    simp only [test, decide_true, boolT, if_true, hit]
    rw [TRun.seq, TRun.assignMem_litWrite σ o i.val _ b hit]
    rfl
  · have test : ¬ i.val < (TEnv.get sizeSlot σ.env).val.toNat := by rw [← length]; exact hit
    simp only [test, decide_false, boolT, if_false, hit]
    rfl

/-- Goal types for routine glue, not axioms or assumed producer instances.
No theorem below consumes an inhabitant of either type. -/
def PutThen : Prop :=
  ∀ (σ : State C Input) (o : MObj σ.H bytesR) (i : Fin 96) (b : UInt8)
    (k : TStep C Buffer Buffer),
    o.1.length = (TEnv.get sizeSlot σ.env).val.toNat →
    TRun.seq (put i b).runR k (σ.allocPush o) =
      k (σ.allocPush (if i.val < o.1.length
        then MObj.setElem .dyn o i.val (byteWord b) else o))

theorem input_bound (σ : State C Input) :
    (TEnv.get sizeSlot σ.env).val.toNat < 2^256 := by
  have range : PrimTy.uint.inRange (TEnv.get sizeSlot σ.env).val = true :=
    (TEnv.get sizeSlot σ.env).property
  simp only [PrimTy.inRange, decide_eq_true_eq] at range
  omega

def AllocateRun : Prop :=
  ∀ σ : State C Input,
    TRun.declMem bytesR (some (.newArr (.local sizeSlot) rfl)) rfl σ =
      .ok ⟨σ.allocPush (zerosObj σ.H (TEnv.get sizeSlot σ.env).val.toNat (input_bound σ)),
        List.prefix_append _ _⟩

end Solidity.Evm.TryPanicSourceBody
