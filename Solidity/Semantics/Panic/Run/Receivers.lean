import Solidity.Semantics.Panic.Run.Updates

namespace Solidity.Semantics.Panic.Run

variable {C : Contract} {Γ : Ctx}

def receiverOp {E : Ty} (op : ReceiverOp C Γ E) (b : SPath C Γ (.array E)) : Step C Γ Γ :=
  match op with
  | .push v _ => push b v
  | .pop => pop b

/-- A storage-returning receiver runs once, before its array operation reads
the source. The temporary return alias is dropped afterwards. -/
def callReceiver {ps Γf : Ctx} {E : Ty} (args : Args C Γ ps) (r : Var)
    (h : Ext ([.alias (.array E)] ++ ps) Γf)
    (body : Step C ([.alias (.array E)] ++ ps) Γf) (op : ReceiverOp C Γ E) :
    Step C Γ Γ := fun σ => do
  let o ← call args (.storage (.array E) r) h body σ
  let o' ← receiverOp (op.wk (.drop .refl)) (.alias .here) o.st
  pure ⟨o'.st.drop (.push .refl), o.ext.trans o'.ext⟩

/-- Complete a deferred operand at its already validated receiver; its temporary
locals end after the source has been read and copied. -/
def pushAfterPrefix {Γv : Ctx} {E : Ty} (h : Ext Γ Γv) (code : Step C Γ Γv)
    (value : Src C Γv E) (ref : SRef C (.ref (.array E))) : Step C Γ Γ := fun σ => do
  let a ← code σ
  let v ← source a.st value
  if a.st.storage.full ref then .error .exhausted else
  let st ← ofOpt (a.st.storage.push ref fun _ => some v.strip)
  pure ⟨(a.st.withStorage st).drop h, a.ext⟩

/-- Validate a getter result before any deferred operand effect runs. -/
def afterReceiverPrefix {Γv : Ctx} {E : Ty} (he : Ext Γ Γv) (code : Step C Γ Γv)
    (value : Src C Γv E) : Step C (.alias (.array E) :: Γ) Γ := fun σ => do
  let ref ← path σ (.alias .here)
  pushAfterPrefix he code value ref (σ.drop (.push .refl))

/-- `f().push(e)` with effects in `e`: getter once, validation before the
operand prefix, then the source snapshot and push at that fixed receiver. -/
def callReceiverPush {ps Γf Γv : Ctx} {E : Ty} (args : Args C Γ ps) (r : Var)
    (hb : Ext ([.alias (.array E)] ++ ps) Γf)
    (body : Step C ([.alias (.array E)] ++ ps) Γf)
    (he : Ext Γ Γv) (code : Step C Γ Γv) (value : Src C Γv E) : Step C Γ Γ := fun σ => do
  let a ← call args (.storage (.array E) r) hb body σ
  (afterReceiverPrefix he code value a.st).map fun b => ⟨b.st, a.ext.trans b.ext⟩

/-- A failed getter is propagated before the receiver operation. -/
theorem callReceiver_error {ps Γf : Ctx} {E : Ty} (args : Args C Γ ps) (r : Var)
    (h : Ext ([.alias (.array E)] ++ ps) Γf)
    (body : Step C ([.alias (.array E)] ++ ps) Γf) (op : ReceiverOp C Γ E)
    (σ : State C Γ) (halt : Halt Raised)
    (failed : call args (.storage (.array E) r) h body σ = .error halt) :
    callReceiver args r h body op σ = .error halt := by
  simp only [callReceiver, failed]
  rfl

/-- Deferred operand effects stop before its source and the final push. -/
theorem pushAfterPrefix_error {Γv : Ctx} {E : Ty} (h : Ext Γ Γv)
    (code : Step C Γ Γv) (value : Src C Γv E) (ref : SRef C (.ref (.array E)))
    (σ : State C Γ) (halt : Halt Raised) (failed : code σ = .error halt) :
    pushAfterPrefix h code value ref σ = .error halt := by
  simp only [pushAfterPrefix, failed]
  rfl

/-- Invalid receiver aliases stop before any deferred operand effects. -/
theorem afterReceiverPrefix_error {Γv : Ctx} {E : Ty} (h : Ext Γ Γv)
    (code : Step C Γ Γv) (value : Src C Γv E)
    (σ : State C (.alias (.array E) :: Γ)) (halt : Halt Raised)
    (failed : path σ (.alias .here) = .error halt) :
    afterReceiverPrefix h code value σ = .error halt := by
  simp only [afterReceiverPrefix, failed]
  rfl

end Solidity.Semantics.Panic.Run
