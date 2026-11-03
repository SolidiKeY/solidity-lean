import Solidity.Backend.Transient.Code

/-! Executable nested target transient slices. These callbacks execute their
actual instruction bodies; G42 still owes CALL/account/code/context admission
and Source envLoop/enterInstance composition. Unsupported instructions remain
adapter errors, never reclassified as completed EVM reverts. -/
namespace Solidity.Backend.Transient

abbrev Write := Roadmap.Address × Word × Word

def writes : State → List Write → State
  | s,[] => s
  | s,(a,k,v)::tail => writes (write s a k v) tail

theorem writes_append (s : State) (first second : List Write) :
    writes s (first++second)=writes (writes s first) second := by
  induction first generalizing s with
  | nil => rfl
  | cons op first ih => rcases op with ⟨a,k,v⟩; exact ih _

theorem journal_writes (s : State) (ops : List Write) :
    (writes s ops).journal.length=s.journal.length+ops.length := by
  induction ops generalizing s with
  | nil => rfl
  | cons op ops ih =>
    rcases op with ⟨a,k,v⟩
    simp only [writes,ih,write,List.length_cons]
    omega

theorem undoN_succ (n : Nat) (s : State) : undoN (n+1) s=undo (undoN n s) := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => exact ih _

theorem undo_writes (s : State) (ops : List Write) : undoN ops.length (writes s ops)=s := by
  induction ops generalizing s with
  | nil => rfl
  | cons op ops ih =>
    rcases op with ⟨a,k,v⟩
    rw [List.length_cons,undoN_succ]
    change undo (undoN ops.length (writes (write s a k v) ops))=s
    rw [ih,undo_write]

theorem rollback_writes (s : State) (ops : List Write) :
    rollback s.journal.length (writes s ops)=s := by
  unfold rollback
  rw [journal_writes]
  have sub : s.journal.length+ops.length-s.journal.length=ops.length := by omega
  rw [sub,undo_writes]

/-- Arbitrary nonempty caller history is preserved by inner rollback. -/
theorem inner_rollback (s : State) (prior child : List Write) :
    rollback (writes s prior).journal.length (writes s (prior++child))=writes s prior := by
  rw [writes_append,rollback_writes]

/-- Successful descendants retain undo records: an enclosing revert restores
all owners and every caller journal entry, not just the last written cell. -/
theorem outer_rollback (s : State) (prior child later : List Write) :
    rollback s.journal.length (writes (writes (writes s prior) child) later)=s := by
  rw [←writes_append,←writes_append,rollback_writes]

def finish (entry : State) : Result → Result
  | .ok child => .ok {child with machine := entry.machine}
  | .error .unsupported dirty => .error .unsupported dirty
  | .error .symbolic dirty => .error .symbolic dirty
  | .error why dirty => .error why {rollback entry.journal.length dirty with machine := entry.machine}

/-- A nested transient-only target body starts with an empty operand stack,
shares the real owner bank and priores, and restores caller machine fields.
Owner/static context is supplied by G42, not invented here. -/
def callback (owner : Roadmap.Address) (static : Bool) (code : List Backend.Instr) (entry : State) : Result :=
  finish entry (run owner static code {entry with machine := {entry.machine with stack := []}})

theorem callback_store (owner : Roadmap.Address) (k v : Word) (entry : State) :
    callback owner false (storeCode k v) entry=.ok (write entry owner k v) := by
  simp only [callback,store_code,finish,write]

/-- This theorem uses an executed local body, not a hypothetical success oracle. -/
theorem callback_load (owner : Roadmap.Address) (static : Bool) (k : Word) (entry : State) :
    callback owner static (loadCode k) entry=.ok entry := by
  simp only [callback,load_code,finish]

/-- Empty REVERT consumes numeric offset/size. Nonempty payload handling is
explicitly refused by this slice; no payload is projected away. -/
def emptyRevert : List Backend.Instr := [pushWord ⟨0,by decide⟩,pushWord ⟨0,by decide⟩,.op .REVERT]

theorem empty_revert_run (owner : Roadmap.Address) (static : Bool) (entry : State) :
    run owner static emptyRevert entry=.error .reverted entry := by
  simp only [emptyRevert,run,push_exact]
  simp only [step,Evm.Machine.push,↓reduceIte]

theorem callback_store_revert (owner : Roadmap.Address) (k v : Word) (entry : State) :
    callback owner false (storeCode k v++emptyRevert) entry=.error .reverted entry := by
  simp only [callback,run_append,store_code,empty_revert_run,finish]
  have restored := rollback_write {entry with machine := {entry.machine with stack := []}} owner k v
  rw [show entry.journal.length=({entry with machine := {entry.machine with stack := []}} : State).journal.length from rfl,restored]

/-- A callback success does not clear the transient bank. Only endTx does. -/
theorem callback_then_reset (owner : Roadmap.Address) (k v : Word) (entry : State) :
    endTx (write entry owner k v)=endTx entry := rfl


def addressWord (a : Roadmap.Address) : Word :=
  ⟨a.val,Nat.lt_trans a.isLt (by decide)⟩

/-- Install the actual supplied Source frame's target identity fields. This is
not code/account selection or a transfer; G42 must establish those before entry. -/
def frameMachine (F : Source.Fr) (m : Evm.Machine) : Evm.Machine :=
  { m with
    self := addressWord F.this
    caller := addressWord F.sender
    callvalue := F.value
    stack := [] }

def callbackInFrame (F : Source.Fr) (code : List Backend.Instr) (entry : State) : Result :=
  finish entry (run F.this F.static code {entry with machine := frameMachine F entry.machine})

theorem frame_fields (F : Source.Fr) (m : Evm.Machine) :
    (frameMachine F m).self=addressWord F.this ∧
    (frameMachine F m).caller=addressWord F.sender ∧
    (frameMachine F m).callvalue=F.value ∧
    (frameMachine F m).store=m.store ∧ (frameMachine F m).mem=m.mem ∧
    (frameMachine F m).bal=m.bal := ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem framed_store (F : Source.Fr) (normal : F.static=false) (k v : Word) (entry : State) :
    callbackInFrame F (storeCode k v) entry=.ok (write entry F.this k v) := by
  simp only [callbackInFrame,normal,store_code,finish,write]

theorem framed_revert (F : Source.Fr) (normal : F.static=false) (k v : Word) (entry : State) :
    callbackInFrame F (storeCode k v++emptyRevert) entry=.error .reverted entry := by
  simp only [callbackInFrame,normal,run_append,store_code,empty_revert_run,finish]
  have restored := rollback_write {entry with machine := frameMachine F entry.machine} F.this k v
  rw [show entry.journal.length=({entry with machine := frameMachine F entry.machine} : State).journal.length from rfl,restored]


theorem framed_static_store (F : Source.Fr) (static : F.static=true) (k v : Word) (entry : State) :
    callbackInFrame F (storeCode k v) entry=.error .staticWrite entry := by
  simp only [callbackInFrame,static,storeCode,run,push_exact]
  simp only [step,Evm.Machine.push,↓reduceIte,finish,rollback,Nat.sub_self,undoN]

end Solidity.Backend.Transient
