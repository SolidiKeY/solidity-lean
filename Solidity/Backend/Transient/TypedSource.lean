import Solidity.Backend.Transient.Instructions
import Solidity.Source.Hoare

/-! G39 typed bool-cell Source relation. BoolSlot is a selected compiler port,
not a second layout or universal allocation theorem. Source execution is the
published writeAt/readAt and journal. Target words stay distinct from persistent
WordStore; arbitrary dirty TSTORE words are not claimed to represent a bool. -/
namespace Solidity.Backend.Transient

structure BoolSlot (E : Source.Env) where
  path : Source.SPath
  typed : E.cellTy path=.bool
  transient : E.transientRoot path=true
  key : Word

def boolWord (b : Bool) : Word := ⟨if b then 1 else 0,by cases b <;> decide⟩
def boolValue {E : Source.Env} (slot : BoolSlot E) (b : Bool) :
    Source.Val E.layout (E.cellTy slot.path) := slot.typed.symm ▸ .bool b

def Represents {E : Source.Env} {Γ : Source.RCtx} (slot : BoolSlot E)
    (owner : Roadmap.Address) (s : Source.EMState E Γ) (t : State) : Prop :=
  ∃ b, (s.2.ex.transient.cells owner).read slot.path=some (boolValue slot b) ∧
    t.bank owner slot.key=boolWord b

def sourceWrite {E : Source.Env} (slot : BoolSlot E) (owner : Roadmap.Address)
    (b : Bool) (s : Source.St E) : Source.St E :=
  {s with ex := s.ex.apply (.transient owner fun cells => cells.write slot.path (boolValue slot b))}

theorem write_actual {E : Source.Env} {Γ : Source.RCtx} (slot : BoolSlot E)
    (F : Source.Fr) (normal : F.static=false) (b : Bool) (s : Source.EMState E Γ) :
    (Source.writeAt F slot.path (.bool b)).run s=(.ok (),(s.1,sourceWrite slot F.this b s.2)) := by
  simp only [Source.writeAt,dif_pos slot.typed.symm,Source.setCell,slot.transient,
    ↓reduceIte,Source.applyOp,normal,Bool.false_eq_true,Source.EM.modSt]
  rfl

theorem write_static {E : Source.Env} {Γ : Source.RCtx} (slot : BoolSlot E)
    (F : Source.Fr) (static : F.static=true) (b : Bool) (s : Source.EMState E Γ) :
    (Source.writeAt F slot.path (.bool b)).run s=(.error (.revert []),s) := by
  simp only [Source.writeAt,dif_pos slot.typed.symm,Source.setCell,slot.transient,
    ↓reduceIte,Source.applyOp,static,Source.EM.halt]
  rfl

theorem write_represents {E : Source.Env} {Γ : Source.RCtx} (slot : BoolSlot E)
    (owner : Roadmap.Address) (b : Bool) (s : Source.EMState E Γ) (t : State) :
    Represents slot owner (s.1,sourceWrite slot owner b s.2)
      (write t owner slot.key (boolWord b)) := by
  refine ⟨b,?_,put_same _ _ _ _⟩
  change ((s.2.ex.transient.set owner ((s.2.ex.transient.cells owner).write slot.path (boolValue slot b))).cells owner).read slot.path=_
  have same : (s.2.ex.transient.set owner ((s.2.ex.transient.cells owner).write slot.path (boolValue slot b))).cells owner=
      (s.2.ex.transient.cells owner).write slot.path (boolValue slot b) := by
    simp only [Source.Transient.set,dif_pos]
  rw [same,Source.Storage.write_read]

/-- Full actual Source result and actual target instruction, not an assumed
callee outcome. Selected-cell representation is derived, not assumed. -/
theorem write_correspondence {E : Source.Env} {Γ : Source.RCtx} (slot : BoolSlot E)
    (F : Source.Fr) (normal : F.static=false) (b : Bool) (s : Source.EMState E Γ)
    (t : State) (tail : List Evm.Word)
    (stack : t.machine.stack=.val slot.key::.val (boolWord b)::tail) :
    (Source.writeAt F slot.path (.bool b)).run s=(.ok (),(s.1,sourceWrite slot F.this b s.2)) ∧
    step F.this false (.op .TSTORE) t=
      .ok {write t F.this slot.key (boolWord b) with machine := {t.machine with stack := tail}} ∧
    Represents slot F.this (s.1,sourceWrite slot F.this b s.2)
      {write t F.this slot.key (boolWord b) with machine := {t.machine with stack := tail}} :=
  ⟨write_actual slot F normal b s,tstore F.this t slot.key (boolWord b) tail stack,
    write_represents slot F.this b s t⟩

theorem source_write_fields {E : Source.Env} (slot : BoolSlot E) (a : Roadmap.Address)
    (b : Bool) (s : Source.St E) :
    (sourceWrite slot a b s).ex.world=s.ex.world ∧
    (sourceWrite slot a b s).heap=s.heap ∧ (sourceWrite slot a b s).events=s.events ∧
    (sourceWrite slot a b s).logs=s.logs ∧ (sourceWrite slot a b s).fnLocals=s.fnLocals := ⟨rfl,rfl,rfl,rfl,rfl⟩

theorem end_represents {E : Source.Env} {Γ : Source.RCtx} (slot : BoolSlot E)
    (owner : Roadmap.Address) (s : Source.EMState E Γ) (t : State) :
    Represents slot owner (s.1,{s.2 with ex := s.2.ex.endTx}) (endTx t) := by
  refine ⟨false,?_,rfl⟩
  change Source.Val.default E.layout (E.cellTy slot.path)=some (boolValue slot false)
  have default (ty : Source.STy) (h : ty=.bool) :
      Source.Val.default E.layout ty=some (h.symm ▸ (Source.Val.bool false : Source.Val E.layout .bool)) := by
    cases h
    rfl
  exact default _ slot.typed


theorem read_actual {E : Source.Env} {Γ : Source.RCtx} (slot : BoolSlot E)
    (F : Source.Fr) (s : Source.EMState E Γ) (b : Bool)
    (found : (s.2.ex.transient.cells F.this).read slot.path=some (boolValue slot b)) :
    (Source.readAt F slot.path .bool).run s=(.ok (.bool b),s) := by
  have read : (Source.readCell F slot.path : Source.EM E Γ _).run s=(.ok (boolValue slot b),s) := by
    simp only [Source.readCell,Source.Hoare.run_bind]
    rw [show (Source.EM.st (E:=E) (Γ:=Γ)).run s=(.ok s.2,s) from rfl]
    simp only [slot.transient,↓reduceIte,found]
    rfl
  have cancel (ty : Source.STy) (h : ty=.bool) :
      h ▸ (h.symm ▸ (Source.Val.bool b : Source.Val E.layout .bool))=Source.Val.bool b := by
    cases h
    rfl
  simp only [Source.readAt,Source.Hoare.run_bind,read,dif_pos slot.typed]
  change ((Except.ok (slot.typed ▸ boolValue slot b) : Source.R (Source.Val E.layout .bool)),s)=
    (Except.ok (Source.Val.bool b),s)
  exact congrArg (fun value : Source.Val E.layout .bool =>
    ((Except.ok value : Source.R (Source.Val E.layout .bool)),s)) (cancel _ slot.typed)

theorem read_correspondence {E : Source.Env} {Γ : Source.RCtx} (slot : BoolSlot E)
    (F : Source.Fr) (s : Source.EMState E Γ) (t : State)
    (relation : Represents slot F.this s t) (tail : List Evm.Word)
    (stack : t.machine.stack=.val slot.key::tail) :
    ∃ b, (Source.readAt F slot.path .bool).run s=(.ok (.bool b),s) ∧
      step F.this F.static (.op .TLOAD) t=
        .ok {t with machine := {t.machine with stack := .val (boolWord b)::tail}} := by
  obtain ⟨b,found,word⟩ := relation
  refine ⟨b,read_actual slot F s b found,?_⟩
  rw [tload F.this F.static t slot.key tail stack,word]


theorem source_other_owner {E : Source.Env} (slot : BoolSlot E) (a other : Roadmap.Address)
    (different : other≠a) (b : Bool) (s : Source.St E) :
    (sourceWrite slot a b s).ex.transient.cells other=s.ex.transient.cells other := by
  simp only [sourceWrite,Source.ExecState.apply,Source.Transient.set,dif_neg different]

end Solidity.Backend.Transient
