import Solidity.Backend.Aggregates.G18ScalarMapping
import Solidity.Source.Eval

/-! Populated integer-valued mapping fixtures using actual declared Source
paths, canonical Boolean key bytes and the published structured copy driver.
These fixtures do not certify a Source compilation unit or physical hashing. -/
namespace Solidity.Backend.Aggregates.ScalarMapping.Controls
open Lowering.V07

/-- Actual key bytes used by Source.keyStep for a Boolean value. -/
def keyBytes (b : Bool) : Roadmap.Bytes := Source.wordBytes (Source.toWord (if b then 1 else 0))
def path (b : Bool) : Source.SPath := ⟨⟨none,"entries"⟩,[.key (keyBytes b)]⟩

def declaration (t : Source.IntTy) : Source.Decl :=
  ⟨.stateVar,"entries",none,true,
    .stateVar (.mapping (.elem .bool (by decide)) none
      (.elem (.int t.signed t.bits t.valid)) none) none none none false "entries" .none⟩
def env (t : Source.IntTy) : Source.Env := ⟨[declaration t]⟩
def cellTypes (t : Source.IntTy) (p : Source.SPath) : Source.STy := ((env t).pathTy p).getD .bool

def source (t : Source.IntTy) (a b : Int) (ha : t.lo ≤ a ∧ a ≤ t.hi) (hb : t.lo ≤ b ∧ b ≤ t.hi) :
    Source.Storage (env t).layout (cellTypes t) :=
  ((Source.Storage.empty.write (path true) (.int a ha)).write (path false) (.int b hb))
def entries (t : Source.IntTy) (a b : Int) (ha : t.lo ≤ a ∧ a ≤ t.hi) (hb : t.lo ≤ b ∧ b ≤ t.hi) :
    SMap .bool (.prim (integerPrim t)) :=
  .cons true (.prim (integerValue t a ha)) (.cons false (.prim (integerValue t b hb)) .nil)
def fallback (t : Source.IntTy) (b : Int) (hb : t.lo ≤ b ∧ b ≤ t.hi) : SVal (.prim (integerPrim t)) :=
  .prim (integerValue t b hb)
def value (t : Source.IntTy) (a b : Int) (ha : t.lo ≤ a ∧ a ≤ t.hi) (hb : t.lo ≤ b ∧ b ≤ t.hi) :
    SVal (MapTy .bool t) := .map (entries t a b ha hb) (fallback t b hb)

def base : Evm.Slot := .root 0

def symbolic (t : Source.IntTy) (a b : Int) (ha : t.lo ≤ a ∧ a ≤ t.hi) (hb : t.lo ≤ b ∧ b ≤ t.hi) :
    Solidity.Storage.Representation.Store :=
  fun l => if l = location (K := .bool) (Solidity.Storage.ofSlot base) true
    then PrimTy.toWord (integerValue t a ha) else PrimTy.toWord (integerValue t b hb)

def target (t : Source.IntTy) (a b : Int) (ha : t.lo ≤ a ∧ a ≤ t.hi) (hb : t.lo ≤ b ∧ b ≤ t.hi) :
    Evm.Machine :=
  {Evm.Machine.init (fun addr => addr.val+17) ⟨41,by decide⟩ with
    store := ⟨fun s => StorageOps.TargetOperations.encodeWord
      (symbolic t a b ha hb (Solidity.Storage.ofSlot s))⟩
    stack := [.val ⟨77,by decide⟩,.slot (.root 99)]
    mem := fun i => if i=17 then .val ⟨42,by decide⟩ else .val ⟨99,by decide⟩
    bal₀ := fun addr => addr.val+29
    caller := ⟨37,by decide⟩
    callvalue := ⟨5,by decide⟩
    timestamp := ⟨101,by decide⟩
    accepts := fun addr _ => addr.val != 13}

theorem typed (t : Source.IntTy) (b : Bool) : cellTypes t (path b) = .int t := by
  rfl

theorem path_injective : Function.Injective path := by
  intro a b
  cases a <;> cases b <;> decide +kernel

/-- Both keys are populated; all source widths and numeric values remain
parameters, so the fixture supports unsigned and signed applications. -/
theorem source_cells (t : Source.IntTy) (a b : Int)
    (ha : t.lo ≤ a ∧ a ≤ t.hi) (hb : t.lo ≤ b ∧ b ≤ t.hi) :
    Cells t (source t a b ha hb) (value t a b ha hb) path (typed t) := by
  intro key
  cases key
  · refine ⟨b,hb,?_,?_⟩
    · exact Source.Storage.write_read _ _ _
    · simp only [value,entries,fallback,SVal.find_key,SVal.find_nil,SMap.toList_cons,
        SMap.toList_nil,Semantics.lookupBy,↓reduceIte] <;> rfl
  · refine ⟨a,ha,?_,?_⟩
    · rw [source,Source.Storage.write_other _ (by decide +kernel),Source.Storage.write_read]
    · simp only [value,entries,fallback,SVal.find_key,SVal.find_nil,SMap.toList_cons,
        SMap.toList_nil,Semantics.lookupBy,↓reduceIte] <;> rfl

theorem represented (t : Source.IntTy) (a b : Int)
    (ha : t.lo ≤ a ∧ a ≤ t.hi) (hb : t.lo ≤ b ∧ b ≤ t.hi) :
    Solidity.Storage.Representation.ValueRep (value t a b ha hb) (.map .word)
      (Solidity.Storage.ofSlot base) (symbolic t a b ha hb) := by
  unfold value entries fallback
  refine Solidity.Storage.Representation.ValueRep.mapping _ _ _ _ _ (.scalar _) ?_
  intro key
  cases key <;> simp only [SMap.toList_cons,SMap.toList_nil,Semantics.lookupBy,↓reduceIte,Option.getD_some]
  · apply Solidity.Storage.Representation.ValueRep.scalar
    exact if_neg (by decide +kernel)
  · apply Solidity.Storage.Representation.ValueRep.scalar
    exact if_pos rfl

theorem target_initial (t : Source.IntTy) (a b : Int)
    (ha : t.lo ≤ a ∧ a ≤ t.hi) (hb : t.lo ≤ b ∧ b ≤ t.hi) (key : Bool) :
    (target t a b ha hb).store.cells (slot (K := .bool) base key) =
      StorageOps.TargetOperations.encodeWord
        (symbolic t a b ha hb (location (K := .bool) (Solidity.Storage.ofSlot base) key)) := by
  rfl

/-- Canonical key construction agrees with the actual Source helper; it is
not a statement about evaluation of an enclosing expression. -/
theorem key_step (E : Source.Env) (Γ : Source.RCtx) (F : Source.Fr)
    (n : Nat) (b : Bool) (y : Source.Locals E.layout Γ × Source.St E) :
    (Source.keyStep (E := E) F n (.val (.bool b))).run y = (.ok (.key (keyBytes b)),y) := by
  cases b <;> rfl

/-- The enclosing Source interpreter still times out at zero horizon, even
for a Boolean literal. Timeout is not divergence and is not erased here. -/
theorem zero_horizon (E : Source.Env) (G : Source.Glob E) (Γ : Source.RCtx)
    (F : Source.Fr) (y : Source.Locals E.layout Γ × Source.St E) :
    (Source.evalE G F 0 (.bool true : Source.RExpr E Γ .bool)).run y = (.error .timeout,y) := by
  rfl

/-- All actual input premises are discharged. The copied value is fixed to
its REAL initial Source read, not an arbitrary existential target payload. -/
theorem copied (t : Source.IntTy) (a b : Int)
    (ha : t.lo ≤ a ∧ a ≤ t.hi) (hb : t.lo ≤ b ∧ b ≤ t.hi) :
    ∃ after, CopyPost t (source t a b ha hb) (value t a b ha hb) after path (typed t)
      true false a ha base (symbolic t a b ha hb) (target t a b ha hb) := by
  obtain ⟨n,range,after,read,post⟩ := copy t (source t a b ha hb) (entries t a b ha hb)
    (fallback t b hb) path (typed t) path_injective (source_cells t a b ha hb) base
    (symbolic t a b ha hb) (represented t a b ha hb) (target t a b ha hb)
    (target_initial t a b ha hb) true false
  have captured : some a = some n := by
    have observed := congrArg (fun x => x.bind Source.Val.key) read
    simpa only [source,Source.Storage.write_other (p := path false) (q := path true) _
      (by decide +kernel),Source.Storage.write_read,Option.bind_some,Source.Val.key] using observed
  have same := Option.some.inj captured
  subst n
  exact ⟨after,post⟩

/-- Fixture parameters are bounded Source integers, not a new execution state. -/
structure Sample where
  ty : Source.IntTy
  a : Int
  b : Int
  ha : ty.lo ≤ a ∧ a ≤ ty.hi
  hb : ty.lo ≤ b ∧ b ≤ ty.hi

def unsigned : Sample := ⟨.u8,7,11,by decide,by decide⟩
def signed : Sample := ⟨⟨true,8,by decide⟩,-1,11,by decide,by decide⟩

def beforeSource (c : Sample) := source c.ty c.a c.b c.ha c.hb
def afterSource (c : Sample) : Source.Storage (env c.ty).layout (cellTypes c.ty) :=
  (beforeSource c).write (path false) (.int c.a c.ha)
def beforeValue (c : Sample) := value c.ty c.a c.b c.ha c.hb
/-- The exact existing mapping_source_save output. -/
def afterValue (c : Sample) : SVal (MapTy .bool c.ty) :=
  .map (.ofList (Semantics.setBy false (.prim (integerValue c.ty c.a c.ha))
    (entries c.ty c.a c.b c.ha c.hb).toList)) (fallback c.ty c.b c.hb)
def beforeStore (c : Sample) := symbolic c.ty c.a c.b c.ha c.hb
def afterStore (c : Sample) := Solidity.Storage.Representation.write (beforeStore c)
  (location (K := .bool) (Solidity.Storage.ofSlot base) false) (PrimTy.toWord (integerValue c.ty c.a c.ha))
def beforeTarget (c : Sample) := target c.ty c.a c.b c.ha c.hb
def afterTarget (c : Sample) := writtenMachine (K := .bool) (beforeTarget c) base false (PrimTy.toWord (integerValue c.ty c.a c.ha))
def code : List Evm.Instr :=
  StorageOps.TargetOperations.copyCode (slot (K := .bool) base false) (slot (K := .bool) base true)

def sourceView (c : Sample) (s : Source.Storage (env c.ty).layout (cellTypes c.ty)) : List (Option Int) :=
  [(s.read (path true)).bind Source.Val.key,(s.read (path false)).bind Source.Val.key]
def valueView (c : Sample) (v : SVal (MapTy .bool c.ty)) : List (Option Int) :=
  [(v.find (.key true .nil)).bind (fun | .prim x => PrimTy.num? x),
   (v.find (.key false .nil)).bind (fun | .prim x => PrimTy.num? x)]
def storeView (st : Solidity.Storage.Representation.Store) : List Int :=
  [(st (location (K := .bool) (Solidity.Storage.ofSlot base) true)).val,
   (st (location (K := .bool) (Solidity.Storage.ofSlot base) false)).val,(st (.root 99)).val]
def targetView (m : Evm.Machine) : List Nat :=
  [(m.store.cells (slot (K := .bool) base true)).val,
   (m.store.cells (slot (K := .bool) base false)).val,(m.store.cells (.root 99)).val]

/-- A fully inhabited copy certificate at the exact producer output value. -/
theorem certificate (c : Sample) :
    CopyPost c.ty (beforeSource c) (beforeValue c) (afterValue c) path (typed c.ty)
      true false c.a c.ha base (beforeStore c) (beforeTarget c) := by
  obtain ⟨after,post⟩ := copied c.ty c.a c.b c.ha c.hb
  have saved := post.1.1
  have expected := Solidity.Storage.Representation.mapping_source_save
    (entries c.ty c.a c.b c.ha c.hb) (fallback c.ty c.b c.hb)
    (.prim (integerValue c.ty c.a c.ha)) false
  have same : after = afterValue c := Option.some.inj (saved.symm.trans expected)
  subst after
  exact post

/-- All target fields except storage are equal, as FUNCTIONS too, not merely
at the chosen finite observations. No Source/world frame identity is inferred. -/
theorem complete_target_frame (c : Sample) :
    {afterTarget c with store := (beforeTarget c).store} = beforeTarget c := by
  rfl

/-- COMPLETE declared vectors in order: Source, intrinsic value, symbolic
word store, target word store; both before and after. Root99 is untouched.
Signed Source -1 remains -1 in typed values and becomes the exact padded word. -/
theorem ordered :
    ((sourceView unsigned (beforeSource unsigned),sourceView unsigned (afterSource unsigned),
      valueView unsigned (beforeValue unsigned),valueView unsigned (afterValue unsigned),
      storeView (beforeStore unsigned),storeView (afterStore unsigned),
      targetView (beforeTarget unsigned),targetView (afterTarget unsigned)) =
      ([some 7,some 11],[some 7,some 7],[some 7,some 11],[some 7,some 7],
       [7,11,11],[7,7,11],[7,11,11],[7,7,11])) ∧
    ((sourceView signed (beforeSource signed),sourceView signed (afterSource signed),
      valueView signed (beforeValue signed),valueView signed (afterValue signed),
      storeView (beforeStore signed),storeView (afterStore signed),
      targetView (beforeTarget signed),targetView (afterTarget signed)) =
      ([some (-1),some 11],[some (-1),some (-1)],[some (-1),some 11],[some (-1),some (-1)],
       [2^256-1,11,11],[2^256-1,2^256-1,11],[2^256-1,11,11],[2^256-1,2^256-1,11])) := by
  constructor <;> simp only [Prod.mk.injEq] <;> decide +kernel

/-- Distinguish all existing structured target outcome tags. This is only a
finite control observer; certificate retains the full Out.ok machine. -/
def runView : Evm.Out → Nat × List Nat
  | .ok m pc => (0,pc::targetView m)
  | .revert => (1,[])
  | .fault => (2,[])

def wrongTarget := writtenMachine (K := .bool) (beforeTarget unsigned) base true ⟨99,by decide⟩
def wrongCode := StorageOps.TargetOperations.copyCode
  (slot (K := .bool) base true) (slot (K := .bool) base false)

def equalValues : Sample := ⟨.u8,7,7,by decide,by decide⟩
def collapsedSourceAfter : Source.Storage (env .u8).layout (cellTypes .u8) :=
  (beforeSource equalValues).write (path true) (.int 8 (by decide))
def collapsedValueAfter : SVal (MapTy .bool .u8) :=
  .map (.ofList (Semantics.setBy false (.prim (integerValue .u8 8 (by decide)))
    (entries .u8 7 7 (by decide) (by decide)).toList)) (fallback .u8 7 (by decide))
def collapsedView (s : Source.Storage (env .u8).layout (cellTypes .u8)) : List (Option Int) :=
  [(s.read (path true)).bind Source.Val.key,(s.read (path true)).bind Source.Val.key]

/-- Actual executions reject wrong slot order and stale target state. Distinct
revert/fault tags are retained. Equal initial observations with collapsed Source
paths become unequal after the write, exhibiting why injectivity is necessary. -/
theorem negative_controls :
  (runView (Evm.run code (beforeTarget unsigned)) = (0,[0,7,7,11])) ∧ (runView (Evm.run wrongCode (beforeTarget unsigned)) = (0,[0,11,11,11])) ∧ (runView (Evm.run code wrongTarget) = (0,[0,99,99,11])) ∧ (runView (Evm.run [.push (.val ⟨0,by decide⟩),.sload] (beforeTarget unsigned)) = (2,[])) ∧ (runView (Evm.run [.revert] (beforeTarget unsigned)) = (1,[])) ∧ (sourceView unsigned (afterSource unsigned) ≠ [some 7,some 11]) ∧ (targetView (afterTarget signed) ≠ [0,0,11]) ∧ ((targetView (beforeTarget unsigned),targetView (afterTarget unsigned)) ≠ ([7,11,11],[11,11,11])) ∧ (collapsedView (beforeSource equalValues) = valueView equalValues (beforeValue equalValues)) ∧ ((collapsedView collapsedSourceAfter,valueView equalValues collapsedValueAfter) = ([some 8,some 8],[some 7,some 8])) ∧ ((fun _ : Bool => path true) false = (fun _ : Bool => path true) true ∧ (false : Bool) ≠ true) ∧ (¬(Source.IntTy.u8.lo ≤ (-1 : Int) ∧ (-1 : Int) ≤ Source.IntTy.u8.hi)) ∧ (¬(Source.IntTy.u8.lo ≤ (256 : Int) ∧ (256 : Int) ≤ Source.IntTy.u8.hi)) := by
  simp only [Prod.mk.injEq]
  decide +kernel

/-- Reject a wrong ENTIRE target result by the NEW instantiated certificate,
not by assuming a target run or selecting just matching storage cells. -/
theorem wrong_frame :
    Evm.run code (beforeTarget unsigned) ≠ .ok {afterTarget unsigned with stack := []} 0 := by
  have actual := (certificate unsigned).2.1
  intro wrong
  have equal := Evm.Out.ok.inj (actual.symm.trans wrong)
  have stacks := congrArg Evm.Machine.stack equal.1
  change [Evm.Word.val ⟨77,by decide⟩,Evm.Word.slot (.root 99)] = [] at stacks
  cases stacks

/-- info: 'Solidity.Backend.Aggregates.ScalarMapping.Controls.typed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms typed

/-- info: 'Solidity.Backend.Aggregates.ScalarMapping.Controls.path_injective' does not depend on any axioms -/
#guard_msgs in #print axioms path_injective

/-- info: 'Solidity.Backend.Aggregates.ScalarMapping.Controls.source_cells' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms source_cells

/-- info: 'Solidity.Backend.Aggregates.ScalarMapping.Controls.represented' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms represented

/-- info: 'Solidity.Backend.Aggregates.ScalarMapping.Controls.target_initial' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms target_initial

/-- info: 'Solidity.Backend.Aggregates.ScalarMapping.Controls.key_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms key_step

/-- info: 'Solidity.Backend.Aggregates.ScalarMapping.Controls.zero_horizon' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms zero_horizon

/-- info: 'Solidity.Backend.Aggregates.ScalarMapping.Controls.copied' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms copied

/-- info: 'Solidity.Backend.Aggregates.ScalarMapping.Controls.certificate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms certificate

/-- info: 'Solidity.Backend.Aggregates.ScalarMapping.Controls.complete_target_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms complete_target_frame

/-- info: 'Solidity.Backend.Aggregates.ScalarMapping.Controls.ordered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ordered

/-- info: 'Solidity.Backend.Aggregates.ScalarMapping.Controls.negative_controls' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms negative_controls

/-- info: 'Solidity.Backend.Aggregates.ScalarMapping.Controls.wrong_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms wrong_frame
end Solidity.Backend.Aggregates.ScalarMapping.Controls
