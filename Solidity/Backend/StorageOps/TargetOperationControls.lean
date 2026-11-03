import Solidity.Backend.StorageOps.TargetOperations

/-! Captured typed-path operation adapters into the unchanged symbolic EVM.
Actual runtime SLOAD distinguishes changed inputs; malformed source reads and
wrong target tags show precisely which checks/expansion remain unproved. -/
namespace Solidity.Backend.StorageOps.TargetOperationControls
open TypeGraph Solidity.Storage Solidity.Storage.Representation Solidity.Storage.Representation.Graph
open TargetOperations
private def graph : Schema 0 where
  origin := "v10-target-operation-controls"
  declId := fun i => nomatch i
  declId_injective := by intro i; exact Fin.elim0 i
  name := fun i => nomatch i
  fields := fun i => nomatch i
  rank := fun i => nomatch i
  nonempty := by intro i; exact Fin.elim0 i
  distinct := by intro i; exact Fin.elim0 i
  guarded := by intro i; exact Fin.elim0 i
private def ix (i : Fin 4) : Index := ⟨i.val,by have bound := i.isLt; omega⟩
private abbrev Elem : TypeGraph.Ty 0 := .array (.prim .bool)
private abbrev Root : TypeGraph.Ty 0 := .mapping .bool Elem
private def oldA : Value graph Elem := .array ⟨3,by decide⟩ ⟨2,by decide⟩ (by decide)
  (fun i => .present (.prim (decide (i.val ≠ 0))))
private def oldB : Value graph Elem := .array ⟨1,by decide⟩ ⟨1,by decide⟩ (by decide) (fun _ => .present (.prim false))
private def root : Value graph Root := .mapping (fun key => .present (if key = true then oldB else oldA))
private def ap : TypeGraph.Path graph Root Elem := .cons (.key false) .nil
private def bp : TypeGraph.Path graph Root Elem := .cons (.key true) .nil
private def elem (p : TypeGraph.Path graph Root Elem) (i : Fin 4) : TypeGraph.Path graph Root (.prim .bool) :=
  p.append (.cons (.index (ix i)) .nil)
private def src := elem ap 1
private def dst := elem bp 0
private def shadow := elem ap 2
private def outside := elem ap 0
private def bad := elem bp 1
private def queries : List (Query graph Root) := [.word shadow,.word outside,.word bad]
private def result := (recursiveCopyAt root dst src).getD root
private def base : Solidity.Storage.Loc := .root 0
private def a : Solidity.Storage.Loc := .hash 0 base 0
private def b : Solidity.Storage.Loc := .hash 1 base 0
private def sl : Solidity.Storage.Loc := .data a 1
private def dl : Solidity.Storage.Loc := .data b 0
private def hl : Solidity.Storage.Loc := .data a 2
private def ol : Solidity.Storage.Loc := .data a 0
private def bl : Solidity.Storage.Loc := .data b 1
private def zero : Semantics.Word := PrimTy.toWord (p := .bool) false
private def one : Semantics.Word := PrimTy.toWord (p := .bool) true
private def two : Semantics.Word := lengthWord 2 (by decide)
private def seven : Semantics.Word := ⟨7,by decide⟩
private def hash (p : Solidity.Storage.Pre) : Nat :=
  if p = .entry 0 0 then 4 else if p = .entry 1 0 then 8 else if p = .data 4 then 16 else if p = .data 8 then 24 else 0
private def preimages : List Solidity.Storage.Pre := [.entry 0 0,.entry 1 0,.data 4,.data 8]
private def locations : List Solidity.Storage.Loc := [sl,dl,hl,ol,bl,a,b]
private def store : Store := fun l => if l = a then two else if l = .root 9 then seven else
  if l = b ∨ l = sl ∨ l = hl ∨ l = bl then one else zero
private def numeric : WordStore := fun n => if n = 4 then two else if n = 9 then seven else
  if n = 8 ∨ n = 17 ∨ n = 18 ∨ n = 25 ∨ n = 40 ∨ n = 44 then one else zero
private def target : Evm.Machine :=
  { Evm.Machine.init (fun addr => if addr.val = 0 then 100 else 50) with
    stack := [.val (encodeWord seven),.slot (.root 9)]
    store := ⟨fun slot => encodeWord (store (Solidity.Storage.ofSlot slot))⟩
    mem := fun n => if n = 3 then .val (encodeWord one) else .slot (.root n)
    bal₀ := fun _ => 200
    caller := ⟨9,by decide⟩
    callvalue := ⟨4,by decide⟩
    timestamp := ⟨23,by decide⟩ }
private def fitBase : KeysFit base := True.intro
private theorem fitting : ∀ l ∈ locations, KeysFit l := by
  intro l member
  simp only [locations,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [KeysFit,Solidity.Storage.KeysBelow,sl,dl,hl,ol,bl,a,b,base] <;> decide
private def ds := toSlot dl (path_keysFit dst base fitBase)
private def ss := toSlot sl (path_keysFit src base fitBase)
private def hs := toSlot hl (path_keysFit shadow base fitBase)
private def bs := toSlot bl (path_keysFit bad base fitBase)
private def afterStore := Representation.write store dl one
private def afterNumeric := RepresentedOperations.numericCopy numeric (dl.word 64 hash) (sl.word 64 hash)
private def afterTarget : Evm.Machine := { target with store := Evm.WordStore.write target.store ds (encodeWord one).val }
private theorem run : FiniteRun 64 4 1 hash preimages locations := by
  constructor
  · intro p; simp only [hash]; split <;> (first | decide | (split <;> (first | decide | (split <;> (first | decide | (split <;> decide))))))
  · decide
  · decide
  · decide
  · intro l member
    simp only [locations,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [sl,dl,hl,ol,bl,a,b,base,Solidity.Storage.Loc.Bounded] <;> decide
  · intro l member
    simp only [locations,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
private theorem numericBefore : Transport 64 hash locations store numeric := by
  intro l member
  simp only [locations,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
private theorem targetBefore : ∀ l (member : l ∈ locations),
    target.store.cells (toSlot l (fitting l member)) = encodeWord (store l) := by
  intro l member
  change encodeWord (store (Solidity.Storage.ofSlot (toSlot l _))) = _
  rw [ofSlot_toSlot]
private theorem before : Represented root (.word src :: queries) base store := by
  intro q member
  simp only [queries,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · refine ⟨?_,True.intro,?_⟩
    · change True ∧ (1 < lmax ∧ True); decide
    · intro word observed; change some one = some word at observed; cases observed; rfl
  · refine ⟨?_,True.intro,?_⟩
    · change True ∧ (2 < lmax ∧ True); decide
    · intro word observed; change some one = some word at observed; cases observed; rfl
  · refine ⟨?_,True.intro,?_⟩
    · change True ∧ (0 < lmax ∧ True); decide
    · intro word observed; change some zero = some word at observed; cases observed; rfl
  · refine ⟨?_,True.intro,?_⟩
    · change True ∧ (1 < lmax ∧ True); decide
    · intro word observed; change (none : Option Semantics.Word) = some word at observed; cases observed
private theorem apart : ∀ q ∈ queries, q.apart dst := by
  intro q member
  simp only [queries,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · change Apart graph dst shadow
    exact .fork (.key (K := .bool) true false (by change (true : Bool) ≠ false; decide)) _ _
  · change Apart graph dst outside
    exact .fork (.key (K := .bool) true false (by change (true : Bool) ≠ false; decide)) _ _
  · change Apart graph dst bad
    exact .under (.key (K := .bool) true) (.fork (.index (ix 0) (ix 1) (by decide)) .nil .nil)
private theorem nonalias : ∀ q ∈ queries, q.location base ≠ dl := by
  intro q member
  simp only [queries,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl <;> decide
private theorem covered : ∀ q ∈ queries, q.location base ∈ locations := by
  intro q member
  simp only [queries,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl <;> decide

/-- Independent graph result + PUBLIC owner representation + actual numeric
transport + CURRENT-source SLOAD/SSTORE execution and target postagreement. -/
theorem bridge :
    Evm.run (copyCode ds ss) target = .ok afterTarget 0 ∧
    Represented result (.word dst :: queries) base afterStore ∧
    Transport 64 hash locations afterStore afterNumeric ∧
    (∀ l (member : l ∈ locations), afterTarget.store.cells (toSlot l (fitting l member)) = encodeWord (afterStore l)) :=
  represented_copy run store numeric numericBefore root result dst src true rfl rfl queries base fitBase before
    (by change True ∧ (0 < lmax ∧ True); decide) apart nonalias (by decide) (by decide) covered fitting target targetBefore

/-- Actual owner-backed successful SLOAD preserves storage and all other
Machine fields, adding precisely one encoded source word to the arbitrary tail. -/
theorem read_bridge : Evm.run (readCode ss) target =
    .ok { target with stack := .val (encodeWord one) :: target.stack } 0 := by
  have initial : ∀ q ∈ (.word src :: queries),
      target.store.cells (toSlot (q.location base) (query_keysFit q base fitBase)) = encodeWord (store (q.location base)) := by
    intro q member
    have location : q.location base ∈ locations := by
      rcases List.mem_cons.mp member with rfl | later
      · decide
      · exact covered q later
    exact targetBefore _ location
  exact represented_read root (.word src :: queries) base fitBase store target before initial
    (.word src) List.mem_cons_self one rfl

private def numericView (m : WordStore) := (m 4,m 8,m 16,m 17,m 18,m 24,m 25,m 9,m 40,m 44)
private def targetView (m : Evm.Machine) :=
  (m.store ss,m.store ds,m.store hs,m.store bs,m.store (.root 9),m.stack,m.mem 3,m.mem 10,
    m.bal m.self,m.bal ⟨9,by decide⟩,m.bal₀ m.self,m.self.val,m.caller.val,m.callvalue.val,m.timestamp.val)
private def graphView (v : Value graph Root) :=
  ((v.find ap).map (fun x => (x.length.val,x.extent.val)),(v.find bp).map (fun x => (x.length.val,x.extent.val)),
    v.observe src,v.observe dst,v.observe shadow,v.observe outside,v.observe bad,
    (shadow.readLive Value.dflt v).map Value.head,(dst.readLive Value.dflt v).map Value.head)

theorem ordered : (graphView root,graphView result,numericView numeric,numericView afterNumeric,targetView target,targetView afterTarget) =
    ((some (2,3),some (1,1),some true,some false,some true,some false,none,none,some false),
     (some (2,3),some (1,1),some true,some true,some true,some false,none,none,some true),
     (two,one,zero,one,one,zero,one,seven,one,one),(two,one,zero,one,one,one,one,seven,one,one),
     (1,0,1,1,7,[.val (encodeWord seven),.slot (.root 9)],.val (encodeWord one),.slot (.root 10),100,50,200,0,9,4,23),
     (1,1,1,1,7,[.val (encodeWord seven),.slot (.root 9)],.val (encodeWord one),.slot (.root 10),100,50,200,0,9,4,23)) := rfl

theorem exact_alias : Evm.run (copyCode ss ss) target = .ok target 0 := run_copy_self ss target

private def changed : Evm.Machine := { target with store := Evm.WordStore.write target.store ss (encodeWord zero).val }
private def changedResult : Evm.Machine := { changed with store := Evm.WordStore.write changed.store ds (encodeWord zero).val }
/-- EXACT same code reads the changed CURRENT source, not original captured
payload1. Constant-source write code is a discriminating wrong implementation. -/
theorem changed_input : Evm.run (copyCode ds ss) changed = .ok changedResult 0 := run_copy ds ss changed
private def wrong : Evm.Machine := { changed with store := Evm.WordStore.write changed.store ds (encodeWord one).val }
theorem wrong_constant_source : Evm.run (writeCode ds one) changed = .ok wrong 0 ∧
    wrong.store ds ≠ changedResult.store ds := ⟨rfl,by decide⟩
theorem changed_ordered : (targetView changed,targetView changedResult,targetView wrong) =
    ((0,0,1,1,7,[.val (encodeWord seven),.slot (.root 9)],.val (encodeWord one),.slot (.root 10),100,50,200,0,9,4,23),
     (0,0,1,1,7,[.val (encodeWord seven),.slot (.root 9)],.val (encodeWord one),.slot (.root 10),100,50,200,0,9,4,23),
     (0,1,1,1,7,[.val (encodeWord seven),.slot (.root 9)],.val (encodeWord one),.slot (.root 10),100,50,200,0,9,4,23)) := rfl

/-- Out-of-extent logical read fails although total target SLOAD returns its
unconstrained garbage word. Runtime path/liveness checks are NOT proved by this
captured successful-read adapter; no profile or failure observation is weakened. -/
theorem malformed_boundary : root.find bad = none ∧ root.observe bad = none ∧
    Evm.run (readCode bs) target = .ok { target with stack := .val (encodeWord one) :: target.stack } 0 := ⟨rfl,rfl,rfl⟩
theorem wrong_tag : Evm.run [.push (.val (encodeWord zero)),.sload] target = .fault := rfl
theorem raw_key_boundary : ¬ KeysFit (.hash Evm.W (.root 0) 0) := by
  change ¬ (Evm.W < Evm.W ∧ True)
  omega

private def nested : Nat → TypeGraph.Ty 0
  | 0 => .prim .bool
  | d + 1 => .mapping .bool (nested d)
private def deep : (d : Nat) → TypeGraph.Path graph (nested d) (.prim .bool)
  | 0 => .nil
  | d + 1 => .cons (.key false) (deep d)
private def nestedValue : (d : Nat) → Value graph (nested d)
  | 0 => .prim true
  | d + 1 => .mapping (fun _ => .present (nestedValue d))
/-- Arbitrarily deep inhabited typed paths use PUBLIC normalized keys; no
runtime depth cap is imposed by the constructive target slot adapter. -/
theorem arbitrary_depth (d : Nat) :
    (nestedValue d).find (deep d) = some (.prim true) ∧
    Solidity.Storage.ofSlot (toSlot (pathLoc (deep d) base) (path_keysFit (deep d) base fitBase)) = pathLoc (deep d) base := by
  constructor
  · induction d with
    | zero => rfl
    | succ d ih => exact ih
  · exact ofSlot_toSlot _ _

/-- info: 'Solidity.Backend.StorageOps.TargetOperationControls.bridge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms bridge
/-- info: 'Solidity.Backend.StorageOps.TargetOperationControls.read_bridge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms read_bridge
/-- info: 'Solidity.Backend.StorageOps.TargetOperationControls.ordered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ordered
/-- info: 'Solidity.Backend.StorageOps.TargetOperationControls.exact_alias' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms exact_alias
/-- info: 'Solidity.Backend.StorageOps.TargetOperationControls.changed_input' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms changed_input
/-- info: 'Solidity.Backend.StorageOps.TargetOperationControls.wrong_constant_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms wrong_constant_source
/-- info: 'Solidity.Backend.StorageOps.TargetOperationControls.changed_ordered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms changed_ordered
/-- info: 'Solidity.Backend.StorageOps.TargetOperationControls.malformed_boundary' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms malformed_boundary
/-- info: 'Solidity.Backend.StorageOps.TargetOperationControls.wrong_tag' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms wrong_tag
/-- info: 'Solidity.Backend.StorageOps.TargetOperationControls.raw_key_boundary' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms raw_key_boundary
/-- info: 'Solidity.Backend.StorageOps.TargetOperationControls.arbitrary_depth' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms arbitrary_depth

end Solidity.Backend.StorageOps.TargetOperationControls
