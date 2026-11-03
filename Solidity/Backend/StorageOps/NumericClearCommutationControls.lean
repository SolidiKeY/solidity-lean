import Solidity.Backend.StorageOps.NumericClearCommutation
import Solidity.Backend.StorageOps.TargetArrayDeleteSequence

/-! Inhabited generated finite-region clear clients, distinct and overlapping
headers. Ordered transport is not unconditional commutation or world rollback. -/
namespace Solidity.Backend.StorageOps.NumericClearCommutation.Controls
open TypeGraph Solidity.Storage Solidity.Storage.Representation Solidity.Storage.Representation.Graph
private def w0 : Semantics.Word := ⟨0,by decide⟩
private def w2 : Semantics.Word := ⟨2,by decide⟩
private def w3 : Semantics.Word := ⟨3,by decide⟩
private def w7 : Semantics.Word := ⟨7,by decide⟩
private def w17 : Semantics.Word := ⟨17,by decide⟩
private def w23 : Semantics.Word := ⟨23,by decide⟩
private def w53 : Semantics.Word := ⟨53,by decide⟩
private def w59 : Semantics.Word := ⟨59,by decide⟩
private def w61 : Semantics.Word := ⟨61,by decide⟩
private def w71 : Semantics.Word := ⟨71,by decide⟩
private def w87 : Semantics.Word := ⟨87,by decide⟩
private def w93 : Semantics.Word := ⟨93,by decide⟩
private def w99 : Semantics.Word := ⟨99,by decide⟩
private def leftBase : Solidity.Storage.Loc := .root 0
private def rightBase : Solidity.Storage.Loc := .root 1
private def hash (p : Solidity.Storage.Pre) : Nat := if p = .data 0 then 4 else if p = .data 1 then 8 else 0
private def preimages : List Solidity.Storage.Pre := [.data 0,.data 1]
private def locations : List Solidity.Storage.Loc := [leftBase,.data leftBase 0,.data leftBase 1,.data leftBase 2,
 rightBase,.data rightBase 0,.data rightBase 1,.data rightBase 2,.data rightBase 3]
private def store : Store := fun l =>
 if l = leftBase then w2 else if l = .data leftBase 0 then w53 else if l = .data leftBase 1 then w59 else
 if l = .data leftBase 2 then w61 else if l = rightBase then w3 else if l = .data rightBase 0 then w7 else
 if l = .data rightBase 1 then w17 else if l = .data rightBase 2 then w23 else if l = .data rightBase 3 then w71 else
 if l = .root 2 then w99 else if l = .root 15 then w87 else w93
private def numeric : WordStore := fun a =>
 if a = 0 then w2 else if a = 4 then w53 else if a = 5 then w59 else if a = 6 then w61 else
 if a = 1 then w3 else if a = 8 then w7 else if a = 9 then w17 else if a = 10 then w23 else if a = 11 then w71 else
 if a = 2 then w99 else if a = 15 then w87 else w93
private def targetStore : Evm.WordStore := .ofFn fun s =>
 if s = .root 0 then 2 else if s = .data (.root 0) 0 then 53 else if s = .data (.root 0) 1 then 59 else
 if s = .data (.root 0) 2 then 61 else if s = .root 1 then 3 else if s = .data (.root 1) 0 then 7 else
 if s = .data (.root 1) 1 then 17 else if s = .data (.root 1) 2 then 23 else if s = .data (.root 1) 3 then 71 else
 if s = .root 2 then 99 else if s = .root 15 then 87 else 93
private def tail : List Evm.Word := [.val ⟨23,by decide⟩,.slot (.root 15)]
private def target : Evm.Machine :=
 {stack := tail,store := targetStore,mem := fun _ => .val ⟨31,by decide⟩,
  bal := fun _ => 19,bal₀ := fun _ => 19,self := ⟨7,by decide⟩,caller := ⟨13,by decide⟩,
  callvalue := ⟨0,by decide⟩,timestamp := ⟨53,by decide⟩,accepts := fun _ _ => false}
private def forward := TargetClearRepresentation.execute 16 hash rightBase (TargetClearRepresentation.execute 16 hash leftBase numeric)
private def backward := TargetClearRepresentation.execute 16 hash leftBase (TargetClearRepresentation.execute 16 hash rightBase numeric)
private def symbolicForward := clearStore rightBase (clearStore leftBase store)
private def targetForward := TargetArrayDeleteSequence.after target tail (.root 0) (.root 1)
private def targetBackward := TargetArrayDeleteSequence.after target tail (.root 1) (.root 0)
private theorem run : FiniteRun 16 4 2 hash preimages locations := by
 constructor
 · intro p; simp only [hash]; split <;> (try split) <;> decide
 · decide
 · decide
 · decide
 · intro l member
   simp only [locations,List.mem_cons,List.not_mem_nil,or_false] at member
   rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
     simp only [leftBase,rightBase,Solidity.Storage.Loc.Bounded] <;> decide
 · intro l member
   simp only [locations,List.mem_cons,List.not_mem_nil,or_false] at member
   rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
private theorem initialTransport : Transport 16 hash locations store numeric := by
 intro l member
 simp only [locations,List.mem_cons,List.not_mem_nil,or_false] at member
 rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
private theorem covered : ∀ l ∈ touches 16 hash leftBase numeric ++ touches 16 hash rightBase numeric, l ∈ locations := by
 intro l member
 change l ∈ [leftBase,.data leftBase 0,.data leftBase 1] ++ [rightBase,.data rightBase 0,.data rightBase 1,.data rightBase 2] at member
 simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at member
 rcases member with (rfl | rfl | rfl) | (rfl | rfl | rfl | rfl) <;> decide
private theorem separate : ∀ a ∈ touches 16 hash leftBase numeric, ∀ b ∈ touches 16 hash rightBase numeric, a ≠ b := by
 intro a insideA b insideB
 change a ∈ [leftBase,.data leftBase 0,.data leftBase 1] at insideA
 change b ∈ [rightBase,.data rightBase 0,.data rightBase 1,.data rightBase 2] at insideB
 simp only [List.mem_cons,List.not_mem_nil,or_false] at insideA insideB
 rcases insideA with rfl | rfl | rfl <;> rcases insideB with rfl | rfl | rfl | rfl <;> decide

/-- Full function equality, not just the observation projection. -/
theorem commutes : forward = backward := clear_clear run leftBase rightBase numeric covered separate

theorem transported : Transport 16 hash locations symbolicForward forward := by
 apply sequence_transport run leftBase rightBase store numeric initialTransport (by decide) (by decide)
 · intro j live
   change j < 2 at live
   have cases : j = 0 ∨ j = 1 := by omega
   rcases cases with rfl | rfl <;> decide
 · intro j live
   change j < 3 at live
   have cases : j = 0 ∨ j = 1 ∨ j = 2 := by omega
   rcases cases with rfl | rfl | rfl <;> decide

theorem target_runs :
 Evm.run (TargetArrayDeleteSequence.code (.root 1)) {target with stack := .slot (.root 0) :: tail} = .ok targetForward 0 ∧
 Evm.run (TargetArrayDeleteSequence.code (.root 0)) {target with stack := .slot (.root 1) :: tail} = .ok targetBackward 0 :=
 ⟨TargetArrayDeleteSequence.run_current target tail _ _,TargetArrayDeleteSequence.run_current target tail _ _⟩
private def physicalView (m : WordStore) := [m 0,m 4,m 5,m 6,m 1,m 8,m 9,m 10,m 11,m 7,m 2,m 15]
private def symbolicView (m : Store) := [m leftBase,m (.data leftBase 0),m (.data leftBase 1),m (.data leftBase 2),
 m rightBase,m (.data rightBase 0),m (.data rightBase 1),m (.data rightBase 2),m (.data rightBase 3),m (.root 7),m (.root 2),m (.root 15)]
private def targetView (m : Evm.Machine) := [m.store (.root 0),m.store (.data (.root 0) 0),m.store (.data (.root 0) 1),m.store (.data (.root 0) 2),
 m.store (.root 1),m.store (.data (.root 1) 0),m.store (.data (.root 1) 1),m.store (.data (.root 1) 2),m.store (.data (.root 1) 3),m.store (.root 7),m.store (.root 2),m.store (.root 15)]
private def context (m : Evm.Machine) := (m.stack,m.mem 0,m.bal m.self,m.bal₀ m.self,m.self,m.caller,m.callvalue,m.timestamp,m.accepts m.self m.self)

/-- Full ordered footprints/logs and all recorded input/output/context words. -/
theorem ordered :
 (touches 16 hash leftBase numeric,touches 16 hash rightBase numeric,
  writeLog 16 hash leftBase numeric,writeLog 16 hash rightBase numeric,
  touches 16 hash leftBase forward,touches 16 hash rightBase forward,
  symbolicView store,symbolicView symbolicForward,physicalView numeric,physicalView forward,physicalView backward,
  targetView target,targetView targetForward,targetView targetBackward,context targetForward,context targetBackward) =
 ([leftBase,.data leftBase 0,.data leftBase 1],[rightBase,.data rightBase 0,.data rightBase 1,.data rightBase 2],
  [(.data leftBase 0,w0),(.data leftBase 1,w0),(leftBase,w0)],
  [(.data rightBase 0,w0),(.data rightBase 1,w0),(.data rightBase 2,w0),(rightBase,w0)],
  [leftBase],[rightBase],
  [w2,w53,w59,w61,w3,w7,w17,w23,w71,w93,w99,w87],
  [w0,w0,w0,w61,w0,w0,w0,w0,w71,w93,w99,w87],
  [w2,w53,w59,w61,w3,w7,w17,w23,w71,w93,w99,w87],
  [w0,w0,w0,w61,w0,w0,w0,w0,w71,w93,w99,w87],
  [w0,w0,w0,w61,w0,w0,w0,w0,w71,w93,w99,w87],
  [2,53,59,61,3,7,17,23,71,93,99,87],[0,0,0,61,0,0,0,0,71,93,99,87],
  [0,0,0,61,0,0,0,0,71,93,99,87],context target,context target) := by rfl

private def w1 : Semantics.Word := ⟨1,by decide⟩
private def w77 : Semantics.Word := ⟨77,by decide⟩
private def aliasBase : Solidity.Storage.Loc := .data leftBase 0
private def aliasHash (p : Solidity.Storage.Pre) : Nat := if p = .data 0 then 4 else if p = .data 4 then 12 else 0
private def aliasLocations : List Solidity.Storage.Loc := [leftBase,aliasBase,.data aliasBase 0]
private def aliasStore : Store := fun l => if l = leftBase then w1 else if l = aliasBase then w1 else w77
private def aliasNumeric : WordStore := fun a => if a = 0 then w1 else if a = 4 then w1 else w77
private def aliasForward := TargetClearRepresentation.execute 32 aliasHash aliasBase
 (TargetClearRepresentation.execute 32 aliasHash leftBase aliasNumeric)
private def aliasBackward := TargetClearRepresentation.execute 32 aliasHash leftBase
 (TargetClearRepresentation.execute 32 aliasHash aliasBase aliasNumeric)
private theorem aliasRun : FiniteRun 32 2 1 aliasHash [.data 0,.data 4] aliasLocations := by
 constructor
 · intro p; simp only [aliasHash]; split <;> (try split) <;> decide
 · decide
 · decide
 · decide
 · intro l member
   simp only [aliasLocations,List.mem_cons,List.not_mem_nil,or_false] at member
   rcases member with rfl | rfl | rfl <;> simp only [aliasBase,leftBase,Solidity.Storage.Loc.Bounded] <;> decide
 · intro l member
   simp only [aliasLocations,List.mem_cons,List.not_mem_nil,or_false] at member
   rcases member with rfl | rfl | rfl <;> decide

/-- Same per-run regions may have overlapping generated HEADER/DATA locations.
Correct CURRENT-header clear is NOT unconditionally commutative. -/
theorem overlap_negative :
 ([aliasForward 0,aliasForward 4,aliasForward 12],[aliasBackward 0,aliasBackward 4,aliasBackward 12],
  touches 32 aliasHash aliasBase (TargetClearRepresentation.execute 32 aliasHash leftBase aliasNumeric)) =
 ([w0,w0,w77],[w0,w0,w0],[aliasBase]) ∧ aliasForward ≠ aliasBackward := by
 refine ⟨rfl,?_⟩
 intro same
 have observed := congrFun same 12
 change w77 = w0 at observed
 exact (by decide : w77 ≠ w0) observed

/-- The overlapping ordered execution still transports, without fictitious
second child coverage: its ACTUAL second header0 means no child iteration. -/
theorem overlapping_transport :
 Transport 32 aliasHash aliasLocations (clearStore aliasBase (clearStore leftBase aliasStore)) aliasForward := by
 apply sequence_transport aliasRun leftBase aliasBase aliasStore aliasNumeric
   (by intro l member; simp only [aliasLocations,List.mem_cons,List.not_mem_nil,or_false] at member; rcases member with rfl | rfl | rfl <;> rfl)
   (by decide) (by decide)
 · intro j live
   change j < 1 at live
   have same : j = 0 := by omega
   subst j
   decide
 · intro j live
   change j < 0 at live
   omega

/-- info: 'Solidity.Backend.StorageOps.NumericClearCommutation.Controls.commutes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms commutes
/-- info: 'Solidity.Backend.StorageOps.NumericClearCommutation.Controls.transported' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms transported
/-- info: 'Solidity.Backend.StorageOps.NumericClearCommutation.Controls.target_runs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms target_runs
/-- info: 'Solidity.Backend.StorageOps.NumericClearCommutation.Controls.ordered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms ordered
/-- info: 'Solidity.Backend.StorageOps.NumericClearCommutation.Controls.overlap_negative' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms overlap_negative
/-- info: 'Solidity.Backend.StorageOps.NumericClearCommutation.Controls.overlapping_transport' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms overlapping_transport
end Solidity.Backend.StorageOps.NumericClearCommutation.Controls
