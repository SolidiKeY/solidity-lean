import Solidity.Backend.StorageOps.AlternatingLifecycle

/-! Generic alternating operation blocks, including empty-block parity,
current-header updates, represented graph composition and exact failure traces.
No emitted code, source admission or world rollback theorem is inferred. -/
namespace Solidity.Backend.StorageOps.AlternatingLifecycleControls
open TypeGraph Solidity.Storage Solidity.Storage.Representation Solidity.Storage.Representation.Graph
open LifecycleSchedules MixedLifecycle AlternatingLifecycle
private def graph : Schema 0 where
  origin := "v10-alternating-lifecycle-controls"
  declId := fun i => nomatch i
  declId_injective := by intro i; exact Fin.elim0 i
  name := fun i => nomatch i
  fields := fun i => nomatch i
  rank := fun i => nomatch i
  nonempty := by intro i; exact Fin.elim0 i
  distinct := by intro i; exact Fin.elim0 i
  guarded := by intro i; exact Fin.elim0 i
private def ix (i : Fin 4) : Index := ⟨i.val,by have bound := i.isLt; omega⟩
private def indices : List Index := [ix 0,ix 1,ix 2,ix 3]
private abbrev Elem : TypeGraph.Ty 0 := .array (.prim .bool)
private def a : Solidity.Storage.Loc := .root 0
private def b : Solidity.Storage.Loc := .root 1
private def zero : Semantics.Word := ClearDemands.zero
private def one : Semantics.Word := PrimTy.toWord (p := .bool) true
private def two : Semantics.Word := lengthWord 2 (by decide)
private def three : Semantics.Word := lengthWord 3 (by decide)
private def four : Semantics.Word := lengthWord 4 (by decide)
private def seven : Semantics.Word := ⟨7,by decide⟩
private def hash (p : Solidity.Storage.Pre) : Nat := if p = .data 0 then 8 else if p = .data 1 then 16 else 0
private def preimages : List Solidity.Storage.Pre := [.data 0,.data 1]
private def locations : List Solidity.Storage.Loc := [a,b,
  .data a 0,.data a 1,.data a 2,.data a 3,.data b 0,.data b 1,.data b 2,.data b 3]
private def old : Value graph Elem := .array ⟨4,by decide⟩ ⟨1,by decide⟩ (by decide) (fun _ => .present (.prim true))
private def other : Value graph Elem := .array ⟨2,by decide⟩ ⟨0,by decide⟩ (by decide) (fun _ => .present (.prim true))
private def store : Store := fun l => if l = a then one else if l = .root 2 then seven else
  if l = .data a 0 ∨ l = .data a 1 ∨ l = .data a 2 ∨ l = .data a 3 ∨ l = .data b 0 ∨ l = .data b 1 then one else zero
private def machine : WordStore := fun n => if n = 0 then one else if n = 2 then seven else
  if n = 8 ∨ n = 9 ∨ n = 10 ∨ n = 11 ∨ n = 16 ∨ n = 17 ∨ n = 24 ∨ n = 28 then one else zero
private def view (m : WordStore) := (m 0,m 1,m 8,m 9,m 10,m 11,m 16,m 17,m 18,m 19,m 24,m 28,m 2)
private def element (i : Index) : TypeGraph.Path graph Elem (.prim .bool) := .cons (.index i) .nil
private def graphView (v : Value graph Elem) :=
  (v.length.val,v.extent.val,v.observe (element (ix 0)),v.observe (element (ix 1)),
   v.observe (element (ix 2)),v.observe (element (ix 3)),
   ((element (ix 0)).readLive Value.dflt v).map Value.head,
   ((element (ix 1)).readLive Value.dflt v).map Value.head,
   ((element (ix 2)).readLive Value.dflt v).map Value.head,
   ((element (ix 3)).readLive Value.dflt v).map Value.head)
private def bases : List Solidity.Storage.Loc := [a,a,b,a,b]
private def pushed := (pushMany 32 hash bases machine).getD machine
private def repeated := (pushMany 32 hash [a,a,a] machine).getD machine
private def popped := (popMany 32 hash [a,a] repeated).getD machine
private def regrown := (pushMany 32 hash [a,a] popped).getD machine
private theorem run : FiniteRun 32 4 2 hash preimages locations := by
  constructor
  · intro p; simp only [hash]; split <;> (first | decide | (split <;> decide))
  · decide
  · decide
  · decide
  · intro l member
    simp only [locations,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [a,b,Solidity.Storage.Loc.Bounded] <;> decide
  · intro l member
    simp only [locations,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
private theorem initial : Transport 32 hash locations store machine := by
  intro l member
  simp only [locations,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
private theorem before : Represented old (PrimitivePop.queries indices) a store := by
  intro q member
  simp only [PrimitivePop.queries,indices,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · refine ⟨True.intro,⟨by decide,by decide⟩,?_⟩
    intro word observed; change some one = some word at observed; cases observed; rfl
  · refine ⟨⟨by change 0 < lmax; decide,True.intro⟩,True.intro,?_⟩
    intro word observed; change some one = some word at observed; cases observed; rfl
  · refine ⟨⟨by change 1 < lmax; decide,True.intro⟩,True.intro,?_⟩
    intro word observed; change some one = some word at observed; cases observed; rfl
  · refine ⟨⟨by change 2 < lmax; decide,True.intro⟩,True.intro,?_⟩
    intro word observed; change some one = some word at observed; cases observed; rfl
  · refine ⟨⟨by change 3 < lmax; decide,True.intro⟩,True.intro,?_⟩
    intro word observed; change some one = some word at observed; cases observed; rfl

private def liveOld : Value graph Elem := .array ⟨4,by decide⟩ ⟨3,by decide⟩ (by decide) (fun _ => .present (.prim true))
private def liveStore := Representation.write (Representation.write store a three) b one
private def liveMachine := writeWord (writeWord machine 0 three) 1 one
private def upDown := (pushPop 32 hash [a] [a,a] liveMachine).getD liveMachine
private def downUp := (popPush 32 hash [a,a] [a] liveMachine).getD liveMachine
private def graphUp := (graphPushes 1 liveOld).getD liveOld
private def graphDown := (graphPops 2 liveOld).getD liveOld
private def graphUpDown := (graphPops 2 graphUp).getD liveOld
private def graphDownUp := (graphPushes 1 graphDown).getD liveOld
private theorem liveBefore : Represented liveOld (PrimitivePop.queries indices) a liveStore := by
  intro q member
  simp only [PrimitivePop.queries,indices,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · refine ⟨True.intro,⟨by decide,by decide⟩,?_⟩
    intro word observed; change some three = some word at observed; cases observed; rfl
  · refine ⟨⟨by change 0 < lmax; decide,True.intro⟩,True.intro,?_⟩
    intro word observed; change some one = some word at observed; cases observed; rfl
  · refine ⟨⟨by change 1 < lmax; decide,True.intro⟩,True.intro,?_⟩
    intro word observed; change some one = some word at observed; cases observed; rfl
  · refine ⟨⟨by change 2 < lmax; decide,True.intro⟩,True.intro,?_⟩
    intro word observed; change some one = some word at observed; cases observed; rfl
  · refine ⟨⟨by change 3 < lmax; decide,True.intro⟩,True.intro,?_⟩
    intro word observed; change some one = some word at observed; cases observed; rfl
private theorem liveTransport : Transport 32 hash locations liveStore liveMachine :=
  transport_write run (transport_write run initial a (by decide) three) b (by decide) one


private def yes : Slot graph (.prim .bool) := .present (.prim true)
private def no : Slot graph (.prim .bool) := .present (.prim false)
private def absent : Slot graph (.prim .bool) := .absent
private def vector (x0 x1 x2 x3 : Slot graph (.prim .bool)) : Fin 4 → Slot graph (.prim .bool) :=
  fun i => if i.val = 0 then x0 else if i.val = 1 then x1 else if i.val = 2 then x2 else x3
private def arr (length : Fin 5) (slots : Fin 4 → Slot graph (.prim .bool)) : Value graph Elem :=
  .array ⟨4,by decide⟩ ⟨length.val,by
      have small := length.isLt
      have bound : (5 : Nat) < 2 ^ 256 := by decide
      exact Nat.lt_trans small bound⟩
    (by change length.val ≤ 4; exact Nat.le_of_lt_succ length.isLt) slots
private def v1 := arr 4 (vector yes yes yes absent)
private def v2 := arr 3 (vector yes yes yes absent)
private def v31 := arr 2 (vector yes yes no absent)
private def v4 := arr 1 (vector yes no no absent)
private def v5 := arr 2 (vector yes absent no absent)
private def v0 := arr 0 (vector no no no absent)
private def r1 := arr 2 (vector yes yes no yes)
private def r2 := arr 1 (vector yes no no yes)
private def r3 := arr 2 (vector yes absent no yes)
private def r4 := arr 1 (vector yes absent no yes)
private def r5 := arr 2 (vector yes absent no yes)
private def r6 := arr 3 (vector yes absent absent yes)
private def w5 : Value graph Elem := .array ⟨5,by decide⟩ ⟨5,by decide⟩ (by decide)
  (fun i => if i.val < 3 then yes else absent)
private def w4 : Value graph Elem := .array ⟨5,by decide⟩ ⟨4,by decide⟩ (by decide)
  (fun i => if i.val < 3 then yes else absent)
private theorem p0 : operationPush liveOld = some v1 := by
  apply congrArg (fun slots : Fin 4 → Slot graph (.prim .bool) =>
    some (Value.array (G := graph) (E := .prim .bool) ⟨4,by decide⟩ ⟨4,by decide⟩ (by decide) slots))
  funext i
  rcases i with ⟨i,inside⟩
  change i < 4 at inside
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases cases with rfl | rfl | rfl | rfl <;> rfl
private theorem p1 : recursivePop v1 = some v2 := by
  apply congrArg (fun slots : Fin 4 → Slot graph (.prim .bool) =>
    some (Value.array (G := graph) (E := .prim .bool) ⟨4,by decide⟩ ⟨3,by decide⟩ (by decide) slots))
  funext i
  rcases i with ⟨i,inside⟩
  change i < 4 at inside
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases cases with rfl | rfl | rfl | rfl <;> rfl
private theorem p2 : recursivePop v2 = some v31 := by
  apply congrArg (fun slots : Fin 4 → Slot graph (.prim .bool) =>
    some (Value.array (G := graph) (E := .prim .bool) ⟨4,by decide⟩ ⟨2,by decide⟩ (by decide) slots))
  funext i
  rcases i with ⟨i,inside⟩
  change i < 4 at inside
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases cases with rfl | rfl | rfl | rfl <;> rfl
private theorem p3 : recursivePop v31 = some v4 := by
  apply congrArg (fun slots : Fin 4 → Slot graph (.prim .bool) =>
    some (Value.array (G := graph) (E := .prim .bool) ⟨4,by decide⟩ ⟨1,by decide⟩ (by decide) slots))
  funext i
  rcases i with ⟨i,inside⟩
  change i < 4 at inside
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases cases with rfl | rfl | rfl | rfl <;> rfl
private theorem p4 : operationPush v4 = some v5 := by
  apply congrArg (fun slots : Fin 4 → Slot graph (.prim .bool) =>
    some (Value.array (G := graph) (E := .prim .bool) ⟨4,by decide⟩ ⟨2,by decide⟩ (by decide) slots))
  funext i
  rcases i with ⟨i,inside⟩
  change i < 4 at inside
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases cases with rfl | rfl | rfl | rfl <;> rfl
private theorem p5 : recursivePop v4 = some v0 := by
  apply congrArg (fun slots : Fin 4 → Slot graph (.prim .bool) =>
    some (Value.array (G := graph) (E := .prim .bool) ⟨4,by decide⟩ ⟨0,by decide⟩ (by decide) slots))
  funext i
  rcases i with ⟨i,inside⟩
  change i < 4 at inside
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases cases with rfl | rfl | rfl | rfl <;> rfl
private theorem r0 : recursivePop liveOld = some r1 := by
  apply congrArg (fun slots : Fin 4 → Slot graph (.prim .bool) =>
    some (Value.array (G := graph) (E := .prim .bool) ⟨4,by decide⟩ ⟨2,by decide⟩ (by decide) slots))
  funext i
  rcases i with ⟨i,inside⟩
  change i < 4 at inside
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases cases with rfl | rfl | rfl | rfl <;> rfl
private theorem r1_step : recursivePop r1 = some r2 := by
  apply congrArg (fun slots : Fin 4 → Slot graph (.prim .bool) =>
    some (Value.array (G := graph) (E := .prim .bool) ⟨4,by decide⟩ ⟨1,by decide⟩ (by decide) slots))
  funext i
  rcases i with ⟨i,inside⟩
  change i < 4 at inside
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases cases with rfl | rfl | rfl | rfl <;> rfl
private theorem r2_step : operationPush r2 = some r3 := by
  apply congrArg (fun slots : Fin 4 → Slot graph (.prim .bool) =>
    some (Value.array (G := graph) (E := .prim .bool) ⟨4,by decide⟩ ⟨2,by decide⟩ (by decide) slots))
  funext i
  rcases i with ⟨i,inside⟩
  change i < 4 at inside
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases cases with rfl | rfl | rfl | rfl <;> rfl
private theorem r3_step : recursivePop r3 = some r4 := by
  apply congrArg (fun slots : Fin 4 → Slot graph (.prim .bool) =>
    some (Value.array (G := graph) (E := .prim .bool) ⟨4,by decide⟩ ⟨1,by decide⟩ (by decide) slots))
  funext i
  rcases i with ⟨i,inside⟩
  change i < 4 at inside
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases cases with rfl | rfl | rfl | rfl <;> rfl
private theorem r4_step : operationPush r4 = some r5 := by
  apply congrArg (fun slots : Fin 4 → Slot graph (.prim .bool) =>
    some (Value.array (G := graph) (E := .prim .bool) ⟨4,by decide⟩ ⟨2,by decide⟩ (by decide) slots))
  funext i
  rcases i with ⟨i,inside⟩
  change i < 4 at inside
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases cases with rfl | rfl | rfl | rfl <;> rfl
private theorem r5_step : operationPush r5 = some r6 := by
  apply congrArg (fun slots : Fin 4 → Slot graph (.prim .bool) =>
    some (Value.array (G := graph) (E := .prim .bool) ⟨4,by decide⟩ ⟨3,by decide⟩ (by decide) slots))
  funext i
  rcases i with ⟨i,inside⟩
  change i < 4 at inside
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases cases with rfl | rfl | rfl | rfl <;> rfl
private theorem w0 : operationPush v2 = some v1 := by
  apply congrArg (fun slots : Fin 4 → Slot graph (.prim .bool) =>
    some (Value.array (G := graph) (E := .prim .bool) ⟨4,by decide⟩ ⟨4,by decide⟩ (by decide) slots))
  funext i
  rcases i with ⟨i,inside⟩
  change i < 4 at inside
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases cases with rfl | rfl | rfl | rfl <;> rfl
private theorem w1 : operationPush v1 = some w5 := by
  apply congrArg (fun slots : Fin 5 → Slot graph (.prim .bool) =>
    some (Value.array (G := graph) (E := .prim .bool) ⟨5,by decide⟩ ⟨5,by decide⟩ (by decide) slots))
  funext i
  rcases i with ⟨i,inside⟩
  change i < 5 at inside
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl <;> rfl
private theorem w2 : recursivePop w5 = some w4 := by
  apply congrArg (fun slots : Fin 5 → Slot graph (.prim .bool) =>
    some (Value.array (G := graph) (E := .prim .bool) ⟨5,by decide⟩ ⟨4,by decide⟩ (by decide) slots))
  funext i
  rcases i with ⟨i,inside⟩
  change i < 5 at inside
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl <;> rfl
private theorem graph_first : graphPushBlocks [1] liveOld = some v1 := by
  simp only [graphPushBlocks,graphPopBlocks,graphPushes,p0,Option.bind_some]
private theorem graph_second : graphPushBlocks [1,1] liveOld = some v2 := by
  simp only [graphPushBlocks,graphPopBlocks,graphPushes,graphPops,p0,p1,Option.bind_some]
private theorem graph_third : graphPushBlocks [1,1,0] liveOld = some v2 := by
  simp only [graphPushBlocks,graphPopBlocks,graphPushes,graphPops,p0,p1,Option.bind_some]
private theorem graph_fourth : graphPushBlocks [1,1,0,2] liveOld = some v4 := by
  simp only [graphPushBlocks,graphPopBlocks,graphPushes,graphPops,p0,p1,p2,p3,Option.bind_some]
private theorem graph_final : graphPushBlocks [1,1,0,2,1] liveOld = some v5 := by
  simp only [graphPushBlocks,graphPopBlocks,graphPushes,graphPops,p0,p1,p2,p3,p4,Option.bind_some]
private theorem graph_reverse : graphPopBlocks [2,1,1,2] liveOld = some r6 := by
  simp only [graphPushBlocks,graphPopBlocks,graphPushes,graphPops,r0,r1_step,r2_step,r3_step,r4_step,r5_step,Option.bind_some]
private theorem graph_failure : graphPushBlocks [1,1,0,4,1] liveOld = none := by
  simp only [graphPushBlocks,graphPopBlocks,graphPushes,graphPops,p0,p1,p2,p3,p5,Option.bind_some]
  rfl

private def counts : List Nat := [1,1,0,2,1]
private def blocks : List (List Solidity.Storage.Loc) := counts.map (fun count => List.replicate count a)
private def final := (pushBlocks 32 hash blocks liveMachine).getD liveMachine
private def gFinal := (graphPushBlocks counts liveOld).getD liveOld
private def first := (pushBlocks 32 hash [[a]] liveMachine).getD liveMachine
private def second := (pushBlocks 32 hash [[a],[a]] liveMachine).getD liveMachine
private def third := (pushBlocks 32 hash [[a],[a],[]] liveMachine).getD liveMachine
private def fourth := (pushBlocks 32 hash [[a],[a],[],[a,a]] liveMachine).getD liveMachine
private def gFirst := (graphPushBlocks [1] liveOld).getD liveOld
private def gSecond := (graphPushBlocks [1,1] liveOld).getD liveOld
private def gThird := (graphPushBlocks [1,1,0] liveOld).getD liveOld
private def gFourth := (graphPushBlocks [1,1,0,2] liveOld).getD liveOld

theorem represented_bridge : ∃ result ops, graphPushBlocks counts liveOld = some result ∧
    pushBlockLog 32 hash (counts.map (fun count => List.replicate count a)) liveMachine = some ops ∧
    Transport 32 hash locations (ops.foldl (fun w op => Representation.write w op.1 op.2) liveStore) final ∧
    Represented result (PrimitivePop.queries indices) a (ops.foldl (fun w op => Representation.write w op.1 op.2) liveStore) :=
  push_blocks_represented run counts liveOld indices a liveStore liveMachine final liveBefore liveTransport rfl (by decide)
    (by
      simp only [counts,pushHeaderCoverage,popHeaderCoverage,graphPushes,graphPops,p0,p1,p2,p3,Option.bind_some]
      change 4 ≤ lmax ∧ (3 ≤ lmax ∧ (2 ≤ lmax ∧ True))
      decide)

/-- Every numeric prefix and graph header/extent/raw/live prefix is pinned.
The EMPTY third block still flips the next family from push to pop. -/
theorem ordered :
    (view liveMachine,view first,view second,view third,view fourth,view final,
     graphView liveOld,graphView gFirst,graphView gSecond,graphView gThird,graphView gFourth,graphView gFinal,
     pushBlockAccesses 32 hash blocks liveMachine) =
    ((three,one,one,one,one,one,one,one,zero,zero,one,one,seven),
     (four,one,one,one,one,zero,one,one,zero,zero,one,one,seven),
     (three,one,one,one,one,zero,one,one,zero,zero,one,one,seven),
     (three,one,one,one,one,zero,one,one,zero,zero,one,one,seven),
     (one,one,one,zero,zero,zero,one,one,zero,zero,one,one,seven),
     (two,one,one,zero,zero,zero,one,one,zero,zero,one,one,seven),
     (3,4,some true,some true,some true,some true,some true,some true,some true,none),
     (4,4,some true,some true,some true,some false,some true,some true,some true,some false),
     (3,4,some true,some true,some true,some false,some true,some true,some true,none),
     (3,4,some true,some true,some true,some false,some true,some true,some true,none),
     (1,4,some true,some false,some false,some false,some true,none,none,none),
     (2,4,some true,some false,some false,some false,some true,some false,none,none),
     [a,.data a 3,a,.data a 3,a,.data a 2,a,.data a 1,a,.data a 1]) := by
  simp only [gFirst,gSecond,gThird,gFourth,gFinal,counts,graph_first,graph_second,graph_third,graph_fourth,graph_final,Option.getD_some]
  rfl

/-- Actual ODD-length prefix (including empty block) restarts with POP. -/
theorem restart : pushBlocks 32 hash ([[a],[a],[]] ++ [[a,a],[a]]) liveMachine =
    (pushBlocks 32 hash [[a],[a],[]] liveMachine).bind (popBlocks 32 hash [[a,a],[a]]) :=
  push_blocks_append 32 hash [[a],[a],[]] [[a,a],[a]] liveMachine

theorem restart_accesses : pushBlockAccesses 32 hash ([[a],[a],[]] ++ [[a,a],[a]]) liveMachine =
    pushBlockAccesses 32 hash [[a],[a],[]] liveMachine ++ popBlockAccesses 32 hash [[a,a],[a]] third :=
  push_accesses_append 32 hash [[a],[a],[]] [[a,a],[a]] liveMachine third rfl

private def wrongRestart := (pushBlocks 32 hash [[a,a],[a]] third).getD third
private def wrongGraph := (graphPushBlocks [2,1] gThird).getD gThird
/-- Wrong restart family changes header/data and source extent; its EXTRA
index4 access is outside the correct covered run, not a new profile refusal. -/
theorem wrong_restart_ordered : (view wrongRestart,view final,graphView wrongGraph,graphView gFinal) =
    ((four,one,one,one,one,zero,one,one,zero,zero,one,one,seven),
     (two,one,one,zero,zero,zero,one,one,zero,zero,one,one,seven),
     (4,5,some true,some true,some true,some false,some true,some true,some true,some false),
     (2,4,some true,some false,some false,some false,some true,some false,none,none)) := by
  have wrongGraph_eq : wrongGraph = w4 := by
    simp only [wrongGraph,gThird,graph_third,Option.getD_some]
    simp only [graphPushBlocks,graphPopBlocks,graphPushes,graphPops,w0,w1,w2,Option.bind_some,Option.getD_some]
  simp only [wrongGraph_eq,gFinal,counts,graph_final,Option.getD_some]
  rfl

private def multiBlocks : List (List Solidity.Storage.Loc) := [[a,b],[b],[],[a],[b,a],[]]
private def multi := (popBlocks 32 hash multiBlocks liveMachine).getD liveMachine

theorem multi_transport : ∃ ops, popBlockLog 32 hash multiBlocks liveMachine = some ops ∧
    Transport 32 hash locations (ops.foldl (fun w op => Representation.write w op.1 op.2) liveStore) multi :=
  pop_blocks_transport run multiBlocks liveStore liveMachine multi liveTransport rfl (by decide)
theorem multi_ordered : (view multi,popBlockAccesses 32 hash multiBlocks liveMachine) =
    ((two,zero,one,one,zero,one,zero,one,zero,zero,one,one,seven),
     [a,.data a 2,b,.data b 0,b,.data b 0,a,.data a 2,b,.data b 0,a,.data a 2]) := rfl

private def reverseCounts : List Nat := [2,1,1,2]
private def reverseBlocks := reverseCounts.map (fun count => List.replicate count a)
private def reverseFinal := (popBlocks 32 hash reverseBlocks liveMachine).getD liveMachine
private def reverseGraph := (graphPopBlocks reverseCounts liveOld).getD liveOld

theorem reverse_bridge : ∃ result ops, graphPopBlocks reverseCounts liveOld = some result ∧
    popBlockLog 32 hash reverseBlocks liveMachine = some ops ∧
    Transport 32 hash locations (ops.foldl (fun w op => Representation.write w op.1 op.2) liveStore) reverseFinal ∧
    Represented result (PrimitivePop.queries indices) a (ops.foldl (fun w op => Representation.write w op.1 op.2) liveStore) :=
  pop_blocks_represented run reverseCounts liveOld indices a liveStore liveMachine reverseFinal liveBefore liveTransport rfl (by decide)
    (by
      simp only [reverseCounts,pushHeaderCoverage,popHeaderCoverage,graphPushes,graphPops,r0,r1_step,r2_step,r3_step,Option.bind_some]
      change 2 ≤ lmax ∧ (3 ≤ lmax ∧ True)
      decide)
theorem reverse_ordered : (view reverseFinal,graphView reverseGraph,popBlockAccesses 32 hash reverseBlocks liveMachine) =
    ((three,one,one,zero,zero,one,one,one,zero,zero,one,one,seven),
     (3,4,some true,some false,some false,some true,some true,some false,some false,none),
     [a,.data a 2,a,.data a 1,a,.data a 1,a,.data a 1,a,.data a 1,a,.data a 2]) := by
  simp only [reverseGraph,reverseCounts,graph_reverse,Option.getD_some]
  rfl

private def failureBlocks : List (List Solidity.Storage.Loc) := [[a],[a],[],[a,a,a,a],[b]]
private def failurePrefix := (popMany 32 hash [a,a,a] third).getD third
/-- Failure in the fourth block stops the fifth; the preceding successful
prefix has changed payloads. No final Option store or world rollback is claimed. -/
theorem failure_ordered :
    ((pushBlocks 32 hash failureBlocks liveMachine).map view,pushBlockAccesses 32 hash failureBlocks liveMachine,
      pushBlockLog 32 hash failureBlocks liveMachine,view failurePrefix,
      (graphPushBlocks [1,1,0,4,1] liveOld).map graphView) =
    (none,[a,.data a 3,a,.data a 3,a,.data a 2,a,.data a 1,a,.data a 0,a],none,
     (zero,one,zero,zero,zero,zero,one,one,zero,zero,one,one,seven),none) := by
  simp only [graph_failure,Option.map_none]
  rfl

theorem failed_prefix : pushBlocks 32 hash ([[a],[a],[],[a,a,a,a]] ++ [[b],[],[a]]) liveMachine = none :=
  push_blocks_failed_prefix 32 hash [[a],[a],[],[a,a,a,a]] [[b],[],[a]] liveMachine rfl

private def full : Semantics.Word := lengthWord (2 ^ 256 - 1) (by decide)
private def capacity := writeWord liveMachine 0 full
private def capacityPrefix := (pushMany 32 hash [b] capacity).getD capacity
/-- Late capacity failure is numeric-only, with no fictitious failed reset. -/
theorem capacity_ordered :
    ((pushBlocks 32 hash [[b],[],[a],[b]] capacity).map view,
      pushBlockAccesses 32 hash [[b],[],[a],[b]] capacity,pushBlockLog 32 hash [[b],[],[a],[b]] capacity,view capacityPrefix) =
    (none,[b,.data b 1,a],none,(full,two,one,one,one,one,one,zero,zero,zero,one,one,seven)) := rfl

/-- Dropping an empty block is NOT safe: it flips which actual operation runs. -/
theorem empty_parity_ordered :
    ((pushBlocks 32 hash [[],[a]] liveMachine).map view,(pushBlocks 32 hash [[a]] liveMachine).map view,
     pushBlockAccesses 32 hash [[],[a]] liveMachine) =
    (some (two,one,one,one,zero,one,one,one,zero,zero,one,one,seven),
     some (four,one,one,one,one,zero,one,one,zero,zero,one,one,seven),[a,.data a 2]) := rfl

/-- info: 'Solidity.Backend.StorageOps.AlternatingLifecycleControls.represented_bridge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms represented_bridge
/-- info: 'Solidity.Backend.StorageOps.AlternatingLifecycleControls.ordered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms ordered
/-- info: 'Solidity.Backend.StorageOps.AlternatingLifecycleControls.restart' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms restart
/-- info: 'Solidity.Backend.StorageOps.AlternatingLifecycleControls.restart_accesses' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms restart_accesses
/-- info: 'Solidity.Backend.StorageOps.AlternatingLifecycleControls.wrong_restart_ordered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms wrong_restart_ordered
/-- info: 'Solidity.Backend.StorageOps.AlternatingLifecycleControls.multi_transport' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms multi_transport
/-- info: 'Solidity.Backend.StorageOps.AlternatingLifecycleControls.multi_ordered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms multi_ordered
/-- info: 'Solidity.Backend.StorageOps.AlternatingLifecycleControls.reverse_bridge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms reverse_bridge
/-- info: 'Solidity.Backend.StorageOps.AlternatingLifecycleControls.reverse_ordered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms reverse_ordered
/-- info: 'Solidity.Backend.StorageOps.AlternatingLifecycleControls.failure_ordered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms failure_ordered
/-- info: 'Solidity.Backend.StorageOps.AlternatingLifecycleControls.failed_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms failed_prefix
/-- info: 'Solidity.Backend.StorageOps.AlternatingLifecycleControls.capacity_ordered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms capacity_ordered
/-- info: 'Solidity.Backend.StorageOps.AlternatingLifecycleControls.empty_parity_ordered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms empty_parity_ordered

end Solidity.Backend.StorageOps.AlternatingLifecycleControls
