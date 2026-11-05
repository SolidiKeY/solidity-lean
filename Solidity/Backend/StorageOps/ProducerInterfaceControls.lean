import Solidity.Backend.StorageOps.ProducerInterface
import Solidity.Backend.StorageOps.CopyDemandControls

/-! A concrete scalar SSTORE inhabits the local endpoint, not a universal G27
or P17 producer. Its actual result changes a word and preserves context. -/
namespace Solidity.Backend.StorageOps.ProducerInterfaceControls
open TypeGraph Solidity.Storage Solidity.Storage.Representation Solidity.Storage.Representation.Graph
open ProducerInterface
abbrev graph := CopyDemandControls.graph
def root : Value graph (.prim .bool) := .prim true
def path : TypeGraph.Path graph (.prim .bool) (.prim .bool) := .nil
def base : Solidity.Storage.Loc := .root 0
def word : Semantics.Word := PrimTy.toWord (p:=.bool) true
def symbolic : Store := fun _=>word
def numeric : WordStore := fun _=>word
def hash : Solidity.Storage.Pre → Nat := fun _=>0
def locations : List Solidity.Storage.Loc := [base]
def queries : List (Query graph (.prim .bool)) := [.word path]
def before : Evm.Machine :=
 {stack:=[.val ⟨23,by decide⟩],store:=Evm.WordStore.zero,mem:=fun _=>.val ⟨31,by decide⟩,
  bal:=fun _=>19,bal₀:=fun _=>19,self:=⟨7,by decide⟩,caller:=⟨13,by decide⟩,
  callvalue:=⟨0,by decide⟩,timestamp:=⟨53,by decide⟩,accepts:=fun _ _=>false}
def after : Evm.Machine := {before with store:=Evm.WordStore.write before.store (.root 0) (TargetOperations.encodeWord word).val}
def code := TargetOperations.writeCode (.root 0) word

def path_endpoint : PathEndpoint path base (.root 0) where
 supported := True.intro
 fits := True.intro
 image := rfl

def state_endpoint : StateEndpoint (N:=8) (L:=1) (R:=1) root queries base hash [] locations symbolic numeric after where
 represented := by
   intro q member
   have equal : q=Query.word path := List.mem_singleton.mp member
   subst q
   refine ⟨True.intro,True.intro,?_⟩
   intro value observed
   have same : word=value := Option.some.inj observed
   exact same
 run := by
   constructor
   · intro p; change 0<8; decide
   · decide
   · decide
   · exact Solidity.Hash.RegionsDisjoint.nil
   · intro l member
     have equal : l=base := List.mem_singleton.mp member
     subst l
     simp only [base,Solidity.Storage.Loc.Bounded]
     decide
   · intro l member p occurs
     have equal : l=base := List.mem_singleton.mp member
     subst l
     cases occurs
 transport := by intro l member; rfl
 covered := by
   intro q member
   have equal : q=Query.word path := List.mem_singleton.mp member
   subst q
   exact List.mem_singleton_self _
 fitting := by
   intro l member
   have equal : l=base := List.mem_singleton.mp member
   subst l
   exact True.intro
 observations := by
   intro l member
   have equal : l=base := List.mem_singleton.mp member
   subst l
   rfl

def reached_endpoint : ReachedEndpoint (N:=8) (L:=1) (R:=1)
 root queries base hash [] locations symbolic numeric code before after where
 state := state_endpoint
 execution := TargetOperations.run_write (.root 0) word before

/-- Inhabited target equation has the exact public LocationStepPremise field
signature, without importing its Source-dependent module into StorageOps. -/
theorem compatible_execution : Evm.run code before=.ok after 0 := reached_endpoint.execution

theorem changed_and_context :
 (before.store (.root 0),after.store (.root 0),after.stack,after.mem 0,after.self,after.caller,after.timestamp)=
 (0,1,before.stack,before.mem 0,before.self,before.caller,before.timestamp) := by rfl

/-- info: 'Solidity.Backend.StorageOps.ProducerInterfaceControls.reached_endpoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms reached_endpoint
/-- info: 'Solidity.Backend.StorageOps.ProducerInterfaceControls.compatible_execution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms compatible_execution
/-- info: 'Solidity.Backend.StorageOps.ProducerInterfaceControls.changed_and_context' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms changed_and_context
end Solidity.Backend.StorageOps.ProducerInterfaceControls
