import Solidity.Lowering.StorageOps.SourceByteStorageCopy

/-! Actual byte-cell operations. These controls do not assert packed layout,
whole storRef-copy cleanup, or rollback. -/
namespace Solidity.Lowering.StorageOps.SourceByteStorageCopyControls
open Solidity
open SourceByteStorageCopy

def unit : Source.Syn .unit := .unit (.cons (.contract false "C" .none .nil
 (.cons (.stateVar (.elem .bytes) none none none false "values" .none) .nil)) .nil)
def env : Source.Env := unit.env
def path : Source.SPath := ⟨⟨some "C","values"⟩,[]⟩
def child (i : Nat) := path.go (.index i)
def address : Roadmap.Address := ⟨7,by decide⟩
def frame : Source.Fr := {this:=address,sender:=⟨13,by decide⟩,value:=⟨0,by decide⟩,static:=false,contract:="C"}
def byte (n : UInt8) : Source.Val env.layout (.fixedBytes 1 (by decide)) := .fixedBytes [n] rfl
def storage : Source.Storage env.layout env.cellTy :=
 let s := (Source.Storage.empty : Source.Storage env.layout env.cellTy).write path (.int 2 (by decide))
 let s := s.write (child 0) (byte 41)
 let s := s.write (child 1) (byte 53)
 let s := s.write (child 2) (byte 59)
 s.write (child 4) (byte 97)
def state : Source.St env :=
 {ex:={world:=⟨fun a=>if a=address then
   {balance:=19,nonce:=3,code:=some 0,storage:=storage}
   else Source.Account.empty _⟩,transient:=Source.Transient.empty,journal:=[]}
  heap:=Source.Heap.empty,events:=[],logs:=[(address,[9,8])],fnLocals:=⟨[],.nil⟩}
def initial : Source.Locals env.layout [] × Source.St env := (.nil,state)
def run (fuel : Nat) := (Source.storeBytes (E:=env) (Γ:=[]) frame fuel path 1 [7,17]).run initial
def typed (j : Nat) : (.fixedBytes 1 (by decide) : Source.STy)=env.cellTy (child j) := rfl
def after (bs : List UInt8) : Source.St env :=
 {state with ex:=state.ex.run (byteWrites frame path typed 1 bs)}
def outcomes : Prop :=
 (run 0,run 1,run 2,run 3)=
 ((.error .timeout,initial),(.error .timeout,(.nil,after [7])),
  (.error .timeout,(.nil,after [7,17])),(.ok (),( .nil,after [7,17])))
def raw (s : Source.St env) (j : Nat) :=
 match (s.ex.world.accounts address).storage.cell (child j) with
 | some (.fixedBytes bs _) => some (bs.map UInt8.toNat)
 | _ => none
def view (s : Source.St env) :=
 ([0,1,2,3,4].map (raw s),s.ex.journal.length,
  (s.ex.world.accounts address).balance,(s.ex.world.accounts address).nonce,
  (s.ex.world.accounts address).code,s.heap.next,s.events.length,
  s.logs.map (fun (a,bs)=>(a.val,bs.map UInt8.toNat)))
def ordered : Prop := [run 0,run 1,run 2,run 3].map (fun r=>view r.2.2)=
 [([some [41],some [53],some [59],none,some [97]],0,19,3,some 0,0,0,[(7,[9,8])]),
  ([some [41],some [7],some [59],none,some [97]],1,19,3,some 0,0,0,[(7,[9,8])]),
  ([some [41],some [7],some [17],none,some [97]],2,19,3,some 0,0,0,[(7,[9,8])]),
  ([some [41],some [7],some [17],none,some [97]],2,19,3,some 0,0,0,[(7,[9,8])])]
def boundaries : Prop :=
 ((Source.storeBytes (E:=env) (Γ:=[]) frame 0 path 1 []).run initial,
  (Source.storeBytes (E:=env) (Γ:=[]) frame 1 path 1 []).run initial,
  (Source.storeBytes (E:=env) (Γ:=[]) {frame with static:=true} 3 path 1 [7,17]).run initial,
  (Source.loadBytes (E:=env) (Γ:=[]) frame 3 path 1 2).run initial,
  (Source.loadBytes (E:=env) (Γ:=[]) frame 2 path 1 2).run initial)=
 ((.error .timeout,initial),(.ok (),initial),(.error (.revert []),initial),
  (.ok [53,59],initial),(.error .timeout,initial))
/-- The general producer is inhabited at an arbitrary original fuel. -/
def write_client (fuel : Nat) := store_bytes_fuel frame rfl path fuel 1 [7,17] typed
 (Source.Locals.nil : Source.Locals env.layout []) state
def capture_client := load_bytes frame path 1 2 0
 (fun j=>if j=1 then 53 else 59) initial (by
  intro j member
  have cases : j=0 ∨ j=1 := by omega
  rcases cases with rfl | rfl <;> rfl)
def journalRows (s : Source.St env) := s.ex.journal.map fun e=>
 match e with
 | .account a old => (a.val,[0,1,2,3,4].map (fun j=>
    match old.storage.cell (child j) with
    | some (.fixedBytes bs _) => some (bs.map UInt8.toNat)
    | _ => none),old.balance,old.nonce,old.code)
 | .transient a _ => (a.val,[],0,0,none)
def journals : Prop := [run 0,run 1,run 2,run 3].map (fun r=>journalRows r.2.2)=
 [[],[(7,[some [41],some [53],some [59],none,some [97]],19,3,some 0)],
  [(7,[some [41],some [7],some [59],none,some [97]],19,3,some 0),
   (7,[some [41],some [53],some [59],none,some [97]],19,3,some 0)],
  [(7,[some [41],some [7],some [59],none,some [97]],19,3,some 0),
   (7,[some [41],some [53],some [59],none,some [97]],19,3,some 0)]]
def missing : Source.SPath := ⟨⟨some "C","missing"⟩,[]⟩
def refusals : Prop :=
 ((Source.storeBytes (E:=env) (Γ:=[]) frame 2 missing 0 [7]).run initial,
  (Source.loadBytes (E:=env) (Γ:=[]) frame 2 missing 0 1).run initial)=
 ((.error (.stuck "storage cell type"),initial),
  (.error (.stuck "storage cell without a value"),initial))
theorem journal_observations : journals := by rfl
theorem refusal_observations : refusals := by rfl
theorem outcome_certificate : outcomes := by rfl
theorem observations : ordered := by rfl
theorem boundary_certificate : boundaries := by rfl
/-- info: 'Solidity.Lowering.StorageOps.SourceByteStorageCopyControls.outcome_certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms outcome_certificate
/-- info: 'Solidity.Lowering.StorageOps.SourceByteStorageCopyControls.observations' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms observations
/-- info: 'Solidity.Lowering.StorageOps.SourceByteStorageCopyControls.boundary_certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms boundary_certificate
/-- info: 'Solidity.Lowering.StorageOps.SourceByteStorageCopyControls.write_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms write_client
/-- info: 'Solidity.Lowering.StorageOps.SourceByteStorageCopyControls.capture_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms capture_client
/-- info: 'Solidity.Lowering.StorageOps.SourceByteStorageCopyControls.journal_observations' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms journal_observations
/-- info: 'Solidity.Lowering.StorageOps.SourceByteStorageCopyControls.refusal_observations' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms refusal_observations
end Solidity.Lowering.StorageOps.SourceByteStorageCopyControls
