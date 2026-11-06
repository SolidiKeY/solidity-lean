import Solidity.Lowering.StorageOps.SourceWordCommutation
import Solidity.Lowering.StorageOps.SourceWordWriteControls
open Solidity Solidity.Lowering.StorageOps
/-! Heterogeneous captured writes with nonempty locals and journal prefix.
Complete ordered snapshots distinguish world commutation from journal/state
commutation; overlap changes the world. Undo is invoked explicitly, never
inferred from an error. No target/compiler/admission extension is claimed. -/
namespace Solidity.Lowering.StorageOps.SourceWordCommutationControls
abbrev uintSyntax := SourceWordWriteControls.uintSyntax
def unit : Source.Syn .unit := .unit (.cons (.contract false "C" .none .nil
 (.cons (.stateVar uintSyntax none none none false "left" .none)
  (.cons (.stateVar (.elem .bool) none none none false "flag" .none)
   (.cons (.stateVar uintSyntax none none none true "scratch" .none)
    (.cons (.stateVar uintSyntax none none none false "sentinel" .none) .nil))))) .nil)
def env : Source.Env := unit.env
def left : Source.SPath := ⟨⟨some "C","left"⟩,[]⟩
def flag : Source.SPath := ⟨⟨some "C","flag"⟩,[]⟩
def scratch : Source.SPath := ⟨⟨some "C","scratch"⟩,[]⟩
def sentinel : Source.SPath := ⟨⟨some "C","sentinel"⟩,[]⟩
def address : Roadmap.Address := ⟨7,by decide⟩
def storage : Source.Storage env.layout env.cellTy :=
 (((Source.Storage.empty : Source.Storage env.layout env.cellTy).write left (.int 11 (by decide))).write flag (.bool false)).write sentinel (.int 97 (by decide))
def state : Source.St env :=
 {ex:={world:=⟨fun a=>if a=address then {balance:=⟨19,by decide⟩,nonce:=3,code:=some 0,storage:=storage} else Source.Account.empty _⟩
       transient:=Source.Transient.empty.set address ((Source.Storage.empty : Source.Storage env.layout env.cellTy).write scratch (.int 41 (by decide)))
       journal:=[]}
  heap:=Source.Heap.empty,events:=[],logs:=[],fnLocals:=⟨[.bool],.cons (.bool false) .nil⟩}
def frame : Source.Fr := {this:=address,sender:=⟨13,by decide⟩,value:=⟨0,by decide⟩,static:=false,contract:="C"}
def v : Source.Val env.layout (env.cellTy left) := .int 83 (by decide)
def w : Source.Val env.layout (env.cellTy flag) := .bool true
def x : Source.Val env.layout (env.cellTy left) := .int 89 (by decide)
def seedValue : Source.Val env.layout (env.cellTy sentinel) := .int 101 (by decide)
def seed := SourceWordWrite.after frame sentinel seedValue state
def Γ : Source.RCtx := [.bool,.int Source.IntTy.u256]
def locals : Source.Locals env.layout Γ := .cons (.bool true) (.cons (.int 73 (by decide)) .nil)
def forwardState := SourceWordWrite.after frame flag w (SourceWordWrite.after frame left v seed)
def reverseState := SourceWordWrite.after frame left v (SourceWordWrite.after frame flag w seed)
def forward := (SourceWordCommutation.two (E:=env) (Γ:=Γ) frame left v flag w).run (locals,seed)
def reverse := (SourceWordCommutation.two (E:=env) (Γ:=Γ) frame flag w left v).run (locals,seed)

def forward_certificate := SourceWordCommutation.run frame left v flag w locals seed rfl rfl rfl
def reverse_certificate := SourceWordCommutation.run frame flag w left v locals seed rfl rfl rfl
def world_certificate := SourceWordCommutation.world_commute env frame left flag v w seed (by decide)
def journal_forward := SourceWordCommutation.journal_order frame left v flag w seed
def journal_reverse := SourceWordCommutation.journal_order frame flag w left v seed


def seed_certificate := SourceWordWrite.source_write frame sentinel seedValue locals state rfl rfl

def wordOf (st : Source.Storage env.layout env.cellTy) (p : Source.SPath) := (st.read p).bind Source.Val.word |>.map Fin.val

def entryView : Source.Entry env.layout env.lay env.lay →
 Bool × Nat × List (Option Nat) × Option (Nat × Nat × Option Nat)
 | .account a old => (true,a.val,[wordOf old.storage left,wordOf old.storage flag,wordOf old.storage sentinel],some (old.balance.val,old.nonce,old.code))
 | .transient a old => (false,a.val,[wordOf old left,wordOf old flag,wordOf old sentinel],none)
def journalView (s : Source.St env) := s.ex.journal.map entryView
def view (s : Source.St env) :=
 ([wordOf (s.ex.world.accounts address).storage left,wordOf (s.ex.world.accounts address).storage flag,wordOf (s.ex.world.accounts address).storage sentinel],
 wordOf (s.ex.transient.cells address) scratch,s.ex.journal.length,(s.ex.world.accounts address).balance.val,
 (s.ex.world.accounts address).nonce,(s.ex.world.accounts address).code,
 s.heap.next,(s.heap.cells 0).isNone,s.events.length,s.logs.length,s.fnLocals.1)

def ordered : Prop :=
 (forward,reverse,view seed,view forward.2.2,view reverse.2.2,journalView forward.2.2,journalView reverse.2.2) =
 ((.ok (), (locals,forwardState)),(.ok (), (locals,reverseState)),
 ([some 11,some 0,some 101],some 41,1,19,3,some 0,0,true,0,0,[.bool]),
 ([some 83,some 1,some 101],some 41,3,19,3,some 0,0,true,0,0,[.bool]),
 ([some 83,some 1,some 101],some 41,3,19,3,some 0,0,true,0,0,[.bool]),
 [(true,7,[some 83,some 0,some 101],some (19,3,some 0)),
  (true,7,[some 11,some 0,some 101],some (19,3,some 0)),
  (true,7,[some 11,some 0,some 97],some (19,3,some 0))],
 [(true,7,[some 11,some 1,some 101],some (19,3,some 0)),
  (true,7,[some 11,some 0,some 101],some (19,3,some 0)),
  (true,7,[some 11,some 0,some 97],some (19,3,some 0))])

theorem observations : ordered := by
 rfl

theorem world_equal : forward.2.2.ex.world=reverse.2.2.ex.world := by
 unfold forward reverse
 rw [forward_certificate,reverse_certificate]
 exact world_certificate

theorem journals_differ : forward.2.2.ex.journal≠reverse.2.2.ex.journal := by
 intro same
 have observed := congrArg (fun journal => (journal.map entryView).head?.bind
   (fun row => row.2.2.1.head?.getD none)) same
 change (some 83 : Option Nat)=some 11 at observed
 have different : (some 83 : Option Nat)≠some 11 := by decide
 exact different observed

def overlapForward := (SourceWordCommutation.two (E:=env) (Γ:=Γ) frame left v left x).run (locals,seed)
def overlapReverse := (SourceWordCommutation.two (E:=env) (Γ:=Γ) frame left x left v).run (locals,seed)
def leftWord (world : Source.World env.layout env.lay) := wordOf (world.accounts address).storage left

theorem overlap_observations :
 (leftWord overlapForward.2.2.ex.world,leftWord overlapReverse.2.2.ex.world)=(some 89,some 83) := by rfl

theorem overlap_worlds_differ : overlapForward.2.2.ex.world≠overlapReverse.2.2.ex.world := by
 intro same
 have different : leftWord overlapForward.2.2.ex.world≠leftWord overlapReverse.2.2.ex.world := by decide
 exact different (congrArg leftWord same)
theorem states_differ : forward.2.2≠reverse.2.2 := by
 intro same
 exact journals_differ (congrArg (fun s => s.ex.journal) same)

theorem explicit_undo :
 Source.ExecState.undoN 2 forward.2.2.ex=seed.ex ∧
 Source.ExecState.undoN 2 reverse.2.2.ex=seed.ex := by
 unfold forward reverse
 rw [forward_certificate,reverse_certificate]
 exact ⟨Source.ExecState.undoN_run seed.ex [SourceWordWrite.op frame left v,SourceWordWrite.op frame flag w],
   Source.ExecState.undoN_run seed.ex [SourceWordWrite.op frame flag w,SourceWordWrite.op frame left v]⟩
end Solidity.Lowering.StorageOps.SourceWordCommutationControls














/-- info: 'Solidity.Lowering.StorageOps.SourceWordCommutationControls.seed_certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Lowering.StorageOps.SourceWordCommutationControls.seed_certificate

/-- info: 'Solidity.Lowering.StorageOps.SourceWordCommutationControls.forward_certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Lowering.StorageOps.SourceWordCommutationControls.forward_certificate

/-- info: 'Solidity.Lowering.StorageOps.SourceWordCommutationControls.reverse_certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Lowering.StorageOps.SourceWordCommutationControls.reverse_certificate

/-- info: 'Solidity.Lowering.StorageOps.SourceWordCommutationControls.world_certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Lowering.StorageOps.SourceWordCommutationControls.world_certificate

/-- info: 'Solidity.Lowering.StorageOps.SourceWordCommutationControls.journal_forward' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Lowering.StorageOps.SourceWordCommutationControls.journal_forward

/-- info: 'Solidity.Lowering.StorageOps.SourceWordCommutationControls.journal_reverse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Lowering.StorageOps.SourceWordCommutationControls.journal_reverse

/-- info: 'Solidity.Lowering.StorageOps.SourceWordCommutationControls.observations' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Lowering.StorageOps.SourceWordCommutationControls.observations

/-- info: 'Solidity.Lowering.StorageOps.SourceWordCommutationControls.world_equal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Lowering.StorageOps.SourceWordCommutationControls.world_equal

/-- info: 'Solidity.Lowering.StorageOps.SourceWordCommutationControls.journals_differ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Lowering.StorageOps.SourceWordCommutationControls.journals_differ

/-- info: 'Solidity.Lowering.StorageOps.SourceWordCommutationControls.overlap_observations' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Lowering.StorageOps.SourceWordCommutationControls.overlap_observations

/-- info: 'Solidity.Lowering.StorageOps.SourceWordCommutationControls.overlap_worlds_differ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Lowering.StorageOps.SourceWordCommutationControls.overlap_worlds_differ

/-- info: 'Solidity.Lowering.StorageOps.SourceWordCommutationControls.states_differ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Lowering.StorageOps.SourceWordCommutationControls.states_differ

/-- info: 'Solidity.Lowering.StorageOps.SourceWordCommutationControls.explicit_undo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Lowering.StorageOps.SourceWordCommutationControls.explicit_undo
