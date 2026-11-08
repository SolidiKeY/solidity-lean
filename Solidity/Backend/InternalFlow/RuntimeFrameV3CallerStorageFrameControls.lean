import Solidity.Backend.InternalFlow.RuntimeFrameV3CallerStorageFrame

/-! An indexed storage alias remains live across real private allocation and
memory mutation. The fixed outer array supplies an actual inhabited fragile
alias; an out-of-bounds alternative is rejected. No world/rollback claim. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.CallerStorageFrame.Controls
open Evm Evm.Memory RecursiveSource

def C : Contract := contract!{ uint[][1] rows; }
abbrev A : RefTy := .array (.prim .uint)
abbrev Γ : Ctx := [.alias A]
def F : Frag Γ := (Frag.init []).push (.alias A) .fragile

def root : SRef C (.ref (.fixed (.ref A) 1)) := SRef.ofRoot "rows" rfl
def alias : SRef C (.ref A) := root.index (.arr .fixed) (countValue 0 W_pos)
def slot : Slot := (rootSlot C "rows").add 0

theorem path : PathSlot C false alias slot := PathSlot.felem (PathSlot.root (C:=C) rfl) (by decide)
theorem live : (Storage.init C).findLive alias=some (SVal.dflt (.ref A)) := by with_unfolding_all rfl

def caller := (State.init C).push (t:=.alias A) (some alias)
def base : Nat → Fin W := fun _ => wmod 0
def blank : Machine := {Machine.init with stack:=[w[77]],mem:=fun a => if a=0 then w[32] else w[0]}
def before := writeMachine blank 1 (.slot slot)

theorem no_ref {R : RefTy} (r : HRef [] R) : False := by
 simpa only [List.getElem?_nil,reduceCtorEq] using r.get?

theorem initial : StateRepr 1 1 16 F caller base before := by
 have hc := ((Sim.init C 0 W_pos (fun _ => 0) ⟨0,W_pos⟩ rfl).congrMem
   (mem:=blank.mem) (by intro l lo hi;simp only [List.length_nil,Nat.add_zero] at hi;omega)).stack [w[77]]
 refine ⟨?_,⟨fun r => (no_ref r).elim,fun r => (no_ref r).elim,fun r _ _ => (no_ref r).elim⟩,
   ?_,by decide,⟨fun r => (no_ref r).elim,fun r => (no_ref r).elim,fun r => (no_ref r).elim⟩,
   (fun _ r => (no_ref r).elim),RefFieldsRepr.withoutStructs _ _ _ (fun r => no_ref r)⟩
 · refine ⟨hc.store,?_,?_,hc.net,hc.netSelf,hc.bound,?_,hc.env,hc.funds,hc.oracle⟩
   · intro p i;cases i with | there i => cases i
   · intro R i flag;cases i with
     | here => cases flag
     | there i => cases i
   · intro R i flag;cases i with
     | here => exact ⟨alias,slot,rfl,rfl,path,_,live⟩
     | there i => cases i
 · intro R i;cases i with | there i => cases i

def child := caller.withEnv (Δ:=[]) ()

theorem child_initial : StateRepr 1 5 16 (Frag.init []) child base before := by
 refine ⟨?_,initial.heap,?_,by decide,initial.structs,initial.separated,initial.refs⟩
 · exact ⟨initial.core.store,(fun i => nomatch i),(fun i => nomatch i),initial.core.net,initial.core.netSelf,
     initial.core.bound,(fun i => nomatch i),initial.core.env,initial.core.funds,initial.core.oracle⟩
 · intro R i;nomatch i

theorem allocator : StructAllocatorRepr child.heap base 16 (⟨32,by decide⟩ : Fin W) before := by
 refine AllocatorRepr.withoutStructs ?_ (fun r => no_ref r)
 refine ⟨initial.heap,?_,fun r => (no_ref r).elim⟩
 refine ⟨by decide,by decide,rfl,?_⟩
 intro x high
 change 32≤x at high
 simp only [before,writeMachine,upd,blank,if_neg (show x≠1 by omega),if_neg (show x≠0 by omega)]

def size : Fin W := ⟨1,by decide⟩
def allocate : Stmt C [] [.mem A] := .declMem A (.user "private") (some (.newArr (.lit 1 rfl) rfl)) rfl rfl
def allocated := child.allocPush (defaultArray .uint size)
def ref : HRef allocated.H A := ⟨0,rfl⟩
def addresses := upd base 0 (⟨32,by decide⟩ : Fin W)
def middle := writeMachine (allocateMachine before (⟨32,by decide⟩ : Fin W) size) 5 w[32]
def post := allocated.withHeap (allocated.heap.set ref (MObj.setElem .dyn (allocated.heap.get ref) 0 (countValue 7 (by decide))))
def after := writeMachine middle 33 w[7]
def write : Stmt C [.mem A] [.mem A] :=
 .assignMem (.index .dyn (.var .here rfl) (.simple (.lit 0 rfl))) (.val (.simple (.lit 7 rfl)))
def body : Prog C [] [.mem A] := .cons allocate (.cons write .nil)
def compiled : CompiledProg 5 (Frag.init []) body := (Memory.compileProg 5 (Frag.init []) body).get (by rfl)

theorem public_root : Memory.compileProg 5 (Frag.init []) body=some compiled := by rfl

theorem allocated_repr : StateRepr 1 5 16 ((Frag.init []).push (.mem A) .ok) allocated addresses middle :=
 (newArray_correct child_initial allocator (by decide) .uint (.lit 1 rfl) rfl size rfl (by decide) (by decide)).2.2.1

theorem allocated_live : 0<allocated.heap.len ref .dyn := by with_unfolding_all decide

theorem reached : StateRepr 1 5 16 compiled.frag post addresses after :=
 allocated_repr.set ref 0 allocated_live (countValue 7 (by decide)) w[7] (ReprV.uint_of rfl)

def writeCompiled : CompiledStmt 5 ((Frag.init []).push (.mem A) .ok) write :=
 (Memory.compileStmt 5 ((Frag.init []).push (.mem A) .ok) write).get (by rfl)

theorem code_eq : compiled.code=declareNewCode (C:=C) (Γ:=[]) 5 (.lit 1 rfl)++writeCompiled.code := by rfl

theorem target : run compiled.code before=.ok after 0 := by
 have allocation := (newArray_correct child_initial allocator (by decide) .uint (.lit 1 rfl) rfl size rfl (by decide) (by decide)).2.1
 obtain ⟨word,encoded,wrote,executed,represented,exterior⟩ := Footprint.write_local allocated_repr
   .here ref rfl (.simple (.lit 0 rfl)) (.simple (.lit 7 rfl))
   ⟨_,.core _ rfl⟩ ⟨_,.core _ rfl⟩ (⟨0,by decide⟩ : Fin W) rfl
   (countValue 7 (by decide)) rfl allocated_live 0
 have word_eq : word=w[7] := Restored.value_unique encoded (ReprV.uint_of rfl)
 rw [word_eq] at executed
 rw [code_eq,run_append_ok allocation]
 exact executed

theorem source : body.run child=.ok ⟨post,List.prefix_append _ _⟩ := by with_unfolding_all rfl

theorem storage : post.storage=caller.storage := by rfl

theorem extended : BaseExtends caller.H base addresses := fun r => (no_ref r).elim

theorem caller_words : ∀ {t : LTy} (i : Idx Γ t),after.mem (cellOf 1 i)=before.mem (cellOf 1 i) := by
 intro t i;cases i with
 | here => rfl
 | there i => cases i

noncomputable def output := post.withEnv (TEnv.wk (List.prefix_append caller.H [A]) Γ caller.env)

def call : Stmt C Γ Γ := .call "fragilePrivate" .nil .none body

theorem call_source : call.run caller=.ok ⟨output,List.prefix_append caller.H [A]⟩ :=
 call_return .nil .none body.ext body.runR caller () rfl ⟨post,List.prefix_append _ _⟩ source

theorem restored : StateRepr 1 1 16 F output addresses after :=
 reframe caller post (List.prefix_append caller.H [A]) base addresses before after initial reached extended caller_words storage

theorem fragile_observed :
 ∃ r s,Look.ofTEnv output.env (.here : Idx Γ (.alias A))=some r ∧ after.mem 1=.slot s ∧
 PathSlot C false r s ∧ ∃ v,output.storage.findLive r=some v := restored.core.fragile .here rfl

theorem observations :
 (after.stack,[after.mem 0,after.mem 1,after.mem 5,after.mem 32,after.mem 33])=
 ([w[77]],[w[34],.slot slot,w[32],w[1],w[7]]) := by rfl

def invalid := root.index (.arr .fixed) (countValue 1 (by decide))
theorem wrong_liveness : (Storage.init C).findLive invalid=none := by with_unfolding_all rfl

theorem wrong_alias : Look.ofTEnv output.env (.here : Idx Γ (.alias A))≠some invalid := by
 intro equal
 have same : alias=invalid := Option.some.inj equal
 have liveWrong := live
 rw [same,wrong_liveness] at liveWrong
 cases liveWrong

end Solidity.Backend.InternalFlow.RuntimeFrame.CallerStorageFrame.Controls

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.CallerStorageFrame.Controls.path' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.CallerStorageFrame.Controls.path

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.CallerStorageFrame.Controls.live' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.CallerStorageFrame.Controls.live

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.CallerStorageFrame.Controls.no_ref' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.CallerStorageFrame.Controls.no_ref

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.CallerStorageFrame.Controls.initial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.CallerStorageFrame.Controls.initial

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.CallerStorageFrame.Controls.child_initial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.CallerStorageFrame.Controls.child_initial

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.CallerStorageFrame.Controls.allocator' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.CallerStorageFrame.Controls.allocator

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.CallerStorageFrame.Controls.public_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.CallerStorageFrame.Controls.public_root

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.CallerStorageFrame.Controls.allocated_repr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.CallerStorageFrame.Controls.allocated_repr

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.CallerStorageFrame.Controls.allocated_live' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.CallerStorageFrame.Controls.allocated_live

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.CallerStorageFrame.Controls.reached' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.CallerStorageFrame.Controls.reached

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.CallerStorageFrame.Controls.code_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.CallerStorageFrame.Controls.code_eq

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.CallerStorageFrame.Controls.target' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.CallerStorageFrame.Controls.target

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.CallerStorageFrame.Controls.source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.CallerStorageFrame.Controls.source

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.CallerStorageFrame.Controls.storage' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.CallerStorageFrame.Controls.storage

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.CallerStorageFrame.Controls.extended' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.CallerStorageFrame.Controls.extended

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.CallerStorageFrame.Controls.caller_words' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.CallerStorageFrame.Controls.caller_words

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.CallerStorageFrame.Controls.call_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.CallerStorageFrame.Controls.call_source

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.CallerStorageFrame.Controls.restored' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.CallerStorageFrame.Controls.restored

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.CallerStorageFrame.Controls.fragile_observed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.CallerStorageFrame.Controls.fragile_observed

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.CallerStorageFrame.Controls.observations' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.CallerStorageFrame.Controls.observations

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.CallerStorageFrame.Controls.wrong_liveness' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.CallerStorageFrame.Controls.wrong_liveness

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.CallerStorageFrame.Controls.wrong_alias' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.CallerStorageFrame.Controls.wrong_alias
