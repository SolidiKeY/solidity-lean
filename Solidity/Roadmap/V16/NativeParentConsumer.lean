import Solidity.Backend.InternalFlow.RuntimeFrameV3MutatingActivation
import Solidity.Calculus.Correct
import Solidity.Calculus.LowerRun

/-! Scoped specification consumers for actual published native allocating-call
return certificates. No Source admission, recursive selection or EVM claim. -/
namespace Solidity.Roadmap.V16.NativeParentConsumer
open Solidity.Backend.InternalFlow.RuntimeFrame
open Evm Evm.Memory RecursiveSource RecursiveActivation GuardedRecursion GuardedPrefixes
open CountdownWitness

abbrev A : RefTy := CountdownWitness.A

def counterSpec {C : Contract} (n : Nat) (fit : n<W) : Spec C (Parameters A) :=
 .eq (.pvV .here) (.lit (countValue n fit))

def program {C : Contract} (n : Nat) : Prog C (Parameters A) (Parameters A) :=
 .cons (.call "allocatingCountdown" (nextArgs A rfl) .none (AllocatingActivation.body (n+1))) .nil

def observe (m : Machine) : List Word × List Word :=
 (m.stack,[m.mem 0,m.mem 1,m.mem 2,m.mem 3,m.mem 7,m.mem 8,m.mem 9,
  m.mem 10,m.mem 11,m.mem 12,m.mem 13,m.mem 16,m.mem 17,m.mem 18,m.mem 20,m.mem 21])

def expected (n : Nat) : List Word × List Word :=
 ([w[77]],[w[30],w[16],w[16],.val (wmod (n+1)),w[10],.val (wmod (10+2*(2-(n+1)))),w[99],
  w[16],w[2],w[16],w[1],w[2],w[7],w[9],w[1],w[4]])


/-- The actual recovered native caller counter, not the child counter. -/
theorem returned_counter : ∀ (n : Nat) (small : n+1≤2),
 Solidity.Spec.sat (Solidity.Backend.InternalFlow.RuntimeFrame.NativeUnwind.Checks.output n small).st
 (Solidity.Roadmap.V16.NativeParentConsumer.counterSpec (n+1) (Nat.lt_of_le_of_lt small (by decide : 2<Solidity.Evm.W))) := by
  intro n small
  have bindings := (Solidity.Backend.InternalFlow.RuntimeFrame.NativeUnwind.Checks.source_facts n small).2.2.2.2.1
  have scalar := congrArg (fun pair : Int × Option Nat => pair.1) bindings
  change ∃ v, some ((Solidity.Backend.InternalFlow.RuntimeFrame.NativeUnwind.Checks.output n small).st.env.1) = some v ∧ some (Solidity.Backend.InternalFlow.RuntimeFrame.RecursiveSource.countValue (n+1) (Nat.lt_of_le_of_lt small (by decide : 2<Solidity.Evm.W))) = some v
  refine ⟨_,?_,rfl⟩
  exact congrArg some (Subtype.ext scalar)


/-- Actual native source/target prefixes and caller-return specs from the
published Entry, with no new source-success, simulation or exhaustion premise.
This is only the allocating-countdown family, not full recursive selection. -/
theorem parent_specification : ∀ {C : Solidity.Contract} {b lo L frame : Nat} {F : Solidity.Evm.Frag (Solidity.Backend.InternalFlow.RuntimeFrame.RecursiveSource.Parameters Solidity.Roadmap.V16.NativeParentConsumer.A)}
 (σ : Solidity.State C (Solidity.Backend.InternalFlow.RuntimeFrame.RecursiveSource.Parameters Solidity.Roadmap.V16.NativeParentConsumer.A)) (base : Nat → Fin Solidity.Evm.W) (before : Solidity.Evm.Machine) (start : Nat)
 (_entry : Solidity.Backend.InternalFlow.RuntimeFrame.InterfaceV1.Entry (Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingEmission.plan (C:=C) b lo F) L b frame F σ base before start)
 (_reads : (Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingEmission.counter σ).val≤Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingEmission.length σ) (n : Nat) (small : n+1≤(Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingEmission.counter σ).val),
 ∃ (ref : Solidity.HRef σ.H Solidity.Roadmap.V16.NativeParentConsumer.A) (η τ : Solidity.State C (Solidity.Backend.InternalFlow.RuntimeFrame.RecursiveSource.Parameters Solidity.Roadmap.V16.NativeParentConsumer.A)) (ep : σ.H <+: η.H) (ef : σ.H <+: τ.H)
 (entered mid down last : Solidity.Evm.Machine) (prefixAddresses addresses : Nat → Fin Solidity.Evm.W)
 (out : Solidity.Out C (Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingActivation.allocated η).H (Solidity.Backend.InternalFlow.RuntimeFrame.RecursiveSource.Parameters Solidity.Roadmap.V16.NativeParentConsumer.A)),
 Solidity.TEnv.get (.there .here : Solidity.Idx (Solidity.Backend.InternalFlow.RuntimeFrame.RecursiveSource.Parameters Solidity.Roadmap.V16.NativeParentConsumer.A) (.mem Solidity.Roadmap.V16.NativeParentConsumer.A)) σ.env=some ref ∧
 Solidity.Evm.run (Solidity.Backend.InternalFlow.RuntimeFrame.RecursiveIngress.code lo (lo-1)) before=.ok entered 0 ∧
 Solidity.Evm.loopIterN (Solidity.Evm.run (Solidity.Backend.InternalFlow.RuntimeFrame.RecursiveActivation.guardCompiled (C:=C) b F).code)
   (Solidity.Evm.run (Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingActivation.code (C:=C) b F lo)) ((Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingEmission.counter σ).val-(n+1)) entered=.inl mid ∧
 Solidity.Evm.Memory.StateRepr L b frame F η prefixAddresses mid ∧
 η.env=(Solidity.Backend.InternalFlow.RuntimeFrame.RecursiveSource.countValue (n+1) (Nat.lt_of_le_of_lt small (Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingEmission.counter σ).isLt),(some (ref.wk ep),())) ∧
 η.H.length=σ.H.length+((Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingEmission.counter σ).val-(n+1)) ∧ Solidity.Heap.Keeps ep σ.heap η.heap ∧
 Solidity.Evm.Memory.BaseExtends σ.H base prefixAddresses ∧
 Solidity.Evm.Memory.GrowsAllocator b frame (4*((Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingEmission.counter σ).val-(n+1))) σ base before η prefixAddresses mid ∧
 Solidity.Evm.loopIterN (Solidity.Evm.run (Solidity.Backend.InternalFlow.RuntimeFrame.RecursiveActivation.guardCompiled (C:=C) b F).code)
   (Solidity.Evm.run (Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingActivation.code (C:=C) b F lo)) (Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingEmission.counter σ).val entered=.inl down ∧
 ((.call "allocatingCountdown" (Solidity.Backend.InternalFlow.RuntimeFrame.RecursiveSource.nextArgs Solidity.Roadmap.V16.NativeParentConsumer.A rfl) .none (Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingActivation.body (n+1)) :
   Solidity.Stmt C (Solidity.Backend.InternalFlow.RuntimeFrame.RecursiveSource.Parameters Solidity.Roadmap.V16.NativeParentConsumer.A) (Solidity.Backend.InternalFlow.RuntimeFrame.RecursiveSource.Parameters Solidity.Roadmap.V16.NativeParentConsumer.A))).run (Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingActivation.allocated η)=.ok out ∧
 out.st=Solidity.Backend.InternalFlow.RuntimeFrame.ParentPrefixes.sourceAt τ (n+1) (Nat.lt_of_le_of_lt small (Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingEmission.counter σ).isLt) ∧
 Solidity.Evm.loopIterN (Solidity.Evm.run (Solidity.Backend.InternalFlow.RuntimeFrame.PairedUnwind.condition lo (lo-1)))
   (Solidity.Evm.run (Solidity.Backend.InternalFlow.RuntimeFrame.Restore.restoreCells lo (Solidity.Backend.InternalFlow.RuntimeFrame.Restore.contextCells b (Solidity.Backend.InternalFlow.RuntimeFrame.RecursiveSource.Parameters Solidity.Roadmap.V16.NativeParentConsumer.A)))) (n+1) down=.inl last ∧
 Solidity.Evm.Memory.StateRepr L b frame F out.st addresses last ∧
 τ.env=(Solidity.Backend.InternalFlow.RuntimeFrame.RecursiveSource.countValue 0 Solidity.Evm.W_pos,(some (ref.wk ef),())) ∧
 τ.H.length=σ.H.length+(Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingEmission.counter σ).val ∧ Solidity.Heap.Keeps ef σ.heap τ.heap ∧
 last.stack=before.stack ∧ Solidity.Evm.Memory.BaseExtends σ.H base addresses ∧
 Solidity.Evm.Memory.GrowsAllocator b frame (4*(Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingEmission.counter σ).val) σ base before out.st addresses last ∧
 last.mem lo=.val (Solidity.Evm.wmod (start+2*((Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingEmission.counter σ).val-(n+1)))) ∧
 last.mem b=.val (base ref.id) ∧
 (Solidity.Roadmap.V16.NativeParentConsumer.program (C:=C) n).run (Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingActivation.allocated η)=.ok out ∧
 Solidity.Spec.sat out.st (Solidity.Roadmap.V16.NativeParentConsumer.counterSpec (n+1) (Nat.lt_of_le_of_lt small (Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingEmission.counter σ).isLt)) ∧
 Solidity.Spec.sat (Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingActivation.allocated η) (.box (Solidity.Roadmap.V16.NativeParentConsumer.program n) (Solidity.Roadmap.V16.NativeParentConsumer.counterSpec (n+1) (Nat.lt_of_le_of_lt small (Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingEmission.counter σ).isLt))) ∧
 Solidity.Spec.sat (Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingActivation.allocated η) (.diamond (Solidity.Roadmap.V16.NativeParentConsumer.program n) (Solidity.Roadmap.V16.NativeParentConsumer.counterSpec (n+1) (Nat.lt_of_le_of_lt small (Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingEmission.counter σ).isLt))) := by
  intro C b lo L frame F σ base before start entry reads n small
  obtain ⟨ref,η,τ,ep,ef,entered,mid,down,last,prefixAddresses,addresses,out,alias,setup,prefixRun,prefixRepr,ancestorEnv,prefixSize,prefixKept,prefixExtended,prefixGrowth,descent,native,outputView,unwinding,represented,zeroEnv,size,kept,stack,extended,growth,cursor,reference⟩ := Solidity.Backend.InternalFlow.RuntimeFrame.NativeUnwind.parent σ base before start entry reads n small
  have runP : (Solidity.Roadmap.V16.NativeParentConsumer.program (C:=C) n).run (Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingActivation.allocated η)=.ok out := by
    simp only [Solidity.Roadmap.V16.NativeParentConsumer.program, Solidity.Prog.run_cons_ok native, Solidity.Prog.run_nil, Except.map] <;> rfl
  have post : Solidity.Spec.sat out.st (Solidity.Roadmap.V16.NativeParentConsumer.counterSpec (n+1) (Nat.lt_of_le_of_lt small (Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingEmission.counter σ).isLt)) := by
    rw [outputView]
    exact ⟨Solidity.Backend.InternalFlow.RuntimeFrame.RecursiveSource.countValue (n+1) (Nat.lt_of_le_of_lt small (Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingEmission.counter σ).isLt),rfl,rfl⟩
  have boxed : Solidity.Spec.sat (Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingActivation.allocated η) (.box (Solidity.Roadmap.V16.NativeParentConsumer.program n) (Solidity.Roadmap.V16.NativeParentConsumer.counterSpec (n+1) (Nat.lt_of_le_of_lt small (Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingEmission.counter σ).isLt))) := by
    simpa only [Solidity.Spec.sat,runP] using post
  have diamond : Solidity.Spec.sat (Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingActivation.allocated η) (.diamond (Solidity.Roadmap.V16.NativeParentConsumer.program n) (Solidity.Roadmap.V16.NativeParentConsumer.counterSpec (n+1) (Nat.lt_of_le_of_lt small (Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingEmission.counter σ).isLt))) := by
    simpa only [Solidity.Spec.sat,runP] using post
  exact ⟨ref,η,τ,ep,ef,entered,mid,down,last,prefixAddresses,addresses,out,alias,setup,prefixRun,prefixRepr,ancestorEnv,prefixSize,prefixKept,prefixExtended,prefixGrowth,descent,native,outputView,unwinding,represented,zeroEnv,size,kept,stack,extended,growth,cursor,reference,runP,post,boxed,diamond⟩

/-- Fixed element one, independent of the decremented callee counter. -/
def atOne {C : Contract} : Val C (Parameters A) .uint :=
 .readMem (.index .dyn (.var (.there .here) rfl) (.simple (.lit 1 rfl)))

def elementSpec {C : Contract} (n : Nat) (fit : n<W) : Spec C (Parameters A) :=
 .eq (atOne (C:=C)).lower (.lit (countValue n fit))

theorem native_program : ∀ (n : Nat) (small : n+1≤2),
 (Solidity.Roadmap.V16.NativeParentConsumer.program (C:=Solidity.Backend.InternalFlow.RuntimeFrame.CountdownWitness.P.C) n).run (Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingActivation.allocated (Solidity.Backend.InternalFlow.RuntimeFrame.NativeUnwind.Checks.ancestor n small)) =
 .ok (Solidity.Backend.InternalFlow.RuntimeFrame.NativeUnwind.Checks.output n small) := by
  intro n small
  have native := (Solidity.Backend.InternalFlow.RuntimeFrame.NativeUnwind.Checks.source_facts n small).2.2.1
  simp only [Solidity.Roadmap.V16.NativeParentConsumer.program,Solidity.Prog.run_cons_ok native,Solidity.Prog.run_nil,Except.map] <;> rfl

theorem mutating_element : (Solidity.Roadmap.V16.NativeParentConsumer.atOne (C:=Solidity.Backend.InternalFlow.RuntimeFrame.CountdownWitness.P.C)).evalT Solidity.Backend.InternalFlow.RuntimeFrame.MutatingActivation.Checks.child =
 .ok (Solidity.Backend.InternalFlow.RuntimeFrame.RecursiveSource.countValue 2 (by decide)) := by
  change Solidity.TRes.ofOpt (Solidity.Backend.InternalFlow.RuntimeFrame.MutatingActivation.Checks.child.heap.readAddr (.index Solidity.Backend.InternalFlow.RuntimeFrame.MutatingActivation.Checks.reference .dyn (Solidity.Backend.InternalFlow.RuntimeFrame.RecursiveSource.countValue 1 (by decide)))) = _
  rw [Solidity.Backend.InternalFlow.RuntimeFrame.MutatingActivation.Checks.source_objects.2.2.1]
  rfl


theorem native_spec_iff : ∀ (n : Nat) (small : n+1≤2) (φ : Solidity.Spec Solidity.Backend.InternalFlow.RuntimeFrame.CountdownWitness.P.C (Solidity.Backend.InternalFlow.RuntimeFrame.RecursiveSource.Parameters Solidity.Roadmap.V16.NativeParentConsumer.A)),
 (Solidity.Spec.sat (Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingActivation.allocated (Solidity.Backend.InternalFlow.RuntimeFrame.NativeUnwind.Checks.ancestor n small)) (.box (Solidity.Roadmap.V16.NativeParentConsumer.program n) φ) ↔ Solidity.Spec.sat (Solidity.Backend.InternalFlow.RuntimeFrame.NativeUnwind.Checks.output n small).st φ) ∧
 (Solidity.Spec.sat (Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingActivation.allocated (Solidity.Backend.InternalFlow.RuntimeFrame.NativeUnwind.Checks.ancestor n small)) (.diamond (Solidity.Roadmap.V16.NativeParentConsumer.program n) φ) ↔ Solidity.Spec.sat (Solidity.Backend.InternalFlow.RuntimeFrame.NativeUnwind.Checks.output n small).st φ) := by
  intro n small φ
  simp only [Solidity.Spec.sat,Solidity.Roadmap.V16.NativeParentConsumer.native_program n small] <;> exact ⟨True.intro,True.intro⟩

theorem mutating_entry_spec : Solidity.Spec.sat Solidity.Backend.InternalFlow.RuntimeFrame.MutatingActivation.Checks.child
 (.and (Solidity.Roadmap.V16.NativeParentConsumer.counterSpec 1 (by decide)) (Solidity.Roadmap.V16.NativeParentConsumer.elementSpec 2 (by decide))) := by
  constructor
  · exact ⟨Solidity.Backend.InternalFlow.RuntimeFrame.RecursiveSource.countValue 1 (by decide),rfl,rfl⟩
  · have lower := Solidity.Val.lower_evalT Solidity.Backend.InternalFlow.RuntimeFrame.MutatingActivation.Checks.child (Solidity.Roadmap.V16.NativeParentConsumer.atOne (C:=Solidity.Backend.InternalFlow.RuntimeFrame.CountdownWitness.P.C))
    rw [Solidity.Roadmap.V16.NativeParentConsumer.mutating_element] at lower
    exact ⟨Solidity.Backend.InternalFlow.RuntimeFrame.RecursiveSource.countValue 2 (by decide),lower,rfl⟩

theorem wrong_child_counter : ¬Solidity.Spec.sat Solidity.Backend.InternalFlow.RuntimeFrame.MutatingActivation.Checks.child (Solidity.Roadmap.V16.NativeParentConsumer.counterSpec 2 (by decide)) := by
  change ¬∃ v, some (Solidity.Backend.InternalFlow.RuntimeFrame.RecursiveSource.countValue 1 (by decide))=some v ∧ some (Solidity.Backend.InternalFlow.RuntimeFrame.RecursiveSource.countValue 2 (by decide))=some v
  rintro ⟨v,one,two⟩
  have same := (Option.some.inj one).trans (Option.some.inj two).symm
  have values := congrArg (fun x : Solidity.PrimTy.uint.Denote => x.val) same
  change (1:Int)=2 at values
  omega

theorem wrong_child_contents : ¬Solidity.Spec.sat Solidity.Backend.InternalFlow.RuntimeFrame.MutatingActivation.Checks.child (Solidity.Roadmap.V16.NativeParentConsumer.elementSpec 9 (by decide)) := by
  have lower := Solidity.Val.lower_evalT Solidity.Backend.InternalFlow.RuntimeFrame.MutatingActivation.Checks.child (Solidity.Roadmap.V16.NativeParentConsumer.atOne (C:=Solidity.Backend.InternalFlow.RuntimeFrame.CountdownWitness.P.C))
  rw [Solidity.Roadmap.V16.NativeParentConsumer.mutating_element] at lower
  change ¬∃ v, (Solidity.Roadmap.V16.NativeParentConsumer.atOne (C:=Solidity.Backend.InternalFlow.RuntimeFrame.CountdownWitness.P.C)).lower.eval Solidity.Backend.InternalFlow.RuntimeFrame.MutatingActivation.Checks.child=some v ∧ some (Solidity.Backend.InternalFlow.RuntimeFrame.RecursiveSource.countValue 9 (by decide))=some v
  rintro ⟨v,read,literal⟩
  rw [lower] at read
  have same := (Option.some.inj read).trans (Option.some.inj literal).symm
  have values := congrArg (fun x : Solidity.PrimTy.uint.Denote => x.val) same
  change (2:Int)=9 at values
  omega

theorem bare_revert_spec : ∀ depth : Nat,
 (Solidity.Backend.InternalFlow.RuntimeFrame.MutatingActivation.body (C:=Solidity.Backend.InternalFlow.RuntimeFrame.CountdownWitness.P.C) (depth+1)).run Solidity.Backend.InternalFlow.RuntimeFrame.MutatingActivation.Checks.bad=.error .revert ∧
 Solidity.Evm.run (Solidity.Backend.InternalFlow.RuntimeFrame.MutatingActivation.code (C:=Solidity.Backend.InternalFlow.RuntimeFrame.CountdownWitness.P.C) 2 Solidity.Backend.InternalFlow.RuntimeFrame.CountdownWitness.F 8) Solidity.Backend.InternalFlow.RuntimeFrame.MutatingActivation.Checks.badMachine=.revert ∧
 ¬Solidity.Spec.sat Solidity.Backend.InternalFlow.RuntimeFrame.MutatingActivation.Checks.bad (.diamond (Solidity.Backend.InternalFlow.RuntimeFrame.MutatingActivation.body (depth+1)) .tt) ∧
 Solidity.Spec.sat Solidity.Backend.InternalFlow.RuntimeFrame.MutatingActivation.Checks.bad (.box (Solidity.Backend.InternalFlow.RuntimeFrame.MutatingActivation.body (depth+1)) .tt) := by
  intro depth
  refine ⟨Solidity.Backend.InternalFlow.RuntimeFrame.MutatingActivation.Checks.bad_body depth,Solidity.Backend.InternalFlow.RuntimeFrame.MutatingActivation.Checks.bad_target,?_,?_⟩
  · simp only [Solidity.Spec.sat,Solidity.Backend.InternalFlow.RuntimeFrame.MutatingActivation.Checks.bad_body depth]
    intro impossible
    cases impossible
  · simp only [Solidity.Spec.sat,Solidity.Backend.InternalFlow.RuntimeFrame.MutatingActivation.Checks.bad_body depth]
    intro impossible
    cases impossible

theorem exhaustion_control : (Solidity.Prog.recBase (C:=Solidity.Backend.InternalFlow.RuntimeFrame.CountdownWitness.P.C) (Γ:=(Solidity.Backend.InternalFlow.RuntimeFrame.RecursiveSource.Parameters Solidity.Roadmap.V16.NativeParentConsumer.A))).run Solidity.Backend.InternalFlow.RuntimeFrame.MutatingActivation.Checks.bad=.error .exhausted ∧
 Solidity.Spec.sat Solidity.Backend.InternalFlow.RuntimeFrame.MutatingActivation.Checks.bad (.diamond (Solidity.Prog.recBase (Γ:=(Solidity.Backend.InternalFlow.RuntimeFrame.RecursiveSource.Parameters Solidity.Roadmap.V16.NativeParentConsumer.A))) .tt) := by
  exact ⟨rfl,rfl⟩

def observeMutation (m : Machine) : List Word × List Word :=
 (m.stack,[m.mem 0,m.mem 1,m.mem 2,m.mem 3,m.mem 4,m.mem 7,m.mem 8,m.mem 9,
  m.mem 10,m.mem 11,m.mem 12,m.mem 13,m.mem 16,m.mem 17,m.mem 18,m.mem 20,m.mem 21,
  m.mem 22,m.mem 23,m.mem 24,m.mem 25])

def expectedMutation : List Word × List Word :=
 ([w[77]],[w[26],w[16],w[16],w[1],w[22],w[10],w[12],w[99],w[16],w[2],w[0],w[0],
  w[2],w[7],w[2],w[1],w[4],w[3],w[0],w[0],w[0]])

theorem native_return_transport : ∀ (n : Nat) (small : n+1≤2), ∃ addresses : Nat → Fin Solidity.Evm.W,
 (Solidity.Roadmap.V16.NativeParentConsumer.program (C:=Solidity.Backend.InternalFlow.RuntimeFrame.CountdownWitness.P.C) n).run (Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingActivation.allocated (Solidity.Backend.InternalFlow.RuntimeFrame.NativeUnwind.Checks.ancestor n small))=.ok (Solidity.Backend.InternalFlow.RuntimeFrame.NativeUnwind.Checks.output n small) ∧
 Solidity.Evm.Memory.StateRepr 1 2 16 Solidity.Backend.InternalFlow.RuntimeFrame.CountdownWitness.F (Solidity.Backend.InternalFlow.RuntimeFrame.NativeUnwind.Checks.output n small).st addresses (Solidity.Backend.InternalFlow.RuntimeFrame.EmissionUnwind.Checks.machine (n+1) small) ∧
 Solidity.Evm.Memory.BaseExtends Solidity.Backend.InternalFlow.RuntimeFrame.CountdownWitness.callee.H Solidity.Backend.InternalFlow.RuntimeFrame.CountdownWitness.P.base addresses ∧
 Solidity.Evm.Memory.GrowsAllocator 2 16 8 Solidity.Backend.InternalFlow.RuntimeFrame.CountdownWitness.callee Solidity.Backend.InternalFlow.RuntimeFrame.CountdownWitness.P.base Solidity.Backend.InternalFlow.RuntimeFrame.EmissionPrefixes.Checks.before (Solidity.Backend.InternalFlow.RuntimeFrame.NativeUnwind.Checks.output n small).st addresses (Solidity.Backend.InternalFlow.RuntimeFrame.EmissionUnwind.Checks.machine (n+1) small) ∧
 Solidity.Roadmap.V16.NativeParentConsumer.observe (Solidity.Backend.InternalFlow.RuntimeFrame.EmissionUnwind.Checks.machine (n+1) small)=Solidity.Roadmap.V16.NativeParentConsumer.expected n ∧
 Solidity.Spec.sat (Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingActivation.allocated (Solidity.Backend.InternalFlow.RuntimeFrame.NativeUnwind.Checks.ancestor n small)) (.box (Solidity.Roadmap.V16.NativeParentConsumer.program n) (Solidity.Roadmap.V16.NativeParentConsumer.counterSpec (n+1) (Nat.lt_of_le_of_lt small (by decide : 2<Solidity.Evm.W)))) ∧
 Solidity.Spec.sat (Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingActivation.allocated (Solidity.Backend.InternalFlow.RuntimeFrame.NativeUnwind.Checks.ancestor n small)) (.diamond (Solidity.Roadmap.V16.NativeParentConsumer.program n) (Solidity.Roadmap.V16.NativeParentConsumer.counterSpec (n+1) (Nat.lt_of_le_of_lt small (by decide : 2<Solidity.Evm.W)))) ∧
 Solidity.Spec.sat (Solidity.Backend.InternalFlow.RuntimeFrame.NativeUnwind.Checks.output n small).st (Solidity.Roadmap.V16.NativeParentConsumer.counterSpec (n+1) (Nat.lt_of_le_of_lt small (by decide : 2<Solidity.Evm.W))) := by
  intro n small
  have h := (Solidity.Backend.InternalFlow.RuntimeFrame.NativeUnwind.Checks.available n small).choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec
  rcases h with ⟨prefixRun,prefixRepr,prefixSize,prefixKept,env,args,native,represented,size,bindings,kept,extended,growth,snapshot⟩
  have post := Solidity.Roadmap.V16.NativeParentConsumer.returned_counter n small
  exact ⟨_,Solidity.Roadmap.V16.NativeParentConsumer.native_program n small,represented,extended,growth,snapshot,
    (Solidity.Roadmap.V16.NativeParentConsumer.native_spec_iff n small _).1.mpr post,(Solidity.Roadmap.V16.NativeParentConsumer.native_spec_iff n small _).2.mpr post,post⟩

theorem mutating_entry_transport : (Solidity.Backend.InternalFlow.RuntimeFrame.MutatingActivation.write (C:=Solidity.Backend.InternalFlow.RuntimeFrame.CountdownWitness.P.C)).run Solidity.Backend.InternalFlow.RuntimeFrame.CountdownWitness.callee=.ok ⟨Solidity.Backend.InternalFlow.RuntimeFrame.MutatingActivation.Checks.mutated,List.prefix_refl _⟩ ∧
 (Solidity.Backend.InternalFlow.RuntimeFrame.RecursiveSource.nextArgs Solidity.Roadmap.V16.NativeParentConsumer.A rfl).evalT Solidity.Backend.InternalFlow.RuntimeFrame.MutatingActivation.Checks.parent=.ok Solidity.Backend.InternalFlow.RuntimeFrame.MutatingActivation.Checks.child.env ∧
 ((Solidity.CallRet.none : Solidity.CallRet (Solidity.Backend.InternalFlow.RuntimeFrame.RecursiveSource.Parameters Solidity.Roadmap.V16.NativeParentConsumer.A) [] (Solidity.Backend.InternalFlow.RuntimeFrame.RecursiveSource.Parameters Solidity.Roadmap.V16.NativeParentConsumer.A)).enterT (Solidity.Backend.InternalFlow.RuntimeFrame.MutatingActivation.Checks.parent.withEnv Solidity.Backend.InternalFlow.RuntimeFrame.MutatingActivation.Checks.child.env)).st=Solidity.Backend.InternalFlow.RuntimeFrame.MutatingActivation.Checks.child ∧
 Solidity.Evm.run (Solidity.Backend.InternalFlow.RuntimeFrame.MutatingActivation.code (C:=Solidity.Backend.InternalFlow.RuntimeFrame.CountdownWitness.P.C) 2 Solidity.Backend.InternalFlow.RuntimeFrame.CountdownWitness.F 8) Solidity.Backend.InternalFlow.RuntimeFrame.MutatingActivation.Checks.before=.ok Solidity.Backend.InternalFlow.RuntimeFrame.MutatingActivation.Checks.machine 0 ∧
 Solidity.Evm.Memory.StateRepr 1 2 16 Solidity.Backend.InternalFlow.RuntimeFrame.CountdownWitness.F Solidity.Backend.InternalFlow.RuntimeFrame.MutatingActivation.Checks.child Solidity.Backend.InternalFlow.RuntimeFrame.MutatingActivation.Checks.addresses Solidity.Backend.InternalFlow.RuntimeFrame.MutatingActivation.Checks.machine ∧
 Solidity.Backend.InternalFlow.RuntimeFrame.MutatingActivation.Checks.machine.stack=Solidity.Backend.InternalFlow.RuntimeFrame.MutatingActivation.Checks.before.stack ∧
 Solidity.Evm.Memory.BaseExtends Solidity.Backend.InternalFlow.RuntimeFrame.CountdownWitness.callee.H Solidity.Backend.InternalFlow.RuntimeFrame.CountdownWitness.P.base Solidity.Backend.InternalFlow.RuntimeFrame.MutatingActivation.Checks.addresses ∧
 Solidity.Evm.Memory.GrowsAllocator 2 16 4 Solidity.Backend.InternalFlow.RuntimeFrame.CountdownWitness.callee Solidity.Backend.InternalFlow.RuntimeFrame.CountdownWitness.P.base Solidity.Backend.InternalFlow.RuntimeFrame.MutatingActivation.Checks.before Solidity.Backend.InternalFlow.RuntimeFrame.MutatingActivation.Checks.child Solidity.Backend.InternalFlow.RuntimeFrame.MutatingActivation.Checks.addresses Solidity.Backend.InternalFlow.RuntimeFrame.MutatingActivation.Checks.machine ∧
 Solidity.Backend.InternalFlow.RuntimeFrame.MutatingActivation.Checks.machine.mem 8=.val (Solidity.Evm.wmod 12) ∧
 (∀ i,i<2 → Solidity.Backend.InternalFlow.RuntimeFrame.MutatingActivation.Checks.machine.mem (10+i)=Solidity.Backend.InternalFlow.RuntimeFrame.MutatingActivation.Checks.before.mem (2+i)) ∧
 (∀ x,0<x → x<16 → x≠3 → x≠4 → x≠8 → (x<10 ∨ 12≤x) → Solidity.Backend.InternalFlow.RuntimeFrame.MutatingActivation.Checks.machine.mem x=Solidity.Backend.InternalFlow.RuntimeFrame.MutatingActivation.Checks.before.mem x) ∧
 (∀ x,x≠8 → x≠3 → (x<10 ∨ 12≤x) → Solidity.Backend.InternalFlow.RuntimeFrame.MutatingActivation.Checks.machine.mem x=Solidity.Backend.InternalFlow.RuntimeFrame.MutatingActivation.Checks.allocationMachine.mem x) ∧
 Solidity.Roadmap.V16.NativeParentConsumer.observeMutation Solidity.Backend.InternalFlow.RuntimeFrame.MutatingActivation.Checks.machine=Solidity.Roadmap.V16.NativeParentConsumer.expectedMutation ∧
 Solidity.Spec.sat Solidity.Backend.InternalFlow.RuntimeFrame.MutatingActivation.Checks.child (.and (Solidity.Roadmap.V16.NativeParentConsumer.counterSpec 1 (by decide)) (Solidity.Roadmap.V16.NativeParentConsumer.elementSpec 2 (by decide))) ∧
 ¬Solidity.Heap.Keeps (List.prefix_refl Solidity.Backend.InternalFlow.RuntimeFrame.CountdownWitness.callee.H) Solidity.Backend.InternalFlow.RuntimeFrame.CountdownWitness.callee.heap Solidity.Backend.InternalFlow.RuntimeFrame.MutatingActivation.Checks.mutated.heap := by
  rcases Solidity.Backend.InternalFlow.RuntimeFrame.MutatingActivation.Checks.specification with ⟨args,entry,actual,represented,stack,extended,growth,cursor,payload,low,exterior⟩
  exact ⟨Solidity.Backend.InternalFlow.RuntimeFrame.MutatingActivation.Checks.source_prefix,args,entry,actual,represented,stack,extended,growth,cursor,payload,low,exterior,
    Solidity.Backend.InternalFlow.RuntimeFrame.MutatingActivation.Checks.observations,Solidity.Roadmap.V16.NativeParentConsumer.mutating_entry_spec,Solidity.Backend.InternalFlow.RuntimeFrame.MutatingActivation.Checks.not_keeps⟩


/-- The actual returned caller cannot satisfy the child-counter postcondition. -/
theorem wrong_returned_counter : ∀ (n : Nat) (small : n+1≤2),
 ¬Solidity.Spec.sat (Solidity.Backend.InternalFlow.RuntimeFrame.NativeUnwind.Checks.output n small).st (Solidity.Roadmap.V16.NativeParentConsumer.counterSpec n (Nat.lt_of_le_of_lt (Nat.le_trans (Nat.le_succ n) small) (by decide : 2<Solidity.Evm.W))) := by
  intro n small
  have post := Solidity.Roadmap.V16.NativeParentConsumer.returned_counter n small
  change (∃ v, some ((Solidity.Backend.InternalFlow.RuntimeFrame.NativeUnwind.Checks.output n small).st.env.1)=some v ∧ some (Solidity.Backend.InternalFlow.RuntimeFrame.RecursiveSource.countValue (n+1) (Nat.lt_of_le_of_lt small (by decide : 2<Solidity.Evm.W)))=some v) at post
  obtain ⟨actual,read,literal⟩ := post
  have parent := (Option.some.inj read).trans (Option.some.inj literal).symm
  change ¬∃ v, some ((Solidity.Backend.InternalFlow.RuntimeFrame.NativeUnwind.Checks.output n small).st.env.1)=some v ∧ some (Solidity.Backend.InternalFlow.RuntimeFrame.RecursiveSource.countValue n (Nat.lt_of_le_of_lt (Nat.le_trans (Nat.le_succ n) small) (by decide : 2<Solidity.Evm.W)))=some v
  rintro ⟨value,childRead,childLiteral⟩
  have child := (Option.some.inj childRead).trans (Option.some.inj childLiteral).symm
  have values := congrArg (fun x : Solidity.PrimTy.uint.Denote => x.val) (parent.symm.trans child)
  change ((n+1:Nat):Int)=(n:Int) at values
  omega


/-- info: 'Solidity.Roadmap.V16.NativeParentConsumer.returned_counter' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms returned_counter

/-- info: 'Solidity.Roadmap.V16.NativeParentConsumer.parent_specification' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms parent_specification

/-- info: 'Solidity.Roadmap.V16.NativeParentConsumer.native_program' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms native_program

/-- info: 'Solidity.Roadmap.V16.NativeParentConsumer.mutating_element' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms mutating_element

/-- info: 'Solidity.Roadmap.V16.NativeParentConsumer.native_spec_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms native_spec_iff

/-- info: 'Solidity.Roadmap.V16.NativeParentConsumer.mutating_entry_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms mutating_entry_spec

/-- info: 'Solidity.Roadmap.V16.NativeParentConsumer.wrong_child_counter' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms wrong_child_counter

/-- info: 'Solidity.Roadmap.V16.NativeParentConsumer.wrong_child_contents' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms wrong_child_contents

/-- info: 'Solidity.Roadmap.V16.NativeParentConsumer.bare_revert_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms bare_revert_spec

/-- info: 'Solidity.Roadmap.V16.NativeParentConsumer.exhaustion_control' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms exhaustion_control

/-- info: 'Solidity.Roadmap.V16.NativeParentConsumer.native_return_transport' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms native_return_transport

/-- info: 'Solidity.Roadmap.V16.NativeParentConsumer.mutating_entry_transport' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms mutating_entry_transport

/-- info: 'Solidity.Roadmap.V16.NativeParentConsumer.wrong_returned_counter' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms wrong_returned_counter

end Solidity.Roadmap.V16.NativeParentConsumer
