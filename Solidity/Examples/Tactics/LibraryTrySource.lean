import Solidity.Frontend.LibraryTryImport

/-! Kernel executions of the unchanged original linked-library try source. -/
namespace Solidity.Examples.Tactics.LibraryTrySource
open Solidity.ContractWorld Semantics
solc_library_try "../../../tests/solc/LibraryTry.ast.json" hash 0x0358fb18516ff9b5
  from_contract "C" as Original

def sender : Address := ⟨⟨103164821458651970696730694074090566093359944210, by decide +kernel⟩, by decide +kernel⟩
def callerAddress : Address := ⟨⟨816484669177263916909924781827997526878516243634, by decide +kernel⟩, by decide +kernel⟩
def libraryAddress : Address := ⟨⟨457415396813334496268612927368880745799219276745, by decide +kernel⟩, by decide +kernel⟩
def initial := World.empty Original.contracts
  (fun a => if a = sender then (⟨1000000000000000000000000000000, by decide +kernel⟩ : ContractWorld.Word) else PrimTy.dflt .uint) Original.roles

def f (b : Bool) : TRes (List Nat) := do
  let (w, linked) ← Original.deployLibrary initial libraryAddress { sender }
  let (w, self) ← Original.deployCaller w callerAddress { sender }
  let (_, bytes) ← Original.m0.run w self { sender } linked.address b
  pure bytes

def expected (value : Nat) (message : List UInt8) : List Nat :=
  (wordBytes value ++ wordBytes 64 ++ wordBytes message.length ++ pad32 message).map UInt8.toNat

/-- Original f(true) returns its actual prefix value through the linked body. -/
theorem f_success : (f true).toOption = some (expected 8 []) := by decide +kernel

/-- Original f(false) catches the actual library Error reason. -/
theorem f_caught : (f false).toOption = some (expected 18 [102,97,105,108,117,114,101]) := by decide +kernel

/-- All original caller calls share the same actual world in original order. -/
def ordered : TRes (List Nat × List Nat × List Nat × List Nat) := do
  let (w, linked) ← Original.deployLibrary initial libraryAddress { sender }
  let (w, self) ← Original.deployCaller w callerAddress { sender }
  let (w,a) ← Original.m0.run w self { sender } linked.address true
  let (w,b) ← Original.m0.run w self { sender } linked.address false
  let (w,c) ← Original.m1.run w self { sender } linked.address true
  let (_,d) ← Original.m1.run w self { sender } linked.address false
  pure (a,b,c,d)

/-- The original ordered assertion, retained while its direct kernel
reduction is factored after the recorded unchanged-limit resource stop. -/
def OriginalOrderedOutputs : Prop := ordered.toOption = some
    (expected 8 [], expected 18 [102,97,105,108,117,114,101],
     expected 9 [], expected 19 [102,97,105,108,117,114,101])

def g (b : Bool) : TRes (List Nat) := do
  let (w, linked) ← Original.deployLibrary initial libraryAddress { sender }
  let (w, self) ← Original.deployCaller w callerAddress { sender }
  let (_, bytes) ← Original.m1.run w self { sender } linked.address b
  pure bytes

/-- Original g(true) reads the actual caller root after its prefix write. -/
theorem g_success : (g true).toOption = some (expected 9 []) := by decide +kernel

/-- Original g(false) catches actual Error bytes after preserving its prefix. -/
theorem g_caught : (g false).toOption = some (expected 19 [102,97,105,108,117,114,101]) := by decide +kernel

/-- The unchanged ordered assertion now reduces through the corrected source
mapping, rather than through an unresolved generated storage method. -/
theorem original_outputs : OriginalOrderedOutputs := by
  unfold OriginalOrderedOutputs
  decide +kernel

def orderedOrdinary : TRes (List Nat × List Nat × List Nat × List Nat) := do
  let (w, linked) ← Original.deployLibrary initial libraryAddress { sender }
  let (w, self) ← Original.deployCaller w callerAddress { sender }
  let (w,a) ← Original.m0.runOrdinary w self { sender } linked.address true
  let (w,b) ← Original.m0.runOrdinary w self { sender } linked.address false
  let (w,c) ← Original.m1.runOrdinary w self { sender } linked.address true
  let (_,d) ← Original.m1.runOrdinary w self { sender } linked.address false
  pure (a,b,c,d)

/-- Typed composition transports all four actual calls, not just each
isolated byte projection, into the unchanged ordinary reading. -/
theorem ordered_approx : TRes.Approx ordered orderedOrdinary := by
  unfold ordered orderedOrdinary
  apply TRes.Approx.bind (.refl _)
  intro deployedLibrary
  apply TRes.Approx.bind (.refl _)
  intro deployedCaller
  apply (Original.m0.run_approx deployedCaller.1 deployedCaller.2 { sender } deployedLibrary.2.address true).bind
  intro first
  apply (Original.m0.run_approx first.1 deployedCaller.2 { sender } deployedLibrary.2.address false).bind
  intro second
  apply (Original.m1.run_approx second.1 deployedCaller.2 { sender } deployedLibrary.2.address true).bind
  intro third
  apply (Original.m1.run_approx third.1 deployedCaller.2 { sender } deployedLibrary.2.address false).bind
  intro fourth
  exact .refl _

/-- The normal bounded witness is the same complete ordinary execution. -/
theorem ordinary_execution : orderedOrdinary = ordered := by
  rcases ordered_approx with divergent | actual
  · have h := original_outputs
    unfold OriginalOrderedOutputs at h
    rw [divergent] at h
    cases h
  · exact actual.symm

/-- Observe caller storage after each original source call, in source order. -/
def storageEffects : TRes (Int × Int × Int × Int) := do
  let (w, linked) ← Original.deployLibrary initial libraryAddress { sender }
  let (w, self) ← Original.deployCaller w callerAddress { sender }
  let (w,_) ← Original.m0.run w self { sender } linked.address true
  let a ← Original.readStorage w self
  let (w,_) ← Original.m0.run w self { sender } linked.address false
  let b ← Original.readStorage w self
  let (w,_) ← Original.m1.run w self { sender } linked.address true
  let c ← Original.readStorage w self
  let (w,_) ← Original.m1.run w self { sender } linked.address false
  let d ← Original.readStorage w self
  pure (a,b,c,d)

/-- g's caller prefix is retained on both success and caught revert, while
f never substitutes its scalar formal for caller storage. -/
theorem actual_prefix_storage : storageEffects.toOption = some (0,0,9,9) := by decide +kernel

end Solidity.Examples.Tactics.LibraryTrySource
