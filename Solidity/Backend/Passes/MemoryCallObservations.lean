import Solidity.Backend.Passes.MemoryCallApplication

/-! Complete fixture observations, keeping every live allocation including
the orphaned default return and privately rebound parameter object. These are
projections of the EXISTING intrinsic state and emitted execution only. -/
namespace Solidity.Backend.Passes.MemoryCallObservations
open Evm Evm.Memory MemoryCallControls MemoryCallApplication

private def arrayAt {H : HTy} (hp : Heap H) (id i : Nat) : Option Int := do
  if h : H[id]? = some A then
    let value ← hp.index (⟨id,h⟩ : HRef H A) .dyn (indexValue (wmod i))
    pure value.val
  else none
private def lengthAt {H : HTy} (hp : Heap H) (id : Nat) : Option Int :=
  if h : H[id]? = some A then some (hp.len (⟨id,h⟩ : HRef H A) .dyn) else none

private def sourceVector (σ : State C After) : Option (List Int) := do
  let returned ← TEnv.get (.here : Idx After (.mem A)) σ.env
  let captured ← TEnv.get (.there .here : Idx After (.mem A)) σ.env
  let old ← TEnv.get (.there (.there (.there .here)) : Idx After (.mem A)) σ.env
  let marker := TEnv.get (.there (.there .here) : Idx After (.val .uint)) σ.env
  let oldLength ← lengthAt σ.heap 0
  let oldValue ← arrayAt σ.heap 0 0
  let defaultLength ← lengthAt σ.heap 1
  let returnedLength ← lengthAt σ.heap 2
  let left ← arrayAt σ.heap 2 0
  let right ← arrayAt σ.heap 2 1
  let reboundLength ← lengthAt σ.heap 3
  let reboundValue ← arrayAt σ.heap 3 0
  pure [σ.H.length,old.id,captured.id,returned.id,marker.val,
    oldLength,oldValue,defaultLength,returnedLength,left,right,reboundLength,reboundValue]

theorem source_before_consume : sourceVector second.st = some [4,0,0,2,42,1,7,0,2,33,34,1,44] := by
  decide +kernel

theorem source_after_consume : sourceVector final.st = some [4,0,0,2,42,1,8,0,2,42,34,1,44] := by
  decide +kernel

private def targetWords (out : Evm.Out) (addresses : List Nat) : Option (List Nat) := do
  match out with
  | .ok m _ => (m.stack ++ addresses.map m.mem).mapM fun w => match w with
    | .val v => some v.val
    | .slot _ => none
  | _ => none

def addresses : List Nat := [0,127,1,2,3,4,5,6,256,257,258,259,260,261,262,263]
def code : List Evm.Instr := allocation.code ++ (producer.code ++ consumer.code)

/-- Caller locals, captured alias, private return/body cells, ALL object
headers/elements, sentinel, allocator and full two-word saved stack. -/
theorem allocation_vector : targetWords (run allocation.code {machine with stack := [w[77],w[88]]}) addresses =
    some [77,88,258,99,256,42,0,0,0,0,1,7,0,0,0,0,0,0] := by decide +kernel

theorem call_vector : targetWords (run (allocation.code ++ producer.code)
    {machine with stack := [w[77],w[88]]}) addresses =
    some [77,88,264,99,256,42,256,259,259,259,1,7,0,2,33,34,1,44] := by decide +kernel

theorem final_vector : targetWords (run code {machine with stack := [w[77],w[88]]}) addresses =
    some [77,88,264,99,256,42,256,259,259,259,1,8,0,2,42,34,1,44] := by decide +kernel

/-- Omitting the consuming suffix leaves the actual successful call prefix
with different old and returned values. No reversed typed run is asserted. -/
theorem skipped_consumer : sourceVector second.st ≠ sourceVector final.st := by
  rw [source_before_consume,source_after_consume]
  decide +kernel

theorem return_identity :
    (TEnv.get (.here : Idx After (.mem A)) second.st.env).map (·.id) = some 2 ∧
    (TEnv.get (.there .here : Idx After (.mem A)) second.st.env).map (·.id) = some 0 ∧
    (TEnv.get (.there (.there (.there .here)) : Idx After (.mem A)) second.st.env).map (·.id) = some 0 := by
  decide +kernel

/-- An actual pre-call reference witnesses nonempty BaseExtends preservation. -/
noncomputable def oldRef : HRef first.st.H A := ⟨0,by decide +kernel⟩
theorem old_map_preserved {mb nb : Nat → Fin W} {mid next : Machine}
    (h : MappedOutput checked 1 128 mb first.st mid second.st next nb) : nb oldRef.id = mb oldRef.id := h.2.1 oldRef

private def cell (out : Evm.Out) (address : Nat) : Option Nat :=
  match out with
  | .ok m _ => match m.mem address with | .val w => some w.val | _ => none
  | _ => none
private theorem actual_return_cell : cell (run (allocation.code ++ producer.code) machine) 4 = some 259 := by
  decide +kernel

/-- The actual returned source ID and target pointer force the selected new
map entry; the old map cannot be silently reused after this allocation. -/
theorem selected_return_base {mb nb : Nat → Fin W} {mid next : Machine}
    (execution : run (allocation.code ++ producer.code) machine = .ok next 0)
    (output : MappedOutput checked 1 128 mb first.st mid second.st next nb) :
    nb 2 = wmod 259 := by
  obtain ⟨r,henv,hptr⟩ := output.1.pointers (.here : Idx After (.mem A))
  have ids := congrArg (Option.map (fun ref => ref.id)) henv
  rw [return_identity.1] at ids
  have id : r.id = 2 := (Option.some.inj ids).symm
  change next.mem 4 = .val (nb r.id) at hptr
  rw [id] at hptr
  have observed := actual_return_cell
  rw [execution] at observed
  change (match next.mem 4 with | .val w => some w.val | _ => none) = some 259 at observed
  rw [hptr] at observed
  apply Fin.ext
  exact Option.some.inj observed

def oldOnly : Nat → Fin W := fun id => if id = 0 then wmod 256 else wmod 0

theorem old_only_keeps_old : oldOnly oldRef.id = wmod 256 := by decide +kernel

theorem stale_map_refused {mb : Nat → Fin W} {mid next : Machine}
    (execution : run (allocation.code ++ producer.code) machine = .ok next 0) :
    ¬ MappedOutput checked 1 128 mb first.st mid second.st next oldOnly := by
  intro output
  have bad := selected_return_base execution output
  have impossible := congrArg Fin.val bad
  change 0 = 259 at impossible
  cases impossible

end Solidity.Backend.Passes.MemoryCallObservations
