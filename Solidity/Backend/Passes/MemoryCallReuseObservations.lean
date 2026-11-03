import Solidity.Backend.Passes.MemoryCallReuseApplication

/-! Complete projections of existing intrinsic/target results. Every old object,
orphan default return, private allocation, local, saved word and allocator cell
is retained. Scratch reuse is code-specific, not a universal framing claim. -/
namespace Solidity.Backend.Passes.MemoryCallReuseObservations
open Evm Evm.Memory Evm.Compiler MemoryCallControls MemoryCallReuse MemoryCallReuseApplication

private def arrayAt {H : HTy} (hp : Heap H) (id i : Nat) : Option Int := do
  if h : H[id]? = some A then
    let value ← hp.index (⟨id,h⟩ : HRef H A) .dyn (indexValue (wmod i))
    pure value.val
  else none
private def lengthAt {H : HTy} (hp : Heap H) (id : Nat) : Option Int :=
  if h : H[id]? = some A then some (hp.len (⟨id,h⟩ : HRef H A) .dyn) else none

/-- The same original13 fields as CP17, with explicit intrinsic local indices. -/
private def oldVector {Γ : Ctx} (σ : State C Γ)
    (old captured returned : Idx Γ (.mem A)) (marker : Idx Γ (.val .uint)) : Option (List Int) := do
  let oldRef ← TEnv.get old σ.env
  let capturedRef ← TEnv.get captured σ.env
  let returnedRef ← TEnv.get returned σ.env
  let markerValue := TEnv.get marker σ.env
  let oldLength ← lengthAt σ.heap 0
  let oldValue ← arrayAt σ.heap 0 0
  let defaultLength ← lengthAt σ.heap 1
  let returnedLength ← lengthAt σ.heap 2
  let left ← arrayAt σ.heap 2 0
  let right ← arrayAt σ.heap 2 1
  let reboundLength ← lengthAt σ.heap 3
  let reboundValue ← arrayAt σ.heap 3 0
  pure [σ.H.length,oldRef.id,capturedRef.id,returnedRef.id,markerValue.val,
    oldLength,oldValue,defaultLength,returnedLength,left,right,reboundLength,reboundValue]

private def afterVector (σ : State C After) : Option (List Int) :=
  oldVector σ (.there (.there (.there .here))) (.there .here) .here (.there (.there .here))

private def scalarVector (σ : State C (.mem A :: After)) : Option (List Int) := do
  let old ← oldVector σ (.there (.there (.there (.there .here))))
    (.there (.there .here)) (.there .here) (.there (.there (.there .here)))
  let following ← TEnv.get (.here : Idx (.mem A :: After) (.mem A)) σ.env
  let len ← lengthAt σ.heap 4
  let value ← arrayAt σ.heap 4 0
  pure (old ++ [(following.id : Int),len,value])

private def aliasVector (σ : State C (.mem A :: AliasContext)) : Option (List Int) := do
  let old ← oldVector σ (.there (.there (.there (.there (.there .here)))))
    (.there (.there (.there .here))) (.there (.there .here))
    (.there (.there (.there (.there .here))))
  let exported ← TEnv.get (.there .here : Idx (.mem A :: AliasContext) (.mem A)) σ.env
  let following ← TEnv.get (.here : Idx (.mem A :: AliasContext) (.mem A)) σ.env
  let orphanLength ← lengthAt σ.heap 4
  let len ← lengthAt σ.heap 5
  let value ← arrayAt σ.heap 5 0
  pure (old ++ [(exported.id : Int),following.id,orphanLength,len,value])

private def voidVector (σ : State C (.mem A :: After)) : Option (List Int) := do
  let old ← oldVector σ (.there (.there (.there (.there .here))))
    (.there (.there .here)) (.there .here) (.there (.there (.there .here)))
  let following ← TEnv.get (.here : Idx (.mem A :: After) (.mem A)) σ.env
  let privateLength ← lengthAt σ.heap 4
  let privateValue ← arrayAt σ.heap 4 0
  let len ← lengthAt σ.heap 5
  let value ← arrayAt σ.heap 5 0
  pure (old ++ [(following.id : Int),privateLength,privateValue,len,value])

theorem prefix_vector : afterVector before.st = some [4,0,0,2,42,1,7,0,2,33,34,1,44] := by
  decide +kernel
theorem scalar_middle_vector : afterVector scalarOut.st = some [4,0,0,2,35,1,7,0,2,33,35,1,44] := by
  decide +kernel
theorem scalar_source_vector : scalarVector scalarFinal.st =
    some [5,0,0,2,35,1,7,0,2,33,35,1,44,4,1,0] := by decide +kernel
theorem alias_source_vector : aliasVector aliasFinal.st =
    some [6,0,0,2,42,1,7,0,2,33,34,1,44,2,5,0,1,0] := by decide +kernel
theorem void_source_vector : voidVector voidFinal.st =
    some [6,0,0,2,42,1,7,0,2,33,35,1,44,5,1,55,1,0] := by decide +kernel

private def words (out : Evm.Out) (addresses : List Nat) : Option (List Nat) := do
  match out with
  | .ok m _ => (m.stack ++ addresses.map m.mem).mapM fun w => match w with
    | .val v => some v.val
    | .slot _ => none
  | _ => none

def addresses (size : Nat) : List Nat := [0,127,1,2,3,4,5,6] ++ (List.range size).map (256 + ·)
def scalarCode : List Evm.Instr := leading.code ++ (scalar.code ++ scalarFresh.code)
def aliasCode : List Evm.Instr := leading.code ++ (alias.code ++ aliasFresh.code)
def voidCode : List Evm.Instr := leading.code ++ (void.code ++ voidFresh.code)

theorem leading_target_vector : words (run leading.code {machine with stack := [w[77],w[88]]}) (addresses 10) =
    some [77,88,264,99,256,42,256,259,259,259,1,7,0,2,33,34,1,44,0,0] := by decide +kernel

theorem scalar_target_vector : words (run scalarCode {machine with stack := [w[77],w[88]]}) (addresses 10) =
    some [77,88,266,99,256,35,256,259,264,35,1,7,0,2,33,35,1,44,1,0] := by decide +kernel
theorem alias_target_vector : words (run aliasCode {machine with stack := [w[77],w[88]]}) (addresses 11) =
    some [77,88,267,99,256,42,256,259,259,265,1,7,0,2,33,34,1,44,0,1,0] := by decide +kernel
theorem void_target_vector : words (run voidCode {machine with stack := [w[77],w[88]]}) (addresses 12) =
    some [77,88,268,99,256,42,256,259,266,264,1,7,0,2,33,35,1,44,1,55,1,0] := by decide +kernel

/-- Private cell6 contains a primitive result after the second call, rather
than the earlier escaped pointer. All other observed cells are retained. -/
theorem scalar_middle_target : words (run (leading.code ++ scalar.code)
    {machine with stack := [w[77],w[88]]}) (addresses 10) =
    some [77,88,264,99,256,35,256,259,259,35,1,7,0,2,33,35,1,44,0,0] := by decide +kernel

theorem skipped_effect : afterVector before.st ≠ afterVector scalarOut.st := by
  rw [prefix_vector,scalar_middle_vector]
  decide +kernel

/-- Permuting the saved stack cannot satisfy the original COMPLETE vector. -/
theorem corrupt_saved_tail : words (run scalarCode {machine with stack := [w[88],w[77]]}) (addresses 10) ≠
    some [77,88,266,99,256,35,256,259,264,35,1,7,0,2,33,35,1,44,1,0] := by decide +kernel

private def cell (out : Evm.Out) (address : Nat) : Option Nat :=
  match out with
  | .ok m _ => match m.mem address with | .val w => some w.val | _ => none
  | _ => none

theorem private_cell_changed : cell (run leading.code machine) 6 ≠
    cell (run (leading.code ++ scalar.code) machine) 6 := by decide +kernel

theorem alias_fresh_identity :
    (TEnv.get (.here : Idx (.mem A :: AliasContext) (.mem A)) aliasFinal.st.env).map (·.id) = some 5 := by
  decide +kernel
private theorem alias_fresh_cell : cell (run aliasCode machine) 6 = some 265 := by decide +kernel

/-- A newly allocated sourceID5 must consume its ACTUAL final selected map,
not an old address table which only records the four earlier objects. -/
theorem selected_fresh_base {nb ob : Nat → Fin W} {next out : Machine}
    (execution : run aliasCode machine = .ok out 0)
    (output : MappedOutput (.memory aliasFresh) 1 128 nb aliasOut.st next aliasFinal.st out ob) :
    ob 5 = wmod 265 := by
  obtain ⟨ref,henv,hptr⟩ := output.1.pointers (.here : Idx (.mem A :: AliasContext) (.mem A))
  have ids := congrArg (Option.map (fun ref => ref.id)) henv
  rw [alias_fresh_identity] at ids
  have id : ref.id = 5 := (Option.some.inj ids).symm
  change out.mem 6 = .val (ob ref.id) at hptr
  rw [id] at hptr
  have observed := alias_fresh_cell
  rw [execution] at observed
  change (match out.mem 6 with | .val w => some w.val | _ => none) = some 265 at observed
  rw [hptr] at observed
  apply Fin.ext
  exact Option.some.inj observed

/-- Concrete addresses of the four earlier objects; no claim is made about
arbitrary unused entries of every possible selected prefix map. -/
def oldAddresses : Nat → Fin W := fun id =>
  if id = 0 then wmod 256 else if id = 1 then wmod 258 else
  if id = 2 then wmod 259 else if id = 3 then wmod 262 else wmod 0

theorem old_addresses : oldAddresses 0 = wmod 256 ∧ oldAddresses 1 = wmod 258 ∧
    oldAddresses 2 = wmod 259 ∧ oldAddresses 3 = wmod 262 := by decide +kernel

theorem stale_map_refused {nb : Nat → Fin W} {next out : Machine}
    (execution : run aliasCode machine = .ok out 0) :
    ¬ MappedOutput (.memory aliasFresh) 1 128 nb aliasOut.st next aliasFinal.st out oldAddresses := by
  intro output
  have bad := selected_fresh_base execution output
  have impossible := congrArg Fin.val bad
  change 0 = 265 at impossible
  cases impossible


private def tupleVector (σ : State C TupleContext) : Option (List Int) := do
  let old ← oldVector σ (.there (.there (.there (.there (.there .here)))))
    (.there (.there (.there .here))) (.there (.there .here))
    (.there (.there (.there (.there .here))))
  let right := TEnv.get (.here : Idx TupleContext (.val .uint)) σ.env
  let left := TEnv.get (.there .here : Idx TupleContext (.val .uint)) σ.env
  pure (old ++ [left.val,right.val])

theorem tuple_source_vector : tupleVector tupleOut.st =
    some [4,0,0,2,42,1,7,0,2,33,34,1,44,0,0] := by decide +kernel

end Solidity.Backend.Passes.MemoryCallReuseObservations
