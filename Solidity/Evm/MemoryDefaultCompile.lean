import Solidity.Evm.MemoryDefaultDynamic

/-! Type-directed default compilation. Only finite array type structure is
traversed; structs use the existing primitive-member predicate and source API. -/
namespace Solidity.Evm.Memory.ReferenceDefaults
open Objects Semantics

def defaultCells : (T : Ty) → Nat
  | .prim _ => 0
  | .ref (.array _) => 1
  | .ref (.struct s) => structAllocationSize s
  | .ref (.fixed (.prim _) n) => max 1 n
  | .ref (.fixed (.ref R) n) => max 1 n + n * defaultCells (.ref R)
  | .ref (.mapping ..) => 0
termination_by structural T => T

private def compileDefaultAny : (T : Ty) → (hm : T.mapFree = true) →
    Option (match T with | .prim _ => PUnit | .ref R => DefaultBuilder R hm (defaultCells T))
  | .prim _, _ => some ⟨⟩
  | .ref (.array E), hm => some (.empty E hm)
  | .ref (.struct s), hm =>
    if hprim : primitiveMembers (structDef s) = true then some (.primitiveStruct hprim hm)
    else none
  | .ref (.fixed (.prim p) n), _ => some (.fixedPrimitive p n)
  | .ref (.fixed (.ref R) n), hm => do
    let child ← compileDefaultAny (.ref R) hm
    pure (.fixedReference child n)
  | .ref (.mapping ..), _ => none
termination_by structural T _hm => T

def compileDefault (R : RefTy) (hm : (Ty.ref R).mapFree = true) :
    Option (DefaultBuilder R hm (defaultCells (.ref R))) := compileDefaultAny (.ref R) hm

theorem compileDefault_correct {R : RefTy} {hm : (Ty.ref R).mapFree = true}
    (builder : DefaultBuilder R hm (defaultCells (.ref R))) {H : HTy}
    (hp : Heap H) (base : Nat → Fin W) (frame : Nat) (cursor : Fin W) (m : Machine)
    (ha : Objects.AllocatorRepr hp base frame cursor m) (hs : cursor.val + defaultCells (.ref R) < W) :
    DefaultBuildResult hp R hm builder.code (defaultCells (.ref R)) base frame cursor m hs :=
  builder.correct hp base frame cursor m ha hs

end Solidity.Evm.Memory.ReferenceDefaults
