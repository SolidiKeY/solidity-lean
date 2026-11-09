import Solidity.Source.CalldataStaticCopyControls
import Solidity.Source.CalldataExamples
import Solidity.Source.TypingExamples

/-!
# Controls of the nested `calldata` copy from typed source (G18.05)

`STy.implicit` compares array elements at the target's location
(`STy.withLoc`, user decision 2026-11-06), so `uint256[2][] calldata`
converts to `uint256[2][] memory`: the nested arm of `cdToMem` is reachable
from a typed declaration. The element type, the static length and the
target location are still compared exactly.

- `nested_implicit` … `to_storage_refused`: the conversion and its
  refusals.
- `struct_mapping_refused`, `array_mapping_refused`,
  `nested_mapping_refused`: copies out of `storage` of structs holding a
  mapping (directly or through a nested struct) are refused; pointers keep
  their type (`mapping_pointer_kept`).
- `dynamic_elements_stuck`: `bytes[] calldata` also converts, but its copy
  is `stuck` (no dynamic element copy; a recorded gap).
- `w_copy`: the typing derivation of `uint256[2][] memory c = xs;` for a
  `uint256[2][] calldata` parameter; its elaborated form converts with
  `convRV`, which runs `cdToMem`'s nested arm (`convRV_nested`) and keeps
  the memory invariant (`convRV_cd_static_ok`, `w_copy_ok`).
- `elabN`: the copy in an elaborated contract, deployed and called
  (`#guard`), with a dirty `bool` element reverting and a wrong static
  length refused at elaboration.
-/

namespace Solidity.Source.CalldataNestedCopyControls

open Solidity.Source Solidity.Source.SemanticsExamples Solidity.Source.CalldataStaticCopyControls
open Solidity.Source.Examples Solidity.Source.ElaborateExamples Solidity.Source.DecodeExamples
open Solidity.Source.CalldataExamples
open Solidity.Roadmap (Bytes Outcome)

def cdPair : STy := .array .calldata u (some 2)
def cdNested : STy := .array .calldata cdPair none
def memNested : STy := .array .memory pair none

/-! ## The conversion -/

theorem nested_implicit (B : DeclName → DeclName → Bool) (M : DeclName → Bool) : cdNested.implicit B M memNested = true := rfl

/-- The storage-to-memory analogue converts the same way (copied by `loadMem`, inner arrays allocated by `loadElem`). -/
theorem storage_nested_implicit (B : DeclName → DeclName → Bool) (M : DeclName → Bool) :
    STy.implicit B M (.array .storage (.array .storage u (some 2)) none) memNested = true := rfl

/-- A `calldata` pointer keeps its type. -/
theorem pointer_implicit (B : DeclName → DeclName → Bool) (M : DeclName → Bool) : cdNested.implicit B M cdNested = true := rfl

/-- A different static length is refused. -/
theorem length_refused (B : DeclName → DeclName → Bool) (M : DeclName → Bool) :
    cdNested.implicit B M (.array .memory (.array .memory u (some 3)) none) = false := rfl

/-- A different element type is refused (no element-wise conversion). -/
theorem element_refused (B : DeclName → DeclName → Bool) (M : DeclName → Bool) :
    STy.implicit B M (.array .calldata (.array .calldata (.int IntTy.u8) (some 2)) none) memNested = false := rfl

/-- Memory does not convert to `calldata`. -/
theorem to_calldata_refused (B : DeclName → DeclName → Bool) (M : DeclName → Bool) : memNested.implicit B M cdNested = false := rfl

/-- `calldata` does not convert implicitly to `storage` (a copy into storage is an assignment, `STy.copiesTo`). -/
theorem to_storage_refused (B : DeclName → DeclName → Bool) (M : DeclName → Bool) :
    cdNested.implicit B M (.array .storage (.array .storage u (some 2)) none) = false := rfl

/-- **A recorded gap** (`docs/feature-work/source-soundness.md`, census): `bytes[] calldata` now converts to `bytes[] memory`, as in solc, but `cdToMem` copies no dynamically encoded element, so the copy is `stuck`. -/
def dynElems := (convRV frame 0 (.array .memory (.bytes .memory) none)
  (σ := .array .calldata (.bytes .calldata) none) (.val (.cdRef rfl 0 1)) : EM EB [] _).run (L0 EB, sB)

theorem dynamic_elements_stuck (B : DeclName → DeclName → Bool) (M : DeclName → Bool) :
    STy.implicit B M (.array .calldata (.bytes .calldata) none) (.array .memory (.bytes .memory) none) = true ∧
    dynElems.1 = .error (.stuck "dynamic ABI decoding is not modelled") := ⟨rfl, rfl⟩

/-! ## Copies out of storage of structs holding a mapping

solc refuses copying a struct that holds a mapping out of `storage`, and an
array of such structs (user decision 2026-11-06): `STy.implicit` asks
`Env.mapFree`. A storage pointer keeps its type. -/

def mU : Syn .typeName := .elem (.int false 256 (by decide))
def mK : MapKey := .elem (.int false 256 (by decide)) (by decide)

/-- `struct Keyed { uint256 a; mapping(uint256 => uint256) m; }` and `struct Plain { uint256 a; uint256[] xs; }`. -/
def mapEnv : Env := ⟨[
  ⟨.struct, "Keyed", none, true, .struct "Keyed" (.structMember mU "a")
    (.cons (.structMember (.mapping mK none mU none) "m") .nil)⟩,
  ⟨.struct, "Plain", none, true, .struct "Plain" (.structMember mU "a")
    (.cons (.structMember (.array mU .none) "xs") .nil)⟩]⟩

/-- `mapEnv` with `struct Outer { Keyed k; }`, `struct Holder { Keyed[] ks; }` and `struct Wrap { Plain p; }`: a mapping held through a nested struct. -/
def nestedEnv : Env := ⟨mapEnv.decls ++ [
  ⟨.struct, "Outer", none, true, .struct "Outer" (.structMember (.userType ⟨"Keyed", []⟩) "k") .nil⟩,
  ⟨.struct, "Holder", none, true, .struct "Holder" (.structMember (.array (.userType ⟨"Keyed", []⟩) .none) "ks") .nil⟩,
  ⟨.struct, "Wrap", none, true, .struct "Wrap" (.structMember (.userType ⟨"Plain", []⟩) "p") .nil⟩]⟩

/-- **Nested structs**: `Outer` and `Holder` hold `Keyed`'s mapping, `Wrap` holds none; `Outer storage` does not copy to memory, `Wrap storage` does. -/
theorem nested_mapping_refused :
    nestedEnv.mapFree ⟨none, "Outer"⟩ = false ∧ nestedEnv.mapFree ⟨none, "Holder"⟩ = false ∧
    nestedEnv.mapFree ⟨none, "Wrap"⟩ = true ∧
    STy.implicit nestedEnv.isBase nestedEnv.mapFree (.struct .storage ⟨none, "Outer"⟩)
      (.struct .memory ⟨none, "Outer"⟩) = false ∧
    STy.implicit nestedEnv.isBase nestedEnv.mapFree (.struct .storage ⟨none, "Wrap"⟩)
      (.struct .memory ⟨none, "Wrap"⟩) = true := ⟨rfl, rfl, rfl, rfl, rfl⟩

def keyed : DeclName := ⟨none, "Keyed"⟩
def plain : DeclName := ⟨none, "Plain"⟩

theorem keyed_holds_mapping : mapEnv.mapFree keyed = false ∧ mapEnv.mapFree plain = true := ⟨rfl, rfl⟩

/-- `Keyed storage` to `Keyed memory` is refused; `Plain` copies. -/
theorem struct_mapping_refused :
    STy.implicit mapEnv.isBase mapEnv.mapFree (.struct .storage keyed) (.struct .memory keyed) = false ∧
    STy.implicit mapEnv.isBase mapEnv.mapFree (.struct .storage plain) (.struct .memory plain) = true := ⟨rfl, rfl⟩

/-- `Keyed[] storage` to `Keyed[] memory` is refused; `Plain[]` copies. -/
theorem array_mapping_refused :
    STy.implicit mapEnv.isBase mapEnv.mapFree (.array .storage (.struct .storage keyed) none)
      (.array .memory (.struct .memory keyed) none) = false ∧
    STy.implicit mapEnv.isBase mapEnv.mapFree (.array .storage (.struct .storage plain) none)
      (.array .memory (.struct .memory plain) none) = true := ⟨rfl, rfl⟩

/-- A storage pointer to a struct holding a mapping keeps its type. -/
theorem mapping_pointer_kept :
    STy.implicit mapEnv.isBase mapEnv.mapFree (.struct .storage keyed) (.struct .storage keyed) = true ∧
    STy.implicit mapEnv.isBase mapEnv.mapFree (.array .storage (.struct .storage keyed) none)
      (.array .storage (.struct .storage keyed) none) = true := ⟨rfl, rfl⟩

/-! ## The conversion arm -/

/-- **An implicit conversion of a `calldata` reference to a statically encoded memory array** runs `cdToMem` (`convRV`'s reference arm), keeps the memory invariant and is never `stuck`: the targets `cdToMem_static_ok` covers, which `STy.implicit` admits from `calldata` once elements are compared at the target's location. -/
theorem convRV_cd_static_ok {E : Env} {Γ' : RCtx} {H : HeapTy} (F : Fr) (n : Nat) {σ τ : STy}
    (hσ : σ.loc? = some .calldata)
    (hτ : (∃ e m, τ = .array .memory (.array .memory e (some m)) none ∧
        (STy.array .memory e (some m)).cdCopyElem E = true) ∨
      (∃ σ m, τ = .array .memory σ (some m) ∧ σ.cdCopyElem E = true))
    (v : Val E.layout σ) :
    Hoare (MemOK E H) (convRV (Γ := Γ') F n τ (.val v))
      (fun v y => MemOK E H y ∧ RValOK E y.2.heap.ty v) (fun e y => MemOK E H y ∧ NotStuck e) := by
  obtain ⟨h, off, len, rfl⟩ := Val.cd_shape hσ v
  have hne : σ ≠ τ := by
    rintro rfl
    rcases hτ with ⟨_, _, rfl, _⟩ | ⟨_, _, rfl, _⟩ <;> simp only [STy.loc?, reduceCtorEq, Option.some.injEq] at hσ
  have hc : convRV (E := E) (Γ := Γ') F n τ (.val (.cdRef h off len)) = cdToMem F τ off len := by
    unfold convRV
    rw [dif_neg hne]
    cases σ <;> first | (simp only [STy.loc?, reduceCtorEq] at hσ; done) | rfl
  rw [hc]
  exact cdToMem_static_ok F off len hτ

/-! ## The typed declaration -/

/-- The body of `function n(uint256[2][] calldata xs)`. -/
def Γ : Ctx := { env := TypingExamples.unitC.env, scope := some "C", locals := [("xs", cdNested)] }

/-- `uint256[2]`. -/
def pairT : Syn .typeName := .array u256 (.some (num 2))

/-- `uint256[2][] memory c = xs;` -/
def copyStmt : Syn (.stmt .body) :=
  .simpleStmt (.declVar (.varDecl (.array pairT .none) (some .memory) "c") (.some (.ident "xs")))

/-- **The nested copy types**: the derivation is the elaborated declaration. -/
def w_copy : StmtD (k := .body) Γ Γ.locals copyStmt (("c", memNested) :: Γ.locals) :=
  .declInit rfl rfl (.loc rfl rfl) rfl

/-- A `uint256[2][] calldata` reference at offset 0 of length 2. -/
def ref : RVal EB.layout cdNested := .val (.cdRef rfl 0 2)

/-- **The conversion of the declaration runs the nested arm**: on the frame
of `CalldataStaticCopyControls` it is that module's `nested` copy (words
1,2 and 3,4 in two inner arrays). -/
theorem convRV_nested :
    (convRV frame 0 memNested ref : EM EB [] _).run (L0 EB, sB) = nested := rfl

/-- **The typed nested copy keeps the memory invariant and is never
`stuck`**, for every frame, heap and reference. -/
theorem w_copy_ok {Γ' : RCtx} {H : HeapTy} (F : Fr) (n : Nat) (v : Val EB.layout cdNested) :
    Hoare (MemOK EB H) (convRV (Γ := Γ') F n memNested (.val v))
      (fun v y => MemOK EB H y ∧ RValOK EB y.2.heap.ty v) (fun e y => MemOK EB H y ∧ NotStuck e) :=
  convRV_cd_static_ok F n rfl (.inl ⟨u, 2, rfl, rfl⟩) v

/-! ## Elaborated, deployed and called

```solidity
contract D {
  uint256 public x;
  function n(uint256[2][] calldata xs) external { uint256[2][] memory c = xs; x = c[1][0]; }
  function b(bool[2][] calldata xs) external { bool[2][] memory c = xs; x = c.length; }
}
```
-/

def boolPairT : Syn .typeName := .array (.elem .bool) (.some (num 2))

def copyTo (t : Syn .typeName) : Syn (.item .body) :=
  .stmtItem (.simpleStmt (.declVar (.varDecl (.array t .none) (some .memory) "c") (.some (.ident "xs"))))

def unitN (target : Syn .typeName) : Syn .unit :=
  .unit (.cons (.contract false "D" .none .nil
      (.cons (.stateVar u256 (some .pub) none none false "x" .none)
      (.cons (ext "n" (.cons (cdParam (.array pairT .none) "xs") .nil)
          (.cons (copyTo target)
          (.cons (setX (.index (.index (.ident "c") (.some (num 1))) (.some (num 0)))) .nil)))
      (.cons (ext "b" (.cons (cdParam (.array boolPairT .none) "xs") .nil)
          (.cons (copyTo boolPairT)
          (.cons (setX (.member (.ident "c") "length")) .nil)))
      .nil))))
    .nil)

def elabN : Option Elaborated := elaborate (resolveUnit { pipeline := .legacy } (unitN pairT))

#guard elabN.isSome

-- **The nested copy**: `[[1, 2], [3, 4]]` copies; `c[1][0]` is 3.
#guard (elabN.map fun el => runD el 0 [callW "n(uint256[2][])" [32, 2, 1, 2, 3, 4], selOf "x()"]) ==
  some [some (.success []), some (.success []), some (.success (arg 3))]

-- **Every element is validated**: `[[true, false], [true, false]]` copies
-- (length 2); a `bool` element holding 2 reverts with no data.
#guard (elabN.map fun el => runD el 0 [callW "b(bool[2][])" [32, 2, 1, 0, 1, 0], selOf "x()"]) ==
  some [some (.success []), some (.success []), some (.success (arg 2))]
#guard (elabN.map fun el => runD el 0 [callW "b(bool[2][])" [32, 2, 1, 0, 2, 0]]) ==
  some [some (.success []), some (.revert [])]

-- **Refusal**: a `uint256[3][] memory` target does not type.
#guard (elaborate (resolveUnit { pipeline := .legacy }
  (unitN (.array u256 (.some (num 3)))))).isNone

#print axioms convRV_cd_static_ok
#print axioms w_copy_ok
#print axioms convRV_nested

end Solidity.Source.CalldataNestedCopyControls
