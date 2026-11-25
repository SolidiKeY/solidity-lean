import Solidity.Correctness.Lowering.Total.ReferenceDecode

/-! The reference decoder on one signature, its Source types, named errors. -/
namespace Solidity.Examples.Lowering.Total.ReferenceDecode
open Solidity.Correctness.Lowering.Total.ReferenceDecode Source

/-- `struct Pair { uint a; uint8 b; }`, spelled in the table by its members. -/
def pairs : Contract := { vars := [], structs := [("Pair", "Pair{a:uint;b:uint8}")] }
def pair : Ty := .ref (.struct "Pair{a:uint;b:uint8}")
def u8 : Syn .typeName := .elem (.int false 8 (by decide))

/-- `function f(uint8[3][] memory xs, Pair storage p, uint n,
mapping(address => uint8[]) storage m, uint[][2] calldata ys) returns (Pair memory r)`. -/
def f : FunDecl where
  params := [("xs", .ref (.array (.ref (.fixed .uint 3)))), ("p", pair), ("n", .uint),
    ("m", .ref (.mapping .uint (.ref (.array .uint)))), ("ys", .ref (.fixed (.ref (.array .uint)) 2))]
  paramLocs := [("xs", .memory), ("p", .storage), ("m", .storage), ("ys", .calldata)]
  rets := [("r", pair)]
  retMem := true
  widths := [("xs[][]", 8), ("m{}#address", 20), ("m[][]", 8)]
  body := []

theorem f_signature : signature pairs f = .ok
    (.cons (.param (.array (.array u8 (.some (lenLit 3))) .none) (some .memory) (some "xs"))
    (.cons (.param (.userType ⟨"Pair", []⟩) (some .storage) (some "p"))
    (.cons (.param (.elem (.int false 256 (by decide))) none (some "n"))
    (.cons (.param (.mapping (.elem .address (by decide)) none (.array u8 .none) none)
      (some .storage) (some "m"))
    (.cons (.param (.array (.array (.elem (.int false 256 (by decide))) .none)
      (.some (lenLit 2))) (some .calldata) (some "ys")) .nil)))),
     .cons (.param (.userType ⟨"Pair", []⟩) (some .memory) (some "r")) .nil) := rfl

/-- The actual Source parameter types, once `Pair` resolves to a declaration `d`. -/
example (E : Source.Env) (d : Source.DeclName) (h : Resolved E (some "C") "Pair" d) :
    ∃ ps rs, signature pairs f = .ok (ps, rs) ∧ ps.tys E (some "C") .memory = some
      [.array .memory (.array .memory (.int ⟨false, 8, by decide⟩) (some 3)) none,
        .struct .storage d, .int ⟨false, 256, by decide⟩,
        .mapping (.address false) (.array .storage (.int ⟨false, 8, by decide⟩) none),
        .array .calldata (.array .calldata (.int ⟨false, 256, by decide⟩) none) (some 2)] :=
  ⟨_, _, f_signature, by
    have none : Source.arrayLen .none = some none := rfl
    simp [Source.Syn.tys, h.userTy, Source.Env.keyTy, arrayLen_lenLit, none, u8, Source.Elem.ty]⟩

/-- The frame context cannot tell `calldata` from `memory`; the decoded list does. -/
def g : FunDecl := { f with paramLocs := [("xs", .calldata), ("p", .storage), ("m", .storage),
  ("ys", .calldata)] }
example : f.paramCtx = g.paramCtx := rfl
example {Γ : ECtx} (h : g.paramCtx = .ok Γ) := (paramCtx_reverse h).1
example : frameTy [] "a" (.ref (.array .uint)) (some .calldata) = .mem (.array .uint) [] :=
  (frameTy_memory_calldata [] "a" _).symm
example : (signature pairs g).map (fun s => declaredLocs s.1) =
    .ok [some .calldata, some .storage, none, some .storage, some .calldata] := rfl

def a (locs : List (Name × ParamLoc)) (widths : List (Name × Nat)) : FunDecl :=
  { params := [("a", .ref (.array .uint))], paramLocs := locs, widths := widths, body := [] }
def r (T : Ty) (mem sto : Bool) : FunDecl :=
  { params := [], rets := [("r", T)], retMem := mem, retStorage := sto, body := [] }

example : signature pairs (a [] []) = .error (.missingLocation "a") := rfl
/-- `Pair` is the only identifier read as its table type. -/
example : pairs.structName? "Pair" = some "Pair{a:uint;b:uint8}" :=
  ((written?_iff (C := pairs) rfl "Pair").mpr rfl).1
example (E : Source.Env) := signature_frame (C := pairs) (d := a [("a", .memory)] []) (E := E)
  (scope := none) rfl (by simp [a, structsTy, structsRef]) .nil false false
example : signature pairs (a [("a", .memory)] [("a[]", 8), ("a[]#bytes", 1)]) =
    .error (.erasedBytes "a") := rfl
example : signature pairs { f with paramLocs := [("xs", .memory), ("p", .storage), ("m", .memory)] } =
    .error (.mappingOutsideStorage "m" .memory) := rfl
example : signature pairs { params := [("c", .uint)], widths := [("c#enum", 1)], body := [] } =
    .error (.unreadRow "c" "c#enum" 1) := rfl
example : signature pairs (r pair false false) = .error (.missingReturnLocation "r") := rfl
example : signature pairs (r .uint true false) = .error (.locationOnValueReturn "r") := rfl
example : signature { vars := [], structs := [("A", "A{a:uint}"), ("B", "A{a:uint}")] }
    (r (.ref (.struct "A{a:uint}")) true false) =
    .error (.ambiguousStruct "r" "A{a:uint}" ["A", "B"]) := rfl
end Solidity.Examples.Lowering.Total.ReferenceDecode
