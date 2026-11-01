import Solidity.Syntax.Elab

/-! Entry-only serialization of a primitive prefix and one bytes/string memory
return, over the existing single-memory-result call. Original source lowering
runs once; encoding reads its actual return locals in declaration order.
The original contract, self-call lookup and source obligation remain unchanged. -/
namespace Solidity.Tools.EntryReturn
open Semantics

/-- These names are confined to the synthetic entry frame, never source entries. -/
def wrapperName : String := "__upstream_encoded_entry"
def resultName : String := "__upstream_encoded_result"

/-- Deliberately bounded admission: no function/reference arguments, storage
results, recursive source entry or general mixed reference tuple forwarding. -/
def admitted (C : Contract) (f : String) (d : FunDecl) : Bool :=
  d.params.all (fun (_, T) => T matches .prim _) &&
  !(d.widths.any (fun (n, _) => (n.splitOn "#function").length > 1)) &&
  d.rets.length > 1 && d.retMem && !d.retStorage &&
  (match d.rets.reverse with
    | (n, .ref R) :: rest => R == bytesR &&
        lookupBy (n ++ "[]#bytes") d.widths == some 1 &&
        lookupBy (n ++ "[]") d.widths == some 8 &&
        rest.all (fun (_, T) => T matches .prim _)
    | _ => false) &&
  !isRecursiveC C f &&
  !(C.funs.any (fun (n, _) => n == wrapperName || n == resultName)) &&
  !(C.vars.any (fun (n, _) => n == wrapperName || n == resultName)) &&
  !((d.params ++ d.rets).any (fun (n, _) => n == resultName)) &&
  !(d.body.any (·.mentions resultName))

/-- Successful preflight always requires primitive argument types. Function
markers have the separate refusal theorem below; they cannot bypass it. -/
theorem admitted_arguments (C : Contract) (f : String) (d : FunDecl)
    (h : admitted C f d = true) : d.params.all (fun (_, T) => T matches .prim _) = true := by
  simp only [admitted, Bool.and_eq_true] at h
  repeat' obtain ⟨h, _⟩ := h
  exact h

/-- Intrinsic array shape alone is insufficient: successful admission retains
actual source bytes/string markers, byte width and the primitive prefix. -/
theorem admitted_result (C : Contract) (f : String) (d : FunDecl)
    (h : admitted C f d = true) :
    (match d.rets.reverse with
    | (n, .ref R) :: rest => R == bytesR &&
        lookupBy (n ++ "[]#bytes") d.widths == some 1 &&
        lookupBy (n ++ "[]") d.widths == some 8 &&
        rest.all (fun (_, T) => T matches .prim _)
    | _ => false) = true := by
  simp only [admitted, Bool.and_eq_true] at h
  exact h.1.1.1.1.1.2

/-- Appending a synthetic declaration keeps every original visible callee's
exact declaration, not merely its return shape or its name. -/
theorem original_declaration (original extra : List (String × FunDecl)) (f : String) (d : FunDecl)
    (h : lookupBy f original = some d) : lookupBy f (original ++ extra) = some d := by
  induction original with
  | nil => cases h
  | cons pair rest ih =>
    rcases pair with ⟨g, value⟩
    by_cases hg : f = g
    · simp only [List.cons_append, lookupBy, hg, ↓reduceIte]
      simpa only [lookupBy, hg, ↓reduceIte] using h
    · simp only [List.cons_append, lookupBy, hg, ↓reduceIte]
      exact ih (by simpa only [lookupBy, hg, ↓reduceIte] using h)

/-- A detected function marker cannot enter this bridge. Marker parsing is
an extrinsic frontend check, tested separately from this Boolean interface. -/
theorem function_marker_refused (C : Contract) (f : String) (d : FunDecl)
    (h : d.widths.any (fun (n, _) => (n.splitOn "#function").length > 1) = true) :
    admitted C f d = false := by
  simp only [admitted, h, Bool.not_true, Bool.and_false, Bool.false_and]

/-- Preserve a return slot's actual source function signature; other slots
retain the existing ABI type/width/byte reconstruction. Inputs never use this. -/
def returnType (d : FunDecl) (n : String) (T : Ty) : RawTy :=
  match fnRow? d.widths n with
  | some signature => .named signature
  | none => abiRawTy T d.widths n

/-- An actual function marker is transported exactly, not replaced by uint. -/
theorem returnType_function (d : FunDecl) (n : String) (T : Ty) (signature : String)
    (h : fnRow? d.widths n = some signature) : returnType d n T = .named signature := by
  simp only [returnType, h]

/-- Shared source-frame serialization. Function return slots retain their
exact original nominal signature; argument decoding is not changed here. -/
def serialize (C : Contract) (d : FunDecl) : ElabM FunDecl := do
  let frame : ECtx := ((d.params ++ d.rets).map fun (n, T) =>
    (n, match T with
      | .prim p => LocalTy.val p ((lookupBy n d.widths).getD 256) (shapeUnder d.widths n)
      | .ref R => LocalTy.mem R (shapeUnder d.widths n))).reverse
  let original ← calleeBody C d [] false false frame
  let declarations := d.rets.map fun (n, T) =>
    match T with
    | .prim _ => RawStmt.decl (returnType d n T) n none
    | .ref _ => RawStmt.declMemory (returnType d n T) n none
  pure { d with
    sourceDecl := none, rets := [(resultName, .ref bytesR)],
    retMem := true, retStorage := false, mods := [], spec := {},
    widths := [(resultName ++ "[]", 8), (resultName ++ "[]#bytes", 1)] ++ d.widths,
    body := declarations ++ original ++
      [.ret (some (.call "abi.encode" (d.rets.map fun (n, _) => .name n)))] }

/-- The existing memory-only entry admission remains unchanged. -/
def prepare (C : Contract) (f : String) : ElabM FunDecl := do
  let some d := lookupBy f C.funs | throw "entry return bridge has no exact source declaration"
  unless admitted C f d do throw "entry return bridge needs a primitive prefix and one final bytes/string memory result"
  serialize C d

/-- The additional output-only fragment: one no-argument external-void function
value in an otherwise primitive tuple. Function arguments remain refused. -/
def functionTupleAdmitted (C : Contract) (f : String) (d : FunDecl) : Bool :=
  d.params.all (fun (_, T) => T matches .prim _) &&
  !(d.params.any (fun (n, _) => (fnRow? d.widths n).isSome)) &&
  d.rets.length > 1 && !d.retMem && !d.retStorage &&
  d.rets.all (fun (n, T) => (T matches .prim _) &&
    match fnRow? d.widths n with
    | none => true
    | some signature => fnParts? signature == some ([], [], true)) &&
  (d.rets.filter (fun (n, _) => (fnRow? d.widths n).isSome)).length == 1 &&
  !isRecursiveC C f &&
  !(C.funs.any (fun (n, _) => n == wrapperName || n == resultName)) &&
  !(C.vars.any (fun (n, _) => n == wrapperName || n == resultName)) &&
  !((d.params ++ d.rets).any (fun (n, _) => n == resultName)) &&
  !(d.body.any (·.mentions resultName))

/-- A detected function-valued input cannot enter the output-only bridge. -/
theorem function_arguments_refused (C : Contract) (f : String) (d : FunDecl)
    (h : d.params.any (fun (n, _) => (fnRow? d.widths n).isSome) = true) :
    functionTupleAdmitted C f d = false := by
  simp only [functionTupleAdmitted, h, Bool.not_true, Bool.and_false, Bool.false_and]

def prepareFunctionTuple (C : Contract) (f : String) : ElabM FunDecl := do
  let some d := lookupBy f C.funs | throw "function return bridge has no exact source declaration"
  unless functionTupleAdmitted C f d do throw "function return bridge needs one external-void function result and no function inputs"
  serialize C d

/-- Local extraction choice, not a semantic/callback/profile option. -/
inductive Plan where
  | memory
  | functionTuple

/-- Preserve the original nonrecursive function's exact rank/prefix scope.
The original entry is resolved by the same name; it is never replaced in C. -/
def scope (C : Contract) (f : String) (plan : Plan := .memory) : ElabM (List (String × FunDecl)) := do
  let some rank := C.funs.findIdx? (fun (n, _) => n == f)
    | throw "entry return bridge has no exact source rank"
  let wrapper ← match plan with
    | .memory => prepare C f
    | .functionTuple => prepareFunctionTuple C f
  pure (C.funs.take rank ++ [(wrapperName, wrapper)])

end Solidity.Tools.EntryReturn
