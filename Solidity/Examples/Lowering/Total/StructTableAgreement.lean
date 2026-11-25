import Solidity.Correctness.Lowering.Total.StructTableAgreement

/-! Nested struct references against their model tables: arrays, fixed arrays and
mapping values; implicit fallback, ambiguous names, absent and ambiguous spellings,
locations. -/
namespace Solidity.Examples.Lowering.Total.StructTableAgreement
open Solidity.Correctness.Lowering.Total Source
open StructTableAgreement
open StructDecode (decode Fields Free)
open ReferenceDecode (Resolved written?)
open Solidity.Semantics (lookupBy structDef)

/-- Contract `K` holding the decoded parts `ps`, after a file-level declaration. -/
def unit (top : Syn (.part true)) (ps : Syn (.list (.part false))) : Syn .unit :=
  .unit (.cons (.topPart top) (.cons (.contract false "K" .none .nil ps) .nil))
def surround (top : Decl) (ps : Syn (.list (.part false))) : List Decl :=
  [top, ⟨.contract, "K", none, true, .contract false "K" .none .nil ps⟩]
/-- The decoded parts, kept opaque to elaboration; facts about them are kernel-checked. -/
@[irreducible] def parts (C : Contract) : Syn (.list (.part false)) :=
  match decode C with | .ok ps => ps | .error _ => .nil
theorem parts_ok {C : Contract} (h : (decode C).toBool = true) : decode C = .ok (parts C) := by
  unfold parts; cases hd : decode C <;> simp_all [Except.toBool]

/-! ## References in arrays, fixed arrays, mapping values and directly -/

/-- `struct Inner { uint8 a; address b; }`, as the table spells it. -/
def inner : Name := "Inner{a:uint8;b:address}"
/-- `struct Outer { Inner[] xs; Inner[2] f; mapping(address => Inner) m; Inner i; }`. -/
def outer : Name :=
  "Outer{xs:Inner{a:uint8;b:address}[];f:Inner{a:uint8;b:address}[2];m:mapping(address=>Inner{a:uint8;b:address});i:Inner{a:uint8;b:address}}"
def C : Contract := { vars := [], structs := [("Outer", outer), ("Inner", inner)] }
/-- A file-level struct also named `Inner`, shadowed from `K`. -/
def fileInner : Decl :=
  ⟨.struct, "Inner", none, true, .struct "Inner" (.structMember (.elem .bool) "z") .nil⟩
def u : Syn .unit := unit fileInner.node (parts C)
theorem decoded : decode C = .ok (parts C) := parts_ok (by decide +kernel)
theorem hE : u.env.decls = surround fileInner (parts C) ++ (parts C).collect (some "K") ++ [] := rfl
theorem free : Free C "K" (surround fileInner (parts C) ++ []) := by
  intro d md sc
  simp only [surround, List.append_nil, List.mem_cons, List.not_mem_nil, or_false] at md
  rcases md with rfl | rfl <;> cases sc
theorem closed : Closed C := by decide +kernel

/-- The references of `Outer`'s members: an array, a fixed array and the direct one keep
the location; the mapping value is in storage. -/
example : (structDef outer).flatMap (fun x => refsTy .memory x.2) =
    [(inner, .memory), (inner, .memory), (inner, .storage), (inner, .memory)] := by decide +kernel
/-- Every reference of `Outer` (here the mapping value) agrees with `Inner`'s table. -/
example : ∃ w, written? C inner = some w ∧ Agrees C u.env "K" w inner ∧ (w, inner) ∈ C.structs :=
  edge_agrees decoded hE free closed (t := outer) (loc := .memory) (p := (inner, .storage)) (by decide +kernel)
    ⟨("m", .ref (.mapping .uint (.ref (.struct inner)))), by decide +kernel, by decide +kernel⟩
/-- `Inner`'s agreement: entry, the generated declaration lookup selects (not the file-level
one), the resolved identity, and its fields in memory and storage. -/
theorem innerAgrees : Agrees C u.env "K" "Inner" inner := agrees decoded hE free rfl (by decide +kernel) (by decide +kernel)
example : (u.env.lookup none "Inner").map (fun d => (d.scope, d.name)) = [(none, "Inner")] := by
  decide +kernel
example : Fields C u.env "K" .memory inner (u.env.structFields ⟨some "K", "Inner"⟩ .memory) :=
  innerAgrees.fields .memory (by decide +kernel)
example : u.env.structFields ⟨some "K", "Inner"⟩ .memory =
    some [("a", .int ⟨false, 8, by decide⟩), ("b", .address false)] := by decide +kernel
/-- `Outer` in storage: its fields, and at each reference the leaf naming `K`'s `Inner`. -/
example := table_agreement decoded hE free closed (w0 := "Outer") (t := outer) rfl (loc := .storage)
  (by decide +kernel)
example : u.env.structFields ⟨some "K", "Outer"⟩ .storage = some
    [("xs", .array .storage (.struct .storage ⟨some "K", "Inner"⟩) none),
     ("f", .array .storage (.struct .storage ⟨some "K", "Inner"⟩) (some 2)),
     ("m", .mapping (.address false) (.struct .storage ⟨some "K", "Inner"⟩)),
     ("i", .struct .storage ⟨some "K", "Inner"⟩)] := by decide +kernel

/-! ## Implicit table-name fallback -/

/-- `Account` references `Token`, which no entry keys: `Token` is written by the fallback. -/
def F : Contract := { vars := [], structs := [("Acct", "Account")] }
def fileToken : Decl :=
  ⟨.struct, "Token", none, true, .struct "Token" (.structMember (.elem .bool) "z") .nil⟩
def v : Syn .unit := unit fileToken.node (parts F)
theorem decodedF : decode F = .ok (parts F) := parts_ok (by decide +kernel)
theorem hEF : v.env.decls = surround fileToken (parts F) ++ (parts F).collect (some "K") ++ [] := rfl
example : written? F "Token" = some "Token" ∧ lookupBy "Token" F.structs = none := ⟨rfl, rfl⟩
example : ¬ Closed F := by decide +kernel
/-- No generated declaration carries `Token`; from `K` it denotes the unrelated
file-level struct, not the model table. -/
example : ((parts F).collect (some "K")).filter (StructDecode.named "K" "Token") = [] :=
  (fallback_unbound decodedF hEF (s := "Token") rfl rfl).2.2.1
example : (v.env.lookup (some "K") "Token").map (fun d => (d.scope, d.name)) = [(none, "Token")] := by
  decide +kernel
/-- Without the file-level `Token` the declaration is absent: lookup finds nothing. -/
def v' : Syn .unit := unit fileInner.node (parts F)
example : (v'.env.lookup (some "K") "Token").isEmpty = true := by decide +kernel

/-! ## Ambiguous names and first entry -/

/-- `I` is keyed twice, first to `Inner`'s table: `O`'s member spells `I`. -/
def A : Contract :=
  { vars := [], structs := [("O", "O{i:Inner{a:uint8;b:address}}"), ("I", inner), ("I", "Inner{c:bool}")] }
def w : Syn .unit := unit fileInner.node (parts A)
theorem decodedA : decode A = .ok (parts A) := parts_ok (by decide +kernel)
theorem hEA : w.env.decls = surround fileInner (parts A) ++ (parts A).collect (some "K") ++ [] := rfl
example : written? A inner = some "I" ∧ ¬ Closed A := ⟨rfl, by decide +kernel⟩
/-- Unresolved, though the first entry is `Inner`'s table ... -/
example : lookupBy "I" A.structs = some inner ∧ ¬ ∃ d, Resolved w.env (some "K") "I" d :=
  ambiguous decodedA hEA rfl (by decide +kernel)
/-- ... whose fields `declOf` selects, the later `I` ignored. -/
example : Fields A w.env "K" .storage inner (w.env.structFields ⟨some "K", "I"⟩ .storage) :=
  first_fields decodedA hEA rfl (by decide +kernel) (fun d md h => by
    simp only [surround, List.mem_cons, List.not_mem_nil, or_false] at md
    rcases md with rfl | rfl <;> cases h.2.1) .storage (by decide +kernel) fun y hy s hs => by
    have none : ∀ y ∈ structDef inner, ReferenceDecode.structsTy y.2 = [] := by decide +kernel
    simp [none y hy] at hs

/-! ## Absent and ambiguous spellings fail decoding -/

def err (C : Contract) : Option StructDecode.Error :=
  match decode C with | .error e => some e | .ok _ => none
/-- No identifier reads as `Inner`'s table type (the contract's `Inner` keys another). -/
example : err { vars := [], structs := [("O", "O{i:Inner{a:uint8;b:address}}"), ("Inner", "Inner{c:bool}")] } =
    some (.member 0 "O" "O{i:Inner{a:uint8;b:address}}" "i" (.unknownStruct "i" inner)) := rfl
/-- Two identifiers read as it. -/
example : err { vars := [], structs := [("O", "O{i:Inner{a:uint8;b:address}}"), ("I", inner), ("J", inner)] } =
    some (.member 0 "O" "O{i:Inner{a:uint8;b:address}}" "i" (.ambiguousStruct "i" inner ["I", "J"])) := rfl

/-! ## Locations -/

/-- `W` has a mapping member; `O` holds an array of `W`. -/
def wm : Name := "W{k:mapping(uint=>uint);n:uint}"
def L : Contract := { vars := [], structs := [("O", "O{ws:W{k:mapping(uint=>uint);n:uint}[]}"), ("W", wm)] }
def x : Syn .unit := unit fileInner.node (parts L)
theorem decodedL : decode L = .ok (parts L) := parts_ok (by decide +kernel)
theorem hEL : x.env.decls = surround fileInner (parts L) ++ (parts L).collect (some "K") ++ [] := rfl
theorem freeL : Free L "K" (surround fileInner (parts L) ++ []) := by
  intro d md sc
  simp only [surround, List.append_nil, List.mem_cons, List.not_mem_nil, or_false] at md
  rcases md with rfl | rfl <;> cases sc
theorem agreesL : Agrees L x.env "K" "W" wm := agrees decodedL hEL freeL rfl (by decide +kernel) (by decide +kernel)
/-- In storage the reference agrees; in memory `W` is not `Placed` and has no fields. -/
example : Fields L x.env "K" .storage wm (x.env.structFields ⟨some "K", "W"⟩ .storage) :=
  agreesL.fields .storage (by decide +kernel)
example : ¬ Placed wm .memory ∧ x.env.structFields ⟨some "K", "W"⟩ .memory = none :=
  ⟨by decide +kernel, by decide +kernel⟩
/-- A mapping value is elaborated in storage whatever the outer location. -/
example : refsTy .memory (.ref (.mapping .uint (.ref (.struct wm)))) = [(wm, .storage)] := rfl

end Solidity.Examples.Lowering.Total.StructTableAgreement
