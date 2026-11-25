import Solidity.Correctness.Lowering.Total.StructDecode

/-! The struct-declaration decoder on one table: nested, narrow, array and mapping
members in order, their Source fields, resolution by scope, and what stays an
obligation: a repeated or interfering name, an undeclared struct, named errors. -/
namespace Solidity.Examples.Lowering.Total.StructDecode
open Solidity.Correctness.Lowering.Total.StructDecode Source
open Solidity.Correctness.Lowering.Total.ReferenceDecode (lenLit Resolved)
open Solidity.Semantics (lookupBy)

/-- `struct Inner { uint8 a; address b; }`, as the table spells it. -/
def inner : Name := "Inner{a:uint8;b:address}"
/-- `struct Outer { uint16[2][] xs; mapping(address => Inner) m; Inner i; uint n; }`. -/
def outer : Name :=
  "Outer{xs:uint16[2][];m:mapping(address=>Inner{a:uint8;b:address});i:Inner{a:uint8;b:address};n:uint}"
def C : Contract := { vars := [], structs := [("Outer", outer), ("Inner", inner)] }

def int (signed : Bool) (n : Nat) (h : n % 8 = 0 ∧ 8 ≤ n ∧ n ≤ 256 := by decide) : Syn .typeName :=
  .elem (.int signed n h)
def ps : Syn (.list (.part false)) :=
  .cons (.struct "Outer"
    (.structMember (.array (.array (int false 16) (.some (lenLit 2))) .none) "xs")
    (.cons (.structMember (.mapping (.elem .address (by decide)) none
      (.userType ⟨"Inner", []⟩) none) "m")
    (.cons (.structMember (.userType ⟨"Inner", []⟩) "i")
    (.cons (.structMember (int false 256) "n") .nil))))
  (.cons (.struct "Inner" (.structMember (int false 8) "a")
    (.cons (.structMember (.elem .address) "b") .nil)) .nil)

/-- Both declarations in table order, under their written names; the nested
struct by its written name, the widths and the mapping as declared. -/
theorem decoded : decode C = .ok ps := rfl
example : (ps.collect (some "K")).map (·.name) = ["Outer", "Inner"] := rfl
example := decode_collect decoded "K"

/-- A plain table name with narrow members: `Packed { uint8 a; int16 b; uint c; uint8[] xs; }`. -/
example : decode { vars := [], structs := [("P", "Packed")] } = .ok
    (.cons (.struct "P" (.structMember (int false 8) "a")
      (.cons (.structMember (int true 16) "b") (.cons (.structMember (int false 256) "c")
      (.cons (.structMember (.array (int false 8) .none) "xs") .nil)))) .nil) := rfl

/-! The unit: a file-level struct also named `Inner`, then contract `K`. -/

def fileInner : Decl :=
  ⟨.struct, "Inner", none, true, .struct "Inner" (.structMember (int false 256) "z") .nil⟩
def pre : List Decl := [fileInner, ⟨.contract, "K", none, true, .contract false "K" .none .nil ps⟩]
def E : Env := ⟨pre ++ ps.collect (some "K") ++ []⟩
theorem hE : E.decls = pre ++ ps.collect (some "K") ++ [] := rfl
theorem free : Free C "K" (pre ++ []) := by
  intro d md sc
  simp only [pre, List.append_nil, List.mem_cons, List.not_mem_nil, or_false] at md
  rcases md with rfl | rfl <;> cases sc

/-- From `K`, `Inner` is the contract's struct: the file-level one is shadowed. -/
example : ∃ e d, lookupBy "Inner" C.structs = some e ∧ Gen C "K" ("Inner", e) d ∧
    E.lookup (some "K") "Inner" = [d] ∧ Resolved E (some "K") "Inner" ⟨some "K", "Inner"⟩ :=
  resolved_of_free decoded hE free (by decide)
/-- From the file level it is the other one. -/
example : E.lookup none "Inner" = [fileInner] := rfl

/-- `Outer`'s Source fields are the retained ones, with every obligation discharged. -/
example : Fields C E "K" .storage outer (E.structFields ⟨some "K", "Outer"⟩ .storage) :=
  structFields_closed decoded hE free rfl (by decide) .storage fun _ _ => .inl rfl
example : E.structFields ⟨some "K", "Outer"⟩ .storage = some
    [("xs", .array .storage (.array .storage (.int ⟨false, 16, by decide⟩) (some 2)) none),
     ("m", .mapping (.address false) (.struct .storage ⟨some "K", "Inner"⟩)),
     ("i", .struct .storage ⟨some "K", "Inner"⟩), ("n", .int ⟨false, 256, by decide⟩)] := by decide
/-- `Inner` has no mapping: the same fields in memory. `Outer` has no memory type. -/
example : Fields C E "K" .memory inner (E.structFields ⟨some "K", "Inner"⟩ .memory) :=
  structFields_closed decoded hE free rfl (by decide) .memory (by decide)
example : E.structFields ⟨some "K", "Inner"⟩ .memory =
    some [("a", .int ⟨false, 8, by decide⟩), ("b", .address false)] := rfl
example : E.structFields ⟨some "K", "Outer"⟩ .memory = none := rfl

/-! Remaining obligations. -/

/-- One written name twice: both are declared, and the name resolves to neither. -/
def twice : Contract := { vars := [], structs := [("A", "A{x:uint}"), ("A", "A{y:bool}")] }
example : ∃ qs, decode twice = .ok qs ∧ (qs.collect (some "K")).map (·.name) = ["A", "A"] :=
  ⟨_, rfl, rfl⟩
example {qs : Syn (.list (.part false))} (h : decode twice = .ok qs) {E : Env}
    {pre post : List Decl} (hE : E.decls = pre ++ qs.collect (some "K") ++ post) :
    ¬ ∃ d, Resolved E (some "K") "A" d := fun r => by
  have two := ((resolved_iff h hE (by decide)).1 r).1
  revert two; decide

/-- An enum of the scope named `Inner` interferes: the name is ambiguous. -/
example {E : Env} {post : List Decl}
    (hE : E.decls = [⟨.enum, "Inner", some "K", false, .enum "Inner" "X" []⟩] ++
      ps.collect (some "K") ++ post) : ¬ ∃ d, Resolved E (some "K") "Inner" d := fun r =>
  ((resolved_iff decoded hE (by decide)).1 r).2 _ (List.mem_append_left _ List.mem_cons_self)
    ⟨rfl, rfl⟩

/-- A table struct with no entry is spelled, but nothing declares it. -/
def usesToken : Contract := { vars := [], structs := [("Outer", "Outer{t:Token;n:uint}")] }
example : decode usesToken = .ok (.cons (.struct "Outer"
    (.structMember (.userType ⟨"Token", []⟩) "t") (.cons (.structMember (int false 256) "n") .nil))
    .nil) := rfl
example : ¬ Declared usesToken "Outer{t:Token;n:uint}" := by decide

def err (C : Contract) : Option Error :=
  match decode C with
  | .error e => some e
  | .ok _ => none
def one (written table : Name) : Contract := { vars := [], structs := [(written, table)] }

/-- The contract's `Inner` shadows the table's: no identifier reads as that type. -/
example : err { vars := [], structs := [("Outer", "Outer{i:Inner;n:uint}"), ("Inner", inner)] } =
    some (.member 0 "Outer" "Outer{i:Inner;n:uint}" "i" (.unknownStruct "i" "Inner")) := rfl
/-- Two written names of one table type: a member of that type has no spelling. -/
example : err { vars := [], structs := [("A", "T{a:uint}"), ("B", "T{a:uint}"),
    ("U", "U{t:T{a:uint}}")] } =
    some (.member 2 "U" "U{t:T{a:uint}}" "t" (.ambiguousStruct "t" "T{a:uint}" ["A", "B"])) := rfl
-- an unknown table type, and one whose member the table does not keep
example : err (one "T" "Nope") = some (.noMembers 0 "T" "Nope") := rfl
example : err (one "T" "T{f:function(uint) external}") =
    some (.noMembers 0 "T" "T{f:function(uint) external}") := rfl
-- a table spelling as the written name; `string`; a `string` key, read as a hash
example : err (one "T{a:uint}" "T{a:uint}") = some (.notWritten 0 "T{a:uint}" "T{a:uint}") := rfl
example : err (one "T" "T{s:string}") = some (.member 0 "T" "T{s:string}" "s" (.erasedBytes "s")) :=
  rfl
example : err (one "T" "T{k:mapping(string=>uint)}") =
    some (.unreadRow 0 "T" "T{k:mapping(string=>uint)}" "k{}#hash" 1) := rfl
/-- A failure names its entry and the cause there. -/
example : ∃ entry, (one "T" "Nope").structs[0]? = some entry ∧
    Cause (one "T" "Nope") entry (.noMembers 0 "T" "Nope") :=
  decode_error (C := one "T" "Nope") rfl
end Solidity.Examples.Lowering.Total.StructDecode
