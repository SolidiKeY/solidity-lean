import Solidity.Correctness.Lowering.Total.StructDecode

/-! The struct decoder: members in order, Source fields, resolution, open obligations. -/
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
/-- Table order, written names, the nested struct by name, widths, arrays, the mapping. -/
theorem decoded : decode C = .ok ps := rfl
/-- A file-level struct also named `Inner`, then contract `K` with the decoded parts. -/
def fileInner : Decl :=
  ⟨.struct, "Inner", none, true, .struct "Inner" (.structMember (int false 256) "z") .nil⟩
def u : Syn .unit := .unit (.cons (.topPart fileInner.node)
  (.cons (.contract false "K" .none .nil ps) .nil))
def pre : List Decl := [fileInner, ⟨.contract, "K", none, true, .contract false "K" .none .nil ps⟩]
theorem hE : u.env.decls = pre ++ ps.collect (some "K") ++ [] := rfl
theorem free : Free C "K" (pre ++ []) := by
  intro d md sc
  simp only [pre, List.append_nil, List.mem_cons, List.not_mem_nil, or_false] at md
  rcases md with rfl | rfl <;> cases sc
/-- From `K`, `Inner` is the contract's struct, the file-level one shadowed; from
the file level it is the other one. -/
example : ∃ e d, lookupBy "Inner" C.structs = some e ∧ Gen C "K" ("Inner", e) d ∧
    u.env.lookup (some "K") "Inner" = [d] ∧ Resolved u.env (some "K") "Inner" ⟨some "K", "Inner"⟩ :=
  resolved decoded hE (by decide) fun d md h => by
    have := free d md h.1; rw [h.2] at this; exact absurd this (by decide)
example : u.env.lookup none "Inner" = [fileInner] := rfl
/-- `Outer`'s Source fields are the retained ones, every obligation discharged. -/
example : Fields C u.env "K" .storage outer (u.env.structFields ⟨some "K", "Outer"⟩ .storage) :=
  structFields_closed decoded hE free rfl (by decide) .storage fun _ _ => .inl rfl
example : u.env.structFields ⟨some "K", "Outer"⟩ .storage = some
    [("xs", .array .storage (.array .storage (.int ⟨false, 16, by decide⟩) (some 2)) none),
     ("m", .mapping (.address false) (.struct .storage ⟨some "K", "Inner"⟩)),
     ("i", .struct .storage ⟨some "K", "Inner"⟩), ("n", .int ⟨false, 256, by decide⟩)] := by decide
/-- `Inner` has no mapping: the same fields in memory; `Outer`'s mapping has no memory type. -/
example : Fields C u.env "K" .memory inner (u.env.structFields ⟨some "K", "Inner"⟩ .memory) :=
  structFields_closed decoded hE free rfl (by decide) .memory (by decide)
example : u.env.structFields ⟨some "K", "Outer"⟩ .memory = none := rfl
/-- One written name twice: both are declared, and the name resolves to neither. -/
def twice : Contract := { vars := [], structs := [("A", "A{x:uint}"), ("A", "A{y:bool}")] }
example : ∃ qs, decode twice = .ok qs ∧ (qs.collect (some "K")).map (·.name) = ["A", "A"] :=
  ⟨_, rfl, rfl⟩
example {qs : Syn (.list (.part false))} (h : decode twice = .ok qs) {E : Env}
    {pre post : List Decl} (hE : E.decls = pre ++ qs.collect (some "K") ++ post) :
    ¬ ∃ d, Resolved E (some "K") "A" d := fun r => by
  have two := (resolved_only h hE (by decide) r).1
  revert two; decide
/-- An enum of the scope named `Inner` interferes: the name is ambiguous. -/
example {E : Env} {post : List Decl}
    (hE : E.decls = [⟨.enum, "Inner", some "K", false, .enum "Inner" "X" []⟩] ++
      ps.collect (some "K") ++ post) : ¬ ∃ d, Resolved E (some "K") "Inner" d := fun r =>
  (resolved_only decoded hE (by decide) r).2 _ (List.mem_append_left _ List.mem_cons_self) ⟨rfl, rfl⟩
/-- A table struct with no entry is spelled, but nothing declares it. -/
def usesToken : Contract := { vars := [], structs := [("Outer", "Outer{t:Token;n:uint}")] }
example : (decode usesToken).toOption.isSome = true := by decide
example : ¬ Declared usesToken "Outer{t:Token;n:uint}" := by decide
def err (written table : Name) (more : List (Name × Name) := []) : Option Error :=
  match decode { vars := [], structs := (written, table) :: more } with
  | .error e => some e
  | .ok _ => none
/-- The contract's `Inner` shadows the table's: no identifier reads as that type. -/
example : err "Outer" "Outer{i:Inner;n:uint}" [("Inner", inner)] =
    some (.member 0 "Outer" "Outer{i:Inner;n:uint}" "i" (.unknownStruct "i" "Inner")) := rfl
-- unknown table type; table spelling as written name; `string`; `string` key; function type
example : err "T" "Nope" = some (.noMembers 0 "T" "Nope") := rfl
example : err "T{a:uint}" "T{a:uint}" = some (.notWritten 0 "T{a:uint}" "T{a:uint}") := rfl
example : err "T" "T{s:string}" = some (.member 0 "T" "T{s:string}" "s" (.erasedBytes "s")) := rfl
example : err "T" "T{k:mapping(string=>uint)}" =
    some (.unreadRow 0 "T" "T{k:mapping(string=>uint)}" "k{}#hash" 1) := rfl
example : err "T" "T{f:function(uint)external}" =
    some (.unreadRow 0 "T" "T{f:function(uint)external}" "f#function(uint)external" 0) := rfl
end Solidity.Examples.Lowering.Total.StructDecode
