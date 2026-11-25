import Solidity.Correctness.Lowering.Total.StructRows

/-! Struct member rows: support, first match, filtering and first failures. -/
namespace Solidity.Examples.Lowering.Total.StructRows
open Solidity.Correctness.Lowering.Total.StructRows
open Solidity.Correctness.Lowering.Total.StructDecode (members part parts decode Error stray)
open Solidity.Semantics (structWidths structDef)
open Solidity.Correctness.Lowering.Total.ReferenceDecode (spellType lenLit readTy)

def C : Contract := { vars := [], structs := [("Inner", "Inner{a:uint8;b:address}")] }
/-- `uint16[2][] xs; mapping(uint8 => int24[]) m; Inner i; bool f;` -/
def xs : Name × Ty := ("xs", .ref (.array (.ref (.fixed (.prim .uint) 2))))
def fs : List (Name × Ty) :=
  [xs,
   ("m", .ref (.mapping .uint (.ref (.array (.prim .int))))),
   ("i", .ref (.struct "Inner{a:uint8;b:address}")), ("f", .prim .bool)]
/-- The rows of the members, a stray row, and a shadowed second `xs[][]` row. -/
def w : List (Name × Nat) :=
  [("xs[][]", 16), ("junk", 3), ("m{}", 8), ("m[][]", 24), ("xs[][]", 32)]

def uintN (n : Nat) (h : n % 8 = 0 ∧ 8 ≤ n ∧ n ≤ 256 := by decide) : Source.Syn .typeName :=
  .elem (.int false n h)
def xsAt (t : Source.Syn .typeName) : Source.Syn (.list .structMember) :=
  .cons (.structMember (.array (.array t (.some (lenLit 2))) .none) "xs") .nil
def intN (n : Nat) (h : n % 8 = 0 ∧ 8 ≤ n ∧ n ≤ 256 := by decide) : Source.Syn .typeName :=
  .elem (.int true n h)
/-- Nested members succeed: arrays, a fixed array, a mapping key and value, a struct. -/
example : members C w fs = .ok (.cons (.structMember (.array (.array (uintN 16)
      (.some (lenLit 2))) .none) "xs")
    (.cons (.structMember (.mapping (.elem (.int false 8 (by decide)) (by decide)) none
      (.array (intN 24) .none) none) "m")
    (.cons (.structMember (.userType ⟨"Inner", []⟩) "i")
    (.cons (.structMember (.elem .bool) "f") .nil)))) := rfl
/-- Only the rows of a spelling's own keys matter. -/
example : spellType C (w.filter fun r => (readTy "xs" xs.2).contains r.1) "xs" .storage xs.2 =
    spellType C w "xs" .storage xs.2 := spellType_filter C _ _ _ (fun _ hk => by simpa using hk) w
/-- The support is conservative: it lists `#address`/`#bytes` markers nobody set. -/
example : support fs = ["xs[][]", "xs[][]#address", "xs[][]#bytes", "m{}", "m{}#address",
    "m{}#bytes", "m[][]", "m[][]#address", "m[][]#bytes", "f", "f#address", "f#bytes"] := rfl
/-- Filtering to the support (dropping `junk`) keeps the spelling. -/
example : members C (w.filter fun r => (support fs).contains r.1) fs = members C w fs :=
  members_filter_support C fs w
/-- `junk` is the first stray row; after filtering none is. -/
example : stray w fs = some ("junk", 3) := rfl
example : stray (w.filter fun r => (support fs).contains r.1) fs = none := stray_filter_support fs w

/-- First match: the first `xs[][]` row decides (`uint16`); the later one is ignored. -/
example : members C [("xs[][]", 16), ("xs[][]", 32)] [xs] =
    members C [("xs[][]", 16)] [xs] :=
  members_congr C _ fun k _ => (agree_shadow [k] "xs[][]" 16 [("xs[][]", 32)] k (by simp)).trans
    (by simp [Solidity.Semantics.lookupBy])
example : members C [("xs[][]", 16), ("xs[][]", 32)] [xs] = .ok (xsAt (uintN 16)) := rfl
example : members C [("xs[][]", 32), ("xs[][]", 16)] [xs] = .ok (xsAt (uintN 32)) := rfl
/-- A struct member reads no row: any table spells it alike. -/
example : spellType C w "i" .storage (.ref (.struct "Inner{a:uint8;b:address}")) =
    spellType C [] "i" .storage (.ref (.struct "Inner{a:uint8;b:address}")) := rfl

/-- Competing member failures: the first by position wins, even under a repeated name. -/
def bad : List (Name × Ty) :=
  [("a", .prim .uint), ("a", .ref (.fixed (.prim .uint) 0)), ("b", .ref (.array (.prim .uint)))]
example : members C [("a", 7)] bad = .error ("a", .unrepresentable "a" .uint) := rfl
/-- The second member, after one that spells, by the characterization. -/
example : members C [] bad = .error ("a", .zeroLength "a") :=
  (members_error_iff C [] bad _ _).2
    ⟨[("a", .prim .uint)], _, [_], rfl, by simp only [List.mem_singleton, forall_eq]; exact ⟨_, rfl⟩,
      rfl, rfl⟩

/-- Empty-member rejection, and a successful entry with its declaration. -/
example : members C w [] = .ok .nil := (members_eq_ok_nil_iff C w []).2 rfl
example : part C 0 ("Inner", "Inner{a:uint8;b:address}") = .ok (.struct "Inner"
    (.structMember (uintN 8) "a") (.cons (.structMember (.elem .address) "b") .nil)) := rfl
/-- Branch priority: an unwritten name before missing members; a failing member (the
`string` value, erased to `bytes`) before the stray `k{}#hash` row. -/
example : part C 3 ("A{x:uint}", "Nope") = .error (.notWritten 3 "A{x:uint}" "Nope") := rfl
example : part C 3 ("A", "Nope") = .error (.noMembers 3 "A" "Nope") := rfl
example : part C 3 ("T", "T{k:mapping(string=>string)}") =
    .error (.member 3 "T" "T{k:mapping(string=>string)}" "k" (.erasedBytes "k[]")) := rfl
example : stray (structWidths "T{k:mapping(string=>string)}")
    (structDef "T{k:mapping(string=>string)}") = some ("k{}#hash", 1) := rfl
/-- An unwritten name before a failing member. -/
example : part C 0 ("", "T{s:string}") = .error (.notWritten 0 "" "T{s:string}") := rfl
/-- A member failure from its characterization: the only member, the `string`. -/
example : part C 4 ("T", "T{s:string}") = .error (.member 4 "T" "T{s:string}" "s" (.erasedBytes "s")) :=
  part_error_member_iff.2 ⟨rfl, rfl, rfl, rfl, by decide, [], _, [], rfl, by simp, rfl, rfl⟩
/-- A stray row read back: the `string` key's hash marker is outside the support. -/
example : "k{}#hash" ∉ support (structDef "T{k:mapping(string=>uint)}") :=
  let ⟨_, _, _, _, _, _, _, _, _, _, h⟩ := part_error_unreadRow_iff.1
    (show part C 1 ("T", "T{k:mapping(string=>uint)}") =
      .error (.unreadRow 1 "T" "T{k:mapping(string=>uint)}" "k{}#hash" 1) from rfl); h

/-- Competing entries from a starting index: the first failing entry, at start plus position. -/
def es : List (Name × Name) :=
  [("Inner", "Inner{a:uint8;b:address}"), ("Inner", "Inner{a:uint8;b:address}"),
   ("T", "T{s:string}"), ("U", "Nope")]
/-- Two representable entries first, then the failing one, by the characterization. -/
example : parts C 5 es = .error (.member 7 "T" "T{s:string}" "s" (.erasedBytes "s")) :=
  (parts_error_iff 5 es _).2 ⟨es.take 2, ("T", "T{s:string}"), [("U", "Nope")], rfl,
    fun e m => (representable_iff_part 0 e).2 (by
      simp only [es, List.take, List.mem_cons, List.not_mem_nil, or_false, or_self] at m
      subst m; exact ⟨_, rfl⟩), rfl⟩
/-- The error names the failing entry: the start plus two retained entries. -/
example : ∃ pre e post, es = pre ++ e :: post ∧ 7 = 5 + pre.length ∧ e = ("T", "T{s:string}") :=
  let ⟨pre, e, post, hes, _, hi, hw, ht, _⟩ := parts_error_index
    (show parts C 5 es = .error (.member 7 "T" "T{s:string}" "s" (.erasedBytes "s")) from rfl)
  ⟨pre, e, post, hes, hi, Prod.ext hw.symm ht.symm⟩
/-- `decode` starts at zero; a duplicated entry is decoded twice before the failure. -/
example : ∃ pre e post, es = pre ++ e :: post ∧ pre.length = 2 ∧
    part { vars := [], structs := es } pre.length e =
      .error (.member 2 "T" "T{s:string}" "s" (.erasedBytes "s")) :=
  let ⟨pre, e, post, h, _, he⟩ := (decode_error_iff { vars := [], structs := es } _).1 rfl
  ⟨pre, e, post, h, by have := (part_error_entry he).1; simpa [Error.index] using this.symm, he⟩
end Solidity.Examples.Lowering.Total.StructRows
