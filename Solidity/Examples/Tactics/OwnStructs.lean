import Solidity.Calculus.Close
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers

/-!
# A contract's own structs

`contract!{ struct S { … } … }` declares a struct the struct table does not
list (`docs/semantic-gaps.md`, "Struct table"): its type is the table's
struct whose name spells its members (`Semantics.StructEnc`), so the
storage, the heap, the rules and the closers read it as any other, and it
prints by the name it is written by.  A struct whose name and members are the
table's keeps the plain name.  Here they are nested, hold a mapping, sit in
an array, and are built by a struct literal; two share a table struct's name
with other members.
-/
namespace Solidity.Examples.Tactics.OwnStructs

def OwnStructsExample : Contract := contract!{
  struct Point { uint x; uint y; }
  struct Line { Point start; Point stop; uint8 width; }
  struct Account { uint balance; mapping(uint => uint) allowance; }
  struct Pair { uint a; bool b; }
  struct Token { uint value; }
  Line line;
  Line[] lines;
  mapping(uint => Account) accounts;
  Pair pair;
  Token token;
}

/--
info: [("Point", "Point{x:uint;y:uint}"), ("Line", "Line{start:Point{x:uint;y:uint};stop:Point{x:uint;y:uint};width:uint8}"),
  ("Account", "Account{balance:uint;allowance:mapping(uint=>uint)}"), ("Pair", "Pair{a:uint;b:bool}"),
  ("Token", "Token")]
-/
#guard_msgs in #eval OwnStructsExample.structs

/-- The narrow member's width, read back from the name. -/
example : Semantics.structWidths
    "Line{start:Point{x:uint;y:uint};stop:Point{x:uint;y:uint};width:uint8}" = [("width", 8)] := by
  decide

local instance : InContract := ⟨OwnStructsExample⟩

open scoped Scoped

/-- Nested members. -/
theorem nested : ⊨ᶠ dl!{ [ line.start.x = 1; line.stop.y = 2; ] line.start.x + line.stop.y == 3 } := by
  sol_symex
  sol_close

/-- A mapping member, and `delete` of its struct. -/
theorem mappingMember :
    ⊨ᶠ dl!{ [ accounts[7].allowance[3] = 9; accounts[7].balance = 5; ]
      accounts[7].balance == 5 && accounts[7].allowance[3] == 9 } := by
  sol_symex
  sol_close

theorem deleteMappingMember :
    ⊨ᶠ dl!{ [ accounts[7].balance = 5; delete accounts[7]; ] accounts[7].balance == 0 } := by
  sol_symex
  sol_close

/-- An array of structs. -/
theorem arrayOfStructs :
    ⊨ᶠ dl!{ lines.length == 1 → [ lines[0].width = 3; lines[0].stop.x = 4; ]
      lines[0].width == 3 && lines[0].stop.x == 4 } := by
  sol_symex
  sol_close

/-- A struct literal, copied into storage. -/
theorem literal :
    ⊨ᶠ dl!{ [ Point memory p = Point(4, 5); line.start = p; ] line.start.y == 5 } := by
  sol_symex
  sol_close

/-- A named struct literal of the contract's `Pair`, not the table's. -/
theorem namedLiteral : ⊨ᶠ dl!{ [ pair = Pair({b: true, a: 2}); ] pair.b == true && pair.a == 2 } := by
  sol_symex
  sol_close

/-- error: struct Bad: identifier already declared: member a -/
#guard_msgs in
example : Contract := contract!{ struct Bad { uint a; bool a; } Bad b; }

/-- error: struct Loop contains itself: no struct of the table does (`structDef_rank_lt`) -/
#guard_msgs in
example : Contract := contract!{ struct Loop { uint n; Loop[] xs; } Loop l; }

end Solidity.Examples.Tactics.OwnStructs
