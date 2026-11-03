import Solidity.Yul.DirectWords
set_option Elab.async false
namespace Solidity.Yul.Checks.DirectWords
open Closed
def types : List ExternalType :=
  [.value (.unsigned 0),.value .boolean,.externalFunction,.constant (word 9)]
def small : WordCell types := .scalar ⟨.unsigned 0,.here⟩
def flag : WordCell types := .scalar ⟨.boolean,.there .here⟩
def function : Member types .externalFunction := .there (.there .here)
def initial : WordCells types := fun _ => word 0
def state : WordState types 1 := ⟨fun _ => word 7,
  Solidity.Yul.WordCells.write
    (Solidity.Yul.WordCells.write
      (Solidity.Yul.WordCells.write
        (Solidity.Yul.WordCells.write initial small (word 257)) flag (word 2))
      (.address function) (word (2^256-1)))
    (.selector function) (word (2^32+1))⟩
def args2 (a b : Expr [] types 1 1) : Fin 2 → Expr [] types 1 1 :=
  Fin.cases a (Fin.cases b Fin.elim0)
def bin (op : Pure 2) (a b : Expr [] types 1 1) : Expr [] types 1 1 :=
  .builtin (.pure op) (args2 a b)
def narrow : Expr [] types 1 1 := .external small.readRef
def boolean : Expr [] types 1 1 := .external flag.readRef
def constant : Expr [] types 1 1 := .external
  ⟨.there (.there (.there .here)),.plain,.constantRead⟩
def address : Expr [] types 1 1 := .external (WordCell.address function).readRef
def selector : Expr [] types 1 1 := .external (WordCell.selector function).readRef
def mulDiv : Expr [] types 1 1 := bin .div
  (bin .mul narrow (.external ⟨.there (.there (.there .here)),.plain,.constantRead⟩))
  (.local 0)
def division : Expr [] types 1 1 := bin .div narrow (.literal (word 0))
def modulo : Expr [] types 1 1 := bin .smod address (.literal (word 0))
def popped : Expr [] types 1 0 :=
  .builtin .pop (Fin.cases (bin .add narrow boolean) Fin.elim0)

structure Case where
  name : String
  results : Nat
  code : Expr [] types 1 results
  policy : Policy.ExprP .A code
def fixtures : List Case :=
  [⟨"raw-u8",1,narrow,by apply (Policy.expr_iff .A _).mp; rfl⟩,⟨"raw-bool",1,boolean,by apply (Policy.expr_iff .A _).mp; rfl⟩,
   ⟨"constant",1,constant,by apply (Policy.expr_iff .A _).mp; rfl⟩,⟨"address",1,address,by apply (Policy.expr_iff .A _).mp; rfl⟩,
   ⟨"selector",1,selector,by apply (Policy.expr_iff .A _).mp; rfl⟩,⟨"mulDiv",1,mulDiv,by apply (Policy.expr_iff .A _).mp; rfl⟩,
   ⟨"div-zero",1,division,by apply (Policy.expr_iff .A _).mp; rfl⟩,⟨"smod-zero",1,modulo,by apply (Policy.expr_iff .A _).mp; rfl⟩,
   ⟨"pop",0,popped,by apply (Policy.expr_iff .A _).mp; rfl⟩]
def snapshot {r} (value : Option (Values r)) : Option (List Nat) :=
  value.map (fun words => (List.ofFn words).map Fin.val)
def observe (c : Case) (fuel : Nat) := snapshot (Solidity.Yul.DirectWords.eval fuel c.code c.policy state)

example : observe ⟨"raw-u8",1,narrow,by apply (Policy.expr_iff .A _).mp; rfl⟩ 1 = some [257] := by decide
example : observe ⟨"raw-bool",1,boolean,by apply (Policy.expr_iff .A _).mp; rfl⟩ 1 = some [2] := by decide
example : observe ⟨"constant",1,constant,by apply (Policy.expr_iff .A _).mp; rfl⟩ 1 = some [9] := by decide
example : observe ⟨"address",1,address,by apply (Policy.expr_iff .A _).mp; rfl⟩ 1 = some [2^256-1] := by decide
example : observe ⟨"selector",1,selector,by apply (Policy.expr_iff .A _).mp; rfl⟩ 1 = some [2^32+1] := by decide
example : observe ⟨"mulDiv",1,mulDiv,by apply (Policy.expr_iff .A _).mp; rfl⟩ 2 = none := by decide
example : observe ⟨"mulDiv",1,mulDiv,by apply (Policy.expr_iff .A _).mp; rfl⟩ 3 = some [330] := by decide
example : observe ⟨"div-zero",1,division,by apply (Policy.expr_iff .A _).mp; rfl⟩ 2 = some [0] := by decide
example : observe ⟨"smod-zero",1,modulo,by apply (Policy.expr_iff .A _).mp; rfl⟩ 2 = some [0] := by decide
example : observe ⟨"pop",0,popped,by apply (Policy.expr_iff .A _).mp; rfl⟩ 2 = none := by decide
example : observe ⟨"pop",0,popped,by apply (Policy.expr_iff .A _).mp; rfl⟩ 3 = some [] := by decide
example : ¬ Policy.ExprP .A
    (Expr.external (F := []) (X := [.memory]) (n := 1) ⟨.here,.plain,.memoryRead⟩) := by intro h; cases h
example : ¬ Policy.ExprP .A
    (Expr.builtin (F := []) (X := types) (n := 1) .gas Fin.elim0) := by intro h; cases h.1.2
example {sig : Sig} (index : Member [] sig) : False := PEmpty.elim (peelMember index)
example (fuel : Nat) : snapshot (Solidity.Yul.DirectWords.eval fuel mulDiv (by apply (Policy.expr_iff .A _).mp; rfl) state) =
    snapshot (evalExpr fuel .nil True.intro
      (WordAdapter.expression mulDiv (by apply (Policy.expr_iff .A _).mp; rfl) (Fin.castAdd (wordCellCount types))
        (fun cell => Fin.natAdd 1 cell.slot)).code
      (WordAdapter.expression mulDiv (by apply (Policy.expr_iff .A _).mp; rfl) (Fin.castAdd (wordCellCount types))
        (fun cell => Fin.natAdd 1 cell.slot)).words state.pack) :=
  congrArg snapshot (Solidity.Yul.DirectWords.packed_agrees fuel mulDiv (by apply (Policy.expr_iff .A _).mp; rfl) state)
def inhabited : Nonempty (WordState types 1) := ⟨state⟩
def programWitness : ∃ code : Expr [] types 1 1,
    ∃ policy : Policy.ExprP .A code,
      snapshot (Solidity.Yul.DirectWords.eval 3 code policy state) = some [330] :=
  ⟨mulDiv,by apply (Policy.expr_iff .A _).mp; rfl,by decide⟩
#eval do
  let mut count := 0
  for c in fixtures do
    let lowered := WordAdapter.expression c.code c.policy
      (Fin.castAdd (wordCellCount types)) (fun cell => Fin.natAdd 1 cell.slot)
    for fuel in List.range 9 do
      unless observe c fuel == snapshot (evalExpr fuel .nil True.intro lowered.code lowered.words state.pack) do
        throw (IO.userError ("direct original-AST agreement failed: " ++ c.name))
      count := count + 1
  unless count == 81 do throw (IO.userError "direct expression matrix incomplete")
  IO.println "DIRECT_WORDS_COMPILED_PASS:81 original-AST/actual packed-interpreter comparisons; not compiler/EVM tests"
#check @Solidity.Yul.DirectWords.agrees
#check @Solidity.Yul.DirectWords.packed_agrees
#print axioms Solidity.Yul.DirectWords.packed_agrees
#print axioms Solidity.Yul.DirectWords.stable
end Solidity.Yul.Checks.DirectWords
