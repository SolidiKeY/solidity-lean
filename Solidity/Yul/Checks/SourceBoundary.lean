import Solidity.Yul.SourceBoundary
import Solidity.Yul.ScalarLocals
import Solidity.Yul.WordAdapter
/-! An actual S01 bool occurrence and declared scalar binding, a clean initial
value, and a concrete raw writer accepting EVERY word. This is not an S02/S03
statement embedding or solc-ID provider. -/
namespace Solidity.Yul.Checks.SourceBoundary
open Solidity.Source

def ctx : Solidity.Source.Ctx :=
  {env := ⟨[]⟩,scope := none,locals := [("flag",.bool)]}
def classified := (checkClassifiedSourceLocal ctx "flag").get (by decide)
def sourceCell : SourceScalarCell ctx := .ofClassified classified .boolean (by decide)
def types : List ExternalType := [.value .boolean]
def binding : ScalarBinding types ctx := ⟨sourceCell,.here⟩
def cell : WordCell types := .scalar binding.ref
def initial : WordState types 0 := ⟨Fin.elim0,fun _ => word 0⟩
def code (raw : Word) : Stmt [] types ⟨false,false⟩ 0 :=
  .assign (fun _ : Fin 1 => .external cell.writeRef) (.literal raw)
def policy (raw : Word) : Policy.StmtP .A (code raw) :=
  ⟨fun _ => True.intro,True.intro⟩

example : ctx.resolve "flag" = some (.loc 0) := rfl
example : sourceCell.ref.ty = .bool := rfl
example : sourceCell.position = 0 := rfl
example : binding.ref.position = 0 := rfl
example : cell.readRef.wordCell = some cell := cell.read_inverse
example : cell.writeRef.wordCell = some cell := cell.write_inverse
example (D : Layout) :
    (Solidity.Source.Val.bool false : Solidity.Source.Val D .bool).key = some ((initial.cells cell).val : Int) := rfl
example (D : Layout) :
    (Solidity.Source.Val.bool true : Solidity.Source.Val D .bool).key = some ((truth true).val : Int) :=
  Solidity.Yul.SourceBoundary.clean_bool_key D true

/-- The actual word runner can store and re-observe ANY raw bool word; no
cleanliness premise is imposed to make the old Source representation fit. -/
theorem write_read (raw : Word) :
    (Solidity.Yul.WordAdapter.run (code raw) (policy raw) 2 initial).map
      (fun result => result.state.cells cell) = some raw := rfl

example : (Solidity.Yul.WordAdapter.run (code (word 2)) (policy (word 2)) 2 initial).map
    (fun result => result.state.cells cell) = some (word 2) := write_read (word 2)
example : (Solidity.Yul.WordAdapter.run (code (word (2^256-1))) (policy (word (2^256-1))) 2 initial).map
    (fun result => result.state.cells cell) = some (word (2^256-1)) :=
  write_read (word (2^256-1))
example (D : Layout) (value : Solidity.Source.Val D .bool) : value.key ≠ some (2 : Int) :=
  Solidity.Yul.SourceBoundary.bool_key_ne_two value
example (D : Layout) (value : Solidity.Source.Val D (.int IntTy.u8)) : value.key ≠ some (257 : Int) :=
  Solidity.Yul.SourceBoundary.u8_key_ne_257 value
example (D : Layout) : ¬ ∃ decode : Word → Solidity.Source.Val D .bool,
    ∀ raw, (decode raw).key = some (raw.val : Int) :=
  Solidity.Yul.SourceBoundary.no_bool_key_decoder D
example (D : Layout) : ¬ ∃ decode : Word → Solidity.Source.Val D (.int IntTy.u8),
    ∀ raw, (decode raw).key = some (raw.val : Int) :=
  Solidity.Yul.SourceBoundary.no_u8_key_decoder D
example (D : Layout) (encode : Solidity.Source.Val D .bool → Word) (decode : Word → Solidity.Source.Val D .bool) :
    ¬ ∀ raw, encode (decode raw) = raw :=
  Solidity.Yul.SourceBoundary.no_bool_retraction D encode decode

theorem actual_boundary (D : Layout) :
    ((Solidity.Yul.WordAdapter.run (code (word 2)) (policy (word 2)) 2 initial).map
      (fun result => result.state.cells cell) = some (word 2)) ∧
    (∀ value : Solidity.Source.Val D .bool, value.key ≠ some ((word 2).val : Int)) := by
  constructor
  · exact write_read (word 2)
  · intro value
    rw [Solidity.Yul.SourceBoundary.word_two_val]
    exact Solidity.Yul.SourceBoundary.bool_key_ne_two value

def bindingWitness : Nonempty (ScalarBinding types ctx) := ⟨binding⟩
def dirtyWitness : ∃ raw : Word,
    (Solidity.Yul.WordAdapter.run (code raw) (policy raw) 2 initial).map
      (fun result => result.state.cells cell) = some (word 2) :=
  ⟨word 2,write_read (word 2)⟩
end Solidity.Yul.Checks.SourceBoundary
