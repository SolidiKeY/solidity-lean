import Solidity.Source.Progress.ScalarBuiltinControls

/-! Controls for `sha256`, `ripemd160`, `require` and `revert` with
string-literal arguments, on actual elaborated builtin calls. -/

namespace Solidity.Source.Progress.LiteralBuiltinControls
open EM Preservation.AllocationControls

def shaSyn : Syn .expr := .call (.ident "sha256") (.positional (.cons (.lit (.str [7,9])) .nil))
def shaTyped : Typed ctx shaSyn .bytes32 := .builtinCall rfl rfl (.cons (.str _) .nil) rfl
def ripemdSyn : Syn .expr := .call (.ident "ripemd160") (.positional (.cons (.lit (.str [7,9])) .nil))
def ripemdTyped : Typed ctx ripemdSyn .bytes20 := .builtinCall rfl rfl (.cons (.str _) .nil) rfl

def grown : St E := {BuiltinControls.initial with heap :=
  (BuiltinControls.initial.heap.alloc ⟨.bytes .memory, .bytes [7,9]⟩).1}

theorem sha_run (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    (evalE (glob p fixed) frame 10 shaTyped.toR).run (.cons (.bool false) .nil, BuiltinControls.initial) =
      (.ok (.val (mkBytes (n := 32) (h := by decide) ((fixed.evm.precompile .sha256 [7,9]).getD []))),
        (.cons (.bool false) .nil, grown)) := by cases p <;> rfl

theorem ripemd_run (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    (evalE (glob p fixed) frame 10 ripemdTyped.toR).run (.cons (.bool false) .nil, BuiltinControls.initial) =
      (.ok (.val (mkBytes (n := 20) (h := by decide) (((fixed.evm.precompile .ripemd160 [7,9]).getD []).drop 12))),
        (.cons (.bool false) .nil, grown)) := by cases p <;> rfl

def requireSyn : Syn .expr := .call (.ident "require")
  (.positional (.cons (.lit (.bool false)) (.cons (.lit (.str [110,111])) .nil)))
def requireTyped : Typed ctx requireSyn (.tuple []) :=
  .builtinCall rfl rfl (.cons (.bool false) (.cons (.str _) .nil)) rfl
def revertSyn : Syn .expr := .call (.ident "revert") (.positional (.cons (.lit (.str [110,111])) .nil))
def revertTyped : Typed ctx revertSyn (.tuple []) :=
  .builtinCall rfl rfl (.cons (.str _) .nil) rfl

theorem require_message (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    (evalE (glob p fixed) frame 10 requireTyped.toR).run (.cons (.bool false) .nil, BuiltinControls.initial) =
      (.error (.revert (errorData [110,111])), (.cons (.bool false) .nil, BuiltinControls.initial)) := by cases p <;> rfl

theorem revert_message (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    (evalE (glob p fixed) frame 10 revertTyped.toR).run (.cons (.bool false) .nil, BuiltinControls.initial) =
      (.error (.revert (errorData [110,111])), (.cons (.bool false) .nil, BuiltinControls.initial)) := by cases p <;> rfl

theorem hash_progress (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) (b : Builtin)
    (hb : b = .keccak256 ∨ b = .sha256 ∨ b = .ripemd160) (n : Nat)
    (k : Nat) (hk : 0 < k ∧ k ≤ 32) :
    NS (evalBuiltin (glob p fixed) frame n b
      (.cons (.str [7,9]) (.nil : RArgs E [.bool] [])) (.fixedBytes k hk)) :=
  builtinFragment_ns _ _ (Source.exprNSAt _ _)
    (.hashLiteral _ _ _ k hk hb (.cons (.literal _) .nil)) n

theorem message_progress (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) (n : Nat) :
    NS (evalBuiltin (glob p fixed) frame n .revert
      (.cons (.str [110,111]) (.nil : RArgs E [.bool] [])) (.tuple [])) :=
  builtinFragment_ns _ _ (Source.exprNSAt _ _) (.revertLiteral _ _ (.cons (.literal _) .nil)) n

#print axioms sha_run
#print axioms ripemd_run
#print axioms require_message
#print axioms revert_message
#print axioms hash_progress
#print axioms message_progress
end Solidity.Source.Progress.LiteralBuiltinControls
