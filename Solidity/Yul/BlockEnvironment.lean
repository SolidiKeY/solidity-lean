import Solidity.Yul.AssignmentCheck
import Solidity.Yul.FunctionScope

/-! Shared intrinsic block-name environment. Declaration names remain mapped to
local Fin slots and signature-indexed function members. These definitions are
moved unchanged from BlockTyping, retaining their fully qualified names and
representation; no Source state or external namespace is stored here. -/
namespace Solidity.Yul.BlockTyping

structure Env (F : List Sig) (n : Nat) where
  locals : List (String × Fin n)
  functions : FunctionNames F

def Env.reads {F n} (E : Env F n) : ExprEnv F [] n :=
  ⟨E.locals, E.functions, []⟩
def Env.writes {F n} (E : Env F n) : TargetEnv [] n := ⟨E.locals, []⟩
def Env.extend {F n} (E : Env F n) (names : List String) : Env F (names.length + n) :=
  ⟨extendLocals names E.locals, E.functions⟩
def Env.hoist {F n} (E : Env F n) (headers : List (String × Sig)) :
    Env (headers.map Prod.snd ++ F) n := ⟨E.locals, hoistNames headers E.functions⟩

/-- Arguments precede return slots, as in the actual intrinsic call frame.
These are positional slots, not initial runtime values. -/
def frameLocals (args rets : List String) :
    List (String × Fin (args.length + rets.length)) :=
  (localBindings args).map (fun p => (p.1, p.2.castAdd rets.length)) ++
  (localBindings rets).map (fun p => (p.1, Fin.natAdd args.length p.2))

def Env.frame {F n} (E : Env F n) (args rets : List String) :
    Env F (args.length + rets.length) := ⟨frameLocals args rets, E.functions⟩

end Solidity.Yul.BlockTyping
