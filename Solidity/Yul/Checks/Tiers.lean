import Solidity.Yul.TierPolicy
import Solidity.Yul.Checks.Static
set_option Elab.async false
namespace Solidity.Yul.Checks.Tiers
open Solidity.Yul.Policy

def pureRoot : Stmt [] [] ⟨false, false⟩ 1 := Static.mulDiv
example : checkGeneral .A true pureRoot = .ok () := rfl
example : checkGeneral .B true pureRoot = .ok () := rfl
example : checkGeneral .C true pureRoot = .ok () := rfl
example : checkGeneral .C false pureRoot = .error .nonMemorySafe := rfl

def hiddenGas : Stmt [] [] ⟨false, false⟩ 1 :=
  .if_ (.literal (word 0)) (.assign (fun _ => .«local» 0) (.builtin .gas Fin.elim0))
example : checkGeneral .C true hiddenGas = .error (.compilerDependent "gas") := rfl
example : checkGeneral .C false hiddenGas = .error .nonMemorySafe := rfl

def gasFunction : Stmt [] [] ⟨false, false⟩ 1 :=
  .functions [⟨0, 1⟩] (.cons
    (.assign (fun _ => .«local» 0) (.builtin .gas Fin.elim0)) .nil) .skip
example : checkGeneral .C true gasFunction = .error (.compilerDependent "gas") := rfl

def memoryExpr : Expr [] [] 0 1 :=
  .builtin (.pure .«add») (fun _ => .builtin .mload (fun _ => .literal (word 0)))
example : checkExpr .A memoryExpr = .error (.needsTier .B) := rfl
example : checkExpr .B memoryExpr = .ok () := rfl
example : checkExpr .C memoryExpr = .ok () := rfl

def globalSlot : Expr [] [.storage false false] 0 1 := .external ⟨.here, .slot, .slotRead⟩
example : checkExpr .A globalSlot = .error (.needsTier .B) := rfl
example : checkExpr .B globalSlot = .ok () := rfl

def internalPointer : Expr [] [.internalFunction] 0 1 := .external ⟨.here, .plain, .internalRead⟩
example : checkExpr .C internalPointer = .error (.compilerDependent "internal function address") := rfl
example : checkTarget .A (Target.external (n := 0) (X := [.memory]) ⟨.here, .plain, .memoryWrite⟩) =
    .error (.needsTier .B) := rfl
example : checkTarget .B (Target.external (n := 0) (X := [.memory]) ⟨.here, .plain, .memoryWrite⟩) = .ok () := rfl
example : checkTarget .A (Target.external (n := 0) (X := [.value (.unsigned 0)]) ⟨.here, .plain, .valueWrite⟩) = .ok () := rfl

def forbidden {a r} (b : Builtin a r) : Expr [] [] 0 r :=
  .builtin b (fun _ => .literal (word 0))
example : checkExpr .C (forbidden .msize) = .error (.compilerDependent "msize") := rfl
example : checkExpr .C (forbidden .pc) = .error (.compilerDependent "pc") := rfl
example : checkExpr .C (forbidden .codesize) = .error (.compilerDependent "codesize") := rfl
example : checkExpr .C (forbidden .codecopy) = .error (.compilerDependent "codecopy") := rfl
example : checkExpr .C (forbidden .callcode) = .error .unsupportedCallcode := rfl
example : checkExpr .B (forbidden .«call») = .error (.needsTier .C) := rfl
example : checkExpr .C (forbidden .«call») = .ok () := rfl

def hiddenSwitch : Stmt [] [] ⟨false, false⟩ 1 :=
  .switch (.literal (word 0))
    (.cons (word 7) (.zero 1
      (.assign (fun _ => .«local» 0) (.builtin .pc Fin.elim0))) .nil) .skip
example : checkGeneral .C true hiddenSwitch = .error (.compilerDependent "pc") := rfl

def hiddenPost : Stmt [] [] ⟨false, false⟩ 1 :=
  .for_ .skip (.literal (word 0))
    (.assign (fun _ => .«local» 0) (.builtin .codesize Fin.elim0)) .skip
example : checkGeneral .C true hiddenPost = .error (.compilerDependent "codesize") := rfl

/-- An open function context supplies signatures, not policy evidence for bodies. -/
def openCall : Expr [⟨0, 1⟩] [] 0 1 := .call .here Fin.elim0
example : checkExpr .A openCall = .ok () := rfl
example : checkGeneral .A true Static.loop = .ok () := rfl

end Solidity.Yul.Checks.Tiers
