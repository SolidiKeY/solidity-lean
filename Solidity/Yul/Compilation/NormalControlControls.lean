import Solidity.Yul.Compilation.NormalControl
namespace Solidity.Yul.Compilation.NormalControl.Controls
open Backend Scalar Solidity.Yul.Closed MachineAdapter

def root : Control := ⟨false,false⟩
def write (i : Fin 2) (value : Solidity.Yul.Word) : Stmt [] [] root 2 :=
  .assign (fun _ : Fin 1 => .local i) (.literal value)
def first : Stmt [] [] root 2 := .if_ (.local 0) (.if_ (.local 1) (write 0 (word 0)))
def second : Stmt [] [] root 2 := .if_ (.local 0) (write 1 (word (2^200+257)))
def program : Stmt [] [] root 2 := .seq first second
def dirty : Scalar.Word := BitVec.ofNat 256 (2^200+257)
def highOnly : Scalar.Word := BitVec.ofNat 256 (2^200)
def compiled := (compile 5 program).get (by rfl)

def sourceResult (a b : Scalar.Word) : Option (Nat × Nat × Bool) :=
  (evalStmt 5 .nil True.intro program compiled.profile
    (ProducerExpressions.sourceLocals #v[a,b])).map
      (fun out => ((out.vars 0).val,(out.vars 1).val,out.flow.isNormal))
#guard sourceResult 0 1 == some (0,1,true)
#guard sourceResult 3 0 == some (3,dirty.toNat,true)
#guard sourceResult 3 1 == some (0,1,true)
#guard sourceResult highOnly 0 == some (highOnly.toNat,dirty.toNat,true)
#guard sourceResult dirty 0 == some (dirty.toNat,dirty.toNat,true)
#guard (PureStatements.compile 5 program).isNone
#guard (compile 4 program).isNone
#guard (evalStmt 4 .nil True.intro program compiled.profile
  (ProducerExpressions.sourceLocals #v[3,1])).isNone
-- Conservative compilation can refuse a horizon at which a short path runs.
#guard (evalStmt 4 .nil True.intro program compiled.profile
  (ProducerExpressions.sourceLocals #v[0,1])).isSome
#guard (compiled.emit 14).isSome
#guard (compiled.emit 15).isNone
#guard ((compiled.emit 2).bind (fun block =>
  Backend.assemble 0 (fun x : Empty => nomatch x) (block.expand 0).1)).isSome
#guard (compile 5 (Stmt.switch (.local 0) .nil .skip : Stmt [] [] root 2)).isNone
#guard (compile 0 program).isNone

def machine := (compiled.emit 2).bind WordControl.blockCode
def modelResult (a b : Scalar.Word) (caller : List Evm.Word) : Option (List Evm.Word × Nat) :=
  match machine with
  | none => none
  | some code =>
    match Evm.run code {Evm.Machine.init with stack := [91,92,a,b].map coreWord ++ caller} with
    | .ok out skip => some (out.stack,skip)
    | _ => none
#guard modelResult 0 1 [.slot (.root 77)] = some ([91,92,0,1].map coreWord ++ [.slot (.root 77)],0)
#guard modelResult 3 0 [.slot (.root 77)] = some ([91,92,3,dirty].map coreWord ++ [.slot (.root 77)],0)
#guard modelResult 3 1 [.slot (.root 77)] = some ([91,92,0,1].map coreWord ++ [.slot (.root 77)],0)
#guard modelResult highOnly 0 [.slot (.root 77)] = some ([91,92,highOnly,dirty].map coreWord ++ [.slot (.root 77)],0)
#guard modelResult dirty 0 [.slot (.root 77)] = some ([91,92,dirty,dirty].map coreWord ++ [.slot (.root 77)],0)
-- Existing model success does not prove the real 1024-word capacity obligation.
#guard (modelResult 0 1 (List.replicate 1021 (coreWord 0))).map (fun out => out.1.length) = some 1025
#guard match machine with
  | none => false
  | some code => match Evm.run code Evm.Machine.init with | .fault => true | _ => false
#guard (compile 2 (Stmt.leave : Stmt [] [] ⟨true,false⟩ 2)).isNone
#guard (compile 2 (Stmt.break_ : Stmt [] [] ⟨false,true⟩ 2)).isNone
#guard (compile 2 (Stmt.continue_ : Stmt [] [] ⟨false,true⟩ 2)).isNone
-- Accepted source certificate is not evidence of target-model opcode coverage.
def unsupported := (compile 3 (.if_
  (.builtin (.pure .signextend) (Fin.cases (.local 0) (fun _ => .local 1)))
  (.skip : Stmt [] [] root 2))).get (by rfl)
#guard ((unsupported.emit 2).bind WordControl.blockCode).isNone
#print axioms Derivation.source
end Solidity.Yul.Compilation.NormalControl.Controls
