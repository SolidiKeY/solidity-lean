import Solidity.Yul.Compilation.ArgumentLowering
import Solidity.Evm.Machine

/-! Target-only transport into the existing compiler machine. Numeric stack
prefixes are mapped exactly, arbitrary caller words (including symbolic slots)
are framed. No source state, frame convention or byte-memory model is added. PUSH
width is erased by this model adapter; no emitted-byte/PC equality is claimed. -/
namespace Solidity.Yul.Compilation.MachineAdapter
open Backend Scalar

def coreWord (w : Scalar.Word) : Evm.Word :=
  .val ⟨w.toNat, by change w.toNat < 2 ^ 256; exact w.isLt⟩

def selectStack : Backend.Instr → Option Evm.Instr
  | .push _ bytes => some (.push (coreWord (immediate bytes.toList)))
  | .op (.DUP n) => some (.dup (n.val + 1))
  | .op (.SWAP n) => some (.swap (n.val + 1))
  | .op .POP => some .pop
  | _ => none

theorem coreWord_injective : Function.Injective coreWord := by
  intro a b equal
  have finEqual := Evm.Word.val.inj equal
  exact BitVec.eq_of_toNat_eq (congrArg Fin.val finEqual)

private theorem mapped_lookup (xs : Stack) (i : Nat) (value : Scalar.Word)
    (found : xs[i]? = some value) (tail : List Evm.Word) :
    (xs.map coreWord ++ tail)[i]? = some (coreWord value) := by
  obtain ⟨bound, _⟩ := List.getElem?_eq_some_iff.mp found
  rw [List.getElem?_append_left (by simpa only [List.length_map] using bound),
    List.getElem?_map, found]
  rfl

/-- Operand success is a real Scalar step premise in this generic transport.
Concrete scoped compiler laws must discharge it; no source adequacy is implied. -/
theorem stack_step (i : Backend.Instr) (j : Evm.Instr)
    (selected : selectStack i = some j) (xs ys : Stack)
    (executed : Scalar.step i xs = some ys)
    (m : Evm.Machine) (tail : List Evm.Word) :
    j.step { m with stack := xs.map coreWord ++ tail } =
      .ok { m with stack := ys.map coreWord ++ tail } 0 := by
  cases i with
  | push width bytes =>
    cases selected
    cases executed
    rfl
  | op opcode =>
    cases opcode <;> simp only [selectStack, Option.some.injEq, reduceCtorEq] at selected
    case POP =>
      subst j
      cases xs with
      | nil => cases executed
      | cons a xs => cases executed; rfl
    case DUP index =>
      subst j
      cases found : xs[index.val]? with
      | none => simp only [Scalar.step, duplicate, found, Option.map_none, reduceCtorEq] at executed
      | some a =>
        simp only [Scalar.step, duplicate, found, Option.map_some, Option.some.injEq] at executed
        subst ys
        simp only [Evm.Instr.step, Nat.add_sub_cancel, mapped_lookup xs index.val a found tail]
        rfl
    case SWAP index =>
      subst j
      cases xs with
      | nil => cases executed
      | cons a xs =>
        cases exchanged : exchange a index.val xs with
        | none => simp only [Scalar.step, swap, exchanged, Option.map_none, reduceCtorEq] at executed
        | some pair =>
          have bound : index.val < xs.length := by
            by_cases outside : xs.length ≤ index.val
            · rw [exchange_out_of_range a xs index.val outside] at exchanged
              cases exchanged
            · omega
          rw [exchange_set a xs index.val bound] at exchanged
          cases exchanged
          simp only [Scalar.step, swap, exchange_set a xs index.val bound,
            Option.map_some, Option.some.injEq] at executed
          subst ys
          have found : xs[index.val]? = some xs[index.val] := List.getElem?_eq_getElem bound
          simp only [Evm.Instr.step, List.map_cons, List.cons_append,
            mapped_lookup xs index.val xs[index.val] found tail]
          rw [List.set_append_left _ _ (by simpa only [List.length_map] using bound), ← List.map_set]
          rfl

/-- Translate only the actual stack-only instructions selected above. -/
def stackCode : Backend.Program → Option (List Evm.Instr)
  | [] => some []
  | i :: p => (selectStack i).bind (fun j => (stackCode p).map (fun q => j :: q))

theorem stack_run (p : Backend.Program) (q : List Evm.Instr)
    (selected : stackCode p = some q) (xs ys : Stack)
    (executed : Scalar.run p xs = some ys) (m : Evm.Machine) (tail : List Evm.Word) :
    Evm.run q { m with stack := xs.map coreWord ++ tail } =
      .ok { m with stack := ys.map coreWord ++ tail } 0 := by
  induction p generalizing q xs ys with
  | nil => cases selected; cases executed; rfl
  | cons i p ih =>
    cases hi : selectStack i with
    | none => simp only [stackCode, hi, Option.bind_none, reduceCtorEq] at selected
    | some j =>
      cases hp : stackCode p with
      | none => simp only [stackCode, hi, hp, Option.bind_some, Option.map_none, reduceCtorEq] at selected
      | some target =>
        simp only [stackCode, hi, hp, Option.bind_some, Option.map_some, Option.some.injEq] at selected
        subst q
        cases hs : Scalar.step i xs with
        | none => simp only [Scalar.run, hs, Option.bind_none, reduceCtorEq] at executed
        | some zs =>
          simp only [Scalar.run, hs, Option.bind_some] at executed
          rw [Evm.run, Evm.exec_cons_zero, stack_step i j hi xs zs hs m tail, Evm.Out.ok_bind]
          exact ih target hp zs ys executed

/-- Actual selected compiler code supplies operand success. The generic Scalar
premise is discharged here by the real compiler certificate, not assumed. -/
theorem loweredExpr_machine {n : Nat} {value : Vector Word n → Word}
    (compiled : LoweredExpr n value) (depth : Nat) (p : Backend.Program) (q : List Evm.Instr)
    (emitted : compiled.code depth = some p) (translated : stackCode p = some q)
    (locals : Vector Word n) (newer : Vector Word depth) (m : Evm.Machine)
    (tail : List Evm.Word) :
    Evm.run q { m with stack := (newer.toList ++ locals.toList).map coreWord ++ tail } =
      .ok { m with stack := coreWord (value locals) ::
        ((newer.toList ++ locals.toList).map coreWord ++ tail) } 0 := by
  have scalar : Scalar.run p (newer.toList ++ locals.toList) =
      some (value locals :: (newer.toList ++ locals.toList)) := by
    simpa only [List.append_nil] using compiled.correct depth p emitted locals newer []
  simpa only [List.map_cons, List.cons_append] using
    stack_run p q translated _ _ scalar m tail

theorem loweredStmt_machine {n : Nat} {update : Vector Word n → Vector Word n}
    (compiled : LoweredStmt n update) (depth : Nat) (p : Backend.Program) (q : List Evm.Instr)
    (emitted : compiled.code depth = some p) (translated : stackCode p = some q)
    (locals : Vector Word n) (newer : Vector Word depth) (m : Evm.Machine)
    (tail : List Evm.Word) :
    Evm.run q { m with stack := (newer.toList ++ locals.toList).map coreWord ++ tail } =
      .ok { m with stack := (newer.toList ++ (update locals).toList).map coreWord ++ tail } 0 := by
  have scalar : Scalar.run p (newer.toList ++ locals.toList) =
      some (newer.toList ++ (update locals).toList) := by
    simpa only [List.append_nil] using compiled.correct depth p emitted locals newer []
  exact stack_run p q translated _ _ scalar m tail

theorem selectStack_pushWord (value : Word) :
    selectStack (pushWord value) = some (.push (coreWord value)) := by
  have pushed := step_pushWord value []
  change some (immediate (toBytesBE 32 value.toNat).toList :: []) = some (value :: []) at pushed
  have word : immediate (toBytesBE 32 value.toNat).toList = value :=
    (List.cons.inj (Option.some.inj pushed)).1
  change some (Evm.Instr.push (coreWord (immediate (toBytesBE 32 value.toNat).toList))) = _
  rw [word]

theorem stackCode_pushWord (value : Word) :
    stackCode [pushWord value] = some [.push (coreWord value)] := by
  rw [stackCode, selectStack_pushWord]
  rfl

theorem local_machine {n depth : Nat} (i : Fin n) (accessible : depth + i.val < 16)
    (locals : Vector Word n) (newer : Vector Word depth) (m : Evm.Machine)
    (tail : List Evm.Word) :
    Evm.run [.dup (depth + i.val + 1)]
      { m with stack := (newer.toList ++ locals.toList).map coreWord ++ tail } =
      .ok { m with stack := coreWord locals[i.val] ::
        ((newer.toList ++ locals.toList).map coreWord ++ tail) } 0 := by
  exact loweredExpr_machine (lowerLocal i) depth [readSlot ⟨depth + i.val, accessible⟩]
    [.dup (depth + i.val + 1)] (by simp only [lowerLocal, dif_pos accessible]) rfl
    locals newer m tail

theorem write_local_machine {n depth : Nat} (i : Fin n) (accessible : depth + i.val < 16)
    (locals : Vector Word n) (newer : Vector Word depth) (value : Word)
    (m : Evm.Machine) (tail : List Evm.Word) :
    Evm.run [.swap (depth + i.val + 1), .pop]
      { m with stack := coreWord value :: ((newer.toList ++ locals.toList).map coreWord ++ tail) } =
      .ok { m with stack := (newer.toList ++ (locals.set i.val value i.isLt).toList).map coreWord ++ tail } 0 := by
  have scalar : Scalar.run (writeSlot ⟨depth + i.val, accessible⟩)
      (value :: (newer.toList ++ locals.toList)) =
      some (newer.toList ++ (locals.set i.val value i.isLt).toList) := by
    simpa only [List.append_nil] using write_under_prefix locals newer i accessible value []
  simpa only [List.map_cons, List.cons_append] using
    stack_run (writeSlot ⟨depth + i.val, accessible⟩) [.swap (depth + i.val + 1), .pop]
      rfl _ _ scalar m tail

theorem assign_literal_machine {n depth : Nat} (i : Fin n)
    (accessible : depth + i.val < 16) (value : Word)
    (locals : Vector Word n) (newer : Vector Word depth) (m : Evm.Machine)
    (tail : List Evm.Word) :
    Evm.run [.push (coreWord value), .swap (depth + i.val + 1), .pop]
      { m with stack := (newer.toList ++ locals.toList).map coreWord ++ tail } =
      .ok { m with stack := (newer.toList ++ (locals.set i.val value i.isLt).toList).map coreWord ++ tail } 0 := by
  apply loweredStmt_machine (lowerAssign i (lowerLiteral value)) depth
    ([pushWord value] ++ writeSlot ⟨depth + i.val, accessible⟩) _ _ _ locals newer m tail
  · simp only [lowerAssign, dif_pos accessible, lowerLiteral, Option.map_some]
  · simp only [writeSlot, List.cons_append, List.nil_append]
    rw [stackCode, selectStack_pushWord]
    rfl

theorem arity_machine {args results : Nat} {output : Vector Word args → Vector Word results}
    (compiled : AritySlice args results output) (q : List Evm.Instr)
    (translated : stackCode compiled.code = some q) (input : Vector Word args)
    (m : Evm.Machine) (tail : List Evm.Word) :
    Evm.run q { m with stack := input.toList.map coreWord ++ tail } =
      .ok { m with stack := (output input).toList.map coreWord ++ tail } 0 := by
  have scalar : Scalar.run compiled.code input.toList = some (output input).toList := by
    simpa only [List.append_nil] using compiled.correct input []
  exact stack_run compiled.code q translated _ _ scalar m tail

#print axioms coreWord_injective
#print axioms stack_step
#print axioms stack_run
#print axioms loweredExpr_machine
#print axioms loweredStmt_machine
#print axioms selectStack_pushWord
#print axioms local_machine
#print axioms write_local_machine
#print axioms assign_literal_machine
#print axioms arity_machine
end Solidity.Yul.Compilation.MachineAdapter
