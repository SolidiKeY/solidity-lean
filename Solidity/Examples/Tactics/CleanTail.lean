import Solidity.Calculus.CleanTailBoundary
import Solidity.Typing.Constructibility
import Solidity.Syntax.Splice

namespace Solidity.Examples.Tactics.CleanTail

open Solidity

def tokens : SRef Tokens (.ref (.array (.ref (.struct "Token")))) :=
  SRef.ofRoot "tokens" rfl

def tokenSeven : SVal (.ref (.struct "Token")) :=
  .struct (.cons (.prim (PrimTy.ofLit .uint 7 rfl)) .nil)

def repaired : Storage Tokens :=
  .cons (.array (.cons tokenSeven .nil) .nil (by decide)) .nil

theorem initial_clean : (Storage.init Tokens).CleanTail := Storage.init_cleanTail Tokens

theorem dangling_not_clean : ¬ Tokens.dangling.CleanTail := by
  simp only [Tokens.dangling, Storage.CleanTail, SFields.All, SVal.All, SList.All,
    SVec.All, cleanTailH, SList.OrdinaryDefault,
    SList.fold, ordinaryDefaultFold, and_true, and_self]
  decide +kernel

theorem dangling_reachable_but_not_clean :
    Reachable Tokens Tokens.dangling ∧ ¬ Tokens.dangling.CleanTail :=
  ⟨dangling_slot_reachable, dangling_not_clean⟩

theorem reused_slot_retains_value :
    Storage.pushPlace Tokens.dangling tokens = some (repaired, PrimTy.dflt .uint) := by
  decide +kernel

theorem repaired_clean : repaired.CleanTail := by
  simp only [repaired, Storage.CleanTail, SFields.All, SVal.All, SList.All, SVec.All,
    cleanTailH, SList.OrdinaryDefault, SList.fold, ordinaryDefaultFold,
    tokenSeven, and_self]

def leaveDirty := (sol[Tokens]{
  Token storage r = tokens.push();
  tokens.pop();
  r.value = 7;
} : Prog Tokens [] _)

def repairDirty := (sol[Tokens]{
  delete tokens;
  tokens.push();
  Token storage r = tokens[0];
  tokens.pop();
  r.value = 7;
  delete tokens;
  tokens.push();
  assert(tokens[0].value == 7);
} : Prog Tokens [] _)

def survivePush := (sol[Tokens]{
  delete tokens;
  tokens.push();
  Token storage r = tokens[0];
  tokens.pop();
  r.value = 7;
  tokens.push();
  assert(tokens[0].value == 7);
} : Prog Tokens [] _)

def CopyTokens : Contract := contract!{ Token[] tokens; Token[] emptyTokens; }

def copyRepaired : Storage CopyTokens :=
  .cons (.array (.cons tokenSeven .nil) .nil (by decide))
    (.cons (.array .nil .nil SVal.zero_lt_bound) .nil)

def copyDirty := (sol[CopyTokens]{
  delete emptyTokens;
  delete tokens;
  tokens.push();
  Token storage r = tokens[0];
  tokens.pop();
  r.value = 7;
  tokens = emptyTokens;
  tokens.push();
  assert(tokens[0].value == 7);
} : Prog CopyTokens [] _)

def Matrix : Contract := contract!{ uint[][] matrix; }

def matrixRepaired : Storage Matrix :=
  .cons (.array
    (.cons (.array (.cons (.prim (PrimTy.ofLit .uint 66 rfl)) .nil) .nil (by decide)) .nil)
    .nil (by decide)) .nil

def regrowInner := (sol[Matrix]{
  delete matrix;
  matrix.push();
  uint[] storage ptr = matrix[0];
  matrix.pop();
  ptr.push(66);
  matrix.push();
  assert(matrix[0].length == 1);
  assert(matrix[0][0] == 66);
} : Prog Matrix [] _)

theorem leaveDirty_run :
    (Prog.run (State.init Tokens) leaveDirty).toOption.map (fun o => o.st.storage) =
      some Tokens.dangling := by
  decide +kernel

theorem repairDirty_run :
    (Prog.run (State.init Tokens) repairDirty).toOption.map (fun o => o.st.storage) =
      some repaired := by
  decide +kernel

theorem survivePush_run :
    (Prog.run (State.init Tokens) survivePush).toOption.map (fun o => o.st.storage) =
      some repaired := by
  decide +kernel

theorem copyDirty_run :
    (Prog.run (State.init CopyTokens) copyDirty).toOption.map (fun o => o.st.storage) =
      some copyRepaired := by
  decide +kernel

theorem regrowInner_run :
    (Prog.run (State.init Matrix) regrowInner).toOption.map (fun o => o.st.storage) =
      some matrixRepaired := by
  decide +kernel

theorem copyRepaired_clean : copyRepaired.CleanTail := by
  simp only [copyRepaired, Storage.CleanTail, SFields.All, SVal.All, SList.All, SVec.All,
    cleanTailH, SList.OrdinaryDefault, SList.fold, ordinaryDefaultFold,
    tokenSeven, and_self]

theorem matrixRepaired_clean : matrixRepaired.CleanTail := by
  simp only [matrixRepaired, Storage.CleanTail, SFields.All, SVal.All, SList.All,
    SVec.All, cleanTailH, SList.OrdinaryDefault, SList.fold, ordinaryDefaultFold, and_self]

theorem repairDirty_initial_boundary : repairDirty.CleanTailBoundaryAt (State.init Tokens) :=
  Prog.cleanTailBoundaryAt_of_runStorage repairDirty_run repaired_clean

theorem survivePush_initial_boundary : survivePush.CleanTailBoundaryAt (State.init Tokens) :=
  Prog.cleanTailBoundaryAt_of_runStorage survivePush_run repaired_clean

theorem copyDirty_initial_boundary : copyDirty.CleanTailBoundaryAt (State.init CopyTokens) :=
  Prog.cleanTailBoundaryAt_of_runStorage copyDirty_run copyRepaired_clean

theorem regrowInner_initial_boundary : regrowInner.CleanTailBoundaryAt (State.init Matrix) :=
  Prog.cleanTailBoundaryAt_of_runStorage regrowInner_run matrixRepaired_clean

theorem leaveDirty_boundary_rejected : ¬ leaveDirty.CleanTailBoundary := by
  intro h
  have hboundary := h (State.init Tokens) (State.init_cleanTail Tokens)
  have hrun := leaveDirty_run
  cases hr : Prog.run (State.init Tokens) leaveDirty with
  | error e => rw [hr] at hrun; cases hrun
  | ok o =>
    rw [hr] at hboundary hrun
    have hstorage : o.st.storage = Tokens.dangling := Option.some.inj hrun
    exact dangling_not_clean (hstorage ▸ hboundary.1)

def interruptRepair := (sol[Tokens]{
  Token storage r = tokens.push();
  tokens.pop();
  r.value = 7;
  uint to = 9;
  to.transfer(0);
  tokens.push();
  assert(tokens[0].value == 7);
} : Prog Tokens [] _)

theorem interruptRepair_run :
    (Prog.run (State.init Tokens) interruptRepair).toOption.map (fun o => o.st.storage) =
      some repaired := by
  decide +kernel

theorem interruptRepair_initial_boundary :
    interruptRepair.CleanTailBoundaryAt (State.init Tokens) :=
  Prog.cleanTailBoundaryAt_of_runStorage interruptRepair_run repaired_clean

private theorem execOfRun {C : Contract} {J : StateInv C} {Γ Γ' : Ctx}
    {σ : State C Γ} {s : Stmt C Γ Γ'} {o : Out C σ.H Γ'} (hf : s.forksIn J.pay = false)
    (h : s.run σ = .ok o) : ExecS J σ s (.ok o) := by
  have := ExecS.det (J := J) (σ := σ) hf
  rwa [h] at this

private def afterPush : State Tokens [.alias (.struct "Token")] :=
  { storage := .cons (.array (.cons (SVal.dflt (.ref (.struct "Token"))) .nil)
      .nil (by decide)) .nil,
    H := [], heap := Heap.empty, env := (some (tokens.append (.at (PrimTy.dflt .uint) .nil)), ()) }

private def afterPop : State Tokens [.alias (.struct "Token")] :=
  { afterPush with storage := .cons (.array .nil
      (.cons (SVal.dflt (.ref (.struct "Token"))) .nil) SVal.zero_lt_bound) .nil }

private def afterDirty : State Tokens [.alias (.struct "Token")] :=
  { afterPush with storage := Tokens.dangling }

private def afterTo : State Tokens [.val .uint, .alias (.struct "Token")] :=
  afterDirty.push (t := .val .uint) (PrimTy.ofLit .uint 9 rfl)

section

attribute [local semireducible] Path.append Path.index SVec.toList SList.toList
  SVal.defaultOf SFields.defaultOf SVec.defaultOf

theorem interruptRepair_callback_violates :
    ExecP (StateInv.cleanTail Tokens) (State.init Tokens) interruptRepair .violated := by
  refine .cons (o₁ := ⟨afterPush, List.prefix_refl []⟩) (execOfRun rfl ?_)
    (.cons (o₁ := ⟨afterPop, List.prefix_refl []⟩) (execOfRun rfl ?_)
      (.cons (o₁ := ⟨afterDirty, List.prefix_refl []⟩) (execOfRun rfl ?_)
        (.cons (o₁ := ⟨afterTo, List.prefix_refl []⟩) (execOfRun rfl ?_)
          (.violated (.transferViolated rfl rfl ?_)))))
  case refine_1 => rfl
  case refine_2 => rfl
  case refine_3 => rfl
  case refine_4 => rfl
  case refine_5 =>
    change ¬ Tokens.dangling.CleanTail
    exact dangling_not_clean

end

theorem interruptRepair_callback_boundary_rejected :
    ¬ interruptRepair.CleanTailCallbackBoundary := by
  intro h
  exact h (State.init Tokens) (State.init_cleanTail Tokens) .violated
    interruptRepair_callback_violates

end Solidity.Examples.Tactics.CleanTail
