import tests.«internal-flow».ArgumentFailureFacts
import Solidity.Backend.InternalFlow.SharedCallPrefix
namespace Solidity.Backend.InternalFlow.SharedCallPrefix.Checks
open Evm Evm.Memory
open ArgumentFailureTarget.Checks
abbrev F := PublishedDirectCalls.Checks.prefixProducer.frag
abbrev Γ₁ : Ctx := .mem A :: Caller
abbrev Γ₂ : Ctx := .val .uint :: Γ₁
abbrev Γ₃ : Ctx := Params ++ Caller

def first : Stmt C Caller Γ₁ :=
 .declMem A (.user "old") (some (.alias ((.var .here rfl : MPath C Caller (.ref A)).unders []))) rfl rfl
def second : Stmt C Γ₁ Γ₂ :=
 .declLocal .uint (.user "marker") (some ((.simple (.local (.there (.there .here))) : Val C Caller .uint).unders [.mem A]))
def last (n : Int) (fits : PrimTy.uint.inRange n = true) : Stmt C Γ₂ Γ₃ :=
 .declLocal .uint (.user "last") (some ((readAt n fits).unders [.val .uint,.mem A]))
def continuation : Prog C Γ₃ (.mem A :: Γ₃) :=
 .cons (.declMem A (.user "result") none rfl rfl)
  (.cons (.block (body.wk (Thin.atop Input Caller)).2.2) .nil)

theorem argument_shape : argumentProgram = .cons first (.cons second (.cons (last 2 rfl) .nil)) := rfl
theorem bad_shape : expanded badArgs = .cons first (.cons second (.cons (last 2 rfl) continuation)) := rfl
theorem good_shape : expanded goodArgs = .cons first (.cons second (.cons (last 1 rfl) continuation)) := rfl

def h₁ : CompiledStmt 1 F first := (Memory.compileStmt 1 F first).get (by decide +kernel)
def h₂ : CompiledStmt 1 h₁.frag second := (Memory.compileStmt 1 h₁.frag second).get (by decide +kernel)
def h₃ (n : Int) (fits : PrimTy.uint.inRange n = true)
    (ok : (Memory.compileStmt 1 h₂.frag (last n fits)).isSome = true) :
    CompiledStmt 1 h₂.frag (last n fits) := (Memory.compileStmt 1 h₂.frag (last n fits)).get ok
def badHead := h₃ 2 rfl (by decide +kernel)
def goodHead := h₃ 1 rfl (by decide +kernel)
def badTail : CompiledProg 1 badHead.frag continuation :=
 (Memory.compileProg 1 badHead.frag continuation).get (by decide +kernel)
def goodTail : CompiledProg 1 goodHead.frag continuation :=
 (Memory.compileProg 1 goodHead.frag continuation).get (by decide +kernel)
def emptyTail : CompiledProg 1 badHead.frag (.nil : Prog C Γ₃ Γ₃) := ⟨badHead.frag,[],.nil _⟩
def sharedArguments := attach h₁ (attach h₂ (attach badHead emptyTail))
def sharedBad := attach h₁ (attach h₂ (attach badHead badTail))
def sharedGood := attach h₁ (attach h₂ (attach goodHead goodTail))

private theorem selected {α : Type} (o : Option α) (h : o.isSome = true) : o = some (o.get h) := by
 cases o with | none => cases h | some x => rfl

theorem first_selected : Memory.compileStmt 1 F first = some h₁ := selected _ _
theorem second_selected : Memory.compileStmt 1 h₁.frag second = some h₂ := selected _ _
theorem bad_selected : Memory.compileStmt 1 h₂.frag (last 2 rfl) = some badHead := selected _ (by decide +kernel)
theorem good_selected : Memory.compileStmt 1 h₂.frag (last 1 rfl) = some goodHead := selected _ (by decide +kernel)
theorem bad_tail_selected : Memory.compileProg 1 badHead.frag continuation = some badTail := selected _ _
theorem good_tail_selected : Memory.compileProg 1 goodHead.frag continuation = some goodTail := selected _ _
theorem empty_selected : Memory.compileProg 1 badHead.frag (.nil : Prog C Γ₃ Γ₃) = some emptyTail := rfl

theorem arguments_selected : Memory.compileProg 1 F argumentProgram = some sharedArguments := by
 change Memory.compileProg 1 F (.cons first (.cons second (.cons (last 2 rfl) .nil))) = some sharedArguments
 exact compile_attach h₁ _ first_selected
  (compile_attach h₂ _ second_selected (compile_attach badHead _ bad_selected empty_selected))
theorem bad_expansion_selected : Memory.compileProg 1 F (expanded badArgs) = some sharedBad := by
 change Memory.compileProg 1 F (.cons first (.cons second (.cons (last 2 rfl) continuation))) = some sharedBad
 exact compile_attach h₁ _ first_selected
  (compile_attach h₂ _ second_selected (compile_attach badHead _ bad_selected bad_tail_selected))
theorem good_expansion_selected : Memory.compileProg 1 F (expanded goodArgs) = some sharedGood := by
 change Memory.compileProg 1 F (.cons first (.cons second (.cons (last 1 rfl) continuation))) = some sharedGood
 exact compile_attach h₁ _ first_selected
  (compile_attach h₂ _ second_selected (compile_attach goodHead _ good_selected good_tail_selected))

theorem shared_decomposition : sharedBad.code = sharedArguments.code ++ badTail.code :=
 attach_prefix h₁ _ _ _ (attach_prefix h₂ _ _ _
  (attach_prefix badHead _ _ _ (by change badTail.code = [] ++ badTail.code;rfl)))


theorem public_arguments : Calls.compile 1 F argumentProgram = some (Calls.plain sharedArguments) := by
 change (Memory.compileProg 1 F argumentProgram).map Calls.plain = some (Calls.plain sharedArguments)
 rw [arguments_selected]
 rfl
theorem public_bad_expansion : Calls.compile 1 F (expanded badArgs) = some (Calls.plain sharedBad) := by
 change (Memory.compileProg 1 F (expanded badArgs)).map Calls.plain = some (Calls.plain sharedBad)
 rw [bad_expansion_selected]
 rfl
theorem public_good_expansion : Calls.compile 1 F (expanded goodArgs) = some (Calls.plain sharedGood) := by
 change (Memory.compileProg 1 F (expanded goodArgs)).map Calls.plain = some (Calls.plain sharedGood)
 rw [good_expansion_selected]
 rfl

theorem original_arguments : argumentProducer = Calls.plain sharedArguments := by
 unfold ArgumentFailureTarget.Checks.argumentProducer
 exact get_some _ (by decide +kernel) _ public_arguments
theorem original_bad_expansion : badExpanded = Calls.plain sharedBad := by
 unfold ArgumentFailureTarget.Checks.badExpanded
 exact get_some _ (by decide +kernel) _ public_bad_expansion
theorem original_good_expansion : goodExpanded = Calls.plain sharedGood := by
 unfold ArgumentFailureTarget.Checks.goodExpanded
 exact get_some _ (by decide +kernel) _ public_good_expansion

def sharedBadCall : Calls.Statement 1 F (.call "arguments" badArgs ret body) :=
 Calls.memoryReturn "arguments" badArgs A (.user "result") rfl rfl body (Calls.plain sharedBad)
def sharedGoodCall : Calls.Statement 1 F (.call "arguments" goodArgs ret body) :=
 Calls.memoryReturn "arguments" goodArgs A (.user "result") rfl rfl body (Calls.plain sharedGood)
def badRoot := Calls.cons sharedBadCall (Calls.nil 1 sharedBadCall.frag)
def goodRoot := Calls.cons sharedGoodCall (Calls.nil 1 sharedGoodCall.frag)

theorem original_bad : badProducer = sharedBadCall := by
 unfold ArgumentFailureTarget.Checks.badProducer sharedBadCall
 rw [original_bad_expansion]
theorem original_good : goodProducer = sharedGoodCall := by
 unfold ArgumentFailureTarget.Checks.goodProducer sharedGoodCall
 rw [original_good_expansion]

theorem public_bad_root : Calls.compile 1 F (.cons (.call "arguments" badArgs ret body) .nil) = some badRoot := by
 change (do
  let head ← (do
   let out ← (Memory.compileProg 1 F (expanded badArgs)).map Calls.plain
   pure (Calls.memoryReturn "arguments" badArgs A (.user "result") rfl rfl body out))
  let tail ← some (Calls.nil 1 head.frag)
  pure (Calls.cons head tail)) = some badRoot
 simp only [bad_expansion_selected,Option.map_some,Option.bind_eq_bind,Option.bind_some,Option.pure_def]
 rfl

theorem public_good_root : Calls.compile 1 F (.cons (.call "arguments" goodArgs ret body) .nil) = some goodRoot := by
 change (do
  let head ← (do
   let out ← (Memory.compileProg 1 F (expanded goodArgs)).map Calls.plain
   pure (Calls.memoryReturn "arguments" goodArgs A (.user "result") rfl rfl body out))
  let tail ← some (Calls.nil 1 head.frag)
  pure (Calls.cons head tail)) = some goodRoot
 simp only [good_expansion_selected,Option.map_some,Option.bind_eq_bind,Option.bind_some,Option.pure_def]
 rfl

def badSuffix : List Evm.Instr := badTail.code ++ Calls.returnPointerCode 1 Caller Params

theorem actual_bad_prefix : badProducer.code = argumentProducer.code ++ badSuffix := by
 rw [original_bad,original_arguments]
 change sharedBad.code ++ Calls.returnPointerCode 1 Caller Params =
  sharedArguments.code ++ (badTail.code ++ Calls.returnPointerCode 1 Caller Params)
 rw [shared_decomposition,List.append_assoc]

def goodArgumentProgram : Prog C Caller Γ₃ := goodArgs.declsThen .nil
def goodEmptyTail : CompiledProg 1 goodHead.frag (.nil : Prog C Γ₃ Γ₃) := ⟨goodHead.frag,[],.nil _⟩
def sharedGoodArguments := attach h₁ (attach h₂ (attach goodHead goodEmptyTail))
def goodArgumentProducer := Calls.plain sharedGoodArguments

theorem good_arguments_selected : Memory.compileProg 1 F goodArgumentProgram = some sharedGoodArguments := by
 change Memory.compileProg 1 F (.cons first (.cons second (.cons (last 1 rfl) .nil))) = some sharedGoodArguments
 exact compile_attach h₁ _ first_selected
  (compile_attach h₂ _ second_selected (compile_attach goodHead _ good_selected rfl))
theorem public_good_arguments : Calls.compile 1 F goodArgumentProgram = some goodArgumentProducer := by
 change (Memory.compileProg 1 F goodArgumentProgram).map Calls.plain = some goodArgumentProducer
 rw [good_arguments_selected]
 rfl
theorem good_shared_decomposition : sharedGood.code = sharedGoodArguments.code ++ goodTail.code :=
 attach_prefix h₁ _ _ _ (attach_prefix h₂ _ _ _
  (attach_prefix goodHead _ _ _ (by change goodTail.code = [] ++ goodTail.code;rfl)))
def goodSuffix : List Evm.Instr := goodTail.code ++ Calls.returnPointerCode 1 Caller Params

theorem actual_good_prefix : goodProducer.code = goodArgumentProducer.code ++ goodSuffix := by
 rw [original_good]
 change sharedGood.code ++ Calls.returnPointerCode 1 Caller Params =
  sharedGoodArguments.code ++ (goodTail.code ++ Calls.returnPointerCode 1 Caller Params)
 rw [good_shared_decomposition,List.append_assoc]

def publicBad : Calls.Program 1 F (.cons (.call "arguments" badArgs ret body) .nil) :=
 (Calls.compile 1 F (.cons (.call "arguments" badArgs ret body) .nil)).get (by decide +kernel)
def publicGood : Calls.Program 1 F (.cons (.call "arguments" goodArgs ret body) .nil) :=
 (Calls.compile 1 F (.cons (.call "arguments" goodArgs ret body) .nil)).get (by decide +kernel)
attribute [irreducible] publicBad publicGood

theorem selected_bad_root : publicBad = badRoot := by
 unfold publicBad
 exact get_some _ (by decide +kernel) _ public_bad_root
theorem selected_good_root : publicGood = goodRoot := by
 unfold publicGood
 exact get_some _ (by decide +kernel) _ public_good_root

theorem public_bad_code : publicBad.code = badProducer.code := by
 rw [selected_bad_root]
 change sharedBadCall.code ++ [] = badProducer.code
 rw [List.append_nil,original_bad]
theorem public_good_code : publicGood.code = goodProducer.code := by
 rw [selected_good_root]
 change sharedGoodCall.code ++ [] = goodProducer.code
 rw [List.append_nil,original_good]
theorem public_good_frag : publicGood.frag = goodProducer.frag := by
 rw [selected_good_root]
 change sharedGoodCall.frag = goodProducer.frag
 rw [original_good]

theorem emitted_bad_prefix : publicBad.code = argumentProducer.code ++ badSuffix :=
 public_bad_code.trans actual_bad_prefix
theorem emitted_good_prefix : publicGood.code = goodArgumentProducer.code ++ goodSuffix :=
 public_good_code.trans actual_good_prefix


/-- The literal C46 drop-form goal, now derived from shared constructors by
list algebra instead of normalizing two independent full compilations. -/
theorem c46_drop_decomposition : badProducer.code = argumentProducer.code ++
 badProducer.code.drop argumentProducer.code.length := by
 rw [actual_bad_prefix,List.drop_left]


/-- Nil has no reached allocation cost; the selector's actual metadata is the
original call cost for EVERY input, without evaluating an unreachable suffix. -/
theorem public_bad_cost (σ : State C Caller) : publicBad.cost σ = badProducer.cost σ := by
 rw [selected_bad_root]
 change sharedBadCall.cost σ + 0 = badProducer.cost σ
 rw [Nat.add_zero,original_bad]
theorem public_good_cost (σ : State C Caller) : publicGood.cost σ = goodProducer.cost σ := by
 rw [selected_good_root]
 change sharedGoodCall.cost σ + 0 = goodProducer.cost σ
 rw [Nat.add_zero,original_good]

#print axioms Solidity.Backend.InternalFlow.SharedCallPrefix.Checks.argument_shape
#print axioms Solidity.Backend.InternalFlow.SharedCallPrefix.Checks.bad_shape
#print axioms Solidity.Backend.InternalFlow.SharedCallPrefix.Checks.good_shape
#print axioms Solidity.Backend.InternalFlow.SharedCallPrefix.Checks.first_selected
#print axioms Solidity.Backend.InternalFlow.SharedCallPrefix.Checks.second_selected
#print axioms Solidity.Backend.InternalFlow.SharedCallPrefix.Checks.bad_selected
#print axioms Solidity.Backend.InternalFlow.SharedCallPrefix.Checks.good_selected
#print axioms Solidity.Backend.InternalFlow.SharedCallPrefix.Checks.bad_tail_selected
#print axioms Solidity.Backend.InternalFlow.SharedCallPrefix.Checks.good_tail_selected
#print axioms Solidity.Backend.InternalFlow.SharedCallPrefix.Checks.empty_selected
#print axioms Solidity.Backend.InternalFlow.SharedCallPrefix.Checks.arguments_selected
#print axioms Solidity.Backend.InternalFlow.SharedCallPrefix.Checks.bad_expansion_selected
#print axioms Solidity.Backend.InternalFlow.SharedCallPrefix.Checks.good_expansion_selected
#print axioms Solidity.Backend.InternalFlow.SharedCallPrefix.Checks.shared_decomposition
#print axioms Solidity.Backend.InternalFlow.SharedCallPrefix.Checks.public_arguments
#print axioms Solidity.Backend.InternalFlow.SharedCallPrefix.Checks.public_bad_expansion
#print axioms Solidity.Backend.InternalFlow.SharedCallPrefix.Checks.public_good_expansion
#print axioms Solidity.Backend.InternalFlow.SharedCallPrefix.Checks.original_arguments
#print axioms Solidity.Backend.InternalFlow.SharedCallPrefix.Checks.original_bad_expansion
#print axioms Solidity.Backend.InternalFlow.SharedCallPrefix.Checks.original_good_expansion
#print axioms Solidity.Backend.InternalFlow.SharedCallPrefix.Checks.original_bad
#print axioms Solidity.Backend.InternalFlow.SharedCallPrefix.Checks.original_good
#print axioms Solidity.Backend.InternalFlow.SharedCallPrefix.Checks.public_bad_root
#print axioms Solidity.Backend.InternalFlow.SharedCallPrefix.Checks.public_good_root
#print axioms Solidity.Backend.InternalFlow.SharedCallPrefix.Checks.actual_bad_prefix
#print axioms Solidity.Backend.InternalFlow.SharedCallPrefix.Checks.good_arguments_selected
#print axioms Solidity.Backend.InternalFlow.SharedCallPrefix.Checks.public_good_arguments
#print axioms Solidity.Backend.InternalFlow.SharedCallPrefix.Checks.good_shared_decomposition
#print axioms Solidity.Backend.InternalFlow.SharedCallPrefix.Checks.actual_good_prefix
#print axioms Solidity.Backend.InternalFlow.SharedCallPrefix.Checks.selected_bad_root
#print axioms Solidity.Backend.InternalFlow.SharedCallPrefix.Checks.selected_good_root
#print axioms Solidity.Backend.InternalFlow.SharedCallPrefix.Checks.public_bad_code
#print axioms Solidity.Backend.InternalFlow.SharedCallPrefix.Checks.public_good_code
#print axioms Solidity.Backend.InternalFlow.SharedCallPrefix.Checks.public_good_frag
#print axioms Solidity.Backend.InternalFlow.SharedCallPrefix.Checks.emitted_bad_prefix
#print axioms Solidity.Backend.InternalFlow.SharedCallPrefix.Checks.emitted_good_prefix
#print axioms Solidity.Backend.InternalFlow.SharedCallPrefix.Checks.c46_drop_decomposition
#print axioms Solidity.Backend.InternalFlow.SharedCallPrefix.Checks.public_bad_cost
#print axioms Solidity.Backend.InternalFlow.SharedCallPrefix.Checks.public_good_cost
#print axioms Solidity.Backend.InternalFlow.SharedCallPrefix.compile_attach
#print axioms Solidity.Backend.InternalFlow.SharedCallPrefix.attach_prefix
#print axioms Solidity.Backend.InternalFlow.SharedCallPrefix.get_some
end Solidity.Backend.InternalFlow.SharedCallPrefix.Checks
