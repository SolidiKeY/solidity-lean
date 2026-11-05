import Solidity.Calculus.Rules
import Solidity.Calculus.PremiseSound

namespace H28.AliasTwiceKill
open Solidity

def counterName : Name := String.singleton 'c'
def arrayName : Name := String.singleton 'a'
def functionName : Name := String.singleton 'g'
def returnVar : Var := .user (String.singleton 'r')
def R : RefTy := .array (.prim .uint)
def C : Contract := { vars := [(counterName, .prim .uint), (arrayName, .ref R)] }
def calleeCtx : Ctx := [.alias R]
def returnedCtx : Ctx := [.alias R, .alias R]
def bindReturn : Stmt C calleeCtx calleeCtx := .rebind .here (.path (.loc (.root arrayName rfl)))
def increment : Stmt C calleeCtx calleeCtx := .opAssign .add rfl rfl
  (.root counterName rfl) (.simple (.lit 1 rfl))
def getter (b : Bool) : Prog C calleeCtx calleeCtx :=
  if b then .cons increment (.cons bindReturn .nil) else .cons bindReturn .nil

def statement (b : Bool) : Stmt C [] [] :=
  .callReceiver functionName .nil returnVar (getter b) (.push none rfl)
def duplicateProgram (b : Bool) : Prog C [] returnedCtx :=
  .cons (.call functionName .nil (.storage R returnVar) (getter b))
    (.cons (.call functionName .nil (.storage R returnVar) (getter b))
      (.cons (.push (.alias .here) none rfl) .nil))
def duplicateFrames : Frames C returnedCtx [] := .pop .capture (.push (.push .refl)) (.seq .nil .nil)
def premise (b : Bool) : Premise C [] [] := (.unfold (duplicateProgram b) (.push (.push .refl)))

theorem source_link : ∀ b : Bool, Taclet C 0 .diamond (statement b) (premise b) := fun b => .storagePush_unfold_leftCallReceiver (f := functionName) (args := .nil) (r := returnVar) (body := getter b) (hd := rfl)

def start : State C [] := .init C
def afterPure : State C [] := start.withStorage (.cons (.prim ⟨0, rfl⟩)
  (.cons (.array (.cons (.prim ⟨0, rfl⟩) .nil) .nil (by decide +kernel)) .nil))
def afterOne : State C [] := start.withStorage (.cons (.prim ⟨1, rfl⟩)
  (.cons (.array (.cons (.prim ⟨0, rfl⟩) .nil) .nil (by decide +kernel)) .nil))
def afterTwo : State C [] := start.withStorage (.cons (.prim ⟨2, rfl⟩)
  (.cons (.array (.cons (.prim ⟨0, rfl⟩) .nil) .nil (by decide +kernel)) .nil))
def returnedRef : SRef C (.ref R) := .ofRoot arrayName rfl
def callOne (b : Bool) : Stmt C [] calleeCtx := .call functionName .nil (.storage R returnVar) (getter b)
def callTwo (b : Bool) : Stmt C calleeCtx returnedCtx := .call functionName .nil (.storage R returnVar) (getter b)
def appendAfter : Stmt C returnedCtx returnedCtx := .push (.alias .here) none rfl
def oneCounter (b : Bool) : PrimTy.uint.Denote := if b then ⟨1, rfl⟩ else ⟨0, rfl⟩
def twoCounter (b : Bool) : PrimTy.uint.Denote := if b then ⟨2, rfl⟩ else ⟨0, rfl⟩
def oneBase (b : Bool) : State C [] := start.withStorage (.cons (.prim (oneCounter b))
  (.cons (.array .nil .nil (by decide +kernel)) .nil))
def twoBase (b : Bool) : State C [] := start.withStorage (.cons (.prim (twoCounter b))
  (.cons (.array .nil .nil (by decide +kernel)) .nil))
def pushedBase (b : Bool) : State C [] := start.withStorage (.cons (.prim (twoCounter b))
  (.cons (.array (.cons (.prim ⟨0, rfl⟩) .nil) .nil (by decide +kernel)) .nil))
def oneAlias (b : Bool) : State C calleeCtx := (oneBase b).push (t := .alias R) (some returnedRef)
def twoAliases (b : Bool) : State C returnedCtx := ((twoBase b).push (t := .alias R) (some returnedRef)).push (t := .alias R) (some returnedRef)
def pushedAliases (b : Bool) : State C returnedCtx := ((pushedBase b).push (t := .alias R) (some returnedRef)).push (t := .alias R) (some returnedRef)

theorem call_one_false : (callOne false).runR start = .ok ⟨oneAlias false, List.prefix_refl _⟩ := by with_unfolding_all rfl
theorem call_one_true : (callOne true).runR start = .ok ⟨oneAlias true, List.prefix_refl _⟩ := by with_unfolding_all rfl
theorem call_two_false : (callTwo false).runR (oneAlias false) = .ok ⟨twoAliases false, List.prefix_refl _⟩ := by with_unfolding_all rfl
theorem call_two_true : (callTwo true).runR (oneAlias true) = .ok ⟨twoAliases true, List.prefix_refl _⟩ := by with_unfolding_all rfl
theorem append_false : appendAfter.runR (twoAliases false) = .ok ⟨pushedAliases false, List.prefix_refl _⟩ := by with_unfolding_all rfl
theorem append_true : appendAfter.runR (twoAliases true) = .ok ⟨pushedAliases true, List.prefix_refl _⟩ := by with_unfolding_all rfl

theorem first_step (b : Bool) : (callOne b).runR start = .ok ⟨oneAlias b, List.prefix_refl _⟩ := by
  cases b
  · exact call_one_false
  · exact call_one_true

theorem second_step (b : Bool) : (callTwo b).runR (oneAlias b) = .ok ⟨twoAliases b, List.prefix_refl _⟩ := by
  cases b
  · exact call_two_false
  · exact call_two_true

theorem append_step (b : Bool) : appendAfter.runR (twoAliases b) = .ok ⟨pushedAliases b, List.prefix_refl _⟩ := by
  cases b
  · exact append_false
  · exact append_true

theorem program_steps (b : Bool) : Prog.run start (duplicateProgram b) = .ok ⟨pushedAliases b, List.prefix_refl _⟩ := by
  change Prog.run start (.cons (callOne b) (.cons (callTwo b) (.cons appendAfter .nil))) = _
  rw [Prog.run_cons_ok (first_step b), Prog.run_cons_ok (second_step b), Prog.run_cons_ok (append_step b), Prog.run_nil]
  rfl

def counterTerm : Tm C [] (.val .uint) := .app2 .find (.app0 .storage) (.app0 (.root counterName rfl))
def two : Tm C [] (.val .uint) := .app0 (.lit (p := .uint) ⟨2, rfl⟩)
def post : Fml C [] := .eq counterTerm two

theorem input_inhabited : Nonempty (State C []) := ⟨start⟩
theorem getter_once : (statement true).runR start = .ok ⟨afterOne, List.prefix_refl _⟩ := by with_unfolding_all rfl
theorem pure_once : (statement false).runR start = .ok ⟨afterPure, List.prefix_refl _⟩ := by with_unfolding_all rfl
theorem pure_twice_control : Prog.runFrames start (duplicateProgram false) duplicateFrames = .ok afterPure := by
  unfold Prog.runFrames
  rw [program_steps false]
  with_unfolding_all rfl

theorem actual_counter_one : counterTerm.denote afterOne = some (⟨1, rfl⟩ : PrimTy.uint.Denote) :=
  Tm.denote_eval afterOne counterTerm ⟨1, rfl⟩ (by with_unfolding_all rfl)

theorem actual_rejects_post : ¬ holds afterOne post := by
  intro h
  change counterTerm.denote afterOne = two.denote afterOne at h
  rw [actual_counter_one] at h
  change (some (⟨1, rfl⟩ : PrimTy.uint.Denote)) = some ⟨2, rfl⟩ at h
  have hn : (some (⟨1, rfl⟩ : PrimTy.uint.Denote)) ≠ some ⟨2, rfl⟩ := by decide +kernel
  exact hn h

theorem typed_landing : Prog.runFrames start (duplicateProgram true) duplicateFrames = .ok afterTwo := by
  unfold Prog.runFrames
  rw [program_steps true]
  with_unfolding_all rfl

theorem duplicated_post : holds afterTwo post := by
  change counterTerm.denote afterTwo = two.denote afterTwo
  have h : counterTerm.denote afterTwo = some (⟨2, rfl⟩ : PrimTy.uint.Denote) :=
    Tm.denote_eval afterTwo counterTerm ⟨2, rfl⟩ (by with_unfolding_all rfl)
  rw [h]
  rfl

theorem premise_accepts_post : holds start ((premise true).fml .diamond .nil .nil post) := by
  change Modality.afterRunTR .diamond (fun τ => holds τ post) (Prog.runFrames start (duplicateProgram true) duplicateFrames)
  rw [typed_landing]
  exact ⟨duplicated_post, by intro h; cases h⟩

theorem real_frames : Prog.runFrames start (.cons (statement true) .nil) .nil = .ok afterOne := by with_unfolding_all rfl

theorem execution_rejects_post : ¬ holds start (.modal .diamond (.cons (statement true) .nil) .nil post) := by
  change ¬ Modality.afterRunTR .diamond (fun τ => holds τ post) (Prog.runFrames start (.cons (statement true) .nil) .nil)
  rw [real_frames]
  intro h
  exact actual_rejects_post h.1

theorem checked_kill : ¬ Premise.Sound .diamond (statement true) (premise true) start := by
  intro h
  exact execution_rejects_post (h .nil .nil post premise_accepts_post)

#print axioms call_one_false
#print axioms call_one_true
#print axioms call_two_false
#print axioms call_two_true
#print axioms append_false
#print axioms append_true
#print axioms first_step
#print axioms second_step
#print axioms append_step
#print axioms program_steps
#print axioms source_link
#print axioms input_inhabited
#print axioms getter_once
#print axioms pure_once
#print axioms pure_twice_control
#print axioms actual_counter_one
#print axioms actual_rejects_post
#print axioms typed_landing
#print axioms duplicated_post
#print axioms premise_accepts_post
#print axioms real_frames
#print axioms execution_rejects_post
#print axioms checked_kill
set_option pp.fullNames true
#check @call_one_false
#check @call_one_true
#check @call_two_false
#check @call_two_true
#check @append_false
#check @append_true
#check @first_step
#check @second_step
#check @append_step
#check @program_steps
#check @source_link
#check @input_inhabited
#check @getter_once
#check @pure_once
#check @pure_twice_control
#check @actual_counter_one
#check @actual_rejects_post
#check @typed_landing
#check @duplicated_post
#check @premise_accepts_post
#check @real_frames
#check @execution_rejects_post
#check @checked_kill
#check @Solidity.Taclet.storagePush_unfold_leftCallReceiver
end H28.AliasTwiceKill
