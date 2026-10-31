import Solidity.Source.Semantics

/-! Actual published initializer/base-argument finite-prefix laws. They thread
the full existing source EM state and exact failure, without a new evaluator,
constructor order, source admission rule or compiler simulation. -/
namespace Solidity.Backend.Executable.SourceInitializers
open Solidity.Source
variable {E : Env}

theorem inits_append (G : Glob E) (F : Fr) (n : Nat) (first rest : List (RInit E)) :
    runInits G F n (first ++ rest) = (runInits G F n first >>= fun _ => runInits G F n rest) := by
  induction first with
  | nil => simp only [List.nil_append, runInits, pure_bind]
  | cons init first ih => simp only [List.cons_append, runInits, ih, bind_assoc]

theorem collect_append (G : Glob E) (F : Fr) (n : Nat) (first rest : List String) (acc : CtorLocals G) :
    collectArgs G F n (first ++ rest) acc =
      (collectArgs G F n first acc >>= fun middle => collectArgs G F n rest middle) := by
  induction first generalizing acc with
  | nil => simp only [List.nil_append, collectArgs, pure_bind]
  | cons name first ih => simp only [List.cons_append, collectArgs, ih, bind_assoc]

theorem arguments_append (G : Glob E) (F : Fr) (n : Nat) (name : String)
    (locals : Locals E.layout (G.prog.ctorLocals name))
    (first rest : List (RBaseArg E (G.prog.ctorLocals name))) (acc : CtorLocals G) :
    giveArgs G F n name locals (first ++ rest) acc =
      (giveArgs G F n name locals first acc >>= fun middle => giveArgs G F n name locals rest middle) := by
  induction first generalizing acc with
  | nil => simp only [List.nil_append, giveArgs, pure_bind]
  | cons arg first ih =>
    simp only [List.cons_append, giveArgs]
    cases acc.any (fun pair => pair.fst == arg.base) with
    | true => simp only [if_true]; exact ih acc
    | false =>
      simp only [Bool.false_eq_true, if_false, bind_assoc]
      congr 1
      funext pair
      rcases pair with ⟨values, ignored⟩
      split
      · exact ih _
      · rfl

/-- The exact successful intermediate state supplies the suffix input. -/
theorem inits_success (G : Glob E) (F : Fr) (n : Nat) (first rest : List (RInit E))
    (before after : Locals E.layout [] × St E)
    (ran : (runInits G F n first).run before = (.ok (),after)) :
    (runInits G F n (first ++ rest)).run before = (runInits G F n rest).run after := by
  rw [inits_append]
  change ExceptT.bindCont (fun _ : Unit => runInits G F n rest)
    ((runInits G F n first).run before).1 ((runInits G F n first).run before).2 = _
  rw [ran]
  rfl

/-- Failure retains its complete actual source state and halt; suffix
initializers never execute. Rollback is a separate enclosing source operation. -/
theorem inits_failure (G : Glob E) (F : Fr) (n : Nat) (first rest : List (RInit E))
    (before after : Locals E.layout [] × St E) (halt : Halt)
    (failed : (runInits G F n first).run before = (.error halt,after)) :
    (runInits G F n (first ++ rest)).run before = (.error halt,after) := by
  rw [inits_append]
  change ExceptT.bindCont (fun _ : Unit => runInits G F n rest)
    ((runInits G F n first).run before).1 ((runInits G F n first).run before).2 = _
  rw [failed]
  rfl

/-- Actual base-argument failure likewise blocks the rest with its exact
halt/state. This alone makes no completed transaction or rollback claim. -/
theorem arguments_failure (G : Glob E) (F : Fr) (n : Nat) (name : String)
    (locals : Locals E.layout (G.prog.ctorLocals name))
    (first rest : List (RBaseArg E (G.prog.ctorLocals name))) (acc : CtorLocals G)
    (before after : Locals E.layout [] × St E) (halt : Halt)
    (failed : (giveArgs G F n name locals first acc).run before = (.error halt,after)) :
    (giveArgs G F n name locals (first ++ rest) acc).run before = (.error halt,after) := by
  rw [arguments_append]
  change ExceptT.bindCont (fun middle => giveArgs G F n name locals rest middle)
    ((giveArgs G F n name locals first acc).run before).1
    ((giveArgs G F n name locals first acc).run before).2 = _
  rw [failed]
  rfl

/-- info: 'Solidity.Backend.Executable.SourceInitializers.inits_append' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms inits_append
/-- info: 'Solidity.Backend.Executable.SourceInitializers.collect_append' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms collect_append
/-- info: 'Solidity.Backend.Executable.SourceInitializers.inits_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms inits_success
/-- info: 'Solidity.Backend.Executable.SourceInitializers.arguments_failure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms arguments_failure
/-- info: 'Solidity.Backend.Executable.SourceInitializers.arguments_append' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms arguments_append
/-- info: 'Solidity.Backend.Executable.SourceInitializers.inits_failure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms inits_failure
end Solidity.Backend.Executable.SourceInitializers
