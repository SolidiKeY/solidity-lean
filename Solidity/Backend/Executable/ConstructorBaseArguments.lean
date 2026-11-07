import Solidity.Source.Semantics
import Solidity.Source.Hoare

/-! Actual inherited-constructor argument binding. Uses the published
Source.giveArgs accumulator and Vals.onto; no constructor/body/compiler/world
simulation or new evaluator is assumed. -/
namespace Solidity.Backend.Executable.ConstructorBaseArguments
open Solidity
variable {E : Source.Env} {Γ : Source.RCtx}

def localArgs (a b : Source.IntTy)
    (i : Source.Idx Γ (.int a)) (j : Source.Idx Γ (.int b))
    (ha : (Source.STy.int a).implicit E.isBase E.mapFree (.int a) = true)
    (hb : (Source.STy.int b).implicit E.isBase E.mapFree (.int b) = true) :
    Source.RConvArgs E Γ [.int a,.int b] :=
  .cons (.local i) ha (.cons (.local j) hb .nil)

def argument (G : Source.Glob E) (derived base : String) (a b : Source.IntTy)
    (i : Source.Idx (G.prog.ctorLocals derived) (.int a))
    (j : Source.Idx (G.prog.ctorLocals derived) (.int b))
    (ha : (Source.STy.int a).implicit E.isBase E.mapFree (.int a) = true)
    (hb : (Source.STy.int b).implicit E.isBase E.mapFree (.int b) = true) :
    Source.RBaseArg E (G.prog.ctorLocals derived) :=
  ⟨base,[.int a,.int b],localArgs a b i j ha hb⟩

/-- Actual pure local argument execution over arbitrary constructor-local
indices. The premises describe initial reads, not an assumed execution. -/
theorem evaluated :
∀ {E : Solidity.Source.Env} {Γ : Solidity.Source.RCtx}
 (G : Solidity.Source.Glob E) (F : Solidity.Source.Fr) (n : Nat)
 (a b : Solidity.Source.IntTy) (i : Solidity.Source.Idx Γ (.int a)) (j : Solidity.Source.Idx Γ (.int b))
 (ha : (Solidity.Source.STy.int a).implicit E.isBase E.mapFree (.int a) = true)
 (hb : (Solidity.Source.STy.int b).implicit E.isBase E.mapFree (.int b) = true)
 (l : Solidity.Source.Locals E.layout Γ) (s : Solidity.Source.St E)
 (x y : Int) (hx : a.lo ≤ x ∧ x ≤ a.hi) (hy : b.lo ≤ y ∧ y ≤ b.hi)
 (hi : l.get i = .int x hx) (hj : l.get j = .int y hy),
 (Solidity.Source.evalConvArgs G F (n+3)
  (Solidity.Backend.Executable.ConstructorBaseArguments.localArgs a b i j ha hb)).run (l,s) =
 (.ok (.cons (.int x hx) (.cons (.int y hy) .nil)),(l,s)) := by
  intro E Γ G F n a b i j ha hb l s x y hx hy hi hj
  simp only [localArgs, Source.evalConvArgs, Source.evalE, Source.convRV, dite_true]
  change (Except.ok (Source.Vals.cons (l.get i) (.cons (l.get j) .nil)),(l,s)) = _
  rw [hi,hj]

/-- The existing priority branch skips all argument evaluation, independent
of its budget and effects. This is not a new admitted-source restriction. -/
theorem already_given :
∀ {E : Solidity.Source.Env} (G : Solidity.Source.Glob E) (F : Solidity.Source.Fr)
 (n : Nat) (derived : String) (l : Solidity.Source.Locals E.layout (G.prog.ctorLocals derived))
 (ba : Solidity.Source.RBaseArg E (G.prog.ctorLocals derived)) (acc : Solidity.Source.CtorLocals G)
 (present : acc.any (fun entry => entry.1 == ba.base) = true),
 Solidity.Source.giveArgs G F n derived l [ba] acc = pure acc := by
  intro E G F n derived l ba acc present
  simp only [Source.giveArgs,present,ite_true]

/-- Actual inherited-argument insertion, including the real parameter reversal
and complete original world. Frame equality is initial program metadata. -/
theorem bound :
∀ {E : Solidity.Source.Env}
 (G : Solidity.Source.Glob E) (F : Solidity.Source.Fr) (n : Nat)
 (derived base : String) (a b : Solidity.Source.IntTy)
 (i : Solidity.Source.Idx (G.prog.ctorLocals derived) (.int a))
 (j : Solidity.Source.Idx (G.prog.ctorLocals derived) (.int b))
 (ha : (Solidity.Source.STy.int a).implicit E.isBase E.mapFree (.int a) = true)
 (hb : (Solidity.Source.STy.int b).implicit E.isBase E.mapFree (.int b) = true)
 (l : Solidity.Source.Locals E.layout (G.prog.ctorLocals derived))
 (s : Solidity.Source.St E) (acc : Solidity.Source.CtorLocals G)
 (absent : acc.any (fun entry => entry.1 == base) = false)
 (frame : [Solidity.Source.STy.int b,.int a] = G.prog.ctorLocals base)
 (x y : Int) (hx : a.lo ≤ x ∧ x ≤ a.hi) (hy : b.lo ≤ y ∧ y ≤ b.hi)
 (hi : l.get i = .int x hx) (hj : l.get j = .int y hy),
 (Solidity.Source.giveArgs G F (n+3) derived l
  [Solidity.Backend.Executable.ConstructorBaseArguments.argument G derived base a b i j ha hb] acc).run
  (Solidity.Source.L0 E,s) =
 (.ok (acc ++ [⟨base,frame ▸ (Solidity.Source.Locals.cons (.int y hy) (.cons (.int x hx) .nil))⟩]),
  (Solidity.Source.L0 E,s)) := by
  intro E G F n derived base a b i j ha hb l s acc absent frame x y hx hy hi hj
  have subRun :
      (Source.EM.sub (Γ := []) l (Source.evalConvArgs G F (n+3)
        (localArgs a b i j ha hb))).run (Source.L0 E,s) =
      (.ok (Source.Vals.cons (.int x hx) (.cons (.int y hy) .nil),l),(Source.L0 E,s)) := by
    have raw : (Source.evalConvArgs G F (n+3) (localArgs a b i j ha hb)) (l,s) =
        (Except.ok (Source.Vals.cons (.int x hx) (.cons (.int y hy) .nil)),(l,s)) :=
      evaluated G F n a b i j ha hb l s x y hx hy hi hj
    simp only [Source.EM.sub,ExceptT.run,ExceptT.mk,raw]
  simp only [argument,Source.giveArgs,absent,Bool.false_eq_true,if_false,
    Source.Hoare.run_bind,subRun,List.reverseAux,dif_pos frame]
  rfl

/-- The body lookup really reads the appended frame, derived from absence of
an earlier base; it is not supplied as a desired lookup equation. -/
theorem lookup_appended :
∀ {E : Solidity.Source.Env} {Γ : Solidity.Source.RCtx}
 (G : Solidity.Source.Glob E) (acc : Solidity.Source.CtorLocals G) (base : String)
 (locals : Solidity.Source.Locals E.layout (G.prog.ctorLocals base))
 (absent : acc.any (fun entry => entry.1 == base) = false),
 Solidity.Source.ctorLocalsOf (Γ := Γ) G (acc ++ [⟨base,locals⟩]) base = pure locals := by
  intro E Γ G acc base locals absent
  have empty : acc.find? (fun entry => entry.1 == base) = none :=
    List.find?_eq_none.mpr (List.any_eq_false.mp absent)
  simp only [Source.ctorLocalsOf,List.find?_append,empty,Option.or,
    List.find?_cons,beq_self_eq_true,dite_true]

end Solidity.Backend.Executable.ConstructorBaseArguments
