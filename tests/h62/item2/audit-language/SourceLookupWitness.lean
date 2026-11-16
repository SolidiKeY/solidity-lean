import tests.h62.item2.«audit-language».FullTelescopeWitness
import Solidity.Source.Resolve

/-!
Guarded regression: builtin-first resolution must not bypass a local or declared
name. Whole frozen telescopes share actual lookup/judgment evidence, including
repeated locals and a declaration shadowing the builtin `msg`. General clients
retain each precedence premise and rule out a builtin result when a local exists.
These certify deterministic source name resolution, not compiler totality or
historical ownership replay.
-/
set_option autoImplicit false
namespace Solidity.H62.AuditLanguage.SourceLookupWitness
open Solidity.Source

def emptyEnv : Env := ⟨[]⟩
def declaredUnit : Syn .unit := .unit (.cons (.topPart
  (.struct "msg" (.structMember (.elem .bool) "flag") .nil)) .nil)
def declEnv : Env := declaredUnit.env

theorem sound_full : hypotheses_of% Env.resolve_sound := by
  exact ⟨emptyEnv, [], none, "msg", Denot.builtin .msg, rfl, True.intro⟩
#verify_hypotheses sound_full for Solidity.Source.Env.resolve_sound
#print axioms sound_full

theorem judgment_full : hypotheses_of% Resolves.resolve := by
  exact ⟨declEnv, [], none, "msg", Denot.decls (declEnv.lookup none "msg"), Resolves.decl rfl (by intro impossible; cases impossible), True.intro⟩
#verify_hypotheses judgment_full for Solidity.Source.Resolves.resolve
#print axioms judgment_full

theorem iff_full : hypotheses_of% resolve_iff := by
  exact ⟨declEnv, [], none, "msg", Denot.decls (declEnv.lookup none "msg"), True.intro⟩
#verify_hypotheses iff_full for Solidity.Source.resolve_iff
#print axioms iff_full

theorem unique_full : hypotheses_of% Resolves.unique := by
  exact ⟨declEnv, ["other", "msg", "msg"], none, "msg", Denot.loc 1, Denot.loc 1, Resolves.inLocals 1 rfl, Resolves.inLocals 1 rfl, True.intro⟩
#verify_hypotheses unique_full for Solidity.Source.Resolves.unique
#print axioms unique_full

/-- Any present local takes precedence over declarations and builtins. -/
theorem local_precedence (E : Env) (names : List String) (scope : Option String)
    (name : String) (i : Nat) (found : names.idxOf? name = some i) :
    E.resolve names scope name = some (.loc i) := by
  simp only [Env.resolve, found]

/-- With no local, any declaration takes precedence over a builtin. -/
theorem declaration_precedence (E : Env) (names : List String) (scope : Option String)
    (name : String) (noLocal : names.idxOf? name = none)
    (declared : E.lookup scope name ≠ []) :
    E.resolve names scope name = some (.decls (E.lookup scope name)) :=
  (Resolves.decl noLocal declared).resolve

/-- A builtin resolves only after the absence of local and declaration shadows. -/
theorem builtin_fallback (E : Env) (names : List String) (scope : Option String)
    (name : String) (builtin : Builtin) (noLocal : names.idxOf? name = none)
    (noDecl : E.lookup scope name = []) (known : Builtin.ofName name = some builtin) :
    E.resolve names scope name = some (.builtin builtin) :=
  (Resolves.builtin builtin noLocal noDecl known).resolve

/-- A builtin-first result cannot satisfy local resolution's output contract. -/
theorem builtin_first_refused (E : Env) (names : List String) (scope : Option String)
    (name : String) (i : Nat) (builtin : Builtin) (found : names.idxOf? name = some i) :
    E.resolve names scope name ≠ some (.builtin builtin) := by
  rw [local_precedence E names scope name i found]
  intro impossible
  cases impossible

example : declEnv.resolve ["other", "msg", "msg"] none "msg" = some (.loc 1) := rfl
example : declEnv.resolve [] none "msg" = some (.decls (declEnv.lookup none "msg")) := rfl
example : emptyEnv.resolve [] none "msg" = some (.builtin .msg) := rfl
example : emptyEnv.resolve [] none "notDeclared" = none := rfl

#print axioms local_precedence
#print axioms declaration_precedence
#print axioms builtin_fallback
#print axioms builtin_first_refused
end Solidity.H62.AuditLanguage.SourceLookupWitness
