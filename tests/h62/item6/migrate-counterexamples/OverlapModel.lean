import Solidity.Counterexamples.DeleteFamilyGenericOverlap

/-! A concrete model for the shared, nonconflicting storage equations.
The two pre-fix default rules fail in this model. This is an isolated negative
control; it changes no premise of either original inconsistency theorem. -/
namespace MigrationFixtures.Overlap
abbrev Store := Nat → Int
abbrev Value := Sum Store Int
def zero : Store := fun _ => 0
def castS : Value → Store
  | .inl s => s
  | .inr _ => zero
def castI : Value → Int
  | .inl _ => 0
  | .inr n => n
def selectS (s : Store) (_ : Unit) : Store := fun n => s (n + 1)
def selectI (s : Store) (_ : Unit) : Int := s 0
def put (_ : Store) (_ : Unit) (v : Value) : Store
  | 0 => castI v
  | n + 1 => castS v n
def delNode (s : Store) : Store := s
def delValueS (s : Store) : Store := s

/-- Both cast equations, both same-field store equations, the dedicated
Struct delete equation, mapping preservation and defaultValueStruct coexist. -/
theorem shared_equations_inhabited :
    (∀ s : Store, castS (.inl s) = s) ∧
    (∀ n : Int, castI (.inr n) = n) ∧
    (∀ s f v, selectS (put s f v) f = castS v) ∧
    (∀ s f v, selectI (put s f v) f = castI v) ∧
    (∀ s, delValueS s = delNode s) ∧
    (∀ s, selectS (delNode s) () = selectS s ()) ∧
    (zero = zero) :=
  ⟨fun _ => rfl, fun _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl,
    fun _ => rfl, fun _ => rfl, rfl⟩

theorem conflicting_delValueDefault_fails :
    ¬ (∀ s, delValueS s = zero) := by
  intro h
  have bad : (1 : Int) = 0 := congrFun (h (fun _ => 1)) 0
  omega

theorem conflicting_selectStDelNodeDefault_fails :
    ¬ (∀ s, selectS (delNode s) () = zero) := by
  intro h
  have bad : (1 : Int) = 0 := congrFun (h (fun _ => 1)) 0
  omega

#print axioms shared_equations_inhabited
#print axioms conflicting_delValueDefault_fails
#print axioms conflicting_selectStDelNodeDefault_fails
end MigrationFixtures.Overlap
