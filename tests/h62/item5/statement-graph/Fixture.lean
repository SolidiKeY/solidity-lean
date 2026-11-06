import tests.h62.item5.«statement-graph».Exporter
namespace H62Fixture
@[h62_statement] theorem base : True := True.intro
@[h62_premise] def Accepted (n : Nat) : Prop := n = n
@[h62_helper] theorem reflexive (n : Nat) : n = n := rfl
@[h62_statement] theorem leaf (n : Nat) : Accepted n := reflexive n
@[h62_statement] theorem root (n : Nat) (accepted : Accepted n) : Accepted n := accepted
@[h62_statement] structure Contract (n : Nat) : Prop where
  available : Accepted n
#h62_export "fixture.json" [Accepted, reflexive, leaf, root, base, Contract]
end H62Fixture
#h62_export "fixture-repeat.json" [H62Fixture.Accepted, H62Fixture.reflexive, H62Fixture.leaf, H62Fixture.root, H62Fixture.base, H62Fixture.Contract]
