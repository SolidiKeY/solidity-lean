import tests.h62.item5.«statement-graph».Exporter
namespace H62Fixture
private theorem privateWitness (n : Nat) : n = n := rfl
@[h62_statement] theorem base : True := True.intro
@[h62_premise] def Accepted (n : Nat) : Prop := n = n
@[h62_helper] theorem reflexive (n : Nat) : n = n := rfl
@[h62_statement] theorem leaf (n : Nat) : Accepted n := reflexive n
@[h62_statement] theorem root (n : Nat) (accepted : Accepted n) : Accepted n := accepted
@[h62_statement] structure Contract (n : Nat) : Prop where
  available : Accepted n
@[h62_helper] theorem contractWitness (n : Nat) : Contract n := ⟨leaf n⟩
@[h62_premise] structure Certificate where
  resource : Nat
  valid : resource = resource
@[h62_helper] def certificateWitness : Certificate := ⟨0, rfl⟩
@[h62_statement] theorem useCertificate (certificate : Certificate) :
    certificate.resource = certificate.resource := certificate.valid
#h62_export "fixture.json" [Accepted, reflexive, leaf, root, base, Contract, contractWitness, Certificate, certificateWitness, useCertificate]
end H62Fixture
#h62_export "fixture-repeat.json" [H62Fixture.Accepted, H62Fixture.reflexive, H62Fixture.leaf, H62Fixture.root, H62Fixture.base, H62Fixture.Contract, H62Fixture.contractWitness, H62Fixture.Certificate, H62Fixture.certificateWitness, H62Fixture.useCertificate]
#h62_census "fixture-census.json" H62Fixture
#h62_census "fixture-census-repeat.json" H62Fixture
