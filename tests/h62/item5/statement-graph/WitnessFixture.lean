import tests.h62.item5.«statement-graph».Exporter

/-! Positive witnesses and explicitly labeled intentional-contradiction controls.
No production statement or pending G49 declaration is inferred from this fixture. -/
namespace H62WitnessFixture
universe u
@[h62_helper] theorem naturalReflexive (n : Nat) : n = n := rfl
@[h62_statement] theorem consumer (n : Nat) (same : n = n) : n = n := same
#h62_witness "binder" consumer 1 naturalReflexive

@[h62_premise] structure Certificate : Type where
  proof : True
@[h62_helper] theorem trueProducer : True := True.intro
@[h62_helper] def certificateProducer : Certificate := ⟨True.intro⟩
@[h62_statement] theorem useCertificate (certificate : Certificate) : True := certificate.proof
#h62_witness "field" Certificate 0 trueProducer
#h62_witness "binder" useCertificate 0 certificateProducer

@[h62_statement] structure Pair (n : Nat) : Type where
  first : n = n
  second : n = n
@[h62_helper] theorem secondProducer (n : Nat) (first : n = n) : n = n := first
#h62_witness "field" Pair 0 naturalReflexive
#h62_witness "field" Pair 1 secondProducer

@[h62_helper] theorem polymorphic (α : Type u) (x : α) : x = x := rfl
@[h62_statement] theorem polyConsumer (α : Type u) (x : α) (same : x = x) : x = x := same
#h62_witness "binder" polyConsumer 2 polymorphic

-- Intentional contradiction: a typed True witness does not discharge False.
@[h62_helper] theorem conditionalProducer (_absurd : False) : True := True.intro
@[h62_statement] theorem conditional (_absurd : False) (trivial : True) : True := trivial
#h62_witness "binder" conditional 1 conditionalProducer
#h62_export "witness-fixture.json" [naturalReflexive, consumer, Certificate, trueProducer, certificateProducer, useCertificate, Pair, secondProducer, polymorphic, polyConsumer, conditionalProducer, conditional]
end H62WitnessFixture
#h62_export "witness-fixture-repeat.json" [H62WitnessFixture.naturalReflexive, H62WitnessFixture.consumer, H62WitnessFixture.Certificate, H62WitnessFixture.trueProducer, H62WitnessFixture.certificateProducer, H62WitnessFixture.useCertificate, H62WitnessFixture.Pair, H62WitnessFixture.secondProducer, H62WitnessFixture.polymorphic, H62WitnessFixture.polyConsumer, H62WitnessFixture.conditionalProducer, H62WitnessFixture.conditional]
