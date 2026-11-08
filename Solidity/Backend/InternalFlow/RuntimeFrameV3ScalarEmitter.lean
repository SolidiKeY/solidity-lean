import Solidity.Backend.InternalFlow.RuntimeFrameV3DisjointScalarReturn

/-! Executable selection for the admitted scalar countdown family. The
published value compiler supplies the argument code and certificate; decidable
static geometry separates caller locals, private callee locals and saved
runtime control cells. Runtime payload capacity is a soundness premise, not
assumed by selection. This is not the general recursive compiler. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.ScalarEmitter
open Evm Evm.Memory

def Geometry (b c frame pointer bottom : Nat) (Γ : Ctx) : Prop :=
 b+Γ.length≤c ∧ c+3≤pointer ∧ pointer<frame ∧
 c+3≤bottom ∧ bottom<frame ∧ bottom≠pointer

instance geometryDecidable (b c frame pointer bottom : Nat) (Γ : Ctx) : Decidable (Geometry b c frame pointer bottom Γ) :=
 inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

structure Emission {C : Contract} {Γ : Ctx} (b c frame pointer bottom : Nat)
 (F : Frag Γ) (count : Val C Γ .uint) where
 value : CompiledVal b F count
 geometry : Geometry b c frame pointer bottom Γ

def compile {C : Contract} {Γ : Ctx} (b c frame pointer bottom : Nat)
 (F : Frag Γ) (count : Val C Γ .uint) : Option (Emission b c frame pointer bottom F count) :=
 if geometry : Geometry b c frame pointer bottom Γ then do
   let value ← Memory.compileVal b F count
   pure ⟨value,geometry⟩
 else none

def Emission.code {C : Contract} {Γ : Ctx} {R : RefTy} {b c frame pointer bottom : Nat}
 {F : Frag Γ} {count : Val C Γ .uint} (emitted : Emission b c frame pointer bottom F count)
 (reference : Idx Γ (.mem R)) (destination : Idx Γ (.val .uint)) : List Instr :=
 DisjointScalarReturn.code b c reference emitted.value destination pointer bottom

theorem selected {C : Contract} {Γ : Ctx} {b c frame pointer bottom : Nat}
 {F : Frag Γ} {count : Val C Γ .uint} (value : CompiledVal b F count)
 (actual : Memory.compileVal b F count=some value) (geometry : Geometry b c frame pointer bottom Γ) :
 compile b c frame pointer bottom F count=some ⟨value,geometry⟩ := by
 simp only [compile,dif_pos geometry,actual]
 rfl

theorem refused_geometry {C : Contract} {Γ : Ctx} {b c frame pointer bottom : Nat}
 {F : Frag Γ} {count : Val C Γ .uint} (outside : ¬Geometry b c frame pointer bottom Γ) :
 compile b c frame pointer bottom F count=none := by
 simp only [compile,dif_neg outside]

theorem refused_value {C : Contract} {Γ : Ctx} {b c frame pointer bottom : Nat}
 {F : Frag Γ} {count : Val C Γ .uint} (outside : Memory.compileVal b F count=none) :
 compile b c frame pointer bottom F count=none := by
 unfold compile
 split <;> simp only [outside] <;> rfl

/-- Every successful selector result retains the exact public value selection,
not only an extensionally similar hand-built argument certificate. -/
theorem selected_value {C : Contract} {Γ : Ctx} {b c frame pointer bottom : Nat}
 {F : Frag Γ} {count : Val C Γ .uint} {emitted : Emission b c frame pointer bottom F count}
 (root : compile b c frame pointer bottom F count=some emitted) :
 Memory.compileVal b F count=some emitted.value := by
 unfold compile at root
 split at root
 · cases actual : Memory.compileVal b F count with
   | none =>
     simp only [actual] at root
     cases root
   | some value =>
     simp only [actual] at root
     have same := Option.some.inj root
     cases same
     rfl
 · cases root

end Solidity.Backend.InternalFlow.RuntimeFrame.ScalarEmitter
