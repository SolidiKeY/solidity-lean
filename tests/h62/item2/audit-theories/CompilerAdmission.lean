import Solidity.Evm.Compiler
import tests.h62.item2.«audit-theories».CoreTotality

/-! Concrete public-entry admission and success contract. Both bool values
must be accepted and encoded in the final machine's local cell. Reject-all and
always-revert controls are excluded by observable code execution. This is not
a claim about gas/fork/byte failure observations absent from the core machine. -/
namespace H62.AuditTheories.CompilerAudit
open Solidity Solidity.Evm

/-- Every program in the existing core fragment is admitted by the public
entry; a compiler returning none everywhere cannot satisfy this totality. -/
theorem core_compile_admitted {C : Contract} {Γ Δ : Ctx} {b : Nat}
    {F : Frag Γ} {F' : Frag Δ} {P : Solidity.Prog C Γ Δ}
    (certificate : inFragP F P = some F') :
    Compiler.compile b F P = some (.core F' certificate) := by
  unfold Compiler.compile
  split
  · rename_i frag hc
    have same : frag = F' := Option.some.inj (hc.symm.trans certificate)
    subst frag
    rfl
  · rename_i hc
    have impossible : (none : Option (Frag Δ)) = some F' := hc.symm.trans certificate
    cases impossible

/-- The common checked entry actually accepts each supported bool program. -/
theorem bool_compile_admitted (C : Contract) (value : Bool) :
    Compiler.compile 0 (Frag.init []) (boolProgram C value) =
      some (.core (Frag.init [.val .bool]) (bool_fragment C value)) :=
  core_compile_admitted (bool_fragment C value)

/-- The actual public entry projected to executable code. -/
def actualBoolCompiler (C : Contract) (value : Bool) : Option (List Instr) :=
  (Compiler.compile 0 (Frag.init []) (boolProgram C value)).map Compiler.Compilation.code

/-- Total admission plus the exact successful bool observation, for both inputs. -/
def BoolSuccessContract (candidate : Bool → Option (List Instr)) : Prop :=
  ∀ value, ∃ code m', candidate value = some code ∧
    Evm.run code initialMachine = .ok m' 0 ∧
    m'.mem 0 = (if value then w[1] else w[0]) ∧ m'.stack = []

/-- The checked entry meets the success contract with an observable local value. -/
theorem actual_compiler_success (C : Contract) : BoolSuccessContract (actualBoolCompiler C) := by
  intro value
  obtain ⟨m', hr, hm, hs⟩ := bool_target_success C value
  refine ⟨compileProg 0 (boolProgram C value), m', ?_, hr, hm, hs⟩
  simp only [actualBoolCompiler, bool_compile_admitted, Option.map_some, Compiler.Compilation.code]

/-- A compiler rejecting every input cannot satisfy total supported admission. -/
theorem reject_all_refuted : ¬ BoolSuccessContract (fun _ => none) := by
  intro h
  obtain ⟨code, m, hc, _⟩ := h true
  cases hc

/-- A compiler always emitting REVERT is admitted but violates success. -/
theorem always_revert_refuted : ¬ BoolSuccessContract (fun _ => some [.revert]) := by
  intro h
  obtain ⟨code, m, hc, hr, _⟩ := h true
  cases hc
  cases hr

/-- The common compiler's complete Input predicate is jointly inhabited. -/
theorem bool_public_joint_input (C : Contract) (value : Bool) :
    (Compiler.Compilation.core (b := 0) (Frag.init [.val .bool])
      (bool_fragment C value)).Input 1 0 (fun _ => ⟨0, W_pos⟩)
      (freshT C 0 W_pos ⟨0, W_pos⟩) initialMachine := by
  exact ⟨(bool_core_joint_input C value).1, (bool_core_joint_input C value).2.1⟩

/-- Total admission and the ENTIRE successful public observation, strengthened
with exact source/target bool values. This is additive to public correctness. -/
def FullSuccess (C : Contract) (value : Bool) : Prop :=
    ∃ (result : Compiler.Compilation 0 (Frag.init []) (boolProgram C value))
      (o : Solidity.Out C (freshT C 0 W_pos ⟨0, W_pos⟩).H [.val .bool]) (m' : Machine),
      Compiler.compile 0 (Frag.init []) (boolProgram C value) = some result ∧
      result.Input 1 0 (fun _ => ⟨0, W_pos⟩) (freshT C 0 W_pos ⟨0, W_pos⟩) initialMachine ∧
      Solidity.Prog.run (freshT C 0 W_pos ⟨0, W_pos⟩) (boolProgram C value) = .ok o ∧
      o.st.env.1 = value ∧ Evm.run result.code initialMachine = .ok m' 0 ∧
      m'.mem 0 = (if value then w[1] else w[0]) ∧ m'.stack = initialMachine.stack ∧
      result.Rep (1 + Evm.Prog.pushes (boolProgram C value)) 0 (fun _ => ⟨0, W_pos⟩)
        (freshT C 0 W_pos ⟨0, W_pos⟩) initialMachine o.st m'

/-- The complete concrete compilation/source/target packet shares one program,
one initial state/machine and all original public success observations. -/
theorem supported_end_to_end (C : Contract) (value : Bool) : FullSuccess C value := by
  obtain ⟨o, ho, hv⟩ := bool_source_success C value (freshT C 0 W_pos ⟨0, W_pos⟩)
  obtain ⟨sim, growth, _⟩ := bool_core_joint_input C value
  obtain ⟨m', hr, hs, hsim⟩ := core_success (bool_fragment C value) sim
    growth (bool_no_payment C value) ho
  obtain ⟨m'', hr', hmem, _⟩ := bool_target_success C value
  rw [hr] at hr'
  cases hr'
  exact ⟨.core (Frag.init [.val .bool]) (bool_fragment C value), o, m',
    bool_compile_admitted C value, bool_public_joint_input C value, ho, hv, hr, hmem, hs, hsim⟩

/-- The stronger packet entails the unchanged public agreement predicate;
no storage/ledger/environment observation has been dropped. -/
theorem success_retains_public_contract (C : Contract) (value : Bool) :
    ∃ (result : Compiler.Compilation 0 (Frag.init []) (boolProgram C value)),
      Compiler.compile 0 (Frag.init []) (boolProgram C value) = some result ∧
      result.Input 1 0 (fun _ => ⟨0, W_pos⟩) (freshT C 0 W_pos ⟨0, W_pos⟩) initialMachine ∧
      result.Agrees 1 0 (fun _ => ⟨0, W_pos⟩) (freshT C 0 W_pos ⟨0, W_pos⟩) initialMachine := by
  obtain ⟨result, o, m', hc, hi, ho, _, hr, _, hs, hrep⟩ := supported_end_to_end C value
  exact ⟨result, hc, hi, .inl ⟨o, m', ho, hr, hs, hrep⟩⟩

/-- Always succeeding without executing the declaration also fails its value
observation; success alone is insufficient. -/
theorem always_noop_refuted : ¬ BoolSuccessContract (fun _ => some []) := by
  intro h
  obtain ⟨code, m, hc, hr, hm, _⟩ := h true
  cases hc
  cases hr
  have different : (w[0] : Word) ≠ w[1] := by decide
  exact different hm

/-- A closed populated contract instance makes the packet's domain explicitly
nonempty; generic parameters are not used as a substitute for a witness. -/
theorem concrete_success_packet : FullSuccess StandardExample true :=
  supported_end_to_end StandardExample true

#print axioms success_retains_public_contract
#print axioms core_compile_admitted
#print axioms concrete_success_packet
#print axioms supported_end_to_end
#print axioms always_noop_refuted
#print axioms bool_compile_admitted
#print axioms actual_compiler_success
#print axioms reject_all_refuted
#print axioms always_revert_refuted
#print axioms bool_public_joint_input
end H62.AuditTheories.CompilerAudit
