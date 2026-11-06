import Solidity.Lowering.P9.CatalogControls
import Solidity.Lowering.P9.RecursiveControls
import Solidity.Lowering.P9.GraphControls
import Solidity.Lowering.P9.ReturnControls
import Solidity.Lowering.P9.ProgramAdmission
import Solidity.Lowering.P9.AdmissionControls

/-! The general executable checker consumes the `ElaboratedCalls` Source fixture.
Its original execution proofs are reused, not re-proved.
-/
namespace Solidity.Lowering.P9.ProgramControls
open Source

theorem checker_accepts (fixed : Roadmap.Fixed) :
    WholeProgram.check resolution (glob fixed) "P9" [declaration] = true := by
  simp only [WholeProgram.check, List.all_cons, List.all_nil, Bool.and_true,
    Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨rfl, declaration_present, ?_⟩
  have hb : (glob fixed).prog.body declaration = some body := prog_body
  simp only [WholeProgram.checkBody, signature, dispatch_eq, hb]
  rfl

/-- `WholeProgram.check_sound` derives the nonempty actual program's certificate. -/
theorem derived_callsOK (fixed : Roadmap.Fixed) :
    CallsOK (fun d => d ∈ [declaration]) (glob fixed) "P9" :=
  WholeProgram.from_elaborate resolution AdmissionControls.truth_accepted
    (glob fixed) rfl "P9" [declaration] (checker_accepts fixed)

theorem allowed_nonempty : ∃ d ∈ [declaration], (d.fnSig resolution.env).isSome = true :=
  ⟨declaration, List.mem_singleton.mpr rfl, rfl⟩

/-- It is the derived certificate, rather than a hand-written certificate,
that now supplies source progress. -/
theorem checked_not_stuck (fixed : Roadmap.Fixed) (n : Nat) :
    NS (Source.evalE (glob fixed) caller n call) :=
  Source.evalE_callFrag_ns (derived_callsOK fixed) caller rfl n call
    ⟨List.mem_singleton.mpr rfl, trivial⟩ trivial

/-- Retain the full inherited execution observation and its caller frame. -/
theorem checked_execution (fixed : Roadmap.Fixed) (s : Source.St resolution.env) :
    (Source.evalE (glob fixed) caller 11 protectedCall).run (.cons (.bool false) .nil, s) =
      (.ok (.val (.bool true)), (.cons (.bool false) .nil, s)) :=
  protected_success fixed s

def globOf (res : Source.Resolution) (fixed : Roadmap.Fixed) : Source.Glob res.env :=
  ⟨Source.progOf res.env, .legacy, fixed, fun _ => ⟨0, by decide⟩,
    fun _ _ => true, fun _ => .answer (.success []), ⟨0, by decide⟩⟩

def incoherent : Source.Resolution := {resolution with env := ⟨[]⟩}

theorem incoherent_refused (fixed : Roadmap.Fixed) :
    WholeProgram.check incoherent (globOf incoherent fixed) "P9" [] = false := by
  rfl

open AdmissionControls in
/-- Abstract source admission does not invent the missing implementation. -/
theorem abstract_refused (fixed : Roadmap.Fixed) :
    WholeProgram.check interfaceResolution (globOf interfaceResolution fixed) "NoContract" [abstractDecl] = false := by
  rfl

#print axioms checker_accepts
#print axioms derived_callsOK
#print axioms checked_not_stuck
#print axioms checked_execution
#print axioms incoherent_refused
#print axioms abstract_refused
end Solidity.Lowering.P9.ProgramControls
