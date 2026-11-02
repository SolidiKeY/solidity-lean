import Solidity.Lowering.P9.ProgramAdmission

/-! Public whole-program adapter: enumerate every source function declaration,
rather than requiring consumers to supply a manually chosen call allowlist.
Admission is still the executable fragment check, not mere elaboration success.
-/
namespace Solidity.Lowering.P9.WholeProgram
open Source

def functions (res : Resolution) : List Decl :=
  res.unit.decls.filter (fun d => decide (d.kind = .function))

def checkFunctions (res : Resolution) (G : Glob res.env) (c : String) : Bool :=
  check res G c (functions res)

theorem functions_mem (res : Resolution) (d : Decl) :
    d ∈ functions res ↔ d ∈ res.unit.decls ∧ d.kind = .function := by
  simp only [functions, List.mem_filter, decide_eq_true_eq]

theorem functions_sound (el : Elaborated) (G : Glob el.res.env) (hG : G.prog = el.prog)
    (c : String) (hc : checkFunctions el.res G c = true) :
    CallsOK (fun d => d ∈ functions el.res) G c :=
  check_sound el G hG c _ hc

theorem functions_from_elaborate (res : Resolution)
    (ha : (Source.elaborate res).isSome = true) (G : Glob res.env)
    (hG : G.prog = Source.progOf res.env) (c : String)
    (hc : checkFunctions res G c = true) :
    CallsOK (fun d => d ∈ functions res) G c :=
  from_elaborate res ha G hG c _ hc

#print axioms functions_from_elaborate
end Solidity.Lowering.P9.WholeProgram
