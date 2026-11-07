import Solidity.Source.Progress.ForwardingReturns

/-! Explicit finite prefixes of source forwarding entries. Every extension uses
only already certified callees and a fresh declaration. This is a proof
certificate over intrinsic bodies, not an automatic source/graph recognizer. -/
namespace Solidity.Source.Progress
open EM Solidity.Lowering.P9

def forwardFresh (values prior : List Decl) (d : Decl) : Bool :=
  decide (d ∉ values ∧ d ∉ prior)

inductive ForwardingChain (res : Resolution) (G : Glob res.env) (c : String) (values : List Decl) :
    List Decl → Prop
  | ready {ds : List Decl} :
      ReadyMemoryCatalogue (fun d => d ∈ values) G c ds → ForwardingChain res G c values ds
  | extend {ds : List Decl} (earlier : ForwardingChain res G c values ds)
      (d : Decl) (ps : List STy) (τ : STy)
      (declared : d ∈ WholeProgram.functions res) (fresh : forwardFresh values ds d = true)
      (signature : d.fnSig res.env = some (ps,[τ]))
      (e : RExpr res.env (returnContext ps τ) τ) (same : τ.implicit res.env.isBase res.env.mapFree τ = true)
      (plain : PlainResultType τ) (defaults : ZeroReady res.env τ)
      (expression : ComposedExpr (fun d => d ∈ values) (fun d => d ∈ ds) e)
      (body : G.prog.body (G.dispatchFn c d) = some (singleReturningBody ps τ e same)) :
      ForwardingChain res G c values (d :: ds)

theorem forwarding_chain_sound (res : Resolution)
    (elaborated : (Source.elaborate res).isSome = true) (G : Glob res.env)
    (program : G.prog = Source.progOf res.env) (c : String) (values ds : List Decl)
    (checked : WholeProgram.check res G c values = true)
    (chain : ForwardingChain res G c values ds) : ReadyMemoryCalls G c ds := by
  induction chain with
  | ready catalogue =>
    exact ready_memory_from_elaborate res elaborated G program c values _ checked catalogue
  | extend earlier d ps τ declared fresh signature e same plain defaults expression body ih =>
    exact extend_forwarding_calls
      (WholeProgram.from_elaborate res elaborated G program c values checked) ih
      d ps τ signature e same plain expression defaults body

theorem forwarding_chain_program_calls (res : Resolution)
    (elaborated : (Source.elaborate res).isSome = true) (G : Glob res.env)
    (program : G.prog = Source.progOf res.env) (c : String) (values ds : List Decl)
    (checked : WholeProgram.check res G c values = true)
    (chain : ForwardingChain res G c values ds)
    (coverage : readyCoverage res values ds = true) : ReadyProgramCalls res G c := by
  have old := WholeProgram.from_elaborate res elaborated G program c values checked
  have memory := forwarding_chain_sound res elaborated G program c values ds checked chain
  intro F contract d ps rs signature declared vs H n
  have member : d ∈ values ∨ d ∈ ds :=
    of_decide_eq_true ((List.all_eq_true.mp coverage) d declared)
  rcases member with value | prior
  · exact ⟨callInternal_callFrag_ns old F contract n d signature value vs,
      (Preservation.fragMemAt old n).call F contract d signature value vs H⟩
  · exact memory F contract d signature prior vs H n

theorem forwarding_chain_composition (res : Resolution)
    (elaborated : (Source.elaborate res).isSome = true) (G : Glob res.env)
    (program : G.prog = Source.progOf res.env) (c : String) (values ds : List Decl)
    (checked : WholeProgram.check res G c values = true)
    (chain : ForwardingChain res G c values ds)
    (coverage : readyCoverage res values ds = true) (n : Nat) :
    CompositionAt (fun d => d ∈ values) G c (WholeProgram.functions res) n :=
  composition_at (WholeProgram.from_elaborate res elaborated G program c values checked)
    (forwarding_chain_program_calls res elaborated G program c values ds checked chain coverage) n

theorem ForwardingChain.declared {res : Resolution} {G : Glob res.env} {c : String}
    {values ds : List Decl} (chain : ForwardingChain res G c values ds)
    (checked : WholeProgram.check res G c values = true) :
    ∀ d ∈ ds, d ∈ res.env.decls := by
  have environment : res.env.decls = res.unit.decls := by
    have certificate := checked
    simp only [WholeProgram.check,Bool.and_eq_true,decide_eq_true_eq] at certificate
    exact certificate.1
  induction chain with
  | ready catalogue => intro d member; exact (catalogue d member).1
  | extend earlier d ps τ declared fresh signature e same plain defaults expression body ih =>
    intro called member
    rcases List.mem_cons.mp member with same | prior
    · subst called
      rw [environment]
      exact (List.mem_filter.mp declared).1
    · exact ih called prior

#print axioms forwarding_chain_sound
#print axioms forwarding_chain_program_calls
#print axioms forwarding_chain_composition
#print axioms ForwardingChain.declared
end Solidity.Source.Progress
