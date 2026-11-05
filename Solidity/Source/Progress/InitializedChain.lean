import Solidity.Source.Progress.InitializedCalls
import Solidity.Source.Progress.ForwardingChain

/-! Finite initialized-return extensions of an existing forwarding chain.
The earlier certificates are reused unchanged. Each added declaration has a
syntax certificate, source provenance and an exact selected body; a separate
coverage check yields the complete source-function call interface. -/
namespace Solidity.Source.Progress
open EM Solidity.Lowering.P9

inductive InitializedChain (res : Resolution) (G : Glob res.env) (c : String) (values : List Decl) :
    List Decl → Prop
  | forwarding {ds : List Decl} :
      ForwardingChain res G c values ds → InitializedChain res G c values ds
  | extend {ds : List Decl} (earlier : InitializedChain res G c values ds)
      (d : Decl) (ps : List STy) (τ : STy)
      (declared : d ∈ WholeProgram.functions res) (fresh : forwardFresh values ds d = true)
      (signature : d.fnSig res.env = some (ps,[τ]))
      {Δ : RCtx} (items : RItems res.env [τ] false .body (returnContext ps τ) Δ)
      (defaults : ZeroReady res.env τ)
      (fragment : InitializedReturns (fun d => d ∈ values) (fun d => d ∈ ds) τ items)
      (body : G.prog.body (G.dispatchFn c d) = some (initializedBody ps τ items)) :
      InitializedChain res G c values (d :: ds)

theorem initialized_chain_sound (res : Resolution)
    (elaborated : (Source.elaborate res).isSome = true) (G : Glob res.env)
    (program : G.prog = Source.progOf res.env) (c : String) (values ds : List Decl)
    (checked : WholeProgram.check res G c values = true)
    (chain : InitializedChain res G c values ds) : ReadyMemoryCalls G c ds := by
  induction chain with
  | forwarding earlier =>
    exact forwarding_chain_sound res elaborated G program c values _ checked earlier
  | extend earlier d ps τ declared fresh signature items defaults fragment body ih =>
    exact extend_initialized_calls
      (WholeProgram.from_elaborate res elaborated G program c values checked) ih
      d ps τ signature items fragment defaults body

theorem initialized_chain_program_calls (res : Resolution)
    (elaborated : (Source.elaborate res).isSome = true) (G : Glob res.env)
    (program : G.prog = Source.progOf res.env) (c : String) (values ds : List Decl)
    (checked : WholeProgram.check res G c values = true)
    (chain : InitializedChain res G c values ds)
    (coverage : readyCoverage res values ds = true) : ReadyProgramCalls res G c := by
  have old := WholeProgram.from_elaborate res elaborated G program c values checked
  have memory := initialized_chain_sound res elaborated G program c values ds checked chain
  intro F contract d ps rs signature declared vs H n
  have member : d ∈ values ∨ d ∈ ds :=
    of_decide_eq_true ((List.all_eq_true.mp coverage) d declared)
  rcases member with value | prior
  · exact ⟨callInternal_callFrag_ns old F contract n d signature value vs,
      (Preservation.fragMemAt old n).call F contract d signature value vs H⟩
  · exact memory F contract d signature prior vs H n

theorem initialized_chain_composition (res : Resolution)
    (elaborated : (Source.elaborate res).isSome = true) (G : Glob res.env)
    (program : G.prog = Source.progOf res.env) (c : String) (values ds : List Decl)
    (checked : WholeProgram.check res G c values = true)
    (chain : InitializedChain res G c values ds)
    (coverage : readyCoverage res values ds = true) (n : Nat) :
    CompositionAt (fun d => d ∈ values) G c (WholeProgram.functions res) n :=
  composition_at (WholeProgram.from_elaborate res elaborated G program c values checked)
    (initialized_chain_program_calls res elaborated G program c values ds checked chain coverage) n

theorem InitializedChain.declared {res : Resolution} {G : Glob res.env} {c : String}
    {values ds : List Decl} (chain : InitializedChain res G c values ds)
    (checked : WholeProgram.check res G c values = true) :
    ∀ d ∈ ds, d ∈ res.env.decls := by
  have environment : res.env.decls = res.unit.decls := by
    have certificate := checked
    simp only [WholeProgram.check,Bool.and_eq_true,decide_eq_true_eq] at certificate
    exact certificate.1
  induction chain with
  | forwarding earlier => exact earlier.declared checked
  | extend earlier d ps τ declared fresh signature items defaults fragment body ih =>
    intro called member
    rcases List.mem_cons.mp member with same | prior
    · subst called
      rw [environment]
      exact (List.mem_filter.mp declared).1
    · exact ih called prior

#print axioms initialized_chain_sound
#print axioms initialized_chain_program_calls
#print axioms initialized_chain_composition
#print axioms InitializedChain.declared
end Solidity.Source.Progress
