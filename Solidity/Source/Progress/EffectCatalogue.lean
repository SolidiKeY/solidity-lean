import Solidity.Source.Progress.EffectBodies

/-! A finite declaration-order certificate for nonrecursive effect bodies.
Each head may call only its certified tail. Actual elaboration supplies the
frame and signature facts; admission stores syntax checks, not progress.
The original recursive value-fragment checker and CallsOK remain unchanged. -/
namespace Solidity.Source.Progress
open EM
open Solidity.Lowering.P9
variable {E : Env}

def CallProgress (A : Decl → Prop) (G : Glob E) (c : String) : Prop :=
  ∀ F, F.contract = c → ∀ n, CallNS A G F n

theorem effect_expr_context {A : Decl → Prop} {G : Glob E} {c : String}
    (calls : CallProgress A G c) (F : Fr) (hc : F.contract = c) : ∀ n, ExprNSAt A G F n
  | 0 => exprNSAt_zero A G F
  | n+1 => exprNSAt_step (effect_expr_context calls F hc n) (calls F hc n)

theorem effect_stmt_context {A : Decl → Prop} {G : Glob E} {c : String}
    (calls : CallProgress A G c) : ∀ n, StmtNSAt G A (· = c) n
  | 0 => stmtNSAt_zero G A _
  | n+1 => stmtNSAt_step (effect_stmt_context calls n) (fun F hc => effect_expr_context calls F hc n)

theorem effect_body_ns {A : Decl → Prop} {G : Glob E} {c : String}
    (calls : CallProgress A G c) (F : Fr) (hc : F.contract = c)
    (b : RBody E) (admitted : EffectItems A b.items) (l : Locals E.layout b.locals)
    (frame : BodyFrame b.ps.length b.rs b.locals) : ∀ n, NS (runMods G F n b [] l)
  | 0 => by rw [runMods.eq_1]; exact NS.halt' (fun _ h => by cases h)
  | n+1 => by
    rw [runMods]
    obtain ⟨ys,extent⟩ := RItems.ext b.items
    refine NSP.ns (NSP.bind (R := fun _ => True)
      (effect_items_ns (fun k F hc => effect_expr_context calls F hc k)
        (effect_stmt_context calls) F hc b.ps.length none n b.items admitted l frame) (fun o noEscape => ?_))
    cases o with
    | normal l' => exact NSP.of_ns (NS.lift' (Locals.restore_ok' ys extent l'))
    | ret l' => exact NSP.pure' trivial
    | brk _ => exact nomatch noEscape
    | cont _ => exact nomatch noEscape

/-- Consume actual source call/default/body/return operations. The body
progress is derived from syntactic effect membership and smaller callees. -/
theorem effect_call_ns {A : Decl → Prop} {G : Glob E} {c : String}
    (calls : CallProgress A G c) (F : Fr) (hc : F.contract = c) (d : Decl)
    {ps : List STy} (vs : Vals E.layout ps) (rs : List STy) (b : RBody E)
    (body : G.prog.body (G.dispatchFn F.contract d) = some b)
    (locals : rs.reverseAux (ps.reverseAux []) = b.locals) (returns : b.rs = rs)
    (parameters : b.ps.length = ps.length) (mods : b.mods = [])
    (defaults : ∀ τ ∈ rs, (Val.default E.layout τ).isSome = true)
    (admitted : EffectItems A b.items) : ∀ n, NS (callInternal G F n d vs rs)
  | 0 => by rw [callInternal.eq_1]; exact NS.halt' (fun _ h => by cases h)
  | n+1 => by
    have layout : b.locals = rs.reverse ++ ps.reverse := by
      rw [← locals,List.reverseAux_eq,List.reverseAux_eq,List.append_nil]
    simp only [callInternal,body]
    refine NS.bind (zeroVals_ns n rs defaults) (fun rv => ?_)
    rw [dif_pos locals,mods]
    refine NS.bind (effect_body_ns calls {F with checked := true} hc b admitted _
      ⟨[],ps.reverse,?_,?_⟩ n) (fun l' => ?_)
    · rw [layout,returns,List.nil_append]
    · rw [List.length_reverse,parameters]
    · exact NS.bind (NS.lift' (Source.retVals_ok l' rs (layout.trans rfl))) (fun _ => NS.pure' _)

/-- Every listed function has its actual selected body, and that body's
syntax calls only the certified suffix. There is no semantic NS premise. -/
inductive EffectCatalogue (G : Glob E) (c : String) : List Decl → Prop
  | nil : EffectCatalogue G c []
  | cons {d : Decl} {ds : List Decl} {ps rs targetPs : List STy} {b : RBody E} :
      EffectCatalogue G c ds → d ∈ E.decls → d.fnSig E = some (ps,rs) →
      (G.dispatchFn c d).fnSig E = some (targetPs,rs) →
      G.prog.body (G.dispatchFn c d) = some b → b.mods = [] →
      (∀ τ ∈ rs, (Val.default E.layout τ).isSome = true) →
      EffectItems (fun d => d ∈ ds) b.items → EffectCatalogue G c (d :: ds)

/-- Actual elaboration supplies dispatch membership, body typing, signature
coherence and frame layout; a finite syntactic catalogue derives call progress. -/
theorem effect_catalogue_progress (el : Elaborated) (G : Glob el.res.env)
    (program : G.prog = el.prog) (environment : el.res.env.decls = el.res.unit.decls)
    (c : String) {ds : List Decl} (admission : EffectCatalogue G c ds) :
    CallProgress (fun d => d ∈ ds) G c := by
  induction admission with
  | nil =>
    intro F hc n d ps rs signature member vs
    cases member
  | @cons d ds ps rs targetPs b tail declared signature selected body mods defaults fragment ih =>
    intro F hc n called inputs outputs callSignature member vs
    rcases List.mem_cons.mp member with same | inTail
    · subst called
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj (signature.symm.trans callSignature))
      have targetMember : G.dispatchFn c d ∈ el.res.unit.decls := by
        rw [← environment]
        exact WholeProgram.dispatch_mem G c d el.res.env.decls rfl declared
      have actualBody : el.prog.body (G.dispatchFn c d) = some b := by rw [← program]; exact body
      obtain ⟨parameterTypes,returnTypes⟩ := el.body_sig targetMember actualBody selected
      have sameParameters := G.dispatchFn_params c d signature selected
      have frame : rs.reverseAux (ps.reverseAux []) = b.locals := by
        rw [el.body_locals targetMember actualBody,parameterTypes,returnTypes,sameParameters,
          List.reverseAux_eq,List.reverseAux_eq,List.append_nil]
      exact effect_call_ns ih F hc d vs rs b (by rw [hc]; exact body) frame returnTypes
        (by rw [parameterTypes,sameParameters]) mods defaults fragment n
    · exact ih F hc n called callSignature inTail vs

/-- Transfer the certificate through actual successful elaborate, using the
published dependent program-identity theorem rather than an assumed CallsOK. -/
theorem effect_from_elaborate (res : Resolution) (ha : (Source.elaborate res).isSome = true)
    (G : Glob res.env) (program : G.prog = Source.progOf res.env)
    (environment : res.env.decls = res.unit.decls) (c : String) {ds : List Decl}
    (admission : EffectCatalogue G c ds) : CallProgress (fun d => d ∈ ds) G c := by
  obtain ⟨el,hel⟩ := Option.isSome_iff_exists.mp ha
  obtain ⟨resolution,bodyProgram⟩ := elaborate_program hel
  rcases el with ⟨r,prog,hb,hcs,hm,hct,hco,hi,hba⟩
  dsimp only at resolution bodyProgram
  subst res
  have hp : prog = Source.progOf r.env := eq_of_heq bodyProgram
  subst prog
  exact effect_catalogue_progress ⟨r,Source.progOf r.env,hb,hcs,hm,hct,hco,hi,hba⟩
    G program environment c admission

/-- Complete-catalogue coverage is checked separately; a caller cannot leave
out a source function silently. This admission is nonrecursive and additive. -/
theorem checked_effect_call (res : Resolution) (ha : (Source.elaborate res).isSome = true)
    (G : Glob res.env) (program : G.prog = Source.progOf res.env)
    (environment : res.env.decls = res.unit.decls) (c : String) (ds : List Decl)
    (admission : EffectCatalogue G c ds)
    (complete : (WholeProgram.functions res).all (fun d => decide (d ∈ ds)) = true)
    (F : Fr) (hc : F.contract = c) (n : Nat) (d : Decl) {ps rs : List STy}
    (signature : d.fnSig res.env = some (ps,rs)) (member : d ∈ WholeProgram.functions res)
    (vs : Vals res.env.layout ps) : NS (callInternal G F n d vs rs) := by
  have covered : d ∈ ds := of_decide_eq_true ((List.all_eq_true.mp complete) d member)
  exact effect_from_elaborate res ha G program environment c admission F hc n d signature covered vs

#print axioms effect_call_ns
#print axioms effect_catalogue_progress
#print axioms effect_from_elaborate
#print axioms checked_effect_call
end Solidity.Source.Progress
