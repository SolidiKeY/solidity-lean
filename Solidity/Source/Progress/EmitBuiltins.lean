import Solidity.Source.Progress.CheckedPrograms

/-! Direct builtin/emit progress adapters over the existing checked call
fragment. These lemmas do not change `CallsOK` or silently admit new callee
bodies. Allocation-sensitive byte arguments require a separate invariant.
-/
namespace Solidity.Source.Progress
open EM
variable {E : Env} {Γ : RCtx}

/-- Elementary event parameters really have ABI words. -/
theorem encodeOne_key_ns (F : Fr) (n : Nat) (packed : Bool) {t : STy}
    (ht : t.keyable = true) (v : Val E.layout t) :
    NS (encodeOne (Γ := Γ) F n packed (.val v)) := by
  have hw := Val.word_isSome ht v
  cases t <;> (try (cases ht <;> done)) <;>
    simp only [encodeOne] <;>
    split <;> first
      | (cases packed <;> exact NS.pure' _)
      | rename_i h; rw [h] at hw; cases hw

/-- Event arguments in the elementary ABI fragment. -/
theorem encodeVals_key_ns (F : Fr) (n : Nat) (packed : Bool)
    {ts : List STy} (ht : ts.all STy.keyable = true) (vs : Vals E.layout ts) :
    NS (encodeVals (Γ := Γ) F n packed vs.toR) := by
  have parts : NS (encodeParts (Γ := Γ) F n packed vs.toR) := by
    induction vs with
    | nil => exact NS.pure' _
    | cons v vs ih =>
      simp only [List.all_cons, Bool.and_eq_true] at ht
      exact NS.bind (encodeOne_key_ns F n packed ht.1 v) fun _ =>
        NS.bind (ih ht.2) fun _ => NS.pure' _
  exact NS.bind parts fun _ => by cases packed <;> exact NS.pure' _

theorem evalBuiltin_require_ns (G : Glob E) (F : Fr) (n : Nat)
    (args : RArgs E Γ [.bool]) (ha : NS (evalArgs G F n args)) :
    NS (evalBuiltin G F (n + 1) .require args (.tuple [])) := by
  simp only [evalBuiltin]
  refine NS.bind ha fun vs => ?_
  cases vs with
  | cons c rest =>
    cases rest
    cases c with
    | val c =>
      obtain ⟨b, rfl⟩ := Val.eq_bool c
      cases b <;> first
        | exact NS.pure' _
        | exact NS.halt' fun _ h => by cases h

theorem evalBuiltin_assert_ns (G : Glob E) (F : Fr) (n : Nat)
    (args : RArgs E Γ [.bool]) (ha : NS (evalArgs G F n args)) :
    NS (evalBuiltin G F (n + 1) .assert args (.tuple [])) := by
  simp only [evalBuiltin]
  refine NS.bind ha fun vs => ?_
  cases vs with
  | cons c rest =>
    cases rest
    cases c with
    | val c =>
      obtain ⟨b, rfl⟩ := Val.eq_bool c
      cases b <;> first
        | exact NS.pure' _
        | (change NS (lift (panic .assert)); exact NS.lift' (by intro w h; cases h))

theorem evalBuiltin_revert_ns (G : Glob E) (F : Fr) (n : Nat)
    (args : RArgs E Γ []) (ha : NS (evalArgs G F n args)) :
    NS (evalBuiltin G F (n + 1) .revert args (.tuple [])) := by
  simp only [evalBuiltin]
  refine NS.bind ha fun vs => ?_
  cases vs
  exact NS.halt' fun _ h => by cases h

/-- Direct emit progress: argument progress and elementary ABI parameters.
The static-frame revert remains an allowed non-stuck outcome. -/
theorem execS_emit_ns (G : Glob E) (F : Fr) (n nps : Nat) (ph : Option (Ph E))
    {R : List STy} {M : Bool} {k : SCtx} {ps : List STy}
    (ev : Decl) (he : ev.paramTys E = some ps) (args : RConvArgs E Γ ps)
    (l : Locals E.layout Γ) (hp : ps.all STy.keyable = true)
    (ha : NS (evalConvArgs G F n args)) :
    NS (execS G F (n + 1) nps ph (.emit (R := R) (M := M) (k := k) ev he args) l) := by
  simp only [execS]
  refine NS.bind (NSP.ns (NSP.sub' (Q := fun _ => True)
    (NSP.weaken (NSP.of_ns ha) fun _ _ _ => trivial))) fun p => ?_
  refine NS.bind (encodeVals_key_ns F n false hp p.1) fun data => ?_
  split
  · exact NS.halt' fun _ h => by cases h
  · exact NS.bind (NS.modSt' (fun s => {s with logs := (F.this, G.selector (sigOf E.layout ev.name ps) ++ data) :: s.logs})) fun _ => NS.pure' _

/-- Reuse the same whole-program checker for event argument calls. The
new direct emit node is not inserted into the old body admission. -/
theorem checked_emit (res : Resolution) (G : Glob res.env) (c : String)
    (ha : (Source.elaborate res).isSome = true) (hg : G.prog = Source.progOf res.env)
    (hc : Solidity.Lowering.P9.WholeProgram.checkFunctions res G c = true)
    (F : Fr) (hF : F.contract = c) (n nps : Nat) (ph : Option (Ph res.env))
    {R : List STy} {M : Bool} {k : SCtx} {Γ : RCtx} {ps : List STy}
    (ev : Decl) (he : ev.paramTys res.env = some ps) (args : RConvArgs res.env Γ ps)
    (l : Locals res.env.layout Γ) (hp : ps.all STy.keyable = true)
    (hf : args.ValFragC (fun d => d ∈ Solidity.Lowering.P9.WholeProgram.functions res))
    (ho : args.OpsOK) :
    NS (execS G F (n + 1) nps ph (.emit (R := R) (M := M) (k := k) ev he args) l) :=
  execS_emit_ns G F n nps ph ev he args l hp
    ((checked_fragments ha hg hc n).1.expr F hF |>.convArgs args hf ho)

#print axioms encodeVals_key_ns
#print axioms checked_emit
#print axioms evalBuiltin_require_ns
#print axioms evalBuiltin_assert_ns
#print axioms evalBuiltin_revert_ns
end Solidity.Source.Progress
