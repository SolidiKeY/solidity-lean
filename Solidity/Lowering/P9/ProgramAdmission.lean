import Solidity.Lowering.P9.FragmentDecidable
import Solidity.Lowering.P9.ElaborationAdmission

/-!
# Deriving whole-program internal-call progress (P9)

A finite, closed allowlist is checked against the actual elaborated program.
Frames and operation domains are derived from elaboration; body availability,
selected return signatures, defaults, modifiers and fragment closure are checked.
Recursion is admitted: progress means non-stuckness, not termination.
-/
namespace Solidity.Lowering.P9
open Source
namespace WholeProgram
variable {E : Env}

/-- Dispatch either keeps its declaration or selects one from the environment. -/
theorem dispatch_mem (G : Glob E) (c : String) (d : Decl) (ds : List Decl)
    (henv : E.decls = ds) (hd : d ∈ ds) : G.dispatchFn c d ∈ ds := by
  unfold Glob.dispatchFn
  cases hs : d.fnSig E with
  | none => exact hd
  | some sig =>
    obtain ⟨ps, rs⟩ := sig
    dsimp only
    split
    · cases hf : ((E.linearize c).getD [c]).findSome? (fun s => (E.fnIn s d.name ps).find?
          fun d' => (G.prog.body d').isSome) with
      | none => exact hd
      | some d' =>
        obtain ⟨s, _, hfind⟩ := List.exists_of_findSome?_eq_some hf
        have hm := List.mem_of_find?_eq_some hfind
        unfold Env.fnIn at hm
        have hm' := (List.mem_filter.mp hm).1
        unfold Env.declared at hm'
        have hin := (List.mem_filter.mp hm').1
        rw [henv] at hin
        exact hin
    · exact hd

/-- The local checks at an allowed declaration. No frame or `OpsOK` premise is
accepted from the caller: those facts will come from `Elaborated`. -/
def checkBody (res : Resolution) (G : Glob res.env) (c : String) (allowed : List Decl) (d : Decl) : Bool :=
  match d.fnSig res.env with
  | none => false
  | some (_, rs) =>
    match (G.dispatchFn c d).fnSig res.env, G.prog.body (G.dispatchFn c d) with
    | some (_, rs'), some b =>
      decide (rs' = rs) && (b.mods.isEmpty &&
        (rs.all (fun τ => (Val.default res.env.layout τ).isSome) &&
          decide (b.items.ValFragC (fun d => d ∈ allowed))))
    | _, _ => false

/-- Finite source admission. Environment coherence and allowlist membership
are checked, including at an `Elaborated` manually built from a resolution. -/
def check (res : Resolution) (G : Glob res.env) (c : String) (allowed : List Decl) : Bool :=
  decide (res.env.decls = res.unit.decls) &&
    allowed.all (fun d => decide (d ∈ res.unit.decls) && checkBody res G c allowed d)

/-- **The checked source program derives `CallsOK`.** This is a derivation,
not a new whole-program hypothesis: the sole admission premise is the finite
executable check. Every body is tied to its actual typing derivation. -/
theorem check_sound (el : Elaborated) (G : Glob el.res.env) (hG : G.prog = el.prog)
    (c : String) (allowed : List Decl) (h : check el.res G c allowed = true) :
    CallsOK (fun d => d ∈ allowed) G c := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  intro d ps rs hs hA
  obtain ⟨hd, hbody⟩ := h.2 d hA
  have htmem := dispatch_mem G c d el.res.unit.decls h.1 hd
  unfold checkBody at hbody
  rw [hs] at hbody
  cases ht : (G.dispatchFn c d).fnSig el.res.env with
  | none => simp only [ht] at hbody; cases hbody
  | some sig =>
    obtain ⟨ps', rs'⟩ := sig
    cases hb : G.prog.body (G.dispatchFn c d) with
    | none => simp only [ht, hb] at hbody; cases hbody
    | some b =>
      simp only [ht, hb, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hbody
      obtain ⟨hret, hmods, hz, hf⟩ := hbody
      subst rs'
      have hb' : el.prog.body (G.dispatchFn c d) = some b := by rw [← hG]; exact hb
      obtain ⟨hps, hrs⟩ := el.body_sig htmem hb' ht
      have hparams := Glob.dispatchFn_params G c d hs ht
      have hps' : b.ps = ps := hps.trans hparams
      have hm : b.mods = [] := by
        cases he : b.mods with
        | nil => rfl
        | cons x xs => rw [he] at hmods; cases hmods
      refine ⟨b, rfl, hm, ?_, hrs, ?_, hz, hf, (el.body_opsOK htmem hb').1⟩
      · rw [el.body_locals htmem hb', hps', hrs, List.reverseAux_eq, List.reverseAux_eq, List.append_nil]
      · rw [hps']

/-- All-horizon source-call progress
with typed actual arguments and no assumed `CallsOK`. -/
theorem call_ns (el : Elaborated) (G : Glob el.res.env) (hG : G.prog = el.prog)
    (c : String) (allowed : List Decl) (h : check el.res G c allowed = true)
    (F : Fr) (hc : F.contract = c) (n : Nat) (d : Decl) {ps rs : List STy}
    (hs : d.fnSig el.res.env = some (ps, rs)) (hd : d ∈ allowed)
    (vs : Vals el.res.env.layout ps) : NS (callInternal G F n d vs rs) :=
  callInternal_callFrag_ns (check_sound el G hG c allowed h) F hc n d hs hd vs

/-- Source expressions, including recursive internal calls, use the same
checked program certificate. The fragment and domain premises are unchanged. -/
theorem expr_ns (el : Elaborated) (G : Glob el.res.env) (hG : G.prog = el.prog)
    (c : String) (allowed : List Decl) (h : check el.res G c allowed = true)
    (F : Fr) (hc : F.contract = c) (n : Nat) {Γ : RCtx} {τ : STy}
    (e : RExpr el.res.env Γ τ) (hf : e.ValFragC (fun d => d ∈ allowed)) (ho : e.OpsOK) :
    NS (evalE G F n e) :=
  evalE_callFrag_ns (check_sound el G hG c allowed h) F hc n e hf ho

/-- Consume actual `elaborate` success. Resolution and dependent program
identity are recovered by `ElaborationAdmission`, not assumed. -/
theorem from_elaborate (res : Resolution) (ha : (Source.elaborate res).isSome = true)
    (G : Glob res.env) (hG : G.prog = Source.progOf res.env) (c : String) (allowed : List Decl)
    (hc : check res G c allowed = true) : CallsOK (fun d => d ∈ allowed) G c := by
  obtain ⟨el, hel⟩ := Option.isSome_iff_exists.mp ha
  obtain ⟨hres, hprog⟩ := elaborate_program hel
  rcases el with ⟨r, prog, hb, hcs, hm, hct, hco, hi, hba⟩
  dsimp only at hres hprog
  subst res
  have hp : prog = Source.progOf r.env := eq_of_heq hprog
  subst prog
  exact check_sound ⟨r, Source.progOf r.env, hb, hcs, hm, hct, hco, hi, hba⟩ G hG c allowed hc

end WholeProgram
end Solidity.Lowering.P9
