import Solidity.Lowering.P9.ProgramAdmission
import Solidity.Lowering.P9.InferenceCuts
import Solidity.Lowering.P9.AdmissionControls

/-! Two actual source functions: leaf returns true; entry calls leaf.
The closure check refuses entry alone. All bodies come from actual inference.
-/
namespace Solidity.Lowering.P9.GraphControls
open Source Roadmap

def fn (name : String) (e : Source.Syn .expr) : Source.Syn (.part true) :=
  .function (.ident name) .nil none none .nil false none
    (.cons (.param (.elem .bool) none none) .nil)
    (.some (.block (.cons (.stmtItem (.returnStmt (.some e))) .nil)))
def leafFunction := fn "leaf" (.lit (.bool true))
def entryFunction := fn "entry" (.call (.ident "leaf") (.positional .nil))
def unit : Source.Syn .unit := .unit (.cons (.topPart leafFunction) (.cons (.topPart entryFunction) .nil))
def resolution := Source.resolveUnit {pipeline := .legacy} unit
def leafDecl : Source.Decl := ⟨.function, "leaf", none, true, leafFunction⟩
def entryDecl : Source.Decl := ⟨.function, "entry", none, true, entryFunction⟩
def leafFrame := (leafDecl.frame? resolution.env).get (by rfl)
def entryFrame := (entryDecl.frame? resolution.env).get (by rfl)
def leafInferred := (Source.ItemsD.infer (leafFrame.ctx resolution.env leafDecl.scope) leafFrame.locals leafFrame.body).get (by rfl)
def entryInferred := (Source.ItemsD.infer (entryFrame.ctx resolution.env entryDecl.scope) entryFrame.locals entryFrame.body).get (by rfl)
theorem leaf_frame : leafDecl.frame? resolution.env = some leafFrame := rfl
theorem entry_frame : entryDecl.frame? resolution.env = some entryFrame := rfl
theorem leaf_inferred : Source.ItemsD.infer (leafFrame.ctx resolution.env leafDecl.scope) leafFrame.locals leafFrame.body = some leafInferred := rfl
theorem entry_inferred : Source.ItemsD.infer (entryFrame.ctx resolution.env entryDecl.scope) entryFrame.locals entryFrame.body = some entryInferred := rfl
theorem leaf_invs : leafDecl.modInvs.invList = [] := by rw [show leafDecl.modInvs = .nil from rfl, Source.Syn.invList]
theorem entry_invs : entryDecl.modInvs.invList = [] := by rw [show entryDecl.modInvs = .nil from rfl, Source.Syn.invList]
theorem leaf_exists : (Source.elabBody resolution.env leafDecl).isSome = true :=
  InferenceCuts.body_some _ _ _ leaf_frame (by rw [leaf_inferred]; rfl) leaf_invs
theorem entry_exists : (Source.elabBody resolution.env entryDecl).isSome = true :=
  InferenceCuts.body_some _ _ _ entry_frame (by rw [entry_inferred]; rfl) entry_invs

theorem elaborates_eq : Source.elaborates resolution.env = true := by
  change (((((Source.elabBody resolution.env leafDecl).isSome &&
    ((Source.elabBody resolution.env entryDecl).isSome && true)) && true) && true)) = true
  rw [leaf_exists, entry_exists]
  rfl

theorem actual_elaboration : (Source.elaborate resolution).isSome = true := by
  simp only [Source.elaborate, elaborates_eq, ↓reduceIte, Option.isSome_some]

def leafBody := Source.RBody.ofDerivation leafFrame leafInferred.2 []
def entryBody := Source.RBody.ofDerivation entryFrame entryInferred.2 []

theorem leaf_body : (Source.progOf resolution.env).body leafDecl = some leafBody := by
  have hm : (Source.elabMods resolution.env leafDecl leafFrame leafDecl.modInvs.invList).map Subtype.val = some [] := by rw [leaf_invs, Source.elabMods]; rfl
  simp only [Source.progOf, Source.elabBody, leaf_frame, leaf_inferred]
  cases he : Source.elabMods resolution.env leafDecl leafFrame leafDecl.modInvs.invList with
  | none => rw [he] at hm; cases hm
  | some v => rcases v with ⟨ms, hms⟩; simp only [he, Option.map_some, Option.some.injEq] at hm; subst ms; rfl

theorem entry_body : (Source.progOf resolution.env).body entryDecl = some entryBody := by
  have hm : (Source.elabMods resolution.env entryDecl entryFrame entryDecl.modInvs.invList).map Subtype.val = some [] := by rw [entry_invs, Source.elabMods]; rfl
  simp only [Source.progOf, Source.elabBody, entry_frame, entry_inferred]
  cases he : Source.elabMods resolution.env entryDecl entryFrame entryDecl.modInvs.invList with
  | none => rw [he] at hm; cases hm
  | some v => rcases v with ⟨ms, hms⟩; simp only [he, Option.map_some, Option.some.injEq] at hm; subst ms; rfl

def glob (fixed : Roadmap.Fixed) : Source.Glob resolution.env :=
  ⟨Source.progOf resolution.env, .legacy, fixed, fun _ => ⟨0, by decide⟩,
    fun _ _ => true, fun _ => .answer (.success []), ⟨0, by decide⟩⟩
theorem leaf_sig : leafDecl.fnSig resolution.env = some ([], [.bool]) := rfl
theorem entry_sig : entryDecl.fnSig resolution.env = some ([], [.bool]) := rfl

theorem leaf_dispatch (fixed : Roadmap.Fixed) : (glob fixed).dispatchFn "P9" leafDecl = leafDecl := by unfold Source.Glob.dispatchFn; rw [leaf_sig]; rfl
theorem entry_dispatch (fixed : Roadmap.Fixed) : (glob fixed).dispatchFn "P9" entryDecl = entryDecl := by unfold Source.Glob.dispatchFn; rw [entry_sig]; rfl

theorem leaf_checked (fixed : Roadmap.Fixed) : WholeProgram.checkBody resolution (glob fixed) "P9" [leafDecl, entryDecl] leafDecl = true := by
  have hb : (glob fixed).prog.body leafDecl = some leafBody := leaf_body
  simp only [WholeProgram.checkBody, leaf_sig, leaf_dispatch, hb]
  rfl

theorem entry_checked (fixed : Roadmap.Fixed) : WholeProgram.checkBody resolution (glob fixed) "P9" [leafDecl, entryDecl] entryDecl = true := by
  have hb : (glob fixed).prog.body entryDecl = some entryBody := entry_body
  simp only [WholeProgram.checkBody, entry_sig, entry_dispatch, hb]
  rfl

theorem checker_accepts (fixed : Roadmap.Fixed) : WholeProgram.check resolution (glob fixed) "P9" [leafDecl, entryDecl] = true := by
  simp only [WholeProgram.check, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨rfl, ⟨List.mem_cons_self, leaf_checked fixed⟩, ⟨?_, entry_checked fixed⟩⟩
  exact List.mem_cons_of_mem _ (List.mem_singleton.mpr rfl)

theorem omitted_callee_refused (fixed : Roadmap.Fixed) : WholeProgram.check resolution (glob fixed) "P9" [entryDecl] = false := by
  have hb : (glob fixed).prog.body entryDecl = some entryBody := entry_body
  simp only [WholeProgram.check, List.all_cons, List.all_nil, Bool.and_true,
    WholeProgram.checkBody, entry_sig, entry_dispatch, hb]
  rfl

theorem derived_callsOK (fixed : Roadmap.Fixed) : Source.CallsOK (fun d => d ∈ [leafDecl, entryDecl]) (glob fixed) "P9" :=
  WholeProgram.from_elaborate resolution actual_elaboration (glob fixed) rfl "P9" _ (checker_accepts fixed)

def call : Source.RExpr resolution.env [.bool] .bool := .call entryDecl entry_sig .nil

theorem graph_not_stuck (fixed : Roadmap.Fixed) (n : Nat) : Source.NS (Source.evalE (glob fixed) Solidity.Lowering.P9.caller n call) :=
  Source.evalE_callFrag_ns (derived_callsOK fixed) Solidity.Lowering.P9.caller rfl n call
    ⟨List.mem_cons_of_mem _ (List.mem_singleton.mpr rfl), trivial⟩ trivial

/-- Shared normal forms are proved equal to both actual inferred bodies. -/
def flatLeaf : Source.RBody resolution.env where
  ps := []; rs := [.bool]; inModifier := false; locals := [.bool]; out := [.bool]
  items := .stmt (.retVal rfl (.bool true) (by rfl)) .nil
  mods := []
def flatEntry : Source.RBody resolution.env where
  ps := []; rs := [.bool]; inModifier := false; locals := [.bool]; out := [.bool]
  items := .stmt (.retVal rfl (.call leafDecl leaf_sig .nil) (by rfl)) .nil
  mods := []
theorem leaf_flat : leafBody = flatLeaf := rfl
theorem entry_flat : entryBody = flatEntry := rfl

def cachedGlob (fixed : Roadmap.Fixed) : Source.Glob resolution.env :=
  {glob fixed with prog := {(glob fixed).prog with
    body := fun d => if d = leafDecl then some flatLeaf else if d = entryDecl then some flatEntry else (glob fixed).prog.body d}}

theorem cachedGlob_eq (fixed : Roadmap.Fixed) : cachedGlob fixed = glob fixed := by
  have hl : (glob fixed).prog.body leafDecl = some flatLeaf := by
    rw [show (glob fixed).prog = Source.progOf resolution.env from rfl, leaf_body, leaf_flat]
  have he : (glob fixed).prog.body entryDecl = some flatEntry := by
    rw [show (glob fixed).prog = Source.progOf resolution.env from rfl, entry_body, entry_flat]
  have hp : (fun d => if d = leafDecl then some flatLeaf else if d = entryDecl then some flatEntry else (glob fixed).prog.body d) =
      (glob fixed).prog.body := by
    funext d
    split
    next h => subst d; exact hl.symm
    next h =>
      split
      next h => subst d; exact he.symm
      next h => rfl
  unfold cachedGlob
  rw [hp]

/-- Both bodies are actually executed; the complete caller and state survive. -/
theorem graph_success (fixed : Roadmap.Fixed) (s : Source.St resolution.env) :
    (Source.evalE (glob fixed) Solidity.Lowering.P9.caller 12 call).run (.cons (.bool false) .nil, s) =
      (.ok (.val (.bool true)), (.cons (.bool false) .nil, s)) := by
  rw [← cachedGlob_eq fixed]
  rfl

theorem graph_wrong_result (fixed : Roadmap.Fixed) (s : Source.St resolution.env) :
    (Source.evalE (glob fixed) Solidity.Lowering.P9.caller 12 call).run (.cons (.bool false) .nil, s) ≠
      (.ok (.val (.bool false)), (.cons (.bool false) .nil, s)) := by
  rw [graph_success]
  intro h
  cases h

#print axioms actual_elaboration
#print axioms checker_accepts
#print axioms omitted_callee_refused
#print axioms derived_callsOK
#print axioms graph_not_stuck
#print axioms graph_success
#print axioms graph_wrong_result
end Solidity.Lowering.P9.GraphControls
