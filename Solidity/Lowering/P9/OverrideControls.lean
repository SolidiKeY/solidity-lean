import Solidity.Lowering.P9.FunctionCatalog
import Solidity.Lowering.P9.InferenceCuts
import Solidity.Lowering.P9.CallControls

/-! A source-admitted inherited override: the called base declaration differs
from the dispatched derived declaration. Both bodies and the complete catalogue
come from the actual elaborator. -/
namespace Solidity.Lowering.P9.OverrideControls
open Source

def fn (value virtual : Bool) (override : Option (List IdPath)) : Syn (.part false) :=
  .function (.ident "truth") .nil (some .internal) none .nil virtual override
    (.cons (.param (.elem .bool) none none) .nil)
    (.some (.block (.cons (.stmtItem (.returnStmt (.some (.lit (.bool value))))) .nil)))
def baseFunction := fn false true none
def derivedFunction := fn true false (some [])
def unit : Syn .unit := .unit
  (.cons (.contract false "Base" .none .nil (.cons baseFunction .nil))
  (.cons (.contract false "Derived" .none (.cons (.inherit ⟨"Base", []⟩ .none) .nil)
    (.cons derivedFunction .nil)) .nil))
def resolution := Source.resolveUnit {pipeline := .legacy} unit
def baseDecl : Decl := ⟨.function, "truth", some "Base", false, baseFunction⟩
def derivedDecl : Decl := ⟨.function, "truth", some "Derived", false, derivedFunction⟩

def baseFrame := (baseDecl.frame? resolution.env).get (by rfl)
def baseInferred := (ItemsD.infer (baseFrame.ctx resolution.env baseDecl.scope) baseFrame.locals baseFrame.body).get (by rfl)
theorem base_frame : baseDecl.frame? resolution.env = some baseFrame := rfl
theorem base_inferred : ItemsD.infer (baseFrame.ctx resolution.env baseDecl.scope) baseFrame.locals baseFrame.body = some baseInferred := rfl
theorem base_invs : baseDecl.modInvs.invList = [] := by rw [show baseDecl.modInvs = .nil from rfl, Syn.invList]
theorem base_exists : (Source.elabBody resolution.env baseDecl).isSome = true :=
  InferenceCuts.body_some _ _ _ base_frame (by rw [base_inferred]; rfl) base_invs
def baseBody := RBody.ofDerivation baseFrame baseInferred.2 []
theorem base_body : (Source.progOf resolution.env).body baseDecl = some baseBody := by
  have hm : (Source.elabMods resolution.env baseDecl baseFrame baseDecl.modInvs.invList).map Subtype.val = some [] := by rw [base_invs, Source.elabMods]; rfl
  simp only [Source.progOf, Source.elabBody, base_frame, base_inferred]
  cases he : Source.elabMods resolution.env baseDecl baseFrame baseDecl.modInvs.invList with
  | none => rw [he] at hm; cases hm
  | some v => rcases v with ⟨ms, hms⟩; simp only [he, Option.map_some, Option.some.injEq] at hm; subst ms; rfl
theorem base_sig : baseDecl.fnSig resolution.env = some ([], [.bool]) := rfl

def derivedFrame := (derivedDecl.frame? resolution.env).get (by rfl)
def derivedInferred := (ItemsD.infer (derivedFrame.ctx resolution.env derivedDecl.scope) derivedFrame.locals derivedFrame.body).get (by rfl)
theorem derived_frame : derivedDecl.frame? resolution.env = some derivedFrame := rfl
theorem derived_inferred : ItemsD.infer (derivedFrame.ctx resolution.env derivedDecl.scope) derivedFrame.locals derivedFrame.body = some derivedInferred := rfl
theorem derived_invs : derivedDecl.modInvs.invList = [] := by rw [show derivedDecl.modInvs = .nil from rfl, Syn.invList]
theorem derived_exists : (Source.elabBody resolution.env derivedDecl).isSome = true :=
  InferenceCuts.body_some _ _ _ derived_frame (by rw [derived_inferred]; rfl) derived_invs
def derivedBody := RBody.ofDerivation derivedFrame derivedInferred.2 []
theorem derived_body : (Source.progOf resolution.env).body derivedDecl = some derivedBody := by
  have hm : (Source.elabMods resolution.env derivedDecl derivedFrame derivedDecl.modInvs.invList).map Subtype.val = some [] := by rw [derived_invs, Source.elabMods]; rfl
  simp only [Source.progOf, Source.elabBody, derived_frame, derived_inferred]
  cases he : Source.elabMods resolution.env derivedDecl derivedFrame derivedDecl.modInvs.invList with
  | none => rw [he] at hm; cases hm
  | some v => rcases v with ⟨ms, hms⟩; simp only [he, Option.map_some, Option.some.injEq] at hm; subst ms; rfl
theorem derived_sig : derivedDecl.fnSig resolution.env = some ([], [.bool]) := rfl

theorem base_arguments : (Source.elabBaseArgs resolution.env "Base").isSome = true :=
  InferenceCuts.base_some _ _ (by rw [show resolution.env.inheritOf "Base" = .nil from rfl, Syn.inheritList]) rfl
theorem derived_arguments : (Source.elabBaseArgs resolution.env "Derived").isSome = true := by
  have hi : (Source.elabInherit resolution.env "Derived"
      (resolution.env.inheritOf "Derived").inheritList).isSome = true := by
    rw [show resolution.env.inheritOf "Derived" = .cons (.inherit ⟨"Base", []⟩ .none) .nil from rfl,
      Syn.inheritList, Syn.inheritList]
    rfl
  have hc : resolution.env.ctorDecl "Derived" = none := rfl
  unfold Source.elabBaseArgs
  cases he : Source.elabInherit resolution.env "Derived" (resolution.env.inheritOf "Derived").inheritList with
  | none => rw [he] at hi; cases hi
  | some value =>
    rcases value with ⟨xs, hxs⟩
    dsimp only [Bind.bind, Option.bind]
    split
    next he => rfl
    next d he => rw [he] at hc; cases hc


theorem elaborates_eq : Source.elaborates resolution.env = true := by
  change (((true && ((Source.elabBody resolution.env baseDecl).isSome &&
    (true && ((Source.elabBody resolution.env derivedDecl).isSome && true)))) && true) &&
    ((Source.elabBaseArgs resolution.env "Base").isSome &&
      ((Source.elabBaseArgs resolution.env "Derived").isSome && true))) = true
  rw [base_exists, derived_exists, base_arguments, derived_arguments]
  rfl

theorem actual_elaboration : (Source.elaborate resolution).isSome = true := by
  simp only [Source.elaborate, elaborates_eq, ↓reduceIte, Option.isSome_some]

def glob (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) : Glob resolution.env :=
  ⟨Source.progOf resolution.env, p, fixed, fun _ => ⟨0, by decide⟩,
    fun _ _ => true, fun _ => .answer (.success []), ⟨0, by decide⟩⟩
def frame : Fr := {Solidity.Lowering.P9.caller with contract := "Derived"}

theorem base_bases : resolution.env.bases "Base" = [] := by
  change (Source.inheritPaths (.nil : Syn (.list .inherit))).map
    (fun p => p.tail.getLast?.getD p.head) = []
  rw [Source.inheritPaths]
  · rfl
  · intro c x xs hc hh; cases Cat.list.inj hc; cases hh
  · intro p a hc _; cases hc

theorem derived_bases : resolution.env.bases "Derived" = ["Base"] := by
  change (Source.inheritPaths (.cons (.inherit ⟨"Base", []⟩ .none) .nil : Syn (.list .inherit))).map
    (fun p => p.tail.getLast?.getD p.head) = ["Base"]
  simp only [Source.inheritPaths, List.append_nil, List.map_cons, List.map_nil]
  rfl

theorem linearize_eq : resolution.env.linearize "Derived" = some ["Derived", "Base"] := by
  have hb : resolution.env.linearizeF 4 "Base" = some ["Base"] := by
    rw [Env.linearizeF, base_bases]
    rfl
  change resolution.env.linearizeF 5 "Derived" = _
  rw [Env.linearizeF, derived_bases]
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append,
    List.mapM_cons, hb, List.mapM_nil]
  rfl

theorem fn_in : resolution.env.fnIn "Derived" "truth" [] = [derivedDecl] := rfl

theorem selected_override (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    (glob p fixed).dispatchFn "Derived" baseDecl = derivedDecl := by
  unfold Glob.dispatchFn
  rw [base_sig, linearize_eq]
  have h : (baseDecl.scope.isSome && ["Derived", "Base"].any (fun x => some x == baseDecl.scope)) = true := by decide
  simp only [Option.getD_some]
  rw [h]
  simp only [↓reduceIte, List.findSome?_cons, show baseDecl.name = "truth" from rfl, fn_in, List.find?_cons,
    show (glob p fixed).prog.body derivedDecl = some derivedBody from derived_body,
    Option.isSome_some, Option.getD_some]

theorem dispatch_differs (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    (glob p fixed).dispatchFn "Derived" baseDecl ≠ baseDecl := by
  rw [selected_override]
  intro h
  have hs := congrArg Decl.scope h
  exact (by decide : (some "Derived" : Option String) ≠ some "Base") hs

theorem derived_dispatch (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    (glob p fixed).dispatchFn "Derived" derivedDecl = derivedDecl := by
  unfold Glob.dispatchFn
  rw [derived_sig, linearize_eq]
  have h : (derivedDecl.scope.isSome && ["Derived", "Base"].any (fun x => some x == derivedDecl.scope)) = true := by decide
  simp only [Option.getD_some]
  rw [h]
  simp only [↓reduceIte, List.findSome?_cons, show derivedDecl.name = "truth" from rfl, fn_in, List.find?_cons,
    show (glob p fixed).prog.body derivedDecl = some derivedBody from derived_body,
    Option.isSome_some, Option.getD_some]

theorem catalogue : WholeProgram.functions resolution = [baseDecl, derivedDecl] := rfl

theorem base_checked (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    WholeProgram.checkBody resolution (glob p fixed) "Derived" [baseDecl, derivedDecl] baseDecl = true := by
  simp only [WholeProgram.checkBody, base_sig, selected_override, derived_sig,
    show (glob p fixed).prog.body derivedDecl = some derivedBody from derived_body]
  rfl

theorem derived_checked (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    WholeProgram.checkBody resolution (glob p fixed) "Derived" [baseDecl, derivedDecl] derivedDecl = true := by
  simp only [WholeProgram.checkBody, derived_sig, derived_dispatch,
    show (glob p fixed).prog.body derivedDecl = some derivedBody from derived_body]
  rfl

theorem checker_accepts (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    WholeProgram.checkFunctions resolution (glob p fixed) "Derived" = true := by
  unfold WholeProgram.checkFunctions
  rw [catalogue]
  simp only [WholeProgram.check, List.all_cons, List.all_nil, Bool.and_true,
    Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨rfl, ⟨by decide, base_checked p fixed⟩, ⟨by decide, derived_checked p fixed⟩⟩

theorem derived_callsOK (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    CallsOK (fun d => d ∈ WholeProgram.functions resolution) (glob p fixed) "Derived" :=
  WholeProgram.functions_from_elaborate _ actual_elaboration _ rfl _ (checker_accepts p fixed)

def call : RExpr resolution.env [.bool] .bool := .call baseDecl base_sig .nil

theorem call_progress (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) (n : Nat) :
    NS (evalE (glob p fixed) frame n call) :=
  Source.evalE_callFrag_ns (derived_callsOK p fixed) frame rfl n call
    ⟨by rw [catalogue]; exact List.mem_cons_self, trivial⟩ trivial

theorem calls_override (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) (s : St resolution.env) :
    (evalE (glob p fixed) frame 12 call).run (.cons (.bool false) .nil, s) =
      (.ok (.val (.bool true)), (.cons (.bool false) .nil, s)) := by
  have hi : (callInternal (glob p fixed) frame 11 baseDecl (ps := []) .nil [.bool]).run (.nil, s) =
      (.ok (.val (.bool true)), (.nil, s)) := by
    rw [Source.callInternal, show frame.contract = "Derived" from rfl, selected_override,
      show (glob p fixed).prog.body derivedDecl = some derivedBody from derived_body]
    rfl
  unfold call
  rw [Source.evalE]
  simp only [Source.evalConvArgs, pure_bind]
  unfold Source.EM.sub
  dsimp only [Bind.bind, Pure.pure, ExceptT.run, ExceptT.mk, ExceptT.bind, ExceptT.bindCont,
    ExceptT.pure, StateT.bind, StateT.pure]
  dsimp only [ExceptT.run] at hi
  rw [hi]
  rfl

theorem not_base_result (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) (s : St resolution.env) :
    (evalE (glob p fixed) frame 12 call).run (.cons (.bool false) .nil, s) ≠
      (.ok (.val (.bool false)), (.cons (.bool false) .nil, s)) := by
  rw [calls_override]
  intro h
  cases h

#print axioms actual_elaboration
#print axioms dispatch_differs
#print axioms checker_accepts
#print axioms call_progress
#print axioms calls_override
end Solidity.Lowering.P9.OverrideControls
