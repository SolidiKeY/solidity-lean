import Solidity.Lowering.P9.ProgramAdmission
import Solidity.Lowering.P9.InferenceCuts
import Solidity.Lowering.P9.AdmissionControls

/-! Negative elaborator-boundary control: duplicate same-parameter declarations
with distinct return lists are not a valid Solidity overload. The current source
elaborator accepts their bodies; dispatch selects the first (void) declaration.
The checker must refuse the requested Boolean signature. No source-coverage or
Solc-acceptance claim is made for this deliberately invalid source unit.
-/
namespace Solidity.Lowering.P9.ReturnControls
open Source Roadmap

def voidFunction : Source.Syn (.part false) :=
  .function (.ident "same") .nil (some .internal) none .nil false none .nil
    (.some (.block .nil))
def boolFunction : Source.Syn (.part false) :=
  .function (.ident "same") .nil (some .internal) none .nil false none
    (.cons (.param (.elem .bool) none none) .nil)
    (.some (.block (.cons (.stmtItem (.returnStmt (.some (.lit (.bool true))))) .nil)))
def leafFunction := voidFunction
def entryFunction := boolFunction
def unit : Source.Syn .unit := .unit (.cons
  (.contract false "P9" .none .nil (.cons leafFunction (.cons entryFunction .nil))) .nil)
def resolution := Source.resolveUnit {pipeline := .legacy} unit
def leafDecl : Source.Decl := ⟨.function, "same", some "P9", false, leafFunction⟩
def entryDecl : Source.Decl := ⟨.function, "same", some "P9", false, entryFunction⟩
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

theorem base_exists : (Source.elabBaseArgs resolution.env "P9").isSome = true :=
  InferenceCuts.base_some _ _
    (by rw [show resolution.env.inheritOf "P9" = .nil from rfl, Source.Syn.inheritList]) rfl

theorem elaborates_eq : Source.elaborates resolution.env = true := by
  change (((((Source.elabBody resolution.env leafDecl).isSome &&
    ((Source.elabBody resolution.env entryDecl).isSome && true)) && true) &&
    ((Source.elabBaseArgs resolution.env "P9").isSome && true))) = true
  rw [leaf_exists, entry_exists, base_exists]
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
theorem leaf_sig : leafDecl.fnSig resolution.env = some ([], []) := rfl
theorem entry_sig : entryDecl.fnSig resolution.env = some ([], [.bool]) := rfl


theorem bases_eq : resolution.env.bases "P9" = [] := by
  change (Source.inheritPaths (.nil : Source.Syn (.list .inherit))).map
    (fun p => p.tail.getLast?.getD p.head) = []
  rw [Source.inheritPaths]
  · rfl
  · intro c x xs hc hh
    cases Source.Cat.list.inj hc
    cases hh
  · intro p a hc _
    cases hc

theorem linearize_eq : resolution.env.linearize "P9" = some ["P9"] := by
  change resolution.env.linearizeF 4 "P9" = some ["P9"]
  rw [Source.Env.linearizeF, bases_eq]
  rfl

theorem fn_in_eq : resolution.env.fnIn "P9" entryDecl.name [] = [leafDecl, entryDecl] := rfl


theorem selected_void (fixed : Roadmap.Fixed) : (glob fixed).dispatchFn "P9" entryDecl = leafDecl := by
  have hb : (glob fixed).prog.body leafDecl = some leafBody := leaf_body
  unfold Source.Glob.dispatchFn
  rw [entry_sig, linearize_eq]
  have hs : (entryDecl.scope.isSome && ["P9"].any (fun x => some x == entryDecl.scope)) = true := by decide
  simp only [Option.getD_some]
  rw [hs]
  simp only [↓reduceIte, List.findSome?_cons, fn_in_eq, List.find?_cons, hb,
    Option.isSome_some, Option.getD_some]

theorem selected_return_mismatch : (leafDecl.fnSig resolution.env).map Prod.snd ≠
    (entryDecl.fnSig resolution.env).map Prod.snd := by rw [leaf_sig, entry_sig]; decide

theorem body_refused (fixed : Roadmap.Fixed) :
    WholeProgram.checkBody resolution (glob fixed) "P9" [leafDecl, entryDecl] entryDecl = false := by
  have hb : (glob fixed).prog.body leafDecl = some leafBody := leaf_body
  simp only [WholeProgram.checkBody, entry_sig, selected_void, leaf_sig, hb]
  rfl

theorem checker_refused (fixed : Roadmap.Fixed) :
    WholeProgram.check resolution (glob fixed) "P9" [entryDecl] = false := by
  have hb : (glob fixed).prog.body leafDecl = some leafBody := leaf_body
  simp only [WholeProgram.check, List.all_cons, List.all_nil, Bool.and_true,
    WholeProgram.checkBody, entry_sig, selected_void, leaf_sig, hb]
  rfl
#print axioms actual_elaboration
#print axioms selected_void
#print axioms body_refused
#print axioms checker_refused
end Solidity.Lowering.P9.ReturnControls
