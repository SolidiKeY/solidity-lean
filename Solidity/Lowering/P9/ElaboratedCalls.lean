import Solidity.Source.Elaborate
import Solidity.Source.StmtProgress

/-! P9 actual elaborated-program client. This derives the published CallsOK
condition for a nonempty actual function set, not all approved Source programs.
No manually supplied target/body execution or CallsOK certificate is an input. -/
namespace Solidity.Lowering.P9
open Source Roadmap

def function : Source.Syn (.part false) :=
  .function (.ident "truth") .nil (some .internal) none .nil false none
    (.cons (.param (.elem .bool) none none) .nil)
    (.some (.block (.cons (.stmtItem (.returnStmt (.some (.lit (.bool true))))) .nil)))

def unit : Source.Syn .unit :=
  .unit (.cons (.contract false "P9" .none .nil (.cons function .nil)) .nil)
def resolution := Source.resolveUnit {pipeline := .legacy} unit

def declaration : Source.Decl := ⟨.function, "truth", some "P9", false, function⟩
def frame := (declaration.frame? resolution.env).get (by rfl)
def inferred := (Source.ItemsD.infer (frame.ctx resolution.env declaration.scope) frame.locals frame.body).get (by rfl)
theorem frame_eq : declaration.frame? resolution.env = some frame := rfl
theorem inferred_eq : Source.ItemsD.infer (frame.ctx resolution.env declaration.scope) frame.locals frame.body = some inferred := rfl
theorem invs_eq : declaration.modInvs.invList = [] := by
  rw [show declaration.modInvs = .nil from rfl, Source.Syn.invList]
theorem mods_some : (Source.elabMods resolution.env declaration frame declaration.modInvs.invList).isSome = true := by
  rw [invs_eq, Source.elabMods]
  rfl

theorem body_exists : (Source.elabBody resolution.env declaration).isSome = true := by
  simp only [Source.elabBody, frame_eq, inferred_eq]
  cases hm : Source.elabMods resolution.env declaration frame declaration.modInvs.invList with
  | none => have hx := mods_some; rw [hm] at hx; cases hx
  | some m => cases m; rfl

theorem base_args_some : (Source.elabBaseArgs resolution.env "P9").isSome = true := by
  have hi : (resolution.env.inheritOf "P9").inheritList = [] := by
    rw [show resolution.env.inheritOf "P9" = .nil from rfl, Source.Syn.inheritList]
  have hs : (Source.elabInherit resolution.env "P9" (resolution.env.inheritOf "P9").inheritList).isSome = true := by
    rw [hi, Source.elabInherit]
    rfl
  unfold Source.elabBaseArgs
  cases he : Source.elabInherit resolution.env "P9" (resolution.env.inheritOf "P9").inheritList with
  | none => have hx := hs; rw [he] at hx; cases hx
  | some v => cases v; rfl

theorem elaborates_eq : Source.elaborates resolution.env = true := by
  change ((((Source.elabBody resolution.env declaration).isSome && true) && true) &&
    ((Source.elabBaseArgs resolution.env "P9").isSome && true)) = true
  rw [body_exists, base_args_some]
  rfl

/-- Actual published elaborate output, including its dependent program. -/
theorem actual_elaboration : ∃ el, Source.elaborate resolution = some el ∧
    el.res = resolution ∧ HEq el.prog (Source.progOf resolution.env) := by
  simp only [Source.elaborate, elaborates_eq, ↓reduceIte]
  exact ⟨_, rfl, rfl, HEq.rfl⟩

def body := Source.RBody.ofDerivation frame inferred.2 []

theorem prog_body : (Source.progOf resolution.env).body declaration = some body := by
  have hm : (Source.elabMods resolution.env declaration frame declaration.modInvs.invList).map Subtype.val = some [] := by
    rw [invs_eq, Source.elabMods]
    rfl
  simp only [Source.progOf, Source.elabBody, frame_eq, inferred_eq]
  cases he : Source.elabMods resolution.env declaration frame declaration.modInvs.invList with
  | none => rw [he] at hm; cases hm
  | some v =>
    rcases v with ⟨ms, hms⟩
    simp only [he, Option.map_some, Option.some.injEq] at hm
    subst ms
    rfl

def glob (fixed : Roadmap.Fixed) : Source.Glob resolution.env :=
  ⟨Source.progOf resolution.env, .legacy, fixed, fun _ => ⟨0, by decide⟩,
    fun _ _ => true, fun _ => .answer (.success []), ⟨0, by decide⟩⟩

theorem declaration_present : declaration ∈ resolution.unit.decls :=
  List.mem_cons_of_mem _ List.mem_cons_self

theorem signature : declaration.fnSig resolution.env = some ([], [.bool]) := rfl

theorem allowed_inhabited : ∃ d, d = declaration ∧ (d.fnSig resolution.env).isSome = true :=
  ⟨declaration, rfl, rfl⟩

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
  change resolution.env.linearizeF 3 "P9" = some ["P9"]
  rw [Source.Env.linearizeF, bases_eq]
  rfl

theorem fn_in_eq : resolution.env.fnIn "P9" declaration.name [] = [declaration] := rfl

theorem dispatch_eq (fixed : Roadmap.Fixed) : (glob fixed).dispatchFn "P9" declaration = declaration := by
  have hscope : (declaration.scope.isSome && ["P9"].any (fun x => some x == declaration.scope)) = true := by
    decide +kernel
  have hb : (glob fixed).prog.body declaration = some body := prog_body
  unfold Source.Glob.dispatchFn
  rw [signature, linearize_eq]
  simp only [Option.getD_some]
  rw [hscope]
  simp only [↓reduceIte, List.findSome?_cons, fn_in_eq, List.find?_cons, hb,
    Option.isSome_some, Option.getD_some]

/-- All conditions derive from the actual computed elaboration/body. -/
theorem callsOK (fixed : Roadmap.Fixed) :
    Source.CallsOK (fun d => d = declaration) (glob fixed) "P9" := by
  intro d ps rs hs hd
  subst d
  rw [signature] at hs
  simp only [Option.some.injEq, Prod.mk.injEq] at hs
  obtain ⟨rfl, rfl⟩ := hs
  refine ⟨body, ?_, rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · rw [dispatch_eq]
    exact prog_body
  · intro τ ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    subst τ
    rfl
  · exact ⟨⟨trivial, rfl, .inl rfl⟩, trivial⟩
  · exact ⟨trivial, trivial⟩

#print axioms actual_elaboration
#print axioms prog_body
#print axioms callsOK
end Solidity.Lowering.P9
