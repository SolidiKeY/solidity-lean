import Solidity.Correctness.Lowering.Total.ReferenceStateDecode
import Solidity.Correctness.Lowering.Total.ConstructorPlacement

/-!
# Reference state roots and the constructor in assembled function units

Composes the landed components `ReferenceStateDecode.state` (every root,
primitive or reference, with its initializer), `Constructor.constructorPart`
and `Callee.withFunctions`, leaving each definition as it is.

* **Prefix.** `prefixParts` is the explicit constructor, if any, then the
  reference-aware state parts: the order `Constructor.declarationParts` uses.
  `assemble` places it in front of the translated function entries. A refusal
  of a component is a named `Error`: a representation gap of that component,
  not an accepted-input restriction.
* **Placement.** `Constructor.withFunctions_placed_prefix` (reused, not
  reproved) gives `Placed u.env scope parts`; collection, kinds and filtering
  are read off the construction. The unit's constructors and non-constant
  state variables of `scope` are exactly the generated constructor
  declarations and roots, in order (`assemble_owned`); function entries
  contribute only ordinary functions (`assemble_functions`).
* **Roots and initializers.** `partsOf_faithful`, exported for the actual
  `u.env.stateVarsOf scope` (`assemble_roots`), and, under the existing
  `Source.elaborates` condition, for `Source.progOf`'s initializer list
  (`assemble_inits`).
* **Constructor.** `u.env.ctorDecl`, `ctorFrame` and `progOf`'s constructor are
  the assembled constructor's Source projections (`assemble_ctor`), explicit
  (`assemble_ctor_explicit`, with `constructorPart_faithful`'s frame) or
  implicit (`assemble_ctor_implicit`).
* **Declared types.** `partsOf_typed` for `u.env.stateVarsOf scope`, under
  `ReferenceStateDecode`'s explicit struct-resolution obligations only
  (`assemble_typed`). The assembled unit declares no struct, so it resolves no
  struct name (`assemble_unresolved`): the obligation holds there exactly when
  no root mentions a written struct, and its discharge stays with the struct
  and complete-unit composition work.
* **Compatibility.** Where `Constructor.declarationParts` succeeds, `prefixParts`
  gives the same parts and `assemble` the same unit as the primitive
  placement (`assemble_of_declarationParts`), so both families of facts hold
  for it.

Not claimed here (the original decoder and assigned lanes): Source frame
correspondence of the whole unit, struct and function integration, metadata
recovery, whole-unit elaboration success, registry/inference completeness and
semantic binding. No `lowerLoopsCorrect` or execution-equivalence credit.
-/
namespace Solidity.Correctness.Lowering.Total.ReferenceStatePlacement

open Source (Syn)
open Decode
open Decode.Constructor (Ordered constructorPart ctorDecl ctorDecls Placed declarationParts)
open Decode.Callee (withFunctions functionParts)
open ReferenceStateDecode (state partsOf rootType RootSlot InitSlot TypedRoot)
open ReferenceDecode (structsTy written? Resolved)

/-- Why a contract and its function entries give no assembled unit: the
component that refused. Each is an open representation gap. -/
inductive Error where
  | state (e : ReferenceStateDecode.Error) -- `ReferenceStateDecode.state` refused a root
  | constructor -- `Constructor.constructorPart` refused the model constructor
  | functions -- `Callee.functionParts` refused a function entry
  deriving Repr

/-- The root-type speller `ReferenceStateDecode.state` uses for `C`. -/
abbrev rootTyOf (C : Contract) : Name → Ty → Except ReferenceStateDecode.Error (Syn .typeName) :=
  rootType C (TransientDecode.elemOf C)

/-- The transient flag `ReferenceStateDecode.state` uses for `C`. -/
abbrev trOf (C : Contract) : Name → Bool := fun x => C.transientRoots.contains x

/-- **The constructor/state prefix**: the explicit constructor, if any, then
every root, primitive or reference, with its initializer. -/
def prefixParts (T : Tables) (R : CallSpellExt.Registry) (C : Contract) :
    Except Error (Syn (.list (.part false))) :=
  match state T R C with
  | .error e => .error (.state e)
  | .ok st => match C.ctor with
    | none => .ok st
    | some d => match constructorPart T R d with
      | some node => .ok (.cons node st)
      | none => .error .constructor

/-- **The assembled unit**: the prefix in front of the translated function entries. -/
def assemble (T : Tables) (R : CallSpellExt.Registry) (C : Contract) (scope : String)
    (fs : List (Name × FunDecl)) : Except Error (Syn .unit) :=
  match prefixParts T R C with
  | .error e => .error e
  | .ok p => match withFunctions T R scope p fs with
    | some u => .ok u
    | none => .error .functions

variable {T : Tables} {R : CallSpellExt.Registry} {C : Contract} {scope : String}
  {fs : List (Name × FunDecl)} {u : Syn .unit} {parts : Syn (.list (.part false))}

/-! ## Order helpers -/

theorem ordered_mem {α β : Type} {r : α → β → Prop} :
    ∀ {as : List α} {bs : List β}, Ordered r as bs → ∀ b ∈ bs, ∃ a ∈ as, r a b
  | _, _, .nil, _, hb => by cases hb
  | _, _, .cons h t, b, hb => by
      rcases List.mem_cons.mp hb with rfl | hb
      · exact ⟨_, List.mem_cons_self, h⟩
      · obtain ⟨a, ha, h'⟩ := ordered_mem t b hb
        exact ⟨a, List.mem_cons_of_mem _ ha, h'⟩

theorem ordered_map_right {α β γ : Type} {r : α → β → Prop} {f : γ → β} :
    ∀ {as : List α} {cs : List γ}, Ordered r as (cs.map f) → Ordered (fun a c => r a (f c)) as cs
  | [], [], _ => .nil
  | [], _ :: _, h => by cases h
  | _ :: _, [], h => by cases h
  | _ :: _, _ :: _, .cons h t => .cons h (ordered_map_right t)

/-! ## The prefix, read off the construction -/

/-- A successful prefix: the state parts, behind the constructor part when the
model has a constructor. -/
theorem prefixParts_ok (h : prefixParts T R C = .ok parts) :
    ∃ st, state T R C = .ok st ∧
      ((C.ctor = none ∧ parts = st) ∨
        ∃ d node, C.ctor = some d ∧ constructorPart T R d = some node ∧ parts = .cons node st) := by
  unfold prefixParts at h
  cases hs : state T R C with
  | error e => simp only [hs] at h; cases h
  | ok st =>
      simp only [hs] at h
      refine ⟨st, rfl, ?_⟩
      cases hc : C.ctor with
      | none => simp only [hc] at h; cases h; exact .inl ⟨rfl, rfl⟩
      | some d =>
          simp only [hc] at h
          cases hn : constructorPart T R d with
          | none => simp only [hn] at h; cases h
          | some node => simp only [hn] at h; cases h; exact .inr ⟨d, node, rfl, hn, rfl⟩

/-- **Prefix collection.** The collected declarations are the constructor
declaration (one for an explicit constructor, none for the implicit one), then
the roots' declarations in root order. -/
theorem prefixParts_collect (h : prefixParts T R C = .ok parts) (scope : String) :
    ∃ st ctors, state T R C = .ok st ∧ ctorDecls T R scope C.ctor = some ctors ∧
      parts.collect (some scope) = ctors ++ st.collect (some scope) := by
  obtain ⟨st, hs, ⟨hc, hst⟩ | ⟨d, node, hc, hn, rfl⟩⟩ := prefixParts_ok h
  · subst hst
    exact ⟨_, [], hs, by rw [hc]; rfl, rfl⟩
  · obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, rfl, _⟩ :=
      Constructor.constructorPart_faithful hn scope ⟨[]⟩
    refine ⟨st, _, hs, by rw [hc, ctorDecls, hn]; rfl, ?_⟩
    rw [Source.Syn.collect]
    rfl

/-- Every root declaration is a non-constant state variable of `scope`. -/
theorem state_kind {st : Syn (.list (.part false))} (h : state T R C = .ok st) (scope : String) :
    ∀ d ∈ st.collect (some scope),
      d.kind = .stateVar ∧ d.scope = some scope ∧ d.isConst = false := by
  intro d hd
  obtain ⟨_, _, _, _, _, _, rfl⟩ :=
    ordered_mem (ReferenceStateDecode.partsOf_faithful scope _ _ st h).1 d hd
  exact ⟨rfl, rfl, rfl⟩

/-- Every generated constructor declaration is a constructor of `scope`. -/
theorem ctorDecls_kind {ctors : List Source.Decl} (h : ctorDecls T R scope C.ctor = some ctors) :
    ∀ d ∈ ctors, d.kind = .constructor ∧ d.scope = some scope := by
  cases hc : C.ctor <;> rw [hc] at h <;>
    simp only [ctorDecls, Option.map_eq_some_iff, Option.some.injEq] at h
  · subst h; simp
  · obtain ⟨node, _, rfl⟩ := h; simp [ctorDecl]

/-! ## The assembled unit -/

/-- A successful assembly: a successful prefix and `withFunctions` on it. -/
theorem assemble_ok (h : assemble T R C scope fs = .ok u) :
    ∃ parts, prefixParts T R C = .ok parts ∧ withFunctions T R scope parts fs = some u := by
  unfold assemble at h
  cases hp : prefixParts T R C with
  | error e => simp only [hp] at h; cases h
  | ok p =>
      simp only [hp] at h
      cases hu : withFunctions T R scope p fs with
      | none => simp only [hu] at h; cases h
      | some u' => simp only [hu] at h; cases h; exact ⟨p, rfl, hu⟩

/-- **Placement**, by `Constructor.withFunctions_placed_prefix`. -/
theorem assemble_placed (h : assemble T R C scope fs = .ok u) :
    ∃ parts, prefixParts T R C = .ok parts ∧ Placed u.env scope parts := by
  obtain ⟨parts, hp, hu⟩ := assemble_ok h
  exact ⟨parts, hp, Constructor.withFunctions_placed_prefix hu⟩

/-- The function entries contribute only ordinary functions. -/
theorem assemble_functions (h : assemble T R C scope fs = .ok u) :
    ∃ functions, functionParts T R scope fs = some functions ∧
      ∀ d ∈ functions.collect (some scope), d.kind = .function := by
  obtain ⟨_, _, hu⟩ := assemble_ok h
  obtain ⟨functions, hf, _, _⟩ := Callee.withFunctions_declarations hu
  exact ⟨functions, hf, Constructor.functionParts_kind hf⟩

theorem placed_filter {E : Source.Env} (h : Placed E scope parts) (q : Source.Decl → Bool)
    (hq : ∀ d, q d = true → d.scope = some scope ∧ (d.kind = .constructor ∨ d.kind = .stateVar)) :
    E.decls.filter q = (parts.collect (some scope)).filter q := by
  obtain ⟨before, after, hd, out⟩ := h
  have gone : ∀ l : List Source.Decl, (∀ d ∈ l, d ∈ before ++ after) → l.filter q = [] := by
    intro l hl
    rw [List.filter_eq_nil_iff]
    intro d hd hqd
    obtain ⟨h1, h2⟩ := out d (hl d hd) (hq d hqd).1
    exact (hq d hqd).2.elim h1 h2
  rw [hd, List.filter_append, List.filter_append,
    gone before (fun d hd => List.mem_append_left _ hd),
    gone after (fun d hd => List.mem_append_right _ hd), List.nil_append, List.append_nil]

/-- **Exactly the generated constructor and roots.** The unit's constructors
and state variables of `scope` are the generated constructor declarations,
then the roots' declarations, in order; nothing else of either kind occurs. -/
theorem assemble_owned (h : assemble T R C scope fs = .ok u) :
    ∃ st ctors, state T R C = .ok st ∧ ctorDecls T R scope C.ctor = some ctors ∧
      u.env.decls.filter (fun d => d.scope == some scope &&
        (d.kind == .constructor || d.kind == .stateVar)) = ctors ++ st.collect (some scope) := by
  obtain ⟨parts, hp, placed⟩ := assemble_placed h
  obtain ⟨st, ctors, hs, hc, hcol⟩ := prefixParts_collect hp scope
  refine ⟨st, ctors, hs, hc, ?_⟩
  rw [placed_filter placed _ (by simp +contextual), hcol, List.filter_eq_self]
  intro d hd
  rcases List.mem_append.mp hd with hd | hd
  · obtain ⟨k, s⟩ := ctorDecls_kind hc d hd; simp [k, s]
  · obtain ⟨k, s, _⟩ := state_kind hs scope d hd; simp [k, s]

/-- The unit's non-constant state variables of `scope` are the roots' declarations. -/
theorem assemble_stateVarsOf (h : assemble T R C scope fs = .ok u) :
    ∃ st, state T R C = .ok st ∧ u.env.stateVarsOf scope = st.collect (some scope) := by
  obtain ⟨parts, hp, placed⟩ := assemble_placed h
  obtain ⟨st, ctors, hs, hc, hcol⟩ := prefixParts_collect hp scope
  refine ⟨st, hs, ?_⟩
  unfold Source.Env.stateVarsOf
  rw [placed_filter placed _ (by simp +contextual), hcol, List.filter_append,
    List.filter_eq_nil_iff.mpr (fun d hd => by simp [(ctorDecls_kind hc d hd).1]),
    List.filter_eq_self.mpr (fun d hd => by simp [state_kind hs scope d hd]), List.nil_append]

/-- **Roots and initializers of the unit** (`partsOf_faithful` for the actual
`u.env.stateVarsOf scope`): the roots, one each and in order; those carrying an
initializer are the model's initializers, one each and in order, each on its
target root. -/
theorem assemble_roots (h : assemble T R C scope fs = .ok u) :
    Ordered (RootSlot (rootTyOf C) (trOf C) scope) C.vars (u.env.stateVarsOf scope) ∧
    Ordered (InitSlot (Calls.expr T R) scope) C.inits
      ((u.env.stateVarsOf scope).filter fun d => d.init?.isSome) := by
  obtain ⟨st, hs, hv⟩ := assemble_stateVarsOf h
  rw [hv]
  exact ReferenceStateDecode.partsOf_faithful scope _ _ st hs

/-- **Initializers of the elaborated program.** When the unit elaborates,
`Source.progOf`'s initializers of `scope` are the model's, one each and in
order, each the spelled original expression on its target root. -/
theorem assemble_inits (h : assemble T R C scope fs = .ok u)
    (hE : Source.elaborates u.env = true) :
    Ordered (fun i (r : Source.RInit u.env) => InitSlot (Calls.expr T R) scope i r.var)
      C.inits ((Source.progOf u.env).inits scope) := by
  have hi := (assemble_roots h).2
  rw [← Constructor.progOf_inits u.env scope hE] at hi
  exact ordered_map_right hi

/-- **The constructor Source finds**: the assembled constructor declaration of
`scope`, or none for the implicit constructor; its frame; and the program's
constructor body, the elaboration of that declaration alone. -/
theorem assemble_ctor (h : assemble T R C scope fs = .ok u) :
    ∃ ctors, ctorDecls T R scope C.ctor = some ctors ∧ u.env.ctorDecl scope = ctors.head? ∧
      u.env.ctorFrame scope = ctors.head?.bind (·.frame? u.env) ∧
      (Source.progOf u.env).ctor scope =
        ctors.head?.bind fun d => (Source.elabBody u.env d).map Subtype.val := by
  obtain ⟨parts, hp, placed⟩ := assemble_placed h
  obtain ⟨st, ctors, hs, hc, hcol⟩ := prefixParts_collect hp scope
  have hf' : u.env.decls.filter (fun d => d.kind == .constructor && d.scope == some scope) =
      ctors := by
    rw [placed_filter placed _ (by simp +contextual), hcol, List.filter_append,
      List.filter_eq_self.mpr (fun d hd => by simp [ctorDecls_kind hc d hd]),
      List.filter_eq_nil_iff.mpr (fun d hd => by simp [(state_kind hs scope d hd).1]),
      List.append_nil]
  have found : u.env.ctorDecl scope = ctors.head? := by
    rw [Source.Env.ctorDecl, ← hf', List.head?_filter]
  exact ⟨ctors, hc, found, by rw [Source.Env.ctorFrame, found],
    by simp only [Source.progOf, found]⟩

/-- **The implicit constructor**: no declaration, no frame, no program body. -/
theorem assemble_ctor_implicit (h : assemble T R C scope fs = .ok u) (hc : C.ctor = none) :
    u.env.ctorDecl scope = none ∧ u.env.ctorFrame scope = none ∧
      (Source.progOf u.env).ctor scope = none := by
  obtain ⟨ctors, hcs, hd, hf, hb⟩ := assemble_ctor h
  rw [hc] at hcs; cases hcs
  exact ⟨hd, hf, hb⟩

/-- **The explicit constructor**: the declaration is the assembled constructor
part, with `constructorPart_faithful`'s Source frame (original parameter
names, table-corresponding parameter types, no return slot, the spelled body,
`msg.value` exactly when payable); the program's body is its elaboration. -/
theorem assemble_ctor_explicit (h : assemble T R C scope fs = .ok u) {d : FunDecl}
    (hc : C.ctor = some d) :
    ∃ node f, constructorPart T R d = some node ∧
      u.env.ctorDecl scope = some (ctorDecl scope node) ∧ u.env.ctorFrame scope = some f ∧
      (Source.progOf u.env).ctor scope =
        (Source.elabBody u.env (ctorDecl scope node)).map Subtype.val ∧
      f.names = d.params.map (fun p => some p.1) ∧ f.rnames = [] ∧
      Callee.Slots d.widths d.params f.ps ∧ f.rs = [] ∧ f.inModifier = false := by
  obtain ⟨ctors, hcs, hd, hf, hb⟩ := assemble_ctor h
  rw [hc] at hcs
  simp only [ctorDecls, Option.map_eq_some_iff] at hcs
  obtain ⟨node, hn, rfl⟩ := hcs
  obtain ⟨_, _, _, _, _, f, _, _, _, _, _, _, _, hfr, names, rn, slots, rs, _, _, im⟩ :=
    Constructor.constructorPart_faithful hn scope u.env
  refine ⟨node, f, hn, hd, ?_, hb, names, rn, slots, rs, im⟩
  rw [hf]; exact hfr

/-! ## Declared types -/

/-- **Declared Source types of the unit's roots** (`partsOf_typed` for the
actual `u.env.stateVarsOf scope`), under `ReferenceStateDecode`'s explicit
struct-resolution obligations for `u.env` and nothing else. -/
theorem assemble_typed (h : assemble T R C scope fs = .ok u)
    (res : ∀ v ∈ C.vars, ∀ s ∈ structsTy v.2, ∀ w, written? C s = some w →
      ∃ d, Resolved u.env (some scope) w d) :
    Ordered (TypedRoot C (TransientDecode.elemOf C) (trOf C) u.env scope) C.vars
      (u.env.stateVarsOf scope) := by
  obtain ⟨st, hs, hv⟩ := assemble_stateVarsOf h
  rw [hv]
  exact ReferenceStateDecode.partsOf_typed scope hs res

theorem lookup_mem {E : Source.Env} {s : Option String} {x : String} {d : Source.Decl}
    (h : d ∈ E.lookup s x) : d ∈ E.decls := by
  simp only [Source.Env.lookup] at h
  split at h <;> simp only [Source.Env.visible, Source.Env.declared, List.mem_filter] at h
  · exact h.1.1
  · exact h.1

/-- The assembled unit declares no struct: its declarations are the contract,
the generated constructor and roots, and ordinary functions. -/
theorem assemble_noStruct (h : assemble T R C scope fs = .ok u) :
    ∀ d ∈ u.env.decls, d.kind ≠ .struct := by
  obtain ⟨parts, hp, hu⟩ := assemble_ok h
  obtain ⟨functions, hf, _, hd⟩ := Callee.withFunctions_declarations hu
  obtain ⟨st, ctors, hs, hc, hcol⟩ := prefixParts_collect hp scope
  intro d hm
  change d ∈ u.decls at hm
  rw [hd, hcol] at hm
  rcases List.mem_cons.mp hm with rfl | hm
  · nofun
  rcases List.mem_append.mp hm with hm | hm
  · rcases List.mem_append.mp hm with hm | hm
    · rw [(ctorDecls_kind hc d hm).1]; nofun
    · rw [(state_kind hs scope d hm).1]; nofun
  · rw [Constructor.functionParts_kind hf d hm]; nofun

/-- **No struct resolves in the assembled unit alone.** So `assemble_typed`'s
obligation holds for `u.env` only when no root mentions a written struct;
discharging it for struct roots needs the generated struct declarations of the
complete unit, which this module does not supply. -/
theorem assemble_unresolved (h : assemble T R C scope fs = .ok u) (s : Option String)
    (w : Name) (d : Source.DeclName) : ¬ Resolved u.env s w d := by
  rintro ⟨decl, look, kind, _⟩
  exact assemble_noStruct h decl (lookup_mem (by rw [look]; exact List.mem_singleton_self _)) kind

/-! ## Compatibility with the primitive placement -/

/-- Where `Constructor.declarationParts` succeeds (all roots primitive), the
reference-aware prefix is the same parts. -/
theorem prefixParts_of_declarationParts (h : declarationParts T R C = some parts) :
    prefixParts T R C = .ok parts := by
  simp only [declarationParts, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨st, hs, h⟩ := h
  have hst : state T R C = .ok st := ReferenceStateDecode.partsOf_stateParts C _ _ st hs
  unfold prefixParts
  rw [hst]
  cases hc : C.ctor with
  | none =>
      rw [hc] at h
      simp only [Option.pure_def, Option.some.injEq] at h
      subst h; rfl
  | some d =>
      rw [hc] at h
      simp only [Option.pure_def, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨node, hn, rfl⟩ := h
      simp only [hn]

/-- **Compatibility.** On the common successful domain the assembled unit is
the primitive placement's unit, so `Constructor.withFunctions_inits`,
`withFunctions_ctor` and `withFunctions_decls` describe it too. -/
theorem assemble_of_declarationParts (hp : declarationParts T R C = some parts)
    (hu : withFunctions T R scope parts fs = some u) : assemble T R C scope fs = .ok u := by
  unfold assemble
  rw [prefixParts_of_declarationParts hp]
  simp only [hu]

/-- Conversely, an assembly whose prefix is the primitive parts places them:
its roots satisfy both the primitive (`VarSlot`) and reference (`RootSlot`)
slots, for the same `u.env.stateVarsOf scope`. -/
theorem assemble_primitive_slots (hp : declarationParts T R C = some parts)
    (h : assemble T R C scope fs = .ok u) :
    Ordered (Constructor.VarSlot (TransientDecode.elemOf C) (trOf C) scope) C.vars
      (u.env.stateVarsOf scope) ∧
    Ordered (RootSlot (rootTyOf C) (trOf C) scope) C.vars (u.env.stateVarsOf scope) := by
  obtain ⟨parts', hp', hu⟩ := assemble_ok h
  rw [prefixParts_of_declarationParts hp] at hp'
  cases hp'
  exact ⟨(Constructor.withFunctions_inits hp hu).1, (assemble_roots h).1⟩

/-! ## Gaps: each component refusal is named -/

theorem assemble_state_error {e : ReferenceStateDecode.Error} (h : state T R C = .error e) :
    assemble T R C scope fs = .error (.state e) := by
  simp only [assemble, prefixParts, h]

theorem assemble_ctor_error {st : Syn (.list (.part false))} {d : FunDecl}
    (hs : state T R C = .ok st) (hc : C.ctor = some d) (hn : constructorPart T R d = none) :
    assemble T R C scope fs = .error .constructor := by
  simp only [assemble, prefixParts, hs, hc, hn]

theorem assemble_functions_error (hp : prefixParts T R C = .ok parts)
    (hf : functionParts T R scope fs = none) : assemble T R C scope fs = .error .functions := by
  simp only [assemble, hp, withFunctions, hf, Option.bind_eq_bind, Option.bind_none]

end Solidity.Correctness.Lowering.Total.ReferenceStatePlacement
