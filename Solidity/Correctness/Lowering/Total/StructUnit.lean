import Solidity.Correctness.Lowering.Total.StructDecode
import Solidity.Correctness.Lowering.Total.ReferenceStatePlacement

/-!
# Struct declarations, reference state roots, the constructor and functions in one unit

`build` composes `StructDecode.decode`, `ReferenceStatePlacement.prefixParts` and
`Callee.withFunctions`, each unchanged: the generated structs in table order, then the
constructor/state prefix, then the translated functions. A refusing component is a named
`Error` (`build_*_error`; only a struct refusal carries its entry's position); nothing is
filtered, no metadata invented, no component replaced by an empty one.

From a successful build: the exact declarations (`build_decls`); the structs and functions
as the entries, one each, in order (`build_structs`, `build_functions`); placement, roots,
initializers and the constructor from the component theorems (`build_placed`,
`build_owned`, `build_roots`, `build_inits`, `build_ctor*`); a struct name resolves exactly
when the table declares it once and no root or function carries it (`build_resolved`,
`build_resolved_only`), discharging field and root typing (`build_structFields`,
`build_typed`). With no struct, `assemble`'s unit is built (`build_of_assemble`).

Open: complete decoder coverage, discharging the components' representability conditions
(the decoder and final producer keep that obligation), nested table interpretation,
file-level declarations, semantic binding and `lowerLoopsCorrect`.
-/
namespace Solidity.Correctness.Lowering.Total.StructUnit

open Source (Syn)
open Decode
open Decode.Constructor (Ordered ctorDecl ctorDecls Placed constructorPart)
open Decode.Callee (withFunctions functionParts fromMetadata appendParts)
open ReferenceStateDecode (state RootSlot InitSlot TypedRoot)
open ReferenceDecode (structsTy written? Resolved)
open ReferenceStatePlacement (prefixParts rootTyOf trOf placed_filter prefixParts_collect
  state_kind ctorDecls_kind ordered_mem ordered_map_right assemble)
open StructDecode (Gen Pairs named Fields Declared)
open Solidity.Semantics (lookupBy structDef)

/-- The component that refused. -/
inductive Error where
  | structs (e : StructDecode.Error) -- `StructDecode.decode` refused a table entry
  | placement (e : ReferenceStatePlacement.Error) -- the constructor/state prefix refused
  | functions -- `Callee.functionParts` refused a function entry
  deriving Repr

/-- **The mixed unit**: the structs, then the constructor/state prefix, then the functions. -/
def build (T : Tables) (R : CallSpellExt.Registry) (C : Contract) (scope : String)
    (fs : List (Name × FunDecl)) : Except Error (Syn .unit) :=
  match StructDecode.decode C with
  | .error e => .error (.structs e)
  | .ok ss => match prefixParts T R C with
    | .error e => .error (.placement e)
    | .ok p => match withFunctions T R scope (appendParts ss p) fs with
      | some u => .ok u
      | none => .error .functions

/-- Noninterference for a struct name: no root and no function entry carries it. -/
def Apart (C : Contract) (fs : List (Name × FunDecl)) (w : Name) : Prop :=
  (∀ v ∈ C.vars, v.1 ≠ w) ∧ ∀ f ∈ fs, ∀ src, f.2.sourceDecl = some src → src.name ≠ w

variable {T : Tables} {R : CallSpellExt.Registry} {C : Contract} {scope : String}
  {fs : List (Name × FunDecl)} {u : Syn .unit}

theorem collect_append (s : Option String) : ∀ xs ys : Syn (.list (.part false)),
    (appendParts xs ys).collect s = xs.collect s ++ ys.collect s
  | .nil, _ => by simp only [appendParts, Source.Syn.collect, List.nil_append]
  | .cons x xs, ys => by
      simp only [appendParts, Source.Syn.collect, collect_append s xs ys, List.append_assoc]

theorem pairs_mem {α β : Type} {r : α → β → Prop} {as : List α} {bs : List β}
    (h : Pairs r as bs) : ∀ b ∈ bs, ∃ a ∈ as, r a b := by
  induction h with
  | nil => intro _ hb; cases hb
  | cons hab _ ih =>
    intro b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · exact ⟨_, List.mem_cons_self, hab⟩
    · obtain ⟨a, ha, r⟩ := ih b hb; exact ⟨a, List.mem_cons_of_mem _ ha, r⟩

/-- Every generated struct declaration is a struct of `scope`. -/
theorem gen_kind {d : Source.Decl} {ss : Syn (.list (.part false))}
    (hs : StructDecode.decode C = .ok ss) (hd : d ∈ ss.collect (some scope)) :
    d.kind = .struct ∧ d.scope = some scope := by
  obtain ⟨_, _, m, ms, rfl, _⟩ := pairs_mem (StructDecode.decode_collect hs scope) d hd
  exact ⟨rfl, rfl⟩

/-- A function entry's declaration carries its retained source name. -/
theorem function_name {functions : Syn (.list (.part false))}
    (hf : functionParts T R scope fs = some functions) {d : Source.Decl}
    (hd : d ∈ functions.collect (some scope)) :
    ∃ f ∈ fs, ∃ src, f.2.sourceDecl = some src ∧ d.name = src.name := by
  have hm : some d ∈ fs.map (fun f => fromMetadata T R scope f.2) := by
    rw [← Callee.functionParts_faithful T R scope fs functions hf]
    exact List.mem_map.mpr ⟨d, hd, rfl⟩
  obtain ⟨f, mf, hf'⟩ := List.mem_map.mp hm
  obtain ⟨src, _, hs, _, _, hn, _⟩ := Callee.fromMetadata_header hf'
  exact ⟨f, mf, src, hs, hn⟩

/-! ## Decomposition -/

/-- A successful build: each component succeeded, and `withFunctions` on their parts. -/
theorem build_ok (h : build T R C scope fs = .ok u) :
    ∃ ss p, StructDecode.decode C = .ok ss ∧ prefixParts T R C = .ok p ∧
      withFunctions T R scope (appendParts ss p) fs = some u := by
  unfold build at h
  split at h; · cases h
  rename_i ss hs
  split at h; · cases h
  rename_i p hp
  split at h
  · rename_i u' hu; cases h; exact ⟨ss, p, hs, hp, hu⟩
  · cases h

/-- **Exact declarations**: the contract, the structs (one per table entry, in order),
the constructor declaration (none for the implicit one), the roots, then the functions
(one per entry, in order); nothing else. -/
theorem build_decls (h : build T R C scope fs = .ok u) :
    ∃ k ss st ctors functions, k.kind = .contract ∧ k.scope = none ∧
      StructDecode.decode C = .ok ss ∧ state T R C = .ok st ∧
      ctorDecls T R scope C.ctor = some ctors ∧ functionParts T R scope fs = some functions ∧
      u.env.decls = k :: (ss.collect (some scope) ++ (ctors ++ st.collect (some scope)) ++
        functions.collect (some scope)) ∧
      Pairs (Gen C scope) C.structs (ss.collect (some scope)) ∧
      (functions.collect (some scope)).map some = fs.map (fun f => fromMetadata T R scope f.2) := by
  obtain ⟨ss, p, hs, hp, hu⟩ := build_ok h
  obtain ⟨functions, hf, _, hd⟩ := Callee.withFunctions_declarations hu
  obtain ⟨st, ctors, hst, hc, hcol⟩ := prefixParts_collect hp scope
  refine ⟨⟨.contract, scope, none, true, .contract false scope .none .nil
    (appendParts (appendParts ss p) functions)⟩, ss, st, ctors, functions, rfl, rfl, hs, hst, hc, hf, ?_,
    StructDecode.decode_collect hs scope, Callee.functionParts_faithful T R scope fs functions hf⟩
  change u.decls = _
  rw [hd, collect_append, hcol]

/-- **Placement** of the constructor/state prefix behind the inserted structs. -/
theorem build_placed (h : build T R C scope fs = .ok u) :
    ∃ p, prefixParts T R C = .ok p ∧ Placed u.env scope p := by
  obtain ⟨ss, p, hs, hp, hu⟩ := build_ok h
  obtain ⟨functions, hf, _, hd⟩ := Callee.withFunctions_declarations hu
  refine ⟨p, hp, ⟨.contract, scope, none, true, .contract false scope .none .nil
    (appendParts (appendParts ss p) functions)⟩ :: ss.collect (some scope), functions.collect (some scope), ?_, ?_⟩
  · change u.decls = _
    rw [hd, collect_append]; simp only [List.cons_append, List.append_assoc]
  intro d hd' hsc
  rcases List.mem_append.mp hd' with h1 | h2
  · rcases List.mem_cons.mp h1 with rfl | h1
    · cases hsc
    · rw [(gen_kind hs h1).1]; exact ⟨nofun, nofun⟩
  · rw [Constructor.functionParts_kind hf d h2]; exact ⟨nofun, nofun⟩

/-- **The unit's structs** are the table entries' declarations, one each and in order. -/
theorem build_structs (h : build T R C scope fs = .ok u) :
    Pairs (Gen C scope) C.structs (u.env.decls.filter (·.kind == .struct)) := by
  obtain ⟨k, ss, st, ctors, functions, hk, -, hs, hst, hc, hf, hd, g, -⟩ := build_decls h
  rw [hd, List.filter_cons, hk, List.filter_append, List.filter_append, List.filter_append,
    List.filter_eq_self.mpr (fun d hd => by simp [(gen_kind hs hd).1]),
    List.filter_eq_nil_iff.mpr (fun d hd => by simp [(ctorDecls_kind hc d hd).1]),
    List.filter_eq_nil_iff.mpr (fun d hd => by simp [(state_kind hst scope d hd).1]),
    List.filter_eq_nil_iff.mpr (fun d hd => by simp [Constructor.functionParts_kind hf d hd])]
  simpa using g

/-- **The unit's functions** are the function entries' translations, one each, in order. -/
theorem build_functions (h : build T R C scope fs = .ok u) :
    (u.env.decls.filter (·.kind == .function)).map some =
      fs.map (fun f => fromMetadata T R scope f.2) := by
  obtain ⟨k, ss, st, ctors, functions, hk, -, hs, hst, hc, hf, hd, -, hfs⟩ := build_decls h
  rw [hd, List.filter_cons, hk, List.filter_append, List.filter_append, List.filter_append,
    List.filter_eq_nil_iff.mpr (fun d hd => by simp [(gen_kind hs hd).1]),
    List.filter_eq_nil_iff.mpr (fun d hd => by simp [(ctorDecls_kind hc d hd).1]),
    List.filter_eq_nil_iff.mpr (fun d hd => by simp [(state_kind hst scope d hd).1]),
    List.filter_eq_self.mpr (fun d hd => by simp [Constructor.functionParts_kind hf d hd])]
  simpa using hfs

/-! ## Constructor, roots and initializers -/

/-- Exactly the generated constructor and roots, in order, among constructors and state
variables of `scope`. -/
theorem build_owned (h : build T R C scope fs = .ok u) :
    ∃ st ctors, state T R C = .ok st ∧ ctorDecls T R scope C.ctor = some ctors ∧
      u.env.decls.filter (fun d => d.scope == some scope &&
        (d.kind == .constructor || d.kind == .stateVar)) = ctors ++ st.collect (some scope) := by
  obtain ⟨p, hp, placed⟩ := build_placed h
  obtain ⟨st, ctors, hs, hc, hcol⟩ := prefixParts_collect hp scope
  refine ⟨st, ctors, hs, hc, ?_⟩
  rw [placed_filter placed _ (by simp +contextual), hcol, List.filter_eq_self]
  intro d hd
  rcases List.mem_append.mp hd with hd | hd
  · obtain ⟨k, s⟩ := ctorDecls_kind hc d hd; simp [k, s]
  · obtain ⟨k, s, _⟩ := state_kind hs scope d hd; simp [k, s]

theorem build_stateVarsOf (h : build T R C scope fs = .ok u) :
    ∃ st, state T R C = .ok st ∧ u.env.stateVarsOf scope = st.collect (some scope) := by
  obtain ⟨p, hp, placed⟩ := build_placed h
  obtain ⟨st, ctors, hs, hc, hcol⟩ := prefixParts_collect hp scope
  refine ⟨st, hs, ?_⟩
  unfold Source.Env.stateVarsOf
  rw [placed_filter placed _ (by simp +contextual), hcol, List.filter_append,
    List.filter_eq_nil_iff.mpr (fun d hd => by simp [(ctorDecls_kind hc d hd).1]),
    List.filter_eq_self.mpr (fun d hd => by simp [state_kind hs scope d hd]), List.nil_append]

/-- **Roots and initializers** of the unit, primitive or reference: `partsOf_faithful`. -/
theorem build_roots (h : build T R C scope fs = .ok u) :
    Ordered (RootSlot (rootTyOf C) (trOf C) scope) C.vars (u.env.stateVarsOf scope) ∧
    Ordered (InitSlot (Calls.expr T R) scope) C.inits
      ((u.env.stateVarsOf scope).filter fun d => d.init?.isSome) := by
  obtain ⟨st, hs, hv⟩ := build_stateVarsOf h
  rw [hv]
  exact ReferenceStateDecode.partsOf_faithful scope _ _ st hs

/-- **Initializers of the elaborated program**, one each and in order. -/
theorem build_inits (h : build T R C scope fs = .ok u) (hE : Source.elaborates u.env = true) :
    Ordered (fun i (r : Source.RInit u.env) => InitSlot (Calls.expr T R) scope i r.var)
      C.inits ((Source.progOf u.env).inits scope) := by
  have hi := (build_roots h).2
  rw [← Constructor.progOf_inits u.env scope hE] at hi
  exact ordered_map_right hi

/-- **The constructor Source finds**, its frame and the program's constructor body. -/
theorem build_ctor (h : build T R C scope fs = .ok u) :
    ∃ ctors, ctorDecls T R scope C.ctor = some ctors ∧ u.env.ctorDecl scope = ctors.head? ∧
      u.env.ctorFrame scope = ctors.head?.bind (·.frame? u.env) ∧
      (Source.progOf u.env).ctor scope =
        ctors.head?.bind fun d => (Source.elabBody u.env d).map Subtype.val := by
  obtain ⟨p, hp, placed⟩ := build_placed h
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

theorem build_ctor_implicit (h : build T R C scope fs = .ok u) (hc : C.ctor = none) :
    u.env.ctorDecl scope = none ∧ u.env.ctorFrame scope = none ∧
      (Source.progOf u.env).ctor scope = none := by
  obtain ⟨ctors, hcs, hd, hf, hb⟩ := build_ctor h
  rw [hc] at hcs; cases hcs
  exact ⟨hd, hf, hb⟩

theorem build_ctor_explicit (h : build T R C scope fs = .ok u) {d : FunDecl}
    (hc : C.ctor = some d) :
    ∃ node f, constructorPart T R d = some node ∧
      u.env.ctorDecl scope = some (ctorDecl scope node) ∧ u.env.ctorFrame scope = some f ∧
      (Source.progOf u.env).ctor scope =
        (Source.elabBody u.env (ctorDecl scope node)).map Subtype.val ∧
      f.names = d.params.map (fun p => some p.1) ∧ f.rnames = [] ∧
      Callee.Slots d.widths d.params f.ps ∧ f.rs = [] ∧ f.inModifier = false := by
  obtain ⟨ctors, hcs, hd, hf, hb⟩ := build_ctor h
  rw [hc] at hcs
  simp only [ctorDecls, Option.map_eq_some_iff] at hcs
  obtain ⟨node, hn, rfl⟩ := hcs
  obtain ⟨_, _, _, _, _, f, _, _, _, _, _, _, _, hfr, names, rn, slots, rs, _, _, im⟩ :=
    Constructor.constructorPart_faithful hn scope u.env
  refine ⟨node, f, hn, hd, ?_, hb, names, rn, slots, rs, im⟩
  rw [hf]; exact hfr

/-! ## Struct names in the unit -/

/-- The unit as `StructDecode`'s `pre ++ generated ++ post`, with the surrounding
declarations apart from every `Apart` name. -/
theorem build_split (h : build T R C scope fs = .ok u) :
    ∃ ss pre post, StructDecode.decode C = .ok ss ∧
      u.env.decls = pre ++ ss.collect (some scope) ++ post ∧
      ∀ w, w ≠ "" → Apart C fs w → ∀ d ∈ pre ++ post, ¬(d.scope = some scope ∧ d.name = w) := by
  obtain ⟨k, ss, st, ctors, functions, -, hk, hs, hst, hc, hf, hd, -, -⟩ := build_decls h
  refine ⟨ss, [k], ctors ++ st.collect (some scope) ++ functions.collect (some scope), hs,
    by rw [hd]; simp, ?_⟩
  intro w hw ⟨roots, funs⟩ d md ⟨sc, nm⟩
  simp only [List.mem_append, List.mem_singleton] at md
  rcases md with rfl | (md | md) | md
  · rw [hk] at sc; cases sc
  · cases hcd : C.ctor <;> rw [hcd] at hc <;>
      simp only [ctorDecls, Option.map_eq_some_iff, Option.some.injEq] at hc
    · subst hc; cases md
    · obtain ⟨node, _, rfl⟩ := hc
      rw [List.mem_singleton] at md; subst md; exact hw nm.symm
  · obtain ⟨v, mv, _, _, _, _, rfl⟩ :=
      ordered_mem (ReferenceStateDecode.partsOf_faithful scope _ _ st hst).1 d md
    exact roots v mv nm
  · obtain ⟨f, mf, src, hsrc, hn⟩ := function_name hf md
    exact funs f mf src hsrc (hn ▸ nm)

/-- A key of a decoded table is a nonempty name. -/
theorem key_ne {ss : Syn (.list (.part false))} (hs : StructDecode.decode C = .ok ss) {w : Name}
    (hw : C.structs.filter (·.1 == w) ≠ []) : w ≠ "" := by
  obtain ⟨entry, mem⟩ := List.exists_mem_of_ne_nil _ hw
  obtain ⟨inTable, key⟩ := List.mem_filter.1 mem
  obtain ⟨_, _, _, ne⟩ := (StructDecode.decode_ok_iff C).1 ⟨ss, hs⟩ entry inTable
  exact (show entry.1 = w by simpa using key) ▸ ne

/-- **Resolution in the unit**: a name the table declares once, carried by no root or
function entry, denotes exactly its entry's generated declaration. -/
theorem build_resolved (h : build T R C scope fs = .ok u) {w : Name}
    (one : (C.structs.filter (·.1 == w)).length = 1) (apart : Apart C fs w) :
    ∃ e d, lookupBy w C.structs = some e ∧ Gen C scope (w, e) d ∧
      u.env.lookup (some scope) w = [d] ∧ Resolved u.env (some scope) w ⟨some scope, w⟩ := by
  obtain ⟨ss, pre, post, hs, hE, free⟩ := build_split h
  have ne : C.structs.filter (·.1 == w) ≠ [] := fun e => by simp [e] at one
  exact StructDecode.resolved hs hE one (free w (key_ne hs ne) apart)

/-- **Only then**: a name with an entry that resolves is declared once and apart; a
repeated name, or one a root or function carries, does not resolve. -/
theorem build_resolved_only (h : build T R C scope fs = .ok u) {w : Name}
    (hw : C.structs.filter (·.1 == w) ≠ []) (r : ∃ d, Resolved u.env (some scope) w d) :
    (C.structs.filter (·.1 == w)).length = 1 ∧ Apart C fs w := by
  obtain ⟨k, ss, st, ctors, functions, -, -, hs, hst, -, hf, hd, -, hfs⟩ := build_decls h
  have hE : u.env.decls = [k] ++ ss.collect (some scope) ++
      (ctors ++ st.collect (some scope) ++ functions.collect (some scope)) := by rw [hd]; simp
  obtain ⟨one, free⟩ := StructDecode.resolved_only hs hE hw r
  refine ⟨one, fun v mv hv => ?_, fun f mf src hsrc hn => ?_⟩
  · obtain ⟨d, md, _, _, _, _, hd⟩ := ordered_mem_left
      (ReferenceStateDecode.partsOf_faithful scope _ _ st hst).1 v mv
    exact free d (by simp [md]) (by rw [hd]; exact ⟨rfl, hv⟩)
  · have hm : fromMetadata T R scope f.2 ∈ (functions.collect (some scope)).map some := by
      rw [hfs]; exact List.mem_map_of_mem mf
    obtain ⟨d, md, hd'⟩ := List.mem_map.mp hm
    obtain ⟨src', _, hs'', _, _, hn', sc⟩ := Callee.fromMetadata_header hd'.symm
    rw [hsrc, Option.some.injEq] at hs''
    subst hs''
    exact free d (by simp [md]) ⟨sc, hn' ▸ hn⟩
where
  ordered_mem_left {α β : Type} {r : α → β → Prop} :
      ∀ {as : List α} {bs : List β}, Ordered r as bs → ∀ a ∈ as, ∃ b ∈ bs, r a b
    | _, _, .nil, _, ha => by cases ha
    | _, _, .cons h t, a, ha => by
        rcases List.mem_cons.mp ha with rfl | ha
        · exact ⟨_, List.mem_cons_self, h⟩
        · obtain ⟨b, hb, h'⟩ := ordered_mem_left t a ha
          exact ⟨b, List.mem_cons_of_mem _ hb, h'⟩

/-- **Struct fields in the unit**: `structFields_closed`, its noninterference derived from
every declared name being `Apart`; `Declared` and `here` remain hypotheses. -/
theorem build_structFields (h : build T R C scope fs = .ok u)
    (apart : ∀ w e, lookupBy w C.structs = some e → Apart C fs w) {w e : Name}
    (hw : lookupBy w C.structs = some e) (dec : Declared C e) (loc : Source.DataLoc)
    (here : ∀ x ∈ structDef e, loc = .storage ∨ StructDecode.maplessTy x.2 = true) :
    Fields C u.env scope loc e (u.env.structFields ⟨some scope, w⟩ loc) := by
  obtain ⟨ss, pre, post, hs, hE, free⟩ := build_split h
  refine StructDecode.structFields_closed hs hE (fun d md sc => ?_) hw dec loc here
  cases hl : lookupBy d.name C.structs with
  | none => rfl
  | some e' =>
    have ne : C.structs.filter (·.1 == d.name) ≠ [] := by
      rw [StructDecode.lookupBy_filter] at hl
      intro em; rw [em] at hl; cases hl
    exact absurd ⟨sc, rfl⟩ (free d.name (key_ne hs ne) (apart _ _ hl) d md)

/-- **Declared types of the roots**, reference roots included: the resolution
obligation discharged by `build_resolved` for every struct a root mentions. -/
theorem build_typed (h : build T R C scope fs = .ok u)
    (named : ∀ v ∈ C.vars, ∀ s ∈ structsTy v.2, ∀ w, written? C s = some w →
      (C.structs.filter (·.1 == w)).length = 1 ∧ Apart C fs w) :
    Ordered (TypedRoot C (TransientDecode.elemOf C) (trOf C) u.env scope) C.vars
      (u.env.stateVarsOf scope) := by
  obtain ⟨st, hs, hv⟩ := build_stateVarsOf h
  rw [hv]
  refine ReferenceStateDecode.partsOf_typed scope hs fun v mv s ms w hw => ?_
  obtain ⟨one, apart⟩ := named v mv s ms w hw
  obtain ⟨_, _, _, _, _, r⟩ := build_resolved h one apart
  exact ⟨_, r⟩

/-! ## Components: refusals and the struct-free unit -/

theorem build_structs_error {e : StructDecode.Error} (hs : StructDecode.decode C = .error e) :
    build T R C scope fs = .error (.structs e) := by
  simp only [build, hs]

theorem build_placement_error {ss : Syn (.list (.part false))} {e : ReferenceStatePlacement.Error}
    (hs : StructDecode.decode C = .ok ss) (hp : prefixParts T R C = .error e) :
    build T R C scope fs = .error (.placement e) := by
  simp only [build, hs, hp]

theorem build_functions_error {ss p : Syn (.list (.part false))}
    (hs : StructDecode.decode C = .ok ss) (hp : prefixParts T R C = .ok p)
    (hf : functionParts T R scope fs = none) : build T R C scope fs = .error .functions := by
  simp only [build, hs, hp, withFunctions, hf, Option.bind_eq_bind, Option.bind_none]

/-- With no struct entry, a unit `assemble` produces is `build`'s. -/
theorem build_of_assemble (hs : C.structs = [])
    (ha : assemble T R C scope fs = .ok u) : build T R C scope fs = .ok u := by
  obtain ⟨p, hp, hu⟩ := ReferenceStatePlacement.assemble_ok ha
  simp only [build, StructDecode.decode, hs, StructDecode.parts, hp, appendParts, hu]

end Solidity.Correctness.Lowering.Total.StructUnit
