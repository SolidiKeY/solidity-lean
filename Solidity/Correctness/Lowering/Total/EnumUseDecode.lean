import Solidity.Correctness.Lowering.Total.EnumDecode
import Solidity.Syntax.Elab.Values

/-!
# Decoding enum member expressions into Source

The expression-level enum component `EnumDecode` leaves open: the raw
elaborator reads `E.m`, `type(E).min` and `type(E).max` through
`Solidity.enumLit?` (an unshadowed enum of the contract, then the member's
position, `0`, or the last position), and erases the result to a `uint`
literal. This module reads those uses back as Source.

- `Form` classifies the field name `enumLit?` inspects (`Form.ofField`), and
  `Form.read` is its ordinal reading of an ordered member list.
- `enumLit?_eq` is the exact reading of `enumLit?` on every input: `none` on a
  non-name base and on a local or state-variable shadow, otherwise the raw
  table's ordinal; `enumLit?_member`, `enumLit?_min`, `enumLit?_max` and the
  failures (`enumLit?_shadow_local`, `enumLit?_shadow_state`, `enumLit?_absent`,
  `enumLit?_empty`) specialize it.
- `Form.spell` is the Source spelling (`E.m`, `type(E).min`, `type(E).max`);
  `ordinalSpell` is the conversion `E(i)` S01 types.
- On a decoded table (`EnumDecode.decode`) placed in the Source environment
  of the contract scope beside only non-enum declarations, `sourceRead_eq`
  transports the ordinal to the Source member list, and the minimum and
  maximum exist exactly for the enums the table has (`sourceRead_min_isSome`).
- Under the explicit raw/Source scope alignment `Aligned`, a successful
  `enumLit?` gives actual Source name resolution of `E` to its single enum
  declaration (`resolve_eq`), S01's conversion target (`convTarget_eq`), a
  `Typed` derivation of `E(i)` at the enum type (`typedOrdinal`), an ordinal
  below the Source layout's member count, and the enum value `Val.enum` whose
  key is the ordinal and which `enumOfInt` produces (`decode_use`).
- A Source local of the name resolves to the local, and a same-scope
  declaration beside the enum makes the name ambiguous: neither is a
  conversion target (`convTarget_local`, `convTarget_shadow`).
- S01 types neither a member access on an enum name (`spell_member_untyped`)
  nor `type(T).min`/`type(T).max` (`spell_bound_untyped`, the S04.02 gap), so
  the typed Source reading of every form is the conversion spelling.

Not established here: reconstruction of enum-typed variables (erased to
`uint` by the raw elaborator, so no enum identity is read from a plain
`uint`), general conversions, whole-unit coverage and execution simulation;
those stay with the complete-unit decoder.
-/
namespace Solidity.Correctness.Lowering.Total.EnumUseDecode

open Solidity.Semantics (lookupBy)
open Solidity.Correctness.Lowering.Total.EnumDecode

/-! ## The forms `enumLit?` reads -/

/-- The enum use a field name spells: a member `E.m`, or the macro's
`type(min)` / `type(max)` fields for `type(E).min` / `type(E).max`. -/
inductive Form where
  | member (m : String)
  | min
  | max
  deriving DecidableEq, Repr

/-- The form of a raw field name, as `enumLit?` tests it. -/
def Form.ofField (m : String) : Form :=
  if m == "type(min)" then .min else if m == "type(max)" then .max else .member m

/-- The raw field name of a form. -/
def Form.field : Form → String
  | .member m => m
  | .min => "type(min)"
  | .max => "type(max)"

/-- The ordinal a form denotes in an ordered member list. -/
def Form.read : Form → List String → Option Nat
  | .member m, ms => ms.findIdx? (· == m)
  | .min, ms => if ms.isEmpty then none else some 0
  | .max, ms => if ms.isEmpty then none else some (ms.length - 1)

/-- The raw spelling of a form on the name `x`. -/
def Form.raw (x : Name) (f : Form) : RawExpr := .field (.name x) f.field

/-- The Source spelling: `E.m`, `type(E).min`, `type(E).max`. -/
def Form.spell (x : String) : Form → Source.Syn .expr
  | .member m => .member (.ident x) m
  | .min => .member (.metaType (.userType ⟨x, []⟩)) "min"
  | .max => .member (.metaType (.userType ⟨x, []⟩)) "max"

/-- The Source conversion `E(i)` of the ordinal `i`, the spelling S01 types. -/
def ordinalSpell (x : String) (i : Nat) : Source.Syn .expr :=
  .call (.ident x) (.positional (.cons (.lit (.num (.dec i 0 0))) .nil))

theorem Form.ofField_field_min : Form.ofField Form.min.field = .min := rfl
theorem Form.ofField_field_max : Form.ofField Form.max.field = .max := rfl

/-- A member name that is not one of the macro's reserved fields reads as
itself (no Solidity identifier contains parentheses). -/
theorem Form.ofField_member {m : String} (h₁ : m ≠ "type(min)") (h₂ : m ≠ "type(max)") :
    Form.ofField m = .member m := by
  simp [Form.ofField, h₁, h₂]

theorem Form.read_lt {f : Form} {ms : List String} {i : Nat} (h : f.read ms = some i) :
    i < ms.length := by
  cases f with
  | member m =>
    simp only [Form.read] at h
    exact List.findIdx?_eq_some_iff_findIdx_eq.mp h |>.1
  | min =>
    cases ms <;> simp_all [Form.read]
    omega
  | max =>
    cases ms <;> simp_all [Form.read]

section RawReading

variable [FreshNames]

/-! ## The exact reading of `enumLit?` -/

/-- The raw shadowing test of `enumLit?`: a local or a state variable named `x`. -/
def Shadowed (C : Contract) (Γ : NCtx) (x : Name) : Bool :=
  (Γ.lookupTy (Var.ofName x)).isSome || (C.rootType x).isSome

/-- **The reading of `enumLit?`**, on every input: a non-name base and a
shadowed name read nothing; otherwise the raw table's enum named `x` is read
at the form of the field. -/
theorem enumLit?_eq (C : Contract) (Γ : NCtx) (e : RawExpr) (m : String) :
    enumLit? C Γ e m =
      match e with
      | .name x => if Shadowed C Γ x then none else
          (lookupBy x C.enums).bind (Form.ofField m).read
      | _ => none := by
  cases e with
  | name x =>
    have hread : ∀ ms : List String,
        (if m == "type(min)" then (if ms.isEmpty then none else some 0)
          else if m == "type(max)" then (if ms.isEmpty then none else some (ms.length - 1))
          else ms.findIdx? (· == m)) = (Form.ofField m).read ms := by
      intro ms
      unfold Form.ofField
      by_cases h₁ : m == "type(min)" <;> by_cases h₂ : m == "type(max)" <;> simp [h₁, h₂, Form.read]
    simp only [enumLit?, Shadowed, hread]
    split <;> split <;> simp_all [Option.isNone_iff_eq_none, Option.isSome_iff_ne_none]
  | _ => rfl

/-- `E.m` for a member name: the raw member index. -/
theorem enumLit?_member (C : Contract) (Γ : NCtx) {x : Name} {m : String}
    (hs : Shadowed C Γ x = false) (h₁ : m ≠ "type(min)") (h₂ : m ≠ "type(max)") :
    enumLit? C Γ (.name x) m = rawMember? C x m := by
  rw [enumLit?_eq]
  simp only [hs, Form.ofField_member h₁ h₂, rawMember?, Bool.false_eq_true, if_false]
  rfl

/-- `type(E).min`: position `0` of a nonempty member list. -/
theorem enumLit?_min (C : Contract) (Γ : NCtx) {x : Name} {ms : List Name}
    (hs : Shadowed C Γ x = false) (hl : lookupBy x C.enums = some ms) (hne : ms ≠ []) :
    enumLit? C Γ (.name x) "type(min)" = some 0 := by
  rw [enumLit?_eq]
  simp [hs, hl, Form.ofField, Form.read, hne]

/-- `type(E).max`: the last position of a nonempty member list. -/
theorem enumLit?_max (C : Contract) (Γ : NCtx) {x : Name} {ms : List Name}
    (hs : Shadowed C Γ x = false) (hl : lookupBy x C.enums = some ms) (hne : ms ≠ []) :
    enumLit? C Γ (.name x) "type(max)" = some (ms.length - 1) := by
  rw [enumLit?_eq]
  simp [hs, hl, Form.ofField, Form.read, hne]

/-- A local named `x` shadows the enum: nothing is read. -/
theorem enumLit?_shadow_local (C : Contract) (Γ : NCtx) {x : Name} {m : String} {t : LTy}
    (h : Γ.lookupTy (Var.ofName x) = some t) : enumLit? C Γ (.name x) m = none := by
  rw [enumLit?_eq]
  simp [Shadowed, h]

/-- A state variable named `x` shadows the enum: nothing is read. -/
theorem enumLit?_shadow_state (C : Contract) (Γ : NCtx) {x : Name} {m : String} {T : Ty}
    (h : C.rootType x = some T) : enumLit? C Γ (.name x) m = none := by
  rw [enumLit?_eq]
  simp [Shadowed, h]

/-- No enum named `x`: nothing is read. -/
theorem enumLit?_absent (C : Contract) (Γ : NCtx) {x : Name} {m : String}
    (h : lookupBy x C.enums = none) : enumLit? C Γ (.name x) m = none := by
  rw [enumLit?_eq]
  simp [h]

/-- An empty enum table reads nothing. -/
theorem enumLit?_empty (C : Contract) (Γ : NCtx) (e : RawExpr) (m : String)
    (h : C.enums = []) : enumLit? C Γ e m = none := by
  rw [enumLit?_eq]
  cases e <;> simp [h, lookupBy]

/-- A successful read is of an unshadowed name with an enum entry, at an
ordinal below its member count. -/
theorem enumLit?_some {C : Contract} {Γ : NCtx} {e : RawExpr} {m : String} {i : Nat}
    (h : enumLit? C Γ e m = some i) :
    ∃ x ms, e = .name x ∧ Shadowed C Γ x = false ∧ lookupBy x C.enums = some ms ∧
      (Form.ofField m).read ms = some i ∧ i < ms.length := by
  rw [enumLit?_eq] at h
  cases e with
  | name x =>
    simp only at h
    cases hs : Shadowed C Γ x with
    | true => simp [hs] at h
    | false =>
      simp only [hs, Bool.false_eq_true, if_false] at h
      cases hl : lookupBy x C.enums with
      | none => simp [hl] at h
      | some ms =>
        simp only [hl, Option.bind_some] at h
        exact ⟨x, ms, rfl, hs, hl, h, Form.read_lt h⟩
  | _ => simp at h

end RawReading

/-! ## The Source reading on a decoded table -/

/-- The Source reading of a form: the enum's Source member list, read at the form. -/
def sourceRead (E : Source.Env) (dn : Source.DeclName) (f : Form) : Option Nat :=
  (sourceMembers E dn).bind f.read

/-- **Source and raw readings agree** in an environment that adds only
non-enum declarations around the decoded ones: members, minimum and maximum,
absent enums and absent members included. -/
theorem sourceRead_eq {C : Contract} {ps : Source.Syn (.list (.part false))}
    (h : decode C = .ok ps) {s : String} {E : Source.Env} {pre post : List Source.Decl}
    (hE : E.decls = pre ++ ps.collect (some s) ++ post)
    (hpre : ∀ d ∈ pre, d.kind ≠ .enum) (hpost : ∀ d ∈ post, d.kind ≠ .enum) (x : Name) (f : Form) :
    sourceRead E ⟨some s, x⟩ f = (lookupBy x C.enums).bind f.read := by
  simp only [sourceRead, sourceMembers_eq h hE hpre hpost x]

/-- On a decoded table the minimum and maximum exist exactly for the enums
the table has: decoding rules out the empty member list. -/
theorem sourceRead_min_isSome {C : Contract} {ps : Source.Syn (.list (.part false))}
    (h : decode C = .ok ps) {s : String} {E : Source.Env} {pre post : List Source.Decl}
    (hE : E.decls = pre ++ ps.collect (some s) ++ post)
    (hpre : ∀ d ∈ pre, d.kind ≠ .enum) (hpost : ∀ d ∈ post, d.kind ≠ .enum) (x : Name) :
    (sourceRead E ⟨some s, x⟩ .min).isSome = (lookupBy x C.enums).isSome ∧
      (sourceRead E ⟨some s, x⟩ .max).isSome = (lookupBy x C.enums).isSome := by
  rw [sourceRead_eq h hE hpre hpost, sourceRead_eq h hE hpre hpost]
  cases hl : lookupBy x C.enums with
  | none => simp
  | some ms =>
    have hne : ms ≠ [] :=
      (decode_ok_iff C).mp ⟨ps, h⟩ (x, ms) (Semantics.lookupBy_eq_some_mem hl)
    cases ms with
    | nil => exact absurd rfl hne
    | cons _ _ => simp [Form.read]

/-! ## Decoded declarations, lookup and the typed conversion -/

/-- The enum declaration decoding produces for the entry `(x, f :: r)`. -/
def enumDecl (s x f : String) (r : List String) : Source.Decl :=
  ⟨.enum, x, some s, false, .enum x f r⟩

private theorem collect_mem (s : String) :
    ∀ (i : Nat) (es : List (Name × List Name)) (ps : Source.Syn (.list (.part false))),
      decodeList i es = .ok ps → ∀ d ∈ ps.collect (some s),
        ∃ f r, d = enumDecl s d.name f r ∧ (d.name, f :: r) ∈ es
  | _, [], ps, h, d, hd => by
    simp only [decodeList, Except.ok.injEq] at h
    subst h
    simp [Source.Syn.collect] at hd
  | _, (n, []) :: _, _, h, _, _ => by simp [decodeList] at h
  | i, (n, m :: ms) :: es, ps, h, d, hd => by
    cases hr : decodeList (i + 1) es with
    | error err => simp [decodeList, hr, bind, Except.bind] at h
    | ok qs =>
      simp only [decodeList, hr, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
      subst h
      simp only [Source.Syn.collect, List.cons_append, List.nil_append, List.mem_cons] at hd
      rcases hd with rfl | hd
      · exact ⟨m, ms, rfl, List.mem_cons_self⟩
      · obtain ⟨f, r, hf, hmem⟩ := collect_mem s (i + 1) es qs hr d hd
        exact ⟨f, r, hf, List.mem_cons_of_mem _ hmem⟩

private theorem collect_filter (s x : String) (hx : x ≠ "") :
    ∀ (i : Nat) (es : List (Name × List Name)) (ps : Source.Syn (.list (.part false))),
      decodeList i es = .ok ps → es.Pairwise (fun a b => a.1 ≠ b.1) →
      ∀ ms, lookupBy x es = some ms → ∃ f r, ms = f :: r ∧
        (ps.collect (some s)).filter (fun d => d.scope == some s && d.name == x && x != "") =
          [enumDecl s x f r]
  | _, [], _, _, _, ms, hl => by simp [lookupBy] at hl
  | _, (n, []) :: _, _, h, _, _, _ => by simp [decodeList] at h
  | i, (n, m :: ms') :: es, ps, h, hd, ms, hl => by
    cases hr : decodeList (i + 1) es with
    | error err => simp [decodeList, hr, bind, Except.bind] at h
    | ok qs =>
      simp only [decodeList, hr, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
      subst h
      have hd' := List.pairwise_cons.mp hd
      by_cases hn : x = n
      · subst hn
        simp only [lookupBy, ↓reduceIte, Option.some.injEq] at hl
        subst hl
        refine ⟨m, ms', rfl, ?_⟩
        have hnone : (qs.collect (some s)).filter
            (fun d => d.scope == some s && d.name == x && x != "") = [] := by
          rw [List.filter_eq_nil_iff]
          intro d hdm
          obtain ⟨f, r, _, hmem⟩ := collect_mem s (i + 1) es qs hr d hdm
          have h2 : d.name ≠ x := fun e => hd'.1 _ hmem (by simp [e])
          simp [h2]
        simp [Source.Syn.collect, enumDecl, hnone, hx]
      · have hl' : lookupBy x es = some ms := by simpa [lookupBy, hn] using hl
        obtain ⟨f, r, hms, hf⟩ := collect_filter s x hx (i + 1) es qs hr hd'.2 ms hl'
        refine ⟨f, r, hms, ?_⟩
        simp [Source.Syn.collect, Ne.symm hn, hf]

private theorem linearize_head (E : Source.Env) (c : String) :
    ∃ rest, (E.linearize c).getD [c] = c :: rest := by
  unfold Source.Env.linearize
  rw [Source.Env.linearizeF]
  split
  · exact ⟨[], rfl⟩
  · cases Source.Env.merge _ _ with
    | none => exact ⟨[], rfl⟩
    | some l => exact ⟨l, rfl⟩

/-- Lookup in contract scope `s` of a name `s` itself declares is that
scope's declarations: the linearization starts at `s`. -/
private theorem lookup_own (E : Source.Env) (s x : String) (h : E.declared (some s) x ≠ []) :
    E.lookup (some s) x = E.declared (some s) x := by
  obtain ⟨rest, hr⟩ := linearize_head E s
  have hv : (E.declared (some s) x).filter (fun d => some s == some s || !d.isPrivate) =
      E.declared (some s) x := by simp
  have hne : (E.declared (some s) x).isEmpty = false := by
    cases hq : E.declared (some s) x with
    | nil => exact absurd hq h
    | cons _ _ => rfl
  unfold Source.Env.lookup Source.Env.visible
  simp only []
  rw [hr, List.map_cons, List.find?_cons_of_pos (by rw [hv, hne]; rfl)]
  exact hv

/-- The conversion `E(i)` is typed at the enum `E` names. -/
def typedOrdinal {Γ : Source.Ctx} {x : String} {dn : Source.DeclName}
    (h : Γ.convTarget x = some (.enum dn)) (i : Nat) :
    Source.Typed Γ (ordinalSpell x i) (.enum dn) :=
  .convUser h (.const rfl rfl rfl) (by simp [Source.STy.explicit, Source.Q.isInt, Source.Q.toInt, Source.NumLit.value])

/-! ## Source shadowing and the untyped member spelling -/

/-- A Source local named `x` shadows every declaration: `x` is no conversion
target. -/
theorem convTarget_local {Γ : Source.Ctx} {x : String} (h : x ∈ Γ.locals.map Prod.fst) :
    Γ.convTarget x = none := by
  obtain ⟨i, hi⟩ : ∃ i, (Γ.locals.map Prod.fst).idxOf? x = some i := by
    cases hq : (Γ.locals.map Prod.fst).idxOf? x with
    | none => exact absurd h (List.idxOf?_eq_none_iff.mp hq)
    | some i => exact ⟨i, rfl⟩
  simp [Source.Ctx.convTarget, Source.Ctx.resolve, Source.Env.resolve, hi]

private theorem ident_untyped {Γ : Source.Ctx} {x : String} {d : Source.Decl}
    (hres : Γ.resolve x = some (.decls [d])) (hk : d.kind = .enum) {σ : Source.STy}
    (t : Source.Typed Γ (.ident x) σ) : False := by
  have hb0 : (Source.Syn.ident x : Source.Syn .expr).binOp? = none := rfl
  have hc0 : (Source.Syn.ident x : Source.Syn .expr).const = none := rfl
  have hb : ∀ p, (Source.Syn.ident x : Source.Syn .expr).binOp? ≠ some p := by
    intro p h; rw [hb0] at h; cases h
  generalize he : (Source.Syn.ident x : Source.Syn .expr) = e at t
  cases t
  all_goals (try (cases he; done))
  all_goals cases he
  case state.refl =>
    rename_i d' hv hr
    rw [hres] at hr
    simp only [Option.some.injEq, Source.Denot.decls.injEq, List.cons.injEq, and_true] at hr
    subst hr
    obtain ⟨k, n, sc, top, node⟩ := d
    cases hk
    simp [Source.Decl.varTy] at hv
  case const.refl => rename_i hc _ _; rw [hc0] at hc; cases hc
  case loc.refl => rename_i _ hr; rw [hres] at hr; cases hr
  case this.refl => rename_i h _; rw [hres] at h; cases h
  all_goals exact absurd ‹(Source.Syn.ident x : Source.Syn .expr).binOp? = some _› (hb _)

/-- S01 types no member access on an enum name: `E.m` has no `Typed`
derivation, so the typed Source reading of a member is `ordinalSpell`. -/
theorem spell_member_untyped {Γ : Source.Ctx} {x m : String} {d : Source.Decl}
    (hres : Γ.resolve x = some (.decls [d])) (hk : d.kind = .enum) {τ : Source.STy}
    (t : Source.Typed Γ (Form.spell x (.member m)) τ) : False := by
  have hb0 : (Source.Syn.member (.ident x) m : Source.Syn .expr).binOp? = none := rfl
  have hc0 : (Source.Syn.member (.ident x) m : Source.Syn .expr).const = none := rfl
  have hb : ∀ p, (Source.Syn.member (.ident x) m : Source.Syn .expr).binOp? ≠ some p := by
    intro p h; rw [hb0] at h; cases h
  change Source.Typed Γ (.member (.ident x) m) τ at t
  generalize he : (Source.Syn.member (.ident x) m : Source.Syn .expr) = e at t
  cases t
  all_goals (try (cases he; done))
  all_goals cases he
  case const.refl => rename_i hc _ _; rw [hc0] at hc; cases hc
  case magic.refl =>
    have h := hres.symm.trans ‹Γ.resolve x = some (Source.Denot.builtin _)›
    cases h
  all_goals first
    | exact absurd ‹(Source.Syn.member (.ident x) m : Source.Syn .expr).binOp? = some _› (hb _)
    | exact ident_untyped hres hk ‹Source.Typed Γ (.ident x) _›

private theorem metaType_untyped {Γ : Source.Ctx} (tn : Source.Syn .typeName) {σ : Source.STy}
    (t : Source.Typed Γ (.metaType tn) σ) : False := by
  have hb0 : (Source.Syn.metaType tn : Source.Syn .expr).binOp? = none := rfl
  have hc0 : (Source.Syn.metaType tn : Source.Syn .expr).const = none := rfl
  have hb : ∀ p, (Source.Syn.metaType tn : Source.Syn .expr).binOp? ≠ some p := by
    intro p h; rw [hb0] at h; cases h
  generalize he : (Source.Syn.metaType tn : Source.Syn .expr) = e at t
  cases t
  all_goals (try (cases he; done))
  all_goals cases he
  case const.refl => rename_i hc _ _; rw [hc0] at hc; cases hc
  all_goals exact absurd ‹(Source.Syn.metaType tn : Source.Syn .expr).binOp? = some _› (hb _)

private theorem bound_untyped {Γ : Source.Ctx} (tn : Source.Syn .typeName) (n : String)
    (h₁ : n ≠ "length") (h₂ : n ≠ "balance") {τ : Source.STy}
    (t : Source.Typed Γ (.member (.metaType tn) n) τ) : False := by
  have hb0 : (Source.Syn.member (.metaType tn) n : Source.Syn .expr).binOp? = none := rfl
  have hc0 : (Source.Syn.member (.metaType tn) n : Source.Syn .expr).const = none := rfl
  have hb : ∀ p, (Source.Syn.member (.metaType tn) n : Source.Syn .expr).binOp? ≠ some p := by
    intro p h; rw [hb0] at h; cases h
  generalize he : (Source.Syn.member (.metaType tn) n : Source.Syn .expr) = e at t
  cases t
  all_goals (try (cases he; done))
  all_goals cases he
  case const.refl => rename_i hc _ _; rw [hc0] at hc; cases hc
  case length.refl => exact h₁ rfl
  case balance.refl => exact h₂ rfl
  case member.refl => exact metaType_untyped tn ‹Source.Typed Γ (.metaType tn) _›
  all_goals exact absurd ‹(Source.Syn.member (.metaType tn) n : Source.Syn .expr).binOp? = some _› (hb _)

/-- S01 types no `type(E).min` or `type(E).max` (`type(T)` is the recorded
S04.02 gap), in any context. -/
theorem spell_bound_untyped {Γ : Source.Ctx} {x : String} {f : Form} (hf : f = .min ∨ f = .max)
    {τ : Source.STy} (t : Source.Typed Γ (Form.spell x f) τ) : False := by
  rcases hf with rfl | rfl
  · exact bound_untyped _ "min" (by decide) (by decide) t
  · exact bound_untyped _ "max" (by decide) (by decide) t

/-! ## Under the raw/Source alignment -/

section Aligned

variable [FreshNames]

/-- **The raw/Source scope alignment** for a name `x` of contract scope `s`,
around a decoded enum table `ps` of `C`: the Source context is the scope of
the contract whose environment holds the decoded enums beside non-enum
declarations; a Source local named `x` is a raw local; a Source declaration
of scope `s` named `x` outside the enum table is a raw state variable; and
enum names are distinct and nonempty (solc: one declaration per identifier). -/
structure Aligned (C : Contract) (ps : Source.Syn (.list (.part false))) (Γr : NCtx)
    (Γs : Source.Ctx) (s : String) (pre post : List Source.Decl) (x : Name) : Prop where
  scope : Γs.scope = some s
  decls : Γs.env.decls = pre ++ ps.collect (some s) ++ post
  pre_nonEnum : ∀ d ∈ pre, d.kind ≠ .enum
  post_nonEnum : ∀ d ∈ post, d.kind ≠ .enum
  locals : x ∈ Γs.locals.map Prod.fst → (Γr.lookupTy (Var.ofName x)).isSome
  state : ∀ d ∈ pre ++ post, d.scope = some s → d.name = x → (C.rootType x).isSome
  distinct : C.enums.Pairwise fun a b => a.1 ≠ b.1
  nonempty : x ≠ ""

private theorem declared_eq {C : Contract} {ps : Source.Syn (.list (.part false))}
    {Γr : NCtx} {Γs : Source.Ctx} {s : String} {pre post : List Source.Decl} {x : Name}
    (hd : decode C = .ok ps) (hA : Aligned C ps Γr Γs s pre post x)
    (hst : C.rootType x = none) {ms : List Name} (hl : lookupBy x C.enums = some ms) :
    ∃ f r, ms = f :: r ∧ Γs.env.declared (some s) x = [enumDecl s x f r] := by
  obtain ⟨f, r, hms, hf⟩ := collect_filter s x hA.nonempty 0 C.enums ps hd hA.distinct ms hl
  refine ⟨f, r, hms, ?_⟩
  have hnone : ∀ l : List Source.Decl, (∀ d ∈ l, d ∈ pre ++ post) →
      l.filter (fun d => d.scope == some s && d.name == x && x != "") = [] := by
    intro l hl'
    rw [List.filter_eq_nil_iff]
    intro d hdm
    have := hA.state d (hl' d hdm)
    simp only [hst, Option.isSome_none, Bool.false_eq_true, imp_false] at this
    simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq]
    exact fun ⟨⟨hsc, hn⟩, _⟩ => this hsc hn
  unfold Source.Env.declared
  rw [hA.decls, List.filter_append, List.filter_append, hf,
    hnone pre (fun d h => List.mem_append_left _ h),
    hnone post (fun d h => List.mem_append_right _ h)]
  rfl

/-- **Name resolution**: under the alignment, an unshadowed raw enum name
resolves in Source to exactly its decoded enum declaration. -/
theorem resolve_eq {C : Contract} {ps : Source.Syn (.list (.part false))}
    {Γr : NCtx} {Γs : Source.Ctx} {s : String} {pre post : List Source.Decl} {x : Name}
    (hd : decode C = .ok ps) (hA : Aligned C ps Γr Γs s pre post x)
    (hs : Shadowed C Γr x = false) {ms : List Name} (hl : lookupBy x C.enums = some ms) :
    ∃ f r, ms = f :: r ∧ Γs.resolve x = some (.decls [enumDecl s x f r]) := by
  have hloc : (Γr.lookupTy (Var.ofName x)).isSome = false := by
    simp only [Shadowed, Bool.or_eq_false_iff] at hs; exact hs.1
  have hst : C.rootType x = none := by
    simp only [Shadowed, Bool.or_eq_false_iff, Option.isSome_eq_false_iff,
      Option.isNone_iff_eq_none] at hs
    exact hs.2
  obtain ⟨f, r, hms, hdecl⟩ := declared_eq hd hA hst hl
  refine ⟨f, r, hms, ?_⟩
  have hidx : (Γs.locals.map Prod.fst).idxOf? x = none := by
    rw [List.idxOf?_eq_none_iff]
    intro hm
    have := hA.locals hm
    simp_all
  have hlook : Γs.env.lookup Γs.scope x = [enumDecl s x f r] := by
    rw [hA.scope, lookup_own _ _ _ (by simp [hdecl]), hdecl]
  simp only [Source.Ctx.resolve, Source.Env.resolve, hidx, hlook]

/-- **The conversion target**: S01's `Ctx.convTarget` reads the name as the
decoded enum type. -/
theorem convTarget_eq {C : Contract} {ps : Source.Syn (.list (.part false))}
    {Γr : NCtx} {Γs : Source.Ctx} {s : String} {pre post : List Source.Decl} {x : Name}
    (hd : decode C = .ok ps) (hA : Aligned C ps Γr Γs s pre post x)
    (hs : Shadowed C Γr x = false) {ms : List Name} (hl : lookupBy x C.enums = some ms) :
    Γs.convTarget x = some (.enum ⟨some s, x⟩) := by
  obtain ⟨f, r, -, hr⟩ := resolve_eq hd hA hs hl
  simp only [Source.Ctx.convTarget, hr, enumDecl]

/-- **A successful raw enum use, read in Source.** Under the alignment, when
`enumLit?` reads `x` with field `m` as the ordinal `i`, the base is the name
`x`, and in Source: `x` resolves to its single decoded enum declaration, whose
members are the raw ones; S01's conversion target of `x` is that enum type;
the Source reading of the form is `i`; `E(i)` is typed at the enum type; `i` is
below the Source layout's member count; and the enum value of ordinal `i` has
key `i` and is the value `enumOfInt` gives `i`. -/
theorem decode_use {C : Contract} {ps : Source.Syn (.list (.part false))}
    {Γr : NCtx} {Γs : Source.Ctx} {s : String} {pre post : List Source.Decl} {x : Name}
    (hd : decode C = .ok ps) (hA : Aligned C ps Γr Γs s pre post x)
    {m : String} {i : Nat} (h : enumLit? C Γr (.name x) m = some i) :
    (∃ f r, lookupBy x C.enums = some (f :: r) ∧
      Γs.resolve x = some (.decls [enumDecl s x f r])) ∧
    Γs.convTarget x = some (.enum ⟨some s, x⟩) ∧
    sourceRead Γs.env ⟨some s, x⟩ (Form.ofField m) = some i ∧
    Nonempty (Source.Typed Γs (ordinalSpell x i) (.enum ⟨some s, x⟩)) ∧
    ∃ hi : i < Γs.env.layout.enumSize ⟨some s, x⟩,
      (Source.Val.enum ⟨i, hi⟩ : Source.Val Γs.env.layout (.enum ⟨some s, x⟩)).key = some i ∧
      Source.enumOfInt (D := Γs.env.layout) ⟨some s, x⟩ i = pure (.enum ⟨i, hi⟩) := by
  obtain ⟨x', ms, he, hs, hl, hread, hlt⟩ := enumLit?_some h
  cases he
  obtain ⟨f, r, hms, hres⟩ := resolve_eq hd hA hs hl
  subst hms
  have hconv := convTarget_eq hd hA hs hl
  have hsize : Γs.env.layout.enumSize ⟨some s, x⟩ = (f :: r).length := by
    rw [enumSize_eq hd hA.decls hA.pre_nonEnum hA.post_nonEnum x, hl]; rfl
  have hi : i < Γs.env.layout.enumSize ⟨some s, x⟩ := hsize ▸ hlt
  refine ⟨⟨f, r, hl, hres⟩, hconv, ?_, ⟨typedOrdinal hconv i⟩, hi, rfl, ?_⟩
  · rw [sourceRead_eq hd hA.decls hA.pre_nonEnum hA.post_nonEnum, hl]
    exact hread
  · simp [Source.enumOfInt, hi]

/-- A declaration of the contract scope named `x` beside its enum (solc's
state-variable shadow, refused there) makes the name ambiguous: `x` is no
conversion target. -/
theorem convTarget_shadow {C : Contract} {ps : Source.Syn (.list (.part false))}
    {Γr : NCtx} {Γs : Source.Ctx} {s : String} {pre post : List Source.Decl} {x : Name}
    (hd : decode C = .ok ps) (hA : Aligned C ps Γr Γs s pre post x)
    (hloc : x ∉ Γs.locals.map Prod.fst) {ms : List Name} (hl : lookupBy x C.enums = some ms)
    {d : Source.Decl} (hdm : d ∈ pre ++ post) (hsc : d.scope = some s) (hn : d.name = x) :
    Γs.convTarget x = none := by
  obtain ⟨f, r, -, hf⟩ := collect_filter s x hA.nonempty 0 C.enums ps hd hA.distinct ms hl
  let p : Source.Decl → Bool := fun d => d.scope == some s && d.name == x && x != ""
  have hpd : p d = true := by simp [p, hsc, hn, hA.nonempty]
  have hdecl : Γs.env.declared (some s) x =
      pre.filter p ++ [enumDecl s x f r] ++ post.filter p := by
    unfold Source.Env.declared
    rw [hA.decls, List.filter_append, List.filter_append, hf]
  have hlen : 2 ≤ (Γs.env.declared (some s) x).length := by
    rw [hdecl]
    rcases List.mem_append.mp hdm with hm | hm
    · have : 0 < (pre.filter p).length :=
        List.length_pos_of_mem (List.mem_filter.mpr ⟨hm, hpd⟩)
      simp only [List.length_append, List.length_singleton]; omega
    · have : 0 < (post.filter p).length :=
        List.length_pos_of_mem (List.mem_filter.mpr ⟨hm, hpd⟩)
      simp only [List.length_append, List.length_singleton]; omega
  have hidx : (Γs.locals.map Prod.fst).idxOf? x = none := List.idxOf?_eq_none_iff.mpr hloc
  have hlook : Γs.env.lookup Γs.scope x = Γs.env.declared (some s) x := by
    rw [hA.scope, lookup_own]
    intro h0; rw [h0] at hlen; simp at hlen
  unfold Source.Ctx.convTarget Source.Ctx.resolve Source.Env.resolve
  rw [hidx]
  simp only [hlook]
  match hq : Γs.env.declared (some s) x, hlen with
  | _ :: _ :: _, _ => rfl

end Aligned

end Solidity.Correctness.Lowering.Total.EnumUseDecode
