import Solidity.Correctness.Lowering.Total.EnumDecode
import Solidity.Syntax.Elab.Values

/-!
# Decoding enum member expressions into Source

`EnumDecode` leaves enum uses open. The raw elaborator reads `E.m`,
`type(E).min` and `type(E).max` through `Solidity.enumLit?` and erases the
ordinal to a `uint` literal; here those uses are read back as Source.

- `enumLit?_eq`: the exact reading of `enumLit?` on every input (`Form.ofField`
  classifies the field, `Form.read` reads an ordered member list): `none` on a
  non-name base, a local or state shadow, an absent enum or member, a memberless
  enum's bounds.
- `Form.spell` is the Source spelling of each form. S01's `Typed` has no rule
  for a member access on an enum name, and `type(T)` is the ledger's S04.02
  gap, so the typed stand-in is the conversion `E(i)` (`ordinalSpell`).
- `sourceRead_eq`: on a decoded table the Source member lists give the same
  readings (`sourceRead_bounds`: decoded enums always have bounds).
- Under the explicit raw/Source alignment `Aligned`, `decode_use`: a successful
  `enumLit?` gives Source resolution of `E` to its single decoded declaration,
  S01's conversion target, the Source reading, a `Typed` `E(i)`, an ordinal
  below the layout's member count, and the enum value `enumOfInt` gives the
  ordinal (the value S01's constant conversion produces, `Value.lean`).
  A Source local hides the enum (`convTarget_local`).

Not established: enum-typed variables (erased to `uint`, so no enum identity
is read from a plain `uint`), general conversions, evaluation of `E(i)`,
whole-unit coverage and execution simulation.
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

/-- The ordinal a form denotes in an ordered member list. -/
def Form.read : Form → List String → Option Nat
  | .member m, ms => ms.findIdx? (· == m)
  | .min, ms => if ms.isEmpty then none else some 0
  | .max, ms => if ms.isEmpty then none else some (ms.length - 1)

/-- The Source spelling: `E.m`, `type(E).min`, `type(E).max`. -/
def Form.spell (x : String) : Form → Source.Syn .expr
  | .member m => .member (.ident x) m
  | .min => .member (.metaType (.userType ⟨x, []⟩)) "min"
  | .max => .member (.metaType (.userType ⟨x, []⟩)) "max"

/-- The conversion `E(i)`: S01's typed stand-in for a form read as `i`. -/
def ordinalSpell (x : String) (i : Nat) : Source.Syn .expr :=
  .call (.ident x) (.positional (.cons (.lit (.num (.dec i 0 0))) .nil))

/-- A member name that is not one of the macro's reserved fields reads as
itself (no Solidity identifier contains parentheses). -/
theorem Form.ofField_member {m : String} (h₁ : m ≠ "type(min)") (h₂ : m ≠ "type(max)") :
    Form.ofField m = .member m := by
  simp [Form.ofField, h₁, h₂]

/-- A read ordinal is a position of the list. -/
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

/-- A local or a state variable named `x` shadows the enum: nothing is read. -/
theorem enumLit?_shadowed (C : Contract) (Γ : NCtx) {x : Name} {m : String}
    (h : Shadowed C Γ x = true) : enumLit? C Γ (.name x) m = none := by
  rw [enumLit?_eq]; simp [h]

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
theorem sourceRead_bounds {C : Contract} {ps : Source.Syn (.list (.part false))}
    (h : decode C = .ok ps) {s : String} {E : Source.Env} {pre post : List Source.Decl}
    (hE : E.decls = pre ++ ps.collect (some s) ++ post)
    (hpre : ∀ d ∈ pre, d.kind ≠ .enum) (hpost : ∀ d ∈ post, d.kind ≠ .enum) (x : Name) :
    (sourceRead E ⟨some s, x⟩ .min).isSome = (lookupBy x C.enums).isSome ∧
      (sourceRead E ⟨some s, x⟩ .max).isSome = (lookupBy x C.enums).isSome := by
  rw [sourceRead_eq h hE hpre hpost, sourceRead_eq h hE hpre hpost]
  cases hl : lookupBy x C.enums with
  | none => simp
  | some ms => cases ms with
    | nil => exact absurd rfl ((decode_ok_iff C).mp ⟨ps, h⟩ _ (Semantics.lookupBy_eq_some_mem hl))
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

/-! ## Source shadowing -/

/-- A Source local named `x` shadows every declaration: `x` is no conversion
target. -/
theorem convTarget_local {Γ : Source.Ctx} {x : String} (h : x ∈ Γ.locals.map Prod.fst) :
    Γ.convTarget x = none := by
  obtain ⟨i, hi⟩ : ∃ i, (Γ.locals.map Prod.fst).idxOf? x = some i := by
    cases hq : (Γ.locals.map Prod.fst).idxOf? x with
    | none => exact absurd h (List.idxOf?_eq_none_iff.mp hq)
    | some i => exact ⟨i, rfl⟩
  simp [Source.Ctx.convTarget, Source.Ctx.resolve, Source.Env.resolve, hi]

/-! ## Under the raw/Source alignment -/

section Aligned

variable [FreshNames]

/-- **The raw/Source scope alignment** for the name `x` in contract `s`: the
Source context is a body of `s` whose environment holds the decoded enums `ps`
of `C` beside non-enum declarations; a Source local `x` is a raw local; a
Source declaration of scope `s` named `x` outside the table is a raw state
variable (solc refuses any other redeclaration); the raw enum names are
distinct (solc well-formedness, not derived from `EnumDecode`); `x ≠ ""`. -/
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
the Source reading of the form is `i`; the stand-in `E(i)` is typed at the enum
type; `i` is below the Source layout's member count; and `enumOfInt` at `i`
gives the enum value of ordinal `i`, whose key is `i`. -/
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

end Aligned

end Solidity.Correctness.Lowering.Total.EnumUseDecode
