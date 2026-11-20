import Solidity.Correctness.Lowering.Total.Boundary

/-!
# Loop lowering: the boundaries of decoder versions (H1258, H1265)

The landed boundary (`Total.Boundary`) is for the landed decoder and is kept
as it is. This module gives decoder versions (`Decode.Tables`) one state
relation and a boundary each, beside it. The versions so far are the
width-aware `Decode.tablesW` and the address-aware `Decode.tablesA`:

* `Version.Relation.ValRel`, `Version.rel`: a model primitive is related to a
  Source Boolean, to a Source integer of the same sign holding the same
  number, at whatever width the decoder gave the slot, or (a `uint`) to the
  Source address with that number. Globals as in
  `loopRel`: primitive state variables of the running account, `msg.value`,
  the timestamp, a writable checking frame.
* `Version.Sound`: what a version's tables must satisfy (`soundW`, `soundA`).
* `Version.initialMatchingAt`: total initial matching for every sound version,
  proved: every admitted
  Source execution of a successful decoded request has a related model state
  under the positional map. It is Source-to-model only. The converse fails at
  a narrow slot: a model `uint` holding 300 where the decoder says `uint8` has
  no related Source value, and nothing here claims it has.
* `Version.boundaryAt`, `residualAt_iff`, `contractV2At_iff`: a version's
  boundary with association `SpellsT`, and what the contract and its version 2
  ask at it; `boundary` and `boundaryA` are the two instances.

The relation does not tie a slot's Source width to the model's declared width:
only the decoder does, and the model context of a request has erased it. The
policies, the simulation and the allocation trace are the landed ones, with
the defects listed in `Total.Boundary`. No goal is stated here.

Limits. Every version still has gaps (the address-aware one reads marked
locals and state variables and the name `address`, but no address
expression): `bytesN`, enums,
function types, references, calls and callee bodies, return slots,
`unchecked`/`checked` scopes, `msg.sender` and `address(this)`, and contracts
with functions, a constructor, initializers or transient roots. So the first
conjunct of `residual_iff` (the decoder is defined on every successful
request) is not provable for it, and the contract at this boundary cannot be
the goal yet. A local the elaborator declares without a type marker is decoded
as a plain integer even if it was declared `address` or `bytesN`
(`Decode.localTyW`): a possibly wrong Source type, not a gap.

Bridge to the landed boundary: at the landed tables the generic decoder and
spelling relation are the landed ones (`Decode.decode_tables1`,
`spellsT_tables1`).
-/
namespace Solidity.Correctness.Lowering.Total

open Solidity.Roadmap.G49Final

namespace Version

open Simulation (StateRelation Positional InitialMatching lookup_of_mem wordDenote)

/-! ## The state relation -/

namespace Relation

/-- A model primitive value and the Source value it stands for: the same
Boolean, or the same number at an integer type of the primitive's sign. -/
inductive ValRel (D : Source.Layout) :
    (τ : Source.STy) → (p : PrimTy) → Source.Val D τ → p.Denote → Prop where
  | bool (b : Bool) : ValRel D .bool .bool (.bool b) b
  | uint (t : Source.IntTy) (unsigned : t.signed = false) (n : Int) (h : t.lo ≤ n ∧ n ≤ t.hi)
      (x : PrimTy.uint.Denote) (same : x.1 = n) : ValRel D (.int t) .uint (.int n h) x
  | int (t : Source.IntTy) (signed : t.signed = true) (n : Int) (h : t.lo ≤ n ∧ n ≤ t.hi)
      (x : PrimTy.int.Denote) (same : x.1 = n) : ValRel D (.int t) .int (.int n h) x
  | address (payable : Bool) (a : Roadmap.Address) (x : PrimTy.uint.Denote)
      (same : x.1 = (a.val : Int)) : ValRel D (.address payable) .uint (.address a) x

/-- Values: primitives only. -/
def val (E : Source.Env) (C : Contract) (H : HTy) (τ : Source.STy) :
    (u : LTy) → Source.Val E.layout τ → u.TDenote C H → Prop
  | .val p, v, x => ValRel E.layout τ p v x
  | _, _, _ => False

/-- One state variable: a primitive holds related values at its path. -/
def field {D : Source.Layout} (read : Source.SPath → Option ((τ : Source.STy) × Source.Val D τ))
    (x : Name) : {T : Ty} → SVal T → Prop
  | _, .prim (p := p) w =>
    ∃ (τ : Source.STy) (v : Source.Val D τ),
      read ⟨⟨some Decode.contractName, x⟩, []⟩ = some ⟨τ, v⟩ ∧ ValRel D τ p v w
  | _, _ => False

/-- Every state variable, in declaration order. -/
def fields {D : Source.Layout} (read : Source.SPath → Option ((τ : Source.STy) × Source.Val D τ)) :
    {fs : List (Name × Ty)} → SFields fs → Prop
  | _, .nil => True
  | _, .cons (f := x) v rest => field read x v ∧ fields read rest

/-- Globals: storage of the running account, `msg.value`, the timestamp, and a
Source frame that may write and checks arithmetic, as the model always does. -/
def glob (E : Source.Env) (C : Contract) (G : Source.Glob E) (F : Source.Fr) (st : Source.St E)
    (σ : State C []) : Prop :=
  fields (fun p => ((st.ex.world.accounts F.this).storage.read p).map fun v => ⟨_, v⟩) σ.storage ∧
  σ.tx.msgValue.1 = (F.value.val : Int) ∧ σ.tx.timestamp.1 = (G.timestamp.val : Int) ∧
  F.static = false ∧ F.checked = true

end Relation

/-- Every model primitive has a related Source value at the full-width type. -/
theorem Relation.val_total (E : Source.Env) (C : Contract) (H : HTy) : (p : PrimTy) →
    (x : p.Denote) → ∃ v, Relation.val E C H (Source.Agreement.sourceTy p) (.val p) v x
  | .bool, b => ⟨.bool b, .bool b⟩
  | .uint, x => ⟨.int x.1 ((Source.Agreement.uint_range x.1).mp x.2),
      .uint Source.IntTy.u256 rfl _ _ x rfl⟩
  | .int, x => ⟨.int x.1 ((Source.Agreement.int_range x.1).mp x.2),
      .int { Source.IntTy.u256 with signed := true } rfl _ _ x rfl⟩

/-- The state relation. -/
def rel (E : Source.Env) (C : Contract) : StateRelation E C :=
  ⟨Relation.val E C, Relation.glob E C⟩

/-- It reflects Booleans. -/
theorem rel_reflect (E : Source.Env) (C : Contract) (H : HTy)
    (v : Source.Val E.layout .bool) (b : Bool)
    (h : (rel E C).val H .bool (.val .bool) v b) : v = .bool b := by
  cases h
  rfl

/-- It relates `false` to `false`. -/
theorem rel_false (E : Source.Env) (C : Contract) (H : HTy) :
    (rel E C).val H .bool (.val .bool) (.bool false) false :=
  .bool false


/-! ## The decoder's primitive types -/


/-- A primitive slot: a model primitive and a Source type a decoder version
may give it. A `bool` is a `bool`; a `uint` is an unsigned integer of any
width or an address; an `int` is a signed integer of any width. -/
inductive Prim : PrimTy → Source.STy → Prop where
  | bool : Prim .bool .bool
  | uint (t : Source.IntTy) (unsigned : t.signed = false) : Prim .uint (.int t)
  | int (t : Source.IntTy) (signed : t.signed = true) : Prim .int (.int t)
  | address (payable : Bool) : Prim .uint (.address payable)

/-- The Source type of an elementary type the decoders use is a primitive
slot's type, and a storage cell of it holds a value of it. -/
theorem prim_of_primElem {p : PrimTy} {bits : Nat} {e : Source.Elem}
    (he : Decode.primElem p bits = some e) :
    Prim p (e.ty .storage) ∧ (e.ty .storage).cell = e.ty .storage ∧
      e.ty .memory = e.ty .storage := by
  cases p <;> simp only [Decode.primElem] at he <;> split at he <;>
    first
    | (cases he; exact ⟨.bool, rfl, rfl⟩)
    | (cases he; exact ⟨.uint _ rfl, rfl, rfl⟩)
    | (cases he; exact ⟨.int _ rfl, rfl, rfl⟩)
    | cases he

/-- The decoders' type of a primitive at a width is a primitive slot's type. -/
theorem prim_of_primTy {p : PrimTy} {bits : Nat} {τ : Source.STy}
    (h : Decode.primTy p bits = some τ) : Prim p τ := by
  simp only [Decode.primTy, Option.map_eq_some_iff] at h
  obtain ⟨e, he, rfl⟩ := h
  obtain ⟨prim, _, same⟩ := prim_of_primElem he
  rw [same]
  exact prim

/-- An unsigned integer type's range is inside `uint`'s. -/
theorem uint_inRange (t : Source.IntTy) (unsigned : t.signed = false) (n : Int)
    (h : t.lo ≤ n ∧ n ≤ t.hi) : PrimTy.uint.inRange n = true := by
  refine (Source.Agreement.uint_range n).mpr ?_
  have pow : 2 ^ t.bits ≤ 2 ^ 256 := Nat.pow_le_pow_right (by decide) t.valid.2.2
  simp only [Source.IntTy.lo, Source.IntTy.hi, unsigned, Source.IntTy.u256, Bool.false_eq_true,
    if_false] at h ⊢
  omega

/-- A signed integer type's range is inside `int`'s. -/
theorem int_inRange (t : Source.IntTy) (signed : t.signed = true) (n : Int)
    (h : t.lo ≤ n ∧ n ≤ t.hi) : PrimTy.int.inRange n = true := by
  refine (Source.Agreement.int_range n).mpr ?_
  have pow : 2 ^ (t.bits - 1) ≤ 2 ^ 255 :=
    Nat.pow_le_pow_right (by decide) (by have := t.valid.2.2; omega)
  simp only [Source.IntTy.lo, Source.IntTy.hi, signed, Source.IntTy.u256, if_true] at h ⊢
  omega

/-- An address is in `uint`'s range. -/
theorem address_inRange (a : Roadmap.Address) : PrimTy.uint.inRange (a.val : Int) = true := by
  simp only [PrimTy.inRange, decide_eq_true_eq]
  exact ⟨Int.natCast_nonneg _,
    Int.ofNat_lt.mpr (Nat.lt_trans a.isLt (Nat.pow_lt_pow_right (by decide) (by decide)))⟩

/-- Every Source value at a primitive slot's type is the image of a model value. -/
theorem prim_onto (D : Source.Layout) {p : PrimTy} {τ : Source.STy} (h : Prim p τ)
    (v : Source.Val D τ) : ∃ w : p.Denote, Relation.ValRel D τ p v w := by
  cases h with
  | bool => exact match v with
      | .bool b => ⟨b, .bool b⟩
  | uint t unsigned => exact match v with
      | .int n hn => ⟨⟨n, uint_inRange t unsigned n hn⟩, .uint t unsigned n hn _ rfl⟩
  | int t signed => exact match v with
      | .int n hn => ⟨⟨n, int_inRange t signed n hn⟩, .int t signed n hn _ rfl⟩
  | address payable => exact match v with
      | .address a => ⟨⟨a.val, address_inRange a⟩, .address payable a _ rfl⟩

/-- A primitive slot's type has a default value, so its cell always reads. -/
theorem Prim.default (D : Source.Layout) {p : PrimTy} {τ : Source.STy} (h : Prim p τ) :
    (Source.Val.default D τ).isSome = true := by
  cases h <;> rfl

/-! ## The storage cell types of the canonical unit at widths -/

/-- The canonical unit's declaration of the state variable the model reads
under the name `x`. -/
theorem stateVars_find (widths : List (Name × Nat)) (x : Name) (p : PrimTy) :
    (vars : List (Name × Ty)) → (parts : Source.Syn (.list (.part false))) →
    Decode.stateVarsW widths vars = some parts → Semantics.lookupBy x vars = some (.prim p) →
    ∃ e, Decode.primElem p (Decode.stateBits widths x) = some e ∧
      (parts.collect (some Decode.contractName)).find?
        (fun d => d.kind == .stateVar && d.scope == some Decode.contractName && d.name == x) =
        some (Decode.varDecl x (.elem e))
  | [], _, _, hx => by cases hx
  | (y, .ref _) :: rest, _, h, _ => by simp [Decode.stateVarsW] at h
  | (y, .prim q) :: rest, parts, h, hx => by
      simp only [Decode.stateVarsW, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff,
        Option.some.injEq] at h
      obtain ⟨e, he, parts', hp, rfl⟩ := h
      simp only [Semantics.lookupBy] at hx
      by_cases same : x = y
      · subst same
        simp only [if_true, Option.some.injEq, Ty.prim.injEq] at hx
        subst hx
        exact ⟨e, he, by simp [Source.Syn.collect, Decode.varDecl]⟩
      · simp only [if_neg same] at hx
        obtain ⟨e', he', found⟩ := stateVars_find widths x p rest parts' hp hx
        refine ⟨e', he', ?_⟩
        have ne : (y == x) = false := by simpa using fun h => same h.symm
        simp [Source.Syn.collect, ne, found]

/-- **The cell type of a primitive state variable** in the canonical unit at
widths is the decoder's Source type of the primitive at the variable's width. -/
theorem unit_cellTy {C : Contract} {u : Source.Syn .unit} (h : Decode.unitW C = some u)
    {x : Name} {p : PrimTy} (hx : Semantics.lookupBy x C.vars = some (.prim p)) :
    ∃ τ, Decode.primTy p (Decode.stateBits C.widths x) = some τ ∧
      u.env.cellTy ⟨⟨some Decode.contractName, x⟩, []⟩ = τ := by
  unfold Decode.unitW at h
  split at h
  · simp only [Option.map_eq_some_iff] at h
    obtain ⟨parts, hp, rfl⟩ := h
    obtain ⟨e, he, found⟩ := stateVars_find C.widths x p C.vars parts hp hx
    have decl : (Source.Syn.unit (.cons (.contract false Decode.contractName .none .nil parts)
        .nil)).env.declOf .stateVar ⟨some Decode.contractName, x⟩ =
        some (Decode.varDecl x (.elem e)) := by
      simp [Source.Env.declOf, Source.Syn.env, Source.Syn.decls, Source.Syn.collect, found]
    refine ⟨e.ty .memory, by simp [Decode.primTy, he], ?_⟩
    simp only [Source.Env.cellTy, Source.Env.pathTy, List.foldl_nil, Source.Env.rootTy, decl,
      Option.bind_some]
    cases p <;> simp only [Decode.primElem] at he <;> split at he <;>
      first | (cases he; rfl) | cases he
  · cases h

/-! ## The locals half of total initial matching -/

/-- Source context of a list of primitive slots. -/
def srcCtx (ss : List (PrimTy × Source.STy)) : Source.RCtx := ss.map (·.2)

/-- Model context of a list of primitive slots. -/
def modCtx (ss : List (PrimTy × Source.STy)) : Ctx := ss.map fun s => .val s.1

/-- The positional map of a list of primitive slots. -/
def slotMap : (ss : List (PrimTy × Source.STy)) → Lowering.V07.ContextMap (srcCtx ss) (modCtx ss)
  | [] => .empty
  | s :: ss => (slotMap ss).cons s.2 (.val s.1)

theorem slotMap_positional : (ss : List (PrimTy × Source.STy)) → Positional (slotMap ss)
  | [] => fun i => nomatch i
  | _ :: ss => fun i => by
      cases i with
      | here => rfl
      | there j => exact congrArg (· + 1) (slotMap_positional ss j)

/-- Every Source locals at primitive slots has related model locals. -/
theorem locals_onto (E : Source.Env) (C : Contract) (H : HTy) :
    (ss : List (PrimTy × Source.STy)) → (∀ s ∈ ss, Prim s.1 s.2) →
    (ls : Source.Locals E.layout (srcCtx ss)) →
      ∃ env : TEnv C H (modCtx ss), (slotMap ss).Related (Relation.val E C H) ls env
  | [], _, .nil => ⟨(), fun i => nomatch i⟩
  | s :: ss, prim, .cons v rest => by
      obtain ⟨x, hx⟩ := prim_onto E.layout (prim s (List.mem_cons_self ..)) v
      obtain ⟨env, henv⟩ := locals_onto E C H ss (fun t m => prim t (List.mem_cons_of_mem _ m)) rest
      exact ⟨(x, env), Lowering.V07.ContextMap.related_cons _ _ _ _ henv _ _ _ _
        (show Relation.val E C H s.2 (.val s.1) v x from hx)⟩

/-- A decoded local is a model primitive at one of the decoder's types. -/
theorem localTy_some {t : LocalTy} {τ : Source.STy} (h : Decode.localTyW t = some τ) :
    ∃ p : PrimTy, t.toLTy = .val p ∧ Prim p τ := by
  cases t with
  | val p bits shape =>
    refine ⟨p, rfl, prim_of_primTy (bits := bits) ?_⟩
    unfold Decode.localTyW at h
    split at h <;> simp_all
  | _ => simp [Decode.localTyW] at h

/-- **A version's tables are sound for the state relation**: a local they
type is a model primitive at a primitive slot's type, and in the unit they
give a contract every state variable is primitive and its cell has a
primitive slot's type. Total initial matching follows for the version. -/
structure Sound (T : Decode.Tables) : Prop where
  localTy : ∀ {t : LocalTy} {τ : Source.STy}, T.localTy t = some τ →
    ∃ p : PrimTy, t.toLTy = .val p ∧ Prim p τ
  cell : ∀ {C : Contract} {u : Source.Syn .unit}, T.unit C = some u → ∀ x U, (x, U) ∈ C.vars →
    ∃ (p : PrimTy) (τ : Source.STy), U = .prim p ∧ Prim p τ ∧
      u.env.cellTy ⟨⟨some Decode.contractName, x⟩, []⟩ = τ

variable {T : Decode.Tables}

/-- A sound version's locals are primitive slots, position by position. -/
theorem locals_primitive (sound : Sound T) : (Γ : ECtx) → (L : List (String × Source.STy)) →
    T.locals Γ = some L →
    ∃ ss : List (PrimTy × Source.STy), (∀ s ∈ ss, Prim s.1 s.2) ∧
      Source.tysOf L = srcCtx ss ∧ ∀ names : FreshNames, (@ECtx.toNCtx names Γ).ctx = modCtx ss
  | [], L, h => by
      cases h
      exact ⟨[], (fun _ m => by cases m), rfl, fun _ => rfl⟩
  | (x, t) :: Γ, L, h => by
      simp only [Decode.Tables.locals, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff,
        Option.some.injEq] at h
      obtain ⟨τ, hτ, L', hL, rfl⟩ := h
      obtain ⟨ss, prim, hs, hm⟩ := locals_primitive sound Γ L' hL
      obtain ⟨p, ht, hp⟩ := sound.localTy hτ
      refine ⟨(p, τ) :: ss, ?_, congrArg (τ :: ·) hs, fun names => ?_⟩
      · intro s m
        rcases List.mem_cons.mp m with e | m'
        · cases e; exact hp
        · exact prim s m'
      · change t.toLTy :: (@ECtx.toNCtx names Γ).ctx = _
        rw [ht, hm names]
        rfl

/-- **The locals half of total initial matching.** A request a sound version
decodes has a positional map under which every Source locals has related
model locals. -/
theorem decode_locals_matching (sound : Sound T) {r : Request} {s : SourceProgram}
    (h : T.decode r = some s) :
    ∃ m : Lowering.V07.ContextMap s.before r.context.ctx, Positional m ∧
      ∀ (H : HTy) (ls : Source.Locals s.env.layout s.before),
        ∃ env : TEnv r.contract H r.context.ctx,
          m.Related (Relation.val s.env r.contract H) ls env := by
  obtain ⟨plain, C, L, b, L', d, _, hL, _, rfl⟩ := decode_spellsT h
  obtain ⟨contract, input, callee⟩ := r
  have none : callee = none := by
    simp only [Decode.plain, Bool.and_eq_true, Option.isNone_iff_eq_none] at plain
    exact plain.1.1.1
  subst none
  obtain ⟨ss, prim, hs, hm⟩ := locals_primitive sound _ _ hL
  have key : ∀ {srcΓ : Source.RCtx} {Γ : Ctx}, srcΓ = srcCtx ss → Γ = modCtx ss →
      ∃ m : Lowering.V07.ContextMap srcΓ Γ, Positional m ∧
        ∀ (H : HTy) (ls : Source.Locals C.env.layout srcΓ),
          ∃ env : TEnv contract H Γ, m.Related (Relation.val C.env contract H) ls env := by
    intro srcΓ Γ e e'
    subst e e'
    exact ⟨slotMap ss, slotMap_positional ss, fun H ls => locals_onto _ _ H ss prim ls⟩
  exact key hs (hm input.names)

/-! ## Total initial matching -/

/-- A model storage related to given Source reads exists when every state
variable is primitive and its cell reads at one of the decoder's types. -/
theorem fields_onto {D : Source.Layout}
    (read : Source.SPath → Option ((τ : Source.STy) × Source.Val D τ)) :
    (fs : List (Name × Ty)) →
    (∀ x T, (x, T) ∈ fs → ∃ p, T = .prim p ∧ ∃ (τ : Source.STy) (v : Source.Val D τ),
      Prim p τ ∧ read ⟨⟨some Decode.contractName, x⟩, []⟩ = some ⟨τ, v⟩) →
    ∃ st : SFields fs, Relation.fields read st
  | [], _ => ⟨.nil, trivial⟩
  | (x, T) :: fs, h => by
      obtain ⟨p, rfl, τ, v, prim, hv⟩ := h x T (List.mem_cons_self ..)
      obtain ⟨w, hw⟩ := prim_onto D prim v
      obtain ⟨rest, hrest⟩ := fields_onto read fs fun y U m => h y U (List.mem_cons_of_mem _ m)
      exact ⟨.cons (.prim w) rest, ⟨τ, v, hv, hw⟩, hrest⟩

/-- The decoder gives a unit only to contracts whose state variables are all
primitive. -/
theorem stateVars_prim (widths : List (Name × Nat)) : (vars : List (Name × Ty)) →
    (parts : Source.Syn (.list (.part false))) →
    Decode.stateVarsW widths vars = some parts → ∀ x T, (x, T) ∈ vars → ∃ p, T = .prim p
  | [], _, _, _, _, m => nomatch m
  | (y, .ref _) :: rest, _, h, _, _, _ => by simp [Decode.stateVarsW] at h
  | (y, .prim q) :: rest, parts, h, x, T, m => by
      simp only [Decode.stateVarsW, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff,
        Option.some.injEq] at h
      obtain ⟨e, he, parts', hp, _⟩ := h
      rcases List.mem_cons.mp m with same | m'
      · cases same; exact ⟨q, rfl⟩
      · exact stateVars_prim widths rest parts' hp x T m'

/-- A cell at one of the decoder's types always reads a value of that type. -/
theorem read_prim {D : Source.Layout} {L : Source.SPath → Source.STy} (s : Source.Storage D L)
    (path : Source.SPath) {p : PrimTy} {τ : Source.STy} (prim : Prim p τ) (h : L path = τ) :
    ∃ v : Source.Val D τ,
      ((s.read path).map fun v => (⟨_, v⟩ : (τ : Source.STy) × Source.Val D τ)) =
        some (⟨τ, v⟩ : (τ : Source.STy) × Source.Val D τ) := by
  subst h
  have present : (s.read path).isSome = true := by
    unfold Source.Storage.read
    split
    · rfl
    · exact prim.default D
  obtain ⟨v, e⟩ := Option.isSome_iff_exists.mp present
  exact ⟨v, by rw [e]; rfl⟩

/-- **Total initial matching holds for every sound version**: every admitted
Source execution of a successful request the version decodes has a related
model state under the positional map. -/
theorem initialMatchingAt (sound : Sound T) : InitialMatching rel T.decode := by
  intro r s _ decoded
  obtain ⟨m, positional, locals⟩ := decode_locals_matching sound decoded
  refine ⟨m, positional, fun e admitted => ?_⟩
  obtain ⟨env, related⟩ := locals [] e.initial.1
  obtain ⟨plain, C, L, b, L', d, hC, _, _, rfl⟩ := decode_spellsT decoded
  simp only [Decode.Tables.context, Option.map_eq_some_iff] at hC
  obtain ⟨u, hu, rfl⟩ := hC
  obtain ⟨storage, hstorage⟩ := fields_onto
    (fun p => ((e.initial.2.ex.world.accounts e.frame.this).storage.read p).map fun v => ⟨_, v⟩)
    r.contract.vars fun x U mem => by
      obtain ⟨p, τ, rfl, prim, cell⟩ := sound.cell hu x U mem
      obtain ⟨v, hv⟩ := read_prim _ _ prim cell
      exact ⟨p, rfl, τ, v, prim, hv⟩
  exact ⟨⟨storage, [], Heap.empty, env, [], PrimTy.dflt .uint,
      { msgValue := wordDenote e.frame.value, timestamp := wordDenote e.glob.timestamp }⟩,
    related, hstorage, rfl, rfl, admitted.2.2.1, admitted.2.2.2⟩

/-! ## The width-aware version is sound -/

/-- The width-aware tables are sound. -/
theorem soundW : Sound Decode.tablesW where
  localTy h := localTy_some h
  cell {C u} h x U mem := by
    have h' : Decode.unitW C = some u := h
    unfold Decode.unitW at h'
    split at h'
    · simp only [Option.map_eq_some_iff] at h'
      obtain ⟨parts, hparts, _⟩ := h'
      obtain ⟨p, rfl⟩ := stateVars_prim _ _ _ hparts x U mem
      obtain ⟨τ, hτ, cell⟩ := unit_cellTy (show Decode.unitW C = some u from h)
        (lookup_of_mem _ C.vars_nodup x _ mem)
      exact ⟨p, τ, rfl, prim_of_primTy hτ, cell⟩
    · cases h'

/-- Total initial matching for the width-aware version. -/
theorem initialMatching : InitialMatching rel Decode.tablesW.decode := initialMatchingAt soundW

/-! ## The address-aware version is sound -/

/-- A local the address-aware tables type is a primitive slot. -/
theorem localTyA_some {t : LocalTy} {τ : Source.STy} (h : Decode.localTyA t = some τ) :
    ∃ p : PrimTy, t.toLTy = .val p ∧ Prim p τ := by
  unfold Decode.localTyA at h
  split at h
  · cases h
    exact ⟨.uint, rfl, .address false⟩
  · exact localTy_some h

/-- The elementary type the address-aware tables give a state variable. -/
theorem elemA_prim {widths : List (Name × Nat)} {x : Name} {p : PrimTy} {e : Source.Elem}
    (h : Decode.elemA widths x p = some e) :
    Prim p (e.ty .storage) ∧ (e.ty .storage).cell = e.ty .storage := by
  unfold Decode.elemA at h
  split at h
  · split at h
    · rename_i ok
      cases h
      rw [ok.1]
      exact ⟨.address false, rfl⟩
    · cases h
  · exact ⟨(prim_of_primElem h).1, (prim_of_primElem h).2.1⟩

/-- The address-aware unit's declaration of the state variable the model reads
under the name `x`, with the type it declares. -/
theorem stateVarsA_find (widths : List (Name × Nat)) (x : Name) (p : PrimTy) :
    (vars : List (Name × Ty)) → (parts : Source.Syn (.list (.part false))) →
    Decode.stateVarsA widths vars = some parts → Semantics.lookupBy x vars = some (.prim p) →
    ∃ e, Prim p (e.ty .storage) ∧ (e.ty .storage).cell = e.ty .storage ∧
      (parts.collect (some Decode.contractName)).find?
        (fun d => d.kind == .stateVar && d.scope == some Decode.contractName && d.name == x) =
        some (Decode.varDecl x (.elem e))
  | [], _, _, hx => by cases hx
  | (y, .ref _) :: rest, _, h, _ => by simp [Decode.stateVarsA] at h
  | (y, .prim q) :: rest, parts, h, hx => by
      simp only [Decode.stateVarsA, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff,
        Option.some.injEq] at h
      obtain ⟨e, he, parts', hp, rfl⟩ := h
      simp only [Semantics.lookupBy] at hx
      by_cases same : x = y
      · subst same
        simp only [if_true, Option.some.injEq, Ty.prim.injEq] at hx
        subst hx
        exact ⟨e, (elemA_prim he).1, (elemA_prim he).2, by simp [Source.Syn.collect, Decode.varDecl]⟩
      · simp only [if_neg same] at hx
        obtain ⟨e', prim, cell, found⟩ := stateVarsA_find widths x p rest parts' hp hx
        refine ⟨e', prim, cell, ?_⟩
        have ne : (y == x) = false := by simpa using fun h => same h.symm
        simp [Source.Syn.collect, ne, found]

/-- The address-aware tables give a unit only to contracts whose state
variables are all primitive. -/
theorem stateVarsA_prim (widths : List (Name × Nat)) : (vars : List (Name × Ty)) →
    (parts : Source.Syn (.list (.part false))) →
    Decode.stateVarsA widths vars = some parts → ∀ x U, (x, U) ∈ vars → ∃ p, U = .prim p
  | [], _, _, _, _, m => nomatch m
  | (y, .ref _) :: rest, _, h, _, _, _ => by simp [Decode.stateVarsA] at h
  | (y, .prim q) :: rest, parts, h, x, U, m => by
      simp only [Decode.stateVarsA, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff,
        Option.some.injEq] at h
      obtain ⟨e, he, parts', hp, _⟩ := h
      rcases List.mem_cons.mp m with same | m'
      · cases same; exact ⟨q, rfl⟩
      · exact stateVarsA_prim widths rest parts' hp x U m'

/-- The address-aware tables are sound. -/
theorem soundA : Sound Decode.tablesA where
  localTy h := localTyA_some h
  cell {C u} h x U mem := by
    have h' : Decode.unitA C = some u := h
    unfold Decode.unitA at h'
    split at h'
    · simp only [Option.map_eq_some_iff] at h'
      obtain ⟨parts, hparts, rfl⟩ := h'
      obtain ⟨p, rfl⟩ := stateVarsA_prim _ _ _ hparts x U mem
      obtain ⟨e, prim, cell, found⟩ := stateVarsA_find C.widths x p C.vars parts hparts
        (lookup_of_mem _ C.vars_nodup x _ mem)
      have decl : (Source.Syn.unit (.cons (.contract false Decode.contractName .none .nil parts)
          .nil)).env.declOf .stateVar ⟨some Decode.contractName, x⟩ =
          some (Decode.varDecl x (.elem e)) := by
        simp [Source.Env.declOf, Source.Syn.env, Source.Syn.decls, Source.Syn.collect, found]
      refine ⟨p, e.ty .storage, rfl, prim, ?_⟩
      simp only [Source.Env.cellTy, Source.Env.pathTy, List.foldl_nil, Source.Env.rootTy, decl,
        Option.bind_some]
      exact congrArg (fun τ => (some τ).getD (.tuple [])) cell
    · cases h'

/-! ## The boundary of a decoder version -/

/-- The boundary of a decoder version at a state relation: the landed
admission, policies, simulation and allocation trace, with the version's
spelling relation as association. -/
def boundaryAt (T : Decode.Tables)
    (rel : (E : Source.Env) → (C : Contract) → StateRelation E C) : SemanticBoundary :=
  ⟨⟨SpellsT T, loopEntry, Observe.source, fun p => Observe.target p⟩,
    fun s _ _ p => Simulation.Simulates rel s p, Allocation.trace⟩

/-- **What the contract asks at a version's boundary**, for a state relation
that reflects Booleans and relates `false` to `false`: the decoder is defined
on every successful request and complete for the version's spelling relation;
the fresh-name scheme round-trips and the run's allocation scope is safe; each
successful pipeline simulates its decoded program and refines it. The e1
family obligations follow from the endpoint theorems. -/
theorem residualAt_iff (T : Decode.Tables)
    {rel : (E : Source.Env) → (C : Contract) → StateRelation E C}
    (reflect : ∀ E C H (v : Source.Val E.layout .bool) (b : Bool),
      (rel E C).val H .bool (.val .bool) v b → v = .bool b)
    (falseRel : ∀ E C H, (rel E C).val H .bool (.val .bool) (.bool false) false) :
    Residual (boundaryAt T rel) T.decode ↔
      (∀ r : Request, r.Succeeds → ∃ s, T.decode r = some s) ∧
      (∀ (r : Request) s, r.Succeeds → SpellsT T r s → T.decode r = some s) ∧
      (∀ (r : Request) o after parts program, r.pipeline o after parts program →
        Allocation.RoundTrip r.input.names ∧
        SafeSpellings r.input.names (Allocation.scope r o after).protectedNames
          (Allocation.scope r o after).generated) ∧
      (∀ (r : Request) o after parts program s, T.decode r = some s →
        r.pipeline o after parts program →
        Simulation.Simulates rel s program ∧
          Nonempty (PassCorrect (Observe.source s).behaviour
            (Observe.target program).behaviour)) := by
  constructor
  · intro h
    refine ⟨h.total, fun r s e spelled => (h.decoder r s e).mpr spelled,
      fun r o after parts program run => ?_,
      fun r o after parts program s d run =>
        h.pipeline r o after parts program s ⟨o, after, parts, program, run⟩ d run⟩
    obtain ⟨scopes, ⟨trace, law⟩, safe⟩ :=
      h.allocation r o after parts program ⟨o, after, parts, program, run⟩ run
    cases trace
    exact ⟨law, safe _ (List.mem_singleton.mpr rfl)⟩
  · intro ⟨covered, complete, allocation, pipeline⟩
    refine ⟨covered, fun r s e => ⟨decode_spellsT, complete r s e⟩,
      fun r o after parts program _ run =>
        ⟨_, ⟨rfl, (allocation r o after parts program run).1⟩, fun scope member => ?_⟩,
      fun r o after parts program s _ d run => pipeline r o after parts program s d run, ?_, ?_⟩
    · cases List.mem_singleton.mp member
      exact (allocation r o after parts program run).2
    · intro k E srcΓ returns M l u C Γ m pair extra names
      obtain ⟨embedding, endpoint⟩ := normalFamily_correct k (returns := returns) (M := M)
        (l := l) (u := u) m pair extra names (k.lowered pair extra names) rfl
      exact Simulation.of_endpoint reflect falseRel endpoint
    · intro k E srcΓ M l u C Γ m pair extra names
      exact Simulation.of_retEndpoint reflect falseRel
        (returnFamily_correct k (M := M) (l := l) (u := u) m pair extra names)

/-- The boundary admits every request whose whole pipeline succeeds. -/
theorem boundaryAt_fullDomain (T : Decode.Tables)
    (rel : (E : Source.Env) → (C : Contract) → StateRelation E C) :
    FullDomain (boundaryAt T rel) := fun _ h => h

/-- The width-aware version's boundary. -/
def boundary : SemanticBoundary := boundaryAt Decode.tablesW rel

/-- What the contract asks at the width-aware version's boundary. The first
conjunct is not provable while the decoder has gaps. -/
theorem residual_iff :
    LowerLoopsCorrectContract boundary boundary.reference Decode.tablesW.decode ↔
      (∀ r : Request, r.Succeeds → ∃ s, Decode.tablesW.decode r = some s) ∧
      (∀ (r : Request) s, r.Succeeds → SpellsT Decode.tablesW r s →
        Decode.tablesW.decode r = some s) ∧
      (∀ (r : Request) o after parts program, r.pipeline o after parts program →
        Allocation.RoundTrip r.input.names ∧
        SafeSpellings r.input.names (Allocation.scope r o after).protectedNames
          (Allocation.scope r o after).generated) ∧
      (∀ (r : Request) o after parts program s, Decode.tablesW.decode r = some s →
        r.pipeline o after parts program →
        Simulation.Simulates rel s program ∧
          Nonempty (PassCorrect (Observe.source s).behaviour
            (Observe.target program).behaviour)) :=
  (contract_reference_iff _ _).trans (residualAt_iff Decode.tablesW rel_reflect rel_false)

/-- Version 2 of the contract at the width-aware version's boundary, with
total initial matching discharged: five obligations are left. -/
theorem contractV2_iff :
    LowerLoopsCorrectContractV2 rel boundary boundary.reference Decode.tablesW.decode ↔
      (∀ r : Request, r.Succeeds → ∃ s, Decode.tablesW.decode r = some s) ∧
      (∀ (r : Request) s, r.Succeeds → SpellsT Decode.tablesW r s →
        Decode.tablesW.decode r = some s) ∧
      (∀ (r : Request) o after parts program, r.pipeline o after parts program →
        Allocation.RoundTrip r.input.names ∧
        SafeSpellings r.input.names (Allocation.scope r o after).protectedNames
          (Allocation.scope r o after).generated) ∧
      (∀ (r : Request) o after parts program s, Decode.tablesW.decode r = some s →
        r.pipeline o after parts program →
        Nonempty (PassCorrect (Observe.source s).behaviour (Observe.target program).behaviour)) ∧
      Simulation.Bound rel Decode.tablesW.decode := by
  unfold LowerLoopsCorrectContractV2
  rw [residual_iff]
  exact ⟨fun ⟨⟨covered, complete, allocation, pipeline⟩, _, bound⟩ =>
      ⟨covered, complete, allocation,
        fun r o after parts program s d run => (pipeline r o after parts program s d run).2,
        bound⟩,
    fun ⟨covered, complete, allocation, refines, bound⟩ =>
      ⟨⟨covered, complete, allocation, fun r o after parts program s d run =>
        ⟨bound.simulates d run, refines r o after parts program s d run⟩⟩, initialMatching,
        bound⟩⟩

/-- **Version 2 of the contract at a sound version's boundary**, with total
initial matching discharged: five obligations are left. -/
theorem contractV2At_iff (sound : Sound T) :
    LowerLoopsCorrectContractV2 rel (boundaryAt T rel) (boundaryAt T rel).reference T.decode ↔
      (∀ r : Request, r.Succeeds → ∃ s, T.decode r = some s) ∧
      (∀ (r : Request) s, r.Succeeds → SpellsT T r s → T.decode r = some s) ∧
      (∀ (r : Request) o after parts program, r.pipeline o after parts program →
        Allocation.RoundTrip r.input.names ∧
        SafeSpellings r.input.names (Allocation.scope r o after).protectedNames
          (Allocation.scope r o after).generated) ∧
      (∀ (r : Request) o after parts program s, T.decode r = some s →
        r.pipeline o after parts program →
        Nonempty (PassCorrect (Observe.source s).behaviour (Observe.target program).behaviour)) ∧
      Simulation.Bound rel T.decode := by
  unfold LowerLoopsCorrectContractV2
  rw [contract_reference_iff, residualAt_iff T rel_reflect rel_false]
  exact ⟨fun ⟨⟨covered, complete, allocation, pipeline⟩, _, bound⟩ =>
      ⟨covered, complete, allocation,
        fun r o after parts program s d run => (pipeline r o after parts program s d run).2,
        bound⟩,
    fun ⟨covered, complete, allocation, refines, bound⟩ =>
      ⟨⟨covered, complete, allocation, fun r o after parts program s d run =>
        ⟨bound.simulates d run, refines r o after parts program s d run⟩⟩,
        initialMatchingAt sound, bound⟩⟩

/-- The address-aware version's boundary. -/
def boundaryA : SemanticBoundary := boundaryAt Decode.tablesA rel

end Version

end Solidity.Correctness.Lowering.Total
