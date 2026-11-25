import Solidity.Correctness.Lowering.Total.Decode.Spelling
import Solidity.Correctness.Lowering.Total.Boundary
import Solidity.Correctness.Lowering.Total.Versions.Primitive
import Solidity.Correctness.Lowering.Total.Decode.Marked

/-!
Initial matching here runs from Source states to model states. `Sound` ensures
primitive-slot compatibility, not agreement with the model declarations' widths
or types. General converse matching fails for narrow integers, addresses and
fixed bytes because model values can lie outside their Source ranges.
-/
namespace Solidity.Correctness.Lowering.Total

open Solidity.Roadmap.G49Final

namespace Version
open Simulation (StateRelation Positional InitialMatching lookup_of_mem wordDenote)

/-! ## The state relation -/

namespace Relation

/-- A model primitive value and the Source value it stands for: the same
Boolean, the same number at an integer type of the primitive's sign, or (for
a `uint`) the address with that number or the `bytesN` with that big-endian
value. -/
inductive ValRel (D : Source.Layout) :
    (τ : Source.STy) → (p : PrimTy) → Source.Val D τ → p.Denote → Prop where
  | bool (b : Bool) : ValRel D .bool .bool (.bool b) b
  | uint (t : Source.IntTy) (unsigned : t.signed = false) (n : Int) (h : t.lo ≤ n ∧ n ≤ t.hi)
      (x : PrimTy.uint.Denote) (same : x.1 = n) : ValRel D (.int t) .uint (.int n h) x
  | int (t : Source.IntTy) (signed : t.signed = true) (n : Int) (h : t.lo ≤ n ∧ n ≤ t.hi)
      (x : PrimTy.int.Denote) (same : x.1 = n) : ValRel D (.int t) .int (.int n h) x
  | address (payable : Bool) (a : Roadmap.Address) (x : PrimTy.uint.Denote)
      (same : x.1 = (a.val : Int)) : ValRel D (.address payable) .uint (.address a) x
  | bytes (n : Nat) (h : 1 ≤ n ∧ n ≤ 32) (bs : List UInt8) (hl : bs.length = n)
      (x : PrimTy.uint.Denote) (same : x.1 = (Source.bytesNat bs : Int)) :
      ValRel D (.fixedBytes n h) .uint (.fixedBytes bs hl) x

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

/-- The balance Source observes for the running account (`Source.evalE` at
`a.balance`): the account's own while it has code, the ledger's otherwise. -/
def ownBalance {E : Source.Env} (G : Source.Glob E) (F : Source.Fr) (st : Source.St E) :
    Roadmap.Word :=
  match (st.ex.world.accounts F.this).code with
  | some _ => Source.Monetary.wordView (st.ex.world.accounts F.this).balance
  | none => G.fixed.ledger G.balance0 st.events F.this

/-- Globals: storage of the running account, `msg.value`, the timestamp, the
caller, the running account's address and observed balance, and a Source frame
that may write and checks arithmetic, as the model always does. -/
def glob (E : Source.Env) (C : Contract) (G : Source.Glob E) (F : Source.Fr) (st : Source.St E)
    (σ : State C []) : Prop :=
  fields (fun p => ((st.ex.world.accounts F.this).storage.read p).map fun v => ⟨_, v⟩) σ.storage ∧
  σ.tx.msgValue.1 = (F.value.val : Int) ∧ σ.tx.timestamp.1 = (G.timestamp.val : Int) ∧
  σ.tx.msgSender.1 = (F.sender.val : Int) ∧
  σ.tx.selfAddress.1 = (F.this.val : Int) ∧ σ.selfBalance.1 = ((ownBalance G F st).val : Int) ∧
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

/-- The big-endian value of a byte string is below `256 ^ length`. -/
theorem bytesNat_lt (bs : List UInt8) : Source.bytesNat bs < 256 ^ bs.length := by
  have fold : ∀ (bs : List UInt8) (acc : Nat),
      bs.foldl (fun acc b => acc * 256 + b.toNat) acc < (acc + 1) * 256 ^ bs.length := by
    intro bs
    induction bs with
    | nil => intro acc; simp
    | cons b rest ih =>
      intro acc
      have step := ih (acc * 256 + b.toNat)
      have byte : b.toNat < 256 := b.toNat_lt
      have le : (acc * 256 + b.toNat + 1) * 256 ^ rest.length ≤
          (acc + 1) * 256 * 256 ^ rest.length :=
        Nat.mul_le_mul_right _ (by omega)
      simp only [List.foldl_cons, List.length_cons, Nat.pow_succ]
      calc _ < (acc * 256 + b.toNat + 1) * 256 ^ rest.length := step
        _ ≤ (acc + 1) * 256 * 256 ^ rest.length := le
        _ = (acc + 1) * (256 ^ rest.length * 256) := by
          rw [Nat.mul_assoc, Nat.mul_comm 256]
  simpa [Source.bytesNat, Source.beValue] using fold bs 0

/-- A `bytesN` value is in `uint`'s range. -/
theorem bytes_inRange {n : Nat} (h : 1 ≤ n ∧ n ≤ 32) (bs : List UInt8) (hl : bs.length = n) :
    PrimTy.uint.inRange (Source.bytesNat bs : Int) = true := by
  simp only [PrimTy.inRange, decide_eq_true_eq]
  refine ⟨Int.natCast_nonneg _, Int.ofNat_lt.mpr (Nat.lt_of_lt_of_le (bytesNat_lt bs) ?_)⟩
  rw [hl]
  calc 256 ^ n ≤ 256 ^ 32 := Nat.pow_le_pow_right (by decide) h.2
    _ = 2 ^ 256 := by decide

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
  | bytes n h => exact match v with
      | .fixedBytes bs hl => ⟨⟨Source.bytesNat bs, bytes_inRange h bs hl⟩, .bytes n h bs hl _ rfl⟩

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
  exact ⟨⟨storage, [], Heap.empty, env, [],
      wordDenote (Relation.ownBalance e.glob e.frame e.initial.2),
      { msgValue := wordDenote e.frame.value, timestamp := wordDenote e.glob.timestamp,
        msgSender := ⟨e.frame.sender.val, address_inRange e.frame.sender⟩,
        selfAddress := ⟨e.frame.this.val, address_inRange e.frame.this⟩ }⟩,
    related, hstorage, rfl, rfl, rfl, rfl, rfl, admitted.2.2.1, admitted.2.2.2⟩

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

end Version

end Solidity.Correctness.Lowering.Total
