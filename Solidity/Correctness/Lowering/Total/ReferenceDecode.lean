import Solidity.Correctness.Lowering.Total.Decode.Callee.Parameters

/-!
# Decoding reference types and declared parameter locations

The reference-type spelling and the ordered parameter/return component that
`Decode/Callee/Parameters.lean` leaves out. Input is the metadata the model
retains: a `Ty`, the width/marker rows below a binder (`FunDecl.widths`), the
contract's struct-name table (`Contract.structs`) and the declared locations
(`FunDecl.paramLocs`, `retMem`, `retStorage`). Primitive positions are read by
the existing marked decoder `Decode.elemB` at the position's key (`xs[]` an
element or mapping value, `m{}` a mapping key).

Nothing erased is guessed; each such case is an `Error` naming the position:
- a struct is written by the one name `Contract.structName?` reads as its table
  type (`written?`); none, or several, is an error;
- a row below a reference binder that the spelling does not read (an enum,
  function-type, hashed-key or `string` marker, a row below a struct) is
  `unreadRow`;
- `uint[]` with `bytes1` elements is `erasedBytes`: the model has the same rows
  for `bytes` and `bytes1[]`;
- a reference binder without a location, a return whose flags give none or two.

Proved for a successful spelling, against `Source.Syn.tys`: `spellTy_typed`
(type), `binders_names`, `binders_typed`, `signature_frame` (actual
`Source.Frame.mk?`), under `Resolved` obligations on the struct names used.
`Rep` keeps nesting, lengths, key/value types, struct identity and the nested
width rows; `paramCtx_reverse` and `signature_paramCtx` relate declared
locations to `FunDecl.paramCtx`, where `memory` and `calldata` coincide
(`frameTy_memory_calldata`).

`rawType` spells a retained `RawTy` the same way, its leaves by
`Decode.typeNameB`, with `rawType_typed` against Source elaboration.

Open, with the complete-unit decoder: `bytes`/`string`, enum identity and
function types inside references, struct declarations and their member widths,
discharging `Resolved`, unit coverage and semantic binding. This is a
component; it defines no admission predicate.
-/
namespace Solidity.Correctness.Lowering.Total.ReferenceDecode

open Solidity.Semantics (lookupBy structDef)
open Source (Syn STy DataLoc)
open Decode (elemB)

/-- Why retained metadata has no Source spelling here. `key` is the width-table
position (`x`, `x[]`, `x{}`, …). -/
inductive Error where
  /-- The width/marker rows at `key` give the primitive no elementary type. -/
  | unrepresentable (key : Name) (p : PrimTy)
  /-- `uint[]` with `bytes1` elements: `bytes` and `bytes1[]` have the same rows. -/
  | erasedBytes (key : Name)
  /-- A fixed array of length zero; Source lengths are positive. -/
  | zeroLength (key : Name)
  /-- A mapping at a position outside storage. -/
  | mappingOutsideStorage (key : Name) (loc : DataLoc)
  /-- No name of the contract reads as the struct's table type. -/
  | unknownStruct (key table : Name)
  /-- Several names read as the same table type; which was written is erased. -/
  | ambiguousStruct (key table : Name) (written : List Name)
  /-- A row at or below a reference binder that the spelling does not read. -/
  | unreadRow (binder key : Name) (value : Nat)
  /-- A reference parameter without a declared location. -/
  | missingLocation (binder : Name)
  /-- A declared location on a value parameter. -/
  | locationOnValue (binder : Name) (loc : ParamLoc)
  /-- A reference return, neither `retMem` nor `retStorage` set. -/
  | missingReturnLocation (binder : Name)
  /-- A reference return, both `retMem` and `retStorage` set. -/
  | conflictingReturnLocation (binder : Name)
  deriving DecidableEq, Repr

/-! ## Struct names -/

/-- The names the table `l` reads as `table`, first match as `lookupBy`. -/
def owners (table : Name) : List (Name × Name) → List Name
  | [] => []
  | (w, e) :: rest =>
    (if e = table then [w] else []) ++ (owners table rest).filter (fun v => v != w)

/-- Every identifier `Contract.structName?` reads as `table`: the contract's
own names, then the plain table name when the contract does not shadow it. A
name that spells its members (`Semantics.isEnc`) is no identifier, though
`structName?` reads it too. -/
def writtenNames (C : Contract) (table : Name) : List Name :=
  (owners table C.structs ++
    (if lookupBy table C.structs = none ∧ (structDef table).isEmpty = false then [table]
      else [])).filter fun w => !Semantics.isEnc w

/-- The written name of a struct type, when exactly one identifier reads as it. -/
def written? (C : Contract) (table : Name) : Option Name :=
  match writtenNames C table with
  | [w] => some w
  | _ => none

theorem owners_iff {table w : Name} : ∀ {l : List (Name × Name)},
    w ∈ owners table l ↔ lookupBy w l = some table
  | [] => by simp [owners, lookupBy]
  | (v, e) :: rest => by
      have ih := owners_iff (table := table) (w := w) (l := rest)
      by_cases same : w = v
      · subst same
        by_cases he : e = table <;> simp [owners, lookupBy, he]
      · by_cases he : e = table <;> simp [owners, lookupBy, he, same, ih]

/-- The candidates are exactly the identifiers the elaborator reads as the type. -/
theorem writtenNames_iff {C : Contract} {table w : Name} :
    w ∈ writtenNames C table ↔
      C.structName? w = some table ∧ Semantics.isEnc w = false := by
  simp only [writtenNames, List.mem_filter, List.mem_append, owners_iff, Contract.structName?,
    Bool.not_eq_true']
  refine and_congr_left fun _ => ?_
  constructor
  · rintro (h | h)
    · simp only [h]
    · split at h
      · rename_i hc
        cases List.mem_singleton.mp h
        simp only [hc.1, hc.2, Bool.false_eq_true, if_false]
      · cases h
  · intro h
    cases hl : lookupBy w C.structs with
    | some e =>
        simp only [hl, Option.some.injEq] at h
        exact Or.inl (h ▸ rfl)
    | none =>
        simp only [hl] at h
        split at h
        · cases h
        · rename_i ne
          cases h
          exact Or.inr (by simp [hl, ne])

/-- The written name is an identifier that elaborates back to the struct's
table type. -/
theorem written?_sound {C : Contract} {table w : Name} (h : written? C table = some w) :
    C.structName? w = some table ∧ Semantics.isEnc w = false := by
  unfold written? at h
  split at h
  · rename_i w' eq
    cases h
    exact writtenNames_iff.mp (by rw [eq]; exact List.mem_singleton.mpr rfl)
  · cases h

/-- No other identifier elaborates to it: the spelling is not a choice. -/
theorem written?_unique {C : Contract} {table w w' : Name} (h : written? C table = some w)
    (h' : C.structName? w' = some table) (ident : Semantics.isEnc w' = false) : w' = w := by
  unfold written? at h
  split at h
  · rename_i w'' eq
    cases h
    have := writtenNames_iff.mpr ⟨h', ident⟩
    rw [eq] at this
    exact List.mem_singleton.mp this
  · cases h

/-! ## Type spelling -/

/-- The decimal literal `n`, an array length. -/
def lenLit (n : Nat) : Syn .expr := .lit (.num (.dec n 0 0))

/-- `bytes1`, the element the model also gives `bytes`. -/
def isBytes1 : Syn .typeName → Bool
  | .elem (.fixedBytes n _) => n == 1
  | _ => false

mutual
/-- The Source type name of a model type at the width-table position `key`,
in the location `loc`. -/
def spellType (C : Contract) (widths : List (Name × Nat)) (key : Name) (loc : DataLoc) :
    Ty → Except Error (Syn .typeName)
  | .prim p =>
    match elemB widths key p with
    | some e => .ok (.elem e)
    | none => .error (.unrepresentable key p)
  | .ref R => spellRef C widths key loc R

/-- The Source type name of a reference type. -/
def spellRef (C : Contract) (widths : List (Name × Nat)) (key : Name) (loc : DataLoc) :
    RefTy → Except Error (Syn .typeName)
  | .struct s =>
    match written? C s with
    | some w => .ok (.userType ⟨w, []⟩)
    | none =>
      .error (if writtenNames C s = [] then .unknownStruct key s
        else .ambiguousStruct key s (writtenNames C s))
  | .array E =>
    match spellType C widths (key ++ "[]") loc E with
    | .ok t => if isBytes1 t then .error (.erasedBytes key) else .ok (.array t .none)
    | .error e => .error e
  | .fixed E n =>
    if n = 0 then .error (.zeroLength key)
    else match spellType C widths (key ++ "[]") loc E with
      | .ok t => .ok (.array t (.some (lenLit n)))
      | .error e => .error e
  | .mapping K V =>
    if loc = .storage then
      match elemB widths (key ++ "{}") K with
      | some e =>
        if h : e = .addressPayable then .error (.unrepresentable (key ++ "{}") K)
        else match spellType C widths (key ++ "[]") .storage V with
          | .ok t => .ok (.mapping (.elem e h) none t none)
          | .error e => .error e
      | none => .error (.unrepresentable (key ++ "{}") K)
    else .error (.mappingOutsideStorage key loc)
end

/-- The rows `elemB` reads at a primitive position. -/
def leafKeys (key : Name) : List Name := [key, key ++ "#address", key ++ "#bytes"]

mutual
/-- The width-table keys the spelling of a type at `key` reads. -/
def readTy (key : Name) : Ty → List Name
  | .prim _ => leafKeys key
  | .ref R => readRef key R

/-- The keys the spelling of a reference type reads; none below a struct. -/
def readRef (key : Name) : RefTy → List Name
  | .struct _ => []
  | .array E => readTy (key ++ "[]") E
  | .fixed E _ => readTy (key ++ "[]") E
  | .mapping _ V => leafKeys (key ++ "{}") ++ readTy (key ++ "[]") V
end

mutual
/-- The struct table types a type mentions, not looking inside a struct. -/
def structsTy : Ty → List Name
  | .prim _ => []
  | .ref R => structsRef R

/-- The struct table types a reference type mentions. -/
def structsRef : RefTy → List Name
  | .struct s => [s]
  | .array E => structsTy E
  | .fixed E _ => structsTy E
  | .mapping _ V => structsTy V
end

/-- A row at or below the binder `x`, as `shapeUnder` reads the table. -/
def below (x k : Name) : Bool :=
  k == x || (x.data ++ ['[']).isPrefixOf k.data || (x.data ++ ['{']).isPrefixOf k.data ||
    (x.data ++ ['#']).isPrefixOf k.data

/-- The first row at or below a reference binder that its spelling does not
read. A primitive binder is read as `Decode.Callee.parameters` reads it. -/
def unread (widths : List (Name × Nat)) (x : Name) : Ty → Option (Name × Nat)
  | .prim _ => none
  | .ref R => widths.find? fun r => below x r.1 && !(readRef x R).contains r.1

/-! ## Binders -/

/-- The Source location a declared parameter location names. -/
def sourceLoc : ParamLoc → DataLoc
  | .memory => .memory
  | .storage => .storage
  | .calldata => .calldata

/-- The declared location of a binder, or why there is none to write. -/
abbrev LocOf := Name → Ty → Except Error (Option DataLoc)

/-- One binder: its declared location, its rows all read, its type in that
location (memory where none is written), its name. -/
def binder (C : Contract) (widths : List (Name × Nat)) (locOf : LocOf) (x : Name × Ty) :
    Except Error (Syn .param) :=
  match locOf x.1 x.2 with
  | .error e => .error e
  | .ok l =>
    match unread widths x.1 x.2 with
    | some r => .error (.unreadRow x.1 r.1 r.2)
    | none =>
      match spellType C widths x.1 (l.getD .memory) x.2 with
      | .ok t => .ok (.param t l (some x.1))
      | .error e => .error e

/-- Every binder in order; the first that has no spelling is the error. -/
def binders (C : Contract) (widths : List (Name × Nat)) (locOf : LocOf) :
    List (Name × Ty) → Except Error (Syn (.list .param))
  | [] => .ok .nil
  | x :: xs =>
    match binder C widths locOf x with
    | .error e => .error e
    | .ok p =>
      match binders C widths locOf xs with
      | .ok ps => .ok (.cons p ps)
      | .error e => .error e

/-- A parameter's declared location: a reference has one, a value none. -/
def paramLoc (d : FunDecl) (x : Name) : Ty → Except Error (Option DataLoc)
  | .prim _ =>
    match lookupBy x d.paramLocs with
    | none => .ok none
    | some l => .error (.locationOnValue x l)
  | .ref _ =>
    match lookupBy x d.paramLocs with
    | some l => .ok (some (sourceLoc l))
    | none => .error (.missingLocation x)

/-- A return's declared location, from the function's two flags: one flag is
the location of every reference return, a value return has none. -/
def retLoc (d : FunDecl) (x : Name) : Ty → Except Error (Option DataLoc)
  | .prim _ => .ok none
  | .ref _ =>
    match d.retMem, d.retStorage with
    | true, false => .ok (some .memory)
    | false, true => .ok (some .storage)
    | false, false => .error (.missingReturnLocation x)
    | true, true => .error (.conflictingReturnLocation x)

/-- Both binder lists of a declaration, from its own metadata. -/
def signature (C : Contract) (d : FunDecl) :
    Except Error (Syn (.list .param) × Syn (.list .param)) :=
  match binders C d.widths (paramLoc d) d.params with
  | .error e => .error e
  | .ok ps =>
    match binders C d.widths (retLoc d) d.rets with
    | .ok rs => .ok (ps, rs)
    | .error e => .error e

/-- The declared locations of a parameter list, in order. -/
def declaredLocs : {c : Source.Cat} → Syn c → List (Option DataLoc)
  | _, .cons x xs => declaredLocs x ++ declaredLocs xs
  | _, .param _ l _ => [l]
  | _, _ => []

/-! ## Source type elaboration -/

/-- The declaration-resolution obligation of a struct name: from `scope` the
name denotes exactly one declaration, a struct, with identity `d`. -/
def Resolved (E : Source.Env) (scope : Option String) (w : Name) (d : Source.DeclName) : Prop :=
  ∃ decl, E.lookup scope w = [decl] ∧ decl.kind = .struct ∧ d = ⟨decl.scope, decl.name⟩

theorem Resolved.userTy {E : Source.Env} {scope : Option String} {w : Name}
    {d : Source.DeclName} (h : Resolved E scope w d) (loc : DataLoc) :
    E.userTy scope loc ⟨w, []⟩ = some (.struct loc d) := by
  obtain ⟨decl, look, kind, rfl⟩ := h
  simp only [Source.Env.userTy, Source.Env.lookupPath, look, kind]

theorem Resolved.unique {E : Source.Env} {scope : Option String} {w : Name}
    {d d' : Source.DeclName} (h : Resolved E scope w d) (h' : Resolved E scope w d') : d = d' := by
  obtain ⟨decl, look, _, rfl⟩ := h
  obtain ⟨decl', look', _, rfl⟩ := h'
  rw [look] at look'
  cases look'
  rfl

/-- What a successful spelling denotes. Each constructor keeps one piece of the
model type: a primitive its marked elementary type at its own rows, an array
its nesting and length, a mapping its key and value, a struct the identity its
written name resolves to. -/
inductive Rep (C : Contract) (widths : List (Name × Nat)) (E : Source.Env)
    (scope : Option String) : Name → DataLoc → Ty → STy → Prop where
  | prim {key loc p e} : elemB widths key p = some e → Version.Prim p (e.ty loc) →
      Rep C widths E scope key loc (.prim p) (e.ty loc)
  | array {key loc T τ} : Rep C widths E scope (key ++ "[]") loc T τ →
      Rep C widths E scope key loc (.ref (.array T)) (.array loc τ none)
  | fixed {key loc T τ n} : 0 < n → Rep C widths E scope (key ++ "[]") loc T τ →
      Rep C widths E scope key loc (.ref (.fixed T n)) (.array loc τ (some n))
  | mapping {key K V e τ} : elemB widths (key ++ "{}") K = some e →
      Version.Prim K (e.ty .memory) → Rep C widths E scope (key ++ "[]") .storage V τ →
      Rep C widths E scope key .storage (.ref (.mapping K V)) (.mapping (e.ty .memory) τ)
  | struct {key loc s w d} : written? C s = some w → Resolved E scope w d →
      Rep C widths E scope key loc (.ref (.struct s)) (.struct loc d)

/-- A marked elementary type is location-free and a primitive slot's type. -/
theorem elemB_ty {widths : List (Name × Nat)} {key : Name} {p : PrimTy} {e : Source.Elem}
    (h : elemB widths key p = some e) (loc : DataLoc) :
    Version.Prim p (e.ty loc) ∧ e ≠ .addressPayable := by
  have hp := (Version.elemB_prim h).1
  cases e with
  | fixed s dims => cases dims <;> cases hp
  | addressPayable =>
      exfalso
      unfold elemB at h
      split at h
      · split at h
        · simp only [Decode.bytesElem] at h
          split at h <;> cases h
        · cases h
      · unfold Decode.elemA at h
        split at h
        · split at h <;> cases h
        · cases p <;> simp only [Decode.primElem] at h <;> split at h <;> cases h
  | _ => first | exact ⟨hp, by simp⟩ | cases hp

theorem lenLit_const (n : Nat) :
    (lenLit n).const = some ⟨n * 10 ^ 0, 10 ^ 0, Nat.pow_pos (by decide)⟩ := rfl

theorem arrayLen_lenLit {n : Nat} (h : 0 < n) :
    Source.arrayLen (.some (lenLit n)) = some (some n) := by
  have ne : ¬ n = 0 := by omega
  unfold Source.arrayLen
  simp only [lenLit_const]
  simp [Source.Q.isInt, Source.Q.toInt, ne]

mutual
/-- A successful spelling elaborates, under the resolution obligations of the
structs it mentions, to a type that represents the model type. -/
theorem spellTy_typed (C : Contract) (widths : List (Name × Nat)) (E : Source.Env)
    (scope : Option String) : (T : Ty) → (key : Name) → (loc : DataLoc) →
    (t : Syn .typeName) → spellType C widths key loc T = .ok t →
    (∀ s ∈ structsTy T, ∀ w, written? C s = some w → ∃ d, Resolved E scope w d) →
    ∃ τ, t.tys E scope loc = some [τ] ∧ Rep C widths E scope key loc T τ
  | .prim p, key, loc, t, h, _ => by
      simp only [spellType] at h
      split at h
      · rename_i e he
        cases h
        exact ⟨e.ty loc, rfl, .prim he (elemB_ty he loc).1⟩
      · cases h
  | .ref R, key, loc, t, h, res => by
      simp only [spellType] at h
      obtain ⟨τ, typed, rep⟩ := spellRef_typed C widths E scope R key loc t h
        (by simpa only [structsTy] using res)
      exact ⟨τ, typed, rep⟩

theorem spellRef_typed (C : Contract) (widths : List (Name × Nat)) (E : Source.Env)
    (scope : Option String) : (R : RefTy) → (key : Name) → (loc : DataLoc) →
    (t : Syn .typeName) → spellRef C widths key loc R = .ok t →
    (∀ s ∈ structsRef R, ∀ w, written? C s = some w → ∃ d, Resolved E scope w d) →
    ∃ τ, t.tys E scope loc = some [τ] ∧ Rep C widths E scope key loc (.ref R) τ
  | .struct s, key, loc, t, h, res => by
      simp only [spellRef] at h
      split at h
      · rename_i w hw
        cases h
        obtain ⟨d, hd⟩ := res s (by simp [structsRef]) w hw
        exact ⟨.struct loc d, by simp [Source.Syn.tys, hd.userTy loc], .struct hw hd⟩
      · cases h
  | .array T, key, loc, t, h, res => by
      simp only [spellRef] at h
      split at h
      · rename_i t' ht
        split at h
        · cases h
        · cases h
          obtain ⟨τ, typed, rep⟩ := spellTy_typed C widths E scope T _ loc t' ht
            (by simpa only [structsRef] using res)
          exact ⟨.array loc τ none, by simp [Source.Syn.tys, typed, Source.arrayLen],
            .array rep⟩
      · cases h
  | .fixed T n, key, loc, t, h, res => by
      simp only [spellRef] at h
      split at h
      · cases h
      · rename_i pos
        split at h
        · rename_i t' ht
          cases h
          obtain ⟨τ, typed, rep⟩ := spellTy_typed C widths E scope T _ loc t' ht
            (by simpa only [structsRef] using res)
          have pos' : 0 < n := Nat.pos_of_ne_zero pos
          exact ⟨.array loc τ (some n),
            by simp [Source.Syn.tys, typed, arrayLen_lenLit pos'], .fixed pos' rep⟩
        · cases h
  | .mapping K V, key, loc, t, h, res => by
      simp only [spellRef] at h
      split at h
      · rename_i hloc
        subst hloc
        split at h
        · rename_i e he
          split at h
          · cases h
          · split at h
            · rename_i t' ht
              cases h
              obtain ⟨τ, typed, rep⟩ := spellTy_typed C widths E scope V _ .storage t' ht
                (by simpa only [structsRef] using res)
              exact ⟨.mapping (e.ty .memory) τ,
                by simp [Source.Syn.tys, typed, Source.Env.keyTy],
                .mapping he (elemB_ty he .memory).1 rep⟩
            · cases h
        · cases h
      · cases h
end

/-- The single-type form: `Source.Syn.ty` of a successful spelling. -/
theorem spellTy_ty {C : Contract} {widths : List (Name × Nat)} {key : Name} {loc : DataLoc}
    {T : Ty} {t : Syn .typeName} (h : spellType C widths key loc T = .ok t)
    (E : Source.Env) (scope : Option String)
    (res : ∀ s ∈ structsTy T, ∀ w, written? C s = some w → ∃ d, Resolved E scope w d) :
    ∃ τ, t.ty E scope loc = some τ ∧ Rep C widths E scope key loc T τ := by
  obtain ⟨τ, typed, rep⟩ := spellTy_typed C widths E scope T key loc t h res
  exact ⟨τ, by simp [Source.Syn.ty, typed], rep⟩

/-! ## What `Rep` keeps -/

namespace Rep

variable {C : Contract} {widths : List (Name × Nat)} {E : Source.Env} {scope : Option String}

/-- A primitive is its marked elementary type at its own rows. -/
theorem prim_inv {key loc p τ} (h : Rep C widths E scope key loc (.prim p) τ) :
    ∃ e, elemB widths key p = some e ∧ τ = e.ty loc ∧ Version.Prim p τ := by
  cases h with
  | prim he hp => exact ⟨_, he, rfl, hp⟩

/-- A dynamic array stays one, at the same location, over its element. -/
theorem array_inv {key loc T τ} (h : Rep C widths E scope key loc (.ref (.array T)) τ) :
    ∃ τ', τ = .array loc τ' none ∧ Rep C widths E scope (key ++ "[]") loc T τ' := by
  cases h with
  | array rep => exact ⟨_, rfl, rep⟩

/-- A fixed array keeps its positive length. -/
theorem fixed_inv {key loc T n τ} (h : Rep C widths E scope key loc (.ref (.fixed T n)) τ) :
    ∃ τ', τ = .array loc τ' (some n) ∧ 0 < n ∧
      Rep C widths E scope (key ++ "[]") loc T τ' := by
  cases h with
  | fixed pos rep => exact ⟨_, rfl, pos, rep⟩

/-- A mapping is in storage and keeps its key and value types. -/
theorem mapping_inv {key loc K V τ}
    (h : Rep C widths E scope key loc (.ref (.mapping K V)) τ) :
    loc = .storage ∧ ∃ e τv, elemB widths (key ++ "{}") K = some e ∧
      Version.Prim K (e.ty .memory) ∧ τ = .mapping (e.ty .memory) τv ∧
      Rep C widths E scope (key ++ "[]") .storage V τv := by
  cases h with
  | mapping he hp rep => exact ⟨rfl, _, _, he, hp, rfl, rep⟩

/-- A struct is the declaration its one written name resolves to; that name
elaborates back to the struct's table type. -/
theorem struct_inv {key loc s τ} (h : Rep C widths E scope key loc (.ref (.struct s)) τ) :
    ∃ w d, written? C s = some w ∧ C.structName? w = some s ∧ Resolved E scope w d ∧
      τ = .struct loc d := by
  cases h with
  | struct hw hd => exact ⟨_, _, hw, (written?_sound hw).1, hd, rfl⟩

/-- The represented Source type is determined: nothing is left to choose. -/
theorem unique {key loc T τ τ'} (h : Rep C widths E scope key loc T τ)
    (h' : Rep C widths E scope key loc T τ') : τ = τ' := by
  induction h generalizing τ' with
  | prim he _ =>
      cases h' with
      | prim he' _ => rw [he] at he'; cases he'; rfl
  | array _ ih =>
      cases h' with
      | array rep' => rw [ih rep']
  | fixed _ _ ih =>
      cases h' with
      | fixed _ rep' => rw [ih rep']
  | mapping he _ _ ih =>
      cases h' with
      | mapping he' _ rep' => rw [he] at he'; cases he'; rw [ih rep']
  | struct hw hd =>
      cases h' with
      | struct hw' hd' => rw [hw] at hw'; cases hw'; rw [hd.unique hd']

end Rep

/-! ## Binder lists against Source parameter lists -/

/-- Every row at or below a reference binder is one its spelling read. -/
theorem unread_none {widths : List (Name × Nat)} {x : Name} {R : RefTy}
    (h : unread widths x (.ref R) = none) :
    ∀ r ∈ widths, below x r.1 = true → r.1 ∈ readRef x R := by
  intro r mem low
  have := List.find?_eq_none.mp h r mem
  simpa [low] using this

/-- A binder and the type its Source parameter denotes: at its declared
location (memory where a value has none), with every row below it read. -/
def Slot (C : Contract) (widths : List (Name × Nat)) (E : Source.Env) (scope : Option String)
    (locOf : LocOf) (x : Name × Ty) (τ : STy) : Prop :=
  ∃ l, locOf x.1 x.2 = .ok l ∧ unread widths x.1 x.2 = none ∧
    Rep C widths E scope x.1 (l.getD .memory) x.2 τ

/-- Ordered correspondence of all binders; neither list has an extra slot. -/
inductive Slots (C : Contract) (widths : List (Name × Nat)) (E : Source.Env)
    (scope : Option String) (locOf : LocOf) : List (Name × Ty) → List STy → Prop where
  | nil : Slots C widths E scope locOf [] []
  | cons {x xs τ τs} : Slot C widths E scope locOf x τ → Slots C widths E scope locOf xs τs →
      Slots C widths E scope locOf (x :: xs) (τ :: τs)

theorem binder_inv {C : Contract} {widths : List (Name × Nat)} {locOf : LocOf}
    {x : Name × Ty} {p : Syn .param} (h : binder C widths locOf x = .ok p) :
    ∃ l t, locOf x.1 x.2 = .ok l ∧ unread widths x.1 x.2 = none ∧
      spellType C widths x.1 (l.getD .memory) x.2 = .ok t ∧ p = .param t l (some x.1) := by
  unfold binder at h
  split at h
  · cases h
  · rename_i l hl
    split at h
    · cases h
    · rename_i hu
      split at h
      · rename_i t ht
        cases h
        exact ⟨l, t, hl, hu, ht, rfl⟩
      · cases h

theorem binders_cons {C : Contract} {widths : List (Name × Nat)} {locOf : LocOf}
    {x : Name × Ty} {xs : List (Name × Ty)} {ps : Syn (.list .param)}
    (h : binders C widths locOf (x :: xs) = .ok ps) :
    ∃ p rest, binder C widths locOf x = .ok p ∧ binders C widths locOf xs = .ok rest ∧
      ps = .cons p rest := by
  simp only [binders] at h
  split at h
  · cases h
  · rename_i p hp
    split at h
    · rename_i rest hr
      cases h
      exact ⟨p, rest, hp, hr, rfl⟩
    · cases h

/-- Names, order and declared locations are exactly the model's: one Source
parameter per binder, under its name, with the location `locOf` gives it. -/
theorem binders_names {C : Contract} {widths : List (Name × Nat)} {locOf : LocOf} :
    ∀ {xs : List (Name × Ty)} {ps : Syn (.list .param)},
      binders C widths locOf xs = .ok ps →
      ps.paramNames = xs.map (fun x => some x.1) ∧
      xs.map (fun x => locOf x.1 x.2) = (declaredLocs ps).map .ok
  | [], ps, h => by
      cases h
      exact ⟨rfl, rfl⟩
  | x :: xs, ps, h => by
      obtain ⟨p, rest, hp, hr, rfl⟩ := binders_cons h
      obtain ⟨l, t, hl, _, _, rfl⟩ := binder_inv hp
      obtain ⟨names, locs⟩ := binders_names hr
      exact ⟨by simp [Source.Syn.paramNames, names], by simp [declaredLocs, hl, locs]⟩

/-- The actual Source elaboration of a decoded parameter list: one type per
binder, in order, each representing its binder at its declared location.
The hypothesis is declaration resolution of the struct names used, not the
elaboration result. -/
theorem binders_typed {C : Contract} {widths : List (Name × Nat)} {locOf : LocOf}
    (E : Source.Env) (scope : Option String) :
    ∀ {xs : List (Name × Ty)} {ps : Syn (.list .param)},
      binders C widths locOf xs = .ok ps →
      (∀ x ∈ xs, ∀ s ∈ structsTy x.2, ∀ w, written? C s = some w →
        ∃ d, Resolved E scope w d) →
      ∃ τs, ps.tys E scope .memory = some τs ∧
        Slots C widths E scope locOf xs τs
  | [], ps, h, _ => by
      cases h
      exact ⟨[], rfl, .nil⟩
  | x :: xs, ps, h, res => by
      obtain ⟨p, rest, hp, hr, rfl⟩ := binders_cons h
      obtain ⟨l, t, hl, hu, ht, rfl⟩ := binder_inv hp
      obtain ⟨τ, typed, rep⟩ := spellTy_typed C widths E scope x.2 x.1 _ t ht
        (res x (List.mem_cons_self))
      obtain ⟨τs, typeds, slots⟩ := binders_typed E scope hr
        (fun y my => res y (List.mem_cons_of_mem _ my))
      exact ⟨τ :: τs, by simp [Source.Syn.tys, typed, typeds],
        .cons ⟨l, hl, hu, rep⟩ slots⟩

/-- On binders the primitive component spells, this component gives the same
parameter list: it extends `Decode.Callee.parameters`. -/
theorem binders_primitive {C : Contract} {widths : List (Name × Nat)} {locOf : LocOf} :
    ∀ {xs : List (Name × Ty)} {ps : Syn (.list .param)},
      Decode.Callee.parameters widths xs = some ps →
      (∀ x ∈ xs, locOf x.1 x.2 = .ok none) →
      binders C widths locOf xs = .ok ps
  | [], ps, h, _ => by
      cases h
      rfl
  | (x, .ref R) :: xs, ps, h, _ => by cases h
  | (x, .prim p) :: xs, ps, h, locs => by
      simp only [Decode.Callee.parameters, Option.bind_eq_bind, Option.pure_def,
        Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨e, he, rest, hr, rfl⟩ := h
      have hl := locs (x, .prim p) List.mem_cons_self
      have ih := binders_primitive (C := C) hr (fun y my => locs y (List.mem_cons_of_mem _ my))
      simp only [binders, binder, hl, unread, spellType, he, ih]

/-- The actual Source frame constructor accepts a successful signature: the
original ordered names, the declared locations, and a representing type per
binder. Body and flags pass through unchanged; no body semantics is claimed. -/
theorem signature_frame {C : Contract} {d : FunDecl} {ps rs : Syn (.list .param)}
    (h : signature C d = .ok (ps, rs)) (E : Source.Env) (scope : Option String)
    (res : ∀ x ∈ d.params ++ d.rets, ∀ s ∈ structsTy x.2, ∀ w, written? C s = some w →
      ∃ d', Resolved E scope w d')
    (body : Syn (.list (.item .body))) (msgValue inModifier : Bool) :
    ∃ f, Source.Frame.mk? E scope ps rs body msgValue inModifier = some f ∧
      f.names = d.params.map (fun p => some p.1) ∧
      f.rnames = d.rets.map (fun p => some p.1) ∧
      d.params.map (fun x => paramLoc d x.1 x.2) = (declaredLocs ps).map .ok ∧
      d.rets.map (fun x => retLoc d x.1 x.2) = (declaredLocs rs).map .ok ∧
      Slots C d.widths E scope (paramLoc d) d.params f.ps ∧
      Slots C d.widths E scope (retLoc d) d.rets f.rs ∧
      f.body = body ∧ f.msgValue = msgValue ∧ f.inModifier = inModifier := by
  unfold signature at h
  split at h
  · cases h
  · rename_i ps' hp
    split at h
    · rename_i rs' hr
      cases h
      obtain ⟨pn, pl⟩ := binders_names hp
      obtain ⟨rn, rl⟩ := binders_names hr
      obtain ⟨pts, pt, pslots⟩ := binders_typed E scope hp
        (fun x mx => res x (List.mem_append_left _ mx))
      obtain ⟨rts, rt, rslots⟩ := binders_typed E scope hr
        (fun x mx => res x (List.mem_append_right _ mx))
      refine ⟨⟨ps.paramNames, pts, rs.paramNames, rts, body, msgValue, inModifier⟩,
        ?_, pn, rn, pl, rl, pslots, rslots, rfl, rfl, rfl⟩
      simp [Source.Frame.mk?, pt, rt]
    · cases h

/-! ## Declared locations and `FunDecl.paramCtx` -/

/-- The declared Source location of the parameter `x`, if any. -/
def declLoc (d : FunDecl) (x : Name) : Option DataLoc := (lookupBy x d.paramLocs).map sourceLoc

/-- The frame type `FunDecl.paramCtx` gives a binder with a declared Source
location: a storage reference is an alias, any other reference a memory one. -/
def frameTy (widths : List (Name × Nat)) (x : Name) : Ty → Option DataLoc → LocalTy
  | .prim p, _ => .val p ((lookupBy x widths).getD 256) (shapeUnder widths x)
  | .ref R, some .storage => .alias R (shapeUnder widths x)
  | .ref R, _ => .mem R (shapeUnder widths x)

/-- The frame does not keep the Source distinction: a `calldata` parameter has
the frame type of a `memory` one. The decoded parameter list keeps it
(`binders_names`). -/
theorem frameTy_memory_calldata (widths : List (Name × Nat)) (x : Name) (T : Ty) :
    frameTy widths x T (some .memory) = frameTy widths x T (some .calldata) := by
  cases T <;> rfl

private theorem mapM_ok {α β ε : Type} {f : α → Except ε β} {g : α → β} {P : α → Prop}
    (hf : ∀ a b, f a = .ok b → b = g a ∧ P a) :
    ∀ (l : List α) (r : List β), l.mapM f = .ok r → r = l.map g ∧ ∀ a ∈ l, P a
  | [], r, h => by
      cases h
      exact ⟨rfl, fun _ m => nomatch m⟩
  | a :: l, r, h => by
      rw [List.mapM_cons] at h
      cases hfa : f a with
      | error e => simp only [hfa, bind, Except.bind] at h; cases h
      | ok b =>
          cases hl : l.mapM f with
          | error e => simp only [hfa, hl, bind, Except.bind] at h; cases h
          | ok bs =>
              simp only [hfa, hl, bind, Except.bind, pure, Except.pure] at h
              cases h
              obtain ⟨eq, all⟩ := mapM_ok hf l bs hl
              obtain ⟨eqb, pa⟩ := hf a b hfa
              refine ⟨by rw [eqb, eq]; rfl, ?_⟩
              intro a' m
              rcases List.mem_cons.mp m with rfl | m'
              · exact pa
              · exact all a' m'

/-- A successful `paramCtx` is, in declaration order, each parameter at the
frame type of its declared location; and each such location is the one
`paramLoc` reads. -/
theorem paramCtx_reverse {d : FunDecl} {Γ : ECtx} (h : d.paramCtx = .ok Γ) :
    Γ.reverse = d.params.map (fun x => (x.1, frameTy d.widths x.1 x.2 (declLoc d x.1))) ∧
      ∀ x ∈ d.params, paramLoc d x.1 x.2 = .ok (declLoc d x.1) := by
  unfold FunDecl.paramCtx at h
  obtain ⟨eq, all⟩ := mapM_ok
    (g := fun x : Name × Ty => (x.1, frameTy d.widths x.1 x.2 (declLoc d x.1)))
    (P := fun x : Name × Ty => paramLoc d x.1 x.2 = .ok (declLoc d x.1)) (by
      rintro ⟨n, T⟩ b hb
      cases T with
      | prim p =>
          simp only at hb
          split at hb
          · cases hb
          · rename_i none
            cases hb
            have hn : lookupBy n d.paramLocs = Option.none := by
              cases hl : lookupBy n d.paramLocs with
              | none => rfl
              | some l => simp [hl] at none
            exact ⟨rfl, by simp [paramLoc, declLoc, hn]⟩
      | ref R =>
          simp only at hb
          split at hb
          · rename_i hl
            cases hb
            exact ⟨by simp [frameTy, declLoc, hl, sourceLoc], by simp [paramLoc, declLoc, hl]⟩
          · rename_i hl
            split at hb
            · cases hb
              exact ⟨by simp [frameTy, declLoc, hl, sourceLoc], by simp [paramLoc, declLoc, hl]⟩
            · cases hb
          · rename_i hl
            split at hb
            · cases hb
              exact ⟨by simp [frameTy, declLoc, hl, sourceLoc], by simp [paramLoc, declLoc, hl]⟩
            · cases hb
          · cases hb) _ _ h
  refine ⟨?_, fun x mx => all x (List.mem_reverse.mpr mx)⟩
  rw [eq, List.map_reverse, List.reverse_reverse]

private theorem map_ok_inj {α ε : Type} : ∀ {l l' : List α},
    l.map (Except.ok (ε := ε)) = l'.map Except.ok → l = l'
  | [], [], _ => rfl
  | [], _ :: _, h => by cases h
  | _ :: _, [], h => by cases h
  | a :: l, b :: l', h => by
      simp only [List.map_cons, List.cons.injEq, Except.ok.injEq] at h
      rw [h.1, map_ok_inj h.2]

private theorem zip_map {α β γ : Type} (f : α → β) (g : α × β → γ) : ∀ l : List α,
    (l.zip (l.map f)).map g = l.map (fun x => g (x, f x))
  | [] => rfl
  | a :: l => by simp [zip_map f g l]

/-- The frame context of a decoded signature, read off the decoded Source
parameter list: each parameter at the frame type of the location its Source
parameter declares. The converse reading fails at `memory`/`calldata`
(`frameTy_memory_calldata`). -/
theorem signature_paramCtx {C : Contract} {d : FunDecl} {ps rs : Syn (.list .param)}
    {Γ : ECtx} (h : signature C d = .ok (ps, rs)) (hΓ : d.paramCtx = .ok Γ) :
    Γ.reverse = (d.params.zip (declaredLocs ps)).map
      (fun xl => (xl.1.1, frameTy d.widths xl.1.1 xl.1.2 xl.2)) := by
  unfold signature at h
  split at h
  · cases h
  · rename_i ps' hp
    split at h
    · cases h
      obtain ⟨ctx, locs⟩ := paramCtx_reverse hΓ
      have decl : declaredLocs ps = d.params.map (fun x => declLoc d x.1) := by
        apply map_ok_inj (ε := Error)
        rw [← (binders_names hp).2, List.map_map]
        exact List.map_congr_left locs
      rw [ctx, decl, zip_map]
    · cases h

/-! ## Retained `RawTy`

A declaration in a body keeps its type as read. Its spelling needs no width
rows: a leaf is the name the marked decoder `Decode.typeNameB` reads, or a
struct name as written. -/

/-- Why a retained type as read has no Source spelling here. -/
inductive RawError where
  /-- An enum, function-type, `bytes`/`string` or member-spelling name: its
  reading stays with the complete-unit decoder. -/
  | unsupportedName (s : String)
  /-- Neither a marked elementary type nor a struct of the contract. -/
  | unknownName (s : String)
  /-- A mapping key that is not a marked elementary type name. -/
  | unsupportedKey (K : RawTy)
  /-- A fixed array of length zero. -/
  | zeroLength
  /-- A mapping at a position outside storage. -/
  | mappingOutsideStorage (loc : DataLoc)
  deriving Repr

/-- The elementary type the marked decoder reads a name as. -/
def rawElem (s : String) : Option Source.Elem :=
  match Decode.typeNameB (.named s) with
  | some (.elem e) => some e
  | _ => none

/-- A leaf name: its marked elementary type, or a struct name as written. -/
def rawLeaf (C : Contract) (s : String) : Except RawError (Syn .typeName) :=
  match rawElem s with
  | some e => .ok (.elem e)
  | none =>
    if (lookupBy s C.enums).isSome || fnTy? s || dynBytesTy s || Semantics.isEnc s then
      .error (.unsupportedName s)
    else match C.structName? s with
      | some _ => .ok (.userType ⟨s, []⟩)
      | none => .error (.unknownName s)

/-- A mapping key: a marked elementary type name. -/
def rawKey : RawTy → Except RawError Source.MapKey
  | .named k =>
    match rawElem k with
    | some e =>
      if h : e = .addressPayable then .error (.unsupportedKey (.named k)) else .ok (.elem e h)
    | none => .error (.unsupportedKey (.named k))
  | K => .error (.unsupportedKey K)

/-- The Source type name of a type as read, in the location `loc`. -/
def rawType (C : Contract) : DataLoc → RawTy → Except RawError (Syn .typeName)
  | _, .named s => rawLeaf C s
  | loc, .array T =>
    match rawType C loc T with
    | .ok t => .ok (.array t .none)
    | .error e => .error e
  | loc, .fixed T n =>
    if n = 0 then .error .zeroLength
    else match rawType C loc T with
      | .ok t => .ok (.array t (.some (lenLit n)))
      | .error e => .error e
  | loc, .mapping K V =>
    if loc = .storage then
      match rawKey K with
      | .ok k =>
        match rawType C .storage V with
        | .ok t => .ok (.mapping k none t none)
        | .error e => .error e
      | .error e => .error e
    else .error (.mappingOutsideStorage loc)

/-- The names a type as read mentions outside mapping keys. -/
def rawNames : RawTy → List String
  | .named s => [s]
  | .array T => rawNames T
  | .fixed T _ => rawNames T
  | .mapping _ V => rawNames V

/-- What a successful spelling of a type as read denotes: the marked
elementary type of each leaf name, the same nesting and lengths, the key and
value of a mapping, and for a struct name both the table type the model
elaborates it to and the declaration it resolves to. -/
inductive RawRep (C : Contract) (E : Source.Env) (scope : Option String) :
    DataLoc → RawTy → STy → Prop where
  | elem {loc s e} : rawElem s = some e → RawRep C E scope loc (.named s) (e.ty loc)
  | struct {loc s table d} : rawElem s = none → C.structName? s = some table →
      Semantics.isEnc s = false → Resolved E scope s d →
      RawRep C E scope loc (.named s) (.struct loc d)
  | array {loc T τ} : RawRep C E scope loc T τ →
      RawRep C E scope loc (.array T) (.array loc τ none)
  | fixed {loc T τ n} : 0 < n → RawRep C E scope loc T τ →
      RawRep C E scope loc (.fixed T n) (.array loc τ (some n))
  | mapping {k V e τ} : rawElem k = some e → RawRep C E scope .storage V τ →
      RawRep C E scope .storage (.mapping (.named k) V) (.mapping (e.ty .memory) τ)

theorem rawKey_ok {K : RawTy} {key : Source.MapKey} (h : rawKey K = .ok key) :
    ∃ k e ne, K = .named k ∧ key = .elem e ne ∧ rawElem k = some e := by
  unfold rawKey at h
  split at h
  · rename_i k
    split at h
    · rename_i e he
      split at h
      · cases h
      · rename_i ne
        cases h
        exact ⟨k, e, ne, rfl, rfl, he⟩
    · cases h
  · cases h

/-- A successful spelling of a type as read elaborates, under the resolution
obligations of the struct names it mentions, to the type it represents. -/
theorem rawType_typed (C : Contract) (E : Source.Env) (scope : Option String) :
    (T : RawTy) → (loc : DataLoc) → (t : Syn .typeName) → rawType C loc T = .ok t →
    (∀ s ∈ rawNames T, rawElem s = none → ∃ d, Resolved E scope s d) →
    ∃ τ, t.tys E scope loc = some [τ] ∧ RawRep C E scope loc T τ
  | .named s, loc, t, h, res => by
      simp only [rawType] at h
      unfold rawLeaf at h
      split at h
      · rename_i e he
        cases h
        exact ⟨e.ty loc, rfl, .elem he⟩
      · rename_i he
        split at h
        · cases h
        · rename_i plain
          split at h
          · rename_i table ht
            cases h
            obtain ⟨d, hd⟩ := res s (by simp [rawNames]) he
            have ident : Semantics.isEnc s = false := by
              cases hi : Semantics.isEnc s with
              | false => rfl
              | true => simp [hi] at plain
            exact ⟨.struct loc d, by simp [Source.Syn.tys, hd.userTy loc],
              .struct he ht ident hd⟩
          · cases h
  | .array T, loc, t, h, res => by
      simp only [rawType] at h
      split at h
      · rename_i t' ht
        cases h
        obtain ⟨τ, typed, rep⟩ := rawType_typed C E scope T loc t' ht
          (by simpa only [rawNames] using res)
        exact ⟨.array loc τ none, by simp [Source.Syn.tys, typed, Source.arrayLen], .array rep⟩
      · cases h
  | .fixed T n, loc, t, h, res => by
      simp only [rawType] at h
      split at h
      · cases h
      · rename_i pos
        split at h
        · rename_i t' ht
          cases h
          obtain ⟨τ, typed, rep⟩ := rawType_typed C E scope T loc t' ht
            (by simpa only [rawNames] using res)
          have pos' : 0 < n := Nat.pos_of_ne_zero pos
          exact ⟨.array loc τ (some n),
            by simp [Source.Syn.tys, typed, arrayLen_lenLit pos'], .fixed pos' rep⟩
        · cases h
  | .mapping K V, loc, t, h, res => by
      simp only [rawType] at h
      split at h
      · rename_i hloc
        subst hloc
        split at h
        · rename_i key hk
          split at h
          · rename_i t' ht
            cases h
            obtain ⟨τ, typed, rep⟩ := rawType_typed C E scope V .storage t' ht
              (by simpa only [rawNames] using res)
            obtain ⟨k, e, ne, rfl, rfl, he⟩ := rawKey_ok hk
            exact ⟨.mapping (e.ty .memory) τ,
              by simp [Source.Syn.tys, typed, Source.Env.keyTy], .mapping he rep⟩
          · cases h
        · cases h
      · cases h

/-- A struct name as read and the written name of the type the model elaborates
it to are the same name: the two spellings agree on struct identity. -/
theorem rawStruct_written {C : Contract} {E : Source.Env} {scope : Option String}
    {loc : DataLoc} {s w table : Name} {τ : STy} (h : RawRep C E scope loc (.named s) τ)
    (ht : C.structName? s = some table) (hw : written? C table = some w)
    (he : rawElem s = none) : w = s := by
  cases h with
  | elem he' => rw [he] at he'; cases he'
  | struct _ _ ident _ => exact (written?_unique hw ht ident).symm

end Solidity.Correctness.Lowering.Total.ReferenceDecode
