import Solidity.Correctness.Lowering.Total.Decode.Callee.Parameters

/-!
# Decoding reference types and declared parameter locations

Reference-type spelling and ordered parameter/return lists from retained
metadata: a `Ty`, the width/marker rows at and below a binder (`xs[]` an element
or mapping value, `m{}` a key), `Contract.structs`, the declared locations.
Primitive positions are read by `Decode.elemB`. Erased or unread metadata is an
`Error` naming the position, never a guess, with one inherited exception: the
model marks `address payable` as `address` and `elemB` spells both `address`.

Proved against `Source.Syn.tys` and `Source.Frame.mk?` under `Resolved`
obligations on the struct names used; `paramCtx_reverse` relates declared
locations to `FunDecl.paramCtx`, where `memory` and `calldata` coincide.

Open: `bytes`/`string`, enum and function types, payability, struct declarations
and member widths, discharging `Resolved`, retained `RawTy` declarations, unit
coverage and semantic binding. A component; it defines no admission predicate.
-/
namespace Solidity.Correctness.Lowering.Total.ReferenceDecode

open Solidity.Semantics (lookupBy structDef isEnc)
open Source (Syn STy DataLoc)
open Decode (elemB)

/-- Why retained metadata has no Source spelling; `key` is the row position. -/
inductive Error where
  | unrepresentable (key : Name) (p : PrimTy) -- its rows give no elementary type
  | erasedBytes (key : Name) -- `bytes` and `bytes1[]` have the same rows
  | zeroLength (key : Name) -- a fixed array of length zero
  | mappingOutsideStorage (key : Name) (loc : DataLoc)
  | unknownStruct (key table : Name) -- no identifier reads as the table type
  | ambiguousStruct (key table : Name) (written : List Name) -- several do
  | unreadRow (binder key : Name) (value : Nat) -- a row the spelling does not read
  | missingLocation (binder : Name) -- a reference parameter without a location
  | locationOnValue (binder : Name) (loc : ParamLoc)
  | missingReturnLocation (binder : Name) -- a reference return, neither flag set
  /-- Both flags: two locations, or the reader's mark for a misplaced one. -/
  | conflictingReturnLocation (binder : Name)
  | locationOnValueReturn (binder : Name) -- a flag, and every return a value
  deriving DecidableEq, Repr
theorem bind_ok {α β ε : Type} {x : Except ε α} {f : α → Except ε β} {b : β} :
    (x >>= f) = .ok b ↔ ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x <;> simp [bind, Except.bind]

/-- The names the table reads as `table`, first match as `lookupBy`. -/
def owners (table : Name) : List (Name × Name) → List Name
  | [] => []
  | (w, e) :: l => (if e = table then [w] else []) ++ (owners table l).filter (· != w)

/-- Every identifier (no member spelling, `isEnc`) `Contract.structName?` reads
as `table`: the contract's own names, then the table name unless shadowed.
`elabTy` asks it after primitive, enum and narrow names; these are not excluded. -/
def writtenNames (C : Contract) (table : Name) : List Name :=
  (owners table C.structs ++
    (if lookupBy table C.structs = none ∧ (structDef table).isEmpty = false then [table]
      else [])).filter (!isEnc ·)
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
theorem writtenNames_iff {C : Contract} {table w : Name} :
    w ∈ writtenNames C table ↔ C.structName? w = some table ∧ isEnc w = false := by
  simp only [writtenNames, List.mem_filter, List.mem_append, owners_iff, Contract.structName?,
    Bool.not_eq_true']
  refine and_congr_left fun _ => ?_
  by_cases hw : w = table
  · subst hw; cases lookupBy w C.structs <;> simp
  · cases lookupBy w C.structs <;> simp [hw] <;> split <;> simp [hw]
/-- The written name is the only identifier read as the table type: no choice. -/
theorem written?_iff {C : Contract} {table w : Name} (h : written? C table = some w)
    (w' : Name) : (C.structName? w' = some table ∧ isEnc w' = false) ↔ w' = w := by
  unfold written? at h
  split at h
  · rename_i eq; cases h
    rw [← writtenNames_iff, eq, List.mem_singleton]
  · cases h
def lenLit (n : Nat) : Syn .expr := .lit (.num (.dec n 0 0))
def isBytes1 : Syn .typeName → Bool
  | .elem (.fixedBytes n _) => n == 1
  | _ => false

mutual
/-- The Source type name of a model type at the row position `key`, in `loc`. -/
def spellType (C : Contract) (widths : List (Name × Nat)) (key : Name) (loc : DataLoc) :
    Ty → Except Error (Syn .typeName)
  | .prim p =>
    match elemB widths key p with
    | some e => .ok (.elem e)
    | none => .error (.unrepresentable key p)
  | .ref R => spellRef C widths key loc R
def spellRef (C : Contract) (widths : List (Name × Nat)) (key : Name) (loc : DataLoc) :
    RefTy → Except Error (Syn .typeName)
  | .struct s =>
    match written? C s with
    | some w => .ok (.userType ⟨w, []⟩)
    | none => .error (if writtenNames C s = [] then .unknownStruct key s
        else .ambiguousStruct key s (writtenNames C s))
  | .array T => do
    let t ← spellType C widths (key ++ "[]") loc T
    if isBytes1 t then .error (.erasedBytes key) else .ok (.array t .none)
  | .fixed T n =>
    if n = 0 then .error (.zeroLength key)
    else do .ok (.array (← spellType C widths (key ++ "[]") loc T) (.some (lenLit n)))
  | .mapping K V =>
    if loc = .storage then
      match elemB widths (key ++ "{}") K with
      | some e => -- never payable; the key constructor asks for the proof
        if h : e = .addressPayable then .error (.unrepresentable (key ++ "{}") K)
        else do .ok (.mapping (.elem e h) none (← spellType C widths (key ++ "[]") .storage V) none)
      | none => .error (.unrepresentable (key ++ "{}") K)
    else .error (.mappingOutsideStorage key loc)
end
/-- The rows `elemB` reads at a primitive position. -/
def leafKeys (key : Name) : List Name := [key, key ++ "#address", key ++ "#bytes"]
mutual
/-- The row keys the spelling of a type at `key` reads; none below a struct. -/
def readTy (key : Name) : Ty → List Name
  | .prim _ => leafKeys key
  | .ref R => readRef key R
def readRef (key : Name) : RefTy → List Name
  | .struct _ => []
  | .array T | .fixed T _ => readTy (key ++ "[]") T
  | .mapping _ V => leafKeys (key ++ "{}") ++ readTy (key ++ "[]") V
end
mutual
/-- The struct table types a type mentions, not looking inside a struct. -/
def structsTy : Ty → List Name
  | .prim _ => []
  | .ref R => structsRef R
def structsRef : RefTy → List Name
  | .struct s => [s]
  | .array T | .fixed T _ | .mapping _ T => structsTy T
end
/-- A row at or below the binder `x`, as `shapeUnder` reads the table. -/
def below (x k : Name) : Bool :=
  k == x || (x.data ++ ['[']).isPrefixOf k.data || (x.data ++ ['{']).isPrefixOf k.data ||
    (x.data ++ ['#']).isPrefixOf k.data
/-- The first row at or below a binder that its spelling does not read. -/
def unread (widths : List (Name × Nat)) (x : Name) (T : Ty) : Option (Name × Nat) :=
  widths.find? fun r => below x r.1 && !(readTy x T).contains r.1

def sourceLoc (l : ParamLoc) : DataLoc :=
  match l with | .memory => .memory | .storage => .storage | .calldata => .calldata
/-- The declared location of a binder, or why there is none to write. -/
abbrev LocOf := Name → Ty → Except Error (Option DataLoc)
/-- One binder: its location, its rows all read, its type there, its name. -/
def binder (C : Contract) (widths : List (Name × Nat)) (locOf : LocOf) (x : Name × Ty) :
    Except Error (Syn .param) := do
  let l ← locOf x.1 x.2
  match unread widths x.1 x.2 with
  | some r => .error (.unreadRow x.1 r.1 r.2)
  | none => do .ok (.param (← spellType C widths x.1 (l.getD .memory) x.2) l (some x.1))
/-- Every binder in order; the first without a spelling is the error. -/
def binders (C : Contract) (widths : List (Name × Nat)) (locOf : LocOf) :
    List (Name × Ty) → Except Error (Syn (.list .param))
  | [] => .ok .nil
  | x :: xs => do
    let p ← binder C widths locOf x
    let ps ← binders C widths locOf xs
    .ok (.cons p ps)
/-- A parameter's declared location: a reference has one, a value none. -/
def paramLoc (d : FunDecl) (x : Name) (T : Ty) : Except Error (Option DataLoc) :=
  match T, lookupBy x d.paramLocs with
  | .prim _, none => .ok none
  | .prim _, some l => .error (.locationOnValue x l)
  | .ref _, some l => .ok (some (sourceLoc l))
  | .ref _, none => .error (.missingLocation x)
/-- A return's declared location: one flag is the location of every reference
return; a flag with no reference return is an error. -/
def retLoc (d : FunDecl) (x : Name) (T : Ty) : Except Error (Option DataLoc) :=
  match T, d.retMem, d.retStorage with
  | .ref _, true, false => .ok (some .memory)
  | .ref _, false, true => .ok (some .storage)
  | .ref _, false, false => .error (.missingReturnLocation x)
  | .ref _, true, true => .error (.conflictingReturnLocation x)
  | .prim _, m, s =>
    if (m || s) && d.rets.all (·.2.isPrimitive) then .error (.locationOnValueReturn x) else .ok none
/-- Both binder lists of a declaration, from its own metadata. -/
def signature (C : Contract) (d : FunDecl) :
    Except Error (Syn (.list .param) × Syn (.list .param)) := do
  let ps ← binders C d.widths (paramLoc d) d.params
  let rs ← binders C d.widths (retLoc d) d.rets
  .ok (ps, rs)
/-- The declared locations of a parameter list, in order. -/
def declaredLocs : {c : Source.Cat} → Syn c → List (Option DataLoc)
  | _, .cons x xs => declaredLocs x ++ declaredLocs xs
  | _, .param _ l _ => [l]
  | _, _ => []

variable {C : Contract} {widths : List (Name × Nat)} {E : Source.Env} {scope : Option String}
  {locOf : LocOf}

/-- The resolution obligation of a struct name: from `scope` it denotes exactly
one declaration, a struct, with identity `d`. -/
def Resolved (E : Source.Env) (scope : Option String) (w : Name) (d : Source.DeclName) : Prop :=
  ∃ decl, E.lookup scope w = [decl] ∧ decl.kind = .struct ∧ d = ⟨decl.scope, decl.name⟩
theorem Resolved.userTy {w : Name} {d : Source.DeclName} (h : Resolved E scope w d) (loc : DataLoc) :
    E.userTy scope loc ⟨w, []⟩ = some (.struct loc d) := by
  obtain ⟨decl, look, kind, rfl⟩ := h
  simp only [Source.Env.userTy, Source.Env.lookupPath, look, kind]

/-- What a spelling denotes: a primitive its marked elementary type at its own
rows (`address` also for `address payable`), an array its nesting and length, a
mapping its key and value, a struct the declaration its written name resolves to. -/
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
theorem elemB_prim {key : Name} {p : PrimTy} {e : Source.Elem}
    (he : elemB widths key p = some e) (loc : DataLoc) : Version.Prim p (e.ty loc) := by
  have hp := (Version.elemB_prim he).1
  cases e with
  | fixed s dims => cases dims <;> cases hp
  | _ => first | exact hp | cases hp
theorem arrayLen_lenLit {n : Nat} (h : n ≠ 0) :
    Source.arrayLen (.some (lenLit n)) = some (some n) := by
  have c : (lenLit n).const = some ⟨n * 10 ^ 0, 10 ^ 0, Nat.pow_pos (by decide)⟩ := rfl
  unfold Source.arrayLen
  simp only [c]
  simp [Source.Q.isInt, Source.Q.toInt, h]

mutual
/-- A successful spelling elaborates, under the resolution obligations of the
structs it mentions, to a type that represents the model type. -/
theorem spellType_typed : (T : Ty) → (key : Name) → (loc : DataLoc) →
    (t : Syn .typeName) → spellType C widths key loc T = .ok t →
    (∀ s ∈ structsTy T, ∀ w, written? C s = some w → ∃ d, Resolved E scope w d) →
    ∃ τ, t.tys E scope loc = some [τ] ∧ Rep C widths E scope key loc T τ
  | .prim p, key, loc, t, h, _ => by
      simp only [spellType] at h
      split at h <;> cases h; rename_i e he
      exact ⟨e.ty loc, rfl, .prim he (elemB_prim he loc)⟩
  | .ref R, key, loc, t, h, res =>
      spellRef_typed R key loc t (by simpa only [spellType] using h)
        (by simpa only [structsTy] using res)
theorem spellRef_typed : (R : RefTy) → (key : Name) → (loc : DataLoc) →
    (t : Syn .typeName) → spellRef C widths key loc R = .ok t →
    (∀ s ∈ structsRef R, ∀ w, written? C s = some w → ∃ d, Resolved E scope w d) →
    ∃ τ, t.tys E scope loc = some [τ] ∧ Rep C widths E scope key loc (.ref R) τ
  | .struct s, key, loc, t, h, res => by
      simp only [spellRef] at h
      split at h <;> cases h; rename_i w hw
      obtain ⟨d, hd⟩ := res s (by simp [structsRef]) w hw
      exact ⟨.struct loc d, by simp [Source.Syn.tys, hd.userTy loc], .struct hw hd⟩
  | .array T, key, loc, t, h, res => by
      simp only [spellRef, bind_ok] at h
      obtain ⟨t', ht, h⟩ := h; split at h <;> cases h
      obtain ⟨τ, typed, rep⟩ := spellType_typed T _ loc t' ht
        (by simpa only [structsRef] using res)
      exact ⟨_, by simp [Source.Syn.tys, typed, Source.arrayLen], .array rep⟩
  | .fixed T n, key, loc, t, h, res => by
      simp only [spellRef] at h
      split at h
      · cases h
      · rename_i pos
        simp only [bind_ok] at h
        obtain ⟨t', ht, h⟩ := h; cases h
        obtain ⟨τ, typed, rep⟩ := spellType_typed T _ loc t' ht
          (by simpa only [structsRef] using res)
        exact ⟨_, by simp [Source.Syn.tys, typed, arrayLen_lenLit pos],
          .fixed (Nat.pos_of_ne_zero pos) rep⟩
  | .mapping K V, key, loc, t, h, res => by
      simp only [spellRef] at h
      split at h
      · rename_i hloc; subst hloc
        split at h
        · rename_i e he
          split at h
          · cases h
          · simp only [bind_ok] at h
            obtain ⟨t', ht, h⟩ := h; cases h
            obtain ⟨τ, typed, rep⟩ := spellType_typed V _ .storage t' ht
              (by simpa only [structsRef] using res)
            exact ⟨_, by simp [Source.Syn.tys, typed, Source.Env.keyTy],
              .mapping he (elemB_prim he .memory) rep⟩
        · cases h
      · cases h
end
/-- A binder and its Source parameter's type: at its declared location (memory
where a value has none), with every row at or below it read. -/
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
theorem binders_cons {x : Name × Ty} {xs : List (Name × Ty)} {ps : Syn (.list .param)}
    (h : binders C widths locOf (x :: xs) = .ok ps) :
    ∃ l t rest, locOf x.1 x.2 = .ok l ∧ unread widths x.1 x.2 = none ∧
      spellType C widths x.1 (l.getD .memory) x.2 = .ok t ∧
      binders C widths locOf xs = .ok rest ∧ ps = .cons (.param t l (some x.1)) rest := by
  simp only [binders, binder, bind_ok] at h
  obtain ⟨p, ⟨l, hl, hp⟩, rest, hr, h⟩ := h; cases h
  split at hp
  · cases hp
  · rename_i hu
    simp only [bind_ok] at hp
    obtain ⟨t, ht, hp⟩ := hp; cases hp
    exact ⟨l, t, rest, hl, hu, ht, hr, rfl⟩
/-- One Source parameter per binder, in order, under its name, with the
location `locOf` gives it. -/
theorem binders_names :
    ∀ {xs : List (Name × Ty)} {ps : Syn (.list .param)},
      binders C widths locOf xs = .ok ps →
      ps.paramNames = xs.map (fun x => some x.1) ∧
      xs.map (fun x => locOf x.1 x.2) = (declaredLocs ps).map .ok
  | [], ps, h => by cases h; exact ⟨rfl, rfl⟩
  | x :: xs, ps, h => by
      obtain ⟨l, t, rest, hl, _, _, hr, rfl⟩ := binders_cons h
      obtain ⟨names, locs⟩ := binders_names hr
      exact ⟨by simp [Source.Syn.paramNames, names], by simp [declaredLocs, hl, locs]⟩
/-- Source elaboration of a decoded list: one type per binder, in order, each
representing it at its declared location, given resolution of the structs used. -/
theorem binders_typed :
    ∀ {xs : List (Name × Ty)} {ps : Syn (.list .param)},
      binders C widths locOf xs = .ok ps →
      (∀ x ∈ xs, ∀ s ∈ structsTy x.2, ∀ w, written? C s = some w →
        ∃ d, Resolved E scope w d) →
      ∃ τs, ps.tys E scope .memory = some τs ∧ Slots C widths E scope locOf xs τs
  | [], ps, h, _ => by cases h; exact ⟨[], rfl, .nil⟩
  | x :: xs, ps, h, res => by
      obtain ⟨l, t, rest, hl, hu, ht, hr, rfl⟩ := binders_cons h
      obtain ⟨τ, typed, rep⟩ := spellType_typed x.2 x.1 _ t ht
        (res x List.mem_cons_self)
      obtain ⟨τs, typeds, slots⟩ := binders_typed hr
        (fun y my => res y (List.mem_cons_of_mem _ my))
      exact ⟨τ :: τs, by simp [Source.Syn.tys, typed, typeds], .cons ⟨l, hl, hu, rep⟩ slots⟩

/-- `Source.Frame.mk?` accepts a successful signature, with the original ordered
names and a representing type per binder (locations: `binders_names`). Body and
flags pass through; no body semantics. -/
theorem signature_frame {d : FunDecl} {ps rs : Syn (.list .param)}
    (h : signature C d = .ok (ps, rs))
    (res : ∀ x ∈ d.params ++ d.rets, ∀ s ∈ structsTy x.2, ∀ w, written? C s = some w →
      ∃ d', Resolved E scope w d')
    (body : Syn (.list (.item .body))) (msgValue inModifier : Bool) :
    binders C d.widths (paramLoc d) d.params = .ok ps ∧
    binders C d.widths (retLoc d) d.rets = .ok rs ∧ ∃ pts rts,
      Source.Frame.mk? E scope ps rs body msgValue inModifier = some
        ⟨d.params.map (fun p => some p.1), pts, d.rets.map (fun p => some p.1), rts, body,
          msgValue, inModifier⟩ ∧
      Slots C d.widths E scope (paramLoc d) d.params pts ∧
      Slots C d.widths E scope (retLoc d) d.rets rts := by
  simp only [signature, bind_ok] at h
  obtain ⟨ps', hp, rs', hr, h⟩ := h; cases h
  obtain ⟨pts, pt, pslots⟩ := binders_typed hp
    (fun x mx => res x (List.mem_append_left _ mx))
  obtain ⟨rts, rt, rslots⟩ := binders_typed hr
    (fun x mx => res x (List.mem_append_right _ mx))
  refine ⟨hp, hr, pts, rts, ?_, pslots, rslots⟩
  simp [Source.Frame.mk?, pt, rt, (binders_names hp).1, (binders_names hr).1]

/-- The declared Source location of the parameter `x`, if any. -/
def declLoc (d : FunDecl) (x : Name) : Option DataLoc := (lookupBy x d.paramLocs).map sourceLoc
/-- The frame type `paramCtx` gives a binder at a declared Source location. -/
def frameTy (widths : List (Name × Nat)) (x : Name) : Ty → Option DataLoc → LocalTy
  | .prim p, _ => .val p ((lookupBy x widths).getD 256) (shapeUnder widths x)
  | .ref R, some .storage => .alias R (shapeUnder widths x)
  | .ref R, _ => .mem R (shapeUnder widths x)
/-- The frame merges `calldata` into `memory`; the decoded list keeps both. -/
theorem frameTy_memory_calldata (widths : List (Name × Nat)) (x : Name) (T : Ty) :
    frameTy widths x T (some .memory) = frameTy widths x T (some .calldata) := by
  cases T <;> rfl
private theorem mapM_ok {α β ε : Type} {f : α → Except ε β} {g : α → β} {P : α → Prop}
    (hf : ∀ a b, f a = .ok b → b = g a ∧ P a) :
    ∀ (l : List α) (r : List β), l.mapM f = .ok r → r = l.map g ∧ ∀ a ∈ l, P a
  | [], r, h => by cases h; exact ⟨rfl, fun _ m => nomatch m⟩
  | a :: l, r, h => by
      simp only [List.mapM_cons, bind_ok] at h
      obtain ⟨b, hb, bs, hbs, h⟩ := h; cases h
      obtain ⟨eq, all⟩ := mapM_ok hf l bs hbs
      refine ⟨by rw [(hf a b hb).1, eq]; rfl, fun a' m => ?_⟩
      rcases List.mem_cons.mp m with rfl | m'
      · exact (hf _ b hb).2
      · exact all a' m'

/-- A successful `paramCtx` is, in declaration order, each parameter at the
frame type of the location `paramLoc` reads. -/
theorem paramCtx_reverse {d : FunDecl} {Γ : ECtx} (h : d.paramCtx = .ok Γ) :
    Γ.reverse = d.params.map (fun x => (x.1, frameTy d.widths x.1 x.2 (declLoc d x.1))) ∧
      ∀ x ∈ d.params, paramLoc d x.1 x.2 = .ok (declLoc d x.1) := by
  unfold FunDecl.paramCtx at h
  obtain ⟨eq, all⟩ := mapM_ok
    (g := fun x : Name × Ty => (x.1, frameTy d.widths x.1 x.2 (declLoc d x.1)))
    (P := fun x : Name × Ty => paramLoc d x.1 x.2 = .ok (declLoc d x.1)) (by
      rintro ⟨n, T⟩ b hb
      cases hl : lookupBy n d.paramLocs with
      | none => cases T <;> simp [hl] at hb <;> subst hb <;>
          exact ⟨rfl, by simp [paramLoc, declLoc, hl]⟩
      | some l =>
          cases T <;> cases l <;> simp only [hl, Option.isSome_some, if_true] at hb <;>
            (try split at hb) <;> cases hb <;>
            exact ⟨by simp [frameTy, declLoc, hl, sourceLoc], by simp [paramLoc, declLoc, hl]⟩)
      _ _ h
  exact ⟨by rw [eq, List.map_reverse, List.reverse_reverse],
    fun x mx => all x (List.mem_reverse.mpr mx)⟩

end Solidity.Correctness.Lowering.Total.ReferenceDecode
