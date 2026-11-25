import Solidity.Correctness.Lowering.Total.Versions.Marked
import Solidity.Syntax.Elab.Values

/-!
# Loop lowering: retained function-type signatures

`expandTy` keeps a function type as its spelling (`RawTy.named (fnTyStr …)`),
and the elaborator keeps it in the marker row `k#function(…) ↦ 0` beside the
`uint` tag (`valueRows?`, `fnRow?`). Here a spelling is read back as a tree
(`part`, `readSig`, by `fnParts?`; `ofDecl`, `ofRows`) whose exact
structure is `part_fn`, `part_leaf` and `part_malformed` (visibility flag,
parameters and returns pointwise in order, nesting; `leaf_elem`: elementary
components at `Decode.typeNameB`'s type and width; reference components with
their recorded location), `Part.spell` spells a tree, and `fnType_ty` gives, from the component typing facts `RefsTyped` of a compositional table
`Refs`, the `Source.Syn.fnType` denoting exactly `STy.fn ext params returns
mutability`.

Erased by `spellFnTy`/`fnTyStr`, so determined by no reading:
* each function type's **mutability** (nested ones too): the annotation `Ann`
  the caller supplies; `mutability_ambiguous`: one spelling, different Source
  types. A declaration's mutability is not its variables' function types';
* whether `internal` was written (`Ann.internalKeyword`, same Source type),
  and the modifier list's order, repetition and a contradictory `internal
  external` (one flag is kept: whether `external` occurs);
* `address payable` (spelled and read `address`); an empty `returns ()`; how
  a fixed array's length was written;
* the boundary between a component's type and its location (no separator:
  `Tmemory` is also `T memory`). `locSuffix` reads any location suffix, the
  base possibly empty; the elaborator reads fewer (`canonFnTy`: `[]memory`,
  `[]storage` after a primitive; `fnRefStruct?`: a struct of the contract).
Parameter names cannot be written in a function type, so none is erased.

The reading is finer than the elaborator's signature equality (`canonFnTy`
reads `uint256`, `address` and enums as `uint`), merges `uint`/`uint256` and
`int`/`int256`, validates no name (any other component is a `Part.named`;
`Refs` decides), and refuses a component that starts as a function type and
continues (`function(uint)[]memory`, which `spellFnTy` can spell).

Not proved: `String.startsWith`, `drop`, `endsWith` have no core lemmas and
do not reduce in the kernel, so `fnParts?` is never computed in a proof. Its
equations are hypotheses (`part_fn`; only its guard, `fnTy_of_parts`, is
proved); concrete spellings are `#guard` checks. That `fnParts? (fnTyStr ps rs
ext) = some (ps, rs, ext)` on well-bracketed components (so that a spelled
tree reads back), that more fuel reads the same and that `readSig`'s fuel
suffices are open, as are, for the
original decoder: function-index binding, unit integration, which annotation
the source had, the `Refs` table and its facts, coverage and simulation.
-/
namespace Solidity.Correctness.Lowering.Total.FunctionTypeDecode

open Source (Syn STy DataLoc)

mutual
/-- A component of a retained signature, annotated by `α` at function types. -/
inductive Part (α : Type) where
  /-- An elementary type, at its width. -/
  | elem (e : Source.Elem)
  /-- Any other component with no location suffix, as spelled. -/
  | named (c : String)
  /-- A reference component: its spelling and its recorded location. -/
  | located (base : String) (loc : DataLoc)
  /-- A function type: external or internal, parameters, returns. -/
  | fn (ext : Bool) (a : α) (ps rs : Parts α)
  deriving DecidableEq, Repr
/-- Components, in order. -/
inductive Parts (α : Type) where
  | nil
  | cons (c : Part α) (cs : Parts α)
  deriving DecidableEq, Repr
end

mutual
/-- The tree without its annotations: what a spelling retains. -/
def Part.erase {α : Type} : Part α → Part Unit
  | .elem e => .elem e
  | .named c => .named c
  | .located b l => .located b l
  | .fn ext _ ps rs => .fn ext () ps.erase rs.erase
def Parts.erase {α : Type} : Parts α → Parts Unit
  | .nil => .nil
  | .cons c cs => .cons c.erase cs.erase
end

/-- A component's location suffix (`spellFnTy` appends it, no separator). -/
def locSuffix (c : String) : Option (String × DataLoc) :=
  if c.endsWith "memory" then some (c.dropRight 6, .memory)
  else if c.endsWith "storage" then some (c.dropRight 7, .storage)
  else if c.endsWith "calldata" then some (c.dropRight 8, .calldata)
  else none

/-- A component that is no function type: an elementary type by name
(`Decode.typeNameB`: `bool`, `uintN`, `intN`, `address`, `bytesN`), else a
located reference, else a name. -/
def leaf (c : String) : Part Unit :=
  match Decode.typeNameB (.named c) with
  | some (.elem e) => .elem e
  | _ =>
    match locSuffix c with
    | some (b, l) => .located b l
    | none => .named c

/-- Components read by `f`, in order; none is dropped. -/
def partsWith (f : String → Option (Part Unit)) : List String → Option (Parts Unit)
  | [] => some .nil
  | c :: cs => do pure (.cons (← f c) (← partsWith f cs))

/-- A function type from `fnParts?`'s split, its components read by `f`. -/
def node (f : String → Option (Part Unit)) :
    Option (List String × List String × Bool) → Option (Part Unit)
  | some (ps, rs, ext) =>
    (partsWith f ps).bind fun P => (partsWith f rs).map fun R => .fn ext () P R
  | none => none

/-- A component: a function type by `fnParts?` (nested ones with one fuel
less, refused if `fnParts?` refuses), anything else a `leaf`. -/
def part : Nat → String → Option (Part Unit)
  | 0, _ => none
  | n + 1, c => if fnTy? c then node (part n) (fnParts? c) else some (leaf c)

/-- A retained function-type spelling; fuel is its length. -/
def readSig (s : String) : Option (Part Unit) :=
  if fnTy? s then part (s.length + 1) s else none

/-- A declaration's type: the marker `expandTy` leaves for a function type. -/
def ofDecl : RawTy → Option (Part Unit)
  | .named s => readSig s
  | _ => none

/-- The function type at the key `k` of marker rows (`fnRow?`): a local's
shape at `""`, the width table at a state variable's name. -/
def ofRows (rows : List (String × Nat)) (k : String) : Option (Part Unit) :=
  (fnRow? rows k).bind readSig

/-- What `fnParts?` splits is a function-type spelling. -/
theorem fnTy_of_parts {s : String} {x : List String × List String × Bool}
    (h : fnParts? s = some x) : fnTy? s = true := by
  by_cases isFn : fnTy? s = true
  · exact isFn
  · unfold fnParts? at h
    simp only [guard, isFn] at h
    cases h

/-- A function type reads exactly as `fnParts?` splits it: its visibility
flag, and its parameters and returns each read in order with the fuel left
(`partsWith`: pointwise, none dropped), nested signatures included. -/
theorem part_fn (n : Nat) {c : String} {ps rs : List String} {ext : Bool}
    (parts : fnParts? c = some (ps, rs, ext)) :
    part (n + 1) c = (partsWith (part n) ps).bind fun P =>
      (partsWith (part n) rs).map fun R => .fn ext () P R := by
  show (if fnTy? c then node (part n) (fnParts? c) else some (leaf c)) = _
  rw [if_pos (fnTy_of_parts parts), parts]
  rfl

/-- A component that is no function type reads as its `leaf`. -/
theorem part_leaf (n : Nat) {c : String} (h : fnTy? c = false) :
    part (n + 1) c = some (leaf c) :=
  if_neg (by rw [h]; exact Bool.false_ne_true)

/-- A function-type marker `fnParts?` refuses is not read, at any fuel. -/
theorem part_malformed {c : String} (isFn : fnTy? c = true) (parts : fnParts? c = none) :
    ∀ n, part n c = none
  | 0 => rfl
  | n + 1 => by
    show (if fnTy? c then node (part n) (fnParts? c) else some (leaf c)) = _
    rw [if_pos isFn, parts]
    rfl

/-- A function type's marker row: a `uint` tag, keyed by the spelling. -/
theorem valueRows_fn {s : String} (isFn : fnTy? s = true) :
    valueRows? s = some (.uint, [("#" ++ s, 0)]) := by
  unfold fnTy? at isFn
  unfold valueRows?
  rw [if_pos isFn]

/-- An elementary component is `Decode.typeNameB`'s reading of its name. -/
theorem leaf_elem {c : String} {e : Source.Elem} (h : leaf c = .elem e) :
    Decode.typeNameB (.named c) = some (.elem e) := by
  unfold leaf at h
  split at h
  · rename_i e' eq
    cases h
    exact eq
  · split at h <;> cases h

/-- The name `leaf` reads an elementary type from; `leaf` produces no other. -/
def elemName : Source.Elem → String
  | .bool => "bool"
  | .address => "address"
  | .int false bits _ => if bits = 256 then "uint" else s!"uint{bits}"
  | .int true bits _ => if bits = 256 then "int" else s!"int{bits}"
  | .fixedBytes n _ => s!"bytes{n}"
  | _ => ""

/-- A location, as `spellFnTy` appends it. -/
def locName : DataLoc → String
  | .memory => "memory"
  | .storage => "storage"
  | .calldata => "calldata"

mutual
/-- The spelling of a tree (`fnTyStr`); annotations are not spelled. -/
def Part.spell {α : Type} : Part α → String
  | .elem e => elemName e
  | .named c => c
  | .located b l => b ++ locName l
  | .fn ext _ ps rs => fnTyStr ps.spells rs.spells ext
def Parts.spells {α : Type} : Parts α → List String
  | .nil => []
  | .cons c cs => c.spell :: cs.spells
end

/-- What a spelling does not retain at a function type, supplied by the
caller: its mutability, and whether an internal one wrote `internal`. -/
structure Ann where
  mutability : Option Source.Mutability
  internalKeyword : Bool := false
  deriving DecidableEq, Repr

/-- The Source visibility: `external` exactly as retained. -/
def Ann.vis (a : Ann) (ext : Bool) : Option Source.Visibility :=
  if ext then some .external else if a.internalKeyword then some .internal else none

/-- The retained flag is the Source type's, whether or not `internal` was written. -/
theorem Ann.vis_external (a : Ann) (ext : Bool) : (a.vis ext == some .external) = ext := by
  cases ext <;> cases h : a.internalKeyword <;> simp [Ann.vis, h]

/-- The components this module does not read, by spelling: a name with no
location, and the type before a location. A reference decoder supplies it. -/
structure Refs where
  value : String → Option (Syn .typeName)
  located : String → Option (Syn .typeName)

/-- A component's recorded location: a reference component's own. -/
def Part.loc {α : Type} : Part α → Option DataLoc
  | .located _ l => some l
  | _ => none

mutual
/-- The Source type name of a component. -/
def Part.typeName (refs : Refs) : Part Ann → Option (Syn .typeName)
  | .elem e => some (.elem e)
  | .named c => refs.value c
  | .located b _ => refs.located b
  | .fn ext a ps rs => do
    pure (.fnType (← ps.params refs) (a.vis ext) a.mutability (← rs.params refs))
/-- Parameters or returns, in order, each at its recorded location. -/
def Parts.params (refs : Refs) : Parts Ann → Option (Syn (.list .param))
  | .nil => some .nil
  | .cons c cs => do pure (.cons (.param (← c.typeName refs) c.loc none) (← cs.params refs))
end

/-- The Source types of the components `Refs` supplies. -/
structure RefTys where
  value : String → Option STy
  located : String → DataLoc → Option STy

/-- The component typing facts: each supplied type name denotes, in the
environment, the type `ρ` states for it (at the component's location). -/
structure RefsTyped (E : Source.Env) (scope : Option String) (refs : Refs) (ρ : RefTys) :
    Prop where
  value : ∀ {c : String} {T : Syn .typeName} {τ : STy},
    refs.value c = some T → ρ.value c = some τ → T.tys E scope .memory = some [τ]
  located : ∀ {b : String} {l : DataLoc} {T : Syn .typeName} {τ : STy},
    refs.located b = some T → ρ.located b l = some τ → T.tys E scope l = some [τ]

mutual
/-- The Source type of a component, from the component types `ρ`. -/
def Part.sty (ρ : RefTys) : Part Ann → Option STy
  | .elem e => some (e.ty .memory)
  | .named c => ρ.value c
  | .located b l => ρ.located b l
  | .fn ext a ps rs => do pure (.fn ext (← ps.stys ρ) (← rs.stys ρ) a.mutability)
def Parts.stys (ρ : RefTys) : Parts Ann → Option (List STy)
  | .nil => some []
  | .cons c cs => do pure ((← c.sty ρ) :: (← cs.stys ρ))
end

section Typing

variable {E : Source.Env} {scope : Option String} {refs : Refs} {ρ : RefTys}

mutual
/-- A component's type name denotes its type, at its recorded location. -/
theorem Part.typeName_tys (typed : RefsTyped E scope refs ρ) :
    (t : Part Ann) → {T : Syn .typeName} → {τ : STy} → t.typeName refs = some T →
      t.sty ρ = some τ → T.tys E scope (t.loc.getD .memory) = some [τ]
  | .elem e, T, τ, hT, hτ => by
    cases hT
    cases hτ
    rfl
  | .named c, T, τ, hT, hτ => typed.value hT hτ
  | .located b l, T, τ, hT, hτ => typed.located hT hτ
  | .fn ext a ps rs, T, τ, hT, hτ => by
    simp only [Part.typeName, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.some.injEq] at hT
    simp only [Part.sty, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.some.injEq] at hτ
    obtain ⟨P, hP, R, hR, rfl⟩ := hT
    obtain ⟨πs, hπ, ρs, hρ, rfl⟩ := hτ
    simp only [Syn.tys, Parts.params_tys typed ps hP hπ, Parts.params_tys typed rs hR hρ,
      Ann.vis_external]
/-- Parameters and returns denote their types, in order. -/
theorem Parts.params_tys (typed : RefsTyped E scope refs ρ) :
    (ts : Parts Ann) → {P : Syn (.list .param)} → {τs : List STy} →
      ts.params refs = some P → ts.stys ρ = some τs → P.tys E scope .memory = some τs
  | .nil, P, τs, hP, hτ => by
    cases hP
    cases hτ
    rfl
  | .cons c cs, P, τs, hP, hτ => by
    simp only [Parts.params, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.some.injEq] at hP
    simp only [Parts.stys, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.some.injEq] at hτ
    obtain ⟨T, hT, P', hP', rfl⟩ := hP
    obtain ⟨τ, hτ', τs', hτs', rfl⟩ := hτ
    simp only [Syn.tys, Part.typeName_tys typed c hT hτ', Parts.params_tys typed cs hP' hτs',
      List.singleton_append]
end

/-- **The Source function type of a retained signature.** Given the component
typing facts, a tree's type name is a `Source.Syn.fnType` with the retained
visibility, the components in order and the supplied mutability, and it
denotes exactly `STy.fn ext params returns mutability`, at every location. -/
theorem fnType_ty (typed : RefsTyped E scope refs ρ) (ext : Bool) (a : Ann) (ps rs : Parts Ann)
    {T : Syn .typeName} {πs ρs : List STy} (loc : DataLoc)
    (hT : (Part.fn ext a ps rs).typeName refs = some T)
    (hπ : ps.stys ρ = some πs) (hρ : rs.stys ρ = some ρs) :
    (∃ P R, ps.params refs = some P ∧ rs.params refs = some R ∧
      T = .fnType P (a.vis ext) a.mutability R ∧
      P.tys E scope .memory = some πs ∧ R.tys E scope .memory = some ρs) ∧
    T.ty E scope loc = some (.fn ext πs ρs a.mutability) := by
  simp only [Part.typeName, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.some.injEq] at hT
  obtain ⟨P, hP, R, hR, rfl⟩ := hT
  have tP := Parts.params_tys typed ps hP hπ
  have tR := Parts.params_tys typed rs hR hρ
  refine ⟨⟨P, R, hP, hR, rfl, tP, tR⟩, ?_⟩
  simp only [Syn.ty, Syn.tys, tP, tR, Ann.vis_external]

end Typing

/-- A function type's Source mutability is its annotation's. -/
theorem sty_mutability {ρ : RefTys} {ext : Bool} {a b : Ann} {ps rs ps' rs' : Parts Ann}
    {τ : STy} (ha : (Part.fn ext a ps rs).sty ρ = some τ)
    (hb : (Part.fn ext b ps' rs').sty ρ = some τ) : a.mutability = b.mutability := by
  simp only [Part.sty, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.some.injEq] at ha hb
  obtain ⟨_, _, _, _, ea⟩ := ha
  obtain ⟨_, _, _, _, eb⟩ := hb
  injection ea.trans eb.symm

/-- **Mutability ambiguity.** Function types that differ only in the root
annotation have one erasure and one spelling; where both have a Source type
and the mutabilities differ, the Source types differ. -/
theorem mutability_ambiguous (ρ : RefTys) (ext : Bool) (ps rs : Parts Ann) {a b : Ann}
    (differ : a.mutability ≠ b.mutability) :
    (Part.fn ext a ps rs).erase = (Part.fn ext b ps rs).erase ∧
      (Part.fn ext a ps rs).spell = (Part.fn ext b ps rs).spell ∧
      ∀ τ τ', (Part.fn ext a ps rs).sty ρ = some τ → (Part.fn ext b ps rs).sty ρ = some τ' →
        τ ≠ τ' :=
  ⟨rfl, rfl, fun _ _ ha hb eq => differ (sty_mutability ha (eq ▸ hb))⟩

end Solidity.Correctness.Lowering.Total.FunctionTypeDecode
