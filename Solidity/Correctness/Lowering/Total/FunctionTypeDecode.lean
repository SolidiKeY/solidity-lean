import Solidity.Correctness.Lowering.Total.Versions.Marked
import Solidity.Syntax.Elab.Values

/-!
# Loop lowering: retained function-type signatures

A function type is no type of the model: `expandTy` keeps its spelling as a
`RawTy.named` marker (`fnTyStr`), and the elaborator keeps that spelling in
the marker row `k#function(…) ↦ 0` beside the `uint` tag (`valueRows?`,
`fnRow?`). This module reads such a spelling back as a signature tree and
relates the tree to Source.

- `comp` (fuel) and `read` read a spelling with `fnParts?` into a `Comp Unit`:
  nested signatures, elementary components at their width (`Decode.typeNameB`),
  other names, and reference components with their recorded location.
  `ofDecl`, `ofShape` and `ofState` read a declaration's marker and the marker
  rows of a local and of a state variable.
- `Reads` is the fuel-free reading. `Reads.leaf`, `Reads.fn`, `Reads.inv` and
  `Reads.unique` are its exact structure: visibility is `fnParts?`'s flag,
  parameters and returns are read pointwise in order (`ReadsAll`), a marker
  `fnParts?` refuses has no reading (`Reads.malformed`).
- `Comp.spell` is the spelling of a tree (`fnTyStr`, annotations ignored).
- `Comp.typeName` is the Source type name of an annotated tree, over a
  compositional table `Refs` for the components this module does not read
  (user types, references). `fnType_ty`: from the component typing facts
  `RefsTyped` the type name is a `Source.Syn.fnType` whose `Source.Syn.ty` is
  exactly `STy.fn ext params returns mutability`.

## What the spelling erases

`spellFnTy`/`fnTyStr` do not record, so no reading here determines:
* the **mutability** of each function type, nested ones included (`pure`,
  `view`, `payable` or none). Trees carry it as an annotation `Ann` that the
  caller supplies; `annotate_erase` and `sty_mutability` show every choice is
  consistent with one spelling and gives a different Source type. A function
  declaration's mutability is not its variables' function types' mutability;
* whether `internal` was written or left out (`Ann.internalKeyword`; both
  denote the same Source type, `vis_external`);
* parameter and return names inside the type (read as unnamed; the Source
  type does not depend on them, `param_name_tys`);
* `address payable` (spelled `address`, read as `address`: a different Source
  type, `STy.address true`, is never produced);
* the boundary between a component's name and its location: the suffix is
  appended with no separator, so a value type named `Tmemory` and `T memory`
  have one spelling; `locSuffix` reads the location, as `canonFnTy` does;
* `uint`/`uint256` and `int`/`int256` (one Source type each).

## What is not proved

Lean's `String.startsWith`, `drop` and `endsWith` have no core lemmas and do
not reduce in the kernel, so nothing here is derived by computing `fnParts?`:
facts about it enter as hypotheses (`Reads.fn`), and the examples check
concrete spellings with `#guard`. In particular `fnParts? (fnTyStr ps rs ext)
= some (ps, rs, ext)` for well-bracketed comma-free components, and that
`read`'s fuel (the spelling's length) always suffices, are not established;
`Reads` is the proof-facing reading and `read` computes it (`read_reads`).

Open, for the original decoder: binding the `uint` tag to a function index,
whole-unit integration, which annotation the original source had, the `Refs`
table and its `RefsTyped` facts, coverage and simulation.
-/
namespace Solidity.Correctness.Lowering.Total.FunctionTypeDecode

open Source (Syn STy DataLoc)

/-! ## Signature trees -/

mutual
/-- A component of a retained signature, with an annotation `α` at each
function type. -/
inductive Comp (α : Type) where
  /-- An elementary type, at its width. -/
  | elem (e : Source.Elem)
  /-- Another name with no location: an enum, a contract, a value type. -/
  | named (c : String)
  /-- A reference component: its spelling and its recorded location. -/
  | located (base : String) (loc : DataLoc)
  /-- A function type: external or internal, parameters, returns. -/
  | fn (ext : Bool) (a : α) (ps rs : Comps α)
  deriving DecidableEq, Repr
/-- Components, in order. -/
inductive Comps (α : Type) where
  | nil
  | cons (c : Comp α) (cs : Comps α)
  deriving DecidableEq, Repr
end

mutual
/-- The tree without its annotations: what a spelling retains. -/
def Comp.erase {α : Type} : Comp α → Comp Unit
  | .elem e => .elem e
  | .named c => .named c
  | .located b l => .located b l
  | .fn ext _ ps rs => .fn ext () ps.erase rs.erase
/-- `Comp.erase`, componentwise. -/
def Comps.erase {α : Type} : Comps α → Comps Unit
  | .nil => .nil
  | .cons c cs => .cons c.erase cs.erase
end

mutual
/-- The tree with the annotation `μ` at every function type. -/
def Comp.annotate {α : Type} (μ : α) : Comp Unit → Comp α
  | .elem e => .elem e
  | .named c => .named c
  | .located b l => .located b l
  | .fn ext _ ps rs => .fn ext μ (ps.annotate μ) (rs.annotate μ)
/-- `Comp.annotate`, componentwise. -/
def Comps.annotate {α : Type} (μ : α) : Comps Unit → Comps α
  | .nil => .nil
  | .cons c cs => .cons (c.annotate μ) (cs.annotate μ)
end

/-- The components as a list. -/
def Comps.toList {α : Type} : Comps α → List (Comp α)
  | .nil => []
  | .cons c cs => c :: cs.toList

mutual
/-- Every annotation is consistent with a retained tree. -/
theorem Comp.annotate_erase {α : Type} (μ : α) : (t : Comp Unit) → (t.annotate μ).erase = t
  | .elem _ | .named _ | .located _ _ => rfl
  | .fn ext () ps rs => by
    simp only [Comp.annotate, Comp.erase, Comps.annotate_erase μ ps, Comps.annotate_erase μ rs]
/-- `Comp.annotate_erase`, componentwise. -/
theorem Comps.annotate_erase {α : Type} (μ : α) : (ts : Comps Unit) → (ts.annotate μ).erase = ts
  | .nil => rfl
  | .cons c cs => by
    simp only [Comps.annotate, Comps.erase, Comp.annotate_erase μ c, Comps.annotate_erase μ cs]
end

/-! ## Reading a spelling -/

/-- A location suffix of a component (`spellFnTy` appends it to the type with
no separator): the spelling before it, and the location. -/
def locSuffix (c : String) : Option (String × DataLoc) :=
  if c.endsWith "memory" then some (c.dropRight 6, .memory)
  else if c.endsWith "storage" then some (c.dropRight 7, .storage)
  else if c.endsWith "calldata" then some (c.dropRight 8, .calldata)
  else none

/-- A component that is no function type: an elementary type by name
(`Decode.typeNameB`: `bool`, `uintN`, `intN`, `address`, `bytesN`), else a
located reference, else a name. -/
def leaf (c : String) : Comp Unit :=
  match Decode.typeNameB (.named c) with
  | some (.elem e) => .elem e
  | _ =>
    match locSuffix c with
    | some (b, l) => .located b l
    | none => .named c

/-- Components read by `f`, in order; none is dropped. -/
def compsWith (f : String → Option (Comp Unit)) : List String → Option (Comps Unit)
  | [] => some .nil
  | c :: cs => do pure (.cons (← f c) (← compsWith f cs))

/-- A function type from `fnParts?`'s split, its components read by `f`. -/
def node (f : String → Option (Comp Unit)) :
    Option (List String × List String × Bool) → Option (Comp Unit)
  | some (ps, rs, ext) => do pure (.fn ext () (← compsWith f ps) (← compsWith f rs))
  | none => none

/-- A component: a function type by `fnParts?` (nested ones with one fuel
less), anything else a `leaf`. A function-type spelling `fnParts?` refuses is
not read. -/
def comp : Nat → String → Option (Comp Unit)
  | 0, _ => none
  | n + 1, c => if fnTy? c then node (comp n) (fnParts? c) else some (leaf c)

/-- A retained function-type spelling; fuel is its length. -/
def read (s : String) : Option (Comp Unit) :=
  if fnTy? s then comp (s.length + 1) s else none

/-- A declaration's type: the marker `expandTy` leaves for a function type. -/
def ofDecl : RawTy → Option (Comp Unit)
  | .named s => read s
  | _ => none

/-- A local's function type, from the marker row of its shape (`localFn?`). -/
def ofShape (shape : List (String × Nat)) : Option (Comp Unit) :=
  (fnRow? shape "").bind read

/-- A state variable's function type, from its marker row of the width table. -/
def ofState (widths : List (Name × Nat)) (x : Name) : Option (Comp Unit) :=
  (fnRow? widths x).bind read

/-- The fuel-free reading: some fuel reads `c` as `t`. -/
def Reads (c : String) (t : Comp Unit) : Prop := ∃ n, comp n c = some t

/-- Components read pointwise, in order, none dropped or added. -/
def ReadsAll : List String → Comps Unit → Prop
  | [], .nil => True
  | c :: cs, .cons t ts => Reads c t ∧ ReadsAll cs ts
  | _, _ => False

theorem comp_step (n : Nat) (c : String) :
    comp (n + 1) c = if fnTy? c then node (comp n) (fnParts? c) else some (leaf c) := rfl

theorem compsWith_cons {f : String → Option (Comp Unit)} {c : String} {cs : List String}
    {ts : Comps Unit} : compsWith f (c :: cs) = some ts ↔
      ∃ t ts', f c = some t ∧ compsWith f cs = some ts' ∧ ts = .cons t ts' := by
  simp only [compsWith, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.some.injEq]
  constructor
  · rintro ⟨t, ht, ts', hts, rfl⟩
    exact ⟨t, ts', ht, hts, rfl⟩
  · rintro ⟨t, ts', ht, hts, rfl⟩
    exact ⟨t, ht, ts', hts, rfl⟩

theorem node_some {f : String → Option (Comp Unit)} {ps rs : List String} {ext : Bool}
    {t : Comp Unit} : node f (some (ps, rs, ext)) = some t ↔
      ∃ P R, compsWith f ps = some P ∧ compsWith f rs = some R ∧ t = .fn ext () P R := by
  simp only [node, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.some.injEq]
  constructor
  · rintro ⟨P, hP, R, hR, rfl⟩
    exact ⟨P, R, hP, hR, rfl⟩
  · rintro ⟨P, R, hP, hR, rfl⟩
    exact ⟨P, hP, R, hR, rfl⟩

theorem compsWith_mono {f g : String → Option (Comp Unit)}
    (h : ∀ c t, f c = some t → g c = some t) :
    ∀ (cs : List String) (ts : Comps Unit), compsWith f cs = some ts → compsWith g cs = some ts
  | [], _, e => e
  | c :: cs, ts, e => by
    obtain ⟨t, ts', ht, hts, rfl⟩ := compsWith_cons.mp e
    exact compsWith_cons.mpr ⟨t, ts', h c t ht, compsWith_mono h cs ts' hts, rfl⟩

/-- More fuel reads the same tree. -/
theorem comp_succ (n : Nat) : ∀ (c : String) (t : Comp Unit),
    comp n c = some t → comp (n + 1) c = some t := by
  induction n with
  | zero =>
    intro c t h
    cases h
  | succ n ih =>
    intro c t h
    rw [comp_step] at h ⊢
    by_cases isFn : fnTy? c = true
    · rw [if_pos isFn] at h ⊢
      cases parts : fnParts? c with
      | none =>
        rw [parts] at h
        cases h
      | some x =>
        obtain ⟨ps, rs, ext⟩ := x
        rw [parts] at h
        obtain ⟨P, R, hP, hR, rfl⟩ := node_some.mp h
        exact node_some.mpr ⟨P, R, compsWith_mono ih ps P hP, compsWith_mono ih rs R hR, rfl⟩
    · rw [if_neg isFn] at h ⊢
      exact h

theorem comp_le {n m : Nat} (le : n ≤ m) {c : String} {t : Comp Unit}
    (h : comp n c = some t) : comp m c = some t := by
  induction le with
  | refl => exact h
  | step _ ih => exact comp_succ _ _ _ ih

/-- One fuel reads all the components. -/
theorem readsAll_iff : ∀ (cs : List String) (ts : Comps Unit),
    ReadsAll cs ts ↔ ∃ n, compsWith (comp n) cs = some ts
  | [], .nil => ⟨fun _ => ⟨0, rfl⟩, fun _ => trivial⟩
  | [], .cons _ _ => ⟨fun h => h.elim, fun ⟨_, h⟩ => by cases h⟩
  | _ :: _, .nil => ⟨fun h => h.elim, fun ⟨_, h⟩ => by
      obtain ⟨_, _, _, _, e⟩ := compsWith_cons.mp h
      cases e⟩
  | c :: cs, .cons t ts => by
    constructor
    · rintro ⟨⟨n, hn⟩, rest⟩
      obtain ⟨m, hm⟩ := (readsAll_iff cs ts).mp rest
      exact ⟨max n m, compsWith_cons.mpr ⟨t, ts, comp_le (Nat.le_max_left n m) hn,
        compsWith_mono (fun _ _ => comp_le (Nat.le_max_right n m)) cs ts hm, rfl⟩⟩
    · rintro ⟨n, h⟩
      obtain ⟨t', ts', ht, hts, e⟩ := compsWith_cons.mp h
      cases e
      exact ⟨⟨n, ht⟩, (readsAll_iff cs ts).mpr ⟨n, hts⟩⟩

namespace Reads

/-- A component that is no function type reads as its `leaf`. -/
theorem leaf {c : String} (h : fnTy? c = false) : Reads c (leaf c) :=
  ⟨1, by rw [comp_step, h]; rfl⟩

/-- A function type reads as `fnParts?` splits it: its visibility flag, and
its parameters and returns read in order. -/
theorem fn {c : String} {ps rs : List String} {ext : Bool} {P R : Comps Unit}
    (isFn : fnTy? c = true) (parts : fnParts? c = some (ps, rs, ext))
    (params : ReadsAll ps P) (returns : ReadsAll rs R) : Reads c (.fn ext () P R) := by
  obtain ⟨n, hn⟩ := (readsAll_iff ps P).mp params
  obtain ⟨m, hm⟩ := (readsAll_iff rs R).mp returns
  refine ⟨max n m + 1, ?_⟩
  rw [comp_step, if_pos isFn, parts]
  exact node_some.mpr ⟨P, R,
    compsWith_mono (fun _ _ => comp_le (Nat.le_max_left n m)) ps P hn,
    compsWith_mono (fun _ _ => comp_le (Nat.le_max_right n m)) rs R hm, rfl⟩

/-- Every reading is one of the two: a leaf, or a function type split by
`fnParts?` with its components read in order. -/
theorem inv {c : String} {t : Comp Unit} (h : Reads c t) :
    (fnTy? c = false ∧ t = FunctionTypeDecode.leaf c) ∨
    ∃ ps rs ext P R, fnTy? c = true ∧ fnParts? c = some (ps, rs, ext) ∧
      ReadsAll ps P ∧ ReadsAll rs R ∧ t = .fn ext () P R := by
  obtain ⟨n, h⟩ := h
  cases n with
  | zero => cases h
  | succ n =>
    rw [comp_step] at h
    by_cases isFn : fnTy? c = true
    · rw [if_pos isFn] at h
      cases parts : fnParts? c with
      | none =>
        rw [parts] at h
        cases h
      | some x =>
        obtain ⟨ps, rs, ext⟩ := x
        rw [parts] at h
        obtain ⟨P, R, hP, hR, rfl⟩ := node_some.mp h
        exact .inr ⟨ps, rs, ext, P, R, isFn, rfl, (readsAll_iff ps P).mpr ⟨n, hP⟩,
          (readsAll_iff rs R).mpr ⟨n, hR⟩, rfl⟩
    · rw [if_neg isFn] at h
      cases h
      exact .inl ⟨Bool.eq_false_iff.mpr isFn, rfl⟩

/-- A spelling has at most one reading. -/
theorem unique {c : String} {t t' : Comp Unit} (h : Reads c t) (h' : Reads c t') : t = t' := by
  obtain ⟨n, hn⟩ := h
  obtain ⟨m, hm⟩ := h'
  have a := comp_le (Nat.le_max_left n m) hn
  have b := comp_le (Nat.le_max_right n m) hm
  exact Option.some.inj (a.symm.trans b)

/-- A function-type marker `fnParts?` refuses has no reading. -/
theorem malformed {c : String} (isFn : fnTy? c = true) (parts : fnParts? c = none)
    (t : Comp Unit) : ¬ Reads c t := by
  intro h
  rcases h.inv with ⟨notFn, _⟩ | ⟨_, _, _, _, _, _, some, _⟩
  · rw [isFn] at notFn
    cases notFn
  · rw [parts] at some
    cases some

end Reads

/-- The components read are as many as the spellings. -/
theorem ReadsAll.length : ∀ {cs : List String} {ts : Comps Unit},
    ReadsAll cs ts → ts.toList.length = cs.length
  | [], .nil, _ => rfl
  | [], .cons _ _, h => h.elim
  | _ :: _, .nil, h => h.elim
  | _ :: cs, .cons _ ts, h => by
    simp only [Comps.toList, List.length_cons, ReadsAll.length h.2]

/-- The `i`-th component read is the reading of the `i`-th spelling. -/
theorem ReadsAll.get : ∀ {cs : List String} {ts : Comps Unit}, ReadsAll cs ts →
    ∀ (i : Nat) (c : String), cs[i]? = some c → ∃ t, ts.toList[i]? = some t ∧ Reads c t
  | [], .nil, _, _, _, h => by simp at h
  | [], .cons _ _, h, _, _, _ => h.elim
  | _ :: _, .nil, h, _, _, _ => h.elim
  | _ :: _, .cons t _, h, 0, c, hc => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hc
    exact ⟨t, rfl, hc ▸ h.1⟩
  | _ :: cs, .cons _ ts, h, i + 1, c, hc => by
    simp only [List.getElem?_cons_succ] at hc
    simpa only [Comps.toList, List.getElem?_cons_succ] using ReadsAll.get h.2 i c hc

theorem read_of_fn {s : String} (isFn : fnTy? s = true) : read s = comp (s.length + 1) s :=
  if_pos isFn

/-- A name that is no function-type spelling is not read as one. -/
theorem read_not_fn {s : String} (h : fnTy? s = false) : read s = none :=
  if_neg (by rw [h]; exact Bool.false_ne_true)

/-- `read` computes a reading of a function-type spelling. -/
theorem read_reads {s : String} {t : Comp Unit} (h : read s = some t) :
    fnTy? s = true ∧ Reads s t := by
  by_cases isFn : fnTy? s = true
  · exact ⟨isFn, _, (read_of_fn isFn).symm.trans h⟩
  · rw [read_not_fn (Bool.eq_false_iff.mpr isFn)] at h
    cases h

/-- What `read` returns is a function type. -/
theorem read_fn {s : String} {t : Comp Unit} (h : read s = some t) :
    ∃ ext P R, t = .fn ext () P R := by
  obtain ⟨isFn, reads⟩ := read_reads h
  rcases reads.inv with ⟨notFn, _⟩ | ⟨_, _, ext, P, R, _, _, _, _, rfl⟩
  · rw [isFn] at notFn
    cases notFn
  · exact ⟨ext, P, R, rfl⟩

/-- The marker row of a function type: the model value is a `uint` tag and
the row's key is the spelling itself (`valueRows?`). -/
theorem valueRows_fn {s : String} (isFn : fnTy? s = true) :
    valueRows? s = some (.uint, [("#" ++ s, 0)]) := by
  unfold fnTy? at isFn
  unfold valueRows?
  rw [if_pos isFn]

/-! ## Elementary components and their widths -/

/-- An elementary component is exactly `Decode.typeNameB`'s reading of its
name. -/
theorem leaf_elem {c : String} {e : Source.Elem} (h : leaf c = .elem e) :
    Decode.typeNameB (.named c) = some (.elem e) := by
  unfold leaf at h
  split at h
  · rename_i e' eq
    cases h
    exact eq
  · split at h <;> cases h

theorem uint256 : (Decode.primElem .uint 256).map Syn.elem =
    some (.elem (.int false 256 (by decide))) := rfl

theorem int256 : (Decode.primElem .int 256).map Syn.elem =
    some (.elem (.int true 256 (by decide))) := rfl

/-- The elementary type a name reads as, with its width: `bytesN` is `N`
bytes, `address`, `bool`, `uint`/`int` are 256 bits, and a narrow `uintN`/`intN`
is `N` bits (`narrowTy?`), as its own width row says (`valueRows?`). -/
theorem typeNameB_named {c : String} {T : Syn .typeName}
    (h : Decode.typeNameB (.named c) = some T) :
    (∃ n e, bytesTy? c = some n ∧ Decode.bytesElem n = some e ∧ T = .elem e) ∨
    (c = "address" ∧ T = .elem .address) ∨
    (c = "bool" ∧ T = .elem .bool) ∨
    ((c = "uint" ∨ c = "uint256") ∧ T = .elem (.int false 256 (by decide))) ∨
    ((c = "int" ∨ c = "int256") ∧ T = .elem (.int true 256 (by decide))) ∨
    (∃ p bits e, narrowTy? c = some (p, bits) ∧ Decode.primElem p bits = some e ∧
      T = .elem e) := by
  delta Decode.typeNameB at h
  dsimp only at h
  generalize hb : bytesTy? c = o at h
  cases o with
  | some n =>
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨e, he, rfl⟩ := h
    exact .inl ⟨n, e, rfl, he, rfl⟩
  | none =>
    delta Decode.typeNameA at h
    dsimp only at h
    by_cases ha : c = "address"
    · rw [if_pos ha] at h
      exact .inr (.inl ⟨ha, (Option.some.inj h).symm⟩)
    rw [if_neg ha] at h
    delta Decode.typeNameW at h
    dsimp only at h
    by_cases hbool : c = "bool"
    · rw [if_pos hbool] at h
      exact .inr (.inr (.inl ⟨hbool, (Option.some.inj h).symm⟩))
    rw [if_neg hbool] at h
    by_cases hu : c = "uint" ∨ c = "uint256"
    · rw [if_pos hu, uint256] at h
      exact .inr (.inr (.inr (.inl ⟨hu, (Option.some.inj h).symm⟩)))
    rw [if_neg hu] at h
    by_cases hi : c = "int" ∨ c = "int256"
    · rw [if_pos hi, int256] at h
      exact .inr (.inr (.inr (.inr (.inl ⟨hi, (Option.some.inj h).symm⟩))))
    rw [if_neg hi] at h
    generalize hn : narrowTy? c = o at h
    cases o with
    | none => cases h
    | some x =>
      obtain ⟨p, bits⟩ := x
      simp only [Option.map_eq_some_iff] at h
      obtain ⟨e, he, rfl⟩ := h
      exact .inr (.inr (.inr (.inr (.inr ⟨p, bits, e, rfl, he, rfl⟩))))

/-! ## Spelling a tree -/

/-- The name of an elementary type as `leaf` reads it back; other elementary
types are not components `leaf` produces. -/
def elemName : Source.Elem → String
  | .bool => "bool"
  | .address => "address"
  | .int false bits _ => if bits = 256 then "uint" else s!"uint{bits}"
  | .int true bits _ => if bits = 256 then "int" else s!"int{bits}"
  | .fixedBytes n _ => s!"bytes{n}"
  | .addressPayable => "address payable"
  | .string => "string"
  | .bytes => "bytes"
  | .fixed _ _ => "fixed"

/-- A location, as `spellFnTy` appends it. -/
def locName : DataLoc → String
  | .memory => "memory"
  | .storage => "storage"
  | .calldata => "calldata"

mutual
/-- The spelling of a tree (`fnTyStr`); annotations are not spelled. -/
def Comp.spell {α : Type} : Comp α → String
  | .elem e => elemName e
  | .named c => c
  | .located b l => b ++ locName l
  | .fn ext _ ps rs => fnTyStr ps.spells rs.spells ext
/-- The spellings of components, in order. -/
def Comps.spells {α : Type} : Comps α → List String
  | .nil => []
  | .cons c cs => c.spell :: cs.spells
end

mutual
/-- Trees with one erasure have one spelling: the spelling retains no
annotation. -/
theorem Comp.spell_erase {α : Type} : (t : Comp α) → t.erase.spell = t.spell
  | .elem _ | .named _ | .located _ _ => rfl
  | .fn _ _ ps rs => by
    simp only [Comp.erase, Comp.spell, Comps.spells_erase ps, Comps.spells_erase rs]
/-- `Comp.spell_erase`, componentwise. -/
theorem Comps.spells_erase {α : Type} : (ts : Comps α) → ts.erase.spells = ts.spells
  | .nil => rfl
  | .cons c cs => by
    simp only [Comps.erase, Comps.spells, Comp.spell_erase c, Comps.spells_erase cs]
end

/-- Parameters and returns are spelled in order, one spelling each. -/
theorem Comps.spells_eq {α : Type} : (ts : Comps α) → ts.spells = ts.toList.map Comp.spell
  | .nil => rfl
  | .cons _ cs => by simp only [Comps.spells, Comps.toList, List.map_cons, Comps.spells_eq cs]

/-! ## Source type names -/

/-- What a spelling does not retain at a function type, supplied by the
caller: its mutability, and whether an internal one wrote `internal`. -/
structure Ann where
  mutability : Option Source.Mutability
  internalKeyword : Bool := false
  deriving DecidableEq, Repr

/-- The Source visibility: `external` exactly as retained. -/
def Ann.vis (a : Ann) (ext : Bool) : Option Source.Visibility :=
  if ext then some .external else if a.internalKeyword then some .internal else none

/-- The retained flag is the Source type's: an internal type is internal
whether or not the keyword was written. -/
theorem Ann.vis_external (a : Ann) (ext : Bool) : (a.vis ext == some .external) = ext := by
  cases ext <;> cases h : a.internalKeyword <;> simp [Ann.vis, h]

/-- The components this module does not read, by spelling: a name with no
location, and the type before a location. A reference decoder supplies it. -/
structure Refs where
  value : String → Option (Syn .typeName)
  located : String → Option (Syn .typeName)

/-- No user type or reference component: elementary and function types only. -/
def Refs.none : Refs := ⟨fun _ => Option.none, fun _ => Option.none⟩

/-- A component's recorded location: a reference component's own. -/
def Comp.loc {α : Type} : Comp α → Option DataLoc
  | .located _ l => some l
  | _ => none

mutual
/-- The Source type name of a component. -/
def Comp.typeName (refs : Refs) : Comp Ann → Option (Syn .typeName)
  | .elem e => some (.elem e)
  | .named c => refs.value c
  | .located b _ => refs.located b
  | .fn ext a ps rs => do
    pure (.fnType (← ps.params refs) (a.vis ext) a.mutability (← rs.params refs))
/-- Parameters or returns, in order: each component at its recorded location,
unnamed. -/
def Comps.params (refs : Refs) : Comps Ann → Option (Syn (.list .param))
  | .nil => some .nil
  | .cons c cs => do pure (.cons (.param (← c.typeName refs) c.loc none) (← cs.params refs))
end

/-- The Source types of the components `Refs` supplies: a name's, and a
located type's at each location. -/
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
def Comp.sty (ρ : RefTys) : Comp Ann → Option STy
  | .elem e => some (e.ty .memory)
  | .named c => ρ.value c
  | .located b l => ρ.located b l
  | .fn ext a ps rs => do pure (.fn ext (← ps.stys ρ) (← rs.stys ρ) a.mutability)
/-- The Source types of components, in order. -/
def Comps.stys (ρ : RefTys) : Comps Ann → Option (List STy)
  | .nil => some []
  | .cons c cs => do pure ((← c.sty ρ) :: (← cs.stys ρ))
end

/-- A parameter's name is not part of its type. -/
theorem param_name_tys (E : Source.Env) (scope : Option String) (loc : DataLoc)
    (T : Syn .typeName) (l : Option DataLoc) (name : Option String) :
    (Syn.param T l name).tys E scope loc = (Syn.param T l none).tys E scope loc := rfl

section Typing

variable {E : Source.Env} {scope : Option String} {refs : Refs} {ρ : RefTys}

mutual
/-- A component's type name denotes its type, at its recorded location. -/
theorem Comp.typeName_tys (typed : RefsTyped E scope refs ρ) :
    (t : Comp Ann) → {T : Syn .typeName} → {τ : STy} → t.typeName refs = some T →
      t.sty ρ = some τ → T.tys E scope (t.loc.getD .memory) = some [τ]
  | .elem e, T, τ, hT, hτ => by
    simp only [Comp.typeName, Option.some.injEq] at hT
    simp only [Comp.sty, Option.some.injEq] at hτ
    subst hT hτ
    rfl
  | .named c, T, τ, hT, hτ => typed.value hT hτ
  | .located b l, T, τ, hT, hτ => typed.located hT hτ
  | .fn ext a ps rs, T, τ, hT, hτ => by
    simp only [Comp.typeName, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.some.injEq] at hT
    simp only [Comp.sty, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.some.injEq] at hτ
    obtain ⟨P, hP, R, hR, rfl⟩ := hT
    obtain ⟨πs, hπ, ρs, hρ, rfl⟩ := hτ
    simp only [Syn.tys, Comps.params_tys typed ps hP hπ, Comps.params_tys typed rs hR hρ,
      Ann.vis_external]
/-- Parameters and returns denote their types, in order. -/
theorem Comps.params_tys (typed : RefsTyped E scope refs ρ) :
    (ts : Comps Ann) → {P : Syn (.list .param)} → {τs : List STy} → ts.params refs = some P →
      ts.stys ρ = some τs → P.tys E scope .memory = some τs
  | .nil, P, τs, hP, hτ => by
    simp only [Comps.params, Option.some.injEq] at hP
    simp only [Comps.stys, Option.some.injEq] at hτ
    subst hP hτ
    rfl
  | .cons c cs, P, τs, hP, hτ => by
    simp only [Comps.params, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.some.injEq] at hP
    simp only [Comps.stys, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.some.injEq] at hτ
    obtain ⟨T, hT, P', hP', rfl⟩ := hP
    obtain ⟨τ, hτ', τs', hτs', rfl⟩ := hτ
    simp only [Syn.tys, Comp.typeName_tys typed c hT hτ', Comps.params_tys typed cs hP' hτs',
      List.singleton_append]
end

/-- **The Source function type of a retained signature.** Given the component
typing facts, a tree's type name is a `Source.Syn.fnType` with the retained
visibility, the components in order and the supplied mutability, and it
denotes exactly `STy.fn ext params returns mutability`, at every location. -/
theorem fnType_ty (typed : RefsTyped E scope refs ρ) {ext : Bool} {a : Ann} {ps rs : Comps Ann}
    {T : Syn .typeName} {πs ρs : List STy} (loc : DataLoc)
    (hT : (Comp.fn ext a ps rs).typeName refs = some T)
    (hπ : ps.stys ρ = some πs) (hρ : rs.stys ρ = some ρs) :
    (∃ P R, ps.params refs = some P ∧ rs.params refs = some R ∧
      T = .fnType P (a.vis ext) a.mutability R ∧
      P.tys E scope .memory = some πs ∧ R.tys E scope .memory = some ρs) ∧
    T.ty E scope loc = some (.fn ext πs ρs a.mutability) := by
  simp only [Comp.typeName, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.some.injEq] at hT
  obtain ⟨P, hP, R, hR, rfl⟩ := hT
  have tP := Comps.params_tys typed ps hP hπ
  have tR := Comps.params_tys typed rs hR hρ
  refine ⟨⟨P, R, hP, hR, rfl, tP, tR⟩, ?_⟩
  simp only [Syn.ty, Syn.tys, tP, tR, Ann.vis_external]

end Typing

/-- Elementary and function-type components need no component facts. -/
theorem RefsTyped.none (E : Source.Env) (scope : Option String) (ρ : RefTys) :
    RefsTyped E scope Refs.none ρ :=
  { value := fun h => (by cases h), located := fun h => (by cases h) }

/-! ## Mutability is not retained -/

/-- The mutability of a function type's Source type is the annotation's:
annotations of different mutability give different Source types. -/
theorem sty_mutability {ρ : RefTys} {ext : Bool} {a b : Ann} {ps rs ps' rs' : Comps Ann}
    {τ : STy} (ha : (Comp.fn ext a ps rs).sty ρ = some τ)
    (hb : (Comp.fn ext b ps' rs').sty ρ = some τ) : a.mutability = b.mutability := by
  simp only [Comp.sty, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.some.injEq] at ha hb
  obtain ⟨_, _, _, _, ea⟩ := ha
  obtain ⟨_, _, _, _, eb⟩ := hb
  injection ea.trans eb.symm

/-- **Mutability ambiguity.** One reading, annotated two ways, has one
spelling and one erasure; where both annotations have a Source type and their
mutabilities differ, the Source types differ. The retained signature does not
determine which the source had. -/
theorem mutability_ambiguous (ρ : RefTys) {ext : Bool} {P R : Comps Unit} (a b : Ann)
    (differ : a.mutability ≠ b.mutability) :
    let t := Comp.fn ext () P R
    (t.annotate a).erase = (t.annotate b).erase ∧ (t.annotate a).spell = (t.annotate b).spell ∧
      ∀ τ τ', (t.annotate a).sty ρ = some τ → (t.annotate b).sty ρ = some τ' → τ ≠ τ' := by
  intro t
  refine ⟨by rw [Comp.annotate_erase, Comp.annotate_erase], ?_, ?_⟩
  · rw [← Comp.spell_erase, Comp.annotate_erase, ← Comp.spell_erase (t.annotate b),
      Comp.annotate_erase]
  · rintro τ _ ha hb rfl
    exact differ (sty_mutability ha hb)

end Solidity.Correctness.Lowering.Total.FunctionTypeDecode
