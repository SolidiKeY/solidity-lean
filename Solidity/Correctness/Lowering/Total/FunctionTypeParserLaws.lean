import Solidity.Correctness.Lowering.Total.FunctionTypeParserLaws.Delimiters

/-!
# Loop lowering: laws of the retained function-signature parser

`FunctionTypeDecode` reads a retained function type with `fnParts?` and takes
its equations as hypotheses. Here they are proved, in the kernel, about the
existing `fnParts?`, `fnTyStr` and `splitTopCommas` (no native evaluation; the
`String` operations by `FunctionTypeParserLaws/Strings`, the scanners by
`FunctionTypeParserLaws/Delimiters`).

* `fnParts?_mk`: on every spelling, read or refused, `fnParts?` is `partsL` of
  its characters (its own `close` and `splitTop`, list tests for the `String`
  ones). A concrete spelling is then decided in the kernel.
* `fnParts?_fnTyStr`: `fnParts? (fnTyStr ps rs ext) = some (ps, rs, ext)` when
  every parameter is `Well` and every return is `SplitOk`: for either flag,
  empty or nonempty lists, any nesting. `splitTopCommas_intercalate`,
  `fnTy?_fnTyStr` (unconditional) and `fnTyStr_inj` are its parts and corollary.
* `well_fnTyStr`, `well_plain`, `Well.append`, `Well.index`, `Covered`: the
  conditions hold for plain names, for function types of such components to
  any depth, and with a location or array suffix (`fnParts?_covered`).

## The conditions, and what stays open

`SplitOk c`: `c` is not empty, has no comma at bracket depth `0`, never
closes (`}` `)` `]`) below depth `0`, and ends at depth `0`. `CloseOk c`: only
the two depth conditions, over `(` `[` / `)` `]` as `close` counts. Depth is
counted as the algorithms count it: bracket kinds are not matched (`(]` is
accepted). They are decidable syntactic conditions on the component strings,
sufficient for the two delimiter algorithms; they are not shown necessary. A signature some component of which
fails them is an unresolved representation obligation of the original
decoder, not excluded here and no premise of `lowerLoopsCorrect`:

* a lone empty component (`fnTyStr [""] [] e` reads back `[]`);
* a comma at a component's own depth (`fnTyStr ["a,b"]` and `fnTyStr ["a",
  "b"]` are one spelling: ambiguous, it reads as two components);
* a component closing below its depth or leaving a bracket open (the
  parameter list ends early, components merge, or the spelling is refused);
* any text `fnTyStr` does not produce: `fnParts?_mk` says what `fnParts?`
  does with it, and nothing relates the result to a signature.

Nothing here recovers what `fnTyStr` erases (mutability, whether `internal`
was written, `payable`, the boundary between a component and its location: a
component comes back as the string it was), validates a component as a type,
or reads `Part` trees: the reader, its fuel, annotation agreement, unit
integration, coverage and simulation stay with the original decoder.
-/
namespace Solidity.Correctness.Lowering.Total.FunctionTypeParserLaws

open Solidity.Semantics.StructEnc (splitTop)
open Str (sepJoin)

/-! ## The parser on character lists -/

/-- `splitTopCommas` on a character list. -/
def splitL (l : List Char) : List String :=
  if l = [] then [] else (splitTop ',' 0 [] l).map String.mk

/-- `fnParts?`'s reading of what follows the visibility: nothing, or
`returns(` … `)`. -/
def returnsL (rest : List Char) : Option (List String) :=
  if rest = [] then some []
  else if rest.take 8 = "returns(".data ∧ rest.drop (rest.length - 1) = [')'] then
    some (splitL ((rest.drop 8).take ((rest.drop 8).length - 1)))
  else none

/-- `fnParts?` on a character list: the same `close` and `splitTop`, the
`String` tests as list equations. -/
def partsL (l : List Char) : Option (List String × List String × Bool) :=
  if l.take 9 = "function(".data then
    (fnParts?.close 0 [] (l.drop 9)).bind fun x =>
      (returnsL (if x.2.take 8 = "external".data then x.2.drop 8 else x.2)).map fun rs =>
        (splitL x.1, rs, decide (x.2.take 8 = "external".data))
  else none

theorem startsWith_lit (l : List Char) (p : String) :
    (String.mk l).startsWith p = decide (l.take p.length = p.data) :=
  Str.startsWith_mk l p.data

theorem endsWith_lit (l : List Char) (p : String) :
    (String.mk l).endsWith p = decide (l.drop (l.length - p.length) = p.data) :=
  Str.endsWith_mk l p.data

theorem splitTopCommas_mk (l : List Char) : splitTopCommas ⟨l⟩ = splitL l := by
  simp [splitTopCommas, splitL, Str.isEmpty_mk]

theorem fnTy?_mk (l : List Char) : fnTy? ⟨l⟩ = decide (l.take 9 = "function(".data) :=
  startsWith_lit l "function("

/-- The returns clause, as `fnParts?` tests it with `String` operations. -/
theorem returns_mk (ps r : List Char) (e : Bool) :
    (if (String.mk r).isEmpty = true then some (splitTopCommas ⟨ps⟩, [], e)
      else if ((String.mk r).startsWith "returns(" && (String.mk r).endsWith ")") = true then
        some (splitTopCommas ⟨ps⟩, splitTopCommas (((String.mk r).drop 8).dropRight 1), e)
      else (none : Option (List String)).bind fun y => some (splitTopCommas ⟨ps⟩, y, e))
      = (returnsL r).map fun rs => (splitL ps, rs, e) := by
  have r8 : "returns(".length = 8 := rfl
  have c1 : ")".length = 1 := rfl
  simp only [Str.isEmpty_mk, startsWith_lit, endsWith_lit, Str.drop_mk, Str.dropRight_mk,
    splitTopCommas_mk, r8, c1, returnsL, List.isEmpty_iff, Bool.and_eq_true,
    decide_eq_true_eq, Option.bind_none]
  split
  · rfl
  · split <;> rfl

/-- `fnParts?` is `partsL` of the characters: every `String` test and cut it
makes is the list one. This holds for every spelling, read or refused. -/
theorem fnParts?_mk (l : List Char) : fnParts? ⟨l⟩ = partsL l := by
  unfold fnParts? partsL
  simp only [fnTy?_mk]
  by_cases h : l.take 9 = "function(".data
  · have e8 : "external".length = 8 := rfl
    simp only [h, decide_true, guard, if_true]
    cases hc : fnParts?.close 0 [] (l.drop 9) with
    | none => simp [Str.drop_mk, hc]
    | some x =>
      obtain ⟨ps, rest⟩ := x
      simp only [Str.drop_mk, String.toList, hc, startsWith_lit, e8, Option.pure_def,
        Option.bind_eq_bind, Option.bind_some]
      by_cases he : rest.take 8 = "external".data
      · simp only [he, decide_true, if_true]
        exact returns_mk ps (rest.drop 8) true
      · simp only [he, decide_false, if_false, Bool.false_eq_true]
        exact returns_mk ps rest false
  · simp [h, guard]

/-! ## The spelling on character lists -/

/-- `fnTyStr`'s visibility text. -/
def visL (ext : Bool) : List Char := if ext then "external".data else []

/-- `fnTyStr`'s returns text. -/
def retsL (rs : List (List Char)) : List Char :=
  if rs = [] then [] else "returns(".data ++ (sepJoin [','] rs ++ [')'])

/-- `fnTyStr` on character lists. -/
def spellL (ps rs : List (List Char)) (ext : Bool) : List Char :=
  "function(".data ++ (sepJoin [','] ps ++ ')' :: (visL ext ++ retsL rs))

theorem fnTyStr_data (ps rs : List String) (ext : Bool) :
    (fnTyStr ps rs ext).data = spellL (ps.map String.data) (rs.map String.data) ext := by
  cases ext <;> cases rs <;>
    simp [fnTyStr, spellL, visL, retsL, Str.data_intercalate, toString]

/-- Every `fnTyStr` spelling is a function-type marker, whatever its components. -/
theorem fnTy?_fnTyStr (ps rs : List String) (ext : Bool) : fnTy? (fnTyStr ps rs ext) = true := by
  have e : fnTyStr ps rs ext = ⟨(fnTyStr ps rs ext).data⟩ := rfl
  rw [e, fnTy?_mk, fnTyStr_data]
  exact decide_eq_true (List.take_left' rfl)

/-! ## Conditions on a component -/

/-- A component `splitTopCommas` gives back from a comma-joined list: not
empty, no comma at depth `0`, no `}` `)` `]` at depth `0`, depth `0` at its
end (depth counted over all three bracket kinds, kinds not matched). -/
def SplitOk (s : String) : Prop := s.data ≠ [] ∧ splitScan 0 s.data = some 0

/-- A component the parameter list's closing `)` is found behind: no `)` or
`]` at depth `0`, depth `0` at its end (depth counted over `(` `[` / `)` `]`). -/
def CloseOk (s : String) : Prop := closeScan 0 s.data = some 0

/-- A component good in both positions. -/
def Well (s : String) : Prop := SplitOk s ∧ CloseOk s

instance (s : String) : Decidable (SplitOk s) := by unfold SplitOk; infer_instance
instance (s : String) : Decidable (CloseOk s) := by unfold CloseOk; infer_instance
instance (s : String) : Decidable (Well s) := by unfold Well; infer_instance

theorem sepJoin_ne_nil {a : List Char} (cs : List (List Char)) (h : a ≠ []) :
    sepJoin [','] (a :: cs) ≠ [] := by
  cases cs <;> simp [sepJoin, h]

/-- `splitTopCommas` of a comma-joined list of `SplitOk` components is that list. -/
theorem splitL_join {cs : List String} (h : ∀ c ∈ cs, SplitOk c) :
    splitL (sepJoin [','] (cs.map String.data)) = cs := by
  cases cs with
  | nil => rfl
  | cons a cs =>
    have ne := sepJoin_ne_nil (cs.map String.data) (h a (by simp)).1
    have sp := splitTop_join (cs := (a :: cs).map String.data)
      (by intro c hc; obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hc; exact (h x hx).2) (by simp)
    rw [List.map_cons] at sp
    simp only [splitL, List.map_cons, if_neg ne, sp]
    simp [Function.comp_def]

theorem splitTopCommas_intercalate {cs : List String} (h : ∀ c ∈ cs, SplitOk c) :
    splitTopCommas (",".intercalate cs) = cs := by
  have e : ",".intercalate cs = ⟨sepJoin [','] (cs.map String.data)⟩ :=
    String.ext (Str.data_intercalate "," cs)
  rw [e, splitTopCommas_mk, splitL_join h]

theorem returnsL_rets {rs : List String} (h : ∀ r ∈ rs, SplitOk r) :
    returnsL (retsL (rs.map String.data)) = some rs := by
  cases rs with
  | nil => rfl
  | cons a rs =>
    have j := splitL_join h
    generalize hJ : sepJoin [','] ((a :: rs).map String.data) = J at j
    have e : retsL ((a :: rs).map String.data) = "returns(".data ++ (J ++ [')']) := by
      subst hJ; simp [retsL]
    have ne : "returns(".data ++ (J ++ [')']) ≠ [] := by simp
    have t : ("returns(".data ++ (J ++ [')'])).take 8 = "returns(".data := List.take_left' rfl
    have d : ("returns(".data ++ (J ++ [')'])).drop 8 = J ++ [')'] := List.drop_left' rfl
    have l : ("returns(".data ++ (J ++ [')'])).drop
        (("returns(".data ++ (J ++ [')'])).length - 1) = [')'] := by
      rw [← List.append_assoc]; exact List.drop_left' (by simp)
    have k : (J ++ [')']).take ((J ++ [')']).length - 1) = J := List.take_left' (by simp)
    rw [e, returnsL, if_neg ne, if_pos ⟨t, l⟩, d, k, j]

/-! ## The round trip -/

/-- On character lists: behind `closeScan`-accepted parameters, `partsL`
reads the spelling back. -/
theorem partsL_spellL {ps rs : List String} (ext : Bool)
    (hp : ∀ p ∈ ps, Well p) (hr : ∀ r ∈ rs, SplitOk r) :
    partsL (spellL (ps.map String.data) (rs.map String.data) ext) = some (ps, rs, ext) := by
  have cl : closeScan 0 (sepJoin [','] (ps.map String.data)) = some 0 :=
    closeScan_join (by intro c hc; obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hc; exact (hp x hx).2) 0
  have t : (spellL (ps.map String.data) (rs.map String.data) ext).take 9 = "function(".data :=
    List.take_left' rfl
  have d : (spellL (ps.map String.data) (rs.map String.data) ext).drop 9
      = sepJoin [','] (ps.map String.data)
        ++ ')' :: (visL ext ++ retsL (rs.map String.data)) := List.drop_left' rfl
  have sp := splitL_join (fun p hp' => (hp p hp').1)
  have rt := returnsL_rets hr
  rw [partsL, if_pos t, d, close_join _ cl]
  cases ext with
  | true =>
    have e : (visL true ++ retsL (rs.map String.data)).take 8 = "external".data :=
      List.take_left' rfl
    have e' : (visL true ++ retsL (rs.map String.data)).drop 8 = retsL (rs.map String.data) :=
      List.drop_left' rfl
    simp only [Option.bind_some, e, if_true, e', rt, sp, Option.map_some, decide_true]
  | false =>
    have e : ¬ ((visL false ++ retsL (rs.map String.data)).take 8 = "external".data) := by
      cases rs with
      | nil => decide
      | cons a rs =>
        intro h
        have : ((visL false ++ retsL ((a :: rs).map String.data)).take 8).head? = some 'r' := by
          simp [visL, retsL]
        rw [h] at this
        exact absurd this (by decide)
    simp only [Option.bind_some, e, if_false, decide_false]
    simp only [visL, Bool.false_eq_true, if_false, List.nil_append, rt, sp, Option.map_some]

/-- **The round trip.** `fnParts?` reads a `fnTyStr` spelling back as its
parameters, returns and visibility flag, when every parameter is `Well` and
every return is `SplitOk`. Both visibilities, empty and nonempty lists. -/
theorem fnParts?_fnTyStr {ps rs : List String} (ext : Bool)
    (hp : ∀ p ∈ ps, Well p) (hr : ∀ r ∈ rs, SplitOk r) :
    fnParts? (fnTyStr ps rs ext) = some (ps, rs, ext) := by
  have e : fnTyStr ps rs ext = ⟨(fnTyStr ps rs ext).data⟩ := rfl
  rw [e, fnParts?_mk, fnTyStr_data, partsL_spellL ext hp hr]

/-- On the covered components the spelling determines the signature. -/
theorem fnTyStr_inj {ps rs ps' rs' : List String} {ext ext' : Bool}
    (hp : ∀ p ∈ ps, Well p) (hr : ∀ r ∈ rs, SplitOk r)
    (hp' : ∀ p ∈ ps', Well p) (hr' : ∀ r ∈ rs', SplitOk r)
    (h : fnTyStr ps rs ext = fnTyStr ps' rs' ext') : ps = ps' ∧ rs = rs' ∧ ext = ext' := by
  have a := fnParts?_fnTyStr ext hp hr
  rw [h, fnParts?_fnTyStr ext' hp' hr'] at a
  cases a
  exact ⟨rfl, rfl, rfl⟩

/-! ## Which spellings are covered -/

theorem splitScan_spellL {ps rs : List (List Char)} (ext : Bool)
    (hp : ∀ c ∈ ps, splitScan 0 c = some 0) (hr : ∀ c ∈ rs, splitScan 0 c = some 0) :
    splitScan 0 (spellL ps rs ext) = some 0 := by
  have v : splitScan 0 (visL ext) = some 0 := by cases ext <;> decide
  have r : splitScan 0 (retsL rs) = some 0 := by
    unfold retsL
    split
    · rfl
    · rw [splitScan_append _ (show splitScan 0 "returns(".data = some 1 by decide),
        splitScan_append _ (splitScan_join hr 0)]
      decide
  have c : ∀ t, splitScan 1 (')' :: t) = splitScan 0 t := fun t => by simp [splitScan, sdepth]
  unfold spellL
  rw [splitScan_append _ (show splitScan 0 "function(".data = some 1 by decide),
    splitScan_append _ (splitScan_join hp 0), c, splitScan_append _ v, r]

theorem closeScan_spellL {ps rs : List (List Char)} (ext : Bool)
    (hp : ∀ c ∈ ps, closeScan 0 c = some 0) (hr : ∀ c ∈ rs, closeScan 0 c = some 0) :
    closeScan 0 (spellL ps rs ext) = some 0 := by
  have v : closeScan 0 (visL ext) = some 0 := by cases ext <;> decide
  have r : closeScan 0 (retsL rs) = some 0 := by
    unfold retsL
    split
    · rfl
    · rw [closeScan_append _ (show closeScan 0 "returns(".data = some 1 by decide),
        closeScan_append _ (closeScan_join hr 1)]
      decide
  have c : ∀ t, closeScan 1 (')' :: t) = closeScan 0 t := fun t => by simp [closeScan, cdepth]
  unfold spellL
  rw [closeScan_append _ (show closeScan 0 "function(".data = some 1 by decide),
    closeScan_append _ (closeScan_join hp 1), c, closeScan_append _ v, r]

/-- A spelling of `Well` components is a `Well` component: nesting to any depth. -/
theorem well_fnTyStr {ps rs : List String} (ext : Bool)
    (hp : ∀ p ∈ ps, Well p) (hr : ∀ r ∈ rs, Well r) : Well (fnTyStr ps rs ext) := by
  have mem : ∀ {cs : List String} {c : List Char}, c ∈ cs.map String.data → ∃ x ∈ cs, x.data = c :=
    fun h => List.mem_map.1 h
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [fnTyStr_data]; simp [spellL]
  · rw [fnTyStr_data]
    exact splitScan_spellL ext
      (fun c hc => by obtain ⟨x, hx, rfl⟩ := mem hc; exact (hp x hx).1.2)
      (fun c hc => by obtain ⟨x, hx, rfl⟩ := mem hc; exact (hr x hx).1.2)
  · show closeScan 0 (fnTyStr ps rs ext).data = some 0
    rw [fnTyStr_data]
    exact closeScan_spellL ext
      (fun c hc => by obtain ⟨x, hx, rfl⟩ := mem hc; exact (hp x hx).2)
      (fun c hc => by obtain ⟨x, hx, rfl⟩ := mem hc; exact (hr x hx).2)

/-- A nonempty name without bracket or comma. -/
theorem well_plain {s : String} (ne : s.data ≠ []) (h : plain s.data = true) : Well s :=
  ⟨⟨ne, splitScan_plain h 0⟩, closeScan_plain h 0⟩

/-- Text both scans accept may follow a `Well` component. -/
theorem Well.append {s t : String} (h : Well s) (st : splitScan 0 t.data = some 0)
    (ct : closeScan 0 t.data = some 0) : Well (s ++ t) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · have := h.1.1; simp [this]
  · rw [String.data_append, splitScan_append _ h.1.2, st]
  · show closeScan 0 (s ++ t).data = some 0
    rw [String.data_append, closeScan_append _ h.2, ct]

/-- An array suffix `[n]` (`n` plain, possibly empty). -/
theorem Well.index {s n : String} (h : Well s) (hn : plain n.data = true) :
    Well (s ++ "[" ++ n ++ "]") := by
  rw [String.append_assoc, String.append_assoc]
  have d : ("[" ++ (n ++ "]")).data = '[' :: (n.data ++ [']']) := rfl
  refine h.append ?_ ?_
  · rw [d]
    show splitScan 1 (n.data ++ [']']) = some 0
    rw [splitScan_append _ (splitScan_plain hn 1)]; rfl
  · rw [d]
    show closeScan 1 (n.data ++ [']']) = some 0
    rw [closeScan_append _ (closeScan_plain hn 1)]; rfl

/-- The component spellings the laws are stated for, as a grammar: plain
names, function types of covered components (any nesting), and a covered
component followed by plain text (a location) or an array suffix. Other
`Well` components (decidable on a concrete spelling) are not `Covered` but
satisfy `fnParts?_fnTyStr` all the same. -/
inductive Covered : String → Prop
  | name {s : String} : s.data ≠ [] → plain s.data = true → Covered s
  | fn {ps rs : List String} (ext : Bool) :
      (∀ p ∈ ps, Covered p) → (∀ r ∈ rs, Covered r) → Covered (fnTyStr ps rs ext)
  | suffix {s t : String} : Covered s → plain t.data = true → Covered (s ++ t)
  | index {s n : String} : Covered s → plain n.data = true → Covered (s ++ "[" ++ n ++ "]")

theorem Covered.well {s : String} (h : Covered s) : Well s := by
  induction h with
  | name ne p => exact well_plain ne p
  | fn ext _ _ ihp ihr => exact well_fnTyStr ext ihp ihr
  | suffix _ p ih => exact ih.append (splitScan_plain p 0) (closeScan_plain p 0)
  | index _ p ih => exact ih.index p

/-- The round trip on the grammar: a function type of covered components
reads back. A returned component that is itself `fnTyStr` of covered
components reads back by this law again; one continued by a suffix is
returned as a string and is no function-type spelling. -/
theorem fnParts?_covered {ps rs : List String} (ext : Bool)
    (hp : ∀ p ∈ ps, Covered p) (hr : ∀ r ∈ rs, Covered r) :
    fnParts? (fnTyStr ps rs ext) = some (ps, rs, ext) :=
  fnParts?_fnTyStr ext (fun p h => (hp p h).well) (fun r h => (hr r h).well.1)

end Solidity.Correctness.Lowering.Total.FunctionTypeParserLaws
