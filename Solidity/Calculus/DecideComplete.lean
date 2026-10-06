import Solidity.Calculus.DecideSyn

/-!
# The reads are realizable: `sol_decide` decides

`Fml.valid_iff_reduce` (`Decide.lean`) leaves `∀ σ, ψ.holds σ`, where `ψ`
reads the starting storage at finitely many paths, and a statement about
`σ`'s storage is not something `omega` or `grind` can decide: two reads are
unrelated atoms to them, while in a storage they are not.  This module is
mini-solkey's realizability (`Ch15_Decide`, `LFml.valid_iff`) for a storage
of shapes: the reads become free, under the constraints a storage puts on
them, and nothing is lost.

* **What a read sees** (`Obs`): nothing, a word, a struct, an array with its
  live length and whether it is fixed-size, a mapping.  `find`, `has`, the
  shape tests and `length` read nothing more (`obsOf`).
* **The constraint** (`ChildOk`) between a location and one a segment
  below: a struct may have any member; a dynamic array has its length at
  `length` and its elements exactly at the indices below it; a fixed-size
  array the same with no `length`; a mapping has every key; a word, and
  nothing, have nothing below.  Every storage meets it
  (`childOk_findLive`).
* **Realizability** (`realize_findLive`): any choice of what finitely many
  paths show, closed under prefixes and meeting `ChildOk` at every step, is
  what some storage shows (`realize`, built level by level).  The
  constraints are local — each read path against the one above it — because
  the read paths include every prefix (`LTerm.reads`).
* **Completeness** (`LFml.valid_iff_cons`, `Fml.valid_iff_cons`): for a
  reduction that reads the starting storage only, and no value of the
  transaction (`LFml.initOnly`; `msg.sender` is decided by `LFml.syn` or the
  heuristic finish),
  `∀ σ, ψ.holds σ` is exactly `ψ` over free reads `o` under the
  constraints of its read paths (`consAll`).
* **`sol_decide`** rewrites by both equivalences, splits on the locals and
  on the shape of every location with a read below it, and closes what is
  left by `omega` or `grind`.

**What is decided.**  After the splits the goal is quantifier-free up to the
values the reads return: equalities between reads and the shapes and words
they show, integer arithmetic over keys, indices and lengths, and the
operators of the program.  `sol_decide` closes a valid goal exactly when
`omega` or `grind` closes that statement; neither is proved complete for it
(`grind` instantiates the quantifiers over values, and a product of two
variables is outside linear arithmetic).

**The fragment covered** is `Fml.inL`'s, all of it but a write or `delete`
through a member named `length` (`LStor.okE` keeps such a write whole, so
the reduction reads a written storage there and `initOnly` fails), and the
two reads the elimination keeps whole: the slot a `push()` of a struct or
an array recycles, and a read below a key of a copy (`Decide.lean`); for
those `sol_decide` falls back to `sol_decide_heuristic`.  Fixed-size arrays,
mappings, `delete` below a key, `values.length` (`Term.len`) are covered.
-/

namespace Solidity

namespace Decide

open Semantics SemanticsProperties

/-! ## What a formula sees of a location -/

/-- What the reduced formula can see of the storage at one path: nothing
there, a word, or a node of one of the four shapes, an array with its live
length. -/
inductive Obs where
  | absent
  | word (v : Value)
  | struct
  | arr (n : Nat) (fixed : Bool)
  | map
  deriving DecidableEq, Repr, Inhabited

/-- What a read of the storage shows. -/
def obsOf : Res SVal → Obs
  | .ok (.prim p) => .word p
  | .ok (.struct _) => .struct
  | .ok (.array es _ fx) => .arr es.length fx
  | .ok (.map _ _) => .map
  | .error _ => .absent

/-- **The constraint between a location and one below it**, `p` at the
parent, `c` at the child one segment `s` further down: a struct may have any
member; a dynamic array has its length at `length` and its elements exactly
at the indices below it; a mapping has every key; nothing else has anything
below it. -/
def ChildOk : Obs → Seg → Obs → Prop
  | .struct, .field _, _ => True
  | .arr n fx, .field f, c => if fx = false ∧ f = "length" then c = .word (.int n) else c = .absent
  | .arr n _, .at i, c => if 0 ≤ i ∧ i < n then c ≠ .absent else c = .absent
  | .map, .at _, c => c ≠ .absent
  | .absent, _, c | .word _, _, c | .struct, .at _, c | .map, .field _, c => c = .absent

/-- **Every storage meets the constraint**: `alice.account` and
`alice.account.balance` as read in any tree. -/
theorem childOk_findLive (T : SVal) (P : List Seg) (s : Seg) :
    ChildOk (obsOf (T.findLive P)) s (obsOf (T.findLive (P ++ [s]))) := by
  rw [SVal.findLive_append]
  rcases T.findLive P with e | v
  · cases s <;> simp [ChildOk, obsOf, bind, Except.bind]
  · simp only [Res.ok_bind]
    cases v with
    | prim p => cases s <;> simp [ChildOk, obsOf, SVal.findLive]
    | struct fs =>
      cases s with
      | field f =>
        simp [ChildOk, obsOf]
      | «at» i => simp [ChildOk, obsOf, SVal.findLive]
    | array es sh fx =>
      cases s with
      | field f =>
        by_cases hf : f = "length"
        · subst hf; cases fx <;> simp [ChildOk, obsOf, SVal.findLive]
        · simp [ChildOk, obsOf, SVal.findLive, hf]
      | «at» i =>
        simp only [ChildOk, obsOf, SVal.findLive]
        by_cases h : 0 ≤ i ∧ i.toNat < es.length
        · rw [dif_pos h, if_pos ⟨h.1, by omega⟩]
          cases (es.get ⟨i.toNat, h.2⟩) <;> simp
        · rw [dif_neg h, if_neg (by omega)]
    | map es d =>
      cases s with
      | field f => simp [ChildOk, obsOf, SVal.findLive]
      | «at» i =>
        cases h : lookupBy i es with
        | none => cases d <;> simp [ChildOk, obsOf, SVal.findLive, h]
        | some v => cases v <;> simp [ChildOk, obsOf, SVal.findLive, h]

/-! ## Realizing the reads

Given what each of finitely many paths should show, `build` makes a tree
that shows it: a node of the shape asked for, with the members and entries
the paths below it name, an array's elements at every live index.  It works
when the paths are closed under prefixes and every step down meets
`ChildOk` (`build_findLive`). -/

/-- The members `P` has among the paths `Ks`, those that show something. -/
def fieldKids (o : List Seg → Obs) (Ks : List (List Seg)) (P : List Seg) : List Name :=
  Ks.filterMap fun K => match K.getLast? with
    | some (.field f) => if K.dropLast = P ∧ o K ≠ .absent then some f else none
    | _ => none

/-- The keys `P` has among the paths `Ks`. -/
def keyKids (Ks : List (List Seg)) (P : List Seg) : List Int :=
  Ks.filterMap fun K => match K.getLast? with
    | some (.at i) => if K.dropLast = P then some i else none
    | _ => none

/-- A tree showing `o` at the paths `Ks`, from `P` down, `d` levels deep. -/
def build (o : List Seg → Obs) (Ks : List (List Seg)) : Nat → List Seg → SVal
  | 0, _ => .prim (.int 0)
  | d + 1, P =>
    match o P with
    | .absent => .prim (.int 0)
    | .word v => .prim v
    | .struct => .struct ((fieldKids o Ks P).map fun f => (f, build o Ks d (P ++ [.field f])))
    | .arr n fx => .array ((List.range n).map fun i => build o Ks d (P ++ [.at (i : Int)])) [] fx
    | .map => .map ((keyKids Ks P).map fun i => (i, build o Ks d (P ++ [.at i]))) (.prim (.int 0))

theorem mem_fieldKids {o : List Seg → Obs} {Ks : List (List Seg)} {P : List Seg} {f : Name} :
    f ∈ fieldKids o Ks P ↔ P ++ [.field f] ∈ Ks ∧ o (P ++ [.field f]) ≠ .absent := by
  simp only [fieldKids, List.mem_filterMap]
  constructor
  · rintro ⟨K, hK, h⟩
    split at h
    · rename_i g hg
      split at h
      · rename_i hc
        cases h
        obtain ⟨ys, rfl⟩ := List.getLast?_eq_some_iff.1 hg
        simp only [List.dropLast_concat] at hc
        obtain ⟨rfl, h2⟩ := hc
        exact ⟨hK, h2⟩
      · cases h
    · cases h
  · rintro ⟨hK, ho⟩
    exact ⟨_, hK, by simp [ho]⟩

theorem mem_keyKids {Ks : List (List Seg)} {P : List Seg} {i : Int}
    (h : P ++ [.at i] ∈ Ks) : i ∈ keyKids Ks P := by
  simp only [keyKids, List.mem_filterMap]
  exact ⟨_, h, by simp⟩

/-- Looking a key up in a list built from its keys. -/
theorem lookupBy_map_self {κ α : Type} [DecidableEq κ] (F : κ → α) (k : κ) :
    ∀ l : List κ, lookupBy k (l.map fun x => (x, F x)) = if k ∈ l then some (F k) else none
  | [] => by simp [lookupBy]
  | x :: l => by
    simp only [List.map_cons, lookupBy, List.mem_cons, lookupBy_map_self F k l]
    by_cases h : k = x
    · subst h; simp
    · simp [h]

/-- The paths are closed under prefixes, the root aside. -/
def PrefixClosed (Ks : List (List Seg)) : Prop :=
  ∀ K ∈ Ks, ∀ P s, K = P ++ [s] → P = [] ∨ P ∈ Ks

theorem PrefixClosed.mem {Ks : List (List Seg)} (hc : PrefixClosed Ks) :
    ∀ (t : List Seg) (P : List Seg), P ++ t ∈ Ks → P = [] ∨ P ∈ Ks
  | [], P, h => .inr (by simpa using h)
  | s :: t, P, h => by
    rcases PrefixClosed.mem hc t (P ++ [s]) (by simpa using h) with h' | h'
    · simp at h'
    · exact hc _ h' P s rfl

/-- Below a location that shows nothing, or a word, the paths show nothing. -/
theorem absent_below {o : List Seg → Obs} {Ks : List (List Seg)} (hc : PrefixClosed Ks)
    (hok : ∀ K ∈ Ks, ∀ P s, K = P ++ [s] → ChildOk (o P) s (o K)) :
    ∀ (t : List Seg) {P : List Seg}, (o P = .absent ∨ ∃ v, o P = .word v) →
      t ≠ [] → P ++ t ∈ Ks → o (P ++ t) = .absent
  | [], _, _, h, _ => absurd rfl h
  | s :: t, P, hP, _, hK => by
    have hm : P ++ [s] ∈ Ks := by
      rcases hc.mem t (P ++ [s]) (by simpa using hK) with h | h
      · simp at h
      · exact h
    have hk := hok _ hm P s rfl
    have hs : o (P ++ [s]) = .absent := by
      rcases hP with hP | ⟨v, hP⟩ <;> rw [hP] at hk <;> cases s <;> exact hk
    by_cases ht : t = []
    · subst ht; exact hs
    · have := absent_below hc hok t (P := P ++ [s]) (.inl hs) ht (by simpa using hK)
      simpa using this

/-- **`build` shows what it was asked to**: at every path of `Ks` below a
location that shows something, the tree built from there shows `o`. -/
theorem build_findLive {o : List Seg → Obs} {Ks : List (List Seg)} (hc : PrefixClosed Ks)
    (hok : ∀ K ∈ Ks, ∀ P s, K = P ++ [s] → ChildOk (o P) s (o K)) :
    ∀ (rest : List Seg) (d : Nat) (P : List Seg), rest.length < d → o P ≠ .absent →
      (rest ≠ [] → P ++ rest ∈ Ks) → obsOf ((build o Ks d P).findLive rest) = o (P ++ rest)
  | [], 0, _, hd, _, _ => absurd hd (by simp)
  | _ :: _, 0, _, hd, _, _ => absurd hd (by simp)
  | [], d + 1, P, _, hP, _ => by
    simp only [List.append_nil, SVal.findLive_nil, build]
    split <;> simp_all [obsOf]
  | s :: rest, d + 1, P, hd, hP, hK => by
    have hK := hK (by simp)
    have hm : P ++ [s] ∈ Ks :=
      (hc.mem rest (P ++ [s]) (by simpa using hK)).resolve_left (by simp)
    have hk := hok _ hm P s rfl
    have hbelow : o (P ++ [s]) = .absent → ∀ e, obsOf (.error e) = o (P ++ s :: rest) := by
      intro h e
      by_cases hr : rest = []
      · subst hr; simp [obsOf, h]
      · have := absent_below hc hok rest (P := P ++ [s]) (.inl h) hr (by simpa using hK)
        simp only [List.append_assoc, List.singleton_append] at this
        simp [obsOf, this]
    have ih : ∀ P', P' = P ++ [s] → o P' ≠ .absent →
        obsOf ((build o Ks d P').findLive rest) = o (P ++ s :: rest) := by
      rintro P' rfl hP'
      have := build_findLive hc hok rest d (P ++ [s]) (by simp at hd; omega) hP'
        (fun _ => by simpa using hK)
      simpa using this
    simp only [build]
    split
    · exact absurd ‹_› hP
    · rename_i v hv
      rw [hv] at hk
      cases s <;> exact hbelow hk _
    · rename_i hv
      rw [hv] at hk
      cases s with
      | field f =>
        simp only [SVal.findLive, lookupBy_map_self]
        by_cases hf : f ∈ fieldKids o Ks P
        · simp only [if_pos hf]
          exact ih _ rfl (mem_fieldKids.1 hf).2
        · simp only [if_neg hf]
          have : o (P ++ [.field f]) = .absent :=
            Classical.byContradiction fun h => hf (mem_fieldKids.2 ⟨hm, h⟩)
          exact hbelow this _
      | «at» i => exact hbelow hk _
    · rename_i n fx hv
      rw [hv] at hk
      cases s with
      | field f =>
        by_cases hl : fx = false ∧ f = "length"
        · obtain ⟨rfl, rfl⟩ := hl
          simp only [ChildOk, and_self, if_true] at hk
          simp only [SVal.findLive, List.length_map, List.length_range]
          cases rest with
          | nil => simp [obsOf, hk]
          | cons s' rest' =>
            have := absent_below hc hok (s' :: rest') (P := P ++ [.field "length"])
              (.inr ⟨_, hk⟩) (by simp) (by simpa using hK)
            simp only [List.append_assoc, List.singleton_append] at this
            simp [SVal.findLive, obsOf, this]
        · simp only [ChildOk, hl, if_false] at hk
          have : (SVal.array ((List.range n).map fun i => build o Ks d (P ++ [.at (i : Int)])) []
              fx).findLive (.field f :: rest) = .error .stuck := by
            by_cases hf : f = "length"
            · subst hf
              have : fx = true := by cases fx <;> simp_all
              subst this; rfl
            · simp [SVal.findLive]
          rw [this]; exact hbelow hk _
      | «at» i =>
        simp only [ChildOk] at hk
        simp only [SVal.findLive, List.length_map, List.length_range]
        split
        · rename_i hb
          rw [if_pos ⟨hb.1, by omega⟩] at hk
          simp only [List.get_eq_getElem, List.getElem_map, List.getElem_range,
            Int.toNat_of_nonneg hb.1]
          exact ih _ rfl hk
        · rename_i hb
          rw [if_neg (by omega)] at hk
          exact hbelow hk _
    · rename_i hv
      rw [hv] at hk
      cases s with
      | field f => exact hbelow hk _
      | «at» i =>
        simp only [SVal.findLive, lookupBy_map_self, if_pos (mem_keyKids hm)]
        exact ih _ rfl hk

/-- The deepest path of `Ks`, and one more. -/
def depth (Ks : List (List Seg)) : Nat := Ks.foldr (fun K m => max K.length m) 0 + 1

theorem length_lt_depth : ∀ (Ks : List (List Seg)), ∀ K ∈ Ks, K.length < depth Ks
  | [] => by simp
  | K :: Ks => by
    intro K' h
    have ih := length_lt_depth Ks
    simp only [depth, List.foldr_cons, List.mem_cons] at h ih ⊢
    rcases h with rfl | h
    · omega
    · have := ih K' h; omega

/-- The shape a choice of what each path shows gives the root: the storage
is a struct of its roots. -/
def atRoot (o : List Seg → Obs) (P : List Seg) : Obs := if P = [] then .struct else o P

/-- The storage showing `o` at the paths `Ks`. -/
def realize (o : List Seg → Obs) (Ks : List (List Seg)) : SVal :=
  build (atRoot o) Ks (depth Ks) []

/-- **Realizability**: any choice of what the finitely many paths `Ks` show,
closed under prefixes and meeting `ChildOk` at every step below a root, is
what some storage shows.  Example: `balances` a mapping, `balances[3]` the
word `7`, `values` a dynamic array of length `4`, `values.length` the word
`4` and `values[2]` a word: `realize` builds that storage. -/
theorem realize_findLive {o : List Seg → Obs} {Ks : List (List Seg)} (hc : PrefixClosed Ks)
    (hok : ∀ K ∈ Ks, ∀ P s, K = P ++ [s] → P ≠ [] → ChildOk (o P) s (o K))
    (hroot : ∀ K ∈ Ks, ∃ r t, K = .field r :: t) :
    ∀ K ∈ Ks, obsOf ((realize o Ks).findLive K) = o K := by
  intro K hK
  have hne : ∀ K ∈ Ks, K ≠ [] := fun K hK => by
    obtain ⟨r, t, rfl⟩ := hroot K hK; simp
  have hok' : ∀ K ∈ Ks, ∀ P s, K = P ++ [s] → ChildOk (atRoot o P) s (atRoot o K) := by
    intro K hK P s he
    have hK0 := hne K hK
    by_cases hP : P = []
    · subst hP; subst he
      cases s with
      | field f => simp [atRoot, ChildOk]
      | «at» i => obtain ⟨r, t, h⟩ := hroot _ hK; simp at h
    · have := hok K hK P s he hP
      simp only [atRoot, if_neg hP, if_neg hK0]
      exact this
  have := build_findLive hc hok' K _ [] (length_lt_depth Ks K hK) (by simp [atRoot])
    (fun _ => by simpa using hK)
  simpa [atRoot, hne K hK] using this

/-! ## The reduced formula over free reads

A reduced formula reads the initial storage at finitely many paths, and
only through what `Obs` keeps.  `LTerm.evalA` evaluates it with the locals of
`E` and the reads chosen by `o`, any function at all; at the storage of a
state it is `LTerm.eval` (`LTerm.evalA_sim`). -/

/-- The word a location shows. -/
def Obs.find : Obs → Res Value
  | .word v => .ok v
  | _ => .error .stuck

/-- Whether a location is there. -/
def Obs.has : Obs → Res Value
  | .absent => .error .stuck
  | _ => .ok (.bool true)

/-- The length of an array. -/
def Obs.len : Obs → Res Value
  | .arr n _ => .ok (.int n)
  | _ => .error .stuck

/-- Whether a location is a mapping (a fixed-size array). -/
def Obs.test : KShape → Obs → Res Value
  | .map, .map => .ok (.bool true)
  | .fixed, .arr _ true => .ok (.bool true)
  | _, _ => .error .stuck

mutual

/-- A term over the locals `E` and the reads `o`.  A storage other than the
initial one halts: a reduced formula has none but where a write goes
through a member named `length` (`LTerm.initOnly`). -/
def LTerm.evalA (E : Var → Res Value) (o : List Seg → Obs) : LTerm → Res Value
  | .lit v => .ok v
  | .var x => E x
  | .binop op p a b => a.evalA E o >>= fun x => evalBinop op p x (b.evalA E o)
  | .unop op p a => a.evalA E o >>= fun x => applyUnOp op x >>= unopCheck op p
  | .ite c a b => c.evalA E o >>= fun cv => pickBranch cv (a.evalA E o) (b.evalA E o)
  | .find .init q => q.evalA E o >>= fun qs => (o qs).find
  | .has .init q => q.evalA E o >>= fun qs => (o qs).has
  | .kmap sh .init q => q.evalA E o >>= fun qs => (o qs).test sh
  | .len .init q => q.evalA E o >>= fun qs => (o qs).len
  | .sok .init => .ok (.bool true)
  | .pok q => q.evalA E o >>= fun _ => .ok (.bool true)
  | .seq d a => d.evalA E o >>= fun _ => a.evalA E o
  | .orElse a b => orElseR (a.evalA E o) (b.evalA E o)
  | .kite a b t e =>
    (a.evalA E o >>= Value.asInt) >>= fun i => (b.evalA E o >>= Value.asInt) >>= fun j =>
      if i = j then t.evalA E o else e.evalA E o
  | .zero a => a.evalA E o >>= fun v => .ok (zeroV v)
  | .err | .env _ | .findP _ _ | .find _ _ | .has _ _ | .kmap _ _ _ | .len _ _ | .sok _
  | .cpok _ _ => .error .stuck

/-- A path over the locals `E` and the reads `o`. -/
def LPath.evalA (E : Var → Res Value) (o : List Seg → Obs) : LPath → Res (List Seg)
  | .root r => .ok [.field r]
  | .field q f => q.evalA E o >>= fun qs => .ok (qs ++ [.field f])
  | .at q k => q.evalA E o >>= fun qs => k.evalA E o >>= Value.asInt >>= fun i => .ok (qs ++ [.at i])

end

/-- A formula over the locals `E` and the reads `o`. -/
def LFml.holdsA (E : Var → Res Value) (o : List Seg → Obs) : LFml → Prop
  | .tt => True
  | .eq a b =>
    match a.evalA E o, b.evalA E o with
    | .ok x, .ok y => x = y
    | _, _ => False
  | .not φ => ¬ φ.holdsA E o
  | .and φ ψ => φ.holdsA E o ∧ ψ.holdsA E o
  | .imp φ ψ => φ.holdsA E o → ψ.holdsA E o
  -- outside `initOnly`: the free reads do not decide a quantifier
  | .all .. => True

mutual

/-- The term reads the initial storage only. -/
def LTerm.initOnly : LTerm → Bool
  | .lit _ | .var _ | .err | .sok .init => true
  | .find .init q | .has .init q | .kmap _ .init q | .len .init q | .pok q => q.initOnly
  | .find _ _ | .has _ _ | .kmap _ _ _ | .len _ _ | .sok _ | .env _ | .findP _ _ | .cpok _ _ => false
  | .binop _ _ a b | .seq a b | .orElse a b => a.initOnly && b.initOnly
  | .unop _ _ a | .zero a => a.initOnly
  | .ite c a b => c.initOnly && a.initOnly && b.initOnly
  | .kite a b t e => a.initOnly && b.initOnly && t.initOnly && e.initOnly

/-- The path's keys read the initial storage only. -/
def LPath.initOnly : LPath → Bool
  | .root _ => true
  | .field q _ => q.initOnly
  | .at q k => q.initOnly && k.initOnly

end

/-- The formula reads the initial storage only. -/
def LFml.initOnly : LFml → Bool
  | .tt => true
  | .eq a b => a.initOnly && b.initOnly
  | .not φ => φ.initOnly
  | .and φ ψ | .imp φ ψ => φ.initOnly && ψ.initOnly
  | .all .. => false

/-- The locals of a state, as values. -/
def envOf (σ : State) : Var → Res Value := fun x => σ.getEnv x >>= Close.bindingVal

/-- What the storage of a state shows at each path. -/
def obsAt (σ : State) : List Seg → Obs := fun qs => obsOf ((SVal.struct σ.storage).findLive qs)

theorem find_sim (r : Res SVal) : Sim ((obsOf r).find) (r >>= SVal.asValue) := by
  intro a
  rcases r with e | (p | fs | ⟨es, sh, fx⟩ | ⟨es, d⟩)
  · simp [obsOf, Obs.find, bind, Except.bind]
  · cases p <;> simp [obsOf, Obs.find, SVal.asValue, Res.ok_bind]
  all_goals simp [obsOf, Obs.find, SVal.asValue, Res.ok_bind]

theorem has_sim (r : Res SVal) : Sim ((obsOf r).has) (r >>= fun _ => .ok (.bool true)) := by
  intro a
  rcases r with e | (p | fs | ⟨es, sh, fx⟩ | ⟨es, d⟩) <;>
    simp [obsOf, Obs.has, bind, Except.bind]

theorem len_sim (r : Res SVal) : Sim ((obsOf r).len) (r >>= Close.arrLen) := by
  intro a
  rcases r with e | (p | fs | ⟨es, sh, fx⟩ | ⟨es, d⟩) <;>
    simp [obsOf, Obs.len, Close.arrLen, bind, Except.bind]

theorem test_sim (sh : KShape) (r : Res SVal) : Sim ((obsOf r).test sh) (r >>= sh.test) := by
  intro a
  rcases r with e | (p | fs | ⟨es, sh', fx⟩ | ⟨es, d⟩)
  · cases sh <;> simp [obsOf, Obs.test, bind, Except.bind]
  all_goals cases sh <;> try cases fx
  all_goals simp [obsOf, Obs.test, KShape.test, kmapF, isMapV, isFixV, Res.ok_bind]

mutual

/-- **Over the storage of a state, the free reads are the reads**:
`balances[k]` read through `o = obsAt σ` returns what it returns in `σ`. -/
theorem LTerm.evalA_sim (σ : State) :
    (t : LTerm) → t.initOnly = true → Sim (t.evalA (envOf σ) (obsAt σ)) (t.eval σ)
  | .lit _, _ => Sim.refl _
  | .var _, _ => Sim.refl _
  | .err, _ => Sim.refl _
  | .env _, h | .findP _ _, h | .cpok _ _, h => by
    simp only [LTerm.initOnly, Bool.false_eq_true] at h
  | .binop _ _ a b, h => by
    simp only [LTerm.initOnly, Bool.and_eq_true] at h
    exact Sim.bind (LTerm.evalA_sim σ a h.1) fun _ => evalBinop_sim (LTerm.evalA_sim σ b h.2)
  | .unop _ _ a, h => Sim.bind (LTerm.evalA_sim σ a h) fun _ => Sim.refl _
  | .ite c a b, h => by
    simp only [LTerm.initOnly, Bool.and_eq_true] at h
    exact Sim.bind (LTerm.evalA_sim σ c h.1.1) fun _ =>
      pickBranch_sim (LTerm.evalA_sim σ a h.1.2) (LTerm.evalA_sim σ b h.2)
  | .find .init q, h => Sim.bind (LPath.evalA_sim σ q h) fun _ => find_sim _
  | .has .init q, h => Sim.bind (LPath.evalA_sim σ q h) fun _ => has_sim _
  | .kmap sh .init q, h => Sim.bind (LPath.evalA_sim σ q h) fun _ => test_sim sh _
  | .len .init q, h => Sim.bind (LPath.evalA_sim σ q h) fun _ => len_sim _
  | .sok .init, _ => Sim.refl _
  | .pok q, h => Sim.bind (LPath.evalA_sim σ q h) fun _ => Sim.refl _
  | .seq d a, h => by
    simp only [LTerm.initOnly, Bool.and_eq_true] at h
    exact Sim.bind (LTerm.evalA_sim σ d h.1) fun _ => LTerm.evalA_sim σ a h.2
  | .orElse a b, h => by
    simp only [LTerm.initOnly, Bool.and_eq_true] at h
    exact Sim.orElse (LTerm.evalA_sim σ a h.1) (LTerm.evalA_sim σ b h.2)
  | .kite a b t e, h => by
    simp only [LTerm.initOnly, Bool.and_eq_true] at h
    exact Sim.bind (Sim.bind (LTerm.evalA_sim σ a h.1.1.1) fun _ => Sim.refl _) fun i =>
      Sim.bind (Sim.bind (LTerm.evalA_sim σ b h.1.1.2) fun _ => Sim.refl _) fun j => by
        by_cases hij : i = j
        · simp only [hij, if_true]; exact LTerm.evalA_sim σ t h.1.2
        · simp only [hij, if_false]; exact LTerm.evalA_sim σ e h.2
  | .zero a, h => Sim.bind (LTerm.evalA_sim σ a h) fun _ => Sim.refl _
  | .find (.save ..) _, h | .find (.del ..) _, h | .has (.save ..) _, h | .has (.del ..) _, h
  | .kmap _ (.save ..) _, h | .kmap _ (.del ..) _, h | .sok (.save ..), h | .sok (.del ..), h
  | .len (.save ..) _, h | .len (.del ..) _, h => by
    simp [LTerm.initOnly] at h

/-- The same for a path. -/
theorem LPath.evalA_sim (σ : State) :
    (q : LPath) → q.initOnly = true → Sim (q.evalA (envOf σ) (obsAt σ)) (q.eval σ)
  | .root _, _ => Sim.refl _
  | .field q _, h => Sim.bind (LPath.evalA_sim σ q h) fun _ => Sim.refl _
  | .at q k, h => by
    simp only [LPath.initOnly, Bool.and_eq_true] at h
    exact Sim.bind (LPath.evalA_sim σ q h.1) fun _ =>
      Sim.bind (Sim.bind (LTerm.evalA_sim σ k h.2) fun _ => Sim.refl _) fun _ => Sim.refl _

end

/-- A formula holds alike of runs that agree. -/
theorem LFml.holdsA_iff (σ : State) :
    (φ : LFml) → φ.initOnly = true → (φ.holdsA (envOf σ) (obsAt σ) ↔ φ.holds σ)
  | .tt, _ => Iff.rfl
  | .all .., h => by simp [LFml.initOnly] at h
  | .eq a b, h => by
    simp only [LFml.initOnly, Bool.and_eq_true] at h
    have ha := LTerm.evalA_sim σ a h.1
    have hb := LTerm.evalA_sim σ b h.2
    simp only [LFml.holdsA, LFml.holds]
    constructor
    · intro hh
      split at hh
      · rename_i x y hx hy
        rw [(ha x).1 hx, (hb y).1 hy]; exact hh
      · exact hh.elim
    · intro hh
      split at hh
      · rename_i x y hx hy
        rw [(ha x).2 hx, (hb y).2 hy]; exact hh
      · exact hh.elim
  | .not φ, h => not_congr (LFml.holdsA_iff σ φ h)
  | .and φ ψ, h => by
    simp only [LFml.initOnly, Bool.and_eq_true] at h
    exact and_congr (LFml.holdsA_iff σ φ h.1) (LFml.holdsA_iff σ ψ h.2)
  | .imp φ ψ, h => by
    simp only [LFml.initOnly, Bool.and_eq_true] at h
    exact imp_congr (LFml.holdsA_iff σ φ h.1) (LFml.holdsA_iff σ ψ h.2)

/-! ## The reads, and the constraints on them -/

mutual

/-- The paths a term reads the storage at, with every prefix of each:
`balances[people[a].age]` reads `balances[people[a].age]`, `balances`,
`people[a].age`, `people[a]` and `people`. -/
def LTerm.reads : LTerm → List LPath
  | .lit _ | .var _ | .err | .sok _ | .env _ | .findP _ _ | .cpok _ _ => []
  | .find _ q | .has _ q | .kmap _ _ q | .len _ q => q.reads
  | .pok q => q.keyReads
  | .binop _ _ a b | .seq a b | .orElse a b => a.reads ++ b.reads
  | .unop _ _ a | .zero a => a.reads
  | .ite c a b => c.reads ++ a.reads ++ b.reads
  | .kite a b t e => a.reads ++ b.reads ++ t.reads ++ e.reads

/-- The path and its prefixes, and what its keys read. -/
def LPath.reads : LPath → List LPath
  | .root r => [.root r]
  | .field q f => .field q f :: q.reads
  | .at q k => .at q k :: (q.reads ++ k.reads)

/-- What the path's keys read. -/
def LPath.keyReads : LPath → List LPath
  | .root _ => []
  | .field q _ => q.keyReads
  | .at q k => q.keyReads ++ k.reads

end

/-- The paths a formula reads the storage at. -/
def LFml.reads : LFml → List LPath
  | .tt => []
  | .eq a b => a.reads ++ b.reads
  | .not φ => φ.reads
  | .and φ ψ | .imp φ ψ => φ.reads ++ ψ.reads
  | .all .. => []

theorem LPath.mem_reads_self : (q : LPath) → q ∈ q.reads
  | .root _ | .field _ _ | .at _ _ => List.mem_cons_self

theorem LPath.keyReads_sub : (q : LPath) → ∀ Q ∈ q.keyReads, Q ∈ q.reads
  | .root _ => by simp [LPath.keyReads]
  | .field q _ => fun Q h => List.mem_cons_of_mem _ (LPath.keyReads_sub q Q h)
  | .at q k => fun Q h => by
    simp only [LPath.keyReads, List.mem_append] at h
    simp only [LPath.reads, List.mem_cons, List.mem_append]
    rcases h with h | h
    · exact .inr (.inl (LPath.keyReads_sub q Q h))
    · exact .inr (.inr h)

/-- Two choices of reads that agree where `R` reads, under the first. -/
def Agree (E : Var → Res Value) (o o' : List Seg → Obs) (R : List LPath) : Prop :=
  ∀ Q ∈ R, ∀ qs, Q.evalA E o = .ok qs → o' qs = o qs

theorem Agree.append_left {E o o'} {R R' : List LPath} (h : Agree E o o' (R ++ R')) :
    Agree E o o' R := fun Q hQ => h Q (List.mem_append_left _ hQ)

theorem Agree.append_right {E o o'} {R R' : List LPath} (h : Agree E o o' (R ++ R')) :
    Agree E o o' R' := fun Q hQ => h Q (List.mem_append_right _ hQ)

theorem Agree.cons {E o o'} {Q : LPath} {R : List LPath} (h : Agree E o o' (Q :: R)) :
    Agree E o o' R := fun Q' hQ => h Q' (List.mem_cons_of_mem _ hQ)

theorem Agree.sub {E o o'} {R R' : List LPath} (h : Agree E o o' R) (hs : ∀ Q ∈ R', Q ∈ R) :
    Agree E o o' R' := fun Q hQ => h Q (hs Q hQ)

/-- A read through agreeing choices. -/
theorem bind_agree {α : Type} {E o o'} {q : LPath} {R : List LPath} (h : Agree E o o' R)
    (hq : q ∈ R) (F : Obs → Res α) :
    (q.evalA E o >>= fun qs => F (o' qs)) = (q.evalA E o >>= fun qs => F (o qs)) := by
  cases hv : q.evalA E o with
  | error e => rfl
  | ok qs => simp only [Res.ok_bind, h q hq qs hv]

mutual

/-- **A term depends on the reads it makes only**: two choices agreeing at
them give it the same value. -/
theorem LTerm.evalA_agree {E : Var → Res Value} {o o' : List Seg → Obs} :
    (t : LTerm) → Agree E o o' t.reads → t.evalA E o' = t.evalA E o
  | .lit _, _ | .var _, _ | .err, _ | .env _, _ | .findP _ _, _ | .cpok _ _, _ => rfl
  | .sok .init, _ | .sok (.save ..), _ | .sok (.del ..), _ | .sok (.arr ..), _
  | .sok (.stale ..), _ | .sok (.copy ..), _ | .sok (.view ..), _ => rfl
  | .find (.save ..) _, _ | .find (.del ..) _, _ | .has (.save ..) _, _ | .has (.del ..) _, _
  | .kmap _ (.save ..) _, _ | .kmap _ (.del ..) _, _ | .len (.save ..) _, _
  | .len (.del ..) _, _ => rfl
  | .find (.arr ..) _, _ | .find (.copy ..) _, _ | .has (.arr ..) _, _ | .has (.copy ..) _, _
  | .kmap _ (.arr ..) _, _ | .kmap _ (.copy ..) _, _ | .len (.arr ..) _, _
  | .len (.copy ..) _, _ => rfl
  | .find (.stale ..) _, _ | .has (.stale ..) _, _ | .kmap _ (.stale ..) _, _
  | .len (.stale ..) _, _ => rfl
  | .find (.view ..) _, _ | .has (.view ..) _, _ | .kmap _ (.view ..) _, _
  | .len (.view ..) _, _ => rfl
  | .binop _ _ a b, h => by
    simp only [LTerm.evalA, LTerm.evalA_agree a h.append_left, LTerm.evalA_agree b h.append_right]
  | .unop _ _ a, h => by simp only [LTerm.evalA, LTerm.evalA_agree a h]
  | .zero a, h => by simp only [LTerm.evalA, LTerm.evalA_agree a h]
  | .ite c a b, h => by
    simp only [LTerm.evalA, LTerm.evalA_agree c h.append_left.append_left,
      LTerm.evalA_agree a h.append_left.append_right, LTerm.evalA_agree b h.append_right]
  | .seq a b, h => by
    simp only [LTerm.evalA, LTerm.evalA_agree a h.append_left, LTerm.evalA_agree b h.append_right]
  | .orElse a b, h => by
    simp only [LTerm.evalA, LTerm.evalA_agree a h.append_left, LTerm.evalA_agree b h.append_right]
  | .kite a b t e, h => by
    simp only [LTerm.evalA, LTerm.evalA_agree a h.append_left.append_left.append_left,
      LTerm.evalA_agree b h.append_left.append_left.append_right,
      LTerm.evalA_agree t h.append_left.append_right, LTerm.evalA_agree e h.append_right]
  | .find .init q, h => by
    simp only [LTerm.evalA, LPath.evalA_agree q (h.sub (LPath.keyReads_sub q))]
    exact bind_agree h (LPath.mem_reads_self q) Obs.find
  | .has .init q, h => by
    simp only [LTerm.evalA, LPath.evalA_agree q (h.sub (LPath.keyReads_sub q))]
    exact bind_agree h (LPath.mem_reads_self q) Obs.has
  | .kmap sh .init q, h => by
    simp only [LTerm.evalA, LPath.evalA_agree q (h.sub (LPath.keyReads_sub q))]
    exact bind_agree h (LPath.mem_reads_self q) (Obs.test sh)
  | .len .init q, h => by
    simp only [LTerm.evalA, LPath.evalA_agree q (h.sub (LPath.keyReads_sub q))]
    exact bind_agree h (LPath.mem_reads_self q) Obs.len
  | .pok q, h => by simp only [LTerm.evalA, LPath.evalA_agree q h]

/-- The same for a path, whose value depends on what its keys read. -/
theorem LPath.evalA_agree {E : Var → Res Value} {o o' : List Seg → Obs} :
    (q : LPath) → Agree E o o' q.keyReads → q.evalA E o' = q.evalA E o
  | .root _, _ => rfl
  | .field q _, h => by simp only [LPath.evalA, LPath.evalA_agree q h]
  | .at q k, h => by
    simp only [LPath.evalA, LPath.evalA_agree q h.append_left, LTerm.evalA_agree k h.append_right]

end

/-- The same for a formula. -/
theorem LFml.holdsA_agree {E : Var → Res Value} {o o' : List Seg → Obs} :
    (φ : LFml) → Agree E o o' φ.reads → (φ.holdsA E o' ↔ φ.holdsA E o)
  | .tt, _ => Iff.rfl
  | .eq a b, h => by
    simp only [LFml.holdsA, LTerm.evalA_agree a h.append_left, LTerm.evalA_agree b h.append_right]
  | .not φ, h => not_congr (LFml.holdsA_agree φ h)
  | .and φ ψ, h => and_congr (LFml.holdsA_agree φ h.append_left) (LFml.holdsA_agree ψ h.append_right)
  | .imp φ ψ, h => imp_congr (LFml.holdsA_agree φ h.append_left) (LFml.holdsA_agree ψ h.append_right)
  | .all .., _ => Iff.rfl

/-- **The constraint a read path puts on the reads**: the location it names
stands to the one above it as `ChildOk` says.  Example: for `balances[k]`,
where `balances` is a mapping `balances[k]` is there. -/
def LPath.consA (E : Var → Res Value) (o : List Seg → Obs) : LPath → Prop
  | .root _ => True
  | .field q f => ∀ qs, q.evalA E o = .ok qs → ChildOk (o qs) (.field f) (o (qs ++ [.field f]))
  | .at q k => ∀ qs, q.evalA E o = .ok qs → ∀ i, (k.evalA E o >>= Value.asInt) = .ok i →
      ChildOk (o qs) (.at i) (o (qs ++ [.at i]))

/-- **The constraints**: every read path's. -/
def consAll (E : Var → Res Value) (o : List Seg → Obs) : List LPath → Prop
  | [] => True
  | Q :: R => Q.consA E o ∧ consAll E o R

theorem consAll_iff {E o} : (R : List LPath) → (consAll E o R ↔ ∀ Q ∈ R, Q.consA E o)
  | [] => by simp [consAll]
  | Q :: R => by simp [consAll, consAll_iff R]

/-- **Every storage meets the constraints.** -/
theorem consA_obsAt (σ : State) : (Q : LPath) → Q.consA (envOf σ) (obsAt σ)
  | .root _ => trivial
  | .field _ f => fun qs _ => childOk_findLive _ qs (.field f)
  | .at _ _ => fun qs _ i _ => childOk_findLive _ qs (.at i)

/-! ## Realizability -/

/-- The paths the read paths `R` evaluate to, under `E` and `o`. -/
def evalPaths (E : Var → Res Value) (o : List Seg → Obs) (R : List LPath) : List (List Seg) :=
  R.filterMap fun Q => match Q.evalA E o with
    | .ok qs => some qs
    | .error _ => none

theorem mem_evalPaths {E o} {R : List LPath} {K : List Seg} :
    K ∈ evalPaths E o R ↔ ∃ Q ∈ R, Q.evalA E o = .ok K := by
  simp only [evalPaths, List.mem_filterMap]
  constructor
  · rintro ⟨Q, hQ, h⟩
    split at h
    · rename_i qs hq; cases h; exact ⟨Q, hQ, hq⟩
    · cases h
  · rintro ⟨Q, hQ, h⟩
    exact ⟨Q, hQ, by simp [h]⟩

/-- The path above: `balances` of `balances[k]`. -/
def LPath.parent : LPath → Option LPath
  | .root _ => none
  | .field q _ | .at q _ => some q

/-- The read paths hold the path above each. -/
def ParentClosed (R : List LPath) : Prop := ∀ Q ∈ R, ∀ q, Q.parent = some q → q ∈ R

theorem ParentClosed.append {R R' : List LPath} (h : ParentClosed R) (h' : ParentClosed R') :
    ParentClosed (R ++ R') := by
  intro Q hQ q hq
  rcases List.mem_append.1 hQ with hQ | hQ
  · exact List.mem_append_left _ (h Q hQ q hq)
  · exact List.mem_append_right _ (h' Q hQ q hq)

mutual

theorem LTerm.reads_closed : (t : LTerm) → ParentClosed t.reads
  | .lit _ | .var _ | .err | .sok _ | .env _ | .findP _ _ | .cpok _ _ => by
    intro Q h; simp only [LTerm.reads, List.not_mem_nil] at h
  | .find _ q | .has _ q | .kmap _ _ q | .len _ q => LPath.reads_closed q
  | .pok q => LPath.keyReads_closed q
  | .binop _ _ a b | .seq a b | .orElse a b =>
    (LTerm.reads_closed a).append (LTerm.reads_closed b)
  | .unop _ _ a | .zero a => LTerm.reads_closed a
  | .ite c a b => ((LTerm.reads_closed c).append (LTerm.reads_closed a)).append
      (LTerm.reads_closed b)
  | .kite a b t e => (((LTerm.reads_closed a).append (LTerm.reads_closed b)).append
      (LTerm.reads_closed t)).append (LTerm.reads_closed e)

theorem LPath.reads_closed : (q : LPath) → ParentClosed q.reads
  | .root _ => by
    intro Q h p hp
    simp only [LPath.reads, List.mem_singleton] at h
    subst h; cases hp
  | .field q f => by
    intro Q h p hp
    simp only [LPath.reads, List.mem_cons] at h
    rcases h with rfl | h
    · cases hp; exact List.mem_cons_of_mem _ (LPath.mem_reads_self q)
    · exact List.mem_cons_of_mem _ (LPath.reads_closed q Q h p hp)
  | .at q k => by
    intro Q h p hp
    simp only [LPath.reads, List.mem_cons] at h
    rcases h with rfl | h
    · cases hp; exact List.mem_cons_of_mem _ (List.mem_append_left _ (LPath.mem_reads_self q))
    · exact List.mem_cons_of_mem _
        (((LPath.reads_closed q).append (LTerm.reads_closed k)) Q h p hp)

theorem LPath.keyReads_closed : (q : LPath) → ParentClosed q.keyReads
  | .root _ => by intro Q h; simp [LPath.keyReads] at h
  | .field q _ => LPath.keyReads_closed q
  | .at q k => (LPath.keyReads_closed q).append (LTerm.reads_closed k)

end

theorem LFml.reads_closed : (φ : LFml) → ParentClosed φ.reads
  | .tt => by intro Q h; simp [LFml.reads] at h
  | .eq a b => (LTerm.reads_closed a).append (LTerm.reads_closed b)
  | .not φ => LFml.reads_closed φ
  | .and φ ψ | .imp φ ψ => (LFml.reads_closed φ).append (LFml.reads_closed ψ)
  | .all .. => by intro Q h; simp [LFml.reads] at h

/-- A path starts at a root. -/
theorem LPath.evalA_root {E o} : (q : LPath) → ∀ {K : List Seg}, q.evalA E o = .ok K →
    ∃ r t, K = .field r :: t
  | .root r, K, h => by cases h; exact ⟨r, [], rfl⟩
  | .field q f, K, h => by
    obtain ⟨qs, hq, he⟩ := Res.bind_eq_ok.1 h; cases he
    obtain ⟨r, t, rfl⟩ := LPath.evalA_root q hq
    exact ⟨r, t ++ [.field f], rfl⟩
  | .at q k, K, h => by
    obtain ⟨qs, hq, h⟩ := Res.bind_eq_ok.1 h
    obtain ⟨i, _, he⟩ := Res.bind_eq_ok.1 h; cases he
    obtain ⟨r, t, rfl⟩ := LPath.evalA_root q hq
    exact ⟨r, t ++ [.at i], rfl⟩

theorem append_singleton_inj {P Q : List Seg} {s t : Seg} (h : P ++ [s] = Q ++ [t]) :
    P = Q ∧ s = t := by
  have h1 := congrArg List.dropLast h
  have h2 := congrArg List.getLast? h
  simp only [List.dropLast_concat, List.getLast?_concat, Option.some.injEq] at h1 h2
  exact ⟨h1, h2⟩

/-- The evaluated read paths are closed under prefixes, and meet `ChildOk`
at every step, where the read paths are closed and meet the constraints. -/
theorem evalPaths_closed {E o} {R : List LPath} (hR : ParentClosed R) :
    PrefixClosed (evalPaths E o R) := by
  intro K hK P s he
  obtain ⟨Q, hQ, hv⟩ := mem_evalPaths.1 hK
  cases Q with
  | root r =>
    cases hv
    left
    cases P with
    | nil => rfl
    | cons _ _ => simp at he
  | field q f =>
    obtain ⟨qs, hq, h⟩ := Res.bind_eq_ok.1 hv; cases h
    obtain ⟨rfl, -⟩ := append_singleton_inj he.symm
    exact .inr (mem_evalPaths.2 ⟨q, hR _ hQ q rfl, hq⟩)
  | «at» q k =>
    obtain ⟨qs, hq, h⟩ := Res.bind_eq_ok.1 hv
    obtain ⟨i, _, h⟩ := Res.bind_eq_ok.1 h; cases h
    obtain ⟨rfl, -⟩ := append_singleton_inj he.symm
    exact .inr (mem_evalPaths.2 ⟨q, hR _ hQ q rfl, hq⟩)

theorem evalPaths_childOk {E o} {R : List LPath} (hc : ∀ Q ∈ R, Q.consA E o) :
    ∀ K ∈ evalPaths E o R, ∀ P s, K = P ++ [s] → P ≠ [] → ChildOk (o P) s (o K) := by
  intro K hK P s he hP
  obtain ⟨Q, hQ, hv⟩ := mem_evalPaths.1 hK
  have hc := hc Q hQ
  cases Q with
  | root r =>
    cases hv
    cases P with
    | nil => exact absurd rfl hP
    | cons _ _ => simp at he
  | field q f =>
    obtain ⟨qs, hq, h⟩ := Res.bind_eq_ok.1 hv; cases h
    obtain ⟨rfl, rfl⟩ := append_singleton_inj he.symm
    exact hc _ hq
  | «at» q k =>
    obtain ⟨qs, hq, h⟩ := Res.bind_eq_ok.1 hv
    obtain ⟨i, hi, h⟩ := Res.bind_eq_ok.1 h; cases h
    obtain ⟨rfl, rfl⟩ := append_singleton_inj he.symm
    exact hc _ hq _ hi

/-- The roots of a storage tree. -/
def rootsOf : SVal → List (Name × SVal)
  | .struct fs => fs
  | _ => []

theorem realize_struct (o : List Seg → Obs) (Ks : List (List Seg)) :
    SVal.struct (rootsOf (realize o Ks)) = realize o Ks := by
  simp [realize, depth, build, atRoot, rootsOf]

/-- **Realizability, for a formula**: a choice of reads that meets the
constraints of `ψ`'s read paths is what the storage of some state shows at
every one of them, a state with the locals of `σ`. -/
theorem realize_reads (ψ : LFml) (σ : State) (o : List Seg → Obs)
    (hc : consAll (envOf σ) o ψ.reads) :
    ∃ σ' : State, envOf σ' = envOf σ ∧ Agree (envOf σ) o (obsAt σ') ψ.reads := by
  let Ks := evalPaths (envOf σ) o ψ.reads
  refine ⟨{ σ with storage := rootsOf (realize o Ks) }, rfl, ?_⟩
  intro Q hQ qs hq
  have hK : qs ∈ Ks := mem_evalPaths.2 ⟨Q, hQ, hq⟩
  simp only [obsAt, realize_struct]
  exact realize_findLive (evalPaths_closed (LFml.reads_closed ψ))
    (evalPaths_childOk ((consAll_iff _).1 hc))
    (fun K hK => by
      obtain ⟨Q, _, hv⟩ := mem_evalPaths.1 hK
      exact LPath.evalA_root Q hv) qs hK

/-- **Completeness of the reads**: a reduced formula that reads the initial
storage only holds in every state exactly when it holds for every choice of
locals and of what each read path shows that meets the constraints.  This
is mini-solkey's `LFml.valid_iff`, for a storage of shapes: the right-hand
side has the reads as free atoms, so it is a statement of propositional
logic, integer arithmetic and equalities between reads. -/
theorem LFml.valid_iff_cons (ψ : LFml) (h : ψ.initOnly = true) :
    (∀ σ, ψ.holds σ) ↔
      ∀ σ (o : List Seg → Obs), consAll (envOf σ) o ψ.reads → ψ.holdsA (envOf σ) o := by
  constructor
  · intro hv σ o hc
    obtain ⟨σ', he, ha⟩ := realize_reads ψ σ o hc
    have := (LFml.holdsA_iff σ' ψ h).2 (hv σ')
    rw [he] at this
    exact (LFml.holdsA_agree ψ ha).1 this
  · intro hv σ
    exact (LFml.holdsA_iff σ ψ h).1
      (hv σ _ ((consAll_iff _).2 fun Q _ => consA_obsAt σ Q))

/-- **`⊨ φ` is exactly the reduction under the constraints**, for every `φ`
in the fragment whose reduction reads the initial storage only.  Example:
`[ uint y = x.a; uint z = x.a.b; ] false` is valid, since a word has
nothing below it: the constraint of `x.a.b` says that where `x.a` shows a
word, `x.a.b` shows nothing. -/
theorem _root_.Solidity.Fml.valid_iff_cons {C : Contract} (φ : Fml C)
    (hf : φ.inL Sym.empty = true) (hi : φ.reduce.initOnly = true) :
    (⊨ φ) ↔ ∀ σ (o : List Seg → Obs),
      consAll (envOf σ) o φ.reduce.reads → φ.reduce.holdsA (envOf σ) o := by
  rw [Fml.valid_iff_reduce φ hf]
  exact LFml.valid_iff_cons _ hi

/-! ## The tactic, with the constraints -/

/-! The equations of `evalA` and `holdsA`, the local's aside: a local is
split on first. -/

theorem LFml.holdsA_tt (E o) : LFml.tt.holdsA E o ↔ True := Iff.rfl
theorem LFml.holdsA_not (E o) (φ : LFml) : (LFml.not φ).holdsA E o ↔ ¬ φ.holdsA E o := Iff.rfl
theorem LFml.holdsA_and (E o) (φ ψ : LFml) :
    (LFml.and φ ψ).holdsA E o ↔ φ.holdsA E o ∧ ψ.holdsA E o := Iff.rfl
theorem LFml.holdsA_imp (E o) (φ ψ : LFml) :
    (LFml.imp φ ψ).holdsA E o ↔ (φ.holdsA E o → ψ.holdsA E o) := Iff.rfl
theorem LFml.holdsA_eq (E o) (a b : LTerm) : (LFml.eq a b).holdsA E o ↔
    Modality.diamond.wp (a.evalA E o) fun x => Modality.diamond.wp (b.evalA E o) fun y => x = y := by
  simp only [LFml.holdsA]
  cases a.evalA E o <;> cases b.evalA E o <;> simp [Modality.wp, Modality.onHalt]

section
variable (E : Var → Res Value) (o : List Seg → Obs)
theorem LTerm.evalA_lit (v : Value) : (LTerm.lit v).evalA E o = .ok v := rfl
theorem LTerm.evalA_binop (op : BinOp) (p : PrimTy) (a b : LTerm) :
    (LTerm.binop op p a b).evalA E o = a.evalA E o >>= fun x => evalBinop op p x (b.evalA E o) :=
  rfl
theorem LTerm.evalA_unop (op : UnOp) (p : PrimTy) (a : LTerm) :
    (LTerm.unop op p a).evalA E o = a.evalA E o >>= fun x => applyUnOp op x >>= unopCheck op p :=
  rfl
theorem LTerm.evalA_ite (c a b : LTerm) : (LTerm.ite c a b).evalA E o =
    c.evalA E o >>= fun cv => pickBranch cv (a.evalA E o) (b.evalA E o) := rfl
theorem LTerm.evalA_find (q : LPath) :
    (LTerm.find .init q).evalA E o = q.evalA E o >>= fun qs => (o qs).find := rfl
theorem LTerm.evalA_has (q : LPath) :
    (LTerm.has .init q).evalA E o = q.evalA E o >>= fun qs => (o qs).has := rfl
theorem LTerm.evalA_kmap (sh : KShape) (q : LPath) :
    (LTerm.kmap sh .init q).evalA E o = q.evalA E o >>= fun qs => (o qs).test sh := rfl
theorem LTerm.evalA_len (q : LPath) :
    (LTerm.len .init q).evalA E o = q.evalA E o >>= fun qs => (o qs).len := rfl
theorem LTerm.evalA_sok : (LTerm.sok .init).evalA E o = .ok (.bool true) := rfl
theorem LTerm.evalA_pok (q : LPath) :
    (LTerm.pok q).evalA E o = q.evalA E o >>= fun _ => .ok (.bool true) := rfl
theorem LTerm.evalA_seq (d a : LTerm) :
    (LTerm.seq d a).evalA E o = d.evalA E o >>= fun _ => a.evalA E o := rfl
theorem LTerm.evalA_orElse (a b : LTerm) :
    (LTerm.orElse a b).evalA E o = orElseR (a.evalA E o) (b.evalA E o) := rfl
theorem LTerm.evalA_kite (a b t e : LTerm) : (LTerm.kite a b t e).evalA E o =
    (a.evalA E o >>= Value.asInt) >>= fun i => (b.evalA E o >>= Value.asInt) >>= fun j =>
      if i = j then t.evalA E o else e.evalA E o := rfl
theorem LTerm.evalA_zero (a : LTerm) :
    (LTerm.zero a).evalA E o = a.evalA E o >>= fun v => .ok (zeroV v) := rfl
theorem LTerm.evalA_err : LTerm.err.evalA E o = .error .stuck := rfl
theorem LTerm.evalA_var (x : Var) : (LTerm.var x).evalA E o = E x := rfl
end

open Lean Elab Tactic Meta in
/-- Compute the read paths `LFml.reads ψ` of the goal `∀ σ o, consAll … (LFml.reads ψ) → …`
as a list, run as compiled code and quoted back; the kernel checks it. -/
def readsGoal (g : MVarId) : MetaM MVarId := do
  let ty ← instantiateMVars (← g.getType)
  let ty' ← Meta.transform ty (pre := fun e => do
    if e.isAppOfArity ``LFml.reads 1 && !e.hasFVar && !e.hasLooseBVars && !e.hasMVar then
      let l ← unsafe evalExpr (List LPath)
        (mkApp (mkConst ``List [levelZero]) (mkConst ``LPath)) e
      return .done (toExpr l)
    return .continue)
  g.replaceTargetDefEq ty'

open Lean Elab Tactic in
/-- Replace `LFml.reads ψ` by the list it computes to. -/
elab "sol_reads" : tactic => do replaceMainGoal [← readsGoal (← getMainGoal)]

open Lean Elab Tactic Meta in
/-- Take the hypothesis `consAll E o [Q₀, …]` apart: one hypothesis
`LPath.consA E o Q` for each read path, each once. -/
elab "sol_cons_split" h:ident : tactic => withMainContext do
  let g ← getMainGoal
  let d ← getLocalDeclFromUserName h.getId
  let ty ← instantiateMVars d.type
  let_expr consAll E o l := ty | throwError "sol_decide: expected `consAll …`"
  let some (_, elems) := l.listLit? | throwError "sol_decide: the read paths are not a list"
  let lpath := mkConst ``LPath
  let mut seen : Array Expr := #[]
  let mut hyps : Array Hypothesis := #[]
  let mut prf : Expr := d.toExpr
  for k in [0:elems.length] do
    let q := elems[k]!
    let rest ← mkListLit lpath (elems.drop (k + 1))
    let a := mkApp3 (mkConst ``LPath.consA) E o q
    let b := mkApp3 (mkConst ``consAll) E o rest
    unless seen.contains q do
      seen := seen.push q
      let n ← mkFreshUserName `hq
      hyps := hyps.push { userName := n, type := a, value := mkApp3 (mkConst ``And.left) a b prf }
    prf := mkApp3 (mkConst ``And.right) a b prf
  let (_, g) ← g.assertHypotheses hyps
  let g ← g.clear d.fvarId
  replaceMainGoal [g]

/-! What a location shows, in the terms `grind` reasons in. -/

@[simp] theorem Obs.find_eq_ok {c : Obs} {v : Value} : c.find = .ok v ↔ c = .word v := by
  cases c <;> simp [Obs.find]

@[simp] theorem Obs.has_eq_ok {c : Obs} {v : Value} :
    c.has = .ok v ↔ v = .bool true ∧ c ≠ .absent := by
  cases c <;> simp [Obs.has, eq_comm]

@[simp] theorem Obs.test_map_eq_ok {c : Obs} {v : Value} :
    c.test .map = .ok v ↔ v = .bool true ∧ c = .map := by
  cases c <;> simp [Obs.test, eq_comm]

@[simp] theorem Obs.test_fixed_eq_ok {c : Obs} {v : Value} :
    c.test .fixed = .ok v ↔ v = .bool true ∧ ∃ n, c = .arr n true := by
  cases c <;> simp [Obs.test, eq_comm]
  rename_i fx; cases fx <;> simp

@[simp] theorem Obs.len_eq_ok {c : Obs} {v : Value} :
    c.len = .ok v ↔ ∃ n : Nat, v = .int n ∧ ∃ fx, c = .arr n fx := by
  cases c <;> simp [Obs.len, eq_comm]

/-- A local read as a value halts, is an integer, or is a boolean. -/
theorem res_value_cases (r : Res Value) :
    (∃ e, r = .error e) ∨ (∃ i, r = .ok (.int i)) ∨ ∃ b, r = .ok (.bool b) := value_cases r

open Lean Elab Tactic Meta in
/-- Split on every local the formula reads: `E x` halts, is an integer, or a
boolean. -/
elab "sol_decide_splitA" : tactic => withMainContext do
  let g ← getMainGoal
  let ty ← instantiateMVars (← g.getType)
  let_expr LFml.holdsA E _ r := ty | throwError "sol_decide: expected `LFml.holdsA E o …`"
  let xs ← unsafe evalExpr (List Var) (mkApp (mkConst ``List [levelZero]) (mkConst ``Var))
    (mkApp (mkConst ``LFml.vars) r)
  for x in xs.eraseDups do
    let tt ← Term.exprToSyntax (mkApp E (toExpr x))
    evalTactic (← `(tactic| all_goals
      rcases res_value_cases $tt with ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩))

/-- The shape a location shows: nothing, a word, a struct, an array, a
mapping. -/
theorem obs_cases (c : Obs) :
    c = .absent ∨ (∃ v, c = .word v) ∨ c = .struct ∨ (∃ n, c = .arr n false) ∨
      (∃ n, c = .arr n true) ∨ c = .map := by
  cases c <;> simp

open Lean Elab Tactic Meta in
/-- Split on the shape of every location that has a read path below it
(the first argument of a `ChildOk`): what it shows decides what the location
below may show. -/
elab "sol_decide_parents" : tactic => withMainContext do
  let mut parents : Array Expr := #[]
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    let found : Array Expr ← (StateT.run (s := #[]) do
      ty.forEachWhere (fun e => e.isAppOfArity ``ChildOk 3 && !e.hasLooseBVars)
        fun e => (modify (·.push e.appFn!.appFn!.appArg!) :
          StateT (Array Expr) TacticM Unit)) <&> (·.2)
    for e in found do
      unless parents.contains e do parents := parents.push e
  for e in parents do
    let t ← Term.exprToSyntax e
    evalTactic (← `(tactic| all_goals
      rcases obs_cases $t with h | ⟨_, h⟩ | h | ⟨_, h⟩ | ⟨_, h⟩ | h <;> simp only [h] at *))

attribute [decide_evalA] LFml.holdsA_tt LFml.holdsA_not LFml.holdsA_and LFml.holdsA_imp
  LFml.holdsA_eq LTerm.evalA_lit LTerm.evalA_binop LTerm.evalA_unop LTerm.evalA_ite
  LTerm.evalA_find LTerm.evalA_has LTerm.evalA_kmap LTerm.evalA_len LTerm.evalA_sok
  LTerm.evalA_pok LTerm.evalA_seq LTerm.evalA_orElse LTerm.evalA_kite LTerm.evalA_zero
  LTerm.evalA_err LTerm.evalA_var LPath.evalA LPath.consA zeroV_int zeroV_bool orElseR_ok
  orElseR_error Obs.find_eq_ok Obs.has_eq_ok Obs.test_map_eq_ok Obs.test_fixed_eq_ok Obs.len_eq_ok

/-- Unfold the reduced formula over free reads into `sol_close`'s weakest
preconditions, the constraints into `ChildOk`s between reads, and what a
location shows into equations on `o`. -/
macro "sol_decide_unfoldA" : tactic => `(tactic|
  set_option linter.unusedSimpArgs false in
  simp only [decide_evalA, close_rw, and_assoc, *] at *)

/-- The finishing step with the constraints (`LFml.valid_iff_cons`), on a
goal `∀ σ, ψ.holds σ` with `ψ` computed and reading the initial storage
only: the reads become free (`o`), the constraints hypotheses; split on the
locals and on the shape of every location with a read below it, and close
with `omega` or `grind`. -/
macro "sol_decide_cons" : tactic => `(tactic| (
    refine (LFml.valid_iff_cons _ (by decide)).2 ?_
    sol_reads
    intro σ o hc
    sol_cons_split hc
    sol_decide_splitA
    all_goals sol_decide_unfoldA
    all_goals first
      | omega
      | grind
      | (sol_decide_parents
         all_goals simp only [ChildOk, Obs.test, Obs.find, Obs.has, Obs.len, Res.ok_bind,
           Res.error_bind, orElseR_ok, orElseR_error, Bool.false_eq_true, false_and, and_self,
           if_true, if_false] at *
         all_goals first | omega | grind)))

/-- `sol_decide` without the constraints: the reduction, then
`sol_decide_heuristic`, which reads the initial storage as unrelated atoms.
What `sol_decide` did before the reads were proved realizable; the examples
use it to show a goal that needs the constraints. -/
macro "sol_decide_unconstrained" : tactic => `(tactic|
  all_goals
   (refine (Fml.valid_iff_reduce _ (by decide)).2 ?_
    sol_reduce
    sol_decide_heuristic))

/-- `sol_decide`: prove `⊨ φ` for a `φ` whose modalities are gone (run
`sol_symex` first) and which is in the fragment (`Fml.inL`).  It rewrites
the goal by `Fml.valid_iff_reduce`, computes the reduction, closes it by its terms where it can (`LFml.syn`,
`Calculus/DecideSyn.lean`: KeY's syntactic closing), and otherwise, where the
reduction reads the initial storage only, rewrites it once more by
`LFml.valid_iff_cons`: a statement about free reads under the constraints
the storage puts on them, which it closes by splitting on the locals and on
the shapes of the locations above the reads, and `omega` or `grind`.  Both
steps are equivalences, so it fails on an invalid formula; on a valid one it
fails only where `omega`/`grind` do.  Where the reduction still writes
through a member named `length` it falls back to `sol_decide_heuristic`.
It says so when `φ` is outside the fragment; with no goal left it does
nothing. -/
macro "sol_decide" : tactic => `(tactic|
  all_goals
   (refine (Fml.valid_iff_reduce _ (by
      first
      | decide +kernel
      | fail "sol_decide: the formula is outside the fragment (a modality, a push of a memory object, a copy of memory whose guards are not literals, a copy from storage outside its allocation's pair, a memory past memSize, a read of the ledger, an alias no update binds, or one through an index used after a write)")).2 ?_
    sol_reduce
    first
    | exact LFml.syn_valid _ (by decide +kernel)
    | sol_decide_cons
    | sol_decide_heuristic))

end Decide

end Solidity
