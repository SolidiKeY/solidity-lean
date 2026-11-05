import Solidity.Semantics.AbiEntry

/-!
# ABI entry decoding: access-time failures of calldata elements

`AbiEntry.cval` validates a calldata reference completely and stops at the
first failing access. solc validates nested calldata only when it is read
(`calldata_array_index_access`, `access_calldata_tail`, the word validator),
so an input whose reference fails somewhere can still run a body that never
reads the failing element. `cpart` is the same lazy reader, in the same
order and with the same checks, except that a failing node does not stop it:
the node is recorded by its access path (element and member indices from the
reference) and replaced by a substitute value of its shape (`Shape.dflt?`),
and the reading goes on with its siblings.

* `cpart_agree`: `cpart` and `cval` agree. No recorded path: `cval` accepts
  with the same value. Some recorded path: `cval` reverts (empty data). An
  error of `cpart` (fuel, or a shape without a substitute): `cval` fails too.
  So `abi.encode` of the reference, a complete lazy read (`abi_encode_*`
  from calldata goes through the same accessors, `docs/feature-work/abi-hashes.md`,
  lane FU2-C probes), reverts exactly when a path is recorded.
* `cpart_cval`: conversely, a reference `cval` accepts records no path and
  yields `cval`'s value.
* `cat` is one access along an index path (`x[i]…[j]`, or the base of a
  `.length`): each step's index access and tail check, then the word's
  validation for a word. `cat_cpart`: on the recorded paths of `cpart`, an
  access in range fails exactly when a recorded path is a prefix of its path.
  This is the guard the replay inserts before each read
  (`Tools/UpstreamEntry.lean`).

Design and evidence: `docs/feature-work/abi-hashes.md`, "Lane FU2-C".
-/

namespace Solidity.AbiEntry

/-- An access path below a calldata reference: element and member indices. -/
abbrev Path := List Nat

/-- `n` copies of a value. -/
def Seq.replicate {e : Shape} (v : Val e) : (n : Nat) → Seq e n
  | 0 => .nil
  | n + 1 => .cons v (Seq.replicate v n)

theorem zero_lt_W : 0 < W := by decide

mutual
/-- A substitute value of a shape, for a node whose access fails: zero words,
empty `bytes` and arrays. `none` only for a word kind without a valid zero
(an enum of no members). -/
def Shape.dflt? : (s : Shape) → Option (Val s)
  | .word k => if h : k.valid 0 = true then some (.word ⟨0, zero_lt_W, h⟩) else none
  | .bytes => some (.bytes [])
  | .array _ => some (.array (n := 0) .nil)
  | .fixed e n => (Shape.dflt? e).map fun d => .fixed (Seq.replicate d n)
  | .tuple ms => (Shape.dflts? ms).map .tuple
/-- Substitutes for a member list. -/
def Shape.dflts? : (ms : List Shape) → Option (Vals ms)
  | [] => some .nil
  | m :: ms => match Shape.dflt? m, Shape.dflts? ms with
    | some d, some ds => some (.cons d ds)
    | _, _ => none
end

/-- A failing node: its substitute, recorded at the empty path. A shape
without a substitute is outside the model (`Fail.panic`, never certified). -/
def miss (s : Shape) : Except Fail (Val s × List Path) :=
  match s.dflt? with
  | some d => .ok (d, [[]])
  | none => .error .panic

/-- A tail reference, or the failing node's substitute when its check fails. -/
def missOr (e : Shape) (r : Except Fail (Nat × Nat))
    (k : Nat × Nat → Except Fail (Val e × List Path)) : Except Fail (Val e × List Path) :=
  match r with
  | .ok r => k r
  | .error _ => miss e

mutual
/-- `cval` that records failing accesses instead of stopping at the first:
the value with every failing node replaced by its substitute, and the
failing nodes' paths, in reading order. -/
def cpart (I : Input) : Nat → (s : Shape) → Nat → Nat → Except Fail (Val s × List Path)
  | 0, _, _, _ => .error .fuel
  | _ + 1, .word k, addr, _ =>
    if h : k.valid (load I.data addr) = true then .ok (.word ⟨load I.data addr, load_lt _ _, h⟩, [])
    else miss (.word k)
  | _ + 1, .bytes, addr, len => .ok (.bytes (bytesAt I.data addr len), [])
  | f + 1, .array e, addr, len =>
    match cseqP I f e addr 0 len with
    | .ok (xs, ps) => .ok (.array xs, ps)
    | .error x => .error x
  | f + 1, .fixed e n, addr, _ =>
    match cseqP I f e addr 0 n with
    | .ok (xs, ps) => .ok (.fixed xs, ps)
    | .error x => .error x
  | f + 1, .tuple ms, addr, _ =>
    match cmembersP I f ms addr 0 0 with
    | .ok (vs, ps) => .ok (.tuple vs, ps)
    | .error x => .error x
  termination_by structural fuel _ _ _ => fuel

/-- `cseq`, recording: element `i`'s paths start with `i`. -/
def cseqP (I : Input) : Nat → (e : Shape) → Nat → Nat → (n : Nat) → Except Fail (Seq e n × List Path)
  | _, _, _, _, 0 => .ok (.nil, [])
  | 0, _, _, _, _ + 1 => .error .fuel
  | f + 1, e, base, i, n + 1 =>
    match celemP I f e base (wrap (base + i * e.headSize)) with
    | .error x => .error x
    | .ok (v, p) =>
      match cseqP I f e base (i + 1) n with
      | .error x => .error x
      | .ok (vs, q) => .ok (.cons v vs, p.map (i :: ·) ++ q)
  termination_by structural fuel _ _ _ _ => fuel

/-- `celem`, recording: a failing tail check fails the element itself. -/
def celemP (I : Input) : Nat → (e : Shape) → Nat → Nat → Except Fail (Val e × List Path)
  | 0, _, _, _ => .error .fuel
  | f + 1, e, base, src =>
    if e.dynamic then missOr e (tailRef I e base src) fun r => cpart I f e r.1 r.2
    else cpart I f e src 0
  termination_by structural fuel _ _ _ => fuel

/-- `cmembers`, recording: member `j`'s paths start with `j`. -/
def cmembersP (I : Input) : Nat → (ms : List Shape) → Nat → Nat → Nat → Except Fail (Vals ms × List Path)
  | _, [], _, _, _ => .ok (.nil, [])
  | 0, _ :: _, _, _, _ => .error .fuel
  | f + 1, m :: ms, base, pos, j =>
    match celemP I f m base (wrap (base + pos)) with
    | .error x => .error x
    | .ok (v, p) =>
      match cmembersP I f ms base (pos + m.headSize) (j + 1) with
      | .error x => .error x
      | .ok (vs, q) => .ok (.cons v vs, p.map (j :: ·) ++ q)
  termination_by structural fuel _ _ _ _ => fuel
end

/-- How a recording read and a stopping read of the same reference relate:
no recorded path and the same value, some path and an empty revert, or an
error on both sides. -/
def Agree {α : Type} : Except Fail (α × List Path) → Except Fail α → Prop
  | .ok (a, []), r => r = .ok a
  | .ok (_, _ :: _), r => r = .error .revert
  | .error _, r => ∃ x, r = .error x

theorem miss_agree (s : Shape) : Agree (miss s) (.error .revert) := by
  unfold miss
  split
  · exact rfl
  · exact ⟨.revert, rfl⟩

/-- A reading followed by another: the recorded paths of the first, then of
the second; the stopping read stops at the first failure. -/
theorem agree_seq {α β γ : Type} (c : α → β → γ) (i : Nat)
    {r1 : Except Fail (α × List Path)} {r2 : Except Fail (β × List Path)}
    {s1 : Except Fail α} {s2 : Except Fail β} :
    Agree r1 s1 → Agree r2 s2 → Agree (match r1 with
        | .error x => .error x
        | .ok (v, p) => match r2 with
          | .error x => .error x
          | .ok (vs, q) => .ok (c v vs, p.map (i :: ·) ++ q))
      (match s1 with
        | .error x => .error x
        | .ok v => match s2 with
          | .error x => .error x
          | .ok vs => .ok (c v vs)) := by
  intro h1 h2
  match r1, s1, h1 with
  | .error _, _, ⟨x, hx⟩ => subst hx; exact ⟨x, rfl⟩
  | .ok (_, _ :: _), _, h =>
    subst h
    match r2 with
    | .error x => exact ⟨.revert, rfl⟩
    | .ok (_, _) => exact rfl
  | .ok (v, []), _, h =>
    subst h
    match r2, s2, h2 with
    | .error _, _, ⟨x, hx⟩ => subst hx; exact ⟨x, rfl⟩
    | .ok (_, _ :: _), _, h => subst h; exact rfl
    | .ok (vs, []), _, h => subst h; exact rfl

/-- Wrapping the value of a reading. -/
theorem agree_map {α β : Type} (c : α → β) {r : Except Fail (α × List Path)} {s : Except Fail α} :
    Agree r s → Agree (match r with
        | .ok (xs, ps) => .ok (c xs, ps)
        | .error x => .error x)
      (match s with
        | .ok xs => .ok (c xs)
        | .error x => .error x) := by
  intro h
  match r, s, h with
  | .error _, _, ⟨x, hx⟩ => subst hx; exact ⟨x, rfl⟩
  | .ok (_, _ :: _), _, h => subst h; exact rfl
  | .ok (v, []), _, h => subst h; exact rfl

/-- `access_calldata_tail` fails only with an empty revert. -/
theorem tailRef_error {I : Input} {e : Shape} {base ptr : Nat} {x : Fail}
    (h : tailRef I e base ptr = .error x) : x = .revert := by
  unfold tailRef at h
  dsimp only at h
  repeat' split at h
  all_goals first
    | exact (Except.error.inj h).symm
    | exact Except.noConfusion h

theorem celem_step (I : Input) (f : Nat)
    (ih1 : ∀ (s : Shape) (addr len : Nat), Agree (cpart I f s addr len) (cval I f s addr len))
    (e : Shape) (base src : Nat) :
    Agree (celemP I (f + 1) e base src) (celem I (f + 1) e base src) := by
  rw [celemP, celem]
  cases hd : e.dynamic
  · exact ih1 e src 0
  · simp only [if_true]
    match ht : tailRef I e base src with
    | .ok r => exact ih1 e r.1 r.2
    | .error x =>
      have hx := tailRef_error ht
      subst hx
      exact miss_agree e

/-- Case analysis on an `Agree` hypothesis `h : Agree r s` whose sides were
generalized: both sides reduce on each case. -/
local macro "agree_cases" r:ident h:ident : tactic => `(tactic| (
  rcases $r:ident with _ | ⟨_, _ | ⟨_, _⟩⟩
  · obtain ⟨x, hx⟩ := $h:ident; subst hx; exact ⟨x, rfl⟩
  · simp only [Agree] at $h:ident; subst $h:ident; exact rfl
  · simp only [Agree] at $h:ident; subst $h:ident; exact rfl))

/-- The agreement, for the four mutually recursive readers at once. -/
theorem cpart_agree_all (I : Input) : ∀ f : Nat,
    (∀ (s : Shape) (addr len : Nat), Agree (cpart I f s addr len) (cval I f s addr len)) ∧
    (∀ (e : Shape) (base i n : Nat), Agree (cseqP I f e base i n) (cseq I f e base i n)) ∧
    (∀ (e : Shape) (base src : Nat), Agree (celemP I f e base src) (celem I f e base src)) ∧
    (∀ (ms : List Shape) (base pos j : Nat),
      Agree (cmembersP I f ms base pos j) (cmembers I f ms base pos)) := by
  intro f
  induction f with
  | zero =>
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro s addr len; exact ⟨.fuel, by simp only [cval]⟩
    · intro e base i n
      cases n with
      | zero => exact rfl
      | succ n => exact ⟨.fuel, by simp only [cseq]⟩
    · intro e base src; exact ⟨.fuel, by simp only [celem]⟩
    · intro ms base pos j
      cases ms with
      | nil => exact rfl
      | cons m ms => exact ⟨.fuel, by simp only [cmembers]⟩
  | succ f ih =>
    obtain ⟨ih1, ih2, ih3, ih4⟩ := ih
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro s addr len
      cases s with
      | word k =>
        simp only [cpart, cval]
        split
        · exact rfl
        · exact miss_agree _
      | bytes => exact rfl
      | array e =>
        rw [cpart, cval]
        have h := ih2 e addr 0 len
        revert h
        generalize cseqP I f e addr 0 len = r
        generalize cseq I f e addr 0 len = s
        intro h
        agree_cases r h
      | fixed e n =>
        rw [cpart, cval]
        have h := ih2 e addr 0 n
        revert h
        generalize cseqP I f e addr 0 n = r
        generalize cseq I f e addr 0 n = s
        intro h
        agree_cases r h
      | tuple ms =>
        rw [cpart, cval]
        have h := ih4 ms addr 0 0
        revert h
        generalize cmembersP I f ms addr 0 0 = r
        generalize cmembers I f ms addr 0 = s
        intro h
        agree_cases r h
    · intro e base i n
      cases n with
      | zero => exact rfl
      | succ n =>
        rw [cseqP, cseq]
        have h1 := ih3 e base (wrap (base + i * e.headSize))
        have h2 := ih2 e base (i + 1) n
        revert h1 h2
        generalize celemP I f e base (wrap (base + i * e.headSize)) = r1
        generalize celem I f e base (wrap (base + i * e.headSize)) = s1
        generalize cseqP I f e base (i + 1) n = r2
        generalize cseq I f e base (i + 1) n = s2
        intro h1 h2
        rcases r1 with _ | ⟨_, _ | ⟨_, _⟩⟩
        · obtain ⟨x, hx⟩ := h1; subst hx; exact ⟨x, rfl⟩
        · simp only [Agree] at h1; subst h1; agree_cases r2 h2
        · simp only [Agree] at h1; subst h1
          rcases r2 with _ | ⟨_, _⟩ <;> first | exact ⟨_, rfl⟩ | exact rfl
    · intro e base src
      exact celem_step I f ih1 e base src
    · intro ms base pos j
      cases ms with
      | nil => exact rfl
      | cons m ms =>
        rw [cmembersP, cmembers]
        have h1 := ih3 m base (wrap (base + pos))
        have h2 := ih4 ms base (pos + m.headSize) (j + 1)
        revert h1 h2
        generalize celemP I f m base (wrap (base + pos)) = r1
        generalize celem I f m base (wrap (base + pos)) = s1
        generalize cmembersP I f ms base (pos + m.headSize) (j + 1) = r2
        generalize cmembers I f ms base (pos + m.headSize) = s2
        intro h1 h2
        rcases r1 with _ | ⟨_, _ | ⟨_, _⟩⟩
        · obtain ⟨x, hx⟩ := h1; subst hx; exact ⟨x, rfl⟩
        · simp only [Agree] at h1; subst h1; agree_cases r2 h2
        · simp only [Agree] at h1; subst h1
          rcases r2 with _ | ⟨_, _⟩ <;> first | exact ⟨_, rfl⟩ | exact rfl

/-- **Agreement.** The recording reader and `cval` agree on every reference:
no recorded path and `cval`'s value, or some path and `cval`'s empty revert,
or a failure of both. -/
theorem cpart_agree (I : Input) (f : Nat) (s : Shape) (addr len : Nat) :
    Agree (cpart I f s addr len) (cval I f s addr len) :=
  (cpart_agree_all I f).1 s addr len

/-- A recorded path means `cval` (and so `abi.encode` of the reference)
reverts with empty data. -/
theorem cval_revert_of_cpart {I : Input} {f : Nat} {s : Shape} {addr len : Nat}
    {v : Val s} {q : Path} {qs : List Path}
    (h : cpart I f s addr len = .ok (v, q :: qs)) : cval I f s addr len = .error .revert := by
  have := cpart_agree I f s addr len
  rw [h] at this
  exact this

/-- No recorded path means `cval` accepts with the same value. -/
theorem cval_of_cpart {I : Input} {f : Nat} {s : Shape} {addr len : Nat} {v : Val s}
    (h : cpart I f s addr len = .ok (v, [])) : cval I f s addr len = .ok v := by
  have := cpart_agree I f s addr len
  rw [h] at this
  exact this

/-- **Converse.** A reference `cval` accepts records no path, and the value
is `cval`'s. -/
theorem cpart_of_cval {I : Input} {f : Nat} {s : Shape} {addr len : Nat} {v : Val s}
    (h : cval I f s addr len = .ok v) : cpart I f s addr len = .ok (v, []) := by
  have hA := cpart_agree I f s addr len
  match hc : cpart I f s addr len, hA with
  | .ok (w, []), hA =>
    have : cval I f s addr len = .ok w := hA
    rw [h] at this
    cases this
    rfl
  | .ok (_, _ :: _), hA =>
    have : cval I f s addr len = .error .revert := hA
    rw [h] at this
    cases this
  | .error _, hA =>
    obtain ⟨x, hx⟩ := hA
    rw [h] at hx
    cases hx

/-! ### One access along a path -/

/-- `q` is a prefix of `π`. -/
def Path.pre : Path → Path → Bool
  | [], _ => true
  | _ :: _, [] => false
  | a :: p, b :: q => a == b && Path.pre p q

/-- A byte of a calldata `bytes`: in place, never validated (an index out of
range is `Panic(0x32)`, outside the model). -/
def catBytes (len : Nat) : Path → Except Fail Unit
  | [] => .ok ()
  | [i] => if i < len then .ok () else .error .panic
  | _ => .error .panic

theorem catBytes_ne (len : Nat) (π : Path) : catBytes len π ≠ .error .revert := by
  unfold catBytes
  split
  · exact fun h => Except.noConfusion h
  · split
    · exact fun h => Except.noConfusion h
    · exact fun h => Except.noConfusion h fun h => Fail.noConfusion h
  · exact fun h => Except.noConfusion h fun h => Fail.noConfusion h

mutual
/-- **One access** below a reference of shape `s` at `addr` (`len` elements),
along the path `π`, in solc's order: `calldata_array_index_access` for each
index (out of range: `Panic(0x32)`, here `Fail.panic`, never certified), then
`access_calldata_tail` for a dynamic element (`tailRef`), and at the end the
word validator for a word. The empty path is the reference itself (the base
of a `.length`). The walk to element `i` takes one step per element, as
`cseq` does, so both readers spend the same fuel. -/
def cat (I : Input) : Nat → (s : Shape) → Nat → Nat → Path → Except Fail Unit
  | 0, _, _, _, _ => .error .fuel
  | _ + 1, .word k, addr, _, π =>
    if k.valid (load I.data addr) then (if π.isEmpty then .ok () else .error .panic)
    else .error .revert
  | _ + 1, .bytes, _, len, π => catBytes len π
  | _ + 1, .array _, _, _, [] => .ok ()
  | f + 1, .array e, addr, len, i :: π => catSeq I f e addr 0 len i π
  | _ + 1, .fixed _ _, _, _, [] => .ok ()
  | f + 1, .fixed e n, addr, _, i :: π => catSeq I f e addr 0 n i π
  | _ + 1, .tuple _, _, _, [] => .ok ()
  | f + 1, .tuple ms, addr, _, j :: π => catMembers I f ms addr 0 0 j π
  termination_by structural fuel _ _ _ _ => fuel

/-- Element `t` (then `π` below it) of a sequence, walking from element `i`
of the `n` left. -/
def catSeq (I : Input) : Nat → (e : Shape) → Nat → Nat → Nat → Nat → Path → Except Fail Unit
  | _, _, _, _, 0, _, _ => .error .panic
  | 0, _, _, _, _ + 1, _, _ => .error .fuel
  | f + 1, e, base, i, n + 1, t, π =>
    if t = i then catElem I f e base (wrap (base + i * e.headSize)) π
    else catSeq I f e base (i + 1) n t π
  termination_by structural fuel _ _ _ _ _ _ => fuel

/-- The element whose head is at `src`: through `access_calldata_tail` if it
is dynamic, then `π` below it. -/
def catElem (I : Input) : Nat → (e : Shape) → Nat → Nat → Path → Except Fail Unit
  | 0, _, _, _, _ => .error .fuel
  | f + 1, e, base, src, π =>
    if e.dynamic then (tailRef I e base src).bind fun r => cat I f e r.1 r.2 π
    else cat I f e src 0 π
  termination_by structural fuel _ _ _ _ => fuel

/-- Member `t` (then `π` below it), walking from member `j` at head
position `pos`. -/
def catMembers (I : Input) : Nat → (ms : List Shape) → Nat → Nat → Nat → Nat → Path →
    Except Fail Unit
  | _, [], _, _, _, _, _ => .error .panic
  | 0, _ :: _, _, _, _, _, _ => .error .fuel
  | f + 1, m :: ms, base, pos, j, t, π =>
    if t = j then catElem I f m base (wrap (base + pos)) π
    else catMembers I f ms base (pos + m.headSize) (j + 1) t π
  termination_by structural fuel _ _ _ _ _ _ => fuel
end

theorem any_pre_map (p : List Path) (i t : Nat) (π : Path) :
    (p.map (i :: ·)).any (fun q => Path.pre q (t :: π)) = (decide (i = t) && p.any (fun q => Path.pre q π)) := by
  induction p with
  | nil => simp only [List.map_nil, List.any_nil, Bool.and_false]
  | cons q p ih =>
    simp only [List.map_cons, List.any_cons, ih, Path.pre]
    by_cases hi : i = t
    · subst hi; simp only [beq_self_eq_true, decide_true, Bool.true_and]
    · have : (i == t) = false := by simp only [beq_eq_false_iff_ne, ne_eq, hi, not_false_eq_true]
      simp only [this, hi, decide_false, Bool.false_and, Bool.false_or]

/-- Paths whose heads all differ from `t` have no prefix of `t :: π`. -/
theorem any_pre_heads (q : List Path) (t : Nat) (π : Path)
    (h : ∀ x ∈ q, ∃ j r, x = j :: r ∧ j ≠ t) : q.any (fun x => Path.pre x (t :: π)) = false := by
  induction q with
  | nil => rfl
  | cons x q ih =>
    obtain ⟨j, r, rfl, hj⟩ := h x (List.mem_cons_self ..)
    have : (j == t) = false := by simp only [beq_eq_false_iff_ne, ne_eq, hj, not_false_eq_true]
    simp only [List.any_cons, Path.pre, this, Bool.false_and, Bool.false_or]
    exact ih fun y hy => h y (List.mem_cons_of_mem _ hy)

/-- Paths that are all nonempty have no prefix of the empty path. -/
theorem any_pre_nil (q : List Path) (h : ∀ x ∈ q, ∃ j r, x = j :: r) :
    q.any (fun x => Path.pre x []) = false := by
  induction q with
  | nil => rfl
  | cons x q ih =>
    obtain ⟨j, r, rfl⟩ := h x (List.mem_cons_self ..)
    simp only [List.any_cons, Path.pre, Bool.false_or]
    exact ih fun y hy => h y (List.mem_cons_of_mem _ hy)

/-- The heads of the paths recorded from element (or member) `i` of `n`. -/
def Heads (ps : List Path) (i n : Nat) : Prop := ∀ x ∈ ps, ∃ j r, x = j :: r ∧ i ≤ j ∧ j < i + n

theorem heads_seq {p q : List Path} {i n : Nat} (hq : Heads q (i + 1) n) :
    Heads (p.map (i :: ·) ++ q) i (n + 1) := by
  intro x hx
  rcases List.mem_append.1 hx with hx | hx
  · obtain ⟨r, _, rfl⟩ := List.mem_map.1 hx
    exact ⟨i, r, rfl, Nat.le_refl _, by omega⟩
  · obtain ⟨j, r, rfl, h1, h2⟩ := hq x hx
    exact ⟨j, r, rfl, by omega, by omega⟩

/-- The access property of `cpart`, `cseqP`, `celemP`, `cmembersP` at fuel `f`. -/
def CatP1 (I : Input) (f : Nat) : Prop :=
  ∀ (s : Shape) (addr len : Nat) (v : Val s) (ps : List Path) (π : Path),
    cpart I f s addr len = .ok (v, ps) →
    (cat I f s addr len π = .error .revert ↔ ps.any (Path.pre · π) = true)
def CatP2 (I : Input) (f : Nat) : Prop :=
  ∀ (e : Shape) (base i n : Nat) (vs : Seq e n) (ps : List Path),
    cseqP I f e base i n = .ok (vs, ps) → Heads ps i n ∧ ∀ (t : Nat) (π : Path),
    (catSeq I f e base i n t π = .error .revert ↔ ps.any (Path.pre · (t :: π)) = true)
def CatP3 (I : Input) (f : Nat) : Prop :=
  ∀ (e : Shape) (base src : Nat) (v : Val e) (ps : List Path) (π : Path),
    celemP I f e base src = .ok (v, ps) →
    (catElem I f e base src π = .error .revert ↔ ps.any (Path.pre · π) = true)
def CatP4 (I : Input) (f : Nat) : Prop :=
  ∀ (ms : List Shape) (base pos j : Nat) (vs : Vals ms) (ps : List Path),
    cmembersP I f ms base pos j = .ok (vs, ps) → Heads ps j ms.length ∧ ∀ (t : Nat) (π : Path),
    (catMembers I f ms base pos j t π = .error .revert ↔ ps.any (Path.pre · (t :: π)) = true)

theorem cat_step1 (I : Input) (f : Nat) (ih2 : CatP2 I f) (ih4 : CatP4 I f) : CatP1 I (f + 1) := by
  intro s addr len v ps π h
  cases s with
  | word k =>
    rw [cpart] at h
    rw [cat]
    by_cases hk : k.valid (load I.data addr) = true
    · rw [dif_pos hk] at h
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨_, rfl⟩ := h
      rw [if_pos hk]
      simp only [List.any_nil, Bool.false_eq_true, iff_false]
      split
      · exact fun h => Except.noConfusion h
      · exact fun h => Except.noConfusion h fun h => Fail.noConfusion h
    · rw [dif_neg hk] at h
      rw [if_neg hk]
      unfold miss at h
      split at h
      · simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨_, rfl⟩ := h
        simp only [List.any_cons, Path.pre, List.any_nil, Bool.or_false]
      · cases h
  | bytes =>
    rw [cpart] at h
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨_, rfl⟩ := h
    rw [cat]
    simp only [List.any_nil, Bool.false_eq_true, iff_false]
    exact catBytes_ne len π
  | array e =>
    rw [cpart] at h
    rcases hs : cseqP I f e addr 0 len with _ | ⟨xs, qs⟩ <;> rw [hs] at h
    · cases h
    · simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨_, rfl⟩ := h
      obtain ⟨hh, hi⟩ := ih2 e addr 0 len xs qs hs
      cases π with
      | nil =>
        rw [cat, any_pre_nil qs (fun x hx => (hh x hx).elim fun j ⟨r, e, _⟩ => ⟨j, r, e⟩)]
        exact ⟨fun h => Except.noConfusion h, fun h => Bool.noConfusion h⟩
      | cons i π => rw [cat]; exact hi i π
  | fixed e n =>
    rw [cpart] at h
    rcases hs : cseqP I f e addr 0 n with _ | ⟨xs, qs⟩ <;> rw [hs] at h
    · cases h
    · simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨_, rfl⟩ := h
      obtain ⟨hh, hi⟩ := ih2 e addr 0 n xs qs hs
      cases π with
      | nil =>
        rw [cat, any_pre_nil qs (fun x hx => (hh x hx).elim fun j ⟨r, e, _⟩ => ⟨j, r, e⟩)]
        exact ⟨fun h => Except.noConfusion h, fun h => Bool.noConfusion h⟩
      | cons i π => rw [cat]; exact hi i π
  | tuple ms =>
    rw [cpart] at h
    rcases hs : cmembersP I f ms addr 0 0 with _ | ⟨xs, qs⟩ <;> rw [hs] at h
    · cases h
    · simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨_, rfl⟩ := h
      obtain ⟨hh, hi⟩ := ih4 ms addr 0 0 xs qs hs
      cases π with
      | nil =>
        rw [cat, any_pre_nil qs (fun x hx => (hh x hx).elim fun j ⟨r, e, _⟩ => ⟨j, r, e⟩)]
        exact ⟨fun h => Except.noConfusion h, fun h => Bool.noConfusion h⟩
      | cons i π => rw [cat]; exact hi i π

theorem cat_step2 (I : Input) (f : Nat) (ih2 : CatP2 I f) (ih3 : CatP3 I f) : CatP2 I (f + 1) := by
  intro e base i n vs ps h
  cases n with
  | zero =>
    simp only [cseqP, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨_, rfl⟩ := h
    refine ⟨fun x hx => (by cases hx), fun t π => ?_⟩
    simp only [catSeq, List.any_nil, Bool.false_eq_true, iff_false]
    exact fun h => Except.noConfusion h fun h => Fail.noConfusion h
  | succ n =>
    rw [cseqP] at h
    rcases h1 : celemP I f e base (wrap (base + i * e.headSize)) with _ | ⟨v, p⟩ <;>
      rw [h1] at h
    · cases h
    rcases h2 : cseqP I f e base (i + 1) n with _ | ⟨vs', q⟩ <;> rw [h2] at h
    · cases h
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨_, rfl⟩ := h
    obtain ⟨hq, hiq⟩ := ih2 e base (i + 1) n vs' q h2
    refine ⟨heads_seq hq, fun t π => ?_⟩
    rw [catSeq, List.any_append, any_pre_map]
    by_cases ht : t = i
    · subst ht
      rw [if_pos rfl, any_pre_heads q t π
        (fun x hx => (hq x hx).elim fun j ⟨r, e, h1, _⟩ => ⟨j, r, e, by omega⟩)]
      simp only [decide_true, Bool.true_and, Bool.or_false]
      exact ih3 e base _ v p π h1
    · have : decide (i = t) = false := decide_eq_false fun h => ht h.symm
      rw [if_neg ht, this, Bool.false_and, Bool.false_or]
      exact hiq t π

theorem cat_step3 (I : Input) (f : Nat) (ih1 : CatP1 I f) : CatP3 I (f + 1) := by
  intro e base src v ps π h
  rw [celemP] at h
  rw [catElem]
  by_cases hd : e.dynamic = true
  · rw [if_pos hd] at h ⊢
    cases ht : tailRef I e base src with
    | ok r =>
      rw [ht] at h
      have h' : cpart I f e r.1 r.2 = .ok (v, ps) := h
      show cat I f e r.1 r.2 π = .error .revert ↔ _
      exact ih1 e r.1 r.2 v ps π h'
    | error x =>
      have hx := tailRef_error ht
      subst hx
      rw [ht] at h
      have h' : miss e = .ok (v, ps) := h
      show (Except.error Fail.revert : Except Fail Unit) = .error .revert ↔ _
      unfold miss at h'
      cases hm : e.dflt? with
      | none => rw [hm] at h'; exact Except.noConfusion h'
      | some d =>
        rw [hm] at h'
        have : ps = [[]] := (Prod.mk.inj (Except.ok.inj h')).2.symm
        subst this
        exact ⟨fun _ => rfl, fun _ => rfl⟩
  · rw [if_neg hd] at h ⊢
    exact ih1 e src 0 v ps π h

theorem cat_step4 (I : Input) (f : Nat) (ih3 : CatP3 I f) (ih4 : CatP4 I f) : CatP4 I (f + 1) := by
  intro ms base pos j vs ps h
  cases ms with
  | nil =>
    simp only [cmembersP, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨_, rfl⟩ := h
    refine ⟨fun x hx => (by cases hx), fun t π => ?_⟩
    simp only [catMembers, List.any_nil, Bool.false_eq_true, iff_false]
    exact fun h => Except.noConfusion h fun h => Fail.noConfusion h
  | cons m ms =>
    rw [cmembersP] at h
    rcases h1 : celemP I f m base (wrap (base + pos)) with _ | ⟨v, p⟩ <;> rw [h1] at h
    · cases h
    rcases h2 : cmembersP I f ms base (pos + m.headSize) (j + 1) with _ | ⟨vs', q⟩ <;>
      rw [h2] at h
    · cases h
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨_, rfl⟩ := h
    obtain ⟨hq, hiq⟩ := ih4 ms base (pos + m.headSize) (j + 1) vs' q h2
    refine ⟨heads_seq hq, fun t π => ?_⟩
    rw [catMembers, List.any_append, any_pre_map]
    by_cases ht : t = j
    · subst ht
      rw [if_pos rfl, any_pre_heads q t π
        (fun x hx => (hq x hx).elim fun j ⟨r, e, h1, _⟩ => ⟨j, r, e, by omega⟩)]
      simp only [decide_true, Bool.true_and, Bool.or_false]
      exact ih3 m base _ v p π h1
    · have : decide (j = t) = false := decide_eq_false fun h => ht h.symm
      rw [if_neg ht, this, Bool.false_and, Bool.false_or]
      exact hiq t π

/-- **Access agreement**, for the four mutually recursive readers at once. -/
theorem cat_cpart_all (I : Input) : ∀ f : Nat,
    (∀ (s : Shape) (addr len : Nat) (v : Val s) (ps : List Path) (π : Path),
      cpart I f s addr len = .ok (v, ps) →
      (cat I f s addr len π = .error .revert ↔ ps.any (Path.pre · π) = true)) ∧
    (∀ (e : Shape) (base i n : Nat) (vs : Seq e n) (ps : List Path),
      cseqP I f e base i n = .ok (vs, ps) → Heads ps i n ∧ ∀ (t : Nat) (π : Path),
      (catSeq I f e base i n t π = .error .revert ↔ ps.any (Path.pre · (t :: π)) = true)) ∧
    (∀ (e : Shape) (base src : Nat) (v : Val e) (ps : List Path) (π : Path),
      celemP I f e base src = .ok (v, ps) →
      (catElem I f e base src π = .error .revert ↔ ps.any (Path.pre · π) = true)) ∧
    (∀ (ms : List Shape) (base pos j : Nat) (vs : Vals ms) (ps : List Path),
      cmembersP I f ms base pos j = .ok (vs, ps) → Heads ps j ms.length ∧ ∀ (t : Nat) (π : Path),
      (catMembers I f ms base pos j t π = .error .revert ↔ ps.any (Path.pre · (t :: π)) = true)) := by
  intro f
  induction f with
  | zero =>
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro s addr len v ps π h; simp only [cpart] at h; cases h
    · intro e base i n vs ps h
      cases n with
      | zero =>
        simp only [cseqP, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨_, rfl⟩ := h
        refine ⟨fun x hx => (by cases hx), fun t π => ?_⟩
        simp only [catSeq, List.any_nil, Bool.false_eq_true, iff_false]
        exact fun h => Except.noConfusion h fun h => Fail.noConfusion h
      | succ n => simp only [cseqP] at h; cases h
    · intro e base src v ps π h; simp only [celemP] at h; cases h
    · intro ms base pos j vs ps h
      cases ms with
      | nil =>
        simp only [cmembersP, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨_, rfl⟩ := h
        refine ⟨fun x hx => (by cases hx), fun t π => ?_⟩
        simp only [catMembers, List.any_nil, Bool.false_eq_true, iff_false]
        exact fun h => Except.noConfusion h fun h => Fail.noConfusion h
      | cons m ms => simp only [cmembersP] at h; cases h
  | succ f ih =>
    obtain ⟨ih1, ih2, ih3, ih4⟩ := ih
    exact ⟨cat_step1 I f ih2 ih4, cat_step2 I f ih2 ih3, cat_step3 I f ih1, cat_step4 I f ih3 ih4⟩

/-- **Access agreement.** For a reference the recording reader reads
(`cpart … = .ok (v, ps)`), one access along any path `π` fails with an empty
revert exactly when a recorded path is a prefix of `π`. An access that does
not revert succeeds or leaves the model (`Panic(0x32)` out of range, fuel). -/
theorem cat_cpart {I : Input} {f : Nat} {s : Shape} {addr len : Nat} {v : Val s} {ps : List Path}
    (h : cpart I f s addr len = .ok (v, ps)) (π : Path) :
    cat I f s addr len π = .error .revert ↔ ps.any (Path.pre · π) = true :=
  (cat_cpart_all I f).1 s addr len v ps π h

/-! ### The verdict with access-time failures -/

/-- How the adapter treats an input when some calldata parameters are read
at access time (`acc k`: the body's reads of parameter `k` are each guarded
as solc's accessors check them, `Tools/UpstreamEntry.lean`). -/
inductive VerdictA (ps : List Param) where
  /-- solc reverts with empty data before the body. -/
  | revert
  /-- The body runs on these values; parameter `k`'s accesses below the
  recorded paths `fails[k]` revert (empty for every other parameter). -/
  | run (vs : Vals (ps.map Param.shape)) (fails : List (List Path))
  /-- Outside the proved fragment. -/
  | blocked (reason : String)

/-- `bodyValues`, except that a calldata parameter `k` with `acc k` whose
eager copy fails takes the recording reader's value and failing paths
(`cpart`). Every other parameter is treated exactly as `bodyValues` treats
it (`bodyValuesA_off`). -/
def bodyValuesA (I : Input) (f : Nat) (acc : Nat → Bool) : (ps : List Param) → Entries ps → Nat → Nat →
    Except String (Vals (ps.map Param.shape) × List (List Path))
  | [], .nil, _, _ => .ok (.nil, [])
  | p :: ps, .cons e es, pos, k => do
    let (v, q) ← match e with
      | .val v => pure (v, [])
      | .ref addr len =>
        match eager I f p.shape pos with
        | .ok v => pure (v, [])
        | .error .fuel => throw "ABI decoder fuel exhausted"
        | .error _ =>
          if acc k then
            match cpart I f p.shape addr len with
            | .ok r => pure r
            | .error .fuel => throw "calldata element validation exhausted fuel"
            | .error _ => throw "calldata element without a substitute value: outside the model"
          else
            match cvalRef I f p.shape addr len with
            | .ok v =>
              if p.readsOnly then pure (v, [])
              else throw "calldata layout accepted by lazy access but rejected by an eager copy needs calldata references in the source semantics"
            | .error .revert => throw "calldata element fails only on access: needs access-time calldata semantics"
            | .error _ => throw "calldata element validation exhausted fuel"
    let (vs, qs) ← bodyValuesA I f acc ps es (pos + p.shape.headSize) (k + 1)
    pure (.cons v vs, q :: qs)

def verdictA (I : Input) (f : Nat) (acc : Nat → Bool) (ps : List Param) : VerdictA ps :=
  match entry I f ps with
  | .error .revert => .revert
  | .error .panic => .blocked "possible Panic(0x41) allocation failure in memory decoding"
  | .error .fuel => .blocked "ABI decoder fuel exhausted"
  | .ok es =>
    match bodyValuesA I f acc ps es 0 0 with
    | .ok (vs, fs) => .run vs fs
    | .error r => .blocked r

/-- With no parameter read at access time, `bodyValuesA` is `bodyValues`
and records no path. -/
theorem bodyValuesA_off (I : Input) (f : Nat) : ∀ (ps : List Param) (es : Entries ps) (pos k : Nat),
    bodyValuesA I f (fun _ => false) ps es pos k =
      (bodyValues I f ps es pos).map (fun vs => (vs, ps.map fun _ => [])) := by
  intro ps
  induction ps with
  | nil => intro es pos k; cases es; rfl
  | cons p ps ih =>
    intro es pos k
    cases es with
    | cons e es =>
      simp only [bodyValuesA, bodyValues, Bool.false_eq_true, if_false, ih]
      cases e with
      | val v =>
        simp only [bind, Except.bind, pure, Except.pure, Except.map, List.map_cons]
        cases bodyValues I f ps es (pos + p.shape.headSize) <;> rfl
      | ref addr len =>
        cases eager I f p.shape pos with
        | ok v =>
          simp only [bind, Except.bind, pure, Except.pure, Except.map, List.map_cons]
          cases bodyValues I f ps es (pos + p.shape.headSize) <;> rfl
        | error x =>
          cases x with
          | fuel => rfl
          | revert | panic =>
            simp only
            cases cvalRef I f p.shape addr len with
            | ok v =>
              cases p.readsOnly
              · rfl
              · simp only [bind, Except.bind, pure, Except.pure, Except.map, List.map_cons, if_true]
                cases bodyValues I f ps es (pos + p.shape.headSize) <;> rfl
            | error y => cases y <;> rfl

/-- **Conservative extension.** With no parameter read at access time the
verdict is CF1's: the same revert, the same values (no recorded path), the
same refusals. -/
theorem verdictA_off (I : Input) (f : Nat) (ps : List Param) :
    verdictA I f (fun _ => false) ps = match verdict I f ps with
      | .revert => .revert
      | .run vs => .run vs (ps.map fun _ => [])
      | .blocked r => .blocked r := by
  unfold verdictA verdict
  cases entry I f ps with
  | error x => cases x <;> rfl
  | ok es =>
    simp only
    rw [bodyValuesA_off]
    cases bodyValues I f ps es 0 <;> rfl

/-- **Failure timing.** A certified revert is exactly an entry failure. -/
theorem verdictA_revert_iff (I : Input) (f : Nat) (acc : Nat → Bool) (ps : List Param) :
    verdictA I f acc ps = .revert ↔ entry I f ps = .error .revert := by
  constructor
  · intro h
    unfold verdictA at h
    split at h
    · assumption
    all_goals (try split at h) <;> simp_all
  · intro h
    simp only [verdictA, h]

/-- A body runs only after every entry check passed, on `bodyValuesA`'s
values. -/
theorem verdictA_run_entry {I : Input} {f : Nat} {acc : Nat → Bool} {ps : List Param}
    {vs : Vals (ps.map Param.shape)} {fs : List (List Path)}
    (h : verdictA I f acc ps = .run vs fs) :
    ∃ es, entry I f ps = .ok es ∧ bodyValuesA I f acc ps es 0 0 = .ok (vs, fs) := by
  unfold verdictA at h
  split at h <;> try simp at h
  rename_i es hes
  split at h
  · rename_i vs' fs' hv
    simp only [VerdictA.run.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨es, hes, hv⟩
  · simp at h

end Solidity.AbiEntry

/-- info: 'Solidity.AbiEntry.cpart_agree' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.AbiEntry.cpart_agree
/-- info: 'Solidity.AbiEntry.cpart_of_cval' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.AbiEntry.cpart_of_cval
/-- info: 'Solidity.AbiEntry.cat_cpart' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.AbiEntry.cat_cpart
/-- info: 'Solidity.AbiEntry.verdictA_off' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.AbiEntry.verdictA_off
/-- info: 'Solidity.AbiEntry.verdictA_revert_iff' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.AbiEntry.verdictA_revert_iff
/-- info: 'Solidity.AbiEntry.verdictA_run_entry' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.AbiEntry.verdictA_run_entry
