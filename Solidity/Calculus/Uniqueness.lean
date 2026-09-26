import Solidity.Calculus.Completeness

/-!
# At most one rule per statement, and where the table has more

`Taclet` is a `Prop`, so "one rule per statement" is a statement about
premises: two derivations of `s` leave the same premise.  For the table as
it is written that is **false**, and this file pins why before anyone relies
on it.  `Rules.lean` says a taclet is what is *sound*, not what *fires*: its
schema variables carry no side condition, so `nsp`, `nse`, `nmp`, `nadr`
and `e` range over simple parts too, and `sp`, `map`, `arr` over paths that
are not simple.  The naming convention of `RuleSyntax.lean` (`sp` simple,
`nsp` not) is read by `Stmt.step`, never by `Taclet`.  Five ways two rules
open on one statement, each a theorem below with its two premises:

* an unfold or capture rule takes a part that is already simple
  (`Taclet.overlap_ite`: `if (b) …` splits or captures `b`);
* a terminal rule takes a receiver that is not simple, and an unfold rule
  one that is (`Taclet.overlap_fieldRead`: `x = b.f;` for *every* `b`);
* a conditional written to storage is captured or lowered
  (`Taclet.overlap_ternaryWrite`);
* a copy between two storage members unfolds its target or its source
  (`Taclet.overlap_copyOrder`);
* a reference between two memory members, likewise
  (`Taclet.overlap_memRefOrder`).

The last three are the kernel-port Decisions row "Overlapping taclets",
whose side conditions (`Val.notTernary`, `Loc.isTarget`,
`MPath.isBindable`) the removed staging table carried and this one does not.

What does hold is uniqueness on the statements no two constructors share a
pattern for (`Stmt.oneRule`: declarations, `revert();`, a local assigned a
simple value, state variables read, copied and deleted whole, `v++`, …), and
there every derivation is `Stmt.step`'s (`Taclet.eq_step_of_oneRule`).
Uniqueness for every statement needs the side conditions in the
constructors, which is a change to `Rules.lean`, not a theorem here.
-/

namespace Solidity

variable {C : Contract} {k : Nat} {m : Modality}

/-! ## Where two rules fire -/

/-- `if (b) { … } else { … }` with `b` a local: `ifElseSplit` branches on it,
and `ifElseUnfold`, whose `nse` may be simple, captures it into
`bool se = b;` first. -/
theorem Taclet.overlap_ite (c : Simple C .bool) (thn els : Prog C) :
    ∃ p₁ p₂, Taclet C k m (.ite (.simple c) thn els) p₁ ∧
      Taclet C k m (.ite (.simple c) thn els) p₂ ∧ p₁ ≠ p₂ :=
  ⟨_, _, .ifElseSplit, .ifElseUnfold, nofun⟩

/-- The premise is not unique: some statement has two derivations with
different premises, `if (true) {} else {}` among them. -/
theorem Taclet.not_premise_unique :
    ¬ ∀ {C : Contract} {k : Nat} {m : Modality} {s : Stmt C} {p p' : Premise C},
      Taclet C k m s p → Taclet C k m s p' → p = p' := by
  intro h
  obtain ⟨_, _, d₁, d₂, hne⟩ :=
    Taclet.overlap_ite (C := default) (k := 0) (m := .box) (.bool true) [] []
  exact hne (h d₁ d₂)

/-- `x = b.f;`, whatever the receiver `b`: `storageFieldReadFind` reads it as
one update, and `storageFieldRead_unfold_rightFst` binds `b` to an alias
first.  With `b = alice` the unfold is not the rule that runs; with
`b = people[i]` the update is not. -/
theorem Taclet.overlap_fieldRead {s : Name} {p : PrimTy} (x : Var) (b : SPath C (.struct s))
    (f : Name) (hf : C.fieldType s f = some (.prim p)) :
    ∃ p₁ p₂, Taclet C k m (.assignLocal x (.read (.field b f hf))) p₁ ∧
      Taclet C k m (.assignLocal x (.read (.field b f hf))) p₂ ∧ p₁ ≠ p₂ :=
  ⟨_, _, .storageFieldReadFind,
    @Taclet.storageFieldRead_unfold_rightFst C k m _ (.local x) s b f hf, nofun⟩

/-- `b.f = c ? e₁ : e₂;` with `c` simple: `ternaryToIf` lowers it to
`if (c) { b.f = e₁; } else { b.f = e₂; }`, and `fieldWriteValueRhsCapture`
captures the whole conditional into `uint se = c ? e₁ : e₂;`. -/
theorem Taclet.overlap_ternaryWrite {s : Name} {p : PrimTy} (b : SPath C (.struct s)) (f : Name)
    (hf : C.fieldType s f = some (.prim p)) (c : Simple C .bool) (e₁ e₂ : Val C p) :
    ∃ p₁ p₂, Taclet C k m (.assign (.field b f hf) (.val (.ternary (.simple c) e₁ e₂))) p₁ ∧
      Taclet C k m (.assign (.field b f hf) (.val (.ternary (.simple c) e₁ e₂))) p₂ ∧
      p₁ ≠ p₂ :=
  ⟨_, _, @Taclet.ternaryToIf C k m p (.store (.field b f hf)) c e₁ e₂,
    .fieldWriteValueRhsCapture, by simp⟩

/-- `l.f = l'.g;`, a copy between two storage members whose receivers are
locations (`folks[1].account = folks[2].account;`):
`storageFieldWriteStorageRef_unfold_leftFst` binds the target's receiver
`folks[1]` first, `storageFieldRead_unfold_rightFst` the source's
`folks[2]`. -/
theorem Taclet.overlap_copyOrder {s s' : Name} {R : RefTy} (l : Loc C (.struct s))
    (l' : Loc C (.struct s')) (f g : Name) (hf : C.fieldType s f = some (.ref R))
    (hg : C.fieldType s' g = some (.ref R)) (hm : (Ty.ref R).mapFree = true) :
    ∃ p₁ p₂, Taclet C k m (.assign (.field (.loc l) f hf) (.copy (.loc (.field (.loc l') g hg)) hm)) p₁ ∧
      Taclet C k m (.assign (.field (.loc l) f hf) (.copy (.loc (.field (.loc l') g hg)) hm)) p₂ ∧
      p₁ ≠ p₂ :=
  ⟨_, _, .storageFieldWriteStorageRef_unfold_leftFst,
    @Taclet.storageFieldRead_unfold_rightFst C k m _ (.copy (.field (.loc l) f hf) hm) s' (.loc l') g hg,
    by simp [Hole.fill]⟩

/-- `ml.f = ml'.g;`, a reference between two memory members whose receivers
are locations (`m.inner.acc = n.inner.acc;`): `memoryFieldWrite_unfold_leftFst`
binds the target's receiver `m.inner` first, `memoryFieldRead_unfold_rightFst`
the source's `n.inner`. -/
theorem Taclet.overlap_memRefOrder {s s' : Name} {R : RefTy} (ml : MLoc C (.struct s))
    (ml' : MLoc C (.struct s')) (f g : Name) (hf : C.fieldType s f = some (.ref R))
    (hg : C.fieldType s' g = some (.ref R)) :
    ∃ p₁ p₂, Taclet C k m (.assignMem (.field (.loc ml) f hf) (.ref (.loc (.field (.loc ml') g hg)))) p₁ ∧
      Taclet C k m (.assignMem (.field (.loc ml) f hf) (.ref (.loc (.field (.loc ml') g hg)))) p₂ ∧
      p₁ ≠ p₂ :=
  ⟨_, _, .memoryFieldWrite_unfold_leftFst,
    @Taclet.memoryFieldRead_unfold_rightFst C k m _ (.write (.field (.loc ml) f hf)) s' (.loc ml') g hg,
    by simp [MHole.fill]⟩

/-! ## Where one rule fires -/

/-- `total`: a state variable. -/
def Loc.isRoot {T : Ty} : Loc C T → Bool
  | .root .. => true
  | _ => false

/-- `x = total;`: a state variable read. -/
def Val.readsRoot {p : PrimTy} : Val C p → Bool
  | .read l => l.isRoot
  | _ => false

/-- `alice = bob;`: a copy from an alias or a state variable. -/
def Src.copiesSimple {T : Ty} : Src C T → Bool
  | .copy sp _ => sp.isSimple
  | _ => false

/-- `x++`, `total++`: a target with no receiver. -/
def OpLoc.isLocalOrRoot {p : PrimTy} : OpLoc C p → Bool
  | .local _ | .root .. => true
  | _ => false

/-- The statements exactly one constructor matches: declarations,
`revert();`, `x = se;`, `x = total;`, `lsv = sp;` and `lsv = persons;`,
`m = n;`, `total = sp;` and `alice = bob;`, `alice = m;`, `delete total;`,
`x++;`, `total++;`, and `y = l++;` (whose receiver is simple by its type). -/
def Stmt.oneRule : Stmt C → Bool
  | .declLocal .. | .declStorage .. | .declMem .. | .revert | .assignIncDec .. => true
  | .assignLocal _ v => v.isSimple || v.readsRoot
  | .rebind _ (.path sp) => sp.isSimple
  | .rebindMem _ (.alias mp) => mp.isSimple
  | .assign l r => l.isRoot && r.copiesSimple
  | .assignFromMem l _ | .delete l => l.isRoot
  | .incDec _ _ l => l.isLocalOrRoot
  | _ => false

/-- On those statements every derivation is `Stmt.step`'s: `uint x = 1;`
has only `localValueDeclInitDrop`, and `alice = bob;` only
`storageRootWriteCopySource`. -/
theorem Taclet.eq_step_of_oneRule {s : Stmt C} {p : Premise C} (d : Taclet C k m s p)
    (h : s.oneRule = true) : p = (s.step k m).premise := by
  cases d <;> (try cases ‹Hole _ _›) <;> (try cases ‹MHole _ _›) <;> (try cases ‹VHole _ _›) <;>
    simp_all [Stmt.oneRule, Hole.fill, MHole.fill, VHole.fill, Val.isSimple, Val.readsRoot,
      SPath.isSimple, MPath.isSimple, Loc.isRoot, Src.copiesSimple, OpLoc.isLocalOrRoot] <;>
    first
      | rfl
      -- `lsv = sp;`, `gsp = sp;`: `Stmt.step` asks which path `sp` is
      | (cases ‹SPath _ _› <;> (try cases ‹Loc _ _›) <;> simp_all <;> rfl)

/-- Two derivations of `x = y;` leave the same premise, `{ x := y } ⟨[ ]⟩`. -/
theorem Taclet.premise_unique_of_oneRule {s : Stmt C} {p p' : Premise C}
    (d : Taclet C k m s p) (d' : Taclet C k m s p') (h : s.oneRule = true) : p = p' := by
  rw [d.eq_step_of_oneRule h, d'.eq_step_of_oneRule h]

end Solidity
