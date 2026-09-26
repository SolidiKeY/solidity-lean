import Solidity.Calculus.Notation

/-!
# Closing the first-order goal: `sol_close`

`sol_symex` leaves `{U₁} … {Uₙ} φ` with no modality in it.  Its updates are
not rewritten away, as mini-solkey's `Ch14_Updates` does: a term here *is* a
call of the interpreter (`Term.eval`, `STerm.eval`), so applying an update
in an arbitrary state `σ` is running it, and what remains is a statement
about what `saveStorage`, `findStorage` and `getEnv` return on a `σ` nobody
knows.  `sol_close` proves that statement, in two stages.

**Weakest preconditions.**  `Modality.wp m x P` is `P` of what `x` returns,
or `m.onHalt` when it halts; `Modality.after` is its instance at `State`.
Pushed through the binds of the evaluators (`Modality.wp_bind`, and one
equation per constructor below), it turns the goal into a nest of `∀ τ,
x = .ok τ → …` (the box) or `∃ τ, x = .ok τ ∧ …` (the diamond).  A
`split` on the unfolded `match`es does not get there: it splits the
outermost one only, and leaves the evaluator's inner matches in
hypotheses.  Under the box, a write is named on the spot
(`Modality.wp_box_saveStorage`) together with everything the rest of the
goal needs of its result: the path written reads back, a path apart from
it (`Diverge`) reads as before, the locals are untouched.

**Read after write.**  A contextual `simp` then rewrites every read with
those facts, discharging the apartness of concrete paths by computation
and that of symbolic keys (`balances[k]`, `balances[j]`) by a hypothesis
`k != j` of the formula; `omega` or `grind` finishes the arithmetic.
This is mini-solkey's `Ch07` `sol_close` with `findOnSave` and
`findOnSaveDifferent` as facts about one state, rather than rewrite rules
about `save` terms.  Every step is a `simp` lemma or a hypothesis:
nothing evaluated is trusted, the kernel checks the proof.

What does not close, and why:

* a write under the diamond: `⊨` quantifies over every state, including
  those without `alice`, where `alice.age = 1;` is stuck, so
  `⟨ alice.age = 1; ⟩ true` is not valid.  Write the box, or put the
  well-formedness of the storage in the premise;
* a read above or below a write (`alice = bob; uint y = alice.age;`):
  `Diverge` covers only paths that part ways, and the four-way comparison
  of mini-solkey's `Ch15_Decide` is not ported;
* two symbolic keys the formula does not tell apart: there is no case
  split on `k = j`;
* `push`, `pop`, a memory term, `transfer`: they have no equations below,
  and fall to `grind`.
-/

namespace Solidity

open Semantics SemanticsProperties

namespace Close

/-! ## Paths that part ways -/

/-- Two storage paths part ways: at some position their segments differ.
`alice.age` and `alice.account.balance` do (`age` against `account`);
`alice` and `alice.age` do not — one is a prefix of the other. -/
def Diverge : List Seg → List Seg → Prop
  | a :: p, b :: q => a ≠ b ∨ Diverge p q
  | _, _ => False

/-- `balances[k]` and `balances[j]` part ways when `k ≠ j`, or later on. -/
@[simp] theorem diverge_cons {a b : Seg} {p q : List Seg} :
    Diverge (a :: p) (b :: q) ↔ a ≠ b ∨ Diverge p q := Iff.rfl

/-- `diverge_cons` as `sol_close` uses it, with the disequation both ways
round: a premise `k != j` then discharges the frame of `balances[k]`
against `balances[j]` whichever of the two was written first. -/
theorem diverge_cons' {a b : Seg} {p q : List Seg} :
    Diverge (a :: p) (b :: q) ↔ (¬ a = b ∨ ¬ b = a) ∨ Diverge p q := by
  simp only [diverge_cons, ne_eq]
  exact ⟨fun h => h.elim (fun h => .inl (.inl h)) .inr,
    fun h => h.elim (fun h => .inl (h.elim id (fun h' e => h' e.symm))) .inr⟩

/-- A root does not part ways with anything below it: `alice` against
`alice.age`. -/
@[simp] theorem not_diverge_nil_left {q : List Seg} : ¬ Diverge [] q := id

/-- Nor does a path with its root: `alice.age` against `alice`. -/
@[simp] theorem not_diverge_nil_right {p : List Seg} : ¬ Diverge p [] := by
  cases p <;> exact id

/-! ## Storage: read after write -/

/-- **Frame, in a tree**: a write leaves every path apart from it as it was.
After `alice.age = 10;` the tree of `alice` reads the same at `account`;
after `values[0] = 7;` the array reads the same at `[1]` and at `length`;
after `balances[1] = 5;` the mapping reads the same at `[2]`. -/
theorem find_save_diverge {new : SVal} :
    ∀ {p q : List Seg} {old upd : SVal}, Diverge p q → old.save p new = .ok upd →
      upd.find q = old.find q
  | [], _, _, _, h, _ => h.elim
  | _ :: _, [], _, _, h, _ => (not_diverge_nil_right h).elim
  | a :: p, b :: q, old, upd, h, hs => by
    cases old with
    | prim v => cases a <;> simp [SVal.save] at hs
    | struct fields =>
      cases a with
      | «at» i => simp [SVal.save] at hs
      | field n =>
        simp only [SVal.save] at hs
        split at hs
        · rename_i old' hl
          cases hu : old'.save p new with
          | error e => simp [hu, bind, Except.bind] at hs
          | ok u =>
            simp only [hu, bind, Except.bind, Except.ok.injEq] at hs
            subst hs
            cases b with
            | «at» j => simp [SVal.find]
            | field m =>
              by_cases hnm : m = n
              · subst hnm
                have hd : Diverge p q := by simpa using h
                simp [SVal.find, hl, find_save_diverge hd hu]
              · simp [SVal.find, lookupBy_setBy_ne hnm]
        · simp at hs
    | array elems shadow =>
      cases a with
      | field n => simp [SVal.save] at hs
      | «at» i =>
        simp only [SVal.save] at hs
        split at hs
        · rename_i hi
          cases hu : (elems[i.toNat]'hi.2).save p new with
          | error e => simp [List.get_eq_getElem, hu, bind, Except.bind] at hs
          | ok u =>
            simp only [List.get_eq_getElem, hu, bind, Except.bind, Except.ok.injEq] at hs
            subst hs
            cases b with
            | field m =>
              -- `length` reads the extent, which a write in bounds keeps
              by_cases hm : m = "length"
              · subst hm; simp [SVal.find]
              · simp [SVal.find]
            | «at» j =>
              by_cases hij : j = i
              · subst hij
                have hd : Diverge p q := by simpa using h
                simp [SVal.find, hi, find_save_diverge hd hu]
              · by_cases hj : 0 ≤ j ∧ j.toNat < elems.length
                · have hne : i.toNat ≠ j.toNat := by omega
                  simp [SVal.find, hj, List.getElem_set_ne hne]
                · simp [SVal.find, hj]
        · simp at hs
    | map entries dflt =>
      cases a with
      | field n => simp [SVal.save] at hs
      | «at» i =>
        simp only [SVal.save] at hs
        -- the slot written: the entry at `i`, or the default when there is none
        obtain ⟨old', hold, hfind⟩ : ∃ old' : SVal, (old'.save p new >>= fun u =>
            Except.ok (SVal.map (setBy i u entries) dflt)) = Except.ok upd ∧
            (SVal.map entries dflt).find (.at i :: q) = old'.find q := by
          split at hs <;> rename_i hl <;> exact ⟨_, hs, by simp [SVal.find, hl]⟩
        cases hu : old'.save p new with
        | error e => simp [hu, bind, Except.bind] at hold
        | ok u =>
          simp only [hu, bind, Except.bind, Except.ok.injEq] at hold
          subst hold
          cases b with
          | field m => simp [SVal.find]
          | «at» j =>
            by_cases hij : j = i
            · subst hij
              have hd : Diverge p q := by simpa using h
              simp [SVal.find] at hfind ⊢
              rw [hfind, find_save_diverge hd hu]
            · simp [SVal.find, lookupBy_setBy_ne hij]

/-- **Frame, in the storage**: `alice.age = 10;` leaves `bob.age` (another
root) and `alice.account` (a path apart) as they were. -/
theorem findStorage_saveStorage_apart {σ τ : State} {r r' : Name} {p q : List Seg}
    {v : SVal} (h : σ.saveStorage r p v = .ok τ) (hd : r' ≠ r ∨ Diverge p q) :
    τ.findStorage r' q = σ.findStorage r' q := by
  unfold State.saveStorage at h
  split at h
  · rename_i old hl
    cases hu : old.save p v with
    | error e => simp [hu, bind, Except.bind] at h
    | ok u =>
      simp only [hu, bind, Except.bind, Except.ok.injEq] at h
      subst h
      by_cases hr : r' = r
      · subst hr
        have hd : Diverge p q := hd.resolve_left (· rfl)
        simp [State.findStorage, hl, find_save_diverge hd hu]
      · simp [State.findStorage, lookupBy_setBy_ne hr]
  · simp at h

/-- A write changes the storage only: the state an update `{storage :=
save(storage, alice.age, 10)}` builds from `σ` is the one the write returns. -/
theorem saveStorage_restore {σ τ : State} {r : Name} {p : List Seg} {v : SVal}
    (h : σ.saveStorage r p v = .ok τ) : { σ with storage := τ.storage } = τ := by
  obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := State.saveStorage_frame h
  cases τ; simp_all

/-- A write leaves the locals alone: `x` reads the same after
`alice.age = 10;`. -/
theorem getEnv_saveStorage {σ τ : State} {r : Name} {p : List Seg} {v : SVal}
    (h : σ.saveStorage r p v = .ok τ) (x : Var) : τ.getEnv x = σ.getEnv x := by
  simp [State.getEnv, (State.saveStorage_frame h).2.2.1]

end Close

/-! ## Weakest preconditions -/

/-- `P` of what `x` returns, or `m.onHalt` when it halts: under the box
`[ alice.age = 1; ] φ` holds of a state without `alice`, under the diamond
it does not. -/
def Modality.wp {α : Type} (m : Modality) (x : Res α) (P : α → Prop) : Prop :=
  match x with
  | .ok a => P a
  | .error _ => m.onHalt

section WP

variable {α β : Type} {m : Modality}

/-- `Modality.after` is `wp` at `State`: `⟨ x = 1; ⟩ x == 1` holds where
running `x = 1;` returns a state with `x == 1`. -/
theorem Modality.after_eq_wp (p : State → Prop) (r : Res State) : m.after p r = m.wp r p := by
  cases r <;> rfl

/-- A run that returns: `uint x = 10;` leaves `x == 10` to check. -/
@[simp] theorem Modality.wp_ok {a : α} {P : α → Prop} : m.wp (.ok a) P ↔ P a := Iff.rfl

/-- `wp_ok` for `pure`. -/
@[simp] theorem Modality.wp_pure {a : α} {P : α → Prop} : m.wp (pure a) P ↔ P a := Iff.rfl

/-- A run that halts: `revert();` proves every box formula, no diamond one. -/
@[simp] theorem Modality.wp_error {e : Halt} {P : α → Prop} : m.wp (.error e) P ↔ m.onHalt :=
  Iff.rfl

/-- Under the box a halt is fine: `[ revert(); ] false`. -/
@[simp] theorem Modality.onHalt_box : Modality.box.onHalt = True := rfl

/-- Under the diamond it is not: `⟨ revert(); ⟩ true` fails. -/
@[simp] theorem Modality.onHalt_diamond : Modality.diamond.onHalt = False := rfl

/-- Sequencing: `y = x + 1` evaluates `x`, then adds, then range-checks, and
the postcondition is asked of the last. -/
theorem Modality.wp_bind {x : Res α} {f : α → Res β} {P : β → Prop} :
    m.wp (x >>= f) P ↔ m.wp x (fun a => m.wp (f a) P) := by
  cases x <;> exact Iff.rfl

/-- A range check: `y = x + 1` at `uint` returns `x + 1` when it is below
`2²⁵⁶`, and reverts otherwise. -/
theorem Modality.wp_ite {c : Prop} [Decidable c] {x y : Res α} {P : α → Prop} :
    m.wp (if c then x else y) P ↔ (c → m.wp x P) ∧ (¬ c → m.wp y P) := by
  by_cases h : c <;> simp [h]

/-- The box, of a step nothing is known about: whatever it returns. -/
theorem Modality.wp_box {x : Res α} {P : α → Prop} :
    Modality.box.wp x P ↔ ∀ a, x = .ok a → P a := by
  cases x <;> simp [Modality.wp, Modality.onHalt]

/-- The diamond: it returns, and what it returns satisfies `P`. -/
theorem Modality.wp_diamond {x : Res α} {P : α → Prop} :
    Modality.diamond.wp x P ↔ ∃ a, x = .ok a ∧ P a := by
  cases x <;> simp [Modality.wp, Modality.onHalt]

/-- **A write under the box**, named with what is known of its result: in
`[ alice.age = 10; bob.age = 20; ] alice.age == 10`, the state `τ` after
the first write reads `10` at `alice.age`, reads as `σ` does at `bob` and
at `alice.account`, and has the locals of `σ`. -/
theorem Modality.wp_box_saveStorage {σ : State} {r : Name} {p : List Seg} {v : SVal}
    {P : State → Prop} :
    Modality.box.wp (σ.saveStorage r p v) P ↔
      ∀ τ, σ.saveStorage r p v = .ok τ → τ.findStorage r p = .ok v →
        (∀ r' q, r' ≠ r ∨ Close.Diverge p q → τ.findStorage r' q = σ.findStorage r' q) →
        (∀ x, τ.getEnv x = σ.getEnv x) → { σ with storage := τ.storage } = τ → P τ := by
  rw [Modality.wp_box]
  exact ⟨fun h τ hs _ _ _ _ => h τ hs, fun h τ hs =>
    h τ hs (State.findStorage_saveStorage_same hs)
      (fun _ _ hd => Close.findStorage_saveStorage_apart hs hd)
      (Close.getEnv_saveStorage hs) (Close.saveStorage_restore hs)⟩

end WP

namespace Close

/-! ## Evaluation, one constructor at a time

The evaluators' own equations end in `match`es on a binding or a pair,
which `simp` cannot see through while the scrutinee is unknown.  These
restate them as binds of named functions, so that `Modality.wp_bind`
applies and the scrutinee is named first. -/

/-- The value a local holds: `x` after `uint x = 10;` is `10`; an alias or
a memory local has none. -/
def bindingVal : Binding → Res Value
  | .val v => .ok v
  | .spath .. | .mref _ => .error .stuck

/-- The path an alias holds: `p` after `Person storage p = alice;` is
`alice`. -/
def bindingPath : Binding → Res (Name × List Seg)
  | .spath r segs => .ok (r, segs)
  | .val _ | .mref _ => .error .stuck

/-- `x` bound to `10` reads `10`. -/
@[simp] theorem bindingVal_val (v : Value) : bindingVal (.val v) = .ok v := rfl
/-- `p` bound to `alice.account` reads that path. -/
@[simp] theorem bindingPath_spath (r : Name) (segs : List Seg) :
    bindingPath (.spath r segs) = .ok (r, segs) := rfl
/-- A local read as a value was bound to one: `a == 1` says `a` holds `1`. -/
@[simp] theorem bindingVal_eq_ok {b : Binding} {v : Value} :
    bindingVal b = .ok v ↔ b = .val v := by
  cases b <;> simp [bindingVal]
/-- An index read as an integer is one: `balances[k]` needs `k` a `uint`. -/
@[simp] theorem asInt_eq_ok {v : Value} {i : Int} : v.asInt = .ok i ↔ v = .int i := by
  cases v <;> simp [Value.asInt]
/-- `alice.age = 10;` stores the word `10`. -/
@[simp] theorem toSVal_int (v : Int) : Value.toSVal (.int v) = .int v := rfl
/-- `flags[k] = true;` stores the word `true`. -/
@[simp] theorem toSVal_bool (b : Bool) : Value.toSVal (.bool b) = .bool b := rfl
/-- Reading the word `10` gives `10`. -/
@[simp] theorem asValue_int (v : Int) : (SVal.int v).asValue = .ok (.int v) := rfl
/-- Reading the word `true` gives `true`. -/
@[simp] theorem asValue_bool (b : Bool) : (SVal.bool b).asValue = .ok (.bool b) := rfl
/-- `delete alice.age;` leaves `0`. -/
@[simp] theorem defaultOf_int (v : Int) : (SVal.int v).defaultOf = .int 0 := rfl
/-- `delete flags[k];` leaves `false`. -/
@[simp] theorem defaultOf_bool (b : Bool) : (SVal.bool b).defaultOf = .bool false := rfl
/-- The index `1` of `values[1]` is the integer `1`. -/
@[simp] theorem asInt_int (v : Int) : Value.asInt (.int v) = .ok v := rfl
/-- Binding a local does not touch the storage: after `uint y = 1;`,
`alice.age` reads as before. -/
@[simp] theorem findStorage_setEnv (σ : State) (x : Var) (b : Binding) (r : Name)
    (segs : List Seg) : (σ.setEnv x b).findStorage r segs = σ.findStorage r segs := rfl

/-- `p.age`, with `p` an alias, is the path `p` holds, then `age`. -/
theorem aliasPath_eq (σ : State) (x : Var) : aliasPath σ x = σ.getEnv x >>= bindingPath := by
  simp only [aliasPath, bind, Except.bind]
  cases σ.getEnv x with
  | error _ => rfl
  | ok b => cases b <;> rfl

/-- Every operator but `&&` and `||` reads both operands: `x + 1` reads `x`,
then `1`, adds, and range-checks the sum. -/
theorem evalBinop_strict {op : BinOp} (h₁ : op ≠ .and) (h₂ : op ≠ .or) (p : PrimTy) (lv : Value)
    (b : Res Value) :
    evalBinop op p lv b =
      b >>= fun rv => applyBinOp op lv rv >>= checkArith (op.retTy (.prim p)) := by
  cases op <;> first | exact absurd rfl h₁ | exact absurd rfl h₂ | rfl

section Eval

variable {C : Contract} (σ : State)

/-- `10` is `10`. -/
theorem Term.eval_lit (v : Value) : (Term.lit v : Term C).eval σ = .ok v := rfl
/-- `x` is what `x` is bound to. -/
theorem Term.eval_pv (x : Var) : (Term.pv x : Term C).eval σ = σ.getEnv x >>= bindingVal := by
  simp only [Term.eval, bind, Except.bind]
  cases σ.getEnv x with
  | error _ => rfl
  | ok b => cases b <;> rfl
/-- `x + 1`: `x`, then the operator on `1`. -/
theorem Term.eval_binop (op : BinOp) (p : PrimTy) (a b : Term C) : (Term.binop op p a b).eval σ =
    a.eval σ >>= fun x => evalBinop op p x (b.eval σ) := rfl
/-- `find(storage, alice.age)`: the storage, the path, the word there. -/
theorem Term.eval_find (s : STerm C) (p : PTerm C) : (Term.find s p).eval σ =
    s.eval σ >>= fun τ => p.eval σ >>= fun rs => τ.findStorage rs.1 rs.2 >>= SVal.asValue := rfl
/-- `alice` is the root `alice`. -/
theorem PTerm.eval_root (r : Name) : (PTerm.root r : PTerm C).eval σ = .ok (r, []) := rfl
/-- `p`, an alias, is the path it holds. -/
theorem PTerm.eval_pv (x : Var) : (PTerm.pv x : PTerm C).eval σ = σ.getEnv x >>= bindingPath :=
  aliasPath_eq σ x
/-- `alice.age` is `alice`, then `age`. -/
theorem PTerm.eval_field (p : PTerm C) (f : Name) : (PTerm.field p f).eval σ =
    p.eval σ >>= fun rs => .ok (rs.1, rs.2 ++ [.field f]) := rfl
/-- `balances[k]` is `balances`, then the integer `k` holds. -/
theorem PTerm.eval_at (p : PTerm C) (i : Term C) : (PTerm.at p i).eval σ =
    p.eval σ >>= fun rs => i.eval σ >>= Value.asInt >>= fun k => .ok (rs.1, rs.2 ++ [.at k]) := by
  simp only [PTerm.eval, bind, Except.bind]
  cases p.eval σ <;> try rfl
  cases i.eval σ <;> rfl
/-- `storage` is the storage of the state it is read in. -/
theorem STerm.eval_storage : (STerm.storage : STerm C).eval σ = .ok σ := rfl
/-- `save(storage, alice.age, 10)`: the value, the storage, the path, the
write. -/
theorem STerm.eval_save (s : STerm C) (p : PTerm C) (v : SValT C) : (STerm.save s p v).eval σ =
    v.eval σ >>= fun sv => s.eval σ >>= fun τ => p.eval σ >>= fun rs =>
      τ.saveStorage rs.1 rs.2 sv := rfl
/-- `delAt(storage, alice.age)`: the word there, reset to its default. -/
theorem STerm.eval_delAt (s : STerm C) (p : PTerm C) : (STerm.delAt s p).eval σ =
    s.eval σ >>= fun τ => p.eval σ >>= fun rs => τ.findStorage rs.1 rs.2 >>= fun cur =>
      τ.saveStorage rs.1 rs.2 cur.defaultOf := rfl
/-- The `10` of `alice.age = 10;`, as a word to store. -/
theorem SValT.eval_val (t : Term C) : (SValT.val t).eval σ = t.eval σ >>= fun v => .ok v.toSVal :=
  rfl
/-- The `bob` of `alice = bob;`: the subtree read there. -/
theorem SValT.eval_find (s : STerm C) (p : PTerm C) : (SValT.find s p).eval σ =
    s.eval σ >>= fun τ => p.eval σ >>= fun rs => τ.findStorage rs.1 rs.2 := rfl
/-- `{y := alice.age}` reads `alice.age` in the state it is applied in and
binds `y`. -/
theorem UpdElem.write_val (σ₀ τ : State) (x : Var) (t : Term C) : (UpdElem.val x t).write σ₀ τ =
    t.eval σ₀ >>= fun v => .ok (τ.setEnv x (.val v)) := rfl
/-- `{p := alice}` binds the alias `p`. -/
theorem UpdElem.write_path (σ₀ τ : State) (x : Var) (p : PTerm C) :
    (UpdElem.path x p).write σ₀ τ = p.eval σ₀ >>= fun rs => .ok (τ.setEnv x (.spath rs.1 rs.2)) :=
  rfl
/-- `{storage := save(…)}` replaces the storage, and nothing else. -/
theorem UpdElem.write_storage (σ₀ τ : State) (s : STerm C) : (UpdElem.storage s).write σ₀ τ =
    s.eval σ₀ >>= fun τ' => .ok { τ with storage := τ'.storage } := rfl

/-- `true` holds. -/
theorem holds_tt : holds σ (Fml.tt : Fml C) ↔ True := Iff.rfl
/-- `¬ φ`. -/
theorem holds_not (φ : Fml C) : holds σ (.not φ) ↔ ¬ holds σ φ := Iff.rfl
/-- `φ ∧ ψ`. -/
theorem holds_and (φ ψ : Fml C) : holds σ (.and φ ψ) ↔ holds σ φ ∧ holds σ ψ := Iff.rfl
/-- `a == 1 → …`. -/
theorem holds_imp (φ ψ : Fml C) : holds σ (.imp φ ψ) ↔ (holds σ φ → holds σ ψ) := Iff.rfl
/-- `y == 10` holds when both sides are defined and equal: as a diamond on
each side, since a side that halts makes it false. -/
theorem holds_eq (a b : Term C) : holds σ (.eq a b) ↔
    Modality.diamond.wp (a.eval σ) fun x => Modality.diamond.wp (b.eval σ) fun y => x = y := by
  simp only [holds]
  cases a.eval σ <;> cases b.eval σ <;> simp [Modality.wp, Modality.onHalt]
/-- `{y := alice.age} y == 10`: apply the update, under the modality it was
produced in. -/
theorem holds_upd (m : Modality) (U : Upd C) (φ : Fml C) :
    holds σ (.upd m U φ) ↔ m.wp (U.apply σ) (holds · φ) := by
  simp only [holds, Modality.after_eq_wp]

end Eval

/-! ## The tactic -/

/-- The second stage of `sol_close`: read after write, on the goal, with
each premise in scope for what follows it. -/
macro "sol_close_reads" : tactic => `(tactic|
  simp (config := { contextual := true }) only [Modality.wp_ok, Modality.wp_error,
    Modality.wp_box, Modality.wp_diamond,
    Modality.wp_ite, Modality.onHalt_box, Modality.onHalt_diamond, List.nil_append,
    List.cons_append, bindingVal_val, bindingPath_spath, bindingVal_eq_ok, asInt_eq_ok,
    toSVal_int, toSVal_bool, asValue_int, asValue_bool, defaultOf_int, defaultOf_bool, asInt_int,
    findStorage_setEnv, State.getEnv_setEnv_self, State.getEnv_setEnv_ne, Except.ok.injEq,
    Binding.val.injEq, PrimVal.int.injEq, forall_eq', exists_eq_left', true_and, and_true,
    and_self, implies_true, forall_const, ne_eq, not_false_eq_true, true_or, or_true, or_false,
    false_or, diverge_cons', not_diverge_nil_left, not_diverge_nil_right, Seg.field.injEq,
    Seg.at.injEq, reduceCtorEq, Var.user.injEq, Var.fresh.injEq, Int.ofNat.injEq,
    String.reduceEq, Nat.reduceEqDiff, Int.reduceEq, Int.reduceAdd, Int.reduceSub, Int.reduceMul,
    Int.reduceNeg, Int.reduceLT, Int.reduceLE, Nat.reducePow])

/-- `sol_close_reads` on the goal and every hypothesis. -/
macro "sol_close_reads_all" : tactic => `(tactic|
  simp_all only [Modality.wp_ok, Modality.wp_error, Modality.wp_box, Modality.wp_diamond,
    Modality.wp_ite, Modality.onHalt_box, Modality.onHalt_diamond, List.nil_append,
    List.cons_append, bindingVal_val, bindingPath_spath, bindingVal_eq_ok, asInt_eq_ok,
    toSVal_int, toSVal_bool, asValue_int, asValue_bool, defaultOf_int, defaultOf_bool, asInt_int,
    findStorage_setEnv, State.getEnv_setEnv_self, State.getEnv_setEnv_ne, Except.ok.injEq,
    Binding.val.injEq, PrimVal.int.injEq, forall_eq', exists_eq_left', true_and, and_true,
    and_self, implies_true, forall_const, ne_eq, not_false_eq_true, true_or, or_true, or_false,
    false_or, diverge_cons', not_diverge_nil_left, not_diverge_nil_right, Seg.field.injEq,
    Seg.at.injEq, reduceCtorEq, Var.user.injEq, Var.fresh.injEq, Int.ofNat.injEq,
    String.reduceEq, Nat.reduceEqDiff, Int.reduceEq, Int.reduceAdd, Int.reduceSub, Int.reduceMul,
    Int.reduceNeg, Int.reduceLT, Int.reduceLE, Nat.reducePow])

/-- `sol_close`: prove a formula with no modality left in an arbitrary state
(`Close.lean`).  Run `sol_symex` first. -/
macro "sol_close" : tactic => `(tactic|
  (intro σ
   simp only [holds_tt, holds_not, holds_and, holds_imp, holds_eq, holds_upd, Upd.apply,
     List.foldlM_cons, List.foldlM_nil, UpdElem.write_val, UpdElem.write_path,
     UpdElem.write_storage, Term.eval_lit, Term.eval_pv, Term.eval_find, Term.eval_binop,
     PTerm.eval_root, PTerm.eval_field, PTerm.eval_at, PTerm.eval_pv, STerm.eval_storage,
     STerm.eval_save, STerm.eval_delAt, SValT.eval_val, SValT.eval_find, Modality.wp_ok,
     Modality.wp_pure, Modality.wp_error, Modality.wp_bind, Modality.wp_ite,
     Modality.wp_box_saveStorage, Modality.onHalt_box, Modality.onHalt_diamond,
     evalBinop_strict, applyBinOp, BinOp.retTy, BinOp.isArith, checkArith, uintBound, intBound,
     ne_eq, reduceCtorEq, not_false_eq_true, ↓reduceIte]
   sol_close_reads
   try (intros; sol_close_reads_all)
   try (subst_vars; sol_close_reads_all)
   all_goals (try intros)
   all_goals first | omega | grind))

/-! ## Examples -/

section Examples

/-- A write, then a read of it; under the box, since `alice.age = 10;` is
stuck in a state without `alice`. -/
example : ⊨ dl[StandardExample]{ [ alice.age = 10; uint y = alice.age; ] y == 10 } := by
  sol_symex
  sol_close

/-- A parameter: the premise binds `a`, so the diamond holds. -/
example : ⊨ dl[StandardExample]{ a == 1 → ⟨ x = a; ⟩ x == 1 } := by
  sol_symex
  sol_close

/-- Frame: a write to another root. -/
example : ⊨ dl[StandardExample]{
    [ alice.age = 10; bob.age = 20; uint y = alice.age; ] y == 10 } := by
  sol_symex
  sol_close

/-- A mapping at a symbolic key, written and read back. -/
example : ⊨ dl[StandardExample]{ [ balances[k] = 5; uint y = balances[k]; ] y == 5 } := by
  sol_symex
  sol_close

/-- Frame: two keys the premise tells apart. -/
example : ⊨ dl[StandardExample]{
    k != j → [ balances[k] = 5; balances[j] = 6; uint y = balances[k]; ] y == 5 } := by
  sol_symex
  sol_close

/-- Frame: a field apart from the one written, through a fresh alias. -/
example : ⊨ dl[StandardExample]{
    [ alice.account.balance = 3; alice.age = 10; uint y = alice.account.balance; ] y == 3 } := by
  sol_symex
  sol_close

/-- A write through an alias, read through the root. -/
example : ⊨ dl[StandardExample]{
    [ Person storage p = alice; p.age = 3; uint y = alice.age; ] y == 3 } := by
  sol_symex
  sol_close

/-- A compound assignment: read, add, range-check, write. -/
example : ⊨ dl[StandardExample]{
    [ alice.age = 3; alice.age += 1; uint y = alice.age; ] y == 4 } := by
  sol_symex
  sol_close

/-- Locals only: the diamond holds everywhere, range check included. -/
example : ⊨ dl[StandardExample]{ x == 1 → ⟨ y = x + 1; ⟩ y == 2 } := by
  sol_symex
  sol_close

/-- `Notation.lean`'s: a declaration's local in the postcondition. -/
example : ⊨ dl[StandardExample]{ ⟨ uint x = 10; ⟩ x == 10 } := by
  sol_symex
  sol_close

end Examples

end Close

end Solidity
