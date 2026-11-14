import Solidity.Calculus.DecisionThresholdStore
import Solidity.Calculus.DecisionSourceDiscovery
import Solidity.Calculus.MemoryWitness

/-!
# Refuting literal-bounded blocks at a threshold region

The negative companions of the source literal-chain family:
`∀ x̄; (∀ uint i; i < n → body) → concl` is refuted at a state `σ` once the
universal prefix is instantiated (at each binder's default), every instance
`body[i]` with `i < n` holds at `σ`, and `concl` fails there. Both are read by
the proof-carrying checker `Fml.checkMemoryAt`; instances `i ≥ n` fail the
guard, so `n` checks cover all `2^256`. Nothing about the candidate state is
assumed: a refutation is returned only with its proof.

The candidates are threshold-uniform regions (`Calculus/DecisionThresholdStore.lean`):
dynamic arrays one past the largest literal index (at most `lenCap`), leaves
`c` below index `n` and `h` past it, with `c` and `h` drawn from the
formula's uint literals, zero, and words different from them. One region
refutes a read past the bound (it reads `h`) and a wrong value inside it (it
reads `c`), below mapping keys, struct fields, struct elements and nested
arrays alike. The bound is capped at 64 instances. This is a sound
semi-decision: the class is the set of formulas this search refutes, not a
syntactic family, and a miss stays unknown.
-/
namespace Solidity.Decide.BlockRefute
open MemoryWitness (Checked)
variable {C : Contract}

/-- All instances of a checked family over a finite list. -/
def allYes {P : Nat → Prop} : (l : List Nat) → ((j : Nat) → Checked (P j)) →
    Option (PLift (∀ j ∈ l, P j))
  | [], _ => some ⟨fun _ h => nomatch h⟩
  | j :: l, f => match f j, allYes l f with
    | .yes h, some ⟨hl⟩ => some ⟨fun k hk => by
        cases List.mem_cons.mp hk with
        | inl e => exact e ▸ h
        | inr m => exact hl k m⟩
    | _, _ => none

/-- The guard holds only below its bound. -/
theorem below_of_guard {Γ : Ctx} (σ : State C Γ) (n i : PrimTy.uint.Denote)
    (h : holds (σ.push (t := .val .uint) i) (sourceUIntBelow n)) : i.1 < n.1 := by
  change (some (decide (i.1 < n.1)) : Option Bool) = some true at h
  exact of_decide_eq_true (Option.some.inj h)

/-- A word below the bound is the literal of its natural number. -/
theorem eq_uintOfNat (i : PrimTy.uint.Denote) : i = uintOfNat i.1.toNat := by
  have hn : 0 ≤ i.1 := PrimTy.uint_nonneg i
  have hb : i.1 < 2 ^ 256 := by
    have h := i.2
    simp only [PrimTy.inRange, decide_eq_true_eq] at h
    exact_mod_cast h.2
  have hb' : i.1.toNat < 2 ^ 256 := by omega
  apply Subtype.ext
  rw [uintOfNat_val hb']
  omega

/-- Refute the block at `σ`, for the bound `n`. -/
def blockAt? {Γ : Ctx} (φ : Fml C Γ) (σ : State C Γ) (n : PrimTy.uint.Denote) :
    Option (PLift (¬ holds σ φ)) := do
  let outer ← sourceImpView? φ
  let all ← sourceUIntAllView? outer.lhs
  let inner ← sourceImpView? all.body
  let ⟨hg⟩ ← sourceEquationSame? inner.lhs (sourceUIntBelow n)
  if n.1.toNat ≤ 64 then
    match outer.rhs.checkMemoryAt σ with
    | .no hc =>
      let ⟨hb⟩ ← allYes (List.range n.1.toNat)
        (fun j => inner.rhs.checkMemoryAt (σ.push (t := .val .uint) (uintOfNat j)))
      some ⟨fun h => by
        have h' : holds σ (.imp (.all all.name .uint (.imp inner.lhs inner.rhs)) outer.rhs) := by
          have e := outer.equation.trans (congrArg (fun l => Fml.imp l outer.rhs)
            (all.equation.trans (congrArg (Fml.all all.name .uint) inner.equation)))
          exact Eq.mp (congrArg (fun ψ => holds σ ψ) e) h
        apply hc
        apply h'
        intro i hgi
        have hlt : i.1 < n.1 := below_of_guard σ n i (hg ▸ hgi)
        have hi : i = uintOfNat i.1.toNat := eq_uintOfNat i
        have hm : i.1.toNat ∈ List.range n.1.toNat := by
          apply List.mem_range.mpr
          have := PrimTy.uint_nonneg i
          omega
        rw [hi]
        exact hb _ hm⟩
    | _ => none
  else none

/-- Instantiate a universal prefix at defaults, then refute the block. -/
def chainAt? {Γ : Ctx} (φ : Fml C Γ) (σ : State C Γ) (n : PrimTy.uint.Denote) :
    Option (PLift (¬ holds σ φ)) := by
  revert σ
  apply @Fml.casesOn C (fun Γ φ => (σ : State C Γ) → Option (PLift (¬ holds σ φ))) Γ φ
  case all =>
    intro Γ name prim body σ
    exact (chainAt? body (σ.push (t := .val prim) (PrimTy.dflt prim)) n).map
      fun ⟨h⟩ => ⟨fun hall => h (hall _)⟩
  all_goals intros; exact blockAt? _ _ n
termination_by structural φ

/-- The bound of a block, among the formula's literals. -/
def blockBound? {Γ : Ctx} (ψ : Fml C Γ) (lits : List PrimTy.uint.Denote) :
    Option PrimTy.uint.Denote := do
  let outer ← sourceImpView? ψ
  let all ← sourceUIntAllView? outer.lhs
  let inner ← sourceImpView? all.body
  lits.find? fun b => (sourceEquationSame? inner.lhs (sourceUIntBelow b)).isSome

/-- The bound of the block below a universal prefix. -/
def boundAt? {Γ : Ctx} (φ : Fml C Γ) (lits : List PrimTy.uint.Denote) :
    Option PrimTy.uint.Denote := by
  apply @Fml.casesOn C (fun Γ φ => Option PrimTy.uint.Denote) Γ φ
  case all => intro Γ name prim body; exact boundAt? body lits
  case imp => intro Γ a b; exact blockBound? (.imp a b) lits
  all_goals intros; exact none
termination_by structural φ

/-- Leaves of each primitive type, below and past the threshold. -/
def leafLo (c : PrimTy.uint.Denote) : (p : PrimTy) → p.Denote
  | .uint => c
  | p => PrimTy.dflt p

def leafHi (h : PrimTy.uint.Denote) : (p : PrimTy) → p.Denote
  | .uint => h
  | p => MemoryWitness.one p

/-- The longest dynamic array a candidate region builds: twice the instance cap. -/
def lenCap : Nat := 129

/-- The candidate regions for bound `n ≤ 64`: dynamic arrays long enough for
every literal index up to `lenCap` (so a read past the bound sees the past
leaf rather than halting; a larger literal is no index such a region can
reach and is ignored), below/past leaves from the literals, without repeats. -/
def fills (n : Nat) (lits : List PrimTy.uint.Denote) : List ThresholdStore.Fill :=
  let len := min ((lits.map fun v => v.1.toNat).filter (· < lenCap) |>.foldl max n) (lenCap - 1) + 1
  if hl : len < 2 ^ 256 then
    let los := lits.eraseDups
    let his := (lits.map (MemoryWitness.different .uint) ++ lits).eraseDups
    los.flatMap fun c => his.map fun h => ⟨n, len, hl, leafLo c, leafHi h⟩
  else []

/-- **The refuter**: a threshold region at which the block is certified false. -/
def refute? (φ : Fml C []) : Option {σ : State C [] // ¬ holds σ φ} :=
  let lits := uintOfNat 0 :: sourceUIntChainLiterals φ
  match boundAt? φ lits with
  | none => none
  | some b =>
    -- `blockAt?` repeats this cap on its own; here it also bounds the regions built.
    if b.1.toNat ≤ 64 then
      (fills b.1.toNat lits).findSome? fun F =>
        (chainAt? φ (ThresholdStore.state F C) b).map fun ⟨h⟩ => ⟨_, h⟩
    else none

/-- Decidable classification by a successful certified refutation. -/
def _root_.Solidity.Fml.blockRefutable (φ : Fml C []) : Bool := (refute? φ).isSome

/-- The answer: the region state, with its proof. -/
def answer? (φ : Fml C []) : Option (MemoryWitness.Answer φ) :=
  (refute? φ).map fun w => .refuted (fun _ => w.1) (fun _ => w.2)

theorem answer_isSome {φ : Fml C []} (h : φ.blockRefutable = true) : (answer? φ).isSome = true := by
  unfold answer?
  simpa only [Option.isSome_map] using h

end Solidity.Decide.BlockRefute
