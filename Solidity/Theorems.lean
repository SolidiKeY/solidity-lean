import Solidity.Calculus.SolkeyFragment
import Solidity.Calculus.Uniqueness
import Solidity.Calculus.Termination
import Solidity.Calculus.Callback
import Solidity.Evm.Correctness

/-!
# The main theorems, in one page

Each theorem below is one the package proves elsewhere, restated in notation
so that it reads as it would in print; the proof is the original's name.
`open Solidity.Main` brings the notation into scope.

| Notation | Reads | Is |
|---|---|---|
| `⊨ φ` | `φ` is valid | `Valid φ`: `φ` holds in every state |
| `σ ⊧ φ` | `φ` holds in `σ` | `holds σ φ` |
| `Γ ⊨ φ` | `φ` is valid under the context `Γ` | `Valid (Hyp.wrap Γ φ)` |
| `Γ ⊢ φ`, `⊢ φ` | the calculus derives `φ` | `Proves .all Γ φ` |
| `Γ ⊢ₖ φ`, `⊢ₖ φ` | solkey's rules alone derive `φ` | `Proves .solkey Γ φ` |
| `s ⇝[k, m] p` | a rule rewrites `s` to `p` | `Rule C k m s p` |
| `s ⇝ₖ[k, m] p` | a rule of solkey's does | `Taclet C k m s p` |
| `p ≃[k, m] s` | the premise `p` does what `s` does | `Premise.Correct k m s p` |
| `k ♯ s` | the names a rule numbers `k` are fresh for `s` | `Avoids s.vars (freshVars k)` |
| `x ∈ SolKey` | `x`'s calls take simple arguments | `Stmt.inSolkey`, `Fml.inSolkey` |
| `⊢[I] φ`, `⊨[I] φ` | the same, when `transfer` may call back into a contract with invariant `I` | `ProvesC`, `ValidC` |
| `(P, σ) ⇓ σ'` | `P` run from `σ` ends in `σ'` | `Prog.run σ P = .ok σ'` |
| `(P, σ) ↯` | `P` run from `σ` reverts | `Prog.run σ P = .error .revert` |
| `⟦P⟧` | `P` compiled | `Evm.compileProg P` |
| `(c, m) ⇓ₘ m'`, `(c, m) ↯ₘ` | the machine runs `c` from `m` to `m'`, or reverts | `Evm.run c m` |
| `Γ ⊩ P ⊣ Γ'` | `P` is in the compiled fragment, locals typed `Γ` then `Γ'` | `Evm.wtProg Γ P = some Γ'` |
| `σ ≈[C, L, Γ] m` | the machine `m` represents the state `σ` | `Evm.Sim C L Γ σ m` |
-/

namespace Solidity

open Semantics

namespace Main

/-! ## The notation

Each symbol is a name for what it abbreviates, so that the statements below
print back in it. -/

/-- `Γ ⊨ φ`: valid under the context `Γ`. -/
abbrev ValidUnder {C : Contract} (Γ : List (Hyp C)) (φ : Fml C) : Prop := Valid (Hyp.wrap Γ φ)

/-- `Γ ⊢ φ`: the calculus derives `φ`. -/
abbrev Derives {C : Contract} (Γ : List (Hyp C)) (φ : Fml C) : Prop := Proves .all Γ φ

/-- `Γ ⊢ₖ φ`: solkey's rules alone derive `φ`. -/
abbrev DerivesK {C : Contract} (Γ : List (Hyp C)) (φ : Fml C) : Prop := Proves .solkey Γ φ

/-- `s ⇝[k, m] p`: a rule rewrites `s` to `p`. -/
abbrev Rewrites {C : Contract} (s : Stmt C) (k : Nat) (m : Modality) (p : Premise C) : Prop :=
  Rule C k m s p

/-- `s ⇝ₖ[k, m] p`: a rule of solkey's rewrites `s` to `p`. -/
abbrev RewritesK {C : Contract} (s : Stmt C) (k : Nat) (m : Modality) (p : Premise C) : Prop :=
  Taclet C k m s p

/-- `p ≃[k, m] s`: the premise does what the statement does. -/
abbrev DoesAs {C : Contract} (p : Premise C) (k : Nat) (m : Modality) (s : Stmt C) : Prop :=
  Premise.Correct k m s p

/-- `k ♯ s`: the names a rule numbers `k` are fresh for `s`. -/
abbrev FreshFor {C : Contract} (k : Nat) (s : Stmt C) : Prop := Avoids s.vars (freshVars k)

/-- No modality left to run: what symbolic execution ends in.  The strategy
runs modalities in positive positions only, so one under `¬` or left of `→`
may remain (`Fml.active`). -/
abbrev FirstOrder {C : Contract} (φ : Fml C) : Prop := φ.active = false

/-- Membership in solkey's fragment, for statements, programs and formulas. -/
class InSolkey (α : Type) where
  inSolkey : α → Bool

instance {C : Contract} : InSolkey (Stmt C) := ⟨Stmt.inSolkey⟩
instance {C : Contract} : InSolkey (Prog C) := ⟨Prog.inSolkey⟩
instance {C : Contract} : InSolkey (Fml C) := ⟨Fml.inSolkey⟩

/-- `x ∈ SolKey`: every call of `x` takes simple arguments. -/
abbrev InFragment {α : Type} [InSolkey α] (x : α) : Prop := InSolkey.inSolkey x = true

/-- `(P, σ) ⇓ σ'`: `P` run from `σ` ends normally in `σ'`. -/
abbrev Runs {C : Contract} (c : Prog C × State) (σ' : State) : Prop :=
  Prog.run c.2 c.1 = .ok σ'

/-- `(P, σ) ↯`: `P` run from `σ` reverts. -/
abbrev Reverts {C : Contract} (c : Prog C × State) : Prop :=
  Prog.run c.2 c.1 = .error .revert

/-- `(c, m) ⇓ₘ m'`: the machine runs the code `c` from `m` to the end, in `m'`. -/
abbrev MRuns (c : List Evm.Instr × Evm.Machine) (m' : Evm.Machine) : Prop :=
  Evm.run c.1 c.2 = .ok m' 0

/-- `(c, m) ↯ₘ`: the machine running `c` from `m` reverts. -/
abbrev MReverts (c : List Evm.Instr × Evm.Machine) : Prop :=
  Evm.run c.1 c.2 = .revert

/-- `Γ ⊩ P ⊣ Γ'`: `P` is in the compiled fragment, its locals typed `Γ` before
and `Γ'` after. -/
abbrev Compiles {C : Contract} (Γ : Evm.TyCtx) (P : Prog C) (Γ' : Evm.TyCtx) : Prop :=
  Evm.wtProg Γ P = some Γ'

scoped notation:25 Γ:26 " ⊨ " φ:26 => ValidUnder Γ φ
scoped notation:25 Γ:26 " ⊢ " φ:26 => Derives Γ φ
scoped notation:25 "⊢ " φ:26 => Derives [] φ
scoped notation:25 Γ:26 " ⊢ₖ " φ:26 => DerivesK Γ φ
scoped notation:25 "⊢ₖ " φ:26 => DerivesK [] φ
scoped notation:50 s:51 " ⇝[" k ", " m "] " p:51 => Rewrites s k m p
scoped notation:50 s:51 " ⇝ₖ[" k ", " m "] " p:51 => RewritesK s k m p
scoped notation:50 p:51 " ≃[" k ", " m "] " s:51 => DoesAs p k m s
scoped notation:50 k:51 " ♯ " s:51 => FreshFor k s
scoped notation:50 x:51 " ∈ " "SolKey" => InFragment x
scoped notation:25 "⊢[" I "] " φ:26 => ProvesC I [] φ
scoped notation:25 "⊨[" I "] " φ:26 => ValidC I φ
scoped notation:50 c:51 " ⇓ " σ':51 => Runs c σ'
scoped notation:50 c:51 " ↯" => Reverts c
scoped notation:max "⟦" P "⟧" => Evm.compileProg P
scoped notation:50 c:51 " ⇓ₘ " m':51 => MRuns c m'
scoped notation:50 c:51 " ↯ₘ" => MReverts c
scoped notation:50 Γ:51 " ⊩ " P " ⊣ " Γ':51 => Compiles Γ P Γ'
scoped notation:50 σ:51 " ≈[" C ", " L ", " Γ "] " m:51 => Evm.Sim C L Γ σ m

/-- `Valid φ` prints as `⊨ φ`, the prefix `RuleSyntax.lean` reads. -/
@[scoped app_unexpander Valid]
def unexpandValid : Lean.PrettyPrinter.Unexpander
  | `($_ $φ) => `(⊨ $φ)
  | _ => throw ()

variable {C : Contract} {k : Nat} {m : Modality} {s : Stmt C} {p p' : Premise C}
  {Γ : List (Hyp C)} {φ : Fml C}

/-! ## The rules -/

/-- **Every rule is sound**: its premise does what its statement does, from
every state, once its fresh names are fresh. -/
theorem rule_sound (d : s ⇝[k, m] p) (fresh : k ♯ s) : p ≃[k, m] s :=
  d.sound fresh

/-- **Every statement has a rule**, under either modality. -/
theorem rule_exists (k : Nat) (m : Modality) (s : Stmt C) : ∃ p, s ⇝[k, m] p :=
  Stmt.complete k m s

/-- **At most one rule**: two rules for `s` leave the same premise. -/
theorem rule_unique (d : s ⇝[k, m] p) (d' : s ⇝[k, m] p') : p = p' :=
  Rule.premise_unique d d'

/-! ## The calculus -/

/-- **Soundness**: what the calculus derives is valid.  A derivation leaves
for the logic (`close`) only once no modality is left in its sequent. -/
theorem soundness : Γ ⊢ φ → Γ ⊨ φ :=
  Proves.sound

/-- **Soundness**, from no assumptions. -/
theorem soundness' : ⊢ φ → ⊨ φ :=
  Proves.valid

/-- **solkey's rules are sound**: what they derive alone is valid. -/
theorem solkey_soundness : ⊢ₖ φ → ⊨ φ :=
  Proves.solkey_valid

/-- **On the fragment, solkey's rules are the calculus**: a formula whose
calls take simple arguments is derived by solkey's rules exactly when it is
derived at all. -/
theorem solkey_eq_calculus (h : φ ∈ SolKey) : (⊢ₖ φ) ↔ (⊢ φ) :=
  Proves.solkey_iff h

/-- **Off the fragment they differ**: `[ f(x + 1); ] true` is derived by the
calculus and not by solkey's rules, so `solkey_eq_calculus` needs its
hypothesis. -/
theorem solkey_lt_calculus : ∃ φ : Fml C, (⊢ φ) ∧ ¬ (⊢ₖ φ) :=
  Proves.solkey_lt_calculus

/-- **On the fragment, solkey has the rule**: the rule the strategy fires is
one of solkey's. -/
theorem solkey_rule_exists (h : s ∈ SolKey) : s ⇝ₖ[k, m] (s.step k m).premise :=
  Stmt.step_taclet h

/-- **With callbacks**: when every `transfer` may call back into a contract
with invariant `I`, what that calculus derives is valid for that reading.  Its
callback rule has two sequents as premises, the second after a `{havoc}`. -/
theorem callback_soundness {I : Invariant C} : ⊢[I] φ → ⊨[I] φ :=
  ProvesC.valid

/-! ## Symbolic execution -/

/-- **Symbolic execution is sound**: where what it leaves holds, the formula
holds. -/
theorem symex_sound (n : Nat) (σ : State) : σ ⊧ symex n φ → σ ⊧ φ :=
  Solidity.symex_sound n φ σ

/-- **Symbolic execution terminates**: given its measure in steps, it leaves
no modality. -/
theorem symex_terminates (n : Nat) (h : φ.measure ≤ n) : FirstOrder (symex n φ) :=
  symex_normalizes n φ h

/-! ## The compiler -/

open Evm in
/-- **The compiler is correct**: from a machine that represents the state,
the program and its compiled code both end, in states the machine still
represents, or both revert.  `L` bounds every array's length, which solc
caps at `2^64`. -/
theorem compiler_correct {P : Prog C} {Γ Γ' : TyCtx} {σ : State} {mc : Machine} {L : Nat}
    (hP : Γ ⊩ P ⊣ Γ') (hm : σ ≈[C, L, Γ] mc) (hL : L + pushesP P ≤ Lmax) :
    (∃ σ' mc', (P, σ) ⇓ σ' ∧ (⟦P⟧, mc) ⇓ₘ mc' ∧ σ' ≈[C, L + pushesP P, Γ'] mc') ∨
      ((P, σ) ↯ ∧ (⟦P⟧, mc) ↯ₘ) :=
  (compile_correct hP hm hL).imp (fun ⟨σ', mc', h, h', _, hs⟩ => ⟨σ', mc', h, h', hs⟩) id

open Evm in
/-- **The fragment never gets stuck**: a program the compiler takes ends or
reverts. -/
theorem never_stuck {P : Prog C} {Γ Γ' : TyCtx} {σ : State} {mc : Machine} {L : Nat}
    (hP : Γ ⊩ P ⊣ Γ') (hm : σ ≈[C, L, Γ] mc) (hL : L + pushesP P ≤ Lmax) :
    Prog.run σ P ≠ .error .stuck :=
  not_stuck hP hm hL

end Main
end Solidity


