import Solidity.Calculus.Core.Sound
import Solidity.Calculus.Core.Symex
import Solidity.Calculus.Core.CallbackSound
import Solidity.Evm.CoreCorrect
import Solidity.Calculus.Core.SolkeyFragment

/-!
# The main theorems, in one page

Each theorem below is one the package proves elsewhere, restated in notation
so that it reads as it would in print; the proof is the original's name.
`open Solidity.Main` brings the notation into scope.  They are the scoped
calculus's (`Calculus/Core/`), over the typed state and its run
(`Semantics/Core/TypedRun.lean`): a formula `φ : Core.Fml C Γ` is read in a
typed state `σ : Core.TState C Γ`, and a program `P : Core.Prog C Γ Γ'` runs
from it by `Core.Prog.trun`.  Two of today's headline theorems have no
scoped statement: that solkey's rules alone derive what the calculus
derives on the fragment (the scoped `⊢ₖ` restricts no rule yet), and that
symbolic execution terminates (the scoped strategy is fuelled);
`docs/intrinsic.md` (W4 `theorems`) says why.

| Notation | Reads | Is |
|---|---|---|
| `⊨ φ` | `φ` is valid | `Core.Valid φ`: `φ` holds in every typed state |
| `σ ⊧ φ` | `φ` holds in `σ` | `Core.holds σ φ` |
| `H ⊨ φ` | `φ` is valid under the context `H` | `∀ σ, Core.holds σ (H.wrap φ)` |
| `H ⊢ φ`, `⊢ φ` | the calculus derives `φ` | `Core.Proves C .all Γ₀ H φ` |
| `H ⊢ₖ φ`, `⊢ₖ φ` | solkey's rules alone derive `φ` (no rule reads the set yet) | `Core.Proves C .solkey Γ₀ H φ` |
| `s ⇝[k, m] p` | a rule rewrites `s` to `p` | `Core.Rule C k m s p` |
| `s ⇝ₖ[k, m] p` | a rule of solkey's does | `Core.Taclet C k m s p` |
| `p ≃[m, σ] s` | from `σ`, the premise `p` does what `s` does | `Core.Premise.Sound m s p σ` |
| `⊢[I] φ`, `⊨[I] φ` | the same, when `transfer` may call back into a contract with invariant `I` | `Core.ProvesC`, `Core.ValidC` |
| `(P, σ) ⇓ o` | `P` run from `σ` ends in `o` | `Core.Prog.trun σ P = .ok o` |
| `⟦P⟧b` | `P` compiled, its frame at `b` | `Evm.Core.compileProg b P` |
| `(c, m) ⇓ₘ m'`, `(c, m) ↯ₘ` | the machine runs `c` from `m` to `m'`, or reverts | `Evm.run c m` |
| `F ⊩ P ⊣ F'` | `P` is in the compiled fragment, its locals laid out by `F` then `F'` | `Evm.Core.inFragP F P = some F'` |
| `σ ≈[C, L, b, F] m` | the machine `m` represents the typed state `σ` | `Evm.Core.Sim C L b F σ.sem (Look.ofTEnv σ.env) m` |
-/

namespace Solidity

open Semantics

namespace Main

/-! ## The notation

Each symbol is a name for what it abbreviates, so that the statements below
print back in it. -/

/-- `H ⊨ φ`: valid under the context `H`, in every typed state of its outer
scope. -/
abbrev ValidUnder {C : Contract} {Γ₀ Γ : Core.Ctx} (H : Core.Hyps C Γ₀ Γ) (φ : Core.Fml C Γ) :
    Prop :=
  ∀ σ : Core.TState C Γ₀, Core.holds σ (H.wrap φ)

/-- `H ⊢ φ`: the calculus derives `φ`. -/
abbrev Derives {C : Contract} {Γ₀ Γ : Core.Ctx} (H : Core.Hyps C Γ₀ Γ) (φ : Core.Fml C Γ) : Prop :=
  Core.Proves C .all Γ₀ H φ

/-- `H ⊢ₖ φ`: solkey's rules alone derive `φ`. -/
abbrev DerivesK {C : Contract} {Γ₀ Γ : Core.Ctx} (H : Core.Hyps C Γ₀ Γ) (φ : Core.Fml C Γ) :
    Prop :=
  Core.Proves C .solkey Γ₀ H φ

/-- `s ⇝[k, m] p`: a rule rewrites `s` to `p`. -/
abbrev Rewrites {C : Contract} {Γ Γ' : Core.Ctx} (s : Core.Stmt C Γ Γ') (k : Nat) (m : Modality)
    (p : Core.Premise C Γ Γ') : Prop :=
  Core.Rule C k m s p

/-- `s ⇝ₖ[k, m] p`: a rule of solkey's rewrites `s` to `p`. -/
abbrev RewritesK {C : Contract} {Γ Γ' : Core.Ctx} (s : Core.Stmt C Γ Γ') (k : Nat) (m : Modality)
    (p : Core.Premise C Γ Γ') : Prop :=
  Core.Taclet C k m s p

/-- `p ≃[m, σ] s`: from `σ`, the premise does what the statement does. -/
abbrev DoesAs {C : Contract} {Γ Γ' : Core.Ctx} (p : Core.Premise C Γ Γ') (m : Modality)
    (σ : Core.TState C Γ) (s : Core.Stmt C Γ Γ') : Prop :=
  Core.Premise.Sound m s p σ

/-- `(P, σ) ⇓ o`: `P` run typed from `σ` ends normally in `o`. -/
abbrev Runs {C : Contract} {Γ Γ' : Core.Ctx} (c : Core.Prog C Γ Γ' × Core.TState C Γ)
    (o : Core.Out C c.2.H Γ') : Prop :=
  Core.Prog.trun c.2 c.1 = .ok o

/-- `(c, m) ⇓ₘ m'`: the machine runs the code `c` from `m` to the end, in `m'`. -/
abbrev MRuns (c : List Evm.Instr × Evm.Machine) (m' : Evm.Machine) : Prop :=
  Evm.run c.1 c.2 = .ok m' 0

/-- `(c, m) ↯ₘ`: the machine running `c` from `m` reverts. -/
abbrev MReverts (c : List Evm.Instr × Evm.Machine) : Prop :=
  Evm.run c.1 c.2 = .revert

/-- `F ⊩ P ⊣ F'`: `P` is in the compiled fragment, its locals laid out by
`F` before and `F'` after. -/
abbrev Compiles {C : Contract} {Γ Γ' : Core.Ctx} (F : Evm.Core.Frag Γ) (P : Core.Prog C Γ Γ')
    (F' : Evm.Core.Frag Γ') : Prop :=
  Evm.Core.inFragP F P = some F'

/-- `σ ≈[C, L, b, F] m`: the machine `m` represents the typed state `σ`. -/
abbrev Represents (C : Contract) (L b : Nat) {Γ : Core.Ctx} (F : Evm.Core.Frag Γ)
    (σ : Core.TState C Γ) (m : Evm.Machine) : Prop :=
  Evm.Core.Sim C L b F σ.sem (Evm.Core.Look.ofTEnv σ.env) m

scoped notation:25 "⊨ " φ:26 => Core.Valid φ
scoped notation:50 σ:51 " ⊧ " φ:51 => Core.holds σ φ
scoped notation:25 H:26 " ⊨ " φ:26 => ValidUnder H φ
scoped notation:25 H:26 " ⊢ " φ:26 => Derives H φ
scoped notation:25 "⊢ " φ:26 => Derives Core.Hyps.nil φ
scoped notation:25 H:26 " ⊢ₖ " φ:26 => DerivesK H φ
scoped notation:25 "⊢ₖ " φ:26 => DerivesK Core.Hyps.nil φ
scoped notation:50 s:51 " ⇝[" k ", " m "] " p:51 => Rewrites s k m p
scoped notation:50 s:51 " ⇝ₖ[" k ", " m "] " p:51 => RewritesK s k m p
scoped notation:50 p:51 " ≃[" m ", " σ "] " s:51 => DoesAs p m σ s
scoped notation:25 "⊢[" I "] " φ:26 => Core.ProvesC (Core.Invariant.fml I) [] Core.Hyps.nil φ
scoped notation:25 "⊨[" I "] " φ:26 => Core.ValidC I φ
scoped notation:50 c:51 " ⇓ " o:51 => Runs c o
scoped notation:max "⟦" P "⟧" b:max => Evm.Core.compileProg b P
scoped notation:50 c:51 " ⇓ₘ " m':51 => MRuns c m'
scoped notation:50 c:51 " ↯ₘ" => MReverts c
scoped notation:50 F:51 " ⊩ " P " ⊣ " F':51 => Compiles F P F'
scoped notation:50 σ:51 " ≈[" C ", " L ", " b ", " F "] " m:51 => Represents C L b F σ m

/-- `Core.Valid φ` prints as `⊨ φ`. -/
@[scoped app_unexpander Core.Valid]
def unexpandValid : Lean.PrettyPrinter.Unexpander
  | `($_ $φ) => `(⊨ $φ)
  | _ => throw ()

variable {C : Contract} {k : Nat} {m : Modality} {Γ Γ' Γ₀ : Core.Ctx} {s : Core.Stmt C Γ Γ'}
  {p p' : Core.Premise C Γ Γ'} {H : Core.Hyps C Γ₀ Γ} {φ : Core.Fml C Γ}

/-! ## The rules -/

/-- **Every rule is sound**: from every typed state, its premise does what
its statement does.  Its fresh names need no side condition: a rule's fresh
locals are scoped to it (`Premise.unfold`, `Premise.bind`). -/
theorem rule_sound (d : s ⇝[k, m] p) (σ : Core.TState C Γ) : p ≃[m, σ] s :=
  Core.Stmt.sound k m s p d.toStep σ

/-- **At most one rule**: two rules for `s` leave the same premise. -/
theorem rule_unique (d : s ⇝[k, m] p) (d' : s ⇝[k, m] p') : p = p' :=
  Core.Rule.premise_unique d d'

/-- **Every rule is the strategy's**: a rule's premise is the one the
strategy (`Core.Stmt.step`) computes. -/
theorem rule_is_step (d : s ⇝[k, m] p) : s.step k m = some p :=
  d.toStep

/-- **Every statement has a rule**, under either modality: the strategy
leaves a premise, and a rule rewrites the statement to it. -/
theorem rule_exists (k : Nat) (m : Modality) (s : Core.Stmt C Γ Γ') :
    ∃ p, s.step k m = some p ∧ s ⇝[k, m] p :=
  Core.Stmt.rule_exists k m s

/-- **The strategy fires only rules**: what it leaves is a rule's premise
(the converse of `rule_is_step`). -/
theorem rule_of_step (h : s.step k m = some p) : s ⇝[k, m] p :=
  Core.Rule.ofStep h

/-! ## solkey's rules -/

/-- **On the fragment, solkey has the rule**: a statement whose calls take
simple arguments, with no loop or `try` and no payment under the diamond,
is rewritten by one of solkey's taclets. -/
theorem solkey_rule_exists (h : s.inSolkey m = true) (hs : s.step k m = some p) : s ⇝ₖ[k, m] p :=
  Core.Stmt.step_taclet h hs

/-- **Off the fragment they differ**: a loop has a rule of the calculus,
and none of solkey's. -/
theorem solkey_lt_calculus (k : Nat) (m : Modality) {Γ₁ : Core.Ctx} (a : Core.LoopAnn C Γ)
    (c : Core.Val C Γ .bool) (body : Core.Prog C Γ Γ₁) :
    (∃ p, Core.Stmt.loop a c body ⇝[k, m] p) ∧ ∀ p, ¬ Core.Stmt.loop a c body ⇝ₖ[k, m] p :=
  Core.Stmt.solkey_lt_calculus k m a c body

/-! ## The calculus -/

/-- **Soundness**: what the calculus derives is valid.  A derivation leaves
for the logic (`close`) only once no modality is left in its sequent. -/
theorem soundness : H ⊢ φ → H ⊨ φ :=
  Core.Proves.sound

/-- **Soundness**, from no assumptions. -/
theorem soundness' {φ : Core.Fml C []} : ⊢ φ → ⊨ φ :=
  Core.Proves.valid

/-- **solkey's rules are sound**: what they derive alone is valid.  (The
scoped judgement takes the rule set as an index no rule reads yet, so this
is `soundness'` itself: `docs/intrinsic.md`, proposed decision 33.) -/
theorem solkey_soundness {φ : Core.Fml C []} : ⊢ₖ φ → ⊨ φ :=
  Core.Proves.valid

/-- **With callbacks**: when every `transfer`, `send` or `try` may call back
into a contract with a first-order invariant `I` (KeY's `CInv`, of the
storage and the ledger), what that calculus derives is valid for that
reading.  Its transfer rule has two sequents as premises, the second after a
`{havoc}`; its send rule a third, the send refused. -/
theorem callback_soundness {I : Core.Invariant C} (hI : I.fml.FO = true) {φ : Core.Fml C []} :
    ⊢[I] φ → ⊨[I] φ :=
  Core.ProvesC.valid hI

/-! ## Symbolic execution -/

/-- **Symbolic execution is sound**: where what it leaves holds, the formula
holds. -/
theorem symex_sound (n : Nat) (σ : Core.TState C Γ) : σ ⊧ Core.symex n φ → σ ⊧ φ :=
  Core.symex_sound Core.Stmt.sound n φ σ

/-! ## The compiler -/

open Evm Evm.Core in
/-- **The compiler is correct**: from a machine that represents the typed
state, the typed run and the compiled code both end, in states the machine
still represents, or both revert (a panic, a failed `assert`, is solc's
revert with `Panic(0x01)` data), or the world refuses a payment the program
makes and the machine alone reverts.  `L` bounds every array's length, which
solc caps at `2^64`.  There is no fourth case: on the fragment the typed run
neither diverges nor is exhausted, and the typed run has no stuck state. -/
theorem compiler_correct {P : Core.Prog C Γ Γ'} {F : Frag Γ} {F' : Frag Γ'} {σ : Core.TState C Γ}
    {mc : Machine} {L b : Nat}
    (hP : F ⊩ P ⊣ F') (hm : σ ≈[C, L, b, F] mc) (hL : L + Prog.pushes P ≤ Lmax) :
    (∃ o mc', (P, σ) ⇓ o ∧ (⟦P⟧b, mc) ⇓ₘ mc' ∧ o.st ≈[C, L + Prog.pushes P, b, F'] mc') ∨
      ((Core.Prog.trun σ P = .error .revert ∨
          (Prog.asserts P = true ∧ Core.Prog.trun σ P = .error .panic)) ∧ (⟦P⟧b, mc) ↯ₘ) ∨
      (Prog.pays P = true ∧ (⟦P⟧b, mc) ↯ₘ ∧ ∃ o, (P, σ) ⇓ o) :=
  (compile_correct hP hm hL).imp (fun ⟨o, mc', h, h', _, hs⟩ => ⟨o, mc', h, h', hs⟩)
    (Or.imp id fun ⟨hp, h, o, _, h', _⟩ => ⟨hp, h, o, h'⟩)

open Evm Evm.Core in
/-- **The box reaches the EVM**: where the compiled code succeeds, the typed
run did too, and `net(a)` is what `a`'s account lost, at every address but
the contract's own, whose entry stays `0`. -/
theorem compiler_net {P : Core.Prog C Γ Γ'} {F : Frag Γ} {F' : Frag Γ'} {σ : Core.TState C Γ}
    {mc mc' : Machine} {L b : Nat}
    (hP : F ⊩ P ⊣ F') (hm : σ ≈[C, L, b, F] mc) (hL : L + Prog.pushes P ≤ Lmax)
    (hrun : (⟦P⟧b, mc) ⇓ₘ mc') :
    ∃ o, (P, σ) ⇓ o ∧
      (∀ a : Nat, a < W → a ≠ mc'.self → o.st.sem.getNet a = (mc'.bal₀ a : Int) - mc'.bal a) ∧
      o.st.sem.getNet mc'.self = 0 :=
  compile_net hP hm hL hrun

/-! ## Their axioms: Lean's three at most -/

/-- info: 'Solidity.Main.rule_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms rule_sound

/-- info: 'Solidity.Main.rule_unique' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms rule_unique

/-- info: 'Solidity.Main.rule_is_step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms rule_is_step

/-- info: 'Solidity.Main.rule_exists' depends on axioms: [propext] -/
#guard_msgs in #print axioms rule_exists

/-- info: 'Solidity.Main.rule_of_step' depends on axioms: [propext] -/
#guard_msgs in #print axioms rule_of_step

/-- info: 'Solidity.Main.solkey_rule_exists' depends on axioms: [propext] -/
#guard_msgs in #print axioms solkey_rule_exists

/-- info: 'Solidity.Main.solkey_lt_calculus' depends on axioms: [propext] -/
#guard_msgs in #print axioms solkey_lt_calculus

/-- info: 'Solidity.Main.soundness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms soundness

/-- info: 'Solidity.Main.soundness'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms soundness'

/-- info: 'Solidity.Main.solkey_soundness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms solkey_soundness

/-- info: 'Solidity.Main.callback_soundness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms callback_soundness

/-- info: 'Solidity.Main.symex_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms symex_sound

/-- info: 'Solidity.Main.compiler_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms compiler_correct

/-- info: 'Solidity.Main.compiler_net' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms compiler_net

end Main
end Solidity
