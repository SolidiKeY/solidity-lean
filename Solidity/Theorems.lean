import Solidity.Calculus.Sound
import Solidity.Calculus.Symex
import Solidity.Calculus.CallbackSound
import Solidity.Evm.Correct
import Solidity.Calculus.SolkeyProves

/-!
# The main theorems, in one page

Each theorem below is one the package proves elsewhere, restated in notation
so that it reads as it would in print; the proof is the original's name.
`open Solidity.Main` brings the notation into scope.  They are the scoped
calculus's (`Calculus/`), over the typed state and its run
(`Semantics/Run.lean`): a formula `φ : Fml C Γ` is read in a
typed state `σ : State C Γ`, and a program `P : Prog C Γ Γ'` runs
from it by `Prog.run`.  A step of `⊢ₖ` must fire one of solkey's
taclets (decision 36: the step rules read the rule set), so solkey's rules
alone derive what the calculus derives on the fragment
(`solkey_eq_calculus`) and less off it (`solkey_lt_calculus`), as master's
did; `solkey_rule_lt_calculus` says the same at the rule level.  Two of
master's statements are not restated: that symbolic execution terminates
(`symex_terminates`), retired at W2: the scoped strategy is fuelled; and
that the compiled fragment never gets stuck (`never_stuck`), subsumed: the
typed run has no stuck outcome, so `compiler_correct` covers every case.  Its progress, that it steps exactly while a modality is left
(`Fml.active_iff_step`), was retired with the old calculus at W4
`calc-del`; one direction holds (`Fml.stepFocusR_eq_none`).
`docs/intrinsic.md` (W2 `symex`, W4 `theorems`) says why.

| Notation | Reads | Is |
|---|---|---|
| `⊨ φ` | `φ` is valid | `Valid φ`: `φ` holds in every typed state |
| `σ ⊧ φ` | `φ` holds in `σ` | `holds σ φ` |
| `H ⊨ φ` | `φ` is valid under the context `H` | `∀ σ, holds σ (H.wrap φ)` |
| `H ⊢ φ`, `⊢ φ` | the calculus derives `φ` | `Proves C .all Γ₀ H φ` |
| `H ⊢ₖ φ`, `⊢ₖ φ` | solkey's rules alone derive `φ` | `Proves C .solkey Γ₀ H φ` |
| `s ⇝[k, m] p` | a rule rewrites `s` to `p` | `Rule C k m s p` |
| `s ⇝ₖ[k, m] p` | a rule of solkey's does | `Taclet C k m s p` |
| `p ≃[m, σ] s` | from `σ`, the premise `p` does what `s` does | `Premise.Sound m s p σ` |
| `⊢[I] φ`, `⊨[I] φ` | the same, when `transfer` may call back into a contract with invariant `I` | `ProvesC`, `ValidC` |
| `(P, σ) ⇓ o` | `P` run from `σ` ends in `o` | `Prog.run σ P = .ok o` |
| `⟦P⟧b` | `P` compiled, its frame at `b` | `Evm.compileProg b P` |
| `(c, m) ⇓ₘ m'`, `(c, m) ↯ₘ` | the machine runs `c` from `m` to `m'`, or reverts | `Evm.run c m` |
| `F ⊩ P ⊣ F'` | `P` is in the compiled fragment, its locals laid out by `F` then `F'` | `Evm.inFragP F P = some F'` |
| `σ ≈[C, L, b, F] m` | the machine `m` represents the typed state `σ` | `Evm.Sim C L b F σ m` |
-/

namespace Solidity

open Semantics

namespace Main

/-! ## The notation

Each symbol is a name for what it abbreviates, so that the statements below
print back in it. -/

/-- `H ⊨ φ`: valid under the context `H`, in every typed state of its outer
scope. -/
abbrev ValidUnder {C : Contract} {Γ₀ Γ : Ctx} (H : Hyps C Γ₀ Γ) (φ : Fml C Γ) :
    Prop :=
  ∀ σ : State C Γ₀, holds σ (H.wrap φ)

/-- `H ⊢ φ`: the calculus derives `φ`. -/
abbrev Derives {C : Contract} {Γ₀ Γ : Ctx} (H : Hyps C Γ₀ Γ) (φ : Fml C Γ) : Prop :=
  Proves C .all Γ₀ H φ

/-- `H ⊢ₖ φ`: solkey's rules alone derive `φ`. -/
abbrev DerivesK {C : Contract} {Γ₀ Γ : Ctx} (H : Hyps C Γ₀ Γ) (φ : Fml C Γ) :
    Prop :=
  Proves C .solkey Γ₀ H φ

/-- `s ⇝[k, m] p`: a rule rewrites `s` to `p`. -/
abbrev Rewrites {C : Contract} {Γ Γ' : Ctx} (s : Stmt C Γ Γ') (k : Nat) (m : Modality)
    (p : Premise C Γ Γ') : Prop :=
  Rule C k m s p

/-- `s ⇝ₖ[k, m] p`: a rule of solkey's rewrites `s` to `p`. -/
abbrev RewritesK {C : Contract} {Γ Γ' : Ctx} (s : Stmt C Γ Γ') (k : Nat) (m : Modality)
    (p : Premise C Γ Γ') : Prop :=
  Taclet C k m s p

/-- `p ≃[m, σ] s`: from `σ`, the premise does what the statement does. -/
abbrev DoesAs {C : Contract} {Γ Γ' : Ctx} (p : Premise C Γ Γ') (m : Modality)
    (σ : State C Γ) (s : Stmt C Γ Γ') : Prop :=
  Premise.Sound m s p σ

/-- `(P, σ) ⇓ o`: `P` run typed from `σ` ends normally in `o`. -/
abbrev Runs {C : Contract} {Γ Γ' : Ctx} (c : Prog C Γ Γ' × State C Γ)
    (o : Out C c.2.H Γ') : Prop :=
  Prog.run c.2 c.1 = .ok o

/-- `(c, m) ⇓ₘ m'`: the machine runs the code `c` from `m` to the end, in `m'`. -/
abbrev MRuns (c : List Evm.Instr × Evm.Machine) (m' : Evm.Machine) : Prop :=
  Evm.run c.1 c.2 = .ok m' 0

/-- `(c, m) ↯ₘ`: the machine running `c` from `m` reverts. -/
abbrev MReverts (c : List Evm.Instr × Evm.Machine) : Prop :=
  Evm.run c.1 c.2 = .revert

/-- `F ⊩ P ⊣ F'`: `P` is in the compiled fragment, its locals laid out by
`F` before and `F'` after. -/
abbrev Compiles {C : Contract} {Γ Γ' : Ctx} (F : Evm.Frag Γ) (P : Prog C Γ Γ')
    (F' : Evm.Frag Γ') : Prop :=
  Evm.inFragP F P = some F'

/-- `σ ≈[C, L, b, F] m`: the machine `m` represents the typed state `σ`. -/
abbrev Represents (C : Contract) (L b : Nat) {Γ : Ctx} (F : Evm.Frag Γ)
    (σ : State C Γ) (m : Evm.Machine) : Prop :=
  Evm.Sim C L b F σ m

scoped notation:25 H:26 " ⊨ " φ:26 => ValidUnder H φ
scoped notation:25 H:26 " ⊢ " φ:26 => Derives H φ
scoped notation:25 "⊢ " φ:26 => Derives Hyps.nil φ
scoped notation:25 H:26 " ⊢ₖ " φ:26 => DerivesK H φ
scoped notation:25 "⊢ₖ " φ:26 => DerivesK Hyps.nil φ
scoped notation:50 s:51 " ⇝[" k ", " m "] " p:51 => Rewrites s k m p
scoped notation:50 s:51 " ⇝ₖ[" k ", " m "] " p:51 => RewritesK s k m p
scoped notation:50 p:51 " ≃[" m ", " σ "] " s:51 => DoesAs p m σ s
scoped notation:25 "⊢[" I "] " φ:26 => ProvesC (Invariant.fml I) [] Hyps.nil φ
scoped notation:25 "⊨[" I "] " φ:26 => ValidC I φ
scoped notation:50 c:51 " ⇓ " o:51 => Runs c o
scoped notation:max "⟦" P "⟧" b:max => Evm.compileProg b P
scoped notation:50 c:51 " ⇓ₘ " m':51 => MRuns c m'
scoped notation:50 c:51 " ↯ₘ" => MReverts c
scoped notation:50 F:51 " ⊩ " P " ⊣ " F':51 => Compiles F P F'
scoped notation:50 σ:51 " ≈[" C ", " L ", " b ", " F "] " m:51 => Represents C L b F σ m

/-- `Valid φ` prints as `⊨ φ`. -/
@[scoped app_unexpander Valid]
def unexpandValid : Lean.PrettyPrinter.Unexpander
  | `($_ $φ) => `(⊨ $φ)
  | _ => throw ()

variable {C : Contract} {k : Nat} {m : Modality} {Γ Γ' Γ₀ : Ctx} {s : Stmt C Γ Γ'}
  {p p' : Premise C Γ Γ'} {H : Hyps C Γ₀ Γ} {φ : Fml C Γ}

/-! ## The rules -/

/-- **Every rule is sound**: from every typed state, its premise does what
its statement does.  Its fresh names need no side condition: a rule's fresh
locals are scoped to it (`Premise.unfold`, `Premise.bind`). -/
theorem rule_sound (d : s ⇝[k, m] p) (σ : State C Γ) : p ≃[m, σ] s :=
  Stmt.sound k m s p d.toStep σ

/-- **At most one rule**: two rules for `s` leave the same premise. -/
theorem rule_unique (d : s ⇝[k, m] p) (d' : s ⇝[k, m] p') : p = p' :=
  Rule.premise_unique d d'

/-- **Every rule is the strategy's**: a rule's premise is the one the
strategy (`Stmt.step`) computes. -/
theorem rule_is_step (d : s ⇝[k, m] p) : s.step k m = p :=
  d.toStep

/-- **Every statement has a rule**, under either modality: a rule rewrites
the statement to the premise the strategy leaves. -/
theorem rule_exists (k : Nat) (m : Modality) (s : Stmt C Γ Γ') : s ⇝[k, m] s.step k m :=
  Stmt.rule_exists k m s

/-- **The strategy fires only rules**: what it leaves is a rule's premise
(the converse of `rule_is_step`). -/
theorem rule_of_step (h : s.step k m = p) : s ⇝[k, m] p :=
  Rule.ofStep h

/-! ## solkey's rules -/

/-- **On the fragment, solkey has the rule**: a statement whose calls take
simple arguments, with no loop or `try` and no payment under the diamond,
is rewritten by one of solkey's taclets. -/
theorem solkey_rule_exists (h : s.inSolkey m = true) (hs : s.step k m = p) : s ⇝ₖ[k, m] p :=
  Stmt.step_taclet h hs

/-- **Off the fragment the rules differ**: a loop has a rule of the
calculus, and none of solkey's. -/
theorem solkey_rule_lt_calculus (k : Nat) (m : Modality) {Γ₁ : Ctx} (a : LoopAnn C Γ)
    (c : Val C Γ .bool) (body : Prog C Γ Γ₁) :
    (∃ p, Stmt.loop a c body ⇝[k, m] p) ∧ ∀ p, ¬ Stmt.loop a c body ⇝ₖ[k, m] p :=
  Stmt.solkey_lt_calculus k m a c body

/-- **A step of `⊢ₖ` is one of solkey's taclets**: the rule set admits the
statement only where the rule the strategy fires is a `Taclet`. -/
theorem solkey_step_taclet (hR : RuleSet.admits .solkey m s = true) (hs : s.step k m = p) :
    s ⇝ₖ[k, m] p :=
  Stmt.taclet_of_admits hR hs

/-- **On the fragment, solkey's rules are the calculus**: where every
program of the goal is in the fragment, solkey's rules alone derive what
the calculus derives. -/
theorem solkey_eq_calculus (hφ : φ.inSolkey = true) : (H ⊢ₖ φ) ↔ (H ⊢ φ) :=
  Proves.solkey_iff hφ

/-- **Off the fragment they derive less**: the calculus derives
`[ while (false) { } ] true`, solkey's rules do not. -/
theorem solkey_lt_calculus : ∃ φ : Fml C [], (⊢ φ) ∧ ¬ (⊢ₖ φ) :=
  Proves.solkey_lt_calculus

/-! ## The calculus -/

/-- **Soundness**: what the calculus derives is valid.  A derivation leaves
for the logic (`close`) only once no modality is left in its sequent. -/
theorem soundness : H ⊢ φ → H ⊨ φ :=
  Proves.sound

/-- **Soundness**, from no assumptions. -/
theorem soundness' {φ : Fml C []} : ⊢ φ → ⊨ φ :=
  Proves.valid

/-- **solkey's rules are sound**: what they derive alone is valid, a
derivation of `⊢ₖ` being one of `⊢` (`Proves.toAll`). -/
theorem solkey_soundness {φ : Fml C []} : ⊢ₖ φ → ⊨ φ :=
  fun h => Proves.valid h.toAll

/-- **With callbacks**: when every `transfer`, `send` or `try` may call back
into a contract with a first-order invariant `I` (KeY's `CInv`, of the
storage and the ledger), what that calculus derives is valid for that
reading.  Its transfer rule has two sequents as premises, the second after a
`{havoc}`; its send rule a third, the send refused. -/
theorem callback_soundness {I : Invariant C} {φ : Fml C []} :
    ⊢[I] φ → ⊨[I] φ :=
  ProvesC.valid

/-! ## Symbolic execution -/

/-- **Symbolic execution is sound**: where what it leaves holds, the formula
holds. -/
theorem symex_sound (n : Nat) (σ : State C Γ) : σ ⊧ symex n φ → σ ⊧ φ :=
  Solidity.symex_sound n φ σ

/-! ## The compiler -/

open Evm Evm in
/-- **The compiler is correct**: from a machine that represents the typed
state, the typed run and the compiled code both end, in states the machine
still represents, or both revert (a panic, a failed `assert`, is solc's
revert with `Panic(0x01)` data), or the world refuses a payment the program
makes and the machine alone reverts.  `L` bounds every array's length, which
solc caps at `2^64`.  There is no fourth case: on the fragment the typed run
neither diverges nor is exhausted, and the typed run halts in no other way. -/
theorem compiler_correct {P : Prog C Γ Γ'} {F : Frag Γ} {F' : Frag Γ'} {σ : State C Γ}
    {mc : Machine} {L b : Nat}
    (hP : F ⊩ P ⊣ F') (hm : σ ≈[C, L, b, F] mc) (hL : L + Prog.pushes P ≤ Lmax) :
    (∃ o mc', (P, σ) ⇓ o ∧ (⟦P⟧b, mc) ⇓ₘ mc' ∧ o.st ≈[C, L + Prog.pushes P, b, F'] mc') ∨
      ((Prog.run σ P = .error .revert ∨
          (Prog.asserts P = true ∧ Prog.run σ P = .error .panic)) ∧ (⟦P⟧b, mc) ↯ₘ) ∨
      (Prog.pays P = true ∧ (⟦P⟧b, mc) ↯ₘ ∧ ∃ o, (P, σ) ⇓ o) :=
  (compile_correct hP hm hL).imp (fun ⟨o, mc', h, h', _, hs⟩ => ⟨o, mc', h, h', hs⟩)
    (Or.imp id fun ⟨hp, h, o, _, h', _⟩ => ⟨hp, h, o, h'⟩)

open Evm Evm in
/-- **The box reaches the EVM**: where the compiled code succeeds, the typed
run did too, and `net(a)` is what `a`'s account lost, at every address but
the contract's own, whose entry stays `0`. -/
theorem compiler_net {P : Prog C Γ Γ'} {F : Frag Γ} {F' : Frag Γ'} {σ : State C Γ}
    {mc mc' : Machine} {L b : Nat}
    (hP : F ⊩ P ⊣ F') (hm : σ ≈[C, L, b, F] mc) (hL : L + Prog.pushes P ≤ Lmax)
    (hrun : (⟦P⟧b, mc) ⇓ₘ mc') :
    ∃ o, (P, σ) ⇓ o ∧
      (∀ a : Fin W, a ≠ mc'.self → netAt o.st.net a.1 = (mc'.bal₀ a.1 : Int) - mc'.bal a.1) ∧
      netAt o.st.net mc'.self = 0 :=
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

/-- info: 'Solidity.Main.solkey_rule_lt_calculus' depends on axioms: [propext] -/
#guard_msgs in #print axioms solkey_rule_lt_calculus

/-- info: 'Solidity.Main.solkey_step_taclet' depends on axioms: [propext] -/
#guard_msgs in #print axioms solkey_step_taclet

/-- info: 'Solidity.Main.solkey_eq_calculus' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms solkey_eq_calculus

/-- info: 'Solidity.Main.solkey_lt_calculus' depends on axioms: [propext, Classical.choice, Quot.sound] -/
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
