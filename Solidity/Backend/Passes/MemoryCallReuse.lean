import Solidity.Backend.Passes.MemoryCallObservations

/-! Three distinct published call producers reuse the actual escaped-reference
state. The primitive, memory and void returns precede a real allocating pass.
These are intrinsic fixtures, not Source name-resolution or world semantics. -/
namespace Solidity.Backend.Passes.MemoryCallReuse
open Evm Evm.Memory Evm.Compiler MemoryCallControls

abbrev AliasContext : Ctx := .mem A :: After

def prefixProgram : Prog C [] After := allocate.join call
def leading : Calls.Program 1 (Frag.init []) prefixProgram :=
  (Calls.compile 1 _ prefixProgram).get (by decide +kernel)
theorem prefix_free : Evm.Prog.pushes prefixProgram = 0 := by decide +kernel
noncomputable def before : Solidity.Out C initial.H After :=
  ⟨second.st,first.ext.trans second.ext⟩
theorem prefix_source : prefixProgram.run initial = .ok before := by
  rw [prefixProgram,DeferredSource.join_run]
  simp only [TRun.seq,first_source,second_source,Except.map]
  rfl

def arguments : Args C After [.mem A] := .snocMemory .nil A (.user "a") (.var .here rfl)
def wrongArguments : Args C After [.mem A] :=
  .snocMemory .nil A (.user "a") (.var (.there (.there (.there .here))) rfl)

def scalarBody : Prog C [.val .uint,.mem A] [.val .uint,.mem A] :=
  .cons (.assignMem (.index .dyn (.var (.there .here) rfl) (.simple (.lit 1 rfl)))
    (.val (.binop .add rfl rfl
      (.readMem (.index .dyn (.var (.there .here) rfl) (.simple (.lit 1 rfl))))
      (.simple (.lit 1 rfl)))))
  (.cons (.assignLocal .here
    (.readMem (.index .dyn (.var (.there .here) rfl) (.simple (.lit 1 rfl))))) .nil)

def scalarCall : Prog C After After :=
  .cons (.call "readReturned" arguments (.val .uint (.user "r")
    (some (.there (.there .here)))) scalarBody) .nil

def wrongCall : Prog C After After :=
  .cons (.call "readOld" wrongArguments (.val .uint (.user "r")
    (some (.there (.there .here)))) scalarBody) .nil

def aliasBody : Prog C [.mem A,.mem A] [.mem A,.mem A] :=
  .cons (.rebindMem .here (.alias (.var (.there .here) rfl))) .nil

def aliasCall : Prog C After AliasContext :=
  .cons (.call "aliasReturned" arguments (.mem A (.user "alias") rfl rfl) aliasBody) .nil

def voidBody : Prog C [.mem A] [.mem A,.mem A] :=
  .cons (.assignMem (.index .dyn (.var .here rfl) (.simple (.lit 1 rfl)))
    (.val (.binop .add rfl rfl
      (.readMem (.index .dyn (.var .here rfl) (.simple (.lit 1 rfl))))
      (.simple (.lit 1 rfl)))))
  (.cons (.declMem A (.user "private") (some (.newArr (.lit 1 rfl) rfl)) rfl rfl)
  (.cons (.assignMem (.index .dyn (.var .here rfl) (.simple (.lit 0 rfl)))
    (.val (.simple (.lit 55 rfl)))) .nil))

def voidCall : Prog C After After :=
  .cons (.call "mutateReturned" arguments .none voidBody) .nil

def fresh (Γ : Ctx) : Prog C Γ (.mem A :: Γ) :=
  .cons (.declMem A (.user "following") (some (.newArr (.lit 1 rfl) rfl)) rfl rfl) .nil

def scalar : Calls.Program 1 leading.frag scalarCall :=
  (Calls.compile 1 _ scalarCall).get (by decide +kernel)
def alias : Calls.Program 1 leading.frag aliasCall :=
  (Calls.compile 1 _ aliasCall).get (by decide +kernel)
def void : Calls.Program 1 leading.frag voidCall :=
  (Calls.compile 1 _ voidCall).get (by decide +kernel)
def wrong : Calls.Program 1 leading.frag wrongCall :=
  (Calls.compile 1 _ wrongCall).get (by decide +kernel)
def scalarFresh : CompiledProg 1 scalar.frag (fresh After) :=
  (compileProg 1 _ (fresh After)).get (by decide +kernel)
def aliasFresh : CompiledProg 1 alias.frag (fresh AliasContext) :=
  (compileProg 1 _ (fresh AliasContext)).get (by decide +kernel)
def voidFresh : CompiledProg 1 void.frag (fresh After) :=
  (compileProg 1 _ (fresh After)).get (by decide +kernel)

theorem free : Evm.Prog.pushes scalarCall = 0 ∧ Evm.Prog.pushes aliasCall = 0 ∧
    Evm.Prog.pushes voidCall = 0 ∧ Evm.Prog.pushes wrongCall = 0 := by decide +kernel

theorem costs : leading.cost initial = 8 ∧ scalar.cost before.st = 0 ∧
    alias.cost before.st = 1 ∧ void.cost before.st = 2 ∧
    scalar.allocates = false := by decide +kernel

theorem frames : 1 + leading.need ≤ 128 ∧ 1 + scalar.need ≤ 128 ∧
    1 + alias.need ≤ 128 ∧ 1 + void.need ≤ 128 ∧ 1 + wrong.need ≤ 128 ∧
    1 + frameNeedProg (fresh After) ≤ 128 ∧
    1 + frameNeedProg (fresh AliasContext) ≤ 128 := by decide +kernel

private theorem source_get {Γ Δ : Ctx} {σ : State C Γ} {P : Prog C Γ Δ}
    {o : Solidity.Out C σ.H Δ} (hx : some o = (P.run σ).toOption) : P.run σ = .ok o := by
  cases hs : P.run σ with
  | ok value => rw [hs] at hx; exact congrArg Except.ok (Option.some.inj hx).symm
  | error e => rw [hs] at hx; cases hx

noncomputable def scalarOut : Solidity.Out C before.st.H After :=
  (scalarCall.run before.st).toOption.get (by decide +kernel)
noncomputable def aliasOut : Solidity.Out C before.st.H AliasContext :=
  (aliasCall.run before.st).toOption.get (by decide +kernel)
noncomputable def voidOut : Solidity.Out C before.st.H After :=
  (voidCall.run before.st).toOption.get (by decide +kernel)
noncomputable def scalarFinal : Solidity.Out C scalarOut.st.H (.mem A :: After) :=
  ((fresh After).run scalarOut.st).toOption.get (by decide +kernel)
noncomputable def aliasFinal : Solidity.Out C aliasOut.st.H (.mem A :: AliasContext) :=
  ((fresh AliasContext).run aliasOut.st).toOption.get (by decide +kernel)
noncomputable def voidFinal : Solidity.Out C voidOut.st.H (.mem A :: After) :=
  ((fresh After).run voidOut.st).toOption.get (by decide +kernel)

theorem scalar_source : scalarCall.run before.st = .ok scalarOut := source_get (Option.some_get _)
theorem alias_source : aliasCall.run before.st = .ok aliasOut := source_get (Option.some_get _)
theorem void_source : voidCall.run before.st = .ok voidOut := source_get (Option.some_get _)
theorem scalar_final : (fresh After).run scalarOut.st = .ok scalarFinal := source_get (Option.some_get _)
theorem alias_final : (fresh AliasContext).run aliasOut.st = .ok aliasFinal := source_get (Option.some_get _)
theorem void_final : (fresh After).run voidOut.st = .ok voidFinal := source_get (Option.some_get _)
theorem wrong_source : wrongCall.run before.st = .error .revert := by
  have tag : (match wrongCall.run before.st with
    | .error .revert => true | _ => false) = true := by decide +kernel
  generalize hx : wrongCall.run before.st = result at tag ⊢
  cases result with
  | ok o => cases tag
  | error halt => cases halt <;> first | rfl | cases tag

theorem public_calls :
    (Compiler.compile 1 leading.frag scalarCall).map (·.isMemoryCalls) = some true ∧
    (Compiler.compile 1 leading.frag aliasCall).map (·.isMemoryCalls) = some true ∧
    (Compiler.compile 1 leading.frag voidCall).map (·.isMemoryCalls) = some true ∧
    (Compiler.compile 1 leading.frag wrongCall).map (·.isMemoryCalls) = some true := by
  decide +kernel

theorem scalar_fresh_cost (σ : State C After) : scalarFresh.cert.cost σ = 2 := by
  with_unfolding_all rfl
theorem alias_fresh_cost (σ : State C AliasContext) : aliasFresh.cert.cost σ = 2 := by
  with_unfolding_all rfl
theorem void_fresh_cost (σ : State C After) : voidFresh.cert.cost σ = 2 := by
  with_unfolding_all rfl


/-- Existing intrinsic tuple returns are meaningful, but the published call
producer still refuses this constructor. This is evidence, not a new exclusion. -/
abbrev TupleContext : Ctx := [.val .uint,.val .uint] ++ After

def tupleCall : Prog C After TupleContext :=
  .cons (.call "tuple" .nil
    (.rets (.snoc (.snoc .nil .uint (.user "left")) .uint (.user "right"))) .nil) .nil

noncomputable def tupleOut : Solidity.Out C before.st.H TupleContext :=
  (tupleCall.run before.st).toOption.get (by decide +kernel)

theorem tuple_source : tupleCall.run before.st = .ok tupleOut := source_get (Option.some_get _)

theorem tuple_refused : (Calls.compile 1 leading.frag tupleCall).isNone = true ∧
    (Compiler.compile 1 leading.frag tupleCall).isNone = true := by decide +kernel

end Solidity.Backend.Passes.MemoryCallReuse
