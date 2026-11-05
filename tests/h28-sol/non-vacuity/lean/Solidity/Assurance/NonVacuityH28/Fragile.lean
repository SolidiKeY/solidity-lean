import Solidity.Assurance.NonVacuityH28.Locals

namespace Solidity.Assurance.NonVacuityH28
open Solidity Semantics

def fragileContract : Contract :=
  { vars := [("xs", .ref (.fixed (.ref (.array (.prim .uint))) 1))] }

def fragileProgram : Prog fragileContract [] [.alias (.array (.prim .uint))] :=
  .cons (.declStorage (.array (.prim .uint)) (.user "p")
    (some (.path (.loc (.index (.arr (.fixed (n := 1)))
      (.loc (.root "xs" rfl)) (.simple (.lit 0 rfl))))))) .nil

def fragileLayout : Evm.Frag [.alias (.array (.prim .uint))] := ⟨[.fragile]⟩

theorem fragile_fragment : Evm.inFragP (Evm.Frag.init []) fragileProgram = some fragileLayout := rfl

theorem fragile_source : ∃ o, Prog.run (localSource fragileContract) fragileProgram = .ok o :=
  ⟨_, rfl⟩

/-- The target execution is obtained from the public compiler contract. The
independent target reduction remains a separately recorded resource stop. -/
theorem fragile_joint :
    ∃ o mc', Prog.run (localSource fragileContract) fragileProgram = .ok o ∧
      Evm.run (Evm.compileProg 0 fragileProgram) localMachine = .ok mc' 0 ∧
      Evm.Sim fragileContract 1 0 fragileLayout o.st mc' ∧
      ∃ (r : SRef fragileContract (.ref (.array (.prim .uint)))) (s : Evm.Slot),
        TEnv.get .here o.st.env = some r ∧
        mc'.memAt (Evm.lvl 0 (.here : Idx [.alias (.array (.prim .uint))] (.alias (.array (.prim .uint))))) = .slot s ∧
        Evm.PathSlot fragileContract false r s ∧ ∃ sv, o.st.storage.findLive r = some sv := by
  obtain ⟨o, ho⟩ := fragile_source
  rcases Main.compiler_correct fragile_fragment (closed_simulation fragileContract)
    (by change 1 ≤ Evm.Lmax; decide) with
    ⟨o', mc', ho', ht, hr⟩ | ⟨he, _⟩ | ⟨hp, _⟩ | ⟨hd, _⟩
  · have heq : (Except.ok o' : TRes (Out fragileContract (localSource fragileContract).H _)) = .ok o :=
      ho'.symm.trans ho
    cases heq
    exact ⟨o, mc', ho, ht, hr, hr.fragile .here rfl⟩
  · rcases he with he | ⟨_, he⟩
    · have hbad : (Except.ok o : TRes (Out fragileContract (localSource fragileContract).H _)) = .error .revert :=
        ho.symm.trans he
      cases hbad
    · have hbad : (Except.ok o : TRes (Out fragileContract (localSource fragileContract).H _)) = .error .panic :=
        ho.symm.trans he
      cases hbad
  · cases hp
  · have hbad : (Except.ok o : TRes (Out fragileContract (localSource fragileContract).H _)) = .error .diverge :=
      ho.symm.trans hd
    cases hbad

end Solidity.Assurance.NonVacuityH28
