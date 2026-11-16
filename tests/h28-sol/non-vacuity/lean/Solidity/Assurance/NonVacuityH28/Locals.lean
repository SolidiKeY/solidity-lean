import Solidity.Assurance.NonVacuityH28.Families

/-! Nonempty local/alias fields of the scoped simulation relation. -/
namespace Solidity.Assurance.NonVacuityH28
open Solidity Semantics

/-- Transport only: the applications below construct all its premises. -/
theorem represented_success {C : Contract} {Γ Δ : Ctx} {P : Prog C Γ Δ}
    {F : Evm.Frag Γ} {G : Evm.Frag Δ} {L b : Nat} {σ : State C Γ}
    {mc mc' : Evm.Machine} {o : Out C σ.H Δ}
    (hf : Evm.inFragP F P = some G) (hm : Evm.Sim C L b F σ mc)
    (hL : L + Evm.Prog.pushes P ≤ Evm.Lmax)
    (hs : Prog.run σ P = .ok o) (ht : Evm.run (Evm.compileProg b P) mc = .ok mc' 0) :
    Evm.Sim C (L + Evm.Prog.pushes P) b G o.st mc' := by
  rcases Main.compiler_correct hf hm hL with
    ⟨o', mc'', ho, hm', hr⟩ | ⟨_, hrev⟩ | ⟨_, hdiv⟩
  · have he : (Except.ok o' : TRes (Out C σ.H Δ)) = .ok o := ho.symm.trans hs
    cases he
    have he' : Evm.Out.ok mc'' 0 = .ok mc' 0 := hm'.symm.trans ht
    cases he'
    exact hr
  · have he : Evm.Out.ok mc' 0 = .revert := ht.symm.trans hrev
    cases he
  · have he : Evm.Out.ok mc' 0 = .fault := ht.symm.trans hdiv
    cases he

variable (C : Contract)

def valueProgram (n : Int) (hn : PrimTy.uint.inRange n = true) : Prog C [] [.val .uint] :=
  .cons (.declLocal .uint (.user "v") (some (.simple (.lit n hn)))) .nil

def localSource : State C [] := Evm.freshT C 0 (by decide) ⟨0, by decide⟩
def localMachine : Evm.Machine := Evm.Machine.init (fun _ => 0) ⟨0, by decide⟩
def valueSource (n : Int) (hn : PrimTy.uint.inRange n = true) : State C [.val .uint] :=
  (localSource C).push (⟨n, hn⟩ : PrimTy.uint.Denote)
def valueMachine (n : Int) : Evm.Machine :=
  { localMachine with mem := Evm.upd localMachine.mem 0 (.val (Evm.wmod (Evm.toWord n))) }

theorem value_fragment (n : Int) (hn : PrimTy.uint.inRange n = true) :
    Evm.inFragP (Evm.Frag.init []) (valueProgram C n hn) = some (Evm.Frag.init [.val .uint]) := rfl

theorem value_source (n : Int) (hn : PrimTy.uint.inRange n = true) :
    Prog.run (localSource C) (valueProgram C n hn) = .ok ⟨valueSource C n hn, List.prefix_refl _⟩ := rfl

theorem value_target (n : Int) (hn : PrimTy.uint.inRange n = true) :
    Evm.run (Evm.compileProg 0 (valueProgram C n hn)) localMachine = .ok (valueMachine n) 0 := rfl

theorem value_representation (n : Int) (hn : PrimTy.uint.inRange n = true) :
    Evm.Sim C 1 0 (Evm.Frag.init [.val .uint]) (valueSource C n hn) (valueMachine n) :=
  represented_success (value_fragment C n hn) (closed_simulation C)
    (by change 1 ≤ Evm.Lmax; decide) (value_source C n hn) (value_target C n hn)

/-- The value-local field is actually queried at its inhabited index. -/
theorem value_field (n : Int) (hn : PrimTy.uint.inRange n = true) :
    Evm.ReprV .uint (TEnv.get .here (valueSource C n hn).env)
      ((valueMachine n).memAt (Evm.lvl 0 (.here : Idx [.val .uint] (.val .uint)))) :=
  (value_representation C n hn).vals .here

def aliasContract : Contract := { vars := [("xs", .ref (.array (.prim .uint)))] }
def aliasRef : SRef aliasContract (.ref (.array (.prim .uint))) := ⟨"xs", rfl, .nil⟩
def aliasProgram : Prog aliasContract [] [.alias (.array (.prim .uint))] :=
  .cons (.declStorage (.array (.prim .uint)) (.user "p") (some (.path (.loc (.root "xs" rfl))))) .nil

def aliasSource : State aliasContract [.alias (.array (.prim .uint))] :=
  (localSource aliasContract).push (some aliasRef)
def aliasMachine : Evm.Machine :=
  { localMachine with mem := Evm.upd localMachine.mem 0 (.slot (.root 0)) }

theorem alias_fragment : Evm.inFragP (Evm.Frag.init []) aliasProgram =
    some (Evm.Frag.init [.alias (.array (.prim .uint))]) := rfl

theorem alias_source : Prog.run (localSource aliasContract) aliasProgram =
    .ok ⟨aliasSource, List.prefix_refl _⟩ := rfl

theorem alias_target : Evm.run (Evm.compileProg 0 aliasProgram) localMachine = .ok aliasMachine 0 := rfl

theorem alias_representation : Evm.Sim aliasContract 1 0
    (Evm.Frag.init [.alias (.array (.prim .uint))]) aliasSource aliasMachine :=
  represented_success alias_fragment (closed_simulation aliasContract)
    (by change 1 ≤ Evm.Lmax; decide) alias_source alias_target

theorem alias_field : ∃ r s, TEnv.get .here aliasSource.env = some r ∧
    aliasMachine.memAt (Evm.lvl 0 (.here : Idx [.alias (.array (.prim .uint))] (.alias (.array (.prim .uint))))) = .slot s ∧
    Evm.PathSlot aliasContract true r s :=
  alias_representation.aliases .here rfl

end Solidity.Assurance.NonVacuityH28
