import Solidity.Calculus.ChainRewrites
import Solidity.Calculus.TheoryLaws

namespace Solidity.Examples.ChainRewrites

local instance : InContract := ⟨StandardExample⟩

def over (m : Modality) (φ : Fml StandardExample) : Fml StandardExample → Fml StandardExample
  | .upd _ U ψ => .upd m U (over m φ ψ)
  | .modal _ P ψ => .modal m P (over m φ ψ)
  | _ => φ

theorem headlineLastLine :
    Fml.mergeSpine 2 dl!{ { se1 := 10 } { sp1 := alice.account } { storage := save(storage, sp1.balance, se1) }
        alice.account.balance == 10 }
      = some dl!{ { se1 := 10 ‖ sp1 := alice.account ‖ storage := save(storage, alice.account.balance, 10) }
        alice.account.balance == 10 } := rfl

theorem headlineCaptures :
    Fml.mergeAt 0 dl!{ { se1 := 10 } { sp1 := alice.account } ⟨ sp1.balance = se1; ⟩ alice.account.balance == 10 }
      = some dl!{ { se1 := 10 ‖ sp1 := alice.account } ⟨ sp1.balance = se1; ⟩ alice.account.balance == 10 } := rfl

theorem headlineWrite :
    Fml.mergeAt 0 dl!{ { se1 := 10 ‖ sp1 := alice.account } { storage := save(storage, sp1.balance, se1) }
        alice.account.balance == 10 }
      = some dl!{ { se1 := 10 ‖ sp1 := alice.account ‖ storage := save(storage, alice.account.balance, 10) }
        alice.account.balance == 10 } := rfl

example :
    Fml.mergeAt 1 dl!{ { se1 := 10 } { sp1 := alice.account } { storage := save(storage, sp1.balance, se1) }
        alice.account.balance == 10 }
      = some dl!{ { se1 := 10 } { sp1 := alice.account ‖ storage := save(storage, alice.account.balance, se1) }
        alice.account.balance == 10 } := rfl

theorem headlineLastLineAny (m : Modality) (φ : Fml StandardExample) :
    Fml.mergeSpine 2 (over m φ dl!{ { se1 := 10 } { sp1 := alice.account }
        { storage := save(storage, sp1.balance, se1) } true })
      = some (over m φ dl!{ { se1 := 10 ‖ sp1 := alice.account
          ‖ storage := save(storage, alice.account.balance, 10) } true }) := rfl

theorem headlineCapturesAny (m : Modality) (φ : Fml StandardExample) :
    Fml.mergeAt 0 (over m φ dl!{ { se1 := 10 } { sp1 := alice.account } ⟨ sp1.balance = se1; ⟩ true })
      = some (over m φ dl!{ { se1 := 10 ‖ sp1 := alice.account } ⟨ sp1.balance = se1; ⟩ true }) := rfl

theorem headlineBox :
    symex 7 dl!{ [ alice.account.balance = 10; ] alice.account.balance ≐ 10 }
      = over .box dl!{ alice.account.balance ≐ 10 }
          dl!{ { se1 := 10 } { sp1 := alice.account } { storage := save(storage, sp1.balance, se1) } true } :=
  rfl

theorem headlineMerged :
    Fml.mergeSpine 2 (over .box dl!{ alice.account.balance ≐ 10 }
        dl!{ { se1 := 10 } { sp1 := alice.account } { storage := save(storage, sp1.balance, se1) } true })
      = some (over .box dl!{ alice.account.balance ≐ 10 }
          dl!{ { se1 := 10 ‖ sp1 := alice.account
            ‖ storage := save(storage, alice.account.balance, 10) } true }) := rfl

theorem headlineSimplified :
    Fml.updRuleAt .simplifyUpdate 0 (over .box dl!{ alice.account.balance ≐ 10 }
        dl!{ { se1 := 10 ‖ sp1 := alice.account
          ‖ storage := save(storage, alice.account.balance, 10) } true })
      = some (over .box dl!{ alice.account.balance ≐ 10 }
          dl!{ { storage := save(storage, alice.account.balance, 10) } true }) := rfl

theorem headlineApplied :
    Fml.applyStorageBoxAt 0 (over .box dl!{ alice.account.balance ≐ 10 }
        dl!{ { storage := save(storage, alice.account.balance, 10) } true })
      = some dl!{ find(save(storage, alice.account.balance, 10), alice.account.balance) ≐ 10 } := rfl

abbrev balance : PTerm StandardExample := .field (.field (.root "alice") "account") "balance"

theorem headlineRead :
    Fml.rwLaw (.find (.save .storage balance (.val (.lit (.int 10)))) balance, .lit (.int 10))
        dl!{ find(save(storage, alice.account.balance, 10), alice.account.balance) ≐ 10 }
      = some dl!{ 10 ≐ 10 } := rfl

end Solidity.Examples.ChainRewrites
