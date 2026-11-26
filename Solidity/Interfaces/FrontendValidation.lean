import Solidity.Frontend.SolcJson.Body
import Solidity.SolcValidation.IrCensusUnique
import Solidity.SolcValidation.IrParse

/-! Fixed structural postconditions, separated from external compiler execution.
These are specification propositions, not proofs or execution assumptions. -/
namespace Solidity.Interfaces.FrontendValidation
open Lean Solidity.Frontend Solidity.SolcValidation.IrSyntax

/-- Typed JSON access preserves the original field and its value. -/
def JsonFields : Prop :=
  (∀ j k v, J.get j k = .ok v → j.getObjVal? k = .ok v) ∧
  (∀ j k v, J.opt j k = some v → j.getObjVal? k = .ok v ∧ v ≠ .null) ∧
  (∀ j k s, J.str j k = .ok s → j.getObjVal? k = .ok (.str s)) ∧
  (∀ j k xs, J.arr j k = .ok xs → j.getObjVal? k = .ok (.arr xs.toArray)) ∧
  (∀ j k s, J.str? j k = some s → j.getObjVal? k = .ok (.str s)) ∧
  (∀ j k xs, J.arr? j k = some xs → j.getObjVal? k = .ok (.arr xs)) ∧
  (∀ j i, J.ref? j = some i → j.getObjValAs? Int "referencedDeclaration" = .ok i) ∧
  (∀ j i, J.id? j = some i → j.getObjValAs? Int "id" = .ok i)

/-- Scalar decoding and binder admission retain exact values and freshness. -/
def IrAtoms : Prop :=
  (∀ n b, toByte? n = some b → b.val = n) ∧
  (∀ c d, hexDigit? c = some d → d < 16 ∧
    ((d < 10 ∧ c.toNat = 48 + d) ∨
      (10 ≤ d ∧ (c.toNat = 87 + d ∨ c.toNat = 55 + d)))) ∧
  (∀ bs w, stringWord bs = some w →
    bs.length ≤ 32 ∧ w.val = bytesValue bs * 256 ^ (32 - bs.length)) ∧
  (∀ L x m, findVar L x = some m → m.index = L.idxOf x) ∧
  (∀ F x s, findFn F x = some s → s.1.name = x ∧
    s.2.index = (F.map FnSig.name).idxOf x) ∧
  (∀ L xs, freshNames L xs = .ok () →
    xs.Nodup ∧ ∀ x ∈ xs, x ∉ L ∧ reserved x = false) ∧
  (∀ ss, namesNodup ss = true → (ss.map FnSig.name).Nodup)

/-- Reduced fractions and exact cross-multiplied arithmetic, with no claim
about malformed input denominators being positive. -/
def Canonical (q : Q) : Prop := 0 < q.den ∧ Nat.gcd q.num.natAbs q.den = 1

def RationalChecks : Prop :=
  (∀ n d q, Q.make n d = some q → d ≠ 0 ∧ Canonical q ∧ q.num * d = n * q.den) ∧
  (∀ a b q, Q.add a b = some q → Canonical q ∧
    q.num * (a.den * b.den : Nat) = (a.num * b.den + b.num * a.den) * q.den) ∧
  (∀ a b q, Q.sub a b = some q → Canonical q ∧
    q.num * (a.den * b.den : Nat) = (a.num * b.den - b.num * a.den) * q.den) ∧
  (∀ a b q, Q.mul a b = some q → Canonical q ∧
    q.num * (a.den * b.den : Nat) = (a.num * b.num) * q.den) ∧
  (∀ a b q, Q.div a b = some q → Canonical q ∧
    q.num * (a.den * b.num) = (a.num * b.den) * q.den) ∧
  (∀ a n, Q.int? a = some n → a.den = 1 ∧ a.num = n)

end Solidity.Interfaces.FrontendValidation
