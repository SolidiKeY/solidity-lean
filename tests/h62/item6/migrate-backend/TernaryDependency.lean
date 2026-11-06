/-!
Isolated reproduction of the library dependencies used by Scalar.ternary.
This is an additive diagnostic fixture, not a replacement Backend definition.
No source pin or public signature is modified.
-/
namespace MigrateBackendFixture

abbrev Word := BitVec 256
inductive Op where
  | ADDMOD | MULMOD | other

def ternary : Op → Option (Word → Word → Word → Word)
  | .ADDMOD => some (fun a b k => if k == 0 then 0
      else BitVec.ofNat 256 ((a.toNat + b.toNat) % k.toNat))
  | .MULMOD => some (fun a b k => if k == 0 then 0
      else BitVec.ofNat 256 ((a.toNat * b.toNat) % k.toNat))
  | _ => none

def zeroProbe : Word := 0
def ofNatProbe (n : Nat) : Word := BitVec.ofNat 256 n
def beqProbe (a b : Word) : Bool := a == b
def modProbe (a b : Nat) : Nat := a % b

def ifProbe (k : Word) : Word := if k == 0 then 0 else k
def addProbe (a b k : Word) : Word := if k == 0 then 0
    else BitVec.ofNat 256 ((a.toNat + b.toNat) % k.toNat)

def ternaryRec (op : Op) : Option (Word → Word → Word → Word) :=
  Op.casesOn op
    (some (fun a b k => if k == 0 then 0
      else BitVec.ofNat 256 ((a.toNat + b.toNat) % k.toNat)))
    (some (fun a b k => if k == 0 then 0
      else BitVec.ofNat 256 ((a.toNat * b.toNat) % k.toNat)))
    none

theorem ternaryRec_eq (op : Op) : ternaryRec op = ternary op := by
  cases op <;> rfl

#print axioms ifProbe
#print axioms addProbe
/-- info: 'MigrateBackendFixture.ternaryRec' does not depend on any axioms -/
#guard_msgs in #print axioms ternaryRec
#print axioms ternaryRec_eq
#print ternary
#print axioms ternary
#print axioms zeroProbe
#print axioms ofNatProbe
#print axioms beqProbe
#print axioms modProbe

example : ternary .other = none := rfl
example : (ternary .ADDMOD).map (fun f => f 7 9 0) = some 0 := rfl
example : (ternary .MULMOD).map (fun f => f 7 9 0) = some 0 := rfl
example : (ternary .ADDMOD).map (fun f => f 3 4 5) = some 2 := rfl
example : (ternary .MULMOD).map (fun f => f 3 4 5) = some 2 := rfl
example : (ternary .ADDMOD).map (fun f => f 3 4 5) ≠ some 3 := by
  decide +kernel

end MigrateBackendFixture
