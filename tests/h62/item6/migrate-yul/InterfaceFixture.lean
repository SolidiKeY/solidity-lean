module
public section
namespace H62.MigrateYul.InterfaceFixture
universe u

@[expose] def identity {α : Sort u} (x : α) : α := x

theorem identity_eq {α : Sort u} (x : α) : identity x = x := rfl

structure PairBox (α : Type u) where
  left : α
  right : α

def withLet (n : Nat) : Nat := let k := n + 1; k + k
opaque sealed : Nat := 3
private def hidden : Nat := 7
private theorem hidden_ok : hidden = 7 := rfl
private theorem private_ext (p q : Prop) (h : p ↔ q) : p = q := propext h
theorem transitive_ext (p q : Prop) (h : p ↔ q) : p = q := private_ext p q h

def «a.b» : Nat := 1
namespace a
def b : Nat := 2
end a
end H62.MigrateYul.InterfaceFixture
