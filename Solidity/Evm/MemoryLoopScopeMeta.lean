import Solidity.Evm.MemoryLoopScope
namespace Solidity.Evm.Memory.LoopScopes
variable {C : Contract}

mutual
private def stmtMetaM {b Γ Δ F G s code}
    (hs : StmtCert (C := C) b (Γ := Γ) (Δ := Δ) F G s code) : Nat × Bool :=
  match hs with
  | .base cert => ((singleton cert).need, (singleton cert).allocates)
  | .block hp => let p := progMetaM hp; (max Γ.length p.1, p.2)
  | .ite _ ht he =>
      let t := progMetaM ht
      let e := progMetaM he
      (max Γ.length (max t.1 e.1), t.2 || e.2)
termination_by structural hs
private def progMetaM {b Γ Δ F G P code}
    (hp : ProgCert (C := C) b (Γ := Γ) (Δ := Δ) F G P code) : Nat × Bool :=
  match hp with
  | .nil _ => (Γ.length, false)
  | .cons hs ht =>
      let s := stmtMetaM hs
      let p := progMetaM ht
      (max s.1 p.1, s.2 || p.2)
termination_by structural hp
end

/-- Recursor metadata avoids indexed match casts during kernel evaluation. -/
@[implemented_by stmtMetaM]
private def stmtMeta {b Γ Δ F G s code}
    (hs : StmtCert (C := C) b (Γ := Γ) (Δ := Δ) F G s code) : Nat × Bool := by
  induction hs using StmtCert.rec
    (motive_2 := fun F G P code _ => Nat × Bool) with
  | base cert => exact ((singleton cert).need, (singleton cert).allocates)
  | @block Γ Δ F G body code hp ih => exact (max Γ.length ih.1, ih.2)
  | @ite Γ Δ Ξ F G K c thn els cond left right hc ht he iht ihe =>
      exact (max Γ.length (max iht.1 ihe.1), iht.2 || ihe.2)
  | @nil Γ F => exact (Γ.length, false)
  | cons hs ht ihs iht => exact (max ihs.1 iht.1, ihs.2 || iht.2)

@[implemented_by progMetaM]
private def progMeta {b Γ Δ F G P code}
    (hp : ProgCert (C := C) b (Γ := Γ) (Δ := Δ) F G P code) : Nat × Bool := by
  induction hp using ProgCert.rec
    (motive_1 := fun F G s code _ => Nat × Bool) with
  | base cert => exact ((singleton cert).need, (singleton cert).allocates)
  | @block Γ Δ F G body code hp ih => exact (max Γ.length ih.1, ih.2)
  | @ite Γ Δ Ξ F G K c thn els cond left right hc ht he iht ihe =>
      exact (max Γ.length (max iht.1 ihe.1), iht.2 || ihe.2)
  | @nil Γ F => exact (Γ.length, false)
  | cons hs ht ihs iht => exact (max ihs.1 iht.1, ihs.2 || iht.2)

private theorem stmtMeta_eq {b Γ Δ F G s code}
    (hs : StmtCert (C := C) b (Γ := Γ) (Δ := Δ) F G s code) : stmtMeta hs = stmtMetaM hs := by
  induction hs using StmtCert.rec
    (motive_2 := fun F G P code hp => progMeta hp = progMetaM hp) with
  | base cert => rfl
  | block hp ih => change (max _ (progMeta hp).1, (progMeta hp).2) = _; rw [ih]; rfl
  | ite hc ht he iht ihe =>
      change (max _ (max (progMeta ht).1 (progMeta he).1), (progMeta ht).2 || (progMeta he).2) = _
      rw [iht, ihe]; rfl
  | nil F => rfl
  | cons hs ht ihs iht =>
      change (max (stmtMeta hs).1 (progMeta ht).1, (stmtMeta hs).2 || (progMeta ht).2) = _
      rw [ihs, iht]; rfl

private theorem progMeta_eq {b Γ Δ F G P code}
    (hp : ProgCert (C := C) b (Γ := Γ) (Δ := Δ) F G P code) : progMeta hp = progMetaM hp := by
  induction hp using ProgCert.rec
    (motive_1 := fun F G s code hs => stmtMeta hs = stmtMetaM hs) with
  | base cert => rfl
  | block hp ih => change (max _ (progMeta hp).1, (progMeta hp).2) = _; rw [ih]; rfl
  | ite hc ht he iht ihe =>
      change (max _ (max (progMeta ht).1 (progMeta he).1), (progMeta ht).2 || (progMeta he).2) = _
      rw [iht, ihe]; rfl
  | nil F => rfl
  | cons hs ht ihs iht =>
      change (max (stmtMeta hs).1 (progMeta ht).1, (stmtMeta hs).2 || (progMeta ht).2) = _
      rw [ihs, iht]; rfl

def StmtCert.need {b Γ Δ F G s code}
    (hs : StmtCert (C := C) b (Γ := Γ) (Δ := Δ) F G s code) : Nat := (stmtMeta hs).1
def ProgCert.need {b Γ Δ F G P code}
    (hp : ProgCert (C := C) b (Γ := Γ) (Δ := Δ) F G P code) : Nat := (progMeta hp).1
def StmtCert.allocates {b Γ Δ F G s code}
    (hs : StmtCert (C := C) b (Γ := Γ) (Δ := Δ) F G s code) : Bool := (stmtMeta hs).2
def ProgCert.allocates {b Γ Δ F G P code}
    (hp : ProgCert (C := C) b (Γ := Γ) (Δ := Δ) F G P code) : Bool := (progMeta hp).2
end Solidity.Evm.Memory.LoopScopes
