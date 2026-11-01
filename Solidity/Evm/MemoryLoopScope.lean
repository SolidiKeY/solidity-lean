import Solidity.Evm.MemoryLoopCompile

/-! Typed scope composition around checked finite-body memory loops.
Loop bodies retain the existing finite certificate. A selected scope keeps
its actual reached-prefix demands; unselected branches contribute no demand. -/
namespace Solidity.Evm.Memory.LoopScopes
variable {C : Contract}

/-- Reuse the complete existing singleton-program simulation, including halts. -/
def singleton {b Γ Δ F G s code}
    (hs : Loops.StmtCert (C := C) b (Γ := Γ) (Δ := Δ) F G s code) :
    Loops.ProgCert b F G (.cons s .nil) (code ++ []) := .cons hs (.nil G)

mutual
inductive StmtCert {C : Contract} (b : Nat) : {Γ Δ : Ctx} → Frag Γ → Frag Δ →
    Stmt C Γ Δ → List Instr → Type where
  | base {Γ Δ F G s code} (hs : Loops.StmtCert (C := C) b (Γ := Γ) (Δ := Δ) F G s code) :
      StmtCert b F G s code
  | block {Γ Δ F G body code}
      (hp : ProgCert (C := C) b (Γ := Γ) (Δ := Δ) F G body code) :
      StmtCert b F (G.restrict Γ) (.block body) code
  | ite {Γ Δ Ξ : Ctx} {F : Frag Γ} {G : Frag Δ} {K : Frag Ξ}
      {c : Val C Γ .bool} {thn : Prog C Γ Δ} {els : Prog C Γ Ξ}
      {cond left right : List Instr}
      (hc : ValFrag (C := C) b (Γ := Γ) F c cond)
      (ht : ProgCert b (Γ := Γ) (Δ := Δ) F G thn left)
      (he : ProgCert b (Γ := Γ) (Δ := Ξ) F K els right) :
      StmtCert b F ((G.restrict Γ).meet (K.restrict Γ)) (.ite c thn els)
        (conditionalCode cond left right)
inductive ProgCert {C : Contract} (b : Nat) : {Γ Δ : Ctx} → Frag Γ → Frag Δ →
    Prog C Γ Δ → List Instr → Type where
  | nil {Γ} (F : Frag Γ) : ProgCert b F F .nil []
  | cons {Γ Δ Ξ F G K s P head tail}
      (hs : StmtCert (C := C) b (Γ := Γ) (Δ := Δ) F G s head)
      (hp : ProgCert b (Γ := Δ) (Δ := Ξ) G K P tail) :
      ProgCert b F K (.cons s P) (head ++ tail)
end

mutual
inductive StmtCost {C : Contract} {b : Nat} : {Γ Δ : Ctx} → {F : Frag Γ} → {G : Frag Δ} →
    {s : Stmt C Γ Δ} → {code : List Instr} → StmtCert b F G s code →
    (σ : State C Γ) → Solidity.Out C σ.H Δ → Nat → Prop where
  | base {Γ Δ F G s code} {hs : Loops.StmtCert b (Γ := Γ) (Δ := Δ) F G s code}
      {σ : State C Γ} {o : Solidity.Out C σ.H Δ} {cost}
      (h : Loops.Cost (singleton hs) σ o cost) : StmtCost (.base hs) σ o cost
  | block {Γ Δ F G body code} {hp : ProgCert b (Γ := Γ) (Δ := Δ) F G body code}
      {σ : State C Γ} {o : Solidity.Out C σ.H Δ} {cost}
      (ho : body.run σ = .ok o) (h : Cost hp σ o cost) :
      StmtCost (.block hp) σ ⟨o.st.drop body.ext, o.ext⟩ cost
  | iteTrue {Γ Δ Ξ : Ctx} {F : Frag Γ} {G : Frag Δ} {K : Frag Ξ}
      {c : Val C Γ .bool} {thn : Prog C Γ Δ} {els : Prog C Γ Ξ}
      {cond left right : List Instr}
      {hc : ValFrag (C := C) b (Γ := Γ) F c cond}
      {ht : ProgCert b (Γ := Γ) (Δ := Δ) F G thn left}
      {he : ProgCert b (Γ := Γ) (Δ := Ξ) F K els right}
      {σ : State C Γ} {o : Solidity.Out C σ.H Δ} {cost}
      (hv : c.evalT σ = .ok true) (ho : thn.run σ = .ok o) (h : Cost ht σ o cost) :
      StmtCost (.ite hc ht he) σ ⟨o.st.drop thn.ext, o.ext⟩ cost
  | iteFalse {Γ Δ Ξ : Ctx} {F : Frag Γ} {G : Frag Δ} {K : Frag Ξ}
      {c : Val C Γ .bool} {thn : Prog C Γ Δ} {els : Prog C Γ Ξ}
      {cond left right : List Instr}
      {hc : ValFrag (C := C) b (Γ := Γ) F c cond}
      {ht : ProgCert b (Γ := Γ) (Δ := Δ) F G thn left}
      {he : ProgCert b (Γ := Γ) (Δ := Ξ) F K els right}
      {σ : State C Γ} {o : Solidity.Out C σ.H Ξ} {cost}
      (hv : c.evalT σ = .ok false) (ho : els.run σ = .ok o) (h : Cost he σ o cost) :
      StmtCost (.ite hc ht he) σ ⟨o.st.drop els.ext, o.ext⟩ cost
inductive Cost {C : Contract} {b : Nat} : {Γ Δ : Ctx} → {F : Frag Γ} → {G : Frag Δ} →
    {P : Prog C Γ Δ} → {code : List Instr} → ProgCert b F G P code →
    (σ : State C Γ) → Solidity.Out C σ.H Δ → Nat → Prop where
  | nil {Γ F} (σ : State C Γ) : Cost (.nil F) σ ⟨σ, List.prefix_refl _⟩ 0
  | cons {Γ Δ Ξ F G K s P head tail}
      {hs : StmtCert b (Γ := Γ) (Δ := Δ) F G s head}
      {hp : ProgCert b (Γ := Δ) (Δ := Ξ) G K P tail}
      {σ : State C Γ} {o : Solidity.Out C σ.H Δ} {o' : Solidity.Out C o.st.H Ξ} {cost rest}
      (ho : s.run σ = .ok o) (hc : StmtCost hs σ o cost) (ht : Cost hp o.st o' rest) :
      Cost (.cons hs hp) σ ⟨o'.st, o.ext.trans o'.ext⟩ (cost + rest)
end

mutual
inductive StmtDemand {C : Contract} {b : Nat} : {Γ Δ : Ctx} → {F : Frag Γ} → {G : Frag Δ} →
    {s : Stmt C Γ Δ} → {code : List Instr} → StmtCert b F G s code →
    State C Γ → Nat → Prop where
  | base {Γ Δ F G s code} {hs : Loops.StmtCert b (Γ := Γ) (Δ := Δ) F G s code}
      {σ : State C Γ} {amount} (h : Loops.Demand (singleton hs) σ amount) :
      StmtDemand (.base hs) σ amount
  | block {Γ Δ F G body code} {hp : ProgCert b (Γ := Γ) (Δ := Δ) F G body code}
      {σ : State C Γ} {amount} (h : Demand hp σ amount) : StmtDemand (.block hp) σ amount
  | iteTrue {Γ Δ Ξ : Ctx} {F : Frag Γ} {G : Frag Δ} {K : Frag Ξ}
      {c : Val C Γ .bool} {thn : Prog C Γ Δ} {els : Prog C Γ Ξ}
      {cond left right : List Instr}
      {hc : ValFrag (C := C) b (Γ := Γ) F c cond}
      {ht : ProgCert b (Γ := Γ) (Δ := Δ) F G thn left}
      {he : ProgCert b (Γ := Γ) (Δ := Ξ) F K els right}
      {σ : State C Γ} {amount} (hv : c.evalT σ = .ok true) (h : Demand ht σ amount) :
      StmtDemand (.ite hc ht he) σ amount
  | iteFalse {Γ Δ Ξ : Ctx} {F : Frag Γ} {G : Frag Δ} {K : Frag Ξ}
      {c : Val C Γ .bool} {thn : Prog C Γ Δ} {els : Prog C Γ Ξ}
      {cond left right : List Instr}
      {hc : ValFrag (C := C) b (Γ := Γ) F c cond}
      {ht : ProgCert b (Γ := Γ) (Δ := Δ) F G thn left}
      {he : ProgCert b (Γ := Γ) (Δ := Ξ) F K els right}
      {σ : State C Γ} {amount} (hv : c.evalT σ = .ok false) (h : Demand he σ amount) :
      StmtDemand (.ite hc ht he) σ amount
inductive Demand {C : Contract} {b : Nat} : {Γ Δ : Ctx} → {F : Frag Γ} → {G : Frag Δ} →
    {P : Prog C Γ Δ} → {code : List Instr} → ProgCert b F G P code →
    State C Γ → Nat → Prop where
  | head {Γ Δ Ξ F G K s P head tail}
      {hs : StmtCert b (Γ := Γ) (Δ := Δ) F G s head}
      {hp : ProgCert b (Γ := Δ) (Δ := Ξ) G K P tail}
      {σ : State C Γ} {amount} (h : StmtDemand hs σ amount) : Demand (.cons hs hp) σ amount
  | tail {Γ Δ Ξ F G K s P head tail}
      {hs : StmtCert b (Γ := Γ) (Δ := Δ) F G s head}
      {hp : ProgCert b (Γ := Δ) (Δ := Ξ) G K P tail}
      {σ : State C Γ} {o : Solidity.Out C σ.H Δ} {cost amount}
      (ho : s.run σ = .ok o) (hc : StmtCost hs σ o cost) (h : Demand hp o.st amount) :
      Demand (.cons hs hp) σ (cost + amount)
end

/-- Exact source cost and allocator growth, with distinct revert/divergence. -/
def Result {Γ Δ : Ctx} (L b frame : Nat) (G : Frag Δ) (σ : State C Γ)
    (base : Nat → Fin W) (m : Machine) (cost : Solidity.Out C σ.H Δ → Nat → Prop)
    (res : TRes (Solidity.Out C σ.H Δ)) (out : Out) : Prop :=
  (∃ o m' base' amount, res = .ok o ∧ out = .ok m' 0 ∧ cost o amount ∧
    StateRepr L b frame G o.st base' m' ∧ m'.stack = m.stack ∧ BaseExtends σ.H base base' ∧
    GrowsAllocator b frame amount σ base m o.st base' m') ∨
  (res = .error .revert ∧ out = .revert) ∨ (res = .error .diverge ∧ out = .fault)

def Room {b : Nat} {Γ Δ F G P code}
    (hp : ProgCert (C := C) b (Γ := Γ) (Δ := Δ) F G P code)
    (frame : Nat) (σ : State C Γ) (base : Nat → Fin W) (m : Machine) : Prop :=
  ∀ amount, Demand hp σ amount → AllocationInput b frame amount σ base m

end Solidity.Evm.Memory.LoopScopes
