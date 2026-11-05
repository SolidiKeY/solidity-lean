import Solidity.Evm.MemoryRecursiveLiftFull

/-! Intrinsic certificates over the EXISTING source AST. Recursive loop bodies,
blocks and branches remain indexed by their exact contexts, fragments and code.
No runtime state/AST or assumed output-law field is introduced. -/
namespace Solidity.Evm.Memory.Recursive
variable {C : Contract}

mutual
inductive StmtCert {C : Contract} (b : Nat) : {Γ Δ : Ctx} → Frag Γ → Frag Δ → Stmt C Γ Δ → List Instr → Type where
  | base {Γ Δ F G s code} (cert : LoopScopes.StmtCert (C:=C) b (Γ:=Γ) (Δ:=Δ) F G s code) : StmtCert b F G s code
  | block {Γ Δ F G body code} (cert : ProgCert (C:=C) b (Γ:=Γ) (Δ:=Δ) F G body code) :
      StmtCert b F (G.restrict Γ) (.block body) code
  | ite {Γ Δ Ξ : Ctx} {F : Frag Γ} {G : Frag Δ} {K : Frag Ξ}
      {c : Val C Γ .bool} {left : Prog C Γ Δ} {right : Prog C Γ Ξ} {cond lc rc : List Instr}
      (condition : ValFrag b F c cond) (yes : ProgCert b F G left lc) (no : ProgCert b F K right rc) :
      StmtCert b F ((G.restrict Γ).meet (K.restrict Γ)) (.ite c left right) (conditionalCode cond lc rc)
  | loop {Γ Δ : Ctx} {F : Frag Γ} {G : Frag Δ} {c : Val C Γ .bool}
      {body : Prog C Γ Δ} {cond code : List Instr} (a : LoopAnn C Γ)
      (condition : ValFrag b F c cond) (bodyCert : ProgCert b F G body code) (stable : G.restrict Γ=F) :
      StmtCert b F F (.loop a c body) [.loop cond code]
inductive ProgCert {C : Contract} (b : Nat) : {Γ Δ : Ctx} → Frag Γ → Frag Δ → Prog C Γ Δ → List Instr → Type where
  | nil {Γ} (F : Frag Γ) : ProgCert b F F .nil []
  | cons {Γ Δ Ξ F G K s P head tail}
      (statement : StmtCert (C:=C) b (Γ:=Γ) (Δ:=Δ) F G s head)
      (rest : ProgCert b (Γ:=Δ) (Δ:=Ξ) G K P tail) : ProgCert b F K (.cons s P) (head++tail)
end

mutual
inductive StmtCost {C : Contract} {b : Nat} : {Γ Δ : Ctx} → {F : Frag Γ} → {G : Frag Δ} →
    {s : Stmt C Γ Δ} → {code : List Instr} → StmtCert b F G s code →
    (σ : State C Γ) → Solidity.Out C σ.H Δ → Nat → Prop where
  | base {Γ Δ F G s code} {cert : LoopScopes.StmtCert b (Γ:=Γ) (Δ:=Δ) F G s code}
      {σ : State C Γ} {out amount} (cost : LoopScopes.StmtCost cert σ out amount) :
      StmtCost (.base cert) σ out amount
  | block {Γ Δ F G body code} {cert : ProgCert b (Γ:=Γ) (Δ:=Δ) F G body code}
      {σ : State C Γ} {out : Solidity.Out C σ.H Δ} {amount}
      (run : body.run σ=.ok out) (cost : Cost cert σ out amount) :
      StmtCost (.block cert) σ ⟨out.st.drop body.ext,out.ext⟩ amount
  | iteTrue {Γ Δ Ξ : Ctx} {F : Frag Γ} {G : Frag Δ} {K : Frag Ξ}
      {c : Val C Γ .bool} {left : Prog C Γ Δ} {right : Prog C Γ Ξ} {cond lc rc : List Instr}
      {hc : ValFrag b F c cond} {ht : ProgCert b F G left lc} {he : ProgCert b F K right rc}
      {σ : State C Γ} {out : Solidity.Out C σ.H Δ} {amount}
      (condition : c.evalT σ=.ok true) (run : left.run σ=.ok out) (cost : Cost ht σ out amount) :
      StmtCost (.ite hc ht he) σ ⟨out.st.drop left.ext,out.ext⟩ amount
  | iteFalse {Γ Δ Ξ : Ctx} {F : Frag Γ} {G : Frag Δ} {K : Frag Ξ}
      {c : Val C Γ .bool} {left : Prog C Γ Δ} {right : Prog C Γ Ξ} {cond lc rc : List Instr}
      {hc : ValFrag b F c cond} {ht : ProgCert b F G left lc} {he : ProgCert b F K right rc}
      {σ : State C Γ} {out : Solidity.Out C σ.H Ξ} {amount}
      (condition : c.evalT σ=.ok false) (run : right.run σ=.ok out) (cost : Cost he σ out amount) :
      StmtCost (.ite hc ht he) σ ⟨out.st.drop right.ext,out.ext⟩ amount
  | loop {Γ Δ : Ctx} {F : Frag Γ} {G : Frag Δ} {c : Val C Γ .bool}
      {body : Prog C Γ Δ} {cond code : List Instr} {a : LoopAnn C Γ}
      {hc : ValFrag b F c cond} {cert : ProgCert b F G body code} {stable : G.restrict Γ=F}
      {σ : State C Γ} {out amount} (hp : LoopPrefix cert c σ out amount) :
      StmtCost (.loop a hc cert stable) σ out amount
inductive Cost {C : Contract} {b : Nat} : {Γ Δ : Ctx} → {F : Frag Γ} → {G : Frag Δ} →
    {P : Prog C Γ Δ} → {code : List Instr} → ProgCert b F G P code →
    (σ : State C Γ) → Solidity.Out C σ.H Δ → Nat → Prop where
  | nil {Γ F} (σ : State C Γ) : Cost (.nil F) σ ⟨σ,List.prefix_refl _⟩ 0
  | cons {Γ Δ Ξ F G K s P head tail}
      {hs : StmtCert b (Γ:=Γ) (Δ:=Δ) F G s head} {hp : ProgCert b (Γ:=Δ) (Δ:=Ξ) G K P tail}
      {σ : State C Γ} {out : Solidity.Out C σ.H Δ} {last : Solidity.Out C out.st.H Ξ} {amount rest}
      (run : s.run σ=.ok out) (cost : StmtCost hs σ out amount) (tailCost : Cost hp out.st last rest) :
      Cost (.cons hs hp) σ ⟨last.st,out.ext.trans last.ext⟩ (amount+rest)
inductive LoopPrefix {C : Contract} {b : Nat} : {Γ Δ : Ctx} → {F : Frag Γ} → {G : Frag Δ} →
    {body : Prog C Γ Δ} → {code : List Instr} → (cert : ProgCert b F G body code) →
    (c : Val C Γ .bool) → (σ : State C Γ) → Solidity.Out C σ.H Γ → Nat → Prop where
  | start {Γ Δ F G body code} (cert : ProgCert (C:=C) b (Γ:=Γ) (Δ:=Δ) F G body code)
      (c : Val C Γ .bool) (σ : State C Γ) : LoopPrefix cert c σ ⟨σ,List.prefix_refl _⟩ 0
  | next {Γ Δ F G body code} {cert : ProgCert (C:=C) b (Γ:=Γ) (Δ:=Δ) F G body code}
      {c : Val C Γ .bool} {σ : State C Γ} {out : Solidity.Out C σ.H Γ} {last : Solidity.Out C out.st.H Δ} {amount spent}
      (before : LoopPrefix cert c σ out amount) (condition : c.evalT out.st=.ok true)
      (run : body.run out.st=.ok last) (bodyCost : Cost cert out.st last spent) :
      LoopPrefix cert c σ ⟨last.st.drop body.ext,out.ext.trans last.ext⟩ (amount+spent)
end

mutual
inductive StmtDemand {C : Contract} {b : Nat} : {Γ Δ : Ctx} → {F : Frag Γ} → {G : Frag Δ} →
    {s : Stmt C Γ Δ} → {code : List Instr} → StmtCert b F G s code → State C Γ → Nat → Prop where
  | base {Γ Δ F G s code} {cert : LoopScopes.StmtCert b (Γ:=Γ) (Δ:=Δ) F G s code}
      {σ amount} (demand : LoopScopes.StmtDemand cert σ amount) : StmtDemand (.base cert) σ amount
  | block {Γ Δ F G body code} {cert : ProgCert b (Γ:=Γ) (Δ:=Δ) F G body code}
      {σ amount} (demand : Demand cert σ amount) : StmtDemand (.block cert) σ amount
  | iteTrue {Γ Δ Ξ : Ctx} {F : Frag Γ} {G : Frag Δ} {K : Frag Ξ}
      {c : Val C Γ .bool} {left : Prog C Γ Δ} {right : Prog C Γ Ξ} {cond lc rc : List Instr}
      {hc : ValFrag b F c cond} {ht : ProgCert b F G left lc} {he : ProgCert b F K right rc}
      {σ amount} (condition : c.evalT σ=.ok true) (demand : Demand ht σ amount) : StmtDemand (.ite hc ht he) σ amount
  | iteFalse {Γ Δ Ξ : Ctx} {F : Frag Γ} {G : Frag Δ} {K : Frag Ξ}
      {c : Val C Γ .bool} {left : Prog C Γ Δ} {right : Prog C Γ Ξ} {cond lc rc : List Instr}
      {hc : ValFrag b F c cond} {ht : ProgCert b F G left lc} {he : ProgCert b F K right rc}
      {σ amount} (condition : c.evalT σ=.ok false) (demand : Demand he σ amount) : StmtDemand (.ite hc ht he) σ amount
  | loopPrefix {Γ Δ : Ctx} {F : Frag Γ} {G : Frag Δ} {c : Val C Γ .bool}
      {body : Prog C Γ Δ} {cond code : List Instr} {a : LoopAnn C Γ}
      {hc : ValFrag b F c cond} {cert : ProgCert b F G body code} {stable : G.restrict Γ=F}
      {σ out amount} (hp : LoopPrefix cert c σ out amount) : StmtDemand (.loop a hc cert stable) σ amount
  | loopBody {Γ Δ : Ctx} {F : Frag Γ} {G : Frag Δ} {c : Val C Γ .bool}
      {body : Prog C Γ Δ} {cond code : List Instr} {a : LoopAnn C Γ}
      {hc : ValFrag b F c cond} {cert : ProgCert b F G body code} {stable : G.restrict Γ=F}
      {σ out amount spent} (hp : LoopPrefix cert c σ out amount) (condition : c.evalT out.st=.ok true)
      (demand : Demand cert out.st spent) : StmtDemand (.loop a hc cert stable) σ (amount+spent)
inductive Demand {C : Contract} {b : Nat} : {Γ Δ : Ctx} → {F : Frag Γ} → {G : Frag Δ} →
    {P : Prog C Γ Δ} → {code : List Instr} → ProgCert b F G P code → State C Γ → Nat → Prop where
  | head {Γ Δ Ξ F G K s P head tail}
      {hs : StmtCert b (Γ:=Γ) (Δ:=Δ) F G s head} {hp : ProgCert b (Γ:=Δ) (Δ:=Ξ) G K P tail}
      {σ amount} (demand : StmtDemand hs σ amount) : Demand (.cons hs hp) σ amount
  | tail {Γ Δ Ξ F G K s P head tail}
      {hs : StmtCert b (Γ:=Γ) (Δ:=Δ) F G s head} {hp : ProgCert b (Γ:=Δ) (Δ:=Ξ) G K P tail}
      {σ : State C Γ} {out : Solidity.Out C σ.H Δ} {amount spent}
      (run : s.run σ=.ok out) (cost : StmtCost hs σ out amount) (demand : Demand hp out.st spent) :
      Demand (.cons hs hp) σ (amount+spent)
end

mutual
private def stmtneedM {b Γ Δ F G s code} : StmtCert (C:=C) b (Γ:=Γ) (Δ:=Δ) F G s code → Nat
  | .base cert => cert.need
  | .block cert => max Γ.length (progneedM cert)
  | .ite _ yes no => max Γ.length (max (progneedM yes) (progneedM no))
  | .loop _ _ cert _ => max Γ.length (progneedM cert)
termination_by structural hs => hs
private def progneedM {b Γ Δ F G P code} : ProgCert (C:=C) b (Γ:=Γ) (Δ:=Δ) F G P code → Nat
  | .nil _ => Γ.length
  | .cons hs hp => max (stmtneedM hs) (progneedM hp)
termination_by structural hp => hp
end

@[implemented_by stmtneedM]
def StmtCert.need {b Γ Δ F G s code} (hs : StmtCert (C:=C) b (Γ:=Γ) (Δ:=Δ) F G s code) : Nat := by
  induction hs using StmtCert.rec (motive_2 := fun F G x code _=>Nat) with
  | base cert=>exact cert.need
  | @block Γ Δ F G body code cert ih=>exact max Γ.length ih
  | @ite Γ Δ Ξ F G K c yes no cond lc rc hc ht he iht ihe=>exact max Γ.length (max iht ihe)
  | @loop Γ Δ F G c body cond code a hc cert stable ih=>exact max Γ.length ih
  | @nil Γ F=>exact Γ.length
  | cons hs hp ihs ihp=>exact max ihs ihp

@[implemented_by progneedM]
def ProgCert.need {b Γ Δ F G P code} (hp : ProgCert (C:=C) b (Γ:=Γ) (Δ:=Δ) F G P code) : Nat := by
  induction hp using ProgCert.rec (motive_1 := fun F G x code _=>Nat) with
  | base cert=>exact cert.need
  | @block Γ Δ F G body code cert ih=>exact max Γ.length ih
  | @ite Γ Δ Ξ F G K c yes no cond lc rc hc ht he iht ihe=>exact max Γ.length (max iht ihe)
  | @loop Γ Δ F G c body cond code a hc cert stable ih=>exact max Γ.length ih
  | @nil Γ F=>exact Γ.length
  | cons hs hp ihs ihp=>exact max ihs ihp

private theorem stmtneed_eq {b Γ Δ F G s code} (hs : StmtCert (C:=C) b (Γ:=Γ) (Δ:=Δ) F G s code) :
    hs.need=stmtneedM hs := by
  induction hs using StmtCert.rec
    (motive_2 := fun F G P code cert=>cert.need=progneedM cert) with
  | base cert=>rfl
  | block cert ih=>change max _ cert.need=max _ (progneedM cert);rw [ih]
  | ite hc ht he iht ihe=>change max _ (max ht.need he.need)=max _ (max (progneedM ht) (progneedM he));rw [iht,ihe]
  | loop a hc cert stable ih=>change max _ cert.need=max _ (progneedM cert);rw [ih]
  | nil F=>rfl
  | cons hs hp ihs ihp=>change max hs.need hp.need=max (stmtneedM hs) (progneedM hp);rw [ihs,ihp]

private theorem progneed_eq {b Γ Δ F G P code} (hp : ProgCert (C:=C) b (Γ:=Γ) (Δ:=Δ) F G P code) :
    hp.need=progneedM hp := by
  induction hp using ProgCert.rec
    (motive_1 := fun F G s code cert=>cert.need=stmtneedM cert) with
  | base cert=>rfl
  | block cert ih=>change max _ cert.need=max _ (progneedM cert);rw [ih]
  | ite hc ht he iht ihe=>change max _ (max ht.need he.need)=max _ (max (progneedM ht) (progneedM he));rw [iht,ihe]
  | loop a hc cert stable ih=>change max _ cert.need=max _ (progneedM cert);rw [ih]
  | nil F=>rfl
  | cons hs hp ihs ihp=>change max hs.need hp.need=max (stmtneedM hs) (progneedM hp);rw [ihs,ihp]


/-- Actual compiler metadata, not supplied output laws. -/
def profile {b Γ Δ F G P code} (cert : ProgCert (C:=C) b (Γ:=Γ) (Δ:=Δ) F G P code) :
    RecursiveLift.BodyProfile b F P code :=
  ⟨G,cert.need,fun σ out amount=>Cost cert σ out amount,fun σ amount=>Demand cert σ amount⟩

def Room {b : Nat} {Γ Δ F G P code} (cert : ProgCert (C:=C) b (Γ:=Γ) (Δ:=Δ) F G P code)
    (frame : Nat) (σ : State C Γ) (base : Nat → Fin W) (m : Machine) : Prop :=
  ∀ amount,Demand cert σ amount → AllocationInput b frame amount σ base m

end Solidity.Evm.Memory.Recursive
