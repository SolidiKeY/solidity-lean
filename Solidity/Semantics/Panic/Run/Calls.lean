import Solidity.Semantics.Panic.Run.Loop

namespace Solidity.Semantics.Panic

abbrev Step (C : Contract) (Γ Δ : Ctx) := (σ : State C Γ) → EvalResult (Out C σ.H Δ)

variable {C : Contract} {Γ : Ctx}

/-- Evaluate typed call arguments in the same order as the original run. -/
def args (σ : State C Γ) : {ps : Ctx} → Args C Γ ps → EvalResult (TEnv C σ.H ps)
  | _, as => Args.casesOn (motive := fun ps _ => EvalResult (TEnv C σ.H ps)) as (pure ())
      (fun as _ _ e => do
        let r ← args σ as
        let v ← value σ e
        pure (v, r))
      (fun as _ _ e => do
        let r ← args σ as
        let v ← path σ e
        pure (some v, r))
      (fun as _ _ e => do
        let r ← args σ as
        let v ← mpath σ e
        pure (some v, r))
  termination_by structural _ as => as

/-- Argument evaluation has a sound local V1 projection, including references. -/
theorem args_erase (σ : State C Γ) {ps : Ctx} (as : Args C Γ ps) :
    erase (args σ as) = as.evalT σ := by
  induction as with
  | nil => rfl
  | snoc as p name e ih =>
    exact erase_bind_congr ih fun _ => erase_bind_congr (value_erase σ e) fun _ => rfl
  | snocStorage as R name e ih =>
    exact erase_bind_congr ih fun _ => erase_bind_congr (path_erase σ e) fun _ => rfl
  | snocMemory as R name e ih =>
    exact erase_bind_congr ih fun _ => erase_bind_congr (mpath_erase σ e) fun _ => rfl

/-- Decode external return words without inventing intrinsic provenance. -/
def decode {H : HTy} : {ρ : Ctx} → Binders ρ → List Semantics.Word →
    EvalResult (TEnv C H ρ × List Semantics.Word)
  | _, bs => Binders.casesOn
      (motive := fun ρ _ => List Semantics.Word → EvalResult (TEnv C H ρ × List Semantics.Word)) bs
      (fun vs => pure ((), vs))
      (fun bs p _ vs => do
        let (e, rest) ← decode bs vs
        match rest with
        | v :: rest => do pure ((← ofOpt (PrimTy.ofWord? p v), e), rest)
        | [] => .error .revert)
  termination_by structural _ bs => bs

/-- This is a local decoder projection, not a whole-program result erasure. -/
theorem decode_erase {H : HTy} {ρ : Ctx} (bs : Binders ρ) (vs : List Semantics.Word) :
    erase (decode (C := C) (H := H) bs vs) = bs.decodeT vs := by
  induction bs generalizing vs with
  | nil => rfl
  | snoc bs p name ih =>
    exact erase_bind_congr (ih vs) fun (e, rest) => by
      cases rest with
      | nil => rfl
      | cons v rest =>
        cases hv : PrimTy.ofWord? p v <;> simp only [ofOpt, hv] <;> rfl

namespace Run

/-- Internal calls retain the complete failure, or restore the caller frame. -/
def call {Γ' ps rs Γf : Ctx} (as : Args C Γ ps) (ret : CallRet Γ rs Γ')
    (hb : Ext (rs ++ ps) Γf) (body : Step C (rs ++ ps) Γf) : Step C Γ Γ' := fun σ => do
  let a ← args σ as
  let o₁ := ret.enterT (σ.withEnv a)
  let o ← body o₁.st
  let e : σ.H <+: o.st.H := o₁.ext.trans o.ext
  pure ⟨o.st.withEnv
    (ret.leaveT (TEnv.wk e Γ σ.env) (TEnv.take rs (TEnv.drop hb o.st.env))), e⟩

/-- No callee halt is rewritten while unwinding an internal call. -/
theorem call_error {Δ ps rs Γf : Ctx} (as : Args C Γ ps) (ret : CallRet Γ rs Δ)
    (hb : Ext (rs ++ ps) Γf) (body : Step C (rs ++ ps) Γf) (σ : State C Γ)
    (a : TEnv C σ.H ps) (halt : Halt Raised) (ha : args σ as = .ok a)
    (failed : body (ret.enterT (σ.withEnv a)).st = .error halt) :
    call as ret hb body σ = .error halt := by
  simp only [call, ha, bind, Except.bind, failed]

def codeWord (code : Code) : Semantics.Word :=
  ⟨(code.code : Int), by cases code <;> decide⟩

/-- Reverting outcomes expose bytes; resource failures remain failures. -/
def haltBytes : Halt Raised → EvalResult (List UInt8)
  | .intrinsic code _ => .ok (Semantics.encodePanic code.code)
  | .externalRevert data | .revertWith data => .ok data
  | .revert => .ok []
  | .exhausted => .error .exhausted
  | .diverge => .error .diverge

/-- Dispatch a reverting callee using its actual code. No oracle is consulted.
External bytes may select a Panic handler but never become an intrinsic origin. -/
def catchHalt {α : Type} (halt : Halt Raised) (err : Unit → EvalResult α)
    (pnc : Semantics.Word → EvalResult α) (other : Unit → EvalResult α) : EvalResult α :=
  match halt with
  | .intrinsic code _ => pnc (codeWord code)
  | .revert => other ()
  | .externalRevert d | .revertWith d =>
    match Semantics.decodeError d with
    | some _ => err ()
    | none => match Semantics.decodePanic d with
      | some code => pnc code
      | none => other ()
  | .exhausted => .error .exhausted
  | .diverge => .error .diverge

theorem catchHalt_intrinsic {α : Type} (code : Code) (origin : Raised)
    (err : Unit → EvalResult α) (pnc : Semantics.Word → EvalResult α) (other : Unit → EvalResult α) :
    catchHalt (.intrinsic code origin) err pnc other = pnc (codeWord code) := rfl

theorem catchHalt_exhausted {α : Type} (err : Unit → EvalResult α)
    (pnc : Semantics.Word → EvalResult α) (other : Unit → EvalResult α) :
    catchHalt .exhausted err pnc other = .error .exhausted := rfl

theorem catchHalt_diverge {α : Type} (err : Unit → EvalResult α)
    (pnc : Semantics.Word → EvalResult α) (other : Unit → EvalResult α) :
    catchHalt .diverge err pnc other = .error .diverge := rfl

/-- Self calls catch the executed callee's halt; other calls use external outcomes.
Handlers start from the caller state on failure, preserving rollback. -/
def tryCall {ρ κ Γ₁ Γ₂ Γ₃ Γ₄ ps Γf : Ctx} (ext : ExtCall C Γ) (rets : Binders ρ)
    (h₁ : Ext (ρ ++ Γ) Γ₁) (ok : Step C (ρ ++ Γ) Γ₁)
    (h₂ : Ext Γ Γ₂) (err : Step C Γ Γ₂) (code : CodeBinder κ)
    (h₃ : Ext (κ ++ Γ) Γ₃) (pnc : Step C (κ ++ Γ) Γ₃)
    (h₄ : Ext Γ Γ₄) (other : Step C Γ Γ₄) (sargs : Args C Γ ps)
    (hs : Ext (ρ ++ ps) Γf) (sbody : Step C (ρ ++ ps) Γf) (self : Bool) : Step C Γ Γ := fun σ =>
  if (ext.addr.evalT σ).1 = 0 then .error .revert else
  let onError := fun (_ : Unit) => (err σ).map fun o => ⟨o.st.drop h₂, o.ext⟩
  let onPanic := fun c =>
    (pnc (σ.withEnv (TEnv.append κ (code.decodeT (H := σ.H) c) σ.env))).map
      fun o => ⟨o.st.drop ((Ext.append Γ κ).trans h₃), o.ext⟩
  let onOther := fun (_ : Unit) => (other σ).map fun o => ⟨o.st.drop h₄, o.ext⟩
  if self && decide ((ext.addr.evalT σ).1 = σ.tx.selfAddress.1) then
    match call sargs (.rets rets.toRet) hs sbody σ with
    | .ok o => (ok o.st).map fun o' =>
      ⟨o'.st.drop ((Ext.append Γ ρ).trans h₁), o.ext.trans o'.ext⟩
    | .error halt => catchHalt halt onError onPanic onOther
  else
    match lookupBy (ext.keyT σ) σ.tx.ext with
    | none => .error .revert
    | some (.ok vs) => do
      let (r, _) ← decode rets vs
      (ok (σ.withEnv (TEnv.append ρ r σ.env))).map fun o =>
        ⟨o.st.drop ((Ext.append Γ ρ).trans h₁), o.ext⟩
    | some (.error _) => onError ()
    | some (.panic c) => onPanic c
    | some (.other _) => onOther ()

/-- The self-call's complete failure selects the handler, independent of the oracle.
Resource failures are covered too, through catchHalt's exhaustive cases. -/
theorem tryCall_self_failure {ρ κ Γ₁ Γ₂ Γ₃ Γ₄ ps Γf : Ctx}
    (ext : ExtCall C Γ) (rets : Binders ρ)
    (h₁ : Ext (ρ ++ Γ) Γ₁) (ok : Step C (ρ ++ Γ) Γ₁)
    (h₂ : Ext Γ Γ₂) (err : Step C Γ Γ₂) (code : CodeBinder κ)
    (h₃ : Ext (κ ++ Γ) Γ₃) (pnc : Step C (κ ++ Γ) Γ₃)
    (h₄ : Ext Γ Γ₄) (other : Step C Γ Γ₄) (sargs : Args C Γ ps)
    (hs : Ext (ρ ++ ps) Γf) (sbody : Step C (ρ ++ ps) Γf)
    (σ : State C Γ) (halt : Halt Raised)
    (nonzero : (ext.addr.evalT σ).1 ≠ 0)
    (self : (ext.addr.evalT σ).1 = σ.tx.selfAddress.1)
    (failed : call sargs (.rets rets.toRet) hs sbody σ = .error halt) :
    tryCall ext rets h₁ ok h₂ err code h₃ pnc h₄ other sargs hs sbody true σ =
      catchHalt halt
        (fun _ => (err σ).map fun o => ⟨o.st.drop h₂, o.ext⟩)
        (fun c => (pnc (σ.withEnv (TEnv.append κ (code.decodeT (H := σ.H) c) σ.env))).map
          fun o => ⟨o.st.drop ((Ext.append Γ κ).trans h₃), o.ext⟩)
        (fun _ => (other σ).map fun o => ⟨o.st.drop h₄, o.ext⟩) := by
  unfold tryCall
  rw [if_neg nonzero]
  simp only [self, decide_true, Bool.true_and, if_true, failed]

/-- Catch-data observes the same self-call outcome as tryCall. -/
def catchBytes {ρ ps Γf : Ctx} (c : ExtCall C Γ) (rets : Binders ρ) (sargs : Args C Γ ps)
    (hs : Ext (ρ ++ ps) Γf) (sbody : Step C (ρ ++ ps) Γf) (self : Bool) (σ : State C Γ) :
    EvalResult (List UInt8) :=
  if (c.addr.evalT σ).1 = 0 then .error .revert else
  if self && decide ((c.addr.evalT σ).1 = σ.tx.selfAddress.1) then
    match call sargs (.rets rets.toRet) hs sbody σ with
    | .ok _ => .error .revert
    | .error halt => haltBytes halt
  else
    match lookupBy (c.keyT σ) σ.tx.ext with
    | some (.error r) => haltBytes (.externalRevert (Semantics.encodeError r))
    | some (.panic p) => haltBytes (.externalRevert (Semantics.encodePanic p.1.toNat))
    | some (.other d) => haltBytes (.externalRevert d)
    | _ => .error .revert

end Run
end Solidity.Semantics.Panic
