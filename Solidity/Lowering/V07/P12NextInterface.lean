import Solidity.Lowering.V07.EffectfulCondition
import Solidity.Lowering.V07.ReferenceCaptureRelated

/-! H26 P12 request-specific dependency contracts, version 1.
Reuse ContextMap and its published local/assignment/capture laws; do not fork
those definitions. Relations below are compiler-independent predicates over
existing worlds/values. No condition/reference compiler or concrete producer
instance is supplied. Fields are pending obligations, not established evidence.
Caller-supplied G/F/expr are existing Source inputs, not producer-selected
semantics. Linking them to actual admitted syntax/P8 origins or H25 exact
authority is an external dependency; this module supplies no origin adapter.
Success/revert clauses do not cover Source fuel/stuck outcomes, admission,
resource adequacy, session failure projection, copy/delete or lifetimes.
Source locals extended below classify a returned reference; they do not claim
execution of a Source declaration. Native errors expose no final state.
initial_nonempty is only an input-alignment obligation, not an execution witness.
Alias reflection is conditional on selected old bindings resolving to some ref;
no nullable-reference, shape or all-old-reference completeness follows.
Compiler independence and shape compatibility require reviewed relation inputs;
the relation types alone cannot enforce those semantic requirements.
-/
namespace Solidity.Lowering.V07.P12NextInterface

abbrev ValueRelation (E : Source.Env) (C : Contract) :=
  (source : Source.St E) → (target : State C []) →
    (τ : Source.STy) → (u : LTy) → Source.Val E.layout τ → u.TDenote C target.H → Prop
abbrev WorldRelation (E : Source.Env) (C : Contract) := Source.St E → State C [] → Prop

/-- Existing ContextMap.Related, indexed by the actual reached worlds so heap
extensions may change the value relation. Relations must not encode compiler
execution or the desired preservation result. -/
def Aligned {E : Source.Env} {C : Contract} {srcΓ : Source.RCtx} {Γ : Ctx}
    (m : ContextMap srcΓ Γ) (values : ValueRelation E C) (worlds : WorldRelation E C)
    (source : Source.EMState E srcΓ) (target : State C Γ) : Prop :=
  worlds source.2 target.glob ∧ m.Related (values source.2 target.glob) source.1 target.env

/-- Request-specific effectful Boolean operand. A G19 consumer may use the
fields conditionally; constructing this record remains the producer's work. -/
structure Condition {E : Source.Env} {C : Contract} {srcΓ : Source.RCtx} {Γ : Ctx}
    (G : Source.Glob E) (F : Source.Fr) (m : ContextMap srcΓ Γ)
    (values : ValueRelation E C) (worlds : WorldRelation E C)
    (expr : Source.RExpr E srcΓ .bool) where
  operand : DeferredSource.Operand C Γ (.prim .bool)
  initial_nonempty : ∃ source target, Aligned m values worlds source target
  success : ∀ (fuel : Nat) (source after : Source.EMState E srcΓ) (target : State C Γ) (choice : Bool),
    Aligned m values worlds source target →
    (Source.evalE G F fuel expr).run source = (.ok (.val (.bool choice)),after) →
    ∃ out : Out C target.H Γ, operand.run target = .ok (out,.prim choice) ∧
      Aligned m values worlds after out.st
  revert : ∀ (fuel : Nat) (source after : Source.EMState E srcΓ) (target : State C Γ) (data : Roadmap.Bytes),
    Aligned m values worlds source target →
    (Source.evalE G F fuel expr).run source = (.error (.revert data),after) →
    operand.run target = .error (THalt.ofData data)

/-- Actual memory-reference capture, not a Src.copyMem snapshot. Native heap
identity is compared by HRef.id even across old reference types. Shape/admission
and heap/world relations are explicit caller/producer prerequisites. -/
structure MemoryCapture {E : Source.Env} {C : Contract} {srcΓ : Source.RCtx} {Γ : Ctx}
    (G : Source.Glob E) (F : Source.Fr) (m : ContextMap srcΓ Γ)
    (values : ValueRelation E C) (worlds : WorldRelation E C)
    (τ : Source.STy) (location : τ.loc? = some .memory)
    (R : RefTy) (mapFree : (Ty.ref R).mapFree = true) (expr : Source.RExpr E srcΓ τ) where
  code : Prog C Γ (.mem R :: Γ)
  initial_nonempty : ∃ source target, Aligned m values worlds source target
  success : ∀ (fuel : Nat) (source after : Source.EMState E srcΓ) (target : State C Γ) (address : Nat),
    Aligned m values worlds source target →
    (Source.evalE G F fuel expr).run source = (.ok (.val (.memRef location address)),after) →
    ∃ (out : Out C target.H (.mem R :: Γ)) (ref : HRef out.st.H R),
      code.run target = .ok out ∧ TEnv.get .here out.st.env = some ref ∧
      (MPath.var .here mapFree : MPath C (.mem R :: Γ) (.ref R)).mvalT out.st = .ok ref ∧
      (m.cons τ (.mem R)).Related (values after.2 out.st.glob)
        (.cons (.memRef location address) after.1) out.st.env ∧
      worlds after.2 out.st.glob ∧
      (∀ (σ : Source.STy) (oldLocation : σ.loc? = some .memory)
        (i : Source.Idx srcΓ σ) (oldR : RefTy) (j : Idx Γ (.mem oldR))
        (oldAddress : Nat) (oldRef : HRef out.st.H oldR),
        m.slot i = ⟨.mem oldR,j⟩ → after.1.get i = .memRef oldLocation oldAddress →
        TEnv.get (.there j) out.st.env = some oldRef →
        (address = oldAddress ↔ ref.id = oldRef.id))
  revert : ∀ (fuel : Nat) (source after : Source.EMState E srcΓ) (target : State C Γ) (data : Roadmap.Bytes),
    Aligned m values worlds source target →
    (Source.evalE G F fuel expr).run source = (.error (.revert data),after) →
    code.run target = .error (THalt.ofData data)

/-- Storage captures preserve a resolved SRef, not its value snapshot. Alias
reflection here concerns logical Source paths and same-native-RefTy SRefs;
it supplies no hashed physical-store representation or cross-shape theorem. -/
structure StorageCapture {E : Source.Env} {C : Contract} {srcΓ : Source.RCtx} {Γ : Ctx}
    (G : Source.Glob E) (F : Source.Fr) (m : ContextMap srcΓ Γ)
    (values : ValueRelation E C) (worlds : WorldRelation E C)
    (τ : Source.STy) (location : τ.loc? = some .storage)
    (R : RefTy) (expr : Source.RExpr E srcΓ τ) where
  code : Prog C Γ (.alias R :: Γ)
  initial_nonempty : ∃ source target, Aligned m values worlds source target
  success : ∀ (fuel : Nat) (source after : Source.EMState E srcΓ) (target : State C Γ) (path : Source.SPath),
    Aligned m values worlds source target →
    (Source.evalE G F fuel expr).run source = (.ok (.val (.storRef location path)),after) →
    ∃ (out : Out C target.H (.alias R :: Γ)) (ref : SRef C (.ref R)),
      code.run target = .ok out ∧ TEnv.get .here out.st.env = some ref ∧
      (SPath.alias .here : SPath C (.alias R :: Γ) (.ref R)).resolveT out.st = .ok ref ∧
      (m.cons τ (.alias R)).Related (values after.2 out.st.glob)
        (.cons (.storRef location path) after.1) out.st.env ∧
      worlds after.2 out.st.glob ∧
      (∀ (σ : Source.STy) (oldLocation : σ.loc? = some .storage)
        (i : Source.Idx srcΓ σ) (j : Idx Γ (.alias R)) (oldPath : Source.SPath) (oldRef : SRef C (.ref R)),
        m.slot i = ⟨.alias R,j⟩ → after.1.get i = .storRef oldLocation oldPath →
        TEnv.get (.there j) out.st.env = some oldRef → (path = oldPath ↔ ref = oldRef))
  revert : ∀ (fuel : Nat) (source after : Source.EMState E srcΓ) (target : State C Γ) (data : Roadmap.Bytes),
    Aligned m values worlds source target →
    (Source.evalE G F fuel expr).run source = (.error (.revert data),after) →
    code.run target = .error (THalt.ofData data)

end Solidity.Lowering.V07.P12NextInterface
