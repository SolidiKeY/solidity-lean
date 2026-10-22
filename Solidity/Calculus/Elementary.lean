import Solidity.Calculus.ChainGen

/-! Elementary capture and update laws for checked traces. Unlike CaptureAll,
each rule below introduces exactly one declaration. No replacement is justified
merely by the label of the old macro step. These are Lean semantic refinement
laws, not additional SolKey taclets. -/
namespace Solidity.Elementary
open Solidity Modality
variable {C : Contract} {Γ : Ctx} {m : Modality}

/-- Capture one value before resolving its destination. This is valid even
when the original value is simple: receiver/index evaluation may change it. -/
theorem captureValue (m : Modality) {p : PrimTy} (lhs : VHole C Γ p) (e : Val C Γ p) (x : Var)
    {Γ₁ Γ₀ : Ctx} (ω : Prog C Γ Γ₁) (κ : Frames C Γ₁ Γ₀) (φ : Fml C Γ₀) :
    Fml.Leads (.modal m (.cons (lhs.fill e) ω) κ φ)
      ((Premise.capture p x e (lhs.up.fill (.simple (.local .here)))).fml m ω κ φ) :=
  fun σ => (VHole.sound_capture σ lhs e x).sound ω κ φ

/-- After the value is captured, capture only the receiver. Both remaining
expressions are weakened from the original context, so neither can mutate the
fresh source local. -/
theorem captureStorageReceiver {R : RefTy} {kp p : PrimTy}
    (it : IndexTy R kp (.prim p)) (b : SPath C Γ (.ref R)) (i : Val C Γ kp) (x : Var)
    (σ : State C (.val p :: Γ)) :
    Premise.Runs m
      (.assign (.index it b.up i.up) (.val (.simple (.local .here))))
      (.captureSP x b.up
        (.assign (.index it (.alias .here) i.up.up)
          (.val (.simple (.local (.there .here)))))) σ := by
  refine Premise.sound_captureSPPushed σ ?_ ?_
  · intro q hq
    exact TRun.assign_pushT σ (t := .alias R) (some q)
      (.index it (.alias .here) i.up.up) (.val (.simple (.local (.there .here))))
      (.index it b.up i.up) (.val (.simple (.local .here)))
      (Src.valueT_up σ _ (.val (.simple (.local .here))))
      (by simp only [Loc.resolveT, Val.evalT_up, hq]; rfl)
  · intro h hh
    change ((TRun.assign (.index it b.up i.up)
      (.val (.simple (.local .here))) σ).map (·.st)) = .error h
    simp only [TRun.assign, Src.valueT, Val.evalT, Loc.resolveT, hh]
    rfl
/-- A field receiver captured alone, after the source value is protected. -/
theorem captureStorageFieldReceiver {s : Solidity.Name} {p : PrimTy}
    (b : SPath C Γ (.struct s)) (f : Solidity.Name)
    (hf : C.fieldType s f = some (.prim p)) (x : Var)
    (σ : State C (.val p :: Γ)) :
    Premise.Runs m (.assign (.field b.up f hf) (.val (.simple (.local .here))))
      (.captureSP x b.up
        (.assign (.field (.alias .here) f hf) (.val (.simple (.local (.there .here)))))) σ := by
  refine Premise.sound_captureSPPushed σ ?_ ?_
  · intro q hq
    exact TRun.assign_pushT σ (t := .alias (.struct s)) (some q)
      (.field (.alias .here) f hf) (.val (.simple (.local (.there .here))))
      (.field b.up f hf) (.val (.simple (.local .here)))
      (Src.valueT_up σ _ (.val (.simple (.local .here))))
      (by simp only [Loc.resolveT, hq]; rfl)
  · intro h hh
    change ((TRun.assign (.field b.up f hf) (.val (.simple (.local .here))) σ).map (·.st)) = .error h
    simp only [TRun.assign, Src.valueT, Val.evalT, Loc.resolveT, hh]
    rfl

/-- Once source and receiver are captured, introduce only the index local. -/
theorem captureStorageIndex {R : RefTy} {kp p : PrimTy}
    (it : IndexTy R kp (.prim p)) (i : Val C Γ kp) (x : Var)
    (σ : State C (.alias R :: .val p :: Γ)) :
    Premise.Runs m
      (.assign (.index it (.alias .here) i.up.up)
        (.val (.simple (.local (.there .here)))))
      (.capture kp x i.up.up
        (.assign (.index it (.alias (.there .here)) (.simple (.local .here)))
          (.val (.simple (.local (.there (.there .here))))))) σ := by
  refine Premise.sound_capturePushed σ ?_ ?_
  · intro v hv
    exact TRun.assign_pushT σ (t := .val kp) v
      (.index it (.alias (.there .here)) (.simple (.local .here)))
      (.val (.simple (.local (.there (.there .here)))))
      (.index it (.alias .here) i.up.up)
      (.val (.simple (.local (.there .here))))
      (Src.valueT_up σ _ (.val (.simple (.local (.there .here)))))
      (by simp only [Loc.resolveT, Val.evalT, Simple.evalT, SPath.resolveT, State.push, TEnv.get, hv]
          cases σ.env.fst <;> rfl)
  · intro h hh
    have he : h = .revert := Val.evalT_revertOnly σ i.up.up h hh
    subst h
    change ((TRun.assign (.index it (.alias .here) i.up.up)
      (.val (.simple (.local (.there .here)))) σ).map (·.st)) = .error .revert
    simp only [TRun.assign, Src.valueT, Val.evalT, Loc.resolveT, hh, SPath.resolveT]
    cases (TEnv.get (.here : Idx _ (.alias R)) σ.env) <;> rfl
/-- Capture a memory-array receiver separately from source and index. -/
theorem captureMemoryReceiver {R : RefTy} {p : PrimTy}
    (a : ArrTy R (.prim p)) (b : MPath C Γ (.ref R)) (i : Val C Γ .uint) (x : Var)
    (σ : State C (.val p :: Γ)) :
    Premise.Runs m (.assignMem (.index a b.up i.up) (.val (.simple (.local .here))))
      (.captureMV x b.up
        (.assignMem (.index a (.var .here b.mapFree) i.up.up)
          (.val (.simple (.local (.there .here)))))) σ := by
  refine Premise.sound_captureMVPushed σ ?_ ?_
  · intro r hr
    exact TRun.assignMem_pushT σ (t := .mem R) (some r)
      (.index a (.var .here b.mapFree) i.up.up) (.index a b.up i.up)
      (.val (.simple (.local (.there .here)))) (.val (.simple (.local .here)))
      (by simp only [MLoc.addrT, Val.evalT_up, hr]; rfl)
      (MSrc.mvalT_up σ _ (.val (.simple (.local .here))))
  · intro h hh
    change ((TRun.assignMem (.index a b.up i.up) (.val (.simple (.local .here))) σ).map (·.st)) = .error h
    simp only [TRun.assignMem, MSrc.mvalT, Val.evalT, MLoc.addrT, hh]
    rfl

/-- Capture only the memory-array index after source and receiver. -/
theorem captureMemoryIndex {R : RefTy} {p : PrimTy}
    (a : ArrTy R (.prim p)) (hm : (Ty.ref R).mapFree = true)
    (i : Val C Γ .uint) (x : Var) (σ : State C (.mem R :: .val p :: Γ)) :
    Premise.Runs m
      (.assignMem (.index a (.var .here hm) i.up.up)
        (.val (.simple (.local (.there .here)))))
      (.capture .uint x i.up.up
        (.assignMem (.index a (.var (.there .here) hm) (.simple (.local .here)))
          (.val (.simple (.local (.there (.there .here))))))) σ := by
  refine Premise.sound_capturePushed σ ?_ ?_
  · intro v hv
    exact TRun.assignMem_pushT σ (t := .val .uint) v
      (.index a (.var (.there .here) hm) (.simple (.local .here)))
      (.index a (.var .here hm) i.up.up)
      (.val (.simple (.local (.there (.there .here)))))
      (.val (.simple (.local (.there .here))))
      (by simp only [MLoc.addrT, MPath.mvalT, Val.evalT, Simple.evalT, State.push, TEnv.get, hv]
          cases σ.env.fst <;> rfl)
      (MSrc.mvalT_up σ _ (.val (.simple (.local (.there .here)))))
  · intro h hh
    have he : h = .revert := Val.evalT_revertOnly σ i.up.up h hh
    subst h
    change ((TRun.assignMem (.index a (.var .here hm) i.up.up)
      (.val (.simple (.local (.there .here)))) σ).map (·.st)) = .error .revert
    simp only [TRun.assignMem, MSrc.mvalT, Val.evalT, MLoc.addrT, hh, MPath.mvalT]
    cases (TEnv.get (.here : Idx _ (.mem R)) σ.env) <;> rfl

/-- Capture a memory reference source independently of its destination. -/
theorem captureMemoryReference {R : RefTy} (l : MLoc C Γ (.ref R))
    (src : MPath C Γ (.ref R)) (x : Var) (σ : State C Γ) :
    Premise.Runs m (.assignMem l (.ref src))
      (.captureMV x src (.assignMem l.up (.ref (.var .here src.mapFree)))) σ := by
  refine Premise.sound_captureMVPushed σ ?_ ?_
  · intro r hr
    exact TRun.assignMem_pushT σ (t := .mem R) (some r)
      l.up l (.ref (.var .here src.mapFree)) (.ref src)
      (MLoc.addrT_up σ _ l)
      (by simp only [MSrc.mvalT, MPath.mvalT, hr]; rfl)
  · intro h hh
    change ((TRun.assignMem l (.ref src) σ).map (·.st)) = .error h
    simp only [TRun.assignMem, MSrc.mvalT, hh]
    rfl

/-- Lift an already checked elementary pair through an enclosing update. -/
theorem underUpdate {Δ : Ctx} (u : Modality) (U : Upd C Γ Δ)
    {a b : Fml C Δ} (h : Fml.Leads a b) :
    Fml.Leads (.upd u U a) (.upd u U b) := holds_upd_mono h

theorem underBind (u : Modality) (x : Var) (t : LTy)
    {a b : Fml C (t :: Γ)} (h : Fml.Leads a b) :
    Fml.Leads (.bind u x t a) (.bind u x t b) :=
  fun σ hp => Modality.forallB_imp (fun v hv => h (σ.push v) hv) hp

theorem underAll (x : Var) (p : PrimTy)
    {a b : Fml C (.val p :: Γ)} (h : Fml.Leads a b) :
    Fml.Leads (.all x p a) (.all x p b) := fun σ hp v => h (σ.push v) (hp v)

/-- Preserve the precondition while refining its consequent. -/
theorem underImp (pre : Fml C Γ) {a b : Fml C Γ} (h : Fml.Leads a b) :
    Fml.Leads (.imp pre a) (.imp pre b) := fun σ hp ha => h σ (hp ha)

theorem underAndLeft (right : Fml C Γ) {a b : Fml C Γ} (h : Fml.Leads a b) :
    Fml.Leads (.and a right) (.and b right) := fun σ hp => ⟨h σ hp.1, hp.2⟩

theorem underAndRight (left : Fml C Γ) {a b : Fml C Γ} (h : Fml.Leads a b) :
    Fml.Leads (.and left a) (.and left b) := fun σ hp => ⟨hp.1, h σ hp.2⟩

theorem underHavoc {a b : Fml C Γ} (h : Fml.Leads a b) :
    Fml.Leads (.havoc a) (.havoc b) := fun σ hp st nt sb => h (σ.havoc st nt sb) (hp st nt sb)

theorem underAnon (xs : List ((t : LTy) × Idx Γ t))
    {a b : Fml C Γ} (h : Fml.Leads a b) :
    Fml.Leads (.anon xs a) (.anon xs b) := fun σ hp v => h (σ.anon xs v) (hp v)

theorem receiverLeads (m : Modality) {R : RefTy} {kp p : PrimTy}
    (it : IndexTy R kp (.prim p)) (b : SPath C Γ (.ref R)) (i : Val C Γ kp) (x : Var)
    {Γ₁ Γ₀ : Ctx} (ω : Prog C (.val p :: Γ) Γ₁)
    (κ : Frames C Γ₁ Γ₀) (φ : Fml C Γ₀) :
    Fml.Leads (.modal m (.cons (.assign (.index it b.up i.up)
      (.val (.simple (.local .here)))) ω) κ φ)
      ((Premise.captureSP x b.up (.assign (.index it (.alias .here) i.up.up)
        (.val (.simple (.local (.there .here)))))).fml m ω κ φ) :=
  fun σ => (captureStorageReceiver it b i x σ).sound ω κ φ

theorem fieldReceiverLeads (m : Modality) {s : Solidity.Name} {p : PrimTy}
    (b : SPath C Γ (.struct s)) (f : Solidity.Name)
    (hf : C.fieldType s f = some (.prim p)) (x : Var)
    {Γ₁ Γ₀ : Ctx} (ω : Prog C (.val p :: Γ) Γ₁) (κ : Frames C Γ₁ Γ₀) (φ : Fml C Γ₀) :
    Fml.Leads (.modal m (.cons (.assign (.field b.up f hf)
      (.val (.simple (.local .here)))) ω) κ φ)
      ((Premise.captureSP x b.up (.assign (.field (.alias .here) f hf)
        (.val (.simple (.local (.there .here)))))).fml m ω κ φ) :=
  fun σ => (captureStorageFieldReceiver b f hf x σ).sound ω κ φ

/-- A single memory-field receiver capture, with the source already saved. -/
theorem memoryFieldReceiverLeads (m : Modality) {s : Solidity.Name} {p : PrimTy}
    (b : MPath C Γ (.struct s)) (f : Solidity.Name)
    (hf : C.fieldType s f = some (.prim p)) (x : Var)
    {Γ₁ Γ₀ : Ctx} (ω : Prog C (.val p :: Γ) Γ₁) (κ : Frames C Γ₁ Γ₀) (φ : Fml C Γ₀) :
    Fml.Leads (.modal m (.cons (.assignMem (.field b.up f hf)
      (.val (.simple (.local .here)))) ω) κ φ)
      ((Premise.captureMV x b.up (.assignMem (.field (.var .here b.mapFree) f hf)
        (.val (.simple (.local (.there .here)))))).fml m ω κ φ) :=
  fun σ => (sound_memFieldWriteRecv σ b.up b.mapFree f hf
    (.val (.simple (.local .here))) x).sound ω κ φ

theorem memoryReceiverLeads (m : Modality) {R : RefTy} {p : PrimTy}
    (a : ArrTy R (.prim p)) (b : MPath C Γ (.ref R)) (i : Val C Γ .uint) (x : Var)
    {Γ₁ Γ₀ : Ctx} (ω : Prog C (.val p :: Γ) Γ₁) (κ : Frames C Γ₁ Γ₀) (φ : Fml C Γ₀) :
    Fml.Leads (.modal m (.cons (.assignMem (.index a b.up i.up)
      (.val (.simple (.local .here)))) ω) κ φ)
      ((Premise.captureMV x b.up (.assignMem (.index a (.var .here b.mapFree) i.up.up)
        (.val (.simple (.local (.there .here)))))).fml m ω κ φ) :=
  fun σ => (captureMemoryReceiver a b i x σ).sound ω κ φ

theorem memoryIndexLeads (m : Modality) {R : RefTy} {p : PrimTy}
    (a : ArrTy R (.prim p)) (hm : (Ty.ref R).mapFree = true)
    (i : Val C Γ .uint) (x : Var)
    {Γ₁ Γ₀ : Ctx} (ω : Prog C (.mem R :: .val p :: Γ) Γ₁)
    (κ : Frames C Γ₁ Γ₀) (φ : Fml C Γ₀) :
    Fml.Leads (.modal m (.cons (.assignMem (.index a (.var .here hm) i.up.up)
      (.val (.simple (.local (.there .here))))) ω) κ φ)
      ((Premise.capture .uint x i.up.up
        (.assignMem (.index a (.var (.there .here) hm) (.simple (.local .here)))
          (.val (.simple (.local (.there (.there .here))))))).fml m ω κ φ) :=
  fun σ => (captureMemoryIndex a hm i x σ).sound ω κ φ

theorem memoryReferenceLeads (m : Modality) {R : RefTy}
    (l : MLoc C Γ (.ref R)) (src : MPath C Γ (.ref R)) (x : Var)
    {Γ₁ Γ₀ : Ctx} (ω : Prog C Γ Γ₁) (κ : Frames C Γ₁ Γ₀) (φ : Fml C Γ₀) :
    Fml.Leads (.modal m (.cons (.assignMem l (.ref src)) ω) κ φ)
      ((Premise.captureMV x src (.assignMem l.up (.ref (.var .here src.mapFree)))).fml m ω κ φ) :=
  fun σ => (captureMemoryReference l src x σ).sound ω κ φ

theorem memoryRefFieldReceiverLeads (m : Modality) {s : Solidity.Name} {R : RefTy}
    (b : MPath C Γ (.struct s)) (src : MPath C Γ (.ref R)) (f : Solidity.Name)
    (hf : C.fieldType s f = some (.ref R)) (x : Var)
    {Γ₁ Γ₀ : Ctx} (ω : Prog C (.mem R :: Γ) Γ₁) (κ : Frames C Γ₁ Γ₀) (φ : Fml C Γ₀) :
    Fml.Leads (.modal m (.cons (.assignMem (.field b.up f hf)
      (.ref (.var .here src.mapFree))) ω) κ φ)
      ((Premise.captureMV x b.up (.assignMem (.field (.var .here b.mapFree) f hf)
        (.ref (.var (.there .here) src.mapFree)))).fml m ω κ φ) :=
  fun σ => (sound_memFieldWriteRecv σ b.up b.mapFree f hf
    (.ref (.var .here src.mapFree)) x).sound ω κ φ

theorem indexLeads (m : Modality) {R : RefTy} {kp p : PrimTy}
    (it : IndexTy R kp (.prim p)) (i : Val C Γ kp) (x : Var)
    {Γ₁ Γ₀ : Ctx} (ω : Prog C (.alias R :: .val p :: Γ) Γ₁)
    (κ : Frames C Γ₁ Γ₀) (φ : Fml C Γ₀) :
    Fml.Leads (.modal m (.cons (.assign (.index it (.alias .here) i.up.up)
      (.val (.simple (.local (.there .here))))) ω) κ φ)
      ((Premise.capture kp x i.up.up
        (.assign (.index it (.alias (.there .here)) (.simple (.local .here)))
          (.val (.simple (.local (.there (.there .here))))))).fml m ω κ φ) :=
  fun σ => (captureStorageIndex it i x σ).sound ω κ φ
/-- The Lean elementary left-operand capture used with literal right operand 1. -/
theorem binaryLeftLeads (m : Modality) {p p' : PrimTy} (i : Idx Γ (.val p))
    (op : BinOp) (ha : op.accepts p' = true) (hq : op.ret p' = p)
    (a b : Val C Γ p') (x : Var)
    {Γ₁ Γ₀ : Ctx} (ω : Prog C Γ Γ₁) (κ : Frames C Γ₁ Γ₀) (φ : Fml C Γ₀) :
    Fml.Leads (.modal m (.cons (.assignLocal i (.binop op ha hq a b)) ω) κ φ)
      ((Premise.capture p' x a (.assignLocal i.there
        (.binop op ha hq (.simple (.local .here)) b.up))).fml m ω κ φ) :=
  fun σ => (sound_binopUnfoldLeft σ i op ha hq a b x).sound ω κ φ

/-- Explicit mode lets a long verified merge be decomposed without changing
its binder-reordering plan between individual pairs. -/
theorem rawAbsorbAllLeads (m : Modality) {Γ Δ E : Ctx}
    (U : Upd C Γ Δ) (φ : Fml C Δ) (V : Upd C Δ E)
    (W : Upd C Γ E) (χ : Fml C E)
    (hAbs : Fml.absorbBinds φ = .upd m V χ)
    (hMerge : U.mergeK? V = some W) :
    Fml.Leads (.upd m U φ) (.upd m W χ) :=
  fun σ hp => holds_upd_mono
    (fun τ hτ => Fml.absorbBinds_holds φ τ (hAbs.symm ▸ hτ)) σ
    (holds_upd_mergeK hMerge σ hp)

def absorbForRaw {Γ Δ : Ctx} {t : LTy} (V : Upd C (t :: Γ) Δ) (x : Var) : Option (Upd C Γ Δ) :=
  V.absorb x

theorem rawSingleAbsorbLeads (m m' : Modality) {Γ Δ E : Ctx} {t : LTy}
    (U : Upd C Γ Δ) (x : Var) (V : Upd C (t :: Δ) E)
    (V' : Upd C Δ E) (W : Upd C Γ E) (χ : Fml C E)
    (hAbs : V.absorb x = some V') (hMerge : U.mergeK? V' = some W) :
    Fml.Leads (.upd m U (.bind m' x t (.upd m V χ))) (.upd m W χ) :=
  fun σ hp => holds_upd_mono
    (fun τ hτ => holds_bind_absorb hAbs τ hτ) σ (holds_upd_mergeK hMerge σ hp)

def liftForRaw {Γ Δ : Ctx} (U : Upd C Γ Δ) (t : LTy) : Option (Upd C (t :: Γ) (t :: Δ)) :=
  U.liftG? (t := t)

def liftAllowedForRaw {Γ Δ : Ctx} (U : Upd C Γ Δ) (t : LTy) : Bool :=
  t.notMem || U.keepsNext

theorem rawUnderLiftLeads (m m' : Modality) {Γ Δ : Ctx}
    (U : Upd C Γ Δ) (t : LTy) (U' : Upd C (t :: Γ) (t :: Δ)) (x : Var)
    (φ : Fml C (t :: Δ)) (χ : Fml C (t :: Γ))
    (hLift : U.liftG? (t := t) = some U')
    (hAllowed : (t.notMem || U.keepsNext) = true)
    (h : Fml.Leads (.upd m U' φ) χ) :
    Fml.Leads (.upd m U (.bind m' x t φ)) (.bind m' x t χ) :=
  fun σ hp => Fml.upd_bind_of_liftG hLift hAllowed σ
    (Modality.forallB_imp (fun _ h' => h _ h') hp)

theorem dropStateLeads (m : Modality) {Γ Δ : Ctx}
    (U : Upd C Γ Δ) (φ : Fml C Δ) :
    Fml.Leads (.upd m U φ) (.upd m (U.dropSh [] []) φ) :=
  fun σ hp => holds_upd_dropSh σ hp

def mergePairMode (C : Contract) (reorder : Bool) (k : Nat) : FmlRw C where
  apply := fun φ => φ.mergeAtP reorder k
  sound := fun h σ hp => Fml.mergeAtP_sound reorder k _ h σ hp

def mergeRunMode (C : Contract) (reorder : Bool) (k n : Nat) : FmlRw C where
  apply := fun φ => φ.mergeRunP reorder k (n + 1)
  sound := fun h σ hp => Fml.mergeRunP_sound reorder k (n + 1) _ h σ hp

end Solidity.Elementary
