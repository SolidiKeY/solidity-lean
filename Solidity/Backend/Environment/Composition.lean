import Solidity.Backend.Environment.Namespace

/-!
# Intrinsic value certificates and local slice composition

No source IR is added: certificates read existing `Val C Γ .uint`, `State C Γ`
and `Val.evalT`. The target is a list of committed Backend instructions with
independently defined local semantics. CALL, resources and world execution
composition remain outside this slice.
-/
namespace Solidity.Backend.Environment

/-- One common target slice for environment, PUSH/MSTORE8 and hash/arithmetic. -/
def sliceStep (f : Frame) (i : Instr) (s : Slice) : Option Slice :=
  match i with
  | .op .ADDRESS | .op .CALLER | .op .CALLVALUE | .op .TIMESTAMP |
    .op .BALANCE | .op .SELFBALANCE =>
      (step f i s.stack).map fun stack => { s with stack := stack }
  | .op .MSTORE8 => dataStep i s
  | _ => cryptoStep i s

def runSlice (f : Frame) : List Instr → Slice → Option Slice
  | [], s => some s
  | i :: code, s => (sliceStep f i s).bind (runSlice f code)

theorem runSlice_append (f : Frame) (a b : List Instr) (s : Slice) :
    runSlice f (a ++ b) s = (runSlice f a s).bind (runSlice f b) := by
  induction a generalizing s with
  | nil => rfl
  | cons i a ih =>
    simp only [List.cons_append, runSlice, Option.bind_assoc]
    cases sliceStep f i s with
    | none => rfl
    | some t => exact ih t

def cryptoInstruction : Instr → Bool
  | .push .. => true
  | .op .KECCAK256 | .op .SUB | .op .MSTORE | .op .SHR | .op .SHL => true
  | _ => false

def dataInstruction : Instr → Bool
  | .push .. | .op .MSTORE8 => true
  | _ => false

theorem sliceStep_crypto (f : Frame) (i : Instr) (s : Slice)
    (h : cryptoInstruction i = true) : sliceStep f i s = cryptoStep i s := by
  cases i with
  | push n imm => rfl
  | op o => cases o <;> first | rfl | contradiction

theorem sliceStep_data (f : Frame) (i : Instr) (s : Slice)
    (h : dataInstruction i = true) : sliceStep f i s = dataStep i s := by
  cases i with
  | push n imm => rfl
  | op o => cases o <;> first | rfl | contradiction

theorem runSlice_crypto (f : Frame) (code : List Instr) (s : Slice)
    (h : code.all cryptoInstruction = true) : runSlice f code s = runCrypto code s := by
  induction code generalizing s with
  | nil => rfl
  | cons i code ih =>
    have hh : (i :: code).all cryptoInstruction = true := h
    simp only [List.all_cons, Bool.and_eq_true] at hh
    simp only [runSlice, runCrypto, sliceStep_crypto f i s hh.1]
    cases cryptoStep i s with
    | none => rfl
    | some t => exact ih t hh.2

theorem runSlice_data (f : Frame) (code : List Instr) (s : Slice)
    (h : code.all dataInstruction = true) : runSlice f code s = runData code s := by
  induction code generalizing s with
  | nil => rfl
  | cons i code ih =>
    have hh : (i :: code).all dataInstruction = true := h
    simp only [List.all_cons, Bool.and_eq_true] at hh
    simp only [runSlice, runData, sliceStep_data f i s hh.1]
    cases dataStep i s with
    | none => rfl
    | some t => exact ih t hh.2

theorem keccak_supported (offset length : W256) :
    (keccakCode offset length).all cryptoInstruction = true := rfl

theorem namespace_supported (offset length scratch : W256) :
    (namespaceCode offset length scratch).all cryptoInstruction = true := rfl

theorem materialize_supported (offset : Nat) (bs : List UInt8) :
    (materialize offset bs).all dataInstruction = true := by
  induction bs generalizing offset with
  | nil => rfl
  | cons b bs ih =>
    simp only [materialize, List.all_append, byteCode, List.all_cons, List.all_nil,
      constant, dataInstruction, Bool.true_and, ih]

theorem slice_select (f : Frame) (k : EnvKey) (s : Slice) :
    runSlice f [select k] s = some { s with stack := observe f k :: s.stack } := by
  cases k <;> rfl

theorem slice_constant (f : Frame) (width : Fin 33) (v : Fin (256 ^ width.val)) (s : Slice) :
    runSlice f [constant width v] s =
      some { s with stack := lenU v.val (constant_bound width v) :: s.stack } := by
  change (cryptoStep (constant width v) s).bind (fun t => some t) = _
  rw [cryptoStep_constant]
  rfl

/-- A compiler-independent certificate over an existing intrinsic expression.
It contains an actual construction/proof, not an assumed desired result. -/
structure ValueCertificate {C : Contract} {Γ : Ctx} (σ : State C Γ)
    (e : Val C Γ .uint) (f : Frame) (code : List Instr) (memoryIn : Memory) where
  value : Word
  memoryOut : Memory
  source : e.evalT σ = .ok value
  target : ∀ tail, runSlice f code ⟨tail, memoryIn⟩ = some ⟨value :: tail, memoryOut⟩

def environmentCertificate {C : Contract} {Γ : Ctx} (σ : State C Γ) (f : Frame)
    (h : Represents f σ) (k : EnvKey) (m : Memory) :
    ValueCertificate σ (.simple (.env k rfl)) f [select k] m :=
  { value := observe f k
    memoryOut := m
    source := (intrinsic_correct h k []).1
    target := fun tail => slice_select f k ⟨tail, m⟩ }

def literalCertificate {C : Contract} {Γ : Ctx} (σ : State C Γ) (f : Frame)
    (width : Fin 33) (v : Fin (256 ^ width.val)) (m : Memory) :
    ValueCertificate σ (.simple (.lit (lenU v.val (constant_bound width v)).1
      (lenU v.val (constant_bound width v)).2)) f [constant width v] m :=
  { value := lenU v.val (constant_bound width v)
    memoryOut := m
    source := rfl
    target := fun tail => slice_constant f width v ⟨tail, m⟩ }

def hashCertificate {C : Contract} {Γ : Ctx} {R : RefTy}
    (σ : State C Γ) (b : MPath C Γ (.ref R)) (r : HRef σ.H R)
    (evaluated : b.mvalT σ = .ok r) (f : Frame) (offset length : W256) (m : Memory)
    (input : HashInput ⟨[], m⟩ offset length (MObj.words R (σ.heap.get r))) :
    ValueCertificate σ (.hash .keccak b rfl) f (keccakCode offset length) m :=
  { value := σ.heap.hash .keccak r
    memoryOut := m
    source := (intrinsic_keccak σ b r evaluated offset length ⟨[], m⟩ input).1
    target := fun tail => by
      rw [runSlice_crypto f _ _ (keccak_supported offset length)]
      exact (intrinsic_keccak σ b r evaluated offset length ⟨tail, m⟩
        ⟨input.fits, input.bytes⟩).2 }

/-- Source sequencing reads the existing intrinsic denotation left to right;
no part of this denotation mentions generated code. -/
def evalValues {C : Contract} {Γ : Ctx} (σ : State C Γ) :
    List (Val C Γ .uint) → TRes (List Word)
  | [] => .ok []
  | e :: es => do
      let value ← e.evalT σ
      let values ← evalValues σ es
      pure (value :: values)

structure ValuesCertificate {C : Contract} {Γ : Ctx} (σ : State C Γ)
    (es : List (Val C Γ .uint)) (f : Frame) (code : List Instr) (memoryIn : Memory) where
  values : List Word
  memoryOut : Memory
  source : evalValues σ es = .ok values
  target : ∀ tail, runSlice f code ⟨tail, memoryIn⟩ = some ⟨values.reverse ++ tail, memoryOut⟩

def nilCertificate {C : Contract} {Γ : Ctx} (σ : State C Γ) (f : Frame) (m : Memory) :
    ValuesCertificate σ [] f [] m :=
  { values := [], memoryOut := m, source := rfl, target := fun _ => rfl }

/-- Composition preserves the evaluation schedule and exact stack order,
including a changed target scratch memory between component slices. -/
def consCertificate {C : Contract} {Γ : Ctx} {σ : State C Γ} {e : Val C Γ .uint}
    {es : List (Val C Γ .uint)} {f : Frame} {a b : List Instr} {m : Memory}
    (head : ValueCertificate σ e f a m)
    (rest : ValuesCertificate σ es f b head.memoryOut) :
    ValuesCertificate σ (e :: es) f (a ++ b) m :=
  { values := head.value :: rest.values
    memoryOut := rest.memoryOut
    source := by
      simp only [evalValues, head.source, rest.source, Except.bind, Except.instMonad, Except.pure]
    target := fun tail => by
      rw [runSlice_append, head.target]
      change runSlice f b ⟨head.value :: tail, head.memoryOut⟩ = _
      rw [rest.target]
      simp only [List.reverse_cons, List.append_assoc, List.singleton_append] }

/-- Backfill A fallback: source failure of the first typed statement cannot be
erased, regardless of its unobserved result or the following statement. -/
theorem source_sequence_failure {C : Contract} {Γ Δ Θ : Ctx}
    (first : TStep C Γ Δ) (rest : TStep C Δ Θ) (σ : State C Γ) (halt : THalt)
    (failed : first σ = .error halt) : TRun.seq first rest σ = .error halt := by
  simp only [TRun.seq, failed]

/-- Source success composes through the existing typed intermediate state. -/
theorem source_sequence_success {C : Contract} {Γ Δ Θ : Ctx}
    (first : TStep C Γ Δ) (rest : TStep C Δ Θ) (σ : State C Γ) (out : Out C σ.H Δ)
    (succeeded : first σ = .ok out) :
    TRun.seq first rest σ = (rest out.st).map (fun final => ⟨final.st, out.ext.trans final.ext⟩) := by
  simp only [TRun.seq, succeeded]

end Solidity.Backend.Environment
