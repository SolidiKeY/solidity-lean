import Solidity.Calculus.DecisionSourceChain

/-! # Exact source reasons for nested array literal-instance gaps
Classification inspects existing intrinsic source constructors and the actual
literal-chain certificate. It does not inspect coverage or a verdict and is
not an exhaustive Residue or a universal unknown theorem.
-/
namespace Solidity.Decide.ResidueReason
variable {C : Contract}

inductive ArrayGapKind where
  | belowKey | belowField | elementsStruct | elementsArray
  deriving DecidableEq, Repr

def arrayBelowKeyReason : String :=
  "The general array-cut source bridge for paths reached through mapping keys remains open."
def arrayBelowFieldReason : String :=
  "The general array-cut source bridge for paths reached through fields remains open."
def arrayOfStructReason : String :=
  "The source bridge for a primitive field selected from an array element remains open."
def arrayOfArrayReason : String :=
  "The source bridge for composed outer and inner array reads remains open."

def ArrayGapKind.reason : ArrayGapKind → String
  | .belowKey => arrayBelowKeyReason
  | .belowField => arrayBelowFieldReason
  | .elementsStruct => arrayOfStructReason
  | .elementsArray => arrayOfArrayReason

private def mapAtOp {a b s : Srt} (op : Op2 C a b s) : Bool := by
  apply @Op2.casesOn C (fun A B S op => Bool) a b s op
  case «at» =>
    intro R k V it
    exact @IndexTy.casesOn (fun _ _ _ _ => Bool) R k V it true (fun _ => false)
  all_goals intros; exact false

private def arrayAtOp {a b s : Srt} (op : Op2 C a b s) : Bool := by
  apply @Op2.casesOn C (fun A B S op => Bool) a b s op
  case «at» =>
    intro R k V it
    exact @IndexTy.casesOn (fun _ _ _ _ => Bool) R k V it false (fun _ => true)
  all_goals intros; exact false

private def findOp {a b s : Srt} (op : Op2 C a b s) : Bool := by
  apply @Op2.casesOn C (fun A B S op => Bool) a b s op
  case find => intro p; exact true
  all_goals intros; exact false

private def fieldOp {a s : Srt} (op : Op1 C a s) : Bool := by
  apply @Op1.casesOn C (fun A S op => Bool) a s op
  case field => intro name field T h; exact true
  all_goals intros; exact false

private def storageOp {s : Srt} (op : Op0 C s) : Bool := by
  apply @Op0.casesOn C (fun S op => Bool) s op
  case storage => exact true
  all_goals intros; exact false

private def storageTerm {Γ : Ctx} {s : Srt} (t : Tm C Γ s) : Bool := by
  apply @Tm.casesOn C Γ (fun s t => Bool) s t
  case app0 => intro s op; exact storageOp op
  all_goals intros; exact false

private def arrayAtTerm {Γ : Ctx} {s : Srt} (t : Tm C Γ s) : Bool := by
  apply @Tm.casesOn C Γ (fun s t => Bool) s t
  case app2 => intro A B S op a b; exact arrayAtOp op
  all_goals intros; exact false

/-- The immediate intrinsically typed prefix of an array index. -/
def sourceArrayParentKind? {Γ : Ctx} {s : Srt} (t : Tm C Γ s) : Option ArrayGapKind := by
  apply @Tm.casesOn C Γ (fun s t => Option ArrayGapKind) s t
  case app1 => intro A S op a; exact if fieldOp op then some .belowField else none
  case app2 =>
    intro A B S op a b
    exact if mapAtOp op then some .belowKey else if arrayAtOp op then some .elementsArray else none
  all_goals intros; exact none

/-- Array indexing through a selector, or a field selected after array indexing. -/
def sourceArrayPathKind? {Γ : Ctx} {s : Srt} (t : Tm C Γ s) : Option ArrayGapKind := by
  apply @Tm.casesOn C Γ (fun s t => Option ArrayGapKind) s t
  case app1 =>
    intro A S op a
    exact if fieldOp op && arrayAtTerm a then some .elementsStruct else none
  case app2 =>
    intro A B S op a b
    exact if arrayAtOp op then sourceArrayParentKind? a else none
  all_goals intros; exact none

/-- Only actual storage finds are classified; memory reads are separate. -/
def sourceArrayReadKind? {Γ : Ctx} {s : Srt} (t : Tm C Γ s) : Option ArrayGapKind := by
  apply @Tm.casesOn C Γ (fun s t => Option ArrayGapKind) s t
  case app2 =>
    intro A B S op a b
    exact if findOp op && storageTerm a then sourceArrayPathKind? b else none
  all_goals intros; exact none

private def sourceArrayLeafKind? {Γ : Ctx} (φ : Fml C Γ) : Option ArrayGapKind := do
  let outer ← sourceImpView? φ
  let all ← sourceUIntAllView? outer.lhs
  let inner ← sourceImpView? all.body
  let body ← MemoryWitness.eqView inner.rhs
  sourceArrayReadKind? body.a

/-- Inspect the actual bounded source premise after positive primitive prefixes. -/
def sourceArrayKind? {Γ : Ctx} (φ : Fml C Γ) : Option ArrayGapKind := by
  apply @Fml.casesOn C (fun Γ φ => Option ArrayGapKind) Γ φ
  case all => intro Γ name prim body; exact sourceArrayKind? body
  case imp => intro Γ a b; exact sourceArrayLeafKind? (.imp a b)
  all_goals intros; exact none
termination_by structural φ

/-- Full source-chain syntax and a separately computed constructor reason. -/
structure ArrayLiteralGapAt {C : Contract} {Γ : Ctx} (φ : Fml C Γ)
    (bound value : PrimTy.uint.Denote) (kind : ArrayGapKind) where
  chain : SourceUIntLiteralChain bound value φ
  shape : sourceArrayKind? φ = some kind

abbrev ArrayBelowKeyAt {Γ : Ctx} (φ : Fml C Γ) (bound value : PrimTy.uint.Denote) :=
  ArrayLiteralGapAt φ bound value .belowKey
abbrev ArrayBelowFieldAt {Γ : Ctx} (φ : Fml C Γ) (bound value : PrimTy.uint.Denote) :=
  ArrayLiteralGapAt φ bound value .belowField
abbrev ArrayOfStructAt {Γ : Ctx} (φ : Fml C Γ) (bound value : PrimTy.uint.Denote) :=
  ArrayLiteralGapAt φ bound value .elementsStruct
abbrev ArrayOfArrayAt {Γ : Ctx} (φ : Fml C Γ) (bound value : PrimTy.uint.Denote) :=
  ArrayLiteralGapAt φ bound value .elementsArray

def arrayLiteralGapAt? {Γ : Ctx} (φ : Fml C Γ) (bound value : PrimTy.uint.Denote)
    (kind : ArrayGapKind) : Option (ArrayLiteralGapAt φ bound value kind) :=
  if hs : sourceArrayKind? φ = some kind then
    (sourceUIntLiteralChain? φ bound value).map (fun w => ⟨w, hs⟩)
  else none

theorem arrayLiteralGapAt_complete {Γ : Ctx} {φ : Fml C Γ}
    {bound value : PrimTy.uint.Denote} {kind : ArrayGapKind}
    (w : ArrayLiteralGapAt φ bound value kind) :
    (arrayLiteralGapAt? φ bound value kind).isSome = true := by
  simp only [arrayLiteralGapAt?, dif_pos w.shape, Option.isSome_map]
  exact sourceUIntLiteralChain_complete w.chain

theorem arrayLiteralGapAt_witness {Γ : Ctx} {φ : Fml C Γ}
    {bound value : PrimTy.uint.Denote} {kind : ArrayGapKind}
    (h : (arrayLiteralGapAt? φ bound value kind).isSome = true) :
    Nonempty (ArrayLiteralGapAt φ bound value kind) := by
  cases he : arrayLiteralGapAt? φ bound value kind with
  | none => rw [he] at h; cases h
  | some w => exact ⟨w⟩

theorem arrayLiteralGapAt_iff {Γ : Ctx} {φ : Fml C Γ}
    {bound value : PrimTy.uint.Denote} {kind : ArrayGapKind} :
    (arrayLiteralGapAt? φ bound value kind).isSome = true ↔
      Nonempty (ArrayLiteralGapAt φ bound value kind) :=
  ⟨arrayLiteralGapAt_witness, fun ⟨w⟩ => arrayLiteralGapAt_complete w⟩

instance arrayLiteralGapAt_decidable {Γ : Ctx} {φ : Fml C Γ}
    {bound value : PrimTy.uint.Denote} {kind : ArrayGapKind} :
    Decidable (Nonempty (ArrayLiteralGapAt φ bound value kind)) :=
  if h : (arrayLiteralGapAt? φ bound value kind).isSome = true then
    isTrue (arrayLiteralGapAt_witness h)
  else isFalse (fun w => h (arrayLiteralGapAt_iff.mpr w))

def _root_.Solidity.Fml.arrayBelowKeyAt {C : Contract} {Γ : Ctx} (φ : Fml C Γ)
    (bound value : PrimTy.uint.Denote) : Bool := (arrayLiteralGapAt? φ bound value .belowKey).isSome
def _root_.Solidity.Fml.arrayBelowFieldAt {C : Contract} {Γ : Ctx} (φ : Fml C Γ)
    (bound value : PrimTy.uint.Denote) : Bool := (arrayLiteralGapAt? φ bound value .belowField).isSome
def _root_.Solidity.Fml.arrayOfStructAt {C : Contract} {Γ : Ctx} (φ : Fml C Γ)
    (bound value : PrimTy.uint.Denote) : Bool := (arrayLiteralGapAt? φ bound value .elementsStruct).isSome
def _root_.Solidity.Fml.arrayOfArrayAt {C : Contract} {Γ : Ctx} (φ : Fml C Γ)
    (bound value : PrimTy.uint.Denote) : Bool := (arrayLiteralGapAt? φ bound value .elementsArray).isSome

theorem ArrayLiteralGapAt.kind_unique {Γ : Ctx} {φ : Fml C Γ}
    {bound value : PrimTy.uint.Denote} {first second : ArrayGapKind}
    (a : ArrayLiteralGapAt φ bound value first) (b : ArrayLiteralGapAt φ bound value second) :
    first = second := Option.some.inj (a.shape.symm.trans b.shape)

theorem ArrayLiteralGapAt.valid {Γ : Ctx} {φ : Fml C Γ}
    {bound value : PrimTy.uint.Denote} {kind : ArrayGapKind}
    (w : ArrayLiteralGapAt φ bound value kind) : ∀ σ : State C Γ, holds σ φ := w.chain.valid

theorem ArrayLiteralGapAt.validH {φ : Fml C []}
    {bound value : PrimTy.uint.Denote} {kind : ArrayGapKind}
    (w : ArrayLiteralGapAt φ bound value kind) (hh : φ.hasHash = false) : Fml.ValidH φ :=
  w.chain.validH hh

end Solidity.Decide.ResidueReason
