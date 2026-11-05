import Solidity.Calculus.DecisionSourceInstance
import Solidity.Calculus.ArrayProperty

/-! # Exact nested partial-OR source reason
A source-syntax component for the later Residue union. Classification is
independent of coverage/verdicts and retains the complete source equation.
-/
namespace Solidity.Decide.ResidueReason

/-- Actual intrinsically typed roots, not a semantic or validity premise. -/
structure PartialOrRoots (C : Contract) where
  scalar : Name
  mapping : Name
  scalarType : C.rootType scalar = some (.prim .uint)
  mappingType : C.rootType mapping = some (.ref (.mapping .uint (.prim .uint)))

namespace PartialOrRoots
variable {C : Contract}

def scalarRead (sp : PartialOrRoots C) {Γ : Ctx} : Tm C Γ (.val .uint) :=
  .app2 .find (.app0 .storage) (.app0 (.root sp.scalar sp.scalarType))

def mapRead (sp : PartialOrRoots C) {Γ : Ctx} (key : Tm C Γ (.val .uint)) : Tm C Γ (.val .uint) :=
  .app2 .find (.app0 .storage) (.app2 (.at .map) (.app0 (.root sp.mapping sp.mappingType)) key)

def sourceGuard (sp : PartialOrRoots C) : Tm C [.val .uint, .val .uint] (.val .bool) :=
  .app2 (.binop .or rfl)
    (.app2 (.binop .and rfl)
      (.app2 (.binop .le (p := .uint) rfl) (.pvV (.there .here)) (.pvV .here))
      (.app2 (.binop .lt (p := .uint) rfl) (.pvV (.there .here))
        (.app2 (.binop .sub rfl) sp.scalarRead (.app0 (.lit (uintOfNat 1))))))
    (.app2 (.binop .le (p := .uint) rfl) (.pvV (.there .here)) (.pvV (.there .here)))

def sourceBlock (sp : PartialOrRoots C) (i j : Var) (value : PrimTy.uint.Denote) : Fml C [] :=
  .all i .uint (.all j .uint
    (.imp (.eq sp.sourceGuard (.app0 (.lit true)))
      (.eq (sp.mapRead (.pvV (.there .here))) (.app0 (.lit value)))))

def sourceClaim (sp : PartialOrRoots C) (i j : Var)
    (value key result : PrimTy.uint.Denote) : Fml C [] :=
  .imp (sp.sourceBlock i j value)
    (.eq (sp.mapRead (.app0 (.lit key))) (.app0 (.lit result)))

end PartialOrRoots

/-- Complete nested source syntax at supplied typed roots and literals. -/
structure PartialOrBlockAt {C : Contract} (sp : PartialOrRoots C)
    (value key result : PrimTy.uint.Denote) (φ : Fml C []) where
  first : Var
  second : Var
  equation : φ = sp.sourceClaim first second value key result

/-- The existing OR guard route requires a left-child definedness condition;
checked scalar subtraction in this nested AND does not supply that condition. -/
def partialOrBlockReason : String :=
  "The APF OR reconstruction requires left-operand definedness that this checked-subtraction guard does not provide."

/-- Generalized intrinsic views and full term comparisons check every source part. -/
def partialOrBlockAt? {C : Contract} (sp : PartialOrRoots C)
    (value key result : PrimTy.uint.Denote) (φ : Fml C []) :
    Option (PartialOrBlockAt sp value key result φ) := do
  let outer ← sourceImpView? φ
  let first ← sourceUIntAllView? outer.lhs
  let second ← sourceUIntAllView? first.body
  let inner ← sourceImpView? second.body
  let ⟨hg⟩ ← sourceEquationSame? inner.lhs (.eq sp.sourceGuard (.app0 (.lit true)))
  let ⟨hb⟩ ← sourceEquationSame? inner.rhs
    (.eq (sp.mapRead (.pvV (.there .here))) (.app0 (.lit value)))
  let ⟨hr⟩ ← sourceEquationSame? outer.rhs
    (.eq (sp.mapRead (.app0 (.lit key))) (.app0 (.lit result)))
  return ⟨first.name, second.name, by
    have hi : second.body = .imp (.eq sp.sourceGuard (.app0 (.lit true)))
        (.eq (sp.mapRead (.pvV (.there .here))) (.app0 (.lit value))) :=
      inner.equation.trans (congr (congrArg Fml.imp hg) hb)
    have hj : first.body = .all second.name .uint
        (.imp (.eq sp.sourceGuard (.app0 (.lit true)))
          (.eq (sp.mapRead (.pvV (.there .here))) (.app0 (.lit value)))) :=
      second.equation.trans (congrArg (Fml.all second.name .uint) hi)
    have hf : outer.lhs = sp.sourceBlock first.name second.name value :=
      first.equation.trans (congrArg (Fml.all first.name .uint) hj)
    exact outer.equation.trans (congr (congrArg Fml.imp hf) hr)⟩

theorem partialOrBlockAt_complete {C : Contract} {sp : PartialOrRoots C}
    {value key result : PrimTy.uint.Denote} {φ : Fml C []}
    (w : PartialOrBlockAt sp value key result φ) : (partialOrBlockAt? sp value key result φ).isSome = true := by
  rcases w with ⟨i, j, hφ⟩
  subst φ
  simp only [partialOrBlockAt?, PartialOrRoots.sourceClaim, PartialOrRoots.sourceBlock,
    sourceImpView?, sourceUIntAllView?, dif_pos True.intro, sourceEquationSame_self,
    Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.isSome_some]

def _root_.Solidity.Fml.partialOrBlockAt {C : Contract} (φ : Fml C [])
    (sp : PartialOrRoots C) (value key result : PrimTy.uint.Denote) : Bool :=
  (partialOrBlockAt? sp value key result φ).isSome

theorem partialOrBlockAt_witness {C : Contract} {sp : PartialOrRoots C}
    {value key result : PrimTy.uint.Denote} {φ : Fml C []}
    (h : φ.partialOrBlockAt sp value key result = true) : Nonempty (PartialOrBlockAt sp value key result φ) := by
  unfold Fml.partialOrBlockAt at h
  cases he : partialOrBlockAt? sp value key result φ with
  | none => rw [he] at h; cases h
  | some w => exact ⟨w⟩

theorem partialOrBlockAt_iff {C : Contract} {sp : PartialOrRoots C}
    {value key result : PrimTy.uint.Denote} {φ : Fml C []} :
    φ.partialOrBlockAt sp value key result = true ↔ Nonempty (PartialOrBlockAt sp value key result φ) :=
  ⟨partialOrBlockAt_witness, fun ⟨w⟩ => partialOrBlockAt_complete w⟩

instance partialOrBlockAt_decidable {C : Contract} {sp : PartialOrRoots C}
    {value key result : PrimTy.uint.Denote} {φ : Fml C []} :
    Decidable (Nonempty (PartialOrBlockAt sp value key result φ)) :=
  if h : φ.partialOrBlockAt sp value key result = true then isTrue (partialOrBlockAt_witness h)
  else isFalse (fun w => h (partialOrBlockAt_iff.mpr w))

theorem PartialOrBlockAt.hashFree {C : Contract} {sp : PartialOrRoots C}
    {value key result : PrimTy.uint.Denote} {φ : Fml C []}
    (w : PartialOrBlockAt sp value key result φ) : φ.hasHash = false := by
  rw [w.equation]
  rfl

end Solidity.Decide.ResidueReason
