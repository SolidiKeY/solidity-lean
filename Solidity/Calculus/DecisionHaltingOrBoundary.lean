import Solidity.Calculus.Decision
import Solidity.Calculus.DecisionHaltingOrReason

/-! # Causal APF boundary for the exact partial-OR source family
The actual source guard lowers to a recognized APF term, whose required
left-operand definedness test fails. This is not a counterexample to floors.
-/
namespace Solidity.Decide.ResidueReason
namespace PartialOrRoots
variable {C : Contract}

theorem scalar_ne_mapping (sp : PartialOrRoots C) : sp.scalar ≠ sp.mapping := by
  intro h
  have hs : C.rootType sp.mapping = some (.prim .uint) := h ▸ sp.scalarType
  have ht : (Ty.prim .uint) = .ref (.mapping .uint (.prim .uint)) :=
    Option.some.inj (hs.symm.trans sp.mappingType)
  cases ht

def roots (sp : PartialOrRoots C) : ARoots := ⟨[sp.mapping], false⟩

theorem scalar_not_root (sp : PartialOrRoots C) : sp.scalar ∉ sp.roots.names := by
  simpa only [roots, List.mem_singleton] using sp.scalar_ne_mapping

def lowerScalar (sp : PartialOrRoots C) : LTm C (.val .uint) :=
  .obsW (.app0 (.root sp.scalar sp.scalarType))
def lowerBound (sp : PartialOrRoots C) : LTm C (.val .uint) :=
  .app2 (.binop .sub rfl) sp.lowerScalar (.app0 (.lit (uintOfNat 1)))
def lowerOrder (_sp : PartialOrRoots C) : LTm C (.val .bool) :=
  .app2 (.binop .le (p := .uint) rfl) (.var 0) (.var 1)
def lowerPartial (sp : PartialOrRoots C) : LTm C (.val .bool) :=
  .app2 (.binop .lt (p := .uint) rfl) (.var 0) sp.lowerBound
def lowerLeft (sp : PartialOrRoots C) : LTm C (.val .bool) :=
  .app2 (.binop .and rfl) sp.lowerOrder sp.lowerPartial
def lowerGuard (sp : PartialOrRoots C) : LTm C (.val .bool) :=
  .app2 (.binop .or rfl) sp.lowerLeft
    (.app2 (.binop .le (p := .uint) rfl) (.var 0) (.var 0))

/-- Actual source translation, preserving the two original binder positions. -/
theorem sourceGuard_translation (sp : PartialOrRoots C) :
    (sp.sourceGuard.toL (((SymS.init (C := C)).pushQ .uint).pushQ .uint)).map
      (fun t => t.elim.condSimp) = some sp.lowerGuard := by
  rfl

def leftEvidence (sp : PartialOrRoots C) : ApfTm sp.roots false sp.lowerLeft :=
  .binop .and rfl
    (.binop .le (p := .uint) rfl (.var 0) (.var 1))
    (.binop .lt (p := .uint) rfl (.var 0)
      (.binop .sub rfl (.word (.root sp.scalar sp.scalarType sp.scalar_not_root))
        (.lit (uintOfNat 1))))

def guardEvidence (sp : PartialOrRoots C) : ApfTm sp.roots false sp.lowerGuard :=
  .binop .or rfl sp.leftEvidence (.binop .le (p := .uint) rfl (.var 0) (.var 0))

private theorem apf_binop_some {C : Contract} {Rs : ARoots} {p : PrimTy}
    (op : BinOp) (hop : op.accepts p = true) {a b : LTm C (.val p)}
    {ha : ApfTm Rs false a} {hb : ApfTm Rs false b}
    (hpa : ApfTm.ofTerm? Rs false a = some ha) (hpb : ApfTm.ofTerm? Rs false b = some hb) :
    ApfTm.ofTerm? Rs false (.app2 (.binop op hop) a b) = some (.binop op hop ha hb) := by
  change (ApfTm.ofTerm? Rs false a).bind (fun x =>
    (ApfTm.ofTerm? Rs false b).bind (fun y => some (ApfTm.binop op hop x y))) = _
  rw [hpa, hpb]
  rfl

private theorem scalar_recognized (sp : PartialOrRoots C) :
    ApfTm.ofTerm? sp.roots false sp.lowerScalar =
      some (.word (.root sp.scalar sp.scalarType sp.scalar_not_root)) := by
  dsimp only [lowerScalar, ApfTm.ofTerm?]
  simp only [dif_neg sp.scalar_not_root, Option.map_some]

/-- This is the actual term recognizer result, not an assumed derivation. -/
theorem lowerGuard_recognized (sp : PartialOrRoots C) :
    ApfTm.ofTerm? sp.roots false sp.lowerGuard = some sp.guardEvidence := by
  have hb : ApfTm.ofTerm? sp.roots false sp.lowerBound =
      some (.binop .sub rfl (.word (.root sp.scalar sp.scalarType sp.scalar_not_root))
        (.lit (uintOfNat 1))) := apf_binop_some .sub rfl (scalar_recognized sp) rfl
  have ho : ApfTm.ofTerm? sp.roots false sp.lowerOrder =
      some (.binop .le (p := .uint) rfl (.var 0) (.var 1)) := apf_binop_some .le rfl rfl rfl
  have hp : ApfTm.ofTerm? sp.roots false sp.lowerPartial =
      some (.binop .lt (p := .uint) rfl (.var 0)
        (.binop .sub rfl (.word (.root sp.scalar sp.scalarType sp.scalar_not_root))
          (.lit (uintOfNat 1)))) := apf_binop_some .lt rfl rfl hb
  have hl : ApfTm.ofTerm? sp.roots false sp.lowerLeft = some sp.leftEvidence :=
    apf_binop_some .and rfl ho hp
  exact apf_binop_some .or rfl hl (apf_binop_some .le rfl rfl rfl)

/-- A skipped checked subtraction is exactly the missing left-definedness premise. -/
theorem left_definedness_refused (sp : PartialOrRoots C) :
    sp.leftEvidence.guardDs [0, 1] = false := by rfl

theorem guard_refused (sp : PartialOrRoots C) (Bs : List Parameter) :
    sp.guardEvidence.guardB .uint [0, 1] Bs = false := by
  change ((_ && false) || false) = false
  simp only [Bool.and_false, Bool.or_false]

/-- The actual source guard's APF route returns a false admission test. -/
theorem translated_guard_refused (sp : PartialOrRoots C) (Bs : List Parameter) :
    ((sp.sourceGuard.toL (((SymS.init (C := C)).pushQ .uint).pushQ .uint)).map
      (fun t => t.elim.condSimp)).bind (fun t => (ApfTm.ofTerm? sp.roots false t).map (fun h => h.guardB .uint [0, 1] Bs)) =
      some false := by
  rw [sourceGuard_translation]
  simp only [Option.bind_some, lowerGuard_recognized, Option.map_some, guard_refused]

end PartialOrRoots

theorem PartialOrBlockAt.target {C : Contract} {sp : PartialOrRoots C}
    {value key result : PrimTy.uint.Denote} {φ : Fml C []}
    (w : PartialOrBlockAt sp value key result φ) (waivers : Waivers) :
    φ.inTarget waivers = true := by
  rw [w.equation]
  change (true && keysAgree [(sp.mapping, none), (sp.mapping, none)] && true) = true
  simp only [keysAgree, List.all_cons, List.all_nil, Bool.and_true, Bool.or_true, beq_self_eq_true]

end Solidity.Decide.ResidueReason
