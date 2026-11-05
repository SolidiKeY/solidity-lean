import Solidity.Backend.FailurePaths.RelationalGuardSelection
import Solidity.Backend.FailurePaths.RelationalGuardControls

/-! Inhabited relational-selector consumers. The fixture context map is a
structural typed integer-index map, not a whole-program lowering producer.
Both pipelines retain full-width ranges, signs and saved stack77. -/
namespace Solidity.Backend.FailurePaths.RelationalGuardSelection.Controls
open Evm Evm.Memory Lowering.V07 PrimitivePackets.Comparisons

/-- Map only integer-context indices, preserving their actual indexed type. -/
def integerIndexMap : (types : List Source.IntTy) → {t : Source.IntTy} →
    Source.Idx (types.map Source.STy.int) (.int t) →
      Idx (types.map (fun t => LTy.val (integerPrim t))) (.val (integerPrim t))
  | [], _, i => nomatch i
  | _::_, _, .here => .here
  | _::rest, _, .there i => .there (integerIndexMap rest i)

abbrev SrcCtx (signed : Bool) : Source.RCtx := [.int (ty signed),.int (ty signed)]
abbrev TgtCtx (signed : Bool) : Ctx := [.val (prim signed),.val (prim signed)]
def map (signed requested : Bool) (i : Source.Idx (SrcCtx signed) (.int (ty requested))) :
    Idx (TgtCtx signed) (.val (prim requested)) := integerIndexMap [ty signed,ty signed] i

def input (o : Order) (signed : Bool) :
    Source.RStmt PrimitivePackets.Comparisons.Controls.E [] false .body (SrcCtx signed) (SrcCtx signed) :=
  RelationalGuard.statement o signed .here (.there .here)
def code (o : Order) (signed : Bool) : List Evm.Instr :=
  (RelationalGuard.selected (C:=PrimitivePackets.Comparisons.Controls.C) 0
    (PrimitivePackets.Comparisons.Controls.fragment signed) o signed .here (.there .here)).code

theorem selected (o : Order) (signed : Bool) :
    compile (C:=PrimitivePackets.Comparisons.Controls.C) (map signed) 0
      (PrimitivePackets.Comparisons.Controls.fragment signed) (input o signed) = some (code o signed) :=
  accepts_relational (map signed) 0 _ o signed .here (.there .here)

theorem local_relation (signed : Bool) (x y : Int)
    (hx : (ty signed).lo ≤ x ∧ x ≤ (ty signed).hi)
    (hy : (ty signed).lo ≤ y ∧ y ≤ (ty signed).hi) :
    ∀ requested (i : Source.Idx (SrcCtx signed) (.int (ty requested))) (z : Int)
      (hz : (ty requested).lo ≤ z ∧ z ≤ (ty requested).hi),
      (PrimitivePackets.Comparisons.Controls.source signed x y hx hy).1.get i = .int z hz →
        TEnv.get (map signed requested i) (PrimitivePackets.Comparisons.Controls.target signed x y hx hy).env =
          integerValue (ty requested) z hz := by
  intro requested i z hz read
  cases signed <;> cases requested <;> cases i
  all_goals first
    | (cases read; rfl)
    | (rename_i j; cases j
       all_goals first | (cases read; rfl) | (rename_i k; exact nomatch k))

theorem success_client (p : Roadmap.Pipeline) (o : Order) (signed : Bool) (x y : Int)
    (hx : (ty signed).lo ≤ x ∧ x ≤ (ty signed).hi)
    (hy : (ty signed).lo ≤ y ∧ y ≤ (ty signed).hi) :
    ∃ (chosen : Order) (mode : Bool) (a b : Source.Idx (SrcCtx signed) (.int (ty mode))) (u v : Int)
      (hu : (ty mode).lo ≤ u ∧ u ≤ (ty mode).hi) (hv : (ty mode).lo ≤ v ∧ v ≤ (ty mode).hi),
      (PrimitivePackets.Comparisons.Controls.source signed x y hx hy).1.get a = .int u hu ∧
      (PrimitivePackets.Comparisons.Controls.source signed x y hx hy).1.get b = .int v hv ∧
      compileStmt 0 (PrimitivePackets.Comparisons.Controls.fragment signed)
        (RelationalGuard.target (C:=PrimitivePackets.Comparisons.Controls.C) chosen mode (map signed mode a) (map signed mode b)) =
        some (RelationalGuard.selected 0 (PrimitivePackets.Comparisons.Controls.fragment signed)
          chosen mode (map signed mode a) (map signed mode b)) ∧
      (Source.execS (PrimitivePackets.Comparisons.Controls.global p) PrimitivePackets.Comparisons.Controls.frame
        7 0 none (input o signed) (PrimitivePackets.Comparisons.Controls.source signed x y hx hy).1).run
        (Source.L0 _,PrimitivePackets.Comparisons.Controls.sourceState) =
        (if result chosen u v then
          (.ok (.normal (PrimitivePackets.Comparisons.Controls.source signed x y hx hy).1),(Source.L0 _,PrimitivePackets.Comparisons.Controls.sourceState))
         else (.error (.revert []),(Source.L0 _,PrimitivePackets.Comparisons.Controls.sourceState))) ∧
      run (code o signed) (PrimitivePackets.Comparisons.Controls.machine signed x y hx hy) =
        (if result chosen u v then .ok (PrimitivePackets.Comparisons.Controls.machine signed x y hx hy) 0 else .revert) :=
  selected_correct (map signed) 0 (PrimitivePackets.Comparisons.Controls.fragment signed) (input o signed) (code o signed) (selected o signed)
    (PrimitivePackets.Comparisons.Controls.global p) PrimitivePackets.Comparisons.Controls.frame 0
    (PrimitivePackets.Comparisons.Controls.source signed x y hx hy).1 PrimitivePackets.Comparisons.Controls.sourceState
    (PrimitivePackets.Comparisons.Controls.target signed x y hx hy) (local_relation signed x y hx hy)
    (PrimitivePackets.Comparisons.Controls.checked o signed p x y hx hy).1

def Check (p : Roadmap.Pipeline) (o : Order) (signed : Bool) (x y : Int)
    (hx : (ty signed).lo ≤ x ∧ x ≤ (ty signed).hi)
    (hy : (ty signed).lo ≤ y ∧ y ≤ (ty signed).hi) : Prop :=
  compile (C:=PrimitivePackets.Comparisons.Controls.C) (map signed) 0
    (PrimitivePackets.Comparisons.Controls.fragment signed) (input o signed) = some (code o signed) ∧
  RelationalGuard.Controls.Check o signed p x y hx hy

theorem checked (p : Roadmap.Pipeline) (o : Order) (signed : Bool) (x y : Int)
    (hx : (ty signed).lo ≤ x ∧ x ≤ (ty signed).hi)
    (hy : (ty signed).lo ≤ y ∧ y ≤ (ty signed).hi) : Check p o signed x y hx hy :=
  ⟨selected o signed,RelationalGuard.Controls.checked o signed p x y hx hy⟩

theorem equality (p : Roadmap.Pipeline) (o : Order) (signed : Bool) :
    Check p o signed 7 7 (by cases signed <;> decide) (by cases signed <;> decide) := checked p o signed 7 7 _ _
theorem sign_boundary (p : Roadmap.Pipeline) (o : Order) :
    Check p o true (-1) 0 (by decide) (by decide) := checked p o true (-1) 0 _ _
theorem maximum_unsigned (p : Roadmap.Pipeline) (o : Order) :
    Check p o false (ty false).hi 0 ⟨by decide,Int.le_refl _⟩ (by decide) :=
  checked p o false (ty false).hi 0 _ _

def narrow : Source.IntTy := ⟨false,8,by decide⟩
def narrowMap (requested : Bool)
    (i : Source.Idx [.int narrow,.int narrow] (.int (ty requested))) :
    Idx [.val .uint,.val .uint] (.val (prim requested)) := integerIndexMap [narrow,narrow] i

theorem width_refused :
    compile (C:=PrimitivePackets.Comparisons.Controls.C) narrowMap 0 (Frag.init [.val .uint,.val .uint])
      (.expr (.builtin .require (.cons (.compare .lt (.local .here) (.local (.there .here))) .nil) rfl) :
        Source.RStmt PrimitivePackets.Comparisons.Controls.E [] false .body [.int narrow,.int narrow] [.int narrow,.int narrow]) = none := rfl

theorem nonlocal_operand_refused (signed : Bool) :
    compile (C:=PrimitivePackets.Comparisons.Controls.C) (map signed) 0 (PrimitivePackets.Comparisons.Controls.fragment signed)
      (.expr (.builtin .require (.cons (.compare .lt (.local .here)
        (.binary .add (.local .here) (.local (.there .here)))) .nil) rfl) :
        Source.RStmt PrimitivePackets.Comparisons.Controls.E [] false .body (SrcCtx signed) (SrcCtx signed)) = none := rfl

theorem assert_refused (o : Order) (signed : Bool) :
    compile (C:=PrimitivePackets.Comparisons.Controls.C) (map signed) 0 (PrimitivePackets.Comparisons.Controls.fragment signed)
      (.expr (.builtin .assert (.cons (expression o signed .here (.there .here)) .nil) rfl) :
        Source.RStmt PrimitivePackets.Comparisons.Controls.E [] false .body (SrcCtx signed) (SrcCtx signed)) = none := rfl

theorem message_refused (o : Order) (signed : Bool) :
    compile (C:=PrimitivePackets.Comparisons.Controls.C) (map signed) 0 (PrimitivePackets.Comparisons.Controls.fragment signed)
      (.expr (.builtin .require (.cons (expression o signed .here (.there .here)) (.cons (.str [1]) .nil)) rfl) :
        Source.RStmt PrimitivePackets.Comparisons.Controls.E [] false .body (SrcCtx signed) (SrcCtx signed)) = none := rfl

theorem zero_horizon (p : Roadmap.Pipeline) (o : Order) (signed : Bool) (x y : Int)
    (hx : (ty signed).lo ≤ x ∧ x ≤ (ty signed).hi)
    (hy : (ty signed).lo ≤ y ∧ y ≤ (ty signed).hi) :
    (Source.execS (PrimitivePackets.Comparisons.Controls.global p) PrimitivePackets.Comparisons.Controls.frame
      0 0 none (input o signed) (PrimitivePackets.Comparisons.Controls.source signed x y hx hy).1).run
      (Source.L0 _,PrimitivePackets.Comparisons.Controls.sourceState) =
      (.error .timeout,(Source.L0 _,PrimitivePackets.Comparisons.Controls.sourceState)) := rfl

def narrowInput : Source.RStmt PrimitivePackets.Comparisons.Controls.E [] false .body
    [.int narrow,.int narrow] [.int narrow,.int narrow] :=
  .expr (.builtin .require (.cons (.compare .lt (.local .here) (.local (.there .here))) .nil) rfl)
def narrowLocals : Source.Locals PrimitivePackets.Comparisons.Controls.E.layout [.int narrow,.int narrow] :=
  .cons (.int 0 (by decide)) (.cons (.int 1 (by decide)) .nil)

theorem narrow_source_succeeds (p : Roadmap.Pipeline) :
    (Source.execS (PrimitivePackets.Comparisons.Controls.global p) PrimitivePackets.Comparisons.Controls.frame
      7 0 none narrowInput narrowLocals).run (Source.L0 _,PrimitivePackets.Comparisons.Controls.sourceState) =
      (.ok (.normal narrowLocals),(Source.L0 _,PrimitivePackets.Comparisons.Controls.sourceState)) := by
  cases p <;> rfl

#print axioms narrow_source_succeeds
#print axioms selected
#print axioms local_relation
#print axioms success_client
#print axioms checked
#print axioms equality
#print axioms sign_boundary
#print axioms maximum_unsigned
#print axioms width_refused
#print axioms nonlocal_operand_refused
#print axioms assert_refused
#print axioms message_refused
#print axioms zero_horizon
end Solidity.Backend.FailurePaths.RelationalGuardSelection.Controls
