import Solidity.Backend.FailurePaths.CheckedGuards
import Solidity.Backend.FailurePaths.RelationalGuardSelectionControls

/-! All dispatch branches share one populated heterogeneous layout: two Boolean
locals and two full-width unsigned locals, exact reserved frame4 and saved77.
Maps/Related group the existing typed premises; they assert no whole-program
context-map construction or position/ref-alias relation. -/
namespace Solidity.Backend.FailurePaths.CheckedGuards.Controls
open Evm Evm.Memory Lowering.V07 PrimitivePackets.Comparisons
abbrev C := PrimitivePackets.Comparisons.Controls.C
abbrev E := PrimitivePackets.Comparisons.Controls.E
abbrev SrcCtx : Source.RCtx := [.bool,.bool,.int (ty false),.int (ty false)]
abbrev TgtCtx : Ctx := [.val .bool,.val .bool,.val .uint,.val .uint]
def frame := PrimitivePackets.Comparisons.Controls.frame
def globals (p : Roadmap.Pipeline) := PrimitivePackets.Comparisons.Controls.global p
def original := PrimitivePackets.Comparisons.Controls.sourceState

def booleanIndex : Source.Idx SrcCtx .bool → Idx TgtCtx (.val .bool)
  | .here => .here
  | .there .here => .there .here
  | .there (.there (.there (.there i))) => nomatch i

def integerIndex (signed : Bool) : Source.Idx SrcCtx (.int (ty signed)) → Idx TgtCtx (.val (prim signed))
  | .there (.there i) => .there (.there
      (RelationalGuardSelection.Controls.integerIndexMap [ty false,ty false] i))

def maps : Maps SrcCtx TgtCtx := ⟨booleanIndex,integerIndex⟩
def fragment : Frag TgtCtx := (PrimitivePackets.Comparisons.Controls.fragment false).push (.val .bool) .ok
  |>.push (.val .bool) .ok

def locals (left right : Bool) (x y : Int)
    (hx : (ty false).lo ≤ x ∧ x ≤ (ty false).hi) (hy : (ty false).lo ≤ y ∧ y ≤ (ty false).hi) :
    Source.Locals E.layout SrcCtx :=
  .cons (.bool left) (.cons (.bool right) (PrimitivePackets.Comparisons.Controls.source false x y hx hy).1)
def state (left right : Bool) (x y : Int)
    (hx : (ty false).lo ≤ x ∧ x ≤ (ty false).hi) (hy : (ty false).lo ≤ y ∧ y ≤ (ty false).hi) :=
  ((PrimitivePackets.Comparisons.Controls.target false x y hx hy).push (t:=.val .bool) right).push
    (t:=.val .bool) left
def machine (left right : Bool) (x y : Int)
    (hx : (ty false).lo ≤ x ∧ x ≤ (ty false).hi) (hy : (ty false).lo ≤ y ∧ y ≤ (ty false).hi) :=
  writeMachine (writeMachine (PrimitivePackets.Comparisons.Controls.machine false x y hx hy)
    (cell 2) (.val (bword right))) (cell 3) (.val (bword left))

theorem represented (left right : Bool) (x y : Int)
    (hx : (ty false).lo ≤ x ∧ x ≤ (ty false).hi) (hy : (ty false).lo ≤ y ∧ y ≤ (ty false).hi) :
    StateRepr 1 0 4 fragment (state left right x y hx hy) PrimitivePackets.Comparisons.Controls.addresses
      (machine left right x y hx hy) :=
  (((PrimitivePackets.Comparisons.Controls.checked .lt false .legacy x y hx hy).1.consVal
    (p:=.bool) right (.val (bword right)) rfl (by change 3 ≤ 4; decide)).consVal
      (p:=.bool) left (.val (bword left)) rfl (by change 4 ≤ 4; decide))

theorem related (left right : Bool) (x y : Int)
    (hx : (ty false).lo ≤ x ∧ x ≤ (ty false).hi) (hy : (ty false).lo ≤ y ∧ y ≤ (ty false).hi) :
    Related maps (locals left right x y hx hy) (state left right x y hx hy) := by
  constructor
  · intro i value read
    cases i with
    | here => cases read; rfl
    | there i =>
      cases i with
      | here => cases read; rfl
      | there i =>
        cases i
        rename_i j
        cases j
        rename_i k
        exact nomatch k
  · intro signed i z hz read
    cases i with
    | there i =>
      cases i with
      | there i => exact RelationalGuardSelection.Controls.local_relation false x y hx hy signed i z hz read

def localInput : Source.RStmt E [] false .body SrcCtx SrcCtx := RuntimeGuard.statement .here
def logicalInput (disjunction : Bool) : Source.RStmt E [] false .body SrcCtx SrcCtx :=
  LogicalGuard.statement disjunction .here (.there .here)
def relationalInput (o : Order) : Source.RStmt E [] false .body SrcCtx SrcCtx :=
  RelationalGuard.statement o false (.there (.there .here)) (.there (.there (.there .here)))
def localCode : List Evm.Instr := (RuntimeGuard.selected (C:=C) 0 fragment .here).code
def logicalCode (disjunction : Bool) : List Evm.Instr :=
  (LogicalGuard.selected (C:=C) 0 fragment disjunction .here (.there .here)).code
def relationalCode (o : Order) : List Evm.Instr :=
  (RelationalGuard.selected (C:=C) 0 fragment o false (.there (.there .here)) (.there (.there (.there .here)))).code

theorem local_selected : compile (C:=C) maps 0 fragment localInput = some localCode := rfl
theorem logical_selected (disjunction : Bool) :
    compile (C:=C) maps 0 fragment (logicalInput disjunction) = some (logicalCode disjunction) := by
  cases disjunction <;> rfl
theorem relational_selected (o : Order) :
    compile (C:=C) maps 0 fragment (relationalInput o) = some (relationalCode o) := by cases o <;> rfl

def Agrees (p : Roadmap.Pipeline) (left right : Bool) (x y : Int)
    (hx : (ty false).lo ≤ x ∧ x ≤ (ty false).hi) (hy : (ty false).lo ≤ y ∧ y ≤ (ty false).hi)
    (stmt : Source.RStmt E [] false .body SrcCtx SrcCtx) (code : List Evm.Instr) : Prop :=
  ∃ value : Bool,
    (Source.execS (globals p) frame 7 0 none stmt (locals left right x y hx hy)).run (Source.L0 E,original) =
      (if value then (.ok (.normal (locals left right x y hx hy)),(Source.L0 E,original))
       else (.error (.revert []),(Source.L0 E,original))) ∧
    run code (machine left right x y hx hy) = (if value then .ok (machine left right x y hx hy) 0 else .revert)

theorem selected_client (p : Roadmap.Pipeline) (left right : Bool) (x y : Int)
    (hx : (ty false).lo ≤ x ∧ x ≤ (ty false).hi) (hy : (ty false).lo ≤ y ∧ y ≤ (ty false).hi)
    (stmt : Source.RStmt E [] false .body SrcCtx SrcCtx) (code : List Evm.Instr)
    (selected : compile (C:=C) maps 0 fragment stmt = some code) : Agrees p left right x y hx hy stmt code :=
  selected_correct maps 0 fragment stmt code selected (globals p) frame 0
    (locals left right x y hx hy) original (state left right x y hx hy)
    (related left right x y hx hy) (represented left right x y hx hy)

theorem local_client (p : Roadmap.Pipeline) (left right : Bool) (x y : Int)
    (hx : (ty false).lo ≤ x ∧ x ≤ (ty false).hi) (hy : (ty false).lo ≤ y ∧ y ≤ (ty false).hi) :
    Agrees p left right x y hx hy localInput localCode :=
  selected_client p left right x y hx hy localInput localCode local_selected

theorem logical_client (p : Roadmap.Pipeline) (left right disjunction : Bool) (x y : Int)
    (hx : (ty false).lo ≤ x ∧ x ≤ (ty false).hi) (hy : (ty false).lo ≤ y ∧ y ≤ (ty false).hi) :
    Agrees p left right x y hx hy (logicalInput disjunction) (logicalCode disjunction) :=
  selected_client p left right x y hx hy _ _ (logical_selected disjunction)

theorem relational_client (p : Roadmap.Pipeline) (left right : Bool) (o : Order) (x y : Int)
    (hx : (ty false).lo ≤ x ∧ x ≤ (ty false).hi) (hy : (ty false).lo ≤ y ∧ y ≤ (ty false).hi) :
    Agrees p left right x y hx hy (relationalInput o) (relationalCode o) :=
  selected_client p left right x y hx hy _ _ (relational_selected o)

theorem or_true_false (x y : Int)
    (hx : (ty false).lo ≤ x ∧ x ≤ (ty false).hi) (hy : (ty false).lo ≤ y ∧ y ≤ (ty false).hi) :
    run (logicalCode true) (machine true false x y hx hy) = .ok (machine true false x y hx hy) 0 :=
  LogicalGuard.selected_run (state true false x y hx hy) true .here (.there .here)
    true false rfl rfl (represented true false x y hx hy)

theorem and_false_true (x y : Int)
    (hx : (ty false).lo ≤ x ∧ x ≤ (ty false).hi) (hy : (ty false).lo ≤ y ∧ y ≤ (ty false).hi) :
    run (logicalCode false) (machine false true x y hx hy) = .revert :=
  LogicalGuard.selected_run (state false true x y hx hy) false .here (.there .here)
    false true rfl rfl (represented false true x y hx hy)

theorem relational_less (left right : Bool) (x y : Int)
    (hx : (ty false).lo ≤ x ∧ x ≤ (ty false).hi) (hy : (ty false).lo ≤ y ∧ y ≤ (ty false).hi) :
    run (relationalCode .lt) (machine left right x y hx hy) =
      (if decide (x < y) then .ok (machine left right x y hx hy) 0 else .revert) :=
  RelationalGuard.selected_run (state left right x y hx hy) .lt false
    (.there (.there .here)) (.there (.there (.there .here))) x y hx hy rfl rfl (represented left right x y hx hy)

theorem literal_refused : compile (C:=C) maps 0 fragment
    (.expr (.builtin .require (.cons (.bool false) .nil) rfl) : Source.RStmt E [] false .body SrcCtx SrcCtx) = none := rfl

theorem assert_refused : compile (C:=C) maps 0 fragment
    (.expr (.builtin .assert (.cons (.local .here) .nil) rfl) : Source.RStmt E [] false .body SrcCtx SrcCtx) = none := rfl

theorem message_refused : compile (C:=C) maps 0 fragment
    (.expr (.builtin .require (.cons (.local .here) (.cons (.str [1]) .nil)) rfl) :
      Source.RStmt E [] false .body SrcCtx SrcCtx) = none := rfl

theorem wrong_relation (x y : Int)
    (hx : (ty false).lo ≤ x ∧ x ≤ (ty false).hi) (hy : (ty false).lo ≤ y ∧ y ≤ (ty false).hi) :
    ¬ Related maps (locals true false x y hx hy) (state false false x y hx hy) := by
  intro bad
  have impossible := bad.booleans .here true rfl
  cases impossible

theorem saved_tail (left right : Bool) (x y : Int)
    (hx : (ty false).lo ≤ x ∧ x ≤ (ty false).hi) (hy : (ty false).lo ≤ y ∧ y ≤ (ty false).hi) :
    (machine left right x y hx hy).stack = [w[77]] := rfl

theorem zero_horizon (p : Roadmap.Pipeline) (left right : Bool) (x y : Int)
    (hx : (ty false).lo ≤ x ∧ x ≤ (ty false).hi) (hy : (ty false).lo ≤ y ∧ y ≤ (ty false).hi) :
    (Source.execS (globals p) frame 0 0 none localInput (locals left right x y hx hy)).run
      (Source.L0 E,original) = (.error .timeout,(Source.L0 E,original)) := rfl

def PublicCode (code : List Evm.Instr) : Prop :=
  ∃ (target : Stmt C TgtCtx TgtCtx) (checked : CompiledStmt 0 fragment target),
    compileStmt 0 fragment target = some checked ∧ checked.code = code

theorem public_branches (disjunction : Bool) (o : Order) :
    PublicCode localCode ∧ PublicCode (logicalCode disjunction) ∧ PublicCode (relationalCode o) :=
  ⟨selected_public_compiler maps 0 fragment localInput localCode local_selected,
    selected_public_compiler maps 0 fragment _ _ (logical_selected disjunction),
    selected_public_compiler maps 0 fragment _ _ (relational_selected o)⟩

#print axioms public_branches
#print axioms zero_horizon
#print axioms represented
#print axioms related
#print axioms local_selected
#print axioms logical_selected
#print axioms relational_selected
#print axioms selected_client
#print axioms local_client
#print axioms logical_client
#print axioms relational_client
#print axioms or_true_false
#print axioms and_false_true
#print axioms relational_less
#print axioms literal_refused
#print axioms assert_refused
#print axioms message_refused
#print axioms wrong_relation
#print axioms saved_tail
end Solidity.Backend.FailurePaths.CheckedGuards.Controls
