import Solidity.Backend.FailurePaths.RelationalGuard

/-! Indexed Source selection of bare relational require over full-width
integer locals. Recognition retains widths, signs, actual indices/operators
and source equality; compilation uses the public checked memory compiler.
The initial context/read relation and physical StateRepr remain explicit. -/
namespace Solidity.Backend.FailurePaths.RelationalGuardSelection
open Evm Evm.Memory Lowering.V07 PrimitivePackets.Comparisons

structure PairView {E : Source.Env} {Γ : Source.RCtx} {τ : Source.STy}
    (a b : Source.RExpr E Γ τ) where
  signed : Bool
  type : τ = .int (ty signed)
  left : Source.Idx Γ (.int (ty signed))
  right : Source.Idx Γ (.int (ty signed))
  sameLeft : type ▸ a = .local left
  sameRight : type ▸ b = .local right

def pairView {E : Source.Env} {Γ : Source.RCtx} {τ : Source.STy} :
    (a b : Source.RExpr E Γ τ) → Option (PairView a b)
  | .local i, .local j =>
      match τ with
      | .int ⟨signed,bits,valid⟩ =>
          if h : bits = 256 then some ⟨signed,by cases h; rfl,
            (by cases h; exact i),(by cases h; exact j),
            (by cases h; rfl),(by cases h; rfl)⟩ else none
      | _ => none
  | _, _ => none

def orderView (op : Source.BinOp) : Option {o : Order // op = sourceOp o} :=
  match op with
  | .lt => some ⟨.lt,rfl⟩ | .le => some ⟨.le,rfl⟩
  | .gt => some ⟨.gt,rfl⟩ | .ge => some ⟨.ge,rfl⟩
  | _ => none

structure ExpressionView {E : Source.Env} {Γ : Source.RCtx} {τ : Source.STy}
    (expr : Source.RExpr E Γ τ) where
  order : Order
  signed : Bool
  left : Source.Idx Γ (.int (ty signed))
  right : Source.Idx Γ (.int (ty signed))
  type : τ = .bool
  same : type ▸ expr = expression order signed left right

def expressionView {E : Source.Env} {Γ : Source.RCtx} {τ : Source.STy} :
    (expr : Source.RExpr E Γ τ) → Option (ExpressionView expr)
  | .compare op left right =>
      match orderView op, pairView left right with
      | some operator, some pair => some ⟨operator.val,pair.signed,pair.left,pair.right,rfl,by
          cases pair with
          | mk signed type a b sameLeft sameRight =>
            cases type; cases sameLeft; cases sameRight
            cases operator with
            | mk o same => cases same; rfl⟩
      | _, _ => none
  | _ => none

structure View {E : Source.Env} {Γ Ξ : Source.RCtx}
    (stmt : Source.RStmt E [] false .body Γ Ξ) where
  order : Order
  signed : Bool
  left : Source.Idx Γ (.int (ty signed))
  right : Source.Idx Γ (.int (ty signed))
  contexts : Ξ = Γ
  same : HEq stmt (RelationalGuard.statement (E:=E) order signed left right)

def view {E : Source.Env} {Γ Ξ : Source.RCtx} :
    (stmt : Source.RStmt E [] false .body Γ Ξ) → Option (View stmt)
  | .expr (.builtin .require (.cons head .nil) typed) =>
      match expressionView head with
      | none => none
      | some witness => some ⟨witness.order,witness.signed,witness.left,witness.right,rfl,by
          cases witness with
          | mk order signed left right type same => cases type; cases same; cases typed; rfl⟩
  | _ => none

def compile {E : Source.Env} {Γ : Source.RCtx} {C : Contract} {Δ : Ctx}
    (map : ∀ signed, Source.Idx Γ (.int (ty signed)) → Idx Δ (.val (prim signed)))
    (base : Nat) (fragment : Frag Δ) (stmt : Source.RStmt E [] false .body Γ Γ) : Option (List Evm.Instr) := do
  let recognized ← view stmt
  let checked ← compileStmt base fragment (RelationalGuard.target (C:=C) recognized.order recognized.signed
    (map recognized.signed recognized.left) (map recognized.signed recognized.right))
  pure checked.code

theorem accepts_relational {E : Source.Env} {Γ : Source.RCtx} {C : Contract} {Δ : Ctx}
    (map : ∀ signed, Source.Idx Γ (.int (ty signed)) → Idx Δ (.val (prim signed)))
    (base : Nat) (fragment : Frag Δ) (o : Order) (signed : Bool)
    (a b : Source.Idx Γ (.int (ty signed))) :
    compile (C:=C) map base fragment (RelationalGuard.statement (E:=E) o signed a b) =
      some (RelationalGuard.selected (C:=C) base fragment o signed (map signed a) (map signed b)).code := by
  cases o <;> cases signed <;> rfl

theorem selected_correct {E : Source.Env} {Γ : Source.RCtx} {C : Contract} {Δ : Ctx}
    (map : ∀ signed, Source.Idx Γ (.int (ty signed)) → Idx Δ (.val (prim signed)))
    (base : Nat) (fragment : Frag Δ) (stmt : Source.RStmt E [] false .body Γ Γ) (code : List Evm.Instr)
    (selected : compile (C:=C) map base fragment stmt = some code)
    (G : Source.Glob E) (F : Source.Fr) (n : Nat) (locals : Source.Locals E.layout Γ)
    (source : Source.St E) (state : State C Δ)
    (localRelation : ∀ signed (i : Source.Idx Γ (.int (ty signed))) (x : Int)
      (range : (ty signed).lo ≤ x ∧ x ≤ (ty signed).hi),
      locals.get i = .int x range → TEnv.get (map signed i) state.env = integerValue (ty signed) x range)
    {L frame : Nat} {addresses : Nat → Fin W} {machine : Machine}
    (represented : StateRepr L base frame fragment state addresses machine) :
    ∃ (o : Order) (signed : Bool) (a b : Source.Idx Γ (.int (ty signed))) (x y : Int)
      (hx : (ty signed).lo ≤ x ∧ x ≤ (ty signed).hi) (hy : (ty signed).lo ≤ y ∧ y ≤ (ty signed).hi),
      locals.get a = .int x hx ∧ locals.get b = .int y hy ∧
      compileStmt base fragment (RelationalGuard.target (C:=C) o signed (map signed a) (map signed b)) =
        some (RelationalGuard.selected base fragment o signed (map signed a) (map signed b)) ∧
      (Source.execS G F (n+7) 0 none stmt locals).run (Source.L0 E,source) =
        (if result o x y then (.ok (.normal locals),(Source.L0 E,source))
         else (.error (.revert []),(Source.L0 E,source))) ∧
      run code machine = (if result o x y then .ok machine 0 else .revert) := by
  cases found : view stmt with
  | none =>
      simp only [compile,found,bind,Option.bind] at selected
      cases selected
  | some witness =>
      have codeEq : (RelationalGuard.selected (C:=C) base fragment witness.order witness.signed
          (map witness.signed witness.left) (map witness.signed witness.right)).code = code := by
        simpa only [compile,found,bind,Option.bind,RelationalGuard.public_selection,pure,Option.some.injEq] using selected
      cases leftRead : locals.get witness.left with
      | int x hx =>
        cases rightRead : locals.get witness.right with
        | int y hy =>
          have actual := RelationalGuard.agreement G F n locals source state witness.order witness.signed
            witness.left witness.right (map witness.signed witness.left) (map witness.signed witness.right)
            x y hx hy leftRead rightRead (localRelation _ _ _ _ leftRead) (localRelation _ _ _ _ rightRead) represented
          refine ⟨witness.order,witness.signed,witness.left,witness.right,x,y,hx,hy,leftRead,rightRead,actual.2.1,?_,?_⟩
          · exact (congrArg (fun chosen : Source.RStmt E [] false .body Γ Γ =>
              (Source.execS G F (n+7) 0 none chosen locals).run (Source.L0 E,source))
              (eq_of_heq witness.same)).trans actual.1
          · rw [←codeEq]
            exact actual.2.2
        | memRef impossible _ => cases impossible
        | storRef impossible _ => cases impossible
        | cdRef impossible _ _ => cases impossible
      | memRef impossible _ => cases impossible
      | storRef impossible _ => cases impossible
      | cdRef impossible _ _ => cases impossible

#print axioms accepts_relational
#print axioms selected_correct
end Solidity.Backend.FailurePaths.RelationalGuardSelection
