import Solidity.Correctness.Lowering.Loops.Statement

/-! H503 relational interface for `Solidity.Goals.lowerLoopsCorrect`.
User/caller names are fixed. Raw spelling safety is separate from intrinsic
name equivalence because `FreshNames` carries no printer/parser laws. -/
namespace Solidity.Correctness.Lowering.Total

/-- An intrinsic bijection fixing caller and user identities. -/
structure FreshRenaming (live : List Var) where
  forward : Var → Var
  backward : Var → Var
  leftInverse : ∀ x, backward (forward x) = x
  rightInverse : ∀ x, forward (backward x) = x
  user : ∀ x, forward (.user x) = .user x
  caller : ∀ x, x ∈ live → forward x = x

/-- One bijection for all occurrences: preserve aliasing and caller identities.
This name interface is not a raw-syntax/program transport theorem. -/
def FreshNameEquiv (live left right : List Var) : Prop :=
  ∃ permutation : FreshRenaming live, left.map permutation.forward = right

/-- Required round trips and absence of spelling/parsed-identity capture. -/
def SafeSpellings (names : FreshNames) (protectedNames : List String)
    (generated : List (String × Nat)) : Prop :=
  (∀ id ∈ generated, names.parse (names.name id.1 id.2) = some id) ∧
  (∀ id ∈ generated, names.name id.1 id.2 ∉ protectedNames) ∧
  (∀ id ∈ generated, ∀ spelling ∈ protectedNames, names.parse spelling ≠ some id)

def FreshRenaming.refl (live : List Var) : FreshRenaming live where
  forward := id
  backward := id
  leftInverse _ := rfl
  rightInverse _ := rfl
  user _ := rfl
  caller _ _ := rfl

def FreshRenaming.symm {live : List Var} (r : FreshRenaming live) : FreshRenaming live where
  forward := r.backward
  backward := r.forward
  leftInverse := r.rightInverse
  rightInverse := r.leftInverse
  user x := (congrArg r.backward (r.user x)).symm.trans (r.leftInverse (.user x))
  caller x h := (congrArg r.backward (r.caller x h)).symm.trans (r.leftInverse x)

def FreshRenaming.trans {live : List Var} (r s : FreshRenaming live) : FreshRenaming live where
  forward := s.forward ∘ r.forward
  backward := r.backward ∘ s.backward
  leftInverse x := (congrArg r.backward (s.leftInverse (r.forward x))).trans (r.leftInverse x)
  rightInverse x := (congrArg s.forward (r.rightInverse (s.backward x))).trans (s.rightInverse x)
  user x := (congrArg s.forward (r.user x)).trans (s.user x)
  caller x h := (congrArg s.forward (r.caller x h)).trans (s.caller x h)

theorem FreshNameEquiv.refl (live names : List Var) : FreshNameEquiv live names names :=
  ⟨FreshRenaming.refl live, List.map_id names⟩

theorem FreshNameEquiv.symm {live left right : List Var}
    (h : FreshNameEquiv live left right) : FreshNameEquiv live right left :=
  h.elim fun r eq => ⟨r.symm,
    (congrArg (List.map r.backward) eq).symm.trans
      ((List.map_map).trans (List.map_id'' r.leftInverse left))⟩

theorem FreshNameEquiv.trans {live left middle right : List Var}
    (h : FreshNameEquiv live left middle) (k : FreshNameEquiv live middle right) :
    FreshNameEquiv live left right :=
  h.elim fun r eq => k.elim fun s eq' => ⟨r.trans s,
    (List.map_map (f := r.forward) (g := s.forward) (l := left)).symm.trans
      ((congrArg (List.map s.forward) eq).trans eq')⟩

/-! Finite relational derivations, independent of totalizing production.
Each depth unfolds one layer of the three mutually recursive rules. Depth zero
has no successful derivation. Helpers are exactly the production helpers;
recursive calls to the opaque production kernel are never used here.
These local step equations are checked against the frozen equations in the
example module, without introducing a Goals import into this interface. -/
section Derivations
variable [FreshNames]

/-- One step of `lowerList`, its calls of `lowerList` and `lowerStmt` given. -/
def listStep
    (L : Option (List String) → List RawStmt → LowerM (List RawStmt × List Abrupt))
    (S : Option (List String) → RawStmt → LowerM (RawStmt × List Abrupt))
    (rs : Option (List String)) : List RawStmt → LowerM (List RawStmt × List Abrupt)
  | [] => pure ([], [])
  | s :: ss => do
    let (s', ab) ← S rs s
    if ab.isEmpty then
      let (ss', ab') ← L rs ss
      pure (s' :: ss', ab')
    else if s.isJump then pure ([s'], ab)
    else
      let (ss', ab') ← L rs ss
      if ss'.isEmpty then pure ([s'], ab)
      else pure ([s', .ite (← notAny ab) ss' []], Abrupt.union ab ab')

/-- One step of `lowerStmt`, its calls of `lowerList` and `lowerLoop` given. -/
def stmtStep
    (L : Option (List String) → List RawStmt → LowerM (List RawStmt × List Abrupt))
    (P : Option (List String) → RawStmt → LowerM (RawStmt × List Abrupt))
    (rs : Option (List String)) (s : RawStmt) : LowerM (RawStmt × List Abrupt) := do
  if s matches .whileLoop .. | .forLoop .. | .doWhile .. | .loop .. then return ← P rs s
  let lowerB (b : List RawStmt) : LowerM (List RawStmt) := do pure (← L rs b).1
  unless (← get).inLoop do
    return ← match s with
      | .block b => do pure (.block (← lowerB b), [])
      | .unchecked b => do pure (.unchecked (← lowerB b), [])
      | .checked o b => do pure (.checked o (← lowerB b), [])
      | .ite c t e => do pure (.ite c (← lowerB t) (← lowerB e), [])
      | .tryCall e g as rets ok err code pnc other => do
        pure (.tryCall e g as rets (← lowerB ok) (← lowerB err) code (← lowerB pnc) (← lowerB other),
          [])
      | .brk => throw "`break` outside a loop"
      | .cont => throw "`continue` outside a loop"
      | s => pure (s, [])
  match s with
  | .brk => pure (.setBool (← LoopFlags.flag .brk) true, [.brk])
  | .cont => pure (.setBool (← LoopFlags.flag .cnt) true, [.cnt])
  | .ret e =>
    let some rs := rs | throw "`return` outside a function's body"
    let pre ← match e with
      | none => pure []
      | some e => ElabM.lift (lowerReturn rs e)
    pure (.block (pre ++ [.setBool (← LoopFlags.flag .ret) true]), [.ret])
  | .block b => do
    let (b', ab) ← L rs b
    pure (.block b', ab)
  | .unchecked b => do
    let (b', ab) ← L rs b
    pure (.unchecked b', ab)
  | .checked o b => do
    let (b', ab) ← L rs b
    pure (.checked o b', ab)
  | .ite c t e => do
    let (t', a) ← L rs t
    let (e', b) ← L rs e
    pure (.ite c t' e', Abrupt.union a b)
  | .tryCall e g as rets ok err code pnc other => do
    if s.hasJump then throw "`break`, `continue` or `return` inside `try` inside a loop"
    LowerM.outside do
      pure (.tryCall e g as rets (← lowerB ok) (← lowerB err) code (← lowerB pnc) (← lowerB other),
        [])
  | s => pure (s, [])

/-- One step of `lowerLoop`, its calls of `lowerList` and `lowerLoop` given; the
second is the synthetic rewrite of an effectful `while` condition. -/
def loopStep
    (L : Option (List String) → List RawStmt → LowerM (List RawStmt × List Abrupt))
    (P : Option (List String) → RawStmt → LowerM (RawStmt × List Abrupt))
    (rs : Option (List String)) (s : RawStmt) : LowerM (RawStmt × List Abrupt) := do
  let (spec, c, init, upd, body, isDo) := match s with
    | .forLoop a i c u b => (a, c.getD (.bool true), i, u, b, false)
    | .doWhile a b c => (a, c, [], [], b, true)
    | .whileLoop a c b | .loop a c b => (a, c, [], [], b, false)
    | _ => ({}, .bool true, [], [], [], false)
  if (s matches .whileLoop ..) && c.hasIncDec && spec.inv.isEmpty &&
      spec.qinv.isEmpty && spec.dec.isNone && spec.unwind.isNone then
    return ← P rs (.whileLoop spec (.bool true)
      [.ite (.unop .not c) [.brk] [], .block body])
  let outer ← get
  let outermost := !outer.inLoop
  set ({ ret := if outermost then none else outer.ret, inLoop := true } : LoopFlags)
  let (body', ab) ← L rs body
  let exits := ab.filter (· != .cnt)
  let mut before : List RawStmt := init
  let mut iter : List RawStmt := []
  let mut cond := c
  let mut heads : List String := []
  if isDo then
    let first := toString (← freshCapture "first")
    before := before ++ [.declBool first true]
    iter := [.setBool first false]
    cond := .binop .or (.name first) cond
    heads := heads ++ [first]
  if let some x := (← get).cnt then iter := iter ++ [.declBool x false]
  iter := iter ++ body'
  unless upd.isEmpty do
    if exits.isEmpty then iter := iter ++ upd
    else iter := iter ++ [.ite (← notAny exits) upd []]
  unless exits.isEmpty do cond ← notAny exits (some cond)
  let fl ← get
  if exits.contains .brk then heads := heads ++ fl.brk.toList
  if exits.contains .ret then heads := heads ++ fl.ret.toList
  if let some x := fl.brk then before := before ++ [.declBool x false]
  let returns := exits.contains .ret
  let retX := fl.ret.getD ""
  if returns && outermost then before := before ++ [.declBool retX false]
  set { outer with ret := if outermost then outer.ret else fl.ret }
  let spec := if spec.inv.isEmpty && spec.qinv.isEmpty then spec else
    { spec with inv := spec.inv ++ heads.map fun f => .binop .or (.name f) (.unop .not (.name f)),
                brk := spec.brk || exits.contains .brk }
  let w := RawStmt.loop spec cond iter
  let ab' := if returns then [Abrupt.ret] else []
  if before.isEmpty && !(returns && outermost) then return (w, ab')
  if returns && outermost then
    return (.block (before ++ [w, .ite (.name retX) [.ret none] []]), [])
  pure (.block (before ++ [w]), ab')

structure Derivation where
  list : Option (List String) → List RawStmt → LowerM (List RawStmt × List Abrupt)
  stmt : Option (List String) → RawStmt → LowerM (RawStmt × List Abrupt)
  loop : Option (List String) → RawStmt → LowerM (RawStmt × List Abrupt)

/-- A depth bound on a derivation, not a bound on accepted source programs.
The zero case only throws; the rules never catch it. -/
def derive : Nat → Derivation
  | 0 => ⟨fun _ _ => throw "no derivation", fun _ _ => throw "no derivation",
      fun _ _ => throw "no derivation"⟩
  | n + 1 => let d := derive n
    ⟨listStep d.list d.stmt, stmtStep d.list d.loop, loopStep d.list d.loop⟩

/-- H503 raw lowering relation: a finite successful rule derivation from the
entire incoming state to the entire outgoing state. The existential depth is
unbounded. No production-success or semantic-equivalence premise is stored.
This is not a graph definition using the opaque production `lowerLoops`. -/
def LowersTo (rs : Option (List String)) (input output : List RawStmt)
    (scope : ElabScope) (before after : Checker.Snapshot) : Prop :=
  ∃ depth, (((do pure (← ((derive depth).list rs input).run' {}).1 :
    ElabM (List RawStmt)).run scope).run before.locals).run before.memo =
      .ok ((output, after.locals), after.memo)
end Derivations

end Solidity.Correctness.Lowering.Total
