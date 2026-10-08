import Solidity.Calculus.Core.ChainKit
import Solidity.Calculus.Core.Notation
import Solidity.Calculus.Core.Completeness
import Solidity.Calculus.Core.Delab

/-!
# Chains on scoped formulas: `φ ~> ψ`, `φ ~[r]~> ψ`, `φ ~*> ψ`

`Calculus/Chains.lean`'s chains for the scoped formulas of
`Calculus/Core/Fml.lean` (W2 of `docs/intrinsic.md`); the relations are
`Calculus/Core/ChainKit.lean`'s.  The notation is the same: a chain whose
first line is a scoped formula (`cdl![m]{ … }`) is read here, any other by
`Calculus/Chains.lean` (`elabChainAny`), and `sol_chain` and `#derivation`
dispatch on the goal's head constant the same way.

**The lines are computed.**  A scoped line keeps what its print does not
show: the scope ends of a rule's fresh locals (`Frames.pop .capture`), the
rest of the program as a frame, the hidden binder.  So a written line after
the first is not read into the chain: the strategy computes it, and the
written text must be the computed line read in names, its erasure
(`Fml.erase`; `matchWritten`): `dl!{ … }`'s reading of the text, the
postcondition `φ` where the line has it.  A line printed with a block's end
(`}`, `Core.Delab`'s `core_item`) reads without it.  The statement holds
the computed lines, which `Core.Delab` prints as written.

**Past the program**, a rewrite arrow (`~[sequentialToParallel]~>`,
`~[findOnSave]~>`, `~=>`) goes on from the erasure of the line before it
(`Fml.ViaE`): `Update.lean`'s line, its postcondition `φ : Post C Γ` read
as `Update.lean`'s `φ.erase ns` (`Post.erase`), and from there
`Calculus/Chains.lean`'s rewrite links, elaborated and proved by its
machinery (`rwLabel`, `solveChain`).

**Proving a link** is the kernel's: `sol_chain` runs the strategy as
compiled code (`Fml.chainLines`, the postconditions in slots and a
modality `m` run as the diamond and the box), and proves each step
`Fml.stepFocusR k φ = some (f, ψ)` by `rfl` where no postcondition stands in
the way; where one does, along the line's connectives (`focusProof`, the
postcondition's `Post.inactive` past a goal that is done), with the fresh
index from `Post.noFresh` (`maxIdxProof`).  A rule that looks at a variable
modality is proved by `Modality.casesOn`, both cases by `rfl`.
-/

namespace Solidity.Core

open Solidity (Modality)

variable {C : Contract}

/-! ## The strategy as compiled code -/

/-- Every position of a context, innermost first. -/
def Ctx.positions : (Γ : Ctx) → List ((t : LTy) × Idx Γ t)
  | [] => []
  | t :: Γ => ⟨t, .here⟩ :: (Ctx.positions Γ).map fun x => ⟨x.1, .there x.2⟩

/-- The slot of the `i`th postcondition while the strategy runs: a formula
with no modality and no fresh name, as a postcondition is, whose erasure
lists the names of its context (`{anon(…)}` of every position). -/
def Fml.chainSlot {Γ : Ctx} (i : Nat) : Fml C Γ :=
  .anon (Ctx.positions Γ) (.defined (.app2 .find (.app0 .storage) (.app0 (.root s!"⟪{i}⟫"))))

/-- `Fml.stepFocusR` as compiled code (`Fml.stepAt`'s shape). -/
def Fml.stepFocusAt (k : Nat) : {Γ : Ctx} → Fml C Γ → Option (Focus C × Fml C Γ)
  | _, φ => Fml.casesOn (motive := fun Γ _ => Option (Focus C × Fml C Γ)) φ
    (tt := none) (eq := fun _ _ => none) (defined := fun _ => none) (not := fun _ => none)
    (and := fun φ ψ => match Fml.stepFocusAt k φ with
      | some (f, φ') => some (f, .and φ' ψ)
      | none => (Fml.stepFocusAt k ψ).map fun (f, ψ') => (f, .and φ ψ'))
    (imp := fun a φ => (Fml.stepFocusAt k φ).map fun (f, φ') => (f, .imp a φ'))
    (upd := fun m U φ => (Fml.stepFocusAt k φ).map fun (f, φ') => (f, .upd m U φ'))
    (modal := fun m P κ φ => Fml.modalFocus k m P κ φ)
    (havoc := fun φ => (Fml.stepFocusAt k φ).map fun (f, φ') => (f, .havoc φ'))
    (all := fun x p φ => (Fml.stepFocusAt k φ).map fun (f, φ') => (f, .all x p φ'))
    (bind := fun x t φ => (Fml.stepFocusAt k φ).map fun (f, φ') => (f, .bind x t φ'))
    (anon := fun xs φ => (Fml.stepFocusAt k φ).map fun (f, φ') => (f, .anon xs φ'))
  termination_by structural _ φ => φ

/-- A focus, quoted. -/
def Focus.quoteRaw (c : Lean.Expr) : Focus C → Lean.Expr
  | @Focus.stmt _ k m Γ Γ' s =>
    Lean.mkAppN (Lean.mkConst ``Focus.stmt) #[c, Lean.toExpr k, Lean.toExpr m, Quote.qCtxRaw Γ,
      Quote.qCtxRaw Γ', (Quote.qStmt Γ Γ' s).run c]
  | .empty => Lean.mkApp (Lean.mkConst ``Focus.empty) c

/-- A line of a derivation as compiled code leaves it: the line and the
statement the step that reached it fired on (`Prod.mk f φ`, hash-consed
together), the step's fresh index, and the line's erasure (`Fml.erase`,
`Update.lean`'s formula, quoted). -/
structure LineQ where
  pair : Lean.Expr
  fresh : Nat
  erased : Lean.Expr

/-- The names a line's context gets in its erasure: none known. -/
def Ctx.blankNames (Γ : Ctx) : List Var := List.replicate Γ.length (.user "_")

/-- The erasure of `φ`, quoted. -/
def Fml.erasedQuoted (c : Lean.Expr) {Γ : Ctx} (φ : Fml C Γ) : Lean.Expr :=
  Solidity.Fml.quote c (φ.erase Γ.blankNames)

/-- The lines of the derivation of `φ`, at most `n` of them. -/
def Fml.chainLines (c : Lean.Expr) {Γ : Ctx} : Nat → Fml C Γ → List LineQ
  | 0, _ => []
  | n + 1, φ =>
    let k := φ.fresh
    match φ.stepFocusAt k with
    | some (f, ψ) =>
      let pair := Lean.ShareCommon.shareCommon
        (Lean.mkApp2 (Lean.mkConst ``Prod.mk [0, 0]) (f.quoteRaw c) ((Quote.qFml Γ ψ).run c))
      ⟨pair, k, ψ.erasedQuoted c⟩ :: Fml.chainLines c n ψ
    | none => []

namespace Chain

open Lean Meta Elab Term

/-! ## Postconditions and the modality, out of the way -/

/-- The Lean terms of a line: its modality, a variable, and its
postconditions `↑φ` (`Core.Post.fml C Γ φ`), the `i`th in slot `i`. -/
structure Splice where
  modality : Option Expr := none
  posts : Array Expr := #[]

/-- Whether `e` is a postcondition `↑φ` over a variable. -/
def isPost (e : Expr) : Bool := e.isAppOfArity ``Core.Post.fml 3 && e.hasFVar

/-- Whether a line holds a postcondition. -/
def hasPost (e : Expr) : Bool := (e.find? isPost).isSome

/-- The postconditions of `e`, in order, added to `sp`. -/
def collectPosts (e : Expr) (sp : Splice) : MetaM Splice := do
  let ref ← IO.mkRef sp
  forEachExpr' e fun x => do
    if isPost x then
      ref.modify fun sp => if sp.posts.contains x then sp else { sp with posts := sp.posts.push x }
      return false
    return true
  ref.get

/-- The slot of postcondition `i` at the context `Γ`. -/
def slotE (C Γ : Expr) (i : Nat) : Expr :=
  mkApp3 (mkConst ``Fml.chainSlot) C Γ (toExpr i)

/-- The line with each postcondition in its slot. -/
def punch (C : Expr) (sp : Splice) (e : Expr) : Expr :=
  e.replace fun x =>
    if isPost x then (sp.posts.idxOf? x).map fun i => slotE C (x.getArg! 1) i else none

/-- The line with each slot's postcondition put back. -/
def unpunch (sp : Splice) (e : Expr) : Expr :=
  e.replace fun x => do
    let (i, _) ← slotIdxC? x
    sp.posts[i]?

/-- The modality of a line with its postconditions in their slots, when it
is a variable; no other variable may be left. -/
def modalityOf? (φ : Expr) : MetaM (Option Expr) := do
  let fvs := (collectFVars {} φ).fvarIds
  if fvs.isEmpty then return none
  for x in fvs do
    let ty ← instantiateMVars (← x.getType)
    if ty.isConstOf ``Modality && fvs.size == 1 then return some (.fvar x)
    unless ty.isConstOf ``Modality do
      throwError "sol_chain: {mkFVar x} is free in the line: only a modality `m` and \
        postconditions `φ : Core.Post C Γ` may be{indentExpr φ}"
  throwError "sol_chain: the line is under two modalities: take `cases` on one{indentExpr φ}"

/-- `e` with the modality constant `μ` read as the variable `m`. -/
def unModality (μ : Lean.Name) (m e : Expr) : Expr :=
  e.replace fun x => if x.isConstOf μ then some m else none

/-! ## Running the strategy -/

/-- A line of a derivation: the line and the statement the step that reached
it fired on (`Focus`), its Lean terms back; the step's fresh index; and the
line's erasure, its postconditions in their slots, once per modality it was
run under (the diamond first). -/
structure Line where
  fml : Expr
  focus : Expr
  fresh : Nat
  erased : Array Expr

/-- The most lines a run computes. -/
def runFuel : Nat := 200

/-- The lines of the derivation of the closed formula `φ : Fml C Γ`. -/
def closedLines (n : Lean.Name) (C Γ φ : Expr) : MetaM (List LineQ) := do
  unsafe evalExpr (List LineQ) (mkApp (mkConst ``List [0]) (mkConst ``LineQ))
    (mkAppN (mkConst ``Fml.chainLines) #[C, quoteConstName n, Γ, toExpr runFuel, φ])

/-- The erasure of the closed formula `φ`, quoted. -/
def closedErased (n : Lean.Name) (C Γ φ : Expr) : MetaM Expr := do
  unsafe evalExpr Expr (mkConst ``Expr)
    (mkAppN (mkConst ``Fml.erasedQuoted) #[C, quoteConstName n, Γ, φ])

/-- A derivation: the Lean terms of its first line, the erasure of that line
(once per modality), its lines, and whether they stop because the next rule
depends on the modality. -/
structure Run where
  splice : Splice
  erased : Array Expr
  lines : List Line
  stuck : Bool

/-- The runs of this declaration, by every line they pass (as
`Calculus/Chains.lean`'s `runCache`). -/
initialize runCache : EnvExtension (Std.HashMap Expr (Run × Nat)) ←
  registerEnvExtension (pure {}) (asyncMode := .local)

/-- The contract and the context of a scoped line. -/
def lineType (φ : Expr) : MetaM (Expr × Expr) := do
  let ty ← whnfR (← instantiateMVars (← inferType φ))
  unless ty.isAppOfArity ``Core.Fml 2 do throwError "not a scoped formula{indentExpr φ}"
  return (ty.getArg! 0, ty.getArg! 1)

/-- Whether `e`'s type is a scoped formula. -/
def isCoreLine (e : Expr) : MetaM Bool := do
  let ty ← whnfR (← instantiateMVars (← inferType e))
  return ty.isAppOfArity ``Core.Fml 2

/-- The pair `(f, ψ)` of a quoted line. -/
def unpair (e : Expr) : Expr × Expr := (e.appFn!.appArg!, e.appArg!)

/-- The derivation of `φ`: its postconditions in slots, and, under a
modality `m`, run as the diamond and as the box, whose shared lines (read
with `m` back) are the lines under `m`. -/
def runChain (φ : Expr) : MetaM Run := do
  let φ ← instantiateMVars φ
  if φ.hasMVar then throwError "sol_chain: the formula is not known{indentExpr φ}"
  if let some (r, i) := (runCache.getState (← getEnv))[φ]? then
    return { r with lines := r.lines.drop i }
  let (C, Γ) ← lineType φ
  let some n := (← whnfR C).constName?
    | throwError "sol_chain: the contract is not a named constant: {C}"
  let sp ← collectPosts φ {}
  let φ' := punch C sp φ
  let m? ← modalityOf? φ'
  let sp := { sp with modality := m? }
  let line (q : LineQ) : Line :=
    let (f, ψ) := unpair q.pair
    { fml := unpunch sp ψ, focus := unpunch sp f, fresh := q.fresh, erased := #[q.erased] }
  let (erased, ls, stuck) ← match m? with
    | none => pure (#[← closedErased n C Γ φ'], (← closedLines n C Γ φ').map line, false)
    | some m =>
      let φd := φ'.replaceFVar m (mkConst ``Modality.diamond)
      let φb := φ'.replaceFVar m (mkConst ``Modality.box)
      let ds ← closedLines n C Γ φd
      let bs ← closedLines n C Γ φb
      let rec shared : List LineQ → List LineQ → List Line × Bool
        | d :: ds, b :: bs =>
          let pd := unModality ``Modality.diamond m d.pair
          let pb := unModality ``Modality.box m b.pair
          if pd == pb && d.fresh == b.fresh then
            let (f, ψ) := unpair pd
            let (ls, s) := shared ds bs
            ({ fml := unpunch sp ψ, focus := unpunch sp f, fresh := d.fresh,
               erased := #[d.erased, b.erased] } :: ls, s)
          else ([], true)
        | [], [] => ([], false)
        | _, _ => ([], true)
      let (ls, s) := shared ds bs
      pure (#[← closedErased n C Γ φd, ← closedErased n C Γ φb], ls, s)
  let r : Run := { splice := sp, erased, lines := ls, stuck }
  modifyEnv fun env => runCache.modifyState env fun c => Id.run do
    let mut c := c.insert φ (r, 0)
    if ls.length < runFuel then
      for (l, j) in ls.zipIdx do
        c := c.insert l.fml ({ r with erased := l.erased }, j + 1)
    return c
  return r

/-! ## Proofs of the steps -/

/-- `a ≡ b` by the kernel's definitional equality (`Calculus/Chains.lean`'s
`kernelDefEq`). -/
def kernelDefEq (a b : Expr) : MetaM Bool := do
  let a ← instantiateMVars a
  let b ← instantiateMVars b
  if a.hasMVar || b.hasMVar then return false
  return Kernel.isDefEqGuarded (← getEnv) (← getLCtx) a b

/-- The kernel's value of a closed `Nat` term. -/
def kernelNat (e : Expr) : MetaM Nat := do
  match Kernel.whnf (← getEnv) (← getLCtx) e with
  | .ok r =>
    let some n := r.rawNatLit? <|> r.nat? | throwError "sol_chain: not a number{indentExpr r}"
    return n
  | .error _ => throwError "sol_chain: cannot compute{indentExpr e}"

/-- `e = n` by `rfl`, `n` the kernel's value of `e`. -/
def natRefl (e : Expr) : MetaM (Nat × Expr) := do
  let n ← kernelNat e
  let ty ← mkEq e (toExpr n)
  return (n, ← mkExpectedTypeHint (← mkEqRefl (toExpr n)) ty)

/-- `A.maxIdx = n`: the postconditions' `Post.noFresh`, put together along
the connectives, the kernel's value of the rest. -/
partial def maxIdxProof (A : Expr) : MetaM (Nat × Expr) := do
  let A := A.consumeMData
  if isPost A then
    return (0, mkApp3 (mkConst ``Core.Post.noFresh) (A.getArg! 0) (A.getArg! 1) A.appArg!)
  let C := A.getArg! 0
  let Γ := A.getArg! 1
  if !hasPost A then return ← natRefl (mkApp3 (mkConst ``Core.Fml.maxIdx) C Γ A)
  let a := A.getAppArgs
  let unary (lem : Lean.Name) (pre : Array Expr) (child : Expr) : MetaM (Nat × Expr) := do
    let (n, h) ← maxIdxProof child
    return (n, mkAppN (mkConst lem) (pre ++ #[child, toExpr n, h]))
  match A.getAppFn.constName? with
  | some ``Core.Fml.not => unary ``Fml.maxIdx_not_eq #[C, Γ] a[2]!
  | some ``Core.Fml.havoc => unary ``Fml.maxIdx_havoc_eq #[C, Γ] a[2]!
  | some ``Core.Fml.anon => unary ``Fml.maxIdx_anon_eq #[C, Γ, a[2]!] a[3]!
  | some ``Core.Fml.and | some ``Core.Fml.imp =>
    let lem := if A.isAppOf ``Core.Fml.and then ``Fml.maxIdx_and_eq else ``Fml.maxIdx_imp_eq
    let (n₁, h₁) ← maxIdxProof a[2]!
    let (n₂, h₂) ← maxIdxProof a[3]!
    return (max n₁ n₂,
      mkAppN (mkConst lem) #[C, Γ, a[2]!, a[3]!, toExpr n₁, toExpr n₂, h₁, h₂])
  | some ``Core.Fml.upd =>
    -- `upd {C Γ Γ'} m U φ`
    let (n₁, h₁) ← natRefl (mkApp4 (mkConst ``Core.Upd.maxIdx) C Γ a[2]! a[4]!)
    let (n₂, h₂) ← maxIdxProof a[5]!
    return (max n₁ n₂, mkAppN (mkConst ``Fml.maxIdx_upd_eq)
      #[C, Γ, a[2]!, a[3]!, a[4]!, a[5]!, toExpr n₁, toExpr n₂, h₁, h₂])
  | some ``Core.Fml.modal =>
    -- `modal {C Γ Γ₁ Γ₀} m P κ φ`
    let pk ← mkAppM ``Max.max #[mkAppN (mkConst ``Core.Prog.maxIdx) #[C, Γ, a[2]!, a[5]!],
      mkAppN (mkConst ``Core.Frames.maxIdx) #[C, a[2]!, a[3]!, a[6]!]]
    let (n₁, h₁) ← natRefl pk
    let (n₂, h₂) ← maxIdxProof a[7]!
    return (max n₁ n₂, mkAppN (mkConst ``Fml.maxIdx_modal_eq)
      #[C, Γ, a[2]!, a[3]!, a[4]!, a[5]!, a[6]!, a[7]!, toExpr n₁, toExpr n₂, h₁, h₂])
  | some ``Core.Fml.all | some ``Core.Fml.bind =>
    let lem := if A.isAppOf ``Core.Fml.all then ``Fml.maxIdx_all_eq else ``Fml.maxIdx_bind_eq
    let (n, h) ← maxIdxProof a[4]!
    let x ← kernelNat (mkApp (mkConst ``Var.idx) a[2]!)
    return (max x n, mkAppN (mkConst lem) #[C, Γ, a[2]!, a[3]!, a[4]!, toExpr n, h])
  | _ => throwError "sol_chain: cannot compute the fresh index of{indentExpr A}"

/-- `A.active = false`: the postconditions' `Post.inactive`, put together
along the connectives, the kernel's `rfl` where none is left below one. -/
partial def inactiveProof (A : Expr) : MetaM (Option Expr) := do
  let A := A.consumeMData
  if isPost A then
    return some (mkApp3 (mkConst ``Core.Post.inactive) (A.getArg! 0) (A.getArg! 1) A.appArg!)
  let C := A.getArg! 0
  let Γ := A.getArg! 1
  if !hasPost A then
    let goal := mkApp3 (mkConst ``Core.Fml.active) C Γ A
    unless ← kernelDefEq goal (toExpr false) do return none
    return some (← mkExpectedTypeHint (← mkEqRefl (toExpr false)) (← mkEq goal (toExpr false)))
  let a := A.getAppArgs
  let one (lem : Lean.Name) (pre : Array Expr) (child : Expr) : MetaM (Option Expr) := do
    let some h ← inactiveProof child | return none
    return some (mkAppN (mkConst lem) (pre ++ #[child, h]))
  match A.getAppFn.constName? with
  | some ``Core.Fml.not => one ``Fml.active_not_false #[C, Γ] a[2]!
  | some ``Core.Fml.havoc => one ``Fml.active_havoc_false #[C, Γ] a[2]!
  | some ``Core.Fml.anon => one ``Fml.active_anon_false #[C, Γ, a[2]!] a[3]!
  | some ``Core.Fml.upd => one ``Fml.active_upd_false #[C, Γ, a[2]!, a[3]!, a[4]!] a[5]!
  | some ``Core.Fml.all => one ``Fml.active_all_false #[C, Γ, a[2]!, a[3]!] a[4]!
  | some ``Core.Fml.bind => one ``Fml.active_bind_false #[C, Γ, a[2]!, a[3]!] a[4]!
  | some ``Core.Fml.and | some ``Core.Fml.imp =>
    let lem := if A.isAppOf ``Core.Fml.and then ``Fml.active_and_false else ``Fml.active_imp_false
    let some h₁ ← inactiveProof a[2]! | return none
    let some h₂ ← inactiveProof a[3]! | return none
    return some (mkAppN (mkConst lem) #[C, Γ, a[2]!, a[3]!, h₁, h₂])
  | _ => return none

/-- The type `Focus C × Fml C Γ`. -/
def pairTy (C Γ : Expr) : Expr :=
  mkApp2 (mkConst ``Prod [0, 0]) (mkApp (mkConst ``Focus) C) (mkApp2 (mkConst ``Core.Fml) C Γ)

/-- `some (f, B)`. -/
def someFocus (C Γ f B : Expr) : Expr :=
  mkApp2 (mkConst ``Option.some [0]) (pairTy C Γ)
    (mkApp4 (mkConst ``Prod.mk [0, 0]) (mkApp (mkConst ``Focus) C) (mkApp2 (mkConst ``Core.Fml) C Γ) f B)

/-- Why the line after is not written under the modality `m`. -/
def modalityStop (m : Expr) : MessageData :=
  m!"depends on the modality {m}, through a rule that reads it (`revertBox`, \
    `revertDiamond`, a loop's invariant rule): go on after `cases {m}`"

/-- `lhs = rhs` by `rfl`, the kernel's; under a modality `m` that the
kernel cannot compute past, by `Modality.casesOn m`, each case by `rfl`. -/
def kernelReflOrCases (m? : Option Expr) (lhs rhs : Expr) : MetaM Expr := do
  let ty ← mkEq lhs rhs
  if ← kernelDefEq lhs rhs then
    return ← mkExpectedTypeHint (← mkEqRefl rhs) ty
  let some m := m? | throwError "sol_chain: the kernel does not compute{indentExpr lhs}\nto{indentExpr rhs}"
  let motive ← withLocalDeclD `m (mkConst ``Modality) fun x => do
    mkLambdaFVars #[x] (ty.replaceFVar m x)
  let case (μ : Lean.Name) : MetaM Expr := do
    let l := lhs.replaceFVar m (mkConst μ)
    let r := rhs.replaceFVar m (mkConst μ)
    unless ← kernelDefEq l r do
      throwError "sol_chain: the line after the step{indentExpr lhs}\n{modalityStop m}"
    mkExpectedTypeHint (← mkEqRefl r) (← mkEq l r)
  return mkAppN (mkConst ``Modality.casesOn [levelZero])
    #[motive, m, ← case ``Modality.diamond, ← case ``Modality.box]

/-- `A.stepFocusR K = some (f, B)`: along the connectives to the statement
that fires where a postcondition stands in the way (past a goal that is
done, its `Post.inactive`), the kernel's `rfl` from there. -/
partial def focusProof (m? : Option Expr) (K : Nat) (A f B : Expr) : MetaM Expr := do
  let A := A.consumeMData
  let B := B.consumeMData
  let C := A.getArg! 0
  let Γ := A.getArg! 1
  let kE := toExpr K
  let leaf : MetaM Expr := do
    kernelReflOrCases m? (mkApp4 (mkConst ``Fml.stepFocusR) C kE Γ A) (someFocus C Γ f B)
  unless hasPost A do return ← leaf
  let a := A.getAppArgs
  let b := B.getAppArgs
  let same (n : Lean.Name) : Bool := A.isAppOf n && B.isAppOf n && a.size == b.size
  if same ``Core.Fml.and then
    if a[2]! == b[2]! then
      let some h ← inactiveProof a[2]! |
        throwError "sol_chain: the step after{indentExpr A}\nasks whether a goal is done, \
          which the kernel does not compute"
      let h₀ := mkAppN (mkConst ``Fml.stepFocusR_eq_none) #[C, kE, Γ, a[2]!, h]
      return mkAppN (mkConst ``Fml.stepFocusR_and_right)
        #[C, kE, Γ, a[2]!, a[3]!, b[3]!, f, h₀, ← focusProof m? K a[3]! f b[3]!]
    return mkAppN (mkConst ``Fml.stepFocusR_and_left)
      #[C, kE, Γ, a[2]!, a[3]!, b[2]!, f, ← focusProof m? K a[2]! f b[2]!]
  if same ``Core.Fml.imp then
    return mkAppN (mkConst ``Fml.stepFocusR_imp)
      #[C, kE, Γ, a[2]!, a[3]!, b[3]!, f, ← focusProof m? K a[3]! f b[3]!]
  if same ``Core.Fml.upd then
    return mkAppN (mkConst ``Fml.stepFocusR_upd)
      #[C, kE, Γ, a[2]!, a[3]!, a[4]!, a[5]!, b[5]!, f, ← focusProof m? K a[5]! f b[5]!]
  if same ``Core.Fml.havoc then
    return mkAppN (mkConst ``Fml.stepFocusR_havoc)
      #[C, kE, Γ, a[2]!, b[2]!, f, ← focusProof m? K a[2]! f b[2]!]
  if same ``Core.Fml.all then
    return mkAppN (mkConst ``Fml.stepFocusR_all)
      #[C, kE, Γ, a[2]!, a[3]!, a[4]!, b[4]!, f, ← focusProof m? K a[4]! f b[4]!]
  if same ``Core.Fml.bind then
    return mkAppN (mkConst ``Fml.stepFocusR_bind)
      #[C, kE, Γ, a[2]!, a[3]!, a[4]!, b[4]!, f, ← focusProof m? K a[4]! f b[4]!]
  if same ``Core.Fml.anon then
    return mkAppN (mkConst ``Fml.stepFocusR_anon)
      #[C, kE, Γ, a[2]!, a[3]!, b[3]!, f, ← focusProof m? K a[3]! f b[3]!]
  leaf

/-- `A.fresh = K`. -/
def freshProof (A : Expr) (K : Nat) : MetaM Expr := do
  let (n, h) ← maxIdxProof A
  unless n + 1 = K do throwError "sol_chain: the fresh index of{indentExpr A}\nis {n + 1}, not {K}"
  let C := A.getArg! 0
  let Γ := A.getArg! 1
  return mkAppN (mkConst ``Fml.fresh_eq) #[C, Γ, A, toExpr n, h]

/-- `A ~> B` along the computed line `B`. -/
def oneStepProof (sp : Splice) (A : Expr) (B : Line) : MetaM Expr := do
  let C := A.getArg! 0
  let Γ := A.getArg! 1
  return mkAppN (mkConst ``Fml.OneStep.ofFocus)
    #[C, Γ, A, B.fml, toExpr B.fresh, B.focus, ← freshProof A B.fresh,
      ← focusProof sp.modality B.fresh A B.focus B.fml]

/-- `A ~[r]~> B`, `r` a label whose focus is `B.focus`. -/
def stepByProof (sp : Splice) (r A : Expr) (B : Line) : MetaM Expr := do
  let C := A.getArg! 0
  let Γ := A.getArg! 1
  let fr := mkApp2 (mkConst ``StepRule.focus) C r
  let h ← focusProof sp.modality B.fresh A B.focus B.fml
  let h ← mkExpectedTypeHint h (← mkEq (mkApp4 (mkConst ``Fml.stepFocusR) C (toExpr B.fresh) Γ A)
    (someFocus C Γ fr B.fml))
  return mkAppN (mkConst ``Fml.StepBy.ofFocus)
    #[C, Γ, A, B.fml, toExpr B.fresh, r, ← freshProof A B.fresh, h]

/-- `A ~*> Z` along the computed lines `ls`, `Z` the last. -/
def stepsProof (sp : Splice) (A : Expr) (ls : List Line) : MetaM Expr := do
  let C := A.getArg! 0
  let Γ := A.getArg! 1
  let Z := (ls.getLast?.map (·.fml)).getD A
  let rec go (A : Expr) : List Line → MetaM Expr
    | [] => pure (mkApp3 (mkConst ``Fml.Steps.refl) C Γ A)
    | B :: ls => do
      let s ← oneStepProof sp A B
      pure (mkAppN (mkConst ``Fml.Steps.cons) #[C, Γ, A, B.fml, Z, s, ← go B.fml ls])
  go A ls

/-! ## Naming the rule -/

/-- The last component of a constructor's name, as `~[r]~>` shows it. -/
def lastName : Lean.Name → Lean.Name
  | .str _ s => .mkSimple s
  | n => n

/-- The derivation of the constructor `c` (of `Core.Taclet` or
`Core.LeanTaclet`) on the statement `s` under `m`, fresh names at `k`: its
schema variables by unification (a hole's statement by its candidates,
`matchFind`), its side conditions by `rfl` or `decide`; the label
`StepRule.taclet k m s p d`. -/
def labelAs? (c : Lean.Name) (k m s : Expr) : MetaM (Option Expr) := do
  let sTy ← whnfR (← inferType s)
  let C := sTy.getArg! 0
  let cands ← holeCandidates s
  let st ← saveState
  let r ← observing? do
    let ctor ← mkConstWithFreshMVarLevels c
    let (xs, _, ty) ← forallMetaTelescopeReducing (← inferType ctor)
    let args := ty.getAppArgs
    unless args.size == 7 do failure
    unless ← isDefEq args[0]! C <&&> isDefEq args[1]! k <&&> isDefEq args[2]! m do failure
    unless ← matchFind args[5]! s cands do failure
    for x in xs do
      if (← instantiateMVars x).isMVar then
        let t ← whnfR (← instantiateMVars (← inferType x))
        let t := if t.isAppOfArity ``autoParam 2 then t.getArg! 0 else t
        if let some (_, a, b) := t.eq? then
          unless ← isDefEq a b do failure
          x.mvarId!.assign (← mkEqRefl a)
        else if ← isProp t then
          x.mvarId!.assign (← mkDecideProof t)
    let d ← instantiateMVars (mkAppN ctor xs)
    let p ← instantiateMVars args[6]!
    if d.hasMVar || p.hasMVar then failure
    let wrap := if (`Solidity.Core.Taclet).isPrefixOf c then ``Rule.key else ``Rule.lean
    let rule ← mkAppM wrap #[d]
    mkAppM ``StepRule.taclet #[k, m, s, p, rule]
  if r.isNone then st.restore
  return r

/-- The constructors a name may be. -/
def ruleCtors (r : Lean.Name) : MetaM (List Lean.Name) := do
  let env ← getEnv
  return [`Solidity.Core.Taclet ++ r, `Solidity.Core.LeanTaclet ++ r].filter env.contains

/-- Every rule constructor, solkey's first. -/
def allRuleCtors : MetaM (List Lean.Name) := do
  let mut out := []
  for J in [``Core.Taclet, ``Core.LeanTaclet] do
    let some (.inductInfo ii) := (← getEnv).find? J | continue
    out := out ++ ii.ctors
  return out

/-- The rule `Stmt.step` fires on the focus `f` (quoted), by name, and its
label: `emptyModality`, or the first constructor that derives it. -/
def labelOfFocus? (f : Expr) : MetaM (Option (Lean.Name × Expr)) := do
  if f.isAppOf ``Focus.empty then
    return some (`emptyModality, mkApp (mkConst ``StepRule.emptyModality) (f.getArg! 0))
  let a := f.getAppArgs
  unless a.size == 6 do return none
  for c in ← allRuleCtors do
    if let some l ← labelAs? c a[1]! a[2]! a[5]! then return some (lastName c, l)
  return none

/-- The label of `~[r]~>` on the focus `f`: the constructor `r` must derive it. -/
def labelFor (r : Lean.Name) (f : Expr) (where_ : Expr) : MetaM Expr := do
  if r == `emptyModality then
    unless f.isAppOf ``Focus.empty do
      throwError "~[{r}]~>: the program of{indentExpr where_}\nis not done"
    return mkApp (mkConst ``StepRule.emptyModality) (f.getArg! 0)
  let a := f.getAppArgs
  unless a.size == 6 do throwError "~[{r}]~>: the step on{indentExpr where_}\nends a program"
  for c in ← ruleCtors r do
    if let some l ← labelAs? c a[1]! a[2]! a[5]! then return l
  let found := match ← labelOfFocus? f with
    | some (n, _) => m!"{n}"
    | none => m!"no rule of the table"
  throwError "~[{r}]~>: the rule for{indentExpr where_}\nis {found}, not {r}"

/-- A derivation, with the auxiliary lemmas the elaborator abstracted it into
unfolded, down to a constructor. -/
partial def tacletHead (d : Expr) : MetaM Expr := do
  let d ← whnfCore d
  let .const c us := d.getAppFn | return d
  if (`Solidity.Core.Taclet).isPrefixOf c || (`Solidity.Core.LeanTaclet).isPrefixOf c then return d
  match ← getConstInfo c with
  | info@(.thmInfo _) => tacletHead ((← instantiateValueLevelParams info us).beta d.getAppArgs)
  | _ => return d

/-- The name `~[r]~>` shows for a label. -/
def ruleName? (r : Expr) : MetaM (Option Lean.Name) := do
  let r ← whnfR (← instantiateMVars r)
  if r.isAppOf ``StepRule.emptyModality then return some `emptyModality
  unless r.isAppOf ``StepRule.taclet do return none
  let rule ← whnfCore r.appArg!
  unless rule.isAppOf ``Rule.key || rule.isAppOf ``Rule.lean do return none
  let d ← tacletHead rule.appArg!
  return d.getAppFn.constName?.map lastName

/-! ## Written lines -/

/-- A written line: left to be found (`_`), a formula in `dl`'s text, or a
term. -/
inductive Written where
  | hole
  | text (c : Lean.Term) (m? : Option Lean.Term) (φ : TSyntax `dl_fml)
  | term (t : Lean.Term)

/-- The `}` items of a modality's program dropped: `core_item`'s text read
as the statements it holds. -/
partial def dropBlockEnds (stx : Syntax) : Syntax :=
  let stx := stx.setArgs (stx.getArgs.map dropBlockEnds)
  match (⟨stx⟩ : TSyntax `dl_fml) with
  | `(dl_fml| ⟨ $[$ss;]* } $items* ⟩ $φ:dl_fml) =>
    let ss' := ss ++ items.filterMap fun i => match i with
      | `(core_item| $s:sol_stmt ;) => some s
      | _ => none
    Unhygienic.run `(dl_fml| ⟨ $[$ss';]* ⟩ $φ) |>.raw
  | `(dl_fml| [ $[$ss;]* } $items* ] $φ:dl_fml) =>
    let ss' := ss ++ items.filterMap fun i => match i with
      | `(core_item| $s:sol_stmt ;) => some s
      | _ => none
    Unhygienic.run `(dl_fml| [ $[$ss';]* ] $φ) |>.raw
  | _ => stx

/-- How a line is written. -/
def Written.of (stx : Syntax) : Written :=
  if stx.isOfKind ``Lean.Parser.Term.hole || stx.isOfKind ``Lean.Parser.Term.syntheticHole then .hole
  else
    let dlf (φ : TSyntax `dl_fml) : TSyntax `dl_fml := ⟨dropBlockEnds φ⟩
    match (⟨stx⟩ : Lean.Term) with
    | `(cdl![ $m ]{ $φ:dl_fml }) => .text (Unhygienic.run `(InContract.contract)) (some m) (dlf φ)
    | `(cdl!{ $φ:dl_fml }) => .text (Unhygienic.run `(InContract.contract)) none (dlf φ)
    | `(cdl[ $c, $m ]{ $φ:dl_fml }) => .text c (some m) (dlf φ)
    | `(cdl[ $c ]{ $φ:dl_fml }) => .text c none (dlf φ)
    | `(dl![ $m ]{ $φ:dl_fml }) => .text (Unhygienic.run `(InContract.contract)) (some m) (dlf φ)
    | `(dl!{ $φ:dl_fml }) => .text (Unhygienic.run `(InContract.contract)) none (dlf φ)
    | `(dl[ $c, $m ]{ $φ:dl_fml }) => .text c (some m) (dlf φ)
    | `(dl[ $c ]{ $φ:dl_fml }) => .text c none (dlf φ)
    | t => .term t

/-- The holes of a written formula, elaborated: each a Lean term. -/
def holeTerms (φ : TSyntax `dl_fml) : TermElabM (Array Syntax × Array Expr) := do
  let holes := fmlHoles φ
  let es ← holes.mapM fun h => do
    let some t := fmlHole? h | throwError "dl: not a formula hole"
    withRef h do
      let e ← withoutAutoBoundImplicit <| elabTerm t none
      synthesizeSyntheticMVarsNoPostponing
      instantiateMVars e
  return (holes, es)

/-- The readings of a written formula, `Update.lean`'s, its Lean formulas
in slots (`Fml.slot i`, the `i`th hole), quoted: at the diamond and at the
box when `m` is a variable, once otherwise. -/
def readings (c : Lean.Term) (m? : Option Expr) (holes : Array Syntax) (φ : TSyntax `dl_fml) :
    TermElabM (Array Expr) := do
  let read (μ : Option Lean.Name) : TermElabM Expr := do
    let raw ← liftMacroM (expandFml { either := μ.map fun n => (mkCIdent n : Lean.Term), holes } φ)
    -- applications built directly: in a quotation `$a $b` reads `$b` as a chain arrow
    elabAgainst c fun q => do
      let rd : Lean.Term := Syntax.mkApp (mkCIdent ``elabDl) #[c, raw, mkCIdent ``Bool.false]
      let qt : Lean.Term := Syntax.mkApp (mkCIdent ``Solidity.Fml.quote) #[q]
      pure (Syntax.mkApp (mkCIdent ``Except.map) #[qt, rd])
  match m? with
  | some m =>
    if m.isConstOf ``Modality.diamond || m.isConstOf ``Modality.box then return #[← read m.constName?]
    return #[← read ``Modality.diamond, ← read ``Modality.box]
  | none => return #[← read none]

/-- The `i` of an erased slot (`Fml.chainSlot i`, erased: `{anon(ns)}` over
`find(storage, ⟪i⟫)`) and its names `ns`, quoted. -/
def erasedSlot? (e : Expr) : Option (Nat × Expr) := do
  guard (e.isAppOfArity ``Solidity.Fml.anon 3)
  let body := e.getArg! 2
  guard (body.isAppOfArity ``Solidity.Fml.defined 2)
  let isSlotLit (x : Expr) : Bool := match x with
    | .lit (.strVal s) => s.startsWith "⟪"
    | _ => false
  let some (.lit (.strVal s)) := body.find? isSlotLit | none
  guard (s.endsWith "⟫")
  let i ← ((s.drop 1).dropRight 1).toNat?
  pure (i, e.getArg! 1)

/-- An erasure with each slot read as the written formula's: `Fml.slot j`,
`j` the hole of the postcondition in slot `i`. -/
def toWrittenSlots (c : Expr) (sp : Splice) (holes : Array Expr) (e : Expr) : Expr :=
  e.replace fun x => do
    let (i, _) ← erasedSlot? x
    let p ← sp.posts[i]?
    let j ← holes.findIdx? fun h => h == p.appArg! || h == p
    pure (slotExpr c j)

/-- An erased line and the lines under its leading `∀`s. -/
partial def underAlls (e : Expr) : List Expr :=
  if e.isAppOfArity ``Solidity.Fml.all 4 then e :: underAlls e.appArg! else [e]

/-- Whether the written line `w` is the computed line whose erasures are
`erased` (once per modality run), the formulas of the computed lines `sp`. -/
def matchWritten (sp : Splice) (C : Expr) (w : Written) (B : Expr) (erased : Array Expr) :
    TermElabM Bool := do
  match w with
  | .hole => return true
  | .term t =>
    let e ← elabTerm t none
    synthesizeSyntheticMVarsNoPostponing
    let e ← instantiateMVars e
    return e == B || (← withReducible (isDefEq e B))
  | .text c m? φ =>
    let m? ← m?.mapM fun m => do instantiateMVars (← elabTermEnsuringType m (mkConst ``Modality))
    -- the written modality is the chain's
    if let (some m, some m') := (m?, sp.modality) then
      unless m == m' do return false
    let (hs, es) ← holeTerms φ
    let rs ← readings c (m?.orElse fun _ => sp.modality) hs φ
    let es' := erased.map (toWrittenSlots C sp es)
    -- the written text may leave out the parameters `cdl!` binds outermost
    let same (r e : Expr) : Bool := (underAlls e).contains r
    if rs.size == es'.size then return (rs.zip es').all fun (r, e) => same r e
    -- a constant modality read once against both runs: the run's own
    return es'.any (same rs[0]! ·)

/-- A scoped line: `dl{ φ }`, a postcondition `↑φ` printed as `φ` (a local
of its name stands for it, which `Core.Delab` prints as a formula variable). -/
def ppCoreLine (e : Expr) : MetaM Lean.Term := do
  let sp ← collectPosts e {}
  let rec go (i : Nat) (e : Expr) : MetaM Lean.Term := do
    if h : i < sp.posts.size then
      let p := sp.posts[i]
      let n ← match p.appArg! with
        | .fvar fv => fv.getUserName
        | _ => pure `φ
      withLocalDeclD n (mkApp2 (mkConst ``Core.Fml) (p.getArg! 0) (p.getArg! 1)) fun x =>
        go (i + 1) (e.replace fun y => if y == p then some x else none)
    else
      let φ ← Delab.ppFmlE e
      if Solidity.isEscape φ then Solidity.escapeTerm e else `(dl{ $φ:dl_fml })
  go 0 e

/-- A scoped line in a message, indented. -/
def indentLine (e : Expr) : MetaM MessageData := do
  try return indentD m!"{← ppCoreLine e}" catch _ => return indentExpr e

/-- The computed line, shown for an error. -/
def showLines (φ : Expr) (lines : List Line) : MetaM MessageData := do
  let mut out := m!"{← indentLine φ}"
  for l in lines do
    let r := match ← labelOfFocus? l.focus with
      | some (n, _) => toString n
      | none => "?"
    out := out ++ m!"\n  ~[{r}]~>{← indentLine l.fml}"
  return out

def stuckNote (run : Run) : MessageData :=
  match run.stuck, run.splice.modality with
  | true, some m => m!"\n  (the line after {modalityStop m})"
  | _, _ => m!""

/-! ## Past the program: the erasure -/

/-- The postcondition `Update.lean` reads for the one in slot `i`, at the
names `ns` (quoted): `↑(φ.erase ns)` (`Post.erase`), its names checked to
name no fresh variable. -/
def erasedPost (sp : Splice) (i : Nat) (ns : Expr) : MetaM Expr := do
  let some p := sp.posts[i]? | throwError "sol_chain: no postcondition {i}"
  let C := p.getArg! 0
  let Γ := p.getArg! 1
  let mx := mkApp (mkConst ``Solidity.maxIdx) ns
  unless (← kernelNat mx) == 0 do
    throwError "sol_chain: the postcondition {p.appArg!} stands where a fresh variable is in \
      scope ({ns}): its erasure is no postcondition"
  let hns ← mkExpectedTypeHint (← mkEqRefl (toExpr 0)) (← mkEq mx (toExpr 0))
  return mkApp2 (mkConst ``Solidity.Post.fml) C
    (mkAppN (mkConst ``Core.Post.erase) #[C, Γ, p.appArg!, ns, hns])

/-- The erasure of a computed line, `Update.lean`'s, its postconditions
`↑(φ.erase ns)` and its modality back. -/
def erasedLine (sp : Splice) (erased : Array Expr) : MetaM Expr := do
  let fill (e : Expr) : MetaM Expr := do
    let mut out := e
    let ref ← IO.mkRef (#[] : Array (Expr × Expr))
    forEachExpr' e fun x => do
      if let some (i, ns) := erasedSlot? x then
        let p ← erasedPost sp i ns
        ref.modify (·.push (x, p))
        return false
      return true
    for (x, p) in ← ref.get do
      out := out.replace fun y => if y == x then some p else none
    return out
  match erased, sp.modality with
  | #[d], _ => fill d
  | #[d, b], some m =>
    let d ← fill (unModality ``Modality.diamond m d)
    let b ← fill (unModality ``Modality.box m b)
    unless d == b do
      throwError "sol_chain: the erasure of the line {modalityStop m}"
    return d
  | _, _ => throwError "sol_chain: no erasure"

/-- The `Update.lean` postcondition standing for the Lean term `e` (a hole
of a written line) in the line `L`. -/
def postIn (L e : Expr) : Option Expr :=
  L.find? fun x => x.isAppOfArity ``Solidity.Post.fml 2 &&
    (let q := x.appArg!; q.isAppOfArity ``Core.Post.erase 5 && q.getArg! 2 == e)

/-- A written line past the program, read as `Update.lean`'s, its
postconditions the line before's. -/
def legacyWritten (C : Expr) (m? : Option Expr) (L : Expr) : Written → TermElabM Expr
  | .hole => mkFreshExprMVar (mkApp (mkConst ``Solidity.Fml) C)
  | .term t => do
    let e ← elabTermEnsuringType t (mkApp (mkConst ``Solidity.Fml) C)
    synthesizeSyntheticMVarsNoPostponing
    instantiateMVars e
  | .text c m' φ => do
    let m'? ← m'.mapM fun m => do instantiateMVars (← elabTermEnsuringType m (mkConst ``Modality))
    let m := m'?.orElse fun _ => m?
    let (hs, es) ← holeTerms φ
    let posts ← es.mapM fun e => match postIn L e with
      | some p => pure p
      | none => throwError "~>: {e} is no postcondition of the line before{indentExpr L}"
    let rs ← readings c m hs φ
    let (d, b) := if h : rs.size = 2 then (rs[0], rs[1]) else (rs[0]!, rs[0]!)
    match fillSlots m posts d b with
    | .ok e => pure e
    | .error msg => throwError "dl[C, m]: {msg}"

/-! ## The chain, elaborated -/

/-- `Link.one`, `Link.many`, `Link.rule r` and the pair type of a chain. -/
def linkTy (C : Expr) : Expr := mkApp (mkConst ``Core.Link) C

/-- A written chain whose first line `A` is a scoped formula: every line
after it computed, checked against its text (`matchWritten`), past the
program by `Calculus/Chains.lean`'s rewrites on the erasure. -/
def elabCoreChain (stx : Syntax) (A : Expr) : TermElabM Expr := do
  let (C, Γ) ← lineType A
  let fml := mkApp2 (mkConst ``Core.Fml) C Γ
  let pairTy := mkApp2 (mkConst ``Prod [0, 0]) (linkTy C) fml
  let lfml := mkApp (mkConst ``Solidity.Fml) C
  let lpairTy := mkApp2 (mkConst ``Prod [0, 0]) (mkApp (mkConst ``Solidity.Link) C) lfml
  let mk (l B : Expr) : Expr := mkAppN (mkConst ``Prod.mk [0, 0]) #[linkTy C, fml, l, B]
  let mut cur := A
  let mut ws : Array Expr := #[]
  -- past the program: the erasure, and `Update.lean`'s links from it
  let mut legacy : Option (Expr × Expr × Option Expr) := none
  let mut rs : Array Expr := #[]
  let mut single : Option Expr := none
  let links := stx[1].getArgs
  for h : i in [0:links.size] do
    let l := links[i]
    let w := Written.of l[1]
    let arrow : TSyntax `chain_arrow := ⟨l[0]⟩
    let rw? ← match arrow with
      | `(chain_arrow| ~[ $r:ident ]~>) => do
        pure ((← Solidity.Chain.rwArrow? r).map fun a => (some (r, a)))
      | `(chain_arrow| ~=>) => pure (some none)
      | _ => pure none
    if let some rw := rw? then
      -- a rewrite: from the erasure of the scoped line, `Update.lean`'s
      let (L₀, m?) ← match legacy with
        | some (_, cur', m?) => pure (cur', m?)
        | none => do
          unless (← whnfR Γ).isAppOf ``List.nil do
            throwError "~>: a rewrite goes on from a line with no context of its own"
          let run ← runChain cur
          let erased ← if cur == A then pure run.erased else
            match (← runChain A).lines.find? (·.fml == cur) with
            | some line => pure line.erased
            | none => pure run.erased
          let L ← erasedLine run.splice erased
          legacy := some (L, L, run.splice.modality)
          pure (L, run.splice.modality)
      let b ← legacyWritten C m? L₀ w
      let (lnk, q) ← match rw with
        | some (r, a) =>
          let (lbl, q, _) ← Solidity.Chain.rwLabel C L₀ b r a
          pure (mkApp3 (mkConst ``Solidity.Link.rw) C (toExpr r.getId.toString) lbl, q)
        | none =>
          if b.isMVar then throwError "~=>: write the line after, it is what picks the rewrite"
          let (_, q, _) ← Solidity.Chain.rwAnyFind C L₀ b
          pure (mkApp (mkConst ``Solidity.Link.rwAny) C, q)
      unless ← isDefEq b q do throwError "~>: the line after is not{indentExpr q}"
      rs := rs.push (mkAppN (mkConst ``Prod.mk [0, 0])
        #[mkApp (mkConst ``Solidity.Link) C, lfml, lnk, q])
      if let some (L, _, m?) := legacy then legacy := some (L, q, m?)
      continue
    if legacy.isSome then
      throwError "~>: past a rewrite the program is done: only rewrites go on"
    let run ← runChain cur
    let notReached (ls : List Line) : TermElabM Unit := do
      throwError "sol_chain: the derivation of{← indentLine cur}\ndoes not reach the line written\n\
        Its lines:\n{← showLines cur ls}{stuckNote run}"
    match arrow with
    | `(chain_arrow| ~*>) =>
      let cands : List (Expr × Array Expr) := (cur, run.erased) :: run.lines.map fun l => (l.fml, l.erased)
      let pick ← match w with
        | .hole => pure (cands.getLast?.map (·.1))
        | _ => cands.findSomeM? fun (B, er) => do
            if ← matchWritten run.splice C w B er then pure (some B) else pure none
      let some B := pick | notReached run.lines
      ws := ws.push (mk (mkApp (mkConst ``Core.Link.many) C) B)
      if links.size == 1 then single := some (mkAppN (mkConst ``Core.Fml.Steps) #[C, Γ, cur, B])
      cur := B
    | _ =>
      let some B := run.lines.head? |
        match run.stuck, run.splice.modality with
        | true, some m => throwError "sol_chain: the line after{indentExpr cur}\n{modalityStop m}"
        | _, _ => throwError "sol_chain: no rule applies to{indentExpr cur}"
      unless ← matchWritten run.splice C w B.fml B.erased do notReached [B]
      match arrow with
      | `(chain_arrow| ~[ $r:ident ]~>) =>
        let lbl ← labelFor r.getId B.focus cur
        ws := ws.push (mk (mkApp2 (mkConst ``Core.Link.rule) C lbl) B.fml)
        if links.size == 1 then single := some (mkAppN (mkConst ``Core.Fml.StepBy) #[C, Γ, lbl, cur, B.fml])
      | _ =>
        ws := ws.push (mk (mkApp (mkConst ``Core.Link.one) C) B.fml)
        if links.size == 1 then single := some (mkAppN (mkConst ``Core.Fml.OneStep) #[C, Γ, cur, B.fml])
      cur := B.fml
  match legacy with
  | some (L, _, _) =>
    return mkAppN (mkConst ``Core.Fml.ViaE)
      #[C, A, ← mkListLit pairTy ws.toList, L, ← mkListLit lpairTy rs.toList]
  | none =>
    if let some e := single then return e
    return mkAppN (mkConst ``Core.Fml.Via) #[C, Γ, A, ← mkListLit pairTy ws.toList]

/-- A chain, read here when its first line is a scoped formula, and by
`Calculus/Chains.lean` otherwise. -/
syntax (name := chainAnyStx) "chain_any% " term : term

/-- Every chain goes through `elabChainAny`, which reads its first line once
to pick the reader. -/
@[macro Solidity.chainStx] def expandChainAny : Macro := fun stx =>
  return mkNode ``chainAnyStx #[mkAtom "chain_any% ", stx]

@[term_elab chainAnyStx] def elabChainAny : TermElab := fun stx expectedType? => do
  let inner := stx[1]
  let st ← saveState
  let first? ← observing? do
    let a ← elabTerm inner[0] none
    synthesizeSyntheticMVarsNoPostponing
    instantiateMVars a
  if let some a := first? then
    if !a.hasMVar && (← isCoreLine a) then return ← elabCoreChain inner a
  st.restore
  if Solidity.chainWritten inner then Solidity.Chain.elabChain inner expectedType?
  else elabTerm (← liftMacroM (Solidity.expandChainStx inner)) expectedType?

/-! ## `sol_chain` on scoped chains -/

/-- The computed line `B` after `A`, its run. -/
def nextLine (A B : Expr) : MetaM (Run × Line) := do
  let run ← runChain A
  let some q := run.lines.head? | throwError "sol_chain: no rule applies to{indentExpr A}"
  unless q.fml == B do
    throwError "sol_chain: the line after{indentExpr A}\nis{indentExpr q.fml}\nnot{indentExpr B}"
  return (run, q)

/-- Whether a goal is a scoped chain's. -/
partial def isCoreGoal (ty : Expr) : MetaM Bool := do
  let ty ← instantiateMVars ty
  if ty.isAppOf ``Core.Fml.OneStep || ty.isAppOf ``Core.Fml.StepBy || ty.isAppOf ``Core.Fml.Steps ||
      ty.isAppOf ``Core.Fml.Via || ty.isAppOf ``Core.Fml.ViaE then return true
  if ty.isAppOfArity ``Nonempty 1 then return ← isCoreGoal ty.appArg!
  return false

/-- `sol_chain` on a scoped goal: each link by the kernel (`oneStepProof`,
`stepByProof`, `stepsProof`), the erasure by `rfl`, and the links past it
by `Calculus/Chains.lean`'s `solveChain`. -/
partial def solveCore (g : MVarId) : TermElabM Unit := do
  let ty ← instantiateMVars (← g.getType)
  match_expr ty with
  | Core.Fml.OneStep _ _ A B =>
    let (run, q) ← nextLine A B
    g.assign (← oneStepProof run.splice A q)
  | Core.Fml.StepBy _ _ r A B =>
    let (run, q) ← nextLine A B
    g.assign (← stepByProof run.splice r A q)
  | Core.Fml.Steps _ _ A B =>
    let run ← runChain A
    let i ← if A == B then pure 0 else
      match run.lines.findIdx? (·.fml == B) with
      | some i => pure (i + 1)
      | none => throwError "sol_chain: the derivation of{indentExpr A}\ndoes not reach{indentExpr B}"
    g.assign (← stepsProof run.splice A (run.lines.take i))
  | Nonempty T =>
    let t ← mkFreshExprMVar T
    solveCore t.mvarId!
    g.assign (mkApp2 (mkConst ``Nonempty.intro [1]) T t)
  | And P Q =>
    let a ← mkFreshExprMVar P
    let b ← mkFreshExprMVar Q
    solveCore a.mvarId!
    solveCore b.mvarId!
    g.assign (mkApp4 (mkConst ``And.intro) P Q a b)
  | Eq T a b =>
    unless ← kernelDefEq a b do
      throwError "sol_chain: the erasure of the last scoped line is not{indentExpr b}"
    g.assign (← mkExpectedTypeHint (← mkEqRefl b) (mkApp3 (mkConst ``Eq [1]) T a b))
  | True => g.assign (mkConst ``True.intro)
  | _ =>
    let ty' ← whnfR ty
    if ty' != ty then return ← solveCore (← g.replaceTargetDefEq ty')
    Solidity.Chain.solveChain g

elab_rules : tactic
  | `(tactic| sol_chain) => Tactic.withMainContext do
    let g ← Tactic.getMainGoal
    unless ← isCoreGoal (← g.getType) do throwUnsupportedSyntax
    solveCore g
    Tactic.replaceMainGoal []

/-- `#derivation φ` for a scoped `φ`: the lines the strategy takes, each with
the rule that reached it. -/
elab_rules : command
  | `(command| #derivation $t) => Command.runTermElabM fun _ => do
    let φ ← instantiateMVars (← elabTerm t none)
    synthesizeSyntheticMVarsNoPostponing
    let φ ← instantiateMVars φ
    unless ← isCoreLine φ do throwUnsupportedSyntax
    let run ← runChain φ
    logInfo ((← showLines φ run.lines) ++ stuckNote run)

/-! ## Printing -/

section Print
open PrettyPrinter Delaborator SubExpr

/-- The arrow a scoped link stands for. -/
def arrowOf (l : Expr) : MetaM (TSyntax `chain_arrow) := do
  let l ← whnfR (← instantiateMVars l)
  if l.isAppOf ``Core.Link.one then `(chain_arrow| ~>)
  else if l.isAppOf ``Core.Link.many then `(chain_arrow| ~*>)
  else if l.isAppOf ``Core.Link.rule then
    let some n ← ruleName? l.appArg! | failure
    `(chain_arrow| ~[$(mkIdent n):ident]~>)
  else failure

/-- A line past the program, `Update.lean`'s: its postconditions
`↑(φ.erase ns)` printed as `φ`. -/
def ppLegacyLine (e : Expr) : MetaM Lean.Term := do
  let ref ← IO.mkRef (#[] : Array Expr)
  forEachExpr' e fun x => do
    if x.isAppOfArity ``Solidity.Post.fml 2 && x.appArg!.isAppOfArity ``Core.Post.erase 5 then
      ref.modify fun ps => if ps.contains x then ps else ps.push x
      return false
    return true
  let ps ← ref.get
  let rec go (i : Nat) (e : Expr) : MetaM Lean.Term := do
    if h : i < ps.size then
      let p := ps[i]
      let n ← match p.appArg!.getArg! 2 with
        | .fvar fv => fv.getUserName
        | _ => pure `φ
      withLocalDeclD n (mkApp (mkConst ``Solidity.Post) (p.getArg! 0)) fun x =>
        go (i + 1) (e.replace fun y => if y == p then some (mkApp2 (mkConst ``Solidity.Post.fml) (p.getArg! 0) x) else none)
    else Solidity.Chain.ppLine e
  go 0 e

/-- The links of a list of `(link, line)` pairs, printed. -/
def linkLines (ws : Expr) (legacyLinks : Bool) : MetaM (Array (TSyntax `chain_arrow × Lean.Term)) := do
  let some ws ← Solidity.listElems? ws | failure
  ws.mapM fun w => do
    let w ← whnfR w
    guard (w.isAppOfArity ``Prod.mk 4)
    if legacyLinks then
      pure (← Solidity.Chain.arrowOf (w.getArg! 2), ← ppLegacyLine (w.getArg! 3))
    else pure (← arrowOf (w.getArg! 2), ← ppCoreLine (w.getArg! 3))

@[delab app.Solidity.Core.Fml.OneStep]
def delabOneStep : Delab := do
  let e ← getExpr
  guard (e.getAppNumArgs == 4)
  return Solidity.Chain.chainNode (← ppCoreLine (e.getArg! 2))
    #[(← `(chain_arrow| ~>), ← ppCoreLine (e.getArg! 3))]

@[delab app.Solidity.Core.Fml.Steps]
def delabSteps : Delab := do
  let e ← getExpr
  guard (e.getAppNumArgs == 4)
  return Solidity.Chain.chainNode (← ppCoreLine (e.getArg! 2))
    #[(← `(chain_arrow| ~*>), ← ppCoreLine (e.getArg! 3))]

@[delab app.Solidity.Core.Fml.StepBy]
def delabStepBy : Delab := do
  let e ← getExpr
  guard (e.getAppNumArgs == 5)
  let some n ← ruleName? (e.getArg! 2) | failure
  return Solidity.Chain.chainNode (← ppCoreLine (e.getArg! 3))
    #[(← `(chain_arrow| ~[$(mkIdent n):ident]~>), ← ppCoreLine (e.getArg! 4))]

@[delab app.Solidity.Core.Fml.Via]
def delabVia : Delab := do
  let e ← getExpr
  guard (e.getAppNumArgs == 4)
  let arrows ← linkLines (e.getArg! 3) false
  guard !arrows.isEmpty
  return Solidity.Chain.chainNode (← ppCoreLine (e.getArg! 2)) arrows

/-- `Fml.ViaE φ ws L rs`: the chain, the erasure `L` unwritten. -/
@[delab app.Solidity.Core.Fml.ViaE]
def delabViaE : Delab := do
  let e ← getExpr
  guard (e.getAppNumArgs == 5)
  let a ← linkLines (e.getArg! 2) false
  let b ← linkLines (e.getArg! 4) true
  return Solidity.Chain.chainNode (← ppCoreLine (e.getArg! 1)) (a ++ b)

end Print

end Chain

end Solidity.Core
