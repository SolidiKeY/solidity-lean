import Solidity.Calculus.SurfaceNotation
import Solidity.Calculus.NotationResolve
import Solidity.Calculus.Quote

/-!
# Reading concrete formulas into scoped ones: `cdl!{ φ }`

`Calculus/SurfaceNotation.lean`'s reader (`dl!{ φ }`), producing a scoped formula
`Fml C []` (`docs/intrinsic.md`, M6b).  The text is the same, so is the
reading of every name; what changes is that every local is now bound
somewhere in the formula, at the type the reading gave it:

* **parameters** (a name read before anything declares it, `x` in
  `x == 1 → ⟨ y = x; ⟩ …` or in `x == 1 → ⟨ uint x = 2; ⟩ …`) are bound
  outermost: a `uint` by `∀ uint x;` (`Fml.all`), an alias (what a
  program binds to a storage path, `p = alice;`) by a hidden binder
  (`Fml.bind`).  A parameter no term or program reads before something
  binds it (`{ x := 10 } x == 10`, where the update declares `x`) is not
  bound: the reading is tried without each parameter in turn, and a
  parameter the formula reads without fails it;
* **an update** declares the locals it binds that are not in scope at that
  type, and assigns the others (`Upd.resolveN`): `{ p := alice }` declares an
  alias, `{ x := 10 }` over a parameter `x` assigns it;
* **a program** binds, by hidden binders in front of its modality, the
  names it assigns without declaring them (`scopeHints`: what a rule leaves
  of a dropped declaration, `carolAcc = carol.account;`), is elaborated
  scoped from the formula's context (`elabModalProg`, the elaborator's
  `elabStmtP` and `SProg.chain`), and leaves its postcondition the context
  it ends in: a local declared in a branch is not in scope after it, so a
  postcondition cannot read it;
* `φ where Person memory carol` binds `carol` by a hidden binder;
* **a Lean formula** where a formula stands (`φ`, `‹t›`) is a `Post C Γ`
  (or a `Fml C Γ`) at the context `Γ` of the place it stands in, which
  the reading computes; for a postcondition, `Γ` without its fresh locals (a
  rule's `se1`, the elaborator's captures), dropped in front of it by an
  update or a frame that prints as nothing (`NCtx.dropFresh`), as
  `Update.lean`'s `Post` names no fresh variable.

The output is quoted (`Fml.quote`) and printed by `Delab`'s
printer, as `dl{ … }` (a hidden binder printing as nothing).  A `∀` written
in the formula, past the parameters, is marked explicit on its variable
(`Fml.markExplicit`, decision 28), which only the tactics read.  `cdl[C]{ φ }`,
`cdl[C, m]{ φ }`, `cdl!{ φ }`, `cdl![m]{ φ }` are `dl[C]{ φ }`'s spellings,
and `dl[C]{ φ }` itself reads this way (`elabDlAuto`; decision 11, and
W9.4 for a formula with no modality), its parameters bound by hidden
binders rather than `∀`.
-/

namespace Solidity

open Solidity (RawFml RawStmt RawUpdElem ECtx LocalTy ElabM inScope nextFree elabUpd
  scopeHints elabTy Reading expandFml fmlHoles fmlHole?)
open Semantics (lookupBy setBy)

variable {C : Contract}

/-! ## Reading -/

/-- The scoped type of a local of the reader's scope. -/
def _root_.Solidity.LocalTy.toLTy : LocalTy → LTy
  | .val p _ => .val p
  | .alias R => .alias R
  | .mem R => .mem R
  | .store => .old

/-- `Fml.slot i` at the context `Γ`: the `i`th Lean formula, read as a
formula no reading writes (`{anon()}` over `find(storage, ⟪i⟫)`), and put
back after (`fillSlotsC`). -/
def Fml.slotC {Γ : Ctx} (i : Nat) : Fml C Γ :=
  .anon [] (.defined (.app2 .find (.app0 .storage) (.app0 (.root s!"⟪{i}⟫"))))

/-! ## A line's key -/

/-- What a line is compared by (`Fml.lineKey`): its connectives, its terms
and updates as text, a modality's program as its text, a postcondition by
its slot. -/
inductive LineKey where
  | tt
  | eq (a b : String)
  | defined (t : String)
  | not (k : LineKey)
  | and (k l : LineKey)
  | imp (k l : LineKey)
  | upd (m : Modality) (U : List String) (k : LineKey)
  /-- `⟨ P ⟩ k` or `[ P ] k`: the statements of the program and of its
  frames, each as `Prog.toStrs` prints it (`Prog.keyStrs`: a block
  flattened, a scope end nothing). -/
  | modal (m : Modality) (P : List String) (k : LineKey)
  | havoc (k : LineKey)
  | all (x : Var) (p : PrimTy) (k : LineKey)
  | anon (xs : List Var) (k : LineKey)
  /-- The postcondition in slot `i` (`Fml.chainSlot`, `Fml.slotC`). -/
  | slot (i : Nat)
  deriving Inhabited

/-- A key, quoted. -/
def LineKey.quote : LineKey → Lean.Expr
  | .tt => Lean.mkConst ``LineKey.tt
  | .eq a b => Lean.mkApp2 (Lean.mkConst ``LineKey.eq) (Lean.toExpr a) (Lean.toExpr b)
  | .defined t => Lean.mkApp (Lean.mkConst ``LineKey.defined) (Lean.toExpr t)
  | .not k => Lean.mkApp (Lean.mkConst ``LineKey.not) k.quote
  | .and k l => Lean.mkApp2 (Lean.mkConst ``LineKey.and) k.quote l.quote
  | .imp k l => Lean.mkApp2 (Lean.mkConst ``LineKey.imp) k.quote l.quote
  | .upd m U k => Lean.mkApp3 (Lean.mkConst ``LineKey.upd) (Lean.toExpr m) (Lean.toExpr U) k.quote
  | .modal m P k => Lean.mkApp3 (Lean.mkConst ``LineKey.modal) (Lean.toExpr m) (Lean.toExpr P) k.quote
  | .havoc k => Lean.mkApp (Lean.mkConst ``LineKey.havoc) k.quote
  | .all x p k => Lean.mkApp3 (Lean.mkConst ``LineKey.all) (Lean.toExpr x) (Lean.toExpr p) k.quote
  | .anon xs k => Lean.mkApp2 (Lean.mkConst ``LineKey.anon) (Lean.toExpr xs) k.quote
  | .slot i => Lean.mkApp (Lean.mkConst ``LineKey.slot) (Lean.toExpr i)

section Read

variable [FreshNames] (C : Contract)

/-- What the reader's scope `Γe` says of the local `x`. -/
def hintOf (Γe : ECtx) (x : Var) : Option LTy :=
  (Γe.find? fun (n, _) => Var.ofName n == x).map (·.2.toLTy)

/-- The locals the scope `Γe'` types and `Γe` does not, or types otherwise:
what a program binds without declaring them (`scopeHints`). -/
def newBinders (Γe Γe' : ECtx) : NCtx :=
  Γe'.filterMap fun (x, t) => if lookupBy x Γe == some t then none else some (Var.ofName x, t.toLTy)

/-- `k` under hidden binders for the locals `B`, the first outermost, read
as the box reads them: universal. -/
def withBinds (k : (Γ : NCtx) → ElabM (Fml C Γ.ctx)) : NCtx → (Γ : NCtx) → ElabM (Fml C Γ.ctx)
  | [], Γ => k Γ
  | (x, t) :: B, Γ => do pure (.bind .box x t (← withBinds k B ((x, t) :: Γ)))

/-- The locals among the `n` newest of `Γ`, the fresh ones (an elaborator's
capture, `uint idx; idx = ++i;`, or a rule's, `se1`) dropped: the context a
postcondition stands at, which names no fresh variable (`Post.noFresh`), and
the thinning into the context it is read in. -/
def _root_.Solidity.NCtx.dropFresh : Nat → (Γ : NCtx) → (Δ : NCtx) × Thin Δ.ctx Γ.ctx
  | 0, Γ => ⟨Γ, .refl⟩
  | _ + 1, [] => ⟨[], .refl⟩
  | n + 1, (x, t) :: Γ =>
    let ⟨Δ, h⟩ := NCtx.dropFresh n Γ
    if x.idx > 0 then ⟨Δ, .drop h⟩ else ⟨(x, t) :: Δ, .keep h⟩

/-- The names `ns` given to the context `Δ`, the newest first (`_` past the
end of `ns`): the named context a scoped block leaves. -/
def _root_.Solidity.NCtx.named : List Var → (Δ : Ctx) → {Γ : NCtx // Γ.ctx = Δ}
  | _, [] => ⟨[], rfl⟩
  | ns, t :: Δ =>
    let ⟨Γ, h⟩ := NCtx.named ns.tail Δ
    ⟨(ns.headD (.user "_"), t) :: Γ, congrArg (List.cons t) h⟩

/-- The reader's scope `Γe` in the order of the named context `Γ`, the
newest first, its locals `Γ` does not name after them: the elaborator
places each statement where the one before leaves by thinning its context
into `Γ` by names (`SStmt.place`), which keeps their order, while the
reader's scope appends a quantifier's local (`setBy`). -/
def alignScope (Γ : NCtx) (Γe : ECtx) : ECtx :=
  let names := Γ.names.eraseDups
  names.filterMap (fun x => Γe.find? fun (n, _) => Var.ofName n == x) ++
    Γe.filter fun (n, _) => !names.contains (Var.ofName n)

/-- A program of the formula, scoped from the formula's context `Γ`,
statement by statement: a capture takes the least index the formula's
written fresh variables leave (`nextFree`), and a statement whose captures
would run into a written index is numbered past them all.  Each statement is
elaborated from the reader's scope (`elabStmtP`) and placed where the one
before leaves (`SProg.chain`), as `elabProgAtS` places them. -/
def elabModalProg (taken : List Nat) (P : List RawStmt) (Γ : NCtx) : ElabM (Blk C Γ.ctx) := do
  modify fun (Γe, k) => (alignScope Γ Γe, k)
  -- a block's locals renamed apart (`freshenBlocks`)
  let P ← ElabM.lift (freshenBlocks (C.vars.map (·.1)) ((← get).1.map (·.1)) P)
  let mut acc : Blk C Γ.ctx := ⟨Γ.ctx, .nil⟩
  let mut ns := Γ.names
  for s in P do
    let (Γe, k) ← get
    let k₀ := nextFree taken k
    set (Γe, k₀)
    let mut Q ← elabStmtP C s
    let (_, k₁) ← get
    if (List.range' k₀ (k₁ - k₀)).any taken.contains then
      set (Γe, max k (taken.foldl max 0 + 1))
      Q ← elabStmtP C s
    let b ← ElabM.lift (SProg.chain ns acc.1 Q)
    acc ← ElabM.lift (Blk.append acc b)
    ns := b.2.outNames ns
  pure acc

/-- An atom of a formula (an equation, `defined`, a comparison), as
`elabFml` reads it, its names in the reader's scope: a formula read where
it stands (`NRead`). -/
def elabAtomN : RawFml → ElabM (NRead C)
  | .tt => pure .tt
  | .eq a b => do
    let (Γ, _) ← get
    pure (.eqD (← tVal C Γ a) (← tVal C Γ b))
  | .teq a b => do
    let (Γ, _) ← get
    pure (.eq (← tVal C Γ a) (← tVal C Γ b))
  | .defined t => do
    let (Γ, _) ← get
    pure (.defined (← tVal C Γ t))
  | .peq a b => do
    let (Γ, _) ← get
    let (a, b) ← elabCompare C Γ a b
    pure (.eqD a b)
  | .pne a b => do
    let (Γ, _) ← get
    let (a, b) ← elabCompare C Γ a b
    pure (.not (.eqD a b))
  | .cmp op a b => do
    let (Γ, _) ← get
    pure (NRead.cmp op .uint (← tVal C Γ a) (← tVal C Γ b))
  | _ => throw "internal: not an atom"

/-- A `where` clause's locals, with their types. -/
def whereLocals (ds : List RawStmt) : ElabM (List (String × LocalTy)) :=
  ds.mapM fun d => match d with
    | .declMemory T x none => do
      let .ref R ← ElabM.lift (elabTy C T) | throw s!"`{x}`: a memory local is of a reference type"
      pure (x, LocalTy.mem R)
    | .declStorage T x none => do
      let .ref R ← ElabM.lift (elabTy C T) | throw s!"`{x}`: a storage alias is of a reference type"
      pure (x, LocalTy.alias R)
    | .decl T x none => do
      let .prim p ← ElabM.lift (elabTy C T) | throw s!"`{x}`: a local without a location is a value"
      pure (x, LocalTy.val p)
    | _ => throw "`where` declares locals: `Person memory carol`, `Account storage p`, `uint v`"

/-- **A formula read in the named context `Γ`**, as `elabFml` reads it, the
reader's scope (`ECtx`) and `Γ` binding the same names: a quantifier, an
update, a program's hints and a `where` push on both.  An atom is read by
`elabAtomN` and its names resolved in `Γ`.  With `posts`, a Lean postcondition
right after a program or an update stands where the fresh locals are out of
scope (`NCtx.dropFresh`, a `Frames.drop` or an update `Upd.drop`, which print
as nothing), as a rule's own fresh locals are (`Frames.pop .capture`): the
elaborator writes a statement's captures in front of it, at the program's top
level, and a line may bind a rule's fresh locals (`{ se1 := 10 } φ`). -/
def elabFmlC (taken : List Nat) (posts : Bool := false) : RawFml → (Γ : NCtx) → ElabM (Fml C Γ.ctx)
  | .all p x φ, Γ => inScope do
    modify fun (Γe, k) => (setBy x (.val p) Γe, k)
    pure (.all (Var.ofName x) p (← elabFmlC taken posts φ ((Var.ofName x, .val p) :: Γ)))
  | .not φ, Γ => do pure (.not (← inScope (elabFmlC taken posts φ Γ)))
  | .and φ ψ, Γ => do
    pure (.and (← inScope (elabFmlC taken posts φ Γ)) (← inScope (elabFmlC taken posts ψ Γ)))
  | .imp φ ψ, Γ => do
    pure (.imp (← inScope (elabFmlC taken posts φ Γ)) (← inScope (elabFmlC taken posts ψ Γ)))
  | .upd m U φ, Γ => inScope do
    let (Γe, k) ← get
    let (U', Γe') ← ElabM.lift (elabUpd C Γe U)
    set (Γe', k)
    let ⟨Δ, U''⟩ ← ElabM.lift (Upd.resolveN (hintOf Γe') Γ Γ .nil U')
    if posts && φ matches .lean _ then
      let ⟨Δ₀, h⟩ := NCtx.dropFresh Δ.length Δ
      if Δ₀.length < Δ.length then
        return .upd m U'' (.upd m (Upd.nil.drop h) (← elabFmlC taken posts φ Δ₀))
    pure (.upd m U'' (← elabFmlC taken posts φ Δ))
  | .modal m P φ, Γ => inScope do
    let (Γe, _) ← get
    let Γh := scopeHints C Γe P
    modify fun (_, k) => (Γh, k)
    withBinds C (fun Γb => do
      let ⟨Δ, Q⟩ ← elabModalProg C taken P Γb
      let ⟨Γ', h⟩ := NCtx.named (Q.outNames Γb.names) Δ
      let Q : Prog C Γb.ctx Γ'.ctx := h ▸ Q
      if posts && φ matches .lean _ then
        let ⟨Γ₀, h⟩ := NCtx.dropFresh Γ'.length Γ'
        if Γ₀.length < Γ'.length then
          return .modal m Q (.drop h .nil) (← elabFmlC taken posts φ Γ₀)
      pure (.modal m Q .nil (← elabFmlC taken posts φ Γ'))) (newBinders Γe Γh) Γ
  | .lean i, Γ => do
    -- a postcondition under a connective: the fresh locals dropped in front of it
    if posts then
      let ⟨Γ₀, h⟩ := NCtx.dropFresh Γ.length Γ
      if Γ₀.length < Γ.length then
        return .upd .box (Upd.nil.drop h) (Fml.slotC i)
    pure (Fml.slotC i)
  | .decl ds φ, Γ => inScope do
    let ls ← whereLocals C ds
    for (x, t) in ls do
      modify fun (Γe, k) => (setBy x t Γe, k)
    withBinds C (elabFmlC taken posts φ) (ls.map fun (x, t) => (Var.ofName x, t.toLTy)) Γ
  | φ, Γ => do
    let ψ ← elabAtomN C φ
    ElabM.lift (ψ Γ)

/-- `elabDl`'s parameters of `φ` (the names read, a declared one
included), the elaborator's scope (a declared name's parameter left out),
and the indices of the fresh variables the formula writes. -/
def dlParams (φ : RawFml) (pastAll : Bool) : ECtx × List String × List Nat :=
  let (used, declared) := φ.names
  let hints := φ.stmts.flatMap (RawStmt.aliasHints C)
  let free := (used.filter fun x => (C.rootType x).isNone &&
    (lookupBy x C.enums).isNone).eraseDups
  let unsets := φ.unsets
  let params : ECtx := free.filterMap fun x =>
    match lookupBy x hints, Var.ofName x with
    | some R, _ => some (x, LocalTy.alias R)
    | none, .fresh "sp" _ | none, .fresh "mv" _ => none
    | none, _ => if unsets.contains x then none else some (x, LocalTy.val .uint)
  let taken := ((used ++ declared).map fun x => (Var.ofName x).idx).filter (· > 0)
  let taken := if pastAll then List.range' 1 (taken.foldl max 0) else taken
  (params, declared, taken)

/-- `φ` read with the parameters `ps` in scope, open: at their context. -/
def elabDlIn (φ : RawFml) (pastAll : Bool) (declared : List String) (taken : List Nat)
    (ps : ECtx) : Except String ((Γ : NCtx) × Fml C Γ.ctx) :=
  let Γ : NCtx := ps.map fun (x, t) => (Var.ofName x, t.toLTy)
  -- a declared name's parameter is not in the program's scope, which may
  -- declare it (as `dl!` reads it free, a `pv`)
  let scope := ps.filter fun (x, _) => !declared.contains x
  (((elabFmlC C taken (!pastAll) φ Γ).run { funs := C.funs }).run' (scope, 1)).map (⟨Γ, ·⟩)

/-- **A formula against `C`, scoped**: `elabDl`'s parameters (the names
read, a declared one included) bound outermost (`Fml.closeN`), each only if
the formula reads it before anything binds it (tried without it, in order).
A declared name's parameter is bound but not in the elaborator's scope, so
the program's declaration shadows it, as `dl!` reads it.  With the number
of parameters bound, the outermost binders (`Fml.markExplicit`).  A
value parameter is bound by `∀` when `useAll` (`cdl!`), by a hidden binder,
printing as nothing, otherwise (`dl!` outside the flip, `elabDlAuto`). -/
def elabDlCN (φ : RawFml) (pastAll : Bool := false) (useAll : Bool := true)
    (keepAll : Bool := false) (keep : List String := []) : Except String (Nat × Fml C []) := do
  let (params, declared, taken) := dlParams C φ pastAll
  let run (ps : ECtx) : Except String (Fml C []) :=
    (elabDlIn C φ pastAll declared taken ps).map fun r => Fml.closeN useAll r.1 r.2
  let mut ps := params
  for p in if keepAll then [] else params.filter (!keep.contains ·.1) do
    let ps' := ps.erase p
    if let .ok _ := run ps' then ps := ps'
  return (ps.length, ← run ps)

/-- **A written line of a chain**, read as `elabDlCN` reads it but open:
every parameter left in the context, unbound, as today's `elabDl` left it
free (`Calculus/Chains.lean`'s `readings`). -/
def elabDlOpen (φ : RawFml) : Except String ((Γ : NCtx) × Fml C Γ.ctx) :=
  let (params, declared, taken) := dlParams C φ false
  elabDlIn C φ false declared taken params

/-! ### A written line's key, read by name

A written line with no modality (one past the program) is compared with a
computed one by its key (`LineKey`, `Calculus/Chains.lean`'s `Fml.lineKey`),
which reads a line in names.  So it is read by name too: its terms by the
readers of `Calculus/SurfaceNotation.lean`, as `elabAtomN` reads them, with
no type asked of a local a line past the program no longer declares (a
memory local the program wrote, a capture): a term's key (`NTm.key`) is
the text `Tm.keyStr` writes of the scoped term it names. -/

/-- `a = b` with both sides defined, as `Fml.eqD`'s key. -/
def LineKey.eqD (a b : String) : LineKey := .and (.defined a) (.and (.defined b) (.eq a b))

/-- A written line with no modality, its key read by name (`Fml.lineKey`'s
shapes: `Fml.eqD` a conjunction, a comparison `a < b` the equation
`a < b = true`, a Lean formula its slot). -/
def elabKeyFml : RawFml → ElabM LineKey
  | .tt => pure .tt
  | .eq a b => do
    let (Γ, _) ← get
    pure (.eqD (← tVal C Γ a).key (← tVal C Γ b).key)
  | .teq a b => do
    let (Γ, _) ← get
    pure (.eq (← tVal C Γ a).key (← tVal C Γ b).key)
  | .defined t => do
    let (Γ, _) ← get
    pure (.defined (← tVal C Γ t).key)
  | .peq a b => do
    let (Γ, _) ← get
    let (a, b) ← elabCompare C Γ a b
    pure (.eqD a.key b.key)
  | .pne a b => do
    let (Γ, _) ← get
    let (a, b) ← elabCompare C Γ a b
    pure (.not (.eqD a.key b.key))
  | .cmp op a b => do
    let (Γ, _) ← get
    let t : NTerm C := .binop op .uint (← tVal C Γ a) (← tVal C Γ b)
    pure (.eqD t.key (NTerm.lit (C := C) (.bool true)).key)
  | .all p x φ => inScope do
    modify fun (Γ, k) => (setBy x (.val p) Γ, k)
    pure (.all (Var.ofName x) p (← elabKeyFml φ))
  | .not φ => do pure (.not (← inScope (elabKeyFml φ)))
  | .and φ ψ => do pure (.and (← inScope (elabKeyFml φ)) (← inScope (elabKeyFml ψ)))
  | .imp φ ψ => do pure (.imp (← inScope (elabKeyFml φ)) (← inScope (elabKeyFml ψ)))
  | .upd m U φ => inScope do
    let (Γ, k) ← get
    let (U', Γ') ← elabUpd C Γ U
    set (Γ', k)
    let k' ← elabKeyFml φ
    pure (if U'.isEmpty then k' else .upd m (U'.map (·.keyStr)) k')
  | .modal .. => throw "a modality is read scoped (`elabDlOpen`)"
  | .lean i => pure (.slot i)
  | .decl ds φ => inScope do
    for (x, t) in ← whereLocals C ds do
      modify fun (Γ, k) => (setBy x t Γ, k)
    elabKeyFml φ

/-- **A written line's key, by name**, quoted: `elabDlOpen`'s parameters in
scope, the line read by `elabKeyFml`. -/
def elabKeyQ (φ : RawFml) : Except String Lean.Expr :=
  let (params, _, _) := dlParams C φ false
  ((elabKeyFml C φ).run { funs := C.funs }).run' (params, 1) |>.map LineKey.quote

end Read

/-! ## Putting the Lean terms back -/

section Fill

open Lean Elab Term Meta

/-- The `i` of a quoted `Fml.slotC i`, and the context it stands at. -/
def slotIdxC? (e : Lean.Expr) : Option (Nat × Lean.Expr) := do
  guard (e.isAppOfArity ``Fml.anon 4)
  let d := e.appArg!
  guard (d.isAppOfArity ``Fml.defined 3)
  let t := d.appArg!
  guard (t.isAppOfArity ``Tm.app2 8)
  let r := t.appArg!
  guard (r.isAppOfArity ``Tm.app0 4)
  let o := r.appArg!
  guard (o.isAppOfArity ``Op0.root 1)
  let .lit (.strVal s) := o.appArg! | none
  guard (s.startsWith "⟪" && s.endsWith "⟫")
  let i ← ((s.drop 1).dropRight 1).toNat?
  pure (i, e.getArg! 1)

/-- The formula whose readings at the diamond (`d`) and at the box (`b`)
are given, with its Lean terms back: `m` where `d` has the diamond and `b`
the box, the hole `holes[i]` at the slot `i`, elaborated at the type
`Fml C Γ` of the place it stands in. -/
partial def fillSlotsC (c : Lean.Expr) (m? : Option Lean.Expr) (holes : Array Syntax)
    (d b : Lean.Expr) : TermElabM Lean.Expr := do
  if let some m := m? then
    if d.isConstOf ``Modality.diamond && b.isConstOf ``Modality.box then return m
  if let some (i, Γ) := slotIdxC? d then
    if (slotIdxC? b).map (·.1) == some i then
      let some h := holes[i]? | throwError "cdl[C]: no Lean formula {i}"
      let some t := fmlHole? h | throwError "cdl[C]: not a formula hole"
      return ← withRef h do
        if let `($x:ident) := t then
          if (← resolveLocalName x.getId).isNone && (← resolveGlobalName x.getId).isEmpty then
            throwError "a name where a formula stands is a Lean formula (φ : Post C Γ): \
              unknown `{x}`"
        withoutAutoBoundImplicit do
          elabTermEnsuringType t (mkApp2 (mkConst ``Fml) c Γ)
  match d, b with
  | .app f x, .app g y => return .app (← fillSlotsC c m? holes f g) (← fillSlotsC c m? holes x y)
  | _, _ => if d == b then pure d else throwError "cdl[C, m]: the readings at the diamond and at the box differ"

end Fill

/-! ## `cdl[C]{ … }` and `cdl!{ … }` -/

/-- `cdl[C]{ φ }`: `dl[C]{ φ }` read into a scoped formula `Fml C []`. -/
syntax "cdl[" term "]{ " dl_fml " }" : term

/-- `cdl[C, m]{ φ }`: `cdl[C]{ φ }` at the modality `m`. -/
syntax "cdl[" term ", " term "]{ " dl_fml " }" : term

/-- `cdl!{ φ }`: `cdl[C]{ φ }` for the file's `InContract` contract. -/
syntax "cdl!{ " dl_fml " }" : term

/-- `cdl![m]{ φ }`: `cdl[C, m]{ φ }` for the file's `InContract` contract. -/
syntax "cdl![" term "]{ " dl_fml " }" : term

/-- A sequent line, `cdl[C]{ Γ ⟹ φ }`: the formula `a₁ → … → φ`. -/
syntax (name := cdlSeq) "cdl[" term "]{ " sepBy1(dl_fml, ", ") " ⟹ " dl_fml " }" : term
@[inherit_doc cdlSeq] syntax "cdl[" term ", " term "]{ " sepBy1(dl_fml, ", ") " ⟹ " dl_fml " }" : term
@[inherit_doc cdlSeq] syntax "cdl!{ " sepBy1(dl_fml, ", ") " ⟹ " dl_fml " }" : term
@[inherit_doc cdlSeq] syntax "cdl![" term "]{ " sepBy1(dl_fml, ", ") " ⟹ " dl_fml " }" : term

open Lean Elab Term Meta in
/-- `elabAgainst` with no kernel check of the throwaway definition it
evaluates (`debug.skipKernelTC`), as `Calculus/Chains.lean`'s
`evalQuoted`: it returns a quoted formula, which the kernel checks where it
is used.  The check cost about 7 ms a formula. -/
def elabAgainstQ (c : Lean.Term) (f : Lean.Term → TermElabM Lean.Term) : TermElabM Lean.Expr :=
  withOptions (debug.skipKernelTC.set · true) (elabAgainst c f)

open Lean Elab Term Meta in
/-- `cdl[C, m]{ φ }`, `m` optional: a
modality that is no constructor is read twice, at the diamond and at the
box, and `fillSlotsC` puts it and the Lean formulas back.  `useAll` as
`elabDlCN`'s. -/
def elabCdlAt (c : Lean.Term) (m? : Option Lean.Term) (φ : TSyntax `dl_fml)
    (useAll : Bool := true) (keepAll : Bool := false) (keep : List String := []) :
    TermElabM Lean.Expr := do
  let holes := fmlHoles φ
  let m? ← m?.mapM fun m => do instantiateMVars (← elabTermEnsuringType m (mkConst ``Modality))
  -- a hole that is no postcondition may write fresh variables the reading
  -- cannot see: captures are then numbered past every written index
  let opaqueHole ← holes.anyM fun h => do
    let some t := fmlHole? h | return true
    withoutModifyingState do
      try
        let e ← withoutErrToSorry <| withoutAutoBoundImplicit <| elabTerm t none
        return !(← whnfR (← inferType e)).isAppOf ``Post
      catch _ => return true
  let pastAll := quote opaqueHole
  let useAllQ := quote useAll
  let keepAllQ := quote keepAll
  let keepQ := quote keep
  let read (μ : Option Lean.Name) : TermElabM Lean.Term :=
    liftMacroM (expandFml { either := μ.map fun n => (mkCIdent n : Lean.Term), holes } φ)
  let once (μ : Option Lean.Name) : TermElabM Lean.Expr := do
    let raw ← read μ
    elabAgainstQ c fun q => `((elabDlCN $c $raw $pastAll $useAllQ $keepAllQ $keepQ).map fun r =>
      Fml.markExplicit r.1 (Fml.quote $q r.2))
  let (d, b) ← match m? with
    | none => do let e ← once none; pure (e, e)
    | some m =>
      if m.isConstOf ``Modality.diamond || m.isConstOf ``Modality.box then
        let e ← once m.constName?
        pure (e, e)
      else
        let rd ← read ``Modality.diamond
        let rb ← read ``Modality.box
        let e ← elabAgainstQ c fun q =>
          `(((do
              let (n₁, d) ← elabDlCN $c $rd $pastAll $useAllQ $keepAllQ $keepQ
              let (n₂, b) ← elabDlCN $c $rb $pastAll $useAllQ $keepAllQ $keepQ
              pure (n₁, n₂, Fml.and d b)) : Except String (Nat × Nat × Fml $c [])).map
                fun r => Fml.markExplicitAnd r.1 r.2.1 (Fml.quote $q r.2.2))
        let #[_, _, d, b] := e.getAppArgs | throwError "cdl[C, m]: not two readings{indentExpr e}"
        pure (d, b)
  if holes.isEmpty && d == b then return d
  let cE ← withTransparency .instances <| whnf (← elabTermAndSynthesize c (mkConst ``Contract))
  fillSlotsC cE m? holes d b

open Lean Elab Term Meta in
elab_rules : term
  | `(cdl[ $c ]{ $φ:dl_fml }) => elabCdlAt c none φ
  | `(cdl[ $c, $m ]{ $φ:dl_fml }) => elabCdlAt c (some m) φ

macro_rules
  | `(cdl!{ $φ:dl_fml }) => `(cdl[InContract.contract]{ $φ })
  | `(cdl![ $m ]{ $φ:dl_fml }) => `(cdl[InContract.contract, $m]{ $φ })
  | `(cdl[ $c ]{ $[$as:dl_fml],* ⟹ $φ:dl_fml }) => `(cdl[$c]{ ($[$as],* ⟹ $φ) })
  | `(cdl[ $c, $m ]{ $[$as:dl_fml],* ⟹ $φ:dl_fml }) => `(cdl[$c, $m]{ ($[$as],* ⟹ $φ) })
  | `(cdl!{ $[$as:dl_fml],* ⟹ $φ:dl_fml }) => `(cdl[InContract.contract]{ ($[$as],* ⟹ $φ) })
  | `(cdl![ $m ]{ $[$as:dl_fml],* ⟹ $φ:dl_fml }) =>
    `(cdl[InContract.contract, $m]{ ($[$as],* ⟹ $φ) })

/-! ## `dl[C]{ … }`: scoped -/

/-- Whether a raw formula, as `expandFml` writes it, has a modality. -/
def rawHasModal (raw : Lean.Syntax) : Bool :=
  (raw.find? fun s => s.isIdent && s.getId.eraseMacroScopes.toString.endsWith "RawFml.modal").isSome

open Lean Elab Term Meta in
/-- `dl[C]{ φ }` and `dl[C, m]{ φ }`: `cdl[C]{ φ }` (`elabCdlAt`), a
`Fml C []` with or without a modality, but with its parameters bound by
hidden binders, printing as nothing (the flip's `cdl!` binds a value one by
`∀`). -/
@[term_elab dlAt, term_elab dlAtM]
def elabDlAuto : TermElab := fun stx ty? => do
  let (c, m?, φ) ← match stx with
    | `(dl[ $c ]{ $φ:dl_fml }) => pure (c, none, φ)
    | `(dl[ $c, $m ]{ $φ:dl_fml }) => pure (c, some m, φ)
    | _ => throwUnsupportedSyntax
  if let some ty := ty? then tryPostponeIfMVar ty
  elabCdlAt c m? φ (useAll := false)


/-! ## A storage term and a path, scoped -/

/-- `st!{ s }`, `pt!{ p }`: a storage term and a storage path read against the
file's contract at the empty scope, as `dl!{ … }` reads them: the operands of
a law's premise (`Tm.KindFreeAt st!{ save(storage, alice.age, 1) } pt!{ alice }`).
The path is read as in the frame of a `select`: its root may be a member
(`account`). -/
syntax "st!{ " dl_term " }" : term
@[inherit_doc «termSt!{_}»] syntax "pt!{ " dl_term " }" : term

open Lean Elab Term Meta in
elab_rules : term
  | `(st!{ $t:dl_term }) => do
    let raw ← liftMacroM (expandTerm t)
    let c ← `(InContract.contract)
    elabAgainst c fun q =>
      `((tStor $c [] $raw).bind (·.resolve []) |>.map (Tm.quote $q))
  | `(pt!{ $t:dl_term }) => do
    let raw ← liftMacroM (expandTerm t)
    let c ← `(InContract.contract)
    elabAgainst c fun q =>
      `((tFPath $c [] $raw).bind (·.resolve []) |>.map (Tm.quote $q))

end Solidity
