import Solidity.Calculus.Notation
import Solidity.Calculus.TacticSyntax
import Solidity.Calculus.TreeData
import Solidity.Calculus.ChainRewrites
import Solidity.Calculus.ChainBranches
import Solidity.Calculus.Literals

/-!
# Chains past the program: rewrite links on `Update.lean`'s lines

A worked chain (`Examples/Chains/`) runs the scoped strategy
(`Calculus/Core/Chains.lean`) and, past the program, goes on from the
erasure of its last line by rewrites (`Calculus/ChainRewrites.lean`): the
stack merges into one parallel update, and a Theory law reads a term down
to its value.  This module is that second half, on `Update.lean`'s formulas:

* `φ ~[n]~> ψ` — the rewrite `n` (an update rule, KeY's name, or a law)
  turns `φ` into `ψ` (`Fml.RwBy`), its label a rewrite of
  `Calculus/ChainRewrites.lean` (`LineRw`): the elaborator finds, from the
  line before, the position on the update spine and the law's instance (as
  `rw` finds one) that give the line after, and the kernel checks
  `r.apply φ = some ψ`.  A name that is no rewrite, a rewrite that does not
  apply and a name that resolves twice are errors;
* `φ ~=> ψ` — a rewrite the arrow does not name (`Fml.RwAny`): the line
  after picks it, `sol_chain` trying the update rules and then the laws
  (`rwAnyArrows`) until one gives it;
* `φ ~~> ψ` (`Fml.Leads`): wherever `ψ` holds, `φ` does, what a chain
  composes to; a chain of rewrites is `Fml.Via`, `Fml.Via.leads` makes it a
  `~~>`, and `Fml.Leads.via` composes segments of a long one.

The steps of the strategy (`~>`, `~*>`, `~[r]~>` for a rule) are the scoped
chains'; today's, on `Update.lean`'s formulas, went with today's rule table
(W4 `calc-del`, `docs/intrinsic.md`).  A line keeps a modality open with
`dl![m]{ … }` and a postcondition with `φ : Post C`.

**Checking a rewrite.**  A rewrite acts on the update spine, never inside
the postcondition or on the modality, so its `rfl` computes past both; but
the elaborator's reduction (`Meta.whnf`) over a whole line is two orders of
magnitude slower than the kernel's.  The statement's elaborator therefore
asks the kernel (`kernelDefEq`, in `rwProof`), once, to choose a label, and
`sol_chain` takes the proof it found from there (`rwProofCache`) instead of
reducing the line again.  A merge of two updates that may halt compares
the line's modality with itself, which a variable `m` does not decide: that
link is `Modality.casesOn m`, one kernel `rfl` per modality.  A written
chain's lines are elaborated once each (`elabChain`), not once per link
they stand in.
-/

namespace Solidity

open Semantics

variable {C : Contract}

/-! ## An abstract postcondition

A chain is stated for any postcondition `φ`, a `Post C`, written by its
name in a line (`dl![m]{ … φ }`, printed back so).  A rewrite that asks it
which fresh variables it reads (`LineRw.simplifyFresh`) is proved from
`Post.noFresh` (`proveRw`). -/

/-- A postcondition `φ`: a formula that names no fresh variable
(`se1`, `sp1`, …), so that the rules' fresh names avoid it whatever it is,
and has no modality, so that the strategy never steps into it.

Example: `⟨dl!{ alice.account.balance == 10 }, by decide, by decide⟩`, which
`{ fml := dl!{ alice.account.balance == 10 } }` abbreviates. -/
structure Post (C : Contract) where
  fml : Fml C
  noFresh : maxIdx fml.vars = 0 := by decide
  inactive : fml.active = false := by decide

attribute [coe] Post.fml

/-- A postcondition names no fresh variable: `simplifyUpdate` over it drops
a capture of the rules (`LineRw.simplifyFresh`). -/
theorem Post.freshVars_eq_nil (φ : Post C) : φ.fml.freshVars = [] := by
  rw [Fml.freshVars_eq, List.filter_eq_nil_iff]
  intro x hx
  have : x.idx ≤ 0 := φ.noFresh ▸ le_maxIdx hx
  simp only [bne_iff_ne, ne_eq, Decidable.not_not]
  omega

instance : Coe (Post C) (Fml C) := ⟨Post.fml⟩

/-! ## Rewrites and chains of them -/

/-- `φ ~[n]~> ψ` past the strategy: the rewrite `r` of
`Calculus/ChainRewrites.lean` turns `φ` into `ψ`, and `n` is the rule the
arrow names (`sequentialToParallel`, `findOnSave`, …).  The rewrite is the
one the elaborator found for `n` on `φ`: its position on the update spine,
and for a law its instance. -/
def Fml.RwBy (_n : String) (r : LineRw C) (φ ψ : Fml C) : Prop := r.apply φ = some ψ

/-- `φ ~~> ψ`: to prove `φ`, prove `ψ` — wherever `ψ` holds, `φ` does.  What
a chain with a rewrite in it composes to (a rewrite and a step may commute,
so it is no derivation `~*>`). -/
def Fml.Leads (φ ψ : Fml C) : Prop := ∀ σ, holds σ ψ → holds σ φ

@[inherit_doc] notation:50 φ:51 " ~~> " ψ:51 => Fml.Leads φ ψ

/-- `φ ~=> ψ` past the strategy: some rewrite of `Calculus/ChainRewrites.lean`,
an update rule or a Theory law, turns `φ` into `ψ`.  The arrow names none:
the line after picks it (`sol_chain` searches for it). -/
def Fml.RwAny (φ ψ : Fml C) : Prop := ∃ r : LineRw C, r.apply φ = some ψ

/-- The arrows of a chain past the program. -/
inductive Link (C : Contract) : Type where
  /-- `~[n]~>` for a rewrite: an update rule or a Theory law -/
  | rw (n : String) (r : LineRw C)
  /-- `~=>`: a rewrite the line after picks -/
  | rwAny

/-- What an arrow says about the two lines it joins. -/
@[reducible] def Link.Rel : Link C → Fml C → Fml C → Prop
  | .rw n r => Fml.RwBy n r
  | .rwAny => Fml.RwAny

/-- `φ ~> φ₁ ~*> φ₂ …`: every link of a chain that starts at `φ` holds (a
conjunction, one part per arrow).  A proposition, so a chain is a `theorem`:
a `def` of data would have its value, every line in it, searched for proofs
to abstract when it is added. -/
@[reducible] def Fml.Via : Fml C → List (Link C × Fml C) → Prop
  | _, [] => True
  | φ, [(l, ψ)] => l.Rel φ ψ
  | φ, (l, ψ) :: w :: ws => l.Rel φ ψ ∧ Fml.Via ψ (w :: ws)

/-- The last line of a chain. -/
def Fml.Via.last : Fml C → List (Link C × Fml C) → Fml C
  | φ, [] => φ
  | _, (_, ψ) :: ws => Fml.Via.last ψ ws

/-! ## The notation

The arrows are the scoped chains' too (`Calculus/Core/Chains.lean`), which
read a chain whose first line is scoped and hand any other here. -/


/-- `stepBy% φ r ψ`: `φ ~[r]~> ψ`, with `φ` elaborated once: a rule of the
strategy (`Fml.StepBy`) or a rewrite (`Fml.RwBy`).  Elaborated at the end of
the module, after `sol_chain`'s search. -/
syntax "stepBy% " term:max ident term:max : term

/-- `link% φ r ψ`: the `Link` of `φ ~[r]~> ψ` in a chain. -/
syntax "link% " term:max ident term:max : term

declare_syntax_cat chain_arrow
syntax "~> " : chain_arrow
syntax "~*> " : chain_arrow
syntax "~[" ident "]~> " : chain_arrow
syntax "~=> " : chain_arrow
/-- `a ~> b`, `a ~*> b`, `a ~[r]~> b`, and chains of them: `a ~*> b ~[r]~> c ~*> d`. -/
syntax:50 (name := chainStx) term:51 (ppIndent(ppLine chain_arrow term:51))+ : term

open Lean in
/-- Whether a line of a chain is left to be found: `_` or `?x`. -/
def chainHole (s : Syntax) : Bool :=
  s.isOfKind ``Lean.Parser.Term.hole || s.isOfKind ``Lean.Parser.Term.syntheticHole

open Lean in
/-- Whether a chain is two links or more, every line written: `elabChain`
elaborates those, at the end of the module. -/
def chainWritten (stx : Syntax) : Bool :=
  stx[1].getArgs.size ≥ 2 && !chainHole stx[0] && stx[1].getArgs.all fun l => !chainHole l[1]

open Lean in
/-- One link is the relation itself; a longer chain is `Fml.Via`, each line
in the place of every link it stands in (`link% a r b`).  A step of the
strategy (`~>`, `~*>`, `~[r]~>` for a rule) is the scoped chains'. -/
def expandChainStx : Macro := fun stx => do
  let a : Lean.Term := ⟨stx[0]⟩
  -- applications are built directly: in a quotation `$a $b` would read `$b` as an arrow
  let app (f : Lean.Name) (args : Array Lean.Term) : Lean.Term := Syntax.mkApp (mkCIdent f) args
  let mut prev := a
  let mut links := #[]
  for l in stx[1].getArgs do
    let b : Lean.Term := ⟨l[1]⟩
    let link ← match (⟨l[0]⟩ : TSyntax `chain_arrow) with
      | `(chain_arrow| ~=>) => pure (← `(Link.rwAny), app ``Fml.RwAny #[prev, b])
      | `(chain_arrow| ~[ $r:ident ]~>) =>
        pure (← `(link% ($prev) $r ($b)), ← `(stepBy% ($prev) $r ($b)))
      | _ => Macro.throwErrorAt l[0] "a step of the strategy (`~>`, `~*>`) is a scoped chain's: \
          write the first line scoped (`open scoped Solidity.Core.Surface`)"
    links := links.push (link.1, link.2, b)
    prev := b
  match links with
  | #[(_, rel, _)] => pure rel
  | _ =>
    let ws ← links.mapM fun (l, _, b) => `((($l : Link _), $b:term))
    pure (app ``Fml.Via #[a, ← `([$ws,*])])

open Lean in
/-- A chain with a line left to be found, or one link: `expandChainStx`.  A
written chain of two links or more is `elabChain`'s. -/
@[macro chainStx] def expandChain : Macro := fun stx =>
  if chainWritten stx then Macro.throwUnsupported else expandChainStx stx

namespace Chain
section Print
open Lean Meta PrettyPrinter Delaborator SubExpr

/-- A line of a chain: `dl{ φ }`, with its `where` clause, or Lean's own
printing. -/
def ppLine (e : Lean.Expr) : MetaM Lean.Term := do
  let φ ← ppFml e
  if isEscape φ then escapeTerm e else `(dl{ $(← withDecls e φ):dl_fml })

/-- The arrow a `Link` stands for. -/
def arrowOf (l : Lean.Expr) : MetaM (TSyntax `chain_arrow) := do
  let l ← whnfR (← instantiateMVars l)
  if l.isAppOfArity ``Link.rwAny 1 then `(chain_arrow| ~=>)
  else if l.isAppOfArity ``Link.rw 3 then
    let .lit (.strVal n) := l.getArg! 1 | failure
    `(chain_arrow| ~[$(mkIdent n.toName):ident]~>)
  else failure

def chainNode (a : Lean.Term) (arrows : Array (TSyntax `chain_arrow × Lean.Term)) : Lean.Term :=
  ⟨mkNode ``chainStx #[a, mkNullNode (arrows.map fun (l, b) => mkNode groupKind #[l, b])]⟩

/-- `Fml.RwBy n r φ ψ`: `φ ~[n]~> ψ`. -/
@[delab app.Solidity.Fml.RwBy]
def delabRwBy : Delab := do
  let e ← getExpr
  guard (e.getAppNumArgs == 5)
  let .lit (.strVal n) := e.getArg! 1 | failure
  return chainNode (← withNaryArg 3 delab)
    #[(← `(chain_arrow| ~[$(mkIdent n.toName):ident]~>), ← withNaryArg 4 delab)]

/-- `Fml.RwAny φ ψ`: `φ ~=> ψ`. -/
@[delab app.Solidity.Fml.RwAny]
def delabRwAny : Delab := do
  let e ← getExpr
  guard (e.getAppNumArgs == 3)
  return chainNode (← withNaryArg 1 delab) #[(← `(chain_arrow| ~=>), ← withNaryArg 2 delab)]

/-- `Fml.Via φ [(l₁, φ₁), …]`: `φ l₁ φ₁ …`. -/
@[delab app.Solidity.Fml.Via]
def delabVia : Delab := do
  let e ← getExpr
  guard (e.getAppNumArgs == 3)
  let some ws ← listElems? (e.getArg! 2) | failure
  guard !ws.isEmpty
  let arrows ← ws.mapM fun w => do
    let w ← whnfR w
    guard (w.isAppOfArity ``Prod.mk 4)
    pure (← arrowOf (w.getArg! 2), ← ppLine (w.getArg! 3))
  return chainNode (← withNaryArg 1 delab) arrows

end Print
end Chain

/-! ## Soundness: a chain is a proof -/

/-- A rewrite is sound: where the line after it holds, the line before holds.

Example: `{ se1 := 10 } { sp1 := alice.account } ⟨ sp1.balance = se1; ⟩ φ
~[sequentialToParallel]~> { se1 := 10 ‖ sp1 := alice.account } ⟨ sp1.balance = se1; ⟩ φ`. -/
theorem Fml.RwBy.sound {n : String} {r : LineRw C} {φ ψ : Fml C} (h : Fml.RwBy n r φ ψ) :
    φ ~~> ψ :=
  r.sound h

/-- Some rewrite is sound: whichever one the line after picked. -/
theorem Fml.RwAny.sound {φ ψ : Fml C} (h : Fml.RwAny φ ψ) : φ ~~> ψ :=
  let ⟨r, hr⟩ := h
  r.sound hr

/-- A chain is sound state by state: where its last line holds, its first
line holds, whatever its arrows. -/
theorem Fml.Via.sound : {φ : Fml C} → {ws : List (Link C × Fml C)} → Fml.Via φ ws →
    φ ~~> Fml.Via.last φ ws
  | _, [], _ => fun _ h => h
  | _, [(.rw _ _, _)], h => Fml.RwBy.sound h
  | _, [(.rwAny, _)], h => Fml.RwAny.sound h
  | _, (.rw _ _, _) :: _ :: _, ⟨s, v⟩ => fun σ h => Fml.RwBy.sound s σ (Fml.Via.sound v σ h)
  | _, (.rwAny, _) :: _ :: _, ⟨s, v⟩ => fun σ h => Fml.RwAny.sound s σ (Fml.Via.sound v σ h)

/-- A chain is a proof: to prove its first line, prove its last.

Example: `{ x := 1 } { y := x } φ ~[sequentialToParallel]~> { x := 1 ‖ y := 1 } φ`
proves its first line from its last. -/
theorem Fml.Via.valid {φ : Fml C} {ws : List (Link C × Fml C)} (v : Fml.Via φ ws)
    (h : ⊨ Fml.Via.last φ ws) : ⊨ φ :=
  fun σ => v.sound σ (h σ)

/-- A chain with rewrites is a proof: to prove its first line, prove its last.

Example: `BalanceWrite.chain .box φ` of `Examples/Chains/Storage.lean`, down to the
last line, proves `[ alice.account.balance = 10; ] φ` from
`{ se1 := 10 ‖ sp1 := alice.account ‖ storage := save(storage, alice.account.balance, 10) } φ`. -/
theorem Fml.Leads.valid {φ ψ : Fml C} (h : φ ~~> ψ) (hψ : ⊨ ψ) : ⊨ φ :=
  fun σ => h σ (hψ σ)

/-- `~~>` composes: to prove `φ`, prove `ψ`; to prove `ψ`, prove `χ`. -/
theorem Fml.Leads.comp {φ ψ χ : Fml C} (h₁ : φ ~~> ψ) (h₂ : ψ ~~> χ) : φ ~~> χ :=
  fun σ h => h₁ σ (h₂ σ h)

/-- A line leads to itself: the chain of no links. -/
theorem Fml.Leads.self (φ : Fml C) : φ ~~> φ := fun _ h => h

/-- A chain leads from its first line to its last: `Fml.Via.sound`, under the
name a composition reads by.

Example: `(AgeWriteRead.chain m φ).leads` is
`⟨[ alice.age = 42; uint x = alice.age; ]⟩ φ ~~> { storage := save(storage, alice.age, 42) ‖ x := 42 } φ`. -/
theorem Fml.Via.leads {φ : Fml C} {ws : List (Link C × Fml C)} (v : Fml.Via φ ws) :
    φ ~~> Fml.Via.last φ ws :=
  Fml.Via.sound v

/-- A chain goes on with a segment that starts where it ends: `h` reaches
`ψ`, the segment `v` starts at `ψ`, and together they reach `v`'s last line.
The segments of a long trace compose so, each a `theorem` with its own
heartbeats: `(seg₁ ..).leads.via (seg₂ ..) |>.via (seg₃ ..)`. -/
theorem Fml.Leads.via {φ ψ : Fml C} {ws : List (Link C × Fml C)} (h : φ ~~> ψ)
    (v : Fml.Via ψ ws) : φ ~~> Fml.Via.last ψ ws :=
  h.comp v.leads

universe u v

/-- A relation between lines whose evidence carries the second line's truth
back to the first: every arrow of a chain, and `~~>` itself. -/
class Fml.SoundRel (R : Fml C → Fml C → Sort u) : Prop where
  leads : ∀ {φ ψ : Fml C}, R φ ψ → φ ~~> ψ

instance {n : String} {r : LineRw C} : Fml.SoundRel (Fml.RwBy n r) := ⟨fun h => h.sound⟩
instance : Fml.SoundRel (@Fml.RwAny C) := ⟨fun h => h.sound⟩
instance : Fml.SoundRel (@Fml.Leads C) := ⟨id⟩

/-- A `calc` with a rewrite in it composes to `~~>`; one of steps alone still
composes to `~*>`, whose instances come first. -/
instance (priority := low) {R : Fml C → Fml C → Sort u} {S : Fml C → Fml C → Sort v}
    [Fml.SoundRel R] [Fml.SoundRel S] : @Trans (Fml C) (Fml C) (Fml C) R S Fml.Leads :=
  ⟨fun a b σ h => Fml.SoundRel.leads a σ (Fml.SoundRel.leads b σ h)⟩

/-! ## `sol_chain` on rewrites -/

/-- Each rewrite of `rs` on `φ`: the line after, quoted, or `none`. -/
def Fml.rwQuoted (c : Lean.Expr) (φ : Fml C) (rs : List (Fml C → Option (Fml C))) :
    List (Option Lean.Expr) :=
  rs.map fun r => (r φ).map (Fml.quote c)

namespace Chain
section Tactic
open Lean Elab Tactic Meta


/-- The Lean terms of a line (`fillSlots`): its modality, a variable, and
its postconditions `↑φ` by slot, each with its `Post.noFresh`. -/
structure Splice where
  modality : Option Lean.Expr := none
  fmls : Array Lean.Expr := #[]
  noFresh : Array Lean.Expr := #[]

/-- The line with each open postcondition `↑φ` in its slot. -/
partial def punch (C : Lean.Expr) : Lean.Expr → StateT Splice MetaM Lean.Expr
  | e@(.app f x) => do
    unless e.isAppOfArity ``Post.fml 2 && e.hasFVar do
      return .app (← punch C f) (← punch C x)
    let sp ← get
    if let some i := sp.fmls.findIdx? (· == e) then return slotExpr C i
    set { sp with fmls := sp.fmls.push e,
                  noFresh := sp.noFresh.push (mkApp2 (mkConst ``Post.noFresh) (e.getArg! 0) x) }
    return slotExpr C sp.fmls.size
  | .mdata _ e => punch C e
  | e => return e

/-- The modality of a line with its postconditions in their slots, when it
is a variable; no other variable may be left. -/
def modalityOf? (φ : Lean.Expr) : MetaM (Option Lean.Expr) := do
  let fvs := (collectFVars {} φ).fvarIds
  if fvs.isEmpty then return none
  for x in fvs do
    let ty ← instantiateMVars (← x.getType)
    if ty.isConstOf ``Modality && fvs.size == 1 then return some (.fvar x)
    if ty.isAppOfArity ``Fml 1 then
      throwError "sol_chain: {mkFVar x} may name a fresh variable or have a modality: \
        take it as a postcondition, `{mkFVar x} : Post {ty.appArg!}`"
    unless ty.isConstOf ``Modality do
      throwError "sol_chain: {mkFVar x} is free in the line: only a modality `m` and \
        postconditions `φ : Post C` may be{indentExpr φ}"
  throwError "sol_chain: the line is under two modalities: take `cases` on one{indentExpr φ}"

/-- `some ψ = some ψ`, the proof of `φ.step = some ψ` and `φ.run n = some ψ`. -/
def someRefl (C ψ : Lean.Expr) : Lean.Expr :=
  let ty := mkApp (mkConst ``Option [0]) (mkApp (mkConst ``Fml) C)
  mkApp2 (mkConst ``Eq.refl [1]) ty (mkApp2 (mkConst ``Option.some [0]) (mkApp (mkConst ``Fml) C) ψ)

/-- `a ≡ b` by the kernel's definitional equality: the check a `rfl` meets
when the declaration is added, made now instead of by the elaborator's
reduction (`Meta.whnf`), which on a whole line is two orders of magnitude
slower (`docs/kernel-port.md`).  `false` where either side has a
metavariable, which the kernel does not take. -/
def kernelDefEq (a b : Lean.Expr) : MetaM Bool := do
  let a ← instantiateMVars a
  let b ← instantiateMVars b
  if a.hasMVar || b.hasMVar then return false
  return Kernel.isDefEqGuarded (← getEnv) (← getLCtx) a b

/-- Close each goal `a = b` the kernel computes: `Eq.refl b`, checked by
`kernelDefEq`.  The goals it cannot close are returned. -/
def kernelRefl (gs : List MVarId) : MetaM (List MVarId) :=
  gs.filterM fun g => do
    let ty ← instantiateMVars (← g.getType)
    let some (_, a, b) := ty.eq? | return true
    unless ← kernelDefEq a b do return true
    g.assign (← mkExpectedTypeHint (← mkEqRefl b) ty)
    return false

/-! ### Rewrite links

`~[n]~>` names a rewrite when `n` is no rule of the strategy: an update rule
of `Calculus/ChainRewrites.lean`'s table, or a law: a term taclet
(`TermTaclet`, `Calculus/TermTaclets.lean`), a law of a memory read
(`EvalLaw`, `Calculus/ChainRewrites.lean`), or a constant whose statement is
one.  The name stands for several rewrites, which the
line before tells apart: the position on the update spine, and for a law its
instance, found in the line as `rw` finds one.  They are tried in a fixed
order (`rwCandidates`), and the label is the first that gives the line after
— or, with the line after left `_`, the first that applies.  So the next
line is computed, as for a step, and the kernel checks `r.apply φ = some ψ`
by `rfl` — or, where the rewrite asks a postcondition `φ : Post C` what it
reads (`LineRw.simplifyFresh`), `sol_chain` proves it from `Post.noFresh`
(`proveRw`), as it proves a step's fresh index (`proveFresh`). -/

/-- What `~[n]~>` names past the strategy. -/
inductive RwArrow where
  /-- An update rule of the table (`rwTable`). -/
  | table (n : Lean.Name)
  /-- A law: a term taclet, or a constant whose statement is one. -/
  | law (c : Lean.Name)
  /-- A law of a memory read (`EvalLaw`), or a constant whose statement is one. -/
  | evalLaw (c : Lean.Name)
  /-- A literal law (`LitLaw`), or a constant whose statement is one. -/
  | litLaw (c : Lean.Name)

/-- The update rules an arrow names, KeY's names: `sequentialToParallel`
merges, `simplifyUpdate` drops, `applySkip` and the `applyOnRigid…` apply,
`concrete` folds the literal connectives. -/
def rwTable : List Lean.Name :=
  [`sequentialToParallel, `simplifyUpdate, `applySkip, `applyOnRigid, `applyOnRigidBox,
    `applyStorageBox, `applyOnPV, `concrete]

/-- The kind of law the constant `c` states under its arguments:
`TermTaclet`, `EvalLaw`, `LitLaw`, or none. -/
def lawKind? (c : Lean.Name) : MetaM (Option Lean.Name) := do
  let some info := (← getEnv).find? c | return none
  forallTelescope info.type fun _ ty => do
    let ty ← whnfR ty
    if ty.isAppOf ``TermTaclet then return some ``TermTaclet
    if ty.isAppOf ``EvalLaw then return some ``EvalLaw
    if ty.isAppOf ``LitLaw then return some ``LitLaw
    return none

/-- Whether the constant `c` states a `TermTaclet`, an `EvalLaw` or a
`LitLaw`, under its arguments. -/
def isLaw (c : Lean.Name) : MetaM Bool := return (← lawKind? c).isSome

/-- The two sides of a law's statement, `TermTaclet C t t'`, `EvalLaw C u t t'`
or `LitLaw C t t'`. -/
def lawSides? (ty : Lean.Expr) : Option (Lean.Expr × Lean.Expr) :=
  if ty.isAppOfArity ``TermTaclet 3 || ty.isAppOfArity ``LitLaw 3 then
    let args := ty.getAppArgs
    some (args[1]!, args[2]!)
  else if ty.isAppOfArity ``EvalLaw 4 then
    let args := ty.getAppArgs
    some (args[2]!, args[3]!)
  else none

/-- The arrow for the law `c` of kind `k`. -/
def RwArrow.ofLaw (k c : Lean.Name) : RwArrow :=
  if k == ``EvalLaw then .evalLaw c else if k == ``LitLaw then .litLaw c else .law c

/-- What `~[r]~>` names: `none` for a rule of the strategy (a constructor of
the scoped `Core.Taclet` or `Core.LeanTaclet`, `emptyModality`), else a
rewrite; any other name is an error, and so is a name that resolves to more
than one constant. -/
def rwArrow? (r : Ident) : MetaM (Option RwArrow) := do
  let n := r.getId
  let env ← getEnv
  if n == `emptyModality || env.contains (`Solidity.Core.Taclet ++ n) ||
      env.contains (`Solidity.Core.LeanTaclet ++ n) then
    return none
  if rwTable.contains n then return some (.table n)
  if env.contains (``TermTaclet ++ n) then return some (.law (``TermTaclet ++ n))
  if env.contains (``EvalLaw ++ n) then return some (.evalLaw (``EvalLaw ++ n))
  if env.contains (``LitLaw ++ n) then return some (.litLaw (``LitLaw ++ n))
  let cs := ((← resolveGlobalName n).filterMap fun (c, fs) =>
    if fs.isEmpty then some c else none).eraseDups
  match cs with
  | [c] => if let some k ← lawKind? c then return some (.ofLaw k c)
  | [] => pure ()
  | cs => throwError "~[{r}]~>: ambiguous, {r} may be {", ".intercalate (cs.map toString)}"
  throwError "~[{r}]~>: {r} is no rule: not a `Taclet` or `LeanTaclet` constructor, not an \
    update rule ({", ".intercalate (rwTable.map toString)}), not a term taclet (`TermTaclet`), \
    not a law of a memory read (`EvalLaw`), not a literal law (`LitLaw`)"

/-- The formula below `n` updates of the line `e`. -/
partial def bodyBelow (e : Lean.Expr) : Nat → MetaM Lean.Expr
  | 0 => pure e
  | n + 1 => do
    let e ← whnf e
    if e.isAppOfArity ``Fml.upd 4 then bodyBelow e.appArg! n else pure e

/-- What a part of a line folds to under `Fml.concrete`, as far as the
elaborator can tell: `true`, `false`, a formula it must not look at (a
postcondition variable, or a fold that returns one), or anything else. -/
inductive LitStatus where
  | tt | ff | opaque | other
  deriving DecidableEq

/-- The skeleton of a formula (`Skel`), read off the line: the connectives,
the literal leaves, the updates; a postcondition variable, a program, a
quantifier and a `havoc` are opaque, and so is a connective's part whose
fold may return an opaque formula (`LitStatus`), which the folds then do
not test.  The status mirrors `Fml.concrete`'s folds so the flags are exact. -/
partial def skelOf (e : Lean.Expr) : MetaM (Skel × LitStatus) := do
  let e ← instantiateMVars e
  let isLit (t : Lean.Expr) : MetaM Bool := do
    return (← whnfTm t).isAppOfArity ``Term.lit 2
  match e.getAppFnArgs with
  | (``Fml.tt, #[_]) => return (.lit, .tt)
  | (``Fml.eq, #[_, a, b]) =>
    if (← isLit a) && (← isLit b) then
      let va := (← whnfTm a).appArg!
      let vb := (← whnfTm b).appArg!
      return (.lit, if ← isDefEq va vb then .tt else .ff)
    return (.lit, .other)
  | (``Fml.defined, #[_, t]) => return (.lit, if ← isLit t then .tt else .other)
  | (``Fml.not, #[_, a]) =>
    let (sa, ta) ← skelOf a
    let st := match ta with
      | .ff => .tt
      | .tt => .ff
      | .opaque => .opaque
      | .other => .other
    return (.not (ta == .opaque) sa, st)
  | (``Fml.and, #[_, a, b]) =>
    let (sa, ta) ← skelOf a
    let (sb, tb) ← skelOf b
    let st := if ta == .tt then tb else if ta == .ff then .ff
      else if tb == .tt then ta else if tb == .ff then .ff else .other
    return (.and (ta == .opaque) (tb == .opaque) sa sb, st)
  | (``Fml.imp, #[_, a, b]) =>
    let (sa, ta) ← skelOf a
    let (sb, tb) ← skelOf b
    let st := if ta == .tt then tb else if ta == .ff then .tt
      else if tb == .tt then .tt else if tb == .ff then (if ta == .opaque then .opaque else .other)
      else .other
    return (.imp (ta == .opaque) (tb == .opaque) sa sb, st)
  | (``Fml.upd, #[_, _, _, ψ]) => return (.upd (← skelOf ψ).1, .opaque)
  | _ => return (.opaque, .opaque)

/-- The skeleton of the formula below `n` updates of the line `e`, quoted. -/
def skelBelow (e : Lean.Expr) (n : Nat) : MetaM Lean.Expr := do
  return toExpr (← skelOf (← bodyBelow e n)).1

/-- The number of updates in front of a line. -/
partial def spineLen (e : Lean.Expr) : MetaM Nat := do
  let e ← whnf e
  if e.isAppOfArity ``Fml.upd 4 then return (← spineLen e.appArg!) + 1 else return 0

/-- The subterms of `e` with the head of `p`, outermost and leftmost first. -/
partial def subtermsLike (p e : Lean.Expr) : Array Lean.Expr :=
  let rec go (e : Lean.Expr) (acc : Array Lean.Expr) : Array Lean.Expr :=
    let acc := if !e.hasLooseBVars && e.toHeadIndex == p.toHeadIndex &&
        e.headNumArgs == p.headNumArgs then acc.push e else acc
    match e with
    | .app f x => go x (go f acc)
    | .mdata _ e => go e acc
    | _ => acc
  go e #[]

/-- The positions on the spine of the storage term `S`: each storage subterm
reached through the storage argument of a save, a delete or a select, with
the context (`SCtx`) a hole there stands in. -/
partial def spinePositions (C S : Lean.Expr) (mk : Lean.Expr → Lean.Expr := id) :
    MetaM (Array (Lean.Expr × Lean.Expr)) := do
  let here := (S, mk (mkApp (mkConst ``SCtx.hole) C))
  if S.isAppOfArity ``STerm.save 4 then
    let #[_, S', p, v] := S.getAppArgs | return #[here]
    return #[here] ++ (← spinePositions C S' fun K => mk (mkAppN (mkConst ``SCtx.save) #[C, K, p, v]))
  else if S.isAppOfArity ``STerm.delAt 3 then
    let #[_, S', p] := S.getAppArgs | return #[here]
    return #[here] ++ (← spinePositions C S' fun K => mk (mkAppN (mkConst ``SCtx.delAt) #[C, K, p]))
  else if S.isAppOfArity ``STerm.select 3 then
    let #[_, S', r] := S.getAppArgs | return #[here]
    return #[here] ++ (← spinePositions C S' fun K => mk (mkAppN (mkConst ``SCtx.select) #[C, K, r]))
  else return #[here]

/-- `lhs` matched against `e`: by unification, or, for a law in a storage
context (`find(K[X], q)` with `K` to find), `X` against a position on the
spine of `e`'s storage and `K` the context there. -/
def matchLaw (lhs e : Lean.Expr) : MetaM Bool := do
  if lhs.isAppOfArity ``Term.find 3 then
    let #[C, st, q] := lhs.getAppArgs | return ← isDefEq lhs e
    if st.isAppOfArity ``SCtx.fill 3 then
      let #[_, K, X] := st.getAppArgs | return ← isDefEq lhs e
      if (← instantiateMVars K).isMVar then
        unless e.isAppOfArity ``Term.find 3 do return false
        let #[_, S, q'] := e.getAppArgs | return false
        for (T, Kpos) in ← spinePositions C S do
          let s ← saveState
          if (← isDefEq X T) && (← isDefEq K Kpos) && (← isDefEq q q') then return true
          s.restore
        return false
  isDefEq lhs e

/-- The law `c` at the subterm `e`: `(t, t', h)` when `e` is its left side,
its arguments found there and its side conditions (`hp : p.hasSeg = true`,
…) closed by `rfl` or `decide`, as `sol_rw` closes them (`solRwSide`), or by
a hypothesis of the chain (`findOnDelAtBelow`'s `hk`), matched up to
reducible unfolding only: a hypothesis about another node would otherwise be
compared by unfolding the semantics, a second wasted per instance tried;
else why not, if a side condition is why. -/
def lawAt (c : Lean.Name) (e : Lean.Expr) :
    TermElabM (Except (Option MessageData) (Lean.Expr × Lean.Expr × Lean.Expr)) := do
  let pf ← mkConstWithFreshMVarLevels c
  let (args, _, ty) ← forallMetaTelescope (← inferType pf)
  let ty ← whnfR (← instantiateMVars ty)
  let some (lhs, rhs) := lawSides? ty | return .error none
  unless ← matchLaw lhs e do return .error none
  for a in args do
    let g := a.mvarId!
    if (← g.isAssigned) || !(← isProp (← g.getType)) then continue
    let ty := (← instantiateMVars (← g.getType)).cleanupAnnotations
    let g ← g.replaceTargetDefEq ty
    let closed ← try
        pure (← Term.withoutErrToSorry <|
          Tactic.run g (evalTactic (← `(tactic| first | rfl | decide | with_reducible assumption)))).isEmpty
      catch _ => pure false
    unless closed do
      return .error (some m!"the side condition{indentExpr ty}\nof {lastName c} closes by neither \
        `rfl`, `decide` nor a hypothesis")
  let pf ← instantiateMVars (mkAppN pf args)
  let t' ← instantiateMVars rhs
  if pf.hasExprMVar || t'.hasExprMVar then return .error none
  return .ok (← instantiateMVars lhs, t', pf)

/-- The instances `(t, t', h)` of the law `c` in the line `φ`, outermost and
leftmost first (`lawAt`), and the first side condition that did not close. -/
def lawInstances (c : Lean.Name) (φ : Lean.Expr) :
    TermElabM (Array (Lean.Expr × Lean.Expr × Lean.Expr) × Option MessageData) := do
  let lhs0 ← withoutModifyingState do
    let (_, _, ty) ← forallMetaTelescope (← inferType (← mkConstWithFreshMVarLevels c))
    let ty ← whnfR (← instantiateMVars ty)
    let some (lhs, _) := lawSides? ty | throwError "not a law: {c}"
    instantiateMVars lhs
  let mut out := #[]
  let mut failed := none
  for e in subtermsLike lhs0 φ do
    let s ← saveState
    let r ← try lawAt c e catch _ => pure (.error none)
    s.restore
    match r with
    | .ok i => unless out.any (·.2.2 == i.2.2) do out := out.push i
    | .error m => if failed.isNone then failed := m
  return (out, failed)

/-- The rewrites `~[r]~>` stands for on the line `φ`, in the order they are
tried, and why a law found no instance.  `sequentialToParallel`: the whole
spine merged, then fewer updates, then a run of updates further in (the
longest first), then one pair further in; the others at
each position of the spine, outermost first; then, under a branch,
`sequentialToParallel` at the first spine the skeleton finds
(`LineRw.mergeIn`), `applyOnRigid` and `applyOnRigidBox` through the
connectives (`LineRw.applyOnRigidIn`, `LineRw.applyOnRigidBoxIn`), `applyOnPV`
at each update (`LineRw.applyOnPV`), and `concrete` below each number of
updates (`LineRw.concrete`), each with the
skeleton of the formula it acts on (`skelBelow`).  A law: at each instance,
on the equations, then in each update's right-hand sides when its result
cannot halt — under any modality where the update holds the write the law
reads back (`LineRw.lawUpdAny`), else under the box; a frame or
delete-value law (`TermTaclet.RefLaw`) under any modality where the update
holds its storage operation (`LineRw.lawUpdRef`); and a member-wise law under
any modality (`LineRw.lawUpdEq`).  A literal law: in
each update's right-hand sides (`LineRw.lit`), then in the skeleton below
each number of updates (`LineRw.litEq`). -/
def rwCandidatesWith (keep : Lean.Expr → Bool) (C φ : Lean.Expr) :
    RwArrow → TermElabM (Array Lean.Expr × Option MessageData)
  | .table n => do
    let k ← spineLen φ
    let atPos (f : Lean.Name) (is : List Nat) : Array Lean.Expr :=
      (is.map fun i => mkApp2 (mkConst f) C (toExpr i)).toArray
    let upd (r : Lean.Name) : Array Lean.Expr := ((List.range k).map fun i =>
      mkApp3 (mkConst ``LineRw.updRule) C (mkConst r) (toExpr i)).toArray
    -- a rewrite under a branch takes the skeleton of the formula it acts on,
    -- and is tried only where that skeleton gives it somewhere to act (`fit`)
    let skelAt (n : Nat) : MetaM Skel := do return (← skelOf (← bodyBelow φ n)).1
    let inSkel (f : Lean.Name) (is : List Nat) (body : Nat → Nat) (fit : Skel → Bool) :
        MetaM (Array Lean.Expr) :=
      is.toArray.filterMapM fun i => do
        let s ← skelAt (body i)
        return if fit s then some (mkApp3 (mkConst f) C (toExpr i) (toExpr s)) else none
    let rs ←
      if n == `sequentialToParallel then
        pure (atPos ``LineRw.mergeSpine ((List.range (k - 1)).reverse.map (· + 1)) ++
          ((List.range (k - 1)).drop 1).toArray.flatMap (fun i =>
            ((List.range (k - 1 - i)).reverse.map (· + 2)).toArray.map fun n =>
              mkApp3 (mkConst ``LineRw.mergeRun) C (toExpr i) (toExpr n)) ++
          atPos ``LineRw.mergeAt ((List.range (k - 1)).drop 1) ++
          (← do
            let s ← skelAt 0
            return if s.hasConn then #[1, 2, 3].map fun n =>
              mkApp3 (mkConst ``LineRw.mergeIn) C (toExpr n) (toExpr s) else #[]))
      else if n == `simplifyUpdate then
        pure (atPos ``LineRw.simplify (List.range k) ++ atPos ``LineRw.simplifyFresh (List.range k))
      else if n == `applySkip then pure (upd ``UpdRuleName.applySkip)
      else if n == `applyOnRigid then
        pure (upd ``UpdRuleName.applyOnRigid ++
          (← inSkel ``LineRw.applyOnRigidIn (List.range k) (· + 1) Skel.isConn))
      else if n == `applyOnRigidBox then
        pure (atPos ``LineRw.applyOnRigidBox (List.range k) ++
          (← inSkel ``LineRw.applyOnRigidBoxIn (List.range k) (· + 1) Skel.isConn))
      else if n == `applyStorageBox then pure (atPos ``LineRw.applyStorageBox (List.range k))
      else if n == `applyOnPV then
        inSkel ``LineRw.applyOnPV (List.range k) (· + 1) Skel.hasLit
      else if n == `concrete then inSkel ``LineRw.concrete (List.range (k + 1)) id Skel.hasLit
      else pure #[]
    return (rs, none)
  | .law c => do
    let (is, failed) ← lawInstances c φ
    let k ← spineLen φ
    let mut out := #[]
    for (t, t', pf) in is do
      unless keep t do continue
      out := out.push (mkAppN (mkConst ``LineRw.law) #[C, t, t', pf])
      if ← isDefEq (mkApp3 (mkConst ``Tm.total) C (mkConst ``Srt.val) t') (mkConst ``Bool.true) then
        let ht ← mkEqRefl (mkConst ``Bool.true)
        for i in List.range k do
          out := out.push (mkAppN (mkConst ``LineRw.lawUpdAny) #[C, t, t', pf, ht, toExpr i])
        for i in List.range k do
          out := out.push (mkAppN (mkConst ``LineRw.lawUpd) #[C, t, t', pf, ht, toExpr i])
      let refCtor? :=
        if c == ``TermTaclet.findOnSaveFrame then some ``TermTaclet.RefLaw.findOnSaveFrame
        else if c == ``TermTaclet.findOnDelAtValue then some ``TermTaclet.RefLaw.findOnDelAtValue
        else if c == ``TermTaclet.findOnDelAtFrame then some ``TermTaclet.RefLaw.findOnDelAtFrame
        else if c == ``TermTaclet.lenOnSaveFrame then some ``TermTaclet.RefLaw.lenOnSaveFrame
        else if c == ``TermTaclet.lenOnDelAtFrame then some ``TermTaclet.RefLaw.lenOnDelAtFrame
        else none
      if let some refCtor := refCtor? then
        let hr := mkAppN (mkConst refCtor) pf.getAppArgs
        discard <| inferType hr
        for i in List.range k do
          out := out.push (mkAppN (mkConst ``LineRw.lawUpdRef) #[C, t, t', pf, hr, toExpr i])
      for i in List.range k do
        out := out.push (mkAppN (mkConst ``LineRw.lawUpdEq) #[C, t, t', pf, toExpr i])
    return (out, failed)
  | .evalLaw c => do
    let (is, failed) ← lawInstances c φ
    let k ← spineLen φ
    let mut out := #[]
    for (t, t', pf) in is do
      unless keep t do continue
      let u := (← whnfR (← inferType t)).getAppArgs[1]!
      for i in List.range k do
        out := out.push (mkAppN (mkConst ``LineRw.lawUpdEval) #[C, u, t, t', pf, toExpr i])
    return (out, failed)
  | .litLaw c => do
    let (is, failed) ← lawInstances c φ
    let k ← spineLen φ
    let mut out := #[]
    for (t, t', pf) in is do
      unless keep t do continue
      for i in List.range k do
        out := out.push (mkAppN (mkConst ``LineRw.lit) #[C, t, t', pf, toExpr i])
      for n in List.range (k + 1) do
        let s := (← skelOf (← bodyBelow φ n)).1
        if s.hasLit then
          out := out.push (mkAppN (mkConst ``LineRw.litEq) #[C, t, t', pf, toExpr n, toExpr s])
    return (out, failed)

/-- `rwCandidatesWith` at every instance of a law. -/
def rwCandidates (C φ : Lean.Expr) (a : RwArrow) :
    TermElabM (Array Lean.Expr × Option MessageData) :=
  rwCandidatesWith (fun _ => true) C φ a

/-- Each of the rewrites `rs` on the line `φ`, computed: the line after, with
the line's modality and postconditions put back, or `none`.  Under a
modality `m` a rewrite runs at the diamond and at the box, and gives a line
only where the two agree but for `m`. -/
def rwResults (C φ : Lean.Expr) (rs : Array Lean.Expr) :
    MetaM (List (Option Lean.Expr) × Option (Lean.Expr × Bool)) := do
  let some n := (← whnfR C).constName?
    | throwError "sol_chain: the contract is not a named constant: {C}"
  let (φ', sp) ← (punch C φ).run {}
  let ty := mkApp (mkConst ``List [0]) (mkApp (mkConst ``Option [0]) (mkConst ``Lean.Expr))
  -- the rewrites' functions alone: a law closed by a hypothesis of the chain
  -- carries that variable in its proof, which a compiled evaluation cannot
  -- take, and the projection drops the proof
  let fs ← rs.mapM fun r => whnf (mkApp2 (mkConst ``LineRw.apply) C r)
  let fml := mkApp (mkConst ``Fml) C
  let list ← mkListLit (← mkArrow fml (mkApp (mkConst ``Option [0]) fml)) fs.toList
  let eval (φ : Lean.Expr) : MetaM (List (Option Lean.Expr)) :=
    unsafe evalExpr (List (Option Lean.Expr)) ty
      (mkApp4 (mkConst ``Fml.rwQuoted) C (quoteConstName n) φ list)
  let fill (m? : Option Lean.Expr) (d b : Lean.Expr) : Option Lean.Expr :=
    (fillSlots m? sp.fmls d b).toOption
  match ← modalityOf? φ' with
  | none =>
    let qs ← eval φ'
    return (if sp.fmls.isEmpty then qs else qs.map (·.bind fun q => fill none q q), none)
  | some m =>
    let ds ← eval (φ'.replaceFVar m (mkConst ``Modality.diamond))
    let bs ← eval (φ'.replaceFVar m (mkConst ``Modality.box))
    let parts := (ds.zip bs).any fun (d, b) => d.isSome != b.isSome
    let boxOnly := (ds.zip bs).all fun (d, b) => d.isNone || b.isSome
    return ((ds.zip bs).map fun
      | (some d, some b) => fill m d b
      | _ => none, if parts then some (m, boxOnly) else none)

/-- `r.apply A = some B` over a postcondition or a modality, where the kernel
cannot compute what the rewrite asks of them: `simp` takes the rewrite and the
line's fresh variables apart, `Post.freshVars_eq_nil` says the postcondition
has none, and `rfl` computes the rest (`LineRw.simplifyFresh`); a merge of two
updates that may halt compares the line's modalities (`Upd.merge`), which
`cases m` decides, one `rfl` per modality.  `none` if that does not close it. -/
def proveRw (C r A B : Lean.Expr) : TermElabM (Option Lean.Expr) := do
  let ty ← mkEq (mkApp2 (mkApp (mkConst ``LineRw.apply) C) r A)
    (mkApp2 (mkConst ``Option.some [0]) (mkApp (mkConst ``Fml) C) B)
  let simps ← `(tactic| simp only [LineRw.simplifyFresh, Fml.simplifyFreshAt, Fml.atSpine,
    Option.map_some, Fml.simplifyFreshTop, Fml.freshVars, Post.freshVars_eq_nil, List.append_nil,
    List.nil_append])
  -- the line's modality variable, if any: a merge of two updates that may
  -- halt compares modalities, which `cases m` decides
  let m? ← (collectFVars {} A).fvarIds.findM? fun f => do
    return (← whnfR (← f.getType)).isConstOf ``Modality
  let mut tacs := #[← `(tactic| ($simps:tactic; rfl))]
  if let some m := m? then
    let mId := mkIdent (← m.getUserName)
    tacs := tacs.push (← `(tactic| (cases $mId:ident <;> first | rfl | ($simps:tactic; rfl))))
  for tac in tacs do
    let s ← saveState
    let g ← mkFreshExprMVar ty
    let ok ← try
        pure (← Term.withoutErrToSorry <| Tactic.run g.mvarId!
          (Tactic.withoutRecover (evalTactic tac))).isEmpty
      catch _ => pure false
    if ok then
      let p ← instantiateMVars g
      unless p.hasSyntheticSorry || p.hasExprMVar do return some p
    s.restore
  return none

/-- The line's modality, when it is a variable. -/
def modalityVar? (A : Lean.Expr) : MetaM (Option Lean.Expr) := do
  let m? ← (collectFVars {} A).fvarIds.findM? fun f => do
    return (← whnfR (← f.getType)).isConstOf ``Modality
  return m?.map mkFVar

/-- How a rewrite link was proved: by `rfl`, or by `Modality.casesOn m`
with one `rfl` per modality. -/
inductive RwProofKind where
  | refl
  | cases

/-- The rewrite links this declaration's statement checked, by
`canonLink`: how each was proved.  The statement's elaborator (`rwLabel%`,
`link%`) checks a link to choose its label, and `sol_chain` proves it after:
the kernel computes the rewrite once there, not twice.  Local to the
environment branch, as `runCache` is; the kernel checks every link anyway. -/
initialize rwProofCache : EnvExtension (Std.HashMap Lean.Expr RwProofKind) ←
  registerEnvExtension (pure {}) (asyncMode := .local)

/-- The key of a link `r.apply A = some B` in `rwProofCache`: the link closed
over its free variables, their types and values included, in the order of the
context (`mkLambdaFVars`).  The proof's binders are other variables than the
statement's, of the same types, so they meet the same key; two contexts whose
variables differ in a type or a value meet different ones.  `none` if a
variable is not in the context. -/
def canonLink (r A B : Lean.Expr) : MetaM (Option Lean.Expr) := do
  let e := mkApp3 (mkConst `_chainLink) r A B
  let lctx ← getLCtx
  -- the free variables, with those their types and values mention
  let mut todo := (collectFVars {} e).fvarIds
  let mut seen : Std.HashSet FVarId := {}
  let mut decls : Array LocalDecl := #[]
  while !todo.isEmpty do
    let x := todo.back!
    todo := todo.pop
    if seen.contains x then continue
    seen := seen.insert x
    let some d := lctx.find? x | return none
    decls := decls.push d
    let st := collectFVars {} (← instantiateMVars d.type)
    let st := match d.value? with
      | some v => collectFVars st v
      | none => st
    todo := todo ++ st.fvarIds
  let xs := (decls.qsort (·.index < ·.index)).map (mkFVar ·.fvarId)
  return some (← mkLambdaFVars xs e (usedLetOnly := false))

/-- `r.apply A = some B` by `Modality.casesOn m`: one `Eq.refl` per
modality, each checked by the kernel first when `check` is set. -/
def rwCasesProof (C r A B m : Lean.Expr) (check : Bool) : MetaM (Option Lean.Expr) := do
  let fml := mkApp (mkConst ``Fml) C
  let ty := (← mkEq (mkApp2 (mkApp (mkConst ``LineRw.apply) C) r A)
    (mkApp2 (mkConst ``Option.some [0]) fml B)).abstract #[m]
  let pf (c : Lean.Name) : MetaM (Option Lean.Expr) := do
    let some (_, a, b) := (ty.instantiate1 (mkConst c)).eq? | return none
    if check then unless ← kernelDefEq a b do return none
    return some (mkApp2 (mkConst ``Eq.refl [1]) (mkApp (mkConst ``Option [0]) fml) b)
  let (some pd, some pb) := (← pf ``Modality.diamond, ← pf ``Modality.box) | return none
  let motive := Lean.mkLambda `m .default (mkConst ``Modality) ty
  return some (mkAppN (mkConst ``Modality.casesOn [levelZero]) #[motive, m, pd, pb])

/-- `r.apply A = some B` over a line with a modality `m` or postconditions
`φ : Post C`, decided by the kernel (`kernelDefEq`), never by the
elaborator's reduction.  A rewrite of the update spine looks at neither:
its `rfl` computes past them.  A merge of two updates that may halt
compares the line's modality with itself (`Upd.merge`), which a variable
does not decide: then `Modality.casesOn m`, one `rfl` per modality, each
checked by the kernel (`rwCasesProof`).  Else `proveRw`, for a rewrite that
asks the postcondition what it reads (`LineRw.simplifyFresh`).  A link the
statement already checked is not checked again (`rwProofCache`). -/
def rwProof (C r A B : Lean.Expr) : TermElabM (Option Lean.Expr) := do
  let key? ← canonLink r A B
  let m? ← modalityVar? A
  let cached := key?.bind ((rwProofCache.getState (← getEnv))[·]?)
  let record (k : RwProofKind) : MetaM Unit := do
    if let some key := key? then
      modifyEnv fun env => rwProofCache.modifyState env (·.insert key k)
  match cached, m? with
  | some .refl, _ => return some (someRefl C B)
  | some .cases, some m =>
    if let some p ← rwCasesProof C r A B m false then return some p
  | _, _ => pure ()
  let lhs := mkApp2 (mkApp (mkConst ``LineRw.apply) C) r A
  let rhs := mkApp2 (mkConst ``Option.some [0]) (mkApp (mkConst ``Fml) C) B
  if ← kernelDefEq lhs rhs then
    record .refl
    return some (someRefl C B)
  if let some m := m? then
    if let some p ← rwCasesProof C r A B m true then
      record .cases
      return some p
  proveRw C r A B

/-- The rewrite `~[n]~>` names on `φ`, among `rs`, the line after it, and its
proof when `rfl` is not one: the first that gives `ψ`, or, with `ψ` left
`_`, the first that applies.  On a line with a modality `m` or a
postcondition `φ : Post C`, the rewrite must compute over them, which the
kernel checks (`rwProof`), or be proved from `Post.noFresh` (`proveRw`):
`simplifyUpdate`, say, asks the postcondition which variables it reads,
and it is asked only which fresh ones. -/
def rwSelect (C φ ψ : Lean.Expr) (n : String) (rs : Array Lean.Expr)
    (failed : Option MessageData := none) :
    TermElabM (Lean.Expr × Lean.Expr × Option Lean.Expr) := do
  let φ ← instantiateMVars φ
  let ψ ← instantiateMVars ψ
  let (qs, parts) ← rwResults C φ rs
  let mut gives := #[]
  let mut stuck := false
  for (r, q?) in rs.toList.zip qs do
    let some q := q? | continue
    let st ← saveState
    unless ψ.isMVar || q == ψ || (← withReducible (isDefEq q ψ)) do
      st.restore
      gives := gives.push q
      continue
    let mut pf := none
    if φ.hasFVar then
      let some p ← rwProof C r φ q | stuck := true; st.restore; continue
      pf := some p
    return (r, q, pf)
  if stuck then
    throwError "~[{n}]~>: on{indentExpr φ}\nit looks at the line's modality or postcondition, \
      which are not known: state the line for a concrete one"
  if !gives.isEmpty then
    let ls := gives.toList.map fun q => m!"{indentExpr q}"
    throwError "~[{n}]~>: on{indentExpr φ}\nit gives{MessageData.joinSep ls ""}\nnot{indentExpr ψ}"
  let note := match failed, parts with
    | some m, _ => m!"\n({m})"
    | none, some (m, true) => m!"\n(it applies under the box only, where an update that halts \
        makes the line true: go on after `cases {m}`)"
    | none, some (m, false) => m!"\n(it applies under one modality only: go on after `cases {m}`)"
    | none, none => m!""
  throwError "~[{n}]~>: {n} does not apply to{indentExpr φ}{note}"

/-- The label of `φ ~[r]~> ψ` for a rewrite, `φ` known, the line after, and
its proof when `rfl` is not one. -/
def rwLabel (C φ ψ : Lean.Expr) (r : Ident) (a : RwArrow) :
    TermElabM (Lean.Expr × Lean.Expr × Option Lean.Expr) := do
  let (rs, failed) ← rwCandidates C (← instantiateMVars φ) a
  rwSelect C φ ψ r.getId.toString rs failed

/-- The term taclets `~=>` tries, after the update rules of `rwTable`: the
named rules of `TermTaclet`, and `findOnDelAtSave`. -/
def rwLaws : List Lean.Name :=
  [``TermTaclet.findOnSave, ``TermTaclet.findOnSaveFrame, ``TermTaclet.findMemberCons,
    ``TermTaclet.selectOnSaveMember, ``TermTaclet.selectOnSaveFrame, ``TermTaclet.selectOnDelAtMember,
    ``TermTaclet.selectOnDelAtFrame, ``TermTaclet.selectOnSaveMemberIn, ``TermTaclet.selectOnSaveFrameIn,
    ``TermTaclet.selectOnDelAtMemberIn, ``TermTaclet.selectOnDelAtFrameIn,
    ``TermTaclet.findOnDelAt, ``TermTaclet.findOnDelAtSave, ``TermTaclet.findOnDelAtValue,
    ``TermTaclet.delValueLit, ``TermTaclet.findOnDelAtBelow, ``TermTaclet.findOnDelAtFrame,
    ``TermTaclet.findOnPushFrame, ``TermTaclet.findOnPopFrame, ``TermTaclet.lenOnSaveFrame,
    ``TermTaclet.lenOnDelAtFrame]

/-- The laws of memory reads `~=>` tries, after the term taclets. -/
def rwEvalLaws : List Lean.Name :=
  [``EvalLaw.readOnWrite, ``EvalLaw.findCopyMem, ``EvalLaw.readCopySt, ``EvalLaw.readAddEqual,
    ``EvalLaw.readAddDifferent, ``EvalLaw.readAddDifferentIdentity, ``EvalLaw.readWriteDifferent,
    ``EvalLaw.readWriteDifferentIdentity, ``EvalLaw.readOnWriteIdentity]

/-- The literal laws `~=>` tries, after the laws of memory reads. -/
def rwLitLaws : List Lean.Name :=
  [``LitLaw.add_literals, ``LitLaw.sub_literals, ``LitLaw.div_literals, ``LitLaw.leq_literals,
    ``LitLaw.less_literals, ``LitLaw.greater_literals, ``LitLaw.geq_literals]

/-- What `~=>` tries, in order: the update rules, then the laws in scope. -/
def rwAnyArrows : MetaM (List (String × RwArrow)) := do
  let env ← getEnv
  let laws ← rwLaws.filterM fun c => if env.contains c then isLaw c else pure false
  let evalLaws := rwEvalLaws.filter env.contains
  let litLaws := rwLitLaws.filter env.contains
  return rwTable.map (fun n => (n.toString, .table n)) ++
    laws.map (fun c => ((lastName c).toString, .law c)) ++
    evalLaws.map (fun c => ((lastName c).toString, .evalLaw c)) ++
    litLaws.map fun c => ((lastName c).toString, .litLaw c)

/-- The rewrite of `φ ~=> ψ`: the first of `rwAnyArrows` that gives `ψ`, the
line after, and its proof when `rfl` is not one; else an error with what
each rewrite that applies gives. -/
def rwAnyFind (C φ ψ : Lean.Expr) : TermElabM (Lean.Expr × Lean.Expr × Option Lean.Expr) := do
  let mut gives : Array MessageData := #[]
  for (n, a) in ← rwAnyArrows do
    let (rs, failed) ← rwCandidates C φ a
    if rs.isEmpty then continue
    let st ← saveState
    try
      return ← rwSelect C φ ψ n rs failed
    catch _ =>
      st.restore
      let (qs, _) ← rwResults C φ rs
      if let some q := qs.findSome? id then gives := gives.push m!"{n} gives{indentExpr q}"
  let note := if gives.isEmpty then m!"\nno rewrite applies to it" else
    m!"\n{MessageData.joinSep gives.toList "\n"}"
  throwError "~=>: no rewrite gives{indentExpr ψ}\nfrom{indentExpr φ}{note}"

partial def solveChain (g : MVarId) : TermElabM Unit := do
  let ty ← instantiateMVars (← g.getType)
  if ty.isAppOfArity ``Fml.RwAny 3 then
    let #[C, φ, ψ] := ty.getAppArgs | unreachable!
    let φ ← instantiateMVars φ
    let ψ ← instantiateMVars ψ
    if φ.hasExprMVar then throwError "sol_chain: ~=>: the line before it is not known{indentExpr φ}"
    if ψ.isMVar then throwError "sol_chain: ~=>: write the line after, it is what picks the rewrite"
    let (r, q, pf) ← rwAnyFind C φ ψ
    unless ← isDefEq ψ q do throwError "sol_chain: ~=>: the line after is not{indentExpr q}"
    let lrw := mkApp (mkConst ``LineRw) C
    let motive ← withLocalDeclD `r lrw fun x => do
      mkLambdaFVars #[x] (← mkEq (mkApp2 (mkApp (mkConst ``LineRw.apply) C) x φ)
        (mkApp2 (mkConst ``Option.some [0]) (mkApp (mkConst ``Fml) C) ψ))
    g.assign (mkApp4 (mkConst ``Exists.intro [1]) lrw motive r (pf.getD (someRefl C q)))
  else if ty.isAppOfArity ``Fml.RwBy 5 then
    let #[C, n, r, φ, ψ] := ty.getAppArgs | unreachable!
    let .lit (.strVal n) := n | throwError "sol_chain: the arrow's name is not known{indentExpr ty}"
    let φ ← instantiateMVars φ
    if φ.hasExprMVar then throwError "sol_chain: ~[{n}]~>: the line before it is not known{indentExpr φ}"
    let r ← instantiateMVars r
    let ψ ← instantiateMVars ψ
    -- the label the statement chose, and the line after it: one check, by
    -- the kernel; the rewrites are run again only to say why it fails
    if !r.hasMVar && !ψ.hasMVar then
      if let some pf ← rwProof C r φ ψ then
        g.assign pf
        return
    let (r', q, pf) ← if r.isMVar then
        let some a ← rwArrow? (mkIdent n.toName) | throwError "sol_chain: {n} is a rule of the strategy"
        rwLabel C φ ψ (mkIdent n.toName) a
      else rwSelect C φ ψ n #[r]
    unless ← isDefEq r r' do throwError "sol_chain: ~[{n}]~>: the label is not {r'}"
    unless ← isDefEq ψ q do throwError "sol_chain: ~[{n}]~>: the line after is not{indentExpr q}"
    g.assign (pf.getD (someRefl C q))
  else
    -- a chain: split it into its links, unfolding `Fml.Via` and `Link.Rel`
    -- (reducible) and no further, down to the links' relations
    let ty' ← whnfR ty
    match_expr ty' with
    | And A B =>
      let a ← mkFreshExprMVar A
      let b ← mkFreshExprMVar B
      solveChain a.mvarId!
      solveChain b.mvarId!
      g.assign (mkApp4 (mkConst ``And.intro) A B a b)
    | True => g.assign (mkConst ``True.intro)
    | _ =>
      if ty' != ty then return ← solveChain (← g.replaceTargetDefEq ty')
      throwError "sol_chain: expected `φ ~[n]~> ψ` (a rewrite), `φ ~=> ψ` or a chain of them \
        (a step of the strategy is a scoped chain's){indentExpr ty}"

/-- `sol_chain`: prove `φ ~[n]~> ψ`, `φ ~=> ψ` or a chain of them by
running the rewrites; the kernel checks the lines it found. -/
elab "sol_chain" : tactic => withMainContext do
  solveChain (← getMainGoal)
  replaceMainGoal []

/-- `#derivation φ`: the derivation the strategy takes from `φ`, one line per
step with the rule that reached it; the scoped chains'
(`Calculus/Core/Chains.lean`). -/
syntax "#derivation " term : command

end Tactic

section Elab
open Lean Elab Term Meta

/-- `rwLabel% l φ r ψ`: `l`, once `φ` is known, the label of `φ ~[r]~> ψ`
for a rewrite, unless `sol_chain` found it first.  A line before that a
tactic still has to find (a `calc` step's `_` after `by sol_chain`) leaves the
label to the step's own `sol_chain`. -/
elab "rwLabel% " l:term:max a:term:max r:ident b:term:max : term => do
  let l ← elabTerm l none
  if (← instantiateMVars l).isMVar then
    let a' ← instantiateMVars (← elabTerm a none)
    if a'.hasExprMVar then
      tryPostpone
      return l
    let some arrow ← rwArrow? r | throwError "~[{r}]~>: not a rewrite"
    let ty ← whnfR (← inferType a')
    let_expr Fml C := ty | throwError "~[{r}]~>: not a formula{indentExpr a'}"
    let (lbl, _, _) ← rwLabel C a' (← elabTerm b none) r arrow
    unless ← isDefEq l lbl do throwError "~[{r}]~>: the rewrite on{indentExpr a'}\nis not {l}"
  return l

/-- The label of a rewrite arrow after the line `a`: computed when `a` is
known; otherwise left to the proof, `rwLabel%` filling it once `a` is known. -/
def rwLabelOf (C a b : Lean.Expr) (r : Ident) (arrow : RwArrow) : TermElabM Lean.Expr := do
  if !(← instantiateMVars a).hasExprMVar then return (← rwLabel C a b r arrow).1
  let lty := mkApp (mkConst ``LineRw) C
  let l ← mkFreshExprMVar lty
  discard <| elabTermEnsuringType (← `(rwLabel% $(← exprToSyntax l) $(← exprToSyntax a) $r
    $(← exprToSyntax b))) lty
  return l

/-- The contract of a line, `Fml C`. -/
def lineContract (a : Lean.Expr) (r : Ident) : TermElabM Lean.Expr := do
  let ty ← whnfR (← instantiateMVars (← inferType a))
  if let some C := ty.app1? ``Fml then return C
  let C ← mkFreshExprMVar (mkConst ``Contract)
  unless ← isDefEq ty (mkApp (mkConst ``Fml) C) do throwError "~[{r}]~>: not a formula{indentExpr a}"
  return C

elab_rules : term
  | `(stepBy% $a $r $b) => do
    let a ← elabTerm a none
    let C ← lineContract a r
    let b ← elabTermEnsuringType b (mkApp (mkConst ``Fml) C)
    let some arrow ← rwArrow? r
      | throwError "~[{r}]~>: a rule of the strategy is a scoped chain's step: write the line \
          before it scoped (`open scoped Solidity.Core.Surface`)"
    let l ← rwLabelOf C a b r arrow
    return mkAppN (mkConst ``Fml.RwBy) #[C, toExpr r.getId.toString, l, a, b]
  | `(link% $a $r $b) => do
    let some arrow ← rwArrow? r
      | throwError "~[{r}]~>: a rule of the strategy is a scoped chain's step: write the line \
          before it scoped (`open scoped Solidity.Core.Surface`)"
    let a ← elabTerm a none
    let C ← lineContract a r
    let b ← elabTermEnsuringType b (mkApp (mkConst ``Fml) C)
    let l ← rwLabelOf C a b r arrow
    return mkApp3 (mkConst ``Link.rw) C (toExpr r.getId.toString) l

/-- A chain of two links or more, every line written: each line elaborated
once, then each link's label from the lines on its two sides
(`rwLabelOf`).  Expanded (`expandChainStx`), a line would be elaborated in
every place it stands: in the list, after the link before it and before the
link after it, `dl!{ … }` read three times. -/
@[term_elab chainStx] def elabChain : TermElab := fun stx expectedType? => do
  unless chainWritten stx do throwUnsupportedSyntax
  let fallback : TermElabM Lean.Expr := do
    elabTerm (← liftMacroM (expandChainStx stx)) expectedType?
  let a ← elabTerm stx[0] none
  let ty ← whnfR (← instantiateMVars (← inferType a))
  let some C := ty.app1? ``Fml | fallback
  let fml := mkApp (mkConst ``Fml) C
  let mut raw := #[a]
  for l in stx[1].getArgs do
    raw := raw.push (← elabTermEnsuringType l[1] fml)
  synthesizeSyntheticMVarsNoPostponing
  let lines ← raw.mapM instantiateMVars
  if lines.any (·.hasExprMVar) then return ← fallback
  let pairTy := mkApp2 (mkConst ``Prod [0, 0]) (mkApp (mkConst ``Link) C) fml
  let mut ws := #[]
  for i in [0:stx[1].getArgs.size] do
    let l := stx[1].getArgs[i]!
    let (a, b) := (lines[i]!, lines[i + 1]!)
    let link ← withRef l[0] do match (⟨l[0]⟩ : TSyntax `chain_arrow) with
      | `(chain_arrow| ~=>) => pure (mkApp (mkConst ``Link.rwAny) C)
      | `(chain_arrow| ~[ $r:ident ]~>) =>
        match ← rwArrow? r with
        | none => throwError "~[{r}]~>: a rule of the strategy is a scoped chain's step: write \
            the first line scoped (`open scoped Solidity.Core.Surface`)"
        | some arrow =>
          return mkApp3 (mkConst ``Link.rw) C (toExpr r.getId.toString) (← rwLabelOf C a b r arrow)
      | _ => throwError "a step of the strategy (`~>`, `~*>`) is a scoped chain's: write the \
          first line scoped (`open scoped Solidity.Core.Surface`)"
    ws := ws.push (mkAppN (mkConst ``Prod.mk [0, 0]) #[mkApp (mkConst ``Link) C, fml, link, b])
  return mkApp3 (mkConst ``Fml.Via) C a (← mkListLit pairTy ws.toList)

end Elab
end Chain

end Solidity
