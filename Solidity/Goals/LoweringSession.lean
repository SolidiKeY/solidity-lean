import Solidity.Goals.LoweringDiagram
import Solidity.Correctness.IntrinsicSession.Spec
import Solidity.Correctness.Lowering.Sim.Session.Source

/-!
# The session-level lift of the lowering diagram (H556 option A, sg1)

`SessionLift D` is the conjunct `loweringBySimulation` (`Goals/LoweringSim.lean`)
adds for the diagram `D`: the lift of `D` from function bodies to the actual
Source session semantics (`Source.sourceLangEvents`) and the concrete intrinsic
session semantics (`Semantics.IntrinsicSession.spec F`, for every
`F : Roadmap.Fixed`). No goal here; the diagram vocabulary
(`Goals/LoweringDiagram.lean`) is used unchanged.

* **The compilation** (`Compilation`): the raw contract the Source program's
  functions are lowered in, and its deployment and entry stubs: a deployment
  is `constructor(args);`, an entry the call `f(args);` of one function, each
  elaborated by the production top-level elaborator (`topBlock`, the body of
  `elabProgS`, Syntax/Splice.lean). `Names` binds the raw functions to the
  Source program's resolved functions by name, both ways. Every function body
  an entry runs is therefore lowered and elaborated by the actual producer at a
  callee site (`inlinedBody`): the entries are built from the emitted programs.
* **(a) The lowered world** (`loweredWorld`): the session start whose code is
  that one contract with those entries (`loweredCode`), nothing deployed.
  **The accepted fragment** (`Compilation.Accepted`): every deployment and
  entry program is in t0's `ProgOk []`; a Source program is in the fragment
  (`InFragment`) when it has such a compilation.
* **(b) The program-to-body binding** (`BodiesBound`): every production run in the
  fragment at a callee site of a function of the compilation is associated by
  `D.Assoc` with the `Body` whose resolved statement is the actual resolved body
  of the Source function of that name (`Body.ofResolved`), with the run's own raw
  input, slots, scope, state and site. For those bodies the source of
  `Diagram.Total` is no longer existential.
* **(c) The environment map** (`envAbs`): both sides read session
  environments, so it is the identity; `envAbs_sound` and `envAbs_onto` are
  `lang_passCorrect`'s `envSound` and `envOnto` (Correctness/Sim/Lang.lean).
* **(d) The session refinement** (`Lift`): a `G49Final.PassCorrect` from the
  source program's behaviour to the lowered world's, whose environment map is
  `envAbs` and whose resource transport is `D.fuel`: the source horizon `n`
  needs the target bound of horizon `D.fuel n` without resource failure
  (`transport`). Its backward clause covers every guarded target prefix
  without resource failure; it is a field, not discharged by determinism.
* **(e) Storage and event agreement** (`Agrees`): at every boundary of the
  Source session (a reachable running state of `sourceMachine`, after `i`
  actions), the `i`th boundary world of the lowered run at the transported
  bound holds, at the deployed address, a storage `D.globRel` relates to the
  source state, and the source history is a prefix of the target's.

## Choices (stated, not hidden)

* **Two premises are read into the behaviours** (`sourceBehaviour`,
  `targetBehaviour`). Against `Behaviour.ofLang` read verbatim the refinement is
  false for every diagram: the source language's `Forward` is `True`, while
  `need_ok` asks the target `Forward`/`Guard` (fewer than `hashBound` distinct
  preimages, and the hash premise under `F.evm.keccak`, which a `Fixed` with a
  colliding `keccak` refutes); and the target admits bounds with resource
  failures, whose frames revert where the Source session (no resource model)
  succeeds. So the source's `Forward` is the target's readiness at the
  transported bound (`RefinesUnder`'s `FS`/`GS`), and the target's admissible
  bounds are those without resource failure. Observations, environments and
  every other field are `Behaviour.ofLang`'s.
* **No resolver links raw syntax to Source declarations** at the base, so the
  raw compilation is existential per Source program (bound by function names);
  its entry stubs (the calldata decoding as raw argument expressions, the
  return-data reader) are existential too, since no production ABI dispatcher
  over raw contracts exists. The bodies those entries run are the actual
  production runs `BodiesBound` constrains.
* Function bodies are bound by name within the main contract; overloads and
  inherited functions share a name and are not told apart.
-/

namespace Solidity.Goals.Shrink

namespace Lowering

open Solidity.Roadmap (Event Outcome SessionEnv Bytes)
open Solidity.Roadmap.G49Final (Behaviour PassCorrect)
open Solidity.Semantics.IntrinsicSession (Start spec runOf)
open Solidity.Goals.IntrinsicSession (Code)
open Solidity.Correctness.Lowering.Sim.Session (SourceState sourceMachine)

variable [FreshNames]

/-! ## The compilation -/

/-- The production top-level elaboration of a block from no locals: the body of
`elabProgS` (Syntax/Splice.lean), which this core module does not import. -/
def topBlock (C : Contract) (ss : List RawStmt) : Except String (Blk C []) := do
  let k := RawStmt.maxIdxs ss + 1
  let ss ← freshenBlocks (C.vars.map (·.1)) [] ss
  let P ← (elabStmtsP C ss).runFrom' { funs := C.funs } ([], k)
  SProg.chain [] [] P

/-- One entry: the function its calldata calls, the raw argument expressions
(the calldata decoding), the reader of its return data, and whether it is
payable. -/
structure Stub (C : Contract) where
  fn : String
  args : List RawExpr
  result : (Γ : Ctx) → State C Γ → TRes Bytes
  payable : Bool

/-- A raw compilation: the contract, the constructor arguments of a deployment,
and the entry each calldata selects. -/
structure Compilation where
  C : Contract
  ctorArgs : Bytes → Option (List RawExpr)
  entries : Bytes → Option (Stub C)

/-- A deployment's program, as `ctorProgS` builds it: nothing for a contract
with no constructor, no initializer and no arguments, else `constructor(args);`. -/
def Compilation.ctorProg (c : Compilation) (bytes : Bytes) : Option (Prog c.C [] []) :=
  (c.ctorArgs bytes).bind fun args =>
    if c.C.ctor.isNone && c.C.inits.isEmpty && args.isEmpty then some .nil
    else match topBlock c.C [.call (.name "constructor") args] with
      | .ok ⟨[], P⟩ => some P
      | _ => none

/-- An entry: the production elaboration of `f(args);`. -/
def Compilation.entry (c : Compilation) (bytes : Bytes) :
    Option (ContractWorld.Entry c.C Bytes) :=
  (c.entries bytes).bind fun s =>
    match topBlock c.C [.call (.name s.fn) s.args] with
    | .ok ⟨Γ, P⟩ => some ⟨Γ, P, s.result Γ, s.payable⟩
    | .error _ => none

/-- t0's accepted fragment on every deployment and entry program. -/
def Compilation.Accepted (c : Compilation) : Prop :=
  (∀ bytes P, c.ctorProg bytes = some P →
    Solidity.Backend.AbiWorld.PublicCompilerTotal.ProgOk [] P) ∧
  ∀ bytes en, c.entry bytes = some en →
    Solidity.Backend.AbiWorld.PublicCompilerTotal.ProgOk [] en.body

/-- A function of the Source program: a function declaration of its main
contract with a resolved body. -/
def SrcFun {E : Source.Env} (P : Source.SrcProg E) (d : Source.Decl) (rb : Source.RBody E) : Prop :=
  P.prog.body d = some rb ∧ d.kind = .function ∧ d.scope = some P.main

/-- The raw functions are the Source program's functions, by name, both ways. -/
def Compilation.Names {E : Source.Env} (c : Compilation) (P : Source.SrcProg E) : Prop :=
  (∀ d rb, SrcFun P d rb → ∃ fd, (d.name, fd) ∈ c.C.funs) ∧
  ∀ f fd, (f, fd) ∈ c.C.funs → ∃ d rb, SrcFun P d rb ∧ d.name = f

/-- A Source program of t0's accepted fragment: one with a compilation whose
programs are all in it. -/
def InFragment {E : Source.Env} (P : Source.SrcProg E) : Prop :=
  ∃ c : Compilation, c.Names P ∧ c.Accepted

/-! ## (a) The lowered world -/

/-- The code of a compilation: its one contract, deployed by `ctorProg`, entered
by `entry`. -/
def loweredCode (c : Compilation) : Code where
  contracts := [c.C]
  main := 0
  roles := fun _ => .contractCode
  ctor := fun k bytes => match k with
    | ⟨0, _⟩ => c.ctorProg bytes
  entry := fun k bytes => match k with
    | ⟨0, _⟩ => c.entry bytes

/-- **The lowered world**: the session start of the compilation's code, nothing
deployed. -/
def loweredWorld (c : Compilation) : Start := ⟨loweredCode c, .fresh⟩

/-! ## (b) The program-to-body binding -/

/-- The body whose resolved statement is the resolved function body `rb`, with
the given production input and site. -/
def Body.ofResolved {E : Source.Env} (rb : Source.RBody E) (raw : List RawStmt)
    (returnSlots : Option (List String)) (scope : ElabScope)
    (before : Solidity.Correctness.Lowering.Checker.Snapshot) (site : Site) : Body where
  E := E
  returns := rb.rs
  modifier := rb.inModifier
  control := .body
  ctx := rb.locals
  input := ⟨raw, .block rb.items, returnSlots, scope, before⟩
  site := site

/-- The site inlines (or frames) the raw function `f` of `C`. -/
def Site.Calls (C : Contract) (f : String) : Site → Prop
  | .loop => False
  | .callee fd _ _ _ _ _ _ | .recursive fd _ _ _ _ _ _ _ _ => (f, fd) ∈ C.funs

/-- **The binding**: every production run in the fragment at a site of a
function of the compilation is associated by `D` with the actual resolved body
of the Source function of that name. -/
def BodiesBound (D : Diagram) {E : Source.Env} (P : Source.SrcProg E) (c : Compilation) : Prop :=
  ∀ d rb, SrcFun P d rb →
    ∀ raw returnSlots scope before site (u : Emitted), u.C = c.C → site.Calls c.C d.name →
      Production (Body.ofResolved rb raw returnSlots scope before site) u → Accepted u →
        ∃ m, D.Assoc (Body.ofResolved rb raw returnSlots scope before site) u m

/-! ## (c) The environment map -/

/-- **The environment map**: target and source both read session environments. -/
def envAbs : SessionEnv → SessionEnv := id

omit [FreshNames] in
theorem envAbs_sound (F : Roadmap.Fixed) {E : Source.Env} (e : SessionEnv) :
    (spec F).lang.Allowed e → (Source.sourceLangEvents E).Allowed (envAbs e) := id

omit [FreshNames] in
theorem envAbs_onto (F : Roadmap.Fixed) {E : Source.Env} (e : SessionEnv) :
    (Source.sourceLangEvents E).Allowed e → ∃ e', (spec F).lang.Allowed e' ∧ envAbs e' = e :=
  fun h => ⟨e, h, rfl⟩

/-! ## (d) The session refinement -/

/-- **The resource transport**: the source horizon `n` needs the target bound of
horizon `D.fuel n`, without resource failure. -/
def transport (D : Diagram) (n : Nat) : Semantics.IntrinsicSession.Bound := { horizon := D.fuel n }

/-- The lowered world's behaviour: `Behaviour.ofLang` of the session spec, at
bounds without resource failure. -/
noncomputable def targetBehaviour (F : Roadmap.Fixed) (x : Start) : Behaviour :=
  { Behaviour.ofLang (spec F).lang ((spec F).ofWorld x) with
    Admissible := Semantics.IntrinsicSession.Bound.NoFail }

/-- The source program's behaviour: `Behaviour.ofLang` of the Source session,
read at horizons whose transported target bound is ready (no resource failure,
fewer than `hashBound` preimages, the hash premise). -/
noncomputable def sourceBehaviour (D : Diagram) (F : Roadmap.Fixed) {E : Source.Env}
    (P : Source.SrcProg E) (x : Start) : Behaviour :=
  { Behaviour.ofLang (Source.sourceLangEvents E) P with
    Forward := fun e n => (Behaviour.ofLang (spec F).lang ((spec F).ofWorld x)).Ready e (transport D n) }

/-! ## (e) Storage and event agreement -/

/-- The frame state of a boundary instance: its storage, nothing else. -/
def boundaryState {K : Type} {contracts : K → Contract} (a : ContractWorld.Account contracts) :
    State (contracts a.1) [] :=
  { State.init (contracts a.1) with storage := a.2 }

/-- **Agreement at every boundary**: after `i` actions of the Source session at
horizon `n`, whose transported target bound is ready, the `i`th boundary world of
the lowered run holds at the deployed address a storage `D.globRel` relates to
the source state, and the source history is a prefix of the target's. -/
def Agrees (D : Diagram) (F : Roadmap.Fixed) {E : Source.Env} (P : Source.SrcProg E)
    (x : Start) : Prop :=
  ∀ (e : SessionEnv) (n k i : Nat) (s : Source.St E) (last : Outcome), e.Allowed →
    (Behaviour.ofLang (spec F).lang ((spec F).ofWorld x)).Ready e (transport D n) →
    (sourceMachine P e).Reachable (SourceState.run n k i s last) →
      s.events <+: ((spec F).lang.sem x e (transport D n)).events ∧
      ∀ w, (runOf F x e (transport D n)).worlds[i]? = some w →
        ∀ a, w.accounts (Solidity.Lowering.V08.EnvironmentProjection.liftAddress
          (P.fixed.createAddress e.deployer e.deployNonce)) = some a →
          D.globRel s (boundaryState a)

/-- **The lift of `D` for one Source program and its compilation**: a session
refinement with environment map `envAbs` and resource transport `D.fuel`, and
agreement at every boundary. -/
def Lift (D : Diagram) (F : Roadmap.Fixed) {E : Source.Env} (P : Source.SrcProg E)
    (c : Compilation) : Prop :=
  (∃ pc : PassCorrect (sourceBehaviour D F P (loweredWorld c)) (targetBehaviour F (loweredWorld c)),
    pc.envAbs = envAbs ∧ ∀ e n, pc.need e n = transport D n) ∧
  Agrees D F P (loweredWorld c)

/-- **The session-level lift of the diagram**: for every fixed parameter set and
every Source program of t0's accepted fragment, a compilation in the fragment
whose function bodies are bound to the program's resolved bodies, and whose
lowered world refines the program's session. -/
def SessionLift (D : Diagram) : Prop :=
  ∀ (F : Roadmap.Fixed) (E : Source.Env) (P : Source.SrcProg E), InFragment P →
    ∃ c : Compilation, c.Names P ∧ c.Accepted ∧ BodiesBound D P c ∧ Lift D F P c

end Lowering

end Solidity.Goals.Shrink
