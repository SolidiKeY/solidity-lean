import Solidity.Goals.Loops
import Solidity.Correctness.Lowering.Total.Versions

namespace Solidity.Goals

/--
info: unstated Solidity.Goals.lowerLoopsCorrect ← Solidity.Correctness.Lowering.lowerLoops_correct plan e1-loops
-/
#guard_msgs in
#roadmap_goal lowerLoopsCorrect

/--
info: open Solidity.Goals.loweringStudyTarget ← Solidity.Correctness.Lowering.lowerLoops_correct blocked by [Solidity.Goals.lowerLoopsCorrect] plan pa-lowering
-/
#guard_msgs in
#roadmap_goal loweringStudyTarget

/-- The local production contract is exactly the dedicated roadmap goal. -/
example :
    (∀ [FreshNames],
      LowerKernel.Fix lowerList lowerStmt lowerLoop ∧
      (∃ (μL : List RawStmt → Nat) (μS μP : RawStmt → Nat),
        LowerKernel.Contractive μL μS μP) ∧
      LowerKernel.Helpers) = Solidity.Goals.loweringKernelTotal := rfl

example : Solidity.Goals.loweringKernelTotal := Solidity.lowerKernel_total

/--
info: proved Solidity.Goals.loweringKernelTotal ← Solidity.lowerKernel_total plan e2a-lower-total
-/
#guard_msgs in
#roadmap_goal loweringKernelTotal

/-! ### The loop contract (e2b-loops-producer)

`lowerLoopsCorrect` stays unstated: the concrete boundary is not complete. These pin
what is proved about the contract at every boundary. -/

section Contract

open Solidity.Correctness.Lowering Solidity.Correctness.Lowering.Total

/-- The production and family conjuncts are discharged at every boundary. -/
example (b : SemanticBoundary) (i : RawSourceInterpretation)
    (decode : Request → Option SourceProgram) :
    LowerLoopsCorrectContract b i decode ↔ Faithful b i ∧ Residual b decode :=
  contract_iff b i decode

example (b : SemanticBoundary) (decode : Request → Option SourceProgram) :
    LowerLoopsCorrectContract b b.reference decode ↔ Residual b decode :=
  contract_reference_iff b decode

/-- Negative control: the contract alone admits an empty boundary. -/
example (b : SemanticBoundary) (decode : Request → Option SourceProgram)
    (empty : ∀ r, ¬ b.reference.entry r) (normal : RelatesNormalFamily b)
    (returns : RelatesReturnFamily b) : LowerLoopsCorrectContract b b.reference decode :=
  (contract_reference_iff b decode).mpr (Residual.of_empty b decode empty normal returns)

/-- With `FullDomain`, a successful top-level pipeline is in `LowersTo` and has
its decoded, associated, related and refined Source program. -/
example (b : SemanticBoundary) (decode : Request → Option SourceProgram)
    (h : LowerLoopsCorrectContract b b.reference decode) (full : FullDomain b)
    (C : Contract) (input : ProductionInput) (o : ProductionOutput) (after : Checker.Snapshot)
    (parts : SProg C) (program : Blk C input.caller.ctx)
    (run : SuccessfulLoopPipeline input o C after parts program) :
    @LowersTo input.names input.returnSlots input.raw o.raw input.scope input.before o.after ∧
    ∃ s, decode ⟨C, input, none⟩ = some s ∧ b.relates s program :=
  have p := production_correct ((contract_reference_iff b decode).mp h) full ⟨C, input, none⟩ o
    after parts program run
  ⟨p.1 rfl, p.2.2.elim fun s q => ⟨s, q.1, q.2.2.1⟩⟩

/-- An admitted request has at most one associated Source program. -/
example (b : SemanticBoundary) (decode : Request → Option SourceProgram)
    (h : Residual b decode) (r : Request) (s s' : SourceProgram) (e : b.reference.entry r)
    (a : b.reference.associated r s) (a' : b.reference.associated r s') : s = s' :=
  h.associated_unique e a a'

end Contract

/-! ### The decoder on the e1 sample

The decoder alone, from the raw input of the actual `while (i = a) break;`
probe as a top-level request, yields the Source statement the e1 endpoint is
proved against, at the decoder's canonical environment. The right-hand sides
are e1's hand-written typing derivations. Only Boolean locals, empty loop
specifications and the empty contract are exercised. -/

section Decoder

open Solidity.Correctness.Lowering Solidity.Correctness.Lowering.Total
open Solidity.Correctness.Lowering.Checker

/-- The decoder reads neither the fresh-name scheme nor the counter. -/
def sampleNames : FreshNames := ⟨fun s n => s ++ toString n, fun _ => none⟩

def sampleRequest (raw : List RawStmt) : Request :=
  ⟨IntrinsicProbe.C, ⟨sampleNames, none, raw, RawProbe.scope, ⟨(RawProbe.inputLocals, 1), {}⟩⟩,
    none⟩

/-- The canonical unit of the sample contract: one empty contract. -/
def sampleEnv : Source.Env :=
  (Source.Syn.unit (.cons (.contract false Decode.contractName .none .nil .nil) .nil)).env

example : Decode.decode (sampleRequest RawProbe.input) =
    some (SourceProgram.ofStmt (SourceAssociation.resolved sampleEnv)) := rfl

/-- The same for the other e1 samples: each raw input decodes to the resolved
Source statement of its hand-written typing derivation. -/
example : Decode.decode (sampleRequest Loops.Capture.forBreakInput) =
    some (SourceProgram.ofStmt (Loops.Coverage.forBreakTyping sampleEnv).toR) := rfl
example : Decode.decode (sampleRequest Loops.Capture.forBreakUpdateInput) =
    some (SourceProgram.ofStmt (Loops.Coverage.forBreakUpdateTyping sampleEnv).toR) := rfl
example : Decode.decode (sampleRequest Loops.Capture.whileContinueInput) =
    some (SourceProgram.ofStmt (Loops.Coverage.whileContinueTyping sampleEnv).toR) := rfl
example : Decode.decode (sampleRequest Loops.Capture.doBreakInput) =
    some (SourceProgram.ofStmt (Loops.Coverage.doBreakTyping sampleEnv).toR) := rfl
example : Decode.decode (sampleRequest Loops.Capture.whileResetInput) =
    some (SourceProgram.ofStmt (Loops.Coverage.whileResetTyping sampleEnv).toR) := rfl
example : Decode.decode (sampleRequest Loops.Capture.doContinueInput) =
    some (SourceProgram.ofStmt (Loops.Coverage.doContinueTyping sampleEnv).toR) := rfl
example : Decode.decode (sampleRequest Loops.Capture.whileReturnBody) =
    some (SourceProgram.ofStmt (Loops.Coverage.whileReturnTyping sampleEnv).toR) := rfl
example : Decode.decode (sampleRequest Loops.Capture.doReturnBody) =
    some (SourceProgram.ofStmt (Loops.Coverage.doReturnTyping sampleEnv).toR) := rfl
example : Decode.decode (sampleRequest Loops.Capture.returnFlagBody) =
    some (SourceProgram.ofStmt (Loops.Coverage.returnFlagTyping sampleEnv).toR) := rfl

/-- Negative controls: an unbound name is refused by Source typing; `break`
outside a loop and a statement outside the covered syntax have no spelling. -/
example : Decode.decode (sampleRequest [.assign (.name "i") (.name "z")]) = none := rfl
example : Decode.decode (sampleRequest [.brk]) = none := rfl
example : Decode.decode (sampleRequest [.eval []]) = none := rfl

/-- A primitive state variable resolves in the canonical unit; a narrow one
is a gap. -/
example : (Decode.decode { sampleRequest [.assign (.name "s") (.name "a")] with
    contract := { vars := [("s", .prim .bool)] } }).isSome = true := rfl
example : Decode.decode { sampleRequest [.assign (.name "s") (.num 1)] with
    contract := { vars := [("s", .prim .uint)], widths := [("s", 8)] } } = none := rfl

/-- Spellings no e1 sample exercises, over `uint x`, `int y`, `bool a`: each is
typed by Source inference (that it means what the model gives it is open). -/
def wordRequest (raw : List RawStmt) : Request :=
  ⟨IntrinsicProbe.C, ⟨sampleNames, none, raw, RawProbe.scope,
    ⟨([("x", .val .uint), ("y", .val .int), ("a", .val .bool)], 1), {}⟩⟩, none⟩

example : (Decode.decode (wordRequest
    [.unchecked [.opAssign .add (.name "x") (.num 1)], .incDec .postInc (.name "x")])).isSome =
    true := rfl
example : (Decode.decode (wordRequest
    [.forLoop {} [.decl (.named "uint") "k" (some (.num 0))] (some (.binop .lt (.name "k") (.name "x")))
      [.incDec .preInc (.name "k")] [.ite (.name "a") [.cont] [.brk]]])).isSome = true := rfl
example : (Decode.decode (wordRequest
    [.assign (.name "y") (.unop .toInt (.name "x")),
     .assign (.name "x") (.modular .addmod (.name "x") (.num 2) (.num 3)),
     .assign (.name "x") (.binop .shr (.name "x") (.num 1)),
     .assign (.name "x") (.ternary (.name "a") (.env .msgValue) (.env .timestamp))])).isSome =
    true := rfl
example : (Decode.decode (wordRequest
    [.loop {} (.name "a") [.assign (.name "a") (.bool false)], .require (.name "a"),
     .assert (.unop .not (.name "a")), .revert])).isSome = true := rfl
/-- Further gaps: a wrapping operator, a cast written as a call, nested
`unchecked`, a narrow local. -/
example : Decode.decode (wordRequest [.assign (.name "x") (.binop .addW (.name "x") (.num 1))]) =
    none := rfl
example : Decode.decode (wordRequest [.assign (.name "x") (.call "uint" [.name "y"])]) = none := rfl
example : Decode.decode (wordRequest [.unchecked [.unchecked []]]) = none := rfl
example : Decode.decode { wordRequest [] with
    input := { (wordRequest []).input with before := ⟨([("n", .val .uint 8)], 1), {}⟩ } } =
    none := rfl

/-- The decoder reads only plain requests: a callee body, return slots or an
`unchecked` scope is a gap, not a guess. -/
example : Decode.decode { sampleRequest RawProbe.input with
    callee := some ⟨{ params := [], body := RawProbe.input }, [], false, false, [], [], 0⟩ } =
    none := rfl
example : Decode.decode { sampleRequest RawProbe.input with
    input := { (sampleRequest RawProbe.input).input with returnSlots := some [] } } = none := rfl
example : Decode.decode { sampleRequest RawProbe.input with
    input := { (sampleRequest RawProbe.input).input with
      scope := { RawProbe.scope with unchecked := true } } } = none := rfl

/-- The concrete admission is every request whose whole pipeline succeeds, and
at it the contract is the six listed obligations. -/
example {source target relates allocations} :
    FullDomain (loopBoundary source target relates allocations) := loopBoundary_fullDomain

example {source target relates allocations} :
    LowerLoopsCorrectContract (loopBoundary source target relates allocations)
        (loopReference source target) Decode.decode ↔
      (∀ r : Request, r.Succeeds → ∃ s, Decode.decode r = some s) ∧
      (∀ (r : Request) s, r.Succeeds → Spells r s → Decode.decode r = some s) ∧
      (∀ (r : Request) o after parts program, r.pipeline o after parts program →
        ∃ scopes, allocations r o after parts program scopes ∧
          ∀ scope ∈ scopes, SafeSpellings r.input.names scope.protectedNames scope.generated) ∧
      (∀ (r : Request) o after parts program s, Decode.decode r = some s →
        r.pipeline o after parts program →
        relates s program ∧ Nonempty (Solidity.Roadmap.G49Final.PassCorrect
          (source s).behaviour (target program).behaviour)) ∧
      RelatesNormalFamily (loopBoundary source target relates allocations) ∧
      RelatesReturnFamily (loopBoundary source target relates allocations) :=
  (contract_reference_iff _ _).trans loopResidual_iff

/-- With the policies (H1021), the simulation (H1022) and the allocation
trace (H1023) fixed, and for a state relation that reflects Booleans and
relates `false` to `false`, the contract is four obligations; the two e1
family obligations follow from those hypotheses. No such relation is defined. -/
example {rel : (E : Source.Env) → (C : Contract) → Simulation.StateRelation E C}
    (reflect : ∀ E C H (v : Source.Val E.layout .bool) (b : Bool),
      (rel E C).val H .bool (.val .bool) v b → v = .bool b)
    (falseRel : ∀ E C H, (rel E C).val H .bool (.val .bool) (.bool false) false) :
    LowerLoopsCorrectContract (loopBoundaryAt rel) (loopBoundaryAt rel).reference Decode.decode ↔
      (∀ r : Request, r.Succeeds → ∃ s, Decode.decode r = some s) ∧
      (∀ (r : Request) s, r.Succeeds → Spells r s → Decode.decode r = some s) ∧
      (∀ (r : Request) o after parts program, r.pipeline o after parts program →
        Allocation.RoundTrip r.input.names ∧
        SafeSpellings r.input.names (Allocation.scope r o after).protectedNames
          (Allocation.scope r o after).generated) ∧
      (∀ (r : Request) o after parts program s, Decode.decode r = some s →
        r.pipeline o after parts program →
        Simulation.Simulates rel s program ∧
          Nonempty (Solidity.Roadmap.G49Final.PassCorrect (Observe.source s).behaviour
            (Observe.target program).behaviour)) :=
  (contract_reference_iff _ _).trans (loopResidualAt_iff reflect falseRel)

/-- The first-completion observation keeps an outcome once seen, and sees
nothing before it. -/
example : Observe.first (fun n => if n = 2 then some (.success []) else none) 1 = none := rfl
example : Observe.first (fun n => if n = 2 then some (.success []) else none) 5 =
    some (.success []) := rfl

/-- The generated identifiers are those in the counter interval only. -/
example : Allocation.generated ⟨fun s n => s ++ toString n,
      fun s => if s = "brk1" then some ("brk", 1) else if s = "se7" then some ("se", 7) else none⟩
    1 3 ["i", "brk1", "se7"] = [("brk", 1)] := by decide

/-- The decoder against the independent spelling relation (H1024): sound
outright, complete if Source inference is, and a request spells one program. -/
example {r : Request} {s : SourceProgram} (h : Decode.decode r = some s) : Spells r s :=
  decode_spells h
example (complete : InferComplete) {r : Request} {s : SourceProgram} :
    Decode.decode r = some s ↔ Spells r s :=
  ⟨decode_spells, Spells.decode complete⟩
example {r : Request} {s s' : SourceProgram} (h : Spells r s) (h' : Spells r s') : s = s' :=
  h.unique h'
/-- The relation is not the decoder's graph by definition: a spelling is
built here by its rules. -/
example : Spells.Items .body RawProbe.input
    (.cons (.stmtItem (.whileStmt (.assign .assign (.ident "i") (.ident "a")) .breakStmt)) .nil) :=
  .stmt (.whileLoop {} (.assign (.name "i") (.name "a")) (.stmt .brk .nil)) .nil

/-- Negative control: with globals never related, any pair with context maps
simulates. The simulation conjunct needs a non-degenerate state relation. -/
example {rel : (E : Source.Env) → (C : Contract) → Simulation.StateRelation E C}
    (empty : ∀ E C G F st σ, ¬ (rel E C).glob G F st σ) {s : SourceProgram} {C : Contract} {Γ : Ctx}
    (p : Blk C Γ) (m : Solidity.Lowering.V07.ContextMap s.before Γ)
    (m' : Solidity.Lowering.V07.ContextMap s.after p.1) (emb : Thin Γ p.1) :
    Simulation.Simulates rel s p :=
  Simulation.vacuous empty p m m' emb

/-- The stage-1 boundary is a closed term; at it the contract is four
obligations with no hypothesis left on the state relation. -/
example :
    LowerLoopsCorrectContract loopBoundaryStage1 loopBoundaryStage1.reference Decode.decode ↔
      (∀ r : Request, r.Succeeds → ∃ s, Decode.decode r = some s) ∧
      (∀ (r : Request) s, r.Succeeds → Spells r s → Decode.decode r = some s) ∧
      (∀ (r : Request) o after parts program, r.pipeline o after parts program →
        Allocation.RoundTrip r.input.names ∧
        SafeSpellings r.input.names (Allocation.scope r o after).protectedNames
          (Allocation.scope r o after).generated) ∧
      (∀ (r : Request) o after parts program s, Decode.decode r = some s →
        r.pipeline o after parts program →
        Simulation.Simulates loopRel s program ∧
          Nonempty (Solidity.Roadmap.G49Final.PassCorrect (Observe.source s).behaviour
            (Observe.target program).behaviour)) :=
  (contract_reference_iff _ _).trans loopResidualStage1_iff

/-- The stage-1 value relation: a model `uint` and the Source `uint256` of the
same number are related; a `uint` and a `bool` are not. -/
example (E : Source.Env) (C : Contract) (H : HTy) (x : PrimTy.uint.Denote) :
    ∃ v, (loopRel E C).val H (.int Source.IntTy.u256) (.val .uint) v x :=
  Relation.val_total E C H .uint x
example (E : Source.Env) (C : Contract) (H : HTy) (v : Source.Val E.layout .bool)
    (x : PrimTy.uint.Denote) : ¬ (loopRel E C).val H .bool (.val .uint) v x :=
  fun ⟨h, _⟩ => nomatch h

/-- H1033: the Source policy allows exactly the admitted executions, and an
execution with a failure plan is not one. -/
example (s : SourceProgram) (e : SourceExecution s) :
    (Observe.source s).allowed e ↔
      e.plan = none ∧ e.calldataKnown = true ∧ e.frame.static = false ∧ e.frame.checked = true :=
  Iff.rfl
example (s : SourceProgram) (e : SourceExecution s) (points : e.plan.isSome = true) :
    ¬ (Observe.source s).allowed e :=
  fun admitted => by rw [admitted.1] at points; cases points

/-- H1036: the round-trip law is part of the allocation obligation; a scheme
that never reads a name back does not satisfy it. -/
example : ¬ Allocation.RoundTrip ⟨fun s n => s ++ toString n, fun _ => none⟩ :=
  fun law => nomatch law "se" (by decide) 0
/-! The default scheme reads back the allocated bases (sampled, not proved for
every index; evaluated, not kernel-checked). -/
#guard Allocation.bases.all fun base => [0, 1, 7, 42].all fun k =>
  (FreshNames.ofPrefixes "se" "sp" "ie" "mv").parse
    ((FreshNames.ofPrefixes "se" "sp" "ie" "mv").name base k) == some (base, k)
/-- There is at most one positional map. -/
example {srcΓ : Source.RCtx} {Γ : Ctx} {m n : Solidity.Lowering.V07.ContextMap srcΓ Γ}
    (hm : Simulation.Positional m) (hn : Simulation.Positional n) : m = n := hm.unique hn

/-- H1035: the bound simulation gives the `relates` half of the pipeline
obligation; it is an obligation beside the contract, not part of it. -/
example {decode : Request → Option SourceProgram} (h : Simulation.Bound loopRel decode)
    {r : Request} {o after parts} {program : Blk r.contract r.context.ctx} {s : SourceProgram}
    (d : decode r = some s) (run : r.pipeline o after parts program) :
    Simulation.Simulates loopRel s program :=
  h.simulates d run

/-- Version 2 of the contract (H1035, additive): version 1 is a conjunct, and
at the stage-1 boundary it is six obligations. -/
example {rel b i decode} (h : LowerLoopsCorrectContractV2 rel b i decode) :
    LowerLoopsCorrectContract b i decode := h.v1
example :
    LowerLoopsCorrectContractV2 loopRel loopBoundaryStage1 loopBoundaryStage1.reference
        Decode.decode →
      Simulation.InitialMatching loopRel Decode.decode ∧ Simulation.Bound loopRel Decode.decode :=
  fun h => (loopContractV2Stage1_iff.mp h).2.2.2.2

/-- The locals half of total initial matching is a theorem: a decoded request
has a positional map under which every Source locals has related model locals. -/
example {r : Request} {s : SourceProgram} (h : Decode.decode r = some s) :
    ∃ m : Solidity.Lowering.V07.ContextMap s.before r.context.ctx, Simulation.Positional m ∧
      ∀ (H : HTy) (ls : Source.Locals s.env.layout s.before),
        ∃ env : TEnv r.contract H r.context.ctx,
          m.Related ((loopRel s.env r.contract).val H) ls env :=
  Simulation.decode_locals_matching h

/-- Positive control for the globals half, on one contract with a state
variable of each primitive type: the Source cell at each variable's path in
the canonical unit has the type the state relation asks for. The general
statement is `Decode.unit_cellTy`, pinned after these. -/
def cellContract : Contract :=
  { vars := [("s", .prim .bool), ("n", .prim .uint), ("k", .prim .int)] }
def cellEnv : Source.Env := ((Decode.unit cellContract).map (·.env)).getD ⟨[]⟩
example : (Decode.unit cellContract).isSome = true := rfl
example : cellEnv.cellTy ⟨⟨some Decode.contractName, "s"⟩, []⟩ =
    Source.Agreement.sourceTy .bool := rfl
example : cellEnv.cellTy ⟨⟨some Decode.contractName, "n"⟩, []⟩ =
    Source.Agreement.sourceTy .uint := rfl
example : cellEnv.cellTy ⟨⟨some Decode.contractName, "k"⟩, []⟩ =
    Source.Agreement.sourceTy .int := rfl

/-- The general cell-type equation: in the canonical unit, the cell of the
state variable the model reads under a name has that primitive's Source type. -/
example {C : Contract} {u : Source.Syn .unit} (h : Decode.unit C = some u) {x : Name}
    {p : PrimTy} (hx : Semantics.lookupBy x C.vars = some (.prim p)) :
    u.env.cellTy ⟨⟨some Decode.contractName, x⟩, []⟩ = Source.Agreement.sourceTy p :=
  Decode.unit_cellTy h hx

/-- Total initial matching is a theorem for the stage-1 relation: the state
relation is not degenerate on decoded requests. -/
example : Simulation.InitialMatching loopRel Decode.decode := Simulation.initialMatching_loopRel

/-! ### The width-aware decoder version (H1258, additive)

`Decode.tablesW.decode` reads primitives at their declared widths; the landed
decoder is unchanged. -/

/-- Over `uint8 n; uint16 k`: widening `k = n` types, narrowing `n = k` does
not; `n = 255` fits and `n = 256` does not. So the widths are read. -/
def narrowRequest (raw : List RawStmt) : Request :=
  ⟨IntrinsicProbe.C, ⟨sampleNames, none, raw, RawProbe.scope,
    ⟨([("n", .val .uint 8), ("k", .val .uint 16)], 1), {}⟩⟩, none⟩
example : (Decode.tablesW.decode (narrowRequest [.assign (.name "k") (.name "n")])).isSome =
    true := rfl
example : Decode.tablesW.decode (narrowRequest [.assign (.name "n") (.name "k")]) = none := rfl
example : (Decode.tablesW.decode (narrowRequest [.assign (.name "n") (.num 255)])).isSome =
    true := rfl
example : Decode.tablesW.decode (narrowRequest [.assign (.name "n") (.num 256)]) = none := rfl
/-- The landed decoder has no type for a narrow local. -/
example : Decode.decode (narrowRequest [.assign (.name "k") (.name "n")]) = none := rfl
/-- A narrow state variable is read at its row; a marker row, a variable named
like one, and a local marked as an erased `address` are gaps. -/
example : (Decode.tablesW.decode { sampleRequest [.assign (.name "s") (.num 255)] with
    contract := { vars := [("s", .prim .uint)], widths := [("s", 8)] } }).isSome = true := rfl
example : Decode.tablesW.decode { sampleRequest [.assign (.name "s") (.num 256)] with
    contract := { vars := [("s", .prim .uint)], widths := [("s", 8)] } } = none := rfl
example : Decode.tablesW.decode { sampleRequest [] with
    contract := { vars := [("s", .prim .uint)], widths := [("s#address", 20)] } } = none := rfl
example : Decode.tablesW.decode { sampleRequest [] with
    contract := { vars := [("x", .prim .uint), ("x#bytes", .prim .uint)] } } = none := rfl
/-- A `bytes1` state variable (`x ↦ 8` and the marker `x#bytes ↦ 1`) is a gap,
not a `uint8`; so is a `bool` with a width row. A row that names no state
variable is not read. -/
example : Decode.tablesW.decode { sampleRequest [] with
    contract := { vars := [("x", .prim .uint)], widths := [("x", 8), ("x#bytes", 1)] } } =
    none := rfl
example : Decode.tablesW.decode { sampleRequest [] with
    contract := { vars := [("b", .prim .bool)], widths := [("b", 8)] } } = none := rfl
example : (Decode.tablesW.decode { sampleRequest [.assign (.name "s") (.num 256)] with
    contract := { vars := [("s", .prim .uint)], widths := [("t", 8)] } }).isSome = true := rfl
/-! Declarations by name: `uint8 m = n` types over `uint8 n`, `uint8 m = k` does
not over `uint16 k`, and `address`/`bytes1` names are gaps. Names are read by
string functions, so these are evaluated, not kernel-checked. -/
#guard (Decode.tablesW.decode
  (narrowRequest [.decl (.named "uint8") "m" (some (.name "n"))])).isSome
#guard (Decode.tablesW.decode
  (narrowRequest [.decl (.named "uint8") "m" (some (.name "k"))])).isNone
#guard (Decode.tablesW.decode (narrowRequest [.decl (.named "address") "m" none])).isNone
#guard (Decode.tablesW.decode (narrowRequest [.decl (.named "bytes1") "m" none])).isNone
example : Decode.tablesW.decode { narrowRequest [] with
    input := { (narrowRequest []).input with
      before := ⟨([("a", .val .uint 256 [("#address", 20)])], 1), {}⟩ } } = none := rfl
/-- The two versions' tables: the landed decoder's, and the width-aware ones. -/
example : Decode.tables1 = ⟨Decode.typeName, Decode.localTy, Decode.unit⟩ := rfl
example : Decode.tablesW = ⟨Decode.typeNameW, Decode.localTyW, Decode.unitW⟩ := rfl
/-- The bridge: at the landed tables the generic decoder is the landed decoder
and the version's spelling relation is the landed one. -/
example (r : Request) : Decode.tables1.decode r = Decode.decode r := Decode.decode_tables1 r
example {r : Request} {s : SourceProgram} : SpellsT Decode.tables1 r s ↔ Spells r s :=
  spellsT_tables1
/-- On the e1 sample the width-aware version agrees with the landed decoder. -/
example : Decode.tablesW.decode (sampleRequest RawProbe.input) =
    Decode.decode (sampleRequest RawProbe.input) := rfl
/-- A version's decoder against its spelling relation: sound, unique, and
complete if Source inference is. -/
example {T : Decode.Tables} {r : Request} {s : SourceProgram} (h : T.decode r = some s) :
    SpellsT T r s := decode_spellsT h
example {T : Decode.Tables} (complete : InferCompleteT T) {r : Request} {s : SourceProgram} :
    T.decode r = some s ↔ SpellsT T r s := ⟨decode_spellsT, SpellsT.decode complete⟩
example {T : Decode.Tables} {r : Request} {s s' : SourceProgram} (h : SpellsT T r s)
    (h' : SpellsT T r s') : s = s' := h.unique h'

/-! ### The address-aware decoder version

`Decode.tablesA` reads an erased `address` where the model marks one. It has no
boundary yet: only the decoder and its spelling relation. -/

example : Decode.tablesA = ⟨Decode.typeNameA, Decode.localTyA, Decode.unitA⟩ := rfl
/-- Over `address a; address b; uint n`: `a = b` types, and neither `a = n`
nor `n = a` does, so the marker is read as a Source `address`. -/
def addressRequest (raw : List RawStmt) : Request :=
  ⟨IntrinsicProbe.C, ⟨sampleNames, none, raw, RawProbe.scope,
    ⟨([("a", .val .uint 256 Decode.addressShape), ("b", .val .uint 256 Decode.addressShape),
       ("n", .val .uint)], 1), {}⟩⟩, none⟩
example : (Decode.tablesA.decode (addressRequest [.assign (.name "a") (.name "b")])).isSome =
    true := rfl
example : Decode.tablesA.decode (addressRequest [.assign (.name "a") (.name "n")]) = none := rfl
example : Decode.tablesA.decode (addressRequest [.assign (.name "n") (.name "a")]) = none := rfl
/-- The width-aware version has no type for a marked local. -/
example : Decode.tablesW.decode (addressRequest [.assign (.name "a") (.name "b")]) = none := rfl
/-- An address state variable (`owner#address ↦ 20`) is read; assigning it to
a `uint` does not type; a marker on a variable with its own width row, on an
`int`, or with another size is a gap. -/
def ownerContract : Contract :=
  { vars := [("owner", .prim .uint), ("total", .prim .uint)], widths := [("owner#address", 20)] }
example : (Decode.tablesA.decode { addressRequest [.assign (.name "owner") (.name "a")] with
    contract := ownerContract }).isSome = true := rfl
example : Decode.tablesA.decode { addressRequest [.assign (.name "total") (.name "owner")] with
    contract := ownerContract } = none := rfl
example : Decode.tablesA.decode { addressRequest [] with
    contract := { vars := [("o", .prim .uint)], widths := [("o", 8), ("o#address", 20)] } } =
    none := rfl
example : Decode.tablesA.decode { addressRequest [] with
    contract := { vars := [("o", .prim .int)], widths := [("o#address", 20)] } } = none := rfl
example : Decode.tablesA.decode { addressRequest [] with
    contract := { vars := [("o", .prim .uint)], widths := [("o#address", 32)] } } = none := rfl
/-- On requests with no address the version agrees with the width-aware one. -/
example : Decode.tablesA.decode (narrowRequest [.assign (.name "k") (.name "n")]) =
    Decode.tablesW.decode (narrowRequest [.assign (.name "k") (.name "n")]) := rfl
/-- Its decoder is sound for its spelling relation, as every version's is. -/
example {r : Request} {s : SourceProgram} (h : Decode.tablesA.decode r = some s) :
    SpellsT Decode.tablesA r s := decode_spellsT h

/-! ### The width-aware version's boundary (`Total.Versions`) -/

/-- Its value relation: a model `uint` holding 200 is related to the Source
`uint8` 200; a model `uint` is related to no signed Source integer. -/
example (D : Source.Layout) (h : Source.IntTy.u8.lo ≤ 200 ∧ 200 ≤ Source.IntTy.u8.hi)
    (x : PrimTy.uint.Denote) (same : x.1 = 200) :
    Version.Relation.ValRel D (.int Source.IntTy.u8) .uint (.int 200 h) x :=
  .uint Source.IntTy.u8 rfl 200 h x same
example (D : Source.Layout) (t : Source.IntTy) (signed : t.signed = true)
    (v : Source.Val D (.int t)) (x : PrimTy.uint.Denote) :
    ¬ Version.Relation.ValRel D (.int t) .uint v x :=
  fun h => by cases h with | uint _ unsigned => rw [signed] at unsigned; cases unsigned
/-- Total initial matching is a theorem for the version (Source to model). -/
example : Simulation.InitialMatching Version.rel Decode.tablesW.decode := Version.initialMatching
/-- The version's boundary admits every request whose pipeline succeeds. -/
example : FullDomain Version.boundary := Version.boundaryAt_fullDomain _ _
/-- What the contract, and its version 2, ask at the version's boundary. -/
example :
    LowerLoopsCorrectContract Version.boundary Version.boundary.reference
        Decode.tablesW.decode →
      ∀ r : Request, r.Succeeds → ∃ s, Decode.tablesW.decode r = some s :=
  fun h => (Iff.mp Version.residual_iff h).1
example :
    LowerLoopsCorrectContractV2 Version.rel Version.boundary Version.boundary.reference
        Decode.tablesW.decode → Simulation.Bound Version.rel Decode.tablesW.decode :=
  fun h => (Iff.mp Version.contractV2_iff h).2.2.2.2

end Decoder

end Solidity.Goals
