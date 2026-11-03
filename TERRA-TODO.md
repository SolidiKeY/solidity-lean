# VY3 routine proof handoff — H14

Status: pending; the following are precise proposed statements, NOT Lean declarations or assumed facts. No unproved declaration has been added to an importing module. Work in the private dependency implementation package until its real producer modules are integrated; preserve the frozen assignment and original proof budgets. Use automation first as H14 requires.

Target module: Bridge/SolidityBridge/Yul/CountdownScanner.lean, namespace SolidityBridge.Yul.CountdownScanner. Existing opens/names are those of that actual module.

1. `backend_destinations` — routine rewrite glue between the already-proved concrete reference-scanner list and existing backend scanner result. No new scanner soundness argument.

```lean
theorem backend_destinations :
    scanner.destinations.map UInt256.toNat =
      Backend.jumpdests (Backend.encode NativeCountdown.resolvedCode)
```

Inputs: actual `destinations` and `NativeCountdown.jumpdests_exact`.

2. `valid_list` — routine array/list round trip, no new destination coverage.

```lean
theorem valid_list : valid.toList = scanner.destinations
```

Input: actual `valid` definition and existing list/array round-trip lemma.

3. `entry_code` — routine wrapper specialization of actual `site_code`, without proving charged prefix reachability.

```lean
theorem entry_code (seed : EVM.State) (counter u v : Scalar.Word)
    (caller : List UInt256) :
    (ChargedCountdown.entry seed counter u v caller).state.executionEnv.code = code
```

Inputs: actual `ChargedCountdown.entry` and `site_code`; no producer theorem may be assumed or weakened.

Keep scanner path/success proofs, charged execution soundness, P1/P16/source/view/function/divergence and final composition with the lane proof producer. Record automation attempts and check only touched modules before returning a reviewed commit. Do not add axioms, unproved placeholders, changed observations/verdicts or increased budgets.


## ChargedEntry routine glue — pending H14

Target module: Bridge/SolidityBridge/Yul/ChargedEntry.lean, namespace SolidityBridge.Yul.ChargedEntry. Actual producer `gate` is proved. These statements are NOT Lean declarations or assumed facts. Existing module opens apply.

4. `step`: routine application of actual api.charged.checked_jump_dest and gate, preserving original horizon.

```lean
theorem step (api : P10.FrozenV1.API) (seed : EVM.State)
    (counter u v : Scalar.Word) (caller : List UInt256) (valid : Array UInt256)
    (gas : 1 ≤ seed.gasAvailable.toNat) (room : caller.length ≤ 1021) (fuel : Nat) :
    let input := (site seed counter u v caller).state
    Assembly.driverSteps 1 (fuel+2) valid input =
      .ok ((Assembly.chargedPrepare input 1).replaceStackAndIncrPC input.stack)
```

5. `continuation`: routine application of actual api.continuation.x_jump_dest and step; no whole-prefix/loop adequacy.

```lean
theorem continuation (api : P10.FrozenV1.API) (seed : EVM.State)
    (counter u v : Scalar.Word) (caller : List UInt256) (valid : Array UInt256)
    (gas : 1 ≤ seed.gasAvailable.toNat) (room : caller.length ≤ 1021) (fuel : Nat) :
    let input := (site seed counter u v caller).state
    EVM.X (fuel+2) valid input =
      EVM.X (fuel+1) valid ((Assembly.chargedPrepare input 1).replaceStackAndIncrPC input.stack)
```

6. `compiler_origin`: routine transport of SourceCountdownTransport.lowering and NativeCountdown.actual_assembly through the definitional entry-site program. No source runtime claim.

```lean
theorem compiler_origin (seed : EVM.State) (counter u v : Scalar.Word) (caller : List UInt256) :
    SourceCountdown.lower = some NativeCountdown.block ∧
    Backend.assemble 0 (fun x : Empty => nomatch x) (NativeCountdown.block.expand 0).1 =
      some {code := (site seed counter u v caller).before ++ .op .JUMPDEST ::
        (site seed counter u v caller).after, linkRefs := []}
```

Optional-root registration for ChargedEntry/Controls is deferred to coordinator generated integration (REG1 resolved). The earlier rejected edit was never executed/retried; do not hand-edit either root or treat standalone checks as final joint closure.


## Entry failure specialization — pending routine H14 glue

Target module: Bridge/SolidityBridge/Yul/ChargedEntry.lean, namespace SolidityBridge.Yul.ChargedEntry. Producer no_gas and stack_overflow are implemented; these wrappers/classifier are NOT importing declarations or assumed facts.

7. `no_gas_site`: routine specialization of actual no_gas through Site.state gas projection.

```lean
theorem no_gas_site (seed : EVM.State) (counter u v : Scalar.Word)
    (caller : List UInt256) (valid : Array UInt256) (empty : seed.gasAvailable.toNat = 0) :
    Assembly.driverGate valid (site seed counter u v caller).state .JUMPDEST = .error .OutOfGass
```

8. `stack_overflow_site`: routine specialization of actual stack_overflow using existing ChargedCountdown.result_capacity, with actual gas and caller-length bounds.

```lean
theorem stack_overflow_site (seed : EVM.State) (counter u v : Scalar.Word)
    (caller : List UInt256) (valid : Array UInt256)
    (gas : 1 ≤ seed.gasAvailable.toNat) (big : 1021 < caller.length) :
    Assembly.driverGate valid (site seed counter u v caller).state .JUMPDEST = .error .StackOverflow
```

9. `gate_cases`: routine case split using gate and the two specialized refusal laws; no new execution/soundness claim or source-error mapping.

```lean
theorem gate_cases (seed : EVM.State) (counter u v : Scalar.Word)
    (caller : List UInt256) (valid : Array UInt256) :
    let input := (site seed counter u v caller).state
    Assembly.driverGate valid input .JUMPDEST =
      if seed.gasAvailable.toNat = 0 then .error .OutOfGass
      else if caller.length ≤ 1021 then .ok (input,1)
      else .error .StackOverflow
```

REG1 is resolved by the coordinator: keep registration pending; do not edit the optional Bridge root by hand. Coordinator performs generated registration at integration. Required full names: SolidityBridge.Yul.ChargedEntry and SolidityBridge.Yul.ChargedEntryControls, optional root Bridge/SolidityBridge.lean. No further approval question remains.


## General switch composition — routine final wrapper, pending H14

Target module: Bridge/SolidityBridge/Yul/PureSwitchCompilation.lean. Existing module opens apply. Core source and generic cases_machine are already proved; this precise pairing/extraction wrapper is NOT an importing declaration or assumed fact.

10. `execution` — routine extraction of the actual block from accepted Option.bind, then pairing PureSwitch.source with cases_machine specialized to the actual test/default certificates. No additional run/profile premise.

```lean
theorem execution {fuel c n} {selector : Expr [] [] n 1} {arms : Cases [] [] c n}
    {fallback : Stmt [] [] c n} (compiled : PureSwitch.Compiled fuel selector arms fallback)
    (depth : Nat) (code : List Evm.Instr)
    (accepted : (PureSwitch.lower compiled depth).bind WordControl.blockCode = some code)
    (locals : Vector Scalar.Word n) (newer : Vector Scalar.Word depth)
    (m : Evm.Machine) (caller : List Evm.Word) :
    evalStmt (fuel+1) .nil True.intro (.switch selector arms fallback) (PureSwitch.profile compiled)
      (ProducerExpressions.sourceLocals locals) =
        some ⟨ProducerExpressions.sourceLocals (PureSwitch.update compiled locals),.normal⟩ ∧
    Evm.run code {m with stack := (newer.toList ++ locals.toList).map coreWord ++ caller} =
      .ok {m with stack := (newer.toList ++ (PureSwitch.update compiled locals).toList).map coreWord ++ caller} 0
```

This is the existing model, not native byte execution, charged resources, Source/P16/G24 or static/frontend admission. The coordinator registers optional Bridge modules at integration; do not hand-edit that root. Core PureSwitch/Controls registrations are generated with the delivered register.sh in the private tree.


## Nested normal control — routine final pairing, pending H14

Target: Bridge/SolidityBridge/Yul/NormalControlCompilation.lean. Namespace SolidityBridge.Yul.NormalControlCompilation and existing opens apply.

11. `execution`: routine extraction of the actual block from Option.bind, then pairing actual NormalControl.Derivation.source and machine. No extra run premise or budget.

```lean
theorem execution {c n fuel} {stmt : Stmt [] [] c n}
    (compiled : NormalControl.Derivation fuel stmt) (depth : Nat) (code : List Evm.Instr)
    (accepted : (compiled.emit depth).bind WordControl.blockCode = some code)
    (locals : Vector Scalar.Word n) (newer : Vector Scalar.Word depth)
    (m : Evm.Machine) (caller : List Evm.Word) :
    evalStmt fuel .nil True.intro stmt compiled.profile
      (ProducerExpressions.sourceLocals locals) =
      some ⟨ProducerExpressions.sourceLocals (compiled.update locals),.normal⟩ ∧
    Evm.run code {m with stack := (newer.toList ++ locals.toList).map coreWord ++ caller} =
      .ok {m with stack := (newer.toList ++ (compiled.update locals).toList).map coreWord ++ caller} 0
```

This statement is pending text, not an importing declaration, axiom or completed composition proof. Native bytes, charged resources/1024, P16/source-session/G24/world adequacy are excluded from this wrapper. Coordinator-generated optional registration: SolidityBridge.Yul.NormalControlCompilation.


## Charged source quotient sites — routine H14 glue, pending

Target: Bridge/SolidityBridge/Yul/ChargedQuotients.lean; namespace SolidityBridge.Yul.ChargedQuotients and existing opens apply. These are Markdown statements only; no importing declaration/axiom or assumed result. Actual source certificates, charged P10 bodies and general gate are already implemented.

12. `compiler_origin`: direct normalization of actual visitor/code and actual Site fields, not a source execution assumption.

```lean
theorem compiler_origin (seed : EVM.State) :
    divCompiled.lowered.code 0 = some ((divSite seed).before ++ .op .DIV :: (divSite seed).after) ∧
    modCompiled.lowered.code 0 = some ((modSite seed).before ++ .op .MOD :: (modSite seed).after)
```

13. `read_packet`: actual finite-DUP prefix succeeds from the two intrinsic locals and arbitrary caller; no lookup/run premise.

```lean
theorem read_packet (a b : Scalar.Word) (caller : Scalar.Stack) :
    Scalar.run reads (a::b::caller) = some (packet a b caller)
```

14. `capacities`: routine length/actual height-trace arithmetic; entry/peak and shrinking-op output bounds are deliberately different.

```lean
theorem capacities (a b result : Scalar.Word) (caller : Scalar.Stack) :
    ((packet a b caller).length ≤ 1024 ↔ caller.length ≤ 1020) ∧
    ((result::a::b::caller).length ≤ 1024 ↔ caller.length ≤ 1021) ∧
    (Scalar.stackBound divProgram ((a::b::caller).length : Int) = true ↔ caller.length ≤ 1020) ∧
    (Scalar.stackBound modProgram ((a::b::caller).length : Int) = true ↔ caller.length ≤ 1020)
```

Charged execution/gas for the preceding two DUPs and whole source/G24/P16/native/trace adequacy remain original work, not discharged by these wrappers or by P10's single arithmetic step. Optional root registration stays coordinator-generated: SolidityBridge.Yul.ChargedQuotients and SolidityBridge.Yul.ChargedQuotientsControls.


## Counted quotient-prefix joining — routine H14 glue, pending

Target: Bridge/SolidityBridge/Yul/ChargedQuotientPrefix.lean; namespace SolidityBridge.Yul.ChargedQuotientPrefix, existing opens apply. Actual reads/div_continuation/mod_continuation already derive every charged child State and full X continuation.

15. `counted`: routine joining of three successful one-step driver prefixes from those concrete proofs, by the existing driverSteps equations. Do not assume an intermediate desired run.

```lean
theorem counted (seed : EVM.State) (a b : Scalar.Word) (caller : Scalar.Stack)
    (room : caller.length ≤ 1020) (gas : 11 ≤ seed.gasAvailable.toNat) (fuel : Nat) :
    Assembly.driverSteps 3 (fuel+4) #[] (entry seed .DIV a b caller) = .ok (divFinal seed a b caller) ∧
    Assembly.driverSteps 3 (fuel+4) #[] (entry seed .MOD a b caller) = .ok (modFinal seed a b caller)
```

This is pending Markdown, not an importing declaration or assumed fact. The new X theorems already construct the actual three-instruction continuation; universal counted-driver joining and source-origin/source-G24 composition are distinct obligations. Source horizon2 and all earlier proof/test budgets remain unchanged; fuel+4→fuel+1 is the explicit three-native-step horizon relation. Register optional modules only through coordinator generation: SolidityBridge.Yul.ChargedQuotientPrefix and SolidityBridge.Yul.ChargedQuotientPrefixControls.


## Arbitrary quotient suffix — routine counted join (pending H14)

Target Bridge/SolidityBridge/Yul/QuotientSuffix.lean; namespace SolidityBridge.Yul.QuotientSuffix. Existing opens apply.

16. `counted_context`: routine joining of actual reads/div_continuation/mod_continuation charged child results, without adding a desired-run premise.

```lean
theorem counted_context (tailCode : Backend.Program) (seed : EVM.State)
    (a b : Scalar.Word) (caller : Scalar.Stack) (room : caller.length ≤ 1020)
    (gas : 11 ≤ seed.gasAvailable.toNat) (fuel : Nat) :
    Assembly.driverSteps 3 (fuel+4) #[] (entry tailCode seed .DIV a b caller) =
      .ok (divFinal tailCode seed a b caller) ∧
    Assembly.driverSteps 3 (fuel+4) #[] (entry tailCode seed .MOD a b caller) =
      .ok (modFinal tailCode seed a b caller)
```

Pending Markdown, not an imported declaration or assumed theorem. Whole X prefix continuation is proved; source/G24/valid-jump/future-suffix adequacy and arbitrary relocation are separate.


## Core normal stack consumer pairing — routine H14 wrapper, pending

17. Target `Solidity/Yul/Compilation/NormalStackTransport.lean`, namespace
`Solidity.Yul.Compilation.NormalStackTransport`. Existing opens apply.
`execution`: pair actual `NormalControl.Derivation.source` and the proved Core
`machine` theorem after extracting actual emitted/selected blocks. This is
routine Option-bind extraction/pairing, not a new execution soundness argument.
It is pending Markdown, not an importing declaration or assumed fact.

```lean
theorem execution {c n fuel} {stmt : Stmt [] [] c n}
    (compiled : NormalControl.Derivation fuel stmt) (depth : Nat) (code : List Evm.Instr)
    (accepted : (compiled.emit depth).bind blockCode = some code)
    (locals : Vector Scalar.Word n) (newer : Vector Scalar.Word depth)
    (m : Evm.Machine) (caller : List Evm.Word) :
    evalStmt fuel .nil True.intro stmt compiled.profile
      (ProducerExpressions.sourceLocals locals) =
      some ⟨ProducerExpressions.sourceLocals (compiled.update locals),.normal⟩ ∧
    Evm.run code {m with stack := (newer.toList ++ locals.toList).map coreWord ++ caller} =
      .ok {m with stack := (newer.toList ++ (compiled.update locals).toList).map coreWord ++ caller} 0
```

The selector is the actual new stack-only blockCode; do not replace it with the
broader NumericMachine/WordControl selectors. This does not discharge earlier
TERRA11, native charged/byte/1024, general Source/G24/P16 or final adequacy.


## Signed native source slices — routine H14 glue, pending

Target `Bridge/SolidityBridge/Yul/SignedPlacement.lean`, namespace
`SolidityBridge.Yul.SignedPlacement`. Existing opens apply. These are Markdown
statements, not importing declarations or assumed facts.

18. `compiler_origin`: normalization of the two actual intrinsic compiler
visitors, no new correctness argument. Executable controls already check this
code image; formal wrapper remains pending.

```lean
theorem compiler_origin :
    sdivCompiled.lowered.code 0 = some (ChargedQuotients.reads ++ [.op .SDIV]) ∧
    smodCompiled.lowered.code 0 = some (ChargedQuotients.reads ++ [.op .SMOD])
```

19. `counted`: routine joining of actual QuotientPlacement.reads and proved
signed continuation child steps by existing driverSteps equations. Do not add
a desired-run premise. Full X prefix continuation is already proved.

```lean
theorem counted (headCode tailCode : Backend.Program)
    (fits : (Backend.encode headCode).length + 3 < UInt256.size)
    (seed : EVM.State) (a b : Scalar.Word) (caller : Scalar.Stack)
    (room : caller.length ≤ 1020) (gas : 11 ≤ seed.gasAvailable.toNat) (fuel : Nat) :
    Assembly.driverSteps 3 (fuel+4) #[]
      (QuotientPlacement.entry headCode tailCode fits seed .SDIV a b caller) =
      .ok (sdivFinal headCode tailCode fits seed a b caller) ∧
    Assembly.driverSteps 3 (fuel+4) #[]
      (QuotientPlacement.entry headCode tailCode fits seed .SMOD a b caller) =
      .ok (smodFinal headCode tailCode fits seed a b caller)
```

Do not infer prefix reachability, suffix validity, general source/G24/view,
Osaka/world/trace or admission adequacy. Prior TERRA1–17 remain pending.


## Typed binary primitive consumer — routine counted joining, pending H14

20. Target `Bridge/SolidityBridge/Yul/BinaryPlacement.lean`, namespace
`SolidityBridge.Yul.BinaryPlacement`. Existing opens apply. `counted` joins the
actual charged read steps and primitive last-step result by existing driverSteps
equations. Source emitter equality is already a field of Primitive, and actual
SIGNEXTEND/SDIV instances prove both fields. Do not replace this real interface
with a weaker value-only premise or assume a desired prefix run.

```lean
theorem counted {expr : Expr [] [] 2 1} {op : Backend.Op}
    {compiled : ProducerExpressions.Compiled 2 expr} (primitive : Primitive op compiled)
    (headCode tailCode : Backend.Program)
    (fits : (Backend.encode headCode).length+3<UInt256.size)
    (seed : EVM.State) (a b : Scalar.Word) (caller : Scalar.Stack)
    (room : caller.length≤1020) (gas : 11≤seed.gasAvailable.toNat) (fuel : Nat) :
    Assembly.driverSteps 3 (fuel+4) #[]
      (QuotientPlacement.entry headCode tailCode fits seed op a b caller) =
      .ok (final primitive headCode tailCode fits seed a b caller)
```

Pending Markdown only, not an importing declaration/axiom or completed proof.
Whole X continuation and concrete producer/code-origin instances are proved;
full Source/G24/view/frontend/Osaka/world/trace closure remains separate.
Earlier TERRA1–19 stay pending, including signed origin/counting wrappers.


## Actual physical-memory compiler glue — routine H14, pending

Target `Solidity/Yul/Compilation/PhysicalStore.lean`, namespace
`Solidity.Yul.Compilation.PhysicalStore`. Existing opens apply. The hard
word-memory equality and typed image-frame law are proved. These wrappers remain
Markdown only; no unproved importing declaration or axiom.

21. `word_run`: pair existing Backend.Environment.materialize_correct with the
proved word_memory rewrite. Actual range premise must remain explicit.

```lean
theorem word_run (address : Nat) (value : Roadmap.Word) (s : Backend.Environment.Slice)
    (fits : address+32≤2^256) :
    Backend.Environment.runData (wordCode address value) s =
      some {s with memory := mstore s.memory address value}
```

22. `image_run`: routine pairing of actual byte_run and image_frame for the
constructed input view. Do not assume the desired run or logical reads.

```lean
theorem image_run {D : Source.Layout} {h : Source.Heap D} {p : Placement h}
    {τ : Source.STy} {d : Source.Data D τ} (image : MemoryImage p d)
    (m : ByteView) (base : Nat) (address value : Roadmap.Word)
    (outside : address.val<base ∨ base+image.span≤address.val)
    (stack : List Backend.Environment.Word) :
    Backend.Environment.runData (byteCode address value)
      (⟨stack,image.encode m base⟩ : Backend.Environment.Slice) =
      some ⟨stack,mstore8 (image.encode m base) address.val value⟩ ∧
    image.Reads (mstore8 (image.encode m base) address.val value) base
```

This uses the existing byte-addressed metadata slice, not Evm.Machine word cells
or a native charged interpreter. Source MemOK/writeback/admission/G24/full layout
and actual 1024/gas obligations remain separate. Earlier TERRA1–20 unchanged.


## TERRA23 — finite ADD/MUL and stack code model transport (pending)

Module: `Solidity/Yul/Compilation/ArithmeticMachine.lean`.
Routine glue after the concrete `add_step`/`mul_step` producer proofs: copy the
existing `MachineAdapter.stack_run` induction, with stack steps delegated to
`stack_step`, and only ADD/MUL delegated to the new proved laws. Do not infer
support for NumericMachine's remaining operators.

```lean
theorem arithmetic_run (p : Backend.Program) (q : List Evm.Instr)
    (selected : NumericMachine.selectCode p = some q)
    (supported : p.all (fun i => match i with
      | .op .ADD | .op .MUL => true
      | i => (MachineAdapter.selectStack i).isSome) = true)
    (xs ys : Scalar.Stack) (executed : Scalar.run p xs = some ys)
    (m : Evm.Machine) (tail : List Evm.Word) :
    Evm.run q {m with stack := xs.map MachineAdapter.coreWord ++ tail} =
      .ok {m with stack := ys.map MachineAdapter.coreWord ++ tail} 0
```

This is target-model transport with explicit successful Scalar operand/run
premise, not source/G24 or native capacity/charged execution. Concrete compiler
certificates must discharge that premise before claiming source coverage.
Earlier TERRA1–22 remain pending; no unproved Lean declaration is introduced.


## TERRA24 — finite bitwise/stack model transport (pending)

Module: `Solidity/Yul/Compilation/BitMachineExecution.lean`.
Routine finite-code induction, analogous to TERRA23, using actual bitwise model
meanings proved by the concrete sequence proofs and `MachineAdapter.stack_step`.
Extract one-step lemmas by the same simplification if needed. Keep the explicit
successful Scalar-run and supported-op premises. This is not source adequacy.

```lean
theorem bitwise_run (p : Backend.Program) (q : List Evm.Instr)
    (selected : NumericMachine.selectCode p = some q)
    (supported : p.all (fun i => match i with
      | .op .AND | .op .OR | .op .XOR => true
      | i => (MachineAdapter.selectStack i).isSome) = true)
    (xs ys : Scalar.Stack) (executed : Scalar.run p xs = some ys)
    (m : Evm.Machine) (tail : List Evm.Word) :
    Evm.run q {m with stack := xs.map MachineAdapter.coreWord ++ tail} =
      .ok {m with stack := ys.map MachineAdapter.coreWord ++ tail} 0
```

No unproved Lean declaration; TERRA1–23 remain pending. General source compiler
certificates must discharge the success premise; native gas/capacity is separate.


## TERRA25 — finite SUB/SHL/SHR and stack model transport (pending)

Module: `Solidity/Yul/Compilation/ShiftSubMachine.lean`.
Routine finite-code induction analogous to TERRA23/24. Extract matching one-step
laws from the proved concrete sequences by the same automation if required.
Keep the actual full-word shift count branches and these real premises:

```lean
theorem shift_sub_run (p : Backend.Program) (q : List Evm.Instr)
    (selected : NumericMachine.selectCode p = some q)
    (supported : p.all (fun i => match i with
      | .op .SUB | .op .SHL | .op .SHR => true
      | i => (MachineAdapter.selectStack i).isSome) = true)
    (xs ys : Scalar.Stack) (executed : Scalar.run p xs = some ys)
    (m : Evm.Machine) (tail : List Evm.Word) :
    Evm.run q {m with stack := xs.map MachineAdapter.coreWord ++ tail} =
      .ok {m with stack := ys.map MachineAdapter.coreWord ++ tail} 0
```

No unproved Lean declaration. TERRA1–24 remain pending. Concrete source compiler
certificates must discharge the successful-run premise; native resource and
Source/G24 closure remain independent.


## TERRA26 — finite DIV/MOD and stack model transport (pending)

Module: `Solidity/Yul/Compilation/QuotientMachine.lean`.
Routine finite-code induction analogous to TERRA23–25, extracting one-step laws
from the concrete sequence proofs by the same automation if required. Retain
the zero-divisor branches, actual fullword bounds and these real premises:

```lean
theorem quotient_run (p : Backend.Program) (q : List Evm.Instr)
    (selected : NumericMachine.selectCode p = some q)
    (supported : p.all (fun i => match i with
      | .op .DIV | .op .MOD => true
      | i => (MachineAdapter.selectStack i).isSome) = true)
    (xs ys : Scalar.Stack) (executed : Scalar.run p xs = some ys)
    (m : Evm.Machine) (tail : List Evm.Word) :
    Evm.run q {m with stack := xs.map MachineAdapter.coreWord ++ tail} =
      .ok {m with stack := ys.map MachineAdapter.coreWord ++ tail} 0
```

No unproved Lean declaration. TERRA1–25 remain pending. Concrete compiler
certificates must discharge success before source coverage; native/G24 remains
separate from this uncapped target model.


## TERRA27 — finite unary/stack model transport (pending)

Module: `Solidity/Yul/Compilation/UnaryMachine.lean`.
Routine finite-code induction analogous to TERRA23–26, using the existing
stack transport and the actual ISZERO/NOT meanings proved in the unary runs.

```lean
theorem unary_run (p : Backend.Program) (q : List Evm.Instr)
    (selected : WordMachine.selectCode p = some q)
    (supported : p.all (fun i => match i with
      | .op .ISZERO | .op .NOT => true
      | i => (MachineAdapter.selectStack i).isSome) = true)
    (xs ys : Scalar.Stack) (executed : Scalar.run p xs = some ys)
    (m : Evm.Machine) (tail : List Evm.Word) :
    Evm.run q {m with stack := xs.map MachineAdapter.coreWord ++ tail} =
      .ok {m with stack := ys.map MachineAdapter.coreWord ++ tail} 0
```

## TERRA28 — concrete branch source-update normalization (pending)

Module: `Solidity/Yul/Compilation/UnaryBranch.lean`.
Routine unfolding of the actual source compiler's update; split on a=0 and
normalize the existing full-word ISZERO flag. Pair with the already proved
`compiled.source` and `model_run`; no extra semantic premise is allowed.

```lean
theorem source_update (a : Scalar.Word) :
    compiled.update #v[a] = #v[if a = 0 then dirty else a]
```

These are pending statements only, not unproved Lean declarations or source/G24
coverage. TERRA1–26 remain pending; native resources remain independent.


## TERRA29 — finite unsigned-comparison/stack model transport (pending)

Module: `Solidity/Yul/Compilation/ComparisonMachine.lean`.
Routine finite-code induction analogous to TERRA23–27, extracting matching
one-step laws from the concrete run proofs by the same automation if needed.

```lean
theorem comparison_run (p : Backend.Program) (q : List Evm.Instr)
    (selected : WordMachine.selectCode p = some q)
    (supported : p.all (fun i => match i with
      | .op .LT | .op .GT | .op .EQ => true
      | i => (MachineAdapter.selectStack i).isSome) = true)
    (xs ys : Scalar.Stack) (executed : Scalar.run p xs = some ys)
    (m : Evm.Machine) (tail : List Evm.Word) :
    Evm.run q {m with stack := xs.map MachineAdapter.coreWord ++ tail} =
      .ok {m with stack := ys.map MachineAdapter.coreWord ++ tail} 0
```

## TERRA30 — concrete comparison branch source-update normalization (pending)

Module: `Solidity/Yul/Compilation/ComparisonBranch.lean`.
Routine unfolding of the actual compiler update; split on unsigned comparison
and normalize its existing flag. Pair with `compiled.source` and `model_run`.
Do not add a source/target success premise or silently switch to signed order.

```lean
theorem source_update (a b : Scalar.Word) :
    compiled.update #v[a,b] = #v[a,if a.toNat < b.toNat then dirty else b]
```

Pending statements only, no unproved Lean declarations. TERRA1–28 remain pending;
generic source/G24/native/resource closure is not inferred.


## TERRA31 — finite EXP/stack model transport (pending)

Module: `Solidity/Yul/Compilation/ExponentMachine.lean`.
Routine finite-code induction analogous to TERRA23–29, extracting the matching
one-step law from model_run by the same automation if needed. Retain these
actual premises; no exponent or gas budget is to be silently added or removed.

```lean
theorem exponent_run (p : Backend.Program) (q : List Evm.Instr)
    (selected : WordMachine.selectCode p = some q)
    (supported : p.all (fun i => match i with
      | .op .EXP => true
      | i => (MachineAdapter.selectStack i).isSome) = true)
    (xs ys : Scalar.Stack) (executed : Scalar.run p xs = some ys)
    (m : Evm.Machine) (tail : List Evm.Word) :
    Evm.run q {m with stack := xs.map MachineAdapter.coreWord ++ tail} =
      .ok {m with stack := ys.map MachineAdapter.coreWord ++ tail} 0
```

Pending statement only, no unproved Lean declaration. TERRA1–30 remain pending;
mathematical model execution does not certify native gas or feasible evaluation.


## TERRA32 — finite signed-comparison/stack model transport (pending)

Module: `Solidity/Yul/Compilation/SignedComparisonMachine.lean`.
Routine finite-code induction analogous to TERRA23–31, using the proved reading
bridge and extracting one-step comparison laws by the same automation if needed.

```lean
theorem signed_comparison_run (p : Backend.Program) (q : List Evm.Instr)
    (selected : SignedMachine.selectCode p = some q)
    (supported : p.all (fun i => match i with
      | .op .SLT | .op .SGT => true
      | i => (MachineAdapter.selectStack i).isSome) = true)
    (xs ys : Scalar.Stack) (executed : Scalar.run p xs = some ys)
    (m : Evm.Machine) (tail : List Evm.Word) :
    Evm.run q {m with stack := xs.map MachineAdapter.coreWord ++ tail} =
      .ok {m with stack := ys.map MachineAdapter.coreWord ++ tail} 0
```

Pending statement only, no unproved Lean declaration. TERRA1–31 remain pending;
concrete compiler certificates must discharge success before source coverage.


## TERRA33 — finite signed-quotient/stack model transport (pending)

Module: `Solidity/Yul/Compilation/SignedQuotientMachine.lean`.
Routine finite-code induction using the concrete VY1-backed run proofs and
existing stack transport. Preserve producer premises; do not generalize the
one-wrap signed-word encoding beyond its proved range.

```lean
theorem signed_quotient_run (p : Backend.Program) (q : List Evm.Instr)
    (selected : SignedMachine.selectCode p = some q)
    (supported : p.all (fun i => match i with
      | .op .SDIV | .op .SMOD => true
      | i => (MachineAdapter.selectStack i).isSome) = true)
    (xs ys : Scalar.Stack) (executed : Scalar.run p xs = some ys)
    (m : Evm.Machine) (tail : List Evm.Word) :
    Evm.run q {m with stack := xs.map MachineAdapter.coreWord ++ tail} =
      .ok {m with stack := ys.map MachineAdapter.coreWord ++ tail} 0
```

Pending statement only, no unproved Lean declaration. TERRA1–32 remain pending;
source certificates must discharge success before generic source coverage.


## TERRA34 — exact three-gas reserve after the existing DUP prefix (pending)

Module: `Bridge/SolidityBridge/Yul/ChargedBitwise.lean`.
Routine specialization of the already proved two-DUP argument in
QuotientPlacement.reads, with actual initial gas9 and remaining gas3. Do not
apply its old gas11 premise or raise the bitwise budget. Keep old definitions.

```lean
theorem reads_for_three (headCode tailCode : Backend.Program)
    (fits : (Backend.encode headCode).length+3<UInt256.size)
    (seed : EVM.State) (op : Backend.Op) (a b : Scalar.Word) (caller : Scalar.Stack)
    (room : caller.length≤1020) (gas : 9≤seed.gasAvailable.toNat) (fuel : Nat) :
    Assembly.driverSteps 1 (fuel+4) #[]
      (QuotientPlacement.entry headCode tailCode fits seed op a b caller) =
      .ok (QuotientPlacement.firstRead headCode tailCode fits seed op a b caller) ∧
    Assembly.driverSteps 1 (fuel+3) #[]
      (QuotientPlacement.firstRead headCode tailCode fits seed op a b caller) =
      .ok (QuotientPlacement.secondRead headCode tailCode fits seed op a b caller) ∧
    EVM.X (fuel+4) #[] (QuotientPlacement.entry headCode tailCode fits seed op a b caller) =
      EVM.X (fuel+2) #[] (QuotientPlacement.secondRead headCode tailCode fits seed op a b caller) ∧
    3≤(QuotientPlacement.secondRead headCode tailCode fits seed op a b caller).gasAvailable.toNat
```

## TERRA35 — concrete bitwise prefix continuation (pending)

Same module. Routine joining of TERRA34 and the concrete and_correspondence,
with the modularSite identity derived as in BinaryPlacement.continuation.
Repeat for OR/XOR with their actual compiled values; do not assume prefix runs.

```lean
theorem and_prefix_continuation (headCode tailCode : Backend.Program)
    (fits : (Backend.encode headCode).length+3<UInt256.size)
    (seed : EVM.State) (a b : Scalar.Word) (caller : Scalar.Stack)
    (room : caller.length≤1020) (gas : 9≤seed.gasAvailable.toNat) (fuel : Nat) :
    EVM.X (fuel+4) #[] (QuotientPlacement.entry headCode tailCode fits seed .AND a b caller) =
      EVM.X (fuel+1) #[] (after headCode tailCode fits
        (QuotientPlacement.secondRead headCode tailCode fits seed .AND a b caller)
        .AND (BitMachineExecution.andCompiled.value #v[a,b]) a b caller)
```

Pending statements only, no unproved Lean declarations. TERRA1–33 remain pending;
these are local native prefixes, not scanner/Source-G24/whole-program adequacy.

## TERRA36 — counted ISZERO slice (pending)

Module: Bridge/SolidityBridge/Yul/ChargedIszero.lean. Routine joining of
execution's two actual driver steps; no new runtime/source convention.
Statement (same namespace, opens and headCode/tailCode/fits variables):

```lean
theorem counted_execution (seed : EVM.State) (a : Scalar.Word) (caller : Scalar.Stack)
    (room : caller.length ≤ 1022) (gas : 6 ≤ seed.gasAvailable.toNat) (fuel : Nat) :
    Assembly.driverSteps 2 (fuel+3) #[] (entry headCode tailCode fits seed a caller) =
      .ok (final headCode tailCode fits seed a caller)
```

The complete X continuation is already proved by execution; this only joins
counted driverSteps. TERRA1–35 remain pending; no Lean placeholder is added.

## TERRA37 — counted NOT slice (pending)

Module: Bridge/SolidityBridge/Yul/ChargedNot.lean, namespace ChargedNot.
Routine joining of execution's two already derived steps, same arguments.

```lean
theorem counted_execution (headCode tailCode : Backend.Program)
    (fits : (Backend.encode headCode).length+2<UInt256.size)
    (seed : EVM.State) (a : Scalar.Word) (caller : Scalar.Stack)
    (room : caller.length ≤ 1022) (gas : 6 ≤ seed.gasAvailable.toNat) (fuel : Nat) :
    Assembly.driverSteps 2 (fuel+3) #[] (entry headCode tailCode fits seed a caller) =
      .ok (final headCode tailCode fits seed a caller)
```

No new source/calling convention, no assumed run; TERRA1–36 remain pending.

## TERRA38 — counted logical shifts (pending)

Module Bridge/SolidityBridge/Yul/ChargedShifts.lean. Routine counted driver
joining of actual QuotientPlacement.reads and the derived last steps.

```lean
theorem shl_counted (headCode tailCode : Backend.Program)
    (fits : (Backend.encode headCode).length+3<UInt256.size)
    (seed : EVM.State) (count value : Scalar.Word) (caller : Scalar.Stack)
    (room : caller.length≤1020) (gas : 11≤seed.gasAvailable.toNat) (fuel : Nat) :
    Assembly.driverSteps 3 (fuel+4) #[]
      (QuotientPlacement.entry headCode tailCode fits seed .SHL count value caller) =
      .ok (final headCode tailCode fits seed .SHL
        (ShiftSubMachine.shlCompiled.value #v[count,value]) count value caller)
```

Same statement for SHR/shrCompiled. Actual X continuation and source evaluation
are already proved, not assumptions. TERRA1–37 remain pending. The existing
gas11 prefix contract is sufficient; this is not a minimum-gas assertion.

## TERRA39 — counted SAR slice (pending)

Module Bridge/SolidityBridge/Yul/ChargedArithmeticShift.lean. Routine counted
driver joining of actual QuotientPlacement.reads and sar_continuation's last
step. Also expose the computed compiler origin as an rfl wrapper if useful.

```lean
theorem sar_counted (headCode tailCode : Backend.Program)
    (fits : (Backend.encode headCode).length+3<UInt256.size)
    (seed : EVM.State) (count value : Scalar.Word) (caller : Scalar.Stack)
    (room : caller.length≤1020) (gas : 11≤seed.gasAvailable.toNat) (fuel : Nat) :
    Assembly.driverSteps 3 (fuel+4) #[]
      (QuotientPlacement.entry headCode tailCode fits seed .SAR count value caller) =
      .ok (final headCode tailCode fits seed .SAR
        (sarCompiled.value #v[count,value]) count value caller)
```

Source evaluation and actual X chain are already proved. TERRA1–38 pending.
No placeholder theorem or new source/native execution convention is added.

## TERRA40 — counted arity-three modular slices (pending)

Module Bridge/SolidityBridge/Yul/ChargedModular.lean. Routine joining of
read_prefix's three actual counted steps and add_continuation's last step.
The complete source evaluation/X chain is already proved.

```lean
theorem add_counted (headCode tailCode : Backend.Program)
    (fits : (Backend.encode headCode).length+4<UInt256.size)
    (seed : EVM.State) (a b k : Scalar.Word) (caller : Scalar.Stack)
    (room : caller.length≤1018) (gas : 17≤seed.gasAvailable.toNat) (fuel : Nat) :
    Assembly.driverSteps 4 (fuel+5) #[] (entry headCode tailCode fits seed .ADDMOD a b k caller) =
      .ok (final headCode tailCode fits seed .ADDMOD (addCompiled.value #v[a,b,k]) a b k caller)
```

Same statement with MULMOD/mulCompiled. TERRA1–39 remain pending; no placeholder
Lean theorem or assumed prefix run is introduced.

## TERRA41 — counted dynamic-cost EXP slice (pending)

Module Bridge/SolidityBridge/Yul/ChargedExponent.lean. Routine counted joining
of the two actual QuotientPlacement.reads steps and continuation's last step.
No uniform exponent bound, desired run or source gas observation is introduced.

```lean
theorem counted (headCode tailCode : Backend.Program)
    (fits : (Backend.encode headCode).length+3<UInt256.size)
    (seed : EVM.State) (base exponent : Scalar.Word) (caller : Scalar.Stack)
    (room : caller.length≤1020) (gas : 6+cost exponent≤seed.gasAvailable.toNat) (fuel : Nat) :
    Assembly.driverSteps 3 (fuel+4) #[]
      (QuotientPlacement.entry headCode tailCode fits seed .EXP base exponent caller) =
      .ok (final headCode tailCode fits seed base exponent caller)
```

Source evalExpr2 and complete native X continuation already proved. TERRA1–40
remain pending; this is a statement only, without a Lean placeholder.

## TERRA42 — actual arithmetic source-slice frame factories (pending)

Module Bridge/SolidityBridge/Yul/ArithmeticSelection.lean. Routine packaging of
existing ArithmeticMachine compiled.lowered.correct into the REAL published
Selection.FrameCertificate, with prefix bounds from Scalar.prefix_capacity.
InstructionCertificate producers add/mul are already implemented; do not replace
them or claim native/Source-G24 closure. Required factory signatures:

```lean
def addFrame (a b : Scalar.Word) :
    Selection.FrameCertificate [a,b] [a+b,a,b]
def mulFrame (a b : Scalar.Word) :
    Selection.FrameCertificate [a,b] [a*b,a,b]
```

Their code fields must be ArithmeticMachine.addProgram and mulProgram, respectively;
include rfl code-field theorems. The frame fields reuse each ACTUAL compiled
expression's lowered.correct at depth0 and locals #v[a,b]. The prefixes fields
reuse Scalar.prefix_capacity after rewriting the supplied split equality; retain
stackBound as a real explicit condition on the WHOLE incoming stack. No capacity
conclusion from scalar/model success alone. TERRA1–41 remain pending. These are
statements only; no placeholder declaration or assumed theorem is added to Lean.

## TERRA43 — selection-sequence projections and capacity wrapper (pending)

Module Bridge/SolidityBridge/Yul/SelectionSequence.lean. Routine consequences of
the proved exact execute equality; no new semantic assumptions or compiler AST.

```lean
theorem refusal (ir : List Evm.Instr) (pick : Certificates ir)
    (input : Scalar.Stack) (m : Evm.Machine) (represented : m.stack = irStack input) :
    Evm.run ir m = .fault ↔ Scalar.run (emit ir pick) input = none

theorem success (ir : List Evm.Instr) (pick : Certificates ir)
    (input output : Scalar.Stack) (m : Evm.Machine) (represented : m.stack = irStack input) :
    Evm.run ir m = .ok {m with stack := irStack output} 0 ↔
      Scalar.run (emit ir pick) input = some output
```

Use ArithmeticSelection.irStack_injective for the reverse output identity.
An optional prefix-capacity wrapper must retain stackBound on the WHOLE emitted
program/input stack and use Scalar.prefix_capacity; no implication from model
success alone. TERRA1–42 remain pending. These are statements, no Lean placeholders.

## TERRA44 — finite DUP selection and compiler-code projections (pending)

Module Bridge/SolidityBridge/Yul/StackSelection.lean. Routine projections of
implemented concrete producers, not new instruction/source semantics.

```lean
theorem select_dup (n : Fin 16) :
    (select (.dup (n.val+1))).map (fun c => c.code) = some [.op (.DUP n)]

theorem add_emit : SelectionSequence.emit [.dup 2,.dup 2,.add] addCertificates =
    ArithmeticMachine.addProgram

theorem mul_emit : SelectionSequence.emit [.dup 2,.dup 2,.mul] mulCertificates =
    ArithmeticMachine.mulProgram
```

Use exact finite-index arithmetic/proof irrelevance for select_dup; the concrete
code equations already compute in controls. SelectionSequence.execute with these
real certificates now transports the actual source ADD/MUL IR programs, including
failure. TERRA42 frame factories and TERRA43 projections/capacity wrapper remain
pending with TERRA1–41; no native/G24/physical-capacity inference is added.

## TERRA45 — SWAP/POP selection and concrete assignment-code projections (pending)

Module Bridge/SolidityBridge/Yul/WriteSelection.lean. Routine code projections
of already implemented actual producers and concrete source/model instances.

```lean
theorem select_swap (n : Fin 16) :
    (select (.swap (n.val+1))).map (fun c => c.code) = some [.op (.SWAP n)]

theorem assignment_emit : compiled.lowered.code 0 =
    some (SelectionSequence.emit assignmentIR assignmentCertificates)

theorem sequence_emit : sequenceCompiled.lowered.code 0 =
    some (SelectionSequence.emit sequenceIR sequenceCertificates)
```

Concrete assignment_model/sequence_model ALREADY discharge these identities
by rfl and prove the genuine source/model conjunction, not a run assumption.
These named projections are convenience wrappers. TERRA1–44 remain pending;
retain capacity and full Source/G24/native obligations separately.

## TERRA46 — numeric PUSH and scope-code projections (pending)

Module Bridge/SolidityBridge/Yul/LiteralSelection.lean. Routine code projections
of actual producers and concrete source/model scope instances.

```lean
theorem select_push (value : Scalar.Word) :
    (select (.push (coreWord value))).map (fun c => c.code) = some [pushWord value]

theorem let_emit (literal : Scalar.Word) : (letCompiled literal).lowered.code 0 =
    some (SelectionSequence.emit (letIR literal) (letCertificates literal))

theorem zero_emit : zeroCompiled.lowered.code 0 =
    some (SelectionSequence.emit zeroIR zeroCertificates)
```

let_model/zero_model already close emission identities by rfl and prove actual
source/model composition. These are convenience wrappers; retain all numeric
context/depth and capacity/native/G24 limitations. TERRA1–45 remain pending.

## TERRA47 — source/StructuredExec pairing wrapper (pending)

Module Bridge/SolidityBridge/Yul/StructuredSource.lean. Routine conjunction of
existing compiled.source and the implemented structured theorem, not a new
interpreter or control semantics.

```lean
theorem source_and_structured {c n fuel} {stmt : Solidity.Yul.Stmt [] [] c n}
    (compiled : NormalControl.Derivation fuel stmt) (depth : Nat) (block : Backend.Block)
    (emitted : compiled.emit depth = some block)
    (locals : Vector Scalar.Word n) (newer : Vector Scalar.Word depth) (tail : Scalar.Stack) :
    Solidity.Yul.Closed.evalStmt fuel .nil True.intro stmt compiled.profile
      (ProducerExpressions.sourceLocals locals) =
      some ⟨ProducerExpressions.sourceLocals (compiled.update locals),.normal⟩ ∧
    Selection.StructuredExec block (newer.toList ++ (locals.toList ++ tail))
      (newer.toList ++ ((compiled.update locals).toList ++ tail))
```

The actual source and structured facts are already separately checked; this is
a convenience wrapper. It must not imply Evm.Machine or LabelExec/native
realization, shape/ExpansionRoom/capacity, loops or general Source/G24. TERRA1–46
remain pending; no placeholder declaration is added to Lean.

## TERRA48 — concrete arithmetic-branch projections (pending)

Module Bridge/SolidityBridge/Yul/BranchModel.lean. Routine projections of the
implemented genuine source/model conjunction and checked compiler code origin.

```lean
theorem condition_emit : condition.lowered.code 0 =
    some (SelectionSequence.emit conditionIR conditionCertificates)
theorem arm_emit : arm.lowered.code 0 =
    some (SelectionSequence.emit armIR armCertificates)
theorem block_emit : compiled.emit 0 = some
    (.ite (SelectionSequence.emit conditionIR conditionCertificates)
      (.code (SelectionSequence.emit armIR armCertificates)) (.code []))
```

The concrete example_model already closes the child-code identities by rfl and
proves both source evaluation and complete Evm.Machine branch execution for all
correct numeric inputs. Named source/run projections may use its .1/.2. Keep
depth0/numeric source context and native byte/PC/gas/expanded-capacity/G24 limits
visible. TERRA1–47 remain pending; no Lean placeholders are introduced.
