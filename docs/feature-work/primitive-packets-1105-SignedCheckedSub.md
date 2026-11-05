# Checked signed subtraction packet

`Backend.PrimitivePackets.SignedCheckedSub` connects checked int256 subtraction of two actual Source locals to the public memory compiler selection and its native word-machine execution. It reuses the existing intrinsic expression, compiler and interpreter unchanged.

`source_success` (in Source.lean) and `source_overflow` preserve the exact Source state at fuel `fuel+3`, with exact arithmetic panic payload on either signed overflow. `public_selection` (in Selected.lean) proves `Memory.compileVal` selects the supplied intrinsic expression; `original_guard` exposes the actual signed instruction sequence. `target_success` (in Target.lean) retains every machine field and an arbitrary saved stack under the result word. `target_overflow` proves coarse native revert only, without a claim about target panic bytes or a reverted target state.

`success` (in Agreement.lean) and `overflow` join those statements for arbitrary typed local indices. Their explicit premises are initial `IntegerLocalFamily`, actual Source reads and signed ranges, and the existing complete `StateRepr`; the result requires no assumed compiled selection, desired run or poststate. `overflow_iff` includes both signed bounds. Controls inhabit the local family and representation and apply the joined theorems. The Source fixture is an initial state with two locals; the target fixture retains the existing populated heap/frame. They are not a claimed whole-world state correspondence.

Controls cover both pipelines, positive/negative differences, exact signed endpoints, upper and lower overflow, forbidden overflow wrapping, wrong addition-like output and Source fuel exhaustion. The observation test emits twenty complete rows with all panic bytes, successful stack words and all eleven fixture cells. Its independent checker uses integer subtraction and signed range classification. These are kernel/native-interpreter controls, not external solc/EVM agreement, gas/resource adequacy or unknown-memory ABI encoding.

Registration proposal (coordinator/V09 integrates; no shared root or pin changes here):

- `Solidity.Backend.PrimitivePackets.SignedCheckedSub.Source`
- `Solidity.Backend.PrimitivePackets.SignedCheckedSub.Selected`
- `Solidity.Backend.PrimitivePackets.SignedCheckedSub.Target`
- `Solidity.Backend.PrimitivePackets.SignedCheckedSub.Agreement`
- `Solidity.Backend.PrimitivePackets.SignedCheckedSub.Controls`

The five modules belong in the PrimitivePackets area of the module map. Controls print the actual scoped axiom sets for integration pinning. Original V13 queues and producer dependencies remain open; this packet supplies only the bounded checked signed subtraction family.
