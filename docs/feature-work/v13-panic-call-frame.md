# Full-word Panic packet and typed self-call consumers

`PanicReadWindow.decode` proves the published decoder returns the exact typed
word for every natural code below2^256, with arbitrary trailing bytes. There is
no ByteRange premise. `error_reject` proves the preceding Error branch cannot
match. `emitted` consumes actual Failure.Input.panic emission, Fits and stack
capacity and reads the exact canonical36bytes from reached Slice memory.

`PanicCallFrame.call_data` executes an actual zero-argument literal-data callee
through Prog.runR/TRun.call. `selected` discharges that failed call, respects
Error-before-Panic branch order, supplies actual CodeBinder.decodeT and drops
the clause extension. Receiver-nonzero/self identity remain explicit conditions,
not a desired failed-call assumption. The populated `application` discharges
those conditions with receiver7 and a nonempty caller containing result/marker
scalars and two aliases of an older byte object. For ANY code below2^256 and
ANY suffix, actual tryCall copies the code into the original result, drops its
code and bool clause locals, and preserves marker77/heaplength1/alias0 twice
with exact ordered bytes161,178. This is not just a finite decoder fixture.

The callee performs revertData of encoded Panic bytes: its halt is revertWith,
not THalt.panic. No provenance for source panics, arbitrary callees, callback,
external-world rollback, source/target simulation or compiler selection follows.
Canonical emitted bytes are36long; suffix-bearing call packets can be longer.
They share a decoded code, not an assumed same-invocation/byte-machine trace.
No Source PanicCode/profile is extended by testing arbitrary packet codes.

Twelve finite codes include0, all named source-code numbers,300, highbit2^255
and maximum2^256-1. Actual emitter Fits/stack premises are discharged; complete
packet/readback bytes and decoded scalar observations exported. Zero receiver,
truncated word, wrong selector and300-vs44 controls use actual intrinsic calls.
Overflowing natural2^256 wraps to0 in its encoded word, and is explicitly not
read as that natural. This preserves modulo-vs-natural distinctions.

Automation-first failed on generic decoding; existing word/read/append facts
completed it. Failed binder-name/control-elaboration/projection and recursion
attempts retained. Kernel decision discharges overflow controls without a
recursion/heartbeat/fuel/time increase or trust shortcut. Per-file diagnostics
pass; independent source finder/skeptic PASS with no findings. Final artifact
reviews are recorded externally. All old sources, observations, seals and
originalmain remain preserved; no reserved semantic or producer edits.

This advances G41 and intrinsic G42/BackfillB preparation. G21/G41/G42.04/G42.06
and BackfillsA/B remain partial, as do original arbitrary self/external-world
obligations. G40/G42.05 transferred; G42.03/P3 readonly-external-owned. No work
on moved/restricted items, unknown-memory encoder or missing source/native/world
producer is disguised as this proof. Original whole-lane mandatory failures
remain failed; no unchanged heavy retry or goal administration. Serial-j1,
12GiB/no-swap/reserve4GiB and original proof/node/fuel/time limits unchanged.

Coordinator-generated registration modules:

- `Solidity.Backend.AbiWorld.PanicReadWindow`
- `Solidity.Backend.AbiWorld.PanicCallFrame`
- `Solidity.Backend.AbiWorld.PanicCallFrameControls`
