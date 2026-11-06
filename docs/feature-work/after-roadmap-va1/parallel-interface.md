# PARALLEL-INTERFACE: VA1 numeric coverage and fixed-array facts

Producer branch: codex/solidity-automation-20261031/va1-decision.
Frozen base: 8bd8742ad987d566f7ba7624372cec1c020be07c.
Exact checked implementation head: 782dcff93a13fd1a19f0f45e6246146815555ef5.
This is a development dependency package, not full-lane or integration approval.
VA2 may consume these concrete committed declarations in a private dependency
worktree without waiting for the global Residue theorem or this entire branch.
The coordinator exchanges packages; no worker pushes or merges.

## Modules and immutable source hashes

| Actual module path | SHA256 of producer Git blob |
|---|---|
| `Solidity/Calculus/DecisionNumericCoverage.lean` | `413985d346d27f34f7b4c1f39e494eb1c03cdf52205b1c67bbd1f25f31e33f2a` |
| `Solidity/Calculus/DecisionNumericFormula.lean` | `28e82ff93db0b4b31af308f43cdc67fe8290f80848c4263a93479f117ae5fa1e` |
| `Solidity/Calculus/DecisionNumericBounds.lean` | `67d04fcfc13d3a38cdc1ef9a1ebdca04d181e886dcbb3f8d273e9322174e97b0` |
| `Solidity/Calculus/DecisionUIntPrefix.lean` | `d5cb6b168fb43071fc62f3856f7d5250c9997c38a6409fb2ff6a57f933be7b8d` |
| `Solidity/Calculus/DecisionUIntGrammar.lean` | `f0ce7bc2678911f04989030c602aa40f5aad3ccdcb622c1ee36994425d57898c` |
| `Solidity/Calculus/FixedArrayRoot.lean` | `8bece4d6e3c2c2353d0ad8c5d972569aef818da60307229fd1c7f2a32d054fbf` |
| `Solidity/Examples/DecisionNumericCoverage.lean` | `856e9ac9856269e57353517af46d2a4157dbabf7b43db35e33274c94f81e77c8` |

## Concrete typed consumer interfaces

All declarations below live in Solidity.Decide, except the existing intrinsic
grammar Tm.UIntLinear. Import Solidity.Calculus.DecisionNumericCoverage for the
numeric family. The formula constructor primitivePrefixEq takes name : Var and
a,b : Tm C [.val .uint] (.val .uint), returning Fml C []. No untyped term or
semantic oracle is introduced.

```lean
theorem uintPrefix_hashFree {C : Contract} (name : Var)
    {a b : Tm C [.val .uint] (.val .uint)} (ha : a.UIntLinear) (hb : b.UIntLinear) :
    (primitivePrefixEq name a b).hasHash = false

theorem uintPrefix_inTarget {C : Contract} (name : Var)
    {a b : Tm C [.val .uint] (.val .uint)} (ha : a.UIntLinear) (hb : b.UIntLinear) (w : Waivers) :
    (primitivePrefixEq name a b).inTarget w = true

theorem uintPrefix_Covered {C : Contract} (name : Var)
    {a b : Tm C [.val .uint] (.val .uint)} (ha : a.UIntLinear) (hb : b.UIntLinear)
    (hs : a.size + b.size ≤ 71) : (primitivePrefixEq name a b).Covered = true

theorem uintPrefix_decided {C : Contract} (name : Var)
    {a b : Tm C [.val .uint] (.val .uint)} (ha : a.UIntLinear) (hb : b.UIntLinear)
    (hs : a.size + b.size ≤ 71) : decideGoal (primitivePrefixEq name a b) ≠ .unknown

theorem uintPrefix_certified {C : Contract} (name : Var)
    {a b : Tm C [.val .uint] (.val .uint)} (ha : a.UIntLinear) (hb : b.UIntLinear)
    (hs : a.size + b.size ≤ 71) :
    (decideGoal (primitivePrefixEq name a b) = .proved ∧ Fml.ValidH (primitivePrefixEq name a b)) ∨
      ∃ σ : State C [], decideGoal (primitivePrefixEq name a b) = .refuted σ ∧
        ¬ Fml.holdsH σ (primitivePrefixEq name a b)
```

The parser/cut/lift invariants are proved against actual existing functions.
uintPrefix_prepared_coverageFacts exposes leafOf? = some (.all 0 .uint ψ),
source grammar at both flags, permitted atom (.uint,0), condMax=2, the exact
source-derived node upper bound, successful parsing, cut identity at every
previous-definition list/start counter, and zero conditionals. Consumers may use
these facts individually rather than require completion of every pipeline.

## Witnessed concrete clients

Solidity.Examples.DecisionNumericCoverage.near_limit_generic_coverage and
near_limit_generic_decided apply the generic theorem to symbolicChain 17 on
both sides: raw size 70, actual prepared body 503 nodes. partial_generic_coverage
and partial_generic_certificate use x-1 and x-2, with actual refutation and
both-halt/one-halt semantic controls. strict_unused_binder_generic_coverage uses
literal equality and an unused binder. These are checked clients, not assumed
future facts. All 30 public theorem axiom reports and exact-source MCP/build
records are in /workspace/va1-evidence/numeric-coverage-next/verified-gates.json.

## Fixed-array producer facts available independently

Import Solidity.Calculus.FixedArrayRoot. fixedFloorRoot_find proves actual typed
storage-root lookup at every uint index and every typed element continuation
Path E U agrees with the original lookup at fixedFloorIndex B i, provided the
actual fixed length n belongs to B. fixedFloorRoot_retained additionally keeps
retained indices; fixedFloorRoot_word and fixedFloorRoot_has cover word and
presence observations, including absent paths. Other-root/frame facts are
available in that same module. These do not assume a future array classifier
or completed AU02 pipeline. Their exact signatures are in the shipped source.

## Premises and outstanding concrete closure

The numeric source-to-Covered/decided/certified theorem requires both UIntLinear
grammars and a.size+b.size <=71. This condition is sufficient only; it is not a
new budget, target exclusion, Residue definition or characterization of unknown.
The generic target theorem holds for every Waivers setting. Hash-freedom is
proved structurally before existing completeness is applied. Returned proof
certificates are ValidH and refutations are explicit State C [] with not holdsH;
all original hash validity premises remain. Larger-source folded-to-covered
and 517-node uncovered-but-proved countercontrols are retained.

No VA2 future producer declaration is required by these interfaces. VA2 may
build call-sharing consumer proofs now against these exact modules. Combining
with its concrete source and final import/full gates remains necessary; another
VM's timings are not this VM's pass. This package is source/kernel-proof
evidence, not EVM execution evidence. Global Residue/theorem/exhaustive bridge,
broader revised M4 boundary, remaining AU02 pipelines/general fuel and final
full validation stay open. Q1 is answered; Q2/frontend repair remains held.
The existing goal/VM/thread/branch and earlier seals are preserved.
