import Solidity.Calculus.RuleSoundness
import Solidity.Wp.Terminal.Table
import Solidity.Counterexamples.RefSourceOrder
import Solidity.Counterexamples.MappingSideConditions

/-!
# What the unfold-rule soundness theorems still assume

`Calculus/RuleSoundness.lean` promises one `<rule>_sound` theorem per unfold
rule.  This file reads those theorems back and pins, with `#guard_msgs`, the
hypotheses each carries beyond `hcond` and `hfresh`.  Removing a hypothesis,
adding one, a rule losing its theorem or a `sorry` appearing under one all
change the output, so the pin is a ratchet: every such change is a visible
re-pin in the diff, never a silent one.

An unfold rule is one in `ruleNames` without a terminal update
(`Wp.hasUpdate`), and its theorem is `<rule>_sound`, or `<rule>_sound_inlined`
for the two function-call rules, which are only meaningful relative to
inlining.  A hypothesis is reported by its binder name, so the names are part
of the contract: a hypothesis that means something new gets a new name.

`hypKind` says what is known about each name.  A `semantic` entry names the
refutation that shows dropping it is false, and elaborating the table checks
that the refutation exists.  `docs/soundness-hypotheses.md` is the prose
companion: what each hypothesis says, what would free it, and the attempts
made so far.
-/

namespace Solidity
namespace SoundnessLedger

open Lean Meta Elab Command

/-- What is known about a hypothesis name. -/
inductive HypKind where
  /-- Proof-technique residue: the docstring of `RuleSoundness` says the
  theorem should hold without it. -/
  | residue
  /-- Dropping it is refuted by the named theorem. -/
  | semantic (refutation : Lean.Name)
  /-- Guaranteed by the surface language's typing but not by the untyped
  statement model; a well-typedness premise would discharge it. -/
  | typing
  /-- Alias freshness for a theorem stated without `hfresh`: KeY's
  `\newTypeOf`, a property of the calculus and not debt. -/
  | fresh
  | unclassified

def HypKind.label : HypKind → String
  | .residue => "residue"
  | .semantic r => s!"semantic ({r.getString!})"
  | .typing => "typing"
  | .fresh => "fresh"
  | .unclassified => "unclassified"

/-- Stated by every theorem, and not debt. -/
def baseline : List String := ["hcond", "hfresh"]

def hypKind : String → HypKind
  | "hlhs" | "hplhs" => .residue
  | "hprim" => .semantic ``Counterexamples.RefSourceOrder.refSource_disagrees
  | "hnm" => .semantic ``Counterexamples.MappingSideConditions.m3_refutes
  | "horig" | "hself" | "hnsl" | "hnmr" | "hnst" | "hml" | "hwf" | "htye"
  | "hkp" | "hkpm" | "htyE" | "hasgn" | "hkm" => .typing
  | "hfl" => .fresh
  | _ => .unclassified

/-- The constructor name of a rule, without its arguments. -/
def ctorName (r : RuleName) : String :=
  (((reprStr r).splitOn " ").head!.splitOn ".").getLast!.replace "(" ""

/-- One row: the hypotheses beyond `baseline`, whether the theorem depends on
`sorryAx`, or `none` if the rule has no theorem. -/
def ledgerRow (env : Environment) (rule : String) :
    MetaM (Option (List String × Bool)) := do
  let base := Lean.Name.mkStr `Solidity.RuleSoundness (rule ++ "_sound")
  let some c := [base, base.appendAfter "_inlined"].find? env.contains
    | return none
  let hyps ← forallTelescope (← getConstInfo c).type fun xs _ =>
    xs.toList.filterMapM fun x => do
      let d ← x.fvarId!.getDecl
      let n := toString d.userName
      return if (← isProp d.type) && !baseline.contains n then some n else none
  let axioms ← collectAxioms c
  return some (hyps, axioms.contains ``sorryAx)

/-- The ledger of every unfold rule, in `ruleNames` order, followed by a count
per hypothesis. -/
elab "#soundness_ledger" : command => do
  let env ← getEnv
  let rules := (Rules.ruleNames.filter (!Wp.hasUpdate ·)).map ctorName |>.eraseDups
  let mut rows : Array String := #[]
  let mut clean : Nat := 0
  let mut missing : Nat := 0
  let mut sorries : Nat := 0
  let mut counts : Std.HashMap String Nat := {}
  for rule in rules do
    match ← liftTermElabM (ledgerRow env rule) with
    | none =>
        missing := missing + 1
        rows := rows.push s!"{rule}: MISSING"
    | some (hyps, hasSorry) =>
        if hasSorry then sorries := sorries + 1
        if hyps.isEmpty && !hasSorry then
          clean := clean + 1
        else
          let tag := if hasSorry then " [sorry]" else ""
          rows := rows.push s!"{rule}: {" ".intercalate hyps}{tag}"
        for h in hyps do
          counts := counts.insert h (counts.getD h 0 + 1)
  let summary := counts.toList.toArray.qsort (fun a b =>
    a.2 > b.2 || (a.2 == b.2 && a.1 < b.1))
  let summaryRows := summary.toList.map fun (h, n) =>
    s!"  {h} ×{n} {(hypKind h).label}"
  logInfo <| "\n".intercalate <|
    [s!"{rules.length} unfold rules: {clean} clean, {rows.size - missing} open, \
      {missing} missing, {sorries} sorry"] ++ rows.toList ++
    ["hypotheses:"] ++ summaryRows

/--
info: 80 unfold rules: 26 clean, 50 open, 4 missing, 2 sorry
storageFieldReadUnfoldRightFst: hlhs hplhs hppath hnm
storageIndexReadUnfoldRightFst: hlhs hplhs hppath hpidx hnm
storageIndexReadUnfoldRightSndIndex: hlhs hplhs hpidx hbase hnm
storagePushValueUnfoldRightSndArgument: hbase harr htyE hprhs [sorry]
storageFieldReadUnfoldRightSndResult: hlhs hplhs
storageIndexReadUnfoldRightSndResult: hlhs hplhs hnm
storageFieldWriteRefUnfoldLeftFst: hev hstable
storageIndexWriteRefUnfoldLeftFst: hev hstable hstableI
storageLocalRootPushUnfoldLeftFstReceiver: hlhs hplhs hnst hasgn hptgt hprimF hnm
storageIndexWriteRefUnfoldLeftSndIndex: hev hstableI
storageIndexDeleteNonSimpleIndexCapture: hbase
storageRootWriteUnfoldSource: hlhs hplhs hnsl hnmr hstable
storageFieldWriteUnfoldSource: hlhs hplhs hnsl hnmr hstable
storageIndexWriteUnfoldSource: hlhs hplhs hnsl hnmr hstable
storageLocalDeclInitDrop: horig
localValueDeclInitDrop: hself
transferUnfoldRightSndArgument: hrec hpamt
memoryFieldReadUnfoldRightFst: hlhs hplhs hnsl hkp hppath
memoryIndexReadUnfoldRightFst: hlhs hplhs hnsl hkp hppath
memoryIndexReadUnfoldRightSndIndex: hlhs hplhs hnsl hpi hbase
memoryFieldReadUnfoldRightSndResult: hlhs hplhs hml hwf
memoryIndexReadUnfoldRightSndResult: hlhs hplhs hml hwf
memoryFieldWriteUnfoldLeftFst: hkp
memoryIndexWriteUnfoldLeftFst: hkp
memoryFieldWriteRefUnfoldLeftFst: hkpm hev hstable
memoryIndexWriteRefUnfoldLeftFst: hkpm hev hstable hstableI
memoryFieldDeleteUnfoldLeftFst: hkp
memoryIndexDeleteUnfoldLeftFst: hkp
memoryIndexWriteUnfoldLeftSndIndex: hkp
memoryIndexWriteRefUnfoldLeftSndIndex: hkpm hev hstableI
memoryIndexDeleteNonSimpleIndexCapture: hbase
memoryFieldWriteUnfoldSource: hlhs hplhs hnsl hnmr hstable
memoryIndexWriteUnfoldSource: hlhs hplhs hnsl hnmr hstable
memoryToStorageFieldUnfoldLeftFst: hnp hev hstable
memoryToStorageIndexUnfoldLeftFst: hprim
memoryToStorageIndexUnfoldLeftSndIndex: hprim
storageFieldOpAssignUnfoldLeftFst: hprim
storageIndexOpAssignUnfoldLeftFst: hprim
storageFieldIncrementUnfoldLeftFst: hppath
storageIndexIncrementUnfoldLeftFst: hppath
memoryFieldOpAssignUnfoldLeftFst: MISSING
memoryIndexOpAssignUnfoldLeftFst: MISSING
memoryFieldIncrementUnfoldLeftFst: MISSING
memoryIndexIncrementUnfoldLeftFst: MISSING
binopUnfoldRight: hlv hpr
logicalAndShortCircuitRhs: hlv hrb
logicalOrShortCircuitRhs: hlv hrb
ternaryCaptureCond: hlhs hplhs hprim hnsl hnmr hstable
ternaryToIfStorage: hlhs hfl hprim htye hnsl hnmr
ternaryToIfMemory: hlhs hfl hprim htye hnsl hnmr
compoundAssignValueRhsCapture: hplhs hold hstableOld
functionCallArgCapture: hcap hpure hcallee [sorry]
storagePushLhsToPushValue: hpt hprim hev
memoryToStorageUnfoldRightFstSource: hlhs hplhs hnsl hnmr hkm hprhs hevalEq hwf
hypotheses:
  hlhs ×20 residue
  hplhs ×19 residue
  hnsl ×12 typing
  hstable ×11 unclassified
  hnmr ×9 typing
  hev ×8 unclassified
  hprim ×8 semantic (refSource_disagrees)
  hkp ×7 typing
  hppath ×6 unclassified
  hbase ×5 unclassified
  hnm ×5 semantic (m3_refutes)
  hstableI ×4 unclassified
  hkpm ×3 typing
  hlv ×3 unclassified
  hwf ×3 typing
  hfl ×2 fresh
  hml ×2 typing
  hpidx ×2 unclassified
  hprhs ×2 unclassified
  hrb ×2 unclassified
  htye ×2 typing
  harr ×1 unclassified
  hasgn ×1 typing
  hcallee ×1 unclassified
  hcap ×1 unclassified
  hevalEq ×1 unclassified
  hkm ×1 typing
  hnp ×1 unclassified
  hnst ×1 typing
  hold ×1 unclassified
  horig ×1 typing
  hpamt ×1 unclassified
  hpi ×1 unclassified
  hpr ×1 unclassified
  hprimF ×1 unclassified
  hpt ×1 unclassified
  hptgt ×1 unclassified
  hpure ×1 unclassified
  hrec ×1 unclassified
  hself ×1 typing
  hstableOld ×1 unclassified
  htyE ×1 typing
-/
#guard_msgs in
#soundness_ledger

end SoundnessLedger
end Solidity
