import Solidity.Kernel.Sound

/-!
# Every statement has a rule

Phase 4 of `docs/kernel-port.md`, after mini-solkey's `Stmt.step`
(`Ch06_Taclets`) and `Ch11_Completeness`.  `Stmt.step m s` is the rule for `s`
under the modality `m`, with its premise and the derivation `Taclet C m s pr`.
It is a **total function** over the typed syntax, so Lean's exhaustiveness
check on its patterns is the coverage proof: `Stmt.complete` states it.  A
combination the types rule out (an alias assigned a value, a `delete` of an
alias, a stack field) needs no arm.

Which rule fires is decided by the constructors of the statement and by
whether its parts are simple (`SPath.isSimple`, `Val.isSimple`), as the
paper's schema-variable sorts decide it.  Scratch names come from
`freshName`: the rule table's own `sp`, `se`, `ie` when they are free, which
is what makes a residual erase to `ruleEffect`'s on a program that does not
use them.
-/

namespace Solidity
namespace Kernel

open Semantics

variable {C : Contract}

/-- A rule for `s`: its premise, and the derivation. -/
abbrev Step (C : Contract) (m : Modality) {Γ Γ' : Ctx} (s : Stmt C Γ Γ') :=
  (pr : Premise C Γ Γ') ×' Taclet C m s pr

theorem not_simple {b : Bool} (h : ¬ b = true) : b = false := by simpa using h

variable (m : Modality)

/-- Step 1 in a hole: the path read is not bindable, so its receiver or its
index is not simple. -/
def Hole.unfoldStep {Γ Γ' : Ctx} {T : Ty} (k : Hole C Γ Γ' T) :
    (l : Loc C Γ T) → (SPath.loc l).isBindable = false → Step C m (k.fill (.loc l))
  | .root .., h => absurd h (by simp [SPath.isBindable, SPath.isSimple])
  | .field b f hf, h =>
    if hb : b.isSimple = true then absurd h (by simp [SPath.isBindable, hb])
    else ⟨_, .storageFieldRead_unfold_rightFst k b (not_simple hb) f hf _ (freshName_isFresh C Γ' "sp")⟩
  | .index it b i, h =>
    if hb : b.isSimple = true then
      if hi : i.isSimple = true then absurd h (by simp [SPath.isBindable, hb, hi])
      else ⟨_, .storageIndexRead_unfold_rightSndIndex k it b hb i (not_simple hi) _
        (freshName_isFresh C Γ' "ie")⟩
    else ⟨_, .storageIndexRead_unfold_rightFst k it b (not_simple hb) i _ (freshName_isFresh C Γ' "sp")⟩

/-- A copy into a member or an entry (`nlhs = …`), from a path. -/
def copyStep {Γ : Ctx} {R : RefTy} (l : Loc C Γ (.ref R)) (hl : (SPath.loc l).isSimple = false)
    (hm : (Ty.ref R).mapFree = true) (sp₂ : SPath C Γ (.ref R))
    (simpleStep : sp₂.isSimple = true → Step C m (.assign l (.copy sp₂ hm))) :
    Step C m (.assign l (.copy sp₂ hm)) :=
  if hs : sp₂.isSimple = true then simpleStep hs
  else match sp₂, hs with
    | .alias .., hs => absurd rfl hs
    | .loc (.root ..), hs => absurd rfl hs
    | .loc (.field b f hf), hs =>
      if hb : b.isSimple = true then
        ⟨_, .storageFieldRead_unfold_rightSndResult l hl hm b hb f hf _ (freshName_isFresh C Γ "se")⟩
      else (Hole.copy l hm).unfoldStep m (.field b f hf) (by simp [SPath.isBindable, not_simple hb])
    | .loc (.index it b i), hs =>
      if hbi : b.isSimple = true ∧ i.isSimple = true then
        match i, hbi with
        | .simple ie, hbi =>
          ⟨_, .storageIndexRead_unfold_rightSndResult l hl hm it b hbi.1 ie _ (freshName_isFresh C Γ "se")⟩
      else (Hole.copy l hm).unfoldStep m (.index it b i) (by simpa [SPath.isBindable] using hbi)

/-- `lhs = c ? a : b`: lower it to a branch on a simple condition, capture
any other condition first. -/
def ternaryStep {Γ : Ctx} {p : PrimTy} (k : VHole C Γ p) (c : Val C Γ .bool) (a b : Val C Γ p) :
    Step C m (k.fill (.ternary c a b)) :=
  match c with
  | .simple c =>
    match k with
    | .local x h => ⟨_, .ternaryToIf x h c a b⟩
    | .store l => ⟨_, .ternaryToIfStorage l c a b⟩
  | .read l => ⟨_, .ternaryCaptureCond k (.read l) rfl a b _ (freshName_isFresh C Γ "se")⟩
  | .binop op hop hq x y => ⟨_, .ternaryCaptureCond k (.binop op hop hq x y) rfl a b _ (freshName_isFresh C Γ "se")⟩
  | .unop op hop hq x => ⟨_, .ternaryCaptureCond k (.unop op hop hq x) rfl a b _ (freshName_isFresh C Γ "se")⟩
  | .ternary c' x y => ⟨_, .ternaryCaptureCond k (.ternary c' x y) rfl a b _ (freshName_isFresh C Γ "se")⟩

/-- A storage write. -/
def assignStep {Γ : Ctx} {T : Ty} : (l : Loc C Γ T) → (r : Src C Γ T) → Step C m (.assign l r)
  -- a state variable
  | .root x hΓ hr, .val (.simple a) => ⟨_, .storageRootWriteStore x hΓ hr a⟩
  | .root x hΓ hr, .val (.read l) =>
    ⟨_, .storageRootWriteValueRhsCapture x hΓ hr (.read l) rfl _ (freshName_isFresh C Γ "se")⟩
  | .root x hΓ hr, .val (.binop op hop hq a b) =>
    ⟨_, .storageRootWriteValueRhsCapture x hΓ hr (.binop op hop hq a b) rfl _ (freshName_isFresh C Γ "se")⟩
  | .root x hΓ hr, .val (.unop op hop hq a) =>
    ⟨_, .storageRootWriteValueRhsCapture x hΓ hr (.unop op hop hq a) rfl _ (freshName_isFresh C Γ "se")⟩
  | .root x hΓ hr, .val (.ternary c a b) => ternaryStep m (.store (.root x hΓ hr)) c a b
  | .root x hΓ hr, .copy sp₂ hm =>
    if hs : sp₂.isSimple = true then ⟨_, .storageRootWriteCopySource x hΓ hr sp₂ hs hm⟩
    else match sp₂, hs with
      | .alias .., hs => absurd rfl hs
      | .loc (.root ..), hs => absurd rfl hs
      | .loc (.field b f hf), hs =>
        if hb : b.isSimple = true then ⟨_, .storageFieldReadStoreRoot x hΓ hr b hb f hf hm⟩
        else (Hole.copy (.root x hΓ hr) hm).unfoldStep m (.field b f hf)
          (by simp [SPath.isBindable, not_simple hb])
      | .loc (.index it b i), hs =>
        if hbi : b.isSimple = true ∧ i.isSimple = true then
          match it, b, i, hbi with
          | .map, b, .simple ie, hbi => ⟨_, .storageIndexReadMappingStoreRoot x hΓ hr b hbi.1 ie hm⟩
          | .arr, b, .simple ie, hbi => ⟨_, .storageIndexReadArrayStoreRoot x hΓ hr b hbi.1 ie hm⟩
        else (Hole.copy (.root x hΓ hr) hm).unfoldStep m (.index it b i) (by simpa [SPath.isBindable] using hbi)
  -- a member
  | .field b f hf, .val (.ternary c a d) => ternaryStep m (.store (.field b f hf)) c a d
  | .field b f hf, .val e =>
    if hb : b.isSimple = true then
      match e with
      | .simple a => ⟨_, .storageFieldWriteSave b hb f hf a⟩
      | .read l => ⟨_, .fieldWriteValueRhsCapture b hb f hf (.read l) rfl _ (freshName_isFresh C Γ "se")⟩
      | .binop op hop hq a c =>
        ⟨_, .fieldWriteValueRhsCapture b hb f hf (.binop op hop hq a c) rfl _ (freshName_isFresh C Γ "se")⟩
      | .unop op hop hq a =>
        ⟨_, .fieldWriteValueRhsCapture b hb f hf (.unop op hop hq a) rfl _ (freshName_isFresh C Γ "se")⟩
      | .ternary c a d => ternaryStep m (.store (.field b f hf)) c a d
    else ⟨_, .storageFieldWrite_unfold_leftFst b (not_simple hb) f hf e _ _
      (freshName_isFresh C Γ "se") (freshName_isFresh C _ "sp")⟩
  | .field b f hf, .copy src hm =>
    if hb : b.isSimple = true then
      copyStep m (.field b f hf) rfl hm src fun hs => ⟨_, .storageFieldWriteCopySource b hb f hf src hs hm⟩
    else ⟨_, .storageFieldWriteStorageRef_unfold_leftFst b (not_simple hb) f hf src hm _
      (freshName_isFresh C Γ "sp")⟩
  -- an entry
  | .index it b i, .val (.ternary c a d) => ternaryStep m (.store (.index it b i)) c a d
  | .index it b i, .val e =>
    if hb : b.isSimple = true then
      match i with
      | .simple ie =>
        match e with
        | .simple a =>
          match it, b, hb, ie, a with
          | .map, b, hb, ie, a => ⟨_, .storageIndexWriteMappingSave b hb ie a⟩
          | .arr, b, hb, ie, a => ⟨_, .storageIndexWriteArraySave b hb ie a⟩
        | .read l => ⟨_, .indexWriteValueRhsCapture it b hb ie (.read l) rfl _ (freshName_isFresh C Γ "se")⟩
        | .binop op hop hq a c =>
          ⟨_, .indexWriteValueRhsCapture it b hb ie (.binop op hop hq a c) rfl _ (freshName_isFresh C Γ "se")⟩
        | .unop op hop hq a =>
          ⟨_, .indexWriteValueRhsCapture it b hb ie (.unop op hop hq a) rfl _ (freshName_isFresh C Γ "se")⟩
        | .ternary c a d => ternaryStep m (.store (.index it b (.simple ie))) c a d
      | .read l => ⟨_, .storageIndexWriteNonSimpleIndexCapture it b hb (.read l) rfl e _ _
          (freshName_isFresh C Γ "se") (freshName_isFresh C _ "ie")⟩
      | .binop op hop hq a c => ⟨_, .storageIndexWriteNonSimpleIndexCapture it b hb (.binop op hop hq a c) rfl e _ _
          (freshName_isFresh C Γ "se") (freshName_isFresh C _ "ie")⟩
      | .unop op hop hq a => ⟨_, .storageIndexWriteNonSimpleIndexCapture it b hb (.unop op hop hq a) rfl e _ _
          (freshName_isFresh C Γ "se") (freshName_isFresh C _ "ie")⟩
      | .ternary c a d => ⟨_, .storageIndexWriteNonSimpleIndexCapture it b hb (.ternary c a d) rfl e _ _
          (freshName_isFresh C Γ "se") (freshName_isFresh C _ "ie")⟩
    else ⟨_, .storageIndexWrite_unfold_leftFst it b (not_simple hb) i e _ _ _
      (freshName_isFresh C Γ "se") (freshName_isFresh C _ "sp") (freshName_isFresh C _ "ie")⟩
  | .index it b i, .copy src hm =>
    if hb : b.isSimple = true then
      if hi : i.isSimple = true then
        match i, hi with
        | .simple ie, _ =>
          copyStep m (.index it b (.simple ie)) rfl hm src fun hs =>
            match it, b, hb, ie with
            | .map, b, hb, ie => ⟨_, .storageIndexWriteMappingCopySource b hb ie src hs hm⟩
            | .arr, b, hb, ie => ⟨_, .storageIndexWriteArrayCopySource b hb ie src hs hm⟩
      else ⟨_, .storageIndexWriteStorageRefNonSimpleIndexCapture it b hb i (not_simple hi) src hm _
        (freshName_isFresh C Γ "ie")⟩
    else ⟨_, .storageIndexWriteStorageRef_unfold_leftFst it b (not_simple hb) i src hm _ _
      (freshName_isFresh C Γ "sp") (freshName_isFresh C _ "ie")⟩

/-- An alias rebound. -/
def rebindStep {Γ : Ctx} {R : RefTy} (x : Name) (h : lookupBy x Γ = some (.path (.ref R)))
    (p : SPath C Γ (.ref R)) : Step C m (.rebind x h p) :=
  if hs : p.isSimple = true then ⟨_, .storageLocalRootRebind x h p hs⟩
  else match p, hs with
    | .alias .., hs => absurd rfl hs
    | .loc (.root ..), hs => absurd rfl hs
    | .loc (.field b f hf), _ =>
      if hb : b.isSimple = true then ⟨_, .storageFieldReadBindLocalRoot x h b hb f hf⟩
      else (Hole.rebind x h).unfoldStep m (.field b f hf) (by simp [SPath.isBindable, not_simple hb])
    | .loc (.index it b i), _ =>
      if hbi : b.isSimple = true ∧ i.isSimple = true then
        match it, b, i, hbi with
        | .map, b, .simple ie, hbi => ⟨_, .storageIndexReadMappingBindLocalRoot x h b hbi.1 ie⟩
        | .arr, b, .simple ie, hbi => ⟨_, .storageIndexReadArrayBindLocalRoot x h b hbi.1 ie⟩
      else (Hole.rebind x h).unfoldStep m (.index it b i) (by simpa [SPath.isBindable] using hbi)

/-- `v = a && e` and `v = a || e`, with `e` not simple: only `bool` operands
reach here. -/
def shortCircuitStep {Γ : Ctx} {p q : PrimTy} (x : Name) (op : BinOp) (hop : op.accepts p = true)
    (hq : op.ret p = q) (hsc : op.shortCircuits = true) (h : lookupBy x Γ = some (.stack (.prim q)))
    (a : Simple C Γ p) (e : Val C Γ p) (he : e.isSimple = false) :
    Step C m (.assignLocal x h (.binop op hop hq (.simple a) e)) :=
  match p, q, op, hop, hq, hsc, h, a, e, he with
  | .bool, .bool, .and, hop, hq, _, h, a, e, he => ⟨_, .logicalAndShortCircuitRhs hop hq x h a e he⟩
  | .bool, .bool, .or, hop, hq, _, h, a, e, he => ⟨_, .logicalOrShortCircuitRhs hop hq x h a e he⟩
  | .bool, .uint, .and, _, hq, _, _, _, _, _ | .bool, .int, .and, _, hq, _, _, _, _, _
  | .bool, .uint, .or, _, hq, _, _, _, _, _ | .bool, .int, .or, _, hq, _, _, _, _, _ =>
    absurd hq (by decide)
  | .uint, _, .and, hop, _, _, _, _, _, _ | .int, _, .and, hop, _, _, _, _, _, _
  | .uint, _, .or, hop, _, _, _, _, _, _ | .int, _, .or, hop, _, _, _, _, _, _ =>
    absurd hop (by decide)
  | _, _, .add, _, _, hsc, _, _, _, _ | _, _, .sub, _, _, hsc, _, _, _, _
  | _, _, .mul, _, _, hsc, _, _, _, _ | _, _, .pow, _, _, hsc, _, _, _, _
  | _, _, .div, _, _, hsc, _, _, _, _ | _, _, .mod, _, _, hsc, _, _, _, _
  | _, _, .lt, _, _, hsc, _, _, _, _ | _, _, .gt, _, _, hsc, _, _, _, _
  | _, _, .le, _, _, hsc, _, _, _, _ | _, _, .ge, _, _, hsc, _, _, _, _
  | _, _, .eqB, _, _, hsc, _, _, _, _ | _, _, .neB, _, _, hsc, _, _, _, _ => absurd hsc (by decide)

/-- `v = se ⊕ nse`: short-circuit, or capture the right operand. -/
def binopRightStep {Γ : Ctx} {p q : PrimTy} (x : Name) (op : BinOp) (hop : op.accepts p = true)
    (hq : op.ret p = q) (h : lookupBy x Γ = some (.stack (.prim q))) (a : Simple C Γ p)
    (e : Val C Γ p) (he : e.isSimple = false) :
    Step C m (.assignLocal x h (.binop op hop hq (.simple a) e)) :=
  if hsc : op.shortCircuits = true then shortCircuitStep m x op hop hq hsc h a e he
  else ⟨_, .binopUnfoldRight op hop hq (not_simple hsc) x h a e he _ (freshName_isFresh C Γ "se")⟩

/-- A local assigned. -/
def localStep {Γ : Ctx} {p : PrimTy} (x : Name) (h : lookupBy x Γ = some (.stack (.prim p))) :
    (v : Val C Γ p) → Step C m (.assignLocal x h v)
  | .simple a => ⟨_, .localValueAssign x h a⟩
  | .read (.root r hΓ hr) => ⟨_, .storageRootReadSelect x h r hΓ hr⟩
  | .read (.field b f hf) =>
    if hb : b.isSimple = true then ⟨_, .storageFieldReadFind x h b hb f hf⟩
    else (Hole.local x h).unfoldStep m (.field b f hf) (by simp [SPath.isBindable, not_simple hb])
  | .read (.index it b i) =>
    if hbi : b.isSimple = true ∧ i.isSimple = true then
      match it, b, i, hbi with
      | .map, b, .simple ie, hbi => ⟨_, .storageIndexReadMappingFind x h b hbi.1 ie⟩
      | .arr, b, .simple ie, hbi => ⟨_, .storageIndexReadArrayFind x h b hbi.1 ie⟩
    else (Hole.local x h).unfoldStep m (.index it b i) (by simpa [SPath.isBindable] using hbi)
  | .binop op hop hq a e =>
    match a with
    | .simple a =>
      match e with
      | .simple c => ⟨_, .binopAssignment op hop hq x h a c⟩
      | .read l => binopRightStep m x op hop hq h a (.read l) rfl
      | .binop op' hop' hq' a' c' => binopRightStep m x op hop hq h a (.binop op' hop' hq' a' c') rfl
      | .unop op' hop' hq' a' => binopRightStep m x op hop hq h a (.unop op' hop' hq' a') rfl
      | .ternary c' a' d' => binopRightStep m x op hop hq h a (.ternary c' a' d') rfl
    | .read l => ⟨_, .binopUnfoldLeft op hop hq x h (.read l) rfl e _ (freshName_isFresh C Γ "se")⟩
    | .binop op' hop' hq' a' c' =>
      ⟨_, .binopUnfoldLeft op hop hq x h (.binop op' hop' hq' a' c') rfl e _ (freshName_isFresh C Γ "se")⟩
    | .unop op' hop' hq' a' => ⟨_, .binopUnfoldLeft op hop hq x h (.unop op' hop' hq' a') rfl e _ (freshName_isFresh C Γ "se")⟩
    | .ternary c' a' d' => ⟨_, .binopUnfoldLeft op hop hq x h (.ternary c' a' d') rfl e _ (freshName_isFresh C Γ "se")⟩
  | .unop op hop hq a =>
    match a with
    | .simple a => ⟨_, .unopAssignment op hop hq x h a⟩
    | .read l => ⟨_, .unopCapture op hop hq x h (.read l) rfl _ (freshName_isFresh C Γ "se")⟩
    | .binop op' hop' hq' a' c' => ⟨_, .unopCapture op hop hq x h (.binop op' hop' hq' a' c') rfl _ (freshName_isFresh C Γ "se")⟩
    | .unop op' hop' hq' a' => ⟨_, .unopCapture op hop hq x h (.unop op' hop' hq' a') rfl _ (freshName_isFresh C Γ "se")⟩
    | .ternary c' a' d' => ⟨_, .unopCapture op hop hq x h (.ternary c' a' d') rfl _ (freshName_isFresh C Γ "se")⟩
  | .ternary c a d => ternaryStep m (.local x h) c a d

/-- A delete. -/
def deleteStep {Γ : Ctx} {T : Ty} : (l : Loc C Γ T) → Step C m (.delete l)
  | .root r hΓ hr => ⟨_, .storageRootDelete r hΓ hr⟩
  | .field b f hf =>
    if hb : b.isSimple = true then ⟨_, .storageFieldDelete b hb f hf⟩
    else ⟨_, .storageFieldDelete_unfold_leftFst b (not_simple hb) f hf _ (freshName_isFresh C Γ "sp")⟩
  | .index it b i =>
    if hb : b.isSimple = true then
      match i with
      | .simple ie => ⟨_, .storageIndexDelete it b hb ie⟩
      | .read l => ⟨_, .storageIndexDeleteNonSimpleIndexCapture it b hb (.read l) rfl _ (freshName_isFresh C Γ "ie")⟩
      | .binop op hop hq a c =>
        ⟨_, .storageIndexDeleteNonSimpleIndexCapture it b hb (.binop op hop hq a c) rfl _ (freshName_isFresh C Γ "ie")⟩
      | .unop op hop hq a =>
        ⟨_, .storageIndexDeleteNonSimpleIndexCapture it b hb (.unop op hop hq a) rfl _ (freshName_isFresh C Γ "ie")⟩
      | .ternary c a d =>
        ⟨_, .storageIndexDeleteNonSimpleIndexCapture it b hb (.ternary c a d) rfl _ (freshName_isFresh C Γ "ie")⟩
    else ⟨_, .storageIndexDelete_unfold_leftFst it b (not_simple hb) i _ (freshName_isFresh C Γ "sp")⟩

/-- The rule for a compound assignment: the source first (capture a
non-simple one), then the target (capture a non-simple receiver). -/
def opStep {Γ : Ctx} {p : PrimTy} (op : BinOp) (hop : op.hasCompoundAssign = true)
    (hp : p.isNumeric = true) (l : OpLoc C Γ p) : (r : Val C Γ p) → Step C m (.opAssign op hop hp l r)
  | .read l' => ⟨_, .compoundAssignValueRhsCapture op hop hp l (.read l') rfl _ (freshName_isFresh C Γ "se")⟩
  | .binop op' hop' hq' a b =>
    ⟨_, .compoundAssignValueRhsCapture op hop hp l (.binop op' hop' hq' a b) rfl _ (freshName_isFresh C Γ "se")⟩
  | .unop op' hop' hq' a =>
    ⟨_, .compoundAssignValueRhsCapture op hop hp l (.unop op' hop' hq' a) rfl _ (freshName_isFresh C Γ "se")⟩
  | .ternary c a b =>
    ⟨_, .compoundAssignValueRhsCapture op hop hp l (.ternary c a b) rfl _ (freshName_isFresh C Γ "se")⟩
  | .simple se =>
    match l with
    | .local x h => ⟨_, .localOpAssign op hop hp x h se⟩
    | .root r hΓ h => ⟨_, .storageRootOpAssign op hop hp r hΓ h se⟩
    | .field b f h =>
      if hb : b.isSimple = true then ⟨_, .storageFieldOpAssign op hop hp b hb f h se⟩
      else ⟨_, .storageFieldOpAssignUnfoldLeftFst op hop hp b (not_simple hb) f h se _
        (freshName_isFresh C Γ "sp")⟩
    | .index it b ie =>
      if hb : b.isSimple = true then
        match it, b, ie, hb with
        | .map, b, ie, hb => ⟨_, .storageIndexMappingOpAssign op hop hp b hb ie se⟩
        | .arr, b, ie, hb => ⟨_, .storageIndexArrayOpAssign op hop hp b hb ie se⟩
      else ⟨_, .storageIndexOpAssignUnfoldLeftFst op hop hp it b (not_simple hb) ie se _
        (freshName_isFresh C Γ "sp")⟩

/-- The rule for `l++;`: capture a non-simple receiver. -/
def incStep {Γ : Ctx} {p : PrimTy} (op : IncDec) (hp : p.isNumeric = true) :
    (l : OpLoc C Γ p) → Step C m (.incDec op hp l)
  | .local x h => ⟨_, .localIncrement op hp x h⟩
  | .root r hΓ h => ⟨_, .storageRootIncrement op hp r hΓ h⟩
  | .field b f h =>
    if hb : b.isSimple = true then ⟨_, .storageFieldIncrement op hp b hb f h⟩
    else ⟨_, .storageFieldIncrementUnfoldLeftFst op hp b (not_simple hb) f h _ (freshName_isFresh C Γ "sp")⟩
  | .index it b ie =>
    if hb : b.isSimple = true then ⟨_, .storageIndexIncrement op hp it b hb ie⟩
    else ⟨_, .storageIndexIncrementUnfoldLeftFst op hp it b (not_simple hb) ie _
      (freshName_isFresh C Γ "sp")⟩

/-- The rule for `y = l++;`, whose receiver is simple. -/
def assignIncStep {Γ : Ctx} {p : PrimTy} (y : Name) (hy : lookupBy y Γ = some (.stack (.prim p)))
    (op : IncDec) (hp : p.isNumeric = true) :
    (l : OpLoc C Γ p) → (hs : l.recvSimple = true) → Step C m (.assignIncDec y hy op hp l hs)
  | .local x h, rfl => ⟨_, .localAssignIncrement y hy op hp x h⟩
  | .root r hΓ h, rfl => ⟨_, .storageRootIncrementAssignment y hy op hp r hΓ h⟩
  | .field b f h, hs => ⟨_, .storageFieldIncrementAssignment y hy op hp b f h hs⟩
  | .index it b ie, hs => ⟨_, .storageIndexIncrementAssignment y hy op hp it b ie hs⟩

/-- **The rule for a statement**, under the modality `m`.  Total: every
statement of the kernel has one. -/
def Stmt.step {Γ Γ' : Ctx} : (s : Stmt C Γ Γ') → Step C m s
  | .assign l r => assignStep m l r
  | .rebind x h p => rebindStep m x h p
  | .assignLocal x h v => localStep m x h v
  | .declLocal _ x hx init =>
    match init with
    | none => ⟨_, .valueDeclSkip x hx⟩
    | some e => ⟨_, .localValueDeclInitDrop x hx e⟩
  | .declStorage c R x hx p =>
    if hb : p.isBindable = true then ⟨_, .storageLocalDeclInitDrop c x hx p hb⟩
    else match p, hb with
      | .alias .., hb => absurd rfl hb
      | .loc l, hb => (Hole.decl c R x hx).unfoldStep m l (not_simple hb)
  | .opAssign op hop hp l r => opStep m op hop hp l r
  | .incDec op hp l => incStep m op hp l
  | .assignIncDec y hy op hp l hs => assignIncStep m y hy op hp l hs
  | .delete l => deleteStep m l
  | .ite c thn els => ⟨_, .ifElseSplit c thn els⟩
  | .require c => ⟨_, .requireSimple c⟩
  | .assert c => ⟨_, .assertSimple c⟩
  | .revert =>
    match m with
    | .box => ⟨_, .revertBox rfl⟩
    | .diamond => ⟨_, .revertDiamond rfl⟩

/-- **Completeness**: under either modality, every statement of the kernel
has a rule.  No hypothesis, no residue: `uint x = people[i].age;`,
`alice = bob;`, `delete folks[i + 1];` each have one, and so does anything
else `ksol` writes. -/
theorem Stmt.complete {Γ Γ' : Ctx} (s : Stmt C Γ Γ') : ∃ pr, Nonempty (Taclet C m s pr) :=
  ⟨(s.step m).1, ⟨(s.step m).2⟩⟩

/-! ## Printing a step -/

section Print

variable {C : Contract}

def Upd.toStr {Γ : Ctx} : Upd C Γ → String
  | .save l v => s!"\{ storage := save(storage, {l.toStr}, {v.toStr}) }"
  | .delAt l => s!"\{ storage := delAt(storage, {l.toStr}) }"
  | .bind x e => s!"\{ {x} := {e.toStr true} }"
  | .bindPath x p => s!"\{ {x} := {p.toStr} }"
  | .opSave op l se =>
    match l with
    | .local x _ => s!"\{ {x} := {x} {BinOp.sym op} {se.toStr} }"
    | l => s!"\{ storage := save(storage, {l.toStr}, {l.toStr} {BinOp.sym op} {se.toStr}) }"
  | .bump op l => s!"\{ bump({IncDec.show op l.toStr}) }"
  | .bumpBind x op l => s!"\{ bump({IncDec.show op l.toStr}) || {x} := {IncDec.show op l.toStr} }"

def Premise.toStr {Γ Γ' : Ctx} : Premise C Γ Γ' → String
  | .update U => s!"{U.toStr} ⟨[ ]⟩"
  | .unfold _ P _ => s!"⟨[ {P.toStr} ]⟩"
  | .split c P Q => s!"{c.toStr} ⟹ ⟨[ {P.toStr} ]⟩ ; ¬{c.toStr} ⟹ ⟨[ {Q.toStr} ]⟩"
  | .done b => toString b

/-- The premise the rule for the first statement of `P` leaves. -/
def Prog.firstStep (m : Modality) {Γ Γ' : Ctx} : Prog C Γ Γ' → String
  | .nil => "(no statement)"
  | .cons s _ => (s.step m).1.toStr

end Print


section Examples

local instance : InContract := ⟨StandardExample⟩

def exSave := ksol{ alice.age = 10; }
def exLeftFst := ksol{ folks[1].age = 10; }
def exDecl := ksol{ Person storage p = people[1 + 1]; }
def exDelete := ksol{ delete folks[1 + 1]; }

/-- info: "{ storage := save(storage, alice.age, 10) } ⟨[ ]⟩" -/
#guard_msgs in #eval exSave.firstStep .box

/-- info: "⟨[ uint se = 10; Person storage sp = folks[1]; sp.age = se; ]⟩" -/
#guard_msgs in #eval exLeftFst.firstStep .box

/-- info: "⟨[ uint ie = 1 + 1; Person storage p = people[ie]; ]⟩" -/
#guard_msgs in #eval exDecl.firstStep .diamond

/-- info: "true" -/
#guard_msgs in #eval (ksol{ revert(); }).firstStep .box

/-- `delete folks[1 + 1];` has a rule, as every statement does. -/
example : match exDelete with
    | .cons s .nil => ∃ pr, Nonempty (Taclet StandardExample .diamond s pr)
    | _ => False :=
  Stmt.complete _ _

end Examples

end Kernel
end Solidity
