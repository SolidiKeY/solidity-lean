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

/-- A memory read, rebind, declaration or reference write from a location
that is not bindable: capture its receiver or its index. -/
def MHole.unfoldStep {Γ Γ' : Ctx} {T : Ty} (k : MHole C Γ Γ' T) :
    (l : MLoc C Γ T) → (MPath.loc l).isBindable = false → Step C m (k.fill l)
  | .field b f hf, h =>
    if hb : b.isSimple = true then absurd h (by simp [MPath.isBindable, hb])
    else ⟨_, .memoryFieldRead_unfold_rightFst k b (not_simple hb) f hf _ (freshName_isFresh C Γ' "mv")⟩
  | .index b i, h =>
    if hb : b.isSimple = true then
      if hi : i.isSimple = true then absurd h (by simp [MPath.isBindable, hb, hi])
      else ⟨_, .memoryIndexRead_unfold_rightSndIndex k b hb i (not_simple hi) _
        (freshName_isFresh C Γ' "ie")⟩
    else ⟨_, .memoryIndexRead_unfold_rightFst k b (not_simple hb) i _ (freshName_isFresh C Γ' "mv")⟩

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
    | .mem l => ⟨_, .ternaryToIfMemory l c a b⟩
  | .read l => ⟨_, .ternaryCaptureCond k (.read l) rfl a b _ (freshName_isFresh C Γ "se")⟩
  | .binop op hop hq x y => ⟨_, .ternaryCaptureCond k (.binop op hop hq x y) rfl a b _ (freshName_isFresh C Γ "se")⟩
  | .unop op hop hq x => ⟨_, .ternaryCaptureCond k (.unop op hop hq x) rfl a b _ (freshName_isFresh C Γ "se")⟩
  | .ternary c' x y => ⟨_, .ternaryCaptureCond k (.ternary c' x y) rfl a b _ (freshName_isFresh C Γ "se")⟩
  | .readMem ml => ⟨_, .ternaryCaptureCond k (.readMem ml) rfl a b _ (freshName_isFresh C Γ "se")⟩

/-- `nsp.fld = e`: the receiver captured, a conditional lowered first. -/
def fieldLeftFstStep {Γ : Ctx} {s : Name} {p : PrimTy} (nsp : SPath C Γ (.struct s))
    (hn : nsp.isSimple = false) (f : Name) (hf : C.fieldType s f = some (.prim p)) (e : Val C Γ p) :
    Step C m (.assign (.field nsp f hf) (.val e)) :=
  if hnt : e.notTernary = true then
    ⟨_, .storageFieldWrite_unfold_leftFst nsp hn f hf e _ _ (freshName_isFresh C Γ "se")
      (freshName_isFresh C _ "sp") hnt⟩
  else
    match e, hnt with
    | .ternary c a d, _ => ternaryStep m (.store (.field nsp f hf)) c a d
    | .simple _, h | .read _, h | .binop .., h | .unop .., h | .readMem _, h => absurd rfl h

/-- `nsp[e1] = e2`: the receiver captured, a conditional lowered first. -/
def indexLeftFstStep {Γ : Ctx} {R₀ : RefTy} {kp p : PrimTy} (it : IndexTy R₀ kp (.prim p))
    (nsp : SPath C Γ (.ref R₀)) (hn : nsp.isSimple = false) (i : Val C Γ kp) (e : Val C Γ p) :
    Step C m (.assign (.index it nsp i) (.val e)) :=
  if hnt : e.notTernary = true then
    ⟨_, .storageIndexWrite_unfold_leftFst it nsp hn i e _ _ _ (freshName_isFresh C Γ "se")
      (freshName_isFresh C _ "sp") (freshName_isFresh C _ "ie") hnt⟩
  else
    match e, hnt with
    | .ternary c a d, _ => ternaryStep m (.store (.index it nsp i)) c a d
    | .simple _, h | .read _, h | .binop .., h | .unop .., h | .readMem _, h => absurd rfl h

/-- `sp[nse] = e`: the index captured, a conditional lowered first. -/
def indexCaptureStep {Γ : Ctx} {R₀ : RefTy} {kp p : PrimTy} (it : IndexTy R₀ kp (.prim p))
    (b : SPath C Γ (.ref R₀)) (hb : b.isSimple = true) (nse : Val C Γ kp) (hn : nse.isSimple = false)
    (e : Val C Γ p) : Step C m (.assign (.index it b nse) (.val e)) :=
  if hnt : e.notTernary = true then
    ⟨_, .storageIndexWriteNonSimpleIndexCapture it b hb nse hn e _ _ (freshName_isFresh C Γ "se")
      (freshName_isFresh C _ "ie") hnt⟩
  else
    match e, hnt with
    | .ternary c a d, _ => ternaryStep m (.store (.index it b nse)) c a d
    | .simple _, h | .read _, h | .binop .., h | .unop .., h | .readMem _, h => absurd rfl h

/-- A storage write. -/
def assignStep {Γ : Ctx} {T : Ty} : (l : Loc C Γ T) → (r : Src C Γ T) → Step C m (.assign l r)
  -- a state variable
  | .root x hΓ hr, .val (.simple a) => ⟨_, .storageRootWriteStore x hΓ hr a⟩
  | .root x hΓ hr, .val (.read l) =>
    ⟨_, .storageRootWriteValueRhsCapture x hΓ hr (.read l) rfl _ (freshName_isFresh C Γ "se") rfl⟩
  | .root x hΓ hr, .val (.binop op hop hq a b) =>
    ⟨_, .storageRootWriteValueRhsCapture x hΓ hr (.binop op hop hq a b) rfl _ (freshName_isFresh C Γ "se") rfl⟩
  | .root x hΓ hr, .val (.unop op hop hq a) =>
    ⟨_, .storageRootWriteValueRhsCapture x hΓ hr (.unop op hop hq a) rfl _ (freshName_isFresh C Γ "se") rfl⟩
  | .root x hΓ hr, .val (.ternary c a b) => ternaryStep m (.store (.root x hΓ hr)) c a b
  | .root x hΓ hr, .val (.readMem ml) =>
    ⟨_, .storageRootWriteValueRhsCapture x hΓ hr (.readMem ml) rfl _ (freshName_isFresh C Γ "se") rfl⟩
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
  | .field b f hf, .val e =>
    if hb : b.isSimple = true then
      match e with
      | .simple a => ⟨_, .storageFieldWriteSave b hb f hf a⟩
      | .read l => ⟨_, .fieldWriteValueRhsCapture b hb f hf (.read l) rfl _ (freshName_isFresh C Γ "se") rfl⟩
      | .binop op hop hq a c =>
        ⟨_, .fieldWriteValueRhsCapture b hb f hf (.binop op hop hq a c) rfl _ (freshName_isFresh C Γ "se") rfl⟩
      | .unop op hop hq a =>
        ⟨_, .fieldWriteValueRhsCapture b hb f hf (.unop op hop hq a) rfl _ (freshName_isFresh C Γ "se") rfl⟩
      | .ternary c a d => ternaryStep m (.store (.field b f hf)) c a d
      | .readMem ml => ⟨_, .fieldWriteValueRhsCapture b hb f hf (.readMem ml) rfl _ (freshName_isFresh C Γ "se") rfl⟩
    else fieldLeftFstStep m b (not_simple hb) f hf e
  | .field b f hf, .copy src hm =>
    if hb : b.isSimple = true then
      copyStep m (.field b f hf) rfl hm src fun hs => ⟨_, .storageFieldWriteCopySource b hb f hf src hs hm⟩
    else ⟨_, .storageFieldWriteStorageRef_unfold_leftFst b (not_simple hb) f hf src hm _
      (freshName_isFresh C Γ "sp")⟩
  -- an entry
  | .index it b i, .val e =>
    if hb : b.isSimple = true then
      match i with
      | .simple ie =>
        match e with
        | .simple a =>
          match it, b, hb, ie, a with
          | .map, b, hb, ie, a => ⟨_, .storageIndexWriteMappingSave b hb ie a⟩
          | .arr, b, hb, ie, a => ⟨_, .storageIndexWriteArraySave b hb ie a⟩
        | .read l => ⟨_, .indexWriteValueRhsCapture it b hb ie (.read l) rfl _ (freshName_isFresh C Γ "se") rfl⟩
        | .binop op hop hq a c =>
          ⟨_, .indexWriteValueRhsCapture it b hb ie (.binop op hop hq a c) rfl _ (freshName_isFresh C Γ "se") rfl⟩
        | .unop op hop hq a =>
          ⟨_, .indexWriteValueRhsCapture it b hb ie (.unop op hop hq a) rfl _ (freshName_isFresh C Γ "se") rfl⟩
        | .ternary c a d => ternaryStep m (.store (.index it b (.simple ie))) c a d
        | .readMem ml =>
          ⟨_, .indexWriteValueRhsCapture it b hb ie (.readMem ml) rfl _ (freshName_isFresh C Γ "se") rfl⟩
      | .read l => indexCaptureStep m it b hb (.read l) rfl e
      | .binop op hop hq a c => indexCaptureStep m it b hb (.binop op hop hq a c) rfl e
      | .unop op hop hq a => indexCaptureStep m it b hb (.unop op hop hq a) rfl e
      | .ternary c a d => indexCaptureStep m it b hb (.ternary c a d) rfl e
      | .readMem ml => indexCaptureStep m it b hb (.readMem ml) rfl e
    else indexLeftFstStep m it b (not_simple hb) i e
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
      | .readMem ml => binopRightStep m x op hop hq h a (.readMem ml) rfl
    | .read l => ⟨_, .binopUnfoldLeft op hop hq x h (.read l) rfl e _ (freshName_isFresh C Γ "se")⟩
    | .binop op' hop' hq' a' c' =>
      ⟨_, .binopUnfoldLeft op hop hq x h (.binop op' hop' hq' a' c') rfl e _ (freshName_isFresh C Γ "se")⟩
    | .unop op' hop' hq' a' => ⟨_, .binopUnfoldLeft op hop hq x h (.unop op' hop' hq' a') rfl e _ (freshName_isFresh C Γ "se")⟩
    | .ternary c' a' d' => ⟨_, .binopUnfoldLeft op hop hq x h (.ternary c' a' d') rfl e _ (freshName_isFresh C Γ "se")⟩
    | .readMem ml => ⟨_, .binopUnfoldLeft op hop hq x h (.readMem ml) rfl e _ (freshName_isFresh C Γ "se")⟩
  | .unop op hop hq a =>
    match a with
    | .simple a => ⟨_, .unopAssignment op hop hq x h a⟩
    | .read l => ⟨_, .unopCapture op hop hq x h (.read l) rfl _ (freshName_isFresh C Γ "se")⟩
    | .binop op' hop' hq' a' c' => ⟨_, .unopCapture op hop hq x h (.binop op' hop' hq' a' c') rfl _ (freshName_isFresh C Γ "se")⟩
    | .unop op' hop' hq' a' => ⟨_, .unopCapture op hop hq x h (.unop op' hop' hq' a') rfl _ (freshName_isFresh C Γ "se")⟩
    | .ternary c' a' d' => ⟨_, .unopCapture op hop hq x h (.ternary c' a' d') rfl _ (freshName_isFresh C Γ "se")⟩
    | .readMem ml => ⟨_, .unopCapture op hop hq x h (.readMem ml) rfl _ (freshName_isFresh C Γ "se")⟩
  | .ternary c a d => ternaryStep m (.local x h) c a d
  | .readMem l =>
    if hl : (MPath.loc l).isBindable = true then
      match l, hl with
      | .field b f hf, hl => ⟨_, .memoryFieldReadHeap x h b hl f hf⟩
      | .index b i, hl =>
        match i, hl with
        | .simple ie, hl =>
          ⟨_, .memoryIndexReadHeap x h b (by simpa [MPath.isBindable, Val.isSimple] using hl) ie⟩
        | .read _, hl | .binop .., hl | .unop .., hl | .ternary .., hl | .readMem _, hl =>
          absurd hl (by simp [MPath.isBindable, Val.isSimple])
    else (MHole.local x h).unfoldStep m l (not_simple hl)

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
      | .readMem ml =>
        ⟨_, .storageIndexDeleteNonSimpleIndexCapture it b hb (.readMem ml) rfl _ (freshName_isFresh C Γ "ie")⟩
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
  | .readMem ml =>
    ⟨_, .compoundAssignValueRhsCapture op hop hp l (.readMem ml) rfl _ (freshName_isFresh C Γ "se")⟩
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
    | .mfield b f h =>
      if hb : b.isSimple = true then ⟨_, .memoryFieldOpAssign op hop hp b hb f h se⟩
      else ⟨_, .memoryFieldOpAssignUnfoldLeftFst op hop hp b (not_simple hb) f h se _
        (freshName_isFresh C Γ "mv")⟩
    | .mindex b ie =>
      if hb : b.isSimple = true then ⟨_, .memoryIndexArrayOpAssign op hop hp b hb ie se⟩
      else ⟨_, .memoryIndexOpAssignUnfoldLeftFst op hop hp b (not_simple hb) ie se _
        (freshName_isFresh C Γ "mv")⟩

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
  | .mfield b f h =>
    if hb : b.isSimple = true then ⟨_, .memoryFieldIncrement op hp b hb f h⟩
    else ⟨_, .memoryFieldIncrementUnfoldLeftFst op hp b (not_simple hb) f h _ (freshName_isFresh C Γ "mv")⟩
  | .mindex b ie =>
    if hb : b.isSimple = true then ⟨_, .memoryIndexArrayIncrement op hp b hb ie⟩
    else ⟨_, .memoryIndexIncrementUnfoldLeftFst op hp b (not_simple hb) ie _ (freshName_isFresh C Γ "mv")⟩

/-- The rule for `y = l++;`, whose receiver is simple. -/
def assignIncStep {Γ : Ctx} {p : PrimTy} (y : Name) (hy : lookupBy y Γ = some (.stack (.prim p)))
    (op : IncDec) (hp : p.isNumeric = true) :
    (l : OpLoc C Γ p) → (hs : l.recvSimple = true) → Step C m (.assignIncDec y hy op hp l hs)
  | .local x h, rfl => ⟨_, .localAssignIncrement y hy op hp x h⟩
  | .root r hΓ h, rfl => ⟨_, .storageRootIncrementAssignment y hy op hp r hΓ h⟩
  | .field b f h, hs => ⟨_, .storageFieldIncrementAssignment y hy op hp b f h hs⟩
  | .index it b ie, hs => ⟨_, .storageIndexIncrementAssignment y hy op hp it b ie hs⟩
  | .mfield b f h, hs => ⟨_, .memoryFieldIncrementAssignment y hy op hp b f h hs⟩
  | .mindex b ie, hs => ⟨_, .memoryIndexArrayIncrementAssignment y hy op hp b ie hs⟩

/-- The rule for a push: the receiver first, then the argument. -/
def pushStep {Γ : Ctx} {E : Ty} (b : SPath C Γ (.array E)) (v : Option (Src C Γ E))
    (hd : (v.isSome || E.defaultOkS) = true) : Step C m (.push b v hd) :=
  if hb : b.isSimple = true then
    match v with
    | none => ⟨_, .storagePushLengthSave b hb hd⟩
    | some r =>
      if hr : r.isSimple = true then
        match E, b, hb, r, hr, hd with
        | _, b, hb, .val (.simple se), _, hd => ⟨_, .storagePushValueSave b hb se hd⟩
        | _, b, hb, .copy sp₂ hm, hr, hd => ⟨_, .storagePushValueCopySource b hb sp₂ hr hm hd⟩
        | _, _, _, .val (.read _), hr, _ | _, _, _, .val (.binop ..), hr, _
        | _, _, _, .val (.unop ..), hr, _ | _, _, _, .val (.ternary ..), hr, _
        | _, _, _, .val (.readMem _), hr, _ =>
          absurd hr (by simp [Src.isSimple, Val.isSimple])
      else ⟨_, .storagePushValue_unfold_rightSndArgument b hb r (not_simple hr) _
        (freshName_isFresh C Γ "se") hd⟩
  else
    match v with
    | none => ⟨_, .storagePush_unfold_leftFstReceiver b (not_simple hb) _ (freshName_isFresh C Γ "sp") hd⟩
    | some e => ⟨_, .storagePushValue_unfold_leftFstReceiver b (not_simple hb) e _
      (freshName_isFresh C Γ "sp") hd⟩

/-- The rule for a pop. -/
def popStep {Γ : Ctx} {E : Ty} (b : SPath C Γ (.array E)) : Step C m (.pop b) :=
  if hb : b.isSimple = true then ⟨_, .storagePopSave b hb⟩
  else ⟨_, .storagePop_unfold_leftFstReceiver b (not_simple hb) _ (freshName_isFresh C Γ "sp")⟩

/-- The rule for a transfer: the receiver first, then the amount. -/
def transferStep {Γ : Ctx} : (r a : Val C Γ .uint) → Step C m (.transfer r a)
  | .simple r, .simple a => ⟨_, .transferNoCallback r a⟩
  | .simple r, .read l => ⟨_, .transfer_unfold_rightSndArgument r (.read l) rfl _ (freshName_isFresh C Γ "se")⟩
  | .simple r, .binop op h hq x y =>
    ⟨_, .transfer_unfold_rightSndArgument r (.binop op h hq x y) rfl _ (freshName_isFresh C Γ "se")⟩
  | .simple r, .unop op h hq x =>
    ⟨_, .transfer_unfold_rightSndArgument r (.unop op h hq x) rfl _ (freshName_isFresh C Γ "se")⟩
  | .simple r, .ternary c x y =>
    ⟨_, .transfer_unfold_rightSndArgument r (.ternary c x y) rfl _ (freshName_isFresh C Γ "se")⟩
  | .simple r, .readMem ml =>
    ⟨_, .transfer_unfold_rightSndArgument r (.readMem ml) rfl _ (freshName_isFresh C Γ "se")⟩
  | .read l, a => ⟨_, .transfer_unfold_leftFstReceiver (.read l) rfl a _ (freshName_isFresh C Γ "se")⟩
  | .binop op h hq x y, a =>
    ⟨_, .transfer_unfold_leftFstReceiver (.binop op h hq x y) rfl a _ (freshName_isFresh C Γ "se")⟩
  | .unop op h hq x, a => ⟨_, .transfer_unfold_leftFstReceiver (.unop op h hq x) rfl a _ (freshName_isFresh C Γ "se")⟩
  | .ternary c x y, a => ⟨_, .transfer_unfold_leftFstReceiver (.ternary c x y) rfl a _ (freshName_isFresh C Γ "se")⟩
  | .readMem ml, a => ⟨_, .transfer_unfold_leftFstReceiver (.readMem ml) rfl a _ (freshName_isFresh C Γ "se")⟩

/-- A memory local rebound. -/
def rebindMemStep {Γ : Ctx} {R : RefTy} (x : Name) (h : lookupBy x Γ = some (.mem (.ref R))) :
    (r : MRhs C Γ R) → Step C m (.rebindMem x h r)
  | .alias (.var y hy) => ⟨_, .memoryRootAlias x h y hy⟩
  | .alias (.loc l) =>
    if hl : (MPath.loc l).isBindable = true then
      match l, hl with
      | .field b f hf, hl => ⟨_, .memoryFieldReadAliasRoot x h b hl f hf⟩
      | .index b i, hl =>
        match i, hl with
        | .simple ie, hl =>
          ⟨_, .memoryIndexReadAliasRoot x h b (by simpa [MPath.isBindable, Val.isSimple] using hl) ie⟩
        | .read _, hl | .binop .., hl | .unop .., hl | .ternary .., hl | .readMem _, hl =>
          absurd hl (by simp [MPath.isBindable, Val.isSimple])
    else (MHole.rebind x h).unfoldStep m l (not_simple hl)
  | .copy p hm =>
    if hs : p.isSimple = true then ⟨_, .memoryStorageCopy x h p hs hm⟩
    else ⟨_, .memoryStorageCopyUnfold x h p (not_simple hs) hm _ (freshName_isFresh C Γ "sp")⟩

/-- A memory local declared. -/
def declMemStep {Γ : Ctx} (R : RefTy) (x : Name) (hx : isFresh C Γ x = true) :
    (init : Option (MRhs C Γ R)) → (hd : (init.isSome || (Ty.ref R).defaultOkS) = true) →
      Step C m (.declMem R x hx init hd)
  | none, hd => ⟨_, .memoryDeclFreshAlloc R x hx hd⟩
  | some (.alias p), hd =>
    if hp : p.isBindable = true then ⟨_, .memoryLocalDeclInitDrop R x hx p hp hd⟩
    else
      match p, hp with
      | .var .., hp => absurd rfl hp
      | .loc l, hp => (MHole.decl R x hx).unfoldStep m l (not_simple hp)
  | some (.copy p hm), hd =>
    if hs : p.isSimple = true then ⟨_, .storageToMemoryDeclCopyRoot R x hx p hs hm hd⟩
    else
      match p, hs with
      | .loc (.field b f hf), hs =>
        if hb : b.isSimple = true then ⟨_, .storageToMemoryDeclCopyField R x hx b hb f hf hm hd⟩
        else ⟨_, .storageToMemoryDeclUnfoldRightFst R x hx (.loc (.field b f hf)) (not_simple hs)
          (fun _ _ _ _ h => by cases h; exact not_simple hb) hm _ (freshName_isFresh C _ "sp") hd⟩
      | .loc (.index it b i), hs =>
        ⟨_, .storageToMemoryDeclUnfoldRightFst R x hx (.loc (.index it b i)) (not_simple hs)
          (fun _ _ _ _ h => by cases h) hm _ (freshName_isFresh C _ "sp") hd⟩
      | .alias .., hs | .loc (.root ..), hs => absurd rfl hs

/-- A memory location written with a value: `k` for a value that is not a
conditional, which is lowered first. -/
def memValStep {Γ : Ctx} {p : PrimTy} (l : MLoc C Γ (.prim p)) (v : Val C Γ p)
    (k : v.notTernary = true → Step C m (.assignMem l (.val v))) : Step C m (.assignMem l (.val v)) :=
  if hnt : v.notTernary = true then k hnt
  else
    match v, hnt with
    | .ternary c a d, _ => ternaryStep m (.mem l) c a d
    | .simple _, h | .read _, h | .binop .., h | .unop .., h | .readMem _, h => absurd rfl h

/-- A memory location written. -/
def assignMemStep {Γ : Ctx} {T : Ty} : (l : MLoc C Γ T) → (r : MSrc C Γ T) → Step C m (.assignMem l r)
  | .field b f hf, .val v =>
    if hb : b.isSimple = true then
      if hv : v.isSimple = true then
        match v, hv with
        | .simple se, _ => ⟨_, .memoryFieldWriteStore b hb f hf se⟩
        | .read _, hv | .binop .., hv | .unop .., hv | .ternary .., hv | .readMem _, hv =>
          absurd hv (by simp [Val.isSimple])
      else memValStep m (.field b f hf) v fun hnt =>
        ⟨_, .memoryFieldWriteUnfoldSource b hb f hf v (not_simple hv) _ (freshName_isFresh C Γ "se") hnt⟩
    else memValStep m (.field b f hf) v fun hnt =>
      ⟨_, .memoryFieldWrite_unfold_leftFst b (not_simple hb) f hf v _ _ (freshName_isFresh C Γ "se")
        (freshName_isFresh C _ "mv") hnt⟩
  | .index b i, .val v =>
    if hb : b.isSimple = true then
      if hi : i.isSimple = true then
        match i, hi with
        | .simple ie, _ =>
          if hv : v.isSimple = true then
            match v, hv with
            | .simple se, _ => ⟨_, .memoryIndexWriteStore b hb ie se⟩
            | .read _, hv | .binop .., hv | .unop .., hv | .ternary .., hv | .readMem _, hv =>
              absurd hv (by simp [Val.isSimple])
          else memValStep m (.index b (.simple ie)) v fun hnt =>
            ⟨_, .memoryIndexWriteUnfoldSource b hb ie v (not_simple hv) _ (freshName_isFresh C Γ "se") hnt⟩
        | .read _, hi | .binop .., hi | .unop .., hi | .ternary .., hi | .readMem _, hi =>
          absurd hi (by simp [Val.isSimple])
      else memValStep m (.index b i) v fun hnt =>
        ⟨_, .memoryIndexWriteNonSimpleIndexCapture b hb i (not_simple hi) v _ _
          (freshName_isFresh C Γ "se") (freshName_isFresh C _ "ie") hnt⟩
    else memValStep m (.index b i) v fun hnt =>
      ⟨_, .memoryIndexWrite_unfold_leftFst b (not_simple hb) i v _ _ (freshName_isFresh C Γ "se")
        (freshName_isFresh C _ "mv") hnt⟩
  | l, .ref src =>
    if hs : src.isBindable = true then
      match l with
      | .field b f hf =>
        if hb : b.isSimple = true then ⟨_, .memoryFieldWriteCopy b hb f hf src hs⟩
        else ⟨_, .memoryFieldWriteMemRef_unfold_leftFst b (not_simple hb) f hf src hs _
          (freshName_isFresh C Γ "mv")⟩
      | .index b i =>
        if hb : b.isSimple = true then
          if hi : i.isSimple = true then
            match i, hi with
            | .simple ie, _ => ⟨_, .memoryIndexWriteCopy b hb ie src hs⟩
            | .read _, hi | .binop .., hi | .unop .., hi | .ternary .., hi | .readMem _, hi =>
              absurd hi (by simp [Val.isSimple])
          else ⟨_, .memoryIndexWriteMemRefNonSimpleIndexCapture b hb i (not_simple hi) src hs _
            (freshName_isFresh C Γ "ie")⟩
        else ⟨_, .memoryIndexWriteMemRef_unfold_leftFst b (not_simple hb) i src hs _
          (freshName_isFresh C Γ "mv")⟩
    else
      match src, hs with
      | .var .., hs => absurd rfl hs
      | .loc sl, hs => (MHole.write l).unfoldStep m sl (not_simple hs)

/-- A storage location written from memory. -/
def assignFromMemStep {Γ : Ctx} {R : RefTy} :
    (l : Loc C Γ (.ref R)) → (p : MPath C Γ (.ref R)) → Step C m (.assignFromMem l p)
  | .root r hΓ hr, p => ⟨_, .memoryToStorageStoreRoot r hΓ hr p⟩
  | .field b f hf, p =>
    if hb : b.isSimple = true then
      match p with
      | .var x hx => ⟨_, .memoryToStorageFieldCopyRoot b hb f hf x hx⟩
      | .loc ml => ⟨_, .memoryToStorageFieldCopyField b hb f hf ml⟩
    else ⟨_, .memoryToStorageField_unfold_leftFst b (not_simple hb) f hf p _ (freshName_isFresh C Γ "sp")⟩
  | .index it b i, p =>
    if hb : b.isSimple = true then
      if hi : i.isSimple = true then
        match it, b, hb, i, hi with
        | .map, b, hb, .simple ie, _ => ⟨_, .memoryToStorageIndexMappingCopyRoot b hb ie p⟩
        | .arr, b, hb, .simple ie, _ => ⟨_, .memoryToStorageIndexArrayCopyRoot b hb ie p⟩
        | _, _, _, .read _, hi | _, _, _, .binop .., hi | _, _, _, .unop .., hi
        | _, _, _, .ternary .., hi | _, _, _, .readMem _, hi => absurd hi (by simp [Val.isSimple])
      else ⟨_, .memoryToStorageIndexNonSimpleIndexCapture it b hb i (not_simple hi) p _
        (freshName_isFresh C Γ "ie")⟩
    else ⟨_, .memoryToStorageIndex_unfold_leftFst it b (not_simple hb) i p _ (freshName_isFresh C Γ "sp")⟩

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
  | .declMem R x hx init hd => declMemStep m R x hx init hd
  | .rebindMem x h r => rebindMemStep m x h r
  | .assignMem l r => assignMemStep m l r
  | .assignFromMem l p => assignFromMemStep m l p
  | .opAssign op hop hp l r => opStep m op hop hp l r
  | .incDec op hp l => incStep m op hp l
  | .push b v hd => pushStep m b v hd
  | .pop b => popStep m b
  | .transfer r a => transferStep m r a
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
  | .push b v =>
    match v with
    | none => s!"\{ storage := push(storage, {b.toStr}) }"
    | some r => s!"\{ storage := push(storage, {b.toStr}, {r.toStr}) }"
  | .pop b => s!"\{ storage := pop(storage, {b.toStr}) }"
  | .transfer r a => s!"\{ transfer({r.toStr}, {a.toStr}) }"
  | .bindMem x p => s!"\{ {x} := ref({p.toStr}) }"
  | .bindCopy x p _ => s!"\{ {x} := freshId(alloc({x}, {p.toStr})) || memory := alloc({x}, {p.toStr}) }"
  | .allocMem x _ => s!"\{ {x} := freshId(alloc({x})) || memory := alloc({x}) }"
  | .writeMem l r => s!"\{ memory := write(memory, {l.toStr}, {r.toStr}) }"
  | .saveMem l p => s!"\{ storage := save(storage, {l.toStr}, copyMem(mtSt, memory, {p.toStr})) }"
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
