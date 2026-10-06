import Solidity.Calculus.KeyNotation

/-!
# Reading memory as solkey reads it

The memory clauses of `sol_decide`, each the transcription of the solkey
taclets named on it (`memoryRules.key`, `structMemoryRules.key`;
`docs/lean-key-rule-map.md` has the rows), and each proved against the
interpreter: Theory's memory has no heap denotation, so the interpreter lemma
is the soundness and `Theory/Memory.lean` the cited counterpart.

* **Static.**  A memory is the tree of its writes and allocations (`LMem`),
  and a read walks the writes from the newest, comparing names and selectors
  without running anything (`LMem.readT`, `LMem.readI`): a name is fixed at
  its birth (`MemNames.Births`), so two names are one object exactly when
  they are one name (`MemNames.Births.eval_inj`).  An index that is no
  literal is compared with a `kite`, once per write to the same object.
* **No memory in a word.**  What `readT` gives is the term written, a
  default, or a read of storage: never a read of memory.  A value written
  from a read of memory (`xs[i] += 1`) therefore holds no copy of the
  memory, and the leaf does not double with each write, as a read deferred
  to the elimination would make it.
* **Halting is Lean's.**  KeY's functions are total; here a read below a
  length halts, a member write needs a struct, a name may resolve to
  nothing.  Each reader is exact under the run of the memory it reads
  (`LMem.run`), and each guard (`nameG`, `structG`, `writeG`) returns exactly
  where the interpreter's operation does.  A copy from storage reads the
  storage through `findLive`, so a path asking for a `length` is refused
  (`noLen`) rather than read past the copy's shape.
* **Cost.**  Every reader makes one recursive call per arm, so its run is
  linear in the writes; nothing builds an allocation's default value, which
  is read off the declared type instead (`dfltSel`, `Ty.memberTy`).
-/

namespace Solidity
namespace Decide
open Semantics SemanticsProperties MemNames
open Theory.Memory (resolveFrom step)

/-! ## Reading memory as solkey reads it -/

/-- What the selector `a` reads in the object `n` of the memory `μ`: the
word at a member or an element, or the length. -/
def LSel.read (σ μ : State) (n : Nat) : LSel → Res Value
  | .fld f => readAddr μ (.memoryField n f) >>= MVal.asValue
  | .idx t => t.eval σ >>= Value.asInt >>= fun j => readAddr μ (.memoryIndex n j) >>= MVal.asValue
  | .size => memArrayLen μ n

/-- The object the reference slot `a` of the object `n` names. -/
def LSel.iread (σ μ : State) (n : Nat) (a : LSel) : Res Nat :=
  a.addr σ n >>= readAddr μ >>= MVal.asRef

/-- How a selector read stands to a selector written: the same slot, apart,
or a comparison of the index read `r` with the index written `w`. -/
inductive SelRel where
  | same
  | apart
  | key (r w : LTerm)

/-- `selRel a1 a2`: the selector `a1` written against the selector `a2` read,
`readOnWrite`'s `a1 = a2` decided statically: members by name, literal
indices by value, other indices by a `kite` (`.key r w`, the index read `r`
first). -/
def selRel : LSel → LSel → SelRel
  | .fld f, .fld g => if f = g then .same else .apart
  | key{ at(w) }, key{ at(r) } =>
    match r, w with
    | .lit (.int c), .lit (.int d) => if c = d then .same else .apart
    | _, _ => .key r w
  | _, _ => .apart

/-- The word a memory value is, KeY's `cast(v)`: a reference is none. -/
def LMV.wordT : LMV → LTerm
  | .word t => t
  | .ref _ => key{ err }

/-- `true` where `0 ≤ k < n`, halting elsewhere. -/
def ltG (k n : LTerm) : LTerm :=
  key{ if(0 <= k && k < n) then true else err }

/-- `ltG`, decided on literals. -/
def ltR (k n : LTerm) : LTerm :=
  match k, n with
  | .lit (.int c), .lit (.int d) => if 0 ≤ c ∧ c < d then key{ true } else key{ err }
  | _, _ => ltG k n

/-- `n`, or `0` where it is negative: the length `new T[](n)` allocates. -/
def natL (n : LTerm) : LTerm :=
  match n with
  | .lit (.int c) => .lit (.int c.toNat)
  | n => key{ if(binop(‹.lt›, int, n, 0)) then 0 else n }

/-- No segment of the path asks for a `length`. -/
def noLen (p : List Seg) : Bool := p.all fun s => s != .field "length"

/-- The path `q` extended by literal segments. -/
def LPath.ext : LPath → List Seg → LPath
  | q, [] => q
  | q, .field f :: r => (q.field f).ext r
  | q, .at j :: r => (q.at (.lit (.int j))).ext r

/-- The name one literal segment longer. -/
def LId.extend (i : LId) (s : Seg) : LId := ⟨i.root, i.path ++ [s]⟩

/-- The literal segment a selector is. -/
def LSel.seg? : LSel → Option Seg
  | .fld f => some (.field f)
  | .idx (.lit (.int j)) => some (.at j)
  | _ => none

/-- What a selector reads below a copy, its storage reads given: `find` for a
word, `len` for the length (`readFromCopyToStorage`'s
`find(st, consr(fxs, a))`). -/
def copySelG (find len : LPath → LTerm) (q : LPath) (fxs : List Seg) : LSel → Option LTerm
  | .fld f => if noLen (fxs ++ [.field f]) then some (find ((q.ext fxs).field f)) else none
  | key{ at(t) } => if noLen fxs then some (find ((q.ext fxs).at t)) else none
  | key{ size } => if noLen fxs then some (len (q.ext fxs)) else none

/-! ### What an allocation holds -/

/-- The word a default of the type `T` holds: a primitive's default
(`defaultValueInt`, `defaultValueBool`). -/
def dfltWord : Option Ty → LTerm
  | some (.prim q) => .lit q.default
  | _ => key{ err }

/-- What a selector reads in a fresh default of `T`, KeY's
`init(idC(idp, flds), a)`. -/
def dfltSel : Option Ty → LSel → LTerm
  -- initMember
  | some T, .fld f => dfltWord (T.at (.field f))
  -- initElement, below the length (sizeOfFixed)
  | some (.ref (.fixed E n)), key{ at(t) } => seqL (ltR t (.lit (.int n))) (dfltWord (some E))
  -- initSize: sizeOfFixed
  | some (.ref (.fixed _ n)), key{ size } => .lit (.int n)
  -- initSize: sizeOfDyn
  | some (.ref (.array _)), key{ size } => key{ 0 }
  -- sizeOfLeaf, and an element of an empty `T[]`: halts
  | _, _ => key{ err }

/-- `true` where the object at `p` of a fresh default of `T` is there. -/
def dfltRef (T : Option Ty) : LTerm :=
  match T with
  | some (.ref _) => key{ true }
  | _ => key{ err }

/-- `true` where the object at `p` of a fresh default of `T` is a struct. -/
def dfltStruct (T : Option Ty) : LTerm :=
  match T with
  | some (.ref (.struct _)) => key{ true }
  | _ => key{ err }

/-- What a selector reads below `new R(n)` at the path `flds`: an element is
there below the length `n` (`memoryArrayFreshAlloc`, `shapeAtDyn`). -/
def newSel (R : RefTy) (n : LTerm) (flds : List Seg) (a : LSel) : LTerm :=
  match R, flds, a with
  | .array _, [], .fld _ => key{ err }
  -- initElement below the length written
  | .array E, [], key{ at(t) } => seqL (ltR t n) (dfltWord (some E))
  -- readOnWrite at `size`: the length written, `0` where negative
  | .array _, [], key{ size } => natL n
  -- shapeAtDyn: below an element, its type's default
  | .array E, .at j :: rest, a => seqL (ltR (.lit (.int j)) n) (dfltSel (E.memberTy rest) a)
  | .array _, .field _ :: _, _ => key{ err }
  | R, flds, a => dfltSel ((Ty.ref R).memberTy flds) a

/-- `g` of the type at `p` below `new R(n)`, an element guarded by the length. -/
def newObj (g : Option Ty → LTerm) (R : RefTy) (n : LTerm) (p : List Seg) : LTerm :=
  match R, p with
  | .array E, [] => g (some (.ref (.array E)))
  | .array E, .at j :: rest => seqL (ltR (.lit (.int j)) n) (g (E.memberTy rest))
  | .array _, .field _ :: _ => key{ err }
  | R, p => g ((Ty.ref R).memberTy p)

/-- A test that the object at `Q` of the storage `st` is one memory would
hold by reference: present, and no word. -/
def refT (st : LStor) (Q : LPath) : LTerm := key{ if(‹isT key{ find(st, Q) }›) then err else has(st, Q) }

/-- What a selector reads below a copy of the subtree at `q` of `st`, at the
path `fxs`: the storage read one segment further (`readFromCopyToStorage`,
`find(st, consr(fxs, a))`; at `size`, `findDefinitionSize`). -/
def copySel (st : LStor) (q : LPath) (fxs : List Seg) : LSel → Option LTerm :=
  copySelG (LTerm.find st) (LTerm.len st) q fxs

/-- `refT`'s test, a struct and no array: what a member write asks. -/
def structT (st : LStor) (Q : LPath) : LTerm :=
  key{ if(‹isT key{ find(st, Q.length) }›) then err else ‹refT st Q› }

/-! ### The readers

Each arm is the taclet named above it, in that taclet's schema variables:
KeY's `\find(read(write(mem, id1, a1, v), id2, a2))` is the arm
`key{ write(mem, id1, a1, v) }, id2, a2`. -/

/-- **The word a read of memory finds** (`readOnWrite`, `readOnAddM`,
`readFromCopyToStorage`): the writes walked from the newest, each compared
with the read statically, down to the allocation of the name's root.  A
word written is the term written, so a read holds no memory. -/
def LMem.readT : LMem → LId → LSel → Option LTerm
  -- readFromEmptyMemory: refused (the bottom is the pre-state, not `mtMem`)
  | key{ memory }, _, _ => none
  -- readOnAddM: \if(idp1 = idp2) \then init(idC(idp2, flds), a2) \else read(mem, id2, a2)
  | key{ addM(mem, shaped(idp1, R)) }, id2, a2 =>
    if id2.root = idp1 then some (dfltSel ((Ty.ref R).memberTy id2.path) a2) else mem.readT id2 a2
  -- memoryArrayFreshAlloc: readOnAddM and readOnWrite at `size`, as one node
  | key{ write(addM(mem, shaped(idp1, R)), idC(idp1, nil), size, n) }, id2, a2 =>
    if id2.root = idp1 then some (newSel R n id2.path a2) else mem.readT id2 a2
  -- readFromCopyToStorage: \if(idp1 = idp2) \then find(st, consr(fxs, a2)) \else read(mem, id2, a2)
  | key{ copySt(mem, idp1, find(st, q)) }, id2, a2 =>
    if id2.root = idp1 then copySel st q id2.path a2 else mem.readT id2 a2
  -- readOnWrite: \if(id1 = id2 & a1 = a2) \then cast(v) \else read(mem, id2, a2)
  | key{ write(mem, id1, a1, v) }, id2, a2 =>
    if id2 = id1 then
      match selRel a1 a2 with
      | .same => some key{ cast(v) }
      | .apart => mem.readT id2 a2
      -- if(r = w) then cast(v) else read(mem, id2, a2)
      | .key r w => (mem.readT id2 a2).map (.kite r w v.wordT)
    else mem.readT id2 a2

/-- **The object a reference slot names** (`initIdentity`,
`readFromCopyToStorageIdentity`, `readOnWrite` at an `Identity`): the name
one segment longer where nothing wrote the slot, the name written where a
reference was. -/
def LMem.readI : LMem → LId → LSel → Option LId
  -- readFromEmptyMemory: refused
  | key{ memory }, _, _ => none
  -- readOnAddM, then initIdentity: idC(idp2, consr(flds, a2))
  | key{ addM(mem, shaped(idp1, _)) }, id2, a2 =>
    if id2.root = idp1 then a2.seg?.map id2.extend else mem.readI id2 a2
  -- memoryArrayFreshAlloc, then initIdentity
  | key{ write(addM(mem, shaped(idp1, _)), idC(idp1, nil), size, _) }, id2, a2 =>
    if id2.root = idp1 then a2.seg?.map id2.extend else mem.readI id2 a2
  -- readFromCopyToStorageIdentity: \then idC(idp1, consr(fxs, a2))
  | key{ copySt(mem, idp1, find(_, _)) }, id2, a2 =>
    if id2.root = idp1 then a2.seg?.map id2.extend else mem.readI id2 a2
  -- readOnWrite at an Identity; a word, or a symbolic index, is refused
  | key{ write(mem, id1, a1, v) }, id2, a2 =>
    if id2 = id1 then
      match selRel a1 a2, v with
      | .same, .ref j' => some j'
      | .apart, _ => mem.readI id2 a2
      | _, _ => none
    else mem.readI id2 a2

/-- A test that the name denotes an object: decided by the type below an
allocation, read off the storage below a copy (Lean only). -/
def LMem.nameG : LMem → LId → Option LTerm
  | key{ memory }, _ => none
  | key{ addM(mem, shaped(idp1, R)) }, id2 =>
    if id2.root = idp1 then some (dfltRef ((Ty.ref R).memberTy id2.path)) else mem.nameG id2
  | key{ write(addM(mem, shaped(idp1, R)), idC(idp1, nil), size, n) }, id2 =>
    if id2.root = idp1 then some (newObj dfltRef R n id2.path) else mem.nameG id2
  -- readFromCopyToStorageIdentity: there where the storage holds no word
  | key{ copySt(mem, idp1, find(st, q)) }, id2 => if id2.root = idp1 then
      (if noLen id2.path then some (refT st (q.ext id2.path)) else none) else mem.nameG id2
  -- newFromWrite: a write allocates nothing
  | key{ write(mem, _, _, _) }, id2 => mem.nameG id2

/-- A test that the name denotes a struct: what a member write needs (Lean
only). -/
def LMem.structG : LMem → LId → Option LTerm
  | key{ memory }, _ => none
  | key{ addM(mem, shaped(idp1, R)) }, id2 =>
    if id2.root = idp1 then some (dfltStruct ((Ty.ref R).memberTy id2.path)) else mem.structG id2
  | key{ write(addM(mem, shaped(idp1, R)), idC(idp1, nil), size, n) }, id2 =>
    if id2.root = idp1 then some (newObj dfltStruct R n id2.path) else mem.structG id2
  | key{ copySt(mem, idp1, find(st, q)) }, id2 => if id2.root = idp1 then
      (if noLen id2.path then some (structT st (q.ext id2.path)) else none) else mem.structG id2
  | key{ write(mem, _, _, _) }, id2 => mem.structG id2

/-- The length of the object a name denotes, `read(mem, id, size)`
(`initSize`, `findDefinitionSize`). -/
def LMem.lenT (mem : LMem) (id : LId) : Option LTerm := mem.readT id key{ size }

/-- **The guard of a write** (Lean only, the program rules'
`\add(0 <= ie & ie < read(memory, mv, size))`): a member is written in a
struct, an element below the length. -/
def LMem.writeG (mem : LMem) (id : LId) : LSel → Option LTerm
  | .fld _ => mem.structG id
  | key{ at(t) } => (mem.lenT id).map (ltR t)
  | key{ size } => none

/-- Every reference written in the memory names an object of an older root,
so a copy out of it halts on no cycle (Lean only; `MemNames.DescFrom`). -/
def LMem.refDesc : LMem → Bool
  | key{ memory } => true
  | key{ addM(mem, shaped(_, _)) }
  | key{ write(addM(mem, shaped(_, _)), idC(_, nil), size, _) }
  | key{ copySt(mem, _, find(_, _)) } => mem.refDesc
  | key{ write(mem, id1, _, v) } => mem.refDesc && match v with
    | .word _ => true
    | .ref j' => decide (j'.root < id1.root)

/-! ### Soundness: the runs -/

theorem readPath_ref_iff (τ : State) : ∀ (p : List Seg) (r n : Nat),
    resolveFrom τ.heap r p = some n ↔ (MVal.ref r).readPath τ p = .ok (.ref n)
  | [], r, n => by
    simp only [resolveFrom, MVal.readPath, Option.some.injEq, Except.ok.injEq, MVal.ref.injEq]
  | a :: p, r, n => by
    rw [resolveFrom_cons]
    simp only [MVal.readPath]
    constructor
    · rintro ⟨c, hs, hr⟩
      rw [(step_iff_readAddr τ r c a).1 hs, Res.ok_bind']
      exact (readPath_ref_iff τ p c n).1 hr
    · intro h
      cases hra : readAddr τ (.ofSeg r a) with
      | error e => rw [hra] at h; cases h
      | ok mv =>
        rw [hra, Res.ok_bind'] at h
        cases mv with
        | ref c => exact ⟨c, (step_iff_readAddr τ r c a).2 hra, (readPath_ref_iff τ p c n).2 h⟩
        | prim pv => cases p <;> simp only [MVal.readPath, Except.ok.injEq, reduceCtorEq] at h

theorem Births.eval_snoc_ne {B : Births} {b : Birth} {k : Nat} (hk : k ≠ B.length)
    (p : List Seg) : (B ++ [b]).eval k p = B.eval k p := by
  by_cases h : k < B.length
  · exact Births.eval_mono h p
  · have e1 : (B ++ [b])[k]? = none :=
      List.getElem?_eq_none (by simp only [List.length_append, List.length_singleton]; omega)
    have e2 : B[k]? = none := List.getElem?_eq_none (by omega)
    simp only [Births.eval, e1, e2]

theorem LId.evalR_ok {B : Births} {i : LId} {n : Nat} :
    LId.evalR B i = .ok n ↔ B.eval i.root i.path = some n := by
  unfold LId.evalR
  split <;> rename_i h <;> simp only [h, Except.ok.injEq, Option.some.injEq, reduceCtorEq]

theorem asRef_ok {mv : MVal} {id : Nat} (h : MVal.asRef mv = .ok id) : mv = .ref id := by
  cases mv with
  | ref r => cases h; rfl
  | prim _ => cases h

/-- A run's allocations are births in order (`MemNames.Births.Ok`). -/
theorem LMem.run_births (σ : State) : (m : LMem) → ∀ {μ : State} {B : Births},
    m.run σ = .ok (μ, B) → B.Ok σ.nextId μ
  | .init, μ, B, h => by
    simp only [LMem.run, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact Births.Ok.nil (Nat.le_refl _)
  | .addM m k R, μ, B, h => by
    simp only [LMem.run, Res.bind_eq_ok] at h
    obtain ⟨r, hr, h⟩ := h
    split at h
    · simp only [Res.bind_eq_ok] at h
      obtain ⟨a, ha, h⟩ := h
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact (LMem.run_births σ m hr).snoc (Close.allocDefault_copy ha)
    · cases h
  | .newArr m k R n, μ, B, h => by
    simp only [LMem.run, Res.bind_eq_ok] at h
    obtain ⟨c, _, r, hr, h⟩ := h
    split at h
    · simp only [Res.bind_eq_ok] at h
      obtain ⟨a, ha, id, hid, h⟩ := h
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hc : copyStToM r.1 (newArrVal R c) = .ok (a.1, .ref id) := by
        rw [ha, ← asRef_ok hid]
      exact (LMem.run_births σ m hr).snoc hc
    · cases h
  | .copySt m k s q, μ, B, h => by
    simp only [LMem.run, Res.bind_eq_ok] at h
    obtain ⟨_, _, _, _, sv, _, r, hr, h⟩ := h
    split at h
    · simp only [Res.bind_eq_ok] at h
      obtain ⟨a, ha, id, hid, h⟩ := h
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hc : copyStToM r.1 sv = .ok (a.1, .ref id) := by
        rw [ha, ← asRef_ok hid]
      exact (LMem.run_births σ m hr).snoc hc
    · cases h
  | .write m i a v, μ, B, h => by
    simp only [LMem.run, Res.bind_eq_ok] at h
    obtain ⟨r, hr, _, _, ad, _, mv, _, μ', hw, h⟩ := h
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact (LMem.run_births σ m hr).mono (Nat.le_of_eq (Close.writeAddr_nextId hw).symm)

/-! ### Soundness: the guards -/

/-- What a term returns, where it returns. -/
def Rets (x : Res Value) : Prop := ∃ v, x = .ok v

theorem ltG_rets (σ : State) (k n : LTerm) :
    Rets ((ltG k n).eval σ) ↔
      ∃ c d, k.eval σ = .ok (.int c) ∧ n.eval σ = .ok (.int d) ∧ 0 ≤ c ∧ c < d := by
  unfold ltG Rets
  cases hk : k.eval σ with
  | error e =>
    simp only [LTerm.eval, hk, evalBinop, bind, Except.bind, reduceCtorEq, false_and,
      exists_false]
  | ok x =>
    cases x with
    | bool b =>
      simp only [LTerm.eval, hk, evalBinop, applyBinOp, Value.asInt, bind, Except.bind,
        reduceCtorEq, Except.ok.injEq, false_and, exists_false, 
        ]
    | int c =>
      cases hn : n.eval σ with
      | error e =>
        by_cases h0 : 0 ≤ c <;>
        simp only [LTerm.eval, bind, Except.bind, evalBinop, hk, applyBinOp, Value.asInt, h0, decide_true,
          decide_false, checkArith, pure, Except.pure, hn, pickBranch, reduceCtorEq, exists_false,
          Except.ok.injEq, PrimVal.int.injEq, false_and, and_false]
      | ok y =>
        cases y with
        | bool b =>
          by_cases h0 : 0 ≤ c <;>
          simp only [LTerm.eval, bind, Except.bind, evalBinop, hk, applyBinOp, Value.asInt, h0, decide_true,
          decide_false, checkArith, pure, Except.pure, hn, pickBranch, reduceCtorEq, exists_false,
          Except.ok.injEq, PrimVal.int.injEq, false_and, and_false]
        | int d =>
          by_cases h0 : 0 ≤ c <;> by_cases h1 : c < d <;>
          simp only [LTerm.eval, bind, Except.bind, evalBinop, hk, applyBinOp, Value.asInt, h0, decide_true,
            decide_false, checkArith, pure, Except.pure, hn, h1, Value.asBool, Bool.and_self,
            Bool.and_false, pickBranch, reduceCtorEq, exists_false, Except.ok.injEq, exists_eq',
            PrimVal.int.injEq, exists_and_left, exists_eq_left', and_self, and_false, and_true]

theorem ltR_rets (σ : State) (k n : LTerm) :
    Rets ((ltR k n).eval σ) ↔
      ∃ c d, k.eval σ = .ok (.int c) ∧ n.eval σ = .ok (.int d) ∧ 0 ≤ c ∧ c < d := by
  unfold ltR
  split
  · rename_i c d
    by_cases h : 0 ≤ c ∧ c < d
    · simp only [h, and_self, if_true, Rets, LTerm.eval]
      exact ⟨fun _ => ⟨c, d, rfl, rfl, h⟩, fun _ => ⟨_, rfl⟩⟩
    · simp only [h, if_false, Rets, LTerm.eval, reduceCtorEq, exists_false, false_iff]
      rintro ⟨c', d', hc, hd, h0, h1⟩
      cases hc; cases hd
      exact h ⟨h0, h1⟩
  · exact ltG_rets σ k n

theorem seqL_rets (σ : State) (g a : LTerm) :
    Rets ((seqL g a).eval σ) ↔ Rets (g.eval σ) ∧ Rets (a.eval σ) := by
  rw [seqL_eval]
  unfold Rets
  cases g.eval σ with
  | error e => simp only [bind, Except.bind, reduceCtorEq, exists_false, false_and]
  | ok x => simp only [Res.ok_bind', Except.ok.injEq, exists_eq', true_and]

theorem natL_eval (σ : State) (n : LTerm) {c : Int} (hn : n.eval σ = .ok (.int c)) :
    (natL n).eval σ = .ok (.int c.toNat) := by
  unfold natL
  split
  · rename_i c'
    simp only [LTerm.eval] at hn
    cases hn; rfl
  · by_cases h : c < 0
    · simp only [LTerm.eval, bind, Except.bind, hn, evalBinop, applyBinOp, Value.asInt, h,
        decide_true, checkArith, pickBranch, Int.ofNat_toNat, Except.ok.injEq, PrimVal.int.injEq]
      omega
    · simp only [LTerm.eval, bind, Except.bind, hn, evalBinop, applyBinOp, Value.asInt, h,
        decide_false, checkArith, pickBranch, Int.ofNat_toNat, Except.ok.injEq, PrimVal.int.injEq]
      omega

/-! ### Soundness: writes and allocations leave the other slots -/

/-- An object's kind: a struct (`none`), or an array of its length. -/
def objKind (μ : State) (n : Nat) : Res (Option Nat) :=
  μ.getObj n >>= fun o => match o with
    | .struct _ => .ok none
    | .array es _ => .ok (some es.length)

theorem memArrayLen_objKind (μ : State) (n : Nat) :
    memArrayLen μ n = objKind μ n >>= fun o => match o with
      | none => .error .stuck
      | some l => .ok (.int l) := by
  unfold memArrayLen objKind
  cases μ.getObj n with
  | error e => rfl
  | ok o => cases o <;> rfl

/-- A write changes no object's kind, nor an array's length. -/
theorem objKind_writeAddr {μ μ' : State} {mv : MVal} {ad : Addr} (h : writeAddr μ' mv ad = .ok μ)
    (n : Nat) : objKind μ n = objKind μ' n := by
  cases ad with
  | memoryField id f =>
    simp only [writeAddr, memWriteField] at h
    cases hg : μ'.getObj id with
    | error e => simp only [bind, Except.bind, hg, reduceCtorEq] at h
    | ok o =>
      cases o with
      | array es fx => simp only [bind, Except.bind, hg, reduceCtorEq] at h
      | struct fs =>
        simp only [hg, bind, Except.bind, Except.ok.injEq] at h
        subst h
        by_cases hn : n = id
        · subst hn
          rw [objKind, objKind, hg]
          simp only [State.getObj, State.setObj, lookupBy_setBy_self]
          rfl
        · simp only [objKind, State.getObj, State.setObj, lookupBy_setBy_ne hn]
  | memoryIndex id i =>
    simp only [writeAddr, memWriteIndex] at h
    cases hg : μ'.getObj id with
    | error e => simp only [bind, Except.bind, hg, reduceCtorEq] at h
    | ok o =>
      cases o with
      | struct fs => simp only [bind, Except.bind, hg, reduceCtorEq] at h
      | array es fx =>
        simp only [hg, bind, Except.bind] at h
        split at h
        · simp only [Except.ok.injEq] at h
          subst h
          by_cases hn : n = id
          · subst hn
            rw [objKind, objKind, hg]
            simp only [State.getObj, State.setObj, lookupBy_setBy_self, Res.ok_bind',
              List.length_set]
          · simp only [objKind, State.getObj, State.setObj, lookupBy_setBy_ne hn]
        · cases h

theorem memArrayLen_writeAddr {μ μ' : State} {mv : MVal} {ad : Addr}
    (h : writeAddr μ' mv ad = .ok μ) (n : Nat) : memArrayLen μ n = memArrayLen μ' n := by
  rw [memArrayLen_objKind, memArrayLen_objKind, objKind_writeAddr h]

/-- A write at another object leaves every read of this one. -/
theorem LSel.read_write_ne {σ μ μ' : State} {mv : MVal} {ad : Addr} {n : Nat}
    (h : writeAddr μ' mv ad = .ok μ) (hn : ad.id ≠ n) (a : LSel) :
    a.read σ μ n = a.read σ μ' n := by
  obtain ⟨_, _, _, hfr⟩ := Close.writeAddr_setObj h
  have hap : ∀ a', a'.id = n → Close.Apart ad a' := by
    intro a' ha'
    cases ad <;> cases a' <;> simp only [Addr.id] at hn ha' <;>
      simp only [Close.Apart, true_or, ha', Ne.symm hn, not_false_eq_true, true_or]
  cases a with
  | fld f => simp only [LSel.read, hfr (.memoryField n f) (hap _ rfl)]
  | idx t =>
    simp only [LSel.read]
    congr 1; funext j; congr 1
    exact hfr _ (hap (.memoryIndex n j) rfl)
  | size => exact memArrayLen_writeAddr h n

theorem LSel.iread_write_ne {σ μ μ' : State} {mv : MVal} {ad : Addr} {n : Nat}
    (h : writeAddr μ' mv ad = .ok μ) (hn : ad.id ≠ n) (a : LSel) :
    a.iread σ μ n = a.iread σ μ' n := by
  obtain ⟨_, _, _, hfr⟩ := Close.writeAddr_setObj h
  unfold LSel.iread
  cases ha : a.addr σ n with
  | error e => rfl
  | ok a' =>
    have hid : a'.id = n := by
      cases a with
      | fld f => cases ha; rfl
      | idx t =>
        simp only [LSel.addr, Res.bind_eq_ok] at ha
        obtain ⟨_, _, ha⟩ := ha
        cases ha; rfl
      | size => cases ha
    have hap : Close.Apart ad a' := by
      cases ad <;> cases a' <;> simp only [Addr.id] at hn hid <;>
        simp only [Close.Apart, true_or, hid, Ne.symm hn, not_false_eq_true, true_or]
    simp only [Res.ok_bind', hfr _ hap]

/-- An allocation leaves every read of an older object. -/
theorem LSel.read_heapExt {σ μ μ' : State} (hx : μ'.HeapExt μ) {n : Nat} (hn : n < μ'.nextId)
    (a : LSel) : a.read σ μ n = a.read σ μ' n := by
  cases a with
  | fld f => simp only [LSel.read, readAddr_heapExt hx (a := .memoryField n f) hn]
  | idx t =>
    simp only [LSel.read]
    congr 1; funext j; congr 1
    exact readAddr_heapExt hx (a := .memoryIndex n j) hn
  | size => simp only [LSel.read, memArrayLen, State.getObj_heapExt hx hn]

theorem LSel.iread_heapExt {σ μ μ' : State} (hx : μ'.HeapExt μ) {n : Nat} (hn : n < μ'.nextId)
    (a : LSel) : a.iread σ μ n = a.iread σ μ' n := by
  unfold LSel.iread
  cases ha : a.addr σ n with
  | error e => rfl
  | ok a' =>
    have hid : a'.id = n := by
      cases a with
      | fld f => cases ha; rfl
      | idx t =>
        simp only [LSel.addr, Res.bind_eq_ok] at ha
        obtain ⟨_, _, ha⟩ := ha
        cases ha; rfl
      | size => cases ha
    simp only [Res.ok_bind', readAddr_heapExt hx (a := a') (hid ▸ hn)]

theorem objKind_heapExt {μ μ' : State} (hx : μ'.HeapExt μ) {n : Nat} (hn : n < μ'.nextId) :
    objKind μ n = objKind μ' n := by
  simp only [objKind, State.getObj_heapExt hx hn]

/-! ### Soundness: a fresh default -/

/-- `findLive` of a default reads the default of the declared type. -/
theorem findLive_default : ∀ (p : List Seg) (T : Ty) {T' : Ty} {v : SVal},
    (defaultForTy T).findLive p = .ok v → T.memberTy p = some T' → v = defaultForTy T'
  | [], T, T', v, h, hT => by
    simp only [SVal.findLive_nil, Except.ok.injEq] at h
    simp only [Ty.memberTy, Option.some.injEq] at hT
    subst h hT; rfl
  | s :: rest, T, T', v, h, hT => by
    simp only [Ty.memberTy] at hT
    cases hs : T.at s with
    | none => simp only [hs, Option.bind_none, reduceCtorEq] at hT
    | some T₁ =>
      simp only [hs, Option.bind_some] at hT
      cases T with
      | prim q => simp only [Ty.at_prim, reduceCtorEq] at hs
      | ref R =>
        cases R with
        | struct sn =>
          cases s with
          | field f =>
            simp only [Ty.at] at hs
            rw [defaultForTy] at h
            simp only [SVal.findLive, lookupBy_defaultForFields, hs, Option.map_some] at h
            exact findLive_default rest T₁ h hT
          | «at» k => simp only [Ty.at, reduceCtorEq] at hs
        | fixed E n =>
          cases s with
          | field f => simp only [Ty.at, reduceCtorEq] at hs
          | «at» k =>
            simp only [Ty.at] at hs
            split at hs
            · rename_i hk
              cases hs
              rw [defaultForTy] at h
              simp only [SVal.findLive, List.length_replicate] at h
              split at h
              · simp only [List.get_eq_getElem, List.getElem_replicate] at h
                exact findLive_default rest T₁ h hT
              · cases h
            · cases hs
        | array E => cases s <;> simp only [Ty.at, reduceCtorEq] at hs
        | mapping K V => cases s <;> simp only [Ty.at, reduceCtorEq] at hs

/-- The object a path below a fresh default reaches is a fresh default of the
declared type there. -/
theorem dflt_obj {τ : State} {T : Ty} {r n : Nat} {p : List Seg}
    (hc : CopiedTo τ (defaultForTy T) (.ref r)) (hr : resolveFrom τ.heap r p = some n) :
    ∃ R, T.memberTy p = some (.ref R) ∧ CopiedTo τ (defaultForTy (.ref R)) (.ref n) := by
  have hrp := (readPath_ref_iff τ p r n).1 hr
  obtain ⟨v', hv', hc'⟩ := (copiedTo_readPath p hc).1 _ hrp
  obtain ⟨σ₁, σ₂, hcp, hx⟩ := hc
  obtain ⟨T', hT', -⟩ := (copyStToM_default_readPath p hcp hx).1 _ hrp
  rw [findLive_default p T hv' hT'] at hc'
  cases T' with
  | prim q =>
    obtain ⟨_, _, hq, _⟩ := hc'
    have h' := (copyStToM_default_prim hq).2
    cases q <;> simp only [PrimTy.default, Value.toMVal, reduceCtorEq] at h'
  | ref R => exact ⟨R, hT', hc'⟩

theorem readPath_single (τ : State) (n : Nat) (s : Seg) :
    (MVal.ref n).readPath τ [s] = readAddr τ (.ofSeg n s) := by
  simp only [MVal.readPath]
  cases readAddr τ (.ofSeg n s) <;> rfl

theorem memberTy_single (T : Ty) (s : Seg) : T.memberTy [s] = T.at s := by
  simp only [Ty.memberTy]
  cases T.at s <;> rfl

theorem asValue_toMVal (v : Value) : (Value.toMVal v).asValue = .ok v := by
  cases v <;> rfl

/-- **A slot of a fresh default** (`initMember`, `initElement`,
`defaultValueInt`/`Bool`): the default of the declared type, where it is a
primitive. -/
theorem slot_default (σ : State) {τ : State} {T : Ty} {n : Nat}
    (hc : CopiedTo τ (defaultForTy T) (.ref n)) (s : Seg) :
    Sim ((dfltWord (T.at s)).eval σ) (readAddr τ (.ofSeg n s) >>= MVal.asValue) := by
  obtain ⟨σ₁, σ₂, hcp, hx⟩ := hc
  have hd := copyStToM_default_readPath [s] hcp hx
  rw [readPath_single, memberTy_single] at hd
  intro u
  constructor
  · intro h
    cases hts : T.at s with
    | none => simp only [hts, dfltWord, LTerm.eval, reduceCtorEq] at h
    | some T'' =>
      cases T'' with
      | ref R => simp only [hts, dfltWord, LTerm.eval, reduceCtorEq] at h
      | prim q =>
        simp only [hts, dfltWord, LTerm.eval, Except.ok.injEq] at h
        subst h
        obtain ⟨mv', hmv, hdm⟩ := hd.2 _ hts
        simp only [DefaultMVal] at hdm
        rw [hmv, hdm, Res.ok_bind', asValue_toMVal]
  · intro h
    simp only [Res.bind_eq_ok] at h
    obtain ⟨mv', hmv, hu⟩ := h
    obtain ⟨T'', hts, hdm⟩ := hd.1 _ hmv
    cases T'' with
    | ref R =>
      obtain ⟨id, rfl, -⟩ := hdm
      cases hu
    | prim q =>
      simp only [DefaultMVal] at hdm
      rw [hdm, asValue_toMVal] at hu
      cases hu
      simp only [hts, dfltWord, LTerm.eval]

theorem defaultForTy_fixed (E : Ty) (n : Nat) :
    defaultForTy (.ref (.fixed E n)) = .array (List.replicate n (defaultForTy E)) [] true := by
  rw [defaultForTy]

/-- **What a selector reads in a fresh default** (`initMember`,
`initElement`, `initSize`, `sizeOfFixed`). -/
theorem dfltSel_sim (σ : State) {τ : State} {T : Ty} {n : Nat}
    (hc : CopiedTo τ (defaultForTy T) (.ref n)) :
    (a : LSel) → Sim ((dfltSel (some T) a).eval σ) (a.read σ τ n)
  | .fld f => by
    simp only [dfltSel, LSel.read]
    exact slot_default σ hc (.field f)
  | .idx t => by
    have hslot : Sim (t.eval σ >>= Value.asInt >>= fun j => (dfltWord (T.at (.at j))).eval σ)
        ((LSel.idx t).read σ τ n) :=
      Sim.bind (Sim.refl _) fun j => slot_default σ hc (.at j)
    refine Sim.trans ?_ hslot
    intro u
    cases ht : t.eval σ with
    | error e =>
      constructor
      · intro h
        cases T with
        | prim q => simp only [dfltSel, LTerm.eval, reduceCtorEq] at h
        | ref R =>
          cases R with
          | fixed E len =>
            have hr : ¬ Rets ((ltR t (.lit (.int len))).eval σ) := by
              rw [ltR_rets]; rintro ⟨c, d, hc', -⟩; rw [ht] at hc'; cases hc'
            simp only [dfltSel] at h
            exact absurd ((seqL_rets σ _ _).1 ⟨u, h⟩).1 hr
          | _ => simp only [dfltSel, LTerm.eval, reduceCtorEq] at h
      · intro h; simp only [bind, Except.bind, reduceCtorEq] at h
    | ok x =>
      cases x with
      | bool b =>
        constructor
        · intro h
          cases T with
          | prim q => simp only [dfltSel, LTerm.eval, reduceCtorEq] at h
          | ref R =>
            cases R with
            | fixed E len =>
              have hr : ¬ Rets ((ltR t (.lit (.int len))).eval σ) := by
                rw [ltR_rets]; rintro ⟨c, d, hc', -⟩; rw [ht] at hc'; cases hc'
              simp only [dfltSel] at h
              exact absurd ((seqL_rets σ _ _).1 ⟨u, h⟩).1 hr
            | _ => simp only [dfltSel, LTerm.eval, reduceCtorEq] at h
        · intro h; simp only [Value.asInt, bind, Except.bind, reduceCtorEq] at h
      | int j =>
        simp only [Res.ok_bind', Value.asInt]
        cases T with
        | prim q => simp only [dfltSel, Ty.at_prim, dfltWord]
        | ref R =>
          cases R with
          | fixed E len =>
            simp only [dfltSel, Ty.at]
            rw [seqL_eval]
            by_cases hj : 0 ≤ j ∧ j < (len : Int)
            · have hr : Rets ((ltR t (.lit (.int len))).eval σ) :=
                (ltR_rets σ _ _).2 ⟨j, len, ht, rfl, hj.1, hj.2⟩
              obtain ⟨v, hv⟩ := hr
              simp only [hv, Res.ok_bind', hj, and_self, if_true]
            · have hr : ¬ Rets ((ltR t (.lit (.int len))).eval σ) := by
                rw [ltR_rets]; rintro ⟨c, d, hc', hd', h0, h1⟩
                rw [ht] at hc'; cases hc'; cases hd'; exact hj ⟨h0, h1⟩
              cases hv : (ltR t (.lit (.int len))).eval σ with
              | ok v => exact absurd ⟨v, hv⟩ hr
              | error e =>
                simp only [bind, Except.bind, hj, if_false, dfltWord, LTerm.eval, reduceCtorEq]
          | struct _ => simp only [dfltSel, Ty.at, dfltWord]
          | array _ => simp only [dfltSel, Ty.at, dfltWord]
          | mapping _ _ => simp only [dfltSel, Ty.at, dfltWord]
  | .size => by
    simp only [LSel.read, copiedTo_len hc]
    cases T with
    | prim q => cases q <;> (rw [defaultForTy]; exact Sim.refl _)
    | ref R =>
      cases R with
      | fixed E len =>
        rw [defaultForTy_fixed]
        simp only [dfltSel, LTerm.eval, Close.arrLen, List.length_replicate]
        exact Sim.refl _
      | array E =>
        rw [defaultForTy]
        simp only [dfltSel, LTerm.eval, Close.arrLen, List.length_nil]
        exact Sim.refl _
      | struct sn =>
        rw [defaultForTy]
        exact Sim.refl _
      | mapping K V =>
        rw [defaultForTy]
        exact Sim.refl _

/-- The object a path from `r` reaches in the heap `h`; it halts on none. -/
def resolveR (h : List (Nat × MObj)) (r : Nat) (p : List Seg) : Res Nat :=
  match resolveFrom h r p with
  | some n => .ok n
  | none => .error .stuck

theorem resolveR_ok {h : List (Nat × MObj)} {r n : Nat} {p : List Seg} :
    resolveR h r p = .ok n ↔ resolveFrom h r p = some n := by
  unfold resolveR
  split <;> rename_i hr <;> simp only [hr, Except.ok.injEq, Option.some.injEq, reduceCtorEq]

/-- A name of the newest root denotes what its path reaches in the heap of its
birth. -/
theorem evalR_last (B : Births) (b : Birth) {i : LId} (hk : i.root = B.length) :
    LId.evalR (B ++ [b]) i = resolveR b.heap b.root i.path := by
  unfold LId.evalR resolveR
  rw [hk, Births.eval_last]
  rfl

theorem dflt_resolve {τ : State} {T : Ty} {r : Nat} {p : List Seg} {R : RefTy}
    (hc : CopiedTo τ (defaultForTy T) (.ref r)) (hT : T.memberTy p = some (.ref R)) :
    ∃ n, resolveFrom τ.heap r p = some n := by
  obtain ⟨σ₁, σ₂, hcp, hx⟩ := hc
  obtain ⟨mv', hmv, id, rfl, -⟩ := (copyStToM_default_readPath p hcp hx).2 _ hT
  exact ⟨id, (readPath_ref_iff τ p r id).2 hmv⟩

/-- A fresh default of a reference type is a struct exactly for a struct type. -/
theorem dflt_struct_iff {τ : State} {R : RefTy} {n : Nat}
    (hc : CopiedTo τ (defaultForTy (.ref R)) (.ref n)) :
    (∃ fs, τ.getObj n = .ok (.struct fs)) ↔ ∃ sn, R = .struct sn := by
  rcases copiedTo_ref_obj hc with ⟨fs, mfs, hv, hobj⟩ | ⟨es, sh, fx, mes, hv, hobj, -⟩
  · have hR : ∃ sn, R = .struct sn := by
      cases R with
      | struct sn => exact ⟨sn, rfl⟩
      | fixed E k => rw [defaultForTy_fixed] at hv; cases hv
      | array E => rw [defaultForTy] at hv; cases hv
      | mapping K V => rw [defaultForTy] at hv; cases hv
    simp only [State.getObj, hobj, hR, iff_true]
    exact ⟨mfs, rfl⟩
  · have hR : ¬ ∃ sn, R = .struct sn := by
      rintro ⟨sn, rfl⟩; rw [defaultForTy] at hv; cases hv
    simp only [State.getObj, hobj, hR, iff_false, not_exists]
    intro fs h; cases h

/-- **A read below a fresh default**, along the path of a name. -/
theorem dflt_read_sim (σ : State) {τ : State} {T : Ty} {r : Nat}
    (hc : CopiedTo τ (defaultForTy T) (.ref r)) (p : List Seg) (a : LSel) :
    Sim ((dfltSel (T.memberTy p) a).eval σ) (resolveR τ.heap r p >>= fun n => a.read σ τ n) := by
  cases hres : resolveFrom τ.heap r p with
  | some n =>
    obtain ⟨R, hT, hc'⟩ := dflt_obj hc hres
    simp only [resolveR, hres, Res.ok_bind', hT]
    exact dfltSel_sim σ hc' a
  | none =>
    simp only [resolveR, hres]
    apply Sim.halt _ (fun _ h => by cases h)
    intro u h
    cases hT : T.memberTy p with
    | none => cases a <;> simp only [hT, dfltSel, LTerm.eval, reduceCtorEq] at h
    | some T' =>
      cases T' with
      | ref R =>
        obtain ⟨n, hn⟩ := dflt_resolve hc hT
        rw [hres] at hn; cases hn
      | prim q =>
        cases a <;> simp only [hT, dfltSel, Ty.at_prim, dfltWord, LTerm.eval, reduceCtorEq] at h

theorem dfltRef_rets (σ : State) {τ : State} {T : Ty} {r : Nat}
    (hc : CopiedTo τ (defaultForTy T) (.ref r)) (p : List Seg) :
    Rets ((dfltRef (T.memberTy p)).eval σ) ↔ ∃ n, resolveFrom τ.heap r p = some n := by
  constructor
  · rintro ⟨v, hv⟩
    cases hT : T.memberTy p with
    | none => simp only [hT, dfltRef, LTerm.eval, reduceCtorEq] at hv
    | some T' =>
      cases T' with
      | ref R => exact dflt_resolve hc hT
      | prim q => simp only [hT, dfltRef, LTerm.eval, reduceCtorEq] at hv
  · rintro ⟨n, hn⟩
    obtain ⟨R, hT, -⟩ := dflt_obj hc hn
    simp only [hT, dfltRef, Rets, LTerm.eval, Except.ok.injEq, exists_eq']

theorem dfltStruct_rets (σ : State) {τ : State} {T : Ty} {r : Nat}
    (hc : CopiedTo τ (defaultForTy T) (.ref r)) (p : List Seg) :
    Rets ((dfltStruct (T.memberTy p)).eval σ) ↔
      ∃ n fs, resolveFrom τ.heap r p = some n ∧ τ.getObj n = .ok (.struct fs) := by
  constructor
  · rintro ⟨v, hv⟩
    cases hT : T.memberTy p with
    | none => simp only [hT, dfltStruct, LTerm.eval, reduceCtorEq] at hv
    | some T' =>
      cases T' with
      | ref R =>
        cases R with
        | struct sn =>
          obtain ⟨n, hn⟩ := dflt_resolve hc hT
          obtain ⟨R', hT', hc'⟩ := dflt_obj hc hn
          rw [hT] at hT'
          cases hT'
          obtain ⟨fs, hfs⟩ := (dflt_struct_iff hc').2 ⟨sn, rfl⟩
          exact ⟨n, fs, hn, hfs⟩
        | _ => simp only [hT, dfltStruct, LTerm.eval, reduceCtorEq] at hv
      | prim q => simp only [hT, dfltStruct, LTerm.eval, reduceCtorEq] at hv
  · rintro ⟨n, fs, hn, hfs⟩
    obtain ⟨R, hT, hc'⟩ := dflt_obj hc hn
    obtain ⟨sn, rfl⟩ := (dflt_struct_iff hc').1 ⟨fs, hfs⟩
    simp only [hT, dfltStruct, Rets, LTerm.eval, Except.ok.injEq, exists_eq']

/-- An element read below a length: `seqL (ltR t n) W` against the read at
each index. -/
theorem seqL_ltR_sim (σ : State) (t n W : LTerm) {c : Int} (hn : n.eval σ = .ok (.int c))
    (F : Int → Res Value) (hF : ∀ j, 0 ≤ j → j < c → Sim (W.eval σ) (F j))
    (hout : ∀ j u, ¬ (0 ≤ j ∧ j < c) → F j ≠ .ok u) :
    Sim ((seqL (ltR t n) W).eval σ) (t.eval σ >>= Value.asInt >>= F) := by
  rw [seqL_eval]
  have hhalt : ¬ Rets ((ltR t n).eval σ) → ∀ u,
      ((ltR t n).eval σ >>= fun _ => W.eval σ) ≠ .ok u := by
    intro hr u h
    simp only [Res.bind_eq_ok] at h
    obtain ⟨v, hv, -⟩ := h
    exact hr ⟨v, hv⟩
  intro u
  cases ht : t.eval σ with
  | error e =>
    have hr : ¬ Rets ((ltR t n).eval σ) := by
      rw [ltR_rets]; rintro ⟨c', d, hc', -⟩; rw [ht] at hc'; cases hc'
    simp only [bind, Except.bind, reduceCtorEq, iff_false]
    exact hhalt hr u
  | ok x =>
    cases x with
    | bool b =>
      have hr : ¬ Rets ((ltR t n).eval σ) := by
        rw [ltR_rets]; rintro ⟨c', d, hc', -⟩; rw [ht] at hc'; cases hc'
      simp only [Value.asInt, bind, Except.bind, reduceCtorEq, iff_false]
      exact hhalt hr u
    | int j =>
      simp only [Res.ok_bind', Value.asInt]
      by_cases hj : 0 ≤ j ∧ j < c
      · obtain ⟨v, hv⟩ := (ltR_rets σ t n).2 ⟨j, c, ht, hn, hj.1, hj.2⟩
        rw [hv, Res.ok_bind']
        exact hF j hj.1 hj.2 u
      · have hr : ¬ Rets ((ltR t n).eval σ) := by
          rw [ltR_rets]; rintro ⟨c', d, hc', hd', h0, h1⟩
          rw [ht] at hc'; rw [hn] at hd'; cases hc'; cases hd'; exact hj ⟨h0, h1⟩
        exact ⟨fun h => absurd h (hhalt hr u), fun h => absurd h (hout j u hj)⟩

/-- The word a copy of a default holds: its default, where it is a primitive. -/
theorem dfltWord_copied (σ : State) {τ : State} {E : Ty} {mv : MVal}
    (hc : CopiedTo τ (defaultForTy E) mv) : Sim ((dfltWord (some E)).eval σ) mv.asValue := by
  obtain ⟨σ₁, σ₂, hcp, -⟩ := hc
  rw [Close.copyStToM_asValue hcp]
  cases E with
  | prim q => cases q <;> (rw [defaultForTy]; exact Sim.refl _)
  | ref R =>
    cases R with
    | fixed E k => rw [defaultForTy_fixed]; exact Sim.refl _
    | _ => rw [defaultForTy]; exact Sim.refl _

theorem copied_default_prim {τ : State} {E : Ty} {pv : PrimVal}
    (hc : CopiedTo τ (defaultForTy E) (.prim pv)) : ∃ q, E = .prim q := by
  obtain ⟨σ₁, σ₂, hcp, -⟩ := hc
  cases E with
  | prim q => exact ⟨q, rfl⟩
  | ref R =>
    cases R with
    | fixed E k =>
      rw [defaultForTy_fixed] at hcp
      obtain ⟨id, h⟩ := copyStToM_array_ref hcp; cases h
    | array E =>
      rw [defaultForTy] at hcp
      obtain ⟨id, h⟩ := copyStToM_array_ref hcp; cases h
    | struct sn =>
      rw [defaultForTy] at hcp
      obtain ⟨id, h⟩ := copyStToM_struct_ref hcp; cases h
    | mapping K V =>
      rw [defaultForTy] at hcp
      exact (copyStToM_map_inv hcp).elim

theorem newArrVal_other {R : RefTy} (hR : ∀ E, R ≠ .array E) (c : Int) :
    newArrVal R c = defaultForTy (.ref R) := by
  cases R with
  | array E => exact absurd rfl (hR E)
  | _ => rfl

/-- `new R(n)`'s root is an array, for an array type. -/
theorem newArr_root {μ' μ : State} {E : Ty} {c : Int} {r : Nat}
    (hcp : copyStToM μ' (newArrVal (.array E) c) = .ok (μ, .ref r)) :
    ∃ es, lookupBy r μ.heap = some (.array es false) := by
  rcases copiedTo_ref_obj ⟨μ', μ, hcp, State.HeapExt.refl μ⟩ with
    ⟨fs, mfs, hv, -⟩ | ⟨es, sh, fx, mes, hv, hobj, -⟩
  · simp only [newArrVal, reduceCtorEq] at hv
  · simp only [newArrVal, SVal.array.injEq] at hv
    obtain ⟨-, -, rfl⟩ := hv
    exact ⟨mes, hobj⟩

/-- **A read below `new R(n)`** (`memoryArrayFreshAlloc`, then
`readOnWrite` at `size` and `initElement`). -/
theorem new_read_sim (σ : State) {μ' μ : State} {R : RefTy} {n : LTerm} {c : Int} {r : Nat}
    (hn : n.eval σ = .ok (.int c)) (hcp : copyStToM μ' (newArrVal R c) = .ok (μ, .ref r))
    (p : List Seg) (a : LSel) :
    Sim ((newSel R n p a).eval σ) (resolveR μ.heap r p >>= fun x => a.read σ μ x) := by
  by_cases hR : ∃ E, R = .array E
  · obtain ⟨E, rfl⟩ := hR
    obtain ⟨es, hroot⟩ := newArr_root hcp
    have hx := State.HeapExt.refl μ
    match p, a with
    | [], .fld f =>
      simp only [newSel, resolveR, resolveFrom, Res.ok_bind', LSel.read,
        readAddr_field_array f hroot]
      exact Sim.halt (fun _ h => by cases h) (fun _ h => by cases h)
    | [], .idx t =>
      simp only [newSel, resolveR, resolveFrom, Res.ok_bind', LSel.read]
      refine seqL_ltR_sim σ t n _ hn _ (fun j h0 h1 => ?_) (fun j u hj h => ?_)
      · obtain ⟨mv', hmv, hc'⟩ := (copyStToM_newArr_at j hcp hx).2 h0 h1
        rw [hmv, Res.ok_bind']
        exact dfltWord_copied σ hc'
      · simp only [Res.bind_eq_ok] at h
        obtain ⟨mv', hmv, -⟩ := h
        obtain ⟨h0, h1, -⟩ := (copyStToM_newArr_at j hcp hx).1 _ hmv
        exact hj ⟨h0, h1⟩
    | [], .size =>
      simp only [newSel, resolveR, resolveFrom, Res.ok_bind', LSel.read,
        copyStToM_newArr_len hcp hx, natL_eval σ n hn]
      exact Sim.refl _
    | .field f :: rest, a =>
      have hs : step μ.heap r (.field f) = none := by simp only [step, hroot]
      simp only [newSel, resolveR, resolveFrom, hs]
      exact Sim.halt (fun _ h => by cases h) (fun _ h => by cases h)
    | .at j :: rest, a =>
      simp only [newSel]
      rw [seqL_eval]
      by_cases hj : 0 ≤ j ∧ j < c
      · obtain ⟨v, hv⟩ := (ltR_rets σ (.lit (.int j)) n).2 ⟨j, c, rfl, hn, hj.1, hj.2⟩
        rw [hv, Res.ok_bind']
        obtain ⟨mv', hmv, hc'⟩ := (copyStToM_newArr_at j hcp hx).2 hj.1 hj.2
        cases mv' with
        | ref c₁ =>
          have hs : step μ.heap r (.at j) = some c₁ :=
            (step_iff_readAddr μ r c₁ (.at j)).2 hmv
          simp only [resolveR, resolveFrom, hs]
          exact dflt_read_sim σ hc' rest a
        | prim pv =>
          obtain ⟨q, rfl⟩ := copied_default_prim hc'
          have hs : step μ.heap r (.at j) = none := by
            cases hst : step μ.heap r (.at j) with
            | none => rfl
            | some c₁ =>
              have := (step_iff_readAddr μ r c₁ (.at j)).1 hst
              simp only [Addr.ofSeg, hmv] at this; cases this
          simp only [resolveR, resolveFrom, hs]
          apply Sim.halt _ (fun _ h => by cases h)
          intro u h
          cases rest with
          | nil => cases a <;> simp only [Ty.memberTy, dfltSel, Ty.at_prim, dfltWord, LTerm.eval,
              reduceCtorEq] at h
          | cons s rest =>
            simp only [Ty.memberTy, Ty.at_prim, Option.bind_none] at h
            cases a <;> simp only [dfltSel, LTerm.eval, reduceCtorEq] at h
      · have hr : ¬ Rets ((ltR (.lit (.int j)) n).eval σ) := by
          rw [ltR_rets]; rintro ⟨c', d, hc', hd', h0, h1⟩
          rw [hn] at hd'; cases hc'; cases hd'; exact hj ⟨h0, h1⟩
        have hs : step μ.heap r (.at j) = none := by
          cases hst : step μ.heap r (.at j) with
          | none => rfl
          | some c₁ =>
            obtain ⟨h0, h1, -⟩ := (copyStToM_newArr_at j hcp hx).1 _
              ((step_iff_readAddr μ r c₁ (.at j)).1 hst)
            exact absurd ⟨h0, h1⟩ hj
        simp only [resolveR, resolveFrom, hs]
        apply Sim.halt _ (fun _ h => by cases h)
        intro u h
        simp only [Res.bind_eq_ok] at h
        obtain ⟨v, hv, -⟩ := h
        exact hr ⟨v, hv⟩
  · have hR' : ∀ E, R ≠ .array E := fun E h => hR ⟨E, h⟩
    rw [newArrVal_other hR'] at hcp
    have hsel : newSel R n p a = dfltSel ((Ty.ref R).memberTy p) a := by
      cases R with
      | array E => exact absurd rfl (hR' E)
      | _ => rfl
    rw [hsel]
    exact dflt_read_sim σ ⟨μ', μ, hcp, State.HeapExt.refl μ⟩ p a

/-- A test of the object at a path below `new R(n)`, by its declared type. -/
theorem newObj_rets (σ : State) {μ' μ : State} {R : RefTy} {n : LTerm} {c : Int} {r : Nat}
    (hn : n.eval σ = .ok (.int c)) (hcp : copyStToM μ' (newArrVal R c) = .ok (μ, .ref r))
    (g : Option Ty → LTerm) (Q : Nat → Prop)
    (hg : ∀ (T : Ty) (r' : Nat) (p : List Seg), CopiedTo μ (defaultForTy T) (.ref r') →
      (Rets ((g (T.memberTy p)).eval σ) ↔ ∃ x, resolveFrom μ.heap r' p = some x ∧ Q x))
    (hprim : ∀ (q : PrimTy) (p : List Seg), ¬ Rets ((g ((Ty.prim q).memberTy p)).eval σ))
    (hroot : ∀ E, R = .array E → (Rets ((g (some (.ref (.array E)))).eval σ) ↔ Q r))
    (p : List Seg) :
    Rets ((newObj g R n p).eval σ) ↔ ∃ x, resolveFrom μ.heap r p = some x ∧ Q x := by
  by_cases hR : ∃ E, R = .array E
  · obtain ⟨E, rfl⟩ := hR
    obtain ⟨es, hroot'⟩ := newArr_root hcp
    have hx := State.HeapExt.refl μ
    match p with
    | [] =>
      simp only [newObj, resolveFrom, Option.some.injEq, exists_eq_left']
      exact hroot E rfl
    | .field f :: rest =>
      have hs : step μ.heap r (.field f) = none := by simp only [step, hroot']
      simp only [newObj, resolveFrom, hs, Rets, LTerm.eval, reduceCtorEq, exists_false,
        false_and]
    | .at j :: rest =>
      simp only [newObj]
      rw [seqL_rets, ltR_rets]
      constructor
      · rintro ⟨⟨c', d, hc', hd', h0, h1⟩, hgr⟩
        cases hc'; rw [hn] at hd'; cases hd'
        obtain ⟨mv', hmv, hc''⟩ := (copyStToM_newArr_at j hcp hx).2 h0 h1
        cases mv' with
        | ref c₁ =>
          have hs : step μ.heap r (.at j) = some c₁ :=
            (step_iff_readAddr μ r c₁ (.at j)).2 hmv
          simp only [resolveFrom, hs]
          exact (hg E c₁ rest hc'').1 hgr
        | prim pv =>
          obtain ⟨q, rfl⟩ := copied_default_prim hc''
          exact absurd hgr (hprim q rest)
      · rintro ⟨x, hxr, hQ⟩
        rw [resolveFrom_cons] at hxr
        obtain ⟨c₁, hs, hr'⟩ := hxr
        obtain ⟨h0, h1, hc''⟩ := (copyStToM_newArr_at j hcp hx).1 _
          ((step_iff_readAddr μ r c₁ (.at j)).1 hs)
        exact ⟨⟨j, c, rfl, hn, h0, h1⟩, (hg E c₁ rest hc'').2 ⟨x, hr', hQ⟩⟩
  · have hR' : ∀ E, R ≠ .array E := fun E h => hR ⟨E, h⟩
    rw [newArrVal_other hR'] at hcp
    have hsel : newObj g R n p = g ((Ty.ref R).memberTy p) := by
      cases R with
      | array E => exact absurd rfl (hR' E)
      | _ => rfl
    rw [hsel]
    exact hg (.ref R) r p ⟨μ', μ, hcp, State.HeapExt.refl μ⟩

/-! ### Soundness: a copy from storage -/

theorem LPath.ext_eval (σ : State) : (p : List Seg) → (q : LPath) →
    (q.ext p).eval σ = q.eval σ >>= fun qs => .ok (qs ++ p)
  | [], q => by
    simp only [LPath.ext, List.append_nil]
    cases q.eval σ <;> rfl
  | .field f :: r, q => by
    rw [LPath.ext, LPath.ext_eval σ r]
    simp only [LPath.eval]
    cases q.eval σ <;> simp only [bind, Except.bind, List.append_assoc, List.singleton_append]
  | .at j :: r, q => by
    rw [LPath.ext, LPath.ext_eval σ r]
    simp only [LPath.eval, LTerm.eval]
    cases q.eval σ with
    | error e => rfl
    | ok qs =>
      simp only [Res.ok_bind', Value.asInt, List.append_assoc, List.singleton_append]

theorem noLen_append {p q : List Seg} : noLen (p ++ q) = (noLen p && noLen q) := by
  simp only [noLen, List.all_append]

theorem noLen_mem {p : List Seg} (h : noLen p = true) : ∀ s ∈ p, s ≠ .field "length" := by
  intro s hs
  have := List.all_eq_true.1 h s hs
  simpa only [bne_iff_ne, ne_eq] using this

/-- The setting of a copy from storage: the storage `s` and the path `q` read
the subtree `w`, which copies to the root `r`. -/
structure CopyAt (σ μ : State) (s : LStor) (q : LPath) (r : Nat) where
  v : SVal
  qs : List Seg
  w : SVal
  μ' : State
  hv : s.eval σ = .ok v
  hq : q.eval σ = .ok qs
  hw : v.findLive qs = .ok w
  hc : copyStToM μ' w = .ok (μ, .ref r)

theorem CopyAt.find (h : CopyAt σ μ s q r) (p : List Seg) :
    s.eval σ >>= (fun v => (q.ext p).eval σ >>= fun qs => v.findLive qs) = h.w.findLive p := by
  rw [h.hv, Res.ok_bind', LPath.ext_eval, h.hq, Res.ok_bind', Res.ok_bind',
    SVal.findLive_append, h.hw, Res.ok_bind']

/-- A slot below a copy reads as its source (`readFromCopyToStorage`). -/
theorem copy_slot_sim (h : CopyAt σ μ s q r) {p : List Seg} {a : Seg}
    (hl : noLen (p ++ [a]) = true) :
    Sim (h.w.findLive (p ++ [a]) >>= SVal.asValue)
      (resolveR μ.heap r p >>= fun x => readAddr μ (.ofSeg x a) >>= MVal.asValue) := by
  have hx := State.HeapExt.refl μ
  intro u
  constructor
  · intro hu
    simp only [Res.bind_eq_ok] at hu
    obtain ⟨w', hw', hu⟩ := hu
    obtain ⟨mv', hmv, hc'⟩ := (copyStToM_readPath (p ++ [a]) h.hc hx).2 (noLen_mem hl) w' hw'
    rw [MVal.readPath_snoc, Res.bind_eq_ok] at hmv
    obtain ⟨mv₀, hp, hmv⟩ := hmv
    cases mv₀ with
    | prim _ => cases hmv
    | ref x =>
      have hres := (readPath_ref_iff μ p r x).2 hp
      obtain ⟨σ₁, σ₂, hcp, -⟩ := hc'
      simp only [resolveR, hres, Res.ok_bind', hmv, Close.copyStToM_asValue hcp, hu]
  · intro hu
    simp only [Res.bind_eq_ok] at hu
    obtain ⟨x, hx', mv', hmv, hu⟩ := hu
    have hp := (readPath_ref_iff μ p r x).1 (resolveR_ok.1 hx')
    have hfull : (MVal.ref r).readPath μ (p ++ [a]) = .ok mv' := by
      rw [MVal.readPath_snoc, hp, Res.ok_bind']; exact hmv
    obtain ⟨w', hw', σ₁, σ₂, hcp, -⟩ := (copyStToM_readPath (p ++ [a]) h.hc hx).1 _ hfull
    rw [hw', Res.ok_bind', ← Close.copyStToM_asValue hcp]
    exact hu

/-- **A read below a copy from storage** (`readFromCopyToStorage`; at `size`,
`findDefinitionSize`). -/
theorem copy_read_sim (h : CopyAt σ μ s q r) (p : List Seg) (a : LSel) {t : LTerm}
    (ht : copySel s q p a = some t) :
    Sim (t.eval σ) (resolveR μ.heap r p >>= fun x => a.read σ μ x) := by
  have hx := State.HeapExt.refl μ
  cases a with
  | fld f =>
    simp only [copySel, copySelG] at ht
    split at ht
    · rename_i hl
      cases ht
      have he : (LTerm.find s ((q.ext p).field f)).eval σ =
          h.w.findLive (p ++ [.field f]) >>= SVal.asValue := by
        rw [← h.find]
        simp only [LTerm.eval, LPath.eval, h.hv, Res.ok_bind', LPath.ext_eval, h.hq,
          List.append_assoc]
      rw [he]
      exact copy_slot_sim h hl
    · cases ht
  | idx t' =>
    simp only [copySel, copySelG] at ht
    split at ht
    · rename_i hl
      cases ht
      intro u
      simp only [LTerm.eval, LPath.eval, h.hv, Res.ok_bind', LPath.ext_eval, h.hq, LSel.read]
      cases ht' : t'.eval σ with
      | error e =>
        simp only [bind, Except.bind, reduceCtorEq, false_iff]
        cases resolveR μ.heap r p <;> simp only [reduceCtorEq, not_false_eq_true]
      | ok x =>
        cases x with
        | bool b =>
          simp only [bind, Except.bind, Value.asInt, reduceCtorEq, false_iff]
          cases resolveR μ.heap r p <;> simp only [reduceCtorEq, not_false_eq_true]
        | int j =>
          simp only [Res.ok_bind', Value.asInt]
          have hl' : noLen (p ++ [.at j]) = true := by
            rw [noLen_append, hl]; rfl
          rw [List.append_assoc, SVal.findLive_append, h.hw, Res.ok_bind']
          exact copy_slot_sim h hl' u
    · cases ht
  | size =>
    simp only [copySel, copySelG] at ht
    split at ht
    · rename_i hl
      cases ht
      have he : (LTerm.len s (q.ext p)).eval σ = h.w.findLive p >>= Close.arrLen := by
        simp only [LTerm.eval, h.hv, Res.ok_bind', LPath.ext_eval, h.hq, SVal.findLive_append,
          h.hw]
      rw [he]
      intro u
      simp only [LSel.read]
      constructor
      · intro hu
        rw [Res.bind_eq_ok] at hu
        obtain ⟨w', hw', hu⟩ := hu
        obtain ⟨mv', hmv, hc'⟩ := (copyStToM_readPath p h.hc hx).2 (noLen_mem hl) w' hw'
        have hlen : ∃ es sh fx, w' = .array es sh fx := by
          cases w' with
          | array es sh fx => exact ⟨es, sh, fx, rfl⟩
          | _ => cases hu
        obtain ⟨es, sh, fx, rfl⟩ := hlen
        obtain ⟨σ₁, σ₂, hcp, hx₂⟩ := hc'
        obtain ⟨x, rfl⟩ := copyStToM_array_ref hcp
        have hres := (readPath_ref_iff μ p r x).2 hmv
        simp only [resolveR, hres, Res.ok_bind', copiedTo_len ⟨σ₁, σ₂, hcp, hx₂⟩, hu]
      · intro hu
        rw [Res.bind_eq_ok] at hu
        obtain ⟨x, hx', hu⟩ := hu
        have hp := (readPath_ref_iff μ p r x).1 (resolveR_ok.1 hx')
        rw [← copyStToM_lenPath h.hc hx hp]
        exact hu
    · cases ht

theorem copy_obj (h : CopyAt σ μ s q r) {p : List Seg} {x : Nat}
    (hx : resolveFrom μ.heap r p = some x) : ∃ w', h.w.findLive p = .ok w' ∧ CopiedTo μ w' (.ref x) :=
  (copyStToM_readPath p h.hc (State.HeapExt.refl μ)).1 _ ((readPath_ref_iff μ p r x).1 hx)

theorem copy_obj' (h : CopyAt σ μ s q r) {p : List Seg} (hl : noLen p = true) {w' : SVal}
    (hw : h.w.findLive p = .ok w') (hp : ∀ pv, w' ≠ .prim pv) :
    ∃ x, resolveFrom μ.heap r p = some x ∧ CopiedTo μ w' (.ref x) := by
  obtain ⟨mv', hmv, hc'⟩ :=
    (copyStToM_readPath p h.hc (State.HeapExt.refl μ)).2 (noLen_mem hl) w' hw
  obtain ⟨σ₁, σ₂, hcp, hx₂⟩ := hc'
  have hr : ∃ x, mv' = .ref x := by
    cases w' with
    | prim pv => exact absurd rfl (hp pv)
    | struct fs => exact copyStToM_struct_ref hcp
    | array es sh fx => exact copyStToM_array_ref hcp
    | map e d => exact (copyStToM_map_inv hcp).elim
  obtain ⟨x, rfl⟩ := hr
  exact ⟨x, (readPath_ref_iff μ p r x).2 hmv, σ₁, σ₂, hcp, hx₂⟩

theorem copiedTo_not_prim {τ : State} {pv : PrimVal} {x : Nat} : ¬ CopiedTo τ (.prim pv) (.ref x) := by
  rintro ⟨σ₁, σ₂, hcp, -⟩
  cases (copyStToM_prim_inv hcp).2

theorem CopyAt.term_eval (h : CopyAt σ μ s q r) (p : List Seg) :
    (LTerm.find s (q.ext p)).eval σ = h.w.findLive p >>= SVal.asValue ∧
    (LTerm.has s (q.ext p)).eval σ = (h.w.findLive p >>= fun _ => .ok (.bool true)) ∧
    (LTerm.len s (q.ext p)).eval σ = h.w.findLive p >>= Close.arrLen := by
  simp only [LTerm.eval, h.hv, Res.ok_bind', LPath.ext_eval, h.hq, SVal.findLive_append, h.hw,
    and_self]

theorem ite_isT_rets (σ : State) (c b : LTerm) :
    Rets ((LTerm.ite (isT c) .err b).eval σ) ↔ ¬ Rets (c.eval σ) ∧ Rets (b.eval σ) := by
  simp only [LTerm.eval, isT_eval, Res.ok_bind']
  unfold Rets
  cases c.eval σ with
  | ok x => simp only [pickBranch, reduceCtorEq, exists_false, Except.ok.injEq,
      exists_eq', not_true_eq_false, false_and]
  | error e => simp only [pickBranch, reduceCtorEq, exists_false, not_false_eq_true, true_and]

/-- **A name below a copy from storage denotes an object** where the storage
holds a struct or an array there (`readFromCopyToStorageIdentity`). -/
theorem copy_ref_rets (h : CopyAt σ μ s q r) {p : List Seg} (hl : noLen p = true) :
    Rets ((refT s (q.ext p)).eval σ) ↔ ∃ x, resolveFrom μ.heap r p = some x := by
  obtain ⟨hf, hh, -⟩ := h.term_eval p
  unfold refT
  rw [ite_isT_rets]
  unfold Rets
  rw [hf, hh]
  cases hw : h.w.findLive p with
  | error e =>
    simp only [bind, Except.bind, reduceCtorEq, exists_false, and_false, false_iff, not_exists]
    intro x hx
    obtain ⟨w', hw', -⟩ := copy_obj h hx
    rw [hw] at hw'; cases hw'
  | ok w' =>
    simp only [Res.ok_bind', Except.ok.injEq, exists_eq', and_true]
    cases w' with
    | prim pv =>
      have hpv : ∃ v, SVal.asValue (.prim pv) = .ok v := by cases pv <;> exact ⟨_, rfl⟩
      simp only [hpv, not_true_eq_false, false_iff, not_exists]
      intro x hx
      obtain ⟨w'', hw', hc⟩ := copy_obj h hx
      rw [hw] at hw'; cases hw'
      exact copiedTo_not_prim hc
    | _ =>
      simp only [SVal.asValue, reduceCtorEq, exists_false, not_false_eq_true, true_iff]
      obtain ⟨x, hx, -⟩ := copy_obj' h hl hw (fun _ h => by cases h)
      exact ⟨x, hx⟩

theorem copy_struct_rets (h : CopyAt σ μ s q r) {p : List Seg} (hl : noLen p = true) :
    Rets ((structT s (q.ext p)).eval σ) ↔
      ∃ x fs, resolveFrom μ.heap r p = some x ∧ μ.getObj x = .ok (.struct fs) := by
  obtain ⟨-, -, hl'⟩ := h.term_eval p
  unfold structT
  rw [ite_isT_rets, copy_ref_rets h hl]
  unfold Rets
  rw [hl']
  constructor
  · rintro ⟨hna, x, hx⟩
    obtain ⟨w'', hw', hc⟩ := copy_obj h hx
    rcases copiedTo_ref_obj hc with ⟨_, mfs, -, hobj⟩ | ⟨_, _, _, _, rfl, -, -⟩
    · exact ⟨x, mfs, hx, by simp only [State.getObj, hobj]⟩
    · exact absurd ⟨_, by rw [hw', Res.ok_bind']; rfl⟩ hna
  · rintro ⟨x, fs, hx, hfs⟩
    refine ⟨?_, x, hx⟩
    rintro ⟨v, hv⟩
    obtain ⟨w'', hw', hc⟩ := copy_obj h hx
    rw [hw', Res.ok_bind'] at hv
    rcases copiedTo_ref_obj hc with ⟨_, _, rfl, -⟩ | ⟨_, _, _, _, -, hobj, -⟩
    · cases hv
    · simp only [State.getObj, hobj, Except.ok.injEq, reduceCtorEq] at hfs

/-! ### Soundness: the readers -/

/-- A read of a name older than an allocation is the read before it. -/
theorem alloc_frame {σ μ' : State} {B' : Births} {b : Birth} {i : LId}
    (hB : B'.Ok σ.nextId μ') (hk : i.root ≠ B'.length) {β : Type} (F G : Nat → Res β)
    (hF : ∀ n, n < μ'.nextId → F n = G n) :
    (LId.evalR (B' ++ [b]) i >>= F) = (LId.evalR B' i >>= G) := by
  unfold LId.evalR
  rw [Births.eval_snoc_ne hk]
  cases he : B'.eval i.root i.path with
  | none => rfl
  | some n =>
    obtain ⟨_, _, _, _, _, hn⟩ := Births.eval_interval hB he
    simp only [Res.ok_bind', hF n hn]

/-- Two names of one run are one object exactly when they are one name. -/
theorem evalR_ne {σ μ : State} {B : Births} (hB : B.Ok σ.nextId μ) {i j : LId} (hij : i ≠ j)
    {n n' : Nat} (hi : LId.evalR B i = .ok n) (hj : LId.evalR B j = .ok n') : n ≠ n' := by
  rintro rfl
  obtain ⟨h₁, h₂⟩ := Births.eval_inj hB (LId.evalR_ok.1 hi) (LId.evalR_ok.1 hj)
  exact hij (by cases i; cases j; simp only at h₁ h₂; subst h₁ h₂; rfl)

theorem LSel.addr_id {σ : State} {n : Nat} {b : LSel} {ad : Addr} (h : b.addr σ n = .ok ad) :
    ad.id = n := by
  cases b with
  | fld f => cases h; rfl
  | idx t =>
    simp only [LSel.addr, Res.bind_eq_ok] at h
    obtain ⟨_, _, h⟩ := h
    cases h; rfl
  | size => cases h

theorem selRel_same {σ μ : State} {n : Nat} {b a : LSel} {ad : Addr} (h : selRel b a = .same)
    (hb : b.addr σ n = .ok ad) : a.read σ μ n = readAddr μ ad >>= MVal.asValue := by
  cases b with
  | fld f =>
    cases a with
    | fld g =>
      simp only [selRel] at h
      split at h
      · rename_i hfg; subst hfg; cases hb; rfl
      · cases h
    | _ => simp only [selRel, reduceCtorEq] at h
  | idx w =>
    cases a with
    | idx r =>
      simp only [selRel] at h
      split at h
      · rename_i c d
        split at h
        · rename_i hcd
          subst hcd
          simp only [LSel.addr, LTerm.eval, Res.ok_bind', Value.asInt] at hb
          cases hb; rfl
        · cases h
      · cases h
    | _ => simp only [selRel, reduceCtorEq] at h
  | size => cases hb

theorem selRel_apart {σ μ μ' : State} {n : Nat} {b a : LSel} {ad : Addr} {mv : MVal}
    (h : selRel b a = .apart) (hb : b.addr σ n = .ok ad) (hw : writeAddr μ' mv ad = .ok μ) :
    a.read σ μ n = a.read σ μ' n := by
  obtain ⟨_, _, _, hfr⟩ := Close.writeAddr_setObj hw
  cases a with
  | size => exact memArrayLen_writeAddr hw n
  | fld g =>
    have hap : Close.Apart ad (.memoryField n g) := by
      cases b with
      | fld f =>
        cases hb
        simp only [selRel] at h
        split at h
        · cases h
        · rename_i hfg
          exact Or.inr (Ne.symm hfg)
      | idx w =>
        simp only [LSel.addr, Res.bind_eq_ok] at hb
        obtain ⟨_, _, hb⟩ := hb
        cases hb; trivial
      | size => cases hb
    simp only [LSel.read, hfr _ hap]
  | idx r =>
    cases b with
    | fld f =>
      cases hb
      simp only [LSel.read]
      congr 1; funext j; congr 1
      exact hfr _ trivial
    | idx w =>
      simp only [selRel] at h
      split at h
      · rename_i c d
        split at h
        · cases h
        · rename_i hcd
          simp only [LSel.addr, LTerm.eval, Res.ok_bind', Value.asInt] at hb
          cases hb
          simp only [LSel.read, LTerm.eval, Res.ok_bind', Value.asInt]
          exact congrArg (· >>= MVal.asValue) (hfr _ (Or.inr hcd))
      · cases h
    | size => cases hb

theorem selRel_key {b a : LSel} {r w : LTerm} (h : selRel b a = .key r w) :
    b = .idx w ∧ a = .idx r := by
  cases b with
  | fld f =>
    cases a with
    | fld g => simp only [selRel] at h; split at h <;> cases h
    | _ => simp only [selRel, reduceCtorEq] at h
  | idx w' =>
    cases a with
    | idx r' =>
      simp only [selRel] at h
      split at h
      · split at h <;> cases h
      · cases h; exact ⟨rfl, rfl⟩
    | _ => simp only [selRel, reduceCtorEq] at h
  | size => cases a <;> simp only [selRel, reduceCtorEq] at h

theorem LMV.wordT_sim {σ : State} {B : Births} {v : LMV} {mv : MVal} (h : v.eval σ B = .ok mv) :
    Sim (v.wordT.eval σ) mv.asValue := by
  cases v with
  | word t =>
    simp only [LMV.eval, Res.bind_eq_ok, Except.ok.injEq] at h
    obtain ⟨x, hx, rfl⟩ := h
    simp only [LMV.wordT, hx, asValue_toMVal]
    exact Sim.refl _
  | ref j =>
    simp only [LMV.eval, Res.bind_eq_ok, Except.ok.injEq] at h
    obtain ⟨x, -, rfl⟩ := h
    exact Sim.halt (fun _ h => by cases h) (fun _ h => by cases h)

/-- What a run's step leaves, by the kind of the step. -/
theorem LMem.run_addM {σ μ : State} {B : Births} {m : LMem} {k : Nat} {R : RefTy}
    (h : (LMem.addM m k R).run σ = .ok (μ, B)) : ∃ μ' B' id, m.run σ = .ok (μ', B') ∧
      k = B'.length ∧ copyStToM μ' (defaultForTy (.ref R)) = .ok (μ, .ref id) ∧
      B = B' ++ [Birth.ofCopy μ' μ id] := by
  simp only [LMem.run, Res.bind_eq_ok] at h
  obtain ⟨⟨μ', B'⟩, hr, h⟩ := h
  split at h
  · rename_i hk
    simp only [Res.bind_eq_ok] at h
    obtain ⟨a, ha, h⟩ := h
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨μ', B', a.2, hr, hk, Close.allocDefault_copy ha, rfl⟩
  · cases h

theorem LMem.run_newArr {σ μ : State} {B : Births} {m : LMem} {k : Nat} {R : RefTy} {n : LTerm}
    (h : (LMem.newArr m k R n).run σ = .ok (μ, B)) : ∃ μ' B' id c, m.run σ = .ok (μ', B') ∧
      k = B'.length ∧ n.eval σ = .ok (.int c) ∧ copyStToM μ' (newArrVal R c) = .ok (μ, .ref id) ∧
      B = B' ++ [Birth.ofCopy μ' μ id] := by
  simp only [LMem.run, Res.bind_eq_ok] at h
  obtain ⟨c, ⟨x, hx, hc⟩, ⟨μ', B'⟩, hr, h⟩ := h
  have hn : n.eval σ = .ok (.int c) := by
    cases x with
    | int c' => cases hc; exact hx
    | bool _ => cases hc
  split at h
  · rename_i hk
    simp only [Res.bind_eq_ok] at h
    obtain ⟨a, ha, id, hid, h⟩ := h
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨μ', B', id, c, hr, hk, hn, by rw [ha, ← asRef_ok hid], rfl⟩
  · cases h

theorem LMem.run_copySt {σ μ : State} {B : Births} {m : LMem} {k : Nat} {s : LStor} {q : LPath}
    (h : (LMem.copySt m k s q).run σ = .ok (μ, B)) : ∃ μ' B' id, m.run σ = .ok (μ', B') ∧
      k = B'.length ∧ (∃ c : CopyAt σ μ s q id, c.μ' = μ') ∧
      B = B' ++ [Birth.ofCopy μ' μ id] := by
  simp only [LMem.run, Res.bind_eq_ok] at h
  obtain ⟨v, hv, qs, hq, w, hw, ⟨μ', B'⟩, hr, h⟩ := h
  split at h
  · rename_i hk
    simp only [Res.bind_eq_ok] at h
    obtain ⟨a, ha, id, hid, h⟩ := h
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨μ', B', id, hr, hk, ⟨⟨v, qs, w, μ', hv, hq, hw, by rw [ha, ← asRef_ok hid]⟩, rfl⟩, rfl⟩
  · cases h

theorem LMem.run_write {σ μ : State} {B : Births} {m : LMem} {j : LId} {b : LSel} {v : LMV}
    (h : (LMem.write m j b v).run σ = .ok (μ, B)) : ∃ μ' n' ad mv, m.run σ = .ok (μ', B) ∧
      LId.evalR B j = .ok n' ∧ b.addr σ n' = .ok ad ∧ v.eval σ B = .ok mv ∧
      writeAddr μ' mv ad = .ok μ := by
  simp only [LMem.run, Res.bind_eq_ok] at h
  obtain ⟨⟨μ', B'⟩, hr, n', hn', ad, had, mv, hmv, μ₁, hw, h⟩ := h
  simp only [Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨μ', n', ad, mv, hr, hn', had, hmv, hw⟩

/-- **A read of memory is the term `readT` gives**: under the run of the
memory, the term returns what the interpreter's read of the slot does. -/
theorem LMem.readT_sim (σ : State) : (m : LMem) → ∀ {μ : State} {B : Births} (i : LId) (a : LSel)
    {t : LTerm}, m.run σ = .ok (μ, B) → m.readT i a = some t →
    Sim (t.eval σ) (LId.evalR B i >>= fun n => a.read σ μ n)
  | .init, _, _, _, _, _, _, ht => by simp only [LMem.readT, reduceCtorEq] at ht
  | .addM m k R, μ, B, i, a, t, h, ht => by
    obtain ⟨μ', B', id, hr, rfl, hc, rfl⟩ := LMem.run_addM h
    simp only [LMem.readT] at ht
    split at ht
    · rename_i hk
      cases ht
      rw [evalR_last B' _ hk]
      exact dflt_read_sim σ ⟨μ', μ, hc, State.HeapExt.refl μ⟩ i.path a
    · rename_i hk
      rw [alloc_frame (LMem.run_births σ m hr) hk _ (fun n => a.read σ μ' n)
        (fun n hn => LSel.read_heapExt (copyStToM_heapExt μ' _ _ _ hc) hn a)]
      exact LMem.readT_sim σ m i a hr ht
  | .newArr m k R n, μ, B, i, a, t, h, ht => by
    obtain ⟨μ', B', id, c, hr, rfl, hn, hc, rfl⟩ := LMem.run_newArr h
    simp only [LMem.readT] at ht
    split at ht
    · rename_i hk
      cases ht
      rw [evalR_last B' _ hk]
      exact new_read_sim σ hn hc i.path a
    · rename_i hk
      rw [alloc_frame (LMem.run_births σ m hr) hk _ (fun n => a.read σ μ' n)
        (fun n hn => LSel.read_heapExt (copyStToM_heapExt μ' _ _ _ hc) hn a)]
      exact LMem.readT_sim σ m i a hr ht
  | .copySt m k s q, μ, B, i, a, t, h, ht => by
    obtain ⟨μ', B', id, hr, rfl, ⟨hcp, rfl⟩, rfl⟩ := LMem.run_copySt h
    simp only [LMem.readT] at ht
    split at ht
    · rename_i hk
      rw [evalR_last B' _ hk]
      exact copy_read_sim hcp i.path a ht
    · rename_i hk
      rw [alloc_frame (LMem.run_births σ m hr) hk _ (fun n => a.read σ hcp.μ' n)
        (fun n hn => LSel.read_heapExt (copyStToM_heapExt _ _ _ _ hcp.hc) hn a)]
      exact LMem.readT_sim σ m i a hr ht
  | .write m j b v, μ, B, i, a, t, h, ht => by
    obtain ⟨μ', n', ad, mv, hr, hn', hb, hv, hw⟩ := LMem.run_write h
    have hB := LMem.run_births σ m hr
    simp only [LMem.readT] at ht
    split at ht
    · rename_i hij
      subst hij
      rw [hn', Res.ok_bind']
      split at ht
      · rename_i hs
        cases ht
        rw [selRel_same hs hb, Close.readAddr_writeAddr_same hw, Res.ok_bind']
        exact LMV.wordT_sim hv
      · rename_i hs
        rw [selRel_apart hs hb hw]
        have ih := LMem.readT_sim σ m i a hr ht
        rw [hn', Res.ok_bind'] at ih
        exact ih
      · rename_i r w hs
        obtain ⟨rfl, rfl⟩ := selRel_key hs
        simp only [Option.map_eq_some_iff] at ht
        obtain ⟨t', ht', rfl⟩ := ht
        have ih := LMem.readT_sim σ m i (.idx r) hr ht'
        rw [hn', Res.ok_bind'] at ih
        simp only [LSel.addr, Res.bind_eq_ok] at hb
        obtain ⟨d, ⟨wv, hwv, hd⟩, hb⟩ := hb
        cases hb
        have hwi : w.eval σ = .ok (.int d) := by
          cases wv with
          | int d' => cases hd; exact hwv
          | bool _ => cases hd
        obtain ⟨_, _, _, hfr⟩ := Close.writeAddr_setObj hw
        intro u
        simp only [LTerm.eval, hwi, Res.ok_bind', Value.asInt, LSel.read] at ih ⊢
        cases hre : r.eval σ with
        | error e =>
          simp only [bind, Except.bind, reduceCtorEq]
        | ok x =>
          cases x with
          | bool _ => simp only [Value.asInt, bind, Except.bind, reduceCtorEq]
          | int c =>
            simp only [hre, Res.ok_bind', Value.asInt] at ih ⊢
            by_cases hcd : c = d
            · subst hcd
              simp only [if_true, Close.readAddr_writeAddr_same hw, Res.ok_bind']
              exact LMV.wordT_sim hv u
            · simp only [hcd, if_false, hfr (.memoryIndex n' c) (Or.inr hcd)]
              exact ih u
    · rename_i hij
      have ih := LMem.readT_sim σ m i a hr ht
      refine Sim.trans ih (Sim.of_eq ?_)
      cases hi : LId.evalR B i with
      | error e => rfl
      | ok n =>
        simp only [Res.ok_bind']
        exact (LSel.read_write_ne hw (by rw [LSel.addr_id hb]; exact
          (evalR_ne hB hij hi hn').symm) a).symm

theorem LSel.seg_iread {σ μ : State} {n : Nat} {a : LSel} {sg : Seg} (h : a.seg? = some sg) :
    a.iread σ μ n = readAddr μ (.ofSeg n sg) >>= MVal.asRef := by
  cases a with
  | fld f => cases h; rfl
  | idx t =>
    unfold LSel.seg? at h
    split at h
    · rename_i heq; cases heq
    · rename_i j heq; cases heq; cases h; rfl
    · cases h
  | size => cases h

/-- A reference slot below a name is the name one segment longer, read in its
birth heap (`MemNames.birth_slot`). -/
theorem resolveR_snoc_sim (μ : State) (r : Nat) (p : List Seg) (sg : Seg) :
    Sim (resolveR μ.heap r (p ++ [sg]))
      (resolveR μ.heap r p >>= fun n => readAddr μ (.ofSeg n sg) >>= MVal.asRef) := by
  intro m'
  rw [resolveR_ok, resolveFrom_append, Res.bind_eq_ok]
  constructor
  · intro h
    cases hp : resolveFrom μ.heap r p with
    | none => rw [hp] at h; cases h
    | some n =>
      rw [hp, Option.bind_some, resolveFrom_cons] at h
      obtain ⟨c, hs, hc⟩ := h
      simp only [resolveFrom, Option.some.injEq] at hc
      subst hc
      refine ⟨n, resolveR_ok.2 hp, ?_⟩
      rw [(step_iff_readAddr μ n c sg).1 hs]; rfl
  · rintro ⟨n, hn, h⟩
    rw [resolveR_ok.1 hn, Option.bind_some, resolveFrom_cons]
    rw [Res.bind_eq_ok] at h
    obtain ⟨mv, hmv, h⟩ := h
    cases mv with
    | ref c =>
      simp only [MVal.asRef, pure, Except.pure, Except.ok.injEq] at h
      subst h
      exact ⟨c, (step_iff_readAddr μ n c sg).2 hmv, rfl⟩
    | prim _ => cases h

theorem selRel_same_addr {σ : State} {n : Nat} {b a : LSel} {ad : Addr} (h : selRel b a = .same)
    (hb : b.addr σ n = .ok ad) : a.addr σ n = .ok ad := by
  cases b with
  | fld f =>
    cases a with
    | fld g =>
      simp only [selRel] at h
      split at h
      · rename_i hfg; subst hfg; exact hb
      · cases h
    | _ => simp only [selRel, reduceCtorEq] at h
  | idx w =>
    cases a with
    | idx r =>
      simp only [selRel] at h
      split at h
      · rename_i c d
        split at h
        · rename_i hcd
          subst hcd
          simp only [LSel.addr, LTerm.eval, Res.ok_bind', Value.asInt] at hb ⊢
          exact hb
        · cases h
      · cases h
    | _ => simp only [selRel, reduceCtorEq] at h
  | size => cases hb

theorem selRel_apart_iread {σ μ μ' : State} {n : Nat} {b a : LSel} {ad : Addr} {mv : MVal}
    (h : selRel b a = .apart) (hb : b.addr σ n = .ok ad) (hw : writeAddr μ' mv ad = .ok μ) :
    a.iread σ μ n = a.iread σ μ' n := by
  obtain ⟨_, _, _, hfr⟩ := Close.writeAddr_setObj hw
  unfold LSel.iread
  cases a with
  | size => rfl
  | fld g =>
    have hap : Close.Apart ad (.memoryField n g) := by
      cases b with
      | fld f =>
        cases hb
        simp only [selRel] at h
        split at h
        · cases h
        · rename_i hfg
          exact Or.inr (Ne.symm hfg)
      | idx w =>
        simp only [LSel.addr, Res.bind_eq_ok] at hb
        obtain ⟨_, _, hb⟩ := hb
        cases hb; trivial
      | size => cases hb
    simp only [LSel.addr, Res.ok_bind', hfr _ hap]
  | idx r =>
    cases b with
    | fld f =>
      cases hb
      simp only [LSel.addr]
      cases r.eval σ >>= Value.asInt with
      | error e => rfl
      | ok j => simp only [Res.ok_bind', hfr (.memoryIndex n j) trivial]
    | idx w =>
      simp only [selRel] at h
      split at h
      · rename_i c d
        split at h
        · cases h
        · rename_i hcd
          simp only [LSel.addr, LTerm.eval, Res.ok_bind', Value.asInt] at hb ⊢
          cases hb
          simp only [hfr (.memoryIndex n c) (Or.inr hcd)]
      · cases h
    | size => cases hb

theorem evalR_root_lt {B : Births} {j : LId} {x : Nat} (h : LId.evalR B j = .ok x) :
    j.root < B.length := by
  obtain ⟨b, hb, -⟩ := Births.eval_some (LId.evalR_ok.1 h)
  exact (List.getElem?_eq_some_iff.1 hb).1

theorem readI_alloc (σ : State) {m : LMem} {μ' μ : State} {B' : Births} {id k : Nat}
    (hr : m.run σ = .ok (μ', B')) (hk : k = B'.length) (hx : μ'.HeapExt μ)
    (ih : ∀ (i : LId) (a : LSel) {j : LId}, m.readI i a = some j →
      (j.root = i.root ∨ j.root < B'.length) ∧
        Sim (LId.evalR B' j) (LId.evalR B' i >>= fun n => a.iread σ μ' n))
    (i : LId) (a : LSel) {j : LId}
    (hj : (if i.root = k then a.seg?.map i.extend else m.readI i a) = some j) :
    (j.root = i.root ∨ j.root < (B' ++ [Birth.ofCopy μ' μ id]).length) ∧
      Sim (LId.evalR (B' ++ [Birth.ofCopy μ' μ id]) j)
        (LId.evalR (B' ++ [Birth.ofCopy μ' μ id]) i >>= fun n => a.iread σ μ n) := by
  subst hk
  split at hj
  · rename_i hk
    simp only [Option.map_eq_some_iff] at hj
    obtain ⟨sg, hsg, rfl⟩ := hj
    refine ⟨.inl rfl, ?_⟩
    rw [evalR_last B' _ (i := i.extend sg) hk, evalR_last B' _ hk]
    simp only [LSel.seg_iread hsg]
    exact resolveR_snoc_sim μ id i.path sg
  · rename_i hk
    obtain ⟨hroot, hsim⟩ := ih i a hj
    have hjk : j.root ≠ B'.length := by
      rcases hroot with h | h
      · rw [h]; exact hk
      · exact Nat.ne_of_lt h
    refine ⟨hroot.imp (fun h => h) (fun h => by simp only [List.length_append, List.length_singleton]; omega),
      ?_⟩
    have hj' : LId.evalR (B' ++ [Birth.ofCopy μ' μ id]) j = LId.evalR B' j := by
      unfold LId.evalR; rw [Births.eval_snoc_ne hjk]
    rw [hj', alloc_frame (LMem.run_births σ m hr) hk _ (fun n => a.iread σ μ' n)
      (fun n hn => LSel.iread_heapExt hx hn a)]
    exact hsim

/-- **The object a reference slot names is the name `readI` gives**
(`initIdentity`, `readFromCopyToStorageIdentity`, `readOnWrite`). -/
theorem LMem.readI_sim (σ : State) : (m : LMem) → ∀ {μ : State} {B : Births} (i : LId) (a : LSel)
    {j : LId}, m.run σ = .ok (μ, B) → m.readI i a = some j →
    (j.root = i.root ∨ j.root < B.length) ∧
      Sim (LId.evalR B j) (LId.evalR B i >>= fun n => a.iread σ μ n)
  | .init, _, _, _, _, _, _, hj => by simp only [LMem.readI, reduceCtorEq] at hj
  | .addM m k R, μ, B, i, a, j, h, hj => by
    obtain ⟨μ', B', id, hr, rfl, hc, rfl⟩ := LMem.run_addM h
    exact readI_alloc σ hr rfl (copyStToM_heapExt μ' _ _ _ hc)
      (fun i a {_} hj => LMem.readI_sim σ m i a hr hj) i a hj
  | .newArr m k R n, μ, B, i, a, j, h, hj => by
    obtain ⟨μ', B', id, c, hr, rfl, -, hc, rfl⟩ := LMem.run_newArr h
    exact readI_alloc σ hr rfl (copyStToM_heapExt μ' _ _ _ hc)
      (fun i a {_} hj => LMem.readI_sim σ m i a hr hj) i a hj
  | .copySt m k s q, μ, B, i, a, j, h, hj => by
    obtain ⟨μ', B', id, hr, rfl, ⟨hcp, rfl⟩, rfl⟩ := LMem.run_copySt h
    exact readI_alloc σ hr rfl (copyStToM_heapExt _ _ _ _ hcp.hc)
      (fun i a {_} hj => LMem.readI_sim σ m i a hr hj) i a hj
  | .write m j₀ b v, μ, B, i, a, j, h, hj => by
    obtain ⟨μ', n', ad, mv, hr, hn', hb, hv, hw⟩ := LMem.run_write h
    have hB := LMem.run_births σ m hr
    simp only [LMem.readI] at hj
    split at hj
    · rename_i hij
      subst hij
      split at hj
      · rename_i hs
        cases hj
        simp only [LMV.eval, Res.bind_eq_ok, Except.ok.injEq] at hv
        obtain ⟨x, hx, rfl⟩ := hv
        refine ⟨.inr (evalR_root_lt hx), ?_⟩
        rw [hx, hn', Res.ok_bind']
        simp only [LSel.iread, selRel_same_addr hs hb, Res.ok_bind',
          Close.readAddr_writeAddr_same hw]
        exact Sim.refl _
      · rename_i hs
        obtain ⟨hroot, hsim⟩ := LMem.readI_sim σ m i a hr hj
        refine ⟨hroot, ?_⟩
        rw [hn', Res.ok_bind', selRel_apart_iread hs hb hw]
        rw [hn', Res.ok_bind'] at hsim
        exact hsim
      · cases hj
    · rename_i hij
      obtain ⟨hroot, hsim⟩ := LMem.readI_sim σ m i a hr hj
      refine ⟨hroot, Sim.trans hsim (Sim.of_eq ?_)⟩
      cases hi : LId.evalR B i with
      | error e => rfl
      | ok n =>
        simp only [Res.ok_bind']
        exact (LSel.iread_write_ne hw (by rw [LSel.addr_id hb]; exact
          (evalR_ne hB hij hi hn').symm) a).symm

/-! ### Soundness: the guards of names and writes -/

theorem evalR_snoc_ne {B : Births} {b : Birth} {i : LId} (hk : i.root ≠ B.length) :
    LId.evalR (B ++ [b]) i = LId.evalR B i := by
  unfold LId.evalR; rw [Births.eval_snoc_ne hk]

theorem struct_iff_objKind (μ : State) (n : Nat) :
    (∃ fs, μ.getObj n = .ok (.struct fs)) ↔ objKind μ n = .ok none := by
  unfold objKind
  cases μ.getObj n with
  | error e => simp only [reduceCtorEq, exists_false, bind, Except.bind]
  | ok o =>
    cases o with
    | struct fs => simp only [Res.ok_bind', Except.ok.injEq, MObj.struct.injEq, exists_eq']
    | array es fx => simp only [Res.ok_bind', Except.ok.injEq, reduceCtorEq, exists_false]

theorem dfltRef_prim (σ : State) (q : PrimTy) (p : List Seg) :
    ¬ Rets ((dfltRef ((Ty.prim q).memberTy p)).eval σ) := by
  rintro ⟨v, hv⟩
  cases p with
  | nil => simp only [Ty.memberTy, dfltRef, LTerm.eval, reduceCtorEq] at hv
  | cons s p => simp only [Ty.memberTy, Ty.at_prim, Option.bind_none, dfltRef, LTerm.eval,
      reduceCtorEq] at hv

theorem dfltStruct_prim (σ : State) (q : PrimTy) (p : List Seg) :
    ¬ Rets ((dfltStruct ((Ty.prim q).memberTy p)).eval σ) := by
  rintro ⟨v, hv⟩
  cases p with
  | nil => simp only [Ty.memberTy, dfltStruct, LTerm.eval, reduceCtorEq] at hv
  | cons s p => simp only [Ty.memberTy, Ty.at_prim, Option.bind_none, dfltStruct, LTerm.eval,
      reduceCtorEq] at hv

/-- An allocation leaves which older objects are structs. -/
theorem structG_alloc {σ μ' μ : State} {B' : Births} {i : LId} (hB : B'.Ok σ.nextId μ')
    (hx : μ'.HeapExt μ) :
    (∃ n fs, LId.evalR B' i = .ok n ∧ μ'.getObj n = .ok (.struct fs)) ↔
      (∃ n fs, LId.evalR B' i = .ok n ∧ μ.getObj n = .ok (.struct fs)) := by
  constructor
  · rintro ⟨n, fs, hn, hfs⟩
    obtain ⟨_, _, _, _, _, hlt⟩ := Births.eval_interval hB (LId.evalR_ok.1 hn)
    exact ⟨n, fs, hn, by rw [State.getObj_heapExt hx hlt]; exact hfs⟩
  · rintro ⟨n, fs, hn, hfs⟩
    obtain ⟨_, _, _, _, _, hlt⟩ := Births.eval_interval hB (LId.evalR_ok.1 hn)
    exact ⟨n, fs, hn, by rw [← State.getObj_heapExt hx hlt]; exact hfs⟩

/-- **A name denotes an object exactly where `nameG` returns.** -/
theorem LMem.nameG_sim (σ : State) : (m : LMem) → ∀ {μ : State} {B : Births} (i : LId) {g : LTerm},
    m.run σ = .ok (μ, B) → m.nameG i = some g → (Rets (g.eval σ) ↔ ∃ n, LId.evalR B i = .ok n)
  | .init, _, _, _, _, _, hg => by simp only [LMem.nameG, reduceCtorEq] at hg
  | .addM m k R, μ, B, i, g, h, hg => by
    obtain ⟨μ', B', id, hr, rfl, hc, rfl⟩ := LMem.run_addM h
    simp only [LMem.nameG] at hg
    split at hg
    · rename_i hk
      cases hg
      rw [evalR_last B' _ hk, dfltRef_rets σ ⟨μ', μ, hc, State.HeapExt.refl μ⟩ i.path]
      simp only [resolveR_ok, Birth.ofCopy]
    · rename_i hk
      rw [evalR_snoc_ne hk]
      exact LMem.nameG_sim σ m i hr hg
  | .newArr m k R n, μ, B, i, g, h, hg => by
    obtain ⟨μ', B', id, c, hr, rfl, hn, hc, rfl⟩ := LMem.run_newArr h
    simp only [LMem.nameG] at hg
    split at hg
    · rename_i hk
      cases hg
      rw [evalR_last B' _ hk]
      simp only [resolveR_ok]
      have := newObj_rets σ hn hc dfltRef (fun _ => True)
        (fun T r' p hc' => by rw [dfltRef_rets σ hc' p]; simp only [and_true])
        (dfltRef_prim σ) (fun E _ => by
          simp only [dfltRef, Rets, LTerm.eval, Except.ok.injEq, exists_eq'])
        i.path
      simp only [and_true] at this
      exact this
    · rename_i hk
      rw [evalR_snoc_ne hk]
      exact LMem.nameG_sim σ m i hr hg
  | .copySt m k s q, μ, B, i, g, h, hg => by
    obtain ⟨μ', B', id, hr, rfl, ⟨hcp, rfl⟩, rfl⟩ := LMem.run_copySt h
    simp only [LMem.nameG] at hg
    split at hg
    · rename_i hk
      split at hg
      · rename_i hl
        cases hg
        rw [evalR_last B' _ hk, copy_ref_rets hcp hl]
        simp only [resolveR_ok, Birth.ofCopy]
      · cases hg
    · rename_i hk
      rw [evalR_snoc_ne hk]
      exact LMem.nameG_sim σ m i hr hg
  | .write m j b v, μ, B, i, g, h, hg => by
    obtain ⟨μ', n', ad, mv, hr, -, -, -, -⟩ := LMem.run_write h
    exact LMem.nameG_sim σ m i hr hg

/-- **A name denotes a struct exactly where `structG` returns**: what a member
write needs. -/
theorem LMem.structG_sim (σ : State) : (m : LMem) → ∀ {μ : State} {B : Births} (i : LId)
    {g : LTerm}, m.run σ = .ok (μ, B) → m.structG i = some g →
    (Rets (g.eval σ) ↔ ∃ n fs, LId.evalR B i = .ok n ∧ μ.getObj n = .ok (.struct fs))
  | .init, _, _, _, _, _, hg => by simp only [LMem.structG, reduceCtorEq] at hg
  | .addM m k R, μ, B, i, g, h, hg => by
    obtain ⟨μ', B', id, hr, rfl, hc, rfl⟩ := LMem.run_addM h
    simp only [LMem.structG] at hg
    split at hg
    · rename_i hk
      cases hg
      rw [evalR_last B' _ hk, dfltStruct_rets σ ⟨μ', μ, hc, State.HeapExt.refl μ⟩ i.path]
      simp only [resolveR_ok, Birth.ofCopy]
    · rename_i hk
      rw [evalR_snoc_ne hk, LMem.structG_sim σ m i hr hg]
      exact structG_alloc (LMem.run_births σ m hr) (copyStToM_heapExt μ' _ _ _ hc)
  | .newArr m k R n, μ, B, i, g, h, hg => by
    obtain ⟨μ', B', id, c, hr, rfl, hn, hc, rfl⟩ := LMem.run_newArr h
    simp only [LMem.structG] at hg
    split at hg
    · rename_i hk
      cases hg
      rw [evalR_last B' _ hk]
      simp only [resolveR_ok]
      have := newObj_rets σ hn hc dfltStruct (fun x => ∃ fs, μ.getObj x = .ok (.struct fs))
        (fun T r' p hc' => by rw [dfltStruct_rets σ hc' p]; simp only [exists_and_left])
        (dfltStruct_prim σ) (fun E hR => by
          subst hR
          obtain ⟨es, hroot⟩ := newArr_root hc
          simp only [dfltStruct, Rets, LTerm.eval, reduceCtorEq, exists_false, false_iff,
            not_exists, State.getObj, hroot]
          intro fs h; cases h)
        i.path
      simp only [exists_and_left] at this ⊢
      exact this
    · rename_i hk
      rw [evalR_snoc_ne hk, LMem.structG_sim σ m i hr hg]
      exact structG_alloc (LMem.run_births σ m hr) (copyStToM_heapExt μ' _ _ _ hc)
  | .copySt m k s q, μ, B, i, g, h, hg => by
    obtain ⟨μ', B', id, hr, rfl, ⟨hcp, rfl⟩, rfl⟩ := LMem.run_copySt h
    simp only [LMem.structG] at hg
    split at hg
    · rename_i hk
      split at hg
      · rename_i hl
        cases hg
        rw [evalR_last B' _ hk, copy_struct_rets hcp hl]
        simp only [resolveR_ok, Birth.ofCopy]
      · cases hg
    · rename_i hk
      rw [evalR_snoc_ne hk, LMem.structG_sim σ m i hr hg]
      exact structG_alloc (LMem.run_births σ m hr) (copyStToM_heapExt _ _ _ _ hcp.hc)
  | .write m j b v, μ, B, i, g, h, hg => by
    obtain ⟨μ', n', ad, mv, hr, -, -, -, hw⟩ := LMem.run_write h
    rw [LMem.structG_sim σ m i hr hg]
    constructor
    · rintro ⟨n, fs, hn, hfs⟩
      obtain ⟨fs', hfs'⟩ := (struct_iff_objKind μ n).2
        ((objKind_writeAddr hw n).symm ▸ (struct_iff_objKind μ' n).1 ⟨fs, hfs⟩)
      exact ⟨n, fs', hn, hfs'⟩
    · rintro ⟨n, fs, hn, hfs⟩
      obtain ⟨fs', hfs'⟩ := (struct_iff_objKind μ' n).2
        ((objKind_writeAddr hw n) ▸ (struct_iff_objKind μ n).1 ⟨fs, hfs⟩)
      exact ⟨n, fs', hn, hfs'⟩

theorem writeField_ok (μ : State) (mv : MVal) (n : Nat) (f : Name) :
    (∃ μ₁, writeAddr μ mv (.memoryField n f) = .ok μ₁) ↔ ∃ fs, μ.getObj n = .ok (.struct fs) := by
  simp only [writeAddr, memWriteField]
  cases μ.getObj n with
  | error e => simp only [bind, Except.bind, reduceCtorEq, exists_false]
  | ok o =>
    cases o with
    | struct fs => simp only [Res.ok_bind', Except.ok.injEq, exists_eq', MObj.struct.injEq]
    | array es fx => simp only [Res.ok_bind', reduceCtorEq, exists_false, Except.ok.injEq]

theorem writeIndex_ok (μ : State) (mv : MVal) (n : Nat) (c : Int) :
    (∃ μ₁, writeAddr μ mv (.memoryIndex n c) = .ok μ₁) ↔
      ∃ d, memArrayLen μ n = .ok (.int d) ∧ 0 ≤ c ∧ c < d := by
  simp only [writeAddr, memWriteIndex, memArrayLen]
  cases μ.getObj n with
  | error e => simp only [bind, Except.bind, reduceCtorEq, exists_false, false_and]
  | ok o =>
    cases o with
    | struct fs => simp only [Res.ok_bind', reduceCtorEq, exists_false, false_and]
    | array es fx =>
      simp only [Res.ok_bind', pure, Except.pure, Except.ok.injEq, PrimVal.int.injEq,
        exists_eq_left']
      by_cases hc : 0 ≤ c ∧ c.toNat < es.length
      · simp only [hc, and_self, if_true, Except.ok.injEq, exists_eq', true_and, true_iff]
        omega
      · simp only [hc, if_false, reduceCtorEq, exists_false, false_iff, not_and, Int.not_lt]
        omega

/-- **A write returns exactly where `writeG` does** (Lean only): a member in a
struct, an element below the length. -/
theorem LMem.writeG_sim (σ : State) {m : LMem} {μ : State} {B : Births}
    (h : m.run σ = .ok (μ, B)) (i : LId) (a : LSel) {g : LTerm} (hg : m.writeG i a = some g)
    (mv : MVal) :
    Rets (g.eval σ) ↔
      ∃ n ad μ₁, LId.evalR B i = .ok n ∧ a.addr σ n = .ok ad ∧ writeAddr μ mv ad = .ok μ₁ := by
  cases a with
  | size => simp only [LMem.writeG, reduceCtorEq] at hg
  | fld f =>
    simp only [LMem.writeG] at hg
    rw [LMem.structG_sim σ m i h hg]
    constructor
    · rintro ⟨n, fs, hn, hfs⟩
      obtain ⟨μ₁, hw⟩ := (writeField_ok μ mv n f).2 ⟨fs, hfs⟩
      exact ⟨n, _, μ₁, hn, rfl, hw⟩
    · rintro ⟨n, ad, μ₁, hn, had, hw⟩
      cases had
      obtain ⟨fs, hfs⟩ := (writeField_ok μ mv n f).1 ⟨μ₁, hw⟩
      exact ⟨n, fs, hn, hfs⟩
  | idx t =>
    simp only [LMem.writeG, LMem.lenT, Option.map_eq_some_iff] at hg
    obtain ⟨L, hL, rfl⟩ := hg
    have hs := LMem.readT_sim σ m i .size h hL
    rw [ltR_rets]
    constructor
    · rintro ⟨c, d, hc, hd, h0, h1⟩
      obtain ⟨n, hn, hlen⟩ := Res.bind_eq_ok.1 ((hs _).1 hd)
      obtain ⟨μ₁, hw⟩ := (writeIndex_ok μ mv n c).2 ⟨d, hlen, h0, h1⟩
      exact ⟨n, _, μ₁, hn, by simp only [LSel.addr, hc, Res.ok_bind', Value.asInt], hw⟩
    · rintro ⟨n, ad, μ₁, hn, had, hw⟩
      simp only [LSel.addr, Res.bind_eq_ok] at had
      obtain ⟨c, ⟨x, hx, hc⟩, had⟩ := had
      cases had
      have hti : t.eval σ = .ok (.int c) := by
        cases x with
        | int c' => cases hc; exact hx
        | bool _ => cases hc
      obtain ⟨d, hlen, h0, h1⟩ := (writeIndex_ok μ mv n c).1 ⟨μ₁, hw⟩
      exact ⟨c, d, hti, (hs _).2 (by rw [hn, Res.ok_bind']; exact hlen), h0, h1⟩

theorem refDesc_alloc {μ' μ : State} {base : Nat} {v : SVal} {id : Nat}
    (hle : base ≤ μ'.nextId) (hd : DescFrom μ'.heap base μ'.nextId)
    (hc : copyStToM μ' v = .ok (μ, .ref id)) : DescFrom μ.heap base μ.nextId := by
  have hx := copyStToM_heapExt μ' v μ _ hc
  exact DescFrom.append (hd.ext (Nat.le_refl _) hx)
    (copyStToM_desc μ μ' v μ _ hc (State.HeapExt.refl μ)).1 hle

/-- **A memory whose references all name older roots holds no cycle**
(`LMem.refDesc`): every object of the run references only older ones, so a
copy out of it returns (`MemNames.copyMem_ok_desc`). -/
theorem LMem.refDesc_desc (σ : State) : (m : LMem) → ∀ {μ : State} {B : Births},
    m.run σ = .ok (μ, B) → m.refDesc = true → MemNames.DescFrom μ.heap σ.nextId μ.nextId
  | .init, μ, B, h, _ => by
    simp only [LMem.run, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact DescFrom.empty _ _
  | .addM m k R, μ, B, h, hd => by
    obtain ⟨μ', B', id, hr, -, hc, -⟩ := LMem.run_addM h
    exact refDesc_alloc (LMem.run_births σ m hr).1 (LMem.refDesc_desc σ m hr hd) hc
  | .newArr m k R n, μ, B, h, hd => by
    obtain ⟨μ', B', id, c, hr, -, -, hc, -⟩ := LMem.run_newArr h
    exact refDesc_alloc (LMem.run_births σ m hr).1 (LMem.refDesc_desc σ m hr hd) hc
  | .copySt m k s q, μ, B, h, hd => by
    obtain ⟨μ', B', id, hr, -, ⟨hcp, rfl⟩, -⟩ := LMem.run_copySt h
    exact refDesc_alloc (LMem.run_births σ m hr).1 (LMem.refDesc_desc σ m hr hd) hcp.hc
  | .write m j b v, μ, B, h, hd => by
    obtain ⟨μ', n', ad, mv, hr, hn', hb, hv, hw⟩ := LMem.run_write h
    simp only [LMem.refDesc, Bool.and_eq_true] at hd
    have hB := LMem.run_births σ m hr
    rw [Close.writeAddr_nextId hw]
    refine DescFrom.writeAddr (LMem.refDesc_desc σ m hr hd.1) hw (fun _ _ x hx => ?_)
    cases v with
    | word t =>
      simp only [LMV.eval, Res.bind_eq_ok, Except.ok.injEq] at hv
      obtain ⟨y, -, rfl⟩ := hv
      cases y <;> cases hx
    | ref j' =>
      simp only [decide_eq_true_eq] at hd
      simp only [LMV.eval, Res.bind_eq_ok, Except.ok.injEq] at hv
      obtain ⟨x', hx', rfl⟩ := hv
      cases hx
      rw [LSel.addr_id hb]
      obtain ⟨b', hb', hlo', hhi', hbase', -⟩ := Births.eval_interval hB (LId.evalR_ok.1 hx')
      obtain ⟨b, hbb, hlo, -, -, -⟩ := Births.eval_interval hB (LId.evalR_ok.1 hn')
      obtain ⟨-, -, -, hord⟩ := hB.2 _ b' hb'
      have := hord _ b hd.2 hbb
      exact ⟨hbase', by omega⟩

/-! ### Paths through a view of memory -/

/-- The selector a literal segment is. -/
def LSel.ofSeg : Seg → LSel
  | .field f => .fld f
  | .at j => .idx (.lit (.int j))

theorem LSel.ofSeg_addr (σ : State) (n : Nat) (s : Seg) :
    (LSel.ofSeg s).addr σ n = .ok (.ofSeg n s) := by
  cases s <;> rfl

/-- A path of a root and literal segments: its root and its segments. -/
def LPath.lit? : LPath → Option (Name × List Seg)
  | .root r => some (r, [])
  | .field q f => (q.lit?).map fun rp => (rp.1, rp.2 ++ [.field f])
  | .at q k =>
    match k.ground? with
    | some (.int j) => (q.lit?).map fun rp => (rp.1, rp.2 ++ [.at j])
    | _ => none

theorem LPath.lit?_eval (σ : State) : (Q : LPath) → ∀ {r : Name} {p : List Seg},
    Q.lit? = some (r, p) → Q.eval σ = .ok (.field r :: p)
  | .root r', r, p, h => by
    simp only [LPath.lit?, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  | .field q f, r, p, h => by
    simp only [LPath.lit?] at h
    cases hq : q.lit? with
    | none => rw [hq] at h; cases h
    | some rp =>
      obtain ⟨r', p'⟩ := rp
      rw [hq] at h
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp only [LPath.eval, LPath.lit?_eval σ q hq, Res.ok_bind', List.cons_append]
  | .at q k, r, p, h => by
    simp only [LPath.lit?] at h
    split at h
    · rename_i j hj
      cases hq : q.lit? with
      | none => rw [hq] at h; cases h
      | some rp =>
        obtain ⟨r', p'⟩ := rp
        rw [hq] at h
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp only [LPath.eval, LPath.lit?_eval σ q hq, Res.ok_bind', LTerm.ground?_eval σ k hj,
          Value.asInt, List.cons_append]
    · cases h

/-- The name a literal path reaches from a name, slot by slot: KeY's
`readR(mem, id, flds)` (`readRCons`). -/
def LMem.walk (m : LMem) (i : LId) : List Seg → Option LId
  | [] => some i
  | s :: p => (m.readI i (LSel.ofSeg s)).bind fun j => m.walk j p

/-- **A literal path from a name reaches the name `walk` gives** (`readREmpty`,
`readRCons`). -/
theorem LMem.walk_sim (σ : State) {m : LMem} {μ : State} {B : Births}
    (h : m.run σ = .ok (μ, B)) : (p : List Seg) → ∀ {i j : LId}, m.walk i p = some j →
    Sim (LId.evalR B j) (LId.evalR B i >>= fun n => (MVal.ref n).readPath μ p >>= MVal.asRef)
  | [], i, j, hw => by
    simp only [LMem.walk, Option.some.injEq] at hw
    subst hw
    apply Sim.of_eq
    cases LId.evalR B i <;> rfl
  | s :: p, i, j, hw => by
    simp only [LMem.walk, Option.bind_eq_some_iff] at hw
    obtain ⟨i₁, hi₁, hw⟩ := hw
    have ih := LMem.walk_sim σ h p hw
    have hI := (LMem.readI_sim σ m i (LSel.ofSeg s) h hi₁).2
    refine Sim.trans ih (Sim.trans (Sim.bind hI fun _ => Sim.refl _) ?_)
    intro u
    simp only [LSel.iread, LSel.ofSeg_addr, Res.ok_bind', Res.bind_eq_ok, MVal.readPath]
    constructor
    · rintro ⟨n₁, ⟨n, hn, mv, hmv, hr⟩, hp⟩
      refine ⟨n, hn, ?_⟩
      cases mv with
      | prim _ => cases hr
      | ref c =>
        simp only [MVal.asRef, pure, Except.pure, Except.ok.injEq] at hr
        subst hr
        obtain ⟨a, hpa, hra⟩ := hp
        exact ⟨a, ⟨_, hmv, hpa⟩, hra⟩
    · rintro ⟨n, hn, a, ⟨mv, hmv, hpa⟩, hra⟩
      cases mv with
      | ref c => exact ⟨c, ⟨n, hn, _, hmv, rfl⟩, a, hpa, hra⟩
      | prim pv =>
        cases p with
        | nil =>
          simp only [MVal.readPath, Except.ok.injEq] at hpa
          subst hpa; cases hra
        | cons _ _ => simp only [MVal.readPath, reduceCtorEq] at hpa

theorem copyMToSt_asValue_sim {σ : State} {rem : List Nat} {mv : MVal} {w : SVal}
    (h : copyMToSt σ rem mv = .ok w) : Sim w.asValue mv.asValue := by
  cases mv with
  | prim pv =>
    rw [Close.copyMToSt_prim, Except.ok.injEq] at h
    subst h
    cases pv <;> exact Sim.refl _
  | ref n =>
    obtain ⟨-, ⟨_, _, -, -, rfl⟩ | ⟨_, _, _, -, -, rfl⟩⟩ := copyMToSt_ref_inv h <;>
      exact Sim.halt (fun _ h => by cases h) (fun _ h => by cases h)

/-- The view of the object `n`: what `copyMem` gives, read along `P`, against
memory read along `P` (`findOnCopy`, `selectOnCopyMemPrim`/`Ref`). -/
theorem view_sim {μ : State} {n : Nat} {cv : SVal} (hcv : copyMem μ (.ref n) = .ok cv)
    {P : List Seg} (hl : noLen P = true) {β : Type} (F : SVal → Res β) (G : MVal → Res β)
    (hFG : ∀ rem mv w, copyMToSt μ rem mv = .ok w → Sim (F w) (G mv)) :
    Sim (cv.findLive P >>= F) ((MVal.ref n).readPath μ P >>= G) := by
  have hc : IsCopy μ cv := ⟨_, _, hcv⟩
  rw [IsCopy.findLive_eq P hc]
  have hr := copyMToSt_readPath μ P (noLen_mem hl) hcv
  intro u
  constructor
  · intro hu
    rw [Res.bind_eq_ok] at hu
    obtain ⟨w, hw, hu⟩ := hu
    obtain ⟨mv', rem', hmv, hcw⟩ := hr.1 w hw
    rw [hmv, Res.ok_bind']
    exact (hFG _ _ _ hcw u).1 hu
  · intro hu
    rw [Res.bind_eq_ok] at hu
    obtain ⟨mv', hmv, hu⟩ := hu
    obtain ⟨w, rem', hw, hcw⟩ := hr.2 mv' hmv
    rw [hw, Res.ok_bind']
    exact (hFG _ _ _ hcw u).2 hu

/-- A view holds no mapping (Lean only). -/
theorem view_noMap {μ : State} {n : Nat} {cv : SVal} (hcv : copyMem μ (.ref n) = .ok cv)
    (P : List Seg) (u : Value) : (cv.findLive P >>= kmapF) ≠ .ok u := by
  intro h
  rw [IsCopy.findLive_eq P ⟨_, _, hcv⟩, Res.bind_eq_ok] at h
  obtain ⟨w, hw, hk⟩ := h
  unfold kmapF at hk
  split at hk
  · rename_i hm
    cases w with
    | map e d => exact copyMToSt_noMap hcv P hw e d rfl
    | _ => simp only [isMapV, Bool.false_eq_true] at hm
  · cases hk

theorem Sim.symm {α : Type} {x y : Res α} (h : Sim x y) : Sim y x := fun a => (h a).symm

/-- A slot below a path: the object the path reaches, then the slot. -/
theorem readPath_snoc_sim {β : Type} (μ : State) (mv : MVal) (p : List Seg) (s : Seg)
    (G : MVal → Res β) :
    Sim ((mv.readPath μ p >>= MVal.asRef) >>= fun n' => readAddr μ (.ofSeg n' s) >>= G)
      (mv.readPath μ (p ++ [s]) >>= G) := by
  rw [MVal.readPath_snoc]
  cases mv.readPath μ p with
  | error e => exact Sim.halt (fun _ h => by cases h) (fun _ h => by cases h)
  | ok mv' =>
    cases mv' with
    | ref n' => exact Sim.refl _
    | prim pv => exact Sim.halt (fun _ h => by cases h) (fun _ h => by cases h)

/-- What a path below a view reads: the literal segments to the object and
the last selector (`readRCons`); none where a segment asks a `length` or a
leading index is no literal. -/
def viewPath : LPath → Option (List Seg × LSel)
  | .field Q f =>
    match Q.lit? with
    | some (r, p) => if r = viewRoot ∧ noLen (p ++ [.field f]) = true then some (p, .fld f) else none
    | none => none
  | .at Q t =>
    match Q.lit? with
    | some (r, p) => if r = viewRoot ∧ noLen p = true then some (p, .idx t) else none
    | none => none
  | .root _ => none

/-- The literal segments to the object a path below a view names. -/
def viewObj (Q : LPath) : Option (List Seg) :=
  match Q.lit? with
  | some (r, p) => if r = viewRoot ∧ noLen p = true then some p else none
  | none => none

theorem view_findLive (cv : SVal) (P : List Seg) :
    (SVal.struct [(viewRoot, cv)]).findLive (.field viewRoot :: P) = cv.findLive P := by
  simp only [SVal.findLive, lookupBy, if_true]

/-- The slot a path below a view reads, segment by segment. -/
theorem viewPath_eval (σ : State) {Q : LPath} {p : List Seg} {a : LSel} {qs : List Seg}
    (hQ : viewPath Q = some (p, a)) (hq : Q.eval σ = .ok qs) :
    ∃ s, noLen (p ++ [s]) = true ∧ qs = .field viewRoot :: (p ++ [s]) ∧
      (∀ n μ, a.read σ μ n = readAddr μ (.ofSeg n s) >>= MVal.asValue) ∧
      ∀ n, a.addr σ n = .ok (.ofSeg n s) := by
  cases Q with
  | root r => cases hQ
  | field Q f =>
    simp only [viewPath] at hQ
    split at hQ
    · rename_i r p' hl
      split at hQ
      · rename_i hc
        simp only [Option.some.injEq, Prod.mk.injEq] at hQ
        obtain ⟨rfl, rfl⟩ := hQ
        obtain ⟨rfl, hn⟩ := hc
        simp only [LPath.eval, LPath.lit?_eval σ Q hl, Res.ok_bind', Except.ok.injEq] at hq
        subst hq
        exact ⟨.field f, hn, rfl, fun _ _ => rfl, fun _ => rfl⟩
      · cases hQ
    · cases hQ
  | «at» Q t =>
    simp only [viewPath] at hQ
    split at hQ
    · rename_i r p' hl
      split at hQ
      · rename_i hc
        simp only [Option.some.injEq, Prod.mk.injEq] at hQ
        obtain ⟨rfl, rfl⟩ := hQ
        obtain ⟨rfl, hn⟩ := hc
        simp only [LPath.eval, LPath.lit?_eval σ Q hl, Res.ok_bind', Res.bind_eq_ok,
          Except.ok.injEq] at hq
        obtain ⟨c, ⟨x, hx, hc⟩, rfl⟩ := hq
        have ht : t.eval σ = .ok (.int c) := by
          cases x with
          | int c' => cases hc; exact hx
          | bool _ => cases hc
        refine ⟨.at c, by rw [noLen_append, hn]; rfl, by simp only [List.cons_append], ?_, ?_⟩
        · intro n μ
          simp only [LSel.read, ht, Res.ok_bind', Value.asInt]
          rfl
        · intro n
          simp only [LSel.addr, ht, Res.ok_bind', Value.asInt]
          rfl
      · cases hQ
    · cases hQ

theorem viewObj_eval (σ : State) {Q : LPath} {p : List Seg} {qs : List Seg}
    (hQ : viewObj Q = some p) (hq : Q.eval σ = .ok qs) :
    noLen p = true ∧ qs = .field viewRoot :: p := by
  unfold viewObj at hQ
  split at hQ
  · rename_i r p' hl
    split at hQ
    · rename_i hc
      cases hQ
      obtain ⟨rfl, hn⟩ := hc
      rw [LPath.lit?_eval σ Q hl, Except.ok.injEq] at hq
      exact ⟨hn, hq.symm⟩
    · cases hQ
  · cases hQ

/-- The setting of a read below a view: the memory runs, the name denotes
`n`, and its copy out is `cv`. -/
structure ViewAt (σ : State) (m : LMem) (i : LId) (μ : State) (B : Births) (cv : SVal) : Prop where
  run : m.run σ = .ok (μ, B)
  obj : ∃ n, LId.evalR B i = .ok n ∧ copyMem μ (.ref n) = .ok cv

theorem LStor.eval_view {σ : State} {m : LMem} {i : LId} {v : SVal}
    (h : (LStor.view m i).eval σ = .ok v) :
    ∃ μ B cv, ViewAt σ m i μ B cv ∧ v = .struct [(viewRoot, cv)] := by
  simp only [LStor.eval, Res.bind_eq_ok, Except.ok.injEq] at h
  obtain ⟨⟨μ, B⟩, hr, n, hn, cv, hcv, rfl⟩ := h
  exact ⟨μ, B, cv, ⟨hr, n, hn, hcv⟩, rfl⟩

/-- **A word read below a view** (`findOnCopy`, `selectOnCopyMemPrim`): the
slot the same path reads in memory. -/
theorem view_read_sim {σ : State} {m : LMem} {i j : LId} {μ : State} {B : Births} {cv : SVal}
    (hv : ViewAt σ m i μ B cv) {Q : LPath} {p : List Seg} {a : LSel} {qs : List Seg}
    (hQ : viewPath Q = some (p, a)) (hq : Q.eval σ = .ok qs) (hw : m.walk i p = some j) :
    Sim (LId.evalR B j >>= fun n' => a.read σ μ n')
      ((SVal.struct [(viewRoot, cv)]).findLive qs >>= SVal.asValue) := by
  obtain ⟨s, hl, rfl, hrd, -⟩ := viewPath_eval σ hQ hq
  obtain ⟨n, hn, hcv⟩ := hv.obj
  rw [view_findLive]
  refine Sim.trans ?_ (Sim.symm (view_sim hcv hl SVal.asValue MVal.asValue
    fun _ _ _ h => copyMToSt_asValue_sim h))
  simp only [hrd]
  have hW := LMem.walk_sim σ hv.run p hw
  rw [hn, Res.ok_bind'] at hW
  exact Sim.trans (Sim.bind hW fun _ => Sim.refl _) (readPath_snoc_sim μ _ p s _)

/-- **The length below a view** (`selectOnCopyMemPrim` at `size`). -/
theorem view_len_sim {σ : State} {m : LMem} {i j : LId} {μ : State} {B : Births} {cv : SVal}
    (hv : ViewAt σ m i μ B cv) {Q : LPath} {p : List Seg} {qs : List Seg}
    (hQ : viewObj Q = some p) (hq : Q.eval σ = .ok qs) (hw : m.walk i p = some j) :
    Sim (LId.evalR B j >>= fun n' => memArrayLen μ n')
      ((SVal.struct [(viewRoot, cv)]).findLive qs >>= Close.arrLen) := by
  obtain ⟨hl, rfl⟩ := viewObj_eval σ hQ hq
  obtain ⟨n, hn, hcv⟩ := hv.obj
  rw [view_findLive]
  refine Sim.trans ?_ (Sim.symm (view_sim hcv hl Close.arrLen
    (fun mv => MVal.asRef mv >>= memArrayLen μ) fun rem mv w h => ?_))
  · have hW := LMem.walk_sim σ hv.run p hw
    rw [hn, Res.ok_bind'] at hW
    refine Sim.trans (Sim.bind hW fun _ => Sim.refl _) (Sim.of_eq ?_)
    cases (MVal.ref n).readPath μ p <;> rfl
  · cases mv with
    | prim pv =>
      rw [Close.copyMToSt_prim, Except.ok.injEq] at h
      subst h
      exact Sim.halt (fun _ h => by cases h) (fun _ h => by cases h)
    | ref n' =>
      rw [copyMToSt_arrLen h]
      exact Sim.refl _

/-- **Whether a slot below a view is there**: a word is read, or a reference
names an object. -/
theorem view_has_sim {σ : State} {m : LMem} {i j j' : LId} {μ : State} {B : Births} {cv : SVal}
    (hv : ViewAt σ m i μ B cv) {Q : LPath} {p : List Seg} {a : LSel} {qs : List Seg}
    (hQ : viewPath Q = some (p, a)) (hq : Q.eval σ = .ok qs) (hw : m.walk i p = some j)
    {W N : LTerm} (hW : Sim (W.eval σ) (LId.evalR B j >>= fun n' => a.read σ μ n'))
    (hI : Sim (LId.evalR B j') (LId.evalR B j >>= fun n' => a.iread σ μ n'))
    (hN : Rets (N.eval σ) ↔ ∃ x, LId.evalR B j' = .ok x) :
    Sim ((LTerm.orElse (.seq W (.lit (.bool true))) (.seq N (.lit (.bool true)))).eval σ)
      ((SVal.struct [(viewRoot, cv)]).findLive qs >>= fun _ => .ok (.bool true)) := by
  obtain ⟨s, hl, rfl, hrd, had⟩ := viewPath_eval σ hQ hq
  obtain ⟨n, hn, hcv⟩ := hv.obj
  rw [view_findLive]
  refine Sim.trans ?_ (Sim.symm (view_sim hcv hl (fun _ => (.ok (.bool true) : Res Value))
    (fun _ => (.ok (.bool true) : Res Value)) fun _ _ _ _ => Sim.refl _))
  have hWk := LMem.walk_sim σ hv.run p hw
  rw [hn, Res.ok_bind'] at hWk
  have hsnoc := readPath_snoc_sim μ (.ref n) p s (fun _ => (.ok (.bool true) : Res Value))
  have hir : ∀ n', a.iread σ μ n' = readAddr μ (.ofSeg n' s) >>= MVal.asRef := by
    intro n'; simp only [LSel.iread, had, Res.ok_bind']
  have key : (∃ n', ((MVal.ref n).readPath μ p >>= MVal.asRef) = .ok n' ∧
      ∃ mv, readAddr μ (.ofSeg n' s) = .ok mv) ↔ Rets (W.eval σ) ∨ Rets (N.eval σ) := by
    rw [hN]
    constructor
    · rintro ⟨n', hp, mv, hmv⟩
      have he := (hWk n').2 hp
      cases mv with
      | prim pv =>
        refine .inl ⟨pv, (hW pv).2 ?_⟩
        rw [he, Res.ok_bind', hrd, hmv, Res.ok_bind']
        cases pv <;> rfl
      | ref x =>
        refine .inr ⟨x, (hI x).2 ?_⟩
        rw [he, Res.ok_bind', hir, hmv]
        rfl
    · rintro (⟨w, hw'⟩ | ⟨x, hx⟩)
      · obtain ⟨n', he, hr⟩ := Res.bind_eq_ok.1 ((hW w).1 hw')
        rw [hrd] at hr
        obtain ⟨mv, hmv, -⟩ := Res.bind_eq_ok.1 hr
        exact ⟨n', (hWk n').1 he, mv, hmv⟩
      · obtain ⟨n', he, hr⟩ := Res.bind_eq_ok.1 ((hI x).1 hx)
        rw [hir] at hr
        obtain ⟨mv, hmv, -⟩ := Res.bind_eq_ok.1 hr
        exact ⟨n', (hWk n').1 he, mv, hmv⟩
  intro u
  have hR : ((MVal.ref n).readPath μ (p ++ [s]) >>= fun _ => (.ok (.bool true) : Res Value)) = .ok u ↔
      u = .bool true ∧ ∃ n', ((MVal.ref n).readPath μ p >>= MVal.asRef) = .ok n' ∧
        ∃ mv, readAddr μ (.ofSeg n' s) = .ok mv := by
    rw [← hsnoc u]
    simp only [Res.bind_eq_ok, Except.ok.injEq]
    constructor
    · rintro ⟨n', hp, mv, hmv, rfl⟩; exact ⟨rfl, n', hp, mv, hmv⟩
    · rintro ⟨rfl, n', hp, mv, hmv⟩; exact ⟨n', hp, mv, hmv, rfl⟩
  rw [hR, key]
  simp only [Rets, LTerm.eval]
  cases W.eval σ with
  | ok w =>
    simp only [Res.ok_bind', orElseR, Except.ok.injEq, exists_eq', true_or, and_true]
    exact eq_comm
  | error e =>
    cases N.eval σ with
    | ok x =>
      simp only [orElseR, bind, Except.bind, Except.ok.injEq, exists_eq', or_true,
        and_true, reduceCtorEq, exists_false]
      exact eq_comm
    | error e' =>
      simp only [orElseR, bind, Except.bind, reduceCtorEq, exists_false, or_self, and_false]

/-! ### Agreeing terms in the clauses -/

theorem rets_of_sim {x y : Res Value} (h : Sim x y) : Rets x ↔ Rets y :=
  ⟨fun ⟨v, hv⟩ => ⟨v, (h v).1 hv⟩, fun ⟨v, hv⟩ => ⟨v, (h v).2 hv⟩⟩

theorem ltR_val {σ : State} {k n : LTerm} {v : Value} (h : (ltR k n).eval σ = .ok v) :
    v = .bool true := by
  unfold ltR at h
  split at h
  · split at h
    · cases h; rfl
    · cases h
  · simp only [ltG, LTerm.eval, Res.bind_eq_ok] at h
    obtain ⟨cv, -, h⟩ := h
    cases cv with
    | bool b => cases b <;> simp only [pickBranch, reduceCtorEq, Except.ok.injEq] at h
                <;> exact h.symm
    | int _ => cases h

theorem ltR_congr (σ : State) (k : LTerm) {n n' : LTerm} (hn : Sim (n'.eval σ) (n.eval σ)) :
    Sim ((ltR k n').eval σ) ((ltR k n).eval σ) := by
  have hr : Rets ((ltR k n').eval σ) ↔ Rets ((ltR k n).eval σ) := by
    rw [ltR_rets, ltR_rets]
    constructor
    · rintro ⟨c, d, hc, hd, h0, h1⟩; exact ⟨c, d, hc, (hn _).1 hd, h0, h1⟩
    · rintro ⟨c, d, hc, hd, h0, h1⟩; exact ⟨c, d, hc, (hn _).2 hd, h0, h1⟩
  intro u
  constructor
  · intro h
    obtain ⟨v, hv⟩ := hr.1 ⟨u, h⟩
    rw [ltR_val h, ← ltR_val hv]; exact hv
  · intro h
    obtain ⟨v, hv⟩ := hr.2 ⟨u, h⟩
    rw [ltR_val h, ← ltR_val hv]; exact hv

theorem natL_ok {σ : State} {n : LTerm} {v : Value} :
    (natL n).eval σ = .ok v ↔ ∃ c, n.eval σ = .ok (.int c) ∧ v = .int c.toNat := by
  constructor
  · intro h
    unfold natL at h
    split at h
    · rename_i c
      cases h
      exact ⟨c, rfl, rfl⟩
    · simp only [LTerm.eval, Res.bind_eq_ok] at h
      obtain ⟨cv, ⟨x, hx, hc⟩, h⟩ := h
      cases x with
      | int c =>
        refine ⟨c, hx, ?_⟩
        simp only [evalBinop, applyBinOp, Value.asInt, checkArith, bind, Except.bind,
          Except.ok.injEq] at hc
        subst hc
        by_cases hc0 : c < 0
        · simp only [hc0, decide_true, pickBranch, Except.ok.injEq] at h
          subst h; congr 1; omega
        · simp only [hc0, decide_false, pickBranch, hx, Except.ok.injEq] at h
          subst h; congr 1; omega
      | bool b =>
        simp only [evalBinop, applyBinOp, Value.asInt, bind, Except.bind, reduceCtorEq] at hc
  · rintro ⟨c, hc, rfl⟩
    exact natL_eval σ n hc

theorem natL_congr (σ : State) {n n' : LTerm} (hn : Sim (n'.eval σ) (n.eval σ)) :
    Sim ((natL n').eval σ) ((natL n).eval σ) := by
  intro u
  rw [natL_ok, natL_ok]
  exact ⟨fun ⟨c, hc, hu⟩ => ⟨c, (hn _).1 hc, hu⟩, fun ⟨c, hc, hu⟩ => ⟨c, (hn _).2 hc, hu⟩⟩

theorem seqL_congr (σ : State) {g g' a a' : LTerm} (hg : Sim (g'.eval σ) (g.eval σ))
    (ha : Sim (a'.eval σ) (a.eval σ)) : Sim ((seqL g' a').eval σ) ((seqL g a).eval σ) := by
  rw [seqL_eval, seqL_eval]
  exact Sim.bind hg fun _ => ha

/-- `new R(n)`'s reads agree where the lengths do. -/
theorem newSel_congr (σ : State) (R : RefTy) {n n' : LTerm} (hn : Sim (n'.eval σ) (n.eval σ))
    (p : List Seg) (a : LSel) : Sim ((newSel R n' p a).eval σ) ((newSel R n p a).eval σ) := by
  unfold newSel
  split
  · exact Sim.refl _
  · exact seqL_congr σ (ltR_congr σ _ hn) (Sim.refl _)
  · exact natL_congr σ hn
  · exact seqL_congr σ (ltR_congr σ _ hn) (Sim.refl _)
  · exact Sim.refl _
  · exact Sim.refl _

theorem newObj_congr (σ : State) (g : Option Ty → LTerm) (R : RefTy) {n n' : LTerm}
    (hn : Sim (n'.eval σ) (n.eval σ)) (p : List Seg) :
    Sim ((newObj g R n' p).eval σ) ((newObj g R n p).eval σ) := by
  unfold newObj
  split
  · exact Sim.refl _
  · exact seqL_congr σ (ltR_congr σ _ hn) (Sim.refl _)
  · exact Sim.refl _
  · exact Sim.refl _

theorem kite_congr (σ : State) {a a' b b' t t' e e' : LTerm} (ha : Sim (a'.eval σ) (a.eval σ))
    (hb : Sim (b'.eval σ) (b.eval σ)) (ht : Sim (t'.eval σ) (t.eval σ))
    (he : Sim (e'.eval σ) (e.eval σ)) :
    Sim ((LTerm.kite a' b' t' e').eval σ) ((LTerm.kite a b t e).eval σ) :=
  Sim.bind (Sim.bind ha fun _ => Sim.refl _) fun i =>
    Sim.bind (Sim.bind hb fun _ => Sim.refl _) fun j => by
      by_cases hij : i = j
      · simp only [hij, if_true]; exact ht
      · simp only [hij, if_false]; exact he

theorem LPath.ext_congr (σ : State) {q q' : LPath} (hq : Sim (q'.eval σ) (q.eval σ))
    (p : List Seg) : Sim ((q'.ext p).eval σ) ((q.ext p).eval σ) := by
  rw [LPath.ext_eval, LPath.ext_eval]
  exact Sim.bind hq fun _ => Sim.refl _

/-! ### Soundness: a copy into memory returns in any state -/

mutual

theorem copyStToM_ok_any (v : SVal) : ∀ (σ σ' : State) (r : State × MVal),
    copyStToM σ v = .ok r → ∃ r', copyStToM σ' v = .ok r' := by
  intro σ σ' r h
  cases v with
  | prim pv => cases pv <;> exact ⟨_, rfl⟩
  | map e d => exact (copyStToM_map_inv (τ := r.1) (mv := r.2) h).elim
  | struct fs =>
    obtain ⟨τ₁, mfs, hf, -, -⟩ := copyStToM_struct_inv (τ := r.1) (mv := r.2) h
    obtain ⟨⟨τ', mfs'⟩, hf'⟩ := copyStFields_ok_any fs σ σ' _ hf
    exact ⟨_, by rw [copyStToM, hf']; rfl⟩
  | array es sh fx =>
    obtain ⟨τ₁, mes, he, -, -⟩ := copyStToM_array_inv (τ := r.1) (mv := r.2) h
    obtain ⟨⟨τ', mes'⟩, he'⟩ := copyStElems_ok_any es σ σ' _ he
    exact ⟨_, by rw [copyStToM, he']; rfl⟩

theorem copyStFields_ok_any (fs : List (Name × SVal)) : ∀ (σ σ' : State)
    (r : State × List (Name × MVal)), copyStFields σ fs = .ok r →
    ∃ r', copyStFields σ' fs = .ok r' := by
  intro σ σ' r h
  cases fs with
  | nil => exact ⟨_, rfl⟩
  | cons fv rest =>
    obtain ⟨n, v⟩ := fv
    obtain ⟨σ₁, mv, mrest, h1, h2, -⟩ := copyStFields_cons_inv (τ := r.1) (mfs := r.2) h
    obtain ⟨⟨σ₁', mv'⟩, h1'⟩ := copyStToM_ok_any v σ σ' _ h1
    obtain ⟨⟨τ', mrest'⟩, h2'⟩ := copyStFields_ok_any rest σ₁ σ₁' _ h2
    exact ⟨_, by rw [copyStFields, h1', Res.ok_bind']; dsimp only; rw [h2']; rfl⟩

theorem copyStElems_ok_any (es : List SVal) : ∀ (σ σ' : State) (r : State × List MVal),
    copyStElems σ es = .ok r → ∃ r', copyStElems σ' es = .ok r' := by
  intro σ σ' r h
  cases es with
  | nil => exact ⟨_, rfl⟩
  | cons v rest =>
    obtain ⟨σ₁, mv, mrest, h1, h2, -⟩ := copyStElems_cons_inv (τ := r.1) (mes := r.2) h
    obtain ⟨⟨σ₁', mv'⟩, h1'⟩ := copyStToM_ok_any v σ σ' _ h1
    obtain ⟨⟨τ', mrest'⟩, h2'⟩ := copyStElems_ok_any rest σ₁ σ₁' _ h2
    exact ⟨_, by rw [copyStElems, h1', Res.ok_bind']; dsimp only; rw [h2']; rfl⟩

end

end Decide
end Solidity
