import Solidity.Syntax.Elab.Panic

/-!
# Origins of the generated guards that read storage or memory

For the index guards `Checked.idxPG` and `Checked.mIdxPG` and the pop guard of
`Stmt.panics`: the generated guard list, the `Panic.Origin` of the producer at
the evaluated operands, the bare V1 revert of the unguarded path or statement,
and the emitted panic bytes. Operand reads are hypotheses. A dynamic guard reads
the length the producer checks (`*_guard_length`); a fixed guard reads none, so
its storage origin needs the value at the path to be found.
-/

namespace Solidity.Correctness.Panic
open Solidity Semantics
variable {C : Contract} {Γ : Ctx}

/-- `a < b` at `uint`, once both operands are read. -/
private theorem lt_eval (σ : State C Γ) (a b : Val C Γ .uint) (x y : PrimTy.uint.Denote)
    (left : a.evalT σ = .ok x) (right : b.evalT σ = .ok y) :
    (Checked.cmpU .lt rfl rfl a b).evalT σ = .ok (decide (x.val < y.val)) := by
  simp [Checked.cmpU, Val.evalT, left, right, BinOp.shortT, BinOp.evalT, BinOp.evalNum,
    TRes.ofOpt, bind, Except.bind]

/-- A comparison whose right operand halts, halts with it. -/
private theorem cmp_right_halt (σ : State C Γ) (op : BinOp) (h : op.accepts .uint = true)
    (hq : op.ret .uint = .bool) (a b : Val C Γ .uint) (x : PrimTy.uint.Denote) (halt : THalt)
    (left : a.evalT σ = .ok x) (short : op.shortT x = none) (right : b.evalT σ = .error halt) :
    (Checked.cmpU op h hq a b).evalT σ = .error halt := by
  simp [Checked.cmpU, Val.evalT, left, right, short, bind, Except.bind]

/-- `a > 0` at `uint`, once `a` is read; a halt of `a` is the guard's. -/
private theorem positive_eval (σ : State C Γ) (a : Val C Γ .uint) :
    (Checked.cmpU .gt rfl rfl a (Checked.litU 0 (by decide))).evalT σ =
      (a.evalT σ).map fun x => decide (0 < x.val) := by
  cases read : a.evalT σ <;>
    simp [Checked.cmpU, Checked.litU, Val.evalT, read, BinOp.shortT, Simple.evalT, PrimTy.ofLit,
      BinOp.evalT, BinOp.evalNum, TRes.ofOpt, bind, Except.bind, Except.map]

/-! ## Storage index (`Checked.idxPG`, `0x32`) -/

/-- A mapping index generates no guard. -/
theorem storage_mapping_index_no_guard {k : PrimTy} {V : Ty}
    (b : SPath C Γ (.ref (.mapping k V))) (i : Val C Γ k) : Checked.idxPG .map b i = [] := rfl

/-- The length the dynamic guards read is the live length `Storage.inBounds`
and the pop producer check: the `n` of the view of the value found at the path. -/
theorem storage_guard_length {E : Ty} (σ : State C Γ) (b : SPath C Γ (.ref (.array E)))
    (ref : SRef C (.ref (.array E))) (value : SVal (.ref (.array E)))
    (base : b.resolveT σ = .ok ref) (found : σ.storage.find ref = some value) :
    (Val.len b rfl).evalT σ =
      .ok (lenU (SVal.view value : ArrView E).n (SVal.view value : ArrView E).hn) := by
  simp [Val.evalT, base, Storage.len, found, TRes.ofOpt, bind, Except.bind, pure, Except.pure]

/-- A length guard that was evaluated found the value at its path. -/
private theorem len_found {E : Ty} (σ : State C Γ) (b : SPath C Γ (.ref (.array E)))
    (ref : SRef C (.ref (.array E))) (base : b.resolveT σ = .ok ref)
    (missing : σ.storage.find ref = none) : (Val.len b rfl).evalT σ = .error .revert := by
  simp [Val.evalT, base, Storage.len, missing, TRes.ofOpt, bind, Except.bind]

/-- The dynamic storage index guard, after its operands are read. -/
theorem storage_dyn_index_guard_eval {E : Ty} (σ : State C Γ)
    (b : SPath C Γ (.ref (.array E))) (i : Val C Γ .uint) (ref : SRef C (.ref (.array E)))
    (k : PrimTy.uint.Denote) (value : SVal (.ref (.array E)))
    (base : b.resolveT σ = .ok ref) (index : i.evalT σ = .ok k)
    (found : σ.storage.find ref = some value) :
    (Checked.cmpU .lt rfl rfl i (.len b rfl)).evalT σ =
      .ok (decide (k.val.toNat < (SVal.view value : ArrView E).n)) := by
  rw [lt_eval σ i _ k _ index (storage_guard_length σ b ref value base found)]
  have nonneg := PrimTy.uint_nonneg k
  simp only [lenU]
  congr 1
  apply decide_eq_decide.mpr
  omega

/-- A failed dynamic storage index guard: the bounds origin of the storage
index producer at the evaluated path and index, and the path's V1 revert. -/
theorem storage_dyn_index_guard_origin {E : Ty} (σ : State C Γ)
    (b : SPath C Γ (.ref (.array E))) (i : Val C Γ .uint) (ref : SRef C (.ref (.array E)))
    (k : PrimTy.uint.Denote) (base : b.resolveT σ = .ok ref) (index : i.evalT σ = .ok k)
    (failed : (Checked.cmpU .lt rfl rfl i (.len b rfl)).evalT σ = .ok false) :
    Panic.Origin (.storageIndex σ.storage ref .dyn k) .bounds ∧
      (Loc.index (.arr .dyn) b i).resolveT σ = .error .revert := by
  cases found : σ.storage.find ref with
  | none =>
    rw [cmp_right_halt σ .lt rfl rfl i _ k .revert index rfl (len_found σ b ref base found)]
      at failed
    cases failed
  | some value =>
    rw [storage_dyn_index_guard_eval σ b i ref k value base index found] at failed
    have out : ¬k.val.toNat < (SVal.view value : ArrView E).n :=
      of_decide_eq_false (Except.ok.inj failed)
    have bounds : Storage.inBounds (.arr .dyn) k value = none := by
      simp [Storage.inBounds, out]
    have origin := Panic.storage_index_origin σ.storage ref .dyn k value found bounds
    exact ⟨origin.1, by
      simp [Loc.resolveT, base, index, origin.2, TRes.ofOpt, bind, Except.bind]⟩

/-- The guard list of a dynamic storage array index. -/
theorem storage_dyn_index_guards {E : Ty} (b : SPath C Γ (.ref (.array E)))
    (i : Val C Γ .uint) : Checked.idxPG (.arr .dyn) b i =
      [(Panic.Site.bounds.code, Checked.cmpU .lt rfl rfl i (.len b rfl))] := by
  rw [Checked.idxPG]
  rfl

/-- Association at the dynamic storage index guard of `Checked.idxPG`. -/
theorem storage_dyn_index_source {E : Ty} (σ : State C Γ)
    (b : SPath C Γ (.ref (.array E))) (i : Val C Γ .uint) (ref : SRef C (.ref (.array E)))
    (k : PrimTy.uint.Denote) (base : b.resolveT σ = .ok ref) (index : i.evalT σ = .ok k)
    (failed : (Checked.cmpU .lt rfl rfl i (.len b rfl)).evalT σ = .ok false) :
    Checked.idxPG (.arr .dyn) b i =
      [(Panic.Site.bounds.code, Checked.cmpU .lt rfl rfl i (.len b rfl))] ∧
    Panic.Origin (.storageIndex σ.storage ref .dyn k) .bounds ∧
    (Loc.index (.arr .dyn) b i).resolveT σ = .error .revert ∧
    (panicStmt Panic.Site.bounds.code (Checked.cmpU .lt rfl rfl i (.len b rfl))).runR σ =
      .error (THalt.ofData (encodePanic Panic.Site.bounds.code)) :=
  ⟨storage_dyn_index_guards b i, (storage_dyn_index_guard_origin σ b i ref k base index failed).1,
    (storage_dyn_index_guard_origin σ b i ref k base index failed).2,
    panic_guard_source_failure σ _ failed _⟩

/-- The guard list of a fixed storage array whose length is a `uint`. A longer
fixed array generates no guard. -/
theorem storage_fixed_index_guards {E : Ty} {n : Nat} (b : SPath C Γ (.ref (.fixed E n)))
    (i : Val C Γ .uint) (range : PrimTy.uint.inRange (n : Int) = true) :
    Checked.idxPG (.arr .fixed) b i =
      [(Panic.Site.bounds.code, Checked.cmpU .lt rfl rfl i (Checked.litU n range))] := by
  rw [Checked.idxPG]
  exact dif_pos range

/-- The fixed index guard (storage or memory), after its index is read. -/
theorem fixed_index_guard_eval (σ : State C Γ) (i : Val C Γ .uint) (k : PrimTy.uint.Denote)
    (n : Nat) (range : PrimTy.uint.inRange (n : Int) = true) (index : i.evalT σ = .ok k) :
    (Checked.cmpU .lt rfl rfl i (Checked.litU n range)).evalT σ =
      .ok (decide (k.val.toNat < n)) := by
  rw [lt_eval σ i _ k ⟨n, range⟩ index (by simp [Checked.litU, Val.evalT, Simple.evalT, PrimTy.ofLit])]
  have nonneg := PrimTy.uint_nonneg k
  exact congrArg Except.ok (decide_eq_decide.mpr (by show k.val < (n : Int) ↔ _; omega))

/-- A failed fixed storage index guard. The guard reads no storage: the value
at the path is a hypothesis, as the producer's origin needs it found. -/
theorem storage_fixed_index_guard_origin {E : Ty} {n : Nat} (σ : State C Γ)
    (b : SPath C Γ (.ref (.fixed E n))) (i : Val C Γ .uint) (ref : SRef C (.ref (.fixed E n)))
    (k : PrimTy.uint.Denote) (value : SVal (.ref (.fixed E n)))
    (range : PrimTy.uint.inRange (n : Int) = true)
    (base : b.resolveT σ = .ok ref) (index : i.evalT σ = .ok k)
    (found : σ.storage.find ref = some value)
    (failed : (Checked.cmpU .lt rfl rfl i (Checked.litU n range)).evalT σ = .ok false) :
    Panic.Origin (.storageIndex σ.storage ref .fixed k) .bounds ∧
      (Loc.index (.arr .fixed) b i).resolveT σ = .error .revert := by
  rw [fixed_index_guard_eval σ i k n range index] at failed
  have out : ¬k.val.toNat < n := of_decide_eq_false (Except.ok.inj failed)
  have bounds : Storage.inBounds (.arr .fixed) k value = none := by
    simp [Storage.inBounds, out]
  have origin := Panic.storage_index_origin σ.storage ref .fixed k value found bounds
  exact ⟨origin.1, by
    simp [Loc.resolveT, base, index, origin.2, TRes.ofOpt, bind, Except.bind]⟩

/-- Association at the fixed storage index guard of `Checked.idxPG`. -/
theorem storage_fixed_index_source {E : Ty} {n : Nat} (σ : State C Γ)
    (b : SPath C Γ (.ref (.fixed E n))) (i : Val C Γ .uint) (ref : SRef C (.ref (.fixed E n)))
    (k : PrimTy.uint.Denote) (value : SVal (.ref (.fixed E n)))
    (range : PrimTy.uint.inRange (n : Int) = true)
    (base : b.resolveT σ = .ok ref) (index : i.evalT σ = .ok k)
    (found : σ.storage.find ref = some value)
    (failed : (Checked.cmpU .lt rfl rfl i (Checked.litU n range)).evalT σ = .ok false) :
    Checked.idxPG (.arr .fixed) b i =
      [(Panic.Site.bounds.code, Checked.cmpU .lt rfl rfl i (Checked.litU n range))] ∧
    Panic.Origin (.storageIndex σ.storage ref .fixed k) .bounds ∧
    (Loc.index (.arr .fixed) b i).resolveT σ = .error .revert ∧
    (panicStmt Panic.Site.bounds.code
      (Checked.cmpU .lt rfl rfl i (Checked.litU n range))).runR σ =
        .error (THalt.ofData (encodePanic Panic.Site.bounds.code)) :=
  ⟨storage_fixed_index_guards b i range,
    (storage_fixed_index_guard_origin σ b i ref k value range base index found failed).1,
    (storage_fixed_index_guard_origin σ b i ref k value range base index found failed).2,
    panic_guard_source_failure σ _ failed _⟩

/-! ## Memory index (`Checked.mIdxPG`, `0x32`) -/

/-- The length the dynamic memory guard reads is `Heap.len`, the length of the
element list `Heap.index` looks the index up in. -/
theorem memory_guard_length {E : Ty} (σ : State C Γ) (b : MPath C Γ (.ref (.array E)))
    (ref : HRef σ.H (.array E)) (base : b.mvalT σ = .ok ref) :
    (Val.mlen b rfl).evalT σ = .ok (σ.heap.lenU ref) ∧
      (σ.heap.lenU ref).val = (MObj.elems .dyn (σ.heap.get ref)).length := by
  constructor
  · simp [Val.evalT, base, bind, Except.bind, pure, Except.pure]
  · rfl

/-- A failed dynamic memory index guard: the bounds origin of the heap index
producer at the evaluated object and index, and the path's V1 revert. -/
theorem memory_dyn_index_guard_origin {E : Ty} (σ : State C Γ)
    (b : MPath C Γ (.ref (.array E))) (i : Val C Γ .uint) (ref : HRef σ.H (.array E))
    (k : PrimTy.uint.Denote) (base : b.mvalT σ = .ok ref) (index : i.evalT σ = .ok k)
    (failed : (Checked.cmpU .lt rfl rfl i (.mlen b rfl)).evalT σ = .ok false) :
    Panic.Origin (.index σ.heap ref .dyn k) .bounds ∧
      (MPath.loc (.index .dyn b i)).mvalT σ = .error .revert := by
  rw [lt_eval σ i _ k _ index (memory_guard_length σ b ref base).1,
    (memory_guard_length σ b ref base).2] at failed
  have out := of_decide_eq_false (Except.ok.inj failed)
  have nonneg := PrimTy.uint_nonneg k
  have none : σ.heap.index ref .dyn k = none := by
    rw [Heap.index, List.getElem?_eq_none_iff]
    omega
  exact ⟨Panic.index_origin σ.heap ref .dyn k none, by
    simp [MPath.mvalT, MLoc.addrT, base, index, Heap.readAddr, none, TRes.ofOpt, bind,
      Except.bind, pure, Except.pure]⟩

/-- Association at the dynamic memory index guard of `Checked.mIdxPG`. -/
theorem memory_dyn_index_source {E : Ty} (σ : State C Γ)
    (b : MPath C Γ (.ref (.array E))) (i : Val C Γ .uint) (ref : HRef σ.H (.array E))
    (k : PrimTy.uint.Denote) (base : b.mvalT σ = .ok ref) (index : i.evalT σ = .ok k)
    (failed : (Checked.cmpU .lt rfl rfl i (.mlen b rfl)).evalT σ = .ok false) :
    Checked.mIdxPG .dyn b i =
      [(Panic.Site.bounds.code, Checked.cmpU .lt rfl rfl i (.mlen b rfl))] ∧
    Panic.Origin (.index σ.heap ref .dyn k) .bounds ∧
    (MPath.loc (.index .dyn b i)).mvalT σ = .error .revert ∧
    (panicStmt Panic.Site.bounds.code (Checked.cmpU .lt rfl rfl i (.mlen b rfl))).runR σ =
      .error (THalt.ofData (encodePanic Panic.Site.bounds.code)) :=
  ⟨rfl, (memory_dyn_index_guard_origin σ b i ref k base index failed).1,
    (memory_dyn_index_guard_origin σ b i ref k base index failed).2,
    panic_guard_source_failure σ _ failed _⟩

/-- The guard list of a fixed memory array whose length is a `uint`. -/
theorem memory_fixed_index_guards {E : Ty} {n : Nat} (b : MPath C Γ (.ref (.fixed E n)))
    (i : Val C Γ .uint) (range : PrimTy.uint.inRange (n : Int) = true) :
    Checked.mIdxPG .fixed b i =
      [(Panic.Site.bounds.code, Checked.cmpU .lt rfl rfl i (Checked.litU n range))] := by
  unfold Checked.mIdxPG
  exact dif_pos range

/-- A failed fixed memory index guard: the object's element list has the
type's length `n`, the literal the guard compares with. -/
theorem memory_fixed_index_guard_origin {E : Ty} {n : Nat} (σ : State C Γ)
    (b : MPath C Γ (.ref (.fixed E n))) (i : Val C Γ .uint) (ref : HRef σ.H (.fixed E n))
    (k : PrimTy.uint.Denote) (range : PrimTy.uint.inRange (n : Int) = true)
    (base : b.mvalT σ = .ok ref) (index : i.evalT σ = .ok k)
    (failed : (Checked.cmpU .lt rfl rfl i (Checked.litU n range)).evalT σ = .ok false) :
    Panic.Origin (.index σ.heap ref .fixed k) .bounds ∧
      (MPath.loc (.index .fixed b i)).mvalT σ = .error .revert := by
  rw [fixed_index_guard_eval σ i k n range index] at failed
  have out : ¬k.val.toNat < n := of_decide_eq_false (Except.ok.inj failed)
  have none : σ.heap.index ref .fixed k = none := by
    rw [Heap.index, List.getElem?_eq_none_iff, MObj.elems_fixed,
      (σ.heap.get ref : {l : List (MVal σ.H E) // l.length = n}).2]
    omega
  exact ⟨Panic.index_origin σ.heap ref .fixed k none, by
    simp [MPath.mvalT, MLoc.addrT, base, index, Heap.readAddr, none, TRes.ofOpt, bind,
      Except.bind, pure, Except.pure]⟩

/-- Association at the fixed memory index guard of `Checked.mIdxPG`. -/
theorem memory_fixed_index_source {E : Ty} {n : Nat} (σ : State C Γ)
    (b : MPath C Γ (.ref (.fixed E n))) (i : Val C Γ .uint) (ref : HRef σ.H (.fixed E n))
    (k : PrimTy.uint.Denote) (range : PrimTy.uint.inRange (n : Int) = true)
    (base : b.mvalT σ = .ok ref) (index : i.evalT σ = .ok k)
    (failed : (Checked.cmpU .lt rfl rfl i (Checked.litU n range)).evalT σ = .ok false) :
    Checked.mIdxPG .fixed b i =
      [(Panic.Site.bounds.code, Checked.cmpU .lt rfl rfl i (Checked.litU n range))] ∧
    Panic.Origin (.index σ.heap ref .fixed k) .bounds ∧
    (MPath.loc (.index .fixed b i)).mvalT σ = .error .revert ∧
    (panicStmt Panic.Site.bounds.code
      (Checked.cmpU .lt rfl rfl i (Checked.litU n range))).runR σ =
        .error (THalt.ofData (encodePanic Panic.Site.bounds.code)) :=
  ⟨memory_fixed_index_guards b i range,
    (memory_fixed_index_guard_origin σ b i ref k range base index failed).1,
    (memory_fixed_index_guard_origin σ b i ref k range base index failed).2,
    panic_guard_source_failure σ _ failed _⟩

/-! ## Empty pop (`Stmt.panics`, `0x31`) -/

/-- The guards of `b.pop()`: the path's, then the length check. -/
theorem pop_guards {E : Ty} (b : SPath C Γ (.array E)) :
    (Stmt.pop b).panics = b.panics ++ [(Panic.Site.emptyPop.code,
      Checked.cmpU .gt rfl rfl (.len b rfl) (Checked.litU 0 (by decide)))] := rfl

/-- A failed pop guard: the value at the path is found and has no live
element, the test of the pop producer; the V1 statement reverts. -/
theorem pop_guard_origin {E : Ty} (σ : State C Γ) (b : SPath C Γ (.array E))
    (ref : SRef C (.ref (.array E))) (keep : Bool) (base : b.resolveT σ = .ok ref)
    (failed : (Checked.cmpU .gt rfl rfl (.len b rfl) (Checked.litU 0 (by decide))).evalT σ =
      .ok false) :
    Panic.Origin (.pop σ.storage keep ref) .emptyPop ∧
      (Stmt.pop b).runR σ = .error .revert := by
  cases found : σ.storage.find ref with
  | none =>
    rw [positive_eval, len_found σ b ref base found] at failed
    cases failed
  | some value =>
    rw [positive_eval, storage_guard_length σ b ref value base found] at failed
    have zero : ¬(0 : Int) < ((SVal.view value : ArrView E).n : Int) :=
      of_decide_eq_false (Except.ok.inj failed)
    have empty : (SVal.view value : ArrView E).elems.toList = [] :=
      List.eq_nil_of_length_eq_zero (by rw [SVec.length_toList]; omega)
    exact ⟨Panic.pop_origin σ.storage keep ref value found (by rw [empty]; rfl), by
      simp [Stmt.runR, TRun.pop, base, Storage.pop, found, empty, TRes.ofOpt, bind, Except.bind]⟩

/-- Association at the pop guard of `Stmt.panics`. -/
theorem pop_source {E : Ty} (σ : State C Γ) (b : SPath C Γ (.array E))
    (ref : SRef C (.ref (.array E))) (keep : Bool) (base : b.resolveT σ = .ok ref)
    (failed : (Checked.cmpU .gt rfl rfl (.len b rfl) (Checked.litU 0 (by decide))).evalT σ =
      .ok false) :
    (Stmt.pop b).panics = b.panics ++ [(Panic.Site.emptyPop.code,
      Checked.cmpU .gt rfl rfl (.len b rfl) (Checked.litU 0 (by decide)))] ∧
    Panic.Origin (.pop σ.storage keep ref) .emptyPop ∧
    (Stmt.pop b).runR σ = .error .revert ∧
    (panicStmt Panic.Site.emptyPop.code
      (Checked.cmpU .gt rfl rfl (.len b rfl) (Checked.litU 0 (by decide)))).runR σ =
        .error (THalt.ofData (encodePanic Panic.Site.emptyPop.code)) :=
  ⟨rfl, (pop_guard_origin σ b ref keep base failed).1,
    (pop_guard_origin σ b ref keep base failed).2, panic_guard_source_failure σ _ failed _⟩

end Solidity.Correctness.Panic
