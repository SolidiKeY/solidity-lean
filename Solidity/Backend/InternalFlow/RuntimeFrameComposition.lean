import Solidity.Backend.InternalFlow.RuntimeFrameFootprint
import Solidity.Backend.InternalFlow.RuntimeFrameTarget
import Solidity.Evm.MemoryCalls

/-! Structural scratch transport for EXISTING checked compiler certificates.
The proof component is derived by constructors and inhabited leaves, not a new
execution relation or a simulation oracle. No global admission changes. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.Composition
open Evm Evm.Memory
variable {C : Contract}

def ProgramSafe {b : Nat} {Γ Δ : Ctx} {F : Frag Γ} {P : Prog C Γ Δ}
    (checked : Calls.Program b F P) : Prop :=
  ∀ {L frame lo : Nat} {σ : State C Γ} {base : Nat → Fin W} {m target : Machine},
    StateRepr L b frame F σ base m → b + checked.need ≤ lo → lo ≤ frame →
    AllocationInput b frame (checked.cost σ) σ base m →
    run checked.code m = .ok target 0 → Footprint.Words lo frame m target

def StatementSafe {b : Nat} {Γ Δ : Ctx} {F : Frag Γ} {s : Stmt C Γ Δ}
    (checked : Calls.Statement b F s) : Prop :=
  ∀ {L frame lo : Nat} {σ : State C Γ} {base : Nat → Fin W} {m target : Machine},
    StateRepr L b frame F σ base m → b + checked.need ≤ lo → lo ≤ frame →
    AllocationInput b frame (checked.cost σ) σ base m →
    run checked.code m = .ok target 0 → Footprint.Words lo frame m target

/-- The actual producer is retained with all code/fragment/need/cost fields.
A consumer cannot obtain this wrapper without its checked footprint proof. -/
structure Program (b : Nat) {Γ Δ : Ctx} (F : Frag Γ) (P : Prog C Γ Δ) where
  checked : Calls.Program b F P
  safe : ProgramSafe checked

structure Statement (b : Nat) {Γ Δ : Ctx} (F : Frag Γ) (s : Stmt C Γ Δ) where
  checked : Calls.Statement b F s
  safe : StatementSafe checked

theorem cons_cost {b : Nat} {Γ Δ Ξ : Ctx} {F : Frag Γ}
    {s : Stmt C Γ Δ} {P : Prog C Δ Ξ}
    (head : Calls.Statement b F s) (tail : Calls.Program b head.frag P)
    (σ : State C Γ) (out : Solidity.Out C σ.H Δ) (actual : s.run σ = .ok out) :
    (Calls.cons head tail).cost σ = head.cost σ + tail.cost out.st := by
  dsimp only [Calls.cons]
  rw [actual]
  cases alloc : tail.allocates with
  | false => simp only [tail.zeroCost alloc];rfl
  | true => rfl

def nil (b : Nat) {Γ : Ctx} (F : Frag Γ) : Program (C := C) b F .nil where
  checked := Calls.nil b F
  safe := by
    intro L frame lo σ base m target repr room boundary capacity actual
    have same : m = target := (Evm.Out.ok.inj actual).1
    subst target
    exact Footprint.words_refl lo frame m

/-- The same source-reached allocation split used by Calls.cons supplies the
REAL tail input. Actual error heads absorb the suffix and cannot masquerade
as successful endpoints. -/
def cons {b : Nat} {Γ Δ Ξ : Ctx} {F : Frag Γ} {s : Stmt C Γ Δ} {P : Prog C Δ Ξ}
    (head : Statement b F s) (tail : Program b head.checked.frag P) :
    Program b F (.cons s P) where
  checked := Calls.cons head.checked tail.checked
  safe := by
    intro L frame lo σ base m target repr room boundary capacity actual
    have headRoom : b + head.checked.need ≤ lo := by
      change b + max head.checked.need tail.checked.need ≤ lo at room
      omega
    have tailRoom : b + tail.checked.need ≤ lo := by
      change b + max head.checked.need tail.checked.need ≤ lo at room
      omega
    have firstInput : AllocationInput b frame (head.checked.cost σ) σ base m :=
      capacity.of_le (by change head.checked.cost σ ≤ head.checked.cost σ + _;omega)
    rcases head.checked.sound repr (by omega) firstInput with
      ⟨out,mid,addresses,source,code,represented,stack,extension,growth⟩ | ⟨source,code⟩
    · have input : AllocationInput b frame (head.checked.cost σ + tail.checked.cost out.st) σ base m := by
        rw [← cons_cost head.checked tail.checked σ out source]
        exact capacity
      have next := growth.nextInput input
      have tailRun : run tail.checked.code mid = .ok target 0 := by
        change run (head.checked.code ++ tail.checked.code) m = _ at actual
        rw [run_append_ok code] at actual
        exact actual
      exact Footprint.words_trans (head.safe repr headRoom boundary firstInput code)
        (tail.safe represented tailRoom boundary next tailRun)
    · have impossible : run (head.checked.code ++ tail.checked.code) m = .revert := run_append_revert code
      change run (head.checked.code ++ tail.checked.code) m = _ at actual
      rw [impossible] at actual
      contradiction

def block {b : Nat} {Γ Δ : Ctx} {F : Frag Γ} {P : Prog C Γ Δ}
    (body : Program b F P) : Statement b F (.block P) where
  checked := Calls.block body.checked
  safe := body.safe

/-- Exact source expansion equivalence retains the same proven code
footprint, in addition to the public producer's dependent state transport. -/
def equivalent {b : Nat} {Γ Δ : Ctx} {F : Frag Γ} {s : Stmt C Γ Δ} {P : Prog C Γ Δ}
    (body : Program b F P) (actual : ∀ σ, P.runSt σ = s.runSt σ) : Statement b F s where
  checked := Calls.equivalent body.checked actual
  safe := body.safe
theorem branch_cost {b : Nat} {Γ Δ Ξ : Ctx} {F : Frag Γ}
    (condition : Val C Γ .bool) (cond : CompiledVal b F condition)
    {thn : Prog C Γ Δ} {els : Prog C Γ Ξ}
    (left : Calls.Program b F thn) (right : Calls.Program b F els)
    (σ : State C Γ) (value : PrimTy.bool.Denote)
    (evaluated : condition.evalT σ = .ok value) :
    (Calls.branch condition cond left right).cost σ =
      if boolT value then left.cost σ else right.cost σ := by
  dsimp only [Calls.branch]
  rw [evaluated]
  cases alloc : left.allocates || right.allocates with
  | false =>
    have both := Bool.or_eq_false_iff.mp alloc
    simp only [left.zeroCost both.1,right.zeroCost both.2,ite_self]
    rfl
  | true => rfl

/-- Branching consumes the ACTUALLY selected branch input and the condition's
checked exact machine/word result. Neither skipped allocations nor branch
code jumps can silently change a reserved frame word. -/
def branch {b : Nat} {Γ Δ Ξ : Ctx} {F : Frag Γ}
    (condition : Val C Γ .bool) (cond : CompiledVal b F condition)
    {thn : Prog C Γ Δ} {els : Prog C Γ Ξ}
    (left : Program b F thn) (right : Program b F els) :
    Statement b F (.ite condition thn els) where
  checked := Calls.branch condition cond left.checked right.checked
  safe := by
    intro L frame lo σ base m target repr room boundary capacity actual
    have leftRoom : b + left.checked.need ≤ lo := by
      change b + max left.checked.need right.checked.need ≤ lo at room
      omega
    have rightRoom : b + right.checked.need ≤ lo := by
      change b + max left.checked.need right.checked.need ≤ lo at room
      omega
    rcases cond.cert.correct repr with ⟨value,word,evaluated,represented,executed⟩ | ⟨evaluated,executed⟩
    · have cost := branch_cost condition cond left.checked right.checked σ value evaluated
      rw [cost] at capacity
      obtain rfl := represented.bool_inv
      change run (conditionalCode cond.code left.checked.code right.checked.code) m = _ at actual
      simp only [conditionalCode,List.append_assoc] at actual
      rw [run_append_ok executed] at actual
      cases value
      · have input : AllocationInput b frame (right.checked.cost σ) σ base m := capacity
        rw [run_append_skip (m' := m) (k := left.checked.code.length + 1) rfl,
          show left.checked.code.length + 1 = left.checked.code.length + 1 from rfl,
          exec_append,exec_skip] at actual
        simp only [Out.ok_bind] at actual
        exact right.safe repr rightRoom boundary input actual
      · have input : AllocationInput b frame (left.checked.cost σ) σ base m := capacity
        rw [run_append_skip (m' := m) (k := 0) rfl] at actual
        rcases left.checked.sound repr (by omega) input with
          ⟨out,mid,addresses,source,code,represented,stack,extension,growth⟩ | ⟨source,code⟩
        · have skip : run ([.jump right.checked.code.length] ++ right.checked.code) mid = .ok mid 0 := by
            rw [run_append_skip (m' := mid) (k := right.checked.code.length) rfl]
            exact exec_length _ _
          change run (left.checked.code ++ ([.jump right.checked.code.length] ++ right.checked.code)) m = _ at actual
          rw [run_append_ok code,skip] at actual
          have same := (Evm.Out.ok.inj actual).1
          subst target
          exact left.safe repr leftRoom boundary input code
        · change run (left.checked.code ++ _) m = _ at actual
          rw [run_append_revert code] at actual
          contradiction
    · change run (conditionalCode cond.code left.checked.code right.checked.code) m = _ at actual
      simp only [conditionalCode,List.append_assoc] at actual
      rw [run_append_revert executed] at actual
      contradiction

/-- Existing core value code is store-free. A scalar destination is below the
certificate's real local need, so this leaf derives its entire scratch frame
without an arbitrary memory-preservation premise. -/
def scalar {b : Nat} {Γ : Ctx} (F : Frag Γ) {p : PrimTy}
    (destination : Idx Γ (.val p)) (value : Val C Γ p) (admitted : valIn F value = true) :
    Statement b F (.assignLocal destination value) where
  checked := Calls.plainStmt ⟨F,_,.assign F destination value (Evm.compileVal b value) (.core value admitted)⟩
  safe := by
    intro L frame lo σ base m target repr room boundary capacity actual
    intro address lower upper
    have destinationBound : cellOf b destination < lo := by
      have bound := lvl_lt b destination
      change b + frameNeedStmt (.assignLocal destination value) ≤ lo at room
      have full : Γ.length ≤ frameNeedStmt (.assignLocal destination value) := by
        change Γ.length ≤ max Γ.length (max Γ.length 0)
        omega
      exact Nat.lt_of_lt_of_le bound (by omega)
    have noWrite : codeStoresCell address
        (Evm.compileVal b value ++ [.mstore (cellOf b destination)]) = false := by
      rw [codeStoresCell_append,(noStore_compileVal b value).noCellStore address]
      simp only [codeStoresCell,Instr.storesCell,Bool.false_or,Bool.or_false,beq_eq_false_iff_ne]
      omega
    exact exec_mem noWrite actual
/-- General admitted allocating declarations derive the size from the real
checked Simple evaluation. Actual source cost supplies the same cursor budget;
no source-content or scratch-preservation equation is assumed. -/
def allocate {b : Nat} {Γ : Ctx} (F : Frag Γ) (p : PrimTy) (name : Var)
    (size : Simple C Γ .uint) (positive : 0 < b) (admitted : simpleIn size = true) :
    Statement b F (.declMem (.array (.prim p)) name (some (.newArr size rfl)) rfl rfl) where
  checked := Calls.plainStmt ⟨_,_,.allocate F p name size positive admitted⟩
  safe := by
    intro L frame lo σ base m target repr room boundary capacity actual
    obtain ⟨word,represented,executed⟩ := simple_sim repr.core size admitted
    obtain ⟨a,ha,numeric,rfl⟩ := represented.uint_inv
    have evaluated : size.evalT σ = indexValue ⟨a,ha⟩ := Subtype.ext numeric
    have cost : allocationCostStmt
        (.declMem (.array (.prim p)) name (some (.newArr size rfl)) rfl rfl) σ = a + 1 := by
      change (size.evalT σ).word.val + 1 = a + 1
      have same := Int.ofNat_inj.mp ((word_val (size.evalT σ)).trans numeric)
      rw [same]
    change AllocationInput b frame (allocationCostStmt (.declMem (.array (.prim p)) name (some (.newArr size rfl)) rfl rfl) σ) σ base m at capacity
    rw [cost] at capacity
    rcases capacity with impossible | ⟨hb,cursor,allocator,space⟩
    · omega
    · have spare : cursor.val + (⟨a,ha⟩ : Fin W).val + 1 < W := by
        change cursor.val + a + 1 < W
        simpa only [cost,Nat.add_assoc] using space
      have localBound : b + Γ.length < lo := by
        change b + max Γ.length (max (Γ.length + 1) 0) ≤ lo at room
        omega
      obtain ⟨source,code,represented,allocator,stack,words⟩ := Footprint.declare repr allocator positive
        p size admitted ⟨a,ha⟩ evaluated spare localBound (by omega)
      have same := (Evm.Out.ok.inj (actual.symm.trans code)).1
      exact same.symm ▸ words

def reallocate {b : Nat} {Γ : Ctx} (F : Frag Γ) (p : PrimTy)
    (destination : Idx Γ (.mem (.array (.prim p))))
    (size : Simple C Γ .uint) (positive : 0 < b) (admitted : simpleIn size = true) :
    Statement b F (.rebindMem destination (.newArr size rfl)) where
  checked := Calls.plainStmt ⟨_,_,.reallocate F p destination size positive admitted⟩
  safe := by
    intro L frame lo σ base m target repr room boundary capacity actual
    obtain ⟨word,represented,executed⟩ := simple_sim repr.core size admitted
    obtain ⟨a,ha,numeric,rfl⟩ := represented.uint_inv
    have evaluated : size.evalT σ = indexValue ⟨a,ha⟩ := Subtype.ext numeric
    have cost : allocationCostStmt (.rebindMem destination (.newArr size rfl)) σ = a + 1 := by
      change (size.evalT σ).word.val + 1 = a + 1
      have same := Int.ofNat_inj.mp ((word_val (size.evalT σ)).trans numeric)
      rw [same]
    change AllocationInput b frame (allocationCostStmt (.rebindMem destination (.newArr size rfl)) σ) σ base m at capacity
    rw [cost] at capacity
    rcases capacity with impossible | ⟨hb,cursor,allocator,space⟩
    · omega
    · have spare : cursor.val + (⟨a,ha⟩ : Fin W).val + 1 < W := by
        change cursor.val + a + 1 < W
        simpa only [cost,Nat.add_assoc] using space
      have localBound : b + Γ.length ≤ lo := by
        change b + max Γ.length (max Γ.length 0) ≤ lo at room
        omega
      obtain ⟨source,code,represented,allocator,stack,words⟩ := Footprint.rebind repr allocator positive
        p destination size admitted ⟨a,ha⟩ evaluated spare localBound
      have same := (Evm.Out.ok.inj (actual.symm.trans code)).1
      exact same.symm ▸ words

/-- Actual source success selects the unique checked target, strengthened by
the structurally derived scratch proof. Full representation and allocator
fields remain the existing producer's fields. -/
theorem endpoint {b : Nat} {Γ Δ : Ctx} {F : Frag Γ} {P : Prog C Γ Δ}
    (body : Program b F P) {L frame lo : Nat} {σ : State C Γ}
    {base : Nat → Fin W} {m : Machine} (repr : StateRepr L b frame F σ base m)
    (room : b + body.checked.need ≤ lo) (boundary : lo ≤ frame)
    (capacity : AllocationInput b frame (body.checked.cost σ) σ base m)
    (out : Solidity.Out C σ.H Δ) (source : P.run σ = .ok out) :
    ∃ target addresses, run body.checked.code m = .ok target 0 ∧
      StateRepr L b frame body.checked.frag out.st addresses target ∧
      target.stack = m.stack ∧ BaseExtends σ.H base addresses ∧
      GrowsAllocator b frame (body.checked.cost σ) σ base m out.st addresses target ∧
      Footprint.Words lo frame m target := by
  rcases body.checked.sound repr (by omega) capacity with
    ⟨actual,target,addresses,hs,code,represented,stack,extension,growth⟩ | ⟨hs,code⟩
  · have same := Except.ok.inj (hs.symm.trans source)
    subst actual
    exact ⟨target,addresses,code,represented,stack,extension,growth,
      body.safe repr room boundary capacity code⟩
  · rw [source] at hs
    contradiction
/-- General checked value expressions may read represented memory. Their
existing certificate returns the EXACT input machine with one pushed word,
so only the following real local store contributes to this footprint. -/
def assign {b : Nat} {Γ : Ctx} (F : Frag Γ) {p : PrimTy}
    (destination : Idx Γ (.val p)) (value : Val C Γ p) (compiled : CompiledVal b F value) :
    Statement b F (.assignLocal destination value) where
  checked := Calls.plainStmt ⟨F,_,.assign F destination value compiled.code compiled.cert⟩
  safe := by
    intro L frame lo σ base m target repr room boundary capacity actual
    rcases compiled.cert.correct repr with ⟨v,w,source,represented,code⟩ | ⟨source,code⟩
    · change run (compiled.code ++ [.mstore (cellOf b destination)]) m = _ at actual
      rw [run_append_ok code] at actual
      have store : run [.mstore (cellOf b destination)] (m.push w) =
          .ok (writeMachine m (cellOf b destination) w) 0 := rfl
      rw [store] at actual
      have same := (Evm.Out.ok.inj actual).1
      subst target
      apply Footprint.write_below
      have localBound := lvl_lt b destination
      change b + max Γ.length (max Γ.length 0) ≤ lo at room
      exact Nat.lt_of_lt_of_le localBound (by omega)
    · change run (compiled.code ++ [.mstore (cellOf b destination)]) m = _ at actual
      rw [run_append_revert code] at actual
      contradiction

def declareValue {b : Nat} {Γ : Ctx} (F : Frag Γ) {p : PrimTy}
    (name : Var) (value : Val C Γ p) (compiled : CompiledVal b F value) :
    Statement b F (.declLocal p name (some value)) where
  checked := Calls.plainStmt ⟨_,_,.declare F name value compiled.code compiled.cert⟩
  safe := by
    intro L frame lo σ base m target repr room boundary capacity actual
    rcases compiled.cert.correct repr with ⟨v,w,source,represented,code⟩ | ⟨source,code⟩
    · change run (compiled.code ++ [.mstore (cell (b + Γ.length))]) m = _ at actual
      rw [run_append_ok code] at actual
      have store : run [.mstore (cell (b + Γ.length))] (m.push w) =
          .ok (writeMachine m (cell (b + Γ.length)) w) 0 := rfl
      rw [store] at actual
      have same := (Evm.Out.ok.inj actual).1
      subst target
      apply Footprint.write_below
      change b + max Γ.length (max (Γ.length + 1) 0) ≤ lo at room
      change b + Γ.length < lo
      omega
    · change run (compiled.code ++ [.mstore (cell (b + Γ.length))]) m = _ at actual
      rw [run_append_revert code] at actual
      contradiction

/-- Argument/reference declarations use the actual published pointer copy.
All type/refusal premises are the producer's unchanged premises. -/
def declareAlias {b : Nat} {Γ : Ctx} (F : Frag Γ) {R : RefTy}
    (name : Var) (source : Idx Γ (.mem R)) (mapFree : (Ty.ref R).mapFree = true) :
    Statement (C := C) b F (.declMem R name (some (.alias (.var source mapFree))) rfl mapFree) where
  checked := Calls.plainStmt ⟨_,_,.declareAlias F name source mapFree⟩
  safe := by
    intro L frame lo σ base m target repr room boundary capacity actual address lower upper
    have below : b + Γ.length < lo := by
      change b + max Γ.length (max (Γ.length + 1) 0) ≤ lo at room
      omega
    have noWrite : codeStoresCell address (declareAliasCode b source) = false := by
      simp only [declareAliasCode,codeStoresCell,Instr.storesCell,Bool.false_or,
        Bool.or_false,beq_eq_false_iff_ne]
      change b + Γ.length ≠ address
      omega
    exact exec_mem noWrite actual
def declareDefault {b : Nat} {Γ : Ctx} (F : Frag Γ) (p : PrimTy) (name : Var) :
    Statement (C := C) b F (.declLocal p name none) where
  checked := Calls.plainStmt ⟨_,_,.declareDefault F p name⟩
  safe := by
    intro L frame lo σ base m target repr room boundary capacity actual address lower upper
    have below : b + Γ.length < lo := by
      change b + max Γ.length (max (Γ.length + 1) 0) ≤ lo at room
      omega
    have noWrite : codeStoresCell address [.push w[0],.mstore (cell (b + Γ.length))] = false := by
      simp only [codeStoresCell,Instr.storesCell,Bool.false_or,Bool.or_false,beq_eq_false_iff_ne]
      change b + Γ.length ≠ address
      omega
    exact exec_mem noWrite actual

def defaultArray {b : Nat} {Γ : Ctx} (F : Frag Γ) (p : PrimTy) (name : Var) (positive : 0 < b) :
    Statement (C := C) b F (.declMem (.array (.prim p)) name none rfl rfl) where
  checked := Calls.plainStmt ⟨_,_,.defaultArray F p name _ (.allocate F p name (.lit 0 rfl) positive rfl)⟩
  safe := (allocate F p name (.lit 0 rfl) positive rfl).safe

def alias {b : Nat} {Γ : Ctx} (F : Frag Γ) {R : RefTy}
    (destination source : Idx Γ (.mem R)) (mapFree : (Ty.ref R).mapFree = true) :
    Statement (C := C) b F (.rebindMem destination (.alias (.var source mapFree))) where
  checked := Calls.plainStmt ⟨_,_,.rebind F destination source mapFree⟩
  safe := by
    intro L frame lo σ base m target repr room boundary capacity actual address lower upper
    have below : cellOf b destination < lo := by
      have localBound := lvl_lt b destination
      change b + max Γ.length (max Γ.length 0) ≤ lo at room
      exact Nat.lt_of_lt_of_le localBound (by omega)
    have noWrite : codeStoresCell address (aliasLocalCode b destination source) = false := by
      simp only [aliasLocalCode,codeStoresCell,Instr.storesCell,Bool.false_or,
        Bool.or_false,beq_eq_false_iff_ne]
      omega
    exact exec_mem noWrite actual

/-- Real memory-result export performs one final pointer copy below the
expanded frame's genuine output-context bound. The returned reference is
provided by Calls.memoryReturn's actual reached representation, not a cast. -/
def memoryReturn {b : Nat} {Γ ps Γf : Ctx} {F : Frag Γ}
    (name : Name) (args : Args C Γ ps) (R : RefTy) (result : Var)
    (defaultOk : (Ty.ref R).defaultOkS = true) (mapFree : (Ty.ref R).mapFree = true)
    (body : Prog C (.mem R :: ps) Γf)
    (expanded : Program b F (Calls.expandMem args R result defaultOk mapFree body))
    (outputBound : (.mem R :: (ps ++ Γ)).length ≤ expanded.checked.need) :
    Statement b F (.call name args (.mem R result defaultOk mapFree) body) where
  checked := Calls.memoryReturn name args R result defaultOk mapFree body expanded.checked
  safe := by
    intro L frame lo σ base m target repr room boundary capacity actual
    change b + expanded.checked.need ≤ lo at room
    rcases expanded.checked.sound repr (by omega) capacity with
      ⟨out,mid,addresses,source,code,represented,stack,extension,growth⟩ | ⟨source,code⟩
    · have next : run (Calls.returnPointerCode b Γ ps) mid = .ok target 0 := by
        change run (expanded.checked.code ++ Calls.returnPointerCode b Γ ps) m = _ at actual
        rw [run_append_ok code] at actual
        exact actual
      apply Footprint.words_trans (expanded.safe repr room boundary capacity code)
      intro address lower upper
      have bound : b + Γ.length < lo := by
        simp only [List.length_cons,List.length_append] at outputBound
        omega
      have noWrite : codeStoresCell address (Calls.returnPointerCode b Γ ps) = false := by
        simp only [Calls.returnPointerCode,codeStoresCell,Instr.storesCell,
          Bool.false_or,Bool.or_false,beq_eq_false_iff_ne]
        change b + Γ.length ≠ address
        omega
      exact exec_mem noWrite next
    · change run (expanded.checked.code ++ Calls.returnPointerCode b Γ ps) m = _ at actual
      rw [run_append_revert code] at actual
      contradiction

mutual
/-- Structural selection over finite intrinsic syntax. Unsupported leaves
return none; this is a footprint capability selector, not a global admission
change or a numerical call-depth search. -/
def compileStatement (b : Nat) {Γ Δ : Ctx} (F : Frag Γ) :
    (s : Stmt C Γ Δ) → Option (Statement b F s)
  | .block body => do
    let selected ← compileProgram b F body
    pure (block selected)
  | .ite condition thn els => do
    let cond ← Memory.compileVal b F condition
    let left ← compileProgram b F thn
    let right ← compileProgram b F els
    pure (branch condition cond left right)
  | .assignLocal destination value => do
    let selected ← Memory.compileVal b F value
    pure (assign F destination value selected)
  | .declLocal p name (some value) => do
    let selected ← Memory.compileVal b F value
    pure (declareValue F name value selected)
  | .declLocal p name none => some (declareDefault F p name)
  | .declMem R name (some (.alias (.var source hm))) _ _ =>
    some (declareAlias F name source hm)
  | .declMem (.array (.prim p)) name (some (.newArr size _)) _ _ =>
    if hb : 0 < b then if hn : simpleIn size = true then some (allocate F p name size hb hn) else none else none
  | .declMem (.array (.prim p)) name none _ _ =>
    if hb : 0 < b then some (defaultArray F p name hb) else none
  | .rebindMem destination (.alias (.var source hm)) => some (alias F destination source hm)
  | @Solidity.Stmt.rebindMem _ _ (.array (.prim p)) destination (.newArr size _) =>
    if hb : 0 < b then if hn : simpleIn size = true then some (reallocate F p destination size hb hn) else none else none
  | _ => none

def compileProgram (b : Nat) {Γ Δ : Ctx} (F : Frag Γ) :
    (P : Prog C Γ Δ) → Option (Program b F P)
  | .nil => some (nil b F)
  | .cons head tail => do
    let first ← compileStatement b F head
    let rest ← compileProgram b first.checked.frag tail
    pure (cons first rest)
end

/-- Consume the actual published finite call expansions. The structural body
selector currently refuses nested call leaves; that is unfinished footprint
coverage, never a source exclusion or recursion theorem. -/
def compileCall (b : Nat) {Γ ps rs Δ Γf : Ctx} (F : Frag Γ) (name : Name)
    (args : Args C Γ ps) (ret : CallRet Γ rs Δ) (body : Prog C (rs ++ ps) Γf) :
    Option (Statement b F (.call name args ret body)) :=
  CallRet.casesOn (motive := fun rs _ ret => (body : Prog C (rs ++ ps) Γf) →
      Option (Statement b F (.call name args ret body))) ret
    (fun body => do
      let out ← compileProgram b F (Calls.expandNone args body)
      pure (equivalent out (Calls.expandNone_run name args body)))
    (fun p result destination body => do
      let out ← compileProgram b F (Calls.expandVal args p result destination body)
      pure (equivalent out (Calls.expandVal_run name args p result destination body)))
    (fun _ _ => none)
    (fun R result hd hm body => do
      let out ← compileProgram b F (Calls.expandMem args R result hd hm body)
      if bound : (.mem R :: (ps ++ Γ)).length ≤ out.checked.need then
        pure (memoryReturn name args R result hd hm body out bound)
      else none)
    (fun _ _ _ => none) body
/-- Transport an actual certificate across a PROVED equality of fragment
flags. No flag is promoted, inferred from liveness, or silently discarded. -/
def reflag {b : Nat} {Γ Δ : Ctx} {F G : Frag Γ} {s : Stmt C Γ Δ}
    (equal : F = G) (selected : Statement b G s) : Statement b F s := equal.symm ▸ selected

theorem reflag_code {b : Nat} {Γ Δ : Ctx} {F G : Frag Γ} {s : Stmt C Γ Δ}
    (equal : F = G) (selected : Statement b G s) :
    (reflag equal selected).checked.code = selected.checked.code := by
  cases equal
  rfl

theorem reflag_fields {b : Nat} {Γ Δ : Ctx} {F G : Frag Γ} {s : Stmt C Γ Δ}
    (equal : F = G) (selected : Statement b G s) :
    ((reflag equal selected).checked.code,(reflag equal selected).checked.frag,
      (reflag equal selected).checked.need,(reflag equal selected).checked.cost) =
    (selected.checked.code,selected.checked.frag,selected.checked.need,selected.checked.cost) := by
  cases equal
  rfl

theorem reflag_selection {b : Nat} {Γ ps rs Δ Γf : Ctx} {F G : Frag Γ}
    (equal : F = G) (name : Name) (args : Args C Γ ps) (ret : CallRet Γ rs Δ)
    (body : Prog C (rs ++ ps) Γf) (selected : Statement b G (.call name args ret body))
    (actual : compileCall b G name args ret body = some selected) :
    compileCall b F name args ret body = some (reflag equal selected) := by
  cases equal
  exact actual
/-- Exact intrinsic normalization retains the source statement as the
certificate index. The scratch proof follows the SAME code/need/cost, while
source agreement is the existing checked statement_run theorem. -/
def normalizeStatement {b : Nat} {Γ Δ : Ctx} {F : Frag Γ} (source : Stmt C Γ Δ)
    (selected : Statement b F (RuntimeFrame.statement source)) : Statement b F source where
  checked := {
    frag := selected.checked.frag
    code := selected.checked.code
    need := selected.checked.need
    cost := selected.checked.cost
    allocates := selected.checked.allocates
    zeroCost := selected.checked.zeroCost
    sound := by
      intro L frame σ base m repr room capacity
      have result := selected.checked.sound repr room capacity
      have same : (RuntimeFrame.statement source).run σ = source.run σ :=
        congrFun (RuntimeFrame.statement_run source) σ
      rw [same] at result
      exact result }
  safe := selected.safe

/-- Actual callRec frame transport for a supported FINITE supplied body.
No unrolling index is searched or exhausted execution replaced by success.
Nested-call/loop coverage remains the structural selector's open work. -/
def compileRecursive (b : Nat) {Γ ps rs Δ : Ctx} (F : Frag Γ) (name : Name) (depth : Nat)
    (args : Args C Γ ps) (ret : CallRet Γ rs Δ)
    (body : Unit → Prog C (rs ++ ps) (rs ++ ps)) :
    Option (Statement b F (.callRec name depth args ret body)) :=
  (compileCall b F name args ret (RuntimeFrame.program (body ()))).map
    (normalizeStatement (.callRec name depth args ret body))

theorem recursive_index {b : Nat} {Γ ps rs Δ : Ctx} (F : Frag Γ) (name : Name)
    (first second : Nat) (args : Args C Γ ps) (ret : CallRet Γ rs Δ)
    (body : Unit → Prog C (rs ++ ps) (rs ++ ps)) :
    (compileRecursive b F name first args ret body).map (fun out => out.checked.code) =
    (compileRecursive b F name second args ret body).map (fun out => out.checked.code) := by
  simp only [compileRecursive,Option.map_map]
  rfl
end Solidity.Backend.InternalFlow.RuntimeFrame.Composition
