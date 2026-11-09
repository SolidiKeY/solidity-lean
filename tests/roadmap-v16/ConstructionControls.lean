import Solidity.Examples.Roadmap.V16.ConstructionCompilation
import Solidity.Evm.MemoryReferenceArrayRebindExamples
import Solidity.Examples.Roadmap.V16.ConstructionConsumer
import Solidity.Evm.MemoryObjectConstructionExamples
import Lean

/-! Actual published construction fixtures, read only. No duplicated source AST,
compiler, execution semantics or assumed success. -/
open Lean Elab Term in
elab "publishedConstruction%" n:ident : term => do
  let name := mkPrivateNameCore `Solidity.Evm.MemoryObjectConstructionExamples
    (`Solidity.Evm.Memory.ConstructionExamples ++ n.getId)
  unless (← getEnv).contains name do throwError "missing published construction fixture {name}"
  return mkConst name

open Lean Elab Term in
elab "publishedRebind%" n:ident : term => do
  let name := mkPrivateNameCore `Solidity.Evm.MemoryReferenceArrayRebindExamples
    (`Solidity.Evm.Memory.ReferenceArrayRebindExamples ++ n.getId)
  unless (← getEnv).contains name do throwError "missing published rebind fixture {name}"
  return mkConst name

namespace Solidity.Roadmap.V16.ConstructionControls
open Solidity.Evm
abbrev K := publishedConstruction% C
abbrev OutputCtx : Ctx := publishedConstruction% Δ
def P : Prog K [] OutputCtx := publishedConstruction% program
attribute [irreducible] P
def compiled : Compiler.Compilation 1 (Frag.init []) P := by
  simpa only [P] using (publishedConstruction% compiled)
attribute [irreducible] compiled
abbrev bases := publishedConstruction% base
abbrev initial := publishedConstruction% state
abbrev machine := publishedConstruction% machine

theorem path : compiled.isConstruction = true := by decide +kernel

theorem input : compiled.Input 1 8 bases initial machine := by
  simpa only [compiled, P] using Memory.ConstructionExamples.compiled_input

theorem cost : compiled.allocationCost initial = 15 := by
  rw [construction_allocation_cost compiled path]
  simpa only [P] using Memory.ConstructionExamples.source_cost

/-- A projection of the existing typed result; no execution semantics. -/
def observe (r : TRes (Solidity.Out K [] OutputCtx)) : Option Nat := do
  let o ← r.toOption
  pure (TEnv.get (.here : Idx OutputCtx (.val .uint)) o.st.env).val.toNat

theorem observed_success {r : TRes (Solidity.Out K [] OutputCtx)} {n : Nat}
    (observed : observe r = some n) : ∃ o, r = .ok o ∧
      (TEnv.get (.here : Idx OutputCtx (.val .uint)) o.st.env).val.toNat = n := by
  cases r with
  | error e => cases observed
  | ok o => exact ⟨o, rfl, Option.some.inj observed⟩

theorem observed : observe (P.run initial) = some 11013 := by
  simpa only [P, observe] using Memory.ConstructionExamples.source_result

theorem source_exists : ∃ o : Solidity.Out K [] OutputCtx, P.run initial = .ok o := by
  obtain ⟨o,hs,_⟩ := observed_success observed
  exact ⟨o,hs⟩

theorem get_source {α : Type} {r : TRes α} (h : r.toOption.isSome = true) :
    r = .ok (r.toOption.get h) := by
  cases r with
  | error e => cases h
  | ok o => rfl

theorem positive : (P.run initial).toOption.isSome = true := by
  obtain ⟨o,h⟩ := source_exists
  simp only [h, Except.toOption, Option.isSome_some]

def output : Solidity.Out K [] OutputCtx := (P.run initial).toOption.get positive
attribute [irreducible] output

theorem source : P.run initial = .ok output := by
  simpa only [output] using (get_source (r := P.run initial) positive)

def actualAnswer : PrimTy.uint.Denote := TEnv.get .here output.st.env
attribute [irreducible] actualAnswer

theorem answer : actualAnswer = ⟨11013, by decide⟩ := by
  obtain ⟨o,hs,value⟩ := observed_success observed
  have eq : o = output := Except.ok.inj (hs.symm.trans source)
  subst o
  have natValue : actualAnswer.val.toNat = 11013 := by
    simpa only [actualAnswer] using value
  apply Subtype.ext
  have nonnegative := PrimTy.uint_nonneg actualAnswer
  change actualAnswer.val = 11013
  omega

def post : Spec K OutputCtx := .eq (.pvV .here) (.app0 (.lit ⟨11013, by decide⟩))

theorem diamond : Spec.sat initial (.diamond P post) := by
  rw [Spec.sat, source]
  refine ⟨actualAnswer, ?_, congrArg some answer.symm⟩
  simp only [actualAnswer, Tm.eval]

theorem represented : ∃ o m' base', P.run initial = .ok o ∧
    run compiled.code machine = .ok m' 0 ∧ m'.stack = [w[77]] ∧
    Memory.Objects.StateRepr 1 1 8 compiled.frag o.st base' m' ∧
    Memory.BaseExtends initial.H bases base' ∧
    Memory.Objects.GrowsAllocator 1 8 (compiled.allocationCost initial)
      initial bases machine o.st base' m' ∧ Spec.sat o.st post := by
  exact construction_diamond (C := K) (b := 1) (L := 1) (frame := 8)
    (Γ := []) (Δ := OutputCtx) (F := Frag.init []) (P := P)
    compiled path (σ := initial) (base := bases) (m := machine) input (φ := post) diamond

theorem public_represented : ∃ o m', P.run initial = .ok o ∧
    run compiled.code machine = .ok m' 0 ∧ m'.stack = [w[77]] ∧
    compiled.Rep 1 8 bases initial machine o.st m' ∧ Spec.sat o.st post := by
  obtain ⟨o,m',base',hs,ht,stack,repr,extension,grows,hp⟩ := represented
  exact ⟨o,m',hs,ht,stack,(construction_rep_iff (C := K) (b := 1) (L := 1) (frame := 8) (Γ := []) (Δ := OutputCtx) (F := Frag.init []) (P := P) compiled path (σ := initial) (τ := o.st) (base := bases) (m := machine) (m' := m')).2
    ⟨base',repr,extension,grows⟩,hp⟩

theorem wrong_frame : ¬ compiled.Input 1 0 bases initial machine := by
  apply construction_small_frame compiled path
  exact Nat.lt_of_lt_of_le (by decide : 0 < 1) (Nat.le_add_right 1 _)

theorem false_post : ¬ Spec.sat initial (.diamond P (.not .tt)) := by
  intro h
  obtain ⟨_,_,_,_,_,_,_,_,_,bad⟩ := construction_diamond (C := K) (b := 1) (L := 1) (frame := 8) (Γ := []) (Δ := OutputCtx) (F := Frag.init []) (P := P) compiled path (σ := initial) (base := bases) (m := machine) input (φ := .not .tt) h
  exact bad trivial

theorem no_wrong_revert : run compiled.code machine ≠ .revert := by
  obtain ⟨_,m',_,_,ht,_⟩ := represented
  intro h
  rw [h] at ht
  cases ht

theorem exact_boundary_input : compiled.Input 1 8 bases initial
    ((publishedConstruction% boundaryMachine) (publishedConstruction% exactCursor)) := by
  simpa only [compiled, P] using Memory.ConstructionExamples.exact_capacity_input

theorem insufficient_capacity : ¬ compiled.Input 1 8 bases initial
    ((publishedConstruction% boundaryMachine) (publishedConstruction% badCursor)) := by
  simpa only [compiled, P] using Memory.ConstructionExamples.insufficient_capacity_refuted

abbrev Child : RefTy := publishedConstruction% child
def retained : Idx OutputCtx (.mem Child) := .there .here
def oldLeft : Idx OutputCtx (.mem Child) := .there (.there (.there .here))
def otherChild : Idx OutputCtx (.mem Child) := .there (.there .here)

/-- Test-local equality decision uses the existing intrinsic reference identity.
Proof fields are equal by proof irrelevance; no global instance/profile changes. -/
local instance {H : HTy} {R : RefTy} : DecidableEq (HRef H R) := fun a b =>
  if h : a.id = b.id then .isTrue (by cases a; cases b; cases h; rfl)
  else .isFalse (fun eq => h (congrArg HRef.id eq))

theorem source_alias : TEnv.get retained output.st.env = TEnv.get oldLeft output.st.env := by
  decide +kernel

theorem source_distinct : TEnv.get retained output.st.env ≠ TEnv.get otherChild output.st.env := by
  decide +kernel

/-- The NEW specification witness retains the represented source alias. -/
theorem represented_alias : ∃ m' base', run compiled.code machine = .ok m' 0 ∧
    m'.stack = [w[77]] ∧ Memory.Objects.StateRepr 1 1 8 compiled.frag output.st base' m' ∧
    Memory.BaseExtends initial.H bases base' ∧
    Memory.Objects.GrowsAllocator 1 8 (compiled.allocationCost initial)
      initial bases machine output.st base' m' ∧ Spec.sat output.st post ∧
    m'.mem (cellOf 1 retained) = m'.mem (cellOf 1 oldLeft) := by
  obtain ⟨o,m',base',hs,ht,stack,repr,extension,grows,hp⟩ := represented
  have eq : o = output := Except.ok.inj (hs.symm.trans source)
  subst o
  obtain ⟨ref,href,_⟩ := repr.pointers retained
  have left : TEnv.get oldLeft output.st.env = some ref := source_alias.symm.trans href
  have alias := construction_alias (C := K) (L := 1) (b := 1) (frame := 8)
    (Γ := OutputCtx) (F := compiled.frag) (σ := output.st) (base := base') (m := m')
    repr retained oldLeft ref href left
  exact ⟨m',base',ht,stack,repr,extension,grows,hp,alias⟩

/-- Numeric target result derived from the NEW representation witness. -/
theorem machine_value : ∃ m' base', run compiled.code machine = .ok m' 0 ∧
    m'.stack = [w[77]] ∧ Memory.Objects.StateRepr 1 1 8 compiled.frag output.st base' m' ∧
    Memory.BaseExtends initial.H bases base' ∧
    Memory.Objects.GrowsAllocator 1 8 (compiled.allocationCost initial)
      initial bases machine output.st base' m' ∧ Spec.sat output.st post ∧
    m'.mem 7 = w[11013] := by
  obtain ⟨o,m',base',hs,ht,stack,repr,extension,grows,hp⟩ := represented
  have eq : o = output := Except.ok.inj (hs.symm.trans source)
  subst o
  have hv := repr.core.vals (.here : Idx OutputCtx (.val .uint))
  change ReprV .uint (TEnv.get (.here : Idx OutputCtx (.val .uint)) output.st.env) (m'.mem 7) at hv
  have valEq : (TEnv.get (.here : Idx OutputCtx (.val .uint)) output.st.env).val = 11013 := by
    simpa only [actualAnswer] using congrArg Subtype.val answer
  obtain ⟨a,ha,he,hw⟩ := hv.uint_inv
  have aEq : a = 11013 := by rw [valEq] at he; omega
  subst a
  exact ⟨m',base',ht,stack,repr,extension,grows,hp,hw⟩

/-- Actual input and entry allocator DERIVE cost capacity and exact cursor31. -/
theorem cursor : ∃ o m' base', P.run initial = .ok o ∧ run compiled.code machine = .ok m' 0 ∧
    m'.stack = [w[77]] ∧ Memory.Objects.StateRepr 1 1 8 compiled.frag o.st base' m' ∧
    Memory.BaseExtends initial.H bases base' ∧
    Memory.Objects.GrowsAllocator 1 8 (compiled.allocationCost initial)
      initial bases machine o.st base' m' ∧ Spec.sat o.st post ∧ m'.mem 0 = w[31] := by
  obtain ⟨o,m',base',space,hs,ht,stack,repr,extension,grows,hp,allocator,cell⟩ :=
    construction_diamond_cursor (C := K) (b := 1) (L := 1) (frame := 8)
      (Γ := []) (Δ := OutputCtx) (F := Frag.init []) (P := P) compiled path
      (σ := initial) (base := bases) (m := machine) input (φ := post) diamond (wmod 16)
      (by decide) Memory.ConstructionExamples.initial_allocator
  have eq : (.val ⟨(wmod 16).val + compiled.allocationCost initial,space⟩ : Word) = w[31] := by
    apply congrArg Word.val
    apply Fin.ext
    change 16 + compiled.allocationCost initial = 31
    have hcost := cost
    omega
  exact ⟨o,m',base',hs,ht,stack,repr,extension,grows,hp,cell.trans eq⟩

def wrongPost : Spec K OutputCtx := .eq (.pvV .here) (.app0 (.lit ⟨11014,by decide⟩))

theorem wrong_value : ¬ Spec.sat initial (.diamond P wrongPost) := by
  rw [Spec.sat,source]
  change ¬ (∃ v, (Tm.pvV .here : Tm K OutputCtx (.val .uint)).eval output.st = some v ∧ _ = some v)
  rintro ⟨v,hv,hw⟩
  have actual : (Tm.pvV .here : Tm K OutputCtx (.val .uint)).eval output.st = some actualAnswer := by
    simp only [actualAnswer,Tm.eval]
  rw [actual] at hv
  have values : actualAnswer = (⟨11014,by decide⟩ : PrimTy.uint.Denote) :=
    (Option.some.inj hv).trans (Option.some.inj hw).symm
  exact (by decide : (⟨11013,by decide⟩ : PrimTy.uint.Denote) ≠ ⟨11014,by decide⟩)
    (answer.symm.trans values)


/-- Every cell in the complete frame/gap/sentinel/allocated prefix, ordered. -/
def orderedCells : Evm.Out → Option (List Nat)
  | .ok m 0 => (List.range 32).mapM fun a => match m.mem a with | .val w => some w.val | _ => none
  | _ => none

theorem ordered_transport : ∃ o m' base', P.run initial = .ok o ∧
    run compiled.code machine = .ok m' 0 ∧ m'.stack = [w[77]] ∧
    Memory.Objects.StateRepr 1 1 8 compiled.frag o.st base' m' ∧
    Memory.BaseExtends initial.H bases base' ∧
    Memory.Objects.GrowsAllocator 1 8 (compiled.allocationCost initial)
      initial bases machine o.st base' m' ∧ Spec.sat o.st post ∧
    orderedCells (.ok m' 0) = orderedCells (run compiled.code machine) := by
  obtain ⟨o,m',base',hs,ht,stack,repr,extension,grows,hp⟩ := represented
  exact ⟨o,m',base',hs,ht,stack,repr,extension,grows,hp,congrArg orderedCells ht.symm⟩

/-- info: some [31, 16, 2, 26, 22, 24, 22, 11013, 0, 0, 0, 0, 0, 0, 0, 99, 0, 2, 24, 22, 0, 0, 1, 11, 1, 13, 2, 29, 30, 0, 0, 0] -/
#guard_msgs in #eval orderedCells (run compiled.code machine)
/-- info: false -/
#guard_msgs in #eval orderedCells (run compiled.code machine) == some
  [30,16,2,26,22,24,22,11013,0,0,0,0,0,0,0,99,0,2,24,22,0,0,1,11,1,13,2,29,30,0,0,0]
/-- info: false -/
#guard_msgs in #eval orderedCells (run compiled.code machine) == some
  [31,16,2,26,22,24,24,11013,0,0,0,0,0,0,0,99,0,2,24,22,0,0,1,11,1,13,2,29,30,0,0,0]

namespace boundary
abbrev entry := (publishedConstruction% boundaryMachine) (publishedConstruction% exactCursor)
abbrev cursor := publishedConstruction% exactCursor
def lastCursor : Fin W := ⟨W-1,by
  have h : 1 < W := by decide
  omega⟩

theorem allocator : Memory.Objects.AllocatorRepr initial.heap bases 8 cursor entry :=
  (publishedConstruction% boundary_allocator) cursor (by
    change 8 ≤ W - 16
    have h : 24 < W := by decide
    omega)

theorem successful_last_cursor : ∃ o m' base', P.run initial = .ok o ∧ run compiled.code entry = .ok m' 0 ∧
    m'.stack = entry.stack ∧ Memory.Objects.StateRepr 1 1 8 compiled.frag o.st base' m' ∧
    Memory.BaseExtends initial.H bases base' ∧
    Memory.Objects.GrowsAllocator 1 8 (compiled.allocationCost initial)
      initial bases entry o.st base' m' ∧ Spec.sat o.st post ∧ m'.mem 0 = .val lastCursor := by
  obtain ⟨o,m',base',space,hs,ht,stack,repr,extension,grows,hp,next,cell⟩ :=
    construction_diamond_cursor (C := K) (b := 1) (L := 1) (frame := 8)
      (Γ := []) (Δ := OutputCtx) (F := Frag.init []) (P := P) compiled path
      (σ := initial) (base := bases) (m := entry) exact_boundary_input (φ := post)
      diamond cursor (by decide) allocator
  have eq : (.val ⟨cursor.val + compiled.allocationCost initial,space⟩ : Word) =
      .val lastCursor := by
    apply congrArg Word.val
    apply Fin.ext
    change W - 16 + compiled.allocationCost initial = W - 1
    have hcost := cost
    have hw : 16 < W := by decide
    omega
  exact ⟨o,m',base',hs,ht,stack,repr,extension,grows,hp,cell.trans eq⟩
end boundary

namespace unreachable
abbrev program := publishedConstruction% unreachable
abbrev compiled := publishedConstruction% unreachableCompiled

theorem path : compiled.isConstruction = true := by decide +kernel

theorem input : compiled.Input 1 8 bases initial machine := Memory.ConstructionExamples.unreachable_input

theorem reached_cost : compiled.allocationCost initial = 5 := by
  rw [construction_allocation_cost compiled path]
  exact Memory.ConstructionExamples.unreachable_cost

theorem box : Spec.sat initial (.box program (.not .tt)) := by
  simp only [Spec.sat,Memory.ConstructionExamples.unreachable_source,ne_eq,reduceCtorEq,not_false_eq_true]

theorem exact_revert : program.run initial = .error .revert ∧ run compiled.code machine = .revert := by
  rcases construction_box compiled path input box with ⟨_,_,_,_,_,_,_,_,_,bad⟩ | h
  · exact (bad trivial).elim
  · exact h
end unreachable

namespace bounds
abbrev program := publishedConstruction% failing
abbrev failed := publishedConstruction% failed

theorem path (k : Fin 3) : (failed k).isConstruction = true := by
  have h : ∀ k : Fin 3, (failed k).isConstruction = true := by decide +kernel
  exact h k

theorem input (k : Fin 3) : (failed k).Input 1 8 bases initial machine :=
  Memory.ConstructionExamples.failed_input k

theorem box (k : Fin 3) : Spec.sat initial (.box (program k) (.not .tt)) := by
  simp only [Spec.sat, Memory.ConstructionExamples.source_bounds k,
    ne_eq, reduceCtorEq, not_false_eq_true]

theorem exact_revert (k : Fin 3) : (program k).run initial = .error .revert ∧
    run (failed k).code machine = .revert := by
  rcases construction_box (failed k) (path k) (input k) (box k) with
    ⟨_,_,_,_,_,_,_,_,_,bad⟩ | h
  · exact (bad trivial).elim
  · exact h

theorem no_diamond (k : Fin 3) : ¬ Spec.sat initial (.diamond (program k) .tt) := by
  intro h
  obtain ⟨o,_,_,hs,_⟩ := construction_diamond (failed k) (path k) (input k) h
  rw [(exact_revert k).1] at hs
  cases hs
theorem wrong_fault (k : Fin 3) : run (failed k).code machine ≠ .fault := by
  rw [(exact_revert k).2]
  intro h
  cases h

theorem wrong_payload (k : Fin 3) : (program k).run initial ≠ .error (.revertWith [9]) := by
  rw [(exact_revert k).1]
  intro h
  cases h

theorem all_three :
    ((program 0).run initial = .error .revert ∧ run (failed 0).code machine = .revert) ∧
    ((program 1).run initial = .error .revert ∧ run (failed 1).code machine = .revert) ∧
    ((program 2).run initial = .error .revert ∧ run (failed 2).code machine = .revert) :=
  ⟨exact_revert 0,exact_revert 1,exact_revert 2⟩

end bounds
/-! Further actual construction combinations: zero runtime extent, fixed-child
zero/rebinding and nonempty fixed-child alias escape. -/
def headObserve {C : Contract} {H : HTy} {Δ : Ctx}
    (r : TRes (Solidity.Out C H (.val .uint :: Δ))) : Option Nat := do
  let o ← r.toOption
  pure (TEnv.get .here o.st.env).val.toNat

theorem head_success {C : Contract} {H : HTy} {Δ : Ctx}
    {r : TRes (Solidity.Out C H (.val .uint :: Δ))} {n : Nat}
    (observed : headObserve r = some n) : ∃ o, r = .ok o ∧
      (TEnv.get (.here : Idx (.val .uint :: Δ) (.val .uint)) o.st.env).val.toNat = n := by
  cases r with
  | error e => cases observed
  | ok o => exact ⟨o,rfl,Option.some.inj observed⟩

theorem head_diamond {C : Contract} {Γ Δ : Ctx} {σ : State C Γ}
    {P : Prog C Γ (.val .uint :: Δ)} (n : PrimTy.uint.Denote)
    (observed : headObserve (P.run σ) = some n.val.toNat) :
    Spec.sat σ (.diamond P (.eq (.pvV .here) (.app0 (.lit n)))) := by
  obtain ⟨o,hs,value⟩ := head_success observed
  have eq : TEnv.get (.here : Idx (.val .uint :: Δ) (.val .uint)) o.st.env = n := by
    apply Subtype.ext
    have hn := PrimTy.uint_nonneg n
    have hv := PrimTy.uint_nonneg (TEnv.get (.here : Idx (.val .uint :: Δ) (.val .uint)) o.st.env)
    omega
  rw [Spec.sat,hs]
  refine ⟨n,?_,rfl⟩
  simp only [Tm.eval,eq]

namespace runtimeZero
abbrev K := publishedConstruction% C
abbrev OutputCtx : Ctx := publishedConstruction% BoundsΔ
def P : Prog K [] OutputCtx := publishedConstruction% zeroProgram
attribute [irreducible] P
def compiled : Compiler.Compilation 1 (Frag.init []) P := by
  simpa only [P] using (publishedConstruction% zeroCompiled)
attribute [irreducible] compiled
abbrev initial := publishedConstruction% state
abbrev machine := publishedConstruction% machine
abbrev bases := publishedConstruction% base

theorem path : compiled.isConstruction = true := by decide +kernel

theorem input : compiled.Input 1 8 bases initial machine := by
  simpa only [compiled,P] using Solidity.Evm.Memory.ConstructionExamples.zero_public_input

theorem observed : headObserve (P.run initial) = some 0 := by
  simpa only [P,headObserve] using Solidity.Evm.Memory.ConstructionExamples.zero_public_source

def post : Spec K OutputCtx := .eq (.pvV .here) (.app0 (.lit ⟨0,by decide⟩))

theorem diamond : Spec.sat initial (.diamond P post) :=
  head_diamond ⟨0,by decide⟩ observed

theorem cost : compiled.allocationCost initial = 1 := by
  rw [construction_allocation_cost compiled path]
  decide +kernel

theorem represented : ∃ o m' base', P.run initial = .ok o ∧ run compiled.code machine = .ok m' 0 ∧
    m'.stack = [w[77]] ∧ Memory.Objects.StateRepr 1 1 8 compiled.frag o.st base' m' ∧
    Memory.BaseExtends initial.H bases base' ∧
    Memory.Objects.GrowsAllocator 1 8 (compiled.allocationCost initial)
      initial bases machine o.st base' m' ∧ Spec.sat o.st post := by
  exact construction_diamond (C := K) (b := 1) (L := 1) (frame := 8)
    (Γ := []) (Δ := OutputCtx) (F := Frag.init []) (P := P) compiled path
    (σ := initial) (base := bases) (m := machine) input (φ := post) diamond

theorem wrong_frame : ¬ compiled.Input 1 0 bases initial machine := by
  apply construction_small_frame compiled path
  exact Nat.lt_of_lt_of_le (by decide : 0 < 1) (Nat.le_add_right 1 _)

theorem false_post : ¬ Spec.sat initial (.diamond P (.not .tt)) := by
  intro h
  obtain ⟨_,_,_,_,_,_,_,_,_,bad⟩ := construction_diamond (C := K) (b := 1) (L := 1) (frame := 8)
    (Γ := []) (Δ := OutputCtx) (F := Frag.init []) (P := P) compiled path
    (σ := initial) (base := bases) (m := machine) input (φ := .not .tt) h
  exact bad trivial

theorem ordered_transport : ∃ o m' base', P.run initial = .ok o ∧ run compiled.code machine = .ok m' 0 ∧
    m'.stack = [w[77]] ∧ Memory.Objects.StateRepr 1 1 8 compiled.frag o.st base' m' ∧
    Memory.BaseExtends initial.H bases base' ∧
    Memory.Objects.GrowsAllocator 1 8 (compiled.allocationCost initial)
      initial bases machine o.st base' m' ∧ Spec.sat o.st post ∧
    orderedCells (.ok m' 0) = orderedCells (run compiled.code machine) := by
  obtain ⟨o,m',base',hs,ht,stack,repr,extension,grows,hp⟩ := represented
  exact ⟨o,m',base',hs,ht,stack,repr,extension,grows,hp,congrArg orderedCells ht.symm⟩

/-- info: some [17, 0, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 99, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] -/
#guard_msgs in #eval orderedCells (run compiled.code machine)
/-- info: false -/
#guard_msgs in #eval orderedCells (run compiled.code machine) == some [16, 0, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 99, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
end runtimeZero

namespace fixedZero
abbrev K := publishedConstruction% C
abbrev OutputCtx : Ctx := publishedConstruction% FixedZeroΔ
def P : Prog K [] OutputCtx := publishedConstruction% fixedZeroProgram
attribute [irreducible] P
def compiled : Compiler.Compilation 1 (Frag.init []) P := by
  simpa only [P] using (publishedConstruction% fixedZeroCompiled)
attribute [irreducible] compiled
abbrev initial := publishedConstruction% state
abbrev machine := publishedConstruction% machine
abbrev bases := publishedConstruction% base

theorem path : compiled.isConstruction = true := by decide +kernel

theorem input : compiled.Input 1 8 bases initial machine := by
  simpa only [compiled,P] using Solidity.Evm.Memory.ConstructionExamples.fixed_zero_input

theorem observed : headObserve (P.run initial) = some 0 := by
  decide +kernel

def post : Spec K OutputCtx := .eq (.pvV .here) (.app0 (.lit ⟨0,by decide⟩))

theorem diamond : Spec.sat initial (.diamond P post) :=
  head_diamond ⟨0,by decide⟩ observed

theorem cost : compiled.allocationCost initial = 2 := by
  rw [construction_allocation_cost compiled path]
  decide +kernel

theorem represented : ∃ o m' base', P.run initial = .ok o ∧ run compiled.code machine = .ok m' 0 ∧
    m'.stack = [w[77]] ∧ Memory.Objects.StateRepr 1 1 8 compiled.frag o.st base' m' ∧
    Memory.BaseExtends initial.H bases base' ∧
    Memory.Objects.GrowsAllocator 1 8 (compiled.allocationCost initial)
      initial bases machine o.st base' m' ∧ Spec.sat o.st post := by
  exact construction_diamond (C := K) (b := 1) (L := 1) (frame := 8)
    (Γ := []) (Δ := OutputCtx) (F := Frag.init []) (P := P) compiled path
    (σ := initial) (base := bases) (m := machine) input (φ := post) diamond

theorem wrong_frame : ¬ compiled.Input 1 0 bases initial machine := by
  apply construction_small_frame compiled path
  exact Nat.lt_of_lt_of_le (by decide : 0 < 1) (Nat.le_add_right 1 _)

theorem false_post : ¬ Spec.sat initial (.diamond P (.not .tt)) := by
  intro h
  obtain ⟨_,_,_,_,_,_,_,_,_,bad⟩ := construction_diamond (C := K) (b := 1) (L := 1) (frame := 8)
    (Γ := []) (Δ := OutputCtx) (F := Frag.init []) (P := P) compiled path
    (σ := initial) (base := bases) (m := machine) input (φ := .not .tt) h
  exact bad trivial

theorem ordered_transport : ∃ o m' base', P.run initial = .ok o ∧ run compiled.code machine = .ok m' 0 ∧
    m'.stack = [w[77]] ∧ Memory.Objects.StateRepr 1 1 8 compiled.frag o.st base' m' ∧
    Memory.BaseExtends initial.H bases base' ∧
    Memory.Objects.GrowsAllocator 1 8 (compiled.allocationCost initial)
      initial bases machine o.st base' m' ∧ Spec.sat o.st post ∧
    orderedCells (.ok m' 0) = orderedCells (run compiled.code machine) := by
  obtain ⟨o,m',base',hs,ht,stack,repr,extension,grows,hp⟩ := represented
  exact ⟨o,m',base',hs,ht,stack,repr,extension,grows,hp,congrArg orderedCells ht.symm⟩

/-- info: some [18, 17, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 99, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] -/
#guard_msgs in #eval orderedCells (run compiled.code machine)
/-- info: false -/
#guard_msgs in #eval orderedCells (run compiled.code machine) == some [17, 17, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 99, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
end fixedZero

namespace fixedRebind
abbrev K := publishedRebind% C
abbrev OutputCtx : Ctx := publishedRebind% Δ
def P : Prog K [] OutputCtx := publishedRebind% program
attribute [irreducible] P
def compiled : Compiler.Compilation 1 (Frag.init []) P := by
  simpa only [P] using (publishedRebind% compiled)
attribute [irreducible] compiled
abbrev initial := publishedRebind% state
abbrev machine := publishedRebind% machine
abbrev bases := publishedRebind% base

theorem path : compiled.isConstruction = true := by decide +kernel

theorem input : compiled.Input 1 8 bases initial machine := by
  simpa only [compiled,P] using Solidity.Evm.Memory.ReferenceArrayRebindExamples.compiled_input

theorem observed : headObserve (P.run initial) = some 17000 := by
  simpa only [P,headObserve] using Solidity.Evm.Memory.ReferenceArrayRebindExamples.source_result

def post : Spec K OutputCtx := .eq (.pvV .here) (.app0 (.lit ⟨17000,by decide⟩))

theorem diamond : Spec.sat initial (.diamond P post) :=
  head_diamond ⟨17000,by decide⟩ observed

theorem cost : compiled.allocationCost initial = 10 := by
  rw [construction_allocation_cost compiled path]
  decide +kernel

theorem represented : ∃ o m' base', P.run initial = .ok o ∧ run compiled.code machine = .ok m' 0 ∧
    m'.stack = [w[77]] ∧ Memory.Objects.StateRepr 1 1 8 compiled.frag o.st base' m' ∧
    Memory.BaseExtends initial.H bases base' ∧
    Memory.Objects.GrowsAllocator 1 8 (compiled.allocationCost initial)
      initial bases machine o.st base' m' ∧ Spec.sat o.st post := by
  exact construction_diamond (C := K) (b := 1) (L := 1) (frame := 8)
    (Γ := []) (Δ := OutputCtx) (F := Frag.init []) (P := P) compiled path
    (σ := initial) (base := bases) (m := machine) input (φ := post) diamond

theorem wrong_frame : ¬ compiled.Input 1 0 bases initial machine := by
  apply construction_small_frame compiled path
  exact Nat.lt_of_lt_of_le (by decide : 0 < 1) (Nat.le_add_right 1 _)

theorem false_post : ¬ Spec.sat initial (.diamond P (.not .tt)) := by
  intro h
  obtain ⟨_,_,_,_,_,_,_,_,_,bad⟩ := construction_diamond (C := K) (b := 1) (L := 1) (frame := 8)
    (Γ := []) (Δ := OutputCtx) (F := Frag.init []) (P := P) compiled path
    (σ := initial) (base := bases) (m := machine) input (φ := .not .tt) h
  exact bad trivial

theorem ordered_transport : ∃ o m' base', P.run initial = .ok o ∧ run compiled.code machine = .ok m' 0 ∧
    m'.stack = [w[77]] ∧ Memory.Objects.StateRepr 1 1 8 compiled.frag o.st base' m' ∧
    Memory.BaseExtends initial.H bases base' ∧
    Memory.Objects.GrowsAllocator 1 8 (compiled.allocationCost initial)
      initial bases machine o.st base' m' ∧ Spec.sat o.st post ∧
    orderedCells (.ok m' 0) = orderedCells (run compiled.code machine) := by
  obtain ⟨o,m',base',hs,ht,stack,repr,extension,grows,hp⟩ := represented
  exact ⟨o,m',base',hs,ht,stack,repr,extension,grows,hp,congrArg orderedCells ht.symm⟩

/-- info: some [26, 2, 21, 19, 17000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 99, 2, 20, 20, 17, 13, 2, 24, 25, 0, 0, 0, 0, 0, 0, 0, 0] -/
#guard_msgs in #eval orderedCells (run compiled.code machine)
/-- info: false -/
#guard_msgs in #eval orderedCells (run compiled.code machine) == some [25, 2, 21, 19, 17000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 99, 2, 20, 20, 17, 13, 2, 24, 25, 0, 0, 0, 0, 0, 0, 0, 0]

namespace bounds
abbrev program := publishedRebind% failing
abbrev failed := publishedRebind% failed

theorem path (k : Fin 2) : (failed k).isConstruction = true := by
  have h : ∀ k : Fin 2, (failed k).isConstruction = true := by decide +kernel
  exact h k

theorem input (k : Fin 2) : (failed k).Input 1 8 bases initial machine :=
  Memory.ReferenceArrayRebindExamples.failed_input k

theorem box (k : Fin 2) : Spec.sat initial (.box (program k) (.not .tt)) := by
  simp only [Spec.sat,Memory.ReferenceArrayRebindExamples.source_bounds k,
    ne_eq,reduceCtorEq,not_false_eq_true]

theorem exact_revert (k : Fin 2) : (program k).run initial = .error .revert ∧ run (failed k).code machine = .revert := by
  rcases construction_box (failed k) (path k) (input k) (box k) with ⟨_,_,_,_,_,_,_,_,_,bad⟩ | h
  · exact (bad trivial).elim
  · exact h

theorem all_two :
    ((program 0).run initial = .error .revert ∧ run (failed 0).code machine = .revert) ∧
    ((program 1).run initial = .error .revert ∧ run (failed 1).code machine = .revert) :=
  ⟨exact_revert 0,exact_revert 1⟩
end bounds
end fixedRebind

/-! An actual structural prefix/suffix of the published program. No replacement
syntax or execution relation: both pieces are existing intrinsic constructors. -/
namespace populated

def cut {C : Contract} {Γ Δ : Ctx} (n : Nat) (P : Prog C Γ Δ) :
    Sigma (fun Ξ : Ctx => Prog C Γ Ξ × Prog C Ξ Δ) :=
  match n with
  | 0 => ⟨Γ,.nil,P⟩
  | n+1 => match P with
    | .nil => ⟨Γ,.nil,.nil⟩
    | .cons stmt tail =>
      let ⟨Ξ,head,rest⟩ := cut n tail
      ⟨Ξ,.cons stmt head,rest⟩

abbrev join := @constructionAppend

def split := cut 3 (publishedConstruction% program)
abbrev Parent : RefTy := publishedConstruction% parent
abbrev CallerCtx : Ctx := [.mem Parent,.val .uint,.mem Parent]
def callerPrefix : Prog K [] CallerCtx := split.2.1
def suffix : Prog K CallerCtx OutputCtx := split.2.2
attribute [irreducible] callerPrefix suffix

theorem reconstruct_source : join callerPrefix suffix = P := by
  with_unfolding_all rfl

def prefixCompiled : Compiler.Compilation 1 (Frag.init []) callerPrefix :=
  (Compiler.compile 1 (Frag.init []) callerPrefix).get (by decide +kernel)
def suffixCompiled : Compiler.Compilation 1 (Frag.init CallerCtx) suffix :=
  (Compiler.compile 1 (Frag.init CallerCtx) suffix).get (by decide +kernel)
attribute [irreducible] prefixCompiled suffixCompiled

theorem prefix_path : prefixCompiled.isConstruction = true := by decide +kernel
theorem suffix_path : suffixCompiled.isConstruction = true := by decide +kernel
theorem prefix_fragment : prefixCompiled.frag = Frag.init CallerCtx := by decide +kernel

theorem canonical_accepted : Compiler.compile 1 (Frag.init []) P = some compiled := by
  with_unfolding_all
    exact (Option.some_get (x := Compiler.compile 1 (Frag.init []) P) (by decide +kernel)).symm

theorem prefix_accepted : Compiler.compile 1 (Frag.init []) callerPrefix = some prefixCompiled := by
  with_unfolding_all
    exact (Option.some_get (x := Compiler.compile 1 (Frag.init []) callerPrefix) (by decide +kernel)).symm

theorem suffix_accepted : Compiler.compile 1 (Frag.init CallerCtx) suffix = some suffixCompiled := by
  with_unfolding_all
    exact (Option.some_get (x := Compiler.compile 1 (Frag.init CallerCtx) suffix) (by decide +kernel)).symm

/-- All algorithm, path, source and fragment-link premises of the generic
canonical append theorem are DISCHARGED by these actual compiler outputs. -/
theorem code_composes : compiled.code = prefixCompiled.code ++ suffixCompiled.code :=
  (construction_public_append_code compiled path prefixCompiled prefix_path
    suffixCompiled suffix_path prefix_fragment reconstruct_source
    canonical_accepted prefix_accepted suffix_accepted).1

theorem fragment_composes : compiled.frag = suffixCompiled.frag :=
  (construction_public_append_code compiled path prefixCompiled prefix_path
    suffixCompiled suffix_path prefix_fragment reconstruct_source
    canonical_accepted prefix_accepted suffix_accepted).2

theorem prefix_cost : prefixCompiled.allocationCost initial = 6 := by decide +kernel

theorem prefix_input : prefixCompiled.Input 1 8 bases initial machine := by
  apply (prefixCompiled.construction_input prefix_path 1 8 bases initial machine).2
  exact ⟨Memory.ConstructionExamples.initial_repr,by decide +kernel,
    .inr ⟨by decide,wmod 16,Memory.ConstructionExamples.initial_allocator,by decide +kernel⟩⟩

theorem prefix_successful : (callerPrefix.run initial).toOption.isSome = true := by decide +kernel
def entry : Solidity.Out K [] CallerCtx := (callerPrefix.run initial).toOption.get prefix_successful
attribute [irreducible] entry

theorem prefix_source : callerPrefix.run initial = .ok entry := by
  simpa only [entry] using (get_source (r := callerPrefix.run initial) prefix_successful)

theorem entry_populated : entry.st.H.length = 4 := by decide +kernel

def oldRef : HRef entry.st.H Parent := ⟨3,by decide +kernel⟩
theorem entry_pointer : TEnv.get (.here : Idx CallerCtx (.mem Parent)) entry.st.env = some oldRef := by
  decide +kernel

theorem suffix_cost : suffixCompiled.allocationCost entry.st = 9 := by decide +kernel

theorem suffix_observed : headObserve (suffix.run entry.st) = some 11013 := by decide +kernel

theorem suffix_diamond : Spec.sat entry.st (.diamond suffix post) :=
  head_diamond ⟨11013,by decide⟩ suffix_observed

/-- The reached suffix Input is BUILT from actual callerPrefix execution, complete
object representation and allocator growth. No suffix Input/run is assumed. -/
theorem reached_input : ∃ m₁ base₁, run prefixCompiled.code machine = .ok m₁ 0 ∧
    m₁.stack = [w[77]] ∧ suffixCompiled.Input 1 8 base₁ entry.st m₁ ∧
    Memory.Objects.StateRepr 1 1 8 (Frag.init CallerCtx) entry.st base₁ m₁ ∧
    Memory.Objects.AllocatorRepr entry.st.heap base₁ 8 (wmod 22) m₁ := by
  have space : (wmod 16).val + prefixCompiled.allocationCost initial < W := by
    rw [prefix_cost]
    decide +kernel
  obtain ⟨m₁,base₁,ht,stack,repr,extension,allocator,cell⟩ :=
    construction_cursor (C := K) (b := 1) (L := 1) (frame := 8)
      (Γ := []) (Δ := CallerCtx) (F := Frag.init []) (P := callerPrefix) prefixCompiled prefix_path
      (σ := initial) (base := bases) (m := machine) prefix_input prefix_source (wmod 16)
      (by decide) Memory.ConstructionExamples.initial_allocator space
  have repr₁ : Memory.Objects.StateRepr 1 1 8 (Frag.init CallerCtx) entry.st base₁ m₁ := by
    simpa only [prefix_fragment] using repr
  have allocator₁ : Memory.Objects.AllocatorRepr entry.st.heap base₁ 8 (wmod 22) m₁ := by
    simpa only [prefix_cost] using allocator
  have nextInput : suffixCompiled.Input 1 8 base₁ entry.st m₁ := by
    apply (suffixCompiled.construction_input suffix_path 1 8 base₁ entry.st m₁).2
    refine ⟨repr₁,by decide +kernel,.inr ⟨by decide,wmod 22,allocator₁,?_⟩⟩
    have eq : Memory.Construction.allocationCostProg suffix entry.st = 9 :=
      (construction_allocation_cost suffixCompiled suffix_path entry.st).symm.trans suffix_cost
    rw [eq]
    decide +kernel
  exact ⟨m₁,base₁,ht,stack,nextInput,repr₁,allocator₁⟩

/-- A concrete composition adapter from TWO actual public compiler outputs. -/
def composedCertificate : Memory.Construction.CompiledProg 1 (Frag.init []) P where
  frag := suffixCompiled.frag
  code := prefixCompiled.code ++ suffixCompiled.code
  cert := by
    have combined := (constructionCompose prefixCompiled prefix_path suffixCompiled suffix_path prefix_fragment).cert
    change Memory.Construction.ProgFrag 1 (Frag.init []) suffixCompiled.frag
      (constructionAppend callerPrefix suffix) (prefixCompiled.code ++ suffixCompiled.code) at combined
    have sourceJoin : constructionAppend callerPrefix suffix = P := reconstruct_source
    rw [sourceJoin] at combined
    exact combined

def composed : Compiler.Compilation 1 (Frag.init []) P := .construction composedCertificate
attribute [irreducible] composedCertificate composed

theorem composed_path : composed.isConstruction = true := by decide +kernel

theorem composed_code : composed.code = prefixCompiled.code ++ suffixCompiled.code := by
  unfold composed composedCertificate
  rfl

theorem composed_input : composed.Input 1 8 bases initial machine := by
  apply (composed.construction_input composed_path 1 8 bases initial machine).2
  exact (compiled.construction_input path 1 8 bases initial machine).1 input

/-- The actual adapter's entire original source program has a represented
successful output and the real11013post. Canonical code equality is linked
separately below by actual compiler-function algebra. -/
theorem composed_specification : ∃ o m' base', P.run initial = .ok o ∧ run composed.code machine = .ok m' 0 ∧
    m'.stack = [w[77]] ∧ Memory.Objects.StateRepr 1 1 8 composed.frag o.st base' m' ∧
    Memory.BaseExtends initial.H bases base' ∧
    Memory.Objects.GrowsAllocator 1 8 (composed.allocationCost initial)
      initial bases machine o.st base' m' ∧ Spec.sat o.st post := by
  exact construction_diamond (C := K) (b := 1) (L := 1) (frame := 8)
    (Γ := []) (Δ := OutputCtx) (F := Frag.init []) (P := P) composed composed_path
    (σ := initial) (base := bases) (m := machine) composed_input (φ := post) diamond

/-- An actual old reference is retained at the same address through the NEW
suffix diamond; staged code execution is linked by the published append law.
Canonical public code equality is proved separately by code_composes below. -/
theorem staged_old_reference_transport : ∃ m₁ base₁ o m₂ base₂,
    run prefixCompiled.code machine = .ok m₁ 0 ∧ m₁.stack = [w[77]] ∧
    suffixCompiled.Input 1 8 base₁ entry.st m₁ ∧
    suffix.run entry.st = .ok o ∧ run suffixCompiled.code m₁ = .ok m₂ 0 ∧
    run composed.code machine = .ok m₂ 0 ∧ m₂.stack = [w[77]] ∧
    Memory.Objects.StateRepr 1 1 8 suffixCompiled.frag o.st base₂ m₂ ∧
    Memory.BaseExtends entry.st.H base₁ base₂ ∧
    Memory.Objects.GrowsAllocator 1 8 (suffixCompiled.allocationCost entry.st)
      entry.st base₁ m₁ o.st base₂ m₂ ∧ Spec.sat o.st post ∧
    base₂ oldRef.id = base₁ oldRef.id ∧
    ¬ Memory.BaseExtends entry.st.H base₁ (fun _ => wmod 0) := by
  obtain ⟨m₁,base₁,ht,stack,nextInput,entryRepr,allocator⟩ := reached_input
  obtain ⟨o,m₂,base₂,hs,ht₂,stack₂,repr,extension,grows,hp⟩ :=
    construction_diamond (C := K) (b := 1) (L := 1) (frame := 8)
      (Γ := CallerCtx) (Δ := OutputCtx) (F := Frag.init CallerCtx) (P := suffix)
      suffixCompiled suffix_path (σ := entry.st) (base := base₁) (m := m₁)
      nextInput (φ := post) suffix_diamond
  have whole : run composed.code machine = .ok m₂ 0 := by
    rw [composed_code,Evm.run_append_ok ht]
    exact ht₂
  have wrong : ¬ Memory.BaseExtends entry.st.H base₁ (fun _ => wmod 0) := by
    intro h
    have eq := congrArg Fin.val (h oldRef)
    have bound := entryRepr.heap.owner.above oldRef
    change 0 = (base₁ oldRef.id).val at eq
    omega
  exact ⟨m₁,base₁,o,m₂,base₂,ht,stack,nextInput,hs,ht₂,whole,stack₂.trans stack,
    repr,extension,grows,hp,extension oldRef,wrong⟩
/-- The previously budget-blocked canonical whole-program application now
follows from actual compiler-function algebra, not an added equality premise. -/
theorem canonical_old_reference_transport : ∃ m₁ base₁ o m₂ base₂,
    run prefixCompiled.code machine = .ok m₁ 0 ∧ m₁.stack = [w[77]] ∧
    suffixCompiled.Input 1 8 base₁ entry.st m₁ ∧
    suffix.run entry.st = .ok o ∧ run suffixCompiled.code m₁ = .ok m₂ 0 ∧
    run compiled.code machine = .ok m₂ 0 ∧ m₂.stack = [w[77]] ∧
    Memory.Objects.StateRepr 1 1 8 compiled.frag o.st base₂ m₂ ∧
    Memory.BaseExtends entry.st.H base₁ base₂ ∧
    Memory.Objects.GrowsAllocator 1 8 (suffixCompiled.allocationCost entry.st)
      entry.st base₁ m₁ o.st base₂ m₂ ∧ Spec.sat o.st post ∧
    base₂ oldRef.id = base₁ oldRef.id ∧
    ¬ Memory.BaseExtends entry.st.H base₁ (fun _ => wmod 0) := by
  obtain ⟨m₁,base₁,o,m₂,base₂,ht,stack,nextInput,hs,ht₂,whole,stack₂,repr,extension,grows,hp,old,wrong⟩ :=
    staged_old_reference_transport
  have canonical : run compiled.code machine = .ok m₂ 0 := by
    rw [composed_code,← code_composes] at whole
    exact whole
  have repr' : Memory.Objects.StateRepr 1 1 8 compiled.frag o.st base₂ m₂ := by
    rw [fragment_composes]
    exact repr
  exact ⟨m₁,base₁,o,m₂,base₂,ht,stack,nextInput,hs,ht₂,canonical,stack₂,repr',extension,grows,hp,old,wrong⟩

end populated

end Solidity.Roadmap.V16.ConstructionControls

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut inductives : Array Json := #[]
  for (n, info) in env.constants.toList do
    if (`Solidity).isPrefixOf n then
      if let .inductInfo info := info then
        inductives := inductives.push (Json.mkObj [
          ("name", toJson n.toString), ("constructors", toJson (info.ctors.map Name.toString))])
  let mut theorems : Array Json := #[]
  for (n, info) in env.constants.toList do
    if (`Solidity.Roadmap.V16).isPrefixOf ((privateToUserName? n).getD n) ||
        (`_private.Solidity.Roadmap.V16).isPrefixOf n ||
        (`_private.Solidity.Examples.Roadmap.V16).isPrefixOf n then
      if let .thmInfo _ := info then
        let axs ← collectAxioms n
        let ty ← liftTermElabM do return (← Meta.ppExpr info.type).pretty
        let premises ← liftTermElabM do
          Meta.forallBoundedTelescope info.type (some info.type.getNumHeadForalls) fun xs _ => do
            let mut rows : Array Json := #[]
            let mut rawType := info.type
            for x in xs do
              let decl ← x.fvarId!.getDecl
              let ty ← Meta.ppExpr decl.type
              let rawDomain := rawType.consumeMData.bindingDomain!
              rawType := rawType.consumeMData.bindingBody!
              rows := rows.push (Json.mkObj [
                ("name", toJson decl.userName.toString), ("type", toJson ty.pretty),
                ("isProp", toJson (← Meta.isProp decl.type)),
                ("closedExpr", toJson (reprStr rawDomain)),
                ("constants", toJson (decl.type.getUsedConstants.toList.map Name.toString))])
            return rows
        theorems := theorems.push (Json.mkObj [
          ("name", toJson n.toString), ("ownerName", toJson ((privateToUserName? n).getD n).toString),
          ("type", toJson ty), ("premises", .arr premises),
          ("typeConstants", toJson (info.type.getUsedConstants.toList.map Name.toString)),
          ("dependencies", toJson (info.getUsedConstantsAsSet.toList.map Name.toString)),
          ("axioms", toJson (axs.toList.map Name.toString))])
  let mut definitions : Array Json := #[]
  for (n, info) in env.constants.toList do
    if (`Solidity.Roadmap.V16).isPrefixOf ((privateToUserName? n).getD n) ||
        (`_private.Solidity.Roadmap.V16).isPrefixOf n ||
        (`_private.Solidity.Examples.Roadmap.V16).isPrefixOf n then
      if let .defnInfo _ := info then
        let axs ← collectAxioms n
        let ty ← liftTermElabM do return (← Meta.ppExpr info.type).pretty
        definitions := definitions.push (Json.mkObj [
          ("name", toJson n.toString), ("ownerName", toJson ((privateToUserName? n).getD n).toString),
          ("type", toJson ty),
          ("typeConstants", toJson (info.type.getUsedConstants.toList.map Name.toString)),
          ("dependencies", toJson (info.getUsedConstantsAsSet.toList.map Name.toString)),
          ("axioms", toJson (axs.toList.map Name.toString))])
  logInfo m!"V16-INVENTORY {(Json.mkObj [("definitions", .arr definitions), ("modules", toJson (env.header.moduleNames.toList.map Name.toString)), ("inductives", .arr inductives), ("theorems", .arr theorems)]).compress}"
