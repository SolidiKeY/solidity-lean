import Solidity.Lowering.StorageOps.SourceArrayDeleteTarget
import Solidity.Source.Hoare

/-! Actual Source read outcomes over generated disjoint operation logs.
This upper test preserves the existing failure/state/journal distinctions. -/
namespace Solidity.Backend.StorageOps.SourceReadFrames
open SourceScalarDeleteLog SourceArrayDeleteTarget

/-- Elimination form of actual readCell, including missing-value failure. -/
theorem readCell_run {E : Source.Env} {Γ : Source.RCtx}
    (frame : Source.Fr) (path : Source.SPath)
    (locals : Source.Locals E.layout Γ) (state : Source.St E) :
    (Source.readCell (E := E) (Γ := Γ) frame path).run (locals,state) =
      match (if E.transientRoot path then (state.ex.transient.cells frame.this).read path
        else (state.ex.world.accounts frame.this).storage.read path) with
      | some v => (.ok v,(locals,state))
      | none => (.error (.stuck "storage cell without a value"),(locals,state)) := by
  unfold Source.readCell
  rw [Source.Hoare.run_bind]
  change ((match (if E.transientRoot path then (state.ex.transient.cells frame.this).read path
      else (state.ex.world.accounts frame.this).storage.read path) with
    | some v => (pure v : Source.EM E Γ _)
    | none => Source.EM.halt (.stuck "storage cell without a value")).run (locals,state)) = _
  cases value : (if E.transientRoot path then (state.ex.transient.cells frame.this).read path
    else (state.ex.world.accounts frame.this).storage.read path) <;> rfl

/-- Read result and exact read-only state are retained under both storage roots.
The input equalities are ordinary raw observations, not a preservation result. -/
theorem readCell_transport {E : Source.Env} {Γ : Source.RCtx}
    (frame : Source.Fr) (path : Source.SPath)
    (locals : Source.Locals E.layout Γ) (before after : Source.St E)
    (persistent : (after.ex.world.accounts frame.this).storage.read path =
      (before.ex.world.accounts frame.this).storage.read path)
    (transient : (after.ex.transient.cells frame.this).read path =
      (before.ex.transient.cells frame.this).read path) :
    (Source.readCell (E := E) (Γ := Γ) frame path).run (locals,after) =
      (((Source.readCell (E := E) (Γ := Γ) frame path).run (locals,before)).1,(locals,after)) := by
  rw [readCell_run,readCell_run,persistent,transient]
  cases value : (if E.transientRoot path then (before.ex.transient.cells frame.this).read path
    else (before.ex.world.accounts frame.this).storage.read path) <;> rfl

/-- Typed cell reads retain type-failure as well as missing-value failure. -/
theorem readAt_transport {E : Source.Env} {Γ : Source.RCtx}
    (frame : Source.Fr) (path : Source.SPath) (τ : Source.STy)
    (locals : Source.Locals E.layout Γ) (before after : Source.St E)
    (persistent : (after.ex.world.accounts frame.this).storage.read path =
      (before.ex.world.accounts frame.this).storage.read path)
    (transient : (after.ex.transient.cells frame.this).read path =
      (before.ex.transient.cells frame.this).read path) :
    (Source.readAt (E := E) (Γ := Γ) frame path τ).run (locals,after) =
      (((Source.readAt (E := E) (Γ := Γ) frame path τ).run (locals,before)).1,(locals,after)) := by
  simp only [Source.readAt,Source.Hoare.run_bind,readCell_run,persistent,transient]
  cases value : (if E.transientRoot path then (before.ex.transient.cells frame.this).read path
    else (before.ex.world.accounts frame.this).storage.read path) with
  | none => rfl
  | some v =>
    by_cases typed : E.cellTy path = τ
    · simp only [dif_pos typed]
      rfl
    · simp only [dif_neg typed]
      rfl

/-- Generalized-index elimination is proof-side only; no indexed executable
matcher or alternate value type is introduced. -/
private theorem int_exists {D : Source.Layout} {τ : Source.STy}
    (v : Source.Val D τ) (typed : τ = .int Source.IntTy.u256) :
    ∃ (n : Int) (bound : Source.IntTy.u256.lo ≤ n ∧ n ≤ Source.IntTy.u256.hi),
      typed ▸ v = .int n bound := by
  cases v <;> cases typed
  · exact ⟨_,_,rfl⟩
  all_goals rename_i impossible
  all_goals simp only [Source.STy.loc?,reduceCtorEq] at impossible

/-- Actual readLen result/failure is transported without changing the read's
input state. Journal contents in the two inputs need not be equal. -/
theorem readLen_transport {E : Source.Env} {Γ : Source.RCtx}
    (frame : Source.Fr) (path : Source.SPath)
    (locals : Source.Locals E.layout Γ) (before after : Source.St E)
    (persistent : (after.ex.world.accounts frame.this).storage.read path =
      (before.ex.world.accounts frame.this).storage.read path)
    (transient : (after.ex.transient.cells frame.this).read path =
      (before.ex.transient.cells frame.this).read path) :
    (Source.readLen (E := E) (Γ := Γ) frame path).run (locals,after) =
      (((Source.readLen (E := E) (Γ := Γ) frame path).run (locals,before)).1,(locals,after)) := by
  have afterRead := readAt_transport frame path (.int Source.IntTy.u256) locals before after persistent transient
  have beforeRead := readAt_transport frame path (.int Source.IntTy.u256) locals before before rfl rfl
  simp only [Source.readLen,Source.Hoare.run_bind]
  rw [afterRead,beforeRead]
  cases result : ((Source.readAt (E := E) (Γ := Γ) frame path (.int Source.IntTy.u256)).run (locals,before)).1 with
  | error error => rfl
  | ok v =>
    obtain ⟨n,bound,same⟩ := int_exists v rfl
    cases same
    rfl

/-- Existing disjoint operation facts discharge both read-observation inputs. -/
theorem readLen_clearOp_other {E : Source.Env} {Γ : Source.RCtx}
    (frame : Source.Fr) (path query : Source.SPath)
    (locals : Source.Locals E.layout Γ) (state : Source.St E) (apart : query ≠ path) :
    (Source.readLen (E := E) (Γ := Γ) frame query).run
      (locals,{state with ex := state.ex.apply (clearOp E frame path)}) =
      (((Source.readLen (E := E) (Γ := Γ) frame query).run (locals,state)).1,
        (locals,{state with ex := state.ex.apply (clearOp E frame path)})) := by
  have frames := clearOp_other frame state.ex path query apart
  exact readLen_transport frame query locals state _ frames.1 frames.2

/-- Finite generated touched-set transport covers arbitrary index lists,
including duplicates, order and empty lists, with actual failure outcomes. -/
theorem readLen_log_other {E : Source.Env} {Γ : Source.RCtx}
    (frame : Source.Fr) (path query : Source.SPath) (indices : List Nat)
    (locals : Source.Locals E.layout Γ) (state : Source.St E)
    (apart : ∀ i ∈ indices, query ≠ path.go (.index i)) :
    (Source.readLen (E := E) (Γ := Γ) frame query).run
      (locals,{state with ex := state.ex.run (indices.map (fun i => clearOp E frame (path.go (.index i))))}) =
      (((Source.readLen (E := E) (Γ := Γ) frame query).run (locals,state)).1,
        (locals,{state with ex := state.ex.run (indices.map (fun i => clearOp E frame (path.go (.index i))))})) := by
  have frames := clear_log_other frame state.ex path query indices apart
  exact readLen_transport frame query locals state _ frames.1 frames.2

/-- Actual Source runtime prefix on success OR timeout, with its generated
min(count,budget) accesses. Reading the retained prefix state is not rollback. -/
theorem range_readLen_other {E : Source.Env} {Γ : Source.RCtx}
    (frame : Source.Fr) (writable : frame.static = false) (intTy : Source.IntTy)
    (path query : Source.SPath) (start count budget : Nat)
    (locals : Source.Locals E.layout Γ) (state : Source.St E)
    (apart : ∀ i ∈ List.range' start (min count budget), query ≠ path.go (.index i)) :
    let result := (Source.deleteRange (E := E) (Γ := Γ) frame (budget + 1)
      (.int intTy) path start count).run (locals,state)
    (Source.readLen frame query).run result.2 =
      (((Source.readLen (E := E) (Γ := Γ) frame query).run (locals,state)).1,result.2) := by
  dsimp only
  rw [scalar_range_prefix frame writable intTy path start count budget locals state]
  exact readLen_log_other frame path query _ locals state apart

/-- Actual successful operation-family sequence. Only the ORIGINAL other header
read is supplied; its intermediate read is derived from generated disjoint writes.
The exact existing Op log/journal order is retained, never commuted. -/
theorem range_then_array {E : Source.Env} {Γ : Source.RCtx}
    (frame : Source.Fr) (writable : frame.static = false)
    (elementTy arrayTy : Source.IntTy) (path other : Source.SPath)
    (start count length : Nat) (locals : Source.Locals E.layout Γ) (state : Source.St E)
    (input : (Source.readLen (E := E) (Γ := Γ) frame other).run (locals,state) =
      (.ok length,(locals,state)))
    (apart : ∀ i ∈ List.range' start count, other ≠ path.go (.index i)) :
    ((do
      Source.deleteRange frame (count + 1) (.int elementTy) path start count
      Source.deleteStor frame (length + 2) (.array .storage (.int arrayTy) none) other) :
      Source.EM E Γ Unit).run (locals,state) =
      (.ok (), (locals,{state with ex := state.ex.run (((List.range' start count).map (fun i => clearOp E frame (path.go (.index i)))) ++
          ((List.range' 0 length).map (fun i => clearOp E frame (other.go (.index i)))) ++
          [clearOp E frame other])})) := by
  rw [Source.Hoare.run_bind,scalar_range_run frame writable elementTy path start count 0 locals state]
  simp only []
  have readback := readLen_log_other frame path other (List.range' start count) locals state apart
  rw [input] at readback
  rw [source_array_run frame writable arrayTy other length _ _ readback]
  simp only [Source.run_append]

namespace Controls
private def uintSyntax : Source.Syn .typeName := .elem (.int false 256 (by decide))
private def unit : Source.Syn .unit := .unit (.cons (.contract false "C" .none .nil
  (.cons (.stateVar (.array uintSyntax .none) none none none false "left" .none)
    (.cons (.stateVar (.array uintSyntax .none) none none none false "right" .none)
      (.cons (.stateVar (.elem .bool) none none none false "bad" .none)
        (.cons (.stateVar uintSyntax none none none true "scratch" .none)
          (.cons (.stateVar uintSyntax none none none false "sentinel" .none) .nil)))))) .nil)
private def env : Source.Env := unit.env
private def left : Source.SPath := ⟨⟨some "C","left"⟩,[]⟩
private def right : Source.SPath := ⟨⟨some "C","right"⟩,[]⟩
private def bad : Source.SPath := ⟨⟨some "C","bad"⟩,[]⟩
private def scratch : Source.SPath := ⟨⟨some "C","scratch"⟩,[]⟩
private def sentinel : Source.SPath := ⟨⟨some "C","sentinel"⟩,[]⟩
private def missing : Source.SPath := ⟨⟨some "C","missing"⟩,[]⟩
private def elem (p : Source.SPath) (i : Nat) : Source.SPath := p.go (.index i)
private def address : Roadmap.Address := ⟨7,by decide⟩
private def storage : Source.Storage env.layout env.cellTy :=
  let s := (Source.Storage.empty : Source.Storage env.layout env.cellTy).write left (.int 2 (by decide))
  let s := s.write (elem left 0) (.int 53 (by decide))
  let s := s.write (elem left 1) (.int 59 (by decide))
  let s := s.write (elem left 2) (.int 61 (by decide))
  let s := s.write right (.int 3 (by decide))
  let s := s.write (elem right 0) (.int 7 (by decide))
  let s := s.write (elem right 1) (.int 17 (by decide))
  let s := s.write (elem right 2) (.int 23 (by decide))
  let s := s.write (elem right 3) (.int 71 (by decide))
  let s := s.write bad (.bool true)
  s.write sentinel (.int 99 (by decide))
private def state : Source.St env :=
  { ex :=
      { world := ⟨fun a => if a = address then
          { balance := 19, nonce := 3, code := some 0, storage := storage }
          else Source.Account.empty _⟩
        transient := Source.Transient.empty.set address
          ((Source.Storage.empty : Source.Storage env.layout env.cellTy).write scratch (.int 5 (by decide)))
        journal := [] }
    heap := Source.Heap.empty
    events := []
    logs := []
    fnLocals := ⟨[],.nil⟩ }
private def frame : Source.Fr :=
  {this := address,sender := ⟨13,by decide⟩,value := ⟨0,by decide⟩,static := false,contract := "C"}
private def initial : Source.Locals env.layout [] × Source.St env := (.nil,state)
private def rangeOp : Source.EM env [] Unit := Source.deleteRange frame 3 (.int Source.IntTy.u256) left 0 2
private def arrayOp : Source.EM env [] Unit := Source.deleteStor frame 5
  (.array .storage (.int Source.IntTy.u256) none) right
private def forward := (rangeOp >>= fun _ => arrayOp).run initial
private def reverse := (arrayOp >>= fun _ => rangeOp).run initial
private def prefixResult := (Source.deleteRange (E := env) (Γ := []) frame 2 (.int Source.IntTy.u256) left 0 2).run initial
private def paths := [left,elem left 0,elem left 1,elem left 2,right,elem right 0,elem right 1,elem right 2,elem right 3,bad,sentinel,missing]
private def view (ex : Source.ExecState env.layout env.lay env.lay) :=
  paths.map (wordAt frame ex) ++
    [(((ex.transient.cells frame.this).read scratch).bind Source.Val.word).map Fin.val]
private def readViews (input : Source.Locals env.layout [] × Source.St env) :=
  [right,scratch,bad,missing].map (fun query => ((Source.readLen (E := env) (Γ := []) frame query).run input).1)

theorem sequence_witness : forward =
    (.ok (),(.nil,{state with ex := state.ex.run ([clearOp env frame (elem left 0),clearOp env frame (elem left 1)] ++
       [clearOp env frame (elem right 0),clearOp env frame (elem right 1),clearOp env frame (elem right 2)] ++
       [clearOp env frame right])})) := by
  exact range_then_array frame rfl Source.IntTy.u256 Source.IntTy.u256 left right 0 2 3 .nil state rfl
    (by intro i member; intro same; have roots := congrArg Source.SPath.root same
        exact (by decide : right.root ≠ left.root) roots)

/-- Complete ordered vectors preserve every recorded retained/outside cell. -/
theorem ordered_observations :
    (forward.1,reverse.1,view state.ex,view forward.2.2.ex,view reverse.2.2.ex,
      forward.2.2.ex.journal.length,reverse.2.2.ex.journal.length) =
    (.ok (),.ok (),
      [some 2,some 53,some 59,some 61,some 3,some 7,some 17,some 23,some 71,some 1,some 99,none,some 5],
      [some 2,some 0,some 0,some 61,some 0,some 0,some 0,some 0,some 71,some 1,some 99,none,some 5],
      [some 2,some 0,some 0,some 61,some 0,some 0,some 0,some 0,some 71,some 1,some 99,none,some 5],6,6) := by rfl

theorem failure_reads :
    (prefixResult.1,view prefixResult.2.2.ex,prefixResult.2.2.ex.journal.length,
      readViews initial,readViews prefixResult.2) =
    (.error .timeout,
      [some 2,some 0,some 59,some 61,some 3,some 7,some 17,some 23,some 71,some 1,some 99,none,some 5],1,
      [.ok 3,.ok 5,.error (.stuck "storage cell type"),.error (.stuck "storage cell without a value")],
      [.ok 3,.ok 5,.error (.stuck "storage cell type"),.error (.stuck "storage cell without a value")]) := by rfl

theorem actual_prefix_readback (query : Source.SPath)
    (apart : ∀ i ∈ List.range' 0 (min 2 1), query ≠ left.go (.index i)) :
    (Source.readLen (E := env) (Γ := []) frame query).run prefixResult.2 =
      (((Source.readLen (E := env) (Γ := []) frame query).run initial).1,prefixResult.2) := by
  exact range_readLen_other frame rfl Source.IntTy.u256 left query 0 2 1 .nil state apart

/-- Same physical account snapshots remain ordered in the existing journal.
Undoing ONE operation distinguishes the equal-storage final states. -/
theorem order_negative :
    (view forward.2.2.ex.undo,view reverse.2.2.ex.undo) =
      ([some 2,some 0,some 0,some 61,some 3,some 0,some 0,some 0,some 71,some 1,some 99,none,some 5],
       [some 2,some 0,some 59,some 61,some 0,some 0,some 0,some 0,some 71,some 1,some 99,none,some 5]) ∧
    forward.2.2 ≠ reverse.2.2 := by
  refine ⟨rfl,?_⟩
  intro same
  have observation := congrArg (fun s : Source.St env => wordAt frame s.ex.undo (elem left 1)) same
  change some (0 : Nat) = some 59 at observation
  cases observation

/-- Dropping the actual touched-path exclusion is false. -/
theorem overlap_negative :
    (((Source.readLen (E := env) (Γ := []) frame (elem left 0)).run initial).1,
      ((Source.readLen (E := env) (Γ := []) frame (elem left 0)).run prefixResult.2).1) = (.ok 53,.ok 0) := by rfl
end Controls

/-- info: 'Solidity.Backend.StorageOps.SourceReadFrames.readCell_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms readCell_run

/-- info: 'Solidity.Backend.StorageOps.SourceReadFrames.readCell_transport' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms readCell_transport

/-- info: 'Solidity.Backend.StorageOps.SourceReadFrames.readAt_transport' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms readAt_transport

/-- info: 'Solidity.Backend.StorageOps.SourceReadFrames.readLen_transport' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms readLen_transport

/-- info: 'Solidity.Backend.StorageOps.SourceReadFrames.readLen_clearOp_other' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms readLen_clearOp_other

/-- info: 'Solidity.Backend.StorageOps.SourceReadFrames.readLen_log_other' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms readLen_log_other

/-- info: 'Solidity.Backend.StorageOps.SourceReadFrames.range_readLen_other' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms range_readLen_other

/-- info: 'Solidity.Backend.StorageOps.SourceReadFrames.range_then_array' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms range_then_array

/-- info: 'Solidity.Backend.StorageOps.SourceReadFrames.Controls.sequence_witness' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Controls.sequence_witness

/-- info: 'Solidity.Backend.StorageOps.SourceReadFrames.Controls.ordered_observations' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Controls.ordered_observations

/-- info: 'Solidity.Backend.StorageOps.SourceReadFrames.Controls.failure_reads' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Controls.failure_reads

/-- info: 'Solidity.Backend.StorageOps.SourceReadFrames.Controls.actual_prefix_readback' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Controls.actual_prefix_readback

/-- info: 'Solidity.Backend.StorageOps.SourceReadFrames.Controls.order_negative' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Controls.order_negative

/-- info: 'Solidity.Backend.StorageOps.SourceReadFrames.Controls.overlap_negative' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Controls.overlap_negative

end Solidity.Backend.StorageOps.SourceReadFrames
