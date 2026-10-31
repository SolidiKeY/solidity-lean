import SolidityBridge.ExternalEvm.StorageSlots
import Solidity.Evm.Compile
import Solidity.Syntax.Splice
import Solidity.Calculus.Logic

/-! Actual scoped Solidity source and its compiled storage macro observations.
No physical-layout or source-assembly feature is admitted by these fixtures. -/
namespace Solidity.Evm.StorageSlots.Examples

private def C : Contract := contract!{ uint total; }
private def putSeven : Prog C [] [] := sol[C]{ total = 7; }
private def putClear : Prog C [] [] := sol[C]{ total = 7; total = 0; }

private def total (s : State C []) : Int :=
  match s.storage.get (T := .prim .uint) (f := "total") (by rfl) with
  | .prim n => n.val

theorem source_seven :
    ((Prog.runFrames (State.init C) putSeven .nil).toOption.map total) = some 7 := by
  rfl

theorem source_clear :
    ((Prog.runFrames (State.init C) putClear .nil).toOption.map total) = some 0 := by
  rfl

theorem compiled_seven : compileProg 0 putSeven =
    [.push (.val (wmod 7)), .push (.slot (.root 0)), .sstore] := rfl

theorem lowered_source_seven : lowerProgram (compileProg 0 putSeven) =
    .ok [(.Push .PUSH32, some (.ofNat 7, 32)),
      (.Push .PUSH32, some (.ofNat 0, 32)), (.SSTORE, none)] := rfl

/-- Actual upstream execution of exactly the source compiler's lowered code. -/
theorem upstream_seven :
    ∃ out, runMacro [(.Push .PUSH32, some (.ofNat 7, 32)),
      (.Push .PUSH32, some (.ofNat 0, 32)), (.SSTORE, none)] freshAccount = .ok out ∧
      storageRead out.toState (.ofNat 0) = wmod 7  := by
  obtain ⟨ops, m, out, hl, hc, ht, hr⟩ := bounded_refinement [.root 0]
    [.push (.val (wmod 7)), .push (.slot (.root 0)), .sstore]
    Machine.init freshAccount (fresh_agrees _) (ready_write _ _ _ _)
  have hlower : lowerProgram [.push (.val (wmod 7)), .push (.slot (.root 0)), .sstore] =
      .ok [(.Push .PUSH32, some (.ofNat 7, 32)),
        (.Push .PUSH32, some (.ofNat 0, 32)), (.SSTORE, none)] := rfl
  rw [hlower] at hl
  cases hl
  refine ⟨out, ht, ?_⟩
  have hv : m.store.cells (.root 0) = wmod 7 := by cases hc; rfl
  exact (hr.storage (.root 0) (by simp only [List.mem_singleton])).symm.trans hv


theorem lowered_source_clear : lowerProgram (compileProg 0 putClear) =
    .ok [(.Push .PUSH32, some (.ofNat 7, 32)),
      (.Push .PUSH32, some (.ofNat 0, 32)), (.SSTORE, none),
      (.Push .PUSH32, some (.ofNat 0, 32)),
      (.Push .PUSH32, some (.ofNat 0, 32)), (.SSTORE, none)] := rfl

theorem upstream_clear :
    ∃ out, runMacro [(.Push .PUSH32, some (.ofNat 7, 32)),
      (.Push .PUSH32, some (.ofNat 0, 32)), (.SSTORE, none),
      (.Push .PUSH32, some (.ofNat 0, 32)),
      (.Push .PUSH32, some (.ofNat 0, 32)), (.SSTORE, none)] freshAccount = .ok out ∧
      storageRead out.toState (.ofNat 0) = wmod 0  := by
  let first : List Instr := [.push (.val (wmod 7)), .push (.slot (.root 0)), .sstore]
  let rest : List Instr := [.push (.val (wmod 0)), .push (.slot (.root 0)), .sstore]
  have ready : Ready [.root 0] (first ++ rest) Machine.init freshAccount :=
    Ready.append first rest _ _ (ready_write _ _ _ _) (fun _ _ => ready_write _ _ _ _)
  obtain ⟨ops, m, out, hl, hc, ht, hr⟩ := bounded_refinement [.root 0]
    (first ++ rest) Machine.init freshAccount (fresh_agrees _) ready
  have hlower : lowerProgram (first ++ rest) =
      .ok [(.Push .PUSH32, some (.ofNat 7, 32)),
        (.Push .PUSH32, some (.ofNat 0, 32)), (.SSTORE, none),
        (.Push .PUSH32, some (.ofNat 0, 32)),
        (.Push .PUSH32, some (.ofNat 0, 32)), (.SSTORE, none)] := rfl
  rw [hlower] at hl
  cases hl
  refine ⟨out, ht, ?_⟩
  have hv : m.store.cells (.root 0) = wmod 0 := by cases hc; rfl
  exact (hr.storage (.root 0) (by simp only [List.mem_singleton])).symm.trans hv



/-- A prepared mapping hash followed by an actual storage write, with a
nonempty observed domain. Arbitrary keys, parents and values are admitted. -/
theorem map_write (key : Fin W) (a : Slot) (v : Fin W) :
    ∃ out, runMacro (mapMacro ++ [(.SSTORE, none)])
      {freshAccount with stack := [encode key, address a, encode v]} = .ok out ∧
      storageRead out.toState (address (.hash key a 0)) = v := by
  let a' := Slot.hash key a 0
  let m := {Machine.init with stack := [.val key, .slot a, .val v]}
  let s := {freshAccount with stack := [encode key, address a, encode v]}
  have ha : Agrees [a'] m s :=
    ⟨rfl, (fresh_agrees [a']).storage, (fresh_agrees [a']).present⟩
  have ready : Ready [a'] [.keccakMap, .sstore] m s := by
    refine ⟨.mapping key a [.val v] rfl (map_setup_empty _ _ _ rfl), ?_⟩
    intro ops m1 s1 _ hc _
    cases hc
    exact ⟨.store a' v [] rfl (singleton_compatible _ _ _), fun _ _ _ _ _ _ => True.intro⟩
  obtain ⟨ops, m1, out, hl, hc, ht, hr⟩ :=
    bounded_refinement [a'] [.keccakMap, .sstore] m s ha ready
  have hlower : lowerProgram [.keccakMap, .sstore] = .ok (mapMacro ++ [(.SSTORE, none)]) := rfl
  rw [hlower] at hl
  cases hl
  refine ⟨out, ht, ?_⟩
  have hv : m1.store.cells a' = v := by
    cases hc
    change (Machine.init.store.write a' v.val).cells a' = v
    rw [WordStore.write_cells_same]
  exact (hr.storage a' (by simp only [List.mem_singleton])).symm.trans hv

theorem array_write (a : Slot) (v : Fin W) :
    ∃ out, runMacro (arrayMacro ++ [(.SSTORE, none)])
      {freshAccount with stack := [address a, encode v]} = .ok out ∧
      storageRead out.toState (address (.data a 0)) = v := by
  let a' := Slot.data a 0
  let m := {Machine.init with stack := [.slot a, .val v]}
  let s := {freshAccount with stack := [address a, encode v]}
  have ha : Agrees [a'] m s :=
    ⟨rfl, (fresh_agrees [a']).storage, (fresh_agrees [a']).present⟩
  have ready : Ready [a'] [.keccakArr, .sstore] m s := by
    refine ⟨.array a [.val v] rfl (array_setup_empty _ _ rfl), ?_⟩
    intro ops m1 s1 _ hc _
    cases hc
    exact ⟨.store a' v [] rfl (singleton_compatible _ _ _), fun _ _ _ _ _ _ => True.intro⟩
  obtain ⟨ops, m1, out, hl, hc, ht, hr⟩ :=
    bounded_refinement [a'] [.keccakArr, .sstore] m s ha ready
  have hlower : lowerProgram [.keccakArr, .sstore] = .ok (arrayMacro ++ [(.SSTORE, none)]) := rfl
  rw [hlower] at hl
  cases hl
  refine ⟨out, ht, ?_⟩
  have hv : m1.store.cells a' = v := by
    cases hc
    change (Machine.init.store.write a' v.val).cells a' = v
    rw [WordStore.write_cells_same]
  exact (hr.storage a' (by simp only [List.mem_singleton])).symm.trans hv


private def M : Contract := contract!{ mapping(uint => uint) balances; }
private def mapPut : Prog M [] [] := sol[M]{ balances[7] = 5; }

private def mapped (s : State M []) : Int :=
  match (s.storage.get (T := .ref (.mapping .uint (.prim .uint)))
      (f := "balances") (by rfl)).find (.key ⟨7, by decide⟩ .nil) with
  | some (.prim n) => n.val
  | none => -1

theorem source_mapping :
    ((Prog.runFrames (State.init M) mapPut .nil).toOption.map mapped) = some 5 := by with_unfolding_all rfl

theorem compiled_mapping : compileProg 0 mapPut =
    [.push (.val (wmod 5)), .push (.slot (.root 0)), .push (.val (wmod 7)),
      .keccakMap, .sstore] := rfl

/-- Existence and observation of the upstream run for exactly the mapping
source compiler's lowerProgram output, not a detached arithmetic hash law. -/
theorem upstream_mapping :
    ∃ ops out, lowerProgram (compileProg 0 mapPut) = .ok ops ∧
      runMacro ops freshAccount = .ok out ∧
      storageRead out.toState (address (.hash (wmod 7) (.root 0) 0)) = wmod 5 := by
  let a := Slot.hash (wmod 7) (.root 0) 0
  obtain ⟨ops, m, out, hl, hc, ht, hr⟩ := bounded_refinement [a]
    (compileProg 0 mapPut) Machine.init freshAccount (fresh_agrees _)
    (ready_map_write_empty _ _ (.root 0) (wmod 7) (wmod 5) rfl)
  refine ⟨ops, out, hl, ht, ?_⟩
  have hv : m.store.cells a = wmod 5 := by cases hc; rfl
  exact (hr.storage a (by simp only [List.mem_singleton])).symm.trans hv


private def copySeven : Prog C [] [] := sol[C]{ total = 7; total = total; }

theorem source_read_seven :
    ((Prog.runFrames (State.init C) copySeven .nil).toOption.map total) = some 7 := by rfl

theorem compiled_read_seven : compileProg 0 copySeven =
    [.push (.val (wmod 7)), .push (.slot (.root 0)), .sstore,
      .push (.slot (.root 0)), .sload, .push (.slot (.root 0)), .sstore] := rfl

theorem upstream_read_seven :
    ∃ ops out, lowerProgram (compileProg 0 copySeven) = .ok ops ∧
      runMacro ops freshAccount = .ok out ∧
      storageRead out.toState (.ofNat 0) = wmod 7 := by
  let first : List Instr := [.push (.val (wmod 7)), .push (.slot (.root 0)), .sstore]
  let rest : List Instr := [.push (.slot (.root 0)), .sload, .push (.slot (.root 0)), .sstore]
  have ready : Ready [.root 0] (first ++ rest) Machine.init freshAccount :=
    Ready.append first rest _ _ (ready_write _ _ _ _) (fun _ _ => ready_read_store _ _ _)
  obtain ⟨ops, m, out, hl, hc, ht, hr⟩ := bounded_refinement [.root 0]
    (compileProg 0 copySeven) Machine.init freshAccount (fresh_agrees _) ready
  refine ⟨ops, out, hl, ht, ?_⟩
  have firstRun : Evm.run first Machine.init =
      .ok {Machine.init with store := Machine.init.store.write (.root 0) 7} 0 := rfl
  have restRun (n : Machine) : Evm.run rest n =
      .ok {n with store := n.store.write (.root 0) (n.store.cells (.root 0)).val} 0 := rfl
  rw [compiled_read_seven] at hc
  change Evm.run (first ++ rest) Machine.init = _ at hc
  rw [Evm.run_append_ok firstRun, restRun] at hc
  cases hc
  have hv : (Machine.init.store.write (.root 0) 7 |>.write (.root 0)
      ((Machine.init.store.write (.root 0) 7).cells (.root 0)).val).cells (.root 0) = wmod 7 := by
    rw [WordStore.write_cells_same]
    rfl
  exact (hr.storage (.root 0) (by simp only [List.mem_singleton])).symm.trans hv

/-- An absent executing account is refused by the representation relation. -/
theorem absent_account_refused (domain : List Slot) (m : Machine) :
    ¬ Agrees domain m (default : EvmYul.EVM.State) := by
  intro h
  rcases h.present with ⟨acc, hp⟩
  change none = some acc at hp
  contradiction

/-- info: 'Solidity.Evm.StorageSlots.Examples.source_mapping' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms source_mapping
/-- info: 'Solidity.Evm.StorageSlots.Examples.upstream_mapping' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms upstream_mapping
/-- info: 'Solidity.Evm.StorageSlots.Examples.upstream_read_seven' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms upstream_read_seven
/-- info: 'Solidity.Evm.StorageSlots.Examples.map_write' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms map_write
/-- info: 'Solidity.Evm.StorageSlots.Examples.array_write' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms array_write

/-- The existing source array compiler needs bounds/control-flow and element
arithmetic; this partial lowering retains a named refusal for that code. -/
private def A : Contract := contract!{ uint[] xs; uint total; }
private def arrayRead : Prog A [] [] := sol[A]{ total = xs[0]; }

theorem array_source_refused : lowerProgram (compileProg 0 arrayRead) =
    .error "evm-storage-slots: unsupported instruction" := rfl

end Solidity.Evm.StorageSlots.Examples
