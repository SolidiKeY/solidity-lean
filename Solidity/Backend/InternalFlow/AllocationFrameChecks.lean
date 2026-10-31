import Solidity.Backend.InternalFlow.AllocationFrame
import Solidity.Backend.InternalFlow.Controls

/-! Two actual allocating memory-result calls frame nonempty caller contents.
The published withinM guard remains unchanged; an old-alias write is rejected. -/
namespace Solidity.Backend.InternalFlow.AllocationFrameChecks

open Controls (contract arrayType seven nine eleven persistent transient)

abbrev Input : Ctx := [.mem arrayType, .mem arrayType, .mem arrayType]
abbrev CallerCtx : Ctx := [.mem arrayType, .mem arrayType, .val .uint, .val .uint]
abbrev FirstCtx : Ctx := [.mem arrayType, .mem arrayType, .mem arrayType, .val .uint, .val .uint]
abbrev FinalCtx : Ctx := [.mem arrayType, .mem arrayType, .mem arrayType, .mem arrayType, .val .uint, .val .uint]
abbrev Params : Ctx := [.mem arrayType, .mem arrayType]

def thirteen : PrimTy.uint.Denote := ⟨13, rfl⟩
def seventeen : PrimTy.uint.Denote := ⟨17, rfl⟩
def zero : PrimTy.uint.Denote := ⟨0, rfl⟩
def one : PrimTy.uint.Denote := ⟨1, rfl⟩
def ninetyNine : PrimTy.uint.Denote := ⟨99, rfl⟩
def seedValue : SVal (.ref arrayType) :=
  .array (SVec.ofList [.prim seven, .prim eleven]) .nil (by decide +kernel)
def returnedValue : SVal (.ref arrayType) :=
  .array (SVec.ofList [.prim thirteen, .prim seventeen]) .nil (by decide +kernel)
def seed : Grew contract [] [] (MVal · (.ref arrayType)) :=
  (State.init contract).copyStToMG seedValue rfl

def store : Storage contract :=
  Controls.saved.set (f := "a") (T := .ref arrayType) (by rfl) returnedValue

def caller : State contract CallerCtx :=
  { seed.st.withEnv (Δ := CallerCtx) (some seed.val, some seed.val, nine, eleven, ()) with
    storage := store
    tx := { msgSender := nine, msgValue := seven, timestamp := eleven, selfAddress := nine }
    selfBalance := eleven }

def args1 : Args contract CallerCtx Params :=
  .snocMemory (.snocMemory .nil arrayType (.user "aliasA") (.var .here rfl))
    arrayType (.user "aliasB") (.var (.there .here) rfl)
def env1 : TEnv contract caller.H Params := (some seed.val, some seed.val, ())
def ret1 : CallRet CallerCtx [.mem arrayType] FirstCtx := .mem arrayType (.user "copyResult") rfl rfl
def entry1 : Out contract caller.H Input := ret1.enterT (caller.withEnv env1)

def condition : Val contract Input .bool :=
  .binop .gt rfl rfl (.read (.root "p" rfl)) (.simple (.lit 0 rfl))
def copyInit : MRhs contract Input arrayType := .copy (.loc (.root "a" rfl)) rfl
def newInit : MRhs contract Input arrayType := .newArr (.lit 3 rfl) rfl

def branch (init : MRhs contract Input arrayType) :
    Prog contract Input (.mem arrayType :: Input) :=
  .cons (.declMem arrayType (.user "temporary") (some init) rfl rfl)
    (.cons (.rebindMem (.there .here) (.alias (.var .here rfl))) .nil)

def body (init : MRhs contract Input arrayType) : Prog contract Input Input :=
  .cons (.block (.cons (.ite condition (branch init) .nil) .nil)) .nil

def growth1 : Grew contract Input entry1.st.H (MVal · (.ref arrayType)) :=
  entry1.st.copyStToMG returnedValue rfl

def bodyOut1 : Out contract entry1.st.H Input :=
  ⟨((growth1.st.push (t := .mem arrayType) (some growth1.val)).setLocal
    (.there .here) (some growth1.val)).drop (.push .refl), growth1.ext⟩
def first : Out contract caller.H FirstCtx :=
  ⟨bodyOut1.st.withEnv (ret1.leaveT (TEnv.wk (entry1.ext.trans bodyOut1.ext) CallerCtx caller.env)
    (TEnv.take [.mem arrayType] (TEnv.drop (body copyInit).ext bodyOut1.st.env))),
    entry1.ext.trans bodyOut1.ext⟩

theorem args1_evaluate : args1.evalT caller = .ok env1 := rfl
theorem copy_body_evaluates : (body copyInit).runR entry1.st = .ok bodyOut1 := rfl
theorem args1_readable : args1.readsIn .view = true := rfl
theorem copy_body_within : Prog.withinM .view (body copyInit) = true := rfl

theorem first_call : TRun.call args1 ret1 (body copyInit).ext (body copyInit).runR caller = .ok first :=
  call_return args1 ret1 (body copyInit).ext (body copyInit).runR caller env1 args1_evaluate
    bodyOut1 copy_body_evaluates

theorem first_frame : TGFrameM .view caller first.st first.ext :=
  (memory_call_allocation_frame .view arrayType "copyCall" (.user "copyResult") rfl rfl
    args1 args1_readable (body copyInit) copy_body_within caller env1 args1_evaluate
    bodyOut1 copy_body_evaluates).2.2.1

def args2 : Args contract FirstCtx Params :=
  .snocMemory (.snocMemory .nil arrayType (.user "aliasA") (.var (.there .here) rfl))
    arrayType (.user "aliasB") (.var (.there (.there .here)) rfl)
def env2 : TEnv contract first.st.H Params :=
  (some (HRef.wk first.ext (seed.val : HRef caller.H arrayType)),
    some (HRef.wk first.ext (seed.val : HRef caller.H arrayType)), ())
def ret2 : CallRet FirstCtx [.mem arrayType] FinalCtx := .mem arrayType (.user "newResult") rfl rfl
def entry2 : Out contract first.st.H Input := ret2.enterT (first.st.withEnv env2)
def growth2 : Grew contract Input entry2.st.H (MVal · (.ref arrayType)) :=
  entry2.st.copyStToMG (newArrT arrayType ⟨3, rfl⟩ rfl) rfl

def bodyOut2 : Out contract entry2.st.H Input :=
  ⟨((growth2.st.push (t := .mem arrayType) (some growth2.val)).setLocal
    (.there .here) (some growth2.val)).drop (.push .refl), growth2.ext⟩
def second : Out contract first.st.H FinalCtx :=
  ⟨bodyOut2.st.withEnv (ret2.leaveT (TEnv.wk (entry2.ext.trans bodyOut2.ext) FirstCtx first.st.env)
    (TEnv.take [.mem arrayType] (TEnv.drop (body newInit).ext bodyOut2.st.env))),
    entry2.ext.trans bodyOut2.ext⟩
def final : Out contract caller.H FinalCtx := ⟨second.st, first.ext.trans second.ext⟩

theorem args2_evaluate : args2.evalT first.st = .ok env2 := rfl
theorem new_body_evaluates : (body newInit).runR entry2.st = .ok bodyOut2 := rfl
theorem args2_readable : args2.readsIn .view = true := rfl
theorem new_body_within : Prog.withinM .view (body newInit) = true := rfl

theorem second_call : TRun.call args2 ret2 (body newInit).ext (body newInit).runR first.st = .ok second :=
  call_return args2 ret2 (body newInit).ext (body newInit).runR first.st env2 args2_evaluate
    bodyOut2 new_body_evaluates

theorem second_frame : TGFrameM .view first.st second.st second.ext :=
  (memory_call_allocation_frame .view arrayType "newCall" (.user "newResult") rfl rfl
    args2 args2_readable (body newInit) new_body_within first.st env2 args2_evaluate
    bodyOut2 new_body_evaluates).2.2.1

def twoCalls : Prog contract CallerCtx FinalCtx :=
  .cons (.call "copyCall" args1 ret1 (body copyInit))
    (.cons (.call "newCall" args2 ret2 (body newInit)) .nil)

theorem actual_two_calls : twoCalls.runR caller = .ok final := by
  change TRun.seq (TRun.call args1 ret1 (body copyInit).ext (body copyInit).runR)
    (TRun.seq (TRun.call args2 ret2 (body newInit).ext (body newInit).runR) TRun.nil) caller = .ok final
  simp only [TRun.seq, first_call, second_call, TRun.nil, Except.map]
  rfl

theorem total_frame : TGFrameM .view caller final.st final.ext := first_frame.trans second_frame _
theorem all_caller_objects_kept : Heap.Keeps final.ext caller.heap final.st.heap := total_frame.keeps

theorem globals_preserved : final.st.storage = caller.storage ∧ final.st.tx = caller.tx ∧
    final.st.selfBalance = caller.selfBalance ∧ final.st.net = caller.net :=
  ⟨(total_frame.keepsSt (by decide)).1, total_frame.tx,
    total_frame.selfBalance (by decide), (total_frame.keepsSt (by decide)).2⟩

def contents {Γ : Ctx} (state : State contract Γ) (i : Idx Γ (.mem arrayType)) : Option (List Int) :=
  (TEnv.get i state.env).map (fun (r : HRef state.H arrayType) => (state.heap.get r).1.map Subtype.val)

theorem initial_contents :
    (contents caller .here, contents caller (.there .here)) = (some [7, 11], some [7, 11]) := by
  decide +kernel

theorem intermediate_contents :
    (TRun.call args1 ret1 (body copyInit).ext (body copyInit).runR caller).map
      (fun out => (contents out.st .here, contents out.st (.there .here),
        contents out.st (.there (.there .here)))) =
      .ok (some [13, 17], some [7, 11], some [7, 11]) := by
  rw [first_call]
  apply congrArg Except.ok
  decide +kernel

theorem final_contents : (twoCalls.runR caller).map
    (fun out => (contents out.st .here, contents out.st (.there .here),
      contents out.st (.there (.there .here)), contents out.st (.there (.there (.there .here))))) =
      .ok (some [0, 0, 0], some [13, 17], some [7, 11], some [7, 11]) := by
  rw [actual_two_calls]
  apply congrArg Except.ok
  decide +kernel

def ids (out : Out contract caller.H FinalCtx) : Option Nat × Option Nat × Option Nat × Option Nat × Nat :=
  (out.st.env.1.map HRef.id, out.st.env.2.1.map HRef.id,
    out.st.env.2.2.1.map HRef.id, out.st.env.2.2.2.1.map HRef.id, out.st.H.length)

theorem final_identities : (twoCalls.runR caller).map ids = .ok (some 4, some 2, some 0, some 0, 5) := by
  rw [actual_two_calls]
  apply congrArg Except.ok
  decide +kernel

theorem allocation_phases :
    (caller.H.length, entry1.st.H.length, first.st.H.length, entry2.st.H.length, final.st.H.length) =
      (1, 2, 3, 4, 5) := by decide +kernel

def globals {Γ : Ctx} (state : State contract Γ) (a b : Idx Γ (.val .uint)) :
    Int × Int × Int × Int × Int × Int :=
  ((TEnv.get a state.env).1, (TEnv.get b state.env).1,
    (state.storage.get persistent.declared).view.1, (state.storage.get transient.declared).view.1,
    state.tx.msgSender.1, state.tx.msgValue.1)

theorem intermediate_globals :
    (TRun.call args1 ret1 (body copyInit).ext (body copyInit).runR caller).map
      (fun out => globals out.st (.there (.there (.there .here))) (.there (.there (.there (.there .here))))) =
      .ok (9, 11, 7, 9, 9, 7) := by
  rw [first_call]
  apply congrArg Except.ok
  decide +kernel

theorem final_globals : (twoCalls.runR caller).map
    (fun out => globals out.st (.there (.there (.there (.there .here))))
      (.there (.there (.there (.there (.there .here)))))) = .ok (9, 11, 7, 9, 9, 7) := by
  rw [actual_two_calls]
  apply congrArg Except.ok
  decide +kernel

theorem wrong_old_content : (twoCalls.runR caller).map
    (fun out => contents out.st (.there (.there .here))) ≠ .ok (some [99, 11]) := by
  rw [actual_two_calls]
  intro h
  have correct : contents final.st (.there (.there .here)) = some [7, 11] := by decide +kernel
  have bad : (some [7, 11] : Option (List Int)) = some [99, 11] := correct.symm.trans (Except.ok.inj h)
  have impossible : (7 : Int) = 99 := congrArg (fun x => x.head!) (Option.some.inj bad)
  cases impossible

theorem swapped_fresh_results : (twoCalls.runR caller).map ids ≠ .ok (some 2, some 4, some 0, some 0, 5) := by
  rw [final_identities]
  intro h
  have impossible : (4 : Nat) = 2 := Option.some.inj (congrArg Prod.fst (Except.ok.inj h))
  cases impossible

theorem premature_transient_reset : (twoCalls.runR caller).map
    (fun out => (out.st.storage.get transient.declared).view.1) ≠ .ok 0 := by
  rw [actual_two_calls]
  intro h
  have impossible : (9 : Int) = 0 := Except.ok.inj h
  cases impossible

/-- A genuine older-alias write: the existing withinM guard must reject it. -/
def writeOld : Prog contract CallerCtx CallerCtx :=
  .cons (.assignMem (.index .dyn (.var .here rfl) (.simple (.lit 0 rfl)))
    (.val (.simple (.lit 99 rfl)))) .nil

theorem write_old_rejected : Prog.withinM .view writeOld = false ∧
    Prog.withinM .nonpayable writeOld = false := ⟨rfl, rfl⟩

private def resultEq {α : Type} [DecidableEq α] : DecidableEq (TRes α)
  | .ok a, .ok b => if h : a = b then isTrue (h ▸ rfl) else isFalse (fun e => h (Except.ok.inj e))
  | .error a, .error b => if h : a = b then isTrue (h ▸ rfl) else isFalse (fun e => h (Except.error.inj e))
  | .ok _, .error _ => isFalse (by intro h; cases h)
  | .error _, .ok _ => isFalse (by intro h; cases h)
private def contentsResultEq : DecidableEq (TRes (Option (List Int) × Option (List Int))) :=
  @resultEq _ inferInstance

theorem actual_old_alias_write : (writeOld.runR caller).map
    (fun out => (contents out.st .here, contents out.st (.there .here))) =
      .ok (some [99, 11], some [99, 11]) := by
  apply @of_decide_eq_true _ (contentsResultEq _ _)
  decide +kernel

/-- info: 'Solidity.Backend.InternalFlow.AllocationFrameChecks.args1_evaluate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms args1_evaluate
/-- info: 'Solidity.Backend.InternalFlow.AllocationFrameChecks.copy_body_evaluates' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms copy_body_evaluates
/-- info: 'Solidity.Backend.InternalFlow.AllocationFrameChecks.args1_readable' depends on axioms: [propext] -/
#guard_msgs in
#print axioms args1_readable
/-- info: 'Solidity.Backend.InternalFlow.AllocationFrameChecks.copy_body_within' depends on axioms: [propext] -/
#guard_msgs in
#print axioms copy_body_within
/-- info: 'Solidity.Backend.InternalFlow.AllocationFrameChecks.first_call' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms first_call
/-- info: 'Solidity.Backend.InternalFlow.AllocationFrameChecks.first_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms first_frame
/-- info: 'Solidity.Backend.InternalFlow.AllocationFrameChecks.args2_evaluate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms args2_evaluate
/-- info: 'Solidity.Backend.InternalFlow.AllocationFrameChecks.new_body_evaluates' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms new_body_evaluates
/-- info: 'Solidity.Backend.InternalFlow.AllocationFrameChecks.args2_readable' depends on axioms: [propext] -/
#guard_msgs in
#print axioms args2_readable
/-- info: 'Solidity.Backend.InternalFlow.AllocationFrameChecks.new_body_within' depends on axioms: [propext] -/
#guard_msgs in
#print axioms new_body_within
/-- info: 'Solidity.Backend.InternalFlow.AllocationFrameChecks.second_call' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms second_call
/-- info: 'Solidity.Backend.InternalFlow.AllocationFrameChecks.second_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms second_frame
/-- info: 'Solidity.Backend.InternalFlow.AllocationFrameChecks.actual_two_calls' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms actual_two_calls
/-- info: 'Solidity.Backend.InternalFlow.AllocationFrameChecks.total_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms total_frame
/-- info: 'Solidity.Backend.InternalFlow.AllocationFrameChecks.all_caller_objects_kept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms all_caller_objects_kept
/-- info: 'Solidity.Backend.InternalFlow.AllocationFrameChecks.globals_preserved' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms globals_preserved
/-- info: 'Solidity.Backend.InternalFlow.AllocationFrameChecks.initial_contents' depends on axioms: [propext] -/
#guard_msgs in
#print axioms initial_contents
/-- info: 'Solidity.Backend.InternalFlow.AllocationFrameChecks.intermediate_contents' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms intermediate_contents
/-- info: 'Solidity.Backend.InternalFlow.AllocationFrameChecks.final_contents' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms final_contents
/-- info: 'Solidity.Backend.InternalFlow.AllocationFrameChecks.final_identities' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms final_identities
/-- info: 'Solidity.Backend.InternalFlow.AllocationFrameChecks.allocation_phases' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms allocation_phases
/-- info: 'Solidity.Backend.InternalFlow.AllocationFrameChecks.intermediate_globals' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms intermediate_globals
/-- info: 'Solidity.Backend.InternalFlow.AllocationFrameChecks.final_globals' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms final_globals
/-- info: 'Solidity.Backend.InternalFlow.AllocationFrameChecks.wrong_old_content' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms wrong_old_content
/-- info: 'Solidity.Backend.InternalFlow.AllocationFrameChecks.swapped_fresh_results' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms swapped_fresh_results
/-- info: 'Solidity.Backend.InternalFlow.AllocationFrameChecks.premature_transient_reset' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms premature_transient_reset
/-- info: 'Solidity.Backend.InternalFlow.AllocationFrameChecks.write_old_rejected' depends on axioms: [propext] -/
#guard_msgs in
#print axioms write_old_rejected
/-- info: 'Solidity.Backend.InternalFlow.AllocationFrameChecks.actual_old_alias_write' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms actual_old_alias_write

end Solidity.Backend.InternalFlow.AllocationFrameChecks
