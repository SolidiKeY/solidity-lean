import Solidity.Backend.Transient.WordControls
import Solidity.Source.Eval
import Solidity.Source.WellTyped
import Solidity.Roadmap.Controls

/-! Real Source callAddr/envLoop/registered fallback transient execution.
Resolved-program fixture only: no frontend/code provenance or allowed-external-
EVM-strategy adequacy is inferred. Full ordered Source events are retained. -/
namespace Solidity.Backend.Transient.SourceCallback
open Solidity.Backend.Transient
open Solidity.Source

def fallbackDecl : Source.Decl :=
  ⟨.fallback,"",some "P7",false,
   .fallback .fbNoParams true (some .payable) .nil false none
     (.some (.block (.cons (.stmtItem (.simpleStmt (.exprStmt
       (.assign .assign (.ident "scratch") (.lit (.bool true)))))) .nil)))⟩
def unit : Source.Syn .unit := .unit (.cons (.contract false "P7" .none .nil
  (.cons (Controls.declaration "saved" false).node
    (.cons (Controls.declaration "scratch" true).node (.cons fallbackDecl.node .nil)))) .nil)
def env : Source.Env := unit.env
def slot : BoolSlot env := ⟨Controls.path,rfl,rfl,Controls.slot.key⟩
def body : Source.RBody env :=
  ⟨[],[],false,[],[],.stmt (.expr (.assign (.state (Controls.declaration "scratch" true) rfl rfl)
    (.bool true))) .nil,[]⟩
def external : Roadmap.Address := ⟨0x40,by decide⟩
def program : Source.Program env :=
  {body := fun d => if d.kind==.fallback then some body else none,
   consts := fun _ => none,inits := fun _ => [],ctor := fun _ => none,
   ctorLocals := fun _ => [],baseArgs := fun _ => [],contracts := ["P7"]}
def global (pipeline : Roadmap.Pipeline) (out : Roadmap.Outcome) : Source.Glob env :=
  {prog := program,pipeline := pipeline,fixed := Roadmap.Controls.toyFixed,
   balance0 := fun _ => ⟨100,by decide⟩,hasCode := fun _ a => a==external,
   callee := fun history => match history.getLast? with
     | some (.call a _ _ _) => if a=external then .reenter Controls.owner external ⟨0,by decide⟩ [] false else .answer out
     | _ => .answer out,
   timestamp := ⟨12345,by decide⟩}
def source : Source.EMState env [.bool] :=
  ⟨.cons (.bool true) .nil,
   ⟨⟨⟨fun _ => Source.Account.empty _⟩,Source.Transient.empty,[]⟩,
    (Source.Heap.empty.alloc ⟨.bytes .memory,.bytes [0xa1,0,0xfe]⟩).1,
    [.call Controls.other ⟨3,by decide⟩ [0x12] false],[(Controls.owner,[0x99,0x42])],
    ⟨[.bool],.cons (.bool false) .nil⟩,Source.FailureExecution.Cursor.empty⟩⟩
def before : Source.EMState env [.bool] :=
  ⟨source.1,{source.2 with ex := source.2.ex.run [
    .account Controls.owner (fun a => { a with
      balance := ⟨93,by decide⟩
      nonce := 4
      code := some 0
      storage := a.storage.write Controls.saved (.bool true) }),
    .transient Controls.other (fun cells => cells.write Controls.path (.bool true))]}⟩
def credited := before.2.ex.apply (.account Controls.owner (fun a => a.withBalance ⟨93,by decide⟩))
def changed := credited.apply (.transient Controls.owner (fun cells => cells.write Controls.path (.bool true)))
def run (pipeline : Roadmap.Pipeline) (out : Roadmap.Outcome) (static : Bool) (horizon : Nat) :
    Source.EM env [.bool] Roadmap.Outcome := do
  let (result,_) ← Source.EM.sub (Source.L0 env)
    (Source.callAddr (global pipeline out) {Controls.frame with static:=static} horizon external ⟨0,by decide⟩ [0x42] false)
  pure result

def events (out : Roadmap.Outcome) (static : Bool) : List Roadmap.Event := before.2.events++
  [.call external ⟨0,by decide⟩ [0x42] static,
   .reenter Controls.owner external ⟨0,by decide⟩ [] false,
   .reentered (if static then .revert [] else .success []),.answer out none]
def after (out : Roadmap.Outcome) (static : Bool) : Source.EMState env [.bool] :=
  ⟨before.1,{ before.2 with
    ex := if static then before.2.ex else match out with
      | .success _ => changed | .revert _ => before.2.ex
    events := events out static }⟩

theorem success (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    (run pipeline (.success bytes) false 10).run before=(.ok (.success bytes),after (.success bytes) false) := by
  cases pipeline <;> rfl

theorem undo_changed : Source.ExecState.undoN 2 changed=before.2.ex := by
  simp only [changed,credited,Source.ExecState.undoN,Source.ExecState.undo_apply]

theorem undo_credit : Source.ExecState.undoN 1 credited=before.2.ex := by
  simp only [credited,Source.ExecState.undoN,Source.ExecState.undo_apply]

theorem revert (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    (run pipeline (.revert bytes) false 10).run before=(.ok (.revert bytes),after (.revert bytes) false) := by
  have actual : (run pipeline (.revert bytes) false 10).run before=
      (.ok (.revert bytes),(before.1,{before.2 with
        ex := Source.ExecState.undoN 2 changed
        events := events (.revert bytes) false})) := by
    cases pipeline <;> rfl
  rw [undo_changed] at actual
  exact actual

theorem static (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    (run pipeline (.success bytes) true 10).run before=(.ok (.success bytes),after (.success bytes) true) := by
  have actual : (run pipeline (.success bytes) true 10).run before=
      (.ok (.success bytes),(before.1,{before.2 with
        ex := Source.ExecState.undoN 1 credited
        events := events (.success bytes) true})) := by
    cases pipeline <;> rfl
  rw [undo_credit] at actual
  exact actual

def pending : Source.EMState env [.bool] :=
  ⟨before.1,{before.2 with ex := credited,events := before.2.events++
    [.call external ⟨0,by decide⟩ [0x42] false,
     .reenter Controls.owner external ⟨0,by decide⟩ [] false]}⟩

theorem timeout_prefix (pipeline : Roadmap.Pipeline) :
    (run pipeline (.success []) false 4).run before=(.error .timeout,pending) := by
  cases pipeline <;> rfl

def child (static : Bool) : Source.Fr :=
  {this := Controls.owner,sender := external,value := ⟨0,by decide⟩,
   static := static,contract := "P7",depth := 2}

theorem registered : env.special "P7" .fallback=some fallbackDecl := rfl

theorem classification (pipeline : Roadmap.Pipeline) (out : Roadmap.Outcome) :
    (before.2.ex.world.accounts Controls.owner).code=some 0 ∧
    (global pipeline out).contractAt 0=some "P7" ∧
    (global pipeline out).hasCode before.2.events external=true ∧
    (before.2.ex.world.accounts external).code=none ∧
    external≠Controls.owner := ⟨rfl,rfl,rfl,rfl,by decide⟩

/-- Actual Source callback execution paired with executed target context/code on
an arbitrary target state. Only the post-write selected cell is related; no
initial relation is assumed, so this is not a composition or G42 correspondence. -/
theorem source_target (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) (target : State) :
    (run pipeline (.success bytes) false 10).run before=
      (.ok (.success bytes),after (.success bytes) false) ∧
    callbackInFrame (child false) (storeCode slot.key (boolWord true)) target=
      .ok (write target Controls.owner slot.key (boolWord true)) ∧
    Represents slot Controls.owner (after (.success bytes) false)
      (write target Controls.owner slot.key (boolWord true)) := by
  refine ⟨success pipeline bytes,framed_store (child false) rfl _ _ target,true,?_,?_⟩
  · rfl
  · exact put_same target.bank Controls.owner slot.key (boolWord true)

theorem static_target (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) (target : State) :
    (run pipeline (.success bytes) true 10).run before=
      (.ok (.success bytes),after (.success bytes) true) ∧
    callbackInFrame (child true) (storeCode slot.key (boolWord true)) target=
      .error .staticWrite target :=
  ⟨static pipeline bytes,framed_static_store (child true) rfl _ _ target⟩

theorem before_memOK : Source.MemOK env before.2.heap.ty before := by
  have ok : Source.HeapOK (E:=env) before.2.heap :=
    Source.HeapOK.alloc Source.HeapOK.empty (.bytes [0xa1,0,0xfe])
  have shaped : Source.HeapShaped (E:=env) before.2.heap :=
    Source.HeapShaped.alloc (E:=env) (x:=⟨.bytes .memory,.bytes [0xa1,0,0xfe]⟩) Source.HeapShaped.empty trivial
  have inner : Source.HeapInner (E:=env) before.2.heap :=
    Source.HeapInner.alloc (E:=env) (x:=⟨.bytes .memory,.bytes [0xa1,0,0xfe]⟩) Source.HeapInner.empty trivial
  exact ⟨⟨⟨ok,Source.HeapTy.Le.refl _⟩,⟨trivial,trivial⟩⟩,shaped,inner⟩

theorem after_memOK (out : Roadmap.Outcome) (static : Bool) :
    Source.MemOK env before.2.heap.ty (after out static) :=
  ⟨⟨⟨before_memOK.1.1.heap,before_memOK.1.1.le⟩,before_memOK.1.2⟩,before_memOK.2⟩

theorem exact_prefix (out : Roadmap.Outcome) (static : Bool) :
    (after out static).2.events=events out static ∧
    (after out static).2.logs=before.2.logs ∧ (after out static).2.heap=before.2.heap ∧
    (after out static).1=before.1 ∧ (after out static).2.fnLocals=before.2.fnLocals := ⟨rfl,rfl,rfl,rfl,rfl⟩


def wrongCode : Source.EMState env [.bool] :=
  ⟨before.1,{before.2 with ex := before.2.ex.apply (.account Controls.owner (fun account => {account with code := some 99}))}⟩

def wrongCodeEvents : List Roadmap.Event := before.2.events++
  [.call external ⟨0,by decide⟩ [0x42] false,
   .reenter Controls.owner external ⟨0,by decide⟩ [] false,
   .reentered (.revert []),.answer (.success []) none]

theorem wrong_code (pipeline : Roadmap.Pipeline) :
    (run pipeline (.success []) false 10).run wrongCode=
      (.ok (.success []),(wrongCode.1,{wrongCode.2 with events := wrongCodeEvents})) := by
  cases pipeline <;> rfl

theorem nonempty_outer_revert (pipeline : Roadmap.Pipeline) :
    (run pipeline (.revert [0xa1,0,0xfe]) false 10).run before=
      (.ok (.revert [0xa1,0,0xfe]),after (.revert [0xa1,0,0xfe]) false) := revert pipeline _

theorem wrong_or_truncated_bytes :
    (Roadmap.Outcome.revert [0xa1,0,0xfe])≠.revert [] ∧
    (Roadmap.Outcome.revert [0xa1,0,0xfe])≠.revert [0xa1,0] ∧
    (Roadmap.Outcome.revert [0xa1,0,0xfe])≠.revert [0xfe,0,0xa1] := by decide

end Solidity.Backend.Transient.SourceCallback
