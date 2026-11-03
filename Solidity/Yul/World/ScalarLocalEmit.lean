import Solidity.Yul.World.GeneralFailure

/-! Actual scalar local argument evaluation; new observation extension only. -/
namespace Solidity.Yul.World.ScalarLocalEmit
open Solidity.Source
open Solidity.Yul.Views
open Solidity.Roadmap (Bytes)
open Solidity.Yul.World.ScalarEmitPort (env eventDecl frame signature)
open Solidity.Yul.World.PhysicalCompletion

def statement (indexed anonymous : Bool) (Γ : RCtx) :
    RStmt (env indexed anonymous) [] false ⟨false,false⟩ (ReturningCall.uint::Γ) (ReturningCall.uint::Γ) :=
  .emit (eventDecl indexed anonymous) rfl (.cons (.local .here) (by cases indexed <;> cases anonymous <;> decide) .nil)

def data (v : Int) : Bytes := wordBytes (intWord v)
def after {indexed anonymous Γ} (G : Glob (env indexed anonymous)) (v : Int)
    (s : EMState (env indexed anonymous) Γ) : EMState (env indexed anonymous) Γ :=
  ⟨s.1,{s.2 with logs:=(CallerFrameChecks.owner,G.selector (signature indexed anonymous)++data v)::s.2.logs}⟩

theorem actual_local {indexed anonymous Γ} (G : Glob (env indexed anonymous))
    (v : Int) (bound : IntTy.u256.lo≤v ∧ v≤IntTy.u256.hi)
    (tail : Locals (env indexed anonymous).layout Γ) (st : St (env indexed anonymous)) :
    (Source.execS G (frame false) 5 0 none (statement indexed anonymous Γ)
      (.cons (.int v bound) tail)).run ⟨Source.L0 (env indexed anonymous),st⟩=
      (.ok (.normal (.cons (.int v bound) tail)),after G v ⟨Source.L0 (env indexed anonymous),st⟩) := by
  change ((.ok (.normal (.cons (.int v bound) tail)) : Except Source.Halt (Source.Out (env indexed anonymous).layout (ReturningCall.uint::Γ) (ReturningCall.uint::Γ))),
    (Source.L0 (env indexed anonymous),{st with logs:=(CallerFrameChecks.owner,
      G.selector (signature indexed anonymous)++((data v++[])++[]))::st.logs}))=_
  simp only [List.append_nil]
  rfl

theorem actual_static {indexed anonymous Γ} (G : Glob (env indexed anonymous))
    (v : Int) (bound : IntTy.u256.lo≤v ∧ v≤IntTy.u256.hi)
    (tail : Locals (env indexed anonymous).layout Γ) (st : St (env indexed anonymous)) :
    (Source.execS G (frame true) 5 0 none (statement indexed anonymous Γ)
      (.cons (.int v bound) tail)).run ⟨Source.L0 (env indexed anonymous),st⟩=
      (.error (.revert []),⟨Source.L0 (env indexed anonymous),st⟩) := rfl

def encoding {indexed anonymous} (G : Glob (env indexed anonymous)) (v : Int) : Log :=
  match indexed,anonymous with
  | false,false => ⟨CallerFrameChecks.owner,⟨1,by decide⟩,#v[G.fixed.hash (asciiBytes (signature false false))],data v⟩
  | true,false => ⟨CallerFrameChecks.owner,⟨2,by decide⟩,#v[G.fixed.hash (asciiBytes (signature true false)),intWord v],[]⟩
  | false,true => ⟨CallerFrameChecks.owner,⟨0,by decide⟩,#v[],data v⟩
  | true,true => ⟨CallerFrameChecks.owner,⟨1,by decide⟩,#v[intWord v],[]⟩

def source {indexed anonymous Γ Δ} (G : Glob (env indexed anonymous)) (static : Bool)
    (v : Int) (bound : IntTy.u256.lo≤v ∧ v≤IntTy.u256.hi)
    (tail : Locals (env indexed anonymous).layout Γ) (s : EMState (env indexed anonymous) Δ) :=
  (Source.EM.sub (Source.L0 (env indexed anonymous)) (Source.execS G (frame static) 5 0 none
    (statement indexed anonymous Γ) (.cons (.int v bound) tail))).run s

theorem source_run {indexed anonymous Γ Δ} (G : Glob (env indexed anonymous))
    (v : Int) (bound : IntTy.u256.lo≤v ∧ v≤IntTy.u256.hi)
    (tail : Locals (env indexed anonymous).layout Γ) (s : EMState (env indexed anonymous) Δ) :
    source G false v bound tail s=
      (.ok (.normal (.cons (.int v bound) tail),Source.L0 (env indexed anonymous)),after G v s) := by
  unfold source
  rw [Source.run_sub,actual_local]
  rfl

theorem source_static {indexed anonymous Γ Δ} (G : Glob (env indexed anonymous))
    (v : Int) (bound : IntTy.u256.lo≤v ∧ v≤IntTy.u256.hi)
    (tail : Locals (env indexed anonymous).layout Γ) (s : EMState (env indexed anonymous) Δ) :
    source G true v bound tail s=(.error (.revert []),s) := by
  unfold source
  rw [Source.run_sub,actual_static]

def execute {indexed anonymous Γ Δ} (G : Glob (env indexed anonymous)) (static : Bool)
    (v : Int) (bound : IntTy.u256.lo≤v ∧ v≤IntTy.u256.hi) (tail : Locals (env indexed anonymous).layout Γ)
    (s : EMState (env indexed anonymous) Δ) (r : ResidualJournal Solidity.Yul.Views.complementCarrierOwnership)
    (b : BoolEncodingJournal) (o : ObservedEffects (env indexed anonymous).layout (env indexed anonymous).lay (env indexed anonymous).lay)
    (_shared : o.effects.execution=s.2.ex) :=
  let actual:=source G static v bound tail s
  ((actual.1.map (fun _=>()),(⟨⟨actual.2,r⟩,b⟩ : Carrier (env indexed anonymous) Δ)),
    match actual.1 with | .ok _ => emitObserved o (encoding G v) | .error _ => o)

theorem execute_run {indexed anonymous Γ Δ} (G : Glob (env indexed anonymous))
    (v : Int) (bound : IntTy.u256.lo≤v ∧ v≤IntTy.u256.hi) (tail : Locals (env indexed anonymous).layout Γ)
    (s : EMState (env indexed anonymous) Δ) r b
    (o : ObservedEffects (env indexed anonymous).layout (env indexed anonymous).lay (env indexed anonymous).lay) (shared : o.effects.execution=s.2.ex) :
    execute G false v bound tail s r b o shared=((.ok (),⟨⟨after G v s,r⟩,b⟩),emitObserved o (encoding G v)) := by
  unfold execute
  rw [source_run]
  rfl

theorem execute_static {indexed anonymous Γ Δ} (G : Glob (env indexed anonymous))
    (v : Int) (bound : IntTy.u256.lo≤v ∧ v≤IntTy.u256.hi) (tail : Locals (env indexed anonymous).layout Γ)
    (s : EMState (env indexed anonymous) Δ) r b
    (o : ObservedEffects (env indexed anonymous).layout (env indexed anonymous).lay (env indexed anonymous).lay) (shared : o.effects.execution=s.2.ex) :
    execute G true v bound tail s r b o shared=((.error (.revert []),⟨⟨s,r⟩,b⟩),o) := by
  unfold execute
  rw [source_static]
  rfl

theorem distinct_data : data 1≠data 256 := by decide

theorem inhabited {indexed anonymous} (G : Glob (env indexed anonymous)) (st : St (env indexed anonymous)) :
    source G false 256 (by decide) (.cons (.int (t:=IntTy.u256) 1 (by decide)) .nil) ⟨Source.L0 (env indexed anonymous),st⟩=
      (.ok (.normal (.cons (.int 256 (by decide)) (.cons (.int (t:=IntTy.u256) 1 (by decide)) .nil)),Source.L0 (env indexed anonymous)),
        after G 256 ⟨Source.L0 (env indexed anonymous),st⟩) := source_run G _ _ _ _

end Solidity.Yul.World.ScalarLocalEmit
