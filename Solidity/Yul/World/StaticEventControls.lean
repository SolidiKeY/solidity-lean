import Solidity.Yul.World.StaticEventSource

namespace Solidity.Yul.World.StaticEventControls
open Solidity.Source
open Solidity.Roadmap (Word Bytes)
open Solidity.Yul.World.StaticEventArgs
open Solidity.Yul.World.StaticEventEncoding

def declaration (anonymous : Bool) : Decl := ⟨.event,"Mixed",some "Finite",false,
  .event "Mixed" (.cons (.eventParam (.elem .bool) true (some "flag"))
    (.cons (.eventParam (.elem (.int false 256 (by decide))) false (some "value"))
      (.cons (.eventParam (.elem .address) true (some "target")) .nil))) anonymous⟩
def env (anonymous : Bool) : Env := ⟨declaration anonymous::ReturningCall.env.decls⟩
def target : Solidity.Roadmap.Address := ⟨0x70,by decide⟩
def types : List STy := [.bool,ReturningCall.uint,.address false]
def values (anonymous : Bool) : Vals (env anonymous).layout types :=
  .cons (.bool true) (.cons (.int ReturningCall.value (by decide)) (.cons (.address target) .nil))
def locals (anonymous : Bool) : Locals (env anonymous).layout types :=
  .cons (.bool true) (.cons (.int ReturningCall.value (by decide)) (.cons (.address target) .nil))
def args (anonymous : Bool) : RConvArgs (env anonymous) types types :=
  .cons (.local .here) (by cases anonymous <;> decide)
    (.cons (.local (.there .here)) (by cases anonymous <;> decide)
      (.cons (.local (.there (.there .here))) (by cases anonymous <;> decide) .nil))
def part (anonymous : Bool) : Split (env anonymous).layout :=
  ([1,(0x70 : Word)],
    ⟨[ReturningCall.uint],.cons (.int ReturningCall.value (by decide)) .nil⟩)

theorem registered (anonymous : Bool) : (env anonymous).decls.head?=some (declaration anonymous) := rfl

theorem typed (anonymous : Bool) : (declaration anonymous).paramTys (env anonymous)=some types := rfl

theorem partition (anonymous : Bool) : split [true,false,true] (values anonymous)=some (part anonymous) := rfl

theorem evaluated {anonymous} (G : Glob (env anonymous)) (F : Fr) (st : St (env anonymous)) :
    (Source.evalConvArgs G F 8 (args anonymous)).run ⟨locals anonymous,st⟩=(.ok (values anonymous),⟨locals anonymous,st⟩) := by
  cases anonymous <;> cases G with
  | mk p pipeline fixed balance code strategy timestamp => cases pipeline <;> rfl

theorem full_source {anonymous} (G : Glob (env anonymous)) (F : Fr) (st : St (env anonymous))
    (nonstatic : F.static=false) :
    (Source.execS G F 9 0 none (StaticEventSource.statement (declaration anonymous) (typed anonymous) (args anonymous))
      (locals anonymous)).run ⟨Source.L0 (env anonymous),st⟩=
      (.ok (.normal (locals anonymous)),⟨Source.L0 (env anonymous),{st with logs:=(F.this,
        G.selector (sigOf (env anonymous).layout "Mixed" types)++Source.abiLayout
          ([(1 : Word),Source.intWord ReturningCall.value,
            (0x70 : Word)].map (fun w=>(false,wordBytes w))))::st.logs}⟩) := by
  apply StaticEventSource.actual
  · exact evaluated G F st
  · rfl
  · exact nonstatic

theorem encoded {anonymous Γ} (G : Glob (env anonymous)) (F : Fr) (st : EMState (env anonymous) Γ) :
    (encode G F 8 (declaration anonymous) (typed anonymous) (values anonymous)).run st=
      (.ok (some (resultLog (ts:=types) G F (declaration anonymous) anonymous (part anonymous)
        (by cases anonymous <;> simp only [topics,part,Bool.false_eq_true,if_false,if_true,List.length_cons,List.length_nil] <;> decide) ReturningCall.output)),st) := by
  apply encode_exact G F 8 (declaration anonymous) (typed anonymous) (values anonymous) st [true,false,true]
    anonymous (by cases anonymous <;> simp only [metadata,declaration,indexedFlags]) (part anonymous) (partition anonymous) [Source.intWord ReturningCall.value] rfl

theorem static_source {anonymous} (G : Glob (env anonymous)) (F : Fr) (st : St (env anonymous))
    (static : F.static=true) :
    (Source.execS G F 9 0 none (StaticEventSource.statement (declaration anonymous) (typed anonymous) (args anonymous))
      (locals anonymous)).run ⟨Source.L0 (env anonymous),st⟩=(.error (.revert []),⟨Source.L0 (env anonymous),st⟩) := by
  apply StaticEventSource.actual_static G F 8 (declaration anonymous) (typed anonymous) (args anonymous)
    (locals anonymous) (locals anonymous) st st (values anonymous) (evaluated G F st)
    [1,Source.intWord ReturningCall.value,0x70] rfl static

def four (anonymous : Bool) : Decl := ⟨.event,"Four",some "Finite",false,
  .event "Four" (.cons (.eventParam (.elem .bool) true none) (.cons (.eventParam (.elem .bool) true none)
    (.cons (.eventParam (.elem .bool) true none) (.cons (.eventParam (.elem .bool) true none) .nil)))) anonymous⟩
def fourEnv (anonymous : Bool) : Env := ⟨[four anonymous]⟩
def fourValues (anonymous : Bool) : Vals (fourEnv anonymous).layout [.bool,.bool,.bool,.bool] :=
  .cons (.bool true) (.cons (.bool false) (.cons (.bool true) (.cons (.bool false) .nil)))
def fourPart (anonymous : Bool) : Split (fourEnv anonymous).layout := ([1,0,1,0],⟨[],.nil⟩)

theorem fifth_topic_refused {Γ} (G : Glob (fourEnv false)) (F : Fr) (s : EMState (fourEnv false) Γ) :
    (encode G F 8 (four false) rfl (fourValues false)).run s=(.ok none,s) := by
  apply overflow_refused G F 8 (four false) rfl (fourValues false) s [true,true,true,true] false
    (by simp only [metadata,four,indexedFlags]) (fourPart false) rfl
  change ¬(5 : Nat)<5
  decide

theorem anonymous_four {Γ} (G : Glob (fourEnv true)) (F : Fr) (s : EMState (fourEnv true) Γ) :
    (encode G F 8 (four true) rfl (fourValues true)).run s=
      (.ok (some (resultLog (ts:=[.bool,.bool,.bool,.bool]) G F (four true) true (fourPart true) (by change (4 : Nat)<5; decide) [])),s) := by
  apply encode_exact G F 8 (four true) rfl (fourValues true) s [true,true,true,true] true
    (by simp only [metadata,four,indexedFlags]) (fourPart true) rfl [] rfl

theorem wrong_arity (anonymous : Bool) : split [true] (values anonymous)=none := rfl

theorem reference_refused {D : Layout} :
    split [true] (Vals.cons (τ:=.bytes .memory) (.memRef rfl 0) (Vals.nil (D:=D)))=none := rfl
end Solidity.Yul.World.StaticEventControls
