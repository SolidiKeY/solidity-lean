import Solidity.Yul.World.EffectfulEmitFunction

namespace Solidity.Yul.World.EffectfulEmitDispatch
open Solidity.Source
open Solidity.Roadmap (Bytes)
open Solidity.Yul.World.EffectfulEmitSource
open Solidity.Yul.World.EffectfulEmitFunction

def input {indexed anonymous} (G : Glob (env indexed anonymous)) : Bytes :=
  G.selector (sigOf (env indexed anonymous).layout "answer" [])

/-- Actual selector/body selection, decode and ordinary call; no selected-run premise. -/
theorem actual {indexed anonymous} (G : Glob (env indexed anonymous)) (F : Fr)
    (s : EMState (env indexed anonymous) []) (normal : F.static=false)
    (code : F.contract="Finite") :
    (Source.dispatch (glob G) F 8 (input G)).run s=
      (.error (.revert (EffectfulEmitRevert.data G)),after G F s) := by
  have length : (input G).length=4 := by
    simp only [input,Glob.selector,List.length_take,Solidity.Source.wordBytes_length]
    rfl
  have nonempty : (input G).isEmpty=false := by
    apply List.isEmpty_eq_false_iff.mpr
    intro nil
    have impossible : (4 : Nat)=0 := length.symm.trans (congrArg List.length nil)
    exact (by decide : (4 : Nat)≠0) impossible
  have resolved : (glob G).dispatchFn "Finite" ReturningCall.answerDecl=ReturningCall.answerDecl := by
    cases indexed <;> cases anonymous <;> rfl
  have found : (glob G).prog.body ReturningCall.answerDecl=some (body indexed anonymous) := rfl
  have signature : ReturningCall.answerDecl.fnSig (env indexed anonymous)=some ([],[ReturningCall.uint]) := rfl
  have picked : (glob G).pickFn F (input G)=some ReturningCall.answerDecl := by
    unfold Glob.pickFn
    rw [code]
    change ([ReturningCall.answerDecl].find? (fun d=>((glob G).prog.body ((glob G).dispatchFn "Finite" d)).isSome &&
      match d.fnSig (env indexed anonymous) with
      | some (ps,_) => (glob G).selector (sigOf (env indexed anonymous).layout d.name ps)==(input G).take 4
      | none => false))=_
    simp only [List.find?_cons,resolved,found,Option.isSome_some,signature,Bool.true_and]
    rw [List.take_of_length_le (by rw [length]; exact Nat.le_refl _)]
    simp only [input,glob,Glob.selector,ReturningCall.answerDecl,BEq.rfl]
  rw [Source.dispatch,picked,nonempty]
  have payable : (ReturningCall.answerDecl.fnMut != some .payable)=false := rfl
  simp only [signature,length,payable,Bool.and_false,Bool.false_eq_true,if_false]
  change ((do
    let (r,_) ← Source.EM.sub (Source.L0 (env indexed anonymous))
      (Source.callInternal (glob G) F 7 ReturningCall.answerDecl .nil [ReturningCall.uint])
    Source.encodeVals F 7 false (← Source.EM.lift (Source.unRet [ReturningCall.uint] r))).run s)=_
  rw [Source.Hoare.run_bind,Source.run_sub,internal_actual G F ⟨Source.L0 (env indexed anonymous),s.2⟩ normal code]
  rfl

end Solidity.Yul.World.EffectfulEmitDispatch
