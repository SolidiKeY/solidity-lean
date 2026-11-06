import Solidity.Lowering.V08.LiteralFailureNestedSlice

/-! Proof evidence indexed by actual typed slice expressions. This is not a
second expression syntax, evaluator or admission predicate. Every step retains
the original local-index observations and the existing slice bounds. -/
namespace Solidity.Lowering.V08.LiteralFailureSliceChain
open Solidity Source

inductive Checked {E : Env} {Γ : RCtx} (locals : Locals E.layout Γ) :
 RExpr E Γ (.bytes .calldata) → Nat → Nat → Nat → Prop
 | local (index : Source.Idx Γ (.bytes .calldata)) (off len : Nat)
   (present : locals.get index=.cdRef rfl off len) :
   Checked locals (.local index) 1 off len
 | range {a h off len} (prior : Checked locals a h off len)
   (i j : Source.Idx Γ (.int IntTy.u256)) (s e : Roadmap.Word)
   (start : locals.get i=SourceEnvironment.sourceWord s)
   (stop : locals.get j=SourceEnvironment.sourceWord e)
   (ordered : s.val≤e.val) (bounded : e.val≤len) :
   Checked locals (.slice a rfl (.local i) rfl (.local j) rfl false)
    (h+1) (off+s.val) (e.val-s.val)
 | from {a h off len} (prior : Checked locals a h off len)
   (i : Source.Idx Γ (.int IntTy.u256)) (s : Roadmap.Word)
   (start : locals.get i=SourceEnvironment.sourceWord s) (bounded : s.val≤len) :
   Checked locals (.slice a rfl (.local i) rfl (.const (Q.ofInt 0)) zero_isIndex true)
    (h+1) (off+s.val) (len-s.val)

theorem height_positive {E : Env} {Γ a h off len} {locals : Locals E.layout Γ}
 (checked : Checked locals a h off len) : 0<h := by
 induction checked <;> omega

theorem run {E : Env} {Γ a h off len} {locals : Locals E.layout Γ}
 (G : Glob E) (F : Fr) (fuel : Nat) (state : St E)
 (checked : Checked locals a h off len) (sufficient : h≤fuel) :
 (evalE G F fuel a).run (locals,state)=
 (.ok (.val (.cdRef rfl off len)),(locals,state)) := by
 induction checked generalizing fuel with
 | «local» index off len present =>
  cases fuel with
  | zero => omega
  | succ n =>
   simp only [evalE,EM.locals,bind,pure,ExceptT.bind,ExceptT.pure,ExceptT.bindCont,
    ExceptT.run,ExceptT.mk,StateT.bind,StateT.pure,StateT.get,get,getThe,
    MonadStateOf.get,liftM,monadLift,MonadLift.monadLift,ExceptT.lift,
    Functor.map,StateT.map,present]
 | range prior i j s e start stop ordered bounded ih =>
  have positive := height_positive prior
  cases fuel with
  | zero => omega
  | succ k =>
   have head := ih k (by omega)
   cases k with
   | zero => omega
   | succ n =>
    rw [evalE]
    dsimp only [ExceptT.run] at head
    simp only [bind,pure,ExceptT.bind,ExceptT.pure,ExceptT.bindCont,ExceptT.run,
     ExceptT.mk,StateT.bind]
    rw [head]
    simp only [evalE,EM.locals,getV,RVal.get,indexNat,RVal.amount,start,stop,
     SourceEnvironment.sourceWord,EM.lift,bind,pure,ExceptT.bind,ExceptT.pure,
     ExceptT.bindCont,ExceptT.mk,StateT.bind,StateT.pure,StateT.get,
     get,getThe,MonadStateOf.get,liftM,monadLift,MonadLift.monadLift,ExceptT.lift,
     Functor.map,StateT.map,Except.pure,Int.toNat_natCast,sliceR,STy.cdStride,
     Bool.false_eq_true,↓reduceIte,Nat.one_mul,if_neg (Nat.not_lt.mpr ordered),if_neg (Nat.not_lt.mpr bounded)]
 | «from» prior i s start bounded ih =>
  have positive := height_positive prior
  cases fuel with
  | zero => omega
  | succ k =>
   have head := ih k (by omega)
   cases k with
   | zero => omega
   | succ n =>
    rw [evalE]
    dsimp only [ExceptT.run] at head
    simp only [bind,pure,ExceptT.bind,ExceptT.pure,ExceptT.bindCont,ExceptT.run,
     ExceptT.mk,StateT.bind]
    rw [head]
    simp only [evalE,EM.locals,getV,RVal.get,indexNat,RVal.amount,start,
     SourceEnvironment.sourceWord,EM.lift,bind,pure,ExceptT.bind,ExceptT.pure,
     ExceptT.bindCont,ExceptT.mk,StateT.bind,StateT.pure,StateT.get,
     get,getThe,MonadStateOf.get,liftM,monadLift,MonadLift.monadLift,ExceptT.lift,
     Functor.map,StateT.map,Except.pure,Int.toNat_natCast,sliceR,STy.cdStride,
     ↓reduceIte,Nat.one_mul,Nat.lt_irrefl,if_neg (Nat.not_lt.mpr bounded)]

theorem arguments_run {E : Env} {Γ a h off len types} {locals : Locals E.layout Γ}
 {tail : RArgs E Γ types} {values : Source.Vals E.layout types}
 (G : Glob E) (F : Fr) (fuel : Nat) (state : St E)
 (checked : Checked locals a h off len) (head_room : h≤fuel) (tail_room : types.length+3≤fuel)
 (lookups : LiteralFailureMixedExpression.LocalArgs locals tail values) :
 (evalArgs G F (fuel+1) (.cons a tail)).run (locals,state)=
 (.ok (.cons (.val (.cdRef rfl off len)) values.toR),(locals,state)) := by
 have head := run G F fuel state checked head_room
 have tailRun := LiteralFailureMixedExpression.arguments_run G F (fuel-(types.length+3)) locals state lookups
 have same : types.length+(fuel-(types.length+3))+3=fuel := by omega
 rw [same] at tailRun
 rw [evalArgs]
 dsimp only [ExceptT.run] at head tailRun
 simp only [bind,pure,ExceptT.bind,ExceptT.pure,ExceptT.bindCont,ExceptT.run,ExceptT.mk,StateT.bind]
 rw [head]
 simp only [bind,pure,ExceptT.bindCont,StateT.bind]
 rw [tailRun]
 rfl

theorem encode_run {E : Env} {Γ a h off len types shapes} {locals : Locals E.layout Γ}
 {tail : RArgs E Γ types} {values : Source.Vals E.layout types} {encoded : AbiEntry.Vals shapes} {parts}
 (G : Glob E) (F : Fr) (fuel : Nat) (state : St E)
 (checked : Checked locals a h off len) (head_room : h≤fuel) (tail_room : types.length+3≤fuel)
 (lookups : LiteralFailureMixedExpression.LocalArgs locals tail values)
 (located : LiteralFailureCalldataPrefix.Located F state values encoded parts) :
 (evalE G F (fuel+2) (.abiEncode .encode (.cons a tail))).run (locals,state)=
 (.ok (.val (.memRef rfl state.heap.next)),
  (locals,SourceKeccak.afterLiteral state
   (AbiEntry.encodeArgs (.cons (.bytes ((F.cd.drop off).take len)) encoded)))) :=
 SourceAbi.execute G F (fuel+1) false (.cons a tail) _ _ _ state state state _ _
 (arguments_run G F fuel state checked head_room tail_room lookups)
 (LiteralFailureCalldataPrefix.encoding_run F _ _ state (.bytes off len located))

theorem range_revert {E : Env} {Γ a h off len} {locals : Locals E.layout Γ}
 (G : Glob E) (F : Fr) (fuel : Nat) (state : St E)
 (checked : Checked locals a h off len) (sufficient : h≤fuel)
 (i j : Source.Idx Γ (.int IntTy.u256)) (s e : Roadmap.Word)
 (start : locals.get i=SourceEnvironment.sourceWord s) (stop : locals.get j=SourceEnvironment.sourceWord e)
 (wrong : e.val<s.val ∨ len<e.val) :
 (evalE G F (fuel+1) (.slice a rfl (.local i) rfl (.local j) rfl false)).run (locals,state)=
 (.error (.revert []),(locals,state)) := by
 have head := run G F fuel state checked sufficient
 have positive := height_positive checked
 cases fuel with
 | zero => omega
 | succ n =>
  rw [evalE]
  dsimp only [ExceptT.run] at head
  simp only [bind,pure,ExceptT.bind,ExceptT.pure,ExceptT.bindCont,ExceptT.run,ExceptT.mk,StateT.bind]
  rw [head]
  simp only [evalE,EM.locals,getV,RVal.get,indexNat,RVal.amount,start,stop,
   SourceEnvironment.sourceWord,EM.lift,bind,pure,ExceptT.bind,ExceptT.pure,
   ExceptT.bindCont,ExceptT.mk,StateT.bind,StateT.pure,StateT.get,
   get,getThe,MonadStateOf.get,liftM,monadLift,MonadLift.monadLift,ExceptT.lift,
   Functor.map,StateT.map,Except.pure,Int.toNat_natCast,sliceR,Bool.false_eq_true,↓reduceIte]
  rcases wrong with wrong | wrong
  · simp only [if_pos wrong]
    rfl
  · by_cases order : e.val<s.val
    · simp only [if_pos order]
      rfl
    · simp only [if_neg order,if_pos wrong]
      rfl

theorem from_revert {E : Env} {Γ a h off len} {locals : Locals E.layout Γ}
 (G : Glob E) (F : Fr) (fuel : Nat) (state : St E)
 (checked : Checked locals a h off len) (sufficient : h≤fuel)
 (i : Source.Idx Γ (.int IntTy.u256)) (s : Roadmap.Word)
 (start : locals.get i=SourceEnvironment.sourceWord s) (wrong : len<s.val) :
 (evalE G F (fuel+1) (.slice a rfl (.local i) rfl (.const (Q.ofInt 0)) zero_isIndex true)).run (locals,state)=
 (.error (.revert []),(locals,state)) := by
 have head := run G F fuel state checked sufficient
 have positive := height_positive checked
 cases fuel with
 | zero => omega
 | succ n =>
  rw [evalE]
  dsimp only [ExceptT.run] at head
  simp only [bind,pure,ExceptT.bind,ExceptT.pure,ExceptT.bindCont,ExceptT.run,ExceptT.mk,StateT.bind]
  rw [head]
  simp only [evalE,EM.locals,getV,RVal.get,indexNat,RVal.amount,start,
   SourceEnvironment.sourceWord,EM.lift,bind,pure,ExceptT.bind,ExceptT.pure,
   ExceptT.bindCont,ExceptT.mk,StateT.bind,StateT.pure,StateT.get,
   get,getThe,MonadStateOf.get,liftM,monadLift,MonadLift.monadLift,ExceptT.lift,
   Functor.map,StateT.map,Except.pure,Int.toNat_natCast,sliceR,↓reduceIte,if_pos wrong]
  rfl

private theorem encode_error {E : Env} {Γ types} {a : RExpr E Γ (.bytes .calldata)} (G : Glob E) (F : Fr) (fuel : Nat)
 (locals : Locals E.layout Γ) (state : St E) (tail : RArgs E Γ types)
 (head : (evalE G F fuel a).run (locals,state)=(.error (.revert []),(locals,state))) :
 (evalE G F (fuel+2) (.abiEncode .encode (.cons a tail))).run (locals,state)=
 (.error (.revert []),(locals,state)) := by
 have args : (evalArgs G F (fuel+1) (.cons a tail)).run (locals,state)=
  (.error (.revert []),(locals,state)) := by
  rw [evalArgs]
  dsimp only [ExceptT.run] at head
  simp only [bind,pure,ExceptT.bind,ExceptT.bindCont,ExceptT.run,ExceptT.mk,StateT.bind,StateT.pure,head]
 dsimp only [ExceptT.run] at args
 simp only [evalE,bind,pure,ExceptT.bind,ExceptT.bindCont,ExceptT.run,ExceptT.mk,StateT.bind,StateT.pure,args]

theorem encode_from_revert {E : Env} {Γ a h off len types} {locals : Locals E.layout Γ}
 (G : Glob E) (F : Fr) (fuel : Nat) (state : St E)
 (checked : Checked locals a h off len) (sufficient : h≤fuel)
 (i : Source.Idx Γ (.int IntTy.u256)) (s : Roadmap.Word)
 (start : locals.get i=SourceEnvironment.sourceWord s) (wrong : len<s.val)
 (tail : RArgs E Γ types) :
 (evalE G F (fuel+3) (.abiEncode .encode (.cons
  (.slice a rfl (.local i) rfl (.const (Q.ofInt 0)) zero_isIndex true) tail))).run (locals,state)=
 (.error (.revert []),(locals,state)) :=
 encode_error G F (fuel+1) locals state tail (from_revert G F fuel state checked sufficient i s start wrong)

theorem encode_range_revert {E : Env} {Γ a h off len types} {locals : Locals E.layout Γ}
 (G : Glob E) (F : Fr) (fuel : Nat) (state : St E)
 (checked : Checked locals a h off len) (sufficient : h≤fuel)
 (i j : Source.Idx Γ (.int IntTy.u256)) (s e : Roadmap.Word)
 (start : locals.get i=SourceEnvironment.sourceWord s) (stop : locals.get j=SourceEnvironment.sourceWord e)
 (wrong : e.val<s.val ∨ len<e.val) (tail : RArgs E Γ types) :
 (evalE G F (fuel+3) (.abiEncode .encode (.cons (.slice a rfl (.local i) rfl (.local j) rfl false) tail))).run (locals,state)=
 (.error (.revert []),(locals,state)) :=
 encode_error G F (fuel+1) locals state tail (range_revert G F fuel state checked sufficient i j s e start stop wrong)

end Solidity.Lowering.V08.LiteralFailureSliceChain
