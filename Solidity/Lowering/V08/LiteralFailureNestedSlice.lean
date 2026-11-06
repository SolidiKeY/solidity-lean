import Solidity.Lowering.V08.LiteralFailureSliceEncoding

/-! Actual nested bytes-calldata slicing and its standard encoding consumer.
Both range checks are the published slice evaluator; no semantics or input
admission is replaced by a desired reference or serialized packet. -/
namespace Solidity.Lowering.V08.LiteralFailureNestedSlice
open Solidity Source
abbrev context (Γ : RCtx) := SliceFailureLowering.context (.bytes .calldata)
 (.int IntTy.u256::.int IntTy.u256::Γ)
abbrev caller {E : Env} {Γ} (off len : Nat) (s e u v : Roadmap.Word)
 (older : Locals E.layout Γ) : Locals E.layout (context Γ) :=
 SliceFailureLowering.caller (τ:=.bytes .calldata) rfl off len s e
  (.cons (SourceEnvironment.sourceWord u) (.cons (SourceEnvironment.sourceWord v) older))
def expression {E : Env} {Γ} : RExpr E (context Γ) (.bytes .calldata) :=
 .slice (SliceFailureLowering.expression (.bytes .calldata) rfl false) rfl
  (.local (.there (.there (.there .here)))) rfl
  (.local (.there (.there (.there (.there .here))))) rfl false

theorem after_first {E : Env} {Γ} (G : Glob E) (F : Fr) (n off len : Nat)
 (s e u v : Roadmap.Word) (ordered : s.val≤e.val) (bounded : e.val≤len)
 (older : Locals E.layout Γ) (state : St E) :
 (evalE G F (n+3) expression).run (caller off len s e u v older,state)=
 ((match sliceR (.cdRef rfl (off+s.val) (e.val-s.val) : Source.Val E.layout (.bytes .calldata)) u.val v.val false with
   | .ok value => .ok (.val value) | .error error => .error error),
  (caller off len s e u v older,state)) := by
 have head := SliceFailureLowering.accepted G F n (.bytes .calldata) rfl rfl
  off len s e ordered bounded
  (.cons (SourceEnvironment.sourceWord u) (.cons (SourceEnvironment.sourceWord v) older)) state
 simp only [Nat.one_mul] at head
 simp only [expression]
 rw [evalE]
 dsimp only [ExceptT.run] at head
 simp only [bind,pure,ExceptT.bind,ExceptT.pure,ExceptT.bindCont,ExceptT.run,
  ExceptT.mk,StateT.bind]
 rw [head]
 simp only [evalE,caller,SliceFailureLowering.caller,EM.locals,getV,RVal.get,indexNat,
  RVal.amount,SourceEnvironment.sourceWord,Locals.get,EM.lift,
  bind,pure,ExceptT.bind,ExceptT.pure,ExceptT.bindCont,ExceptT.mk,
  StateT.bind,StateT.pure,StateT.get,get,getThe,MonadStateOf.get,liftM,monadLift,
  MonadLift.monadLift,ExceptT.lift,Functor.map,StateT.map,Except.pure,Int.toNat_natCast]
 cases h : sliceR (Source.Val.cdRef rfl (off+s.val) (e.val-s.val) : Source.Val E.layout (.bytes .calldata)) u.val v.val false <;> rfl

theorem accepted {E : Env} {Γ} (G : Glob E) (F : Fr) (n off len : Nat)
 (s e u v : Roadmap.Word) (ordered : s.val≤e.val) (bounded : e.val≤len)
 (ordered2 : u.val≤v.val) (bounded2 : v.val≤e.val-s.val)
 (older : Locals E.layout Γ) (state : St E) :
 (evalE G F (n+3) expression).run (caller off len s e u v older,state)=
 (.ok (.val (.cdRef rfl (off+s.val+u.val) (v.val-u.val))),
  (caller off len s e u v older,state)) := by
 rw [after_first G F n off len s e u v ordered bounded older state]
 simp only [sliceR,Bool.false_eq_true,↓reduceIte,Nat.one_mul,
  if_neg (Nat.not_lt.mpr ordered2),if_neg (Nat.not_lt.mpr bounded2)]
 rfl

theorem first_revert {E : Env} {Γ} (G : Glob E) (F : Fr) (n off len : Nat)
 (s e u v : Roadmap.Word) (wrong : e.val<s.val ∨ len<e.val)
 (older : Locals E.layout Γ) (state : St E) :
 (evalE G F (n+3) expression).run (caller off len s e u v older,state)=
 (.error (.revert []),(caller off len s e u v older,state)) := by
 have head := SliceFailureLowering.invalid G F n (.bytes .calldata) rfl rfl
  off len s e wrong
  (.cons (SourceEnvironment.sourceWord u) (.cons (SourceEnvironment.sourceWord v) older)) state
 simp only [expression]
 rw [evalE]
 dsimp only [ExceptT.run] at head
 simp only [bind,pure,ExceptT.bind,ExceptT.bindCont,ExceptT.run,ExceptT.mk,StateT.bind,StateT.pure,head]

theorem second_revert {E : Env} {Γ} (G : Glob E) (F : Fr) (n off len : Nat)
 (s e u v : Roadmap.Word) (ordered : s.val≤e.val) (bounded : e.val≤len)
 (wrong : v.val<u.val ∨ e.val-s.val<v.val)
 (older : Locals E.layout Γ) (state : St E) :
 (evalE G F (n+3) expression).run (caller off len s e u v older,state)=
 (.error (.revert []),(caller off len s e u v older,state)) := by
 rw [after_first G F n off len s e u v ordered bounded older state]
 rcases wrong with wrong | wrong
 · simp only [sliceR,Bool.false_eq_true,↓reduceIte,if_pos wrong]
 · by_cases h : v.val<u.val
   · simp only [sliceR,Bool.false_eq_true,↓reduceIte,if_pos h]
   · simp only [sliceR,Bool.false_eq_true,↓reduceIte,if_neg h,if_pos wrong]

/-- The flattened relative range remains inside the first range and a full
word. This does not bound the absolute calldata base or admit an entry. -/
theorem flattened_bounds (s e u v : Roadmap.Word) (first : s.val≤e.val)
 (second : u.val≤v.val) (inside : v.val≤e.val-s.val) :
 s.val+u.val≤s.val+v.val ∧ s.val+v.val≤e.val ∧ s.val+v.val<2^256 := by
 have bound := e.isLt
 omega

def arguments {E : Env} {Γ types} (tail : RArgs E (context Γ) types) :
 RArgs E (context Γ) (.bytes .calldata::types) := .cons expression tail

theorem arguments_run {E : Env} {Γ types} {tail : RArgs E (context Γ) types}
 {values : Source.Vals E.layout types} (G : Glob E) (F : Fr) (extra off len : Nat)
 (s e u v : Roadmap.Word) (ordered : s.val≤e.val) (bounded : e.val≤len)
 (ordered2 : u.val≤v.val) (bounded2 : v.val≤e.val-s.val)
 (older : Locals E.layout Γ) (state : St E)
 (lookups : LiteralFailureMixedExpression.LocalArgs (caller off len s e u v older) tail values) :
 (evalArgs G F (types.length+extra+4) (arguments tail)).run (caller off len s e u v older,state)=
 (.ok (.cons (.val (.cdRef rfl (off+s.val+u.val) (v.val-u.val))) values.toR),
  (caller off len s e u v older,state)) := by
 have head := accepted G F (types.length+extra) off len s e u v ordered bounded ordered2 bounded2 older state
 have tailRun := LiteralFailureMixedExpression.arguments_run G F extra (caller off len s e u v older) state lookups
 simp only [arguments]
 rw [evalArgs]
 dsimp only [ExceptT.run] at head tailRun
 simp only [bind,pure,ExceptT.bind,ExceptT.pure,ExceptT.bindCont,ExceptT.run,ExceptT.mk,StateT.bind]
 rw [head]
 simp only [bind,pure,ExceptT.bindCont,StateT.bind]
 rw [tailRun]
 rfl

theorem encode_run {E : Env} {Γ types shapes} {tail : RArgs E (context Γ) types}
 {values : Source.Vals E.layout types} {encoded : AbiEntry.Vals shapes} {parts}
 (G : Glob E) (F : Fr) (extra off len : Nat) (s e u v : Roadmap.Word)
 (ordered : s.val≤e.val) (bounded : e.val≤len) (ordered2 : u.val≤v.val) (bounded2 : v.val≤e.val-s.val)
 (older : Locals E.layout Γ) (state : St E)
 (lookups : LiteralFailureMixedExpression.LocalArgs (caller off len s e u v older) tail values)
 (located : LiteralFailureCalldataPrefix.Located F state values encoded parts) :
 (evalE G F (types.length+extra+5) (.abiEncode .encode (arguments tail))).run (caller off len s e u v older,state)=
 (.ok (.val (.memRef rfl state.heap.next)),
  (caller off len s e u v older,SourceKeccak.afterLiteral state
   (AbiEntry.encodeArgs (.cons (.bytes ((F.cd.drop (off+s.val+u.val)).take (v.val-u.val))) encoded)))) :=
 SourceAbi.execute G F (types.length+extra+4) false (arguments tail) _ _ _ state state state _ _
 (arguments_run G F extra off len s e u v ordered bounded ordered2 bounded2 older state lookups)
 (LiteralFailureCalldataPrefix.encoding_run F _ _ state (.bytes (off+s.val+u.val) (v.val-u.val) located))

theorem encode_revert {E : Env} {Γ types} (G : Glob E) (F : Fr) (extra off len : Nat)
 (s e u v : Roadmap.Word)
 (wrong : (e.val<s.val ∨ len<e.val) ∨ (v.val<u.val ∨ e.val-s.val<v.val))
 (older : Locals E.layout Γ) (state : St E) (tail : RArgs E (context Γ) types) :
 (evalE G F (types.length+extra+5) (.abiEncode .encode (arguments tail))).run (caller off len s e u v older,state)=
 (.error (.revert []),(caller off len s e u v older,state)) := by
 have head : (evalE G F (types.length+extra+3) expression).run (caller off len s e u v older,state)=
  (.error (.revert []),(caller off len s e u v older,state)) := by
  by_cases first : e.val<s.val ∨ len<e.val
  · exact first_revert G F (types.length+extra) off len s e u v first older state
  · exact second_revert G F (types.length+extra) off len s e u v (by omega) (by omega) (wrong.resolve_left first) older state
 have args : (evalArgs G F (types.length+extra+4) (arguments tail)).run (caller off len s e u v older,state)=
  (.error (.revert []),(caller off len s e u v older,state)) := by
  simp only [arguments]
  rw [evalArgs]
  dsimp only [ExceptT.run] at head
  simp only [bind,pure,ExceptT.bind,ExceptT.bindCont,ExceptT.run,ExceptT.mk,StateT.bind,StateT.pure,head]
 dsimp only [ExceptT.run] at args
 simp only [evalE,bind,pure,ExceptT.bind,ExceptT.bindCont,ExceptT.run,ExceptT.mk,StateT.bind,StateT.pure,args]

end Solidity.Lowering.V08.LiteralFailureNestedSlice
