import Solidity.Lowering.V07.LocationProducerControls
import Solidity.Lowering.V07.LocationGraphLaws
import Solidity.Lowering.V07.RecursiveGraphControls
import Solidity.Lowering.V07.WrappedPairControls
import Solidity.Lowering.V07.UnsignedNarrowingControls
import Solidity.Lowering.V07.GraphAdmissionBoundary
import Solidity.Lowering.V07.ShortCircuitControls
import Solidity.Lowering.V07.AllAliasControls
import Solidity.Lowering.V07.PrimitiveGraphControls
import Solidity.Lowering.V07.DoubleNegativeControls
import Solidity.Lowering.V07.ReferenceControls
import Solidity.Lowering.V07.ConditionLoopControl
import Solidity.Lowering.V07.AssignmentBoundaries
import Solidity.Lowering.V07.LocalFamilyControls

/-! Bounded executable observations of actual runs, supplementary to the
unbounded kernel theorems. No external solc/EVM test or source completeness. -/
namespace Solidity.Lowering.V07.EffectFixtures
open Source.SemanticsExamples

def pairValues (p : Roadmap.Pipeline) : List (Option Int) :=
  let result := (Source.evalPair (G0 p) F0 3
    (.assign (.local (.there .here)) (.local .here)) (.local (.there .here))).run ReadControls.source
  match result with
  | (.ok (.val left,.val right),state) =>
    [left.key,right.key,(state.1.get .here).key,(state.1.get (.there .here)).key]
  | _ => []

def prefixValues (p : Roadmap.Pipeline) : List (Option Int) :=
  match (assignReadPrefix p (.there .here) .here).run ReadControls.target with
  | .ok out =>
    [PrimTy.num? (TEnv.get .here out.st.env),
     PrimTy.num? (TEnv.get (.there .here) out.st.env),
     PrimTy.num? (TEnv.get (.there (.there .here)) out.st.env),
     PrimTy.num? (TEnv.get (.there (.there (.there .here))) out.st.env)]
  | .error _ => []

def finalValues (p : Roadmap.Pipeline) : List (Option Int) :=
  [intOf ((Source.evalE (G0 p) F0 4 AssignmentControls.expression).run ReadControls.source),
   AssignmentControls.observed ((assignReadSubOperand p .u8 (.there .here) .here).run ReadControls.target)]

def uncheckedFinal (p : Roadmap.Pipeline) : List (Option Int) :=
  [intOf ((Source.evalE (G0 p) {F0 with checked := false} 4 AssignmentControls.expression).run ReadControls.source),
   AssignmentControls.observed ((assignReadSubOperand p .u8 (.there .here) .here).run ReadControls.target)]

def mixedReferences : List (Option Int) :=
  match (assignReadSubOperand .legacy .u8 (.there .here) .here).run MixedAssignmentControls.target with
  | .error _ => []
  | .ok (out,_) =>
    match TEnv.get (.there (.there .here)) out.st.env,
        TEnv.get (.there (.there (.there .here))) out.st.env with
    | some memory,some storage => [some memory.id,some (out.st.heap.len memory .dyn),
        if storage.root = "live" then some 1 else none]
    | _,_ => []

def signedActual (p : Roadmap.Pipeline) : List (Option Int) :=
  [intOf ((Source.evalE (G0 p) F0 4
      (.binary .sub (.assign (.local (.there .here)) (.local .here)) (.local (.there .here)))).run
      AssignmentBoundaries.signedSource),
   AssignmentControls.observed ((assignReadSubOperand p Controls.i8 (.there .here) .here).run
      AssignmentBoundaries.signedTarget)]

def prefixActual (n : Nat) (key : LocalFamilyControls.Keys) : List (Option Int) :=
  let source := (Source.evalE (G0 .legacy) F0 2
    (.assign (.local (LocalFamilyControls.si (LocalFamilyControls.written n)))
      (.local (LocalFamilyControls.si (LocalFamilyControls.rhs n))))).run
    (sourceIntegerPrefixes LocalFamilyControls.si LocalFamilyControls.written LocalFamilyControls.rhs
      LocalFamilyControls.source.1 n,LocalFamilyControls.source.2)
  let target := (assignLocalOperand (LocalFamilyControls.ti (LocalFamilyControls.written n))
    (LocalFamilyControls.ti (LocalFamilyControls.rhs n))).run
    (LocalFamilyControls.target.withEnv (targetIntegerPrefixes LocalFamilyControls.ti
      LocalFamilyControls.written LocalFamilyControls.rhs LocalFamilyControls.target.env n))
  match source,target with
  | (.ok _,state),.ok (out,_) =>
    [(state.1.get (LocalFamilyControls.si key)).key,PrimTy.num? (TEnv.get (LocalFamilyControls.ti key) out.st.env)]
  | _,_ => []


def doublePairValues (p : Roadmap.Pipeline) : List (Option Int) :=
  match (Source.evalPair (G0 p) F0 3
    (.assign (.local .here) (.local (.there .here)))
    (.assign (.local (.there .here)) (.local (.there (.there .here))))).run DoubleControls.source with
  | (.ok (.val left,.val right),state) =>
    [left.key,right.key,(state.1.get .here).key,(state.1.get (.there .here)).key,
      (state.1.get (.there (.there .here))).key]
  | _ => []

def doublePrefixValues (p : Roadmap.Pipeline) (physical : Bool := false) : List (Option Int) :=
  match (assignAssignPrefix p .here (.there .here) (.there (.there .here))).run DoubleControls.target with
  | .ok out =>
    let first := PrimTy.num? (TEnv.get .here out.st.env)
    let second := PrimTy.num? (TEnv.get (.there .here) out.st.env)
    [(if physical || p == .legacy then first else second),
      (if physical || p == .legacy then second else first),
      PrimTy.num? (TEnv.get (.there (.there .here)) out.st.env),
      PrimTy.num? (TEnv.get (.there (.there (.there .here))) out.st.env),
      PrimTy.num? (TEnv.get (.there (.there (.there (.there .here)))) out.st.env)]
  | .error _ => []

def doubleFinalValues (p : Roadmap.Pipeline) (checked : Bool := true) : List (Option Int) :=
  [intOf ((Source.evalE (G0 p) {F0 with checked := checked} 4 DoubleControls.expression).run DoubleControls.source),
    AssignmentControls.observed ((assignAssignSubOperand p .u8 .here (.there .here) (.there (.there .here))).run DoubleControls.target)]

def aliasFinalValues (p : Roadmap.Pipeline) : List (Option Int) :=
  [intOf ((Source.evalE (G0 p) F0 4 DoubleNegativeControls.aliasExpression).run ReadControls.source),
    AssignmentControls.observed ((assignAssignSubOperand p .u8 .here .here (.there .here)).run ReadControls.target)]

def doubleSignedValues (p : Roadmap.Pipeline) : List (Option Int) :=
  [intOf ((Source.evalE (G0 p) F0 4
    (.binary .sub (.assign (.local .here) (.local .here))
      (.assign (.local .here) (.local (.there .here))))).run AssignmentBoundaries.signedSource),
    AssignmentControls.observed ((assignAssignSubOperand p Controls.i8 .here .here (.there .here)).run AssignmentBoundaries.signedTarget)]

def sourceAddress (v : Source.Val E0.layout (.bytes .memory)) : Option Int :=
  match v with | .memRef _ address => some address | _ => none

def referenceSourceValues (p : Roadmap.Pipeline) : List (Option Int) :=
  match (Source.evalPair (G0 p) F0 3
    (.assign (.local (.there .here)) (.local .here)) (.local (.there .here))).run ReferenceControls.source with
  | (.ok (.val left,.val right),state) =>
    [sourceAddress left,sourceAddress right,sourceAddress (state.1.get .here),
      sourceAddress (state.1.get (.there .here))]
  | _ => []

def referenceTargetValues (p : Roadmap.Pipeline) : List (Option Int) :=
  match (memoryAssignReadPrefix p (.there .here) .here rfl).run ReferenceControls.target with
  | .ok out =>
    [(TEnv.get .here out.st.env).map (fun r => (r.id : Int)),
      (TEnv.get (.there .here) out.st.env).map (fun r => (r.id : Int)),
      (TEnv.get (.there (.there .here)) out.st.env).map (fun r => (r.id : Int)),
      (TEnv.get (.there (.there (.there .here))) out.st.env).map (fun r => (r.id : Int))]
  | .error _ => []

def snapshotLength (result : TRes (SVal (.ref bytesR))) : Option Int :=
  match result with | .ok value => some (value.view.n : Int) | .error _ => none

def boolNumber (b : Bool) : Option Int := some (if b then 1 else 0)
def boolResult (r : TRes Bool) : Option Int := match r with | .ok b => boolNumber b | .error _ => none

def conditionSource : List (Option Int) :=
  match (Source.evalE (MixedAssignmentControls.globals .legacy) F0 2
    (.assign (.local .here) (.local (.there .here)))).run P12Controls.source with
  | (.ok (.val value),state) => [value.key,(state.1.get .here).key,(state.1.get (.there .here)).key]
  | _ => []

def conditionTarget : List (Option Int) :=
  match (assignLocalOperand (.here : Idx P12Controls.TgtCtx (.val .bool)) (.there .here)).code.run P12Controls.target with
  | .ok out =>
    match TEnv.get (.there (.there (.there (.there (.there .here))))) out.st.env,
      TEnv.get (.there (.there (.there (.there (.there (.there .here)))))) out.st.env with
    | some memory,some storage =>
      [boolNumber (TEnv.get .here out.st.env),boolNumber (TEnv.get (.there .here) out.st.env),
        boolNumber (TEnv.get (.there (.there .here)) out.st.env),some memory.id,
        some (out.st.heap.len memory .dyn),if storage.root = "live" then some 1 else none]
    | _,_ => []
  | .error _ => []

def capturedMemory : List (Option Int) :=
  match (memoryCapture (.there (.there (.there (.there .here)))) rfl).run P12Controls.target with
  | .ok out =>
    match (MPath.var .here rfl : MPath P12Controls.C (.mem bytesR :: P12Controls.TgtCtx) (.ref bytesR)).mvalT out.st with
    | .ok r => [some r.id,some (out.st.heap.len r .dyn)]
    | .error _ => []
  | .error _ => []

def capturedStorage : List (Option Int) :=
  match (storageCapture (.there (.there (.there (.there (.there .here)))))).run P12Controls.target with
  | .ok out =>
    match (SPath.alias .here : SPath P12Controls.C (.alias bytesR :: P12Controls.TgtCtx) (.ref bytesR)).resolveT out.st with
    | .ok r => [if r.root = "live" then some 1 else none]
    | .error _ => []
  | .error _ => []

def loopPrefixChoice (n : Nat) : Option Int :=
  match TLoop.iterN ConditionLoopControl.body ConditionLoopControl.condition n ConditionLoopControl.before with
  | .inl state => boolNumber (TEnv.get .here state.env)
  | .inr _ => none

def aliasPairValues (p : Roadmap.Pipeline) : List (Option Int) :=
  match (Source.evalPair (MixedAssignmentControls.globals p) F0 3
    (.assign (.local (.there .here)) (.local .here))
    (.assign (.local .here) (.local (.there .here)))).run MixedAssignmentControls.source with
  | (.ok (.val left,.val right),state) =>
    [left.key,right.key,(state.1.get .here).key,(state.1.get (.there .here)).key]
  | _ => []

def aliasPrefixValues (p : Roadmap.Pipeline) : List (Option Int) :=
  match (assignAssignPrefix p (.there .here) .here (.there .here)).run MixedAssignmentControls.target with
  | .ok out =>
    [PrimTy.num? (TEnv.get .here out.st.env),
     PrimTy.num? (TEnv.get (.there .here) out.st.env),
     PrimTy.num? (TEnv.get (.there (.there .here)) out.st.env),
     PrimTy.num? (TEnv.get (.there (.there (.there .here))) out.st.env),
     match TEnv.get (.there (.there (.there (.there .here)))) out.st.env with
       | some r => some (Int.ofNat (out.st.heap.len r .dyn))
       | none => none,
     some (if (TEnv.get (.there (.there (.there (.there (.there .here))))) out.st.env).isSome then 1 else 0)]
  | .error _ => []

def rhsAliasedFinalValues (p : Roadmap.Pipeline) (checked : Bool) : List (Option Int) :=
  [intOf ((Source.evalE (MixedAssignmentControls.globals p) {F0 with checked := checked} 4
    AllAliasControls.expression).run MixedAssignmentControls.source),
   AssignmentControls.observed ((assignAssignSubOperand p .u8 (.there .here) .here (.there .here)).run
     MixedAssignmentControls.target)]

def aliasSignedValues (p : Roadmap.Pipeline) : List (Option Int) :=
  [intOf ((Source.evalE (G0 p) F0 4
    (.binary .sub (.assign (.local (.there .here)) (.local .here))
      (.assign (.local .here) (.local (.there .here))))).run AllAliasControls.signedSource),
   AssignmentControls.observed ((assignAssignSubOperand p Controls.i8 (.there .here) .here (.there .here)).run
     AllAliasControls.signedTarget)]

def scSourceValues (p : Roadmap.Pipeline) (conj : Bool)
    (i a j b : Source.Idx P12Controls.SrcCtx .bool) : List (Option Int) :=
  let left := (Source.evalE (MixedAssignmentControls.globals p) F0 2
    (.assign (.local i) (.local a))).run P12Controls.source
  let final := (Source.evalE (MixedAssignmentControls.globals p) F0 3
    (.binary (if conj then .and else .or) (.assign (.local i) (.local a))
      (.assign (.local j) (.local b)))).run P12Controls.source
  match left,final with
  | (.ok (.val v),mid),(.ok (.val result),out) =>
    [v.key,(mid.1.get .here).key,(mid.1.get b).key,result.key,
      (out.1.get .here).key,(out.1.get (.there .here)).key]
  | _,_ => []

def scTargetValues (conj : Bool) (i a j b : Idx P12Controls.TgtCtx (.val .bool)) : List (Option Int) :=
  match (shortAssignPrefix conj i a j b).run P12Controls.target with
  | .ok out =>
    [some (if boolT (TEnv.get .here out.st.env) then 1 else 0),
      some (if boolT (TEnv.get (.there .here) out.st.env) then 1 else 0),
      some (if boolT (TEnv.get (.there (.there .here)) out.st.env) then 1 else 0),
      match TEnv.get (.there (.there (.there (.there (.there .here))))) out.st.env with
        | some r => some (Int.ofNat (out.st.heap.len r .dyn))
        | none => none,
      some (if (TEnv.get (.there (.there (.there (.there (.there (.there .here)))))) out.st.env).isSome then 1 else 0)]
  | .error _ => []

def scFailureSource (p : Roadmap.Pipeline) : List (Option Int) :=
  [some (if revertOf ((Source.evalE (MixedAssignmentControls.globals p) F0 10
      ShortCircuitControls.failure).run P12Controls.source) == some (Source.panicData .divZero) then 1 else 0),
   (match (Source.evalE (MixedAssignmentControls.globals p) F0 3
      (.binary .and (.assign (.local .here) (.local .here)) ShortCircuitControls.failure)).run P12Controls.source with
     | (.ok (.val v),_) => v.key
     | _ => none),
   some (if revertOf ((Source.evalE (MixedAssignmentControls.globals p) F0 12
      (.binary .or (.assign (.local .here) (.local .here)) ShortCircuitControls.failure)).run P12Controls.source) ==
        some (Source.panicData .divZero) then 1 else 0)]

def scFailureTarget (v : Bool) : Option Int :=
  match (Stmt.ite (.simple (.local .here)) ShortCircuitControls.failingBranch
      (Prog.nil : Prog P12Controls.C (.val .bool :: P12Controls.TgtCtx) (.val .bool :: P12Controls.TgtCtx))).run
      (P12Controls.target.push (t := .val .bool) v) with
  | .ok _ => some 0
  | .error .revert => some 1
  | .error _ => none

def graphMetadata (u : Source.Syn .unit) (p : Roadmap.Pipeline) : List (Option Int) :=
  let r := Source.resolveUnit ⟨p,[]⟩ u
  [some (if Frontend.Static.metadataChecker.check r () () then 1 else 0),
   some (if Frontend.Static.strictMetadataChecker.check r () () then 1 else 0)]

def graphBoundaryShape (guarded : Bool) (loc : Source.DataLoc) : Option Int :=
  let env := if guarded then GraphAdmissionBoundary.guardedEnv else GraphAdmissionBoundary.directEnv
  match env.structFields GraphAdmissionBoundary.loopName loc with
  | some [(_, .struct _ _)] => some 0
  | some [(_, .array _ (.struct _ _) none)] => some 1
  | _ => none

def unsignedValue (r : TRes PrimTy.uint.Denote) : Option Int :=
  match r with | .ok v => some v.val | .error _ => none

def unsignedPureValues (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256)
    (p : Roadmap.Pipeline) : List (Option Int) :=
  [intOf ((Source.evalE (G0 p) {F0 with checked := false} 3
      (.binary .sub (.local .here) (.local (.there .here)))).run
        (UnsignedNarrowingControls.pureSource bits valid)),
   unsignedValue ((UnsignedNarrowing.subValue bits (.simple (.local .here))
      (.simple (.local (.there .here)))).evalT (UnsignedNarrowingControls.pureTarget bits valid))]

def unsignedEffectPair (p : Roadmap.Pipeline) : List (Option Int) :=
  match (Source.evalPair (MixedAssignmentControls.globals p) {F0 with checked := false} 3
      (.assign (.local (.there .here)) (.local .here)) (.local (.there .here))).run
      UnsignedNarrowingControls.source with
  | (.ok (.val l,.val r),out) => [l.key,r.key,(out.1.get .here).key,(out.1.get (.there .here)).key]
  | _ => []

def unsignedEffectPrefix (p : Roadmap.Pipeline) : List (Option Int) :=
  match (assignReadPrefix p (.there .here) .here).run UnsignedNarrowingControls.target with
  | .ok out => [PrimTy.num? (TEnv.get .here out.st.env),
      PrimTy.num? (TEnv.get (.there .here) out.st.env),
      PrimTy.num? (TEnv.get (.there (.there .here)) out.st.env),
      PrimTy.num? (TEnv.get (.there (.there (.there .here))) out.st.env),
      match TEnv.get (.there (.there (.there (.there .here)))) out.st.env with
        | some r => some (Int.ofNat (out.st.heap.len r .dyn))
        | none => none,
      some (if (TEnv.get (.there (.there (.there (.there (.there .here))))) out.st.env).isSome then 1 else 0)]
  | .error _ => []

def unsignedEffectFinal (p : Roadmap.Pipeline) : List (Option Int) :=
  [intOf ((Source.evalE (MixedAssignmentControls.globals p) {F0 with checked := false} 4
      (.binary .sub (.assign (.local (.there .here)) (.local .here)) (.local (.there .here)))).run
        UnsignedNarrowingControls.source),
   AssignmentControls.observed ((UnsignedNarrowing.assignReadOperand p 8 (.there .here) .here).run
      UnsignedNarrowingControls.target)]

def wrappedPairSource (p : Roadmap.Pipeline) : List (Option Int) :=
  match (Source.evalPair (MixedAssignmentControls.globals p) {F0 with checked := false} 3
      (.assign (.local .here) (.local .here))
      (.assign (.local .here) (.local (.there .here)))).run WrappedPairControls.U with
  | (.ok (.val l,.val r),out) => [l.key,r.key,(out.1.get .here).key,(out.1.get (.there .here)).key]
  | _ => []

def wrappedPairPrefix (p : Roadmap.Pipeline) (physical : Bool := false) : List (Option Int) :=
  match (assignAssignPrefix p .here .here (.there .here)).run WrappedPairControls.T with
  | .ok out =>
    let head := PrimTy.num? (TEnv.get .here out.st.env)
    let second := PrimTy.num? (TEnv.get (.there .here) out.st.env)
    let lr := if physical || p = .legacy then [head,second] else [second,head]
    lr ++ [PrimTy.num? (TEnv.get (.there (.there .here)) out.st.env),
      PrimTy.num? (TEnv.get (.there (.there (.there .here))) out.st.env),
      match TEnv.get (.there (.there (.there (.there .here)))) out.st.env with
        | some r => some (Int.ofNat (out.st.heap.len r .dyn))
        | none => none,
      some (if (TEnv.get (.there (.there (.there (.there (.there .here))))) out.st.env).isSome then 1 else 0)]
  | _ => []

def wrappedPairFinal (p : Roadmap.Pipeline) : List (Option Int) :=
  [intOf ((Source.evalE (MixedAssignmentControls.globals p) {F0 with checked := false} 4
      WrappedPairControls.expression).run WrappedPairControls.U),
   AssignmentControls.observed ((WrappedAssignmentPair.operand p 8 .here .here (.there .here)).run WrappedPairControls.T)]

def wrappedRhsFinal (p : Roadmap.Pipeline) : List (Option Int) :=
  let sr := (Source.evalE (MixedAssignmentControls.globals p) {F0 with checked := false} 4
    (.binary .sub (.assign (.local (.there .here)) (.local .here))
      (.assign (.local .here) (.local (.there .here))))).run WrappedPairControls.U
  match sr,(WrappedAssignmentPair.operand p 8 (.there .here) .here (.there .here)).run WrappedPairControls.T with
  | (.ok (.val v),ss),.ok (tt,w) =>
    [v.key,match w with | .prim z => PrimTy.num? z,
      (ss.1.get .here).key,(ss.1.get (.there .here)).key,
      PrimTy.num? (TEnv.get .here tt.st.env),PrimTy.num? (TEnv.get (.there .here) tt.st.env)]
  | _,_ => []

def wrappedTripleFinal (p : Roadmap.Pipeline) : List (Option Int) :=
  [intOf ((Source.evalE (MixedAssignmentControls.globals p) {F0 with checked := false} 4
      WrappedPairControls.tripleExpression).run WrappedPairControls.tripleSource),
   AssignmentControls.observed ((WrappedAssignmentPair.operand p 8 .here (.there .here)
      (.there (.there .here))).run WrappedPairControls.tripleTarget)]

def wrappedTripleCaller (p : Roadmap.Pipeline) : List (Option Int) :=
  match (Source.evalE (MixedAssignmentControls.globals p) {F0 with checked := false} 4
      WrappedPairControls.tripleExpression).run WrappedPairControls.tripleSource,
      (WrappedAssignmentPair.operand p 8 .here (.there .here) (.there (.there .here))).run WrappedPairControls.tripleTarget with
  | (.ok _,ss),.ok (tt,_) => [(ss.1.get .here).key,(ss.1.get (.there .here)).key,
      (ss.1.get (.there (.there .here))).key,PrimTy.num? (TEnv.get .here tt.st.env),
      PrimTy.num? (TEnv.get (.there .here) tt.st.env),PrimTy.num? (TEnv.get (.there (.there .here)) tt.st.env),
      match TEnv.get (.there (.there (.there .here))) tt.st.env with
        | some r => some (Int.ofNat (tt.st.heap.len r .dyn))
        | none => none,
      some (if (TEnv.get (.there (.there (.there (.there .here)))) tt.st.env).isSome then 1 else 0)]
  | _,_ => []

def wrappedPairWidth (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256)
    (p : Roadmap.Pipeline) : List (Option Int) :=
  [intOf ((Source.evalE (G0 p) {F0 with checked := false} 4
    (.binary .sub (.assign (.local .here) (.local .here))
      (.assign (.local .here) (.local (.there .here))))).run (UnsignedNarrowingControls.pureSource bits valid)),
   AssignmentControls.observed ((WrappedAssignmentPair.operand p bits .here .here (.there .here)).run
      (UnsignedNarrowingControls.pureTarget bits valid))]

def recursiveGraphIds (E : Source.Env) (loc : Source.DataLoc) : List (Option Int) :=
  match RecursiveGraph.produce "ordered-graph-fixtures" E loc with
  | none => []
  | some result => some (Int.ofNat (PrimitiveGraph.nodes E).length) ::
      ((List.finRange (PrimitiveGraph.nodes E).length).map fun i => some (Int.ofNat (result.1.declId i)))

def recursiveGraphRanks (E : Source.Env) (loc : Source.DataLoc) : List (Option Int) :=
  match RecursiveGraph.produce "ordered-graph-fixtures" E loc with
  | none => []
  | some result => (List.finRange (PrimitiveGraph.nodes E).length).map fun i => some (Int.ofNat (result.1.rank i))

def recursiveGraphSuccess (E : Source.Env) (loc : Source.DataLoc) : Option Int :=
  some (if (RecursiveGraph.produce "ordered-graph-fixtures" E loc).isSome then 1 else 0)

def recursiveGraphAllLocations (E : Source.Env) : List (Option Int) :=
  [recursiveGraphSuccess E .storage,recursiveGraphSuccess E .memory,recursiveGraphSuccess E .calldata]

def recursiveChainEdges : List (Option Int) :=
  match RecursiveGraph.produce "ordered-chain-edges" RecursiveGraphControls.chain .storage with
  | none => []
  | some result => (List.finRange (PrimitiveGraph.nodes RecursiveGraphControls.chain).length).map fun i =>
      match (result.1.fields i).head? with
      | some (_, .node j) => some (Int.ofNat j.val)
      | _ => none

def recursiveEnumFields : List (Option Int) :=
  [some (if RecursiveGraph.targetFields RecursiveGraphControls.wrappedEnv .storage ⟨0,by decide⟩ = [("choice",.prim .uint),("distance",.prim .uint)] then 1 else 0)]

def h15Allowed (E : Source.Env) (dn : Source.DeclName) (loc : Source.DataLoc) : Option Int :=
  some (if LocationGraphInterface.StructAdmissible E dn loc then 1 else 0)

def h15MappingType : Source.Syn .typeName :=
  .mapping (.elem (.int false 8 (by decide)) (by decide)) none (.userType ⟨"Loop",[]⟩) none

def h15MemoryFields : Option Int :=
  some (if LocationGraphLaws.memorySchema.fields ⟨0,by decide⟩ = [("value",.prim .uint)] then 1 else 0)

def h15StorageFields : Option Int :=
  some (if LocationGraphLaws.storageResult.1.fields ⟨0,by decide⟩ =
    [("next",.mapping .uint (.node ⟨0,by decide⟩))] then 1 else 0)

def h15TypedDeclaration : Option Int :=
  match LocationGraphLaws.typed_local .body with
  | .declVar _ _ => some 1

def locationProducedIds (E : Source.Env) (loc : Source.DataLoc) : List (Option Int) :=
  match LocationGraphProducer.produce "ordered-location-producer" E loc with
  | none => []
  | some result => (List.finRange (LocationGraphProducer.choices E loc).length).map fun i =>
      some (Int.ofNat (result.1.declId i))

def locationProducedRanks (E : Source.Env) (loc : Source.DataLoc) : List (Option Int) :=
  match LocationGraphProducer.produce "ordered-location-producer" E loc with
  | none => []
  | some result => (List.finRange (LocationGraphProducer.choices E loc).length).map fun i =>
      some (Int.ofNat (result.1.rank i))

def locationProducedShape (E : Source.Env) (loc : Source.DataLoc) : List (Option Int) :=
  [some (if (LocationGraphProducer.produce "ordered-location-producer" E loc).isSome then 1 else 0),
   some (Int.ofNat (LocationGraphProducer.choices E loc).length)]

def locationMemoryFields : Option Int :=
  some (if LocationProducerControls.memoryResult.1.fields ⟨0,by decide⟩ = [("value",.prim .uint)] then 1 else 0)

def locationStorageFields : Option Int :=
  some (if LocationProducerControls.storageResult.1.fields ⟨0,by decide⟩ =
    [("next",.mapping .uint (.node ⟨0,by decide⟩))] then 1 else 0)

def locationTransitiveFields : Option Int :=
  some (if LocationProducerControls.transitiveStorageResult.1.fields ⟨1,by decide⟩ =
    [("nested",.array (.array (.node ⟨0,by decide⟩)))] then 1 else 0)

def rows : List (String × List (Option Int)) :=
  [("legacy.source-pair-and-caller",pairValues .legacy),
   ("legacy.target-captures-and-caller",prefixValues .legacy),
   ("legacy.source-target-final",finalValues .legacy),
   ("viaIR.source-pair-and-caller",pairValues .viaIR),
   ("viaIR.target-captures-and-caller",prefixValues .viaIR),
   ("viaIR.source-target-final",finalValues .viaIR),
   ("unchecked.legacy-source-target",uncheckedFinal .legacy),
   ("unchecked.viaIR-source-target",uncheckedFinal .viaIR),
   ("mixed.live-memory-and-storage",mixedReferences),
   ("bad.uncaptured-target",[AssignmentControls.observed (AssignmentControls.uncaptured.run ReadControls.target)]),
   ("prefix1.repeated-alias",[((sourceIntegerPrefixes LocalFamilyControls.si LocalFamilyControls.written
      LocalFamilyControls.rhs LocalFamilyControls.source.1 1).get (LocalFamilyControls.si (true,true))).key]),
   ("prefix2.reached-copy",[((sourceIntegerPrefixes LocalFamilyControls.si LocalFamilyControls.written
      LocalFamilyControls.rhs LocalFamilyControls.source.1 2).get (LocalFamilyControls.si (false,false))).key]),
   ("prefix3.repeated-alias",[((sourceIntegerPrefixes LocalFamilyControls.si LocalFamilyControls.written
      LocalFamilyControls.rhs LocalFamilyControls.source.1 3).get (LocalFamilyControls.si (true,true))).key]),
   ("signed.legacy-viaIR",[some (AssignmentBoundaries.delta .legacy),some (AssignmentBoundaries.delta .viaIR)]),
   ("signed.actual-legacy-source-target",signedActual .legacy),
   ("signed.actual-viaIR-source-target",signedActual .viaIR),
   ("prefix1.actual-source-target",prefixActual 0 (true,true)),
   ("prefix2.actual-source-target",prefixActual 1 (false,false)),
   ("prefix3.actual-source-target",prefixActual 2 (true,true)),
   ("double.legacy.source-pair-caller",doublePairValues .legacy),
   ("double.legacy.target-semantic-captures-caller",doublePrefixValues .legacy),
   ("double.legacy.actual-final",doubleFinalValues .legacy),
   ("double.viaIR.source-pair-caller",doublePairValues .viaIR),
   ("double.viaIR.target-semantic-captures-caller",doublePrefixValues .viaIR),
   ("double.viaIR.target-physical-captures-caller",doublePrefixValues .viaIR true),
   ("double.viaIR.actual-final",doubleFinalValues .viaIR),
   ("double.unchecked.legacy",doubleFinalValues .legacy false),
   ("double.unchecked.viaIR",doubleFinalValues .viaIR false),
   ("double.shared-destination.legacy",aliasFinalValues .legacy),
   ("double.shared-destination.viaIR",aliasFinalValues .viaIR),
   ("double.bad-uncaptured",[AssignmentControls.observed (DoubleNegativeControls.uncaptured.run ReadControls.target)]),
   ("double.aliasing-rhs.actual",[intOf ((Source.evalE (G0 .viaIR) F0 4 DoubleNegativeControls.rhsAliasExpression).run ReadControls.source),AssignmentControls.observed ((assignAssignSubOperand .viaIR .u8 (.there .here) .here (.there .here)).run ReadControls.target)]),
   ("double.signed.legacy",doubleSignedValues .legacy),
   ("double.signed.viaIR",doubleSignedValues .viaIR),
   ("reference.legacy.internal-source-pointers-caller",referenceSourceValues .legacy),
   ("reference.legacy.internal-target-pointers-caller",referenceTargetValues .legacy),
   ("reference.viaIR.internal-source-pointers-caller",referenceSourceValues .viaIR),
   ("reference.viaIR.internal-target-pointers-caller",referenceTargetValues .viaIR),
   ("reference.old-capture-versus-late-snapshot-length",[snapshotLength ReferenceControls.capturedSnapshot,snapshotLength ReferenceControls.lateSnapshot]),
   ("p12.condition.actual-source-value-caller",conditionSource),
   ("p12.condition.target-capture-caller-live-refs",conditionTarget),
   ("p12.memory.actual-captured-reference",capturedMemory),
   ("p12.storage.actual-captured-root",capturedStorage),
   ("loop.once-captured-versus-refreshed",[boolResult (ConditionLoopControl.condition ConditionLoopControl.after),boolResult ((.simple (.local .here) : Val ConditionLoopControl.C (.val .bool :: ConditionLoopControl.CapturedCtx) .bool).evalT ((ConditionLoopControl.after.setLocal (.there (.there .here)) false).push (t := .val .bool) false))]),
   ("loop.intrinsic-prefix1-prefix2-stale-choice",[loopPrefixChoice 1,loopPrefixChoice 2]),
   ("graph.actual-selected-positions",[some (Int.ofNat (PrimitiveGraph.nodes PrimitiveGraphControls.env).length),
     some (Int.ofNat (PrimitiveGraph.index PrimitiveGraphControls.env ⟨0,by decide⟩).val),
     some (Int.ofNat (PrimitiveGraph.index PrimitiveGraphControls.env ⟨1,by decide⟩).val)]),
   ("graph.computed-memory-storage-success",[
     some (if (PrimitiveGraph.produce "fixture" PrimitiveGraphControls.env .memory).isSome then 1 else 0),
     some (if (PrimitiveGraph.produce "fixture" PrimitiveGraphControls.env .storage).isSome then 1 else 0)]),
   ("graph.scoped-same-name-success",[
     some (if (PrimitiveGraph.produce "fixture" PrimitiveGraphControls.scopedEnv .storage).isSome then 1 else 0)]),
   ("graph.duplicate-identity-and-field-rejection",[
     some (if (PrimitiveGraph.produce "fixture" PrimitiveGraphControls.duplicated .storage).isNone then 1 else 0),
     some (if (PrimitiveGraph.produce "fixture" PrimitiveGraphControls.repeatedEnv .storage).isNone then 1 else 0)]),
   ("graph.resolved-bytes-component-open",[
     some (if (PrimitiveGraph.produce "fixture" PrimitiveGraphControls.byteEnv .memory).isNone then 1 else 0)]),
   ("graph.signed-payable-bool-success",[
     some (if (PrimitiveGraph.produce "fixture" PrimitiveGraphControls.mixedEnv .storage).isSome then 1 else 0)]),
   ("graph.unresolved-source-fields-not-empty-success",[
     some (if (PrimitiveGraph.produce "fixture" PrimitiveGraphControls.unresolvedEnv .memory).isNone then 1 else 0)]),
   ("alias-rhs.legacy.source-pair-caller",aliasPairValues .legacy),
   ("alias-rhs.viaIR.source-pair-caller",aliasPairValues .viaIR),
   ("alias-rhs.legacy.target-captures-caller-live",aliasPrefixValues .legacy),
   ("alias-rhs.viaIR.target-captures-caller-live",aliasPrefixValues .viaIR),
   ("alias-rhs.legacy.actual-source-target",rhsAliasedFinalValues .legacy true),
   ("alias-rhs.viaIR.actual-source-target",rhsAliasedFinalValues .viaIR true),
   ("alias-rhs.legacy.unchecked-source-target",rhsAliasedFinalValues .legacy false),
   ("alias-rhs.viaIR.unchecked-source-target",rhsAliasedFinalValues .viaIR false),
   ("alias-rhs.signed-boundary.legacy",aliasSignedValues .legacy),
   ("alias-rhs.signed-boundary.viaIR",aliasSignedValues .viaIR),
   ("alias-rhs.all-three-equal",[
     AssignmentControls.observed ((assignAssignSubOperand .legacy .u8 .here .here .here).run MixedAssignmentControls.target),
     AssignmentControls.observed ((assignAssignSubOperand .viaIR .u8 .here .here .here).run MixedAssignmentControls.target)]),
   ("alias-rhs.actual-versus-initial-rhs-formula",[
     AssignmentControls.observed ((assignAssignSubOperand .viaIR .u8 (.there .here) .here (.there .here)).run MixedAssignmentControls.target),
     some (doubleDelta .viaIR 7 3)]),
   ("short.and.take.legacy.source",scSourceValues .legacy true .here (.there .here) (.there .here) .here),
   ("short.and.take.viaIR.source",scSourceValues .viaIR true .here (.there .here) (.there .here) .here),
   ("short.or.take.legacy.source",scSourceValues .legacy false (.there .here) .here .here (.there .here)),
   ("short.or.take.viaIR.source",scSourceValues .viaIR false (.there .here) .here .here (.there .here)),
   ("short.and.skip.legacy.source",scSourceValues .legacy true .here .here (.there .here) .here),
   ("short.and.skip.viaIR.source",scSourceValues .viaIR true .here .here (.there .here) .here),
   ("short.or.skip.legacy.source",scSourceValues .legacy false (.there .here) (.there .here) .here (.there .here)),
   ("short.or.skip.viaIR.source",scSourceValues .viaIR false (.there .here) (.there .here) .here (.there .here)),
   ("short.and.take.target-capture-caller-live",scTargetValues true .here (.there .here) (.there .here) .here),
   ("short.or.take.target-capture-caller-live",scTargetValues false (.there .here) .here .here (.there .here)),
   ("short.and.skip.target-capture-caller-live",scTargetValues true .here .here (.there .here) .here),
   ("short.or.skip.target-capture-caller-live",scTargetValues false (.there .here) (.there .here) .here (.there .here)),
   ("short.source-only-failure.legacy",scFailureSource .legacy),
   ("short.source-only-failure.viaIR",scFailureSource .viaIR),
   ("short.target-only-failure.skip-force",[scFailureTarget false,scFailureTarget true]),
   ("short.eager-right-caller-wrong",[
     some (if boolT (TEnv.get (.there .here) ShortCircuitControls.eagerTarget.env) then 1 else 0),
     some (if boolT (TEnv.get (.there .here) P12Controls.target.env) then 1 else 0)]),
   ("graph.boundary.direct.metadata.legacy",graphMetadata GraphAdmissionBoundary.directUnit .legacy),
   ("graph.boundary.direct.metadata.viaIR",graphMetadata GraphAdmissionBoundary.directUnit .viaIR),
   ("graph.boundary.guarded.metadata",graphMetadata GraphAdmissionBoundary.guardedUnit .viaIR),
   ("graph.boundary.resolved-direct-guarded-memory-storage",[
     graphBoundaryShape false .memory,graphBoundaryShape false .storage,
     graphBoundaryShape true .memory,graphBoundaryShape true .storage]),
   ("graph.boundary.guarded-identity-fieldcount-ranks",[
     some (Int.ofNat (GraphAdmissionBoundary.schema.declId ⟨0,by decide⟩)),
     some (Int.ofNat (GraphAdmissionBoundary.schema.fields ⟨0,by decide⟩).length),
     some (Int.ofNat ((TypeGraph.Ty.node ⟨0,by decide⟩).inlineRank GraphAdmissionBoundary.schema.rank)),
     some (Int.ofNat ((TypeGraph.Ty.array (.node ⟨0,by decide⟩)).inlineRank GraphAdmissionBoundary.schema.rank))]),
   ("graph.boundary.inline-versus-guarded-check",[
     some (if (TypeGraph.Ty.node ⟨0,by decide⟩).inlineRank GraphAdmissionBoundary.schema.rank <
       GraphAdmissionBoundary.schema.rank ⟨0,by decide⟩ then 1 else 0),
     some (if (TypeGraph.Ty.array (.node ⟨0,by decide⟩)).inlineRank GraphAdmissionBoundary.schema.rank <
       GraphAdmissionBoundary.schema.rank ⟨0,by decide⟩ then 1 else 0)]),
   ("unsigned8.pure.legacy",unsignedPureValues 8 (by decide) .legacy),
   ("unsigned8.pure.viaIR",unsignedPureValues 8 (by decide) .viaIR),
   ("unsigned16.pure.legacy",unsignedPureValues 16 (by decide) .legacy),
   ("unsigned16.pure.viaIR",unsignedPureValues 16 (by decide) .viaIR),
   ("unsigned256.pure.legacy",unsignedPureValues 256 (by decide) .legacy),
   ("unsigned256.pure.viaIR",unsignedPureValues 256 (by decide) .viaIR),
   ("unsigned8.effect.legacy.source-pair-caller",unsignedEffectPair .legacy),
   ("unsigned8.effect.viaIR.source-pair-caller",unsignedEffectPair .viaIR),
   ("unsigned8.effect.legacy.capture-caller-live",unsignedEffectPrefix .legacy),
   ("unsigned8.effect.viaIR.capture-caller-live",unsignedEffectPrefix .viaIR),
   ("unsigned8.effect.legacy.source-target",unsignedEffectFinal .legacy),
   ("unsigned8.effect.viaIR.source-target",unsignedEffectFinal .viaIR),
   ("unsigned8.inrange.source-target",[
     intOf ((Source.evalE (G0 .legacy) {F0 with checked := false} 3
       (.binary .sub (.local .here) (.local (.there .here)))).run ReadControls.source),
     unsignedValue ((UnsignedNarrowing.subValue 8 (.simple (.local .here)) (.simple (.local (.there .here)))).evalT ReadControls.target)]),
   ("unsigned8.bare-checked-versus-wrapped",[
     (BinOp.evalT .sub (p := .uint) rfl (integerValue .u8 0 (by decide)) (integerValue .u8 1 (by decide))).map (fun v => v.val),
     AssignmentControls.observed ((UnsignedNarrowing.assignReadOperand .legacy 8 (.there .here) .here).run UnsignedNarrowingControls.target)]),
   ("unsigned8.unmasked-word-versus-narrow",[
     unsignedValue ((Val.binop .subW rfl rfl (.simple (.local .here)) (.simple (.local (.there .here)))).evalT
       (UnsignedNarrowingControls.pureTarget 8 (by decide))),
     AssignmentControls.observed ((UnsignedNarrowing.assignReadOperand .legacy 8 (.there .here) .here).run UnsignedNarrowingControls.target)]),
   ("unsigned8.reversed-dropped-versus-captured",[
     unsignedValue ((UnsignedNarrowing.subValue 8 (.simple (.local (.there .here))) (.simple (.local .here))).evalT
       (UnsignedNarrowingControls.pureTarget 8 (by decide))),
     unsignedValue ((UnsignedNarrowing.subValue 8 (.simple (.local (.there .here))) (.simple (.local (.there .here)))).evalT
       UnsignedNarrowingControls.targetPost),
     AssignmentControls.observed ((UnsignedNarrowing.assignReadOperand .legacy 8 (.there .here) .here).run UnsignedNarrowingControls.target)]),
   ("unsigned8.source-only-checked-mode",[
     some (if revertOf ((Source.evalE (G0 .legacy) F0 3 (.binary .sub (.local .here) (.local (.there .here)))).run
       (UnsignedNarrowingControls.pureSource 8 (by decide))) == some (Source.panicData .arithmetic) then 1 else 0),
     (unsignedPureValues 8 (by decide) .legacy).head!]),
   ("unsigned8.same-index-both-pipelines",[
     AssignmentControls.observed ((UnsignedNarrowing.assignReadOperand .legacy 8 .here .here).run UnsignedNarrowingControls.target),
     AssignmentControls.observed ((UnsignedNarrowing.assignReadOperand .viaIR 8 .here .here).run UnsignedNarrowingControls.target)]),
   ("wrapped-pair.legacy.source-pair-caller",wrappedPairSource .legacy),
   ("wrapped-pair.viaIR.source-pair-caller",wrappedPairSource .viaIR),
   ("wrapped-pair.legacy.semantic-captures-caller-live",wrappedPairPrefix .legacy),
   ("wrapped-pair.viaIR.semantic-captures-caller-live",wrappedPairPrefix .viaIR),
   ("wrapped-pair.viaIR.physical-captures-caller-live",wrappedPairPrefix .viaIR true),
   ("wrapped-pair.legacy.actual-final",wrappedPairFinal .legacy),
   ("wrapped-pair.viaIR.actual-final",wrappedPairFinal .viaIR),
   ("wrapped-pair.rhs-alias.legacy",wrappedRhsFinal .legacy),
   ("wrapped-pair.rhs-alias.viaIR",wrappedRhsFinal .viaIR),
   ("wrapped-pair.all-same-both-pipelines",[AssignmentControls.observed ((WrappedAssignmentPair.operand .legacy 8 .here .here .here).run WrappedPairControls.T),AssignmentControls.observed ((WrappedAssignmentPair.operand .viaIR 8 .here .here .here).run WrappedPairControls.T)]),
   ("wrapped-pair.stale-versus-legacy",[unsignedValue ((UnsignedNarrowing.subValue 8 (.simple (.local .here)) (.simple (.local (.there .here)))).evalT WrappedPairControls.T),AssignmentControls.observed ((WrappedAssignmentPair.operand .legacy 8 .here .here (.there .here)).run WrappedPairControls.T)]),
   ("wrapped-pair.uncaptured-versus-viaIR",[unsignedValue ((UnsignedNarrowing.subValue 8 (.simple (.local .here)) (.simple (.local (.there .here)))).evalT WrappedPairControls.targetFinal),AssignmentControls.observed ((WrappedAssignmentPair.operand .viaIR 8 .here .here (.there .here)).run WrappedPairControls.T)]),
   ("wrapped-pair.reversed-versus-viaIR",[unsignedValue ((UnsignedNarrowing.subValue 8 (.simple (.local (.there .here))) (.simple (.local .here))).evalT WrappedPairControls.T),AssignmentControls.observed ((WrappedAssignmentPair.operand .viaIR 8 .here .here (.there .here)).run WrappedPairControls.T)]),
   ("wrapped-pair.triple.legacy.final",wrappedTripleFinal .legacy),
   ("wrapped-pair.triple.viaIR.final",wrappedTripleFinal .viaIR),
   ("wrapped-pair.triple.legacy.caller-live",wrappedTripleCaller .legacy),
   ("wrapped-pair.triple.viaIR.caller-live",wrappedTripleCaller .viaIR),
   ("wrapped-pair.uint16.viaIR",wrappedPairWidth 16 (by decide) .viaIR),
   ("wrapped-pair.uint256.viaIR",wrappedPairWidth 256 (by decide) .viaIR),
   ("wrapped-pair.uint256.legacy",wrappedPairWidth 256 (by decide) .legacy),
   ("recursive-graph.chain.storage.ids",recursiveGraphIds RecursiveGraphControls.chain .storage),
   ("recursive-graph.chain.memory.ids",recursiveGraphIds RecursiveGraphControls.chain .memory),
   ("recursive-graph.chain.ranks",recursiveGraphRanks RecursiveGraphControls.chain .storage),
   ("recursive-graph.chain.typed-node-edges",recursiveChainEdges),
   ("recursive-graph.guarded-self.all-locations",recursiveGraphAllLocations GraphAdmissionBoundary.guardedEnv),
   ("recursive-graph.inline-self.all-locations",recursiveGraphAllLocations GraphAdmissionBoundary.directEnv),
   ("recursive-graph.guarded-mutual.all-locations",recursiveGraphAllLocations RecursiveGraphControls.guardedMutual),
   ("recursive-graph.inline-mutual.all-locations",recursiveGraphAllLocations RecursiveGraphControls.mutualEnv),
   ("recursive-graph.fixed-around-guard",[recursiveGraphSuccess RecursiveGraphControls.fixedGuard .storage] ++ recursiveGraphRanks RecursiveGraphControls.fixedGuard .storage),
   ("recursive-graph.fixed-inline-cycle",[recursiveGraphSuccess RecursiveGraphControls.fixedInline .storage]),
   ("recursive-graph.mapping.storage-memory",[recursiveGraphSuccess RecursiveGraphControls.mappingEnv .storage,recursiveGraphSuccess RecursiveGraphControls.mappingEnv .memory]),
   ("recursive-graph.mapping.source-resolution",[some (if (RecursiveGraphControls.mappingEnv.structFields GraphAdmissionBoundary.loopName .storage).isSome then 1 else 0),some (if (RecursiveGraphControls.mappingEnv.structFields GraphAdmissionBoundary.loopName .memory).isSome then 1 else 0)]),
   ("recursive-graph.enum-udvt.actual-id",recursiveGraphIds RecursiveGraphControls.wrappedEnv .storage),
   ("recursive-graph.enum-udvt.target-fields",recursiveEnumFields),
   ("recursive-graph.fixed-capacity-boundaries",[some (if (RecursiveGraph.lowerType RecursiveGraphControls.chain.layout (PrimitiveGraph.name RecursiveGraphControls.chain) (.array .memory .bool (some 0))).isSome then 1 else 0), some (if (RecursiveGraph.lowerType RecursiveGraphControls.chain.layout (PrimitiveGraph.name RecursiveGraphControls.chain) (.array .memory .bool (some (2^256)))).isSome then 1 else 0), some (if (RecursiveGraph.lowerType RecursiveGraphControls.chain.layout (PrimitiveGraph.name RecursiveGraphControls.chain) (.array .memory .bool (some 3))).isSome then 1 else 0)]),
   ("recursive-graph.enum-capacity-boundary",[some (if (RecursiveGraph.lowerType RecursiveGraphControls.excessiveEnumLayout (PrimitiveGraph.name RecursiveGraphControls.chain) (.enum ⟨none,"TooLarge"⟩)).isSome then 1 else 0)]),
   ("recursive-graph.duplicate-unresolved-bytes-components",[recursiveGraphSuccess PrimitiveGraphControls.duplicated .storage,recursiveGraphSuccess PrimitiveGraphControls.unresolvedEnv .storage,recursiveGraphSuccess PrimitiveGraphControls.byteEnv .storage]),
   ("recursive-graph.zero-actual-declarations",[recursiveGraphSuccess (Source.Env.mk []) .storage] ++ recursiveGraphIds (Source.Env.mk []) .storage),
   ("recursive-graph.mapping.metadata-both-pipelines",[some (if Frontend.Static.strictMetadataChecker.check (Source.resolveUnit ⟨.legacy,[]⟩ RecursiveGraphControls.mappingUnit) () () then 1 else 0),some (if Frontend.Static.strictMetadataChecker.check (Source.resolveUnit ⟨.viaIR,[]⟩ RecursiveGraphControls.mappingUnit) () () then 1 else 0)]),
   ("h15.mapping.admissible-locations",[h15Allowed LocationGraphLaws.E LocationGraphLaws.loop .storage,h15Allowed LocationGraphLaws.E LocationGraphLaws.loop .memory,h15Allowed LocationGraphLaws.E LocationGraphLaws.loop .calldata]),
   ("h15.mixed.plain-and-mapping-memory",[h15Allowed LocationGraphLaws.mixed ⟨none,"Plain"⟩ .memory,h15Allowed LocationGraphLaws.mixed LocationGraphLaws.loop .memory]),
   ("h15.mixed.memory-physical-identities",[some (Int.ofNat (LocationGraphLaws.memorySchema.declId ⟨0,by decide⟩)),some (Int.ofNat (LocationGraphLaws.memoryCertificate.sourceIndex ⟨0,by decide⟩).val)]),
   ("h15.mixed.memory-fields",[h15MemoryFields]),
   ("h15.storage.original-and-revised-identities",[some (Int.ofNat (LocationGraphLaws.storageResult.1.declId ⟨0,by decide⟩)),some (Int.ofNat (LocationGraphLaws.storageCertificate.sourceIndex ⟨0,by decide⟩).val)]),
   ("h15.storage.mapping-guard-preserved",[h15StorageFields]),
   ("h15.direct-mapping.memory-calldata-refused",[some (if (h15MappingType.ty LocationGraphLaws.E none .memory).isSome then 1 else 0),some (if (h15MappingType.ty LocationGraphLaws.E none .calldata).isSome then 1 else 0)]),
   ("h15.direct-mapping.storage-admitted",[some (if (h15MappingType.ty LocationGraphLaws.E none .storage).isSome then 1 else 0)]),
   ("h15.source-named-memory-resolution-gap",[some (if ((Source.Syn.userType ⟨"Loop",[]⟩).ty LocationGraphLaws.E none .memory).isSome then 1 else 0)]),
   ("h15.source-memory-local-flag-gap",[some (if Source.locOK (.struct .memory LocationGraphLaws.loop) (some .memory) false then 1 else 0)]),
   ("h15.source-actual-declaration-admission-gap",[h15TypedDeclaration]),
   ("h15.storage-schema-rank",[some (Int.ofNat (LocationGraphLaws.storageResult.1.rank ⟨0,by decide⟩))]),
   ("location-producer.mixed.memory.shape",locationProducedShape LocationProducerControls.mixed .memory),
   ("location-producer.mixed.memory.ids",locationProducedIds LocationProducerControls.mixed .memory),
   ("location-producer.mixed.calldata.ids",locationProducedIds LocationProducerControls.mixed .calldata),
   ("location-producer.mixed.storage.ids",locationProducedIds LocationProducerControls.mixed .storage),
   ("location-producer.mixed.storage.ranks",locationProducedRanks LocationProducerControls.mixed .storage),
   ("location-producer.mixed.memory.fields",[locationMemoryFields]),
   ("location-producer.mixed.storage.mapping-fields",[locationStorageFields]),
   ("location-producer.storage-only.empty-memory-view",locationProducedShape RecursiveGraphControls.mappingEnv .memory),
   ("location-producer.chain.memory.ids",locationProducedIds LocationProducerControls.chain .memory),
   ("location-producer.chain.memory.ranks",locationProducedRanks LocationProducerControls.chain .memory),
   ("location-producer.guarded-self.memory.shape",locationProducedShape GraphAdmissionBoundary.guardedEnv .memory),
   ("location-producer.inline-cycle.memory.component-failure",locationProducedShape GraphAdmissionBoundary.directEnv .memory),
   ("location-producer.scoped.memory.ids",locationProducedIds PrimitiveGraphControls.scopedEnv .memory),
   ("location-producer.unsupported-admissible-field.not-omitted",locationProducedShape LocationProducerControls.withBytes .memory),
   ("location-producer.transitive.memory.ids",locationProducedIds LocationProducerControls.transitiveEnv .memory),
   ("location-producer.transitive.storage.ids",locationProducedIds LocationProducerControls.transitiveEnv .storage),
   ("location-producer.transitive.storage.fields",[locationTransitiveFields]),
   ("location-producer.physical-versus-compacted-index",[some (Int.ofNat (LocationProducerControls.memoryResult.1.declId ⟨0,by decide⟩)),some 0])]

/-- info: legacy.source-pair-and-caller=[some 7, some 3, some 7, some 7]
legacy.target-captures-and-caller=[some 7, some 3, some 7, some 7]
legacy.source-target-final=[some 4, some 4]
viaIR.source-pair-and-caller=[some 7, some 7, some 7, some 7]
viaIR.target-captures-and-caller=[some 7, some 7, some 7, some 7]
viaIR.source-target-final=[some 0, some 0]
unchecked.legacy-source-target=[some 4, some 4]
unchecked.viaIR-source-target=[some 0, some 0]
mixed.live-memory-and-storage=[some 0, some 2, some 1]
bad.uncaptured-target=[some 0]
prefix1.repeated-alias=[some 7]
prefix2.reached-copy=[some 3]
prefix3.repeated-alias=[some 3]
signed.legacy-viaIR=[some (-5), some 0]
signed.actual-legacy-source-target=[some (-5), some (-5)]
signed.actual-viaIR-source-target=[some 0, some 0]
prefix1.actual-source-target=[some 7, some 7]
prefix2.actual-source-target=[some 3, some 3]
prefix3.actual-source-target=[some 3, some 3]
double.legacy.source-pair-caller=[some 3, some 3, some 3, some 3, some 3]
double.legacy.target-semantic-captures-caller=[some 3, some 3, some 3, some 3, some 3]
double.legacy.actual-final=[some 0, some 0]
double.viaIR.source-pair-caller=[some 7, some 3, some 7, some 3, some 3]
double.viaIR.target-semantic-captures-caller=[some 7, some 3, some 7, some 3, some 3]
double.viaIR.target-physical-captures-caller=[some 3, some 7, some 7, some 3, some 3]
double.viaIR.actual-final=[some 4, some 4]
double.unchecked.legacy=[some 0, some 0]
double.unchecked.viaIR=[some 4, some 4]
double.shared-destination.legacy=[some 0, some 0]
double.shared-destination.viaIR=[some 4, some 4]
double.bad-uncaptured=[some 0]
double.aliasing-rhs.actual=[some 0, some 0]
double.signed.legacy=[some 0, some 0]
double.signed.viaIR=[some (-5), some (-5)]
reference.legacy.internal-source-pointers-caller=[some 1, some 0, some 1, some 1]
reference.legacy.internal-target-pointers-caller=[some 1, some 0, some 1, some 1]
reference.viaIR.internal-source-pointers-caller=[some 1, some 1, some 1, some 1]
reference.viaIR.internal-target-pointers-caller=[some 1, some 1, some 1, some 1]
reference.old-capture-versus-late-snapshot-length=[some 2, some 3]
p12.condition.actual-source-value-caller=[some 1, some 1, some 1]
p12.condition.target-capture-caller-live-refs=[some 1, some 1, some 1, some 0, some 2, some 1]
p12.memory.actual-captured-reference=[some 0, some 2]
p12.storage.actual-captured-root=[some 1]
loop.once-captured-versus-refreshed=[some 1, some 0]
loop.intrinsic-prefix1-prefix2-stale-choice=[some 1, some 1]
graph.actual-selected-positions=[some 2, some 1, some 2]
graph.computed-memory-storage-success=[some 1, some 1]
graph.scoped-same-name-success=[some 1]
graph.duplicate-identity-and-field-rejection=[some 1, some 1]
graph.resolved-bytes-component-open=[some 1]
graph.signed-payable-bool-success=[some 1]
graph.unresolved-source-fields-not-empty-success=[some 1]
alias-rhs.legacy.source-pair-caller=[some 3, some 3, some 3, some 3]
alias-rhs.viaIR.source-pair-caller=[some 7, some 7, some 7, some 7]
alias-rhs.legacy.target-captures-caller-live=[some 3, some 3, some 3, some 3, some 2, some 1]
alias-rhs.viaIR.target-captures-caller-live=[some 7, some 7, some 7, some 7, some 2, some 1]
alias-rhs.legacy.actual-source-target=[some 0, some 0]
alias-rhs.viaIR.actual-source-target=[some 0, some 0]
alias-rhs.legacy.unchecked-source-target=[some 0, some 0]
alias-rhs.viaIR.unchecked-source-target=[some 0, some 0]
alias-rhs.signed-boundary.legacy=[some 0, some 0]
alias-rhs.signed-boundary.viaIR=[some 0, some 0]
alias-rhs.all-three-equal=[some 0, some 0]
alias-rhs.actual-versus-initial-rhs-formula=[some 0, some 4]
short.and.take.legacy.source=[some 1, some 1, some 1, some 1, some 1, some 1]
short.and.take.viaIR.source=[some 1, some 1, some 1, some 1, some 1, some 1]
short.or.take.legacy.source=[some 0, some 0, some 0, some 0, some 0, some 0]
short.or.take.viaIR.source=[some 0, some 0, some 0, some 0, some 0, some 0]
short.and.skip.legacy.source=[some 0, some 0, some 0, some 0, some 0, some 1]
short.and.skip.viaIR.source=[some 0, some 0, some 0, some 0, some 0, some 1]
short.or.skip.legacy.source=[some 1, some 0, some 1, some 1, some 0, some 1]
short.or.skip.viaIR.source=[some 1, some 0, some 1, some 1, some 0, some 1]
short.and.take.target-capture-caller-live=[some 1, some 1, some 1, some 2, some 1]
short.or.take.target-capture-caller-live=[some 0, some 0, some 0, some 2, some 1]
short.and.skip.target-capture-caller-live=[some 0, some 0, some 1, some 2, some 1]
short.or.skip.target-capture-caller-live=[some 1, some 0, some 1, some 2, some 1]
short.source-only-failure.legacy=[some 1, some 0, some 1]
short.source-only-failure.viaIR=[some 1, some 0, some 1]
short.target-only-failure.skip-force=[some 0, some 1]
short.eager-right-caller-wrong=[some 0, some 1]
graph.boundary.direct.metadata.legacy=[some 1, some 1]
graph.boundary.direct.metadata.viaIR=[some 1, some 1]
graph.boundary.guarded.metadata=[some 1, some 1]
graph.boundary.resolved-direct-guarded-memory-storage=[some 0, some 0, some 1, some 1]
graph.boundary.guarded-identity-fieldcount-ranks=[some 0, some 1, some 1, some 0]
graph.boundary.inline-versus-guarded-check=[some 0, some 1]
unsigned8.pure.legacy=[some 255, some 255]
unsigned8.pure.viaIR=[some 255, some 255]
unsigned16.pure.legacy=[some 65535, some 65535]
unsigned16.pure.viaIR=[some 65535, some 65535]
unsigned256.pure.legacy=[some 115792089237316195423570985008687907853269984665640564039457584007913129639935, some 115792089237316195423570985008687907853269984665640564039457584007913129639935]
unsigned256.pure.viaIR=[some 115792089237316195423570985008687907853269984665640564039457584007913129639935, some 115792089237316195423570985008687907853269984665640564039457584007913129639935]
unsigned8.effect.legacy.source-pair-caller=[some 0, some 1, some 0, some 0]
unsigned8.effect.viaIR.source-pair-caller=[some 0, some 0, some 0, some 0]
unsigned8.effect.legacy.capture-caller-live=[some 0, some 1, some 0, some 0, some 2, some 1]
unsigned8.effect.viaIR.capture-caller-live=[some 0, some 0, some 0, some 0, some 2, some 1]
unsigned8.effect.legacy.source-target=[some 255, some 255]
unsigned8.effect.viaIR.source-target=[some 0, some 0]
unsigned8.inrange.source-target=[some 4, some 4]
unsigned8.bare-checked-versus-wrapped=[none, some 255]
unsigned8.unmasked-word-versus-narrow=[some 115792089237316195423570985008687907853269984665640564039457584007913129639935, some 255]
unsigned8.reversed-dropped-versus-captured=[some 1, some 0, some 255]
unsigned8.source-only-checked-mode=[some 1, some 255]
unsigned8.same-index-both-pipelines=[some 0, some 0]
wrapped-pair.legacy.source-pair-caller=[some 1, some 1, some 1, some 1]
wrapped-pair.viaIR.source-pair-caller=[some 0, some 1, some 1, some 1]
wrapped-pair.legacy.semantic-captures-caller-live=[some 1, some 1, some 1, some 1, some 2, some 1]
wrapped-pair.viaIR.semantic-captures-caller-live=[some 0, some 1, some 1, some 1, some 2, some 1]
wrapped-pair.viaIR.physical-captures-caller-live=[some 1, some 0, some 1, some 1, some 2, some 1]
wrapped-pair.legacy.actual-final=[some 0, some 0]
wrapped-pair.viaIR.actual-final=[some 255, some 255]
wrapped-pair.rhs-alias.legacy=[some 0, some 0, some 1, some 1, some 1, some 1]
wrapped-pair.rhs-alias.viaIR=[some 0, some 0, some 0, some 0, some 0, some 0]
wrapped-pair.all-same-both-pipelines=[some 0, some 0]
wrapped-pair.stale-versus-legacy=[some 255, some 0]
wrapped-pair.uncaptured-versus-viaIR=[some 0, some 255]
wrapped-pair.reversed-versus-viaIR=[some 1, some 255]
wrapped-pair.triple.legacy.final=[some 0, some 0]
wrapped-pair.triple.viaIR.final=[some 255, some 255]
wrapped-pair.triple.legacy.caller-live=[some 1, some 1, some 1, some 1, some 1, some 1, some 2, some 1]
wrapped-pair.triple.viaIR.caller-live=[some 0, some 1, some 1, some 0, some 1, some 1, some 2, some 1]
wrapped-pair.uint16.viaIR=[some 65535, some 65535]
wrapped-pair.uint256.viaIR=[some 115792089237316195423570985008687907853269984665640564039457584007913129639935, some 115792089237316195423570985008687907853269984665640564039457584007913129639935]
wrapped-pair.uint256.legacy=[some 0, some 0]
recursive-graph.chain.storage.ids=[some 3, some 1, some 2, some 3]
recursive-graph.chain.memory.ids=[some 3, some 1, some 2, some 3]
recursive-graph.chain.ranks=[some 3, some 2, some 1]
recursive-graph.chain.typed-node-edges=[some 1, some 2, none]
recursive-graph.guarded-self.all-locations=[some 1, some 1, some 1]
recursive-graph.inline-self.all-locations=[some 0, some 0, some 0]
recursive-graph.guarded-mutual.all-locations=[some 1, some 1, some 1]
recursive-graph.inline-mutual.all-locations=[some 0, some 0, some 0]
recursive-graph.fixed-around-guard=[some 1, some 2]
recursive-graph.fixed-inline-cycle=[some 0]
recursive-graph.mapping.storage-memory=[some 1, some 0]
recursive-graph.mapping.source-resolution=[some 1, some 0]
recursive-graph.enum-udvt.actual-id=[some 1, some 2]
recursive-graph.enum-udvt.target-fields=[some 1]
recursive-graph.fixed-capacity-boundaries=[some 0, some 0, some 1]
recursive-graph.enum-capacity-boundary=[some 0]
recursive-graph.duplicate-unresolved-bytes-components=[some 0, some 0, some 0]
recursive-graph.zero-actual-declarations=[some 1, some 0]
recursive-graph.mapping.metadata-both-pipelines=[some 1, some 1]
h15.mapping.admissible-locations=[some 1, some 0, some 0]
h15.mixed.plain-and-mapping-memory=[some 1, some 0]
h15.mixed.memory-physical-identities=[some 1, some 1]
h15.mixed.memory-fields=[some 1]
h15.storage.original-and-revised-identities=[some 0, some 0]
h15.storage.mapping-guard-preserved=[some 1]
h15.direct-mapping.memory-calldata-refused=[some 0, some 0]
h15.direct-mapping.storage-admitted=[some 1]
h15.source-named-memory-resolution-gap=[some 1]
h15.source-memory-local-flag-gap=[some 1]
h15.source-actual-declaration-admission-gap=[some 1]
h15.storage-schema-rank=[some 1]
location-producer.mixed.memory.shape=[some 1, some 1]
location-producer.mixed.memory.ids=[some 1]
location-producer.mixed.calldata.ids=[some 1]
location-producer.mixed.storage.ids=[some 0, some 1]
location-producer.mixed.storage.ranks=[some 1, some 1]
location-producer.mixed.memory.fields=[some 1]
location-producer.mixed.storage.mapping-fields=[some 1]
location-producer.storage-only.empty-memory-view=[some 1, some 0]
location-producer.chain.memory.ids=[some 2, some 3, some 4]
location-producer.chain.memory.ranks=[some 3, some 2, some 1]
location-producer.guarded-self.memory.shape=[some 1, some 1]
location-producer.inline-cycle.memory.component-failure=[some 0, some 1]
location-producer.scoped.memory.ids=[some 0, some 1]
location-producer.unsupported-admissible-field.not-omitted=[some 0, some 2]
location-producer.transitive.memory.ids=[some 2]
location-producer.transitive.storage.ids=[some 0, some 1, some 2]
location-producer.transitive.storage.fields=[some 1]
location-producer.physical-versus-compacted-index=[some 1, some 0] -/
#guard_msgs in
#eval IO.println (String.intercalate "\n" (rows.map fun r => r.1 ++ "=" ++ (reprStr r.2).replace "\n" ""))

end Solidity.Lowering.V07.EffectFixtures
