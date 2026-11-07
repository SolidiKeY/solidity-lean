import Solidity.Backend.InternalFlow.RuntimeFrameV3AllocatingHeadViews

/-! Typed value views used by allocating-recursion leaf recognition. Every
reader generalizes the primitive index and keeps the actual constructor
payload and equality; no evaluator or syntactic equality oracle is used. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingValueViews

structure SimpleView {C : Contract} {Γ : Ctx} {p : PrimTy} (source : Val C Γ p) : Type where
 value : Simple C Γ p
 shape : source=.simple value

def readSimple {C : Contract} {Γ : Ctx} {p : PrimTy} (source : Val C Γ p) : Option (SimpleView source) :=
 Val.casesOn (motive_5:=fun _ source => Option (SimpleView source)) source
   (simple:=fun value => some ⟨value,rfl⟩)
   (read:=by intros;exact none) (binop:=by intros;exact none)
   (unop:=by intros;exact none) (ternary:=by intros;exact none)
   (readMem:=by intros;exact none) (len:=by intros;exact none)
   (mlen:=by intros;exact none) (modular:=by intros;exact none) (hash:=by intros;exact none)

structure LocalView {C : Contract} {Γ : Ctx} {p : PrimTy} (source : Simple C Γ p) : Type where
 slot : Idx Γ (.val p)
 shape : source=.local slot

def readLocal {C : Contract} {Γ : Ctx} {p : PrimTy} (source : Simple C Γ p) : Option (LocalView source) :=
 Simple.casesOn (motive:=fun _ source => Option (LocalView source)) source
   (lit:=by intros;exact none) (bool:=by intros;exact none)
   («local»:=fun slot => some ⟨slot,rfl⟩) (env:=by intros;exact none)

structure BinaryView {C : Contract} {Γ : Ctx} {q : PrimTy} (source : Val C Γ q) : Type where
 primitive : PrimTy
 operator : BinOp
 accepted : operator.accepts primitive=true
 output : operator.ret primitive=q
 left : Val C Γ primitive
 right : Val C Γ primitive
 shape : source=.binop operator accepted output left right

def readBinary {C : Contract} {Γ : Ctx} {q : PrimTy} (source : Val C Γ q) : Option (BinaryView source) :=
 Val.casesOn (motive_5:=fun _ source => Option (BinaryView source)) source
   (simple:=by intros;exact none) (read:=by intros;exact none)
   (binop:=fun operator accepted output left right => some ⟨_,operator,accepted,output,left,right,rfl⟩)
   (unop:=by intros;exact none) (ternary:=by intros;exact none)
   (readMem:=by intros;exact none) (len:=by intros;exact none)
   (mlen:=by intros;exact none) (modular:=by intros;exact none) (hash:=by intros;exact none)

structure UintBinary {C : Contract} {Γ : Ctx} {q : PrimTy} (source : Val C Γ q) : Type where
 operator : BinOp
 accepted : operator.accepts .uint=true
 output : operator.ret .uint=q
 left : Val C Γ .uint
 right : Val C Γ .uint
 shape : source=.binop operator accepted output left right

def closeBinary {C : Contract} {Γ : Ctx} {q : PrimTy} {source : Val C Γ q}
 (view : BinaryView source) (same : view.primitive=.uint) : UintBinary source := by
 rcases view with ⟨primitive,operator,accepted,output,left,right,shape⟩
 simp only [] at same
 subst primitive
 exact ⟨operator,accepted,output,left,right,shape⟩

def readUintBinary {C : Contract} {Γ : Ctx} {q : PrimTy} (source : Val C Γ q) : Option (UintBinary source) := do
 let view ← readBinary source
 if same : view.primitive=.uint then pure (closeBinary view same) else none

end Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingValueViews

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingValueViews.closeBinary' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingValueViews.closeBinary
