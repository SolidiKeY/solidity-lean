import Solidity.Backend.InternalFlow.RuntimeFrameV3AllocatingHeadViews

/-! Executable exact syntax checking of the existing scoped private bool-array
allocation. Every equation is obtained from actual generalized syntax views;
no execution/simulation, artifact binding or compiler admission is assumed. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingDeclarationCheck
open Evm Evm.Memory RecursiveSource ScalarRecursiveSource AllocatingHeadViews
abbrev Array := RefTy.array (.prim .bool)

def allocation {C : Contract} {Γ : Ctx} : Stmt C Γ Γ :=
 .block (.cons (.declMem Array (.user "private")
   (some (.newArr (.lit 3 rfl) rfl)) rfl rfl) .nil)

theorem assemble {C : Contract} {Γ : Ctx} {source : Stmt C Γ Γ}
 (block : Block source) (parts : AllocatingSourceViews.ConsView block.body)
 (declaration : MemoryDeclaration parts.head) (ending : NilView parts.tail)
 (referenceEq : declaration.reference=Array) (nameEq : declaration.name=.user "private")
 (rhs : MRhs C Γ declaration.reference) (initialEq : declaration.initial=some rhs)
 (array : NewArray rhs) (literal : Literal array.length) (numberEq : literal.number=3) :
 source=allocation := by
 rcases block with ⟨inside,body,output,sourceShape⟩
 rcases parts with ⟨middle,head,tail,bodyShape⟩
 rcases declaration with ⟨reference,name,initial,defaultAllowed,memoryFree,middleEq,headShape⟩
 rcases ending with ⟨insideEq,tailShape⟩
 rcases array with ⟨length,allowed,rhsShape⟩
 rcases literal with ⟨number,valid,lengthShape⟩
 simp only [] at *
 subst reference
 subst name
 subst number
 simp only [] at *
 have middleContext : middle=.mem Array::Γ := middleEq
 have insideContext : inside=.mem Array::Γ := insideEq.trans middleContext
 clear insideEq
 subst middle
 simp only [] at *
 subst inside
 change MRhs C Γ Array at rhs
 change Array.newArrOk=true at allowed
 subst initial
 subst rhs
 have actualLength : length=Simple.lit 3 valid := lengthShape
 subst length
 have sameSource : source=Stmt.block body := eq_of_heq sourceShape
 have sameHead : head=Stmt.declMem Array (.user "private") (some (.newArr (.lit 3 valid) allowed)) defaultAllowed memoryFree :=
   eq_of_heq headShape
 have sameTail : tail=(.nil : Prog C (.mem Array::Γ) (.mem Array::Γ)) := eq_of_heq tailShape
 have actualBody : body=Prog.cons head tail := bodyShape
 rw [sameSource,actualBody,sameHead,sameTail]
 rfl

def check {C : Contract} {Γ : Ctx} (source : Stmt C Γ Γ) : Option (PLift (source=allocation)) := do
 let block ← readBlock source
 let parts ← AllocatingSourceViews.readCons block.body
 let declaration ← readMemoryDeclaration parts.head
 let ending ← readNil parts.tail
 if referenceEq : declaration.reference=Array then
   if nameEq : declaration.name=.user "private" then
     match initialEq : declaration.initial with
     | none => none
     | some rhs => do
       let array ← readNewArray rhs
       let literal ← readLiteral array.length
       if numberEq : literal.number=3 then
         pure ⟨assemble block parts declaration ending referenceEq nameEq rhs initialEq array literal numberEq⟩
       else none
   else none
 else none

end Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingDeclarationCheck
/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingDeclarationCheck.assemble' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingDeclarationCheck.assemble
