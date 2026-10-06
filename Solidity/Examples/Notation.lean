import Solidity.Calculus.Close

/-!
# The notation, pinned

What the printers show, as `#guard_msgs` tests: a taclet as its rule line
(`Rules.lean`, `RuleSyntax.lean`), a premise standing alone, a formula read
by `dl!{ … }` and printed back (`Notation.lean`), and the goals of an `apply`
derivation as sequents `dl{ Γ ⟹ φ }` (`Logic.lean`).  If a printer changes,
these fail.
-/

namespace Solidity.Examples.Notation

open Proves

local instance : InContract := ⟨StandardExample⟩

/-! ## A taclet is its rule line

`#check` shows what hovering the rule name shows.  The `\find` binds the
schema variables (`∀ {…}`); `T` is the type of the part a capture declares,
and `se`, `sp`, `ie` on the right are the fresh variables at index `k`.
`⟨[ ]⟩` is the combined modality: the rule fires under either.  One taclet
per family. -/

/-! ### Step 1: a read whose receiver is not simple -/

/--
info: @Taclet.storageFieldRead_unfold_rightFst : ∀ {C : Contract} {k : Nat} {m : Modality} {x : Ty} {lhs : Hole C x}
  {x_1 : Name} {nsp : SPath C (Ty.struct x_1)} {fld : Name},
  dl{ ⟨[ lhs = nsp.fld; ]⟩ ⇝ ⟨[ T storage sp = nsp; lhs = sp.fld; ]⟩ }
-/
#guard_msgs in #check @Taclet.storageFieldRead_unfold_rightFst

/-! ### Step 2: a write, source, receiver and index captured in that order -/

/--
info: @Taclet.storageIndexWriteCaptureAllComplexRecv : ∀ {C : Contract} {k : Nat} {m : Modality} {x : RefTy}
  {x_1 x_2 : PrimTy} {it : IndexTy x x_1 (Ty.prim x_2)} {nsp : SPath C (Ty.ref x)} {e₁ : Val C x_1} {e₂ : Val C x_2},
  dl{ ⟨[ nsp[e₁] = e₂; ]⟩ ⇝ ⟨[ T se = e₂; T storage sp = nsp; T ie = e₁; sp[ie] = se; ]⟩ }
-/
#guard_msgs in #check @Taclet.storageIndexWriteCaptureAllComplexRecv

/-! ### Step 3: a statement with simple parts is an update -/

/--
info: @Taclet.storageFieldWriteSave : ∀ {C : Contract} {k : Nat} {m : Modality} {x : Name} {sp : SPath C (Ty.struct x)}
  {fld : Name} {x_1 : PrimTy} {se : Simple C x_1},
  dl{ ⟨[ sp.fld = se; ]⟩ ⇝ { storage := save(storage, sp.fld, se) } ⟨[ ]⟩ }
-/
#guard_msgs in #check @Taclet.storageFieldWriteSave

/-! ### Memory `delete`, `new T[](n)`, `.length` -/

/--
info: @Taclet.memoryFieldDeleteReference : ∀ {C : Contract} {k : Nat} {m : Modality} {R : RefTy} {mv : Var} {rfld x : Name}
  {hd : (Ty.ref R).defaultOkS = true},
  dl{ ⟨[ delete mv.rfld; ]⟩ ⇝ { memory := write(addM(memory), mv.rfld, freshId(addM(memory))) } ⟨[ ]⟩ }
-/
#guard_msgs in #check @Taclet.memoryFieldDeleteReference

/--
info: @Taclet.newArrayCapture : ∀ {C : Contract} {k : Nat} {m : Modality} {R : RefTy} {tgt : NewLhs C R}
  {se : Simple C PrimTy.uint} {hn : R.newArrOk = true},
  dl{ ⟨[ tgt = new T(se); ]⟩ ⇝ ⟨[ T memory mv = new T(se); tgt = mv; ]⟩ }
-/
#guard_msgs in #check @Taclet.newArrayCapture

/--
info: @Taclet.storageLengthRead : ∀ {C : Contract} {k : Nat} {m : Modality} {v : Var} {E : Ty} {sp : SPath C E.array}
  {x : PrimTy} {hlen : x = PrimTy.uint}, dl{ ⟨[ v = sp.length; ]⟩ ⇝ { v := sp.length } ⟨[ ]⟩ }
-/
#guard_msgs in #check @Taclet.storageLengthRead

/-! ### Declarations -/

/--
info: @Taclet.valueDeclSkip : ∀ {C : Contract} {k : Nat} {m : Modality} {p : PrimTy} {v : Var},
  dl{ ⟨[ T v; ]⟩ ⇝ { v := defVal(T) } ⟨[ ]⟩ }
-/
#guard_msgs in #check @Taclet.valueDeclSkip

/-! ### Compound assignment and `++`: `⊕` and `⊕⊕` are operator schema variables -/

/--
info: @Taclet.storageRootOpAssign : ∀ {C : Contract} {k : Nat} {m : Modality} {p : PrimTy} {op : BinOp} {gsp : Name}
  {se : Simple C p}, dl{ ⟨[ gsp ⊕= se; ]⟩ ⇝ { storage := save(storage, gsp, find(storage, gsp) ⊕ se) } ⟨[ ]⟩ }
-/
#guard_msgs in #check @Taclet.storageRootOpAssign

/--
info: @Taclet.storageFieldIncrementAssignment : ∀ {C : Contract} {k : Nat} {m : Modality} {p : PrimTy} {v : Var} {op : IncDec}
  {x : Name} {sp : SPath C (Ty.struct x)} {fld : Name} {hfld : C.fieldType x fld = some (Ty.prim p)}
  {hs : (OpLoc.field sp fld hfld).recvSimple = true},
  dl{ ⟨[ v = sp.fld⊕⊕; ]⟩ ⇝
    { storage := save(storage, sp.fld, find(storage, sp.fld) ± 1) ‖ v := find(storage, sp.fld)⊕⊕ } ⟨[ ]⟩ }
-/
#guard_msgs in #check @Taclet.storageFieldIncrementAssignment

/-! ### Arrays: a push is two nested writes over the length -/

/--
info: @Taclet.storagePushValueSave : ∀ {C : Contract} {k : Nat} {m : Modality} {x : PrimTy} {sp : SPath C (Ty.prim x).array}
  {se : Simple C x},
  dl{ ⟨[ sp .push(se); ]⟩ ⇝ { storage := save(save(storage, sp[sp.length], se), sp.length, sp.length + 1) } ⟨[ ]⟩ }
-/
#guard_msgs in #check @Taclet.storagePushValueSave

/-! ### Memory, and a copy from storage: an allocation is two elements -/

/--
info: @Taclet.memoryFieldWrite : ∀ {C : Contract} {k : Nat} {m : Modality} {mv : Var} {fld x : Name} {x_1 : PrimTy}
  {se : Simple C x_1}, dl{ ⟨[ mv.fld = se; ]⟩ ⇝ { memory := write(memory, mv.fld, se) } ⟨[ ]⟩ }
-/
#guard_msgs in #check @Taclet.memoryFieldWrite

/--
info: @Taclet.memoryStorageCopy : ∀ {C : Contract} {k : Nat} {m : Modality} {mv : Var} {x : RefTy} {sp : SPath C (Ty.ref x)}
  {hm : (Ty.ref x).mapFree = true},
  dl{ ⟨[ mv = sp; ]⟩ ⇝
    { mv := freshId(copySt(memory, find(storage, sp))) ‖ memory := copySt(memory, find(storage, sp)) } ⟨[ ]⟩ }
-/
#guard_msgs in #check @Taclet.memoryStorageCopy

/-! ### With the notation off: the constructors it stands for

and the side condition the line leaves out: `sp` is simple (`Rules.lean`,
"Side conditions"), filled by `side_cond` wherever the rule is applied. -/

/--
info: @Taclet.storageFieldWriteSave : ∀ {C : Contract} {k : Nat} {m : Modality} {x : Name} {sp : SPath C (Ty.struct x)}
  {fld : Name} {x_1 : PrimTy} {hfld : C.fieldType x fld = some (Ty.prim x_1)} {se : Simple C x_1},
  autoParam (sp.isSimple = true) sideCond →
    Taclet C k m (Stmt.assign (Loc.field sp fld hfld) (Src.val (Val.simple se)))
      (Premise.update [UpdElem.storage (STerm.storage.save (sp.lower.field fld) (SValT.val se.lower))])
-/
#guard_msgs in
set_option pp.sol.dl false in
#check @Taclet.storageFieldWriteSave

/-! ## A premise standing alone -/

/-- info: dl{ true } : Premise StandardExample -/
#guard_msgs in #check (Premise.done true : Premise StandardExample)

/-- info: dl{ ⟨[ uint x = 1; alice.age = x; ]⟩ } : Premise StandardExample -/
#guard_msgs in #check (Premise.unfold sol{ uint x = 1; alice.age = x; } : Premise StandardExample)

/-! ## A formula prints as it reads

`a != b` is `¬a = b`, and `balances[a] == 1` on a storage read is
`find(storage, balances[a]) = 1`: `==` compares program expressions, and
prints as the equation of their lowerings. -/

/--
info: dl{ ¬a = b → [ balances[a] = 1; balances[b] = 2; ] find(storage, balances[a]) = 1 } : Fml StandardExample
-/
#guard_msgs in #check dl!{ a != b → [ balances[a] = 1; balances[b] = 2; ] balances[a] == 1 }

/-! A comparison captured by a check, `{ se1 := x <= 255 }`, has no term
spelling of its own: the update element carries it, and prints as it reads. -/

/--
info: dl{ { x := 250 + 10 ‖ se1 := 250 + 10 <= 255 ‖ se2 := 1 < 2 } true } : Fml StandardExample
-/
#guard_msgs in #check dl!{ { x := 250 + 10 ‖ se1 := 250 + 10 <= 255 ‖ se2 := 1 < 2 } true }

/-- What a rule leaves reads back through `dl!{ … }` as the term it is. -/
example : (dl!{ [ balances[a] = 1; ] balances[a] == 1 }).step =
    some dl!{ { storage := save(storage, balances[a], 1) } [ ] find(storage, balances[a]) = 1 } :=
  rfl

/-! ## The goals of a derivation are sequents

`Γ` is the context (preconditions and updates, in order), right of `⟹` the
formula still to prove. -/

/--
trace: ⊢ dl{ ⟹ ¬a = b → [ balances[a] = 1; balances[b] = 2; ] find(storage, balances[a]) = 1 }
---
trace: case h
⊢ dl{ ¬a = b ⟹ [ balances[a] = 1; balances[b] = 2; ] find(storage, balances[a]) = 1 }
---
trace: case h
⊢ dl{ ¬a = b, { storage := save(storage, balances[a], 1) } ⟹ [ balances[b] = 2; ] find(storage, balances[a]) = 1 }
---
trace: case h.h
⊢ dl{ ¬a = b, { storage := save(storage, balances[a], 1) }, { storage := save(storage, balances[b], 2) } ⟹
    find(storage, balances[a]) = 1 }
-/
#guard_msgs in
/-- Two keys the precondition tells apart:
`a != b → [ balances[a] = 1; balances[b] = 2; ] balances[a] == 1`. -/
theorem twoKeys : ⊢ dl!{ a != b → [ balances[a] = 1; balances[b] = 2; ] balances[a] == 1 } := by
  trace_state
  apply intro
  trace_state
  apply update .storageIndexWriteMappingSave
  trace_state
  apply update .storageIndexWriteMappingSave
  apply empty
  trace_state
  refine close ?_
  sol_symex
  sol_close

/-! ## The rules of `⊢` are sequents

A constructor of `Proves` is written as KeY writes its rule: a sequent over
the rest `..Γ` of the context, the premises above the conclusion.  `{U} [ ]`
is an update produced under the box.  `impRight`, `allRight`,
`emptyModality`, `sequentialToParallel`, `simplifyUpdate` and
`applyOnRigidFormula` are the constructors' aliases by solkey's names
(theorems, `Calculus/Logic.lean`). -/

/--
info: @impRight : ∀ {C : Contract} {R : RuleSet} {Γ : List (Hyp C)} {a φ : Fml C}, dl{ ..Γ, a ⟹[R] φ } → dl{ ..Γ ⟹[R] a → φ }
-/
#guard_msgs in #check @Proves.impRight

/--
info: @merge : ∀ {C : Contract} {R : RuleSet} {Γ : List (Hyp C)} {m : Modality} {U V : Upd C} {φ : Fml C},
  U.envOnly = true → dl{ ..Γ, { U ‖ {U}V } ⟹[R] φ } → dl{ ..Γ, { U }, { V } ⟹[R] φ }
-/
#guard_msgs in #check @Proves.merge

/-- The sequent macros build exactly the spines the reflective checks expect
(`Γ ++ [h]` nested to the left, `s :: ω`, `P ++ ω`): the same `Expr`
(`=ₛ`), which `rfl` would not tell from a `[s] ++ ω` spine. -/
example {C : Contract} (R : RuleSet) (Γ : List (Hyp C)) (a φ : Fml C) (U V : Upd C)
    (m : Modality) (s : Stmt C) (ω P : Prog C) (x : Var) (p : PrimTy) : True := by
  guard_expr dl{ ..Γ, a ⟹[R] φ } =ₛ Proves R (Γ ++ [Hyp.pre a]) φ
  guard_expr dl{ ..Γ, {U}, {V} ⟹[R] φ } =ₛ Proves R (Γ ++ [Hyp.upd m U] ++ [Hyp.upd m V]) φ
  guard_expr dl{ ..Γ, ∀ p x ⟹[R] φ } =ₛ Proves R (Γ ++ [Hyp.all x p]) φ
  guard_expr dl{ ..Γ ⟹[R] ⟨[ s; ..ω ]⟩ φ } =ₛ Proves R Γ (Fml.modal m (s :: ω) φ)
  guard_expr dl{ ..Γ ⟹[R] ⟨[ P; ..ω ]⟩ φ } =ₛ Proves R Γ (Fml.modal m (P ++ ω) φ)
  trivial

/-- The sequents read back as the terms they print. -/
example {C : Contract} (R : RuleSet) (Γ : List (Hyp C)) (x : Var) (p : PrimTy) (U : Upd C)
    (φ : Fml C) :
    dl{ ..Γ, ∀ p x, {U} [ ] ⟹[R] φ } = Proves R (Γ ++ [.all x p] ++ [.upd .box U]) φ := rfl

end Solidity.Examples.Notation
