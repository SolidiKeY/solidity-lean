import Solidity.Calculus.NFmlClose
import Solidity.Calculus.Surface
import Solidity.Calculus.Derive
import Solidity.Tools.Inspect
import Solidity.Calculus.SequentNotation

/-!
# The notation, pinned

What the printers show, as `#guard_msgs` tests: a taclet as its rule line
(`Rules.lean`, `RuleSyntax.lean`), a premise standing alone, a formula read
by `dl!{ … }` and printed back (`Notation.lean`), and the goals of an `apply`
derivation as sequents `dl{ Γ ⟹ φ }` (`Logic.lean`).  If a printer changes,
these fail.

Everything here is the scoped calculus's: the rule lines are
`Taclet`'s, printed by `Delab` as today's print, the premises
`Premise`'s, the rules of `⊢` `Proves`'s, and the formulas and
the derivation read scoped (`open scoped Solidity.Scoped`, section
`Scoped`): a parameter is bound by `∀`, a formula is a `Fml C []`.
A sequent is read as it prints under `open scoped Solidity.Sequent`
(section `Sequents`).
-/

namespace Solidity.Examples.Notation

local instance : InContract := ⟨StandardExample⟩

/-! ## A taclet is its rule line

`#check` shows what hovering the rule name shows.  The `\find` binds the
schema variables (`∀ {…}`); `T` is the type of the part a capture declares,
and `se`, `sp`, `ie` on the right are the fresh variables at index `k`.
`⟨[ ]⟩` is the combined modality: the rule fires under either.  One taclet
per family. -/

/-! ### Step 1: a read whose receiver is not simple -/

/-! `lhs` is a hole: the statement a read lands in (`v = □`, `lsv = □`,
`loc = □`), one rule for the three. -/

/--
info: @Taclet.storageFieldRead_unfold_rightFst : ∀ {C : Contract} {k : Nat} {m : Modality} {Γ : Ctx} {x : Ty}
  {lhs : SHole C Γ x} {x_1 : Name} {nsp : SPath C Γ (Ty.struct x_1)} {fld : Name},
  dl{ ⟨[ lhs = nsp.fld; ]⟩ ⇝ ⟨[ T storage sp = nsp; lhs = sp.fld; ]⟩ }
-/
#guard_msgs in #check @Taclet.storageFieldRead_unfold_rightFst

/-! ### Step 2: a write, source, receiver and index captured in that order -/

/--
info: @Taclet.storageIndexWriteCaptureAllComplexRecv : ∀ {C : Contract} {k : Nat} {m : Modality} {Γ : Ctx} {x : RefTy}
  {x_1 x_2 : PrimTy} {it : IndexTy x x_1 (Ty.prim x_2)} {nsp : SPath C Γ (Ty.ref x)} {e₁ : Val C Γ x_1}
  {e₂ : Val C Γ x_2}, dl{ ⟨[ nsp[e₁] = e₂; ]⟩ ⇝ ⟨[ T se = e₂; T storage sp = nsp; T ie = e₁; sp[ie] = se; ]⟩ }
-/
#guard_msgs in #check @Taclet.storageIndexWriteCaptureAllComplexRecv

/-! ### Step 3: a statement with simple parts is an update -/

/--
info: @Taclet.storageFieldWriteSave : ∀ {C : Contract} {k : Nat} {m : Modality} {Γ : Ctx} {x : Name}
  {sp : SPath C Γ (Ty.struct x)} {fld : Name} {x_1 : PrimTy} {se : Simple C Γ x_1},
  dl{ ⟨[ sp.fld = se; ]⟩ ⇝ { storage := save(storage, sp.fld, se) } ⟨[ ]⟩ }
-/
#guard_msgs in #check @Taclet.storageFieldWriteSave

/-! ### Memory `delete`, `new T[](n)`, `.length` -/

/--
info: @Taclet.memoryFieldDeleteReference : ∀ {C : Contract} {k : Nat} {m : Modality} {Γ : Ctx} {R : RefTy} {x : Name}
  {mv : Idx Γ (LTy.mem (RefTy.struct x))} {hmv : (Ty.ref (RefTy.struct x)).mapFree = true} {rfld : Name}
  {hd : (Ty.ref R).defaultOkS = true},
  dl{ ⟨[ delete mv.rfld; ]⟩ ⇝ { memory := write(addM(memory), mv.rfld, freshId(addM(memory))) } ⟨[ ]⟩ }
-/
#guard_msgs in #check @Taclet.memoryFieldDeleteReference

/-! `tgt` is where the fresh array lands (`NewLhs`): a storage or a memory
location. -/

/--
info: @Taclet.newArrayCapture : ∀ {C : Contract} {k : Nat} {m : Modality} {Γ : Ctx} {R : RefTy} {tgt : NewLhs C Γ R}
  {se : Simple C Γ PrimTy.uint} {hn : R.newArrOk = true},
  dl{ ⟨[ tgt = new T(se); ]⟩ ⇝ ⟨[ T memory mv = new T(se); tgt = mv; ]⟩ }
-/
#guard_msgs in #check @Taclet.newArrayCapture

/--
info: @Taclet.storageLengthRead : ∀ {C : Contract} {k : Nat} {m : Modality} {Γ : Ctx} {x : PrimTy} {v : Idx Γ (LTy.val x)}
  {E : Ty} {sp : SPath C Γ E.array} {hlen : x = PrimTy.uint}, dl{ ⟨[ v = sp.length; ]⟩ ⇝ { v := sp.length } ⟨[ ]⟩ }
-/
#guard_msgs in #check @Taclet.storageLengthRead

/-! ### Declarations -/

/--
info: @Taclet.valueDeclSkip : ∀ {C : Contract} {k : Nat} {m : Modality} {Γ : Ctx} {p : PrimTy} {v : Var},
  dl{ ⟨[ T v; ]⟩ ⇝ { v := defVal(T) } ⟨[ ]⟩ }
-/
#guard_msgs in #check @Taclet.valueDeclSkip

/-! ### Compound assignment and `++`: `⊕` and `⊕⊕` are operator schema variables -/

/--
info: @Taclet.storageRootOpAssign : ∀ {C : Contract} {k : Nat} {m : Modality} {Γ : Ctx} {p : PrimTy} {op : BinOp} {gsp : Name}
  {se : Simple C Γ p}, dl{ ⟨[ gsp ⊕= se; ]⟩ ⇝ { storage := save(storage, gsp, find(storage, gsp) ⊕ se) } ⟨[ ]⟩ }
-/
#guard_msgs in #check @Taclet.storageRootOpAssign

/--
info: @Taclet.storageFieldIncrementAssignment : ∀ {C : Contract} {k : Nat} {m : Modality} {Γ : Ctx} {p : PrimTy}
  {v : Idx Γ (LTy.val p)} {op : IncDec} {x : Name} {sp : SPath C Γ (Ty.struct x)} {fld : Name}
  {hfld : C.fieldType x fld = some (Ty.prim p)} {hs : (OpLoc.field sp fld hfld).recvSimple = true},
  dl{ ⟨[ v = sp.fld⊕⊕; ]⟩ ⇝
    { storage := save(storage, sp.fld, find(storage, sp.fld) ± 1) ‖ v := find(storage, sp.fld)⊕⊕ } ⟨[ ]⟩ }
-/
#guard_msgs in #check @Taclet.storageFieldIncrementAssignment

/-! ### Arrays: a push is two nested writes over the length -/

/--
info: @Taclet.storagePushValueSave : ∀ {C : Contract} {k : Nat} {m : Modality} {Γ : Ctx} {x : PrimTy}
  {sp : SPath C Γ (Ty.prim x).array} {se : Simple C Γ x},
  dl{ ⟨[ sp .push(se); ]⟩ ⇝ { storage := save(save(storage, sp[sp.length], se), sp.length, sp.length + 1) } ⟨[ ]⟩ }
-/
#guard_msgs in #check @Taclet.storagePushValueSave

/-! ### Memory, and a copy from storage: an allocation is two elements -/

/--
info: @Taclet.memoryFieldWrite : ∀ {C : Contract} {k : Nat} {m : Modality} {Γ : Ctx} {x : Name}
  {mv : Idx Γ (LTy.mem (RefTy.struct x))} {hmv : (Ty.ref (RefTy.struct x)).mapFree = true} {fld : Name} {x_1 : PrimTy}
  {se : Simple C Γ x_1}, dl{ ⟨[ mv.fld = se; ]⟩ ⇝ { memory := write(memory, mv.fld, se) } ⟨[ ]⟩ }
-/
#guard_msgs in #check @Taclet.memoryFieldWrite

/--
info: @Taclet.memoryStorageCopy : ∀ {C : Contract} {k : Nat} {m : Modality} {Γ : Ctx} {x : RefTy} {mv : Idx Γ (LTy.mem x)}
  {sp : SPath C Γ (Ty.ref x)} {hm : (Ty.ref x).mapFree = true},
  dl{ ⟨[ mv = sp; ]⟩ ⇝
    { mv := freshId(copySt(memory, find(storage, sp))) ‖ memory := copySt(memory, find(storage, sp)) } ⟨[ ]⟩ }
-/
#guard_msgs in #check @Taclet.memoryStorageCopy

/-! ### With the notation off: the constructors it stands for

and the side condition the line leaves out: `sp` is simple (`Rules.lean`,
"Side conditions"), filled by `side_cond` wherever the rule is applied. -/

/--
info: @Taclet.storageFieldWriteSave : ∀ {C : Contract} {k : Nat} {m : Modality} {Γ : Ctx} {x : Name}
  {sp : SPath C Γ (Ty.struct x)} {fld : Name} {x_1 : PrimTy} {hfld : C.fieldType x fld = some (Ty.prim x_1)}
  {se : Simple C Γ x_1},
  autoParam (sp.isSimple = true) sideCond →
    Taclet C k m (Stmt.assign (Loc.field sp fld hfld) (Src.val (Val.simple se)))
      (Premise.update
        (Upd.nil.snoc
          (UpdElem.storage (Tms.STerm.save Tms.STerm.storage (Tms.PTerm.field sp.lower fld) (Tms.SValT.val se.lower)))))
-/
#guard_msgs in
set_option pp.sol.dl false in
#check @Taclet.storageFieldWriteSave

/-! ## A premise standing alone -/

/-- info: dl{ true } : Premise StandardExample [] [] -/
#guard_msgs in #check (Premise.done true : Premise StandardExample [] [])

/-! A block of statements, resolved (`Prog.resolve`), its locals left
in scope after it, quoted (`Premise.quote`) and type-checked
(`Meta.check`, the elaborator's checker). -/

/--
info: dl{ ⟨[ uint x = 1; alice.age = x; ]⟩ } : Premise StandardExample [] [LTy.val PrimTy.uint]
-/
#guard_msgs in
run_meta do
  let .ok ⟨_, P⟩ := Prog.resolve (C := StandardExample) [] sol{ uint x = 1; alice.age = x; }
    | throwError "the block does not resolve"
  let e := Premise.quote (Lean.mkConst ``StandardExample) (.unfold P .refl)
  Lean.Meta.check e
  Lean.logInfo m!"{e} : {← Lean.Meta.inferType e}"

section Scoped
open scoped Scoped

/-! ## A formula prints as it reads

`a != b` is `¬a = b`, and `balances[a] == 1` on a storage read is
`find(storage, balances[a]) = 1`: `==` compares program expressions, and
prints as the equation of their lowerings. -/

/--
info: dl{
  ∀ uint b;
    ∀ uint a; ¬a = b → [ balances[a] = 1; balances[b] = 2; ] find(storage, balances[a]) = 1 } : Fml StandardExample []
-/
#guard_msgs in #check dl!{ a != b → [ balances[a] = 1; balances[b] = 2; ] balances[a] == 1 }

/-! A comparison captured by a check, `{ se1 := x <= 255 }`, has no term
spelling of its own: the update element carries it, and prints as it reads. -/

/--
info: dl{ { x := 250 + 10 ‖ se1 := 250 + 10 <= 255 ‖ se2 := 1 < 2 } true } : Fml StandardExample []
-/
#guard_msgs in #check dl!{ { x := 250 + 10 ‖ se1 := 250 + 10 <= 255 ‖ se2 := 1 < 2 } true }

/-! What a rule leaves prints as `dl!{ … }` reads it; the last statement's
rule goes on to the postcondition (no `[ ]` left), and its update is the
box's (`dl![.box]{ … }`, as a box chain's last line is).  `#step`
(`Tools/Inspect.lean`) prints it. -/

/-- What a rule leaves reads back through `dl![.box]{ … }` as the term it is. -/
example : (dl!{ [ balances[a] = 1; ] balances[a] == 1 }).step =
    some dl![.box]{ { storage := save(storage, balances[a], 1) } find(storage, balances[a]) = 1 } :=
  rfl

/--
info:   ~[storageIndexWriteMappingSave]~>
    dl{ ∀ uint a; { storage := save(storage, balances[a], 1) } find(storage, balances[a]) = 1 }
-/
#guard_msgs in
#step dl!{ [ balances[a] = 1; ] balances[a] == 1 }

/-! ## The goals of a derivation are sequents

`Γ` is the context (parameters, preconditions and updates, in order), right
of `⟹` the formula still to prove. -/

/--
trace: ⊢ dl{ ⟹ ∀ uint b; ∀ uint a; ¬a = b → [ balances[a] = 1; balances[b] = 2; ] find(storage, balances[a]) = 1 }
---
trace: case h.h.h
⊢ dl{ ∀ uint b, ∀ uint a, ¬a = b ⟹ [ balances[a] = 1; balances[b] = 2; ] find(storage, balances[a]) = 1 }
---
trace: case h.h.h
⊢ dl{ ∀ uint b, ∀ uint a, ¬a = b, { storage := save(storage, balances[a], 1) } ⟹
    [ balances[b] = 2; ] find(storage, balances[a]) = 1 }
---
trace: case h.h.h
⊢ dl{ ∀ uint b, ∀ uint a, ¬a = b, { storage := save(storage, balances[a], 1) },
    { storage := save(storage, balances[b], 2) } ⟹ find(storage, balances[a]) = 1 }
-/
#guard_msgs in
/-- Two keys the precondition tells apart:
`a != b → [ balances[a] = 1; balances[b] = 2; ] balances[a] == 1`. -/
theorem twoKeys : ⊢ dl!{ a != b → [ balances[a] = 1; balances[b] = 2; ] balances[a] == 1 } := by
  trace_state
  apply Proves.allRight
  apply Proves.allRight
  apply Proves.impRight
  trace_state
  apply Proves.update (Taclet.toStep .storageIndexWriteMappingSave)
  trace_state
  apply Proves.update (Taclet.toStep .storageIndexWriteMappingSave)
  trace_state
  refine Proves.close [] rfl List.nodup_nil ?_
  sol_symex
  sol_close

end Scoped

/-! ## The rules of `⊢` are sequents

A rule of the scoped `Proves` (`Calculus/Proves.lean`) is
written as KeY writes its rule: a sequent over the rest `..H` of the
context, the premises above the conclusion.  `{U} [ ]` is an update produced
under the box.  `Proves.impRight`, `allRight` and `emptyModality` are
the constructors `intro`, `allIntro` and `empty` by solkey's names (theorems,
`Calculus/ProofTree.lean`); `sequentialToParallel` is the constructor
`merge`. -/

/--
info: @Proves.impRight : ∀ {C : Contract} {R : RuleSet} {Γ₀ Γ : Ctx} {H : Hyps C Γ₀ Γ} {a φ : Fml C Γ},
  dl{ ..H, a ⟹[R] φ } → dl{ ..H ⟹[R] a → φ }
-/
#guard_msgs in #check @Proves.impRight

/-! ### Sequents as input

Under `open scoped Solidity.Sequent` (`Calculus/SequentNotation.lean`)
a sequent is read as it prints: `dl{ ..H, a ⟹[R] φ }` is the scoped
judgement `Proves C R Γ₀ (H.pre a) φ`, its context a telescope
(`Hyps`) built from the left.  `sequentialToParallel` is the
constructor `merge`, past the hidden binders `bs` between the two updates
(Lean only), its side conditions computed. -/

section Sequents
open scoped Solidity.Sequent

/-- `sequentialToParallel` with no hidden binder between the two updates:
`{U}, {V}` become the one parallel update `W` (`Upd.seqPar`). -/
theorem sequentialToParallelNil {C : Contract} {R : RuleSet} {m : Modality} {Γ₀ Γ Δ Ε : Ctx}
    {H : Hyps C Γ₀ Γ} {U : Upd C Γ Δ} {V : Upd C Δ Ε} {W : Upd C Γ Ε}
    {φ : Fml C Ε} (hW : U.seqPar V = some W) :
    dl{ ..H, {W} ⟹[R] φ } → dl{ ..H, {U}, {V} ⟹[R] φ } :=
  Proves.merge (bs := []) rfl hW

/--
info: @sequentialToParallelNil : ∀ {C : Contract} {R : RuleSet} {m : Modality} {Γ₀ Γ Δ Ε : Ctx} {H : Hyps C Γ₀ Γ}
  {U : Upd C Γ Δ} {V : Upd C Δ Ε} {W : Upd C Γ Ε} {φ : Fml C Ε},
  U.seqPar V = some W → dl{ ..H, { W } ⟹[R] φ } → dl{ ..H, { U }, { V } ⟹[R] φ }
-/
#guard_msgs in #check @sequentialToParallelNil

set_option linter.unusedVariables false in
/-- The sequents build the context from the left (`(H.pre a).upd .box U`),
the program as `Prog.cons`, the frames empty: the same `Expr` (`=ₛ`). -/
example {C : Contract} (R : RuleSet) {Γ₀ Γ Δ Γ' Γ₁ : Ctx} (H : Hyps C Γ₀ Γ)
    (a φ : Fml C Γ) (U : Upd C Γ Δ) (ψ : Fml C Δ) (m : Modality) (x : Var)
    (p : PrimTy) (χ : Fml C (.val p :: Γ)) (s : Stmt C Γ Γ') (ω : Prog C Γ' Γ₁)
    (θ : Fml C Γ₁) : True := by
  guard_expr dl{ ..H, a ⟹[R] φ } =ₛ Proves C R Γ₀ (H.pre a) φ
  guard_expr dl{ ..H, a, {U} [ ] ⟹[R] ψ } =ₛ Proves C R Γ₀ ((H.pre a).upd .box U) ψ
  guard_expr dl{ ..H, {U} ⟹[R] ψ } =ₛ Proves C R Γ₀ (H.upd m U) ψ
  guard_expr dl{ ..H, ∀ p x ⟹[R] χ } =ₛ Proves C R Γ₀ (H.all x p) χ
  guard_expr dl{ ..H ⟹[R] ⟨[ s; ..ω ]⟩ θ } =ₛ Proves C R Γ₀ H (.modal m (.cons s ω) .nil θ)
  trivial

/-- A rule reads back as it prints (`Proves.impRight`, above). -/
example {C : Contract} {R : RuleSet} {Γ₀ Γ : Ctx} {H : Hyps C Γ₀ Γ} {a φ : Fml C Γ} :
    dl{ ..H, a ⟹[R] φ } → dl{ ..H ⟹[R] a → φ } :=
  Proves.impRight

end Sequents

end Solidity.Examples.Notation
