import Solidity.Calculus.Close
import Solidity.Calculus.Core.Surface
import Solidity.Calculus.Core.Derive
import Solidity.Tools.CoreInspect

/-!
# The notation, pinned

What the printers show, as `#guard_msgs` tests: a taclet as its rule line
(`Rules.lean`, `RuleSyntax.lean`), a premise standing alone, a formula read
by `dl!{ … }` and printed back (`Notation.lean`), and the goals of an `apply`
derivation as sequents `dl{ Γ ⟹ φ }` (`Logic.lean`).  If a printer changes,
these fail.

Everything here is the scoped calculus's: the rule lines are
`Core.Taclet`'s, printed by `Core.Delab` as today's print, the premises
`Core.Premise`'s, the rules of `⊢` `Core.Proves`'s, and the formulas and
the derivation read scoped (`open scoped Solidity.Core.Surface`, section
`Scoped`): a parameter is bound by `∀`, a formula is a `Core.Fml C []`.
Three rule lines `Core.Delab` does not print yet, today's `merge` and
today's sequent macros stay today's, each in a section that says so, until
W4 (`docs/intrinsic.md`).
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

/-! Today's rule: `Core.Delab` prints the scoped twin's hole (`SHole.fill`)
as its `match` (`#check_rule_text`'s list), until W4. -/

/--
info: @Taclet.storageFieldRead_unfold_rightFst : ∀ {C : Contract} {k : Nat} {m : Modality} {x : Ty} {lhs : Hole C x}
  {x_1 : Name} {nsp : SPath C (Ty.struct x_1)} {fld : Name},
  dl{ ⟨[ lhs = nsp.fld; ]⟩ ⇝ ⟨[ T storage sp = nsp; lhs = sp.fld; ]⟩ }
-/
#guard_msgs in #check @Taclet.storageFieldRead_unfold_rightFst

/-! ### Step 2: a write, source, receiver and index captured in that order -/

/--
info: @Core.Taclet.storageIndexWriteCaptureAllComplexRecv : ∀ {C : Contract} {k : Nat} {m : Modality} {Γ : Core.Ctx}
  {x : RefTy} {x_1 x_2 : PrimTy} {it : IndexTy x x_1 (Ty.prim x_2)} {nsp : Core.SPath C Γ (Ty.ref x)}
  {e₁ : Core.Val C Γ x_1} {e₂ : Core.Val C Γ x_2},
  dl{ ⟨[ nsp[e₁] = e₂; ]⟩ ⇝ ⟨[ T se = e₂; T storage sp = nsp; T ie = e₁; sp[ie] = se; ]⟩ }
-/
#guard_msgs in #check @Core.Taclet.storageIndexWriteCaptureAllComplexRecv

/-! ### Step 3: a statement with simple parts is an update -/

/--
info: @Core.Taclet.storageFieldWriteSave : ∀ {C : Contract} {k : Nat} {m : Modality} {Γ : Core.Ctx} {x : Name}
  {sp : Core.SPath C Γ (Ty.struct x)} {fld : Name} {x_1 : PrimTy} {se : Core.Simple C Γ x_1},
  dl{ ⟨[ sp.fld = se; ]⟩ ⇝ { storage := save(storage, sp.fld, se) } ⟨[ ]⟩ }
-/
#guard_msgs in #check @Core.Taclet.storageFieldWriteSave

/-! ### Memory `delete`, `new T[](n)`, `.length` -/

/--
info: @Core.Taclet.memoryFieldDeleteReference : ∀ {C : Contract} {k : Nat} {m : Modality} {Γ : Core.Ctx} {R : RefTy}
  {x : Name} {mv : Core.Idx Γ (Core.LTy.mem (RefTy.struct x))} {hmv : (Ty.ref (RefTy.struct x)).mapFree = true}
  {rfld : Name} {hd : (Ty.ref R).defaultOkS = true},
  dl{ ⟨[ delete mv.rfld; ]⟩ ⇝ { memory := write(addM(memory), mv.rfld, freshId(addM(memory))) } ⟨[ ]⟩ }
-/
#guard_msgs in #check @Core.Taclet.memoryFieldDeleteReference

/-! Today's rule: the scoped twin's target (`NewLhs`) prints as its `match`,
until W4. -/

/--
info: @Taclet.newArrayCapture : ∀ {C : Contract} {k : Nat} {m : Modality} {R : RefTy} {tgt : NewLhs C R}
  {se : Simple C PrimTy.uint} {hn : R.newArrOk = true},
  dl{ ⟨[ tgt = new T(se); ]⟩ ⇝ ⟨[ T memory mv = new T(se); tgt = mv; ]⟩ }
-/
#guard_msgs in #check @Taclet.newArrayCapture

/--
info: @Core.Taclet.storageLengthRead : ∀ {C : Contract} {k : Nat} {m : Modality} {Γ : Core.Ctx} {x : PrimTy}
  {v : Core.Idx Γ (Core.LTy.val x)} {E : Ty} {sp : Core.SPath C Γ E.array} {hlen : x = PrimTy.uint},
  dl{ ⟨[ v = sp.length; ]⟩ ⇝ { v := sp.length } ⟨[ ]⟩ }
-/
#guard_msgs in #check @Core.Taclet.storageLengthRead

/-! ### Declarations -/

/--
info: @Core.Taclet.valueDeclSkip : ∀ {C : Contract} {k : Nat} {m : Modality} {Γ : Core.Ctx} {p : PrimTy} {v : Var},
  dl{ ⟨[ T v; ]⟩ ⇝ { v := defVal(T) } ⟨[ ]⟩ }
-/
#guard_msgs in #check @Core.Taclet.valueDeclSkip

/-! ### Compound assignment and `++`: `⊕` and `⊕⊕` are operator schema variables -/

/--
info: @Core.Taclet.storageRootOpAssign : ∀ {C : Contract} {k : Nat} {m : Modality} {Γ : Core.Ctx} {p : PrimTy} {op : BinOp}
  {gsp : Name} {se : Core.Simple C Γ p},
  dl{ ⟨[ gsp ⊕= se; ]⟩ ⇝ { storage := save(storage, gsp, find(storage, gsp) ⊕ se) } ⟨[ ]⟩ }
-/
#guard_msgs in #check @Core.Taclet.storageRootOpAssign

/-! Today's rule: `Core.Delab` fails on the scoped twin's statement, until
W4. -/

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
info: @Core.Taclet.storagePushValueSave : ∀ {C : Contract} {k : Nat} {m : Modality} {Γ : Core.Ctx} {x : PrimTy}
  {sp : Core.SPath C Γ (Ty.prim x).array} {se : Core.Simple C Γ x},
  dl{ ⟨[ sp .push(se); ]⟩ ⇝ { storage := save(save(storage, sp[sp.length], se), sp.length, sp.length + 1) } ⟨[ ]⟩ }
-/
#guard_msgs in #check @Core.Taclet.storagePushValueSave

/-! ### Memory, and a copy from storage: an allocation is two elements -/

/--
info: @Core.Taclet.memoryFieldWrite : ∀ {C : Contract} {k : Nat} {m : Modality} {Γ : Core.Ctx} {x : Name}
  {mv : Core.Idx Γ (Core.LTy.mem (RefTy.struct x))} {hmv : (Ty.ref (RefTy.struct x)).mapFree = true} {fld : Name}
  {x_1 : PrimTy} {se : Core.Simple C Γ x_1}, dl{ ⟨[ mv.fld = se; ]⟩ ⇝ { memory := write(memory, mv.fld, se) } ⟨[ ]⟩ }
-/
#guard_msgs in #check @Core.Taclet.memoryFieldWrite

/--
info: @Core.Taclet.memoryStorageCopy : ∀ {C : Contract} {k : Nat} {m : Modality} {Γ : Core.Ctx} {x : RefTy}
  {mv : Core.Idx Γ (Core.LTy.mem x)} {sp : Core.SPath C Γ (Ty.ref x)} {hm : (Ty.ref x).mapFree = true},
  dl{ ⟨[ mv = sp; ]⟩ ⇝
    { mv := freshId(copySt(memory, find(storage, sp))) ‖ memory := copySt(memory, find(storage, sp)) } ⟨[ ]⟩ }
-/
#guard_msgs in #check @Core.Taclet.memoryStorageCopy

/-! ### With the notation off: the constructors it stands for

and the side condition the line leaves out: `sp` is simple (`Rules.lean`,
"Side conditions"), filled by `side_cond` wherever the rule is applied. -/

/--
info: @Core.Taclet.storageFieldWriteSave : ∀ {C : Contract} {k : Nat} {m : Modality} {Γ : Core.Ctx} {x : Name}
  {sp : Core.SPath C Γ (Ty.struct x)} {fld : Name} {x_1 : PrimTy} {hfld : C.fieldType x fld = some (Ty.prim x_1)}
  {se : Core.Simple C Γ x_1},
  autoParam (sp.isSimple = true) sideCond →
    Core.Taclet C k m (Core.Stmt.assign (Core.Loc.field sp fld hfld) (Core.Src.val (Core.Val.simple se)))
      (Core.Premise.update
        (Core.Upd.nil.snoc
          (Core.UpdElem.storage
            (Core.Tms.STerm.save Core.Tms.STerm.storage (Core.Tms.PTerm.field sp.lower fld)
              (Core.Tms.SValT.val se.lower)))))
-/
#guard_msgs in
set_option pp.sol.dl false in
#check @Core.Taclet.storageFieldWriteSave

/-! ## A premise standing alone -/

/-- info: dl{ true } : Core.Premise StandardExample [] [] -/
#guard_msgs in #check (Core.Premise.done true : Core.Premise StandardExample [] [])

/-! A block of statements, resolved (`Core.Prog.resolve`), its locals left
in scope after it, quoted (`Core.Premise.quote`) and checked by the
kernel's type checker. -/

/--
info: dl{ ⟨[ uint x = 1; alice.age = x; ]⟩ } : Core.Premise StandardExample [] [Core.LTy.val PrimTy.uint]
-/
#guard_msgs in
run_meta do
  let .ok ⟨_, P⟩ := Core.Prog.resolve (C := StandardExample) [] sol{ uint x = 1; alice.age = x; }
    | throwError "the block does not resolve"
  let e := Core.Premise.quote (Lean.mkConst ``StandardExample) (.unfold P .refl)
  Lean.Meta.check e
  Lean.logInfo m!"{e} : {← Lean.Meta.inferType e}"

section Scoped
open scoped Solidity.Core.Surface

/-! ## A formula prints as it reads

`a != b` is `¬a = b`, and `balances[a] == 1` on a storage read is
`find(storage, balances[a]) = 1`: `==` compares program expressions, and
prints as the equation of their lowerings. -/

/--
info: dl{
  ∀ uint b;
    ∀ uint a;
      ¬a = b → [ balances[a] = 1; balances[b] = 2; ] find(storage, balances[a]) = 1 } : Core.Fml StandardExample []
-/
#guard_msgs in #check dl!{ a != b → [ balances[a] = 1; balances[b] = 2; ] balances[a] == 1 }

/-! A comparison captured by a check, `{ se1 := x <= 255 }`, has no term
spelling of its own: the update element carries it, and prints as it reads. -/

/--
info: dl{ { x := 250 + 10 ‖ se1 := 250 + 10 <= 255 ‖ se2 := 1 < 2 } true } : Core.Fml StandardExample []
-/
#guard_msgs in #check dl!{ { x := 250 + 10 ‖ se1 := 250 + 10 <= 255 ‖ se2 := 1 < 2 } true }

/-! What a rule leaves prints as `dl!{ … }` reads it; the last statement's
rule goes on to the postcondition (no `[ ]` left), and its update is the
box's (`dl![.box]{ … }`, as a box chain's last line is).  `#step`
(`Tools/CoreInspect.lean`) prints it. -/

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
  apply Core.Proves.allRight
  apply Core.Proves.allRight
  apply Core.Proves.impRight
  trace_state
  apply Core.Proves.update (Core.Taclet.toStep .storageIndexWriteMappingSave)
  trace_state
  apply Core.Proves.update (Core.Taclet.toStep .storageIndexWriteMappingSave)
  trace_state
  refine Core.Proves.close [] rfl List.nodup_nil ?_
  sol_symex
  sol_close

end Scoped

/-! ## The rules of `⊢` are sequents

A constructor of `Proves` is written as KeY writes its rule: a sequent over
the rest `..Γ` of the context, the premises above the conclusion.  `{U} [ ]`
is an update produced under the box.  `impRight`, `allRight`,
`emptyModality`, `sequentialToParallel`, `simplifyUpdate` and
`applyOnRigidFormula` are the constructors' aliases by solkey's names
(theorems, `Calculus/Logic.lean`). -/

/--
info: @Core.Proves.impRight : ∀ {C : Contract} {R : RuleSet} {Γ₀ Γ : Core.Ctx} {H : Core.Hyps C Γ₀ Γ} {a φ : Core.Fml C Γ},
  dl{ ..H, a ⟹[R] φ } → dl{ ..H ⟹[R] a → φ }
-/
#guard_msgs in #check @Core.Proves.impRight

/-! ### Today's, until W4

Today's `merge`, which the scoped sequent states otherwise (`Core.Proves.merge`
merges past hidden binders, its side conditions computed), and today's
sequent macros, which have no scoped input form: the scoped goals print as
sequents (above) but are written as `Core.Proves` terms. -/

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
