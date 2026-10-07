import Solidity.Calculus.Core.Arms

/-!
# The rules of the statements that hold blocks

`Completeness.lean`'s arms for calls, `try` and loops over the scoped
syntax (`docs/intrinsic.md`, M6a), and the loop frame they need
(`Mutability.lean`'s `Prog.loopFrame`).

* **A call** (`internalCallExpand`, `functionBodyExpand`) is inlined as
  KeY's `expand_function_body` writes it: the parameters declared with the
  arguments, the return variables declared, the body, the result assigned.
  The body is closed over its frame `rs ++ ps`, so it is read under the
  caller's locals once (`Prog.wk (Thin.atop …)`), as a block.  After it,
  the frame is popped (`Premise.unfold`), or, when the call leaves its
  return variables (`CallRet.rets`, a memory return), dropped from under
  them (`Premise.inline`, a `Thin`).  An argument that is not simple is
  captured first, the leftmost first (`functionCallArgCapture`).
* **A `try`** has a goal per clause, each a block with the locals its
  outcome binds (`Premise.branches`, `tryCallNoCallbackBox`).
* **A loop** is unwound (`whileUnwind`: `if (c) { { body } while (c) body }`,
  the body a block, so the loop after it reads the loop's own context), ends
  (`loopExit`), or is proved by its invariant (`whileInvariantBox`,
  `whileInvariantDiamond`).  The invariant rule's frame anonymises the
  locals of the loop's context the body writes; the body's own locals are
  popped every iteration, so, unlike `Prog.loopFrame`, it does not list
  them (a deviation of the erasure, not of the rule).
-/

namespace Solidity.Core

open Solidity (Modality Mutability)

variable {C : Contract}

/-! ## Calls -/

section Calls

variable {Γ : Ctx}

/-- A value read with the locals `ρ` pushed on its context. -/
def Val.unders {p : PrimTy} (v : Val C Γ p) : (ρ : Ctx) → Val C (ρ ++ Γ) p
  | [] => v
  | _ :: ρ => (v.unders ρ).up

/-- The arguments read with one local more on top. -/
def Args.up {t : LTy} : {ps : Ctx} → Args C Γ ps → Args C (t :: Γ) ps
  | _, as => Args.casesOn (motive := fun ps _ => Args C (t :: Γ) ps) as .nil
      (fun as p x e => .snoc (Args.up as) p x e.up)
  termination_by structural _ as => as

/-- The leftmost argument that is not simple, and the arguments read with it
captured on top: it replaced by the capture, the others shifted. -/
def Args.capture : {ps : Ctx} → Args C Γ ps →
    Option ((p : PrimTy) × Val C Γ p × Args C (.val p :: Γ) ps)
  | _, as => Args.casesOn
      (motive := fun ps _ => Option ((p : PrimTy) × Val C Γ p × Args C (.val p :: Γ) ps)) as none
      (fun as p' x e => match Args.capture as with
        | some ⟨p, v, as'⟩ => some ⟨p, v, .snoc as' p' x e.up⟩
        | none => if e.isSimple then none else some ⟨p', e, .snoc as.up p' x (.simple (.local .here))⟩)
  termination_by structural _ as => as

/-- `T x = e; …; rest`: the parameters declared with their arguments, in
order, each argument read under the parameters before it. -/
def Args.declsThen {Δ : Ctx} : {ps : Ctx} → Args C Γ ps → Prog C (ps ++ Γ) Δ → Prog C Γ Δ
  | _, as => Args.casesOn (motive := fun ps _ => Prog C (ps ++ Γ) Δ → Prog C Γ Δ) as (fun rest => rest)
      (fun {ps'} as p x e rest => Args.declsThen as (.cons (.declLocal p x (some (e.unders ps'))) rest))
  termination_by structural _ as => as

/-- `T r; …; rest`: the locals of the binders declared at their defaults. -/
def Binders.declsThen {Δ : Ctx} : {ρ : Ctx} → Binders ρ → Prog C (ρ ++ Γ) Δ → Prog C Γ Δ
  | _, bs => Binders.casesOn (motive := fun ρ _ => Prog C (ρ ++ Γ) Δ → Prog C Γ Δ) bs (fun rest => rest)
      (fun bs p x rest => Binders.declsThen bs (.cons (.declLocal p x none) rest))
  termination_by structural _ bs => bs

/-- A call (`callStep`): its leftmost argument that is not simple captured
(`functionCallArgCapture`), or, with every argument simple, its body
inlined (`internalCallExpand`; `functionBodyExpand` for one that returns to
targets). -/
def callStep (k : Nat) {Γ' ps rs Γf : Ctx} (f : Name) (args : Args C Γ ps) (ret : CallRet Γ rs Γ')
    (body : Prog C (rs ++ ps) Γf) : Option (Premise C Γ Γ') :=
  CallRet.casesOn (motive := fun rs Γ' _ => Prog C (rs ++ ps) Γf → Option (Premise C Γ Γ')) ret
    (fun body => match args.capture with
      | some ⟨p, v, as'⟩ => some (.capture p (fse k) v (.call f as' .none body))
      | none => some (.unfold (args.declsThen
          (.cons (.block (body.wk (Thin.atop ps Γ)).2.2) .nil)) (Ext.append Γ ps)))
    (fun p r res body => match args.capture with
      | some ⟨p', v, as'⟩ => some (.capture p' (fse k) v (.call f as' (.val p r (res.map .there)) body))
      | none =>
        let result : Prog C (.val p :: (ps ++ Γ)) (.val p :: (ps ++ Γ)) := match res with
          | none => .nil
          | some j => .cons (.assignLocal (j.under ps).there (.simple (.local .here))) .nil
        some (.unfold (args.declsThen (.cons (.declLocal p r none)
          (.cons (.block (body.wk (Thin.atop (.val p :: ps) Γ)).2.2) result)))
          (.push (Ext.append Γ ps))))
    (fun {rs} bs body => match args.capture with
      | some ⟨p', v, as'⟩ => some (.inline
          (.cons (.declLocal p' (fse k) (some v)) (.cons (.call f as' (.rets bs) body) .nil))
          (Thin.keepAll rs (.drop .refl)))
      | none => some (.inline (args.declsThen (bs.declsThen
          (.cons (.block (body.wk (Thin.keepAll rs (Thin.atop ps Γ))).2.2) .nil)))
          (Thin.keepAll rs (Thin.ofExt (Ext.append Γ ps)))))
    (fun R r hd hm body => match args.capture with
      | some ⟨p', v, as'⟩ => some (.inline
          (.cons (.declLocal p' (fse k) (some v)) (.cons (.call f as' (.mem R r hd hm) body) .nil))
          (.keep (.drop .refl)))
      | none => some (.inline (args.declsThen (.cons (.declMem R r none hd hm)
          (.cons (.block (body.wk (Thin.atop (.mem R :: ps) Γ)).2.2) .nil)))
          (.keep (Thin.ofExt (Ext.append Γ ps)))))
    body

end Calls

/-! ## `try` -/

/-- The `Panic` clause's code as binders. -/
def CodeBinder.binders : {κ : Ctx} → CodeBinder κ → Binders κ
  | _, c => CodeBinder.casesOn (motive := fun κ _ => Binders κ) c .nil (fun x => Binders.nil.snoc .uint x)

/-- `try …` (`tryStep`): a goal per clause under the box
(`tryCallNoCallbackBox`), `false` under the diamond (`tryCallDiamond`, Lean). -/
def tryStep (m : Modality) {Γ ρ κ Γ₁ Γ₂ Γ₃ Γ₄ : Ctx} (rets : Binders ρ) (ok : Prog C (ρ ++ Γ) Γ₁)
    (err : Prog C Γ Γ₂) (code : CodeBinder κ) (pnc : Prog C (κ ++ Γ) Γ₃) (other : Prog C Γ Γ₄) :
    Option (Premise C Γ Γ) :=
  match m with
  | .box => some (.branches [⟨rets, ok⟩, ⟨Binders.nil, err⟩, ⟨code.binders, pnc⟩, ⟨Binders.nil, other⟩])
  | .diamond => some (.done false)

/-! ## The loop frame -/

section Frame

variable {Γ : Ctx}

/-- `v` reads something other than locals (`Mutability.lean`'s `Val.readsState`). -/
def Val.readsState : {p : PrimTy} → Val C Γ p → Bool
  | _, .simple (.env ..) => true
  | _, .simple _ => false
  | _, .read _ | _, .readMem _ | _, .len .. | _, .mlen .. => true
  | _, .binop _ _ _ a b => a.readsState || b.readsState
  | _, .unop _ _ _ a => a.readsState
  | _, .ternary c a b => c.readsState || a.readsState || b.readsState

/-- A callee of mutability `μ` may evaluate `v`. -/
def Val.readsIn {p : PrimTy} (μ : Mutability) (v : Val C Γ p) : Bool := μ != .pure || !v.readsState

/-- The target of `x += e` or `x++` is a stack local, or in storage. -/
def OpLoc.isLocal {p : PrimTy} : OpLoc C Γ p → Bool
  | .local _ => true
  | _ => false

def OpLoc.isStorage {p : PrimTy} : OpLoc C Γ p → Bool
  | .root .. | .field .. | .index .. => true
  | _ => false

/-- What a callee of mutability `μ` may write by `x ⊕= e` or `x++`. -/
def OpLoc.writableIn {p : PrimTy} (μ : Mutability) (l : OpLoc C Γ p) : Bool :=
  l.isLocal || μ == .nonpayable && l.isStorage

/-- Every argument may be evaluated by a callee of mutability `μ`. -/
def Args.readsIn (μ : Mutability) : {ps : Ctx} → Args C Γ ps → Bool
  | _, as => Args.casesOn (motive := fun _ _ => Bool) as true
      (fun as _ _ e => Args.readsIn μ as && e.readsIn μ)
  termination_by structural _ as => as

/-- No memory return (its body would allocate, which no frame allows). -/
def CallRet.noMem {rs Γ' : Ctx} (r : CallRet Γ rs Γ') : Bool :=
  CallRet.casesOn (motive := fun _ _ _ => Bool) r true (fun _ _ _ => true) (fun _ => true)
    (fun _ _ _ _ => false)

/-- A position of `Γ'` read as one of the context `d` locals below it, if it
is one. -/
def Idx.outer {Γ' : Ctx} {t : LTy} (d : Nat) (i : Idx Γ' t) : List (LTy × Nat) :=
  if d ≤ i.toNat then [(t, i.toNat - d)] else []

/-- The locals the call writes in its caller: where its result lands. -/
def CallRet.writesAt (d : Nat) {rs Γ' : Ctx} (r : CallRet Γ rs Γ') : List (LTy × Nat) :=
  CallRet.casesOn (motive := fun _ _ _ => List (LTy × Nat)) r []
    (fun _ _ res => match res with
      | .some j => j.outer d
      | .none => [])
    (fun _ => []) (fun _ _ _ _ => [])

/-- The local `x ⊕= e` or `x++` writes, if its target is one. -/
def OpLoc.writesAt (d : Nat) {p : PrimTy} : OpLoc C Γ p → List (LTy × Nat)
  | .local i => i.outer d
  | _ => []

mutual

/-- **A statement a callee of mutability `μ` may run** (`Mutability.lean`'s
`Stmt.within`): one writing locals only (`view`, reading no state if
`pure`), or storage and the ledger (`nonpayable`). -/
def Stmt.within (μ : Mutability) : {Γ Γ' : Ctx} → Stmt C Γ Γ' → Bool
  | _, _, s => Stmt.casesOn (motive_1 := fun _ _ _ => Bool) s
    (assign := fun _ _ => μ == .nonpayable) (rebind := fun _ _ => false)
    (assignLocal := fun _ r => r.readsIn μ)
    (declLocal := fun _ _ init => match init with
      | none => true
      | some e => e.readsIn μ)
    (declStorage := fun _ _ _ => false)
    (opAssign := fun _ _ _ l r => r.readsIn μ && l.writableIn μ)
    (incDec := fun _ _ l => l.writableIn μ) (assignIncDec := fun _ _ _ l _ => l.writableIn μ)
    (push := fun _ _ _ => false) (pop := fun _ => false)
    (transfer := fun _ _ => μ == .nonpayable) (send := fun _ _ _ => μ == .nonpayable)
    (declMem := fun _ _ _ _ _ => false) (rebindMem := fun _ _ => false)
    (assignFromMem := fun _ _ => false) (assignMem := fun _ _ => false)
    (delete := fun _ => μ == .nonpayable) (deleteMem := fun _ _ => false)
    (assignNew := fun _ _ _ => false)
    (ite := fun c thn els => c.readsIn μ && Prog.within μ thn && Prog.within μ els)
    (require := fun c => c.readsIn μ) (assert := fun c => c.readsIn μ) (revert := true)
    (call := fun _ args ret body => args.readsIn μ && ret.noMem && Prog.within μ body)
    (tryCall := fun _ _ _ _ _ _ _ => false)
    (loop := fun _ c body => c.readsIn μ && Prog.within μ body)
    (block := fun body => Prog.within μ body)
  termination_by structural _ _ s => s

def Prog.within (μ : Mutability) : {Γ Γ' : Ctx} → Prog C Γ Γ' → Bool
  | _, _, P => Prog.casesOn (motive_2 := fun _ _ _ => Bool) P true
      (fun s P => Stmt.within μ s && Prog.within μ P)
  termination_by structural _ _ P => P

end

mutual

/-- The locals of the context `d` locals below `s`'s that `s` may write,
by type and position there (`Mutability.lean`'s `Stmt.writes`, less the
locals `s`'s own scopes declare). -/
def Stmt.writesAt (d : Nat) : {Γ Γ' : Ctx} → Stmt C Γ Γ' → List (LTy × Nat)
  | _, _, s => Stmt.casesOn (motive_1 := fun _ _ _ => List (LTy × Nat)) s
    (assign := fun _ _ => []) (rebind := fun _ _ => []) (assignLocal := fun i _ => i.outer d)
    (declLocal := fun _ _ _ => []) (declStorage := fun _ _ _ => [])
    (opAssign := fun _ _ _ l _ => l.writesAt d) (incDec := fun _ _ l => l.writesAt d)
    (assignIncDec := fun i _ _ l _ => i.outer d ++ l.writesAt d)
    (push := fun _ _ _ => []) (pop := fun _ => []) (transfer := fun _ _ => [])
    (send := fun pv _ _ => pv.outer d)
    (declMem := fun _ _ _ _ _ => []) (rebindMem := fun _ _ => []) (assignFromMem := fun _ _ => [])
    (assignMem := fun _ _ => []) (delete := fun _ => []) (deleteMem := fun _ _ => [])
    (assignNew := fun _ _ _ => [])
    (ite := fun _ thn els => Prog.writesAt d thn ++ Prog.writesAt d els)
    (require := fun _ => []) (assert := fun _ => []) (revert := [])
    (call := fun _ _ ret _ => ret.writesAt d) (tryCall := fun _ _ _ _ _ _ _ => [])
    (loop := fun _ _ body => Prog.writesAt d body) (block := fun body => Prog.writesAt d body)
  termination_by structural _ _ s => s

def Prog.writesAt (d : Nat) : {Γ Γ' : Ctx} → Prog C Γ Γ' → List (LTy × Nat)
  | _, _, P => Prog.casesOn (motive_2 := fun _ _ _ => List (LTy × Nat)) P []
      (fun s P => Stmt.writesAt d s ++ Prog.writesAt (d + s.ext.depth) P)
  termination_by structural _ _ P => P

end

/-- **The frame of a loop body** (`Mutability.lean`'s `Prog.loopFrame`): the
locals of the loop's context it writes, and whether it writes the storage
and the ledger too; `none` when it does more. -/
def Prog.frame {Γ₁ : Ctx} (P : Prog C Γ Γ₁) : Option (List ((t : LTy) × Idx Γ t) × Bool) :=
  let xs := (Prog.writesAt 0 P).filterMap fun (t, n) => (Γ.idx? n t).map (⟨t, ·⟩)
  if Prog.within .view P then some (xs, false)
  else if Prog.within .nonpayable P then some (xs, true)
  else none

end Frame

/-! ## Loops -/

/-- A loop (`loopStep`): unwound (`whileUnwind`), ended (`loopExit`), or by
its invariant (`whileInvariantBox`, `whileInvariantDiamond`, under the
diamond with a cover goal, `Fml.invCases`), closed to
`false` when its body has no frame (`whileClose`) or, under the diamond,
it has no variant (`whileNoVariantDiamond`). -/
def loopStep (k : Nat) (m : Modality) {Γ Γ₁ : Ctx} (a : LoopAnn C Γ) (c : Val C Γ .bool)
    (body : Prog C Γ Γ₁) : Option (Premise C Γ Γ) :=
  match a with
  -- loopExit
  | .unwind 0 => some (.check (.eqD c.lower (Tm.lit (.bool false))))
  -- whileUnwind
  | .unwind (n + 1) =>
    some (.unfold (.cons (.ite c (.cons (.block body) (.cons (.loop (.unwind n) c body) .nil)) .nil) .nil)
      .refl)
  | .inv I dec =>
    match body.frame with
    -- whileClose
    | none => some (.done false)
    | some (xs, hv) =>
      match m, dec with
      -- whileInvariantBox
      | .box, _ =>
        some (.inv (.isBoolD I.lower true) xs hv (Upd.nil.decl (fse k) (.val (p := .bool) c.lower))
          (.isBoolD (.pvV (p := .bool) .here) true) (.isBoolD (.pvV (p := .bool) .here) false)
          .refl (.push .refl) body (.isBoolD I.lower true))
      -- whileInvariantDiamond
      | .diamond, some d =>
        let U : Upd C Γ (.val .bool :: .val .uint :: Γ) :=
          (Upd.nil.decl (fie k) (.val (p := .uint) d.lower)).decl (fse k) (.val (p := .bool) c.lower)
        let d' : Tm C (.val .bool :: .val .uint :: Γ) .val := (d.up.up).lower
        let post : Fml C (.val .uint :: Γ) :=
          .and (.isBoolD I.up.lower true)
            (.upd .diamond (Upd.nil.decl (fse k) (.val (p := .bool) c.up.lower))
              (.imp (.isBoolD (.pvV (p := .bool) .here) true)
                (.and (.isBoolD (.app2 (.binop .le .uint) (Tm.lit (.int 0)) d') true)
                  (.isBoolD (.app2 (.binop .lt .uint) d' (.pvV (p := .uint) (.there .here))) true))))
        some (.inv (.isBoolD I.lower true) xs hv U
          (.isBoolD (.pvV (p := .bool) .here) true) (.isBoolD (.pvV (p := .bool) .here) false)
          (.push .refl) (.push .refl) (body.wk up).2.2 post)
      -- whileNoVariantDiamond
      | .diamond, none => some (.done false)

end Solidity.Core
