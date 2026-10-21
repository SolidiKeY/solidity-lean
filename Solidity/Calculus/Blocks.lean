import Solidity.Calculus.Arms
import Solidity.Semantics.NoPanic

/-!
# The rules of the statements that hold blocks

master's arms for calls, `try` and loops (`Calculus/Completeness.lean` at
`ad728b16`) over the scoped syntax (`docs/intrinsic.md`, M6a), and the loop
frame they need (master's `Prog.loopFrame`, at `ad728b16`).

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
  popped every iteration, so, unlike master's `Prog.loopFrame`, it does not
  list them (the frame differs from master's, not the rule).
-/

namespace Solidity

open Solidity (Modality Mutability)

variable {C : Contract}

/-! ## Calls -/

section Calls

variable {Γ : Ctx}

/-- A value read with the locals `ρ` pushed on its context. -/
def Val.unders {p : PrimTy} (v : Val C Γ p) : (ρ : Ctx) → Val C (ρ ++ Γ) p
  | [] => v
  | _ :: ρ => (v.unders ρ).up

def SPath.unders {T : Ty} (v : SPath C Γ T) : (ρ : Ctx) → SPath C (ρ ++ Γ) T
  | [] => v
  | _ :: ρ => (v.unders ρ).up

def MPath.unders {T : Ty} (v : MPath C Γ T) : (ρ : Ctx) → MPath C (ρ ++ Γ) T
  | [] => v
  | _ :: ρ => (v.unders ρ).up

/-- The arguments read with one local more on top. -/
def Args.up {t : LTy} : {ps : Ctx} → Args C Γ ps → Args C (t :: Γ) ps
  | _, as => Args.casesOn (motive := fun ps _ => Args C (t :: Γ) ps) as .nil
      (fun as p x e => .snoc (Args.up as) p x e.up)
      (fun as R x e => .snocStorage (Args.up as) R x e.up)
      (fun as R x e => .snocMemory (Args.up as) R x e.up)
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
      (fun as R x e => match Args.capture as with
        | some ⟨p, v, as'⟩ => some ⟨p, v, .snocStorage as' R x e.up⟩
        | none => none)
      (fun as R x e => match Args.capture as with
        | some ⟨p, v, as'⟩ => some ⟨p, v, .snocMemory as' R x e.up⟩
        | none => none)
  termination_by structural _ as => as

/-- `T x = e; …; rest`: the parameters declared with their arguments, in
order, each argument read under the parameters before it. -/
def Args.declsThen {Δ : Ctx} : {ps : Ctx} → Args C Γ ps → Prog C (ps ++ Γ) Δ → Prog C Γ Δ
  | _, as => Args.casesOn (motive := fun ps _ => Prog C (ps ++ Γ) Δ → Prog C Γ Δ) as (fun rest => rest)
      (fun {ps'} as p x e rest => Args.declsThen as (.cons (.declLocal p x (some (e.unders ps'))) rest))
      (fun {ps'} as R x e rest =>
        Args.declsThen as (.cons (.declStorage R x (some (.path (e.unders ps')))) rest))
      (fun {ps'} as R x e rest =>
        Args.declsThen as (.cons (.declMem R x (some (.alias (e.unders ps'))) rfl e.mapFree) rest))
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
    (body : Prog C (rs ++ ps) Γf) : Premise C Γ Γ' :=
  CallRet.casesOn (motive := fun rs Γ' _ => Prog C (rs ++ ps) Γf → Premise C Γ Γ') ret
    (fun body => match args.capture with
      | some ⟨p, v, as'⟩ => .capture p (fse k) v (.call f as' .none body)
      | none => .unfold (args.declsThen
          (.cons (.block (body.wk (Thin.atop ps Γ)).2.2) .nil)) (Ext.append Γ ps))
    (fun p r res body => match args.capture with
      | some ⟨p', v, as'⟩ => .capture p' (fse k) v (.call f as' (.val p r (res.map .there)) body)
      | none =>
        let result : Prog C (.val p :: (ps ++ Γ)) (.val p :: (ps ++ Γ)) := match res with
          | none => .nil
          | some j => .cons (.assignLocal (j.under ps).there (.simple (.local .here))) .nil
        .unfold (args.declsThen (.cons (.declLocal p r none)
          (.cons (.block (body.wk (Thin.atop (.val p :: ps) Γ)).2.2) result)))
          (.push (Ext.append Γ ps)))
    (fun {rs} bs body => match args.capture with
      | some ⟨p', v, as'⟩ => .inline
          (.cons (.declLocal p' (fse k) (some v)) (.cons (.call f as' (.rets bs) body) .nil))
          (Thin.keepAll rs (.drop .refl))
      | none => .inline (args.declsThen (bs.declsThen
          (.cons (.block (body.wk (Thin.keepAll rs (Thin.atop ps Γ))).2.2) .nil)))
          (Thin.keepAll rs (Thin.ofExt (Ext.append Γ ps))))
    (fun R r hd hm body => match args.capture with
      | some ⟨p', v, as'⟩ => .inline
          (.cons (.declLocal p' (fse k) (some v)) (.cons (.call f as' (.mem R r hd hm) body) .nil))
          (.keep (.drop .refl))
      | none => .inline (args.declsThen (.cons (.declMem R r none hd hm)
          (.cons (.block (body.wk (Thin.atop (.mem R :: ps) Γ)).2.2) .nil)))
          (.keep (Thin.ofExt (Ext.append Γ ps))))
    (fun R r body => match args.capture with
      | some ⟨p', v, as'⟩ => .inline
          (.cons (.declLocal p' (fse k) (some v)) (.cons (.call f as' (.storage R r) body) .nil))
          (.keep (.drop .refl))
      | none => .inline (args.declsThen (.cons (.declStorage R r none)
          (.cons (.block (body.wk (Thin.atop (.alias R :: ps) Γ)).2.2) .nil)))
          (.keep (Thin.ofExt (Ext.append Γ ps))))
    body

/-- The array operation in `f().push(e)` after the receiver was captured. -/
def ReceiverOp.toStmt {E : Ty} (op : ReceiverOp C Γ E) (b : SPath C Γ (.array E)) : Stmt C Γ Γ
  := match op with
  | .push v hd => .push b v hd
  | .pop => .pop b

/-- Capture `f()` once in `sp`, then run `sp.push(e)` or `sp.pop()`.
The getter's return alias and the explicit capture both end with the statement. -/
def callReceiverCapture (k : Nat) {ps Γf : Ctx} {E : Ty} (f : Name) (args : Args C Γ ps)
    (r : Var) (body : Prog C ([.alias (.array E)] ++ ps) Γf) (op : ReceiverOp C Γ E) :
    Prog C Γ (.alias (.array E) :: .alias (.array E) :: Γ) :=
  .cons (.call f args (.storage _ r) body)
    (.cons (.declStorage (.array E) (fsp k) (some (.path (.alias .here))))
      (.cons (((op.wk (.drop .refl)).wk (.drop .refl)).toStmt (.alias .here)) .nil))

/-- The native call-receiver capture in `f().push(e)`, `f().push()` and `f().pop()`. -/
def callReceiverStep (k : Nat) {ps Γf : Ctx} {E : Ty} (f : Name) (args : Args C Γ ps)
    (r : Var) (body : Prog C ([.alias (.array E)] ++ ps) Γf) (op : ReceiverOp C Γ E) :
    Premise C Γ Γ :=
  .unfold (callReceiverCapture k f args r body op) (.push (.push .refl))

/-- The operand of `f().push(e)`: a source, or its scoped evaluation prefix.
The two forms retain the same upstream capture taclet. -/
inductive ReceiverValue (C : Contract) (Γ : Ctx) (E : Ty) where
  | pure (value : Src C Γ E)
  | deferred {Γv : Ctx} (code : Prog C Γ Γv) (value : Src C Γv E)

/-- Keep `f().push(i++)` intact until the receiver capture rule fires. -/
def ReceiverValue.statement {ps Γf : Ctx} {E : Ty} (f : Name) (args : Args C Γ ps)
    (r : Var) (body : Prog C ([.alias (.array E)] ++ ps) Γf)
    (e : ReceiverValue C Γ E) : Stmt C Γ Γ :=
  match e with
  | .pure value => .callReceiver f args r body (.push (some value) rfl)
  | .deferred code value => .callReceiverPush f args r body code value

/-- Capture `f()` before the private evaluation prefix of `f().push(i++)`. -/
def callReceiverPushCapture (k : Nat) {ps Γf Γv : Ctx} {E : Ty}
    (f : Name) (args : Args C Γ ps) (r : Var)
    (body : Prog C ([.alias (.array E)] ++ ps) Γf)
    (code : Prog C Γ Γv) (value : Src C Γv E) :
    Prog C Γ (.alias (.array E) :: .alias (.array E) :: Γ) :=
  let h : Thin Γ (.alias (.array E) :: Γ) := .drop .refl
  let p := code.wk h
  let q := p.2.2.wk (.drop .refl)
  .cons (.call f args (.storage _ r) body)
    (.cons (.declStorage (.array E) (fsp k) (some (.path (.alias .here))))
      (.cons (.block (q.2.2.join
        (.cons (.push (.alias ((Idx.here).ext q.2.2.ext))
          (some ((value.wk p.2.1).wk q.2.1)) rfl) .nil))) .nil))

/-- One replacement for both pure and effectful operands of `f().push(e)`. -/
def ReceiverValue.step (k : Nat) {ps Γf : Ctx} {E : Ty}
    (f : Name) (args : Args C Γ ps) (r : Var)
    (body : Prog C ([.alias (.array E)] ++ ps) Γf)
    (e : ReceiverValue C Γ E) : Premise C Γ Γ :=
  match e with
  | .pure value => callReceiverStep k f args r body (.push (some value) rfl)
  | .deferred code value =>
    .unfold (callReceiverPushCapture k f args r body code value) (.push (.push .refl))

end Calls

/-! ## `try` -/

/-- The `Panic` clause's code as binders. -/
def CodeBinder.binders : {κ : Ctx} → CodeBinder κ → Binders κ
  | _, c => CodeBinder.casesOn (motive := fun κ _ => Binders κ) c .nil (fun x => Binders.nil.snoc .uint x)

/-- `try …` (`tryStep`): a goal per clause under the box
(`tryCallNoCallbackBox`), `false` under the diamond (`tryCallDiamond`, Lean). -/
def tryStep (m : Modality) {Γ ρ κ Γ₁ Γ₂ Γ₃ Γ₄ : Ctx} (rets : Binders ρ) (ok : Prog C (ρ ++ Γ) Γ₁)
    (err : Prog C Γ Γ₂) (code : CodeBinder κ) (pnc : Prog C (κ ++ Γ) Γ₃) (other : Prog C Γ Γ₄) :
    Premise C Γ Γ :=
  match m with
  | .box => .branches [⟨rets, ok, none⟩, ⟨Binders.nil, err, none⟩, ⟨code.binders, pnc, none⟩,
      ⟨Binders.nil, other, none⟩]
  | .diamond => .done false

/-- A self-call's guards (`tryCallSelfBox`, Lean): the receiver has code
(`a != 0`), is the contract (`a == address(this)`), is another (`a !=
address(this)`). -/
def ExtCall.hasCode {Γ : Ctx} (c : ExtCall C Γ) : Val C Γ .bool :=
  .binop .neB rfl rfl (.simple c.addr) (.simple (.lit 0 rfl))

def ExtCall.isSelf {Γ : Ctx} (c : ExtCall C Γ) : Val C Γ .bool :=
  .binop .eqB rfl rfl (.simple c.addr) (.simple (.env .selfAddress rfl))

def ExtCall.notSelf {Γ : Ctx} (c : ExtCall C Γ) : Val C Γ .bool :=
  .binop .neB rfl rfl (.simple c.addr) (.simple (.env .selfAddress rfl))

/-- What a self-call's `catch` block may assume (`trySelfStep`): the call
does not end normally as a call to the contract itself, `¬⟨ require(a ==
address(this)); f(args) → rets; ⟩ true`.  A `catch` is reached from another
contract's callee, where the `require` reverts, or from the contract's own
callee when it fails. -/
def ExtCall.selfFails {Γ ρ ps Γf : Ctx} (call : ExtCall C Γ) (rets : Binders ρ)
    (sargs : Args C Γ ps) (sbody : Prog C (ρ ++ ps) Γf) : Fml C Γ :=
  .not (.modal .diamond (.cons (.require call.isSelf)
    (.cons (.call call.fn sargs (.rets rets) sbody) .nil)) .nil .tt)

/-! ## Revert data -/

/-- Two lists of what may be, each `none` where it is not known. -/
def optCat {α : Type} : Option (List α) → Option (List α) → Option (List α)
  | some a, some b => some (a ++ b)
  | _, _ => none

/-- A datum known in part: each byte known (`some b`) or not (a byte of a
word that is not literal). -/
abbrev Pat := List (Option UInt8)

/-- The data `p` stands for: its length, its known bytes. -/
def Pat.Matches (p : Pat) (d : List UInt8) : Prop :=
  p.length = d.length ∧ ∀ (i : Nat) (b : UInt8), p[i]? = some (some b) → d[i]? = some b

/-- What a program's reverts may carry: literal data, and data known in
part (`Pat`). -/
abbrev DSet := List (List UInt8) × List Pat

/-- `d` is one of the data `S` lists. -/
def DSet.Mem (S : DSet) (d : List UInt8) : Prop := d ∈ S.1 ∨ ∃ p ∈ S.2, p.Matches d

/-- Two sets of what may be, each `none` where it is not known. -/
def optCatD : Option DSet → Option DSet → Option DSet
  | some a, some b => some (a.1 ++ b.1, a.2 ++ b.2)
  | _, _ => none

/-- The bytes of `revert(d)` when they are literal. -/
def RevPart.litData {Γ : Ctx} : List (RevPart C Γ) → Option (List UInt8)
  | [] => some []
  | .bytes bs :: d => (RevPart.litData d).map (bs ++ ·)
  | _ :: _ => none

/-- The bytes of `revert(d)` known in part: a literal's, each value's ABI
word unknown (32 bytes); `none` with a selector not folded. -/
def RevPart.pat? {Γ : Ctx} : List (RevPart C Γ) → Option Pat
  | [] => some []
  | .bytes bs :: d => (RevPart.pat? d).map (bs.map some ++ ·)
  | .word _ :: d => (RevPart.pat? d).map (List.replicate 32 none ++ ·)
  | .sel _ :: _ => none

/-- Data whose first part is literal bytes that do not begin with `Error`'s
selector (a custom error's): it cannot reach a `catch Error(string memory
r)`, whatever its other parts. -/
def RevPart.notError {Γ : Ctx} : List (RevPart C Γ) → Bool
  | .bytes bs :: _ => decide (4 ≤ bs.length) && !decide (bs.take 4 = Semantics.errorSelector)
  | _ => false

/-- What `revert(d)` may carry: nothing a clause keeps (without `raw`, data
that cannot decode as `Error`), its literal bytes, or its bytes known in
part. -/
def RevPart.datas {Γ : Ctx} (raw : Bool) (d : List (RevPart C Γ)) : Option DSet :=
  if !raw && RevPart.notError d then some ([], []) else
  match RevPart.litData d with
  | some bs => some ([bs], [])
  | none => (RevPart.pat? d).map fun p => ([], [p])

mutual

/-- **The data a program's revert may carry** (`docs/semantic-gaps.md`,
"Revert data"): the `revert(d)`s in it (`RevPart.datas`: literal, or known
in part), in a branch, a block, a loop, a called body or a `try`'s clauses
(a self-call's callee reverts into its `try`, not past it); a revert with
no data besides.  `none` at a recursive call, which is not unfolded.  An
`assert` reverts with no data: what a panic binds is `CatchKind.datas`'s.
Without `raw` (what a `catch Error(string memory r)`
may bind), a datum that cannot decode as `Error` (`RevPart.notError`) is
left out, literal or not.  Sound by `Prog.run_dataS`. -/
def Stmt.revertDatas (raw : Bool) : {Γ Γ' : Ctx} → Stmt C Γ Γ' → Option DSet
  | _, _, s => Stmt.casesOn (motive_1 := fun _ _ _ => Option DSet) s
    (assign := fun _ _ => some ([], [])) (rebind := fun _ _ => some ([], []))
    (assignLocal := fun _ _ => some ([], []))
    (declLocal := fun _ _ _ => some ([], [])) (declStorage := fun _ _ _ => some ([], []))
    (opAssign := fun _ _ _ _ _ => some ([], [])) (incDec := fun _ _ _ => some ([], []))
    (assignIncDec := fun _ _ _ _ _ => some ([], [])) (assignLocalPush := fun _ _ => some ([], []))
    (pushOpAssign := fun _ _ _ _ _ => some ([], [])) (pushIncDec := fun _ _ _ => some ([], []))
    (push := fun _ _ _ => some ([], [])) (pop := fun _ => some ([], []))
    (transfer := fun _ _ => some ([], [])) (send := fun _ _ _ _ => some ([], []))
    (declMem := fun _ _ _ _ _ => some ([], [])) (rebindMem := fun _ _ => some ([], []))
    (assignFromMem := fun _ _ => some ([], [])) (assignMem := fun _ _ => some ([], []))
    (delete := fun _ => some ([], [])) (deleteMem := fun _ _ => some ([], []))
    (assignNew := fun _ _ _ => some ([], []))
    (ite := fun _ thn els => optCatD (Prog.revertDatas raw thn) (Prog.revertDatas raw els))
    (require := fun _ => some ([], [])) (assert := fun _ => some ([], []))
    (revert := some ([], [])) (assumeFalse := some ([], []))
    (call := fun _ _ _ body => Prog.revertDatas raw body)
    (tryCall := fun _ _ ok err _ pnc other _ _ _ =>
      optCatD (optCatD (Prog.revertDatas raw ok) (Prog.revertDatas raw err))
        (optCatD (Prog.revertDatas raw pnc) (Prog.revertDatas raw other)))
    (loop := fun _ _ body => Prog.revertDatas raw body)
    (block := fun body => Prog.revertDatas raw body)
    (callReceiver := fun _ _ _ body _ => Prog.revertDatas raw body)
    (callReceiverPush := fun _ _ _ body code _ =>
      optCatD (Prog.revertDatas raw body) (Prog.revertDatas raw code))
    (callRec := fun _ _ _ _ _ => none)
    (revertData := fun d => RevPart.datas raw d)
    (catchData := fun _ _ _ _ _ _ _ body => Prog.revertDatas raw body)
  termination_by structural _ _ s => s

def Prog.revertDatas (raw : Bool) : {Γ Γ' : Ctx} → Prog C Γ Γ' → Option DSet
  | _, _, P => Prog.casesOn (motive_2 := fun _ _ _ => Option DSet) P (some ([], []))
      (fun s P => optCatD (Stmt.revertDatas raw s) (Prog.revertDatas raw P))
  termination_by structural _ _ P => P

end

/-- `Panic(uint256)`'s data, its code not known: the selector, then a word
(`Semantics.encodePanic`). -/
def Pat.panic : Pat := Semantics.panicSelector.map some ++ List.replicate 32 none

/-- The data a clause of `kind` may be reached with when the contract's own
callee `sbody` fails: the data its body lists, a revert with none among
them for the raw data (the `Error` clause is not reached with none), and,
where the body may panic (`Prog.asserts`), `Panic`'s selector and a code
(`Pat.panic`: the code is the transaction's, `TRun.selfPanicCode`). -/
def CatchKind.datas {Γ Γ' : Ctx} : CatchKind → Prog C Γ Γ' → Option DSet
  | .reason, P => P.revertDatas false
  | .raw, P => (P.revertDatas true).map fun S =>
    ([] :: S.1, (if P.asserts then [Pat.panic] else []) ++ S.2)

/-- Data known in part that no `Panic(uint256)` data matches: not its
length, or a known byte of the selector that is not `Panic`'s. -/
def Pat.notPanic (p : Pat) : Bool :=
  p.length != 36 || (List.range 4).any fun i => match p[i]? with
    | some (some b) => b != Semantics.panicSelector[i]!
    | _ => false

/-- **The codes a self-call's callee may panic with** (`trySelfStep`): the
`Panic` codes of the data its body lists (`Stmt.revertDatas`, solc's `0x01`
for a failed `assert`, `0x11` for an overflow in `checked { … }`, each the
callee's `revert` of `Panic`'s data), where they are known: the body raises
no panic of its own (`Prog.asserts`, whose code is the transaction's,
`TRun.selfPanicCode`), calls nobody back (`Prog.hasTransfer`: a callee that
calls back is read with any code, `ExecS.trySelfPanic`), lists its data,
and none of its data known in part may be `Panic`'s (`Pat.notPanic`).
`none` where they are not known. -/
def Prog.panicCodes {Γ Γ' : Ctx} (P : Prog C Γ Γ') : Option (List Semantics.Word) :=
  if P.asserts || P.hasTransfer then none else
  match P.revertDatas true with
  | some S => if S.2.all Pat.notPanic then some (S.1.filterMap Semantics.decodePanic) else none
  | none => none

/-- `c == k₁ || … || c == kₙ`, of the `Panic` code `c` bound on top. -/
def codeGuard {Γ : Ctx} : List Semantics.Word → Val C (.val .uint :: Γ) .bool
  | [] => .simple (.bool false)
  | [k] => .binop .eqB rfl rfl (.simple (.local .here)) (.simple (.lit k.1 k.2))
  | k :: ks => .binop .or rfl rfl
      (.binop .eqB rfl rfl (.simple (.local .here)) (.simple (.lit k.1 k.2))) (codeGuard ks)

/-- The `Panic` clause of a self-call, behind the codes its callee may
panic with (`Prog.panicCodes`): where the receiver is the contract, the
clause is reached with one of them, and at another receiver with the
oracle's code, any.  So `require(a != address(this) || c == k₁ || …);` in
front of it where the clause binds the code `c`, `require(a !=
address(this));` where it binds none and the callee panics with none; the
clause where the codes are not known. -/
def CodeBinder.guard {Γ Γ₃ : Ctx} (call : ExtCall C Γ) : {κ : Ctx} → CodeBinder κ →
    Option (List Semantics.Word) → Prog C (κ ++ Γ) Γ₃ → Prog C (κ ++ Γ) Γ₃
  | _, _, Option.none, P => P
  | _, .some _, Option.some ks, P => .cons (.require (.binop .or rfl rfl
      (call.wk (Thin.ofExt (Ext.append Γ [.val .uint]))).notSelf (codeGuard ks))) P
  | _, .none, Option.some [], P => .cons (.require call.notSelf) P
  | _, .none, Option.some (_ :: _), P => P

/-- `try …` whose callee is the contract's own (`self`, `docs/options.md`
O8) under the box (`tryCallSelfBox`, Lean): the receiver being the contract,
the callee's body inlined with the returned values as its targets and the
success block after it; the receiver another, the success block for every
value of the returned data; and each `catch` block from the state the call
was made in, where the call does not end normally as a self-call
(`ExtCall.selfFails`), the `Panic` block behind the codes the callee may
panic with (`CodeBinder.guard`, `Prog.panicCodes`).  At address `0` both
success goals hold vacuously (the `require`s revert). -/
def trySelfStep {Γ ρ κ Γ₁ Γ₂ Γ₃ Γ₄ ps Γf : Ctx} (call : ExtCall C Γ) (rets : Binders ρ)
    (ok : Prog C (ρ ++ Γ) Γ₁) (err : Prog C Γ Γ₂) (code : CodeBinder κ)
    (pnc : Prog C (κ ++ Γ) Γ₃) (other : Prog C Γ Γ₄) (sargs : Args C Γ ps)
    (sbody : Prog C (ρ ++ ps) Γf) : Premise C Γ Γ :=
  let up := (call.wk (Thin.ofExt (Ext.append Γ ρ)))
  let nx := some (call.selfFails rets sargs sbody)
  .branches [⟨Binders.nil, .cons (.require call.hasCode) (.cons (.require call.isSelf)
      (.cons (.call call.fn sargs (.rets rets) sbody) ok)), none⟩,
    ⟨rets, .cons (.require up.hasCode) (.cons (.require up.notSelf) ok), none⟩,
    ⟨Binders.nil, err, nx⟩, ⟨code.binders, code.guard call sbody.panicCodes pnc, nx⟩,
    ⟨Binders.nil, other, nx⟩]

/-- A `try`'s rule (`Stmt.step`): `tryStep` for another contract's callee,
`trySelfStep` under the box for the contract's own; `false` under the
diamond either way. -/
def tryStepS (m : Modality) {Γ ρ κ Γ₁ Γ₂ Γ₃ Γ₄ ps Γf : Ctx} (call : ExtCall C Γ)
    (rets : Binders ρ) (ok : Prog C (ρ ++ Γ) Γ₁) (err : Prog C Γ Γ₂) (code : CodeBinder κ)
    (pnc : Prog C (κ ++ Γ) Γ₃) (other : Prog C Γ Γ₄) (sargs : Args C Γ ps)
    (sbody : Prog C (ρ ++ ps) Γf) (self : Bool) : Premise C Γ Γ :=
  match self, m with
  | false, m => tryStep m rets ok err code pnc other
  | true, .box => trySelfStep call rets ok err code pnc other sargs sbody
  | true, .diamond => .done false

/-- The clause after the datum `d` is bound (`catchDataBox`'s goal for it):
what a clause of `kind` binds of it allocated as a literal (`litBytes`) in
front of the clause; a revert where it binds nothing of it (an `Error` clause
at data that does not decode). -/
def catchLit {Γ Γ₁ : Ctx} (x : Var) (kind : CatchKind) (d : List UInt8)
    (body : Prog C (.mem bytesR :: Γ) Γ₁) : Prog C Γ Γ₁ :=
  match kind.decode d with
  | some bs => litBytes x bs body
  | none => .cons .revert (litBytes x [] body)

/-- `n` as a `uint` literal, modulo `2^256` (no `bytes` is that long):
`uintOfNat` below the bound, a literal the closers fold. -/
def Pat.word (n : Nat) : PrimTy.uint.Denote :=
  PrimTy.ofLit .uint ((n % 2 ^ 256 : Nat) : Int)
    (PrimTy.inRange_uint_of_lt (Nat.mod_lt _ (Nat.two_pow_pos 256)))

theorem Pat.word_eq {n : Nat} (h : n < 2 ^ 256) : Pat.word n = uintOfNat n := by
  rw [uintOfNat_eq_lenU h]
  unfold Pat.word lenU PrimTy.ofLit
  simp only [Nat.mod_eq_of_lt h]

/-- `x.length`, the fresh `bytes` on top. -/
def Pat.lenTm {Γ : Ctx} : Tm C (.mem bytesR :: Γ) (.val .uint) :=
  .app2 (.mlen (E := .prim .uint)) (.app0 .memory) (.pvI .here)

/-- `x[i]`, the fresh `bytes` on top. -/
def Pat.byteTm {Γ : Ctx} (i : Nat) : Tm C (.mem bytesR :: Γ) (.val .uint) :=
  .app2 .read (.app0 .memory) (.app2 (.mat .dyn) (.pvI .here) (.app0 (.lit (Pat.word i))))

/-- The bytes known from position `i` on, as equations. -/
def Pat.byteFmls {Γ : Ctx} : Pat → Nat → List (Fml C (.mem bytesR :: Γ))
  | [], _ => []
  | none :: p, i => Pat.byteFmls p (i + 1)
  | some b :: p, i => .eq (Pat.byteTm i) (.app0 (.lit (Pat.word b.toNat))) :: Pat.byteFmls p (i + 1)

/-- **What a datum known in part says of the fresh `bytes` on top**: its
length, and its known bytes. -/
def Pat.fml {Γ : Ctx} (p : Pat) : Fml C (.mem bytesR :: Γ) :=
  Fml.conj (.eq Pat.lenTm (.app0 (.lit (Pat.word p.length))) :: Pat.byteFmls p 0)

/-- What a clause of `kind` may assume of the bytes it binds of a datum
known in part: the raw data its length and known bytes; of an `Error`
reason, nothing (its decoding is any bytes). -/
def CatchKind.patFml {Γ : Ctx} : CatchKind → Pat → Option (Fml C (.mem bytesR :: Γ))
  | .raw, p => some p.fml
  | .reason, _ => none

/-- `Stmt.catchData` (`catchDataBox`, Lean only), under the box: for a
self-call whose callee's data are known (`CatchKind.datas`), the receiver
the contract (`require(a != 0); require(a == address(this));`), a goal per
literal datum, bound as a literal in front of the clause (`catchLit`), and
one per datum known in part, the clause for every fresh `bytes` of the
datum's length and known bytes (`Pat.fml`, `Fml.allocAll`); then, the
receiver another (`require(a != 0); require(a != address(this));`), the
clause for every fresh `bytes` of any contents: another contract's data is
any bytes.  Where the callee's data are not known (a recursive call, a
panic's code, a selector not folded), or the call is not to the contract's
own function, the clause for every fresh `bytes` behind `require(a != 0);`
alone.  Under the diamond, `false`. -/
def catchDataStep (m : Modality) {Γ ρ ps Γf Γ₁ : Ctx} (call : ExtCall C Γ) (sbody : Prog C (ρ ++ ps) Γf)
    (self : Bool) (kind : CatchKind) (x : Var) (body : Prog C (.mem bytesR :: Γ) Γ₁) :
    Premise C Γ Γ :=
  match m, self, kind.datas sbody with
  | .box, true, some ds =>
    .allocBranches (ds.1.map (fun d => (⟨Binders.nil, .cons (.require call.hasCode)
        (.cons (.require call.isSelf) (catchLit x kind d body)), none⟩ : Branch C Γ))) x bytesR body
      (ds.2.map (fun p => (.cons (.require call.hasCode) (.cons (.require call.isSelf) .nil),
          kind.patFml p)) ++
        [(.cons (.require call.hasCode) (.cons (.require call.notSelf) .nil), none)])
  | .box, _, _ => .allocBranches [] x bytesR body [(.cons (.require call.hasCode) .nil, none)]
  | .diamond, _, _ => .done false

/-! ## The loop frame -/

section Frame

variable {Γ : Ctx}

/-- `v` reads something other than locals (master's `Val.readsState`, at `ad728b16`). -/
def Val.readsState : {p : PrimTy} → Val C Γ p → Bool
  | _, .simple (.env ..) => true
  | _, .simple _ => false
  | _, .read _ | _, .readMem _ | _, .len .. | _, .mlen .. | _, .hash .. => true
  | _, .binop _ _ _ a b => a.readsState || b.readsState
  | _, .modular _ a b k => a.readsState || b.readsState || k.readsState
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
      (fun as _ _ _ => Args.readsIn μ as && μ != .pure)
      (fun as _ _ _ => Args.readsIn μ as && μ != .pure)
  termination_by structural _ as => as

/-- No memory return (its body would allocate, which no frame allows). -/
def CallRet.noMem {rs Γ' : Ctx} (r : CallRet Γ rs Γ') : Bool :=
  CallRet.casesOn (motive := fun _ _ _ => Bool) r true (fun _ _ _ => true) (fun _ => true)
    (fun _ _ _ _ => false) (fun _ _ => true)

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
    (fun _ => []) (fun _ _ _ _ => []) (fun _ _ => [])

/-- The local `x ⊕= e` or `x++` writes, if its target is one. -/
def OpLoc.writesAt (d : Nat) {p : PrimTy} : OpLoc C Γ p → List (LTy × Nat)
  | .local i => i.outer d
  | _ => []

mutual

/-- **A statement a callee of mutability `μ` may run** (master's
`Stmt.within`, at `ad728b16`): one writing locals only (`view`, reading no state if
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
    (assignLocalPush := fun _ _ => false)
    (pushOpAssign := fun _ _ _ _ _ => false) (pushIncDec := fun _ _ _ => false)
    (push := fun _ _ _ => false) (pop := fun _ => false)
    (transfer := fun _ _ => μ == .nonpayable) (send := fun _ _ _ _ => μ == .nonpayable)
    (declMem := fun _ _ _ _ _ => false) (rebindMem := fun _ _ => false)
    (assignFromMem := fun _ _ => false) (assignMem := fun _ _ => false)
    (delete := fun _ => μ == .nonpayable) (deleteMem := fun _ _ => false)
    (assignNew := fun _ _ _ => false)
    (ite := fun c thn els => c.readsIn μ && Prog.within μ thn && Prog.within μ els)
    (require := fun c => c.readsIn μ) (assert := fun c => c.readsIn μ) (revert := true) (assumeFalse := true)
    (call := fun _ args ret body => args.readsIn μ && ret.noMem && Prog.within μ body)
    -- a `try` pays (its callee may write the storage, and call back), its
    -- clauses and a self-call's callee within `μ`, nothing allocated
    (tryCall := fun _ _ ok err _ pnc other sargs sbody _ =>
      μ == .nonpayable && sargs.readsIn μ && Prog.within μ sbody && Prog.within μ ok &&
        Prog.within μ err && Prog.within μ pnc && Prog.within μ other)
    (loop := fun _ c body => c.readsIn μ && Prog.within μ body)
    (block := fun body => Prog.within μ body)
    (callReceiver := fun _ _ _ _ _ => false)
    (callReceiverPush := fun _ _ _ _ _ _ => false)
    -- every frame of the unrolling (a run deeper than it is exhausted)
    (callRec := fun _ _ args ret body =>
      args.readsIn μ && ret.noMem && Prog.within μ (body ()))
    (revertData := fun d => d.all fun p => match p with | .word v => v.readsIn μ | _ => true)
    (catchData := fun _ _ _ _ _ _ _ _ => false)
  termination_by structural _ _ s => s

def Prog.within (μ : Mutability) : {Γ Γ' : Ctx} → Prog C Γ Γ' → Bool
  | _, _, P => Prog.casesOn (motive_2 := fun _ _ _ => Bool) P true
      (fun s P => Stmt.within μ s && Prog.within μ P)
  termination_by structural _ _ P => P

end

mutual

/-- The locals of the context `d` locals below `s`'s that `s` may write,
by type and position there (master's `Stmt.writes` at `ad728b16`, less the
locals `s`'s own scopes declare). -/
def Stmt.writesAt (d : Nat) : {Γ Γ' : Ctx} → Stmt C Γ Γ' → List (LTy × Nat)
  | _, _, s => Stmt.casesOn (motive_1 := fun _ _ _ => List (LTy × Nat)) s
    (assign := fun _ _ => []) (rebind := fun _ _ => []) (assignLocal := fun i _ => i.outer d)
    (declLocal := fun _ _ _ => []) (declStorage := fun _ _ _ => [])
    (opAssign := fun _ _ _ l _ => l.writesAt d) (incDec := fun _ _ l => l.writesAt d)
    (assignIncDec := fun i _ _ l _ => i.outer d ++ l.writesAt d)
    (assignLocalPush := fun i _ => i.outer d)
    (pushOpAssign := fun _ _ _ _ _ => []) (pushIncDec := fun _ _ _ => [])
    (push := fun _ _ _ => []) (pop := fun _ => []) (transfer := fun _ _ => [])
    (send := fun pv _ _ _ => pv.outer d)
    (declMem := fun _ _ _ _ _ => []) (rebindMem := fun _ _ => []) (assignFromMem := fun _ _ => [])
    (assignMem := fun _ _ => []) (delete := fun _ => []) (deleteMem := fun _ _ => [])
    (assignNew := fun _ _ _ => [])
    (ite := fun _ thn els => Prog.writesAt d thn ++ Prog.writesAt d els)
    (require := fun _ => []) (assert := fun _ => []) (revert := []) (assumeFalse := [])
    (call := fun _ _ ret _ => ret.writesAt d)
    (tryCall := fun {Γ ρ κ _ _ _ _ _ _} _ _ ok err _ pnc other _ _ _ =>
      Prog.writesAt (d + (Ext.append Γ ρ).depth) ok ++ Prog.writesAt d err ++
        Prog.writesAt (d + (Ext.append Γ κ).depth) pnc ++ Prog.writesAt d other)
    (loop := fun _ _ body => Prog.writesAt d body) (block := fun body => Prog.writesAt d body)
    (callReceiver := fun _ _ _ _ _ => [])
    (callReceiverPush := fun _ _ _ _ code _ => Prog.writesAt d code)
    (callRec := fun _ _ _ ret _ => ret.writesAt d)
    (revertData := fun _ => [])
    (catchData := fun _ _ _ _ _ _ _ body => Prog.writesAt (d + 1) body)
  termination_by structural _ _ s => s

def Prog.writesAt (d : Nat) : {Γ Γ' : Ctx} → Prog C Γ Γ' → List (LTy × Nat)
  | _, _, P => Prog.casesOn (motive_2 := fun _ _ _ => List (LTy × Nat)) P []
      (fun s P => Stmt.writesAt d s ++ Prog.writesAt (d + s.ext.depth) P)
  termination_by structural _ _ P => P

end

/-- **The frame of a loop body** (master's `Prog.loopFrame`, at
`ad728b16`): the
locals of the loop's context it writes, and whether it writes the storage
and the ledger too; `none` when it does more. -/
def Prog.frame {Γ₁ : Ctx} (P : Prog C Γ Γ₁) : Option (List ((t : LTy) × Idx Γ t) × Bool) :=
  let xs := (Prog.writesAt 0 P).filterMap fun (t, n) => (Γ.idx? n t).map (⟨t, ·⟩)
  if Prog.within .view P then some (xs, false)
  else if Prog.within .nonpayable P then some (xs, true)
  else none

end Frame

/-! ## Loops -/

/-- One application of `whileUnwind`, with either a written bound or automatic search. -/
def loopUnwindStep {Γ Γ₁ : Ctx} (u : LoopUnwind) (c : Val C Γ .bool)
    (body : Prog C Γ Γ₁) : Premise C Γ Γ :=
  .unfold (.cons (.ite c (.cons (.block body) (.cons (.loop u.after c body) .nil)) .nil) .nil)
    .refl

/-- `!x && r` is `false` where `x` reads `true`, `r` not read. -/
theorem Val.evalT_andNotFlag {Γ : Ctx} {p : PrimTy} (h : BinOp.and.accepts p = true)
    (hq : BinOp.and.ret p = .bool) (h' : UnOp.not.accepts .bool = true)
    (hq' : UnOp.not.ret .bool = p) (x : Idx Γ (.val .bool)) (r : Val C Γ p) (σ : State C Γ)
    (hx : (Val.simple (.local x) : Val C Γ .bool).evalT σ = .ok true) :
    (Val.binop .and h hq (.unop .not h' hq' (.simple (.local x))) r).evalT σ = .ok false := by
  subst hq'
  have hx' : Simple.evalT σ (.local x) = true := by injection hx
  dsimp only [Val.evalT]
  rw [hx']
  rfl

/-- `c` is `!x && r`. -/
def Val.AndNotFlag {Γ : Ctx} (c : Val C Γ .bool) (x : Idx Γ (.val .bool)) : Prop :=
  ∃ (p : PrimTy) (h : BinOp.and.accepts p = true) (hq : BinOp.and.ret p = .bool)
    (h' : UnOp.not.accepts .bool = true) (hq' : UnOp.not.ret .bool = p) (r : Val C Γ p),
    c = .binop .and h hq (.unop .not h' hq' (.simple (.local x))) r

/-- The flag a lowered `break` sets, where the loop's condition starts with
its negation, `!brk && …` (`lowerLoops`), with the condition's shape: where
the flag reads `true` the condition is `false` (`Val.evalT_andNotFlag`). -/
def Val.breakExit {Γ : Ctx} : (c : Val C Γ .bool) →
    Option ((x : Idx Γ (.val .bool)) ×' c.AndNotFlag x)
  | .binop .and h hq (.unop .not h' hq' (@Val.simple _ _ .bool (.local x))) r =>
    some ⟨x, _, h, hq, h', hq', r, rfl⟩
  | _ => none

/-- A quantified invariant clause as a formula: a value read `true`, `→`
and `∀` as written (`Fml.all`). -/
def LoopQ.toFml : {Γ : Ctx} → LoopQ C Γ → Fml C Γ
  | _, .val a => .isBool a.lower true
  | _, .imp a c => .imp (.isBool a.lower true) (.isBool c.lower true)
  | _, .all x p b => .all x p b.toFml

/-- A loop's invariant as the rules read it (solkey's `\getInvariant`): `I`
read `true`, then each quantified clause. -/
def invFml {Γ : Ctx} (I : Val C Γ .bool) (qs : List (LoopQ C Γ)) : Fml C Γ :=
  qs.foldl (fun acc q => .and acc q.toFml) (.isBool I.lower true)

/-- A box loop's break test (solkey's `\getLoopBreak`): its `break` flag
read `true`, where the elaborator lowered a `break` (`brk`) and the
condition starts with the flag's negation (`Val.breakExit`). -/
def loopBreak {Γ : Ctx} (brk : Bool) (c : Val C Γ .bool) : Option (Fml C Γ) :=
  (if brk then c.breakExit else none).map fun x => .isBool (.pvV (p := .bool) x.1) true

/-- A loop (`loopStep`): unwound (`whileUnwind`), ended (`loopExit`), or by
its invariant (`whileInvariantBox`, `whileInvariantDiamond`), closed to
`false` when its body has no frame (`whileClose`) or, under the diamond,
it has no variant (`whileNoVariantDiamond`). -/
def loopStep (k : Nat) (m : Modality) {Γ Γ₁ : Ctx} (a : LoopAnn C Γ) (c : Val C Γ .bool)
    (body : Prog C Γ Γ₁) : Premise C Γ Γ :=
  match a with
  -- loopExit
  | .unwind 0 =>
    .check (.upd .diamond (Upd.nil.decl (fse k) (.val (p := .bool) c.lower))
      (.isBool (.pvV (p := .bool) .here) false))
  -- whileUnwind
  | .unwind (n + 1) =>
    loopUnwindStep (.bounded n) c body
  | .auto => loopUnwindStep .automatic c body
  | .inv I dec brk qs =>
    match body.frame with
    -- whileClose
    | none => .done false
    | some (xs, hv) =>
      match m, dec, qs with
      -- whileInvariantBox
      | .box, _, _ =>
        .inv (invFml I qs) (loopBreak brk c) xs hv
          (Upd.nil.decl (fse k) (.val (p := .bool) c.lower))
          (.isBool (.pvV (p := .bool) .here) true) (.isBool (.pvV (p := .bool) .here) false)
          .refl (.push .refl) body (invFml I qs)
      -- whileInvariantDiamond
      | .diamond, some d, [] =>
        let U : Upd C Γ (.val .bool :: .val .uint :: Γ) :=
          (Upd.nil.decl (fie k) (.val (p := .uint) d.lower)).decl (fse k) (.val (p := .bool) c.lower)
        let d' : Tm C (.val .bool :: .val .uint :: Γ) (.val .uint) := (d.up.up).lower
        let post : Fml C (.val .uint :: Γ) :=
          .and (.isBool I.up.lower true)
            (.upd .diamond (Upd.nil.decl (fse k) (.val (p := .bool) c.up.lower))
              (.imp (.isBool (.pvV (p := .bool) .here) true)
                (.and (.isBool (.app2 (.binop .le (p := .uint) rfl) (Tm.lit (p := .uint) ⟨0, rfl⟩) d') true)
                  (.isBool (.app2 (.binop .lt (p := .uint) rfl) d' (.pvV (p := .uint) (.there .here))) true))))
        .inv (.isBool I.lower true) none xs hv U
          (.isBool (.pvV (p := .bool) .here) true) (.isBool (.pvV (p := .bool) .here) false)
          (.push .refl) (.push .refl) (body.wk up).2.2 post
      -- whileNoVariantDiamond: no variant, or a quantified clause (Lean only)
      | .diamond, _, _ => .done false

end Solidity
