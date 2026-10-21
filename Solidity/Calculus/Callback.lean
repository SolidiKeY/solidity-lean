import Solidity.Calculus.CallbackRules
import Solidity.Calculus.Delab
import Solidity.Calculus.Proves
import Solidity.Semantics.Callback
import Solidity.Calculus.CallbackHolds
import Solidity.Semantics.CallbackCapture

/-!
# The callback taclets on scoped statements

The callback taclets (`CallbackTaclet`, solkey's `…WithCallbackBox`) are
`Calculus/CallbackRules.lean`'s, below the sequents, so the rule table's
checks (`Calculus/RuleShapes.lean`) read them without the judgement: what a
callback changes is how the premise is read, the invariant owed on exit and
the callee's `{havoc}` (`ProvesC`), not what the rule leaves.

The rules print as today's (`dl[CallbackTaclet C k]{ … }`, `delabCallbackTaclet`),
their goals labelled by their no-callback twins' labels.

`ProvesC I pay H φ` is the callback judgement on scoped sequents:
the ordinary rules on a statement that runs no other and hands control to no
callee that calls back (`Stmt.forksIn pay`: a `try` and a value call always,
a `transfer` and a `send` when `pay` is set, a call where its body does,
`docs/options.md`), a split, the
callback taclets with solkey's goals ("invariant on exit", the rest resumed
under `{havoc}` with the invariant assumed), and the plain calculus
(`Proves`) on a goal where nothing calls back (`Fml.callsBack pay`); and the
rules a walk needs on the way where `Proves` would take them: a closing
taclet, `assertSimple`, a gas-limited send, a block that calls back.  The
invariant is a closed formula `I : Fml C []`, read in any scope
past an update that drops every local (`Fml.closedAt`, invisible when
printed), so it needs no weakening.

`ProvesC` is sound against `ValidC` (the callback reading over `State`,
`Calculus/CallbackHolds.lean`) for a first-order invariant:
`ProvesC.valid`, `Calculus/CallbackSound.lean`.
-/

namespace Solidity

open Solidity (Modality)

open scoped Solidity.Schema

variable {C : Contract}

/-! ## The judgement -/

/-- A closed formula read in the scope `Γ`: past an update that drops every
local (a frame end, which prints as nothing), so it reads the state's
global part alone. -/
def Fml.closedAt {Γ : Ctx} (I : Fml C []) : Fml C Γ :=
  .upd .box (Upd.nil.drop (Thin.nilTo Γ)) I

/-- A rule's fresh index in a sequent with callbacks: past the invariant
too. -/
def Hyps.freshC {Γ₀ Γ : Ctx} (I : Fml C []) (H : Hyps C Γ₀ Γ) (φ : Fml C Γ) : Nat :=
  H.fresh (.and (Fml.closedAt I) φ)

/-- A call's result assigned to its target, if it has one, under the
callee's parameters and return variable (`callStep`'s, `Calculus/Blocks.lean`). -/
def Prog.callResult {Γ ps : Ctx} {p : PrimTy} :
    Option (Idx Γ (.val p)) → Prog C (.val p :: (ps ++ Γ)) (.val p :: (ps ++ Γ))
  | none => .nil
  | some j => .cons (.assignLocal (j.under ps).there (.simple (.local .here))) .nil

/-- `ProvesC I pay H φ`: the calculus proves `φ` in the context `H` when a
callee may call back into a contract with invariant `I`, from every `try`
and value call and, when `pay` is set, from every `transfer` and `send`. -/
inductive ProvesC (I : Fml C []) (pay : Bool) (Γ₀ : Ctx) :
    {Γ : Ctx} → Hyps C Γ₀ Γ → Fml C Γ → Prop where
  /-- A goal where nothing calls back is a goal of the calculus: there the
  two readings agree. -/
  | plain {Γ : Ctx} {H : Hyps C Γ₀ Γ} {φ : Fml C Γ} (h : Proves C .all Γ₀ H φ)
      (hφ : (H.wrap φ).callsBack pay = false) : ProvesC I pay Γ₀ H φ
  /-- `impRight`. -/
  | intro {Γ : Ctx} {H : Hyps C Γ₀ Γ} {a φ : Fml C Γ} (h : ProvesC I pay Γ₀ (H.pre a) φ) :
      ProvesC I pay Γ₀ H (.imp a φ)
  /-- `impRight`, then `notLeft`: `X` to prove instead of the goal
  (`Proves.notLeft`). -/
  | notLeft {Γ : Ctx} {H : Hyps C Γ₀ Γ} {X φ : Fml C Γ} (h : ProvesC I pay Γ₀ H X) :
      ProvesC I pay Γ₀ H (.imp (.not X) φ)
  /-- `impRight`, then `hide_left` on the premise. -/
  | hideLeft {Γ : Ctx} {H : Hyps C Γ₀ Γ} {a φ : Fml C Γ} (h : ProvesC I pay Γ₀ H φ) :
      ProvesC I pay Γ₀ H (.imp a φ)
  /-- `allRight`. -/
  | allIntro {Γ : Ctx} {H : Hyps C Γ₀ Γ} {x : Var} {p : PrimTy} {φ : Fml C (.val p :: Γ)}
      (h : ProvesC I pay Γ₀ (H.all x p) φ) : ProvesC I pay Γ₀ H (.all x p φ)
  /-- `{havoc}` in front of the formula joins the context (Lean only: what
"post" of a contract forgets, `Fml.anonC`). -/
  | havocIntro {Γ : Ctx} {H : Hyps C Γ₀ Γ} {φ : Fml C Γ} (h : ProvesC I pay Γ₀ H.havoc φ) :
      ProvesC I pay Γ₀ H (.havoc φ)
  /-- An update in front of the formula joins the context. -/
  | updIntro {Γ Δ : Ctx} {H : Hyps C Γ₀ Γ} {m : Modality} {U : Upd C Γ Δ} {φ : Fml C Δ}
      (h : ProvesC I pay Γ₀ (H.upd m U) φ) : ProvesC I pay Γ₀ H (.upd m U φ)
  /-- The hidden binder joins the context (Lean only). -/
  | bindIntro {Γ : Ctx} {H : Hyps C Γ₀ Γ} {m : Modality} {x : Var} {t : LTy}
      {φ : Fml C (t :: Γ)} (h : ProvesC I pay Γ₀ (H.bind m x t) φ) :
      ProvesC I pay Γ₀ H (.bind m x t φ)
  /-- A rule that produces an update, on a statement that runs no other and
  pays nothing. -/
  | update {Γ Γ' Γ₁ Γ₂ : Ctx} {H : Hyps C Γ₀ Γ} {m : Modality} {s : Stmt C Γ Γ'}
      {ω : Prog C Γ' Γ₁} {κ : Frames C Γ₁ Γ₂} {φ : Fml C Γ₂} {U : Upd C Γ Γ'}
      (d : Rule C (H.freshC I (.modal m (.cons s ω) κ φ)) m s (.update U))
      (hs : s.forksIn pay = false)
      (h : ProvesC I pay Γ₀ (H.upd m U) (.modalK m ω κ φ)) :
      ProvesC I pay Γ₀ H (.modal m (.cons s ω) κ φ)
  /-- Two updates in sequence, as in `a.push() += x`, on a statement that
  runs no callback of its own. -/
  | updates {Γ Δ Γ' Γ₁ Γ₂ : Ctx} {H : Hyps C Γ₀ Γ} {m : Modality} {s : Stmt C Γ Γ'}
      {ω : Prog C Γ' Γ₁} {κ : Frames C Γ₁ Γ₂} {φ : Fml C Γ₂}
      {U : Upd C Γ Δ} {V : Upd C Δ Γ'}
      (d : Rule C (H.freshC I (.modal m (.cons s ω) κ φ)) m s (.updates U V))
      (hs : s.forksIn pay = false)
      (h : ProvesC I pay Γ₀ ((H.upd m U).upd m V) (.modalK m ω κ φ)) :
      ProvesC I pay Γ₀ H (.modal m (.cons s ω) κ φ)
  /-- The outer zero-divisor branch of `sp.push() /= se`, with callbacks
  permitted only in the continuation. -/
  | guardedUpdates {Γ Δ Γ₁ Γ₂ : Ctx} {H : Hyps C Γ₀ Γ} {m : Modality}
      {s : Stmt C Γ Γ} {ω : Prog C Γ Γ₁} {κ : Frames C Γ₁ Γ₂} {φ : Fml C Γ₂}
      {c : Fml C Γ} {U : Upd C Γ Δ} {V : Upd C Δ Γ}
      (d : Rule C (H.freshC I (.modal m (.cons s ω) κ φ)) m s (.guardedUpdates c U V))
      (hs : s.forksIn pay = false)
      (thn : ProvesC I pay Γ₀ (H.pre c) (.upd m U (.upd m V (.modalK m ω κ φ))))
      (els : ProvesC I pay Γ₀ (H.pre (.not c)) (.modal m (.cons .revert ω) κ φ)) :
      ProvesC I pay Γ₀ H (.modal m (.cons s ω) κ φ)
  /-- A rule that produces statements, on a statement that runs no other and
  pays nothing, when they pay nothing either. -/
  | unfold {Γ Γ' Γ'' Γ₁ Γ₂ : Ctx} {H : Hyps C Γ₀ Γ} {m : Modality} {s : Stmt C Γ Γ'}
      {ω : Prog C Γ' Γ₁} {κ : Frames C Γ₁ Γ₂} {φ : Fml C Γ₂} {P : Prog C Γ Γ''} {e : Ext Γ' Γ''}
      (d : Rule C (H.freshC I (.modal m (.cons s ω) κ φ)) m s (.unfold P e))
      (hs : s.forksIn pay = false)
      (hP : P.callsBack pay = false)
      (h : ProvesC I pay Γ₀ H (.modal m P (.pop .capture e (.seq ω κ)) φ)) :
      ProvesC I pay Γ₀ H (.modal m (.cons s ω) κ φ)
  /-- A capture (`ifElseUnfold`, `whileUnwind`, `transfer_unfold_…`,
  `send_unfold_…`) whose rest may call back: the side condition is on the
  capture alone, which declares a value and hands control to nobody, so the
  statement runs, with callbacks, as the captured program
  (`Stmt.CapturesAs`, `Semantics/CallbackCapture.lean`). -/
  | capture {Γ Γ' Γ'' Γ₁ Γ₂ : Ctx} {H : Hyps C Γ₀ Γ} {m : Modality} {s : Stmt C Γ Γ'}
      {ω : Prog C Γ' Γ₁} {κ : Frames C Γ₁ Γ₂} {φ : Fml C Γ₂} {P : Prog C Γ Γ''} {e : Ext Γ' Γ''}
      (d : Rule C (H.freshC I (.modal m (.cons s ω) κ φ)) m s (.unfold P e))
      (hc : s.CapturesAs pay m P e)
      (h : ProvesC I pay Γ₀ H (.modal m P (.pop .capture e (.seq ω κ)) φ)) :
      ProvesC I pay Γ₀ H (.modal m (.cons s ω) κ φ)
  /-- `storagePushValue_unfold_leftCallReceiver`, including callbacks in the
  getter or deferred operand. Both captured aliases end with this statement. -/
  | unfoldReceiver {Γ Γv ps Γf Γ₁ Γ₂ : Ctx} {H : Hyps C Γ₀ Γ} {m : Modality}
      {E : Ty} {f : Name} {args : Args C Γ ps} {r : Var}
      {body : Prog C ([.alias (.array E)] ++ ps) Γf}
      {code : Prog C Γ Γv} {value : Src C Γv E} {k : Nat}
      {ω : Prog C Γ Γ₁} {κ : Frames C Γ₁ Γ₂} {φ : Fml C Γ₂}
      (d : Rule C (H.freshC I (.modal m
        (.cons (.callReceiverPush f args r body code value) ω) κ φ)) m
        (.callReceiverPush f args r body code value)
        (.unfold (callReceiverPushCapture k f args r body code value) (.push (.push .refl))))
      (h : ProvesC I pay Γ₀ H (.modal m (callReceiverPushCapture k f args r body code value)
        (.pop .capture (.push (.push .refl)) (.seq ω κ)) φ)) :
      ProvesC I pay Γ₀ H (.modal m (.cons (.callReceiverPush f args r body code value) ω) κ φ)
  /-- A declaration with its initializer dropped (`localValueDeclInitDrop`),
  when the assignment pays nothing. -/
  | bind {Γ Γ' Γ₁ Γ₂ : Ctx} {H : Hyps C Γ₀ Γ} {m : Modality} {s : Stmt C Γ Γ'}
      {ω : Prog C Γ' Γ₁} {κ : Frames C Γ₁ Γ₂} {φ : Fml C Γ₂} {x : Var} {t : LTy}
      {P : Prog C (t :: Γ) Γ'}
      (d : Rule C (H.freshC I (.modal m (.cons s ω) κ φ)) m s (.bind x t P))
      (hs : s.forksIn pay = false)
      (hP : P.callsBack pay = false)
      (h : ProvesC I pay Γ₀ (H.bind m x t) (.modal m P (.seq ω κ) φ)) :
      ProvesC I pay Γ₀ H (.modal m (.cons s ω) κ φ)
  /-- A rule that branches (`ifElseSplit`, `requireSimple`): KeY's two goals,
  each branch a block ended as the premise says, whatever its branches pay. -/
  | split {Γ Γ₁ Γ₂ Δ₁ Δ₂ : Ctx} {H : Hyps C Γ₀ Γ} {m : Modality} {s : Stmt C Γ Γ}
      {ω : Prog C Γ Γ₁} {κ : Frames C Γ₁ Γ₂} {φ : Fml C Γ₂} {b : BlockKind} {c c' : Fml C Γ}
      {P : Prog C Γ Δ₁} {Q : Prog C Γ Δ₂}
      (d : Rule C (H.freshC I (.modal m (.cons s ω) κ φ)) m s (.split b c c' P Q))
      (thn : ProvesC I pay Γ₀ (H.pre c) (.modalK m P (.pop b P.ext (.seq ω κ)) φ))
      (els : ProvesC I pay Γ₀ (H.pre c') (.modalK m Q (.pop b Q.ext (.seq ω κ)) φ)) :
      ProvesC I pay Γ₀ H (.modal m (.cons s ω) κ φ)
  /-- `emptyModality`. -/
  | empty {Γ Γ₂ : Ctx} {H : Hyps C Γ₀ Γ} {m : Modality} {κ : Frames C Γ Γ₂} {φ : Fml C Γ₂}
      (h : ProvesC I pay Γ₀ H (κ.exit m φ)) : ProvesC I pay Γ₀ H (.modal m .nil κ φ)
  /-- A taclet that closes the modality (`revertBox`, a diamond's `false`),
  on a statement that hands control to no callee: `true` or `false`. -/
  | done {Γ Γ' Γ₁ Γ₂ : Ctx} {H : Hyps C Γ₀ Γ} {m : Modality} {s : Stmt C Γ Γ'}
      {ω : Prog C Γ' Γ₁} {κ : Frames C Γ₁ Γ₂} {φ : Fml C Γ₂} {b : Bool}
      (d : Rule C (H.freshC I (.modal m (.cons s ω) κ φ)) m s (.done b))
      (hs : s.forksIn pay = false)
      (h : ProvesC I pay Γ₀ H (if b then .tt else .ff)) :
      ProvesC I pay Γ₀ H (.modal m (.cons s ω) κ φ)
  /-- `assertSimple`: the rest where the condition holds ("Holds"), and the
  condition ("Violated"). -/
  | assert {Γ Γ₁ Γ₂ : Ctx} {H : Hyps C Γ₀ Γ} {m : Modality} {v : Simple C Γ .bool}
      {ω : Prog C Γ Γ₁} {κ : Frames C Γ₁ Γ₂} {φ : Fml C Γ₂}
      (thn : ProvesC I pay Γ₀ (H.pre (Fml.isBool v.lower true)) (.modalK m ω κ φ))
      (els : ProvesC I pay Γ₀ H (Fml.isBool v.lower true)) :
      ProvesC I pay Γ₀ H (.modal m (.cons (.assert (.simple v)) ω) κ φ)
  /-- **`loopExit` with callbacks**, under the box: a loop at its
unwinding bound ends there, whatever its body calls ("loop exited", the
condition `false` assumed; "unwound to the end", that it is).  A loop whose
body calls back may diverge, which the box accepts and the diamond does
not. -/
  | loopExit {Γ Γ₁ Γ₂ Γb : Ctx} {H : Hyps C Γ₀ Γ} {c : Val C Γ .bool} {body : Prog C Γ Γb}
      {ω : Prog C Γ Γ₁} {κ : Frames C Γ₁ Γ₂} {φ : Fml C Γ₂}
      (thn : ProvesC I pay Γ₀ (H.pre (.upd .diamond (Upd.nil.decl
          (.fresh "se" (H.freshC I (.modal .box (.cons (.loop (.unwind 0) c body) ω) κ φ)))
          (.val (p := .bool) c.lower)) (.isBool (.pvV (p := .bool) .here) false)))
        (.modalK .box ω κ φ))
      (els : ProvesC I pay Γ₀ H (.upd .diamond (Upd.nil.decl
          (.fresh "se" (H.freshC I (.modal .box (.cons (.loop (.unwind 0) c body) ω) κ φ)))
          (.val (p := .bool) c.lower)) (.isBool (.pvV (p := .bool) .here) false))) :
      ProvesC I pay Γ₀ H (.modal .box (.cons (.loop (.unwind 0) c body) ω) κ φ)
  /-- **`whileInvariantBox` with callbacks** (`Proves.inv`'s goals, under the
  box): the invariant now ("invariant initially valid"); from every state
  the body's frame allows (`{anon(xs)}`, with `{havoc}` when the body may
  write the storage: a body that calls back pays, so its frame has it), the
  invariant holding, the body to the invariant where the condition holds
  ("body preserves invariant"), the rest where it does not ("use case").
  Whatever the body calls: a callback leaves a state the frame allows. -/
  | invBox {Γ Γb Γ₁ Γ₂ : Ctx} {H : Hyps C Γ₀ Γ} {Iv : Val C Γ .bool}
      {dec : Option (Val C Γ .uint)} {brk : Bool} {qs : List (LoopQ C Γ)} {c : Val C Γ .bool}
      {body : Prog C Γ Γb} {ω : Prog C Γ Γ₁} {κ : Frames C Γ₁ Γ₂} {φ : Fml C Γ₂}
      {xs : List ((t : LTy) × Idx Γ t)} {hv : Bool}
      (hf : body.frame = some (xs, hv))
      (init : ProvesC I pay Γ₀ H ((invFml Iv qs).invHyp (loopBreak brk c)))
      (thn : ProvesC I pay Γ₀ ((((H.anonHavoc xs hv).pre ((invFml Iv qs).invHyp (loopBreak brk c))).upd
          .box (Upd.nil.decl (fse (H.freshC I (.modal .box (.cons (.loop (.inv Iv dec brk qs) c body)
            ω) κ φ))) (.val (p := .bool) c.lower))).pre (.isBool (.pvV (p := .bool) .here) true))
        (.upd .box (Upd.nil.pop (.push .refl)) (.modalK .box body (.pop .block body.ext .nil)
          (Fml.invPost .box .refl ω κ φ (invFml Iv qs) (loopBreak brk c)))))
      (els : ProvesC I pay Γ₀ ((((H.anonHavoc xs hv).pre ((invFml Iv qs).invHyp (loopBreak brk c))).upd
          .box (Upd.nil.decl (fse (H.freshC I (.modal .box (.cons (.loop (.inv Iv dec brk qs) c body)
            ω) κ φ))) (.val (p := .bool) c.lower))).pre (.isBool (.pvV (p := .bool) .here) false))
        (.upd .box (Upd.nil.pop (.push .refl)) (.modalK .box ω κ φ))) :
      ProvesC I pay Γ₀ H (.modal .box (.cons (.loop (.inv Iv dec brk qs) c body) ω) κ φ)
  /-- **`sendNoCallbackBox`**, a send that does not call back (`pay` unset,
  the 2300-gas stipend): the rest after the booking and `pv := true` ("send
  succeeded"), and after `pv := false` ("send failed"), no `{havoc}`. -/
  | sendDet {Γ Γ₁ Γ₂ : Ctx} {H : Hyps C Γ₀ Γ} {pv : Idx Γ (.val .bool)} {sadr se : Simple C Γ .uint}
      {ω : Prog C Γ Γ₁} {κ : Frames C Γ₁ Γ₂} {φ : Fml C Γ₂}
      (hp : pay = false)
      (ok : ProvesC I pay Γ₀ (H.upd .box ((Upd.nil.snoc (UpdElem.payTo sadr se)).snoc
        (.local pv (.val (Tm.lit (p := .bool) true))))) (.modalK .box ω κ φ))
      (failed : ProvesC I pay Γ₀
        (H.upd .box (Upd.nil.snoc (.local pv (.val (Tm.lit (p := .bool) false)))))
        (.modalK .box ω κ φ)) :
      ProvesC I pay Γ₀ H (.modal .box (.cons (.send pv (.simple sadr) (.simple se) false) ω) κ φ)
  /-- A block whose body calls back (`blockUnfold`'s premise): the body, its
  locals popped, then the rest. -/
  | block {Γ Γ₁ Γ₁' Γ₂ : Ctx} {H : Hyps C Γ₀ Γ} {m : Modality} {body : Prog C Γ Γ₁'}
      {ω : Prog C Γ Γ₁} {κ : Frames C Γ₁ Γ₂} {φ : Fml C Γ₂}
      (h : ProvesC I pay Γ₀ H (.modal m body (.pop .capture body.ext (.seq ω κ)) φ)) :
      ProvesC I pay Γ₀ H (.modal m (.cons (.block body) ω) κ φ)
  /-- `internalCallExpand` of a call with no result whose body may call
  back: the parameters declared with the arguments, the body under the
  caller's locals as a block, the parameters popped (`callStep`'s program). -/
  | callNone {Γ ps Γf Γ₁ Γ₂ : Ctx} {H : Hyps C Γ₀ Γ} {m : Modality} {f : Name}
      {args : Args C Γ ps} {body : Prog C ([] ++ ps) Γf} {ω : Prog C Γ Γ₁} {κ : Frames C Γ₁ Γ₂}
      {φ : Fml C Γ₂}
      (h : ProvesC I pay Γ₀ H (.modal m
        (args.declsThen (.cons (.block (body.wk (Thin.atop ps Γ)).2.2) .nil))
        (.pop .capture (Ext.append Γ ps) (.seq ω κ)) φ)) :
      ProvesC I pay Γ₀ H (.modal m (.cons (.call f args .none body) ω) κ φ)
  /-- `functionBodyExpand` of a call with targets whose body may call back:
  the parameters declared, the return variables at their defaults, the body
  as a block, the parameters thinned out from under the return variables. -/
  | callRets {Γ ps rs Γf Γ₁ Γ₂ : Ctx} {H : Hyps C Γ₀ Γ} {m : Modality} {f : Name}
      {args : Args C Γ ps} {bs : Binders rs} {body : Prog C (rs ++ ps) Γf}
      {ω : Prog C (rs ++ Γ) Γ₁} {κ : Frames C Γ₁ Γ₂} {φ : Fml C Γ₂}
      (h : ProvesC I pay Γ₀ H (.modal m (args.declsThen (bs.declsThen
          (.cons (.block (body.wk (Thin.keepAll rs (Thin.atop ps Γ))).2.2) .nil)))
        (.drop (Thin.keepAll rs (Thin.ofExt (Ext.append Γ ps))) (.seq ω κ)) φ)) :
      ProvesC I pay Γ₀ H (.modal m (.cons (.call f args (.rets bs) body) ω) κ φ)
  /-- `internalCallExpand` of a call of one value (`y = f(x)`) whose body may
  call back: the parameters declared, the return variable at its default,
  the body as a block, the result assigned to its target, the frame popped
  (`callStep`'s program). -/
  | callVal {Γ ps Γf Γ₁ Γ₂ : Ctx} {H : Hyps C Γ₀ Γ} {m : Modality} {f : Name}
      {args : Args C Γ ps} {p : PrimTy} {r : Var} {res : Option (Idx Γ (.val p))}
      {body : Prog C ([.val p] ++ ps) Γf} {ω : Prog C Γ Γ₁} {κ : Frames C Γ₁ Γ₂} {φ : Fml C Γ₂}
      (h : ProvesC I pay Γ₀ H (.modal m (args.declsThen (.cons (.declLocal p r none)
          (.cons (.block (body.wk (Thin.atop (.val p :: ps) Γ)).2.2) (Prog.callResult res))))
        (.pop .capture (.push (Ext.append Γ ps)) (.seq ω κ)) φ)) :
      ProvesC I pay Γ₀ H (.modal m (.cons (.call f args (.val p r res) body) ω) κ φ)
  /-- `internalCallExpand` of a call of a storage reference whose body may
  call back: the return alias unset, the body as a block, the parameters
  thinned out from under the alias. -/
  | callStorage {Γ ps Γf Γ₁ Γ₂ : Ctx} {H : Hyps C Γ₀ Γ} {m : Modality} {f : Name}
      {args : Args C Γ ps} {R : RefTy} {r : Var} {body : Prog C ([.alias R] ++ ps) Γf}
      {ω : Prog C (.alias R :: Γ) Γ₁} {κ : Frames C Γ₁ Γ₂} {φ : Fml C Γ₂}
      (h : ProvesC I pay Γ₀ H (.modal m (args.declsThen (.cons (.declStorage R r none)
          (.cons (.block (body.wk (Thin.atop (.alias R :: ps) Γ)).2.2) .nil)))
        (.drop (.keep (Thin.ofExt (Ext.append Γ ps))) (.seq ω κ)) φ)) :
      ProvesC I pay Γ₀ H (.modal m (.cons (.call f args (.storage R r) body) ω) κ φ)
  /-- `internalCallExpand` of a call of a memory reference whose body may
  call back: the return object allocated at its default, the body as a
  block, the parameters thinned out from under the object. -/
  | callMem {Γ ps Γf Γ₁ Γ₂ : Ctx} {H : Hyps C Γ₀ Γ} {m : Modality} {f : Name}
      {args : Args C Γ ps} {R : RefTy} {r : Var} {hd : (Ty.ref R).defaultOkS = true}
      {hm : (Ty.ref R).mapFree = true} {body : Prog C ([.mem R] ++ ps) Γf}
      {ω : Prog C (.mem R :: Γ) Γ₁} {κ : Frames C Γ₁ Γ₂} {φ : Fml C Γ₂}
      (h : ProvesC I pay Γ₀ H (.modal m (args.declsThen (.cons (.declMem R r none hd hm)
          (.cons (.block (body.wk (Thin.atop (.mem R :: ps) Γ)).2.2) .nil)))
        (.drop (.keep (Thin.ofExt (Ext.append Γ ps))) (.seq ω κ)) φ)) :
      ProvesC I pay Γ₀ H (.modal m (.cons (.call f args (.mem R r hd hm) body) ω) κ φ)
  /-- **`transferWithCallbackBox`**: the invariant after the booking ("invariant
  on exit", `{U} I`), and the rest resumed after the callback, from any state
  the callee may leave in which the invariant holds (`{U} {havoc} (I → [ ω ] φ)`). -/
  | callback {Γ Γ₁ Γ₂ : Ctx} {H : Hyps C Γ₀ Γ} {s : Stmt C Γ Γ} {ω : Prog C Γ Γ₁}
      {κ : Frames C Γ₁ Γ₂} {φ : Fml C Γ₂} {U : Upd C Γ Γ}
      (d : CallbackTaclet C (H.freshC I (.modal .box (.cons s ω) κ φ)) .box s (.update U))
      (exit : ProvesC I pay Γ₀ H (.upd .box U (Fml.closedAt I)))
      (resume : ProvesC I pay Γ₀ (((H.upd .box U).havoc).pre (Fml.closedAt I))
        (.modalK .box ω κ φ)) :
      ProvesC I pay Γ₀ H (.modal .box (.cons s ω) κ φ)
  /-- **`sendWithCallbackBox`**: the invariant after the booking ("invariant on
  exit"); the rest after the booking and `pv := true`, from any state the
  callee may leave in which the invariant holds ("send succeeded"); the rest
  after `pv := false`, nothing booked ("send failed"). -/
  | send {Γ Γ₁ Γ₂ : Ctx} {H : Hyps C Γ₀ Γ} {pv : Idx Γ (.val .bool)} {sadr se : Simple C Γ .uint}
      {full : Bool}
      {ω : Prog C Γ Γ₁} {κ : Frames C Γ₁ Γ₂} {φ : Fml C Γ₂} {Uok Ufail : Upd C Γ Γ}
      (d : CallbackTaclet C
        (H.freshC I (.modal .box (.cons (.send pv (.simple sadr) (.simple se) full) ω) κ φ))
        .box (.send pv (.simple sadr) (.simple se) full) (.cases [] [Uok, Ufail]))
      (exit : ProvesC I pay Γ₀ H
        (.upd .box (Upd.nil.snoc (.pay sadr.lower se.lower)) (Fml.closedAt I)))
      (ok : ProvesC I pay Γ₀ (((H.upd .box Uok).havoc).pre (Fml.closedAt I)) (.modalK .box ω κ φ))
      (failed : ProvesC I pay Γ₀ (H.upd .box Ufail) (.modalK .box ω κ φ)) :
      ProvesC I pay Γ₀ H (.modal .box (.cons (.send pv (.simple sadr) (.simple se) full) ω) κ φ)
  /-- **`sendWithCallbackDiamond`**: `sendWithCallbackBox`'s goals under the
  diamond, and "non-negative amount". -/
  | sendD {Γ Γ₁ Γ₂ : Ctx} {H : Hyps C Γ₀ Γ} {pv : Idx Γ (.val .bool)} {sadr se : Simple C Γ .uint}
      {full : Bool} {ω : Prog C Γ Γ₁} {κ : Frames C Γ₁ Γ₂} {φ : Fml C Γ₂} {f : Fml C Γ}
      {Uok Ufail : Upd C Γ Γ}
      (d : CallbackTaclet C
        (H.freshC I (.modal .diamond (.cons (.send pv (.simple sadr) (.simple se) full) ω) κ φ))
        .diamond (.send pv (.simple sadr) (.simple se) full) (.cases [f] [Uok, Ufail]))
      (fml : ProvesC I pay Γ₀ H f)
      (exit : ProvesC I pay Γ₀ H
        (.upd .diamond (Upd.nil.snoc (.pay sadr.lower se.lower)) (Fml.closedAt I)))
      (ok : ProvesC I pay Γ₀ (((H.upd .diamond Uok).havoc).pre (Fml.closedAt I))
        (.modalK .diamond ω κ φ))
      (failed : ProvesC I pay Γ₀ (H.upd .diamond Ufail) (.modalK .diamond ω κ φ)) :
      ProvesC I pay Γ₀ H (.modal .diamond (.cons (.send pv (.simple sadr) (.simple se) full) ω) κ φ)
  /-- **`sendNoCallbackDiamond`**, a send that does not call back: "non-negative
  amount", then `sendDet`'s goals under the diamond. -/
  | sendDetD {Γ Γ₁ Γ₂ : Ctx} {H : Hyps C Γ₀ Γ} {pv : Idx Γ (.val .bool)}
      {sadr se : Simple C Γ .uint}
      {ω : Prog C Γ Γ₁} {κ : Frames C Γ₁ Γ₂} {φ : Fml C Γ₂}
      (hp : pay = false)
      (fml : ProvesC I pay Γ₀ H
        (.isBool (.app2 (.binop .le (p := .uint) rfl) (Tm.lit (p := .uint) ⟨0, rfl⟩) se.lower)
          true))
      (ok : ProvesC I pay Γ₀ (H.upd .diamond ((Upd.nil.snoc (UpdElem.payTo sadr se)).snoc
        (.local pv (.val (Tm.lit (p := .bool) true))))) (.modalK .diamond ω κ φ))
      (failed : ProvesC I pay Γ₀
        (H.upd .diamond (Upd.nil.snoc (.local pv (.val (Tm.lit (p := .bool) false)))))
        (.modalK .diamond ω κ φ)) :
      ProvesC I pay Γ₀ H
        (.modal .diamond (.cons (.send pv (.simple sadr) (.simple se) false) ω) κ φ)
  /-- **`tryCallWithCallbackBox`**: the invariant where control leaves
  ("invariant on exit"); the call's success, from any state the callee may
  leave in which the invariant holds, for every value of its return data
  ("call succeeded"); each clause's block where the call reverted, which
  undid whatever the callee did. -/
  | tryCall {Γ Γ₁ Γ₂ : Ctx} {H : Hyps C Γ₀ Γ} {s : Stmt C Γ Γ} {ω : Prog C Γ Γ₁}
      {κ : Frames C Γ₁ Γ₂} {φ : Fml C Γ₂} {b : Branch C Γ} {bs : List (Branch C Γ)}
      (d : CallbackTaclet C (H.freshC I (.modal .box (.cons s ω) κ φ)) .box s (.branches (b :: bs)))
      (exit : ProvesC I pay Γ₀ H (Fml.closedAt I))
      (ok : ProvesC I pay Γ₀ (H.havoc.pre (Fml.closedAt I))
        (b.bs.all (.modalK .box b.P (.pop .block ((Ext.append Γ b.ρ).trans b.P.ext) (.seq ω κ)) φ)))
      (caught : ∀ b ∈ bs, ProvesC I pay Γ₀ H
        (b.bs.all
          (.modalK .box b.P (.pop .block ((Ext.append Γ b.ρ).trans b.P.ext) (.seq ω κ)) φ))) :
      ProvesC I pay Γ₀ H (.modal .box (.cons s ω) κ φ)
  /-- **`tryCallSelfBox` with callbacks** (Lean, `docs/options.md` O8): a
  self-call `try`, `tryCallSelfBox`'s goals read as `tryCallWithCallbackBox`
  reads its own.  The invariant where control leaves ("invariant on exit");
  the receiver the contract: the callee inlined, which may itself call back,
  then the success block ("self call succeeded"); the receiver another
  contract: the success block from any state the callee may leave in which
  the invariant holds, for every value of the return data ("call
  succeeded"); each `catch` block from the caller's state, where the call
  does not end normally as a self-call (`ExtCall.selfFails`).  At address
  `0` the `require`s revert. -/
  | trySelf {Γ ρ κc Γok Γe Γ₃ Γ₄ ps Γf Γ₁ Γ₂ : Ctx} {H : Hyps C Γ₀ Γ} {call : ExtCall C Γ}
      {rets : Binders ρ} {body : Prog C (ρ ++ Γ) Γok} {errorBody : Prog C Γ Γe}
      {code : CodeBinder κc} {panicBody : Prog C (κc ++ Γ) Γ₃} {otherBody : Prog C Γ Γ₄}
      {selfArgs : Args C Γ ps} {selfBody : Prog C (ρ ++ ps) Γf} {ω : Prog C Γ Γ₁}
      {κ : Frames C Γ₁ Γ₂} {φ : Fml C Γ₂} {b₀ b₁ : Branch C Γ} {bs : List (Branch C Γ)}
      (d : LeanTaclet C (H.freshC I (.modal .box (.cons (.tryCall call rets body errorBody code
          panicBody otherBody selfArgs selfBody true) ω) κ φ)) .box
        (.tryCall call rets body errorBody code panicBody otherBody selfArgs selfBody true)
        (.branches (b₀ :: b₁ :: bs)))
      (exit : ProvesC I pay Γ₀ H (Fml.closedAt I))
      (self : ProvesC I pay Γ₀ H
        (b₀.bs.all (.modalK .box b₀.P
          (.pop .block ((Ext.append Γ b₀.ρ).trans b₀.P.ext) (.seq ω κ)) φ)))
      (ok : ProvesC I pay Γ₀ (H.havoc.pre (Fml.closedAt I))
        (b₁.bs.all (.modalK .box b₁.P
          (.pop .block ((Ext.append Γ b₁.ρ).trans b₁.P.ext) (.seq ω κ)) φ)))
      (caught : ∀ b ∈ bs, ProvesC I pay Γ₀ H
        (Option.casesOn (motive := fun _ => Fml C Γ) b.hyp
          (b.bs.all
            (.modalK .box b.P (.pop .block ((Ext.append Γ b.ρ).trans b.P.ext) (.seq ω κ)) φ))
          fun c => .imp c (b.bs.all
            (.modalK .box b.P (.pop .block ((Ext.append Γ b.ρ).trans b.P.ext) (.seq ω κ)) φ)))) :
      ProvesC I pay Γ₀ H (.modal .box (.cons (.tryCall call rets body errorBody code panicBody
        otherBody selfArgs selfBody true) ω) κ φ)

  /-- **A recursive call by a lemma** (Lean, `docs/kernel-port.md`,
  "Recursion"): a recursive call at the head of the box, where every reading
  of the goals `goals` is one of the call's: a contract proved by induction
  over the frames (`ProvesC.recContract`, `Calculus/RecursionCallback.lean`),
  or the call read without callbacks where nothing calls back
  (`ProvesC.recValid`). -/
  | recCall {Γ Γ' ps rs Γ₁ Γ₂ : Ctx} {H : Hyps C Γ₀ Γ} {m : Modality} {f : Name} {d : Nat}
      {args : Args C Γ ps} {ret : CallRet Γ rs Γ'} {body : Unit → Prog C (rs ++ ps) (rs ++ ps)}
      {ω : Prog C Γ' Γ₁} {κ : Frames C Γ₁ Γ₂} {φ : Fml C Γ₂} (goals : List (Fml C Γ))
      (hc : ∀ τ, (∀ ψ ∈ goals, holdsC I pay τ (H.wrap ψ)) →
        holdsC I pay τ (H.wrap (.modal m (.cons (.callRec f d args ret body) ω) κ φ)))
      (h : ∀ ψ ∈ goals, ProvesC I pay Γ₀ H ψ) :
      ProvesC I pay Γ₀ H (.modal m (.cons (.callRec f d args ret body) ω) κ φ)

end Solidity

namespace Solidity.Delab

open Lean Meta PrettyPrinter Delaborator SubExpr
open Solidity (ppOn isEscape)

/-- `CallbackTaclet C k m s p`: `dl[CallbackTaclet C k]{ [ s; ] ⇝ p }`,
as `Rules.lean`'s delaborator prints today's, the goals labelled as the
no-callback twin's. -/
@[delab app.Solidity.CallbackTaclet]
def delabCallbackTaclet : Delab := do
  unless ← ppOn do failure
  let e ← getExpr
  guard (e.getAppNumArgs == 7)
  let m ← whnf (e.getArg! 2)
  let some (s, p) ← tacletLine? e (e.getArg! 5) (e.getArg! 6) m | failure
  if isEscape s then failure
  let args ← (List.range 2).toArray.mapM fun i => withNaryArg i delab
  let J ← `($(mkIdent (← unresolveNameGlobal ``CallbackTaclet)) $args*)
  match_expr m with
  | Modality.box => `(dl[ $J ]{ [ $s:sol_stmt; ] ⇝ $p })
  | Modality.diamond => `(dl[ $J ]{ ⟨ $s:sol_stmt; ⟩ ⇝ $p })
  | _ => `(dl[ $J ]{ ⟨[ $s:sol_stmt; ]⟩ ⇝ $p })

/-- `ProvesC I pay Γ₀ H φ`: the sequent `dl{ ..H, h₁, … ⟹ᶜ[I] φ }`
(`⟹ᶜ[I; noCallback]` unless `pay`), the context printed as `delabProves`
prints it. -/
@[delab app.Solidity.ProvesC]
def delabProvesC : Delab := do
  unless ← ppOn do failure
  let e ← getExpr
  guard (e.getAppNumArgs == 7)
  let c := e.getArg! 0
  let out? ← withPrinter (contract? := some c) e true do
    let some (rest, hs, ns) ← (try some <$> hypsPartsS c (e.getArg! 5) catch _ => pure none)
      | return none
    let φ ← ppFmlS ns (e.getArg! 6)
    let mut out : Array (TSyntax `dl_hyp) := #[]
    if let some r := rest then out := out.push (← `(dl_hyp| ..$(mkIdent r):ident))
    for h in hs do out := out.push ⟨← fixBlockEnds h⟩
    return some (out, (⟨← fixBlockEnds φ⟩ : TSyntax `dl_fml))
  let some (out, φ) := out? | failure
  guard !(isEscape φ)
  let I ← withNaryArg 1 delab
  match_expr ← whnfR (e.getArg! 2) with
  | Bool.false => `(dl{ $[$out],* ⟹ᶜ[$I; noCallback] $φ:dl_fml })
  | _ => `(dl{ $[$out],* ⟹ᶜ[$I] $φ:dl_fml })

end Solidity.Delab
