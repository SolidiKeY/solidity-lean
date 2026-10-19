import Solidity.Calculus.CallbackRules
import Solidity.Calculus.Delab
import Solidity.Calculus.Proves
import Solidity.Semantics.Callback

/-!
# The callback taclets on scoped statements

The callback taclets (`CallbackTaclet`, solkey's `…WithCallbackBox`) are
`Calculus/CallbackRules.lean`'s, below the sequents, so the rule table's
checks (`Calculus/RuleShapes.lean`) read them without the judgement: what a
callback changes is how the premise is read, the invariant owed on exit and
the callee's `{havoc}` (`ProvesC`), not what the rule leaves.

The rules print as today's (`dl[CallbackTaclet C k]{ … }`, `delabCallbackTaclet`),
their goals labelled by their no-callback twins' labels.

`ProvesC I H φ` is the callback judgement on scoped sequents:
the ordinary rules on a statement that runs no other and pays nothing
(`Stmt.forks`), a split, the callback taclets with solkey's goals
("invariant on exit", the rest resumed under `{havoc}` with the invariant
assumed), and the plain calculus (`Proves`) on a goal with no `transfer`
left.  The invariant is a closed formula `I : Fml C []`, read in any scope
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

/-- `ProvesC I pay H φ`: the calculus proves `φ` in the context `H` when a
callee may call back into a contract with invariant `I`, from every `try`
and, when `pay` is set, from every `transfer` and `send`. -/
inductive ProvesC (I : Fml C []) (pay : Bool) (Γ₀ : Ctx) :
    {Γ : Ctx} → Hyps C Γ₀ Γ → Fml C Γ → Prop where
  /-- A goal where nothing calls back is a goal of the calculus: there the
  two readings agree. -/
  | plain {Γ : Ctx} {H : Hyps C Γ₀ Γ} {φ : Fml C Γ} (h : Proves C .all Γ₀ H φ)
      (hφ : (H.wrap φ).callsBack pay = false) : ProvesC I pay Γ₀ H φ
  /-- `impRight`. -/
  | intro {Γ : Ctx} {H : Hyps C Γ₀ Γ} {a φ : Fml C Γ} (h : ProvesC I pay Γ₀ (H.pre a) φ) :
      ProvesC I pay Γ₀ H (.imp a φ)
  /-- `allRight`. -/
  | allIntro {Γ : Ctx} {H : Hyps C Γ₀ Γ} {x : Var} {p : PrimTy} {φ : Fml C (.val p :: Γ)}
      (h : ProvesC I pay Γ₀ (H.all x p) φ) : ProvesC I pay Γ₀ H (.all x p φ)
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
