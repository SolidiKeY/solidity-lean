import Solidity.Correctness.Elab.HashCongruence

/-! # Instantiated hash agreement checks
Callbacks may differ away from the exact requested input. The error checks
also pin the boundary at which later callbacks cannot run. -/
namespace Solidity.Examples.ElabTotal.HashCongruence
open Solidity ElabAgree
variable (C : Contract) [FreshNames]

private def one (e : RawExpr) : ElabM (SProg C × RawExpr) := pure ([], e)
private def onlyName (e : RawExpr) : ElabM (SProg C × RawExpr) :=
  match e with
  | .name "input" => pure ([], e)
  | _ => throw "unreachable hoist"
private def bytes (_ : RawExpr) : ElabM (SProg C × String) := pure ([], "buffer")
private def stmts (_ : List RawStmt) : ElabM (SProg C) := pure []

/-- Distinct hoisters agree at the actual successful input, including the
fresh name, final state, and memo, for both bytes32 and bytes20 hashes. -/
example (sc : ElabScope) (f : String) (hf : f ≠ "ecrecover") :
    Agree sc (hoistHashWith C (one C) (bytes C) (stmts C) f [.name "input"])
      (hoistHashWith C (onlyName C) (bytes C) (stmts C) f [.name "input"]) := by
  apply hoistHashWith_single_agree C _ _ _ _ _ _ sc f (.name "input") hf
  · intro st m
    simp [one, onlyName]
  · intros; exact agree_refl _ _
  · intros; exact agree_refl _ _

/-- Successful hashing allocates exactly one capture after both callbacks. -/
example (sc : ElabScope) (st : ECtx × Nat) (m : CallMemo) :
    hoistHashWith C (one C) (bytes C) (stmts C) "ripemd160" [.name "input"] sc st m =
      .ok ((([], .name (toString (Var.fresh "se" st.2))), (st.1, st.2 + 1)), m) := by
  rfl

/-- Each later callback checks the preceding output, including the fresh
capture in the final result. -/
example (sc : ElabScope) (st : ECtx × Nat) (m : CallMemo) :
    hoistHashWith C (fun _ => pure ([], .name "lowered"))
      (fun e => match e with
        | .name "lowered" => pure ([], "copied")
        | _ => throw "wrong lowered output")
      (fun ss => match ss with
        | [.decl (.named "bytes20") _ (some (.field (.name "copied") member))] =>
          if member == hashMember .ripemd160
          then pure [] else throw "wrong declaration"
        | _ => throw "wrong statement input")
      "ripemd160" [.name "source"] sc st m =
      .ok ((([], .name (toString (Var.fresh "se" st.2))), (st.1, st.2 + 1)), m) := by
  rfl

/-- A failing byte callback stops before allocation and statements. -/
example (sc : ElabScope) (st : ECtx × Nat) (m : CallMemo)
    (S : List RawStmt → ElabM (SProg C)) :
    hoistHashWith C (one C) (fun _ => throw "byte boundary") S
      "sha256" [.name "input"] sc st m = .error "byte boundary" := by
  rfl

/-- The ecrecover hoister consumes the ABI tuple, not four independent calls. -/
example (sc : ElabScope) (st : ECtx × Nat) (m : CallMemo)
    (B : RawExpr → ElabM (SProg C × String)) (S : List RawStmt → ElabM (SProg C)) :
    hoistHashWith C (fun e => match e with
      | .call "abi.encode" [.num 1,.num 2,.num 3,.num 4] => throw "encoded boundary"
      | _ => pure ([], e)) B S "ecrecover"
      [.num 1,.num 2,.num 3,.num 4] sc st m = .error "encoded boundary" := by
  rfl

/-- Arity errors win over callbacks, even when every callback fails. -/
example (sc : ElabScope) (st : ECtx × Nat) (m : CallMemo) :
    hoistHashWith C (fun _ => throw "hoist") (fun _ => throw "bytes")
      (fun _ => throw "statements") "ecrecover" [.num 0] sc st m =
      .error "ecrecover takes four arguments" := by rfl

example (sc : ElabScope) (st : ECtx × Nat) (m : CallMemo) :
    hoistERC7201With C (fun _ => throw "hoist") [] sc st m =
      .error "erc7201 takes one string argument" := by rfl

/-- Malformed ordinary hashes reject arbitrary callbacks before invoking
any of them; instantiate the arity congruence against successful callbacks. -/
example (sc : ElabScope) (st : ECtx × Nat) (m : CallMemo)
    (H : RawExpr → ElabM (SProg C × RawExpr))
    (B : RawExpr → ElabM (SProg C × String)) (S : List RawStmt → ElabM (SProg C)) :
    hoistHashWith C H B S "sha256" [.num 1, .num 2] sc st m =
      .error "sha256 takes one argument" := by
  exact hoistHashWith_bad_arity_agree C H (one C) B (bytes C) S (stmts C) sc
    "sha256" [.num 1, .num 2] (by decide) st m

/-- A literal root folds successfully even with an always failing callback. -/
example (sc : ElabScope) (st : ECtx × Nat) (m : CallMemo) :
    hoistERC7201With C (fun _ => throw "unreachable") [RawExpr.bytesLit []] sc st m =
      .ok ((([], .num (ERC7201.root []).val), st), m) := by rfl

/-- A successful ecrecover instance uses the same staged congruence. -/
example (sc : ElabScope) :
    Agree sc (hoistHashWith C (one C) (bytes C) (stmts C) "ecrecover"
      [.num 1,.num 2,.num 3,.num 4])
      (hoistHashWith C (fun e => pure ([], e)) (bytes C) (stmts C) "ecrecover"
      [.num 1,.num 2,.num 3,.num 4]) := by
  apply hoistHashWith_ecrecover_agree
  · exact agree_refl _ _
  · intros; exact agree_refl _ _
  · intros; exact agree_refl _ _

private def onDynamic (e : RawExpr) : ElabM (SProg C × RawExpr) :=
  match e with
  | .binop .band (.call "uint256" [.call "keccak256" [.call "abi.encode"
      [.binop .subW (.call "uint256" [.call "keccak256" [.name "input"]]) (.num 1)]]])
      (.num n) =>
    if n == 2 ^ 256 - 256 then pure ([], e) else throw "wrong mask"
  | _ => throw "wrong expression"

/-- The dynamic callback succeeds only on the exact ERC7201 expression. -/
example (sc : ElabScope) (st : ECtx × Nat) (m : CallMemo) :
    hoistERC7201With C (onDynamic C) [.name "input"] sc st m =
      .ok ((([], .binop .band (.call "uint256" [.call "keccak256" [.call "abi.encode"
        [.binop .subW (.call "uint256" [.call "keccak256" [.name "input"]]) (.num 1)]]])
        (.num (2 ^ 256 - 256))), st), m) := by rfl

/-- Instantiate dynamic congruence with callbacks that differ elsewhere. -/
example (sc : ElabScope) :
    Agree sc (hoistERC7201With C (one C) [.name "input"])
      (hoistERC7201With C (onDynamic C) [.name "input"]) := by
  apply hoistERC7201With_agree
  intro a ha _
  cases ha
  intro st m
  rfl

/-- Dynamic ERC7201 forwards the complete callback failure. -/
example (sc : ElabScope) (st : ECtx × Nat) (m : CallMemo) :
    hoistERC7201With C (fun _ => throw "dynamic boundary") [.name "input"] sc st m =
      .error "dynamic boundary" := by rfl

end Solidity.Examples.ElabTotal.HashCongruence
