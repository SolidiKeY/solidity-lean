import Solidity.Source.Progress.LiteralBuiltins

/-! A direct builtin admission over the existing checked whole-program call
fragment. It admits scalar/constant argument expressions and literal bytes.
It does not change the old checker or admit emitting/builtin callee bodies.
Memory/storage/calldata byte expressions need invariant-relative admission.
-/
namespace Solidity.Source.Progress
open EM
variable {E : Env}

inductive ArgFragment (C : Decl → Prop) {Γ : RCtx} : {t : STy} → RExpr E Γ t → Prop
  | checked {t} (e : RExpr E Γ t) : e.ValFragC C → e.OpsOK → ArgFragment C e
  | literal (bs : Roadmap.Bytes) : ArgFragment C (.str bs)

inductive ArgsFragment (C : Decl → Prop) {Γ : RCtx} : {ts : List STy} → RArgs E Γ ts → Prop
  | nil : ArgsFragment C .nil
  | cons {t ts} {e : RExpr E Γ t} {es : RArgs E Γ ts} :
      ArgFragment C e → ArgsFragment C es → ArgsFragment C (.cons e es)

theorem argsFragment_ns {C : Decl → Prop} (G : Glob E) (F : Fr)
    (he : ∀ n, ExprNSAt C G F n) {Γ : RCtx} {ts : List STy} (es : RArgs E Γ ts)
    (hf : ArgsFragment C es) (n : Nat) :
    NS (evalArgs G F n es) ∧ NS (evalArgsRev G F n es) := by
  have arg : ∀ n {t} (e : RExpr E Γ t), ArgFragment C e → NS (evalE G F n e) := by
    intro n t e h
    cases h with
    | checked e hf ho => exact (he n).val e hf ho
    | literal bs =>
      cases n
      · exact NS.halt' fun _ h => by cases h
      · exact NS.pure' _
  induction n generalizing ts with
  | zero => exact ⟨NS.halt' (fun _ h => by cases h), NS.halt' (fun _ h => by cases h)⟩
  | succ n ih =>
    cases hf with
    | nil => exact ⟨NS.pure' _, NS.pure' _⟩
    | cons h hs =>
      have ht := ih _ hs
      exact ⟨NS.bind (arg n _ h) fun _ => NS.bind ht.1 fun _ => NS.pure' _,
        NS.bind ht.2 fun _ => NS.bind (arg n _ h) fun _ => NS.pure' _⟩

/-- Typed intrinsic builtin nodes additionally carry the unchanged callTy
equation. This predicate selects the proved direct fragment, not a replacement
source typing rule. -/
inductive BuiltinFragment (C : Decl → Prop) {Γ : RCtx} :
    (b : Builtin) → {ts : List STy} → RArgs E Γ ts → STy → Prop
  | require (args : RArgs E Γ [.bool]) : ArgsFragment C args →
      BuiltinFragment C .require args (.tuple [])
  | assert (args : RArgs E Γ [.bool]) : ArgsFragment C args →
      BuiltinFragment C .assert args (.tuple [])
  | revert (args : RArgs E Γ []) : ArgsFragment C args →
      BuiltinFragment C .revert args (.tuple [])
  | requireLiteral (bs : Roadmap.Bytes) (args : RArgs E Γ [.bool, .stringLit bs]) :
      ArgsFragment C args → BuiltinFragment C .require args (.tuple [])
  | revertLiteral (bs : Roadmap.Bytes) (args : RArgs E Γ [.stringLit bs]) :
      ArgsFragment C args → BuiltinFragment C .revert args (.tuple [])
  | hashLiteral (bs : Roadmap.Bytes) (b : Builtin) (args : RArgs E Γ [.stringLit bs])
      (k : Nat) (hk : 0 < k ∧ k ≤ 32) :
      (b = .keccak256 ∨ b = .sha256 ∨ b = .ripemd160) → ArgsFragment C args →
      BuiltinFragment C b args (.fixedBytes k hk)
  | mod (b : Builtin) {x y k : STy} (args : RArgs E Γ [x,y,k]) :
      (b = .addmod ∨ b = .mulmod) →
      ScalarSource x → ScalarSource y → ScalarSource k →
      x.implicit E.isBase E.mapFree (.int IntTy.u256) = true →
      y.implicit E.isBase E.mapFree (.int IntTy.u256) = true →
      k.implicit E.isBase E.mapFree (.int IntTy.u256) = true →
      ArgsFragment C args → BuiltinFragment C b args (.int IntTy.u256)
  | recovery {h v r s : STy} (args : RArgs E Γ [h,v,r,s]) :
      WordSource h → WordSource v → WordSource r → WordSource s →
      h.implicit E.isBase E.mapFree .bytes32 = true →
      v.implicit E.isBase E.mapFree (.int IntTy.u8) = true →
      r.implicit E.isBase E.mapFree .bytes32 = true →
      s.implicit E.isBase E.mapFree .bytes32 = true →
      ArgsFragment C args → BuiltinFragment C .ecrecover args (.address false)

theorem builtinFragment_ns {C : Decl → Prop} (G : Glob E) (F : Fr)
    (he : ∀ n, ExprNSAt C G F n) {Γ : RCtx} {ts : List STy} {b : Builtin}
    {args : RArgs E Γ ts} {t : STy} (hf : BuiltinFragment C b args t) (n : Nat) :
    NS (evalBuiltin G F n b args t) := by
  cases n with
  | zero => exact NS.halt' fun _ h => by cases h
  | succ n =>
    cases hf with
    | require args h => exact evalBuiltin_require_ns G F n args (argsFragment_ns G F he args h n).1
    | assert args h => exact evalBuiltin_assert_ns G F n args (argsFragment_ns G F he args h n).1
    | revert args h => exact evalBuiltin_revert_ns G F n args (argsFragment_ns G F he args h n).1
    | requireLiteral bs args h => exact evalBuiltin_requireLiteral_ns G F n bs args (argsFragment_ns G F he args h n).1
    | revertLiteral bs args h => exact evalBuiltin_revertLiteral_ns G F n bs args (argsFragment_ns G F he args h n).1
    | hashLiteral bs b args k hk hb h => exact evalBuiltin_hashLiteral_ns G F n bs b hb args k hk (argsFragment_ns G F he args h n).1
    | mod b args hb hx hy hk cx cy ck h =>
      exact evalBuiltin_mod_ns G F n b hb args hx hy hk cx cy ck
        (argsFragment_ns G F he args h n).1 (argsFragment_ns G F he args h n).2
    | recovery args hh hv hr hs ch cv cr cs h =>
      exact evalBuiltin_ecrecover_ns G F n args hh hv hr hs ch cv cr cs (argsFragment_ns G F he args h n).1

theorem checked_builtin (res : Resolution) (G : Glob res.env) (c : String)
    (ha : (Source.elaborate res).isSome = true) (hg : G.prog = Source.progOf res.env)
    (hc : Solidity.Lowering.P9.WholeProgram.checkFunctions res G c = true)
    (F : Fr) (hF : F.contract = c) (n : Nat) {Γ : RCtx} {ts : List STy}
    (b : Builtin) (args : RArgs res.env Γ ts) (t : STy)
    (ht : b.callTy res.env.isBase res.env.mapFree ts = some t)
    (hf : BuiltinFragment (fun d => d ∈ Solidity.Lowering.P9.WholeProgram.functions res) b args t) :
    NS (evalE G F n (.builtin b args ht)) := by
  cases n with
  | zero => exact NS.halt' fun _ h => by cases h
  | succ n => exact builtinFragment_ns G F (fun k => (checked_fragments ha hg hc k).1.expr F hF) hf n

#print axioms argsFragment_ns
#print axioms builtinFragment_ns
#print axioms checked_builtin
end Solidity.Source.Progress
