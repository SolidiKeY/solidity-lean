import Solidity.Source.WellFormed
import Solidity.Source.Examples

/-!
# S01 controls: typing derivations and constructor coverage

A contract with state variables of several types and a function with
parameters, a derivation for every expression constructor S01 types
(`exprCoverage`), the counter of `Solidity/Source/Examples.lean` proved well
formed, and ill-typed programs refuted.
-/

namespace Solidity.Source.TypingExamples

open Solidity.Source Solidity.Source.Examples

/-- `bool`. -/
def tBool : Syn .typeName := .elem .bool

/-- ```
contract C {
  uint256 count; bool flag; uint256[] arr; mapping(address => uint256) m; uint8 small;
}
``` -/
def unitC : Syn .unit :=
  .unit (.cons (.contract false "C" .none .nil
    (.cons (.stateVar u256 none none none false "count" .none)
    (.cons (.stateVar tBool none none none false "flag" .none)
    (.cons (.stateVar (.array u256 .none) none none none false "arr" .none)
    (.cons (.stateVar (.mapping (.elem .address (by decide)) none u256 none) none none none false "m" .none)
    (.cons (.stateVar (.elem (.int false 8 (by decide))) none none none false "small" .none)
      .nil)))))) .nil)

/-- The body context of `function f(uint256 a, bool b, address o) returns (uint256)`. -/
def Γ : Ctx := ⟨unitC.env, some "C", [("o", .address false), ("b", .bool), ("a", .int IntTy.u256)],
  [.int IntTy.u256]⟩

def a : Syn .expr := .ident "a"
def one : Syn .expr := .lit (.num (.dec 1 0 0))

theorem ty_a : HasType Γ a (.int IntTy.u256) := .var rfl
theorem ty_b : HasType Γ (.ident "b") .bool := .var rfl
theorem ty_count : HasType Γ (.ident "count") (.int IntTy.u256) := .var rfl
theorem ty_flag : HasType Γ (.ident "flag") .bool := .var rfl
theorem ty_arr : HasType Γ (.ident "arr") (.array .storage (.int IntTy.u256) none) := .var rfl
theorem ty_m : HasType Γ (.ident "m") (.mapping (.address false) (.int IntTy.u256)) := .var rfl
theorem ty_one : HasType Γ one (.rational (Q.ofInt 1)) := .const rfl

/-! ## One derivation per typed expression constructor -/

theorem w_ident : HasType Γ (.ident "a") (.int IntTy.u256) := ty_a
theorem w_lit : HasType Γ (.lit (.bool true)) .bool := .bool true
theorem w_litUnit : HasType Γ (.litUnit (.dec 1 0 0) .ether)
    (.rational ((NumLit.dec 1 0 0).value.mul (Q.ofInt (Denom.factor .ether)))) :=
  .const rfl
theorem w_tuple : HasType Γ (.tuple (.some a) (.cons (.some (.ident "b")) .nil))
    (.tuple [.int IntTy.u256, .bool]) :=
  .tuple ty_a (.cons ty_b .nil) (by simp)
theorem w_index : HasType Γ (.index (.ident "arr") (.some one)) (.int IntTy.u256) :=
  .indexArray ty_arr ty_one rfl
theorem w_index_mapping : HasType Γ (.index (.ident "m") (.some (.ident "o"))) (.int IntTy.u256) :=
  .indexMapping ty_m (.var rfl) rfl
theorem w_member : HasType Γ (.member (.ident "arr") "length") (.int IntTy.u256) := .length ty_arr rfl
theorem w_call : HasType Γ (.call (.elemType (.int false 8 (by decide)) (by decide))
    (.positional (.cons a .nil))) (.int IntTy.u8) := .convElem ty_a rfl
theorem w_payableConv : HasType Γ (.payableConv (.positional (.cons (.ident "o") .nil))) (.address true) :=
  .payable (.var rfl) rfl
theorem w_unaryPrefix : HasType Γ (.unaryPrefix .not (.ident "flag")) .bool := .not ty_flag
theorem w_unarySuffix : HasType Γ (.unarySuffix .inc (.ident "count")) (.int IntTy.u256) :=
  .incDecSuffix rfl ty_count rfl
theorem w_exp : HasType Γ (.exp a one) (.int IntTy.u256) := .exp rfl ty_a ty_one rfl
theorem w_mulDivMod : HasType Γ (.mulDivMod .mul a one) (.int IntTy.u256) :=
  .arith rfl ty_a ty_one rfl rfl
theorem w_addSub : HasType Γ (.addSub .add a a) (.int IntTy.u256) := .arith rfl ty_a ty_a rfl rfl
theorem w_shift : HasType Γ (.shift .shl a one) (.int IntTy.u256) := .shift rfl ty_a ty_one rfl
theorem w_bitAnd : HasType Γ (.bitAnd a a) (.int IntTy.u256) := .bit rfl ty_a ty_a rfl rfl
theorem w_bitXor : HasType Γ (.bitXor a a) (.int IntTy.u256) := .bit rfl ty_a ty_a rfl rfl
theorem w_bitOr : HasType Γ (.bitOr a a) (.int IntTy.u256) := .bit rfl ty_a ty_a rfl rfl
theorem w_order : HasType Γ (.order .lt a one) .bool := .order rfl ty_a ty_one rfl rfl
theorem w_equality : HasType Γ (.equality .eq a a) .bool := .eq rfl ty_a ty_a rfl rfl
theorem w_and : HasType Γ (.and (.ident "b") (.ident "flag")) .bool := .logic rfl ty_b ty_flag
theorem w_or : HasType Γ (.or (.ident "b") (.ident "flag")) .bool := .logic rfl ty_b ty_flag
theorem w_cond : HasType Γ (.cond (.ident "b") a a) (.int IntTy.u256) := .cond ty_b ty_a ty_a rfl
theorem w_assign : HasType Γ (.assign .assign (.ident "count") a) (.int IntTy.u256) :=
  .assign rfl ty_count ty_a rfl

/-! ## Builtins, events and errors -/

theorem w_msgSender : HasType Γ (.member (.ident "msg") "sender") (.address false) := .magic rfl rfl rfl

/-- `require(b, "no");` -/
theorem w_require : StmtOK (k := .body) Γ (.simpleStmt (.exprStmt (.call (.ident "require")
    (.positional (.cons (.ident "b") (.cons (.lit (.str [110, 111])) .nil)))))) Γ :=
  .expr (.builtinCall rfl rfl (.cons ty_b (.cons (.str _) .nil)) rfl)

/-- `gasleft()` has no typing rule: an excluded builtin. -/
theorem gasleft_untyped (τ : STy) (h : HasType Γ (.call (.ident "gasleft") (.positional .nil)) τ) : False := by
  cases h with
  | builtinCall hr hs _ _ =>
    have e : Γ.resolve "gasleft" = some (.builtin .gasleft) := rfl
    rw [e] at hr
    cases hr
    cases hs
  | callInternal hd _ _ _ _ => cases hd
  | const hq => nomatch hq
  | arith hb => nomatch hb
  | bit hb => nomatch hb
  | shift hb => nomatch hb
  | exp hb => nomatch hb
  | order hb => nomatch hb
  | eq hb => nomatch hb
  | compareConst hb => nomatch hb
  | logic hb => nomatch hb

/-- `contract E { event Done(uint256 v); error Bad(); }` -/
def unitE : Syn .unit :=
  .unit (.cons (.contract false "E" .none .nil
    (.cons (.event "Done" (.cons (.eventParam u256 false (some "v")) .nil) false)
    (.cons (.error "Bad" .nil) .nil))) .nil)

/-- A function body of `E` with a local `a : uint256`. -/
def ΓE : Ctx := ⟨unitE.env, some "E", [("a", .int IntTy.u256)], []⟩

/-- `emit Done(a);` -/
theorem w_emit : StmtOK (k := .body) ΓE (.emit (.ident "Done") (.positional (.cons (.ident "a") .nil))) ΓE :=
  .emit (List.mem_singleton.2 rfl) rfl (.cons (.var rfl) .nil) rfl rfl

/-- `revert Bad();` -/
theorem w_revertError : StmtOK (k := .body) ΓE (.revert (.ident "Bad") (.positional .nil)) ΓE :=
  .revertError (List.mem_singleton.2 rfl) rfl .nil rfl rfl

/-! ## Coverage -/

/-- How S01 covers an expression constructor. -/
inductive Coverage where
  | typed
  /-- Deferred to a stage, with the reason. -/
  | deferred (stage reason : String)
  deriving DecidableEq, Repr

/-- The expression constructors of S00. -/
def exprCtors : List Ctor :=
  [.index, .slice, .member, .callOptions, .call, .payableConv, .metaType, .unaryPrefix,
    .unarySuffix, .exp, .mulDivMod, .addSub, .shift, .bitAnd, .bitXor, .bitOr, .order, .equality,
    .and, .or, .cond, .assign, .new, .tuple, .inlineArray, .ident, .lit, .litUnit, .elemType]

/-- **The coverage of every expression constructor.** -/
def exprCoverage : Ctor → Coverage
  | .slice => .deferred "S02" "calldata slices are typed with the calldata references of S02"
  | .callOptions => .deferred "S02" "call options belong to external calls and creation (S02/S03)"
  | .metaType => .deferred "S04.02" "type(T) members read the artifact table and ABI identities"
  | .new => .deferred "S03" "creation and memory allocation are typed with their semantics"
  | .inlineArray => .deferred "S02" "inline arrays take the mobile type of their elements (S02)"
  | .elemType => .deferred "S01" "a type name is typed only as a conversion callee (rule convElem)"
  | _ => .typed

/-- Every expression constructor is in the list, and the list holds only
expression constructors (each one's witness or deferral below). -/
theorem exprCtors_length : exprCtors.length = 29 := rfl

/-- **Coverage**: every expression constructor classified as typed has a
derivation whose root is that constructor. -/
theorem exprCoverage_typed : ∀ k ∈ exprCtors, exprCoverage k = .typed →
    ∃ (e : Syn .expr) (τ : STy), e.ctor = k ∧ HasType Γ e τ := by
  intro k hk ht
  simp only [exprCtors, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    first
    | exact ⟨_, _, rfl, w_index⟩
    | exact ⟨_, _, rfl, w_member⟩
    | exact ⟨_, _, rfl, w_call⟩
    | exact ⟨_, _, rfl, w_payableConv⟩
    | exact ⟨_, _, rfl, w_unaryPrefix⟩
    | exact ⟨_, _, rfl, w_unarySuffix⟩
    | exact ⟨_, _, rfl, w_exp⟩
    | exact ⟨_, _, rfl, w_mulDivMod⟩
    | exact ⟨_, _, rfl, w_addSub⟩
    | exact ⟨_, _, rfl, w_shift⟩
    | exact ⟨_, _, rfl, w_bitAnd⟩
    | exact ⟨_, _, rfl, w_bitXor⟩
    | exact ⟨_, _, rfl, w_bitOr⟩
    | exact ⟨_, _, rfl, w_order⟩
    | exact ⟨_, _, rfl, w_equality⟩
    | exact ⟨_, _, rfl, w_and⟩
    | exact ⟨_, _, rfl, w_or⟩
    | exact ⟨_, _, rfl, w_cond⟩
    | exact ⟨_, _, rfl, w_assign⟩
    | exact ⟨_, _, rfl, w_tuple⟩
    | exact ⟨_, _, rfl, w_ident⟩
    | exact ⟨_, _, rfl, w_lit⟩
    | exact ⟨_, _, rfl, w_litUnit⟩
    | (simp only [exprCoverage, reduceCtorEq] at ht)

/-! ## Resolution controls -/

/-- `contract A {} contract B is A {} contract C is A {} contract D is B, C {}` -/
def diamond : Syn .unit :=
  .unit (.cons (.contract false "A" .none .nil .nil)
    (.cons (.contract false "B" .none (.cons (.inherit ⟨"A", []⟩ .none) .nil) .nil)
    (.cons (.contract false "C" .none (.cons (.inherit ⟨"A", []⟩ .none) .nil) .nil)
    (.cons (.contract false "D" .none (.cons (.inherit ⟨"B", []⟩ .none)
      (.cons (.inherit ⟨"C", []⟩ .none) .nil)) .nil) .nil))))

/-- **C3**: `D`'s linearization, most derived first, is `D, C, B, A`. -/
theorem diamond_linearize : diamond.env.linearize "D" = some ["D", "C", "B", "A"] := rfl

/-- `contract X is Y {} contract Y is X {}`: a cycle has no linearization. -/
theorem cycle_rejected :
    (Syn.unit (.cons (.contract false "X" .none (.cons (.inherit ⟨"Y", []⟩ .none) .nil) .nil)
      (.cons (.contract false "Y" .none (.cons (.inherit ⟨"X", []⟩ .none) .nil) .nil) .nil))).env.linearize
      "X" = none := rfl

/-- An excluded builtin resolves, and is refused with its feature. -/
theorem gasleft_excluded :
    Γ.resolve "gasleft" = some (.builtin .gasleft) ∧ Builtin.gasleft.status = .excluded "gasleft" :=
  ⟨rfl, rfl⟩

/-- An excluded member: `block.number`. -/
theorem blockNumber_excluded : Builtin.block.memberStatus "number" = some (.excluded "blockNumber") := rfl

/-- A local shadows a state variable. -/
theorem local_shadows :
    ({ Γ with locals := ("count", .bool) :: Γ.locals } : Ctx).varTy "count" = some .bool := rfl

/-! ## Typing controls -/

/-- A number literal has only its exact rational type. -/
theorem HasType.lit_num {Γ : Ctx} {n : NumLit} {σ : STy} (h : HasType Γ (.lit (.num n)) σ) :
    σ = .rational n.value := by
  cases h with
  | const hq =>
    have hv : (Syn.lit (.num n) : Syn .expr).const = some n.value := rfl
    rw [hv] at hq
    cases hq
    rfl
  | arith hb => nomatch hb
  | bit hb => nomatch hb
  | shift hb => nomatch hb
  | exp hb => nomatch hb
  | order hb => nomatch hb
  | eq hb => nomatch hb
  | compareConst hb => nomatch hb
  | logic hb => nomatch hb

/-- `uint8 x = 300;` -/
def tooBig : Syn (.stmt .body) :=
  .simpleStmt (.declVar (.varDecl (.elem (.int false 8 (by decide))) none "x")
    (.some (.lit (.num (.dec 300 0 0)))))

/-- **An out-of-range constant does not convert**: `uint8 x = 300;` is ill
typed in every context. -/
theorem tooBig_illTyped (Γ Γ' : Ctx) : ¬ StmtOK Γ tooBig Γ' := by
  intro h
  cases h with
  | declInit ht he hc =>
    have hσ := HasType.lit_num he
    subst hσ
    simp only [Syn.ty, Syn.tys, Elem.ty] at ht
    cases ht
    simp only [STy.implicit] at hc
    revert hc
    decide

/-- `uint8 x = 255;` is well typed. -/
theorem fits_wellTyped : StmtOK (k := .body) Γ (.simpleStmt (.declVar (.varDecl (.elem (.int false 8 (by decide)))
    none "x") (.some (.lit (.num (.dec 255 0 0)))))) (Γ.push "x" (.int IntTy.u8)) :=
  .declInit rfl (.const rfl) rfl

/-! ## A well-formed unit -/

/-- The counter under the legacy pipeline. -/
def counterRes : Resolution := resolveUnit ⟨.legacy, []⟩ counter

/-- The counter's contract definition. -/
def counterTop : Syn .top :=
  .contract false "Counter" .none .nil
    (.cons (.stateVar u256 (some .pub) none none false "count" .none)
      (.cons (extFn "inc" (.cons incStmt .nil)) .nil))

/-- The counter's declarations, explicitly. -/
theorem counter_decls_eq : counter.decls =
    [⟨.contract, "Counter", none, true, counterTop⟩,
     ⟨.stateVar, "count", some "Counter", false, .stateVar u256 (some .pub) none none false "count" .none⟩,
     ⟨.function, "inc", some "Counter", false, extFn "inc" (.cons incStmt .nil)⟩] := rfl

/-- **The counter is well formed** (and inside the profile's syntax). -/
theorem counter_wellFormed : WellFormed counterRes ∧ InProfileSyntax counterRes := by
  have hd : counterRes.unit.decls = _ := counter_decls_eq
  refine ⟨⟨?_, ?_, by decide, ?_, ?_⟩, rfl⟩
  · intro d hm _
    rw [hd] at hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl <;> rfl
  · intro d hm d' hm' hc
    rw [hd] at hm hm'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm hm'
    rcases hm with rfl | rfl | rfl <;> rcases hm' with rfl | rfl | rfl <;>
      first | rfl | exact absurd hc (by decide)
  · intro d hm e he
    rw [hd] at hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl <;> cases he
  · intro d hm b hb
    rw [hd] at hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl
    · cases hb
    · cases hb
    · cases hb
      exact ⟨[], [], _, rfl, .stmt (.expr (.incDecSuffix rfl (.var rfl) rfl)) .nil⟩

/-- `contract D { uint256 x; function x() external {} }`: a name declared
twice in one scope. -/
def clashing : Syn .unit :=
  .unit (.cons (.contract false "D" .none .nil
    (.cons (.stateVar u256 none none none false "x" .none) (.cons (extFn "x" .nil) .nil))) .nil)

/-- **A clash is ill formed.** -/
theorem clashing_illFormed (s : Settings) : ¬ WellFormed (resolveUnit s clashing) := by
  intro h
  have e := h.noClash ⟨.stateVar, "x", some "D", false, .stateVar u256 none none none false "x" .none⟩
    (by simp only [resolveUnit, show clashing.decls = [_, _, _] from rfl, List.mem_cons, true_or, or_true])
    ⟨.function, "x", some "D", false, extFn "x" .nil⟩
    (by
      rw [show (resolveUnit s clashing).unit.decls =
        [_, _, ⟨.function, "x", some "D", false, extFn "x" .nil⟩] from rfl]
      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))) rfl
  have ek := congrArg Decl.kind e
  cases ek

/-- Both pipelines resolve the counter, recording their coders: the
pragma's (v2 by default) under legacy, v2 under via-IR. -/
theorem counter_pipelines :
    (resolveUnit ⟨.legacy, []⟩ counter).coder = .v2 ∧ (resolveUnit ⟨.viaIR, []⟩ counter).coder = .v2 :=
  ⟨rfl, rfl⟩

/-- `pragma abicoder v1;`: v1 under legacy, v2 under via-IR. -/
theorem abicoderV1 :
    let u : Syn .unit := .unit (.cons (.pragma ["abicoder", "v1"]) .nil)
    (resolveUnit ⟨.legacy, []⟩ u).coder = .v1 ∧ (resolveUnit ⟨.viaIR, []⟩ u).coder = .v2 := ⟨rfl, rfl⟩

end Solidity.Source.TypingExamples

/-- info: 'Solidity.Source.TypingExamples.exprCoverage_typed' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Source.TypingExamples.exprCoverage_typed
/-- info: 'Solidity.Source.TypingExamples.counter_wellFormed' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Source.TypingExamples.counter_wellFormed
/-- info: 'Solidity.Source.TypingExamples.tooBig_illTyped' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Source.TypingExamples.tooBig_illTyped
/-- info: 'Solidity.Source.TypingExamples.clashing_illFormed' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Source.TypingExamples.clashing_illFormed
/-- info: 'Solidity.Source.TypingExamples.diamond_linearize' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Source.TypingExamples.diamond_linearize
/-- info: 'Solidity.Source.implicit_int_range' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.implicit_int_range
/-- info: 'Solidity.Source.FixTy.subsumes_inRange' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.FixTy.subsumes_inRange
/-- info: 'Solidity.Source.Q.toFixedExplicit?_of_toFixed?' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.Q.toFixedExplicit?_of_toFixed?
/-- info: 'Solidity.Source.resolve_iff' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Source.resolve_iff
/-- info: 'Solidity.Source.Resolves.unique' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Source.Resolves.unique
/-- info: 'Solidity.Source.StmtOK.locals_suffix' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Source.StmtOK.locals_suffix
/-- info: 'Solidity.Source.TypingExamples.gasleft_untyped' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Source.TypingExamples.gasleft_untyped
/-- info: 'Solidity.Source.TypingExamples.w_emit' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Source.TypingExamples.w_emit
