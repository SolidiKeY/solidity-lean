import Solidity.Source.WellFormed
import Solidity.Source.Resolved
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
def Γ : Ctx :=
  { env := unitC.env, scope := some "C", locals := [("o", .address false), ("b", .bool), ("a", .int IntTy.u256)],
    rets := [.int IntTy.u256] }

def a : Syn .expr := .ident "a"
def one : Syn .expr := .lit (.num (.dec 1 0 0))

/-! Derivations are data (`Typed`): each is the elaborated term. -/

def ty_a : Typed Γ a (.int IntTy.u256) := .loc rfl rfl
def ty_b : Typed Γ (.ident "b") .bool := .loc rfl rfl
def ty_o : Typed Γ (.ident "o") (.address false) := .loc rfl rfl
def ty_count : Typed Γ (.ident "count") (.int IntTy.u256) := .state rfl rfl
def ty_flag : Typed Γ (.ident "flag") .bool := .state rfl rfl
def ty_arr : Typed Γ (.ident "arr") (.array .storage (.int IntTy.u256) none) := .state rfl rfl
def ty_m : Typed Γ (.ident "m") (.mapping (.address false) (.int IntTy.u256)) := .state rfl rfl
def ty_one : Typed Γ one (.rational (Q.ofInt 1)) := .const rfl rfl

/-! ## One derivation per typed expression constructor -/

def w_ident : Typed Γ (.ident "a") (.int IntTy.u256) := ty_a
def w_lit : Typed Γ (.lit (.bool true)) .bool := .bool true
def w_litUnit : Typed Γ (.litUnit (.dec 1 0 0) .ether)
    (.rational ((NumLit.dec 1 0 0).value.mul (Q.ofInt (Denom.factor .ether)))) :=
  .const rfl rfl
def w_tuple : Typed Γ (.tuple (.some a) (.cons (.some (.ident "b")) .nil))
    (.tuple [.int IntTy.u256, .bool]) :=
  .tuple ty_a (.cons ty_b .nil) (by simp only [ne_eq, reduceCtorEq, not_false_eq_true])
def w_index : Typed Γ (.index (.ident "arr") (.some one)) (.int IntTy.u256) :=
  .indexArray ty_arr ty_one rfl rfl
def w_index_mapping : Typed Γ (.index (.ident "m") (.some (.ident "o"))) (.int IntTy.u256) :=
  .indexMapping ty_m ty_o rfl
def w_member : Typed Γ (.member (.ident "arr") "length") (.int IntTy.u256) := .length ty_arr rfl
def w_call : Typed Γ (.call (.elemType (.int false 8 (by decide)) (by decide))
    (.positional (.cons a .nil))) (.int IntTy.u8) := .convElem ty_a rfl rfl
def w_payableConv : Typed Γ (.payableConv (.positional (.cons (.ident "o") .nil))) (.address true) :=
  .payable ty_o rfl
def w_unaryPrefix : Typed Γ (.unaryPrefix .not (.ident "flag")) .bool := .not ty_flag
def w_unarySuffix : Typed Γ (.unarySuffix .inc (.ident "count")) (.int IntTy.u256) :=
  .incDecSuffix (.state rfl rfl rfl) rfl
def w_exp : Typed Γ (.exp a one) (.int IntTy.u256) := .exp rfl ty_a ty_one rfl rfl
def w_mulDivMod : Typed Γ (.mulDivMod .mul a one) (.int IntTy.u256) :=
  .arith rfl ty_a ty_one rfl rfl
def w_addSub : Typed Γ (.addSub .add a a) (.int IntTy.u256) := .arith rfl ty_a ty_a rfl rfl
def w_shift : Typed Γ (.shift .shl a one) (.int IntTy.u256) := .shift rfl ty_a ty_one rfl rfl
def w_bitAnd : Typed Γ (.bitAnd a a) (.int IntTy.u256) := .bit rfl ty_a ty_a rfl rfl
def w_bitXor : Typed Γ (.bitXor a a) (.int IntTy.u256) := .bit rfl ty_a ty_a rfl rfl
def w_bitOr : Typed Γ (.bitOr a a) (.int IntTy.u256) := .bit rfl ty_a ty_a rfl rfl
def w_order : Typed Γ (.order .lt a one) .bool := .order rfl ty_a ty_one rfl rfl
def w_equality : Typed Γ (.equality .eq a a) .bool := .eq rfl ty_a ty_a rfl rfl
def w_and : Typed Γ (.and (.ident "b") (.ident "flag")) .bool := .logic rfl ty_b ty_flag
def w_or : Typed Γ (.or (.ident "b") (.ident "flag")) .bool := .logic rfl ty_b ty_flag
def w_cond : Typed Γ (.cond (.ident "b") a a) (.int IntTy.u256) := .cond ty_b ty_a ty_a rfl
def w_assign : Typed Γ (.assign .assign (.ident "count") a) (.int IntTy.u256) :=
  .assign (.state rfl rfl rfl) ty_a rfl

/-- The elaborated form of `count = a`: an assignment to a state variable. -/
def r_assign : RExpr Γ.isBase Γ.tys (.int IntTy.u256) := w_assign.toR

/-! ## Builtins, events and errors -/

def w_msgSender : Typed Γ (.member (.ident "msg") "sender") (.address false) := .magic rfl rfl rfl rfl

/-- `require(b, "no");` -/
def w_require : StmtD (k := .body) Γ Γ.locals (.simpleStmt (.exprStmt (.call (.ident "require")
    (.positional (.cons (.ident "b") (.cons (.lit (.str [110, 111])) .nil)))))) Γ.locals :=
  .expr (.builtinCall rfl rfl (.cons ty_b (.cons (.str _) .nil)) rfl)

/-- `gasleft()` has no typing rule: an excluded builtin. -/
theorem gasleft_untyped (τ : STy) (h : HasType Γ (.call (.ident "gasleft") (.positional .nil)) τ) : False := by
  obtain ⟨h⟩ := h
  cases h with
  | builtinCall hr hs _ _ =>
    have e : Γ.resolve "gasleft" = some (.builtin .gasleft) := rfl
    rw [e] at hr
    cases hr
    cases hs
  | callInternal _ hd _ => cases hd
  | const hq => nomatch hq
  | arith hb => nomatch hb
  | bit hb => nomatch hb
  | shift hb => nomatch hb
  | exp hb => nomatch hb
  | order hb => nomatch hb
  | eq hb => nomatch hb
  | compareConst hb => nomatch hb
  | logic hb => nomatch hb

/-- A non-payable external function's body: `msg.value` is refused. -/
def Γv : Ctx := { Γ with msgValue := false }

/-- **`msg.value` outside a payable function is ill typed** (solc error
5887). -/
theorem msgValue_refused (τ : STy) (h : HasType Γv (.member (.ident "msg") "value") τ) : False := by
  obtain ⟨h⟩ := h
  generalize hm : "value" = m at h
  cases h with
  | length _ _ => exact absurd hm (by decide)
  | lengthBytesN _ => exact absurd hm (by decide)
  | balance _ => exact absurd hm (by decide)
  | magic hr _ _ hv =>
    have e : Γv.resolve "msg" = some (.builtin .msg) := rfl
    rw [e] at hr
    cases hr
    subst hm
    revert hv
    decide
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
def CE : Ctx := { env := unitE.env, scope := some "E", locals := [] }
def LE : List (String × STy) := [("a", .int IntTy.u256)]

/-- `emit Done(a);` -/
def w_emit : StmtD (k := .body) CE LE (.emit (.ident "Done") (.positional (.cons (.ident "a") .nil))) LE :=
  .emit (.cons (.loc rfl rfl) .nil) rfl

/-- `revert Bad();` -/
def w_revertError : StmtD (k := .body) CE LE (.revert (.ident "Bad") (.positional .nil)) LE :=
  .revertError .nil rfl

/-- The elaborated `emit`: the event's declaration and the argument. -/
def r_emit : RStmt CE.isBase (tysOf LE) (tysOf LE) := w_emit.toR

/-! ## Coverage -/

/-- How S01 covers a constructor. -/
inductive Coverage where
  | typed
  /-- Deferred to a stage, with the reason. -/
  | deferred (stage reason : String)
  deriving DecidableEq, Repr

/-- **The coverage of every expression constructor**, explicitly; `none`
for constructors of other categories (`exprCoverage_total`). -/
def exprCoverage : Ctor → Option Coverage
  | .index | .member | .call | .payableConv | .unaryPrefix | .unarySuffix | .exp | .mulDivMod
  | .addSub | .shift | .bitAnd | .bitXor | .bitOr | .order | .equality | .and | .or | .cond
  | .assign | .tuple | .ident | .lit | .litUnit => some .typed
  | .slice => some (.deferred "S02" "calldata slices are typed with the calldata references of S02")
  | .callOptions => some (.deferred "S02" "call options belong to external calls and creation (S02/S03)")
  | .metaType => some (.deferred "S04.02" "type(T) members read the artifact table and ABI identities")
  | .new => some (.deferred "S03" "creation and memory allocation are typed with their semantics")
  | .inlineArray => some (.deferred "S02" "inline arrays take the mobile type of their elements (S02)")
  | .elemType => some (.deferred "S02" "a type name as a value (abi.decode, type(T)) is S02's; S01 types it only as a conversion callee (convElem)")
  | _ => none

/-- **Every expression constructor is classified.** -/
theorem exprCoverage_total (e : Syn .expr) : (exprCoverage e.ctor).isSome = true := by
  cases e <;> rfl

/-- **Coverage**: every constructor classified as typed has a derivation
whose root is that constructor. -/
theorem exprCoverage_typed (k : Ctor) (ht : exprCoverage k = some .typed) :
    ∃ (e : Syn .expr) (τ : STy), e.ctor = k ∧ HasType Γ e τ := by
  cases k <;> simp only [exprCoverage, reduceCtorEq, Option.some.injEq] at ht <;>
    first
    | exact ⟨_, _, rfl, ⟨w_index⟩⟩
    | exact ⟨_, _, rfl, ⟨w_member⟩⟩
    | exact ⟨_, _, rfl, ⟨w_call⟩⟩
    | exact ⟨_, _, rfl, ⟨w_payableConv⟩⟩
    | exact ⟨_, _, rfl, ⟨w_unaryPrefix⟩⟩
    | exact ⟨_, _, rfl, ⟨w_unarySuffix⟩⟩
    | exact ⟨_, _, rfl, ⟨w_exp⟩⟩
    | exact ⟨_, _, rfl, ⟨w_mulDivMod⟩⟩
    | exact ⟨_, _, rfl, ⟨w_addSub⟩⟩
    | exact ⟨_, _, rfl, ⟨w_shift⟩⟩
    | exact ⟨_, _, rfl, ⟨w_bitAnd⟩⟩
    | exact ⟨_, _, rfl, ⟨w_bitXor⟩⟩
    | exact ⟨_, _, rfl, ⟨w_bitOr⟩⟩
    | exact ⟨_, _, rfl, ⟨w_order⟩⟩
    | exact ⟨_, _, rfl, ⟨w_equality⟩⟩
    | exact ⟨_, _, rfl, ⟨w_and⟩⟩
    | exact ⟨_, _, rfl, ⟨w_or⟩⟩
    | exact ⟨_, _, rfl, ⟨w_cond⟩⟩
    | exact ⟨_, _, rfl, ⟨w_assign⟩⟩
    | exact ⟨_, _, rfl, ⟨w_tuple⟩⟩
    | exact ⟨_, _, rfl, ⟨w_ident⟩⟩
    | exact ⟨_, _, rfl, ⟨w_lit⟩⟩
    | exact ⟨_, _, rfl, ⟨w_litUnit⟩⟩

/-- **The coverage of every statement constructor**, explicitly. -/
def stmtCoverage : Ctor → Option Coverage
  | .blockStmt | .simpleStmt | .declVar | .exprStmt | .ifStmt | .forStmt | .whileStmt | .doWhile
  | .continueStmt | .breakStmt | .returnStmt | .emit | .revert => some .typed
  | .declTuple => some (.deferred "S02" "tuple declarations destructure tuple values, typed with S02's calls")
  | .tryStmt => some (.deferred "S03" "try/catch is an external call's")
  | .assembly => some (.deferred "S00" "inline assembly is excluded; only the canonical rethrow is typed (rethrow)")
  | _ => none

/-- **Every statement constructor is classified.** -/
theorem stmtCoverage_total {k : SCtx} (s : Syn (.stmt k)) : (stmtCoverage s.ctor).isSome = true := by
  cases s <;> rfl

/-- **Every simple-statement constructor is classified.** -/
theorem simpleCoverage_total (s : Syn .simple) : (stmtCoverage s.ctor).isSome = true := by
  cases s <;> rfl

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
    (Γ.push "count" .bool).resolve "count" = some (.loc 0) := rfl

/-! ## Typing controls -/

/-- A number literal has its exact rational type, a `bytesN` type or the
`address` type. -/
theorem Typed.lit_num {Γ : Ctx} {n : NumLit} {σ : STy} (h : Typed Γ (.lit (.num n)) σ) : σ = .rational n.value ∨ (∃ len h, σ = .fixedBytes len h) ∨
      σ = .address false := by
  cases h with
  | const hq =>
    have hv : (Syn.lit (.num n) : Syn .expr).const = some n.value := rfl
    rw [hv] at hq
    cases hq
    exact Or.inl rfl
  | litBytes _ => exact Or.inr (Or.inl ⟨_, _, rfl⟩)
  | litAddress _ => exact Or.inr (Or.inr rfl)
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
typed in every body. -/
theorem tooBig_illTyped (C : Ctx) (L L' : List (String × STy)) : ¬ StmtOK C L tooBig L' := by
  intro ⟨h⟩
  cases h with
  | declInit ht _ he hc =>
    simp only [Syn.ty, Syn.tys, Elem.ty] at ht
    cases ht
    rcases Typed.lit_num he with rfl | ⟨_, _, rfl⟩ | rfl <;>
      simp only [STy.implicit] at hc <;> revert hc <;> decide

/-- `uint8 x = 255;` is well typed. -/
def fits_wellTyped : StmtD (k := .body) Γ Γ.locals (.simpleStmt (.declVar (.varDecl (.elem (.int false 8 (by decide)))
    none "x") (.some (.lit (.num (.dec 255 0 0)))))) (("x", .int IntTy.u8) :: Γ.locals) :=
  .declInit rfl rfl (.const rfl rfl) rfl

/-- `break;` outside a loop has no statement context to live in: a
`breakStmt` is a statement only of a loop body (`Syn (.stmt ⟨true, u⟩)`), so
`StmtD` needs no rule refusing it. -/
example : (Syn.breakStmt (u := false) : Syn (.stmt ⟨true, false⟩)).ctor = .breakStmt := rfl

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

/-- The body of `inc`, typed: `count++;` on the state variable. -/
def incBody : ItemsD (k := .body)
    ({ env := counter.env, scope := some "Counter", locals := [], rets := [], msgValue := false } : Ctx)
    [] (.cons incStmt .nil) [] :=
  .stmt (.expr (.incDecSuffix (.state rfl rfl rfl) rfl)) .nil

/-- **The counter is well formed** (and inside the profile's syntax). -/
theorem counter_wellFormed : WellFormed counterRes ∧ InProfileSyntax counterRes := by
  have hd : counterRes.unit.decls = _ := counter_decls_eq
  refine ⟨⟨rfl, ?_, ?_, ?_, by decide, ?_, ?_, ?_, ?_, ?_⟩, rfl⟩
  · rw [hd]; decide
  · rw [hd]; decide
  · intro ws hw; nomatch hw
  · rw [hd]; decide
  · rw [hd]; decide
  · rw [hd]; decide
  · intro d hm e he
    rw [hd] at hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl <;> cases he
  · intro d hm hb
    rw [hd] at hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl
    · cases hb
    · cases hb
    · exact ⟨_, _, rfl, List.Pairwise.nil, ⟨incBody⟩⟩

/-- `contract D { uint256 x; function x() external {} }`: a name declared
twice in one scope. -/
def clashing : Syn .unit :=
  .unit (.cons (.contract false "D" .none .nil
    (.cons (.stateVar u256 none none none false "x" .none) (.cons (extFn "x" .nil) .nil))) .nil)

/-- **A clash is ill formed.** -/
theorem clashing_illFormed (s : Settings) : ¬ WellFormed (resolveUnit s clashing) := by
  intro h
  have e : clashing.decls.Pairwise fun d d' => d.clash clashing.env d' = false := h.noClash
  revert e
  decide

/-- `contract O { function f(uint256 a) external {} function f(uint256 b) external {} }`:
two functions with one signature. -/
def sameSig : Syn .unit :=
  .unit (.cons (.contract false "O" .none .nil
    (.cons (.function (.ident "f") (.cons (.param u256 none (some "a")) .nil) (some .external) none .nil
        false none .nil (.some (.block .nil)))
      (.cons (.function (.ident "f") (.cons (.param u256 none (some "b")) .nil) (some .external) none .nil
        false none .nil (.some (.block .nil))) .nil))) .nil)

/-- **Overloads need distinct parameter types.** -/
theorem sameSig_illFormed (s : Settings) : ¬ WellFormed (resolveUnit s sameSig) := by
  intro h
  have e : sameSig.decls.Pairwise fun d d' => d.clash sameSig.env d' = false := h.noClash
  revert e
  decide

/-- `interface I { function f() external {} }`: an interface function with
a body. -/
def ifaceBody : Syn .unit :=
  .unit (.cons (.interface "I" .nil (.cons (extFn "f" .nil) .nil)) .nil)

/-- **An interface function has no body.** -/
theorem ifaceBody_illFormed (s : Settings) : ¬ WellFormed (resolveUnit s ifaceBody) := by
  intro h
  have e : ∀ d ∈ ifaceBody.decls, d.placementOK ifaceBody.env = true := h.placement
  revert e
  decide

/-- `pragma solidity ^0.8.0; pragma foo;`: an unknown pragma. -/
theorem unknownPragma_illFormed (s : Settings) :
    ¬ WellFormed (resolveUnit s (.unit (.cons (.pragma ["solidity", "^0.8.0"]) (.cons (.pragma ["foo"]) .nil)))) := by
  intro h
  exact absurd (h.pragmas ["foo"] (List.mem_cons_of_mem _ (List.mem_singleton.2 rfl))) (by decide)

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

/-- info: 'Solidity.Source.TypingExamples.exprCoverage_typed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.TypingExamples.exprCoverage_typed
/-- info: 'Solidity.Source.TypingExamples.counter_wellFormed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.TypingExamples.counter_wellFormed
/-- info: 'Solidity.Source.TypingExamples.tooBig_illTyped' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.TypingExamples.tooBig_illTyped
/-- info: 'Solidity.Source.TypingExamples.clashing_illFormed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
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
/-- info: 'Solidity.Source.StmtD.locals_suffix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.StmtD.locals_suffix
/-- info: 'Solidity.Source.TypingExamples.gasleft_untyped' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.TypingExamples.gasleft_untyped
/-- info: 'Solidity.Source.TypingExamples.msgValue_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.TypingExamples.msgValue_refused
/-- info: 'Solidity.Source.TypingExamples.sameSig_illFormed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.TypingExamples.sameSig_illFormed
/-- info: 'Solidity.Source.TypingExamples.ifaceBody_illFormed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.TypingExamples.ifaceBody_illFormed
/-- info: 'Solidity.Source.TypingExamples.exprCoverage_total' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Source.TypingExamples.exprCoverage_total
/-- info: 'Solidity.Source.StmtOK.resolved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.StmtOK.resolved
