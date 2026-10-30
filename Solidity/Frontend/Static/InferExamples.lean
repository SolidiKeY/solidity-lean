import Solidity.Frontend.Static.WellFormedCheck
import Solidity.Source.TypingExamples
import Solidity.Frontend.Static.Consts
import Solidity.Frontend.Static.UserOps
import Solidity.Frontend.Static.Standalone

/-!
# G13 controls: the checkers on S01's own examples

S01's controls (`Solidity/Source/TypingExamples.lean`) are hand-written
derivations and refutations.  Here the checkers compute the same verdicts
in the kernel (`decide`), independently of those proofs:

| Theorem | Statement |
|---|---|
| `counter_checked` | S00's counter is `WellFormed` and in the syntax profile, by `wellFormedB` (no hand derivation) |
| `clashing_checked`, `sameSig_checked`, `ifaceBody_checked`, `twoCtors_checked`, `noVisibility_checked` | S01's five ill-formed units are refused |
| `tooBig_checked`, `fits_checked` | `uint8 x = 300;` has no statement derivation; `uint8 x = 255;` has one |
| `shl18_checked`, `gasleft_checked`, `msgValue_checked` | `1 << 8` has only its folded type; `gasleft()` and `msg.value` in a non-payable public body have none |
| `zero_types`, `addLit_types`, `cond_types` | `0x00` has one type, `hexConst 0 1` (solc's literal typing); `a + 1` and `b ? a : a` have exactly one |
| `member_checked`, `structNew_checked`, `extCall_checked`, `extCallValue_checked`, `pay_checked`, `abiEncode_checked` | the S02 rules: struct members (read and assigned), `P(x)`, external calls with and without `value`, `transfer`/`send`, `abi.encode`, each with a refused neighbour |
| `require_checked` | `require(b, "no");` is a statement |
| `named_value`, `named_length` | `N = 3; M = N * 2 + 1` gives `M = 7`, and `uint256[M]` has length 7 |
| `cyclic_none` | `A = B + 1; B = A + 1` has no value |
| `timestamp_wellFormed`, `timestamp_refused`, `keccak_pure` | `uint256 constant T = block.timestamp;` passes S01's `WellFormed` but is refused as not compile-time (solc 8349); `keccak256("x")` is compile-time |
| `udvt_add`, `udvt_noBinding`, `udvt_wrap`, `udvt_unwrap` | with `using {add as +} for Fixed global`, `a + b` is a `Fixed`; `a - b` has no binding; `Fixed.wrap(1)` is a `Fixed`; `Fixed.unwrap(a)` a `uint256` |
-/

namespace Solidity.Frontend.Static.InferExamples

open Solidity.Source Solidity.Source.TypingExamples Solidity.Frontend.Static Solidity.Language.FixedPoint

/-- **The counter, checked**: well formed and in the syntax profile. -/
theorem counter_checked : WellFormed counterRes ∧ InProfileSyntax counterRes :=
  ⟨wellFormed_iff.mp (by decide), inProfileSyntaxB_iff.mp (by decide)⟩

/-- A refusal of `wellFormedB` refutes `WellFormed`. -/
theorem refuted {r : Resolution} (h : wellFormedB r = false) : ¬ WellFormed r := fun w => by
  rw [wellFormed_iff.mpr w] at h
  cases h

def legacy : Settings := ⟨.legacy, []⟩

theorem clashing_checked : ¬ WellFormed (resolveUnit legacy clashing) := refuted (by decide)
theorem sameSig_checked : ¬ WellFormed (resolveUnit legacy sameSig) := refuted (by decide)
theorem ifaceBody_checked : ¬ WellFormed (resolveUnit legacy ifaceBody) := refuted (by decide)
theorem twoCtors_checked : ¬ WellFormed (resolveUnit legacy twoCtors) := refuted (by decide)
theorem noVisibility_checked : ¬ WellFormed (resolveUnit legacy noVisibility) := refuted (by decide)

/-- **Negative control**: `uint8 x = 300;` has no derivation (in `Γ`). -/
theorem tooBig_checked (L' : List (String × STy)) : ¬ StmtOK Γ Γ.locals tooBig L' := fun h => by
  have hm := stmtOK_iff.mp h
  have e : (stmtLocals Γ tooBig Γ.locals).isEmpty = true := by decide
  rw [List.isEmpty_iff.mp e] at hm
  cases hm

/-- `uint8 x = 255;` -/
def fits : Syn (.stmt .body) :=
  .simpleStmt (.declVar (.varDecl (.elem (.int false 8 (by decide))) none "x")
    (.some (.lit (.num (.dec 255 0 0)))))

theorem fits_checked : (stmtLocals Γ fits Γ.locals).length = 1 := by decide

/-- `1 << 8` has one type, its folded constant. -/
theorem shl18_checked : (inferTys Γ shl18).map (STy.same (.rational ⟨256, 1, by decide⟩)) = [true] := by
  decide

/-- **Negative control**: `gasleft()` has no type. -/
theorem gasleft_checked : (inferTys Γ (.call (.ident "gasleft") (.positional .nil))).isEmpty = true := by
  decide

/-- **Negative control**: `msg.value` in a non-payable public body has no type. -/
theorem msgValue_checked : (inferTys Γv (.member (.ident "msg") "value")).isEmpty = true := by decide

/-- `0x00`: one type, the hexadecimal constant `hexConst 0 1`, which
converts to every `bytesN` (solc's literal typing, Q1). -/
theorem zero_types :
    (inferTys Γ (.lit (.num (.hex [0, 0] false)))).map (STy.same (.hexConst (Q.ofInt 0) 1)) = [true] := by
  decide

theorem addLit_types : (inferTys Γ (.addSub .add a one)).length = 1 := by decide

theorem cond_types : (inferTys Γ (.cond (.ident "b") a a)).length = 1 := by decide

theorem require_checked :
    (stmtLocals (k := .body) Γ (.simpleStmt (.exprStmt (.call (.ident "require")
      (.positional (.cons (.ident "b") (.cons (.lit (.str [110, 111])) .nil)))))) Γ.locals).length = 1 := by
  decide

/-! ## Named constants and compile-time initializers -/

def u256T : Syn .typeName := .elem (.int false 256 (by decide))
def num (n : Nat) : Syn .expr := .lit (.num (.dec n 0 0))

/-- `uint256 constant N = 3; uint256 constant M = N * 2 + 1;` -/
def namedUnit : Syn .unit := .unit
  (.cons (.topPart (.constant u256T "N" (num 3)))
  (.cons (.topPart (.constant u256T "M" (.addSub .add (.mulDivMod .mul (.ident "N") (num 2)) (num 1))))
  .nil))

theorem named_value : (evalConst (Syn.env namedUnit) Option.none (.ident "M")).map (·.2.toInt) = Option.some 7 := by
  decide

/-- The length expression `M` of `uint256[M]`. -/
theorem named_length :
    arrayLenB (Syn.env namedUnit) Option.none (.some (.ident "M")) = Option.some (Option.some 7) := by decide

/-- `uint256 constant A = 7;` -/
def sevenUnit : Syn .unit := .unit (.cons (.topPart (.constant u256T "A" (num 7))) .nil)

/-- solc's typed evaluation: `A / 2` is a `uint256` division, `3`, so
`A / 2 * 2` is `6` (folding over rationals would give `7`). -/
theorem typed_division :
    arrayLenB (Syn.env sevenUnit) Option.none
      (.some (.mulDivMod .mul (.mulDivMod .div (.ident "A") (num 2)) (num 2))) = Option.some (Option.some 6) := by
  decide

/-- `uint8 constant C = 255;` -/
def u8Unit : Syn .unit :=
  .unit (.cons (.topPart (.constant (.elem (.int false 8 (by decide))) "C" (num 255))) .nil)

/-- **Negative control**: `C + 1` is out of `uint8`'s range, so it is no
array length (solc: "Invalid array length"). -/
theorem overflow_length : arrayLenB (Syn.env u8Unit) Option.none (.some (.addSub .add (.ident "C") (num 1))) =
    Option.none := by decide

/-- `uint256 constant A = B + 1; uint256 constant B = A + 1;` -/
def cyclicUnit : Syn .unit := .unit
  (.cons (.topPart (.constant u256T "A" (.addSub .add (.ident "B") (num 1))))
  (.cons (.topPart (.constant u256T "B" (.addSub .add (.ident "A") (num 1))))
  .nil))

/-- **Negative control**: the cyclic definition is refused outright. -/
theorem cyclic_refused : ¬ ConstsAcyclic (Syn.env cyclicUnit) := fun h => by
  have e := acyclic_iff.mpr h
  revert e
  decide

theorem named_acyclic : ConstsAcyclic (Syn.env namedUnit) := acyclic_iff.mp (by decide)

/-- The expressions of the cycle. -/
def cycE (e : Syn .expr) : Prop :=
  e = .addSub .add (.ident "B") (num 1) ∨ e = .addSub .add (.ident "A") (num 1) ∨
    e = .ident "A" ∨ e = .ident "B"

/-- No value in the cycle, by the mutual recursor of `TEval`/`NamedConst`. -/
theorem cyc_nc {s : Option String} {x : String} {t : IntTy} {q : Q}
    (h : NamedConst (Syn.env cyclicUnit) s x t q) : s = Option.none → (x = "A" ∨ x = "B") → False := by
  refine NamedConst.rec (motive_1 := fun s e _ _ => s = Option.none → cycE e → False)
    (motive_2 := fun s x _ _ _ => s = Option.none → (x = "A" ∨ x = "B") → False) ?_ ?_ ?_ ?_ ?_ ?_ h
  · intro s e q hc _ he
    rcases he with he | he | he | he <;> subst he <;> cases hc
  · intro s x t q _ ih hs he
    rcases he with he | he | he | he <;> cases he
    · exact ih hs (.inl rfl)
    · exact ih hs (.inr rfl)
  · intro s e t q _ _ _ he
    rcases he with he | he | he | he <;> cases he
  · intro s x op t q r r' l _ _ _ _ _ _ _ he
    rcases he with he | he | he | he <;> cases he
  · intro s e a b k va vb t la lb r r' hk _ _ _ _ _ _ _ _ iha _ hs he
    rcases he with he | he | he | he <;> subst he <;> cases hk
    · exact iha hs (.inr (.inr (.inr rfl)))
    · exact iha hs (.inr (.inr (.inl rfl)))
  · intro s x d e t v q hl _ he _ _ _ ih hs hx
    subst hs
    rcases hx with hx | hx <;> subst hx
    · have hA : (Syn.env cyclicUnit).lookup Option.none "A" =
          [(Syn.env cyclicUnit).decls[0]'(by decide)] := rfl
      rw [hA] at hl
      cases hl
      have he' : e = .addSub .add (.ident "B") (num 1) := (Option.some.inj he).symm
      subst he'
      exact ih rfl (.inl rfl)
    · have hB : (Syn.env cyclicUnit).lookup Option.none "B" =
          [(Syn.env cyclicUnit).decls[1]'(by decide)] := rfl
      rw [hB] at hl
      cases hl
      have he' : e = .addSub .add (.ident "A") (num 1) := (Option.some.inj he).symm
      subst he'
      exact ih rfl (.inr (.inl rfl))

/-- **Negative control, on the relation**: `A` has no value at all (no
level bound involved). -/
theorem cyclic_noValue (t : IntTy) (q : Q) : ¬ NamedConst (Syn.env cyclicUnit) Option.none "A" t q :=
  fun h => cyc_nc h rfl (.inl rfl)

/-- `uint256 constant T = block.timestamp;` -/
def timestampUnit : Syn .unit := .unit
  (.cons (.topPart (.constant u256T "T" (.member (.ident "block") "timestamp"))) .nil)

/-- S01's well-formedness accepts it. -/
theorem timestamp_wellFormed : WellFormed (resolveUnit legacy timestampUnit) := wellFormed_iff.mp (by decide)

/-- **Negative control**: the initializer is not compile-time (solc error 8349). -/
theorem timestamp_refused : ¬ ConstInitsPure (resolveUnit legacy timestampUnit) := fun h => by
  have e := constInitsB_iff.mpr h
  revert e
  decide

/-- `bytes32 constant H = keccak256("x");` is compile-time. -/
def keccakUnit : Syn .unit := .unit
  (.cons (.topPart (.constant (.elem (.fixedBytes 32 (by decide))) "H"
    (.call (.ident "keccak256") (.positional (.cons (.lit (.str [120])) .nil))))) .nil)

theorem keccak_pure : ConstInitsPure (resolveUnit legacy keccakUnit) ∧ WellFormed (resolveUnit legacy keccakUnit) :=
  ⟨constInitsB_iff.mp (by decide), wellFormed_iff.mp (by decide)⟩

/-! ## User-defined value types -/

def fixedT : Syn .typeName := .userType ⟨"Fixed", []⟩

/-- `type Fixed is uint256; function add(Fixed a, Fixed b) pure returns (Fixed r) {}
using {add as +} for Fixed global;` -/
def udvtUnit : Syn .unit := .unit
  (.cons (.topPart (.udvt (t := true) "Fixed" (.int false 256 (by decide))))
  (.cons (.topPart (.function (t := true) (.ident "add")
      (.cons (.param fixedT Option.none (Option.some "a")) (.cons (.param fixedT Option.none (Option.some "b")) .nil))
      Option.none (Option.some .pure) .nil false Option.none
      (.cons (.param fixedT Option.none (Option.some "r")) .nil) (.some (.block .nil))))
  (.cons (.topPart (.usingPart (.usingAliases (.usingAlias ⟨"add", []⟩ (Option.some .add)) .nil
      (.some fixedT) true)))
  .nil)))

def fixedTy : STy := .udvt ⟨Option.none, "Fixed"⟩

def Γu : Ctx := { env := Syn.env udvtUnit, scope := Option.none, locals := [("a", fixedTy), ("b", fixedTy)] }

theorem udvt_add :
    (udvtTys Γu udvtUnit (.addSub .add (.ident "a") (.ident "b"))).map (STy.same fixedTy) = [true] := by
  decide

/-- **Negative control**: no binding for `-`. -/
theorem udvt_noBinding : (udvtTys Γu udvtUnit (.addSub .sub (.ident "a") (.ident "b"))).isEmpty = true := by
  decide

theorem udvt_wrap :
    (udvtTys Γu udvtUnit (.call (.member (.ident "Fixed") "wrap") (.positional (.cons (num 1) .nil)))).map
      (STy.same fixedTy) = [true] := by decide

theorem udvt_unwrap :
    (udvtTys Γu udvtUnit (.call (.member (.ident "Fixed") "unwrap")
      (.positional (.cons (.ident "a") .nil)))).map (STy.same (.int IntTy.u256)) = [true] := by decide

theorem udvt_bindings_ok : UsingOpsOK (Syn.env udvtUnit) udvtUnit := usingOpsB_iff.mp (by decide)

/-- `udvtUnit` with `add` also bound to `<`, which must return `bool`. -/
def badBindingUnit : Syn .unit := .unit
  (.cons (.topPart (.udvt (t := true) "Fixed" (.int false 256 (by decide))))
  (.cons (.topPart (.function (t := true) (.ident "add")
      (.cons (.param fixedT Option.none (Option.some "a")) (.cons (.param fixedT Option.none (Option.some "b")) .nil))
      Option.none (Option.some .pure) .nil false Option.none
      (.cons (.param fixedT Option.none (Option.some "r")) .nil) (.some (.block .nil))))
  (.cons (.topPart (.usingPart (.usingAliases (.usingAlias ⟨"add", []⟩ (Option.some .add))
      (.cons (.usingAlias ⟨"add", []⟩ (Option.some .lt)) .nil) (.some fixedT) true)))
  .nil)))

/-- **Negative control**: a binding of the wrong signature refuses the unit. -/
theorem badBinding_refused : ¬ UsingOpsOK (Syn.env badBindingUnit) badBindingUnit := fun h => by
  have e := usingOpsB_iff.mpr h
  revert e
  decide

/-! ## Overload uniqueness (formerly an S01 deviation, now aligned with solc) -/

/-- A parameter of type `t`. -/
def paramOf (t : Syn .typeName) : Syn .param := .param t Option.none (Option.some "v")

/-- `function f(p) internal {}` -/
def fnOf (p : Syn .param) : Syn (.part false) :=
  .function (.ident "f") (.cons p .nil) (Option.some .internal) Option.none .nil false Option.none .nil
    (.some (.block .nil))

/-- `contract C { function f(uint8) …; function f(bytes1) …; }` -/
def hexUnit : Syn .unit := .unit (.cons (.contract false "C" .none .nil
  (.cons (fnOf (paramOf (.elem (.int false 8 (by decide)))))
  (.cons (fnOf (paramOf (.elem (.fixedBytes 1 (by decide))))) .nil))) .nil)

def Γh : Ctx := { env := Syn.env hexUnit, scope := Option.some "C", locals := [] }

/-- **Former deviation, now aligned** (the name is kept for the pins; the
call is now refused): `f(0x01)` with `f(uint8)` and
`f(bytes1)` is refused as ambiguous, as solc does.  Under the earlier S01
typing `0x01` had a rational and a `bytes1` typing, each selecting one
overload, so the call had two derivations; with solc's literal typing
(Q1) `0x01` has the one type `hexConst 1 1`, which both overloads accept,
so `callInternal`'s uniqueness premise fails. -/
theorem hexCall_typed :
    (inferTys Γh (.call (.ident "f") (.positional (.cons (.lit (.num (.hex [0, 1] false))) .nil)))).length = 0 := by
  decide

/-! ## Rules added by S02 (members, struct construction, external calls, payments, encoding) -/

/-- `contract K { struct P { uint256 a; } function g(uint256 v) external payable {}
function h(uint256 v) external {} }` -/
def callUnit : Syn .unit := .unit (.cons (.contract false "K" .none .nil
  (.cons (.struct "P" (.structMember u256T "a") .nil)
  (.cons (.function (.ident "g") (.cons (paramOf u256T) .nil) (Option.some .external)
      (Option.some .payable) .nil false Option.none .nil (.some (.block .nil)))
  (.cons (.function (.ident "h") (.cons (paramOf u256T) .nil) (Option.some .external)
      Option.none .nil false Option.none .nil (.some (.block .nil))) .nil)))) .nil)

/-- Locals `P memory p`, `K k`, `address payable q`, `address r`, `uint256 x`. -/
def Γc : Ctx := { env := Syn.env callUnit, scope := Option.some "K", locals :=
  [("p", .struct .memory ⟨Option.some "K", "P"⟩), ("k", .contract ⟨Option.none, "K"⟩),
   ("q", .address true), ("r", .address false), ("x", .int IntTy.u256)] }

def x1 : Syn (.list .expr) := .cons (.ident "x") .nil

/-- `p.a` is a `uint256`, an lvalue, and `p.a = x` is typed; `p.b` has no
type. -/
theorem member_checked :
    (inferTys Γc (.member (.ident "p") "a")).map (STy.same (.int IntTy.u256)) = [true] ∧
    (lvsOf Γc (infer Γc (.member (.ident "p") "a"))).length = 1 ∧
    (inferTys Γc (.assign .assign (.member (.ident "p") "a") (.ident "x"))).map
      (STy.same (.int IntTy.u256)) = [true] ∧
    (inferTys Γc (.member (.ident "p") "b")).isEmpty = true := by decide

/-- `P(x)` is a `P memory`; `P()` (too few members) has no type. -/
theorem structNew_checked :
    (inferTys Γc (.call (.ident "P") (.positional x1))).map
      (STy.same (.struct .memory ⟨Option.some "K", "P"⟩)) = [true] ∧
    (inferTys Γc (.call (.ident "P") (.positional .nil))).isEmpty = true := by decide

/-- `k.g(x)` and `k.h(x)` are external calls; `k.z(x)` has no type. -/
theorem extCall_checked :
    (inferTys Γc (.call (.member (.ident "k") "g") (.positional x1))).map (STy.same (.tuple [])) = [true] ∧
    (inferTys Γc (.call (.member (.ident "k") "h") (.positional x1))).map (STy.same (.tuple [])) = [true] ∧
    (inferTys Γc (.call (.member (.ident "k") "z") (.positional x1))).isEmpty = true := by decide

/-- `k.g{value: x}(x)` is typed (`g` is `payable`); `k.h{value: x}(x)` is
not (`h` is not), as in solc.  `k.g{gas: x}(x)`, which solc accepts, is not
typed: call options other than `value` are a recorded S02 gap. -/
theorem extCallValue_checked :
    (inferTys Γc (.call (.callOptions (.member (.ident "k") "g") (.namedArg "value" (.ident "x")) .nil)
      (.positional x1))).map (STy.same (.tuple [])) = [true] ∧
    (inferTys Γc (.call (.callOptions (.member (.ident "k") "h") (.namedArg "value" (.ident "x")) .nil)
      (.positional x1))).isEmpty = true ∧
    (inferTys Γc (.call (.callOptions (.member (.ident "k") "g") (.namedArg "gas" (.ident "x")) .nil)
      (.positional x1))).isEmpty = true := by decide

/-- `q.transfer(x)` and `q.send(x)` on an `address payable`; neither on a
plain `address`. -/
theorem pay_checked :
    (inferTys Γc (.call (.member (.ident "q") "transfer") (.positional x1))).map (STy.same (.tuple [])) = [true] ∧
    (inferTys Γc (.call (.member (.ident "q") "send") (.positional x1))).map (STy.same .bool) = [true] ∧
    (inferTys Γc (.call (.member (.ident "r") "transfer") (.positional x1))).isEmpty = true ∧
    (inferTys Γc (.call (.member (.ident "r") "send") (.positional x1))).isEmpty = true := by decide

/-- `abi.encode(x)` is `bytes memory`.  `abi.encode(p)` (a struct) is not
typed: S01's `STy.abiArg` admits value types and memory `bytes`/`string`
only, where solc (ABI coder v2) also encodes structs and arrays — a
recorded deviation (`docs/feature-work/source-soundness.md`), not a
refusal solc makes. -/
theorem abiEncode_checked :
    (inferTys Γc (.call (.member (.ident "abi") "encode") (.positional x1))).map (STy.same (.bytes .memory)) = [true] ∧
    (inferTys Γc (.call (.member (.ident "abi") "encode")
      (.positional (.cons (.ident "p") .nil)))).isEmpty = true := by decide

/-! ## Local storage pointers (lane-soundness typing fixes) -/

/-- `contract K { struct P { uint256 a; } P s; }` -/
def ptrUnit : Syn .unit := .unit (.cons (.contract false "K" .none .nil
  (.cons (.struct "P" (.structMember u256T "a") .nil)
  (.cons (.stateVar (.userType ⟨"P", []⟩) none none none false "s" .none) .nil))) .nil)

/-- Locals `P storage p`, `P memory m`, `uint256 x`. -/
def Γp : Ctx := { env := Syn.env ptrUnit, scope := Option.some "K", locals :=
  [("p", .struct .storage ⟨Option.some "K", "P"⟩), ("m", .struct .memory ⟨Option.some "K", "P"⟩),
   ("x", .int IntTy.u256)] }

/-- **Typing fix**: `p = P(x)` with `p` a local storage pointer has no type
(solc 7407: a memory struct is not a storage pointer); `s = P(x)`, a copy
into the state variable, and `p = s`, rebinding the pointer, are typed. -/
theorem ptrCopy_refused :
    (inferTys Γp (.assign .assign (.ident "p") (.call (.ident "P") (.positional x1)))).isEmpty = true ∧
    (inferTys Γp (.assign .assign (.ident "s") (.call (.ident "P") (.positional x1)))).length = 1 ∧
    (inferTys Γp (.assign .assign (.ident "p") (.ident "s"))).length = 1 := by
  decide

/-- **Typing fix**: `delete p` with `p` a local storage pointer has no type
(solc: delete cannot be applied to storage pointers); `delete s` and
`delete m` (a memory local) are typed. -/
theorem ptrDelete_refused :
    (inferTys Γp (.unaryPrefix .delete (.ident "p"))).isEmpty = true ∧
    (inferTys Γp (.unaryPrefix .delete (.ident "s"))).length = 1 ∧
    (inferTys Γp (.unaryPrefix .delete (.ident "m"))).length = 1 := by
  decide

/-! ## Standalone constants (backfill item 5) -/

/-- The fields of a fixed-point type, else `none`. -/
def fixedFields : STy → Option (Bool × Nat × Nat)
  | .fixed f => Option.some (f.signed, f.bits, f.digits)
  | _ => Option.none

/-- `1 / 3` -/
def oneThird : Syn .expr := .mulDivMod .div (num 1) (num 3)

/-- `2**256 + 1/2`: fractional, beyond 256 bits. -/
def tooBigFrac : Syn .expr := .addSub .add (num (2 ^ 256)) (.mulDivMod .div (num 1) (num 2))

/-- **`1 / 3` stands alone at `ufixed256x77`** (solc's mobile type; not
`ufixed256x76` or a signed type, by the exact list) and is an ABI argument
there; S01's own `STy.mobile` leaves it rational. -/
theorem oneThird_standalone :
    (standaloneTys Γ oneThird).map fixedFields = [Option.some (false, 256, 77)] ∧
    (abiArgTys Γ oneThird).length = 1 ∧
    (inferTys Γ oneThird).map (fun τ => τ.mobile.isConstOnly) = [true] := by
  decide +kernel

/-- The integer fields of a type, else `none`. -/
def intFields : STy → Option (Bool × Nat)
  | .int t => Option.some (t.signed, t.bits)
  | _ => Option.none

/-- **Negative controls**: a fractional constant without a mobile type has
no standalone fixed-point type and is no ABI argument; `2**256` (integral,
beyond 256 bits) is no ABI argument either; `5` stands alone at `uint8`. -/
theorem tooBigFrac_refused :
    (standaloneTys Γ tooBigFrac).map fixedFields = [Option.none] ∧
    (abiArgTys Γ tooBigFrac).isEmpty = true ∧ (abiArgTys Γ (num (2 ^ 256))).isEmpty = true ∧
    (standaloneTys Γ (num 5)).map intFields = [Option.some (false, 8)] ∧
    (abiArgTys Γ (num 5)).length = 1 := by
  decide +kernel

/-- Unreduced constants: `4 / 2` stands alone at `uint8` (S01's rational
`4/2` is integral), `2 / 6` at `ufixed256x77`, as `1 / 3`. -/
theorem unreduced_standalone :
    (standaloneTys Γ (.mulDivMod .div (num 4) (num 2))).map intFields = [Option.some (false, 8)] ∧
    (standaloneTys Γ (.mulDivMod .div (num 2) (num 6))).map fixedFields = [Option.some (false, 256, 77)] := by
  decide +kernel

/-- The value of `1 / 3` standing alone: 77 threes, truncated (`3 · v ≠
10^77`). -/
theorem oneThird_value :
    (Fx.mobileConst? (Q.toRat ⟨1, 3, by decide⟩)).map (fun x => x.2.1) = Option.some ((10 ^ 77 - 1) / 3) ∧
    (Fx.mobileConst? (Q.toRat ⟨1, 3, by decide⟩)).map (fun x => 3 * x.2.1) ≠ Option.some (10 ^ 77) := by
  decide +kernel

end Solidity.Frontend.Static.InferExamples
/-- info: 'Solidity.Frontend.Static.typed_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.Static.typed_complete
/-- info: 'Solidity.Frontend.Static.lval_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.Static.lval_complete
/-- info: 'Solidity.Frontend.Static.args_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.Static.args_complete
/-- info: 'Solidity.Frontend.Static.slots_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.Static.slots_complete
/-- info: 'Solidity.Frontend.Static.stmt_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.Static.stmt_complete
/-- info: 'Solidity.Frontend.Static.items_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.Static.items_complete
/-- info: 'Solidity.Frontend.Static.stmtOK_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.Static.stmtOK_iff
/-- info: 'Solidity.Frontend.Static.itemsOK_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.Static.itemsOK_iff
/-- info: 'Solidity.Frontend.Static.wellFormed_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.Static.wellFormed_iff
/-- info: 'Solidity.Frontend.Static.inProfileSyntaxB_iff' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.Static.inProfileSyntaxB_iff
/-- info: 'Solidity.Frontend.Static.pureB_iff' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Frontend.Static.pureB_iff
/-- info: 'Solidity.Frontend.Static.constInitsB_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.Static.constInitsB_iff
/-- info: 'Solidity.Frontend.Static.evalConst_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.Static.evalConst_sound
/-- info: 'Solidity.Frontend.Static.evalConst_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.Static.evalConst_complete
/-- info: 'Solidity.Frontend.Static.arrayLenB_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.Static.arrayLenB_sound
/-- info: 'Solidity.Frontend.Static.udvt_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.Static.udvt_iff
/-- info: 'Solidity.Frontend.Static.InferExamples.counter_checked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.Static.InferExamples.counter_checked
/-- info: 'Solidity.Frontend.Static.InferExamples.clashing_checked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.Static.InferExamples.clashing_checked
/-- info: 'Solidity.Frontend.Static.InferExamples.tooBig_checked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.Static.InferExamples.tooBig_checked
/-- info: 'Solidity.Frontend.Static.InferExamples.gasleft_checked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.Static.InferExamples.gasleft_checked
/-- info: 'Solidity.Frontend.Static.InferExamples.timestamp_refused' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.Static.InferExamples.timestamp_refused
/-- info: 'Solidity.Frontend.Static.InferExamples.udvt_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.Static.InferExamples.udvt_add
/-- info: 'Solidity.Frontend.Static.InferExamples.udvt_noBinding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.Static.InferExamples.udvt_noBinding
/-- info: 'Solidity.Frontend.Static.InferExamples.named_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.Static.InferExamples.named_length
/-- info: 'Solidity.Frontend.Static.teval_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.Static.teval_complete
/-- info: 'Solidity.Frontend.Static.nconst_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.Static.nconst_complete
/-- info: 'Solidity.Frontend.Static.acyclic_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.Static.acyclic_iff
/-- info: 'Solidity.Frontend.Static.usingOpsB_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.Static.usingOpsB_iff
/-- info: 'Solidity.Frontend.Static.hasType_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.Static.hasType_iff
/-- info: 'Solidity.Frontend.Static.InferExamples.cyclic_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.Static.InferExamples.cyclic_refused
/-- info: 'Solidity.Frontend.Static.InferExamples.cyclic_noValue' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.Static.InferExamples.cyclic_noValue
/-- info: 'Solidity.Frontend.Static.InferExamples.typed_division' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.Static.InferExamples.typed_division
/-- info: 'Solidity.Frontend.Static.InferExamples.overflow_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.Static.InferExamples.overflow_length
/-- info: 'Solidity.Frontend.Static.InferExamples.badBinding_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.Static.InferExamples.badBinding_refused
/-- info: 'Solidity.Frontend.Static.InferExamples.hexCall_typed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.Static.InferExamples.hexCall_typed
/-- info: 'Solidity.Frontend.Static.standalone_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.Static.standalone_iff
/-- info: 'Solidity.Frontend.Static.abiArg_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.Static.abiArg_iff
/-- info: 'Solidity.Frontend.Static.standalone_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.Static.standalone_value
/-- info: 'Solidity.Frontend.Static.InferExamples.oneThird_standalone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.Static.InferExamples.oneThird_standalone
/-- info: 'Solidity.Frontend.Static.InferExamples.tooBigFrac_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.Static.InferExamples.tooBigFrac_refused
/-- info: 'Solidity.Frontend.Static.InferExamples.oneThird_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.Static.InferExamples.oneThird_value
/-- info: 'Solidity.Frontend.Static.InferExamples.unreduced_standalone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.Static.InferExamples.unreduced_standalone
/-- info: 'Solidity.Frontend.Static.standalone_toFixedExplicit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.Static.standalone_toFixedExplicit
/-- info: 'Solidity.Frontend.Static.standalone_abi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.Static.standalone_abi
/-- info: 'Solidity.Frontend.Static.InferExamples.member_checked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.Static.InferExamples.member_checked
/-- info: 'Solidity.Frontend.Static.InferExamples.structNew_checked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.Static.InferExamples.structNew_checked
/-- info: 'Solidity.Frontend.Static.InferExamples.extCall_checked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.Static.InferExamples.extCall_checked
/-- info: 'Solidity.Frontend.Static.InferExamples.extCallValue_checked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.Static.InferExamples.extCallValue_checked
/-- info: 'Solidity.Frontend.Static.InferExamples.pay_checked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.Static.InferExamples.pay_checked
/-- info: 'Solidity.Frontend.Static.InferExamples.abiEncode_checked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Frontend.Static.InferExamples.abiEncode_checked
