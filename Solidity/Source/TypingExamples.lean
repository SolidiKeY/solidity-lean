import Solidity.Source.WellFormed
import Solidity.Source.Resolved
import Solidity.Source.Examples


namespace Solidity.Source.TypingExamples

open Solidity.Source Solidity.Source.Examples

def tBool : Syn .typeName := .elem .bool

def unitC : Syn .unit :=
  .unit (.cons (.contract false "C" .none .nil
    (.cons (.stateVar u256 none none none false "count" .none)
    (.cons (.stateVar tBool none none none false "flag" .none)
    (.cons (.stateVar (.array u256 .none) none none none false "arr" .none)
    (.cons (.stateVar (.mapping (.elem .address (by decide)) none u256 none) none none none false "m" .none)
    (.cons (.stateVar (.elem (.int false 8 (by decide))) none none none false "small" .none)
      .nil)))))) .nil)

def Γ : Ctx :=
  { env := unitC.env, scope := some "C",
    locals := [("o", .address false), ("b", .bool), ("a", .int IntTy.u256), ("cd", .bytes .calldata)],
    rets := [.int IntTy.u256] }

def a : Syn .expr := .ident "a"
def one : Syn .expr := .lit (.num (.dec 1 0 0))


def ty_a : Typed Γ a (.int IntTy.u256) := .loc rfl rfl
def ty_b : Typed Γ (.ident "b") .bool := .loc rfl rfl
def ty_o : Typed Γ (.ident "o") (.address false) := .loc rfl rfl
def ty_count : Typed Γ (.ident "count") (.int IntTy.u256) := .state rfl rfl
def ty_flag : Typed Γ (.ident "flag") .bool := .state rfl rfl
def ty_arr : Typed Γ (.ident "arr") (.array .storage (.int IntTy.u256) none) := .state rfl rfl
def ty_m : Typed Γ (.ident "m") (.mapping (.address false) (.int IntTy.u256)) := .state rfl rfl
def ty_one : Typed Γ one (.rational (Q.ofInt 1)) := .const rfl rfl rfl


def w_ident : Typed Γ (.ident "a") (.int IntTy.u256) := ty_a
def w_lit : Typed Γ (.lit (.bool true)) .bool := .bool true
def w_litUnit : Typed Γ (.litUnit (.dec 1 0 0) .ether)
    (.rational ((NumLit.dec 1 0 0).value.mul (Q.ofInt (Denom.factor .ether)))) :=
  .const rfl rfl rfl
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
def w_abiDecode : Typed Γ (.call (.member (.ident "abi") "decode") (.positional (.cons (.lit (.hexStr [0, 1]))
    (.cons (.tuple (.some (.elemType (.int false 8 (by decide)) (by decide)))
      (.cons (.some (.elemType .bool (by decide))) .nil)) .nil))))
    (.tuple [.int IntTy.u8, .bool]) :=
  .abiDecode (τs := [.int IntTy.u8, .bool]) rfl (.hexStr _) rfl rfl rfl
def w_slice : Typed Γ (.slice (.ident "cd") (.some one) .none) (.bytes .calldata) :=
  .sliceFrom (.loc rfl rfl) rfl ty_one rfl
def w_inlineArray : Typed Γ (.inlineArray a (.cons one .nil)) (.array .memory (.int IntTy.u256) (some 2)) :=
  .inlineArray ty_a (.cons ty_one .nil) rfl rfl rfl
def w_payableConv : Typed Γ (.payableConv (.positional (.cons (.ident "o") .nil))) (.address true) :=
  .payable ty_o rfl
def w_unaryPrefix : Typed Γ (.unaryPrefix .not (.ident "flag")) .bool := .not ty_flag
def w_unarySuffix : Typed Γ (.unarySuffix .inc (.ident "count")) (.int IntTy.u256) :=
  .incDecSuffix (.state rfl rfl rfl) rfl
def w_exp : Typed Γ (.exp a one) (.int IntTy.u256) := .exp rfl ty_a ty_one rfl rfl rfl
def w_mulDivMod : Typed Γ (.mulDivMod .mul a one) (.int IntTy.u256) :=
  .arith rfl ty_a ty_one rfl rfl rfl
def w_addSub : Typed Γ (.addSub .add a a) (.int IntTy.u256) := .arith rfl ty_a ty_a rfl rfl rfl
def w_shift : Typed Γ (.shift .shl a one) (.int IntTy.u256) := .shift rfl ty_a ty_one rfl rfl rfl
def w_bitAnd : Typed Γ (.bitAnd a a) (.int IntTy.u256) := .bit rfl ty_a ty_a rfl rfl
def w_bitXor : Typed Γ (.bitXor a a) (.int IntTy.u256) := .bit rfl ty_a ty_a rfl rfl
def w_bitOr : Typed Γ (.bitOr a a) (.int IntTy.u256) := .bit rfl ty_a ty_a rfl rfl
def w_order : Typed Γ (.order .lt a one) .bool := .order rfl ty_a ty_one rfl rfl
def w_equality : Typed Γ (.equality .eq a a) .bool := .eq rfl ty_a ty_a rfl rfl
def w_and : Typed Γ (.and (.ident "b") (.ident "flag")) .bool := .logic rfl ty_b ty_flag
def w_or : Typed Γ (.or (.ident "b") (.ident "flag")) .bool := .logic rfl ty_b ty_flag
def w_cond : Typed Γ (.cond (.ident "b") a a) (.int IntTy.u256) := .cond ty_b ty_a ty_a rfl
def w_assign : Typed Γ (.assign .assign (.ident "count") a) (.int IntTy.u256) :=
  .assign (.state rfl rfl rfl) ty_a rfl rfl

def r_assign : RExpr Γ.env Γ.tys (.int IntTy.u256) := w_assign.toR


def w_msgSender : Typed Γ (.member (.ident "msg") "sender") (.address false) := .magic rfl rfl rfl rfl

def w_require : StmtD (k := .body) Γ Γ.locals (.simpleStmt (.exprStmt (.call (.ident "require")
    (.positional (.cons (.ident "b") (.cons (.lit (.str [110, 111])) .nil)))))) Γ.locals :=
  .expr (.builtinCall rfl rfl (.cons ty_b (.cons (.str _) .nil)) rfl) rfl

theorem gasleft_untyped (τ : STy) (h : HasType Γ (.call (.ident "gasleft") (.positional .nil)) τ) : False := by
  obtain ⟨h⟩ := h
  cases h with
  | builtinCall hr hs _ _ =>
    have e : Γ.resolve "gasleft" = some (.builtin .gasleft) := rfl
    rw [e] at hr
    cases hr
    cases hs
  | callInternal _ hd _ => cases hd
  | structNew hs =>
    have e : Γ.structOf "gasleft" = none := rfl
    rw [e] at hs
    cases hs
  | const hq => nomatch hq
  | arith hb => nomatch hb
  | bit hb => nomatch hb
  | shift hb => nomatch hb
  | exp hb => nomatch hb
  | order hb => nomatch hb
  | eq hb => nomatch hb
  | compareConst hb => nomatch hb
  | logic hb => nomatch hb

theorem Typed.ident_builtin_not_struct {Γ : Ctx} {x : String} {b : Builtin} {l : DataLoc} {dn : DeclName}
    (hr : Γ.resolve x = some (.builtin b)) (d : Typed Γ (.ident x) (.struct l dn)) : False := by
  generalize ht : STy.struct l dn = τ at d
  cases d with
  | loc h _ => rw [hr] at h; cases h
  | state h _ => rw [hr] at h; cases h
  | this => cases ht
  | const hq => nomatch hq
  | arith hb => nomatch hb
  | bit hb => nomatch hb
  | shift hb => nomatch hb
  | exp hb => nomatch hb
  | order hb => nomatch hb
  | eq hb => nomatch hb
  | compareConst hb => nomatch hb
  | logic hb => nomatch hb

def Γv : Ctx := { Γ with msgValue := false }

theorem msgValue_refused (τ : STy) (h : HasType Γv (.member (.ident "msg") "value") τ) : False := by
  obtain ⟨h⟩ := h
  generalize hm : "value" = m at h
  cases h with
  | length _ _ => exact absurd hm (by decide)
  | balance _ => exact absurd hm (by decide)
  | magic hr _ _ hv =>
    have e : Γv.resolve "msg" = some (.builtin .msg) := rfl
    rw [e] at hr
    cases hr
    subst hm
    revert hv
    decide
  | member ha _ =>
    have e : Γv.resolve "msg" = some (.builtin .msg) := rfl
    exact Typed.ident_builtin_not_struct e ha
  | const hq => nomatch hq
  | arith hb => nomatch hb
  | bit hb => nomatch hb
  | shift hb => nomatch hb
  | exp hb => nomatch hb
  | order hb => nomatch hb
  | eq hb => nomatch hb
  | compareConst hb => nomatch hb
  | logic hb => nomatch hb

def unitE : Syn .unit :=
  .unit (.cons (.contract false "E" .none .nil
    (.cons (.event "Done" (.cons (.eventParam u256 false (some "v")) .nil) false)
    (.cons (.error "Bad" .nil) .nil))) .nil)

def CE : Ctx := { env := unitE.env, scope := some "E", locals := [] }
def LE : List (String × STy) := [("a", .int IntTy.u256)]

def w_emit : StmtD (k := .body) CE LE (.emit (.ident "Done") (.positional (.cons (.ident "a") .nil))) LE :=
  .emit (.cons (.loc rfl rfl) .nil) rfl

def w_revertError : StmtD (k := .body) CE LE (.revert (.ident "Bad") (.positional .nil)) LE :=
  .revertError .nil rfl

def r_emit : RStmt CE.env CE.rets CE.inModifier .body (tysOf LE) (tysOf LE) := w_emit.toR


inductive Coverage where
  | typed
  | operand (parent : Ctor) (role : String)
  | deferred (stage reason : String)
  deriving DecidableEq, Repr

def exprCoverage : Ctor → Option Coverage
  | .index | .member | .call | .payableConv | .unaryPrefix | .unarySuffix | .exp | .mulDivMod
  | .addSub | .shift | .bitAnd | .bitXor | .bitOr | .order | .equality | .and | .or | .cond
  | .assign | .tuple | .ident | .lit | .litUnit | .slice | .inlineArray => some .typed
  | .callOptions => some (.deferred "S02" "call options belong to external calls and creation (S02/S03)")
  | .metaType => some (.deferred "S04.02" "type(T) members read the artifact table and ABI identities")
  | .new => some (.deferred "S03" "contract creation is typed with its semantics; new T[](n), new bytes(n) and new string(n) are typed as the callee of a call (newArray, FU2-B)")
  | .elemType => some (.operand .call "a type name: the callee of an elementary conversion (convElem) and a type expression of abi.decode (abiDecode, FU2-B); type(T) is metaType's")
  | _ => none

theorem exprCoverage_total (e : Syn .expr) : (exprCoverage e.ctor).isSome = true := by
  cases e <;> rfl

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
    | exact ⟨_, _, rfl, ⟨w_slice⟩⟩
    | exact ⟨_, _, rfl, ⟨w_inlineArray⟩⟩

theorem exprCoverage_operand (k p : Ctor) (r : String) (ho : exprCoverage k = some (.operand p r)) :
    ∃ (e : Syn .expr) (τ : STy), e.ctor = p ∧ k ∈ e.nodes.map Node.ctor ∧ HasType Γ e τ := by
  cases k <;> simp only [exprCoverage, reduceCtorEq, Option.some.injEq, Coverage.operand.injEq] at ho
  obtain ⟨rfl, -⟩ := ho
  exact ⟨_, _, rfl, by decide, ⟨w_call⟩⟩

theorem elemType_decode_operand :
    ∃ (e : Syn .expr) (τ : STy), e.ctor = .call ∧ Ctor.elemType ∈ e.nodes.map Node.ctor ∧
      (∃ g x ts, e = .call (.member (.ident g) "decode") (.positional (.cons x (.cons ts .nil)))) ∧
      HasType Γ e τ :=
  ⟨_, _, rfl, by decide, ⟨_, _, _, rfl⟩, ⟨w_abiDecode⟩⟩

def stmtCoverage : Ctor → Option Coverage
  | .blockStmt | .simpleStmt | .declVar | .exprStmt | .ifStmt | .forStmt | .whileStmt | .doWhile
  | .continueStmt | .breakStmt | .returnStmt | .emit | .revert | .declTuple => some .typed
  | .tryStmt => some (.deferred "S03" "try/catch is an external call's; typed and evaluated for a call without value and one plain or bytes memory catch clause (tryCall, FU2-B), other clauses not")
  | .assembly => some (.deferred "S00" "inline assembly is excluded; only the canonical rethrow is typed (rethrow)")
  | _ => none

def w_declTuple : StmtD (k := .body) Γ Γ.locals
    (.simpleStmt (.declTuple 0 (.varDecl u256 none "p") (.cons .none .nil)
      (.tuple (.some a) (.cons (.some (.ident "b")) .nil))))
    (("p", .int IntTy.u256) :: Γ.locals) :=
  .declTuple (slots := [some ("p", .int IntTy.u256), none]) (by
    simp only [Ctx.tupleSlots, Ctx.declSlot, Ctx.declSlots]; rfl) w_tuple rfl

theorem slotsFit_hole_empty (B : DeclName → DeclName → Bool) (M : DeclName → Bool) :
    slotsFit B M [Option.none, Option.some (.int IntTy.u256)] [.tuple [], .int IntTy.u256] = false := rfl

theorem stmtCoverage_total {k : SCtx} (s : Syn (.stmt k)) : (stmtCoverage s.ctor).isSome = true := by
  cases s <;> rfl

theorem simpleCoverage_total (s : Syn .simple) : (stmtCoverage s.ctor).isSome = true := by
  cases s <;> rfl


def diamond : Syn .unit :=
  .unit (.cons (.contract false "A" .none .nil .nil)
    (.cons (.contract false "B" .none (.cons (.inherit ⟨"A", []⟩ .none) .nil) .nil)
    (.cons (.contract false "C" .none (.cons (.inherit ⟨"A", []⟩ .none) .nil) .nil)
    (.cons (.contract false "D" .none (.cons (.inherit ⟨"B", []⟩ .none)
      (.cons (.inherit ⟨"C", []⟩ .none) .nil)) .nil) .nil))))

theorem diamond_linearize : diamond.env.linearize "D" = some ["D", "C", "B", "A"] := rfl

theorem cycle_rejected :
    (Syn.unit (.cons (.contract false "X" .none (.cons (.inherit ⟨"Y", []⟩ .none) .nil) .nil)
      (.cons (.contract false "Y" .none (.cons (.inherit ⟨"X", []⟩ .none) .nil) .nil) .nil))).env.linearize
      "X" = none := rfl

theorem gasleft_excluded :
    Γ.resolve "gasleft" = some (.builtin .gasleft) ∧ Builtin.gasleft.status = .excluded "gasleft" :=
  ⟨rfl, rfl⟩

theorem blockNumber_excluded : Builtin.block.memberStatus "number" = some (.excluded "blockNumber") := rfl

theorem local_shadows :
    (Γ.push "count" .bool).resolve "count" = some (.loc 0) := rfl


theorem Typed.lit_num {Γ : Ctx} {n : NumLit} {σ : STy} (h : Typed Γ (.lit (.num n)) σ) :
    σ = .rational n.value ∨ (∃ len, σ = .hexConst n.value len) ∨ σ = .address false := by
  cases h with
  | const hq =>
    rw [Syn.const_lit_eq hq]
    exact Or.inl rfl
  | litBytes _ => exact Or.inr (Or.inl ⟨_, rfl⟩)
  | litAddress _ => exact Or.inr (Or.inr rfl)
  | arith hb => nomatch hb
  | bit hb => nomatch hb
  | shift hb => nomatch hb
  | exp hb => nomatch hb
  | order hb => nomatch hb
  | eq hb => nomatch hb
  | compareConst hb => nomatch hb
  | logic hb => nomatch hb

def tooBig : Syn (.stmt .body) :=
  .simpleStmt (.declVar (.varDecl (.elem (.int false 8 (by decide))) none "x")
    (.some (.lit (.num (.dec 300 0 0)))))

theorem tooBig_illTyped (C : Ctx) (L L' : List (String × STy)) : ¬ StmtOK C L tooBig L' := by
  intro ⟨h⟩
  cases h with
  | declInit ht _ he hc =>
    simp only [Syn.ty, Syn.tys, Elem.ty] at ht
    cases ht
    rcases Typed.lit_num he with rfl | ⟨_, rfl⟩ | rfl
    · rw [STy.implicit_rational_int] at hc
      exact absurd (of_decide_eq_true hc) (by decide)
    · rw [STy.implicit_hexConst_int] at hc
      exact absurd (of_decide_eq_true hc) (by decide)
    · cases hc

def shl18 : Syn .expr := .shift .shl one (.lit (.num (.dec 8 0 0)))

theorem shl18_folded {Γ : Ctx} {τ : STy} (h : Typed Γ shl18 τ) : τ = .rational (Q.ofInt 256) := by
  cases h with
  | const hq _ =>
    have hv : shl18.const = some (Q.ofInt 256) := rfl
    rw [hv] at hq
    cases hq
    rfl
  | shift hb _ _ _ _ hc =>
    cases hb
    exact absurd hc (by decide)
  | arith hb => nomatch hb
  | bit hb => nomatch hb
  | exp hb => nomatch hb
  | order hb => nomatch hb
  | eq hb => nomatch hb
  | compareConst hb hk =>
    cases hb
    rcases hk with h | h <;> cases h
  | logic hb => nomatch hb

theorem shlTooBig_illTyped (C : Ctx) (L L' : List (String × STy)) :
    ¬ StmtOK (k := .body) C L (.simpleStmt (.declVar (.varDecl (.elem (.int false 8 (by decide))) none "x")
      (.some shl18))) L' := by
  intro ⟨h⟩
  cases h with
  | declInit ht _ he hc =>
    simp only [Syn.ty, Syn.tys, Elem.ty] at ht
    cases ht
    rw [shl18_folded he] at hc
    rw [STy.implicit_rational_int] at hc
    exact absurd (of_decide_eq_true hc) (by decide)

theorem bareReturn_refused (L L' : List (String × STy)) :
    ¬ StmtOK (k := .body) Γ L (.returnStmt .none) L' := by
  intro ⟨h⟩
  cases h with
  | ret h => cases h

def fits_wellTyped : StmtD (k := .body) Γ Γ.locals (.simpleStmt (.declVar (.varDecl (.elem (.int false 8 (by decide)))
    none "x") (.some (.lit (.num (.dec 255 0 0)))))) (("x", .int IntTy.u8) :: Γ.locals) :=
  .declInit rfl rfl (.const rfl rfl rfl) rfl

example : (Syn.breakStmt (u := false) : Syn (.stmt ⟨true, false⟩)).ctor = .breakStmt := rfl


def counterRes : Resolution := resolveUnit ⟨.legacy, []⟩ counter

def counterTop : Syn .top :=
  .contract false "Counter" .none .nil
    (.cons (.stateVar u256 (some .pub) none none false "count" .none)
      (.cons (extFn "inc" (.cons incStmt .nil)) .nil))

theorem counter_decls_eq : counter.decls =
    [⟨.contract, "Counter", none, true, counterTop⟩,
     ⟨.stateVar, "count", some "Counter", false, .stateVar u256 (some .pub) none none false "count" .none⟩,
     ⟨.function, "inc", some "Counter", false, extFn "inc" (.cons incStmt .nil)⟩] := rfl

def incBody : ItemsD (k := .body)
    ({ env := counter.env, scope := some "Counter", locals := [], rets := [], msgValue := false } : Ctx)
    [] (.cons incStmt .nil) [] :=
  .stmt (.expr (.incDecSuffix (.state rfl rfl rfl) rfl) rfl) .nil

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

def clashing : Syn .unit :=
  .unit (.cons (.contract false "D" .none .nil
    (.cons (.stateVar u256 none none none false "x" .none) (.cons (extFn "x" .nil) .nil))) .nil)

theorem clashing_illFormed (s : Settings) : ¬ WellFormed (resolveUnit s clashing) := by
  intro h
  have e : clashing.decls.Pairwise fun d d' => d.clash clashing.env d' = false := h.noClash
  revert e
  decide

def sameSig : Syn .unit :=
  .unit (.cons (.contract false "O" .none .nil
    (.cons (.function (.ident "f") (.cons (.param u256 none (some "a")) .nil) (some .external) none .nil
        false none .nil (.some (.block .nil)))
      (.cons (.function (.ident "f") (.cons (.param u256 none (some "b")) .nil) (some .external) none .nil
        false none .nil (.some (.block .nil))) .nil))) .nil)

theorem sameSig_illFormed (s : Settings) : ¬ WellFormed (resolveUnit s sameSig) := by
  intro h
  have e : sameSig.decls.Pairwise fun d d' => d.clash sameSig.env d' = false := h.noClash
  revert e
  decide

def ifaceBody : Syn .unit :=
  .unit (.cons (.interface "I" .nil (.cons (extFn "f" .nil) .nil)) .nil)

theorem ifaceBody_illFormed (s : Settings) : ¬ WellFormed (resolveUnit s ifaceBody) := by
  intro h
  have e : ∀ d ∈ ifaceBody.decls, d.placementOK ifaceBody.env = true := h.placement
  revert e
  decide

def twoCtors : Syn .unit :=
  .unit (.cons (.contract false "K" .none .nil
    (.cons (.constructor .nil .nil false none (.block .nil))
      (.cons (.constructor .nil .nil false none (.block .nil)) .nil))) .nil)

theorem twoCtors_illFormed (s : Settings) : ¬ WellFormed (resolveUnit s twoCtors) := by
  intro h
  have e : twoCtors.decls.Pairwise fun d d' => d.clash twoCtors.env d' = false := h.noClash
  revert e
  decide

def noVisibility : Syn .unit :=
  .unit (.cons (.contract false "V" .none .nil
    (.cons (.function (.ident "f") .nil none none .nil false none .nil (.some (.block .nil))) .nil)) .nil)

theorem noVisibility_illFormed (s : Settings) : ¬ WellFormed (resolveUnit s noVisibility) := by
  intro h
  have e : ∀ d ∈ noVisibility.decls, d.placementOK noVisibility.env = true := h.placement
  revert e
  decide

theorem unknownPragma_illFormed (s : Settings) :
    ¬ WellFormed (resolveUnit s (.unit (.cons (.pragma ["solidity", "^0.8.0"]) (.cons (.pragma ["foo"]) .nil)))) := by
  intro h
  exact absurd (h.pragmas ["foo"] (List.mem_cons_of_mem _ (List.mem_singleton.2 rfl))) (by decide)

theorem counter_pipelines :
    (resolveUnit ⟨.legacy, []⟩ counter).coder = .v2 ∧ (resolveUnit ⟨.viaIR, []⟩ counter).coder = .v2 :=
  ⟨rfl, rfl⟩

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
/-- info: 'Solidity.Source.ItemsOK.resolved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.ItemsOK.resolved
/-- info: 'Solidity.Source.TypingExamples.shlTooBig_illTyped' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.TypingExamples.shlTooBig_illTyped
/-- info: 'Solidity.Source.TypingExamples.bareReturn_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.TypingExamples.bareReturn_refused
/-- info: 'Solidity.Source.TypingExamples.twoCtors_illFormed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.TypingExamples.twoCtors_illFormed

/-- info: 'Solidity.Source.TypingExamples.exprCoverage_operand' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.TypingExamples.exprCoverage_operand
/-- info: 'Solidity.Source.TypingExamples.elemType_decode_operand' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.TypingExamples.elemType_decode_operand
