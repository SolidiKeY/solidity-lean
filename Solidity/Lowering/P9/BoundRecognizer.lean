import Solidity.Source.Progress.BoundCatalogue
import Solidity.Lowering.P9.FragmentDecidable

/-! Executable sound recognizers for the bound-parent body catalogue. The
checked propositions (`ReadyExpr`, `ReadyItems`, `BoundParentItems`,
`FiniteDefault`, `BoundMemoryCatalogue`) are unchanged; each Boolean check only
implies them. `OpsOK` is not decided: it is taken from the enclosing elaborated
body (`Elaborated.body_opsOK`) and propagated to subterms. `FiniteDefault`
uses explicit fuel because struct layouts are not structurally smaller.
A `false` answer is not a refutation. -/
namespace Solidity.Source.Calls.Recognize
open EM Solidity.Lowering.P9 Solidity.Source.Progress
variable {E : Env} {Γ : RCtx}

/-- `PlainResultType`, as a Boolean. -/
def plainB (τ : STy) : Bool := τ.isValue || decide (τ.loc? = some .memory)

theorem plainB_sound {τ : STy} (h : plainB τ = true) : PlainResultType τ := by
  unfold plainB at h
  rcases Bool.or_eq_true_iff.mp h with value | memory
  · exact .inl value
  · exact .inr (of_decide_eq_true memory)

def newReadyB (E : Env) : STy → Bool
  | .bytes .memory | .string .memory => true
  | .array .memory σ none => σ.oneWord && (Val.default E.layout σ).isSome
  | _ => false

theorem newReadyB_sound : ∀ {τ : STy}, newReadyB E τ = true → NewReady E τ := by
  intro τ h
  unfold newReadyB at h
  split at h
  · exact .bytes
  · exact .string
  · rcases Bool.and_eq_true_iff.mp h with ⟨word, defaults⟩
    exact .array _ word defaults
  · cases h

def emptyB : STy → Bool
  | .bytes .memory | .string .memory | .array .memory _ none => true
  | _ => false

def zeroReadyB (E : Env) (τ : STy) : Bool := (Val.default E.layout τ).isSome || emptyB τ

theorem zeroReadyB_sound {τ : STy} (h : zeroReadyB E τ = true) : ZeroReady E τ := by
  unfold zeroReadyB at h
  rcases Bool.or_eq_true_iff.mp h with value | empty
  · exact .value value
  · unfold emptyB at empty
    split at empty
    · exact .memory .bytes
    · exact .memory .string
    · exact .memory (.array _)
    · cases empty

/-- `FiniteDefault` with explicit fuel for struct-field recursion. -/
def finiteDefaultB (E : Env) : Nat → STy → Bool
  | 0, τ => zeroReadyB E τ
  | n+1, τ => zeroReadyB E τ ||
      match τ with
      | .array .memory σ (some _) => finiteDefaultB E n σ
      | .struct .memory dn => (E.layout.fields dn).all (finiteDefaultB E n)
      | _ => false

theorem finiteDefaultB_sound : ∀ (n : Nat) {τ : STy}, finiteDefaultB E n τ = true → FiniteDefault E τ
  | 0, _, h => .ready (zeroReadyB_sound h)
  | n+1, τ, h => by
    unfold finiteDefaultB at h
    rcases Bool.or_eq_true_iff.mp h with ready | shape
    · exact .ready (zeroReadyB_sound ready)
    · split at shape
      · exact .fixed _ (finiteDefaultB_sound n shape)
      · exact .structNew _ (fun σ member => finiteDefaultB_sound n (List.all_eq_true.mp shape σ member))
      · cases shape

section
variable (vs : List Decl)

/-- The value-fragment disjunct (`ReadyExpr.value`), decided by P9. -/
def fragB {τ : STy} (e : RExpr E Γ τ) : Bool := decide (e.ValFragC (· ∈ vs))

/-- The structural `ReadyExpr` disjuncts; children may use either. -/
def readyB : {τ : STy} → RExpr E Γ τ → Bool
  | _, .local _ => true
  | τ, .conv (σ := σ) a _ => decide (σ = τ) && (fragB vs a || readyB a)
  | _, .cond c a b => (fragB vs c || readyB c) && (fragB vs a || readyB a) && (fragB vs b || readyB b)
  | τ, .newArray _ len _ => newReadyB E τ && (fragB vs len || readyB len)
  | _, .const .. | _, .bytesLit .. | _, .addressLit .. | _, .bool .. | _, .this ..
  | _, .compareConst .. | _, .state .. | _, .unary .. | _, .binary .. | _, .compare ..
  | _, .shiftLike .. | _, .assign .. | _, .compound .. | _, .incDec ..
  | _, .indexMapping .. | _, .call .. | _, .str .. | _, .tuple .. | _, .convExplicit ..
  | _, .delete .. | _, .indexArray .. | _, .indexBytes .. | _, .length .. | _, .payable ..
  | _, .magic .. | _, .balance .. | _, .builtin .. | _, .member .. | _, .structNew ..
  | _, .extCall .. | _, .transfer .. | _, .send .. | _, .abiEncode .. | _, .assignCopy ..
  | _, .abiDecode .. | _, .slice .. | _, .inlineArray .. => false
termination_by structural _ e => e

def exprB {τ : STy} (e : RExpr E Γ τ) : Bool := fragB vs e || readyB vs e

def argsB : {ts : List STy} → RConvArgs E Γ ts → Bool
  | _, .nil => true
  | _, .cons (σ := σ) (τ := τ) e _ es => decide (σ = τ) && plainB τ && exprB vs e && argsB es

def parentB {τ : STy} : RExpr E Γ τ → Bool
  | .inlineArray args _ => argsB vs args
  | .structNew _ args => argsB vs args
  | .local .. | .conv .. | .cond .. | .newArray .. | .const .. | .bytesLit .. | .addressLit .. | .bool ..
  | .this .. | .compareConst .. | .state .. | .unary .. | .binary .. | .compare .. | .shiftLike ..
  | .assign .. | .compound .. | .incDec .. | .indexMapping .. | .call .. | .str .. | .tuple ..
  | .convExplicit .. | .delete .. | .indexArray .. | .indexBytes .. | .length .. | .payable .. | .magic ..
  | .balance .. | .builtin .. | .member .. | .extCall .. | .transfer .. | .send .. | .abiEncode ..
  | .assignCopy .. | .abiDecode .. | .slice .. => false

variable {R : List STy} {M : Bool}

mutual
/-- The structural `ReadyStmt` disjuncts; children may use either. -/
def stmtB : {k : SCtx} → {Γ Δ : RCtx} → RStmt E R M k Γ Δ → Bool
  | _, _, _, .expr e => exprB vs e
  | _, _, _, .declVar τ => zeroReadyB E τ
  | _, _, _, .declInit (σ := σ) (τ := τ) e _ => decide (σ = τ) && plainB τ && exprB vs e
  | _, _, _, .retVal (σ := σ) (τ := τ) _ e _ => decide (σ = τ) && plainB τ && exprB vs e
  | _, _, _, .retTuple args => argsB vs args
  | _, _, _, .ifThen c t => exprB vs c && (decide (t.ValFragC (· ∈ vs)) || stmtB t)
  | _, _, _, .ifElse c t f => exprB vs c && (decide (t.ValFragC (· ∈ vs)) || stmtB t) &&
      (decide (f.ValFragC (· ∈ vs)) || stmtB f)
  | _, _, _, .block b => itemsB b
  | _, _, _, .whileLoop .. | _, _, _, .doWhile .. | _, _, _, .forLoop .. | _, _, _, .skip
  | _, _, _, .brk | _, _, _, .cont | _, _, _, .ret .. | _, _, _, .placeholder .. | _, _, _, .emit ..
  | _, _, _, .revertError .. | _, _, _, .rethrow .. | _, _, _, .declTuple .. | _, _, _, .tryCall .. => false

def itemsB : {k : SCtx} → {Γ Δ : RCtx} → RItems E R M k Γ Δ → Bool
  | _, _, _, .nil => true
  | _, _, _, .stmt s rest => (decide (s.ValFragC (· ∈ vs)) || stmtB s) && itemsB rest
  | _, _, _, .unchecked b rest => itemsB b && itemsB rest
end

/-- An initialized allocation-parent head, given the verdict on its suffix. -/
def initB {k : SCtx} {Γ Ξ : RCtx} : RStmt E R M k Γ Ξ → Bool → Bool
  | .declInit (σ := σ) (τ := τ) e _, tail => decide (σ = τ) && plainB τ && parentB vs e && tail
  | .expr .., _ | .declVar .., _ | .retVal .., _ | .retTuple .., _ | .ifThen .., _ | .ifElse .., _
  | .block .., _ | .whileLoop .., _ | .doWhile .., _ | .forLoop .., _ | .skip, _ | .brk, _ | .cont, _
  | .ret .., _ | .placeholder .., _ | .emit .., _ | .revertError .., _ | .rethrow .., _
  | .declTuple .., _ | .tryCall .., _ => false

/-- `BoundParentItems`: initialized allocation-parent prefixes, then ready items. -/
def boundB : {k : SCtx} → {Γ Δ : RCtx} → RItems E R M k Γ Δ → Bool
  | _, _, _, .nil => true
  | _, _, _, .stmt s rest => itemsB vs (.stmt s rest) || initB vs s (boundB rest)
  | _, _, _, .unchecked b rest => itemsB vs (.unchecked b rest)

end

/-! ## Soundness -/

section
variable {vs : List Decl}

theorem fragB_sound {τ : STy} {e : RExpr E Γ τ} (h : fragB vs e = true) : e.ValFragC (· ∈ vs) :=
  of_decide_eq_true h

/-- One child: either disjunct, given the structural verdict's soundness. -/
theorem child_sound {τ : STy} {a : RExpr E Γ τ}
    (structural : readyB vs a = true → a.OpsOK → ReadyExpr (· ∈ vs) a)
    (h : (fragB vs a || readyB vs a) = true) (o : a.OpsOK) : ReadyExpr (· ∈ vs) a :=
  (Bool.or_eq_true_iff.mp h).elim (fun f => .value (fragB_sound f) o) (fun r => structural r o)

theorem readyB_sound : ∀ {Γ : RCtx} {τ : STy} (e : RExpr E Γ τ),
    readyB vs e = true → e.OpsOK → ReadyExpr (· ∈ vs) e
  | _, _, .local i, _, _ => .local i
  | _, _, .conv a h, ok, ops => by
    simp only [readyB, Bool.and_eq_true, decide_eq_true_eq] at ok
    obtain ⟨rfl, inner⟩ := ok
    exact .same h (child_sound (readyB_sound a) inner ops)
  | _, _, .cond c a b, ok, ops => by
    simp only [readyB, Bool.and_eq_true] at ok
    exact .branch (child_sound (readyB_sound c) ok.1.1 ops.1)
      (child_sound (readyB_sound a) ok.1.2 ops.2.1) (child_sound (readyB_sound b) ok.2 ops.2.2)
  | _, _, .newArray _ len hl, ok, ops => by
    simp only [readyB, Bool.and_eq_true] at ok
    exact .newArray (newReadyB_sound ok.1) hl (child_sound (readyB_sound len) ok.2 ops)
  | _, _, .const .., ok, _ | _, _, .bytesLit .., ok, _ | _, _, .addressLit .., ok, _
  | _, _, .bool .., ok, _ | _, _, .this .., ok, _ | _, _, .compareConst .., ok, _
  | _, _, .state .., ok, _ | _, _, .unary .., ok, _ | _, _, .binary .., ok, _
  | _, _, .compare .., ok, _ | _, _, .shiftLike .., ok, _ | _, _, .assign .., ok, _
  | _, _, .compound .., ok, _ | _, _, .incDec .., ok, _ | _, _, .indexMapping .., ok, _
  | _, _, .call .., ok, _ | _, _, .str .., ok, _ | _, _, .tuple .., ok, _
  | _, _, .convExplicit .., ok, _ | _, _, .delete .., ok, _ | _, _, .indexArray .., ok, _
  | _, _, .indexBytes .., ok, _ | _, _, .length .., ok, _ | _, _, .payable .., ok, _
  | _, _, .magic .., ok, _ | _, _, .balance .., ok, _ | _, _, .builtin .., ok, _
  | _, _, .member .., ok, _ | _, _, .structNew .., ok, _ | _, _, .extCall .., ok, _
  | _, _, .transfer .., ok, _ | _, _, .send .., ok, _ | _, _, .abiEncode .., ok, _
  | _, _, .assignCopy .., ok, _ | _, _, .abiDecode .., ok, _ | _, _, .slice .., ok, _
  | _, _, .inlineArray .., ok, _ => by simp only [readyB, Bool.false_eq_true] at ok

theorem exprB_sound {τ : STy} {e : RExpr E Γ τ} (h : exprB vs e = true) (ops : e.OpsOK) :
    ReadyExpr (· ∈ vs) e :=
  child_sound (readyB_sound e) h ops

theorem argsB_sound : ∀ {Γ : RCtx} {ts : List STy} (es : RConvArgs E Γ ts),
    argsB vs es = true → es.OpsOK → ReadyArgs (· ∈ vs) es
  | _, _, .nil, _, _ => .nil
  | _, _, .cons e same es, ok, ops => by
    simp only [argsB, Bool.and_eq_true, decide_eq_true_eq] at ok
    obtain ⟨⟨⟨rfl, plain⟩, head⟩, tail⟩ := ok
    exact .cons same (plainB_sound plain) (exprB_sound head ops.1) (argsB_sound es tail ops.2)

theorem parentB_sound : ∀ {τ : STy} (e : RExpr E Γ τ), parentB vs e = true → e.OpsOK →
    AllocationParent (· ∈ vs) e
  | _, .inlineArray args word, ok, ops => .inline word (argsB_sound args ok ops)
  | _, .structNew typed args, ok, ops => .structNew typed (argsB_sound args ok ops)
  | _, .local .., ok, _ | _, .conv .., ok, _ | _, .cond .., ok, _ | _, .newArray .., ok, _
  | _, .const .., ok, _ | _, .bytesLit .., ok, _ | _, .addressLit .., ok, _ | _, .bool .., ok, _
  | _, .this .., ok, _ | _, .compareConst .., ok, _ | _, .state .., ok, _ | _, .unary .., ok, _
  | _, .binary .., ok, _ | _, .compare .., ok, _ | _, .shiftLike .., ok, _ | _, .assign .., ok, _
  | _, .compound .., ok, _ | _, .incDec .., ok, _ | _, .indexMapping .., ok, _ | _, .call .., ok, _
  | _, .str .., ok, _ | _, .tuple .., ok, _ | _, .convExplicit .., ok, _ | _, .delete .., ok, _
  | _, .indexArray .., ok, _ | _, .indexBytes .., ok, _ | _, .length .., ok, _
  | _, .payable .., ok, _ | _, .magic .., ok, _ | _, .balance .., ok, _ | _, .builtin .., ok, _
  | _, .member .., ok, _ | _, .extCall .., ok, _ | _, .transfer .., ok, _ | _, .send .., ok, _
  | _, .abiEncode .., ok, _ | _, .assignCopy .., ok, _ | _, .abiDecode .., ok, _
  | _, .slice .., ok, _ => by simp only [parentB, Bool.false_eq_true] at ok

variable {R : List STy} {M : Bool}

theorem stmtOr_sound {k : SCtx} {Γ Δ : RCtx} {s : RStmt E R M k Γ Δ}
    (structural : stmtB vs s = true → s.OpsOK → ReadyStmt (· ∈ vs) R M s)
    (ok : (decide (s.ValFragC (· ∈ vs)) || stmtB vs s) = true) (ops : s.OpsOK) :
    ReadyStmt (· ∈ vs) R M s :=
  (Bool.or_eq_true_iff.mp ok).elim (fun f => .value (of_decide_eq_true f) ops)
    (fun r => structural r ops)

mutual
theorem stmtB_sound : ∀ {k : SCtx} {Γ Δ : RCtx} (s : RStmt E R M k Γ Δ),
    stmtB vs s = true → s.OpsOK → ReadyStmt (· ∈ vs) R M s
  | _, _, _, .expr e, ok, ops => .expr (exprB_sound ok ops)
  | _, _, _, .declVar τ, ok, _ => .declVar τ (zeroReadyB_sound ok)
  | _, _, _, .declInit e same, ok, ops => by
    simp only [stmtB, Bool.and_eq_true, decide_eq_true_eq] at ok
    obtain ⟨⟨rfl, plain⟩, head⟩ := ok
    exact .declInit same (plainB_sound plain) (exprB_sound head ops)
  | _, _, _, .retVal returns e same, ok, ops => by
    simp only [stmtB, Bool.and_eq_true, decide_eq_true_eq] at ok
    obtain ⟨⟨rfl, plain⟩, head⟩ := ok
    exact .returnValue returns same (plainB_sound plain) (exprB_sound head ops)
  | _, _, _, .retTuple args, ok, ops => .returns (argsB_sound args ok ops)
  | _, _, _, .ifThen c t, ok, ops => by
    simp only [stmtB, Bool.and_eq_true] at ok
    exact .ifThen (exprB_sound ok.1 ops.1) (stmtOr_sound (stmtB_sound t) ok.2 ops.2)
  | _, _, _, .ifElse c t f, ok, ops => by
    simp only [stmtB, Bool.and_eq_true] at ok
    exact .ifElse (exprB_sound ok.1.1 ops.1) (stmtOr_sound (stmtB_sound t) ok.1.2 ops.2.1)
      (stmtOr_sound (stmtB_sound f) ok.2 ops.2.2)
  | _, _, _, .block b, ok, ops => .block (itemsB_sound b ok ops)
  | _, _, _, .whileLoop .., ok, _ | _, _, _, .doWhile .., ok, _ | _, _, _, .forLoop .., ok, _
  | _, _, _, .skip, ok, _ | _, _, _, .brk, ok, _ | _, _, _, .cont, ok, _ | _, _, _, .ret .., ok, _
  | _, _, _, .placeholder .., ok, _ | _, _, _, .emit .., ok, _ | _, _, _, .revertError .., ok, _
  | _, _, _, .rethrow .., ok, _ | _, _, _, .declTuple .., ok, _ | _, _, _, .tryCall .., ok, _ =>
    by simp only [stmtB, Bool.false_eq_true] at ok

theorem itemsB_sound : ∀ {k : SCtx} {Γ Δ : RCtx} (items : RItems E R M k Γ Δ),
    itemsB vs items = true → items.OpsOK → ReadyItems (· ∈ vs) R M items
  | _, _, _, .nil, _, _ => .nil
  | _, _, _, .stmt s rest, ok, ops => by
    simp only [itemsB, Bool.and_eq_true] at ok
    exact .stmt (stmtOr_sound (stmtB_sound s) ok.1 ops.1) (itemsB_sound rest ok.2 ops.2)
  | _, _, _, .unchecked b rest, ok, ops => by
    simp only [itemsB, Bool.and_eq_true] at ok
    exact .unchecked (itemsB_sound b ok.1 ops.1) (itemsB_sound rest ok.2 ops.2)
end

/-- The initialized head, given soundness of the suffix verdict. -/
theorem initB_sound {k : SCtx} {Γ Ξ Δ : RCtx} :
    ∀ (s : RStmt E R M k Γ Ξ) (rest : RItems E R M k Ξ Δ) (tail : Bool),
    (tail = true → rest.OpsOK → BoundParentItems (· ∈ vs) R M rest) →
    initB vs s tail = true → (RItems.stmt s rest).OpsOK →
    BoundParentItems (· ∈ vs) R M (.stmt s rest)
  | .declInit e same, rest, tail, suffix, ok, ops => by
    simp only [initB, Bool.and_eq_true, decide_eq_true_eq] at ok
    obtain ⟨⟨⟨rfl, plain⟩, parent⟩, good⟩ := ok
    exact .initialized same (plainB_sound plain) (parentB_sound e parent ops.1) (suffix good ops.2)
  | .expr .., _, _, _, ok, _ | .declVar .., _, _, _, ok, _ | .retVal .., _, _, _, ok, _
  | .retTuple .., _, _, _, ok, _ | .ifThen .., _, _, _, ok, _ | .ifElse .., _, _, _, ok, _
  | .block .., _, _, _, ok, _ | .whileLoop .., _, _, _, ok, _ | .doWhile .., _, _, _, ok, _
  | .forLoop .., _, _, _, ok, _ | .skip, _, _, _, ok, _ | .brk, _, _, _, ok, _
  | .cont, _, _, _, ok, _ | .ret .., _, _, _, ok, _ | .placeholder .., _, _, _, ok, _
  | .emit .., _, _, _, ok, _ | .revertError .., _, _, _, ok, _ | .rethrow .., _, _, _, ok, _
  | .declTuple .., _, _, _, ok, _ | .tryCall .., _, _, _, ok, _ => by simp only [initB, Bool.false_eq_true] at ok

theorem boundB_sound : ∀ {k : SCtx} {Γ Δ : RCtx} (items : RItems E R M k Γ Δ),
    boundB vs items = true → items.OpsOK → BoundParentItems (· ∈ vs) R M items
  | _, _, _, .nil, _, _ => .ready .nil
  | _, _, _, .unchecked b rest, ok, ops => .ready (itemsB_sound (.unchecked b rest) ok ops)
  | _, _, _, .stmt s rest, ok, ops => by
    simp only [boundB, Bool.or_eq_true] at ok
    rcases ok with ready | initialized
    · exact .ready (itemsB_sound _ ready ops)
    · exact initB_sound s rest _ (boundB_sound rest) initialized ops

end

/-! ## Catalogue checker -/

/-- One catalogue entry, read from the actual dispatch target and body. -/
def entryB (G : Glob E) (c : String) (vs : List Decl) (fuel : Nat) (d : Decl) : Bool :=
  decide (d ∈ E.decls) &&
    match d.fnSig E, (G.dispatchFn c d).fnSig E, G.prog.body (G.dispatchFn c d) with
    | some (_, rs), some (_, rs'), some b =>
      decide (rs' = rs) && b.mods.isEmpty && rs.all (finiteDefaultB E fuel) && boundB vs b.items
    | _, _, _ => false

def catalogueB (G : Glob E) (c : String) (vs : List Decl) (fuel : Nat) (ds : List Decl) : Bool :=
  ds.all (entryB G c vs fuel)

/-- The checker implies the unchanged catalogue proposition. `OpsOK` of the
selected body comes from actual elaboration. -/
theorem catalogueB_sound (el : Elaborated) (G : Glob el.res.env) (program : G.prog = el.prog)
    (c : String) (values ds : List Decl) (fuel : Nat)
    (checked : WholeProgram.check el.res G c values = true)
    (ok : catalogueB G c values fuel ds = true) :
    BoundMemoryCatalogue (fun d => d ∈ values) G c ds := by
  intro d member
  have entry := List.all_eq_true.mp ok d member
  unfold entryB at entry
  rcases Bool.and_eq_true_iff.mp entry with ⟨declared, rest⟩
  have declared : d ∈ el.res.env.decls := of_decide_eq_true declared
  split at rest
  · rename_i ps rs targetPs rs' b sourceSig targetSig body
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.isEmpty_iff] at rest
    obtain ⟨⟨⟨rfl, mods⟩, defaults⟩, items⟩ := rest
    have environment : el.res.env.decls = el.res.unit.decls := by
      have certificate := checked
      simp only [WholeProgram.check, Bool.and_eq_true, decide_eq_true_eq] at certificate
      exact certificate.1
    have targetMember : G.dispatchFn c d ∈ el.res.unit.decls := by
      rw [← environment]
      exact WholeProgram.dispatch_mem G c d el.res.env.decls rfl declared
    have ops := (el.body_opsOK targetMember (program ▸ body)).1
    exact ⟨declared, ps, rs', targetPs, b, sourceSig, targetSig, body, mods,
      fun τ m => finiteDefaultB_sound fuel (List.all_eq_true.mp defaults τ m),
      boundB_sound b.items items ops⟩
  · cases rest

theorem catalogueB_from_elaborate (res : Resolution) (elaborated : (Source.elaborate res).isSome = true)
    (G : Glob res.env) (program : G.prog = Source.progOf res.env) (c : String)
    (values ds : List Decl) (fuel : Nat)
    (checked : WholeProgram.check res G c values = true)
    (ok : catalogueB G c values fuel ds = true) :
    BoundMemoryCatalogue (fun d => d ∈ values) G c ds := by
  obtain ⟨el,result⟩ := Option.isSome_iff_exists.mp elaborated
  obtain ⟨resolution,bodyProgram⟩ := elaborate_program result
  rcases el with ⟨r,prog,bodies,constructors,mods,constructorTypes,constructorOrder,inits,bases⟩
  dsimp only at resolution bodyProgram
  subst res
  have same : prog = Source.progOf r.env := eq_of_heq bodyProgram
  subst prog
  exact catalogueB_sound ⟨r,Source.progOf r.env,bodies,constructors,mods,
    constructorTypes,constructorOrder,inits,bases⟩ G program c values ds fuel checked ok

/-- Complete admitted call program with no catalogue proof supplied: the
value domain, bound-body catalogue and coverage are all Boolean checks. -/
theorem checked_program_calls (res : Resolution)
    (elaborated : (Source.elaborate res).isSome = true)
    (G : Glob res.env) (program : G.prog = Source.progOf res.env) (c : String)
    (values memory : List Decl) (fuel : Nat)
    (checked : WholeProgram.check res G c values = true)
    (ok : catalogueB G c values fuel memory = true)
    (complete : readyCoverage res values memory = true) : ReadyProgramCalls res G c :=
  bound_memory_program_calls res elaborated G program c values memory checked
    (catalogueB_from_elaborate res elaborated G program c values memory fuel checked ok) complete

/-- info: 'Solidity.Source.Calls.Recognize.readyB_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms readyB_sound
/-- info: 'Solidity.Source.Calls.Recognize.argsB_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms argsB_sound
/-- info: 'Solidity.Source.Calls.Recognize.parentB_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms parentB_sound
/-- info: 'Solidity.Source.Calls.Recognize.itemsB_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms itemsB_sound
/-- info: 'Solidity.Source.Calls.Recognize.boundB_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms boundB_sound
/-- info: 'Solidity.Source.Calls.Recognize.finiteDefaultB_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms finiteDefaultB_sound
/-- info: 'Solidity.Source.Calls.Recognize.catalogueB_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms catalogueB_sound
/-- info: 'Solidity.Source.Calls.Recognize.catalogueB_from_elaborate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms catalogueB_from_elaborate
/-- info: 'Solidity.Source.Calls.Recognize.checked_program_calls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms checked_program_calls

end Solidity.Source.Calls.Recognize
