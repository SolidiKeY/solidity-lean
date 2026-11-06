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
def readyB : {Γ : RCtx} → {τ : STy} → RExpr E Γ τ → Bool
  | _, _, .local _ => true
  | _, τ, .conv (σ := σ) a _ => decide (σ = τ) && (fragB vs a || readyB a)
  | _, _, .cond c a b => (fragB vs c || readyB c) && (fragB vs a || readyB a) && (fragB vs b || readyB b)
  | _, τ, .newArray _ len _ => newReadyB E τ && (fragB vs len || readyB len)
  | _, _, _ => false

def exprB {τ : STy} (e : RExpr E Γ τ) : Bool := fragB vs e || readyB vs e

def argsB : {Γ : RCtx} → {ts : List STy} → RConvArgs E Γ ts → Bool
  | _, _, .nil => true
  | _, _, .cons (σ := σ) (τ := τ) e _ es => decide (σ = τ) && plainB τ && exprB vs e && argsB es

def parentB {τ : STy} : RExpr E Γ τ → Bool
  | .inlineArray args _ => argsB vs args
  | .structNew _ args => argsB vs args
  | _ => false

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
  | _, _, _, _ => false

def itemsB : {k : SCtx} → {Γ Δ : RCtx} → RItems E R M k Γ Δ → Bool
  | _, _, _, .nil => true
  | _, _, _, .stmt s rest => (decide (s.ValFragC (· ∈ vs)) || stmtB s) && itemsB rest
  | _, _, _, .unchecked b rest => itemsB b && itemsB rest
end

/-- `BoundParentItems`: initialized allocation-parent prefixes, then ready items. -/
def boundB : {k : SCtx} → {Γ Δ : RCtx} → RItems E R M k Γ Δ → Bool
  | _, _, _, items@(.stmt (.declInit (σ := σ) (τ := τ) e _) rest) =>
      itemsB vs items || (decide (σ = τ) && plainB τ && parentB vs e && boundB rest)
  | _, _, _, items => itemsB vs items

end

/-! ## Soundness -/

section
variable {vs : List Decl}

theorem fragB_sound {τ : STy} {e : RExpr E Γ τ} (h : fragB vs e = true) : e.ValFragC (· ∈ vs) :=
  of_decide_eq_true h

theorem readyB_sound {Γ : RCtx} {τ : STy} (e : RExpr E Γ τ)
    (ok : readyB vs e = true) (ops : e.OpsOK) : ReadyExpr (· ∈ vs) e := by
  have child : ∀ {τ : STy} (a : RExpr E Γ τ), (fragB vs a || readyB vs a) = true → a.OpsOK →
      ReadyExpr (· ∈ vs) a := fun a h o =>
    (Bool.or_eq_true_iff.mp h).elim (fun f => .value (fragB_sound f) o) (fun r => readyB_sound a r o)
  cases e with
  | «local» i => exact .local i
  | conv a h =>
    simp only [readyB, Bool.and_eq_true, decide_eq_true_eq] at ok
    obtain ⟨rfl, inner⟩ := ok
    exact .same h (child a inner ops)
  | cond c a b =>
    simp only [readyB, Bool.and_eq_true] at ok
    exact .branch (child c ok.1.1 ops.1) (child a ok.1.2 ops.2.1) (child b ok.2 ops.2.2)
  | newArray hτ len hl =>
    simp only [readyB, Bool.and_eq_true] at ok
    exact .newArray (newReadyB_sound ok.1) hl (child len ok.2 ops)
  | _ => exact absurd ok (by simp only [readyB]; decide)

theorem exprB_sound {τ : STy} {e : RExpr E Γ τ} (h : exprB vs e = true) (ops : e.OpsOK) :
    ReadyExpr (· ∈ vs) e :=
  (Bool.or_eq_true_iff.mp h).elim (fun f => .value (fragB_sound f) ops) (fun r => readyB_sound e r ops)

theorem argsB_sound : ∀ {Γ : RCtx} {ts : List STy} (es : RConvArgs E Γ ts),
    argsB vs es = true → es.OpsOK → ReadyArgs (· ∈ vs) es
  | _, _, .nil, _, _ => .nil
  | _, _, .cons e same es, ok, ops => by
    simp only [argsB, Bool.and_eq_true, decide_eq_true_eq] at ok
    obtain ⟨⟨⟨rfl, plain⟩, head⟩, tail⟩ := ok
    exact .cons same (plainB_sound plain) (exprB_sound head ops.1) (argsB_sound es tail ops.2)

theorem parentB_sound {τ : STy} (e : RExpr E Γ τ) (ok : parentB vs e = true) (ops : e.OpsOK) :
    AllocationParent (· ∈ vs) e := by
  cases e with
  | inlineArray args word => exact .inline word (argsB_sound args ok ops)
  | structNew typed args => exact .structNew typed (argsB_sound args ok ops)
  | _ => exact absurd ok (by simp only [parentB]; decide)

variable {R : List STy} {M : Bool}

mutual
theorem stmtB_sound {k : SCtx} {Γ Δ : RCtx} (s : RStmt E R M k Γ Δ)
    (ok : stmtB vs s = true) (ops : s.OpsOK) : ReadyStmt (· ∈ vs) R M s := by
  cases s with
  | expr e => exact .expr (exprB_sound ok ops)
  | declVar τ => exact .declVar τ (zeroReadyB_sound ok)
  | declInit e same =>
    simp only [stmtB, Bool.and_eq_true, decide_eq_true_eq] at ok
    obtain ⟨⟨rfl, plain⟩, head⟩ := ok
    exact .declInit same (plainB_sound plain) (exprB_sound head ops)
  | retVal returns e same =>
    simp only [stmtB, Bool.and_eq_true, decide_eq_true_eq] at ok
    obtain ⟨⟨rfl, plain⟩, head⟩ := ok
    exact .returnValue returns same (plainB_sound plain) (exprB_sound head ops)
  | retTuple args => exact .returns (argsB_sound args ok ops)
  | ifThen c t =>
    simp only [stmtB, Bool.and_eq_true] at ok
    exact .ifThen (exprB_sound ok.1 ops.1) (stmtOrB_sound t ok.2 ops.2)
  | ifElse c t f =>
    simp only [stmtB, Bool.and_eq_true] at ok
    exact .ifElse (exprB_sound ok.1.1 ops.1) (stmtOrB_sound t ok.1.2 ops.2.1)
      (stmtOrB_sound f ok.2 ops.2.2)
  | block b => exact .block (itemsB_sound b ok ops)
  | _ => exact absurd ok (by simp only [stmtB]; decide)

theorem stmtOrB_sound {k : SCtx} {Γ Δ : RCtx} (s : RStmt E R M k Γ Δ)
    (ok : (decide (s.ValFragC (· ∈ vs)) || stmtB vs s) = true) (ops : s.OpsOK) :
    ReadyStmt (· ∈ vs) R M s :=
  (Bool.or_eq_true_iff.mp ok).elim (fun f => .value (of_decide_eq_true f) ops)
    (fun r => stmtB_sound s r ops)

theorem itemsB_sound {k : SCtx} {Γ Δ : RCtx} (items : RItems E R M k Γ Δ)
    (ok : itemsB vs items = true) (ops : items.OpsOK) : ReadyItems (· ∈ vs) R M items := by
  cases items with
  | nil => exact .nil
  | stmt s rest =>
    simp only [itemsB, Bool.and_eq_true] at ok
    exact .stmt (stmtOrB_sound s ok.1 ops.1) (itemsB_sound rest ok.2 ops.2)
  | unchecked b rest =>
    simp only [itemsB, Bool.and_eq_true] at ok
    exact .unchecked (itemsB_sound b ok.1 ops.1) (itemsB_sound rest ok.2 ops.2)
end

theorem boundB_sound {k : SCtx} {Γ Δ : RCtx} (items : RItems E R M k Γ Δ)
    (ok : boundB vs items = true) (ops : items.OpsOK) : BoundParentItems (· ∈ vs) R M items := by
  cases items with
  | nil => exact .ready (itemsB_sound _ ok ops)
  | unchecked b rest => exact .ready (itemsB_sound _ ok ops)
  | stmt s rest =>
    cases s with
    | declInit e same =>
      simp only [boundB, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at ok
      rcases ok with ready | ⟨⟨⟨rfl, plain⟩, parent⟩, tail⟩
      · exact .ready (itemsB_sound _ ready ops)
      · exact .initialized same (plainB_sound plain) (parentB_sound e parent ops.1)
          (boundB_sound rest tail ops.2)
    | _ => exact .ready (itemsB_sound _ ok ops)

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

#print axioms readyB_sound
#print axioms argsB_sound
#print axioms parentB_sound
#print axioms itemsB_sound
#print axioms boundB_sound
#print axioms finiteDefaultB_sound
#print axioms catalogueB_sound
#print axioms catalogueB_from_elaborate
#print axioms checked_program_calls

end Solidity.Source.Calls.Recognize
