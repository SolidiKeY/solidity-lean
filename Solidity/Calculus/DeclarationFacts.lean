import Solidity.Calculus.SurfaceSpec
import Solidity.Calculus.Logic
import Solidity.Calculus.Quote

/-!
# Certified declaration facts

The scalar bounds and quantified mapping facts generated for specifications
are mathematical facts about typed reads. They need not be established by
trying a finite pool of mapping keys. `Path.Declared` records the paths whose
reads return in every typed storage: roots, struct fields and mapping keys.
Array indices remain partial and are deliberately absent.
-/

namespace Solidity

variable {C : Contract}

/-- A path through declarations only, with no array index. -/
inductive Path.Declared : {T U : Ty} → Path T U → Prop where
  | nil {T : Ty} : Declared (Path.nil (T := T))
  | field {s f : Name} {T U : Ty} (h : Semantics.lookupBy f (Semantics.structDef s) = some T)
      {p : Path T U} (hp : Declared p) : Declared (.field h p)
  | key {K : PrimTy} {T U : Ty} (k : K.Denote) {p : Path T U}
      (hp : Declared p) : Declared (.key k p)

/-- Following two declared paths still has no failing array read. -/
theorem Path.Declared.append {T U V : Ty} {p : Path T U} (hp : p.Declared)
    {q : Path U V} (hq : q.Declared) : (p.append q).Declared := by
  induction hp with
  | nil => simpa only [Path.append_nil] using hq
  | field h _ ih => simpa only [Path.append_field] using Declared.field h (ih hq)
  | key k _ ih => simpa only [Path.append_key] using Declared.key k (ih hq)

/-- Every declared path reads a value of its endpoint type, including a
mapping key absent from its finite entries (which reads the typed default). -/
theorem Path.Declared.find {T U : Ty} {p : Path T U} (hp : p.Declared) (v : SVal T) :
    ∃ w : SVal U, v.find p = some w := by
  induction hp with
  | nil => exact ⟨v, rfl⟩
  | field h _ ih =>
    cases v with
    | struct fs => exact ih (fs.get h)
  | key k _ ih =>
    cases v with
    | map entries dflt =>
      rw [SVal.find_key]
      cases h : Semantics.lookupBy k entries.toList with
      | none => exact ih dflt
      | some w => exact ih w

/-- A storage reference whose path uses only total declaration steps. -/
def SRef.Declared {T : Ty} (r : SRef C T) : Prop := r.path.Declared

/-- A declared location can be read in every typed storage. -/
theorem SRef.Declared.find {T : Ty} {r : SRef C T} (h : r.Declared) (st : Storage C) :
    ∃ w : SVal T, st.find r = some w := Path.Declared.find h (st.get r.hroot)

namespace Tm

variable {Γ : Ctx}

/-- A term that returns in every typed state of its context. -/
def Total {s : Srt} (t : Tm C Γ s) : Prop := ∀ σ : State C Γ, ∃ v, t.eval σ = some v

/-- A path term that always names a declared location. -/
def Declared {T : Ty} (t : Tm C Γ (.path T)) : Prop :=
  ∀ σ : State C Γ, ∃ r, t.eval σ = some r ∧ r.Declared

theorem total_local {p : PrimTy} (i : Idx Γ (.val p)) : Total (pvV (C := C) i) :=
  fun _ => ⟨_, rfl⟩

theorem total_lit {p : PrimTy} (v : p.Denote) : Total (app0 (.lit v) : Tm C Γ _) :=
  fun _ => ⟨v, rfl⟩

theorem total_env (k : EnvKey) : Total (app0 (.env k) : Tm C Γ _) :=
  fun σ => ⟨σ.envVal k, rfl⟩

theorem total_storage : Total (app0 .storage : Tm C Γ _) := fun σ => ⟨σ.storage, rfl⟩

theorem total_old (i : Idx Γ .old) : Total (pvS (C := C) i) := fun _ => ⟨_, rfl⟩

theorem declared_root (r : Name) {T : Ty} (h : C.rootType r = some T) :
    Declared (app0 (.root r h) : Tm C Γ _) := fun _ => ⟨_, rfl, .nil⟩

theorem declared_field {s f : Name} {T : Ty} (h : C.fieldType s f = some T)
    {q : Tm C Γ (.path (.ref (.struct s)))} (hq : q.Declared) :
    Declared (app1 (.field h) q) := by
  intro σ
  obtain ⟨r, hr, hd⟩ := hq σ
  refine ⟨r.field h, ?_, hd.append (.field h .nil)⟩
  simp only [Tm.eval_app1, Close.Op1.eval_field, hr, Option.map_some]

theorem declared_key {K : PrimTy} {T : Ty}
    {q : Tm C Γ (.path (.ref (.mapping K T)))} {k : Tm C Γ (.val K)}
    (hq : q.Declared) (hk : k.Total) : Declared (app2 (.at .map) q k) := by
  intro σ
  obtain ⟨r, hr, hd⟩ := hq σ
  obtain ⟨v, hv⟩ := hk σ
  obtain ⟨w, hw⟩ := SRef.Declared.find hd σ.storage
  refine ⟨r.index .map v, ?_, ?_⟩
  · rw [Tm.eval_app2, Close.Op2.eval_at, hr, hv]
    simp only [Option.bind_some]
    change σ.storage.atT .map r v = some (r.index .map v)
    unfold Storage.atT Storage.checkIndex
    rw [hw]
    cases w
    rfl
  · exact hd.append (by rw [Path.index_map]; exact .key v .nil)

theorem total_find {p : PrimTy} {s : Tm C Γ .st} {q : Tm C Γ (.path (.prim p))}
    (hs : s.Total) (hq : q.Declared) : Total (app2 .find s q) := by
  intro σ
  obtain ⟨st, hst⟩ := hs σ
  obtain ⟨r, hr, hd⟩ := hq σ
  obtain ⟨v, hv⟩ := SRef.Declared.find hd st
  refine ⟨v.view, ?_⟩
  simp only [Tm.eval_app2, Close.Op2.eval_find, hst, hr, Option.bind_some]
  change (st.find r).bind (fun v => some v.view) = some v.view
  rw [hv]
  rfl

theorem total_not {t : Tm C Γ (.val .bool)} (ht : t.Total) :
    Total (app1 (.unop .not rfl) t) := by
  intro σ
  obtain ⟨v, hv⟩ := ht σ
  refine ⟨!v, ?_⟩
  simp only [Tm.eval_app1, Close.Op1.eval_unop, hv, Option.bind_some, UnOp.evalT]

end Tm

namespace DeclarationFacts

open Semantics

variable {Γ : Ctx}

/-- A typed scalar's inclusive declaration bounds. -/
def lower : (p : PrimTy) → p.Denote
  | .bool => false
  | .uint => PrimTy.ofLit .uint 0 rfl
  | .int => PrimTy.ofLit .int (-intBound) (by decide)

def upper : (p : PrimTy) → p.Denote
  | .bool => true
  | .uint => PrimTy.ofLit .uint (uintBound - 1) (by decide)
  | .int => PrimTy.ofLit .int (intBound - 1) (by decide)

/-- The range formula emitted by a numeric declaration, at its actual type. -/
def range {p : PrimTy} (hp : p ≠ .bool) (t : Tm C Γ (.val p)) : Fml C Γ :=
  let h : BinOp.le.accepts p = true := by
    cases p <;> simp_all only [BinOp.accepts, PrimTy.isNumeric, ne_self_iff_false]
  .and (.eqD (.app2 (.binop .le h) (.app0 (.lit (lower p))) t) (.app0 (.lit true)))
    (.eqD (.app2 (.binop .le h) t (.app0 (.lit (upper p)))) (.app0 (.lit true)))

/-- Every defined typed numeric read satisfies its declared range. -/
theorem range_holds {p : PrimTy} (hp : p ≠ .bool) {t : Tm C Γ (.val p)}
    (ht : t.Total) (σ : State C Γ) : holds σ (range hp t) := by
  obtain ⟨v, hv⟩ := ht σ
  cases p with
  | bool => exact (hp rfl).elim
  | uint =>
    have hb : 0 ≤ v.1 ∧ v.1 < uintBound := by
      have h := v.property
      simpa only [PrimTy.inRange, decide_eq_true_eq] using h
    have hu : v.1 ≤ uintBound - 1 := by omega
    unfold range
    constructor <;> apply (holds_eqD _ _ _).2 <;> refine ⟨true, ?_, rfl⟩
    · rw [Tm.eval_app2, Close.Op2.eval_binop, hv]
      change some (decide (0 ≤ v.1)) = some true
      simp only [hb.1, decide_true]
    · rw [Tm.eval_app2, Close.Op2.eval_binop, hv]
      change some (decide (v.1 ≤ uintBound - 1)) = some true
      simp only [hu, decide_true]
  | int =>
    have hb : -intBound ≤ v.1 ∧ v.1 < intBound := by
      have h := v.property
      simpa only [PrimTy.inRange, decide_eq_true_eq] using h
    have hu : v.1 ≤ intBound - 1 := by omega
    unfold range
    constructor <;> apply (holds_eqD _ _ _).2 <;> refine ⟨true, ?_, rfl⟩
    · rw [Tm.eval_app2, Close.Op2.eval_binop, hv]
      change some (decide (-intBound ≤ v.1)) = some true
      simp only [hb.1, decide_true]
    · rw [Tm.eval_app2, Close.Op2.eval_binop, hv]
      change some (decide (v.1 ≤ intBound - 1)) = some true
      simp only [hu, decide_true]

/-- Declaration facts can be proved before choosing a state or a mapping key. -/
def Valid (φ : Fml C Γ) : Prop := ∀ σ : State C Γ, holds σ φ

theorem uint_range {t : Tm C Γ (.val .uint)} (ht : t.Total) :
    Valid (range (by decide : PrimTy.uint ≠ .bool) t) := range_holds _ ht

theorem int_range {t : Tm C Γ (.val .int)} (ht : t.Total) :
    Valid (range (by decide : PrimTy.int ≠ .bool) t) := range_holds _ ht

theorem bool_range {t : Tm C Γ (.val .bool)} (ht : t.Total) :
    Valid (.eqD (.app1 (.unop .not rfl) t) (.app1 (.unop .not rfl) t)) := by
  intro σ
  obtain ⟨v, hv⟩ := Tm.total_not ht σ
  exact (holds_eqD _ _ _).2 ⟨v, hv, hv⟩

theorem valid_true : Valid (.tt : Fml C Γ) := fun _ => trivial

theorem valid_and {φ ψ : Fml C Γ} (hφ : Valid φ) (hψ : Valid ψ) :
    Valid (.and φ ψ) := fun σ => ⟨hφ σ, hψ σ⟩

theorem valid_all (x : Var) (p : PrimTy) {φ : Fml C (.val p :: Γ)} (hφ : Valid φ) :
    Valid (.all x p φ) := fun σ v => hφ (σ.push (t := .val p) v)

open Lean Meta Elab Tactic

/-- Search only the declaration rules, with a shared node budget. Every
successful branch is an ordinary proof term checked by the kernel. -/
private partial def proveCore (conjunctions : Bool) (g : MVarId) : StateRefT Nat MetaM Unit := do
  let n ← get
  if n == 0 then throwError "declaration facts: node budget exhausted"
  set (n - 1)
  let rules := #[``uint_range, ``int_range, ``bool_range, ``valid_true,
    ``valid_and, ``valid_all, ``Tm.total_local, ``Tm.total_lit, ``Tm.total_env,
    ``Tm.total_storage, ``Tm.total_old, ``Tm.total_find, ``Tm.total_not,
    ``Tm.declared_root, ``Tm.declared_field, ``Tm.declared_key]
  for rule in rules do
    if !conjunctions && rule == ``valid_and then continue
    let saved ← saveState
    try
      let attempt ← liftM <| tryCatchRuntimeEx (withCurrHeartbeats <| g.withContext do
        pure (some (← g.apply (← mkConstWithFreshMVarLevels rule)))) (fun _ => pure none)
      let some goals := attempt | throwError "declaration facts: rule did not finish"
      for next in goals do proveCore conjunctions next
      return
    catch _ => saved.restore
  throwError "declaration facts: outside the certified declaration fragment"

/-- Produce a proof that a declaration formula holds in every typed state.
No user hypothesis or semantic closure rule is used by the search. -/
def prove (φ : Expr) (budget : Nat := 1024) (conjunctions : Bool := true) : MetaM Expr := do
  let goal ← mkFreshExprMVar (← mkAppM ``Valid #[φ])
  tryCatchRuntimeEx (do
    (proveCore conjunctions goal.mvarId!).run' budget
    instantiateMVars goal) fun e => throw e

/-- The specification reader's generated declaration ranges, quoted as an
ordinary scoped formula. Compilation errors are reported, never discarded. -/
syntax (name := declarationFactsTerm) "declaration_facts[" term "]" : term

@[term_elab declarationFactsTerm]
def elabDeclarationFacts : Term.TermElab := fun stx _ => do
  let cE ← instantiateMVars (← Term.elabTerm stx[1] (some (mkConst ``Contract)))
  unless cE.isConst do throwError "declaration_facts: expected a named contract"
  let c ← unsafe evalExpr Contract (mkConst ``Contract) cE
  match NRead.conj (layoutFmls c (c.vars.map (·.1))) [] with
  | .ok φ => pure (Fml.quote cE φ)
  | .error e => throwError "declaration_facts: {e}"

/-- Certify the ranges generated from scalar, struct and mapping declarations. -/
elab "sol_decl_facts" : tactic => withMainContext do
  let goal ← getMainGoal
  let ty ← goal.getType
  if ty.isAppOfArity ``Solidity.Valid 2 then
    goal.assign (← prove ty.appArg!)
  else if ty.isAppOfArity ``holds 4 then
    goal.assign (mkApp (← prove ty.appArg!) ty.appFn!.appArg!)
  else
    unless ty.isAppOfArity ``DeclarationFacts.Valid 3 do
      throwError "sol_decl_facts: expected validity or satisfaction of a scoped formula"
    goal.assign (← prove ty.appArg!)
  replaceMainGoal []

end DeclarationFacts

end Solidity
