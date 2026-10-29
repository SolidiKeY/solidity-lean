import Solidity.Source.Inheritance
import Solidity.Frontend.Static.WellFormedCheck

/-!
# Checking inheritance (G14)

Boolean checkers for the relations of `Solidity/Source/Inheritance.lean`,
each proved to decide its relation exactly (`*_iff`), and `inheritanceB`
for the whole judgment `InheritanceOK` (`inheritance_iff`).  Callable
identity: in a `WellFormed` unit, two functions with one identity (contract,
name, parameter types) are one declaration (`callable_unique`).
-/

namespace Solidity.Frontend.Static

open Solidity.Source

/-! ## Overrides -/

/-- The override check of one function. -/
def fnOverrideB (E : Env) (c : String) (d : Decl) : Bool :=
  let bs := E.baseFns c d
  (bs.isEmpty || d.overrideList.isSome) &&
  (!bs.isEmpty || d.overrideList.isNone) &&
  bs.all (·.isVirtual E) &&
  (decide (bs.length < 2) || bs.all fun f =>
    match d.overrideList with
    | Option.some ps => (overrideNames ps).contains (f.scope.getD "")
    | Option.none => false) &&
  (match d.overrideList with
   | Option.some ps => (overrideNames ps).all fun n => bs.any (·.scope == Option.some n)
   | Option.none => true) &&
  bs.all (fun f => visOK f.fnVis d.fnVis) &&
  bs.all (fun f => mutOK f.mutability d.mutability) &&
  bs.all (fun f => f.sameRets E d)

theorem fnOverrideB_iff {E : Env} {c : String} {d : Decl} : fnOverrideB E c d = true ↔ FnOverrideOK E c d := by
  simp only [fnOverrideB, Bool.and_eq_true, Bool.or_eq_true, List.all_eq_true, List.isEmpty_iff,
    Bool.not_eq_true', Option.isSome_iff_exists, Option.isNone_iff_eq_none, decide_eq_true_eq]
  constructor
  · intro ⟨⟨⟨⟨⟨⟨⟨hm, hn⟩, hv⟩, hl⟩, hval⟩, hvis⟩, hmu⟩, hr⟩
    refine ⟨fun h => ?_, fun h => ?_, hv, fun h2 f hf => ?_, fun ps hps n hn' => ?_, hvis, hmu, hr⟩
    · rcases hm with h' | h'
      · exact absurd h' h
      · obtain ⟨ps, hps⟩ := h'; rw [hps]; rfl
    · rcases hn with h' | h'
      · rw [h] at h'; cases h'
      · exact h'
    · rcases hl with h' | h'
      · omega
      · have := h' f hf
        cases ho : d.overrideList with
        | none => rw [ho] at this; cases this
        | some ps =>
          rw [ho] at this
          exact ⟨ps, rfl, List.contains_iff_mem.mp this⟩
    · rw [hps] at hval
      simp only [List.all_eq_true, List.any_eq_true, beq_iff_eq] at hval
      exact hval n hn'
  · intro w
    refine ⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, w.virtual⟩, ?_⟩, ?_⟩, w.vis⟩, w.mutab⟩, w.rets⟩
    · by_cases h : E.baseFns c d = []
      · exact .inl h
      · right
        have := w.missing h
        exact Option.isSome_iff_exists.mp this
    · by_cases h : E.baseFns c d = []
      · exact .inr (w.nothing h)
      · left
        cases hb : E.baseFns c d with
        | nil => exact absurd hb h
        | cons _ _ => rfl
    · by_cases h : (E.baseFns c d).length < 2
      · exact .inl h
      · right
        intro f hf
        obtain ⟨ps, hps, hm⟩ := w.listed (by omega) f hf
        rw [hps]
        exact List.contains_iff_mem.mpr hm
    · cases ho : d.overrideList with
      | none => trivial
      | some ps =>
        simp only [List.all_eq_true, List.any_eq_true, beq_iff_eq]
        exact w.valid ps ho

/-- The override check of a unit. -/
def overridesB (E : Env) : Bool := E.contractNames.all fun c => (E.ownFns c).all (fnOverrideB E c)

theorem overridesB_iff {E : Env} : overridesB E = true ↔ OverridesOK E := by
  simp only [overridesB, List.all_eq_true, fnOverrideB_iff, OverridesOK]

/-! ## Required overrides, implementations -/

def mustOverrideB (E : Env) : Bool :=
  E.contractNames.all fun c => (E.inheritedFnsAll c).all fun f =>
    decide ((dedupScope ((E.bases c).filterMap fun B => E.inheritedVersion B f)).length < 2) ||
      E.declaresSig c f

theorem mustOverrideB_iff {E : Env} : mustOverrideB E = true ↔ MustOverride E := by
  simp only [mustOverrideB, List.all_eq_true, Bool.or_eq_true, decide_eq_true_eq, MustOverride]
  constructor
  · intro h c hc f hf h2
    rcases h c hc f hf with h' | h'
    · omega
    · exact h'
  · intro h c hc f hf
    by_cases h2 : (dedupScope ((E.bases c).filterMap fun B => E.inheritedVersion B f)).length < 2
    · exact .inl h2
    · exact .inr (h c hc f hf (by omega))

/-- 5424 for one declaration. -/
def virtualOK (E : Env) (d : Decl) : Bool :=
  !(d.kind == .function) || d.top || d.hasBody || E.scopeKind d.scope == Option.some .interface ||
    d.isVirtual E

theorem virtualOK_iff {E : Env} {d : Decl} : virtualOK E d = true ↔
    (d.kind = .function → d.top = false → d.hasBody = false →
      E.scopeKind d.scope ≠ Option.some .interface → d.isVirtual E = true) := by
  unfold virtualOK
  cases hk : d.kind == .function <;> cases ht : d.top <;> cases hb : d.hasBody <;>
    cases hi : E.scopeKind d.scope == Option.some .interface <;> cases hv : d.isVirtual E <;>
    simp_all

/-- 3656 for one contract. -/
def implC (E : Env) (c : String) : Bool :=
  !E.isContract c || E.isAbstract c ||
    (E.ownFns c ++ E.inheritedFnsAll c).all fun f =>
      match E.finalVersion c f with
      | Option.some g => g.hasBody
      | Option.none => true

theorem implC_iff {E : Env} {c : String} : implC E c = true ↔
    (E.isContract c = true → E.isAbstract c = false →
      ∀ f ∈ E.ownFns c ++ E.inheritedFnsAll c, ∀ g, E.finalVersion c f = Option.some g → g.hasBody = true) := by
  unfold implC
  have key : ((E.ownFns c ++ E.inheritedFnsAll c).all fun f =>
      match E.finalVersion c f with
      | Option.some g => g.hasBody
      | Option.none => true) = true ↔
      ∀ f ∈ E.ownFns c ++ E.inheritedFnsAll c, ∀ g, E.finalVersion c f = Option.some g → g.hasBody = true := by
    simp only [List.all_eq_true]
    apply forall_congr'; intro f; apply forall_congr'; intro _
    cases hf : E.finalVersion c f with
    | none => simp only [true_iff]; intro g h; cases h
    | some g => simp only [Option.some.injEq, forall_eq']
  cases hco : E.isContract c <;> cases hab : E.isAbstract c <;> simp only [Bool.not_true, Bool.not_false,
    Bool.true_or, Bool.false_or, Bool.or_true, true_iff, forall_const, key, false_implies,
    Bool.false_eq_true, imp_self, Bool.true_eq_false, implies_true, reduceCtorEq]

def implB (E : Env) : Bool := E.decls.all (virtualOK E) && E.contractNames.all (implC E)

theorem implB_iff {E : Env} : implB E = true ↔ ImplOK E := by
  simp only [implB, Bool.and_eq_true, List.all_eq_true, virtualOK_iff, implC_iff]
  constructor
  · intro ⟨hv, hi⟩
    exact ⟨hv, hi⟩
  · intro w
    exact ⟨w.virtual, w.implemented⟩

/-! ## Base constructors, modifiers, `using for` -/

def ctorArgsB (E : Env) (c : String) : Bool :=
  ((E.chain c).drop 1).all fun B =>
    (decide (E.ctorParams B = 0) || decide ((E.argsFor (E.chain c) B).length ≤ 1)) &&
    (E.isAbstract c || decide (E.ctorParams B = 0) || decide ((E.argsFor (E.chain c) B).length = 1)) &&
    (E.argsFor [c] B).all fun a => a.argCount == Option.some (E.ctorParams B)

theorem ctorArgsB_iff {E : Env} {c : String} : ctorArgsB E c = true ↔ CtorArgsOK E c := by
  simp only [ctorArgsB, List.all_eq_true, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq]
  constructor
  · intro h
    refine ⟨fun B hB hp => ?_, fun hab B hB hp => ?_, fun B hB a ha => (h B hB).2 a ha⟩
    · rcases (h B hB).1.1 with h' | h'
      · omega
      · exact h'
    · rcases (h B hB).1.2 with (h' | h') | h'
      · rw [hab] at h'; cases h'
      · omega
      · exact h'
  · intro w B hB
    refine ⟨⟨?_, ?_⟩, w.count B hB⟩
    · by_cases hp : E.ctorParams B = 0
      · exact .inl hp
      · exact .inr (w.once B hB (by omega))
    · cases hab : E.isAbstract c with
      | true => exact .inl (.inl rfl)
      | false =>
        by_cases hp : E.ctorParams B = 0
        · exact .inl (.inr hp)
        · exact .inr (w.given hab B hB (by omega))

/-- One modifier invocation resolves. -/
def modInvB (E : Env) (d : Decl) (inv : IdPath × Option (Syn .callArgs)) : Bool :=
  (match (E.lookupPath d.scope inv.1).filter (·.kind == .modifier) with
   | [m] =>
     match inv.2 with
     | Option.some a => a.argCount == Option.some m.modParams
     | Option.none => true
   | _ => false) ||
  (d.kind == .constructor &&
    match d.scope with
    | Option.some c => ((E.chain c).drop 1).contains inv.1.last
    | Option.none => false)

def modInvsB (E : Env) : Bool := E.decls.all fun d => d.modInvs.all (modInvB E d)

theorem modInvsB_iff {E : Env} : modInvsB E = true ↔ ModInvOK E := by
  unfold modInvsB ModInvOK modInvB
  simp only [List.all_eq_true, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq]
  apply forall_congr'; intro d; apply forall_congr'; intro _
  apply forall_congr'; intro inv; apply forall_congr'; intro _
  apply or_congr
  · constructor
    · intro h
      split at h
      · rename_i m hm
        refine ⟨m, hm, fun a ha => ?_⟩
        rw [ha] at h
        simpa only [beq_iff_eq] using h
      · cases h
    · intro ⟨m, hm, ha⟩
      rw [hm]
      cases h2 : inv.2 with
      | none => rfl
      | some a => simpa only [beq_iff_eq] using ha a h2
  · constructor
    · intro ⟨hk, hs⟩
      split at hs
      · rename_i c hc
        exact ⟨hk, c, hc, List.contains_iff_mem.mp hs⟩
      · cases hs
    · intro ⟨hk, c, hc, hm⟩
      refine ⟨hk, ?_⟩
      rw [hc]
      exact List.contains_iff_mem.mpr hm

def usingLibB (E : Env) (u : Syn .unit) : Bool :=
  u.usingLibs.all fun l =>
    match E.lookupPath Option.none l with
    | [d] => d.kind == .library
    | _ => false

theorem usingLibB_iff {E : Env} {u : Syn .unit} : usingLibB E u = true ↔ UsingLibOK E u := by
  unfold usingLibB UsingLibOK
  simp only [List.all_eq_true]
  apply forall_congr'; intro l; apply forall_congr'; intro _
  constructor
  · intro h
    split at h
    · rename_i d hd
      exact ⟨d, hd, by simpa only [beq_iff_eq] using h⟩
    · cases h
  · intro ⟨d, hd, hk⟩
    rw [hd]
    simp only [hk, beq_self_eq_true]

/-! ## The whole judgment -/

/-- **G14's inheritance check.** -/
def inheritanceB (r : Resolution) : Bool :=
  overridesB r.env && mustOverrideB r.env && implB r.env &&
    r.env.contractNames.all (fun c => !r.env.isContract c || ctorArgsB r.env c) &&
    modInvsB r.env && usingLibB r.env r.unit

/-- **The check decides `InheritanceOK`.** -/
theorem inheritance_iff {r : Resolution} : inheritanceB r = true ↔ InheritanceOK r := by
  simp only [inheritanceB, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    overridesB_iff, mustOverrideB_iff, implB_iff, modInvsB_iff, usingLibB_iff, ctorArgsB_iff]
  constructor
  · intro ⟨⟨⟨⟨⟨ho, hm⟩, hi⟩, hc⟩, hmi⟩, hu⟩
    refine ⟨ho, hm, hi, fun c hcn hco => ?_, hmi, hu⟩
    rcases hc c hcn with h | h
    · rw [hco] at h; cases h
    · exact h
  · intro w
    refine ⟨⟨⟨⟨⟨w.overrides, w.mustOverride⟩, w.impl⟩, fun c hcn => ?_⟩, w.modInvs⟩, w.usingLibs⟩
    cases hco : r.env.isContract c with
    | false => exact .inl rfl
    | true => exact .inr (w.ctorArgs c hcn hco)

/-! ## Callable identity -/

theorem clash_of_id {E : Env} {d d' : Decl} (h : CallableId E d d') (hn : d.name ≠ "") :
    d.clash E d' = true := by
  obtain ⟨hk, hk', hs, hnm, hp, _⟩ := h
  unfold Decl.sameParams at hp
  unfold Decl.clash
  split at hp
  · rename_i ps rs ps' rs' h1 h2
    simp only [hk, hk', hs, hnm, h1, h2, hp, beq_self_eq_true, Bool.and_self, Bool.true_and,
      Bool.or_true, if_true, bne_iff_ne, ne_eq, Bool.and_true]
    rw [← hnm]
    have : (d.name != "") = true := bne_iff_ne.mpr hn
    rw [this, Bool.or_true]
  · cases hp

/-- **Callable identity**: in a well-formed unit, two functions with one
identity (contract, name, parameter types) are one declaration. -/
theorem callable_unique {r : Resolution} (w : WellFormed r) {i j : Nat} {d d' : Decl}
    (hi : r.unit.decls[i]? = Option.some d) (hj : r.unit.decls[j]? = Option.some d')
    (hid : CallableId r.env d d') (hn : d.name ≠ "") : i = j := by
  have hp := List.pairwise_iff_getElem.mp w.noClash
  obtain ⟨hi', hdi⟩ := List.getElem?_eq_some_iff.mp hi
  obtain ⟨hj', hdj⟩ := List.getElem?_eq_some_iff.mp hj
  rcases Nat.lt_trichotomy i j with h | h | h
  · have := hp i j hi' hj' h
    rw [hdi, hdj, clash_of_id hid hn] at this
    cases this
  · exact h
  · have hid' : CallableId r.env d' d := by
      obtain ⟨hk, hk', hs, hnm, hp1, hp2⟩ := hid
      exact ⟨hk', hk, hs.symm, hnm.symm, hp2, hp1⟩
    have := hp j i hj' hi' h
    rw [hdi, hdj, clash_of_id hid' (by rw [← hid.2.2.2.1]; exact hn)] at this
    cases this

end Solidity.Frontend.Static
