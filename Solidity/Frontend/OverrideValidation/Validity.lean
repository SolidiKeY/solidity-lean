import Solidity.Frontend.OverrideValidation.OverrideLists

/-! Explicit validity obligations for the original declaration graph. No
claim of G13 body typing is made by this G14-only judgment. -/
namespace Solidity.Frontend.OverrideValidation
open Solidity.Source

/-- The descriptor names the same root constructor and collected declaration. -/
def Descriptor (d : Decl) : Prop :=
  d.top = d.scope.isNone ∧ d.node.ctor = d.kind.ctor ∧ ∃ head tail, d.node.collect d.scope = head :: tail ∧
    head.kind = d.kind ∧ head.top = d.top ∧ head.scope = d.scope ∧ head.name = d.name

def descriptorB (d : Decl) : Bool :=
  d.top == d.scope.isNone && d.node.ctor == d.kind.ctor &&
  match d.node.collect d.scope with
  | head :: _ => head.kind == d.kind && head.top == d.top && head.scope == d.scope && head.name == d.name
  | [] => false

/-- Contract, interface or library owning a declaration scope. -/
def topOwnerB (d : Decl) : Bool :=
  d.top && d.scope.isNone && (d.kind == .contract || d.kind == .interface || d.kind == .library)

/-- A getter must return at least one field. -/
def getterReturns (E : Env) (d : Decl) : Prop :=
  ∃ ps rs, signature E d = some (ps, rs) ∧ rs ≠ []

def getterReturnsB (E : Env) (d : Decl) : Bool :=
  match signature E d with
  | some (_, rs) => !rs.isEmpty
  | none => false

/-- Exact bytes-calldata to bytes-memory tuple, stated without a checker helper. -/
def BytesSignature (sig : Option (List STy × List STy)) : Prop :=
  sig = some ([.bytes .calldata], [.bytes .memory])

def bytesSignatureB (sig : Option (List STy × List STy)) : Bool :=
  match sig with
  | some ([.bytes .calldata], [.bytes .memory]) => true
  | _ => false

/-- The fallback grammar/type rule over the original Source node. -/
def FallbackShape (E : Env) (d : Decl) : Prop :=
  match d.kind, d.top, d.node with
  | .fallback, _, .fallback .fbNoParams _ _ _ _ _ _ => True
  | .fallback, _, .fallback (.fbParams ..) _ _ _ _ _ _ => BytesSignature (signature E d)
  | _, _, _ => False

def fallbackShapeB (E : Env) (d : Decl) : Bool :=
  match d.kind, d.top, d.node with
  | .fallback, _, .fallback .fbNoParams _ _ _ _ _ _ => true
  | .fallback, _, .fallback (.fbParams ..) _ _ _ _ _ _ => bytesSignatureB (signature E d)
  | _, _, _ => false

theorem bytesSignatureB_iff {sig : Option (List STy × List STy)} :
    bytesSignatureB sig = true ↔ BytesSignature sig := by
  unfold bytesSignatureB BytesSignature
  split
  · exact ⟨fun _ => rfl, fun _ => rfl⟩
  · constructor
    · intro h
      cases h
    · intro h
      subst sig
      contradiction

theorem fallbackShapeB_iff {E : Env} {d : Decl} : fallbackShapeB E d = true ↔ FallbackShape E d := by
  unfold fallbackShapeB FallbackShape
  split
  · exact ⟨fun _ => trivial, fun _ => rfl⟩
  · exact bytesSignatureB_iff
  · constructor
    · intro h
      cases h
    · intro h
      exact h.elim

/-- Primitive Source-attribute obligations supplement the existing placement
predicate. In particular, G14 does not accept internal-payable functions,
private/library virtual declarations, or bodyless non-virtual callables. -/
structure AttributesOK (E : Env) (d : Decl) : Prop where
  placement : d.placementOK E = true
  signature : (family d).isSome = true → (signature E d).isSome = true
  bodyVirtual : (family d).isSome = true → implemented d = false → Virtual E d
  virtualPrivate : writtenVirtual d = true → visibility d ≠ some .priv
  virtualLibrary : writtenVirtual d = true → E.scopeKind d.scope ≠ some .library
  free : d.top = true → (family d).isSome = true → writtenVirtual d = false ∧ overridePaths d = none
  payable : family d = some .function → mutability d = some .payable →
    visibility d = some .pub ∨ visibility d = some .external
  specialVis : family d = some .fallback ∨ family d = some .receive → visibility d = some .external
  specialMut : family d = some .fallback → mutability d = none ∨ mutability d = some .payable
  receiveMut : family d = some .receive → mutability d = some .payable
  interfaceBody : functionLikeB d = true → E.scopeKind d.scope = some .interface → implemented d = false
  getter : family d = some .getter → getterReturns E d
  fallbackShape : family d = some .fallback → FallbackShape E d
  libraryOverrides : E.scopeKind d.scope = some .library → overridePaths d = none
  stateVariableOverride : d.kind = .stateVar → (overridePaths d).isSome = true → family d = some .getter

def attributesOKB (E : Env) (d : Decl) : Bool :=
  d.placementOK E && (!(family d).isSome || (signature E d).isSome) &&
  (!(family d).isSome || implemented d || virtualB E d) &&
  (!writtenVirtual d || visibility d != some .priv) &&
  (!writtenVirtual d || E.scopeKind d.scope != some .library) &&
  (!d.top || !(family d).isSome || (!writtenVirtual d && (overridePaths d).isNone)) &&
  (family d != some .function || mutability d != some .payable ||
    visibility d == some .pub || visibility d == some .external) &&
  ((family d != some .fallback && family d != some .receive) || visibility d == some .external) &&
  (family d != some .fallback || mutability d == none || mutability d == some .payable) &&
  (family d != some .receive || mutability d == some .payable) &&
  (!functionLikeB d || E.scopeKind d.scope != some .interface || !implemented d) &&
  (family d != some .getter || getterReturnsB E d) &&
  (family d != some .fallback || fallbackShapeB E d) &&
  (E.scopeKind d.scope != some .library || (overridePaths d).isNone) &&
  (d.kind != .stateVar || (overridePaths d).isNone || family d == some .getter)

def ScopeKnown (E : Env) (d : Node E) : Prop :=
  ∀ scope, d.decl.scope = some scope →
    ∃ owner : Node E, topOwnerB owner.decl = true ∧ owner.decl.name = scope

def scopeKnownB (E : Env) (d : Node E) : Bool :=
  match d.decl.scope with
  | none => true
  | some scope => (nodes E).any fun owner => topOwnerB owner.decl && owner.decl.name == scope

/-- Graph validity uses original positions, not nominal-key quotients. -/
structure GraphValid (E : Env) : Prop where
  descriptors : ∀ d : Node E, Descriptor d.decl
  attributes : ∀ d : Node E, AttributesOK E d.decl
  roots : ∀ d : Node E, (d.decl.kind = .contract ∨ d.decl.kind = .interface ∨ d.decl.kind = .library) → topOwnerB d.decl = true
  owners : ∀ d : Node E, ∀ scope, d.decl.scope = some scope →
    ∃ owner : Node E, topOwnerB owner.decl = true ∧ owner.decl.name = scope
  uniqueOwners : ∀ a b : Node E, topOwnerB a.decl = true → topOwnerB b.decl = true → a.decl.name = b.decl.name → a = b
  noClashes : ∀ a b : Node E, a ≠ b → a.decl.clash E b.decl = false
  uniqueSlots : ∀ c d f : Node E, Own E c d → Own E c f → SameSlot E d.decl f.decl → d = f
  basePaths : ∀ c : Node E, contractB c.decl = true → ∀ p ∈ basePaths c.decl,
    ∃ b, Refers E p b ∧ b.val < c.val ∧ (c.decl.kind = .interface → b.decl.kind = .interface)
  earlier : ∀ a b : Node E, BaseEdge E a b → b.val < a.val
  linearizes : ∀ c : Node E, contractB c.decl = true → (E.linearize c.decl.name).isSome = true

def graphValidB (E : Env) : Bool :=
  (nodes E).all (fun d => descriptorB d.decl && attributesOKB E d.decl) &&
  (nodes E).all (fun d =>
    (!(d.decl.kind == .contract || d.decl.kind == .interface || d.decl.kind == .library) || topOwnerB d.decl) &&
    scopeKnownB E d) &&
  (nodes E).all (fun a => (nodes E).all fun b =>
    (!topOwnerB a.decl || !topOwnerB b.decl || a.decl.name != b.decl.name || a == b) &&
    (a == b || !a.decl.clash E b.decl) &&
    (!baseEdgeB E a b || decide (b.val < a.val))) &&
  (nodes E).all (fun c => (nodes E).all fun d => (nodes E).all fun f =>
    !ownB E c d || !ownB E c f || !sameSlotB E d.decl f.decl || d == f) &&
  (nodes E).all (fun c => !contractB c.decl ||
    ((basePaths c.decl).all (fun p => (nodes E).any fun b => refersB E p b && decide (b.val < c.val) &&
      (c.decl.kind != .interface || b.decl.kind == .interface)) &&
      (E.linearize c.decl.name).isSome))

theorem descriptorB_iff {d : Decl} : descriptorB d = true ↔ Descriptor d := by
  unfold descriptorB Descriptor
  cases h : d.node.collect d.scope with
  | nil => simp only [Bool.and_eq_true, Bool.false_eq_true, and_false, reduceCtorEq, false_and, exists_false]
  | cons head tail =>
    simp only [Bool.and_eq_true, beq_iff_eq, List.cons.injEq, exists_and_left,
      exists_eq_left', and_assoc]

theorem getterReturnsB_iff {E : Env} {d : Decl} : getterReturnsB E d = true ↔ getterReturns E d := by
  unfold getterReturnsB getterReturns
  cases h : signature E d with
  | none => simp only [Bool.false_eq_true, reduceCtorEq, false_and, exists_false]
  | some pair =>
    obtain ⟨ps, rs⟩ := pair
    simp only [Bool.not_eq_true', List.isEmpty_eq_false_iff, Option.some.injEq,
      Prod.mk.injEq, and_assoc, exists_and_left, exists_eq_left']

theorem attributesOKB_iff {E : Env} {d : Decl} : attributesOKB E d = true ↔ AttributesOK E d := by
  simp only [attributesOKB, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    bne_iff_ne, beq_iff_eq, Option.isNone_iff_eq_none, virtualB_iff, getterReturnsB_iff, fallbackShapeB_iff]
  constructor
  · intro h
    rcases h with ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hp, hs⟩, hv⟩, hpr⟩, hl⟩, hf⟩, hpay⟩, hvis⟩, hmut⟩, hr⟩, hi⟩, hg⟩, hfb⟩, hlib⟩, hstate⟩
    constructor <;> grind
  · intro h
    have := h.placement
    have := h.signature
    have := h.bodyVirtual
    have := h.virtualPrivate
    have := h.virtualLibrary
    have := h.free
    have := h.payable
    have := h.specialVis
    have := h.specialMut
    have := h.receiveMut
    have := h.interfaceBody
    have := h.getter
    have := h.fallbackShape
    have := h.libraryOverrides
    have := h.stateVariableOverride
    have hstate : d.kind = .stateVar → overridePaths d ≠ none → family d = some .getter :=
      fun hk ho => h.stateVariableOverride hk (Option.isSome_iff_ne_none.mpr ho)
    repeat' apply And.intro
    all_goals grind

theorem scopeKnownB_iff {E : Env} {d : Node E} : scopeKnownB E d = true ↔ ScopeKnown E d := by
  unfold scopeKnownB ScopeKnown
  cases h : d.decl.scope <;>
    simp only [reduceCtorEq, false_implies, implies_true,
      Option.some.injEq, forall_eq', any_nodes_iff, Bool.and_eq_true, beq_iff_eq]

theorem graphValidB_iff {E : Env} : graphValidB E = true ↔ GraphValid E := by
  simp only [graphValidB, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    bne_iff_ne, beq_iff_eq, Bool.eq_false_iff, ne_eq, any_nodes_iff, descriptorB_iff, attributesOKB_iff,
    ownB_iff, sameSlotB_iff, baseEdgeB_iff, refersB_iff, decide_eq_true_eq,
    List.all_eq_true, mem_nodes, true_implies, scopeKnownB_iff]
  constructor
  · rintro ⟨⟨⟨⟨hda, hro⟩, hp⟩, hs⟩, hb⟩
    refine ⟨fun d => (hda d).1, fun d => (hda d).2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro d hd
      have hh := (hro d).1
      grind
    · intro d scope hscope
      exact (hro d).2 scope hscope
    · intro a b ha hb hn
      have hh := (hp a b).1.1
      grind
    · intro a b hne
      have hh := (hp a b).1.2
      grind
    · intro c d f hcd hcf hdf
      have hh := hs c d f
      grind
    · intro c hc p hpm
      have hh := hb c
      rcases hh with hh | hh
      · exact (hh hc).elim
      · obtain ⟨b, ⟨hbr, hlt⟩, hkind⟩ := hh.1 p hpm
        exact ⟨b, hbr, hlt, fun hi => by grind⟩
    · intro a b he
      have hh := (hp a b).2
      grind
    · intro c hc
      have hh := hb c
      grind
  · intro h
    refine ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩
    · intro d
      exact ⟨h.descriptors d, h.attributes d⟩
    · intro d
      refine ⟨?_, h.owners d⟩
      have hh := h.roots d
      grind
    · intro a b
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · have hh := h.uniqueOwners a b
        grind
      · have hh := h.noClashes a b
        grind
      · have hh := h.earlier a b
        grind
    · intro c d f
      have hh := h.uniqueSlots c d f
      grind
    · intro c
      by_cases hc : contractB c.decl = true
      · right
        refine ⟨?_, h.linearizes c hc⟩
        intro p hp
        obtain ⟨b, hbr, hlt, hk⟩ := h.basePaths c hc p hp
        exact ⟨b, ⟨hbr, hlt⟩, by grind⟩
      · exact .inl hc

/-- Every base edge strictly decreases its original declaration position. -/
theorem valid_no_self_base {E : Env} (h : GraphValid E) (d : Node E) : ¬ BaseEdge E d d :=
  fun he => Nat.lt_irrefl d.val (h.earlier d d he)

/-- Valid owners have unique original declaration identities. -/
theorem valid_owner_identity {E : Env} (h : GraphValid E) {a b : Node E}
    (ha : topOwnerB a.decl = true) (hb : topOwnerB b.decl = true)
    (hn : a.decl.name = b.decl.name) : a = b := h.uniqueOwners a b ha hb hn

end Solidity.Frontend.OverrideValidation
