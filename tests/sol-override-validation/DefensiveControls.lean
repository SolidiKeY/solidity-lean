import Solidity.Frontend.OverrideValidation.Memoized

/-! Direct typed controls for defensive helper arms that cannot be obtained
from a successfully checked parser result. These do not expand G14 into G13. -/
namespace Solidity.Frontend.OverrideValidation.DefensiveControls
open Solidity.Source

def body : Syn (.opt (.block .body)) := .some (.block .nil)
def functionNode : Syn (.part false) :=
  .function (.ident "f") .nil (some .pub) none .nil false none .nil body

def contractNode : Syn .top := .contract false "C" .none .nil (.cons functionNode .nil)
def contractDecl : Decl := ⟨.contract, "C", none, true, contractNode⟩
def functionDecl : Decl := ⟨.function, "f", some "C", false, functionNode⟩
def E : Env := ⟨[contractDecl, functionDecl]⟩
def c : Node E := ⟨0, by decide⟩
def f : Node E := ⟨1, by decide⟩

theorem missing_signature :
    paramsB E c.decl f.decl = false ∧
    signatureConditionB E c.decl f.decl (fun _ _ _ _ => true) = false ∧
    getterReturnsB E c.decl = false ∧
    paramsB E f.decl c.decl = false ∧
    signatureConditionB E f.decl c.decl (fun _ _ _ _ => true) = false := by decide

theorem fallback_other_constructor : fallbackShapeB E f.decl = false := rfl

theorem bytes_refusals : bytesSignatureB none = false ∧
    bytesSignatureB (some ([], [])) = false := by decide

theorem classifier_controls : contractB c.decl = true ∧ contractB f.decl = false ∧
    topOwnerB c.decl = true ∧ topOwnerB f.decl = false ∧
    ordinaryB f.decl = true ∧ ordinaryB c.decl = false := by decide

theorem absent_reference : refersB E ⟨"Absent", []⟩ c = false := by decide

theorem ownership_controls : ownB E c f = true ∧ ownB E f c = false := by decide

def wrongDescriptor : Decl := ⟨.function, "wrong", some "C", false, functionNode⟩
theorem descriptor_refusal : descriptorB wrongDescriptor = false := by decide

def wrongTop : Decl := ⟨.contract, "C", none, false, contractNode⟩
theorem root_flag_refusal : descriptorB wrongTop = false ∧ topOwnerB wrongTop = false := by decide

def orphan : Env := ⟨[⟨.function, "f", some "Ghost", false, functionNode⟩]⟩
def orphanRef : Node orphan := ⟨0, by decide⟩
theorem unknown_owner_refusal : scopeKnownB orphan orphanRef = false := by decide

def duplicateOwners : Env := ⟨[contractDecl, contractDecl]⟩
def ownerA : Node duplicateOwners := ⟨0, by decide⟩
def ownerB : Node duplicateOwners := ⟨1, by decide⟩

theorem duplicate_owners_rejected : ¬ GraphValid duplicateOwners := by
  intro h
  have he : ownerA = ownerB := h.uniqueOwners ownerA ownerB (by decide) (by decide) rfl
  exact (by decide : ownerA ≠ ownerB) he

def duplicateSlots : Env := ⟨[contractDecl, functionDecl, functionDecl]⟩
def slotOwner : Node duplicateSlots := ⟨0, by decide⟩
def slotA : Node duplicateSlots := ⟨1, by decide⟩
def slotB : Node duplicateSlots := ⟨2, by decide⟩

theorem duplicate_slots_rejected : ¬ GraphValid duplicateSlots := by
  intro h
  exact (by decide : slotA ≠ slotB) (h.uniqueSlots slotOwner slotA slotB
    (ownB_iff.mp (by decide)) (ownB_iff.mp (by decide)) (sameSlotB_iff.mp (by decide)))

theorem duplicate_clash : slotA.decl.clash duplicateSlots slotB.decl = true := by decide

def privateNode : Syn (.part false) :=
  .function (.ident "f") .nil (some .priv) none .nil false none .nil body

def privateEnv : Env := (Syn.unit (.cons (.contract false "P" .none .nil (.cons privateNode .nil))
  (.cons (.contract false "D" .none (.cons (.inherit ⟨"P", []⟩ .none) .nil) .nil) .nil))).env
def privateOwner : Node privateEnv := ⟨0, by decide⟩
def privateFn : Node privateEnv := ⟨1, by decide⟩

theorem private_frontier_distinction :
    ownMatchingB privateEnv privateFn privateOwner privateFn = false ∧
    overrideOwnB privateEnv privateFn privateOwner privateFn = true := by decide

def privateChild : Node privateEnv := ⟨2, by decide⟩
theorem selection_private_controls :
    exposesB privateEnv privateOwner privateFn "P" privateFn = true ∧
    exposesB privateEnv privateChild privateFn "P" privateFn = false := by decide

def abstractNode : Syn (.part false) :=
  .function (.ident "f") .nil (some .pub) none .nil true none .nil .none
def missingImpl : Env :=
  (Syn.unit (.cons (.contract false "Missing" .none .nil (.cons abstractNode .nil)) .nil)).env
def missingOwner : Node missingImpl := ⟨0, by decide⟩
def missingFn : Node missingImpl := ⟨1, by decide⟩
theorem unimplemented_concrete : implementationB missingImpl missingOwner missingFn = false := by decide

def freeNode (virtual : Bool) : Syn (.part true) :=
  .function (.ident "free") .nil none none .nil virtual none .nil body
def freeEnv (virtual : Bool) : Env := (Syn.unit (.cons (.topPart (freeNode virtual)) .nil)).env

theorem free_accepted : OverrideGraphOK (freeEnv false) := by
  apply validateB_iff.mp
  unfold validateB
  have he : extractionB (freeEnv false) = true := extractionB_iff.mpr rfl
  rw [he]
  decide

def freeVirtualRef : Node (freeEnv true) := ⟨0, by decide⟩
theorem free_virtual_rejected : ¬ OverrideGraphOK (freeEnv true) := by
  intro h
  have hv := (h.valid.attributes freeVirtualRef).free rfl rfl
  change true = false ∧ _ at hv
  cases hv.1

/-- Pure runtime defensive control for an invalid cyclic C3 input: no chosen
scope contains the requested declaration. No accepted-input claim is made. -/
def cyclic : Env := (Syn.unit
  (.cons (.contract false "A" .none (.cons (.inherit ⟨"B", []⟩ .none) .nil) .nil)
  (.cons (.contract false "B" .none (.cons (.inherit ⟨"A", []⟩ .none) .nil)
    (.cons functionNode .nil)) .nil))).env
def cyclicA : Node cyclic := ⟨0, by decide⟩
def cyclicFn : Node cyclic := ⟨2, by decide⟩
theorem cyclic_choice_none : choose cyclic cyclicA cyclicFn = none := by decide

/-- info: false -/
#guard_msgs in
#eval implementationB cyclic cyclicA cyclicFn

def emptyCollection : Decl := ⟨.function, "using", some "C", false,
  .usingPart (.usingPath ⟨"L", []⟩ .none false)⟩
def wrongConstructor : Decl := ⟨.function, "m", some "C", false, .modifier "m" .none false none body⟩

theorem descriptor_defenses :
    emptyCollection.node.collect emptyCollection.scope = [] ∧
    descriptorB emptyCollection = false ∧ descriptorB wrongConstructor = false := by decide

def missingVisibility : Decl := ⟨.function, "f", some "C", false,
  .function (.ident "f") .nil none none .nil false none .nil body⟩
def unknownSignature : Decl := ⟨.function, "f", some "C", false,
  .function (.ident "f") (.cons (.param (.userType ⟨"Missing", []⟩) none none) .nil)
    (some .pub) none .nil false none .nil body⟩
def bodyless : Decl := ⟨.function, "f", some "C", false,
  .function (.ident "f") .nil (some .pub) none .nil false none .nil .none⟩
def notExternal : Decl := ⟨.fallback, "", some "C", false,
  .fallback .fbNoParams false none .nil false none body⟩
def interfaceEnv : Env := (Syn.unit (.cons (.interface "I" .nil .nil) .nil)).env
def interfaceBody : Decl := ⟨.fallback, "", some "I", false,
  .fallback .fbNoParams true none .nil false none body⟩
def libraryEnv : Env := (Syn.unit (.cons (.library "L" .nil) .nil)).env
def libraryOverride : Decl := ⟨.modifier, "m", some "L", false,
  .modifier "m" .none false (some [])
    (.some (.block (.cons (.stmtItem (.simpleStmt (.exprStmt (.ident "_")))) .nil)))⟩

theorem attribute_defenses :
    missingVisibility.placementOK E = false ∧
    signature E unknownSignature = none ∧
    attributesOKB E missingVisibility = false ∧
    attributesOKB E unknownSignature = false ∧
    attributesOKB E bodyless = false ∧
    attributesOKB E notExternal = false ∧
    attributesOKB interfaceEnv interfaceBody = false ∧
    attributesOKB libraryEnv libraryOverride = false := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

def missingBase : Env := (Syn.unit (.cons
  (.contract false "Child" .none (.cons (.inherit ⟨"Absent", []⟩ .none) .nil) .nil) .nil)).env
def missingBaseOwner : Node missingBase := ⟨0, by decide⟩

theorem missing_base_rejected : ¬ GraphValid missingBase := by
  intro h
  obtain ⟨b, hb, _, _⟩ := h.basePaths missingBaseOwner (by decide) ⟨"Absent", []⟩ (by decide)
  have hf : refersB missingBase ⟨"Absent", []⟩ b = false := by
    have he : b = missingBaseOwner := Fin.fin_one_eq_zero b
    subst b
    decide
  have ht : refersB missingBase ⟨"Absent", []⟩ b = true := refersB_iff.mpr hb
  rw [hf] at ht
  cases ht

theorem projection_defaults : family c.decl = none ∧ overridePaths c.decl = none ∧
    writtenVirtual c.decl = false ∧ visibility c.decl = none ∧ mutability c.decl = none ∧
    implemented c.decl = false ∧ signature E c.decl = none := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

def receiveFlags : Decl := ⟨.receive, "", some "C", false,
  .receive false false .nil false none body⟩
theorem receive_flag_defenses : visibility receiveFlags = none ∧ mutability receiveFlags = none ∧
    attributesOKB E receiveFlags = false := by decide

end Solidity.Frontend.OverrideValidation.DefensiveControls


/-- info: 'Solidity.Frontend.OverrideValidation.DefensiveControls.missing_signature' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Frontend.OverrideValidation.DefensiveControls.missing_signature

/-- info: 'Solidity.Frontend.OverrideValidation.DefensiveControls.fallback_other_constructor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Frontend.OverrideValidation.DefensiveControls.fallback_other_constructor

/-- info: 'Solidity.Frontend.OverrideValidation.DefensiveControls.bytes_refusals' does not depend on any axioms -/
#guard_msgs in
#print axioms Solidity.Frontend.OverrideValidation.DefensiveControls.bytes_refusals

/-- info: 'Solidity.Frontend.OverrideValidation.DefensiveControls.classifier_controls' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Solidity.Frontend.OverrideValidation.DefensiveControls.classifier_controls

/-- info: 'Solidity.Frontend.OverrideValidation.DefensiveControls.absent_reference' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Solidity.Frontend.OverrideValidation.DefensiveControls.absent_reference

/-- info: 'Solidity.Frontend.OverrideValidation.DefensiveControls.ownership_controls' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Solidity.Frontend.OverrideValidation.DefensiveControls.ownership_controls

/-- info: 'Solidity.Frontend.OverrideValidation.DefensiveControls.descriptor_refusal' does not depend on any axioms -/
#guard_msgs in
#print axioms Solidity.Frontend.OverrideValidation.DefensiveControls.descriptor_refusal

/-- info: 'Solidity.Frontend.OverrideValidation.DefensiveControls.root_flag_refusal' does not depend on any axioms -/
#guard_msgs in
#print axioms Solidity.Frontend.OverrideValidation.DefensiveControls.root_flag_refusal

/-- info: 'Solidity.Frontend.OverrideValidation.DefensiveControls.unknown_owner_refusal' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Solidity.Frontend.OverrideValidation.DefensiveControls.unknown_owner_refusal

/-- info: 'Solidity.Frontend.OverrideValidation.DefensiveControls.duplicate_owners_rejected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Frontend.OverrideValidation.DefensiveControls.duplicate_owners_rejected

/-- info: 'Solidity.Frontend.OverrideValidation.DefensiveControls.duplicate_slots_rejected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Frontend.OverrideValidation.DefensiveControls.duplicate_slots_rejected

/-- info: 'Solidity.Frontend.OverrideValidation.DefensiveControls.duplicate_clash' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Frontend.OverrideValidation.DefensiveControls.duplicate_clash

/-- info: 'Solidity.Frontend.OverrideValidation.DefensiveControls.private_frontier_distinction' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Frontend.OverrideValidation.DefensiveControls.private_frontier_distinction

/-- info: 'Solidity.Frontend.OverrideValidation.DefensiveControls.selection_private_controls' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Frontend.OverrideValidation.DefensiveControls.selection_private_controls

/-- info: 'Solidity.Frontend.OverrideValidation.DefensiveControls.unimplemented_concrete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Frontend.OverrideValidation.DefensiveControls.unimplemented_concrete

/-- info: 'Solidity.Frontend.OverrideValidation.DefensiveControls.free_accepted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Frontend.OverrideValidation.DefensiveControls.free_accepted

/-- info: 'Solidity.Frontend.OverrideValidation.DefensiveControls.free_virtual_rejected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Frontend.OverrideValidation.DefensiveControls.free_virtual_rejected

/-- info: 'Solidity.Frontend.OverrideValidation.DefensiveControls.cyclic_choice_none' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Frontend.OverrideValidation.DefensiveControls.cyclic_choice_none

/-- info: 'Solidity.Frontend.OverrideValidation.DefensiveControls.descriptor_defenses' does not depend on any axioms -/
#guard_msgs in
#print axioms Solidity.Frontend.OverrideValidation.DefensiveControls.descriptor_defenses

/-- info: 'Solidity.Frontend.OverrideValidation.DefensiveControls.attribute_defenses' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Frontend.OverrideValidation.DefensiveControls.attribute_defenses

/-- info: 'Solidity.Frontend.OverrideValidation.DefensiveControls.missing_base_rejected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Frontend.OverrideValidation.DefensiveControls.missing_base_rejected

/-- info: 'Solidity.Frontend.OverrideValidation.DefensiveControls.projection_defaults' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Frontend.OverrideValidation.DefensiveControls.projection_defaults

/-- info: 'Solidity.Frontend.OverrideValidation.DefensiveControls.receive_flag_defenses' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Frontend.OverrideValidation.DefensiveControls.receive_flag_defenses
