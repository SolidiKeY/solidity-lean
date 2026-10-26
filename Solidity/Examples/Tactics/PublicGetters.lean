import Solidity.Frontend.Testing
import Solidity.Tools.Run
import Solidity.Syntax.Contract
import Solidity.Semantics.RunFuel

/-!
# Public getters through the ordinary self-call calculus

Getter aliases keep source selectors while storage reads keep their roots.
Mapping keys and ordinary array indexes become typed parameters; terminal
structs retain primitive fields and omit mapping/ordinary array fields.
Reference-valued getters are refused explicitly rather than shortened.
-/

namespace Solidity.Examples.Tactics.PublicGetters
open Frontend
open scoped Scoped

solc_import "../../../tests/solc/PublicGetters.ast.json" hash 0x968ad03a36798cc3
  as Imported.PublicGetters testing
solc_scoped_problems Imported.PublicGetters decl

/-- `count = 37; assert(this.count() == 37);`: a getter reads the storage root. -/
theorem scalar : ⊢ Imported.PublicGetters.scalar.problem := by
  sol_prove

/-- An interface function overridden by a public variable selects that getter. -/
theorem interfaceOverride : ⊢ Imported.PublicGetters.viaInterface.problem := by
  sol_prove

/-- Signed, Boolean, address, fixed-byte and expression-backed getters retain their values. -/
theorem primitives : ⊢ Imported.PublicGetters.primitives.problem := by
  sol_prove

/-- Getter selectors/addresses also work when ABI encoding consumes the function value. -/
theorem abiIdentity : ⊢ Imported.PublicGetters.identity.problem := by
  sol_prove

/-- Named arguments preserve the declared mapping-key order and widths. -/
theorem nestedMapping : ⊢ Imported.PublicGetters.nestedMapping.problem := by
  sol_prove

/-- Boolean keys remain two distinct storage selections. -/
theorem booleanKeys : ⊢ Imported.PublicGetters.boolKeys.problem := by
  sol_prove

/-- Dynamic/fixed/nested array getters take indexes, not the array as a result. -/
theorem arrays : ⊢ Imported.PublicGetters.arrays.problem := by
  sol_prove

/-- A struct getter returns its value fields in source order through `try`. -/
theorem structOmissions : ⊢ Imported.PublicGetters.structFields.problem := by
  sol_prove

/-- An out-of-bounds getter keeps empty revert data, unlike an ordinary array read. -/
theorem bounds : ⊢ Imported.PublicGetters.fixedBounds.problem := by
  sol_prove

/-- A constant getter selector still evaluates a receiver whose array read can panic. -/
theorem selectorReceiverBounds : ⊢ Imported.PublicGetters.selectorBounds.problem := by
  sol_prove
  all_goals (sol_leaf; sol_close)

/-- Inherited getters and ordinary functions retain their source ABI identities. -/
theorem inherited : ⊢ Imported.PublicGetters.inheritedGetters.problem := by
  sol_prove

private def sourceMember (name : String) : Option (String × FunDecl) :=
  Imported.PublicGetters.funs.find? fun (_, f) => f.sourceDecl.any (·.name == name)

/-- The model alias must avoid the actual source function `solcGetter27`. -/
example : (sourceMember "count").map (·.1) = some "solcGetter27_" := by
  decide +kernel

/-- A getter has no internal function tag, even though a direct generated call exists. -/
example : (fnTag Imported.PublicGetters "solcGetter27_").isOk = false := by
  decide +kernel

/-- A synthesized key parameter cannot shadow a storage root of its default name. -/
example : ((sourceMember "items").map fun (_, f) => f.params.map (·.1)) =
    some ["solcGetterArg54_0_"] := by
  decide +kernel

/-- ABI identity never hashes the synthesized model alias. -/
example : fnSelector? Imported.PublicGetters "solcGetter27_" =
    some 0x06661abd := by
  decide +kernel

/-- A renamed inherited function uses solc's selector, not a hash of its alias. -/
example : ((sourceMember "inherited").bind fun (name, _) =>
    fnSelector? Imported.PublicGetters name) = some 0x810c8f31 := by
  decide +kernel

/-- Inherited model aliases retain the source's unerased parameter signature. -/
example : ((sourceMember "inherited").bind fun (name, _) =>
    fnSignature? Imported.PublicGetters name) = some "inherited(uint8)" := by
  decide +kernel

solc_import "../../../tests/solc/PublicGetters.ast.json" hash 0x968ad03a36798cc3
  as Imported.GetterReferences testing

/- Bytes/string are returned, so lack of reference ABI returns rejects the whole getter. -/
#guard ["rejectedBytes", "rejectedMixed"].all fun name =>
  (Imported.GetterReferences.report.find? (·.name == name)).any (·.status == .unsupported)

solc_import "../../../tests/solc/PublicGetters.ast.json" hash 0x968ad03a36798cc3
  as Imported.GetterCtorCollision testing
solc_scoped_problems Imported.GetterCtorCollision decl

/-- The base's `return` ends its body; a colliding source function never runs instead. -/
theorem constructorFreshness : ⊢ Imported.GetterCtorCollision.constructor.problem := by
  sol_prove

/-- The emitted constructor helper is fresh and has no function value or selector. -/
example : (fnTag Imported.GetterCtorCollision "solcCtorBody721_").isOk = false ∧
    fnSelector? Imported.GetterCtorCollision "solcCtorBody721_" = none := by
  decide +kernel

solc_import "../../../tests/solc/PublicGetters.ast.json" hash 0x968ad03a36798cc3
  as Imported.GetterCtorStructAlias renaming GetterBox => solcCtorBody721 testing
solc_scoped_problems Imported.GetterCtorStructAlias decl

/-- A renamed struct constructor cannot be hijacked by a generated base-body helper. -/
theorem constructorTypeFreshness : ⊢ Imported.GetterCtorStructAlias.constructor.problem := by
  sol_prove

/-- Source visibility roles are distinct, independently of selector availability. -/
example : SourceFunction.internalValue { callable := .abi .externalFn .selected none } = false ∧
    SourceFunction.externalEntry { callable := .abi .publicFn .retained none } = false := by
  decide +kernel

solc_import "../../../tests/solc/PublicGetters.ast.json" hash 0x968ad03a36798cc3
  as Imported.GetterFunctionSlot testing
solc_scoped_problems Imported.GetterFunctionSlot decl

/-- Metadata access to a getter is distinct from a stored function value's selector. -/
theorem storedGetterSelector : ⊢ Imported.GetterFunctionSlot.getterSelector.problem := by
  sol_prove

private def slotDeclaration : Lean.Json := Lean.Json.mkObj [
  ("nodeType", .str "VariableDeclaration"), ("id", Lean.toJson (1 : Int)),
  ("stateVariable", .bool true), ("visibility", .str "public"),
  ("functionSelector", .str "e582dd31")]

private def slotRead : Lean.Json := Lean.Json.mkObj [
  ("nodeType", .str "Identifier"), ("referencedDeclaration", Lean.toJson (1 : Int))]

/- A stored function slot has no declaration-selector rewrite. JSON parser
operations are executable evidence, separate from the calculus proofs. -/
#guard !(isPublicGetterMember slotDeclaration slotRead)
#guard (declarationMetadata [slotDeclaration] slotRead "selector").toOption == some none

private def malformedFunction : Lean.Json := Lean.Json.mkObj [
  ("nodeType", .str "FunctionDefinition"), ("name", .str "bad"),
  ("kind", .str "function"), ("visibility", .str "external"),
  ("functionSelector", Lean.toJson (0 : Nat))]

/-- A present selector of the wrong JSON type cannot become a signature fallback. -/
example : (sourceFunction [] malformedFunction .selected false).isOk = false := by
  decide +kernel


/- The ABI's full-width elementary spellings remain canonical (including
synthetic uint256 getter indexes, which need not carry typeDescriptions). -/
#guard sourceAbiType [] 1 (Lean.Json.mkObj
  [("nodeType", .str "ElementaryTypeName"), ("name", .str "uint256")]) == some "uint256"
#guard sourceAbiType [] 1 (Lean.Json.mkObj
  [("nodeType", .str "ElementaryTypeName"), ("name", .str "int256")]) == some "int256"

/-- Narrow self returns use a resolved typed frame, preserve ABI markers, and
check their result rather than accepting or truncating arbitrary words. -/
def NarrowSelf : Contract := contract!{
  function unsignedValue() returns (uint8 r) { r = 7; }
  function signedValue() returns (int16 r) { r = -5; }
  function byteValue() returns (bytes2 r) { r = 0x1234; }
  function wideValue() returns (uint r) { r = 256; }
  function values() returns (bool ok) {
    uint8 x = this.unsignedValue();
    int16 y = this.signedValue();
    bytes2 z = this.byteValue();
    bytes memory encoded = abi.encodePacked(z);
    ok = x == 7 && y == -5 && z == bytes2(0x1234) && encoded.length == 2 &&
      uint8(encoded[0]) == 0x12 && uint8(encoded[1]) == 0x34;
  }
  function widenedNumeric() returns (bool ok) {
    try this.unsignedValue() returns (uint16 value) { ok = value == 7; }
    catch { ok = false; }
  }
  function explicitStringPrefix() returns (bool ok) {
    string memory text = "ab";
    bytes4 value = bytes4(bytes(text));
    ok = value == bytes4(0x61620000);
  }
  function lazyStringPrefix(bool take) returns (bool ok) {
    string memory text = "ab";
    ok = !take || bytes4(bytes(text)) == bytes4(0x61620000);
  }
  function failedDecode() returns (bool ok) {
    try this.wideValue() returns (uint8 x) { ok = x == 0; ok = true; }
    catch { ok = true; }
  }
}

private def narrowSelfState : State NarrowSelf [] :=
  { State.init NarrowSelf with tx := { selfAddress := ⟨7, by decide⟩ } }

/-- info: ok
returns true -/
#guard_msgs in #run NarrowSelf.values() from narrowSelfState

/- Native DSL adversarial decoder test: Solidity rejects this mismatched
try-return declaration. A failed caller-side decode is an empty revert outside
this try's catch; 256 cannot become a successful uint8 result. -/
/-- info: revert -/
#guard_msgs in #run NarrowSelf.failedDecode() from narrowSelfState


#guard selfReturnAbiCompatible "uint8" "uint16"
#guard selfReturnAbiCompatible "int8" "int16"
#guard selfReturnAbiCompatible "bytes2" "bytes2"
#guard !selfReturnAbiCompatible "bytes2" "bytes4"
#guard !selfReturnAbiCompatible "uint8" "bytes1"
#guard !selfReturnAbiCompatible "bytes2" "uint16"

/-- info: ok
returns true -/
#guard_msgs in #run NarrowSelf.widenedNumeric() from narrowSelfState

/-- info: ok
returns true -/
#guard_msgs in #run NarrowSelf.explicitStringPrefix() from narrowSelfState

/-- info: ok
returns true -/
#guard_msgs in #run NarrowSelf.lazyStringPrefix(true) from narrowSelfState

/-- info: ok
returns true -/
#guard_msgs in #run NarrowSelf.lazyStringPrefix(false) from narrowSelfState

/- Compact self-frame returns cannot stand in for ABI alignment conversions. -/
/-- error: Solidity elaboration failed: a self-call result has incompatible ABI type -/
#guard_msgs in #check sol[NarrowSelf]{
  try this.byteValue() returns (bytes4 x) { assert(true); } catch {}; }

/-- error: Solidity elaboration failed: a self-call result has incompatible ABI type -/
#guard_msgs in #check sol[NarrowSelf]{
  try this.unsignedValue() returns (bytes1 x) { assert(true); } catch {}; }

/-- error: Solidity elaboration failed: a self-call result has incompatible ABI type -/
#guard_msgs in #check sol[NarrowSelf]{
  try this.byteValue() returns (uint16 x) { assert(true); } catch {}; }


/- The calculus intentionally closes every external-call diamond to false.
These new source cases request box safety, matching FunctionTypes; concrete
kernel-checked runs below additionally establish normal execution. -/
private theorem fuelSuccess {C : Contract} {Γ Δ : Ctx} (P : Prog C Γ Δ)
    (σ : State C Γ) (h : (Prog.runF 8 P σ).isOk = true) :
    (Prog.run σ P).isOk = true := by
  have hd : Prog.runF 8 P σ ≠ .error .diverge := by
    intro he
    rw [he] at h
    cases h
  change (Prog.runR P σ).isOk = true
  rw [← (Prog.runF_approx 8 P σ).eq hd]
  exact h

private theorem fuelPanic {C : Contract} {Γ Δ : Ctx} (P : Prog C Γ Δ)
    (σ : State C Γ) (halt : (Prog.runF 8 P σ).halt? = some .panic) :
    Prog.run σ P = .error .panic := by
  have h : Prog.runF 8 P σ = .error .panic := by
    cases hr : Prog.runF 8 P σ with
    | ok o => simp only [hr, TRes.halt?, reduceCtorEq] at halt
    | error e =>
      simp only [hr, TRes.halt?, Option.some.injEq] at halt
      exact congrArg Except.error halt
  have hd : Prog.runF 8 P σ ≠ .error .diverge := by
    rw [h]
    intro he
    cases he
  exact ((Prog.runF_approx 8 P σ).eq hd).symm.trans h

private def getterState : State Imported.PublicGetters [] :=
  { State.init Imported.PublicGetters with tx := { selfAddress := ⟨7, by decide⟩ } }

/-- `scalar` ends normally from a concrete nonzero self address. -/
theorem scalar_exec : (Prog.run getterState Imported.PublicGetters.scalar).isOk = true := by
  apply fuelSuccess
  decide +kernel

/-- `viaInterface` ends normally from a concrete nonzero self address. -/
theorem viaInterface_exec : (Prog.run getterState Imported.PublicGetters.viaInterface).isOk = true := by
  apply fuelSuccess
  decide +kernel

/-- `primitives` ends normally from a concrete nonzero self address. -/
theorem primitives_exec : (Prog.run getterState Imported.PublicGetters.primitives).isOk = true := by
  apply fuelSuccess
  decide +kernel

/-- `nestedMapping` ends normally from a concrete nonzero self address. -/
theorem nestedMapping_exec : (Prog.run getterState Imported.PublicGetters.nestedMapping).isOk = true := by
  apply fuelSuccess
  decide +kernel

/-- `boolKeys` ends normally from a concrete nonzero self address. -/
theorem boolKeys_exec : (Prog.run getterState Imported.PublicGetters.boolKeys).isOk = true := by
  apply fuelSuccess
  decide +kernel

/-- `arrays` ends normally from a concrete nonzero self address. -/
theorem arrays_exec : (Prog.run getterState Imported.PublicGetters.arrays).isOk = true := by
  apply fuelSuccess
  decide +kernel

/-- `structFields` ends normally from a concrete nonzero self address. -/
theorem structFields_exec : (Prog.run getterState Imported.PublicGetters.structFields).isOk = true := by
  apply fuelSuccess
  decide +kernel

/-- `inheritedGetters` ends normally from a concrete nonzero self address. -/
theorem inheritedGetters_exec : (Prog.run getterState Imported.PublicGetters.inheritedGetters).isOk = true := by
  apply fuelSuccess
  decide +kernel

/-- `fixedBounds` ends normally from a concrete nonzero self address. -/
theorem fixedBounds_exec : (Prog.run getterState Imported.PublicGetters.fixedBounds).isOk = true := by
  apply fuelSuccess
  decide +kernel

/-- `selectorBounds` ends normally from a concrete nonzero self address. -/
theorem selectorBounds_exec : (Prog.run getterState Imported.PublicGetters.selectorBounds).isOk = true := by
  apply fuelSuccess
  decide +kernel

/-- `identity` ends normally from a concrete nonzero self address. -/
theorem identity_exec : (Prog.run getterState Imported.PublicGetters.identity).isOk = true := by
  apply fuelSuccess
  decide +kernel

/-- The false `falseScalar` assertion panics in the actual typed run. -/
theorem falseScalar_exec : Prog.run getterState Imported.PublicGetters.falseScalar = .error .panic := by
  apply fuelPanic
  decide +kernel

/-- The false `falseBoundsPanic` assertion panics in the actual typed run. -/
theorem falseBoundsPanic_exec : Prog.run getterState Imported.PublicGetters.falseBoundsPanic = .error .panic := by
  apply fuelPanic
  decide +kernel

solc_import "../../../tests/solc/PublicGetters.ast.json" hash 0x968ad03a36798cc3
  as Imported.GetterBytePrefixes testing
solc_scoped_problems Imported.GetterBytePrefixes decl

private def prefixState : State Imported.GetterBytePrefixes [] :=
  { State.init Imported.GetterBytePrefixes with tx := { selfAddress := ⟨7, by decide⟩ } }

/-- `emptyPrefix` preserves the prefix's zero padding and evaluation position. -/
theorem emptyPrefix_exec : (Prog.run prefixState Imported.GetterBytePrefixes.emptyPrefix).isOk = true := by
  apply fuelSuccess
  decide +kernel

/-- `shortPrefix` preserves the prefix's zero padding and evaluation position. -/
theorem shortPrefix_exec : (Prog.run prefixState Imported.GetterBytePrefixes.shortPrefix).isOk = true := by
  apply fuelSuccess
  decide +kernel

/-- `leadingZeroPrefix` preserves the prefix's zero padding and evaluation position. -/
theorem leadingZeroPrefix_exec : (Prog.run prefixState Imported.GetterBytePrefixes.leadingZeroPrefix).isOk = true := by
  apply fuelSuccess
  decide +kernel

/-- `longPrefix` preserves the prefix's zero padding and evaluation position. -/
theorem longPrefix_exec : (Prog.run prefixState Imported.GetterBytePrefixes.longPrefix).isOk = true := by
  apply fuelSuccess
  decide +kernel

/-- `evaluateOnce` preserves the prefix's zero padding and evaluation position. -/
theorem evaluateOnce_exec : (Prog.run prefixState Imported.GetterBytePrefixes.evaluateOnce).isOk = true := by
  apply fuelSuccess
  decide +kernel

/-- `lazyPrefix` preserves the prefix's zero padding and evaluation position. -/
theorem lazyPrefix_exec : (Prog.run prefixState Imported.GetterBytePrefixes.lazyPrefix).isOk = true := by
  apply fuelSuccess
  decide +kernel

/- An ordinary uint8 array is not bytes: the kind check remains in force. -/
#guard (narrowWholeUse? Imported.GetterBytePrefixes
  [("#xs", .shape [("[]", 8)]), ("xs", .mem (.array .uint))]
  (.call "bytes4" [.name "xs"])).isSome

/- String shape markers must survive the prefix admission check. -/
#guard !dynamicBytesExpr Imported.GetterBytePrefixes
  [("#text", .shape [("[]", 8), ("[]#bytes", 1), ("#string", 1)]),
    ("text", .mem (.array .uint))] (.name "text")

/-- error: Solidity elaboration failed: text has a narrow element, key or value: it is used through an index, `.length`, `.push`, `.pop` or `delete`, or whole where the same narrow positions are expected, not whole -/
#guard_msgs in #check sol[Imported.GetterBytePrefixes]{
  string memory text = "abcd"; bytes4 value = bytes4(text); }


/- Replaying a hidden prefix still validates its width and raw byte kind. -/
#guard (bytesPure NarrowSelf [] (.call "#bytesPrefix0" [.call "bytes" [RawExpr.bytesLit []]])).toOption.isNone
#guard (bytesPure NarrowSelf [] (.call "#bytesPrefix33" [.call "bytes" [RawExpr.bytesLit []]])).toOption.isNone
#guard (bytesPure NarrowSelf [] (.call "#bytesPrefix4" [.name "unknown"])).toOption.isNone
#guard (bytesPure NarrowSelf
  [("#text", .shape [("[]", 8), ("[]#bytes", 1), ("#string", 1)]),
    ("text", .mem (.array .uint))]
  (.call "#bytesPrefix4" [.name "text"])).toOption.isNone

end Solidity.Examples.Tactics.PublicGetters
