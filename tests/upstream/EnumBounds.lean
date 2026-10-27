import Solidity.Tools.Upstream

open Solidity Solidity.Semantics

solc_import "../solc/EnumDeclarationBounds.ast.json" hash 0xe94035f3ffc089f4 as BoundsLegacy.EnumDeclarationBounds testing

private def LegacyReject : Blk BoundsLegacy.EnumDeclarationBounds [] := ⟨_, sol[BoundsLegacy.EnumDeclarationBounds]{ foreignRead(2); }⟩
theorem LegacyReject_checked : (match Prog.run (State.init BoundsLegacy.EnumDeclarationBounds) LegacyReject.2 with | .error .panic => true | _ => false) = true := by decide +kernel
#print axioms LegacyReject_checked

private def LegacyForeign : Blk BoundsLegacy.EnumDeclarationBounds [] := ⟨_, sol[BoundsLegacy.EnumDeclarationBounds]{ uint x = foreignRead(1); assert(x == 1); }⟩
theorem LegacyForeign_checked : (Prog.run (State.init BoundsLegacy.EnumDeclarationBounds) LegacyForeign.2).isOk = true := by decide +kernel
#print axioms LegacyForeign_checked

private def LegacyLocal : Blk BoundsLegacy.EnumDeclarationBounds [] := ⟨_, sol[BoundsLegacy.EnumDeclarationBounds]{ localAccepts(); }⟩
theorem LegacyLocal_checked : (Prog.run (State.init BoundsLegacy.EnumDeclarationBounds) LegacyLocal.2).isOk = true := by decide +kernel
#print axioms LegacyLocal_checked

solc_import "../solc/EnumDeclarationBounds-viaIR.ast.json" hash 0xb0381165d0dad385 as BoundsIR.EnumDeclarationBounds testing

private def IRReject : Blk BoundsIR.EnumDeclarationBounds [] := ⟨_, sol[BoundsIR.EnumDeclarationBounds]{ foreignRead(2); }⟩
theorem IRReject_checked : (match Prog.run (State.init BoundsIR.EnumDeclarationBounds) IRReject.2 with | .error .panic => true | _ => false) = true := by decide +kernel
#print axioms IRReject_checked

private def IRForeign : Blk BoundsIR.EnumDeclarationBounds [] := ⟨_, sol[BoundsIR.EnumDeclarationBounds]{ uint x = foreignRead(1); assert(x == 1); }⟩
theorem IRForeign_checked : (Prog.run (State.init BoundsIR.EnumDeclarationBounds) IRForeign.2).isOk = true := by decide +kernel
#print axioms IRForeign_checked

private def IRLocal : Blk BoundsIR.EnumDeclarationBounds [] := ⟨_, sol[BoundsIR.EnumDeclarationBounds]{ localAccepts(); }⟩
theorem IRLocal_checked : (Prog.run (State.init BoundsIR.EnumDeclarationBounds) IRLocal.2).isOk = true := by decide +kernel
#print axioms IRLocal_checked

