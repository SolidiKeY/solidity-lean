import Solidity.SolcValidation.IrParse
import Solidity.SolcValidation.IrEval

/-!
# solc's `checked_exp` helpers, as imported

`expHelpersText` is the verbatim text of six functions cut from the saved solc
0.8.38 `--ir` output of `Census` (`tests/fullscope-20261104/vt1/extract-helpers.py`):
`checked_exp_t_uint256_t_uint256` and everything it calls. The tree was printed
from the parser's output (`IrLeanGen.lean`) and split into named bodies
(`gen-helper-modules.py`); `expHelpers_certified` re-checks it against the text by
kernel evaluation (`Parsed.sound`'s statement).
-/
namespace Solidity.SolcValidation.IrSyntax
open Solidity.SolcValidation

def expHelpersText : String :=
  "object \"ExpHelpers\" {\n    code {\n        function cleanup_t_uint256(value) -> cleaned {\n            cleaned := value\n        }\n\n            function panic_error_0x11() {\n                mstore(0, 35408467139433450592217433187231851964531694900788300625387963629091585785856)\n                mstore(4, 0x11)\n                revert(0, 0x24)\n            }\n\n            function shift_right_1_unsigned(value) -> newValue {\n                newValue :=\n\n                shr(1, value)\n\n            }\n\n            function checked_exp_helper(_power, _base, exponent, max) -> power, base {\n                power := _power\n                base  := _base\n                for { } gt(exponent, 1) {}\n                {\n                    // overflow check for base * base\n                    if gt(base, div(max, base)) { panic_error_0x11() }\n                    if and(exponent, 1)\n                    {\n                        // No checks for power := mul(power, base) needed, because the check\n                        // for base * base above is sufficient, since:\n                        // |power| <= base (proof by induction) and thus:\n                        // |power * base| <= base * base <= max <= |min| (for signed)\n                        // (this is equally true for signed and unsigned exp)\n                        power := mul(power, base)\n                    }\n                    base := mul(base, base)\n                    exponent := shift_right_1_unsigned(exponent)\n                }\n            }\n\n            function checked_exp_unsigned(base, exponent, max) -> power {\n                // This function currently cannot be inlined because of the\n                // \"leave\" statements. We have to improve the optimizer.\n\n                // Note that 0**0 == 1\n                if iszero(exponent) { power := 1 leave }\n                if iszero(base) { power := 0 leave }\n\n                // Specializations for small bases\n                switch base\n                // 0 is handled above\n                case 1 { power := 1 leave }\n                case 2\n                {\n                    if gt(exponent, 255) { panic_error_0x11() }\n                    power := exp(2, exponent)\n                    if gt(power, max) { panic_error_0x11() }\n                    leave\n                }\n                if or(\n                    and(lt(base, 11), lt(exponent, 78)),\n                    and(lt(base, 307), lt(exponent, 32))\n                )\n                {\n                    power := exp(base, exponent)\n                    if gt(power, max) { panic_error_0x11() }\n                    leave\n                }\n\n                power, base := checked_exp_helper(1, base, exponent, max)\n\n                if gt(power, div(max, base)) { panic_error_0x11() }\n                power := mul(power, base)\n            }\n\n            function checked_exp_t_uint256_t_uint256(base, exponent) -> power {\n                base := cleanup_t_uint256(base)\n                exponent := cleanup_t_uint256(exponent)\n\n                power := checked_exp_unsigned(base, exponent, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)\n\n            }\n    }\n}\n"

def expSigs : List FnSig :=
  [⟨"cleanup_t_uint256", ["value"], ["cleaned"]⟩, ⟨"panic_error_0x11", [], []⟩, ⟨"shift_right_1_unsigned", ["value"], ["newValue"]⟩, ⟨"checked_exp_helper", ["_power", "_base", "exponent", "max"], ["power", "base"]⟩, ⟨"checked_exp_unsigned", ["base", "exponent", "max"], ["power"]⟩, ⟨"checked_exp_t_uint256_t_uint256", ["base", "exponent"], ["power"]⟩]

abbrev ExpBody (params rets : List String) :=
  Block (expSigs ++ []) ⟨true, false⟩ (params ++ rets)

def expCleanupU : ExpBody ["value"] ["cleaned"] :=
  (.mk [] .nil (.stmt (.assign [⟨"cleaned", (.there .here)⟩] (.var "value" .here)) .nil))

def expPanic11 : ExpBody [] [] :=
  (.mk [] .nil (.stmt (.discard (.op (.evm .«mstore») (.cons (.lit ⟨.num 0, 0, rfl⟩) (.cons (.lit ⟨.num 35408467139433450592217433187231851964531694900788300625387963629091585785856, 35408467139433450592217433187231851964531694900788300625387963629091585785856, rfl⟩) .nil)))) (.stmt (.discard (.op (.evm .«mstore») (.cons (.lit ⟨.num 4, 4, rfl⟩) (.cons (.lit ⟨.num 17, 17, rfl⟩) .nil)))) (.stmt (.discard (.op (.evm .«revert») (.cons (.lit ⟨.num 0, 0, rfl⟩) (.cons (.lit ⟨.num 36, 36, rfl⟩) .nil)))) .nil))))

def expShr1 : ExpBody ["value"] ["newValue"] :=
  (.mk [] .nil (.stmt (.assign [⟨"newValue", (.there .here)⟩] (.op (.evm (.pure .«shr»)) (.cons (.lit ⟨.num 1, 1, rfl⟩) (.cons (.var "value" .here) .nil)))) .nil))

def expExpHelper : ExpBody ["_power", "_base", "exponent", "max"] ["power", "base"] :=
  (.mk [] .nil (.stmt (.assign [⟨"power", (.there (.there (.there (.there .here))))⟩] (.var "_power" .here)) (.stmt (.assign [⟨"base", (.there (.there (.there (.there (.there .here)))))⟩] (.var "_base" (.there .here))) (.stmt (.for_ (.run (.op (.evm (.pure .«gt»)) (.cons (.var "exponent" (.there (.there .here))) (.cons (.lit ⟨.num 1, 1, rfl⟩) .nil))) (.mk [] .nil .nil) (.mk [] .nil (.stmt (.if_ (.op (.evm (.pure .«gt»)) (.cons (.var "base" (.there (.there (.there (.there (.there .here)))))) (.cons (.op (.evm (.pure .«div»)) (.cons (.var "max" (.there (.there (.there .here)))) (.cons (.var "base" (.there (.there (.there (.there (.there .here)))))) .nil))) .nil))) (.mk [] .nil (.stmt (.discard (.call (.there .here) .nil)) .nil))) (.stmt (.if_ (.op (.evm (.pure .«and»)) (.cons (.var "exponent" (.there (.there .here))) (.cons (.lit ⟨.num 1, 1, rfl⟩) .nil))) (.mk [] .nil (.stmt (.assign [⟨"power", (.there (.there (.there (.there .here))))⟩] (.op (.evm (.pure .«mul»)) (.cons (.var "power" (.there (.there (.there (.there .here))))) (.cons (.var "base" (.there (.there (.there (.there (.there .here)))))) .nil)))) .nil))) (.stmt (.assign [⟨"base", (.there (.there (.there (.there (.there .here)))))⟩] (.op (.evm (.pure .«mul»)) (.cons (.var "base" (.there (.there (.there (.there (.there .here)))))) (.cons (.var "base" (.there (.there (.there (.there (.there .here)))))) .nil)))) (.stmt (.assign [⟨"exponent", (.there (.there .here))⟩] (.call (.there (.there .here)) (.cons (.var "exponent" (.there (.there .here))) .nil))) .nil))))))) .nil))))

def expExpUnsigned : ExpBody ["base", "exponent", "max"] ["power"] :=
  (.mk [] .nil (.stmt (.if_ (.op (.evm (.pure .«iszero»)) (.cons (.var "exponent" (.there .here)) .nil)) (.mk [] .nil (.stmt (.assign [⟨"power", (.there (.there (.there .here)))⟩] (.lit ⟨.num 1, 1, rfl⟩)) (.stmt .leave .nil)))) (.stmt (.if_ (.op (.evm (.pure .«iszero»)) (.cons (.var "base" .here) .nil)) (.mk [] .nil (.stmt (.assign [⟨"power", (.there (.there (.there .here)))⟩] (.lit ⟨.num 0, 0, rfl⟩)) (.stmt .leave .nil)))) (.stmt (.switch (.var "base" .here) (.cons ⟨.num 1, 1, rfl⟩ (.mk [] .nil (.stmt (.assign [⟨"power", (.there (.there (.there .here)))⟩] (.lit ⟨.num 1, 1, rfl⟩)) (.stmt .leave .nil))) (.cons ⟨.num 2, 2, rfl⟩ (.mk [] .nil (.stmt (.if_ (.op (.evm (.pure .«gt»)) (.cons (.var "exponent" (.there .here)) (.cons (.lit ⟨.num 255, 255, rfl⟩) .nil))) (.mk [] .nil (.stmt (.discard (.call (.there .here) .nil)) .nil))) (.stmt (.assign [⟨"power", (.there (.there (.there .here)))⟩] (.op (.evm (.pure .«exp»)) (.cons (.lit ⟨.num 2, 2, rfl⟩) (.cons (.var "exponent" (.there .here)) .nil)))) (.stmt (.if_ (.op (.evm (.pure .«gt»)) (.cons (.var "power" (.there (.there (.there .here)))) (.cons (.var "max" (.there (.there .here))) .nil))) (.mk [] .nil (.stmt (.discard (.call (.there .here) .nil)) .nil))) (.stmt .leave .nil))))) .nil))) (.stmt (.if_ (.op (.evm (.pure .«or»)) (.cons (.op (.evm (.pure .«and»)) (.cons (.op (.evm (.pure .«lt»)) (.cons (.var "base" .here) (.cons (.lit ⟨.num 11, 11, rfl⟩) .nil))) (.cons (.op (.evm (.pure .«lt»)) (.cons (.var "exponent" (.there .here)) (.cons (.lit ⟨.num 78, 78, rfl⟩) .nil))) .nil))) (.cons (.op (.evm (.pure .«and»)) (.cons (.op (.evm (.pure .«lt»)) (.cons (.var "base" .here) (.cons (.lit ⟨.num 307, 307, rfl⟩) .nil))) (.cons (.op (.evm (.pure .«lt»)) (.cons (.var "exponent" (.there .here)) (.cons (.lit ⟨.num 32, 32, rfl⟩) .nil))) .nil))) .nil))) (.mk [] .nil (.stmt (.assign [⟨"power", (.there (.there (.there .here)))⟩] (.op (.evm (.pure .«exp»)) (.cons (.var "base" .here) (.cons (.var "exponent" (.there .here)) .nil)))) (.stmt (.if_ (.op (.evm (.pure .«gt»)) (.cons (.var "power" (.there (.there (.there .here)))) (.cons (.var "max" (.there (.there .here))) .nil))) (.mk [] .nil (.stmt (.discard (.call (.there .here) .nil)) .nil))) (.stmt .leave .nil))))) (.stmt (.assign [⟨"power", (.there (.there (.there .here)))⟩, ⟨"base", .here⟩] (.call (.there (.there (.there .here))) (.cons (.lit ⟨.num 1, 1, rfl⟩) (.cons (.var "base" .here) (.cons (.var "exponent" (.there .here)) (.cons (.var "max" (.there (.there .here))) .nil)))))) (.stmt (.if_ (.op (.evm (.pure .«gt»)) (.cons (.var "power" (.there (.there (.there .here)))) (.cons (.op (.evm (.pure .«div»)) (.cons (.var "max" (.there (.there .here))) (.cons (.var "base" .here) .nil))) .nil))) (.mk [] .nil (.stmt (.discard (.call (.there .here) .nil)) .nil))) (.stmt (.assign [⟨"power", (.there (.there (.there .here)))⟩] (.op (.evm (.pure .«mul»)) (.cons (.var "power" (.there (.there (.there .here)))) (.cons (.var "base" .here) .nil)))) .nil))))))))

def expExpU256 : ExpBody ["base", "exponent"] ["power"] :=
  (.mk [] .nil (.stmt (.assign [⟨"base", .here⟩] (.call .here (.cons (.var "base" .here) .nil))) (.stmt (.assign [⟨"exponent", (.there .here)⟩] (.call .here (.cons (.var "exponent" (.there .here)) .nil))) (.stmt (.assign [⟨"power", (.there (.there .here))⟩] (.call (.there (.there (.there (.there .here)))) (.cons (.var "base" .here) (.cons (.var "exponent" (.there .here)) (.cons (.lit ⟨.num 115792089237316195423570985008687907853269984665640564039457584007913129639935, 115792089237316195423570985008687907853269984665640564039457584007913129639935, rfl⟩) .nil))))) .nil))))

def expBodies : Bodies (expSigs ++ []) expSigs :=
  (.cons expCleanupU (.cons expPanic11 (.cons expShr1 (.cons expExpHelper (.cons expExpUnsigned (.cons expExpU256 .nil))))))

def expItems : Items (expSigs ++ []) ⟨false, false⟩ [] expSigs.length :=
  (.fn ⟨0, by decide⟩ (.fn ⟨1, by decide⟩ (.fn ⟨2, by decide⟩ (.fn ⟨3, by decide⟩ (.fn ⟨4, by decide⟩ (.fn ⟨5, by decide⟩ .nil))))))

def expHelpersCode : Code := .mk expSigs expBodies expItems

def expHelpersRoot : Object Code := .object "ExpHelpers" expHelpersCode []

/-- The generated tree carries the same certificate as a parse of the text. -/
theorem expHelpers_certified :
    lex expHelpersText = some (objectToks expHelpersRoot) ∧ objectWf expHelpersRoot = true := by
  decide +kernel

end Solidity.SolcValidation.IrSyntax
