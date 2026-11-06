import Solidity.SolcValidation.IrCensusMaps
import Solidity.SolcValidation.IrCensusTree
import Solidity.SolcValidation.IrHelperSource
import Solidity.SolcValidation.IrAbiSim
import Solidity.SolcValidation.IrPushSim

/-!
# The helper theorems on the certified Census and LinkedMath trees

The helper theorems of C08/C09 are about the extracted helper groups
(`helperEnv`, `expEnv`, `abiEnv`, `pushEnv`). Here they are moved onto the
function groups of the fixtures' trees (`censusRoot`, `linkedRoot`,
`SolcValidation/IrCensusTree.lean`). Both trees carry the parser's certificate
for their fixture text (`census_certified`, `linked_certified`); that the tree is
the parser's own result is proved for LinkedMath only (`linked_is_the_parse`,
`SolcValidation/IrCensusParse.lean`), and for Census rests on the generator.

- `<group>_lookup_<obj>`: looking up a function of an extracted group in the
  object's group (`ren<Group><Obj>`, by its full signature) yields the extracted
  body with its calls renamed to the object's positions (`Block.ren … = some …`):
  the same text, up to the positions of the called functions. The pairs are
  Helpers→`Census_134_deployed`/`LinkedMath_14_deployed`, exp→`Census_134_deployed`,
  ABI→`Census_134_deployed`/`LinkedMath_14_deployed`, push→`Census_134_deployed`/`Census_134`;
  a function the map sends to `none` is one the object does not define
  (`<group>_unmapped_<obj>`, `SolcValidation/IrCensusUnique.lean`).
- `sim_<group>_<obj>`: hence the two environments are related at every fuel
  (`Sim`, `SolcValidation/IrRename.lean`), and `evalExpr_ren`/`evalBlock_ren`
  give the same result, effects and faults for the renamed code.
- `census_*`/`linked_*`: the headline helper theorems restated for the objects'
  own bodies and environments (`cdEnv`: `Census_134_deployed`, `ccEnv`: `Census_134`,
  `ldEnv`: `LinkedMath_14_deployed`); each environment is the one evaluating that
  object's code installs (`cdEnv_installed`, …), and each body is the group's body
  at the helper's position (`cd_div_at`, …).

What a call site inside a `fun_<name>_<id>` passes to these helpers is T02's
per-function layer, which waits on G01.
-/
namespace Solidity.SolcValidation.IrSyntax
open Solidity.SolcValidation

/-- Evaluating an object's code (as `runCode` does) installs exactly its top-level group. -/
theorem cdEnv_installed {σ : Type} (M : Machine σ) (ctx : ObjectCtx) (k : Nat) (s : σ) :
    evalBlock M ctx (k + 1) .nil cdCode .nil s = evalItems M ctx k cdEnv cdItems .nil s := rfl
theorem ccEnv_installed {σ : Type} (M : Machine σ) (ctx : ObjectCtx) (k : Nat) (s : σ) :
    evalBlock M ctx (k + 1) .nil ccCode .nil s = evalItems M ctx k ccEnv ccItems .nil s := rfl
theorem ldEnv_installed {σ : Type} (M : Machine σ) (ctx : ObjectCtx) (k : Nat) (s : σ) :
    evalBlock M ctx (k + 1) .nil ldCode .nil s = evalItems M ctx k ldEnv ldItems .nil s := rfl

/-- The objects whose groups are used below, at their paths in the parsed trees. -/
theorem censusRoot_objects : ∃ children : List (Object Code),
    censusRoot = .object "Census_134" ccCode [.object "Census_134_deployed" cdCode children] := ⟨_, rfl⟩

theorem linkedRoot_objects : ∃ children : List (Object Code),
    linkedRoot = .object "LinkedMath_14" lcCode [.object "LinkedMath_14_deployed" ldCode children] := ⟨_, rfl⟩

/-- Every function of the extracted group that `cdSigs` defines is, in the parsed
object's group, exactly the extracted body with its calls renamed by `renHelpersCd`. -/
theorem helpers_lookup_cd : ∀ {s : FnSig} (m : Mem (helperSigs ++ []) s) (m' : Mem (cdSigs ++ []) s),
    renHelpersCd m = some m' →
      (helperBodies.get (Mem.flat _ m)).ren renHelpersCd = some (cdBodies.get (Mem.flat _ m')) := by
  intro s m m' hm
  repeat' (first
    | (obtain rfl := Option.some.inj hm; rfl)
    | exact Option.noConfusion hm
    | rcases m with _ | m)

theorem sim_helpers_cd : ∀ k, Sim k renHelpersCd helperEnv cdEnv :=
  Sim.flat helperBodies cdBodies renHelpersCd helpers_lookup_cd

/-- Every function of the extracted group that `ldSigs` defines is, in the parsed
object's group, exactly the extracted body with its calls renamed by `renHelpersLd`. -/
theorem helpers_lookup_ld : ∀ {s : FnSig} (m : Mem (helperSigs ++ []) s) (m' : Mem (ldSigs ++ []) s),
    renHelpersLd m = some m' →
      (helperBodies.get (Mem.flat _ m)).ren renHelpersLd = some (ldBodies.get (Mem.flat _ m')) := by
  intro s m m' hm
  repeat' (first
    | (obtain rfl := Option.some.inj hm; rfl)
    | exact Option.noConfusion hm
    | rcases m with _ | m)

theorem sim_helpers_ld : ∀ k, Sim k renHelpersLd helperEnv ldEnv :=
  Sim.flat helperBodies ldBodies renHelpersLd helpers_lookup_ld

/-- Every function of the extracted group that `cdSigs` defines is, in the parsed
object's group, exactly the extracted body with its calls renamed by `renExpCd`. -/
theorem exp_lookup_cd : ∀ {s : FnSig} (m : Mem (expSigs ++ []) s) (m' : Mem (cdSigs ++ []) s),
    renExpCd m = some m' →
      (expBodies.get (Mem.flat _ m)).ren renExpCd = some (cdBodies.get (Mem.flat _ m')) := by
  intro s m m' hm
  repeat' (first
    | (obtain rfl := Option.some.inj hm; rfl)
    | exact Option.noConfusion hm
    | rcases m with _ | m)

theorem sim_exp_cd : ∀ k, Sim k renExpCd expEnv cdEnv :=
  Sim.flat expBodies cdBodies renExpCd exp_lookup_cd

/-- Every function of the extracted group that `cdSigs` defines is, in the parsed
object's group, exactly the extracted body with its calls renamed by `renAbiCd`. -/
theorem abi_lookup_cd : ∀ {s : FnSig} (m : Mem (abiSigs ++ []) s) (m' : Mem (cdSigs ++ []) s),
    renAbiCd m = some m' →
      (abiBodies.get (Mem.flat _ m)).ren renAbiCd = some (cdBodies.get (Mem.flat _ m')) := by
  intro s m m' hm
  repeat' (first
    | (obtain rfl := Option.some.inj hm; rfl)
    | exact Option.noConfusion hm
    | rcases m with _ | m)

theorem sim_abi_cd : ∀ k, Sim k renAbiCd abiEnv cdEnv :=
  Sim.flat abiBodies cdBodies renAbiCd abi_lookup_cd

/-- Every function of the extracted group that `ldSigs` defines is, in the parsed
object's group, exactly the extracted body with its calls renamed by `renAbiLd`. -/
theorem abi_lookup_ld : ∀ {s : FnSig} (m : Mem (abiSigs ++ []) s) (m' : Mem (ldSigs ++ []) s),
    renAbiLd m = some m' →
      (abiBodies.get (Mem.flat _ m)).ren renAbiLd = some (ldBodies.get (Mem.flat _ m')) := by
  intro s m m' hm
  repeat' (first
    | (obtain rfl := Option.some.inj hm; rfl)
    | exact Option.noConfusion hm
    | rcases m with _ | m)

theorem sim_abi_ld : ∀ k, Sim k renAbiLd abiEnv ldEnv :=
  Sim.flat abiBodies ldBodies renAbiLd abi_lookup_ld

/-- Every function of the extracted group that `cdSigs` defines is, in the parsed
object's group, exactly the extracted body with its calls renamed by `renPushCd`. -/
theorem push_lookup_cd : ∀ {s : FnSig} (m : Mem (pushSigs ++ []) s) (m' : Mem (cdSigs ++ []) s),
    renPushCd m = some m' →
      (pushBodies.get (Mem.flat _ m)).ren renPushCd = some (cdBodies.get (Mem.flat _ m')) := by
  intro s m m' hm
  repeat' (first
    | (obtain rfl := Option.some.inj hm; rfl)
    | exact Option.noConfusion hm
    | rcases m with _ | m)

theorem sim_push_cd : ∀ k, Sim k renPushCd pushEnv cdEnv :=
  Sim.flat pushBodies cdBodies renPushCd push_lookup_cd

/-- Every function of the extracted group that `ccSigs` defines is, in the parsed
object's group, exactly the extracted body with its calls renamed by `renPushCc`. -/
theorem push_lookup_cc : ∀ {s : FnSig} (m : Mem (pushSigs ++ []) s) (m' : Mem (ccSigs ++ []) s),
    renPushCc m = some m' →
      (pushBodies.get (Mem.flat _ m)).ren renPushCc = some (ccBodies.get (Mem.flat _ m')) := by
  intro s m m' hm
  repeat' (first
    | (obtain rfl := Option.some.inj hm; rfl)
    | exact Option.noConfusion hm
    | rcases m with _ | m)

theorem sim_push_cc : ∀ k, Sim k renPushCc pushEnv ccEnv :=
  Sim.flat pushBodies ccBodies renPushCc push_lookup_cc

/-! ## The headline helper theorems on the parsed objects -/

/-- `checked_add_t_uint256(a, b)` in `Census_134_deployed`'s scope. -/
def cdAddCall : Expr (cdSigs ++ []) ArgNames 1 := (addCall.ren renHelpersCd).get rfl
/-- `checked_sub_t_uint256(a, b)` in `Census_134_deployed`'s scope. -/
def cdSubCall : Expr (cdSigs ++ []) ArgNames 1 := (subCall.ren renHelpersCd).get rfl
/-- `checked_mul_t_uint256(a, b)` in `LinkedMath_14_deployed`'s scope. -/
def ldMulCall : Expr (ldSigs ++ []) ArgNames 1 := (mulCall.ren renHelpersLd).get rfl

theorem cdAddCall_ren : addCall.ren renHelpersCd = some cdAddCall := rfl
theorem cdSubCall_ren : subCall.ren renHelpersCd = some cdSubCall := rfl
theorem ldMulCall_ren : mulCall.ren renHelpersLd = some ldMulCall := rfl

theorem cdAddCall_toks : cdAddCall.toks = callToks "checked_add_t_uint256" [[.ident "a"], [.ident "b"]] := by
  decide +kernel
theorem cdSubCall_toks : cdSubCall.toks = callToks "checked_sub_t_uint256" [[.ident "a"], [.ident "b"]] := by
  decide +kernel
theorem ldMulCall_toks : ldMulCall.toks = callToks "checked_mul_t_uint256" [[.ident "a"], [.ident "b"]] := by
  decide +kernel

/-- The parsed bodies the theorems below are about, by their position in the group. -/
theorem cd_bodies_named :
    (cdSigs.get ⟨72, by decide⟩).name = "checked_div_t_int256" ∧
    (cdSigs.get ⟨67, by decide⟩).name = "checked_exp_t_uint256_t_uint256" ∧
    (cdSigs.get ⟨8, by decide⟩).name = "abi_decode_tuple_t_uint256" ∧
    (cdSigs.get ⟨87, by decide⟩).name = "array_push_from_t_uint256_to_t_array$_t_uint256_$dyn_storage_ptr" ∧
    (ccSigs.get ⟨25, by decide⟩).name = "array_push_from_t_uint256_to_t_array$_t_uint256_$dyn_storage_ptr" ∧
    (ldSigs.get ⟨7, by decide⟩).name = "abi_decode_tuple_t_uint256" := by
  decide +kernel

/-! Each body below is the object's group body at the position of its helper. -/
theorem cd_div_at : ∃ m', renHelpersCd (s := ⟨"checked_div_t_int256", ["x", "y"], ["r"]⟩)
    (.there (.there (.there (.there (.there (.there .here)))))) = some m' ∧
      cdBodies.get (Mem.flat _ m') = cdF72 := ⟨_, rfl, rfl⟩
theorem cd_exp_at : ∃ m', renExpCd (s := ⟨"checked_exp_t_uint256_t_uint256", ["base", "exponent"], ["power"]⟩)
    (.there (.there (.there (.there (.there .here))))) = some m' ∧
      cdBodies.get (Mem.flat _ m') = cdF67 := ⟨_, rfl, rfl⟩
theorem cd_decode_at : ∃ m', renAbiCd (s := ⟨"abi_decode_tuple_t_uint256", ["headStart", "dataEnd"], ["value0"]⟩)
    (.there (.there (.there (.there .here)))) = some m' ∧
      cdBodies.get (Mem.flat _ m') = cdF8 := ⟨_, rfl, rfl⟩
theorem ld_decode_at : ∃ m', renAbiLd (s := ⟨"abi_decode_tuple_t_uint256", ["headStart", "dataEnd"], ["value0"]⟩)
    (.there (.there (.there (.there .here)))) = some m' ∧
      ldBodies.get (Mem.flat _ m') = ldF7 := ⟨_, rfl, rfl⟩
theorem cd_push_at : ∃ m', renPushCd
    (s := ⟨"array_push_from_t_uint256_to_t_array$_t_uint256_$dyn_storage_ptr", ["array", "value0"], []⟩)
    (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))
      = some m' ∧ cdBodies.get (Mem.flat _ m') = cdF87 := ⟨_, rfl, rfl⟩
theorem cc_push_at : ∃ m', renPushCc
    (s := ⟨"array_push_from_t_uint256_to_t_array$_t_uint256_$dyn_storage_ptr", ["array", "value0"], []⟩)
    (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))
      = some m' ∧ ccBodies.get (Mem.flat _ m') = ccF25 := ⟨_, rfl, rfl⟩

section
variable {σ : Type} (M : Machine σ) (ctx : ObjectCtx)

/-! Transfer equations: the parsed object's code evaluates as the extracted one. -/

theorem cd_add_eq (n : Nat) (vs : Vals ArgNames) (s : σ) :
    evalExpr M ctx n cdEnv cdAddCall vs s = evalExpr M ctx n helperEnv addCall vs s :=
  evalExpr_ren M ctx n renHelpersCd helperEnv cdEnv addCall cdAddCall vs s (sim_helpers_cd n) cdAddCall_ren
theorem cd_sub_eq (n : Nat) (vs : Vals ArgNames) (s : σ) :
    evalExpr M ctx n cdEnv cdSubCall vs s = evalExpr M ctx n helperEnv subCall vs s :=
  evalExpr_ren M ctx n renHelpersCd helperEnv cdEnv subCall cdSubCall vs s (sim_helpers_cd n) cdSubCall_ren
theorem ld_mul_eq (n : Nat) (vs : Vals ArgNames) (s : σ) :
    evalExpr M ctx n ldEnv ldMulCall vs s = evalExpr M ctx n helperEnv mulCall vs s :=
  evalExpr_ren M ctx n renHelpersLd helperEnv ldEnv mulCall ldMulCall vs s (sim_helpers_ld n) ldMulCall_ren
theorem cd_div_eq (n : Nat) (vs : Vals (["x", "y"] ++ ["r"])) (s : σ) :
    evalBlock M ctx n cdEnv cdF72 vs s = evalBlock M ctx n helperEnv bodyDiv vs s :=
  evalBlock_ren M ctx n renHelpersCd helperEnv cdEnv bodyDiv cdF72 vs s (sim_helpers_cd n) rfl
theorem cd_exp_eq (n : Nat) (vs : Vals (["base", "exponent"] ++ ["power"])) (s : σ) :
    evalBlock M ctx n cdEnv cdF67 vs s = evalBlock M ctx n expEnv expExpU256 vs s :=
  evalBlock_ren M ctx n renExpCd expEnv cdEnv expExpU256 cdF67 vs s (sim_exp_cd n) rfl
theorem cd_decode_eq (n : Nat) (vs : Vals (["headStart", "dataEnd"] ++ ["value0"])) (s : σ) :
    evalBlock M ctx n cdEnv cdF8 vs s = evalBlock M ctx n abiEnv abiDecodeTuple vs s :=
  evalBlock_ren M ctx n renAbiCd abiEnv cdEnv abiDecodeTuple cdF8 vs s (sim_abi_cd n) rfl
theorem ld_decode_eq (n : Nat) (vs : Vals (["headStart", "dataEnd"] ++ ["value0"])) (s : σ) :
    evalBlock M ctx n ldEnv ldF7 vs s = evalBlock M ctx n abiEnv abiDecodeTuple vs s :=
  evalBlock_ren M ctx n renAbiLd abiEnv ldEnv abiDecodeTuple ldF7 vs s (sim_abi_ld n) rfl
theorem cd_push_eq (n : Nat) (vs : Vals (["array", "value0"] ++ [])) (s : σ) :
    evalBlock M ctx n cdEnv cdF87 vs s = evalBlock M ctx n pushEnv pushPush vs s :=
  evalBlock_ren M ctx n renPushCd pushEnv cdEnv pushPush cdF87 vs s (sim_push_cd n) rfl
theorem cc_push_eq (n : Nat) (vs : Vals (["array", "value0"] ++ [])) (s : σ) :
    evalBlock M ctx n ccEnv ccF25 vs s = evalBlock M ctx n pushEnv pushPush vs s :=
  evalBlock_ren M ctx n renPushCc pushEnv ccEnv pushPush ccF25 vs s (sim_push_cc n) rfl

theorem census_checked_add_sim (k : Nat) (x y : Word) (s : σ) :
    evalExpr M ctx (k + 20) cdEnv cdAddCall (argVals x y) s =
      if x.val + y.val < 2 ^ 256 then .ok (s, fun _ => Solidity.Yul.word (x.val + y.val))
      else (fun s => (s, fun _ => Solidity.Yul.word (x.val + y.val))) <$> panicRun M 0x11 s := by
  simp only [cd_add_eq]
  exact checked_add_sim M ctx k x y s

theorem census_checked_sub_sim (k : Nat) (x y : Word) (s : σ) :
    evalExpr M ctx (k + 34) cdEnv cdSubCall (argVals x y) s =
      if y.val ≤ x.val then .ok (s, fun _ => Solidity.Yul.word (x.val - y.val))
      else (fun s => (s, fun _ => Solidity.Yul.Pure.eval .«sub» (word2 x y))) <$> panicRun M 0x11 s := by
  simp only [cd_sub_eq]
  exact checked_sub_sim M ctx k x y s

theorem linked_checked_mul_sim (k : Nat) (x y : Word) (s : σ) :
    evalExpr M ctx (k + 34) ldEnv ldMulCall (argVals x y) s =
      if x.val * y.val < 2 ^ 256 then .ok (s, fun _ => Solidity.Yul.word (x.val * y.val))
      else (fun s => (s, fun _ => Solidity.Yul.word (x.val * y.val))) <$> panicRun M 0x11 s := by
  simp only [ld_mul_eq]
  exact checked_mul_sim M ctx k x y s

theorem census_checked_div_body (k : Nat) (x y : Word) (s : σ) :
    evalBlock M ctx (k + 60) cdEnv cdF72 (.cons x (.cons y (.cons 0 .nil))) s =
      panicIf M (y.val == 0) 0x12 s >>= fun s =>
        panicIf M (x.val == 2 ^ 255 && y.val == 2 ^ 256 - 1) 0x11 s >>= fun s =>
          .ok (s, .cons x (.cons y (.cons (Solidity.Yul.Pure.eval .«sdiv» (word2 x y)) .nil)), .normal) := by
  simp only [cd_div_eq]
  exact checked_div_body M ctx k x y s

theorem census_checked_add_matches_source (k : Nat) (x y : Word) (s : σ) :
    match sourceAdd x y with
    | some v => evalExpr M ctx (k + 20) cdEnv cdAddCall (argVals x y) s =
        .ok (s, fun _ => Solidity.Yul.word v.toNat)
    | none => evalExpr M ctx (k + 20) cdEnv cdAddCall (argVals x y) s =
        (fun s => (s, fun _ => Solidity.Yul.word (x.val + y.val))) <$> panicRun M 0x11 s := by
  rw [sourceAdd_eq, census_checked_add_sim]
  by_cases fits : x.val + y.val < 2 ^ 256
  · simp only [fits, if_true, Int.toNat_natCast]
  · simp only [fits, if_false]

theorem census_checked_sub_matches_source (k : Nat) (x y : Word) (s : σ) :
    match sourceSub x y with
    | some v => evalExpr M ctx (k + 34) cdEnv cdSubCall (argVals x y) s =
        .ok (s, fun _ => Solidity.Yul.word v.toNat)
    | none => evalExpr M ctx (k + 34) cdEnv cdSubCall (argVals x y) s =
        (fun s => (s, fun _ => Solidity.Yul.Pure.eval .«sub» (word2 x y))) <$> panicRun M 0x11 s := by
  have h := checked_sub_matches_source M ctx k x y s
  revert h
  cases sourceSub x y <;> intro h <;> simp only [cd_sub_eq] at h ⊢ <;> exact h

theorem linked_checked_mul_matches_source (k : Nat) (x y : Word) (s : σ) :
    match sourceMul x y with
    | some v => evalExpr M ctx (k + 34) ldEnv ldMulCall (argVals x y) s =
        .ok (s, fun _ => Solidity.Yul.word v.toNat)
    | none => evalExpr M ctx (k + 34) ldEnv ldMulCall (argVals x y) s =
        (fun s => (s, fun _ => Solidity.Yul.word (x.val * y.val))) <$> panicRun M 0x11 s := by
  rw [sourceMul_eq, linked_checked_mul_sim]
  by_cases fits : x.val * y.val < 2 ^ 256
  · simp only [fits, if_true, Int.toNat_natCast]
  · simp only [fits, if_false]

theorem census_checked_div_matches_source (k : Nat) (x y : Word) (s : σ) :
    match sourceDiv x y with
    | some v => evalBlock M ctx (k + 60) cdEnv cdF72 (.cons x (.cons y (.cons 0 .nil))) s =
        .ok (s, .cons x (.cons y (.cons (Solidity.Yul.iword v) .nil)), .normal)
    | none => evalBlock M ctx (k + 60) cdEnv cdF72 (.cons x (.cons y (.cons 0 .nil))) s =
        panicRun M (if y.val = 0 then 0x12 else 0x11) s >>= fun s =>
          .ok (s, .cons x (.cons y (.cons (Solidity.Yul.Pure.eval .«sdiv» (word2 x y)) .nil)), .normal) := by
  have h := checked_div_matches_source M ctx k x y s
  revert h
  cases sourceDiv x y <;> intro h <;> simp only [cd_div_eq] at h ⊢ <;> exact h

theorem census_checked_exp_body (j : Nat) (x y : Word) (s : σ) :
    (x.val ^ y.val < 2 ^ 256 → evalBlock M ctx (j + 420) cdEnv cdF67 (.cons x (.cons y (.cons 0 .nil))) s =
      .ok (s, .cons x (.cons y (.cons (Solidity.Yul.word (x.val ^ y.val)) .nil)), .normal)) ∧
    (¬ x.val ^ y.val < 2 ^ 256 → ∃ cont, evalBlock M ctx (j + 420) cdEnv cdF67
      (.cons x (.cons y (.cons 0 .nil))) s = panicRun M 0x11 s >>= cont) := by
  simp only [cd_exp_eq]
  exact checked_exp_body M ctx j x y s

theorem census_checked_exp_overflow_halts (j : Nat) (x y : Word) (s : σ) (h : RevertHalts M)
    (over : ¬ x.val ^ y.val < 2 ^ 256) :
    ∃ e, panicRun M 0x11 s = .error e ∧
      evalBlock M ctx (j + 420) cdEnv cdF67 (.cons x (.cons y (.cons 0 .nil))) s = .error e := by
  simp only [cd_exp_eq]
  exact checked_exp_overflow_halts M ctx j x y s h over

theorem census_checked_exp_matches_source (k : Nat) (x y : Word) (s : σ) :
    match sourceExp x y with
    | some v => evalBlock M ctx (k + 420) cdEnv cdF67 (.cons x (.cons y (.cons 0 .nil))) s =
        .ok (s, .cons x (.cons y (.cons (Solidity.Yul.word v.toNat) .nil)), .normal)
    | none => ∃ cont, evalBlock M ctx (k + 420) cdEnv cdF67 (.cons x (.cons y (.cons 0 .nil))) s =
        panicRun M 0x11 s >>= cont := by
  have h := checked_exp_matches_source M ctx k x y s
  revert h
  cases sourceExp x y <;> intro h <;> simp only [cd_exp_eq] at h ⊢ <;> exact h

theorem census_decodeTuple_body (k : Nat) (h d : Word) (s : σ) :
    let short := decide (Solidity.Yul.signed (Solidity.Yul.Pure.eval .«sub» (word2 d h)) < 32)
    (short = true → ∃ cont, evalBlock M ctx (k + 80) cdEnv cdF8 (.cons h (.cons d (.cons 0 .nil))) s =
      M.run .«revert» (word2 0 0) s >>= cont) ∧
    (short = false → evalBlock M ctx (k + 80) cdEnv cdF8 (.cons h (.cons d (.cons 0 .nil))) s =
      (fun r => (r.1, .cons h (.cons d (.cons (r.2 0) .nil)), .normal)) <$> M.run .«calldataload» (fun _ => h) s) := by
  simp only [cd_decode_eq]
  exact decodeTuple_body M ctx k h d s

theorem linked_decodeTuple_body (k : Nat) (h d : Word) (s : σ) :
    let short := decide (Solidity.Yul.signed (Solidity.Yul.Pure.eval .«sub» (word2 d h)) < 32)
    (short = true → ∃ cont, evalBlock M ctx (k + 80) ldEnv ldF7 (.cons h (.cons d (.cons 0 .nil))) s =
      M.run .«revert» (word2 0 0) s >>= cont) ∧
    (short = false → evalBlock M ctx (k + 80) ldEnv ldF7 (.cons h (.cons d (.cons 0 .nil))) s =
      (fun r => (r.1, .cons h (.cons d (.cons (r.2 0) .nil)), .normal)) <$> M.run .«calldataload» (fun _ => h) s) := by
  simp only [ld_decode_eq]
  exact decodeTuple_body M ctx k h d s

theorem census_decodeTuple_short_halts (k : Nat) (h d : Word) (s : σ) (hr : RevertHalts M)
    (short : decide (Solidity.Yul.signed (Solidity.Yul.Pure.eval .«sub» (word2 d h)) < 32) = true) :
    ∃ e, M.run .«revert» (word2 0 0) s = .error e ∧
      evalBlock M ctx (k + 80) cdEnv cdF8 (.cons h (.cons d (.cons 0 .nil))) s = .error e := by
  simp only [cd_decode_eq]
  exact decodeTuple_short_halts M ctx k h d s hr short

/-- The push script, as in `push_body`, for the deployed object's `array_push…`
(`values.push` in `push(uint256)`) and the creation object's (the constructor's). -/
abbrev PushScript (M : Machine σ) (a v : Word) (s : σ) : Run σ (σ × Vals (["array", "value0"] ++ []) × Flow) :=
  M.run .«sload» (fun _ => a) s >>= fun r1 =>
  panicIf M (!decide ((r1.2 0).val < 2 ^ 64)) 0x41 r1.1 >>= fun s2 =>
  M.run .«sstore» (word2 a (Solidity.Yul.word ((r1.2 0).val + 1))) s2 >>= fun r3 =>
  M.run .«sload» (fun _ => a) r3.1 >>= fun r4 =>
  panicIf M (!decide ((r1.2 0).val < (r4.2 0).val)) 0x32 r4.1 >>= fun s5 =>
  M.run .«mstore» (word2 0 a) s5 >>= fun r6 =>
  M.run .«keccak256» (word2 0 32) r6.1 >>= fun r7 =>
  M.run .«sload» (fun _ => Solidity.Yul.word ((r7.2 0).val + (r1.2 0).val)) r7.1 >>= fun r8 =>
  (fun r9 => (r9.1, .cons a (.cons v .nil), .normal)) <$>
    M.run .«sstore» (word2 (Solidity.Yul.word ((r7.2 0).val + (r1.2 0).val)) v) r8.1

theorem census_push_body (k : Nat) (a v : Word) (s : σ) :
    evalBlock M ctx (k + 300) cdEnv cdF87 (.cons a (.cons v .nil)) s = PushScript M a v s := by
  simp only [cd_push_eq]
  exact push_body M ctx k a v s

theorem census_constructor_push_body (k : Nat) (a v : Word) (s : σ) :
    evalBlock M ctx (k + 300) ccEnv ccF25 (.cons a (.cons v .nil)) s = PushScript M a v s := by
  simp only [cc_push_eq]
  exact push_body M ctx k a v s

end

end Solidity.SolcValidation.IrSyntax
