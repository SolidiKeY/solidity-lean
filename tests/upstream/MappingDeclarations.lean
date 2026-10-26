import Solidity.Tools.Upstream
solc_import "../solc/MappingAliases.ast.json" hash 0x0ac73744dfdbf75b as Imported.MappingAliases testing
solc_import "../solc/MappingAliasesIR.ast.json" hash 0x9763b92c2484ec50 as Imported.IR.MappingAliases testing
open Solidity
namespace Solidity.Upstream.MappingDeclarations

/-- A fresh snapshot is unchanged by a subsequent rebind of an older alias. -/
theorem snapshot_rebind {C : Contract} {Γ : Ctx} {R S : RefTy}
    (σ : State C (.alias R :: Γ)) (i : Idx Γ (.alias S))
    (rhs : ARhs C (.alias R :: Γ) S) (st : Storage C) (ref : SRef C (.ref S))
    (h : rhs.evalT σ = .ok (st, ref)) :
    (TRun.rebind (.there i) rhs σ).toOption.map
        (fun out => (TEnv.get (H := out.st.H) (.here : Idx (.alias R :: Γ) (.alias R)) out.st.env : Option (SRef C (.ref R)))) =
      some (TEnv.get (H := σ.H) .here σ.env : Option (SRef C (.ref R))) := by
  simp only [TRun.rebind, h]
  rfl

/-- info: 'Solidity.Upstream.MappingDeclarations.snapshot_rebind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms snapshot_rebind
/-- info: 'Solidity.mappingAssignmentShape' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms mappingAssignmentShape

private def C : Contract := contract!{
  mapping(uint8 => uint8) a;
  mapping(uint8 => uint8) b;
  mapping(uint16 => uint8) wideKey;
  mapping(uint8 => uint16) wideValue;
  uint stored;
}
private def observe {Γ : Ctx} (o : TRes (Out C [] Γ)) : Option Int :=
  (do let a ← o; pure (← Val.evalT a.st (.read (.root "stored" rfl))).1).toOption

theorem assigned : observe ((sol[C]{
    mapping(uint8 => uint8) storage m = a;
    m[1] = 42; (m = b)[2] = 21;
    stored = uint(a[1]) + uint(a[2]) + uint(b[1]) + uint(b[2]);
  }).run (State.init C)) = some 63 := by decide +kernel

theorem snapshot : observe ((sol[C]{
    mapping(uint8 => uint8) storage m = a;
    mapping(uint8 => uint8) storage n = b;
    (m = n)[(n = a)[0]] = 7;
    stored = uint(m[0]) * 100 + uint(n[0]) * 10 + uint(b[0]);
  }).run (State.init C)) = some 707 := by decide +kernel

theorem bare_snapshot : observe ((sol[C]{
    mapping(uint8 => uint8) storage n = b;
    n[(n = a)[0]] = 7;
    stored = uint(a[0]) * 10 + uint(b[0]);
  }).run (State.init C)) = some 7 := by decide +kernel

theorem once : observe ((sol[C]{
    mapping(uint8 => uint8) storage m = a;
    uint8 i = 0; (m = b)[i++] = 9;
    stored = uint(m[0]) + uint(i);
  }).run (State.init C)) = some 10 := by decide +kernel

theorem read_width : observe ((sol[C]{
    b[0] = 255; mapping(uint8 => uint8) storage m = a;
    uint z = (m = b)[0]; stored = z;
  }).run (State.init C)) = some 255 := by decide +kernel

theorem overflow_width : ((sol[C]{
    b[0] = 255; mapping(uint8 => uint8) storage m = a;
    uint z = (m = b)[0] + 1; stored = z;
  }).run (State.init C)).toOption.isNone := by decide +kernel

#guard (elabProgS C [
  .declStorage (.mapping (.named "uint8") (.named "uint8")) "m" (some (.name "a")),
  .assign (.index (.assign (.name "m") (.name "wideKey")) (.num 0)) (.num 1)
  ]).toOption.isNone
#guard (elabProgS C [
  .declStorage (.mapping (.named "uint8") (.named "uint8")) "m" (some (.name "a")),
  .assign (.index (.assign (.name "m") (.name "wideValue")) (.num 0)) (.num 1)
  ]).toOption.isNone
#guard (elabProgS C [
  .declStorage (.mapping (.named "uint8") (.named "uint8")) "m" (some (.name "a")),
  .declMemory (.array (.named "uint8")) "p" (some (.newArr (.named "uint8") (.num 1))),
  .assign (.index (.assign (.name "m") (.name "p")) (.num 0)) (.num 1)
  ]).toOption.isNone
private def check (wrong : Bool) (ir : Bool) : IO Unit := do
  let text := "{\"vectors\":[" ++
    "{\"signature\":\"nested()\",\"args\":[],\"failure\":false,\"expected\":[\"" ++
      (if wrong then "7" else "0") ++ "\",\"7\",\"7\",\"0\"]}," ++
    "{\"signature\":\"bare()\",\"args\":[],\"failure\":false,\"expected\":[\"0\",\"7\"]}," ++
    "{\"signature\":\"once()\",\"args\":[],\"failure\":false,\"expected\":[\"0\",\"9\",\"2\"]}," ++
    "{\"signature\":\"overflow()\",\"args\":[],\"failure\":true,\"expected\":[]}," ++
    "{\"signature\":\"value()\",\"args\":[],\"failure\":false,\"expected\":[\"7\"]}]}"
  let data ← IO.ofExcept (Lean.Json.parse text)
  let result := Tools.Upstream.replay (if ir then Imported.IR.MappingAliases else Imported.MappingAliases)
    (if ir then Imported.IR.MappingAliases.report else Imported.MappingAliases.report) data
  unless (result.getObjValAs? String "status").toOption == some (if wrong then "broken" else "working") do
    throw (IO.userError result.pretty)
#eval check false false
#eval check true false
#eval check false true
#eval check true true

end Solidity.Upstream.MappingDeclarations
