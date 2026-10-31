import Solidity.Semantics.ContractWorld

/-! Independent refusal/role/callee controls for the published world interface.
These are intrinsic controls, not compiled calls or a readonly implementation. -/
namespace Solidity.Backend.AbiWorld.PublishedCallControls
open ContractWorld
variable {K : Type} [DecidableEq K] {contracts : K → Contract} {α : Type}

/-- Every result signature retains the published nonempty-static-body refusal. -/
theorem static_frame_refused (w : World contracts) {k : K} (r : Handle k)
    (entry : Entry (contracts k) α) (ctx : Context)
    (hs : ctx.isStatic = true) (hb : emptyBody entry.body = false) :
    w.callFrame r entry ctx = .error .revert := by
  simp only [World.callFrame, hs, hb, Bool.not_false, Bool.true_and, Bool.or_true, ite_true]

/-- The same static restriction applies to linked library entries at caller types. -/
theorem static_library_refused (w : World contracts) {k : K} (r : Handle k)
    (library : Library contracts k α) (ctx : Context)
    (hs : ctx.isStatic = true) (hb : emptyBody library.entry.body = false) :
    w.libraryCall r library ctx = .error .revert := by
  simp only [World.libraryCall, hs, hb, Bool.not_false, Bool.true_and, Bool.or_true, ite_true]

/-- Being cast to a typed handle supplies no installed-callee premise. -/
theorem absent_callee_refused (w : World contracts) {k : K} (r : Handle k)
    (entry : Entry (contracts k) α) (ctx : Context)
    (hg : (w.isLibrary k || (ctx.isStatic && !(emptyBody entry.body))) = false)
    (hc : w.storage? r = none) : w.callFrame r entry ctx = .error .revert := by
  simp only [World.callFrame, hg, Bool.false_eq_true, ite_false, hc]
  rfl

private def contract : Contract := { vars := [] }
private def catalog (_ : Bool) : Contract := contract
private def address : Address := ⟨⟨7, by decide +kernel⟩, by decide +kernel⟩
private def reference : Handle false := ⟨address⟩
private def context : Context := ⟨address, .readOnly, []⟩
private def entry : Entry contract (Bool × List UInt8) :=
  ⟨[], .cons (.require (.simple (.bool true))) .nil, fun _ => .ok (true, [1, 2]), false⟩
private def world : World catalog := World.empty catalog (fun _ => PrimTy.dflt .uint)
private def libraryAddress : Address := ⟨⟨8, by decide +kernel⟩, by decide +kernel⟩
private def library : Library catalog false (Bool × List UInt8) := ⟨true, libraryAddress, entry⟩
private def installed : World catalog := {
  accounts := fun a => if a = address then some ⟨false, (State.init contract).storage⟩
    else if a = libraryAddress then some ⟨true, (State.init contract).storage⟩ else none,
  funds := fun _ => PrimTy.dflt .uint,
  roles := fun k => if k then .libraryCode else .contractCode }


/-- Inhabited self-address and paired result-type static/library combination. -/
theorem self_static_library_combination :
    installed.callFrame reference entry context = .error .revert ∧
      installed.libraryCall reference library context = .error .revert := by
  exact ⟨static_frame_refused _ _ _ _ rfl rfl, static_library_refused _ _ _ _ rfl rfl⟩

/-- Removing either static guard would turn the previous refusal into this success. -/
theorem installed_nonstatic_success :
    (installed.call reference entry { context with mode := .ordinary (PrimTy.dflt .uint) }).map Prod.snd =
      .ok (true, [1, 2]) ∧
    (installed.libraryCall reference library { context with mode := .ordinary (PrimTy.dflt .uint) }).map Prod.snd =
      .ok (true, [1, 2]) := by
  constructor <;> rfl

/-- Even an empty self-address entry requires actual installed typed code. -/
theorem absent_self_callee :
    world.callFrame reference (Entry.unit .nil) context = .error .revert :=
  absent_callee_refused _ _ _ _ rfl rfl

/-- Library roles remain checked even with an empty body and nonstatic context. -/
theorem missing_library_role :
    world.libraryCall reference
      (⟨true, address, Entry.unit .nil⟩ : Library catalog false Unit)
      { context with mode := .ordinary (PrimTy.dflt .uint) } = .error .revert := rfl

/-- info: 'Solidity.Backend.AbiWorld.PublishedCallControls.static_frame_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms static_frame_refused
/-- info: 'Solidity.Backend.AbiWorld.PublishedCallControls.absent_callee_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms absent_callee_refused
/-- info: 'Solidity.Backend.AbiWorld.PublishedCallControls.self_static_library_combination' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms self_static_library_combination
end Solidity.Backend.AbiWorld.PublishedCallControls
