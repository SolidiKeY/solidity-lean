import Solidity.Lowering.V08.WorldCatalogueTransport
import Solidity.Lowering.V08.LibraryFrameTransport

/-! Typed installed-store lookup from the actual image and independent source
code/name/kind equations. No name-map injectivity, runtime producer or desired
execution-preservation equation is assumed. -/
namespace Solidity.Lowering.V08.WorldImageAccess
open Solidity
variable {E : Source.Env} {K : Type} {contracts : K → Contract}
  {g : Source.Glob E} {kindOf : String → Option K}
  {relation : WorldImage.StoreRelation E contracts}
  {environment : Roadmap.SessionEnv} {history : List Roadmap.Event}
  {source : Source.St E} {target : ContractWorld.World contracts}

theorem installed_store
    (image : WorldImage.Image g kindOf relation environment history source target)
    (address : Roadmap.Address) (code : Nat) (name : String) (kind : K)
    (atCode : (source.ex.world.accounts address).code = some code)
    (selected : g.contractAt code = some name) (linked : kindOf name = some kind) :
    ∃ store : Storage (contracts kind),
      target.accounts (EnvironmentProjection.liftAddress address) = some ⟨kind,store⟩ ∧
      relation address kind (source.ex.world.accounts address).storage
        (source.ex.transient.cells address) store := by
  have account := image.accounts (EnvironmentProjection.liftAddress address)
  unfold WorldImage.AccountImage at account
  dsimp only at account
  rw [EnvironmentProjection.lower_lift_address, atCode] at account
  obtain ⟨otherName, otherKind, store, otherSelected, otherLinked, installed, represented⟩ := account
  have sameName : otherName = name := Option.some.inj (otherSelected.symm.trans selected)
  subst otherName
  have sameKind : otherKind = kind := Option.some.inj (otherLinked.symm.trans linked)
  subst otherKind
  exact ⟨store, installed, represented⟩

/-- Typed handle lookup retains the very same dependent store, rather than
identifying account framing with any body or readonly preservation law. -/
theorem account_lookup [DecidableEq K] (address : ContractWorld.Address)
    (kind : K) (store : Storage (contracts kind))
    (installed : target.accounts address = some ⟨kind,store⟩) :
    target.storage? (⟨address⟩ : ContractWorld.Handle kind) = some store := by
  simp only [ContractWorld.World.storage?, installed, bind, Option.bind]
  rfl

/-- Source code/name/kind selection yields an actual typed lookup and the
original persistent/transient relation. No whole-execution premise is used. -/
theorem installed_lookup [DecidableEq K]
    (image : WorldImage.Image g kindOf relation environment history source target)
    (address : Roadmap.Address) (code : Nat) (name : String) (kind : K)
    (atCode : (source.ex.world.accounts address).code = some code)
    (selected : g.contractAt code = some name) (linked : kindOf name = some kind) :
    ∃ store : Storage (contracts kind),
      target.storage? (⟨EnvironmentProjection.liftAddress address⟩ : ContractWorld.Handle kind) = some store ∧
      relation address kind (source.ex.world.accounts address).storage
        (source.ex.transient.cells address) store := by
  obtain ⟨store, installed, represented⟩ :=
    installed_store image address code name kind atCode selected linked
  exact ⟨store, account_lookup _ _ store installed, represented⟩

/-- Library account/role inputs follow from source catalogue evidence and the
image; neither body success nor a runtime-input certificate is a premise. -/
theorem library_inputs [DecidableEq K]
    (image : WorldImage.Image g kindOf relation environment history source target)
    (callerAddress libraryAddress : Roadmap.Address) (callerCode libraryCode : Nat)
    (callerName libraryName : String) (caller library : K)
    (callerInstalled : (source.ex.world.accounts callerAddress).code = some callerCode)
    (libraryInstalled : (source.ex.world.accounts libraryAddress).code = some libraryCode)
    (callerSelected : g.contractAt callerCode = some callerName)
    (librarySelected : g.contractAt libraryCode = some libraryName)
    (callerLinked : kindOf callerName = some caller)
    (libraryLinked : kindOf libraryName = some library)
    (callerRole : WorldImage.sourceLibrary E callerName = false)
    (libraryRole : WorldImage.sourceLibrary E libraryName = true) :
    Nonempty (LibraryFrameTransport.RuntimeInputs target caller library
      ⟨EnvironmentProjection.liftAddress callerAddress⟩
      (EnvironmentProjection.liftAddress libraryAddress)) := by
  obtain ⟨callerStore, callerAccount, _⟩ := installed_store image callerAddress callerCode
    callerName caller callerInstalled callerSelected callerLinked
  obtain ⟨libraryStore, libraryAccount, _⟩ := installed_store image libraryAddress libraryCode
    libraryName library libraryInstalled librarySelected libraryLinked
  exact ⟨⟨libraryStore, callerStore,
    (image.roles libraryName library libraryLinked).trans libraryRole,
    (image.roles callerName caller callerLinked).trans callerRole,
    libraryAccount, callerAccount⟩⟩

/-- Changing only the actual world clock preserves Image, precisely because
its account/store/funds/role fields contain no clock equation. -/
theorem image_atTime
    (image : WorldImage.Image g kindOf relation environment history source target)
    (timestamp : Semantics.Word) :
    WorldImage.Image g kindOf relation environment history source (target.atTime timestamp) := by
  exact ⟨image.accounts,image.funds,image.roles⟩

/-- Actual Source execution and an existing Context.tx frame timestamp read.
Clock agreement is explicit; no arbitrary World equality or admitted body/frame
execution is inferred from the account image. -/
theorem timestamp_frame {Γ : Source.RCtx} (clock : WorldImage.TimeAligned g target)
    (frame : Source.Fr) (horizon : Nat) (locals : Source.Locals E.layout Γ)
    (caller : K) (owner : ContractWorld.Handle caller) (context : ContractWorld.Context)
    (store : Storage (contracts caller)) :
    (Source.evalE g frame (horizon+1)
      (.magic .block "timestamp" rfl : Source.RExpr E Γ (.int Source.IntTy.u256))).run (locals,source) =
      (.ok (.val (SourceEnvironment.sourceWord g.timestamp)),(locals,source)) ∧
    (Solidity.Val.simple (.env .timestamp rfl) : Solidity.Val (contracts caller) [] .uint).evalT
      (LibraryFrameTransport.emptyFrame target owner context store) =
      .ok (EnvironmentProjection.liftWord g.timestamp) := by
  refine ⟨SourceEnvironment.eval_timestamp g frame horizon locals source, ?_⟩
  change (Except.ok target.timestamp : TRes Semantics.Word) = _
  exact congrArg Except.ok clock

/-- info: 'Solidity.Lowering.V08.WorldImageAccess.installed_store' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms installed_store
/-- info: 'Solidity.Lowering.V08.WorldImageAccess.account_lookup' depends on axioms: [propext] -/
#guard_msgs in
#print axioms account_lookup
/-- info: 'Solidity.Lowering.V08.WorldImageAccess.installed_lookup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms installed_lookup
/-- info: 'Solidity.Lowering.V08.WorldImageAccess.library_inputs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms library_inputs
/-- info: 'Solidity.Lowering.V08.WorldImageAccess.image_atTime' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms image_atTime
/-- info: 'Solidity.Lowering.V08.WorldImageAccess.timestamp_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms timestamp_frame
/-- A real journaled balance replacement leaves the account image's code and
persistent/transient store observations unchanged. This says nothing about
Image.funds or the whole Source state: the journal and balance really change. -/
theorem account_balance (owner : Roadmap.Address) (amount : Source.Monetary.Balance)
    (address : ContractWorld.Address) :
    WorldImage.AccountImage g kindOf relation
      {source with ex := source.ex.apply (.account owner (fun account => account.withBalance amount))}
      target address ↔ WorldImage.AccountImage g kindOf relation source target address := by
  unfold WorldImage.AccountImage
  by_cases same : EnvironmentProjection.lowerAddress address = owner
  · subst owner
    simp only [Source.ExecState.apply, Source.World.set_get, Source.Account.withBalance]
  · simp only [Source.ExecState.apply, Source.World.set_other source.ex.world same]

/-- Success is supplied by the actual transfer Option equation, not a desired
image equation. Same-owner success and both distinct-owner journal updates
preserve exactly the code/store component; funds remain a separate obligation. -/
theorem account_transfer (sender recipient : Roadmap.Address) (amount : Roadmap.Word)
    (after : Source.ExecState E.layout E.lay E.lay)
    (paid : source.ex.transfer sender recipient amount = some after)
    (address : ContractWorld.Address) :
    WorldImage.AccountImage g kindOf relation {source with ex := after} target address ↔
      WorldImage.AccountImage g kindOf relation source target address := by
  unfold Source.ExecState.transfer Source.ExecState.transferNat at paid
  dsimp only at paid
  split at paid
  · split at paid
    · cases (Option.some.inj paid)
      rfl
    · cases paid
  · split at paid
    · cases (Option.some.inj paid)
      exact (account_balance
        (source := {source with ex := source.ex.apply (.account sender (fun account =>
          account.withBalance ((source.ex.world.accounts sender).balance - amount.val)))})
        recipient ((source.ex.world.accounts recipient).balance + amount.val) address).trans
        (account_balance sender _ address)
    · cases paid

/-- info: 'Solidity.Lowering.V08.WorldImageAccess.account_balance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms account_balance
/-- info: 'Solidity.Lowering.V08.WorldImageAccess.account_transfer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms account_transfer

end Solidity.Lowering.V08.WorldImageAccess


/-! Converse catalogue facts concern the initial image and actual typed lookup,
not execution/body/catch/admission or complete World equality. The exact store
relation survives reflection; no functionality/injectivity of that relation or
the source-name map is assumed. -/
namespace Solidity.Lowering.V08.WorldImageAccess
open Solidity
variable {E : Source.Env} {K : Type} [DecidableEq K] {contracts : K → Contract}
  {g : Source.Glob E} {kindOf : String → Option K}
  {relation : WorldImage.StoreRelation E contracts}
  {environment : Roadmap.SessionEnv} {history : List Roadmap.Event}
  {source : Source.St E} {target : ContractWorld.World contracts}

theorem lookup_reflect
    (image : WorldImage.Image g kindOf relation environment history source target)
    (address : Roadmap.Address) (kind : K) (store : Storage (contracts kind))
    (lookup : target.storage? (⟨EnvironmentProjection.liftAddress address⟩ : ContractWorld.Handle kind) = some store) :
    ∃ code name, (source.ex.world.accounts address).code = some code ∧
      g.contractAt code = some name ∧ kindOf name = some kind ∧
      relation address kind (source.ex.world.accounts address).storage (source.ex.transient.cells address) store := by
  have actual := LibraryFrameTransport.account_of_lookup target _ store lookup
  have account := image.accounts (EnvironmentProjection.liftAddress address)
  unfold WorldImage.AccountImage at account
  dsimp only at account
  rw [EnvironmentProjection.lower_lift_address] at account
  cases code : (source.ex.world.accounts address).code with
  | none =>
    rw [code] at account
    rw [account] at actual
    cases actual
  | some index =>
    rw [code] at account
    obtain ⟨name,otherKind,otherStore,selected,linked,installed,represented⟩ := account
    have pair := Option.some.inj (installed.symm.trans actual)
    have sameKind : otherKind = kind := congrArg (fun entry : (k : K) × Storage (contracts k) => entry.1) pair
    subst otherKind
    have sameStore : otherStore = store := Option.some.inj ((account_lookup _ kind otherStore installed).symm.trans lookup)
    subst otherStore
    exact ⟨index,name,rfl,selected,linked,represented⟩

/-- Existential lookup is two-sided without assuming that StoreRelation is
functional. A relation alone cannot choose an arbitrary exact target store. -/
theorem lookup_some_iff
    (image : WorldImage.Image g kindOf relation environment history source target)
    (address : Roadmap.Address) (kind : K) :
    (∃ store, target.storage? (⟨EnvironmentProjection.liftAddress address⟩ : ContractWorld.Handle kind) = some store) ↔
    ∃ code name, (source.ex.world.accounts address).code = some code ∧
      g.contractAt code = some name ∧ kindOf name = some kind := by
  constructor
  · rintro ⟨store,lookup⟩
    obtain ⟨code,name,present,selected,linked,_⟩ := lookup_reflect image address kind store lookup
    exact ⟨code,name,present,selected,linked⟩
  · rintro ⟨code,name,present,selected,linked⟩
    obtain ⟨store,lookup,_⟩ := installed_lookup image address code name kind present selected linked
    exact ⟨store,lookup⟩

theorem lookup_none_iff
    (image : WorldImage.Image g kindOf relation environment history source target)
    (address : Roadmap.Address) (kind : K) :
    target.storage? (⟨EnvironmentProjection.liftAddress address⟩ : ContractWorld.Handle kind) = none ↔
      ¬ ∃ code name, (source.ex.world.accounts address).code = some code ∧
        g.contractAt code = some name ∧ kindOf name = some kind := by
  constructor
  · intro empty present
    obtain ⟨store,lookup⟩ := (lookup_some_iff image address kind).mpr present
    rw [empty] at lookup
    cases lookup
  · intro absent
    cases lookup : target.storage? (⟨EnvironmentProjection.liftAddress address⟩ : ContractWorld.Handle kind) with
    | none => rfl
    | some store => exact False.elim (absent ((lookup_some_iff image address kind).mp ⟨store,lookup⟩))

theorem lookup_none_of_code_absent
    (image : WorldImage.Image g kindOf relation environment history source target)
    (address : Roadmap.Address) (kind : K)
    (absent : (source.ex.world.accounts address).code = none) :
    target.storage? (⟨EnvironmentProjection.liftAddress address⟩ : ContractWorld.Handle kind) = none := by
  apply (lookup_none_iff image address kind).mpr
  rintro ⟨code,name,present,_,_⟩
  rw [absent] at present
  cases present

theorem lookup_none_of_kind_mismatch
    (image : WorldImage.Image g kindOf relation environment history source target)
    (address : Roadmap.Address) (code : Nat) (name : String) (kind : K)
    (present : (source.ex.world.accounts address).code = some code)
    (selected : g.contractAt code = some name) (mismatch : kindOf name ≠ some kind) :
    target.storage? (⟨EnvironmentProjection.liftAddress address⟩ : ContractWorld.Handle kind) = none := by
  apply (lookup_none_iff image address kind).mpr
  rintro ⟨otherCode,otherName,otherPresent,otherSelected,otherLinked⟩
  have sameCode : otherCode = code := Option.some.inj (otherPresent.symm.trans present)
  subst otherCode
  have sameName : otherName = name := Option.some.inj (otherSelected.symm.trans selected)
  subst otherName
  exact mismatch otherLinked

/-- info: 'Solidity.Lowering.V08.WorldImageAccess.lookup_reflect' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.WorldImageAccess.lookup_reflect
/-- info: 'Solidity.Lowering.V08.WorldImageAccess.lookup_some_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.WorldImageAccess.lookup_some_iff
/-- info: 'Solidity.Lowering.V08.WorldImageAccess.lookup_none_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.WorldImageAccess.lookup_none_iff
/-- info: 'Solidity.Lowering.V08.WorldImageAccess.lookup_none_of_code_absent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.WorldImageAccess.lookup_none_of_code_absent
/-- info: 'Solidity.Lowering.V08.WorldImageAccess.lookup_none_of_kind_mismatch' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.WorldImageAccess.lookup_none_of_kind_mismatch
end Solidity.Lowering.V08.WorldImageAccess
