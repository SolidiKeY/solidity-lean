import Solidity.Yul.World.EffectfulEmitSource

/-! Complete represented source/complement/owned-byte transport for the actual
persistent assignment inside an event argument. Layout is an explicit selected
one-byte input, not a universal solc-layout or G01 compiler certificate. -/
namespace Solidity.Yul.World.EffectfulEmitPort
open Solidity.Source
open Solidity.Roadmap (Address Word Bytes)
open Solidity.Yul.Views
open Solidity.Yul.World.PhysicalCompletion
open Solidity.Yul.World.EffectfulEmitSource
open Solidity.Yul.World.StaticEventEncoding

def flag (indexed anonymous : Bool) (a : Address) : ScalarPath (env indexed anonymous).layout ((env indexed anonymous).lay a) :=
  ⟨path,7,boolField,boolCodec _,.bool⟩
def registry (indexed anonymous : Bool) (a : Address) := [flag indexed anonymous a]
def request (a : Address) : PackedSlotRequest := ⟨false,a,7,0xaabbcc01⟩

theorem preserve_true {indexed anonymous f} (c : ScalarCodec (env indexed anonymous).layout ((env indexed anonymous).cellTy path) f)
    (cells : Source.Storage (env indexed anonymous).layout ((env indexed anonymous).lay (0 : Address))) :
    preserveScalarWrite path c (.bool true) cells=cells.write path (.bool true) := by
  unfold preserveScalarWrite
  split
  · rename_i same
    obtain ⟨old,read,encoded⟩ := Option.map_eq_some_iff.mp same
    have value : old=(.bool true : Source.Val (env indexed anonymous).layout ((env indexed anonymous).cellTy path)) := c.encode_injective encoded
    rw [value] at read
    have cell : cells.cell path=some (.bool true) := by
      cases found : cells.cell path with
      | none => simp only [Source.Storage.read,found] at read; cases read
      | some x => simpa only [Source.Storage.read,found] using read
    cases cells with
    | mk cells =>
      simp only [Source.Storage.write,Source.Storage.set,Source.Storage.mk.injEq]
      funext q
      by_cases samePath : q=path
      · subst q; simpa only [Source.Storage.cell,dif_pos] using cell
      · simp only [dif_neg samePath]
  · rfl

theorem selected_encoding (indexed anonymous : Bool) (a : Address) (b : BoolEncodingJournal) :
    (requestEncoding (E:=env indexed anonymous) (registry indexed anonymous) (registry indexed anonymous) (request a) b).cells
      (ownedByteKey false a (flag indexed anonymous a))=canonicalTrueByte := by
  have actual:=encodingWrites_result [flag indexed anonymous a] false a (fun _=>(request a).raw) b
    (by simp only [finiteSeparated,List.pairwise_singleton]) (flag indexed anonymous a) List.mem_cons_self
  change (requestEncoding (E:=env indexed anonymous) (registry indexed anonymous) (registry indexed anonymous) (request a) b).cells
    (ownedByteKey false a (flag indexed anonymous a))=chosenPathCode (flag indexed anonymous a)
      (b.cells (ownedByteKey false a (flag indexed anonymous a))) (fun _=>(request a).raw) at actual
  rw [actual]
  have typed : (env indexed anonymous).lay a (flag indexed anonymous a).path=.bool := by
    cases indexed <;> cases anonymous <;> rfl
  unfold chosenPathCode
  rw [dif_pos typed]
  have raw : fieldBooleanByte (flag indexed anonymous a).field ((flag indexed anonymous a).bool_width typed)
      ((flag indexed anonymous a).field.findWord ((request a).raw))=(⟨1,by decide⟩ : Fin 256) := by
    apply Fin.ext
    change (boolField.findWord (0xaabbcc01 : Word)).val=1
    decide +kernel
  rw [raw]
  rfl

theorem source_op {indexed anonymous} (a : Address) (b : BoolEncodingJournal)
    (p : RepresentedSlotPlan (E:=env indexed anonymous) (registry indexed anonymous) (registry indexed anonymous) (request a) b) :
    p.packed.sourceOp=writeOp a := by
  have checked:=p.packed.prepared
  rw [p.request_eq] at checked
  change finiteAccountWrite? a [representedPath (flag indexed anonymous a)
    ((requestEncoding (E:=env indexed anonymous) (registry indexed anonymous) (registry indexed anonymous) (request a) b).cells
      (ownedByteKey false a (flag indexed anonymous a)))] (fun _=>(request a).raw)=some p.packed.sourceOp at checked
  rw [selected_encoding] at checked
  have fixed : finiteAccountWrite? a [representedPath (flag indexed anonymous a) canonicalTrueByte]
      (fun _=>(request a).raw)=some (writeOp (indexed:=indexed) (anonymous:=anonymous) a) := by
    have encoded : (representedPath (flag indexed anonymous a) canonicalTrueByte).field.findWord ((request a).raw)=
        (representedPath (flag indexed anonymous a) canonicalTrueByte).codec.encode (.bool true) := by
      apply Fin.ext
      change (boolField.findWord (0xaabbcc01 : Word)).val=1
      decide +kernel
    unfold finiteAccountWrite?
    simp only [finitePrepare]
    rw [encoded,canonicalScalarDecode_encode]
    simp only [Option.bind_some,Option.map_some,id_eq]
    change some (Source.Op.account a (fun ac=>{ac with storage:=(preserveScalarWrite path (representedPath (flag indexed anonymous a) canonicalTrueByte).codec (.bool true) ac.storage)}))=_
    apply congrArg some
    apply congrArg (Source.Op.account a)
    funext ac
    rw [preserve_true]
    rfl
  exact Option.some.inj (checked.symm.trans fixed)

def values (indexed anonymous : Bool) : Vals (env indexed anonymous).layout [.bool] := .cons (.bool true) .nil
def part (indexed anonymous : Bool) : Split (env indexed anonymous).layout :=
  if indexed then ([1],⟨[],.nil⟩) else ([],⟨[.bool],values indexed anonymous⟩)
def dataWords (indexed : Bool) : List Word := if indexed then [] else [1]

theorem fits {indexed anonymous} (G : Glob (env indexed anonymous)) :
    (topics (ts:=[.bool]) G (declaration indexed anonymous) anonymous (part indexed anonymous)).length<5 := by
  cases indexed <;> cases anonymous <;> simp only [topics,part,Bool.false_eq_true,if_false,if_true,List.length_cons,List.length_nil] <;> decide

def log {indexed anonymous} (G : Glob (env indexed anonymous)) (F : Fr) : Log :=
  resultLog (ts:=[.bool]) G F (declaration indexed anonymous) anonymous (part indexed anonymous) (fits G)
    (Source.abiLayout ((dataWords indexed).map (fun w=>(false,wordBytes w))))

theorem format {indexed anonymous Γ} (G : Glob (env indexed anonymous)) (F : Fr) (s : EMState (env indexed anonymous) Γ) :
    (encode G F 8 (declaration indexed anonymous) rfl (values indexed anonymous)).run s=(.ok (some (log G F)),s) := by
  apply encode_exact G F 8 (declaration indexed anonymous) rfl (values indexed anonymous) s [indexed] anonymous
    (by simp only [metadata,EffectfulEmitSource.declaration,indexedFlags]) (part indexed anonymous)
    (by cases indexed <;> rfl) (dataWords indexed)
    (by cases indexed <;> rfl) (fits G)

/-- Operational driver for a selected raw request; by itself this is NOT
arbitrary-carrier adequacy of typed assignment. Use checkedExecute? to validate
the actual before-view and complement before effectful evaluation. -/
def execute {indexed anonymous Γ} (G : Glob (env indexed anonymous)) (F : Fr)
    (s : EMState (env indexed anonymous) Γ) (r : ResidualJournal complementCarrierOwnership)
    (b : BoolEncodingJournal)
    (p : RepresentedSlotPlan (E:=env indexed anonymous) (registry indexed anonymous) (registry indexed anonymous) (request F.this) b)
    (o : ObservedEffects (env indexed anonymous).layout (env indexed anonymous).lay (env indexed anonymous).lay)
    (shared : o.effects.execution=s.2.ex) :
    (Except Halt Unit × Carrier (env indexed anonymous) Γ) ×
      ObservedEffects (env indexed anonymous).layout (env indexed anonymous).lay (env indexed anonymous).lay :=
  let actual:=source G F s
  match actual.1 with
  | .error error => ((.error error,(⟨⟨actual.2,r⟩,b⟩ : Carrier (env indexed anonymous) Γ)),o)
  | .ok _ =>
    let physical:=PhysicalSlotPort.step (registry indexed anonymous) (registry indexed anonymous) (request F.this) b F p s r o shared rfl
    ((physical.1.1.1.1,(⟨⟨actual.2,physical.1.1.2⟩,physical.1.2⟩ : Carrier (env indexed anonymous) Γ)),
      emitObserved physical.2 (log G F))

def completed {indexed anonymous Γ} (G : Glob (env indexed anonymous)) (F : Fr)
    (s : EMState (env indexed anonymous) Γ) (r : ResidualJournal complementCarrierOwnership)
    (b : BoolEncodingJournal)
    (p : RepresentedSlotPlan (E:=env indexed anonymous) (registry indexed anonymous) (registry indexed anonymous) (request F.this) b)
    (o : ObservedEffects (env indexed anonymous).layout (env indexed anonymous).lay (env indexed anonymous).lay) :
    (Except Halt Unit × Carrier (env indexed anonymous) Γ) ×
      ObservedEffects (env indexed anonymous).layout (env indexed anonymous).lay (env indexed anonymous).lay :=
  ((.ok (), (⟨⟨after G F s,residualWrite r p.packed.residualUpdate⟩,
    requestEncoding (E:=env indexed anonymous) (registry indexed anonymous) (registry indexed anonymous) (request F.this) b⟩ : Carrier (env indexed anonymous) Γ)),
   emitObserved {o with effects:={o.effects with execution:=(changed F s).2.ex}} (log G F))

theorem execute_normal {indexed anonymous Γ} (G : Glob (env indexed anonymous)) (F : Fr)
    (normal : F.static=false) (s : EMState (env indexed anonymous) Γ)
    (r : ResidualJournal complementCarrierOwnership) (b : BoolEncodingJournal)
    (p : RepresentedSlotPlan (E:=env indexed anonymous) (registry indexed anonymous) (registry indexed anonymous) (request F.this) b)
    (o : ObservedEffects (env indexed anonymous).layout (env indexed anonymous).lay (env indexed anonymous).lay)
    (shared : o.effects.execution=s.2.ex) :
    execute G F s r b p o shared=completed G F s r b p o := by
  unfold execute
  rw [source_actual G F normal]
  unfold PhysicalSlotPort.step
  rw [representedSourceStep_nonstatic _ _ _ _ normal,source_op]
  rfl

theorem execute_static {indexed anonymous Γ} (G : Glob (env indexed anonymous)) (F : Fr)
    (refused : F.static=true) (s : EMState (env indexed anonymous) Γ)
    (r : ResidualJournal complementCarrierOwnership) (b : BoolEncodingJournal)
    (p : RepresentedSlotPlan (E:=env indexed anonymous) (registry indexed anonymous) (registry indexed anonymous) (request F.this) b)
    (o : ObservedEffects (env indexed anonymous).layout (env indexed anonymous).lay (env indexed anonymous).lay)
    (shared : o.effects.execution=s.2.ex) :
    execute G F s r b p o shared=((.error (.revert []),⟨⟨s,r⟩,b⟩),o) := by
  unfold execute
  rw [source_static G F refused]
/-- The actual before-view is obtained from the producer's full coupled
source/complement/owned-byte carriers. None is adapter input refusal. -/
def beforeWord {indexed anonymous Γ} (F : Fr) (s : EMState (env indexed anonymous) Γ)
    (r : ResidualJournal complementCarrierOwnership) (b : BoolEncodingJournal) : Option Word :=
  reencodePersistentSlot (representedBanks (registry indexed anonymous) false b) ⟨s.2.ex,r⟩ F.this 7

/-- Restricted fixed-layout adapter. Check both actual before-view and exact
padding BEFORE running the effectful Source expression. Other padding is not
an EVM/Source failure; it is outside this selected request's physical domain. -/
def checkedExecute? {indexed anonymous Γ} (G : Glob (env indexed anonymous)) (F : Fr)
    (s : EMState (env indexed anonymous) Γ) (r : ResidualJournal complementCarrierOwnership)
    (b : BoolEncodingJournal) (o : ObservedEffects (env indexed anonymous).layout (env indexed anonymous).lay (env indexed anonymous).lay)
    (shared : o.effects.execution=s.2.ex) :=
  match beforeWord F s r b with
  | none => none
  | some old =>
    if r.cells (complementKey false F.this 7)=0xaabbcc00 ∧
        boolField.saveWord old ((boolCodec (env indexed anonymous).layout).encode (.bool true))=(request F.this).raw then
      (prepareRepresentedSlot (E:=env indexed anonymous) (registry indexed anonymous) (registry indexed anonymous) (request F.this) b).map
        (fun p=>execute G F s r b p o shared)
    else none

theorem checked_padding_refusal {indexed anonymous Γ} (G : Glob (env indexed anonymous)) (F : Fr)
    (s : EMState (env indexed anonymous) Γ) (r : ResidualJournal complementCarrierOwnership)
    (b : BoolEncodingJournal) (o : ObservedEffects (env indexed anonymous).layout (env indexed anonymous).lay (env indexed anonymous).lay)
    (shared : o.effects.execution=s.2.ex) (different : r.cells (complementKey false F.this 7)≠0xaabbcc00) :
    checkedExecute? G F s r b o shared=none := by
  unfold checkedExecute?
  cases beforeWord F s r b with
  | none => rfl
  | some old => simp only [different,false_and,if_false]

theorem checked_actual {indexed anonymous Γ} (G : Glob (env indexed anonymous)) (F : Fr)
    (s : EMState (env indexed anonymous) Γ) (r : ResidualJournal complementCarrierOwnership)
    (b : BoolEncodingJournal) (o : ObservedEffects (env indexed anonymous).layout (env indexed anonymous).lay (env indexed anonymous).lay)
    (shared : o.effects.execution=s.2.ex) (old : Word)
    (view : beforeWord F s r b=some old)
    (padding : r.cells (complementKey false F.this 7)=0xaabbcc00)
    (patch : boolField.saveWord old ((boolCodec (env indexed anonymous).layout).encode (.bool true))=(request F.this).raw)
    (p : RepresentedSlotPlan (E:=env indexed anonymous) (registry indexed anonymous) (registry indexed anonymous) (request F.this) b)
    (prepared : prepareRepresentedSlot (E:=env indexed anonymous) (registry indexed anonymous) (registry indexed anonymous) (request F.this) b=some p) :
    checkedExecute? G F s r b o shared=some (execute G F s r b p o shared) := by
  simp only [checkedExecute?,view,padding,patch,and_self,if_true,prepared,Option.map_some]

theorem checked_normal {indexed anonymous Γ} (G : Glob (env indexed anonymous)) (F : Fr)
    (normal : F.static=false) (s : EMState (env indexed anonymous) Γ) (r : ResidualJournal complementCarrierOwnership)
    (b : BoolEncodingJournal) (o : ObservedEffects (env indexed anonymous).layout (env indexed anonymous).lay (env indexed anonymous).lay)
    (shared : o.effects.execution=s.2.ex) (old : Word)
    (view : beforeWord F s r b=some old)
    (padding : r.cells (complementKey false F.this 7)=0xaabbcc00)
    (patch : boolField.saveWord old ((boolCodec (env indexed anonymous).layout).encode (.bool true))=(request F.this).raw)
    (p : RepresentedSlotPlan (E:=env indexed anonymous) (registry indexed anonymous) (registry indexed anonymous) (request F.this) b)
    (prepared : prepareRepresentedSlot (E:=env indexed anonymous) (registry indexed anonymous) (registry indexed anonymous) (request F.this) b=some p) :
    checkedExecute? G F s r b o shared=some (completed G F s r b p o) := by
  rw [checked_actual G F s r b o shared old view padding patch p prepared,
    execute_normal G F normal s r b p o shared]

theorem execute_shared {indexed anonymous Γ} (G : Glob (env indexed anonymous)) (F : Fr)
    (normal : F.static=false) (s : EMState (env indexed anonymous) Γ)
    (r : ResidualJournal complementCarrierOwnership) (b : BoolEncodingJournal)
    (p : RepresentedSlotPlan (E:=env indexed anonymous) (registry indexed anonymous) (registry indexed anonymous) (request F.this) b)
    (o : ObservedEffects (env indexed anonymous).layout (env indexed anonymous).lay (env indexed anonymous).lay)
    (shared : o.effects.execution=s.2.ex) :
    (execute G F s r b p o shared).2.effects.execution=(execute G F s r b p o shared).1.2.1.1.2.ex := by
  rw [execute_normal G F normal s r b p o shared]
  rfl

theorem execute_word {indexed anonymous Γ} (G : Glob (env indexed anonymous)) (F : Fr)
    (normal : F.static=false) (s : EMState (env indexed anonymous) Γ)
    (r : ResidualJournal complementCarrierOwnership) (b : BoolEncodingJournal)
    (p : RepresentedSlotPlan (E:=env indexed anonymous) (registry indexed anonymous) (registry indexed anonymous) (request F.this) b)
    (o : ObservedEffects (env indexed anonymous).layout (env indexed anonymous).lay (env indexed anonymous).lay)
    (shared : o.effects.execution=s.2.ex) :
    let result := execute G F s r b p o shared
    reencodePersistentSlot (representedBanks (registry indexed anonymous) false result.1.2.2)
      ⟨result.1.2.1.1.2.ex,result.1.2.1.2⟩ F.this 7=some (request F.this).raw := by
  dsimp only
  rw [←execute_shared G F normal s r b p o shared]
  have physical := PhysicalSlotPort.persistent_word F p s r o shared rfl normal rfl
    (by simp only [registry,finiteSeparated,List.pairwise_singleton])
  simpa only [execute,source_actual G F normal,emitObserved] using physical

/-- A successful checked adapter writes exactly the typed bool field update
of its actual before-word. No requested target result is a premise. -/
theorem checked_word {indexed anonymous Γ} (G : Glob (env indexed anonymous)) (F : Fr)
    (normal : F.static=false) (s : EMState (env indexed anonymous) Γ)
    (r : ResidualJournal complementCarrierOwnership) (b : BoolEncodingJournal)
    (o : ObservedEffects (env indexed anonymous).layout (env indexed anonymous).lay (env indexed anonymous).lay)
    (shared : o.effects.execution=s.2.ex) (result)
    (done : checkedExecute? G F s r b o shared=some result) :
    ∃ old, beforeWord F s r b=some old ∧
      reencodePersistentSlot (representedBanks (registry indexed anonymous) false result.1.2.2)
        ⟨result.1.2.1.1.2.ex,result.1.2.1.2⟩ F.this 7=
        some (boolField.saveWord old ((boolCodec (env indexed anonymous).layout).encode (.bool true))) := by
  unfold checkedExecute? at done
  cases view : beforeWord F s r b with
  | none => rw [view] at done; cases done
  | some old =>
    rw [view] at done
    simp only [] at done
    by_cases aligned : r.cells (complementKey false F.this 7)=0xaabbcc00 ∧
      boolField.saveWord old ((boolCodec (env indexed anonymous).layout).encode (.bool true))=(request F.this).raw
    · rw [if_pos aligned] at done
      obtain ⟨p,prepared,same⟩ := Option.map_eq_some_iff.mp done
      subst result
      refine ⟨old,rfl,?_⟩
      rw [aligned.2]
      exact execute_word G F normal s r b p o shared
    · rw [if_neg aligned] at done
      cases done

theorem complement_update {indexed anonymous} (a : Address) (b : BoolEncodingJournal)
    (p : RepresentedSlotPlan (E:=env indexed anonymous) (registry indexed anonymous) (registry indexed anonymous) (request a) b) :
    p.packed.residualUpdate=(complementKey false a 7,0xaabbcc00) := by
  unfold PackedSlotPlan.residualUpdate
  rw [p.request_eq]
  have mask : packedCarrierOwns
      (representedBanks (registry indexed anonymous) false
        (requestEncoding (registry indexed anonymous) (registry indexed anonymous) (request a) b))
      (representedBanks (registry indexed anonymous) true
        (requestEncoding (registry indexed anonymous) (registry indexed anonymous) (request a) b))
      (complementKey false a 7) = fun i => decide (i.val < 1) := by
    funext i
    simp only [packedCarrierOwns, complementKey, Bool.false_eq_true, if_false,
      representedBanks, registry, representedRegistry, List.map_cons, List.map_nil,
      packedOwnsByte, List.any_cons, List.any_nil, representedPath_slot,
      representedPath_field, Bool.or_false, flag]
    simp only [boolField, Nat.zero_le, Nat.zero_add, true_and]
  change (complementKey false a 7, complementWord _ (0xaabbcc01 : Word))=_
  simp only [request] at mask ⊢
  rw [mask]
  apply congrArg (fun w : Word => (complementKey false a 7,w))
  decide +kernel

theorem execute_padding {indexed anonymous Γ} (G : Glob (env indexed anonymous)) (F : Fr)
    (normal : F.static=false) (s : EMState (env indexed anonymous) Γ)
    (r : ResidualJournal complementCarrierOwnership) (b : BoolEncodingJournal)
    (p : RepresentedSlotPlan (E:=env indexed anonymous) (registry indexed anonymous) (registry indexed anonymous) (request F.this) b)
    (o : ObservedEffects (env indexed anonymous).layout (env indexed anonymous).lay (env indexed anonymous).lay)
    (shared : o.effects.execution=s.2.ex) (padding : r.cells (complementKey false F.this 7)=0xaabbcc00) :
    (execute G F s r b p o shared).1.2.1.2.cells=r.cells := by
  rw [execute_normal G F normal s r b p o shared]
  change (residualWrite r p.packed.residualUpdate).cells=r.cells
  rw [complement_update]
  change residualSave r.cells (complementKey false F.this 7) (0xaabbcc00 : Word)=r.cells
  funext key
  unfold residualSave
  split
  · rename_i same
    subst key
    exact padding.symm
  · rfl

end Solidity.Yul.World.EffectfulEmitPort
