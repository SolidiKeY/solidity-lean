import Solidity.Yul.ScalarLocals
import Init.Data.List.Range

/-! Concrete enumeration and classification of the ORIGINAL S01 local context.
All entries retain intrinsic Source indices and exact declaration-backed types.
This is a local-context adapter, not whole-block/source-ID/global construction
or execution/pipeline refinement. Unsupported locals must still shadow globals. -/
namespace Solidity.Yul

abbrev Occurrence (X : List α) := (ty : α) × Member X ty

def allOccurrences : (types : List α) → List (Occurrence types)
  | [] => []
  | head :: rest => ⟨head,.here⟩ :: (allOccurrences rest).map
      (fun ⟨ty,index⟩ => ⟨ty,.there index⟩)

theorem allOccurrences_complete {types : List α} {ty : α} (index : Member types ty) :
    (⟨ty,index⟩ : Occurrence types) ∈ allOccurrences types := by
  induction index with
  | here => exact List.mem_cons_self
  | @there a b rest previous ih =>
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨⟨a,previous⟩,ih,rfl⟩)

theorem allOccurrences_positions (types : List α) :
    (allOccurrences types).map (fun occurrence => occurrence.2.position) = List.range types.length := by
  induction types with
  | nil => rfl
  | cons head rest ih =>
    change 0 :: ((allOccurrences rest).map (fun ⟨ty,index⟩ =>
      (⟨ty,Member.there (b := head) index⟩ : Occurrence (head::rest)))).map
        (fun occurrence => occurrence.2.position) = _
    rw [List.map_map]
    change 0 :: (allOccurrences rest).map (fun occurrence => occurrence.2.position + 1) = _
    have expand : (allOccurrences rest).map (fun occurrence => occurrence.2.position + 1) =
        ((allOccurrences rest).map (fun occurrence => occurrence.2.position)).map Nat.succ := by
      rw [List.map_map]
      rfl
    rw [expand,ih]
    exact List.range_succ_eq_map.symm

theorem memberSourceIndex_position {types : Solidity.Source.RCtx} {ty}
    (index : Member types ty) :
    (memberSourceIndex index).toNat = index.position := by
  induction index with
  | here => rfl
  | there previous ih => exact congrArg Nat.succ ih

def allSourceRefs (ctx : Solidity.Source.Ctx) : List (SourceLocalRef ctx) :=
  (allOccurrences ctx.tys).map (sourceRefFromPayload ctx)

theorem allSourceRefs_complete (ctx : Solidity.Source.Ctx) (ref : SourceLocalRef ctx) :
    ref ∈ allSourceRefs ctx := by
  have member := allOccurrences_complete (sourceIndexMember ref.index)
  have mapped := List.mem_map.mpr ⟨sourceRefPayload ctx ref,member,sourceRefPayload_inverse ctx ref⟩
  exact mapped

theorem allSourceRefs_positions (ctx : Solidity.Source.Ctx) :
    (allSourceRefs ctx).map (fun ref => ref.index.toNat) = List.range ctx.tys.length := by
  unfold allSourceRefs
  rw [List.map_map]
  change (allOccurrences ctx.tys).map
    (fun occurrence => (sourceRefFromPayload ctx occurrence).index.toNat) = _
  have pointwise : (fun occurrence : Occurrence ctx.tys =>
      (sourceRefFromPayload ctx occurrence).index.toNat) =
      (fun occurrence : Occurrence ctx.tys => occurrence.2.position) := by
    funext occurrence
    exact memberSourceIndex_position occurrence.2
  rw [pointwise,allOccurrences_positions]

/-- A classified source occurrence, independent of whether its name is queried.
Every type and handle comes from actual S01 context data. -/
structure SourceLocalEntry (ctx : Solidity.Source.Ctx) where
  ref : SourceLocalRef ctx
  kind : ExternalType
  shape : DeclaredSourceTypeD ctx.env ref.ty kind

def classifySourceRef (ctx : Solidity.Source.Ctx) (ref : SourceLocalRef ctx) :
    Option (SourceLocalEntry ctx) :=
  (checkDeclaredSourceType ctx.env ref.ty).map (fun ⟨kind,shape⟩ => ⟨ref,kind,shape⟩)

theorem SourceLocalEntry.complete {ctx} (entry : SourceLocalEntry ctx) :
    classifySourceRef ctx entry.ref = some entry := by
  rcases entry with ⟨ref,kind,shape⟩
  unfold classifySourceRef
  rw [shape.complete]
  rfl

def sourceLocalEntries (ctx : Solidity.Source.Ctx) : List (SourceLocalEntry ctx) :=
  (allSourceRefs ctx).filterMap (classifySourceRef ctx)

theorem SourceLocalEntry.mem {ctx} (entry : SourceLocalEntry ctx) :
    entry ∈ sourceLocalEntries ctx :=
  List.mem_filterMap.mpr ⟨entry.ref,allSourceRefs_complete ctx entry.ref,entry.complete⟩

/-- Target occurrence allocation follows the classified entry list, retaining
every actual source occurrence; this is not a compiler stack layout. -/
structure MappedLocal (ctx : Solidity.Source.Ctx) (X : List ExternalType) where
  source : SourceLocalEntry ctx
  index : Member X source.kind

def mappedLocals (ctx : Solidity.Source.Ctx) :
    (entries : List (SourceLocalEntry ctx)) → List (MappedLocal ctx (entries.map SourceLocalEntry.kind))
  | [] => []
  | first :: rest =>
    ⟨first,.here⟩ :: (mappedLocals ctx rest).map (fun mapped =>
      ⟨mapped.source,.there mapped.index⟩)

theorem mappedLocals_complete (ctx : Solidity.Source.Ctx)
    (entries : List (SourceLocalEntry ctx)) (entry : SourceLocalEntry ctx) (member : entry ∈ entries) :
    ∃ mapped ∈ mappedLocals ctx entries, mapped.source = entry := by
  induction entries with
  | nil => cases member
  | cons first rest ih =>
    rcases List.mem_cons.mp member with same|tail
    · cases same
      exact ⟨⟨entry,.here⟩,List.mem_cons_self,rfl⟩
    · rcases ih tail with ⟨mapped,present,same⟩
      refine ⟨⟨mapped.source,.there mapped.index⟩,?_,same⟩
      exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨mapped,present,rfl⟩)

def localExternalTypes (ctx : Solidity.Source.Ctx) : List ExternalType :=
  (sourceLocalEntries ctx).map (·.kind)

def localExternalMap (ctx : Solidity.Source.Ctx) : List (MappedLocal ctx (localExternalTypes ctx)) :=
  mappedLocals ctx (sourceLocalEntries ctx)

/-- Every declaration-backed source local is concretely represented. This
does not filter the original NAME resolution or expose a shadowed declaration. -/
theorem localExternalMap_complete (ctx : Solidity.Source.Ctx) (entry : SourceLocalEntry ctx) :
    ∃ mapped ∈ localExternalMap ctx, mapped.source = entry :=
  mappedLocals_complete ctx _ entry entry.mem


def SourceLocalEntry.position {ctx} (entry : SourceLocalEntry ctx) : Nat := entry.ref.index.toNat

theorem classifySourceRef_ref {ctx ref entry}
    (found : classifySourceRef ctx ref = some entry) : entry.ref = ref := by
  unfold classifySourceRef at found
  rcases Option.map_eq_some_iff.mp found with ⟨⟨kind,shape⟩,checked,same⟩
  cases same
  rfl

theorem sourceLocalEntries_distinct (ctx : Solidity.Source.Ctx) :
    ((sourceLocalEntries ctx).map (·.position)).Nodup := by
  have original : ((allSourceRefs ctx).map (fun ref => ref.index.toNat)).Nodup := by
    rw [allSourceRefs_positions]
    exact List.nodup_range
  have pairwise := List.pairwise_map.mp original
  apply List.pairwise_map.mpr
  apply List.Pairwise.filterMap (classifySourceRef ctx) ?_ pairwise
  intro first second different a foundA b foundB
  change a.ref.index.toNat ≠ b.ref.index.toNat
  rw [classifySourceRef_ref foundA,classifySourceRef_ref foundB]
  exact different

theorem Member.position_lt {α : Type} {X : List α} {ty : α} (index : Member X ty) :
    index.position < X.length := by
  induction index with
  | here => exact Nat.zero_lt_succ _
  | there previous ih => exact Nat.succ_lt_succ ih

theorem mappedLocals_source_positions (ctx : Solidity.Source.Ctx) (entries : List (SourceLocalEntry ctx)) :
    (mappedLocals ctx entries).map (fun mapped => mapped.source.position) = entries.map (·.position) := by
  induction entries with
  | nil => rfl
  | cons first rest ih =>
    change first.position :: ((mappedLocals ctx rest).map
      (fun mapped => (⟨mapped.source,Member.there (b := first.kind) mapped.index⟩ :
        MappedLocal ctx (first.kind :: rest.map SourceLocalEntry.kind)))).map
          (fun mapped => mapped.source.position) = _
    rw [List.map_map]
    change first.position :: (mappedLocals ctx rest).map (fun mapped => mapped.source.position) = _
    rw [ih]
    rfl

theorem mappedLocals_at (ctx : Solidity.Source.Ctx) (entries : List (SourceLocalEntry ctx))
    (mapped : MappedLocal ctx (entries.map SourceLocalEntry.kind)) (present : mapped ∈ mappedLocals ctx entries) :
    entries[mapped.index.position]? = some mapped.source := by
  induction entries with
  | nil => cases present
  | cons first rest ih =>
    rcases List.mem_cons.mp present with equal|tail
    · cases equal
      rfl
    · rcases List.mem_map.mp tail with ⟨old,member,equal⟩
      cases equal
      change rest[old.index.position]? = some old.source
      exact ih old member

/-- Actual list construction preserves aliases in both directions whenever its
input source occurrences are distinct. The concrete root proves that premise. -/
theorem mappedLocals_coherent (ctx : Solidity.Source.Ctx) (entries : List (SourceLocalEntry ctx))
    (distinct : (entries.map (·.position)).Nodup)
    (first second : MappedLocal ctx (entries.map SourceLocalEntry.kind))
    (one : first ∈ mappedLocals ctx entries) (two : second ∈ mappedLocals ctx entries) :
    first.index.position = second.index.position ↔ first.source.position = second.source.position := by
  have atOne := mappedLocals_at ctx entries first one
  have atTwo := mappedLocals_at ctx entries second two
  constructor
  · intro same
    rw [same] at atOne
    have sources := Option.some.inj (atOne.symm.trans atTwo)
    exact congrArg SourceLocalEntry.position sources
  · intro same
    have keysOne : (entries.map (·.position))[first.index.position]? = some first.source.position := by
      rw [List.getElem?_map,atOne]
      rfl
    have keysTwo : (entries.map (·.position))[second.index.position]? = some second.source.position := by
      rw [List.getElem?_map,atTwo]
      rfl
    have bound : first.index.position < (entries.map (·.position)).length := by
      simpa only [List.length_map] using first.index.position_lt
    exact List.getElem?_inj bound distinct (keysOne.trans ((congrArg some same).trans keysTwo.symm))

theorem localExternalMap_coherent (ctx : Solidity.Source.Ctx)
    (first second : MappedLocal ctx (localExternalTypes ctx))
    (one : first ∈ localExternalMap ctx) (two : second ∈ localExternalMap ctx) :
    first.index.position = second.index.position ↔ first.source.position = second.source.position :=
  mappedLocals_coherent ctx _ (sourceLocalEntries_distinct ctx) first second one two


/-- Extracting a scalar binding preserves both occurrence coordinates. -/
def MappedLocal.scalar {ctx X} (mapped : MappedLocal ctx X) : Option (ScalarBinding X ctx) := by
  rcases mapped with ⟨⟨ref,kind,shape⟩,index⟩
  cases kind with
  | value encoding => exact some ⟨⟨ref,encoding,shape⟩,index⟩
  | _ => exact none

theorem MappedLocal.scalar_positions {ctx X} (mapped : MappedLocal ctx X)
    (binding : ScalarBinding X ctx) (found : mapped.scalar = some binding) :
    binding.ref.position = mapped.index.position ∧
      binding.source.position = mapped.source.position := by
  rcases mapped with ⟨⟨ref,kind,shape⟩,index⟩
  cases kind <;> cases found
  exact ⟨rfl,rfl⟩

def localScalarBindings (ctx : Solidity.Source.Ctx) :
    List (ScalarBinding (localExternalTypes ctx) ctx) :=
  (localExternalMap ctx).filterMap MappedLocal.scalar

/-- The actual context constructor DISCHARGES bidirectional alias coherence.
This is a static occurrence theorem, not an initializer/pipeline simulation. -/
theorem localScalarBindings_coherent (ctx : Solidity.Source.Ctx) :
    ScalarBindingsCoherent (localScalarBindings ctx) := by
  intro first one second two
  rcases List.mem_filterMap.mp one with ⟨firstMapped,firstMember,firstScalar⟩
  rcases List.mem_filterMap.mp two with ⟨secondMapped,secondMember,secondScalar⟩
  obtain ⟨firstYul,firstSource⟩ := firstMapped.scalar_positions first firstScalar
  obtain ⟨secondYul,secondSource⟩ := secondMapped.scalar_positions second secondScalar
  rw [firstYul,secondYul,firstSource,secondSource]
  exact localExternalMap_coherent ctx firstMapped secondMapped firstMember secondMember

theorem localScalarBindings_complete (ctx : Solidity.Source.Ctx) (cell : SourceScalarCell ctx) :
    ∃ binding ∈ localScalarBindings ctx, binding.source = cell := by
  let entry : SourceLocalEntry ctx := ⟨cell.ref,.value cell.encoding,cell.shape⟩
  rcases localExternalMap_complete ctx entry with ⟨mapped,member,same⟩
  rcases mapped with ⟨actual,index⟩
  change actual = entry at same
  subst actual
  refine ⟨⟨cell,index⟩,?_,rfl⟩
  exact List.mem_filterMap.mpr ⟨⟨entry,index⟩,member,rfl⟩

/-- Real-root instantiation of the scalar write law: coherence is proved by
construction. Prior raw-view agreement remains a REAL premise; initialization
and execution/pipeline refinement are not assumed or asserted here. -/
theorem localScalarBindings_write (ctx : Solidity.Source.Ctx)
    (yul : ScalarView (localExternalTypes ctx)) (source : SourceScalarView ctx)
    (agree : ScalarViewsAgree (localScalarBindings ctx) yul source)
    (target : ScalarBinding (localExternalTypes ctx) ctx)
    (present : target ∈ localScalarBindings ctx) (value : Word) :
    ScalarViewsAgree (localScalarBindings ctx) (yul.write target.ref value)
      (source.write target.source value) :=
  agree.write (localScalarBindings_coherent ctx) target present value


theorem DeclaredSourceTypeD.not_global {env ty kind} (shape : DeclaredSourceTypeD env ty kind) :
    kind.isGlobal = false := by
  cases shape with
  | basic basic =>
    cases basic with
    | scalar scalar => rfl
    | reference reference => cases reference <;> rfl
  | enum lookup node range => rfl
  | udvt lookup node scalar => rfl

/-- Source local references cannot become captured globals merely by filtering
the context. Actual constant/library/state declarations are separate inputs. -/
theorem localExternalTypes_not_global (ctx : Solidity.Source.Ctx) (kind : ExternalType)
    (member : kind ∈ localExternalTypes ctx) : kind.isGlobal = false := by
  rcases List.mem_map.mp member with ⟨entry,present,same⟩
  cases same
  exact entry.shape.not_global

theorem localExternalTypes_globals (ctx : Solidity.Source.Ctx) :
    globals (localExternalTypes ctx) = [] := by
  apply List.filter_eq_nil_iff.mpr
  intro kind member
  rw [localExternalTypes_not_global ctx kind member]
  decide


/-- Independent FIRST occurrence lookup in an intrinsic mapped table. -/
inductive MappedLookupD {ctx X} :
    List (MappedLocal ctx X) → SourceLocalRef ctx → MappedLocal ctx X → Type where
  | head {first rest ref} : first.source.ref = ref → MappedLookupD (first::rest) ref first
  | tail {first rest ref mapped} :
      first.source.position ≠ ref.index.toNat →
      MappedLookupD rest ref mapped → MappedLookupD (first::rest) ref mapped

def lookupMapped {ctx X} : (entries : List (MappedLocal ctx X)) → (ref : SourceLocalRef ctx) →
    Option ((mapped : MappedLocal ctx X) × MappedLookupD entries ref mapped)
  | [], _ => none
  | first::rest, ref =>
    if same : first.source.position = ref.index.toNat then
      some ⟨first,.head (SourceLocalRef.position_injective first.source.ref ref same)⟩
    else do
      let ⟨mapped,found⟩ ← lookupMapped rest ref
      pure ⟨mapped,.tail same found⟩

theorem MappedLookupD.complete {ctx X entries ref mapped}
    (found : @MappedLookupD ctx X entries ref mapped) :
    lookupMapped entries ref = some ⟨mapped,found⟩ := by
  induction found with
  | @head first rest ref same =>
    have position := congrArg (fun ref : SourceLocalRef ctx => ref.index.toNat) same
    change first.source.position = ref.index.toNat at position
    unfold lookupMapped
    rw [dif_pos position]
  | tail different found ih =>
    unfold lookupMapped
    rw [dif_neg different,ih]
    rfl

theorem MappedLookupD.source_ref {ctx X entries ref mapped}
    (found : @MappedLookupD ctx X entries ref mapped) : mapped.source.ref = ref := by
  induction found with
  | head same => exact same
  | tail different found ih => exact ih

theorem MappedLookupD.mem {ctx X entries ref mapped}
    (found : @MappedLookupD ctx X entries ref mapped) : mapped ∈ entries := by
  induction found with
  | head same => exact List.mem_cons_self
  | tail different found ih => exact List.mem_cons_of_mem _ ih

theorem lookupMapped_exists {ctx X} (entries : List (MappedLocal ctx X)) (ref : SourceLocalRef ctx)
    (mapped : MappedLocal ctx X) (present : mapped ∈ entries) (same : mapped.source.ref = ref) :
    (lookupMapped entries ref).isSome = true := by
  induction entries with
  | nil => cases present
  | cons first rest ih =>
    unfold lookupMapped
    split
    · rfl
    · next different =>
      have tail : mapped ∈ rest := by
        rcases List.mem_cons.mp present with equal|tail
        · cases equal
          exact False.elim (different (congrArg (fun ref : SourceLocalRef ctx => ref.index.toNat) same))
        · exact tail
      have found := ih tail
      cases lookup : lookupMapped rest ref with
      | none => rw [lookup] at found; cases found
      | some result => rfl

/-- Actual S01 resolution occurs BEFORE looking in the classified projection.
An unsupported selected local cannot expose an older local/global name. -/
inductive LocalMappedD (ctx : Solidity.Source.Ctx) (name : String) :
    MappedLocal ctx (localExternalTypes ctx) → Type where
  | intro {ref mapped} : SourceLocalD ctx name ref →
      MappedLookupD (localExternalMap ctx) ref mapped → LocalMappedD ctx name mapped

def checkLocalMapped (ctx : Solidity.Source.Ctx) (name : String) :
    Option ((mapped : MappedLocal ctx (localExternalTypes ctx)) × LocalMappedD ctx name mapped) := do
  let ⟨ref,identity⟩ ← checkSourceLocal ctx name
  let ⟨mapped,found⟩ ← lookupMapped (localExternalMap ctx) ref
  pure ⟨mapped,.intro identity found⟩

theorem LocalMappedD.complete {ctx name mapped} (d : LocalMappedD ctx name mapped) :
    checkLocalMapped ctx name = some ⟨mapped,d⟩ := by
  cases d with
  | intro identity found =>
    unfold checkLocalMapped
    rw [identity.complete]
    change (lookupMapped _ _).bind _ = _
    rw [found.complete]
    rfl

def LocalMappedD.classified {ctx name mapped} (d : LocalMappedD ctx name mapped) :
    ClassifiedSourceLocal ctx name :=
  LocalMappedD.casesOn (motive := fun _ _ => ClassifiedSourceLocal ctx name) d
    (intro := fun {_ref} {mapped} identity found =>
      ⟨mapped.source.ref,found.source_ref ▸ identity,mapped.source.kind,mapped.source.shape⟩)

theorem checkLocalMapped_iff (ctx : Solidity.Source.Ctx) (name : String) :
    (checkLocalMapped ctx name).isSome = true ↔
      Nonempty (ClassifiedSourceLocal ctx name) := by
  constructor
  · intro accepted
    cases found : checkLocalMapped ctx name with
    | none => rw [found] at accepted; cases accepted
    | some result => exact ⟨result.2.classified⟩
  · rintro ⟨source⟩
    let entry : SourceLocalEntry ctx := ⟨source.ref,source.kind,source.shape⟩
    rcases localExternalMap_complete ctx entry with ⟨mapped,present,same⟩
    have sameRef : mapped.source.ref = source.ref := congrArg SourceLocalEntry.ref same
    have available := lookupMapped_exists (localExternalMap ctx) source.ref mapped present sameRef
    unfold checkLocalMapped
    rw [source.identity.complete]
    change ((lookupMapped _ _).bind _).isSome = true
    cases found : lookupMapped (localExternalMap ctx) source.ref with
    | none => rw [found] at available; cases available
    | some result => rfl


/-- Actual local name/type/occurrence plus independently typed suffix access.
Global Solidity declarations and function-boundary policy remain separate. -/
inductive LocalExternalD (ctx : Solidity.Source.Ctx) (name : String)
    (suffix : List String) (write : Bool) : ExternalRef (localExternalTypes ctx) write → Type where
  | intro {mapped attr} :
      LocalMappedD ctx name mapped → SuffixD suffix attr →
      (cap : Access mapped.source.kind attr write) →
      LocalExternalD ctx name suffix write ⟨mapped.index,attr,cap⟩

private def checkedSuffix (suffix : List String) :
    Option {attr : Attribute // SuffixD suffix attr} :=
  match h : checkSuffix suffix with
  | none => none
  | some attr => some ⟨attr,checkSuffix_sound h⟩

private theorem checkedSuffix_complete {suffix attr} (d : SuffixD suffix attr) :
    checkedSuffix suffix = some ⟨attr,d⟩ := by
  unfold checkedSuffix
  split
  · rename_i h
    rw [d.complete] at h
    cases h
  · rename_i other h
    have same := d.complete.symm.trans h
    cases Option.some.inj same
    rfl

def checkLocalExternal (ctx : Solidity.Source.Ctx) (name : String)
    (suffix : List String) (write : Bool) :
    Option ((ref : ExternalRef (localExternalTypes ctx) write) ×
      LocalExternalD ctx name suffix write ref) := do
  let ⟨mapped,resolved⟩ ← checkLocalMapped ctx name
  let ⟨attr,spelling⟩ ← checkedSuffix suffix
  let cap ← checkAccess mapped.source.kind attr write
  pure ⟨⟨mapped.index,attr,cap⟩,.intro resolved spelling cap⟩

theorem LocalExternalD.complete {ctx name suffix write ref}
    (d : LocalExternalD ctx name suffix write ref) :
    checkLocalExternal ctx name suffix write = some ⟨ref,d⟩ := by
  cases d with
  | intro resolved spelling cap =>
    unfold checkLocalExternal
    rw [resolved.complete]
    change (checkedSuffix suffix).bind _ = _
    rw [checkedSuffix_complete spelling]
    change (checkAccess _ _ _).bind _ = _
    rw [cap.complete]
    rfl

theorem checkLocalExternal_iff (ctx : Solidity.Source.Ctx) (name : String)
    (suffix : List String) (write : Bool) :
    (checkLocalExternal ctx name suffix write).isSome = true ↔
      ∃ ref, Nonempty (LocalExternalD ctx name suffix write ref) := by
  constructor
  · intro accepted
    cases found : checkLocalExternal ctx name suffix write with
    | none => rw [found] at accepted; cases accepted
    | some result => exact ⟨result.1,⟨result.2⟩⟩
  · rintro ⟨ref,⟨d⟩⟩
    rw [d.complete]
    rfl

end Solidity.Yul
