import Solidity.Yul.SourceTypes
import Solidity.Yul.ExternalScope

/-! Intrinsic scalar-local word views. These are logical occurrence-indexed
projections, NOT storage/memory/stack layouts or a full Source state. Writes
retain all256 bits for every scalar encoding. Source initialization, subsequent
Solidity operations, pipeline refinement and the general interpreter remain
separate obligations; no Source.Val representation is changed. -/
namespace Solidity.Yul

def Member.position {α : Type} {X : List α} {ty : α} (index : Member X ty) : Nat := by
  apply Member.casesOn (motive := fun _ _ _ => Nat) index
  case here => intros; exact 0
  case there => intro a b rest previous; exact previous.position + 1
termination_by structural index

theorem Member.mem {α : Type} {X : List α} {ty : α} (index : Member X ty) : ty ∈ X := by
  induction index with
  | here => exact List.mem_cons_self
  | there previous ih => exact List.mem_cons_of_mem _ ih


/-- A context position uniquely determines the selected type and occurrence.
No equality decision on the type labels or filtering injectivity is assumed. -/
theorem Member.payload_position {α : Type} (X : List α)
    (first second : (ty : α) × Member X ty)
    (same : first.2.position = second.2.position) : first = second := by
  induction X with
  | nil => rcases first with ⟨ty,index⟩; cases index
  | cons head rest ih =>
    rcases first with ⟨a,one⟩
    rcases second with ⟨b,two⟩
    cases one with
    | here =>
      cases two with
      | here => rfl
      | there two => cases same
    | there one =>
      cases two with
      | here => cases same
      | there two =>
        have tails : one.position = two.position := Nat.succ.inj same
        have equal := ih ⟨a,one⟩ ⟨b,two⟩ tails
        cases equal
        rfl

/-- Only genuine scalar VALUE occurrences inhabit this domain. No arbitrary
word placeholder is supplied for storage, memory, calldata or function fields. -/
structure ScalarRef (X : List ExternalType) where
  encoding : Encoding
  index : Member X (.value encoding)

def ScalarRef.position {X} (ref : ScalarRef X) : Nat := ref.index.position


theorem ScalarRef.position_injective {X} (first second : ScalarRef X)
    (same : first.position = second.position) : first = second := by
  rcases first with ⟨a,one⟩
  rcases second with ⟨b,two⟩
  have equal := Member.payload_position X ⟨ExternalType.value a,one⟩ ⟨ExternalType.value b,two⟩ same
  cases equal
  rfl

abbrev ScalarView (X : List ExternalType) := ScalarRef X → Word

def ScalarView.write {X} (view : ScalarView X) (target : ScalarRef X) (value : Word) :
    ScalarView X :=
  fun ref => if ref.position = target.position then value else view ref

theorem ScalarView.write_same {X} (view : ScalarView X) (target : ScalarRef X) (value : Word) :
    (view.write target value) target = value := by
  exact if_pos rfl

theorem ScalarView.write_other {X} (view : ScalarView X) (target other : ScalarRef X)
    (value : Word) (different : other.position ≠ target.position) :
    (view.write target value) other = view other := if_neg different

theorem ScalarView.write_shadow {X} (view : ScalarView X) (target : ScalarRef X)
    (first second : Word) :
    (view.write target first).write target second = view.write target second := by
  funext ref
  by_cases same : ref.position = target.position
  · simp only [ScalarView.write, same, ↓reduceIte]
  · simp only [ScalarView.write, same, ↓reduceIte]

theorem ScalarView.write_commute {X} (view : ScalarView X) (first second : ScalarRef X)
    (a b : Word) (different : first.position ≠ second.position) :
    (view.write first a).write second b = (view.write second b).write first a := by
  funext ref
  by_cases one : ref.position = first.position
  · simp only [ScalarView.write, one, different, ↓reduceIte]
  · by_cases two : ref.position = second.position
    · simp only [ScalarView.write, two, Ne.symm different, ↓reduceIte]
    · simp only [ScalarView.write, one, two, ↓reduceIte]

/-- Global projection contains no Solidity VALUE locals. Constants remain
separate literal-valued references; physical globals are not scalar cells. -/
theorem ScalarRef.not_globals {X} (ref : ScalarRef (globals X)) : False := by
  have member := ref.index.mem
  change ExternalType.value ref.encoding ∈ X.filter ExternalType.isGlobal at member
  have global := (List.mem_filter.mp member).2
  cases global

def ScalarView.functionEmpty (X : List ExternalType) : ScalarView (globals X) :=
  fun ref => False.elim ref.not_globals

theorem ScalarView.function_unique {X} (first second : ScalarView (globals X)) : first = second := by
  funext ref
  exact False.elim ref.not_globals


/-- Intrinsic conversion uses the actual Source type/context indices. -/
def sourceIndexMember {types : Solidity.Source.RCtx} {ty}
    (index : Solidity.Source.Idx types ty) : Member types ty := by
  apply Solidity.Source.Idx.casesOn (motive := fun types ty _ => Member types ty) index
  case here => intros; exact .here
  case there => intro a b rest previous; exact .there (sourceIndexMember previous)
termination_by structural index

def memberSourceIndex {types : Solidity.Source.RCtx} {ty}
    (index : Member types ty) : Solidity.Source.Idx types ty := by
  apply Member.casesOn (motive := fun types ty _ => Solidity.Source.Idx types ty) index
  case here => intros; exact .here
  case there => intro a b rest previous; exact .there (memberSourceIndex previous)
termination_by structural index

theorem sourceIndexMember_position {types : Solidity.Source.RCtx} {ty}
    (index : Solidity.Source.Idx types ty) :
    (sourceIndexMember index).position = index.toNat := by
  induction index with
  | here => rfl
  | there previous ih => exact congrArg Nat.succ ih

theorem memberSourceIndex_inverse {types : Solidity.Source.RCtx} {ty}
    (index : Solidity.Source.Idx types ty) : memberSourceIndex (sourceIndexMember index) = index := by
  induction index with
  | here => rfl
  | there previous ih => exact congrArg Solidity.Source.Idx.there ih

def sourceRefPayload (ctx : Solidity.Source.Ctx) (ref : SourceLocalRef ctx) :
    (ty : Solidity.Source.STy) × Member ctx.tys ty := ⟨ref.ty,sourceIndexMember ref.index⟩

def sourceRefFromPayload (ctx : Solidity.Source.Ctx)
    (payload : (ty : Solidity.Source.STy) × Member ctx.tys ty) : SourceLocalRef ctx :=
  ⟨memberSourceIndex payload.2⟩

theorem sourceRefPayload_inverse (ctx : Solidity.Source.Ctx) (ref : SourceLocalRef ctx) :
    sourceRefFromPayload ctx (sourceRefPayload ctx ref) = ref := by
  change (⟨memberSourceIndex (sourceIndexMember ref.index)⟩ : SourceLocalRef ctx) = ref
  rw [memberSourceIndex_inverse]

theorem SourceLocalRef.position_injective {ctx} (first second : SourceLocalRef ctx)
    (same : first.index.toNat = second.index.toNat) : first = second := by
  have positions : (sourceRefPayload ctx first).2.position = (sourceRefPayload ctx second).2.position := by
    change (sourceIndexMember first.index).position = (sourceIndexMember second.index).position
    rw [sourceIndexMember_position,sourceIndexMember_position]
    exact same
  have equal := Member.payload_position ctx.tys (sourceRefPayload ctx first) (sourceRefPayload ctx second) positions
  have back := congrArg (sourceRefFromPayload ctx) equal
  rw [sourceRefPayload_inverse,sourceRefPayload_inverse] at back
  exact back

/-- The source occurrence and its real declaration-backed scalar type remain
in the cell. This carries no solc-ID inference or raw/logical initialization law. -/
structure SourceScalarCell (ctx : Solidity.Source.Ctx) where
  ref : SourceLocalRef ctx
  encoding : Encoding
  shape : DeclaredSourceTypeD ctx.env ref.ty (.value encoding)

def SourceScalarCell.position {ctx} (cell : SourceScalarCell ctx) : Nat := cell.ref.index.toNat


theorem SourceScalarCell.position_injective {ctx} (first second : SourceScalarCell ctx)
    (same : first.position = second.position) : first = second := by
  rcases first with ⟨one,a,da⟩
  rcases second with ⟨two,b,db⟩
  have references := SourceLocalRef.position_injective one two same
  cases references
  have encodings : a = b := ExternalType.value.inj (DeclaredSourceTypeD.unique da db)
  cases encodings
  have certificates := Option.some.inj (da.complete.symm.trans db.complete)
  cases certificates
  rfl

def SourceScalarCell.ofClassified {ctx name} (source : ClassifiedSourceLocal ctx name)
    (encoding : Encoding) (kind : source.kind = .value encoding) : SourceScalarCell ctx :=
  ⟨source.ref, encoding, kind ▸ source.shape⟩

theorem SourceScalarCell.ofClassified_resolves {ctx name}
    (source : ClassifiedSourceLocal ctx name) (encoding : Encoding)
    (kind : source.kind = .value encoding) :
    ctx.resolve name = some (.loc (SourceScalarCell.ofClassified source encoding kind).position) :=
  source.identity.position_resolves

abbrev SourceScalarView (ctx : Solidity.Source.Ctx) := SourceScalarCell ctx → Word

def SourceScalarView.write {ctx} (view : SourceScalarView ctx) (target : SourceScalarCell ctx)
    (value : Word) : SourceScalarView ctx :=
  fun cell => if cell.position = target.position then value else view cell

theorem SourceScalarView.write_same {ctx} (view : SourceScalarView ctx)
    (target : SourceScalarCell ctx) (value : Word) :
    (view.write target value) target = value := if_pos rfl

theorem SourceScalarView.write_other {ctx} (view : SourceScalarView ctx)
    (target other : SourceScalarCell ctx) (value : Word)
    (different : other.position ≠ target.position) :
    (view.write target value) other = view other := if_neg different

/-- A binding keeps BOTH actual typed occurrences. Binding provenance/totality
and injectivity for a constructed root table are real remaining obligations. -/
structure ScalarBinding (X : List ExternalType) (ctx : Solidity.Source.Ctx) where
  source : SourceScalarCell ctx
  index : Member X (.value source.encoding)

def ScalarBinding.ref {X ctx} (binding : ScalarBinding X ctx) : ScalarRef X :=
  ⟨binding.source.encoding,binding.index⟩

def ScalarBinding.readSource {X ctx} (binding : ScalarBinding X ctx)
    (view : SourceScalarView ctx) : Word := view binding.source

theorem ScalarBinding.write_source_read {X ctx} (binding : ScalarBinding X ctx)
    (view : SourceScalarView ctx) (value : Word) :
    binding.readSource (view.write binding.source value) = value :=
  SourceScalarView.write_same view binding.source value


/-- Real alias preservation for the supplied binding table, in both directions.
The root-table constructor must prove this; distinct names are insufficient. -/
def ScalarBindingsCoherent {X ctx} (bindings : List (ScalarBinding X ctx)) : Prop :=
  ∀ first ∈ bindings, ∀ second ∈ bindings,
    first.ref.position = second.ref.position ↔ first.source.position = second.source.position

def ScalarViewsAgree {X ctx} (bindings : List (ScalarBinding X ctx))
    (yul : ScalarView X) (source : SourceScalarView ctx) : Prop :=
  ∀ binding ∈ bindings, yul binding.ref = source binding.source

/-- Conditional projection/write agreement, NOT a Source/pipeline refinement.
All raw input words survive exactly under the actual alias-coherence premise. -/
theorem ScalarViewsAgree.write {X ctx bindings yul source}
    (agree : @ScalarViewsAgree X ctx bindings yul source)
    (coherent : ScalarBindingsCoherent bindings)
    (target : ScalarBinding X ctx) (present : target ∈ bindings) (value : Word) :
    ScalarViewsAgree bindings (yul.write target.ref value) (source.write target.source value) := by
  intro other member
  by_cases same : other.ref.position = target.ref.position
  · have sourceSame := (coherent other member target present).mp same
    simp only [ScalarView.write,SourceScalarView.write,same,sourceSame,↓reduceIte]
  · have sourceDifferent : other.source.position ≠ target.source.position :=
      fun equal => same ((coherent other member target present).mpr equal)
    simp only [ScalarView.write,SourceScalarView.write,same,sourceDifferent,↓reduceIte]
    exact agree other member

end Solidity.Yul
