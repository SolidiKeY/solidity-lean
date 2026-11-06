import Solidity.Yul.Views.FullWordLayout
import Solidity.Yul.Views.FinitePaths
import Solidity.Yul.Views.StaticUintMemory

namespace Solidity.Yul.Views

inductive LocatedError where
  | missingRoot | layoutMismatch | invalidPath | keyOutOfRange | nonValueCell | emptyRegion
  deriving DecidableEq, Repr

def sourceLayoutSteps : List Storage.Step → Except LocatedError (List Source.Step)
  | [] => .ok []
  | .field i::rest => (sourceLayoutSteps rest).map (Source.Step.field i :: ·)
  | .index i::rest => (sourceLayoutSteps rest).map (Source.Step.index i :: ·)
  | .key k::rest => if bound : k < 2^256 then
      (sourceLayoutSteps rest).map (Source.Step.key (Source.wordBytes ⟨k,bound⟩) :: ·)
    else .error .keyOutOfRange

/-- Intrinsic certificate of COMPUTED declaration/layout/path checks. Fields
are actual lookups and constructor alignment, never inverse/read/safety laws.
The supplied owner layout is anchored at root0, as in located_word_inj; arbitrary
contract root placement and packed-layout inference are not claimed. -/
structure LocatedWord (E : Source.Env) (fixed : Roadmap.Evm.Fixed) (root : Source.DeclName)
    (tree : Storage.STy) (access : List Storage.Step) where
  rootType : Source.STy
  rootFound : E.rootTy root = some rootType
  layout : FullWordLayout E rootType tree
  sourceSteps : List Source.Step
  translated : sourceLayoutSteps access = .ok sourceSteps
  reached : Storage.STy
  location : Storage.Loc
  located : tree.locate (.root 0) access = some (reached,location)
  positive : 0 < reached.size
  cellType : E.cellTy ⟨root,sourceSteps⟩ = .int .u256

def prepareLocatedWord (E : Source.Env) (fixed : Roadmap.Evm.Fixed) (root : Source.DeclName)
    (tree : Storage.STy) (access : List Storage.Step) : Except LocatedError (LocatedWord E fixed root tree access) :=
  match rootFound : E.rootTy root with
  | none => .error .missingRoot
  | some rootType =>
    if aligned : fullWordLayoutCheck E rootType tree = true then
      match translated : sourceLayoutSteps access with
      | .error reason => .error reason
      | .ok steps => match located : tree.locate (.root 0) access with
        | none => .error .invalidPath
        | some (reached,location) =>
          if positive : 0 < reached.size then
            if cellType : E.cellTy ⟨root,steps⟩ = .int .u256 then
              .ok ⟨rootType,rootFound,fullWordLayoutCheck_sound E _ _ aligned,steps,translated,reached,location,located,positive,cellType⟩
            else .error .nonValueCell
          else .error .emptyRegion
    else .error .layoutMismatch

def LocatedWord.path {E fixed root tree access} (r : LocatedWord E fixed root tree access) : Source.SPath := ⟨root,r.sourceSteps⟩

def LocatedWord.registration {E fixed root tree access} (r : LocatedWord E fixed root tree access)
    (a : Roadmap.Address) : ScalarPath E.layout (E.lay a) where
  path := r.path
  slot := physicalSlot (fixedLayoutHash fixed) r.location
  field := intField .u256 0 (by decide)
  codec := r.cellType.symm ▸ intCodec E.layout .u256 0 (by decide)
  width := r.cellType.symm ▸ StorageWidth.int .u256

theorem LocatedWord.slot_computed {E fixed root tree access} (r : LocatedWord E fixed root tree access) (a : Roadmap.Address) :
    (r.registration a).slot.val = r.location.word (2^256) (fun p => fixed.keccak (layoutPreimageBytes p)) := rfl

theorem LocatedWord.bounded {E fixed root tree access} (r : LocatedWord E fixed root tree access)
    (L R : Nat) (fits : tree.Fits L) (rootFits : tree.size ≤ R) : r.location.Bounded L R := by
  have placed := (Storage.STy.locate_bounded tree (.root 0) access fits (Storage.placed_root rootFits) r.located).2
  have bound := placed 0 r.positive
  rwa [Storage.Loc.add_zero] at bound

/-- Concrete instance: location, slot equality and default availability are
DERIVED from the checked registration, not caller-supplied agreement fields. -/
def LocatedWord.obligations {E fixed root tree access} (r : LocatedWord E fixed root tree access)
    (a : Roadmap.Address) (residual : SlotView) :
    ScalarStorageObligations E.layout (E.lay a) {c // c ∈ [r.registration a]} :=
  finiteScalarObligations [r.registration a] (List.pairwise_singleton _ _)
    (fixedLayoutHash fixed) (fun _ => r.location)
    (by intro c; have same := List.mem_singleton.mp c.property; rw [same]; rfl)
    (by
      intro c member
      have same := List.mem_singleton.mp member
      subst c
      change ∃ v, Source.Val.default E.layout (E.cellTy r.path) = some v
      rw [show E.cellTy r.path = .int .u256 from r.cellType]
      exact ⟨.int 0 (by decide),rfl⟩) residual

theorem located_keyStep {E : Source.Env} {Γ : Source.RCtx} (F : Source.Fr) (horizon : Nat)
    (w : Roadmap.Word) (s : Source.EMState E Γ) :
    (Source.keyStep F horizon (.val (uintValueOfWord E.layout w))).run s = (.ok (.key (Source.wordBytes w)),s) := by
  simp only [Source.keyStep, uintValueOfWord_word]
  rfl

end Solidity.Yul.Views
