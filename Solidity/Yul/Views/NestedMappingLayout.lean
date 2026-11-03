import Solidity.Yul.Views.MappingSlots

namespace Solidity.Yul.Views

/-- Finite actual source schema, with no externally chosen traversal budget. -/
def nestedMappingType : Nat → Source.STy
  | 0 => .int .u256
  | n+1 => .mapping (.int .u256) (nestedMappingType n)

def nestedMappingTree : Nat → Storage.STy
  | 0 => .word
  | n+1 => .map (nestedMappingTree n)

def nestedMappingDepth : Source.STy → Nat
  | .mapping _ value => nestedMappingDepth value+1
  | _ => 0

def nestedMappingAccess (keys : List Roadmap.Word) : List Storage.Step :=
  keys.map (fun k => .key k.val)

def nestedMappingSteps (keys : List Roadmap.Word) : List Source.Step :=
  keys.map (fun k => .key (Source.wordBytes k))

def nestedMappingLocation : Storage.Loc → List Roadmap.Word → Storage.Loc
  | loc, [] => loc
  | loc, k::ks => nestedMappingLocation (.hash k.val loc 0) ks

theorem nestedMapping_layout (E : Source.Env) (n : Nat) :
    FullWordLayout E (nestedMappingType n) (nestedMappingTree n) := by
  induction n with
  | zero => exact .word
  | succ n ih => exact .mapping ih

theorem nestedMapping_size (n : Nat) : (nestedMappingTree n).size=1 := by
  cases n <;> rfl

theorem nestedMapping_fits (n : Nat) : (nestedMappingTree n).Fits 1 := by
  induction n with
  | zero => trivial
  | succ n ih => exact ⟨by rw [nestedMapping_size]; exact Nat.le_refl 1,ih⟩

theorem nestedMapping_translate (keys : List Roadmap.Word) :
    sourceLayoutSteps (nestedMappingAccess keys)=.ok (nestedMappingSteps keys) := by
  induction keys with
  | nil => rfl
  | cons k ks ih =>
    simp only [nestedMappingAccess,nestedMappingSteps,List.map_cons,sourceLayoutSteps,
      dif_pos k.isLt,Except.map] at *
    rw [ih]

theorem nestedMapping_locate (keys : List Roadmap.Word) (loc : Storage.Loc) :
    (nestedMappingTree keys.length).locate loc (nestedMappingAccess keys)=
      some (.word,nestedMappingLocation loc keys) := by
  induction keys generalizing loc with
  | nil => rfl
  | cons k ks ih => exact ih (.hash k.val loc 0)

theorem nestedMapping_path_type (E : Source.Env) (keys : List Roadmap.Word) :
    (nestedMappingSteps keys).foldl (fun o step => o.bind (E.stepTy · step))
      (some (nestedMappingType keys.length))=some (.int .u256) := by
  induction keys with
  | nil => rfl
  | cons k ks ih => exact ih

/-- Checked declaration metadata. The origin remains the owner's root0;
this does not assert global Solidity declaration placement. -/
structure NestedWordMappingRoot (E : Source.Env) (root : Source.DeclName) where
  depth : Nat
  positive : 0<depth
  found : E.rootTy root=some (nestedMappingType depth)
  persistent : E.transientRoot ⟨root,[]⟩=false

def prepareNestedWordMappingRoot (E : Source.Env) (root : Source.DeclName) :
    Option (NestedWordMappingRoot E root) :=
  match found : E.rootTy root with
  | none => none
  | some ty =>
    let depth := nestedMappingDepth ty
    if positive : 0<depth then
      if shape : ty=nestedMappingType depth then
        if bank : E.transientRoot ⟨root,[]⟩=false then
          some ⟨depth,positive,found.trans (congrArg some shape),bank⟩
        else none
      else none
    else none

abbrev NestedWordMappingRoot.Keys {E root} (mapping : NestedWordMappingRoot E root) :=
  { keys : List Roadmap.Word // keys.length=mapping.depth }

def NestedWordMappingRoot.entry {E root} (mapping : NestedWordMappingRoot E root)
    (fixed : Roadmap.Evm.Fixed) (keys : mapping.Keys) :
    LocatedWord E fixed root (nestedMappingTree mapping.depth) (nestedMappingAccess keys.val) where
  rootType := nestedMappingType mapping.depth
  rootFound := mapping.found
  layout := nestedMapping_layout E mapping.depth
  sourceSteps := nestedMappingSteps keys.val
  translated := nestedMapping_translate keys.val
  reached := .word
  location := nestedMappingLocation (.root 0) keys.val
  located := by simpa only [keys.property] using nestedMapping_locate keys.val (.root 0)
  positive := by decide
  cellType := by
    simp only [Source.Env.cellTy,Source.Env.pathTy,mapping.found]
    have reached := nestedMapping_path_type E keys.val
    simp only [keys.property] at reached
    rw [reached]
    rfl

/-- Hash each actual key word with the previously computed physical word. -/
def nestedMappingWord (fixed : Roadmap.Evm.Fixed) : Nat → List Roadmap.Word → Nat
  | word, [] => word
  | word, key::keys => nestedMappingWord fixed
      (fixed.keccak (layoutPreimageBytes (.entry key.val word))) keys

theorem nestedMapping_word (fixed : Roadmap.Evm.Fixed) (loc : Storage.Loc)
    (keys : List Roadmap.Word) :
    (nestedMappingLocation loc keys).word (2^256) (fixedLayoutHash fixed)=
      nestedMappingWord fixed (loc.word (2^256) (fixedLayoutHash fixed)) keys := by
  induction keys generalizing loc with
  | nil => rfl
  | cons key keys ih =>
    rw [nestedMappingLocation,ih]
    simp only [Storage.Loc.word,fixedLayoutHash,Nat.add_zero,
      Nat.mod_eq_of_lt (fixed.keccak_lt _),nestedMappingWord]

example : nestedMappingLocation (.root 0) ([1,2,3] : List Roadmap.Word)=
    .hash 3 (.hash 2 (.hash 1 (.root 0) 0) 0) 0 := rfl
example : prepareNestedWordMappingRoot (⟨[]⟩ : Source.Env) ⟨none,"table"⟩=none := rfl

end Solidity.Yul.Views
