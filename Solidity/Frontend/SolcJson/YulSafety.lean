
import Solidity.Frontend.SolcJson.YulMetadata

/-! Pinned inline-assembly NatSpec tag preparation. This models the upstream
DocStringParser byte transitions and memory-safe-assembly tag lookup; it does
not validate source attachment, prove equivalence to C++, or admit a whole block.
Malformed @param ends parsing while retaining earlier tags, matching the pinned
warning-only inline-assembly path. Tags remain in source order; only membership
is used, not equality to C++ multimap iteration order. Unknown tags/values do not
grant safety. -/
namespace Solidity.Frontend.YulJson
open Solidity.Frontend.Checked (Bytes isIdStart isIdPart)
open Solidity.Yul

structure DocTag where
  name : Bytes
  content : Bytes
  deriving DecidableEq, Repr

def spaceTab (b : UInt8) : Bool := b == 32 || b == 9

def docWhitespace (b : UInt8) : Bool := spaceTab b || b == 10 || b == 13

def tagSeparator (b : UInt8) : Bool := spaceTab b || b == 10

def lineBytes (bs : Bytes) : Bytes × Bytes :=
  let pair := bs.span (fun b => b != 10)
  (pair.1, pair.2.drop 1)

def finishTags (done : List DocTag) (current : Option DocTag) : List DocTag :=
  done.reverse ++ current.toList

def appendLine (t : DocTag) (bs : Bytes) : DocTag × Bytes :=
  let (line, rest) := lineBytes bs
  let separator := match bs with
    | [] => []
    | b :: _ => if spaceTab b then [] else [32]
  (⟨t.name, t.content ++ separator ++ line⟩, rest)

def flushTag (done : List DocTag) (current : Option DocTag) : List DocTag :=
  match current with
  | none => done
  | some t => t :: done

/-- Recursion consumes a line or a complete tag and its first content line.
The raw-text wrapper derives the bound from actual bytes. The sufficiency
proof and an independent upstream correspondence theorem remain obligations. -/
def docTagsAux : Nat → Bytes → List DocTag → Option DocTag → Except Error (List DocTag)
  | _, [], done, current => .ok (finishTags done current)
  | 0, _ :: _, _, _ => .error .depth
  | n + 1, bs, done, current =>
    let initial :=  bs.takeWhile (fun b => b != 64 && b != 10)
    let afterInitial := bs.drop initial.length
    if afterInitial.head? == some 64 then
      let tagRest := afterInitial.drop 1
      let name := tagRest.takeWhile (fun b => !tagSeparator b)
      let data := (tagRest.drop name.length).drop 1
      if name.isEmpty && current.isSome then
        match current with
        | none => .error (.field "unreachable empty NatSpec tag")
        | some t =>
          let (t, rest) := appendLine t data
          docTagsAux n rest done (some t)
      else if name == bytes "param" then
        let start := data.dropWhile spaceTab
        if start.isEmpty then .ok (finishTags done current)
        else
          let paramName := if (start.head?.map isIdStart).getD false then
            start.takeWhile isIdPart else []
          let description := (start.drop paramName.length).dropWhile spaceTab
          let (content, rest) := lineBytes description
          if content.isEmpty then .ok (finishTags done current)
          else docTagsAux n rest (flushTag done current) (some ⟨name, content⟩)
      else
        let (content, rest) := lineBytes (data.dropWhile spaceTab)
        docTagsAux n rest (flushTag done current) (some ⟨name, content⟩)
    else
      match current with
      | some t =>
        let (t, rest) := appendLine t bs
        docTagsAux n rest done (some t)
      | none =>
        let (content, rest) := lineBytes (bs.dropWhile spaceTab)
        docTagsAux n rest done (some ⟨bytes "notice", content⟩)

def documentationTags (raw : String) : Except Error (List DocTag) :=
  docTagsAux (raw.toUTF8.size + 1) (bytes raw) [] none

/-- Split exactly on the pinned C++ whitespace set: space, tab, LF and CR.
Non-ASCII whitespace remains part of a token. -/
def docWords (content : Bytes) : List Bytes :=
  (content.splitBy (fun a b => docWhitespace a == docWhitespace b)).filter
    (fun group => !(group.head?.map docWhitespace).getD true)

/-- An independent membership condition over parsed tag data, not a substring
test. This does not prove that parsed data matches the original source comment. -/
def HasMemorySafeTag (tags : List DocTag) : Prop :=
  ∃ tag ∈ tags, tag.name = bytes "solidity" ∧ bytes "memory-safe-assembly" ∈ docWords tag.content

instance (tags : List DocTag) : Decidable (HasMemorySafeTag tags) := by
  unfold HasMemorySafeTag
  infer_instance

/-- The exact metadata premise supplied by this component. The comment branch
requires successful tag parsing AND independent tag/token membership. -/
inductive MetadataSafetyD (flags : List String) : Option String → Prop where
  | flag {doc} : "memory-safe" ∈ flags → MetadataSafetyD flags doc
  | comment {raw tags} : documentationTags raw = .ok tags → HasMemorySafeTag tags →
      MetadataSafetyD flags (some raw)

structure SafetyCertificate (flags : List String) (doc : Option String) : Type where
  derivation : MetadataSafetyD flags doc

def checkMetadataSafety (flags : List String) (doc : Option String) :
    Except Refusal (SafetyCertificate flags doc) :=
  if h : "memory-safe" ∈ flags then .ok ⟨.flag h⟩
  else match doc with
    | none => .error .nonMemorySafe
    | some raw => match hp : documentationTags raw with
      | .error _ => .error .nonMemorySafe
      | .ok tags =>
        if hs : HasMemorySafeTag tags then .ok ⟨.comment hp hs⟩
        else .error .nonMemorySafe

/-- Success has a kernel-typed metadata derivation. It is not a memory-layout,
source attachment, memory-safe execution or compiler refinement theorem. -/
theorem SafetyCertificate.sound {flags doc} (c : SafetyCertificate flags doc) :
    MetadataSafetyD flags doc := c.derivation


/-- Completeness is against the stated metadata premise, including a successful
decoder equality in the comment case, not against an unproved C++ relation. -/
theorem MetadataSafetyD.complete {flags doc} (d : MetadataSafetyD flags doc) :
    ∃ c, checkMetadataSafety flags doc = .ok c := by
  cases d with
  | flag h =>
    exact ⟨⟨.flag h⟩, dif_pos h⟩
  | comment hp hs =>
    by_cases h : "memory-safe" ∈ flags
    · exact ⟨⟨.flag h⟩, dif_pos h⟩
    · refine ⟨⟨.comment hp hs⟩, ?_⟩
      simp only [checkMetadataSafety, dif_neg h]
      split
      · next e he => cases (he.symm.trans hp)
      · next ts he =>
          have ht : ts = _ := Except.ok.inj (he.symm.trans hp)
          cases ht
          exact dif_pos hs

theorem checkMetadataSafety_iff (flags : List String) (doc : Option String) :
    (checkMetadataSafety flags doc).toOption.isSome = true ↔ MetadataSafetyD flags doc := by
  constructor
  · intro h
    cases hc : checkMetadataSafety flags doc with
    | error e =>
      simp only [hc, Except.toOption, Option.isSome] at h
      cases h
    | ok c => exact c.derivation
  · intro d
    obtain ⟨c, hc⟩ := d.complete
    simp only [hc, Except.toOption, Option.isSome]


end Solidity.Frontend.YulJson
