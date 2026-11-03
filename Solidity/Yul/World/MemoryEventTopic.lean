import Solidity.Yul.World.LocalEventBoundary
import Solidity.Yul.Views.Inputs

/-! Direct-word and top-level memory bytes/string event topics. Dynamic topics
hash exact raw contents, not ABI heads, lengths or padding. Aggregates/storage
references remain outside this consumer; no new Source or hash semantics. -/
namespace Solidity.Yul.World.MemoryEventTopic
open Solidity.Source
open Solidity.Roadmap (Word Bytes)
open Solidity.Yul.Views
open Solidity.Yul.World.PhysicalCompletion

def topic {E Γ τ} (G : Glob E) (F : Fr) (n : Nat) (v : Source.Val E.layout τ) : EM E Γ (Option Word) :=
  match v.word with
  | some word => pure (some word)
  | none => match τ with
    | .bytes .memory | .string .memory => do
      let contents←Source.bytesOfRV F n (.val v)
      pure (some (G.fixed.hash contents))
    | _ => pure none

theorem word {E Γ τ} (G : Glob E) (F : Fr) (n : Nat) (v : Source.Val E.layout τ)
    (w : Word) (found : v.word=some w) (s : EMState E Γ) :
    (topic G F n v).run s=(.ok (some w),s) := by
  simp only [topic,found]
  rfl

theorem bytes_read {E Γ} (F : Fr) (n a : Nat) (contents : Bytes) (s : EMState E Γ)
    (found : s.2.heap.get a=some ⟨.bytes .memory,.bytes contents⟩) :
    (Source.bytesOfRV F n (.val (.memRef rfl a : Source.Val E.layout (.bytes .memory)))).run s=(.ok contents,s) := by
  have state : (Source.EM.st : EM E Γ (St E)).run s=(.ok s.2,s) := rfl
  simp only [Source.bytesOfRV,Source.heapBytes,Source.heapObj,Source.Hoare.run_bind,state]
  rw [found]
  rfl

theorem string_read {E Γ} (F : Fr) (n a : Nat) (contents : Bytes) (s : EMState E Γ)
    (found : s.2.heap.get a=some ⟨.string .memory,.string contents⟩) :
    (Source.bytesOfRV F n (.val (.memRef rfl a : Source.Val E.layout (.string .memory)))).run s=(.ok contents,s) := by
  have state : (Source.EM.st : EM E Γ (St E)).run s=(.ok s.2,s) := rfl
  simp only [Source.bytesOfRV,Source.heapBytes,Source.heapObj,Source.Hoare.run_bind,state]
  rw [found]
  rfl

theorem bytes_topic {E Γ} (G : Glob E) (F : Fr) (n a : Nat) (contents : Bytes) (s : EMState E Γ)
    (found : s.2.heap.get a=some ⟨.bytes .memory,.bytes contents⟩) :
    (topic G F n (.memRef rfl a : Source.Val E.layout (.bytes .memory))).run s=(.ok (some (G.fixed.hash contents)),s) := by
  simp only [topic,Source.Val.word,Source.Hoare.run_bind]
  rw [bytes_read F n a contents s found]
  rfl

theorem string_topic {E Γ} (G : Glob E) (F : Fr) (n a : Nat) (contents : Bytes) (s : EMState E Γ)
    (found : s.2.heap.get a=some ⟨.string .memory,.string contents⟩) :
    (topic G F n (.memRef rfl a : Source.Val E.layout (.string .memory))).run s=(.ok (some (G.fixed.hash contents)),s) := by
  simp only [topic,Source.Val.word,Source.Hoare.run_bind]
  rw [string_read F n a contents s found]
  rfl

theorem raw_hash {E : Env} (G : Glob E) (m : ByteView) (offset size : Nat) (contents : Bytes)
    (matched : readBytes m offset size=contents) :
    keccak256 G.fixed.evm m offset size=G.fixed.hash contents := by
  apply Fin.ext
  exact congrArg G.fixed.evm.keccak matched

theorem bytes_codec {E Γ} (F : Fr) (n a : Nat) (contents : Bytes) (s : EMState E Γ)
    (found : s.2.heap.get a=some ⟨.bytes .memory,.bytes contents⟩) :
    (Source.encodeOne F n false (.val (.memRef rfl a : Source.Val E.layout (.bytes .memory)))).run s=
      (.ok (true,contents),s) := by
  simp only [Source.encodeOne,Source.Hoare.run_bind]
  rw [bytes_read F n a contents s found]
  rfl

theorem string_codec {E Γ} (F : Fr) (n a : Nat) (contents : Bytes) (s : EMState E Γ)
    (found : s.2.heap.get a=some ⟨.string .memory,.string contents⟩) :
    (Source.encodeOne F n false (.val (.memRef rfl a : Source.Val E.layout (.string .memory)))).run s=
      (.ok (true,contents),s) := by
  simp only [Source.encodeOne,Source.Hoare.run_bind]
  rw [string_read F n a contents s found]
  rfl

theorem storage_refused {E Γ} (G : Glob E) (F : Fr) (n : Nat) (p : Source.SPath) (s : EMState E Γ) :
    (topic G F n (.storRef rfl p : Source.Val E.layout (.bytes .storage))).run s=(.ok none,s) := rfl

theorem dangling_bytes {E Γ} (G : Glob E) (F : Fr) (n a : Nat) (s : EMState E Γ)
    (missing : s.2.heap.get a=none) :
    (topic G F n (.memRef rfl a : Source.Val E.layout (.bytes .memory))).run s=
      (.error (.stuck "dangling memory reference"),s) := by
  have state : (Source.EM.st : EM E Γ (St E)).run s=(.ok s.2,s) := rfl
  simp only [topic,Source.Val.word,Source.bytesOfRV,Source.heapBytes,Source.heapObj,Source.Hoare.run_bind,state,missing]
  rfl
end Solidity.Yul.World.MemoryEventTopic
