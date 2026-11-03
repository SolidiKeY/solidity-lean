import Solidity.Yul.World.MemoryEventTopic

namespace Solidity.Yul.World.MemoryEventEncoding
open Solidity.Source
open Solidity.Roadmap (Word Bytes)
open Solidity.Yul.World.PhysicalCompletion
open Solidity.Yul.World.StaticEventEncoding (Split metadata topics resultLog)

def split {E Γ} (G : Glob E) (F : Fr) (n : Nat) :
    {ts : List STy} → List Bool → Vals E.layout ts → EM E Γ (Option (Split E.layout))
  | _,[],.nil => pure (some ([],⟨[],.nil⟩))
  | _,flag::flags,.cons v vs => do
    let word←MemoryEventTopic.topic G F n v
    match word with
    | none => pure none
    | some w =>
      let rest←split G F n flags vs
      pure (rest.map fun p=>if flag then (w::p.1,p.2) else (p.1,⟨_,.cons v p.2.2⟩))
  | _,_,_ => pure none

/-- Exact topic hashing and nonindexed data over the existing owner codecs.
Unsupported references refuse; genuine Source read/codec halts propagate. -/
def encode {E Γ ts} (G : Glob E) (F : Fr) (n : Nat) (event : Decl)
    (_typed : event.paramTys E=some ts) (vs : Vals E.layout ts) : EM E Γ (Option Log) :=
  match metadata event with
  | none => pure none
  | some (flags,anonymous) => do
    let computed←split G F n flags vs
    match computed with
    | none => pure none
    | some part =>
      if fits : (topics (ts:=ts) G event anonymous part).length<5 then do
        let bytes←Source.encodeVals F n false part.2.2.toR
        pure (some (resultLog (ts:=ts) G F event anonymous part fits bytes))
      else pure none

theorem encode_exact {E Γ ts} (G : Glob E) (F : Fr) (n : Nat) (event : Decl)
    (typed : event.paramTys E=some ts) (vs : Vals E.layout ts) (s : EMState E Γ)
    (flags : List Bool) (anonymous : Bool) (shape : metadata event=some (flags,anonymous))
    (part : Split E.layout) (partition : (split G F n flags vs).run s=(.ok (some part),s))
    (bytes : Bytes) (codec : (Source.encodeVals F n false part.2.2.toR).run s=(.ok bytes,s))
    (fits : (topics (ts:=ts) G event anonymous part).length<5) :
    (encode G F n event typed vs).run s=(.ok (some (resultLog (ts:=ts) G F event anonymous part fits bytes)),s) := by
  simp only [encode,shape,Source.Hoare.run_bind]
  rw [partition]
  dsimp only
  rw [dif_pos fits,Source.Hoare.run_bind,codec]
  rfl

theorem overflow_refused {E Γ ts} (G : Glob E) (F : Fr) (n : Nat) (event : Decl)
    (typed : event.paramTys E=some ts) (vs : Vals E.layout ts) (s : EMState E Γ)
    (flags : List Bool) (anonymous : Bool) (shape : metadata event=some (flags,anonymous))
    (part : Split E.layout) (partition : (split G F n flags vs).run s=(.ok (some part),s))
    (overflow : ¬(topics (ts:=ts) G event anonymous part).length<5) :
    (encode G F n event typed vs).run s=(.ok none,s) := by
  simp only [encode,shape,Source.Hoare.run_bind]
  rw [partition]
  dsimp only
  rw [dif_neg overflow]
  rfl
end Solidity.Yul.World.MemoryEventEncoding
