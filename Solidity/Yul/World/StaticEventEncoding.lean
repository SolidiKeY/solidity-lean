import Solidity.Yul.World.StaticEventArgs

/-! Declaration-driven direct-word event encoding. The original argument
values and selected nonindexed values stay intrinsic; Source.encodeVals owns
ABI data. Dynamic/reference/indexed aggregate hashing is outside this port. -/
namespace Solidity.Yul.World.StaticEventEncoding
open Solidity.Source
open Solidity.Roadmap (Word Bytes)
open Solidity.Yul.World.StaticEventArgs
open Solidity.Yul.World.PhysicalCompletion

abbrev Split (D : Layout) := List Word × (Σ ts : List STy, Vals D ts)

def indexedFlags : Syn (.list .eventParam) → List Bool
  | .nil => []
  | .cons (.eventParam _ flag _) rest => flag::indexedFlags rest

def metadata (event : Decl) : Option (List Bool × Bool) :=
  match event.kind,event.top,event.node with
  | .event,_,.event _ params anonymous => some (indexedFlags params,anonymous)
  | _,_,_ => none

def split {D : Layout} : {ts : List STy} → List Bool → Vals D ts → Option (Split D)
  | _,[],.nil => some ([],⟨[],.nil⟩)
  | _,flag::flags,.cons v vs => do
    let word←v.word
    let rest←split flags vs
    pure (if flag then (word::rest.1,rest.2) else (rest.1,⟨_ , .cons v rest.2.2⟩))
  | _,_,_ => none

/-- Actual partition success derives both original and selected static codec
premises. No supplied encoding/adequacy theorem is a certificate field. -/
theorem split_words {D ts} (flags : List Bool) (vs : Vals D ts) (part : Split D)
    (computed : split flags vs=some part) :
    (∃ words,words? vs=some words) ∧ (∃ words,words? part.2.2=some words) := by
  induction vs generalizing flags part with
  | nil =>
    cases flags with
    | nil => cases computed; exact ⟨⟨[],rfl⟩,⟨[],rfl⟩⟩
    | cons flag flags => cases computed
  | @cons ty ts v vs ih =>
    cases flags with
    | nil => cases computed
    | cons flag flags =>
      cases word : v.word with
      | none => simp only [split,word,bind,Option.bind_none] at computed; cases computed
      | some w =>
        cases rest : split flags vs with
        | none => simp only [split,word,rest,bind,Option.bind_some,Option.bind_none] at computed; cases computed
        | some tail =>
          obtain ⟨⟨all,allComputed⟩,⟨data,dataComputed⟩⟩:=ih flags tail rest
          cases flag <;> simp only [split,word,rest,Bool.false_eq_true,if_false,if_true,bind,Option.bind_some,pure,Option.some.injEq] at computed
          · subst part
            exact ⟨⟨w::all,by simp only [words?,word,allComputed,bind,Option.bind_some,pure]⟩,
              ⟨w::data,by simp only [words?,word,dataComputed,bind,Option.bind_some,pure]⟩⟩
          · subst part
            exact ⟨⟨w::all,by simp only [words?,word,allComputed,bind,Option.bind_some,pure]⟩,⟨data,dataComputed⟩⟩

def topics {E : Env} {ts : List STy} (G : Glob E) (event : Decl) (anonymous : Bool) (part : Split E.layout) : List Word :=
  if anonymous then part.1 else G.fixed.hash (asciiBytes (sigOf E.layout event.name ts))::part.1

/-- Type equality is the actual Source.emit declaration/argument relation.
Topic capacity is checked; no fourth nonanonymous indexed argument is dropped. -/
def encode {E Γ ts} (G : Glob E) (F : Fr) (n : Nat) (event : Decl)
    (_typed : event.paramTys E=some ts) (vs : Vals E.layout ts) : EM E Γ (Option Log) :=
  match metadata event with
  | none => pure none
  | some (flags,anonymous) =>
    match split flags vs with
    | none => pure none
    | some part =>
      let words:=topics (ts:=ts) G event anonymous part
      if bound : words.length<5 then do
        let bytes←Source.encodeVals F n false part.2.2.toR
        pure (some ⟨F.this,⟨words.length,bound⟩,words.toArray.toVector,bytes⟩)
      else pure none

theorem overflow_refused {E Γ ts} (G : Glob E) (F : Fr) (n : Nat) (event : Decl)
    (typed : event.paramTys E=some ts) (vs : Vals E.layout ts) (s : EMState E Γ)
    (flags : List Bool) (anonymous : Bool) (shape : metadata event=some (flags,anonymous))
    (part : Split E.layout) (partition : split flags vs=some part)
    (overflow : ¬(topics (ts:=ts) G event anonymous part).length<5) :
    (encode G F n event typed vs).run s=(.ok none,s) := by
  simp only [encode,shape,partition,overflow]
  rfl

def resultLog {E : Env} {ts : List STy} (G : Glob E) (F : Fr) (event : Decl)
    (anonymous : Bool) (part : Split E.layout)
    (fits : (topics (ts:=ts) G event anonymous part).length<5) (bytes : Bytes) : Log :=
  ⟨F.this,⟨(topics (ts:=ts) G event anonymous part).length,fits⟩,
    (topics (ts:=ts) G event anonymous part).toArray.toVector,bytes⟩

theorem encode_exact {E Γ ts} (G : Glob E) (F : Fr) (n : Nat) (event : Decl)
    (typed : event.paramTys E=some ts) (vs : Vals E.layout ts) (s : EMState E Γ)
    (flags : List Bool) (anonymous : Bool) (shape : metadata event=some (flags,anonymous))
    (part : Split E.layout) (partition : split flags vs=some part)
    (ws : List Word) (computed : words? part.2.2=some ws)
    (fits : (topics (ts:=ts) G event anonymous part).length<5) :
    (encode G F n event typed vs).run s=(.ok (some (resultLog (ts:=ts) G F event anonymous part fits
      (Source.abiLayout (ws.map (fun w=>(false,wordBytes w)))))),s) := by
  simp only [encode,shape,partition,dif_pos fits]
  rw [Source.Hoare.run_bind,encodeVals_words F n part.2.2 ws computed]
  rfl

/-- Successful concrete partition itself supplies the codec premise. -/
theorem encode_prepared {E Γ ts} (G : Glob E) (F : Fr) (n : Nat) (event : Decl)
    (typed : event.paramTys E=some ts) (vs : Vals E.layout ts) (s : EMState E Γ)
    (flags : List Bool) (anonymous : Bool) (shape : metadata event=some (flags,anonymous))
    (part : Split E.layout) (partition : split flags vs=some part)
    (fits : (topics (ts:=ts) G event anonymous part).length<5) :
    ∃ ws,words? part.2.2=some ws ∧
      (encode G F n event typed vs).run s=(.ok (some (resultLog (ts:=ts) G F event anonymous part fits
        (Source.abiLayout (ws.map (fun w=>(false,wordBytes w)))))),s) := by
  obtain ⟨ws,computed⟩:=(split_words flags vs part partition).2
  exact ⟨ws,computed,encode_exact G F n event typed vs s flags anonymous shape part partition ws computed fits⟩
end Solidity.Yul.World.StaticEventEncoding
