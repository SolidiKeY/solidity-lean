import Solidity.Yul.World.IndexedEmitSequenceRaw

/-! Declaration-independent static event arguments over actual intrinsic Source
Vals. ABI words and bytes reuse Val.word and Source.encodeVals, not a second ABI. -/
namespace Solidity.Yul.World.StaticEventArgs
open Solidity.Source
open Solidity.Roadmap (Word Bytes)

def words? {D : Layout} : {τs : List STy} → Vals D τs → Option (List Word)
  | _,.nil => some []
  | _,.cons v vs => do
    let word←v.word
    let rest←words? vs
    pure (word::rest)

theorem encodeOne_word {E Γ τ} (F : Fr) (n : Nat) (v : Source.Val E.layout τ) (w : Word)
    (encoded : v.word=some w) (s : EMState E Γ) :
    (Source.encodeOne F n false (.val v)).run s=(.ok (false,wordBytes w),s) := by
  cases v <;> first
  | (solve | simp only [Source.Val.word] at encoded; cases encoded)
  | (simp only [Source.encodeOne,encoded]; rfl)

theorem encodeParts_words {E Γ τs} (F : Fr) (n : Nat) (vs : Vals E.layout τs)
    (ws : List Word) (computed : words? vs=some ws) (s : EMState E Γ) :
    (Source.encodeParts F n false vs.toR).run s=(.ok (ws.map (fun w=>(false,wordBytes w))),s) := by
  induction vs generalizing ws with
  | nil =>
    change some []=some ws at computed
    cases computed
    rfl
  | @cons τ τs v vs ih =>
    cases word : v.word with
    | none => simp only [words?,word,bind,Option.bind_none] at computed; cases computed
    | some w =>
      cases rest : words? vs with
      | none => simp only [words?,word,rest,bind,Option.bind_some,Option.bind_none] at computed; cases computed
      | some tail =>
        have result : ws=w::tail := by
          simpa only [words?,word,rest,bind,Option.bind_some,pure,Option.pure_def,Option.some.injEq] using computed.symm
        rw [result]
        change ((do pure ((←Source.encodeOne F n false (.val v))::(←Source.encodeParts F n false vs.toR))) : EM E Γ _).run s=_
        simp only [Source.Hoare.run_bind,encodeOne_word F n v w word,ih tail rest]
        rfl

theorem encodeVals_words {E Γ τs} (F : Fr) (n : Nat) (vs : Vals E.layout τs)
    (ws : List Word) (computed : words? vs=some ws) (s : EMState E Γ) :
    (Source.encodeVals F n false vs.toR).run s=(.ok (Source.abiLayout (ws.map (fun w=>(false,wordBytes w)))),s) := by
  unfold Source.encodeVals
  rw [Source.Hoare.run_bind,encodeParts_words F n vs ws computed]
  rfl
end Solidity.Yul.World.StaticEventArgs
