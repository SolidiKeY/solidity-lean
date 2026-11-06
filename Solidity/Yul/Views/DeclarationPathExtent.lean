import Solidity.Yul.Views.DeclarationPathSeparation

namespace Solidity.Yul.Views

theorem declarationMembers_replicate {D τ} (seed : DeclScalar D τ)
    (found : declarationScalar? D τ = some seed) (n : Nat) :
    declarationMembers? D (List.replicate n τ) =
      some (repeatedMembers seed.field seed.width seed.codec n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [List.replicate_succ,declarationMembers?,found,Option.bind_some,ih,Option.map_some]
    rfl

theorem packDeclarationPaths_end (E : Source.Env) (pathAt : Nat → Source.SPath) (a : Roadmap.Address)
    (fields : List (String × Source.STy)) (index cursor : Nat)
    (cs : List (ScalarPath E.layout (E.lay a))) (stop : Nat)
    (members : PackedMembers E.layout (fields.map Prod.snd))
    (prepared : declarationMembers? E.layout (fields.map Prod.snd) = some members)
    (success : packDeclarationPaths E pathAt a index fields cursor = .ok (cs,stop)) :
    stop = members.endByte cursor := by
  induction fields generalizing index cursor cs stop with
  | nil => cases prepared; cases success; rfl
  | cons head rest ih =>
    rcases head with ⟨name,τ⟩
    cases scalar : declarationScalar? E.layout τ with
    | none => simp only [List.map_cons,declarationMembers?,scalar,Option.bind_none] at prepared; cases prepared
    | some seed =>
      cases tailPrepared : declarationMembers? E.layout (rest.map Prod.snd) with
      | none =>
        simp only [List.map_cons,declarationMembers?,scalar,Option.bind_some,tailPrepared,Option.map_none] at prepared
        cases prepared
      | some tail =>
        simp only [List.map_cons,declarationMembers?,scalar,Option.bind_some,tailPrepared,Option.map_some] at prepared
        cases prepared
        simp only [packDeclarationPaths,scalar] at success
        split at success
        · split at success
          · cases next : packDeclarationPaths E pathAt a (index+1) rest
                ((seed.position cursor).start+(seed.position cursor).field.width) with
            | error reason => simp only [next,Except.map] at success; cases success
            | ok result =>
              rcases result with ⟨tailCs,finish⟩
              simp only [next,Except.map,Except.ok.injEq,Prod.mk.injEq] at success
              obtain ⟨rfl,rfl⟩ := success
              exact ih _ _ _ _ tail tailPrepared next
          · cases success
        · cases success

theorem packDeclarationPaths_end_option (E : Source.Env) (pathAt : Nat → Source.SPath) (a : Roadmap.Address)
    (fields : List (String × Source.STy)) (index cursor : Nat)
    (cs : List (ScalarPath E.layout (E.lay a))) (stop : Nat)
    (prepared : (declarationMembers? E.layout (fields.map Prod.snd)).isSome)
    (success : packDeclarationPaths E pathAt a index fields cursor = .ok (cs,stop)) :
    (declarationMembers? E.layout (fields.map Prod.snd)).map (fun members => members.endByte cursor) = some stop := by
  obtain ⟨members,ready⟩ := Option.isSome_iff_exists.mp prepared
  rw [ready,Option.map_some,packDeclarationPaths_end E pathAt a fields index cursor cs stop members ready success]

theorem packDeclarationPaths_paths (E : Source.Env) (pathAt : Nat → Source.SPath) (a : Roadmap.Address)
    (fields : List (String × Source.STy)) (index cursor : Nat)
    (cs : List (ScalarPath E.layout (E.lay a))) (stop : Nat)
    (success : packDeclarationPaths E pathAt a index fields cursor = .ok (cs,stop)) :
    cs.map ScalarPath.path = (List.range' index fields.length).map pathAt := by
  induction fields generalizing index cursor cs stop with
  | nil => cases success; rfl
  | cons head rest ih =>
    rcases head with ⟨name,τ⟩
    cases scalar : declarationScalar? E.layout τ with
    | none => simp only [packDeclarationPaths,scalar] at success; cases success
    | some seed =>
      simp only [packDeclarationPaths,scalar] at success
      split at success
      · split at success
        · cases next : packDeclarationPaths E pathAt a (index+1) rest
              ((seed.position cursor).start+(seed.position cursor).field.width) with
          | error reason => simp only [next,Except.map] at success; cases success
          | ok result =>
            rcases result with ⟨tail,finish⟩
            simp only [next,Except.map,Except.ok.injEq,Prod.mk.injEq] at success
            obtain ⟨rfl,rfl⟩ := success
            simp only [List.map_cons,List.length_cons,List.range'_succ]
            exact congrArg (List.cons (pathAt index)) (ih _ _ _ _ next)
        · cases success
      · cases success

theorem declarationEnd_word_bound {D L} (c : ScalarPath D L) : declarationEnd c ≤ (2^256)*32 := by
  have slot := c.slot.isLt
  have field := c.field.fits
  unfold declarationEnd declarationStart
  omega

/-- Only the real input physical-coordinate bound is needed. Every output
slot has already been constructed as an intrinsic Word by the actual traversal. -/
theorem packDeclarationPaths_bound (E : Source.Env) (pathAt : Nat → Source.SPath) (a : Roadmap.Address)
    (fields : List (String × Source.STy)) (index cursor : Nat)
    (cs : List (ScalarPath E.layout (E.lay a))) (stop : Nat) (initial : cursor ≤ (2^256)*32)
    (success : packDeclarationPaths E pathAt a index fields cursor = .ok (cs,stop)) : stop ≤ (2^256)*32 := by
  induction fields generalizing index cursor cs stop with
  | nil => cases success; exact initial
  | cons head rest ih =>
    rcases head with ⟨name,τ⟩
    cases scalar : declarationScalar? E.layout τ with
    | none => simp only [packDeclarationPaths,scalar] at success; cases success
    | some seed =>
      simp only [packDeclarationPaths,scalar] at success
      split at success
      · rename_i typed
        split at success
        · rename_i bound
          have nextBound := declarationEnd_word_bound ((seed.position cursor).registration (pathAt index) typed a bound)
          rw [declarationEnd,DeclPosition.registration_start] at nextBound
          cases next : packDeclarationPaths E pathAt a (index+1) rest
              ((seed.position cursor).start+(seed.position cursor).field.width) with
          | error reason => simp only [next,Except.map] at success; cases success
          | ok result =>
            rcases result with ⟨tail,finish⟩
            simp only [next,Except.map,Except.ok.injEq,Prod.mk.injEq] at success
            obtain ⟨rfl,rfl⟩ := success
            exact ih _ _ _ _ nextBound next
        · cases success
      · cases success

theorem roundSlot_bounded (a : Nat) (bound : a ≤ (2^256)*32) : roundSlot a ≤ (2^256)*32 := by
  have spec := roundSlot_spec a
  have div := Nat.mod_add_div (roundSlot a) 32
  omega

end Solidity.Yul.Views
