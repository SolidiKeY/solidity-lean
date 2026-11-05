import Solidity.Yul.Views.DeclarationPacking
import Solidity.Yul.Views.NestedDeclarationReset

/-! Defaults of actual declaration-selected canonical codecs. Available Source
defaults encode as zero; unavailable defaults remain none, including function
types. This does not strengthen arbitrary ScalarCodec or alter Source defaults. -/
namespace Solidity.Yul.Views.DeclarationDefaults

theorem zero_bytes (n : Nat) : Source.beValue (List.replicate n 0)=0 := by
  first | (simp only;done) | skip
  induction n with
  | zero => rfl
  | succ n ih =>
    change ((List.replicate n 0).foldl (fun (acc : Nat) (byte : UInt8) => acc*256+byte.toNat) 0)=0
    exact ih

theorem payload {D τ} (seed : DeclScalar D τ) (computed : declarationScalar? D τ=some seed) :
    (Source.Val.default D τ).map (fun value => (seed.codec.encode value).val)=
      (Source.Val.default D τ).map (fun _ => 0) := by
  first | (simp only;done) | skip
  cases τ with
  | bool => cases computed; rfl
  | int t => cases computed; rfl
  | fixed t => cases computed; rfl
  | address payable => cases computed; rfl
  | contract name => cases computed; rfl
  | fixedBytes n valid =>
    cases computed
    change some (Source.beValue (List.replicate n 0))=some 0
    rw [zero_bytes]
  | enum name =>
    by_cases bounded : 0<D.enumSize name ∧ D.enumSize name≤256
    · simp only [declarationScalar?,dif_pos bounded] at computed
      cases computed
      simp only [Source.Val.default,dif_pos bounded.1,Option.map_some]
      rfl
    · simp only [declarationScalar?,dif_neg bounded] at computed
      cases computed
  | fn external ps rs mode =>
    cases external <;> cases computed <;> rfl
  | _ => cases computed

theorem available {D τ} (seed : DeclScalar D τ) (computed : declarationScalar? D τ=some seed)
    (value : Source.Val D τ) (actual : Source.Val.default D τ=some value) :
    (seed.codec.encode value).val=0 := by
  have equal := payload seed computed
  rw [actual] at equal
  exact Option.some.inj equal

theorem position {D τ} (seed : DeclScalar D τ) (computed : declarationScalar? D τ=some seed)
    (cursor : Nat) :
    (Source.Val.default D τ).map (fun value => ((seed.position cursor).codec.encode value).val)=
      (Source.Val.default D τ).map (fun _ => 0) :=
  payload seed computed
theorem registration {E : Source.Env} {τ} (seed : DeclScalar E.layout τ) (computed : declarationScalar? E.layout τ=some seed)
    (cursor : Nat) (path : Source.SPath) (typed : E.cellTy path=τ) (a : Roadmap.Address)
    (bound : (seed.position cursor).start/32<2^256) :
    let c := (seed.position cursor).registration path typed a bound
    (Source.Val.default E.layout (E.lay a c.path)).map (fun value => (c.codec.encode value).val)=
      (Source.Val.default E.layout (E.lay a c.path)).map (fun _ => 0) := by
  cases typed
  exact position seed computed cursor

theorem packed {E : Source.Env} (pathAt : Nat → Source.SPath) (a : Roadmap.Address)
    (fields : List (String × Source.STy)) (index cursor : Nat) (cs : List (ScalarPath E.layout (E.lay a))) (stop : Nat)
    (success : packDeclarationPaths E pathAt a index fields cursor=.ok (cs,stop)) :
    ∀ c ∈ cs, (Source.Val.default E.layout (E.lay a c.path)).map (fun value => (c.codec.encode value).val)=
      (Source.Val.default E.layout (E.lay a c.path)).map (fun _ => 0) := by
  first | (simp only;done) | skip
  induction fields generalizing index cursor cs stop with
  | nil => cases success; intro c member; cases member
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
          cases next : packDeclarationPaths E pathAt a (index+1) rest
              ((seed.position cursor).start+(seed.position cursor).field.width) with
          | error reason => simp only [next,Except.map] at success; cases success
          | ok result =>
            rcases result with ⟨tail,finish⟩
            simp only [next,Except.map,Except.ok.injEq,Prod.mk.injEq] at success
            obtain ⟨rfl,rfl⟩ := success
            intro c member
            rcases List.mem_cons.mp member with same | later
            · subst c
              exact registration seed scalar cursor _ typed a bound
            · exact ih (index+1) _ tail finish next c later
        · cases success
      · cases success
theorem packed_check {E : Source.Env} (pathAt : Nat → Source.SPath) (a : Roadmap.Address)
    (fields : List (String × Source.STy)) (index cursor : Nat) (cs : List (ScalarPath E.layout (E.lay a))) (stop : Nat)
    (success : packDeclarationPaths E pathAt a index fields cursor=.ok (cs,stop)) :
    scalarZeroDefaultCheck cs=cs.all (fun c => (Source.Val.default E.layout (E.lay a c.path)).isSome) := by
  first | (simp only;done) | skip
  have each : ∀ c ∈ cs, ((Source.Val.default E.layout (E.lay a c.path)).map (fun value => (c.codec.encode value).val) == some 0)=
      (Source.Val.default E.layout (E.lay a c.path)).isSome := by
    intro c member
    rw [packed pathAt a fields index cursor cs stop success c member]
    cases Source.Val.default E.layout (E.lay a c.path) <;> rfl
  apply Bool.eq_iff_iff.mpr
  simp only [scalarZeroDefaultCheck,List.all_eq_true]
  constructor
  · intro checked c member
    rw [←each c member]
    exact checked c member
  · intro checked c member
    rw [each c member]
    exact checked c member

theorem packed_available {E : Source.Env} (pathAt : Nat → Source.SPath) (a : Roadmap.Address)
    (fields : List (String × Source.STy)) (index cursor : Nat) (cs : List (ScalarPath E.layout (E.lay a))) (stop : Nat)
    (success : packDeclarationPaths E pathAt a index fields cursor=.ok (cs,stop))
    (present : ∀ c ∈ cs, (Source.Val.default E.layout (E.lay a c.path)).isSome=true) :
    ∀ c ∈ cs, ∃ value, Source.Val.default E.layout (E.lay a c.path)=some value ∧ (c.codec.encode value).val=0 := by
  intro c member
  have payload := packed pathAt a fields index cursor cs stop success c member
  cases actual : Source.Val.default E.layout (E.lay a c.path) with
  | none => have available := present c member; rw [actual] at available; cases available
  | some value =>
    rw [actual] at payload
    exact ⟨value,rfl,Option.some.inj payload⟩
end Solidity.Yul.Views.DeclarationDefaults
