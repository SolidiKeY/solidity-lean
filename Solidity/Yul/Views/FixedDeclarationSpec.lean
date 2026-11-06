import Solidity.Yul.Views.FixedDeclarationPack

namespace Solidity.Yul.Views

def fixedExtend (p : Source.SPath) (suffix : List Source.Step) : Source.SPath := ⟨p.root,p.steps++suffix⟩
def FixedBelow (p q : Source.SPath) : Prop := ∃ suffix, q = fixedExtend p suffix

theorem fixedBelow_refl (p : Source.SPath) : FixedBelow p p := by
  refine ⟨[],?_⟩
  cases p
  simp only [fixedExtend,List.append_nil]

theorem fixedBelow_child {p q : Source.SPath} {step : Source.Step} (h : FixedBelow (p.go step) q) : FixedBelow p q := by
  obtain ⟨suffix,rfl⟩ := h
  exact ⟨step::suffix,by simp only [fixedExtend,Source.SPath.go,List.append_assoc,List.singleton_append]⟩

theorem fixedBelow_children_ne {p q r : Source.SPath} {s t : Source.Step}
    (different : s ≠ t) (left : FixedBelow (p.go s) q) (right : FixedBelow (p.go t) r) : q ≠ r := by
  obtain ⟨xs,rfl⟩ := left
  obtain ⟨ys,rfl⟩ := right
  intro same
  have steps := congrArg Source.SPath.steps same
  simp only [fixedExtend,Source.SPath.go,List.append_assoc,List.singleton_append] at steps
  exact different (List.cons.inj (List.append_cancel_left steps)).1

/-- A derived operational specification, never a caller-supplied layout law. -/
def FixedPackGood {E : Source.Env} (pack : FixedPackFn E) : Prop :=
  ∀ path a cursor cs stop, pack path a cursor = .ok (cs,stop) →
    cursor ≤ stop ∧ (cursor ≤ (2^256)*32 → stop ≤ (2^256)*32) ∧ finiteSeparated cs ∧
    ∀ c ∈ cs, cursor ≤ declarationStart c ∧ declarationEnd c ≤ stop ∧ FixedBelow path c.path

def FixedRowsGood {E : Source.Env} (step : Nat → Source.Step) (count : Nat) (pack : Nat → FixedPackFn E) : Prop :=
  ∀ index path a cursor cs stop, pack index path a cursor = .ok (cs,stop) →
    cursor ≤ stop ∧ (cursor ≤ (2^256)*32 → stop ≤ (2^256)*32) ∧ finiteSeparated cs ∧
    ∀ c ∈ cs, ∃ i, index ≤ i ∧ i < index+count ∧ cursor ≤ declarationStart c ∧
      declarationEnd c ≤ stop ∧ FixedBelow (path.go (step i)) c.path

abbrev FixedFieldsGood {E : Source.Env} := @FixedRowsGood E Source.Step.field

theorem alignFixedPack_good {E} (body : FixedPackFn E) (good : FixedPackGood body) : FixedPackGood (alignFixedPack body) := by
  intro path a cursor cs stop success
  unfold alignFixedPack at success
  cases encoded : body path a (roundSlot cursor) with
  | error reason => simp only [encoded,Except.map] at success; cases success
  | ok result =>
    rcases result with ⟨out,last⟩
    simp only [encoded,Except.map,Except.ok.injEq,Prod.mk.injEq] at success
    obtain ⟨rfl,rfl⟩ := success
    have spec := good path a (roundSlot cursor) out last encoded
    have lower := (roundSlot_spec cursor).1
    have upper := (roundSlot_spec last).1
    refine ⟨by omega,(fun bound => roundSlot_bounded _ (spec.2.1 (roundSlot_bounded _ bound))),spec.2.2.1,?_⟩
    intro c member
    obtain ⟨lo,hi,below⟩ := spec.2.2.2 c member
    exact ⟨by omega,by omega,below⟩

theorem fixedScalar_good (E : Source.Env) (τ : Source.STy) :
    FixedPackGood (fun path a cursor => packDeclarationPaths E (fun _ => path) a 0 [("",τ)] cursor) := by
  intro path a cursor cs stop success
  cases found : declarationScalar? E.layout τ with
  | none => simp only [packDeclarationPaths,found] at success; cases success
  | some seed =>
    simp only [packDeclarationPaths,found] at success
    split at success
    · rename_i typed
      split at success
      · rename_i bound
        simp only [Except.map,Except.ok.injEq,Prod.mk.injEq] at success
        obtain ⟨rfl,rfl⟩ := success
        let c := (seed.position cursor).registration path typed a bound
        have coordinate : declarationStart c = (seed.position cursor).start := DeclPosition.registration_start _ _ _ _ _
        have lower := (seed.position_bounds cursor).1
        have endValue : declarationEnd c = (seed.position cursor).start+(seed.position cursor).field.width := by
          unfold declarationEnd
          rw [coordinate]
          rfl
        have endBound := declarationEnd_word_bound c
        rw [endValue] at endBound
        refine ⟨by omega,(fun _ => endBound),List.pairwise_singleton _ _,?_⟩
        intro d member
        have same := List.mem_singleton.mp member
        subst d
        exact ⟨by rw [coordinate]; exact lower,by rw [endValue]; exact Nat.le_refl _,fixedBelow_refl path⟩
      · cases success
    · cases success

theorem packFixedRow_good {E} (step : Nat → Source.Step)
    (injective : Function.Injective step) (count : Nat) (head : FixedPackFn E)
    (tail : Nat → FixedPackFn E) (headGood : FixedPackGood head)
    (tailGood : FixedRowsGood step count tail) :
    FixedRowsGood step (count+1) (packFixedRow step head tail) := by
  intro index path a cursor cs stop success
  unfold packFixedRow at success
  cases first : head (path.go (step index)) a cursor with
  | error reason => simp only [first,Except.bind] at success; cases success
  | ok result =>
    rcases result with ⟨left,middle⟩
    cases second : tail (index+1) path a middle with
    | error reason => simp only [first,second,Except.bind,Except.map] at success; cases success
    | ok result =>
      rcases result with ⟨right,last⟩
      simp only [first,second,Except.bind,Except.map,Except.ok.injEq,Prod.mk.injEq] at success
      obtain ⟨rfl,rfl⟩ := success
      obtain ⟨lower,leftBound,leftSep,leftMembers⟩ := headGood _ _ _ _ _ first
      obtain ⟨upper,rightBound,rightSep,rightMembers⟩ := tailGood _ _ _ _ _ _ second
      refine ⟨by omega,(fun bound => rightBound (leftBound bound)),?_,?_⟩
      · apply List.pairwise_append.mpr
        refine ⟨leftSep,rightSep,?_⟩
        intro c hc d hd
        obtain ⟨cl,ch,cp⟩ := leftMembers c hc
        obtain ⟨j,jl,jh,dl,dh,dp⟩ := rightMembers d hd
        refine ⟨fixedBelow_children_ne (fun same => ?_) cp dp,pathsApart_of_span c d (by omega)⟩
        have : index = j := injective same
        omega
      · intro c member
        rcases List.mem_append.mp member with h | h
        · obtain ⟨lo,hi,below⟩ := leftMembers c h
          exact ⟨index,Nat.le_refl _,by omega,lo,by omega,below⟩
        · obtain ⟨j,jl,jh,lo,hi,below⟩ := rightMembers c h
          exact ⟨j,by omega,by omega,by omega,hi,below⟩

theorem fixedRowsNil_good {E} (step : Nat → Source.Step) :
    FixedRowsGood (E := E) step 0 (fun _ _ _ cursor => .ok ([],cursor)) := by
  intro index path a cursor cs stop success
  cases success
  exact ⟨Nat.le_refl _,(fun h => h),(by constructor),by intro c h; cases h⟩

theorem packFixedElements_good {E} (child : FixedPackFn E) (good : FixedPackGood child) (count : Nat) :
    FixedRowsGood Source.Step.index count (fun index path a cursor => packFixedElements child path a index count cursor) := by
  induction count with
  | zero => exact fixedRowsNil_good Source.Step.index
  | succ n ih => exact packFixedRow_good Source.Step.index (fun _ _ h => Source.Step.index.inj h) n child _ good ih

theorem fixedRows_body_good {E} (step : Nat → Source.Step) (count : Nat) (pack : Nat → FixedPackFn E)
    (good : FixedRowsGood step count pack) : FixedPackGood (pack 0) := by
  intro path a cursor cs stop success
  obtain ⟨lo,bound,sep,members⟩ := good 0 path a cursor cs stop success
  refine ⟨lo,bound,sep,?_⟩
  intro c hc
  obtain ⟨i,_,_,cl,ch,below⟩ := members c hc
  exact ⟨cl,ch,fixedBelow_child below⟩

mutual
theorem FixedDeclaration.pack_good {E : Source.Env} {τ : Source.STy} (d : FixedDeclaration E τ) :
    FixedPackGood d.pack := by
  cases d with
  | scalar τ supported => exact fixedScalar_good E τ
  | array count positive element =>
    exact alignFixedPack_good _ (fixedRows_body_good Source.Step.index count _
      (packFixedElements_good element.pack element.pack_good count))
  | strct name fields found members =>
    exact alignFixedPack_good _ (fixedRows_body_good Source.Step.field (fields.map Prod.snd).length _ members.pack_good)

theorem FixedDeclarationFields.pack_good {E : Source.Env} {τs : List Source.STy}
    (d : FixedDeclarationFields E τs) : FixedFieldsGood τs.length d.pack := by
  cases d with
  | nil => exact fixedRowsNil_good Source.Step.field
  | cons head tail =>
    exact packFixedRow_good Source.Step.field (fun _ _ h => Source.Step.field.inj h) _ _ _ head.pack_good tail.pack_good
end

end Solidity.Yul.Views
