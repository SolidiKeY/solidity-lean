import Solidity.Backend.MemoryOps.SourceCalldataSliceRead

/-! Single Source slice reads agree with the selected element of an ACTUAL
successful existing checked fresh transfer. Whole-window decoder success is
needed for that copy, not for a lazy Source read. No Source heap/target machine
representation is invented for the independently supplied initial native heap. -/
namespace Solidity.Backend.MemoryOps

private theorem source_mapM_element {α β : Type} (f : α → Source.R β)
    (xs : List α) (ys : List β) (decoded : xs.mapM f=.ok ys)
    (i : Nat) (x : α) (hit : xs[i]?=some x) :
    ∃ value,ys[i]?=some value ∧ f x=.ok value := by
  first
  | solve
    | rfl
    | simp only [List.mapM_cons]
    | decide
    | omega
  | induction xs generalizing ys i with
    | nil => simp only [List.getElem?_nil] at hit;cases hit
    | cons a xs ih =>
      rw [List.mapM_cons] at decoded
      cases head : f a with
      | error err => simp only [head,bind,Except.bind] at decoded;cases decoded
      | ok value =>
        simp only [head,bind,Except.bind] at decoded
        cases tail : xs.mapM f with
        | error err => simp only [tail] at decoded;cases decoded
        | ok rest =>
          simp only [tail,pure,Except.pure] at decoded
          cases Except.ok.inj decoded
          cases i with
          | zero =>
            simp only [List.getElem?_cons_zero,Option.some.injEq] at hit
            cases hit
            exact ⟨value,rfl,head⟩
          | succ i =>
            have tailHit : xs[i]?=some x := hit
            obtain ⟨v,hv,hf⟩ := ih rest tail i tailHit
            exact ⟨v,hv,hf⟩

/-- Successful computed traversal determines the selected word's own decoder
result. This is extraction from the actual mapM, not payload agreement input. -/
theorem source_bool_decoded_element {E : Source.Env} (F : Source.Fr) (off len i : Nat)
    (vs : List (Source.Val E.layout .bool))
    (decoded : sourceCalldataBoolValues E F off len=.ok vs) (bound : i<len) :
    ∃ v, vs[i]?=some v ∧ Source.decodeWord E.layout (Source.cdWordAt F (off+32*i)) .bool=.ok v := by
  have rangeHit : (List.range len)[i]?=some i := by
    rw [List.getElem?_eq_getElem (by rw [List.length_range];exact bound),List.getElem_range]
  exact source_mapM_element (fun j => Source.decodeWord E.layout (Source.cdWordAt F (off+32*j)) .bool)
    (List.range len) vs decoded i i rangeHit

/-- The actual Source read and actual checked transfer reach matching Boolean
observations from computed initial bytes. The native fresh object/identity and
all old native frames follow from existing alloc and checked-copy execution.
No Source input-heap/native-heap relation or emitted target state is claimed. -/
theorem source_bool_slice_index_checked {E : Source.Env} {Γ : Source.RCtx} {H : HTy}
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat) (y : Source.EMState E Γ)
    (root : Source.Idx Γ (.array .calldata .bool none))
    (start finish index : Source.Idx Γ (.int .u256)) (off len : Nat)
    (s e k : PrimTy.uint.Denote) (toEnd : Bool)
    (hr : y.1.get root=.cdRef rfl off len)
    (hs : y.1.get start=sourceUint s) (he : y.1.get finish=sourceUint e)
    (hk : y.1.get index=sourceUint k)
    (ordered : s.1.toNat≤(if toEnd then len else e.1.toNat))
    (bounded : (if toEnd then len else e.1.toNat)≤len)
    (inside : k.1.toNat<(if toEnd then len else e.1.toNat)-s.1.toNat)
    (hp : Heap H) (cap : ((if toEnd then len else e.1.toNat)-s.1.toNat)<2^256)
    (vs : List (Source.Val E.layout .bool))
    (decoded : sourceCalldataBoolValues E F (off+32*s.1.toNat)
      ((if toEnd then len else e.1.toNat)-s.1.toNat)=.ok vs) :
    ∃ (valid : (sourceBoolValuePayload vs).length<2^256) (value : Bool),
      let obj : MObj H (.array (.prim .bool)) := ⟨sourceBoolValuePayload vs,valid⟩
      let pair := hp.alloc obj
      (Source.evalE G F (fuel+3) (sourceSliceIndex .bool rfl root start finish index toEnd)).run y=
        (.ok (.val (.bool value)),y) ∧
      checkedSourceFreshBools (E := E) F (off+32*s.1.toNat)
        ((if toEnd then len else e.1.toNat)-s.1.toNat) hp cap=.ok (some pair.1) ∧
      pair.1.index pair.2 .dyn k=some value ∧
      Heap.Keeps (List.prefix_append H [RefTy.array (.prim .bool)]) hp pair.1 ∧
      pair.2.id=H.length := by
  obtain ⟨v,hit,word⟩ := source_bool_decoded_element F (off+32*s.1.toNat)
    ((if toEnd then len else e.1.toNat)-s.1.toNat) k.1.toNat vs decoded inside
  let value := calldataBool (Source.Data.val v)
  have exactValue : v=Source.Val.bool value := Source.Data.val.inj (calldataBool_exact (.val v))
  have address : off+32*s.1.toNat+32*k.1.toNat=off+32*(s.1.toNat+k.1.toNat) := by omega
  have selectedWord : Source.decodeWord E.layout
      (Source.cdWordAt F (off+32*(s.1.toNat+k.1.toNat))) .bool=.ok (.bool value) := by
    rw [←address]
    exact word.trans (congrArg Except.ok exactValue)
  have payloadHit : (sourceBoolValuePayload vs)[k.1.toNat]?=some value := by
    simp only [sourceBoolValuePayload,List.getElem?_map,hit,Option.map_some]
    rfl
  obtain ⟨valid,checked,run⟩ := checkedSourceFreshBools_some F (off+32*s.1.toNat)
    ((if toEnd then len else e.1.toNat)-s.1.toNat) hp cap vs decoded
  refine ⟨valid,value,?_,run,?_,hp.keeps_alloc _,rfl⟩
  · rw [source_slice_index_eval .bool rfl G F fuel y root start finish index off len s e k toEnd hr hs he hk,
      if_neg (Nat.not_lt.mpr ordered),if_neg (Nat.not_lt.mpr bounded),if_pos inside,selectedWord]
  · change (MObj.elems .dyn ((hp.alloc (R := .array (.prim .bool))
      (⟨sourceBoolValuePayload vs,valid⟩ : MObj H (.array (.prim .bool)))).1.get
      (hp.alloc (R := .array (.prim .bool)) (⟨sourceBoolValuePayload vs,valid⟩ : MObj H (.array (.prim .bool)))).2))[k.1.toNat]?=some value
    rw [Heap.get_alloc,MObj.elems_wk,MObj.elems_dyn]
    simp only [List.map_id'' (f := MVal.wk (List.prefix_append H [RefTy.array (.prim .bool)]) (.prim .bool)) (fun _ => rfl)]
    exact payloadHit

/-- info: 'Solidity.Backend.MemoryOps.source_bool_decoded_element' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms source_bool_decoded_element
/-- info: 'Solidity.Backend.MemoryOps.source_bool_slice_index_checked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms source_bool_slice_index_checked
end Solidity.Backend.MemoryOps
