import Solidity.Backend.MemoryOps.PhysicalLocalDeleteGoal

/-! Actual parent-pointer redirection followed by a reached primitive child
write. Existing typed/word/byte operations are composed. Physical footprint
separation is local and sufficient, not a Source admission restriction. -/
namespace Solidity.Backend.MemoryOps.Physical

/-- A reference-slot write frames a primitive child's INITIAL word layout.
Object inequality follows from intrinsic types; only physical cells need the
explicit local separation hypothesis. -/
theorem primitive_words_after_reference {H : HTy} {R : RefTy} {p : PrimTy}
    {hp : Heap H} (root : HRef H (.array (.ref R))) (replacement : HRef H R)
    (child : HRef H (.array (.prim p))) (base : Nat → Fin Evm.W) (m : Evm.Machine)
    (i : Nat) (words : Evm.Memory.ArrayRepr hp child (base child.id) m)
    (separate : ∀ c,(base child.id).val≤c ∧ c<(base child.id).val+1+hp.len child .dyn →
      c≠(base root.id).val+1+i) :
    Evm.Memory.ArrayRepr (hp.set root (MObj.setElem .dyn (hp.get root) i replacement)) child (base child.id)
      (Evm.Memory.writeMachine m ((base root.id).val+1+i) (.val (base replacement.id))) := by
  have distinct : root.id≠child.id := by
    intro same
    cases (HRef.heq_of_id root child same).1
  have object : (hp.set root (MObj.setElem .dyn (hp.get root) i replacement)).get child=hp.get child :=
    Heap.get_set_ne hp root child distinct _
  have length : (hp.set root (MObj.setElem .dyn (hp.get root) i replacement)).len child .dyn=hp.len child .dyn := by
    simp only [Heap.len,object]
  constructor
  · rw [length]
    exact words.space
  · change Evm.upd m.mem _ _ (base child.id).val=_
    rw [Evm.upd_other _ _ (separate _ ⟨Nat.le_refl _,by omega⟩),length]
    exact words.length
  · intro k value hit
    rw [object] at hit
    have bound : k<hp.len child .dyn := (List.getElem?_eq_some_iff.mp hit).1
    change Evm.ReprV p value (Evm.upd m.mem _ _ ((base child.id).val+1+k))
    rw [Evm.upd_other _ _ (separate _ ⟨by omega,by omega⟩)]
    exact words.elements k value hit

/-- Both actual checked native writes, both word runs and their complete
append are linked through the reached heap. Both MSTORE steps retain their
separate pointer/numeric encodings; the selected reference is derived. -/
theorem ReferenceArrayAt.redirect_primitive {H : HTy} {p : PrimTy}
    {hp : Heap H} {root : HRef H (.array (.ref (.array (.prim p))))}
    {base : Nat → Fin Evm.W} {m : Evm.Machine} {bytes : Environment.Memory}
    (parent : ReferenceArrayAt hp root base m bytes) (child : HRef H (.array (.prim p)))
    (words : Evm.Memory.ArrayRepr hp child (base child.id) m)
    (physical : WordFrame m bytes (fun c => (base child.id).val≤c ∧ c<(base child.id).val+1+hp.len child .dyn))
    (i j w : Fin Evm.W) (v : p.Denote)
    (hi : i.val<hp.len root .dyn) (hj : j.val<hp.len child .dyn) (hv : Evm.ReprV p v (.val w))
    (childFits : 32*(base child.id).val<2^256)
    (numbersOutside : ∀ c,(base child.id).val≤c ∧ c<(base child.id).val+1+hp.len child .dyn →
      c≠(base root.id).val+1+i.val)
    (parentHeader : (base root.id).val≠(base child.id).val+1+j.val)
    (parentSlots : ∀ c,ReferenceSlots hp root base c → c≠(base child.id).val+1+j.val) :
    let middle := hp.set root (MObj.setElem .dyn (hp.get root) i.val child)
    let pointerCell := (base root.id).val+1+i.val
    let middleWord := Evm.Memory.writeMachine m pointerCell (.val (base child.id))
    let middleBytes := Environment.writeBytes bytes (32*pointerCell) (Semantics.wordBytes (32*(base child.id).val))
    let valueCell := (base child.id).val+1+j.val
    let finalWord := Evm.Memory.writeMachine middleWord valueCell (.val w)
    let finalBytes := Environment.writeBytes middleBytes (32*valueCell) (Semantics.wordBytes w.val)
    ∃ out : Heap H,
      hp.writeAddr (.index root .dyn (Evm.Memory.indexValue i)) child=some middle ∧
      middle.index root .dyn (Evm.Memory.indexValue i)=some child ∧
      Evm.run (Evm.Memory.writeArrayCode (base root.id)) ((m.push (.val (base child.id))).push (.val i))=.ok middleWord 0 ∧
      (∃ offset : Fin Evm.W,offset.val=32*pointerCell ∧ ∀ tail : List Environment.Word,
        Environment.cryptoStep (.op .MSTORE)
          ⟨lenU offset.val offset.isLt::lenU (32*(base child.id).val) childFits::tail,bytes⟩=some ⟨tail,middleBytes⟩) ∧
      Evm.Memory.ArrayRepr middle child (base child.id) middleWord ∧
      middle.writeAddr (.index child .dyn (Evm.Memory.indexValue j)) v=some out ∧
      Evm.run (Evm.Memory.writeArrayCode (base child.id)) ((middleWord.push (.val w)).push (.val j))=.ok finalWord 0 ∧
      Evm.run (Evm.Memory.writeArrayCode (base root.id) ++
        ([.push (.val w),.push (.val j)] ++ Evm.Memory.writeArrayCode (base child.id)))
        ((m.push (.val (base child.id))).push (.val i))=.ok finalWord 0 ∧
      Evm.run (Evm.Memory.writeArrayCode (base root.id) ++
        ([.push (.val w),.push (.val i)] ++ (Evm.Memory.readArrayCode (base root.id) ++
          ([.push (.val j)] ++ Evm.Memory.writeArrayStackCode))))
        ((m.push (.val (base child.id))).push (.val i))=.ok finalWord 0 ∧
      (∃ offset : Fin Evm.W,offset.val=32*valueCell ∧ ∀ tail : List Environment.Word,
        Environment.cryptoStep (.op .MSTORE)
          ⟨lenU offset.val offset.isLt::lenU w.val w.isLt::tail,middleBytes⟩=some ⟨tail,finalBytes⟩) ∧
      ReferenceArrayAt out root base finalWord finalBytes ∧
      Evm.Memory.ArrayRepr out child (base child.id) finalWord ∧
      WordFrame finalWord finalBytes (fun c => (base child.id).val≤c ∧ c<(base child.id).val+1+out.len child .dyn) ∧
      out.get root=middle.get root ∧ out.index root .dyn (Evm.Memory.indexValue i)=some child ∧
      Evm.run (Evm.Memory.readArrayCode (base root.id)) (finalWord.push (.val i))=
        .ok (finalWord.push (.val (base child.id))) 0 ∧
      Environment.readMemory finalBytes (32*pointerCell) 32=Semantics.wordBytes (32*(base child.id).val) ∧
      (∀ Q (q : HRef H Q),q.id≠root.id → q.id≠child.id → out.get q=hp.get q) ∧
      finalWord.mem 0=m.mem 0 ∧
      (∀ c,c≠pointerCell → c≠valueCell → finalWord.mem c=m.mem c) ∧ finalWord.stack=m.stack := by
  dsimp only
  let middle := hp.set root (MObj.setElem .dyn (hp.get root) i.val child)
  let cell := (base root.id).val+1+i.val
  let mw := Evm.Memory.writeMachine m cell (.val (base child.id))
  let mb := Environment.writeBytes bytes (32*cell) (Semantics.wordBytes (32*(base child.id).val))
  obtain ⟨actual,firstTyped,firstWord,firstByte,parentMid,firstFrame⟩ := parent.store i hi child childFits
  have canonical : hp.writeAddr (.index root .dyn (Evm.Memory.indexValue i)) child=some middle := by
    have bound : i.val<(MObj.elems .dyn (hp.get root)).length := hi
    simp only [Heap.writeAddr,Heap.setIndex,Evm.Memory.indexValue,Int.toNat_natCast,bound,↓reduceIte]
    rfl
  have same : actual=middle := Option.some.inj (firstTyped.symm.trans canonical)
  subst actual
  have distinct : root.id≠child.id := by
    intro eq
    cases (HRef.heq_of_id root child eq).1
  have childObject : middle.get child=hp.get child := firstFrame child distinct
  have childLength : middle.len child .dyn=hp.len child .dyn := by simp only [Heap.len,childObject]
  have parentLength : middle.len root .dyn=hp.len root .dyn := by
    simp only [middle,Heap.len,Heap.get_set_same,MObj.elems_setElem,List.length_set]
  have selected : middle.index root .dyn (Evm.Memory.indexValue i)=some child := by
    simp only [middle,Heap.index,Evm.Memory.indexValue,Int.toNat_natCast,
      Heap.get_set_same,MObj.elems_setElem,List.getElem?_set_self hi]
  have reachedWords : Evm.Memory.ArrayRepr middle child (base child.id) mw :=
    primitive_words_after_reference root child child base m i.val words numbersOutside
  have reachedBytes : WordFrame mw mb (fun c => (base child.id).val≤c ∧
      c<(base child.id).val+1+middle.len child .dyn) := by
    simpa only [childLength] using physical.pointer_write cell (base child.id) numbersOutside
  have jBound : j.val<middle.len child .dyn := by rw [childLength];exact hj
  have slots : ∀ c,ReferenceSlots middle root base c → c≠(base child.id).val+1+j.val := by
    intro c hc
    obtain ⟨k,bound,eq⟩ := hc
    rw [parentLength] at bound
    exact parentSlots c ⟨k,bound,eq⟩
  obtain ⟨out,secondTyped,secondWord,secondByte,finalWords,finalPhysical,finalParent,parentObject⟩ :=
    primitive_child_store parentMid child reachedWords reachedBytes j w v jBound hv parentHeader slots
  have whole : Evm.run (Evm.Memory.writeArrayCode (base root.id) ++
      ([.push (.val w),.push (.val j)] ++ Evm.Memory.writeArrayCode (base child.id)))
      ((m.push (.val (base child.id))).push (.val i))=
        .ok (Evm.Memory.writeMachine mw ((base child.id).val+1+j.val) (.val w)) 0 := by
    rw [Evm.run_append_ok firstWord]
    rw [Evm.run_append_ok (show Evm.run [.push (.val w),.push (.val j)] mw=
      .ok ((mw.push (.val w)).push (.val j)) 0 from rfl)]
    exact secondWord
  have dynamicWhole : Evm.run (Evm.Memory.writeArrayCode (base root.id) ++
      ([.push (.val w),.push (.val i)] ++ (Evm.Memory.readArrayCode (base root.id) ++
        ([.push (.val j)] ++ Evm.Memory.writeArrayStackCode))))
      ((m.push (.val (base child.id))).push (.val i))=
        .ok (Evm.Memory.writeMachine mw ((base child.id).val+1+j.val) (.val w)) 0 := by
    have pointer := (parentMid.word.stack (mw.push (.val w)).stack).read i
    simp only [Evm.Memory.RefOut,selected,TRes.ofOpt,Except.ok.injEq,reduceCtorEq,false_and,or_false] at pointer
    obtain ⟨actualChild,equal,readPointer⟩ := pointer
    cases equal
    have readReached : Evm.run (Evm.Memory.readArrayCode (base root.id))
        ((mw.push (.val w)).push (.val i))=.ok ((mw.push (.val w)).push (.val (base child.id))) 0 := by
      simpa only [mw,cell,Evm.Machine.push] using readPointer
    have stacked : Evm.run Evm.Memory.writeArrayStackCode
        ((((mw.push (.val w)).push (.val (base child.id))).push (.val j)))=
          .ok (Evm.Memory.writeMachine mw ((base child.id).val+1+j.val) (.val w)) 0 := by
      rw [Evm.Memory.writeArrayStackCode,Evm.Memory.arrayStack_append_eq (mw.push (.val w))
        (base child.id) j (middle.len child .dyn) (middle.len_dyn_lt child) reachedWords.length]
      exact secondWord
    rw [Evm.run_append_ok firstWord,
      Evm.run_append_ok (show Evm.run [.push (.val w),.push (.val i)] mw=
        .ok ((mw.push (.val w)).push (.val i)) 0 from rfl),
      Evm.run_append_ok readReached,
      Evm.run_append_ok (show Evm.run [.push (.val j)] ((mw.push (.val w)).push (.val (base child.id)))=
        .ok (((mw.push (.val w)).push (.val (base child.id))).push (.val j)) 0 from rfl)]
    exact stacked
  have selectedFinal : out.index root .dyn (Evm.Memory.indexValue i)=some child := by
    change (MObj.elems .dyn (out.get root))[i.val]?=some child
    rw [parentObject]
    exact selected
  have canonicalSecond : middle.writeAddr (.index child .dyn (Evm.Memory.indexValue j)) v=
      some (middle.set child (MObj.setElem .dyn (middle.get child) j.val v)) := by
    have bound : j.val<(MObj.elems .dyn (middle.get child)).length := jBound
    simp only [Heap.writeAddr,Heap.setIndex,Evm.Memory.indexValue,Int.toNat_natCast,bound,↓reduceIte]
  have outputIs : out=middle.set child (MObj.setElem .dyn (middle.get child) j.val v) :=
    Option.some.inj (secondTyped.symm.trans canonicalSecond)
  have hit : (MObj.elems .dyn (out.get root))[i.val]?=some child := selectedFinal
  have pointerRun := finalParent.word.read i
  simp only [Evm.Memory.RefOut,selectedFinal,TRes.ofOpt,Except.ok.injEq,reduceCtorEq,false_and,or_false] at pointerRun
  obtain ⟨actualChild,equal,readRun⟩ := pointerRun
  cases equal
  refine ⟨out,firstTyped,selected,firstWord,firstByte,reachedWords,secondTyped,secondWord,whole,dynamicWhole,secondByte,
    finalParent,finalWords,finalPhysical,parentObject,selectedFinal,readRun,
    (finalParent.child_bytes i.val child hit).2,?_,?_,?_,rfl⟩
  · intro Q q notRoot notChild
    rw [outputIs,Heap.get_set_ne middle child q (Ne.symm notChild)]
    exact firstFrame q (Ne.symm notRoot)
  · change Evm.upd (Evm.upd m.mem cell (.val (base child.id)))
      ((base child.id).val+1+j.val) (.val w) 0=m.mem 0
    rw [Evm.upd_other _ _ (by omega),Evm.upd_other _ _ (by dsimp only [cell];omega)]
  · intro c notPointer notValue
    change Evm.upd (Evm.upd m.mem cell (.val (base child.id)))
      ((base child.id).val+1+j.val) (.val w) c=m.mem c
    rw [Evm.upd_other _ _ notValue,Evm.upd_other _ _ notPointer]

/-- info: 'Solidity.Backend.MemoryOps.Physical.primitive_words_after_reference' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms primitive_words_after_reference
/-- info: 'Solidity.Backend.MemoryOps.Physical.ReferenceArrayAt.redirect_primitive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReferenceArrayAt.redirect_primitive
end Solidity.Backend.MemoryOps.Physical
