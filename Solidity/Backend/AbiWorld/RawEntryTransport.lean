import Solidity.Backend.AbiWorld.ReferenceFields

/-! Shared actual raw Entries witnesses from canonical windows. No decoder
success or desired entry identity is assumed; real melem/eager/cref executions
are derived for both inputs, and the old typed-only theorem stays unchanged. -/
namespace Solidity.Backend.AbiWorld.RawEntryTransport
open AbiEntry RecursiveLayout RecursiveEntry

theorem joint_window (ps : List Param) (vs : Vals (ps.map Param.shape)) (I J : Input)
    (hp hs tp ts hp' hs' tp' ts' : List UInt8) (pos off a f : Nat)
    (ha : I.data = hp ++ (AbiEntry.assemble.go (Vals.parts vs) off).1 ++ hs)
    (ta : I.data = tp ++ (AbiEntry.assemble.go (Vals.parts vs) off).2 ++ ts)
    (hb : J.data = hp' ++ (AbiEntry.assemble.go (Vals.parts vs) off).1 ++ hs')
    (tb : J.data = tp' ++ (AbiEntry.assemble.go (Vals.parts vs) off).2 ++ ts')
    (pa : hp.length = 4 + pos) (qa : tp.length = 4 + off)
    (pb : hp'.length = 4 + pos) (qb : tp'.length = 4 + off)
    (hpad : 32 ≤ hs.length) (tpad : 32 ≤ ts.length)
    (hpad' : 32 ≤ hs'.length) (tpad' : 32 ≤ ts'.length)
    (sizeI : I.size ≤ lim) (sizeJ : J.size ≤ lim)
    (roomI : I.free + (a + LocationPeak.peak ps vs) ≤ lim)
    (roomJ : J.free + (a + LocationPeak.peak ps vs) ≤ lim)
    (fuel : parameterNeed vs ≤ f) :
    ∃ es : Entries ps, enter I f ps pos a = .ok (es,a + spent ps vs) ∧
      enter J f ps pos a = .ok (es,a + spent ps vs) ∧
      bodyValues I f ps es pos = .ok vs ∧ bodyValues J f ps es pos = .ok vs := by
  induction ps generalizing hp tp hp' tp' pos off a with
  | nil => cases vs; exact ⟨.nil,rfl,rfl,rfl,rfl⟩
  | cons p ps ih =>
    cases vs with
    | cons v vs =>
      simp only [LocationPeak.peak,parameterNeed] at roomI roomJ fuel
      let off' := if p.shape.dynamic then off + (Val.enc v).length else off
      let b := if p.shape.dynamic then AbiEntry.wordBytes off else Val.enc v
      let t := if p.shape.dynamic then Val.enc v else []
      let c := if p.loc == .calldata then 0 else allocation v
      have hc := Nat.le_max_left (allocation v) (c + LocationPeak.peak ps vs)
      have tc := Nat.le_max_right (allocation v) (c + LocationPeak.peak ps vs)
      have nf : need v + 1 ≤ f := by have h := Nat.le_max_left (need v + 1) (parameterNeed vs); omega
      have fp : 0 < f := by omega
      obtain ⟨g,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt fp)
      have dmI := RecursiveReadback.element (g + 1) v I hp ((AbiEntry.assemble.go (Vals.parts vs) off').1 ++ hs) tp
        ((AbiEntry.assemble.go (Vals.parts vs) off').2 ++ ts) 4 (4 + pos) off a
        (by simpa only [Vals.parts,go_head_cons,List.append_assoc,b,off'] using ha)
        (by intro hd; simpa only [Vals.parts,go_tail_cons,hd,ite_true,List.append_assoc,off'] using ta)
        pa (by intro _; exact qa)
        (by simp only [List.length_append]; omega) (by simp only [List.length_append]; omega)
        sizeI (by dsimp only [c] at hc tc; omega) nf
      have dmI0 := RecursiveReadback.element (g + 1) v I hp ((AbiEntry.assemble.go (Vals.parts vs) off').1 ++ hs) tp
        ((AbiEntry.assemble.go (Vals.parts vs) off').2 ++ ts) 4 (4 + pos) off 0
        (by simpa only [Vals.parts,go_head_cons,List.append_assoc,b,off'] using ha)
        (by intro hd; simpa only [Vals.parts,go_tail_cons,hd,ite_true,List.append_assoc,off'] using ta)
        pa (by intro _; exact qa)
        (by simp only [List.length_append]; omega) (by simp only [List.length_append]; omega)
        sizeI (by dsimp only [c] at hc tc; omega) nf
      have ewI : eager I (g + 1) p.shape pos = .ok v := by simp only [eager,dmI0,Nat.zero_add]
      obtain ⟨addrI,lenI,crI,_⟩ := eager_cref sizeI ewI
      have dmJ := RecursiveReadback.element (g + 1) v J hp' ((AbiEntry.assemble.go (Vals.parts vs) off').1 ++ hs') tp'
        ((AbiEntry.assemble.go (Vals.parts vs) off').2 ++ ts') 4 (4 + pos) off a
        (by simpa only [Vals.parts,go_head_cons,List.append_assoc,b,off'] using hb)
        (by intro hd; simpa only [Vals.parts,go_tail_cons,hd,ite_true,List.append_assoc,off'] using tb)
        pb (by intro _; exact qb)
        (by simp only [List.length_append]; omega) (by simp only [List.length_append]; omega)
        sizeJ (by dsimp only [c] at hc tc; omega) nf
      have dmJ0 := RecursiveReadback.element (g + 1) v J hp' ((AbiEntry.assemble.go (Vals.parts vs) off').1 ++ hs') tp'
        ((AbiEntry.assemble.go (Vals.parts vs) off').2 ++ ts') 4 (4 + pos) off 0
        (by simpa only [Vals.parts,go_head_cons,List.append_assoc,b,off'] using hb)
        (by intro hd; simpa only [Vals.parts,go_tail_cons,hd,ite_true,List.append_assoc,off'] using tb)
        pb (by intro _; exact qb)
        (by simp only [List.length_append]; omega) (by simp only [List.length_append]; omega)
        sizeJ (by dsimp only [c] at hc tc; omega) nf
      have ewJ : eager J (g + 1) p.shape pos = .ok v := by simp only [eager,dmJ0,Nat.zero_add]
      obtain ⟨addrJ,lenJ,crJ,_⟩ := eager_cref sizeJ ewJ
      have same := ReferenceFields.agree v I J hp ((AbiEntry.assemble.go (Vals.parts vs) off').1 ++ hs)
        tp ((AbiEntry.assemble.go (Vals.parts vs) off').2 ++ ts)
        hp' ((AbiEntry.assemble.go (Vals.parts vs) off').1 ++ hs')
        tp' ((AbiEntry.assemble.go (Vals.parts vs) off').2 ++ ts') pos off addrI lenI addrJ lenJ
        (by simpa only [Vals.parts,go_head_cons,List.append_assoc,b,off'] using ha)
        (by simpa only [Vals.parts,go_head_cons,List.append_assoc,b,off'] using hb)
        (by intro hd; simpa only [Vals.parts,go_tail_cons,hd,ite_true,List.append_assoc,off'] using ta)
        (by intro hd; simpa only [Vals.parts,go_tail_cons,hd,ite_true,List.append_assoc,off'] using tb)
        pa pb (by intro _; exact qa) (by intro _; exact qb) sizeI crI crJ
      have addrEq : addrI = addrJ := congrArg Prod.fst same
      have lenEq : lenI = lenJ := congrArg Prod.snd same
      rw [← addrEq,← lenEq] at crJ
      have single : ∃ es : Entries [p], enter I (g+1) [p] pos a = .ok (es,a+c) ∧
          enter J (g+1) [p] pos a = .ok (es,a+c) ∧
          bodyValues I (g+1) [p] es pos = .ok (.cons v .nil) ∧
          bodyValues J (g+1) [p] es pos = .ok (.cons v .nil) := by
        cases hl : p.loc
        case value | memory =>
          refine ⟨.cons (.val v) .nil,?_,?_,?_,?_⟩ <;>
            simp only [enter,hl,dmI,dmJ,bodyValues,c,bind,Except.bind,pure,Except.pure,BEq.beq,reduceCtorEq,decide_false,Bool.false_eq_true,ite_false]
        case calldata =>
          refine ⟨.cons (.ref addrI lenI) .nil,?_,?_,?_,?_⟩ <;>
            simp only [enter,hl,crI,crJ,bodyValues,ewI,ewJ,c,bind,Except.bind,pure,Except.pure,BEq.beq,decide_true,ite_true,Nat.add_zero]
      obtain ⟨es,enI,enJ,bodyI,bodyJ⟩ := single
      obtain ⟨fs,tailI,tailJ,tailBodyI,tailBodyJ⟩ := ih vs (hp ++ b) (tp ++ t) (hp' ++ b) (tp' ++ t)
        (pos + p.shape.headSize) off' (a+c)
        (by simpa only [Vals.parts,go_head_cons,List.append_assoc,b,off'] using ha)
        (by simpa only [Vals.parts,go_tail_cons,List.append_assoc,t,off'] using ta)
        (by simpa only [Vals.parts,go_head_cons,List.append_assoc,b,off'] using hb)
        (by simpa only [Vals.parts,go_tail_cons,List.append_assoc,t,off'] using tb)
        (by simp only [List.length_append,b,piece_length,pa,Nat.add_assoc])
        (by cases hd : p.shape.dynamic <;> simp only [List.length_append,t,off',hd,Bool.false_eq_true,ite_false,ite_true,List.length_nil,qa,Nat.add_zero] <;> omega)
        (by simp only [List.length_append,b,piece_length,pb,Nat.add_assoc])
        (by cases hd : p.shape.dynamic <;> simp only [List.length_append,t,off',hd,Bool.false_eq_true,ite_false,ite_true,List.length_nil,qb,Nat.add_zero] <;> omega)
        (by dsimp only [c] at hc tc; omega) (by dsimp only [c] at hc tc; omega)
        (by have h := Nat.le_max_right (need v + 1) (parameterNeed vs); omega)
      refine ⟨EntryComposition.appendEntries es fs,?_,?_,?_,?_⟩
      · change enter I (g+1) ([p] ++ ps) pos a = _
        rw [EntryComposition.enter_append,enI]
        simp only [headsOf,List.map_cons,List.map_nil,Shape.headsSize,Nat.add_zero,spent,c,tailI,bind,Except.bind,pure,Except.pure,Nat.add_assoc]
      · change enter J (g+1) ([p] ++ ps) pos a = _
        rw [EntryComposition.enter_append,enJ]
        simp only [headsOf,List.map_cons,List.map_nil,Shape.headsSize,Nat.add_zero,spent,c,tailJ,bind,Except.bind,pure,Except.pure,Nat.add_assoc]
      · have h := BodyComposition.body_success I (g+1) es fs (.cons v .nil) vs pos bodyI
          (by simpa only [headsOf,List.map_cons,List.map_nil,Shape.headsSize,Nat.add_zero] using tailBodyI)
        simpa only [BodyComposition.appendValues_cons,BodyComposition.appendValues_nil] using h
      · have h := BodyComposition.body_success J (g+1) es fs (.cons v .nil) vs pos bodyJ
          (by simpa only [headsOf,List.map_cons,List.map_nil,Shape.headsSize,Nat.add_zero] using tailBodyJ)
        simpa only [BodyComposition.appendValues_cons,BodyComposition.appendValues_nil] using h

/-- Later values may change all later head bytes/tail lengths; equal shapes
retain the actual head extent. The shared raw prefix includes ref addresses. -/
theorem sibling_window (ps qs : List Param) (vs : Vals (ps.map Param.shape))
    (ws zs : Vals (qs.map Param.shape)) (I J : Input) (hp lead post : List UInt8) (pos off a f : Nat)
    (headPos : hp.length = 4 + pos) (offset : off = pos + headsOf ps + headsOf qs + lead.length)
    (dataI : I.data = hp ++ (AbiEntry.assemble.go (Vals.parts vs ++ Vals.parts ws) off).1 ++ lead ++
      (AbiEntry.assemble.go (Vals.parts vs ++ Vals.parts ws) off).2 ++ post)
    (dataJ : J.data = hp ++ (AbiEntry.assemble.go (Vals.parts vs ++ Vals.parts zs) off).1 ++ lead ++
      (AbiEntry.assemble.go (Vals.parts vs ++ Vals.parts zs) off).2 ++ post)
    (padding : 32 ≤ post.length) (sizeI : I.size ≤ lim) (sizeJ : J.size ≤ lim)
    (roomI : I.free + (a + LocationPeak.peak ps vs) ≤ lim)
    (roomJ : J.free + (a + LocationPeak.peak ps vs) ≤ lim) (fuel : parameterNeed vs ≤ f) :
    ∃ es : Entries ps, enter I f ps pos a = .ok (es,a + spent ps vs) ∧
      enter J f ps pos a = .ok (es,a + spent ps vs) ∧
      bodyValues I f ps es pos = .ok vs ∧ bodyValues J f ps es pos = .ok vs := by
  let next := off + (AbiEntry.assemble.go (Vals.parts vs) off).2.length
  let wh := (AbiEntry.assemble.go (Vals.parts ws) next).1
  let wt := (AbiEntry.assemble.go (Vals.parts ws) next).2
  let zh := (AbiEntry.assemble.go (Vals.parts zs) next).1
  let zt := (AbiEntry.assemble.go (Vals.parts zs) next).2
  apply joint_window ps vs I J hp (wh ++ lead ++ (AbiEntry.assemble.go (Vals.parts vs) off).2 ++ wt ++ post)
    (hp ++ (AbiEntry.assemble.go (Vals.parts vs) off).1 ++ wh ++ lead) (wt ++ post)
    hp (zh ++ lead ++ (AbiEntry.assemble.go (Vals.parts vs) off).2 ++ zt ++ post)
    (hp ++ (AbiEntry.assemble.go (Vals.parts vs) off).1 ++ zh ++ lead) (zt ++ post) pos off a f
  · simpa only [DynamicListReadback.go_append,List.append_assoc,next,wh,wt] using dataI
  · simpa only [DynamicListReadback.go_append,List.append_assoc,next,wh,wt] using dataI
  · simpa only [DynamicListReadback.go_append,List.append_assoc,next,zh,zt] using dataJ
  · simpa only [DynamicListReadback.go_append,List.append_assoc,next,zh,zt] using dataJ
  · exact headPos
  · simp only [List.length_append,wh,go_head_length,member_heads,headPos]
    simp only [headsOf] at offset
    omega
  · exact headPos
  · simp only [List.length_append,zh,go_head_length,member_heads,headPos]
    simp only [headsOf] at offset
    omega
  all_goals first | exact sizeI | exact sizeJ | exact roomI | exact roomJ | exact fuel | (simp only [List.length_append]; omega)

theorem canonical_data (ps qs : List Param) (vs : Vals (ps.map Param.shape))
    (ws : Vals (qs.map Param.shape)) (selector post : List UInt8) (free : Nat) :
    (input (ps ++ qs) (BodyComposition.appendValues ps qs vs ws) selector post free).data =
      selector ++ (AbiEntry.assemble.go (Vals.parts vs ++ Vals.parts ws) (headsOf ps + headsOf qs)).1 ++
      (AbiEntry.assemble.go (Vals.parts vs ++ Vals.parts ws) (headsOf ps + headsOf qs)).2 ++ post := by
  simp only [input,encodeArgs,assembled,SiblingReadback.parts_append]
  have heads : RecursiveLayout.heads (Vals.parts vs ++ Vals.parts ws) = headsOf ps + headsOf qs := by
    rw [← SiblingReadback.parts_append,member_heads,← headsOf,EntryComposition.heads_append]
  rw [heads]
  simp only [List.append_assoc]

/-- Actual common raw Entries, not a typed projection or desired-output
hypothesis. No successful decoding/admission of later siblings is required. -/
theorem noninterference (ps qs : List Param) (vs : Vals (ps.map Param.shape))
    (ws zs : Vals (qs.map Param.shape)) (selector post : List UInt8) (free a f : Nat)
    (sel : selector.length = 4) (padding : 32 ≤ post.length)
    (sizeI : (input (ps ++ qs) (BodyComposition.appendValues ps qs vs ws) selector post free).size ≤ lim)
    (sizeJ : (input (ps ++ qs) (BodyComposition.appendValues ps qs vs zs) selector post free).size ≤ lim)
    (room : free + (a + LocationPeak.peak ps vs) ≤ lim) (fuel : parameterNeed vs ≤ f) :
    let I := input (ps ++ qs) (BodyComposition.appendValues ps qs vs ws) selector post free
    let J := input (ps ++ qs) (BodyComposition.appendValues ps qs vs zs) selector post free
    ∃ es : Entries ps, enter I f ps 0 a = .ok (es,a + spent ps vs) ∧
      enter J f ps 0 a = .ok (es,a + spent ps vs) ∧ bodyValues I f ps es 0 = .ok vs ∧ bodyValues J f ps es 0 = .ok vs := by
  apply sibling_window ps qs vs ws zs _ _ selector [] post 0 (headsOf ps + headsOf qs) a f
  · omega
  · simp only [List.length_nil,Nat.add_zero,Nat.zero_add]
  · simpa only [List.append_nil] using canonical_data ps qs vs ws selector post free
  · simpa only [List.append_nil] using canonical_data ps qs vs zs selector post free
  · exact padding
  · exact sizeI
  · exact sizeJ
  · exact room
  · exact room
  · exact fuel

theorem enter_equal (ps qs : List Param) (vs : Vals (ps.map Param.shape))
    (ws zs : Vals (qs.map Param.shape)) (selector post : List UInt8) (free a f : Nat)
    (sel : selector.length = 4) (padding : 32 ≤ post.length)
    (sizeI : (input (ps ++ qs) (BodyComposition.appendValues ps qs vs ws) selector post free).size ≤ lim)
    (sizeJ : (input (ps ++ qs) (BodyComposition.appendValues ps qs vs zs) selector post free).size ≤ lim)
    (room : free + (a + LocationPeak.peak ps vs) ≤ lim) (fuel : parameterNeed vs ≤ f) :
    enter (input (ps ++ qs) (BodyComposition.appendValues ps qs vs ws) selector post free) f ps 0 a =
      enter (input (ps ++ qs) (BodyComposition.appendValues ps qs vs zs) selector post free) f ps 0 a := by
  obtain ⟨es,hi,hj,_,_⟩ := noninterference ps qs vs ws zs selector post free a f sel padding sizeI sizeJ room fuel
  exact hi.trans hj.symm

theorem entry_from_run (I : Input) (ps : List Param) (f c : Nat) (es : Entries ps)
    (existsEntry : ∃ xs, entry I f ps = .ok xs) (run : enter I f ps 0 0 = .ok (es,c)) :
    entry I f ps = .ok es := by
  obtain ⟨xs,hx⟩ := existsEntry
  have guard : ¬ I.size < 4 + headsOf ps := by
    intro bad
    rw [entry,if_pos bad] at hx
    cases hx
  simp only [entry,if_neg guard,run]

/-- The actual raw entry result, including every stored reference field,
is equal; its head checks are discharged from actual canonical inputs. -/
theorem entry_equal (ps qs : List Param) (vs : Vals (ps.map Param.shape))
    (ws zs : Vals (qs.map Param.shape)) (selector post : List UInt8) (free f : Nat)
    (sel : selector.length = 4) (padding : 32 ≤ post.length)
    (sizeI : (input (ps ++ qs) (BodyComposition.appendValues ps qs vs ws) selector post free).size ≤ lim)
    (sizeJ : (input (ps ++ qs) (BodyComposition.appendValues ps qs vs zs) selector post free).size ≤ lim)
    (room : free + LocationPeak.peak ps vs ≤ lim) (fuel : parameterNeed vs ≤ f) :
    entry (input (ps ++ qs) (BodyComposition.appendValues ps qs vs ws) selector post free) f ps =
      entry (input (ps ++ qs) (BodyComposition.appendValues ps qs vs zs) selector post free) f ps := by
  obtain ⟨es,hi,hj,_,_⟩ := noninterference ps qs vs ws zs selector post free 0 f sel padding sizeI sizeJ
    (by simpa only [Nat.zero_add] using room) fuel
  obtain ⟨ei,eiRun,_⟩ := SiblingReadback.prefix_entry ps qs vs ws selector post free f sel padding sizeI room fuel
  obtain ⟨ej,ejRun,_⟩ := SiblingReadback.prefix_entry ps qs vs zs selector post free f sel padding sizeJ room fuel
  rw [entry_from_run _ ps f _ es ⟨ei,eiRun⟩ hi,entry_from_run _ ps f _ es ⟨ej,ejRun⟩ hj]

end Solidity.Backend.AbiWorld.RawEntryTransport
