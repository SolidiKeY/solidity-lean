import Solidity.Backend.AbiWorld.RecursiveEntry

/-! Location-sensitive sufficient canonical allocation bound. This is derived
from actual enter/body equations, not a new admission rule or minimality claim.
Original full-copy theorem and all decoder semantics remain unchanged. -/
namespace Solidity.Backend.AbiWorld.LocationPeak
open AbiEntry RecursiveLayout RecursiveEntry

def peak : (ps : List Param) → Vals (ps.map Param.shape) → Nat
  | [], .nil => 0
  | p :: ps, .cons v vs => max (allocation v)
      ((if p.loc == .calldata then 0 else allocation v) + peak ps vs)

theorem peak_le_sum (ps : List Param) (vs : Vals (ps.map Param.shape)) :
    peak ps vs ≤ memberAllocation vs := by
  induction ps with
  | nil => cases vs; exact Nat.le_refl 0
  | cons p ps ih =>
    cases vs with
    | cons v vs =>
      have h := ih vs
      simp only [peak,memberAllocation]
      cases hl : p.loc <;> simp only [BEq.beq,reduceCtorEq,decide_true,decide_false,ite_true,ite_false] <;> omega

theorem spent_le_peak (ps : List Param) (vs : Vals (ps.map Param.shape)) :
    spent ps vs ≤ peak ps vs := by
  induction ps with
  | nil => cases vs; exact Nat.le_refl 0
  | cons p ps ih =>
    cases vs with
    | cons v vs =>
      have h := ih vs
      simp only [peak,spent]
      omega

/-- Original full-copy hypothesis implies the new sufficient bound. -/
theorem room_of_sum (ps : List Param) (vs : Vals (ps.map Param.shape))
    (free a : Nat) (h : free + (a + memberAllocation vs) ≤ lim) :
    free + (a + peak ps vs) ≤ lim := by
  have hpeak := peak_le_sum ps vs
  omega

/-- Calldata contributes no retained cursor; the head eager copy is still
budgeted. Its actual body readback starts at zero, as proved in window. This
recurrence is sufficient, not asserted minimal for interleaved locations. -/
theorem calldata_cons (p : Param) (ps : List Param) (v : AbiEntry.Val p.shape)
    (vs : Vals (ps.map Param.shape)) (h : p.loc = .calldata) :
    peak (p :: ps) (.cons v vs) = max (allocation v) (peak ps vs) := by
  simp only [peak,h,BEq.beq,decide_true,ite_true,Nat.zero_add]

theorem window (ps : List Param) (vs : Vals (ps.map Param.shape)) (I : Input)
    (hp hs tp ts : List UInt8) (pos off a f : Nat)
    (headData : I.data = hp ++ (AbiEntry.assemble.go (Vals.parts vs) off).1 ++ hs)
    (tailData : I.data = tp ++ (AbiEntry.assemble.go (Vals.parts vs) off).2 ++ ts)
    (headPos : hp.length = 4 + pos) (tailPos : tp.length = 4 + off)
    (headPad : 32 ≤ hs.length) (tailPad : 32 ≤ ts.length) (size : I.size ≤ lim)
    (room : I.free + (a + peak ps vs) ≤ lim) (fuel : parameterNeed vs ≤ f) :
    ∃ es : Entries ps, enter I f ps pos a = .ok (es,a + spent ps vs) ∧
      bodyValues I f ps es pos = .ok vs := by
  induction ps generalizing hp tp pos off a with
  | nil => cases vs; exact ⟨.nil,rfl,rfl⟩
  | cons p ps ih =>
    cases vs with
    | cons v vs =>
      simp only [peak,parameterNeed] at room fuel
      let off' := if p.shape.dynamic then off + (Val.enc v).length else off
      let b := if p.shape.dynamic then AbiEntry.wordBytes off else Val.enc v
      let t := if p.shape.dynamic then Val.enc v else []
      let c := if p.loc == .calldata then 0 else allocation v
      have headCost := Nat.le_max_left (allocation v) ((if p.loc == .calldata then 0 else allocation v) + peak ps vs)
      have tailCost := Nat.le_max_right (allocation v) ((if p.loc == .calldata then 0 else allocation v) + peak ps vs)
      have nf : need v + 1 ≤ f := by have h := Nat.le_max_left (need v + 1) (parameterNeed vs); omega
      have fp : 0 < f := by omega
      obtain ⟨g,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt fp)
      have dm := RecursiveReadback.element (g + 1) v I hp ((AbiEntry.assemble.go (Vals.parts vs) off').1 ++ hs) tp
        ((AbiEntry.assemble.go (Vals.parts vs) off').2 ++ ts) 4 (4 + pos) off a
        (by simpa only [Vals.parts,go_head_cons,List.append_assoc,b,off'] using headData)
        (by intro hd; simpa only [Vals.parts,go_tail_cons,hd,ite_true,List.append_assoc,off'] using tailData)
        headPos (by intro _; exact tailPos)
        (by simp only [List.length_append]; omega) (by simp only [List.length_append]; omega)
        size (by omega) nf
      have dm0 := RecursiveReadback.element (g + 1) v I hp ((AbiEntry.assemble.go (Vals.parts vs) off').1 ++ hs) tp
        ((AbiEntry.assemble.go (Vals.parts vs) off').2 ++ ts) 4 (4 + pos) off 0
        (by simpa only [Vals.parts,go_head_cons,List.append_assoc,b,off'] using headData)
        (by intro hd; simpa only [Vals.parts,go_tail_cons,hd,ite_true,List.append_assoc,off'] using tailData)
        headPos (by intro _; exact tailPos)
        (by simp only [List.length_append]; omega) (by simp only [List.length_append]; omega)
        size (by omega) nf
      have ew : eager I (g + 1) p.shape pos = .ok v := by simp only [eager,dm0,Nat.zero_add]
      obtain ⟨addr,len,cr,lv⟩ := eager_cref size ew
      obtain ⟨es,en,body⟩ := DynamicListReadback.one_success p v I pos a (g + 1) (allocation v) addr len dm ew cr
      have cl : c ≤ allocation v := by dsimp only [c]; split <;> omega
      obtain ⟨fs,tailEnter,tailBody⟩ := ih vs (hp ++ b) (tp ++ t) (pos + p.shape.headSize) off' (a + c)
        (by simpa only [Vals.parts,go_head_cons,List.append_assoc,b,off'] using headData)
        (by simpa only [Vals.parts,go_tail_cons,List.append_assoc,t,off'] using tailData)
        (by simp only [List.length_append,b,piece_length,headPos,Nat.add_assoc])
        (by cases hd : p.shape.dynamic <;> simp only [List.length_append,t,off',hd,Bool.false_eq_true,ite_false,ite_true,List.length_nil,tailPos,Nat.add_zero] <;> omega)
        (by omega) (by have h := Nat.le_max_right (need v + 1) (parameterNeed vs); omega)
      refine ⟨EntryComposition.appendEntries es fs,?_,?_⟩
      · change enter I (g + 1) ([p] ++ ps) pos a = _
        rw [EntryComposition.enter_append,en]
        simp only [headsOf,List.map_cons,List.map_nil,Shape.headsSize,Nat.add_zero,spent,c,
          tailEnter,bind,Except.bind,pure,Except.pure,Nat.add_assoc]
      · have h := BodyComposition.body_success I (g + 1) es fs (.cons v .nil) vs pos body
          (by simpa only [headsOf,List.map_cons,List.map_nil,Shape.headsSize,Nat.add_zero] using tailBody)
        simpa only [BodyComposition.appendValues_cons,BodyComposition.appendValues_nil] using h

theorem roundtrip (ps : List Param) (vs : Vals (ps.map Param.shape)) (selector post : List UInt8) (free f : Nat)
    (sel : selector.length = 4) (padding : 32 ≤ post.length)
    (size : (input ps vs selector post free).size ≤ lim)
    (room : free + peak ps vs ≤ lim) (fuel : parameterNeed vs ≤ f) :
    ∃ es : Entries ps,
      enter (input ps vs selector post free) f ps 0 0 = .ok (es,spent ps vs) ∧
      entry (input ps vs selector post free) f ps = .ok es ∧
      bodyValues (input ps vs selector post free) f ps es 0 = .ok vs ∧
      verdict (input ps vs selector post free) f ps = .run vs ∧ 4 + headsOf ps ≤ lim := by
  let off := heads (Vals.parts vs)
  let h := (AbiEntry.assemble.go (Vals.parts vs) off).1
  let t := (AbiEntry.assemble.go (Vals.parts vs) off).2
  have enc : encodeArgs vs = h ++ t := assembled _
  obtain ⟨es,en,body⟩ := window ps vs (input ps vs selector post free) selector (t ++ post) (selector ++ h) post
    0 off 0 f
    (by simp only [input,enc,List.append_assoc,h])
    (by simp only [input,enc,List.append_assoc,t]) (by omega)
    (by simp only [List.length_append,h,go_head_length,off,sel])
    (by simp only [List.length_append]; omega) padding size
    (by simpa only [input,Nat.zero_add] using room) fuel
  have fit : 4 + headsOf ps ≤ (input ps vs selector post free).size := by
    have hb := assemble_head_bound (Vals.parts vs)
    rw [member_heads] at hb
    simp only [input,Input.size,List.length_append,sel,headsOf,encodeArgs]
    omega
  have ep : entry (input ps vs selector post free) f ps = .ok es := by rw [entry,if_neg (Nat.not_lt.mpr fit),en]
  refine ⟨es,by simpa only [Nat.zero_add] using en,ep,body,?_,Nat.le_trans fit size⟩
  rw [verdict,ep]
  simp only [body]

end Solidity.Backend.AbiWorld.LocationPeak
