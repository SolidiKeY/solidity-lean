import Solidity.Backend.AbiWorld.LocationPeak

/-! Actual indexed canonical prefix readback under replacement of later
sibling values. Builder identities alone do not supply the entry/body result.
Bounds are sufficient; no Source admission or runtime/world claim. -/
namespace Solidity.Backend.AbiWorld.SiblingReadback
open AbiEntry RecursiveLayout RecursiveEntry

theorem parts_append (ps qs : List Param) (vs : Vals (ps.map Param.shape))
    (ws : Vals (qs.map Param.shape)) :
    Vals.parts (BodyComposition.appendValues ps qs vs ws) = Vals.parts vs ++ Vals.parts ws := by
  induction ps with
  | nil => cases vs; rfl
  | cons p ps ih =>
    cases vs with
    | cons v vs => simp only [BodyComposition.appendValues_cons,Vals.parts,List.cons_append,ih]

theorem encoded_split (ps qs : List Param) (vs : Vals (ps.map Param.shape))
    (ws : Vals (qs.map Param.shape)) :
    let off := headsOf ps + headsOf qs
    encodeArgs (BodyComposition.appendValues ps qs vs ws) =
      (AbiEntry.assemble.go (Vals.parts vs) off).1 ++
      (AbiEntry.assemble.go (Vals.parts ws) (off + (AbiEntry.assemble.go (Vals.parts vs) off).2.length)).1 ++
      (AbiEntry.assemble.go (Vals.parts vs) off).2 ++
      (AbiEntry.assemble.go (Vals.parts ws) (off + (AbiEntry.assemble.go (Vals.parts vs) off).2.length)).2 := by
  dsimp only
  rw [encodeArgs,assembled,parts_append]
  have heads : RecursiveLayout.heads (Vals.parts vs ++ Vals.parts ws) = headsOf ps + headsOf qs := by
    rw [← parts_append,member_heads,← headsOf,EntryComposition.heads_append]
  rw [heads,DynamicListReadback.go_append]
  simp only [List.append_assoc]

/-- Complete actual input extent, derived before specializing recursive
values so clients need not normalize a large concrete byte list. -/
theorem canonical_size (ps qs : List Param) (vs : Vals (ps.map Param.shape))
    (ws : Vals (qs.map Param.shape)) (selector post : List UInt8) (free : Nat) :
    let off := headsOf ps + headsOf qs
    (input (ps ++ qs) (BodyComposition.appendValues ps qs vs ws) selector post free).size =
      selector.length + headsOf ps + headsOf qs +
      (AbiEntry.assemble.go (Vals.parts vs) off).2.length +
      (AbiEntry.assemble.go (Vals.parts ws) (off + (AbiEntry.assemble.go (Vals.parts vs) off).2.length)).2.length + post.length := by
  simp only [input,Input.size,List.length_append,encoded_split,go_head_length,member_heads,headsOf,Nat.add_assoc]

/-- Exact actual byte windows, not merely encoded total lengths. The later
head extent is derived from its indexed shapes; later payload lengths may vary. -/
theorem prefix_bytes (ps qs : List Param) (vs : Vals (ps.map Param.shape))
    (ws : Vals (qs.map Param.shape)) :
    let off := headsOf ps + headsOf qs
    let bs := encodeArgs (BodyComposition.appendValues ps qs vs ws)
    bs.take (headsOf ps) = (AbiEntry.assemble.go (Vals.parts vs) off).1 ∧
    (bs.drop off).take (AbiEntry.assemble.go (Vals.parts vs) off).2.length =
      (AbiEntry.assemble.go (Vals.parts vs) off).2 := by
  dsimp only
  let off := headsOf ps + headsOf qs
  let hp := (AbiEntry.assemble.go (Vals.parts vs) off).1
  let tp := (AbiEntry.assemble.go (Vals.parts vs) off).2
  let hs := (AbiEntry.assemble.go (Vals.parts ws) (off + tp.length)).1
  let ts := (AbiEntry.assemble.go (Vals.parts ws) (off + tp.length)).2
  have hpL : hp.length = headsOf ps := by simp only [hp,go_head_length,member_heads,headsOf]
  have hsL : hs.length = headsOf qs := by simp only [hs,go_head_length,member_heads,headsOf]
  have hL : (hp ++ hs).length = off := by simp only [List.length_append,hpL,hsL,off]
  have enc : encodeArgs (BodyComposition.appendValues ps qs vs ws) = (hp ++ hs) ++ (tp ++ ts) := by
    simpa only [hp,tp,hs,ts,off,List.append_assoc] using encoded_split ps qs vs ws
  rw [enc]
  constructor
  · simpa only [hpL,List.append_assoc,List.take_left] using
      (List.take_left (l₁ := hp) (l₂ := hs ++ (tp ++ ts)))
  · have cut := List.drop_left' hL (l₂ := tp ++ ts)
    rw [cut,List.take_left]

/-- Extent of the actual nonzero-position/leading-tail window. -/
theorem window_size (ps qs : List Param) (vs : Vals (ps.map Param.shape))
    (ws : Vals (qs.map Param.shape)) (I : Input) (hp lead post : List UInt8) (off : Nat)
    (data : I.data = hp ++ (AbiEntry.assemble.go (Vals.parts vs ++ Vals.parts ws) off).1 ++ lead ++
      (AbiEntry.assemble.go (Vals.parts vs ++ Vals.parts ws) off).2 ++ post) :
    I.size = hp.length + headsOf ps + headsOf qs + lead.length +
      (AbiEntry.assemble.go (Vals.parts vs) off).2.length +
      (AbiEntry.assemble.go (Vals.parts ws) (off + (AbiEntry.assemble.go (Vals.parts vs) off).2.length)).2.length + post.length := by
  simp only [Input.size,data,DynamicListReadback.go_append,List.length_append,go_head_length,member_heads,headsOf,Nat.add_assoc]

/-- Arbitrary SAME actual prefix, nonzero pos/off/cursor included. The later
head count is fixed by qs; off is derived from actual heads and leading tails.
Only the earlier prefix is decoded: no later-success premise is assumed. -/
theorem window (ps qs : List Param) (vs : Vals (ps.map Param.shape))
    (ws : Vals (qs.map Param.shape)) (I : Input) (hp lead post : List UInt8) (pos off a f : Nat)
    (headPos : hp.length = 4 + pos)
    (offset : off = pos + headsOf ps + headsOf qs + lead.length)
    (data : I.data = hp ++ (AbiEntry.assemble.go (Vals.parts vs ++ Vals.parts ws) off).1 ++ lead ++
      (AbiEntry.assemble.go (Vals.parts vs ++ Vals.parts ws) off).2 ++ post)
    (padding : 32 ≤ post.length) (size : I.size ≤ lim)
    (room : I.free + (a + LocationPeak.peak ps vs) ≤ lim) (fuel : parameterNeed vs ≤ f) :
    ∃ es : Entries ps, enter I f ps pos a = .ok (es,a + spent ps vs) ∧
      bodyValues I f ps es pos = .ok vs := by
  let next := off + (AbiEntry.assemble.go (Vals.parts vs) off).2.length
  let sh := (AbiEntry.assemble.go (Vals.parts ws) next).1
  let st := (AbiEntry.assemble.go (Vals.parts ws) next).2
  apply LocationPeak.window ps vs I hp (sh ++ lead ++ (AbiEntry.assemble.go (Vals.parts vs) off).2 ++ st ++ post)
    (hp ++ (AbiEntry.assemble.go (Vals.parts vs) off).1 ++ sh ++ lead) (st ++ post) pos off a f
  · simpa only [DynamicListReadback.go_append,List.append_assoc,next,sh,st] using data
  · simpa only [DynamicListReadback.go_append,List.append_assoc,next,sh,st] using data
  · exact headPos
  · simp only [List.length_append,sh,go_head_length,member_heads,headPos]
    simp only [headsOf] at offset
    omega
  · simp only [List.length_append]; omega
  · simp only [List.length_append]; omega
  · exact size
  · exact room
  · exact fuel

theorem members_window (ps qs : List Param) (vs : Vals (ps.map Param.shape))
    (ws : Vals (qs.map Param.shape)) (I : Input) (hp lead post : List UInt8) (pos off a f : Nat)
    (headPos : hp.length = 4 + pos)
    (offset : off = pos + headsOf ps + headsOf qs + lead.length)
    (data : I.data = hp ++ (AbiEntry.assemble.go (Vals.parts vs ++ Vals.parts ws) off).1 ++ lead ++
      (AbiEntry.assemble.go (Vals.parts vs ++ Vals.parts ws) off).2 ++ post)
    (padding : 32 ≤ post.length) (size : I.size ≤ lim)
    (room : I.free + (a + memberAllocation vs) ≤ lim) (fuel : memberNeed vs ≤ f) :
    mmembers I f (ps.map Param.shape) 4 pos a = .ok (vs,a + memberAllocation vs) := by
  let next := off + (AbiEntry.assemble.go (Vals.parts vs) off).2.length
  let sh := (AbiEntry.assemble.go (Vals.parts ws) next).1
  let st := (AbiEntry.assemble.go (Vals.parts ws) next).2
  apply RecursiveReadback.members f vs I hp (sh ++ lead ++ (AbiEntry.assemble.go (Vals.parts vs) off).2 ++ st ++ post)
    (hp ++ (AbiEntry.assemble.go (Vals.parts vs) off).1 ++ sh ++ lead) (st ++ post) 4 pos off a
  · simpa only [DynamicListReadback.go_append,List.append_assoc,next,sh,st] using data
  · simpa only [DynamicListReadback.go_append,List.append_assoc,next,sh,st] using data
  · exact headPos
  · simp only [List.length_append,sh,go_head_length,member_heads,headPos]
    simp only [headsOf] at offset
    omega
  · simp only [List.length_append]; omega
  · simp only [List.length_append]; omega
  · exact size
  · exact room
  · exact fuel


/-- Genuinely typed prefix entry/body for the actual canonical encodeArgs
of arbitrary recursive indexed values. Allocation/fuel cover only ps, not qs. -/
theorem canonical (ps qs : List Param) (vs : Vals (ps.map Param.shape))
    (ws : Vals (qs.map Param.shape)) (selector post : List UInt8) (free a f : Nat)
    (sel : selector.length = 4) (padding : 32 ≤ post.length)
    (size : (input (ps ++ qs) (BodyComposition.appendValues ps qs vs ws) selector post free).size ≤ lim)
    (room : free + (a + LocationPeak.peak ps vs) ≤ lim) (fuel : parameterNeed vs ≤ f) :
    let I := input (ps ++ qs) (BodyComposition.appendValues ps qs vs ws) selector post free
    ∃ es : Entries ps, enter I f ps 0 a = .ok (es,a + spent ps vs) ∧ bodyValues I f ps es 0 = .ok vs := by
  apply window ps qs vs ws _ selector [] post 0 (headsOf ps + headsOf qs) a f
  · omega
  · simp only [List.length_nil,Nat.add_zero,Nat.zero_add]
  · simp only [input,encodeArgs,assembled,parts_append]
    have heads : RecursiveLayout.heads (Vals.parts vs ++ Vals.parts ws) = headsOf ps + headsOf qs := by
      rw [← parts_append,member_heads,← headsOf,EntryComposition.heads_append]
    rw [heads]
    simp only [List.append_nil,List.append_assoc]
  · exact padding
  · exact size
  · exact room
  · exact fuel

theorem decoder_canonical (ps qs : List Param) (vs : Vals (ps.map Param.shape))
    (ws : Vals (qs.map Param.shape)) (selector post : List UInt8) (free a f : Nat)
    (sel : selector.length = 4) (padding : 32 ≤ post.length)
    (size : (input (ps ++ qs) (BodyComposition.appendValues ps qs vs ws) selector post free).size ≤ lim)
    (room : free + (a + memberAllocation vs) ≤ lim) (fuel : memberNeed vs ≤ f) :
    let I := input (ps ++ qs) (BodyComposition.appendValues ps qs vs ws) selector post free
    mmembers I f (ps.map Param.shape) 4 0 a = .ok (vs,a + memberAllocation vs) := by
  apply members_window ps qs vs ws _ selector [] post 0 (headsOf ps + headsOf qs) a f
  · omega
  · simp only [List.length_nil,Nat.add_zero,Nat.zero_add]
  · simp only [input,encodeArgs,assembled,parts_append]
    have heads : RecursiveLayout.heads (Vals.parts vs ++ Vals.parts ws) = headsOf ps + headsOf qs := by
      rw [← parts_append,member_heads,← headsOf,EntryComposition.heads_append]
    rw [heads]
    simp only [List.append_nil,List.append_assoc]
  · exact padding
  · exact size
  · exact room
  · exact fuel


/-- Actual entry head guard and body identity for the selected prefix. This
is entry on ps, not successful admission of every later sibling. -/
theorem prefix_entry (ps qs : List Param) (vs : Vals (ps.map Param.shape))
    (ws : Vals (qs.map Param.shape)) (selector post : List UInt8) (free f : Nat)
    (sel : selector.length = 4) (padding : 32 ≤ post.length)
    (size : (input (ps ++ qs) (BodyComposition.appendValues ps qs vs ws) selector post free).size ≤ lim)
    (room : free + LocationPeak.peak ps vs ≤ lim) (fuel : parameterNeed vs ≤ f) :
    let I := input (ps ++ qs) (BodyComposition.appendValues ps qs vs ws) selector post free
    ∃ es : Entries ps, entry I f ps = .ok es ∧ bodyValues I f ps es 0 = .ok vs := by
  obtain ⟨es,en,body⟩ := canonical ps qs vs ws selector post free 0 f sel padding size
    (by simpa only [Nat.zero_add] using room) fuel
  have bound := assemble_head_bound (Vals.parts (BodyComposition.appendValues ps qs vs ws))
  rw [member_heads,← headsOf,EntryComposition.heads_append] at bound
  have fit : 4 + headsOf ps ≤ (input (ps ++ qs) (BodyComposition.appendValues ps qs vs ws) selector post free).size := by
    simp only [input,Input.size,List.length_append,sel,encodeArgs]
    omega
  refine ⟨es,?_,body⟩
  rw [entry,if_neg (Nat.not_lt.mpr fit),en]

/-- Both actual root byte windows have the same immutable prefix, even when
later encoded tails have different lengths. -/
theorem byte_noninterference (ps qs : List Param) (vs : Vals (ps.map Param.shape))
    (ws zs : Vals (qs.map Param.shape)) :
    let off := headsOf ps + headsOf qs
    let bs := encodeArgs (BodyComposition.appendValues ps qs vs ws)
    let cs := encodeArgs (BodyComposition.appendValues ps qs vs zs)
    bs.take (headsOf ps) = cs.take (headsOf ps) ∧
    (bs.drop off).take (AbiEntry.assemble.go (Vals.parts vs) off).2.length =
      (cs.drop off).take (AbiEntry.assemble.go (Vals.parts vs) off).2.length := by
  have hw := prefix_bytes ps qs vs ws
  have hz := prefix_bytes ps qs vs zs
  exact ⟨hw.1.trans hz.1.symm,hw.2.trans hz.2.symm⟩

/-- Replacing later VALUES at the same actual shapes leaves the entered
prefix's typed body and exact cursor invariant. This observes actual enter
and bodyValues, not host encoded-byte equality. Raw Entries identity is not
asserted here; the result retains each actual Entries witness. -/
theorem noninterference (ps qs : List Param) (vs : Vals (ps.map Param.shape))
    (ws zs : Vals (qs.map Param.shape)) (selector post : List UInt8) (free a f : Nat)
    (sel : selector.length = 4) (padding : 32 ≤ post.length)
    (sizeW : (input (ps ++ qs) (BodyComposition.appendValues ps qs vs ws) selector post free).size ≤ lim)
    (sizeZ : (input (ps ++ qs) (BodyComposition.appendValues ps qs vs zs) selector post free).size ≤ lim)
    (room : free + (a + LocationPeak.peak ps vs) ≤ lim) (fuel : parameterNeed vs ≤ f) :
    let IW := input (ps ++ qs) (BodyComposition.appendValues ps qs vs ws) selector post free
    let IZ := input (ps ++ qs) (BodyComposition.appendValues ps qs vs zs) selector post free
    (enter IW f ps 0 a).map (fun r => (bodyValues IW f ps r.1 0,r.2)) = .ok (.ok vs,a + spent ps vs) ∧
    (enter IZ f ps 0 a).map (fun r => (bodyValues IZ f ps r.1 0,r.2)) = .ok (.ok vs,a + spent ps vs) := by
  obtain ⟨ew,hw,bw⟩ := canonical ps qs vs ws selector post free a f sel padding sizeW room fuel
  obtain ⟨ez,hz,bz⟩ := canonical ps qs vs zs selector post free a f sel padding sizeZ room fuel
  constructor <;> simp only [hw,hz,Except.map,bw,bz]

end Solidity.Backend.AbiWorld.SiblingReadback
