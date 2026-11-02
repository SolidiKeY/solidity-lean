import Solidity.Backend.AbiWorld.SiblingReadback

/-! Raw fields of ACTUAL successful calldata entry. No new decoder, admitted
profile or oracle. All length/header observations use the existing loader. -/
namespace Solidity.Backend.AbiWorld.ReferenceFields
open AbiEntry

theorem word_window (pre post : List UInt8) (n : Nat) :
    load (pre ++ AbiEntry.wordBytes n ++ post) pre.length = load (AbiEntry.wordBytes n) 0 := by
  have a := CanonicalReadback.bytes_word pre post n
  have b := CanonicalReadback.bytes_word [] [] n
  have fold (d : List UInt8) (p : Nat) : load d p = Semantics.bytesNat (bytesAt d p 32) % W := by
    simp only [load,Semantics.bytesNat,bytesAt,List.foldl_map]
  rw [fold,fold,a]
  simpa only [List.nil_append,List.append_nil,List.length_nil] using congrArg (fun bs => Semantics.bytesNat bs % W) b.symm

theorem bytes_run (I : Input) (pos off count : Nat)
    (head : load I.data (4+pos) = off) (length : load I.data (4+off) = count)
    (offsetBound : off ≤ lim) (countBound : count ≤ lim)
    (header : 4+off+31 < I.size) (region : 4+off+32+count ≤ I.size) :
    cref I .bytes 4 pos = .ok (4+off+32,count) := by
  simp only [cref,Shape.dynamic,ite_true,head,if_neg (Nat.not_lt.mpr offsetBound),
    if_pos header,length,if_neg (Nat.not_lt.mpr countBound),Shape.stride,Nat.mul_one,
    if_neg (Nat.not_lt.mpr region)]

/-- Successful cref determines its REAL fields, including zero-length/static
cases. Failed guards are eliminated using the actual successful execution. -/
theorem fields (I : Input) (s : AbiEntry.Shape) (pos addr len : Nat)
    (h : cref I s 4 pos = .ok (addr,len)) :
    (addr,len) = if s.dynamic then
      (if s.lengthPrefixed then (4 + load I.data (4 + pos) + 32,load I.data (4 + load I.data (4 + pos)))
       else (4 + load I.data (4 + pos),0)) else (4 + pos,0) := by
  cases s with
  | word k =>
    simp only [cref,Shape.dynamic,Bool.false_eq_true,ite_false] at h ⊢
    exact (Except.ok.inj h).symm
  | bytes =>
    simp only [cref,Shape.dynamic,ite_true] at h
    simp only [Shape.dynamic,Shape.lengthPrefixed,ite_true]
    split at h
    · cases h
    · split at h
      · split at h
        · cases h
        · split at h
          · cases h
          · exact (Except.ok.inj h).symm
      · cases h
  | array e =>
    simp only [cref,Shape.dynamic,ite_true] at h
    simp only [Shape.dynamic,Shape.lengthPrefixed,ite_true]
    split at h
    · cases h
    · split at h
      · split at h
        · cases h
        · split at h
          · cases h
          · exact (Except.ok.inj h).symm
      · cases h
  | fixed e n =>
    by_cases hd : (AbiEntry.Shape.fixed e n).dynamic = true
    · simp only [cref,hd,ite_true] at h
      simp only [hd,ite_true,Shape.lengthPrefixed,Bool.false_eq_true,ite_false]
      split at h
      · cases h
      · split at h
        · cases h
        · exact (Except.ok.inj h).symm
    · simp only [cref,hd,Bool.false_eq_true,ite_false] at h ⊢
      exact (Except.ok.inj h).symm
  | tuple ms =>
    by_cases hd : (AbiEntry.Shape.tuple ms).dynamic = true
    · simp only [cref,hd,ite_true] at h
      simp only [hd,ite_true,Shape.lengthPrefixed,Bool.false_eq_true,ite_false]
      split at h
      · cases h
      · split at h
        · cases h
        · exact (Except.ok.inj h).symm
    · simp only [cref,hd,Bool.false_eq_true,ite_false] at h ⊢
      exact (Except.ok.inj h).symm

theorem length_header {s : AbiEntry.Shape} (v : AbiEntry.Val s) (I J : Input)
    (pre post pre' post' : List UInt8) (p : Nat)
    (a : I.data = pre ++ v.enc ++ post) (b : J.data = pre' ++ v.enc ++ post')
    (pa : pre.length = p) (pb : pre'.length = p) (hl : s.lengthPrefixed = true) :
    load I.data p = load J.data p := by
  cases v with
  | word w => cases hl
  | bytes bs =>
    have ra := word_window pre (bs ++ List.replicate (roundUp bs.length - bs.length) 0 ++ post) bs.length
    have rb := word_window pre' (bs ++ List.replicate (roundUp bs.length - bs.length) 0 ++ post') bs.length
    rw [pa] at ra
    rw [pb] at rb
    simpa only [a,b,Val.enc,List.append_assoc] using ra.trans rb.symm
  | @array e n xs =>
    have ra := word_window pre (AbiEntry.assemble (Seq.parts xs) ++ post) n
    have rb := word_window pre' (AbiEntry.assemble (Seq.parts xs) ++ post') n
    rw [pa] at ra
    rw [pb] at rb
    simpa only [a,b,Val.enc,List.append_assoc] using ra.trans rb.symm
  | fixed xs => cases hl
  | tuple vs => cases hl

/-- Conditional field lemma only; the raw-entry consumer discharges BOTH
cref successes from real canonical melem/eager execution. -/
theorem agree {s : AbiEntry.Shape} (v : AbiEntry.Val s) (I J : Input)
    (hp hs tp ts hp' hs' tp' ts' : List UInt8) (pos off addr len addr' len' : Nat)
    (ha : I.data = hp ++ (if s.dynamic then AbiEntry.wordBytes off else v.enc) ++ hs)
    (hb : J.data = hp' ++ (if s.dynamic then AbiEntry.wordBytes off else v.enc) ++ hs')
    (ta : s.dynamic = true → I.data = tp ++ v.enc ++ ts)
    (tb : s.dynamic = true → J.data = tp' ++ v.enc ++ ts')
    (pa : hp.length = 4 + pos) (pb : hp'.length = 4 + pos)
    (qa : s.dynamic = true → tp.length = 4 + off) (qb : s.dynamic = true → tp'.length = 4 + off)
    (size : I.size ≤ lim)
    (ca : cref I s 4 pos = .ok (addr,len)) (cb : cref J s 4 pos = .ok (addr',len')) :
    (addr,len) = (addr',len') := by
  rw [fields I s pos addr len ca,fields J s pos addr' len' cb]
  cases hd : s.dynamic
  case false => simp only [hd,Bool.false_eq_true,ite_false]
  case true =>
    have bound : off ≤ lim := by
      have d := ta hd
      have q := qa hd
      have h : tp.length ≤ I.size := by simp only [Input.size,d,List.length_append]; omega
      omega
    have ra : load I.data (4 + pos) = off := by
      rw [← pa,ha]
      simpa only [hd,ite_true] using CanonicalReadback.load_word hp hs off (Nat.lt_of_le_of_lt bound (by decide))
    have rb : load J.data (4 + pos) = off := by
      rw [← pb,hb]
      simpa only [hd,ite_true] using CanonicalReadback.load_word hp' hs' off (Nat.lt_of_le_of_lt bound (by decide))
    simp only [hd,ite_true,ra,rb]
    cases hl : s.lengthPrefixed
    case false => simp only [hl,Bool.false_eq_true,ite_false]
    case true =>
      simp only [hl,ite_true]
      exact congrArg (fun n => (4 + off + 32,n))
        (length_header v I J tp ts tp' ts' (4 + off) (ta hd) (tb hd) (qa hd) (qb hd) hl)

end Solidity.Backend.AbiWorld.ReferenceFields
