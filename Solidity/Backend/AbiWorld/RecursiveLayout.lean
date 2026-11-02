import Solidity.Backend.AbiWorld.NestedByteReadback

/-! Measurements and actual codec layout for arbitrary existing intrinsic
Val/Seq/Vals. No decoder, evaluator, admission predicate or simulation oracle. -/
namespace Solidity.Backend.AbiWorld.RecursiveLayout
open AbiEntry

mutual
def allocation : {s : AbiEntry.Shape} → AbiEntry.Val s → Nat
  | _, .word _ => 0
  | _, .bytes bs => BytesReadback.allocationBytes bs
  | _, .array (n := n) xs => n * 32 + 32 + sequenceAllocation xs
  | _, .fixed (n := n) xs => n * 32 + sequenceAllocation xs
  | _, .tuple (ms := ms) vs => ms.length * 32 + memberAllocation vs
def sequenceAllocation : {e : AbiEntry.Shape} → {n : Nat} → Seq e n → Nat
  | _, _, .nil => 0
  | _, _, .cons v vs => allocation v + sequenceAllocation vs
def memberAllocation : {ms : List AbiEntry.Shape} → Vals ms → Nat
  | _, .nil => 0
  | _, .cons v vs => allocation v + memberAllocation vs
end

mutual
/-- Sufficient ORIGINAL mdec fuel; no default or execution budget changes. -/
def need : {s : AbiEntry.Shape} → AbiEntry.Val s → Nat
  | _, .word _ => 1
  | _, .bytes _ => 1
  | _, .array xs => sequenceNeed xs + 1
  | _, .fixed xs => sequenceNeed xs + 1
  | _, .tuple vs => memberNeed vs + 1
def sequenceNeed : {e : AbiEntry.Shape} → {n : Nat} → Seq e n → Nat
  | _, _, .nil => 0
  | _, _, .cons v vs => max (need v + 1) (sequenceNeed vs) + 1
def memberNeed : {ms : List AbiEntry.Shape} → Vals ms → Nat
  | _, .nil => 0
  | _, .cons v vs => max (need v + 1) (memberNeed vs) + 1
end

def heads (ps : List (Bool × List UInt8)) : Nat :=
  ps.foldr (fun p n => (if p.1 then 32 else p.2.length) + n) 0

theorem heads_cons (p : Bool × List UInt8) (ps : List (Bool × List UInt8)) :
    heads (p :: ps) = (if p.1 then 32 else p.2.length) + heads ps := rfl

theorem fold_heads (ps : List (Bool × List UInt8)) (a : Nat) :
    ps.foldl (fun acc (d,b) => acc + if d then 32 else b.length) a = a + heads ps := by
  induction ps generalizing a with
  | nil => simp only [List.foldl_nil,heads,List.foldr_nil,Nat.add_zero]
  | cons p ps ih =>
    rcases p with ⟨d,b⟩
    simp only [List.foldl_cons,ih,heads,List.foldr_cons,Nat.add_assoc]

theorem go_head_length (ps : List (Bool × List UInt8)) (off : Nat) :
    (AbiEntry.assemble.go ps off).1.length = heads ps := by
  induction ps generalizing off with
  | nil => rfl
  | cons p ps ih =>
    rcases p with ⟨d,b⟩
    cases d <;> simp only [AbiEntry.assemble.go,Bool.false_eq_true,ite_false,ite_true,List.length_append,
      MixedPacket.word_length,ih,heads,List.foldr_cons]

theorem assembled (ps : List (Bool × List UInt8)) :
    AbiEntry.assemble ps = (AbiEntry.assemble.go ps (heads ps)).1 ++ (AbiEntry.assemble.go ps (heads ps)).2 := by
  simp only [AbiEntry.assemble,fold_heads,Nat.zero_add]

theorem sequence_flags {e : AbiEntry.Shape} {n : Nat} (xs : Seq e n) (stat : e.dynamic = false) :
    ∀ p ∈ Seq.parts xs, p.1 = false := by
  induction n with
  | zero => cases xs; simp only [Seq.parts,List.not_mem_nil,false_implies,forall_const]
  | succ n ih =>
    cases xs with
    | cons v xs =>
      intro p hp
      simp only [Seq.parts,List.mem_cons] at hp
      rcases hp with rfl | hp
      · exact stat
      · exact ih xs p hp

theorem member_flags {ms : List AbiEntry.Shape} (vs : Vals ms) (stat : Shape.anyDynamic ms = false) :
    ∀ p ∈ Vals.parts vs, p.1 = false := by
  induction ms with
  | nil => cases vs; simp only [Vals.parts,List.not_mem_nil,false_implies,forall_const]
  | cons s ss ih =>
    cases vs with
    | cons v vs =>
      have hs : s.dynamic = false := by
        cases h : s.dynamic with
        | false => rfl
        | true => simp only [Shape.anyDynamic,h,Bool.true_or] at stat; cases stat
      have ht : Shape.anyDynamic ss = false := by simpa only [Shape.anyDynamic,hs,Bool.false_or] using stat
      intro p hp
      simp only [Vals.parts,List.mem_cons] at hp
      rcases hp with rfl | hp
      · exact hs
      · exact ih vs ht p hp

theorem any_static_cons (s : AbiEntry.Shape) (ss : List AbiEntry.Shape)
    (stat : Shape.anyDynamic (s :: ss) = false) : s.dynamic = false ∧ Shape.anyDynamic ss = false := by
  cases h : s.dynamic with
  | false => exact ⟨rfl,by simpa only [Shape.anyDynamic,h,Bool.false_or] using stat⟩
  | true => simp only [Shape.anyDynamic,h,Bool.true_or] at stat; cases stat

mutual
/-- Actual STATIC payload length, including zero-sized static aggregates. -/
theorem static_length : {s : AbiEntry.Shape} → (v : AbiEntry.Val s) → s.dynamic = false → (Val.enc v).length = s.headSize
  | _, .word w, _ => MixedPacket.word_length w.val
  | _, .bytes _, stat => by cases stat
  | _, .array _, stat => by cases stat
  | _, .fixed xs, stat => by
    simp only [Shape.dynamic] at stat
    simp only [Val.enc,Shape.headSize,stat,Bool.false_eq_true,ite_false]
    exact static_sequence xs stat
  | _, .tuple vs, stat => by
    simp only [Shape.dynamic] at stat
    simp only [Val.enc,Shape.headSize,stat,Bool.false_eq_true,ite_false]
    exact static_members vs stat

theorem static_sequence : {e : AbiEntry.Shape} → {n : Nat} → (xs : Seq e n) → e.dynamic = false →
    (AbiEntry.assemble (Seq.parts xs)).length = n * e.headSize
  | e, _, .nil, _ => by change 0 = 0 * e.headSize; rw [Nat.zero_mul]
  | e, _, .cons v xs, stat => by
    have hv := static_length v stat
    have ht := static_sequence xs stat
    rw [WordListReadback.assemble_static _ (sequence_flags xs stat)] at ht
    rw [WordListReadback.assemble_static _ (sequence_flags (Seq.cons v xs) stat)]
    simp only [Seq.parts,List.flatMap_cons,List.length_append,hv,ht,Nat.succ_mul]
    omega

theorem static_members : {ms : List AbiEntry.Shape} → (vs : Vals ms) → Shape.anyDynamic ms = false →
    (AbiEntry.assemble (Vals.parts vs)).length = Shape.headsSize ms
  | _, .nil, _ => rfl
  | _, .cons v vs, stat => by
    obtain ⟨hs,ht⟩ := any_static_cons _ _ stat
    have hv := static_length v hs
    have tail := static_members vs ht
    rw [WordListReadback.assemble_static _ (member_flags vs ht)] at tail
    rw [WordListReadback.assemble_static _ (member_flags (Vals.cons v vs) stat)]
    simp only [Vals.parts,List.flatMap_cons,List.length_append,hv,tail,Shape.headsSize]
end

theorem sequence_heads {e : AbiEntry.Shape} {n : Nat} (xs : Seq e n) :
    heads (Seq.parts xs) = n * e.headSize := by
  induction n with
  | zero => cases xs; change 0 = 0 * e.headSize; rw [Nat.zero_mul]
  | succ n ih =>
    cases xs with
    | cons v xs =>
      cases h : e.dynamic
      case false => simp only [Seq.parts,heads_cons,h,Bool.false_eq_true,ite_false,static_length v h,ih xs,Nat.succ_mul]; omega
      case true => simp only [Seq.parts,heads_cons,h,ite_true,ByteSequenceReadback.dynamic_head e h,ih xs,Nat.succ_mul]; omega

theorem member_heads {ms : List AbiEntry.Shape} (vs : Vals ms) :
    heads (Vals.parts vs) = Shape.headsSize ms := by
  induction ms with
  | nil => cases vs; rfl
  | cons s ss ih =>
    cases vs with
    | cons v vs =>
      cases h : s.dynamic
      case false => simp only [Vals.parts,heads_cons,h,Bool.false_eq_true,ite_false,static_length v h,ih vs,Shape.headsSize]
      case true => simp only [Vals.parts,heads_cons,h,ite_true,ByteSequenceReadback.dynamic_head s h,ih vs,Shape.headsSize]

theorem go_head_cons (d : Bool) (b : List UInt8) (ps : List (Bool × List UInt8)) (off : Nat) :
    (AbiEntry.assemble.go ((d,b) :: ps) off).1 =
      (if d then AbiEntry.wordBytes off else b) ++ (AbiEntry.assemble.go ps (if d then off + b.length else off)).1 := by
  cases d <;> rfl

theorem go_tail_cons (d : Bool) (b : List UInt8) (ps : List (Bool × List UInt8)) (off : Nat) :
    (AbiEntry.assemble.go ((d,b) :: ps) off).2 =
      (if d then b else []) ++ (AbiEntry.assemble.go ps (if d then off + b.length else off)).2 := by
  cases d <;> simp only [AbiEntry.assemble.go,Bool.false_eq_true,ite_false,ite_true,List.nil_append]

theorem piece_length {s : AbiEntry.Shape} (v : AbiEntry.Val s) (off : Nat) :
    (if s.dynamic then AbiEntry.wordBytes off else Val.enc v).length = s.headSize := by
  cases h : s.dynamic
  case false => simp only [h,Bool.false_eq_true,ite_false,static_length v h]
  case true => simp only [h,ite_true,MixedPacket.word_length,ByteSequenceReadback.dynamic_head s h]

theorem assemble_head_bound (ps : List (Bool × List UInt8)) : heads ps ≤ (AbiEntry.assemble ps).length := by
  rw [assembled,List.length_append,go_head_length]
  omega

theorem tail_length (ps : List (Bool × List UInt8)) (off : Nat) :
    (AbiEntry.assemble.go ps off).2.length =
      (ps.map (fun p => if p.1 then p.2.length else 0)).sum := by
  induction ps generalizing off with
  | nil => rfl
  | cons p ps ih =>
    rcases p with ⟨d,b⟩
    rw [go_tail_cons]
    cases d <;> simp only [Bool.false_eq_true,ite_false,ite_true,List.length_append,List.length_nil,
      ih,List.map_cons,List.sum_cons,Nat.zero_add]

theorem assemble_length (ps : List (Bool × List UInt8)) :
    (AbiEntry.assemble ps).length = heads ps +
      (ps.map (fun p => if p.1 then p.2.length else 0)).sum := by
  rw [assembled,List.length_append,go_head_length,tail_length]

end Solidity.Backend.AbiWorld.RecursiveLayout
