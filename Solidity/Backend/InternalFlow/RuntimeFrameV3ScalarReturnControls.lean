import Solidity.Backend.InternalFlow.RuntimeFrameV3ScalarCallReturn
import Solidity.Backend.InternalFlow.RuntimeFrameV3AllocatorReturn

/-! Inhabited zero/one/two/three-count clients of the SAME generic scalar-call
image, with genuine initial owner and complete protected/payload/heap words.
No target endpoint is normalized independently or assumed. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.ScalarCallReturn.Client
open Evm Evm.Memory RecursiveSource ScalarRecursiveSource CountdownWitness

def caller (n : Nat) (bound : n<W) := CountdownWitness.callee.setLocal .here (countValue n bound)
def before (n : Nat) := writeMachine AllocatorReturn.Checks.input 3 (.val (wmod n))

theorem encoded (n : Nat) (bound : n<W) : ReprV .uint (countValue n bound) (.val (wmod n)) := by
 have same : wmod n=(⟨n,bound⟩ : Fin W) := Fin.ext (Nat.mod_eq_of_lt bound)
 rw [same]
 exact ReprV.uint_of rfl

theorem initial (n : Nat) (bound : n<W) : StateRepr 1 2 16 CountdownWitness.F (caller n bound) P.base (before n) :=
 AllocatorReturn.Checks.represented.setVal .here (countValue n bound) (.val (wmod n)) (encoded n bound)

theorem initial_owner (n : Nat) (bound : n<W) :
 StructAllocatorRepr (caller n bound).heap P.base 16 ⟨22,by decide⟩ (before n) :=
 AllocatorReturn.Checks.ownership.localWrite 3 (by decide) (by decide) (.val (wmod n))

theorem available (n : Nat) (within : n≤3) : ∃ after addresses,
 run (image (C:=P.C) 2 CountdownWitness.F 8 7) (before n)=.ok after 0 ∧
 (∀ f depth,(call (R:=CountdownWitness.A) rfl f depth).run (caller n (Nat.lt_of_le_of_lt within (by decide)))=
   if n<depth then .ok ⟨(caller n (Nat.lt_of_le_of_lt within (by decide))).setLocal .here
     (countValue n (Nat.lt_of_le_of_lt within (by decide))),List.prefix_refl _⟩ else .error .exhausted) ∧
 StateRepr 1 2 16 CountdownWitness.F ((caller n (Nat.lt_of_le_of_lt within (by decide))).setLocal .here
   (countValue n (Nat.lt_of_le_of_lt within (by decide)))) addresses after ∧
 after.stack=[w[77]] ∧ BaseExtends (caller n (Nat.lt_of_le_of_lt within (by decide))).H P.base addresses ∧
 after.mem 8=w[10] ∧ after.mem 7=w[10] ∧ after.mem 2=w[16] ∧ after.mem 3=.val (wmod n) ∧ after.mem 4=.val (wmod n) ∧
 StructAllocatorRepr (caller n (Nat.lt_of_le_of_lt within (by decide))).heap addresses 16 ⟨22,by decide⟩ after ∧
 (∀ x,x≠8 → x≠7 → x≠2 → x≠3 → x≠4 → (x<10 ∨ 10+2*n≤x) → after.mem x=(before n).mem x) ∧
 (∀ j,j<n → after.mem (10+2*j)=w[16] ∧ after.mem (10+2*j+1)=.val (wmod (n-j))) := by
 obtain ⟨after,addresses,executed,source,reached,stack,extended,cursor,bottomWord,reference,destination,privateWord,growth,outside,saved⟩ :=
   endpoint rfl n (Nat.lt_of_le_of_lt within (by decide)) (caller n (Nat.lt_of_le_of_lt within (by decide))) P.r0 rfl rfl
     P.base (before n) (initial n _) 8 8 7 10 (by decide) (by decide) (by decide) (by decide) (by decide)
       (by decide) (by decide) (by decide) (by decide) (by omega)
       (Nat.lt_of_le_of_lt (show 10+2*n≤16 from by omega) (by decide)) rfl
 have owned := growth ⟨22,by decide⟩ (by decide) (initial_owner n _) (by decide)
 refine ⟨after,addresses,executed,source,reached,stack,extended,cursor,bottomWord,reference,destination,privateWord,owned,outside,?_⟩
 intro j small
 exact ⟨(saved j small).1,(saved j small).2⟩

noncomputable def machine (n : Nat) (within : n≤3) : Machine := (available n within).choose
noncomputable def addresses (n : Nat) (within : n≤3) : Nat → Fin W := (available n within).choose_spec.choose

theorem specification (n : Nat) (within : n≤3) :
 run (image (C:=P.C) 2 CountdownWitness.F 8 7) (before n)=.ok (machine n within) 0 ∧
 (∀ f depth,(call (R:=CountdownWitness.A) rfl f depth).run (caller n (Nat.lt_of_le_of_lt within (by decide)))=
   if n<depth then .ok ⟨(caller n (Nat.lt_of_le_of_lt within (by decide))).setLocal .here
     (countValue n (Nat.lt_of_le_of_lt within (by decide))),List.prefix_refl _⟩ else .error .exhausted) ∧
 StateRepr 1 2 16 CountdownWitness.F ((caller n (Nat.lt_of_le_of_lt within (by decide))).setLocal .here
   (countValue n (Nat.lt_of_le_of_lt within (by decide)))) (addresses n within) (machine n within) ∧
 (machine n within).stack=[w[77]] ∧ BaseExtends (caller n (Nat.lt_of_le_of_lt within (by decide))).H P.base (addresses n within) ∧
 (machine n within).mem 8=w[10] ∧ (machine n within).mem 7=w[10] ∧ (machine n within).mem 2=w[16] ∧ (machine n within).mem 3=.val (wmod n) ∧ (machine n within).mem 4=.val (wmod n) ∧
 StructAllocatorRepr (caller n (Nat.lt_of_le_of_lt within (by decide))).heap (addresses n within) 16 ⟨22,by decide⟩ (machine n within) ∧
 (∀ x,x≠8 → x≠7 → x≠2 → x≠3 → x≠4 → (x<10 ∨ 10+2*n≤x) → (machine n within).mem x=(before n).mem x) ∧
 (∀ j,j<n → (machine n within).mem (10+2*j)=w[16] ∧ (machine n within).mem (10+2*j+1)=.val (wmod (n-j))) := (available n within).choose_spec.choose_spec

theorem payload_words (n : Nat) (within : n≤3) (j : Nat) (small : j<3) :
 (machine n within).mem (10+2*j)=(if j<n then w[16] else w[0]) ∧
 (machine n within).mem (10+2*j+1)=(if j<n then .val (wmod (n-j)) else w[0]) := by
 rcases specification n within with ⟨_,_,_,_,_,_,_,_,_,_,_,outside,saved⟩
 by_cases live : j<n
 · simp only [if_pos live]
   exact saved j live
 · simp only [if_neg live]
   have refWord := outside (10+2*j) (by omega) (by omega) (by omega) (by omega) (by omega) (.inr (by omega))
   have countWord := outside (10+2*j+1) (by omega) (by omega) (by omega) (by omega) (by omega) (.inr (by omega))
   rw [refWord,countWord]
   rcases (by omega : j=0 ∨ j=1 ∨ j=2) with rfl | rfl | rfl <;> constructor <;> rfl

theorem snapshot (n : Nat) (within : n≤3) :
 ((machine n within).stack,[(machine n within).mem 0,(machine n within).mem 1,(machine n within).mem 2,
 (machine n within).mem 3,(machine n within).mem 4,(machine n within).mem 6,(machine n within).mem 7,
 (machine n within).mem 8,(machine n within).mem 9,(machine n within).mem 10,(machine n within).mem 11,
 (machine n within).mem 12,(machine n within).mem 13,(machine n within).mem 14,(machine n within).mem 15,
 (machine n within).mem 16,(machine n within).mem 17,(machine n within).mem 18,(machine n within).mem 20,
 (machine n within).mem 21])=
 ([w[77]],[w[22],w[16],w[16],.val (wmod n),.val (wmod n),w[0],w[10],w[10],w[99],
 if 0<n then w[16] else w[0],if 0<n then .val (wmod n) else w[0],
 if 1<n then w[16] else w[0],if 1<n then .val (wmod (n-1)) else w[0],
 if 2<n then w[16] else w[0],if 2<n then .val (wmod (n-2)) else w[0],
 w[2],w[7],w[9],w[1],w[4]]) := by
 rcases specification n within with ⟨executed,source,reached,stack,extended,cursor,bottomWord,alias,count,result,owner,outside,saved⟩
 have same (x : Nat) (hp : x≠8) (hb : x≠7) (hr : x≠2) (hc : x≠3) (hv : x≠4)
     (region : x<10 ∨ 10+2*n≤x) : (machine n within).mem x=(before n).mem x := outside x hp hb hr hc hv region
 rw [stack,owner.arrays.free.cell,alias,count,result,bottomWord,cursor,
   same 1 (by decide) (by decide) (by decide) (by decide) (by decide) (.inl (by decide)),
   same 6 (by decide) (by decide) (by decide) (by decide) (by decide) (.inl (by decide)),
   same 9 (by decide) (by decide) (by decide) (by decide) (by decide) (.inl (by decide)),
   (payload_words n within 0 (by decide)).1,(payload_words n within 0 (by decide)).2,
   (payload_words n within 1 (by decide)).1,(payload_words n within 1 (by decide)).2,
   (payload_words n within 2 (by decide)).1,(payload_words n within 2 (by decide)).2,
   same 16 (by decide) (by decide) (by decide) (by decide) (by decide) (.inr (by omega)),
   same 17 (by decide) (by decide) (by decide) (by decide) (by decide) (.inr (by omega)),
   same 18 (by decide) (by decide) (by decide) (by decide) (by decide) (.inr (by omega)),
   same 20 (by decide) (by decide) (by decide) (by decide) (by decide) (.inr (by omega)),
   same 21 (by decide) (by decide) (by decide) (by decide) (by decide) (.inr (by omega))]
 rfl

theorem native_and_target (n : Nat) (within : n≤3) (f : Name) (depth : Nat) (enough : n<depth) :
 (call (R:=CountdownWitness.A) rfl f depth).run (caller n (Nat.lt_of_le_of_lt within (by decide)))=
   .ok ⟨(caller n (Nat.lt_of_le_of_lt within (by decide))).setLocal .here
     (countValue n (Nat.lt_of_le_of_lt within (by decide))),List.prefix_refl _⟩ ∧
 run (image (C:=P.C) 2 CountdownWitness.F 8 7) (before n)=.ok (machine n within) 0 := by
 have actual := (specification n within).2.1 f depth
 rw [if_pos enough] at actual
 exact ⟨actual,(specification n within).1⟩

theorem wrong_alias (n : Nat) (within : n≤3) : (machine n within).mem 2≠w[20] := by
 rcases specification n within with ⟨_,_,_,_,_,_,_,alias,_⟩
 rw [alias]
 decide

theorem wrong_private (n : Nat) (within : n≤3) (positive : 0<n) : (machine n within).mem 4≠w[0] := by
 rcases specification n within with ⟨_,_,_,_,_,_,_,_,_,result,_⟩
 rw [result]
 intro wrong
 have same := congrArg Fin.val (Word.val.inj wrong)
 change n%W=0 at same
 rw [Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt within (by decide))] at same
 omega

theorem wrong_runtime_cursor (n : Nat) (within : n≤3) : (machine n within).mem 8≠w[16] := by
 rcases specification n within with ⟨_,_,_,_,_,cursor,_⟩
 rw [cursor]
 decide

theorem wrong_heap_cursor (n : Nat) (within : n≤3) : (machine n within).mem 0≠w[23] := by
 rcases specification n within with ⟨_,_,_,_,_,_,_,_,_,_,owner,_⟩
 rw [owner.arrays.free.cell]
 decide

theorem shallow (n : Nat) (within : n≤3) (f : Name) (depth : Nat) (short : depth≤n) :
 (call (R:=CountdownWitness.A) rfl f depth).run (caller n (Nat.lt_of_le_of_lt within (by decide)))=.error .exhausted := by
 have actual := (specification n within).2.1 f depth
 simpa only [if_neg (show ¬n<depth from by omega)] using actual

theorem shallow_not_revert (n : Nat) (within : n≤3) (f : Name) (depth : Nat) (short : depth≤n) :
 (call (R:=CountdownWitness.A) rfl f depth).run (caller n (Nat.lt_of_le_of_lt within (by decide)))≠.error .revert := by
 rw [shallow n within f depth short]
 intro wrong
 cases wrong

theorem not_revert (n : Nat) (within : n≤3) :
 run (image (C:=P.C) 2 CountdownWitness.F 8 7) (before n)≠.revert := by
 rw [(specification n within).1]
 intro wrong
 cases wrong

theorem not_fault (n : Nat) (within : n≤3) :
 run (image (C:=P.C) 2 CountdownWitness.F 8 7) (before n)≠.fault := by
 rw [(specification n within).1]
 intro wrong
 cases wrong

end Solidity.Backend.InternalFlow.RuntimeFrame.ScalarCallReturn.Client
