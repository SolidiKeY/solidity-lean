import Solidity.Backend.MemoryOps.MixedCalldataScheduleTransport
import Solidity.Backend.MemoryOps.CalldataUintScheduleControls

namespace Solidity.Backend.MemoryOps.MixedScheduleControls
open SequenceFixtures
open UintScheduleControls (repairs repairs_origin)
private def eight : U := ⟨8,by decide⟩
private def nine : U := ⟨9,by decide⟩
/-- Both operations read ONE existing immutable decoded table. -/
def input : Source.Calldata D := ⟨[],fun off => if off=7 then (bools [true]).objects off else (uints [nine]).objects off⟩
theorem input_bool : DecodedArrayAt (n:=none) input 7 1 (fun _ h => by cases h)
    (fun i => .val (.bool ([true][i]))) := rfl
theorem input_uint : DecodedArrayAt (n:=none) input 9 1 (fun _ h => by cases h)
    (fun i => .val (sourceUint ([nine][i]))) := rfl
private theorem input_bools_values : List.ofFn (fun i : Fin 1 => calldataBool
    (Source.Data.val (Source.Val.bool (D:=D) ([true][i]))))=[true] := by rfl
private theorem input_uints_values : List.ofFn (fun i : Fin 1 => calldataUint
    (Source.Data.val (sourceUint (D:=D) ([nine][i]))))=[nine] := by
  simpa only [List.ofFn_succ,List.ofFn_zero] using
    congrArg (fun value : U => [value]) (calldataUint_sourceUint (D:=D) nine)
private theorem lookupB : calldataBools input 7=some [true] := by rw [calldataBools_lookup input_bool,input_bools_values]
private theorem lookupU : calldataUints input 9=some [nine] := by rw [calldataUints_lookup input_uint,input_uints_values]

theorem repairs_valid (size copies : Nat) (hsize : 3 ≤ size) : CapturesValid size (repairs copies) := by
  intro x hx
  have he : x=UintScheduleControls.repair := by
    rcases List.mem_cons.mp hx with h | h
    · exact h
    · exact (List.mem_replicate.mp h).2
  subst x
  change 2 ≤ 3 ∧ 3 ≤ size ∧ 1+(3-2) ≤ size
  omega

theorem initial_bool_agreement (tail : List Bool) (copies : Nat) : ∀ k,
    (replaceSlice ([true,false,false]++tail) 1 (([true].drop 0).take (1-0)))[captureOrigin (repairs copies) k]? =
      ([true,false,false]++tail)[k]? := by
  intro k
  rw [repairs_origin]
  cases k with
  | zero => rfl
  | succ k =>
    cases k with
    | zero => rfl
    | succ k => rw [if_neg (by omega)]; rfl

/-- Input-only certificates reconstruct the actual mixed run, then independently
computed BOTH initial criteria derive final heap equality; no run/postrelation input. -/
theorem fixture_restore {H : HTy} {R Q : RefTy} (hp : Heap H)
    (r : HRef H R) (a : ArrTy R (.prim .bool)) (q : HRef H Q) (b : ArrTy Q (.prim .uint))
    (bt : List Bool) (ut : List U)
    (hb : MObj.elems a (hp.get r)=[true,false,false]++bt)
    (hu : MObj.elems b (hp.get q)=[seven,eight,eight]++ut) (bc uc : Nat) :
    checkedMixedCaptures input 7 input 9 hp r a 0 1 1 q b 0 1 1 (repairs bc) (repairs uc)=some hp := by
  have lb : 3 ≤ hp.len r a := by
    unfold Heap.len
    rw [hb,List.length_append]
    simp only [List.length_cons,List.length_nil]; omega
  have lu : 3 ≤ hp.len q b := by
    unfold Heap.len
    rw [hu,List.length_append]
    simp only [List.length_cons,List.length_nil]; omega
  obtain ⟨out,ho⟩ := (checkedMixedCaptures_success_lookup input 7 input 9 hp r a 0 1 1 q b 0 1 1 _ _).mpr
    ⟨[true],[nine],lookupB,lookupU,⟨by decide,by decide⟩,by omega,
      ⟨by decide,by decide⟩,by omega,repairs_valid _ bc lb,repairs_valid _ uc lu⟩
  have he : out=hp := (checkedMixedCaptures_restore input 7 input 9 hp r a 0 1 1 q b 0 1 1 _ _ out ho).mpr
    ⟨[true],[nine],lookupB,lookupU,by rw [hb]; exact initial_bool_agreement bt bc,
      by rw [hu]; exact UintScheduleControls.initial_agreement ut uc⟩
  exact ho.trans (congrArg some he)

private abbrev B : RefTy := .array (.prim .bool)
private abbrev V : RefTy := .array (.prim .uint)
private abbrev PB : RefTy := .fixed (.ref B) 2
private abbrev PU : RefTy := .fixed (.ref V) 2
private abbrev H : HTy := [B,V,V,PB,PU]
private def r : HRef H B := ⟨0,rfl⟩
private def q : HRef H V := ⟨1,rfl⟩
private def neighbor : HRef H V := ⟨2,rfl⟩
private def pr : HRef H PB := ⟨3,rfl⟩
private def pq : HRef H PU := ⟨4,rfl⟩
private def bold (n : Nat) := [true,false,false]++List.replicate n false
private def uold (n : Nat) := [seven,eight,eight]++List.replicate n maximum
private def hp (n : Nat) (hn : n+3<2^256) : Heap H :=
  (⟨bold n,by simp only [bold,List.length_append,List.length_cons,List.length_nil,List.length_replicate]; omega⟩,
    ⟨uold n,by simp only [uold,List.length_append,List.length_cons,List.length_nil,List.length_replicate]; omega⟩,
    ⟨[zero,maximum,one],by decide⟩,⟨[r,r],rfl⟩,⟨[q,q],rfl⟩,())
private theorem blen (n : Nat) (hn : n+3<2^256) : (hp n hn).len r .dyn=n+3 := by
  simp only [Heap.len,Heap.get,Objs.get,hp,r,MObj.elems_dyn,bold,List.length_append,List.length_cons,List.length_nil,List.length_replicate]; omega
private theorem ulen (n : Nat) (hn : n+3<2^256) : (hp n hn).len q .dyn=n+3 := by
  simp only [Heap.len,Heap.get,Objs.get,hp,q,MObj.elems_dyn,uold,List.length_append,List.length_cons,List.length_nil,List.length_replicate]; omega

theorem runtime (n bc uc : Nat) (hn : n+3<2^256) :
    checkedMixedCaptures input 7 input 9 (hp n hn) r .dyn 0 1 1 q .dyn 0 1 1 (repairs bc) (repairs uc)=some (hp n hn) :=
  fixture_restore _ r .dyn q .dyn _ _ (by simp only [MObj.elems_dyn]; rfl) (by simp only [MObj.elems_dyn]; rfl) bc uc

/-- Complete ordered vectors for INITIAL, afterBoolDecode, afterUintDecode,
afterBoolSchedule, FINAL; neighbors and both repeated-reference parents at EACH. -/
theorem ordered (n bc uc : Nat) (hn : n+3<2^256) :
    ∃ bm ini mid, checkedCalldataBools input 7 (hp n hn) r .dyn 0 1 1=some bm ∧
      checkedCalldataUints input 9 bm q .dyn 0 1 1=some ini ∧
      runCaptures ini r .dyn (repairs bc)=some mid ∧ runCaptures mid q .dyn (repairs uc)=some (hp n hn) ∧
      [MObj.elems .dyn ((hp n hn).get r),MObj.elems .dyn (bm.get r),MObj.elems .dyn (ini.get r),MObj.elems .dyn (mid.get r),MObj.elems .dyn ((hp n hn).get r)] =
        [bold n,[true,true,false]++List.replicate n false,[true,true,false]++List.replicate n false,bold n,bold n] ∧
      [MObj.elems .dyn ((hp n hn).get q),MObj.elems .dyn (bm.get q),MObj.elems .dyn (ini.get q),MObj.elems .dyn (mid.get q),MObj.elems .dyn ((hp n hn).get q)] =
        [uold n,uold n,[seven,nine,eight]++List.replicate n maximum,[seven,nine,eight]++List.replicate n maximum,uold n] ∧
      ∀ h ∈ [hp n hn,bm,ini,mid,hp n hn],
        MObj.elems .dyn (h.get neighbor)=[zero,maximum,one] ∧
        (MObj.elems .fixed (h.get pr)).map HRef.id=[0,0] ∧
        (MObj.elems .fixed (h.get pq)).map HRef.id=[1,1] := by
  obtain ⟨bm,ini,mid,hb,hu,hs,hsu⟩ := (checkedMixedCaptures_some _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).mp (runtime n bc uc hn)
  have hi := (checkedBoolUintSequence_some_iff input 7 input 9 (hp n hn) r .dyn 0 1 1 q .dyn 0 1 1 ini).mpr ⟨bm,hb,hu⟩
  have bmB : MObj.elems .dyn (bm.get r)=[true,true,false]++List.replicate n false := by
    rw [checkedCalldataBools_elems input_bool _ _ _ _ _ _ _ hb,input_bools_values]
    simp only [MObj.elems_dyn]; rfl
  have bmU : MObj.elems .dyn (bm.get q)=uold n := by
    rw [checkedCalldataBools_frame input_bool _ _ _ _ _ _ _ hb q (by decide)]
    simp only [MObj.elems_dyn]; rfl
  have iniObs := checkedBoolUintSequence_elems input_bool input_uint (hp n hn) r .dyn 0 1 1 q .dyn 0 1 1 ini hi
  have iniB : MObj.elems .dyn (ini.get r)=[true,true,false]++List.replicate n false := by
    rw [iniObs.1,input_bools_values]; simp only [MObj.elems_dyn]; rfl
  have iniU : MObj.elems .dyn (ini.get q)=[seven,nine,eight]++List.replicate n maximum := by
    rw [iniObs.2,input_uints_values]; simp only [MObj.elems_dyn]; rfl
  have midB : MObj.elems .dyn (mid.get r)=bold n := by
    apply List.ext_getElem?
    intro k
    rw [runCaptures_read ini mid r .dyn (repairs bc) hs k,iniB,repairs_origin]
    cases k with
    | zero => rfl
    | succ k =>
      cases k with
      | zero => rfl
      | succ k => rw [if_neg (by omega)]; rfl
  have midU : MObj.elems .dyn (mid.get q)=[seven,nine,eight]++List.replicate n maximum := by
    rw [runCaptures_frame ini mid r .dyn (repairs bc) hs q (by decide),iniU]
  refine ⟨bm,ini,mid,hb,hu,hs,hsu,?_,?_,?_⟩
  · rw [bmB,iniB,midB]; simp only [MObj.elems_dyn]; rfl
  · rw [bmU,iniU,midU]; simp only [MObj.elems_dyn]; rfl
  · have obs (h : Heap H) (hnbr : h.get neighbor=(hp n hn).get neighbor)
        (hr : h.get pr=(hp n hn).get pr) (hq : h.get pq=(hp n hn).get pq) :
        MObj.elems .dyn (h.get neighbor)=[zero,maximum,one] ∧
        (MObj.elems .fixed (h.get pr)).map HRef.id=[0,0] ∧ (MObj.elems .fixed (h.get pq)).map HRef.id=[1,1] := by
      rw [hnbr,hr,hq]
      simp only [MObj.elems_dyn,MObj.elems_fixed]
      exact ⟨rfl,rfl,rfl⟩
    have obm := obs bm (checkedCalldataBools_frame input_bool _ _ _ _ _ _ _ hb neighbor (by decide))
      (checkedCalldataBools_frame input_bool _ _ _ _ _ _ _ hb pr (by decide))
      (checkedCalldataBools_frame input_bool _ _ _ _ _ _ _ hb pq (by decide))
    have oini := obs ini (checkedBoolUintSequence_frame input_bool input_uint _ _ _ _ _ _ _ _ _ _ _ ini hi neighbor (by decide) (by decide))
      (checkedBoolUintSequence_frame input_bool input_uint _ _ _ _ _ _ _ _ _ _ _ ini hi pr (by decide) (by decide))
      (checkedBoolUintSequence_frame input_bool input_uint _ _ _ _ _ _ _ _ _ _ _ ini hi pq (by decide) (by decide))
    have omid := obs mid
      ((runCaptures_frame ini mid r .dyn (repairs bc) hs neighbor (by decide)).trans
        (checkedBoolUintSequence_frame input_bool input_uint _ _ _ _ _ _ _ _ _ _ _ ini hi neighbor (by decide) (by decide)))
      ((runCaptures_frame ini mid r .dyn (repairs bc) hs pr (by decide)).trans
        (checkedBoolUintSequence_frame input_bool input_uint _ _ _ _ _ _ _ _ _ _ _ ini hi pr (by decide) (by decide)))
      ((runCaptures_frame ini mid r .dyn (repairs bc) hs pq (by decide)).trans
        (checkedBoolUintSequence_frame input_bool input_uint _ _ _ _ _ _ _ _ _ _ _ ini hi pq (by decide) (by decide)))
    intro h hh
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hh
    rcases hh with rfl | rfl | rfl | rfl | rfl
    · exact obs _ rfl rfl rfl
    · exact obm
    · exact oini
    · exact omid
    · exact obs _ rfl rfl rfl

private abbrev FB : RefTy := .fixed (.prim .bool) 3
private abbrev FU : RefTy := .fixed (.prim .uint) 3
private def fr : HRef [FB,FU] FB := ⟨0,rfl⟩
private def fq : HRef [FB,FU] FU := ⟨1,rfl⟩
private def fhp : Heap [FB,FU] := (⟨[true,false,false],rfl⟩,⟨[seven,eight,eight],rfl⟩,())
theorem fixed_runtime (bc uc : Nat) :
    checkedMixedCaptures input 7 input 9 fhp fr .fixed 0 1 1 fq .fixed 0 1 1 (repairs bc) (repairs uc)=some fhp :=
  fixture_restore _ fr .fixed fq .fixed [] [] (by simp only [MObj.elems_fixed]; rfl)
    (by simp only [MObj.elems_fixed]; rfl) bc uc

private theorem some_fixture (n : Nat) (hn : n+3<2^256) (bs us : List SnapshotArgs)
    (hb : CapturesValid (n+3) bs) (hu : CapturesValid (n+3) us) :
    ∃ out, checkedMixedCaptures input 7 input 9 (hp n hn) r .dyn 0 1 1 q .dyn 0 1 1 bs us=some out := by
  apply (checkedMixedCaptures_success_lookup input 7 input 9 (hp n hn) r .dyn 0 1 1 q .dyn 0 1 1 bs us).mpr
  refine ⟨[true],[nine],lookupB,lookupU,⟨by decide,by decide⟩,?_,⟨by decide,by decide⟩,?_,?_,?_⟩
  · rw [blen]; omega
  · rw [ulen]; omega
  · rw [blen]; exact hb
  · rw [ulen]; exact hu

private theorem computed_reads (n : Nat) (hn : n+3<2^256) (bs us : List SnapshotArgs) (out : Heap H)
    (ho : checkedMixedCaptures input 7 input 9 (hp n hn) r .dyn 0 1 1 q .dyn 0 1 1 bs us=some out) :
    (∀ k, (MObj.elems .dyn (out.get r))[k]?=([true,true,false]++List.replicate n false)[captureOrigin bs k]?) ∧
    (∀ k, (MObj.elems .dyn (out.get q))[k]?=([seven,nine,eight]++List.replicate n maximum)[captureOrigin us k]?) := by
  obtain ⟨pb,pu,hpb,hpu,hbr,hur⟩ := checkedMixedCaptures_read _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ho
  have eb : pb=[true] := Option.some.inj (hpb.symm.trans lookupB)
  have eu : pu=[nine] := Option.some.inj (hpu.symm.trans lookupU)
  subst pb; subst pu
  constructor
  · intro k
    rw [hbr k]; simp only [MObj.elems_dyn]; rfl
  · intro k
    rw [hur k]; simp only [MObj.elems_dyn]; rfl

private theorem other_observations (n : Nat) (hn : n+3<2^256) (bs us : List SnapshotArgs) (out : Heap H)
    (ho : checkedMixedCaptures input 7 input 9 (hp n hn) r .dyn 0 1 1 q .dyn 0 1 1 bs us=some out) :
    MObj.elems .dyn (out.get neighbor)=[zero,maximum,one] ∧
    (MObj.elems .fixed (out.get pr)).map HRef.id=[0,0] ∧
    (MObj.elems .fixed (out.get pq)).map HRef.id=[1,1] := by
  rw [checkedMixedCaptures_frame _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ho neighbor (by decide) (by decide),
      checkedMixedCaptures_frame _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ho pr (by decide) (by decide),
      checkedMixedCaptures_frame _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ho pq (by decide) (by decide)]
  simp only [MObj.elems_dyn,MObj.elems_fixed]; exact ⟨rfl,rfl,rfl⟩

/-- Successful selective nonrestoration retains the FINAL uint observations;
only Bool repair is omitted. Not an Option rejection or assumed postrelation. -/
theorem skipped_bool (n uc : Nat) (hn : n+3<2^256) :
    ∃ out, checkedMixedCaptures input 7 input 9 (hp n hn) r .dyn 0 1 1 q .dyn 0 1 1 [] (repairs uc)=some out ∧
      MObj.elems .dyn (out.get r)=[true,true,false]++List.replicate n false ∧
      MObj.elems .dyn (out.get q)=uold n ∧ out ≠ hp n hn ∧
      MObj.elems .dyn (out.get neighbor)=[zero,maximum,one] ∧
      (MObj.elems .fixed (out.get pr)).map HRef.id=[0,0] ∧ (MObj.elems .fixed (out.get pq)).map HRef.id=[1,1] := by
  obtain ⟨out,ho⟩ := some_fixture n hn [] (repairs uc) (fun x hx => by cases hx) (repairs_valid _ uc (by omega))
  have hr := computed_reads n hn [] (repairs uc) out ho
  have hb : MObj.elems .dyn (out.get r)=[true,true,false]++List.replicate n false := List.ext_getElem? hr.1
  have hu : MObj.elems .dyn (out.get q)=uold n := by
    apply List.ext_getElem?
    intro k
    rw [hr.2 k,repairs_origin]
    cases k with
    | zero => rfl
    | succ k =>
      cases k with
      | zero => rfl
      | succ k => rw [if_neg (by omega)]; rfl
  refine ⟨out,ho,hb,hu,?_,(other_observations n hn _ _ out ho).1,
    (other_observations n hn _ _ out ho).2.1,(other_observations n hn _ _ out ho).2.2⟩
  intro he
  have hv := congrArg (fun h : Heap H => (MObj.elems .dyn (h.get r))[1]?) he
  dsimp only at hv
  rw [hb] at hv
  simp only [MObj.elems_dyn] at hv
  change (some true : Option Bool)=some false at hv
  cases hv

/-- Later Boolean rejection follows both real decoded calls AND a nonempty
successful Bool prefix; the Uint schedule has no fabricated suffix heap. -/
theorem late_bool_failure (n : Nat) (hn : n+3<2^256) :
    ∃ bm ini mid, checkedCalldataBools input 7 (hp n hn) r .dyn 0 1 1=some bm ∧
      checkedCalldataUints input 9 bm q .dyn 0 1 1=some ini ∧
      runCaptures ini r .dyn (repairs 0)=some mid ∧
      checkedCaptureOverwrite mid r .dyn r .dyn 0 1 (n+3)=none ∧
      checkedMixedCaptures input 7 input 9 (hp n hn) r .dyn 0 1 1 q .dyn 0 1 1
        [UintScheduleControls.repair,(0,1,n+3),UintScheduleControls.repair] (repairs 0)=none ∧
      MObj.elems .dyn (mid.get r)=bold n ∧ MObj.elems .dyn (mid.get q)=[seven,nine,eight]++List.replicate n maximum := by
  obtain ⟨bm,ini,mid,hb,hu,hs,hsu⟩ := (checkedMixedCaptures_some _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).mp (runtime n 0 0 hn)
  have hi := (checkedBoolUintSequence_some_iff input 7 input 9 (hp n hn) r .dyn 0 1 1 q .dyn 0 1 1 ini).mpr ⟨bm,hb,hu⟩
  have hlen : mid.len r .dyn=n+3 := by
    rw [runCaptures_all_len ini mid r .dyn (repairs 0) hs r .dyn,
      mixedInitialization_all_len input 7 input 9 (hp n hn) r .dyn 0 1 1 q .dyn 0 1 1 ini hi r .dyn,blen]
  have hbad : checkedCaptureOverwrite mid r .dyn r .dyn 0 1 (n+3)=none := by
    rw [checkedCaptureOverwrite_none_iff,hlen]; omega
  have hbval : MObj.elems .dyn (mid.get r)=bold n := by
    have hfinal := runCaptures_frame mid (hp n hn) q .dyn (repairs 0) hsu r (by decide)
    rw [← hfinal]; simp only [MObj.elems_dyn]; rfl
  have huval : MObj.elems .dyn (mid.get q)=[seven,nine,eight]++List.replicate n maximum := by
    rw [runCaptures_frame ini mid r .dyn (repairs 0) hs q (by decide)]
    rw [(checkedBoolUintSequence_elems input_bool input_uint _ _ _ _ _ _ _ _ _ _ _ ini hi).2,input_uints_values]
    simp only [MObj.elems_dyn]; rfl
  refine ⟨bm,ini,mid,hb,hu,hs,hbad,?_,hbval,huval⟩
  apply (checkedMixedCaptures_none_first _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).mpr
  exact Or.inr ⟨ini,hi,Or.inl ⟨[UintScheduleControls.repair],(0,1,n+3),[UintScheduleControls.repair],mid,rfl,hs,hbad⟩⟩

/-- Uint rejection follows the COMPLETE real Bool schedule and a nonempty
successful Uint prefix. Both reached destinations are already restored. -/
theorem late_uint_failure (n : Nat) (hn : n+3<2^256) :
    ∃ bm ini mid, checkedCalldataBools input 7 (hp n hn) r .dyn 0 1 1=some bm ∧
      checkedCalldataUints input 9 bm q .dyn 0 1 1=some ini ∧
      runCaptures ini r .dyn (repairs 0)=some mid ∧ runCaptures mid q .dyn (repairs 0)=some (hp n hn) ∧
      checkedCaptureOverwrite (hp n hn) q .dyn q .dyn 0 1 (n+3)=none ∧
      checkedMixedCaptures input 7 input 9 (hp n hn) r .dyn 0 1 1 q .dyn 0 1 1 (repairs 0)
        [UintScheduleControls.repair,(0,1,n+3),UintScheduleControls.repair]=none := by
  obtain ⟨bm,ini,mid,hb,hu,hs,hsu⟩ := (checkedMixedCaptures_some _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).mp (runtime n 0 0 hn)
  have hi := (checkedBoolUintSequence_some_iff input 7 input 9 (hp n hn) r .dyn 0 1 1 q .dyn 0 1 1 ini).mpr ⟨bm,hb,hu⟩
  have hbad : checkedCaptureOverwrite (hp n hn) q .dyn q .dyn 0 1 (n+3)=none := by
    rw [checkedCaptureOverwrite_none_iff,ulen]; omega
  refine ⟨bm,ini,mid,hb,hu,hs,hsu,hbad,?_⟩
  apply (checkedMixedCaptures_none_first _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).mpr
  exact Or.inr ⟨ini,hi,Or.inr ⟨mid,hs,[UintScheduleControls.repair],(0,1,n+3),[UintScheduleControls.repair],hp n hn,rfl,hsu,hbad⟩⟩

/-- Initial Bool failures short-circuit. Uint failures are observed on the
REAL successful Bool output; all eight full results retain adapter None only. -/
theorem initial_failures (n : Nat) (hn : n+3<2^256) :
    ∃ bm, checkedCalldataBools input 7 (hp n hn) r .dyn 0 1 1=some bm ∧
      [checkedCalldataUints input 10 bm q .dyn 0 1 1,
       checkedCalldataUints input 9 bm q .dyn 1 0 0,
       checkedCalldataUints input 9 bm q .dyn 0 2 0,
       checkedCalldataUints input 9 bm q .dyn 0 1 (n+3)]=List.replicate 4 none ∧
      [checkedMixedCaptures input 8 input 9 (hp n hn) r .dyn 0 1 1 q .dyn 0 1 1 (repairs 0) (repairs 0),
       checkedMixedCaptures input 7 input 9 (hp n hn) r .dyn 1 0 0 q .dyn 0 1 1 (repairs 0) (repairs 0),
       checkedMixedCaptures input 7 input 9 (hp n hn) r .dyn 0 2 0 q .dyn 0 1 1 (repairs 0) (repairs 0),
       checkedMixedCaptures input 7 input 9 (hp n hn) r .dyn 0 1 (n+3) q .dyn 0 1 1 (repairs 0) (repairs 0),
       checkedMixedCaptures input 7 input 10 (hp n hn) r .dyn 0 1 1 q .dyn 0 1 1 (repairs 0) (repairs 0),
       checkedMixedCaptures input 7 input 9 (hp n hn) r .dyn 0 1 1 q .dyn 1 0 0 (repairs 0) (repairs 0),
       checkedMixedCaptures input 7 input 9 (hp n hn) r .dyn 0 1 1 q .dyn 0 2 0 (repairs 0) (repairs 0),
       checkedMixedCaptures input 7 input 9 (hp n hn) r .dyn 0 1 1 q .dyn 0 1 (n+3) (repairs 0) (repairs 0)]=List.replicate 8 none := by
  obtain ⟨bm,ini,mid,hb,hu,hs,hsu⟩ := (checkedMixedCaptures_some _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).mp (runtime n 0 0 hn)
  have b0 : checkedCalldataBools input 8 (hp n hn) r .dyn 0 1 1=none := by rfl
  have b1 := (checkedCalldataBools_none_iff input_bool (hp n hn) r .dyn 1 0 0).mpr (Or.inl (by decide))
  have b2 := (checkedCalldataBools_none_iff input_bool (hp n hn) r .dyn 0 2 0).mpr (Or.inr (Or.inl (by decide)))
  have b3 := (checkedCalldataBools_none_iff input_bool (hp n hn) r .dyn 0 1 (n+3)).mpr (Or.inr (Or.inr (by rw [blen]; omega)))
  have u0 : checkedCalldataUints input 10 bm q .dyn 0 1 1=none := by rfl
  have u1 := (checkedCalldataUints_none_iff input_uint bm q .dyn 1 0 0).mpr (Or.inl (by decide))
  have u2 := (checkedCalldataUints_none_iff input_uint bm q .dyn 0 2 0).mpr (Or.inr (Or.inl (by decide)))
  have u3 := (checkedCalldataUints_none_iff input_uint bm q .dyn 0 1 (n+3)).mpr
    (Or.inr (Or.inr (by rw [boolTransfer_all_len input 7 (hp n hn) r .dyn 0 1 1 bm hb q .dyn,ulen]; omega)))
  refine ⟨bm,hb,?_,?_⟩
  · rw [u0,u1,u2,u3]; rfl
  · simp only [checkedMixedCaptures,checkedBoolUintSequence,b0,b1,b2,b3,hb,u0,u1,u2,u3,Option.bind_none,Option.bind_some]
    rfl

private theorem changed_valid (size : Nat) (hsize : 3 ≤ size) : CapturesValid size [(1,2,0)] := by
  intro x hx
  have he : x=(1,2,0) := by simpa only [List.mem_cons,List.not_mem_nil,or_false] using hx
  subst x
  change 1 ≤ 2 ∧ 2 ≤ size ∧ 0+(2-1) ≤ size
  omega

/-- BOTH schedules read their actually decoded changed index1. Frozen INITIAL
reads false/8 produce different BOTH destination vectors; no frozen evaluator. -/
theorem changed_source (n : Nat) (hn : n+3<2^256) :
    ∃ out frozen : Heap H,
      checkedMixedCaptures input 7 input 9 (hp n hn) r .dyn 0 1 1 q .dyn 0 1 1 [(1,2,0)] [(1,2,0)]=some out ∧
      MObj.elems .dyn (out.get r)=[true,true,false]++List.replicate n false ∧
      MObj.elems .dyn (out.get q)=[nine,nine,eight]++List.replicate n maximum ∧
      MObj.elems .dyn (frozen.get r)=[false,true,false]++List.replicate n false ∧
      MObj.elems .dyn (frozen.get q)=[eight,nine,eight]++List.replicate n maximum ∧
      MObj.elems .dyn (out.get neighbor)=[zero,maximum,one] ∧
      (MObj.elems .fixed (out.get pr)).map HRef.id=[0,0] ∧
      (MObj.elems .fixed (out.get pq)).map HRef.id=[1,1] ∧ frozen ≠ out := by
  obtain ⟨out,ho⟩ := some_fixture n hn _ _ (changed_valid _ (by omega)) (changed_valid _ (by omega))
  have hr := computed_reads n hn _ _ out ho
  have origin (k : Nat) : snapshotOrigin (1,2,0) (k+1)=k+1 := by
    unfold snapshotOrigin
    change (if 0 ≤ k+1 ∧ k+1 < 0+(2-1) then 1+(k+1-0) else k+1)=k+1
    rw [if_neg (by omega)]
  have outB : MObj.elems .dyn (out.get r)=[true,true,false]++List.replicate n false := by
    apply List.ext_getElem?
    intro k
    rw [hr.1 k]
    change ([true,true,false]++List.replicate n false)[snapshotOrigin (1,2,0) k]?=([true,true,false]++List.replicate n false)[k]?
    cases k with
    | zero => rfl
    | succ k => rw [origin]
  have outU : MObj.elems .dyn (out.get q)=[nine,nine,eight]++List.replicate n maximum := by
    apply List.ext_getElem?
    intro k
    rw [hr.2 k]
    change ([seven,nine,eight]++List.replicate n maximum)[snapshotOrigin (1,2,0) k]?=([nine,nine,eight]++List.replicate n maximum)[k]?
    cases k with
    | zero => rfl
    | succ k => rw [origin]; rfl
  obtain ⟨bm,ini,mid,hb,hu,hs,hsu⟩ := (checkedMixedCaptures_some _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).mp ho
  have hi := (checkedBoolUintSequence_some_iff input 7 input 9 (hp n hn) r .dyn 0 1 1 q .dyn 0 1 1 ini).mpr ⟨bm,hb,hu⟩
  have iniObs := checkedBoolUintSequence_elems input_bool input_uint (hp n hn) r .dyn 0 1 1 q .dyn 0 1 1 ini hi
  have iniB : MObj.elems .dyn (ini.get r)=[true,true,false]++List.replicate n false := by
    rw [iniObs.1,input_bools_values]; simp only [MObj.elems_dyn]; rfl
  have iniU : MObj.elems .dyn (ini.get q)=[seven,nine,eight]++List.replicate n maximum := by
    rw [iniObs.2,input_uints_values]; simp only [MObj.elems_dyn]; rfl
  have capB : 0+[false].length ≤ ini.len r .dyn := by
    rw [mixedInitialization_all_len input 7 input 9 (hp n hn) r .dyn 0 1 1 q .dyn 0 1 1 ini hi r .dyn,blen]
    change 0+1 ≤ n+3; omega
  have capU : 0+[eight].length ≤ ini.len q .dyn := by
    rw [mixedInitialization_all_len input 7 input 9 (hp n hn) r .dyn 0 1 1 q .dyn 0 1 1 ini hi q .dyn,ulen]
    change 0+1 ≤ n+3; omega
  let frozen := overwriteTwo ini r .dyn 0 [false] capB q .dyn 0 [eight] capU (bool_uint_transfer_ne r .dyn q .dyn)
  have frozenB : MObj.elems .dyn (frozen.get r)=[false,true,false]++List.replicate n false := by
    dsimp only [frozen]
    rw [overwriteTwo_first,overwriteSlice_elems,iniB]; rfl
  have frozenU : MObj.elems .dyn (frozen.get q)=[eight,nine,eight]++List.replicate n maximum := by
    dsimp only [frozen,overwriteTwo]
    rw [overwriteSlice_elems,overwriteSlice_frame ini r q .dyn 0 [false] capB (bool_uint_transfer_ne r .dyn q .dyn),iniU]; rfl
  refine ⟨out,frozen,ho,outB,outU,frozenB,frozenU,(other_observations n hn _ _ out ho).1,
    (other_observations n hn _ _ out ho).2.1,(other_observations n hn _ _ out ho).2.2,?_⟩
  intro he
  have hv := congrArg (fun h : Heap H => (MObj.elems .dyn (h.get r))[0]?) he
  dsimp only at hv
  rw [frozenB,outB] at hv
  change (some false : Option Bool)=some true at hv
  cases hv

/-- Directly exercise BOTH new source-read laws at provenance origins inside
actual decoded footprints, after changed-source recapture. -/
theorem source_reads (n : Nat) (hn : n+3<2^256) :
    ∃ out, checkedMixedCaptures input 7 input 9 (hp n hn) r .dyn 0 1 1 q .dyn 0 1 1 [(1,2,0)] [(1,2,0)]=some out ∧
      (∃ bv, (MObj.elems .dyn (out.get r))[0]?=some bv ∧ DecodedArrayRead input 7 .bool none 0 (.val (.bool bv))) ∧
      (∃ uv, (MObj.elems .dyn (out.get q))[0]?=some uv ∧ DecodedArrayRead input 9 (.int .u256) none 0 (.val (sourceUint uv))) := by
  obtain ⟨out,frozen,ho,hrest⟩ := changed_source n hn
  exact ⟨out,ho,checkedMixedCaptures_bool_source _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ input_bool _ _ out ho 0 (by decide),
    checkedMixedCaptures_uint_source _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ input_uint _ _ out ho 0 (by decide)⟩

theorem empty_end (n : Nat) (hn : n+3<2^256) :
    checkedMixedCaptures input 7 input 9 (hp n hn) r .dyn 1 1 (n+3) q .dyn 1 1 (n+3) [] []=some (hp n hn) ∧
    checkedMixedCaptures input 7 input 9 (hp n hn) r .dyn 1 1 (n+3) q .dyn 1 1 (n+3)
      [(n+3,n+3,n+3)] [(n+3,n+3,n+3)]=some (hp n hn) := by
  have hi : checkedBoolUintSequence input 7 input 9 (hp n hn) r .dyn 1 1 (n+3) q .dyn 1 1 (n+3)=some (hp n hn) := by
    have h := checkedBoolUintSequence_checked input_bool input_uint (hp n hn) r .dyn 1 1 (n+3) q .dyn 1 1 (n+3)
      ⟨by decide,by decide⟩ (by rw [blen]; omega) ⟨by decide,by decide⟩ (by rw [ulen]; omega)
    simpa only [Nat.sub_self,List.take_zero,overwriteTwo,overwriteSlice_empty] using h
  have endB : checkedCaptureOverwrite (hp n hn) r .dyn r .dyn (n+3) (n+3) (n+3)=some (hp n hn) := by
    have h := checkedCaptureOverwrite_some (hp n hn) r .dyn r .dyn (n+3) (n+3) (n+3)
      ⟨Nat.le_refl _,by rw [blen]; exact Nat.le_refl _⟩ (by rw [blen]; omega)
    simpa only [captureOverwrite,sliceElems,Nat.sub_self,List.take_zero,overwriteSlice_empty] using h
  have endU : checkedCaptureOverwrite (hp n hn) q .dyn q .dyn (n+3) (n+3) (n+3)=some (hp n hn) := by
    have h := checkedCaptureOverwrite_some (hp n hn) q .dyn q .dyn (n+3) (n+3) (n+3)
      ⟨Nat.le_refl _,by rw [ulen]; exact Nat.le_refl _⟩ (by rw [ulen]; omega)
    simpa only [captureOverwrite,sliceElems,Nat.sub_self,List.take_zero,overwriteSlice_empty] using h
  simp only [checkedMixedCaptures,hi,Option.bind_some,runCaptures,endB,endU,and_self]

private abbrev ANew : RefTy := .array (.ref B)
private def obj : MObj H ANew := ⟨[r,r],by decide⟩
private def e := List.prefix_append H [ANew]
/-- Direct new Keeps application to ACTUAL INITIAL Heap.alloc; complete both
old arrays, neighbor and old/fresh alias parents remain observed. -/
theorem initial_allocation (n bc uc : Nat) (hn : n+3<2^256) :
    ∃ out, checkedMixedCaptures input 7 input 9 ((hp n hn).alloc obj).1 (r.wk e) .dyn 0 1 1 (q.wk e) .dyn 0 1 1
        (repairs bc) (repairs uc)=some out ∧ Heap.Keeps e (hp n hn) out ∧
      MObj.elems .dyn (out.get (r.wk e))=bold n ∧ MObj.elems .dyn (out.get (q.wk e))=uold n ∧
      MObj.elems .dyn (out.get (neighbor.wk e))=[zero,maximum,one] ∧
      (MObj.elems .fixed (out.get (pr.wk e))).map HRef.id=[0,0] ∧
      (MObj.elems .fixed (out.get (pq.wk e))).map HRef.id=[1,1] ∧
      (MObj.elems .dyn (out.get ((hp n hn).alloc obj).2)).map HRef.id=[0,0] ∧ ((hp n hn).alloc obj).2.id=5 := by
  obtain ⟨out,ho,hk⟩ := checkedMixedCaptures_keeps input_bool input_uint e (Heap.keeps_alloc (hp n hn) obj)
    r .dyn 0 1 1 q .dyn 0 1 1 _ _ (hp n hn) (runtime n bc uc hn)
  refine ⟨out,ho,hk,?_,?_,?_,?_,?_,?_,rfl⟩
  · rw [hk r,MObj.elems_wk,List.map_id'' (f:=MVal.wk e (.prim .bool)) (fun _ => rfl)]
    simp only [MObj.elems_dyn]; rfl
  · rw [hk q,MObj.elems_wk,List.map_id'' (f:=MVal.wk e (.prim .uint)) (fun _ => rfl)]
    simp only [MObj.elems_dyn]; rfl
  · rw [hk neighbor,MObj.elems_wk,List.map_id'' (f:=MVal.wk e (.prim .uint)) (fun _ => rfl)]
    simp only [MObj.elems_dyn]; rfl
  · rw [hk pr,MObj.elems_wk,List.map_map]; simp only [MObj.elems_fixed]; rfl
  · rw [hk pq,MObj.elems_wk,List.map_map]; simp only [MObj.elems_fixed]; rfl
  · rw [checkedMixedCaptures_frame _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ho ((hp n hn).alloc obj).2
      (old_ne_fresh (hp n hn) obj r) (old_ne_fresh (hp n hn) obj q),Heap.get_alloc,MObj.elems_wk,List.map_map]
    simp only [MObj.elems_dyn]; rfl

/-- Allocation is on the REAL both-decoded changed heap. Both actual schedules
then repair old arrays, while the fresh parent retains the changed child's ID. -/
theorem interstage_allocation (n bc uc : Nat) (hn : n+3<2^256) :
    ∃ ini mid out, checkedBoolUintSequence input 7 input 9 (hp n hn) r .dyn 0 1 1 q .dyn 0 1 1=some ini ∧
      MObj.elems .dyn (ini.get r)=[true,true,false]++List.replicate n false ∧
      MObj.elems .dyn (ini.get q)=[seven,nine,eight]++List.replicate n maximum ∧
      runCaptures (ini.alloc obj).1 (r.wk e) .dyn (repairs bc)=some mid ∧
      runCaptures mid (q.wk e) .dyn (repairs uc)=some out ∧
      MObj.elems .dyn (out.get (r.wk e))=bold n ∧ MObj.elems .dyn (out.get (q.wk e))=uold n ∧
      MObj.elems .dyn (out.get (neighbor.wk e))=[zero,maximum,one] ∧
      (MObj.elems .dyn (out.get (ini.alloc obj).2)).map HRef.id=[0,0] ∧ (ini.alloc obj).2.id=5 := by
  obtain ⟨ini,mid,out,hi,hs,hsu,hk,hfresh⟩ := checkedMixedCaptures_alloc input 7 input 9 (hp n hn)
    r .dyn 0 1 1 q .dyn 0 1 1 _ _ (hp n hn) (runtime n bc uc hn) obj
  have iniObs := checkedBoolUintSequence_elems input_bool input_uint (hp n hn) r .dyn 0 1 1 q .dyn 0 1 1 ini hi
  refine ⟨ini,mid,out,hi,?_,?_,hs,hsu,?_,?_,?_,?_,rfl⟩
  · rw [iniObs.1,input_bools_values]; simp only [MObj.elems_dyn]; rfl
  · rw [iniObs.2,input_uints_values]; simp only [MObj.elems_dyn]; rfl
  · rw [hk r,MObj.elems_wk,List.map_id'' (f:=MVal.wk e (.prim .bool)) (fun _ => rfl)]
    simp only [MObj.elems_dyn]; rfl
  · rw [hk q,MObj.elems_wk,List.map_id'' (f:=MVal.wk e (.prim .uint)) (fun _ => rfl)]
    simp only [MObj.elems_dyn]; rfl
  · rw [hk neighbor,MObj.elems_wk,List.map_id'' (f:=MVal.wk e (.prim .uint)) (fun _ => rfl)]
    simp only [MObj.elems_dyn]; rfl
  · rw [hfresh,Heap.get_alloc,MObj.elems_wk,List.map_map]; simp only [MObj.elems_dyn]; rfl

private def wordInput (value : U) : Source.Calldata D :=
  ⟨[],fun off => if off=7 then (bools [true]).objects off else (uints [value]).objects off⟩
private theorem word_bool (value : U) : DecodedArrayAt (n:=none) (wordInput value) 7 1 (fun _ h => by cases h)
    (fun i => .val (.bool ([true][i]))) := rfl
private theorem word_uint (value : U) : DecodedArrayAt (n:=none) (wordInput value) 9 1 (fun _ h => by cases h)
    (fun i => .val (sourceUint ([value][i]))) := rfl
private theorem word_values (value : U) : List.ofFn (fun i : Fin 1 => calldataUint
    (Source.Data.val (sourceUint (D:=D) ([value][i]))))=[value] := by
  simpa only [List.ofFn_succ,List.ofFn_zero] using
    congrArg (fun word : U => [word]) (calldataUint_sourceUint (D:=D) value)

/-- Actual mixed decoded input writes ANY existing uint value, including zero
and maximum. No common encoding or numeric truncation is assumed. -/
theorem decoded_word (n : Nat) (hn : n+3<2^256) (value : U) :
    ∃ out, checkedMixedCaptures (wordInput value) 7 (wordInput value) 9 (hp n hn) r .dyn 0 1 1 q .dyn 0 1 1 [] []=some out ∧
      MObj.elems .dyn (out.get r)=[true,true,false]++List.replicate n false ∧
      MObj.elems .dyn (out.get q)=[seven,value,eight]++List.replicate n maximum ∧
      MObj.elems .dyn (out.get neighbor)=[zero,maximum,one] := by
  have lB : calldataBools (wordInput value) 7=some [true] := by rw [calldataBools_lookup (word_bool value),input_bools_values]
  have lU : calldataUints (wordInput value) 9=some [value] := by rw [calldataUints_lookup (word_uint value),word_values]
  obtain ⟨out,ho⟩ := (checkedMixedCaptures_success_lookup (wordInput value) 7 (wordInput value) 9 (hp n hn)
      r .dyn 0 1 1 q .dyn 0 1 1 [] []).mpr
    ⟨[true],[value],lB,lU,⟨by decide,by decide⟩,by rw [blen]; omega,
      ⟨by decide,by simp only [List.length_cons,List.length_nil]; decide⟩,by rw [ulen]; omega,
      (fun x hx => by cases hx),(fun x hx => by cases hx)⟩
  obtain ⟨pb,pu,hpb,hpu,hr,hu⟩ := checkedMixedCaptures_read _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ho
  have eb : pb=[true] := Option.some.inj (hpb.symm.trans lB)
  have eu : pu=[value] := Option.some.inj (hpu.symm.trans lU)
  subst pb; subst pu
  refine ⟨out,ho,?_,?_,?_⟩
  · apply List.ext_getElem?
    intro k
    rw [hr k]; simp only [MObj.elems_dyn]; rfl
  · apply List.ext_getElem?
    intro k
    rw [hu k]; simp only [MObj.elems_dyn]; rfl
  · rw [checkedMixedCaptures_frame _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ho neighbor (by decide) (by decide)]
    simp only [MObj.elems_dyn]; rfl

theorem zero_maximum (n : Nat) (hn : n+3<2^256) :
    ∃ oz om, checkedMixedCaptures (wordInput zero) 7 (wordInput zero) 9 (hp n hn) r .dyn 0 1 1 q .dyn 0 1 1 [] []=some oz ∧
      checkedMixedCaptures (wordInput maximum) 7 (wordInput maximum) 9 (hp n hn) r .dyn 0 1 1 q .dyn 0 1 1 [] []=some om ∧
      MObj.elems .dyn (oz.get r)=[true,true,false]++List.replicate n false ∧
      MObj.elems .dyn (om.get r)=[true,true,false]++List.replicate n false ∧
      MObj.elems .dyn (oz.get q)=[seven,zero,eight]++List.replicate n maximum ∧
      MObj.elems .dyn (om.get q)=[seven,maximum,eight]++List.replicate n maximum ∧
      MObj.elems .dyn (oz.get neighbor)=[zero,maximum,one] ∧ MObj.elems .dyn (om.get neighbor)=[zero,maximum,one] ∧
      maximum.val=((2^256-1 : Nat) : Int) := by
  obtain ⟨oz,hz,hzB,hzU,hzN⟩ := decoded_word n hn zero
  obtain ⟨om,hm,hmB,hmU,hmN⟩ := decoded_word n hn maximum
  exact ⟨oz,om,hz,hm,hzB,hmB,hzU,hmU,hzN,hmN,rfl⟩

theorem boundary33 :
    checkedMixedCaptures input 7 input 9 (hp 33 (by decide)) r .dyn 0 1 1 q .dyn 0 1 1 (repairs 3) (repairs 4)=some (hp 33 (by decide)) ∧
    (MObj.elems .dyn ((hp 33 (by decide)).get r))[32]?=some false ∧
    (MObj.elems .dyn ((hp 33 (by decide)).get q))[32]?=some maximum := by
  refine ⟨runtime 33 3 4 (by decide),?_,?_⟩
  all_goals simp only [MObj.elems_dyn]; rfl

/-- Lengths of BOTH changed destinations and directly observed fixed-reference
parents are derived by the new all-object law on a nonrestoring actual run. -/
theorem changed_lengths (n : Nat) (hn : n+3<2^256) :
    ∃ out, checkedMixedCaptures input 7 input 9 (hp n hn) r .dyn 0 1 1 q .dyn 0 1 1 [(1,2,0)] [(1,2,0)]=some out ∧
      [out.len r .dyn,out.len q .dyn,out.len neighbor .dyn,out.len pr .fixed,out.len pq .fixed]=[n+3,n+3,3,2,2] := by
  obtain ⟨out,frozen,ho,hrest⟩ := changed_source n hn
  refine ⟨out,ho,?_⟩
  rw [checkedMixedCaptures_all_len _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ho r .dyn,blen,
      checkedMixedCaptures_all_len _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ho q .dyn,ulen,
      checkedMixedCaptures_all_len _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ho neighbor .dyn,
      checkedMixedCaptures_all_len _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ho pr .fixed,
      checkedMixedCaptures_all_len _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ho pq .fixed]
  simp only [Heap.len,MObj.elems_dyn,MObj.elems_fixed]; rfl

/-- info: 'Solidity.Backend.MemoryOps.MixedScheduleControls.input_bool' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms input_bool
/-- info: 'Solidity.Backend.MemoryOps.MixedScheduleControls.input_uint' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms input_uint
/-- info: 'Solidity.Backend.MemoryOps.MixedScheduleControls.repairs_valid' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms repairs_valid
/-- info: 'Solidity.Backend.MemoryOps.MixedScheduleControls.initial_bool_agreement' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms initial_bool_agreement
/-- info: 'Solidity.Backend.MemoryOps.MixedScheduleControls.fixture_restore' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms fixture_restore
/-- info: 'Solidity.Backend.MemoryOps.MixedScheduleControls.runtime' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms runtime
/-- info: 'Solidity.Backend.MemoryOps.MixedScheduleControls.ordered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ordered
/-- info: 'Solidity.Backend.MemoryOps.MixedScheduleControls.fixed_runtime' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms fixed_runtime
/-- info: 'Solidity.Backend.MemoryOps.MixedScheduleControls.skipped_bool' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms skipped_bool
/-- info: 'Solidity.Backend.MemoryOps.MixedScheduleControls.late_bool_failure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms late_bool_failure
/-- info: 'Solidity.Backend.MemoryOps.MixedScheduleControls.late_uint_failure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms late_uint_failure
/-- info: 'Solidity.Backend.MemoryOps.MixedScheduleControls.initial_failures' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms initial_failures
/-- info: 'Solidity.Backend.MemoryOps.MixedScheduleControls.changed_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms changed_source
/-- info: 'Solidity.Backend.MemoryOps.MixedScheduleControls.source_reads' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms source_reads
/-- info: 'Solidity.Backend.MemoryOps.MixedScheduleControls.empty_end' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms empty_end
/-- info: 'Solidity.Backend.MemoryOps.MixedScheduleControls.initial_allocation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms initial_allocation
/-- info: 'Solidity.Backend.MemoryOps.MixedScheduleControls.interstage_allocation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms interstage_allocation
/-- info: 'Solidity.Backend.MemoryOps.MixedScheduleControls.decoded_word' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms decoded_word
/-- info: 'Solidity.Backend.MemoryOps.MixedScheduleControls.zero_maximum' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms zero_maximum
/-- info: 'Solidity.Backend.MemoryOps.MixedScheduleControls.boundary33' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms boundary33
/-- info: 'Solidity.Backend.MemoryOps.MixedScheduleControls.changed_lengths' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms changed_lengths
end Solidity.Backend.MemoryOps.MixedScheduleControls
