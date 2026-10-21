import Solidity.Semantics.Run

/-!
# A byte string allocated is a fresh object of its bytes

`Fml.allocAll` (`Calculus/Fml.lean`) reads a fresh memory object of any
contents: the state `State.allocPush` (the heap grown by the object, its
reference pushed as a new memory local).  The run allocates a byte string a
`catch` clause binds as the statements `litBytes` writes (`new bytes(n)`,
then one write per byte, `TRun.litBytesT`); this module shows that run ends
in `State.allocPush` at the object of the bytes (`TRun.litBytesT_alloc`),
which `catchDataBox`'s goal for another contract's data reads
(`Calculus/SoundCatch.lean`).

The copies and allocations are `@[irreducible]` (`SVal.copyStToM`): the
proofs state each step against an abstract grown heap (`Grown.prims_cons`,
`Grown.alloc_prims_eq`, `State.adopt_push_alloc`), instantiated with the
definitions unfolded (`with_unfolding_all`).
-/

namespace Solidity

variable {C : Contract}

theorem Grown.prims_cons {H : HTy} {p : PrimTy} (hp : Heap H) (v : p.Denote) (l : List p.Denote)
    {n : Nat} (g : Grown H (fun H' => {l : List (MVal H' (.prim p)) // l.length = n}))
    (hl : l.length = n) (hg : g = ⟨List.prefix_refl H, hp, ⟨l, hl⟩⟩) (e : H <+: g.H')
    (e' : H <+: g.H') (q : (MVal.wk e' (.prim p) v :: g.val.1).length = n + 1) :
    (⟨e, g.heap, ⟨MVal.wk e' (.prim p) v :: g.val.1, q⟩⟩ :
        Grown H (fun H' => {l : List (MVal H' (.prim p)) // l.length = n + 1})) =
      ⟨List.prefix_refl H, hp, ⟨v :: l, by rw [List.length_cons, hl]⟩⟩ := by
  subst hg
  rfl

/-- A list of prim words copied: no allocation, the words themselves. -/
theorem SVec.copyStToM_prims {H : HTy} (hp : Heap H) {p : PrimTy} :
    (l : List p.Denote) → (h : (Ty.prim p).mapFree = true) →
      SVec.copyStToM hp (SVec.ofList (l.map fun v => (SVal.prim v : SVal (.prim p)))) h =
        ⟨List.prefix_refl H, hp, ⟨l, by simp⟩⟩
  | [], h => by
    simp only [List.map_nil, SVec.ofList, SVec.copyStToM_nil]
  | v :: l, h => by
    simp only [List.map_cons, SVec.ofList, SVec.copyStToM_cons, SVal.copyStToM_prim]
    with_unfolding_all exact Grown.prims_cons hp v l _ _ (SVec.copyStToM_prims hp l h) _ _ _

end Solidity

namespace Solidity

variable {C : Contract} {Γ : Ctx}

/-- A fresh object `o` of type `R`, its reference pushed as a new memory
local (`Fml.allocAll`'s state). -/
def State.allocPush {R : RefTy} (σ : State C Γ) (o : MObj σ.H R) : State C (.mem R :: Γ) :=
  (σ.alloc o).1.push (t := .mem R) (some (σ.alloc o).2)

/-- `n` zero words: `new bytes(n)`'s object. -/
def zerosObj (H : HTy) (n : Nat) (hn : n < 2 ^ 256) : MObj H bytesR :=
  (⟨List.replicate n (PrimTy.dflt .uint), by rw [List.length_replicate]; exact hn⟩ :
    {l : List (MVal H (.prim .uint)) // l.length < 2 ^ 256})

theorem SVec.copyStToM_prims' {H : HTy} (hp : Heap H) {p : PrimTy}
    (L : List (SVal (.prim p))) (l : List p.Denote) (h : (Ty.prim p).mapFree = true)
    (hL : L = l.map fun v => (SVal.prim v : SVal (.prim p))) :
    SVec.copyStToM hp (SVec.ofList L) h = ⟨List.prefix_refl H, hp, ⟨l, by subst hL; simp⟩⟩ := by
  subst hL; exact SVec.copyStToM_prims hp l h

theorem Grown.alloc_prims_eq {H : HTy} (hp : Heap H) {n : Nat}
    (g : Grown H (fun H' => {l : List (MVal H' (.prim .uint)) // l.length = n}))
    (l : List PrimTy.uint.Denote) (hl : l.length = n) (hn : n < 2 ^ 256)
    (hg : g = ⟨List.prefix_refl H, hp, ⟨l, hl⟩⟩) (q : g.val.1.length < 2 ^ 256) :
    Grown.alloc (R := bytesR) ⟨g.ext, g.heap, ⟨g.val.1, q⟩⟩ =
      Grown.alloc (⟨List.prefix_refl H, hp,
        (⟨l, by rw [hl]; exact hn⟩ : {l : List (MVal H (.prim .uint)) // l.length < 2 ^ 256})⟩ :
          Grown H (MObj · bytesR)) := by
  subst hg; rfl

/-- `new bytes(n)`'s object, copied: one fresh object of `n` zero words. -/
theorem SVal.copyStToM_zeros {H : HTy} (hp : Heap H) (n : Nat) (hn : n < 2 ^ 256)
    (h : (Ty.ref bytesR).mapFree = true) (hk) :
    SVal.copyStToM hp (.array (SVec.ofList (List.replicate n (SVal.dflt (.prim .uint)))) .nil hk) h =
      Grown.alloc ⟨List.prefix_refl H, hp, zerosObj H n hn⟩ := by
  rw [SVal.copyStToM_array]
  have e : List.replicate n (SVal.dflt (.prim .uint)) =
      (List.replicate n (PrimTy.dflt .uint)).map fun v => (SVal.prim v : SVal (.prim .uint)) := by
    rw [List.map_replicate]; rfl
  with_unfolding_all exact (Grown.alloc_prims_eq (n := (List.replicate n
    (SVal.dflt (.prim .uint))).length) hp _ (List.replicate n (PrimTy.dflt .uint))
    (by simp only [List.length_replicate]) hk (SVec.copyStToM_prims' hp _ _ h e) _)

theorem State.adopt_push_alloc {R : RefTy} (σ : State C Γ) (o : MObj σ.H R)
    (G : Grown σ.H (MVal · (.ref R))) (hG : G = Grown.alloc ⟨List.prefix_refl _, σ.heap, o⟩)
    (e : σ.H <+: ((σ.adopt G).1.push (t := .mem R) (some G.val)).H)
    (e' : σ.H <+: (σ.allocPush o).H) :
    (Except.ok (⟨(σ.adopt G).1.push (t := .mem R) (some G.val), e⟩ : Out C σ.H (.mem R :: Γ)) :
      TRes (Out C σ.H (.mem R :: Γ))) = .ok ⟨σ.allocPush o, e'⟩ := by
  subst hG; rfl

theorem TRun.declMem_newArr_bytes (σ : State C Γ) (n : Nat) (hn : n < 2 ^ 256) :
    TRun.declMem bytesR (some (.newArr (.lit (n : Int) (PrimTy.inRange_uint_of_lt hn)) rfl))
      rfl σ = .ok ⟨σ.allocPush (zerosObj σ.H n hn), List.prefix_append _ _⟩ := by
  simp only [TRun.declMem, MRhs.evalT, State.copyStToMG, State.grow, newArrT, bind, Except.bind,
    pure, Except.pure]
  with_unfolding_all exact State.adopt_push_alloc σ _ _ (SVal.copyStToM_zeros σ.heap n hn _ _) _ _

end Solidity

namespace Solidity

theorem Objs.get_snoc_top {H : HTy} {R : RefTy} (o : MObj H R) :
    (Rs : List RefTy) → (os : Objs H Rs) → (h : (Rs ++ [R])[Rs.length]? = some R) →
      Objs.get (Rs ++ [R]) (Objs.snoc o Rs os) Rs.length h = o
  | [], _, _ => rfl
  | _ :: Rs, os, _ => Objs.get_snoc_top o Rs os.2 _

theorem Objs.set_snoc_top {H : HTy} {R : RefTy} (o o' : MObj H R) :
    (Rs : List RefTy) → (os : Objs H Rs) → (h : (Rs ++ [R])[Rs.length]? = some R) →
      Objs.set (Rs ++ [R]) (Objs.snoc o Rs os) Rs.length h o' = Objs.snoc o' Rs os
  | [], _, _ => rfl
  | _ :: Rs, os, h => by
    show (os.1, Objs.set (Rs ++ [R]) (Objs.snoc o Rs os.2) Rs.length _ o') = (os.1, Objs.snoc o' Rs os.2)
    rw [Objs.set_snoc_top o o' Rs os.2]

end Solidity

namespace Solidity

variable {C : Contract} {Γ : Ctx}

/-- A byte's word, as `litSrc` writes it. -/
def byteWord (b : UInt8) : PrimTy.uint.Denote :=
  PrimTy.ofLit .uint (b.toNat : Int) (PrimTy.inRange_uint_of_lt (Nat.lt_trans b.toNat_lt (by decide)))

theorem Heap.get_alloc_self {H : HTy} {R : RefTy} (hp : Heap H) (o : MObj H R) :
    (hp.alloc o).1.get (hp.alloc o).2 = MObj.wk (List.prefix_append H [R]) R o :=
  Objs.get_snoc_top _ H _ _

theorem Heap.set_alloc_self {H : HTy} {R : RefTy} (hp : Heap H) (o o' : MObj H R) :
    (hp.alloc o).1.set (hp.alloc o).2 (MObj.wk (List.prefix_append H [R]) R o') = (hp.alloc o').1 :=
  Objs.set_snoc_top _ _ H _ _

theorem State.allocPush_withHeap {R : RefTy} (σ : State C Γ) (o o' : MObj σ.H R) :
    (σ.allocPush o).withHeap (σ.heap.alloc o').1 = σ.allocPush o' := rfl

theorem State.allocPush_get {R : RefTy} (σ : State C Γ) (o : MObj σ.H R) :
    (σ.allocPush o).heap.get (σ.alloc o).2 = MObj.wk (List.prefix_append σ.H [R]) R o :=
  Heap.get_alloc_self σ.heap o

theorem State.allocPush_set {R : RefTy} (σ : State C Γ) (o o' : MObj σ.H R) :
    (σ.allocPush o).heap.set (σ.alloc o).2 (MObj.wk (List.prefix_append σ.H [R]) R o') =
      (σ.heap.alloc o').1 :=
  Heap.set_alloc_self σ.heap o o'

theorem MObj.setElem_wk_bytes {H H' : HTy} (e : H <+: H') (o : MObj H bytesR) (i : Nat)
    (w : PrimTy.uint.Denote) :
    MObj.setElem .dyn (MObj.wk e bytesR o) i w = MObj.wk e bytesR (MObj.setElem .dyn o i w) := by
  simp only [MObj.setElem_dyn, MObj.wk]
  exact Subtype.ext (List.map_set ..).symm

theorem MObj.wk_bytes_len {H H' : HTy} (e : H <+: H') (o : MObj H bytesR) :
    (MObj.elems .dyn (MObj.wk e bytesR o)).length =
      (o : {l : List (MVal H (.prim .uint)) // l.length < 2 ^ 256}).1.length := by
  simp only [MObj.elems_dyn, MObj.wk, List.length_map]

theorem TRun.assignMem_litWrite (σ : State C Γ) (o : MObj σ.H bytesR) (i : Nat) (hi : i < 2 ^ 256)
    (b : UInt8) (hl : i < (o : {l : List (MVal σ.H (.prim .uint)) // l.length < 2 ^ 256}).1.length) :
    TRun.assignMem (litLoc i hi) (litSrc b) (σ.allocPush o) =
      .ok ⟨σ.allocPush (MObj.setElem .dyn o i (byteWord b)), List.prefix_refl _⟩ := by
  have hg : TEnv.get Idx.here (σ.allocPush o).env = (some (σ.alloc o).2 : Option (HRef _ bytesR)) :=
    rfl
  simp only [TRun.assignMem, MSrc.mvalT, Val.evalT, litLoc, litSrc, MLoc.addrT, MPath.mvalT,
    bind, Except.bind, pure, Except.pure, hg, TRes.ofOpt, Heap.writeAddr, Heap.setIndex,
    State.allocPush_get, MObj.wk_bytes_len]
  have hi' : (Simple.evalT (σ.allocPush o)
      (Simple.lit (i : Int) (PrimTy.inRange_uint_of_lt hi))).val.toNat = i := rfl
  simp only [hi', if_pos hl, MObj.setElem_wk_bytes, State.allocPush_set]
  rfl

end Solidity

namespace Solidity

variable {C : Contract} {Γ : Ctx}

/-- A `bytes` object of the words `l`. -/
abbrev wordsObj (H : HTy) (l : List PrimTy.uint.Denote) (h : l.length < 2 ^ 256) : MObj H bytesR :=
  (⟨l, h⟩ : {l : List (MVal H (.prim .uint)) // l.length < 2 ^ 256})

theorem TRun.litWritesT_alloc (σ : State C Γ) : (bs : List UInt8) → (i : Nat) →
    (pre rest : List PrimTy.uint.Denote) → (o : MObj σ.H bytesR) →
    (o : {l : List (MVal σ.H (.prim .uint)) // l.length < 2 ^ 256}).1 = pre ++ rest →
    pre.length = i → rest.length = bs.length →
    (h : (pre ++ bs.map byteWord).length < 2 ^ 256) →
    (TRun.litWritesT bs i TRun.nil (σ.allocPush o)).map (·.st) =
      .ok (σ.allocPush (wordsObj σ.H (pre ++ bs.map byteWord) h))
  | [], i, pre, rest, o, ho, _, hr, h => by
    have : o = wordsObj σ.H (pre ++ [].map byteWord) h := by
      apply Subtype.ext
      rw [ho, List.length_eq_zero_iff.1 hr]
      rfl
    subst this
    rfl
  | b :: bs, i, pre, rest, o, ho, hp, hr, h => by
    obtain ⟨r, rest', rfl⟩ : ∃ r rest', rest = r :: rest' := by
      cases rest with
      | nil => cases hr
      | cons r rest' => exact ⟨r, rest', rfl⟩
    have hlen : i < (o : {l : List (MVal σ.H (.prim .uint)) // l.length < 2 ^ 256}).1.length := by
      rw [ho, List.length_append, hp, List.length_cons]; omega
    have hi : i < 2 ^ 256 := Nat.lt_trans hlen o.2
    simp only [TRun.litWritesT, dif_pos hi]
    have hl' : (pre ++ [byteWord b] ++ bs.map byteWord).length < 2 ^ 256 := by
      simpa only [List.map_cons, List.append_assoc, List.cons_append, List.nil_append] using h
    have ih := TRun.litWritesT_alloc σ bs (i + 1) (pre ++ [byteWord b]) rest'
      (MObj.setElem .dyn o i (byteWord b))
      (by rw [MObj.setElem_dyn]; simp only [ho, ← hp, List.set_append_right _ _ (Nat.le_refl _),
        Nat.sub_self, List.set_cons_zero, List.append_assoc, List.cons_append, List.nil_append])
      (by rw [List.length_append, hp]; rfl)
      (by simpa only [List.length_cons, Nat.add_right_cancel_iff] using hr) hl'
    rw [TRun.seq, TRun.assignMem_litWrite σ o i hi b hlen]
    have hw : wordsObj σ.H (pre ++ [byteWord b] ++ bs.map byteWord) hl' =
        wordsObj σ.H (pre ++ (b :: bs).map byteWord) h := by
      apply Subtype.ext
      simp only [List.map_cons, List.append_assoc, List.cons_append, List.nil_append]
    rw [hw] at ih
    dsimp only
    revert ih
    cases litWritesT bs (i + 1) nil (σ.allocPush (MObj.setElem ArrTy.dyn o i (byteWord b))) with
    | error e => intro ih; cases ih
    | ok o' => intro ih; exact ih

end Solidity

namespace Solidity

variable {C : Contract} {Γ : Ctx}

theorem TRun.seq_map_st {Γ₁ Γ₂ : Ctx} {s : TStep C Γ Γ₁} {P : TStep C Γ₁ Γ₂} {σ : State C Γ}
    {o : Out C σ.H Γ₁} (h : s σ = .ok o) : (TRun.seq s P σ).map (·.st) = (P o.st).map (·.st) := by
  rw [TRun.seq, h]
  dsimp only
  cases P o.st <;> rfl

/-- A byte string's object: its bytes, as words. -/
abbrev bytesObj (H : HTy) (bs : List UInt8) (hn : bs.length < 2 ^ 256) : MObj H bytesR :=
  wordsObj H (bs.map byteWord) (by rw [List.length_map]; exact hn)

/-- **A literal's allocation is a fresh object of its bytes**: `litBytesT`
runs `k` from the state `Fml.allocAll` reads at that object. -/
theorem TRun.litBytesT_alloc {Γ₁ : Ctx} (σ : State C Γ) (bs : List UInt8)
    (hn : bs.length < 2 ^ 256) (k : TStep C (.mem bytesR :: Γ) Γ₁) :
    (TRun.litBytesT bs k σ).map (·.st) = (k (σ.allocPush (bytesObj σ.H bs hn))).map (·.st) := by
  have hw : (TRun.litBytesT bs TRun.nil σ).map (·.st) =
      .ok (σ.allocPush (bytesObj σ.H bs hn)) := by
    rw [TRun.litBytesT, dif_pos hn, TRun.seq_map_st (TRun.declMem_newArr_bytes σ bs.length hn)]
    exact TRun.litWritesT_alloc σ bs 0 [] (List.replicate bs.length (PrimTy.dflt .uint)) _ rfl rfl
      (List.length_replicate) _
  rw [TRun.litBytesT_seq]
  cases h : TRun.litBytesT bs TRun.nil σ with
  | error e => rw [h] at hw; cases hw
  | ok o =>
    rw [h] at hw
    have hst : o.st = σ.allocPush (bytesObj σ.H bs hn) := Except.ok.inj hw
    rw [TRun.seq_map_st h, hst]

end Solidity
