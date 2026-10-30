import Solidity.Storage.Representation.Reads

/-! Representation is local to the existing `Occ` footprint. -/
namespace Solidity.Storage.Representation

private theorem fields_head_occ {t : STy} {ts : List STy} {l x : Loc}
    (h : Occ t l x) : Occ (.strct (t :: ts)) l x := by
  have h' : Occ t (l.add (STy.sizes ([] : List STy))) x := by
    simpa only [STy.sizes, Loc.add_zero] using h
  exact .field (i := 0) rfl h'

private theorem fields_tail_occ {t : STy} {ts : List STy} {l x : Loc}
    (h : Occ (.strct ts) (l.add t.size) x) : Occ (.strct (t :: ts)) l x := by
  cases h with
  | @field _ i f _ _ hi hx =>
    apply Occ.field (i := i + 1) (by exact hi)
    simpa only [List.take_succ_cons, STy.sizes, Loc.add_add] using hx

private theorem elements_head_occ {t : STy} {n : Nat} {l x : Loc}
    (h : Occ t l x) : Occ (.sarr t (n + 1)) l x := by
  apply Occ.sarr (i := 0) (Nat.zero_lt_succ n)
  simpa only [Nat.zero_mul, Loc.add_zero] using h

private theorem elements_tail_occ {t : STy} {n : Nat} {l x : Loc}
    (h : Occ (.sarr t n) (l.add t.size) x) : Occ (.sarr t (n + 1)) l x := by
  cases h with
  | @sarr _ _ i _ _ hi hx =>
    apply Occ.sarr (i := i + 1) (Nat.succ_lt_succ hi)
    simpa only [Loc.add_add, Nat.succ_mul, Nat.add_comm] using hx

private def VLocal {T : Ty} (v : SVal T) (t : STy) (l : Loc) (w : Store) : Prop :=
  ∀ w', (∀ x, Occ t l x → w' x = w x) → ValueRep v t l w'
private def FLocal {fs : List (Name × Ty)} (vs : SFields fs) (ts : List STy)
    (l : Loc) (w : Store) : Prop :=
  ∀ w', (∀ x, Occ (.strct ts) l x → w' x = w x) → FieldsRep vs ts l w'
private def ELocal {E : Ty} (vs : List (SVal E)) (t : STy) (l : Loc) (w : Store) : Prop :=
  ∀ w', (∀ x, Occ (.sarr t vs.length) l x → w' x = w x) → ElementsRep vs t l w'

private theorem local_scalar {p : PrimTy} (v : p.Denote) (l : Loc) (w : Store)
    (read : w l = PrimTy.toWord v) : VLocal (.prim v) .word l w := by
  intro w' agree
  exact .scalar v l w' ((agree l .word).trans read)

private theorem local_struct {s : Name} (fs : SFields (Semantics.structDef s))
    (ts : List STy) (l : Loc) (w : Store) (_ : FieldsRep fs ts l w)
    (ih : FLocal fs ts l w) : VLocal (.struct (s := s) fs) (.strct ts) l w := by
  intro w' agree
  exact .strct fs ts l w' (ih w' agree)

private theorem local_fixed {E : Ty} {n : Nat} (vs : SVec E n) (t : STy)
    (l : Loc) (w : Store) (shape : TypeRep E t) (_ : ElementsRep vs.toList t l w)
    (ih : ELocal vs.toList t l w) : VLocal (.fixed vs) (.sarr t n) l w := by
  intro w' agree
  apply ValueRep.fixed vs t l w' shape
  apply ih w'
  intro x hx
  apply agree x
  simpa only [SVec.length_toList] using hx

private theorem local_array {E : Ty} {n : Nat} (vs : SVec E n) (sh : SList E)
    (hn : n < 2 ^ 256) (t : STy) (l : Loc) (w : Store) (shape : TypeRep E t)
    (live : n ≤ lmax) (extent : (vs.toList ++ sh.toList).length ≤ lmax)
    (header : (w l).val = n) (_ : ElementsRep (vs.toList ++ sh.toList) t (.data l 0) w)
    (ih : ELocal (vs.toList ++ sh.toList) t (.data l 0) w) :
    VLocal (.array vs sh hn) (.darr t) l w := by
  intro w' agree
  apply ValueRep.array vs sh hn t l w' shape live extent
  · exact (congrArg Subtype.val (agree l .len)).trans header
  · apply ih w'
    intro x hx
    cases hx with
    | @sarr _ _ i _ _ hi he =>
      apply agree x (Occ.darr (Nat.lt_of_lt_of_le hi extent) ?_)
      simpa only [Loc.add, Nat.zero_add] using he

private theorem local_mapping {K : PrimTy} {V : Ty} (entries : SMap K V) (d : SVal V)
    (t : STy) (l : Loc) (w : Store) (shape : TypeRep V t)
    (_ : ∀ k : K.Denote, ValueRep ((Semantics.lookupBy k entries.toList).getD d) t
      (.hash (PrimTy.toWord k).val.toNat l 0) w)
    (ih : ∀ k : K.Denote, VLocal ((Semantics.lookupBy k entries.toList).getD d) t
      (.hash (PrimTy.toWord k).val.toNat l 0) w) : VLocal (.map entries d) (.map t) l w := by
  intro w' agree
  apply ValueRep.mapping entries d t l w' shape
  intro k
  exact ih k w' (fun x hx => agree x (.entry hx))

private theorem local_fnil (l : Loc) (w : Store) : FLocal .nil [] l w := by
  intro w' _
  exact .nil _ _

private theorem local_fcons {f : Name} {T : Ty} {fs : List (Name × Ty)}
    (v : SVal T) (rest : SFields fs) (t : STy) (ts : List STy) (l : Loc) (w : Store)
    (_ : ValueRep v t l w) (_ : FieldsRep rest ts (l.add t.size) w)
    (ih : VLocal v t l w) (it : FLocal rest ts (l.add t.size) w) :
    FLocal (SFields.cons (f := f) v rest) (t :: ts) l w := by
  intro w' agree
  exact .cons v rest t ts l w'
    (ih w' (fun x hx => agree x (fields_head_occ hx)))
    (it w' (fun x hx => agree x (fields_tail_occ hx)))

private theorem local_enil {E : Ty} (t : STy) (l : Loc) (w : Store) :
    ELocal (E := E) [] t l w := by
  intro w' _
  exact .nil _ _ _

private theorem local_econs {E : Ty} (v : SVal E) (rest : List (SVal E))
    (t : STy) (l : Loc) (w : Store)
    (_ : ValueRep v t l w) (_ : ElementsRep rest t (l.add t.size) w)
    (ih : VLocal v t l w) (it : ELocal rest t (l.add t.size) w) :
    ELocal (v :: rest) t l w := by
  intro w' agree
  exact .cons v rest t l w'
    (ih w' (fun x hx => agree x (elements_head_occ hx)))
    (it w' (fun x hx => agree x (elements_tail_occ hx)))

/-- Changing no occupied word preserves a represented value. -/
theorem ValueRep.congr {T : Ty} {v : SVal T} {t : STy} {l : Loc} {w w' : Store}
    (h : ValueRep v t l w) (agree : ∀ x, Occ t l x → w' x = w x) : ValueRep v t l w' :=
  ValueRep.rec (motive_1 := fun v t l w _ => VLocal v t l w)
    (motive_2 := fun vs ts l w _ => FLocal vs ts l w)
    (motive_3 := fun vs t l w _ => ELocal vs t l w)
    local_scalar local_struct local_fixed local_array local_mapping
    local_fnil local_fcons local_enil local_econs h w' agree

theorem FieldsRep.congr {fs : List (Name × Ty)} {vs : SFields fs}
    {ts : List STy} {l : Loc} {w w' : Store} (h : FieldsRep vs ts l w)
    (agree : ∀ x, Occ (.strct ts) l x → w' x = w x) : FieldsRep vs ts l w' :=
  FieldsRep.rec (motive_1 := fun v t l w _ => VLocal v t l w)
    (motive_2 := fun vs ts l w _ => FLocal vs ts l w)
    (motive_3 := fun vs t l w _ => ELocal vs t l w)
    local_scalar local_struct local_fixed local_array local_mapping
    local_fnil local_fcons local_enil local_econs h w' agree

theorem ElementsRep.congr {E : Ty} {vs : List (SVal E)} {t : STy} {l : Loc} {w w' : Store}
    (h : ElementsRep vs t l w) (agree : ∀ x, Occ (.sarr t vs.length) l x → w' x = w x) :
    ElementsRep vs t l w' :=
  ElementsRep.rec (motive_1 := fun v t l w _ => VLocal v t l w)
    (motive_2 := fun vs ts l w _ => FLocal vs ts l w)
    (motive_3 := fun vs t l w _ => ELocal vs t l w)
    local_scalar local_struct local_fixed local_array local_mapping
    local_fnil local_fcons local_enil local_econs h w' agree

/-- A write outside a subtree's occupied terms preserves its representation. -/
theorem ValueRep.frame {T : Ty} {v : SVal T} {t : STy} {l x : Loc} {w : Store}
    (h : ValueRep v t l w) (outside : ¬ Occ t l x) (new : Semantics.Word) :
    ValueRep v t l (write w x new) := by
  apply h.congr
  intro y hy
  apply write_other
  intro eq
  exact outside (eq ▸ hy)

/-- Different mapping keys frame every represented nested value. -/
theorem mapping_entry_frame {T : Ty} {v : SVal T} {t u : STy} {l x : Loc}
    {k k' : Nat} {w : Store} (h : ValueRep v t (.hash k l 0) w)
    (different : k ≠ k') (touched : Occ u (.hash k' l 0) x) (new : Semantics.Word) :
    ValueRep v t (.hash k l 0) (write w x new) :=
  h.frame (fun hx => occ_keys_disjoint different hx touched) new

/-- A header write cannot alter any represented nested element value. -/
theorem array_element_header_frame {T : Ty} {v : SVal T} {t : STy} {l : Loc} {i : Nat}
    {w : Store} (h : ValueRep v t (.data l (i * t.size)) w) (new : Semantics.Word) :
    ValueRep v t (.data l (i * t.size)) (write w l new) :=
  h.frame (fun hx => occ_darr_len_elem hx) new

end Solidity.Storage.Representation
