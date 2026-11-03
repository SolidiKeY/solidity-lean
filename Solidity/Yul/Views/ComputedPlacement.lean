import Solidity.Yul.Views.MemoryContract

/-! Checked mathematical ordinary placements from the actual finite Source
heap. This selects a witness, not a target allocator policy or refinement.
Unsupported occupied IDs and Word-extent overflow are preparation errors,
never source/Yul refusals. Existing Placement and Source representations stay
unchanged. Sparse holes reserve nothing; zero footprints reserve one byte only
to satisfy ordinary Placement's distinct-address requirement. -/
namespace Solidity.Yul.Views.ComputedPlacement

/-- Inspect actual top-level constructors, never relabel scalar cells or
storage/calldata aggregates as ordinary allocated memory. -/
def objectShape {D : Source.Layout} {τ : Source.STy} (d : Source.Data D τ) : Option MemoryShape := by
  cases d with
  | val _ => exact none
  | mapping _ => exact none
  | @bytes l bs => cases l with
    | memory => exact some (.bytes bs.length)
    | _ => exact none
  | @string l bs => cases l with
    | memory => exact some (.bytes bs.length)
    | _ => exact none
  | @array l τ n len hl xs => cases l with
    | memory => exact some (.array n.isNone len)
    | _ => exact none
  | @struct l name fs => cases l with
    | memory => exact some (.strct (D.fields name).length)
    | _ => exact none

theorem objectShape_sound {D : Source.Layout} {τ : Source.STy} (d : Source.Data D τ)
    (shape : MemoryShape) (found : objectShape d=some shape) : HasMemoryShape d shape := by
  cases d with
  | val _ => cases found
  | mapping _ => cases found
  | @bytes l bs => cases l with
    | memory => cases found;exact .bytes bs
    | storage | calldata => cases found
  | @string l bs => cases l with
    | memory => cases found;exact .string bs
    | storage | calldata => cases found
  | @array l τ n len hl xs => cases l with
    | memory => cases found;exact .array len hl xs
    | storage | calldata => cases found
  | @struct l name fs => cases l with
    | memory => cases found;exact .strct fs
    | storage | calldata => cases found

def shapeAt {D : Source.Layout} (h : Source.Heap D) (a : Nat) : MemoryShape :=
  ((h.get a).bind (fun x=>objectShape x.2)).getD (.bytes 0)

def unsupported {D : Source.Layout} (h : Source.Heap D) : List Nat :=
  (List.range h.next).filter (fun a=>match h.get a with
    | none=>false | some x=>(objectShape x.2).isNone)

def position {D : Source.Layout} (h : Source.Heap D) : Nat → Nat
  | 0=>128
  | n+1=>position h n + if (h.get n).isSome then max 1 (shapeAt h n).size else 0

theorem position_mono {D : Source.Layout} (h : Source.Heap D) (a b : Nat) (bound : a≤b) :
    position h a≤position h b := by
  induction b generalizing a with
  | zero =>
    have same : a=0 := by omega
    subst a
    exact Nat.le_refl _
  | succ b ih =>
    by_cases small : a≤b
    · have old := ih a small
      change position h a≤position h b+_
      omega
    · have same : a=b+1 := by omega
      subst a
      exact Nat.le_refl _

theorem occupied_lt {D : Source.Layout} (h : Source.Heap D) (a : Nat)
    (present : (h.get a).isSome) : a<h.next := by
  by_cases small : a<h.next
  · exact small
  · have no := h.bounded a (by omega)
    change (h.cells a).isSome=true at present
    rw [no] at present
    cases present

theorem shape_typed {D : Source.Layout} (h : Source.Heap D) (clear : unsupported h=[])
    (a : Nat) (τ : Source.STy) (d : Source.Data D τ) (found : h.get a=some ⟨τ,d⟩) :
    HasMemoryShape d (shapeAt h a) := by
  have bound := occupied_lt h a (by rw [found];rfl)
  cases shape : objectShape d with
  | none =>
    have bad : a∈unsupported h := by
      apply List.mem_filter.mpr
      refine ⟨List.mem_range.mpr bound,?_⟩
      change (match h.get a with | none=>false | some x=>(objectShape x.2).isNone)=true
      rw [found]
      change (objectShape d).isNone=true
      rw [shape]
      rfl
    rw [clear] at bad
    cases bad
  | some sh =>
    have same : shapeAt h a=sh := by
      simp only [shapeAt,found,Option.bind_some,shape,Option.getD_some]
    rw [same]
    exact objectShape_sound d sh shape

theorem interval_before {D : Source.Layout} (h : Source.Heap D) (a b : Nat)
    (present : (h.get a).isSome) (order : a<b) :
    position h a+(shapeAt h a).size≤position h b := by
  have step : position h a+(shapeAt h a).size≤position h (a+1) := by
    simp only [position,present,↓reduceIte]
    omega
  exact Nat.le_trans step (position_mono h (a+1) b (by omega))

theorem present_strict {D : Source.Layout} (h : Source.Heap D) (a b : Nat)
    (present : (h.get a).isSome) (order : a<b) : position h a<position h b := by
  have step : position h a<position h (a+1) := by
    simp only [position,present,↓reduceIte]
    omega
  have later := position_mono h (a+1) b (by omega)
  omega

/-- Construct the existing intrinsic Placement. Guards concern exact computed
shape support and Word extent, not a supplied separation/layout theorem. -/
def build {D : Source.Layout} (h : Source.Heap D) (clear : unsupported h=[])
    (bound : position h h.next<2^256) : Placement h where
  address := position h
  shape := shapeAt h
  free := ⟨position h h.next,bound⟩
  free_start := position_mono h 0 h.next (Nat.zero_le _)
  distinct a b ha hb same := by
    by_cases order : a<b
    · have strict := present_strict h a b ha order
      omega
    · by_cases reverse : b<a
      · have strict := present_strict h b a hb reverse
        omega
      · omega
  typed a τ d found := shape_typed h clear a τ d found
  starts a _ := position_mono h 0 a (Nat.zero_le _)
  ends a present := interval_before h a h.next present (occupied_lt h a present)
  separate a b ha hb different := by
    by_cases order : a<b
    · exact Or.inl (interval_before h a b ha order)
    · exact Or.inr (interval_before h b a hb (by omega))

inductive Error where
  | unsupported (ids : List Nat)
  | overflow (computedEnd : Nat)
  deriving DecidableEq, Repr

/-- No chosen addresses or shape/separation facts are inputs. Every occupied
unsupported ID remains explicit; sparse holes are not treated as errors. -/
def prepare {D : Source.Layout} (h : Source.Heap D) : Except Error (Placement h) :=
  if clear : unsupported h=[] then
    if bound : position h h.next<2^256 then .ok (build h clear bound)
    else .error (.overflow (position h h.next))
  else .error (.unsupported (unsupported h))

theorem prepare_success {D : Source.Layout} (h : Source.Heap D) (clear : unsupported h=[])
    (bound : position h h.next<2^256) : prepare h=.ok (build h clear bound) := by
  rw [prepare,dif_pos clear,dif_pos bound]

theorem prepare_unsupported {D : Source.Layout} (h : Source.Heap D) (bad : unsupported h≠[]) :
    prepare h=.error (.unsupported (unsupported h)) := by rw [prepare,dif_neg bad]

theorem prepare_overflow {D : Source.Layout} (h : Source.Heap D) (clear : unsupported h=[])
    (large : 2^256≤position h h.next) : prepare h=.error (.overflow (position h h.next)) := by
  rw [prepare,dif_pos clear,dif_neg (by omega)]

/-- Exact computed output choices and complete support accounting. The
Placement itself carries the proved typing/separation/bounds fields. -/
theorem prepare_choices {D : Source.Layout} (h : Source.Heap D) (p : Placement h)
    (done : prepare h=.ok p) : p.address=position h ∧ p.shape=shapeAt h ∧
      p.free.val=position h h.next ∧ unsupported h=[] := by
  unfold prepare at done
  split at done
  · rename_i clear
    split at done
    · cases done
      exact ⟨rfl,rfl,rfl,clear⟩
    · cases done
  · cases done

end Solidity.Yul.Views.ComputedPlacement
