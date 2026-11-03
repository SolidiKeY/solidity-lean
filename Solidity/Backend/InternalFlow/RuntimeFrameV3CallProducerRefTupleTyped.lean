import Solidity.Backend.InternalFlow.RuntimeFrameV3CallProducerRefTupleFrame

/-! Typed representation of tuple result words. This is a proof layer over
existing return binders, typed environments and machine words; it introduces no
new value or statement representation. compacted proves the exact source
thinning; RefTupleCall builds the complete call certificate from it. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.V3CallProducerRef.Tuple
open Evm Evm.Memory

def resultFrag {Γ : Ctx} {rs : Ctx} (binders : RetBinders rs) (F : Frag Γ) : Frag (rs ++ Γ) :=
  match binders with
  | .nil => F
  | .snoc bs p _ => (resultFrag bs F).push (.val p) .ok
  | .snocMem bs R _ _ _ => (resultFrag bs F).push (.mem R) .ok

/-- Each returned value or live reference has its actual word in the result
interval. The reference denotes an object in the same reached typed heap. -/
structure ResultWords {C : Contract} {H : HTy} {rs : Ctx}
    (start : Nat) (env : TEnv C H rs) (base : Nat → Fin W) (m : Machine) : Prop where
  values : ∀ {p : PrimTy} (i : Idx rs (.val p)),
    ReprV p (TEnv.get i env) (m.mem (cellOf start i))
  pointers : ∀ {R : RefTy} (i : Idx rs (.mem R)),
    ∃ r : HRef H R, TEnv.get i env = some r ∧ m.mem (cellOf start i) = .val (base r.id)

/-- Precise target for the prefix transport proof; no simulation is hidden in
ResultWords beyond the represented result cells themselves. -/
def PrependGoal : Prop :=
  ∀ {C : Contract} {Γ rs : Ctx} {L b frame : Nat} {F : Frag Γ}
    (binders : RetBinders rs) (post : State C Γ) (env : TEnv C post.H rs)
    (base : Nat → Fin W) (m : Machine),
    StateRepr L b frame F post base m → b + (rs ++ Γ).length ≤ frame →
    ResultWords (b + Γ.length) env base m →
    StateRepr L b frame (resultFrag binders F)
      (post.withEnv (TEnv.append rs env post.env)) base m

private theorem write_read (m : Machine) (address : Nat) :
    writeMachine m address (m.mem address) = m := by
  have memory : upd m.mem address (m.mem address) = m.mem := by
    funext x
    by_cases same : x = address
    · subst x; exact upd_same _ _ _
    · exact upd_other _ _ same
  simp only [writeMachine, memory]

/-- Reconstruct the complete typed result prefix over the retained caller.
No result reference is fabricated: every memory binder has a reached HRef and
its actual pointer in ResultWords. -/
theorem prepend : PrependGoal := by
  intro C Γ rs L b frame F binders
  induction binders with
  | nil =>
    intro post env base m represented room words
    exact represented
  | @snoc rs bs p name ih =>
    intro post env base m represented room words
    have tail : ResultWords (b + Γ.length) env.2 base m := by
      constructor
      · intro q index
        simpa only [cellOf, lvl_there] using words.values (.there index)
      · intro R index
        simpa only [cellOf, lvl_there] using words.pointers (.there index)
    have prior := ih post env.2 base m represented (by
      simp only [List.cons_append, List.length_cons] at room
      omega) tail
    have address : cellOf (b + Γ.length) (Idx.here : Idx (.val p :: rs) (.val p)) =
        cell (b + (rs ++ Γ).length) := by
      simp only [cellOf, lvl_here, List.length_append]
      congr 1
      omega
    have value := words.values (Idx.here : Idx (.val p :: rs) (.val p))
    rw [address] at value
    have full := prior.consVal env.1 (m.mem (cell (b + (rs ++ Γ).length))) value
      (by simpa only [List.cons_append, List.length_cons] using room)
    rw [write_read] at full
    exact full
  | @snocMem rs bs R name hd hm ih =>
    intro post env base m represented room words
    have tail : ResultWords (b + Γ.length) env.2 base m := by
      constructor
      · intro p index
        simpa only [cellOf, lvl_there] using words.values (.there index)
      · intro S index
        simpa only [cellOf, lvl_there] using words.pointers (.there index)
    have prior := ih post env.2 base m represented (by
      simp only [List.cons_append, List.length_cons] at room
      omega) tail
    obtain ⟨reference, bound, word⟩ := words.pointers (Idx.here : Idx (.mem R :: rs) (.mem R))
    change env.1 = some reference at bound
    have address : cellOf (b + Γ.length) (Idx.here : Idx (.mem R :: rs) (.mem R)) =
        cell (b + (rs ++ Γ).length) := by
      simp only [cellOf, lvl_here, List.length_append]
      congr 1
      omega
    rw [address] at word
    have full := prior.consMem reference
      (by simpa only [List.cons_append, List.length_cons] using room)
    rw [← word, write_read] at full
    simpa only [resultFrag, TEnv.append, State.withEnv, State.push, bound] using full

#print axioms prepend

/-- Exact typed thinning target after removal of private parameters. -/
def CompactionGoal : Prop :=
  ∀ {C : Contract} {Γ ps rs : Ctx} {L b frame : Nat}
    {G : Frag (rs ++ (ps ++ Γ))} (binders : RetBinders rs)
    (post : State C (rs ++ (ps ++ Γ))) (base : Nat → Fin W) (before after : Machine),
    StateRepr L b frame G post base before →
    Evm.run (code b Γ ps binders) before = .ok after 0 →
    StateRepr L b frame
      (resultFrag binders ((G.restrict (ps ++ Γ)).restrict Γ))
      (post.thin (Thin.keepAll rs (Thin.ofExt (Ext.append Γ ps)))) base after

private theorem take_get {C : Contract} {H : HTy} {Γ rs : Ctx} {t : LTy}
    (i : Idx rs t) : ∀ env : TEnv C H (rs ++ Γ),
    TEnv.get (i.wk (Thin.atop rs Γ)) env = TEnv.get i (TEnv.take rs env) := by
  induction i with
  | here => intro env; rfl
  | there i ih => intro env; exact ih env.2

private theorem atop_number {rs : Ctx} {t : LTy} (i : Idx rs t) (Γ : Ctx) :
    (i.wk (Thin.atop rs Γ)).toNat = i.toNat := by
  induction i with
  | here => rfl
  | there i ih => exact congrArg Nat.succ ih

private theorem atop_cell {Γ rs : Ctx} {t : LTy} (b : Nat) (i : Idx rs t) :
    cellOf b (i.wk (Thin.atop rs Γ)) = cellOf (b + Γ.length) i := by
  have bound := i.toNat_lt
  simp only [cellOf, cell, lvl, atop_number, List.length_append]
  omega

/-- Extract actual typed return words from the reached expanded-body state. -/
theorem ResultWords.of_repr {C : Contract} {Γ rs : Ctx} {L b frame : Nat}
    {G : Frag (rs ++ Γ)} {post : State C (rs ++ Γ)}
    {base : Nat → Fin W} {m : Machine}
    (represented : StateRepr L b frame G post base m) :
    ResultWords (b + Γ.length) (TEnv.take rs post.env) base m := by
  constructor
  · intro p i
    have value := represented.core.vals (i.wk (Thin.atop rs Γ))
    change ReprV p (TEnv.get (i.wk (Thin.atop rs Γ)) post.env)
      (m.mem (cellOf b (i.wk (Thin.atop rs Γ)))) at value
    rw [take_get, atop_cell] at value
    exact value
  · intro R i
    obtain ⟨r, value, word⟩ := represented.pointers (i.wk (Thin.atop rs Γ))
    rw [take_get] at value
    rw [atop_cell] at word
    exact ⟨r, value, word⟩

/-- Actual overlapping copies transport each typed return value and reference,
not merely the raw interval size. -/
theorem ResultWords.copy {C : Contract} {H : HTy} {rs : Ctx}
    {env : TEnv C H rs} {base : Nat → Fin W} {before after : Machine}
    {source destination : Nat} (words : ResultWords source env base before)
    (ordered : destination ≤ source)
    (evaluated : Evm.run (copyCode source destination rs.length) before = .ok after 0) :
    ResultWords destination env base after := by
  obtain ⟨actual, executed, stack, values, outside, fields⟩ :=
    copy_run rs.length source destination before ordered
  have same : actual = after := (Evm.Out.ok.inj (executed.symm.trans evaluated)).1
  subst actual
  have moved {t : LTy} (i : Idx rs t) :
      after.mem (cellOf destination i) = before.mem (cellOf source i) := by
    exact values (rs.length - 1 - i.toNat) (by have bound := i.toNat_lt; omega)
  constructor
  · intro p i
    rw [moved i]
    exact words.values i
  · intro R i
    obtain ⟨r, value, word⟩ := words.pointers i
    exact ⟨r, value, (moved i).trans word⟩

/-- Removal of the private parameters is exactly the existing intrinsic
thinning. Typed result words are derived from the reached StateRepr, rather
than assumed as a new simulation premise. -/
theorem compacted : CompactionGoal := by
  intro C Γ ps rs L b frame G binders post base before after represented evaluated
  have source_eq : b + Γ.length + ps.length = b + (ps ++ Γ).length := by
    simp only [List.length_append]
    omega
  rw [code, source_eq] at evaluated
  have ordered : b + Γ.length ≤ b + (ps ++ Γ).length := by
    simp only [List.length_append]
    omega
  have bound := represented.locals
  have room : b + Γ.length + rs.length ≤ frame := by
    simp only [List.length_append] at bound
    omega
  let caller := (post.drop (Ext.append (ps ++ Γ) rs)).drop (Ext.append Γ ps)
  have retained := copy_retained rs.length (b + (ps ++ Γ).length) (b + Γ.length)
    ordered (Nat.le_refl _) room
    ((represented.drop (Ext.append (ps ++ Γ) rs)).drop (Ext.append Γ ps)) evaluated
  have words := (ResultWords.of_repr represented).copy ordered evaluated
  have result := prepend binders caller (TEnv.take rs post.env) base after retained
    (by simpa only [List.length_append, Nat.add_comm rs.length Γ.length, Nat.add_assoc] using room) words
  have thinned : post.thin (Thin.keepAll rs (Thin.ofExt (Ext.append Γ ps))) =
      caller.withEnv (TEnv.append rs (TEnv.take rs post.env) caller.env) := by
    change post.withEnv (TEnv.thin _ post.env) =
      post.withEnv (TEnv.append rs (TEnv.take rs post.env)
        (TEnv.drop (Ext.append Γ ps) (TEnv.drop (Ext.append (ps ++ Γ) rs) post.env)))
    apply congrArg (fun env => post.withEnv env)
    calc
      TEnv.thin _ post.env = TEnv.thin _
          (TEnv.append rs (TEnv.take rs post.env)
            (TEnv.drop (Ext.append (ps ++ Γ) rs) post.env)) :=
        congrArg (TEnv.thin _) (TEnv.append_take_drop rs post.env).symm
      _ = _ := by rw [TEnv.thin_keepAll, TEnv.thin_ofExt]
  rw [thinned]
  exact result

#print axioms ResultWords.of_repr
#print axioms ResultWords.copy
#print axioms compacted

end Solidity.Backend.InternalFlow.RuntimeFrame.V3CallProducerRef.Tuple
