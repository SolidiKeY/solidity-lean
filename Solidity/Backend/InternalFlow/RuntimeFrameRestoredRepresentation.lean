import Solidity.Backend.InternalFlow.RuntimeFrameInterfaceV1
import Solidity.Evm.Correct

/-! Implementation of the FROZEN restored-representation obligation. The
source caller environment and current fragment facts are real inputs; neither
old heap contents nor old fragile-alias liveness is inferred. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.Restored
open Evm Evm.Memory
variable {C : Contract}

theorem value_unique {p : PrimTy} {v : p.Denote} {left right : Word}
 (a : ReprV p v left) (b : ReprV p v right) : left = right := by
 cases p with
 | uint => exact Restore.uint_unique a b
 | bool => exact Eq.trans a (Eq.symm b)
 | int =>
  obtain ⟨x,rfl,hx⟩ := a
  obtain ⟨y,rfl,hy⟩ := b
  have same : x = y := Fin.ext (sgn_inj x.isLt y.isLt (hx.symm.trans hy))
  rw [same]

theorem path_unique {a : Bool} {T U : Ty} {p : Path T U} {root left right : Slot}
 (first : PathAt a p root left) (second : PathAt a p root right) : left = right := by
 induction first generalizing right with
 | nil => cases second; rfl
 | field _ ih => cases second with | field other => exact ih other
 | key _ ih => cases second with | key other => exact ih other
 | elem _ ih => cases second with | elem other => exact ih other
 | felem bound _ ih => cases second with | felem _ other => exact ih other

theorem member_bounds (b : Nat) (Γ : Ctx) (x : Nat)
 (member : x ∈ Restore.contextCells b Γ) : b ≤ x ∧ x < b + Γ.length := by
 obtain ⟨n,hn,rfl⟩ := List.mem_map.mp member
 have small := List.mem_range.mp hn
 omega

theorem captured_index {Γ Δ : Ctx} (scope : Ext Γ Δ) (b : Nat) {t : LTy}
 (index : Idx Δ t) (member : cellOf b index ∈ Restore.contextCells b Γ) :
 ∃ old : Idx Γ t, old.ext scope = index := by
 induction scope with
 | refl => exact ⟨index,rfl⟩
 | @push Δ u scope ih =>
  cases index with
  | here =>
   have upper := (member_bounds b Γ _ member).2
   have length := scope.length_eq
   simp only [cellOf,cell,lvl,Idx.toNat,List.length_cons,Nat.sub_zero,Nat.add_sub_cancel] at upper
   omega
  | there index =>
   have child : cellOf b index ∈ Restore.contextCells b Γ := by
    simpa only [cellOf,lvl_there] using member
   obtain ⟨old,same⟩ := ih index child
   exact ⟨old,by cases same; rfl⟩

/-- The exact source transport at an old typed index. -/
theorem source_value {Γ Δ : Ctx} {caller : State C Γ} {post : State C Δ}
 (scope : Ext Γ Δ) (growth : caller.H <+: post.H)
 (environment : TEnv.drop scope post.env = TEnv.wk growth Γ caller.env)
 {t : LTy} (index : Idx Γ t) :
 TEnv.get (index.ext scope) post.env = LTy.TDenote.wk growth t (TEnv.get index caller.env) := by
 rw [← Evm.TEnv.get_drop scope post.env index,environment,TEnv.get_wk]

def Observed {Γ : Ctx} (F : Frag Γ) {t : LTy} (index : Idx Γ t) : Prop :=
 match t with
 | .val _ | .mem _ => True
 | .alias _ => F.get index ≠ .dead
 | .old | .oldNet | .kint => False

/-- Either live alias class supplies its genuine slot; current liveness is
not transported from this lemma to a different storage state. -/
theorem alias_slot {Γ : Ctx} {L b frame : Nat} {F : Frag Γ}
 {state : State C Γ} {base : Nat → Fin W} {m : Machine}
 (repr : StateRepr L b frame F state base m) {R : RefTy} (index : Idx Γ (.alias R))
 (live : F.get index ≠ .dead) :
 ∃ reference slot, Look.ofTEnv state.env index = some reference ∧
 m.mem (cellOf b index) = .slot slot ∧ PathSlot C false reference slot := by
 cases flag : F.get index with
 | dead => exact (live flag).elim
 | ok =>
  obtain ⟨reference,slot,value,word,path⟩ := repr.core.aliases index flag
  exact ⟨reference,slot,value,word,path.weaken⟩
 | fragile =>
  obtain ⟨reference,slot,value,word,path,liveNow⟩ := repr.core.fragile index flag
  exact ⟨reference,slot,value,word,path⟩

/-- Old semantically represented caller cells agree from SOURCE transport
and the two actual representations, not a target preservation premise. -/
theorem caller_word {Γ Δ : Ctx} {L b frame : Nat} {F : Frag Γ} {G : Frag Δ}
 {caller : State C Γ} {post : State C Δ} {base addresses : Nat → Fin W}
 {before after : Machine}
 (scope : Ext Γ Δ) (growth : caller.H <+: post.H)
 (initial : StateRepr L b frame F caller base before)
 (reached : StateRepr L b frame G post addresses after)
 (environment : TEnv.drop scope post.env = TEnv.wk growth Γ caller.env)
 (extension : BaseExtends caller.H base addresses)
 (flags : InterfaceV1.NoAliasPromotion F G scope)
 {t : LTy} (index : Idx Γ t) (needed : Observed G (index.ext scope)) :
 before.mem (cellOf b index) = after.mem (cellOf b index) := by
 have transported := source_value scope growth environment index
 have read : Look.ofTEnv post.env (index.ext scope) = Look.ofTEnv caller.env index := by
  simp only [Look.ofTEnv,transported,see_wk]
 cases t with
 | val p =>
  have a := initial.core.vals index
  have z := reached.core.vals (index.ext scope)
  rw [read,lvl_ext] at z
  exact value_unique a z
 | mem R =>
  obtain ⟨old,oldValue,oldWord⟩ := initial.pointers index
  obtain ⟨current,currentValue,currentWord⟩ := reached.pointers (index.ext scope)
  have value : TEnv.get (index.ext scope) post.env = some (old.wk growth) := by
   rw [transported,oldValue]
   rfl
  have same : current = old.wk growth := Option.some.inj (currentValue.symm.trans value)
  subst current
  simp only [cellOf,lvl_ext,HRef.wk] at currentWord
  rw [extension old] at currentWord
  exact oldWord.trans currentWord.symm
 | alias R =>
  obtain ⟨old,oldSlot,oldValue,oldWord,oldPath⟩ := alias_slot initial index (flags index needed)
  obtain ⟨current,currentSlot,currentValue,currentWord,currentPath⟩ := alias_slot reached (index.ext scope) needed
  have same : old = current := Option.some.inj (oldValue.symm.trans (read.symm.trans currentValue))
  subst current
  have slot := path_unique oldPath currentPath
  simp only [cellOf,lvl_ext] at currentWord
  rw [← slot] at currentWord
  exact oldWord.trans currentWord.symm
 | old => exact needed.elim
 | oldNet => exact needed.elim
 | kint => exact needed.elim

/-- Rebuild all representation fields with observed locals and heap words.
Post-body machine fields are retained; this is not a whole-State rollback. -/
theorem memory_transport {Δ : Ctx} {L b frame : Nat} {G : Frag Δ}
 {post : State C Δ} {addresses : Nat → Fin W} {after : Machine}
 (reached : StateRepr L b frame G post addresses after) (memory : Nat → Word)
 (locals : ∀ {t : LTy} (index : Idx Δ t), Observed G index →
   memory (cellOf b index) = after.mem (cellOf b index))
 (heap : ∀ x, frame ≤ x → memory x = after.mem x) :
 StateRepr L b frame G post addresses {after with mem := memory} := by
 constructor
 · refine ⟨reached.core.store,?_,?_,reached.core.net,reached.core.netSelf,reached.core.bound,
    ?_,reached.core.env,reached.core.funds,reached.core.oracle⟩
   · intro p index
     change ReprV p _ (memory (cellOf b index))
     rw [locals index True.intro]
     exact reached.core.vals index
   · intro R index flag
     obtain ⟨reference,slot,value,word,path⟩ := reached.core.aliases index flag
     refine ⟨reference,slot,value,?_,path⟩
     change memory (cellOf b index) = _
     rw [locals index (by change G.get index ≠ .dead;rw [flag];decide)]
     exact word
   · intro R index flag
     obtain ⟨reference,slot,value,word,path,live⟩ := reached.core.fragile index flag
     refine ⟨reference,slot,value,?_,path,live⟩
     change memory (cellOf b index) = _
     rw [locals index (by change G.get index ≠ .dead;rw [flag];decide)]
     exact word
 · refine ⟨?_,reached.heap.above,reached.heap.separated⟩
   intro p reference
   refine ⟨(reached.heap.arrays reference).space,?_,?_⟩
   · change memory _ = _
     rw [heap _ (reached.heap.above reference)]
     exact (reached.heap.arrays reference).length
   · intro i value source
     change ReprV p value (memory _)
     rw [heap _ (by have h := reached.heap.above reference;omega)]
     exact (reached.heap.arrays reference).elements i value source
 · intro R index
   obtain ⟨reference,value,word⟩ := reached.pointers index
   refine ⟨reference,value,?_⟩
   change memory (cellOf b index) = _
   rw [locals index True.intro]
   exact word
 · exact reached.locals
 · refine ⟨?_,reached.structs.above,reached.structs.separated⟩
   intro name reference
   refine ⟨(reached.structs.objects reference).space,?_⟩
   intro field p source
   change ReprV p _ (memory _)
   rw [heap _ (by have h := reached.structs.above reference;omega)]
   exact (reached.structs.objects reference).fields source
 · exact reached.separated
 · intro name field R reference source
   change memory _ = _
   rw [heap _ (by have h := reached.structs.above reference;omega)]
   exact reached.refs reference source

/-- The EXACT frozen v1 statement, for all caller/context local types.
The old caller may contain aliases/logical locals; none is excluded. -/
theorem restored_representation : InterfaceV1.RestoredRepresentationClaim := by
 intro C Γ Δ L b frame lo pointer start F G caller post base addresses before after last
   scope growth initial reached environment extension flags bodyBound pointerAbove pointerBelow boundary recovered
 have locals : ∀ {t : LTy} (index : Idx Δ t), Observed G index →
     last.mem (cellOf b index) = after.mem (cellOf b index) := by
  intro t index needed
  have below : cellOf b index < lo := Nat.lt_of_lt_of_le (lvl_lt b index) bodyBound
  by_cases captured : cellOf b index ∈ Restore.contextCells b Γ
  · obtain ⟨old,same⟩ := captured_index scope b index captured
    subst index
    have oldWord := caller_word scope growth initial reached environment extension flags old needed
    have localWord := recovered.locals (cellOf b (old.ext scope)) below
    rw [if_pos captured] at localWord
    simp only [cellOf,lvl_ext] at localWord ⊢
    exact localWord.trans oldWord
  · have localWord := recovered.locals (cellOf b index) below
    simpa only [if_neg captured] using localWord
 have heap : ∀ x, frame ≤ x → last.mem x = after.mem x := by
  intro x above
  exact recovered.exterior x (by omega) (by omega)
 have represented := memory_transport reached last.mem locals heap
 have changed := represented.stack last.stack
 have fields := congrArg (fun m : Machine => {m with mem := last.mem,stack := last.stack}) recovered.fields
 have same : {after with mem := last.mem,stack := last.stack} = last := fields.symm
 rw [same] at changed
 exact changed

/-- First implemented frozen premise; not a complete call/recursive producer. -/
def restorationProducer : InterfaceV1.PendingRestoration := ⟨restored_representation⟩
end Solidity.Backend.InternalFlow.RuntimeFrame.Restored
