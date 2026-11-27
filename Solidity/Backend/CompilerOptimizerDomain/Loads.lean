import Solidity.Backend.CompilerOptimizerDomain.Propagate
import Solidity.Optimizer.Loads

/-! Accepted replacements in the actual redundant-load elimination table. -/
namespace Solidity.Backend.CompilerOptimizerDomain
open Solidity Solidity.Optimizer.ConstFold
open Solidity.Backend.AbiWorld.PublicCompilerTotal
variable {C : Contract}

def LoadsOk {Γ : Ctx} (E : List (LEnt C Γ)) : Prop :=
  ∀ a ∈ E, ValOk (.simple a.s)

theorem loads_nil_ok {Γ : Ctx} : LoadsOk ([] : List (LEnt C Γ)) := fun _ h => nomatch h

theorem loads_cons_ok {Γ : Ctx} {E : List (LEnt C Γ)} {a : LEnt C Γ}
    (ha : ValOk (.simple a.s)) (hE : LoadsOk E) : LoadsOk (a :: E) := by
  intro b hb
  rcases List.mem_cons.mp hb with rfl | hb
  · exact ha
  · exact hE b hb

theorem loads_filter_ok {Γ : Ctx} {E : List (LEnt C Γ)} (hE : LoadsOk E)
    (f : LEnt C Γ → Bool) : LoadsOk (E.filter f) :=
  fun a ha => hE a (List.mem_filter.mp ha).1

theorem loads_find_ok {Γ : Ctx} {E : List (LEnt C Γ)} (hE : LoadsOk E)
    {p : PrimTy} (l : Load C Γ p) {s : Simple C Γ p} (hf : LEnt.find? l E = some s) :
    ValOk (.simple s) := by
  induction E with
  | nil => contradiction
  | cons a E ih =>
    have ha := hE a List.mem_cons_self
    have ht : LoadsOk E := fun b hb => hE b (List.mem_cons_of_mem a hb)
    obtain ⟨q, l', s'⟩ := a
    simp only [LEnt.find?] at hf
    split at hf
    · next e =>
      subst e
      split at hf
      · cases hf; exact ha
      · exact ih ht hf
    · exact ih ht hf

theorem val_rle_ok {Γ : Ctx} {E : List (LEnt C Γ)} (hE : LoadsOk E) :
    {p : PrimTy} → {v : Val C Γ p} → ValOk v → ValOk (v.rle E)
  | _, _, h@(.lit ..) => h
  | _, _, h@(.bool ..) => h
  | _, _, h@(.local ..) => h
  | _, _, h@(.env ..) => h
  | _, _, h@(.read ..) => by
      simp only [Val.rle]
      split
      · split
        · exact loads_find_ok hE _ ‹_›
        · exact h
      · exact h
  | _, _, h@(.len ..) => h
  | _, _, .binop op h hq ha hb => .binop op h hq (val_rle_ok hE ha) (val_rle_ok hE hb)
  | _, _, .unop op h hq ha => .unop op h hq (val_rle_ok hE ha)
  | _, _, .ternary hc ha hb => .ternary (val_rle_ok hE hc) (val_rle_ok hE ha) (val_rle_ok hE hb)

theorem loads_set_ok {Γ : Ctx} {E : List (LEnt C Γ)} (hE : LoadsOk E)
    {p : PrimTy} (i : Idx Γ (.val p)) (v : Val C Γ p) : LoadsOk (LEnt.set E i v) := by
  unfold LEnt.set
  split
  · split
    · exact loads_filter_ok hE _
    · exact loads_cons_ok (.local i) (loads_filter_ok hE _)
  · exact loads_filter_ok hE _

theorem loads_decl_ok {Γ : Ctx} {E : List (LEnt C Γ)} (hE : LoadsOk E)
    {p : PrimTy} (v : Option (Val C Γ p)) : LoadsOk (LEnt.decl E v) := by
  have hsh : LoadsOk (E.map (LEnt.shift (t := .val p))) := by
    intro a ha
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
    exact shiftS_ok (hE b hb) _
  unfold LEnt.decl
  split
  · exact loads_cons_ok (.local .here) hsh
  · exact hsh

theorem loads_store_ok {Γ : Ctx} {E : List (LEnt C Γ)} (hE : LoadsOk E)
    {p : PrimTy} (l : Loc C Γ (.prim p)) {v : Val C Γ p} (hv : ValOk v) :
    LoadsOk (LEnt.store E l (.val v)) := by
  have hk := loads_filter_ok hE (fun a => match a.l.sroot? with
    | some r => match l.root? with | some n => r != n | none => false
    | none => true)
  simp only [LEnt.store, LEnt.storeEnt?]
  split
  · next s ld hs _ =>
    split
    · exact loads_cons_ok (by rw [← simple?_eq hs]; exact hv) hk
    · exact hk
  · exact hk

mutual
theorem stmt_rle_ok : {Γ Γ' : Ctx} → {K K' : Kinds} → {s : Solidity.Stmt C Γ Γ'} →
    StmtOk K s K' → {F : List (LEnt C Γ)} → LoadsOk F →
    StmtOk K (Stmt.rle F s).1 K' ∧ LoadsOk (Stmt.rle F s).2
  | _, _, _, _, _, .assign hl hv, _, hF => ⟨.assign hl (val_rle_ok hF hv), loads_store_ok hF _ (val_rle_ok hF hv)⟩
  | _, _, _, _, _, .assignLocal i hv, _, hF =>
      ⟨.assignLocal i (val_rle_ok hF hv), loads_set_ok hF i _⟩
  | _, _, _, _, _, .declNone p x, _, hF => ⟨.declNone p x, loads_decl_ok hF none⟩
  | _, _, _, _, _, .declSome p x hv, _, hF =>
      ⟨.declSome p x (val_rle_ok hF hv), loads_decl_ok hF (some _)⟩
  | _, _, _, _, _, h@(.declStorage ..), _, _ => ⟨h, loads_nil_ok⟩
  | _, _, _, _, _, h@(.declIndexed ..), _, _ => ⟨h, loads_nil_ok⟩
  | _, _, _, _, _, h@(.rebind ..), _, _ => ⟨h, loads_nil_ok⟩
  | _, _, _, _, _, h@(.rebindIndexed ..), _, _ => ⟨h, loads_nil_ok⟩
  | _, _, _, _, _, h@(.opAssign ..), _, _ => ⟨h, loads_nil_ok⟩
  | _, _, _, _, _, h@(.incDec ..), _, _ => ⟨h, loads_nil_ok⟩
  | _, _, _, _, _, .require hc, _, hF => ⟨.require (val_rle_ok hF hc), hF⟩
  | _, _, _, _, _, .assert hc, _, hF => ⟨.assert (val_rle_ok hF hc), hF⟩
  | _, _, _, _, _, h@(.revert), _, _ => ⟨h, loads_nil_ok⟩
  | _, _, _, _, _, h@(.callNone ..), _, _ => ⟨h, loads_nil_ok⟩
  | _, _, _, _, _, h@(.callVal ..), _, _ => ⟨h, loads_nil_ok⟩
  | _, _, _, _, _, .ite hc ht he, _, hF =>
      ⟨.ite (val_rle_ok hF hc) (prog_rle_ok ht hF) (prog_rle_ok he hF), loads_nil_ok⟩
  | _, _, _, _, _, .block hb, _, hF => ⟨.block (prog_rle_ok hb hF), loads_nil_ok⟩
  | _, _, _, _, _, .loop a hc hb, _, _ =>
      ⟨.loop a hc (prog_rle_ok hb loads_nil_ok), loads_nil_ok⟩

theorem prog_rle_ok : {Γ Δ : Ctx} → {K : Kinds} → {P : Solidity.Prog C Γ Δ} →
    ProgOk K P → {F : List (LEnt C Γ)} → LoadsOk F → ProgOk K (Prog.rle F P)
  | _, _, _, _, .nil, _, _ => .nil
  | _, _, _, _, .cons hs hp, _, hF =>
      .cons (stmt_rle_ok hs hF).1 (prog_rle_ok hp (stmt_rle_ok hs hF).2)
end

end Solidity.Backend.CompilerOptimizerDomain
