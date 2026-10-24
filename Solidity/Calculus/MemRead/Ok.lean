import Solidity.Calculus.MemRead.Laws

/-!
# Memory reads: lengths and terms that return

The length of an array walked down its memory, and memory terms that
return.

A piece of `Calculus/MemRead.lean`, whose docstring describes the whole.
-/

namespace Solidity

namespace Decide

open Semantics (lookupBy structDef)

variable {C : Contract}

/-! ## The length of an array, walked down its memory -/

section Len

variable {g : State C []} {ν : AEnv}

/-- `new T[](n)`'s `n`, where a storage value term is one. -/
def _root_.Solidity.Op1.newArrArg {a s : Srt} (o : Op1 C a s) (x : LTm C a) :
    Option (LTm C (.val .uint)) :=
  match o, x with
  | .newArr _, x => some x
  | _, _ => none

def LTm.newArrLen? {U : Ty} (S : LTm C (.sv U)) : Option (LTm C (.val .uint)) :=
  match S with
  | .app1 o x => o.newArrArg x
  | _ => none

/-- `len(s, p)` of `sfind(s, p)` at an array path (Lean only): the length a
copy of the stored array keeps. -/
def _root_.Solidity.Op2.sfindLen {a b s : Srt} (o : Op2 C a b s) (x : LTm C a) (y : LTm C b) :
    Option (LTm C (.val .uint)) :=
  match o, x, y with
  | @Op2.sfind _ (.ref (.array _)), x, y => some (.app2 .len x y)
  | _, _, _ => none

def LTm.sfindLen? {U : Ty} (S : LTm C (.sv U)) : Option (LTm C (.val .uint)) :=
  match S with
  | .app2 o x y => o.sfindLen x y
  | _ => none

/-- **An array's length, walked down a memory that returns**: a write keeps every length, an allocation and a copy
every older array's; a fresh dynamic array's is `0`, a copy of
`new T[](n)`'s is `n`, a copy of a stored array's its stored length
(`len(s, p)`, Lean only: solkey copies no storage array to memory).  By the recursor on the depth. -/
def lenAtN (n : Nat) : {E : Ty} → LTm C .mem → LTm C (.ident (.array E)) → LTm C (.val .uint) :=
  Nat.rec (motive := fun _ => {E : Ty} → LTm C .mem → LTm C (.ident (.array E)) →
      LTm C (.val .uint))
    (fun X t => .app2 .mlen X t)
    (fun _ ih {_} X t =>
      match X.memView with
      | .write m _ _ => ih m t
      | .addM m R _ =>
        if t.boundedIn m then ih m t
        else
          match t.identView with
          | .alloc m' R' _ => if m'.beqR m && R' == R then .nat 0 else .app2 .mlen X t
          | _ => .app2 .mlen X t
      | .copySt m _ S =>
        if t.boundedIn m then ih m t
        else
          match t.identView with
          | .copy m' _ S' =>
            if (m'.beqR m || m'.beqR m.stripW) && S'.beqR S then
              match S'.newArrLen? with
              | some x => x
              | none =>
                match S'.sfindLen? with
                | some x => x
                | none => .app2 .mlen X t
            else .app2 .mlen X t
          | _ => .app2 .mlen X t
      | .other => .app2 .mlen X t) n

theorem lenAtN_eval (n : Nat) : ∀ {E : Ty} (X : LTm C .mem) (t : LTm C (.ident (.array E)))
    (μ : Grown g.H (fun _ => Unit)), X.eval g ν = some μ →
    ((lenAtN n X t).eval g ν : Option PrimTy.uint.Denote) = (LTm.app2 .mlen X t).eval g ν := by
  induction n with
  | zero => intro E X t μ _; rfl
  | succ n ih =>
    intro E X t μ hX
    show (match X.memView with
      | .write m _ _ => lenAtN n m t
      | .addM m R _ =>
        if t.boundedIn m then lenAtN n m t
        else
          match t.identView with
          | .alloc m' R' _ => if m'.beqR m && R' == R then .nat 0 else .app2 .mlen X t
          | _ => .app2 .mlen X t
      | .copySt m _ S =>
        if t.boundedIn m then lenAtN n m t
        else
          match t.identView with
          | .copy m' _ S' =>
            if (m'.beqR m || m'.beqR m.stripW) && S'.beqR S then
              match S'.newArrLen? with
              | some x => x
              | none =>
                match S'.sfindLen? with
                | some x => x
                | none => .app2 .mlen X t
            else .app2 .mlen X t
          | _ => .app2 .mlen X t
      | .other => .app2 .mlen X t : LTm C (.val .uint)).eval g ν = _
    split
    · rename_i m T a v hM
      obtain rfl := LTm.memView_write hM
      obtain ⟨μ₀, ad, w, hm, -, -, hw⟩ := LTm.write_some hX
      rw [ih m t μ₀ hm, LTm.mlen_evalT, LTm.mlen_evalT, hm, hX, Option.bind_some, Option.bind_some]
      cases (t.eval g ν : Option Nat) with
      | none => rfl
      | some id => exact (Grown.writeT_lenU hw id).symm
    · rename_i m R hR hM
      obtain rfl := LTm.memView_addM hM
      have hX' := hX
      rw [LTm.eval_app1, Op1.eval_eq_evalM] at hX'
      simp only [Op1.evalM, Option.map_eq_some_iff] at hX'
      obtain ⟨μ₀, hm, rfl⟩ := hX'
      split
      · rename_i hb
        rw [ih m t μ₀ hm, LTm.mlen_evalT, LTm.mlen_evalT, hm, hX, Option.bind_some, Option.bind_some]
        cases ht : (t.eval g ν : Option Nat) with
        | none => rfl
        | some id =>
          exact (Grown.lenU_addM_old μ₀ R hR id (LTm.boundedIn_eval hm t hb id ht)).symm
      · split
        · rename_i m' R' hR' ht
          split
          · rename_i hc
            simp only [Bool.and_eq_true, beq_iff_eq] at hc
            obtain ⟨hmm, rfl⟩ := hc
            cases LTm.sigma_eq_of_beqR hmm
            cases t with
            | app1 o x =>
              cases o <;> simp only [LTm.identView, Op1.identV, reduceCtorEq, IdentV.alloc.injEq] at ht
              obtain ⟨rfl, -, -⟩ := ht
              rw [LTm.mlen_evalT, hX, Option.bind_some, LTm.eval_app1, hm, Op1.eval_eq_evalM]
              simp only [Op1.evalM, Option.map_some, Option.bind_some]
              show some (uintOfNat 0) = Option.map (fun r => (μ₀.heap.allocDefault _ hR).heap.lenU r)
                (HRef.ofId? (μ₀.heap.allocDefault _ hR).H' _ (μ₀.heap.allocDefault _ hR).val.id)
              rw [HRef.ofId?_self (r := ((μ₀.heap.allocDefault _ hR).val : HRef _ _)), Option.map_some]
              refine congrArg some (Subtype.ext ?_)
              rw [uintOfNat_val (by decide)]
              show (0 : Int) = ((μ₀.heap.allocDefault _ hR).heap.len (μ₀.heap.allocDefault _ hR).val .dyn : Int)
              rw [Heap.allocDefault_array_len]; rfl
            | app2 o x y => cases o <;> simp only [LTm.identView, Op2.identV, reduceCtorEq] at ht
            | _ => simp only [LTm.identView, reduceCtorEq] at ht
          · rfl
        · rfl
    · rename_i m U hU S hM
      obtain rfl := LTm.memView_copySt hM
      have hX' := hX
      rw [LTm.eval_app2, Op2.eval_eq_evalM] at hX'
      simp only [Op2.evalM, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hX'
      obtain ⟨μ₀, hm, v, hv, rfl⟩ := hX'
      split
      · rename_i hb
        rw [ih m t μ₀ hm, LTm.mlen_evalT, LTm.mlen_evalT, hm, hX, Option.bind_some, Option.bind_some]
        cases ht : (t.eval g ν : Option Nat) with
        | none => rfl
        | some id =>
          exact (Grown.lenU_copySt_old μ₀ v hU id (LTm.boundedIn_eval hm t hb id ht)).symm
      · split
        · rename_i m' U' hU' S' ht
          split
          · rename_i hc
            split
            · rename_i x hx
              simp only [Bool.and_eq_true] at hc
              obtain ⟨hmm, hSS⟩ := hc
              obtain ⟨μ₁, h₁, e₁⟩ := LTm.base_eval hmm hm
              obtain ⟨hUU, hS⟩ := Sigma.mk.inj (LTm.sigma_eq_of_beqR hSS)
              cases hUU
              cases eq_of_heq hS
              cases t with
              | app2 o x' y' =>
                cases o <;> simp only [LTm.identView, Op2.identV, reduceCtorEq, IdentV.copy.injEq] at ht
                obtain ⟨rfl, rfl, hy⟩ := ht
                cases eq_of_heq hy
                cases y' with
                | app1 o z =>
                  cases o <;> simp only [LTm.newArrLen?, Op1.newArrArg, reduceCtorEq,
                    Option.some.injEq] at hx
                  subst hx
                  have hv' := hv
                  rw [LTm.eval_app1, Op1.eval_eq_evalM] at hv'
                  simp only [Op1.evalM, Option.map_eq_some_iff] at hv'
                  obtain ⟨k, hk, rfl⟩ := hv'
                  rw [hk, LTm.mlen_evalT, hX, Option.bind_some, LTm.eval_app2, h₁, hv,
                    Op2.eval_eq_evalM]
                  show some k = Option.map
                    (fun r => (SVal.copyStToM μ₀.heap (newArrT (RefTy.array E) k _) hU).heap.lenU r)
                    (HRef.ofId? (SVal.copyStToM μ₀.heap (newArrT (RefTy.array E) k _) hU).H' _
                      (SVal.copyStToM μ₁.heap (newArrT (RefTy.array E) k _) hU).val.id)
                  rw [SVal.copyStToM_id_eq _ hU μ₁.heap μ₀.heap e₁]
                  rw [HRef.ofId?_self (r := ((SVal.copyStToM μ₀.heap (newArrT (RefTy.array E) k _)
                    hU).val : HRef _ _)), Option.map_some]
                  refine congrArg some (Subtype.ext ?_)
                  show k.1 = ((SVal.copyStToM μ₀.heap (newArrT (RefTy.array E) k _) hU).heap.len
                    (SVal.copyStToM μ₀.heap (newArrT (RefTy.array E) k _) hU).val .dyn : Int)
                  rw [newArrT_copy_len]
                  have := k.2
                  simp only [PrimTy.inRange, decide_eq_true_eq] at this
                  omega
                | _ => simp only [LTm.newArrLen?, reduceCtorEq] at hx
              | app1 o x' => cases o <;> simp only [LTm.identView, Op1.identV, reduceCtorEq] at ht
              | _ => simp only [LTm.identView, reduceCtorEq] at ht
            · split
              · rename_i x _ hx
                simp only [Bool.and_eq_true] at hc
                obtain ⟨hmm, hSS⟩ := hc
                obtain ⟨μ₁, h₁, e₁⟩ := LTm.base_eval hmm hm
                obtain ⟨hUU, hS⟩ := Sigma.mk.inj (LTm.sigma_eq_of_beqR hSS)
                cases hUU
                cases eq_of_heq hS
                cases t with
                | app2 o x' y' =>
                  cases o <;> simp only [LTm.identView, Op2.identV, reduceCtorEq,
                    IdentV.copy.injEq] at ht
                  obtain ⟨rfl, rfl, hy⟩ := ht
                  cases eq_of_heq hy
                  cases y' with
                  | app2 o st q =>
                    cases o <;> simp only [LTm.sfindLen?, Op2.sfindLen, reduceCtorEq,
                      Option.some.injEq] at hx
                    subst hx
                    have hv' := hv
                    rw [LTm.eval_app2, Op2.eval_eq_evalM] at hv'
                    simp only [Op2.evalM, Option.bind_eq_bind, Option.bind_eq_some_iff] at hv'
                    obtain ⟨s₀, hs₀, r₀, hr₀, hf⟩ := hv'
                    have hlen : ((LTm.app2 Op2.len st q).eval g ν : Option PrimTy.uint.Denote) =
                        Storage.len s₀ r₀ := by
                      rw [LTm.eval_app2, Op2.eval_eq_evalM, hs₀, hr₀]; rfl
                    rw [hlen, LTm.mlen_evalT, hX, Option.bind_some, LTm.eval_app2, h₁, hv,
                      Op2.eval_eq_evalM]
                    show (Storage.len s₀ r₀ : Option PrimTy.uint.Denote) = Option.map
                      (fun r => (SVal.copyStToM μ₀.heap v hU).heap.lenU r)
                      (HRef.ofId? (SVal.copyStToM μ₀.heap v hU).H' _
                        (SVal.copyStToM μ₁.heap v hU).val.id)
                    rw [SVal.copyStToM_id_eq v hU μ₁.heap μ₀.heap e₁]
                    rw [HRef.ofId?_self (r := ((SVal.copyStToM μ₀.heap v hU).val : HRef _ _)),
                      Option.map_some]
                    unfold Storage.len
                    rw [hf]
                    show some (Solidity.lenU (SVal.view v : ArrView _).n (SVal.view v : ArrView _).hn) = _
                    refine congrArg some (Subtype.ext ?_)
                    show ((SVal.view v : ArrView _).n : Int) =
                      ((SVal.copyStToM μ₀.heap v hU).heap.len (SVal.copyStToM μ₀.heap v hU).val
                        .dyn : Int)
                    rw [SVal.copyStToM_array_len]
                  | _ => simp only [LTm.sfindLen?, reduceCtorEq] at hx
                | app1 o x' => cases o <;> simp only [LTm.identView, Op1.identV, reduceCtorEq] at ht
                | _ => simp only [LTm.identView, reduceCtorEq] at ht
              · rfl
          · rfl
        · rfl
    · rfl

end Len

/-! ## Memory terms that return -/

section Ok

variable {g : State C []} {ν : AEnv}

theorem LTm.onSpineAny_eval {k : Srt} {w : LTm C k} {u : Srt} (t : LTm C u)
    (h : w.onSpineAny t = true) (ht : t.eval g ν ≠ none) : w.eval g ν ≠ none := by
  induction t with
  | app1 o x ihx =>
    have hx : x.eval g ν ≠ none := fun hx => ht (LTm.eval_app1_none o x hx)
    simp only [LTm.onSpineAny, Bool.or_eq_true] at h
    rcases h with h | h
    · cases LTm.sigma_eq_of_beqR h; exact hx
    · exact ihx h hx
  | app2 o x y ihx _ =>
    have hx : x.eval g ν ≠ none := fun hx => ht (LTm.eval_app2_none o x y hx)
    simp only [LTm.onSpineAny, Bool.or_eq_true] at h
    rcases h with h | h
    · cases LTm.sigma_eq_of_beqR h; exact hx
    · exact ihx h hx
  | app3 o x y z ihx _ _ =>
    have hx : x.eval g ν ≠ none := fun hx => ht (LTm.eval_app3_none o x y z hx)
    simp only [LTm.onSpineAny, Bool.or_eq_true] at h
    rcases h with h | h
    · cases LTm.sigma_eq_of_beqR h; exact hx
    · exact ihx h hx
  | _ => simp only [LTm.onSpineAny, Bool.false_eq_true] at h

/-- Where `M` returns, `W` on its spine returns, its heap typing below `M`'s. -/
theorem LTm.onSpine_eval {M W : LTm C .mem} (h : M.onSpine W = true)
    {μ : Grown g.H (fun _ => Unit)} (hM : M.eval g ν = some μ) :
    ∃ ω, W.eval g ν = some ω ∧ ω.H' <+: μ.H' := by
  have hW : W.eval g ν ≠ none := by
    rcases Bool.or_eq_true_iff.mp h with h | h
    · obtain rfl := LTm.eq_of_beqR h; rw [hM]; exact nofun
    · exact LTm.onSpineAny_eval M h (by rw [hM]; exact nofun)
  obtain ⟨ω, hω⟩ := Option.ne_none_iff_exists'.1 hW
  exact ⟨ω, hω, LTm.onSpine_grows h hM hω⟩


/-- `LTm.onSpine_eval` up to writes. -/
theorem LTm.onSpineS_eval {M W : LTm C .mem} (h : M.onSpineS W = true)
    {μ : Grown g.H (fun _ => Unit)} (hM : M.eval g ν = some μ) :
    ∃ ω, W.eval g ν = some ω ∧ ω.H' <+: μ.H' := by
  rcases Bool.or_eq_true_iff.mp h with h | h
  · exact LTm.onSpine_eval h hM
  · obtain ⟨μ₁, h₁, e₁⟩ := LTm.stripW_eval hM
    obtain ⟨ω, hω, hext⟩ := LTm.onSpine_eval (Bool.and_eq_true_iff.1 h).2 h₁
    exact ⟨ω, hω, e₁ ▸ hext⟩
/-- A question of returning, about a memory: whether it returns; whether an
identity is an object of its type in it; whether an address resolves and
reads there. -/
inductive MemQ (C : Contract) where
  | mem (M : LTm C .mem)
  | ident {R : RefTy} (t : LTm C (.ident R)) (M : LTm C .mem)
  | addr {T : Ty} (a : LTm C (.addr T)) (M : LTm C .mem)

/-- Every word of `cs` is `true`. -/
def AllT (g : State C []) (ν : AEnv) (cs : List (LTm C (.val .bool))) : Prop :=
  ∀ c ∈ cs, (c.eval g ν : Option Bool) = some true

theorem AllT.append {cs ds : List (LTm C (.val .bool))} :
    AllT g ν (cs ++ ds) ↔ AllT g ν cs ∧ AllT g ν ds :=
  ⟨fun h => ⟨fun c hc => h c (List.mem_append_left _ hc),
      fun c hc => h c (List.mem_append_right _ hc)⟩,
    fun ⟨h₁, h₂⟩ c hc => (List.mem_append.1 hc).elim (h₁ c) (h₂ c)⟩

theorem AllT.nil : AllT g ν ([] : List (LTm C (.val .bool))) := fun _ h => nomatch h

theorem AllT.single {c : LTm C (.val .bool)} :
    AllT g ν [c] ↔ (c.eval g ν : Option Bool) = some true := by
  constructor
  · intro h; exact h c (List.mem_singleton_self c)
  · intro h c' hc; rw [List.mem_singleton.1 hc]; exact h

/-- `(t; true)`: `true` where `t` returns. -/
def LTm.retsC {s : Srt} (t : LTm C s) : LTm C (.val .bool) := .seq t .tt

theorem LTm.retsC_true {s : Srt} (t : LTm C s) :
    AllT g ν [t.retsC] ↔ (t.eval g ν).isSome = true := by
  rw [AllT.single, LTm.retsC, LTm.eval_seq]
  cases t.eval g ν with
  | none => exact ⟨fun h => (nomatch h), fun h => (nomatch h)⟩
  | some _ => exact ⟨fun _ => rfl, fun _ => rfl⟩

/-- The word a guard comes to: `c` of `if (c) then · else err`, `d`
returning of `d; ·`. -/
def GFrame.cond? : GFrame C → Option (LTm C (.val .bool))
  | .kite (p := .bool) c b => if b.isTT then some c else none
  | .kite _ _ => none
  | .seq d => some d.retsC

theorem GFrame.cond?_iff {f : GFrame C} {c : LTm C (.val .bool)} (h : f.cond? = some c) :
    f.Holds g ν ↔ (c.eval g ν : Option Bool) = some true := by
  cases f with
  | kite a b =>
    rename_i p
    cases p with
    | bool =>
      simp only [GFrame.cond?] at h
      split at h
      · rename_i hb
        cases h
        have hb' := LTm.isTT_eval (g := g) (ν := ν) hb
        constructor
        · rintro ⟨x, hx, hy⟩
          rw [hb'] at hy
          cases hy
          exact hx
        · intro hc
          exact ⟨true, hc, hb'⟩
      · cases h
    | uint | int => simp only [GFrame.cond?, reduceCtorEq] at h
  | seq d =>
    simp only [GFrame.cond?, Option.some.injEq] at h
    subst h
    rw [← AllT.single, LTm.retsC_true]
    rfl

/-- The words the guards `fs` come to. -/
def framesCond? (fs : List (GFrame C)) : Option (List (LTm C (.val .bool))) :=
  fs.mapM GFrame.cond?

theorem framesCond?_iff : (fs : List (GFrame C)) → {cs : List (LTm C (.val .bool))} →
    framesCond? fs = some cs → ((∀ f ∈ fs, f.Holds g ν) ↔ AllT g ν cs)
  | [], cs, h => by
    simp only [framesCond?, List.mapM_nil, pure, Option.some.injEq] at h
    subst h
    exact ⟨fun _ => AllT.nil, fun _ f hf => nomatch hf⟩
  | f :: fs, cs, h => by
    simp only [framesCond?, List.mapM_cons, bind, pure, Option.bind_eq_some_iff,
      Option.some.injEq] at h
    obtain ⟨c, hc, cs', hcs', rfl⟩ := h
    have H := framesCond?_iff fs hcs'
    rw [show c :: cs' = [c] ++ cs' from rfl, AllT.append, AllT.single, ← GFrame.cond?_iff hc, ← H]
    simp only [List.mem_cons, forall_eq_or_imp]

open Classical in
/-- A guarded term returns where its guards hold and what they guard returns. -/
theorem LTm.eval_peel {s : Srt} (t : LTm C s) :
    t.eval g ν = if ∀ f ∈ t.peel.1, f.Holds g ν then t.peel.2.eval g ν else none := by
  classical
  rw [← LTm.peel_eval, wrapP_eval]

/-- **What a question's words say**: a memory returns exactly where they
are `true`; where the memory returns, an identity is an object of its type
there, and an address resolves and reads, where they are, and they are
where the identity or the address returns so. -/
def MemQ.HoldsC (g : State C []) (ν : AEnv) : MemQ C → List (LTm C (.val .bool)) → Prop
  | .mem M, cs => (M.eval g ν : Option (Grown g.H (fun _ => Unit))).isSome = true ↔ AllT g ν cs
  | @MemQ.ident _ R t M, cs => ∀ μ, (M.eval g ν : Option (Grown g.H (fun _ => Unit))) = some μ →
      (AllT g ν cs → ∃ id, (t.eval g ν : Option Nat) = some id ∧ μ.H'[id]? = some R) ∧
      ((t.eval g ν : Option Nat).isSome = true → AllT g ν cs)
  | @MemQ.addr _ T a M, cs => ∀ μ, (M.eval g ν : Option (Grown g.H (fun _ => Unit))) = some μ →
      (AllT g ν cs → ∃ ad ra, (a.eval g ν : Option (MAddrT T)) = some ad ∧
        ad.resolve μ.H' = some ra ∧ (μ.heap.readAddr ra).isSome = true) ∧
      (∀ ad ra, (a.eval g ν : Option (MAddrT T)) = some ad → ad.resolve μ.H' = some ra →
        (μ.heap.readAddr ra).isSome = true → AllT g ν cs)

/-- An address term's object, where it is a member. -/
def _root_.Solidity.Op1.fieldObj {a s : Srt} (o : Op1 C a s) (x : LTm C a) :
    Option ((R : RefTy) × LTm C (.ident R)) :=
  match o, x with
  | .mfield _, x => some ⟨_, x⟩
  | _, _ => none

/-- A member address's object. -/
def LTm.fieldObj? {s : Srt} (a : LTm C s) : Option ((R : RefTy) × LTm C (.ident R)) :=
  match a with
  | .app1 o x => o.fieldObj x
  | _ => none

/-- An address term's array, its kind and the index, where it is an
element. -/
def _root_.Solidity.Op2.matObj {a b s : Srt} (o : Op2 C a b s) (x : LTm C a) (y : LTm C b) :
    Option ((R : RefTy) × (E : Ty) × ArrTy R E × LTm C (.ident R) × LTm C (.val .uint)) :=
  match o, x, y with
  | .mat arr, x, y => some ⟨_, _, arr, x, y⟩
  | _, _, _ => none

/-- An element address's array and index. -/
def LTm.matObj? {s : Srt} (a : LTm C s) :
    Option ((R : RefTy) × (E : Ty) × ArrTy R E × LTm C (.ident R) × LTm C (.val .uint)) :=
  match a with
  | .app2 o x y => o.matObj x y
  | _ => none

/-- A memory value term's identity, where it writes one. -/
def _root_.Solidity.Op1.refArg {a s : Srt} (o : Op1 C a s) (x : LTm C a) :
    Option ((R : RefTy) × LTm C (.ident R)) :=
  match o, x with
  | .ref, x => some ⟨_, x⟩
  | _, _ => none

/-- A copy's source that returns: a fresh array of a length that does. -/
def _root_.Solidity.Op1.svOk {a s : Srt} (o : Op1 C a s) (x : LTm C a) : Bool :=
  match o, x with
  | .newArr _, x => x.retsS
  | _, _ => false

theorem retsS_isSome {s : Srt} {t : LTm C s} (h : t.retsS = true) :
    (t.eval g ν).isSome = true := by
  obtain ⟨v, hv⟩ := LTm.retsS_eval (g := g) (ν := ν) h
  rw [hv]; rfl

/-- The words a copy's source returns at: none for a fresh array of a
length that returns. -/
def svConds {U : Ty} (S : LTm C (.sv U)) : List (LTm C (.val .bool)) :=
  match S with
  | .app1 o x => if o.svOk x then [] else [S.retsC]
  | _ => [S.retsC]

theorem svConds_iff {U : Ty} (S : LTm C (.sv U)) :
    (S.eval g ν : Option (SVal U)).isSome = true ↔ AllT g ν (svConds S) := by
  cases S with
  | app1 o x =>
    show _ ↔ AllT g ν (if o.svOk x then [] else [(LTm.app1 o x).retsC])
    split
    · rename_i hok
      refine ⟨fun _ => AllT.nil, fun _ => ?_⟩
      cases o <;> simp only [Op1.svOk, Bool.false_eq_true] at hok
      obtain ⟨w, hw⟩ := Option.isSome_iff_exists.1 (retsS_isSome (g := g) (ν := ν) hok)
      rw [LTm.eval_app1, hw]; rfl
    · exact (LTm.retsC_true _).symm
  | _ => exact (LTm.retsC_true _).symm

/-- **An index within an array's bounds** (`memoryIndexInBounds`), in a
memory that returns: below its length walked down the memory (`lenAtN`),
or below a fixed array's. -/
def lenCond {R : RefTy} {E : Ty} (arr : ArrTy R E) (M : LTm C .mem) (t : LTm C (.ident R))
    (i : LTm C (.val .uint)) : LTm C (.val .bool) :=
  match R, arr, t with
  | _, .dyn, t => .lt i (lenAtN memFuel M t)
  | _, @ArrTy.fixed _ n, _ => if n < 2 ^ 256 then .lt i (.nat n) else i.retsC

theorem lenCond_iff {R : RefTy} {E : Ty} (arr : ArrTy R E) (M : LTm C .mem)
    (t : LTm C (.ident R)) (i : LTm C (.val .uint)) {μ : Grown g.H (fun _ => Unit)}
    (hM : M.eval g ν = some μ) {id : Nat} (ht : (t.eval g ν : Option Nat) = some id)
    {r : HRef μ.H' R} (hr : HRef.ofId? μ.H' R id = some r) :
    ((lenCond arr M t i).eval g ν : Option Bool) = some true ↔
      ∃ k : PrimTy.uint.Denote, (i.eval g ν : Option _) = some k ∧ k.1.toNat < μ.heap.len r arr := by
  have k0 : ∀ k : PrimTy.uint.Denote, 0 ≤ k.1 := fun k => by
    have := k.2
    simp only [PrimTy.inRange, decide_eq_true_eq] at this
    omega
  have klt : ∀ k : PrimTy.uint.Denote, k.1 < 2 ^ 256 := fun k => by
    have := k.2
    simp only [PrimTy.inRange, decide_eq_true_eq] at this
    omega
  cases arr with
  | dyn =>
    show ((LTm.lt i (lenAtN memFuel M t)).eval g ν : Option Bool) = some true ↔ _
    rw [LTm.eval_lt, lenAtN_eval memFuel M t μ hM, LTm.mlen_evalT, hM, Option.bind_some, ht,
      Option.bind_some, hr, Option.map_some]
    cases (i.eval g ν : Option PrimTy.uint.Denote) with
    | none => exact ⟨fun h => (nomatch h), fun ⟨_, hk, _⟩ => (nomatch hk)⟩
    | some k =>
      simp only [Option.bind_some, Option.map_some, Option.some.injEq, decide_eq_true_eq]
      have e : (μ.heap.lenU r).1 = (μ.heap.len r .dyn : Int) := rfl
      have := k0 k
      constructor
      · intro hlt; exact ⟨k, rfl, by omega⟩
      · rintro ⟨k', hk', hlt⟩; cases hk'; omega
  | @fixed E n =>
    have hlen : μ.heap.len r .fixed = n := by
      unfold Heap.len; rw [MObj.elems_fixed]
      exact (μ.heap.get r : {l : List (MVal μ.H' E) // l.length = n}).2
    rw [hlen]
    show ((if n < 2 ^ 256 then LTm.lt i (.nat n) else i.retsC).eval g ν : Option Bool) = some true ↔ _
    split
    · rename_i hn
      rw [LTm.eval_lt, LTm.eval_nat]
      cases (i.eval g ν : Option PrimTy.uint.Denote) with
      | none => exact ⟨fun h => (nomatch h), fun ⟨_, hk, _⟩ => (nomatch hk)⟩
      | some k =>
        simp only [Option.bind_some, Option.map_some, Option.some.injEq, decide_eq_true_eq,
          uintOfNat_val hn]
        have := k0 k
        constructor
        · intro hlt; exact ⟨k, rfl, by omega⟩
        · rintro ⟨k', hk', hlt⟩; cases hk'; omega
    · rename_i hn
      rw [← AllT.single, LTm.retsC_true]
      cases (i.eval g ν : Option PrimTy.uint.Denote) with
      | none => exact ⟨fun h => (nomatch h), fun ⟨_, hk, _⟩ => (nomatch hk)⟩
      | some k =>
        have := klt k
        have := k0 k
        exact ⟨fun _ => ⟨k, rfl, by omega⟩, fun _ => rfl⟩

/-- One step of the returning check: the words each question comes to. -/
def memCondStep (ih : MemQ C → Option (List (LTm C (.val .bool)))) :
    MemQ C → Option (List (LTm C (.val .bool)))
  | .mem M =>
    match M.memView with
    | .write m a v =>
      (ih (.mem m)).bind fun c₁ => (ih (.addr a m)).bind fun c₂ =>
        (match v with
          | .app1 o x =>
            match o.refArg x with
            | some ⟨_, t⟩ => ih (.ident t m)
            | none =>
              some (if ({} : Facts C).returns (({} : Facts C).nf x) then [] else [x.retsC])
          | _ => none).map fun c₃ => c₁ ++ c₂ ++ c₃
    | .addM m _ _ => ih (.mem m)
    | .copySt m _ S =>
      (ih (.mem m)).map fun c => c ++ svConds S
    | .other => if M.retsS then some [] else none
  | .ident t M =>
    if t.peel.1.isEmpty then
      match t.identView with
      | .alloc m R h => if M.onSpine (.app1 (.addM R h) m) then some [] else none
      | .copy m h S => if M.onSpineS (.app2 (.copySt h) m S) then some [] else none
      | .iread X b => if M.onSpine X then ih (.addr b X) else none
      | .other => none
    else (framesCond? t.peel.1).bind fun c₀ => (ih (.ident t.peel.2 M)).map fun c => c₀ ++ c
  | .addr a M =>
    match a.fieldObj? with
    | some ⟨_, t⟩ => ih (.ident t M)
    | none =>
      match a.matObj? with
      | some ⟨_, _, arr, t, i⟩ => (ih (.ident t M)).map fun c => c ++ [lenCond arr M t i]
      | none => none

/-- **When a memory term returns, read on the terms** `n` deep: the words
it comes to — each write lands (a member of an object of the memory, or an
element within its array's bounds; its value a word or an identity there),
each copy copies a source that returns.  By the recursor on the depth. -/
def memCondN (n : Nat) : MemQ C → Option (List (LTm C (.val .bool))) :=
  Nat.rec (motive := fun _ => MemQ C → Option (List (LTm C (.val .bool)))) (fun _ => none)
    (fun _ ih => memCondStep ih) n


/-- **What the check says holds.** -/
theorem memCondN_sound (n : Nat) :
    ∀ (q : MemQ C) (cs : List (LTm C (.val .bool))), memCondN n q = some cs → q.HoldsC g ν cs := by
  induction n with
  | zero => intro q cs h; cases h
  | succ n ih =>
    intro q cs h
    cases q with
    | mem M =>
      show (M.eval g ν : Option (Grown g.H (fun _ => Unit))).isSome = true ↔ AllT g ν cs
      simp only [memCondN, memCondStep] at h
      split at h
      · rename_i m T a v hX
        obtain rfl := LTm.memView_write hX
        obtain ⟨c₁, h₁, h⟩ := Option.bind_eq_some_iff.1 h
        obtain ⟨c₂, h₂, h⟩ := Option.bind_eq_some_iff.1 h
        obtain ⟨c₃, h₃, rfl⟩ := Option.map_eq_some_iff.1 h
        have H₁ := ih _ _ h₁
        have H₂ := ih _ _ h₂
        have H₃ : ∀ μ, (m.eval g ν : Option (Grown g.H (fun _ => Unit))) = some μ →
            (AllT g ν c₃ → ∃ w mv, (v.eval g ν : Option (MvT T)) = some w ∧
              MvT.toMVal μ.H' T w = some mv) ∧
            ((v.eval g ν : Option (MvT T)).isSome = true → AllT g ν c₃) := by
          intro μ hμ
          cases v with
          | app1 o x =>
            simp only at h₃
            split at h₃
            · rename_i R' t hr
              cases o <;> simp only [Op1.refArg, reduceCtorEq, Option.some.injEq] at hr
              obtain ⟨rfl, hh⟩ := Sigma.mk.inj hr
              cases hh
              have HI := ih _ _ h₃ μ hμ
              refine ⟨fun hc => ?_, fun hv => HI.2 ?_⟩
              · obtain ⟨id, hid, hty⟩ := HI.1 hc
                refine ⟨id, ⟨id, hty⟩, ?_, ?_⟩
                · rw [LTm.eval_app1, hid]; rfl
                · simp only [MvT.toMVal, HRef.ofId?, hty, dite_true]
              · cases ht : (x.eval g ν : Option Nat) with
                | none => rw [LTm.eval_app1_none _ _ ht] at hv; cases hv
                | some _ => rfl
            · rename_i hr
              cases o <;> simp only [Op1.refArg, reduceCtorEq] at hr
              simp only [Option.some.injEq] at h₃
              subst h₃
              split
              · rename_i hv
                refine ⟨fun _ => ?_, fun _ => AllT.nil⟩
                have hv' := Facts.returns_sound (g := g) (ν := ν) (Facts.ok_empty ν) _ hv
                rw [Facts.nf_eval (Facts.ok_empty ν)] at hv'
                obtain ⟨w, hw⟩ := Option.isSome_iff_exists.1 hv'
                exact ⟨w, w, by rw [LTm.eval_app1, hw]; rfl, rfl⟩
              · refine ⟨fun hc => ?_, fun hv => (LTm.retsC_true x).2 ?_⟩
                · obtain ⟨w, hw⟩ := Option.isSome_iff_exists.1 ((LTm.retsC_true x).1 hc)
                  exact ⟨w, w, by rw [LTm.eval_app1, hw]; rfl, rfl⟩
                · cases hx : x.eval g ν with
                  | none => rw [LTm.eval_app1_none _ _ hx] at hv; cases hv
                  | some _ => rfl
          | _ => simp only [reduceCtorEq] at h₃
        rw [AllT.append, AllT.append]
        constructor
        · intro hW
          obtain ⟨μ', hμ'⟩ := Option.isSome_iff_exists.1 hW
          obtain ⟨μ, ad, w, hm, ha, hv, hw⟩ := LTm.write_some hμ'
          unfold Grown.writeT at hw
          simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at hw
          obtain ⟨ra, hra, mv, hmv, hp, hhp, -⟩ := hw
          refine ⟨⟨H₁.1 (by rw [hm]; rfl), (H₂ μ hm).2 ad ra ha hra ?_⟩,
            (H₃ μ hm).2 (by rw [hv]; rfl)⟩
          rw [← Heap.writeAddr_isSome _ _ mv, hhp]; rfl
        · rintro ⟨⟨a₁, a₂⟩, a₃⟩
          obtain ⟨μ, hμ⟩ := Option.isSome_iff_exists.1 (H₁.2 a₁)
          obtain ⟨ad, ra, had, hra, hrd⟩ := (H₂ μ hμ).1 a₂
          obtain ⟨w, mv, hvw, hmv⟩ := (H₃ μ hμ).1 a₃
          obtain ⟨hp, hhp⟩ := Option.isSome_iff_exists.1
            ((Heap.writeAddr_isSome μ.heap ra mv).trans hrd)
          rw [LTm.eval_app3, hμ, had, hvw, Op3.eval_eq_evalM]
          simp only [Op3.evalM, Grown.writeT, Option.bind_eq_bind, Option.bind_some, hra, hmv, hhp]
          rfl
      · rename_i m R hR hX
        obtain rfl := LTm.memView_addM hX
        have H : (m.eval g ν : Option (Grown g.H (fun _ => Unit))).isSome = true ↔ AllT g ν cs :=
          ih _ _ h
        rw [← H, LTm.eval_app1, Op1.eval_eq_evalM]
        simp only [Op1.evalM, Option.isSome_map]
      · rename_i m U hU S hX
        obtain rfl := LTm.memView_copySt hX
        obtain ⟨c, h₁, rfl⟩ := Option.map_eq_some_iff.1 h
        have hS := svConds_iff (g := g) (ν := ν) S
        have H : (m.eval g ν : Option (Grown g.H (fun _ => Unit))).isSome = true ↔ AllT g ν c :=
          ih _ _ h₁
        rw [AllT.append, ← H, ← hS, LTm.eval_app2, Op2.eval_eq_evalM]
        cases (m.eval g ν : Option (Grown g.H (fun _ => Unit))) <;>
          cases (S.eval g ν : Option (SVal U)) <;>
          simp only [Op2.evalM, Option.bind_eq_bind, Option.bind_none, Option.bind_some,
            Option.isSome_none, Option.isSome_some, Bool.false_eq_true, and_false, false_and,
            and_self, iff_self]
      · split at h
        · rename_i hr
          cases h
          exact ⟨fun _ => AllT.nil, fun _ => retsS_isSome hr⟩
        · cases h
    | ident t M =>
      intro μ hμ
      simp only [memCondN, memCondStep] at h
      by_cases hpe : t.peel.1.isEmpty = true
      case neg =>
        rw [if_neg hpe] at h
        obtain ⟨c₀, h₀, h⟩ := Option.bind_eq_some_iff.1 h
        obtain ⟨c₁, h₁, rfl⟩ := Option.map_eq_some_iff.1 h
        have HF := framesCond?_iff (g := g) (ν := ν) _ h₀
        have HI := ih _ _ h₁ μ hμ
        classical
        rw [AllT.append, LTm.eval_peel t]
        refine ⟨fun ⟨a₀, a₁⟩ => ?_, fun ht => ?_⟩
        · rw [if_pos (HF.2 a₀)]; exact HI.1 a₁
        · split at ht
          · rename_i hf
            exact ⟨HF.1 hf, HI.2 ht⟩
          · cases ht
      rw [if_pos hpe] at h
      split at h
      · rename_i m R' hR ht
        split at h
        · rename_i hsp
          cases h
          refine ⟨fun _ => ?_, fun _ => AllT.nil⟩
          cases t with
          | app1 o x =>
            cases o <;> simp only [LTm.identView, Op1.identV, reduceCtorEq] at ht
            simp only [IdentV.alloc.injEq] at ht
            obtain ⟨rfl, rfl⟩ := ht
            obtain ⟨ω, hω, hext⟩ := LTm.onSpine_eval hsp hμ
            rw [LTm.eval_app1, Op1.eval_eq_evalM] at hω
            simp only [Op1.evalM, Option.map_eq_some_iff] at hω
            obtain ⟨μ₀, hμ₀, rfl⟩ := hω
            refine ⟨(μ₀.heap.allocDefault _ hR).val.id, ?_, ?_⟩
            · rw [LTm.eval_app1, hμ₀, Op1.eval_eq_evalM]; rfl
            · exact HTy.getElem?_of_prefix hext (μ₀.heap.allocDefault _ hR).val.get?
          | app2 o x y => cases o <;> simp only [LTm.identView, Op2.identV, reduceCtorEq] at ht
          | _ => simp only [LTm.identView, reduceCtorEq] at ht
        · cases h
      · rename_i m U hU S ht
        split at h
        · rename_i hsp
          cases h
          refine ⟨fun _ => ?_, fun _ => AllT.nil⟩
          cases t with
          | app1 o x => cases o <;> simp only [LTm.identView, Op1.identV, reduceCtorEq] at ht
          | app2 o x y =>
            cases o <;> simp only [LTm.identView, Op2.identV, reduceCtorEq] at ht
            simp only [IdentV.copy.injEq] at ht
            obtain ⟨rfl, hU', hS⟩ := ht
            subst hU'
            cases hS
            obtain ⟨ω, hω, hext⟩ := LTm.onSpineS_eval hsp hμ
            rw [LTm.eval_app2, Op2.eval_eq_evalM] at hω
            simp only [Op2.evalM, Option.bind_eq_bind, Option.bind_eq_some_iff,
              Option.some.injEq] at hω
            obtain ⟨μ₀, hμ₀, v, hv, rfl⟩ := hω
            refine ⟨(v.copyStToM μ₀.heap hU).val.id, ?_, ?_⟩
            · rw [LTm.eval_app2, hμ₀, hv, Op2.eval_eq_evalM]; rfl
            · exact HTy.getElem?_of_prefix hext (v.copyStToM μ₀.heap hU).val.get?
          | _ => simp only [LTm.identView, reduceCtorEq] at ht
        · cases h
      · rename_i X T b ht
        split at h
        · rename_i hX
          cases t with
          | app1 o x => cases o <;> simp only [LTm.identView, Op1.identV, reduceCtorEq] at ht
          | app2 o x y =>
            cases o <;> simp only [LTm.identView, Op2.identV, reduceCtorEq] at ht
            simp only [IdentV.iread.injEq] at ht
            obtain ⟨rfl, hT, hb'⟩ := ht
            subst hT
            cases hb'
            obtain ⟨ξ, hξ, hext⟩ := LTm.onSpine_eval hX hμ
            have HA := ih _ _ h ξ hξ
            refine ⟨fun hc => ?_, fun hi => ?_⟩
            · obtain ⟨ad, ra, had, hra, hrd⟩ := HA.1 hc
              obtain ⟨r, hr⟩ := Option.isSome_iff_exists.1 hrd
              refine ⟨r.id, ?_, HTy.getElem?_of_prefix hext r.get?⟩
              rw [LTm.iread_evalT, hξ, had, Option.bind_some, Option.bind_some, hra,
                Option.bind_some, hr]
              rfl
            · rw [LTm.iread_evalT, hξ, Option.bind_some] at hi
              cases hb : (y.eval g ν : Option (MAddrT _)) with
              | none => rw [hb] at hi; cases hi
              | some ad =>
                rw [hb, Option.bind_some] at hi
                cases hra : ad.resolve ξ.H' with
                | none => rw [hra] at hi; cases hi
                | some ra =>
                  rw [hra, Option.bind_some] at hi
                  refine HA.2 ad ra hb hra ?_
                  cases hrd : ξ.heap.readAddr ra with
                  | none => rw [hrd] at hi; cases hi
                  | some _ => rfl
          | _ => simp only [LTm.identView, reduceCtorEq] at ht
        · cases h
      · cases h
    | addr a M =>
      intro μ hμ
      simp only [memCondN, memCondStep] at h
      split at h
      · rename_i R t ht
        cases a with
        | app1 o x =>
          cases o <;> simp only [LTm.fieldObj?, Op1.fieldObj, reduceCtorEq, Option.some.injEq] at ht
          obtain ⟨rfl, ht⟩ := Sigma.mk.inj ht
          cases ht
          rename_i s f T hf
          have HI := ih _ _ h μ hμ
          refine ⟨fun hc => ?_, fun ad ra had _ _ => HI.2 ?_⟩
          · obtain ⟨id, hid, hty⟩ := HI.1 hc
            refine ⟨.field id hf, .field ⟨id, hty⟩ hf, ?_, ?_, rfl⟩
            · rw [LTm.eval_app1, hid]; rfl
            · simp only [MAddrT.resolve_eq_resolveM, MAddrT.resolveM, HRef.ofId?, hty, dite_true,
                Option.map_some]
          · cases hx : (x.eval g ν : Option Nat) with
            | none => rw [LTm.eval_app1_none _ _ hx] at had; cases had
            | some _ => rfl
        | _ => simp only [LTm.fieldObj?, reduceCtorEq] at ht
      · split at h
        · rename_i R E arr t i _ hm
          obtain ⟨c, h₁, rfl⟩ := Option.map_eq_some_iff.1 h
          have HI := ih _ _ h₁ μ hμ
          cases a with
          | app2 o x y =>
            cases o <;> simp only [LTm.matObj?, Op2.matObj, reduceCtorEq, Option.some.injEq] at hm
            cases hm
            rename_i k arr _
            have hev : ∀ id (kv : PrimTy.uint.Denote), (i.eval g ν : Option Nat) = some id →
                (k.eval g ν : Option PrimTy.uint.Denote) = some kv →
                ((LTm.app2 (.mat arr) i k).eval g ν : Option (MAddrT _)) =
                  some (.index id arr kv) := by
              intro id kv h1 h2; rw [LTm.eval_app2, h1, h2, Op2.eval_eq_evalM]; rfl
            rw [AllT.append]
            refine ⟨fun ⟨a₁, a₂⟩ => ?_, fun ad ra had hra hrd => ⟨?_, ?_⟩⟩
            · obtain ⟨id, hid, hty⟩ := HI.1 a₁
              have hr : HRef.ofId? μ.H' E id = some ⟨id, hty⟩ := by
                simp only [HRef.ofId?, hty, dite_true]
              obtain ⟨kv, hk, hlt⟩ := (lenCond_iff arr M i k hμ hid hr).1 (AllT.single.1 a₂)
              refine ⟨.index id arr kv, .index ⟨id, hty⟩ arr kv, hev id kv hid hk, ?_, ?_⟩
              · simp only [MAddrT.resolve_eq_resolveM, MAddrT.resolveM, hr, Option.map_some]
              · rw [Heap.readAddr_index_isSome]
                simp only [decide_eq_true_eq]
                exact hlt
            · apply HI.2
              cases hx : (i.eval g ν : Option Nat) with
              | none => rw [LTm.eval_app2_none _ _ _ hx] at had; cases had
              | some _ => rfl
            · cases hx : (i.eval g ν : Option Nat) with
              | none => rw [LTm.eval_app2_none _ _ _ hx] at had; cases had
              | some id =>
                cases hk : (k.eval g ν : Option PrimTy.uint.Denote) with
                | none => rw [LTm.eval_app2, hx, hk, Op2.eval_eq_evalM] at had; cases had
                | some kv =>
                  rw [hev id kv hx hk] at had
                  cases had
                  simp only [MAddrT.resolve_eq_resolveM, MAddrT.resolveM,
                    Option.map_eq_some_iff] at hra
                  obtain ⟨r, hr, rfl⟩ := hra
                  rw [Heap.readAddr_index_isSome] at hrd
                  simp only [decide_eq_true_eq] at hrd
                  exact AllT.single.2 ((lenCond_iff arr M i k hμ hx hr).2 ⟨kv, hk, hrd⟩)
          | _ => simp only [LTm.matObj?, reduceCtorEq] at hm
        · cases h

/-- The memory an identity term's returning is read in. -/
def LTm.identMem? {s : Srt} (t : LTm C s) : Option (LTm C .mem) :=
  match t.identView with
  | .alloc m R h => some (.app1 (.addM R h) m)
  | .copy m h S => some (.app2 (.copySt h) m S)
  | .iread X _ => some X
  | .other => none

theorem LTm.identMem?_rets {R : RefTy} {t : LTm C (.ident R)} {M : LTm C .mem}
    (h : t.identMem? = some M) (ht : (t.eval g ν : Option Nat).isSome = true) :
    (M.eval g ν : Option (Grown g.H (fun _ => Unit))).isSome = true := by
  unfold LTm.identMem? at h
  split at h
  · rename_i m R' hR ht'
    cases h
    cases t with
    | app1 o x =>
      cases o <;> simp only [LTm.identView, Op1.identV, reduceCtorEq, IdentV.alloc.injEq] at ht'
      obtain ⟨rfl, -⟩ := ht'
      cases hx : (x.eval g ν : Option (Grown g.H (fun _ => Unit))) with
      | none => rw [LTm.eval_app1_none _ _ hx] at ht; cases ht
      | some μ => rw [LTm.eval_app1, hx, Op1.eval_eq_evalM]; rfl
    | app2 o x y => cases o <;> simp only [LTm.identView, Op2.identV, reduceCtorEq] at ht'
    | _ => simp only [LTm.identView, reduceCtorEq] at ht'
  · rename_i m U hU S ht'
    cases h
    cases t with
    | app1 o x => cases o <;> simp only [LTm.identView, Op1.identV, reduceCtorEq] at ht'
    | app2 o x y =>
      cases o <;> simp only [LTm.identView, Op2.identV, reduceCtorEq, IdentV.copy.injEq] at ht'
      obtain ⟨rfl, rfl, hy⟩ := ht'
      cases eq_of_heq hy
      cases hx : (x.eval g ν : Option (Grown g.H (fun _ => Unit))) with
      | none => rw [LTm.eval_app2_none _ _ _ hx] at ht; cases ht
      | some μ =>
        cases hy' : (y.eval g ν : Option (SVal _)) with
        | none =>
          rw [LTm.eval_app2, hx, hy', Op2.eval_eq_evalM] at ht; cases ht
        | some v => rw [LTm.eval_app2, hx, hy', Op2.eval_eq_evalM]; rfl
    | _ => simp only [LTm.identView, reduceCtorEq] at ht'
  · rename_i X T b ht'
    cases h
    cases t with
    | app1 o x => cases o <;> simp only [LTm.identView, Op1.identV, reduceCtorEq] at ht'
    | app2 o x y =>
      cases o <;> simp only [LTm.identView, Op2.identV, reduceCtorEq, IdentV.iread.injEq] at ht'
      obtain ⟨rfl, -⟩ := ht'
      cases hx : (x.eval g ν : Option (Grown g.H (fun _ => Unit))) with
      | none => rw [LTm.eval_app2_none _ _ _ hx] at ht; cases ht
      | some μ => rfl
    | _ => simp only [LTm.identView, reduceCtorEq] at ht'
  · cases h

/-- A copy into storage, viewed: its memory and object. -/
def _root_.Solidity.Op2.copyMemV {a b s : Srt} (o : Op2 C a b s) (x : LTm C a) (y : LTm C b) :
    Option ((R : RefTy) × LTm C .mem × LTm C (.ident R)) :=
  match o, x, y with
  | .copyMem, x, y => some ⟨_, x, y⟩
  | _, _, _ => none

/-- A copy into storage's memory and object. -/
def LTm.copyMemV? {s : Srt} (t : LTm C s) : Option ((R : RefTy) × LTm C .mem × LTm C (.ident R)) :=
  match t with
  | .app2 o x y => o.copyMemV x y
  | _ => none

theorem LTm.copyMem_isSome {R : RefTy} (M : LTm C .mem) (t : LTm C (.ident R)) :
    ((LTm.app2 .copyMem M t).eval g ν : Option (SVal (.ref R))).isSome = true ↔
      ∃ μ : Grown g.H (fun _ => Unit), M.eval g ν = some μ ∧
        ∃ id, (t.eval g ν : Option Nat) = some id ∧ μ.H'[id]? = some R := by
  rw [LTm.eval_app2, Op2.eval_eq_evalM]
  cases hm : (M.eval g ν : Option (Grown g.H (fun _ => Unit))) with
  | none => exact ⟨fun h => (nomatch h), fun ⟨_, h, _⟩ => (nomatch h)⟩
  | some μ =>
    cases ht : (t.eval g ν : Option Nat) with
    | none => exact ⟨fun h => (nomatch h), fun ⟨_, _, _, h, _⟩ => (nomatch h)⟩
    | some id =>
      show ((HRef.ofId? μ.H' R id).bind fun r =>
        some (MVal.copyMToSt μ.heap (T := .ref R) r)).isSome = true ↔ _
      unfold HRef.ofId?
      by_cases hid : μ.H'[id]? = some R
      · simp only [hid, dite_true, Option.bind_some, Option.isSome_some, true_iff]
        exact ⟨μ, rfl, id, rfl, hid⟩
      · simp only [hid, dite_false, Option.bind_none, Option.isSome_none, Bool.false_eq_true,
          false_iff, not_exists, not_and]
        intro μ' hμ' id' hid' hR
        cases hμ'
        cases hid'
        exact hid hR

/-- The words a guard's returning comes to: a memory's, an identity's in
its memory. -/
def guardQ {s : Srt} (d : LTm C s) : Option (List (LTm C (.val .bool))) :=
  match (d.castTo? : Option (LTm C .mem)) with
  | some M => memCondN memFuel (.mem M)
  | none =>
    match s, d with
    | .ident _, d =>
      if d.peel.1.isEmpty then
        d.identMem?.bind fun M => (memCondN memFuel (.mem M)).bind fun c₁ =>
          (memCondN memFuel (.ident d M)).map fun c₂ => c₁ ++ c₂
      else
        (framesCond? d.peel.1).bind fun c₀ =>
          (d.peel.2.identMem?.bind fun M => (memCondN memFuel (.mem M)).bind fun c₁ =>
            (memCondN memFuel (.ident d.peel.2 M)).map fun c₂ => c₁ ++ c₂).map fun c => c₀ ++ c
    | .sv _, d =>
      match d.copyMemV? with
      | some ⟨_, M, t⟩ => (memCondN memFuel (.mem M)).bind fun c₁ =>
          (memCondN memFuel (.ident t M)).map fun c₂ => c₁ ++ c₂
      | none => some (svConds d)
    | _, _ => none

/-- `guardQ` at an identity with no guard of its own. -/
theorem guardQ_ident {R : RefTy} (d' : LTm C (.ident R)) {cs : List (LTm C (.val .bool))}
    (h : (d'.identMem?.bind fun M => (memCondN memFuel (.mem M)).bind fun c₁ =>
        (memCondN memFuel (.ident d' M)).map fun c₂ => c₁ ++ c₂) = some cs) :
    (d'.eval g ν : Option Nat).isSome = true ↔ AllT g ν cs := by
  obtain ⟨M, hM, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨c₁, h₁, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨c₂, h₂, rfl⟩ := Option.map_eq_some_iff.1 h
  have HM := memCondN_sound (g := g) (ν := ν) memFuel (.mem M) c₁ h₁
  have HI := memCondN_sound (g := g) (ν := ν) memFuel (.ident d' M) c₂ h₂
  rw [AllT.append]
  constructor
  · intro hd
    have hMs := LTm.identMem?_rets hM hd
    obtain ⟨μ, hμ⟩ := Option.isSome_iff_exists.1 hMs
    exact ⟨HM.1 hMs, (HI μ hμ).2 hd⟩
  · rintro ⟨a₁, a₂⟩
    obtain ⟨μ, hμ⟩ := Option.isSome_iff_exists.1 (HM.2 a₁)
    obtain ⟨id, hid, -⟩ := (HI μ hμ).1 a₂
    show (d'.eval g ν : Option Nat).isSome = true
    rw [hid]; rfl

theorem guardQ_sound {s : Srt} {d : LTm C s} {cs : List (LTm C (.val .bool))}
    (h : guardQ d = some cs) : (d.eval g ν).isSome = true ↔ AllT g ν cs := by
  unfold guardQ at h
  split at h
  · rename_i M hM
    cases LTm.castTo?_eq hM
    exact memCondN_sound memFuel (.mem M) cs h
  · split at h
    · rename_i R d' _
      split at h
      · exact guardQ_ident d' h
      · obtain ⟨c₀, h₀, h⟩ := Option.bind_eq_some_iff.1 h
        obtain ⟨c, hc, rfl⟩ := Option.map_eq_some_iff.1 h
        have HF := framesCond?_iff (g := g) (ν := ν) _ h₀
        have HI := guardQ_ident (g := g) (ν := ν) d'.peel.2 hc
        classical
        rw [AllT.append, ← HI, LTm.eval_peel d']
        constructor
        · intro hd
          split at hd
          · rename_i hf; exact ⟨HF.1 hf, hd⟩
          · cases hd
        · rintro ⟨a₀, a₁⟩
          rw [if_pos (HF.2 a₀)]; exact a₁
    · rename_i U d' _
      split at h
      · rename_i R M t hcm
        obtain ⟨c₁, h₁, h⟩ := Option.bind_eq_some_iff.1 h
        obtain ⟨c₂, h₂, rfl⟩ := Option.map_eq_some_iff.1 h
        have HM := memCondN_sound (g := g) (ν := ν) memFuel (.mem M) c₁ h₁
        have HI := memCondN_sound (g := g) (ν := ν) memFuel (.ident t M) c₂ h₂
        cases d' with
        | app2 o x y =>
          cases o <;> simp only [LTm.copyMemV?, Op2.copyMemV, reduceCtorEq, Option.some.injEq] at hcm
          obtain ⟨rfl, hcm⟩ := Sigma.mk.inj hcm
          simp only [heq_eq_eq, Prod.mk.injEq] at hcm
          obtain ⟨rfl, rfl⟩ := hcm
          rw [LTm.copyMem_isSome, AllT.append]
          constructor
          · rintro ⟨μ, hμ, id, hid, hR⟩
            exact ⟨HM.1 (by rw [hμ]; rfl), (HI μ hμ).2 (by rw [hid]; rfl)⟩
          · rintro ⟨a₁, a₂⟩
            obtain ⟨μ, hμ⟩ := Option.isSome_iff_exists.1 (HM.2 a₁)
            exact ⟨μ, hμ, (HI μ hμ).1 a₂⟩
        | _ => simp only [LTm.copyMemV?, reduceCtorEq] at hcm
      · cases h
        exact svConds_iff d'
    · cases h

/-- A word the closer folds to `true` (`Facts.nf` with no facts). -/
def LTm.isTrueC (c : LTm C (.val .bool)) : Bool :=
  match (({} : Facts C).nf c).litV? with
  | some v => v
  | none => false

theorem LTm.isTrueC_eval {c : LTm C (.val .bool)} (h : c.isTrueC = true) :
    (c.eval g ν : Option Bool) = some true := by
  unfold LTm.isTrueC at h
  split at h
  · rename_i v hv
    rw [← Facts.nf_eval (Facts.ok_empty ν), LTm.eval_litV? g ν hv, h]
  · cases h

/-- `a`, guarded by the words `cs`: `if (c) then … else err`, a word the
closer folds to `true` dropped, and a guard `a` already has at its top
(`LTm.peel`). -/
def guardL (cs : List (LTm C (.val .bool))) {s : Srt} (a : LTm C s) : LTm C s :=
  cs.foldr (fun c a => if c.isTrueC then a
    else if a.peel.1.any (GFrame.kite c .tt).beq then a else .kite c .tt a .err) a

open Classical in
theorem guardL_eval (cs : List (LTm C (.val .bool))) {s : Srt} (a : LTm C s) :
    (guardL cs a).eval g ν = if AllT g ν cs then a.eval g ν else none := by
  induction cs with
  | nil => rw [if_pos AllT.nil]; rfl
  | cons c cs ih =>
    have hc : AllT g ν (c :: cs) ↔ (c.eval g ν : Option Bool) = some true ∧ AllT g ν cs := by
      rw [show c :: cs = [c] ++ cs from rfl, AllT.append, AllT.single]
    show (if c.isTrueC then guardL cs a
      else if (guardL cs a).peel.1.any (GFrame.kite c .tt).beq then guardL cs a
      else .kite c .tt (guardL cs a) .err).eval g ν = _
    split
    · rename_i htc
      have h1 := LTm.isTrueC_eval (g := g) (ν := ν) htc
      rw [ih]
      by_cases h2 : AllT g ν cs
      · rw [if_pos h2, if_pos (hc.2 ⟨h1, h2⟩)]
      · rw [if_neg h2, if_neg (fun h => h2 (hc.1 h).2)]
    split
    · rename_i hany
      obtain ⟨f', hf', hb⟩ := List.any_eq_true.1 hany
      cases GFrame.eq_of_beq hb
      by_cases h1 : (c.eval g ν : Option Bool) = some true
      · rw [ih]
        by_cases h2 : AllT g ν cs
        · rw [if_pos h2, if_pos (hc.2 ⟨h1, h2⟩)]
        · rw [if_neg h2, if_neg (fun h => h2 (hc.1 h).2)]
      · have hn : ¬ (GFrame.kite c .tt).Holds g ν := by
          rintro ⟨x, hx, hy⟩
          have ht : ((LTm.tt : LTm C (.val .bool)).eval g ν : Option Bool) = some true := rfl
          rw [ht] at hy
          cases hy
          exact h1 hx
        rw [LTm.eval_none_of_peel hf' hn, if_neg (fun h => h1 (hc.1 h).1)]
    rw [LTm.eval_kite, ih]
    by_cases h1 : (c.eval g ν : Option Bool) = some true
    · rw [h1]
      by_cases h2 : AllT g ν cs
      · rw [if_pos (hc.2 ⟨h1, h2⟩), if_pos h2]; rfl
      · rw [if_neg (fun h => h2 (hc.1 h).2), if_neg h2]; rfl
    · rw [if_neg (fun h => h1 (hc.1 h).1)]
      cases hce : (c.eval g ν : Option Bool) with
      | none => rfl
      | some x =>
        cases x
        · rfl
        · exact absurd hce h1

/-- `d; a`, the guard read as the words it comes to (`guardQ`). -/
def seqMemL1 {s' s : Srt} (d : LTm C s') (a : LTm C s) : LTm C s :=
  match guardQ d with
  | some cs => guardL cs a
  | none => .seq d a

theorem seqMemL1_eval {s' s : Srt} (d : LTm C s') (a : LTm C s) :
    (seqMemL1 d a).eval g ν = (LTm.seq d a).eval g ν := by
  unfold seqMemL1
  split
  · rename_i cs h
    rw [guardL_eval, LTm.eval_seq]
    by_cases hc : AllT g ν cs
    · obtain ⟨w, hw⟩ := Option.isSome_iff_exists.1 ((guardQ_sound h).2 hc)
      rw [if_pos hc, hw]; rfl
    · have hd : d.eval g ν = none := by
        cases hd : d.eval g ν with
        | none => rfl
        | some _ => exact absurd ((guardQ_sound h).1 (by rw [hd]; rfl)) hc
      rw [if_neg hc, hd]; rfl
  · rfl

/-- `d; a`, a guard `d₁; d₂` taken as two (`(d₁; d₂); a` is `d₁; (d₂; a)`),
each read as the words it comes to. -/
def seqMemL {s' s : Srt} (d : LTm C s') (a : LTm C s) : LTm C s :=
  match d with
  | .seq d₁ d₂ => seqMemL1 d₁ (seqMemL1 d₂ a)
  | d => seqMemL1 d a

theorem seqMemL_eval {s' s : Srt} (d : LTm C s') (a : LTm C s) :
    (seqMemL d a).eval g ν = (LTm.seq d a).eval g ν := by
  cases d with
  | seq d₁ d₂ =>
    show (seqMemL1 d₁ (seqMemL1 d₂ a)).eval g ν = _
    rw [seqMemL1_eval, LTm.eval_seq, LTm.eval_seq, LTm.eval_seq]
    cases d₁.eval g ν with
    | none => rfl
    | some _ => simp only [Option.bind_some, seqMemL1_eval, LTm.eval_seq]
  | _ => simp only [seqMemL]; exact seqMemL1_eval _ a

end Ok

end Decide

end Solidity
