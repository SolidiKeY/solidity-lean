import Solidity.Evm.CoreStmt

/-!
# The scoped compiler is correct

`Evm/Correctness.lean`'s headline over the scoped syntax (`docs/intrinsic.md`,
M5): `stmt_sim`/`prog_sim` by structural recursion on `Core.Stmt`/`Core.Prog`,
each statement dispatched to its lemma in `Evm/CoreStmt.lean` or, for the
statements with a sub-program, to a lemma here that takes the sub-program's
outcome as a hypothesis (`ite_sim`, `block_sim`, `call_sim`), so that every
family elaborates on its own.  Then `compile_correct`, `compile_exact`,
`compile_box`, `compile_net` and `compile_storage`.

A scope's end pops its locals in the state (`State.drop`) and nothing on the
machine: the cells stay, above the enclosing scope's level, and `Sim.drop`
forgets them.  A branch's fragment is met with the other's (`Frag.meet`).

There is no `not_stuck` here: the scoped interpreter's statements in the
fragment never reach `.stuck` (a `Value` of the wrong shape), and
`compile_correct` says so by listing every outcome without it.
-/

namespace Solidity.Evm
namespace Core

open Semantics
open SemanticsProperties
open Solidity.Core (Ctx Idx Ext Env)

variable {C : Contract}

/-! ## Outcomes, rearranged -/

section Outcomes

variable {L b : Nat} {Γ' : Ctx} {sh pays asserts : Bool} {out : Out} {m : Machine}

theorem Frag.guard_some {Γ : Ctx} {F F' : Frag Γ} {ok : Bool} (h : F.guard ok = some F') :
    ok = true ∧ F' = F := by
  unfold Frag.guard at h
  cases ok
  · cases h
  · cases h; exact ⟨rfl, rfl⟩

theorem Keeps.weaken {sh' : Bool} {m m' : Machine} (h : Keeps C b sh m m')
    (hs : sh = true → sh' = true) : Keeps C b sh' m m' :=
  ⟨h.mem, fun h' => h.len (by cases sh <;> simp_all)⟩

/-- A scope's end in the state: its locals popped. -/
theorem Sim.dropState {Γ Δ : Ctx} {G : Frag Δ} {σ' : Solidity.Core.State C Δ} (h : Ext Γ Δ)
    (hm : Sim C L b G σ'.glob (Look.ofEnv σ'.env) m) :
    Sim C L b (G.restrict Γ) (σ'.drop h).glob (Look.ofEnv (σ'.drop h).env) m :=
  (hm.drop h).congrLook fun i => Look.ofEnv_drop h σ'.env i

/-- The outcome of a scope, its locals popped. -/
theorem StmtOut.drop {Γ Δ : Ctx} {G : Frag Δ} (h : Ext Γ Δ)
    {res : Res (Solidity.Core.State C Δ)} (H : StmtOut C L b G sh pays asserts res out m) :
    StmtOut C L b (G.restrict Γ) sh pays asserts (res.map (Solidity.Core.State.drop h)) out m := by
  rcases H with ⟨σ', m', h1, h2, h3, h4, h5⟩ | ⟨h1, h2⟩ | ⟨ha, h1, h2⟩ |
      ⟨hp, h1, σ', m', h2, h4, h5⟩
  · exact .inl ⟨σ'.drop h, m', by rw [h1]; rfl, h2, h3, h4, Sim.dropState h h5⟩
  · exact .inr ⟨by rw [h1]; rfl, h2⟩
  · exact .panic ha ⟨by rw [h1]; rfl, h2⟩
  · exact .refused hp ⟨h1, σ'.drop h, m', by rw [h2]; rfl, h4, Sim.dropState h h5⟩

/-- An outcome under weaker flags: fewer aliases known, a statement that
may shrink, pay or assert more. -/
theorem StmtOut.weaken {G G' : Frag Γ'} {sh' pays' asserts' : Bool}
    {res : Res (Solidity.Core.State C Γ')}
    (hG : ∀ {R : RefTy} (i : Idx Γ' (.alias R)) (g : Fl), G'.get i = g → g ≠ .dead → G.get i = g)
    (hs : sh = true → sh' = true) (hp : pays = true → pays' = true)
    (ha : asserts = true → asserts' = true) (H : StmtOut C L b G sh pays asserts res out m) :
    StmtOut C L b G' sh' pays' asserts' res out m := by
  rcases H with ⟨σ', m', h1, h2, h3, h4, h5⟩ | h | ⟨ha', h⟩ | ⟨hp', h1, σ', m', h2, h4, h5⟩
  · exact .inl ⟨σ', m', h1, h2, h3, h4.weaken hs, h5.flags hG⟩
  · exact .inr h
  · exact .panic (ha ha') h
  · exact .refused (hp hp') ⟨h1, σ', m', h2, h4.weaken hs, h5.flags hG⟩

end Outcomes

/-! ## Branches and blocks -/

section Scopes

variable {L b : Nat} {Γ : Ctx} {F : Frag Γ} {σ : Solidity.Core.State C Γ} {m : Machine}

/-- **`if (c) { t } else { e }`**: the condition, then the branch it picks,
whose locals are popped; the branches' fragments met.

Example: `if (total > 3) { uint x = 1; total = x; } else { revert(); }` runs
`MSTORE %0` in the `then` branch, and `x` is gone after it. -/
theorem ite_sim {Γ₁ Γ₂ : Ctx} (c : Solidity.Core.Val C Γ .bool)
    (t : Solidity.Core.Prog C Γ Γ₁) (e : Solidity.Core.Prog C Γ Γ₂) {F₁ : Frag Γ₁}
    {F₂ : Frag Γ₂} {L' : Nat} (hm : Sim C L b F σ.glob (Look.ofEnv σ.env) m)
    (hwc : valIn F c = true)
    (iht : StmtOut C L' b F₁ (Prog.shrinks t) (Prog.pays t) (Prog.asserts t)
      (Solidity.Core.Prog.run σ t) (run (compileProg b t) m) m)
    (ihe : StmtOut C L' b F₂ (Prog.shrinks e) (Prog.pays e) (Prog.asserts e)
      (Solidity.Core.Prog.run σ e) (run (compileProg b e) m) m) :
    StmtOut C L' b ((F₁.restrict Γ).meet (F₂.restrict Γ)) (Prog.shrinks t || Prog.shrinks e)
      (Prog.pays t || Prog.pays e) (Prog.asserts t || Prog.asserts e)
      (Solidity.Core.Stmt.run σ (.ite c t e)) (run (compileStmt b (.ite c t e)) m) m := by
  rw [Solidity.Core.Stmt.run_ite]
  simp only [compileStmt, List.append_assoc]
  rcases val_sim c hm hwc with ⟨vc, wc, hvc, hrc, hrunc⟩ | ⟨hvc, hrunc⟩
  · obtain ⟨x, rfl, rfl⟩ := hrc.bool_inv
    rw [run_append_ok hrunc]
    simp only [Solidity.Core.Run.ite, hvc, Res.ok_bind]
    cases x
    · rw [run_append_skip (m' := m) (k := (compileProg b t).length + 1) rfl, exec_skip_append,
        show exec ([Instr.jump (compileProg b e).length] ++ compileProg b e) 1 m =
          run (compileProg b e) m from rfl]
      exact (ihe.drop e.ext).weaken (fun i _ hg hd => Frag.get_meet_right _ _ i hg hd)
        (by simp_all) (by simp_all) (by simp_all)
    · rw [run_append_skip (m' := m) (k := 0) rfl]
      refine (StmtOut.drop (sh := Prog.shrinks t) (pays := Prog.pays t)
        (asserts := Prog.asserts t) t.ext ?_).weaken (fun i _ hg hd => Frag.get_meet _ _ i hg hd)
        (by simp_all) (by simp_all) (by simp_all)
      rcases iht with ⟨τ', m', hτ', hrun', hst', hk', hm'⟩ | ⟨hτ', hrun'⟩ | ⟨ha, hτ', hrun'⟩ |
          ⟨hp, hrun', τ', m', hτ', hk', hm'⟩
      · refine .inl ⟨τ', m', hτ', ?_, hst', hk', hm'⟩
        change run _ m = _
        rw [run_append_skip (k := 0) hrun']
        exact exec_length (.jump (compileProg b e).length :: compileProg b e) m' |>.trans rfl
      · exact .inr ⟨hτ', run_append_revert hrun'⟩
      · exact .panic ha ⟨hτ', run_append_revert hrun'⟩
      · exact .refused hp ⟨run_append_revert hrun', τ', m', hτ', hk', hm'⟩
  · exact .inr ⟨by rw [Solidity.Core.Run.ite, hvc]; rfl, run_append_revert hrunc⟩

/-- **`{ … }`**: the body, its locals popped. -/
theorem block_sim {Γ₁ : Ctx} (body : Solidity.Core.Prog C Γ Γ₁) {G : Frag Γ₁} {L' : Nat}
    {sh pays asserts : Bool}
    (ih : StmtOut C L' b G sh pays asserts (Solidity.Core.Prog.run σ body)
      (run (compileProg b body) m) m) :
    StmtOut C L' b (G.restrict Γ) sh pays asserts (Solidity.Core.Stmt.run σ (.block body))
      (run (compileStmt b (.block body)) m) m :=
  ih.drop body.ext

end Scopes

/-! ## Calls -/

section Calls

variable {L b : Nat} {Γ : Ctx} {F : Frag Γ} {σ : Solidity.Core.State C Γ} {m : Machine}

theorem Args.eval_nil : Solidity.Core.Args.eval σ (.nil : Solidity.Core.Args C Γ []) = pure () :=
  rfl

theorem Args.eval_snoc {ps : Ctx} (as : Solidity.Core.Args C Γ ps) (p : PrimTy) (x : Var)
    (e : Solidity.Core.Val C Γ p) :
    Solidity.Core.Args.eval σ (.snoc as p x e) =
      (do let r ← Solidity.Core.Args.eval σ as; let v ← e.eval σ; pure (v, r)) := rfl

/-- A call's parameters are values. -/
theorem Args.noAlias : ∀ {ps : Ctx}, Solidity.Core.Args C Γ ps → ∀ {R : RefTy},
    Idx ps (.alias R) → False
  | _, .snoc as _ _ _, _, i => by
    cases i with
    | there j => exact Args.noAlias as j

/-- **A call's arguments**: each read in the caller's state, in order, and
stored at its level in the callee's frame, which starts at `b + Γ.length`;
the caller's cells left.

Example: `addTwo(3)` from no locals is `PUSH 3; MSTORE %0`. -/
theorem args_sim (hm : Sim C L b F σ.glob (Look.ofEnv σ.env) m) :
    ∀ {ps : Ctx} (args : Solidity.Core.Args C Γ ps), argsIn F args = true →
      (∃ a mem', Solidity.Core.Args.eval σ args = .ok a ∧
        run (argsCode b args) m = .ok { m with mem := mem' } 0 ∧
        (∀ l, l < b + Γ.length → mem' (cell l) = m.mem (cell l)) ∧
        ∀ {p : PrimTy} (i : Idx ps (.val p)), ∃ v, Look.ofEnv a i = .val v ∧
          ReprV p v (({ m with mem := mem' } : Machine).memAt (lvl (b + Γ.length) i))) ∨
      (Solidity.Core.Args.eval σ args = .error .revert ∧ run (argsCode b args) m = .revert)
  | _, .nil, _ => .inl ⟨(), m.mem, rfl, rfl, fun _ _ => rfl, fun i => nomatch i⟩
  | _, @Solidity.Core.Args.snoc _ _ ps as p x e, hw => by
    simp only [argsIn, Bool.and_eq_true] at hw
    rw [Args.eval_snoc]
    simp only [argsCode, List.append_assoc]
    rcases args_sim hm as hw.1 with ⟨a, mem₁, ha, hrun₁, hmem₁, hv₁⟩ | ⟨ha, hrun₁⟩
    · rw [ha, run_append_ok hrun₁]
      have hm₁ := hm.congrMem (mem := mem₁) fun l _ hl => hmem₁ l hl
      rcases val_sim e hm₁ hw.2 with ⟨v, w, hv, hrv, hrun⟩ | ⟨hv, hrun⟩
      · rw [run_append_ok hrun]
        refine .inl ⟨(v, a), upd mem₁ (cell (b + Γ.length + ps.length)) w,
          by simp only [Res.ok_bind, hv]; rfl, rfl, fun l hl => ?_, fun i => ?_⟩
        · rw [upd_other _ _ (fun h => by have := cell_inj h; omega)]; exact hmem₁ l hl
        · cases i with
          | here =>
            refine ⟨v, rfl, ?_⟩
            show ReprV _ v (upd mem₁ _ w (cell (lvl _ (Idx.here (Γ := ps)))))
            rw [lvl_here, upd_same]; exact hrv
          | there j =>
            obtain ⟨v', hj, hv'⟩ := hv₁ j
            refine ⟨v', hj, ?_⟩
            show ReprV _ v' (upd mem₁ _ w (cell (lvl _ (Idx.there (u := .val p) j))))
            have := lvl_lt (b + Γ.length) j
            rw [lvl_there, upd_other _ _ (fun h => by have := cell_inj h; omega)]; exact hv'
      · exact .inr ⟨by simp only [Res.ok_bind, hv]; rfl, run_append_revert hrun⟩
    · exact .inr ⟨by rw [ha]; rfl, run_append_revert hrun₁⟩

/-- **Back from a call**: the caller's locals where they were (the callee
kept every cell below its frame), its storage, ledger and transaction the
callee's, its fragile aliases forgotten if the callee may have shrunk an
array; and what the call keeps, from what its body keeps. -/
theorem Sim.back {Δ : Ctx} {G : Frag Δ} {τ : Semantics.State} {ρ' : Look Δ} {m₁ m₃ : Machine}
    {sh : Bool} {L' : Nat} (hL : L ≤ L') (hm : Sim C L b F σ.glob (Look.ofEnv σ.env) m)
    (h₁ : ∀ l, l < b + Γ.length → m₁.memAt l = m.memAt l) (hs₁ : m₁.store = m.store)
    (hk : Keeps C (b + Γ.length) sh m₁ m₃) (h₃ : Sim C L' (b + Γ.length) G τ ρ' m₃) :
    Sim C L' b (F.after sh) τ (Look.ofEnv σ.env) m₃ ∧ Keeps C b sh m m₃ := by
  have hm' := hm.mono hL h₃.bound
  have hmem : ∀ l, l < b + Γ.length → m₃.memAt l = m.memAt l :=
    fun l hl => (hk.mem l hl).trans (h₁ l hl)
  have hlen : sh = false → ∀ x, LenSlot C x → m.store x ≤ m₃.store x :=
    fun hsh x hx => by rw [← hs₁]; exact hk.len hsh x hx
  refine ⟨?_, ⟨fun l hl => hmem l (by omega), hlen⟩⟩
  cases sh
  · exact hm'.return h₃ hmem (hlen rfl)
  · exact hm'.returnDrop h₃ hmem

/-- A call whose arguments and return variables are in: the body run in
its frame, and the caller's locals given back what the call leaves them. -/
theorem call_run_eq {Γ' ps rs Γf : Ctx} (f : Name) (args : Solidity.Core.Args C Γ ps)
    (ret : Solidity.Core.CallRet Γ rs Γ') (body : Solidity.Core.Prog C (rs ++ ps) Γf)
    {a : Env C ps} {τ : Semantics.State} {r : Env C rs}
    (ha : Solidity.Core.Args.eval σ args = .ok a) (he : ret.enter σ.glob = .ok (τ, r)) :
    Solidity.Core.Stmt.run σ (.call f args ret body) =
      (Solidity.Core.Prog.run (Solidity.Core.State.ofGlob τ (Env.append rs r a)) body).map
        fun υ => υ.withEnv (ret.leave σ.env (Env.take rs (Env.drop body.ext υ.env))) := by
  rw [Solidity.Core.Stmt.run_call]
  simp only [Solidity.Core.Run.call, ha, he, Res.ok_bind]
  dsimp only [Solidity.Core.Prog.run]
  cases Solidity.Core.Prog.runR body _ <;> rfl

/-- **A call with no return value**, `f(e);`: the arguments in the frame,
the body, back. -/
theorem callNone_sim {ps Γf : Ctx} (f : Name) (args : Solidity.Core.Args C Γ ps)
    (body : Solidity.Core.Prog C ([] ++ ps) Γf) {L' : Nat} {sh pays asserts : Bool}
    (hL : L ≤ L') (hm : Sim C L b F σ.glob (Look.ofEnv σ.env) m) (hwa : argsIn F args = true)
    (ih : ∀ {τ : Solidity.Core.State C ([] ++ ps)} {m₂ : Machine},
      Sim C L (b + Γ.length) (Frag.init ([] ++ ps)) τ.glob (Look.ofEnv τ.env) m₂ →
      ∃ G : Frag Γf, StmtOut C L' (b + Γ.length) G sh pays asserts
        (Solidity.Core.Prog.run τ body) (run (compileProg (b + Γ.length) body) m₂) m₂) :
    StmtOut C L' b (F.after sh) sh pays asserts
      (Solidity.Core.Stmt.run σ (.call f args .none body))
      (run (compileStmt b (.call f args .none body)) m) m := by
  simp only [compileStmt, retEnterCode, retLeaveCode, List.append_nil]
  rcases args_sim hm args hwa with ⟨a, mem₁, ha, hrun₁, hmem₁, hv₁⟩ | ⟨ha, hrun₁⟩
  · rw [run_append_ok hrun₁, call_run_eq f args .none body ha rfl]
    have hb := (hm.congrMem (mem := mem₁) fun l _ hl => hmem₁ l hl).enter (b + Γ.length)
      (Look.ofEnv a) hv₁ (Args.noAlias args)
    obtain ⟨G, hout⟩ :=
      ih (τ := Solidity.Core.State.ofGlob σ.glob (Env.append [] () a)) (hb.congrGlob rfl rfl rfl)
    have h₁ : ∀ l, l < b + Γ.length →
        ({ m with mem := mem₁ } : Machine).memAt l = m.memAt l := fun l hl => hmem₁ l hl
    rcases hout with ⟨υ, m₃, hυ, hrun₃, hst₃, hk₃, hm₃⟩ | ⟨hυ, hrun₃⟩ | ⟨hasr, hυ, hrun₃⟩ |
        ⟨hp, hrun₃, υ, m₃, hυ, hk₃, hm₃⟩
    · obtain ⟨hs, hk⟩ := Sim.back hL hm h₁ rfl hk₃ hm₃
      exact .inl ⟨υ.withEnv σ.env, m₃, by rw [hυ]; rfl, hrun₃, hst₃, hk, hs⟩
    · exact .inr ⟨by rw [hυ]; rfl, hrun₃⟩
    · exact .panic hasr ⟨by rw [hυ]; rfl, hrun₃⟩
    · obtain ⟨hs, hk⟩ := Sim.back hL hm h₁ rfl hk₃ hm₃
      exact .refused hp ⟨hrun₃, υ.withEnv σ.env, m₃, by rw [hυ]; rfl, hk, hs⟩
  · refine .inr ⟨?_, run_append_revert hrun₁⟩
    rw [Solidity.Core.Stmt.run_call]
    simp only [Solidity.Core.Run.call, ha]; rfl

/-- **A call with a return value**, `y = f(e);` (or `f(e);` dropping it): the
arguments and the return variable (`0`) in the frame, the body, back, and
the return variable's word copied into `y`'s cell.

Example: `uint y = addTwo(3);` stores `3` at `%1`, `0` at `%2`, runs
`addTwo`'s body above level `1`, then `MLOAD %2; MSTORE %0`. -/
theorem callVal_sim {ps Γf : Ctx} (f : Name) (args : Solidity.Core.Args C Γ ps) (p : PrimTy)
    (r : Var) (res : Option (Idx Γ (.val p))) (body : Solidity.Core.Prog C ([.val p] ++ ps) Γf)
    {L' : Nat} {sh pays asserts : Bool}
    (hL : L ≤ L') (hm : Sim C L b F σ.glob (Look.ofEnv σ.env) m) (hwa : argsIn F args = true)
    (ih : ∀ {τ : Solidity.Core.State C ([.val p] ++ ps)} {m₂ : Machine},
      Sim C L (b + Γ.length) (Frag.init ([.val p] ++ ps)) τ.glob (Look.ofEnv τ.env) m₂ →
      ∃ G : Frag Γf, StmtOut C L' (b + Γ.length) G sh pays asserts
        (Solidity.Core.Prog.run τ body) (run (compileProg (b + Γ.length) body) m₂) m₂) :
    StmtOut C L' b (F.after sh) sh pays asserts
      (Solidity.Core.Stmt.run σ (.call f args (.val p r res) body))
      (run (compileStmt b (.call f args (.val p r res) body)) m) m := by
  simp only [compileStmt, List.append_assoc]
  rcases args_sim hm args hwa with ⟨a, mem₁, ha, hrun₁, hmem₁, hv₁⟩ | ⟨ha, hrun₁⟩
  · rw [run_append_ok hrun₁, call_run_eq f args (.val p r res) body ha rfl]
    simp only [retEnterCode]
    rw [run_append_ok (m' := { m with mem := upd mem₁ (cell (b + Γ.length + ps.length)) (.val 0) })
      rfl]
    have hb := ((hm.congrMem (mem := mem₁) fun l _ hl => hmem₁ l hl).enter (b + Γ.length)
      (Look.ofEnv a) hv₁ (Args.noAlias args)).consVal (ReprV.default p)
    obtain ⟨G, hout⟩ :=
      ih (τ := Solidity.Core.State.ofGlob σ.glob (Env.append [.val p] (PrimTy.default p, ()) a))
        ((hb.congrLook fun j => Look.ofEnv_cons (u := .val p) (PrimTy.default p) a j).congrGlob
          rfl rfl rfl)
    have h₁ : ∀ l, l < b + Γ.length →
        ({ m with mem := upd mem₁ (cell (b + Γ.length + ps.length)) (.val 0) } : Machine).memAt l =
          m.memAt l := fun l hl => by
      show upd mem₁ _ _ (cell l) = _
      rw [upd_other _ _ (fun h => by have := cell_inj h; omega)]; exact hmem₁ l hl
    -- what the call leaves the caller, from the machine `m₃` and state `υ` the body left
    have leave : ∀ {υ : Solidity.Core.State C Γf} {m₃ : Machine},
        Keeps C (b + Γ.length) sh
          { m with mem := upd mem₁ (cell (b + Γ.length + ps.length)) (.val 0) } m₃ →
        Sim C L' (b + Γ.length) G υ.glob (Look.ofEnv υ.env) m₃ →
        ∃ m₄, run (retLeaveCode b ps (.val p r res)) m₃ = .ok m₄ 0 ∧ m₄.stack = m₃.stack ∧
          Keeps C b sh m m₄ ∧
          Sim C L' b (F.after sh)
            (υ.withEnv ((Solidity.Core.CallRet.val p r res).leave σ.env
              (Env.take [.val p] (Env.drop body.ext υ.env)))).glob
            (Look.ofEnv (υ.withEnv ((Solidity.Core.CallRet.val p r res).leave σ.env
              (Env.take [.val p] (Env.drop body.ext υ.env)))).env) m₄ := by
      intro υ m₃ hk₃ hm₃
      obtain ⟨hs, hk⟩ := Sim.back hL hm h₁ rfl hk₃ hm₃
      cases res with
      | none => exact ⟨m₃, rfl, rfl, hk, hs⟩
      | some y =>
        obtain ⟨v, hv, hrv⟩ := hm₃.vals (Idx.ext (Idx.here (Γ := ps) (t := .val p)) body.ext)
        have hl : lvl (b + Γ.length) (Idx.ext (Idx.here (Γ := ps) (t := .val p)) body.ext) =
            b + Γ.length + ps.length := by
          rw [lvl_ext]
          simp only [lvl, Idx.toNat, List.length_cons]
          omega
        rw [hl] at hrv
        have hV : v = (Env.drop body.ext υ.env).1 := by
          have := (Look.ofEnv_drop body.ext υ.env (Idx.here (Γ := ps) (t := .val p))).symm
          rw [show Look.drop body.ext (Look.ofEnv υ.env) Idx.here =
            Look.ofEnv υ.env (Idx.ext Idx.here body.ext) from rfl, hv] at this
          exact Binding.val.inj this
        subst hV
        have hs' := Sim.setLocalVal (σ := υ.withEnv σ.env) hs y hrv
        refine ⟨_, rfl, rfl, (hk.trans (Keeps.upd (sh := false) (le_lvl b y) _)).weaken
          (by simp only [Bool.or_false, imp_self]), hs'⟩
    rcases hout with ⟨υ, m₃, hυ, hrun₃, hst₃, hk₃, hm₃⟩ | ⟨hυ, hrun₃⟩ | ⟨hasr, hυ, hrun₃⟩ |
        ⟨hp, hrun₃, υ, m₃, hυ, hk₃, hm₃⟩
    · obtain ⟨m₄, hrun₄, hst₄, hk, hs⟩ := leave hk₃ hm₃
      exact .inl ⟨_, m₄, by rw [hυ]; rfl, by rw [run_append_ok hrun₃, hrun₄],
        hst₄.trans hst₃, hk, hs⟩
    · exact .inr ⟨by rw [hυ]; rfl, run_append_revert hrun₃⟩
    · exact .panic hasr ⟨by rw [hυ]; rfl, run_append_revert hrun₃⟩
    · obtain ⟨m₄, -, -, hk, hs⟩ := leave hk₃ hm₃
      exact .refused hp ⟨run_append_revert hrun₃, _, m₄, by rw [hυ]; rfl, hk, hs⟩
  · refine .inr ⟨?_, run_append_revert hrun₁⟩
    rw [Solidity.Core.Stmt.run_call]
    simp only [Solidity.Core.Run.call, ha]; rfl

end Calls


/-! ## One lemma per family

What `inFrag` admits of each statement with no sub-program, and that
statement's lemma of `Evm/CoreStmt.lean`. -/

section Families

variable {L b : Nat} {Γ : Ctx} {F : Frag Γ} {σ : Solidity.Core.State C Γ} {m : Machine}

theorem assign_family {T : Ty} (l : Solidity.Core.Loc C Γ T) (r : Solidity.Core.Src C Γ T)
    {F' : Frag Γ} (hm : Sim C L b F σ.glob (Look.ofEnv σ.env) m)
    (hw : inFrag F (.assign l r) = some F') :
    StmtOut C L b F' false false false (Solidity.Core.Stmt.run σ (.assign l r))
      (run (compileStmt b (.assign l r)) m) m := by
  simp only [inFrag] at hw
  obtain ⟨hok, rfl⟩ := Frag.guard_some hw
  cases r with
  | val v =>
    simp only [assignIn, Bool.and_eq_true] at hok
    exact assign_sim l v hm hok.1 hok.2
  | copy q hq =>
    simp only [assignIn, Bool.and_eq_true] at hok
    exact copy_sim l q hq hok.1.1 hm hok.1.2 hok.2

theorem rebind_family {R : RefTy} (i : Idx Γ (.alias R)) (r : Solidity.Core.ARhs C Γ R)
    {F' : Frag Γ} (hm : Sim C L b F σ.glob (Look.ofEnv σ.env) m)
    (hw : inFrag F (.rebind i r) = some F') :
    StmtOut C L b F' false false false (Solidity.Core.Stmt.run σ (.rebind i r))
      (run (compileStmt b (.rebind i r)) m) m := by
  cases r with
  | path q => simp only [inFrag] at hw; exact rebind_sim i q hm hw
  | push _ _ => simp only [inFrag, reduceCtorEq] at hw

theorem assignLocal_family {p : PrimTy} (i : Idx Γ (.val p)) (r : Solidity.Core.Val C Γ p)
    {F' : Frag Γ} (hm : Sim C L b F σ.glob (Look.ofEnv σ.env) m)
    (hw : inFrag F (.assignLocal i r) = some F') :
    StmtOut C L b F' false false false (Solidity.Core.Stmt.run σ (.assignLocal i r))
      (run (compileStmt b (.assignLocal i r)) m) m := by
  simp only [inFrag] at hw
  obtain ⟨hok, rfl⟩ := Frag.guard_some hw
  exact assignLocal_sim i r hm hok

theorem declLocal_family (p : PrimTy) (x : Var) (init : Option (Solidity.Core.Val C Γ p))
    {F' : Frag (.val p :: Γ)} (hm : Sim C L b F σ.glob (Look.ofEnv σ.env) m)
    (hw : inFrag F (.declLocal p x init) = some F') :
    StmtOut C L b F' false false false (Solidity.Core.Stmt.run σ (.declLocal p x init))
      (run (compileStmt b (.declLocal p x init)) m) m := by
  simp only [inFrag] at hw
  obtain ⟨hok, rfl⟩ := Frag.guard_some hw
  cases init with
  | none => exact declLocal_sim p none hm hok
  | some e => exact declLocal_sim p (some e) hm hok

theorem declStorage_family (R : RefTy) (x : Var) (init : Option (Solidity.Core.ARhs C Γ R))
    {F' : Frag (.alias R :: Γ)} (hm : Sim C L b F σ.glob (Look.ofEnv σ.env) m)
    (hw : inFrag F (.declStorage R x init) = some F') :
    StmtOut C L b F' false false false (Solidity.Core.Stmt.run σ (.declStorage R x init))
      (run (compileStmt b (.declStorage R x init)) m) m := by
  simp only [inFrag] at hw
  rcases init with _ | (q | _)
  · simp only [declStorageIn, Option.some.injEq] at hw
    subst hw
    exact .inl ⟨σ.push (t := .alias R) none, m, rfl, rfl, rfl, Keeps.refl m, hm.pushDead R none⟩
  · exact declAlias_sim q hm hw
  · simp only [declStorageIn, reduceCtorEq] at hw

theorem opAssign_family {p : PrimTy} (op : BinOp) (hop : op.hasCompoundAssign = true)
    (hpn : p.isNumeric = true) (l : Solidity.Core.OpLoc C Γ p) (r : Solidity.Core.Val C Γ p)
    {F' : Frag Γ} (hm : Sim C L b F σ.glob (Look.ofEnv σ.env) m)
    (hw : inFrag F (.opAssign op hop hpn l r) = some F') :
    StmtOut C L b F' false false false (Solidity.Core.Stmt.run σ (.opAssign op hop hpn l r))
      (run (compileStmt b (.opAssign op hop hpn l r)) m) m := by
  simp only [inFrag] at hw
  obtain ⟨hok, rfl⟩ := Frag.guard_some hw
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hok
  obtain ⟨⟨hp, hl⟩, hr⟩ := hok
  cases l with
  | «local» i => exact opLocal_sim hp hop i r hm hr
  | root rt h => exact opStore_sim hp hop rfl r hm hl hr
  | field q f h => exact opStore_sim hp hop rfl r hm hl hr
  | index it q i => exact opStore_sim hp hop rfl r hm hl hr
  | mfield _ _ _ => simp [opLocIn, opLocToLoc] at hl
  | mindex _ _ _ => simp [opLocIn, opLocToLoc] at hl

theorem incDec_family {p : PrimTy} (op : IncDec) (hpn : p.isNumeric = true)
    (l : Solidity.Core.OpLoc C Γ p) {F' : Frag Γ} (hm : Sim C L b F σ.glob (Look.ofEnv σ.env) m)
    (hw : inFrag F (.incDec op hpn l) = some F') :
    StmtOut C L b F' false false false (Solidity.Core.Stmt.run σ (.incDec op hpn l))
      (run (compileStmt b (.incDec op hpn l)) m) m := by
  simp only [inFrag] at hw
  obtain ⟨hok, rfl⟩ := Frag.guard_some hw
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hok
  obtain ⟨hp, hl⟩ := hok
  cases l with
  | «local» i => exact bumpLocal_sim hp op i hm
  | root rt h => exact bumpStore_sim hp op rfl hm hl
  | field q f h => exact bumpStore_sim hp op rfl hm hl
  | index it q i => exact bumpStore_sim hp op rfl hm hl
  | mfield _ _ _ => simp [opLocIn, opLocToLoc] at hl
  | mindex _ _ _ => simp [opLocIn, opLocToLoc] at hl

theorem assignIncDec_family {p : PrimTy} (i : Idx Γ (.val p)) (op : IncDec)
    (hpn : p.isNumeric = true) (l : Solidity.Core.OpLoc C Γ p) (hs : l.recvSimple = true)
    {F' : Frag Γ} (hm : Sim C L b F σ.glob (Look.ofEnv σ.env) m)
    (hw : inFrag F (.assignIncDec i op hpn l hs) = some F') :
    StmtOut C L b F' false false false (Solidity.Core.Stmt.run σ (.assignIncDec i op hpn l hs))
      (run (compileStmt b (.assignIncDec i op hpn l hs)) m) m := by
  simp only [inFrag] at hw
  obtain ⟨hok, rfl⟩ := Frag.guard_some hw
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hok
  obtain ⟨hp, hl⟩ := hok
  cases l with
  | «local» j => exact assignBumpLocal_sim hp op i j hm
  | root rt h => exact assignBumpStore_sim hp op i rfl hm hl
  | field q f h => exact assignBumpStore_sim hp op i rfl hm hl
  | index it q j => exact assignBumpStore_sim hp op i rfl hm hl
  | mfield _ _ _ => simp [opLocIn, opLocToLoc] at hl
  | mindex _ _ _ => simp [opLocIn, opLocToLoc] at hl

theorem push_family {E : Ty} (q : Solidity.Core.SPath C Γ (.array E))
    (v : Option (Solidity.Core.Src C Γ E)) (hd : (v.isSome || E.defaultOkS) = true) {F' : Frag Γ}
    (hm : Sim C L b F σ.glob (Look.ofEnv σ.env) m) (hw : inFrag F (.push q v hd) = some F')
    (hL : L + 1 ≤ Lmax) :
    StmtOut C (L + 1) b F' false false false (Solidity.Core.Stmt.run σ (.push q v hd))
      (run (compileStmt b (.push q v hd)) m) m := by
  simp only [inFrag] at hw
  obtain ⟨hok, rfl⟩ := Frag.guard_some hw
  exact push_sim q v hm hok hL

theorem pop_family {E : Ty} (q : Solidity.Core.SPath C Γ (.array E)) {F' : Frag Γ}
    (hm : Sim C L b F σ.glob (Look.ofEnv σ.env) m) (hw : inFrag F (.pop q) = some F') :
    StmtOut C L b F' true false false (Solidity.Core.Stmt.run σ (.pop q))
      (run (compileStmt b (.pop q)) m) m := by
  simp only [inFrag] at hw
  obtain ⟨hok, rfl⟩ := Frag.guard_some hw
  exact pop_sim q hm hok

theorem delete_family {T : Ty} (l : Solidity.Core.Loc C Γ T) {F' : Frag Γ}
    (hm : Sim C L b F σ.glob (Look.ofEnv σ.env) m) (hw : inFrag F (.delete l) = some F') :
    StmtOut C L b F' true false false (Solidity.Core.Stmt.run σ (.delete l))
      (run (compileStmt b (.delete l)) m) m := by
  simp only [inFrag] at hw
  obtain ⟨hok, rfl⟩ := Frag.guard_some hw
  exact delete_sim l hm hok

theorem transfer_family (r a : Solidity.Core.Val C Γ .uint) {F' : Frag Γ}
    (hm : Sim C L b F σ.glob (Look.ofEnv σ.env) m) (hw : inFrag F (.transfer r a) = some F') :
    StmtOut C L b F' false true false (Solidity.Core.Stmt.run σ (.transfer r a))
      (run (compileStmt b (.transfer r a)) m) m := by
  simp only [inFrag] at hw
  obtain ⟨hok, rfl⟩ := Frag.guard_some hw
  simp only [Bool.and_eq_true] at hok
  exact transfer_sim r a hm hok.1 hok.2

theorem require_family (c : Solidity.Core.Val C Γ .bool) {F' : Frag Γ}
    (hm : Sim C L b F σ.glob (Look.ofEnv σ.env) m) (hw : inFrag F (.require c) = some F') :
    StmtOut C L b F' false false false (Solidity.Core.Stmt.run σ (.require c))
      (run (compileStmt b (.require c)) m) m := by
  simp only [inFrag] at hw
  obtain ⟨hok, rfl⟩ := Frag.guard_some hw
  exact require_sim c hm hok

theorem assert_family (c : Solidity.Core.Val C Γ .bool) {F' : Frag Γ}
    (hm : Sim C L b F σ.glob (Look.ofEnv σ.env) m) (hw : inFrag F (.assert c) = some F') :
    StmtOut C L b F' false false true (Solidity.Core.Stmt.run σ (.assert c))
      (run (compileStmt b (.assert c)) m) m := by
  simp only [inFrag] at hw
  obtain ⟨hok, rfl⟩ := Frag.guard_some hw
  exact assert_sim c hm hok

/-- What `inFrag` admits of a branch. -/
theorem ite_frag {Γ₁ Γ₂ : Ctx} {c : Solidity.Core.Val C Γ .bool} {t : Solidity.Core.Prog C Γ Γ₁}
    {e : Solidity.Core.Prog C Γ Γ₂} {F' : Frag Γ} (hw : inFrag F (.ite c t e) = some F') :
    valIn F c = true ∧ ∃ F₁ F₂, inFragP F t = some F₁ ∧ inFragP F e = some F₂ ∧
      F' = (F₁.restrict Γ).meet (F₂.restrict Γ) := by
  simp only [inFrag] at hw
  split at hw
  · rename_i hc
    split at hw
    · rename_i F₁ F₂ ht he
      cases hw
      exact ⟨hc, F₁, F₂, ht, he, rfl⟩
    · cases hw
  · cases hw

/-- What `inFrag` admits of a block. -/
theorem block_frag {Γ₁ : Ctx} {body : Solidity.Core.Prog C Γ Γ₁} {F' : Frag Γ}
    (hw : inFrag F (.block body) = some F') :
    ∃ G, inFragP F body = some G ∧ F' = G.restrict Γ := by
  simp only [inFrag, Option.map_eq_some_iff] at hw
  obtain ⟨G, hG, rfl⟩ := hw
  exact ⟨G, hG, rfl⟩

/-- What `inFrag` admits of a call. -/
theorem call_frag {Γ' ps rs Γf : Ctx} {f : Name} {args : Solidity.Core.Args C Γ ps}
    {ret : Solidity.Core.CallRet Γ rs Γ'} {body : Solidity.Core.Prog C (rs ++ ps) Γf}
    {F' : Frag Γ'} (hw : inFrag F (.call f args ret body) = some F') :
    argsIn F args = true ∧ (∃ G, inFragP (Frag.init (rs ++ ps)) body = some G) ∧
      CallRetIn (F.after (Prog.shrinks body)) ret = some F' := by
  simp only [inFrag] at hw
  split at hw
  · rename_i ha
    split at hw
    · rename_i G hG
      exact ⟨ha, ⟨G, hG⟩, hw⟩
    · cases hw
  · cases hw

/-- **A call** in the fragment: no return value or one value, the body's
outcome given (`ih`, `prog_sim` on the body in its frame). -/
theorem call_family {Γ' ps rs Γf : Ctx} (f : Name) (args : Solidity.Core.Args C Γ ps)
    (ret : Solidity.Core.CallRet Γ rs Γ') (body : Solidity.Core.Prog C (rs ++ ps) Γf)
    {F' : Frag Γ'} (hm : Sim C L b F σ.glob (Look.ofEnv σ.env) m)
    (hw : inFrag F (.call f args ret body) = some F')
    (ih : ∀ {G : Frag Γf} {τ : Solidity.Core.State C (rs ++ ps)} {m₂ : Machine},
      inFragP (Frag.init (rs ++ ps)) body = some G →
      Sim C L (b + Γ.length) (Frag.init (rs ++ ps)) τ.glob (Look.ofEnv τ.env) m₂ →
      StmtOut C (L + Prog.pushes body) (b + Γ.length) G (Prog.shrinks body) (Prog.pays body)
        (Prog.asserts body) (Solidity.Core.Prog.run τ body)
        (run (compileProg (b + Γ.length) body) m₂) m₂) :
    StmtOut C (L + Stmt.pushes (.call f args ret body)) b F'
      (Stmt.shrinks (.call f args ret body)) (Stmt.pays (.call f args ret body))
      (Stmt.asserts (.call f args ret body)) (Solidity.Core.Stmt.run σ (.call f args ret body))
      (run (compileStmt b (.call f args ret body)) m) m := by
  obtain ⟨hwa, ⟨G, hb⟩, hret⟩ := call_frag hw
  cases ret with
  | none =>
    cases hret
    exact callNone_sim f args body (Nat.le_add_right _ _) hm hwa fun hm₂ => ⟨G, ih hb hm₂⟩
  | val p r res =>
    cases hret
    exact callVal_sim f args p r res body (Nat.le_add_right _ _) hm hwa
      fun hm₂ => ⟨G, ih hb hm₂⟩
  | rets _ => cases hret
  | mem _ _ _ _ => cases hret

end Families


/-! ## Statements and blocks -/

section Sim

variable {L b : Nat} {Γ : Ctx} {F : Frag Γ} {σ : Solidity.Core.State C Γ} {m : Machine}

/-- **A sequence**: the first statement, then the rest from where it left
both; after a refused payment the machine has stopped, and the interpreter
goes on from the world that paid. -/
theorem seq_sim {Γ₁ Γ₂ : Ctx} (s : Solidity.Core.Stmt C Γ Γ₁) (P : Solidity.Core.Prog C Γ₁ Γ₂)
    {L₁ L₂ : Nat} {F₁ : Frag Γ₁} {F₂ : Frag Γ₂} {sh₁ p₁ a₁ sh₂ p₂ a₂ : Bool}
    (hs : StmtOut C L₁ b F₁ sh₁ p₁ a₁ (Solidity.Core.Stmt.run σ s) (run (compileStmt b s) m) m)
    (hP : ∀ {τ : Solidity.Core.State C Γ₁} {m₁ : Machine},
      Sim C L₁ b F₁ τ.glob (Look.ofEnv τ.env) m₁ →
      StmtOut C L₂ b F₂ sh₂ p₂ a₂ (Solidity.Core.Prog.run τ P) (run (compileProg b P) m₁) m₁) :
    StmtOut C L₂ b F₂ (sh₁ || sh₂) (p₁ || p₂) (a₁ || a₂)
      (Solidity.Core.Prog.run σ (.cons s P)) (run (compileProg b (.cons s P)) m) m := by
  rw [Solidity.Core.Prog.run_cons]
  simp only [compileProg]
  rcases hs with ⟨τ₁, m₁, hτ₁, hrun₁, hst₁, hk₁, hm₁⟩ | ⟨hτ₁, hrun₁⟩ | ⟨ha₁, hτ₁, hrun₁⟩ |
      ⟨hp₁, hrun₁, τ₁, m₁, hτ₁, hk₁, hm₁⟩
  · rw [run_append_ok hrun₁, hτ₁]
    rcases hP hm₁ with ⟨τ₂, m₂, hτ₂, hrun₂, hst₂, hk₂, hm₂⟩ | ⟨hτ₂, hrun₂⟩ | ⟨ha₂, hτ₂, hrun₂⟩ |
        ⟨hp₂, hrun₂, τ₂, m₂, hτ₂, hk₂, hm₂⟩
    · exact .inl ⟨τ₂, m₂, hτ₂, hrun₂, hst₂.trans hst₁, hk₁.trans hk₂, hm₂⟩
    · exact .inr ⟨hτ₂, hrun₂⟩
    · exact .panic (by simp only [ha₂, Bool.or_true]) ⟨hτ₂, hrun₂⟩
    · exact .refused (by simp only [hp₂, Bool.or_true]) ⟨hrun₂, τ₂, m₂, hτ₂, hk₁.trans hk₂, hm₂⟩
  · exact .inr ⟨by rw [hτ₁]; rfl, run_append_revert hrun₁⟩
  · exact .panic (by simp only [ha₁, Bool.true_or]) ⟨by rw [hτ₁]; rfl, run_append_revert hrun₁⟩
  · -- the machine stopped at a refused payment; the interpreter goes on
    rw [run_append_revert hrun₁, hτ₁]
    rcases hP hm₁ with ⟨τ₂, m₂, hτ₂, -, -, hk₂, hm₂⟩ | ⟨hτ₂, -⟩ | ⟨ha₂, hτ₂, -⟩ |
        ⟨-, -, τ₂, m₂, hτ₂, hk₂, hm₂⟩
    · exact .refused (by simp only [hp₁, Bool.true_or]) ⟨rfl, τ₂, m₂, hτ₂, hk₁.trans hk₂, hm₂⟩
    · exact .inr ⟨hτ₂, rfl⟩
    · exact .panic (by simp only [ha₂, Bool.or_true]) ⟨hτ₂, rfl⟩
    · exact .refused (by simp only [hp₁, Bool.true_or]) ⟨rfl, τ₂, m₂, hτ₂, hk₁.trans hk₂, hm₂⟩

mutual

/-- **A statement's code does what the statement does**: both succeed, the
machine's stack as it was, the cells below the frame and (unless it may
shrink one) every array's length kept, and the states related; or both
revert; or, in code with an `assert`, the interpreter panics where the
machine reverts; or, in code that pays, the world refuses a payment and the
machine alone reverts.

Example: `alice.age = 10;` is `PUSH 10; PUSH @11; PUSH 2; ADD; SSTORE`, which
writes slot `13`; `require(total > 3);` with `total = 2` reverts in both. -/
theorem stmt_sim : ∀ {Γ Γ' : Ctx} (s : Solidity.Core.Stmt C Γ Γ') {L b : Nat} {F : Frag Γ}
    {F' : Frag Γ'} {σ : Solidity.Core.State C Γ} {m : Machine},
    Sim C L b F σ.glob (Look.ofEnv σ.env) m → inFrag F s = some F' → L + Stmt.pushes s ≤ Lmax →
      StmtOut C (L + Stmt.pushes s) b F' (Stmt.shrinks s) (Stmt.pays s) (Stmt.asserts s)
        (Solidity.Core.Stmt.run σ s) (run (compileStmt b s) m) m
  | _, _, .assign l r => fun hm hw _ => assign_family l r hm hw
  | _, _, .rebind i r => fun hm hw _ => rebind_family i r hm hw
  | _, _, .assignLocal i r => fun hm hw _ => assignLocal_family i r hm hw
  | _, _, .declLocal p x init => fun hm hw _ => declLocal_family p x init hm hw
  | _, _, .declStorage R x init => fun hm hw _ =>
    declStorage_family R x init hm hw
  | _, _, .opAssign op hop hp l r => fun hm hw _ =>
    opAssign_family op hop hp l r hm hw
  | _, _, .incDec op hp l => fun hm hw _ => incDec_family op hp l hm hw
  | _, _, .assignIncDec i op hp l hs => fun hm hw _ =>
    assignIncDec_family i op hp l hs hm hw
  | _, _, .push q v hd => fun hm hw hL => push_family q v hd hm hw hL
  | _, _, .pop q => fun hm hw _ => pop_family q hm hw
  | _, _, .transfer r a => fun hm hw _ => transfer_family r a hm hw
  | _, _, .delete l => fun hm hw _ => delete_family l hm hw
  | _, _, .require c => fun hm hw _ => require_family c hm hw
  | _, _, .assert c => fun hm hw _ => assert_family c hm hw
  | _, _, .revert => fun _ _ _ => .inr ⟨rfl, rfl⟩
  | _, _, .ite c t e => fun hm hw hL => by
    obtain ⟨hwc, F₁, F₂, ht, he, rfl⟩ := ite_frag hw
    have hL' : _ + (Prog.pushes t + Prog.pushes e) ≤ Lmax := hL
    have hite : Stmt.pushes (.ite c t e) = Prog.pushes t + Prog.pushes e := rfl
    exact ite_sim c t e hm hwc ((prog_sim t hm ht (by omega)).mono (by omega) hL')
      ((prog_sim e hm he (by omega)).mono (by omega) hL')
  | _, _, .block body => fun hm hw hL => by
    obtain ⟨G, hb, rfl⟩ := block_frag hw
    exact block_sim body (prog_sim body hm hb hL)
  | _, _, .call f args ret body => fun hm hw hL =>
    call_family f args ret body hm hw fun hb hm₂ => prog_sim body hm₂ hb hL
  | _, _, .send .. => fun _ hw _ => by simp only [inFrag, reduceCtorEq] at hw
  | _, _, .declMem .. => fun _ hw _ => by simp only [inFrag, reduceCtorEq] at hw
  | _, _, .rebindMem .. => fun _ hw _ => by simp only [inFrag, reduceCtorEq] at hw
  | _, _, .assignFromMem .. => fun _ hw _ => by
    simp only [inFrag, reduceCtorEq] at hw
  | _, _, .assignMem .. => fun _ hw _ => by simp only [inFrag, reduceCtorEq] at hw
  | _, _, .deleteMem .. => fun _ hw _ => by simp only [inFrag, reduceCtorEq] at hw
  | _, _, .assignNew .. => fun _ hw _ => by simp only [inFrag, reduceCtorEq] at hw
  | _, _, .tryCall .. => fun _ hw _ => by simp only [inFrag, reduceCtorEq] at hw
  | _, _, .loop .. => fun _ hw _ => by simp only [inFrag, reduceCtorEq] at hw

/-- A block's code does what the block does. -/
theorem prog_sim : ∀ {Γ Γ' : Ctx} (P : Solidity.Core.Prog C Γ Γ') {L b : Nat} {F : Frag Γ}
    {F' : Frag Γ'} {σ : Solidity.Core.State C Γ} {m : Machine},
    Sim C L b F σ.glob (Look.ofEnv σ.env) m → inFragP F P = some F' → L + Prog.pushes P ≤ Lmax →
      StmtOut C (L + Prog.pushes P) b F' (Prog.shrinks P) (Prog.pays P) (Prog.asserts P)
        (Solidity.Core.Prog.run σ P) (run (compileProg b P) m) m
  | _, _, .nil => fun hm hw _ => by
    simp only [inFragP, Option.some.injEq] at hw
    subst hw
    exact .inl ⟨_, _, rfl, rfl, rfl, Keeps.refl _, hm⟩
  | _, _, .cons s P => fun hm hw hL => by
    simp only [inFragP] at hw
    split at hw
    · rename_i F₁ hs
      have hL' : _ + (Stmt.pushes s + Prog.pushes P) ≤ Lmax := hL
      have he : Prog.pushes (.cons s P) = Stmt.pushes s + Prog.pushes P := rfl
      rw [he] at hL ⊢
      exact seq_sim s P (stmt_sim s hm hs (by omega))
        fun hm₁ => (prog_sim P hm₁ hw (by omega)).mono (by omega) hL'
    · cases hw

end

end Sim

end Core
end Solidity.Evm
