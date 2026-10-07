import Solidity.Evm.CoreStmt

/-!
# The scoped compiler is correct

`Evm/Correctness.lean`'s headline over the scoped syntax and the typed run
(`docs/intrinsic.md`, M5, W1): `stmt_sim`/`prog_sim` by structural recursion on `Core.Stmt`/`Core.Prog`,
each statement dispatched to its lemma in `Evm/CoreStmt.lean` or, for the
statements with a sub-program, to a lemma here that takes the sub-program's
outcome as a hypothesis (`ite_sim`, `block_sim`, `call_family`), so that every
family elaborates on its own.  Then `compile_correct`, `compile_exact`,
`compile_box`, `compile_net` and `compile_storage`.

A scope's end pops its locals in the state (`TState.drop`) and nothing on
the machine: the cells stay, above the enclosing scope's level, and
`Sim.drop` forgets them.  A branch's fragment is met with the other's
(`Frag.meet`).  A call's body may grow the heap; the caller's locals come
back weakened along it (`TEnv.wk`), which `Look.ofTEnv` does not see.

There is no `not_stuck` here: the typed run has no `stuck`, and from a state
some machine represents (`Sim`) the fragment never diverges either, which
`compile_correct` says by listing every outcome without it.  `stmt_sim`
checks within `maxHeartbeats 10000` (the W1 gate, pinned below).
-/

namespace Solidity.Evm
namespace Core

open Semantics
open SemanticsProperties
open Solidity.Core (Ctx Idx Ext TEnv TState SRef TRes HTy)

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
  ⟨h.mem, fun h' => h.len (by
    cases sh <;> simp_all only [Bool.false_eq_true, Bool.true_eq_false, implies_true])⟩

/-- A scope's end in the state: its locals popped. -/
theorem Sim.dropState {Γ Δ : Ctx} {G : Frag Δ} {τ : TState C Δ} (h : Ext Γ Δ)
    (hm : Sim C L b G τ.sem (Look.ofTEnv τ.env) m) :
    Sim C L b (G.restrict Γ) (τ.drop h).sem (Look.ofTEnv (τ.drop h).env) m :=
  (hm.drop h).congrLook fun i => Look.ofTEnv_drop h τ.env i

/-- The outcome of a scope, its locals popped. -/
theorem StmtOut.drop {Γ Δ : Ctx} {G : Frag Δ} (h : Ext Γ Δ) {H : HTy}
    {res : TRes (Solidity.Core.Out C H Δ)} (hs : StmtOut C L b G sh pays asserts res out m) :
    StmtOut C L b (G.restrict Γ) sh pays asserts
      (res.map fun o => (⟨o.st.drop h, o.ext⟩ : Solidity.Core.Out C H Γ)) out m := by
  rcases hs with ⟨o, m', h1, h2, h3, h4, h5⟩ | ⟨h1, h2⟩ | ⟨ha, h1, h2⟩ |
      ⟨hp, h1, o, m', h2, h4, h5⟩
  · exact .inl ⟨⟨o.st.drop h, o.ext⟩, m', by rw [h1]; rfl, h2, h3, h4, Sim.dropState h h5⟩
  · exact .inr ⟨by rw [h1]; rfl, h2⟩
  · exact .panic ha ⟨by rw [h1]; rfl, h2⟩
  · exact .refused hp ⟨h1, ⟨o.st.drop h, o.ext⟩, m', by rw [h2]; rfl, h4, Sim.dropState h h5⟩

/-- An outcome under weaker flags: fewer aliases known, a statement that
may shrink, pay or assert more. -/
theorem StmtOut.weaken {G G' : Frag Γ'} {sh' pays' asserts' : Bool} {H : HTy}
    {res : TRes (Solidity.Core.Out C H Γ')}
    (hG : ∀ {R : RefTy} (i : Idx Γ' (.alias R)) (g : Fl), G'.get i = g → g ≠ .dead → G.get i = g)
    (hs : sh = true → sh' = true) (hp : pays = true → pays' = true)
    (ha : asserts = true → asserts' = true) (h : StmtOut C L b G sh pays asserts res out m) :
    StmtOut C L b G' sh' pays' asserts' res out m := by
  rcases h with ⟨o, m', h1, h2, h3, h4, h5⟩ | h | ⟨ha', h⟩ | ⟨hp', h1, o, m', h2, h4, h5⟩
  · exact .inl ⟨o, m', h1, h2, h3, h4.weaken hs, h5.flags hG⟩
  · exact .inr h
  · exact .panic (ha ha') h
  · exact .refused (hp hp') ⟨h1, o, m', h2, h4.weaken hs, h5.flags hG⟩

/-- An outcome whose states are carried along a map that keeps what `Sim`
reads of them. -/
theorem StmtOut.map {H : HTy} {Γ'' : Ctx} {F'' : Frag Γ''} {res : TRes (Solidity.Core.Out C H Γ')}
    {G : Frag Γ'} (f : Solidity.Core.Out C H Γ' → Solidity.Core.Out C H Γ'')
    (hf : ∀ (o : Solidity.Core.Out C H Γ') {m' : Machine},
      Sim C L b G o.st.sem (Look.ofTEnv o.st.env) m' →
        Sim C L b F'' (f o).st.sem (Look.ofTEnv (f o).st.env) m')
    (h : StmtOut C L b G sh pays asserts res out m) :
    StmtOut C L b F'' sh pays asserts (res.map f) out m := by
  rcases h with ⟨o, m', h1, h2, h3, h4, h5⟩ | ⟨h1, h2⟩ | ⟨ha, h1, h2⟩ |
      ⟨hp, h1, o, m', h2, h4, h5⟩
  · exact .inl ⟨f o, m', by rw [h1]; rfl, h2, h3, h4, hf o h5⟩
  · exact .inr ⟨by rw [h1]; rfl, h2⟩
  · exact .panic ha ⟨by rw [h1]; rfl, h2⟩
  · exact .refused hp ⟨h1, f o, m', by rw [h2]; rfl, h4, hf o h5⟩

end Outcomes

/-! ## Branches and blocks -/

section Scopes

variable {L b : Nat} {Γ : Ctx} {F : Frag Γ} {σ : TState C Γ} {m : Machine}

/-- **`if (c) { t } else { e }`**: the condition, then the branch it picks,
whose locals are popped; the branches' fragments met.

Example: `if (total > 3) { uint x = 1; total = x; } else { revert(); }` runs
`MSTORE %0` in the `then` branch, and `x` is gone after it. -/
theorem ite_sim {Γ₁ Γ₂ : Ctx} (c : Solidity.Core.Val C Γ .bool)
    (t : Solidity.Core.Prog C Γ Γ₁) (e : Solidity.Core.Prog C Γ Γ₂) {F₁ : Frag Γ₁}
    {F₂ : Frag Γ₂} {L' : Nat} (hm : Sim C L b F σ.sem (Look.ofTEnv σ.env) m)
    (hwc : valIn F c = true)
    (iht : StmtOut C L' b F₁ (Prog.shrinks t) (Prog.pays t) (Prog.asserts t)
      (Solidity.Core.Prog.trun σ t) (run (compileProg b t) m) m)
    (ihe : StmtOut C L' b F₂ (Prog.shrinks e) (Prog.pays e) (Prog.asserts e)
      (Solidity.Core.Prog.trun σ e) (run (compileProg b e) m) m) :
    StmtOut C L' b ((F₁.restrict Γ).meet (F₂.restrict Γ)) (Prog.shrinks t || Prog.shrinks e)
      (Prog.pays t || Prog.pays e) (Prog.asserts t || Prog.asserts e)
      (Solidity.Core.Stmt.trun σ (.ite c t e)) (run (compileStmt b (.ite c t e)) m) m := by
  show StmtOut C L' b _ _ _ _ (Solidity.Core.TRun.ite c t.ext t.trunR e.ext e.trunR σ) _ m
  simp only [compileStmt, List.append_assoc]
  rcases val_sim c hm hwc with ⟨vc, wc, hvc, hrc, hrunc⟩ | ⟨hvc, hrunc⟩
  · obtain ⟨x, hx, rfl⟩ := hrc.bool_inv
    obtain rfl : vc = x := Semantics.PrimVal.bool.inj hx
    rw [run_append_ok hrunc]
    simp only [Solidity.Core.TRun.ite, hvc, bind, Except.bind, Solidity.Core.boolT]
    cases vc
    · rw [run_append_skip (m' := m) (k := (compileProg b t).length + 1) rfl, exec_skip_append,
        show exec ([Instr.jump (compileProg b e).length] ++ compileProg b e) 1 m =
          run (compileProg b e) m from rfl]
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact (ihe.drop e.ext).weaken (fun i _ hg hd => Frag.get_meet_right _ _ i hg hd)
        (by simp_all only [Bool.or_true, implies_true])
        (by simp_all only [Bool.or_true, implies_true])
        (by simp_all only [Bool.or_true, implies_true])
    · rw [run_append_skip (m' := m) (k := 0) rfl]
      simp only [↓reduceIte]
      refine (StmtOut.drop (sh := Prog.shrinks t) (pays := Prog.pays t)
        (asserts := Prog.asserts t) t.ext ?_).weaken (fun i _ hg hd => Frag.get_meet _ _ i hg hd)
        (by simp_all only [Bool.true_or, implies_true])
        (by simp_all only [Bool.true_or, implies_true])
        (by simp_all only [Bool.true_or, implies_true])
      rcases iht with ⟨τ', m', hτ', hrun', hst', hk', hm'⟩ | ⟨hτ', hrun'⟩ | ⟨ha, hτ', hrun'⟩ |
          ⟨hp, hrun', τ', m', hτ', hk', hm'⟩
      · refine .inl ⟨τ', m', hτ', ?_, hst', hk', hm'⟩
        change run _ m = _
        rw [run_append_skip (k := 0) hrun']
        exact exec_length (.jump (compileProg b e).length :: compileProg b e) m' |>.trans rfl
      · exact .inr ⟨hτ', run_append_revert hrun'⟩
      · exact .panic ha ⟨hτ', run_append_revert hrun'⟩
      · exact .refused hp ⟨run_append_revert hrun', τ', m', hτ', hk', hm'⟩
  · exact .inr ⟨by simp only [Solidity.Core.TRun.ite, hvc, bind, Except.bind],
      run_append_revert hrunc⟩

/-- **`{ … }`**: the body, its locals popped. -/
theorem block_sim {Γ₁ : Ctx} (body : Solidity.Core.Prog C Γ Γ₁) {G : Frag Γ₁} {L' : Nat}
    {sh pays asserts : Bool}
    (ih : StmtOut C L' b G sh pays asserts (Solidity.Core.Prog.trun σ body)
      (run (compileProg b body) m) m) :
    StmtOut C L' b (G.restrict Γ) sh pays asserts (Solidity.Core.Stmt.trun σ (.block body))
      (run (compileStmt b (.block body)) m) m :=
  ih.drop body.ext

end Scopes

/-! ## Calls -/

section Calls

variable {L b : Nat} {Γ : Ctx} {F : Frag Γ} {σ : TState C Γ} {m : Machine}

theorem Args.evalT_snoc {ps : Ctx} (as : Solidity.Core.Args C Γ ps) (p : PrimTy) (x : Var)
    (e : Solidity.Core.Val C Γ p) :
    Solidity.Core.Args.evalT σ (.snoc as p x e) =
      (do let r ← Solidity.Core.Args.evalT σ as; let v ← e.evalT σ; pure (v, r)) := rfl

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
theorem args_sim (hm : Sim C L b F σ.sem (Look.ofTEnv σ.env) m) :
    ∀ {ps : Ctx} (args : Solidity.Core.Args C Γ ps), argsIn F args = true →
      (∃ a mem', Solidity.Core.Args.evalT σ args = .ok a ∧
        run (argsCode b args) m = .ok { m with mem := mem' } 0 ∧
        (∀ l, l < b + Γ.length → mem' (cell l) = m.mem (cell l)) ∧
        ∀ {p : PrimTy} (i : Idx ps (.val p)), ReprV p (PrimTy.erase (Look.ofTEnv a i))
          (({ m with mem := mem' } : Machine).memAt (lvl (b + Γ.length) i))) ∨
      (Solidity.Core.Args.evalT σ args = .error .revert ∧ run (argsCode b args) m = .revert)
  | _, .nil, _ => .inl ⟨(), m.mem, rfl, rfl, fun _ _ => rfl, fun i => nomatch i⟩
  | _, @Solidity.Core.Args.snoc _ _ ps as p x e, hw => by
    simp only [argsIn, Bool.and_eq_true] at hw
    rw [Args.evalT_snoc]
    simp only [argsCode, List.append_assoc]
    rcases args_sim hm as hw.1 with ⟨a, mem₁, ha, hrun₁, hmem₁, hv₁⟩ | ⟨ha, hrun₁⟩
    · rw [ha, run_append_ok hrun₁]
      have hm₁ := hm.congrMem (mem := mem₁) fun l _ hl => hmem₁ l hl
      rcases val_sim e hm₁ hw.2 with ⟨v, w, hv, hrv, hrun⟩ | ⟨hv, hrun⟩
      · rw [run_append_ok hrun]
        refine .inl ⟨(v, a), upd mem₁ (cell (b + Γ.length + ps.length)) w,
          by simp only [bind, Except.bind, hv, pure, Except.pure], rfl, fun l hl => ?_, fun i => ?_⟩
        · rw [upd_other _ _ (fun h => by have := cell_inj h; omega)]; exact hmem₁ l hl
        · cases i with
          | here =>
            show ReprV _ (PrimTy.erase v) (upd mem₁ _ w (cell (lvl _ (Idx.here (Γ := ps)))))
            rw [lvl_here, upd_same]; exact hrv
          | there j =>
            show ReprV _ (PrimTy.erase (Look.ofTEnv a j))
              (upd mem₁ _ w (cell (lvl _ (Idx.there (u := .val p) j))))
            have := lvl_lt (b + Γ.length) j
            rw [lvl_there, upd_other _ _ (fun h => by have := cell_inj h; omega)]; exact hv₁ j
      · exact .inr ⟨by simp only [bind, Except.bind, hv], run_append_revert hrun⟩
    · exact .inr ⟨by simp only [bind, Except.bind, ha], run_append_revert hrun₁⟩

/-- **Back from a call**: the caller's locals where they were (the callee
kept every cell below its frame), its storage, ledger and transaction the
callee's, its fragile aliases forgotten if the callee may have shrunk an
array; and what the call keeps, from what its body keeps. -/
theorem Sim.back {Δ : Ctx} {G : Frag Δ} {τ : Semantics.State} {ρ' : Look C Δ} {m₁ m₃ : Machine}
    {sh : Bool} {L' : Nat} (hL : L ≤ L') (hm : Sim C L b F σ.sem (Look.ofTEnv σ.env) m)
    (h₁ : ∀ l, l < b + Γ.length → m₁.memAt l = m.memAt l) (hs₁ : m₁.store = m.store)
    (hk : Keeps C (b + Γ.length) sh m₁ m₃) (h₃ : Sim C L' (b + Γ.length) G τ ρ' m₃) :
    Sim C L' b (F.after sh) τ (Look.ofTEnv σ.env) m₃ ∧ Keeps C b sh m m₃ := by
  have hm' := hm.mono hL h₃.bound
  have hmem : ∀ l, l < b + Γ.length → m₃.memAt l = m.memAt l :=
    fun l hl => (hk.mem l hl).trans (h₁ l hl)
  have hlen : sh = false → ∀ x, LenSlot C x → m.store x ≤ m₃.store x :=
    fun hsh x hx => by rw [← hs₁]; exact hk.len hsh x hx
  refine ⟨?_, ⟨fun l hl => hmem l (by omega), hlen⟩⟩
  cases sh
  · exact hm'.return h₃ hmem (hlen rfl)
  · exact hm'.returnDrop h₃ hmem

/-- A call whose arguments are in: the body run in its frame, and the
caller's locals, weakened along the heap the body grew, given back what the
call leaves them. -/
theorem call_run_eq {Γ' ps rs Γf : Ctx} (f : Name) (args : Solidity.Core.Args C Γ ps)
    (ret : Solidity.Core.CallRet Γ rs Γ') (body : Solidity.Core.Prog C (rs ++ ps) Γf)
    {a : TEnv C σ.H ps} (ha : Solidity.Core.Args.evalT σ args = .ok a) :
    Solidity.Core.Stmt.trun σ (.call f args ret body) =
      (Solidity.Core.Prog.trun (ret.enterT (σ.withEnv a)).st body).map fun o =>
        ⟨o.st.withEnv (ret.leaveT
          (TEnv.wk ((ret.enterT (σ.withEnv a)).ext.trans o.ext) Γ σ.env)
          (TEnv.take rs (TEnv.drop body.ext o.st.env))),
          (ret.enterT (σ.withEnv a)).ext.trans o.ext⟩ := by
  show Solidity.Core.TRun.call args ret body.ext body.trunR σ =
    Except.map _ (body.trunR (ret.enterT (σ.withEnv a)).st)
  simp only [Solidity.Core.TRun.call, ha, bind, Except.bind]
  cases body.trunR (ret.enterT (σ.withEnv a)).st <;> rfl

theorem TEnv.get_drop {H : HTy} {Γ₀ Δ : Ctx} (h : Ext Γ₀ Δ) (e : TEnv C H Δ) {t : CLTy}
    (i : Idx Γ₀ t) : TEnv.get i (TEnv.drop h e) = TEnv.get (i.ext h) e := by
  induction h with
  | refl => rfl
  | push h ih => exact ih e.2

/-- A call with no return value, run. -/
theorem callNone_run_eq {ps Γf : Ctx} (f : Name) (args : Solidity.Core.Args C Γ ps)
    (body : Solidity.Core.Prog C ([] ++ ps) Γf) {a : TEnv C σ.H ps}
    (ha : Solidity.Core.Args.evalT σ args = .ok a) :
    Solidity.Core.Stmt.trun σ (.call f args .none body) =
      (Solidity.Core.Prog.trun (σ.withEnv a) body).map fun o =>
        ⟨o.st.withEnv (TEnv.wk o.ext Γ σ.env), o.ext⟩ :=
  call_run_eq f args .none body ha

/-- A call with one return value, run: the body from the frame with the
return variable at its default. -/
theorem callVal_run_eq {ps Γf : Ctx} (f : Name) (args : Solidity.Core.Args C Γ ps) (p : PrimTy)
    (r : Var) (res : Option (Idx Γ (.val p))) (body : Solidity.Core.Prog C ([.val p] ++ ps) Γf)
    {a : TEnv C σ.H ps} (ha : Solidity.Core.Args.evalT σ args = .ok a) :
    Solidity.Core.Stmt.trun σ (.call f args (.val p r res) body) =
      (Solidity.Core.Prog.trun ((σ.withEnv a).push (t := .val p) (PrimTy.dflt p)) body).map
        fun (o : Solidity.Core.Out C ((σ.withEnv a).push (t := .val p) (PrimTy.dflt p)).H Γf) =>
          (⟨o.st.withEnv (match res with
          | some i => TEnv.set i (TEnv.get (Idx.ext Idx.here body.ext) o.st.env)
              (TEnv.wk o.ext Γ σ.env)
          | none => TEnv.wk o.ext Γ σ.env), o.ext⟩ : Solidity.Core.Out C σ.H Γ) := by
  rw [call_run_eq f args (.val p r res) body ha]
  congr 1
  funext o
  cases res with
  | none => rfl
  | some y =>
    show (⟨o.st.withEnv (TEnv.set y (TEnv.drop body.ext o.st.env).1 _), _⟩ :
      Solidity.Core.Out C σ.H Γ) = _
    rw [show (TEnv.drop body.ext o.st.env).1 = TEnv.get Idx.here (TEnv.drop body.ext o.st.env)
      from rfl, TEnv.get_drop]

/-- **A call with no return value**, `f(e);`: the arguments in the frame,
the body, back. -/
theorem callNone_sim {ps Γf : Ctx} (f : Name) (args : Solidity.Core.Args C Γ ps)
    (body : Solidity.Core.Prog C ([] ++ ps) Γf) {L' : Nat} {sh pays asserts : Bool}
    (hL : L ≤ L') (hm : Sim C L b F σ.sem (Look.ofTEnv σ.env) m) (hwa : argsIn F args = true)
    (ih : ∀ {τ : TState C ([] ++ ps)} {m₂ : Machine},
      Sim C L (b + Γ.length) (Frag.init ([] ++ ps)) τ.sem (Look.ofTEnv τ.env) m₂ →
      ∃ G : Frag Γf, StmtOut C L' (b + Γ.length) G sh pays asserts
        (Solidity.Core.Prog.trun τ body) (run (compileProg (b + Γ.length) body) m₂) m₂) :
    StmtOut C L' b (F.after sh) sh pays asserts
      (Solidity.Core.Stmt.trun σ (.call f args .none body))
      (run (compileStmt b (.call f args .none body)) m) m := by
  simp only [compileStmt, retEnterCode, retLeaveCode, List.append_nil]
  rcases args_sim hm args hwa with ⟨a, mem₁, ha, hrun₁, hmem₁, hv₁⟩ | ⟨ha, hrun₁⟩
  · rw [run_append_ok hrun₁, callNone_run_eq f args body ha]
    have hb := (hm.congrMem (mem := mem₁) fun l _ hl => hmem₁ l hl).enter (b + Γ.length)
      (Look.ofTEnv a) hv₁ (Args.noAlias args)
    obtain ⟨G, hout⟩ := ih (τ := σ.withEnv a) hb
    have h₁ : ∀ l, l < b + Γ.length →
        ({ m with mem := mem₁ } : Machine).memAt l = m.memAt l := fun l hl => hmem₁ l hl
    rcases hout with ⟨υ, m₃, hυ, hrun₃, hst₃, hk₃, hm₃⟩ | ⟨hυ, hrun₃⟩ | ⟨hasr, hυ, hrun₃⟩ |
        ⟨hp, hrun₃, υ, m₃, hυ, hk₃, hm₃⟩
    · obtain ⟨hs, hk⟩ := Sim.back hL hm h₁ rfl hk₃ hm₃
      exact .inl ⟨_, m₃, by rw [hυ]; rfl, hrun₃, hst₃, hk,
        hs.congrLook fun i => Look.ofTEnv_wk υ.ext σ.env i⟩
    · exact .inr ⟨by rw [hυ]; rfl, hrun₃⟩
    · exact .panic hasr ⟨by rw [hυ]; rfl, hrun₃⟩
    · obtain ⟨hs, hk⟩ := Sim.back hL hm h₁ rfl hk₃ hm₃
      exact .refused hp ⟨hrun₃, _, m₃, by rw [hυ]; rfl, hk,
        hs.congrLook fun i => Look.ofTEnv_wk υ.ext σ.env i⟩
  · refine .inr ⟨?_, run_append_revert hrun₁⟩
    show Solidity.Core.TRun.call args .none body.ext body.trunR σ = _
    simp only [Solidity.Core.TRun.call, ha, bind, Except.bind]

/-- **A call with a return value**, `y = f(e);` (or `f(e);` dropping it): the
arguments and the return variable (`0`) in the frame, the body, back, and
the return variable's word copied into `y`'s cell.

Example: `uint y = addTwo(3);` stores `3` at `%1`, `0` at `%2`, runs
`addTwo`'s body above level `1`, then `MLOAD %2; MSTORE %0`. -/
theorem callVal_sim {ps Γf : Ctx} (f : Name) (args : Solidity.Core.Args C Γ ps) (p : PrimTy)
    (r : Var) (res : Option (Idx Γ (.val p))) (body : Solidity.Core.Prog C ([.val p] ++ ps) Γf)
    {L' : Nat} {sh pays asserts : Bool}
    (hL : L ≤ L') (hm : Sim C L b F σ.sem (Look.ofTEnv σ.env) m) (hwa : argsIn F args = true)
    (ih : ∀ {τ : TState C ([.val p] ++ ps)} {m₂ : Machine},
      Sim C L (b + Γ.length) (Frag.init ([.val p] ++ ps)) τ.sem (Look.ofTEnv τ.env) m₂ →
      ∃ G : Frag Γf, StmtOut C L' (b + Γ.length) G sh pays asserts
        (Solidity.Core.Prog.trun τ body) (run (compileProg (b + Γ.length) body) m₂) m₂) :
    StmtOut C L' b (F.after sh) sh pays asserts
      (Solidity.Core.Stmt.trun σ (.call f args (.val p r res) body))
      (run (compileStmt b (.call f args (.val p r res) body)) m) m := by
  simp only [compileStmt, List.append_assoc]
  rcases args_sim hm args hwa with ⟨a, mem₁, ha, hrun₁, hmem₁, hv₁⟩ | ⟨ha, hrun₁⟩
  · rw [run_append_ok hrun₁, callVal_run_eq f args p r res body ha]
    simp only [retEnterCode]
    rw [run_append_ok (m' := { m with mem := upd mem₁ (cell (b + Γ.length + ps.length)) (.val 0) })
      rfl]
    have hb := ((hm.congrMem (mem := mem₁) fun l _ hl => hmem₁ l hl).enter (b + Γ.length)
      (Look.ofTEnv a) hv₁ (Args.noAlias args)).consVal (v := PrimTy.dflt p)
      (by rw [PrimTy.erase_dflt]; exact ReprV.default p)
    obtain ⟨G, hout⟩ :=
      ih (τ := (σ.withEnv a).push (t := .val p) (PrimTy.dflt p))
        (hb.congrLook fun j => Look.ofTEnv_cons (u := .val p) (PrimTy.dflt p) a j)
    have h₁ : ∀ l, l < b + Γ.length →
        ({ m with mem := upd mem₁ (cell (b + Γ.length + ps.length)) (.val 0) } : Machine).memAt l =
          m.memAt l := fun l hl => by
      show upd mem₁ _ _ (cell l) = _
      rw [upd_other _ _ (fun h => by have := cell_inj h; omega)]; exact hmem₁ l hl
    -- what the call leaves the caller, from the machine `m₃` and state `υ` the body left
    have leave : ∀ {υ : Solidity.Core.Out C ((σ.withEnv a).push (t := .val p) (PrimTy.dflt p)).H Γf}
        {m₃ : Machine},
        Keeps C (b + Γ.length) sh
          { m with mem := upd mem₁ (cell (b + Γ.length + ps.length)) (.val 0) } m₃ →
        Sim C L' (b + Γ.length) G υ.st.sem (Look.ofTEnv υ.st.env) m₃ →
        ∃ m₄, run (retLeaveCode b ps (.val p r res)) m₃ = .ok m₄ 0 ∧ m₄.stack = m₃.stack ∧
          Keeps C b sh m m₄ ∧
          Sim C L' b (F.after sh)
            (υ.st.withEnv (match res with
              | some i => TEnv.set i (TEnv.get (Idx.ext Idx.here body.ext) υ.st.env)
                  (TEnv.wk υ.ext Γ σ.env)
              | none => TEnv.wk υ.ext Γ σ.env)).sem
            (Look.ofTEnv (υ.st.withEnv (match res with
              | some i => TEnv.set i (TEnv.get (Idx.ext Idx.here body.ext) υ.st.env)
                  (TEnv.wk υ.ext Γ σ.env)
              | none => TEnv.wk υ.ext Γ σ.env)).env) m₄ := by
      intro υ m₃ hk₃ hm₃
      obtain ⟨hs, hk⟩ := Sim.back hL hm h₁ rfl hk₃ hm₃
      have hs' : Sim C L' b (F.after sh) (υ.st.withEnv (TEnv.wk υ.ext Γ σ.env)).sem
          (Look.ofTEnv (υ.st.withEnv (TEnv.wk υ.ext Γ σ.env)).env) m₃ :=
        hs.congrLook fun i => Look.ofTEnv_wk υ.ext σ.env i
      cases res with
      | none => exact ⟨m₃, rfl, rfl, hk, hs'⟩
      | some y =>
        have hrv := hm₃.vals (Idx.ext (Idx.here (Γ := ps) (t := .val p)) body.ext)
        have hl : lvl (b + Γ.length) (Idx.ext (Idx.here (Γ := ps) (t := .val p)) body.ext) =
            b + Γ.length + ps.length := by
          rw [lvl_ext]
          simp only [lvl, Idx.toNat, List.length_cons]
          omega
        rw [hl] at hrv
        have hs'' := Sim.setLocalVal hs' y hrv
        refine ⟨_, rfl, rfl, (hk.trans (Keeps.upd (sh := false) (le_lvl b y) _)).weaken
          (by simp only [Bool.or_false, imp_self]), hs''⟩
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
    show Solidity.Core.TRun.call args (.val p r res) body.ext body.trunR σ = _
    simp only [Solidity.Core.TRun.call, ha, bind, Except.bind]

end Calls

/-! ## One lemma per family

What `inFrag` admits of each statement with no sub-program, and that
statement's lemma of `Evm/CoreStmt.lean`. -/

section Families

variable {L b : Nat} {Γ : Ctx} {F : Frag Γ} {σ : TState C Γ} {m : Machine}

theorem assign_family {T : Ty} (l : Solidity.Core.Loc C Γ T) (r : Solidity.Core.Src C Γ T)
    {F' : Frag Γ} (hm : Sim C L b F σ.sem (Look.ofTEnv σ.env) m)
    (hw : inFrag F (.assign l r) = some F') :
    StmtOut C L b F' false false false (Solidity.Core.Stmt.trun σ (.assign l r))
      (run (compileStmt b (.assign l r)) m) m := by
  simp only [inFrag] at hw
  obtain ⟨hok, rfl⟩ := Frag.guard_some hw
  cases r with
  | val v =>
    simp only [assignIn, Bool.and_eq_true] at hok
    exact assign_sim l v hm hok.1 hok.2
  | copy q hq =>
    simp only [assignIn, Bool.and_eq_true] at hok
    exact copy_sim l q hq hok.1.1.1 hok.1.1.2 hm hok.1.2 hok.2

theorem rebind_family {R : RefTy} (i : Idx Γ (.alias R)) (r : Solidity.Core.ARhs C Γ R)
    {F' : Frag Γ} (hm : Sim C L b F σ.sem (Look.ofTEnv σ.env) m)
    (hw : inFrag F (.rebind i r) = some F') :
    StmtOut C L b F' false false false (Solidity.Core.Stmt.trun σ (.rebind i r))
      (run (compileStmt b (.rebind i r)) m) m := by
  cases r with
  | path q => simp only [inFrag] at hw; exact rebind_sim i q hm hw
  | push _ _ => simp only [inFrag, reduceCtorEq] at hw

theorem assignLocal_family {p : PrimTy} (i : Idx Γ (.val p)) (r : Solidity.Core.Val C Γ p)
    {F' : Frag Γ} (hm : Sim C L b F σ.sem (Look.ofTEnv σ.env) m)
    (hw : inFrag F (.assignLocal i r) = some F') :
    StmtOut C L b F' false false false (Solidity.Core.Stmt.trun σ (.assignLocal i r))
      (run (compileStmt b (.assignLocal i r)) m) m := by
  simp only [inFrag] at hw
  obtain ⟨hok, rfl⟩ := Frag.guard_some hw
  exact assignLocal_sim i r hm hok

theorem declLocal_family (p : PrimTy) (x : Var) (init : Option (Solidity.Core.Val C Γ p))
    {F' : Frag (.val p :: Γ)} (hm : Sim C L b F σ.sem (Look.ofTEnv σ.env) m)
    (hw : inFrag F (.declLocal p x init) = some F') :
    StmtOut C L b F' false false false (Solidity.Core.Stmt.trun σ (.declLocal p x init))
      (run (compileStmt b (.declLocal p x init)) m) m := by
  simp only [inFrag] at hw
  obtain ⟨hok, rfl⟩ := Frag.guard_some hw
  cases init with
  | none => exact declLocal_sim p none hm hok
  | some e => exact declLocal_sim p (some e) hm hok

theorem declStorage_family (R : RefTy) (x : Var) (init : Option (Solidity.Core.ARhs C Γ R))
    {F' : Frag (.alias R :: Γ)} (hm : Sim C L b F σ.sem (Look.ofTEnv σ.env) m)
    (hw : inFrag F (.declStorage R x init) = some F') :
    StmtOut C L b F' false false false (Solidity.Core.Stmt.trun σ (.declStorage R x init))
      (run (compileStmt b (.declStorage R x init)) m) m := by
  simp only [inFrag] at hw
  rcases init with _ | (q | _)
  · simp only [declStorageIn, Option.some.injEq] at hw
    subst hw
    exact .inl ⟨⟨σ.push (t := .alias R) none, List.prefix_refl _⟩, m, rfl, rfl, rfl, Keeps.refl m,
      hm.pushDead R none⟩
  · exact declAlias_sim q hm hw
  · simp only [declStorageIn, reduceCtorEq] at hw

theorem opAssign_family {p : PrimTy} (op : BinOp) (hop : op.hasCompoundAssign = true)
    (hpn : p.isNumeric = true) (l : Solidity.Core.OpLoc C Γ p) (r : Solidity.Core.Val C Γ p)
    {F' : Frag Γ} (hm : Sim C L b F σ.sem (Look.ofTEnv σ.env) m)
    (hw : inFrag F (.opAssign op hop hpn l r) = some F') :
    StmtOut C L b F' false false false (Solidity.Core.Stmt.trun σ (.opAssign op hop hpn l r))
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
  | mfield _ _ _ => simp only [opLocIn, opLocToLoc, Bool.false_eq_true] at hl
  | mindex _ _ _ => simp only [opLocIn, opLocToLoc, Bool.false_eq_true] at hl

theorem incDec_family {p : PrimTy} (op : IncDec) (hpn : p.isNumeric = true)
    (l : Solidity.Core.OpLoc C Γ p) {F' : Frag Γ} (hm : Sim C L b F σ.sem (Look.ofTEnv σ.env) m)
    (hw : inFrag F (.incDec op hpn l) = some F') :
    StmtOut C L b F' false false false (Solidity.Core.Stmt.trun σ (.incDec op hpn l))
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
  | mfield _ _ _ => simp only [opLocIn, opLocToLoc, Bool.false_eq_true] at hl
  | mindex _ _ _ => simp only [opLocIn, opLocToLoc, Bool.false_eq_true] at hl

theorem assignIncDec_family {p : PrimTy} (i : Idx Γ (.val p)) (op : IncDec)
    (hpn : p.isNumeric = true) (l : Solidity.Core.OpLoc C Γ p) (hs : l.recvSimple = true)
    {F' : Frag Γ} (hm : Sim C L b F σ.sem (Look.ofTEnv σ.env) m)
    (hw : inFrag F (.assignIncDec i op hpn l hs) = some F') :
    StmtOut C L b F' false false false (Solidity.Core.Stmt.trun σ (.assignIncDec i op hpn l hs))
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
  | mfield _ _ _ => simp only [opLocIn, opLocToLoc, Bool.false_eq_true] at hl
  | mindex _ _ _ => simp only [opLocIn, opLocToLoc, Bool.false_eq_true] at hl

theorem push_family {E : Ty} (q : Solidity.Core.SPath C Γ (.array E))
    (v : Option (Solidity.Core.Src C Γ E)) (hd : (v.isSome || E.defaultOkS) = true) {F' : Frag Γ}
    (hm : Sim C L b F σ.sem (Look.ofTEnv σ.env) m) (hw : inFrag F (.push q v hd) = some F')
    (hL : L + 1 ≤ Lmax) :
    StmtOut C (L + 1) b F' false false false (Solidity.Core.Stmt.trun σ (.push q v hd))
      (run (compileStmt b (.push q v hd)) m) m := by
  simp only [inFrag] at hw
  obtain ⟨hok, rfl⟩ := Frag.guard_some hw
  exact push_sim q v hm hok hL

theorem pop_family {E : Ty} (q : Solidity.Core.SPath C Γ (.array E)) {F' : Frag Γ}
    (hm : Sim C L b F σ.sem (Look.ofTEnv σ.env) m) (hw : inFrag F (.pop q) = some F') :
    StmtOut C L b F' true false false (Solidity.Core.Stmt.trun σ (.pop q))
      (run (compileStmt b (.pop q)) m) m := by
  simp only [inFrag] at hw
  obtain ⟨hok, rfl⟩ := Frag.guard_some hw
  exact pop_sim q hm hok

theorem delete_family {T : Ty} (l : Solidity.Core.Loc C Γ T) {F' : Frag Γ}
    (hm : Sim C L b F σ.sem (Look.ofTEnv σ.env) m) (hw : inFrag F (.delete l) = some F') :
    StmtOut C L b F' true false false (Solidity.Core.Stmt.trun σ (.delete l))
      (run (compileStmt b (.delete l)) m) m := by
  simp only [inFrag] at hw
  obtain ⟨hok, rfl⟩ := Frag.guard_some hw
  exact delete_sim l hm hok

theorem transfer_family (r a : Solidity.Core.Val C Γ .uint) {F' : Frag Γ}
    (hm : Sim C L b F σ.sem (Look.ofTEnv σ.env) m) (hw : inFrag F (.transfer r a) = some F') :
    StmtOut C L b F' false true false (Solidity.Core.Stmt.trun σ (.transfer r a))
      (run (compileStmt b (.transfer r a)) m) m := by
  simp only [inFrag] at hw
  obtain ⟨hok, rfl⟩ := Frag.guard_some hw
  simp only [Bool.and_eq_true] at hok
  exact transfer_sim r a hm hok.1 hok.2

theorem require_family (c : Solidity.Core.Val C Γ .bool) {F' : Frag Γ}
    (hm : Sim C L b F σ.sem (Look.ofTEnv σ.env) m) (hw : inFrag F (.require c) = some F') :
    StmtOut C L b F' false false false (Solidity.Core.Stmt.trun σ (.require c))
      (run (compileStmt b (.require c)) m) m := by
  simp only [inFrag] at hw
  obtain ⟨hok, rfl⟩ := Frag.guard_some hw
  exact require_sim c hm hok

theorem assert_family (c : Solidity.Core.Val C Γ .bool) {F' : Frag Γ}
    (hm : Sim C L b F σ.sem (Look.ofTEnv σ.env) m) (hw : inFrag F (.assert c) = some F') :
    StmtOut C L b F' false false true (Solidity.Core.Stmt.trun σ (.assert c))
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
    {F' : Frag Γ'} (hm : Sim C L b F σ.sem (Look.ofTEnv σ.env) m)
    (hw : inFrag F (.call f args ret body) = some F')
    (ih : ∀ {G : Frag Γf} {τ : TState C (rs ++ ps)} {m₂ : Machine},
      inFragP (Frag.init (rs ++ ps)) body = some G →
      Sim C L (b + Γ.length) (Frag.init (rs ++ ps)) τ.sem (Look.ofTEnv τ.env) m₂ →
      StmtOut C (L + Prog.pushes body) (b + Γ.length) G (Prog.shrinks body) (Prog.pays body)
        (Prog.asserts body) (Solidity.Core.Prog.trun τ body)
        (run (compileProg (b + Γ.length) body) m₂) m₂) :
    StmtOut C (L + Stmt.pushes (.call f args ret body)) b F'
      (Stmt.shrinks (.call f args ret body)) (Stmt.pays (.call f args ret body))
      (Stmt.asserts (.call f args ret body)) (Solidity.Core.Stmt.trun σ (.call f args ret body))
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

variable {L b : Nat} {Γ : Ctx} {F : Frag Γ} {σ : TState C Γ} {m : Machine}

/-- A sequence whose first statement halts halts the same way. -/
theorem Prog.trun_cons_error {Γ₁ Γ₂ : Ctx} {s : Solidity.Core.Stmt C Γ Γ₁}
    {P : Solidity.Core.Prog C Γ₁ Γ₂} {e : Solidity.Core.THalt}
    (h : Solidity.Core.Stmt.trun σ s = .error e) :
    Solidity.Core.Prog.trun σ (.cons s P) = .error e := by
  show Solidity.Core.TRun.seq s.trunR P.trunR σ = _
  simp only [Solidity.Core.TRun.seq, Solidity.Core.Stmt.trun] at h ⊢
  rw [h]

/-- **A sequence**: the first statement, then the rest from where it left
both; after a refused payment the machine has stopped, and the typed run
goes on from the world that paid. -/
theorem seq_sim {Γ₁ Γ₂ : Ctx} (s : Solidity.Core.Stmt C Γ Γ₁) (P : Solidity.Core.Prog C Γ₁ Γ₂)
    {L₁ L₂ : Nat} {F₁ : Frag Γ₁} {F₂ : Frag Γ₂} {sh₁ p₁ a₁ sh₂ p₂ a₂ : Bool}
    (hs : StmtOut C L₁ b F₁ sh₁ p₁ a₁ (Solidity.Core.Stmt.trun σ s) (run (compileStmt b s) m) m)
    (hP : ∀ {τ : TState C Γ₁} {m₁ : Machine},
      Sim C L₁ b F₁ τ.sem (Look.ofTEnv τ.env) m₁ →
      StmtOut C L₂ b F₂ sh₂ p₂ a₂ (Solidity.Core.Prog.trun τ P) (run (compileProg b P) m₁) m₁) :
    StmtOut C L₂ b F₂ (sh₁ || sh₂) (p₁ || p₂) (a₁ || a₂)
      (Solidity.Core.Prog.trun σ (.cons s P)) (run (compileProg b (.cons s P)) m) m := by
  simp only [compileProg]
  rcases hs with ⟨τ₁, m₁, hτ₁, hrun₁, hst₁, hk₁, hm₁⟩ | ⟨hτ₁, hrun₁⟩ | ⟨ha₁, hτ₁, hrun₁⟩ |
      ⟨hp₁, hrun₁, τ₁, m₁, hτ₁, hk₁, hm₁⟩
  · rw [run_append_ok hrun₁, Solidity.Core.Prog.trun_cons_ok hτ₁]
    rcases hP hm₁ with ⟨τ₂, m₂, hτ₂, hrun₂, hst₂, hk₂, hm₂⟩ | ⟨hτ₂, hrun₂⟩ | ⟨ha₂, hτ₂, hrun₂⟩ |
        ⟨hp₂, hrun₂, τ₂, m₂, hτ₂, hk₂, hm₂⟩
    · exact .inl ⟨_, m₂, by rw [hτ₂]; rfl, hrun₂, hst₂.trans hst₁, hk₁.trans hk₂, hm₂⟩
    · exact .inr ⟨by rw [hτ₂]; rfl, hrun₂⟩
    · exact .panic (by simp only [ha₂, Bool.or_true]) ⟨by rw [hτ₂]; rfl, hrun₂⟩
    · exact .refused (by simp only [hp₂, Bool.or_true])
        ⟨hrun₂, _, m₂, by rw [hτ₂]; rfl, hk₁.trans hk₂, hm₂⟩
  · exact .inr ⟨Prog.trun_cons_error hτ₁, run_append_revert hrun₁⟩
  · exact .panic (by simp only [ha₁, Bool.true_or])
      ⟨Prog.trun_cons_error hτ₁, run_append_revert hrun₁⟩
  · -- the machine stopped at a refused payment; the typed run goes on
    rw [run_append_revert hrun₁, Solidity.Core.Prog.trun_cons_ok hτ₁]
    rcases hP hm₁ with ⟨τ₂, m₂, hτ₂, -, -, hk₂, hm₂⟩ | ⟨hτ₂, -⟩ | ⟨ha₂, hτ₂, -⟩ |
        ⟨-, -, τ₂, m₂, hτ₂, hk₂, hm₂⟩
    · exact .refused (by simp only [hp₁, Bool.true_or])
        ⟨rfl, _, m₂, by rw [hτ₂]; rfl, hk₁.trans hk₂, hm₂⟩
    · exact .inr ⟨by rw [hτ₂]; rfl, rfl⟩
    · exact .panic (by simp only [ha₂, Bool.or_true]) ⟨by rw [hτ₂]; rfl, rfl⟩
    · exact .refused (by simp only [hp₁, Bool.true_or])
        ⟨rfl, _, m₂, by rw [hτ₂]; rfl, hk₁.trans hk₂, hm₂⟩

set_option maxHeartbeats 10000 in
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
    {F' : Frag Γ'} {σ : TState C Γ} {m : Machine},
    Sim C L b F σ.sem (Look.ofTEnv σ.env) m → inFrag F s = some F' → L + Stmt.pushes s ≤ Lmax →
      StmtOut C (L + Stmt.pushes s) b F' (Stmt.shrinks s) (Stmt.pays s) (Stmt.asserts s)
        (Solidity.Core.Stmt.trun σ s) (run (compileStmt b s) m) m
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
    {F' : Frag Γ'} {σ : TState C Γ} {m : Machine},
    Sim C L b F σ.sem (Look.ofTEnv σ.env) m → inFragP F P = some F' → L + Prog.pushes P ≤ Lmax →
      StmtOut C (L + Prog.pushes P) b F' (Prog.shrinks P) (Prog.pays P) (Prog.asserts P)
        (Solidity.Core.Prog.trun σ P) (run (compileProg b P) m) m
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

/-! ## The headline -/

section Headline

variable {L b : Nat} {Γ Γ' : Ctx} {F : Frag Γ} {F' : Frag Γ'} {σ : TState C Γ}
  {m : Machine}

/-- **The compiler is correct.**  For a program of the fragment and a machine
representing the typed state it starts in, the typed run and the compiled
code agree: both succeed — the machine's stack as it was, its storage,
locals and balances representing the final state and ledger — or both
revert (a panic, a failed `assert`, is solc's revert with `Panic(0x01)`
data, and only code with an `assert` panics), or, in code that pays, the
world refuses a payment and the machine alone reverts.  There is no fourth
case: on the fragment the typed run neither diverges nor is stuck.

Example: from a state where `total = 3`,
```solidity
total += 1; if (total > 3) { delete alice; } else { revert(); }
```
runs to `total = 4` and a default `alice`, and on the machine to slot `0`
holding `4` and slots `11`–`13` holding `0`. -/
theorem compile_correct {P : Solidity.Core.Prog C Γ Γ'} (hP : inFragP F P = some F')
    (hm : Sim C L b F σ.sem (Look.ofTEnv σ.env) m) (hL : L + Prog.pushes P ≤ Lmax) :
    (∃ o m', Solidity.Core.Prog.trun σ P = .ok o ∧ run (compileProg b P) m = .ok m' 0 ∧
      m'.stack = m.stack ∧ Sim C (L + Prog.pushes P) b F' o.st.sem (Look.ofTEnv o.st.env) m') ∨
    ((Solidity.Core.Prog.trun σ P = .error .revert ∨
        (Prog.asserts P = true ∧ Solidity.Core.Prog.trun σ P = .error .panic)) ∧
      run (compileProg b P) m = .revert) ∨
    (Prog.pays P = true ∧ run (compileProg b P) m = .revert ∧ ∃ o m',
      Solidity.Core.Prog.trun σ P = .ok o ∧
      Sim C (L + Prog.pushes P) b F' o.st.sem (Look.ofTEnv o.st.env) m') := by
  rcases prog_sim P hm hP hL with ⟨o, m', h1, h2, h3, -, h5⟩ | ⟨h1, h2⟩ | ⟨ha, h1, h2⟩ |
      ⟨hp, h1, o, m', h2, -, h5⟩
  · exact .inl ⟨o, m', h1, h2, h3, h5⟩
  · exact .inr (.inl ⟨.inl h1, h2⟩)
  · exact .inr (.inl ⟨.inr ⟨ha, h1⟩, h2⟩)
  · exact .inr (.inr ⟨hp, h1, o, m', h2, h5⟩)

/-- **Code that pays no one agrees exactly**: with no `transfer`, nothing can
be refused, and the machine reverts where the typed run does; with no
`assert` either, the typed run's revert is a plain one.

Example: `total += 1;` at `2^256 - 1` reverts in both. -/
theorem compile_exact {P : Solidity.Core.Prog C Γ Γ'} (hP : inFragP F P = some F')
    (hm : Sim C L b F σ.sem (Look.ofTEnv σ.env) m) (hL : L + Prog.pushes P ≤ Lmax)
    (hpay : Prog.pays P = false) :
    (∃ o m', Solidity.Core.Prog.trun σ P = .ok o ∧ run (compileProg b P) m = .ok m' 0 ∧
      m'.stack = m.stack ∧ Sim C (L + Prog.pushes P) b F' o.st.sem (Look.ofTEnv o.st.env) m') ∨
    ((Solidity.Core.Prog.trun σ P = .error .revert ∨
        (Prog.asserts P = true ∧ Solidity.Core.Prog.trun σ P = .error .panic)) ∧
      run (compileProg b P) m = .revert) := by
  rcases compile_correct hP hm hL with h | h | ⟨hp, _⟩
  · exact .inl h
  · exact .inr h
  · rw [hpay] at hp; cases hp

/-- **What the machine does, the typed run did**: the box reading of
`compile_correct`.  Where the compiled code succeeds, so does the typed run,
in a state the final machine represents.

Example: `to.transfer(5);` that the machine completes is one the typed run
completes, its ledger `5` less at `to` (`compile_net`). -/
theorem compile_box {P : Solidity.Core.Prog C Γ Γ'} {m' : Machine} (hP : inFragP F P = some F')
    (hm : Sim C L b F σ.sem (Look.ofTEnv σ.env) m) (hL : L + Prog.pushes P ≤ Lmax)
    (hrun : run (compileProg b P) m = .ok m' 0) :
    ∃ o, Solidity.Core.Prog.trun σ P = .ok o ∧
      Sim C (L + Prog.pushes P) b F' o.st.sem (Look.ofTEnv o.st.env) m' := by
  rcases compile_correct hP hm hL with ⟨o, m'', h1, h2, _, h4⟩ | ⟨_, h2⟩ | ⟨_, h2, _⟩
  · rw [hrun] at h2; cases h2; exact ⟨o, h1, h4⟩
  · rw [hrun] at h2; cases h2
  · rw [hrun] at h2; cases h2

/-- **The ledger is the money that moved.**  Where the compiled code
succeeds, the typed run's `net(a)` is what `a`'s account lost since the
transaction began, at every address but the contract's own, whose entry
stays at `0`.

Example: `to.transfer(5);` from an empty ledger, completed by the machine,
leaves `net(to) = -5` and `to`'s account `5` richer. -/
theorem compile_net {P : Solidity.Core.Prog C Γ Γ'} {m' : Machine} (hP : inFragP F P = some F')
    (hm : Sim C L b F σ.sem (Look.ofTEnv σ.env) m) (hL : L + Prog.pushes P ≤ Lmax)
    (hrun : run (compileProg b P) m = .ok m' 0) :
    ∃ o, Solidity.Core.Prog.trun σ P = .ok o ∧
      (∀ a : Nat, a < W → a ≠ m'.self → o.st.sem.getNet a = (m'.bal₀ a : Int) - m'.bal a) ∧
      o.st.sem.getNet m'.self = 0 := by
  obtain ⟨o, h1, h2⟩ := compile_box hP hm hL hrun
  exact ⟨o, h1, h2.net, h2.netSelf⟩

/-- A word, as the `uint` the typed state holds. -/
def uintT (n : Nat) (h : n < W) : PrimTy.uint.Denote :=
  (⟨n, by simp only [PrimTy.inRange, decide_eq_true_eq]; unfold W at h; omega⟩ :
    {n : Int // PrimTy.uint.inRange n = true})

/-- A fresh contract, typed: its storage at deployment, no memory, no
locals, its funds `balance` and its address `self` (`Evm.State.fresh`). -/
def freshT (C : Contract) (balance : Nat) (hb : balance < W) (self : Nat) (hs : self < W) :
    TState C [] :=
  { storage := Solidity.Core.Storage.init C, H := [], heap := Solidity.Core.Heap.empty, env := (),
    selfBalance := uintT balance hb, tx := { selfAddress := uintT self hs } }

theorem freshT_sem (C : Contract) (balance : Nat) (hb : balance < W) (self : Nat)
    (hs : self < W) : (freshT C balance hb self hs).sem = State.fresh C balance self := by
  simp only [Solidity.Core.TState.sem, freshT, Solidity.Core.Storage.init_erase, State.fresh]
  rfl

/-- A fresh machine represents a fresh contract with no locals
(`Evm.Sim.init`). -/
theorem Sim.init (C : Contract) (balance : Nat) (hb : balance < W) (bal : Nat → Nat) (self : Nat)
    (hs : self < W) :
    Sim C 1 0 (Frag.init []) (freshT C balance hb self hs).sem
      (Look.ofTEnv (freshT C balance hb self hs).env) (Machine.init bal self) := by
  have h := Evm.Sim.init C balance bal self hs
  rw [← freshT_sem C balance hb self hs] at h
  exact ⟨h.store, (fun i => nomatch i), (fun i => nomatch i), h.net, h.netSelf, h.bound,
    (fun i => nomatch i), h.env⟩

/-- **The EVM agrees with the typed run's storage.**  From a fresh contract,
a program of the fragment either reverts in both, or runs in both, and then
every `uint` the typed run reads live at a reference whose indices are in
bounds, the machine holds at its slot; or the world refuses a payment, and
the machine alone reverts.

Example: `alice.age = 10;` leaves `10` at slot `13` of `StandardExample`
(`Evm/CoreInterpreter.lean`'s `setAge_interpreter` derives it from this
theorem). -/
theorem compile_storage {P : Solidity.Core.Prog C [] Γ'} (hP : inFragP (Frag.init []) P = some F')
    (hL : Prog.pushes P < Lmax) (balance : Nat) (hb : balance < W) (bal : Nat → Nat)
    (self : Nat) (hs : self < W) :
    (∃ o m', Solidity.Core.Prog.trun (freshT C balance hb self hs) P = .ok o ∧
        run (compileProg 0 P) (Machine.init bal self) = .ok m' 0 ∧
      ∀ (r : SRef C (.prim .uint)) s (v : PrimTy.uint.Denote),
        PathSlot C false r.root r.path.erase (.prim .uint) s →
        o.st.storage.findLive r = some (.prim v) → m'.store s = v.1.toNat) ∨
    ((Solidity.Core.Prog.trun (freshT C balance hb self hs) P = .error .revert ∨
        (Prog.asserts P = true ∧
          Solidity.Core.Prog.trun (freshT C balance hb self hs) P = .error .panic)) ∧
      run (compileProg 0 P) (Machine.init bal self) = .revert) ∨
    (Prog.pays P = true ∧ run (compileProg 0 P) (Machine.init bal self) = .revert ∧
      ∃ o, Solidity.Core.Prog.trun (freshT C balance hb self hs) P = .ok o) := by
  rcases compile_correct hP (Sim.init C balance hb bal self hs) (by omega) with
    ⟨o, m', h1, h2, _, hm⟩ | h | ⟨hp, h1, o, _, h2, _⟩
  · refine .inl ⟨o, m', h1, h2, fun r s v hp hf => ?_⟩
    have hl := Solidity.Core.Storage.findLive_erase (σ := o.st.sem) rfl r
    rw [hf] at hl
    rcases find_repr hm.store hp with ⟨sv, hsv, hr⟩ | ⟨_, hsv⟩
    · rw [hl] at hsv; cases hsv
      rw [Solidity.Core.SVal.erase_prim] at hr
      change ReprAt _ _ _ _ (.prim (.int v.1)) at hr
      cases hr with
      | uint _ _ h => exact h
    · rw [hl] at hsv; cases hsv
  · exact .inr (.inl h)
  · exact .inr (.inr ⟨hp, h1, o, h2⟩)

end Headline

end Core
end Solidity.Evm
