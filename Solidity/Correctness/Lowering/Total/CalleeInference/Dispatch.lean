import Solidity.Correctness.Lowering.Total.CalleeInference.Args

/-!
# The dispatch order of `f(args)` in `Typed.inferN`

`Typed.inferN (n + 1) Γ (f(args))` first tries `tryConst`, which never fires on a
call (`tryConst_call`); then infers the arguments with `TypedArgs.inferN n`, and a
failure there fails the call (`inferN_call_args_none`). From the argument types it
tries, in order, a conversion (`convTarget`, one argument), a struct construction
(`structOf`), a builtin (`resolve` to `.builtin`), and only then `inferCall`
(`inferN_call_dispatch`, under the three local facts `NotOther`).

`NotOther` holds whenever the callee name denotes a declaration set containing a
function-kind declaration (`notOther_of_function`), in particular whenever some
callable function is visible under it (`notOther_of_functions`), and under a
local of the name (`notOther_local`). Where no function-kind declaration is
denoted, the competing branches stay possible and `NotOther` is a local fact
the caller must supply.
-/
namespace Solidity.Correctness.Lowering.Total.CalleeInference

open Source (STy Syn Ctx Typed TypedArgs Decl Denot)

variable {Γ : Ctx} {n : Nat} {f : String} {args : Syn (.list .expr)}

/-- The competing branches before `inferCall` do not apply to callee `f`. -/
structure NotOther (Γ : Ctx) (f : String) : Prop where
  conv : Γ.convTarget f = none
  struct : Γ.structOf f = none
  builtin : ∀ b, Γ.resolve f ≠ some (.builtin b)

/-- A call is never a constant. -/
theorem tryConst_call {c : Syn .expr} {a : Syn .callArgs} :
    Source.tryConst Γ (.call c a) = none := rfl

/-- Argument failure fails the call, before any branch is tried. -/
theorem inferN_call_args_none (h : TypedArgs.inferN n Γ args = none) :
    Typed.inferN (n + 1) Γ (.call (.ident f) (.positional args)) = none := by
  rw [Typed.inferN]
  show (TypedArgs.inferN n Γ args >>= _) = _
  rw [h]; rfl

/-- The conversion match of the call branch (Lean generates no equations for
it) takes its fallback alternative when no conversion target exists. -/
theorem convMatch_none {motive x args σs da discr h_1 h_2} (hx : x = none) :
    Typed.inferN.match_39 Γ motive x args σs da discr h_1 h_2 = h_2 x args σs da discr rfl := by
  subst hx; rfl

/-- **Dispatch**: past `tryConst` and successful argument inference, with the
conversion, struct and builtin branches excluded, the call branch is `inferCall`
on the inferred argument typing. -/
theorem inferN_call_dispatch {σs : List STy} {da : TypedArgs Γ args σs}
    (hargs : TypedArgs.inferN n Γ args = some ⟨σs, da⟩) (ho : NotOther Γ f) :
    Typed.inferN (n + 1) Γ (.call (.ident f) (.positional args)) =
      Source.inferCall Γ f args σs da := by
  rw [Typed.inferN]
  show (TypedArgs.inferN n Γ args >>= _) = _
  rw [hargs]
  show Typed.inferN.match_39 _ _ _ _ _ _ _ _ _ = _
  rw [convMatch_none ho.conv]
  split
  · rename_i hs; rw [ho.struct] at hs; cases hs
  · split
    · rename_i b hr; exact absurd hr (ho.builtin b)
    · rfl

/-- A function-kind declaration in the callee's denotation excludes the
conversion, struct and builtin branches. -/
theorem notOther_of_function {ds : List Decl} {d : Decl}
    (hr : Γ.resolve f = some (.decls ds)) (hd : d ∈ ds) (hk : d.kind = .function) :
    NotOther Γ f := by
  refine ⟨?_, ?_, fun b h => by rw [hr] at h; cases h⟩
  · simp only [Ctx.convTarget, hr]
    split
    · rename_i d' h; cases h; simp at hd; subst hd; simp [hk]
    · rfl
  · simp only [Ctx.structOf, hr]
    split
    · rename_i d' h; cases h; simp at hd; subst hd; simp [hk]
    · rfl

/-- A callable function under the name excludes the competing branches. -/
theorem notOther_of_functions {d : Decl} (hd : d ∈ Γ.functions f) : NotOther Γ f := by
  unfold Ctx.functions at hd
  split at hd
  · rename_i ds hr
    obtain ⟨hm, hk⟩ := List.mem_filter.mp hd
    exact notOther_of_function hr hm (by simp at hk; exact hk.1)
  · cases hd

/-- A local of the name excludes the competing branches. -/
theorem notOther_local {i : Nat} (hloc : (Γ.locals.map Prod.fst).idxOf? f = some i) :
    NotOther Γ f := by
  have hr : Γ.resolve f = some (.loc i) := by
    simp [Ctx.resolve, Source.Env.resolve, hloc]
  exact ⟨by simp [Ctx.convTarget, hr], by simp [Ctx.structOf, hr],
    fun b h => by rw [hr] at h; cases h⟩

end Solidity.Correctness.Lowering.Total.CalleeInference
