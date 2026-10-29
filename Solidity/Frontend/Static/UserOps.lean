import Solidity.Source.UserOps
import Solidity.Frontend.Static.InferComplete

/-!
# Checking user-defined value type operations (G13)

`udvtRes Γ u e` returns the types of `e` under `UdvtTyped`
(`Solidity/Source/UserOps.lean`), each with its derivation, so it is sound
by construction; `udvt_complete` proves every `UdvtTyped` type is among
them.  Operand types come from `infer`, whose completeness
(`typed_complete`) carries over.
-/

namespace Solidity.Frontend.Static

open Solidity.Source

section
variable (Γ : Ctx) (u : Syn .unit)

/-- The bound function's result for an operator on `T` with `n` operands. -/
def boundRes (T : DeclName) (op : UserOp) (n : Nat) (k : (d : Decl) → (ps : List STy) → (τ : STy) →
    opBindings Γ.env u T op n = [d] → d.fnSig Γ.env = Option.some (ps, [τ]) → UdvtTyped Γ u e τ) :
    List {τ // UdvtTyped Γ u e τ} :=
  match hb : opBindings Γ.env u T op n with
  | [d] =>
    match hs : d.fnSig Γ.env with
    | Option.some (ps, [τ]) => [⟨τ, k d ps τ hb hs⟩]
    | _ => []
  | _ => []

/-- `a op b`. -/
def binUdvt (e : Syn .expr) : List {τ // UdvtTyped Γ u e τ} :=
  match hk : e.userBinOp? with
  | Option.some (op, a, b) =>
    (tysOf Γ (infer Γ a)).flatMap fun pa =>
      match pa with
      | ⟨.udvt T, da⟩ =>
        (tysOf Γ (infer Γ b)).flatMap fun pb =>
          match pb with
          | ⟨.udvt T', db⟩ =>
            if hT : T' = T then
              boundRes Γ u T op 2 fun _ _ _ hb hs => .binOp hk ⟨da⟩ (by subst hT; exact ⟨db⟩) hb hs
            else []
          | _ => []
      | _ => []
  | Option.none => []

/-- `-x`, `~x`. -/
def unUdvt (e : Syn .expr) : List {τ // UdvtTyped Γ u e τ} :=
  match hk : e.userUnOp? with
  | Option.some (op, x) =>
    if hu : op.unaryOK = true then
      (tysOf Γ (infer Γ x)).flatMap fun px =>
        match px with
        | ⟨.udvt T, dx⟩ => boundRes Γ u T op 1 fun _ _ _ hb hs => .unOp hk hu ⟨dx⟩ hb hs
        | _ => []
    else []
  | Option.none => []

/-- `T.wrap(x)`. -/
def wrapRes (T : String) (x : Syn .expr) :
    List {τ // UdvtTyped Γ u (.call (.member (.ident T) "wrap") (.positional (.cons x .nil))) τ} :=
  match hr : Γ.resolve T with
  | Option.some (.decls [d]) =>
    match hl : d.underlying? with
    | Option.some el =>
      (tysOf Γ (infer Γ x)).flatMap fun p =>
        if hi : p.1.implicit Γ.isBase (el.ty .memory) = true then
          [⟨.udvt ⟨d.scope, d.name⟩, .wrap hr hl ⟨p.2⟩ hi⟩]
        else []
    | Option.none => []
  | _ => []

/-- `T.unwrap(x)`. -/
def unwrapRes (T : String) (x : Syn .expr) :
    List {τ // UdvtTyped Γ u (.call (.member (.ident T) "unwrap") (.positional (.cons x .nil))) τ} :=
  match hr : Γ.resolve T with
  | Option.some (.decls [d]) =>
    match hl : d.underlying? with
    | Option.some el =>
      (tysOf Γ (infer Γ x)).flatMap fun p =>
        match p with
        | ⟨.udvt T', dx⟩ =>
          if hT : T' = ⟨d.scope, d.name⟩ then [⟨el.ty .memory, .unwrap hr hl (by subst hT; exact ⟨dx⟩)⟩]
          else []
        | _ => []
    | Option.none => []
  | _ => []

/-- Conversions, by the call's shape. -/
def convUdvt : (e : Syn .expr) → List {τ // UdvtTyped Γ u e τ}
  | .call (.member (.ident T) m) (.positional (.cons x .nil)) =>
    match m with
    | "wrap" => wrapRes Γ u T x
    | "unwrap" => unwrapRes Γ u T x
    | _ => []
  | _ => []

/-- **The checker** of user-defined value type operations. -/
def udvtRes (e : Syn .expr) : List {τ // UdvtTyped Γ u e τ} :=
  binUdvt Γ u e ++ unUdvt Γ u e ++ convUdvt Γ u e

/-- The types it finds. -/
def udvtTys (e : Syn .expr) : List STy := (udvtRes Γ u e).map Subtype.val

end

/-- **Sound**: every type found is a `UdvtTyped` type. -/
theorem udvt_sound {Γ : Ctx} {u : Syn .unit} {e : Syn .expr} {τ : STy} (h : τ ∈ udvtTys Γ u e) :
    UdvtTyped Γ u e τ := by
  obtain ⟨⟨τ', hτ⟩, _, e'⟩ := List.mem_map.mp h
  subst e'
  exact hτ

theorem boundRes_mem {Γ : Ctx} {u : Syn .unit} {e : Syn .expr} {T : DeclName} {op : UserOp} {n : Nat}
    {k : (d : Decl) → (ps : List STy) → (τ : STy) → opBindings Γ.env u T op n = [d] →
      d.fnSig Γ.env = Option.some (ps, [τ]) → UdvtTyped Γ u e τ}
    {d : Decl} {ps : List STy} {τ : STy} (hb : opBindings Γ.env u T op n = [d])
    (hs : d.fnSig Γ.env = Option.some (ps, [τ])) : τ ∈ (boundRes Γ u T op n k).map Subtype.val := by
  unfold boundRes
  split
  · rename_i d' hb'
    rw [hb] at hb'; cases hb'
    split
    · rename_i ps' τ' hs'
      rw [hs] at hs'; cases hs'
      exact List.mem_singleton.mpr rfl
    · rename_i hn; exact absurd hs (hn ps τ)
  · rename_i hn; exact absurd hb (hn d)

/-- **Complete**: every `UdvtTyped` type is found. -/
theorem udvt_complete {Γ : Ctx} {u : Syn .unit} {e : Syn .expr} {τ : STy} (h : UdvtTyped Γ u e τ) :
    τ ∈ udvtTys Γ u e := by
  unfold udvtTys udvtRes
  rw [List.map_append, List.map_append]
  cases h with
  | binOp hk ha hb hbind hs =>
    obtain ⟨da⟩ := ha
    obtain ⟨db⟩ := hb
    obtain ⟨da', ha'⟩ := exists_expr (typed_complete da)
    obtain ⟨db', hb'⟩ := exists_expr (typed_complete db)
    refine List.mem_append_left _ (List.mem_append_left _ ?_)
    unfold binUdvt
    split
    · rename_i op' a' b' hk'
      rw [hk] at hk'; cases hk'
      rw [List.map_flatMap]
      refine List.mem_flatMap.mpr ⟨⟨_, da'⟩, mem_tysOf' ha', ?_⟩
      dsimp only
      rw [List.map_flatMap]
      refine List.mem_flatMap.mpr ⟨⟨_, db'⟩, mem_tysOf' hb', ?_⟩
      dsimp only
      rw [dif_pos rfl]
      exact boundRes_mem hbind hs
    · rename_i hn; rw [hk] at hn; cases hn
  | unOp hk hu hx hbind hs =>
    obtain ⟨dx⟩ := hx
    obtain ⟨dx', hx'⟩ := exists_expr (typed_complete dx)
    refine List.mem_append_left _ (List.mem_append_right _ ?_)
    unfold unUdvt
    split
    · rename_i op' x' hk'
      rw [hk] at hk'; cases hk'
      rw [dif_pos hu, List.map_flatMap]
      refine List.mem_flatMap.mpr ⟨⟨_, dx'⟩, mem_tysOf' hx', ?_⟩
      exact boundRes_mem hbind hs
    · rename_i hn; rw [hk] at hn; cases hn
  | wrap hr hl hx hi =>
    obtain ⟨dx⟩ := hx
    obtain ⟨dx', hx'⟩ := exists_expr (typed_complete dx)
    refine List.mem_append_right _ ?_
    show _ ∈ (wrapRes Γ u _ _).map Subtype.val
    unfold wrapRes
    split
    · rename_i d' hr'
      rw [hr] at hr'; cases hr'
      split
      · rename_i el' hl'
        rw [hl] at hl'; cases hl'
        rw [List.map_flatMap]
        refine List.mem_flatMap.mpr ⟨⟨_, dx'⟩, mem_tysOf' hx', ?_⟩
        dsimp only
        rw [dif_pos hi]
        exact List.mem_singleton.mpr rfl
      · rename_i hl'; rw [hl] at hl'; cases hl'
    · rename_i hn; exact absurd hr (hn _)
  | unwrap hr hl hx =>
    obtain ⟨dx⟩ := hx
    obtain ⟨dx', hx'⟩ := exists_expr (typed_complete dx)
    refine List.mem_append_right _ ?_
    show _ ∈ (unwrapRes Γ u _ _).map Subtype.val
    unfold unwrapRes
    split
    · rename_i d' hr'
      rw [hr] at hr'; cases hr'
      split
      · rename_i el' hl'
        rw [hl] at hl'; cases hl'
        rw [List.map_flatMap]
        refine List.mem_flatMap.mpr ⟨⟨_, dx'⟩, mem_tysOf' hx', ?_⟩
        dsimp only
        rw [dif_pos rfl]
        exact List.mem_singleton.mpr rfl
      · rename_i hl'; rw [hl] at hl'; cases hl'
    · rename_i hn; exact absurd hr (hn _)

/-- **The checker decides `UdvtTyped`.** -/
theorem udvt_iff {Γ : Ctx} {u : Syn .unit} {e : Syn .expr} {τ : STy} :
    τ ∈ udvtTys Γ u e ↔ UdvtTyped Γ u e τ := ⟨udvt_sound, udvt_complete⟩

/-- The operator-binding check. -/
def usingOpsB (E : Env) (u : Syn .unit) : Bool := (u.opUsesAt true).all (opUseOK E)

theorem usingOpsB_iff {E : Env} {u : Syn .unit} : usingOpsB E u = true ↔ UsingOpsOK E u := by
  simp only [usingOpsB, List.all_eq_true, UsingOpsOK]

end Solidity.Frontend.Static
