import Solidity.Frontend.Static.Infer

namespace Solidity.Frontend.Static

open Solidity.Source

theorem mem_tysOf {Γ : Ctx} {e : Syn .expr} {L : List (Res Γ .expr e)} {τ : STy} {d : Typed Γ e τ}
    (h : Res.expr d ∈ L) : τ ∈ (tysOf Γ L).map Sigma.fst :=
  List.mem_map.mpr ⟨⟨τ, d⟩, List.mem_filterMap.mpr ⟨_, h, rfl⟩, rfl⟩

theorem mem_lvsOf {Γ : Ctx} {e : Syn .expr} {L : List (Res Γ .expr e)} {τ : STy} {d : LVal Γ e τ}
    (h : Res.lval d ∈ L) : τ ∈ (lvsOf Γ L).map Sigma.fst :=
  List.mem_map.mpr ⟨⟨τ, d⟩, List.mem_filterMap.mpr ⟨_, h, rfl⟩, rfl⟩

theorem exists_expr {Γ : Ctx} {e : Syn .expr} {L : List (Res Γ .expr e)} {τ : STy}
    (h : τ ∈ (tysOf Γ L).map Sigma.fst) : ∃ d : Typed Γ e τ, Res.expr d ∈ L := by
  obtain ⟨⟨τ', d⟩, hm, e'⟩ := List.mem_map.mp h
  simp only at e'
  subst e'
  obtain ⟨r, hr, hs⟩ := List.mem_filterMap.mp hm
  cases r with
  | expr d' => cases hs; exact ⟨_, hr⟩
  | _ => cases hs

theorem exists_lval {Γ : Ctx} {e : Syn .expr} {L : List (Res Γ .expr e)} {τ : STy}
    (h : τ ∈ (lvsOf Γ L).map Sigma.fst) : ∃ d : LVal Γ e τ, Res.lval d ∈ L := by
  obtain ⟨⟨τ', d⟩, hm, e'⟩ := List.mem_map.mp h
  simp only at e'
  subst e'
  obtain ⟨r, hr, hs⟩ := List.mem_filterMap.mp hm
  cases r with
  | lval d' => cases hs; exact ⟨_, hr⟩
  | _ => cases hs

theorem exists_args {Γ : Ctx} {es : Syn (.list .expr)} {L : List (Res Γ (.list .expr) es)} {τs : List STy}
    (h : τs ∈ (argsOf Γ L).map Sigma.fst) : ∃ d : TypedArgs Γ es τs, ⟨τs, d⟩ ∈ argsOf Γ L := by
  obtain ⟨⟨τs', d⟩, hm, e'⟩ := List.mem_map.mp h
  simp only at e'
  subst e'
  exact ⟨d, hm⟩

theorem exists_slots {Γ : Ctx} {s : Syn (.list (.opt .expr))} {L : List (Res Γ (.list (.opt .expr)) s)}
    {τs : List STy} (h : τs ∈ (slotsOf Γ L).map Sigma.fst) :
    ∃ d : TypedSlots Γ s τs, ⟨τs, d⟩ ∈ slotsOf Γ L := by
  obtain ⟨⟨τs', d⟩, hm, e'⟩ := List.mem_map.mp h
  simp only at e'
  subst e'
  exact ⟨d, hm⟩

theorem mem_tysOf' {Γ : Ctx} {e : Syn .expr} {L : List (Res Γ .expr e)} {τ : STy} {d : Typed Γ e τ}
    (h : Res.expr d ∈ L) : ⟨τ, d⟩ ∈ tysOf Γ L := List.mem_filterMap.mpr ⟨_, h, rfl⟩

theorem mem_lvsOf' {Γ : Ctx} {e : Syn .expr} {L : List (Res Γ .expr e)} {τ : STy} {d : LVal Γ e τ}
    (h : Res.lval d ∈ L) : ⟨τ, d⟩ ∈ lvsOf Γ L := List.mem_filterMap.mpr ⟨_, h, rfl⟩

/-- The constant rule is offered at every expression. -/
theorem constRes_sub {Γ : Ctx} : ∀ (e : Syn .expr) (r : Res Γ .expr e), r ∈ constRes Γ e → r ∈ infer Γ e := by
  intro e r h
  cases e <;>
    first
    | exact h
    | exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
        (List.mem_append_left _ h)))
    | exact List.mem_append_left _ (List.mem_append_left _ h)
    | exact List.mem_append_left _ h

theorem const_mem {Γ : Ctx} {e : Syn .expr} {q : Q} (hq : e.const = Option.some q)
    (ha : e.isAddressLit = false) (hx : e.hexLen? = Option.none) :
    Res.expr (Typed.const (Γ := Γ) hq ha hx) ∈ constRes Γ e := by
  unfold constRes
  split
  · rename_i q' hq' ha' hx'
    have e' : q' = q := by rw [hq] at hq'; exact (Option.some.inj hq').symm
    subst e'
    exact List.mem_singleton.mpr rfl
  · rename_i hn
    exact absurd hx (hn q hq ha)

theorem loc_mem {Γ : Ctx} {x : String} {i : Nat} {τ : STy} (hr : Γ.resolve x = Option.some (.loc i))
    (ht : Γ.tys[i]? = Option.some τ) :
    Res.expr (Typed.loc hr ht) ∈ infer Γ (.ident x) ∧ Res.lval (LVal.loc hr ht) ∈ infer Γ (.ident x) := by
  refine ⟨List.mem_append_right _ (List.mem_append_left _ ?_),
    List.mem_append_right _ (List.mem_append_left _ ?_)⟩ <;>
  · split
    · rename_i i' hr'
      rw [hr] at hr'
      cases hr'
      split
      · rename_i τ' ht'
        rw [ht] at ht'
        cases ht'
        simp only [List.mem_cons, List.not_mem_nil, or_false, true_or, or_true]
      · rename_i ht'
        rw [ht] at ht'
        cases ht'
    · rename_i d hr'
      rw [hr] at hr'
      cases hr'
    · rename_i hn _
      exact absurd hr (hn i)

theorem state_mem {Γ : Ctx} {x : String} {d : Decl} {τ : STy} (hr : Γ.resolve x = Option.some (.decls [d]))
    (hv : d.varTy Γ.env = Option.some τ) :
    Res.expr (Typed.state hr hv) ∈ infer Γ (.ident x) ∧
      ∀ hm : d.mutable = true, Res.lval (LVal.state hr hv hm) ∈ infer Γ (.ident x) := by
  have key : ∀ r, r ∈ (.expr (.state hr hv) :: (if hm : d.mutable = true then [.lval (.state hr hv hm)] else [])) →
      r ∈ infer Γ (.ident x) := by
    intro r hm
    refine List.mem_append_right _ (List.mem_append_left _ ?_)
    split
    · rename_i i' hr'
      rw [hr] at hr'
      cases hr'
    · rename_i d' hr'
      rw [hr] at hr'
      cases hr'
      split
      · rename_i τ' hv'
        rw [hv] at hv'
        cases hv'
        exact hm
      · rename_i hv'
        rw [hv] at hv'
        cases hv'
    · rename_i _ hn
      exact absurd hr (hn d)
  refine ⟨key _ List.mem_cons_self, fun hm => key _ (List.mem_cons_of_mem _ ?_)⟩
  simp only [hm, dite_true, List.mem_singleton]

theorem this_mem {Γ : Ctx} {c : String} (hr : Γ.resolve "this" = Option.some (.builtin .this))
    (hs : Γ.scope = Option.some c) : Res.expr (Typed.this hr hs) ∈ infer Γ (.ident "this") := by
  refine List.mem_append_right _ (List.mem_append_right _ ?_)
  simp only [thisFor]
  unfold thisRes
  split
  · rename_i c' hr' hs'
    rw [hs] at hs'
    cases hs'
    exact List.mem_singleton.mpr rfl
  · rename_i hn
    exact absurd hs (hn c hr)

theorem lit_sub {Γ : Ctx} {l : Lit} {r : Res Γ .expr (.lit l)} (h : r ∈ litRes Γ l) :
    r ∈ infer Γ (.lit l) := List.mem_append_right _ h

theorem litBytes_mem {Γ : Ctx} {n : NumLit} {len : Nat}
    (hx : (Syn.lit (.num n)).hexLen? = Option.some len) :
    Res.expr (Typed.litBytes (Γ := Γ) hx) ∈ infer Γ (.lit (.num n)) := by
  refine lit_sub (List.mem_append_left _ ?_)
  split
  · rename_i len' hx'
    rw [hx] at hx'; cases hx'
    exact List.mem_singleton.mpr rfl
  · rename_i hx'; rw [hx] at hx'; cases hx'

theorem litAddress_mem {Γ : Ctx} {ds : List (Fin 16)} (h : ds.length = 40) :
    Res.expr (Typed.litAddress (Γ := Γ) h) ∈ infer Γ (.lit (.num (.hex ds true))) := by
  refine lit_sub (List.mem_append_right _ ?_)
  simp only [h, dite_true, List.mem_singleton]

/-! ## Lists, slots and arguments -/

theorem nil_mem {Γ : Ctx} {c : Cat} : (Res.nilList : Res Γ (.list c) .nil) ∈ infer Γ (.nil : Syn (.list c)) :=
  List.mem_singleton.mpr rfl

theorem slot_mem {Γ : Ctx} {e : Syn .expr} {τ : STy} {d : Typed Γ e τ} (h : Res.expr d ∈ infer Γ e) :
    Res.slot d ∈ infer Γ (.some e) := List.mem_filterMap.mpr ⟨_, h, rfl⟩

theorem slotL_mem {Γ : Ctx} {e : Syn .expr} {τ : STy} {d : LVal Γ e τ} (h : Res.lval d ∈ infer Γ e) :
    Res.slotL d ∈ infer Γ (.some e) := List.mem_filterMap.mpr ⟨_, h, rfl⟩

theorem pos_mem {Γ : Ctx} {es : Syn (.list .expr)} {τs : List STy} {d : TypedArgs Γ es τs}
    (h : ⟨τs, d⟩ ∈ argsOf Γ (infer Γ es)) : Res.pos d ∈ infer Γ (.positional es) :=
  List.mem_map.mpr ⟨_, h, rfl⟩

theorem args1_mem {Γ : Ctx} {x : Syn .expr} {σ : STy} {d : Typed Γ x σ} (h : Res.expr d ∈ infer Γ x) :
    Res.pos (TypedArgs.cons d .nil) ∈ infer Γ (.positional (.cons x .nil)) := by
  apply pos_mem
  refine List.mem_filterMap.mpr ⟨Res.args (.cons d .nil), ?_, rfl⟩
  exact List.mem_flatMap.mpr ⟨_, h, List.mem_filterMap.mpr ⟨_, nil_mem, rfl⟩⟩

/-! ## Unary, binary -/

theorem prefix_sub {Γ : Ctx} {op : PrefixOp} {x : Syn .expr} {r0 : Res Γ .expr x}
    {r : Res Γ .expr (.unaryPrefix op x)} (h0 : r0 ∈ infer Γ x) (h : r ∈ prefixOne Γ op r0) :
    r ∈ infer Γ (.unaryPrefix op x) := List.mem_append_right _ (List.mem_flatMap.mpr ⟨_, h0, h⟩)

theorem suffix_sub {Γ : Ctx} {op : SuffixOp} {x : Syn .expr} {r0 : Res Γ .expr x}
    {r : Res Γ .expr (.unarySuffix op x)} (h0 : r0 ∈ infer Γ x) (h : r ∈ suffixOne Γ op r0) :
    r ∈ infer Γ (.unarySuffix op x) := List.mem_append_right _ (List.mem_flatMap.mpr ⟨_, h0, h⟩)

theorem binRes_sub {Γ : Ctx} {e a b : Syn .expr} {k : BinKind} (hk : e.binOp? = Option.some (k, a, b))
    {r : Res Γ .expr e} (h : r ∈ binRes Γ e a b k hk (infer Γ a) (infer Γ b)) : r ∈ infer Γ e := by
  revert h
  cases e <;> cases hk <;> intro h <;> exact List.mem_append_right _ h

theorem bin_mem {Γ : Ctx} {e a b : Syn .expr} {k : BinKind} (hk : e.binOp? = Option.some (k, a, b))
    {τa τb : STy} {da : Typed Γ a τa} {db : Typed Γ b τb} (ha : Res.expr da ∈ infer Γ a)
    (hb : Res.expr db ∈ infer Γ b) {r : Res Γ .expr e} (h : r ∈ binPair Γ e a b k hk τa da τb db) :
    r ∈ infer Γ e :=
  binRes_sub hk (List.mem_append_left _ (List.mem_flatMap.mpr ⟨⟨τa, da⟩, mem_tysOf' ha,
    List.mem_flatMap.mpr ⟨⟨τb, db⟩, mem_tysOf' hb, h⟩⟩))

theorem compare_mem {Γ : Ctx} {e a b : Syn .expr} {k : BinKind} (hk : e.binOp? = Option.some (k, a, b))
    {r : Res Γ .expr e} (h : r ∈ compareConstRes Γ e a b k hk) : r ∈ infer Γ e :=
  binRes_sub hk (List.mem_append_right _ h)

section Rules
variable {Γ : Ctx} {e a b : Syn .expr} {τa τb τ : STy} {da : Typed Γ a τa} {db : Typed Γ b τb}

theorem arith_pair (hk : e.binOp? = Option.some (.arith, a, b)) (hc : STy.common? Γ.isBase τa τb = Option.some τ)
    (hn : τ.isNumeric = true) (hz : (e.isDivMod && τb.isZeroConst) = false) :
    Res.expr (Typed.arith hk da db hc hn hz) ∈ binPair Γ e a b .arith hk τa da τb db := by
  simp only [binPair]
  split
  · rename_i τ' hc'
    rw [hc] at hc'; cases hc'
    rw [dif_pos hn, dif_pos hz]; exact List.mem_singleton.mpr rfl
  · rename_i hc'; rw [hc] at hc'; cases hc'

theorem bit_pair (hk : e.binOp? = Option.some (.bit, a, b)) (hc : STy.common? Γ.isBase τa τb = Option.some τ)
    (hn : τ.isBits = true) :
    Res.expr (Typed.bit hk da db hc hn) ∈ binPair Γ e a b .bit hk τa da τb db := by
  simp only [binPair]
  split
  · rename_i τ' hc'
    rw [hc] at hc'; cases hc'
    rw [dif_pos hn]; exact List.mem_singleton.mpr rfl
  · rename_i hc'; rw [hc] at hc'; cases hc'

theorem order_pair (hk : e.binOp? = Option.some (.order, a, b)) (hc : STy.common? Γ.isBase τa τb = Option.some τ)
    (hn : τ.isOrdered = true) :
    Res.expr (Typed.order hk da db hc hn) ∈ binPair Γ e a b .order hk τa da τb db := by
  simp only [binPair]
  split
  · rename_i τ' hc'
    rw [hc] at hc'; cases hc'
    rw [dif_pos hn]; exact List.mem_singleton.mpr rfl
  · rename_i hc'; rw [hc] at hc'; cases hc'

theorem eq_pair (hk : e.binOp? = Option.some (.eq, a, b)) (hc : STy.common? Γ.isBase τa τb = Option.some τ)
    (hn : τ.hasEq = true) :
    Res.expr (Typed.eq hk da db hc hn) ∈ binPair Γ e a b .eq hk τa da τb db := by
  simp only [binPair]
  split
  · rename_i τ' hc'
    rw [hc] at hc'; cases hc'
    rw [dif_pos hn]; exact List.mem_singleton.mpr rfl
  · rename_i hc'; rw [hc] at hc'; cases hc'

theorem shift_pair (hk : e.binOp? = Option.some (.shift, a, b)) (h1 : τa.shiftTy.isBits = true)
    (h2 : τb.isAmount = true) (h3 : (a.const.isSome && b.const.isSome) = false) :
    Res.expr (Typed.shift hk da db h1 h2 h3) ∈ binPair Γ e a b .shift hk τa da τb db := by
  simp only [binPair]
  rw [dif_pos h1, dif_pos h2, dif_pos h3]; exact List.mem_singleton.mpr rfl

theorem exp_pair (hk : e.binOp? = Option.some (.exp, a, b)) (h1 : τa.shiftTy.isInt = true)
    (h2 : τb.isAmount = true) (h3 : (a.const.isSome && b.const.isSome) = false) :
    Res.expr (Typed.exp hk da db h1 h2 h3) ∈ binPair Γ e a b .exp hk τa da τb db := by
  simp only [binPair]
  rw [dif_pos h1, dif_pos h2, dif_pos h3]; exact List.mem_singleton.mpr rfl

theorem logic_pair (hk : e.binOp? = Option.some (.logic, a, b)) {da : Typed Γ a .bool} {db : Typed Γ b .bool} :
    Res.expr (Typed.logic hk da db) ∈ binPair Γ e a b .logic hk .bool da .bool db :=
  List.mem_singleton.mpr rfl

theorem compare_res {k : BinKind} (hk : e.binOp? = Option.some (k, a, b)) (hkk : k = .order ∨ k = .eq)
    {qa qb : Q} (ha : a.const = Option.some qa) (hb : b.const = Option.some qb) :
    Res.expr (Typed.compareConst hk hkk ha hb) ∈ compareConstRes Γ e a b k hk := by
  rcases hkk with e' | e' <;> subst e' <;> simp only [compareConstRes] <;> split
  all_goals first
    | (rename_i qa' qb' ha' hb'
       rw [ha] at ha'; rw [hb] at hb'; cases ha'; cases hb'
       exact List.mem_singleton.mpr rfl)
    | (rename_i hn; exact absurd hb (hn qa qb ha))

theorem neg_res {t : IntTy} (d : Typed Γ a (.int t)) (hs : t.signed = true) :
    Res.expr (Typed.neg d hs) ∈ prefixOne Γ .neg (.expr d) := by
  simp only [prefixOne]; rw [dif_pos hs]; exact List.mem_singleton.mpr rfl

theorem negFixed_res {f : FixTy} (d : Typed Γ a (.fixed f)) :
    Res.expr (Typed.negFixed d) ∈ prefixOne Γ .neg (.expr d) := by
  simp only [prefixOne]; exact List.mem_singleton.mpr rfl

theorem not_res (d : Typed Γ a .bool) : Res.expr (Typed.not d) ∈ prefixOne Γ .not (.expr d) := by
  simp only [prefixOne]; exact List.mem_singleton.mpr rfl

theorem bitNot_res (d : Typed Γ a τ) (h : τ.isBits = true) :
    Res.expr (Typed.bitNot d h) ∈ prefixOne Γ .bitNot (.expr d) := by
  simp only [prefixOne]; rw [dif_pos h]; exact List.mem_singleton.mpr rfl

theorem incDec_res {op : PrefixOp} (hop : op = .inc ∨ op = .dec) (d : LVal Γ a τ) (h : τ.isNumeric = true) :
    Res.expr (Typed.incDec hop d h) ∈ prefixOne Γ op (.lval d) := by
  rcases hop with e' | e' <;> subst e' <;> simp only [prefixOne] <;> rw [dif_pos h] <;>
    exact List.mem_singleton.mpr rfl

theorem delete_res (d : LVal Γ a τ) (h : isMappingTy τ = false)
    (hp : Γ.deleteRefused τ a = false) :
    Res.expr (Typed.delete d h hp) ∈ prefixOne Γ .delete (.lval d) := by
  simp only [prefixOne]; rw [dif_pos h, dif_pos hp]; exact List.mem_singleton.mpr rfl

theorem suffix_res {op : SuffixOp} (d : LVal Γ a τ) (h : τ.isNumeric = true) :
    Res.expr (Typed.incDecSuffix (op := op) d h) ∈ suffixOne Γ op (.lval d) := by
  simp only [suffixOne]; rw [dif_pos h]; exact List.mem_singleton.mpr rfl

end Rules

/-! ## Conditionals, assignments, indexing, members, calls -/

section Rules2
variable {Γ : Ctx} {c a b i : Syn .expr} {τa τb τ σ : STy}

theorem cond_mem {dc : Typed Γ c .bool} {da : Typed Γ a τa} {db : Typed Γ b τb}
    (hc : Res.expr dc ∈ infer Γ c) (ha : Res.expr da ∈ infer Γ a) (hb : Res.expr db ∈ infer Γ b)
    (h : STy.common? Γ.isBase τa.mobile τb.mobile = Option.some τ) :
    Res.expr (Typed.cond dc da db h) ∈ infer Γ (.cond c a b) := by
  refine List.mem_append_right _ (List.mem_flatMap.mpr ⟨⟨.bool, dc⟩, mem_tysOf' hc, ?_⟩)
  refine List.mem_flatMap.mpr ⟨⟨τa, da⟩, mem_tysOf' ha, List.mem_flatMap.mpr ⟨⟨τb, db⟩, mem_tysOf' hb, ?_⟩⟩
  split
  · rename_i τ' h'
    rw [h] at h'; cases h'
    exact List.mem_singleton.mpr rfl
  · rename_i h'; rw [h] at h'; cases h'

theorem assign_mem {dl : LVal Γ a τ} {db : Typed Γ b σ} (hl : Res.lval dl ∈ infer Γ a)
    (hb : Res.expr db ∈ infer Γ b) (h1 : σ.implicit Γ.isBase τ = true)
    (h2 : Γ.assignRefused τ a = false) :
    Res.expr (Typed.assign dl db h1 h2) ∈ infer Γ (.assign .assign a b) := by
  refine List.mem_append_right _ (List.mem_flatMap.mpr ⟨⟨τ, dl⟩, mem_lvsOf' hl,
    List.mem_flatMap.mpr ⟨⟨σ, db⟩, mem_tysOf' hb, List.mem_append_left _ (List.mem_append_left _ ?_)⟩⟩)
  dsimp only
  rw [dif_pos h1, dif_pos h2]
  exact List.mem_singleton.mpr rfl

theorem assignCopy_mem {dl : LVal Γ a τ} {db : Typed Γ b σ} (hl : Res.lval dl ∈ infer Γ a)
    (hb : Res.expr db ∈ infer Γ b) (h : σ.copiesTo τ = true) (hn : Γ.namesLocal a = false) :
    Res.expr (Typed.assignCopy dl db h hn) ∈ infer Γ (.assign .assign a b) := by
  refine List.mem_append_right _ (List.mem_flatMap.mpr ⟨⟨τ, dl⟩, mem_lvsOf' hl,
    List.mem_flatMap.mpr ⟨⟨σ, db⟩, mem_tysOf' hb, List.mem_append_left _ (List.mem_append_right _ ?_)⟩⟩)
  dsimp only
  rw [dif_pos h, dif_pos hn]
  exact List.mem_singleton.mpr rfl

theorem compound_mem {op : AssignOp} {dl : LVal Γ a τ} {db : Typed Γ b σ} (hl : Res.lval dl ∈ infer Γ a)
    (hb : Res.expr db ∈ infer Γ b) (h : op.fits Γ.isBase σ τ = true) :
    Res.expr (Typed.compound dl db h) ∈ infer Γ (.assign op a b) := by
  refine List.mem_append_right _ (List.mem_flatMap.mpr ⟨⟨τ, dl⟩, mem_lvsOf' hl,
    List.mem_flatMap.mpr ⟨⟨σ, db⟩, mem_tysOf' hb, List.mem_append_right _ ?_⟩⟩)
  dsimp only
  rw [dif_pos h]
  exact List.mem_singleton.mpr rfl

theorem index_sub {da : Typed Γ a τ} {di : Typed Γ i σ} (ha : Res.expr da ∈ infer Γ a)
    (hi : Res.expr di ∈ infer Γ i) {r : Res Γ .expr (.index a (.some i))}
    (h : r ∈ indexPair Γ τ da σ di) : r ∈ infer Γ (.index a (.some i)) :=
  List.mem_append_right _ (List.mem_flatMap.mpr ⟨_, slot_mem hi,
    List.mem_flatMap.mpr ⟨⟨τ, da⟩, mem_tysOf' ha, h⟩⟩)

theorem indexArray_res {l : DataLoc} {n : Option Nat} (da : Typed Γ a (.array l τ n)) (di : Typed Γ i σ)
    (h1 : σ.isIndex = true) (h2 : inBounds σ n = true) :
    Res.expr (Typed.indexArray da di h1 h2) ∈ indexPair Γ _ da σ di ∧
      ∀ hl : l ≠ .calldata, Res.lval (LVal.indexArray da hl di h1 h2) ∈ indexPair Γ _ da σ di := by
  simp only [indexPair]
  rw [dif_pos h1, dif_pos h2]
  refine ⟨List.mem_append_left _ (List.mem_append_left _ List.mem_cons_self), fun hl => ?_⟩
  refine List.mem_append_left _ (List.mem_append_left _ (List.mem_cons_of_mem _ ?_))
  rw [dif_pos hl]
  exact List.mem_singleton.mpr rfl

theorem indexMapping_res {τk : STy} (da : Typed Γ a (.mapping τk τ)) (di : Typed Γ i σ)
    (h : σ.implicit Γ.isBase τk = true) :
    Res.expr (Typed.indexMapping da di h) ∈ indexPair Γ _ da σ di ∧
      Res.lval (LVal.indexMapping da di h) ∈ indexPair Γ _ da σ di := by
  simp only [indexPair]
  rw [dif_pos h]
  exact ⟨List.mem_append_left _ (List.mem_append_left _ List.mem_cons_self),
    List.mem_append_left _ (List.mem_append_left _ (List.mem_cons_of_mem _ List.mem_cons_self))⟩

theorem indexBytes_res (da : Typed Γ a τ) (hm : bytesLike τ = true)
    (di : Typed Γ i σ) (h1 : σ.isIndex = true) (h2 : inBounds σ (fixedLen τ) = true) :
    Res.expr (Typed.indexBytes da hm di h1 h2) ∈ indexPair Γ τ da σ di := by
  refine List.mem_append_left _ (List.mem_append_right _ ?_)
  rw [dif_pos hm, dif_pos h1, dif_pos h2]
  exact List.mem_singleton.mpr rfl

theorem indexBytesL_res {l : DataLoc} (da : Typed Γ a (.bytes l)) (hl : l ≠ .calldata) (di : Typed Γ i σ)
    (h1 : σ.isIndex = true) : Res.lval (LVal.indexBytes da hl di h1) ∈ indexPair Γ _ da σ di := by
  refine List.mem_append_right _ ?_
  simp only
  rw [dif_pos hl, dif_pos h1]
  exact List.mem_singleton.mpr rfl

theorem length_mem {ρ : STy} {da : Typed Γ a τ} (ha : Res.expr da ∈ infer Γ a) (h : τ.lengthTy = Option.some ρ) :
    Res.expr (Typed.length da h) ∈ infer Γ (.member a "length") := by
  refine List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_right _ ?_)))
  simp only [memberRes]
  refine List.mem_flatMap.mpr ⟨⟨τ, da⟩, mem_tysOf' ha, ?_⟩
  split
  · rename_i ρ' h'
    rw [h] at h'; cases h'
    exact List.mem_singleton.mpr rfl
  · rename_i h'; rw [h] at h'; cases h'

theorem balance_mem {p : Bool} {da : Typed Γ a (.address p)} (ha : Res.expr da ∈ infer Γ a) :
    Res.expr (Typed.balance da) ∈ infer Γ (.member a "balance") := by
  refine List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_right _ ?_)))
  simp only [memberRes]
  exact List.mem_flatMap.mpr ⟨⟨_, da⟩, mem_tysOf' ha, List.mem_singleton.mpr rfl⟩

theorem magic_mem {g m feature : String} {bi : Builtin} (hr : Γ.resolve g = Option.some (.builtin bi))
    (hs : bi.memberStatus m = Option.some (.admitted feature)) (ht : bi.memberTy m = Option.some τ)
    (hv : (bi == .msg && m == "value" && !Γ.msgValue) = false) :
    Res.expr (Typed.magic hr hs ht hv) ∈ infer Γ (.member (.ident g) m) := by
  refine List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ ?_))
  show _ ∈ magicRes Γ g m
  unfold magicRes
  split
  · rename_i b' hr'
    rw [hr] at hr'; cases hr'
    split
    · rename_i f' hs'
      rw [hs] at hs'; cases hs'
      split
      · rename_i τ' ht'
        rw [ht] at ht'; cases ht'
        rw [dif_pos hv]
        exact List.mem_singleton.mpr rfl
      · rename_i ht'; rw [ht] at ht'; cases ht'
    · rename_i hn; exact absurd hs (hn feature)
  · rename_i hn; exact absurd hr (hn bi)

theorem callIdent_sub {f : String} {es : Syn (.list .expr)} {σs : List STy} {ds : TypedArgs Γ es σs}
    (h : ⟨σs, ds⟩ ∈ argsOf Γ (infer Γ es)) {r : Res Γ .expr (.call (.ident f) (.positional es))}
    (hr : r ∈ callIdentRes Γ f σs ds) : r ∈ infer Γ (.call (.ident f) (.positional es)) :=
  List.mem_append_right _ (List.mem_flatMap.mpr ⟨_, pos_mem h, hr⟩)

theorem callInternal_res {f : String} {es : Syn (.list .expr)} {σs ps rs : List STy} {d : Decl}
    (ds : TypedArgs Γ es σs)
    (hf : (Γ.functions f).filter (fun d' => match d'.fnSig Γ.env with
        | Option.some (ps', _) => argsFit Γ.isBase σs ps'
        | Option.none => false) = [d])
    (hs : d.fnSig Γ.env = Option.some (ps, rs)) :
    Res.expr (Typed.callInternal ds hf hs) ∈ callIdentRes Γ f σs ds := by
  refine List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ ?_))
  split
  · rename_i d' hf'
    have e' : [d] = [d'] := hf.symm.trans hf'
    cases e'
    split
    · rename_i p' hs'
      rw [hs] at hs'; cases hs'
      exact List.mem_singleton.mpr rfl
    · rename_i hs'; rw [hs] at hs'; cases hs'
  · rename_i hn; exact absurd hf (hn d)

theorem convUser_res {n : String} {x : Syn .expr} (dx : Typed Γ x σ) (ht : Γ.convTarget n = Option.some τ)
    (h : σ.explicit Γ.isBase τ = true) :
    Res.expr (Typed.convUser ht dx h) ∈ callIdentRes Γ n [σ] (.cons dx .nil) := by
  refine List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ ?_))
  show _ ∈ (match ht : Γ.convTarget n with
     | Option.some τ => if h : σ.explicit Γ.isBase τ = true then [Res.expr (Typed.convUser ht dx h)] else []
     | Option.none => [])
  split
  · rename_i τ' ht'
    rw [ht] at ht'; cases ht'
    rw [dif_pos h]; exact List.mem_singleton.mpr rfl
  · rename_i ht'; rw [ht] at ht'; cases ht'

theorem builtin_res {f feature : String} {es : Syn (.list .expr)} {σs : List STy} {bi : Builtin}
    (hr : Γ.resolve f = Option.some (.builtin bi)) (hst : bi.status = .admitted feature)
    (ds : TypedArgs Γ es σs) (hc : bi.callTy Γ.isBase σs = Option.some τ) :
    Res.expr (Typed.builtinCall hr hst ds hc) ∈ callIdentRes Γ f σs ds := by
  refine List.mem_append_left _ (List.mem_append_right _ ?_)
  split
  · rename_i b' hr'
    rw [hr] at hr'; cases hr'
    split
    · rename_i f' hst'
      rw [hst] at hst'; cases hst'
      split
      · rename_i τ' hc'
        rw [hc] at hc'; cases hc'
        exact List.mem_singleton.mpr rfl
      · rename_i hc'; rw [hc] at hc'; cases hc'
    · rename_i hn; exact absurd hst (hn feature)
  · rename_i hn; exact absurd hr (hn bi)

theorem structNew_res {S : String} {es : Syn (.list .expr)} {σs : List STy} {dn : DeclName}
    {fs : List (String × STy)} (hs : Γ.structOf S = Option.some dn)
    (hf : Γ.env.structFields dn .memory = Option.some fs) (ds : TypedArgs Γ es σs)
    (ha : argsFit Γ.isBase σs (fs.map Prod.snd) = true) :
    Res.expr (Typed.structNew hs hf ds ha) ∈ callIdentRes Γ S σs ds := by
  refine List.mem_append_right _ ?_
  split
  · rename_i dn' hs'
    rw [hs] at hs'; cases hs'
    split
    · rename_i fs' hf'
      rw [hf] at hf'; cases hf'
      rw [dif_pos ha]; exact List.mem_singleton.mpr rfl
    · rename_i hf'; rw [hf] at hf'; cases hf'
  · rename_i hs'; rw [hs] at hs'; cases hs'

theorem structMember_mem {l : DataLoc} {dn : DeclName} {x : String} {i : Nat}
    {da : Typed Γ a (.struct l dn)} (ha : Res.expr da ∈ infer Γ a)
    (hf : Γ.env.fieldAt dn l x = Option.some (i, τ)) :
    Res.expr (Typed.member da hf) ∈ infer Γ (.member a x) ∧
      ∀ hl : l ≠ .calldata, Res.lval (LVal.member da hl hf) ∈ infer Γ (.member a x) := by
  have key : ∀ r, r ∈ (Res.expr (Typed.member da hf) ::
      (if hl : l ≠ .calldata then [Res.lval (LVal.member da hl hf)] else [])) →
      r ∈ infer Γ (.member a x) := by
    intro r hr
    refine List.mem_append_left _ (List.mem_append_right _ ?_)
    refine List.mem_flatMap.mpr ⟨⟨_, da⟩, mem_tysOf' ha, ?_⟩
    dsimp only
    split
    · rename_i p hf'
      rw [hf] at hf'; cases hf'; exact hr
    · rename_i hf'; rw [hf] at hf'; cases hf'
  refine ⟨key _ List.mem_cons_self, fun hl => key _ (List.mem_cons_of_mem _ ?_)⟩
  rw [dif_pos hl]; exact List.mem_singleton.mpr rfl

theorem recv_mem {m : String} {da : Typed Γ a τ} (ha : Res.expr da ∈ infer Γ a) :
    Res.recv (m := m) da ∈ infer Γ (.member a m) :=
  List.mem_append_right _ (List.mem_map.mpr ⟨⟨τ, da⟩, mem_tysOf' ha, rfl⟩)

theorem callMember_sub {c : Syn .expr} {m : String} {es : Syn (.list .expr)} {σs : List STy}
    {ds : TypedArgs Γ es σs} (h : ⟨σs, ds⟩ ∈ argsOf Γ (infer Γ es))
    {r : Res Γ .expr (.call (.member c m) (.positional es))}
    (hr : r ∈ abiRes Γ c m σs ds ++ (infer Γ (.member c m)).flatMap (memberCallOne Γ σs ds)) :
    r ∈ infer Γ (.call (.member c m) (.positional es)) :=
  List.mem_append_right _ (List.mem_flatMap.mpr ⟨_, pos_mem h, hr⟩)

theorem extCall_mem {c : Syn .expr} {f : String} {es : Syn (.list .expr)} {σs ps rs : List STy}
    {dn : DeclName} {d : Decl} {dc : Typed Γ c (.contract dn)} (hc : Res.expr dc ∈ infer Γ c)
    {ds : TypedArgs Γ es σs} (h : ⟨σs, ds⟩ ∈ argsOf Γ (infer Γ es))
    (hx : extOverloads Γ.env Γ.isBase dn f σs = [d]) (hs : d.fnSig Γ.env = Option.some (ps, rs)) :
    Res.expr (Typed.extCall dc ds hx hs) ∈ infer Γ (.call (.member c f) (.positional es)) := by
  refine callMember_sub h (List.mem_append_right _ (List.mem_flatMap.mpr ⟨_, recv_mem hc, ?_⟩))
  simp only [memberCallOne]
  split
  · rename_i d' hx'
    have e' : [d] = [d'] := hx.symm.trans hx'
    cases e'
    split
    · rename_i p' hs'
      rw [hs] at hs'; cases hs'
      exact List.mem_singleton.mpr rfl
    · rename_i hs'; rw [hs] at hs'; cases hs'
  · rename_i hn; exact absurd hx (hn d)

theorem transfer_mem {c v : Syn .expr} {dc : Typed Γ c (.address true)} (hc : Res.expr dc ∈ infer Γ c)
    {dv : Typed Γ v σ} (hv : Res.expr dv ∈ infer Γ v) (h : σ.implicit Γ.isBase (.int IntTy.u256) = true) :
    Res.expr (Typed.transfer dc dv h) ∈
      infer Γ (.call (.member c "transfer") (.positional (.cons v .nil))) := by
  refine List.mem_append_right _ (List.mem_flatMap.mpr ⟨_, args1_mem hv,
    List.mem_append_right _ (List.mem_flatMap.mpr ⟨_, recv_mem hc, ?_⟩)⟩)
  simp only [memberCallOne, payRes, payOne]
  rw [dif_pos h]; exact List.mem_singleton.mpr rfl

theorem send_mem {c v : Syn .expr} {dc : Typed Γ c (.address true)} (hc : Res.expr dc ∈ infer Γ c)
    {dv : Typed Γ v σ} (hv : Res.expr dv ∈ infer Γ v) (h : σ.implicit Γ.isBase (.int IntTy.u256) = true) :
    Res.expr (Typed.send dc dv h) ∈
      infer Γ (.call (.member c "send") (.positional (.cons v .nil))) := by
  refine List.mem_append_right _ (List.mem_flatMap.mpr ⟨_, args1_mem hv,
    List.mem_append_right _ (List.mem_flatMap.mpr ⟨_, recv_mem hc, ?_⟩)⟩)
  show _ ∈ (if h : σ.implicit Γ.isBase (.int IntTy.u256) = true then [Res.expr (Typed.send dc dv h)] else [])
  rw [dif_pos h]; exact List.mem_singleton.mpr rfl

theorem abiEncode_mem {g m : String} {es : Syn (.list .expr)} {σs : List STy} {k : AbiKind}
    {ds : TypedArgs Γ es σs} (h : ⟨σs, ds⟩ ∈ argsOf Γ (infer Γ es))
    (hr : Γ.resolve g = Option.some (.builtin .abi)) (hk : AbiKind.ofMember m = Option.some k)
    (ha : k.argsOK Γ.isBase σs = true) :
    Res.expr (Typed.abiEncode hr hk ds ha) ∈ infer Γ (.call (.member (.ident g) m) (.positional es)) := by
  refine callMember_sub h (List.mem_append_left _ ?_)
  simp only [abiRes]
  split
  · rename_i hr'
    split
    · rename_i k' hk'
      rw [hk] at hk'; cases hk'
      rw [dif_pos ha]; exact List.mem_singleton.mpr rfl
    · rename_i hk'; rw [hk] at hk'; cases hk'
  · rename_i hn; exact absurd hr hn

theorem extCallValue_mem {c v : Syn .expr} {f : String} {es : Syn (.list .expr)} {σs ps rs : List STy}
    {dn : DeclName} {d : Decl} {dc : Typed Γ c (.contract dn)} (hc : Res.expr dc ∈ infer Γ c)
    {dv : Typed Γ v σ} (hv' : Res.expr dv ∈ infer Γ v)
    (hv : σ.implicit Γ.isBase (.int IntTy.u256) = true)
    {ds : TypedArgs Γ es σs} (h : ⟨σs, ds⟩ ∈ argsOf Γ (infer Γ es))
    (hx : extOverloads Γ.env Γ.isBase dn f σs = [d]) (hs : d.fnSig Γ.env = Option.some (ps, rs))
    (hm : d.fnMut = Option.some .payable) :
    Res.expr (Typed.extCallValue dc dv hv ds hx hs hm) ∈
      infer Γ (.call (.callOptions (.member c f) (.namedArg "value" v) .nil) (.positional es)) := by
  have hw : Res.withValue (ns := .nil) dc dv ∈
      infer Γ (.callOptions (.member c f) (.namedArg "value" v) .nil) :=
    List.mem_append_right _ (List.mem_flatMap.mpr ⟨_, recv_mem hc, List.mem_flatMap.mpr
      ⟨_, List.mem_map.mpr ⟨⟨σ, dv⟩, mem_tysOf' hv', rfl⟩, List.mem_singleton.mpr rfl⟩⟩)
  refine List.mem_append_right _ (List.mem_flatMap.mpr ⟨_, pos_mem h, List.mem_flatMap.mpr ⟨_, hw, ?_⟩⟩)
  simp only [valueCallOne]
  rw [dif_pos hv]
  split
  · rename_i d' hx'
    have e' : [d] = [d'] := hx.symm.trans hx'
    cases e'
    split
    · rename_i p' hs'
      rw [hs] at hs'; cases hs'
      rw [dif_pos hm]; exact List.mem_singleton.mpr rfl
    · rename_i hs'; rw [hs] at hs'; cases hs'
  · rename_i hn; exact absurd hx (hn d)

theorem convElem_mem {el : Elem} {h : el ≠ .addressPayable} {x : Syn .expr} {dx : Typed Γ x σ}
    (hx' : Res.expr dx ∈ infer Γ x) (hx : σ.explicit Γ.isBase (el.ty (convLoc σ)) = true) :
    Res.expr (Typed.convElem (h := h) dx rfl hx) ∈ infer Γ (.call (.elemType el h) (.positional (.cons x .nil))) := by
  refine List.mem_append_right _ (List.mem_flatMap.mpr ⟨_, args1_mem hx', ?_⟩)
  show _ ∈ convElemRes Γ el h [σ] (.cons dx .nil)
  simp only [convElemRes]
  rw [dif_pos hx]; exact List.mem_singleton.mpr rfl

theorem payable_mem {x : Syn .expr} {dx : Typed Γ x σ} (hx' : Res.expr dx ∈ infer Γ x)
    (h : payableArg σ = true) :
    Res.expr (Typed.payable dx h) ∈ infer Γ (.payableConv (.positional (.cons x .nil))) := by
  refine List.mem_append_right _ (List.mem_flatMap.mpr ⟨_, args1_mem hx', ?_⟩)
  show _ ∈ payableRes Γ [σ] (.cons dx .nil)
  simp only [payableRes]
  rw [dif_pos h]; exact List.mem_singleton.mpr rfl

theorem paren_mem {d : Typed Γ a τ} (h : Res.expr d ∈ infer Γ a) :
    Res.expr (Typed.paren d) ∈ infer Γ (.tuple (.some a) .nil) :=
  List.mem_append_right _ (List.mem_flatMap.mpr ⟨_, slot_mem h,
    List.mem_flatMap.mpr ⟨_, nil_mem, List.mem_singleton.mpr rfl⟩⟩)

theorem parenL_mem {d : LVal Γ a τ} (h : Res.lval d ∈ infer Γ a) :
    Res.lval (LVal.paren d) ∈ infer Γ (.tuple (.some a) .nil) :=
  List.mem_append_right _ (List.mem_flatMap.mpr ⟨_, slotL_mem h,
    List.mem_flatMap.mpr ⟨_, nil_mem, List.mem_singleton.mpr rfl⟩⟩)

theorem slots_of_mem {s : Syn (.list (.opt .expr))} {L : List (Res Γ (.list (.opt .expr)) s)}
    {τs : List STy} {ds : TypedSlots Γ s τs} (h : ⟨τs, ds⟩ ∈ slotsOf Γ L) (hne : τs ≠ []) :
    Res.slots ds ∈ L := by
  obtain ⟨r, hr, hs⟩ := List.mem_filterMap.mp h
  cases r with
  | slots d0 => cases hs; exact hr
  | nilList => cases hs; exact absurd rfl hne

theorem tuple_mem {s : Syn (.list (.opt .expr))} {τs : List STy} {d : Typed Γ a τ} {ds : TypedSlots Γ s τs}
    (h : Res.expr d ∈ infer Γ a) (hs : ⟨τs, ds⟩ ∈ slotsOf Γ (infer Γ s)) (hne : τs ≠ []) :
    Res.expr (Typed.tuple d ds hne) ∈ infer Γ (.tuple (.some a) s) := by
  have hr := slots_of_mem hs hne
  refine List.mem_append_right _ (List.mem_flatMap.mpr ⟨_, slot_mem h,
    List.mem_flatMap.mpr ⟨_, hr, ?_⟩⟩)
  cases τs with
  | nil => exact absurd rfl hne
  | cons _ _ => exact List.mem_singleton.mpr rfl

theorem args_cons_mem {x : Syn .expr} {es : Syn (.list .expr)} {τs : List STy} {d : Typed Γ x τ}
    {ds : TypedArgs Γ es τs} (h : Res.expr d ∈ infer Γ x) (hs : ⟨τs, ds⟩ ∈ argsOf Γ (infer Γ es)) :
    ⟨τ :: τs, TypedArgs.cons d ds⟩ ∈ argsOf Γ (infer Γ (.cons x es)) := by
  obtain ⟨r, hr, he⟩ := List.mem_filterMap.mp hs
  refine List.mem_filterMap.mpr ⟨Res.args (.cons d ds), List.mem_flatMap.mpr ⟨_, h,
    List.mem_filterMap.mpr ⟨r, hr, ?_⟩⟩, rfl⟩
  cases r with
  | args d0 => cases he; rfl
  | nilList => cases he; rfl

theorem slots_cons_mem {x : Syn .expr} {s : Syn (.list (.opt .expr))} {τs : List STy} {d : Typed Γ x τ}
    {ds : TypedSlots Γ s τs} (h : Res.expr d ∈ infer Γ x) (hs : ⟨τs, ds⟩ ∈ slotsOf Γ (infer Γ s)) :
    ⟨τ :: τs, TypedSlots.cons d ds⟩ ∈ slotsOf Γ (infer Γ (.cons (.some x) s)) := by
  obtain ⟨r, hr, he⟩ := List.mem_filterMap.mp hs
  refine List.mem_filterMap.mpr ⟨Res.slots (.cons d ds), List.mem_flatMap.mpr ⟨_, slot_mem h,
    List.mem_filterMap.mpr ⟨r, hr, ?_⟩⟩, rfl⟩
  cases r with
  | slots d0 => cases he; rfl
  | nilList => cases he; rfl

end Rules2

mutual

/-- **Completeness for expressions**: every type S01 derives for an
expression is one `infer` finds. -/
theorem typed_complete {Γ : Ctx} : {e : Syn .expr} → {τ : STy} → Typed Γ e τ → τ ∈ inferTys Γ e
  | _, _, .const hq ha hx => mem_tysOf (constRes_sub _ _ (const_mem hq ha hx))
  | _, _, .litBytes hf => mem_tysOf (litBytes_mem hf)
  | _, _, .litAddress h => mem_tysOf (litAddress_mem h)
  | _, _, .bool _ => mem_tysOf (lit_sub (List.mem_singleton.mpr rfl))
  | _, _, .str _ => mem_tysOf (lit_sub (List.mem_singleton.mpr rfl))
  | _, _, .hexStr _ => mem_tysOf (lit_sub (List.mem_singleton.mpr rfl))
  | _, _, .unicodeStr _ => mem_tysOf (lit_sub (List.mem_singleton.mpr rfl))
  | _, _, .loc hr ht => mem_tysOf (loc_mem hr ht).1
  | _, _, .state hr hv => mem_tysOf (state_mem hr hv).1
  | _, _, .this hr hs => mem_tysOf (this_mem hr hs)
  | _, _, .paren d => by
    obtain ⟨d', h⟩ := exists_expr (typed_complete d)
    exact mem_tysOf (paren_mem h)
  | _, _, .tuple d ds hne => by
    obtain ⟨d', h⟩ := exists_expr (typed_complete d)
    obtain ⟨ds', hs⟩ := exists_slots (slots_complete ds)
    exact mem_tysOf (tuple_mem h hs hne)
  | _, _, .neg d hs => by
    obtain ⟨d', h⟩ := exists_expr (typed_complete d)
    exact mem_tysOf (prefix_sub h (neg_res d' hs))
  | _, _, .negFixed d => by
    obtain ⟨d', h⟩ := exists_expr (typed_complete d)
    exact mem_tysOf (prefix_sub h (negFixed_res d'))
  | _, _, .not d => by
    obtain ⟨d', h⟩ := exists_expr (typed_complete d)
    exact mem_tysOf (prefix_sub h (not_res d'))
  | _, _, .bitNot d hb => by
    obtain ⟨d', h⟩ := exists_expr (typed_complete d)
    exact mem_tysOf (prefix_sub h (bitNot_res d' hb))
  | _, _, .incDec hop dl hn => by
    obtain ⟨d', h⟩ := exists_lval (lval_complete dl)
    exact mem_tysOf (prefix_sub h (incDec_res hop d' hn))
  | _, _, .incDecSuffix dl hn => by
    obtain ⟨d', h⟩ := exists_lval (lval_complete dl)
    exact mem_tysOf (suffix_sub h (suffix_res d' hn))
  | _, _, .delete dl hm hp => by
    obtain ⟨d', h⟩ := exists_lval (lval_complete dl)
    exact mem_tysOf (prefix_sub h (delete_res d' hm hp))
  | _, _, .arith hk da db hc hn hz => by
    obtain ⟨da', ha⟩ := exists_expr (typed_complete da)
    obtain ⟨db', hb⟩ := exists_expr (typed_complete db)
    exact mem_tysOf (bin_mem hk ha hb (arith_pair hk hc hn hz))
  | _, _, .bit hk da db hc hn => by
    obtain ⟨da', ha⟩ := exists_expr (typed_complete da)
    obtain ⟨db', hb⟩ := exists_expr (typed_complete db)
    exact mem_tysOf (bin_mem hk ha hb (bit_pair hk hc hn))
  | _, _, .shift hk da db h1 h2 h3 => by
    obtain ⟨da', ha⟩ := exists_expr (typed_complete da)
    obtain ⟨db', hb⟩ := exists_expr (typed_complete db)
    exact mem_tysOf (bin_mem hk ha hb (shift_pair hk h1 h2 h3))
  | _, _, .exp hk da db h1 h2 h3 => by
    obtain ⟨da', ha⟩ := exists_expr (typed_complete da)
    obtain ⟨db', hb⟩ := exists_expr (typed_complete db)
    exact mem_tysOf (bin_mem hk ha hb (exp_pair hk h1 h2 h3))
  | _, _, .order hk da db hc hn => by
    obtain ⟨da', ha⟩ := exists_expr (typed_complete da)
    obtain ⟨db', hb⟩ := exists_expr (typed_complete db)
    exact mem_tysOf (bin_mem hk ha hb (order_pair hk hc hn))
  | _, _, .eq hk da db hc hn => by
    obtain ⟨da', ha⟩ := exists_expr (typed_complete da)
    obtain ⟨db', hb⟩ := exists_expr (typed_complete db)
    exact mem_tysOf (bin_mem hk ha hb (eq_pair hk hc hn))
  | _, _, .compareConst hk hkk ha hb => mem_tysOf (compare_mem hk (compare_res hk hkk ha hb))
  | _, _, .logic hk da db => by
    obtain ⟨da', ha⟩ := exists_expr (typed_complete da)
    obtain ⟨db', hb⟩ := exists_expr (typed_complete db)
    exact mem_tysOf (bin_mem hk ha hb (logic_pair hk))
  | _, _, .cond dc da db hc => by
    obtain ⟨dc', h0⟩ := exists_expr (typed_complete dc)
    obtain ⟨da', ha⟩ := exists_expr (typed_complete da)
    obtain ⟨db', hb⟩ := exists_expr (typed_complete db)
    exact mem_tysOf (cond_mem h0 ha hb hc)
  | _, _, .assign dl db h1 h2 => by
    obtain ⟨dl', hl⟩ := exists_lval (lval_complete dl)
    obtain ⟨db', hb⟩ := exists_expr (typed_complete db)
    exact mem_tysOf (assign_mem hl hb h1 h2)
  | _, _, .compound dl db h => by
    obtain ⟨dl', hl⟩ := exists_lval (lval_complete dl)
    obtain ⟨db', hb⟩ := exists_expr (typed_complete db)
    exact mem_tysOf (compound_mem hl hb h)
  | _, _, .indexArray da di h1 h2 => by
    obtain ⟨da', ha⟩ := exists_expr (typed_complete da)
    obtain ⟨di', hi⟩ := exists_expr (typed_complete di)
    exact mem_tysOf (index_sub ha hi (indexArray_res da' di' h1 h2).1)
  | _, _, .indexMapping da di h => by
    obtain ⟨da', ha⟩ := exists_expr (typed_complete da)
    obtain ⟨di', hi⟩ := exists_expr (typed_complete di)
    exact mem_tysOf (index_sub ha hi (indexMapping_res da' di' h).1)
  | _, _, .indexBytes da hm di h1 h2 => by
    obtain ⟨da', ha⟩ := exists_expr (typed_complete da)
    obtain ⟨di', hi⟩ := exists_expr (typed_complete di)
    exact mem_tysOf (index_sub ha hi (indexBytes_res da' hm di' h1 h2))
  | _, _, .length da h => by
    obtain ⟨da', ha⟩ := exists_expr (typed_complete da)
    exact mem_tysOf (length_mem ha h)
  | _, _, .convElem dx hτ hx => by
    subst hτ
    obtain ⟨dx', h⟩ := exists_expr (typed_complete dx)
    exact mem_tysOf (convElem_mem h hx)
  | _, _, .convUser ht dx h => by
    obtain ⟨dx', hx⟩ := exists_expr (typed_complete dx)
    exact mem_tysOf (List.mem_append_right _ (List.mem_flatMap.mpr ⟨_, args1_mem hx, convUser_res dx' ht h⟩))
  | _, _, .payable dx h => by
    obtain ⟨dx', hx⟩ := exists_expr (typed_complete dx)
    exact mem_tysOf (payable_mem hx h)
  | _, _, .callInternal ds hf hs => by
    obtain ⟨ds', h⟩ := exists_args (args_complete ds)
    exact mem_tysOf (callIdent_sub h (callInternal_res ds' hf hs))
  | _, _, .magic hr hs ht hv => mem_tysOf (magic_mem hr hs ht hv)
  | _, _, .balance da => by
    obtain ⟨da', ha⟩ := exists_expr (typed_complete da)
    exact mem_tysOf (balance_mem ha)
  | _, _, .builtinCall hr hst ds hc => by
    obtain ⟨ds', h⟩ := exists_args (args_complete ds)
    exact mem_tysOf (callIdent_sub h (builtin_res hr hst ds' hc))
  | _, _, .member da hf => by
    obtain ⟨da', ha⟩ := exists_expr (typed_complete da)
    exact mem_tysOf (structMember_mem ha hf).1
  | _, _, .structNew hs hf ds ha => by
    obtain ⟨ds', h⟩ := exists_args (args_complete ds)
    exact mem_tysOf (callIdent_sub h (structNew_res hs hf ds' ha))
  | _, _, .extCall dc ds hx hs => by
    obtain ⟨dc', hc⟩ := exists_expr (typed_complete dc)
    obtain ⟨ds', h⟩ := exists_args (args_complete ds)
    exact mem_tysOf (extCall_mem hc h hx hs)
  | _, _, .extCallValue dc dv hv ds hx hs hm => by
    obtain ⟨dc', hc⟩ := exists_expr (typed_complete dc)
    obtain ⟨dv', hv'⟩ := exists_expr (typed_complete dv)
    obtain ⟨ds', h⟩ := exists_args (args_complete ds)
    exact mem_tysOf (extCallValue_mem hc hv' hv h hx hs hm)
  | _, _, .transfer dc dv h => by
    obtain ⟨dc', hc⟩ := exists_expr (typed_complete dc)
    obtain ⟨dv', hv⟩ := exists_expr (typed_complete dv)
    exact mem_tysOf (transfer_mem hc hv h)
  | _, _, .send dc dv h => by
    obtain ⟨dc', hc⟩ := exists_expr (typed_complete dc)
    obtain ⟨dv', hv⟩ := exists_expr (typed_complete dv)
    exact mem_tysOf (send_mem hc hv h)
  | _, _, .abiEncode hr hk ds ha => by
    obtain ⟨ds', h⟩ := exists_args (args_complete ds)
    exact mem_tysOf (abiEncode_mem h hr hk ha)
  | _, _, .assignCopy dl db h hn => by
    obtain ⟨dl', hl⟩ := exists_lval (lval_complete dl)
    obtain ⟨db', hb⟩ := exists_expr (typed_complete db)
    exact mem_tysOf (assignCopy_mem hl hb h hn)

/-- **Completeness for lvalues.** -/
theorem lval_complete {Γ : Ctx} : {e : Syn .expr} → {τ : STy} → LVal Γ e τ →
    τ ∈ (lvsOf Γ (infer Γ e)).map Sigma.fst
  | _, _, .loc hr ht => mem_lvsOf (loc_mem hr ht).2
  | _, _, .state hr hv hm => mem_lvsOf ((state_mem hr hv).2 hm)
  | _, _, .paren d => by
    obtain ⟨d', h⟩ := exists_lval (lval_complete d)
    exact mem_lvsOf (parenL_mem h)
  | _, _, .indexArray da hl di h1 h2 => by
    obtain ⟨da', ha⟩ := exists_expr (typed_complete da)
    obtain ⟨di', hi⟩ := exists_expr (typed_complete di)
    exact mem_lvsOf (index_sub ha hi ((indexArray_res da' di' h1 h2).2 hl))
  | _, _, .indexMapping da di h => by
    obtain ⟨da', ha⟩ := exists_expr (typed_complete da)
    obtain ⟨di', hi⟩ := exists_expr (typed_complete di)
    exact mem_lvsOf (index_sub ha hi (indexMapping_res da' di' h).2)
  | _, _, .indexBytes da hl di h1 => by
    obtain ⟨da', ha⟩ := exists_expr (typed_complete da)
    obtain ⟨di', hi⟩ := exists_expr (typed_complete di)
    exact mem_lvsOf (index_sub ha hi (indexBytesL_res da' hl di' h1))
  | _, _, .member da hl hf => by
    obtain ⟨da', ha⟩ := exists_expr (typed_complete da)
    exact mem_lvsOf ((structMember_mem ha hf).2 hl)

/-- **Completeness for argument lists.** -/
theorem args_complete {Γ : Ctx} : {es : Syn (.list .expr)} → {τs : List STy} → TypedArgs Γ es τs →
    τs ∈ (argsOf Γ (infer Γ es)).map Sigma.fst
  | _, _, .nil => List.mem_map.mpr ⟨⟨[], .nil⟩, List.mem_filterMap.mpr ⟨_, nil_mem, rfl⟩, rfl⟩
  | _, _, .cons d ds => by
    obtain ⟨d', h⟩ := exists_expr (typed_complete d)
    obtain ⟨ds', hs⟩ := exists_args (args_complete ds)
    exact List.mem_map.mpr ⟨_, args_cons_mem h hs, rfl⟩

/-- **Completeness for tuple slots.** -/
theorem slots_complete {Γ : Ctx} : {s : Syn (.list (.opt .expr))} → {τs : List STy} → TypedSlots Γ s τs →
    τs ∈ (slotsOf Γ (infer Γ s)).map Sigma.fst
  | _, _, .nil => List.mem_map.mpr ⟨⟨[], .nil⟩, List.mem_filterMap.mpr ⟨_, nil_mem, rfl⟩, rfl⟩
  | _, _, .cons d ds => by
    obtain ⟨d', h⟩ := exists_expr (typed_complete d)
    obtain ⟨ds', hs⟩ := exists_slots (slots_complete ds)
    exact List.mem_map.mpr ⟨_, slots_cons_mem h hs, rfl⟩

end

end Solidity.Frontend.Static

namespace Solidity.Frontend.Static

/-- **The checker decides S01's expression typing.** -/
theorem hasType_iff {Γ : Solidity.Source.Ctx} {e : Solidity.Source.Syn .expr} {τ : Solidity.Source.STy} :
    Solidity.Source.HasType Γ e τ ↔ τ ∈ inferTys Γ e :=
  ⟨fun ⟨d⟩ => typed_complete d, fun h => (exists_expr h).elim fun d _ => ⟨d⟩⟩

end Solidity.Frontend.Static
