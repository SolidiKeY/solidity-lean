import Solidity.Calculus.UpdRuleScoped
import Solidity.Calculus.StateFacts

/-!
# Merges over a storage or memory write, on scoped updates

Two merges on `Upd C Γ Δ`, where
`Upd.seqPar` (`Calculus/Graft.lean`) refuses them: it reads `V` in `U`'s
state exactly, so a symbol of `V` that reads a global part `U` writes is
refused, but `storage` after a storage write.

* `{L ‖ storage := S}{V}`, `L` locals (`Upd.stOnly`, `Upd.lastSt`), is
  `{L ‖ storage := S ‖ V[L, S/storage]}` (`Upd.mergeSt?`): the locals and
  `storage` substituted in one pass, memory reads included, and a push
  slot `p[p.length]` or an index check `p[i]`, which read the storage of
  the state they run in, carried over as `p[p.length]@S` and `p[i]@S`
  (`nextIn`, `atIn`).  A storage variable `U` sets (`old := s`) reads `s`.
* `{memory := M}{V}` is `{memory := M ‖ V[M/memory]}` (`Upd.mergeMem?`), and
  `{L ‖ memory := M}{V}` the locals and `memory` substituted in one pass
  (`Upd.mergeMemL?`).

**Typed sorts** (W9.8.3d).  One substitution does all three
(`Tm.substP`: the locals by what `U` leaves, `storage` and `memory` by
what it writes where it writes them), read where a write looks: a term of
`V` read in a typed state `U` lands on, and its substitute read before,
are one reading up to the heap typing of a memory (`Srt.SameO`,
`Tm.substP_eval`), every symbol but the ones that read the storage
(`storage`, `next`, `at`) or the memory (`memory`) reading the global part
alike in the two states (`Op1.eval_sameP` …: they keep the ledger, the
funds and the transaction).  The grafts share one shape (`Upd.graftF`:
`U`'s elements, then `V`'s, each right-hand side mapped by a term map),
which gives `U` then `V` where the map reads each term so (`GraftOK`,
`holds_upd_graftF`, as `holds_upd_graft` does for `Upd.seqPar`); each
merge gives the two updates in turn under one modality
(`holds_upd_mergeSt`, `holds_upd_mergeMem`, `holds_upd_mergeMemL`), one
way, as `Calculus/UpdRuleScoped.lean`'s rules.

Gate G0's first two conditions hold as in `Calculus/UpdRuleScoped.lean`:
the walk over `V` (`Upd.graftF`) is the recursor, its `match` twin
`Upd.graftFM` linked by `Upd.graftF_eq_graftFM`; a head is read by
`Upd.casesOn` (`Upd.mergeMem?`) or `Fml.updHead?` (`MergeNameS.top`), and
a symbol by a `match` on the symbol alone (`Op1.substStep` …).
-/

namespace Solidity

open Solidity (Srt Op0 Op1 Op2 Op3 Modality)

variable {C : Contract}

/-! ## Symbols over two global parts

Two global parts that keep the ledger, the funds and the transaction read
every symbol alike but the ones that read the storage (`storage`, `next`,
`at`) and `memory`, the only symbol that reads the heap: a memory symbol
reads the memory it is given, whose heap typing is its own. -/

/-- A constant that reads no storage. -/
def _root_.Solidity.Op0.stFree {s : Srt} : Op0 C s → Bool
  | .storage => false
  | _ => true

/-- A constant that reads no memory. -/
def _root_.Solidity.Op0.memFree {s : Srt} : Op0 C s → Bool
  | .memory => false
  | _ => true

/-- A unary symbol that reads no storage. -/
def _root_.Solidity.Op1.stFree {a s : Srt} : Op1 C a s → Bool
  | .next => false
  | _ => true

/-- A binary symbol that reads no storage. -/
def _root_.Solidity.Op2.stFree {a b s : Srt} : Op2 C a b s → Bool
  | .at _ => false
  | _ => true

/-- Two global parts with one ledger, funds and transaction. -/
structure State.SameRest (g₀ g₁ : State C []) : Prop where
  net : g₁.net = g₀.net
  bal : g₁.selfBalance = g₀.selfBalance
  tx : g₁.tx = g₀.tx

section EvalSameP

/-- A memory argument of two readings, one grown heap: its pieces. -/
local macro "same_mem " h:ident x:ident y:ident : tactic =>
  `(tactic| (rcases $x:ident with _ | ⟨_, _, ⟨⟩⟩ <;> rcases $y:ident with _ | ⟨_, _, ⟨⟩⟩ <;>
      first
      | rfl
      | exact Option.noConfusion $h
      | (obtain ⟨hH, hhp⟩ := Sigma.mk.inj (Option.some.inj $h); subst hH; cases hhp; rfl)))

/-- A reading at a sort whose values do not depend on the heap typing:
the two are one. -/
local macro "same_eq " h:ident x:ident y:ident : tactic =>
  `(tactic| (cases $x:ident <;> cases $y:ident <;>
      first | rfl | exact Option.noConfusion $h | exact congrArg some (Option.some.inj $h)))

local macro "same_subst " h:ident x:ident y:ident : tactic =>
  `(tactic| (have hxy : $x = $y := (by same_eq $h $x $y); rw [← hxy]; clear hxy))

variable {g₀ g₁ : State C []}

/-- A memory write's heap, by the heap it writes into alone. -/
theorem Grown.writeT_sig {H : HTy} (m : Grown H (fun _ => Unit)) {T : Ty} (a : MAddrT T)
    (v : MvT T) : (m.writeT a v).map (Srt.forget (C := C) .mem) =
      ((a.resolve m.H').bind fun ra => (MvT.toMVal m.H' T v).bind fun mv =>
        m.heap.writeAddr ra mv).map (fun hp => (⟨m.H', hp⟩ : (H' : HTy) × Heap H')) := by
  unfold Grown.writeT
  simp only [Option.bind_eq_bind]
  cases a.resolve m.H' with
  | none => rfl
  | some ra =>
    simp only [Option.bind_some]
    cases MvT.toMVal m.H' T v with
    | none => rfl
    | some mv =>
      simp only [Option.bind_some]
      cases m.heap.writeAddr ra mv <;> rfl

theorem _root_.Solidity.Op0.eval_sameP {s : Srt} (o : Op0 C s) (hr : g₀.SameRest g₁)
    (hs : g₁.storage = g₀.storage ∨ o.stFree = true)
    (hm : Srt.forget (C := C) .mem g₁.memT = Srt.forget .mem g₀.memT ∨ o.memFree = true) :
    Srt.SameO s (o.eval g₀) (o.eval g₁) := by
  rcases g₀ with ⟨st₀, H₀, hp₀, ⟨⟩, n₀, b₀, t₀⟩
  rcases g₁ with ⟨st₁, H₁, hp₁, ⟨⟩, n₁, b₁, t₁⟩
  obtain ⟨hn, hb, ht⟩ := hr
  dsimp only at hn hb ht
  subst hn hb ht
  cases o with
  | storage =>
    rcases hs with hs | hs
    · dsimp only at hs; subst hs; rfl
    · exact absurd hs Bool.false_ne_true
  | memory =>
    rcases hm with hm | hm
    · exact congrArg some hm.symm
    · exact absurd hm Bool.false_ne_true
  | _ => rfl

theorem _root_.Solidity.Op1.eval_sameP {a s : Srt} (o : Op1 C a s) (hr : g₀.SameRest g₁)
    (hs : g₁.storage = g₀.storage ∨ o.stFree = true) {x : Option (a.Den C g₀.H)}
    {y : Option (a.Den C g₁.H)} (h : Srt.SameO a x y) :
    Srt.SameO s (o.eval g₀ x) (o.eval g₁ y) := by
  rcases g₀ with ⟨st₀, H₀, hp₀, ⟨⟩, n₀, b₀, t₀⟩
  rcases g₁ with ⟨st₁, H₁, hp₁, ⟨⟩, n₁, b₁, t₁⟩
  obtain ⟨hn, hb, ht⟩ := hr
  dsimp only at hn hb ht
  subst hn hb ht
  cases o with
  | next =>
    rcases hs with hs | hs
    · dsimp only at hs; subst hs; same_subst h x y; rfl
    · exact absurd hs Bool.false_ne_true
  | alloc R hR => same_mem h x y
  | addM R hR => same_mem h x y
  | _ => same_subst h x y; rfl

theorem _root_.Solidity.Op2.eval_sameP {a b s : Srt} (o : Op2 C a b s) (hr : g₀.SameRest g₁)
    (hs : g₁.storage = g₀.storage ∨ o.stFree = true) {x : Option (a.Den C g₀.H)}
    {x' : Option (a.Den C g₁.H)} {y : Option (b.Den C g₀.H)} {y' : Option (b.Den C g₁.H)}
    (hx : Srt.SameO a x x') (hy : Srt.SameO b y y') :
    Srt.SameO s (o.eval g₀ x y) (o.eval g₁ x' y') := by
  rcases g₀ with ⟨st₀, H₀, hp₀, ⟨⟩, n₀, b₀, t₀⟩
  rcases g₁ with ⟨st₁, H₁, hp₁, ⟨⟩, n₁, b₁, t₁⟩
  obtain ⟨hn, hb, ht⟩ := hr
  dsimp only at hn hb ht
  subst hn hb ht
  cases o with
  | «at» it =>
    rcases hs with hs | hs
    · dsimp only at hs; subst hs; same_subst hx x x'; same_subst hy y y'; rfl
    · exact absurd hs Bool.false_ne_true
  | read => same_subst hy y y'; same_mem hx x x'
  | mlen => same_subst hy y y'; same_mem hx x x'
  | copyMem => same_subst hy y y'; same_mem hx x x'
  | iread => same_subst hy y y'; same_mem hx x x'
  | copy hR => same_subst hy y y'; same_mem hx x x'
  | copySt hT => same_subst hy y y'; cases y <;> same_mem hx x x'
  | _ => same_subst hx x x'; same_subst hy y y'; rfl

theorem _root_.Solidity.Op3.eval_sameP {a b c s : Srt} (o : Op3 C a b c s)
    {x : Option (a.Den C g₀.H)} {x' : Option (a.Den C g₁.H)} {y : Option (b.Den C g₀.H)}
    {y' : Option (b.Den C g₁.H)} {z : Option (c.Den C g₀.H)} {z' : Option (c.Den C g₁.H)}
    (hx : Srt.SameO a x x') (hy : Srt.SameO b y y') (hz : Srt.SameO c z z') :
    Srt.SameO s (o.eval g₀ x y z) (o.eval g₁ x' y' z') := by
  cases o with
  | write =>
    same_subst hy y y'; same_subst hz z z'
    rcases x with _ | ⟨e₀, hp₀, ⟨⟩⟩ <;> rcases x' with _ | ⟨e₁, hp₁, ⟨⟩⟩
    · rfl
    · exact Option.noConfusion hx
    · exact Option.noConfusion hx
    · obtain ⟨hH, hhp⟩ := Sigma.mk.inj (Option.some.inj hx)
      subst hH
      cases hhp
      rw [Op3.eval_eq_evalM, Op3.eval_eq_evalM]
      cases y with
      | none => rfl
      | some a =>
        cases z with
        | none => rfl
        | some w =>
          exact (Grown.writeT_sig (C := C) _ a w).trans
            (Grown.writeT_sig (C := C) (Grown.mk e₁ hp₀ ()) a w).symm
  | _ => same_subst hx x x'; same_subst hy y y'; same_subst hz z z'; rfl

end EvalSameP

/-! ## An update grafted through a term map -/

section GraftF

variable {Γ Δ : Ctx} (F : {k : Srt} → Tm C Δ k → Option (Tm C Γ k))

/-- A right-hand side of `Δ` read in `Γ` through `F`. -/
def Rhs.mapF : {t : LTy} → Rhs C Δ t → Option (Rhs C Γ t)
  | _, .val t => (F t).map .val
  | _, .path p => (F p).map .path
  | _, .unset => some .unset
  | _, .mref i => (F i).map .mref
  | _, .store x => (F x).map .store
  | _, .saveNet => some .saveNet
  | _, .saveNetMt => some .saveNetMt
  | _, .zint t => (F t).map .zint

/-- An element whose right-hand sides are read in `Δ`, read in `Γ` through `F`. -/
def UpdElem.mapF {Ε : Ctx} : UpdElem C Δ Ε → Option (UpdElem C Γ Ε)
  | .local i r => (r.mapF F).map (.local i)
  | .storage x => (F x).map .storage
  | .memory m => (F m).map .memory
  | .selfBalance op a => (F a).map (.selfBalance op)
  | .net r op a => do pure (.net (← F r) op (← F a))
  | .pay r a => do pure (.pay (← F r) (← F a))
  | .netMt r a => do pure (.netMt (← F r) (← F a))
  | .setBalance a => (F a).map .setBalance

/-- `Upd.graftF`'s compiled twin. -/
def Upd.graftFM (U : Upd C Γ Δ) : {Δ₂ : Ctx} → Upd C Δ Δ₂ → Option (Upd C Γ Δ₂)
  | _, .nil => some U
  | _, .snoc V e => do pure (.snoc (← Upd.graftFM U V) (← e.mapF F))
  | _, .decl V x r => do pure (.decl (← Upd.graftFM U V) x (← r.mapF F))
  | _, .pop V h => (Upd.graftFM U V).map (.pop · h)
  | _, .drop V h => (Upd.graftFM U V).map (.drop · h)

/-- `V` after `U`, as one update from `U`'s state: `U`'s elements, then
`V`'s, each right-hand side read through `F`; by the recursor. -/
@[implemented_by Upd.graftFM]
def Upd.graftF (U : Upd C Γ Δ) {Δ₂ : Ctx} (V : Upd C Δ Δ₂) : Option (Upd C Γ Δ₂) :=
  Upd.rec (motive := fun Δ₂ _ => Option (Upd C Γ Δ₂)) (some U)
    (fun _ e ih => do pure (.snoc (← ih) (← e.mapF F)))
    (fun _ x r ih => do pure (.decl (← ih) x (← r.mapF F)))
    (fun _ h ih => ih.map (.pop · h)) (fun _ h ih => ih.map (.drop · h)) V

theorem Upd.graftF_eq_graftFM (U : Upd C Γ Δ) {Δ₂ : Ctx} (V : Upd C Δ Δ₂) :
    U.graftF F V = U.graftFM F V := by
  induction V with
  | nil => rfl
  | snoc V e ih | decl V x r ih | pop V h ih | drop V h ih =>
    simp only [Upd.graftFM, ← ih]; rfl

end GraftF

/-- `F` reads a term of a typed state an update lands on (`σ₁`) in the
state before it (`σ₀`), up to the heap typing of a memory; the update keeps
the ledger, the funds and the transaction. -/
structure GraftOK {Γ Δ : Ctx} (σ₀ : State C Γ) (σ₁ : State C Δ)
    (F : {k : Srt} → Tm C Δ k → Option (Tm C Γ k)) : Prop where
  tm : ∀ {k : Srt} (t : Tm C Δ k) {t' : Tm C Γ k}, F t = some t' →
    Srt.SameO k (t'.eval σ₀) (t.eval σ₁)
  rest : σ₀.glob.SameRest σ₁.glob
  /-- A term out of gas before is out of gas where the update lands. -/
  exh : ∀ {k : Srt} (t : Tm C Δ k) {t' : Tm C Γ k}, F t = some t' → t'.exhB σ₀ = true →
    t.exhB σ₁ = true

section GraftFSound

variable {Γ Δ : Ctx} {F : {k : Srt} → Tm C Δ k → Option (Tm C Γ k)} {σ₀ : State C Γ}
  {σ₁ : State C Δ}

theorem Rhs.eval_mapF (hF : GraftOK σ₀ σ₁ F) :
    {t : LTy} → (r : Rhs C Δ t) → {r' : Rhs C Γ t} → r.mapF F = some r' →
      r'.eval σ₀ = r.eval σ₁
  | _, .val t, r', h => by
    obtain ⟨t', ht, rfl⟩ := Option.map_eq_some_iff.1 h
    exact Srt.sameO_val.1 (hF.tm t ht)
  | _, .path p, r', h => by
    obtain ⟨p', hp, rfl⟩ := Option.map_eq_some_iff.1 h
    show (p'.eval σ₀).bind _ = (p.eval σ₁).bind _
    rw [Srt.sameO_path.1 (hF.tm p hp)]
  | _, .unset, r', h => by cases h; rfl
  | _, .mref i, r', h => by
    obtain ⟨i', hi, rfl⟩ := Option.map_eq_some_iff.1 h
    show (i'.eval σ₀).bind _ = (i.eval σ₁).bind _
    rw [Srt.sameO_ident.1 (hF.tm i hi)]
  | _, .store x, r', h => by
    obtain ⟨x', hx, rfl⟩ := Option.map_eq_some_iff.1 h
    show (x'.eval σ₀).bind _ = (x.eval σ₁).bind _
    rw [Srt.sameO_st.1 (hF.tm x hx)]
  | _, .saveNet, r', h => by
    cases h
    show some σ₀.net = some σ₁.net
    rw [show σ₁.net = σ₀.net from hF.rest.net]
  | _, .saveNetMt, r', h => by cases h; rfl
  | _, .zint t, r', h => by
    obtain ⟨t', ht, rfl⟩ := Option.map_eq_some_iff.1 h
    exact Srt.sameO_kint.1 (hF.tm t ht)

/-- An element mapped computes the global part the element does, read where
`U` lands, from one global part. -/
theorem UpdElem.globT_mapF (hF : GraftOK σ₀ σ₁ F) {Ε : Ctx} (e : UpdElem C Δ Ε)
    {e' : UpdElem C Γ Ε} (h : e.mapF F = some e') (G₀ : GlobT C σ₀.H) (G₁ : GlobT C σ₁.H)
    (hG : G₀.1 = G₁.1) : (e'.globT σ₀ G₀).map (·.1) = (e.globT σ₁ G₁).map (·.1) := by
  cases e with
  | «local» i r =>
    obtain ⟨r', hr, rfl⟩ := Option.map_eq_some_iff.1 h
    show ((r'.eval σ₀).bind fun _ => some G₀).map (·.1) =
      ((r.eval σ₁).bind fun _ => some G₁).map (·.1)
    rw [Rhs.eval_mapF hF r hr]
    cases r.eval σ₁ <;> simp only [Option.bind_none, Option.bind_some, Option.map_some, hG,
      Option.map_none]
  | storage x =>
    obtain ⟨x', hx, rfl⟩ := Option.map_eq_some_iff.1 h
    show ((x'.eval σ₀).bind fun st => some (G₀.withStorage st)).map (·.1) =
      ((x.eval σ₁).bind fun st => some (G₁.withStorage st)).map (·.1)
    rw [Srt.sameO_st.1 (hF.tm x hx)]
    cases x.eval σ₁ with
    | none => rfl
    | some st => exact congrArg some (GlobT.withStorage_congr hG st)
  | memory x =>
    obtain ⟨x', hx, rfl⟩ := Option.map_eq_some_iff.1 h
    have hm := hF.tm x hx
    show ((x'.eval σ₀).bind fun μ => some (G₀.withMem μ)).map (·.1) =
      ((x.eval σ₁).bind fun μ => some (G₁.withMem μ)).map (·.1)
    revert hm
    cases x'.eval σ₀ <;> cases x.eval σ₁ <;> intro hm
    · rfl
    · exact Option.noConfusion hm
    · exact Option.noConfusion hm
    · exact congrArg some (GlobT.withMem_congr hG (Option.some.inj hm))
  | selfBalance op a =>
    obtain ⟨a', ha, rfl⟩ := Option.map_eq_some_iff.1 h
    have hb : σ₁.selfBalance = σ₀.selfBalance := hF.rest.bal
    show ((a'.eval σ₀).bind fun amt =>
        (PrimTy.uint.ofInt? (op.apply σ₀.selfBalance.1 amt.1)).bind fun b =>
          some (G₀.withBalance b)).map (·.1) =
      ((a.eval σ₁).bind fun amt =>
        (PrimTy.uint.ofInt? (op.apply σ₁.selfBalance.1 amt.1)).bind fun b =>
          some (G₁.withBalance b)).map (·.1)
    rw [Srt.sameO_val.1 (hF.tm a ha), hb]
    cases a.eval σ₁ with
    | none => rfl
    | some amt =>
      simp only [Option.bind_some]
      cases PrimTy.uint.ofInt? (op.apply σ₀.selfBalance.1 amt.1) with
      | none => rfl
      | some b => exact congrArg some (GlobT.withBalance_congr hG b)
  | net r op a =>
    simp only [UpdElem.mapF] at h
    obtain ⟨r', hr, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨a', ha, h⟩ := Option.bind_eq_some_iff.1 h
    cases h
    show ((r'.eval σ₀).bind fun addr => (a'.eval σ₀).bind fun amt =>
        some (G₀.withNet (Semantics.setBy addr.1
          (op.apply ((Semantics.lookupBy addr.1 G₀.1.net).getD 0) amt.1) G₀.1.net))).map (·.1) =
      ((r.eval σ₁).bind fun addr => (a.eval σ₁).bind fun amt =>
        some (G₁.withNet (Semantics.setBy addr.1
          (op.apply ((Semantics.lookupBy addr.1 G₁.1.net).getD 0) amt.1) G₁.1.net))).map (·.1)
    rw [Srt.sameO_val.1 (hF.tm r hr), Srt.sameO_val.1 (hF.tm a ha), hG]
    cases r.eval σ₁ <;> cases a.eval σ₁ <;>
      first | rfl | exact congrArg some (GlobT.withNet_congr hG _)
  | pay r a =>
    simp only [UpdElem.mapF] at h
    obtain ⟨r', hr, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨a', ha, h⟩ := Option.bind_eq_some_iff.1 h
    cases h
    have ht : σ₁.tx = σ₀.tx := hF.rest.tx
    show ((r'.eval σ₀).bind fun addr => (a'.eval σ₀).bind fun amt =>
        some (G₀.withNet (if addr.1 = σ₀.tx.selfAddress.1 then G₀.1.net
          else Semantics.setBy addr.1 ((Semantics.lookupBy addr.1 G₀.1.net).getD 0 - amt.1)
            G₀.1.net))).map (·.1) =
      ((r.eval σ₁).bind fun addr => (a.eval σ₁).bind fun amt =>
        some (G₁.withNet (if addr.1 = σ₁.tx.selfAddress.1 then G₁.1.net
          else Semantics.setBy addr.1 ((Semantics.lookupBy addr.1 G₁.1.net).getD 0 - amt.1)
            G₁.1.net))).map (·.1)
    rw [Srt.sameO_val.1 (hF.tm r hr), Srt.sameO_val.1 (hF.tm a ha), ht, hG]
    cases r.eval σ₁ <;> cases a.eval σ₁ <;>
      first | rfl | exact congrArg some (GlobT.withNet_congr hG _)
  | netMt r a =>
    simp only [UpdElem.mapF] at h
    obtain ⟨r', hr, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨a', ha, h⟩ := Option.bind_eq_some_iff.1 h
    cases h
    show ((r'.eval σ₀).bind fun addr => (a'.eval σ₀).bind fun amt =>
        some (G₀.withNet [(addr.1, amt.1)])).map (·.1) =
      ((r.eval σ₁).bind fun addr => (a.eval σ₁).bind fun amt =>
        some (G₁.withNet [(addr.1, amt.1)])).map (·.1)
    rw [Srt.sameO_val.1 (hF.tm r hr), Srt.sameO_val.1 (hF.tm a ha)]
    cases r.eval σ₁ <;> cases a.eval σ₁ <;>
      first | rfl | exact congrArg some (GlobT.withNet_congr hG _)
  | setBalance a =>
    obtain ⟨a', ha, rfl⟩ := Option.map_eq_some_iff.1 h
    show ((a'.eval σ₀).bind fun amt => some (G₀.withBalance amt)).map (·.1) =
      ((a.eval σ₁).bind fun amt => some (G₁.withBalance amt)).map (·.1)
    rw [Srt.sameO_val.1 (hF.tm a ha)]
    cases a.eval σ₁ <;> first | rfl | exact congrArg some (GlobT.withBalance_congr hG _)

end GraftFSound

section GraftFT

variable {Γ Δ₁ : Ctx} {F : {k : Srt} → Tm C Δ₁ k → Option (Tm C Γ k)} {σ₀ : State C Γ}
  {U : Upd C Γ Δ₁}

/-- The grafted update halts where `U` does (on the twin). -/
theorem Upd.globT_graftFM_none (hU : U.globT σ₀ = none) :
    {Δ₂ : Ctx} → (V : Upd C Δ₁ Δ₂) → {W : Upd C Γ Δ₂} → U.graftFM F V = some W →
      W.globT σ₀ = none
  | _, .nil, W, h => by cases h; exact hU
  | _, .snoc V e', W, h => by
    simp only [Upd.graftFM] at h
    obtain ⟨W', hW, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨e'', -, h⟩ := Option.bind_eq_some_iff.1 h
    cases h
    show (W'.globT σ₀).bind _ = none
    rw [Upd.globT_graftFM_none hU V hW]
    rfl
  | _, .decl V x r, W, h => by
    simp only [Upd.graftFM] at h
    obtain ⟨W', hW, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨r', -, h⟩ := Option.bind_eq_some_iff.1 h
    cases h
    show (W'.globT σ₀).bind _ = none
    rw [Upd.globT_graftFM_none hU V hW]
    rfl
  | _, .pop V _, W, h => by
    obtain ⟨W', hW, rfl⟩ := Option.map_eq_some_iff.1 h
    exact Upd.globT_graftFM_none hU V hW
  | _, .drop V _, W, h => by
    obtain ⟨W', hW, rfl⟩ := Option.map_eq_some_iff.1 h
    exact Upd.globT_graftFM_none hU V hW

variable {σ₁ : State C Δ₁} {g₁ : GlobT C σ₀.H}

/-- **The grafted update computes the global part `V` does** in a typed
state `U` lands on (on the twin). -/
theorem Upd.globT_graftFM (hL : U.Lands σ₀ g₁ σ₁) (hF : GraftOK σ₀ σ₁ F) :
    {Δ₂ : Ctx} → (V : Upd C Δ₁ Δ₂) → {W : Upd C Γ Δ₂} → U.graftFM F V = some W →
      (W.globT σ₀).map (·.1) = (V.globT σ₁).map (·.1)
  | _, .nil, W, h => by
    cases h
    rw [hL.1]
    show some g₁.1 = some σ₁.glob
    rw [hL.2.1]
  | _, .snoc V e, W, h => by
    simp only [Upd.graftFM] at h
    obtain ⟨W', hW, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨e', he, h⟩ := Option.bind_eq_some_iff.1 h
    cases h
    exact GlobT.map_val_bind (Upd.globT_graftFM hL hF V hW)
      fun G₀ G₁ hG => UpdElem.globT_mapF hF e he G₀ G₁ hG
  | _, .decl V x r, W, h => by
    simp only [Upd.graftFM] at h
    obtain ⟨W', hW, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨r', hr, h⟩ := Option.bind_eq_some_iff.1 h
    cases h
    refine GlobT.map_val_bind (Upd.globT_graftFM hL hF V hW) fun G₀ G₁ hG => ?_
    show ((r'.eval σ₀).bind fun _ => some G₀).map (·.1) =
      ((r.eval σ₁).bind fun _ => some G₁).map (·.1)
    rw [Rhs.eval_mapF hF r hr]
    cases r.eval σ₁ <;> simp only [Option.bind_none, Option.bind_some, Option.map_some, hG,
      Option.map_none]
  | _, .pop V _, W, h => by
    obtain ⟨W', hW, rfl⟩ := Option.map_eq_some_iff.1 h
    exact Upd.globT_graftFM hL hF V hW
  | _, .drop V _, W, h => by
    obtain ⟨W', hW, rfl⟩ := Option.map_eq_some_iff.1 h
    exact Upd.globT_graftFM hL hF V hW

/-- **The grafted update leaves in each local what `V` does**, read in a
typed state `U` lands on (on the twin). -/
theorem Upd.held_graftFM (hL : U.Lands σ₀ g₁ σ₁) (hF : GraftOK σ₀ σ₁ F) :
    {Δ₂ : Ctx} → (V : Upd C Δ₁ Δ₂) → {W : Upd C Γ Δ₂} → U.graftFM F V = some W →
      ∀ {t : LTy} (i : Idx Δ₂ t) (v : t.VDen C), Held.OKV σ₁ v (V.held i) →
        Held.OKV σ₀ v (W.held i)
  | _, .nil, W, h, t, i, v, hv => by
    cases h
    have hi := (Held.OK_iff_OKV σ₀ σ₁ i _).1 (hL.2.2 i)
    show Held.OKV σ₀ v (U.held i)
    have hv : v = σ₁.getV i := hv
    rw [hv]
    exact hi
  | _, .snoc V e, W, h, t, i, v, hv => by
    simp only [Upd.graftFM] at h
    obtain ⟨W', hW, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨e', he, h⟩ := Option.bind_eq_some_iff.1 h
    cases h
    cases e with
    | «local» k r =>
      obtain ⟨r', hr, rfl⟩ := Option.map_eq_some_iff.1 he
      show Held.OKV σ₀ v (Subst.set (Upd.held W') k r' i)
      have hv : Held.OKV σ₁ v (Subst.set (Upd.held V) k r i) := hv
      unfold Subst.set at hv ⊢
      split
      · rename_i hki
        rw [dif_pos hki] at hv
        obtain rfl := Idx.ty_eq_of_toNat hki
        obtain rfl := Idx.toNat_inj k i hki
        show r'.eval σ₀ = some v
        rw [Rhs.eval_mapF hF r hr]
        exact hv
      · rename_i hki
        rw [dif_neg hki] at hv
        exact Upd.held_graftFM hL hF V hW i v hv
    | storage x | memory x | setBalance x =>
      obtain ⟨_, -, rfl⟩ := Option.map_eq_some_iff.1 he
      exact Upd.held_graftFM hL hF V hW i v hv
    | selfBalance op a =>
      obtain ⟨_, -, rfl⟩ := Option.map_eq_some_iff.1 he
      exact Upd.held_graftFM hL hF V hW i v hv
    | net r op a | netMt r a | pay r a =>
      simp only [UpdElem.mapF] at he
      obtain ⟨_, -, he⟩ := Option.bind_eq_some_iff.1 he
      obtain ⟨_, -, he⟩ := Option.bind_eq_some_iff.1 he
      cases he
      exact Upd.held_graftFM hL hF V hW i v hv
  | _, .decl V x r, W, h, t, i, v, hv => by
    simp only [Upd.graftFM] at h
    obtain ⟨W', hW, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨r', hr, h⟩ := Option.bind_eq_some_iff.1 h
    cases h
    cases i with
    | here =>
      show r'.eval σ₀ = some v
      rw [Rhs.eval_mapF hF r hr]
      exact hv
    | there j => exact Upd.held_graftFM hL hF V hW j v hv
  | _, .pop V e, W, h, t, i, v, hv => by
    obtain ⟨W', hW, rfl⟩ := Option.map_eq_some_iff.1 h
    exact Upd.held_graftFM hL hF V hW (i.ext e) v hv
  | _, .drop V e, W, h, t, i, v, hv => by
    obtain ⟨W', hW, rfl⟩ := Option.map_eq_some_iff.1 h
    exact Upd.held_graftFM hL hF V hW (i.wk e) v hv

/-- The grafted update reverts nowhere only where `U` does not. -/
theorem Upd.exhOk_graftFM_prefix :
    {Δ₂ : Ctx} → (V : Upd C Δ₁ Δ₂) → {W : Upd C Γ Δ₂} → U.graftFM F V = some W →
      W.exhOk σ₀ = true → U.exhOk σ₀ = true
  | _, .nil, W, h, hx => by cases h; exact hx
  | _, .snoc V e', W, h, hx => by
    simp only [Upd.graftFM] at h
    obtain ⟨W', hW, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨e'', -, h⟩ := Option.bind_eq_some_iff.1 h
    cases h
    exact Upd.exhOk_graftFM_prefix V hW (Bool.and_eq_true_iff.1 hx).1
  | _, .decl V x r, W, h, hx => by
    simp only [Upd.graftFM] at h
    obtain ⟨W', hW, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨r', -, h⟩ := Option.bind_eq_some_iff.1 h
    cases h
    exact Upd.exhOk_graftFM_prefix V hW (Bool.and_eq_true_iff.1 hx).1
  | _, .pop V _, W, h, hx => by
    obtain ⟨W', hW, rfl⟩ := Option.map_eq_some_iff.1 h
    exact Upd.exhOk_graftFM_prefix V hW hx
  | _, .drop V _, W, h, hx => by
    obtain ⟨W', hW, rfl⟩ := Option.map_eq_some_iff.1 h
    exact Upd.exhOk_graftFM_prefix V hW hx

/-- The grafted update is out of gas, where `U` halts, only where `U` is. -/
theorem Upd.exh_graftFM_none (hU : U.globT σ₀ = none) {Δ₂ : Ctx} (V : Upd C Δ₁ Δ₂)
    {W : Upd C Γ Δ₂} (h : U.graftFM F V = some W) (hx : W.exh σ₀ = true) : U.exh σ₀ = true := by
  have hk := Upd.exhOk_graftFM_prefix V h (Bool.and_eq_true_iff.1 hx).2
  exact Bool.and_eq_true_iff.2 ⟨Upd.exhAny_of_none σ₀ U hk hU, hk⟩

theorem Rhs.exhB_mapF (hF : GraftOK σ₀ σ₁ F) {t : LTy} (r : Rhs C Δ₁ t) {r' : Rhs C Γ t}
    (h : r.mapF F = some r') (hx : r'.exhB σ₀ = true) : r.exhB σ₁ = true := by
  cases r with
  | val x | path x | mref x | store x | zint x =>
    obtain ⟨x', hx', rfl⟩ := Option.map_eq_some_iff.1 h
    exact hF.exh x hx' hx
  | unset | saveNet | saveNetMt => cases h; exact hx

/-- An element mapped is out of gas where the element is. -/
theorem UpdElem.exhB_mapF (hF : GraftOK σ₀ σ₁ F) {Ε : Ctx} (e : UpdElem C Δ₁ Ε)
    {e' : UpdElem C Γ Ε} (h : e.mapF F = some e') (hx : e'.exhB σ₀ = true) :
    e.exhB σ₁ = true := by
  cases e with
  | «local» _ r =>
    obtain ⟨r', hr', rfl⟩ := Option.map_eq_some_iff.1 h
    exact Rhs.exhB_mapF hF r hr' hx
  | storage x | memory x | selfBalance _ x | setBalance x =>
    obtain ⟨x', hx', rfl⟩ := Option.map_eq_some_iff.1 h
    exact hF.exh x hx' hx
  | net r _ a | pay r a | netMt r a =>
    simp only [UpdElem.mapF] at h
    obtain ⟨r', hr', h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨a', ha', h⟩ := Option.bind_eq_some_iff.1 h
    cases h
    have er := hF.tm r hr'
    have ea := hF.tm a ha'
    simp only [UpdElem.exhB, Bool.or_eq_true, Bool.and_eq_true] at hx ⊢
    exact hx.imp (fun h => ⟨hF.exh r hr' h.1, ea.isSome ▸ h.2⟩)
      (fun h => ⟨hF.exh a ha' h.1, er.isSome ▸ h.2⟩)

/-- An element mapped returns where the element does. -/
theorem UpdElem.okB_mapF (hL : U.Lands σ₀ g₁ σ₁) (hF : GraftOK σ₀ σ₁ F) {Ε : Ctx}
    (e : UpdElem C Δ₁ Ε) {e' : UpdElem C Γ Ε} (h : e.mapF F = some e') :
    e'.okB σ₀ = e.okB σ₁ := by
  have hm := UpdElem.globT_mapF hF e h g₁ σ₁.globG hL.2.1.symm
  rw [← UpdElem.globT_isSome σ₀ e' g₁, ← UpdElem.globT_isSome σ₁ e σ₁.globG]
  revert hm
  cases e'.globT σ₀ g₁ <;> cases e.globT σ₁ σ₁.globG <;>
    simp only [Option.map_none, Option.map_some, reduceCtorEq, Option.isSome_none,
      Option.isSome_some, imp_self, false_implies, implies_true]

theorem Upd.exhOk_graftFM (hL : U.Lands σ₀ g₁ σ₁) (hF : GraftOK σ₀ σ₁ F) :
    {Δ₂ : Ctx} → (V : Upd C Δ₁ Δ₂) → {W : Upd C Γ Δ₂} → U.graftFM F V = some W →
      W.exhOk σ₀ = true → V.exhOk σ₁ = true
  | _, .nil, W, h, hx => rfl
  | _, .snoc V e, W, h, hx => by
    simp only [Upd.graftFM] at h
    obtain ⟨W', hW, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨e', he, h⟩ := Option.bind_eq_some_iff.1 h
    cases h
    simp only [Upd.exhOk, Bool.and_eq_true, Bool.or_eq_true] at hx ⊢
    refine ⟨Upd.exhOk_graftFM hL hF V hW hx.1, ?_⟩
    rw [← UpdElem.okB_mapF hL hF e he]
    exact hx.2.imp_right (UpdElem.exhB_mapF hF e he)
  | _, .decl V x r, W, h, hx => by
    simp only [Upd.graftFM] at h
    obtain ⟨W', hW, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨r', hr, h⟩ := Option.bind_eq_some_iff.1 h
    cases h
    simp only [Upd.exhOk, Bool.and_eq_true, Bool.or_eq_true] at hx ⊢
    rw [← Rhs.eval_mapF hF r hr]
    exact ⟨Upd.exhOk_graftFM hL hF V hW hx.1, hx.2.imp_right (Rhs.exhB_mapF hF r hr)⟩
  | _, .pop V _, W, h, hx => by
    obtain ⟨W', hW, rfl⟩ := Option.map_eq_some_iff.1 h
    exact Upd.exhOk_graftFM hL hF V hW hx
  | _, .drop V _, W, h, hx => by
    obtain ⟨W', hW, rfl⟩ := Option.map_eq_some_iff.1 h
    exact Upd.exhOk_graftFM hL hF V hW hx

theorem Upd.exhAny_graftFM (hL : U.Lands σ₀ g₁ σ₁) (hF : GraftOK σ₀ σ₁ F) :
    {Δ₂ : Ctx} → (V : Upd C Δ₁ Δ₂) → {W : Upd C Γ Δ₂} → U.graftFM F V = some W →
      W.exhAny σ₀ = true → V.exhAny σ₁ = true
  | _, .nil, W, h, hx => by
    cases h
    rw [Upd.exhAny_of_globT hL.1] at hx
    cases hx
  | _, .snoc V e, W, h, hx => by
    simp only [Upd.graftFM] at h
    obtain ⟨W', hW, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨e', he, h⟩ := Option.bind_eq_some_iff.1 h
    cases h
    simp only [Upd.exhAny, Bool.or_eq_true] at hx ⊢
    exact hx.imp (Upd.exhAny_graftFM hL hF V hW) (UpdElem.exhB_mapF hF e he)
  | _, .decl V x r, W, h, hx => by
    simp only [Upd.graftFM] at h
    obtain ⟨W', hW, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨r', hr, h⟩ := Option.bind_eq_some_iff.1 h
    cases h
    simp only [Upd.exhAny, Bool.or_eq_true] at hx ⊢
    exact hx.imp (Upd.exhAny_graftFM hL hF V hW) (Rhs.exhB_mapF hF r hr)
  | _, .pop V _, W, h, hx => by
    obtain ⟨W', hW, rfl⟩ := Option.map_eq_some_iff.1 h
    exact Upd.exhAny_graftFM hL hF V hW hx
  | _, .drop V _, W, h, hx => by
    obtain ⟨W', hW, rfl⟩ := Option.map_eq_some_iff.1 h
    exact Upd.exhAny_graftFM hL hF V hW hx

/-- **The grafted update is out of gas where `V` is**, in a typed state `U`
lands on. -/
theorem Upd.exh_graftFM (hL : U.Lands σ₀ g₁ σ₁) (hF : GraftOK σ₀ σ₁ F) {Δ₂ : Ctx}
    (V : Upd C Δ₁ Δ₂) {W : Upd C Γ Δ₂} (h : U.graftFM F V = some W) (hx : W.exh σ₀ = true) :
    V.exh σ₁ = true :=
  Bool.and_eq_true_iff.2 ⟨Upd.exhAny_graftFM hL hF V h (Bool.and_eq_true_iff.1 hx).1,
    Upd.exhOk_graftFM hL hF V h (Bool.and_eq_true_iff.1 hx).2⟩

end GraftFT

/-- **The grafted update gives the two in turn**, where `F` reads each
term where a write looks, in every typed state `U` lands on. -/
theorem holds_upd_graftF {m : Modality} {Γ Δ₁ Δ₂ : Ctx}
    {F : {k : Srt} → Tm C Δ₁ k → Option (Tm C Γ k)} {U : Upd C Γ Δ₁} {V : Upd C Δ₁ Δ₂}
    {W : Upd C Γ Δ₂} (σ : State C Γ)
    (hF : ∀ (g₁ : GlobT C σ.H) (σ₁ : State C Δ₁), U.Lands σ g₁ σ₁ → GraftOK σ σ₁ F)
    (hW : U.graftF F V = some W) {φ : Fml C Δ₂} (h : holds σ (.upd m W φ)) :
    holds σ (.upd m U (.upd m V φ)) := by
  have hW : U.graftFM F V = some W := Upd.graftF_eq_graftFM F U V ▸ hW
  have h : W.afterT m σ (holds · φ) := h
  refine Upd.afterT_introX (fun hU => (h.of_none (Upd.globT_graftFM_none hU V hW)).imp_right
    (Upd.exh_graftFM_none hU V hW)) fun g₁ σ₁ hL => ?_
  have hF := hF g₁ σ₁ hL
  have hG := Upd.globT_graftFM hL hF V hW
  refine Upd.afterT_introX (fun hV => (h.of_none ?_).imp_right (Upd.exh_graftFM hL hF V hW))
    fun g₂ σ₂ hL₂ => ?_
  · rw [hV] at hG
    cases hw : W.globT σ with
    | none => rfl
    | some _ => rw [hw] at hG; exact Option.noConfusion hG
  · rw [hL₂.1] at hG
    cases hw : W.globT σ with
    | none => rw [hw] at hG; exact Option.noConfusion hG
    | some g₂' =>
      rw [hw] at hG
      have hg : g₂'.1 = g₂.1 := Option.some.inj hG
      exact h.of_lands ⟨hw, hL₂.2.1.trans hg.symm, fun i => (Held.OK_iff_OKV _ _ _ _).2
        (Upd.held_graftFM hL hF V hW i _ ((Held.OK_iff_OKV _ _ _ _).1 (hL₂.2.2 i)))⟩

/-! ## The locals, the storage and the memory substituted -/

section SubstP

variable {Γ Δ : Ctx} (s : Subst C Γ Δ) (stS : Option (Tm C Γ .st)) (memS : Option (Tm C Γ .mem))

/-- A constant read before the update: `storage` by the storage it writes,
`memory` by the memory it writes, where it writes them. -/
def Op0.substStep {k : Srt} : Op0 C k → Tm C Γ k
  | .storage => stS.getD (.app0 .storage)
  | .memory => memS.getD (.app0 .memory)
  | o => .app0 o

/-- `p[p.length]` read before a storage write: `p[p.length]@S`. -/
def Op1.substStep {a k : Srt} : Op1 C a k → Tm C Γ a → Tm C Γ k
  | .next, x => match stS with
    | some S => .app2 .nextIn S x
    | none => .app1 .next x
  | o, x => .app1 o x

/-- `p[i]` read before a storage write: `p[i]@S`. -/
def Op2.substStep {a b k : Srt} : Op2 C a b k → Tm C Γ a → Tm C Γ b → Tm C Γ k
  | .at it, x, y => match stS with
    | some S => .app3 (.atIn it) S x y
    | none => .app2 (.at it) x y
  | o, x, y => .app2 o x y

/-- A term of `Δ` read in `Γ` before an update of locals, the storage
(`stS`) and the memory (`memS`): its locals replaced by what they hold (a
storage variable set to `x` by `x`), `storage` by `S` and `memory` by `M`
where the update writes them, a push slot and an index check read in `S`
(`nextIn`, `atIn`); `none` past an unset alias or a ledger variable the
update sets. -/
def Tm.substP : {k : Srt} → Tm C Δ k → Option (Tm C Γ k)
  | _, .pvV i => match s i with
    | .pos j => some (.pvV j)
    | .rhs (.val t) => some t
  | _, .pvP i => match s i with
    | .pos j => some (.pvP j)
    | .rhs (.path p) => some p
    | .rhs .unset => none
  | _, .pvS i => match s i with
    | .pos j => some (.pvS j)
    | .rhs (.store x) => some x
  | _, .pvI i => match s i with
    | .pos j => some (.pvI j)
    | .rhs (.mref t) => some t
  | _, .netOf i a => match s i with
    | .pos j => (Tm.substP a).map (.netOf j)
    | .rhs _ => none
  | _, .app0 o => some (o.substStep stS memS)
  | _, .app1 o x => (Tm.substP x).map (o.substStep stS)
  | _, .app2 o x y => do pure (o.substStep stS (← Tm.substP x) (← Tm.substP y))
  | _, .app3 o x y z => do pure (.app3 o (← Tm.substP x) (← Tm.substP y) (← Tm.substP z))
  | _, .pvZ i => match s i with
    | .pos j => some (.pvZ j)
    | .rhs (.zint t) => some t

theorem Op1.substStep_of_stFree {a k : Srt} {o : Op1 C a k} (h : o.stFree = true) (x : Tm C Γ a) :
    o.substStep stS x = .app1 o x := by
  cases o <;> first | rfl | exact absurd h Bool.false_ne_true

theorem Op2.substStep_of_stFree {a b k : Srt} {o : Op2 C a b k} (h : o.stFree = true)
    (x : Tm C Γ a) (y : Tm C Γ b) : o.substStep stS x y = .app2 o x y := by
  cases o <;> first | rfl | exact absurd h Bool.false_ne_true

end SubstP

section SubstPSound

variable {Γ Δ : Ctx} {U : Upd C Γ Δ} {σ₀ : State C Γ} {σ₁ : State C Δ} {g : GlobT C σ₀.H}
  {stS : Option (Tm C Γ .st)} {memS : Option (Tm C Γ .mem)}

/-- What the update leaves in the storage: `stS` read before it, else the
storage before. -/
def StOK (σ₀ : State C Γ) (σ₁ : State C Δ) : Option (Tm C Γ .st) → Prop
  | some S => S.eval σ₀ = some σ₁.storage
  | none => σ₁.storage = σ₀.storage

/-- What the update leaves in the memory: `memS` read before it, else the
memory before. -/
def MemOK (σ₀ : State C Γ) (σ₁ : State C Δ) : Option (Tm C Γ .mem) → Prop
  | some M => Srt.SameO .mem (M.eval σ₀) (some σ₁.glob.memT)
  | none => Srt.forget (C := C) .mem σ₁.glob.memT = Srt.forget .mem σ₀.glob.memT

/-- **Read before the update, the substituted term reads as the term in a
typed state it lands on**, up to the heap typing of a memory. -/
theorem Tm.substP_eval (hL : U.Lands σ₀ g σ₁) (hr : σ₀.glob.SameRest σ₁.glob)
    (hst : StOK σ₀ σ₁ stS) (hmem : MemOK σ₀ σ₁ memS) :
    {k : Srt} → (t : Tm C Δ k) → {t' : Tm C Γ k} → Tm.substP U.held stS memS t = some t' →
      Srt.SameO k (t'.eval σ₀) (t.eval σ₁)
  | _, .pvV i, t', h => by
    have hx := hL.2.2 i
    have h : (match U.held i with
        | .pos j => some (Tm.pvV j) | .rhs (.val t) => some t) = some t' := h
    generalize U.held i = x at h hx
    rw [Srt.sameO_val]
    match x, hx, h with
    | .pos j, hx, h =>
      cases h
      have hx : TEnv.get i σ₁.env = TEnv.get j σ₀.env := hx
      show some (TEnv.get j σ₀.env) = some (TEnv.get i σ₁.env)
      rw [hx]
    | .rhs (.val t), hx, h =>
      cases h
      exact hx
  | _, .pvP i, t', h => by
    have hx := hL.2.2 i
    have h : (match U.held i with
        | .pos j => some (Tm.pvP j) | .rhs (.path p) => some p | .rhs .unset => none) =
          some t' := h
    generalize U.held i = x at h hx
    rw [Srt.sameO_path]
    match x, hx, h with
    | .pos j, hx, h =>
      cases h
      have hx : TEnv.get i σ₁.env = TEnv.get j σ₀.env := hx
      show TEnv.get j σ₀.env = TEnv.get i σ₁.env
      rw [hx]
    | .rhs (.path p), hx, h =>
      cases h
      have hx : (t'.eval σ₀).bind (fun r => some (some r)) = some (TEnv.get i σ₁.env) := hx
      show t'.eval σ₀ = TEnv.get i σ₁.env
      cases hp : t'.eval σ₀ with
      | none => rw [hp] at hx; cases hx
      | some q =>
        rw [hp] at hx
        exact (Option.some.inj hx)
  | _, .pvS i, t', h => by
    have hx := hL.2.2 i
    have h : (match U.held i with
        | .pos j => some (Tm.pvS j) | .rhs (.store x) => some x) = some t' := h
    generalize U.held i = x at h hx
    rw [Srt.sameO_st]
    match x, hx, h with
    | .pos j, hx, h =>
      cases h
      have hx : TEnv.get i σ₁.env = TEnv.get j σ₀.env := hx
      show some (TEnv.get j σ₀.env) = some (TEnv.get i σ₁.env)
      rw [hx]
    | .rhs (.store x), hx, h =>
      cases h
      have hx : (t'.eval σ₀).bind (fun st => some st) = some (TEnv.get i σ₁.env) := hx
      show t'.eval σ₀ = some (TEnv.get i σ₁.env)
      cases hp : t'.eval σ₀ with
      | none => rw [hp] at hx; cases hx
      | some q => rw [hp] at hx; exact hx
  | _, .pvI i, t', h => by
    have hx := hL.2.2 i
    have h : (match U.held i with
        | .pos j => some (Tm.pvI j) | .rhs (.mref t) => some t) = some t' := h
    generalize U.held i = x at h hx
    rw [Srt.sameO_ident]
    match x, hx, h with
    | .pos j, hx, h =>
      cases h
      exact hx.symm
    | .rhs (.mref t), hx, h =>
      cases h
      have hx : (t'.eval σ₀).bind (fun id => some (some id)) = some (σ₁.getV i) := hx
      show t'.eval σ₀ = σ₁.getV i
      cases hp : t'.eval σ₀ with
      | none => rw [hp] at hx; cases hx
      | some q =>
        rw [hp] at hx
        exact (Option.some.inj hx)
  | _, .netOf i a, t', h => by
    have hx := hL.2.2 i
    have h : (match U.held i with
        | .pos j => (Tm.substP U.held stS memS a).map (Tm.netOf j) | .rhs _ => none) =
          some t' := h
    generalize U.held i = x at h hx
    rw [Srt.sameO_kint]
    match x, hx, h with
    | .rhs _, _, h => cases h
    | .pos j, hx, h =>
      obtain ⟨a', ha, rfl⟩ := Option.map_eq_some_iff.1 h
      have hx : TEnv.get i σ₁.env = TEnv.get j σ₀.env := hx
      have ha' : a'.eval σ₀ = a.eval σ₁ := Srt.sameO_val.1 (Tm.substP_eval hL hr hst hmem a ha)
      show (a'.eval σ₀).bind _ = (a.eval σ₁).bind _
      rw [ha', hx]
  | _, .app0 o, t', h => by
    cases h
    cases o with
    | storage =>
      cases stS with
      | some S => exact Srt.sameO_st.2 (hst.trans rfl)
      | none =>
        exact Op0.eval_sameP .storage hr (.inl hst) (.inr rfl)
    | memory =>
      cases memS with
      | some M => exact hmem
      | none => exact Op0.eval_sameP .memory hr (.inr rfl) (.inl hmem)
    | lit v => exact Op0.eval_sameP (.lit v) hr (.inr rfl) (.inr rfl)
    | env k => exact Op0.eval_sameP (.env k) hr (.inr rfl) (.inr rfl)
    | root r hr' => exact Op0.eval_sameP (.root r hr') hr (.inr rfl) (.inr rfl)
    | mtSt => exact Op0.eval_sameP .mtSt hr (.inr rfl) (.inr rfl)
    | member s f hf => exact Op0.eval_sameP (.member s f hf) hr (.inr rfl) (.inr rfl)
    | zlit n => exact Op0.eval_sameP (.zlit n) hr (.inr rfl) (.inr rfl)
  | _, .app1 o x, t', h => by
    obtain ⟨x', hx, rfl⟩ := Option.map_eq_some_iff.1 h
    have ihx := Tm.substP_eval hL hr hst hmem x hx
    by_cases hn : o.stFree = true
    · rw [Op1.substStep_of_stFree stS hn]
      exact Op1.eval_sameP o hr (.inr hn) ihx
    cases o with
    | next =>
      cases stS with
      | some S =>
        have hS : S.eval σ₀ = some σ₁.storage := hst
        show Srt.SameO _ (Tm.eval σ₀ (Tm.app2 .nextIn S x')) (Tm.eval σ₁ (Tm.app1 .next x))
        rw [Tm.eval_app2, Tm.eval_app1, hS, Srt.sameO_path.1 ihx, Op2.eval_eq_evalM,
          Op1.eval_eq_evalM]
        cases x.eval σ₁ <;> rfl
      | none => exact Op1.eval_sameP .next hr (.inl hst) ihx
    | _ => exact absurd rfl hn
  | _, .app2 o x y, t', h => by
    obtain ⟨x', hx, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨y', hy, h⟩ := Option.bind_eq_some_iff.1 h
    cases h
    have ihx := Tm.substP_eval hL hr hst hmem x hx
    have ihy := Tm.substP_eval hL hr hst hmem y hy
    by_cases hn : o.stFree = true
    · rw [Op2.substStep_of_stFree stS hn]
      exact Op2.eval_sameP o hr (.inr hn) ihx ihy
    cases o with
    | «at» it =>
      cases stS with
      | some S =>
        have hS : S.eval σ₀ = some σ₁.storage := hst
        show Srt.SameO _ (Tm.eval σ₀ (Tm.app3 (.atIn it) S x' y'))
          (Tm.eval σ₁ (Tm.app2 (.at it) x y))
        rw [Tm.eval_app3, Tm.eval_app2, hS, Srt.sameO_path.1 ihx, Srt.sameO_val.1 ihy,
          Op3.eval_eq_evalM, Op2.eval_eq_evalM]
        cases x.eval σ₁ <;> cases y.eval σ₁ <;> rfl
      | none => exact Op2.eval_sameP (.at it) hr (.inl hst) ihx ihy
    | _ => exact absurd rfl hn
  | _, .app3 o x y z, t', h => by
    obtain ⟨x', hx, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨y', hy, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨z', hz, h⟩ := Option.bind_eq_some_iff.1 h
    cases h
    exact Op3.eval_sameP o (Tm.substP_eval hL hr hst hmem x hx)
      (Tm.substP_eval hL hr hst hmem y hy) (Tm.substP_eval hL hr hst hmem z hz)
  | _, .pvZ i, t', h => by
    have hx := hL.2.2 i
    have h : (match U.held i with
        | .pos j => some (Tm.pvZ j) | .rhs (.zint t) => some t) = some t' := h
    generalize U.held i = x at h hx
    rw [Srt.sameO_kint]
    match x, hx, h with
    | .pos j, hx, h =>
      cases h
      have hx : TEnv.get i σ₁.env = TEnv.get j σ₀.env := hx
      show some (TEnv.get j σ₀.env) = some (TEnv.get i σ₁.env)
      rw [hx]
    | .rhs (.zint t), hx, h =>
      cases h
      exact hx

/-- **A term out of gas before the update, substituted, is out of gas in a
typed state it lands on.** -/
theorem Tm.substP_exhB (hL : U.Lands σ₀ g σ₁) (hr : σ₀.glob.SameRest σ₁.glob)
    (hst : StOK σ₀ σ₁ stS) (hmem : MemOK σ₀ σ₁ memS) :
    {k : Srt} → (t : Tm C Δ k) → {t' : Tm C Γ k} → Tm.substP U.held stS memS t = some t' →
      t'.exhB σ₀ = true → t.exhB σ₁ = true
  | _, .app2 o x y, t', h, hx => by
    have hw := Tm.substP_eval hL hr hst hmem (Tm.app2 o x y) h
    obtain ⟨x', hx', h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨y', hy', h⟩ := Option.bind_eq_some_iff.1 h
    cases h
    have ex := Tm.substP_eval hL hr hst hmem x hx'
    have ey := Tm.substP_eval hL hr hst hmem y hy'
    have ihx := Tm.substP_exhB hL hr hst hmem x hx'
    have ihy := Tm.substP_exhB hL hr hst hmem y hy'
    by_cases hn : o.stFree = true
    · rw [Op2.substStep_of_stFree stS hn] at hx hw
      simp only [Tm.exhB, Bool.or_eq_true, Bool.and_eq_true] at hx ⊢
      rcases hx with hx | ⟨hn', hx⟩
      · exact .inl (o.exhB_same ex ey ▸ hx)
      · refine .inr ⟨hw.isNone ▸ hn', ?_⟩
        rcases hx with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
        · exact .inl ⟨ihx h₁, ey.isSome ▸ h₂⟩
        · exact .inr ⟨ihy h₁, ex.isSome ▸ h₂⟩
    cases o with
    | «at» it =>
      cases stS with
      | some S =>
        have hS : S.eval σ₀ = some σ₁.storage := hst
        change (Tm.app3 (.atIn it) S x' y').exhB σ₀ = true at hx
        change Srt.SameO _ ((Tm.app3 (.atIn it) S x' y').eval σ₀) _ at hw
        simp only [Tm.exhB, Bool.or_eq_true, Bool.and_eq_true, Tm.exhB_of_eval σ₀ S hS, hS,
          Option.isSome_some, and_true, Bool.false_eq_true, false_and, false_or] at hx ⊢
        rcases hx with hx | ⟨hn', hx⟩
        · cases hx
        · refine .inr ⟨hw.isNone ▸ hn', ?_⟩
          rcases hx with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
          · exact .inl ⟨ihx h₁, ey.isSome ▸ h₂⟩
          · exact .inr ⟨ihy h₁, ex.isSome ▸ h₂⟩
      | none =>
        change (Tm.app2 (.at it) x' y').exhB σ₀ = true at hx
        change Srt.SameO _ ((Tm.app2 (.at it) x' y').eval σ₀) _ at hw
        simp only [Tm.exhB, Bool.or_eq_true, Bool.and_eq_true] at hx ⊢
        rcases hx with hx | ⟨hn', hx⟩
        · exact .inl (Op2.exhB_same _ ex ey ▸ hx)
        · refine .inr ⟨hw.isNone ▸ hn', ?_⟩
          rcases hx with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
          · exact .inl ⟨ihx h₁, ey.isSome ▸ h₂⟩
          · exact .inr ⟨ihy h₁, ex.isSome ▸ h₂⟩
    | _ => exact absurd rfl hn
  | _, .app3 o x y z, t', h, hx => by
    have hw := Tm.substP_eval hL hr hst hmem (Tm.app3 o x y z) h
    obtain ⟨x', hx', h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨y', hy', h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨z', hz', h⟩ := Option.bind_eq_some_iff.1 h
    cases h
    have ex := Tm.substP_eval hL hr hst hmem x hx'
    have ey := Tm.substP_eval hL hr hst hmem y hy'
    have ez := Tm.substP_eval hL hr hst hmem z hz'
    simp only [Tm.exhB, Bool.or_eq_true, Bool.and_eq_true] at hx ⊢
    rcases hx with hx | ⟨hn, hx⟩
    · exact .inl (o.exhB_same ex ey ez ▸ hx)
    · refine .inr ⟨hw.isNone ▸ hn, ?_⟩
      rcases hx with (⟨⟨h₁, h₂⟩, h₃⟩ | ⟨⟨h₁, h₂⟩, h₃⟩) | ⟨⟨h₁, h₂⟩, h₃⟩
      · exact .inl (.inl ⟨⟨Tm.substP_exhB hL hr hst hmem x hx' h₁, ey.isSome ▸ h₂⟩,
          ez.isSome ▸ h₃⟩)
      · exact .inl (.inr ⟨⟨Tm.substP_exhB hL hr hst hmem y hy' h₁, ex.isSome ▸ h₂⟩,
          ez.isSome ▸ h₃⟩)
      · exact .inr ⟨⟨Tm.substP_exhB hL hr hst hmem z hz' h₁, ex.isSome ▸ h₂⟩, ey.isSome ▸ h₃⟩
  | _, .app1 o x, t', h, hx => by
    have hw := Tm.substP_eval hL hr hst hmem (Tm.app1 o x) h
    obtain ⟨x', hx', rfl⟩ := Option.map_eq_some_iff.1 h
    have ex := Tm.substP_eval hL hr hst hmem x hx'
    have ihx := Tm.substP_exhB hL hr hst hmem x hx'
    by_cases hn : o.stFree = true
    · rw [Op1.substStep_of_stFree stS hn] at hx hw
      simp only [Tm.exhB, Bool.and_eq_true] at hx ⊢
      exact ⟨hw.isNone ▸ hx.1, ihx hx.2⟩
    cases o with
    | next =>
      cases stS with
      | some S =>
        have hS : S.eval σ₀ = some σ₁.storage := hst
        change (Tm.app2 .nextIn S x').exhB σ₀ = true at hx
        change Srt.SameO _ ((Tm.app2 .nextIn S x').eval σ₀) _ at hw
        simp only [Tm.exhB, Bool.or_eq_true, Bool.and_eq_true, Tm.exhB_of_eval σ₀ S hS, hS,
          Option.isSome_some, Bool.false_eq_true, false_and, false_or, and_true] at hx ⊢
        rcases hx with hx | ⟨hn', hx⟩
        · cases hx
        · exact ⟨hw.isNone ▸ hn', ihx hx⟩
      | none =>
        change (Tm.app1 .next x').exhB σ₀ = true at hx
        change Srt.SameO _ ((Tm.app1 .next x').eval σ₀) _ at hw
        simp only [Tm.exhB, Bool.and_eq_true] at hx ⊢
        exact ⟨hw.isNone ▸ hx.1, ihx hx.2⟩
    | _ => exact absurd rfl hn
  | _, .netOf i a, t', h, hx => by
    have hw := Tm.substP_eval hL hr hst hmem (Tm.netOf i a) h
    have h₀ := h
    have h : (match U.held i with
        | .pos j => (Tm.substP U.held stS memS a).map (Tm.netOf j) | .rhs _ => none) =
          some t' := h
    generalize U.held i = x at h
    match x, h with
    | .rhs _, h => cases h
    | .pos j, h =>
      obtain ⟨a', ha', rfl⟩ := Option.map_eq_some_iff.1 h
      simp only [Tm.exhB, Bool.and_eq_true] at hx ⊢
      exact ⟨hw.isNone ▸ hx.1, Tm.substP_exhB hL hr hst hmem a ha' hx.2⟩
  | _, .pvV i, t', h, hx => by
    have hw := Tm.substP_eval hL hr hst hmem (Tm.pvV i) h
    rw [Tm.eval_of_exhB σ₀ t' hx] at hw
    exact absurd hw (by nofun)
  | _, .pvS i, t', h, hx => by
    have hw := Tm.substP_eval hL hr hst hmem (Tm.pvS i) h
    rw [Tm.eval_of_exhB σ₀ t' hx] at hw
    exact absurd hw (by nofun)
  | _, .pvZ i, t', h, hx => by
    have hw := Tm.substP_eval hL hr hst hmem (Tm.pvZ i) h
    rw [Tm.eval_of_exhB σ₀ t' hx] at hw
    exact absurd hw (by nofun)
  | _, .pvP i, t', h, hx => by
    have hx' := hL.2.2 i
    have h : (match U.held i with
        | .pos j => some (Tm.pvP j) | .rhs (.path p) => some p | .rhs .unset => none) =
          some t' := h
    generalize U.held i = x at h hx'
    match x, hx', h with
    | .pos j, _, h => cases h; simp only [Tm.exhB, Bool.false_eq_true] at hx
    | .rhs (.path p), hx', h =>
      cases h
      have hx'' : (t'.eval σ₀).bind (fun r => some (some r)) = some (TEnv.get i σ₁.env) := hx'
      rw [Tm.eval_of_exhB σ₀ t' hx, Option.bind_none] at hx''
      cases hx''
  | _, .pvI i, t', h, hx => by
    have hx' := hL.2.2 i
    have h : (match U.held i with
        | .pos j => some (Tm.pvI j) | .rhs (.mref t) => some t) = some t' := h
    generalize U.held i = x at h hx'
    match x, hx', h with
    | .pos j, _, h => cases h; simp only [Tm.exhB, Bool.false_eq_true] at hx
    | .rhs (.mref p), hx', h =>
      cases h
      have hx'' : (t'.eval σ₀).bind (fun id => some (some id)) = some (σ₁.getV i) := hx'
      rw [Tm.eval_of_exhB σ₀ t' hx, Option.bind_none] at hx''
      cases hx''
  | _, .app0 o, t', h, hx => by
    cases h
    cases o with
    | storage =>
      cases stS with
      | some S =>
        have hS : S.eval σ₀ = some σ₁.storage := hst
        change S.exhB σ₀ = true at hx
        rw [Tm.exhB_of_eval σ₀ S hS] at hx
        cases hx
      | none => cases hx
    | memory =>
      cases memS with
      | some M =>
        have hM : Srt.SameO .mem (M.eval σ₀) (some σ₁.glob.memT) := hmem
        change M.exhB σ₀ = true at hx
        have hn := Tm.eval_of_exhB σ₀ M hx
        rw [hn] at hM
        exact absurd hM (by nofun)
      | none => cases hx
    | _ => cases hx

end SubstPSound

/-! ## What a storage or memory write leaves -/

section Leaves

variable {Γ : Ctx} {σ₀ : State C Γ}

/-- An update of locals and the storage keeps the rest of the global part
and the memory. -/
theorem Upd.stOnly_glob : {Δ : Ctx} → (U : Upd C Γ Δ) → U.stOnly = true →
    {g : GlobT C σ₀.H} → U.globT σ₀ = some g →
      σ₀.glob.SameRest g.1 ∧ Srt.forget (C := C) .mem g.1.memT = Srt.forget .mem σ₀.glob.memT
  | _, .nil, _, g, h => by
    cases h
    exact ⟨⟨rfl, rfl, rfl⟩, rfl⟩
  | _, .snoc U e, hU, g, h => by
    change (U.globT σ₀).bind (e.globT σ₀) = some g at h
    rw [Option.bind_eq_some_iff] at h
    obtain ⟨g', hg', h⟩ := h
    simp only [Upd.stOnly, Bool.and_eq_true] at hU
    obtain ⟨hr, hm⟩ := Upd.stOnly_glob U hU.1 hg'
    rw [UpdElem.globT_eq_globTM] at h
    cases e with
    | «local» k r =>
      simp only [UpdElem.globTM, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨_, _, rfl⟩ := h
      exact ⟨hr, hm⟩
    | storage x =>
      simp only [UpdElem.globTM, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨_, _, rfl⟩ := h
      exact ⟨⟨hr.net, hr.bal, hr.tx⟩, hm⟩
    | _ => nomatch hU.2
  | _, .decl U _ r, hU, g, h => by
    change (U.globT σ₀).bind (fun g => (r.eval σ₀).bind fun _ => some g) = some g at h
    simp only [Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨g', hg', _, _, rfl⟩ := h
    exact Upd.stOnly_glob U hU hg'
  | _, .pop U _, hU, _, h => Upd.stOnly_glob U hU h
  | _, .drop U _, hU, _, h => Upd.stOnly_glob U hU h

/-- The memory an update of locals writes last, its locals before it:
`{L ‖ memory := M}`, `L` an update of locals (`Upd.envOnly`); `none` for
any other update (`Upd.casesOn`). -/
def Upd.memLast? {Δ : Ctx} (U : Upd C Γ Δ) : Option (Tm C Γ .mem) :=
  Upd.casesOn (motive := fun _ _ => Option (Tm C Γ .mem)) U (nil := none)
    (snoc := fun L e => match e with
      | .memory M => if L.envOnly then some M else none
      | _ => none)
    (decl := fun _ _ _ => none) (pop := fun _ _ => none) (drop := fun _ _ => none)

/-- After `{L ‖ memory := M}` the global part is the one before with the
memory `M` leaves. -/
theorem Upd.memLast?_glob {Δ : Ctx} {U : Upd C Γ Δ} {M : Tm C Γ .mem} (hm : U.memLast? = some M)
    {g : GlobT C σ₀.H} (hU : U.globT σ₀ = some g) :
    ∃ μ, M.eval σ₀ = some μ ∧ g = σ₀.globG.withMem μ := by
  cases U with
  | snoc L e =>
    cases e with
    | memory M' =>
      change (if L.envOnly then some M' else none) = some M at hm
      split at hm
      · rename_i hL
        cases hm
        change (L.globT σ₀).bind (UpdElem.globT σ₀ (.memory M)) = some g at hU
        rw [Option.bind_eq_some_iff] at hU
        obtain ⟨g', hg', h⟩ := hU
        obtain rfl := Upd.envOnly_globT L hL hg'
        rw [UpdElem.globT_eq_globTM] at h
        simp only [UpdElem.globTM, Option.bind_eq_some_iff, Option.some.injEq] at h
        obtain ⟨μ, hμ, rfl⟩ := h
        exact ⟨μ, hμ, rfl⟩
      · cases hm
    | _ => cases hm
  | _ => cases hm

end Leaves

/-- **`sequentialToParallel` over a storage write**: `{U}{V}` as one update
where `U` writes locals and the storage, last `S`, and no other global
part; `none` otherwise. -/
def Upd.mergeSt? {Γ Δ₁ Δ₂ : Ctx} (U : Upd C Γ Δ₁) (V : Upd C Δ₁ Δ₂) : Option (Upd C Γ Δ₂) :=
  if U.stOnly then
    match U.lastSt with
    | some S => U.graftF (Tm.substP U.held (some S) none) V
    | none => none
  else none

/-- `{W} φ` gives `{U}{V} φ` for the storage merge `W`. -/
theorem holds_upd_mergeSt {m : Modality} {Γ Δ₁ Δ₂ : Ctx} {U : Upd C Γ Δ₁} {V : Upd C Δ₁ Δ₂}
    {W : Upd C Γ Δ₂} (hW : U.mergeSt? V = some W) {φ : Fml C Δ₂} (σ : State C Γ)
    (h : holds σ (.upd m W φ)) : holds σ (.upd m U (.upd m V φ)) := by
  unfold Upd.mergeSt? at hW
  split at hW
  · rename_i hst
    split at hW
    · rename_i S hS
      refine holds_upd_graftF σ (fun g₁ σ₁ hL => ?_) hW h
      obtain ⟨hr, hm⟩ := Upd.stOnly_glob U hst hL.1
      have hg : σ₁.glob = g₁.1 := hL.2.1
      have hr' : σ.glob.SameRest σ₁.glob := hg ▸ hr
      have hS' : StOK σ σ₁ (some S) := by
        show S.eval σ = some σ₁.storage
        rw [Upd.lastSt_eval U hL.1 S hS, ← hg]
        rfl
      have hm' : MemOK σ σ₁ (none : Option (Tm C Γ .mem)) := by
        show Srt.forget .mem σ₁.glob.memT = _
        rw [hg]
        exact hm
      exact ⟨fun t _ ht => Tm.substP_eval hL hr' hS' hm' t ht, hr',
        fun t _ ht hx => Tm.substP_exhB hL hr' hS' hm' t ht hx⟩
    · cases hW
  · cases hW

/-- What `{L ‖ memory := M}` leaves, read where it lands. -/
theorem MemOK.of_memLast {Γ Δ : Ctx} {U : Upd C Γ Δ} {M : Tm C Γ .mem} (hm : U.memLast? = some M)
    {σ : State C Γ} {g₁ : GlobT C σ.H} {σ₁ : State C Δ} (hL : U.Lands σ g₁ σ₁) :
    σ.glob.SameRest σ₁.glob ∧ StOK σ σ₁ (none : Option (Tm C Γ .st)) ∧ MemOK σ σ₁ (some M) := by
  obtain ⟨μ, hμ, rfl⟩ := Upd.memLast?_glob hm hL.1
  have hg : σ₁.glob = (σ.globG.withMem μ).1 := hL.2.1
  refine ⟨hg ▸ ⟨rfl, rfl, rfl⟩, ?_, ?_⟩
  · show σ₁.storage = σ.storage
    exact congrArg State.storage hg
  · show Srt.SameO .mem (M.eval σ) (some σ₁.glob.memT)
    rw [hμ, hg]
    rfl

/-- **`sequentialToParallel` over a memory write**: `{memory := M}{V}` as
one update, `M` substituted for `memory` in `V`; `none` for any other `U`. -/
def Upd.mergeMem? {Γ Δ₁ Δ₂ : Ctx} (U : Upd C Γ Δ₁) (V : Upd C Δ₁ Δ₂) : Option (Upd C Γ Δ₂) :=
  Upd.casesOn (motive := fun Δ₁ U => Upd C Δ₁ Δ₂ → Option (Upd C Γ Δ₂)) U
    (nil := fun _ => none)
    (snoc := fun U e V =>
      Upd.casesOn (motive := fun Δ₁ _ => UpdElem C Γ Δ₁ → Upd C Δ₁ Δ₂ → Option (Upd C Γ Δ₂)) U
        (nil := fun e V => match e with
          | .memory M => (Upd.snoc .nil (.memory M)).graftF
            (Tm.substP (Upd.snoc .nil (.memory M)).held none (some M)) V
          | _ => none)
        (snoc := fun _ _ _ _ => none) (decl := fun _ _ _ _ _ => none)
        (pop := fun _ _ _ _ => none) (drop := fun _ _ _ _ => none) e V)
    (decl := fun _ _ _ _ => none) (pop := fun _ _ _ => none) (drop := fun _ _ _ => none) V

/-- `{W} φ` gives `{memory := M}{V} φ` for the memory merge `W`. -/
theorem holds_upd_mergeMem {m : Modality} {Γ Δ₁ Δ₂ : Ctx} {U : Upd C Γ Δ₁} {V : Upd C Δ₁ Δ₂}
    {W : Upd C Γ Δ₂} (hW : U.mergeMem? V = some W) {φ : Fml C Δ₂} (σ : State C Γ)
    (h : holds σ (.upd m W φ)) : holds σ (.upd m U (.upd m V φ)) := by
  cases U with
  | snoc U e =>
    cases U with
    | nil =>
      cases e with
      | memory M =>
        refine holds_upd_graftF σ (fun g₁ σ₁ hL => ?_) hW h
        obtain ⟨hr, hs, hm⟩ := MemOK.of_memLast (U := Upd.snoc .nil (.memory M)) rfl hL
        exact ⟨fun t _ ht => Tm.substP_eval hL hr hs hm t ht, hr,
          fun t _ ht hx => Tm.substP_exhB hL hr hs hm t ht hx⟩
      | _ => cases hW
    | _ => cases hW
  | _ => cases hW

/-- **`sequentialToParallel` over locals and a memory write**:
`{L ‖ memory := M}{V}` as one update (`Tm.substP`); `none` for any other
`U`. -/
def Upd.mergeMemL? {Γ Δ₁ Δ₂ : Ctx} (U : Upd C Γ Δ₁) (V : Upd C Δ₁ Δ₂) : Option (Upd C Γ Δ₂) :=
  match U.memLast? with
  | some M => U.graftF (Tm.substP U.held none (some M)) V
  | none => none

/-- `{W} φ` gives `{L ‖ memory := M}{V} φ` for the merge `W`. -/
theorem holds_upd_mergeMemL {m : Modality} {Γ Δ₁ Δ₂ : Ctx} {U : Upd C Γ Δ₁} {V : Upd C Δ₁ Δ₂}
    {W : Upd C Γ Δ₂} (hW : U.mergeMemL? V = some W) {φ : Fml C Δ₂} (σ : State C Γ)
    (h : holds σ (.upd m W φ)) : holds σ (.upd m U (.upd m V φ)) := by
  unfold Upd.mergeMemL? at hW
  split at hW
  · rename_i M hm
    refine holds_upd_graftF σ (fun g₁ σ₁ hL => ?_) hW h
    obtain ⟨hr, hs, hm'⟩ := MemOK.of_memLast hm hL
    exact ⟨fun t _ ht => Tm.substP_eval hL hr hs hm' t ht, hr,
      fun t _ ht hx => Tm.substP_exhB hL hr hs hm' t ht hx⟩
  · cases hW

/-! ## The merges at a position -/

/-- The merges, by the write they merge over. -/
inductive MergeNameS where
  | storage
  | memory
  /-- Locals, then a memory write (`Upd.mergeMemL?`). -/
  | localsMemory
  deriving DecidableEq, Repr

/-- Merge `r` on `{U}{V} ψ` under one modality. -/
def MergeNameS.top (r : MergeNameS) {Γ Δ : Ctx} (m : Modality) (U : Upd C Γ Δ) (φ : Fml C Δ) :
    Option (Fml C Γ) :=
  match φ.updHead? with
  | some ⟨m', V, ψ⟩ =>
    if m' = m then
      (match r with
        | .storage => U.mergeSt? V
        | .memory => U.mergeMem? V
        | .localsMemory => U.mergeMemL? V).map fun W => .upd m W ψ
    else none
  | none => none

theorem MergeNameS.top_sound (r : MergeNameS) : UpdRw.Sound (C := C) fun m U φ => r.top m U φ := by
  intro Γ Δ m U φ ψ h σ hψ
  cases φ with
  | upd m' V ψ' =>
    change (if m' = m then
      (match r with
        | .storage => U.mergeSt? V
        | .memory => U.mergeMem? V
        | .localsMemory => U.mergeMemL? V).map fun W => Fml.upd m W ψ'
    else none) = some ψ at h
    split at h
    · rename_i hm; subst hm
      obtain ⟨W, hW, rfl⟩ := Option.map_eq_some_iff.1 h
      cases r with
      | storage => exact holds_upd_mergeSt hW σ hψ
      | memory => exact holds_upd_mergeMem hW σ hψ
      | localsMemory => exact holds_upd_mergeMemL hW σ hψ
    · cases h
  | _ => cases h

/-- Merge `r` at the first update where it fits (`Fml.rwAtS`). -/
def Fml.mergeAtS (r : MergeNameS) {Γ : Ctx} (φ : Fml C Γ) : Option (Fml C Γ) :=
  φ.rwAtS fun m U ψ => r.top m U ψ

/-- A merge where it fits first gives a formula that gives the original. -/
theorem Fml.mergeAtS_sound {r : MergeNameS} {Γ : Ctx} (φ : Fml C Γ) {ψ : Fml C Γ}
    (h : φ.mergeAtS r = some ψ) (σ : State C Γ) (hψ : holds σ ψ) : holds σ φ :=
  Fml.rwAtS_sound r.top_sound φ h σ hψ

/-- A scoped formula is valid where a merge of it is. -/
theorem Valid.of_mergeAtS {r : MergeNameS} {φ ψ : Fml C []} (hr : φ.mergeAtS r = some ψ)
    (h : Valid ψ) : Valid φ :=
  fun σ => Fml.mergeAtS_sound φ hr σ (h σ)

end Solidity
