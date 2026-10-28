import Solidity.Calculus.MemInst

/-!
# Stable typed exterior observations of one fresh primitive array

A proof-carrying supported-shape view of existing intrinsic terms/formulas.
The view has a primitive sort at every node and reifies to `Tm`/`Fml`;
unsupported symbols and binders are refused. Optional observations, including
halted reads and checked operators, are preserved exactly by reconstruction.
-/

namespace Solidity.Decide

variable {C : Contract} {Γ : Ctx} {q p : PrimTy}

inductive MxObs (q : PrimTy) : PrimTy → Type where
  | lit (p : PrimTy) (v : p.Denote) : MxObs q p
  | len : MxObs q .uint
  | read (k : PrimTy.uint.Denote) : MxObs q q
  | binop (op : BinOp) {p : PrimTy} (h : op.accepts p = true)
      (a b : MxObs q p) : MxObs q (op.ret p)

def MxObs.tm : {p : PrimTy} → MxObs q p → Tm C (.mem (.array (.prim q)) :: Γ) (.val p)
  | _, .lit _ v => .app0 (.lit v)
  | _, .len => (MxOrig.len .here).tm
  | _, .read k => .app2 .read (.app0 .memory)
      (.app2 (.mat .dyn) (.pvI .here) (.app0 (.lit k)))
  | _, .binop op h a b => .app2 (.binop op h) a.tm b.tm

def MxObs.reads : {p : PrimTy} → MxObs q p → List PrimTy.uint.Denote
  | _, .lit _ _ | _, .len => []
  | _, .read k => [k]
  | _, .binop _ _ a b => a.reads ++ b.reads

def MxObs.obs {H : HTy} (o : MObj H (.array (.prim q))) : {p : PrimTy} → MxObs q p → Option p.Denote
  | _, .lit _ v => some v
  | _, .len => some (mxFillN .dyn o)
  | _, .read k => (MObj.elems .dyn o)[k.1.toNat]?
  | _, .binop op h a b => (a.obs o).bind fun v => binopT op h v (b.obs o)

/-- Extract a proposed literal key only; the complete read is checked
against its typed reconstruction before accepting it. -/
def mxObsReadKey? {p : PrimTy} : Tm C (.mem (.array (.prim q)) :: Γ) (.val p) →
    Option PrimTy.uint.Denote
  | .app2 .read (.app0 .memory) addr =>
    match mxAt? addr with
    | some ⟨_, (_, _, .app0 (.lit k)), _⟩ => some k
    | _ => none
  | _ => none

def MxObs.atom? {p : PrimTy} (t : Tm C (.mem (.array (.prim q)) :: Γ) (.val p)) :
    Option {a : MxObs q p // t = a.tm} :=
  let len? : Option {a : MxObs q p // t = a.tm} :=
    if hp : p = .uint then
      let l : MxObs q .uint := .len
      if ht : (hp ▸ t).beqR (l.tm (C := C) (Γ := Γ)) = true then
        some ⟨hp.symm ▸ l, by cases hp; exact Tm.eq_of_beqR ht⟩
      else none
    else none
  match len? with
  | some a => some a
  | none =>
    if hp : p = q then
      match mxObsReadKey? t with
      | some k =>
        let a : MxObs q q := .read k
        if ht : (hp ▸ t).beqR (a.tm (C := C) (Γ := Γ)) = true then
          some ⟨hp.symm ▸ a, by cases hp; exact Tm.eq_of_beqR ht⟩
        else none
      | none => none
    else none

/-- Sort-indexed wrapper lets the parser recurse on the existing `Tm`
recursor without a partial or fuel-bounded untyped intermediate. -/
inductive MxObsAt (q : PrimTy) : Srt → Type where
  | val {p : PrimTy} (a : MxObs q p) : MxObsAt q (.val p)

def MxObsAt.tm {s : Srt} : MxObsAt q s → Tm C (.mem (.array (.prim q)) :: Γ) s
  | .val a => a.tm

def mxObsAtomAt? {s : Srt} (t : Tm C (.mem (.array (.prim q)) :: Γ) s) :
    Option {a : MxObsAt q s // t = a.tm} :=
  match s, t with
  | .val _, t => (MxObs.atom? t).map fun ⟨a, ha⟩ => ⟨.val a, ha⟩
  | _, _ => none

def MxObs.parse : {s : Srt} → (t : Tm C (.mem (.array (.prim q)) :: Γ) s) →
    Option {a : MxObsAt q s // t = a.tm}
  | _, .app0 o =>
    match o with
    | .lit v => some ⟨.val (.lit _ v), rfl⟩
    | _ => none
  | _, .app2 (.binop op h) x y => do
      let ⟨.val a, ha⟩ ← MxObs.parse x
      let ⟨.val b, hb⟩ ← MxObs.parse y
      pure ⟨.val (.binop op h a b), by rw [ha, hb]; rfl⟩
  | _, .app2 o x y => mxObsAtomAt? (.app2 o x y)
  | _, _ => none

def MxObs.ofTm? {p : PrimTy} (t : Tm C (.mem (.array (.prim q)) :: Γ) (.val p)) :
    Option {a : MxObs q p // t = a.tm} :=
  (MxObs.parse t).map fun ⟨.val a, ha⟩ => ⟨a, ha⟩

theorem MxObs.eval_alloc (σ : State C Γ) (o : MObj σ.H (.array (.prim q))) :
    {p : PrimTy} → (a : MxObs q p) → a.tm.eval (σ.allocPush o) = a.obs o
  | _, .lit _ _ => rfl
  | _, .len => by
    have hl : (MObj.elems .dyn o).length < 2 ^ 256 := by rw [MObj.elems_dyn]; exact o.2
    simpa only [MxObs.tm, MxObs.obs, mxFillN, uintOfNat_eq_lenU hl] using mxLenNew_eval σ o
  | _, .read k => by
    simpa only [MxObs.tm, MxObs.obs, Tm.wk_app0, Tm.eval, Op0.eval, Option.bind_some] using
      mxReadNew_eval σ o .dyn (.app0 (.lit k)) rfl rfl
  | _, .binop op h a b => by
    change Op2.eval (σ.allocPush o).glob (.binop op h) (a.tm.eval (σ.allocPush o))
      (b.tm.eval (σ.allocPush o)) = _
    rw [a.eval_alloc σ o, b.eval_alloc σ o, Op2.eval_eq_evalM]
    rfl

theorem MxObs.denote_alloc (σ : State C Γ) (o : MObj σ.H (.array (.prim q))) :
    {p : PrimTy} → (a : MxObs q p) → a.tm.denote (σ.allocPush o) = a.obs o
  | _, .lit _ _ => rfl
  | _, .len => by
    change (MxOrig.len .here).tm.denote (σ.allocPush o) = _
    rw [MxOrig.denote_eq]
    exact MxObs.eval_alloc σ o .len
  | _, .read k => by
    change (MxOrig.elem .here .dyn (.app0 (.lit k)) rfl).tm.denote (σ.allocPush o) = _
    rw [MxOrig.denote_eq]
    exact MxObs.eval_alloc σ o (.read k)
  | _, .binop op h a b => by
    change (a.tm.denote (σ.allocPush o)).bind (fun v => binopT op h v (b.tm.denote (σ.allocPush o))) = _
    rw [a.denote_alloc σ o, b.denote_alloc σ o]
    rfl

/-- Stability is proved from the read footprint, not from denote/eval
agreement alone. It includes all optional failures of exterior operators. -/
theorem MxObs.rebuild {H : HTy} (o : MObj H (.array (.prim q))) (B : List Int)
    (hn : ((MObj.elems .dyn o).length : Int) ∈ B) :
    {p : PrimTy} → (a : MxObs q p) → (∀ k ∈ a.reads, k.1 ∈ B) →
      a.obs (mxFloorRebuild .dyn (by trivial) o B) = a.obs o
  | _, .lit _ _, _ => rfl
  | _, .len, _ => congrArg some (mxFloorRebuild_fillN .dyn (by trivial) o B)
  | _, .read k, hr => by
    change (MObj.elems .dyn (mxFloorRebuild .dyn (by trivial) o B))[k.1.toNat]? = _
    apply mxFloorRebuild_at .dyn (by trivial) o B hn
    have h0 := mxUint_nonneg k
    have hk := hr k (List.mem_singleton_self k)
    have he : (k.1.toNat : Int) = k.1 := by omega
    rw [he]
    exact hk
  | _, .binop op h a b, hr => by
    change (a.obs (mxFloorRebuild .dyn (by trivial) o B)).bind
      (fun v => binopT op h v (b.obs (mxFloorRebuild .dyn (by trivial) o B))) = _
    rw [a.rebuild o B hn (fun k hk => hr k (List.mem_append_left _ hk)),
      b.rebuild o B hn (fun k hk => hr k (List.mem_append_right _ hk))]
    rfl

inductive MxExterior (q : PrimTy) where
  | tt
  | eq {p : PrimTy} (a b : MxObs q p)
  | not (a : MxExterior q)
  | and (a b : MxExterior q)
  | imp (a b : MxExterior q)

def MxExterior.fml : MxExterior q → Fml C (.mem (.array (.prim q)) :: Γ)
  | .tt => .tt
  | .eq a b => .eq a.tm b.tm
  | .not a => .not a.fml
  | .and a b => .and a.fml b.fml
  | .imp a b => .imp a.fml b.fml

def MxExterior.reads : MxExterior q → List PrimTy.uint.Denote
  | .tt => []
  | .eq a b => a.reads ++ b.reads
  | .not a => a.reads
  | .and a b | .imp a b => a.reads ++ b.reads

def MxExterior.obs {H : HTy} (o : MObj H (.array (.prim q))) : MxExterior q → Prop
  | .tt => True
  | .eq a b => a.obs o = b.obs o
  | .not a => ¬ a.obs o
  | .and a b => a.obs o ∧ b.obs o
  | .imp a b => a.obs o → b.obs o

def MxExterior.ofFml? : (φ : Fml C (.mem (.array (.prim q)) :: Γ)) →
    Option {a : MxExterior q // φ = a.fml}
  | .tt => some ⟨.tt, rfl⟩
  | .eq a b => do
    let ⟨a', ha⟩ ← MxObs.ofTm? a
    let ⟨b', hb⟩ ← MxObs.ofTm? b
    pure ⟨.eq a' b', by rw [ha, hb]; rfl⟩
  | .not a => do
    let ⟨a', ha⟩ ← MxExterior.ofFml? a
    pure ⟨.not a', by rw [ha]; rfl⟩
  | .and a b => do
    let ⟨a', ha⟩ ← MxExterior.ofFml? a
    let ⟨b', hb⟩ ← MxExterior.ofFml? b
    pure ⟨.and a' b', by rw [ha, hb]; rfl⟩
  | .imp a b => do
    let ⟨a', ha⟩ ← MxExterior.ofFml? a
    let ⟨b', hb⟩ ← MxExterior.ofFml? b
    pure ⟨.imp a' b', by rw [ha, hb]; rfl⟩
  | _ => none

theorem MxExterior.holds_alloc (σ : State C Γ) (o : MObj σ.H (.array (.prim q))) :
    (a : MxExterior q) → (holds (σ.allocPush o) a.fml ↔ a.obs o)
  | .tt => Iff.rfl
  | .eq a b => by change a.tm.denote _ = b.tm.denote _ ↔ _; rw [a.denote_alloc σ o, b.denote_alloc σ o]; rfl
  | .not a => not_congr (a.holds_alloc σ o)
  | .and a b => and_congr (a.holds_alloc σ o) (b.holds_alloc σ o)
  | .imp a b => imp_congr (a.holds_alloc σ o) (b.holds_alloc σ o)

theorem MxExterior.rebuild {H : HTy} (o : MObj H (.array (.prim q))) (B : List Int)
    (hn : ((MObj.elems .dyn o).length : Int) ∈ B) :
    (a : MxExterior q) → (∀ k ∈ a.reads, k.1 ∈ B) →
      (a.obs (mxFloorRebuild .dyn (by trivial) o B) ↔ a.obs o)
  | .tt, _ => Iff.rfl
  | .eq a b, hr => by
    change a.obs _ = b.obs _ ↔ _
    rw [a.rebuild o B hn (fun k hk => hr k (List.mem_append_left _ hk)),
      b.rebuild o B hn (fun k hk => hr k (List.mem_append_right _ hk))]
    rfl
  | .not a, hr => not_congr (a.rebuild o B hn hr)
  | .and a b, hr => and_congr
      (a.rebuild o B hn (fun k hk => hr k (List.mem_append_left _ hk)))
      (b.rebuild o B hn (fun k hk => hr k (List.mem_append_right _ hk)))
  | .imp a b, hr => imp_congr
      (a.rebuild o B hn (fun k hk => hr k (List.mem_append_left _ hk)))
      (b.rebuild o B hn (fun k hk => hr k (List.mem_append_right _ hk)))

#print axioms MxExterior.rebuild
#print axioms MxExterior.holds_alloc

end Solidity.Decide
