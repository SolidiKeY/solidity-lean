import Solidity.Evm.MemoryObjectAllocationCost

/-! Narrow construction certificates over complete typed object ownership. -/
namespace Solidity.Evm.Memory.Construction
open Objects
variable {C : Contract}

inductive StmtFrag (b : Nat) : {Γ Δ : Ctx} → Frag Γ → Frag Δ → Stmt C Γ Δ → List Instr → Prop where
  | old {Γ Δ : Ctx} {F : Frag Γ} {G : Frag Δ} {s : Stmt C Γ Δ} {code : List Instr}
      (hs : Objects.StmtFrag b F G s code) : StmtFrag b F G s code
  | empty {Γ : Ctx} (F : Frag Γ) (E : Ty) (x : Var) (hd hm) (hb : 0 < b) :
      StmtFrag b F (F.push (.mem (.array E)) .ok) (.declMem (.array E) x none hd hm)
        ([.push w[0]] ++ allocateArrayCode ++ [.mstore (cell (b + Γ.length))])
  | primitive {Γ : Ctx} (F : Frag Γ) (p : PrimTy) (x : Var) (n : Simple C Γ .uint)
      (hb : 0 < b) (hn : simpleIn n = true) :
      StmtFrag b F (F.push (.mem (.array (.prim p))) .ok)
        (.declMem (.array (.prim p)) x (some (.newArr n rfl)) rfl rfl) (declareNewCode b n)
  | reprimitive {Γ : Ctx} (F : Frag Γ) (p : PrimTy) (dst : Idx Γ (.mem (.array (.prim p))))
      (n : Simple C Γ .uint) (hb : 0 < b) (hn : simpleIn n = true) :
      StmtFrag b F F (.rebindMem dst (.newArr n rfl)) (rebindNewCode b dst n)
  | nested {Γ : Ctx} (F : Frag Γ) (E : Ty) (x : Var) (n : Simple C Γ .uint)
      (hb : 0 < b) (hns : simpleIn n = true) (hn : (RefTy.array (.ref (.array E))).newArrOk = true)
      (hm : (Ty.ref (.array E)).mapFree = true) :
      StmtFrag b F (F.push (.mem (.array (.ref (.array E)))) .ok)
        (.declMem (.array (.ref (.array E))) x (some (.newArr n hn)) rfl
          (RefTy.mapFree_of_newArrOk hn)) (nestedDeclareCode b n)
  | renested {Γ : Ctx} (F : Frag Γ) (E : Ty) (dst : Idx Γ (.mem (.array (.ref (.array E)))) )
      (n : Simple C Γ .uint) (hb : 0 < b) (hns : simpleIn n = true)
      (hn : (RefTy.array (.ref (.array E))).newArrOk = true) (hm : (Ty.ref (.array E)).mapFree = true) :
      StmtFrag b F F (.rebindMem dst (.newArr n hn)) (nestedRebindCode b dst n)

  | newEmpty {Γ : Ctx} (F : Frag Γ) (E : Ty) (x : Var)
      (hn : (RefTy.array E).newArrOk = true) (hm : (Ty.ref (.array E)).mapFree = true) (hb : 0 < b) :
      StmtFrag b F (F.push (.mem (.array E)) .ok)
        (.declMem (.array E) x (some (.newArr (.lit 0 rfl) hn)) rfl hm)
        ([.push w[0]] ++ allocateArrayCode ++ [.mstore (cell (b + Γ.length))])
  | reEmpty {Γ : Ctx} (F : Frag Γ) (E : Ty) (dst : Idx Γ (.mem (.array E)))
      (hn : (RefTy.array E).newArrOk = true) (hb : 0 < b) :
      StmtFrag b F F (.rebindMem dst (.newArr (.lit 0 rfl) hn))
        ([.push w[0]] ++ allocateArrayCode ++ [.mstore (cellOf b dst)])

inductive ProgFrag (b : Nat) : {Γ Δ : Ctx} → Frag Γ → Frag Δ → Prog C Γ Δ → List Instr → Prop where
  | nil {Γ : Ctx} (F : Frag Γ) : ProgFrag b F F .nil []
  | cons {Γ Δ Ξ : Ctx} {F : Frag Γ} {G : Frag Δ} {K : Frag Ξ}
      {s : Stmt C Γ Δ} {P : Prog C Δ Ξ} {head tail : List Instr}
      (hs : StmtFrag b F G s head) (hp : ProgFrag b G K P tail) :
      ProgFrag b F K (.cons s P) (head ++ tail)

structure CompiledStmt (b : Nat) {Γ Δ : Ctx} (F : Frag Γ) (s : Stmt C Γ Δ) where
  frag : Frag Δ
  code : List Instr
  cert : StmtFrag b F frag s code

structure CompiledProg (b : Nat) {Γ Δ : Ctx} (F : Frag Γ) (P : Prog C Γ Δ) where
  frag : Frag Δ
  code : List Instr
  cert : ProgFrag b F frag P code

def compileStmt (b : Nat) {Γ Δ : Ctx} (F : Frag Γ) (s : Stmt C Γ Δ) :
    Option (CompiledStmt b F s) :=
  match Objects.compileStmt b F s with
  | some r => some ⟨r.frag, r.code, .old r.cert⟩
  | none => if hb : 0 < b then
    match s with
    | .declMem (.array E) x none hd hm => some ⟨_, _, .empty F E x hd hm hb⟩
    | .declMem (.array (.prim p)) x (some (.newArr n _)) _ _ =>
      if hn : simpleIn n = true then some ⟨_, _, .primitive F p x n hb hn⟩ else none
    | .rebindMem (R := .array (.prim p)) dst (.newArr n _) =>
      if hn : simpleIn n = true then some ⟨_, _, .reprimitive F p dst n hb hn⟩ else none
    | .declMem (.array (.ref (.array E))) x (some (.newArr n hn)) _ hm =>
      if hns : simpleIn n = true then
        some ⟨_, _, .nested F E x n hb hns hn (by simpa only [Ty.mapFree] using hm)⟩ else none
    | .rebindMem (R := .array (.ref (.array E))) dst (.newArr n hn) =>
      if hns : simpleIn n = true then
        some ⟨_, _, .renested F E dst n hb hns hn (by
          simpa only [Ty.mapFree] using RefTy.mapFree_of_newArrOk hn)⟩ else none
    | .declMem (.array E) x (some (.newArr (.lit 0 _) hn)) _ hm =>
      some ⟨_, _, .newEmpty F E x hn hm hb⟩
    | .rebindMem (R := .array E) dst (.newArr (.lit 0 _) hn) =>
      some ⟨_, _, .reEmpty F E dst hn hb⟩
    | _ => none
    else none

def compileProg (b : Nat) {Γ Δ : Ctx} (F : Frag Γ) :
    (P : Prog C Γ Δ) → Option (CompiledProg b F P)
  | .nil => some ⟨F, [], .nil F⟩
  | .cons s P => do
    let head ← compileStmt b F s
    let tail ← compileProg b head.frag P
    pure ⟨tail.frag, _, .cons head.cert tail.cert⟩

private theorem old_cost_zero {b : Nat} {Γ Δ : Ctx} {F : Frag Γ} {G : Frag Δ}
    {s : Stmt C Γ Δ} {code : List Instr} (hs : Objects.StmtFrag b F G s code) (σ : State C Γ) :
    allocationCostStmt s σ = 0 := by
  cases hs with
  | @alias F R x src code hs hm =>
    exact allocationCostStmt_zero _ (by cases R <;> rfl) σ
  | rebind => rfl
  | write => rfl
  | assign => rfl
  | declare => rfl

theorem StmtFrag.correct {b L frame : Nat} {Γ Δ : Ctx} {F : Frag Γ} {G : Frag Δ}
    {s : Stmt C Γ Δ} {code : List Instr} (hs : StmtFrag b F G s code)
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
    (h : Objects.StateRepr L b frame F σ base m) (hcap : b + frameNeedStmt s ≤ frame)
    (ha : Objects.AllocationInput b frame (allocationCostStmt s σ) σ base m) :
    Objects.GrowingResult L b frame (allocationCostStmt s σ) G σ base m (s.run σ) (run code m) := by
  cases hs with
  | old hs => rw [old_cost_zero hs]; exact (hs.correct h hcap).growing
  | empty F E x hd hm hb =>
    rcases ha with hz | ⟨_, cursor, hal, hspace⟩
    · change 1 = 0 at hz; cases hz
    · have hspace' : cursor.val + 1 < W := hspace
      have cap : b + (Γ.length + 1) ≤ frame := by
        change b + max Γ.length (max (Γ.length + 1) 0) ≤ frame at hcap
        omega
      have hn := Objects.defaultEmpty_correct h hal hb E hm hspace' cap
      refine .inl ⟨⟨σ.allocPush (emptyArray E), List.prefix_append _ _⟩, _,
        upd base σ.H.length cursor, hn.1, hn.2.1, hn.2.2.1, hn.2.2.2.2,
        (fun r => allocationBase_old base cursor r), ?_⟩
      intro c _ hc hcspace
      have he : c = cursor := Word.val.inj (hc.free.cell.symm.trans hal.free.cell)
      subst c
      exact hn.2.2.2.1
  | primitive F p x n hb hn =>
    rcases ha with hz | ⟨_, cursor, hal, hspace⟩
    · change (n.evalT σ).word.val + 1 = 0 at hz
      omega
    · have hs : n.evalT σ = indexValue (n.evalT σ).word :=
        Subtype.ext (word_val (n.evalT σ)).symm
      have hspace' : cursor.val + (n.evalT σ).word.val + 1 < W := by
        change cursor.val + ((n.evalT σ).word.val + 1) < W at hspace
        omega
      have cap : b + (Γ.length + 1) ≤ frame := by
        change b + max Γ.length (max (Γ.length + 1) 0) ≤ frame at hcap
        omega
      have hn' := Objects.primitiveDeclare_correct h hal hb p n hn (n.evalT σ).word hs hspace' cap
      refine .inl ⟨⟨_, List.prefix_append _ _⟩, _, upd base σ.H.length cursor,
        hn'.1, hn'.2.1, hn'.2.2.1, hn'.2.2.2.2,
        (fun r => allocationBase_old base cursor r), ?_⟩
      intro c _ hc hcspace
      have he : c = cursor := Word.val.inj (hc.free.cell.symm.trans hal.free.cell)
      subst c
      simpa only [Nat.add_assoc] using hn'.2.2.2.1
  | reprimitive F p dst n hb hn =>
    rcases ha with hz | ⟨_, cursor, hal, hspace⟩
    · change (n.evalT σ).word.val + 1 = 0 at hz
      omega
    · have hs : n.evalT σ = indexValue (n.evalT σ).word :=
        Subtype.ext (word_val (n.evalT σ)).symm
      have hspace' : cursor.val + (n.evalT σ).word.val + 1 < W := by
        change cursor.val + ((n.evalT σ).word.val + 1) < W at hspace
        omega
      have hn' := Objects.primitiveRebind_correct h hal hb p dst n hn (n.evalT σ).word hs hspace'
      refine .inl ⟨⟨_, List.prefix_append _ _⟩, _, upd base σ.H.length cursor,
        hn'.1, hn'.2.1, hn'.2.2.1, hn'.2.2.2.2,
        (fun r => allocationBase_old base cursor r), ?_⟩
      intro c _ hc hcspace
      have he : c = cursor := Word.val.inj (hc.free.cell.symm.trans hal.free.cell)
      subst c
      simpa only [Nat.add_assoc] using hn'.2.2.2.1
  | nested F E x n hb hns hn hm =>
    rcases ha with hz | ⟨_, cursor, hal, hspace⟩
    · change (n.evalT σ).word.val + 1 + (n.evalT σ).word.val = 0 at hz
      omega
    · have hs : n.evalT σ = indexValue (n.evalT σ).word :=
        Subtype.ext (word_val (n.evalT σ)).symm
      have hspace' : cursor.val + (n.evalT σ).word.val + 1 + (n.evalT σ).word.val < W := by
        change cursor.val + ((n.evalT σ).word.val + 1 + (n.evalT σ).word.val) < W at hspace
        omega
      have cap : b + (Γ.length + 1) ≤ frame := by
        change b + max Γ.length (max (Γ.length + 1) 0) ≤ frame at hcap
        omega
      obtain ⟨base', m', ho, hc, hm', hal', hex, hst⟩ := Objects.nestedDeclare_correct h hal hb E n hns hn hm (n.evalT σ).word hs hspace' cap
      refine .inl ⟨⟨_, (nestedCopy σ.heap E hm (n.evalT σ).word).ext⟩, m', base',
        ho, hc, hm', hst, hex, ?_⟩
      intro c _ hc hcspace
      have he : c = cursor := Word.val.inj (hc.free.cell.symm.trans hal.free.cell)
      subst c
      simpa only [allocationCostStmt, hasAllocationStmt, rawAllocationCostStmt, arrayCost, if_true, Nat.add_assoc] using hal'
  | renested F E dst n hb hns hn hm =>
    rcases ha with hz | ⟨_, cursor, hal, hspace⟩
    · change (n.evalT σ).word.val + 1 + (n.evalT σ).word.val = 0 at hz
      omega
    · have hs : n.evalT σ = indexValue (n.evalT σ).word :=
        Subtype.ext (word_val (n.evalT σ)).symm
      have hspace' : cursor.val + (n.evalT σ).word.val + 1 + (n.evalT σ).word.val < W := by
        change cursor.val + ((n.evalT σ).word.val + 1 + (n.evalT σ).word.val) < W at hspace
        omega
      obtain ⟨base', m', ho, hc, hm', hal', hex, hst⟩ := Objects.nestedRebind_correct h hal hb E dst n hns hn hm (n.evalT σ).word hs hspace'
      refine .inl ⟨⟨_, (nestedCopy σ.heap E hm (n.evalT σ).word).ext⟩, m', base',
        ho, hc, hm', hst, hex, ?_⟩
      intro c _ hc hcspace
      have he : c = cursor := Word.val.inj (hc.free.cell.symm.trans hal.free.cell)
      subst c
      simpa only [allocationCostStmt, hasAllocationStmt, rawAllocationCostStmt, arrayCost, if_true, Nat.add_assoc] using hal'
  | newEmpty F E x hn hm hb =>
    have hcost : allocationCostStmt (.declMem (.array E) x (some (.newArr (.lit 0 rfl) hn)) rfl hm) σ = 1 := by
      change arrayCost E 0 = 1
      exact arrayCost_zero E
    rw [hcost] at ha ⊢
    rcases ha with hz | ⟨_, cursor, hal, hspace⟩
    · cases hz
    · have cap : b + (Γ.length + 1) ≤ frame := by
        change b + max Γ.length (max (Γ.length + 1) 0) ≤ frame at hcap
        omega
      have hr := Objects.newEmpty_correct h hal hb E hn hm hspace cap
      refine .inl ⟨⟨_, List.prefix_append _ _⟩, _, upd base σ.H.length cursor,
        hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.2, (fun r => allocationBase_old base cursor r), ?_⟩
      intro c _ hc hcspace
      have he : c = cursor := Word.val.inj (hc.free.cell.symm.trans hal.free.cell)
      subst c
      exact hr.2.2.2.1
  | reEmpty F E dst hn hb =>
    have hcost : allocationCostStmt (.rebindMem dst (.newArr (.lit 0 rfl) hn)) σ = 1 := by
      change arrayCost E 0 = 1
      exact arrayCost_zero E
    rw [hcost] at ha ⊢
    rcases ha with hz | ⟨_, cursor, hal, hspace⟩
    · cases hz
    · have hr := Objects.rebindEmpty_correct h hal hb E dst hn hspace
      refine .inl ⟨⟨_, List.prefix_append _ _⟩, _, upd base σ.H.length cursor,
        hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.2, (fun r => allocationBase_old base cursor r), ?_⟩
      intro c _ hc hcspace
      have he : c = cursor := Word.val.inj (hc.free.cell.symm.trans hal.free.cell)
      subst c
      exact hr.2.2.2.1

private theorem run_cons_revert {Γ Δ Ξ : Ctx} {σ : State C Γ}
    {s : Stmt C Γ Δ} {P : Prog C Δ Ξ} (h : s.run σ = .error .revert) :
    (Prog.cons s P).run σ = .error .revert := by
  show TRun.seq s.runR P.runR σ = _
  simp only [TRun.seq, Solidity.Stmt.run] at h ⊢
  rw [h]

theorem ProgFrag.correct {b L frame : Nat} {Γ Δ : Ctx} {F : Frag Γ} {G : Frag Δ}
    {P : Prog C Γ Δ} {code : List Instr} (hp : ProgFrag b F G P code)
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
    (h : Objects.StateRepr L b frame F σ base m) (hcap : b + frameNeedProg P ≤ frame)
    (ha : Objects.AllocationInput b frame (allocationCostProg P σ) σ base m) :
    Objects.GrowingResult L b frame (allocationCostProg P σ) G σ base m (P.run σ) (run code m) := by
  induction hp generalizing base m with
  | nil F => exact .inl ⟨⟨σ, List.prefix_refl _⟩, m, base, rfl, rfl, h, rfl,
      BaseExtends.refl _, fun _ _ ha _ => ha⟩
  | @cons Γ Δ Ξ F G K s P head tail hs hp ih =>
    have hcaps : b + frameNeedStmt s ≤ frame := by
      change b + max (frameNeedStmt s) (frameNeedProg P) ≤ frame at hcap
      omega
    have hcapp : b + frameNeedProg P ≤ frame := by
      change b + max (frameNeedStmt s) (frameNeedProg P) ≤ frame at hcap
      omega
    have hah : Objects.AllocationInput b frame (allocationCostStmt s σ) σ base m :=
      ha.of_le (by rw [allocationCostProg_cons]; exact Nat.le_add_right _ _)
    rcases hs.correct h hcaps hah with ⟨o, m₁, base₁, ho, hc, hm, hst, hex, hal⟩ | ⟨ho, hc⟩
    · rw [Solidity.Prog.run_cons_ok ho, run_append_ok hc]
      have hcost : allocationCostProg (.cons s P) σ = allocationCostStmt s σ + allocationCostProg P o.st := by
        rw [allocationCostProg_cons, ho]
      have hat : Objects.AllocationInput b frame (allocationCostProg P o.st) o.st base₁ m₁ :=
        hal.nextInput (hcost ▸ ha)
      rcases ih hm hcapp hat with ⟨o', m₂, base₂, ho', hc', hm', hst', hex', hal'⟩ | ⟨ho', hc'⟩
      · refine .inl ⟨⟨o'.st, o.ext.trans o'.ext⟩, m₂, base₂,
          by rw [ho']; rfl, hc', hm', hst'.trans hst, hex.trans o.ext hex', ?_⟩
        rw [hcost]
        exact hal.comp hal'
      · exact .inr ⟨by rw [ho']; rfl, hc'⟩
    · exact .inr ⟨run_cons_revert ho, run_append_revert hc⟩

theorem StmtFrag.pushes_zero {b : Nat} {Γ Δ : Ctx} {F : Frag Γ} {G : Frag Δ}
    {s : Stmt C Γ Δ} {code : List Instr} (hs : StmtFrag b F G s code) : Evm.Stmt.pushes s = 0 := by
  cases hs <;> first | rfl | (rename_i hs; cases hs <;> rfl)

theorem ProgFrag.pushes_zero {b : Nat} {Γ Δ : Ctx} {F : Frag Γ} {G : Frag Δ}
    {P : Prog C Γ Δ} {code : List Instr} (hp : ProgFrag b F G P code) : Evm.Prog.pushes P = 0 := by
  induction hp with
  | nil => rfl
  | cons hs hp ih => exact Nat.add_eq_zero.mpr ⟨hs.pushes_zero, ih⟩

end Solidity.Evm.Memory.Construction
