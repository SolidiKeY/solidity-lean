import Solidity.Evm.Compiler

/-! # Compiler success (totality) of the public compiler on a stated domain

H62 (2)/H69 ask for a separate totality theorem: a compiler that rejects
everything must not satisfy the public statements. The public compiler entry
is `Solidity.Evm.Compiler.compile`; its fixed observation is
`Compilation.Agrees` (typed state and stack on success, a data-free machine
`revert` for source revert/panic/payment refusal, fault on divergence).

The domain is stated here as inductive predicates over the intrinsic syntax.
They mention no compiler function, no fragment (`Frag`) and no compile result:
alias-free scalar programs over locals and storage locations, with branches,
blocks, loops and single-value internal calls. Each side condition records an
actual gap of the compiler, not a success filter:

* `env` excludes `address(this).balance` (`simpleIn`);
* `binop` excludes `&`, `|`, `^` at `int` (typed, but not in `binInFrag`);
* mapping keys are `uint` and a fixed array or struct offset fits a word.

`compile_core` proves every program of the domain is compiled, from every
fragment and base, by the core branch; `compile_agrees` composes it with the
existing `Compilation.correct`. No statement, premise or observation of the
compiler is changed. -/
namespace Solidity.Backend.AbiWorld.PublicCompilerTotal
open Solidity.Evm

variable {C : Contract}

/-! ## The domain -/

mutual
/-- An alias-free storage path. -/
inductive PathOk {Γ : Ctx} : {T : Ty} → Solidity.SPath C Γ T → Prop
  | loc {T : Ty} {l : Solidity.Loc C Γ T} : LocOk l → PathOk (.loc l)

/-- An alias-free storage location. -/
inductive LocOk {Γ : Ctx} : {T : Ty} → Solidity.Loc C Γ T → Prop
  | root {T : Ty} (r : Name) (h : C.rootType r = some T) : LocOk (.root r h)
  | field {s : Name} {T : Ty} {b : Solidity.SPath C Γ (.ref (.struct s))} (f : Name)
      (h : C.fieldType s f = some T) (fits : offset s f < W) : PathOk b → LocOk (.field b f h)
  | map {V : Ty} {b : Solidity.SPath C Γ (.ref (.mapping .uint V))}
      {i : Solidity.Val C Γ .uint} : PathOk b → ValOk i → LocOk (.index .map b i)
  | dyn {E : Ty} {b : Solidity.SPath C Γ (.ref (.array E))} {i : Solidity.Val C Γ .uint} :
      PathOk b → ValOk i → LocOk (.index (.arr .dyn) b i)
  | fixed {E : Ty} {n : Nat} {b : Solidity.SPath C Γ (.ref (.fixed E n))}
      {i : Solidity.Val C Γ .uint} (fits : n < W) :
      PathOk b → ValOk i → LocOk (.index (.arr .fixed) b i)

/-- A scalar value of the domain. -/
inductive ValOk {Γ : Ctx} : {p : PrimTy} → Solidity.Val C Γ p → Prop
  | lit {p : PrimTy} (n : Int) (h : p.inRange n = true) : ValOk (.simple (.lit n h))
  | bool (v : Bool) : ValOk (.simple (.bool v))
  | local {p : PrimTy} (i : Idx Γ (.val p)) : ValOk (.simple (.local i))
  | env {p : PrimTy} (k : EnvKey) (hp : p = .uint) (hk : k ≠ .selfBalance) :
      ValOk (.simple (.env k hp))
  | read {p : PrimTy} {l : Solidity.Loc C Γ (.prim p)} : LocOk l → ValOk (.read l)
  | binop {p q : PrimTy} (op : BinOp) (h : op.accepts p = true) (hq : op.ret p = q)
      {a b : Solidity.Val C Γ p}
      (signedBitwise : ¬ (p = .int ∧ (op = .band ∨ op = .bor ∨ op = .bxor))) :
      ValOk a → ValOk b → ValOk (.binop op h hq a b)
  | unop {p q : PrimTy} (op : UnOp) (h : op.accepts p = true) (hq : op.ret p = q)
      {a : Solidity.Val C Γ p} : ValOk a → ValOk (.unop op h hq a)
  | ternary {p : PrimTy} {c : Solidity.Val C Γ .bool} {a b : Solidity.Val C Γ p} :
      ValOk c → ValOk a → ValOk b → ValOk (.ternary c a b)
  | len {p : PrimTy} {E : Ty} {b : Solidity.SPath C Γ (.array E)} (hp : p = .uint) :
      PathOk b → ValOk (.len b hp)
end

/-- Value arguments of the domain. -/
inductive ArgsOk {Γ : Ctx} : {ps : Ctx} → Solidity.Args C Γ ps → Prop
  | nil : ArgsOk .nil
  | snoc {ps : Ctx} {as : Solidity.Args C Γ ps} (p : PrimTy) (x : Var)
      {e : Solidity.Val C Γ p} : ArgsOk as → ValOk e → ArgsOk (.snoc as p x e)

mutual
/-- A statement of the domain. -/
inductive StmtOk : {Γ Γ' : Ctx} → Solidity.Stmt C Γ Γ' → Prop
  | assign {Γ : Ctx} {p : PrimTy} {l : Solidity.Loc C Γ (.prim p)} {v : Solidity.Val C Γ p} :
      LocOk l → ValOk v → StmtOk (.assign l (.val v))
  | assignLocal {Γ : Ctx} {p : PrimTy} (i : Idx Γ (.val p)) {v : Solidity.Val C Γ p} :
      ValOk v → StmtOk (.assignLocal i v)
  | declNone {Γ : Ctx} (p : PrimTy) (x : Var) : StmtOk (Γ := Γ) (.declLocal p x none)
  | declSome {Γ : Ctx} (p : PrimTy) (x : Var) {v : Solidity.Val C Γ p} :
      ValOk v → StmtOk (.declLocal p x (some v))
  | opAssign {Γ : Ctx} {p : PrimTy} (op : BinOp) (hop : op.hasCompoundAssign = true)
      (hp : p.isNumeric = true) (i : Idx Γ (.val p)) {v : Solidity.Val C Γ p} :
      ValOk v → StmtOk (.opAssign op hop hp (.local i) v)
  | incDec {Γ : Ctx} {p : PrimTy} (op : IncDec) (hp : p.isNumeric = true) (i : Idx Γ (.val p)) :
      StmtOk (.incDec op hp (.local i))
  | require {Γ : Ctx} {c : Solidity.Val C Γ .bool} : ValOk c → StmtOk (.require c)
  | assert {Γ : Ctx} {c : Solidity.Val C Γ .bool} : ValOk c → StmtOk (.assert c)
  | revert {Γ : Ctx} : StmtOk (Γ := Γ) .revert
  | ite {Γ Γ₁ Γ₂ : Ctx} {c : Solidity.Val C Γ .bool} {t : Solidity.Prog C Γ Γ₁}
      {e : Solidity.Prog C Γ Γ₂} : ValOk c → ProgOk t → ProgOk e → StmtOk (.ite c t e)
  | block {Γ Γ₁ : Ctx} {body : Solidity.Prog C Γ Γ₁} : ProgOk body → StmtOk (.block body)
  | loop {Γ Γ₁ : Ctx} (a : LoopAnn C Γ) {c : Solidity.Val C Γ .bool}
      {body : Solidity.Prog C Γ Γ₁} : ValOk c → ProgOk body → StmtOk (.loop a c body)
  | callNone {Γ ps Γf : Ctx} (f : Name) {args : Solidity.Args C Γ ps}
      {body : Solidity.Prog C ([] ++ ps) Γf} :
      ArgsOk args → ProgOk body → StmtOk (.call f args .none body)
  | callVal {Γ ps Γf : Ctx} (f : Name) (p : PrimTy) (r : Var) (res : Option (Idx Γ (.val p)))
      {args : Solidity.Args C Γ ps} {body : Solidity.Prog C ([.val p] ++ ps) Γf} :
      ArgsOk args → ProgOk body → StmtOk (.call f args (.val p r res) body)

/-- A program of the domain. -/
inductive ProgOk : {Γ Γ' : Ctx} → Solidity.Prog C Γ Γ' → Prop
  | nil {Γ : Ctx} : ProgOk (Γ := Γ) .nil
  | cons {Γ Γ₁ Γ₂ : Ctx} {s : Solidity.Stmt C Γ Γ₁} {P : Solidity.Prog C Γ₁ Γ₂} :
      StmtOk s → ProgOk P → ProgOk (.cons s P)
end


/-! ## Values are accepted from every fragment -/

/-- The typed binary operators the domain admits are the compiled ones. -/
theorem binInFrag_of {op : BinOp} {p : PrimTy} (h : op.accepts p = true)
    (signedBitwise : ¬ (p = .int ∧ (op = .band ∨ op = .bor ∨ op = .bxor))) :
    binInFrag op p = true := by
  revert h signedBitwise
  cases op <;> cases p <;> decide

/-- Every typed unary operator is compiled. -/
theorem unInFrag_of {op : UnOp} {p : PrimTy} (h : op.accepts p = true) :
    unInFrag op p = true := by
  revert h
  cases op <;> cases p <;> decide

mutual
theorem PathOk.spathIn {Γ : Ctx} (F : Frag Γ) : {T : Ty} → {q : Solidity.SPath C Γ T} →
    PathOk q → spathIn F false q = true
  | _, _, .loc h => by simp only [Evm.spathIn, h.locIn F]

theorem LocOk.locIn {Γ : Ctx} (F : Frag Γ) : {T : Ty} → {l : Solidity.Loc C Γ T} →
    LocOk l → locIn F false l = true
  | _, _, .root _ _ => by simp only [Evm.locIn]
  | _, _, .field _ _ fits hb => by
    simp only [Evm.locIn, decide_eq_true fits, hb.spathIn F, Bool.and_self]
  | _, _, .map hb hi => by
    simp only [Evm.locIn, hb.spathIn F, hi.valIn F, Bool.and_self, beq_self_eq_true]
  | _, _, .dyn hb hi => by
    simp only [Evm.locIn, hb.spathIn F, hi.valIn F, Bool.and_self, Bool.not_false]
  | _, _, .fixed fits hb hi => by
    simp only [Evm.locIn, decide_eq_true fits, hb.spathIn F, hi.valIn F, Bool.and_self,
      Bool.not_false]

theorem ValOk.valIn {Γ : Ctx} (F : Frag Γ) : {p : PrimTy} → {v : Solidity.Val C Γ p} →
    ValOk v → valIn F v = true
  | _, _, .lit _ _ => by simp only [Evm.valIn, simpleIn]
  | _, _, .bool _ => by simp only [Evm.valIn, simpleIn]
  | _, _, .local _ => by simp only [Evm.valIn, simpleIn]
  | _, _, .env _ _ hk => by simp only [Evm.valIn, simpleIn, bne_iff_ne, ne_eq, hk, not_false_eq_true]
  | _, _, .read hl => by simp only [Evm.valIn, hl.locIn F]
  | _, _, .binop _ h _ sb ha hb => by
    simp only [Evm.valIn, binInFrag_of h sb, ha.valIn F, hb.valIn F, Bool.and_self]
  | _, _, .unop _ h _ ha => by simp only [Evm.valIn, unInFrag_of h, ha.valIn F, Bool.and_self]
  | _, _, .ternary hc ha hb => by
    simp only [Evm.valIn, hc.valIn F, ha.valIn F, hb.valIn F, Bool.and_self]
  | _, _, .len _ hb => by simp only [Evm.valIn, hb.spathIn F]
end

theorem ArgsOk.argsIn {Γ : Ctx} (F : Frag Γ) : {ps : Ctx} → {as : Solidity.Args C Γ ps} →
    ArgsOk as → argsIn F as = true
  | _, _, .nil => by simp only [Evm.argsIn]
  | _, _, .snoc _ _ ha he => by simp only [Evm.argsIn, ha.argsIn F, he.valIn F, Bool.and_self]

/-! ## Programs push, pay and shrink nothing -/

mutual
theorem StmtOk.quiet : {Γ Γ' : Ctx} → {s : Solidity.Stmt C Γ Γ'} → StmtOk s →
    Stmt.pushes s = 0 ∧ Stmt.pays s = false ∧ Stmt.shrinks s = false
  | _, _, _, .assign _ _ | _, _, _, .assignLocal _ _ | _, _, _, .declNone _ _
  | _, _, _, .declSome _ _ _ | _, _, _, .opAssign _ _ _ _ _ | _, _, _, .incDec _ _ _
  | _, _, _, .require _ | _, _, _, .assert _ | _, _, _, .revert =>
    by simp only [Stmt.pushes, Stmt.pays, Stmt.shrinks, and_self]
  | _, _, _, .ite _ ht he => by
    have t := ht.quiet
    have e := he.quiet
    simp only [Stmt.pushes, Stmt.pays, Stmt.shrinks, t.1, t.2.1, t.2.2, e.1, e.2.1, e.2.2,
      Nat.add_zero, Bool.or_self, and_self]
  | _, _, _, .block hb | _, _, _, .loop _ _ hb | _, _, _, .callNone _ _ hb
  | _, _, _, .callVal _ _ _ _ _ hb => by
    have q := hb.quiet
    simp only [Stmt.pushes, Stmt.pays, Stmt.shrinks, q.1, q.2.1, q.2.2, and_self]

theorem ProgOk.quiet : {Γ Γ' : Ctx} → {P : Solidity.Prog C Γ Γ'} → ProgOk P →
    Prog.pushes P = 0 ∧ Prog.pays P = false ∧ Prog.shrinks P = false
  | _, _, _, .nil => by simp only [Prog.pushes, Prog.pays, Prog.shrinks, and_self]
  | _, _, _, .cons hs hP => by
    have s := hs.quiet
    have q := hP.quiet
    simp only [Prog.pushes, Prog.pays, Prog.shrinks, s.1, s.2.1, s.2.2, q.1, q.2.1, q.2.2,
      Nat.add_zero, Bool.or_self, and_self]
end

/-! ## Fragment growth -/

/-- `G` is `F` with only readable value locals pushed. -/
def Grows {Γ Γ' : Ctx} (F : Frag Γ) (G : Frag Γ') : Prop :=
  G.fl = List.replicate (Γ'.length - Γ.length) Fl.ok ++ F.fl ∧ Γ.length ≤ Γ'.length

theorem Grows.refl {Γ : Ctx} (F : Frag Γ) : Grows F F :=
  ⟨by simp only [Nat.sub_self, List.replicate_zero, List.nil_append], Nat.le_refl _⟩

theorem Grows.trans {Γ Γ₁ Γ₂ : Ctx} {F : Frag Γ} {G : Frag Γ₁} {H : Frag Γ₂}
    (fg : Grows F G) (gh : Grows G H) : Grows F H := by
  refine ⟨?_, Nat.le_trans fg.2 gh.2⟩
  rw [gh.1, fg.1, ← List.append_assoc, ← List.replicate_add]
  congr 2
  have := fg.2
  have := gh.2
  omega

theorem Grows.restrict {Γ Γ' : Ctx} {F : Frag Γ} {G : Frag Γ'} (fg : Grows F G) :
    G.restrict Γ = F := by
  cases F with
  | mk fl =>
    simp only [Frag.restrict, fg.1]
    rw [List.drop_left' (List.length_replicate ..)]

theorem Frag.meet_self {Γ : Ctx} (F : Frag Γ) : F.meet F = F := by
  cases F with
  | mk fl =>
    simp only [Frag.meet, Frag.mk.injEq]
    induction fl with
    | nil => rfl
    | cons f fl ih => simp only [List.zipWith_cons_cons, ite_true, ih]

/-! ## Every program of the domain is in the core fragment -/

mutual
theorem StmtOk.frag : {Γ Γ' : Ctx} → {s : Solidity.Stmt C Γ Γ'} → StmtOk s →
    ∀ F : Frag Γ, ∃ G, inFrag F s = some G ∧ Grows F G
  | _, _, _, .assign hl hv, F => ⟨F, by
      simp only [Evm.inFrag, assignIn, hl.locIn F, hv.valIn F, Bool.and_self, Frag.guard,
        ite_true], Grows.refl F⟩
  | _, _, _, .assignLocal _ hv, F => ⟨F, by
      simp only [Evm.inFrag, hv.valIn F, Frag.guard, ite_true], Grows.refl F⟩
  | _, _, _, .declNone p _, F => ⟨F.push (.val p) .ok, by
      simp only [Evm.inFrag, Option.all, Frag.guard, ite_true],
      ⟨by simp only [Frag.push, List.length_cons, Nat.add_sub_cancel_left, List.replicate_one,
        List.singleton_append], Nat.le_succ _⟩⟩
  | _, _, _, .declSome p _ hv, F => ⟨F.push (.val p) .ok, by
      simp only [Evm.inFrag, Option.all, hv.valIn F, Frag.guard, ite_true],
      ⟨by simp only [Frag.push, List.length_cons, Nat.add_sub_cancel_left, List.replicate_one,
        List.singleton_append], Nat.le_succ _⟩⟩
  | _, _, _, .opAssign _ _ _ _ hv, F => ⟨F, by
      simp only [Evm.inFrag, opLocIn, hv.valIn F, Bool.and_self, Frag.guard, ite_true],
      Grows.refl F⟩
  | _, _, _, .incDec _ _ _, F => ⟨F, by
      simp only [Evm.inFrag, opLocIn, Frag.guard, ite_true], Grows.refl F⟩
  | _, _, _, .require hc, F => ⟨F, by
      simp only [Evm.inFrag, hc.valIn F, Frag.guard, ite_true], Grows.refl F⟩
  | _, _, _, .assert hc, F => ⟨F, by
      simp only [Evm.inFrag, hc.valIn F, Frag.guard, ite_true], Grows.refl F⟩
  | _, _, _, .revert, F => ⟨F, by simp only [Evm.inFrag], Grows.refl F⟩
  | _, _, _, .ite hc ht he, F => by
    obtain ⟨F₁, h₁, g₁⟩ := ht.frag F
    obtain ⟨F₂, h₂, g₂⟩ := he.frag F
    refine ⟨F, ?_, Grows.refl F⟩
    simp only [Evm.inFrag, hc.valIn F, ite_true, h₁, h₂, g₁.restrict, g₂.restrict,
      Frag.meet_self]
  | _, _, _, .block hb, F => by
    obtain ⟨G, h, g⟩ := hb.frag F
    exact ⟨F, by simp only [Evm.inFrag, h, Option.map_some, g.restrict], Grows.refl F⟩
  | _, _, _, .loop _ hc hb, F => by
    obtain ⟨G, h, g⟩ := hb.frag F
    have q := hb.quiet
    refine ⟨F, ?_, Grows.refl F⟩
    simp only [Evm.inFrag, hc.valIn F, q.1, q.2.1, q.2.2, h, g.restrict, beq_self_eq_true,
      Bool.not_false, Bool.and_self, ite_true]
  | _, _, _, .callNone _ ha hb, F => by
    obtain ⟨G, h, _⟩ := hb.frag (Frag.init _)
    refine ⟨F, ?_, Grows.refl F⟩
    simp only [Evm.inFrag, ha.argsIn F, ite_true, h, hb.quiet.2.2, Frag.after, CallRetIn]
  | _, _, _, .callVal _ _ _ _ ha hb, F => by
    obtain ⟨G, h, _⟩ := hb.frag (Frag.init _)
    refine ⟨F, ?_, Grows.refl F⟩
    simp only [Evm.inFrag, ha.argsIn F, ite_true, h, hb.quiet.2.2, Frag.after, CallRetIn]

theorem ProgOk.frag : {Γ Γ' : Ctx} → {P : Solidity.Prog C Γ Γ'} → ProgOk P →
    ∀ F : Frag Γ, ∃ G, inFragP F P = some G ∧ Grows F G
  | _, _, _, .nil, F => ⟨F, by simp only [Evm.inFragP], Grows.refl F⟩
  | _, _, _, .cons hs hP, F => by
    obtain ⟨F₁, h₁, g₁⟩ := hs.frag F
    obtain ⟨G, h, g⟩ := hP.frag F₁
    exact ⟨G, by simp only [Evm.inFragP, h₁, h], g₁.trans g⟩
end

/-! ## Totality and the fixed observation -/

/-- **Compiler success.** Every program of the domain is compiled by the
public entry, from every fragment and frame base, through its core branch. -/
theorem compile_core {Γ Δ : Ctx} (b : Nat) (F : Frag Γ) {P : Solidity.Prog C Γ Δ}
    (hP : ProgOk P) : ∃ G h, Compiler.compile b F P = some (.core G h) := by
  obtain ⟨G, h, _⟩ := hP.frag F
  refine ⟨G, h, ?_⟩
  unfold Compiler.compile
  split
  · next G' h' =>
    have same : G' = G := Option.some.inj (h'.symm.trans h)
    subst same
    rfl
  · next h' => exact absurd (h'.symm.trans h) (by simp only [reduceCtorEq, not_false_eq_true])

theorem compile_isSome {Γ Δ : Ctx} (b : Nat) (F : Frag Γ) {P : Solidity.Prog C Γ Δ}
    (hP : ProgOk P) : (Compiler.compile b F P).isSome = true := by
  obtain ⟨G, h, eq⟩ := compile_core b F hP
  rw [eq]
  rfl

/-- The compiled result satisfies the public compiler's fixed observation
`Compilation.Agrees` from every simulated machine below the word horizon. -/
theorem compile_agrees {Γ Δ : Ctx} (b : Nat) (F : Frag Γ) {P : Solidity.Prog C Γ Δ}
    (hP : ProgOk P) : ∃ result, Compiler.compile b F P = some result ∧
      ∀ (L frame : Nat) (base : Nat → Fin W) (σ : State C Γ) (m : Machine),
        Sim C L b F σ m → L ≤ Lmax → result.Agrees L frame base σ m := by
  obtain ⟨G, h, eq⟩ := compile_core b F hP
  refine ⟨.core G h, eq, fun L frame base σ m hs hL => ?_⟩
  apply Compiler.Compilation.correct
  show Sim C L b F σ m ∧ L + Prog.pushes P ≤ Lmax
  rw [hP.quiet.1, Nat.add_zero]
  exact ⟨hs, hL⟩

end Solidity.Backend.AbiWorld.PublicCompilerTotal
