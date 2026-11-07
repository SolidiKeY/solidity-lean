import Solidity.Evm.Compiler

/-! # Compiler success (totality) of the public compiler on a stated domain

H62 (2)/H69 ask for a separate totality theorem: a compiler that rejects
everything must not satisfy the public statements. The public compiler entry
is `Solidity.Evm.Compiler.compile`; its fixed observation is
`Compilation.Agrees`: a disjunction pairing each source outcome with a machine
outcome (success with typed state and stack; source revert or asserting panic
with a data-free machine `revert`; payment refusal; divergence with a fault).

The domain is stated here as inductive predicates over the intrinsic syntax.
They mention no acceptance function, no fragment (`Frag`) and no compile
result; the word-fit side conditions read the backend's storage layout
(`Evm.offset`, `W`). It is a subset of the core branch's fragment (H87
widened it by signed `&`/`|`/`^`, storage aliases and storage compound
assignment; H96 by aliases bound through an array index): scalar programs
over locals, storage locations and storage aliases, with branches, blocks,
loops and single-value internal calls. Two side conditions are refusals in
the compiler's code:

* `env` excludes `address(this).balance` (`simpleIn`);
* mapping keys are `uint` and a fixed array or struct offset fits a word
  (`locIn`).

Aliases carry a kind (`Kinds`): plain (bound to a path through no array index
and no indexed alias) or indexed (`S storage s = arr[i];`, or a path through
an indexed alias). The judgement fixes each alias's kind at its declaration
and requires every rebind to keep it: where the two branches of an `if`
disagree on an alias's flag the compiler's meet marks it unreadable (`dead`),
so a later read is refused, and a loop whose body changes a flag fails the
fixed-point check. The other exclusions are this domain's choices, not
refusals: an alias is declared with an initializer (an unset one is not
readable until rebound, which this domain does not track), and the core
branch also compiles transfers, `push`/`pop`/`delete`, `assignIncDec` and
static storage copies, which are outside this domain.

`compile_core` proves every program of the domain is compiled, from every
fragment whose alias flags match the kinds (`Matches`, e.g. `Frag.init` with
no kinds) and every base, by the core branch; `compile_agrees` composes it
with the existing `Compilation.correct`. -/
namespace Solidity.Backend.AbiWorld.PublicCompilerTotal
open Solidity.Evm

variable {C : Contract}

/-! ## The domain -/

mutual
/-- A storage path: a storage alias, or a location. -/
inductive PathOk {Γ : Ctx} : {T : Ty} → Solidity.SPath C Γ T → Prop
  | alias {R : RefTy} (i : Idx Γ (.alias R)) : PathOk (.alias i)
  | loc {T : Ty} {l : Solidity.Loc C Γ T} : LocOk l → PathOk (.loc l)

/-- A storage location. -/
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
      {a b : Solidity.Val C Γ p} : ValOk a → ValOk b → ValOk (.binop op h hq a b)
  | unop {p q : PrimTy} (op : UnOp) (h : op.accepts p = true) (hq : op.ret p = q)
      {a : Solidity.Val C Γ p} : ValOk a → ValOk (.unop op h hq a)
  | ternary {p : PrimTy} {c : Solidity.Val C Γ .bool} {a b : Solidity.Val C Γ p} :
      ValOk c → ValOk a → ValOk b → ValOk (.ternary c a b)
  | len {p : PrimTy} {E : Ty} {b : Solidity.SPath C Γ (.array E)} (hp : p = .uint) :
      PathOk b → ValOk (.len b hp)
end

/-- The kind of each storage alias in scope, innermost first: `true` for an
alias bound through an array index, `false` for a plain one. Value-local
positions and positions past the list read `false`. -/
abbrev Kinds := List Bool

/-- The kind recorded at a local's position. -/
def Kinds.at (K : Kinds) {Γ : Ctx} {t : LTy} (i : Idx Γ t) : Bool := K.getD i.toNat false

/-- A path that indexes no array and reaches only plain aliases: a plain
binding. -/
inductive FreePath (K : Kinds) {Γ : Ctx} : {T : Ty} → Solidity.SPath C Γ T → Prop
  | alias {R : RefTy} (i : Idx Γ (.alias R)) (plain : K.at i = false) : FreePath K (.alias i)
  | root {T : Ty} (r : Name) (h : C.rootType r = some T) : FreePath K (.loc (.root r h))
  | field {s : Name} {T : Ty} {b : Solidity.SPath C Γ (.ref (.struct s))} (f : Name)
      (h : C.fieldType s f = some T) (fits : offset s f < W) :
      FreePath K b → FreePath K (.loc (.field b f h))
  | map {V : Ty} {b : Solidity.SPath C Γ (.ref (.mapping .uint V))}
      {i : Solidity.Val C Γ .uint} : FreePath K b → ValOk i → FreePath K (.loc (.index .map b i))

/-- A path through an array index or an indexed alias: an indexed binding. -/
inductive IndexedPath (K : Kinds) {Γ : Ctx} : {T : Ty} → Solidity.SPath C Γ T → Prop
  | alias {R : RefTy} (i : Idx Γ (.alias R)) (indexed : K.at i = true) :
      IndexedPath K (.alias i)
  | dyn {E : Ty} {b : Solidity.SPath C Γ (.ref (.array E))} {i : Solidity.Val C Γ .uint} :
      IndexedPath K (.loc (.index (.arr .dyn) b i))
  | fixed {E : Ty} {n : Nat} {b : Solidity.SPath C Γ (.ref (.fixed E n))}
      {i : Solidity.Val C Γ .uint} : IndexedPath K (.loc (.index (.arr .fixed) b i))
  | field {s : Name} {T : Ty} {b : Solidity.SPath C Γ (.ref (.struct s))} (f : Name)
      (h : C.fieldType s f = some T) : IndexedPath K b → IndexedPath K (.loc (.field b f h))
  | map {k : PrimTy} {V : Ty} {b : Solidity.SPath C Γ (.ref (.mapping k V))}
      {i : Solidity.Val C Γ k} : IndexedPath K b → IndexedPath K (.loc (.index .map b i))

/-- A compound-assignment target: a local or a storage location. -/
inductive OpLocOk {Γ : Ctx} : {p : PrimTy} → Solidity.OpLoc C Γ p → Prop
  | local {p : PrimTy} (i : Idx Γ (.val p)) : OpLocOk (.local i)
  | root {p : PrimTy} (r : Name) (h : C.rootType r = some (.prim p)) : OpLocOk (.root r h)
  | field {s : Name} {p : PrimTy} {b : Solidity.SPath C Γ (.ref (.struct s))} (f : Name)
      (h : C.fieldType s f = some (.prim p)) (fits : offset s f < W) :
      PathOk b → OpLocOk (.field b f h)
  | index {R : RefTy} {k p : PrimTy} {it : IndexTy R k (.prim p)}
      {b : Solidity.SPath C Γ (.ref R)} {i : Solidity.Simple C Γ k} :
      LocOk (.index it b (.simple i)) → OpLocOk (.index it b i)

/-- Value arguments of the domain. -/
inductive ArgsOk {Γ : Ctx} : {ps : Ctx} → Solidity.Args C Γ ps → Prop
  | nil : ArgsOk .nil
  | snoc {ps : Ctx} {as : Solidity.Args C Γ ps} (p : PrimTy) (x : Var)
      {e : Solidity.Val C Γ p} : ArgsOk as → ValOk e → ArgsOk (.snoc as p x e)

mutual
/-- A statement of the domain, from the alias kinds before it to those after. -/
inductive StmtOk : {Γ Γ' : Ctx} → Kinds → Solidity.Stmt C Γ Γ' → Kinds → Prop
  | assign {Γ : Ctx} {K : Kinds} {p : PrimTy} {l : Solidity.Loc C Γ (.prim p)}
      {v : Solidity.Val C Γ p} : LocOk l → ValOk v → StmtOk K (.assign l (.val v)) K
  | assignLocal {Γ : Ctx} {K : Kinds} {p : PrimTy} (i : Idx Γ (.val p))
      {v : Solidity.Val C Γ p} : ValOk v → StmtOk K (.assignLocal i v) K
  | declNone {Γ : Ctx} {K : Kinds} (p : PrimTy) (x : Var) :
      StmtOk (Γ := Γ) K (.declLocal p x none) (false :: K)
  | declSome {Γ : Ctx} {K : Kinds} (p : PrimTy) (x : Var) {v : Solidity.Val C Γ p} :
      ValOk v → StmtOk K (.declLocal p x (some v)) (false :: K)
  | declStorage {Γ : Ctx} {K : Kinds} (R : RefTy) (x : Var) {q : Solidity.SPath C Γ (.ref R)} :
      FreePath K q → StmtOk K (.declStorage R x (some (.path q))) (false :: K)
  | declIndexed {Γ : Ctx} {K : Kinds} (R : RefTy) (x : Var) {q : Solidity.SPath C Γ (.ref R)} :
      PathOk q → IndexedPath K q → StmtOk K (.declStorage R x (some (.path q))) (true :: K)
  | rebind {Γ : Ctx} {K : Kinds} {R : RefTy} (i : Idx Γ (.alias R))
      {q : Solidity.SPath C Γ (.ref R)} (plain : K.at i = false) :
      FreePath K q → StmtOk K (.rebind i (.path q)) K
  | rebindIndexed {Γ : Ctx} {K : Kinds} {R : RefTy} (i : Idx Γ (.alias R))
      {q : Solidity.SPath C Γ (.ref R)} (indexed : K.at i = true) :
      PathOk q → IndexedPath K q → StmtOk K (.rebind i (.path q)) K
  | opAssign {Γ : Ctx} {K : Kinds} {p : PrimTy} (op : BinOp) (hop : op.hasCompoundAssign = true)
      (hp : p.isNumeric = true) {l : Solidity.OpLoc C Γ p} {v : Solidity.Val C Γ p} :
      OpLocOk l → ValOk v → StmtOk K (.opAssign op hop hp l v) K
  | incDec {Γ : Ctx} {K : Kinds} {p : PrimTy} (op : IncDec) (hp : p.isNumeric = true)
      {l : Solidity.OpLoc C Γ p} : OpLocOk l → StmtOk K (.incDec op hp l) K
  | require {Γ : Ctx} {K : Kinds} {c : Solidity.Val C Γ .bool} :
      ValOk c → StmtOk K (.require c) K
  | assert {Γ : Ctx} {K : Kinds} {c : Solidity.Val C Γ .bool} : ValOk c → StmtOk K (.assert c) K
  | revert {Γ : Ctx} {K : Kinds} : StmtOk (Γ := Γ) K .revert K
  | ite {Γ Γ₁ Γ₂ : Ctx} {K : Kinds} {c : Solidity.Val C Γ .bool} {t : Solidity.Prog C Γ Γ₁}
      {e : Solidity.Prog C Γ Γ₂} : ValOk c → ProgOk K t → ProgOk K e → StmtOk K (.ite c t e) K
  | block {Γ Γ₁ : Ctx} {K : Kinds} {body : Solidity.Prog C Γ Γ₁} :
      ProgOk K body → StmtOk K (.block body) K
  | loop {Γ Γ₁ : Ctx} {K : Kinds} (a : LoopAnn C Γ) {c : Solidity.Val C Γ .bool}
      {body : Solidity.Prog C Γ Γ₁} : ValOk c → ProgOk K body → StmtOk K (.loop a c body) K
  | callNone {Γ ps Γf : Ctx} {K : Kinds} (f : Name) {args : Solidity.Args C Γ ps}
      {body : Solidity.Prog C ([] ++ ps) Γf} :
      ArgsOk args → ProgOk [] body → StmtOk K (.call f args .none body) K
  | callVal {Γ ps Γf : Ctx} {K : Kinds} (f : Name) (p : PrimTy) (r : Var)
      (res : Option (Idx Γ (.val p))) {args : Solidity.Args C Γ ps}
      {body : Solidity.Prog C ([.val p] ++ ps) Γf} :
      ArgsOk args → ProgOk [] body → StmtOk K (.call f args (.val p r res) body) K

/-- A program of the domain from the alias kinds before it. -/
inductive ProgOk : {Γ Γ' : Ctx} → Kinds → Solidity.Prog C Γ Γ' → Prop
  | nil {Γ : Ctx} {K : Kinds} : ProgOk (Γ := Γ) K .nil
  | cons {Γ Γ₁ Γ₂ : Ctx} {K K₁ : Kinds} {s : Solidity.Stmt C Γ Γ₁} {P : Solidity.Prog C Γ₁ Γ₂} :
      StmtOk K s K₁ → ProgOk K₁ P → ProgOk K (.cons s P)
end

/-! ## Fragments matching the kinds -/

/-- Each storage alias of `Γ` is flagged as its kind says: plain `ok` or
indexed `fragile`. Value locals are not constrained. -/
def Matches (K : Kinds) {Γ : Ctx} (F : Frag Γ) : Prop :=
  ∀ (R : RefTy) (i : Idx Γ (.alias R)), F.get i = if K.at i then .fragile else .ok

/-- A fresh frame, every local readable, matches no kinds. -/
theorem Matches.init (Γ : Ctx) : Matches [] (Frag.init Γ) := by
  intro R i
  simp only [Kinds.at, Frag.get, Frag.init, List.getD_eq_getElem?_getD, List.getElem?_nil,
    Option.getD_none, Bool.false_eq_true, ite_false, List.getElem?_map, Idx.getElem?_toNat,
    Option.map_some, Option.getD_some]

theorem Matches.push {K : Kinds} {Γ : Ctx} {F : Frag Γ} (hF : Matches K F) (t : LTy)
    (k : Bool) {f : Fl} (hf : f = if k then .fragile else .ok) : Matches (k :: K) (F.push t f) := by
  intro R i
  cases i with
  | here => simp only [Frag.get, Frag.push, Idx.toNat, Kinds.at, List.getD_cons_zero, hf]
  | there j =>
    simp only [Frag.get, Frag.push, Idx.toNat, Kinds.at, List.getD_cons_succ]
    exact hF _ j

/-- Either kind is readable as a storage path. -/
theorem Matches.read {K : Kinds} {Γ : Ctx} {F : Frag Γ} (hF : Matches K F) {R : RefTy}
    (i : Idx Γ (.alias R)) : spathIn (C := C) F false (.alias i) = true := by
  show (F.get i == Fl.ok || (!false && F.get i == Fl.fragile)) = true
  rw [hF _ i]
  cases K.at i <;> rfl

/-- Rebinding an alias with the flag it has leaves the fragment unchanged. -/
theorem Frag.set_of_get {Γ : Ctx} {F : Frag Γ} {t : LTy} {i : Idx Γ t} {f : Fl}
    (h : F.get i = f) (live : f ≠ .dead) : F.set i f = F := by
  cases F with
  | mk fl =>
    simp only [Frag.get, List.getD_eq_getElem?_getD] at h
    simp only [Frag.set, Frag.mk.injEq]
    match e : fl[i.toNat]? with
    | none =>
      rw [e, Option.getD_none] at h
      exact absurd h.symm live
    | some g =>
      rw [e, Option.getD_some] at h
      obtain ⟨hi, hv⟩ := List.getElem?_eq_some_iff.mp e
      rw [← h, ← hv]
      exact List.set_getElem_self hi

/-! ## Values are accepted from every matching fragment -/

/-- Every typed binary operator is compiled. -/
theorem binInFrag_of {op : BinOp} {p : PrimTy} (h : op.accepts p = true) :
    binInFrag op p = true := by
  revert h
  cases op <;> cases p <;> decide

/-- Every typed unary operator is compiled. -/
theorem unInFrag_of {op : UnOp} {p : PrimTy} (h : op.accepts p = true) :
    unInFrag op p = true := by
  revert h
  cases op <;> cases p <;> decide

mutual
theorem PathOk.spathIn {K : Kinds} {Γ : Ctx} {F : Frag Γ} (hF : Matches K F) : {T : Ty} →
    {q : Solidity.SPath C Γ T} → PathOk q → spathIn F false q = true
  | _, _, .alias i => Matches.read hF i
  | _, _, .loc h => by simp only [Evm.spathIn, h.locIn hF]

theorem LocOk.locIn {K : Kinds} {Γ : Ctx} {F : Frag Γ} (hF : Matches K F) : {T : Ty} →
    {l : Solidity.Loc C Γ T} → LocOk l → locIn F false l = true
  | _, _, .root _ _ => by simp only [Evm.locIn]
  | _, _, .field _ _ fits hb => by
    simp only [Evm.locIn, decide_eq_true fits, hb.spathIn hF, Bool.and_self]
  | _, _, .map hb hi => by
    simp only [Evm.locIn, hb.spathIn hF, hi.valIn hF, Bool.and_self, beq_self_eq_true]
  | _, _, .dyn hb hi => by
    simp only [Evm.locIn, hb.spathIn hF, hi.valIn hF, Bool.and_self, Bool.not_false]
  | _, _, .fixed fits hb hi => by
    simp only [Evm.locIn, decide_eq_true fits, hb.spathIn hF, hi.valIn hF, Bool.and_self,
      Bool.not_false]

theorem ValOk.valIn {K : Kinds} {Γ : Ctx} {F : Frag Γ} (hF : Matches K F) : {p : PrimTy} →
    {v : Solidity.Val C Γ p} → ValOk v → valIn F v = true
  | _, _, .lit _ _ => by simp only [Evm.valIn, simpleIn]
  | _, _, .bool _ => by simp only [Evm.valIn, simpleIn]
  | _, _, .local _ => by simp only [Evm.valIn, simpleIn]
  | _, _, .env _ _ hk => by
    simp only [Evm.valIn, simpleIn, bne_iff_ne, ne_eq, hk, not_false_eq_true]
  | _, _, .read hl => by simp only [Evm.valIn, hl.locIn hF]
  | _, _, .binop _ h _ ha hb => by
    simp only [Evm.valIn, binInFrag_of h, ha.valIn hF, hb.valIn hF, Bool.and_self]
  | _, _, .unop _ h _ ha => by simp only [Evm.valIn, unInFrag_of h, ha.valIn hF, Bool.and_self]
  | _, _, .ternary hc ha hb => by
    simp only [Evm.valIn, hc.valIn hF, ha.valIn hF, hb.valIn hF, Bool.and_self]
  | _, _, .len _ hb => by simp only [Evm.valIn, hb.spathIn hF]
end

theorem FreePath.spathIn {K : Kinds} {Γ : Ctx} {F : Frag Γ} (hF : Matches K F) : {T : Ty} →
    {q : Solidity.SPath C Γ T} → FreePath K q → spathIn F true q = true
  | _, _, .alias i plain => by
    simp only [Evm.spathIn, hF _ i, plain, Bool.false_eq_true, ite_false, beq_self_eq_true,
      Bool.true_or]
  | _, _, .root _ _ => by simp only [Evm.spathIn, Evm.locIn]
  | _, _, .field _ _ fits hb => by
    simp only [Evm.spathIn, Evm.locIn, decide_eq_true fits, hb.spathIn hF, Bool.and_self]
  | _, _, .map hb hi => by
    simp only [Evm.spathIn, Evm.locIn, hb.spathIn hF, hi.valIn hF, Bool.and_self,
      beq_self_eq_true]

theorem IndexedPath.not_free {K : Kinds} {Γ : Ctx} {F : Frag Γ} (hF : Matches K F) :
    {T : Ty} → {q : Solidity.SPath C Γ T} → IndexedPath K q → spathIn F true q = false
  | _, _, .alias i indexed => by simp only [Evm.spathIn, hF _ i, indexed, ite_true]; rfl
  | _, _, .dyn => by simp only [Evm.spathIn, Evm.locIn, Bool.not_true, Bool.false_and]
  | _, _, .fixed => by simp only [Evm.spathIn, Evm.locIn, Bool.not_true, Bool.false_and]
  | _, _, .field _ _ hb => by simp only [Evm.spathIn, Evm.locIn, hb.not_free hF, Bool.and_false]
  | _, _, .map hb => by
    simp only [Evm.spathIn, Evm.locIn, hb.not_free hF, Bool.and_false, Bool.false_and]

theorem FreePath.bindFl {K : Kinds} {Γ : Ctx} {F : Frag Γ} (hF : Matches K F) {R : RefTy}
    {q : Solidity.SPath C Γ (.ref R)} (hq : FreePath K q) : bindFl F q = some .ok := by
  simp only [Evm.bindFl, hq.spathIn hF, ite_true]

theorem IndexedPath.bindFl {K : Kinds} {Γ : Ctx} {F : Frag Γ} (hF : Matches K F) {R : RefTy}
    {q : Solidity.SPath C Γ (.ref R)} (hp : PathOk q) (hq : IndexedPath K q) :
    bindFl F q = some .fragile := by
  simp only [Evm.bindFl, hq.not_free hF, hp.spathIn hF, Bool.false_eq_true, ite_false, ite_true]

theorem OpLocOk.opLocIn {K : Kinds} {Γ : Ctx} {F : Frag Γ} (hF : Matches K F) {p : PrimTy}
    {l : Solidity.OpLoc C Γ p} : OpLocOk l → opLocIn F l = true
  | .local _ => by simp only [Evm.opLocIn]
  | .root _ _ => by simp only [Evm.opLocIn, opLocToLoc, Evm.locIn]
  | .field _ _ fits hb => by
    simp only [Evm.opLocIn, opLocToLoc, Evm.locIn, decide_eq_true fits, hb.spathIn hF,
      Bool.and_self]
  | .index hl => by simp only [Evm.opLocIn, opLocToLoc, hl.locIn hF]

theorem ArgsOk.argsIn {K : Kinds} {Γ : Ctx} {F : Frag Γ} (hF : Matches K F) : {ps : Ctx} →
    {as : Solidity.Args C Γ ps} → ArgsOk as → argsIn F as = true
  | _, _, .nil => by simp only [Evm.argsIn]
  | _, _, .snoc _ _ ha he => by simp only [Evm.argsIn, ha.argsIn hF, he.valIn hF, Bool.and_self]

/-! ## Programs push, pay and shrink nothing -/

mutual
theorem StmtOk.quiet : {Γ Γ' : Ctx} → {K K' : Kinds} → {s : Solidity.Stmt C Γ Γ'} →
    StmtOk K s K' → Stmt.pushes s = 0 ∧ Stmt.pays s = false ∧ Stmt.shrinks s = false
  | _, _, _, _, _, .assign _ _ | _, _, _, _, _, .assignLocal _ _
  | _, _, _, _, _, .declNone _ _ | _, _, _, _, _, .declSome _ _ _
  | _, _, _, _, _, .declStorage _ _ _ | _, _, _, _, _, .declIndexed _ _ _ _
  | _, _, _, _, _, .rebind _ _ _ | _, _, _, _, _, .rebindIndexed _ _ _ _
  | _, _, _, _, _, .opAssign _ _ _ _ _ | _, _, _, _, _, .incDec _ _ _
  | _, _, _, _, _, .require _ | _, _, _, _, _, .assert _ | _, _, _, _, _, .revert =>
    by simp only [Stmt.pushes, Stmt.pays, Stmt.shrinks, and_self]
  | _, _, _, _, _, .ite _ ht he => by
    have t := ht.quiet
    have e := he.quiet
    simp only [Stmt.pushes, Stmt.pays, Stmt.shrinks, t.1, t.2.1, t.2.2, e.1, e.2.1, e.2.2,
      Nat.add_zero, Bool.or_self, and_self]
  | _, _, _, _, _, .block hb | _, _, _, _, _, .loop _ _ hb | _, _, _, _, _, .callNone _ _ hb
  | _, _, _, _, _, .callVal _ _ _ _ _ hb => by
    have q := hb.quiet
    simp only [Stmt.pushes, Stmt.pays, Stmt.shrinks, q.1, q.2.1, q.2.2, and_self]

theorem ProgOk.quiet : {Γ Γ' : Ctx} → {K : Kinds} → {P : Solidity.Prog C Γ Γ'} → ProgOk K P →
    Prog.pushes P = 0 ∧ Prog.pays P = false ∧ Prog.shrinks P = false
  | _, _, _, _, .nil => by simp only [Prog.pushes, Prog.pays, Prog.shrinks, and_self]
  | _, _, _, _, .cons hs hP => by
    have s := hs.quiet
    have q := hP.quiet
    simp only [Prog.pushes, Prog.pays, Prog.shrinks, s.1, s.2.1, s.2.2, q.1, q.2.1, q.2.2,
      Nat.add_zero, Bool.or_self, and_self]
end

/-! ## Fragment growth -/

/-- `G` is `F` with locals pushed and nothing else changed. -/
def Grows {Γ Γ' : Ctx} (F : Frag Γ) (G : Frag Γ') : Prop :=
  ∃ pre : List Fl, G.fl = pre ++ F.fl ∧ pre.length + Γ.length = Γ'.length

theorem Grows.refl {Γ : Ctx} (F : Frag Γ) : Grows F F :=
  ⟨[], (List.nil_append _).symm, Nat.zero_add _⟩

theorem Grows.push {Γ : Ctx} (F : Frag Γ) (t : LTy) (f : Fl) : Grows F (F.push t f) :=
  ⟨[f], rfl, by simp only [List.length_cons, List.length_nil]; omega⟩

theorem Grows.trans {Γ Γ₁ Γ₂ : Ctx} {F : Frag Γ} {G : Frag Γ₁} {H : Frag Γ₂}
    (fg : Grows F G) (gh : Grows G H) : Grows F H := by
  obtain ⟨p₁, e₁, l₁⟩ := fg
  obtain ⟨p₂, e₂, l₂⟩ := gh
  refine ⟨p₂ ++ p₁, by rw [e₂, e₁, List.append_assoc], ?_⟩
  rw [List.length_append]
  omega

theorem Grows.restrict {Γ Γ' : Ctx} {F : Frag Γ} {G : Frag Γ'} (fg : Grows F G) :
    G.restrict Γ = F := by
  obtain ⟨pre, e, l⟩ := fg
  cases F with
  | mk fl =>
    simp only [Frag.restrict, e, Frag.mk.injEq]
    rw [show Γ'.length - Γ.length = pre.length by omega]
    exact List.drop_left

theorem Frag.meet_self {Γ : Ctx} (F : Frag Γ) : F.meet F = F := by
  cases F with
  | mk fl =>
    simp only [Frag.meet, Frag.mk.injEq]
    induction fl with
    | nil => rfl
    | cons f fl ih => simp only [List.zipWith_cons_cons, ite_true, ih]

/-! ## Every program of the domain is in the core fragment -/

mutual
theorem StmtOk.frag : {Γ Γ' : Ctx} → {K K' : Kinds} → {s : Solidity.Stmt C Γ Γ'} →
    StmtOk K s K' → ∀ F : Frag Γ, Matches K F →
      ∃ G, inFrag F s = some G ∧ Grows F G ∧ Matches K' G
  | _, _, _, _, _, .assign hl hv, F, hF => ⟨F, by
      simp only [Evm.inFrag, assignIn, hl.locIn hF, hv.valIn hF, Bool.and_self, Frag.guard,
        ite_true], Grows.refl F, hF⟩
  | _, _, _, _, _, .assignLocal _ hv, F, hF => ⟨F, by
      simp only [Evm.inFrag, hv.valIn hF, Frag.guard, ite_true], Grows.refl F, hF⟩
  | _, _, _, _, _, .declNone p _, F, hF => ⟨F.push (.val p) .ok, by
      simp only [Evm.inFrag, Option.all, Frag.guard, ite_true],
      Grows.push F _ _, Matches.push hF _ false rfl⟩
  | _, _, _, _, _, .declSome p _ hv, F, hF => ⟨F.push (.val p) .ok, by
      simp only [Evm.inFrag, Option.all, hv.valIn hF, Frag.guard, ite_true],
      Grows.push F _ _, Matches.push hF _ false rfl⟩
  | _, _, _, _, _, .declStorage R _ hq, F, hF => ⟨F.push (.alias R) .ok, by
      simp only [Evm.inFrag, declStorageIn, hq.bindFl hF, Option.map_some],
      Grows.push F _ _, Matches.push hF _ false rfl⟩
  | _, _, _, _, _, .declIndexed R _ hp hq, F, hF => ⟨F.push (.alias R) .fragile, by
      simp only [Evm.inFrag, declStorageIn, hq.bindFl hF hp, Option.map_some],
      Grows.push F _ _, Matches.push hF _ true rfl⟩
  | _, _, _, _, _, .rebind i plain hq, F, hF => ⟨F, by
      have flag : F.get i = .ok := by rw [hF _ i, plain]; rfl
      simp only [Evm.inFrag, hq.bindFl hF, Option.map_some,
        Frag.set_of_get flag (by simp only [ne_eq, reduceCtorEq, not_false_eq_true])],
      Grows.refl F, hF⟩
  | _, _, _, _, _, .rebindIndexed i indexed hp hq, F, hF => ⟨F, by
      have flag : F.get i = .fragile := by rw [hF _ i, indexed]; rfl
      simp only [Evm.inFrag, hq.bindFl hF hp, Option.map_some,
        Frag.set_of_get flag (by simp only [ne_eq, reduceCtorEq, not_false_eq_true])],
      Grows.refl F, hF⟩
  | _, _, _, _, _, .opAssign _ _ _ hl hv, F, hF => ⟨F, by
      simp only [Evm.inFrag, hl.opLocIn hF, hv.valIn hF, Bool.and_self, Frag.guard, ite_true],
      Grows.refl F, hF⟩
  | _, _, _, _, _, .incDec _ _ hl, F, hF => ⟨F, by
      simp only [Evm.inFrag, hl.opLocIn hF, Frag.guard, ite_true], Grows.refl F, hF⟩
  | _, _, _, _, _, .require hc, F, hF => ⟨F, by
      simp only [Evm.inFrag, hc.valIn hF, Frag.guard, ite_true], Grows.refl F, hF⟩
  | _, _, _, _, _, .assert hc, F, hF => ⟨F, by
      simp only [Evm.inFrag, hc.valIn hF, Frag.guard, ite_true], Grows.refl F, hF⟩
  | _, _, _, _, _, .revert, F, hF => ⟨F, by simp only [Evm.inFrag], Grows.refl F, hF⟩
  | _, _, _, _, _, .ite hc ht he, F, hF => by
    obtain ⟨F₁, h₁, g₁⟩ := ht.frag F hF
    obtain ⟨F₂, h₂, g₂⟩ := he.frag F hF
    refine ⟨F, ?_, Grows.refl F, hF⟩
    simp only [Evm.inFrag, hc.valIn hF, ite_true, h₁, h₂, g₁.restrict, g₂.restrict,
      Frag.meet_self]
  | _, _, _, _, _, .block hb, F, hF => by
    obtain ⟨G, h, g⟩ := hb.frag F hF
    exact ⟨F, by simp only [Evm.inFrag, h, Option.map_some, g.restrict], Grows.refl F, hF⟩
  | _, _, _, _, _, .loop _ hc hb, F, hF => by
    obtain ⟨G, h, g⟩ := hb.frag F hF
    have q := hb.quiet
    refine ⟨F, ?_, Grows.refl F, hF⟩
    simp only [Evm.inFrag, hc.valIn hF, q.1, q.2.1, q.2.2, h, g.restrict, beq_self_eq_true,
      Bool.not_false, Bool.and_self, ite_true]
  | _, _, _, _, _, .callNone _ ha hb, F, hF => by
    obtain ⟨G, h, _⟩ := hb.frag (Frag.init _) (Matches.init _)
    refine ⟨F, ?_, Grows.refl F, hF⟩
    simp only [Evm.inFrag, ha.argsIn hF, ite_true, h, hb.quiet.2.2, Frag.after, CallRetIn,
      Bool.false_eq_true, ite_false]
  | _, _, _, _, _, .callVal _ _ _ _ ha hb, F, hF => by
    obtain ⟨G, h, _⟩ := hb.frag (Frag.init _) (Matches.init _)
    refine ⟨F, ?_, Grows.refl F, hF⟩
    simp only [Evm.inFrag, ha.argsIn hF, ite_true, h, hb.quiet.2.2, Frag.after, CallRetIn,
      Bool.false_eq_true, ite_false]

theorem ProgOk.frag : {Γ Γ' : Ctx} → {K : Kinds} → {P : Solidity.Prog C Γ Γ'} → ProgOk K P →
    ∀ F : Frag Γ, Matches K F → ∃ G, inFragP F P = some G ∧ Grows F G
  | _, _, _, _, .nil, F, _ => ⟨F, by simp only [Evm.inFragP], Grows.refl F⟩
  | _, _, _, _, .cons hs hP, F, hF => by
    obtain ⟨F₁, h₁, g₁, r₁⟩ := hs.frag F hF
    obtain ⟨G, h, g⟩ := hP.frag F₁ r₁
    exact ⟨G, by simp only [Evm.inFragP, h₁, h], g₁.trans g⟩
end

/-! ## Totality and the fixed observation -/

/-- **Compiler success.** Every program of the domain is compiled by the
public entry, from every fragment matching its alias kinds and every frame
base, through its core branch. -/
theorem compile_core {Γ Δ : Ctx} (b : Nat) {K : Kinds} {F : Frag Γ} (hF : Matches K F)
    {P : Solidity.Prog C Γ Δ} (hP : ProgOk K P) :
    ∃ G h, Compiler.compile b F P = some (.core G h) := by
  obtain ⟨G, h, _⟩ := hP.frag F hF
  refine ⟨G, h, ?_⟩
  unfold Compiler.compile
  split
  · next G' h' =>
    have same : G' = G := Option.some.inj (h'.symm.trans h)
    subst same
    rfl
  · next h' => exact absurd (h'.symm.trans h) (by simp only [reduceCtorEq, not_false_eq_true])

theorem compile_isSome {Γ Δ : Ctx} (b : Nat) {K : Kinds} {F : Frag Γ} (hF : Matches K F)
    {P : Solidity.Prog C Γ Δ} (hP : ProgOk K P) : (Compiler.compile b F P).isSome = true := by
  obtain ⟨G, h, eq⟩ := compile_core b hF hP
  rw [eq]
  rfl

/-- The entry form: a whole program or call body from its fresh frame. -/
theorem compile_init {Γ Δ : Ctx} (b : Nat) {P : Solidity.Prog C Γ Δ} (hP : ProgOk [] P) :
    (Compiler.compile b (Frag.init Γ) P).isSome = true :=
  compile_isSome b (Matches.init Γ) hP

/-- The compiled result satisfies the public compiler's fixed observation
`Compilation.Agrees` from every simulated machine below the word horizon. -/
theorem compile_agrees {Γ Δ : Ctx} (b : Nat) {K : Kinds} {F : Frag Γ} (hF : Matches K F)
    {P : Solidity.Prog C Γ Δ} (hP : ProgOk K P) :
    ∃ result, Compiler.compile b F P = some result ∧
      ∀ (L frame : Nat) (base : Nat → Fin W) (σ : State C Γ) (m : Machine),
        Sim C L b F σ m → L ≤ Lmax → result.Agrees L frame base σ m := by
  obtain ⟨G, h, eq⟩ := compile_core b hF hP
  refine ⟨.core G h, eq, fun L frame base σ m hs hL => ?_⟩
  apply Compiler.Compilation.correct
  show Sim C L b F σ m ∧ L + Prog.pushes P ≤ Lmax
  rw [hP.quiet.1, Nat.add_zero]
  exact ⟨hs, hL⟩

end Solidity.Backend.AbiWorld.PublicCompilerTotal
