import Solidity.SolcValidation.IrParse
import Solidity.Yul.CatalogLaws

/-!
# An injective, decidable erasure of the intrinsic IR tree

The intrinsic tree (`SolcValidation/IrSyntax.lean`) has no decidable equality:
its terms are indexed by scopes and carry literal proofs. `erase` maps it to a
plain tree that keeps every name, every resolved position (`Mem.index`), every
signature, operation and literal, and drops only the proofs; `objectErase_inj`
proves that two trees with the same erasure are equal. Equalities of concrete
trees can then be decided by kernel evaluation (`SolcValidation/IrCensusParse.lean`).
-/
namespace Solidity.SolcValidation.IrSyntax
open Solidity.SolcValidation

/-- An operation: arities, spelling, and its literal metadata (label or number). -/
structure UOp where
  arity : Nat
  results : Nat
  name : String
  label : String
  num : Nat
  deriving DecidableEq, Repr

def objectOpErase {a r : Nat} : ObjectOp a r → UOp
  | .datasize l => ⟨0, 1, "datasize", l, 0⟩
  | .dataoffset l => ⟨0, 1, "dataoffset", l, 0⟩
  | .datacopy => ⟨3, 0, "datacopy", "", 0⟩
  | .setimmutable l => ⟨2, 0, "setimmutable", l, 0⟩
  | .loadimmutable l => ⟨0, 1, "loadimmutable", l, 0⟩
  | .linkersymbol l => ⟨0, 1, "linkersymbol", l, 0⟩
  | .memoryguard n => ⟨0, 1, "memoryguard", "", n.val⟩

def opErase {a r : Nat} : Op a r → UOp
  | .evm b => ⟨a, r, b.name, "", 1⟩
  | .object o => objectOpErase o

mutual
inductive UExpr where
  | lit (t : LitTok)
  | var (x : String) (i : Nat)
  | op (o : UOp) (args : UArgs)
  | call (s : FnSig) (i : Nat) (args : UArgs)

inductive UArgs where
  | nil
  | cons (e : UExpr) (rest : UArgs)
end

deriving instance DecidableEq for UExpr, UArgs

inductive UInit where
  | none
  | some (e : UExpr)
  deriving DecidableEq

mutual
inductive UStmt where
  | block (b : UBlock)
  | discard (e : UExpr)
  | assign (ts : List (String × Nat)) (e : UExpr)
  | if_ (e : UExpr) (b : UBlock)
  | switch (e : UExpr) (cs : UCases)
  | switchDefault (e : UExpr) (cs : UCases) (b : UBlock)
  | for_ (lp : ULoop)
  | leave | break_ | continue_

inductive UCases where
  | nil
  | cons (t : LitTok) (b : UBlock) (rest : UCases)

inductive ULoop where
  | stmt (s : UStmt) (rest : ULoop)
  | let_ (xs : List String) (i : UInit) (rest : ULoop)
  | run (e : UExpr) (post body : UBlock)

inductive UItems where
  | nil
  | stmt (s : UStmt) (rest : UItems)
  | let_ (xs : List String) (i : UInit) (rest : UItems)
  | fn (k : Nat) (rest : UItems)

inductive UBlock where
  | mk (ss : List FnSig) (bodies : UBodies) (items : UItems)

inductive UBodies where
  | nil
  | cons (b : UBlock) (rest : UBodies)
end

mutual
inductive UObject where
  | object (name : String) (code : UBlock) (children : UObjects)
  | data (name : String) (bytes : List (Fin 256))

inductive UObjects where
  | nil
  | cons (o : UObject) (rest : UObjects)
end

deriving instance DecidableEq for UStmt, UCases, ULoop, UItems, UBlock, UBodies
deriving instance DecidableEq for UObject, UObjects

mutual
def Expr.erase {F L r} : Expr F L r → UExpr
  | .lit l => .lit l.tok
  | .var x m => .var x m.index
  | .op o args => .op (opErase o) args.erase
  | @Expr.call _ _ s m args => .call s m.index args.erase

def Args.erase {F L k} : Args F L k → UArgs
  | .nil => .nil
  | .cons e rest => .cons e.erase rest.erase
end

def initErase {F L} {xs : List String} : Option (Expr F L xs.length) → UInit
  | none => .none
  | some e => .some e.erase

def targetsErase {L : List String} (ts : List (Var L)) : List (String × Nat) :=
  ts.map fun t => (t.1, t.2.index)

mutual
def Stmt.erase {F c L} : Stmt F c L → UStmt
  | .block b => .block b.erase
  | .discard e => .discard e.erase
  | .assign ts e => .assign (targetsErase ts) e.erase
  | .if_ e b => .if_ e.erase b.erase
  | .switch e cs => .switch e.erase cs.erase
  | .switchDefault e cs b => .switchDefault e.erase cs.erase b.erase
  | .for_ lp => .for_ lp.erase
  | .leave => .leave
  | .break_ => .break_
  | .continue_ => .continue_

def Cases.erase {F c L} : Cases F c L → UCases
  | .nil => .nil
  | .cons l b rest => .cons l.tok b.erase rest.erase

def Loop.erase {F c L} : Loop F c L → ULoop
  | .stmt s rest => .stmt s.erase rest.erase
  | .let_ xs e rest => .let_ xs (initErase e) rest.erase
  | .run e post body => .run e.erase post.erase body.erase

def Items.erase {F c L g} : Items F c L g → UItems
  | .nil => .nil
  | .stmt s rest => .stmt s.erase rest.erase
  | .let_ xs e rest => .let_ xs (initErase e) rest.erase
  | .fn k rest => .fn k.val rest.erase

def Block.erase {F c L} : Block F c L → UBlock
  | .mk ss bodies items => .mk ss bodies.erase items.erase

def Bodies.erase {F ss} : Bodies F ss → UBodies
  | .nil => .nil
  | .cons body rest => .cons body.erase rest.erase
end

mutual
def objectErase : Object Code → UObject
  | .object name code children => .object name code.erase (objectsErase children)
  | .data name bytes => .data name bytes

def objectsErase : List (Object Code) → UObjects
  | [] => .nil
  | o :: os => .cons (objectErase o) (objectsErase os)
end

/-! ## Injectivity -/

theorem Lit.eq_of_tok : ∀ {l₁ l₂ : Lit}, l₁.tok = l₂.tok → l₁ = l₂
  | ⟨t, v₁, d₁⟩, ⟨_, v₂, d₂⟩, rfl => by
      have hv : v₁ = v₂ := Option.some.inj (d₁.symm.trans d₂)
      subst hv
      rfl

theorem builtin_entry_eq {a₁ r₁ a₂ r₂ : Nat} (b₁ : Solidity.Yul.Builtin a₁ r₁)
    (b₂ : Solidity.Yul.Builtin a₂ r₂) (h : b₁.name = b₂.name) :
    a₁ = a₂ ∧ r₁ = r₂ ∧ HEq b₁ b₂ := by
  have h₁ := Solidity.Yul.lookup_builtin_name b₁
  have h₂ := Solidity.Yul.lookup_builtin_name b₂
  rw [h, h₂] at h₁
  cases h₁
  exact ⟨rfl, rfl, HEq.rfl⟩

theorem builtin_not_object {a r : Nat} (b : Solidity.Yul.Builtin a r) (x : String)
    (hx : x ∈ objectNames) : b.name ≠ x := by
  intro h
  have hnone : (Solidity.Yul.lookupBuiltin x).isSome = false := by
    simp only [objectNames, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have h₁ := Solidity.Yul.lookup_builtin_name b
  rw [h] at h₁
  simp only [h₁, Option.isSome_some, Bool.true_eq_false] at hnone

theorem opErase_heq {a₁ r₁ a₂ r₂ : Nat} (o₁ : Op a₁ r₁) (o₂ : Op a₂ r₂)
    (h : opErase o₁ = opErase o₂) : a₁ = a₂ ∧ r₁ = r₂ ∧ HEq o₁ o₂ := by
  cases o₁ with
  | evm b₁ =>
    cases o₂ with
    | evm b₂ =>
      simp only [opErase, UOp.mk.injEq] at h
      obtain ⟨rfl, rfl, hb⟩ := builtin_entry_eq b₁ b₂ h.2.2.1
      cases hb
      exact ⟨rfl, rfl, HEq.rfl⟩
    | object o =>
      cases o <;> simp only [opErase, objectOpErase, UOp.mk.injEq] at h <;>
        exact absurd h.2.2.1 (builtin_not_object b₁ _ (by decide))
  | object o₁ =>
    cases o₂ with
    | evm b₂ =>
      cases o₁ <;> simp only [opErase, objectOpErase, UOp.mk.injEq] at h <;>
        exact absurd h.2.2.1.symm (builtin_not_object b₂ _ (by decide))
    | object o₂ =>
      cases o₁ <;> cases o₂ <;> simp only [opErase, objectOpErase, UOp.mk.injEq] at h <;>
        (try exact absurd h.2.2.1 (by decide)) <;>
        (try (obtain ⟨-, -, -, rfl, -⟩ := h; exact ⟨rfl, rfl, HEq.rfl⟩)) <;>
        (try exact ⟨rfl, rfl, HEq.rfl⟩)
      · obtain ⟨-, -, -, -, hn⟩ := h
        exact ⟨rfl, rfl, by rw [Fin.ext hn]⟩

theorem Mem.heq_of_index {α : Type} : ∀ {L : List α} {x y : α} (m₁ : Mem L x) (m₂ : Mem L y),
    m₁.index = m₂.index → x = y ∧ HEq m₁ m₂
  | _, _, _, .here, .here, _ => ⟨rfl, HEq.rfl⟩
  | _, _, _, .there m₁, .there m₂, h => by
      simp only [Mem.index, Nat.add_right_cancel_iff] at h
      obtain ⟨rfl, hm⟩ := Mem.heq_of_index m₁ m₂ h
      cases hm
      exact ⟨rfl, HEq.rfl⟩
  | _, _, _, .here, .there _, h => by simp only [Mem.index] at h; omega
  | _, _, _, .there _, .here, h => by simp only [Mem.index] at h; omega

mutual
theorem Expr.erase_heq {F L} : ∀ {r₁ r₂ : Nat} (e₁ : Expr F L r₁) (e₂ : Expr F L r₂),
    e₁.erase = e₂.erase → r₁ = r₂ ∧ HEq e₁ e₂
  | _, _, .lit l₁, e₂, h => by
      cases e₂ <;> simp only [Expr.erase, UExpr.lit.injEq, reduceCtorEq] at h
      rw [Lit.eq_of_tok h]
      exact ⟨rfl, HEq.rfl⟩
  | _, _, .var x m₁, e₂, h => by
      cases e₂ <;> simp only [Expr.erase, UExpr.var.injEq, reduceCtorEq] at h
      obtain ⟨rfl, hi⟩ := h
      obtain ⟨-, hm⟩ := Mem.heq_of_index m₁ _ hi
      cases hm
      exact ⟨rfl, HEq.rfl⟩
  | _, _, .op o₁ args₁, e₂, h => by
      cases e₂ <;> simp only [Expr.erase, UExpr.op.injEq, reduceCtorEq] at h
      rename_i args₂ o₂
      obtain ⟨ho, ha⟩ := h
      obtain ⟨rfl, hargs⟩ := Args.erase_heq args₁ args₂ ha
      cases hargs
      obtain ⟨-, rfl, hop⟩ := opErase_heq o₁ o₂ ho
      cases hop
      exact ⟨rfl, HEq.rfl⟩
  | _, _, .call m₁ args₁, e₂, h => by
      cases e₂ <;> simp only [Expr.erase, UExpr.call.injEq, reduceCtorEq] at h
      rename_i m₂ args₂
      obtain ⟨rfl, hi, ha⟩ := h
      obtain ⟨-, hm⟩ := Mem.heq_of_index m₁ m₂ hi
      cases hm
      obtain ⟨-, hargs⟩ := Args.erase_heq args₁ args₂ ha
      cases hargs
      exact ⟨rfl, HEq.rfl⟩

theorem Args.erase_heq {F L} : ∀ {k₁ k₂ : Nat} (a₁ : Args F L k₁) (a₂ : Args F L k₂),
    a₁.erase = a₂.erase → k₁ = k₂ ∧ HEq a₁ a₂
  | _, _, .nil, a₂, h => by
      cases a₂ <;> simp only [Args.erase, reduceCtorEq] at h
      exact ⟨rfl, HEq.rfl⟩
  | _, _, .cons e₁ r₁, a₂, h => by
      cases a₂ <;> simp only [Args.erase, UArgs.cons.injEq, reduceCtorEq] at h
      rename_i e₂ r₂
      obtain ⟨he, hr⟩ := h
      obtain ⟨-, he'⟩ := Expr.erase_heq e₁ e₂ he
      cases he'
      obtain ⟨rfl, hr'⟩ := Args.erase_heq r₁ r₂ hr
      cases hr'
      exact ⟨rfl, HEq.rfl⟩
end

theorem Expr.erase_inj {F L r} (e₁ e₂ : Expr F L r) (h : e₁.erase = e₂.erase) : e₁ = e₂ :=
  eq_of_heq (Expr.erase_heq e₁ e₂ h).2

theorem initErase_inj {F L} {xs : List String} :
    ∀ (i₁ i₂ : Option (Expr F L xs.length)), initErase i₁ = initErase i₂ → i₁ = i₂
  | none, none, _ => rfl
  | some e₁, some e₂, h => by
      simp only [initErase, UInit.some.injEq] at h
      rw [Expr.erase_inj e₁ e₂ h]
  | none, some _, h => by simp only [initErase, reduceCtorEq] at h
  | some _, none, h => by simp only [initErase, reduceCtorEq] at h

theorem targetsErase_inj {L : List String} :
    ∀ (ts₁ ts₂ : List (Var L)), targetsErase ts₁ = targetsErase ts₂ → ts₁ = ts₂
  | [], [], _ => rfl
  | ⟨x, m₁⟩ :: ts₁, ⟨y, m₂⟩ :: ts₂, h => by
      simp only [targetsErase, List.map_cons, List.cons.injEq, Prod.mk.injEq] at h
      obtain ⟨⟨rfl, hi⟩, ht⟩ := h
      obtain ⟨-, hm⟩ := Mem.heq_of_index m₁ m₂ hi
      cases hm
      rw [targetsErase_inj ts₁ ts₂ ht]
  | [], _ :: _, h => by simp only [targetsErase, List.map_nil, List.map_cons, reduceCtorEq] at h
  | _ :: _, [], h => by simp only [targetsErase, List.map_nil, List.map_cons, reduceCtorEq] at h

mutual
theorem Stmt.erase_inj : ∀ {F c L} (s₁ s₂ : Stmt F c L), s₁.erase = s₂.erase → s₁ = s₂
  | _, _, _, .block b₁, s₂, h => by
      cases s₂ <;> simp only [Stmt.erase, UStmt.block.injEq, reduceCtorEq] at h
      rw [Block.erase_inj _ _ h]
  | _, _, _, .discard e₁, s₂, h => by
      cases s₂ <;> simp only [Stmt.erase, UStmt.discard.injEq, reduceCtorEq] at h
      rw [Expr.erase_inj _ _ h]
  | _, _, _, .assign ts₁ e₁, s₂, h => by
      cases s₂ <;> simp only [Stmt.erase, UStmt.assign.injEq, reduceCtorEq] at h
      obtain ⟨ht, he⟩ := h
      cases targetsErase_inj _ _ ht
      rw [Expr.erase_inj _ _ he]
  | _, _, _, .if_ e₁ b₁, s₂, h => by
      cases s₂ <;> simp only [Stmt.erase, UStmt.if_.injEq, reduceCtorEq] at h
      rw [Expr.erase_inj _ _ h.1, Block.erase_inj _ _ h.2]
  | _, _, _, .switch e₁ cs₁, s₂, h => by
      cases s₂ <;> simp only [Stmt.erase, UStmt.switch.injEq, reduceCtorEq] at h
      rw [Expr.erase_inj _ _ h.1, Cases.erase_inj _ _ h.2]
  | _, _, _, .switchDefault e₁ cs₁ b₁, s₂, h => by
      cases s₂ <;> simp only [Stmt.erase, UStmt.switchDefault.injEq, reduceCtorEq] at h
      rw [Expr.erase_inj _ _ h.1, Cases.erase_inj _ _ h.2.1, Block.erase_inj _ _ h.2.2]
  | _, _, _, .for_ lp₁, s₂, h => by
      cases s₂ <;> simp only [Stmt.erase, UStmt.for_.injEq, reduceCtorEq] at h
      rw [Loop.erase_inj _ _ h]
  | _, _, _, .leave, s₂, h => by
      cases s₂ <;> simp only [Stmt.erase, reduceCtorEq] at h
      rfl
  | _, _, _, .break_, s₂, h => by
      cases s₂ <;> simp only [Stmt.erase, reduceCtorEq] at h
      rfl
  | _, _, _, .continue_, s₂, h => by
      cases s₂ <;> simp only [Stmt.erase, reduceCtorEq] at h
      rfl
  termination_by _ _ _ x _ _ => sizeOf x

theorem Cases.erase_inj : ∀ {F c L} (c₁ c₂ : Cases F c L), c₁.erase = c₂.erase → c₁ = c₂
  | _, _, _, .nil, c₂, h => by
      cases c₂ <;> simp only [Cases.erase, reduceCtorEq] at h
      rfl
  | _, _, _, .cons l₁ b₁ r₁, c₂, h => by
      cases c₂ <;> simp only [Cases.erase, UCases.cons.injEq, reduceCtorEq] at h
      rw [Lit.eq_of_tok h.1, Block.erase_inj _ _ h.2.1, Cases.erase_inj _ _ h.2.2]
  termination_by _ _ _ x _ _ => sizeOf x

theorem Loop.erase_inj : ∀ {F c L} (l₁ l₂ : Loop F c L), l₁.erase = l₂.erase → l₁ = l₂
  | _, _, _, .stmt s₁ r₁, l₂, h => by
      cases l₂ <;> simp only [Loop.erase, ULoop.stmt.injEq, reduceCtorEq] at h
      rw [Stmt.erase_inj _ _ h.1, Loop.erase_inj _ _ h.2]
  | _, _, _, .let_ xs₁ i₁ r₁, l₂, h => by
      cases l₂ <;> simp only [Loop.erase, ULoop.let_.injEq, reduceCtorEq] at h
      obtain ⟨rfl, hi, hr⟩ := h
      rw [initErase_inj _ _ hi, Loop.erase_inj _ _ hr]
  | _, _, _, .run e₁ p₁ b₁, l₂, h => by
      cases l₂ <;> simp only [Loop.erase, ULoop.run.injEq, reduceCtorEq] at h
      rw [Expr.erase_inj _ _ h.1, Block.erase_inj _ _ h.2.1, Block.erase_inj _ _ h.2.2]
  termination_by _ _ _ x _ _ => sizeOf x

theorem Items.erase_inj : ∀ {F c L g} (i₁ i₂ : Items F c L g), i₁.erase = i₂.erase → i₁ = i₂
  | _, _, _, _, .nil, i₂, h => by
      cases i₂ <;> simp only [Items.erase, reduceCtorEq] at h
      rfl
  | _, _, _, _, .stmt s₁ r₁, i₂, h => by
      cases i₂ <;> simp only [Items.erase, UItems.stmt.injEq, reduceCtorEq] at h
      rw [Stmt.erase_inj _ _ h.1, Items.erase_inj _ _ h.2]
  | _, _, _, _, .let_ xs₁ e₁ r₁, i₂, h => by
      cases i₂ <;> simp only [Items.erase, UItems.let_.injEq, reduceCtorEq] at h
      obtain ⟨rfl, hi, hr⟩ := h
      rw [initErase_inj _ _ hi, Items.erase_inj _ _ hr]
  | _, _, _, _, .fn k₁ r₁, i₂, h => by
      cases i₂ <;> simp only [Items.erase, UItems.fn.injEq, reduceCtorEq] at h
      rw [Fin.ext h.1, Items.erase_inj _ _ h.2]
  termination_by _ _ _ _ x _ _ => sizeOf x

theorem Block.erase_inj : ∀ {F c L} (b₁ b₂ : Block F c L), b₁.erase = b₂.erase → b₁ = b₂
  | _, _, _, .mk ss₁ bs₁ is₁, .mk ss₂ bs₂ is₂, h => by
      simp only [Block.erase, UBlock.mk.injEq] at h
      obtain ⟨rfl, hb, hi⟩ := h
      rw [Bodies.erase_inj _ _ hb, Items.erase_inj _ _ hi]
  termination_by _ _ _ x _ _ => sizeOf x

theorem Bodies.erase_inj : ∀ {F ss} (b₁ b₂ : Bodies F ss), b₁.erase = b₂.erase → b₁ = b₂
  | _, _, .nil, .nil, _ => rfl
  | _, _, .cons x₁ r₁, .cons x₂ r₂, h => by
      simp only [Bodies.erase, UBodies.cons.injEq] at h
      rw [Block.erase_inj _ _ h.1, Bodies.erase_inj _ _ h.2]
  termination_by _ _ x _ _ => sizeOf x
end

mutual
theorem objectErase_inj : ∀ (o₁ o₂ : Object Code), objectErase o₁ = objectErase o₂ → o₁ = o₂
  | .object n₁ c₁ ch₁, o₂, h => by
      cases o₂ <;> simp only [objectErase, UObject.object.injEq, reduceCtorEq] at h
      rw [h.1, Block.erase_inj _ _ h.2.1, objectsErase_inj _ _ h.2.2]
  | .data n₁ b₁, o₂, h => by
      cases o₂ <;> simp only [objectErase, UObject.data.injEq, reduceCtorEq] at h
      rw [h.1, h.2]

theorem objectsErase_inj : ∀ (os₁ os₂ : List (Object Code)), objectsErase os₁ = objectsErase os₂ → os₁ = os₂
  | [], [], _ => rfl
  | o₁ :: r₁, o₂ :: r₂, h => by
      simp only [objectsErase, UObjects.cons.injEq] at h
      rw [objectErase_inj _ _ h.1, objectsErase_inj _ _ h.2]
  | [], _ :: _, h => by simp only [objectsErase, reduceCtorEq] at h
  | _ :: _, [], h => by simp only [objectsErase, reduceCtorEq] at h
end

end Solidity.SolcValidation.IrSyntax
