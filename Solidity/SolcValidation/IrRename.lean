import Solidity.SolcValidation.IrEval

/-!
# Moving IR code between function environments

A helper's body cut out of a large function group into a small one (the
extracted helper groups of `SolcValidation/IrHelpers.lean` and its siblings) is
the same text with different call memberships: calls point into a different
signature list. `Ren F G` maps memberships of `F` to memberships of `G`
partially (a function missing from the target maps to `none`), and `Expr.ren`
… `Bodies.ren` rename every call of a term, failing exactly when the term calls
a function the map leaves out. Locals, literals and operations are untouched,
so a renamed term has the same shape and is evaluated with the same fuel.

`Sim k ρ E E'` says that, up to fuel `k`, every function `ρ` maps is looked up
in `E'` as the renaming of its body in `E`, with closure environments again
related. `evalExpr_ren`/`evalBlock_ren` are the simulation: a renamed term evaluates in `E'`
exactly as the original evaluates in `E` (same machine effects, same result,
same fault), at every fuel. `Sim.flat` discharges `Sim` for a single top-level
group (the shape of an object's code) from one equation per mapped function.
-/
namespace Solidity.SolcValidation.IrSyntax
open Solidity.SolcValidation

/-- A partial map of function memberships, signature by signature. -/
abbrev Ren (F G : List FnSig) := ∀ {s : FnSig}, Mem F s → Option (Mem G s)

/-- A map that sends the head to `x` and the tail by `ρ`. -/
def Ren.cons {G : List FnSig} {a : FnSig} {as : List FnSig} (x : Option (Mem G a)) (ρ : Ren as G) :
    Ren (a :: as) G :=
  fun m => match m with
    | .here => x
    | .there m => ρ m

def Ren.nil {G : List FnSig} : Ren [] G := fun m => nomatch m

def Mem.inl {α : Type} {G : List α} {a : α} : (ss : List α) → Mem ss a → Mem (ss ++ G) a
  | _ :: _, .here => .here
  | _ :: ss, .there m => .there (Mem.inl ss m)

def Mem.inr {α : Type} {G : List α} {a : α} : (ss : List α) → Mem G a → Mem (ss ++ G) a
  | [], m => m
  | _ :: ss, m => .there (Mem.inr ss m)

/-- A block's own group is kept; outer functions are renamed. -/
def Ren.lift {F G : List FnSig} (ss : List FnSig) (ρ : Ren F G) : Ren (ss ++ F) (ss ++ G) :=
  fun m => match Mem.split ss m with
    | .inl h => some (Mem.inl ss h)
    | .inr o => (ρ o).map (Mem.inr ss)

theorem Mem.split_inl {α : Type} {G : List α} {a : α} :
    (ss : List α) → (h : Mem ss a) → Mem.split (F := G) ss (Mem.inl ss h) = .inl h
  | _ :: _, .here => rfl
  | _ :: ss, .there m => by
      simp only [Mem.inl, Mem.split, Mem.split_inl ss m, Sum.elim_inl]

theorem Mem.split_inr {α : Type} {G : List α} {a : α} :
    (ss : List α) → (o : Mem G a) → Mem.split ss (Mem.inr ss o) = .inr o
  | [], _ => rfl
  | _ :: ss, o => by
      simp only [Mem.inr, Mem.split, Mem.split_inr ss o, Sum.elim_inr]

section
variable {F G : List FnSig} (ρ : Ren F G) {L : List String}

mutual
def Expr.ren : {r : Nat} → Expr F L r → Option (Expr G L r)
  | _, .lit l => some (.lit l)
  | _, .var x m => some (.var x m)
  | _, .op o args =>
      match Args.ren args with
      | some a => some (.op o a)
      | none => none
  | _, .call m args =>
      match ρ m, Args.ren args with
      | some m', some a => some (.call m' a)
      | _, _ => none
  termination_by structural _ e => e

def Args.ren : {k : Nat} → Args F L k → Option (Args G L k)
  | _, .nil => some .nil
  | _, .cons e rest =>
      match Expr.ren e, Args.ren rest with
      | some e', some r' => some (.cons e' r')
      | _, _ => none
  termination_by structural _ a => a
end

end

def initRen {F G : List FnSig} (ρ : Ren F G) {L : List String} {xs : List String} :
    Option (Expr F L xs.length) → Option (Option (Expr G L xs.length))
  | none => some none
  | some e => (e.ren ρ).map some

mutual
def Stmt.ren : {F G : List FnSig} → Ren F G → {c : Ctl} → {L : List String} →
    Stmt F c L → Option (Stmt G c L)
  | _, _, ρ, _, _, .block b =>
      match b.ren ρ with | some b' => some (.block b') | none => none
  | _, _, ρ, _, _, .discard e =>
      match e.ren ρ with | some e' => some (.discard e') | none => none
  | _, _, ρ, _, _, .assign ts e =>
      match e.ren ρ with | some e' => some (.assign ts e') | none => none
  | _, _, ρ, _, _, .if_ e b =>
      match e.ren ρ, b.ren ρ with
      | some e', some b' => some (.if_ e' b')
      | _, _ => none
  | _, _, ρ, _, _, .switch e cs =>
      match e.ren ρ, cs.ren ρ with
      | some e', some cs' => some (.switch e' cs')
      | _, _ => none
  | _, _, ρ, _, _, .switchDefault e cs b =>
      match e.ren ρ, cs.ren ρ, b.ren ρ with
      | some e', some cs', some b' => some (.switchDefault e' cs' b')
      | _, _, _ => none
  | _, _, ρ, _, _, .for_ lp =>
      match lp.ren ρ with | some lp' => some (.for_ lp') | none => none
  | _, _, _, _, _, .leave => some .leave
  | _, _, _, _, _, .break_ => some .break_
  | _, _, _, _, _, .continue_ => some .continue_

def Cases.ren : {F G : List FnSig} → Ren F G → {c : Ctl} → {L : List String} →
    Cases F c L → Option (Cases G c L)
  | _, _, _, _, _, .nil => some .nil
  | _, _, ρ, _, _, .cons l b rest =>
      match b.ren ρ, rest.ren ρ with
      | some b', some r' => some (.cons l b' r')
      | _, _ => none

def Loop.ren : {F G : List FnSig} → Ren F G → {c : Ctl} → {L : List String} →
    Loop F c L → Option (Loop G c L)
  | _, _, ρ, _, _, .stmt st rest =>
      match st.ren ρ, rest.ren ρ with
      | some st', some r' => some (.stmt st' r')
      | _, _ => none
  | _, _, ρ, _, _, .let_ xs e rest =>
      match initRen ρ e, rest.ren ρ with
      | some e', some r' => some (.let_ xs e' r')
      | _, _ => none
  | _, _, ρ, _, _, .run e post body =>
      match e.ren ρ, post.ren ρ, body.ren ρ with
      | some e', some p', some b' => some (.run e' p' b')
      | _, _, _ => none

def Items.ren : {F G : List FnSig} → Ren F G → {c : Ctl} → {L : List String} → {g : Nat} →
    Items F c L g → Option (Items G c L g)
  | _, _, _, _, _, _, .nil => some .nil
  | _, _, ρ, _, _, _, .stmt st rest =>
      match st.ren ρ, rest.ren ρ with
      | some st', some r' => some (.stmt st' r')
      | _, _ => none
  | _, _, ρ, _, _, _, .let_ xs e rest =>
      match initRen ρ e, rest.ren ρ with
      | some e', some r' => some (.let_ xs e' r')
      | _, _ => none
  | _, _, ρ, _, _, _, .fn k rest =>
      match rest.ren ρ with | some r' => some (.fn k r') | none => none

def Block.ren : {F G : List FnSig} → Ren F G → {c : Ctl} → {L : List String} →
    Block F c L → Option (Block G c L)
  | _, _, ρ, _, _, .mk ss bodies items =>
      match bodies.ren (ρ.lift ss), items.ren (ρ.lift ss) with
      | some bs, some is => some (.mk ss bs is)
      | _, _ => none

def Bodies.ren : {F G : List FnSig} → Ren F G → {ss : List FnSig} →
    Bodies F ss → Option (Bodies G ss)
  | _, _, _, _, .nil => some .nil
  | _, _, ρ, _, .cons body rest =>
      match body.ren ρ, rest.ren ρ with
      | some b', some r' => some (.cons b' r')
      | _, _ => none
end

/-- Up to fuel `k`: each function `ρ` maps is the renaming of its source body,
in closure environments that are again related. -/
def Sim : Nat → {F G : List FnSig} → Ren F G → FunEnv F → FunEnv G → Prop
  | 0, _, _, _, _, _ => True
  | k + 1, _, _, ρ, E, E' => ∀ {s : FnSig} (m : _) (m' : _), ρ (s := s) m = some m' →
      ∃ ρ₀ : Ren (E.lookup m).scope (E'.lookup m').scope,
        Sim k ρ₀ (E.lookup m).env (E'.lookup m').env ∧
        (E.lookup m).body.ren ρ₀ = some (E'.lookup m').body

theorem Sim.mono : ∀ (k : Nat) {F G : List FnSig} (ρ : Ren F G) (E : FunEnv F) (E' : FunEnv G),
    Sim (k + 1) ρ E E' → Sim k ρ E E'
  | 0, _, _, _, _, _, _ => trivial
  | k + 1, _, _, _, _, _, h => fun m m' hm =>
      let ⟨ρ₀, hs, hb⟩ := h m m' hm
      ⟨ρ₀, Sim.mono k ρ₀ _ _ hs, hb⟩

theorem Bodies.ren_get : ∀ {F G : List FnSig} (ρ : Ren F G) {ss : List FnSig} (bs : Bodies F ss)
    (bs' : Bodies G ss), bs.ren ρ = some bs' → ∀ {s : FnSig} (m : Mem ss s),
    (bs.get m).ren ρ = some (bs'.get m)
  | _, _, _, _, .nil, _, _, _, m => nomatch m
  | _, _, ρ, _, .cons body rest, bs', h, _, m => by
      simp only [Bodies.ren] at h
      split at h
      · next b' r' hb hr =>
        cases h
        cases m with
        | here => exact hb
        | there m => exact Bodies.ren_get ρ rest r' hr m
      · cases h

theorem lookup_group_inl {F : List FnSig} {s : FnSig} (ss : List FnSig) (bs : Bodies (ss ++ F) ss)
    (E : FunEnv F) (m : Mem (ss ++ F) s) (h : Mem ss s) (hs : Mem.split ss m = .inl h) :
    (FunEnv.group ss bs E).lookup m = ⟨_, .group ss bs E, bs.get h⟩ := by
  simp only [FunEnv.lookup, hs]

theorem lookup_group_inr {F : List FnSig} {s : FnSig} (ss : List FnSig) (bs : Bodies (ss ++ F) ss)
    (E : FunEnv F) (m : Mem (ss ++ F) s) (o : Mem F s) (hs : Mem.split ss m = .inr o) :
    (FunEnv.group ss bs E).lookup m = E.lookup o := by
  simp only [FunEnv.lookup, hs]

/-- Installing related groups keeps environments related. -/
theorem Sim.group : ∀ (k : Nat) {F G : List FnSig} (ρ : Ren F G) (E : FunEnv F) (E' : FunEnv G)
    (ss : List FnSig) (bs : Bodies (ss ++ F) ss) (bs' : Bodies (ss ++ G) ss),
    Sim k ρ E E' → bs.ren (ρ.lift ss) = some bs' →
    Sim k (ρ.lift ss) (.group ss bs E) (.group ss bs' E')
  | 0, _, _, _, _, _, _, _, _, _, _ => trivial
  | k + 1, _, _, ρ, E, E', ss, bs, bs', hs, hb => by
      intro m m' hm
      simp only [Ren.lift] at hm
      cases hsplit : Mem.split ss m with
      | inl h =>
        rw [hsplit] at hm
        cases hm
        rw [lookup_group_inl ss bs E m h hsplit,
          lookup_group_inl ss bs' E' (Mem.inl ss h) h (Mem.split_inl ss h)]
        exact ⟨ρ.lift ss, Sim.group k ρ E E' ss bs bs' (Sim.mono k ρ E E' hs) hb,
          Bodies.ren_get _ bs bs' hb h⟩
      | inr o =>
        rw [hsplit] at hm
        cases ho : ρ o with
        | none => simp only [ho, Option.map] at hm; cases hm
        | some o' =>
          simp only [ho, Option.map, Option.some.injEq] at hm
          cases hm
          rw [lookup_group_inr ss bs E m o hsplit,
            lookup_group_inr ss bs' E' (Mem.inr ss o') o' (Mem.split_inr ss o')]
          exact hs o o' ho

/-- The position of a function in a top-level group (nothing is outside it). -/
def Mem.flat {α : Type} {a : α} (ss : List α) (m : Mem (ss ++ []) a) : Mem ss a :=
  match Mem.split ss m with
  | .inl h => h
  | .inr o => nomatch o

theorem Mem.split_flat {α : Type} {a : α} (ss : List α) (m : Mem (ss ++ []) a) :
    Mem.split ss m = .inl (Mem.flat ss m) := by
  unfold Mem.flat
  split
  · next h hs => exact hs
  · next o _ => exact nomatch o

/-- Two top-level groups are related at every fuel when each mapped function's
body renames to its image's body. -/
theorem Sim.flat {ss ts : List FnSig} (bs : Bodies (ss ++ []) ss) (bt : Bodies (ts ++ []) ts)
    (ρ : Ren (ss ++ []) (ts ++ []))
    (h : ∀ {s : FnSig} (m : Mem (ss ++ []) s) (m' : Mem (ts ++ []) s), ρ m = some m' →
      (bs.get (Mem.flat ss m)).ren ρ = some (bt.get (Mem.flat ts m'))) :
    ∀ k, Sim k ρ (.group ss bs .nil) (.group ts bt .nil)
  | 0 => trivial
  | k + 1 => by
    intro m m' hm
    rw [lookup_group_inl ss bs .nil m _ (Mem.split_flat ss m),
      lookup_group_inl ts bt .nil m' _ (Mem.split_flat ts m')]
    exact ⟨ρ, Sim.flat bs bt ρ h k, h m m' hm⟩

/-! ## The simulation -/

section
variable {σ : Type} (M : Machine σ) (ctx : ObjectCtx)

/-! The statement proved by induction on fuel, one per syntactic class. -/

def PExpr (k : Nat) : Prop :=
  ∀ {F G : List FnSig} (ρ : Ren F G) (E : FunEnv F) (E' : FunEnv G) {L : List String} {r : Nat}
      (e : Expr F L r) (e' : Expr G L r) (vs : Vals L) (s : σ),
      Sim k ρ E E' → e.ren ρ = some e' → evalExpr M ctx k E' e' vs s = evalExpr M ctx k E e vs s

def PArgs (k : Nat) : Prop :=
  ∀ {F G : List FnSig} (ρ : Ren F G) (E : FunEnv F) (E' : FunEnv G) {L : List String} {n : Nat}
      (a : Args F L n) (a' : Args G L n) (vs : Vals L) (s : σ),
      Sim k ρ E E' → a.ren ρ = some a' → evalArgs M ctx k E' a' vs s = evalArgs M ctx k E a vs s

def PStmt (k : Nat) : Prop :=
  ∀ {F G : List FnSig} (ρ : Ren F G) (E : FunEnv F) (E' : FunEnv G) {c : Ctl} {L : List String}
      (st : Stmt F c L) (st' : Stmt G c L) (vs : Vals L) (s : σ),
      Sim k ρ E E' → st.ren ρ = some st' → evalStmt M ctx k E' st' vs s = evalStmt M ctx k E st vs s

def PLoop (k : Nat) : Prop :=
  ∀ {F G : List FnSig} (ρ : Ren F G) (E : FunEnv F) (E' : FunEnv G) {c : Ctl} {L : List String}
      (lp : Loop F c L) (lp' : Loop G c L) (vs : Vals L) (s : σ),
      Sim k ρ E E' → lp.ren ρ = some lp' → evalLoop M ctx k E' lp' vs s = evalLoop M ctx k E lp vs s

def PIter (k : Nat) : Prop :=
  ∀ {F G : List FnSig} (ρ : Ren F G) (E : FunEnv F) (E' : FunEnv G) {c : Ctl} {L : List String}
      (cond : Expr F L 1) (cond' : Expr G L 1) (post : Block F ⟨c.function, false⟩ L)
      (post' : Block G ⟨c.function, false⟩ L) (body : Block F ⟨c.function, true⟩ L)
      (body' : Block G ⟨c.function, true⟩ L) (vs : Vals L) (s : σ),
      Sim k ρ E E' → cond.ren ρ = some cond' → post.ren ρ = some post' → body.ren ρ = some body' →
      iterate M ctx k E' cond' post' body' vs s = iterate M ctx k E cond post body vs s

def PInit (k : Nat) : Prop :=
  ∀ {F G : List FnSig} (ρ : Ren F G) (E : FunEnv F) (E' : FunEnv G) {L : List String}
      (xs : List String) (i : Option (Expr F L xs.length)) (i' : Option (Expr G L xs.length))
      (vs : Vals L) (s : σ),
      Sim k ρ E E' → initRen ρ i = some i' → evalInit M ctx k E' xs i' vs s = evalInit M ctx k E xs i vs s

def PItems (k : Nat) : Prop :=
  ∀ {F G : List FnSig} (ρ : Ren F G) (E : FunEnv F) (E' : FunEnv G) {c : Ctl} {L : List String} {g : Nat}
      (it : Items F c L g) (it' : Items G c L g) (vs : Vals L) (s : σ),
      Sim k ρ E E' → it.ren ρ = some it' → evalItems M ctx k E' it' vs s = evalItems M ctx k E it vs s

def PBlock (k : Nat) : Prop :=
  ∀ {F G : List FnSig} (ρ : Ren F G) (E : FunEnv F) (E' : FunEnv G) {c : Ctl} {L : List String}
      (b : Block F c L) (b' : Block G c L) (vs : Vals L) (s : σ),
      Sim k ρ E E' → b.ren ρ = some b' → evalBlock M ctx k E' b' vs s = evalBlock M ctx k E b vs s

def RenSim (k : Nat) : Prop :=
  PExpr M ctx k ∧ PArgs M ctx k ∧ PStmt M ctx k ∧ PLoop M ctx k ∧ PIter M ctx k ∧ PInit M ctx k ∧ PItems M ctx k ∧ PBlock M ctx k

theorem select_ren {F G : List FnSig} (ρ : Ren F G) {c : Ctl} {L : List String} :
    ∀ (cs : Cases F c L) (cs' : Cases G c L), cs.ren ρ = some cs' → ∀ v : Word,
      (cs.select v = none ∧ cs'.select v = none) ∨
      ∃ b b', cs.select v = some b ∧ cs'.select v = some b' ∧ b.ren ρ = some b'
  | .nil, cs', h, v => by
      simp only [Cases.ren, Option.some.injEq] at h
      subst h
      exact .inl ⟨rfl, rfl⟩
  | .cons l b rest, cs', h, v => by
      simp only [Cases.ren] at h
      split at h
      · next b' r' hb hr =>
        cases h
        simp only [Cases.select]
        by_cases hv : l.value = v
        · simp only [hv, if_true]
          exact .inr ⟨b, b', rfl, rfl, hb⟩
        · simp only [hv, if_false]
          exact select_ren ρ rest r' hr v
      · cases h

theorem bind_congr' {σ α β : Type} (x : Run σ α) (f g : α → Run σ β) (h : ∀ a, f a = g a) :
    x >>= f = x >>= g := by
  cases x with
  | error e => rfl
  | ok a => exact h a

section steps
variable {M ctx} {k : Nat} (ih : RenSim M ctx k)
include ih

theorem step_expr : PExpr M ctx (k + 1) := by
  obtain ⟨iE, iA, iS, iL, iI, iN, iT, iB⟩ := ih
  intro F G ρ E E' L r e e' vs s hs he
  have hs' : Sim k ρ E E' := Sim.mono k ρ E E' hs
  cases e with
  | lit l => simp only [Expr.ren, Option.some.injEq] at he; subst he; rfl
  | var x m => simp only [Expr.ren, Option.some.injEq] at he; subst he; rfl
  | op o args =>
    simp only [Expr.ren] at he
    split at he
    · next a ha =>
      cases he
      simp only [evalExpr]
      rw [iA ρ E E' args a vs s hs' ha]
    · cases he
  | call m args =>
    simp only [Expr.ren] at he
    split at he
    · next m' a hm ha =>
      cases he
      obtain ⟨ρ₀, h0, hb⟩ := hs m m' hm
      simp only [evalExpr]
      rw [iA ρ E E' args a vs s hs' ha]
      refine bind_congr' _ _ _ fun p => ?_
      rw [iB ρ₀ _ _ _ _ _ _ h0 hb]
    · cases he

theorem step_args : PArgs M ctx (k + 1) := by
  obtain ⟨iE, iA, iS, iL, iI, iN, iT, iB⟩ := ih
  intro F G ρ E E' L n a a' vs s hs ha
  have hs' : Sim k ρ E E' := Sim.mono k ρ E E' hs
  cases a with
  | nil => simp only [Args.ren, Option.some.injEq] at ha; subst ha; rfl
  | cons e rest =>
    simp only [Args.ren] at ha
    split at ha
    · next e' r' he hr =>
      cases ha
      simp only [evalArgs]
      rw [iA ρ E E' rest r' vs s hs' hr]
      refine bind_congr' _ _ _ fun p => ?_
      rw [iE ρ E E' e e' vs p.1 hs' he]
    · cases ha

theorem step_stmt : PStmt M ctx (k + 1) := by
  obtain ⟨iE, iA, iS, iL, iI, iN, iT, iB⟩ := ih
  intro F G ρ E E' c L st st' vs s hs hst
  have hs' : Sim k ρ E E' := Sim.mono k ρ E E' hs
  cases st with
  | block b =>
    simp only [Stmt.ren] at hst
    split at hst
    · next b' hb => cases hst; simp only [evalStmt]; rw [iB ρ E E' b b' vs s hs' hb]
    · cases hst
  | discard e =>
    simp only [Stmt.ren] at hst
    split at hst
    · next e' he => cases hst; simp only [evalStmt]; rw [iE ρ E E' e e' vs s hs' he]
    · cases hst
  | assign ts e =>
    simp only [Stmt.ren] at hst
    split at hst
    · next e' he => cases hst; simp only [evalStmt]; rw [iE ρ E E' e e' vs s hs' he]
    · cases hst
  | if_ e b =>
    simp only [Stmt.ren] at hst
    split at hst
    · next e' b' he hb =>
      cases hst
      simp only [evalStmt]
      rw [iE ρ E E' e e' vs s hs' he]
      refine bind_congr' _ _ _ fun p => ?_
      rw [iB ρ E E' b b' vs p.1 hs' hb]
    · cases hst
  | switch e cs =>
    simp only [Stmt.ren] at hst
    split at hst
    · next e' cs' he hc =>
      cases hst
      simp only [evalStmt]
      rw [iE ρ E E' e e' vs s hs' he]
      refine bind_congr' _ _ _ fun p => ?_
      rcases select_ren ρ cs cs' hc (p.2 0) with ⟨h1, h2⟩ | ⟨b, b', h1, h2, hb⟩
      · simp only [h1, h2]
      · simp only [h1, h2]; rw [iB ρ E E' b b' vs p.1 hs' hb]
    · cases hst
  | switchDefault e cs d =>
    simp only [Stmt.ren] at hst
    split at hst
    · next e' cs' d' he hc hd =>
      cases hst
      simp only [evalStmt]
      rw [iE ρ E E' e e' vs s hs' he]
      refine bind_congr' _ _ _ fun p => ?_
      rcases select_ren ρ cs cs' hc (p.2 0) with ⟨h1, h2⟩ | ⟨b, b', h1, h2, hb⟩
      · simp only [h1, h2, Option.getD]; rw [iB ρ E E' d d' vs p.1 hs' hd]
      · simp only [h1, h2, Option.getD]; rw [iB ρ E E' b b' vs p.1 hs' hb]
    · cases hst
  | for_ lp =>
    simp only [Stmt.ren] at hst
    split at hst
    · next lp' hl => cases hst; simp only [evalStmt]; rw [iL ρ E E' lp lp' vs s hs' hl]
    · cases hst
  | leave => simp only [Stmt.ren, Option.some.injEq] at hst; subst hst; rfl
  | break_ => simp only [Stmt.ren, Option.some.injEq] at hst; subst hst; rfl
  | continue_ => simp only [Stmt.ren, Option.some.injEq] at hst; subst hst; rfl

theorem step_loop : PLoop M ctx (k + 1) := by
  obtain ⟨iE, iA, iS, iL, iI, iN, iT, iB⟩ := ih
  intro F G ρ E E' c L lp lp' vs s hs hl
  have hs' : Sim k ρ E E' := Sim.mono k ρ E E' hs
  cases lp with
  | stmt st rest =>
    simp only [Loop.ren] at hl
    split at hl
    · next st' r' h1 h2 =>
      cases hl
      simp only [evalLoop]
      rw [iS ρ E E' st st' vs s hs' h1]
      refine bind_congr' _ _ _ fun p => ?_
      rw [iL ρ E E' rest r' _ _ hs' h2]
    · cases hl
  | let_ xs i rest =>
    simp only [Loop.ren] at hl
    split at hl
    · next i' r' h1 h2 =>
      cases hl
      simp only [evalLoop]
      rw [iN ρ E E' xs i i' vs s hs' h1]
      refine bind_congr' _ _ _ fun p => ?_
      rw [iL ρ E E' rest r' _ _ hs' h2]
    · cases hl
  | run e post body =>
    simp only [Loop.ren] at hl
    split at hl
    · next e' p' b' h1 h2 h3 =>
      cases hl
      simp only [evalLoop]
      rw [iI ρ E E' e e' post p' body b' vs s hs' h1 h2 h3]
    · cases hl

theorem step_iterate : PIter M ctx (k + 1) := by
  obtain ⟨iE, iA, iS, iL, iI, iN, iT, iB⟩ := ih
  intro F G ρ E E' c L cond cond' post post' body body' vs s hs h1 h2 h3
  have hs' : Sim k ρ E E' := Sim.mono k ρ E E' hs
  simp only [iterate]
  rw [iE ρ E E' cond cond' vs s hs' h1]
  refine bind_congr' _ _ _ fun p => ?_
  split
  · rfl
  · rw [iB ρ E E' body body' vs p.1 hs' h3]
    refine bind_congr' _ _ _ fun q => ?_
    split
    · rfl
    · rfl
    · rw [iB ρ E E' post post' _ _ hs' h2]
      refine bind_congr' _ _ _ fun r => ?_
      split
      · rfl
      · rw [iI ρ E E' cond cond' post post' body body' _ _ hs' h1 h2 h3]
    · rw [iB ρ E E' post post' _ _ hs' h2]
      refine bind_congr' _ _ _ fun r => ?_
      split
      · rfl
      · rw [iI ρ E E' cond cond' post post' body body' _ _ hs' h1 h2 h3]

theorem step_init : PInit M ctx (k + 1) := by
  obtain ⟨iE, iA, iS, iL, iI, iN, iT, iB⟩ := ih
  intro F G ρ E E' L xs i i' vs s hs hi
  have hs' : Sim k ρ E E' := Sim.mono k ρ E E' hs
  cases i with
  | none => simp only [initRen, Option.some.injEq] at hi; subst hi; rfl
  | some e =>
    simp only [initRen] at hi
    cases he : e.ren ρ with
    | none => simp only [he, Option.map] at hi; cases hi
    | some e' =>
      simp only [he, Option.map, Option.some.injEq] at hi
      subst hi
      simp only [evalInit]
      rw [iE ρ E E' e e' vs s hs' he]

theorem step_items : PItems M ctx (k + 1) := by
  obtain ⟨iE, iA, iS, iL, iI, iN, iT, iB⟩ := ih
  intro F G ρ E E' c L g it it' vs s hs hit
  have hs' : Sim k ρ E E' := Sim.mono k ρ E E' hs
  cases it with
  | nil => simp only [Items.ren, Option.some.injEq] at hit; subst hit; rfl
  | stmt st rest =>
    simp only [Items.ren] at hit
    split at hit
    · next st' r' h1 h2 =>
      cases hit
      simp only [evalItems]
      rw [iS ρ E E' st st' vs s hs' h1]
      refine bind_congr' _ _ _ fun p => ?_
      rw [iT ρ E E' rest r' _ _ hs' h2]
    · cases hit
  | let_ xs i rest =>
    simp only [Items.ren] at hit
    split at hit
    · next i' r' h1 h2 =>
      cases hit
      simp only [evalItems]
      rw [iN ρ E E' xs i i' vs s hs' h1]
      refine bind_congr' _ _ _ fun p => ?_
      rw [iT ρ E E' rest r' _ _ hs' h2]
    · cases hit
  | fn j rest =>
    simp only [Items.ren] at hit
    split at hit
    · next r' h2 =>
      cases hit
      simp only [evalItems]
      rw [iT ρ E E' rest r' _ _ hs' h2]
    · cases hit

theorem step_block : PBlock M ctx (k + 1) := by
  obtain ⟨iE, iA, iS, iL, iI, iN, iT, iB⟩ := ih
  intro F G ρ E E' c L b b' vs s hs hb
  have hs' : Sim k ρ E E' := Sim.mono k ρ E E' hs
  cases b with
  | mk ss bodies items =>
    simp only [Block.ren] at hb
    split at hb
    · next bs is h1 h2 =>
      cases hb
      simp only [evalBlock]
      exact iT _ _ _ items is vs s (Sim.group k ρ E E' ss bodies bs hs' h1) h2
    · cases hb

end steps

theorem renSim : ∀ k, RenSim M ctx k := by
  intro k
  induction k with
  | zero =>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      dsimp only [PExpr, PArgs, PStmt, PLoop, PIter, PInit, PItems, PBlock] <;> intros <;> rfl
  | succ k ih =>
    exact ⟨step_expr ih, step_args ih, step_stmt ih, step_loop ih, step_iterate ih, step_init ih,
      step_items ih, step_block ih⟩

/-- Renamed code evaluates in the target environment exactly as the original
does in the source environment: same machine effects, result and fault. -/
theorem evalExpr_ren (k : Nat) {F G : List FnSig} (ρ : Ren F G) (E : FunEnv F) (E' : FunEnv G)
    {L : List String} {r : Nat} (e : Expr F L r) (e' : Expr G L r) (vs : Vals L) (s : σ)
    (hs : Sim k ρ E E') (he : e.ren ρ = some e') :
    evalExpr M ctx k E' e' vs s = evalExpr M ctx k E e vs s := by
  obtain ⟨iE, -⟩ := renSim M ctx k
  exact iE ρ E E' e e' vs s hs he

theorem evalBlock_ren (k : Nat) {F G : List FnSig} (ρ : Ren F G) (E : FunEnv F) (E' : FunEnv G)
    {c : Ctl} {L : List String} (b : Block F c L) (b' : Block G c L) (vs : Vals L) (s : σ)
    (hs : Sim k ρ E E') (hb : b.ren ρ = some b') :
    evalBlock M ctx k E' b' vs s = evalBlock M ctx k E b vs s := by
  obtain ⟨-, -, -, -, -, -, -, iB⟩ := renSim M ctx k
  exact iB ρ E E' b b' vs s hs hb

end

end Solidity.SolcValidation.IrSyntax
