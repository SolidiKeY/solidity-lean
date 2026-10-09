import Solidity.Calculus.Decide
import Solidity.Calculus.Close

/-!
# The reduction on a scoped leaf

`sol_decide` on a scoped leaf `Valid φ` (`φ : Fml C []`, M6c wave 6b)
reduces `φ` itself: the updates pushed in by position (`Fml.toLS`), the
fragment checked on it (`Fml.inLS`), and the reads of writes eliminated
as before (`LFml.elim`).  The symbolic state (`SymS`) keeps one entry per
position of the context, the local's name and what an update bound it to,
so a read of a local is a read of its position, and a pop or a frame's
drop is a pop or a drop of the entries.

What the reduction produces is the erased reduction's formula, exactly
(`Fml.toLS_eq`, the fragment with it), so `NFml.valid_iff_reduce` (the reduction
is exact on the erasure) and `Valid.of_erase` (a leaf is valid where its
erasure is) give its soundness, `Valid.of_reduceS`, with no erasure
computed: the leaf's terms are lowered from their positions, and only two
syntactic tests compare terms by their erasure (`sameAt`, an equation's
two readings; `allocPairS?`, an allocation's pair).

The symbolic state keeps, beside the positions, the erased reduction's
`Sym`: its bindings by name, newest first, which two checks read where the
scope no longer has the name.  A quantifier's local must be read by no
binding made so far, a popped local's included (`Sym.vars`); a hidden
binder's local starts at its name's last binding (`SymS.push`), as the
erasure reads it, since a hidden binder erases to nothing.  The atoms of
the reduction (`LTerm.var`) keep the names of the leaf's binders: `DecideLang`
is a symbol library and does not port (decision 78).

The erasure drops two constructors, an update of pops and a hidden binder;
an equation `eqD a b` is recognised through them (`Fml.peelS`), as the
erased reduction recognises it on the erasure (`NFml.eqDView`).

What the kernel evaluates (`Fml.inLS` checked, `Fml.toLS` unfolded by
`sol_decide`) is written by the recursors (Gate G0, conditions 1 and 2),
each with its `match` form as the compiled twin (`…M`) and a link theorem
(`…_eq_…M`); the proofs are stated on the twins and carried across.
-/

namespace Solidity

namespace Decide

open Semantics SemanticsProperties

variable {C : Contract}

/-! ## The symbolic state, by position -/

/-- The updates so far on a scoped leaf: per position of the context, the
innermost first, the local's name and what an update bound it to (`none`:
nothing, a free local); and the erased reduction's state (`Sym`), its
bindings by name, the storage and the memory. -/
structure SymS where
  loc : List (Var × Option SymB)
  sym : Sym

/-- No update yet, no local. -/
def SymS.empty : SymS := ⟨[], Sym.empty⟩

/-- The names of the context's positions, the innermost first. -/
def SymS.names (ρ : SymS) : List Var := ρ.loc.map Prod.fst

/-- What the local at position `n` is bound to. -/
def SymS.get (ρ : SymS) (n : Nat) : Option SymB := (ρ.loc[n]?).bind Prod.snd

/-- The positions agree with the bindings by name: the local at each
position, named as `ns` says, is bound to its name's last binding. -/
def SymS.Ok (ns : List Var) (ρ : SymS) : Prop :=
  ρ.loc = ns.map fun y => (y, lookupBy y ρ.sym.env)

theorem SymS.names_of_ok {ns : List Var} {ρ : SymS} (h : ρ.Ok ns) : ρ.names = ns := by
  unfold SymS.Ok at h
  simp only [SymS.names, h, List.map_map, Function.comp_def, List.map_id']

theorem SymS.get_of_ok {ns : List Var} {ρ : SymS} (h : ρ.Ok ns) {Γ : Ctx} {t : LTy}
    (hl : ns.length = Γ.length) (i : Idx Γ t) :
    ρ.get i.toNat = lookupBy (i.name ns) ρ.sym.env := by
  have hi : i.toNat < ns.length := hl ▸ i.toNat_lt
  unfold SymS.Ok at h
  simp only [SymS.get, h, List.getElem?_map, List.getElem?_eq_getElem hi, Option.map_some,
    Option.bind_some, Idx.name, List.getD_eq_getElem?_getD, Option.getD_some]

/-- `Idx.toNat`, by the recursor. -/
@[implemented_by Idx.toNat]
def _root_.Solidity.Idx.toNatR {Γ : Ctx} {t : LTy} (i : Idx Γ t) : Nat :=
  Idx.rec (motive := fun _ _ _ => Nat) 0 (fun _ ih => ih + 1) i

theorem _root_.Solidity.Idx.toNatR_eq {Γ : Ctx} {t : LTy} (i : Idx Γ t) : i.toNatR = i.toNat := by
  induction i with
  | here => rfl
  | there i ih => exact congrArg (· + 1) ih

/-! ## Terms, by position -/

section Terms

variable {Γ : Ctx}

/-- The storage a storage variable is bound to (`Surface.Tm.storLocal?`). -/
def _root_.Solidity.Tm.storLocalS (ρ : SymS) : Tm C Γ .st → Option LStor
  | .pvS i =>
    match ρ.get i.toNatR with
    | some (.stor s) => some s
    | _ => none
  | _ => none

/-- `storage` itself (`Surface.Tm.isStorage`). -/
def _root_.Solidity.Tm.isStorageS {s : Srt} : Tm C Γ s → Bool
  | .app0 .storage => true
  | _ => false

/-- A storage variable (`Surface.Tm.isPvS`). -/
def _root_.Solidity.Tm.isPvSS : Tm C Γ .st → Bool
  | .pvS _ => true
  | _ => false

/-- `Op2.toLAt`, by position. -/
def _root_.Solidity.Op2.toLAtS {a b s : Srt} (ρ : SymS) : Op2 a b s → Tm C Γ a → a.LTy → b.LTy →
    s.LTy
  | .find, t, x, y =>
    match t.storLocalS ρ with
    | some st => .seq (guardPath ρ.sym.stor y) (.findP st y)
    | none => .find x y
  | o, _, x, y => o.toL x y

/-- The type `addM(memory)` allocates (`addMOf?`). -/
def addMOfS? : Tm C Γ .mem → Option RefTy
  | .app1 (.addM R) _ (.app0 .memory) => some R
  | _ => none

/-- The type `freshId(addM(memory))`, written as a reference, allocates
(`allocRefOf?`). -/
def allocRefOfS? : Tm C Γ .mv → Option RefTy
  | .app1 .ref _ (.app1 (.alloc R) _ (.app0 .memory)) => some R
  | _ => none

/-- `freshRef`, by position. -/
def freshRefS (ρ : SymS) (m : Tm C Γ .mem) (v : Tm C Γ .mv) (z : Option (LMV × LTerm)) :
    Option (LMV × LTerm) :=
  match addMOfS? m, allocRefOfS? v with
  | some R, some R' =>
    if R = R' then some (.ref key{ idC(‹ρ.sym.mem.nAlloc›, nil) }, key{ true }) else z
  | _, _ => z

/-- `Op3.toLAt`, by position. -/
def _root_.Solidity.Op3.toLAtS {a b c s : Srt} (ρ : SymS) : Op3 a b c s → Tm C Γ a → Tm C Γ c →
    a.LTy → b.LTy → c.LTy → s.LTy
  | .write, m, v, x, y, z => writeM x y (freshRefS ρ m v z)
  | o, _, _, x, y, z => o.toL x y z

/-- `Tm.toLS`'s compiled twin. -/
def _root_.Solidity.Tm.toLSM (ρ : SymS) : {s : Srt} → Tm C Γ s → s.LTy
  | _, .pvV i =>
    match ρ.get i.toNat with
    | some (.val t) => t
    | some (.path _) | some (.stale _) | some (.stor _) | some (.mref _) | some .unset => .err
    | none => .var (i.name ρ.names)
  | _, .pvP i =>
    match ρ.get i.toNat with
    | some (.path q) => q
    | _ => .undef
  | _, .pvS _ => .init
  | _, .pvI i =>
    match ρ.get i.toNat with
    | some (.mref j) => some (j, .lit (.bool true))
    | _ => none
  | _, .netOf _ _ => .err
  | _, .app0 o => o.toL ρ.sym
  | _, .app1 o _ a => o.toL (a.toLSM ρ)
  | _, .app2 o a b => Op2.toLAtS ρ o a (a.toLSM ρ) (b.toLSM ρ)
  | _, .app3 o a b c => Op3.toLAtS ρ o a c (a.toLSM ρ) (b.toLSM ρ) (c.toLSM ρ)

/-- **A term with the updates pushed in, its locals read by position**
(`Surface.Tm.toL`), by the recursor. -/
@[implemented_by Tm.toLSM]
def _root_.Solidity.Tm.toLS (ρ : SymS) {s : Srt} (t : Tm C Γ s) : s.LTy :=
  Tm.rec (motive := fun s _ => s.LTy)
    (fun i =>
      match ρ.get i.toNatR with
      | some (.val t) => t
      | some (.path _) | some (.stale _) | some (.stor _) | some (.mref _) | some .unset => .err
      | none => .var (i.nameR ρ.names))
    (fun i =>
      match ρ.get i.toNatR with
      | some (.path q) => q
      | _ => .undef)
    (fun _ => .init)
    (fun i =>
      match ρ.get i.toNatR with
      | some (.mref j) => some (j, .lit (.bool true))
      | _ => none)
    (fun _ _ _ => .err) (fun o => o.toL ρ.sym) (fun o _ _ ih => o.toL ih)
    (fun o a _ iha ihb => Op2.toLAtS ρ o a iha ihb)
    (fun o a _ c iha ihb ihc => Op3.toLAtS ρ o a c iha ihb ihc) t

/-- `Op2.inL`, by position. -/
def _root_.Solidity.Op2.inLS {a b s : Srt} (ρ : SymS) : Op2 a b s → Tm C Γ a → a.LTy → b.LTy →
    Bool → Bool → Bool
  | .binop .., _, _, _, ha, hb | .at, _, _, _, ha, hb => ha && hb
  | .find, s, _, _, _, hb => (s.isStorageS || (s.storLocalS ρ).isSome) && hb
  | .len, s, _, _, _, hb | .delAt, s, _, _, _, hb | .sfind, s, _, _, _, hb => s.isStorageS && hb
  | .pushSlot _, s, _, _, _, hb | .extend _, s, _, _, _, hb | .pop, s, _, _, _, hb
  | .shrink, s, _, _, _, hb =>
    s.isStorageS && hb
  | .read, _, x, y, ha, hb => ha && hb && (readM x y).isSome
  | .mlen, _, x, y, ha, hb => ha && hb && (lenM x y).isSome
  | .mat, _, _, _, ha, hb => ha && hb
  | .iread, _, x, y, ha, hb => ha && hb && irOk ρ.sym (ireadM x y)
  | .copySt, _, x, y, ha, hb => ha && hb && (newM x y).isSome
  | .copyMem, _, x, y, ha, hb => ha && hb && (memL x y).isSome
  | _, _, _, _, _, _ => false

/-- `Op3.inL`, by position. -/
def _root_.Solidity.Op3.inLS {a b c s : Srt} (ρ : SymS) : Op3 a b c s → Tm C Γ a → Tm C Γ c →
    a.LTy → b.LTy → c.LTy → Bool → Bool → Bool → Bool
  | .ite, _, _, _, _, _, hc, ha, hb => hc && ha && hb
  | .save, s, _, _, _, z, _, hp, hv => s.isStorageS && hp && hv && z.storable
  | .push, s, .app1 .sval _ _, _, _, _, _, hp, hv | .push, s, .app2 .sfind _ _, _, _, _, _, hp, hv =>
    s.isStorageS && hp && hv
  | .write, m, v, x, y, z, hm, ha, hv =>
    hm && ha && (hv || (freshRefS ρ m v none).isSome) && (writeM x y (freshRefS ρ m v z)).isSome
  | _, _, _, _, _, _, _, _, _ => false

/-- `Tm.inLS`'s compiled twin. -/
def _root_.Solidity.Tm.inLSM (ρ : SymS) : {s : Srt} → Tm C Γ s → Bool
  | _, .pvV _ => true
  | _, .pvP i =>
    match ρ.get i.toNat with
    | some (.path _) | some (.val _) => true
    | some (.stale _) | some (.stor _) | some (.mref _) | some .unset | none => false
  | _, .pvS _ => false
  | _, .pvI i =>
    match ρ.get i.toNat with
    | some (.mref _) => true
    | _ => false
  | _, .netOf _ _ => false
  | _, .app0 o => o.inL
  | _, .app1 o _ a => o.inL (a.toLSM ρ) (a.inLSM ρ)
  | _, .app2 o a b => Op2.inLS ρ o a (a.toLSM ρ) (b.toLSM ρ) (a.inLSM ρ) (b.inLSM ρ)
  | _, .app3 o a b c =>
    Op3.inLS ρ o a c (a.toLSM ρ) (b.toLSM ρ) (c.toLSM ρ) (a.inLSM ρ) (b.inLSM ρ) (c.inLSM ρ)

/-- **The fragment, by position** (`Surface.Tm.inL`), by the recursor. -/
@[implemented_by Tm.inLSM]
def _root_.Solidity.Tm.inLS (ρ : SymS) {s : Srt} (t : Tm C Γ s) : Bool :=
  Tm.rec (motive := fun _ _ => Bool)
    (fun _ => true)
    (fun i =>
      match ρ.get i.toNatR with
      | some (.path _) | some (.val _) => true
      | some (.stale _) | some (.stor _) | some (.mref _) | some .unset | none => false)
    (fun _ => false)
    (fun i =>
      match ρ.get i.toNatR with
      | some (.mref _) => true
      | _ => false)
    (fun _ _ _ => false) (fun o => o.inL) (fun o _ a ih => o.inL (a.toLS ρ) ih)
    (fun o a b iha ihb => Op2.inLS ρ o a (a.toLS ρ) (b.toLS ρ) iha ihb)
    (fun o a b c iha ihb ihc =>
      Op3.inLS ρ o a c (a.toLS ρ) (b.toLS ρ) (c.toLS ρ) iha ihb ihc) t

/-- The recursor's reading is the twin's. -/
theorem _root_.Solidity.Tm.toLS_eq_toLSM (ρ : SymS) {s : Srt} (t : Tm C Γ s) :
    t.toLS ρ = t.toLSM ρ := by
  induction t with
  | pvV i | pvP i | pvI i => simp only [Tm.toLSM, ← Idx.toNatR_eq, ← Idx.nameR_eq]; rfl
  | pvS _ | netOf _ _ | app0 _ => rfl
  | app1 o _ x ih => simp only [Tm.toLSM, ← ih]; rfl
  | app2 o x y ihx ihy => simp only [Tm.toLSM, ← ihx, ← ihy]; rfl
  | app3 o x y z ihx ihy ihz => simp only [Tm.toLSM, ← ihx, ← ihy, ← ihz]; rfl

theorem _root_.Solidity.Tm.inLS_eq_inLSM (ρ : SymS) {s : Srt} (t : Tm C Γ s) :
    t.inLS ρ = t.inLSM ρ := by
  induction t with
  | pvP i | pvI i => simp only [Tm.inLSM, ← Idx.toNatR_eq]; rfl
  | pvV _ | pvS _ | netOf _ _ | app0 _ => rfl
  | app1 o _ x ih => simp only [Tm.inLSM, ← ih, ← Tm.toLS_eq_toLSM]; rfl
  | app2 o x y ihx ihy => simp only [Tm.inLSM, ← ihx, ← ihy, ← Tm.toLS_eq_toLSM]; rfl
  | app3 o x y z ihx ihy ihz =>
    simp only [Tm.inLSM, ← ihx, ← ihy, ← ihz, ← Tm.toLS_eq_toLSM]; rfl

/-! ### The same as the erasure's -/

variable {ns : List Var} {ρ : SymS}

theorem _root_.Solidity.Tm.storLocalS_eq (hok : ρ.Ok ns) (hl : ns.length = Γ.length)
    (t : Tm C Γ .st) : t.storLocalS ρ = (t.erase ns).storLocal? ρ.sym := by
  cases t with
  | pvS i =>
    simp only [Tm.storLocalS, Tm.erase, Surface.Tm.storLocal?, Idx.toNatR_eq, SymS.get_of_ok hok hl i]
    rcases lookupBy (i.name ns) ρ.sym.env with _ | b
    · rfl
    · cases b <;> rfl
  | _ => rfl

theorem _root_.Solidity.Tm.isStorageS_eq {s : Srt} (t : Tm C Γ s) :
    t.isStorageS = (t.erase ns).isStorage := by
  cases t with
  | app0 o => cases o <;> rfl
  | _ => rfl

theorem _root_.Solidity.Tm.isPvSS_eq (t : Tm C Γ .st) : t.isPvSS = (t.erase ns).isPvS := by
  cases t <;> rfl

theorem addMOfS?_eq (m : Tm C Γ .mem) : addMOfS? m = addMOf? (m.erase ns) := by
  cases m with
  | app1 o ho x =>
    cases o <;> first | rfl | (cases x with | app0 o' => cases o' <;> rfl | _ => rfl)
  | app2 o x y => cases o <;> rfl
  | app3 o x y z => cases o <;> rfl
  | app0 o => cases o <;> rfl

theorem allocRefOfS?_eq (v : Tm C Γ .mv) : allocRefOfS? v = allocRefOf? (v.erase ns) := by
  cases v with
  | app1 o ho x =>
    cases o with
    | ref =>
      cases x with
      | app1 o' ho' y =>
        cases o' with
        | alloc R => cases y with
          | app0 o'' => cases o'' <;> rfl
          | _ => rfl
        | _ => rfl
      | _ => rfl
    | _ => rfl
  | app2 o x y => cases o <;> rfl
  | app3 o x y z => cases o <;> rfl
  | app0 o => cases o <;> rfl

theorem freshRefS_eq (m : Tm C Γ .mem) (v : Tm C Γ .mv) (z : Option (LMV × LTerm)) :
    freshRefS ρ m v z = freshRef ρ.sym (m.erase ns) (v.erase ns) z := by
  unfold freshRefS freshRef
  rw [addMOfS?_eq (ns := ns) m, allocRefOfS?_eq (ns := ns) v]
  rcases addMOf? (m.erase ns) with _ | _ <;> rcases allocRefOf? (v.erase ns) with _ | _ <;> rfl

theorem _root_.Solidity.Op2.toLAtS_eq (hok : ρ.Ok ns) (hl : ns.length = Γ.length) {a b s : Srt}
    (o : Op2 a b s) (t : Tm C Γ a) (x : a.LTy) (y : b.LTy) :
    Op2.toLAtS ρ o t x y = Op2.toLAt ρ.sym o (t.erase ns) x y := by
  cases o with
  | find =>
    simp only [Op2.toLAtS, Op2.toLAt, Tm.storLocalS_eq hok hl t]
    rcases (t.erase ns).storLocal? ρ.sym with _ | _ <;> rfl
  | _ => rfl

theorem _root_.Solidity.Op3.toLAtS_eq {a b c s : Srt} (o : Op3 a b c s) (t : Tm C Γ a)
    (u : Tm C Γ c) (x : a.LTy) (y : b.LTy) (z : c.LTy) :
    Op3.toLAtS ρ o t u x y z = Op3.toLAt ρ.sym o (t.erase ns) (u.erase ns) x y z := by
  cases o with
  | write => simp only [Op3.toLAtS, Op3.toLAt, freshRefS_eq (ns := ns)]
  | _ => rfl

theorem _root_.Solidity.Tm.toLSM_eq (hok : ρ.Ok ns) (hl : ns.length = Γ.length) :
    {s : Srt} → (t : Tm C Γ s) → t.toLSM ρ = (t.erase ns).toL ρ.sym
  | _, .pvV i => by
    simp only [Tm.toLSM, Tm.erase, Surface.Tm.toL, SymS.get_of_ok hok hl i, SymS.names_of_ok hok]
    rcases lookupBy (i.name ns) ρ.sym.env with _ | b
    · rfl
    · cases b <;> rfl
  | _, .pvP i => by
    simp only [Tm.toLSM, Tm.erase, Surface.Tm.toL, SymS.get_of_ok hok hl i]
    rcases lookupBy (i.name ns) ρ.sym.env with _ | b
    · rfl
    · cases b <;> rfl
  | _, .pvS _ => rfl
  | _, .pvI i => by
    simp only [Tm.toLSM, Tm.erase, Surface.Tm.toL, SymS.get_of_ok hok hl i]
    rcases lookupBy (i.name ns) ρ.sym.env with _ | b
    · rfl
    · cases b <;> rfl
  | _, .netOf _ _ => rfl
  | _, .app0 _ => rfl
  | _, .app1 o _ a => by
    simp only [Tm.toLSM, Tm.erase, Surface.Tm.toL, Tm.toLSM_eq hok hl a]
  | _, .app2 o a b => by
    simp only [Tm.toLSM, Tm.erase, Surface.Tm.toL, Tm.toLSM_eq hok hl a, Tm.toLSM_eq hok hl b,
      Op2.toLAtS_eq hok hl]
  | _, .app3 o a b c => by
    simp only [Tm.toLSM, Tm.erase, Surface.Tm.toL, Tm.toLSM_eq hok hl a, Tm.toLSM_eq hok hl b,
      Tm.toLSM_eq hok hl c, Op3.toLAtS_eq (ns := ns)]

/-- **A term reads as its erasure**: lowered by position, it is what the
erased reduction lowers by name. -/
theorem _root_.Solidity.Tm.toLS_eq (hok : ρ.Ok ns) (hl : ns.length = Γ.length) {s : Srt}
    (t : Tm C Γ s) : t.toLS ρ = (t.erase ns).toL ρ.sym :=
  (Tm.toLS_eq_toLSM ρ t).trans (Tm.toLSM_eq hok hl t)

theorem _root_.Solidity.Op2.inLS_eq (hok : ρ.Ok ns) (hl : ns.length = Γ.length) {a b s : Srt}
    (o : Op2 a b s) (t : Tm C Γ a) (x : a.LTy) (y : b.LTy) (ha hb : Bool) :
    Op2.inLS ρ o t x y ha hb = Op2.inL ρ.sym o (t.erase ns) x y ha hb := by
  cases o <;>
    simp only [Op2.inLS, Op2.inL, Tm.isStorageS_eq (ns := ns), Tm.storLocalS_eq hok hl]

theorem _root_.Solidity.Op3.inLS_eq {a b c s : Srt} (o : Op3 a b c s) (t : Tm C Γ a)
    (u : Tm C Γ c) (x : a.LTy) (y : b.LTy) (z : c.LTy) (h₁ h₂ h₃ : Bool) :
    Op3.inLS ρ o t u x y z h₁ h₂ h₃ = Op3.inL ρ.sym o (t.erase ns) (u.erase ns) x y z h₁ h₂ h₃ := by
  cases o with
  | push =>
    cases u with
    | app1 o _ _ => cases o <;> simp only [Op3.inLS, Op3.inL, Tm.isStorageS_eq (ns := ns), Tm.erase]
    | app2 o _ _ => cases o <;> simp only [Op3.inLS, Op3.inL, Tm.isStorageS_eq (ns := ns), Tm.erase]
    | _ => rfl
  | write => simp only [Op3.inLS, Op3.inL, freshRefS_eq (ns := ns)]
  | save => simp only [Op3.inLS, Op3.inL, Tm.isStorageS_eq (ns := ns)]
  | _ => rfl

theorem _root_.Solidity.Tm.inLSM_eq (hok : ρ.Ok ns) (hl : ns.length = Γ.length) :
    {s : Srt} → (t : Tm C Γ s) → t.inLSM ρ = (t.erase ns).inL ρ.sym
  | _, .pvV _ => rfl
  | _, .pvP i => by
    simp only [Tm.inLSM, Tm.erase, Surface.Tm.inL, SymS.get_of_ok hok hl i]
    rcases lookupBy (i.name ns) ρ.sym.env with _ | b
    · rfl
    · cases b <;> rfl
  | _, .pvS _ => rfl
  | _, .pvI i => by
    simp only [Tm.inLSM, Tm.erase, Surface.Tm.inL, SymS.get_of_ok hok hl i]
    rcases lookupBy (i.name ns) ρ.sym.env with _ | b
    · rfl
    · cases b <;> rfl
  | _, .netOf _ _ => rfl
  | _, .app0 _ => rfl
  | _, .app1 o _ a => by
    simp only [Tm.inLSM, Tm.erase, Surface.Tm.inL, Tm.toLSM_eq hok hl a, Tm.inLSM_eq hok hl a]
  | _, .app2 o a b => by
    simp only [Tm.inLSM, Tm.erase, Surface.Tm.inL, Tm.toLSM_eq hok hl a, Tm.toLSM_eq hok hl b,
      Tm.inLSM_eq hok hl a, Tm.inLSM_eq hok hl b, Op2.inLS_eq hok hl]
  | _, .app3 o a b c => by
    simp only [Tm.inLSM, Tm.erase, Surface.Tm.inL, Tm.toLSM_eq hok hl a, Tm.toLSM_eq hok hl b,
      Tm.toLSM_eq hok hl c, Tm.inLSM_eq hok hl a, Tm.inLSM_eq hok hl b, Tm.inLSM_eq hok hl c,
      Op3.inLS_eq (ns := ns)]

/-- **The fragment is the erasure's.** -/
theorem _root_.Solidity.Tm.inLS_eq (hok : ρ.Ok ns) (hl : ns.length = Γ.length) {s : Srt}
    (t : Tm C Γ s) : t.inLS ρ = (t.erase ns).inL ρ.sym :=
  (Tm.inLS_eq_inLSM ρ t).trans (Tm.inLSM_eq hok hl t)

/-! ### Equations and stale writes -/

/-- `Op2.shape`, by position. -/
def _root_.Solidity.Op2.shapeS {a b s : Srt} : Op2 a b s → Tm C Γ a → Bool → Bool → Bool
  | .binop .., _, x, y | .at, _, x, y => x && y
  | .find, s, _, y => (s.isStorageS || s.isPvSS) && y
  | .len, s, _, y => s.isStorageS && y
  | _, _, _, _ => false

/-- The terms `sameAt` compares (`Surface.Tm.sameShape`). -/
def _root_.Solidity.Tm.sameShapeS : {s : Srt} → Tm C Γ s → Bool
  | _, .pvV _ | _, .pvP _ => true
  | _, .pvS _ | _, .pvI _ | _, .netOf _ _ => false
  | _, .app0 o => match o with
    | .lit _ | .env _ | .root _ => true
    | _ => false
  | _, .app1 o _ a => o.shape a.sameShapeS
  | _, .app2 o a b => o.shapeS a a.sameShapeS b.sameShapeS
  | _, .app3 o a b c => match o with
    | .ite => a.sameShapeS && b.sameShapeS && c.sameShapeS
    | _ => false

/-- A literal or a local (`Term.isAtom`). -/
def _root_.Solidity.Tm.isAtomS : Tm C Γ .val → Bool
  | .app0 (.lit _) | .pvV _ => true
  | _ => false

/-- A literal, or a value of the transaction (`Term.isLitLike`). -/
def _root_.Solidity.Tm.isLitLikeS : Tm C Γ .val → Bool
  | .app0 (.lit _) | .app0 (.env _) => true
  | _ => false

/-- A total equation the fragment takes (`Term.eqLit`). -/
def _root_.Solidity.Tm.eqLitS (a b : Tm C Γ .val) : Bool :=
  (a.isLitLikeS && b.isAtomS) || (b.isLitLikeS && a.isAtomS)

/-- The slot-level path of a stale alias, and of its members
(`Surface.Tm.slotPath?`). -/
def _root_.Solidity.Tm.slotPathS (ρ : SymS) : {u : Srt} → Tm C Γ u → Option LPath
  | _, .pvP i =>
    match ρ.get i.toNatR with
    | some (.stale q) => some q
    | _ => none
  | _, .app1 (.field f) _ p => (Tm.slotPathS ρ p).map fun q => key{ q.f }
  | _, _ => none

/-- A write through a stale alias (`STerm.staleWrite?`). -/
def _root_.Solidity.Tm.staleWriteS (ρ : SymS) : Tm C Γ .st → Option (Option AOp × LPath × Tm C Γ .val)
  | .app3 .save (.app0 .storage) p (.app1 .sval _ t) => (p.slotPathS ρ).map fun q => (none, q, t)
  | .app3 .push (.app0 .storage) p (.app1 .sval _ t) =>
    (p.slotPathS ρ).map fun q => (some .push, q, t)
  | _ => none

/-- A storage update pushed in (`STerm.toLS`). -/
def _root_.Solidity.Tm.toLSt (ρ : SymS) (s : Tm C Γ .st) : LStor :=
  match s.staleWriteS ρ with
  | some (op, q, t) => .stale op ρ.sym.stor q (t.toLS ρ)
  | none => s.toLS ρ

/-- The storage updates `toLSt` is exact on (`STerm.inLS`). -/
def _root_.Solidity.Tm.inLSt (ρ : SymS) (s : Tm C Γ .st) : Bool :=
  match s.staleWriteS ρ with
  | some (_, _, t) => t.inLS ρ
  | none => s.inLS ρ

theorem _root_.Solidity.Op2.shapeS_eq {a b s : Srt} (o : Op2 a b s) (t : Tm C Γ a) (x y : Bool) :
    o.shapeS t x y = o.shape (t.erase ns) x y := by
  cases o <;> simp only [Op2.shapeS, Op2.shape, Tm.isStorageS_eq (ns := ns), Tm.isPvSS_eq (ns := ns)]

theorem _root_.Solidity.Tm.sameShapeS_eq : {s : Srt} → (t : Tm C Γ s) →
    t.sameShapeS = (t.erase ns).sameShape
  | _, .pvV _ | _, .pvP _ | _, .pvS _ | _, .pvI _ | _, .netOf _ _ => rfl
  | _, .app0 o => by cases o <;> rfl
  | _, .app1 o _ a => by
    simp only [Tm.sameShapeS, Tm.erase, Surface.Tm.sameShape, Tm.sameShapeS_eq a]
  | _, .app2 o a b => by
    simp only [Tm.sameShapeS, Tm.erase, Surface.Tm.sameShape, Tm.sameShapeS_eq a,
      Tm.sameShapeS_eq b, Op2.shapeS_eq (ns := ns)]
  | _, .app3 o a b c => by
    have ha := Tm.sameShapeS_eq a
    have hb := Tm.sameShapeS_eq b
    have hc := Tm.sameShapeS_eq c
    cases o <;> simp only [Tm.sameShapeS, Tm.erase, Surface.Tm.sameShape, ha, hb, hc]

theorem _root_.Solidity.Tm.eqLitS_eq (a b : Tm C Γ .val) :
    a.eqLitS b = Term.eqLit (a.erase ns) (b.erase ns) := by
  have h₁ : ∀ t : Tm C Γ .val, t.isAtomS = Term.isAtom (t.erase ns) := by
    intro t
    cases t with
    | app0 o => cases o <;> rfl
    | _ => rfl
  have h₂ : ∀ t : Tm C Γ .val, t.isLitLikeS = Term.isLitLike (t.erase ns) := by
    intro t
    cases t with
    | app0 o => cases o <;> rfl
    | _ => rfl
  simp only [Tm.eqLitS, Term.eqLit, h₁, h₂]

theorem _root_.Solidity.Tm.slotPathS_eq (hok : ρ.Ok ns) (hl : ns.length = Γ.length) :
    {u : Srt} → (t : Tm C Γ u) → t.slotPathS ρ = (t.erase ns).slotPath? ρ.sym
  | _, .pvP i => by
    simp only [Tm.slotPathS, Tm.erase, Surface.Tm.slotPath?, Idx.toNatR_eq, SymS.get_of_ok hok hl i]
    rcases lookupBy (i.name ns) ρ.sym.env with _ | b
    · rfl
    · cases b <;> rfl
  | _, .app1 o _ p => by
    have hp := Tm.slotPathS_eq hok hl p
    cases o with
    | field f => simp only [Tm.slotPathS, Tm.erase, Surface.Tm.slotPath?, hp]
    | _ => rfl
  | _, .pvV _ | _, .pvS _ | _, .pvI _ | _, .netOf _ _ | _, .app0 _ | _, .app2 .. | _, .app3 .. => rfl

theorem _root_.Solidity.Tm.staleWriteS_eq (hok : ρ.Ok ns) (hl : ns.length = Γ.length)
    (s : Tm C Γ .st) :
    (s.staleWriteS ρ).map (fun w => (w.1, w.2.1, w.2.2.erase ns)) =
      STerm.staleWrite? ρ.sym (s.erase ns) := by
  cases s with
  | app3 o x p v =>
    cases o with
    | save | push =>
      cases x with
      | app0 o' =>
        cases o' with
        | storage =>
          cases v with
          | app1 o'' _ t =>
            cases o'' with
            | sval =>
              simp only [Tm.staleWriteS, Tm.erase, STerm.staleWrite?, ← Tm.slotPathS_eq hok hl p,
                Option.map_map, Function.comp_def]
            | _ => rfl
          | _ => rfl
        | _ => rfl
      | _ => rfl
    | _ => rfl
  | _ => rfl

theorem _root_.Solidity.Tm.toLSt_eq (hok : ρ.Ok ns) (hl : ns.length = Γ.length) (s : Tm C Γ .st) :
    s.toLSt ρ = STerm.toLS ρ.sym (s.erase ns) := by
  have h := Tm.staleWriteS_eq hok hl s
  unfold Tm.toLSt STerm.toLS
  rcases hw : s.staleWriteS ρ with _ | ⟨op, q, t⟩ <;> rw [hw] at h <;> rw [← h]
  · exact Tm.toLS_eq hok hl s
  · simp only [Option.map_some, Tm.toLS_eq hok hl t]

theorem _root_.Solidity.Tm.inLSt_eq (hok : ρ.Ok ns) (hl : ns.length = Γ.length) (s : Tm C Γ .st) :
    s.inLSt ρ = STerm.inLS ρ.sym (s.erase ns) := by
  have h := Tm.staleWriteS_eq hok hl s
  unfold Tm.inLSt STerm.inLS
  rcases hw : s.staleWriteS ρ with _ | ⟨op, q, t⟩ <;> rw [hw] at h <;> rw [← h]
  · exact Tm.inLS_eq hok hl s
  · simp only [Option.map_some, Tm.inLS_eq hok hl t]

end Terms

/-! ## Updates, by position

An update's elements are read in the state it is applied in (`ρ₀`) and
applied in order: an element binds its local (at its position, or pushed
by a declaration), writes the storage, or sets the memory (`Act`); a pop
or a frame's drop pops or drops the positions.  The erased reduction
takes an update of one element, or an allocation's pair, and leaves the
rest outside the fragment; so does this one (`Upd.view`). -/

/-- What one element does to the symbolic state. -/
inductive Act where
  | keep
  | bind (b : SymB)
  | write (s : LStor)
  | mem (M : LMem)

/-- What one element does, on the erasure: its local by name. -/
inductive NAct where
  | keep
  | bind (x : Var) (b : SymB)
  | write (s : LStor)
  | mem (M : LMem)

/-- The act, its local named `x`. -/
def Act.named (x : Var) : Act → NAct
  | .keep => .keep
  | .bind b => .bind x b
  | .write s => .write s
  | .mem M => .mem M

/-- A binding or none, as an act. -/
def Act.ofOpt : Option SymB → Act
  | some b => .bind b
  | none => .keep

/-- The erased state after the act. -/
def NAct.apply (ρ : Sym) : NAct → Sym
  | .keep => ρ
  | .bind x b => { ρ with env := (x, b) :: ρ.env }
  | .write s => { ρ with stor := s, env := ρ.env.map fun b => (b.1, b.2.onWrite) }
  | .mem M => { ρ with mem := M }

/-- The local at position `n` bound to `b`. -/
def SymS.bindAt (ρ : SymS) (n : Nat) (b : SymB) : SymS :=
  let x := ρ.names.getD n (.user "_")
  ⟨ρ.loc.set n (x, some b), { ρ.sym with env := (x, b) :: ρ.sym.env }⟩

/-- The act applied, a binding at the position `n?` (an assignment's
target; none for an element that assigns no local). -/
def SymS.act (ρ : SymS) (n? : Option Nat) : Act → SymS
  | .keep => ρ
  | .bind b =>
    match n? with
    | some n => ρ.bindAt n b
    | none => ρ
  | .write s =>
    ⟨ρ.loc.map fun e => (e.1, e.2.map SymB.onWrite),
      { ρ.sym with stor := s, env := ρ.sym.env.map fun b => (b.1, b.2.onWrite) }⟩
  | .mem M => ⟨ρ.loc, { ρ.sym with mem := M }⟩

/-- A local pushed: bound by the act, or at its name's last binding (a
hidden binder, or a declaration outside the fragment), as the erasure
reads it. -/
def SymS.push (ρ : SymS) (x : Var) : Act → SymS
  | .bind b => ⟨(x, some b) :: ρ.loc, { ρ.sym with env := (x, b) :: ρ.sym.env }⟩
  | _ => ⟨(x, lookupBy x ρ.sym.env) :: ρ.loc, ρ.sym⟩

/-- `Thin.sel`'s compiled twin. -/
def _root_.Solidity.Thin.selM {α : Type} : {Γ Δ : Ctx} → Thin Γ Δ → List α → List α
  | _, _, .refl, l => l
  | _, _, .keep h, a :: l => a :: Thin.selM h l
  | _, _, .keep h, [] => Thin.selM h []
  | _, _, .drop h, l => Thin.selM h l.tail

/-- The positions a thinning keeps (`Thin.names`, for any list), by the
recursor. -/
@[implemented_by Thin.selM]
def _root_.Solidity.Thin.sel {α : Type} {Γ Δ : Ctx} (h : Thin Γ Δ) : List α → List α :=
  Thin.rec (motive := fun _ _ _ => List α → List α) (fun l => l)
    (fun _ ih l => List.casesOn (motive := fun _ => List α) l (ih []) (fun a l => a :: ih l))
    (fun _ ih l => ih l.tail) h

theorem _root_.Solidity.Thin.sel_eq_selM {α : Type} {Γ Δ : Ctx} (h : Thin Γ Δ) (l : List α) :
    Thin.sel h l = Thin.selM h l := by
  induction h generalizing l with
  | refl => rfl
  | keep h ih =>
    cases l with
    | nil => exact (ih []).trans (by simp only [Thin.selM])
    | cons a l => exact (congrArg (a :: ·) (ih l)).trans (by simp only [Thin.selM])
  | drop h ih => exact (ih l.tail).trans (by simp only [Thin.selM])

/-- The target position of an element: an assignment's local. -/
def _root_.Solidity.UpdElem.tgt {Γ Δ : Ctx} : UpdElem C Γ Δ → Option Nat
  | .local i _ => some i.toNatR
  | _ => none

/-- The target's name. -/
def _root_.Solidity.UpdElem.tgtName {Γ Δ : Ctx} (ms : List Var) : UpdElem C Γ Δ → Var
  | .local i _ => i.name ms
  | _ => .user "_"

section Upd

variable {Γ : Ctx}

/-- `Upd.replayS`'s compiled twin. -/
def _root_.Solidity.Upd.replaySM (aE : ∀ {Δ : Ctx}, UpdElem C Γ Δ → Act)
    (aR : ∀ {t : LTy}, Rhs C Γ t → Act) (ρ₀ : SymS) : {Δ : Ctx} → Upd C Γ Δ → SymS
  | _, .nil => ρ₀
  | _, .snoc U e => (U.replaySM aE aR ρ₀).act e.tgt (aE e)
  | _, .decl U x r => (U.replaySM aE aR ρ₀).push x (aR r)
  | _, .pop U h => ⟨(U.replaySM aE aR ρ₀).loc.drop h.depth, (U.replaySM aE aR ρ₀).sym⟩
  | _, .drop U h => ⟨Thin.sel h (U.replaySM aE aR ρ₀).loc, (U.replaySM aE aR ρ₀).sym⟩

/-- The state an update leaves, every element's act read off it by
`aE` (an assignment) and `aR` (a declaration's right-hand side), by the
recursor. -/
@[implemented_by Upd.replaySM]
def _root_.Solidity.Upd.replayS (aE : ∀ {Δ : Ctx}, UpdElem C Γ Δ → Act)
    (aR : ∀ {t : LTy}, Rhs C Γ t → Act) (ρ₀ : SymS) {Δ : Ctx} (U : Upd C Γ Δ) : SymS :=
  Upd.rec (motive := fun _ _ => SymS) ρ₀ (fun _ e ih => ih.act e.tgt (aE e))
    (fun _ x r ih => ih.push x (aR r)) (fun _ h ih => ⟨ih.loc.drop h.depth, ih.sym⟩)
    (fun _ h ih => ⟨Thin.sel h ih.loc, ih.sym⟩) U

theorem _root_.Solidity.Upd.replayS_eq_replaySM (aE : ∀ {Δ : Ctx}, UpdElem C Γ Δ → Act)
    (aR : ∀ {t : LTy}, Rhs C Γ t → Act) (ρ₀ : SymS) {Δ : Ctx} (U : Upd C Γ Δ) :
    U.replayS aE aR ρ₀ = U.replaySM aE aR ρ₀ := by
  induction U with
  | nil => rfl
  | snoc U e ih | decl U x r ih | pop U h ih | drop U h ih =>
    simp only [Upd.replaySM, ← ih]; rfl

/-- An element of an update: a right-hand side (an assignment's or a
declaration's), or an element that assigns no local. -/
inductive ElemS (C : Contract) (Γ : Ctx) where
  | rhs {t : LTy} (r : Rhs C Γ t)
  | glob {Δ : Ctx} (e : UpdElem C Γ Δ)

/-- An assignment as its right-hand side. -/
def _root_.Solidity.UpdElem.toElemS {Δ : Ctx} : UpdElem C Γ Δ → ElemS C Γ
  | .local _ r => .rhs r
  | e => .glob e

/-- How many elements an update has: none, one, two, or more. -/
inductive UView (C : Contract) (Γ : Ctx) where
  | zero
  | one (a : ElemS C Γ)
  | two (a b : ElemS C Γ)
  | many

/-- One more element. -/
def UView.add : UView C Γ → ElemS C Γ → UView C Γ
  | .zero, a => .one a
  | .one a, b => .two a b
  | _, _ => .many

/-- `Upd.view`'s compiled twin. -/
def _root_.Solidity.Upd.viewM : {Δ : Ctx} → Upd C Γ Δ → UView C Γ
  | _, .nil => .zero
  | _, .snoc U e => U.viewM.add e.toElemS
  | _, .decl U _ r => U.viewM.add (.rhs r)
  | _, .pop U _ => U.viewM
  | _, .drop U _ => U.viewM

/-- The elements of an update, pops and drops aside, by the recursor. -/
@[implemented_by Upd.viewM]
def _root_.Solidity.Upd.view {Δ : Ctx} (U : Upd C Γ Δ) : UView C Γ :=
  Upd.rec (motive := fun _ _ => UView C Γ) .zero (fun _ e ih => ih.add e.toElemS)
    (fun _ _ r ih => ih.add (.rhs r)) (fun _ _ ih => ih) (fun _ _ ih => ih) U

theorem _root_.Solidity.Upd.view_eq_viewM {Δ : Ctx} (U : Upd C Γ Δ) : U.view = U.viewM := by
  induction U with
  | nil => rfl
  | snoc U e ih | decl U x r ih | pop U h ih | drop U h ih => simp only [Upd.viewM, ← ih]; rfl

/-- The element on the erasure, its local named `x`. -/
def ElemS.erase (ns : List Var) (x : Var) : ElemS C Γ → Surface.UpdElem C
  | .rhs r => r.erase ns x
  | .glob (.local _ r) => r.erase ns x
  | .glob e => e.erase ns []

/-- What a right-hand side binds its local to (`Surface.UpdElem.toL`). -/
def _root_.Solidity.Rhs.actS (ρ : SymS) {t : LTy} : Rhs C Γ t → Option SymB
  | .val t => some (.val (t.toLS ρ))
  | .path p => some (.path (p.toLS ρ))
  | .unset => some .unset
  | .mref i => (i.toLS ρ).map fun p => .mref p.1
  | .store s => some (.stor (s.toLS ρ))
  | .saveNet | .saveNetMt => none

/-- What a right-hand side's term must return. -/
def _root_.Solidity.Rhs.guardS (ρ : SymS) {t : LTy} : Rhs C Γ t → LTerm
  | .val t => t.toLS ρ
  | .path p => guardPath ρ.sym.stor (p.toLS ρ)
  | .unset => .lit (.bool true)
  | .mref i =>
    match i.toLS ρ with
    | some (_, g) => g
    | none => .err
  | .store s => .sok (s.toLS ρ)
  | .saveNet | .saveNetMt => .err

/-- A right-hand side in the fragment. -/
def _root_.Solidity.Rhs.inLS (ρ : SymS) {t : LTy} : Rhs C Γ t → Bool
  | .val t => t.inLS ρ
  | .path p => p.inLS ρ
  | .unset => true
  | .mref i => i.inLS ρ
  | .store s => s.inLS ρ
  | .saveNet | .saveNetMt => false

/-- An element's act, read in `ρ`. -/
def _root_.Solidity.UpdElem.actS (ρ : SymS) {Δ : Ctx} : UpdElem C Γ Δ → Act
  | .local _ r => .ofOpt (r.actS ρ)
  | .storage s => .write (s.toLSt ρ)
  | .memory m =>
    match m.toLS ρ with
    | some (M, _) => if M.within memSize then .mem M else .keep
    | none => .keep
  | _ => .keep

/-- What an element's terms must return. -/
def ElemS.guard (ρ : SymS) : ElemS C Γ → LTerm
  | .rhs r => r.guardS ρ
  | .glob (.local _ r) => r.guardS ρ
  | .glob (.storage s) => .sok (s.toLSt ρ)
  | .glob (.net r _ a) => .kite (r.toLS ρ) (a.toLS ρ) (.lit (.bool true)) (.lit (.bool true))
  | .glob (.pay r a) => .kite (r.toLS ρ) (a.toLS ρ) (payGuard (a.toLS ρ)) (payGuard (a.toLS ρ))
  | .glob (.memory m) =>
    match m.toLS ρ with
    | some (M, g) => if M.within memSize then g else .err
    | none => .err
  | .glob _ => .err

/-- An element in the fragment (`Surface.UpdElem.inL`). -/
def ElemS.inLS (ρ : SymS) : ElemS C Γ → Bool
  | .rhs r => r.inLS ρ
  | .glob (.local _ r) => r.inLS ρ
  | .glob (.storage s) => s.inLSt ρ
  | .glob (.net r _ a) | .glob (.pay r a) => r.inLS ρ && a.inLS ρ
  | .glob (.memory m) => m.inLS ρ && memWithin (m.toLS ρ)
  | .glob _ => false

/-- An allocation's pair: the identity and the memory (`pairView`). -/
def pairViewS : ElemS C Γ → ElemS C Γ → Option (Tm C Γ .ident × Tm C Γ .mem)
  | .rhs (.mref i), .glob (.memory mm) | .glob (.local _ (.mref i)), .glob (.memory mm) =>
    some (i, mm)
  | _, _ => none

/-- `allocPair?`, a syntactic test on the pair's two terms, read on their
erasures (two copies of the same value compared). -/
def allocPairS? (ρ : SymS) (i : Tm C Γ .ident) (mm : Tm C Γ .mem) : Bool :=
  allocPair? (i.eraseR ρ.names) (mm.eraseR ρ.names)

/-- A copy from storage (`copyOf?`): its path. -/
def copyOfS? : Tm C Γ .mem → Option (Tm C Γ .path)
  | .app2 .copySt (.app0 .memory) (.app2 .sfind (.app0 .storage) p) => some p
  | _ => none

/-- `pairMem`, by position. -/
def pairMemS (ρ : SymS) (mm : Tm C Γ .mem) : Option (LMem × LTerm) :=
  match copyOfS? mm with
  | some p =>
    some (key{ copySt(‹ρ.sym.mem›, ‹ρ.sym.mem.nAlloc›, find(‹ρ.sym.stor›, ‹p.toLS ρ›)) },
      copyG ρ.sym.stor (p.toLS ρ))
  | none => mm.toLS ρ

/-- `pairIn`, by position. -/
def pairInS (ρ : SymS) (mm : Tm C Γ .mem) : Bool :=
  match copyOfS? mm with
  | some p => p.inLS ρ
  | none => mm.inLS ρ

/-- The pair's guard and the memory it leaves (`pairL`). -/
def pairLS (ρ : SymS) (i : Tm C Γ .ident) (mm : Tm C Γ .mem) : Option (LTerm × LMem) :=
  if allocPairS? ρ i mm then
    (pairMemS ρ mm).bind fun p => if p.1.within memSize then some (p.2, p.1) else none
  else none

/-- The pair's acts: the identity's local bound to the root of the next
ordinal, the memory set. -/
def pairActE (ρ : SymS) (M : LMem) {Δ : Ctx} : UpdElem C Γ Δ → Act
  | .local _ (.mref _) => .bind (.mref key{ idC(‹ρ.sym.mem.nAlloc›, nil) })
  | .memory _ => .mem M
  | _ => .keep

/-- The pair's act on a declaration. -/
def pairActR (ρ : SymS) {t : LTy} : Rhs C Γ t → Act
  | .mref _ => .bind (.mref key{ idC(‹ρ.sym.mem.nAlloc›, nil) })
  | _ => .keep

end Upd

/-! ## Formulas, by position -/

section Fml

/-- No act: an update of pops and drops. -/
def noActE {Γ Δ : Ctx} (_ : UpdElem C Γ Δ) : Act := .keep

/-- No act, on a declaration. -/
def noActR {Γ : Ctx} {t : LTy} (_ : Rhs C Γ t) : Act := .keep

/-- `Fml.peelS`'s compiled twin. -/
def _root_.Solidity.Fml.peelSM : {Γ : Ctx} → SymS → Fml C Γ → (Γ' : Ctx) × SymS × Fml C Γ'
  | _, ρ, .upd m U φ =>
    match U.view with
    | .zero => φ.peelSM (U.replayS noActE noActR ρ)
    | _ => ⟨_, ρ, .upd m U φ⟩
  | _, ρ, .bind _ x _ φ => φ.peelSM (ρ.push x .keep)
  | Γ, ρ, φ => ⟨Γ, ρ, φ⟩

/-- The formula under the constructors the erasure drops (an update of
pops and drops, a hidden binder), and the state they leave, by the
recursor. -/
@[implemented_by Fml.peelSM]
def _root_.Solidity.Fml.peelS {Γ : Ctx} (ρ : SymS) (φ : Fml C Γ) : (Γ' : Ctx) × SymS × Fml C Γ' :=
  Fml.rec (motive := fun _ _ => SymS → (Γ' : Ctx) × SymS × Fml C Γ')
    (tt := fun {Γ} ρ => ⟨Γ, ρ, .tt⟩) (eq := fun a b ρ => ⟨_, ρ, .eq a b⟩)
    (defined := fun t ρ => ⟨_, ρ, .defined t⟩) (not := fun φ _ ρ => ⟨_, ρ, .not φ⟩)
    (and := fun φ ψ _ _ ρ => ⟨_, ρ, .and φ ψ⟩) (imp := fun φ ψ _ _ ρ => ⟨_, ρ, .imp φ ψ⟩)
    (upd := fun m U φ ih ρ =>
      match U.view with
      | .zero => ih (U.replayS noActE noActR ρ)
      | _ => ⟨_, ρ, .upd m U φ⟩)
    (modal := fun m P κ φ _ ρ => ⟨_, ρ, .modal m P κ φ⟩)
    (havoc := fun φ _ ρ => ⟨_, ρ, .havoc φ⟩) (all := fun x p φ _ ρ => ⟨_, ρ, .all x p φ⟩)
    (bind := fun _ x _ _ ih ρ => ih (ρ.push x .keep))
    (anon := fun xs φ _ ρ => ⟨_, ρ, .anon xs φ⟩) φ ρ

theorem _root_.Solidity.Fml.peelS_eq_peelSM {Γ : Ctx} (ρ : SymS) (φ : Fml C Γ) :
    φ.peelS ρ = φ.peelSM ρ := by
  induction φ generalizing ρ with
  | upd m U φ ih => simp only [Fml.peelSM, ← ih]; rfl
  | bind m x t φ ih => simp only [Fml.peelSM, ← ih]; rfl
  | _ => rfl

/-- Two terms the same (`Surface.Tm.sameL`), each with the state it is
read in: compared by their erasures, a syntactic test. -/
def sameAt {Γ Δ : Ctx} (ρa : SymS) (a : Tm C Γ .val) (ρb : SymS) (b : Tm C Δ .val) : Bool :=
  a.sameShapeS && decide (a.eraseR ρa.names = b.eraseR ρb.names)

/-- `defined a`. -/
def _root_.Solidity.Fml.asDefinedS {Γ : Ctx} : Fml C Γ → Option (Tm C Γ .val)
  | .defined a => some a
  | _ => none

/-- `φ ∧ ψ`. -/
def _root_.Solidity.Fml.asAndS {Γ : Ctx} : Fml C Γ → Option (Fml C Γ × Fml C Γ)
  | .and φ ψ => some (φ, ψ)
  | _ => none

/-- `a = b`. -/
def _root_.Solidity.Fml.asEqS {Γ : Ctx} : Fml C Γ → Option (Tm C Γ .val × Tm C Γ .val)
  | .eq a b => some (a, b)
  | _ => none

/-- `eqD a b` (`NFml.eqDView`), through the constructors the erasure
drops: each side with the state it is read in. -/
def eqDViewS {Γ : Ctx} (ρ : SymS) (φ ψ : Fml C Γ) :
    Option (((Γ' : Ctx) × SymS × Tm C Γ' .val) × ((Γ' : Ctx) × SymS × Tm C Γ' .val)) :=
  let pa := φ.peelS ρ
  let pb := ψ.peelS ρ
  match pa.2.2.asDefinedS, pb.2.2.asAndS with
  | some a, some (ψ₁, ψ₂) =>
    let p₁ := ψ₁.peelS pb.2.1
    let p₂ := ψ₂.peelS pb.2.1
    match p₁.2.2.asDefinedS, p₂.2.2.asEqS with
    | some b, some (a', b') =>
      if sameAt pa.2.1 a p₂.2.1 a' && sameAt p₁.2.1 b p₂.2.1 b' then
        some (⟨_, pa.2.1, a⟩, ⟨_, p₁.2.1, b⟩)
      else none
    | _, _ => none
  | _, _ => none

/-- `Fml.toLS`'s compiled twin. -/
def _root_.Solidity.Fml.toLSM : {Γ : Ctx} → SymS → Fml C Γ → LFml
  | _, _, .tt => .tt
  | _, ρ, .eq a b => .eq (a.toLS ρ) (b.toLS ρ)
  | _, ρ, .defined t => .eq (t.toLS ρ) (t.toLS ρ)
  | _, ρ, .not φ => .not (φ.toLSM ρ)
  | _, ρ, .and φ ψ =>
    match eqDViewS ρ φ ψ with
    | some (⟨_, ρa, a⟩, ⟨_, ρb, b⟩) => .eq (a.toLS ρa) (b.toLS ρb)
    | none => .and (φ.toLSM ρ) (ψ.toLSM ρ)
  | _, ρ, .imp φ ψ => .imp (φ.toLSM ρ) (ψ.toLSM ρ)
  | _, ρ, .upd m U φ =>
    match U.view with
    | .zero => φ.toLSM (U.replayS noActE noActR ρ)
    | .one a => guardM m (a.guard ρ) (φ.toLSM (U.replayS (UpdElem.actS ρ) (fun r => .ofOpt (r.actS ρ)) ρ))
    | .two a b =>
      match pairViewS a b with
      | some (i, mm) =>
        match pairLS ρ i mm with
        | some (g, M) => guardM m g (φ.toLSM (U.replayS (pairActE ρ M) (pairActR ρ) ρ))
        | none => .tt
      | none => .tt
    | .many => .tt
  | _, _, .modal .. => .not .tt
  | _, _, .havoc _ => .tt
  | _, ρ, .all x p φ => .all x p (φ.toLSM (ρ.push x (.bind (.val (.var x)))))
  | _, ρ, .bind _ x _ φ => φ.toLSM (ρ.push x .keep)
  | _, _, .anon .. => .tt

/-- `Fml.inLS`'s compiled twin. -/
def _root_.Solidity.Fml.inLSM : {Γ : Ctx} → SymS → Fml C Γ → Bool
  | _, _, .tt => true
  | _, _, .eq a b => a.eqLitS b
  | _, ρ, .defined t => t.inLS ρ
  | _, ρ, .not φ => φ.inLSM ρ
  | _, ρ, .and φ ψ =>
    match eqDViewS ρ φ ψ with
    | some (⟨_, ρa, a⟩, ⟨_, ρb, b⟩) => a.inLS ρa && b.inLS ρb
    | none => φ.inLSM ρ && ψ.inLSM ρ
  | _, ρ, .imp φ ψ => φ.inLSM ρ && ψ.inLSM ρ
  | _, ρ, .upd _ U φ =>
    match U.view with
    | .zero => φ.inLSM (U.replayS noActE noActR ρ)
    | .one a => a.inLS ρ && φ.inLSM (U.replayS (UpdElem.actS ρ) (fun r => .ofOpt (r.actS ρ)) ρ)
    | .two a b =>
      match pairViewS a b with
      | some (i, mm) =>
        match pairLS ρ i mm with
        | some (_, M) =>
          pairInS ρ mm && M.within memSize && φ.inLSM (U.replayS (pairActE ρ M) (pairActR ρ) ρ)
        | none => false
      | none => false
    | .many => false
  | _, _, .modal .. => true
  | _, _, .havoc _ => false
  | _, ρ, .all x _ φ => !ρ.sym.vars.contains x && φ.inLSM (ρ.push x (.bind (.val (.var x))))
  | _, ρ, .bind _ x _ φ => φ.inLSM (ρ.push x .keep)
  | _, _, .anon .. => false

/-- **A scoped formula with its updates pushed in** (`NFml.toL` of its
erasure), by the recursor. -/
@[implemented_by Fml.toLSM]
def _root_.Solidity.Fml.toLS {Γ : Ctx} (ρ : SymS) (φ : Fml C Γ) : LFml :=
  Fml.rec (motive := fun _ _ => SymS → LFml)
    (tt := fun _ => .tt) (eq := fun a b ρ => .eq (a.toLS ρ) (b.toLS ρ))
    (defined := fun t ρ => .eq (t.toLS ρ) (t.toLS ρ))
    (not := fun _ ih ρ => .not (ih ρ))
    (and := fun φ ψ ihφ ihψ ρ =>
      match eqDViewS ρ φ ψ with
      | some (⟨_, ρa, a⟩, ⟨_, ρb, b⟩) => .eq (a.toLS ρa) (b.toLS ρb)
      | none => .and (ihφ ρ) (ihψ ρ))
    (imp := fun _ _ ihφ ihψ ρ => .imp (ihφ ρ) (ihψ ρ))
    (upd := fun m U _ ih ρ =>
      match U.view with
      | .zero => ih (U.replayS noActE noActR ρ)
      | .one a => guardM m (a.guard ρ) (ih (U.replayS (UpdElem.actS ρ) (fun r => .ofOpt (r.actS ρ)) ρ))
      | .two a b =>
        match pairViewS a b with
        | some (i, mm) =>
          match pairLS ρ i mm with
          | some (g, M) => guardM m g (ih (U.replayS (pairActE ρ M) (pairActR ρ) ρ))
          | none => .tt
        | none => .tt
      | .many => .tt)
    (modal := fun _ _ _ _ _ _ => .not .tt) (havoc := fun _ _ _ => .tt)
    (all := fun x p _ ih ρ => .all x p (ih (ρ.push x (.bind (.val (.var x))))))
    (bind := fun _ x _ _ ih ρ => ih (ρ.push x .keep)) (anon := fun _ _ _ _ => .tt) φ ρ

/-- **The fragment, on a scoped formula** (`NFml.inL` of its erasure), by the
recursor. -/
@[implemented_by Fml.inLSM]
def _root_.Solidity.Fml.inLS {Γ : Ctx} (ρ : SymS) (φ : Fml C Γ) : Bool :=
  Fml.rec (motive := fun _ _ => SymS → Bool)
    (tt := fun _ => true) (eq := fun a b _ => a.eqLitS b) (defined := fun t ρ => t.inLS ρ)
    (not := fun _ ih ρ => ih ρ)
    (and := fun φ ψ ihφ ihψ ρ =>
      match eqDViewS ρ φ ψ with
      | some (⟨_, ρa, a⟩, ⟨_, ρb, b⟩) => a.inLS ρa && b.inLS ρb
      | none => ihφ ρ && ihψ ρ)
    (imp := fun _ _ ihφ ihψ ρ => ihφ ρ && ihψ ρ)
    (upd := fun _ U _ ih ρ =>
      match U.view with
      | .zero => ih (U.replayS noActE noActR ρ)
      | .one a => a.inLS ρ && ih (U.replayS (UpdElem.actS ρ) (fun r => .ofOpt (r.actS ρ)) ρ)
      | .two a b =>
        match pairViewS a b with
        | some (i, mm) =>
          match pairLS ρ i mm with
          | some (_, M) =>
            pairInS ρ mm && M.within memSize && ih (U.replayS (pairActE ρ M) (pairActR ρ) ρ)
          | none => false
        | none => false
      | .many => false)
    (modal := fun _ _ _ _ _ _ => true) (havoc := fun _ _ _ => false)
    (all := fun x _ _ ih ρ => !ρ.sym.vars.contains x && ih (ρ.push x (.bind (.val (.var x)))))
    (bind := fun _ x _ _ ih ρ => ih (ρ.push x .keep)) (anon := fun _ _ _ _ => false) φ ρ

theorem _root_.Solidity.Fml.toLS_eq_toLSM {Γ : Ctx} (ρ : SymS) (φ : Fml C Γ) :
    φ.toLS ρ = φ.toLSM ρ := by
  induction φ generalizing ρ with
  | tt | modal | havoc | anon => rfl
  | eq | defined => simp only [Fml.toLSM]; rfl
  | not φ ih | all x p φ ih | bind m x t φ ih => simp only [Fml.toLSM, ← ih]; rfl
  | and φ ψ ihφ ihψ | imp φ ψ ihφ ihψ => simp only [Fml.toLSM, ← ihφ, ← ihψ]; rfl
  | upd m U φ ih => simp only [Fml.toLSM, ← ih]; rfl

theorem _root_.Solidity.Fml.inLS_eq_inLSM {Γ : Ctx} (ρ : SymS) (φ : Fml C Γ) :
    φ.inLS ρ = φ.inLSM ρ := by
  induction φ generalizing ρ with
  | tt | modal | havoc | anon => rfl
  | eq | defined => simp only [Fml.inLSM]; rfl
  | not φ ih | all x p φ ih | bind m x t φ ih => simp only [Fml.inLSM, ← ih]; rfl
  | and φ ψ ihφ ihψ | imp φ ψ ihφ ihψ => simp only [Fml.inLSM, ← ihφ, ← ihψ]; rfl
  | upd m U φ ih => simp only [Fml.inLSM, ← ih]; rfl

/-- What `sol_decide` proves of a scoped leaf: its updates pushed in by
position, the reads of writes eliminated (`NFml.reduce`). -/
def _root_.Solidity.Fml.reduceS (φ : Fml C []) : LFml := (φ.toLS SymS.empty).elim

/-- The names a scoped formula binds are fresh where `Fml.toLS` reads them:
a declaration, a quantifier and a hidden binder take a name not in scope
(what `Fml.posB` checks). -/
def _root_.Solidity.Fml.FreshS : {Γ : Ctx} → List Var → Fml C Γ → Prop
  | _, _, .tt | _, _, .eq .. | _, _, .defined _ => True
  | _, ns, .not φ => φ.FreshS ns
  | _, ns, .and φ ψ | _, ns, .imp φ ψ => φ.FreshS ns ∧ ψ.FreshS ns
  | _, ns, .upd _ U φ => U.Fresh ns ∧ φ.FreshS (U.names ns)
  | _, _, .modal .. | _, _, .havoc _ | _, _, .anon .. => True
  | _, ns, .all x _ φ | _, ns, .bind _ x _ φ => x ∉ ns ∧ φ.FreshS (x :: ns)

end Fml

/-! ## The positions stay the names' bindings -/

section Ok

theorem lookupBy_map_snd {α β : Type} [DecidableEq α] (f : β → β) (y : α) :
    (l : List (α × β)) → lookupBy y (l.map fun b => (b.1, f b.2)) = (lookupBy y l).map f
  | [] => rfl
  | (k, v) :: l => by
    simp only [List.map_cons, lookupBy]
    split
    · rfl
    · exact lookupBy_map_snd f y l

theorem nodup_getElem_ne {α : Type} {l : List α} (h : l.Nodup) {i j : Nat} (hi : i < l.length)
    (hj : j < l.length) (hij : i ≠ j) : l[i] ≠ l[j] := by
  rcases Nat.lt_or_gt_of_ne hij with h' | h'
  · exact List.pairwise_iff_getElem.1 h i j hi hj h'
  · exact (List.pairwise_iff_getElem.1 h j i hj hi h').symm

theorem _root_.Solidity.Thin.selM_nil {α : Type} : {Γ Δ : Ctx} → (h : Thin Γ Δ) →
    Thin.selM h ([] : List α) = []
  | _, _, .refl => rfl
  | _, _, .keep h => Thin.selM_nil h
  | _, _, .drop h => Thin.selM_nil h

theorem _root_.Solidity.Thin.selM_map {α β : Type} (f : α → β) :
    {Γ Δ : Ctx} → (h : Thin Γ Δ) → (l : List α) → Thin.selM h (l.map f) = (Thin.selM h l).map f
  | _, _, .refl, _ => rfl
  | _, _, .keep h, a :: l => by simp only [List.map_cons, Thin.selM, Thin.selM_map f h l]
  | _, _, .keep h, [] => by simp only [List.map_nil, Thin.selM, Thin.selM_nil]
  | _, _, .drop h, l => by simp only [Thin.selM, ← List.map_tail, Thin.selM_map f h l.tail]

theorem _root_.Solidity.Thin.sel_map {α β : Type} (f : α → β) {Γ Δ : Ctx} (h : Thin Γ Δ)
    (l : List α) : Thin.sel h (l.map f) = (Thin.sel h l).map f := by
  simp only [Thin.sel_eq_selM, Thin.selM_map]

/-- On names, the positions kept are `Thin.namesR`'s, the same recursion. -/
theorem _root_.Solidity.Thin.sel_eq_names {Γ Δ : Ctx} (h : Thin Γ Δ) (l : List Var) :
    Thin.sel h l = h.names l :=
  Thin.namesR_eq h l

variable {ms : List Var} {ρ : SymS}

theorem SymS.bindAt_ok (hok : ρ.Ok ms) (hnd : ms.Nodup) {n : Nat} (hn : n < ms.length)
    (b : SymB) : (ρ.bindAt n b).Ok ms ∧
      (ρ.bindAt n b).sym = (NAct.bind (ms.getD n (.user "_")) b).apply ρ.sym := by
  refine ⟨?_, by simp only [SymS.bindAt, SymS.names_of_ok hok, NAct.apply]⟩
  unfold SymS.Ok at hok ⊢
  simp only [SymS.bindAt, SymS.names_of_ok hok, hok]
  apply List.ext_getElem
  · simp only [List.length_set, List.length_map]
  · intro k h₁ h₂
    simp only [List.getElem_set, List.getElem_map, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hn, Option.getD_some, lookupBy]
    by_cases hk : n = k
    · subst hk; simp only [if_true]
    · have hk' : k < ms.length := by simpa only [List.length_map] using h₂
      have hne : ms[k] ≠ ms[n] := nodup_getElem_ne hnd hk' hn (Ne.symm hk)
      simp only [hk, hne, if_false]

theorem SymS.act_ok (hok : ρ.Ok ms) (hnd : ms.Nodup) {Γ Δ : Ctx} (hl : ms.length = Δ.length)
    (e : UpdElem C Γ Δ) (a : Act) (hb : ∀ b, a = .bind b → e.tgt.isSome = true) :
    (ρ.act e.tgt a).Ok ms ∧ (ρ.act e.tgt a).sym = (a.named (e.tgtName ms)).apply ρ.sym := by
  cases a with
  | keep => exact ⟨hok, rfl⟩
  | mem M => exact ⟨hok, rfl⟩
  | write s =>
    refine ⟨?_, rfl⟩
    unfold SymS.Ok at hok ⊢
    simp only [SymS.act, hok, List.map_map, Function.comp_def, lookupBy_map_snd]
  | bind b =>
    cases e with
    | «local» i r =>
      have hi : i.toNat < ms.length := hl ▸ i.toNat_lt
      simp only [UpdElem.tgt, Idx.toNatR_eq]
      exact SymS.bindAt_ok hok hnd hi b
    | _ => exact absurd (hb b rfl) (by simp only [UpdElem.tgt, Option.isSome_none,
        Bool.false_eq_true, not_false_eq_true])

theorem SymS.push_ok (hok : ρ.Ok ms) (x : Var) (a : Act) (ha : a = .keep ∨ ∃ b, a = .bind b)
    (hx : (∃ b, a = .bind b) → x ∉ ms) :
    (ρ.push x a).Ok (x :: ms) ∧ (ρ.push x a).sym = (a.named x).apply ρ.sym := by
  unfold SymS.Ok at hok ⊢
  rcases ha with rfl | ⟨b, rfl⟩
  · exact ⟨by simp only [SymS.push, hok, List.map_cons], rfl⟩
  · refine ⟨?_, rfl⟩
    have hx' := hx ⟨b, rfl⟩
    simp only [SymS.push, hok, List.map_cons, lookupBy, if_true, List.cons.injEq, true_and]
    refine List.map_congr_left fun y hy => ?_
    have hne : y ≠ x := fun he => hx' (he ▸ hy)
    simp only [hne, if_false]

theorem _root_.Solidity.Upd.replaySM_ok {Γ : Ctx} {ns : List Var}
    (aE : ∀ {Δ : Ctx}, UpdElem C Γ Δ → Act) (aR : ∀ {t : LTy}, Rhs C Γ t → Act)
    (hbE : ∀ {Δ : Ctx} (e : UpdElem C Γ Δ) (b : SymB), aE e = .bind b → e.tgt.isSome = true)
    (hR : ∀ {t : LTy} (r : Rhs C Γ t), aR r = .keep ∨ ∃ b, aR r = .bind b)
    (aN : Surface.UpdElem C → NAct)
    (hE : ∀ {Δ : Ctx} (ms : List Var) (e : UpdElem C Γ Δ),
      aN (e.erase ns ms) = (aE e).named (e.tgtName ms))
    (hRN : ∀ {t : LTy} (x : Var) (r : Rhs C Γ t), aN (r.erase ns x) = (aR r).named x)
    {ρ₀ : SymS} (hok : ρ₀.Ok ns) (hnd : ns.Nodup) (hl : ns.length = Γ.length) :
    ∀ {Δ : Ctx} (U : Upd C Γ Δ), U.Fresh ns →
      (U.replaySM aE aR ρ₀).Ok (U.names ns) ∧ (U.names ns).Nodup ∧
        (U.names ns).length = Δ.length ∧
        (U.replaySM aE aR ρ₀).sym = (U.erase ns).foldl (fun acc e => (aN e).apply acc) ρ₀.sym
  | _, .nil, _ => ⟨hok, hnd, hl, rfl⟩
  | _, .snoc U e, hf => by
    obtain ⟨h₁, h₂, h₃, h₄⟩ := Upd.replaySM_ok aE aR hbE hR aN hE hRN hok hnd hl U hf
    obtain ⟨h₅, h₆⟩ := SymS.act_ok h₁ h₂ h₃ e (aE e) (hbE e)
    refine ⟨h₅, h₂, h₃, ?_⟩
    simp only [Upd.replaySM, Upd.erase, List.foldl_append, List.foldl_cons,
      List.foldl_nil, h₆, h₄, hE]
  | _, .decl U x r, hf => by
    obtain ⟨h₁, h₂, h₃, h₄⟩ := Upd.replaySM_ok aE aR hbE hR aN hE hRN hok hnd hl U hf.1
    obtain ⟨h₅, h₆⟩ := SymS.push_ok h₁ x (aR r) (hR r) fun _ => hf.2
    refine ⟨h₅, List.nodup_cons.2 ⟨hf.2, h₂⟩, by simp only [Upd.names, List.length_cons, h₃], ?_⟩
    simp only [Upd.replaySM, Upd.erase, List.foldl_append, List.foldl_cons,
      List.foldl_nil, h₆, h₄, hRN]
  | _, .pop U h, hf => by
    obtain ⟨h₁, h₂, h₃, h₄⟩ := Upd.replaySM_ok aE aR hbE hR aN hE hRN hok hnd hl U hf
    refine ⟨?_, h₂.sublist (List.drop_sublist _ _), ?_, h₄⟩
    · unfold SymS.Ok at h₁ ⊢
      simp only [Upd.replaySM, Upd.names, h₁, List.map_drop]
    · simp only [Upd.names, List.length_drop, h₃, h.length_eq]
      omega
  | _, .drop U h, hf => by
    obtain ⟨h₁, h₂, h₃, h₄⟩ := Upd.replaySM_ok aE aR hbE hR aN hE hRN hok hnd hl U hf
    refine ⟨?_, (Thin.names_sublist h _).nodup h₂, Thin.names_length h _ h₃, h₄⟩
    unfold SymS.Ok at h₁ ⊢
    simp only [Upd.replaySM, Upd.names, h₁, Thin.sel_map, Thin.sel_eq_names]

/-- **An update's replay keeps the positions the names' bindings**, and
leaves the erased reduction's state: the elements of its erasure applied
in order, each act as `aN` reads it. -/
theorem _root_.Solidity.Upd.replayS_ok {Γ : Ctx} {ns : List Var}
    (aE : ∀ {Δ : Ctx}, UpdElem C Γ Δ → Act) (aR : ∀ {t : LTy}, Rhs C Γ t → Act)
    (hbE : ∀ {Δ : Ctx} (e : UpdElem C Γ Δ) (b : SymB), aE e = .bind b → e.tgt.isSome = true)
    (hR : ∀ {t : LTy} (r : Rhs C Γ t), aR r = .keep ∨ ∃ b, aR r = .bind b)
    (aN : Surface.UpdElem C → NAct)
    (hE : ∀ {Δ : Ctx} (ms : List Var) (e : UpdElem C Γ Δ),
      aN (e.erase ns ms) = (aE e).named (e.tgtName ms))
    (hRN : ∀ {t : LTy} (x : Var) (r : Rhs C Γ t), aN (r.erase ns x) = (aR r).named x)
    {ρ₀ : SymS} (hok : ρ₀.Ok ns) (hnd : ns.Nodup) (hl : ns.length = Γ.length)
    {Δ : Ctx} (U : Upd C Γ Δ) (hf : U.Fresh ns) :
      (U.replayS aE aR ρ₀).Ok (U.names ns) ∧ (U.names ns).Nodup ∧
        (U.names ns).length = Δ.length ∧
        (U.replayS aE aR ρ₀).sym = (U.erase ns).foldl (fun acc e => (aN e).apply acc) ρ₀.sym := by
  rw [Upd.replayS_eq_replaySM]
  exact Upd.replaySM_ok aE aR hbE hR aN hE hRN hok hnd hl U hf

end Ok

/-! ## The elements, as the erasure's -/

section Elems

/-- What one element of the erasure does (`Surface.UpdElem.toL`'s state). -/
def _root_.Solidity.Surface.UpdElem.nact (ρ : Sym) : Surface.UpdElem C → NAct
  | .val x t => .bind x (.val (t.toL ρ))
  | .path x p => .bind x (.path (p.toL ρ))
  | .storage s => .write (s.toLS ρ)
  | .store x s => .bind x (.stor (s.toL ρ))
  | .mref x i =>
    match i.toL ρ with
    | some (j, _) => .bind x (.mref j)
    | none => .keep
  | .memory m =>
    match m.toL ρ with
    | some (M, _) => if M.within memSize then .mem M else .keep
    | none => .keep
  | .unset x => .bind x .unset
  | _ => .keep

theorem _root_.Solidity.Surface.UpdElem.toL_snd (ρ : Sym) (e : Surface.UpdElem C) :
    (e.toL ρ).2 = (e.nact ρ).apply ρ := by
  cases e with
  | mref x i =>
    simp only [Surface.UpdElem.toL, Surface.UpdElem.nact]
    rcases i.toL ρ with _ | ⟨j, g⟩ <;> rfl
  | memory m =>
    simp only [Surface.UpdElem.toL, Surface.UpdElem.nact]
    rcases m.toL ρ with _ | ⟨M, g⟩
    · rfl
    · simp only
      split <;> rfl
  | _ => rfl

variable {Γ : Ctx} {ns : List Var} {ρ : SymS}

theorem _root_.Solidity.Rhs.nact_eq (hok : ρ.Ok ns) (hl : ns.length = Γ.length) {t : LTy}
    (x : Var) (r : Rhs C Γ t) :
    (r.erase ns x).nact ρ.sym = (Act.ofOpt (r.actS ρ)).named x := by
  cases r with
  | mref i =>
    simp only [Rhs.erase, Surface.UpdElem.nact, Rhs.actS, ← Tm.toLS_eq hok hl]
    rcases i.toLS ρ with _ | ⟨j, g⟩ <;> rfl
  | _ => simp only [Rhs.erase, Surface.UpdElem.nact, Rhs.actS, Act.ofOpt, Act.named,
      Tm.toLS_eq hok hl]

theorem _root_.Solidity.UpdElem.nact_eq (hok : ρ.Ok ns) (hl : ns.length = Γ.length) {Δ : Ctx}
    (ms : List Var) (e : UpdElem C Γ Δ) :
    (e.erase ns ms).nact ρ.sym = (e.actS ρ).named (e.tgtName ms) := by
  cases e with
  | «local» i r => exact Rhs.nact_eq hok hl _ r
  | storage s => simp only [UpdElem.erase, Surface.UpdElem.nact, UpdElem.actS, Act.named,
      Tm.toLSt_eq hok hl]
  | memory m =>
    simp only [UpdElem.erase, Surface.UpdElem.nact, UpdElem.actS, ← Tm.toLS_eq hok hl]
    rcases m.toLS ρ with _ | ⟨M, g⟩
    · rfl
    · simp only
      split <;> rfl
  | _ => rfl

theorem _root_.Solidity.UpdElem.actS_bind {Δ : Ctx} (e : UpdElem C Γ Δ) (b : SymB)
    (h : e.actS ρ = .bind b) : e.tgt.isSome = true := by
  cases e with
  | «local» => rfl
  | memory m =>
    simp only [UpdElem.actS] at h
    split at h
    · split at h <;> cases h
    · cases h
  | _ => cases h

theorem Act.ofOpt_cases (o : Option SymB) : Act.ofOpt o = .keep ∨ ∃ b, Act.ofOpt o = .bind b := by
  cases o with
  | none => exact .inl rfl
  | some b => exact .inr ⟨b, rfl⟩

/-- An element's local named `x`, on the erasure: an assignment's is its
target's name. -/
theorem _root_.Solidity.UpdElem.erase_toElemS {Δ : Ctx} (ms : List Var) (e : UpdElem C Γ Δ) :
    e.erase ns ms = e.toElemS.erase ns (e.tgtName ms) := by
  cases e <;> rfl

theorem ElemS.guard_eq (hok : ρ.Ok ns) (hl : ns.length = Γ.length) (x : Var) (a : ElemS C Γ) :
    ((a.erase ns x).toL ρ.sym).1 = a.guard ρ := by
  have hr : ∀ {t : LTy} (r : Rhs C Γ t) (x : Var), ((r.erase ns x).toL ρ.sym).1 = r.guardS ρ := by
    intro t r x
    cases r with
    | mref i =>
      simp only [Rhs.erase, Surface.UpdElem.toL, Rhs.guardS, ← Tm.toLS_eq hok hl]
      rcases i.toLS ρ with _ | ⟨j, g⟩ <;> rfl
    | _ => simp only [Rhs.erase, Surface.UpdElem.toL, Rhs.guardS, Tm.toLS_eq hok hl]
  cases a with
  | rhs r => exact hr r x
  | glob e =>
    cases e with
    | «local» i r => exact hr r _
    | memory m =>
      simp only [ElemS.erase, UpdElem.erase, Surface.UpdElem.toL, ElemS.guard, ← Tm.toLS_eq hok hl]
      rcases m.toLS ρ with _ | ⟨M, g⟩
      · rfl
      · simp only
        split <;> rfl
    | _ => simp only [ElemS.erase, UpdElem.erase, Surface.UpdElem.toL, ElemS.guard,
        Tm.toLS_eq hok hl, Tm.toLSt_eq hok hl]

theorem ElemS.inLS_eq (hok : ρ.Ok ns) (hl : ns.length = Γ.length) (x : Var) (a : ElemS C Γ) :
    (a.erase ns x).inL ρ.sym = a.inLS ρ := by
  have hr : ∀ {t : LTy} (r : Rhs C Γ t) (x : Var), (r.erase ns x).inL ρ.sym = r.inLS ρ := by
    intro t r x
    cases r <;> simp only [Rhs.erase, Surface.UpdElem.inL, Rhs.inLS, Tm.inLS_eq hok hl]
  cases a with
  | rhs r => exact hr r x
  | glob e =>
    cases e with
    | «local» i r => exact hr r _
    | _ => simp only [ElemS.erase, UpdElem.erase, Surface.UpdElem.inL, ElemS.inLS,
        Tm.inLS_eq hok hl, Tm.toLS_eq hok hl, Tm.inLSt_eq hok hl]

end Elems

/-! ## How many elements, on the erasure -/

section Views

variable {Γ : Ctx}

/-- The erasure of an update with the elements `v` says. -/
def UView.Erases (ns : List Var) : UView C Γ → List (Surface.UpdElem C) → Prop
  | .zero, l => l = []
  | .one a, l => ∃ x, l = [a.erase ns x]
  | .two a b, l => ∃ x y, l = [a.erase ns x, b.erase ns y]
  | .many, l => ∃ e₁ e₂ e₃ rest, l = e₁ :: e₂ :: e₃ :: rest

theorem UView.erases_add {ns : List Var} {v : UView C Γ} {l : List (Surface.UpdElem C)}
    (h : v.Erases ns l) (a : ElemS C Γ) (x : Var) : (v.add a).Erases ns (l ++ [a.erase ns x]) := by
  cases v with
  | zero => cases h; exact ⟨x, rfl⟩
  | one b => obtain ⟨y, rfl⟩ := h; exact ⟨y, x, rfl⟩
  | two b c => obtain ⟨y, z, rfl⟩ := h; exact ⟨_, _, _, [], rfl⟩
  | many => obtain ⟨e₁, e₂, e₃, rest, rfl⟩ := h; exact ⟨e₁, e₂, e₃, rest ++ _, rfl⟩

theorem _root_.Solidity.Upd.view_erases (ns : List Var) :
    {Δ : Ctx} → (U : Upd C Γ Δ) → U.view.Erases ns (U.erase ns)
  | _, .nil => rfl
  | _, .snoc U e => by
    show (U.view.add e.toElemS).Erases ns (U.erase ns ++ [e.erase ns (U.names ns)])
    rw [UpdElem.erase_toElemS (ns := ns)]
    exact UView.erases_add (Upd.view_erases ns U) _ _
  | _, .decl U x r => UView.erases_add (Upd.view_erases ns U) (.rhs r) x
  | _, .pop U _ => Upd.view_erases ns U
  | _, .drop U _ => Upd.view_erases ns U

/-- The local of an allocation's pair: the root of the next ordinal. -/
abbrev idRef (ρ : SymS) : SymB := .mref key{ idC(‹ρ.sym.mem.nAlloc›, nil) }

/-- The pair's acts on the erasure (`pairL`'s state). -/
def pairNAct (ρ : SymS) (M : LMem) : Surface.UpdElem C → NAct
  | .mref x _ => .bind x (.mref key{ idC(‹ρ.sym.mem.nAlloc›, nil) })
  | .memory _ => .mem M
  | _ => .keep

variable {ns : List Var} {ρ : SymS}

theorem pairNAct_eqE (M : LMem) {Δ : Ctx} (ms : List Var) (e : UpdElem C Γ Δ) :
    pairNAct ρ M (e.erase ns ms) = (pairActE ρ M e).named (e.tgtName ms) := by
  cases e with
  | «local» i r => cases r <;> rfl
  | _ => rfl

theorem pairNAct_eqR (M : LMem) {t : LTy} (x : Var) (r : Rhs C Γ t) :
    pairNAct ρ M (r.erase ns x) = (pairActR ρ r).named x := by
  cases r <;> rfl

theorem pairActE_bind (M : LMem) {Δ : Ctx} (e : UpdElem C Γ Δ) (b : SymB)
    (h : pairActE ρ M e = .bind b) : e.tgt.isSome = true := by
  cases e with
  | «local» => rfl
  | _ => cases h

theorem pairActR_cases {t : LTy} (r : Rhs C Γ t) :
    pairActR ρ r = .keep ∨ ∃ b, pairActR ρ r = .bind b := by
  cases r with
  | mref => exact .inr ⟨_, rfl⟩
  | _ => exact .inl rfl

theorem pairViewS_eq (a b : ElemS C Γ) (x y : Var) :
    pairView (a.erase ns x) (b.erase ns y) [] =
      (pairViewS a b).map fun p => (x, p.1.erase ns, p.2.erase ns) := by
  rcases a with r | (⟨_, r⟩ | _ | _ | _ | _ | _ | _ | _) <;>
    rcases b with r' | (⟨_, r'⟩ | _ | _ | _ | _ | _ | _ | _) <;>
    (try cases r) <;> (try cases r') <;> rfl

theorem copyOfS?_eq (mm : Tm C Γ .mem) :
    (copyOfS? mm).map (·.erase ns) = copyOf? (mm.erase ns) := by
  cases mm with
  | app2 o x v =>
    cases o with
    | copySt =>
      cases x with
      | app0 o' =>
        cases o'
        cases v with
        | app2 o'' s p =>
          cases o'' with
          | sfind =>
            cases s with
            | app0 o₃ => cases o₃ <;> rfl
            | _ => rfl
          | _ => rfl
        | _ => rfl
      | _ => rfl
    | _ => rfl
  | _ => rfl

theorem pairMemS_eq (hok : ρ.Ok ns) (hl : ns.length = Γ.length) (mm : Tm C Γ .mem) :
    pairMemS ρ mm = pairMem ρ.sym (mm.erase ns) := by
  have h := copyOfS?_eq (ns := ns) mm
  unfold pairMemS pairMem
  rcases hc : copyOfS? mm with _ | p <;> rw [hc] at h <;> rw [← h]
  · exact Tm.toLS_eq hok hl mm
  · simp only [Option.map_some, Tm.toLS_eq hok hl p]

theorem pairInS_eq (hok : ρ.Ok ns) (hl : ns.length = Γ.length) (mm : Tm C Γ .mem) :
    pairInS ρ mm = pairIn ρ.sym (mm.erase ns) := by
  have h := copyOfS?_eq (ns := ns) mm
  unfold pairInS pairIn
  rcases hc : copyOfS? mm with _ | p <;> rw [hc] at h <;> rw [← h]
  · exact Tm.inLS_eq hok hl mm
  · simp only [Option.map_some, Tm.inLS_eq hok hl p]

theorem pairLS_eq (hok : ρ.Ok ns) (hl : ns.length = Γ.length) (x : Var) (i : Tm C Γ .ident)
    (mm : Tm C Γ .mem) :
    pairL ρ.sym x (i.erase ns) (mm.erase ns) = (pairLS ρ i mm).map fun p =>
      (p.1, { ρ.sym with env := (x, idRef ρ) :: ρ.sym.env, mem := p.2 }) := by
  unfold pairL pairLS allocPairS?
  rw [Tm.eraseR_eq, Tm.eraseR_eq, SymS.names_of_ok hok, ← pairMemS_eq hok hl]
  split
  · rcases pairMemS ρ mm with _ | ⟨M, g⟩
    · rfl
    · simp only [Option.bind_some]
      split <;> rfl
  · rfl

end Views

/-! ## The reduction is the erasure's -/

section Main

/-- What a state read in `Γ`, its positions named `ns`, keeps. -/
structure Inv (ns : List Var) (Γ : Ctx) (ρ : SymS) : Prop where
  ok : ρ.Ok ns
  nodup : ns.Nodup
  len : ns.length = Γ.length

theorem Inv.self {ns : List Var} {Γ : Ctx} {ρ : SymS} (h : Inv ns Γ ρ) : Inv ρ.names Γ ρ := by
  rw [SymS.names_of_ok h.ok]
  exact h

/-- Not a constructor the erasure drops. -/
def _root_.Solidity.Fml.isHead : {Γ : Ctx} → Fml C Γ → Bool
  | _, .upd _ U _ =>
    match U.view with
    | .zero => false
    | _ => true
  | _, .bind .. => false
  | _, _ => true

theorem _root_.Solidity.Fml.erase_upd_of_view {Γ Δ : Ctx} {m : Modality} {U : Upd C Γ Δ}
    {φ : Fml C Δ} (n : List Var) (hv : U.view ≠ .zero) :
    (Fml.upd m U φ).erase n = .upd m (U.erase n) (φ.erase (U.names n)) := by
  have he := U.view_erases n
  simp only [Fml.erase]
  cases hU : U.view with
  | zero => exact absurd hU hv
  | one a => rw [hU] at he; obtain ⟨x, hx⟩ := he; rw [hx]
  | two a b => rw [hU] at he; obtain ⟨x, y, hx⟩ := he; rw [hx]
  | many => rw [hU] at he; obtain ⟨e₁, e₂, e₃, rest, hx⟩ := he; rw [hx]

/-- `defined t`, on the erasure. -/
def _root_.Solidity.NFml.asDefined : NFml C → Option (Term C)
  | .defined t => some t
  | _ => none

/-- `φ ∧ ψ`, on the erasure. -/
def _root_.Solidity.NFml.asAnd : NFml C → Option (NFml C × NFml C)
  | .and φ ψ => some (φ, ψ)
  | _ => none

/-- `a = b`, on the erasure. -/
def _root_.Solidity.NFml.asEq : NFml C → Option (Term C × Term C)
  | .eq a b => some (a, b)
  | _ => none

theorem _root_.Solidity.NFml.eqDView_eq (X Y : NFml C) :
    NFml.eqDView X Y = X.asDefined.bind fun t => Y.asAnd.bind fun p => p.1.asDefined.bind
      fun u => p.2.asEq.bind fun q =>
        if t.sameL q.1 && u.sameL q.2 then some (t, u) else none := by
  cases X <;> cases Y <;> try rfl
  rename_i Y₁ Y₂
  cases Y₁ <;> cases Y₂ <;> rfl

section Heads

variable {Γ : Ctx} {φ : Fml C Γ}

theorem _root_.Solidity.Fml.view_of_head {Δ : Ctx} {m : Modality} {U : Upd C Γ Δ} {ψ : Fml C Δ}
    (hh : (Fml.upd m U ψ).isHead = true) : U.view ≠ .zero := by
  intro hv
  simp only [Fml.isHead, hv, Bool.false_eq_true] at hh

theorem _root_.Solidity.Fml.asDefined_erase (hh : φ.isHead = true) (n : List Var) :
    (φ.erase n).asDefined = φ.asDefinedS.map (·.erase n) := by
  cases φ with
  | upd m U ψ => rw [Fml.erase_upd_of_view n (Fml.view_of_head hh)]; rfl
  | bind => simp only [Fml.isHead, Bool.false_eq_true] at hh
  | _ => rfl

theorem _root_.Solidity.Fml.asAnd_erase (hh : φ.isHead = true) (n : List Var) :
    (φ.erase n).asAnd = φ.asAndS.map fun p => (p.1.erase n, p.2.erase n) := by
  cases φ with
  | upd m U ψ => rw [Fml.erase_upd_of_view n (Fml.view_of_head hh)]; rfl
  | bind => simp only [Fml.isHead, Bool.false_eq_true] at hh
  | _ => rfl

theorem _root_.Solidity.Fml.asEq_erase (hh : φ.isHead = true) (n : List Var) :
    (φ.erase n).asEq = φ.asEqS.map fun p => (p.1.erase n, p.2.erase n) := by
  cases φ with
  | upd m U ψ => rw [Fml.erase_upd_of_view n (Fml.view_of_head hh)]; rfl
  | bind => simp only [Fml.isHead, Bool.false_eq_true] at hh
  | _ => rfl

theorem _root_.Solidity.Fml.freshS_of_asAnd {n : List Var} {ψ₁ ψ₂ : Fml C Γ}
    (h : φ.asAndS = some (ψ₁, ψ₂)) (hf : φ.FreshS n) : ψ₁.FreshS n ∧ ψ₂.FreshS n := by
  cases φ with
  | and => cases h; exact hf
  | _ => cases h

end Heads

theorem peelS_base {Γ : Ctx} {φ : Fml C Γ} {ns : List Var} {ρ : SymS} (hi : Inv ns Γ ρ)
    (hf : φ.FreshS ns) (hh : φ.isHead = true) {Γ' : Ctx} {ρ' : SymS} {φ' : Fml C Γ'}
    (h : (⟨Γ, ρ, φ⟩ : (Γ' : Ctx) × SymS × Fml C Γ') = ⟨Γ', ρ', φ'⟩) :
    Inv ρ'.names Γ' ρ' ∧ ρ'.sym = ρ.sym ∧ φ'.FreshS ρ'.names ∧ φ'.erase ρ'.names = φ.erase ns ∧
      φ'.isHead = true := by
  cases h
  rw [SymS.names_of_ok hi.ok]
  exact ⟨hi, rfl, hf, rfl, hh⟩

/-- **Peeling keeps the invariant and the erasure.** -/
theorem _root_.Solidity.Fml.peelS_spec : ∀ {Γ : Ctx} (φ : Fml C Γ) {ns : List Var} {ρ : SymS},
    Inv ns Γ ρ → φ.FreshS ns → ∀ {Γ' : Ctx} {ρ' : SymS} {φ' : Fml C Γ'},
    φ.peelS ρ = ⟨Γ', ρ', φ'⟩ →
      Inv ρ'.names Γ' ρ' ∧ ρ'.sym = ρ.sym ∧ φ'.FreshS ρ'.names ∧ φ'.erase ρ'.names = φ.erase ns ∧
        φ'.isHead = true
  | _, .upd m U φ, ns, ρ, hi, hf, Γ', ρ', φ', h => by
    cases hv : U.view with
    | zero =>
      have hp : (Fml.upd m U φ).peelS ρ = φ.peelS (U.replayS noActE noActR ρ) := by
        simp only [Fml.peelS_eq_peelSM, Fml.peelSM, hv]
      rw [hp] at h
      obtain ⟨h₁, h₂, h₃, h₄⟩ := Upd.replayS_ok noActE noActR (fun _ _ h => by cases h)
        (fun _ => .inl rfl) (fun _ => .keep) (fun _ _ => rfl) (fun _ _ => rfl) hi.ok hi.nodup
        hi.len U hf.1
      have hz : U.erase ns = [] := by
        have := U.view_erases ns
        rw [hv] at this
        exact this
      obtain ⟨r₁, r₂, r₃, r₄, r₅⟩ := Fml.peelS_spec φ ⟨h₁, h₂, h₃⟩ hf.2 h
      refine ⟨r₁, ?_, r₃, ?_, r₅⟩
      · rw [r₂, h₄, hz]
        rfl
      · rw [r₄]
        simp only [Fml.erase, hz]
    | _ =>
      have hp : (Fml.upd m U φ).peelS ρ = ⟨_, ρ, .upd m U φ⟩ := by simp only [Fml.peelS_eq_peelSM, Fml.peelSM, hv]
      rw [hp] at h
      exact peelS_base hi hf (by simp only [Fml.isHead, hv]) h
  | Γ, .bind m x t φ, ns, ρ, hi, hf, Γ', ρ', φ', h => by
    have hp : (Fml.bind m x t φ).peelS ρ = φ.peelS (ρ.push x .keep) := by simp only [Fml.peelS_eq_peelSM, Fml.peelSM]
    rw [hp] at h
    obtain ⟨o₁, o₂⟩ := SymS.push_ok hi.ok x .keep (.inl rfl) (fun ⟨_, h⟩ => by cases h)
    have hi' : Inv (x :: ns) (t :: Γ) (ρ.push x .keep) :=
      ⟨o₁, List.nodup_cons.2 ⟨hf.1, hi.nodup⟩, by simp only [List.length_cons, hi.len]⟩
    obtain ⟨r₁, r₂, r₃, r₄, r₅⟩ := Fml.peelS_spec φ hi' hf.2 h
    exact ⟨r₁, r₂.trans o₂, r₃, r₄, r₅⟩
  | _, .tt, _, _, hi, hf, _, _, _, h => peelS_base hi hf rfl h
  | _, .eq .., _, _, hi, hf, _, _, _, h => peelS_base hi hf rfl h
  | _, .defined _, _, _, hi, hf, _, _, _, h => peelS_base hi hf rfl h
  | _, .not _, _, _, hi, hf, _, _, _, h => peelS_base hi hf rfl h
  | _, .and .., _, _, hi, hf, _, _, _, h => peelS_base hi hf rfl h
  | _, .imp .., _, _, hi, hf, _, _, _, h => peelS_base hi hf rfl h
  | _, .modal .., _, _, hi, hf, _, _, _, h => peelS_base hi hf rfl h
  | _, .havoc _, _, _, hi, hf, _, _, _, h => peelS_base hi hf rfl h
  | _, .all .., _, _, hi, hf, _, _, _, h => peelS_base hi hf rfl h
  | _, .anon .., _, _, hi, hf, _, _, _, h => peelS_base hi hf rfl h

theorem sameAt_eq {Γ Δ : Ctx} (ρa : SymS) (a : Tm C Γ .val) (ρb : SymS) (b : Tm C Δ .val) :
    sameAt ρa a ρb b = (a.erase ρa.names).sameL (b.erase ρb.names) := by
  simp only [sameAt, Surface.Tm.sameL, Tm.sameShapeS_eq (ns := ρa.names), Tm.eraseR_eq]

/-- **`eqD a b` is the erasure's.** -/
theorem eqDViewS_spec {Γ : Ctx} {ns : List Var} {ρ : SymS} {φ ψ : Fml C Γ} (hi : Inv ns Γ ρ)
    (hfφ : φ.FreshS ns) (hfψ : ψ.FreshS ns) :
    match eqDViewS ρ φ ψ with
    | some (⟨Γa, ρa, a⟩, ⟨Γb, ρb, b⟩) =>
      NFml.eqDView (φ.erase ns) (ψ.erase ns) = some (a.erase ρa.names, b.erase ρb.names) ∧
        Inv ρa.names Γa ρa ∧ ρa.sym = ρ.sym ∧ Inv ρb.names Γb ρb ∧ ρb.sym = ρ.sym
    | none => NFml.eqDView (φ.erase ns) (ψ.erase ns) = none := by
  rw [NFml.eqDView_eq]
  unfold eqDViewS
  generalize hpφ : φ.peelS ρ = P
  obtain ⟨Γa, ρa, φa⟩ := P
  obtain ⟨a₁, a₂, -, a₄, a₅⟩ := Fml.peelS_spec φ hi hfφ hpφ
  generalize hpψ : ψ.peelS ρ = Q
  obtain ⟨Γ', ρ', ψa⟩ := Q
  obtain ⟨b₁, b₂, b₃, b₄, b₅⟩ := Fml.peelS_spec ψ hi hfψ hpψ
  dsimp only
  rw [← a₄, ← b₄, Fml.asDefined_erase a₅, Fml.asAnd_erase b₅]
  cases φa.asDefinedS with
  | none => rfl
  | some a =>
  cases hand : ψa.asAndS with
  | none => rfl
  | some p =>
  obtain ⟨ψ₁, ψ₂⟩ := p
  obtain ⟨f₁, f₂⟩ := Fml.freshS_of_asAnd hand b₃
  simp only [Option.map_some, Option.bind_some]
  generalize hp₁ : ψ₁.peelS ρ' = R
  obtain ⟨Γb, ρb, ψb⟩ := R
  obtain ⟨c₁, c₂, -, c₄, c₅⟩ := Fml.peelS_spec ψ₁ b₁ f₁ hp₁
  generalize hp₂ : ψ₂.peelS ρ' = S
  obtain ⟨Γe, ρe, ψe⟩ := S
  obtain ⟨-, -, -, d₄, d₅⟩ := Fml.peelS_spec ψ₂ b₁ f₂ hp₂
  dsimp only
  rw [← c₄, ← d₄, Fml.asDefined_erase c₅, Fml.asEq_erase d₅]
  cases ψb.asDefinedS with
  | none => rfl
  | some b =>
  cases ψe.asEqS with
  | none => rfl
  | some q =>
  obtain ⟨a', b'⟩ := q
  simp only [Option.map_some, Option.bind_some, sameAt_eq]
  by_cases hc : ((a.erase ρa.names).sameL (a'.erase ρe.names) &&
      (b.erase ρb.names).sameL (b'.erase ρe.names)) = true
  · simp only [hc, if_true]
    exact ⟨trivial, a₁, a₂, c₁, c₂.trans b₂⟩
  · simp only [hc, if_false, Bool.false_eq_true]

theorem pairView_cons (e₁ e₂ e : Surface.UpdElem C) (rest : List (Surface.UpdElem C)) :
    pairView e₁ e₂ (e :: rest) = none := by
  cases e₁ <;> cases e₂ <;> rfl

theorem _root_.Solidity.Fml.toLSM_eq : ∀ {Γ : Ctx} (φ : Fml C Γ) {ns : List Var} {ρ : SymS},
    Inv ns Γ ρ → φ.FreshS ns →
      φ.toLSM ρ = NFml.toL ρ.sym (φ.erase ns) ∧ φ.inLSM ρ = NFml.inL ρ.sym (φ.erase ns)
  | _, .tt, _, _, _, _ => ⟨rfl, rfl⟩
  | _, .eq a b, ns, ρ, hi, _ =>
    ⟨by simp only [Fml.toLSM, Fml.erase, NFml.toL, Tm.toLS_eq hi.ok hi.len],
      by simp only [Fml.inLSM, Fml.erase, NFml.inL, Tm.eqLitS_eq (ns := ns)]⟩
  | _, .defined t, ns, ρ, hi, _ =>
    ⟨by simp only [Fml.toLSM, Fml.erase, NFml.toL, Tm.toLS_eq hi.ok hi.len],
      by simp only [Fml.inLSM, Fml.erase, NFml.inL, Tm.inLS_eq hi.ok hi.len]⟩
  | _, .not φ, ns, ρ, hi, hf => by
    obtain ⟨h₁, h₂⟩ := Fml.toLSM_eq φ hi hf
    exact ⟨by simp only [Fml.toLSM, Fml.erase, NFml.toL, h₁],
      by simp only [Fml.inLSM, Fml.erase, NFml.inL, h₂]⟩
  | _, .imp φ ψ, ns, ρ, hi, hf => by
    obtain ⟨h₁, h₂⟩ := Fml.toLSM_eq φ hi hf.1
    obtain ⟨h₃, h₄⟩ := Fml.toLSM_eq ψ hi hf.2
    exact ⟨by simp only [Fml.toLSM, Fml.erase, NFml.toL, h₁, h₃],
      by simp only [Fml.inLSM, Fml.erase, NFml.inL, h₂, h₄]⟩
  | _, .and φ ψ, ns, ρ, hi, hf => by
    obtain ⟨h₁, h₂⟩ := Fml.toLSM_eq φ hi hf.1
    obtain ⟨h₃, h₄⟩ := Fml.toLSM_eq ψ hi hf.2
    have hv := eqDViewS_spec hi hf.1 hf.2
    simp only [Fml.toLSM, Fml.inLSM, Fml.erase, NFml.toL, NFml.inL]
    revert hv
    cases eqDViewS ρ φ ψ with
    | none =>
      intro hv
      simp only [hv, h₁, h₂, h₃, h₄]
      exact ⟨trivial, trivial⟩
    | some p =>
      obtain ⟨⟨Γa, ρa, a⟩, ⟨Γb, ρb, b⟩⟩ := p
      intro hv
      obtain ⟨hN, hia, hsa, hib, hsb⟩ := hv
      have ea : (a.erase ρa.names).toL ρ.sym = a.toLS ρa := by rw [Tm.toLS_eq hia.ok hia.len, hsa]
      have eb : (b.erase ρb.names).toL ρ.sym = b.toLS ρb := by rw [Tm.toLS_eq hib.ok hib.len, hsb]
      have fa : (a.erase ρa.names).inL ρ.sym = a.inLS ρa := by rw [Tm.inLS_eq hia.ok hia.len, hsa]
      have fb : (b.erase ρb.names).inL ρ.sym = b.inLS ρb := by rw [Tm.inLS_eq hib.ok hib.len, hsb]
      simp only [hN, ea, eb, fa, fb]
      exact ⟨trivial, trivial⟩
  | _, .upd m U φ, ns, ρ, hi, hf => by
    have hvE := U.view_erases ns
    cases hv : U.view with
    | zero =>
      rw [hv] at hvE
      obtain ⟨h₁, h₂, h₃, h₄⟩ := Upd.replayS_ok noActE noActR (fun _ _ h => by cases h)
        (fun _ => .inl rfl) (fun _ => .keep) (fun _ _ => rfl) (fun _ _ => rfl) hi.ok hi.nodup
        hi.len U hf.1
      obtain ⟨i₁, i₂⟩ := Fml.toLSM_eq φ ⟨h₁, h₂, h₃⟩ hf.2
      have hs : (U.replayS noActE noActR ρ).sym = ρ.sym := by
        rw [h₄]
        change List.foldl _ _ (U.erase ns) = _
        rw [show U.erase ns = [] from hvE]
        rfl
      simp only [Fml.toLSM, Fml.inLSM, hv, Fml.erase, show U.erase ns = [] from hvE]
      rw [i₁, i₂, hs]
      exact ⟨rfl, rfl⟩
    | one a =>
      rw [hv] at hvE
      obtain ⟨x, hx⟩ := hvE
      obtain ⟨h₁, h₂, h₃, h₄⟩ := Upd.replayS_ok (UpdElem.actS ρ) (fun r => .ofOpt (r.actS ρ))
        (fun e b h => UpdElem.actS_bind e b h) (fun r => Act.ofOpt_cases _)
        (Surface.UpdElem.nact ρ.sym) (fun ms e => UpdElem.nact_eq hi.ok hi.len ms e)
        (fun x r => Rhs.nact_eq hi.ok hi.len x r) hi.ok hi.nodup hi.len U hf.1
      obtain ⟨i₁, i₂⟩ := Fml.toLSM_eq φ ⟨h₁, h₂, h₃⟩ hf.2
      have hs : (U.replayS (UpdElem.actS ρ) (fun r => .ofOpt (r.actS ρ)) ρ).sym =
          ((a.erase ns x).toL ρ.sym).2 := by
        rw [h₄, hx, Surface.UpdElem.toL_snd]
        rfl
      simp only [Fml.toLSM, Fml.inLSM, hv, Fml.erase, hx, NFml.toL, NFml.inL]
      rw [i₁, i₂, hs, ElemS.guard_eq hi.ok hi.len x a, ElemS.inLS_eq hi.ok hi.len x a]
      exact ⟨rfl, rfl⟩
    | two a b =>
      rw [hv] at hvE
      obtain ⟨x, y, hx⟩ := hvE
      have hpv := pairViewS_eq (ns := ns) a b x y
      simp only [Fml.toLSM, Fml.inLSM, hv, Fml.erase, hx, NFml.toL, NFml.inL, hpv]
      cases hp : pairViewS a b with
      | none => exact ⟨rfl, rfl⟩
      | some q =>
        obtain ⟨i, mm⟩ := q
        rw [hp] at hpv
        obtain ⟨he₁, he₂, -⟩ := pairView_some hpv
        simp only [Option.map_some, pairLS_eq hi.ok hi.len]
        cases hl : pairLS ρ i mm with
        | none => exact ⟨rfl, rfl⟩
        | some r =>
          obtain ⟨g, M⟩ := r
          obtain ⟨h₁, h₂, h₃, h₄⟩ := Upd.replayS_ok (pairActE ρ M) (pairActR ρ)
            (fun e b h => pairActE_bind M e b h) (fun r => pairActR_cases r) (pairNAct ρ M)
            (fun ms e => pairNAct_eqE M ms e) (fun x r => pairNAct_eqR M x r) hi.ok hi.nodup
            hi.len U hf.1
          obtain ⟨i₁, i₂⟩ := Fml.toLSM_eq φ ⟨h₁, h₂, h₃⟩ hf.2
          have hs : (U.replayS (pairActE ρ M) (pairActR ρ) ρ).sym =
              { ρ.sym with env := (x, idRef ρ) :: ρ.sym.env, mem := M } := by
            rw [h₄, hx, he₁, he₂]
            rfl
          simp only [Option.map_some]
          rw [i₁, i₂, hs, pairInS_eq hi.ok hi.len]
          exact ⟨rfl, rfl⟩
    | many =>
      rw [hv] at hvE
      obtain ⟨e₁, e₂, e₃, rest, hx⟩ := hvE
      simp only [Fml.toLSM, Fml.inLSM, hv, Fml.erase, hx, NFml.toL, NFml.inL, pairView_cons]
      exact ⟨trivial, trivial⟩
  | _, .modal .., _, _, _, _ => ⟨rfl, rfl⟩
  | _, .havoc _, _, _, _, _ => ⟨rfl, rfl⟩
  | _, .anon .., _, _, _, _ => ⟨rfl, rfl⟩
  | Γ, .all x p φ, ns, ρ, hi, hf => by
    obtain ⟨o₁, o₂⟩ := SymS.push_ok hi.ok x (.bind (.val (.var x))) (.inr ⟨_, rfl⟩) fun _ => hf.1
    have hi' : Inv (x :: ns) (.val p :: Γ) (ρ.push x (.bind (.val (.var x)))) :=
      ⟨o₁, List.nodup_cons.2 ⟨hf.1, hi.nodup⟩, by simp only [List.length_cons, hi.len]⟩
    obtain ⟨i₁, i₂⟩ := Fml.toLSM_eq φ hi' hf.2
    simp only [Fml.toLSM, Fml.inLSM, Fml.erase, NFml.toL, NFml.inL, i₁, i₂, o₂]
    exact ⟨rfl, rfl⟩
  | Γ, .bind m x t φ, ns, ρ, hi, hf => by
    obtain ⟨o₁, o₂⟩ := SymS.push_ok hi.ok x .keep (.inl rfl) fun ⟨_, h⟩ => by cases h
    have hi' : Inv (x :: ns) (t :: Γ) (ρ.push x .keep) :=
      ⟨o₁, List.nodup_cons.2 ⟨hf.1, hi.nodup⟩, by simp only [List.length_cons, hi.len]⟩
    obtain ⟨i₁, i₂⟩ := Fml.toLSM_eq φ hi' hf.2
    simp only [Fml.toLSM, Fml.inLSM, Fml.erase, i₁, i₂, o₂]
    exact ⟨rfl, rfl⟩

/-- **The scoped reduction is the erased one**, and so is its fragment. -/
theorem _root_.Solidity.Fml.toLS_eq {Γ : Ctx} (φ : Fml C Γ) {ns : List Var} {ρ : SymS}
    (hi : Inv ns Γ ρ) (hf : φ.FreshS ns) :
    φ.toLS ρ = NFml.toL ρ.sym (φ.erase ns) ∧ φ.inLS ρ = NFml.inL ρ.sym (φ.erase ns) := by
  rw [Fml.toLS_eq_toLSM, Fml.inLS_eq_inLSM]
  exact Fml.toLSM_eq φ hi hf

theorem _root_.Solidity.Fml.freshS_of_plainB {Γ : Ctx} (φ : Fml C Γ) :
    ∀ {ns : List Var}, φ.plainB ns = true → φ.FreshS ns := by
  induction φ with
  | tt | eq | defined | modal | havoc | anon => intro _ _; trivial
  | not φ ih => intro ns h; exact ih h
  | and φ ψ ihφ ihψ =>
    intro ns h
    simp only [Fml.plainB, Bool.and_eq_true] at h
    exact ⟨ihφ h.1, ihψ h.2⟩
  | imp φ ψ ihφ ihψ =>
    intro ns h
    simp only [Fml.plainB, Bool.and_eq_true] at h
    exact ⟨ihφ h.1, ihψ h.2⟩
  | upd | bind => intro ns h; simp only [Fml.plainB, Bool.false_eq_true] at h
  | all x p φ ih =>
    intro ns h
    simp only [Fml.plainB, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at h
    exact ⟨fun hm => (by rw [List.contains_iff_mem.2 hm] at h; cases h.1), ih h.2⟩

theorem _root_.Solidity.Fml.freshS_of_posB {Γ : Ctx} (φ : Fml C Γ) :
    ∀ {ns B : List Var}, φ.posB ns = some B → φ.FreshS ns := by
  induction φ with
  | tt | eq | defined | modal | havoc | anon => intro _ _ _; trivial
  | not φ _ =>
    intro ns B h
    have hp : φ.plainB ns = true := by
      cases hn : φ.plainB ns
      · simp only [Fml.posB, hn] at h; cases h
      · rfl
    exact Fml.freshS_of_plainB φ hp
  | and φ ψ ihφ ihψ =>
    intro ns B h
    change (φ.posB ns).bind (fun B₁ => (ψ.posB ns).map (B₁ ++ ·)) = some B at h
    obtain ⟨B₁, h₁, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨B₂, h₂, -⟩ := Option.map_eq_some_iff.1 h
    exact ⟨ihφ h₁, ihψ h₂⟩
  | imp a φ _ ihφ =>
    intro ns B h
    have ha : a.plainB ns = true := by
      cases hn : a.plainB ns
      · simp only [Fml.posB, hn] at h; cases h
      · rfl
    change (if a.plainB ns then (φ.posB ns).bind fun B =>
        if disjointB B (a.erase ns).vars then some B else none else none) = some B at h
    rw [if_pos ha] at h
    obtain ⟨B', h₁, -⟩ := Option.bind_eq_some_iff.1 h
    exact ⟨Fml.freshS_of_plainB a ha, ihφ h₁⟩
  | upd m U φ ih =>
    intro ns B h
    change (if U.freshK ns then (φ.posB (U.names ns)).bind fun B =>
        if disjointB B (Surface.Upd.vars (U.erase ns)) then some B else none else none) =
      some B at h
    have hU : U.freshK ns = true := by
      cases hn : U.freshK ns
      · rw [hn] at h; cases h
      · rfl
    rw [if_pos hU] at h
    obtain ⟨B', h₁, -⟩ := Option.bind_eq_some_iff.1 h
    exact ⟨Upd.fresh_of_freshK ns U hU, ih h₁⟩
  | all x p φ ih =>
    intro ns B h
    change (if ns.contains x then none
      else (φ.posB (x :: ns)).bind fun B => if B.contains x then none else some B) = some B at h
    split at h
    · cases h
    · rename_i hx
      obtain ⟨B', h₁, -⟩ := Option.bind_eq_some_iff.1 h
      exact ⟨fun hm => hx (List.contains_iff_mem.2 hm), ih h₁⟩
  | bind m x t φ ih =>
    intro ns B h
    change (if ns.contains x then none else (φ.posB (x :: ns)).map (x :: ·)) = some B at h
    split at h
    · cases h
    · rename_i hx
      obtain ⟨B', h₁, -⟩ := Option.map_eq_some_iff.1 h
      exact ⟨fun hm => hx (List.contains_iff_mem.2 hm), ih h₁⟩

/-- **The boundary, scoped**: a leaf is valid where its reduction, computed
on the leaf itself, holds in every state; `Fml.posB` takes the leaf's
hidden binders, and the fragment is checked on the leaf (`Fml.inLS`). -/
theorem _root_.Solidity.Valid.of_reduceS {φ : Fml C []} (hp : (φ.posB []).isSome = true)
    (hf : φ.inLS SymS.empty = true) (h : ∀ σ, φ.reduceS.holds σ) : Valid φ := by
  obtain ⟨B, hB⟩ := Option.isSome_iff_exists.1 hp
  have hi : Inv [] [] SymS.empty := ⟨rfl, List.nodup_nil, rfl⟩
  obtain ⟨h₁, h₂⟩ := Fml.toLS_eq φ hi (Fml.freshS_of_posB φ hB)
  refine Valid.of_erase hp ((NFml.valid_iff_reduce _ (h₂ ▸ hf)).2 fun σ => ?_)
  have := h σ
  rwa [Fml.reduceS, h₁] at this

end Main

end Decide

end Solidity
