import Solidity.Calculus.ReadQuery
import Solidity.Calculus.ExactReduction

/-!
# Storage read queries for existing typed leaf terms

`ReadExpr` recognizes a fragment of `LTm`; it is indexed by the existing
term, not an alternative formula syntax. Its query computes primitive
values and declared paths. A mapping key may itself contain storage reads.
The query's finite trace can then be realized by actual interpreter saves.
Array paths, memory and the ledger require other realization laws.
-/

namespace Solidity.Decide

open ReadRealization
open Semantics

variable {C : Contract}

/-- Query paths retain the evidence that every read returns. -/
def ReadDen (C : Contract) : Srt → Type
  | .val p => p.Denote
  | .path T => { r : SRef C T // r.Declared }
  | .kint => Int
  | _ => Empty

/-- Forget the proof attached to a declared query path. -/
def ReadDen.erase (g : State C []) : {s : Srt} → ReadDen C s → s.Den C g.H
  | .val _, v => v
  | .path _, r => r.val
  | .kint, v => v
  | .st, v | .sv _, v | .ident _, v | .addr _, v | .mem, v |
      .mv _, v | .sts _, v | .spath _ _, v => nomatch v

theorem ReadDen.erase_val (g : State C []) (p : PrimTy) :
    (ReadDen.erase g (s := .val p)) = id := rfl

/-- Supported read expressions, stated on the original typed terms. -/
inductive ReadExpr : {s : Srt} → LTm C s → Type where
  | var {p : PrimTy} (k : Nat) : ReadExpr (LTm.var (p := p) k)
  | lit {p : PrimTy} (v : p.Denote) : ReadExpr (.app0 (.lit v))
  | env (k : EnvKey) : ReadExpr (.app0 (.env k))
  | root (r : Name) {T : Ty} (h : C.rootType r = some T) : ReadExpr (.app0 (.root r h))
  | field {s f : Name} {T : Ty} (h : C.fieldType s f = some T)
      {q : LTm C (.path (.ref (.struct s)))} (hq : ReadExpr q) : ReadExpr (.app1 (.field h) q)
  | index {K : PrimTy} {T : Ty} {q : LTm C (.path (.ref (.mapping K T)))}
      {k : LTm C (.val K)} (hq : ReadExpr q) (hk : ReadExpr k) : ReadExpr (.index .map q k)
  | word {p : PrimTy} {q : LTm C (.path (.prim p))} (hq : ReadExpr q) : ReadExpr (.obsW q)
  | unop (op : UnOp) {p : PrimTy} (h : op.accepts p = true)
      {t : LTm C (.val p)} (ht : ReadExpr t) : ReadExpr (.app1 (.unop op h) t)
  | binop (op : BinOp) {p : PrimTy} (h : op.accepts p = true)
      {a b : LTm C (.val p)} (ha : ReadExpr a) (hb : ReadExpr b) :
      ReadExpr (.app2 (.binop op h) a b)
  | seq {s' s : Srt} {d : LTm C s'} {a : LTm C s}
      (hd : ReadExpr d) (ha : ReadExpr a) : ReadExpr (.seq d a)
  | orElse {s : Srt} {a b : LTm C s} (ha : ReadExpr a) (hb : ReadExpr b) : ReadExpr (.orElse a b)
  | kite {p : PrimTy} {s : Srt} {a b : LTm C (.val p)} {t e : LTm C s}
      (ha : ReadExpr a) (hb : ReadExpr b) (ht : ReadExpr t) (he : ReadExpr e) :
      ReadExpr (.kite a b t e)
  | err {s : Srt} : ReadExpr (LTm.err (C := C) (s := s))
  /-- A KeY `int` literal. -/
  | zlit (n : Int) : ReadExpr (.app0 (.zlit n))
  /-- A `uint` read as a KeY `int`. -/
  | toInt {t : LTm C (.val .uint)} (ht : ReadExpr t) : ReadExpr (.app1 .toInt t)
  /-- The ledger's entry at an address, a KeY `int`. -/
  | net {t : LTm C (.val .uint)} (ht : ReadExpr t) : ReadExpr (.app1 .net t)
  /-- `a ⊕ b` on KeY's `int`. -/
  | zbin (op : BinOp) (h : op.zArith = true) {a b : LTm C .kint} (ha : ReadExpr a)
      (hb : ReadExpr b) : ReadExpr (.app2 (.zbin op h) a b)
  /-- `a ⊲ b` on KeY's `int`. -/
  | zcmp (op : BinOp) (h : op.zCmp = true) {a b : LTm C .kint} (ha : ReadExpr a)
      (hb : ReadExpr b) : ReadExpr (.app2 (.zcmp op h) a b)

namespace ReadExpr

/-- Recognize the fragment by structural recursion on the existing term.
`none` means unsupported, never a claim about the term's value. -/
def ofTerm? : {s : Srt} → (t : LTm C s) → Option (ReadExpr t)
  | _, .var k => some (.var k)
  | _, .app0 (.lit v) => some (.lit v)
  | _, .app0 (.env k) => some (.env k)
  | _, .app0 (.root r h) => some (.root r h)
  | _, .app1 (.field h) q => (ofTerm? q).map (.field h)
  | _, .app1 (.unop op h) t => (ofTerm? t).map (.unop op h)
  | _, .app2 (.binop op h) a b => do return .binop op h (← ofTerm? a) (← ofTerm? b)
  | _, .index .map q k => do return .index (← ofTerm? q) (← ofTerm? k)
  | _, .obsW q => (ofTerm? q).map .word
  | _, .seq d a => do return .seq (← ofTerm? d) (← ofTerm? a)
  | _, .orElse a b => do return .orElse (← ofTerm? a) (← ofTerm? b)
  | _, .kite a b t e => do return .kite (← ofTerm? a) (← ofTerm? b) (← ofTerm? t) (← ofTerm? e)
  | _, .err => some .err
  -- KeY `int` nodes, matched under a variable symbol so that the cases
  -- above do not discriminate on the sort.
  | s, .app0 o =>
    match s, o with
    | _, .zlit n => some (.zlit n)
    | _, _ => none
  | s, .app1 (a := a) o t =>
    match a, s, o, t with
    | _, _, .toInt, t => (ofTerm? t).map .toInt
    | _, _, .net, t => (ofTerm? t).map .net
    | _, _, _, _ => none
  | s, .app2 (a := u) (b := v) o a b =>
    match u, v, s, o, a, b with
    | _, _, _, .zbin op h, a, b => do return .zbin op h (← ofTerm? a) (← ofTerm? b)
    | _, _, _, .zcmp op h, a, b => do return .zcmp op h (← ofTerm? a) (← ofTerm? b)
    | _, _, _, _, _, _ => none
  | _, _ => none

/-- Compute a supported term by recording primitive storage reads. The
result keeps checked arithmetic and short circuit semantics; the footprint
may conservatively include reads of an unused pure operand. -/
def query (g : State C []) (ν : AEnv) : {s : Srt} → {t : LTm C s} →
    ReadExpr t → Query C (Option (ReadDen C s))
  | _, _, .var k => .pure (some (ν.get _ k))
  | _, _, .lit v => .pure (some v)
  | _, _, .env k => .pure (some (g.envVal k))
  | _, _, .root r h => .pure (some ⟨SRef.ofRoot r h, .nil⟩)
  | _, _, .field h hq => (hq.query g ν).bind fun q =>
      .pure (q.map fun r => ⟨r.val.field h, r.property.append (.field h .nil)⟩)
  | _, _, .index hq hk => (hq.query g ν).bind fun q => (hk.query g ν).bind fun k =>
      .pure (q.bind fun r => k.map fun i =>
        ⟨r.val.index .map i, by
          change (r.val.path.append (Path.index .map i)).Declared
          rw [Path.index_map]
          exact r.property.append (.key i .nil)⟩)
  | _, _, .word hq => (hq.query g ν).bind fun q =>
      match q with
      | none => .pure none
      | some r => .read ⟨_, r.val, r.property⟩ (fun v => .pure (some v))
  | _, _, .unop op h ht => (ht.query g ν).bind fun v => .pure (v.bind (op.evalT h))
  | _, _, .binop op h ha hb => (ha.query g ν).bind fun a => (hb.query g ν).bind fun b =>
      .pure (a.bind fun x => binopT op h x b)
  | _, _, .seq hd ha => (hd.query g ν).bind fun d =>
      match d with
      | none => .pure none
      | some _ => ha.query g ν
  | _, _, .orElse ha hb => (ha.query g ν).bind fun a =>
      match a with
      | none => hb.query g ν
      | some x => .pure (some x)
  | _, _, .kite (p := p) ha hb ht he => (ha.query g ν).bind fun a => (hb.query g ν).bind fun b =>
      match a, b with
      | some x, some y => @ite _ (x = y) (PrimTy.decEqDenote p x y) (ht.query g ν) (he.query g ν)
      | _, _ => .pure none
  | _, _, .err => .pure none
  | _, _, .zlit n => .pure (some n)
  | _, _, .toInt ht => (ht.query g ν).bind fun v => .pure (v.map fun n => n.1)
  | _, _, .net ht => (ht.query g ν).bind fun v =>
      .pure (v.map fun n => (lookupBy n g.net).getD 0)
  | _, _, .zbin op _ ha hb => (ha.query g ν).bind fun a => (hb.query g ν).bind fun b =>
      .pure (a.bind fun x => b.map fun y => op.evalZ x y)
  | _, _, .zcmp op _ ha hb => (ha.query g ν).bind fun a => (hb.query g ν).bind fun b =>
      .pure (a.bind fun x => b.map fun y => op.cmpZ x y)

/-- Query evaluation agrees with the original term on every actual typed
storage, retaining the other components of its starting state. -/
theorem query_sound (g : State C []) (ν : AEnv) {s : Srt} {t : LTm C s}
    (ht : ReadExpr t) (st : Storage C) :
    ((ht.query g ν).runStorage st).map (ReadDen.erase g) =
      t.eval { g with storage := st } ν := by
  induction ht with
  | var k => rfl
  | lit v => rfl
  | env k => rfl
  | root r h => rfl
  | field h hq ih =>
    simp only [query, Query.runStorage, Query.run_bind, Query.run, LTm.eval_app1,
      Close.Op1.eval_field, ← ih]
    cases (hq.query g ν).run (fun r => r.read st) <;> rfl
  | index hq hk ihq ihk =>
    simp only [query, Query.runStorage, Query.run_bind, Query.run, LTm.eval_index, ← ihq, ← ihk]
    cases (hq.query g ν).run (fun r => r.read st) <;>
      cases (hk.query g ν).run (fun r => r.read st) <;> rfl
  | word hq ih =>
    simp only [query, Query.runStorage, Query.run_bind, LTm.eval_obsW, ← ih]
    cases (hq.query g ν).run (fun r => r.read st) with
    | none => rfl
    | some r =>
      change some ((Ref.mk _ r.val r.property).read st) = some (st.obs.word (.ref r.val))
      exact congrArg some ((Ref.mk _ r.val r.property).obs_read st).symm
  | unop op h ht ih =>
    simp only [query, Query.runStorage, Query.run_bind, Query.run, LTm.eval_app1,
      Close.Op1.eval_unop, ← ih]
    simp only [ReadDen.erase_val, Option.map_id, id_eq]
  | binop op h ha hb iha ihb =>
    simp only [query, Query.runStorage, Query.run_bind, Query.run, LTm.eval_app2,
      Close.Op2.eval_binop, ← iha, ← ihb, ReadDen.erase_val, Option.map_id, id_eq]
    rfl
  | seq hd ha ihd iha =>
    simp only [query, Query.runStorage, Query.run_bind, LTm.eval_seq, ← ihd, ← iha]
    cases (hd.query g ν).run (fun r => r.read st) <;> rfl
  | orElse ha hb iha ihb =>
    simp only [query, Query.runStorage, Query.run_bind, LTm.eval_orElse, ← iha, ← ihb]
    cases (ha.query g ν).run (fun r => r.read st) <;> rfl
  | kite ha hb ht he iha ihb iht ihe =>
    simp only [query, Query.runStorage, Query.run_bind, LTm.eval_kite, ← iha, ← ihb,
      ReadDen.erase_val, Option.map_id, id_eq]
    cases (ha.query g ν).run (fun r => r.read st) <;>
      cases (hb.query g ν).run (fun r => r.read st) <;>
      simp only [Option.bind_none, Option.bind_some, Query.run, Option.map_none]
    split <;> assumption
  | err => rfl
  | zlit n => rfl
  | toInt ht ih | net ht ih =>
    simp only [query, Query.runStorage, Query.run_bind, Query.run, LTm.eval_app1, ← ih]
    cases (ht.query g ν).run (fun r => r.read st) <;> rfl
  | zbin op h ha hb iha ihb | zcmp op h ha hb iha ihb =>
    simp only [query, Query.runStorage, Query.run_bind, Query.run, LTm.eval_app2, ← iha, ← ihb]
    cases (ha.query g ν).run (fun r => r.read st) <;>
      cases (hb.query g ν).run (fun r => r.read st) <;> rfl

end ReadExpr

/-- Quantifier-free formulas whose terms have read queries. -/
inductive ReadFormula : LFml C → Type where
  | tt : ReadFormula .tt
  | eq {p : PrimTy} {a b : LTm C (.val p)} (ha : ReadExpr a) (hb : ReadExpr b) :
      ReadFormula (.eq a b)
  | not {φ : LFml C} (hφ : ReadFormula φ) : ReadFormula (.not φ)
  | and {φ ψ : LFml C} (hφ : ReadFormula φ) (hψ : ReadFormula ψ) : ReadFormula (.and φ ψ)
  | imp {φ ψ : LFml C} (hφ : ReadFormula φ) (hψ : ReadFormula ψ) : ReadFormula (.imp φ ψ)

namespace ReadFormula

/-- Recognize the quantifier-free query fragment. Quantifiers need a
separate parameter or finite-domain decision, not a finite sample. -/
def ofFormula? : (φ : LFml C) → Option (ReadFormula φ)
  | .tt => some .tt
  | .eq a b => do return .eq (← ReadExpr.ofTerm? a) (← ReadExpr.ofTerm? b)
  | .not φ => (ofFormula? φ).map .not
  | .and φ ψ => do return .and (← ofFormula? φ) (← ofFormula? ψ)
  | .imp φ ψ => do return .imp (← ofFormula? φ) (← ofFormula? ψ)
  | .all .. => none

/-- Defined equality: two failed terms do not count as equal. -/
def equal {p : PrimTy} : Option p.Denote → Option p.Denote → Bool
  | some a, some b => decide (a = b)
  | _, _ => false

/-- Evaluate a supported formula using typed read queries. -/
def query (g : State C []) (ν : AEnv) : {φ : LFml C} → ReadFormula φ → Query C Bool
  | _, .tt => .pure true
  | _, .eq ha hb => (ha.query g ν).bind fun a => (hb.query g ν).bind fun b => .pure (equal a b)
  | _, .not hφ => (hφ.query g ν).bind fun b => .pure (!b)
  | _, .and hφ hψ => (hφ.query g ν).bind fun a => (hψ.query g ν).bind fun b => .pure (a && b)
  | _, .imp hφ hψ => (hφ.query g ν).bind fun a => (hψ.query g ν).bind fun b => .pure (!a || b)

/-- Evaluation is exact on every actual storage; failed reads and checked
arithmetic retain their original meaning. -/
theorem query_iff (g : State C []) (ν : AEnv) {φ : LFml C} (hφ : ReadFormula φ)
    (st : Storage C) :
    (hφ.query g ν).runStorage st = true ↔ φ.holds { g with storage := st } ν := by
  induction hφ with
  | tt => exact iff_of_true rfl trivial
  | eq ha hb =>
    simp only [query, Query.runStorage, Query.run_bind, Query.run, LFml.holds,
      ← ha.query_sound g ν st, ← hb.query_sound g ν st, ReadDen.erase_val, Option.map_id, id_eq]
    cases (ha.query g ν).run (fun r => r.read st) <;>
      cases (hb.query g ν).run (fun r => r.read st) <;>
      simp only [equal, Bool.false_eq_true, decide_eq_true_eq]
  | not hφ ih =>
    simp only [query, Query.runStorage, Query.run_bind, Query.run, LFml.holds,
      Bool.not_eq_true', Bool.eq_false_iff, ← ih]
  | and hφ hψ ihφ ihψ =>
    simp only [query, Query.runStorage, Query.run_bind, Query.run, LFml.holds,
      Bool.and_eq_true, ← ihφ, ← ihψ]
  | imp hφ hψ ihφ ihψ =>
    simp only [query, Query.runStorage, Query.run_bind, Query.run, LFml.holds,
      Bool.or_eq_true, Bool.not_eq_true', Bool.eq_false_iff, ← ihφ, ← ihψ]
    grind

/-- Read abstraction is exact: every valuation is realized for the reads
this formula actually uses, even when locations depend on other reads. -/
theorem realize_iff (g : State C []) (ν : AEnv) {φ : LFml C} (hφ : ReadFormula φ)
    (rd : (r : Ref C) → r.Value) :
    φ.holds { g with storage := (hφ.query g ν).realize rd } ν ↔
      (hφ.query g ν).run rd = true := by
  rw [← hφ.query_iff g ν, Query.run_realize]

/-- No counterstates are lost in read abstraction, with transaction,
ledger and heap fixed by the chosen starting state. -/
theorem valid_iff (g : State C []) (ν : AEnv) {φ : LFml C} (hφ : ReadFormula φ) :
    (∀ st : Storage C, φ.holds { g with storage := st } ν) ↔
      ∀ rd : (r : Ref C) → r.Value, (hφ.query g ν).run rd = true := by
  constructor
  · intro h rd
    exact (hφ.realize_iff g ν rd).1 (h _)
  · intro h st
    exact (hφ.query_iff g ν st).1 (h (fun r => r.read st))

/-- A false abstract query materializes a concrete typed counterstate to
the reduced formula, without testing a finite pool of mapping keys. -/
def countermodel (g : State C []) (ν : AEnv) {φ : LFml C} (hφ : ReadFormula φ)
    (rd : (r : Ref C) → r.Value) (h : (hφ.query g ν).run rd = false) :
    { σ : State C [] // ¬ φ.holds σ ν } :=
  ⟨{ g with storage := (hφ.query g ν).realize rd }, fun hv =>
    Bool.noConfusion (h.symm.trans ((hφ.realize_iff g ν rd).1 hv))⟩

end ReadFormula

/-- A universal prefix followed by a recognized quantifier-free body.
Arguments are selected at their actual primitive types, without assuming
that quantified formulas can be established by finitely many samples. -/
inductive ReadSentence : LFml C → Type where
  | body {φ : LFml C} (hφ : ReadFormula φ) : ReadSentence φ
  | all (k : Nat) (p : PrimTy) {φ : LFml C} (hφ : ReadSentence φ) :
      ReadSentence (.all k p φ)

namespace ReadSentence

/-- Recognize precisely a universal prefix and a query body. -/
def ofFormula? : (φ : LFml C) → Option (ReadSentence φ)
  | .all k p φ => (ofFormula? φ).map (.all k p)
  | φ => (ReadFormula.ofFormula? φ).map .body

/-- Decode one typed argument; missing or differently typed entries select
that type's default. This is a total choice of a quantified instance. -/
def argument (p : PrimTy) (args : List CallValue) : p.Denote :=
  (args.head?.bind (CallValue.as? p)).getD (PrimTy.dflt p)

theorem argument_cons (p : PrimTy) (v : p.Denote) (args : List CallValue) :
    argument p (CallValue.ofTyped v :: args) = v := by
  cases p <;> rfl

/-- Select the universal instances, then record the body's read queries. -/
def query (g : State C []) : {φ : LFml C} → ReadSentence φ → AEnv → List CallValue → Query C Bool
  | _, .body hφ, ν, _ => hφ.query g ν
  | _, .all k p hφ, ν, args => hφ.query g (ν.set p k (argument p args)) args.tail

/-- Every instance of a true sentence evaluates true on its real storage. -/
theorem query_of_holds (g : State C []) {φ : LFml C} (hφ : ReadSentence φ)
    (ν : AEnv) (args : List CallValue) (st : Storage C)
    (h : φ.holds { g with storage := st } ν) : (hφ.query g ν args).runStorage st = true := by
  induction hφ generalizing ν args with
  | body hφ => exact (hφ.query_iff g ν st).2 h
  | all k p hφ ih => exact ih _ args.tail (h (argument p args))

/-- Considering all typed argument lists recovers the universal sentence;
the choice representation loses no possible parameter value. -/
theorem holds_of_queries (g : State C []) {φ : LFml C} (hφ : ReadSentence φ)
    (ν : AEnv) (st : Storage C)
    (h : ∀ args : List CallValue, (hφ.query g ν args).runStorage st = true) :
    φ.holds { g with storage := st } ν := by
  induction hφ generalizing ν with
  | body hφ => exact (hφ.query_iff g ν st).1 (h [])
  | all k p hφ ih =>
    intro v
    apply ih
    intro args
    have hc := h (CallValue.ofTyped v :: args)
    simpa only [query, argument_cons, List.tail_cons] using hc

/-- Validity over storage is exactly validity over all typed argument
choices and all actual-location read valuations. -/
theorem valid_iff (g : State C []) {φ : LFml C} (hφ : ReadSentence φ) (ν : AEnv) :
    (∀ st : Storage C, φ.holds { g with storage := st } ν) ↔
      ∀ (args : List CallValue) (rd : (r : Ref C) → r.Value), (hφ.query g ν args).run rd = true := by
  constructor
  · intro h args rd
    rw [← (hφ.query g ν args).run_realize rd]
    exact hφ.query_of_holds g ν args _ (h _)
  · intro h st
    exact hφ.holds_of_queries g ν st (fun args => h args (fun r => r.read st))

/-- A false quantified instance yields a concrete counterstate to the
whole sentence. Arguments witness failure of its universal prefix; they
are not stored as locals of the returned empty-context state. -/
def countermodel (g : State C []) {φ : LFml C} (hφ : ReadSentence φ)
    (ν : AEnv) (args : List CallValue) (rd : (r : Ref C) → r.Value)
    (h : (hφ.query g ν args).run rd = false) : { σ : State C [] // ¬ φ.holds σ ν } :=
  ⟨{ g with storage := (hφ.query g ν args).realize rd }, fun hv =>
    Bool.noConfusion (h.symm.trans ((hφ.query g ν args).run_realize rd ▸
      hφ.query_of_holds g ν args _ hv))⟩

end ReadSentence

/-- Materialize a false read query and transport it back to the original
scoped formula through both exact reduction stages. -/
def ExactReduction.countermodelFromReads {φ : Fml C []} (r : ExactReduction φ)
    (hf : ReadFormula r.leaf.elim) (g : State C []) (rd : (q : Ref C) → q.Value)
    (h : (hf.query g AEnv.dflt).run rd = false) :
    { σ : State C [] // ¬ holds σ φ } :=
  let cm := hf.countermodel g AEnv.dflt rd h
  ⟨cm.val, fun hv => cm.property ((r.elim_holds_iff cm.val).2 hv)⟩

/-- Countermodel transport also retains the original universal parameters. -/
def ExactReduction.countermodelFromInstance {φ : Fml C []} (r : ExactReduction φ)
    (hf : ReadSentence r.leaf.elim) (g : State C []) (args : List CallValue)
    (rd : (q : Ref C) → q.Value) (h : (hf.query g AEnv.dflt args).run rd = false) :
    { σ : State C [] // ¬ holds σ φ } :=
  let cm := hf.countermodel g AEnv.dflt args rd h
  ⟨cm.val, fun hv => cm.property ((r.elim_holds_iff cm.val).2 hv)⟩

/-- Both computed recognition certificates for a source formula. -/
structure ReadReduction (φ : Fml C []) where
  reduction : ExactReduction φ
  sentence : ReadSentence reduction.leaf.elim

/-- Recognize an exact source reduction and its supported typed read
fragment. Rejection carries no validity or falsity verdict. -/
def readReduction? (φ : Fml C []) : Option (ReadReduction φ) := do
  let r ← exactReduction? φ
  let s ← ReadSentence.ofFormula? r.leaf.elim
  return ⟨r, s⟩

namespace ReadReduction

/-- The complete source-to-read-query pipeline is an equivalence on the
recognized fragment, over all original states and all typed parameters. -/
theorem valid_iff {φ : Fml C []} (r : ReadReduction φ) :
    Fml.Valid φ ↔ ∀ (g : State C []) (args : List CallValue) (rd : (q : Ref C) → q.Value),
      (r.sentence.query g AEnv.dflt args).run rd = true := by
  constructor
  · intro h g
    apply (r.sentence.valid_iff g AEnv.dflt).1
    intro st
    exact (r.reduction.elim_holds_iff _).2 (h _)
  · intro h σ
    apply (r.reduction.elim_holds_iff σ).1
    exact ((r.sentence.valid_iff σ AEnv.dflt).2 (h σ)) σ.storage

/-- Reject conflicting aliases, then check a finite proposed read assignment
and reconstruct its selected footprint when it falsifies a supported
instance. This does not search for assignments or decide validity. -/
def countermodel? {φ : Fml C []} (r : ReadReduction φ) (g : State C [])
    (args : List CallValue) (a : Assignment C) : Option { σ : State C [] // ¬ holds σ φ } :=
  if a.consistentB then
    if h : (r.sentence.query g AEnv.dflt args).run (Assignment.lookup a) = false then
      some (r.reduction.countermodelFromInstance r.sentence g args (Assignment.lookup a) h)
    else none
  else none

end ReadReduction

end Solidity.Decide
