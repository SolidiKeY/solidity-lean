import Solidity.Calculus.MemRead.Ok

/-!
# Memory reads: the walk and the pass

The walk down a memory, the hash of a byte string read off it (Lean only),
the pass, and the fold before the elimination.

A piece of `Calculus/MemRead.lean`, whose docstring describes the whole.
-/

namespace Solidity

namespace Decide

open Semantics (lookupBy structDef)

variable {C : Contract}

/-! ## The walk down a memory -/

section Walk

variable {g : State C []} {ν : AEnv}

/-- What a word or identity written is: `mval(x)`'s `x`, `ref(t)`'s `t`. -/
def _root_.Solidity.Op1.mvArg {a s : Srt} (o : Op1 C a s) (x : LTm C a) :
    Option ((u : Srt) × LTm C u) :=
  match o, x with
  | .mval, x => some ⟨_, x⟩
  | .ref, x => some ⟨_, x⟩
  | _, _ => none

/-- What a memory value term writes. -/
def LTm.mvArg? {s : Srt} (v : LTm C s) : Option ((u : Srt) × LTm C u) :=
  match v with
  | .app1 o x => o.mvArg x
  | _ => none

/-- An array-element address, retaining the array's element type. -/
structure ArrayV (C : Contract) where
  {R : RefTy}
  {E : Ty}
  ak : ArrTy R E
  t : LTm C (.ident R)
  i : LTm C (.val .uint)

def arrayArg {a b s : Srt} (o : Op2 C a b s)
    (x : LTm C a) (y : LTm C b) : Option (ArrayV C) :=
  match o, x, y with
  | .mat ak, x, y => some ⟨ak, x, y⟩
  | _, _, _ => none

def arrayV? {s : Srt} (b : LTm C s) : Option (ArrayV C) :=
  match b with
  | .app2 o x y => arrayArg o x y
  | _ => none

/-- `selectOnCopyMemPrim` followed by `initElement`: a primitive read of
the same fresh-array copy, guarded by its size. -/
def copyNewArrayRd? {U : Ty} {P : PrimTy}
    (m : LTm C .mem) (S : LTm C (.sv U)) (b : LTm C (.addr (.prim P))) :
    Option (LTm C (.val P)) := do
  let a ← arrayV? b
  let t ← a.t.castTo? (s' := .ident (.array (.prim P)))
  match t.identView with
  | .copy m' _ S' =>
    if m'.beqR m && S'.beqR S then
      let n ← S'.newArrLen?
      some (.app3 .ite (.app2 (.binop .lt rfl) a.i n) (.lit (PrimTy.dflt P)) .err)
    else none
  | _ => none

theorem copyNewArrayRd?_eval (g : State C []) (ν : AEnv)
    {U : Ty} {hU : U.mapFree = true} {m : LTm C .mem} {S : LTm C (.sv U)}
    {P : PrimTy} {b : LTm C (.addr (.prim P))} {y : LTm C (.val P)}
    (h : copyNewArrayRd? m S b = some y) :
    ((LTm.app2 .read (.app2 (.copySt hU) m S) b).eval g ν : Option P.Denote) =
      (LTm.seq (.app2 (.copySt hU) m S) y).eval g ν := by
  unfold copyNewArrayRd? at h
  obtain ⟨a, ha, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨t, ht, h⟩ := Option.bind_eq_some_iff.1 h
  split at h
  · rename_i m' R' hR S' hview
    split at h
    · rename_i hc
      obtain ⟨n, hn, h⟩ := Option.bind_eq_some_iff.1 h
      cases h
      simp only [Bool.and_eq_true] at hc
      obtain ⟨hm, hS⟩ := hc
      cases LTm.sigma_eq_of_beqR hm
      obtain ⟨hUU, hSS⟩ := Sigma.mk.inj (LTm.sigma_eq_of_beqR hS)
      cases hUU
      cases eq_of_heq hSS
      cases b with
      | app2 o xb ib =>
        cases o <;> simp only [arrayV?, arrayArg, Option.some.injEq] at ha
        rename_i ak
        cases ha
        obtain ⟨hType, het⟩ := Sigma.mk.inj (LTm.castTo?_eq ht)
        cases hType
        cases eq_of_heq het
        have hak : ak = .dyn := match ak with | .dyn => rfl
        rw [hak]
        dsimp only at hview ⊢
        cases xb with
        | app2 o xm xS =>
          cases o <;> simp only [LTm.identView, Op2.identV, reduceCtorEq,
            IdentV.copy.injEq] at hview
          obtain ⟨rfl, hType, heq⟩ := hview
          cases hType
          cases eq_of_heq heq
          cases xS with
          | app1 o z =>
            cases o <;> simp only [LTm.newArrLen?, Op1.newArrArg,
              Option.some.injEq, reduceCtorEq] at hn
            subst n
            simp only [LTm.eval_app1, LTm.eval_app2, LTm.eval_app3, LTm.eval_seq,
              Op1.eval_eq_evalM, Op2.eval_eq_evalM, Op3.eval_eq_evalM,
              Op1.evalM, Op2.evalM, Op3.evalM, Option.bind_eq_bind]
            cases hx : (xm.eval g ν : Option (Grown g.H (fun _ => Unit))) <;>
              (try simp only [Option.bind_none, Option.bind_some])
            rename_i μ
            cases hz : (z.eval g ν : Option PrimTy.uint.Denote) <;>
              (try simp only [Option.map_none, Option.map_some, Option.bind_none, Option.bind_some])
            rename_i v
            cases hi : (ib.eval g ν : Option PrimTy.uint.Denote) <;>
              (try simp only [Option.bind_none, Option.bind_some])
            rename_i k
            simp only [Grown.readT, Grown.then, MAddrT.resolve_eq_resolveM, MAddrT.resolveM,
              HRef.ofId?_self, Option.map_some]
            simp only [Option.bind_eq_bind, Option.bind_some]
            rw [newArrT_copy_prim_index]
            change (if k.1.toNat < v.1.toNat then some (PrimTy.dflt P) else none) =
              (bif decide (k.1 < v.1) then some (PrimTy.dflt P) else none)
            have hv := v.2
            have hk := k.2
            simp only [PrimTy.inRange, decide_eq_true_eq] at hv hk
            have he : (k.1.toNat < v.1.toNat) = (k.1 < v.1) := propext (by omega)
            simp only [he]
            by_cases hc : k.1 < v.1 <;>
              simp only [hc, decide_true, decide_false, if_true, if_false] <;> rfl
          | _ => simp only [LTm.newArrLen?, reduceCtorEq] at hn
        | app1 o x => cases o <;> simp only [LTm.identView, Op1.identV, reduceCtorEq] at hview
        | _ => simp only [LTm.identView, reduceCtorEq] at hview
      | _ => simp only [arrayV?, reduceCtorEq] at ha
    · cases h
  · cases h

/-- **A read of a word, walked down its memory** `n` writes and
allocations deep: `readOnWrite`, `readOnWriteFrame`, `readOnAddMFrame`,
`readOnAddM`.  By the recursor on the depth. -/
def memReadN (n : Nat) : {P : PrimTy} → LTm C .mem → LTm C (.addr (.prim P)) → LTm C (.val P) :=
  Nat.rec (motive := fun _ => {P : PrimTy} → LTm C .mem → LTm C (.addr (.prim P)) → LTm C (.val P))
    (fun X b => .app2 .read X b)
    (fun _ ih {P} X b =>
      match X.memView with
      | .write m a v =>
        if a.hoistA.2.beqR b then
          match v.mvArg? with
          | some ⟨_, x⟩ =>
            match x.castTo? with
            | some x' => seqMemL X x'
            | none => .app2 .read X b
          | none => .app2 .read X b
        else if a.apart? b then seqMemL X (ih m b)
        else .app2 .read X b
      | .addM m R _ =>
        if b.boundedIn m then ih m b
        else if (LTm.freshPath? m R b).bind (Ty.ref R).memberTy == some (.prim P) then
          seqMemL m (.lit (PrimTy.dflt P))
        else .app2 .read X b
      | .copySt m _ S =>
        if b.boundedIn m then seqMemL S (ih m b)
        else
          match copyFieldRd? m S (b.unstripAddr m) with
          | some y => seqMemL X y
          | none =>
            match copyNewArrayRd? m S (b.unstripAddr m) with
            | some y => seqMemL X y
            | none =>
              match copyPathRd? X m S b with
              | some y => seqMemL X y
              | none => .app2 .read X b
      | .other => .app2 .read X b) n

/-- **A read of an identity, walked down its memory.** -/
def memIReadN (n : Nat) : {R : RefTy} → LTm C .mem → LTm C (.addr (.ref R)) → LTm C (.ident R) :=
  Nat.rec (motive := fun _ => {R : RefTy} → LTm C .mem → LTm C (.addr (.ref R)) → LTm C (.ident R))
    (fun X b => .app2 .iread X b)
    (fun _ ih {R} X b =>
      match X.memView with
      | .write m a v =>
        if a.hoistA.2.beqR b then
          match v.mvArg? with
          | some ⟨_, x⟩ =>
            match x.castTo? with
            | some x' => seqMemL X x'
            | none => .app2 .iread X b
          | none => .app2 .iread X b
        else if a.apart? b then seqMemL X (ih m b)
        else .app2 .iread X b
      | .addM m _ _ =>
        if b.boundedIn m then ih m b else .app2 .iread X b
      | .copySt m _ S =>
        if b.boundedIn m then seqMemL S (ih m b) else .app2 .iread X b
      | .other => .app2 .iread X b) n

theorem memReadN_eval (n : Nat) : ∀ {P : PrimTy} (X : LTm C .mem) (b : LTm C (.addr (.prim P))),
    ((memReadN n X b).eval g ν : Option P.Denote) = (LTm.app2 .read X b).eval g ν := by
  induction n with
  | zero => intro P X b; rfl
  | succ n ih =>
    intro P X b
    show (match X.memView with
      | .write m a v =>
        if a.hoistA.2.beqR b then
          match v.mvArg? with
          | some ⟨_, x⟩ =>
            match x.castTo? with
            | some x' => seqMemL X x'
            | none => .app2 .read X b
          | none => .app2 .read X b
        else if a.apart? b then seqMemL X (memReadN n m b)
        else .app2 .read X b
      | .addM m R _ =>
        if b.boundedIn m then memReadN n m b
        else if (LTm.freshPath? m R b).bind (Ty.ref R).memberTy == some (.prim P) then
          seqMemL m (.lit (PrimTy.dflt P))
        else .app2 .read X b
      | .copySt m _ S =>
        if b.boundedIn m then seqMemL S (memReadN n m b)
        else
          match copyFieldRd? m S (b.unstripAddr m) with
          | some y => seqMemL X y
          | none =>
            match copyNewArrayRd? m S (b.unstripAddr m) with
            | some y => seqMemL X y
            | none =>
              match copyPathRd? X m S b with
              | some y => seqMemL X y
              | none => .app2 .read X b
      | .other => .app2 .read X b : LTm C (.val P)).eval g ν = _
    split
    · rename_i m T a v hX
      obtain rfl := LTm.memView_write hX
      split
      · rename_i hab
        cases LTm.sigma_eq_of_beqR hab
        split
        · rename_i u x hv
          split
          · rename_i x' hx
            cases LTm.castTo?_eq hx
            cases v with
            | app1 o y =>
              cases o <;> simp only [LTm.mvArg?, Op1.mvArg, reduceCtorEq, Option.some.injEq] at hv
              obtain ⟨-, h⟩ := Sigma.mk.inj hv
              cases h
              rw [seqMemL_eval]; exact (LTm.read_write_hoist m _ x').symm
            | _ => simp only [LTm.mvArg?, reduceCtorEq] at hv
          · rfl
        · rfl
      · split
        · rename_i hap
          rw [seqMemL_eval, LTm.read_write_apart' m a v b hap, LTm.eval_seq, LTm.eval_seq, ih]
        · rfl
    · rename_i m R hR hX
      obtain rfl := LTm.memView_addM hX
      split
      · rename_i hb
        rw [ih, LTm.read_addM_old m R hR b hb]
      · split
        · rename_i hf
          rw [seqMemL_eval]; exact (LTm.read_addM_fresh m R hR b (beq_iff_eq.1 hf)).symm
        · rfl
    · rename_i m U hU S hX
      obtain rfl := LTm.memView_copySt hX
      split
      · rename_i hb
        rw [seqMemL_eval, LTm.read_copySt_old m hU S b hb, LTm.eval_seq, LTm.eval_seq, ih]
      · split
        · rename_i y hy
          rw [seqMemL_eval, ← LTm.read_unstrip]
          exact (copyFieldRd?_eval hy).symm
        · split
          · rename_i y hy
            rw [seqMemL_eval, ← LTm.read_unstrip]
            exact (copyNewArrayRd?_eval g ν hy).symm
          · split
            · rename_i y hy
              rw [seqMemL_eval]
              exact (copyPathRd?_eval hy).symm
            · rfl
    · rfl

theorem memIReadN_eval (n : Nat) : ∀ {R : RefTy} (X : LTm C .mem) (b : LTm C (.addr (.ref R))),
    ((memIReadN n X b).eval g ν : Option Nat) = (LTm.app2 .iread X b).eval g ν := by
  induction n with
  | zero => intro R X b; rfl
  | succ n ih =>
    intro R X b
    show (match X.memView with
      | .write m a v =>
        if a.hoistA.2.beqR b then
          match v.mvArg? with
          | some ⟨_, x⟩ =>
            match x.castTo? with
            | some x' => seqMemL X x'
            | none => .app2 .iread X b
          | none => .app2 .iread X b
        else if a.apart? b then seqMemL X (memIReadN n m b)
        else .app2 .iread X b
      | .addM m _ _ =>
        if b.boundedIn m then memIReadN n m b else .app2 .iread X b
      | .copySt m _ S =>
        if b.boundedIn m then seqMemL S (memIReadN n m b) else .app2 .iread X b
      | .other => .app2 .iread X b : LTm C (.ident R)).eval g ν = _
    split
    · rename_i m T a v hX
      obtain rfl := LTm.memView_write hX
      split
      · rename_i hab
        cases LTm.sigma_eq_of_beqR hab
        split
        · rename_i u x hv
          split
          · rename_i x' hx
            cases LTm.castTo?_eq hx
            cases v with
            | app1 o y =>
              cases o <;> simp only [LTm.mvArg?, Op1.mvArg, reduceCtorEq, Option.some.injEq] at hv
              obtain ⟨-, h⟩ := Sigma.mk.inj hv
              cases h
              rw [seqMemL_eval]; exact (LTm.iread_write_hoist m _ x').symm
            | _ => simp only [LTm.mvArg?, reduceCtorEq] at hv
          · rfl
        · rfl
      · split
        · rename_i hap
          rw [seqMemL_eval, LTm.iread_write_apart' m a v b hap, LTm.eval_seq, LTm.eval_seq, ih]
        · rfl
    · rename_i m R' hR hX
      obtain rfl := LTm.memView_addM hX
      split
      · rename_i hb
        rw [ih, LTm.iread_addM_old m R' hR b hb]
      · rfl
    · rename_i m U hU S hX
      obtain rfl := LTm.memView_copySt hX
      split
      · rename_i hb
        rw [seqMemL_eval, LTm.iread_copySt_old m hU S b hb, LTm.eval_seq, LTm.eval_seq, ih]
      · rfl
    · rfl

end Walk

/-! ## The hash of a byte string read off the memory (Lean only)

Where a byte string's length and every byte read down the memory to
literals (`lenAtN`, `memReadN`), a hash of it (`keccak256`, `sha256`,
`ripemd160`: `HashKind.apply`) is that function of
those bytes, which the kernel evaluates; no solkey taclet reads a hash
(solkey's `keccak256` is uninterpreted). -/

section Keccak

variable {g : State C []} {ν : AEnv}

/-- The literal a term comes to where it returns: a literal, under at most
`n` sequences or guards (`guardL`'s `kite c true a err`).  By recursion on
`n`, so that the kernel evaluates it. -/
def LTm.litInN {p : PrimTy} : Nat → LTm C (.val p) → Option p.Denote
  | 0, _ => none
  | n + 1, t =>
    match t with
    | .app0 (.lit v) => some v
    | .seq _ a => LTm.litInN n a
    | .kite _ _ t e => if e.isErr then LTm.litInN n t else none
    | _ => none

/-- `litInN` within the memory's fuel. -/
def LTm.litIn? {p : PrimTy} (t : LTm C (.val p)) : Option p.Denote := LTm.litInN memFuel t

theorem LTm.litInN_eval {p : PrimTy} (n : Nat) : ∀ (t : LTm C (.val p)) {v : p.Denote},
    LTm.litInN n t = some v → ∀ {x : p.Denote}, (t.eval g ν : Option p.Denote) = some x → x = v := by
  induction n with
  | zero => intro t v h; cases h
  | succ n ih =>
    intro t v h x hx
    unfold LTm.litInN at h
    split at h
    · cases h
      exact (Option.some.inj hx).symm
    · rename_i d a
      rw [LTm.eval_seq] at hx
      cases hd : d.eval g ν with
      | none => rw [hd] at hx; cases hx
      | some _ =>
        rw [hd, Option.bind_some] at hx
        exact ih a h hx
    · rename_i q a b t e
      split at h
      · rename_i he
        rw [LTm.eval_kite] at hx
        cases ha : (a.eval g ν : Option q.Denote) with
        | none => rw [ha] at hx; cases hx
        | some u =>
          rw [ha, Option.bind_some] at hx
          cases hb : (b.eval g ν : Option q.Denote) with
          | none => rw [hb] at hx; cases hx
          | some w =>
            rw [hb, Option.bind_some] at hx
            split at hx
            · exact ih t h hx
            · rw [LTm.eval_of_isErr g ν he] at hx; cases hx
      · cases h
    · cases h

theorem LTm.litIn?_eval {p : PrimTy} (t : LTm C (.val p)) {v : p.Denote} (h : t.litIn? = some v)
    {x : p.Denote} (hx : (t.eval g ν : Option p.Denote) = some x) : x = v :=
  LTm.litInN_eval memFuel t h hx

/-- The bytes `i, i+1, …, i+k-1` of the byte string `t` in `X`, each read
down the memory (`memReadN`) to a literal. -/
def keccakWords (rd : PrimTy.uint.Denote → Option PrimTy.uint.Denote) :
    Nat → Nat → Option (List PrimTy.uint.Denote)
  | 0, _ => some []
  | k + 1, i =>
    match rd (uintOfNat i) with
    | some v =>
      match keccakWords rd k (i + 1) with
      | some vs => some (v :: vs)
      | none => none
    | none => none

/-- The most bytes a hash is read for. -/
def keccakMaxBytes : Nat := 64

/-- **The hash of a byte string read off the memory** (Lean only): where
its length and every byte read down the memory to literals, the hash `k` is
evaluated on them (`HashKind.apply`); where the memory does not return, the
symbol as it was. -/
def keccakAt (k : HashKind) (X : LTm C .mem) (t : LTm C (.ident (.array (.prim .uint)))) : LTm C (.val .uint) :=
  match (lenAtN memFuel X t).litIn? with
  | some n =>
    if n.1.toNat ≤ keccakMaxBytes then
      match keccakWords (fun iv => (memReadN memFuel X (.app2 (.mat .dyn) t (.lit iv))).litIn?)
          n.1.toNat 0 with
      | some vs => .orElse (.seq (seqMemL X (lenAtN memFuel X t))
          (.lit (k.apply (vs.map (·.1))))) (.app2 (.hash k) X t)
      | none => .app2 (.hash k) X t
    else .app2 (.hash k) X t
  | none => .app2 (.hash k) X t

/-- `keccakAt` at a byte string, the symbol elsewhere; any hashing builtin `k` (`HashKind.apply`). -/
def keccakRes (k : HashKind) {R : RefTy} (X : LTm C .mem) (t : LTm C (.ident R)) : LTm C (.val .uint) :=
  match R, t with
  | .array (.prim .uint), t => keccakAt k X t
  | _, t => .app2 (.hash k) X t

theorem eval_read_mat (X : LTm C .mem) (t : LTm C (.ident (.array (.prim .uint))))
    (iv : PrimTy.uint.Denote) (μ : Grown g.H (fun _ => Unit)) (id : Nat)
    (hX : X.eval g ν = some μ) (ht : t.eval g ν = some id) :
    ((LTm.app2 .read X (.app2 (.mat .dyn) t (.lit iv))).eval g ν : Option PrimTy.uint.Denote) =
      (HRef.ofId? μ.H' (.array (.prim .uint)) id).bind fun r => μ.heap.index r .dyn iv := by
  rw [LTm.eval_app2, LTm.eval_app2, hX, ht]
  show (μ.readT (MAddrT.index id .dyn iv)) = _
  unfold Grown.readT
  rw [MAddrT.resolve_eq_resolveM]
  simp only [MAddrT.resolveM]
  cases HRef.ofId? μ.H' (.array (.prim .uint)) id <;> rfl

theorem eval_mlen_some (X : LTm C .mem) (t : LTm C (.ident (.array (.prim .uint))))
    {ℓ : PrimTy.uint.Denote} (h : ((LTm.app2 .mlen X t).eval g ν : Option PrimTy.uint.Denote) = some ℓ) :
    ∃ μ id r, X.eval g ν = some μ ∧ t.eval g ν = some id ∧
      HRef.ofId? μ.H' (.array (.prim .uint)) id = some r ∧ μ.heap.lenU r = ℓ := by
  rw [LTm.eval_app2, Op2.eval_eq_evalM] at h
  cases hX : X.eval g ν with
  | none => rw [hX] at h; cases h
  | some μ =>
    cases ht : t.eval g ν with
    | none => rw [hX, ht] at h; cases h
    | some id =>
      rw [hX, ht] at h
      change (HRef.ofId? μ.H' (.array (.prim .uint)) id).bind (fun r => some (μ.heap.lenU r)) =
        some ℓ at h
      cases hr : HRef.ofId? μ.H' (.array (.prim .uint)) id with
      | none => rw [hr] at h; cases h
      | some r =>
        rw [hr] at h
        exact ⟨μ, id, r, rfl, rfl, hr, Option.some.inj h⟩

theorem keccakWords_spec (rd : PrimTy.uint.Denote → Option PrimTy.uint.Denote) (k : Nat) :
    ∀ (i : Nat) (vs : List PrimTy.uint.Denote), keccakWords rd k i = some vs →
      vs.length = k ∧ ∀ (j : Nat) (hj : j < vs.length), rd (uintOfNat (i + j)) = some vs[j] := by
  induction k with
  | zero =>
    intro i vs h
    cases h
    exact ⟨rfl, fun j hj => absurd hj (Nat.not_lt_zero _)⟩
  | succ k ih =>
    intro i vs h
    unfold keccakWords at h
    cases hv : rd (uintOfNat i) with
    | none => rw [hv] at h; cases h
    | some v =>
      rw [hv] at h
      cases hws : keccakWords rd k (i + 1) with
      | none => rw [hws] at h; cases h
      | some ws =>
        rw [hws] at h
        cases h
        obtain ⟨hlen, hall⟩ := ih (i + 1) ws hws
        refine ⟨by simp only [List.length_cons, hlen], ?_⟩
        intro j hj
        cases j with
        | zero => exact hv
        | succ j =>
          have := hall j (by simp only [List.length_cons] at hj; omega)
          rw [show i + (j + 1) = i + 1 + j by omega]
          exact this

theorem keccakAt_eval (k : HashKind) (X : LTm C .mem) (t : LTm C (.ident (.array (.prim .uint)))) :
    (keccakAt k X t).eval g ν = (LTm.app2 (.hash k) X t).eval g ν := by
  unfold keccakAt
  split
  · rename_i n hn
    split
    · split
      · rename_i vs hvs
        rw [LTm.eval_orElse]
        cases hL : ((LTm.seq (seqMemL X (lenAtN memFuel X t))
            (.lit (k.apply (vs.map (·.1))))).eval g ν : Option PrimTy.uint.Denote) with
        | none => rfl
        | some x =>
          show some x = _
          rw [LTm.eval_seq, seqMemL_eval, LTm.eval_seq] at hL
          cases hX : X.eval g ν with
          | none => rw [hX] at hL; cases hL
          | some μ =>
            rw [hX, Option.bind_some] at hL
            cases hℓ : ((lenAtN memFuel X t).eval g ν : Option PrimTy.uint.Denote) with
            | none => rw [hℓ] at hL; cases hL
            | some ℓ =>
              rw [hℓ] at hL
              simp only [Option.bind_some] at hL
              have hx : x = k.apply (vs.map (·.1)) := (Option.some.inj hL).symm
              have hℓn := LTm.litIn?_eval _ hn hℓ
              rw [lenAtN_eval memFuel X t μ hX] at hℓ
              obtain ⟨μ', id, r, hX', ht, hr, hlen⟩ := eval_mlen_some X t hℓ
              rw [hX] at hX'
              cases hX'
              obtain ⟨hvl, hall⟩ := keccakWords_spec _ _ 0 vs hvs
              -- the object's bytes are `vs`
              have hE : MObj.elems .dyn (μ.heap.get r) = vs := by
                have hl : (MObj.elems .dyn (μ.heap.get r)).length = n.1.toNat := by
                  have h1 : (μ.heap.lenU r).1 = ((μ.heap.len r .dyn : Nat) : Int) := rfl
                  rw [hlen, hℓn] at h1
                  unfold Heap.len at h1
                  omega
                apply List.ext_getElem (by rw [hl, hvl])
                intro j h1 h2
                have hrd := hall j h2
                rw [Nat.zero_add] at hrd
                have e := eval_read_mat (g := g) (ν := ν) X t (uintOfNat j) μ id hX ht
                rw [← memReadN_eval memFuel] at e
                rw [hr, Option.bind_some] at e
                unfold Heap.index at e
                have hj : (uintOfNat j).1.toNat = j := by
                  have hn256 := uint_lt n
                  have hjn : j < n.1.toNat := hl ▸ h1
                  rw [uintOfNat_val (by omega)]; rfl
                rw [hj, List.getElem?_eq_getElem h1] at e
                exact LTm.litIn?_eval _ hrd e
              rw [LTm.eval_app2, hX, ht, hx]
              show some (k.apply (vs.map (·.1))) = some (μ.hashId k _ id)
              unfold Grown.hashId
              rw [hr]
              show _ = some (k.apply (MObj.words _ (μ.heap.get r)))
              rw [← hE, MObj.elems_dyn]
              rfl
      · rfl
    · rfl
  · rfl

theorem keccakRes_eval (k : HashKind) {R : RefTy} (X : LTm C .mem) (t : LTm C (.ident R)) :
    (keccakRes k X t).eval g ν = (LTm.app2 (.hash k) X t).eval g ν := by
  unfold keccakRes
  split
  · exact keccakAt_eval k X _
  · rfl

end Keccak

/-! ## The pass -/

section Pass

variable {g : State C []} {ν : AEnv}

/-- **An identity minted over a memory, minted over its allocations**
(`LTm.stripW`, Lean only: solkey names it by a Skolem `freshIdp`): where
every word the memory's writes land on folds to `true` (`guardQ`,
`LTm.isTrueC`), the root of a copy over the memory is the root over it
without its writes, which no longer carries the writes before it; else the
identity is kept as it is, so that the copy's laws still see it. -/
def copyRes {R : RefTy} (h : (Ty.ref R).mapFree = true) (X : LTm C .mem)
    (S : LTm C (.sv (.ref R))) : LTm C (.ident R) :=
  let X' := X.stripW
  if X'.beqR X then .app2 (.copy h) X S
  else match guardQ X with
    | some cs => if cs.all LTm.isTrueC then .app2 (.copy h) X' S else .app2 (.copy h) X S
    | none => .app2 (.copy h) X S

theorem copyRes_eval {R : RefTy} (h : (Ty.ref R).mapFree = true) (X : LTm C .mem)
    (S : LTm C (.sv (.ref R))) :
    (copyRes h X S).eval g ν = (LTm.app2 (.copy h) X S).eval g ν := by
  unfold copyRes
  dsimp only
  split
  · rfl
  split
  · rename_i cs hq
    split
    · rename_i hall
      have hc : AllT g ν cs := fun c hc =>
        LTm.isTrueC_eval (List.all_eq_true.1 hall c hc)
      obtain ⟨μ, hX⟩ := Option.isSome_iff_exists.1 ((guardQ_sound hq).2 hc)
      exact LTm.copy_stripW_eval hX h S
    · rfl
  · rfl

theorem seqMemL_tt_eval {s : Srt} (d : LTm C s) :
    ((seqMemL d .tt).eval g ν : Option Bool) = (seqL d .tt).eval g ν := by
  rw [seqMemL_eval, LTm.eval_seq, seqL_eval]

/-- A binary symbol, its reads of memory walked. -/
def _root_.Solidity.Op2.memRes {a b s : Srt} (o : Op2 C a b s) (x : LTm C a) (y : LTm C b) :
    LTm C s :=
  match o, x, y with
  | .read, X, b => wrapG b.hoistA.1 (memReadN memFuel X b.hoistA.2)
  | .iread, X, b => wrapG b.hoistA.1 (memIReadN memFuel X b.hoistA.2)
  | .mlen, X, t => wrapG t.peel.1 (seqMemL X (lenAtN memFuel X t.peel.2))
  | .hash k, X, t => keccakRes k X t
  | .copy h, X, S => copyRes h X S
  | o, x, y => .app2 o x y

theorem Op2.memRes_eval {a b s : Srt} (o : Op2 C a b s) (x : LTm C a) (y : LTm C b) :
    (o.memRes x y).eval g ν = (LTm.app2 o x y).eval g ν := by
  cases o
  case read =>
    simp only [Op2.memRes]
    rw [LTm.app2_hoistA .read rfl x y]
    exact wrapG_congr _ (memReadN_eval _ x _)
  case iread =>
    simp only [Op2.memRes]
    rw [LTm.app2_hoistA .iread rfl x y]
    exact wrapG_congr _ (memIReadN_eval _ x _)
  case mlen =>
    simp only [Op2.memRes]
    rw [LTm.app2_peel .mlen rfl x y]
    refine wrapG_congr _ ?_
    rw [seqMemL_eval, LTm.eval_seq]
    cases hx : (x.eval g ν : Option (Grown g.H (fun _ => Unit))) with
    | none => rw [LTm.eval_app2_none _ _ _ hx]; rfl
    | some μ => exact lenAtN_eval memFuel x _ μ hx
  case hash k => simp only [Op2.memRes]; exact keccakRes_eval k x y
  case copy h => simp only [Op2.memRes]; exact copyRes_eval h x y
  all_goals simp only [Op2.memRes]

/-- `LTm.memRes`'s compiled twin. -/
def LTm.memResM : {s : Srt} → LTm C s → LTm C s
  | _, .var k => .var k
  | _, .app0 o => .app0 o
  | _, .app1 o x => .app1 o x.memResM
  | _, .app2 o x y => o.memRes x.memResM y.memResM
  | _, .app3 o x y z => .app3 o x.memResM y.memResM z.memResM
  | _, .index it q i => .index it q.memResM i.memResM
  | _, .obsW q => .obsW q.memResM
  | _, .obsL q => .obsL q.memResM
  | _, .obsH q => .obsH q.memResM
  | _, .seq d a => .seq d.memResM a.memResM
  | _, .orElse a b => .orElse a.memResM b.memResM
  | _, .kite a b t e => .kite a.memResM b.memResM t.memResM e.memResM
  | _, .err => .err

/-- **Every read of memory walked down its memory**, bottom-up.  By the
recursor. -/
@[implemented_by LTm.memResM]
def LTm.memRes {s : Srt} (t : LTm C s) : LTm C s :=
  @LTm.rec C (fun s _ => LTm C s)
    (@fun _ k => .var k) (@fun _ o => .app0 o)
    (@fun _ _ o _ ihx => .app1 o ihx)
    (@fun _ _ _ o _ _ ihx ihy => o.memRes ihx ihy)
    (@fun _ _ _ _ o _ _ _ ihx ihy ihz => .app3 o ihx ihy ihz)
    (@fun _ _ _ it _ _ ihq ihi => .index it ihq ihi)
    (@fun _ _ ih => .obsW ih) (@fun _ _ ih => .obsL ih) (@fun _ _ ih => .obsH ih)
    (@fun _ _ _ _ ihd iha => .seq ihd iha)
    (@fun _ _ _ iha ihb => .orElse iha ihb)
    (@fun _ _ _ _ _ _ iha ihb iht ihe => .kite iha ihb iht ihe)
    (@fun _ => .err) s t

theorem LTm.memRes_eq_memResM {s : Srt} (t : LTm C s) : t.memRes = t.memResM := by
  induction t with
  | var | app0 | err => rfl
  | app1 o x ih => simp only [LTm.memResM, ← ih]; rfl
  | app2 o x y ihx ihy => simp only [LTm.memResM, ← ihx, ← ihy]; rfl
  | app3 o x y z ihx ihy ihz => simp only [LTm.memResM, ← ihx, ← ihy, ← ihz]; rfl
  | index it q i ihq ihi => simp only [LTm.memResM, ← ihq, ← ihi]; rfl
  | obsW q ih | obsL q ih | obsH q ih => simp only [LTm.memResM, ← ih]; rfl
  | seq d a ihd iha => simp only [LTm.memResM, ← ihd, ← iha]; rfl
  | orElse a b iha ihb => simp only [LTm.memResM, ← iha, ← ihb]; rfl
  | kite a b t e iha ihb iht ihe => simp only [LTm.memResM, ← iha, ← ihb, ← iht, ← ihe]; rfl

/-- **The pass keeps what a term reads.** -/
theorem LTm.memRes_eval {s : Srt} (t : LTm C s) : t.memRes.eval g ν = t.eval g ν := by
  induction t with
  | var | app0 | err => rfl
  | app1 o x ih =>
    show (LTm.app1 o x.memRes).eval g ν = _
    rw [LTm.eval_app1, LTm.eval_app1, ih]
  | app2 o x y ihx ihy =>
    show (o.memRes x.memRes y.memRes).eval g ν = _
    rw [Op2.memRes_eval, LTm.eval_app2, LTm.eval_app2, ihx, ihy]
  | app3 o x y z ihx ihy ihz =>
    show (LTm.app3 o x.memRes y.memRes z.memRes).eval g ν = _
    rw [LTm.eval_app3, LTm.eval_app3, ihx, ihy, ihz]
  | index it q i ihq ihi =>
    show (LTm.index it q.memRes i.memRes).eval g ν = _
    rw [LTm.eval_index, LTm.eval_index, ihq, ihi]
  | obsW q ih =>
    show (LTm.obsW q.memRes).eval g ν = _
    rw [LTm.eval_obsW, LTm.eval_obsW, ih]
  | obsL q ih =>
    show (LTm.obsL q.memRes).eval g ν = _
    rw [LTm.eval_obsL, LTm.eval_obsL, ih]
  | obsH q ih =>
    show (LTm.obsH q.memRes).eval g ν = _
    rw [LTm.eval_obsH, LTm.eval_obsH, ih]
  | seq d a ihd iha =>
    show (LTm.seq d.memRes a.memRes).eval g ν = _
    rw [LTm.eval_seq, LTm.eval_seq, ihd, iha]
  | orElse a b iha ihb =>
    show (LTm.orElse a.memRes b.memRes).eval g ν = _
    rw [LTm.eval_orElse, LTm.eval_orElse, iha, ihb]
  | kite a b t e iha ihb iht ihe =>
    show (LTm.kite a.memRes b.memRes t.memRes e.memRes).eval g ν = _
    rw [LTm.eval_kite, LTm.eval_kite, iha, ihb, iht, ihe]

/-- `LTm.seqMem`'s compiled twin. -/
def LTm.seqMemM : {s : Srt} → LTm C s → LTm C s
  | _, .var k => .var k
  | _, .app0 o => .app0 o
  | _, .app1 o x => .app1 o x.seqMemM
  | _, .app2 o x y => .app2 o x.seqMemM y.seqMemM
  | _, .app3 o x y z => .app3 o x.seqMemM y.seqMemM z.seqMemM
  | _, .index it q i => .index it q.seqMemM i.seqMemM
  | _, .obsW q => .obsW q.seqMemM
  | _, .obsL q => .obsL q.seqMemM
  | _, .obsH q => .obsH q.seqMemM
  | _, .seq d a => seqMemL d.seqMemM a.seqMemM
  | _, .orElse a b => .orElse a.seqMemM b.seqMemM
  | _, .kite a b t e => .kite a.seqMemM b.seqMemM t.seqMemM e.seqMemM
  | _, .err => .err

/-- **Every guard of a memory that returns dropped.**  By the recursor. -/
@[implemented_by LTm.seqMemM]
def LTm.seqMem {s : Srt} (t : LTm C s) : LTm C s :=
  @LTm.rec C (fun s _ => LTm C s)
    (@fun _ k => .var k) (@fun _ o => .app0 o)
    (@fun _ _ o _ ihx => .app1 o ihx)
    (@fun _ _ _ o _ _ ihx ihy => .app2 o ihx ihy)
    (@fun _ _ _ _ o _ _ _ ihx ihy ihz => .app3 o ihx ihy ihz)
    (@fun _ _ _ it _ _ ihq ihi => .index it ihq ihi)
    (@fun _ _ ih => .obsW ih) (@fun _ _ ih => .obsL ih) (@fun _ _ ih => .obsH ih)
    (@fun _ _ _ _ ihd iha => seqMemL ihd iha)
    (@fun _ _ _ iha ihb => .orElse iha ihb)
    (@fun _ _ _ _ _ _ iha ihb iht ihe => .kite iha ihb iht ihe)
    (@fun _ => .err) s t

theorem LTm.seqMem_eq_seqMemM {s : Srt} (t : LTm C s) : t.seqMem = t.seqMemM := by
  induction t with
  | var | app0 | err => rfl
  | app1 o x ih | obsW x ih | obsL x ih | obsH x ih => simp only [LTm.seqMemM, ← ih]; rfl
  | app2 o x y ihx ihy => simp only [LTm.seqMemM, ← ihx, ← ihy]; rfl
  | app3 o x y z ihx ihy ihz => simp only [LTm.seqMemM, ← ihx, ← ihy, ← ihz]; rfl
  | index it q i ihq ihi => simp only [LTm.seqMemM, ← ihq, ← ihi]; rfl
  | seq d a ihd iha => simp only [LTm.seqMemM, ← ihd, ← iha]; rfl
  | orElse a b iha ihb => simp only [LTm.seqMemM, ← iha, ← ihb]; rfl
  | kite a b t e iha ihb iht ihe => simp only [LTm.seqMemM, ← iha, ← ihb, ← iht, ← ihe]; rfl

theorem LTm.seqMem_eval {s : Srt} (t : LTm C s) : t.seqMem.eval g ν = t.eval g ν := by
  induction t with
  | var | app0 | err => rfl
  | app1 o x ih =>
    show (LTm.app1 o x.seqMem).eval g ν = _
    rw [LTm.eval_app1, LTm.eval_app1, ih]
  | app2 o x y ihx ihy =>
    show (LTm.app2 o x.seqMem y.seqMem).eval g ν = _
    rw [LTm.eval_app2, LTm.eval_app2, ihx, ihy]
  | app3 o x y z ihx ihy ihz =>
    show (LTm.app3 o x.seqMem y.seqMem z.seqMem).eval g ν = _
    rw [LTm.eval_app3, LTm.eval_app3, ihx, ihy, ihz]
  | index it q i ihq ihi =>
    show (LTm.index it q.seqMem i.seqMem).eval g ν = _
    rw [LTm.eval_index, LTm.eval_index, ihq, ihi]
  | obsW q ih =>
    show (LTm.obsW q.seqMem).eval g ν = _
    rw [LTm.eval_obsW, LTm.eval_obsW, ih]
  | obsL q ih =>
    show (LTm.obsL q.seqMem).eval g ν = _
    rw [LTm.eval_obsL, LTm.eval_obsL, ih]
  | obsH q ih =>
    show (LTm.obsH q.seqMem).eval g ν = _
    rw [LTm.eval_obsH, LTm.eval_obsH, ih]
  | seq d a ihd iha =>
    show (seqMemL d.seqMem a.seqMem).eval g ν = _
    rw [seqMemL_eval, LTm.eval_seq, LTm.eval_seq, ihd, iha]
  | orElse a b iha ihb =>
    show (LTm.orElse a.seqMem b.seqMem).eval g ν = _
    rw [LTm.eval_orElse, LTm.eval_orElse, iha, ihb]
  | kite a b t e iha ihb iht ihe =>
    show (LTm.kite a.seqMem b.seqMem t.seqMem e.seqMem).eval g ν = _
    rw [LTm.eval_kite, LTm.eval_kite, iha, ihb, iht, ihe]

/-- `LFml.memRes`'s compiled twin. -/
def LFml.memResM : LFml C → LFml C
  | .tt => .tt
  | .eq a b => .eq (({} : Facts C).nf a).memRes.seqMem (({} : Facts C).nf b).memRes.seqMem
  | .not φ => .not φ.memResM
  | .and φ ψ => .and φ.memResM ψ.memResM
  | .imp φ ψ => .imp φ.memResM ψ.memResM
  | .all k p φ => .all k p φ.memResM

/-- **Every read of memory in a formula walked.**  By the recursor. -/
@[implemented_by LFml.memResM]
def LFml.memRes (φ : LFml C) : LFml C :=
  @LFml.rec C (fun _ => LFml C) .tt
    (@fun _ a b => .eq (({} : Facts C).nf a).memRes.seqMem (({} : Facts C).nf b).memRes.seqMem)
    (fun _ ih => .not ih) (fun _ _ ihφ ihψ => .and ihφ ihψ) (fun _ _ ihφ ihψ => .imp ihφ ihψ)
    (fun k p _ ih => .all k p ih) φ

theorem LFml.memRes_eq_memResM (φ : LFml C) : φ.memRes = φ.memResM := by
  induction φ with
  | tt | eq => rfl
  | not φ ih | all k p φ ih => simp only [LFml.memResM, ← ih]; rfl
  | and φ ψ ihφ ihψ | imp φ ψ ihφ ihψ => simp only [LFml.memResM, ← ihφ, ← ihψ]; rfl

theorem LFml.memRes_holds (φ : LFml C) : ∀ (ν : AEnv), φ.memRes.holds g ν ↔ φ.holds g ν := by
  induction φ with
  | tt => intro ν; exact Iff.rfl
  | eq a b =>
    intro ν
    show (LFml.eq (({} : Facts C).nf a).memRes.seqMem
      (({} : Facts C).nf b).memRes.seqMem).holds g ν ↔ _
    rw [LFml.holds_eq_iff, LFml.holds_eq_iff, LTm.seqMem_eval, LTm.seqMem_eval, LTm.memRes_eval,
      LTm.memRes_eval, Facts.nf_eval (Facts.ok_empty ν), Facts.nf_eval (Facts.ok_empty ν)]
  | not φ ih => intro ν; exact not_congr (ih ν)
  | and φ ψ ihφ ihψ => intro ν; exact and_congr (ihφ ν) (ihψ ν)
  | imp φ ψ ihφ ihψ => intro ν; exact imp_congr (ihφ ν) (ihψ ν)
  | all k p φ ih => intro ν; exact forall_congr' fun v => ih _

theorem LFml.memRes_valid {φ : LFml C} (h : φ.memRes.Valid) : φ.Valid :=
  fun g ν => (LFml.memRes_holds φ ν).1 (h g ν)

end Pass

/-- A read of a storage term the elimination did not take: `find`, `len`,
`sfind`. -/
def _root_.Solidity.Op2.isStRd {a b s : Srt} : Op2 C a b s → Bool
  | .find | .len | .sfind => true
  | _ => false

/-- `LTm.hasStRd`'s compiled twin. -/
def LTm.hasStRdM : {s : Srt} → LTm C s → Bool
  | _, .app1 _ x => x.hasStRdM
  | _, .app2 o x y => o.isStRd || x.hasStRdM || y.hasStRdM
  | _, .app3 _ x y z => x.hasStRdM || y.hasStRdM || z.hasStRdM
  | _, .index _ q i => q.hasStRdM || i.hasStRdM
  | _, .seq d a => d.hasStRdM || a.hasStRdM
  | _, .orElse a b => a.hasStRdM || b.hasStRdM
  | _, .kite a b t e => a.hasStRdM || b.hasStRdM || t.hasStRdM || e.hasStRdM
  | _, _ => false

/-- **A term with a storage read left**: one the walk of memory exposed
(a member of a copy of storage) for the elimination to take.  By the
recursor. -/
@[implemented_by LTm.hasStRdM]
def LTm.hasStRd {s : Srt} (t : LTm C s) : Bool :=
  @LTm.rec C (fun _ _ => Bool)
    (@fun _ _ => false) (@fun _ _ => false)
    (@fun _ _ _ _ ihx => ihx)
    (@fun _ _ _ o _ _ ihx ihy => o.isStRd || ihx || ihy)
    (@fun _ _ _ _ _ _ _ _ ihx ihy ihz => ihx || ihy || ihz)
    (@fun _ _ _ _ _ _ ihq ihi => ihq || ihi)
    (@fun _ _ _ => false) (@fun _ _ _ => false) (@fun _ _ _ => false)
    (@fun _ _ _ _ ihd iha => ihd || iha)
    (@fun _ _ _ iha ihb => iha || ihb)
    (@fun _ _ _ _ _ _ iha ihb iht ihe => iha || ihb || iht || ihe)
    (@fun _ => false) s t

theorem LTm.hasStRd_eq_hasStRdM {s : Srt} (t : LTm C s) : t.hasStRd = t.hasStRdM := by
  induction t with
  | var | app0 | obsW | obsL | obsH | err => rfl
  | app1 o x ih => simp only [LTm.hasStRdM, ← ih]; rfl
  | app2 o x y ihx ihy => simp only [LTm.hasStRdM, ← ihx, ← ihy]; rfl
  | app3 o x y z ihx ihy ihz => simp only [LTm.hasStRdM, ← ihx, ← ihy, ← ihz]; rfl
  | index it q i ihq ihi => simp only [LTm.hasStRdM, ← ihq, ← ihi]; rfl
  | seq d a ihd iha => simp only [LTm.hasStRdM, ← ihd, ← iha]; rfl
  | orElse a b iha ihb => simp only [LTm.hasStRdM, ← iha, ← ihb]; rfl
  | kite a b t e iha ihb iht ihe => simp only [LTm.hasStRdM, ← iha, ← ihb, ← iht, ← ihe]; rfl

/-- `LFml.hasStRd`'s compiled twin. -/
def LFml.hasStRdM : LFml C → Bool
  | .eq a b => a.hasStRd || b.hasStRd
  | .not φ => φ.hasStRdM
  | .and φ ψ | .imp φ ψ => φ.hasStRdM || ψ.hasStRdM
  | .all _ _ φ => φ.hasStRdM
  | .tt => false

/-- A formula with a storage read left.  By the recursor. -/
@[implemented_by LFml.hasStRdM]
def LFml.hasStRd (φ : LFml C) : Bool :=
  @LFml.rec C (fun _ => Bool) false (@fun _ a b => a.hasStRd || b.hasStRd)
    (fun _ ih => ih) (fun _ _ ihφ ihψ => ihφ || ihψ) (fun _ _ ihφ ihψ => ihφ || ihψ)
    (fun _ _ _ ih => ih) φ

theorem LFml.hasStRd_eq_hasStRdM (φ : LFml C) : φ.hasStRd = φ.hasStRdM := by
  induction φ with
  | tt | eq => rfl
  | not φ ih | all k p φ ih => simp only [LFml.hasStRdM, ← ih]; rfl
  | and φ ψ ihφ ihψ | imp φ ψ ihφ ihψ => simp only [LFml.hasStRdM, ← ihφ, ← ihψ]; rfl

/-- The storage reads a walk of memory exposed (a member of a copy of
storage, a guard of a copy's source) eliminated once more (`LFml.elim`),
and memory walked again. -/
def LFml.memElim (φ : LFml C) : LFml C :=
  if φ.hasStRd then φ.elim.memRes else φ

theorem LFml.memElim_valid {φ : LFml C} (h : φ.memElim.Valid) : φ.Valid := by
  unfold LFml.memElim at h
  split at h
  · exact fun g ν => (LFml.elim_holds g φ ν).1 (LFml.memRes_valid h g ν)
  · exact h

/-- **The closer with memory read**: every read of memory walked
(`LFml.memRes`), the storage reads that walk exposed eliminated and the
memory walked again (`LFml.memElim`), then `LFml.close`; where that does
not close, once more, for the reads the second walk exposed (the guards
of a copy's source on a word read below the copy's root). -/
def LFml.closeMem (φ : LFml C) : Bool := closeTwice φ.memRes.memElim
where
  /-- `ψ` closed, or closed after one more elimination. -/
  closeTwice (ψ : LFml C) : Bool := ψ.close || (ψ.hasStRd && ψ.memElim.close)

theorem LFml.closeMem_valid {φ : LFml C} (h : φ.closeMem = true) : φ.Valid := by
  unfold LFml.closeMem LFml.closeMem.closeTwice at h
  rcases Bool.or_eq_true_iff.1 h with h | h
  · exact LFml.memRes_valid (LFml.memElim_valid (LFml.close_valid h))
  · exact LFml.memRes_valid (LFml.memElim_valid (LFml.memElim_valid
      (LFml.close_valid (Bool.and_eq_true_iff.1 h).2)))

/-! ## Before the elimination -/

section Fold

variable {g : State C []}

/-- `LFml.nfE`'s compiled twin. -/
def LFml.nfEM : LFml C → LFml C
  | .tt => .tt
  | .eq a b => .eq (({} : Facts C).nf a) (({} : Facts C).nf b)
  | .not φ => .not φ.nfEM
  | .and φ ψ => .and φ.nfEM ψ.nfEM
  | .imp φ ψ => .imp φ.nfEM ψ.nfEM
  | .all k p φ => .all k p φ.nfEM

/-- **Every term in its normal form with no premise**: literals folded, so
that the elimination compares keys it can (`keyCmp`).  By the recursor. -/
@[implemented_by LFml.nfEM]
def LFml.nfE (φ : LFml C) : LFml C :=
  @LFml.rec C (fun _ => LFml C) .tt
    (@fun _ a b => .eq (({} : Facts C).nf a) (({} : Facts C).nf b))
    (fun _ ih => .not ih) (fun _ _ ihφ ihψ => .and ihφ ihψ) (fun _ _ ihφ ihψ => .imp ihφ ihψ)
    (fun k p _ ih => .all k p ih) φ

theorem LFml.nfE_eq_nfEM (φ : LFml C) : φ.nfE = φ.nfEM := by
  induction φ with
  | tt | eq => rfl
  | not φ ih | all k p φ ih => simp only [LFml.nfEM, ← ih]; rfl
  | and φ ψ ihφ ihψ | imp φ ψ ihφ ihψ => simp only [LFml.nfEM, ← ihφ, ← ihψ]; rfl

theorem LFml.nfE_holds (φ : LFml C) : ∀ (ν : AEnv), φ.nfE.holds g ν ↔ φ.holds g ν := by
  induction φ with
  | tt => intro ν; exact Iff.rfl
  | eq a b =>
    intro ν
    show (LFml.eq (({} : Facts C).nf a) (({} : Facts C).nf b)).holds g ν ↔ _
    rw [LFml.holds_eq_iff, LFml.holds_eq_iff, Facts.nf_eval (Facts.ok_empty ν),
      Facts.nf_eval (Facts.ok_empty ν)]
  | not φ ih => intro ν; exact not_congr (ih ν)
  | and φ ψ ihφ ihψ => intro ν; exact and_congr (ihφ ν) (ihψ ν)
  | imp φ ψ ihφ ihψ => intro ν; exact imp_congr (ihφ ν) (ihψ ν)
  | all k p φ ih => intro ν; exact forall_congr' fun v => ih _

/-- **`sol_decide` on a reduction**: its terms folded (`LFml.nfE`), the
reads of writes eliminated under its premises (`LFml.elimF`), memory read and closed
(`LFml.closeMem`). -/
def LFml.decideMem (φ : LFml C) : Bool := (φ.nfE.elimF {}).closeMem

theorem LFml.decideMem_valid {φ : LFml C} (h : φ.decideMem = true) : φ.Valid := fun g ν =>
  (LFml.nfE_holds φ ν).1 ((LFml.elimF_holds g φ.nfE {} ν (Facts.ok_empty ν)).1
    (LFml.closeMem_valid h g ν))

end Fold

end Decide

end Solidity
