import Solidity.Update

/-!
# What a callee may change: its mutability, read off its body

solc's `pure`, `view` and `nonpayable` say what a function may do to the
contract's state.  The elaborator drops `pure` and `view` (`FunDecl` keeps
only `payable`), so here the mutability is read off the inlined body
(`Stmt.within`): a block of statements that write locals only, and
branches, checks and calls of such, is `view`; one whose expressions also
read nothing outside its locals (`Val.readsState`: storage, a storage or
memory read or length, `msg.sender`, `msg.value`, the funds) is `pure`; one
that may also write storage and pay (`a = e;`, `delete`, `x += e`, `x++`
and `v = x++` on storage, `transfer`, `ok = a.send(v)`) is `nonpayable`.  Anything else
(memory, a push or a pop, an alias, an external call) has no mutability
here, and no contract.  A `view` function cannot pay either: solc rejects a
`transfer` in one.

What each guarantees is `Mutability.Frame`, proved once from `Stmt.run`
for every body the check accepts (`Prog.frame_of_within`): the run changes
only the locals the body writes (`Prog.writes`) and, for `nonpayable`, the
storage and the ledger, which is what `State.havoc` replaces (the state a
callback leaves, `Semantics/Callback.lean`).  The two facts a contract rule
reads (`Calculus/Contracts.lean`): a `view` callee leaves storage and, paying
nothing, the ledger as they were (`Prog.view_frame`), and so does a `pure`
one (`Prog.pure_frame`), whose restriction on reads adds nothing to the
frame: a contract's `ensures` may read the state anyway.
-/

namespace Solidity

open Semantics

variable {C : Contract}

/-- solc's mutabilities, the most restrictive first.  `payable` is
`nonpayable` here: a callee's booking of `msg.value` is its caller's. -/
inductive Mutability where
  | pure
  | view
  | nonpayable
  deriving DecidableEq, Repr

/-! ## The check -/

/-- `v` reads something other than locals: a storage read or length, a
memory read or length, `msg.sender`, `msg.value`, the funds. -/
def Val.readsState : {p : PrimTy} → Val C p → Bool
  | _, .simple (.env ..) => true
  | _, .simple _ => false
  | _, .read _ | _, .readMem _ | _, .len .. | _, .mlen .. => true
  | _, .binop _ _ _ a b => a.readsState || b.readsState
  | _, .unop _ _ _ a => a.readsState
  | _, .ternary c a b => c.readsState || a.readsState || b.readsState

/-- A callee of mutability `μ` may evaluate `v`: any value, but a `pure`
one reads no state. -/
def Mutability.reads {p : PrimTy} (μ : Mutability) (v : Val C p) : Bool :=
  μ != .pure || !v.readsState

/-- The target of `x += e` or `x++` is a stack local. -/
def OpLoc.isLocal {p : PrimTy} : OpLoc C p → Bool
  | .local _ => true
  | _ => false

/-- The target of `x += e` or `x++` is in storage. -/
def OpLoc.isStorage {p : PrimTy} : OpLoc C p → Bool
  | .root .. | .field .. | .index .. => true
  | _ => false

/-- The local `x += e` or `x++` writes, if its target is one. -/
def OpLoc.writes {p : PrimTy} : OpLoc C p → List Var
  | .local x => [x]
  | _ => []

mutual

/-- **A statement a callee of mutability `μ` may run**: one writing locals
only (`view`, reading no state if `pure`), or storage and the ledger
(`nonpayable`). -/
def Stmt.within (μ : Mutability) : Stmt C → Bool
  | .assignLocal _ r => μ.reads r
  | .declLocal _ _ none => true
  | .declLocal _ _ (some e) => μ.reads e
  | .opAssign _ _ _ l r => μ.reads r && (l.isLocal || μ == .nonpayable && l.isStorage)
  | .incDec _ _ l | .assignIncDec _ _ _ l _ => l.isLocal || μ == .nonpayable && l.isStorage
  | .require c | .assert c => μ.reads c
  | .revert => true
  | .ite c thn els => μ.reads c && Prog.within μ thn && Prog.within μ els
  | .call _ args _ _ body => args.all (fun a => μ.reads a.e) && Prog.within μ body
  | .loop _ c body => μ.reads c && Prog.within μ body
  | .assign .. | .delete _ | .transfer .. | .send .. => μ == .nonpayable
  | _ => false

def Prog.within (μ : Mutability) : List (Stmt C) → Bool
  | [] => true
  | s :: P => s.within μ && Prog.within μ P

end

mutual

/-- The locals a statement may write: what it assigns or declares, and in a
call the callee's parameters, its return variable, where the result lands,
and its body's. -/
def Stmt.writes : Stmt C → List Var
  | .assignLocal x _ | .declLocal _ x _ => [x]
  | .opAssign _ _ _ l _ | .incDec _ _ l => l.writes
  | .assignIncDec x _ _ l _ => x :: l.writes
  | .ite _ thn els => Prog.writes thn ++ Prog.writes els
  | .call _ args _ ret body => args.map (·.x) ++ ret.vars ++ Prog.writes body
  | .send pv _ _ => [pv]
  | .loop _ _ body => Prog.writes body
  | _ => []

def Prog.writes : List (Stmt C) → List Var
  | [] => []
  | s :: P => s.writes ++ Prog.writes P

end

theorem Prog.within_append (μ : Mutability) :
    (P Q : List (Stmt C)) → Prog.within μ (P ++ Q) = (Prog.within μ P && Prog.within μ Q)
  | [], _ => by simp only [List.nil_append, Prog.within, Bool.true_and]
  | s :: P, Q => by
    simp only [List.cons_append, Prog.within, Prog.within_append μ P Q, Bool.and_assoc]

theorem Prog.writes_append : (P Q : List (Stmt C)) → Prog.writes (P ++ Q) = Prog.writes P ++ Prog.writes Q
  | [], _ => rfl
  | s :: P, Q => by simp only [List.cons_append, Prog.writes, Prog.writes_append P Q, List.append_assoc]

/-! ## The frame -/

/-- **What a callee of mutability `μ` leaves**, from `σ` to `τ`, writing at
most the locals `W`: a `pure` or `view` one changes nothing else; a
`nonpayable` one also the storage and the ledger, so that `τ` is `σ` after
a callback (`State.havoc`) off `W`. -/
def Mutability.Frame (μ : Mutability) (W : List Var) (σ τ : State) : Prop :=
  match μ with
  | .nonpayable => EnvAgreeExcept W (σ.havoc τ.storage τ.net) τ
  | .pure | .view => EnvAgreeExcept W σ τ

namespace Mutability

theorem agree_trans {W : List Var} {σ τ ρ : State} (h₁ : EnvAgreeExcept W σ τ)
    (h₂ : EnvAgreeExcept W τ ρ) : EnvAgreeExcept W σ ρ :=
  ⟨h₁.storage.trans h₂.storage, h₁.heap.trans h₂.heap, h₁.nextId.trans h₂.nextId,
    h₁.net.trans h₂.net, fun n hn => (h₁.env n hn).trans (h₂.env n hn),
    h₁.selfBalance.trans h₂.selfBalance, h₁.tx.trans h₂.tx⟩

theorem agree_mono {W W' : List Var} (hW : ∀ x ∈ W, x ∈ W') {σ τ : State}
    (h : EnvAgreeExcept W σ τ) : EnvAgreeExcept W' σ τ :=
  ⟨h.storage, h.heap, h.nextId, h.net, fun n hn => h.env n fun hw => hn (hW n hw),
    h.selfBalance, h.tx⟩

theorem agree_setEnv {W : List Var} {x : Var} (hx : x ∈ W) (σ : State) (b : Binding) :
    EnvAgreeExcept W σ (σ.setEnv x b) :=
  (EnvAgreeExcept.refl W σ).setEnv_right hx b

theorem Frame.refl (μ : Mutability) (W : List Var) (σ : State) : μ.Frame W σ σ := by
  cases μ
  all_goals first
    | exact EnvAgreeExcept.refl W σ
    | exact (State.havoc_self σ).symm ▸ EnvAgreeExcept.refl W σ

/-- A run that writes locals only is within every mutability. -/
theorem Frame.ofAgree (μ : Mutability) {W : List Var} {σ τ : State} (h : EnvAgreeExcept W σ τ) :
    μ.Frame W σ τ := by
  cases μ
  · exact h
  · exact h
  · exact ⟨rfl, h.heap, h.nextId, rfl, h.env, h.selfBalance, h.tx⟩

theorem Frame.trans {μ : Mutability} {W : List Var} {σ τ ρ : State} (h₁ : μ.Frame W σ τ)
    (h₂ : μ.Frame W τ ρ) : μ.Frame W σ ρ := by
  cases μ
  · exact agree_trans h₁ h₂
  · exact agree_trans h₁ h₂
  · exact ⟨rfl, h₁.heap.trans h₂.heap, h₁.nextId.trans h₂.nextId, rfl,
      fun n hn => (h₁.env n hn).trans (h₂.env n hn), h₁.selfBalance.trans h₂.selfBalance,
      h₁.tx.trans h₂.tx⟩

theorem Frame.mono {μ : Mutability} {W W' : List Var} (hW : ∀ x ∈ W, x ∈ W') {σ τ : State}
    (h : μ.Frame W σ τ) : μ.Frame W' σ τ := by
  cases μ
  · exact agree_mono hW h
  · exact agree_mono hW h
  · exact agree_mono hW h

/-- A write of storage alone is `nonpayable`'s. -/
theorem Frame.storage (W : List Var) (σ : State) (st : List (Name × SVal)) :
    Mutability.nonpayable.Frame W σ { σ with storage := st } :=
  ⟨rfl, rfl, rfl, rfl, fun _ _ => rfl, rfl, rfl⟩

/-- A payment, the ledger alone, is `nonpayable`'s. -/
theorem Frame.net (W : List Var) (σ : State) (nt : List (Int × Int)) :
    Mutability.nonpayable.Frame W σ { σ with net := nt } :=
  ⟨rfl, rfl, rfl, rfl, fun _ _ => rfl, rfl, rfl⟩

end Mutability

/-! ## Each statement within its frame -/

namespace Mutability

open SemanticsProperties

variable {W : List Var} {σ τ : State}

theorem saveStorage_frame {r : Name} {segs : List Seg} {v : SVal}
    (h : σ.saveStorage r segs v = .ok τ) : Mutability.nonpayable.Frame W σ τ := by
  obtain ⟨_, _, _, _, rfl⟩ := State.saveStorage_ok_inv h
  exact Frame.storage W σ _

theorem writeStorage_frame {r : Name} {segs : List Seg} {v : SVal}
    (h : σ.writeStorage r segs v = .ok τ) : Mutability.nonpayable.Frame W σ τ := by
  unfold State.writeStorage at h
  split at h
  · exact saveStorage_frame h
  all_goals
    obtain ⟨_, _, h⟩ := bind_ok_inv h
    exact saveStorage_frame h

theorem opStore_frame {op : BinOp} {p : PrimTy} {r : Name} {segs : List Seg} {v : Value}
    (h : opStore σ op p r segs v = .ok τ) : Mutability.nonpayable.Frame W σ τ := by
  unfold opStore at h
  obtain ⟨_, _, h⟩ := bind_ok_inv h
  obtain ⟨_, _, h⟩ := bind_ok_inv h
  obtain ⟨_, _, h⟩ := bind_ok_inv h
  obtain ⟨_, _, h⟩ := bind_ok_inv h
  exact saveStorage_frame h

theorem bumpStore_frame {op : IncDec} {p : PrimTy} {r : Name} {segs : List Seg} {w : Value}
    (h : bumpStore σ op p r segs = .ok (τ, w)) : Mutability.nonpayable.Frame W σ τ := by
  unfold bumpStore at h
  obtain ⟨_, _, h⟩ := bind_ok_inv h
  obtain ⟨_, _, h⟩ := bind_ok_inv h
  obtain ⟨_, _, h⟩ := bind_ok_inv h
  obtain ⟨_, _, h⟩ := bind_ok_inv h
  obtain ⟨σ', hσ', h⟩ := bind_ok_inv h
  cases h
  exact saveStorage_frame hσ'

theorem opLocal_agree {op : BinOp} {p : PrimTy} {x : Var} {v : Value}
    (h : opLocal σ op p x v = .ok τ) : EnvAgreeExcept [x] σ τ := by
  unfold opLocal at h
  obtain ⟨b, _, h⟩ := bind_ok_inv h
  cases b <;> simp only [bind, Except.bind, reduceCtorEq] at h
  obtain ⟨_, _, h⟩ := bind_ok_inv h
  obtain ⟨_, _, h⟩ := bind_ok_inv h
  cases h
  exact agree_setEnv (List.mem_singleton_self x) σ _

theorem bumpLocal_agree {op : IncDec} {p : PrimTy} {x : Var} {w : Value}
    (h : bumpLocal σ op p x = .ok (τ, w)) : EnvAgreeExcept [x] σ τ := by
  unfold bumpLocal at h
  obtain ⟨b, _, h⟩ := bind_ok_inv h
  cases b <;> simp only [bind, Except.bind, reduceCtorEq] at h
  obtain ⟨_, _, h⟩ := bind_ok_inv h
  obtain ⟨_, _, h⟩ := bind_ok_inv h
  cases h
  exact agree_setEnv (List.mem_singleton_self x) σ _

theorem guardOk_eq {v : Value} (h : guardOk v σ = .ok τ) : σ = τ := by
  unfold guardOk at h
  split at h <;> first | (cases h; rfl) | cases h

theorem assertOk_eq {v : Value} (h : assertOk v σ = .ok τ) : σ = τ := by
  unfold assertOk at h
  split at h <;> first | (cases h; rfl) | cases h

theorem bindSeq_agree : (args : List (Arg C)) → ∀ {σ τ : State},
    Arg.bindSeq args σ = .ok τ → EnvAgreeExcept (args.map (·.x)) σ τ
  | [], _, _, h => by cases h; exact EnvAgreeExcept.refl _ _
  | a :: as, σ, τ, h => by
    simp only [Arg.bindSeq] at h
    obtain ⟨v, _, h⟩ := bind_ok_inv h
    exact agree_trans (agree_setEnv (List.mem_cons_self ..) σ _)
      (agree_mono (fun _ hy => List.mem_cons_of_mem _ hy) (bindSeq_agree as h))

theorem enterAll_agree : (rs : List (PrimTy × Var)) → (σ : State) →
    EnvAgreeExcept (rs.map (·.2)) σ (CallRet.enterAll rs σ)
  | [], σ => EnvAgreeExcept.refl _ σ
  | _ :: rs, σ =>
    agree_trans (agree_setEnv (List.mem_cons_self ..) σ _)
      (agree_mono (fun _ hy => List.mem_cons_of_mem _ hy) (enterAll_agree rs _))

theorem enter_agree (ret : CallRet) (σ : State) : EnvAgreeExcept ret.vars σ (ret.enter σ) := by
  cases ret with
  | none => exact EnvAgreeExcept.refl _ _
  | val p r res => exact agree_setEnv (List.mem_cons_self ..) σ _
  | rets rs => exact enterAll_agree rs σ

theorem leave_agree {ret : CallRet} (h : CallRet.leave (C := C) σ ret = .ok τ) :
    EnvAgreeExcept ret.vars σ τ := by
  rcases ret with _ | ⟨p, r, _ | res⟩ | rs
  · cases h; exact EnvAgreeExcept.refl _ _
  · cases h; exact EnvAgreeExcept.refl _ _
  · simp only [CallRet.leave] at h
    obtain ⟨_, _, h⟩ := bind_ok_inv h
    cases h
    exact agree_setEnv (by simp only [CallRet.vars, Option.toList_some, List.mem_cons, List.not_mem_nil, or_false, or_true]) σ _
  · cases h; exact EnvAgreeExcept.refl _ _

theorem store_frame {μ : Mutability} {p : PrimTy} {op : BinOp} (l : OpLoc C p) {v : Value}
    (hl : (l.isLocal || μ == .nonpayable && l.isStorage) = true) (h : l.store σ op v = .ok τ) :
    μ.Frame l.writes σ τ := by
  cases l with
  | «local» x => exact Frame.ofAgree μ (opLocal_agree h)
  | root r _ =>
    simp only [OpLoc.isLocal, OpLoc.isStorage, Bool.false_or, Bool.and_true, beq_iff_eq] at hl
    subst hl; exact opStore_frame h
  | field b f hf =>
    simp only [OpLoc.isLocal, OpLoc.isStorage, Bool.false_or, Bool.and_true, beq_iff_eq] at hl
    subst hl
    simp only [OpLoc.store] at h
    obtain ⟨_, _, h⟩ := bind_ok_inv h
    exact opStore_frame h
  | index it b i =>
    simp only [OpLoc.isLocal, OpLoc.isStorage, Bool.false_or, Bool.and_true, beq_iff_eq] at hl
    subst hl
    simp only [OpLoc.store] at h
    obtain ⟨_, _, h⟩ := bind_ok_inv h
    exact opStore_frame h
  | mfield => simp only [OpLoc.isLocal, OpLoc.isStorage, Bool.and_false, Bool.or_self, Bool.false_eq_true] at hl
  | mindex => simp only [OpLoc.isLocal, OpLoc.isStorage, Bool.and_false, Bool.or_self, Bool.false_eq_true] at hl

theorem bump_frame {μ : Mutability} {p : PrimTy} {op : IncDec} (l : OpLoc C p) {w : Value}
    (hl : (l.isLocal || μ == .nonpayable && l.isStorage) = true) (h : l.bump σ op = .ok (τ, w)) :
    μ.Frame l.writes σ τ := by
  cases l with
  | «local» x => exact Frame.ofAgree μ (bumpLocal_agree h)
  | root r _ =>
    simp only [OpLoc.isLocal, OpLoc.isStorage, Bool.false_or, Bool.and_true, beq_iff_eq] at hl
    subst hl; exact bumpStore_frame h
  | field b f hf =>
    simp only [OpLoc.isLocal, OpLoc.isStorage, Bool.false_or, Bool.and_true, beq_iff_eq] at hl
    subst hl
    simp only [OpLoc.bump] at h
    obtain ⟨_, _, h⟩ := bind_ok_inv h
    exact bumpStore_frame h
  | index it b i =>
    simp only [OpLoc.isLocal, OpLoc.isStorage, Bool.false_or, Bool.and_true, beq_iff_eq] at hl
    subst hl
    simp only [OpLoc.bump] at h
    obtain ⟨_, _, h⟩ := bind_ok_inv h
    exact bumpStore_frame h
  | mfield => simp only [OpLoc.isLocal, OpLoc.isStorage, Bool.and_false, Bool.or_self, Bool.false_eq_true] at hl
  | mindex => simp only [OpLoc.isLocal, OpLoc.isStorage, Bool.and_false, Bool.or_self, Bool.false_eq_true] at hl

end Mutability

/-! ## The frame of a body -/

section Body

open Mutability

mutual

/-- **A statement within `μ` runs within `μ`'s frame**, writing at most
`s.writes`. -/
theorem Stmt.frame_of_within {μ : Mutability} : (s : Stmt C) → s.within μ = true →
    ∀ {σ τ : State}, s.run σ = .ok τ → μ.Frame s.writes σ τ
  | .assignLocal x _, _, σ, _, h => by
    simp only [Stmt.run] at h
    obtain ⟨_, _, h⟩ := bind_ok_inv h
    cases h
    exact Frame.ofAgree μ (agree_setEnv (List.mem_singleton_self x) σ _)
  | .declLocal _ x init, _, σ, _, h => by
    simp only [Stmt.run] at h
    cases init <;>
    · obtain ⟨_, _, h⟩ := bind_ok_inv h
      cases h
      exact Frame.ofAgree μ (agree_setEnv (List.mem_singleton_self x) σ _)
  | .opAssign _ _ _ l _, hw, _, _, h => by
    simp only [Stmt.within, Bool.and_eq_true] at hw
    simp only [Stmt.run] at h
    obtain ⟨_, _, h⟩ := bind_ok_inv h
    exact store_frame l hw.2 h
  | .incDec _ _ l, hw, _, _, h => by
    simp only [Stmt.within] at hw
    simp only [Stmt.run] at h
    obtain ⟨⟨_, _⟩, hb, h⟩ := bind_ok_inv h
    cases h
    exact bump_frame l hw hb
  | .require _, _, σ, _, h => by
    simp only [Stmt.run] at h
    obtain ⟨_, _, h⟩ := bind_ok_inv h
    cases guardOk_eq h
    exact Frame.refl μ _ σ
  | .assert _, _, σ, _, h => by
    simp only [Stmt.run] at h
    obtain ⟨_, _, h⟩ := bind_ok_inv h
    cases assertOk_eq h
    exact Frame.refl μ _ σ
  | .revert, _, _, _, h => by cases h
  | .ite _ thn els, hw, _, _, h => by
    simp only [Stmt.within, Bool.and_eq_true] at hw
    simp only [Stmt.run] at h
    obtain ⟨_, _, h⟩ := bind_ok_inv h
    split at h
    · exact Frame.mono (fun _ hx => List.mem_append_left _ hx) (Prog.frame_of_within thn hw.1.2 h)
    · exact Frame.mono (fun _ hx => List.mem_append_right _ hx) (Prog.frame_of_within els hw.2 h)
    · cases h
  | .call _ args _ ret body, hw, _, _, h => by
    simp only [Stmt.within, Bool.and_eq_true] at hw
    simp only [Stmt.run] at h
    obtain ⟨σ₁, h₁, h⟩ := bind_ok_inv h
    obtain ⟨σ₂, h₂, h⟩ := bind_ok_inv h
    have e₁ : μ.Frame (args.map (·.x)) _ σ₁ := Frame.ofAgree μ (bindSeq_agree args h₁)
    have e₂ : μ.Frame ret.vars σ₁ (ret.enter σ₁) := Frame.ofAgree μ (enter_agree ret σ₁)
    have e₃ : μ.Frame (Prog.writes body) (ret.enter σ₁) σ₂ := Prog.frame_of_within body hw.2 h₂
    have e₄ : μ.Frame ret.vars σ₂ _ := Frame.ofAgree μ (leave_agree h)
    simp only [Stmt.writes]
    exact (((e₁.mono fun _ hx => by
        simp only [List.append_assoc, List.mem_append, hx, true_or]).trans
      (e₂.mono fun _ hx => by
        simp only [List.append_assoc, List.mem_append, List.mem_map, hx, true_or, or_true])).trans
      (e₃.mono fun _ hx => by
        simp only [List.append_assoc, List.mem_append, List.mem_map, hx, or_true])).trans
      (e₄.mono fun _ hx => by
        simp only [List.append_assoc, List.mem_append, List.mem_map, hx, true_or, or_true])
  | .assign .., hw, _, _, h => by
    simp only [Stmt.within, beq_iff_eq] at hw
    subst hw
    simp only [Stmt.run] at h
    obtain ⟨_, _, h⟩ := bind_ok_inv h
    obtain ⟨_, _, h⟩ := bind_ok_inv h
    exact writeStorage_frame h
  | .delete _, hw, _, _, h => by
    simp only [Stmt.within, beq_iff_eq] at hw
    subst hw
    simp only [Stmt.run] at h
    obtain ⟨_, _, h⟩ := bind_ok_inv h
    obtain ⟨_, _, h⟩ := bind_ok_inv h
    exact saveStorage_frame h
  | .transfer .., hw, σ, _, h => by
    simp only [Stmt.within, beq_iff_eq] at hw
    subst hw
    simp only [Stmt.run] at h
    obtain ⟨_, _, h⟩ := bind_ok_inv h
    obtain ⟨_, _, h⟩ := bind_ok_inv h
    obtain ⟨_, _, h⟩ := bind_ok_inv h
    obtain ⟨_, _, h⟩ := bind_ok_inv h
    unfold transferAt at h
    split at h
    · cases h
    · cases h
      exact Frame.net _ σ _
  | .send pv r a, hw, σ, _, h => by
    simp only [Stmt.within, beq_iff_eq] at hw
    subst hw
    simp only [Stmt.run] at h
    obtain ⟨_, _, h⟩ := bind_ok_inv h
    obtain ⟨_, _, h⟩ := bind_ok_inv h
    obtain ⟨_, _, h⟩ := bind_ok_inv h
    obtain ⟨_, _, h⟩ := bind_ok_inv h
    unfold sendAt at h
    have hpv : pv ∈ Stmt.writes (C := C) (.send pv r a) := List.mem_singleton_self pv
    split at h
    · cases h
    · split at h
      · cases h
        exact (Frame.net _ σ _).trans (Frame.ofAgree _ (agree_setEnv hpv _ _))
      · cases h
        exact (Frame.net _ σ _).trans (Frame.ofAgree _ (agree_setEnv hpv _ _))
      · cases h
        exact Frame.ofAgree _ (agree_setEnv hpv σ _)
  | .assignIncDec x _ _ l _, hw, _, _, h => by
    simp only [Stmt.within] at hw
    simp only [Stmt.run] at h
    obtain ⟨⟨σ', v⟩, hb, h⟩ := bind_ok_inv h
    cases h
    have e₁ : μ.Frame l.writes _ σ' := bump_frame l hw hb
    have e₂ : μ.Frame [x] σ' (σ'.setEnv x (.val v)) :=
      Frame.ofAgree μ (agree_setEnv (List.mem_singleton_self x) σ' _)
    exact (e₁.mono fun _ hy => List.mem_cons_of_mem _ hy).trans
      (e₂.mono fun _ hy => by rw [List.mem_singleton.1 hy]; exact List.mem_cons_self ..)
  | .loop _ c body, hw, σ, _, h => by
    simp only [Stmt.within, Bool.and_eq_true] at hw
    simp only [Stmt.run] at h
    refine Loop.run_induct (P := μ.Frame (Prog.writes body) σ)
      (Q := fun r => ∀ τ, r = .ok τ → μ.Frame (Prog.writes body) σ τ) (Frame.refl μ _ σ)
      (fun τ hτ => ?_) (fun _ h => by cases h) _ h
    simp only [Loop.step]
    rcases c.eval τ with _ | (_ | b)
    · exact fun _ h => by cases h
    · exact fun _ h => by cases h
    · cases b
      · exact fun _ h => by cases h; exact hτ
      · cases hb : Prog.run τ body with
        | error _ => exact fun _ h => by cases h
        | ok τ' => exact hτ.trans (Prog.frame_of_within body hw.2 hb)
  | .rebind .., hw, _, _, _ | .declStorage .., hw, _, _, _
  | .push .., hw, _, _, _ | .pop _, hw, _, _, _ | .declMem .., hw, _, _, _
  | .rebindMem .., hw, _, _, _ | .assignFromMem .., hw, _, _, _ | .assignMem .., hw, _, _, _
  | .deleteMem .., hw, _, _, _ | .assignNew .., hw, _, _, _ | .tryCall .., hw, _, _, _ => by
    simp only [Stmt.within, Bool.false_eq_true] at hw

/-- **A body within `μ` runs within `μ`'s frame**, writing at most
`Prog.writes P`. -/
theorem Prog.frame_of_within {μ : Mutability} : (P : List (Stmt C)) → Prog.within μ P = true →
    ∀ {σ τ : State}, Prog.run σ P = .ok τ → μ.Frame (Prog.writes P) σ τ
  | [], _, σ, _, h => by
    cases h
    exact Frame.refl μ _ σ
  | s :: P, hw, _, _, h => by
    simp only [Prog.within, Bool.and_eq_true] at hw
    simp only [Prog.run] at h
    obtain ⟨_, h₁, h⟩ := bind_ok_inv h
    exact (Frame.mono (fun _ hx => List.mem_append_left _ hx) (Stmt.frame_of_within s hw.1 h₁)).trans
      (Frame.mono (fun _ hx => List.mem_append_right _ hx) (Prog.frame_of_within P hw.2 h))

end

/-- **A `pure` callee leaves storage and ledger as they were.** -/
theorem Prog.pure_frame {P : Prog C} (hμ : Prog.within .pure P = true) {σ τ : State}
    (h : Prog.run σ P = .ok τ) : τ.storage = σ.storage ∧ τ.net = σ.net :=
  have e : EnvAgreeExcept (Prog.writes P) σ τ := Prog.frame_of_within P hμ h
  ⟨e.storage.symm, e.net.symm⟩

/-- **A `view` callee leaves its storage as it was**, and its ledger: it
cannot pay. -/
theorem Prog.view_frame {P : Prog C} (hμ : Prog.within .view P = true) {σ τ : State}
    (h : Prog.run σ P = .ok τ) : τ.storage = σ.storage ∧ τ.net = σ.net :=
  have e : EnvAgreeExcept (Prog.writes P) σ τ := Prog.frame_of_within P hμ h
  ⟨e.storage.symm, e.net.symm⟩

end Body

end Solidity
