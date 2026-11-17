import Solidity.Correctness.IntrinsicSession.Run
import Solidity.Correctness.IntrinsicSession.Spec
import Solidity.Correctness.IntrinsicSession.View
import Solidity.Goals.IntrinsicSession

/-!
# The intrinsic session: boundary invariant and unfolding lemmas

Shared lemmas of the lanes of `IntrinsicSession.Laws` (plan step
`is0p0-session-invariants`); no goal. A boundary is a `Walks` from the start's
`origin` (`boundary_mk`, through `walk_go`), reached at a good bound
(`boundary_iff`); `Boundary.next` and its companions decompose one action of
`act` (the step at a good bound, `Bound.upto`); listed worlds are boundaries.
-/

namespace Solidity.Semantics.IntrinsicSession

open Solidity.Roadmap
open Solidity.Goals.IntrinsicSession (Code TypedWorld Good Observed)
open Solidity.ContractWorld (World)

/-! ## Walking from a boundary -/

section Walk

variable {contracts : List Contract}
  (entry : (k : Fin contracts.length) → Bytes → Option (ContractWorld.Entry contracts[k] Bytes))
  (F : Fixed) (wire : Wire) (r : Bound) (e : SessionEnv)

/-- The boundary (history, world) `k` completed actions after `(h, n, w)`. -/
noncomputable def walk (h : List Event) (n : Nat) (w : World (catalog contracts)) :
    Nat → Option (List Event × World (catalog contracts))
  | 0 => some (h, w)
  | k + 1 =>
    match e.requests h n with
    | none => none
    | some a =>
      let s := step entry F wire r e h n w a
      if s.stops then none else walk (h ++ s.events) (n + 1) s.world k

variable {entry F wire r e}

/-- One more completed action extends a walk. -/
theorem walk_succ {a : Action} : ∀ (k : Nat) {h h' : List Event} {n : Nat}
    {w w' : World (catalog contracts)}, walk entry F wire r e h n w k = some (h', w') →
    e.requests h' (n + k) = some a → (step entry F wire r e h' (n + k) w' a).stops = false →
    walk entry F wire r e h n w (k + 1) =
      some (h' ++ (step entry F wire r e h' (n + k) w' a).events,
        (step entry F wire r e h' (n + k) w' a).world)
  | 0, h, h', n, w, w', reach, next, completes => by
    simp only [walk, Option.some.injEq, Prod.mk.injEq] at reach
    obtain ⟨rfl, rfl⟩ := reach
    simp only [Nat.add_zero, Nat.zero_add] at next completes ⊢
    simp only [walk, next, completes, Bool.false_eq_true, if_false]
  | k + 1, h, h', n, w, w', reach, next, completes => by
    rw [show n + (k + 1) = n + 1 + k by omega] at next completes ⊢
    cases req : e.requests h n with
    | none => simp [walk, req] at reach
    | some a0 =>
      cases cont : (step entry F wire r e h n w a0).stops
      · simp only [walk, req, cont, Bool.false_eq_true, if_false] at reach ⊢
        exact walk_succ k reach next completes
      · simp [walk, req, cont] at reach

/-- **A walk leads the run**: the walked worlds and frames, then `go` from its end. -/
theorem walk_go : ∀ (k : Nat) {h h' : List Event} {n : Nat} {w w' : World (catalog contracts)},
    walk entry F wire r e h n w k = some (h', w') →
    ∃ ws fs, ws.length = k ∧ (w :: ws).getLast? = some w' ∧ ∀ j,
      go entry F wire r e h n w (k + j) =
        ⟨(go entry F wire r e h' (n + k) w' j).pfx,
          ws ++ (go entry F wire r e h' (n + k) w' j).worlds,
          fs ++ (go entry F wire r e h' (n + k) w' j).frames⟩
  | 0, h, h', n, w, w', reach => by
    simp only [walk, Option.some.injEq, Prod.mk.injEq] at reach
    obtain ⟨rfl, rfl⟩ := reach
    exact ⟨[], [], rfl, rfl, fun j => by rw [Nat.zero_add, Nat.add_zero]; rfl⟩
  | k + 1, h, h', n, w, w', reach => by
    cases req : e.requests h n with
    | none => simp [walk, req] at reach
    | some a =>
      cases cont : (step entry F wire r e h n w a).stops
      · simp only [walk, req, cont, Bool.false_eq_true, if_false] at reach
        obtain ⟨ws, fs, len, last, eq⟩ := walk_go k reach
        refine ⟨_ :: ws, (step entry F wire r e h n w a).frames ++ fs, by simp [len],
          by rw [List.getLast?_cons_cons]; exact last, fun j => ?_⟩
        rw [show k + 1 + j = k + j + 1 by omega, go_step req cont]
        dsimp only
        rw [eq j, show n + 1 + k = n + (k + 1) by omega]
        simp only [Run.after, List.cons_append, List.append_assoc]
      · simp [walk, req, cont] at reach

/-- A walk that stops before `k` actions leaves fewer than `k` worlds. -/
theorem walk_none : ∀ (k : Nat) {h : List Event} {n : Nat} {w : World (catalog contracts)},
    walk entry F wire r e h n w k = none →
      ∀ j, (go entry F wire r e h n w (k + j)).worlds.length < k
  | 0, _, _, _, stop, _ => by simp [walk] at stop
  | k + 1, h, n, w, stop, j => by
    rw [show k + 1 + j = k + j + 1 by omega]
    cases req : e.requests h n with
    | none => rw [go_idle req]; exact Nat.succ_pos k
    | some a =>
      cases cont : (step entry F wire r e h n w a).stops
      · simp only [walk, req, cont, Bool.false_eq_true, if_false] at stop
        rw [go_step req cont]; exact Nat.succ_lt_succ (walk_none k stop j)
      · rw [go_stops req cont]; exact Nat.succ_pos k

/-- The run through `k` actions lists at most `k` worlds. -/
theorem go_length : ∀ (k : Nat) (h : List Event) (n : Nat) (w : World (catalog contracts)),
    (go entry F wire r e h n w k).worlds.length ≤ k
  | 0, _, _, _ => Nat.le_refl 0
  | k + 1, h, n, w => by
    cases req : e.requests h n with
    | none => rw [go_idle req]; exact Nat.zero_le _
    | some a =>
      cases cont : (step entry F wire r e h n w a).stops
      · rw [go_step req cont]; exact Nat.succ_le_succ (go_length k _ _ _)
      · rw [go_stops req cont]; exact Nat.zero_le _

end Walk

/-! ## Good bounds and unfolding -/

/-- The bound at horizon `k` without resource failure. -/
abbrev Bound.upto (k : Nat) : Bound := { horizon := k }

variable {F : Fixed} {x : Start} {e : SessionEnv} {r r' : Bound} {h : List Event} {n : Nat}
  {w : World (catalog x.code.contracts)} {a : Action}

theorem good_iff : Good (spec F) r ↔ r.NoFail := ⟨And.right, fun noFail => ⟨trivial, noFail⟩⟩
theorem good_upto (F : Fixed) (k : Nat) : Good (spec F) (Bound.upto k) :=
  ⟨trivial, rfl, fun _ => rfl⟩
theorem upto_le {a b : Nat} (le : a ≤ b) : Bound.upto a ≤ Bound.upto b := ⟨le, rfl, rfl⟩

/-- A good bound is the bound without failure at its horizon. -/
theorem good_eq (good : Good (spec F) r) : r = Bound.upto r.horizon := by
  obtain ⟨_, _, _⟩ := r; obtain ⟨_, rfl, f⟩ := good; cases funext f; rfl

/-- **Good bounds have common upper bounds.** -/
theorem good_directed (good : Good (spec F) r) (good' : Good (spec F) r') :
    ∃ r'', Good (spec F) r'' ∧ (spec F).lang.resLE.le r r'' ∧ (spec F).lang.resLE.le r' r'' :=
  directed good good'

theorem le_iff : (spec F).lang.resLE.le r r' ↔ r ≤ r' := Iff.rfl
theorem noFail_iff : (spec F).NoFail r ↔ r.NoFail := Iff.rfl
theorem view_boundary : (view F).Boundary = Boundary F := rfl
theorem sem_eq : (spec F).lang.sem x e r = (runOf F x e r).pfx := rfl
theorem worlds_eq :
    (spec F).worlds x e r = (runOf F x e r).worlds.map fun w => ⟨x.code, .boundary w⟩ := rfl
theorem hashed_eq : (spec F).hashed x e r =
    x.stored ++ (runOf F x e r).frames.flatMap fun f => f.inputs.hashed := rfl
theorem slotHashed_eq : (spec F).slotHashed x e r =
    x.stored ++ (runOf F x e r).frames.flatMap fun f => f.inputs.slots := rfl
theorem forward_iff : (spec F).lang.Forward x e r ↔
    r.NoFail ∧ distinctCount ((spec F).hashed x e r) < hashBound := Iff.rfl
theorem guard_iff : (spec F).lang.Guard x e r ↔
    HashPremise F ((spec F).hashed x e r) ((spec F).slotHashed x e r) := Iff.rfl

/-- The one-action step of `Step.lean` at a bound without resource failure. -/
noncomputable abbrev act (F : Fixed) (x : Start) (e : SessionEnv) (h : List Event) (n : Nat)
    (w : World (catalog x.code.contracts)) (a : Action) : StepOut (catalog x.code.contracts) :=
  step x.code.entry F wire (Bound.upto 0) e h n w a

/-- The deployment of `Step.lean` at a bound without resource failure. -/
noncomputable abbrev deployed (F : Fixed) (code : Code) (e : SessionEnv) :
    StepOut (catalog code.contracts) :=
  deploy code.main code.roles code.ctor F wire (Bound.upto 0) e

/-- The first boundary: the resumed world, or a completed deployment's. -/
noncomputable def Start.origin (F : Fixed) (e : SessionEnv) (x : Start) :
    Option (List Event × World (catalog x.code.contracts)) :=
  match x.world with
  | .boundary w => some ([], w)
  | .fresh => if (deployed F x.code e).stops then none
    else some ((deployed F x.code e).events, (deployed F x.code e).world)

/-- From its origin, `n` actions of `x` complete with the history `h` and world `w`. -/
def Walks (F : Fixed) (x : Start) (e : SessionEnv) (h : List Event) (n : Nat)
    (w : World (catalog x.code.contracts)) : Prop :=
  ∃ h0 w0, x.origin F e = some (h0, w0) ∧
    walk x.code.entry F wire (Bound.upto 0) e h0 0 w0 n = some (h, w)

/-- The run at a good bound starts at the origin. -/
theorem runOf_origin (good : Good (spec F) r) :
    (∀ h0 w0, x.origin F e = some (h0, w0) →
      x.boundaries (runOf F x e r).worlds =
        w0 :: (go x.code.entry F wire (Bound.upto 0) e h0 0 w0 r.horizon).worlds ∧
      (runOf F x e r).pfx = (go x.code.entry F wire (Bound.upto 0) e h0 0 w0 r.horizon).pfx) ∧
    (x.origin F e = none →
      x.boundaries (runOf F x e r).worlds = [] ∧ (runOf F x e r).pfx = ⟨[], none⟩) := by
  obtain ⟨k, rfl⟩ : ∃ k, r = Bound.upto k := ⟨_, good_eq good⟩
  obtain ⟨code, _ | w0⟩ := x
  · dsimp only [runOf]
    cases stop : (deployed F code e).stops
    · rw [run_fresh (r := Bound.upto k) stop]
      dsimp only
      rw [deploy_bound (r := Bound.upto k) (r' := Bound.upto 0) rfl,
        go_bound (r := Bound.upto k) (r' := Bound.upto 0) rfl]
      refine ⟨fun h0 w0 o => ?_, fun o => by simp [Start.origin, stop] at o⟩
      simp only [Start.origin, stop, Bool.false_eq_true, if_false, Option.some.injEq,
        Prod.mk.injEq] at o
      obtain ⟨rfl, rfl⟩ := o
      exact ⟨rfl, rfl⟩
    · rw [run_fresh_stops (r := Bound.upto k) stop]
      exact ⟨fun h0 w0 o => by simp [Start.origin, stop] at o, fun _ => ⟨rfl, rfl⟩⟩
  · refine ⟨fun h0 w0' o => ?_, fun o => nomatch o⟩
    simp only [Start.origin, Option.some.injEq, Prod.mk.injEq] at o
    obtain ⟨rfl, rfl⟩ := o
    rw [show runOf F ⟨code, .boundary w0⟩ e (Bound.upto k) =
      go code.entry F wire (Bound.upto 0) e [] 0 w0 k from
      go_bound (r := Bound.upto k) (r' := Bound.upto 0) rfl k [] 0 w0]
    exact ⟨rfl, rfl⟩

/-- **A good bound past a walk** lists its world at `n` and continues as `go`. -/
theorem Walks.run (walks : Walks F x e h n w)
    (good : Good (spec F) r) (le : n ≤ r.horizon) :
    (x.boundaries (runOf F x e r).worlds)[n]? = some w ∧
    (runOf F x e r).pfx = (go x.code.entry F wire (Bound.upto 0) e h n w (r.horizon - n)).pfx := by
  obtain ⟨h0, w0, o, wk⟩ := walks
  obtain ⟨bnds, pfx⟩ := (runOf_origin good).1 h0 w0 o
  obtain ⟨ws, fs, len, last, eq⟩ := walk_go n wk
  have run := eq (r.horizon - n)
  rw [Nat.add_sub_cancel' le] at run
  simp only [Nat.zero_add] at run
  rw [bnds, pfx, run, ← List.cons_append, List.getElem?_append_left (by simp [len]), ← last,
    List.getLast?_eq_getElem?]
  simp [len]

/-- **A boundary is a walk** from the session's origin. -/
theorem boundary_mk :
    (view F).Boundary x e h n ⟨x.code, w⟩ ↔ Walks F x e h n w := by
  have stands {h w} (walks : Walks F x e h n w) : Stands F x e h n w := by
    obtain ⟨h0, w0, o, wk⟩ := walks
    obtain ⟨bnds, pfx⟩ := (runOf_origin (good_upto F n)).1 h0 w0 o
    obtain ⟨ws, fs, len, last, eq⟩ := walk_go n wk
    have run := eq 0
    simp only [Nat.zero_add, Nat.add_zero] at run
    rw [Stands, pfx, bnds, run]
    exact ⟨rfl, by simp [len, go_zero], by simpa [go_zero] using last⟩
  refine ⟨fun ⟨w', eq, st⟩ => ?_, fun walks => ⟨w, rfl, stands walks⟩⟩
  cases eq
  have len := st.2.1
  cases o : x.origin F e with
  | none => rw [((runOf_origin (good_upto F n)).2 o).1] at len; cases len
  | some p =>
    obtain ⟨h0, w0⟩ := p
    rw [((runOf_origin (good_upto F n)).1 h0 w0 o).1, List.length_cons,
      show (Bound.upto n).horizon = n from rfl] at len
    cases wk : walk x.code.entry F wire (Bound.upto 0) e h0 0 w0 n with
    | none => have := walk_none n wk 0; rw [Nat.add_zero] at this; omega
    | some q =>
      obtain ⟨rfl, same⟩ := Boundary.unique (F := F) ⟨w, rfl, st⟩ ⟨_, rfl, stands ⟨h0, w0, o, wk⟩⟩
      cases same
      exact ⟨h0, w0, o, wk⟩

/-! ## The reachable-boundary invariant -/

/-- **The reachable-boundary invariant**: a boundary is what the run reaches at
a good bound whose horizon is the actions issued: its history, `n + 1` boundary
worlds (counting the one resumed), the last one `t`'s. -/
theorem boundary_iff {t : TypedWorld} : (view F).Boundary x e h n t ↔
    ∃ r, Good (spec F) r ∧ r.horizon = n ∧ ∃ w, t = ⟨x.code, w⟩ ∧
      ((spec F).lang.sem x e r).events = h ∧
      (x.boundaries (runOf F x e r).worlds).length = n + 1 ∧
      (x.boundaries (runOf F x e r).worlds).getLast? = some w := by
  refine ⟨fun ⟨w, eq, stands⟩ => ⟨Bound.upto n, good_upto F n, rfl, w, eq, stands⟩, ?_⟩
  rintro ⟨r, good, rfl, w, eq, stands⟩
  rw [good_eq good] at stands
  exact ⟨w, eq, stands⟩

/-- **A boundary's history is observed.** -/
theorem Boundary.observed {t : TypedWorld} (b : (view F).Boundary x e h n t) :
    Observed (spec F) ((spec F).ofWorld x) e h :=
  let ⟨_, _, stands⟩ := b
  ⟨Bound.upto n, good_upto F n, stands.1 ▸ List.prefix_refl _⟩

/-- **A good bound past a boundary** lists its world at `n` and extends its history. -/
theorem Boundary.reached (b : (view F).Boundary x e h n ⟨x.code, w⟩)
    (good : Good (spec F) r) (le : n ≤ r.horizon) :
    (x.boundaries (runOf F x e r).worlds)[n]? = some w ∧ h <+: ((spec F).lang.sem x e r).events :=
  let ⟨at_n, pfx⟩ := (boundary_mk.1 b).run good le
  ⟨at_n, by rw [sem_eq, pfx]; exact go_extends _ _ _ _⟩

/-- A good bound short of a boundary shows a prefix of its history. -/
theorem Boundary.below {t : TypedWorld} (b : (view F).Boundary x e h n t)
    (good : Good (spec F) r) (le : r.horizon ≤ n) : ((spec F).lang.sem x e r).events <+: h := by
  obtain ⟨_, _, stands⟩ := b
  rw [good_eq good]
  exact stands.1 ▸ (run_mono x.world (upto_le le)).1.1

/-- A next boundary is the world of a listed world. -/
theorem Boundary.listed {t : TypedWorld} (b : (view F).Boundary x e h (n + 1) t)
    (good : Good (spec F) r) (le : n + 1 ≤ r.horizon) :
    ∃ ω ∈ (spec F).worlds x e r, (view F).typed ω = t := by
  obtain ⟨w, rfl, st⟩ := b
  have at_n := (Boundary.reached (F := F) ⟨w, rfl, st⟩ good le).1
  refine ⟨⟨x.code, .boundary w⟩, List.mem_map_of_mem ?_, rfl⟩
  obtain ⟨code, _ | w0⟩ := x
  · exact List.mem_of_getElem? at_n
  · exact List.mem_of_getElem? (l := (runOf F ⟨code, .boundary w0⟩ e r).worlds) (i := n) at_n

/-! ## The one-action decomposition -/

/-- **A completed action leads to the next boundary**: its events and world. -/
theorem Boundary.next (b : (view F).Boundary x e h n ⟨x.code, w⟩)
    (next : e.requests h n = some a) (completes : (act F x e h n w a).stops = false) :
    (view F).Boundary x e (h ++ (act F x e h n w a).events) (n + 1)
      ⟨x.code, (act F x e h n w a).world⟩ := by
  obtain ⟨h0, w0, o, wk⟩ := boundary_mk.1 b
  have := walk_succ (a := a) n wk (by rwa [Nat.zero_add]) (by rwa [Nat.zero_add])
  rw [Nat.zero_add] at this
  exact boundary_mk.2 ⟨h0, w0, o, this⟩

/-- A good bound past a completed action shows its events after the history. -/
theorem Boundary.next_events (b : (view F).Boundary x e h n ⟨x.code, w⟩)
    (next : e.requests h n = some a) (completes : (act F x e h n w a).stops = false)
    (good : Good (spec F) r) (lt : n < r.horizon) :
    h ++ (act F x e h n w a).events <+: ((spec F).lang.sem x e r).events := by
  obtain ⟨_, pfx⟩ := (boundary_mk.1 b).run good (Nat.le_of_lt lt)
  rw [sem_eq, pfx, show r.horizon - n = r.horizon - n - 1 + 1 by omega, go_step next completes]
  exact go_extends _ _ _ _

/-- A good bound extending a boundary shows its history alone or the action's events. -/
theorem Boundary.events_cases (b : (view F).Boundary x e h n ⟨x.code, w⟩)
    (next : e.requests h n = some a) (completes : (act F x e h n w a).stops = false)
    (good : Good (spec F) r) (pre : h <+: ((spec F).lang.sem x e r).events) :
    ((spec F).lang.sem x e r).events = h ∨
      h ++ (act F x e h n w a).events <+: ((spec F).lang.sem x e r).events := by
  by_cases lt : n < r.horizon
  · exact .inr (Boundary.next_events b next completes good lt)
  · have below := Boundary.below b good (by omega)
    exact .inl (below.eq_of_length (Nat.le_antisymm below.length_le pre.length_le))

/-- **An action that exhausts or diverges stops the session.** -/
theorem Boundary.stops (b : (view F).Boundary x e h n ⟨x.code, w⟩)
    (next : e.requests h n = some a) (stops : (act F x e h n w a).stops = true)
    (good : Good (spec F) r) (le : n ≤ r.horizon) : ((spec F).lang.sem x e r).events = h := by
  obtain ⟨_, pfx⟩ := (boundary_mk.1 b).run good le
  rw [sem_eq, pfx]
  cases r.horizon - n with
  | zero => rfl
  | succ k => rw [go_stops next stops]

/-- **The end of the session**: the history is final, with its last outcome. -/
theorem Boundary.idle (b : (view F).Boundary x e h n ⟨x.code, w⟩)
    (idle : e.requests h n = none) (good : Good (spec F) r) (le : n ≤ r.horizon) :
    ((spec F).lang.sem x e r).events = h ∧
      (n < r.horizon → ((spec F).lang.sem x e r).final = lastOutcome h) := by
  obtain ⟨_, pfx⟩ := (boundary_mk.1 b).run good le
  rw [sem_eq, pfx]
  cases eq : r.horizon - n with
  | zero => exact ⟨rfl, fun lt => by omega⟩
  | succ k => rw [go_idle idle]; exact ⟨rfl, fun _ => rfl⟩

/-- **A dropped request**: the next action, with the same history and world. -/
theorem Boundary.dropped {q : Request} (b : (view F).Boundary x e h n ⟨x.code, w⟩)
    (next : e.requests h n = some (.request q))
    (unfunded : ¬ Solidity.Goals.IntrinsicSession.Funded F e h q) :
    (view F).Boundary x e h (n + 1) ⟨x.code, w⟩ := by
  have eq : act F x e h n w (.request q) = { events := [], world := w, frames := [] } := by
    simp only [act, step, request, if_pos (show ¬ Funded F e h q from unfunded)]
  have := Boundary.next b next (by rw [eq])
  rwa [eq, List.append_nil] at this

/-- **A credit** is the next event, and the next boundary is the credited world. -/
theorem Boundary.credited {target : Address} {value : Roadmap.Word}
    (b : (view F).Boundary x e h n ⟨x.code, w⟩)
    (next : e.requests h n = some (.credit target value)) :
    (view F).Boundary x e (h ++ [.credit target value]) (n + 1)
      ⟨x.code, (credit w target value).world⟩ :=
  Boundary.next b next rfl

/-- **An affordable request** that completes shows exactly its transaction. -/
theorem request_events {q : Request} (funded : Solidity.Goals.IntrinsicSession.Funded F e h q)
    (completes : (act F x e h n w (.request q)).stops = false) :
    ∃ out, (act F x e h n w (.request q)).events =
      [Event.tx q.sender q.target q.value q.timestamp q.input out] := by
  revert completes
  simp only [act, step, request, Bool.false_eq_true, if_false,
    if_neg (not_not_intro (show Funded F e h q from funded))]
  repeat' split
  all_goals first | exact fun _ => ⟨_, rfl⟩ | exact fun c => nomatch c

/-- **A completed deployment** is the first boundary: its events, its world. -/
theorem deploy_boundary {code : Code} (completes : (deployed F code e).stops = false) :
    (view F).Boundary (Start.initial code) e (deployed F code e).events 0
      ⟨code, (deployed F code e).world⟩ :=
  boundary_mk.2 ⟨_, _, by simp only [Start.origin, Start.initial, completes,
    Bool.false_eq_true, if_false], rfl⟩

/-- **A deployment that exhausts or diverges** shows nothing and lists no world. -/
theorem deploy_stops {code : Code} (stops : (deployed F code e).stops = true)
    (good : Good (spec F) r) : ((spec F).lang.sem (Start.initial code) e r).events = [] ∧
      (spec F).worlds (Start.initial code) e r = [] := by
  obtain ⟨bnds, pfx⟩ := (runOf_origin (x := Start.initial code) (e := e) good).2
    (by simp only [Start.origin, Start.initial, stops, if_true])
  exact ⟨by rw [sem_eq, pfx], List.map_eq_nil_iff.2 bnds⟩

/-! ## Listed worlds -/

/-- A listed world is the start resumed at its typed world, in the session's code. -/
theorem listed_resume {ω : Start} (mem : ω ∈ (spec F).worlds x e r) :
    ω = (view F).resume ((view F).typed ω) ∧ ((view F).typed ω).code = ((view F).typed x).code := by
  obtain ⟨w, _, rfl⟩ := List.mem_map.1 mem
  exact ⟨rfl, x.typed_code.symm⟩

/-- An index into the boundary worlds at a good bound is a boundary. -/
theorem boundary_of_index {m : Nat}
    (good : Good (spec F) r) (at_m : (x.boundaries (runOf F x e r).worlds)[m]? = some w) :
    ∃ h, (view F).Boundary x e h m ⟨x.code, w⟩ ∧ m ≤ r.horizon := by
  obtain ⟨lt, _⟩ := List.getElem?_eq_some_iff.1 at_m
  cases o : x.origin F e with
  | none => rw [((runOf_origin good).2 o).1] at lt; cases lt
  | some p =>
    obtain ⟨h0, w0⟩ := p
    rw [((runOf_origin good).1 h0 w0 o).1, List.length_cons] at lt
    have le : m ≤ r.horizon := by
      have := go_length (entry := x.code.entry) (F := F) (wire := wire) (r := Bound.upto 0)
        (e := e) r.horizon h0 0 w0
      omega
    cases wk : walk x.code.entry F wire (Bound.upto 0) e h0 0 w0 m with
    | none =>
      have := walk_none m wk (r.horizon - m)
      rw [Nat.add_sub_cancel' le] at this
      omega
    | some q =>
      have b := boundary_mk.2 ⟨h0, w0, o, wk⟩
      have := (Boundary.reached b good le).1
      rw [at_m] at this
      cases this
      exact ⟨_, b, le⟩

/-- **Every listed world at a good bound is a boundary** the prefix has reached. -/
theorem listed_boundary {ω : Start} (good : Good (spec F) r) (mem : ω ∈ (spec F).worlds x e r) :
    ∃ h n, (view F).Boundary x e h n ((view F).typed ω) ∧
      h <+: ((spec F).lang.sem x e r).events := by
  obtain ⟨w, wmem, rfl⟩ := List.mem_map.1 mem
  have : w ∈ x.boundaries (runOf F x e r).worlds := by
    obtain ⟨code, _ | w0⟩ := x
    · exact wmem
    · exact List.mem_cons_of_mem _ wmem
  obtain ⟨m, at_m⟩ := List.mem_iff_getElem?.1 this
  obtain ⟨h, b, le⟩ := boundary_of_index good at_m
  exact ⟨h, m, b, (Boundary.reached b good le).2⟩

end Solidity.Semantics.IntrinsicSession
