import Solidity.Correctness.IntrinsicSession.Laws.Common

/-!
# The intrinsic session: the structural laws

The fields of `Solidity.Goals.IntrinsicSession.Laws F (spec F) (view F)` that do not read a
frame (step `is0p-session-laws`, lane structure): `fixed`, `precompiles`, `this`, `directed`,
`worlds_consistent`, `hashed_consistent`, `slotHashed_sub`, `final_last`, `answered`,
`typed_resume`, `initial_code`, `worlds_code`, `listed_resumes`, `stored_hashed`, one theorem
`Laws.<field>` each, at every bound (resource failures included) where the field asks it.

A run shows only deployments, transactions and credits (`Shown`): a deployment's address, if
any, is `Fixed.createAddress` of the deployer and nonce, and no `call` event occurs, so
`precompiles` and `answered` hold with no call to speak of. A final observation is the last
outcome of the history shown (`runOf_final`).
-/

namespace Solidity.Semantics.IntrinsicSession

open Solidity.Roadmap
open Solidity.Goals.IntrinsicSession (Code TypedWorld Good Moved outcomes)
open Solidity.ContractWorld (World Entry Role)

/-- What a session run shows: a deployment at no address or at `a`, a transaction or a
credit; never a call, a creation, an answer or a callback. -/
private def Shown (a : Address) : Event → Prop
  | .deploy _ _ _ _ x => x = none ∨ x = some a
  | .tx .. => True
  | .credit .. => True
  | _ => False

section Events

variable {contracts : List Contract} {main : Nat} {roles : Fin contracts.length → Role}
  {ctor : (k : Fin contracts.length) → Bytes → Option (Prog contracts[k] [] [])}
  {entry : (k : Fin contracts.length) → Bytes → Option (Entry contracts[k] Bytes)}
  {F : Fixed} {wire : Wire} {r : Bound} {e : SessionEnv} {a : Address}

private theorem step_shown (h : List Event) (n : Nat) (w : World (catalog contracts))
    (act : Action) : ∀ x ∈ (step entry F wire r e h n w act).events, Shown a x := by
  cases act <;> simp only [step, request, credit]
  · repeat' split
    all_goals simp [Shown]
  · simp [Shown]

private theorem deploy_shown : ∀ x ∈ (deploy main roles ctor F wire r e).events,
    Shown (F.createAddress e.deployer e.deployNonce) x := by
  simp only [deploy]
  repeat' split
  all_goals simp [Shown]

/-- A run from a boundary shows its history and what its steps show. -/
private theorem go_shown : ∀ (k : Nat) (h : List Event) (n : Nat) (w : World (catalog contracts)),
    (∀ x ∈ h, Shown a x) → ∀ x ∈ (go entry F wire r e h n w k).pfx.events, Shown a x
  | 0, _, _, _, hist => hist
  | k + 1, h, n, w, hist => by
    simp only [go]
    split
    · exact hist
    · split
      · exact hist
      · exact go_shown k _ _ _ fun x mem => (List.mem_append.1 mem).elim (hist x)
          (step_shown h n w _ x)

/-- A run from a boundary is final only with the last outcome of its history. -/
private theorem go_final : ∀ (k : Nat) (h : List Event) (n : Nat) (w : World (catalog contracts)),
    (go entry F wire r e h n w k).pfx.final = none ∨
      (go entry F wire r e h n w k).pfx.final = lastOutcome (go entry F wire r e h n w k).pfx.events
  | 0, _, _, _ => .inl rfl
  | k + 1, h, n, w => by
    simp only [go]
    split
    · exact .inr rfl
    · split
      · exact .inl rfl
      · exact go_final k _ _ _

end Events

variable {F : Fixed}

/-- **A session run shows only deployments at the computed address, transactions and
credits**, at every bound. -/
private theorem runOf_shown (x : Start) (e : SessionEnv) (r : Bound) :
    ∀ ev ∈ ((spec F).lang.sem x e r).events,
      Shown (F.createAddress e.deployer e.deployNonce) ev := by
  obtain ⟨code, _ | w⟩ := x
  · show ∀ ev ∈ (run code.main code.roles code.ctor code.entry F wire .fresh e r).pfx.events, _
    simp only [run]
    split
    · exact fun _ mem => nomatch mem
    · exact go_shown _ _ _ _ deploy_shown
  · exact go_shown _ _ _ _ fun _ mem => nomatch mem

/-- **A final observation is the last outcome shown**, at every bound. -/
private theorem runOf_final (x : Start) (e : SessionEnv) (r : Bound) :
    ((spec F).lang.sem x e r).final = none ∨
      ((spec F).lang.sem x e r).final = lastOutcome ((spec F).lang.sem x e r).events := by
  obtain ⟨code, _ | w⟩ := x
  · show (run code.main code.roles code.ctor code.entry F wire .fresh e r).pfx.final = none ∨
      (run code.main code.roles code.ctor code.entry F wire .fresh e r).pfx.final = lastOutcome
        (run code.main code.roles code.ctor code.entry F wire .fresh e r).pfx.events
    simp only [run]
    split
    · exact .inl rfl
    · exact go_final _ _ _ _
  · exact go_final _ _ _ _

private theorem lastOutcome_eq (h : List Event) : lastOutcome h = (outcomes h).getLast? :=
  congrArg (fun f => (h.filterMap f).getLast?) (funext fun ev => by cases ev <;> rfl)

/-! ## The laws -/

variable (F)

theorem Laws.fixed : (spec F).fixed = F := rfl

theorem Laws.precompiles : (spec F).lang.PrecompilesFixed :=
  fun p e r _ _ _ _ mem => (runOf_shown p e r _ mem).elim

theorem Laws.this : (spec F).lang.ThisFromDeployment F (spec F).session :=
  fun p e r _ _ _ _ _ mem =>
    (runOf_shown p e r _ mem).elim (fun none => nomatch none) fun some => Option.some.inj some

theorem Laws.directed : ∀ r r', Good (spec F) r → Good (spec F) r' →
    ∃ r'', Good (spec F) r'' ∧ (spec F).lang.resLE.le r r'' ∧ (spec F).lang.resLE.le r' r'' :=
  fun _ _ => good_directed

theorem Laws.worlds_consistent : ∀ p e r r', (spec F).lang.resLE.le r r' →
    (spec F).worlds p e r <+: (spec F).worlds p e r' :=
  fun _ _ _ _ => IntrinsicSession.worlds_consistent

theorem Laws.hashed_consistent : ∀ p e r r', (spec F).lang.resLE.le r r' →
    (spec F).hashed p e r <+: (spec F).hashed p e r' :=
  fun _ _ _ _ => hashed_mono

theorem Laws.slotHashed_sub : ∀ p e r b, b ∈ (spec F).slotHashed p e r →
    b ∈ (spec F).hashed p e r :=
  fun _ _ _ _ => IntrinsicSession.slotHashed_sub

theorem Laws.final_last : ∀ p e r o, ((spec F).lang.sem p e r).final = some o →
    outcomes ((spec F).lang.sem p e r).events = [] ∨
      (outcomes ((spec F).lang.sem p e r).events).getLast? = some o :=
  fun p e r o final => .inr <| by
    rw [← lastOutcome_eq, ← final]
    exact ((runOf_final p e r).resolve_left (by rw [final]; exact fun h => nomatch h)).symm

theorem Laws.answered : ∀ p en r h callee value input static x, (spec F).lang.Allowed en →
    Good (spec F) r →
    h ++ [Event.call callee value input static, x] <+: ((spec F).lang.sem p en r).events →
    Moved (((spec F).session en).callee (h ++ [Event.call callee value input static])) x :=
  fun p en r _ _ _ _ _ _ _ _ pre =>
    (runOf_shown p en r _ (pre.subset (List.mem_append_right _ (List.mem_cons_self ..)))).elim

theorem Laws.typed_resume : ∀ t, (view F).typed ((view F).resume t) = t := Start.typed_resume

theorem Laws.initial_code : ∀ c, ((view F).typed ((view F).initial c)).code = c := fun _ => rfl

theorem Laws.worlds_code : ∀ x e r, ∀ ω ∈ (spec F).worlds ((spec F).ofWorld x) e r,
    ((view F).typed ω).code = ((view F).typed x).code :=
  fun _ _ _ _ mem => (listed_resume mem).2

theorem Laws.listed_resumes : ∀ x e r, ∀ ω ∈ (spec F).worlds ((spec F).ofWorld x) e r,
    let p := (spec F).ofWorld ω
    let p' := (spec F).ofWorld ((view F).resume ((view F).typed ω))
    (spec F).lang.sem p = (spec F).lang.sem p' ∧ (spec F).worlds p = (spec F).worlds p' ∧
      (spec F).hashed p = (spec F).hashed p' ∧ (spec F).slotHashed p = (spec F).slotHashed p' :=
  fun _ _ _ _ mem => (listed_resume mem).1 ▸ ⟨rfl, rfl, rfl, rfl⟩

theorem Laws.stored_hashed : ∀ t e r, ∀ b ∈ (view F).stored t,
    b ∈ (spec F).slotHashed ((spec F).ofWorld ((view F).resume t)) e r :=
  fun t e r _ => stored_resume F t e r

end Solidity.Semantics.IntrinsicSession
