import SolidityBridge.ExternalEvm.Assembly.PureFetched

namespace Solidity.Evm.External.Assembly
open EvmYul EvmYul.EVM

/-- Emitted conditional targets are valid even when the condition is zero.
This stronger invariant directly discharges the actual taken-jump check. -/
def JumpSafe (destinations : List UInt256) (packet : Packet) (s : EVM.State) : Prop :=
  match packet.1 with
  | .JUMP | .JUMPI => X.notIn s.stack[0]? destinations.toArray = false
  | _ => True

inductive SafeTrace (destinations : List UInt256) : Nat → EVM.State → EVM.State → Prop where
  | nil (s) : SafeTrace destinations 0 s s
  | cons {n s next out} (packet : Packet)
      (fetch : Fetches s packet) (pure : PurePacket packet) (safe : JumpSafe destinations packet s)
      (head : EVM.step 1 0 none s = .ok next) (tail : SafeTrace destinations n next out) :
      SafeTrace destinations (n + 1) s out

theorem SafeTrace.trans {destinations : List UInt256} {n k : Nat} {s t out : EVM.State}
    (first : SafeTrace destinations n s t) (second : SafeTrace destinations k t out) :
    SafeTrace destinations (n + k) s out := by
  induction first with
  | nil => simpa only [Nat.zero_add] using second
  | cons packet fetch pure safe head _ ih =>
    simpa only [Nat.succ_add] using SafeTrace.cons packet fetch pure safe head (ih second)

theorem SafeTrace.forget {destinations : List UInt256} {n : Nat} {s t : EVM.State}
    (trace : SafeTrace destinations n s t) : fetchedSteps n s = .ok t := by
  induction trace with
  | nil => rfl
  | cons packet fetch pure safe head tail ih =>
    simp only [fetchedSteps, head, bind, Except.bind]
    exact ih

private theorem decode_of_fetch {s : EVM.State} {packet : Packet} (fetch : Fetches s packet) :
    EVM.decode s.executionEnv.code s.pc = some packet := by
  unfold Fetches EVM.fetchInstr at fetch
  cases hd : EVM.decode s.executionEnv.code s.pc with
  | none => rw [hd] at fetch; cases fetch
  | some actual =>
    rw [hd] at fetch
    cases Except.ok.inj fetch
    rfl

theorem SafeTrace.pureFetched {destinations : List UInt256} {n : Nat} {s t : EVM.State}
    (trace : SafeTrace destinations n s t) : PureFetched n s := by
  induction trace with
  | nil => trivial
  | cons packet fetch pure safe head tail ih =>
    rename_i count start next out
    have hd := decode_of_fetch fetch
    have hs : EVM.step 1 0 (some packet) start = .ok next := by
      rw [← fetched_step 0 _ _ fetch]
      exact head
    simp only [PureFetched, hd, hs]
    exact ⟨pure, ih⟩

/-- Every actually reached fetched branch in a certified prefix passes the
original upstream notIn check, independently of gas/resource readiness. -/
theorem SafeTrace.jump_checks {destinations : List UInt256} {n : Nat} {s t : EVM.State}
    (trace : SafeTrace destinations n s t) : ∀ j, j < n → ∀ reached packet,
      fetchedSteps j s = .ok reached → Fetches reached packet → JumpSafe destinations packet reached := by
  induction trace with
  | nil => intro j bound; omega
  | cons expected fetch pure safe head tail ih =>
    intro j bound reached packet prefixRun actualFetch
    cases j with
    | zero =>
      have he : _ = reached := Except.ok.inj prefixRun
      subst reached
      have hp : expected = packet := Except.ok.inj (fetch.symm.trans actualFetch)
      subst packet
      exact safe
    | succ j =>
      simp only [fetchedSteps, head, bind, Except.bind] at prefixRun
      exact ih j (by omega) reached packet prefixRun actualFetch

local instance : LawfulBEq UInt256 where
  rfl {a} := by cases a with | mk a => change (a == a) = true; exact BEq.rfl
  eq_of_beq {a b} h := by
    cases a with
    | mk a => cases b with
      | mk b => apply congrArg UInt256.mk; change (a == b) = true at h; exact eq_of_beq h

theorem notIn_of_member {destinations : List UInt256} {target : UInt256}
    (member : target ∈ destinations) : X.notIn (some target) destinations.toArray = false := by
  have h : destinations.toArray.contains target = true := by simpa only [Array.contains_eq_mem, List.mem_toArray, decide_eq_true_eq] using member
  simp only [X.notIn, X.belongs, h, Bool.not_true]

theorem SafeTrace.dest {destinations : List UInt256} (s : EVM.State)
    (fetch : Fetches s (.JUMPDEST, none)) : SafeTrace destinations 1 s (destState s) :=
  .cons (.JUMPDEST, none) fetch .dest trivial (fetched_dest s fetch) (.nil _)

theorem SafeTrace.push {destinations : List UInt256} (s : EVM.State) (target : UInt256)
    (fetch : Fetches s (.Push .PUSH32, some (target, 32))) :
    SafeTrace destinations 1 s (pushState s target) := by
  refine .cons (.Push .PUSH32, some (target, 32)) fetch (.push target) trivial ?_ (.nil _)
  rw [fetched_step 0 _ _ fetch]
  rfl

theorem SafeTrace.jump {destinations : List UInt256} (s : EVM.State) (target : UInt256)
    (member : target ∈ destinations)
    (push : Fetches s (.Push .PUSH32, some (target, 32)))
    (jump : Fetches (pushState s target) (.JUMP, none)) :
    SafeTrace destinations 2 s (jumpState s target) := by
  apply (SafeTrace.push (destinations := destinations) s target push).trans (k := 1)
  refine .cons (.JUMP, none) jump .jump (notIn_of_member member) ?_ (.nil _)
  rw [fetched_step 0 _ _ jump]
  rfl

theorem SafeTrace.jumpi {destinations : List UInt256} (s : EVM.State) (target c : UInt256)
    (rest : List UInt256) (stack : s.stack = c :: rest) (member : target ∈ destinations)
    (push : Fetches s (.Push .PUSH32, some (target, 32)))
    (jump : Fetches (pushState s target) (.JUMPI, none)) :
    SafeTrace destinations 2 s (jumpiState s target c rest) := by
  apply (SafeTrace.push (destinations := destinations) s target push).trans (k := 1)
  refine .cons (.JUMPI, none) jump .jumpi (notIn_of_member member) ?_ (.nil _)
  rw [fetched_step 0 _ _ jump]
  have he : {s with stack := c :: rest} = s := by rw [← stack]
  rw [← he]
  rfl

end Solidity.Evm.External.Assembly
