import SolidityBridge.ExternalEvm.Assembly.Structured

/-! Finite, executable decoder certificates. The data below is indexed by
an existing instruction and image; it is proof evidence, not a source IR.
A checker can refuse a malformed encoder/layout instead of assuming it correct.
-/
namespace Solidity.Evm.External.Assembly

theorem word_add (a b : Nat) :
    EvmYul.UInt256.ofNat a + .ofNat b = .ofNat (a + b) := by
  apply congrArg EvmYul.UInt256.mk
  apply Fin.ext
  exact (Nat.add_mod a b W).symm

theorem word_nat (a : Nat) (h : a < W) : (EvmYul.UInt256.ofNat a).toNat = a :=
  Nat.mod_eq_of_lt h

theorem boundary_pc {code : List Instr} {base origin : Nat} {image : Image code base}
    {frame s : EvmYul.EVM.State} {m : Machine} (entry : Boundary image frame origin m s)
    (here : Fin W) (h : address code base ⟨origin, entry.inBounds⟩ = some here.val) :
    s.pc = .ofNat here.val := by
  apply congrArg EvmYul.UInt256.mk
  apply Fin.ext
  change s.pc.toNat = here.val % W
  rw [Nat.mod_eq_of_lt here.isLt]
  exact (Option.some.inj (h.symm.trans entry.pc)).symm

theorem decode_fetch (frame s : EvmYul.EVM.State) (pc : Nat) (packet : Packet)
    (he : s.toState = frame.toState) (hp : s.pc = .ofNat pc)
    (hd : EvmYul.EVM.decode frame.executionEnv.code (.ofNat pc) = some packet) :
    Fetches s packet := by
  have hc : s.executionEnv.code = frame.executionEnv.code :=
    congrArg (fun x : EvmYul.State .EVM => x.executionEnv.code) he
  unfold Fetches EvmYul.EVM.fetchInstr
  rw [hc, hp, hd]
  rfl

/-- Quantifier-free facts checked against the actual ambient bytecode. -/
inductive AtomicSite {code : List Instr} {base : Nat}
    (image : Image code base) (frame : EvmYul.EVM.State) (origin : Nat) : Instr → Type where
  | push (w here : Fin W) (hb : origin < code.length + 1)
      (ha : address code base ⟨origin, hb⟩ = some here.val)
      (hn : origin + 1 < code.length + 1) (fit : here.val + 34 < W)
      (next : address code base ⟨origin + 1, hn⟩ = some (here.val + 34))
      (head : EvmYul.EVM.decode frame.executionEnv.code (.ofNat here.val) = some (.JUMPDEST, none))
      (op : EvmYul.EVM.decode frame.executionEnv.code (.ofNat (here.val + 1)) =
        some (.Push .PUSH32, some (.ofNat w.val, 32))) : AtomicSite image frame origin (.push (.val w))
  | pop (here : Fin W) (hb : origin < code.length + 1)
      (ha : address code base ⟨origin, hb⟩ = some here.val)
      (hn : origin + 1 < code.length + 1) (fit : here.val + 2 < W)
      (next : address code base ⟨origin + 1, hn⟩ = some (here.val + 2))
      (head : EvmYul.EVM.decode frame.executionEnv.code (.ofNat here.val) = some (.JUMPDEST, none))
      (op : EvmYul.EVM.decode frame.executionEnv.code (.ofNat (here.val + 1)) = some (.POP, none)) :
      AtomicSite image frame origin .pop
  | jump (offset : Nat) (here : Fin W) (hb : origin < code.length + 1)
      (ha : address code base ⟨origin, hb⟩ = some here.val) (fit : here.val + 35 < W)
      (target : Relocation code base origin offset)
      (head : EvmYul.EVM.decode frame.executionEnv.code (.ofNat here.val) = some (.JUMPDEST, none))
      (push : EvmYul.EVM.decode frame.executionEnv.code (.ofNat (here.val + 1)) =
        some (.Push .PUSH32, some (.ofNat target.pc.val, 32)))
      (op : EvmYul.EVM.decode frame.executionEnv.code (.ofNat (here.val + 34)) = some (.JUMP, none)) :
      AtomicSite image frame origin (.jump offset)
  | jumpi (offset : Nat) (here : Fin W) (hb : origin < code.length + 1)
      (ha : address code base ⟨origin, hb⟩ = some here.val)
      (hn : origin + 1 < code.length + 1) (fit : here.val + 35 < W)
      (next : address code base ⟨origin + 1, hn⟩ = some (here.val + 35))
      (target : Relocation code base origin offset)
      (head : EvmYul.EVM.decode frame.executionEnv.code (.ofNat here.val) = some (.JUMPDEST, none))
      (push : EvmYul.EVM.decode frame.executionEnv.code (.ofNat (here.val + 1)) =
        some (.Push .PUSH32, some (.ofNat target.pc.val, 32)))
      (op : EvmYul.EVM.decode frame.executionEnv.code (.ofNat (here.val + 34)) = some (.JUMPI, none)) :
      AtomicSite image frame origin (.jumpi offset)

theorem relocation_address {code : List Instr} {base origin offset : Nat}
    (r : Relocation code base origin offset) :
    ∃ h : origin + 1 + offset < code.length + 1,
      address code base ⟨origin + 1 + offset, h⟩ = some r.pc.val := by
  have h : origin + 1 + offset < code.length + 1 := by
    have ht := r.target.isLt
    rw [r.relative] at ht
    exact ht
  refine ⟨h, ?_⟩
  have he : (⟨origin + 1 + offset, h⟩ : Label code) = r.target := Fin.ext r.relative.symm
  rw [he]
  exact r.exactAddress

/-- Eliminate finite certificates into the universal local layout premise. -/
theorem AtomicSite.layout {code : List Instr} {base origin : Nat} {image : Image code base}
    {frame : EvmYul.EVM.State} {i : Instr} (site : AtomicSite image frame origin i)
    (m : Machine) (s : EvmYul.EVM.State) (entry : Boundary image frame origin m s) :
    PrimitiveLayout image origin i s := by
  cases site with
  | push w here hb ha hn fit next hd hp =>
    have pc := boundary_pc entry here ha
    refine ⟨decode_fetch frame s _ _ entry.state pc hd, hn, ?_, ?_⟩
    · change address code base ⟨origin + 1, hn⟩ = some ((s.pc + .ofNat 1) + .ofNat 33).toNat
      rw [pc, word_add, word_add]
      have h : here.val + 1 + 33 = here.val + 34 := by omega
      rw [h, word_nat _ fit]
      exact next
    · apply decode_fetch frame (destState s) _ _ entry.state _ hp
      change s.pc + .ofNat 1 = .ofNat (here.val + 1)
      rw [pc, word_add]
  | pop here hb ha hn fit next hd hp =>
    have pc := boundary_pc entry here ha
    refine ⟨decode_fetch frame s _ _ entry.state pc hd, ?_⟩
    intro c tail hs
    refine ⟨hn, ?_, ?_⟩
    · change address code base ⟨origin + 1, hn⟩ = some ((s.pc + .ofNat 1) + .ofNat 1).toNat
      rw [pc, word_add, word_add]
      have h : here.val + 1 + 1 = here.val + 2 := by omega
      rw [h, word_nat _ fit]
      exact next
    · apply decode_fetch frame (destState s) _ _ entry.state _ hp
      change s.pc + .ofNat 1 = .ofNat (here.val + 1)
      rw [pc, word_add]
  | jump offset here hb ha fit target hd hp hj =>
    have pc := boundary_pc entry here ha
    obtain ⟨bound, addr⟩ := relocation_address target
    refine ⟨decode_fetch frame s _ _ entry.state pc hd, target.pc, bound, addr, ?_, ?_⟩
    · apply decode_fetch frame (destState s) _ _ entry.state _ hp
      change s.pc + .ofNat 1 = .ofNat (here.val + 1)
      rw [pc, word_add]
    · apply decode_fetch frame (pushState (destState s) (.ofNat target.pc.val)) _ _ entry.state _ hj
      change (s.pc + .ofNat 1) + .ofNat 33 = .ofNat (here.val + 34)
      rw [pc, word_add, word_add]
  | jumpi offset here hb ha hn fit next target hd hp hj =>
    have pc := boundary_pc entry here ha
    obtain ⟨bound, addr⟩ := relocation_address target
    refine ⟨decode_fetch frame s _ _ entry.state pc hd, ?_⟩
    intro c tail hs
    refine ⟨target.pc, ?_, ?_, ?_, ?_⟩
    · split <;> assumption
    · by_cases hz : c.toNat = 0
      · simp only [hz, if_true]
        change address code base ⟨origin + 1, _⟩ = some
          (if c != ⟨0⟩ then EvmYul.UInt256.ofNat target.pc.val else
            ((s.pc + .ofNat 1) + .ofNat 33) + .ofNat 1).toNat
        simp only [bne, condition_beq, hz, decide_true, Bool.not_true, Bool.false_eq_true, if_false]
        rw [pc, word_add, word_add, word_add]
        have h : here.val + 1 + 33 + 1 = here.val + 35 := by omega
        rw [h, word_nat _ fit]
        exact next
      · simp only [hz, if_false]
        change address code base ⟨origin + 1 + offset, _⟩ = some
          (if c != ⟨0⟩ then EvmYul.UInt256.ofNat target.pc.val else
            ((s.pc + .ofNat 1) + .ofNat 33) + .ofNat 1).toNat
        simp only [bne, condition_beq, hz, decide_false, Bool.not_false, if_true]
        rw [word_nat _ target.pc.isLt]
        exact addr
    · apply decode_fetch frame (destState s) _ _ entry.state _ hp
      change s.pc + .ofNat 1 = .ofNat (here.val + 1)
      rw [pc, word_add]
    · apply decode_fetch frame (pushState (destState s) (.ofNat target.pc.val)) _ _ entry.state _ hj
      change (s.pc + .ofNat 1) + .ofNat 33 = .ofNat (here.val + 34)
      rw [pc, word_add, word_add]

local instance : DecidableEq EvmYul.UInt256
  | ⟨a⟩, ⟨b⟩ => if h : a = b then .isTrue (congrArg EvmYul.UInt256.mk h)
    else .isFalse (fun he => h (congrArg EvmYul.UInt256.val he))

structure WordAddress (code : List Instr) (base origin : Nat) where
  bound : origin < code.length + 1
  pc : Fin W
  exactAddress : address code base ⟨origin, bound⟩ = some pc.val

def readAddress (code : List Instr) (base origin : Nat) : Option (WordAddress code base origin) := do
  if hb : origin < code.length + 1 then
    match ha : address code base ⟨origin, hb⟩ with
    | none => none
    | some n => if hn : n < W then some ⟨hb, ⟨n, hn⟩, ha⟩ else none
  else none

/-- Check the actual packet and both branch endpoints. No encoder theorem,
execution trace, universally quantified input, or search budget is assumed. -/
def checkAtom {code : List Instr} {base : Nat} (image : Image code base)
    (frame : EvmYul.EVM.State) (origin : Nat) (i : Instr) :
    Option (AtomicSite image frame origin i) := do
  let a ← readAddress code base origin
  if hd : EvmYul.EVM.decode frame.executionEnv.code (.ofNat a.pc.val) = some (.JUMPDEST, none) then
    match i with
    | .push (.val w) =>
      if hn : origin + 1 < code.length + 1 then
        if h : a.pc.val + 34 < W ∧
            address code base ⟨origin + 1, hn⟩ = some (a.pc.val + 34) ∧
            EvmYul.EVM.decode frame.executionEnv.code (.ofNat (a.pc.val + 1)) =
              some (.Push .PUSH32, some (.ofNat w.val, 32)) then
          some (.push w a.pc a.bound a.exactAddress hn h.1 h.2.1 hd h.2.2)
        else none
      else none
    | .pop =>
      if hn : origin + 1 < code.length + 1 then
        if h : a.pc.val + 2 < W ∧
            address code base ⟨origin + 1, hn⟩ = some (a.pc.val + 2) ∧
            EvmYul.EVM.decode frame.executionEnv.code (.ofNat (a.pc.val + 1)) = some (.POP, none) then
          some (.pop a.pc a.bound a.exactAddress hn h.1 h.2.1 hd h.2.2)
        else none
      else none
    | .jump offset =>
      let target ← resolve code base origin offset
      if h : a.pc.val + 35 < W ∧
          EvmYul.EVM.decode frame.executionEnv.code (.ofNat (a.pc.val + 1)) =
            some (.Push .PUSH32, some (.ofNat target.pc.val, 32)) ∧
          EvmYul.EVM.decode frame.executionEnv.code (.ofNat (a.pc.val + 34)) = some (.JUMP, none) then
        some (.jump offset a.pc a.bound a.exactAddress h.1 target hd h.2.1 h.2.2)
      else none
    | .jumpi offset =>
      let target ← resolve code base origin offset
      if hn : origin + 1 < code.length + 1 then
        if h : a.pc.val + 35 < W ∧
            address code base ⟨origin + 1, hn⟩ = some (a.pc.val + 35) ∧
            EvmYul.EVM.decode frame.executionEnv.code (.ofNat (a.pc.val + 1)) =
              some (.Push .PUSH32, some (.ofNat target.pc.val, 32)) ∧
            EvmYul.EVM.decode frame.executionEnv.code (.ofNat (a.pc.val + 34)) = some (.JUMPI, none) then
          some (.jumpi offset a.pc a.bound a.exactAddress hn h.1 h.2.1 target hd h.2.2.1 h.2.2.2)
        else none
      else none
    | _ => none
  else none

/-- Traverse a finite indexed family without erasing its dependent evidence. -/
def collectFin : {n : Nat} → {P : Fin n → Type} →
    ((i : Fin n) → Option (P i)) → Option ((i : Fin n) → P i)
  | 0, _, _ => some (fun i => Fin.elim0 i)
  | n + 1, _, f => do
    let head ← f ⟨0, Nat.zero_lt_succ n⟩
    let tail ← collectFin (fun i : Fin n => f i.succ)
    return fun i => Fin.cases head tail i

/-- Automatically build the existing semantic certificate for non-loop code. -/
def certifyAtoms {code : List Instr} {base : Nat} (image : Image code base)
    (frame : EvmYul.EVM.State) : Option (PLift (DecodedCode frame image)) := do
  let sites ← collectFin (fun k : Fin code.length => checkAtom image frame k.val code[k])
  return ⟨DecodedCode.intro image (fun pre i rest hc => by
    have hb : pre.length < code.length := by
      have h := congrArg List.length hc
      simp only [List.length_append, List.length_cons] at h
      omega
    let k : Fin code.length := ⟨pre.length, hb⟩
    have hi : code[k] = i := by
      have h : code[pre.length]? = some i := by
        rw [hc]
        simp only [List.getElem?_append_right, le_refl, Nat.sub_self, List.getElem?_cons_zero]
      exact Option.some.inj ((List.getElem?_eq_getElem hb).symm.trans h)
    have site := sites k
    rw [hi] at site
    exact DecodedSite.primitive image i (fun m s he => site.layout m s he))⟩

/-- A direct typed empty image avoids normalizing well-founded emitter
proofs while certifying empty condition/body blocks. Its emitted/target
fields still prove equations for the existing assembler. -/
def emptyLayout (base : Fin W) : Image [] base.val where
  bytes := [0x5b]
  size := 0
  span_eq := rfl
  emitted := by rw [emit.eq_def]
  length_eq := rfl
  fits := base.isLt
  destinations := by
    intro l
    have h : l.val = 0 := by have hl := l.isLt; change l.val < 1 at hl; omega
    refine ⟨base.val, ?_, ?_⟩
    · simp only [address, h, List.take_zero, span, Option.map_some, Nat.add_zero]
    · simp only [Nat.sub_self, List.getElem?_cons_zero]
  refs := []
  targets_eq := by rw [targets.eq_def]
  validRefs := by intro n hn; cases hn

def assembleChild (code : List Instr) (base : Nat) : Option (Image code base) :=
  match code with
  | [] => if hb : base < W then some (emptyLayout ⟨base, hb⟩) else none
  | i :: rest => assemble (i :: rest) base

structure CheckedImage (code : List Instr) (base : Nat) (frame : EvmYul.EVM.State) where
  image : Image code base
  placement : Placed image frame
  certificate : DecodedCode frame image

def assembleAtoms (code : List Instr) (base : Nat) (frame : EvmYul.EVM.State) :
    Option (CheckedImage code base frame) := do
  let image ← assemble code base
  if hp : (frame.executionEnv.code.data.toList.drop base).take image.bytes.length = image.bytes then
    let cert ← certifyAtoms image frame
    return ⟨image, hp, cert.down⟩
  else none

theorem CheckedImage.simulation {code : List Instr} {base : Nat} {frame : EvmYul.EVM.State}
    (checked : CheckedImage code base frame) (m m' : Machine) (s : EvmYul.EVM.State)
    (entry : Boundary checked.image frame 0 m s) (source : run code m = .ok m' 0) :
    ∃ n t, fetchedSteps n s = .ok t ∧ Boundary checked.image frame code.length m' t :=
  certified_run_simulation checked.image frame checked.certificate m m' s entry source

end Solidity.Evm.External.Assembly
