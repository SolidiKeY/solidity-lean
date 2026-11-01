import SolidityBridge.ExternalEvm.Assembly.Static

namespace Solidity.Evm.External.Assembly

/-- Finite loop packet/address evidence, indexed by the existing source
loop and its actual nested emitted images. All fields are runtime-checkable. -/
structure LoopSite {whole c b : List Instr} {base cb bb origin : Nat}
    (image : Image whole base) (ci : Image c cb) (bi : Image b bb)
    (frame : EvmYul.EVM.State) where
  here : Fin W
  hb : origin < whole.length + 1
  ha : address whole base ⟨origin, hb⟩ = some here.val
  shape : whole[origin]? = some (.loop c b)
  hn : origin + 1 < whole.length + 1
  fits : here.val + ci.size + bi.size + 72 < W
  next : address whole base ⟨origin + 1, hn⟩ = some (here.val + ci.size + bi.size + 72)
  condStart : cb = here.val + 1
  bodyStart : bb = here.val + ci.size + 37
  condEnd : address c cb ⟨c.length, Nat.lt_succ_self _⟩ = some (here.val + ci.size + 1)
  bodyEnd : address b bb ⟨b.length, Nat.lt_succ_self _⟩ = some (here.val + ci.size + bi.size + 37)
  head : EvmYul.EVM.decode frame.executionEnv.code (.ofNat here.val) = some (.JUMPDEST, none)
  guardHead : EvmYul.EVM.decode frame.executionEnv.code (.ofNat (here.val + ci.size + 1)) = some (.JUMPDEST, none)
  guardZero : EvmYul.EVM.decode frame.executionEnv.code (.ofNat (here.val + ci.size + 2)) = some (.ISZERO, none)
  guardPush : EvmYul.EVM.decode frame.executionEnv.code (.ofNat (here.val + ci.size + 3)) =
    some (.Push .PUSH32, some (.ofNat (here.val + ci.size + bi.size + 72), 32))
  guardJump : EvmYul.EVM.decode frame.executionEnv.code (.ofNat (here.val + ci.size + 36)) = some (.JUMPI, none)
  backHead : EvmYul.EVM.decode frame.executionEnv.code (.ofNat (here.val + ci.size + bi.size + 37)) = some (.JUMPDEST, none)
  backPush : EvmYul.EVM.decode frame.executionEnv.code (.ofNat (here.val + ci.size + bi.size + 38)) =
    some (.Push .PUSH32, some (.ofNat here.val, 32))
  backJump : EvmYul.EVM.decode frame.executionEnv.code (.ofNat (here.val + ci.size + bi.size + 71)) = some (.JUMP, none)

theorem iszero_nonzero (w : Fin W) (hn : w.val ≠ 0) :
    EvmYul.UInt256.isZero (.ofNat w.val) = .ofNat 0 := by
  simp only [EvmYul.UInt256.isZero, EvmYul.UInt256.eq0, condition_beq,
    word_nat _ w.isLt, hn, decide_false]
  rfl

/-- Static loop checks discharge every universal routing premise. -/
theorem LoopSite.layout {whole c b : List Instr} {base cb bb origin : Nat}
    {image : Image whole base} {ci : Image c cb} {bi : Image b bb}
    {frame : EvmYul.EVM.State} (site : LoopSite (origin := origin) image ci bi frame) :
    LoopLayout (origin := origin) image ci bi frame site.here
      ⟨site.here.val + ci.size + bi.size + 72, site.fits⟩ where
  shape := site.shape
  headerBound := site.hb
  exitBound := site.hn
  headerAddress := site.ha
  enter := by
    intro m s he
    have pc := boundary_pc he site.here site.ha
    refine ⟨decode_fetch frame s _ _ he.state pc site.head, ?_⟩
    change some cb = some (s.pc + .ofNat 1).toNat
    rw [pc, word_add, word_nat _ (by have hf := site.fits; omega)]
    exact congrArg some site.condStart
  guard := by
    intro mc s w tail rest he hs hr
    have pc := boundary_pc he ⟨site.here.val + ci.size + 1, by have hf := site.fits; omega⟩ site.condEnd
    refine ⟨decode_fetch frame s _ _ he.state pc site.guardHead, ?_, ?_, ?_⟩
    · apply decode_fetch frame (destState s) _ _ he.state _ site.guardZero
      change s.pc + .ofNat 1 = _
      rw [pc, word_add]
    · apply decode_fetch frame (iszeroState s (.ofNat w.val) rest) _ _ he.state _ site.guardPush
      change (s.pc + .ofNat 1) + .ofNat 1 = _
      rw [pc, word_add, word_add]
    · apply decode_fetch frame (pushState (iszeroState s (.ofNat w.val) rest)
        (.ofNat (site.here.val + ci.size + bi.size + 72))) _ _ he.state _ site.guardJump
      change ((s.pc + .ofNat 1) + .ofNat 1) + .ofNat 33 = _
      rw [pc, word_add, word_add, word_add]
  zeroAddress := by
    intro mc s w tail rest he hs hr hz
    change address whole base ⟨origin + 1, site.hn⟩ = some
      (if EvmYul.UInt256.isZero (.ofNat w.val) != ⟨0⟩ then
        EvmYul.UInt256.ofNat (site.here.val + ci.size + bi.size + 72) else
        (((s.pc + .ofNat 1) + .ofNat 1) + .ofNat 33) + .ofNat 1).toNat
    rw [hz]
    change address whole base ⟨origin + 1, site.hn⟩ = some
      (EvmYul.UInt256.ofNat (site.here.val + ci.size + bi.size + 72)).toNat
    rw [word_nat _ site.fits]
    exact site.next
  nonzeroAddress := by
    intro mc s w tail rest he hs hr hn
    have pc := boundary_pc he ⟨site.here.val + ci.size + 1, by have hf := site.fits; omega⟩ site.condEnd
    change some bb = some
      (if EvmYul.UInt256.isZero (.ofNat w.val) != ⟨0⟩ then
        EvmYul.UInt256.ofNat (site.here.val + ci.size + bi.size + 72) else
        (((s.pc + .ofNat 1) + .ofNat 1) + .ofNat 33) + .ofNat 1).toNat
    rw [iszero_nonzero w hn]
    change some bb = some ((((s.pc + .ofNat 1) + .ofNat 1) + .ofNat 33) + .ofNat 1).toNat
    rw [pc, word_add, word_add, word_add, word_add]
    change some bb = some (EvmYul.UInt256.ofNat (site.here.val + ci.size + 37)).toNat
    rw [word_nat _ (by have hf := site.fits; omega)]
    exact congrArg some site.bodyStart
  back := by
    intro m s he
    have pc := boundary_pc he ⟨site.here.val + ci.size + bi.size + 37, by have hf := site.fits; omega⟩ site.bodyEnd
    refine ⟨decode_fetch frame s _ _ he.state pc site.backHead, ?_, ?_⟩
    · apply decode_fetch frame (destState s) _ _ he.state _ site.backPush
      change s.pc + .ofNat 1 = _
      rw [pc, word_add]
    · apply decode_fetch frame (pushState (destState s) (.ofNat site.here.val)) _ _ he.state _ site.backJump
      change (s.pc + .ofNat 1) + .ofNat 33 = _
      rw [pc, word_add, word_add]

local instance : DecidableEq EvmYul.UInt256
  | ⟨a⟩, ⟨b⟩ => if h : a = b then .isTrue (congrArg EvmYul.UInt256.mk h)
    else .isFalse (fun he => h (congrArg EvmYul.UInt256.val he))

/-- A finite loop checker. Child bases are proved, not trusted offsets. -/
def checkLoop {whole c b : List Instr} {base cb bb origin : Nat}
    (image : Image whole base) (ci : Image c cb) (bi : Image b bb)
    (frame : EvmYul.EVM.State) (shape : whole[origin]? = some (.loop c b)) : Option (LoopSite (origin := origin) image ci bi frame) := do
  let a ← readAddress whole base origin
  if hn : origin + 1 < whole.length + 1 then
    if hpos : a.pc.val + ci.size + bi.size + 72 < W ∧
        address whole base ⟨origin + 1, hn⟩ = some (a.pc.val + ci.size + bi.size + 72) ∧
        cb = a.pc.val + 1 ∧ bb = a.pc.val + ci.size + 37 ∧
        address c cb ⟨c.length, Nat.lt_succ_self _⟩ = some (a.pc.val + ci.size + 1) ∧
        address b bb ⟨b.length, Nat.lt_succ_self _⟩ = some (a.pc.val + ci.size + bi.size + 37) then
      if hd : EvmYul.EVM.decode frame.executionEnv.code (.ofNat a.pc.val) = some (.JUMPDEST, none) then
        if hgh : EvmYul.EVM.decode frame.executionEnv.code (.ofNat (a.pc.val + ci.size + 1)) = some (.JUMPDEST, none) then
          if hgz : EvmYul.EVM.decode frame.executionEnv.code (.ofNat (a.pc.val + ci.size + 2)) = some (.ISZERO, none) then
            if hgp : EvmYul.EVM.decode frame.executionEnv.code (.ofNat (a.pc.val + ci.size + 3)) = some (.Push .PUSH32, some (.ofNat (a.pc.val + ci.size + bi.size + 72), 32)) then
              if hgj : EvmYul.EVM.decode frame.executionEnv.code (.ofNat (a.pc.val + ci.size + 36)) = some (.JUMPI, none) then
                if hbh : EvmYul.EVM.decode frame.executionEnv.code (.ofNat (a.pc.val + ci.size + bi.size + 37)) = some (.JUMPDEST, none) then
                  if hbp : EvmYul.EVM.decode frame.executionEnv.code (.ofNat (a.pc.val + ci.size + bi.size + 38)) = some (.Push .PUSH32, some (.ofNat a.pc.val, 32)) then
                    if hbj : EvmYul.EVM.decode frame.executionEnv.code (.ofNat (a.pc.val + ci.size + bi.size + 71)) = some (.JUMP, none) then
                      return by
                        rcases hpos with ⟨hf, he, hcb, hbb, hce, hbe⟩
                        exact ⟨a.pc, a.bound, a.exactAddress, shape, hn, hf, he, hcb, hbb, hce, hbe,
                          hd, hgh, hgz, hgp, hgj, hbh, hbp, hbj⟩
                    else none
                  else none
                else none
              else none
            else none
          else none
        else none
      else none
    else none
  else none

end Solidity.Evm.External.Assembly
