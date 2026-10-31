import SolidityBridge.ExternalEvm.Assembly.StaticLoop

namespace Solidity.Evm.External.Assembly

/-- Assemble finite indexed site evidence into the existing source certificate. -/
def certificateOfSites {code : List Instr} {base : Nat} (image : Image code base)
    (frame : EvmYul.EVM.State)
    (sites : (k : Fin code.length) → PLift (DecodedSite frame image k.val code[k])) :
    DecodedCode frame image :=
  .intro image (fun pre i rest hc => by
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
    have site := (sites k).down
    rw [hi] at site
    exact site)

private theorem instruction_size (code : List Instr) (k : Fin code.length) :
    sizeOf code[k] < sizeOf code := List.sizeOf_get code k

mutual
  /-- Automatically certify every source site, including nested loop blocks.
  This is structural recursion over existing source syntax, with no fuel. -/
  def certifyCode {code : List Instr} {base : Nat} (image : Image code base)
      (frame : EvmYul.EVM.State) : Option (PLift (DecodedCode frame image)) := do
    let sites ← collectFin (fun k : Fin code.length =>
      certifySite image frame k.val code[k] (List.getElem?_eq_getElem k.isLt))
    return ⟨certificateOfSites image frame sites⟩
  termination_by sizeOf code
  decreasing_by exact instruction_size _ _

  def certifySite {code : List Instr} {base : Nat} (image : Image code base)
      (frame : EvmYul.EVM.State) (origin : Nat) (i : Instr) :
      (shape : code[origin]? = some i) → Option (PLift (DecodedSite frame image origin i)) :=
    match i with
    | .loop c b => fun shape => do
      let a ← readAddress code base origin
      let ci ← assembleChild c (a.pc.val + 1)
      let bi ← assembleChild b (a.pc.val + ci.size + 37)
      let site ← checkLoop image ci bi frame shape
      let cc ← certifyCode ci frame
      let bc ← certifyCode bi frame
      return ⟨DecodedSite.loop image ci bi site.here
        ⟨site.here.val + ci.size + bi.size + 72, site.fits⟩ site.layout cc.down bc.down⟩
    | i => fun _shape => do
      let site ← checkAtom image frame origin i
      return ⟨DecodedSite.primitive image i (fun m s he => site.layout m s he)⟩
  termination_by sizeOf i
  decreasing_by all_goals simp_wf <;> omega
end

/-- Verified optional assembly: output includes actual placement and a
recursive semantic certificate produced by finite decoder/address checks. -/
def assembleChecked (code : List Instr) (base : Nat) (frame : EvmYul.EVM.State) :
    Option (CheckedImage code base frame) := do
  let image ← assemble code base
  if hp : (frame.executionEnv.code.data.toList.drop base).take image.bytes.length = image.bytes then
    let cert ← certifyCode image frame
    return ⟨image, hp, cert.down⟩
  else none

/-- Every returned checked image simulates successful source executions.
No caller-supplied per-opcode, branch or loop-layout proof is needed. -/
theorem assembleChecked_simulation {code : List Instr} {base : Nat}
    {frame : EvmYul.EVM.State} {checked : CheckedImage code base frame}
    (_assembled : assembleChecked code base frame = some checked)
    (m m' : Machine) (s : EvmYul.EVM.State)
    (entry : Boundary checked.image frame 0 m s) (source : run code m = .ok m' 0) :
    ∃ n t, fetchedSteps n s = .ok t ∧ Boundary checked.image frame code.length m' t :=
  checked.simulation m m' s entry source

end Solidity.Evm.External.Assembly
