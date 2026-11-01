import SolidityBridge.ExternalEvm.Assembly.Automatic

namespace Solidity.Evm.External.Assembly

def ScannedLabels (code : List Instr) (base : Nat) (destinations : List EvmYul.UInt256) : Prop :=
  ∀ l : Label code, ∃ n, address code base l = some n ∧ .ofNat n ∈ destinations

theorem ScannedLabels.member {code : List Instr} {base : Nat} {destinations : List EvmYul.UInt256}
    (labels : ScannedLabels code base destinations) (l : Label code) (pc : Nat)
    (ha : address code base l = some pc) : EvmYul.UInt256.ofNat pc ∈ destinations := by
  obtain ⟨n, hn, hm⟩ := labels l
  have he : n = pc := Option.some.inj (hn.symm.trans ha)
  exact he ▸ hm

/-- The actual word resolved for any relative branch at this source site
belongs to the certified scanner array. Numeric literal PUSH is not a jump. -/
def TargetsSafe (code : List Instr) (base origin : Nat) (destinations : List EvmYul.UInt256) : Instr → Prop
  | .jump n | .jumpi n => ∀ r : Relocation code base origin n, .ofNat r.pc.val ∈ destinations
  | _ => True

theorem targetsSafeOfLabels {code : List Instr} {base origin : Nat}
    {destinations : List EvmYul.UInt256} (labels : ScannedLabels code base destinations)
    (i : Instr) : TargetsSafe code base origin destinations i := by
  cases i <;> try trivial
  case jump n => intro r; exact labels.member r.target r.pc.val r.exactAddress
  case jumpi n => intro r; exact labels.member r.target r.pc.val r.exactAddress

/-! Scanner safety follows the *same* nested images and packet certificates
that are erased to DecodedCode. It is not inferred only from root refs. -/
mutual
  inductive ScannedCode (frame : EvmYul.EVM.State) (destinations : List EvmYul.UInt256) :
      {code : List Instr} → {base : Nat} → Image code base → Prop where
    | intro {code base} (image : Image code base)
        (labels : ScannedLabels code base destinations)
        (sites : ∀ pre i rest, code = pre ++ i :: rest →
          ScannedSite frame destinations image pre.length i) : ScannedCode frame destinations image
  inductive ScannedSite (frame : EvmYul.EVM.State) (destinations : List EvmYul.UInt256) :
      {code : List Instr} → {base : Nat} → Image code base → Nat → Instr → Prop where
    | atom {code base origin i} (image : Image code base)
        (site : AtomicSite image frame origin i)
        (safe : TargetsSafe code base origin destinations i) : ScannedSite frame destinations image origin i
    | loop {code c b base cb bb origin} (image : Image code base)
        (ci : Image c cb) (bi : Image b bb) (site : LoopSite (origin := origin) image ci bi frame)
        (header : EvmYul.UInt256.ofNat site.here.val ∈ destinations)
        (exit : EvmYul.UInt256.ofNat (site.here.val + ci.size + bi.size + 72) ∈ destinations)
        (cond : ScannedCode frame destinations ci) (body : ScannedCode frame destinations bi) :
        ScannedSite frame destinations image origin (.loop c b)
end

theorem ScannedCode.labels {frame : EvmYul.EVM.State} {destinations : List EvmYul.UInt256}
    {code : List Instr} {base : Nat} {image : Image code base}
    (certificate : ScannedCode frame destinations image) : ScannedLabels code base destinations := by
  cases certificate with
  | intro _ labels _ => exact labels

/-- Erasure retains the exact opcode/routing certificates whose targets
were checked, including all nested source-image boundaries. -/
theorem ScannedCode.decoded {frame : EvmYul.EVM.State} {destinations : List EvmYul.UInt256}
    {code : List Instr} {base : Nat} {image : Image code base}
    (certificate : ScannedCode frame destinations image) : DecodedCode frame image := by
  induction certificate using ScannedCode.rec
    (motive_2 := fun {_ _} image origin i _ => DecodedSite frame image origin i) with
  | intro image _ _ ih => exact DecodedCode.intro image ih
  | atom image site _ => exact DecodedSite.primitive image _ (fun m s he => site.layout m s he)
  | loop image ci bi site _ _ _ _ cond body =>
    exact DecodedSite.loop image ci bi site.here
      ⟨site.here.val + ci.size + bi.size + 72, site.fits⟩ site.layout cond body

local instance : DecidableEq EvmYul.UInt256
  | ⟨a⟩, ⟨b⟩ => if h : a = b then .isTrue (congrArg EvmYul.UInt256.mk h)
    else .isFalse (fun he => h (congrArg EvmYul.UInt256.val he))
local instance : LawfulBEq EvmYul.UInt256 where
  rfl {a} := by cases a with | mk a => change (a == a) = true; exact BEq.rfl
  eq_of_beq {a b} h := by
    cases a with
    | mk a => cases b with
      | mk b => apply congrArg EvmYul.UInt256.mk; change (a == b) = true at h; exact eq_of_beq h

def checkLabels (code : List Instr) (base : Nat) (destinations : List EvmYul.UInt256) :
    Option (PLift (ScannedLabels code base destinations)) :=
  if hl : ∀ l : Label code, (address code base l).any
      (fun n => decide (EvmYul.UInt256.ofNat n ∈ destinations)) = true then
    some ⟨fun l => by
      have hh := hl l
      cases ha : address code base l with
      | none => simp only [ha, Option.any_none, Bool.false_eq_true] at hh
      | some n =>
        refine ⟨n, rfl, ?_⟩
        simpa only [ha, Option.any_some, decide_eq_true_eq] using hh⟩
  else none

def scannedOfSites {code : List Instr} {base : Nat} (image : Image code base)
    (frame : EvmYul.EVM.State) (destinations : List EvmYul.UInt256)
    (labels : ScannedLabels code base destinations)
    (sites : (k : Fin code.length) → PLift (ScannedSite frame destinations image k.val code[k])) :
    ScannedCode frame destinations image :=
  .intro image labels (fun pre i rest hc => by
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

mutual
  def certifyScannedCode {code : List Instr} {base : Nat} (image : Image code base)
      (frame : EvmYul.EVM.State) (destinations : List EvmYul.UInt256) :
      Option (PLift (ScannedCode frame destinations image)) := do
    let labels ← checkLabels code base destinations
    let sites ← collectFin (fun k : Fin code.length => certifyScannedSite image frame destinations
      labels.down k.val code[k] (List.getElem?_eq_getElem k.isLt))
    return ⟨scannedOfSites image frame destinations labels.down sites⟩
  termination_by sizeOf code
  decreasing_by exact List.sizeOf_get _ _

  def certifyScannedSite {code : List Instr} {base : Nat} (image : Image code base)
      (frame : EvmYul.EVM.State) (destinations : List EvmYul.UInt256)
      (labels : ScannedLabels code base destinations) (origin : Nat) (i : Instr) :
      (shape : code[origin]? = some i) → Option (PLift (ScannedSite frame destinations image origin i)) :=
    match i with
    | .loop c b => fun shape => do
      let a ← readAddress code base origin
      let ci ← assembleChild c (a.pc.val + 1)
      let bi ← assembleChild b (a.pc.val + ci.size + 37)
      let site ← checkLoop image ci bi frame shape
      let cond ← certifyScannedCode ci frame destinations
      let body ← certifyScannedCode bi frame destinations
      return ⟨ScannedSite.loop image ci bi site
        (labels.member ⟨origin, site.hb⟩ site.here.val site.ha)
        (labels.member ⟨origin + 1, site.hn⟩ _ site.next) cond.down body.down⟩
    | i => fun _shape => do
      let site ← checkAtom image frame origin i
      return ⟨ScannedSite.atom image site (targetsSafeOfLabels labels i)⟩
  termination_by sizeOf i
  decreasing_by all_goals simp_wf <;> omega
end

end Solidity.Evm.External.Assembly
