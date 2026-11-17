import Solidity.Correctness.Panic.Provenance.Updates
import Solidity.Examples.Panic.ProvenanceEval
import Solidity.Semantics.Panic.Run.UpdateProofs

/-!
# Checks: update leaves of panic code provenance

Failing update steps whose solc code is read off the retained failed site
through the leaves of `Correctness/Panic/Provenance/Updates.lean`.
-/

namespace Solidity.Examples.Panic.ProvenanceUpdates
open Solidity.Panic Solidity.Semantics.Panic Solidity.Correctness.Panic
open Solidity.Examples.Panic.ProvenanceEval

variable {C : Contract} {Γ : Ctx}

/-- A failure retained by the first stage of a sequence is the sequence's. -/
theorem site_bind {α β : Type} {r : EvalResult α} {f : α → EvalResult β} {s : Site}
    (h : site? r = some s) : site? (r >>= f) = some s := by
  cases r with
  | ok => cases h
  | error halt => cases halt <;> exact h

theorem site_ok_bind {α β : Type} {a : α} {f : α → EvalResult β} {s : Site}
    (h : site? (f a) = some s) : site? (.ok a >>= f) = some s := h

/-- A coded step that fails at `site` emits that site's code. -/
theorem code_eq {α : Type} (s : Site) {r : EvalResult α} (hr : ErrCoded r)
    (h : site? r = some s) : code? r = some s.code := by
  rw [code_of_site hr, h]
  rfl

def lit1 : Val C Γ .uint := .simple (.lit 1 (by decide))

/-! Compound assignment and increment: checked arithmetic, code 0x11. -/

theorem maxU_add_one :
    site? (evalProducer (.binary .add .uint rfl maxU one)) = some .arithmetic := by
  decide +kernel

theorem zero_sub_one :
    site? (evalProducer (.binary .sub .uint rfl zero (numericOne .uint rfl))) =
      some .arithmetic := by
  decide +kernel

/-- `x += 1;` on a local holding `type(uint256).max`. -/
example (σ : State C Γ) (i : Idx Γ (.val .uint)) (max : TEnv.get i σ.env = maxU) :
    code? (Run.opAssign .add rfl (.local i) lit1 σ) = some 0x11 :=
  code_eq .arithmetic (Run.opAssign_coded .add rfl (.local i) lit1 σ) <| by
    simp only [Run.opAssign, opLocStore, compound, max]
    rw [show value σ lit1 = .ok one from rfl]
    exact site_ok_bind (site_bind maxU_add_one)

/-- `x--;` on a local holding `0`. -/
example (σ : State C Γ) (i : Idx Γ (.val .uint)) (zero : TEnv.get i σ.env = zero) :
    code? (Run.incDec .postDec rfl (.local i) σ) = some 0x11 :=
  code_eq .arithmetic (Run.incDec_coded .postDec rfl (.local i) σ) <| by
    simp only [Run.incDec, opLocBump, bump, IncDec.isIncrement, zero, Bool.false_eq_true, if_false]
    exact site_bind (site_bind zero_sub_one)

/-- `y = x--;` on a local `x` holding `0`. -/
example (σ : State C Γ) (i j : Idx Γ (.val .uint)) (zero : TEnv.get i σ.env = zero) :
    code? (Run.assignIncDec j .postDec rfl (.local i) σ) = some 0x11 :=
  code_eq .arithmetic (Run.assignIncDec_coded j .postDec rfl (.local i) σ) <| by
    simp only [Run.assignIncDec, opLocBump, bump, IncDec.isIncrement, zero, Bool.false_eq_true, if_false]
    exact site_bind (site_bind zero_sub_one)

/-! A right-hand side `1 / 0` fails the statement at the zero-divisor site, code 0x12. -/

/-- `s.x = 1 / 0;` -/
example (σ : State C Γ) (l : Loc C Γ (.prim .uint)) :
    code? (Run.assign l (.val divZero) σ) = some 0x12 :=
  code_eq .zeroDivisor (Run.assign_coded l _ σ) rfl

/-- `x = 1 / 0;` -/
example (σ : State C Γ) (i : Idx Γ (.val .uint)) :
    code? (Run.assignLocal i divZero σ) = some 0x12 :=
  code_eq .zeroDivisor (Run.assignLocal_coded i divZero σ) rfl

/-- `uint x = 1 / 0;` -/
example (σ : State C Γ) : code? (Run.declLocal .uint (some divZero) σ) = some 0x12 :=
  code_eq .zeroDivisor (Run.declLocal_coded .uint _ σ) rfl

/-- `payable(a).transfer(1 / 0);` -/
example (σ : State C Γ) : code? (Run.transfer lit1 divZero σ) = some 0x12 :=
  code_eq .zeroDivisor (Run.transfer_coded lit1 divZero σ) rfl

/-- `ok = payable(a).send(1 / 0);` -/
example (σ : State C Γ) (ok : Idx Γ (.val .bool)) :
    code? (Run.send ok lit1 divZero σ) = some 0x12 :=
  code_eq .zeroDivisor (Run.send_coded ok lit1 divZero σ) rfl

/-- `values.push(1 / 0);`: the receiver is read, then the pushed value fails. -/
example (σ : State C Γ) (b : SPath C Γ (.array (.prim .uint)))
    (ref : SRef C (.ref (.array (.prim .uint)))) (hr : path σ b = .ok ref) :
    code? (Run.push b (some (.val divZero)) σ) = some 0x12 :=
  code_eq .zeroDivisor (Run.push_coded b _ σ) <| by
    simp only [Run.push, hr]
    rfl

/-! Memory writes out of range: the bounds site, code 0x32. -/

/-- `a[i] = v;` with `i` past the end of the memory array `a`. -/
example {E : Ty} (σ : State C Γ) (l : MLoc C Γ E) (r : MSrc C Γ E) (v : MVal σ.H E)
    {R : RefTy} (ref : HRef σ.H R) (array : ArrTy R E) (i : PrimTy.uint.Denote)
    (hv : msource σ r = .ok v) (ha : mloc σ l = .ok (.index ref array i))
    (failed : σ.heap.index ref array i = none) :
    code? (Run.assignMem l r σ) = some 0x32 := by
  have origin := index_origin σ.heap ref array i failed
  refine code_eq .bounds (Run.assignMem_coded l r σ) ?_
  rw [Run.assignMem_target_error l r σ v _ _ hv ha
    (by rw [memoryRead, evalProducer_origin _ _ origin])]
  exact congrArg some (Raised.ofOrigin_site _ _ _)

/-- `delete a[i];` with `i` past the end of the memory array `a`. -/
example (σ : State C Γ) (l : MLoc C Γ (.prim .uint)) {R : RefTy} (ref : HRef σ.H R)
    (array : ArrTy R (.prim .uint)) (i : PrimTy.uint.Denote)
    (ha : mloc σ l = .ok (.index ref array i)) (failed : σ.heap.index ref array i = none) :
    code? (Run.deleteMem (.loc l) σ) = some 0x32 := by
  have origin := index_origin σ.heap ref array i failed
  refine code_eq .bounds (Run.deleteMem_coded (.loc l) σ) ?_
  simp only [Run.deleteMem, ha]
  refine site_ok_bind ?_
  rw [Run.clear_prim_error σ _ _ (by rw [memoryRead, evalProducer_origin _ _ origin])]
  exact congrArg some (Raised.ofOrigin_site _ _ _)

/-! A storage receiver indexed at `1 / 0` fails at the zero-divisor site, code 0x12. -/

section DivIndex
variable {R : RefTy} {V : Ty} (σ : State C Γ) (it : IndexTy R .uint V)
  (b : SPath C Γ (.ref R)) (ref : SRef C (.ref R)) (hr : path σ b = .ok ref)

/-- `b[1 / 0]` in storage. -/
def divLoc : Loc C Γ V := .index it b divZero

include hr in
theorem divLoc_site : site? (loc σ (divLoc it b)) = some .zeroDivisor := by
  simp only [divLoc, loc, hr]
  exact site_ok_bind rfl

include hr in
/-- `delete b[1 / 0];` -/
example : code? (Run.delete (divLoc it b) σ) = some 0x12 :=
  code_eq .zeroDivisor (Run.delete_coded _ σ) (site_bind (divLoc_site σ it b ref hr))

include hr in
/-- `p = b[1 / 0];` for a storage pointer `p`. -/
example {R' : RefTy} (it : IndexTy R .uint (.ref R')) (p : Idx Γ (.alias R')) :
    code? (Run.rebind p (.path (.loc (divLoc it b))) σ) = some 0x12 :=
  code_eq .zeroDivisor (Run.rebind_coded p _ σ)
    (site_bind (site_bind (divLoc_site σ it b ref hr)))

include hr in
/-- `T storage p = b[1 / 0];` -/
example {R' : RefTy} (it : IndexTy R .uint (.ref R')) :
    code? (Run.declStorage R' (some (.path (.loc (divLoc it b)))) σ) = some 0x12 :=
  code_eq .zeroDivisor (Run.declStorage_coded R' _ σ)
    (site_bind (site_bind (divLoc_site σ it b ref hr)))

include hr in
/-- `m = b[1 / 0];` for a memory local `m`: the copy reads the failing receiver. -/
example {R' : RefTy} (it : IndexTy R .uint (.ref R')) (m : Idx Γ (.mem R'))
    (hm : (Ty.ref R').mapFree = true) :
    code? (Run.rebindMem m (.copy (.loc (divLoc it b)) hm) σ) = some 0x12 :=
  code_eq .zeroDivisor (Run.rebindMem_coded m _ σ)
    (site_bind (site_bind (divLoc_site σ it b ref hr)))

include hr in
/-- `T memory m = b[1 / 0];` -/
example {R' : RefTy} (it : IndexTy R .uint (.ref R')) (hm : (Ty.ref R').mapFree = true) :
    code? (Run.declMem R' (some (.copy (.loc (divLoc it b)) hm)) hm σ) = some 0x12 :=
  code_eq .zeroDivisor (Run.declMem_coded R' _ hm σ)
    (site_bind (site_bind (divLoc_site σ it b ref hr)))

include hr in
/-- `b[1 / 0] = m;` from a memory object `m`. -/
example {R' : RefTy} (it : IndexTy R .uint (.ref R')) (m : MPath C Γ (.ref R'))
    (obj : MVal σ.H (.ref R')) (hm : mpath σ m = .ok obj) :
    code? (Run.assignFromMem (divLoc it b) m σ) = some 0x12 :=
  code_eq .zeroDivisor (Run.assignFromMem_coded _ m σ) <| by
    simp only [Run.assignFromMem, hm]
    exact site_ok_bind (site_bind (divLoc_site σ it b ref hr))

include hr in
/-- `y = b[1 / 0].push();` -/
example {p : PrimTy} (it : IndexTy R .uint (.array (.prim p))) (y : Idx Γ (.val p)) :
    code? (Run.assignLocalPush y (.loc (divLoc it b)) σ) = some 0x12 :=
  code_eq .zeroDivisor (Run.assignLocalPush_coded y _ σ)
    (site_bind (site_bind (divLoc_site σ it b ref hr)))

include hr in
/-- `b[1 / 0].push()++;` -/
example {p : PrimTy} (it : IndexTy R .uint (.array (.prim p))) (hp : p.isNumeric = true) :
    code? (Run.pushIncDec .postInc hp (.loc (divLoc it b)) σ) = some 0x12 :=
  code_eq .zeroDivisor (Run.pushIncDec_coded .postInc hp _ σ)
    (site_bind (divLoc_site σ it b ref hr))

include hr in
/-- `b[1 / 0].push() += 1;`: the right-hand side `1` first, then the receiver. -/
example (it : IndexTy R .uint (.array (.prim .uint))) :
    code? (Run.pushOpAssign .add rfl (.loc (divLoc it b)) lit1 σ) = some 0x12 :=
  code_eq .zeroDivisor (Run.pushOpAssign_coded .add rfl _ lit1 σ)
    (site_ok_bind (site_bind (divLoc_site σ it b ref hr)))

end DivIndex

/-- `b[1 / 0] = new uint[](n);`: the array is allocated, then the receiver fails. -/
example {R R' : RefTy} (σ : State C Γ) (it : IndexTy R .uint (.ref R')) (b : SPath C Γ (.ref R))
    (n : Simple C Γ .uint) (h : R'.newArrOk = true) (ref : SRef C (.ref R))
    (hr : path (σ.copyStToMG (newArrT R' (n.evalT σ) h) (RefTy.mapFree_of_newArrOk h)).st b =
      .ok ref) :
    code? (Run.assignNew (.store (divLoc it b)) n h σ) = some 0x12 :=
  code_eq .zeroDivisor (Run.assignNew_coded _ n h σ) (site_bind (divLoc_site _ it b ref hr))

/-! `pop()` on an empty array: the empty-pop site, code 0x31. -/

/-- `values.pop()` on an empty array retains the empty-pop site, hence code 0x31. -/
example {E : Ty} (b : SPath C Γ (.array E)) (σ : State C Γ)
    (ref : SRef C (.ref (.array E))) (hr : path σ b = .ok ref)
    (empty : Solidity.Panic.Origin (.pop σ.storage E.isMapping ref) .emptyPop) :
    code? (Run.pop b σ) = some 0x31 :=
  code_eq .emptyPop (Run.pop_coded b σ) <| by
    rw [Run.pop_origin b σ ref hr empty]
    exact congrArg some (Raised.ofOrigin_site _ _ _)

end Solidity.Examples.Panic.ProvenanceUpdates
