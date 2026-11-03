import Solidity.Lowering.V07.WordCasts
import Solidity.Lowering.V07.MixedAssignmentControls

namespace Solidity.Lowering.V07.WordCastControls
open WordCasts Source.SemanticsExamples
open MixedAssignmentControls (C E memory heap path globals storageRef)

def source (t : Source.IntTy) (x y : Int) (hx : t.lo ≤ x ∧ x ≤ t.hi)
    (hy : t.lo ≤ y ∧ y ≤ t.hi) :
    Source.EMState E [.int t,.int t,.bytes .memory,.bytes .storage] :=
  (.cons (.int x hx) (.cons (.int y hy)
    (.cons (.memRef rfl 0) (.cons (.storRef rfl path) .nil))),{s0 with heap := heap})
def target (t : Source.IntTy) (x y : Int) (hx : t.lo ≤ x ∧ x ≤ t.hi)
    (hy : t.lo ≤ y ∧ y ≤ t.hi) :
    State C [.val (integerPrim t),.val (integerPrim t),.mem bytesR,.alias bytesR] :=
  (memory.push (integerValue t y hy)).push (integerValue t x hx)
def si (t : Source.IntTy) (k : Bool) :
    Source.Idx [.int t,.int t,.bytes .memory,.bytes .storage] (.int t) :=
  if k then .here else .there .here
def ti (t : Source.IntTy) (k : Bool) :
    Idx [.val (integerPrim t),.val (integerPrim t),.mem bytesR,.alias bytesR] (.val (integerPrim t)) :=
  if k then .here else .there .here

theorem initial (t : Source.IntTy) (x y : Int) (hx : t.lo ≤ x ∧ x ≤ t.hi)
    (hy : t.lo ≤ y ∧ y ≤ t.hi) :
    IntegerLocalFamily t (si t) (ti t) (source t x y hx hy).1 (target t x y hx hy).env := by
  refine ⟨?_,?_⟩
  · intro k
    cases k <;> exact integer_related t _ _
  · intro k l
    cases k <;> cases l <;> rfl

def umax : Int := Semantics.uintBound-1
def uSource := source .u256 umax 7 (by decide) (by decide)
def uTarget := target .u256 umax 7 (by decide) (by decide)
def sSource := source signed (-1) 7 (by decide) (by decide)
def sTarget := target signed (-1) 7 (by decide) (by decide)

-- Closed clients for every generic headline, with actual mixed-location callers.
def cast_signed_wrap := signed_wrap umax (by decide)
def cast_to_int_eval := to_int_eval umax (by decide)
def cast_to_uint_eval := to_uint_eval (-1) (by decide)
def cast_to_int_run := to_int_run uTarget (.simple (.local .here)) umax (by decide) rfl
def cast_to_uint_run := to_uint_run sTarget (.simple (.local .here)) (-1) (by decide) rfl
def cast_source_to_int (p : Roadmap.Pipeline) (fuel : Nat) :=
  source_to_int (globals p) F0 (fuel+1) uSource uSource (.local .here) umax (by decide) rfl
def cast_source_to_uint (p : Roadmap.Pipeline) (fuel : Nat) :=
  source_to_uint (globals p) F0 (fuel+1) sSource sSource (.local .here) (-1) (by decide) rfl
def cast_assigned_to_int := assigned_to_int_run uTarget (.there .here) .here umax (by decide) rfl
def cast_assigned_to_uint := assigned_to_uint_run sTarget (.there .here) .here (-1) (by decide) rfl
def cast_to_int_transport (p : Roadmap.Pipeline) (fuel : Nat) :=
  assignment_to_int_transport (globals p) F0 fuel uSource uTarget (si .u256) (ti .u256)
    (initial .u256 umax 7 (by decide) (by decide)) false true umax (by decide) rfl
def cast_to_uint_transport (p : Roadmap.Pipeline) (fuel : Nat) :=
  assignment_to_uint_transport (globals p) F0 fuel sSource sTarget (si signed) (ti signed)
    (initial signed (-1) 7 (by decide) (by decide)) false true (-1) (by decide) rfl
def cast_to_int_extension := assigned_to_int_extension uTarget (.there .here) .here umax (by decide) rfl
  (Thin.drop (t := .val .bool) .refl) (true,uTarget.env)
def cast_to_uint_extension := assigned_to_uint_extension sTarget (.there .here) .here (-1) (by decide) rfl
  (Thin.drop (t := .val .bool) .refl) (true,sTarget.env)

-- Same-slot assignments and repeated selected aliases are inhabited.
example (p : Roadmap.Pipeline) (fuel : Nat) :=
  assignment_to_int_transport (globals p) F0 fuel uSource uTarget
    (fun _ : Bool => si .u256 true) (fun _ : Bool => ti .u256 true)
    ((initial .u256 umax 7 (by decide) (by decide)).reindex (fun _ : Bool => true))
    false true umax (by decide) rfl
example (p : Roadmap.Pipeline) (fuel : Nat) :=
  assignment_to_uint_transport (globals p) F0 fuel sSource sTarget
    (fun _ : Bool => si signed true) (fun _ : Bool => ti signed true)
    ((initial signed (-1) 7 (by decide) (by decide)).reindex (fun _ : Bool => true))
    false true (-1) (by decide) rfl

def uOut := uTarget.setLocal (.there .here) (integerValue .u256 umax (by decide))
def sOut := sTarget.setLocal (.there .here) (integerValue signed (-1) (by decide))
-- Exact caller outputs retain heaps/worlds, live refs and the original local type.
example : uOut.heap = uTarget.heap ∧ uOut.glob = uTarget.glob ∧
    TEnv.get (.there (.there .here)) uOut.env = TEnv.get (.there (.there .here)) uTarget.env ∧
    TEnv.get (.there (.there (.there .here))) uOut.env = some storageRef := ⟨rfl,rfl,rfl,rfl⟩
example : sOut.heap = sTarget.heap ∧ sOut.glob = sTarget.glob ∧
    TEnv.get (.there (.there .here)) sOut.env = TEnv.get (.there (.there .here)) sTarget.env ∧
    TEnv.get (.there (.there (.there .here))) sOut.env = some storageRef := ⟨rfl,rfl,rfl,rfl⟩
example : uSource.2.heap.get 0 = some ⟨.bytes .memory,.bytes [0,0]⟩ ∧
    E.pathTy path = some (.bytes .storage) := ⟨rfl,rfl⟩
example : ∃ r : HRef uTarget.H bytesR,
    TEnv.get (.there (.there .here)) uTarget.env = some r ∧ uTarget.heap.len r .dyn = 2 :=
  MixedAssignmentControls.live_memory
example : ∃ r : HRef sTarget.H bytesR,
    TEnv.get (.there (.there .here)) sTarget.env = some r ∧ sTarget.heap.len r .dyn = 2 :=
  MixedAssignmentControls.live_memory

def uExpr : Source.RExpr E [.int .u256,.int .u256,.bytes .memory,.bytes .storage] (.int signed) :=
  .convExplicit (.assign (.local (.there .here)) (.local .here)) (by rfl)
def sExpr : Source.RExpr E [.int signed,.int signed,.bytes .memory,.bytes .storage] (.int .u256) :=
  .convExplicit (.assign (.local (.there .here)) (.local .here)) (by rfl)

def sourcePair (p : Roadmap.Pipeline) : Option (Int × Bool × Bool) :=
  match (Source.evalPair (globals p) F0 8 uExpr (.local (.there .here))).run uSource with
  | (.ok (.val x,.val y),_) => match x.key,y.key with
    | some x,some y => some (x,y==7,y==umax) | _,_ => none
  | _ => none
-- Actual target pipeline prefix captures semantic left/right positions.
def targetPair (p : Roadmap.Pipeline) : Option (Int × Bool × Bool) :=
  match (assignReadPrefix p (.there .here) .here).run uTarget with
  | .ok o =>
    let left : Val C [.val .uint,.val .uint,.val .uint,.val .uint,.mem bytesR,.alias bytesR] .uint :=
      match p with | .legacy => .simple (.local .here) | .viaIR => .simple (.local (.there .here))
    let right : Idx [.val .uint,.val .uint,.val .uint,.val .uint,.mem bytesR,.alias bytesR] (.val .uint) :=
      match p with | .legacy => .there .here | .viaIR => .here
    match (Val.unop .toInt rfl rfl left).evalT o.st with
    | .ok x => some (x.val,(TEnv.get right o.st.env).val==7,(TEnv.get right o.st.env).val==umax)
    | _ => none
  | _ => none
/-- info: [some (-1, true, false), some (-1, false, true), some (-1, true, false), some (-1, false, true)] -/
#guard_msgs in
#eval IO.println (reprStr [sourcePair .legacy,sourcePair .viaIR,targetPair .legacy,targetPair .viaIR])

-- A wrong stale read of the old caller returns7, not the captured assignment's−1.
/-- info: [some 7, some (-1)] -/
#guard_msgs in
#eval IO.println (reprStr [match (Val.unop .toInt rfl rfl (.simple (.local (.there .here))) :
  Val C [.val .uint,.val .uint,.mem bytesR,.alias bytesR] .int).evalT uTarget with
  | .ok x => some x.val | _ => none,
  match (assignedToInt (.there .here) .here).run uTarget with
  | .ok (_, .prim x) => some x.val | _ => none])

-- Four threshold boundaries in each direction, using actual Source and target runs.
def checkU (p : Roadmap.Pipeline) (x expected : Int)
    (hx : Source.IntTy.u256.lo ≤ x ∧ x ≤ Source.IntTy.u256.hi) : Bool :=
  let src := source .u256 x 7 hx (by decide)
  let tgt := target .u256 x 7 hx (by decide)
  let sr := match (Source.evalE (globals p) F0 3
    (.convExplicit (τ := .int signed) (.local .here) (by rfl))).run src with
    | (.ok (.val v),_) => v.key | _ => none
  let tr := match (Val.unop .toInt rfl rfl (.simple (.local .here)) :
    Val C [.val .uint,.val .uint,.mem bytesR,.alias bytesR] .int).evalT tgt with
    | .ok v => some v.val | _ => none
  sr == some expected && tr == some expected

def checkS (p : Roadmap.Pipeline) (x expected : Int)
    (hx : signed.lo ≤ x ∧ x ≤ signed.hi) : Bool :=
  let src := source signed x 7 hx (by decide)
  let tgt := target signed x 7 hx (by decide)
  let sr := match (Source.evalE (globals p) F0 3
    (.convExplicit (τ := .int .u256) (.local .here) (by rfl))).run src with
    | (.ok (.val v),_) => v.key | _ => none
  let tr := match (Val.unop .toUint rfl rfl (.simple (.local .here)) :
    Val C [.val .int,.val .int,.mem bytesR,.alias bytesR] .uint).evalT tgt with
    | .ok v => some v.val | _ => none
  sr == some expected && tr == some expected
/-- info: true -/
#guard_msgs in
#eval IO.println (reprStr ([Roadmap.Pipeline.legacy,.viaIR].all fun p =>
  checkU p 0 0 (by decide) &&
  checkU p (Semantics.intBound-1) (Semantics.intBound-1) (by decide) &&
  checkU p Semantics.intBound (-Semantics.intBound) (by decide) &&
  checkU p umax (-1) (by decide) &&
  checkS p (-Semantics.intBound) Semantics.intBound (by decide) &&
  checkS p (-1) umax (by decide) && checkS p 0 0 (by decide) &&
  checkS p (Semantics.intBound-1) (Semantics.intBound-1) (by decide)))

-- Replacing the actual wrapping cast by a checked numeric admission is false.
example : PrimTy.int.ofInt? umax = none := by decide
example : Source.convExplicitVal (D := E.layout) (.int signed)
    (.int umax (by decide) : Source.Val E.layout (.int .u256)) ≠
      .ok (.int 7 (by decide)) := by
  intro h
  have keys := congrArg (fun r : Source.R (Source.Val E.layout (.int signed)) =>
    r.toOption.bind (fun v => v.key)) h
  change some (-1 : Int) = some 7 at keys
  have impossible := Option.some.inj keys
  omega

end Solidity.Lowering.V07.WordCastControls
