import Solidity.Theory.Bridge.Denote

/-!
Joint inputs for all eight explicit Bridge/Denote statements. The contract has
real array and primitive roots; pushes and lookups actually succeed. BridgeO
premises use successful SOME inputs, and operator packets include successful
outputs, so conditional bridge premises are not satisfied only by NONE.
-/
namespace H62.AuditTheories
open Solidity
private abbrev BB : Ty := .prim .bool

/-- A concrete contract with declared array and word roots. -/
def bridgeContract : Contract := { vars := [("items", .ref (.array BB)), ("flag", BB)] }
/-- Real storage with an empty live array and a false primitive. -/
def bridgeStorage : Storage bridgeContract :=
  .cons (.array .nil .nil (by decide)) (.cons (.prim false) .nil)
/-- Its declared array root. -/
def bridgeArray : SRef bridgeContract (.ref (.array BB)) := ⟨"items", rfl, .nil⟩
/-- Its declared primitive root. -/
def bridgeFlag : SRef bridgeContract BB := ⟨"flag", rfl, .nil⟩

/-- Actual successful array lookup witnesses the length statement's premise. -/
theorem bridge_obs_len_joint_witness :
    ∃ (C : Contract) (E : Ty) (st : Storage C)
      (r : SRef C (.ref (.array E))) (w : SVal (.ref (.array E))),
      st.find r = some w :=
  ⟨bridgeContract, BB, bridgeStorage, bridgeArray, .array .nil .nil (by decide), rfl⟩

/-- Actual successful word lookup witnesses the primitive statement's premise. -/
theorem bridge_obs_word_joint_witness :
    ∃ (C : Contract) (P : PrimTy) (st : Storage C)
      (r : SRef C (.prim P)) (w : SVal (.prim P)), st.find r = some w :=
  ⟨bridgeContract, .bool, bridgeStorage, bridgeFlag, .prim false, rfl⟩

/-- Push returns real storage, with all callback/source/root inputs correlated. -/
theorem bridge_full_push_joint_witness :
    ∃ (C : Contract) (E : Ty) (st st' : Storage C)
      (r : SRef C (.ref (.array E))) (val : SVal E → Option (SVal E)),
      st.push r val = some st' := by
  refine ⟨bridgeContract, BB, bridgeStorage,
    .cons (.array (.cons (.prim false) .nil) .nil (by decide)) (.cons (.prim false) .nil),
    bridgeArray, some, ?_⟩
  unfold Storage.push
  rw [show bridgeStorage.find bridgeArray =
    some (SVal.array (E := BB) .nil .nil (by decide)) from rfl]
  simp only [Option.bind_eq_bind, Option.bind_some, SVal.view_array]
  simp only [SList.toList_nil, SVec.toList_nil]
  rfl

/-- Push-as-place returns both storage and an in-bounds uint index. -/
theorem bridge_full_pushPlace_joint_witness :
    ∃ (C : Contract) (E : Ty) (st : Storage C)
      (r : SRef C (.ref (.array E))) (q : Storage C × PrimTy.uint.Denote),
      st.pushPlace r = some q := by
  refine ⟨bridgeContract, BB, bridgeStorage, bridgeArray,
    (.cons (.array (.cons (.prim false) .nil) .nil (by decide)) (.cons (.prim false) .nil), uintOfNat 0), ?_⟩
  unfold Storage.pushPlace
  rw [show bridgeStorage.find bridgeArray =
    some (SVal.array (E := BB) .nil .nil (by decide)) from rfl]
  simp only [Option.bind_eq_bind, Option.bind_some, SVal.view_array]
  simp only [SList.toList_nil, SVec.toList_nil]
  rfl

/-- The constant operator has inhabited inputs and an actual successful value. -/
theorem bridge_op0_joint_witness :
    ∃ (C : Contract) (g : State C []) (s : Srt) (o : Op0 C s),
      ∃ v : s.Den C g.H, o.eval g = some v :=
  ⟨bridgeContract, State.init _, .kint, .zlit 7, 7, rfl⟩

/-- Unary bridge inputs coexist with the full BridgeO premise and success. -/
theorem bridge_op1_joint_witness :
    ∃ (C : Contract) (g : State C []) (a s : Srt) (o : Op1 C a s)
      (x : Option (a.Den C g.H)) (d : a.TDen C),
      Srt.BridgeO C g.H a d x ∧ ∃ v : s.Den C g.H, o.eval g x = some v :=
  ⟨bridgeContract, State.init _, .val .uint, .kint, .toInt,
    some (uintOfNat 0), some (uintOfNat 0),
    (by intro v hv; cases hv; rfl), 0, rfl⟩

/-- Both binary bridge premises hold together at two successful integer inputs. -/
theorem bridge_op2_joint_witness :
    ∃ (C : Contract) (g : State C []) (a b s : Srt) (o : Op2 C a b s)
      (x : Option (a.Den C g.H)) (y : Option (b.Den C g.H))
      (da : a.TDen C) (db : b.TDen C),
      Srt.BridgeO C g.H a da x ∧ Srt.BridgeO C g.H b db y ∧
        ∃ v : s.Den C g.H, o.eval g x y = some v :=
  ⟨bridgeContract, State.init _, .kint, .kint, .kint, .zbin .add rfl,
    some 2, some 3, some 2, some 3,
    (by intro v hv; cases hv; rfl), (by intro v hv; cases hv; rfl), 5, rfl⟩

/-- All three ternary bridge premises coexist and the conditional returns true. -/
theorem bridge_op3_joint_witness :
    ∃ (C : Contract) (g : State C []) (a b c s : Srt) (o : Op3 C a b c s)
      (x : Option (a.Den C g.H)) (y : Option (b.Den C g.H)) (z : Option (c.Den C g.H))
      (da : a.TDen C) (db : b.TDen C) (dc : c.TDen C),
      Srt.BridgeO C g.H a da x ∧ Srt.BridgeO C g.H b db y ∧
        Srt.BridgeO C g.H c dc z ∧ ∃ v : s.Den C g.H, o.eval g x y z = some v :=
  ⟨bridgeContract, State.init _, .val .bool, .val .bool, .val .bool, .val .bool, .ite,
    some true, some true, some false, some true, some true, some false,
    (by intro v hv; cases hv; rfl), (by intro v hv; cases hv; rfl),
    (by intro v hv; cases hv; rfl), true, rfl⟩

#check @Solidity.Storage.obs_len_ref_some
#check @Solidity.Storage.obs_word_ref_some
#check @Solidity.Storage.full_of_push
#check @Solidity.Storage.full_of_pushPlace
#check @Solidity.Op0.denote_eval
#check @Solidity.Op1.denote_eval
#check @Solidity.Op2.denote_eval
#check @Solidity.Op3.denote_eval

#print axioms bridge_obs_len_joint_witness
#print axioms bridge_obs_word_joint_witness
#print axioms bridge_full_push_joint_witness
#print axioms bridge_full_pushPlace_joint_witness
#print axioms bridge_op0_joint_witness
#print axioms bridge_op1_joint_witness
#print axioms bridge_op2_joint_witness
#print axioms bridge_op3_joint_witness
end H62.AuditTheories
