import Solidity.Backend.StorageOps.PrimitiveCycleTransport

/-! Bool/uint/int public-owner controls preserve raw presence, defaulted words,
failed queries and unconstrained raw cells as distinct observations. -/
namespace Solidity.Backend.StorageOps.PrimitiveCycleTransport.Controls
open TypeGraph Solidity.Storage Solidity.Storage.Representation Solidity.Storage.Representation.Graph
private def graph : Schema 0 where
 origin := "v10-primitive-cycle-transport"
 declId := fun i => nomatch i
 declId_injective := by intro i; exact Fin.elim0 i
 name := fun i => nomatch i
 fields := fun i => nomatch i
 rank := fun i => nomatch i
 nonempty := by intro i; exact Fin.elim0 i
 distinct := by intro i; exact Fin.elim0 i
 guarded := by intro i; exact Fin.elim0 i
private def ix (i : Fin 4) : Index := ⟨i.val,by have h:=i.isLt; omega⟩
private def i0 := ix 0
private def i1 := ix 1
private def i2 := ix 2
private def i3 := ix 3
private def ids : List Index := [i2,i1,i0,i3,i1]
private def w0 : Semantics.Word := ⟨0,by decide⟩
private def w1 : Semantics.Word := ⟨1,by decide⟩
private def w2 : Semantics.Word := ⟨2,by decide⟩
private def w87 : Semantics.Word := ⟨87,by decide⟩
private def w99 : Semantics.Word := ⟨99,by decide⟩
private def payload : (p : PrimTy) → p.Denote
 | .bool => true
 | .uint => ⟨53,by decide⟩
 | .int => ⟨-17,by decide⟩
private def encoded (p : PrimTy) : Semantics.Word := PrimTy.toWord (payload p)
private def old (p : PrimTy) : Value graph (.array (.prim p)) :=
 .array ⟨3,by decide⟩ i2 (by decide) (fun _ => .present (.prim (payload p)))
private def middle (p : PrimTy) := (recursivePop (old p)).getD (old p)
private def grown (p : PrimTy) := (operationPush (middle p)).getD (old p)
private def result (p : PrimTy) := (GraphRetainedCycle.execute (old p)).getD (old p)
private def base : Solidity.Storage.Loc := .root 0
private def loc (i : Nat) : Solidity.Storage.Loc := .data base i
private def store (p : PrimTy) : Store := fun l => if l=base then w2 else if l=loc 3 then w99 else encoded p
private def popStore (p : PrimTy) : Store := Representation.write (Representation.write (store p) (loc 1) w0) base w1
private theorem before (p : PrimTy) : Represented (old p) (PrimitivePop.queries ids) base (store p) := by
 intro query member
 simp only [PrimitivePop.queries,ids,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at member
 rcases member with rfl | rfl | rfl | rfl | rfl | rfl
 · refine ⟨True.intro,⟨by change (2:Nat)≤lmax; decide,by change (3:Nat)≤lmax; decide⟩,?_⟩
   intro word found
   change some w2=some word at found
   cases found
   rfl
 · refine ⟨⟨by change i2.val<lmax; decide,True.intro⟩,True.intro,?_⟩
   intro word found
   change some (encoded p)=some word at found
   cases found
   rfl
 · refine ⟨⟨by change i1.val<lmax; decide,True.intro⟩,True.intro,?_⟩
   intro word found
   change some (encoded p)=some word at found
   cases found
   rfl
 · refine ⟨⟨by change i0.val<lmax; decide,True.intro⟩,True.intro,?_⟩
   intro word found
   change some (encoded p)=some word at found
   cases found
   rfl
 · refine ⟨⟨by change i3.val<lmax; decide,True.intro⟩,True.intro,?_⟩
   intro word found
   change none=some word at found
   cases found
 · refine ⟨⟨by change i1.val<lmax; decide,True.intro⟩,True.intro,?_⟩
   intro word found
   change some (encoded p)=some word at found
   cases found
   rfl

/-- All OLD owner premises inhabited for every supported primitive kind. -/
theorem certificate (p : PrimTy) : GraphRetainedCycle.execute (old p)=some (result p) ∧
 Represented (result p) (PrimitivePop.queries ids) base (popStore p) :=
 complete (old p) (middle p) (grown p) (result p) rfl rfl rfl ids base (store p) (before p)

private def view {p : PrimTy} (v : Value graph (.array (.prim p))) :=
 (PrimitivePop.queries ids).map (fun q => q.read v)
private def present {p : PrimTy} (v : Value graph (.array (.prim p))) (i : Index) : Bool :=
 if inside : i.val<v.extent.val then
  match v.slots ⟨i.val,inside⟩ with
  | .absent => false
  | .present _ => true
 else false
private def path (p : PrimTy) (i : Index) : TypeGraph.Path graph (.array (.prim p)) (.prim p) := .cons (.index i) .nil
private def live {p : PrimTy} (v : Value graph (.array (.prim p))) (i : Index) : Option Semantics.Word :=
 ((path p i).readLive Value.dflt v).map (fun value => PrimTy.toWord value.head)

/-- COMPLETE ordered requested queries, raw presence, metadata, retained/live
reads and failed raw-cell distinction; Bool, unsigned53 and signed-17. -/
theorem ordered (p : PrimTy) :
 (view (old p),view (middle p),view (grown p),view (result p),
  present (old p) i1,present (middle p) i1,present (grown p) i1,present (result p) i1,
  present (result p) i2,(old p).extent.val,(middle p).extent.val,(grown p).extent.val,(result p).extent.val,
  live (old p) i1,live (middle p) i1,live (grown p) i1,live (result p) i1,
  live (result p) i0,live (result p) i2,live (result p) i3,
  popStore p (loc 0),popStore p (loc 1),popStore p (loc 2),popStore p (loc 3)) =
 ([some w2,some (encoded p),some (encoded p),some (encoded p),none,some (encoded p)],
  [some w1,some (encoded p),some w0,some (encoded p),none,some w0],
  [some w2,some (encoded p),some w0,some (encoded p),none,some w0],
  [some w1,some (encoded p),some w0,some (encoded p),none,some w0],
  true,true,false,false,true,3,3,3,3,
  some (encoded p),none,some w0,none,some (encoded p),none,none,
  encoded p,w0,encoded p,w99) := by cases p <;> rfl

theorem raw_identity_negative (p : PrimTy) : result p ≠ middle p := by
 intro same
 have impossible := congrArg (fun value => present value i1) same
 change false=true at impossible
 cases impossible

/-- Reusing the OLD selected nonzero owner would be false after the actual cycle. -/
theorem old_owner_negative (p : PrimTy) : ¬ Represented (result p) (PrimitivePop.queries ids) base (store p) := by
 intro alleged
 have member : PrimitivePop.elementQuery (G:=graph) (p:=p) i1 ∈ PrimitivePop.queries ids :=
  List.mem_cons_of_mem _ (List.mem_map.mpr ⟨i1,List.mem_cons_of_mem _ List.mem_cons_self,rfl⟩)
 have read : (PrimitivePop.elementQuery i1).read (result p)=some ClearDemands.zero := by
  rw [element_read (old p) (middle p) (grown p) (result p) rfl rfl rfl i1]
  exact PrimitivePop.last_read (old p) (middle p) rfl i1 rfl
 have cell := (alleged _ member).2.2 _ read
 rw [PrimitivePop.element_location] at cell
 change encoded p=ClearDemands.zero at cell
 have nonzero : encoded p ≠ ClearDemands.zero := by
  intro same
  have integer := congrArg (fun word : Semantics.Word => word.val) same
  cases p with
  | bool => change (1:Int)=0 at integer; omega
  | uint => change (53:Int)=0 at integer; omega
  | int =>
    change (-17+(2:Int)^256)=0 at integer
    have plentyNat : (17:Nat)<2^256 := Nat.lt_of_lt_of_le
      (by decide : (17:Nat)<2^5)
      (Nat.pow_le_pow_right (by decide : 0<2) (by decide : 5≤256))
    have plenty : (17:Int)<2^256 := by
      have casted : ((17:Nat):Int)<((2^256:Nat):Int) := Int.ofNat_lt.mpr plentyNat
      simpa only [Int.natCast_pow] using casted
    omega
 exact nonzero cell

private def hash (key : Solidity.Storage.Pre) : Nat := if key=.data 0 then 4 else 0
private def locations : List Solidity.Storage.Loc := [base,loc 0,loc 1,loc 2,loc 3]
private def preimages : List Solidity.Storage.Pre := [.data 0]
private def numeric (p : PrimTy) : WordStore := fun address =>
 if address=0 then w2 else if address=7 then w99 else encoded p
private def popNumeric (p : PrimTy) : WordStore := writeWord (writeWord (numeric p) 5 w0) 0 w1
private theorem run : FiniteRun 16 4 1 hash preimages locations := by
 constructor
 · intro key; simp only [hash]; split <;> decide
 · decide
 · decide
 · decide
 · intro l member
   simp only [locations,List.mem_cons,List.not_mem_nil,or_false] at member
   rcases member with rfl | rfl | rfl | rfl | rfl <;> simp only [base,loc,Solidity.Storage.Loc.Bounded] <;> decide
 · intro l member
   simp only [locations,List.mem_cons,List.not_mem_nil,or_false] at member
   rcases member with rfl | rfl | rfl | rfl | rfl <;> decide

/-- Boundary only: actual FIRST-pop numeric execution represents the final
query observations. This does not claim an emitted numeric triple or World run. -/
theorem numeric_boundary (p : PrimTy) : FiniteRun 16 4 1 hash preimages locations ∧
 PrimitivePop.execute 16 hash base (numeric p)=some (popNumeric p) ∧
 Transport 16 hash locations (popStore p) (popNumeric p) ∧
 ∀ query ∈ PrimitivePop.queries (G:=graph) (p:=p) ids, ∀ word,
 query.read (result p)=some word → popNumeric p (query.location base |>.word 16 hash)=word := by
 refine ⟨run,rfl,?_,?_⟩
 · intro l member
   simp only [locations,List.mem_cons,List.not_mem_nil,or_false] at member
   rcases member with rfl | rfl | rfl | rfl | rfl <;> rfl
 · have transported : Transport 16 hash locations (popStore p) (popNumeric p) := by
    intro l member
    simp only [locations,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl <;> rfl
   intro query member word observed
   have covered : query.location base ∈ locations := by
    simp only [PrimitivePop.queries,ids,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl
    · change base ∈ locations; decide
    all_goals rw [PrimitivePop.element_location]; decide
   exact (certificate p).2.numeric transported query member covered word observed

private def empty (p : PrimTy) : Value graph (.array (.prim p)) :=
 .array ⟨3,by decide⟩ i0 (by decide) (fun _ => .present (.prim (payload p)))
private def huge : Value graph (.array (.prim .uint)) :=
 .array ⟨2^256,by decide⟩ ⟨2^256-1,by decide⟩ (by decide) (fun _ => .present (.prim ⟨53,by decide⟩))
private def high : Index := ⟨2^256-1,by decide⟩
private def last : Index := ⟨2^256-2,by decide⟩
/-- Full intrinsic word range, outside legacy compatibility: no new lmax source
cap. Positive stored length admits the actual cycle; empty gives Option failure. -/
theorem empty_and_fullword (p : PrimTy) : GraphRetainedCycle.execute (empty p)=none ∧
 (GraphRetainedCycle.execute huge).map (fun v => (PrimitivePop.queries [high,last,i0]).map (fun q => q.read v)) =
 some [some (lengthWord (2^256-2) (by decide)),some ⟨53,by decide⟩,some w0,some ⟨53,by decide⟩] := by
 constructor
 · rfl
 · rw [outcome_queries huge [high,last,i0]]
   rfl

/-- info: 'Solidity.Backend.StorageOps.PrimitiveCycleTransport.Controls.certificate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms certificate
/-- info: 'Solidity.Backend.StorageOps.PrimitiveCycleTransport.Controls.ordered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms ordered
/-- info: 'Solidity.Backend.StorageOps.PrimitiveCycleTransport.Controls.raw_identity_negative' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in #print axioms raw_identity_negative
/-- info: 'Solidity.Backend.StorageOps.PrimitiveCycleTransport.Controls.old_owner_negative' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms old_owner_negative
/-- info: 'Solidity.Backend.StorageOps.PrimitiveCycleTransport.Controls.numeric_boundary' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms numeric_boundary
/-- info: 'Solidity.Backend.StorageOps.PrimitiveCycleTransport.Controls.empty_and_fullword' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms empty_and_fullword
end Solidity.Backend.StorageOps.PrimitiveCycleTransport.Controls
