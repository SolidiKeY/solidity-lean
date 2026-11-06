import Solidity.Lowering.StorageOps.SourceArrayDeleteTarget
import Solidity.Backend.StorageOps.TargetClearRepresentation

/-! Actual captured Source array deletion composes with PUBLIC represented
storage, per-run numeric transport and existing actual target execution.
Source address/argument lowering and general compiler/world closure remain open. -/
namespace Solidity.Backend.StorageOps.SourceArrayDeleteNumeric
open TypeGraph Solidity.Storage Solidity.Storage.Representation Solidity.Storage.Representation.Graph
open SourceArrayDeleteTarget

theorem complete {n N L R : Nat} {G : Schema n}
    {hash : Solidity.Storage.Pre → Nat} {P : List Solidity.Storage.Pre} {locations : List Solidity.Storage.Loc}
    {E : Source.Env} {Γ : Source.RCtx}
    (run : FiniteRun N L R hash P locations)
    (frame : Source.Fr) (writable : frame.static = false)
    (sourcePath : Source.SPath) (locals : Source.Locals E.layout Γ) (sourceState : Source.St E)
    (typed : E.pathTy sourcePath = some (.array .storage (.int Source.IntTy.u256) none))
    (ordinary : E.transientRoot sourcePath = false)
    (old : Value G (.array (.prim .uint))) (indices : List Index) (base : Solidity.Storage.Loc)
    (baseFits : TargetOperations.KeysFit base) (store : Store) (numeric : WordStore)
    (target : Evm.Machine) (tail : List Evm.Word)
    (readLength : (Source.readLen (E := E) (Γ := Γ) frame sourcePath).run (locals,sourceState) =
      (.ok old.length.val,(locals,sourceState)))
    (before : Represented old (TargetClearRepresentation.oldQueries old indices) base store)
    (initial : Transport N hash locations store numeric)
    (covered : ∀ q ∈ PrimitivePop.queries (G := G) (p := .uint) indices, q.location base ∈ locations)
    (visitedCovered : ∀ j, j < old.length.val → Solidity.Storage.Loc.data base j ∈ locations)
    (fitting : ∀ l ∈ locations, TargetOperations.KeysFit l)
    (targetInitial : ∀ l (member : l ∈ locations), target.store.cells (TargetOperations.toSlot l (fitting l member)) = TargetOperations.encodeWord (store l))
    (sourceOld : ∀ i ∈ indices, old.length.val ≤ i.val →
      wordAt frame sourceState.ex (sourcePath.go (.index i.val)) =
        some (TargetOperations.encodeWord (store (.data base i.val))).val) :
    let sourceResult := (Source.deleteStor (E := E) (Γ := Γ) frame (old.length.val + 2)
      (.array .storage (.int Source.IntTy.u256) none) sourcePath).run (locals,sourceState)
    let targetResult := TargetArrayClear.afterClear target tail (TargetOperations.toSlot base baseFits)
    sourceResult = (.ok (), (locals,{sourceState with ex := sourceState.ex.run (((List.range' 0 old.length.val).map (fun i => SourceScalarDeleteLog.clearOp E frame (sourcePath.go (.index i)))) ++ [SourceScalarDeleteLog.clearOp E frame sourcePath])})) ∧
    Evm.run TargetArrayClear.code {target with stack := .slot (TargetOperations.toSlot base baseFits) :: tail} = .ok targetResult 0 ∧
    Represented old.clear (PrimitivePop.queries indices) base (TargetClearRepresentation.afterStore old base store) ∧
    Transport N hash locations (TargetClearRepresentation.afterStore old base store) (TargetClearRepresentation.execute N hash base numeric) ∧
    (∀ l (member : l ∈ locations), targetResult.store.cells (TargetOperations.toSlot l (fitting l member)) =
      TargetOperations.encodeWord ((TargetClearRepresentation.execute N hash base numeric) (l.word N hash))) ∧
    wordAt frame sourceResult.2.2.ex sourcePath =
      some (TargetOperations.encodeWord ((TargetClearRepresentation.execute N hash base numeric) (base.word N hash))).val ∧
    (∀ i ∈ indices, wordAt frame sourceResult.2.2.ex (sourcePath.go (.index i.val)) =
      some (TargetOperations.encodeWord ((TargetClearRepresentation.execute N hash base numeric) ((Solidity.Storage.Loc.data base i.val).word N hash))).val) ∧
    (∀ q ∈ PrimitivePop.queries (G := G) (p := .uint) indices, ∀ word, q.read old.clear = some word →
      (TargetClearRepresentation.execute N hash base numeric) ((q.location base).word N hash) = word) := by
  dsimp only
  have headerOwner : Represented old [.length .nil] base store := by
    intro q member
    have same := List.mem_singleton.mp member
    subst q
    exact before _ List.mem_cons_self
  have headerCovered : base ∈ locations := covered (.length .nil) List.mem_cons_self
  have targetHeader := TargetHeaderPush.source_header old base baseFits store target headerOwner (targetInitial base headerCovered)
  have certificate := TargetClearRepresentation.complete run old indices base baseFits store numeric target tail
    before initial covered visitedCovered fitting targetInitial
  have elementCovered : ∀ i ∈ indices, Solidity.Storage.Loc.data base i.val ∈ locations := by
    intro i member
    have atQuery := covered (PrimitivePop.elementQuery i) (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨i,member,rfl⟩))
    simpa only [PrimitivePop.element_location] using atQuery
  refine ⟨source_array_run frame writable _ sourcePath old.length.val locals sourceState readLength,
    certificate.1,certificate.2.1,certificate.2.2.1,certificate.2.2.2.1,?_,?_,certificate.2.2.2.2⟩
  · have sourceHeader := source_array_header frame writable sourcePath old.length.val locals sourceState typed ordinary readLength
    have numericHeader := congrArg Fin.val (certificate.2.2.2.1 base headerCovered)
    change (TargetArrayClear.afterClear target tail (TargetOperations.toSlot base baseFits)).store (TargetOperations.toSlot base baseFits) = _ at numericHeader
    rw [← numericHeader,TargetArrayClear.after_header]
    exact sourceHeader
  · intro i member
    have oldWord : old.length.val ≤ i.val → wordAt frame sourceState.ex (sourcePath.go (.index i.val)) =
        some (target.store (.data (TargetOperations.toSlot base baseFits) i.val)) := by
      intro unvisited
      have input := congrArg Fin.val (targetInitial (.data base i.val) (elementCovered i member))
      change target.store (.data (TargetOperations.toSlot base baseFits) i.val) = _ at input
      rw [input]
      exact sourceOld i member unvisited
    have sourceWord := data_correspondence frame writable sourcePath old.length.val i.val locals sourceState
      typed ordinary readLength target tail (TargetOperations.toSlot base baseFits) targetHeader oldWord
    have output := congrArg Fin.val (certificate.2.2.2.1 (.data base i.val) (elementCovered i member))
    change (TargetArrayClear.afterClear target tail (TargetOperations.toSlot base baseFits)).store
      (.data (TargetOperations.toSlot base baseFits) i.val) = _ at output
    rw [← output]
    exact sourceWord

namespace Controls
private def uintSyntax : Source.Syn .typeName := .elem (.int false 256 (by decide))
private def mapSyntax : Source.Syn .typeName :=
  .mapping (.elem (.int false 256 (by decide)) (by decide)) none uintSyntax none
private def unit : Source.Syn .unit := .unit (.cons (.contract false "C" .none .nil
  (.cons (.stateVar (.array mapSyntax .none) none none none false "maps" .none)
    (.cons (.stateVar (.array uintSyntax .none) none none none false "values" .none)
      (.cons (.stateVar uintSyntax none none none false "sentinel" .none)
        (.cons (.stateVar uintSyntax none none none true "scratch" .none) .nil))))) .nil)
private def env : Source.Env := unit.env
private def uint : Source.STy := .int Source.IntTy.u256
private def mapTy : Source.STy := .mapping uint uint
private def ty : Source.STy := .array .storage mapTy none
private def root : Source.SPath := ⟨⟨some "C","maps"⟩,[]⟩
private def scalar : Source.SPath := ⟨⟨some "C","values"⟩,[]⟩
private def sentinel : Source.SPath := ⟨⟨some "C","sentinel"⟩,[]⟩
private def scratch : Source.SPath := ⟨⟨some "C","scratch"⟩,[]⟩
private def key (i : Nat) : Source.SPath := (root.go (.index i)).go (.key (List.replicate 32 0))
private def elem (i : Nat) : Source.SPath := scalar.go (.index i)
private def address : Roadmap.Address := ⟨7,by decide⟩
private def storage : Source.Storage env.layout env.cellTy :=
  let s0 : Source.Storage env.layout env.cellTy := Source.Storage.empty
  let s1 : Source.Storage env.layout env.cellTy := s0.write root (.int 2 (by decide))
  let s2 : Source.Storage env.layout env.cellTy := s1.write (key 0) (.int 7 (by decide))
  let s3 : Source.Storage env.layout env.cellTy := s2.write (key 1) (.int 17 (by decide))
  let s4 : Source.Storage env.layout env.cellTy := s3.write (key 2) (.int 71 (by decide))
  let s5 : Source.Storage env.layout env.cellTy := s4.write sentinel (.int 99 (by decide))
  let s6 : Source.Storage env.layout env.cellTy := s5.write scalar (.int 2 (by decide))
  let s7 : Source.Storage env.layout env.cellTy := s6.write (elem 0) (.int 53 (by decide))
  let s8 : Source.Storage env.layout env.cellTy := s7.write (elem 1) (.int 59 (by decide))
  s8.write (elem 2) (.int 61 (by decide))
private def transientStorage : Source.Storage env.layout env.cellTy :=
  (Source.Storage.empty : Source.Storage env.layout env.cellTy).write scratch (.int 41 (by decide))
private def state : Source.St env :=
  { ex :=
      { world := ⟨fun a => if a = address then
          { balance := ⟨19,by decide⟩, nonce := 3, code := some 0, storage := storage }
          else Source.Account.empty _⟩
        transient := Source.Transient.empty.set address transientStorage
        journal := [] }
    heap := Source.Heap.empty
    events := []
    logs := []
    fnLocals := ⟨[],.nil⟩ }
private def initial : Source.Locals env.layout [] × Source.St env := (.nil,state)
private def frame : Source.Fr :=
  { this := address, sender := ⟨13,by decide⟩, value := ⟨0,by decide⟩,
    static := false, contract := "C" }
private def paths : List Source.SPath := [root,key 0,key 1,key 2,sentinel,scalar,elem 0,elem 1,elem 2]
private def view (s : Source.St env) : List (Option (Source.Val env.layout uint)) :=
  [(s.ex.world.accounts address).storage.read root,
   (s.ex.world.accounts address).storage.read (key 0),
   (s.ex.world.accounts address).storage.read (key 1),
   (s.ex.world.accounts address).storage.read (key 2),
   (s.ex.world.accounts address).storage.read sentinel,
   (s.ex.world.accounts address).storage.read scalar,
   (s.ex.world.accounts address).storage.read (elem 0),
   (s.ex.world.accounts address).storage.read (elem 1),
   (s.ex.world.accounts address).storage.read (elem 2),
   (s.ex.transient.cells address).read scratch]
private def value (i : Int) (h : Source.IntTy.u256.lo ≤ i ∧ i ≤ Source.IntTy.u256.hi) : Source.Val env.layout uint := .int i h
private def prior := (Source.setCell (E := env) (Γ := []) frame sentinel (some (.int 101 (by decide)))).run initial
private def graph : Schema 0 where
  origin := "v10-source-array-delete-numeric"
  declId := fun i => nomatch i
  declId_injective := by intro i; exact Fin.elim0 i
  name := fun i => nomatch i
  fields := fun i => nomatch i
  rank := fun i => nomatch i
  nonempty := by intro i; exact Fin.elim0 i
  distinct := by intro i; exact Fin.elim0 i
  guarded := by intro i; exact Fin.elim0 i
private def ix (i : Fin 4) : Index := ⟨i.val,by have bound := i.isLt; omega⟩
private def indices : List Index := [ix 2,ix 0,ix 1,ix 2]
private def w0 : Semantics.Word := ⟨0,by decide⟩
private def w2 : Semantics.Word := ⟨2,by decide⟩
private def w3 : Semantics.Word := ⟨3,by decide⟩
private def w53 : Semantics.Word := ⟨53,by decide⟩
private def w59 : Semantics.Word := ⟨59,by decide⟩
private def w61 : Semantics.Word := ⟨61,by decide⟩
private def w93 : Semantics.Word := ⟨93,by decide⟩
private def w101 : Semantics.Word := ⟨101,by decide⟩
private def w87 : Semantics.Word := ⟨87,by decide⟩
private def old : Value graph (.array (.prim .uint)) :=
  .array ⟨3,by decide⟩ ⟨2,by decide⟩ (by decide)
    (fun i => .present (.prim (if i.val = 0 then w53 else if i.val = 1 then w59 else w61)))
private def base : Solidity.Storage.Loc := .root 0
private def hash (p : Solidity.Storage.Pre) : Nat := if p = .data 0 then 4 else 0
private def preimages : List Solidity.Storage.Pre := [.data 0]
private def locations : List Solidity.Storage.Loc := [base,.data base 0,.data base 1,.data base 2]
private def store : Store := fun l =>
  if l = base then w2 else if l = .data base 0 then w53 else if l = .data base 1 then w59 else
  if l = .data base 2 then w61 else if l = .data base 3 then w93 else
  if l = .root 2 then w101 else if l = .root 11 then w87 else w0
private def numeric : WordStore := fun a =>
  if a = 0 then w2 else if a = 4 then w53 else if a = 5 then w59 else if a = 6 then w61 else
  if a = 7 then w93 else if a = 2 then w101 else if a = 11 then w87 else w0
private def targetStore : Evm.WordStore := .ofFn fun s =>
  if s = .root 0 then 2 else if s = .data (.root 0) 0 then 53 else if s = .data (.root 0) 1 then 59 else
  if s = .data (.root 0) 2 then 61 else if s = .data (.root 0) 3 then 93 else
  if s = .root 2 then 101 else if s = .root 11 then 87 else 0
private def tail : List Evm.Word := [.val ⟨23,by decide⟩,.slot (.root 2)]
private def targetAddress : Fin Evm.W := Source.toWord address.val
private def targetCaller : Fin Evm.W := Source.toWord frame.sender.val
private def target : Evm.Machine :=
  { stack := tail,store := targetStore,mem := fun _ => .val ⟨31,by decide⟩,
    bal := fun a => if a = targetAddress then 19 else 0,
    bal₀ := fun a => if a = targetAddress then 19 else 0,
    self := targetAddress,caller := targetCaller,callvalue := frame.value,
    timestamp := ⟨53,by decide⟩,accepts := fun _ _ => false }
private def sourceRun := (Source.deleteStor (E := env) (Γ := []) frame 4 (.array .storage uint none) scalar).run prior.2
private def targetOut := TargetArrayClear.afterClear target tail (.root 0)
private def numericOut := TargetClearRepresentation.execute 16 hash base numeric
private def storeOut := TargetClearRepresentation.afterStore old base store

private theorem run : FiniteRun 16 4 1 hash preimages locations := by
  constructor
  · intro p; simp only [hash]; split <;> decide
  · decide
  · decide
  · decide
  · intro l member
    simp only [locations,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl | rfl <;> simp only [base,Solidity.Storage.Loc.Bounded] <;> decide
  · intro l member
    simp only [locations,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl | rfl <;> decide
private theorem initialTransport : Transport 16 hash locations store numeric := by
  intro l member
  simp only [locations,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl <;> rfl
private theorem fullBefore : Represented old (PrimitivePop.queries indices) base store := by
  intro q member
  simp only [PrimitivePop.queries,indices,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · refine ⟨True.intro,⟨by decide,by decide⟩,?_⟩
    intro word observed
    change some w2 = some word at observed
    cases observed
    rfl
  · refine ⟨⟨by change 2 < lmax; decide,True.intro⟩,True.intro,?_⟩
    intro word observed
    change some w61 = some word at observed
    cases observed
    rw [PrimitivePop.element_location]
    rfl
  · refine ⟨⟨by change 0 < lmax; decide,True.intro⟩,True.intro,?_⟩
    intro word observed
    change some w53 = some word at observed
    cases observed
    rw [PrimitivePop.element_location]
    rfl
  · refine ⟨⟨by change 1 < lmax; decide,True.intro⟩,True.intro,?_⟩
    intro word observed
    change some w59 = some word at observed
    cases observed
    rw [PrimitivePop.element_location]
    rfl
  · refine ⟨⟨by change 2 < lmax; decide,True.intro⟩,True.intro,?_⟩
    intro word observed
    change some w61 = some word at observed
    cases observed
    rw [PrimitivePop.element_location]
    rfl
private theorem before : Represented old (TargetClearRepresentation.oldQueries old indices) base store := by
  intro q member
  apply fullBefore q
  simp only [TargetClearRepresentation.oldQueries,PrimitivePop.queries,List.mem_cons,List.mem_map] at member
  rcases member with rfl | ⟨i,inside,rfl⟩
  · exact List.mem_cons_self
  · exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨i,(List.mem_filter.mp inside).1,rfl⟩)
private theorem covered : ∀ q ∈ PrimitivePop.queries (G := graph) (p := .uint) indices, q.location base ∈ locations := by
  intro q member
  simp only [PrimitivePop.queries,indices,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact List.mem_cons_self
  · rw [PrimitivePop.element_location]; decide
  · rw [PrimitivePop.element_location]; decide
  · rw [PrimitivePop.element_location]; decide
  · rw [PrimitivePop.element_location]; decide
private theorem visitedCovered : ∀ j, j < old.length.val → Solidity.Storage.Loc.data base j ∈ locations := by
  intro j live
  change j < 2 at live
  have cases : j = 0 ∨ j = 1 := by omega
  rcases cases with rfl | rfl <;> decide
private theorem fitting : ∀ l ∈ locations, TargetOperations.KeysFit l := by
  intro l member
  simp only [locations,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl <;> trivial
private theorem targetInitial : ∀ l (member : l ∈ locations), target.store.cells (TargetOperations.toSlot l (fitting l member)) = TargetOperations.encodeWord (store l) := by
  intro l member
  simp only [locations,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl <;> rfl
private theorem sourceOld : ∀ i ∈ indices, old.length.val ≤ i.val →
    wordAt frame prior.2.2.ex (scalar.go (.index i.val)) = some (TargetOperations.encodeWord (store (.data base i.val))).val := by
  intro i member unvisited
  simp only [indices,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · rfl
  · change 2 ≤ 0 at unvisited; omega
  · change 2 ≤ 1 at unvisited; omega
  · rfl

/-- Every premise is inhabited by actual Source input, existing graph owner,
actual target cells and a checked per-run numeric region. -/
theorem numeric_bridge :
    sourceRun = (.ok (), (prior.2.1,{prior.2.2 with ex := prior.2.2.ex.run [SourceScalarDeleteLog.clearOp env frame (elem 0),SourceScalarDeleteLog.clearOp env frame (elem 1),SourceScalarDeleteLog.clearOp env frame scalar]})) ∧
    Evm.run TargetArrayClear.code {target with stack := .slot (.root 0) :: tail} = .ok targetOut 0 ∧
    Represented old.clear (PrimitivePop.queries indices) base storeOut ∧
    Transport 16 hash locations storeOut numericOut ∧
    (∀ l (member : l ∈ locations), targetOut.store.cells (TargetOperations.toSlot l (fitting l member)) = TargetOperations.encodeWord (numericOut (l.word 16 hash))) ∧
    wordAt frame sourceRun.2.2.ex scalar = some (TargetOperations.encodeWord (numericOut (base.word 16 hash))).val ∧
    (∀ i ∈ indices, wordAt frame sourceRun.2.2.ex (scalar.go (.index i.val)) = some (TargetOperations.encodeWord (numericOut ((Solidity.Storage.Loc.data base i.val).word 16 hash))).val) ∧
    (∀ q ∈ PrimitivePop.queries (G := graph) (p := .uint) indices, ∀ word, q.read old.clear = some word → numericOut ((q.location base).word 16 hash) = word) :=
  complete run frame (by rfl) scalar prior.2.1 prior.2.2 (by rfl) (by rfl) old indices base True.intro
    store numeric target tail (by rfl) before initialTransport covered visitedCovered fitting targetInitial sourceOld
private def path (i : Index) : TypeGraph.Path graph (.array (.prim .uint)) (.prim .uint) := .cons (.index i) .nil
private def graphView (v : Value graph (.array (.prim .uint))) :=
  (v.length.val,v.extent.val,(PrimitivePop.elementQuery (ix 0)).read v,
    (PrimitivePop.elementQuery (ix 1)).read v,(PrimitivePop.elementQuery (ix 2)).read v,
    (PrimitivePop.elementQuery (ix 3)).read v,
    ((path (ix 0)).readLive Value.dflt v).map Value.head,
    ((path (ix 2)).readLive Value.dflt v).map Value.head)
private def numericView (m : WordStore) := (m 0,m 4,m 5,m 6,m 7,m 2,m 11)
private def storeView (w : Store) := (w base,w (.data base 0),w (.data base 1),w (.data base 2),w (.data base 3),w (.root 2),w (.root 11))
private def targetView (m : Evm.Machine) := [m.store (.root 0),m.store (.data (.root 0) 0),m.store (.data (.root 0) 1),
  m.store (.data (.root 0) 2),m.store (.data (.root 0) 3),m.store (.root 2),m.store (.root 11)]
private def wordView (s : Source.St env) :=
  [wordAt frame s.ex root,wordAt frame s.ex (key 0),wordAt frame s.ex (key 1),wordAt frame s.ex (key 2),
   wordAt frame s.ex sentinel,wordAt frame s.ex scalar,wordAt frame s.ex (elem 0),
   wordAt frame s.ex (elem 1),wordAt frame s.ex (elem 2),
   (((s.ex.transient.cells address).read scratch).bind Source.Val.word).map Fin.val]
private def sourceContext (s : Source.St env) :=
  (s.heap.next,s.events.length,s.logs.length,(s.ex.world.accounts address).balance,
    (s.ex.world.accounts address).nonce,(s.ex.world.accounts address).code)
private def targetContext (m : Evm.Machine) :=
  (m.stack,m.mem 0,m.bal targetAddress,m.bal₀ targetAddress,m.self,m.caller,m.callvalue,m.timestamp,
    m.accepts targetAddress ⟨0,by decide⟩)

/-- Complete ordered Source, independent graph, PUBLIC symbolic/numeric and
actual target observations, including retained versus live and raw garbage. -/
theorem ordered :
    (wordView prior.2.2,wordView sourceRun.2.2,sourceRun.2.2.ex.journal.length,
      graphView old,graphView old.clear,storeView store,storeView storeOut,
      numericView numeric,numericView numericOut,targetView target,targetView targetOut,
      sourceContext sourceRun.2.2,targetContext targetOut) =
    ([some 2,some 7,some 17,some 71,some 101,some 2,some 53,some 59,some 61,some 41],
     [some 2,some 7,some 17,some 71,some 101,some 0,some 0,some 0,some 61,some 41],4,
     (2,3,some w53,some w59,some w61,none,some w53,none),
     (0,3,some w0,some w0,some w61,none,none,none),
     (w2,w53,w59,w61,w93,w101,w87),(w0,w0,w0,w61,w93,w101,w87),
     (w2,w53,w59,w61,w93,w101,w87),(w0,w0,w0,w61,w93,w101,w87),
     [2,53,59,61,93,101,87],[0,0,0,61,93,101,87],sourceContext prior.2.2,targetContext target) := by
  rfl

/-- Raw words outside this actual write sequence are preserved by address
separation, not by interpreting a failed graph query as zero or a frame. -/
theorem physical_frames : numericOut 7 = numeric 7 ∧ numericOut 2 = numeric 2 ∧ numericOut 11 = numeric 11 := by
  have outside (a : Nat) (rootApart : a ≠ 0) (firstApart : a ≠ 4) (secondApart : a ≠ 5) : numericOut a = numeric a := by
    apply TargetClearRepresentation.numeric_outside 16 hash numeric base a
    · exact rootApart
    · intro j inside
      change j < 2 at inside
      have cases : j = 0 ∨ j = 1 := by omega
      rcases cases with rfl | rfl
      · exact firstApart
      · exact secondApart
  exact ⟨outside 7 (by decide) (by decide) (by decide),
    outside 2 (by decide) (by decide) (by decide),outside 11 (by decide) (by decide) (by decide)⟩

private def wrongNumeric := TargetClearRepresentation.execute 16 hash base (writeWord numeric 0 w3)

/-- Actual numeric execution with wrong initial header3 erases the old shadow.
The old Source/owner input length is2; initial transport cannot be discarded. -/
theorem wrong_header :
    numericView wrongNumeric = (w0,w0,w0,w0,w93,w101,w87) ∧
    wordAt frame sourceRun.2.2.ex (elem 2) ≠ some (TargetOperations.encodeWord (wrongNumeric 6)).val := by
  refine ⟨rfl,?_⟩
  change some 61 ≠ some (0 : Nat)
  decide

/-- The approved per-run region conditions actually rule out colliding roots
and generated words; no global hash-injectivity premise is substituted. -/
theorem collision_control : ¬ FiniteRun 16 4 1 (fun _ => 0) preimages locations := by
  intro bad
  have same := bad.word_inj (a := base) (b := .data base 0) (by decide) (by decide) rfl
  cases same

theorem failed_query_boundary :
    ((PrimitivePop.elementQuery (ix 3)).read old.clear,wordAt frame sourceRun.2.2.ex (elem 3),
      numericOut 7,targetOut.store (.data (.root 0) 3)) = (none,some 0,w93,93) ∧
    wordAt frame sourceRun.2.2.ex (elem 3) ≠ some (TargetOperations.encodeWord (numericOut 7)).val := by
  refine ⟨rfl,?_⟩
  change some 0 ≠ some (93 : Nat)
  decide

theorem source_restore :
    (sourceRun.2.1,{sourceRun.2.2 with ex :=
      (prior.2.2.ex.enter frame.this frame.sender frame.value [1,2,3] frame.static).rollback sourceRun.2.2.ex}) = prior.2 :=
  source_array_restore frame (by rfl) Source.IntTy.u256 scalar 2 prior.2.1 prior.2.2 [1,2,3] (by rfl)
private def sourceTwice := (Source.deleteStor (E := env) (Γ := []) frame 2 (.array .storage uint none) scalar).run sourceRun.2
private def targetTwice := TargetArrayClear.afterClear targetOut tail (.root 0)
private def numericTwice := TargetClearRepresentation.execute 16 hash base numericOut
private def storeTwice := TargetClearRepresentation.afterStore old.clear base storeOut

/-- The second actual operation consumes the FIRST checked postowner and
transport as its new OLD state; no desired second postowner is assumed. -/
theorem repeated_delete_bridge :
    sourceTwice = (.ok (), (sourceRun.2.1,{sourceRun.2.2 with ex := sourceRun.2.2.ex.run [SourceScalarDeleteLog.clearOp env frame scalar]})) ∧
    Evm.run TargetArrayClear.code {targetOut with stack := .slot (.root 0) :: tail} = .ok targetTwice 0 ∧
    Represented old.clear.clear (PrimitivePop.queries indices) base storeTwice ∧
    Transport 16 hash locations storeTwice numericTwice ∧
    (∀ l (member : l ∈ locations), targetTwice.store.cells (TargetOperations.toSlot l (fitting l member)) = TargetOperations.encodeWord (numericTwice (l.word 16 hash))) ∧
    wordAt frame sourceTwice.2.2.ex scalar = some (TargetOperations.encodeWord (numericTwice (base.word 16 hash))).val ∧
    (∀ i ∈ indices, wordAt frame sourceTwice.2.2.ex (scalar.go (.index i.val)) = some (TargetOperations.encodeWord (numericTwice ((Solidity.Storage.Loc.data base i.val).word 16 hash))).val) ∧
    (∀ q ∈ PrimitivePop.queries (G := graph) (p := .uint) indices, ∀ word, q.read old.clear.clear = some word → numericTwice ((q.location base).word 16 hash) = word) := by
  have nextBefore : Represented old.clear (TargetClearRepresentation.oldQueries old.clear indices) base storeOut := by
    intro q member
    apply numeric_bridge.2.2.1 q
    simp only [TargetClearRepresentation.oldQueries,PrimitivePop.queries,List.mem_cons,List.mem_map] at member
    rcases member with rfl | ⟨i,inside,rfl⟩
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨i,(List.mem_filter.mp inside).1,rfl⟩)
  have elementCovered : ∀ i ∈ indices, Solidity.Storage.Loc.data base i.val ∈ locations := by
    intro i member
    have atQuery := covered (PrimitivePop.elementQuery i) (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨i,member,rfl⟩))
    simpa only [PrimitivePop.element_location] using atQuery
  have nextTarget : ∀ l (member : l ∈ locations), targetOut.store.cells (TargetOperations.toSlot l (fitting l member)) = TargetOperations.encodeWord (storeOut l) := by
    intro l member
    exact (numeric_bridge.2.2.2.2.1 l member).trans
      (congrArg TargetOperations.encodeWord (numeric_bridge.2.2.2.1 l member))
  have nextSource : ∀ i ∈ indices, old.clear.length.val ≤ i.val →
      wordAt frame sourceRun.2.2.ex (scalar.go (.index i.val)) = some (TargetOperations.encodeWord (storeOut (.data base i.val))).val := by
    intro i member unvisited
    have observed := numeric_bridge.2.2.2.2.2.2.1 i member
    rw [numeric_bridge.2.2.2.1 (.data base i.val) (elementCovered i member)] at observed
    exact observed
  exact complete run frame (by rfl) scalar sourceRun.2.1 sourceRun.2.2 (by rfl) (by rfl) old.clear indices base True.intro
    storeOut numericOut targetOut tail (by rfl) nextBefore numeric_bridge.2.2.2.1 covered
    (by intro j live; change j < 0 at live; omega) fitting nextTarget nextSource

theorem ordered_repeated_delete :
    (wordView sourceRun.2.2,wordView sourceTwice.2.2,sourceTwice.2.2.ex.journal.length,
      graphView old.clear,graphView old.clear.clear,storeView storeOut,storeView storeTwice,
      numericView numericOut,numericView numericTwice,targetView targetOut,targetView targetTwice,
      sourceContext sourceTwice.2.2,targetContext targetTwice) =
    ([some 2,some 7,some 17,some 71,some 101,some 0,some 0,some 0,some 61,some 41],
     [some 2,some 7,some 17,some 71,some 101,some 0,some 0,some 0,some 61,some 41],5,
     (0,3,some w0,some w0,some w61,none,none,none),(0,3,some w0,some w0,some w61,none,none,none),
     (w0,w0,w0,w61,w93,w101,w87),(w0,w0,w0,w61,w93,w101,w87),
     (w0,w0,w0,w61,w93,w101,w87),(w0,w0,w0,w61,w93,w101,w87),
     [0,0,0,61,93,101,87],[0,0,0,61,93,101,87],sourceContext prior.2.2,targetContext target) := by
  rfl
end Controls

/-- info: 'Solidity.Backend.StorageOps.SourceArrayDeleteNumeric.complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms complete

/-- info: 'Solidity.Backend.StorageOps.SourceArrayDeleteNumeric.Controls.numeric_bridge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Controls.numeric_bridge

/-- info: 'Solidity.Backend.StorageOps.SourceArrayDeleteNumeric.Controls.ordered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Controls.ordered

/-- info: 'Solidity.Backend.StorageOps.SourceArrayDeleteNumeric.Controls.physical_frames' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Controls.physical_frames

/-- info: 'Solidity.Backend.StorageOps.SourceArrayDeleteNumeric.Controls.wrong_header' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Controls.wrong_header

/-- info: 'Solidity.Backend.StorageOps.SourceArrayDeleteNumeric.Controls.collision_control' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Controls.collision_control

/-- info: 'Solidity.Backend.StorageOps.SourceArrayDeleteNumeric.Controls.failed_query_boundary' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Controls.failed_query_boundary

/-- info: 'Solidity.Backend.StorageOps.SourceArrayDeleteNumeric.Controls.source_restore' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Controls.source_restore

/-- info: 'Solidity.Backend.StorageOps.SourceArrayDeleteNumeric.Controls.repeated_delete_bridge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Controls.repeated_delete_bridge

/-- info: 'Solidity.Backend.StorageOps.SourceArrayDeleteNumeric.Controls.ordered_repeated_delete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Controls.ordered_repeated_delete

end Solidity.Backend.StorageOps.SourceArrayDeleteNumeric
