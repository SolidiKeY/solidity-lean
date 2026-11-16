import Solidity.Tools.Goal
import Solidity.Backend.CompilerEndpoint
import Solidity.Hash.CollisionBridge
import Solidity.Storage.HashedLayoutEvm
import Solidity.Storage.HashedKeccak

/-!
E4A/H811: specification of a word-addressed refinement of the FULL checked
instruction compiler. Ideal-keccak remains the existing symbolic `Evm.run`.
E4B must construct the prefix producers and prove their operational laws,
compiler correspondence and adaptive corollary. None is a caller-supplied
`PublicCorrectness` or Guard-to-P premise. This is not assembled bytes or an
external EVM claim. No accepted compiler branch or existing Input/Rep is changed.
-/
namespace Solidity.Goals.HashContract

open Solidity.Evm
open Solidity.Hash
open Solidity.Roadmap (Fixed Bytes HashPremise)

/-- ABI preimages, including the explicit natural-byte/runtime-byte conversion. -/
def encoded (p : Storage.Pre) : Bytes := (Storage.encode p).map UInt8.ofNat

def hashPre (F : Fixed) (p : Storage.Pre) : Nat := (F.hash (encoded p)).val

def address (F : Fixed) (s : Slot) : Fin W :=
  wmod ((Storage.ofSlot s).word W (hashPre F))

def word (F : Fixed) : Word → Fin W
  | .val v => v
  | .slot s => address F s

/-- All value-bearing machine cells are numeric; storage is word-addressed.
The payment oracle and every environment field retain the ideal machine's meaning. -/
structure Numeric where
  stack : List (Fin W)
  store : Fin W → Fin W
  mem : Nat → Fin W
  bal : Fin W → Nat
  bal₀ : Fin W → Nat
  self : Fin W
  accepts : Fin W → Fin W → Bool
  caller : Fin W
  callvalue : Fin W
  timestamp : Fin W

/-- Only ordinary instructions use this all-value embedding. Storage/hash
instructions have their own numeric clauses below; they never read this store. -/
def embed (m : Numeric) : Machine :=
  { stack := m.stack.map Word.val, store := WordStore.zero,
    mem := fun i => .val (m.mem i), bal := m.bal, bal₀ := m.bal₀,
    self := m.self, accepts := m.accepts, caller := m.caller,
    callvalue := m.callvalue, timestamp := m.timestamp }

def project (F : Fixed) (store : Fin W → Fin W) (m : Machine) : Numeric :=
  { stack := m.stack.map (word F), store, mem := fun i => word F (m.mem i),
    bal := m.bal, bal₀ := m.bal₀, self := m.self, accepts := m.accepts,
    caller := m.caller, callvalue := m.callvalue, timestamp := m.timestamp }

inductive Result (S : Type) where
  | ok (state : S) (skip : Nat)
  | revert
  | fault

def resultMap (f : S → T) : Result S → Result T
  | .ok s k => .ok (f s) k
  | .revert => .revert
  | .fault => .fault

def idealResult : Evm.Out → Result Machine
  | .ok m k => .ok m k
  | .revert => .revert
  | .fault => .fault

/-- Ordinary opcodes reuse the approved ideal instruction definitions on
numeric operands. Loops are interpreted by the continuation protocol, not here. -/
noncomputable def numericAtom (F : Fixed) (i : Instr) (m : Numeric) : Result Numeric :=
  match i with
  | .push w => .ok { m with stack := word F w :: m.stack } 0
  | .keccakMap => match m.stack with
    | k :: s :: tail => .ok { m with stack := F.hash (encoded (.entry k.val s.val)) :: tail } 0
    | _ => .fault
  | .keccakArr => match m.stack with
    | s :: tail => .ok { m with stack := F.hash (encoded (.data s.val)) :: tail } 0
    | _ => .fault
  | .sload => match m.stack with
    | s :: tail => .ok { m with stack := m.store s :: tail } 0
    | _ => .fault
  | .sstore => match m.stack with
    | s :: v :: tail => .ok { m with
        stack := tail
        store := fun a => if a = s then v else m.store a } 0
    | _ => .fault
  | .loop _ _ => .fault
  | _ => resultMap (project F m.store) (idealResult (i.step (embed m)))

/-- Actual runtime KECCAK inputs only: no synthetic hashes for PUSH or setup. -/
def atomQueries (i : Instr) (m : Numeric) : List Bytes :=
  match i, m.stack with
  | .keccakMap, k :: s :: _ => [encoded (.entry k.val s.val)]
  | .keccakArr, s :: _ => [encoded (.data s.val)]
  | _, _ => []

inductive Frame where
  | test (cond body rest : List Instr)
  | body (cond body rest : List Instr)

inductive Cursor (S : Type) where
  | running (code : List Instr) (skip : Nat) (frames : List Frame) (state : S)
  | halted (result : Result S)

/-- Canonical small-step specification. Skipped instructions emit no query.
A loop condition/body with a pending jump faults, exactly as Evm.loopTurn.
A finite unfinished prefix remains running; it does not assert divergence. -/
noncomputable def tick (atom : Instr → S → Result S)
    (test : S → Option (Bool × S)) : Cursor S → Cursor S
  | .halted r => .halted r
  | .running [] k [] s => .halted (.ok s k)
  | .running [] (_ + 1) (_ :: _) _ => .halted .fault
  | .running [] 0 (.test c b rest :: fs) s =>
    match test s with
    | none => .halted .fault
    | some (false, s') => .running rest 0 fs s'
    | some (true, s') => .running b 0 (.body c b rest :: fs) s'
  | .running [] 0 (.body c b rest :: fs) s => .running c 0 (.test c b rest :: fs) s
  | .running (_ :: rest) (k + 1) fs s => .running rest k fs s
  | .running (.loop c b :: rest) 0 fs s => .running c 0 (.test c b rest :: fs) s
  | .running (i :: rest) 0 fs s =>
    match atom i s with
    | .ok s' k => .running rest k fs s'
    | .revert => .halted .revert
    | .fault => .halted .fault

def idealTest (m : Machine) : Option (Bool × Machine) :=
  match m.stack with
  | .val v :: tail => some (v.val != 0, { m with stack := tail })
  | _ => none

def numericTest (m : Numeric) : Option (Bool × Numeric) :=
  match m.stack with
  | v :: tail => some (v.val != 0, { m with stack := tail })
  | _ => none

/-- E4B's actual producer interface. Its equations below forbid invented,
filtered, successful-only, or caller-selected execution histories. -/
structure Producer where
  ideal : Nat → List Instr → Machine → Cursor Machine
  numeric : Fixed → Nat → List Instr → Numeric → Cursor Numeric

structure Produces (E : Producer) : Prop where
  ideal_zero : ∀ c m, E.ideal 0 c m = .running c 0 [] m
  numeric_zero : ∀ F c m, E.numeric F 0 c m = .running c 0 [] m
  ideal_succ : ∀ n c m, E.ideal (n + 1) c m =
    tick (fun i s => idealResult (i.step s)) idealTest (E.ideal n c m)
  numeric_succ : ∀ F n c m, E.numeric F (n + 1) c m =
    tick (numericAtom F) numericTest (E.numeric F n c m)

/-- Runtime preimages are obtained from every executed instruction boundary,
including those preceding a revert/fault; terminal stuttering adds nothing. -/
def queriesAt : Cursor Numeric → List Bytes
  | .running (i :: _) 0 _ m => atomQueries i m
  | _ => []

def queries (E : Producer) (F : Fixed) (n : Nat) (c : List Instr) (m : Numeric) : List Bytes :=
  (List.range n).flatMap (fun k => queriesAt (E.numeric F k c m))

/-- Exact executed storage operations, separately from representation coverage. -/
inductive Access (A : Type) where
  | read (address : A)
  | write (address : A) (value : Fin W)

def mapAccess (f : A → B) : Access A → Access B
  | .read a => .read (f a)
  | .write a v => .write (f a) v

def idealAccessAt : Cursor Machine → List (Access Slot)
  | .running (.sload :: _) 0 _ m => match m.stack with
    | .slot s :: _ => [.read s]
    | _ => []
  | .running (.sstore :: _) 0 _ m => match m.stack with
    | .slot s :: .val v :: _ => [.write s v]
    | _ => []
  | _ => []

def numericAccessAt : Cursor Numeric → List (Access (Fin W))
  | .running (.sload :: _) 0 _ m => match m.stack with
    | s :: _ => [.read s]
    | _ => []
  | .running (.sstore :: _) 0 _ m => match m.stack with
    | s :: v :: _ => [.write s v]
    | _ => []
  | _ => []

def AccessesAgree (E : Producer) (F : Fixed) (n : Nat) (c : List Instr)
    (m : Machine) (v : Numeric) : Prop :=
  ((List.range n).flatMap (fun k => idealAccessAt (E.ideal k c m))).map
    (mapAccess (address F)) =
  (List.range n).flatMap (fun k => numericAccessAt (E.numeric F k c v))

/-- Every reached symbolic slot operand, including SLOAD/SSTORE and values
loaded from memory, is covered. Extra observation cells are explicit below. -/
def stackSlots (m : Machine) : List Slot := m.stack.filterMap fun w =>
  match w with | .slot s => some s | .val _ => none

def slotsAt : Cursor Machine → List Slot
  | .running _ _ _ m => stackSlots m
  | .halted (.ok m _) => stackSlots m
  | _ => []

def locations (E : Producer) (n : Nat) (c : List Instr) (m : Machine)
    (observed : List Slot) : List Slot :=
  observed ++ (List.range (n + 1)).flatMap (fun k => slotsAt (E.ideal k c m))

/-- Concrete representation preimages: the same recursive Loc.pres producer
as Backend.StorageOps.LayoutAccess.runPreimages, after HashedLayoutEvm.ofSlot.
These include setup/PUSH dependencies; they are NOT runtime KECCAK events. -/
def preimages (F : Fixed) (slots : List Slot) : List Bytes :=
  (slots.flatMap (fun s => (Storage.ofSlot s).pres W (hashPre F))).map encoded

/-- All machine fields are retained. Storage agreement is on the complete
run footprint plus arbitrary requested observations, never just final writes. -/
def Represents (F : Fixed) (slots : List Slot) (m : Machine) (v : Numeric) : Prop :=
  v.stack = m.stack.map (word F) ∧ (∀ i, v.mem i = word F (m.mem i)) ∧
  (∀ s ∈ slots, v.store (address F s) = m.store.cells s) ∧
  v.bal = m.bal ∧ v.bal₀ = m.bal₀ ∧ v.self = m.self ∧ v.accepts = m.accepts ∧
  v.caller = m.caller ∧ v.callvalue = m.callvalue ∧ v.timestamp = m.timestamp

def ResultRelated (F : Fixed) (slots : List Slot) : Result Machine → Result Numeric → Prop
  | .ok m k, .ok v j => k = j ∧ Represents F slots m v
  | .revert, .revert | .fault, .fault => True
  | _, _ => False

def Related (F : Fixed) (slots : List Slot) : Cursor Machine → Cursor Numeric → Prop
  | .running c k fs m, .running d j gs v =>
    c = d ∧ k = j ∧ fs = gs ∧ Represents F slots m v
  | .halted r, .halted s => ResultRelated F slots r s
  | _, _ => False

/-- Non-cryptographic representation obligations are explicit, not counted
as collision failures and not inferred from CollisionFree. No fragment filter. -/
def Ready (E : Producer) (F : Fixed) (n : Nat) (c : List Instr)
    (m : Machine) (v : Numeric) (observed : List Slot) : Prop :=
  F.regionLen ≤ W ∧ F.rootSlots ≤ W ∧
  (∀ s ∈ locations E n c m observed, (Storage.ofSlot s).Bounded F.regionLen F.rootSlots) ∧
  Represents F (locations E n c m observed) m v

def Premise (E : Producer) (F : Fixed) (n : Nat) (c : List Instr)
    (m : Machine) (v : Numeric) (observed : List Slot) : Prop :=
  let ps := preimages F (locations E n c m observed)
  HashPremise F (queries E F n c v ++ ps) ps

/-- Every prefix observation, not merely the terminal state. -/
def PrefixRelated (E : Producer) (F : Fixed) (n : Nat) (c : List Instr)
    (m : Machine) (v : Numeric) (observed : List Slot) : Prop :=
  (∀ k, k ≤ n → Related F observed (E.ideal k c m) (E.numeric F k c v)) ∧
  AccessesAgree E F n c m v

/-- Only an execution with no terminal prefix has the divergence/fault limit.
The finite-prefix probability statement below never counts this infinite event. -/
def Limit (run : Nat → Cursor S) (out : Result S) : Prop :=
  (∃ n, run n = .halted out) ∨
    (out = .fault ∧ ∀ n r, run n ≠ .halted r)

/-- Full-domain compiler obligation: same successful checked compilation,
unchanged Input and exact symbolic agreement. H811 adds numeric correspondence;
R1/R2 remain the existing CompilerEndpoint, conjoined in the registered goal. -/
def CompilerBridge (E : Producer) : Prop :=
  ∀ {C : Contract} {Γ Δ : Ctx} (b : Nat) (frag : Frag Γ) (P : Prog C Γ Δ)
    (r : Evm.Compiler.Compilation b frag P), Evm.Compiler.compile b frag P = some r →
  ∀ (L frame : Nat) (base : Nat → Fin W) (σ : State C Γ) (m : Machine),
    r.Input L frame base σ m → r.AgreesExact L frame base σ m ∧
    ∀ (F : Fixed) (v : Numeric) (observed : List Slot),
      (∀ n, Ready E F n r.code m v observed → Premise E F n r.code m v observed →
        PrefixRelated E F n r.code m v observed) ∧
      ((∀ n, Ready E F n r.code m v observed ∧ Premise E F n r.code m v observed) →
        ((∃ out, Limit (fun n => E.numeric F n r.code v) out ∧
          ResultRelated F observed (idealResult (Evm.run r.code m)) out) ∧
         (∀ out, Limit (fun n => E.numeric F n r.code v) out →
          ResultRelated F observed (idealResult (Evm.run r.code m)) out)))

/-- Failure of the concrete compiled prefix relation, not a generic proposition. -/
noncomputable def failure (E : Producer) (F : Fixed) (n : Nat) (c : List Instr)
    (m : Machine) (v : Numeric) (observed : List Slot) : Bool := by
  classical
  exact decide (¬ PrefixRelated E F n c m v observed)

/-- The existing adaptive combined bound, on ONE actual compiled prefix.
The compiler output is fixed; initial worlds may depend on the sampled oracle.
Both runtime and representation/setup inputs must be in the same strategy's
transcript. q counts all its queries, including offline/grinding queries.
No probability assertion about fixed real Keccak, or all infinite prefixes. -/
def AdaptiveBridge (E : Producer) : Prop :=
  ∀ {C : Contract} {Γ Δ : Ctx} (b : Nat) (frag : Frag Γ) (P : Prog C Γ Δ)
    (r : Evm.Compiler.Compilation b frag P), Evm.Compiler.compile b frag P = some r →
  ∀ (F : Fixed) (s : List Nat → Bytes) (dom : List Bytes) (q n : Nat)
    (L frame : Nat) (base : List Nat → Nat → Fin W)
    (σ : List Nat → State C Γ) (m : List Nat → Machine) (v : List Nat → Numeric)
    (observed : List Slot),
    (∀ t, s t ∈ dom) → (∀ a ∈ List.range F.rootSlots, a < W) →
    (∀ g ∈ tuples W dom.length, r.Input L frame (base g) (σ g) (m g)) →
    (∀ g ∈ tuples W dom.length,
      Ready E (CollisionBridge.oracleFixed F dom g) n r.code (m g) (v g) observed) →
    (∀ g ∈ tuples W dom.length, ∀ x ∈
      queries E (CollisionBridge.oracleFixed F dom g) n r.code (v g) ++
      preimages (CollisionBridge.oracleFixed F dom g) (locations E n r.code (m g) observed),
      x ∈ eagerQueries s (oracleOf dom g) q) →
    2 ^ (256 + 1) * (tuples W dom.length).countP (fun g =>
      failure E (CollisionBridge.oracleFixed F dom g) n r.code (m g) (v g) observed) ≤
      CollisionBridge.numerator q F.regionLen (List.range F.rootSlots).length * W ^ dom.length

/-- Producer adequacy for the approved ideal semantics, including divergence.
This correspondence must be proved, not inferred from the new operational spec. -/
def IdealAdequacy (E : Producer) : Prop :=
  ∀ c m out, Limit (fun n => E.ideal n c m) out ↔ out = idealResult (Evm.run c m)

end Solidity.Goals.HashContract

namespace Solidity.Goals
open Solidity.Goal

/-- H811 authorizes this specification, not an implementation or proof.
E4B dependencies: the exact producer equations and IdealAdequacy above;
Storage.ofSlot/Loc.pres and HashedKeccak.encode_inj plus bounded natural-byte
to UInt8 conversion for byte coverage; compiler operand-shape preservation;
Storage.Representation.Transport for finite store steps; CompilerEndpoint and
Compilation.Input/Rep/AgreesExact for every branch; CollisionBridge.run_premise_le
for the sampled bound. IS0C's typed storage/frame observer may help establish
source coverage, but whole IS0 session semantics is not a theorem dependency.
The ideal mode remains true independently of the concrete per-run premise. -/
@[goal Solidity.Hash.compiler_correct_collisionFree "e4-hash-bridge"]
def compilerCorrectCollisionFree : Prop :=
  Backend.CompilerEndpoint ∧ ∃ E : HashContract.Producer,
    HashContract.Produces E ∧ HashContract.IdealAdequacy E ∧
    HashContract.CompilerBridge E ∧ HashContract.AdaptiveBridge E

end Solidity.Goals
