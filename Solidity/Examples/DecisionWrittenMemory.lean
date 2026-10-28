import Solidity.Examples.Decision
import Solidity.Calculus.HashWritten

/-!
# Written-memory/hash composition controls

The original M7 pin is refuted by the certified written-memory stage. The
full ordered matrix retains every prior path and records that improvement. `allocAll` has no `dl!`
notation, as in `Examples/Decision.lean`; all terms use existing printed
memory/hash symbols. The certificate test proves composition without claiming
general negative-array extraction beyond the exact written-equality schema.
-/
namespace Solidity.Examples.DecisionWrittenMemory
open Solidity.Decide Solidity.Examples.DecisionHashes
open Solidity.Examples.Tactics.Hashing (Names)
set_option Elab.async false

def writeFirst : Upd Names Γst Γst :=
  .snoc .nil (.memory (.app3 .write (.app0 .memory)
    (.app2 (.mat .dyn) (.pvI (.there .here)) (num 0)) (.app1 .mval (num 1))))
def writtenSelf : Fml Names [] := strings (.upd .box writeFirst (.eq hS hS))
def inputSelf : Fml Names [] := strings (.upd .box writeFirst .tt)
def inputDiamond : Fml Names [] := strings (.upd .diamond writeFirst .tt)

def observation {C : Contract} : LeafVerdict C → String × Option Nat
  | .proved => ("proved", none)
  | .unknown => ("unknown", none)
  | .refuted σ => ("refuted", some σ.H.length)

def observations (φ : Fml Names []) : List (String × (String × Option Nat)) := [
  ("mem", observation (decideMem φ)),
  ("K-keccak", observation (decideHashK .keccak (by decide) φ)),
  ("K-sha256", observation (decideHashK .sha256 (by decide) φ)),
  ("K-ripemd160", observation (decideHashK .ripemd160 (by decide) φ)),
  ("2-keccak-sha256", observation (decideHash2 .keccak .sha256 (by decide) (by decide) φ)),
  ("2-sha256-keccak", observation (decideHash2 .sha256 .keccak (by decide) (by decide) φ)),
  ("2-keccak-ripemd160", observation (decideHash2 .keccak .ripemd160 (by decide) (by decide) φ)),
  ("2-ripemd160-keccak", observation (decideHash2 .ripemd160 .keccak (by decide) (by decide) φ)),
  ("2-sha256-ripemd160", observation (decideHash2 .sha256 .ripemd160 (by decide) (by decide) φ)),
  ("2-ripemd160-sha256", observation (decideHash2 .ripemd160 .sha256 (by decide) (by decide) φ)),
  ("3-keccak-sha256-ripemd160", observation (decideHash3 .keccak .sha256 .ripemd160 (by decide) (by decide) (by decide) φ)),
  ("3-keccak-ripemd160-sha256", observation (decideHash3 .keccak .ripemd160 .sha256 (by decide) (by decide) (by decide) φ)),
  ("3-sha256-keccak-ripemd160", observation (decideHash3 .sha256 .keccak .ripemd160 (by decide) (by decide) (by decide) φ)),
  ("3-sha256-ripemd160-keccak", observation (decideHash3 .sha256 .ripemd160 .keccak (by decide) (by decide) (by decide) φ)),
  ("3-ripemd160-keccak-sha256", observation (decideHash3 .ripemd160 .keccak .sha256 (by decide) (by decide) (by decide) φ)),
  ("3-ripemd160-sha256-keccak", observation (decideHash3 .ripemd160 .sha256 .keccak (by decide) (by decide) (by decide) φ)),
  ("hash", observation (decideHash φ)), ("goal", observation (decideGoal φ))]

#eval [("original", Solidity.Examples.Decision.gapWrittenMemory),
  ("writtenSelf", writtenSelf), ("inputSelf", inputSelf), ("inputDiamond", inputDiamond)].map
  (fun (name, φ) => (name, observations φ))
#eval Solidity.Examples.Decision.gapWrittenMemory.inTarget {}


open Solidity.Decide.WrittenMemory

/-- `[s[0] = 1] hash(s) == hash(s)` is true even when the box write fails. -/
private theorem writtenSelf_holdsS (σ : State Names []) : Fml.holdsS σ writtenSelf := by
  intro s _ t _
  apply Upd.afterT_intro
  · intro _; trivial
  · intro _ _ _; rfl

/-- The same box with `true` as its input leaf preserves the write guard. -/
private theorem inputSelf_valid : Fml.Valid inputSelf := by
  intro σ s t
  apply Upd.afterT_intro
  · intro _; trivial
  · intro _ _ _; trivial

/-- A concrete proof-backed input reduction, not a claimed general producer. -/
def writtenSelfReduction : HashInputReduction writtenSelf :=
  ⟨inputSelf, fun σ _ => ⟨fun _ => inputSelf_valid σ, fun _ => writtenSelf_holdsS σ⟩⟩

/-- The existing memory decider can finish this certified written-hash goal. -/
theorem writtenSelf_certified : Fml.ValidH writtenSelf := by
  have hb : (match decideMem inputSelf with | .proved => true | _ => false) = true := by
    decide +kernel
  cases hd : decideMem inputSelf with
  | proved => exact writtenSelfReduction.valid_of_decideMem hd
  | refuted σ => rw [hd] at hb; cases hb
  | unknown => rw [hd] at hb; cases hb

#guard writtenSelfReduction.cut?.isSome
#guard (observations Solidity.Examples.Decision.gapWrittenMemory).map (·.2) =
  List.replicate 16 ("unknown", none) ++ List.replicate 2 ("refuted", some 0)
#guard (observations writtenSelf).map (·.2) = List.replicate 18 ("unknown", none)
#guard (observations inputSelf).map (·.2) =
  [("proved", none)] ++ List.replicate 16 ("unknown", none) ++ [("proved", none)]
#guard (observations inputDiamond).map (·.2) =
  [("refuted", some 0)] ++ List.replicate 16 ("unknown", none) ++ [("refuted", some 0)]

/-- Hashes observe bytes, so `1` and `257` have the same input for every kind. -/
theorem modulo_byte_control (k : HashKind) : k.apply [1] = k.apply [257] :=
  k.apply_congr (by decide +kernel)

/-- The actual family has different hashes at bytes `1` and `2`, with no
collision-freedom assumption. This is a concrete negative hash control. -/
theorem distinct_written_hashes (k : HashKind) (hk : k ≠ .ecrecover) :
    famHash k 1 ≠ famHash k 2 := by
  intro he
  have h : (1 : Nat) = 2 := famOK_inj (famOK_bound k hk) (by decide) (by decide) he
  exact (by decide : (1 : Nat) ≠ 2) h

/-- Distinct invalid recovery inputs both return zero: no converse for ecrecover. -/
theorem ecrecover_converse_control :
    HashKind.apply .ecrecover [1] = HashKind.apply .ecrecover [2] ∧
      (([1] : List Int).map byte) ≠ (([2] : List Int).map byte) := by
  exact ⟨rfl, by decide +kernel⟩

abbrev UA : RefTy := .array (.prim .uint)
private def sampleObj : MObj [] UA := ⟨[uintOfNat 9, uintOfNat 2], by decide⟩
private def sampleHeap : Heap [UA] := (Heap.empty.alloc sampleObj).1
private def sampleRef : HRef [UA] UA := ⟨0, rfl⟩
private def sampleWritten : Heap [UA] :=
  sampleHeap.set sampleRef (MObj.setElem .dyn (sampleHeap.get sampleRef) 0 (uintOfNat 1))

/-- The actual heap write succeeds; this is not merely an observation of List.set. -/
private theorem sample_write :
    sampleHeap.writeAddr (.index sampleRef .dyn (uintOfNat 0)) (uintOfNat 1) =
      some sampleWritten := by
  simp only [Heap.writeAddr, Heap.setIndex, MObj.elems_dyn]
  simp only [show (uintOfNat 0).val.toNat = 0 from by decide +kernel,
    show 0 < (sampleHeap.get sampleRef).val.length from by decide +kernel,
    ↓reduceIte, sampleWritten]

/-- Applying the successful-write/hash-input bridge preserves the tail byte. -/
theorem actual_write_input :
    (⟨List.prefix_refl [UA], sampleWritten, ()⟩ : Grown [UA] (fun _ => Unit)).hashInput UA 0 =
      some [1, 2] := by
  have hw := hashInput_write_index
    (⟨List.prefix_refl [UA], sampleHeap, ()⟩ : Grown [UA] (fun _ => Unit)) sample_write
  exact hw

/-- The actual write's input observation determines the output for every
kind, including recovery, without any injectivity assumption. -/
theorem actual_write_hash (k : HashKind) :
    (⟨List.prefix_refl [UA], sampleWritten, ()⟩ : Grown [UA] (fun _ => Unit)).hashId k UA 0 =
      k.apply [1, 2] := by
  change k.apply (MObj.words UA (sampleWritten.get sampleRef)) = _
  apply HashKind.apply_congr
  have h := (hashInput_ref
    (⟨List.prefix_refl [UA], sampleWritten, ()⟩ : Grown [UA] (fun _ => Unit)) sampleRef).symm.trans actual_write_input
  exact Option.some.inj h

private def aliasWrittenState : State Names Γst :=
  { storage := Storage.init Names
    H := [UA]
    heap := sampleWritten
    env := (some sampleRef, some sampleRef, ()) }

/-- Both aliases read the actual newly written bytes, for every hash kind. -/
theorem alias_written_hashes (k : HashKind) :
    (hnode k (.there .here) : Tm Names Γst (.val .uint)).denote aliasWrittenState =
      some (k.apply [1, 2]) ∧
    (hnode k .here : Tm Names Γst (.val .uint)).denote aliasWrittenState =
      some (k.apply [1, 2]) := by
  constructor
  · exact (hnode_denote aliasWrittenState k (.there .here) (id := 0) rfl).trans
      (congrArg some (actual_write_hash k))
  · exact (hnode_denote aliasWrittenState k .here (id := 0) rfl).trans
      (congrArg some (actual_write_hash k))

#guard (([9, 2] : List Int).set 0 1).map byte = [1, 2]
#guard (([9, 2] : List Int).set 0 1).map byte ≠ [1, 3]
#guard (([9, 2] : List Int).set 0 1).map byte ≠ [1]
#guard (([9, 2] : List Int).set 0 257).map byte = [1, 2]

private def emptyState : State Names [.mem UA] :=
  let a := (State.init Names).alloc (R := UA) (⟨[], by decide⟩ : MObj [] UA)
  a.1.push (t := .mem UA) (some a.2)
private def emptyWrite : Upd Names [.mem UA] [.mem UA] :=
  .snoc .nil (.memory (.app3 .write (.app0 .memory)
    (.app2 (.mat .dyn) (.pvI .here) (num 0)) (.app1 .mval (num 1))))
private def emptyPair : Fml Names [.mem UA] := .eq (hnode .keccak .here) (hnode .keccak .here)

/-- A write into a zero-length allocated array fails in the actual updater. -/
private theorem empty_write_fails : emptyWrite.globT emptyState = none := by
  exact Option.isNone_iff_eq_none.mp (by decide +kernel)

/-- The failed zero-length write is accepted by the box. -/
theorem empty_box_control : Fml.holdsS emptyState (.upd .box emptyWrite emptyPair) := by
  change emptyWrite.afterT .box emptyState _
  simp only [Upd.afterT, empty_write_fails]
  exact Or.inl trivial

/-- The same write is rejected by the diamond, with exhaustion excluded by
its existing push-free theorem rather than a changed halt policy. -/
theorem empty_diamond_control : ¬ Fml.holdsS emptyState (.upd .diamond emptyWrite emptyPair) := by
  change ¬ emptyWrite.afterT .diamond emptyState _
  have hx : emptyWrite.exh emptyState = false := Upd.exh_of_pushFree rfl
  simp only [Upd.afterT, empty_write_fails, hx, Modality.onHalt, Bool.false_eq_true, or_self, not_false_eq_true]

/-- An unset local remains unset; the atomic input bridge requires Some identities. -/
theorem unset_control :
    ((State.init Names).push (t := .mem UA) none).getV (.here : Idx [.mem UA] (.mem UA)) = none := rfl

/-- The generalized realization theorem instantiates the ORIGINAL formula;
its syntax certificate and dispatched kernel verdict are checked below. -/
theorem original_refuted :
    ¬ Fml.holdsH (State.init Names) Solidity.Examples.Decision.gapWrittenMemory :=
  WrittenMemory.Realize.schema_refutes (.user "s") (.user "t") .keccak (by decide) .box

/-- info: 'Solidity.Examples.DecisionWrittenMemory.original_refuted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms original_refuted

/-- The actual dispatched original verdict, evaluated by the kernel. -/
theorem original_kernel_verdict :
    (match decideGoal Solidity.Examples.Decision.gapWrittenMemory with
      | .refuted σ => σ.H.length == 0
      | _ => false) = true := by decide +kernel

/-- Coverage here means an actual realized certificate, not a target change. -/
theorem original_realized_covered : Solidity.Examples.Decision.gapWrittenMemory.hashCovered = true :=
  by decide +kernel

/- Every supported kind and both modalities use the same scope-correct
realization. Renaming the binders does not affect extraction. -/
#guard [HashKind.keccak, .sha256, .ripemd160].all fun k =>
  [Modality.box, .diamond].all fun m =>
    let φ : Fml Names [] := WrittenMemory.Realize.schema (.user "a") (.user "b") k m
    observation (decideWrittenHash φ) == ("refuted", some 0)
#eval [HashKind.keccak, .sha256, .ripemd160].map fun k =>
  (k, [Modality.box, .diamond].map fun m =>
    (m, observations (WrittenMemory.Realize.schema (.user "a") (.user "b") k m)))

/- Positive self-equality, recovery, and a different write must be refused
by this exact schema producer. Existing failure controls remain above. -/
#guard decideWrittenHash writtenSelf matches .unknown
#guard decideWrittenHash
  (WrittenMemory.Realize.schema (.user "s") (.user "t") .ecrecover .box : Fml Names []) matches .unknown
private def otherWrite : Fml Names [] := strings (.upd .box
  (.snoc .nil (.memory (.app3 .write (.app0 .memory)
    (.app2 (.mat .dyn) (.pvI (.there .here)) (num 1)) (.app1 .mval (num 1))))) (.eq hS hT))
#guard decideWrittenHash otherWrite matches .unknown

private def otherValue : Fml Names [] := strings (.upd .box
  (.snoc .nil (.memory (.app3 .write (.app0 .memory)
    (.app2 (.mat .dyn) (.pvI (.there .here)) (num 0)) (.app1 .mval (num 2))))) (.eq hS hT))
#guard decideWrittenHash otherValue matches .unknown

private def otherType : Fml Names [] :=
  .allocAll (.user "s") (.array (.prim .bool)) (.allocAll (.user "t") UA
    (.upd .box (.snoc .nil (.memory (.app3 .write (.app0 .memory)
      (.app2 (.mat .dyn) (.pvI (.there .here)) (num 0)) (.app1 .mval (.app0 (.lit false))))))
      (.eq (hnode .keccak (.there .here)) (hnode .keccak .here))))
#guard decideWrittenHash otherType matches .unknown

private def extraScope : Fml Names [] :=
  .allocAll (.user "extra") UA (.allocAll (.user "s") UA (.allocAll (.user "t") UA
    (.upd .box (.snoc .nil (.memory (.app3 .write (.app0 .memory)
      (.app2 (.mat .dyn) (.pvI (.there .here)) (num 0)) (.app1 .mval (num 1)))))
      (.eq (hnode .keccak (.there .here)) (hnode .keccak .here)))))
#guard decideWrittenHash extraScope matches .unknown
#eval [("self", writtenSelf), ("index", otherWrite), ("value", otherValue),
  ("type", otherType), ("scope", extraScope)].map fun (n, φ) => (n, observation (decideWrittenHash φ))

/-- info: 'Solidity.Examples.DecisionWrittenMemory.original_kernel_verdict' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms original_kernel_verdict
/-- info: 'Solidity.Examples.DecisionWrittenMemory.original_realized_covered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms original_realized_covered
/-- info: 'Solidity.Decide.decideWrittenHash_refutes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms decideWrittenHash_refutes
/-- info: 'Solidity.Decide.decideGoal_refutes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms decideGoal_refutes

/-- info: 'Solidity.Examples.DecisionWrittenMemory.writtenSelf_certified' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms writtenSelf_certified
/-- info: 'Solidity.Examples.DecisionWrittenMemory.actual_write_input' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms actual_write_input
/-- info: 'Solidity.Examples.DecisionWrittenMemory.distinct_written_hashes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms distinct_written_hashes
/-- info: 'Solidity.Examples.DecisionWrittenMemory.empty_diamond_control' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms empty_diamond_control

/-- info: 'Solidity.Examples.DecisionWrittenMemory.actual_write_hash' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms actual_write_hash
/-- info: 'Solidity.Examples.DecisionWrittenMemory.alias_written_hashes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms alias_written_hashes

end Solidity.Examples.DecisionWrittenMemory
