import SolidityBridge.Yul.FrameCertificatesV2
namespace SolidityBridge.Yul.FrameCertificatesV2.Controls
open Solidity Backend Scalar
open Solidity.Yul.Compilation

def dirty : Word := BitVec.ofNat 256 (2^200+257)
def maximum : Word := BitVec.ofNat 256 (2^256-1)
def locals : Vector Word 2 := #v[11,dirty]
def newer : Vector Word 2 := #v[31,47]
def reader := (read? locals newer 0).get (by rfl)
def writer := (write? locals newer 0 dirty).get (by rfl)
def writes : NestedWrites 2 2 :=
  [(⟨0,by decide⟩,dirty),(⟨1,by decide⟩,maximum),(⟨0,by decide⟩,257)]
def updater := (updates? writes locals newer).get (by rfl)
def empty := (updates? ([] : NestedWrites 2 2) locals newer).get (by rfl)
def many : Vector Word 14 := #v[0,1,2,3,4,5,6,7,8,9,10,11,12,dirty]
def beyond : Vector Word 15 := #v[0,1,2,3,4,5,6,7,8,9,10,11,12,13,dirty]
def lastReader := (read? many newer 13).get (by rfl)
def lastWriter := (write? many newer 13 maximum).get (by rfl)
#check reader.frame [71,dirty]
#check writer.frame [71,dirty]
#check updater.frame [71,dirty]
#check reader.capacity_empty
#check writer.capacity_empty
#check updater.capacity_empty
#check empty.capacity_empty
#guard reader.peak == 1
#guard writer.peak == 0
#guard updater.peak == 1
#guard empty.peak == 0
#guard reader.code = [.op (.DUP 2)]
#guard lastReader.code = [.op (.DUP 15)]
#guard lastWriter.code = [.op (.SWAP 15),.op .POP]
#guard (read? beyond newer 14).isNone
#guard (write? beyond newer 14 dirty).isNone
#guard run reader.code [31,47,11,dirty,71] = some [11,31,47,11,dirty,71]
#guard run writer.code [dirty,31,47,11,dirty,71] = some [31,47,dirty,dirty,71]
#guard run updater.code [31,47,11,dirty,71] = some [31,47,257,maximum,71]
#guard run lastReader.code (newer.toList ++ many.toList ++ [71]) =
  some (dirty :: (newer.toList ++ many.toList ++ [71]))
#guard run reader.code [] = none
#guard run writer.code [dirty,31,47] = none
#guard run lastReader.code [] = none
-- Actual admitted caller domain and boundary trace. Supplied value counts
-- in writer input; PUSH in updater instead needs one extra transient word.
#guard stackBound reader.code 1023
#guard !(stackBound reader.code 1024)
#guard stackBound writer.code 1024
#guard !(stackBound writer.code 1025)
#guard stackBound updater.code 1023
#guard !(stackBound updater.code 1024)
#guard stackBound empty.code 1024
#guard !(stackBound empty.code 1025)
def read_boundary := reader.capacity (List.replicate 1019 71) (by
  simp only [List.length_append,List.length_replicate,Vector.length_toList]
  decide)
def empty_boundary := empty.capacity (List.replicate 1020 71) (by
  simp only [List.length_append,List.length_replicate,Vector.length_toList]
  decide)
#check read_boundary
#check empty_boundary
-- Frame's gasless run law remains valid outside its capacity domain.
#guard (run reader.code (newer.toList ++ locals.toList ++ List.replicate 1020 71)).map List.length == some 1025
-- No choice of V2 peak can conceal this overfull output, independently of
-- this adapter's room checker or its selected peak.
def impossible_read := Selection.V2.no_overfull_output (List.replicate 1024 dirty)
  (dirty :: List.replicate 1024 dirty) (by
    simp only [List.length_cons,List.length_replicate]
    decide)
#check impossible_read
#guard (updates? ([] : NestedWrites 1024 0) (Vector.replicate 1024 dirty) #v[]).isSome
#guard (updates? ([] : NestedWrites 1025 0) (Vector.replicate 1025 dirty) #v[]).isNone
#guard (read? (Vector.replicate 1024 dirty) #v[] 0).isNone
#guard (write? (Vector.replicate 1024 dirty) #v[] 0 dirty).isNone
-- A real first PUSH prefix reaches the temporary extra word. The generic
-- V2 theorem bounds this actual reached stack using the derived capacity.
def update_peak_witness := updater.prefixes [71] (by decide)
  [pushWord dirty] (updater.code.drop 1) [dirty,31,47,11,dirty,71]
  (by rfl) (by simp only [run,step_pushWord,Option.bind_some]; rfl)
#check update_peak_witness

-- Generated from the actual scoped kernel axiom report.
/-- info: 'SolidityBridge.Yul.FrameCertificatesV2.updatePeak' does not depend on any axioms -/
#guard_msgs in
#print axioms SolidityBridge.Yul.FrameCertificatesV2.updatePeak
/-- info: 'SolidityBridge.Yul.FrameCertificatesV2.readFrame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.FrameCertificatesV2.readFrame
/-- info: 'SolidityBridge.Yul.FrameCertificatesV2.writeFrame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.FrameCertificatesV2.writeFrame
/-- info: 'SolidityBridge.Yul.FrameCertificatesV2.updatesFrame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.FrameCertificatesV2.updatesFrame
/-- info: 'SolidityBridge.Yul.FrameCertificatesV2.read?' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.FrameCertificatesV2.read?
/-- info: 'SolidityBridge.Yul.FrameCertificatesV2.write?' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.FrameCertificatesV2.write?
/-- info: 'SolidityBridge.Yul.FrameCertificatesV2.updates?' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.FrameCertificatesV2.updates?
/-- info: 'SolidityBridge.Yul.FrameCertificatesV2.Controls.reader' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.FrameCertificatesV2.Controls.reader
/-- info: 'SolidityBridge.Yul.FrameCertificatesV2.Controls.writer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.FrameCertificatesV2.Controls.writer
/-- info: 'SolidityBridge.Yul.FrameCertificatesV2.Controls.updater' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.FrameCertificatesV2.Controls.updater
/-- info: 'SolidityBridge.Yul.FrameCertificatesV2.Controls.empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.FrameCertificatesV2.Controls.empty
/-- info: 'SolidityBridge.Yul.FrameCertificatesV2.Controls.lastReader' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.FrameCertificatesV2.Controls.lastReader
/-- info: 'SolidityBridge.Yul.FrameCertificatesV2.Controls.lastWriter' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.FrameCertificatesV2.Controls.lastWriter
/-- info: 'SolidityBridge.Yul.FrameCertificatesV2.Controls.read_boundary' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.FrameCertificatesV2.Controls.read_boundary
/-- info: 'SolidityBridge.Yul.FrameCertificatesV2.Controls.empty_boundary' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.FrameCertificatesV2.Controls.empty_boundary
/-- info: 'SolidityBridge.Yul.FrameCertificatesV2.Controls.impossible_read' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.FrameCertificatesV2.Controls.impossible_read
/-- info: 'SolidityBridge.Yul.FrameCertificatesV2.Controls.update_peak_witness' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SolidityBridge.Yul.FrameCertificatesV2.Controls.update_peak_witness
end SolidityBridge.Yul.FrameCertificatesV2.Controls
