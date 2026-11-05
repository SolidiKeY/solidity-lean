import Solidity.Backend.AbiEntry.SourceRoutes
import Solidity.Source.SemanticsExamples

/-! Typed Source fixture with colliding model selectors, body-less exclusion
and actual compiled routes. The fixed hash is a control, not a Keccak test.
A padded short-input mismatch records the necessary dispatch boundary. -/
namespace Solidity.Backend.AbiEntry.SourceRoutesControls
open Solidity.Evm
open Interface (RouteCtx rawSelectorWord routeResult)
private def fn (name : String) : Source.Syn (.part false) :=
  .function (.ident name) .nil (some .pub) none .nil (decide (name="skip")) none .nil
    (if name="skip" then .none else .some (.block .nil))
private def unit : Source.Syn .unit :=
  .unit (.cons (.contract true "C" .none .nil (.cons (fn "skip") (.cons (fn "f") (.cons (fn "g") .nil)))) .nil)
private def E : Source.Env := unit.env
private def body : Source.RBody E :=
  {ps := [],rs := [],inModifier := false,locals := [],out := [],items := .nil}
private def fixed : Roadmap.Fixed :=
  {Source.SemanticsExamples.toyFixed with
    evm := {Source.SemanticsExamples.toyFixed.evm with
      keccak := fun _ => 0xdeadbe00*2^224
      keccak_lt := fun _ => by decide}}
private def global (pipeline : Roadmap.Pipeline) : Source.Glob E :=
  ⟨{body declaration := if declaration.kind == .function && declaration.name != "skip" then some body else none
    consts _ := none,inits _ := [],ctor _ := none,ctorLocals _ := [],baseArgs _ := [],contracts := ["C"]},
    pipeline,fixed,fun _ => ⟨0,by decide⟩,fun _ _ => false,fun _ => .answer (.success []),⟨0,by decide⟩⟩
private def labels (declaration : Source.Decl) : Fin W :=
  if declaration.name="f" then wmod 11 else if declaration.name="g" then wmod 22 else wmod 77
private def fallback : Fin W := wmod 99
private def C : Contract := {vars := []}
private def fullBytes : List UInt8 := [0xde,0xad,0xbe,0,0xaa,0xbb]
private def missBytes : List UInt8 := [0x12,0x34,0x56,0x78]
private def shortBytes : List UInt8 := [0xde,0xad,0xbe]
private def frame (bytes : List UInt8) : Source.Fr := {Source.SemanticsExamples.F0 with cd := bytes}
private def machine (bytes : List UInt8) : Machine :=
  {Machine.init with
    mem := fun address => if address=7 then .val (rawSelectorWord (frame bytes)) else .val (wmod 71)
    stack := [.val (wmod 258),.val (wmod 513)]}
private def written (bytes : List UInt8) (label : Fin W) : Machine :=
  {machine bytes with mem := upd (machine bytes).mem 8 (.val label)}
private def compiled (pipeline : Roadmap.Pipeline) :=
  SelectorRoutes.compiled C 7 (SourceRoutes.table (global pipeline) "C" labels) fallback

theorem source_table (pipeline : Roadmap.Pipeline) :
    (SourceRoutes.table (global pipeline) "C" labels).length=2 ∧
    (((global pipeline).pickFn (frame fullBytes) fullBytes).map labels).getD fallback=wmod 11 := by cases pipeline <;> decide

theorem source_miss (pipeline : Roadmap.Pipeline) :
    (((global pipeline).pickFn (frame missBytes) missBytes).map labels).getD fallback=fallback := by cases pipeline <;> decide

theorem runtime_match (pipeline : Roadmap.Pipeline) :
    run (compiled pipeline).code (machine fullBytes)=.ok (written fullBytes (wmod 11)) 0 := by
  have reached := SourceRoutes.executed (global pipeline) (frame fullBytes) labels fallback (by decide)
    C 7 (compiled pipeline) (SourceRoutes.selected (global pipeline) "C" labels fallback C 7) (machine fullBytes) rfl
  change run (compiled pipeline).code (machine fullBytes)=
    .ok (written fullBytes ((((global pipeline).pickFn (frame fullBytes) fullBytes).map labels).getD fallback)) 0 at reached
  rw [(source_table pipeline).2] at reached
  exact reached

theorem runtime_miss (pipeline : Roadmap.Pipeline) :
    run (compiled pipeline).code (machine missBytes)=.ok (written missBytes fallback) 0 := by
  have reached := SourceRoutes.executed (global pipeline) (frame missBytes) labels fallback (by decide)
    C 7 (compiled pipeline) (SourceRoutes.selected (global pipeline) "C" labels fallback C 7) (machine missBytes) rfl
  change run (compiled pipeline).code (machine missBytes)=
    .ok (written missBytes ((((global pipeline).pickFn (frame missBytes) missBytes).map labels).getD fallback)) 0 at reached
  rw [source_miss pipeline] at reached
  exact reached

theorem short_source_refuses (pipeline : Roadmap.Pipeline) :
    (((global pipeline).pickFn (frame shortBytes) shortBytes).map labels).getD fallback=fallback := by cases pipeline <;> decide

/-- Numeric routing without the external full-prefix guard differs from Source
on this short input; no SourceRoutes full-prefix theorem is applied here. -/
theorem short_numeric_collision (pipeline : Roadmap.Pipeline) :
    run (compiled pipeline).code (machine shortBytes)=.ok (written shortBytes (wmod 11)) 0 := by
  have reached := SelectorRoutes.executed C 7 (SourceRoutes.table (global pipeline) "C" labels) fallback
    (compiled pipeline) (SourceRoutes.selected (global pipeline) "C" labels fallback C 7)
    (machine shortBytes) (rawSelectorWord (frame shortBytes)) rfl
  have selected : routeResult (SourceRoutes.table (global pipeline) "C" labels) fallback
      (rawSelectorWord (frame shortBytes))=wmod 11 := by cases pipeline <;> decide
  rw [selected] at reached
  exact reached

theorem protected_and_saved (bytes : List UInt8) (label : Fin W) :
    (written bytes label).mem 7=.val (rawSelectorWord (frame bytes)) ∧
    (written bytes label).mem 9=.val (wmod 71) ∧
    (written bytes label).stack=[.val (wmod 258),.val (wmod 513)] := ⟨rfl,rfl,rfl⟩

/-- info: 'Solidity.Backend.AbiEntry.SourceRoutesControls.source_table' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_table
/-- info: 'Solidity.Backend.AbiEntry.SourceRoutesControls.source_miss' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_miss
/-- info: 'Solidity.Backend.AbiEntry.SourceRoutesControls.runtime_match' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms runtime_match
/-- info: 'Solidity.Backend.AbiEntry.SourceRoutesControls.runtime_miss' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms runtime_miss
/-- info: 'Solidity.Backend.AbiEntry.SourceRoutesControls.short_source_refuses' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms short_source_refuses
/-- info: 'Solidity.Backend.AbiEntry.SourceRoutesControls.short_numeric_collision' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms short_numeric_collision
/-- info: 'Solidity.Backend.AbiEntry.SourceRoutesControls.protected_and_saved' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms protected_and_saved
end Solidity.Backend.AbiEntry.SourceRoutesControls
