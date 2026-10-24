import Solidity.Evm.MemoryStructGrow
import Solidity.Evm.Compiler

/-! Populated structs, a separate array and reserved locals exercise the
representation, allocator and public compiler. The checked source programs
retain shared and independent objects across mixed writes, scopes and array
allocation; failed field RHS evaluation reverts on both sides. -/
namespace Solidity.Evm.Memory.StructExamples
open Semantics

private def H : HTy := [.struct "Toggle", .struct "Toggle", .array (.prim .uint)]
private def r0 : HRef H (.struct "Toggle") := ⟨0, rfl⟩
private def r1 : HRef H (.struct "Toggle") := ⟨1, rfl⟩
private def a0 : HRef H (.array (.prim .uint)) := ⟨2, rfl⟩
private def u (n : Fin W) : PrimTy.uint.Denote := indexValue n
private def hp : Heap H :=
  ((true, (u (wmod 7), ())), ((false, (u (wmod 9), ())), (⟨[u (wmod 4), u (wmod 5)], by decide⟩, ())))
private def base (i : Nat) : Fin W := if i = 0 then wmod 32 else if i = 1 then wmod 40 else wmod 48
private def machine : Machine :=
  {Machine.init with stack := [w[77]], mem := fun a =>
    if a = 0 then w[64] else if a = 2 then w[99] else if a = 32 then w[1]
    else if a = 33 then w[7] else if a = 41 then w[9] else if a = 48 then w[2]
    else if a = 49 then w[4] else if a = 50 then w[5] else w[0]}

private theorem structRefs {s : Name} (r : HRef H (.struct s)) :
    s = "Toggle" ∧ (HEq r r0 ∨ HEq r r1) := by
  rcases r with ⟨i, hi⟩
  cases i with
  | zero => cases hi; exact ⟨rfl, .inl HEq.rfl⟩
  | succ i =>
    cases i with
    | zero => cases hi; exact ⟨rfl, .inr HEq.rfl⟩
    | succ i =>
      cases i with
      | zero => cases hi
      | succ i => cases hi

private theorem arrayRefs {p : PrimTy} (r : HRef H (.array (.prim p))) :
    p = .uint ∧ HEq r a0 := by
  rcases r with ⟨i, hi⟩
  cases i with
  | zero => cases hi
  | succ i =>
    cases i with
    | zero => cases hi
    | succ i =>
      cases i with
      | zero => cases hi; exact ⟨rfl, HEq.rfl⟩
      | succ i => cases hi

private theorem toggleRepr (r : HRef H (.struct "Toggle")) (b : Fin W)
    (on : Bool) (n : Fin W) (hv : hp.get r = (on, (u n, ())))
    (hs : b.val + 2 ≤ W) (hb : machine.mem b.val = .val (bword on))
    (hn : machine.mem (b.val + 1) = .val n) : StructRepr hp r b machine := by
  refine ⟨hs, ?_⟩
  intro f p hf
  change lookupBy f [("on", Ty.bool), ("n", Ty.uint)] = some (Ty.prim p) at hf
  by_cases ho : f = "on"
  · subst f
    cases hf
    simpa only [Heap.field, MFields.get, hv] using hb
  · by_cases he : f = "n"
    · subst f
      cases hf
      rw [Heap.field, hv]
      change ∃ x : Fin W, machine.mem (b.val + 1) = .val x ∧ (u n).1 = x.val
      exact ⟨n, hn, rfl⟩
    · simp only [lookupBy, ho, he, if_false, reduceCtorEq] at hf

private theorem repr0 : StructRepr hp r0 (base 0) machine :=
  toggleRepr r0 (base 0) true (wmod 7) rfl (by decide +kernel) rfl rfl
private theorem repr1 : StructRepr hp r1 (base 1) machine :=
  toggleRepr r1 (base 1) false (wmod 9) rfl (by decide +kernel) rfl rfl

private theorem arrayRepr : ArrayRepr hp a0 (base 2) machine := by
  constructor
  · simp only [Heap.len, hp, a0, H, Heap.get, Objs.get, MObj.elems_dyn,
      List.length_cons, List.length_nil]
    decide +kernel
  · simp only [Heap.len, hp, a0, H, Heap.get, Objs.get, MObj.elems_dyn,
      List.length_cons, List.length_nil]
    rfl
  · intro i v hv
    simp only [hp, a0, H, Heap.get, Objs.get, MObj.elems_dyn] at hv
    cases i with
    | zero => cases hv; exact ⟨wmod 4, rfl, rfl⟩
    | succ i =>
      cases i with
      | zero => cases hv; exact ⟨wmod 5, rfl, rfl⟩
      | succ i => cases hv

/-- The combined allocator relation has populated, separated source objects. -/
theorem fixture_repr : StructAllocatorRepr hp base 8 (wmod 64) machine := by
  constructor
  · constructor
    · constructor
      · intro p r
        rcases arrayRefs r with ⟨rfl, hr⟩; cases hr; exact arrayRepr
      · intro p r
        rcases arrayRefs r with ⟨rfl, hr⟩; cases hr; decide +kernel
      · intro p q r s hn
        rcases arrayRefs r with ⟨rfl, hr⟩; cases hr
        rcases arrayRefs s with ⟨rfl, hs⟩; cases hs
        exact False.elim (hn rfl)
    · refine ⟨by decide, by decide, rfl, ?_⟩
      intro addr ha
      change 64 ≤ addr at ha
      simp only [machine]
      split <;> rename_i he
      · omega
      · split <;> rename_i he
        · omega
        · split <;> rename_i he
          · omega
          · split <;> rename_i he
            · omega
            · split <;> rename_i he
              · omega
              · split <;> rename_i he
                · omega
                · split <;> rename_i he
                  · omega
                  · split <;> rename_i he
                    · omega
                    · rfl
    · intro p r
      rcases arrayRefs r with ⟨rfl, hr⟩; cases hr; decide +kernel
  · constructor
    · intro s r
      rcases structRefs r with ⟨rfl, hr | hr⟩ <;> cases hr
      · exact repr0
      · exact repr1
    · intro s r
      rcases structRefs r with ⟨rfl, hr | hr⟩ <;> cases hr <;> decide +kernel
    · intro s t r q hn
      rcases structRefs r with ⟨rfl, hr | hr⟩ <;> cases hr <;>
        rcases structRefs q with ⟨rfl, hq | hq⟩ <;> cases hq
      · exact False.elim (hn rfl)
      · exact .inl (by decide +kernel)
      · exact .inr (by decide +kernel)
      · exact False.elim (hn rfl)
  · intro p s a r
    rcases arrayRefs a with ⟨rfl, ha⟩; cases ha
    rcases structRefs r with ⟨rfl, hr | hr⟩ <;> cases hr <;>
      exact .inr (by decide +kernel)
  · intro s r
    rcases structRefs r with ⟨rfl, hr | hr⟩ <;> cases hr <;> decide +kernel

private def writtenHeap := hp.setField r0 (f := "n") rfl (u (wmod 12))
private def writtenMachine := writeMachine machine 33 w[12]

/-- A struct write keeps the other struct, array, cursor and zero tail represented. -/
theorem written_repr : StructAllocatorRepr writtenHeap base 8 (wmod 64) writtenMachine :=
  fixture_repr.setStruct r0 (f := "n") rfl (u (wmod 12)) w[12] ⟨wmod 12, rfl, rfl⟩

/-- Array writes after a struct write preserve both primitive struct objects. -/
theorem array_written_repr :
    StructAllocatorRepr (writtenHeap.set a0 (MObj.setElem .dyn (writtenHeap.get a0) 0 (u (wmod 6))))
      base 8 (wmod 64) (writeMachine writtenMachine 49 w[6]) :=
  written_repr.setArray a0 0 (by decide +kernel) (u (wmod 6)) w[6] ⟨wmod 6, rfl, rfl⟩

private def grownArrayHeap : Heap (H ++ [.array (.prim .uint)]) :=
  (writtenHeap.alloc (defaultArray .uint (wmod 3))).1
private def grownArrayBase : Nat → Fin W := upd base H.length (wmod 64)
private def grownArrayMachine : Machine := allocateMachine writtenMachine (wmod 64) (wmod 3)

/-- A real fresh array preserves both populated structs and the older array. -/
theorem array_allocated_repr :
    StructAllocatorRepr grownArrayHeap grownArrayBase 8 (wmod 68) grownArrayMachine :=
  written_repr.allocateArray .uint (wmod 3) (by decide +kernel)

private def newToggle : MObj (H ++ [.array (.prim .uint)]) (.struct "Toggle") :=
  (false, (u (wmod 0), ()))

private theorem newToggle_defaults : StructDefaults newToggle := by
  intro f p hf
  change lookupBy f [("on", Ty.bool), ("n", Ty.uint)] = some (Ty.prim p) at hf
  by_cases ho : f = "on"
  · subst f; cases hf; rfl
  · by_cases hn : f = "n"
    · subst f; cases hf; rfl
    · simp only [lookupBy, ho, hn, if_false, reduceCtorEq] at hf

private def grownStructHeap : Heap (H ++ [.array (.prim .uint)] ++ [.struct "Toggle"]) :=
  (grownArrayHeap.alloc newToggle).1
private def grownStructBase : Nat → Fin W :=
  upd grownArrayBase (H ++ [RefTy.array (.prim .uint)]).length (wmod 68)
private def grownStructMachine : Machine := allocateStructMachine grownArrayMachine (wmod 68) 2
private def freshToggle : HRef (H ++ [.array (.prim .uint)] ++ [.struct "Toggle"]) (.struct "Toggle") :=
  (grownArrayHeap.alloc newToggle).2

/-- A fresh headerless struct coexists with all older populated objects. -/
theorem struct_allocated_repr :
    StructAllocatorRepr grownStructHeap grownStructBase 8 (wmod 70) grownStructMachine :=
  array_allocated_repr.allocateStruct newToggle newToggle_defaults (by decide +kernel)

/-- The freshly allocated struct is owned, so an immediate field write is safe. -/
theorem allocated_written_repr :
    StructAllocatorRepr (grownStructHeap.setField freshToggle (f := "on") rfl true)
      grownStructBase 8 (wmod 70) (writeMachine grownStructMachine 68 w[1]) :=
  struct_allocated_repr.setStruct freshToggle (f := "on") rfl true w[1] rfl

private def grownStructHeapWritten : Heap (H ++ [.array (.prim .uint)] ++ [.struct "Toggle"]) :=
  grownStructHeap.setField freshToggle (f := "on") rfl true
private def grownStructMachineWritten : Machine := writeMachine grownStructMachine 68 w[1]
private def oldArray : HRef (H ++ [.array (.prim .uint)] ++ [.struct "Toggle"]) (.array (.prim .uint)) :=
  (a0.wk (List.prefix_append H [.array (.prim .uint)])).wk
  (List.prefix_append (H ++ [.array (.prim .uint)]) [.struct "Toggle"])

/-- Older source identities remain usable after both kinds of allocation. -/
theorem allocated_old_array_written_repr :
    StructAllocatorRepr
      (grownStructHeapWritten.set oldArray (MObj.setElem .dyn (grownStructHeapWritten.get oldArray) 0 (u (wmod 6))))
      grownStructBase 8 (wmod 70) (writeMachine grownStructMachineWritten 49 w[6]) :=
  allocated_written_repr.setArray oldArray 0 (by decide +kernel) (u (wmod 6)) w[6]
    ⟨wmod 6, rfl, rfl⟩

/-- Empty array allocation still reserves its header and preserves new structs. -/
theorem repeated_array_allocated_repr :
    StructAllocatorRepr (grownStructHeapWritten.alloc (defaultArray .bool (wmod 0))).1
      (upd grownStructBase (H ++ [RefTy.array (.prim .uint)] ++ [RefTy.struct "Toggle"]).length (wmod 70))
      8 (wmod 71) (allocateMachine grownStructMachineWritten (wmod 70) (wmod 0)) :=
  allocated_written_repr.allocateArray .bool (wmod 0) (by decide +kernel)

private def mixedCode : List Instr :=
  [.push w[3]] ++ allocateArrayCode ++ [.pop] ++ allocateStructCode 2 ++
    [.push w[1], .swap 1] ++ writeFieldCode 0 ++ [.push w[0]] ++ allocateArrayCode ++ [.pop]

private def mixedObserve : Out → Option (List Nat)
  | .ok m _ => do
    let words := m.stack ++ [m.mem 0, m.mem 2, m.mem 32, m.mem 33, m.mem 40, m.mem 41,
      m.mem 48, m.mem 49, m.mem 50, m.mem 64, m.mem 65, m.mem 66, m.mem 67,
      m.mem 68, m.mem 69, m.mem 70, m.mem 71]
    words.mapM fun w => match w with | .val v => some v.val | .slot _ => none
  | _ => none

-- Both layouts share a cursor. Only the array has a length header.
example : mixedObserve (run mixedCode writtenMachine) =
    some [77, 71, 99, 1, 12, 0, 9, 2, 4, 5, 3, 0, 0, 0, 1, 0, 0, 0] := by
  decide +kernel

-- A cursor must remain a nonzero word even when all allocated cells fit.
example : ¬ (wmod (W - 2)).val + (structDef "Toggle").length < W := by decide +kernel

example : (match run (allocateStructCode 2)
    {machine with mem := fun a => if a = 0 then .val (wmod (W - 2)) else w[0]} with
    | .ok m _ => m.mem 0
    | _ => w[1]) = w[0] := by decide +kernel

private def observe : Out → Option (List Nat)
  | .ok m _ => do
    let words := m.stack ++ [m.mem 0, m.mem 2, m.mem 32, m.mem 33,
      m.mem 40, m.mem 41, m.mem 48, m.mem 49, m.mem 50]
    words.mapM fun w => match w with | .val v => some v.val | .slot _ => none
  | _ => none

private def code := [.push w[12], .push (Word.val (base r0.id))] ++ writeFieldCode 1 ++
  [.push (.val (base r0.id))] ++ readFieldCode 1

-- Two aliases use the same base; the Boolean field and separate objects survive.
example : observe (run code machine) = some [12, 77, 64, 99, 1, 12, 0, 9, 2, 4, 5] := by
  decide +kernel

-- No length header is inserted before the first member.
example : observe (run (readFieldCode 0) (machine.push (.val (base r0.id)))) =
    some [1, 77, 64, 99, 1, 7, 0, 9, 2, 4, 5] := by decide +kernel

/-- Placing this nonempty struct at the last word is rejected by the no-wrap bound. -/
theorem wrapping_invalid : ¬ StructRepr hp r0 wMax machine := by
  intro h
  have hs : W - 1 + 2 ≤ W := h.space
  have hw : 0 < W := W_pos
  omega

private def IH : HTy := [.array (.prim .uint), .struct "Packed"]
private def ia : HRef IH (.array (.prim .uint)) := ⟨0, rfl⟩
private def ir : HRef IH (.struct "Packed") := ⟨1, rfl⟩
private def iv : PrimTy.int.Denote := ⟨-7, by decide⟩
private def ihp : Heap IH :=
  (⟨[], by decide⟩, ((u (wmod 0), (iv, (u (wmod 0), (ia, ())))), ()))
private def im : Machine :=
  {Machine.init with mem := fun a => if a = 81 then .val (wmod (W - 7)) else w[0]}

/-- Signed words and surrounding unsigned fields inhabit the struct relation. -/
theorem signed_repr : StructRepr ihp ir (wmod 80) im := by
  refine ⟨by decide +kernel, ?_⟩
  intro f p hf
  change lookupBy f [("a", Ty.uint), ("b", Ty.int), ("c", Ty.uint),
    ("xs", Ty.ref (.array Ty.uint))] = some (Ty.prim p) at hf
  by_cases ha : f = "a"
  · subst f; cases hf
    exact ⟨wmod 0, rfl, rfl⟩
  · by_cases hb : f = "b"
    · subst f; cases hf
      refine ⟨wmod (W - 7), rfl, ?_⟩
      decide +kernel
    · by_cases hc : f = "c"
      · subst f; cases hf
        exact ⟨wmod 0, rfl, rfl⟩
      · simp only [lookupBy, ha, hb, hc, if_false] at hf
        split at hf <;> cases hf

theorem signed_read_correct :
    ValOutT .int (.ok iv) (run (readFieldCode 1) (im.push (.val (wmod 80)))) im :=
  readField_correct signed_repr (f := "b") rfl

private def ZH : HTy := [.struct "Toggle"]
private def zr : HRef ZH (.struct "Toggle") := ⟨0, rfl⟩
private def zhp : Heap ZH := ((false, (u (wmod 0), ())), ())
private def zb : Nat → Fin W := fun _ => wmod 16
private def zm : Machine :=
  {Machine.init with mem := fun a => if a = 0 then w[8] else w[0]}

/-- The older array-only relation does not own this zero-valued struct interval. -/
theorem legacy_allocator : AllocatorRepr zhp zb 2 (wmod 8) zm := by
  have hn {p : PrimTy} (r : HRef ZH (.array (.prim p))) : False := by
    rcases r with ⟨i, hi⟩
    cases i <;> cases hi
  refine ⟨⟨fun r => (hn r).elim, fun r => (hn r).elim, fun r _ _ => (hn r).elim⟩,
    ⟨by decide, by decide, rfl, ?_⟩, fun r => (hn r).elim⟩
  intro addr ha
  change 8 ≤ addr at ha
  simp only [zm]
  split <;> rename_i he
  · omega
  · rfl

/-- The zero-valued source struct also has its actual target member cells. -/
theorem legacy_struct_repr : StructRepr zhp zr (zb 0) zm := by
  refine ⟨by decide +kernel, ?_⟩
  intro f p hf
  change lookupBy f [("on", Ty.bool), ("n", Ty.uint)] = some (Ty.prim p) at hf
  by_cases ho : f = "on"
  · subst f; cases hf; rfl
  · by_cases hn : f = "n"
    · subst f; cases hf; exact ⟨wmod 0, rfl, rfl⟩
    · simp only [lookupBy, ho, hn, if_false, reduceCtorEq] at hf

/-- Its apparent free zero tail cannot safely support a live struct write. -/
theorem legacy_write_breaks_allocator :
    ¬ AllocatorRepr (zhp.setField zr (f := "on") rfl true) zb 2 (wmod 8)
      (writeMachine zm 16 w[1]) := by
  intro h
  have he : w[1] = w[0] := h.free.zero 16 (by decide +kernel)
  have hn : w[1] ≠ w[0] := by decide +kernel
  exact hn he

/-- The stronger relation rejects the same misplaced live struct. -/
theorem misplaced_invalid : ¬ StructAllocatorRepr zhp zb 2 (wmod 8) zm := by
  intro h
  have hl : 16 + 2 ≤ 8 := h.live zr
  omega

namespace Public

private def C : Contract := contract!{ }
private def Γ : Ctx := [.val .uint, .mem (.array (.prim .uint)),
  .mem (.struct "Toggle"), .mem (.struct "Toggle"), .mem (.struct "Toggle")]
private def state : State C Γ :=
  {storage := Storage.init C, H := H, heap := hp,
    env := (u (wmod 0), some a0, some r1, some r0, some r0, ())}
private def target : Machine :=
  writeMachine (writeMachine (writeMachine (writeMachine (writeMachine machine 7 w[99])
    1 w[32]) 2 w[32]) 3 w[40]) 4 w[48]

private theorem allocator : StructAllocatorRepr hp base 8 (wmod 64) target :=
  ((((fixture_repr.localWrite 7 (by decide) (by decide) w[99]).localWrite
    1 (by decide) (by decide) w[32]).localWrite 2 (by decide) (by decide) w[32]).localWrite
    3 (by decide) (by decide) w[40]).localWrite 4 (by decide) (by decide) w[48]

/-- The public compiler's stronger input is inhabited by aliases and distinct structs. -/
theorem fixture : StateRepr 1 1 8 (Frag.init Γ) state base target := by
  have hc := Sim.init C 0 W_pos (fun _ => 0) ⟨0, W_pos⟩ rfl
  refine ⟨?_, allocator.arrays.heap, ?_, by decide, allocator.structs, allocator.separated, ?_⟩
  · refine ⟨hc.store, ?_, ?_, hc.net, hc.netSelf, hc.bound, ?_, hc.env, hc.funds, hc.oracle⟩
    · intro p i
      cases i with
      | here => exact ⟨wmod 0, rfl, rfl⟩
      | there i => cases i with | there i => cases i with | there i => cases i with
        | there i => cases i with | there i => nomatch i
    · intro R i
      cases i with | there i => cases i with | there i => cases i with
        | there i => cases i with | there i => cases i with | there i => nomatch i
    · intro R i
      cases i with | there i => cases i with | there i => cases i with
        | there i => cases i with | there i => cases i with | there i => nomatch i
  · intro R i
    cases i with
    | there i => cases i with
      | here => exact ⟨a0, rfl, rfl⟩
      | there i => cases i with
        | here => exact ⟨r1, rfl, rfl⟩
        | there i => cases i with
          | here => exact ⟨r0, rfl, rfl⟩
          | there i => cases i with
            | here => exact ⟨r0, rfl, rfl⟩
            | there i => nomatch i
  · intro s f R r hf
    obtain ⟨rfl, _⟩ := structRefs r
    exact (primitiveMembers_noRef (by decide) hf).elim

private def Δ : Ctx := .mem (.struct "Toggle") :: Γ
private def tmp : Idx Δ (.mem (.struct "Toggle")) := .here
private def oldAlias : Idx Δ (.mem (.struct "Toggle")) := .there (.there (.there (.there (.there .here))))
private def other : Idx Δ (.mem (.struct "Toggle")) := .there (.there (.there .here))
private def xs : Idx Δ (.mem (.array (.prim .uint))) := .there (.there .here)
private def fieldN (i : Idx Δ (.mem (.struct "Toggle"))) : Val C Δ .uint :=
  .readMem (.field (.var i rfl) "n" rfl)
private def lit (n : Int) (hn : PrimTy.uint.inRange n = true) : Val C Δ .uint := .simple (.lit n hn)
private def body : Prog C Γ Δ :=
  .cons (.declMem (.struct "Toggle") (.user "tmp")
    (some (.alias (.var (.there (.there (.there .here))) rfl))) rfl rfl)
  (.cons (.assignMem (.field (.var tmp rfl) "n" rfl)
    (.val (.binop .add rfl rfl (fieldN oldAlias)
      (.readMem (.index .dyn (.var xs rfl) (lit 0 rfl))))))
  (.cons (.assignMem (.field (.var tmp rfl) "on" rfl) (.val (.simple (.bool false))))
  (.cons (.assignMem (.index .dyn (.var xs rfl) (lit 1 rfl)) (.val (fieldN tmp)))
  (.cons (.rebindMem tmp (.alias (.var other rfl)))
  (.cons (.assignMem (.field (.var tmp rfl) "n" rfl) (.val (lit 22 rfl)))
  (.cons (.assignLocal (.there .here) (fieldN oldAlias)) .nil))))))

private def program : Prog C Γ (.mem (.array (.prim .bool)) :: Γ) :=
  .cons (.block body)
    (.cons (.declMem (.array (.prim .bool)) (.user "fresh")
      (some (.newArr (.lit 1 rfl) rfl)) rfl rfl) .nil)
private def compiled : Compiler.Compilation 1 (Frag.init Γ) program :=
  (Compiler.compile 1 (Frag.init Γ) program).get (by decide +kernel)

attribute [irreducible] compiled

/-- Struct fields, aliases, scopes and subsequent array allocation share one compiler. -/
theorem compiled_input : compiled.Input 1 8 base state target := by
  apply (compiled.memory_input (by decide +kernel) 1 8 base state target).mpr
  exact ⟨fixture, by decide +kernel, .inr ⟨by decide, wmod 64, allocator, by decide +kernel⟩⟩

theorem compiled_agrees : compiled.Agrees 1 8 base state target := compiled.correct compiled_input

private def observeTarget : Out → Option (List Nat)
  | .ok m _ => do
    let words := m.stack ++ [m.mem 0, m.mem 1, m.mem 2, m.mem 3, m.mem 4, m.mem 5,
      m.mem 6, m.mem 7, m.mem 32, m.mem 33, m.mem 40, m.mem 41, m.mem 48,
      m.mem 49, m.mem 50, m.mem 64, m.mem 65]
    words.mapM fun w => match w with | .val v => some v.val | .slot _ => none
  | _ => none

example : observeTarget (run compiled.code target) =
    some [77, 66, 32, 32, 40, 48, 11, 64, 99, 0, 11, 0, 22, 2, 4, 11, 1, 0] := by
  decide +kernel

private def observeSource : TRes (Solidity.Out C H (.mem (.array (.prim .bool)) :: Γ)) → Option (List Int)
  | .ok o => do
    let a ← o.st.heap.index (a0.wk o.ext) .dyn (u (wmod 1))
    let flag : Bool := o.st.heap.field (T := .prim .bool) (r0.wk o.ext) (f := "on") rfl
    some [(TEnv.get (.there .here) o.st.env).1,
      (o.st.heap.field (r0.wk o.ext) (f := "n") rfl).1,
      (o.st.heap.field (r1.wk o.ext) (f := "n") rfl).1, a.1,
      if flag then 1 else 0]
  | .error _ => none

example : observeSource (program.run state) = some [11, 11, 22, 11, 0] := by decide +kernel

private def bad : Prog C Γ Γ :=
  .cons (.assignMem (.field (.var (.there (.there (.there .here))) rfl) "n" rfl)
    (.val (.binop .div rfl rfl (.simple (.lit 5 rfl)) (.simple (.lit 0 rfl))))) .nil
private def compiledBad : Compiler.Compilation 1 (Frag.init Γ) bad :=
  (Compiler.compile 1 (Frag.init Γ) bad).get (by decide +kernel)

theorem bad_input : compiledBad.Input 1 8 base state target := by
  apply (compiledBad.memory_input rfl 1 8 base state target).mpr
  exact ⟨fixture, by decide +kernel, .inl rfl⟩

theorem bad_agrees : compiledBad.Agrees 1 8 base state target := compiledBad.correct bad_input

example : bad.run state = .error .revert ∧ run compiledBad.code target = .revert := by
  constructor
  · rfl
  · exact Out.eq_revert (by decide +kernel)

end Public
end Solidity.Evm.Memory.StructExamples
