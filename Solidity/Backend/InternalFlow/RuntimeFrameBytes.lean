import Solidity.Backend.InternalFlow.RuntimeFrameRestore
import Solidity.Backend.MemoryOps.PhysicalByteJournal

/-! P6-backed numeric caller-cell restoration. The INITIAL byte image and
physical W-fit are explicit or derived; symbolic slots are never encoded by
assertion. This store-stage bridge does not lower dynamic loads/arithmetic or
supply source/world rollback. Both executions use the existing machines. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.Bytes
open Evm Evm.Memory
variable {C : Contract}

def offset (cell : Fin W) (fits : 32*cell.val+32≤2^256) : Environment.W256 :=
 ⟨32*cell.val,by omega⟩

/-- Exact existing byte instructions for temporary store and recovered store.
The recovered word is already on the real caller stack, not injected by code. -/
def code (cell : Fin W) (fits : 32*cell.val+32≤2^256) (temporary : Fin W) : Backend.Program :=
 [Environment.push256 temporary,Environment.push256 (offset cell fits),.op .MSTORE,
  Environment.push256 (offset cell fits),.op .MSTORE]

def afterBytes (bytes : Environment.Memory) (cell temporary saved : Fin W) : Environment.Memory :=
 Environment.writeBytes (Environment.writeBytes bytes (32*cell.val) (Semantics.wordBytes temporary.val))
   (32*cell.val) (Semantics.wordBytes saved.val)

theorem byte_run (bytes : Environment.Memory) (cell temporary saved : Fin W)
 (fits : 32*cell.val+32≤2^256) (tail : List Environment.Word) :
 Environment.runCrypto (code cell fits temporary) ⟨lenU saved.val saved.isLt :: tail,bytes⟩ =
   some ⟨tail,afterBytes bytes cell temporary saved⟩ := by
 simp only [code,Environment.push256,Environment.runCrypto,Environment.cryptoStep_constant,Option.bind_some]
 simp only [Environment.cryptoStep,lenU,Int.toNat_natCast,Option.bind_some,afterBytes,offset]

theorem clobber_run (bytes : Environment.Memory) (cell temporary saved : Fin W)
 (fits : 32*cell.val+32≤2^256) (tail : List Environment.Word) :
 Environment.runCrypto (code cell fits temporary |>.take 3)
   ⟨lenU saved.val saved.isLt :: tail,bytes⟩ =
 some ⟨lenU saved.val saved.isLt :: tail,
   Environment.writeBytes bytes (32*cell.val) (Semantics.wordBytes temporary.val)⟩ := by
 simp only [code,List.take,Environment.push256,Environment.runCrypto,
   Environment.cryptoStep_constant,Option.bind_some]
 simp only [Environment.cryptoStep,lenU,Int.toNat_natCast,Option.bind_some,offset]

theorem write_self (m : Machine) (cell : Nat) (word : Word) (same : m.mem cell = word) :
 writeMachine m cell word = m := by
 have memory : upd m.mem cell word = m.mem := by
  funext x
  by_cases equal : x = cell
  · subst x
    simp only [upd,↓reduceIte,same]
  · simp only [upd,if_neg equal]
 change {m with mem := upd m.mem cell word} = m
 rw [memory]

/-- Construct an INITIAL sparse physical image from an actual numeric machine
read. This is not a global machine/heap representation or capacity-to-W cast. -/
theorem initial_cell (m : Machine) (background : Environment.Memory) (cell saved : Fin W)
 (same : m.mem cell.val = .val saved) (fits : 32*cell.val+32≤2^256) :
 MemoryOps.Physical.WordFrame m (Environment.writeBytes background (32*cell.val) (Semantics.wordBytes saved.val))
   (fun c => c=cell.val) := by
 have actual := MemoryOps.Physical.cell_write_same m background cell.val saved
 rw [write_self m cell.val (.val saved) same] at actual
 constructor
 · intro c hc
   subst c
   exact fits
 · intro c hc
   subst c
   exact actual

/-- The actual word clobber/recovery and physical byte store sequence share
ONE initial frame, destination, recovered value and reached image. -/
theorem consume_frame {m : Machine} {bytes : Environment.Memory} {live : Nat → Prop}
 (frame : MemoryOps.Physical.WordFrame m bytes live) (cell temporary saved : Fin W)
 (selected : live cell.val) (tail : List Word) (byteTail : List Environment.Word)
 (top : m.stack = .val saved :: tail) (same : m.mem cell.val = .val saved) :
 Evm.run (Restore.consumeCode cell.val (.val temporary)) m = .ok {m with stack := tail} 0 ∧
 Environment.runCrypto (code cell (frame.fits cell.val selected) temporary)
   ⟨lenU saved.val saved.isLt :: byteTail,bytes⟩ =
     some ⟨byteTail,afterBytes bytes cell temporary saved⟩ ∧
 MemoryOps.Physical.WordFrame {m with stack := tail} (afterBytes bytes cell temporary saved) live ∧
 Environment.readMemory (afterBytes bytes cell temporary saved) (32*cell.val) 32 =
   Semantics.wordBytes saved.val := by
 have first := frame.write cell.val temporary (frame.fits cell.val selected)
 have second := first.write cell.val saved (frame.fits cell.val selected)
 have memory : writeMachine (writeMachine m cell.val (.val temporary)) cell.val (.val saved) = m := by
  change {m with mem := upd (upd m.mem cell.val (.val temporary)) cell.val (.val saved)} = m
  have eq : upd (upd m.mem cell.val (.val temporary)) cell.val (.val saved) = m.mem := by
   funext x
   by_cases equal : x=cell.val
   · subst x
     simp only [upd,↓reduceIte,same]
   · simp only [upd,if_neg equal]
  rw [eq]
 rw [memory] at second
 refine ⟨Restore.consume_run m cell.val (.val temporary) (.val saved) tail top same,
   byte_run bytes cell temporary saved _ byteTail,?_,?_⟩
 · constructor
   · intro c hc
     exact frame.fits c hc
   · intro c hc
     exact second.cells c (.inl (.inl hc))
 · simpa only [afterBytes,MemoryOps.Physical.word_bytes_length] using
     Environment.read_written (Semantics.wordBytes saved.val) (32*cell.val)
       (Environment.writeBytes bytes (32*cell.val) (Semantics.wordBytes temporary.val))

/-- Full typed scalar recovery: the saved-word equality is DERIVED from real
source value representation, while physical bounds come from INITIAL frame. -/
theorem scalar {L b frame : Nat} {Γ : Ctx} {F : Frag Γ}
 {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
 (repr : StateRepr L b frame F σ base m) (index : Idx Γ (.val .uint))
 (cell temporary saved : Fin W) (physical : cell.val=cellOf b index)
 (bytes : Environment.Memory) (live : Nat → Prop) (image : MemoryOps.Physical.WordFrame m bytes live)
 (selected : live cell.val) (tail : List Word) (byteTail : List Environment.Word)
 (top : m.stack = .val saved :: tail)
 (captured : ReprV .uint (TEnv.get index σ.env) (.val saved)) :
 Evm.run (Restore.consumeCode cell.val (.val temporary)) m = .ok {m with stack := tail} 0 ∧
 StateRepr L b frame F σ base {m with stack := tail} ∧
 Environment.runCrypto (code cell (image.fits cell.val selected) temporary)
   ⟨lenU saved.val saved.isLt :: byteTail,bytes⟩ =
     some ⟨byteTail,afterBytes bytes cell temporary saved⟩ ∧
 MemoryOps.Physical.WordFrame {m with stack := tail} (afterBytes bytes cell temporary saved) live := by
 have same : m.mem cell.val = .val saved := by
  rw [physical]
  exact Restore.uint_unique (repr.core.vals index) captured
 obtain ⟨wordRun,byteRun,reached,_⟩ := consume_frame image cell temporary saved selected tail byteTail top same
 exact ⟨wordRun,repr.stack tail,byteRun,reached⟩

/-- Actual live REVERT observes the complete recovered numeric word AFTER
both stores, before any separately supplied local/world checkpoint. -/
theorem revert_saved (bytes : Environment.Memory) (cell temporary saved : Fin W)
 (fits : 32*cell.val+32≤2^256) (tail : List Roadmap.Word) (suffix : Backend.Program) :
 Backend.Failure.Slice.run (.op .REVERT :: suffix)
   ⟨(⟨32*cell.val,by change 32*cell.val<2^256;omega⟩ : Roadmap.Word)::
    (⟨32,by decide⟩ : Roadmap.Word)::tail,afterBytes bytes cell temporary saved⟩ =
 some (⟨tail,afterBytes bytes cell temporary saved⟩,
   some (.revert (Semantics.wordBytes saved.val))) :=
 MemoryOps.Physical.revert_written_word _ cell saved fits tail suffix

/-- An actual symbolic slot word is outside this numeric byte boundary.
This is representation rejection, not a source or runtime failure verdict. -/
theorem symbolic_refusal {m : Machine} {bytes : Environment.Memory} {live : Nat → Prop}
 (cell : Nat) (selected : live cell) (slot : Slot) (actual : m.mem cell = .slot slot) :
 ¬ MemoryOps.Physical.WordFrame m bytes live := by
 intro frame
 obtain ⟨word,numeric,image⟩ := frame.cells cell selected
 rw [actual] at numeric
 cases numeric

end Solidity.Backend.InternalFlow.RuntimeFrame.Bytes
