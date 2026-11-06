import Solidity.Yul.Views.MemoryContract
import Solidity.Yul.Views.WordMemory

/-!
# Explicit V11 logical-read agreement obligations

Read relations are over actual typed source Data and DataList.nth, not an
alternative memory state. They describe the ordinary allocated-object case.
Shared zero-slot empty references, dirty bits, functions and full source-run
composition remain separate obligations. Nothing here instantiates a compiler.
-/
namespace Solidity.Yul.Views

/-- Canonical scalar and memory-reference element words. -/
inductive ElementWord {D : Source.Layout} (address : Nat → Nat) :
    {τ : Source.STy} → Source.Val D τ → Roadmap.Word → Prop where
  | scalar {τ} (v : Source.Val D τ) (w : Roadmap.Word) (read : v.word = some w) :
      ElementWord address v w
  | reference {τ : Source.STy} (h : τ.loc? = some .memory) (a : Nat) (ha : address a < 2 ^ 256) :
      ElementWord address (.memRef h a) ⟨address a, ha⟩

/-- Actual documented word reads from a typed object: dynamic headers,
word-per-member structs, word-per-element arrays and pointer words. -/
inductive ObjectWord {D : Source.Layout} (address : Nat → Nat) :
    {τ : Source.STy} → Source.Data D τ → Nat → Roadmap.Word → Prop where
  | value {τ} (v : Source.Val D τ) (w : Roadmap.Word) (read : ElementWord address v w) :
      ObjectWord address (.val v) 0 w
  | bytesLength {l} (bs : List UInt8) (h : bs.length < 2 ^ 256) :
      ObjectWord address (.bytes (l := l) bs) 0 ⟨bs.length, h⟩
  | stringLength {l} (bs : List UInt8) (h : bs.length < 2 ^ 256) :
      ObjectWord address (.string (l := l) bs) 0 ⟨bs.length, h⟩
  | arrayLength {l τ} (len : Nat) (h : len < 2 ^ 256)
      (hl : ∀ m, (none : Option Nat) = some m → m = len) (xs : Fin len → Source.Data D τ) :
      ObjectWord address (.array (l := l) len hl xs) 0 ⟨len, h⟩
  | arrayElement {l τ n} (len : Nat) (hl : ∀ m, n = some m → m = len)
      (xs : Fin len → Source.Data D τ) (i : Fin len) (v : Source.Val D τ) (w : Roadmap.Word)
      (found : xs i = .val v) (read : ElementWord address v w) :
      ObjectWord address (.array (l := l) len hl xs) ((if n.isNone then 32 else 0) + i.val * 32) w
  | structMember {l d τ} (fs : Source.DataList D (D.fields d)) (i : Nat)
      (v : Source.Val D τ) (w : Roadmap.Word)
      (found : fs.nth i τ = .ok (.val v)) (read : ElementWord address v w) :
      ObjectWord address (.struct (l := l) fs) (i * 32) w

/-- Byte/string contents are packed after their length word. -/
inductive ObjectByte {D : Source.Layout} : {τ : Source.STy} → Source.Data D τ → Nat → UInt8 → Prop where
  | bytes {l} (bs : List UInt8) (i : Fin bs.length) :
      ObjectByte (.bytes (l := l) bs) (32 + i.val) bs[i.val]
  | string {l} (bs : List UInt8) (i : Fin bs.length) :
      ObjectByte (.string (l := l) bs) (32 + i.val) bs[i.val]

/-- Full read-side input obligations for the ordinary-object view, separate
from MemoryWritebackObligations. A future instance must supply the proofs. -/
structure MemoryLayoutObligations (E : Source.Env) (Γ : Source.RCtx) where
  view : (s : Source.EMState E Γ) → Placement s.2.heap → ByteView → Prop
  realize : ∀ H s (p : Placement s.2.heap), Source.MemOK E H s → ∃ m, view s p m
  reserved : ∀ s p m, view s p m → ReservedOK m p.free
  word_read : ∀ s p m a τ (d : Source.Data E.layout τ) off w,
    view s p m → s.2.heap.get a = some ⟨τ, d⟩ →
    ObjectWord p.address d off w → mload m (p.address a + off) = w
  byte_read : ∀ s p m a τ (d : Source.Data E.layout τ) off b,
    view s p m → s.2.heap.get a = some ⟨τ, d⟩ →
    ObjectByte d off b → m (p.address a + off) = b

end Solidity.Yul.Views
