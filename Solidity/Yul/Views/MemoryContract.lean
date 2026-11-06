import Solidity.Yul.Views.Regions
import Solidity.Source.WellTyped

/-!
# Allocation/refinement and actual V04b memory obligations (G01 extension)

Logical heap identities are unchanged. A placement assigns nondeterministic
valid physical addresses to those identities. This is an extension interface,
not a claim that the existing deterministic source allocator implements YQ3.
The complete final compiler theorem must quantify over valid placements and
show refinement for the target's selected placement, with exact observations.
-/
namespace Solidity.Yul.Views

/-- Solidity memory object layout: bytes/string payloads are packed; ordinary
 arrays and structs use words, with a length header only for dynamic arrays. -/
inductive MemoryShape where
  | bytes (length : Nat)
  | array (dynamic : Bool) (length : Nat)
  | strct (fields : Nat)
  deriving DecidableEq, Repr

def MemoryShape.size : MemoryShape → Nat
  | .bytes n => 32 + ((n + 31) / 32) * 32
  | .array dynamic n => (if dynamic then 32 else 0) + n * 32
  | .strct n => n * 32

/-- The shape is an obligation against actual typed heap contents. Nested
 reference members are pointer words, not inline recursive object copies. -/
inductive HasMemoryShape {D : Source.Layout} : {τ : Source.STy} → Source.Data D τ → MemoryShape → Prop where
  | bytes {l} (bs : List UInt8) : HasMemoryShape (.bytes (l := l) bs) (.bytes bs.length)
  | string {l} (bs : List UInt8) : HasMemoryShape (.string (l := l) bs) (.bytes bs.length)
  | array {l τ n} (len : Nat) (hl : ∀ m, n = some m → m = len)
      (xs : Fin len → Source.Data D τ) :
      HasMemoryShape (.array (l := l) len hl xs) (.array n.isNone len)
  | strct {l d} (fs : Source.DataList D (D.fields d)) :
      HasMemoryShape (.struct (l := l) fs) (.strct (D.fields d).length)

/-- Scratch bytes [0,64), free pointer word [64,96), zero word [96,128).
No promise is made about arbitrary bytes after the free pointer. -/
def ReservedOK (m : ByteView) (free : Roadmap.Word) : Prop :=
  mloadNat m 64 = free.val ∧ ∀ i : Fin 32, m (96 + i.val) = 0

/-- Ordinary allocated objects, independently of allocation order. Solidity
requires no address alignment (pinned assembly.rst). Default empty references
may instead use shared zero slot 0x60; that separate representation obligation
is not modeled by this ordinary-allocation placement. -/
structure Placement {D : Source.Layout} (h : Source.Heap D) where
  address : Nat → Nat
  shape : Nat → MemoryShape
  free : Roadmap.Word
  free_start : 128 ≤ free.val
  distinct : ∀ a b, (h.cells a).isSome → (h.cells b).isSome → address a = address b → a = b
  typed : ∀ a τ d, h.cells a = some ⟨τ, d⟩ → HasMemoryShape d (shape a)
  starts : ∀ a, (h.cells a).isSome → 128 ≤ address a
  ends : ∀ a, (h.cells a).isSome → address a + (shape a).size ≤ free.val
  separate : ∀ a b, (h.cells a).isSome → (h.cells b).isSome → a ≠ b →
    address a + (shape a).size ≤ address b ∨ address b + (shape b).size ≤ address a

/-- The explicit target-to-source allocation refinement contract. `run` must
be instantiated by the integrated source semantics; exact observations are O.
This does not amend the existing G01 theorem by weakening observations. -/
def AllocationRefines {D : Source.Layout} {O : Type} (h : Source.Heap D)
    (run : Placement h → O → Prop) (target : O → Prop) : Prop :=
  ∀ o, target o → ∃ p : Placement h, run p o

/-- Actual V04b preservation obligation, deliberately not discharged by a
replacement predicate named MemOK. It covers all initial heap typings. -/
def PreservesMemOK (E : Source.Env) {Γ : Source.RCtx}
    (step : Source.EMState E Γ → Source.EMState E Γ → Prop) : Prop :=
  ∀ H before after, Source.MemOK E H before → step before after → Source.MemOK E H after

/-- Preservation sub-obligations only, not the full V11 layout agreement.
Placement/reserved-word and typed logical-read agreement are separate inputs.
An implementation must provide
its relation and prove this exact contract before a memory-safe step is admitted. -/
structure MemoryWritebackObligations (E : Source.Env) (Γ : Source.RCtx) where
  view : Source.EMState E Γ → ByteView → Prop
  realize : ∀ H s, Source.MemOK E H s → ∃ m, view s m
  writeback : ByteView → Source.EMState E Γ → Source.EMState E Γ → Prop
  unchanged_exists : ∀ s m, view s m → writeback m s s
  unchanged : ∀ s m s', view s m → writeback m s s' → s' = s
  safe : ByteView → ByteView → Prop
  preserves : ∀ m m' H s s', view s m → safe m m' →
    Source.MemOK E H s → writeback m' s s' → Source.MemOK E H s'

end Solidity.Yul.Views
