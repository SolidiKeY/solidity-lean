/-!
# ABI entry decoding: solc's generated decoder, eager and lazy

The external-entry decoder of ABI coder v2 as pinned solc 0.8.38 generates
it (`abi_decode_tuple_*`, `abi_decode_*_memory_ptr`, `abi_decode_*_calldata_ptr`,
`access_calldata_tail_*`, `validator_revert_*`; identical in the legacy and
via-IR pipelines, with and without the optimizer — `scripts/abi-entry-probe.mjs`).
Positions are absolute calldata positions; the arguments start at `head = 4`,
after the selector, and a load past the end reads zero bytes.

* **Memory parameters** (`mdec`) are decoded eagerly at entry: every offset is
  unsigned and at most `2^64 - 1`, every length is allocated *before* its
  bounds check (`Panic(0x41)` when an allocation can exceed `2^64 - 1`), and
  every word element is validated.
* **Calldata parameters** get only their entry checks (`cref`): the head
  offset, the length word and the element region of the outermost object.
  Elements are validated when accessed (`cval`, `ctail`): a dynamic element's
  relative offset is a *signed* word added modulo `2^256`, and a word element
  is validated when it is read.

`mdec_cval` is the agreement theorem: whatever the eager decoder accepts, the
lazy access of the same bytes accepts with the same typed value, so a body run
on the eagerly decoded value observes what solc's lazy reads observe.
`entry` runs exactly the checks solc runs before a body; `verdict` classifies
an input as a certified empty revert, a value to run the body on, or a named
refusal. Values are typed by their shape (`Val`); there is no untyped layer.
Design and evidence: `docs/feature-work/abi-hashes.md`, "Entry decoding:
lazy and noncanonical layouts".
-/

namespace Solidity.AbiEntry

/-- `2^256`, the word modulus, as a literal (arithmetic decision procedures
read it). -/
def W : Nat := 115792089237316195423570985008687907853269984665640564039457584007913129639936
/-- `2^255`: the least negative signed word. -/
def H : Nat := 57896044618658097711785492504343953926634992332820282019728792003956564819968
/-- `0xffffffffffffffff`, the bound solc puts on offsets, lengths and memory. -/
def lim : Nat := 18446744073709551615

theorem W_eq : W = 2 ^ 256 := by decide
theorem H_eq : H = 2 ^ 255 := by decide

/-- Word kinds after ABI erasure: `address` is `uint 160`, an enum its
`uint8`, `bytesN` left-aligned. -/
inductive Kind where
  | uint (bits : Nat)
  | int (bits : Nat)
  | bool
  | fixedBytes (n : Nat)
  deriving DecidableEq, Repr

/-- `validator_revert_t_*`: the loaded word equals its cleanup. -/
def Kind.valid : Kind → Nat → Bool
  | .uint b, w => decide (w < 2 ^ b)
  | .int b, w => decide (w < 2 ^ (b - 1)) || decide (W - 2 ^ (b - 1) ≤ w)
  | .bool, w => decide (w < 2)
  | .fixedBytes n, w => w % 2 ^ (256 - 8 * n) == 0

/-- A validated word of its kind. -/
structure Word (k : Kind) where
  val : Nat
  lt : val < W
  valid : k.valid val = true

/-- Nonrecursive ABI types. -/
inductive Shape where
  | word (k : Kind)
  | bytes
  | array (e : Shape)
  | fixed (e : Shape) (n : Nat)
  | tuple (ms : List Shape)
  deriving Repr, Inhabited

mutual
/-- solc's dynamically encoded types. -/
def Shape.dynamic : Shape → Bool
  | .word _ => false
  | .bytes => true
  | .array _ => true
  | .fixed e _ => e.dynamic
  | .tuple ms => Shape.anyDynamic ms
def Shape.anyDynamic : List Shape → Bool
  | [] => false
  | s :: ss => s.dynamic || Shape.anyDynamic ss
end

mutual
/-- The bytes a value takes in its enclosing head (an offset if dynamic). -/
def Shape.headSize : Shape → Nat
  | .word _ => 32
  | .bytes => 32
  | .array _ => 32
  | .fixed e n => if e.dynamic then 32 else n * e.headSize
  | .tuple ms => if Shape.anyDynamic ms then 32 else Shape.headsSize ms
def Shape.headsSize : List Shape → Nat
  | [] => 0
  | s :: ss => s.headSize + Shape.headsSize ss
end

/-- `access_calldata_tail`'s needed length: a length word for an array, the
head otherwise. -/
def Shape.tailSize : Shape → Nat
  | .fixed e n => n * e.headSize
  | .tuple ms => Shape.headsSize ms
  | _ => 32

/-- `bytes` and dynamic arrays: a length word, then the elements. -/
def Shape.lengthPrefixed : Shape → Bool
  | .bytes => true
  | .array _ => true
  | _ => false

/-- Bytes per element in a calldata sequence. -/
def Shape.stride : Shape → Nat
  | .bytes => 1
  | .array e => e.headSize
  | _ => 0

mutual
/-- A decoded value of its shape. -/
inductive Val : Shape → Type
  | word {k : Kind} (w : Word k) : Val (.word k)
  | bytes (bs : List UInt8) : Val .bytes
  | array {e : Shape} {n : Nat} (xs : Seq e n) : Val (.array e)
  | fixed {e : Shape} {n : Nat} (xs : Seq e n) : Val (.fixed e n)
  | tuple {ms : List Shape} (vs : Vals ms) : Val (.tuple ms)
/-- Exactly `n` values of one shape. -/
inductive Seq : Shape → Nat → Type
  | nil {e : Shape} : Seq e 0
  | cons {e : Shape} {n : Nat} (v : Val e) (vs : Seq e n) : Seq e (n + 1)
/-- One value per member shape. -/
inductive Vals : List Shape → Type
  | nil : Vals []
  | cons {s : Shape} {ss : List Shape} (v : Val s) (vs : Vals ss) : Vals (s :: ss)
end

/-! ### Calldata words -/

/-- A calldata byte; zero past the end, as `calldataload`/`calldatacopy`. -/
def byteAt (d : List UInt8) (a : Nat) : UInt8 := d[a]?.getD 0

/-- `calldataload(a)`. -/
def load (d : List UInt8) (a : Nat) : Nat :=
  ((List.range 32).foldl (fun acc i => acc * 256 + (byteAt d (a + i)).toNat) 0) % W

theorem load_lt (d : List UInt8) (a : Nat) : load d a < W :=
  Nat.mod_lt _ (by decide)

/-- `n` bytes from `a`. -/
def bytesAt (d : List UInt8) (a n : Nat) : List UInt8 :=
  (List.range n).map fun i => byteAt d (a + i)

/-- An address modulo `2^256`. -/
def wrap (a : Nat) : Nat := a % W

/-- EVM `sub`. -/
def sub (a b : Nat) : Nat := (a + (W - b % W)) % W

/-- A word read as a signed integer. -/
def toInt (w : Nat) : Int := if w < H then (w : Int) else (w : Int) - (W : Int)

/-- EVM `slt`. -/
def slt (a b : Nat) : Bool := decide (toInt a < toInt b)

/-- `access_calldata_tail`'s offset check:
`slt(rel, sub(sub(calldatasize(), base), sub(tail, 1)))`. -/
def tailFits (size base rel tail : Nat) : Bool := slt rel (sub (sub size base) (sub tail 1))

/-- `access_calldata_tail`'s region check for `len` elements of `stride`
bytes after the length word at `addr`: not
`sgt(add(addr, 32), sub(calldatasize(), mul(len, stride)))`. -/
def regionFits (size addr len stride : Nat) : Bool :=
  !slt (sub size (wrap (len * stride))) (wrap (addr + 32))

/-- Decoder failures. `revert` is `revert(0, 0)`: empty data. `panic` is a
possible `Panic(0x41)` allocation failure; its production is outside this
model, so it is never certified. `fuel` is exhausted recursion. -/
inductive Fail where
  | revert
  | panic
  | fuel
  deriving DecidableEq, Repr

/-- Calldata (selector included) and an upper bound on the free memory
pointer when the decoder starts. -/
structure Input where
  data : List UInt8
  free : Nat

def Input.size (I : Input) : Nat := I.data.length

/-- `round_up_to_mul_of_32`. -/
def roundUp (n : Nat) : Nat := (n + 31) / 32 * 32

/-- `finalize_allocation` after `a` bytes: refuse unless the new free pointer
stays at most `2^64 - 1` from every start below `I.free`. -/
def alloc (I : Input) (a size : Nat) : Except Fail Nat :=
  if I.free + (a + roundUp size) ≤ lim then .ok (a + roundUp size) else .error .panic

/-! ### Memory parameters: eager decoding -/

mutual
/-- `abi_decode_t_<s>_memory_ptr(p, end)` with `a` bytes allocated so far:
the value and the bytes allocated after it. A word is read in place
(`abi_decode_t_<k>`); its caller has checked its bounds. -/
def mdec (I : Input) : Nat → (s : Shape) → Nat → Nat → Except Fail (Val s × Nat)
  | 0, _, _, _ => .error .fuel
  | _ + 1, .word k, p, a =>
    if h : k.valid (load I.data p) = true then
      .ok (.word ⟨load I.data p, load_lt _ _, h⟩, a)
    else .error .revert
  | _ + 1, .bytes, p, a =>
    if p + 31 < I.size then
      if lim < load I.data p then .error .panic else
      match alloc I a (roundUp (load I.data p) + 32) with
      | .error x => .error x
      | .ok a' =>
        if I.size < p + 32 + load I.data p then .error .revert
        else .ok (.bytes (bytesAt I.data (p + 32) (load I.data p)), a')
    else .error .revert
  | f + 1, .array e, p, a =>
    if p + 31 < I.size then
      if lim < load I.data p then .error .panic else
      match alloc I a (load I.data p * 32 + 32) with
      | .error x => .error x
      | .ok a' =>
        if I.size < p + 32 + load I.data p * e.headSize then .error .revert
        else match mseq I f e (p + 32) 0 (load I.data p) a' with
          | .ok (xs, a'') => .ok (.array xs, a'')
          | .error x => .error x
    else .error .revert
  | f + 1, .fixed e n, p, a =>
    if p + 31 < I.size then
      if lim < n then .error .panic else
      match alloc I a (n * 32) with
      | .error x => .error x
      | .ok a' =>
        if I.size < p + n * e.headSize then .error .revert
        else match mseq I f e p 0 n a' with
          | .ok (xs, a'') => .ok (.fixed xs, a'')
          | .error x => .error x
    else .error .revert
  | f + 1, .tuple ms, p, a =>
    if I.size < p + Shape.headsSize ms then .error .revert else
    match alloc I a (ms.length * 32) with
    | .error x => .error x
    | .ok a' =>
      match mmembers I f ms p 0 a' with
      | .ok (vs, a'') => .ok (.tuple vs, a'')
      | .error x => .error x
  termination_by structural fuel _ _ _ => fuel

/-- Elements `i, i+1, …` (`n` of them) of a sequence whose element region
starts at `base`. -/
def mseq (I : Input) : Nat → (e : Shape) → Nat → Nat → (n : Nat) → Nat →
    Except Fail (Seq e n × Nat)
  | _, _, _, _, 0, a => .ok (.nil, a)
  | 0, _, _, _, _ + 1, _ => .error .fuel
  | f + 1, e, base, i, n + 1, a =>
    match melem I f e base (base + i * e.headSize) a with
    | .error x => .error x
    | .ok (v, a') =>
      match mseq I f e base (i + 1) n a' with
      | .error x => .error x
      | .ok (vs, a'') => .ok (.cons v vs, a'')
  termination_by structural fuel _ _ _ _ _ => fuel

/-- The element or member whose head is at `src`, in a region starting at
`base`: in place if static, else at its unsigned offset from `base`. -/
def melem (I : Input) : Nat → (e : Shape) → Nat → Nat → Nat → Except Fail (Val e × Nat)
  | 0, _, _, _, _ => .error .fuel
  | f + 1, e, base, src, a =>
    if e.dynamic then
      if lim < load I.data src then .error .revert
      else mdec I f e (base + load I.data src) a
    else mdec I f e src a
  termination_by structural fuel _ _ _ _ => fuel

/-- Members from head position `pos` of a tuple starting at `base`. -/
def mmembers (I : Input) : Nat → (ms : List Shape) → Nat → Nat → Nat →
    Except Fail (Vals ms × Nat)
  | _, [], _, _, a => .ok (.nil, a)
  | 0, _ :: _, _, _, _ => .error .fuel
  | f + 1, m :: ms, base, pos, a =>
    match melem I f m base (base + pos) a with
    | .error x => .error x
    | .ok (v, a') =>
      match mmembers I f ms base (pos + m.headSize) a' with
      | .error x => .error x
      | .ok (vs, a'') => .ok (.cons v vs, a'')
  termination_by structural fuel _ _ _ _ => fuel

end

/-! ### Calldata parameters: lazy access -/

/-- `access_calldata_tail_t_<e>(base, ptr)`: a signed relative offset that
leaves room for `e`'s tail, then for `bytes`/an array its length (at most
`2^64 - 1`) and its element region. The reference: address and length. -/
def tailRef (I : Input) (e : Shape) (base ptr : Nat) : Except Fail (Nat × Nat) :=
  let rel := load I.data ptr
  if tailFits I.size base rel e.tailSize then
    let addr := wrap (base + rel)
    if e.lengthPrefixed then
      let len := load I.data addr
      if lim < len then .error .revert
      else if regionFits I.size addr len e.stride then .ok (wrap (addr + 32), len)
      else .error .revert
    else .ok (addr, 0)
  else .error .revert


mutual
/-- The value of a calldata reference of shape `s` at `addr` (and `len`
elements for `bytes`/arrays), with every access validated as solc validates
it when the body reads it. -/
def cval (I : Input) : Nat → (s : Shape) → Nat → Nat → Except Fail (Val s)
  | 0, _, _, _ => .error .fuel
  | _ + 1, .word k, addr, _ =>
    if h : k.valid (load I.data addr) = true then .ok (.word ⟨load I.data addr, load_lt _ _, h⟩)
    else .error .revert
  | _ + 1, .bytes, addr, len => .ok (.bytes (bytesAt I.data addr len))
  | f + 1, .array e, addr, len =>
    match cseq I f e addr 0 len with
    | .ok xs => .ok (.array xs)
    | .error x => .error x
  | f + 1, .fixed e n, addr, _ =>
    match cseq I f e addr 0 n with
    | .ok xs => .ok (.fixed xs)
    | .error x => .error x
  | f + 1, .tuple ms, addr, _ =>
    match cmembers I f ms addr 0 with
    | .ok vs => .ok (.tuple vs)
    | .error x => .error x
  termination_by structural fuel _ _ _ => fuel

/-- `calldata_array_index_access` for each index from `i`. -/
def cseq (I : Input) : Nat → (e : Shape) → Nat → Nat → (n : Nat) → Except Fail (Seq e n)
  | _, _, _, _, 0 => .ok .nil
  | 0, _, _, _, _ + 1 => .error .fuel
  | f + 1, e, base, i, n + 1 =>
    match celem I f e base (wrap (base + i * e.headSize)) with
    | .error x => .error x
    | .ok v =>
      match cseq I f e base (i + 1) n with
      | .error x => .error x
      | .ok vs => .ok (.cons v vs)
  termination_by structural fuel _ _ _ _ => fuel

/-- An element or member with its head at `src`: in place if static, else
through `access_calldata_tail` (`tailRef`). -/
def celem (I : Input) : Nat → (e : Shape) → Nat → Nat → Except Fail (Val e)
  | 0, _, _, _ => .error .fuel
  | f + 1, e, base, src =>
    if e.dynamic then
      match tailRef I e base src with
      | .ok r => cval I f e r.1 r.2
      | .error x => .error x
    else cval I f e src 0
  termination_by structural fuel _ _ _ => fuel

/-- Members from head position `pos` of a calldata tuple at `base`. -/
def cmembers (I : Input) : Nat → (ms : List Shape) → Nat → Nat → Except Fail (Vals ms)
  | _, [], _, _ => .ok .nil
  | 0, _ :: _, _, _ => .error .fuel
  | f + 1, m :: ms, base, pos =>
    match celem I f m base (wrap (base + pos)) with
    | .error x => .error x
    | .ok v =>
      match cmembers I f ms base (pos + m.headSize) with
      | .error x => .error x
      | .ok vs => .ok (.cons v vs)
  termination_by structural fuel _ _ _ => fuel

end

/-- The reference a calldata parameter whose head is at `head + pos` holds
after `abi_decode_tuple`: the checks of `abi_decode_t_<s>_calldata_ptr`
only. A static parameter is its head position, unchecked beyond the head. -/
def cref (I : Input) (s : Shape) (head pos : Nat) : Except Fail (Nat × Nat) :=
  if s.dynamic then
    if lim < load I.data (head + pos) then .error .revert else
    let p := head + load I.data (head + pos)
    match s with
    | .bytes | .array _ =>
      if p + 31 < I.size then
        if lim < load I.data p then .error .revert
        else if I.size < p + 32 + load I.data p * s.stride then .error .revert
        else .ok (p + 32, load I.data p)
      else .error .revert
    | .tuple ms => if I.size < p + Shape.headsSize ms then .error .revert else .ok (p, 0)
    | .fixed e n => if I.size < p + n * e.headSize then .error .revert else .ok (p, 0)
    | .word _ => .ok (p, 0)
  else .ok (head + pos, 0)

/-! ### Entry -/

/-- Where a parameter lives in the body. -/
inductive Loc where
  | value
  | memory
  | calldata
  deriving DecidableEq, Repr

structure Param where
  shape : Shape
  loc : Loc

/-- What a parameter holds when the body starts. -/
inductive Entered (s : Shape) where
  | val (v : Val s)
  | ref (addr len : Nat)

inductive Entries : List Param → Type
  | nil : Entries []
  | cons {p : Param} {ps : List Param} (e : Entered p.shape) (es : Entries ps) : Entries (p :: ps)

def headsOf (ps : List Param) : Nat := Shape.headsSize (ps.map Param.shape)

/-- Parameters from head position `pos`, in order, as `abi_decode_tuple`
decodes them: values and memory parameters through `melem`, calldata
parameters through `cref`. -/
def enter (I : Input) (f : Nat) : (ps : List Param) → Nat → Nat → Except Fail (Entries ps × Nat)
  | [], _, a => .ok (.nil, a)
  | p :: ps, pos, a => do
    let (e, a') ← match p.loc with
      | .calldata => do
        let (addr, len) ← cref I p.shape 4 pos
        pure (Entered.ref addr len, a)
      | _ => do
        let (v, a') ← melem I f p.shape 4 (4 + pos) a
        pure (Entered.val v, a')
    let (es, a'') ← enter I f ps (pos + p.shape.headSize) a'
    pure (.cons e es, a'')

/-- Everything solc runs before a body: the head length check, then each
parameter in order. -/
def entry (I : Input) (f : Nat) (ps : List Param) : Except Fail (Entries ps) :=
  if I.size < 4 + headsOf ps then .error .revert
  else match enter I f ps 0 0 with
    | .ok (es, _) => .ok es
    | .error x => .error x

/-- Lazy full validation of an entered calldata reference. -/
def cvalRef (I : Input) (f : Nat) (s : Shape) (addr len : Nat) : Except Fail (Val s) :=
  cval I f s addr len

/-- The same parameter decoded eagerly, as a copy to memory decodes it. -/
def eager (I : Input) (f : Nat) (s : Shape) (pos : Nat) : Except Fail (Val s) :=
  match melem I f s 4 (4 + pos) 0 with
  | .ok (v, _) => .ok v
  | .error x => .error x

/-- How the adapter treats an input. -/
inductive Verdict (ps : List Param) where
  /-- solc reverts with empty data before the body. -/
  | revert
  /-- The body runs on these values. -/
  | run (vs : Vals (ps.map Param.shape))
  /-- Outside the proved fragment. -/
  | blocked (reason : String)

/-- Per parameter: its value for the body, or a refusal. A calldata
parameter must decode eagerly too (then `mdec_cval` makes lazy reads agree);
a layout only the lazy reader accepts, or one whose element fails only on
access, is refused by name. -/
def bodyValues (I : Input) (f : Nat) : (ps : List Param) → Entries ps → Nat →
    Except String (Vals (ps.map Param.shape))
  | [], .nil, _ => .ok .nil
  | p :: ps, .cons e es, pos => do
    let v ← match e with
      | .val v => pure v
      | .ref addr len =>
        match eager I f p.shape pos with
        | .ok v => pure v
        | .error .fuel => throw "ABI decoder fuel exhausted"
        | .error _ =>
          match cvalRef I f p.shape addr len with
          | .ok _ => throw "calldata layout accepted by lazy access but rejected by an eager copy needs calldata references in the source semantics"
          | .error .revert => throw "calldata element fails only on access: needs access-time calldata semantics"
          | .error _ => throw "calldata element validation exhausted fuel"
    let vs ← bodyValues I f ps es (pos + p.shape.headSize)
    pure (.cons v vs)

def verdict (I : Input) (f : Nat) (ps : List Param) : Verdict ps :=
  match entry I f ps with
  | .error .revert => .revert
  | .error .panic => .blocked "possible Panic(0x41) allocation failure in memory decoding"
  | .error .fuel => .blocked "ABI decoder fuel exhausted"
  | .ok es =>
    match bodyValues I f ps es 0 with
    | .ok vs => .run vs
    | .error r => .blocked r

/-! ### Canonical encoding -/

/-- A word's 32 big-endian bytes. -/
def wordBytes (n : Nat) : List UInt8 :=
  (List.range 32).map fun i => UInt8.ofNat (n / 256 ^ (31 - i))

/-- Heads then tails of a tuple of encoded parts (`true`: dynamic). -/
def assemble (parts : List (Bool × List UInt8)) : List UInt8 :=
  let headLen := parts.foldl (fun acc (d, b) => acc + if d then 32 else b.length) 0
  let rec go : List (Bool × List UInt8) → Nat → List UInt8 × List UInt8
    | [], _ => ([], [])
    | (d, b) :: ps, off =>
      let (hs, ts) := go ps (if d then off + b.length else off)
      if d then (wordBytes off ++ hs, b ++ ts) else (b ++ hs, ts)
  let (hs, ts) := go parts headLen
  hs ++ ts

mutual
/-- `abi.encode` of one value (its standalone encoding). -/
def Val.enc : {s : Shape} → Val s → List UInt8
  | _, .word w => wordBytes w.val
  | _, .bytes bs => wordBytes bs.length ++ bs ++ List.replicate (roundUp bs.length - bs.length) 0
  | _, .array (n := n) xs => wordBytes n ++ assemble (Seq.parts xs)
  | _, .fixed xs => assemble (Seq.parts xs)
  | _, .tuple vs => assemble (Vals.parts vs)
def Seq.parts : {e : Shape} → {n : Nat} → Seq e n → List (Bool × List UInt8)
  | _, _, .nil => []
  | e, _, .cons v vs => (e.dynamic, Val.enc v) :: Seq.parts vs
def Vals.parts : {ms : List Shape} → Vals ms → List (Bool × List UInt8)
  | _, .nil => []
  | s :: _, .cons v vs => (s.dynamic, Val.enc v) :: Vals.parts vs
end

/-- The canonical argument bytes of a parameter tuple (no selector). -/
def encodeArgs {ss : List Shape} (vs : Vals ss) : List UInt8 := assemble (Vals.parts vs)

/-- A verdict's observation: `none` to run, `some true` a certified revert,
`some false` a refusal. -/
def Verdict.kind {ps : List Param} : Verdict ps → String
  | .revert => "revert"
  | .run _ => "run"
  | .blocked r => "blocked: " ++ r

end Solidity.AbiEntry
