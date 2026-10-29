import Solidity.Source.Machine

/-!
# Expression and statement semantics (S02, S03)

The independent semantics of resolved Solidity (`RExpr`, `RLVal`, `RStmt`,
`RItems`, `Solidity/Source/Resolved.lean`), never of raw syntax, over the
machine of `Solidity/Source/Machine.lean`.

**Horizons, not fuel limits.**  Every function takes a horizon `n` and
spends one unit per nested evaluation; at `0` it stops with
`Halt.timeout`.  `timeout` is not a behaviour of the program: the
semantics of an execution is the family over all horizons
(`Solidity/Source/Semantics.lean` takes the least horizon at which it
completes, and an execution that completes at none diverges).  No inlining
depth, loop bound or recursion bound restricts what completes.

**Expressions (S02).**

- *Values*: constants are carried exactly and converted only by an explicit
  `conv`; integer and fixed-point arithmetic is checked (`Panic(0x11)`) or,
  under `unchecked`, wrapping; division and modulo by zero `Panic(0x12)`;
  array and `bytes` indices out of bounds `Panic(0x32)`; enum conversions
  out of range `Panic(0x21)`; `assert` `Panic(0x01)`; `require`/`revert`
  with `Error(string)` data or none; custom errors their selector and
  arguments.
- *Effect order*, per pipeline (`Glob.pipeline`, solc's two settings):
  binary operators, comparisons, shifts and powers evaluate the right
  operand first under the legacy pipeline and the left first via IR;
  `addmod`/`mulmod` their arguments right to left under legacy, left to
  right via IR; assignments the right-hand side before the target, and a
  compound assignment or `++`/`--` resolve the target once; call, event,
  error, tuple and struct arguments left to right; `&&`, `||` and `? :`
  evaluate only what they select.
- *Aliases*: a storage reference is a logical path (`SPath`), a memory
  reference an address; assigning a reference to a local copies the
  pointer, assigning to a storage location copies the contents
  (`storeVal`), converting storage to memory copies (`loadMem`), memory to
  memory keeps the pointer.

**Statements (S03.01).**  `execS` gives each statement an outcome
(`Out`): normal completion in the statement's output context, or `break`,
`continue`, `return` with the locals of its input context; blocks end
their scope (`Locals.restore`), loops iterate until their condition fails,
`break` or `return`.  `return e` writes the function's return slots and
leaves the body, as solc compiles it.

**Modifiers and calls (S03.02, S03.03).**  `runMods` runs a body under its
modifiers, outermost first; each `_` runs the rest (`Ph`), any number of
times.  Under the legacy pipeline every `_` shares the function's
parameter and return slots; via IR each `_` starts from the parameters at
entry and fresh (zero) return slots, and the last invocation's returns are
the function's (upstream `modifiers/function_modifier_multi_invocation.sol`
and `…_viair.sol`: `f(true)` is `2` and `1`).  Internal calls dispatch virtually along the C3
linearization of the instance's contract (`Program.dispatchFn`).  External
calls to an instance of the system enter a new frame (`Fr`: `this`,
sender, value, static flag, depth) with fresh memory and a journal mark,
moving the value first; a revert rolls back to the mark and its data
reaches the caller, which re-raises it.  Calls to accounts outside the
system are G01 events: the call, then the environment's moves (answers,
credits and callbacks into any instance at any depth, `envLoop`).  At
depth 1024 a call fails with empty revert data (G01 follow-up
"nested-frame failures").  Writes in a static frame revert.
-/

namespace Solidity.Source

open Solidity.Roadmap (Address Word Bytes Event Outcome Pipeline Strategy Fixed Move)
open EM

variable {E : Env}

/-! ## ABI encoding and decoding -/

/-- Decimal digits (signatures are character lists, which the kernel
evaluates directly, rather than `String`s). -/
def decChars (n : Nat) : List Char := Nat.toDigits 10 n

/-- The ABI name of an elementary type. -/
def STy.elemAbiName : STy → List Char
  | .int t => (if t.signed then "int".toList else "uint".toList) ++ decChars t.bits
  | .bool => "bool".toList
  | .address _ | .contract _ => "address".toList
  | .fixedBytes n _ => "bytes".toList ++ decChars n
  | .fixed f => (if f.signed then "fixed".toList else "ufixed".toList) ++ decChars f.bits ++ 'x' :: decChars f.digits
  | .enum _ => "uint8".toList
  | .bytes _ => "bytes".toList
  | .string _ => "string".toList
  | .fn true _ _ _ => "function".toList
  | _ => "tuple".toList

/-- The ABI name of a type in a signature. -/
def STy.abiName (D : Layout) : STy → List Char
  | .udvt d => (D.underlying d).elemAbiName
  | .array _ τ n => τ.abiName D ++ '[' :: ((n.map decChars).getD []) ++ [']']
  | τ => τ.elemAbiName

/-- Names joined by commas. -/
def commaJoin : List (List Char) → List Char
  | [] => []
  | [x] => x
  | x :: xs => x ++ ',' :: commaJoin xs

/-- A function's, event's or error's signature, `name(T1,T2,…)`. -/
def sigOf (D : Layout) (name : String) (ps : List STy) : List Char :=
  name.toList ++ '(' :: commaJoin (ps.map (STy.abiName D)) ++ [')']

/-- The bytes of an ASCII signature. -/
def asciiBytes (cs : List Char) : Bytes := cs.map fun c => c.toNat.toUInt8

/-- The first four bytes of the fixed hash of a signature. -/
def Glob.selector (G : Glob E) (sig : List Char) : Bytes :=
  (wordBytes (G.fixed.hash (asciiBytes sig))).take 4

/-- The bytes of a byte-array value (`bytes`/`string` in memory or
storage, a string literal). -/
def bytesOfRV {Γ : RCtx} (F : Fr) (n : Nat) {τ : STy} : RVal E.layout τ → EM E Γ Bytes
  | .strLit bs => pure bs
  | .val (.memRef _ a) => heapBytes a
  | .val (.storRef _ p) => do
    match ← loadMem F n (.bytes .memory) p with
    | .bytes bs => pure bs
    | _ => halt (.stuck "bytes in storage")
  | _ => halt (.stuck "not a byte array")

/-- The packed width of a value type. -/
def STy.packedWidth : STy → Nat
  | .int t => t.bits / 8
  | .fixed f => f.bits / 8
  | .bool | .enum _ => 1
  | .address _ | .contract _ => 20
  | .fixedBytes n _ => n
  | _ => 32

/-- One argument's encoding: a static head word, or dynamic contents
(standard) or its raw bytes (packed). -/
def encodeOne {Γ : RCtx} (F : Fr) (n : Nat) (packed : Bool) {τ : STy} (v : RVal E.layout τ) :
    EM E Γ (Bool × Bytes) := do
  match τ, v with
  | .rational q, _ =>
    let w := intWord q.toInt
    match q.mobileInt? with
    | some t => pure (false, if packed then natBytes (t.bits / 8) (wrapBits false t.bits q.toInt).toNat else wordBytes w)
    | none => pure (false, wordBytes w)
  | .stringLit _, v | .bytes _, v | .string _, v => pure (true, ← bytesOfRV F n v)
  | τ, .val x =>
    match x.word with
    | some w =>
      if packed then
        match τ with
        | .fixedBytes k _ => pure (false, (wordBytes w).take k)
        | τ => pure (false, (wordBytes w).drop (32 - τ.packedWidth))
      else pure (false, wordBytes w)
    | none => halt (.stuck "not ABI-encodable")
  | _, _ => halt (.stuck "not ABI-encodable")

/-- Arguments' encodings, in order. -/
def encodeParts {Γ : RCtx} (F : Fr) (n : Nat) (packed : Bool) : {τs : List STy} → RVals E.layout τs →
    EM E Γ (List (Bool × Bytes))
  | _, .nil => pure []
  | _, .cons v vs => do pure ((← encodeOne F n packed v) :: (← encodeParts F n packed vs))

/-- **ABI encoding** (`abi.encode`, call data, return data): heads, then
the dynamic tails with their lengths, padded to words. -/
def abiLayout (parts : List (Bool × Bytes)) : Bytes :=
  let headLen := 32 * parts.length
  let rec go : List (Bool × Bytes) → Nat → Bytes × Bytes
    | [], _ => ([], [])
    | (false, w) :: ps, off => let (h, t) := go ps off; (w ++ h, t)
    | (true, bs) :: ps, off =>
      let tail := wordBytes (toWord bs.length) ++ pad32 bs
      let (h, t) := go ps (off + tail.length)
      (wordBytes (toWord off) ++ h, tail ++ t)
  let (h, t) := go parts headLen
  h ++ t

/-- Encoding arguments, standard or packed. -/
def encodeVals {Γ : RCtx} (F : Fr) (n : Nat) (packed : Bool) {τs : List STy} (vs : RVals E.layout τs) :
    EM E Γ Bytes := do
  let parts ← encodeParts F n packed vs
  if packed then pure (parts.foldr (fun p acc => p.2 ++ acc) []) else pure (abiLayout parts)

/-- The word at a position of ABI data (zeros past its end). -/
def wordAt (data : Bytes) (i : Nat) : Nat := beValue (fitBytes 32 (data.drop (32 * i)))

/-- **Decoding a static value** from its word; an invalid word reverts
with no data, as solc's decoder does. -/
def decodeWord (D : Layout) (w : Nat) : (τ : STy) → R (Val D τ)
  | .int t =>
    match readInt t (toWord w) with
    | some v => mkInt t v
    | none => .error (.revert [])
  | .bool => if w = 0 then pure (.bool false) else if w = 1 then pure (.bool true) else .error (.revert [])
  | .address _ => if h : w < 2 ^ 160 then pure (.address ⟨w, h⟩) else .error (.revert [])
  | .contract _ => if h : w < 2 ^ 160 then pure (.contract ⟨w, h⟩) else .error (.revert [])
  | .fixedBytes n h =>
    let bs := natBytes 32 w
    if bs.drop n = List.replicate (32 - n) 0 then pure (mkBytes (n := n) (h := h) bs) else .error (.revert [])
  | .enum d => if h : w < D.enumSize d then pure (.enum ⟨w, h⟩) else .error (.revert [])
  | .fixed f =>
    match readInt ⟨f.signed, f.bits, by have := f.valid; omega⟩ (toWord w) with
    | some v => mkFix f v
    | none => .error (.revert [])
  | _ => stuck "dynamic ABI decoding is not modelled"

/-- Decoding static values from ABI data, from the `i`-th word. -/
def decodeVals (D : Layout) (data : Bytes) : (τs : List STy) → Nat → R (Vals D τs)
  | [], _ => pure .nil
  | τ :: τs, i => do pure (.cons (← decodeWord D (wordAt data i) τ) (← decodeVals D data τs (i + 1)))

/-- The value of a call returning `rs` from the values of its returns. -/
def mkRet {D : Layout} : (rs : List STy) → RVals D rs → RVal D (STy.ret rs)
  | [_], .cons v .nil => v
  | [], vs => .tuple vs
  | _ :: _ :: _, vs => .tuple vs

/-- The values of a call's returns from its value. -/
def unRet {D : Layout} : (rs : List STy) → RVal D (STy.ret rs) → R (RVals D rs)
  | [_], v => pure (.cons v .nil)
  | [], _ => pure .nil
  | _ :: _ :: _, .tuple vs => pure vs
  | _ :: _ :: _, _ => stuck "return tuple"

/-! ## Conversions with state -/

/-- **An implicit conversion** (`RExpr.conv`): a constant at its target
type; a string literal allocated as `bytes`/`string memory` or padded to
`bytesN`; storage copied to memory; a memory reference kept; value types by
`convVal`. -/
def convRV {Γ : RCtx} (F : Fr) (n : Nat) {σ : STy} (τ : STy) (v : RVal E.layout σ) :
    EM E Γ (RVal E.layout τ) := do
  if h : σ = τ then return h ▸ v
  match σ, τ, v with
  | .rational q, τ, _ => return .val (← lift (constVal q τ))
  | .stringLit bs, .bytes .memory, _ => return .val (← allocRef (Data.bytes (D := E.layout) (l := .memory) bs))
  | .stringLit bs, .string .memory, _ => return .val (← allocRef (Data.string (D := E.layout) (l := .memory) bs))
  | .stringLit bs, .fixedBytes k hk, _ => return .val (mkBytes (n := k) (h := hk) bs)
  | _, τ, .val (.storRef _ p) =>
    if τ.loc? = some .memory then return .val (← allocRef (← loadMem F n τ p))
    else return .val (← storRef τ p)
  | _, τ, .val (.memRef _ a) =>
    if h : τ.loc? = some .memory then return .val (.memRef h a) else halt (.stuck "memory to non-memory")
  | _, τ, .val x => return .val (← lift (convVal τ x))
  | _, _, _ => halt (.stuck "implicit conversion")

/-- **An explicit conversion** (`T(e)`). -/
def convExplicitRV {Γ : RCtx} (F : Fr) (n : Nat) {σ : STy} (τ : STy) (v : RVal E.layout σ) :
    EM E Γ (RVal E.layout τ) := do
  match σ, v with
  | .rational q, _ => return .val (← lift (constExplicit q τ))
  | _, .val (.memRef _ a) =>
    if h : τ.loc? = some .memory then return .val (.memRef h a) else convRV F n τ v
  | _, .val (.storRef _ p) =>
    if h : τ.loc? = some .storage then return .val (.storRef h p) else convRV F n τ v
  | _, .val x =>
    if τ.byRef then convRV F n τ v else return .val (← lift (convExplicitVal τ x))
  | _, _ => convRV F n τ v

/-- A converted argument list as values. -/
def RVals.vals {D : Layout} {τs : List STy} (vs : RVals D τs) : R (Vals D τs) := vs.toVals

/-! ## Locations -/

/-- **A resolved location** an lvalue denotes. -/
inductive Loc (D : Layout) (Γ : RCtx) : STy → Type where
  | local {τ : STy} (i : Idx Γ τ) : Loc D Γ τ
  /-- A storage path of `this` (transient by its root). -/
  | stor {τ : STy} (p : SPath) : Loc D Γ τ
  /-- Element or member `i` of the memory object at `a`. -/
  | mem {τ : STy} (a i : Nat) : Loc D Γ τ
  /-- Byte `i` of the memory `bytes` at `a`. -/
  | memByte (a i : Nat) : Loc D Γ (.fixedBytes 1 (by decide))

/-- The element or member `i` of a memory object, at type `τ`. -/
def memElem {Γ : RCtx} (a i : Nat) (τ : STy) : EM E Γ (Val E.layout τ) := do
  match ← heapObj a with
  | ⟨_, .array len _ xs⟩ =>
    if h : i < len then
      let ⟨σ, x⟩ : Σ σ, Data E.layout σ := ⟨_, xs ⟨i, h⟩⟩
      if e : σ = τ then lift (e ▸ x).asVal else halt (.stuck "element type")
    else panicM
  | ⟨_, .struct fs⟩ => lift ((← lift (fs.nth i τ)).asVal)
  | _ => halt (.stuck "not an aggregate")
where
  panicM {α : Type} : EM E Γ α := lift (panic .index)

/-- **Reading a location**: a storage reference type at a path is the path
itself; a value is read. -/
def readLoc {Γ : RCtx} (F : Fr) {τ : STy} : Loc E.layout Γ τ → EM E Γ (Val E.layout τ)
  | .local i => do return (← locals).get i
  | .stor p => if τ.byRef then storRef τ p else readAt F p τ
  | .mem a i => memElem a i τ
  | .memByte a i => do
    let bs ← heapBytes a
    match bs[i]? with
    | some b => return Val.fixedBytes (n := 1) (h := by decide) [b] rfl
    | none => lift (panic .index)

/-- Replacing element `i` of a memory object. -/
def memSet {Γ : RCtx} (a i : Nat) {τ : STy} (v : Val E.layout τ) : EM E Γ Unit := do
  match ← heapObj a with
  | ⟨_, .array (l := l') (τ := ρ) (n := k') len hl xs⟩ =>
    if h : i < len then
      if e : τ = ρ then
        heapPut a ⟨.array l' ρ k', .array len hl (fun j => if j.val = i then e ▸ Data.val v else xs j)⟩
      else halt (.stuck "element type")
    else lift (panic .index)
  | ⟨_, .struct (l := l') (d := d') fs⟩ => heapPut a ⟨.struct l' d', .struct (← lift (fs.setNth i (Data.val v)))⟩
  | _ => halt (.stuck "not an aggregate")

/-- **Writing a location**: a local or memory element takes the value
(a reference by pointer); a storage location of reference type receives a
copy of the contents. -/
def writeLoc {Γ : RCtx} (F : Fr) (n : Nat) {τ : STy} (loc : Loc E.layout Γ τ) (v : Val E.layout τ) :
    EM E Γ Unit :=
  match loc with
  | .local i => do setLocals ((← locals).set i v)
  | .stor p => if τ.byRef then storeVal F n τ p v else writeAt F p v
  | .mem a i => memSet a i v
  | .memByte a i => do
    let b := match v with | .fixedBytes bs _ => bs.headD 0
    match ← heapObj a with
    | ⟨_, .bytes (l := l') bs⟩ =>
      if i < bs.length then heapPut a ⟨.bytes l', .bytes (bs.set i b)⟩ else lift (panic .index)
    | _ => halt (.stuck "not bytes")

/-- **Deleting a location**: the default value, a fresh zeroed memory
object, or storage reset below the path. -/
def deleteLoc {Γ : RCtx} (F : Fr) (n : Nat) {τ : STy} (loc : Loc E.layout Γ τ) : EM E Γ Unit :=
  match loc with
  | .stor p => if τ.byRef then deleteStor F n τ p else setCell F p none
  | loc => do writeLoc F n loc (← zeroVal n τ)

/-! ## Indexing -/

/-- The length of an array or byte array reference, or of `bytesN`. -/
def lengthOf {Γ : RCtx} (F : Fr) {τ : STy} (v : Val E.layout τ) : EM E Γ Nat :=
  match τ, v with
  | .array _ _ (some m), _ => pure m
  | _, .storRef _ p => readLen F p
  | _, .memRef _ a => do
    match ← heapObj a with
    | ⟨_, .array len _ _⟩ => pure len
    | ⟨_, .bytes bs⟩ | ⟨_, .string bs⟩ => pure bs.length
    | _ => halt (.stuck "length")
  | .fixedBytes k _, _ => pure k
  | _, _ => halt (.stuck "length")

/-- The location of element `i` of an array value. -/
def indexLoc {Γ : RCtx} (F : Fr) {l : DataLoc} {σ : STy} {k : Option Nat}
    (a : Val E.layout (.array l σ k)) (i : Nat) : EM E Γ (Loc E.layout Γ σ) := do
  let len ← lengthOf F a
  if i < len then
    match a with
    | .storRef _ p => pure (.stor (p.go (.index i)))
    | .memRef _ addr => pure (.mem addr i)
    | _ => halt (.stuck "calldata arrays are not modelled")
  else lift (panic .index)

/-- The contents of a mapping key, as its path step. -/
def keyStep {Γ : RCtx} (F : Fr) (n : Nat) {τ : STy} (k : RVal E.layout τ) : EM E Γ Step := do
  match τ, k with
  | .bytes _, k | .string _, k | .stringLit _, k => pure (.key (← bytesOfRV F n k))
  | _, .val x =>
    match x.word with
    | some w => pure (.key (wordBytes w))
    | none => halt (.stuck "mapping key")
  | _, _ => halt (.stuck "mapping key")

/-- An index value as a number. -/
def indexNat {Γ : RCtx} {σ : STy} (v : RVal E.layout σ) : EM E Γ Nat := lift v.amount

/-- The empty locals. -/
abbrev L0 (E : Env) : Locals E.layout [] := .nil

/-! ## Statement outcomes and placeholders -/

/-- **A statement's outcome**: normal completion in its output context;
`break`, `continue` or `return` with the locals of its input context. -/
inductive Out (D : Layout) (Γ Γ' : RCtx) where
  | normal (l : Locals D Γ')
  | brk (l : Locals D Γ)
  | cont (l : Locals D Γ)
  | ret (l : Locals D Γ)

/-- What a modifier's `_` runs: the rest of the modifiers and the body,
with the function's locals at entry (the parameters via-IR restarts
from). -/
structure Ph (E : Env) where
  body : RBody E
  rest : List (RModInv E body.locals)
  orig : Locals E.layout body.locals

/-- An abnormal outcome moved to an enclosing context. -/
def Out.up {D : Layout} {Γ₁ Γ₂ : RCtx} (Γ₀ : RCtx) : Out D Γ₁ Γ₂ → R (Out D Γ₀ Γ₂)
  | .normal l => pure (.normal l)
  | .brk l => do pure (.brk (← l.restore Γ₀))
  | .cont l => do pure (.cont (← l.restore Γ₀))
  | .ret l => do pure (.ret (← l.restore Γ₀))

/-- An outcome's scope ended: normal completion back in the input context. -/
def Out.close {D : Layout} {Γ Γ' : RCtx} : Out D Γ Γ' → R (Out D Γ Γ)
  | .normal l => do pure (.normal (← l.restore Γ))
  | .brk l => pure (.brk l)
  | .cont l => pure (.cont l)
  | .ret l => pure (.ret l)

/-! ## Programs: dispatch -/

/-- The functions named `x` with parameter types `ps` declared in scope `s`. -/
def Env.fnIn (E : Env) (s : String) (x : String) (ps : List STy) : List Decl :=
  (E.declared (some s) x).filter fun d =>
    d.kind == .function && match d.fnSig E with
      | some (ps', _) => STy.sameList ps ps'
      | none => false

/-- **Virtual dispatch**: the implementation of `d` in the most derived
contract `c` of `this`: the first scope of `c`'s linearization that
declares a function of the same name and parameters with a body; a free or
library function is itself. -/
def Glob.dispatchFn (G : Glob E) (c : String) (d : Decl) : Decl :=
  match d.fnSig E with
  | some (ps, _) =>
    let chain := (E.linearize c).getD [c]
    if d.scope.isSome && chain.any (some · == d.scope) then
      ((chain.findSome? fun s => (E.fnIn s d.name ps).find? fun d' => (G.prog.body d').isSome)).getD d
    else d
  | none => d

/-- The functions contract `c` exposes, most derived first. -/
def Env.exposed (E : Env) (c : String) : List Decl :=
  ((E.linearize c).getD [c]).flatMap fun s =>
    E.decls.filter fun d => d.scope == some s && d.kind == .function &&
      (d.fnVis == some .external || d.fnVis == some .pub)

/-- The `receive` or `fallback` function of contract `c`. -/
def Env.special (E : Env) (c : String) (k : DeclKind) : Option Decl :=
  ((E.linearize c).getD [c]).findSome? fun s => E.decls.find? fun d => d.scope == some s && d.kind == k

/-- The position of an instance's contract and its name. -/
def Glob.contractAt (G : Glob E) (k : Nat) : Option String := G.prog.contracts[k]?

/-- The default values of a list of types. -/
def zeroVals {Γ : RCtx} (n : Nat) : (τs : List STy) → EM E Γ (Vals E.layout τs)
  | [] => pure .nil
  | τ :: τs => do pure (.cons (← zeroVal n τ) (← zeroVals n τs))

/-- The return values of a body from its final locals: the `|rs|`
innermost slots, the last return innermost. -/
def retVals {D : Layout} {Γ : RCtx} (l : Locals D Γ) (base : Nat) : (rs : List STy) → R (RVals D rs)
  | [] => pure .nil
  | r :: rs => do pure (.cons (.val (← l.getAt (base + rs.length) r)) (← retVals l base rs))

/-- The instance at an address, if the system has one there: its
contract's name. -/
def instanceAt {Γ : RCtx} (G : Glob E) (a : Address) : EM E Γ (Option String) := do
  match ((← st).ex.world.accounts a).code with
  | some k => pure (G.contractAt k)
  | none => pure none

/-- Recording an observable event. -/
def emitEvent {Γ : RCtx} (e : Event) : EM E Γ Unit := modSt fun s => { s with events := s.events ++ [e] }

/-- Crediting an instance (a callback's value from outside, an
environment credit), journaled. -/
def credit {Γ : RCtx} (a : Address) (v : Word) : EM E Γ Unit := do
  let b := ((← st).ex.world.accounts a).balance.val
  if h : b + v.val < 2 ^ 256 then
    modSt fun s => { s with ex := s.ex.apply (.account a fun x => x.withBalance ⟨b + v.val, h⟩) }
  else halt (.revert [])

/-- Debiting an instance (value sent outside), journaled; `none` when it
cannot afford it. -/
def debit {Γ : RCtx} (a : Address) (v : Word) : EM E Γ Bool := do
  let b := ((← st).ex.world.accounts a).balance.val
  if h : v.val ≤ b then
    modSt fun s => { s with ex := s.ex.apply (.account a fun x => x.withBalance ⟨b - v.val, by omega⟩) }
    pure true
  else pure false

/-- The journal mark of the state: its length and the logs'. -/
def mark {Γ : RCtx} : EM E Γ (Nat × Nat × Heap E.layout) := do
  let s ← st
  pure (s.ex.journal.length, s.logs.length, s.heap)

/-- Rolling back to a mark (a reverted frame). -/
def rollbackTo {Γ : RCtx} (m : Nat × Nat × Heap E.layout) : EM E Γ Unit :=
  modSt fun s => { s with ex := s.ex.undoN (s.ex.journal.length - m.1), logs := s.logs.drop (s.logs.length - m.2.1) }

/-- An outcome's revert data re-raised. -/
def reraise {Γ : RCtx} : Outcome → EM E Γ Bytes
  | .success d => pure d
  | .revert d => halt (.revert d)

/-- The `k` innermost locals reset to their defaults (via IR, each `_`
runs the body in fresh return slots). -/
def zeroInner {Γ' : RCtx} (n : Nat) : (k : Nat) → {Γ : RCtx} → Locals E.layout Γ → EM E Γ' (Locals E.layout Γ)
  | 0, _, l => pure l
  | _ + 1, _, .nil => pure .nil
  | k + 1, _, .cons (τ := τ) _ r => do pure (.cons (← zeroVal n τ) (← zeroInner n k r))

/-- The binary operator of a compound assignment. -/
def AssignOp.binOp : AssignOp → BinOp
  | .add => .add | .sub => .sub | .mul => .mul | .div => .div | .mod => .mod
  | .bitAnd => .bitAnd | .bitOr => .bitOr | .bitXor => .bitXor
  | .shl => .shl | .sar => .sar | .shr => .shr | .assign => .add

/-- A struct's fields from its members' values. -/
def fieldsOf {Γ : RCtx} {D : Layout} : {ps : List STy} → Vals D ps → (τs : List STy) → EM E Γ (DataList D τs)
  | [], .nil, [] => pure .nil
  | σ :: _, .cons v vs, τ :: τs => do
    if h : σ = τ then pure (.cons (.val (h ▸ v)) (← fieldsOf vs τs)) else halt (.stuck "member type")
  | _, _, _ => halt (.stuck "member count")

/-- A hash or digest as `bytesN`. -/
def ret32 {Γ : RCtx} (τ : STy) (bs : Bytes) : EM E Γ (RVal E.layout τ) :=
  match τ with
  | .fixedBytes k hk => pure (.val (mkBytes (n := k) (h := hk) bs))
  | _ => halt (.stuck "digest type")

/-- Writing return values into the return slots from position `base`. -/
def setRets {D : Layout} {Γ : RCtx} (l : Locals D Γ) (base : Nat) : {rs : List STy} → Vals D rs → R (Locals D Γ)
  | _, .nil => pure l
  | _, .cons (τs := τs) v vs => do setRets (← l.setAt (base + τs.length) v) base vs

/-! ## The interpreter -/

mutual

/-- **Expression evaluation** at horizon `n`. -/
def evalE (G : Glob E) (F : Fr) (n : Nat) {Γ : RCtx} {τ : STy} (e : RExpr E Γ τ) :
    EM E Γ (RVal E.layout τ) :=
  match n with
  | 0 => halt .timeout
  | n + 1 =>
  match e with
  | .const q => pure (.const q)
  | .bytesLit (len := len) (h := h) nl _ =>
    pure (.val (mkBytes (n := len) (h := h) (natBytes len nl.value.toInt.toNat)))
  | .addressLit ds =>
    let v := ds.foldl (fun acc d => acc * 16 + d.val) 0
    pure (.val (.address ⟨v % 2 ^ 160, Nat.mod_lt _ (by decide)⟩))
  | .bool b => pure (.val (.bool b))
  | .str bs => pure (.strLit bs)
  | .local i => do return .val ((← locals).get i)
  | .state (τ := τ) d _ =>
    if d.isConst then do
      match G.prog.consts d with
      | some ri =>
        let (v, _) ← sub (L0 E) (evalE G F n ri.e)
        if h : ri.τ = τ then return h ▸ v else halt (.stuck "constant type")
      | none => halt (.stuck "constant without a value")
    else if τ.byRef then do return .val (← storRef τ d.path)
    else do return .val (← readAt F d.path τ)
  | .this _ => pure (.val (.contract F.this))
  | .tuple es => do return .tuple (← evalArgs G F n es)
  | .conv (τ := τ) a _ => do convRV F n τ (← evalE G F n a)
  | .convExplicit (τ := τ) a _ => do convExplicitRV F n τ (← evalE G F n a)
  | .unary op a => do
    let x ← getV (← evalE G F n a)
    return .val (← lift (unaryVal F.checked op x))
  | .incDec inc pre l => do
    let loc ← evalLoc G F n l
    let old ← readLoc F loc
    let new ← lift (incDecVal F.checked inc old)
    writeLoc F n loc new
    return .val (if pre then new else old)
  | .delete l => do
    deleteLoc F n (← evalLoc G F n l)
    return RVal.unit
  | .binary op a b => do
    if op = .and || op = .or then
      let x ← getV (← evalE G F n a)
      match x.key with
      | some kx =>
        if (op = .and && kx = 0) || (op = .or && kx = 1) then return .val x
        else return .val (← getV (← evalE G F n b))
      | none => halt (.stuck "logical operand")
    else
      let (x, y) ← evalPair G F n a b
      return .val (← lift (binVal F.checked op (← getV x) (← getV y)))
  | .compare op a b => do
    let (x, y) ← evalPair G F n a b
    return .val (.bool (← lift (cmpVal op (← getV x) (← getV y))))
  | .compareConst op qa qb => do return .val (.bool (← lift (cmpConst op qa qb)))
  | .shiftLike op a b _ => do
    let (x, k) ← evalPair G F n a b
    return .val (← lift (shiftVal F.checked op (← lift k.amount) (← getV x)))
  | .cond c a b => do
    match ← getV (← evalE G F n c) with
    | .bool true => evalE G F n a
    | _ => evalE G F n b
  | .assign l rhs => do
    let v ← evalE G F n rhs
    let loc ← evalLoc G F n l
    let x ← getV v
    writeLoc F n loc x
    return .val x
  | .compound (τ := τ) op l rhs _ => do
    let v ← evalE G F n rhs
    let loc ← evalLoc G F n l
    let old ← readLoc F loc
    let new ← match op.kind? with
      | some .shift =>
        lift (shiftVal F.checked (if op = .shl then .shl else if op = .sar then .sar else .shr) (← lift v.amount) old)
      | _ => do
        let y ← getV (← convRV F n τ v)
        lift (binVal F.checked (AssignOp.binOp op) old y)
    writeLoc F n loc new
    return .val new
  | .indexArray (τ := τ) a i _ => do
    let av ← getV (← evalE G F n a)
    let k ← indexNat (← evalE G F n i)
    let loc ← indexLoc F av k
    return .val (← readLoc F loc)
  | .indexMapping (τv := τv) a k => do
    match ← getV (← evalE G F n a) with
    | .storRef _ p =>
      let s ← keyStep F n (← evalE G F n k)
      return .val (← readLoc F (Loc.stor (τ := τv) (p.go s)))
    | _ => halt (.stuck "mapping not in storage")
  | .indexBytes a i _ => do
    let av ← evalE G F n a
    let k ← indexNat (← evalE G F n i)
    match av with
    | .val (.fixedBytes bs _) =>
      match bs[k]? with
      | some b => return .val (Val.fixedBytes (n := 1) (h := by decide) [b] rfl)
      | none => lift (panic .index)
    | .val (.memRef _ addr) => return .val (← readLoc F (Loc.memByte addr k))
    | .val (.storRef _ p) =>
      if k < (← readLen F p) then return .val (← readAt F (p.go (.index k)) (.fixedBytes 1 (by decide)))
      else lift (panic .index)
    | _ => halt (.stuck "byte index")
  | .length (ρ := ρ) a _ => do
    let k ← lengthOf F (← getV (← evalE G F n a))
    match ρ with
    | .int t => return .val (intWrap t k)
    | _ => halt (.stuck "length type")
  | .payable a => do
    match ← getV (← evalE G F n a) with
    | .address x | .contract x => return .val (.address x)
    | _ => halt (.stuck "payable")
  | .call (rs := rs) d _ args => do
    let vs ← evalConvArgs G F n args
    let (r, _) ← sub (L0 E) (callInternal G F n d vs rs)
    return r
  | .magic (τ := τ) b m _ =>
    match b, m, τ with
    | .msg, "sender", .address _ => pure (.val (.address F.sender))
    | .msg, "value", .int t => do return .val (← lift (mkInt t F.value.val))
    | .block, "timestamp", .int t => do return .val (← lift (mkInt t G.timestamp.val))
    | _, _, _ => halt (.stuck "magic member")
  | .balance a => do
    match ← getV (← evalE G F n a) with
    | .address x =>
      let s ← st
      let w := match (s.ex.world.accounts x).code with
        | some _ => (s.ex.world.accounts x).balance
        | none => G.fixed.ledger G.balance0 s.events x
      return .val (intWrap IntTy.u256 w.val)
  | .builtin (τ := τ) b args _ => evalBuiltin G F n b args τ
  | .member (τ := τ) a i _ => do
    match ← getV (← evalE G F n a) with
    | .storRef _ p => return .val (← readLoc F (Loc.stor (τ := τ) (p.go (.field i))))
    | .memRef _ addr => return .val (← readLoc F (Loc.mem (τ := τ) addr i))
    | _ => halt (.stuck "member of calldata")
  | .structNew (dn := dn) _ args => do
    let vs ← evalConvArgs G F n args
    let fs ← fieldsOf vs (E.layout.fields dn)
    return .val (← allocRef (Data.struct (l := .memory) (d := dn) fs))
  | .extCall (rs := rs) target d _ value args => do
    let a ← match ← getV (← evalE G F n target) with
      | .contract x => pure x
    let v ← match ← getV (← evalE G F n value) with
      | .int x _ => pure x
    let vs ← evalConvArgs G F n args
    let ps := match d.fnSig E with | some (ps, _) => ps | none => []
    let input := G.selector (sigOf E.layout d.name ps) ++ (← encodeVals F n false vs.toR)
    let out ← (Prod.fst <$> sub (L0 E) (callAddr G F n a ⟨v.toNat % 2 ^ 256, Nat.mod_lt _ (by decide)⟩ input
      (d.fnMut == some .view || d.fnMut == some .pure)))
    let data ← reraise out
    return mkRet rs ((← lift (decodeVals E.layout data rs 0)).toR)
  | .transfer a v => do
    let (ok, _) ← pay G F n a v
    if ok then return RVal.unit else halt (.revert [])
  | .send a v => do
    let (ok, _) ← pay G F n a v
    return .val (.bool ok)
  | .abiEncode k args => do
    let vs ← evalArgs G F n args
    let data ← match k, vs with
      | .encode, vs => encodeVals F n false vs
      | .encodePacked, vs => encodeVals F n true vs
      | .encodeWithSelector, .cons s vs => do
        let sel := match ← getV (← convRV F n (.fixedBytes 4 (by decide)) s) with
          | .fixedBytes bs _ => bs
        pure (sel ++ (← encodeVals F n false vs))
      | .encodeWithSignature, .cons s vs => do
        let sig ← bytesOfRV F n s
        pure ((wordBytes (G.fixed.hash sig)).take 4 ++ (← encodeVals F n false vs))
      | _, _ => halt (.stuck "abi arguments")
    return .val (← allocRef (Data.bytes (l := .memory) data))
  | .assignCopy (τ := τ) l rhs _ => do
    let v ← evalE G F n rhs
    match ← evalLoc G F n l with
    | .stor p =>
      match v with
      | .strLit bs => storeData F n τ p (Data.bytes (D := E.layout) (l := .memory) bs)
      | .val x => storeVal F n τ p x
      | _ => halt (.stuck "copy source")
      return .val (← storRef τ p)
    | _ => halt (.stuck "copy target")
termination_by structural n

/-- Two operands in the pipeline's order: right first under legacy, left
first via IR; the values in source order. -/
def evalPair (G : Glob E) (F : Fr) (n : Nat) {Γ : RCtx} {σ τ : STy} (a : RExpr E Γ σ) (b : RExpr E Γ τ) :
    EM E Γ (RVal E.layout σ × RVal E.layout τ) :=
  match n with
  | 0 => halt .timeout
  | n + 1 =>
    match G.pipeline with
    | .legacy => do
      let y ← evalE G F n b
      let x ← evalE G F n a
      pure (x, y)
    | .viaIR => do
      let x ← evalE G F n a
      let y ← evalE G F n b
      pure (x, y)
termination_by structural n

/-- Arguments, left to right. -/
def evalArgs (G : Glob E) (F : Fr) (n : Nat) {Γ : RCtx} {τs : List STy} (es : RArgs E Γ τs) :
    EM E Γ (RVals E.layout τs) :=
  match n with
  | 0 => halt .timeout
  | n + 1 =>
    match es with
    | .nil => pure .nil
    | .cons e es => do
      let v ← evalE G F n e
      pure (.cons v (← evalArgs G F n es))
termination_by structural n

/-- Arguments converted to parameter types, left to right. -/
def evalConvArgs (G : Glob E) (F : Fr) (n : Nat) {Γ : RCtx} {τs : List STy} (es : RConvArgs E Γ τs) :
    EM E Γ (Vals E.layout τs) :=
  match n with
  | 0 => halt .timeout
  | n + 1 =>
    match es with
    | .nil => pure .nil
    | .cons (τ := τ) e _ es => do
      let v ← getV (← convRV F n τ (← evalE G F n e))
      pure (.cons v (← evalConvArgs G F n es))
termination_by structural n

/-- **Lvalues** as locations: the base, then the index or key. -/
def evalLoc (G : Glob E) (F : Fr) (n : Nat) {Γ : RCtx} {τ : STy} (l : RLVal E Γ τ) :
    EM E Γ (Loc E.layout Γ τ) :=
  match n with
  | 0 => halt .timeout
  | n + 1 =>
    match l with
    | .local i => pure (.local i)
    | .state d _ _ => pure (.stor d.path)
    | .indexArray a _ i _ => do
      let av ← getV (← evalE G F n a)
      let k ← indexNat (← evalE G F n i)
      indexLoc F av k
    | .indexMapping a k => do
      match ← getV (← evalE G F n a) with
      | .storRef _ p => pure (.stor (p.go (← keyStep F n (← evalE G F n k))))
      | _ => halt (.stuck "mapping not in storage")
    | .indexBytes a _ i _ => do
      let av ← getV (← evalE G F n a)
      let k ← indexNat (← evalE G F n i)
      match av with
      | .memRef _ addr => pure (.memByte addr k)
      | .storRef _ p =>
        if k < (← readLen F p) then pure (.stor (p.go (.index k))) else lift (panic .index)
      | _ => halt (.stuck "byte index")
    | .member a _ i _ => do
      match ← getV (← evalE G F n a) with
      | .storRef _ p => pure (.stor (p.go (.field i)))
      | .memRef _ addr => pure (.mem addr i)
      | _ => halt (.stuck "member")
termination_by structural n

/-- **Builtin functions**: every argument evaluated (left to right;
`addmod`/`mulmod` right to left under legacy), then the function. -/
def evalBuiltin (G : Glob E) (F : Fr) (n : Nat) {Γ : RCtx} {σs : List STy} (b : Builtin)
    (args : RArgs E Γ σs) (τ : STy) : EM E Γ (RVal E.layout τ) :=
  match n with
  | 0 => halt .timeout
  | n + 1 => do
    let vs ← if (b = .addmod || b = .mulmod) && G.pipeline = .legacy then evalArgsRev G F n args
      else evalArgs G F n args
    let res : EM E Γ (RVal E.layout τ) := do
      if h : τ = .tuple [] then return h ▸ RVal.unit else halt (.stuck "builtin result")
    match b, vs with
    | .require, .cons c rest => do
      match ← getV c with
      | .bool true => res
      | _ =>
        match rest with
        | .cons m _ => halt (.revert (errorData (← bytesOfRV F n m)))
        | _ => halt (.revert [])
    | .assert, .cons c _ => do
      match ← getV c with
      | .bool true => res
      | _ => lift (panic .assert)
    | .revert, .nil => halt (.revert [])
    | .revert, .cons m _ => halt (.revert (errorData (← bytesOfRV F n m)))
    | .keccak256, .cons x _ => do
      let bs ← bytesOfRV F n (← convRV F n (.bytes .memory) x)
      ret32 τ (wordBytes (G.fixed.hash bs))
    | .sha256, .cons x _ => do
      let bs ← bytesOfRV F n (← convRV F n (.bytes .memory) x)
      ret32 τ ((G.fixed.evm.precompile .sha256 bs).getD [])
    | .ripemd160, .cons x _ => do
      let bs ← bytesOfRV F n (← convRV F n (.bytes .memory) x)
      ret32 τ (((G.fixed.evm.precompile .ripemd160 bs).getD []).drop 12)
    | .addmod, .cons x (.cons y (.cons k _)) | .mulmod, .cons x (.cons y (.cons k _)) => do
      let u := fun {σ : STy} (v : RVal E.layout σ) => do
        match ← getV (← convRV F n (.int IntTy.u256) v) with
        | .int i _ => pure i
      let (a, c, m) ← match G.pipeline with
        | .legacy => do let m ← u k; let c ← u y; let a ← u x; pure (a, c, m)
        | .viaIR => do let a ← u x; let c ← u y; let m ← u k; pure (a, c, m)
      if m = 0 then lift (panic .divZero)
      else
        let r := if b = .addmod then (a + c) % m else (a * c) % m
        match τ with
        | .int t => return .val (intWrap t r)
        | _ => halt (.stuck "addmod type")
    | .ecrecover, .cons h (.cons v (.cons r (.cons s _))) => do
      let w := fun {σ : STy} (x : RVal E.layout σ) (ρ : STy) => do
        match (← getV (← convRV F n ρ x)).word with
        | some w => pure (wordBytes w)
        | none => halt (.stuck "ecrecover argument")
      let input := (← w h STy.bytes32) ++ (← w v (.int IntTy.u8)) ++ (← w r STy.bytes32) ++ (← w s STy.bytes32)
      let out := (G.fixed.evm.precompile .ecrecover input).getD []
      match τ with
      | .address _ => return .val (.address ⟨beValue out % 2 ^ 160, Nat.mod_lt _ (by decide)⟩)
      | _ => halt (.stuck "ecrecover type")
    | _, _ => halt (.stuck "builtin")
termination_by structural n

/-- Arguments, right to left (values in source order). -/
def evalArgsRev (G : Glob E) (F : Fr) (n : Nat) {Γ : RCtx} {τs : List STy} (es : RArgs E Γ τs) :
    EM E Γ (RVals E.layout τs) :=
  match n with
  | 0 => halt .timeout
  | n + 1 =>
    match es with
    | .nil => pure .nil
    | .cons e es => do
      let vs ← evalArgsRev G F n es
      pure (.cons (← evalE G F n e) vs)
termination_by structural n

/-- **A payment** (`transfer`, `send`): the call with value and no data;
whether it succeeded. -/
def pay (G : Glob E) (F : Fr) (n : Nat) {Γ : RCtx} (a : RExpr E Γ (.address true))
    (v : RExpr E Γ (.int IntTy.u256)) : EM E Γ (Bool × Unit) :=
  match n with
  | 0 => halt .timeout
  | n + 1 => do
    let x ← match ← getV (← evalE G F n a) with
      | .address x => pure x
    let w ← match ← getV (← evalE G F n v) with
      | .int i _ => pure i
    let (out, _) ← sub (L0 E) (callAddr G F n x ⟨w.toNat % 2 ^ 256, Nat.mod_lt _ (by decide)⟩ [] false)
    match out with
    | .success _ => pure (true, ())
    | .revert _ => pure (false, ())
termination_by structural n

/-- **Statement execution** at horizon `n`, in a body with `nps`
parameters (its return slots below them), modifiers' `_` running `ph`. -/
def execS (G : Glob E) (F : Fr) (n : Nat) (nps : Nat) (ph : Option (Ph E)) {R : List STy} {M : Bool}
    {k : SCtx} {Γ Γ' : RCtx} (s : RStmt E R M k Γ Γ') (l : Locals E.layout Γ) :
    EM E [] (Out E.layout Γ Γ') :=
  match n with
  | 0 => halt .timeout
  | n + 1 =>
  match s with
  | .expr e => do
    let (_, l') ← sub l (evalE G F n e)
    pure (.normal l')
  | .placeholder _ => do
    match ph with
    | none => halt (.stuck "placeholder outside a modifier")
    | some ph =>
      let ⟨Γf, lf⟩ := (← st).fnLocals
      if h : Γf = ph.body.locals then
        let cur : Locals E.layout ph.body.locals := h ▸ lf
        let lin ← match G.pipeline with
          | .legacy => pure cur
          | .viaIR => zeroInner n ph.body.rs.length ph.orig
        let lout ← runMods G F n ph.body ph.rest lin
        modSt fun s => { s with fnLocals := ⟨_, lout⟩ }
        pure (.normal l)
      else halt (.stuck "placeholder frame")
  | .declVar τ => do
    let (v, l') ← sub l (zeroVal (E := E) n τ)
    pure (.normal (.cons v l'))
  | .declInit (τ := τ) e _ => do
    let (v, l') ← sub l (do getV (← convRV F n τ (← evalE G F n e)))
    pure (.normal (.cons v l'))
  | .block b => do
    let out ← execItems G F n nps ph b l
    lift out.close
  | .ifThen c t => do
    let (cv, l1) ← sub l (evalE G F n c)
    match ← getV cv with
    | .bool true => do lift (← execS G F n nps ph t l1).close
    | _ => pure (.normal l1)
  | .ifElse c t f => do
    let (cv, l1) ← sub l (evalE G F n c)
    match ← getV cv with
    | .bool true => do lift (← execS G F n nps ph t l1).close
    | _ => do lift (← execS G F n nps ph f l1).close
  | .whileLoop (l := lp) c body => do
    let (cv, l1) ← sub l (evalE G F n c)
    match ← getV cv with
    | .bool true =>
      match ← execS G F n nps ph body l1 with
      | .normal l2 => execS G F n nps ph (.whileLoop (l := lp) c body) (← lift (l2.restore _))
      | .cont l2 => execS G F n nps ph (.whileLoop (l := lp) c body) l2
      | .brk l2 => pure (.normal l2)
      | .ret l2 => pure (.ret l2)
    | _ => pure (.normal l1)
  | .doWhile (l := lp) body c => do
    let l1 ← match ← execS G F n nps ph body l with
      | .normal l2 => lift (l2.restore _)
      | .cont l2 => pure l2
      | .brk l2 => return .normal l2
      | .ret l2 => return .ret l2
    let (cv, l3) ← sub l1 (evalE G F n c)
    match ← getV cv with
    | .bool true => execS G F n nps ph (.doWhile (l := lp) body c) l3
    | _ => pure (.normal l3)
  | .forLoop init c post body => do
    match ← execS G F n nps ph init l with
    | .normal l1 =>
      match ← forIter G F n nps ph c post body l1 with
      | .normal l2 => pure (.normal (← lift (l2.restore _)))
      | .ret l2 => pure (.ret (← lift (l2.restore _)))
      | _ => halt (.stuck "for loop")
    | _ => halt (.stuck "for initializer")
  | .skip => pure (.normal l)
  | .brk => pure (.brk l)
  | .cont => pure (.cont l)
  | .ret _ => pure (.ret l)
  | .retVal (τ := τ) hR e _ => do
    let (v, l1) ← sub l (do getV (← convRV F n τ (← evalE G F n e)))
    let base := Γ.length - (nps + R.length)
    pure (.ret (← lift (l1.setAt base v)))
  | .retTuple es => do
    let (vs, l1) ← sub l (evalConvArgs G F n es)
    pure (.ret (← lift (setRets l1 (Γ.length - (nps + R.length)) vs)))
  | .emit (ps := ps) ev _ args => do
    let (vs, l1) ← sub l (evalConvArgs G F n args)
    let data ← encodeVals F n false vs.toR
    modSt fun s => { s with logs := (F.this, G.selector (sigOf E.layout ev.name ps) ++ data) :: s.logs }
    pure (.normal l1)
  | .revertError (ps := ps) er _ args => do
    let (vs, _) ← sub l (evalConvArgs G F n args)
    let data ← encodeVals F n false vs.toR
    halt (.revert (G.selector (sigOf E.layout er.name ps) ++ data))
  | .rethrow i => do
    match l.get i with
    | .memRef _ a => halt (.revert (← heapBytes a))
    | _ => halt (.stuck "rethrow")
termination_by structural n

/-- The iterations of a `for` loop: condition, body, step. -/
def forIter (G : Glob E) (F : Fr) (n : Nat) (nps : Nat) (ph : Option (Ph E)) {R : List STy} {M : Bool}
    {u : Bool} {Γ₁ Γ₂ : RCtx} (c : ROptBool E Γ₁) (post : ROptExpr E Γ₁)
    (body : RStmt E R M ⟨true, u⟩ Γ₁ Γ₂) (l : Locals E.layout Γ₁) : EM E [] (Out E.layout Γ₁ Γ₁) :=
  match n with
  | 0 => halt .timeout
  | n + 1 => do
    let (go, l1) ← match c with
      | .none => pure (true, l)
      | .some ce => do
        let (cv, l1) ← sub l (evalE G F n ce)
        match ← getV cv with
        | .bool b => pure (b, l1)
    if !go then return .normal l1
    let l2 ← match ← execS G F n nps ph body l1 with
      | .normal l2 => lift (l2.restore _)
      | .cont l2 => pure l2
      | .brk l2 => return .normal l2
      | .ret l2 => return .ret l2
    let l3 ← match post with
      | .none => pure l2
      | .some pe => do pure (← sub l2 (evalE G F n pe)).2
    forIter G F n nps ph c post body l3
termination_by structural n

/-- **Block execution**: items in order; an `unchecked` block's arithmetic
wraps. -/
def execItems (G : Glob E) (F : Fr) (n : Nat) (nps : Nat) (ph : Option (Ph E)) {R : List STy} {M : Bool}
    {k : SCtx} {Γ Γ' : RCtx} (b : RItems E R M k Γ Γ') (l : Locals E.layout Γ) :
    EM E [] (Out E.layout Γ Γ') :=
  match n with
  | 0 => halt .timeout
  | n + 1 =>
  match b with
  | .nil => pure (.normal l)
  | .stmt s rest => do
    match ← execS G F n nps ph s l with
    | .normal l1 => lift ((← execItems G F n nps ph rest l1).up _)
    | .brk l1 => pure (.brk l1)
    | .cont l1 => pure (.cont l1)
    | .ret l1 => pure (.ret l1)
  | .unchecked inner rest => do
    match ← execItems G { F with checked := false } n nps ph inner l with
    | .normal l1 => execItems G F n nps ph rest (← lift (l1.restore _))
    | .brk l1 => pure (.brk l1)
    | .cont l1 => pure (.cont l1)
    | .ret l1 => pure (.ret l1)
termination_by structural n

/-- **A body under its modifiers** (outermost first): each modifier's
arguments in the function's locals, its body with `_` running the rest; the
function's final locals. -/
def runMods (G : Glob E) (F : Fr) (n : Nat) (b : RBody E) (mods : List (RModInv E b.locals))
    (l : Locals E.layout b.locals) : EM E [] (Locals E.layout b.locals) :=
  match n with
  | 0 => halt .timeout
  | n + 1 =>
  match mods with
  | [] => do
    match ← execItems G F n b.ps.length none b.items l with
    | .normal l' => lift (l'.restore _)
    | .ret l' => pure l'
    | _ => halt (.stuck "break outside a loop")
  | m :: rest => do
    let (vs, l1) ← sub l (evalConvArgs G F n m.args)
    match G.prog.body m.modifier with
    | none => halt (.stuck "modifier without a body")
    | some mb =>
      let ml := vs.onto (L0 E)
      if h : m.ps.reverseAux [] = mb.locals then
        let saved := (← st).fnLocals
        modSt fun s => { s with fnLocals := ⟨_, l1⟩ }
        let _ ← execItems G F n mb.ps.length (some ⟨b, rest, l1⟩) mb.items (h ▸ ml)
        let ⟨Γf, lf⟩ := (← st).fnLocals
        modSt fun s => { s with fnLocals := saved }
        if e : Γf = b.locals then pure (e ▸ lf) else halt (.stuck "modifier frame")
      else halt (.stuck "modifier parameters")
termination_by structural n

/-- **An internal call**: virtual dispatch, the parameters and zeroed
return slots as the callee's locals, its modifiers and body, its return
slots as the value; a checked context. -/
def callInternal (G : Glob E) (F : Fr) (n : Nat) (d : Decl) {ps : List STy} (vs : Vals E.layout ps)
    (rs : List STy) : EM E [] (RVal E.layout (STy.ret rs)) :=
  match n with
  | 0 => halt .timeout
  | n + 1 => do
    match G.prog.body (G.dispatchFn F.contract d) with
    | none => halt (.stuck "function without a body")
    | some b =>
      let rv ← zeroVals n rs
      let l0 := rv.onto (vs.onto (L0 E))
      if h : rs.reverseAux (ps.reverseAux []) = b.locals then
        let l' ← runMods G { F with checked := true } n b b.mods (h ▸ l0)
        let out ← lift (retVals l' 0 rs)
        pure (mkRet rs out)
      else halt (.stuck "call frame")
termination_by structural n

/-- **A call to an address** with value and input data, as its caller
sees it: an instance of the system runs in a new frame; another account is
the environment's (G01 events). -/
def callAddr (G : Glob E) (F : Fr) (n : Nat) (a : Address) (v : Word) (input : Bytes) (static : Bool) :
    EM E [] Outcome :=
  match n with
  | 0 => halt .timeout
  | n + 1 => do
    if F.depth ≥ 1024 then return .revert []
    if F.static && v.val ≠ 0 then return .revert []
    match ← instanceAt G a with
    | some c =>
      let m ← mark
      let ok ← if a = F.this then pure true
        else do
          match (← st).ex.transfer F.this a v with
          | some ex' => modSt fun s => { s with ex := ex' }; pure true
          | none => pure false
      if !ok then return .revert []
      enterInstance G n a F.this v input (static || F.static) c (F.depth + 1) m
    | none =>
      if v.val ≠ 0 then
        if !(← debit F.this v) then return .revert []
      emitEvent (.call a v input (static || F.static))
      envLoop G n (F.depth + 1)
termination_by structural n

/-- Running an instance's code in a new frame (fresh memory), its writes
rolled back to `m` on a revert. -/
def enterInstance (G : Glob E) (n : Nat) (a sender : Address) (v : Word) (input : Bytes) (static : Bool)
    (c : String) (depth : Nat) (m : Nat × Nat × Heap E.layout) : EM E [] Outcome :=
  match n with
  | 0 => halt .timeout
  | n + 1 => do
    let F' : Fr := { this := a, sender := sender, value := v, static := static, contract := c, depth := depth }
    modSt fun s => { s with heap := Heap.empty }
    let r ← attempt (dispatch G F' n input)
    modSt fun s => { s with heap := m.2.2 }
    match r with
    | .ok data => pure (.success data)
    | .error (.revert data) => do rollbackTo m; pure (.revert data)
    | .error h => halt h
termination_by structural n

/-- **The environment's moves** while a call of the system is pending:
answers end it; credits and callbacks (into any instance) are recorded and
the strategy is asked again. -/
def envLoop (G : Glob E) (n : Nat) (depth : Nat) : EM E [] Outcome :=
  match n with
  | 0 => halt .timeout
  | n + 1 => do
    match G.callee (← st).events with
    | .answer o => do
      emitEvent (.answer o none)
      pure o
    | .credit t v => do
      emitEvent (.credit t v)
      if (← instanceAt G t).isSome then credit t v
      envLoop G n depth
    | .reenter t sender v input static => do
      emitEvent (.reenter t sender v input static)
      let o ← match ← instanceAt G t with
        | some c => do
          let m ← mark
          credit t v
          enterInstance G n t sender v input static c depth m
        | none => pure (.revert [])
      emitEvent (.reentered o)
      envLoop G n depth
termination_by structural n

/-- **Dispatch** of call data on the instance's contract: the function
whose selector the data starts with (a non-`payable` one refusing value),
its arguments decoded, its returns encoded; `receive` on empty data, else
`fallback`; otherwise a revert. -/
def dispatch (G : Glob E) (F : Fr) (n : Nat) (input : Bytes) : EM E [] Bytes :=
  match n with
  | 0 => halt .timeout
  | n + 1 => do
    let fns := E.exposed F.contract
    let pick := fns.find? fun d => match d.fnSig E with
      | some (ps, _) => G.selector (sigOf E.layout d.name ps) == input.take 4
      | none => false
    match pick, input.isEmpty with
    | some d, false =>
      match d.fnSig E with
      | some (ps, rs) =>
        if F.value.val ≠ 0 && d.fnMut != some .payable then halt (.revert [])
        let vs ← lift (decodeVals E.layout (input.drop 4) ps 0)
        let (r, _) ← sub (L0 E) (callInternal G F n d vs rs)
        encodeVals F n false (← lift (unRet rs r))
      | none => halt (.stuck "signature")
    | _, _ =>
      let special := if input.isEmpty then (E.special F.contract .receive).orElse fun _ => E.special F.contract .fallback
        else E.special F.contract .fallback
      match special with
      | some d =>
        match G.prog.body d with
        | some b =>
          if h : b.locals = [] then
            let _ ← runMods G F n b b.mods (h ▸ L0 E)
            pure []
          else halt (.stuck "fallback with parameters is not modelled")
        | none => halt (.stuck "special function without a body")
      | none => halt (.revert [])
termination_by structural n

end

end Solidity.Source
