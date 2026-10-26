import Solidity.Syntax.Elab.Lower

/-!
# The elaborator's arms

The recursion as a record (`ElabRec`) and the large arms that take it
(`hoistWith`, `abiEncodeWith`, `elabCallRetWith`, `hoistStmtWith`,
`elabStmtPWith`, `elabStmt1With`); `Syntax/Elab/Stmt.lean` ties them.

A piece of `Syntax/Elab.lean`, whose docstring describes the whole.
-/

namespace Solidity

open Semantics

variable {C : Contract}

variable [FreshNames]

section Elab

variable (C)

/-- `ElabRec`'s default (`elabRec` is `partial`): an elaboration that fails. -/
local instance {α : Type} : Inhabited (ElabM α) := ⟨fun _ _ => .error ""⟩

/-- **The elaborator's recursion, as a record**: the functions of the
`mutual` block below that its large arms call.  Those arms are defined
before the block (`hoistWith`, `abiEncodeWith`, `elabCallRetWith`,
`hoistStmtWith`, `elabStmtPWith`, `elabStmt1With`), each taking this record,
and the block ties them (`elabRec`): the block's own declarations stay
small, so that it elaborates and compiles well inside its heartbeats, and
each arm is a command of its own.  Behaviour is the block's: the record's
fields are the block's functions. -/
structure ElabRec where
  hoist : RawExpr → ElabM (SProg C × RawExpr)
  hoistBinop : (op : BinOp) → (a b : RawExpr) → ElabM (SProg C × RawExpr)
  hoistTop : RawExpr → ElabM (SProg C × RawExpr)
  hoistAssign : (l r : RawExpr) → ElabM (SProg C × RawStmt)
  hoistArgs : List RawExpr → ElabM (SProg C × List RawExpr)
  abiMemBytes : (a : RawExpr) → ElabM (SProg C × String)
  abiDecodeBytes : (T : String) → (d : ByteSrc) → (h n : Nat) → ElabM (SProg C × String)
  abiEncode : (std strs : Bool) → (args : List RawExpr) → (marks : List (Option AbiKind)) →
    (sel : Option RawExpr := none) → ElabM (SProg C × RawExpr)
  hoistCallArgs : (f : String) → (args : List RawExpr) → ElabM (SProg C × List RawExpr)
  fnDispatch : (h ty : String) → (args : List RawExpr) → (res : Option (Var × PrimTy)) →
    (resW : Nat) → (resNew : Bool) → ElabM (SProg C)
  callValue : (h : RawExpr) → (args : List RawExpr) → (res : Option (Var × PrimTy)) →
    (resW : Nat) → (resNew : Bool) → ElabM (SProg C)
  elabCall : (f : String) → (args : List RawExpr) → (res : Option (Var × PrimTy)) →
    (resW : Nat := 256) → (resNew : Bool := false) → ElabM (SProg C)
  elabMemCall : (f : String) → (args : List RawExpr) → (R : RefTy) →
    (bind : (Γ : NCtx) → Var → (Ty.ref R).mapFree = true → Except String (SStmt C)) →
    ElabM (SProg C)
  elabStorageCall : (f : String) → (args : List RawExpr) → (R : RefTy) →
    (bind : (Γ : NCtx) → Var → Except String (SStmt C)) → ElabM (SProg C)
  elabCallReceiver : (f : String) → (args : List RawExpr) →
    (op : (Γ : NCtx) → (E : Ty) → ElabM (ReceiverOp C Γ.ctx E)) → ElabM (SProg C)
  elabCallReceiverPush : (f : String) → (args : List RawExpr) → (a : RawExpr) → ElabM (SProg C)
  trySelfBody : (g : String) → {Γ : NCtx} → (args : List (ExtArg C Γ.ctx)) → (ρ : Ctx) →
    ElabM (Option ((ps : Ctx) × (Γf : Ctx) × Args C Γ.ctx ps × Prog C (ρ ++ ps) Γf))
  elabValueCall : (Γ : NCtx) → (ix : Idx Γ.ctx (.val .bool)) → (okName : RawExpr) →
    (e a : RawExpr) → ElabM (SProg C)
  elabCtor : (args : List RawExpr) → ElabM (SProg C)
  hoistStmt : RawStmt → ElabM (SProg C × RawStmt)
  elabStmtP : (s : RawStmt) → ElabM (SProg C)
  elabStmt1 : RawStmt → ElabM (SProg C)
  loopExpr : (Γ : NCtx) → (p : PrimTy) → (e : RawExpr) → (what : String) → ElabM (Val C Γ.ctx p)
  loopQ : (Γ : NCtx) → RawInv → ElabM (LoopQ C Γ.ctx)
  elabStmtsP : List RawStmt → ElabM (SProg C)
  elabBranch : (ss : List RawStmt) → ElabM (SProg C)
  elabScope : (Γ : NCtx) → (ss : List RawStmt) → ElabM (Blk C Γ.ctx)
  elabTuple : (ts : List (Option RawExpr)) → (rhs : RawExpr) → (direct : Bool := false) →
    ElabM (SProg C)
  deriving Inhabited

/-- `hoist`, outside its `mutual` block (`elabRec`). -/
def hoistWith (rc : ElabRec C) : RawExpr → ElabM (SProg C × RawExpr) := fun s0 =>
  let hoist := @ElabRec.hoist C rc
  let hoistBinop := @ElabRec.hoistBinop C rc
  let hoistArgs := @ElabRec.hoistArgs C rc
  let abiMemBytes := @ElabRec.abiMemBytes C rc
  let abiDecodeBytes := @ElabRec.abiDecodeBytes C rc
  let abiEncode := @ElabRec.abiEncode C rc
  let hoistCallArgs := @ElabRec.hoistCallArgs C rc
  let elabCall := @ElabRec.elabCall C rc
  let elabMemCall := @ElabRec.elabMemCall C rc
  let elabStorageCall := @ElabRec.elabStorageCall C rc
  let elabStmtsP := @ElabRec.elabStmtsP C rc
  let abiMarks := abiMarks C
  do
  let s0 ← s0.foldConst
  match s0 with
  | .field e f => do
    let (P, e) ← hoist e
    -- `rows[i].length` of a fixed-size `rows[i]`: the base is evaluated (and
    -- may revert) although the length is the literal, so it is captured
    if f == "length" && e.hasIndex then
      match synth C (← nctx) e with
      | .ok (.path (.ref (.fixed ..)) _) | .ok (.mpath (.ref (.fixed ..)) _) =>
        let (Pc, e) ← captureExpr C e
        return (P ++ Pc, .field e f)
      | _ => pure ()
    pure (P, .field e f)
  | .index e k => do
    -- the base first, then the index: `matrix[k][k++]` indexes `matrix[0]`
    let (P, e) ← hoist e
    if k.hasIncDec then
      let ec ← ctx
      let rebinds := k.any fun
        | .assign target _ => storageMappingAlias? C ec target
        | _ => false
      let (Pc, e) ← if storageMappingAlias? C ec e && rebinds then forceArg C e
        else captureExpr C e
      let (Q, k) ← hoist k
      pure (P ++ Pc ++ Q, .index e k)
    else if k.hasIdxLen || k.hasCast || hasNarrow C (← ctx) k then
      let (Q, k) ← hoist k
      pure (P ++ Q, .index e k)
    else pure (P, .index e k)
  | .binop op a b => do
    if op.shortCircuits then
      let (P, a) ← hoist a
      if b.hasCall || b.hasIncDec || hasNarrow C (← ctx) b then
        -- the right operand's effects, its calls and its checks run only where
        -- solc evaluates it: `bool se = a; if (se) { se = b; }` for `&&`, the
        -- negated test for `||` (solkey's `logicalAndShortCircuitRhs`)
        let x := toString (← freshCapture "se")
        let test := if op == .and then RawExpr.name x else .unop .not (.name x)
        let Q ← elabStmtsP [.decl (.named "bool") x (some a), .ite test [.assign (.name x) b] []]
        return (P ++ Q, .name x)
      pure (P, .binop op a b)
    else
      let (P, e) ← hoistBinop op a b
      let (Q, e) ← narrowCapture C e
      pure (P ++ Q, e)
  | .unop op a => do
    let (P, a) ← hoist a
    let (Q, e) ← narrowCapture C (.unop op a)
    pure (P ++ Q, e)
  | .ternary c a b => do
    let (P, c) ← hoist c
    if a.hasCall || b.hasCall || a.hasIncDec || b.hasIncDec ||
        hasNarrow C (← ctx) a || hasNarrow C (← ctx) b then
      -- a branch's effects, calls and checks run only in the branch solc
      -- evaluates: `T se; if (c) { se = a; } else { se = b; }`, solkey's
      -- `ternaryToIf` on a capture.  `T` is the type of the branch that is
      -- not a literal, read after its effects are hoisted, which is undone
      let typed := if a.isLit then b else a
      let st ← get
      let (_, typed) ← hoist typed
      let ⟨_, t⟩ ← synthM C typed
      let w := widthIn C (← ctx) typed
      set st
      let some ⟨p, _⟩ := t.toVal? | throw "a conditional of references with effects in a branch"
      let x := toString (← freshCapture "se")
      let Q ← elabStmtsP [.decl (.named (tyName p w)) x none,
        .ite c [.assign (.name x) a] [.assign (.name x) b]]
      return (P ++ Q, .name x)
    let Γ ← nctx
    match synth C Γ a, synth C Γ b with
    | .ok (.path (.ref R) pa), .ok (.path (.ref R') pb) =>
      if hR : R' = R then
        let c ← checkIn C Γ .bool c
        let x ← captureRef C "sp" (.alias R) a
        let ⟨Γ', th, ix⟩ ← afterCapture Γ x (.alias R)
        pure (P ++ [.of Γ (.declStorage R x none),
          .of Γ' (.ite (c.wk th) (.cons (.rebind ix (.path (pa.wk th))) .nil)
            (.cons (.rebind ix (.path ((hR ▸ pb).wk th))) .nil))], .name (toString x))
      else throw "a conditional of two reference types"
    | .ok (.mpath (.ref R) pa), .ok (.mpath (.ref R') pb) =>
      if hR : R' = R then
        let pb := hR ▸ pb
        let c ← checkIn C Γ .bool c
        let x ← captureRef C "mv" (.mem R) a
        -- declared before the branches, bound to a branch whose read cannot
        -- revert (or, both indexing, to a fresh default object), then rebound
        -- in each branch to the one the condition takes
        let decl : Stmt C Γ.ctx (.mem R :: Γ.ctx) ←
          match (if pa.indexFree then some pa else if pb.indexFree then some pb else none) with
          | some p => pure (Stmt.declMem R x (some (.alias p)) rfl pa.mapFree)
          | none => match hd : (Ty.ref R).defaultOkS with
            | true => pure (Stmt.declMem R x none (by simp only [Option.isSome_none, hd, Bool.or_true]) pa.mapFree)
            | false => throw s!"a conditional of two indexed memory {Ty.ref R}s, whose default is not well-formed"
        let ⟨Γ', th, ix⟩ ← afterCapture Γ x (.mem R)
        pure (P ++ [.of Γ decl, .of Γ' (.ite (c.wk th) (.cons (.rebindMem ix (.alias (pa.wk th))) .nil)
            (.cons (.rebindMem ix (.alias (pb.wk th))) .nil))],
          .name (toString x))
      else throw "a conditional of two reference types"
    | .ok (.path (.ref _) _), .ok (.mpath ..) | .ok (.mpath ..), .ok (.path (.ref _) _) =>
      throw "a conditional of a storage and a memory reference"
    | _, _ => pure (P, .ternary c a b)
  | .incDec op e => do
    let (P, e) ← hoist e
    let (pre, ⟨Γ, p, t, hs⟩) ← elabIncTarget C e
    match hp : p.isNumeric with
    | true =>
      let n := widthIn C (← ctx) e
      let x ← captureAs C "se" (.val p n)
      let ⟨Γ', th, ix⟩ ← afterCapture Γ x (.val p)
      pure (P ++ pre ++ [.of Γ (.declLocal p x none),
          .of Γ' (.assignIncDec ix op hp (t.wk th) ((OpLoc.recvSimple_wk th t).trans hs))] ++
          (← narrowCheck C p n e),
        .name (toString x))
    | false => throw s!"++ or −− at {p.toStr}"
  | .named f ns args => do
    -- the members' order; an effect may not move
    let flds := (C.structFields f).map (·.1)
    if flds.isEmpty then throw s!"{f}(\{…}): {f} is not a struct or a function declared before this one"
    unless ns.length == flds.length && flds.all ns.contains do
      throw s!"{f}(\{…}) names each member of {f} once: {flds}"
    if ns != flds && args.any (·.hasIncDec) then
      throw s!"{f}(\{…}): an argument with an effect, out of the members' order"
    hoist (.call f (flds.map fun g => (lookupBy g (ns.zip args)).getD (.num 0)))
  | .modular op a b k => do
    -- Reject a statically zero modulus before captures can hide the literal.
    if let .ok (.simple (.lit n _)) := check C (← nctx) .uint k then
      if n == 0 then throw s!"{op.toStr}: arithmetic modulo zero"
    if C.evalOrder.modularLeftToRight then
      let (P, args) ← hoistArgs [a, b, k]
      let [a, b, k] := args | throw "internal: modular argument capture changed arity"
      return (P, .modular op a b k)
    -- Legacy solc checks the modulus before evaluating the other arguments.
    -- Save it once: an operand's later effects may change its source.
    let (P, k) ← hoist k
    let (Pc, k) ← captureExpr C k
    let Γ ← nctx
    let guard ← checkIn C Γ .bool (.binop .neB k (.num 0))
    let (Q, args) ← hoistArgs [b, a]
    let [b, a] := args | throw "internal: modular argument capture changed arity"
    pure (P ++ Pc ++ [.of Γ (.require guard)] ++ Q, .modular op a b k)
  | .newArr T n => do
    let (P, n) ← hoist n
    let ⟨R, hR⟩ ← elabNewTy C T
    let (Q, ⟨Γ, se⟩) ← elabSize C n
    let x ← captureRef C "mv" (.mem R) (.newArr T n)
    pure (P ++ Q ++ [.of Γ (.declMem R x (some (.newArr se hR)) rfl
      (MRhs.newArr (C := C) se hR).mapFree)], .name (toString x))
  | .call "#sliceIndex" [off, len, k, past] => do
    let (P, k) ← hoist k
    let x := toString (← freshCapture "se")
    let Q ← elabStmtsP [.decl (.named "uint") x (some k)]
    -- The addition is evaluated only for an in-range relative index.
    -- The base's own bounds check supplies Panic(0x32) otherwise.
    let ix := RawExpr.ternary (.binop .lt (.name x) len) (sliceAdd off (.name x)) past
    let (R, ix) ← hoist ix
    pure (P ++ Q ++ R, ix)
  | .call "#sliceAt" [view, k] => do
    let t := toString (← freshCapture "mv")
    let (v, pre) ← ElabM.lift (inlineSliceOpen t view)
    let P ← elabStmtsP pre
    let (Q, e) ← hoist (.index (.name v.base)
      (.call "#sliceIndex" [v.off, v.len, k, .field (.name v.base) "length"]))
    pure (P ++ Q, e)
  | .call "#sliceLength" [view] => do
    let t := toString (← freshCapture "mv")
    let (v, pre) ← ElabM.lift (inlineSliceOpen t view)
    let P ← elabStmtsP pre
    let (Q, e) ← hoist v.len
    pure (P ++ Q, e)
  | .call "#sliceDecode" (view :: rest) => do
    let t := toString (← freshCapture "mv")
    let (v, pre) ← ElabM.lift (inlineSliceOpen t view)
    let P ← elabStmtsP pre
    let (Q, e) ← hoist (.call "abi.decode" (.call sliceViewName [.name v.base, v.off, v.len] :: rest))
    pure (P ++ Q, e)
  | .call "#sliceCopy" [view] => do
    let t := toString (← freshCapture "mv")
    let (v, pre) ← ElabM.lift (inlineSliceOpen t view)
    let P ← elabStmtsP pre
    let Γ ← ctx
    let .mpath (.ref R@(.array (.prim _))) _ ← ElabM.lift (synth C Γ.toNCtx (.name v.base))
      | throw "a slice copy needs a dynamic array of primitive elements; reference elements are refused"
    let ws := exprShape C Γ (.name v.base)
    if ws.any (fun (k, _) => k.endsWith "#enum" || (k.splitOn "#function").length > 1) then
      throw "a slice copy of enum or function elements needs its nominal source type"
    -- rawTyW preserves primitive widths, fixed bytes and address identities.
    -- Dynamic bytes additionally needs its whole-value ABI marker.
    let T := if abiTyName ws "" (.ref R) == some "bytes" then RawTy.named "bytes"
      else rawTyW ws (.ref R) ""
    let L := toString (← freshCapture "se")
    let j := toString (← freshCapture "se")
    let r := toString (← freshCapture "mv")
    -- The bounds have already been checked. For j < L, off + j < fin;
    -- copying primitive elements retains no reference to the input heap.
    -- Use the existing typed allocation, indexing and loop elaboration.
    let Q ← elabStmtsP [
      .decl (.named "uint") L (some v.len),
      .declMemory T r (some (.newArr T (.name L))),
      .decl (.named "uint") j (some (.num 0)),
      .whileLoop {} (.binop .lt (.name j) (.name L)) [
        .assign (.index (.name r) (.name j))
          (.index (.name v.base) (sliceAdd v.off (.name j))),
        .assign (.name j) (.binop .add (.name j) (.num 1))]]
    pure (P ++ Q, .name r)
  | .call "#array" args => do
    let T ← ElabM.lift (inlineArrayTy C (← ctx) args)
    let x := toString (← freshCapture "mv")
    let Q ← elabStmtsP (.declMemory (.fixed T args.length) x none ::
      args.zipIdx.map fun (a, i) => .assign (.index (.name x) (.num i)) a)
    pure (Q, .name x)
  | .call f args => do
    -- a literal of bytes where a `bytes` or a `string` stands: a fresh memory
    -- array of its bytes (`new bytes(n)`, then each byte written)
    if let some bs := (RawExpr.call f args).bytesLit? then
      let x := toString (← freshCapture "mv")
      let Q ← elabStmtsP (.declMemory (.named "bytes") x (some (.newArr (.named "bytes") (.num bs.length))) ::
        bs.zipIdx.map fun (b, i) => .assign (.index (.name x) (.num i)) (.num b))
      return (Q, .name x)
    let builtin := (← read).funs.all (·.1 != f)
    if builtin && f.startsWith "#bytesPrefix" then
      let some n := (f.drop 12).toNat? | throw "a fixed byte prefix needs its width"
      unless 0 < n && n ≤ 32 do throw "a fixed byte prefix needs one through 32 bytes"
      let [a] := args | throw "a fixed byte prefix takes one bytes argument"
      unless dynamicBytesExpr C (← ctx) a do
        throw "a fixed byte prefix takes bytes, not another reference type"
      let a := match a with | .call "bytes" [v] => v | _ => a
      let (P, a) ← hoist a
      ElabM.lift (shapeCheck C (← ctx) dynBytesRows a)
      let (Q, b) ← abiMemBytes a
      let w := toString (← freshCapture "se")
      let step (i : Nat) : RawStmt :=
        .ite (.binop .lt (.num i) (.field (.name b) "length"))
          [.assign (.name w) (.binop .add (.binop .mul (.name w) (.num 256))
            (.call "uint8" [.index (.name b) (.num i)]))]
          [.assign (.name w) (.binop .mul (.name w) (.num 256))]
      let R ← elabStmtsP (.decl (.named "uint") w (some (.num 0)) :: (List.range n).map step)
      let (S, value) ← hoist (.call (tyName .uint (8 * n)) [.name w])
      return (P ++ Q ++ R ++ S, value)
    if builtin && f == "erc7201" then return ← hoistERC7201With C hoist args
    -- the hashing builtins (`hoistHashWith`)
    if builtin && isHashName f then return ← hoistHashWith C hoist abiMemBytes elabStmtsP f args
    -- `abi.encodeWithSelector(s, …)`, `abi.encodeWithSignature(sig, …)`,
    -- `abi.encodeCall(g, (…))`: the selector's four bytes, then `abi.encode(…)`
    -- of the rest; a literal signature's selector and a function's folded as
    -- solc folds them (`Keccak.selector`), another signature's the first four
    -- bytes of its `keccak256`
    if builtin && (f == "abi.encodeWithSelector" || f == "abi.encodeWithSignature" ||
        f == "abi.encodeCall") then
      let some (sel, rest) ← ElabM.lift (encodeSelector? C (← ctx) f args)
        | throw s!"{f}: its selector or signature first"
      -- Only the selector is encoded, but evaluating a computed receiver may
      -- still panic or have effects. Preserve it before evaluating arguments.
      let H ← match f, args with
        | "abi.encodeCall", [.field r _, _] => do
          if r.isPure then pure [] else
            let (P, r) ← hoist r
            let (Q, _) ← captureExpr C r
            pure (P ++ Q)
        | _, _ => pure []
      -- a `bytes4` already marked (`bytesPure`) is marked once
      let sel := match sel with
        | .call g [x] => if (abiBytesMark? g).isSome then x else sel
        | _ => sel
      let (P, sel) ← hoist sel
      -- a `bytesN` argument marked (`abiBytesMark`), a literal byte string in place
      let marks ← abiMarks rest
      let rest := rest.map fun a => match a with
        | .call g [x] => if (abiBytesMark? g).isSome then x else a
        | _ => a
      let (Q, rest') ← hoistArgs (rest.map fun a => if a.bytesLit?.isSome then .num 0 else a)
      let rest := (rest.zip rest').map fun (a, a') => if a.bytesLit?.isSome then a else a'
      let (R, e) ← abiEncode true false rest marks (sel := some sel)
      return (H ++ P ++ Q ++ R, e)
    if builtin && (f == "abi.encode" || f == "abi.encodePacked" || f == "string.concat" ||
        f == "bytes.concat") then
      -- a `bytesN` marked (`abiBytesMark`); a literal byte string is not
      -- allocated: its bytes are written in place
      let marks ← abiMarks args
      let args := args.map fun a => match a with
        | .call g [x] => if (abiBytesMark? g).isSome then x else a
        | _ => a
      let (P, args') ← hoistArgs (args.map fun a => if a.bytesLit?.isSome then .num 0 else a)
      let args := (args.zip args').map fun (a, a') => if a.bytesLit?.isSome then a else a'
      let (Q, e) ← abiEncode (f == "abi.encode") (f == "string.concat") args marks
      return (P ++ Q, e)
    -- `abi.decode(b, (T))`, `#abiDecode(b, T, i, n)` (`abiDecodeWith`)
    if builtin && (f == "abi.decode" || f == abiDecodeName) then
      return ← abiDecodeWith C hoist abiMemBytes elabStmtsP abiDecodeBytes f args
    if builtin && f == "address" then
      let [a] := args | throw "an address conversion takes one argument"
      let (P, a) ← hoist a
      let (Q, e) ← addressCapture C a
      return (P ++ Q, e)
    if let some ms := lookupBy f C.enums then
      let [a] := args | throw s!"a conversion {f}(…) takes one argument"
      let (P, a) ← hoist a
      let (Q, e) ← enumCapture C ms.length a
      return (P ++ Q, e)
    if (castTy? f).isSome then
      let [a] := args | throw s!"a cast {f}(…) takes one argument"
      let (P, a) ← hoist a
      let (Q, e) ← castCapture C f a
      return (P ++ Q, e)
    -- Legacy code generation allocates the struct, then evaluates and
    -- writes each field. IR evaluates every field (including implicit
    -- storage-to-memory copies) before allocating the enclosing object.
    -- Generic call argument hoisting must not move a field's failure ahead
    -- of the legacy allocation or defer the IR's final field until after it.
    let flds := C.structFields f
    if (← read).funs.all (·.1 != f) && !flds.isEmpty then
      unless flds.length == args.length do
        throw s!"{f} has {flds.length} members, not {args.length}"
      let (P, args) ← if C.evalOrder.binaryLeftToRight then do
          let some structName := C.structName? f | throw s!"{f}: a struct declaration"
          let mut P : SProg C := []
          let mut values : List RawExpr := []
          for ((g, T), a) in flds.zip args do
            let y := toString (← freshCapture (match T with | .prim _ => "se" | .ref _ => "mv"))
            let rawType := rawTyW (structWidths structName) T g
            let declaration := match T with
              | .prim _ => RawStmt.decl rawType y (some a)
              | .ref _ => RawStmt.declMemory rawType y (some a)
            let Q ← elabStmtsP [declaration]
            P := P ++ Q
            values := values ++ [.name y]
          pure (P, values)
        else pure ([], args)
      let x := toString (← freshCapture "mv")
      let Q ← elabStmtsP (.declMemory (.named f) x none ::
        (flds.zip args).map fun ((g, _), a) => .assign (.field (.name x) g) a)
      return (P ++ Q, .name x)
    -- a call through a value that is not a name (`callValue`): its callee's
    -- type, from the callee
    if f == callValueName then
      let h :: rest := args | throw "internal: a call through a value with no callee"
      if let .name g := h then
        if (← read).funs.any (·.1 == g) then return ← hoist (.call g rest)
      let some ty := fnTyOfExpr C (← ctx) h | throw s!"{h.toStr}(…): the callee is not a function value"
      let (P, rest) ← hoistArgs rest
      let some (_, [r], _) := fnParts? ty | throw s!"{h.toStr}(…) returns one value where a value stands"
      let some (p, n) := fnCompTy? C r | throw s!"{h.toStr}(…) returns a {r}, not a value type"
      let Γ ← nctx
      let x ← freshCapture "se"
      let Q ← elabCall f (h :: rest) (some (x, p)) n (resNew := true)
      declare C (toString x) (.val p n)
      declareShape (toString x) (← ElabM.lift (bytesRowsOf C (.named r)))
      return (P ++ [.of Γ (.declLocal p x none)] ++ Q, .name (toString x))
    -- a call through a function value, into a fresh local (`fnDispatch`)
    if (← read).funs.all (·.1 != f) then
      if let some ty := fnTyOf? C (← ctx) f then
        let (P, args) ← hoistArgs args
        let some (_, [r], _) := fnParts? ty | throw s!"{f}(…) returns one value where a value stands"
        let some (p, n) := fnCompTy? C r | throw s!"{f}(…) returns a {r}, not a value type"
        let Γ ← nctx
        let x ← freshCapture "se"
        let Q ← elabCall f args (some (x, p)) n (resNew := true)
        declare C (toString x) (.val p n)
        declareShape (toString x) (← ElabM.lift (bytesRowsOf C (.named r)))
        return (P ++ [.of Γ (.declLocal p x none)] ++ Q, .name (toString x))
    -- a call inside an expression runs before the statement, into a fresh local
    let (P, args) ← hoistCallArgs f args
    let some (_, d) := (← read).funs.find? (·.1 == f) | throw s!"{f} is not a function declared before this one"
    match d.ret with
      | some (r, .prim p) =>
        let n := (lookupBy r d.widths).getD 256
        let Γ ← nctx
        let x ← freshCapture "se"
        let Q ← elabCall f args (some (x, p)) n (resNew := true)
        declare C (toString x) (.val p n)
        declareShape (toString x) (shapeUnder d.widths r)
        pure (P ++ [.of Γ (.declLocal p x none)] ++ Q, .name (toString x))
      | some (r, .ref R) =>
        if d.retStorage then
          let x ← freshCapture "sp"
          let Q ← elabStorageCall f args R fun Γ r =>
            pure (.of ((r, .alias R) :: Γ) (.declStorage R x (some (.path (.alias .here)))))
          declare C (toString x) (.alias R)
          declareShape (toString x) (shapeUnder d.widths r)
          return (P ++ Q, .name (toString x))
        -- `Account memory mv1 = makeAccount();`
        let x ← freshCapture "mv"
        let Q ← elabMemCall f args R fun Γ r hm =>
          pure (.of ((r, .mem R) :: Γ) (.declMem R x (some (.alias (.var .here hm))) rfl hm))
        declare C (toString x) (.mem R)
        declareShape (toString x) (shapeUnder d.widths r)
        pure (P ++ Q, .name (toString x))
      | none =>
        if d.rets.isEmpty then throw s!"{f} returns no value"
        else throw s!"{f} returns {d.rets.length} values, which a tuple assignment takes"
  | .tuple _ => throw "a tuple is the right-hand side of a tuple assignment or of a `return`"
  | .assign l r => do
    -- the right-hand side, then the target (`hoistAssign`); the value is the
    -- one written, held first (solkey's `storageCopyAssignmentValue`:
    -- `pv = e; sp = pv; v = pv;`)
    let (P, r) ← hoist r
    -- The expression yields the old RHS reference, even if a later index
    -- rebinds its source alias. A fresh typed snapshot cannot be rebound by
    -- source syntax and retains the same key/value-width metadata.
    let (Pc, r) ← if storageMappingAlias? C (← ctx) l then forceArg C r
      else captureExpr C r
    let Q ← elabStmtsP [.assign l r]
    pure (P ++ Pc ++ Q, r)
  | .opAssign op l r => do
    -- the write, then the target read again (solkey's `localAddAssignmentValue`:
    -- `lv += e; v = lv;`): a target with an effect would run it twice
    if l.hasIncDec then
      throw s!"{(RawExpr.opAssign op l r).toStr}: a compound assignment's value, its target with an effect"
    let Q ← elabStmtsP [.opAssign op l r]
    pure (Q, l)
  | e => pure ([], e)

/-- `abiEncode`, outside its `mutual` block (`elabRec`). -/
def abiEncodeWith (rc : ElabRec C) (std strs : Bool) (args : List RawExpr) (marks : List (Option AbiKind))
    (sel : Option RawExpr := none) : ElabM (SProg C × RawExpr) := do
  let abiMemBytes := @ElabRec.abiMemBytes C rc
  let elabStmtsP := @ElabRec.elabStmtsP C rc
  let abiKind := abiKind C
  -- nested types, head and tail recursively (`abiEncodeNested?`)
  if std then
    if let some r ← abiEncodeNested? C abiKind abiMemBytes elabStmtsP args marks sel then return r
  let mut P : SProg C := []
  -- a selector's four bytes first (`abi.encodeWithSelector`), every other
  -- position after them; the head's offsets are the arguments' own
  let base : Nat := if sel.isSome then 4 else 0
  let selW : Option String ← match sel with
    | none => pure none
    | some e => match e.litVal? with
      | some v => pure (some ("#" ++ toString v.toNat))
      | none => do
        let w := toString (← freshCapture "se")
        P := P ++ (← elabStmtsP [.decl (.named "uint") w (some e)])
        pure (some w)
  -- each argument read once: its word in a fresh `uint` (a literal's known),
  -- a byte string in a memory local with its length (a literal's bytes known),
  -- an array or a struct as the place it is (its elements read in order), an
  -- array's length in a fresh `uint`
  let mut parts : List (AbiKind × String × String × Option (List Nat) × RawExpr) := []
  for (a, mark) in args.zip marks do
    let k ← match mark with
      | some k => pure k
      | none => abiKind a
    if strs && k != .dyn then throw "string.concat takes `string`s"
    match k, a.bytesLit? with
    | .dyn, some bs => parts := parts ++ [(k, "", "", some bs, a)]
    | .dyn, none =>
      let (Q, x) ← abiMemBytes a
      let L := toString (← freshCapture "se")
      let R ← elabStmtsP [.decl (.named "uint") L (some (.field (.name x) "length"))]
      P := P ++ Q ++ R
      parts := parts ++ [(k, x, L, none, a)]
    | .arr _, _ =>
      let L := toString (← freshCapture "se")
      P := P ++ (← elabStmtsP [.decl (.named "uint") L (some (.field a "length"))])
      parts := parts ++ [(k, "", L, none, a)]
    | .fixed .., _ => parts := parts ++ [(k, "", "", none, a)]
    | .tuple _, _ =>
      if !std then throw s!"{a.toStr}: abi.encodePacked of a struct (solc refuses it)"
      parts := parts ++ [(k, "", "", none, a)]
    | _, _ =>
      -- an enum's member is its literal position
      let Γn ← nctx
      let lit : Option Nat := match a with
        | .field b g => enumLit? C Γn b g
        | _ => none
      match lit.orElse fun _ => k.litWord? a with
      | some v => parts := parts ++ [(k, "#" ++ toString v, "", none, a)]
      | none =>
        let w := toString (← freshCapture "se")
        P := P ++ (← elabStmtsP [.decl (.named "uint") w (some (k.word a))])
        parts := parts ++ [(k, w, "", none, a)]
  let r := toString (← freshCapture "mv")
  let tot := toString (← freshCapture "se")
  let head := (parts.map fun (k, _) => k.headWords).sum
  let len (L : String) (lit : Option (List Nat)) : RawExpr :=
    match lit with
    | some bs => .num bs.length
    | none => .name L
  let pad : RawExpr → RawExpr
    | .num m => .num ((m + 31) / 32 * 32)
    | e => abiPad e
  let words (L : String) : RawExpr := .binop .mul (.num 32) (.name L)
  let total : RawExpr := parts.foldl (fun acc (k, _, L, lit, _) =>
      match k with
      | .dyn =>
        if std then .binop .add acc ((pad (len L lit)).addN 32) else .binop .add acc (len L lit)
      | .arr _ => if std then .binop .add acc ((words L).addN 32) else .binop .add acc (words L)
      | .tuple _ => acc
      | _ => if std then acc else acc.addN k.packedWidth)
    (.num (base + if std then 32 * head else 0))
  let mut S : List RawStmt := [.decl (.named "uint") tot (some total),
    .declMemory (.named "bytes") r (some (.newArr (.named "bytes") (.name tot)))]
  -- `o`: where the next tail (`std`) or the next value (packed) starts
  let o := toString (← freshCapture "se")
  S := S ++ [.decl (.named "uint") o (some (.num (if std then 32 * head else 0)))]
  if let some w := selW then S := S ++ abiWrite r (.num 0) w 4
  -- `o` at its place in `r`, after the selector
  let atO (k : Nat) : RawExpr := (RawExpr.name o).addN (base + k)
  -- a byte string's bytes at `p`: a literal's written, another's copied
  let bytesAt (p : RawExpr) (x L : String) (lit : Option (List Nat)) : ElabM (List RawStmt) := do
    match lit with
    | some bs =>
      pure (bs.zipIdx.filterMap fun (b, j) =>
        if b == 0 then none else some (.assign (.index (.name r) (p.addN j)) (.num b)))
    | none => pure (abiCopy r x (toString (← freshCapture "se")) L p)
  -- a value `e` of kind `k` as a 32-byte word at `p`: read once into a fresh `uint`
  let wordAt (p : RawExpr) (k : AbiKind) (e : RawExpr) : ElabM (List RawStmt) := do
    let w := toString (← freshCapture "se")
    pure (.decl (.named "uint") w (some (k.word e)) :: abiEncodeStaticE r p k (.name w))
  -- the `L` elements of `x`, each a word, from `p` on
  let elemsAt (p : RawExpr) (k : AbiKind) (x : RawExpr) (L : String) : ElabM (List RawStmt) := do
    let j := toString (← freshCapture "se")
    let body ← wordAt (.binop .add p (words j)) k (.index x (.name j))
    pure [.decl (.named "uint") j (some (.num 0)),
      .whileLoop {} (.binop .lt (.name j) (.name L))
        (body ++ [.assign (.name j) (.binop .add (.name j) (.num 1))])]
  let mut hpos := 0
  for (k, x, L, lit, a) in parts do
    if std then
      match k with
      | .dyn =>
        let lenW : List RawStmt := match lit with
          | some bs => abiLitBytes r (atO 0) bs.length 32
          | none => abiBytes r (atO 0) (.name L) 32
        S := S ++ abiBytes r (.num (base + hpos)) (.name o) 32 ++ lenW ++
          (← bytesAt (atO 32) x L lit) ++
          [.assign (.name o) (.binop .add ((RawExpr.name o).addN 32) (pad (len L lit)))]
      | .arr ek =>
        S := S ++ abiBytes r (.num (base + hpos)) (.name o) 32 ++ abiBytes r (atO 0) (.name L) 32 ++
          (← elemsAt (atO 32) ek a L) ++
          [.assign (.name o) (.binop .add ((RawExpr.name o).addN 32) (words L))]
      | .fixed ek n =>
        for j in [0:n] do S := S ++ (← wordAt (.num (base + hpos + 32 * j)) ek (.index a (.num j)))
      | .tuple s =>
        for ((f, ek), j) in ((AbiKind.ofStruct s).getD []).zipIdx do
          S := S ++ (← wordAt (.num (base + hpos + 32 * j)) ek (.field a f))
      | _ => S := S ++ abiStatic r (base + hpos) k x
    else
      match k with
      | .dyn =>
        S := S ++ (← bytesAt (atO 0) x L lit) ++
          [.assign (.name o) (.binop .add (.name o) (len L lit))]
      -- an array's elements packed each in a word, with no length (solc's)
      | .arr ek =>
        S := S ++ (← elemsAt (atO 0) ek a L) ++
          [.assign (.name o) (.binop .add (.name o) (words L))]
      | .fixed ek n =>
        for j in [0:n] do S := S ++ (← wordAt (atO (32 * j)) ek (.index a (.num j)))
        S := S ++ [.assign (.name o) ((RawExpr.name o).addN (32 * n))]
      | _ =>
        S := S ++ abiWrite r (atO 0) x k.packedWidth ++
          [.assign (.name o) ((RawExpr.name o).addN k.packedWidth)]
    hpos := hpos + 32 * k.headWords
  pure (P ++ (← elabStmtsP S), .name r)

/-- Every local of the callee ends with its call: no return variable is
left in the caller (a reference return's, `CallRet.mem`/`storage`). -/
def FunDecl.endsWithCall (d : FunDecl) : Bool :=
  !d.retMem && !d.retStorage && d.rets.all fun (_, T) => match T with | .prim _ => true | _ => false

/-- A callee's body as its frame runs it: its locals renamed (`ρ`), its loops
and `return`s lowered, its modifiers around it, a constructor's initializers
first, a self-call's environment, a block's locals renamed apart. -/
def calleeBody (d : FunDecl) (ρ : List (String × String)) (ctor selfFrame : Bool) (Γf : ECtx) :
    ElabM (List RawStmt) := do
  let body ← renameStmts ρ d.body
  let body ← lowerLoops (some (d.rets.map fun (n, _) => (lookupBy n ρ).getD n)) body
  let body ← ElabM.lift (lowerReturns (d.rets.map fun (n, _) => (lookupBy n ρ).getD n) body)
  let body ← wrapMods body (d.mods.map fun m => { m with args := m.args.map (·.rename ρ) })
  -- a constructor's initializers: after its parameters are bound, before its
  -- modifiers, in declaration order (solkey's `ExpandFunctionBody`)
  let body := (if ctor then C.inits.map fun (x, e) => RawStmt.assign (.name x) e else []) ++ body
  -- an external call of the contract to itself: its frame's environment
  let selfValue := (← read).selfValue
  let body := if selfFrame then body.map (RawStmt.selfFrame selfValue) else body
  -- a block's locals renamed apart (a modifier's `_;` twice repeats the body's)
  ElabM.lift (freshenBlocks (C.vars.map (·.1)) (Γf.map (·.1)) body)

/-- The body of a callee inlined at its call, elaborated in its frame `Γf`
from the caller's `Γ`, its locals numbered from `k₀`.  A `shared` callee's
(`CallMemo`) is elaborated at its first call only: a later call, numbered
from the same `k₀`, reads it back (`CallMemo.body?`), the same body. -/
def inlinedBody (rc : ElabRec C) (f : String) (d : FunDecl) (ρ : List (String × String))
    (shared ctor selfFrame : Bool) (scope : List (Name × FunDecl)) (k₀ : Nat) (Γ Γf : ECtx) :
    ElabM (SProg C) := do
  let key := calleeKey f selfFrame (← read)
  if shared then
    if let some (P, kEnd) ← CallMemo.body? C key k₀ then
      modify fun (Γc, _) => (Γc, kEnd)
      return P
  let body ← calleeBody C d ρ ctor selfFrame Γf
  let k₁ := (← get).2
  modify fun (_, k) => (Γf, k)
  let P ← withReader (fun sc =>
      { sc with funs := scope, top := false, selfFrame := selfFrame, unchecked := false,
                inlined := (k₀, k₁) :: sc.inlined })
    (@ElabRec.elabStmtsP C rc body)
  modify fun (_, k) => (Γ, k)
  if shared then CallMemo.setBody C key k₀ P (← get).2
  pure P

/-- `elabCallRet`'s elaboration of the call, from the numbering it is entered at. -/
def elabCallRetCore (rc : ElabRec C) (f : String) (args : List RawExpr) (res : Option (Var × PrimTy))
    (resW : Nat := 256) (targets : Bool := false) (ctor : Bool := false) (resNew : Bool := false)
    (selfFrame : Bool := false) :
    ElabM (SProg C × Option (NCtx × RefTy × Var × Bool) × List (PrimTy × Var × Nat)) := do
  let fnDispatch := @ElabRec.fnDispatch C rc
  let callValue := @ElabRec.callValue C rc
  let elabStmtsP := @ElabRec.elabStmtsP C rc
  let funs := (← read).funs
  -- a call through a value that is not a name (`callValue`)
  if !ctor && f == callValueName then
    let h :: args := args | throw "internal: a call through a value with no callee"
    if targets then throw s!"{h.toStr}(…): a call through a function value in a tuple assignment"
    return (← callValue h args res resW resNew, none, [])
  -- a call through a function value (`fnDispatch`)
  if !ctor && funs.all (·.1 != f) then
    if let some ty := fnTyOf? C (← ctx) f then
      if targets then throw s!"{f}(…): a call through a function value in a tuple assignment"
      return (← fnDispatch f ty args res resW resNew, none, [])
  let selfFrame := selfFrame || (← read).selfFrame
  -- a call of a recursive function whose body is being elaborated: the frame
  -- below, its names the frame's (`ElabScope.recs`)
  let recs := (← read).recs
  let site := if ctor then none else recs.find? (·.name == f)
  let recursive := !ctor && (site.isSome || isRecursiveC C f)
  -- the callee and the functions its body may call: the constructor (`elabCtor`)
  -- may call every function, a function those declared before it, and a
  -- recursive function those it is mutually recursive with too
  let (d, scope) ← if ctor then pure (C.ctor.getD { params := [], body := [] }, C.funs) else
    let some i := funs.findIdx? (·.1 == f) | throw s!"{f} is not a function declared before this one"
    let d := (funs[i]?.map (·.2)).getD default
    if recursive then
      let j := (C.funs.findIdx? (·.1 == f)).getD 0
      let partners := recPartnersC C f
      pure (d, C.funs.take j ++ (C.funs.drop j).filter (partners.contains ·.1))
    else pure (d, funs.take i)
  ElabM.lift (calldataCheck scope 8 d.calldataParams d.refRets d.body)
  -- a recursive function's frame is one context, `rs ++ ps`, at every call:
  -- a call of several returns returns to its targets (`CallRet.rets`)
  if recursive && d.rets.length > 1 && !targets then
    throw s!"{f} is recursive and returns several values: call it in a tuple assignment"
  -- a parameter's or return variable's name: fresh, or the recursive frame's
  let pickName (base : String) (frameNames : RecFrame → List Var) (j : Nat) : ElabM Var :=
    match site with
    | some rf => match (frameNames rf)[j]? with
      | some x => pure x
      | none => throw s!"internal: {f}'s recursive frame has no name {j}"
    | none => freshCapture base
  unless d.params.length == args.length do
    throw s!"{f} takes {d.params.length} arguments, not {args.length}"
  let Γ ← ctx
  let Γn ← nctx
  -- the callee's locals are numbered from here to `k₁` (`ElabScope.inlined`)
  let k₀ := (← get).2
  let mut targs : (ps : Ctx) × Args C Γn.ctx ps := ⟨[], .nil⟩
  let mut ρ : List (String × String) := []
  -- the frame: the parameters, then the return variables, each newest first
  let mut Γp : ECtx := []
  let mut pj := 0
  let mut pnames : List Var := []
  for ((n, T), a) in d.params.zip args do
    match T with
    | .prim p =>
      if (lookupBy n d.paramLocs).isSome then
        throw s!"{f}: data location on value parameter {n}"
      let w := (lookupBy n d.widths).getD 256
      ElabM.lift (fitCheck C Γ p w a)
      let e ← checkIn C Γn p a
      let x ← pickName "se" (·.params) pj
      pnames := pnames ++ [x]
      targs := ⟨_, targs.2.snoc p x e⟩
      ρ := (n, toString x) :: ρ
      Γp := shapeEntry (toString x) (shapeUnder d.widths n) ++ (toString x, .val p w) :: Γp
    | .ref R =>
      match lookupBy n d.paramLocs with
      | some .storage =>
        ElabM.lift (shapeCheck C Γ (shapeUnder d.widths n) a)
        let e ← ElabM.lift (checkPath C Γn (.ref R) a)
        let x ← pickName "sp" (·.params) pj
        pnames := pnames ++ [x]
        targs := ⟨_, targs.2.snocStorage R x e⟩
        ρ := (n, toString x) :: ρ
        Γp := shapeEntry (toString x) (shapeUnder d.widths n) ++ (toString x, .alias R) :: Γp
      | some .memory | some .calldata =>
        ElabM.lift (shapeCheck C Γ (shapeUnder d.widths n) a)
        let e ← ElabM.lift (checkMPath C Γn (.ref R) a)
        let x ← pickName "mv" (·.params) pj
        pnames := pnames ++ [x]
        targs := ⟨_, targs.2.snocMemory R x e⟩
        ρ := (n, toString x) :: ρ
        Γp := shapeEntry (toString x) (shapeUnder d.widths n) ++ (toString x, .mem R) :: Γp
      | none => throw s!"{f}: reference parameter {n} needs a data location"
    pj := pj + 1
  let mut mret : Option (RefTy × Var × Bool) := none
  let mut mrets : List (PrimTy × Var × Nat) := []
  let mut Γr : ECtx := []
  let kind ← match d.rets, res with
    -- a void call with targets (a void function's obligation, `f(x̄)@C;`)
    -- is a `FunctionBodyStatement` all the same
    | [], none => pure (if targets then RetKind.rets [] else RetKind.none)
    | [], some _ => throw s!"{f} returns no value"
    | [(n, .ref R)], none => do
      if targets then throw s!"{f} returns a {Ty.ref R}, which a tuple assignment does not take"
      if d.retMem && d.retStorage then throw s!"{f}: its return has two data locations"
      if d.retStorage then
        let r ← freshCapture "sp"
        ρ := (n, toString r) :: ρ
        Γr := shapeEntry (toString r) (shapeUnder d.widths n) ++ [(toString r, .alias R)]
        mret := some ⟨R, r, true⟩
        pure (RetKind.storage R r)
      else
        unless d.retMem do throw s!"{f}: its return of reference type {Ty.ref R} needs `memory` or `storage`"
        let r ← freshCapture "mv"
        ρ := (n, toString r) :: ρ
        Γr := shapeEntry (toString r) (shapeUnder d.widths n) ++ [(toString r, .mem R)]
        mret := some ⟨R, r, false⟩
        pure (RetKind.mem R r)
    | [(_, .ref R)], some (_, q) => throw s!"{f} returns a reference {Ty.ref R}, not a {q.toStr}"
    | [(n, .prim p)], res => do
      if d.retMem then throw s!"{f}: `memory` on its return of value type {p.toStr}"
      if d.retStorage then throw s!"{f}: `storage` on its return of value type {p.toStr}"
      if let some (_, q) := res then
        unless q = p do throw s!"{f} returns a {p.toStr}, not a {q.toStr}"
      let w := (lookupBy n d.widths).getD 256
      if resW < w then throw s!"{f} returns a {tyName p w}, where a {tyName p resW} is expected"
      let r ← pickName "se" (·.rets) 0
      ρ := (n, toString r) :: ρ
      Γr := shapeEntry (toString r) (shapeUnder d.widths n) ++ [(toString r, .val p w)]
      if targets then
        mrets := [(p, r, w)]
        pure (RetKind.rets [(p, r)])
      else pure (RetKind.val p r)
    | rs, some _ => throw s!"{f} returns {rs.length} values, which a tuple assignment takes"
    | rs, none => do
      if d.retMem then throw s!"{f}: `memory` on a return of a function of several returns"
      if d.retStorage then throw s!"{f}: `storage` on a return of a function of several returns"
      -- declared in the caller's context too (`CallRet.rets`): fresh at
      -- every call, a recursive one's too
      for (n, T) in rs do
        let .prim p := T | throw s!"{f}: its return {n} has a reference type"
        let w := (lookupBy n d.widths).getD 256
        let r ← freshCapture "se"
        ρ := (n, toString r) :: ρ
        Γr := shapeEntry (toString r) (shapeUnder d.widths n) ++ (toString r, .val p w) :: Γr
        mrets := mrets ++ [(p, r, w)]
      if targets then pure (RetKind.rets (mrets.map fun (p, r, _) => (p, r))) else pure RetKind.none
  let Γf := Γr ++ Γp
  let rnames : List Var := match kind with
    | .val _ r | .mem _ r | .storage _ r => [r]
    | .rets l => l.map (·.2)
    | .none => []
  -- the body: at a recursive function's call in its own body, the frame
  -- below (`ElabScope.recs`); for a recursive function, its body elaborated
  -- per frame, lazily (`recUnroll`, `Stmt.callRec`); otherwise inlined
  let mut P : SProg C := []
  let mut recBody : Option (Nat × ((F : Ctx) → List Var → ElabM (Unit → Prog C F F))) := none
  if let some rf := site then
    recBody := some (rf.depth, fun F _ =>
      if rf.below.frame == F then pure (rf.below.get C F)
      else throw s!"internal: {f}'s recursive frame has another context")
  else if recursive then
    let body ← calleeBody C d ρ ctor selfFrame Γf
    let k₁ := (← get).2
    recBody := some (recDepth, fun F ns => do
      let sc ← read
      let frame (n : Nat) (bt : Unit → Prog C F F) : Except String (Prog C F F × Nat) := do
        let rf : RecFrame :=
          { name := f, params := pnames, rets := rnames, depth := n, below := ⟨C, F, bt⟩ }
        let sc' : ElabScope :=
          { sc with funs := scope, top := false, selfFrame := selfFrame, unchecked := false,
                    inlined := (k₀, k₁) :: sc.inlined, recs := rf :: sc.recs }
        let (Q, (_, kEnd)) ← (elabStmtsP body).runFrom sc' (Γf, k₁)
        let ⟨_, b⟩ ← SProg.chain ns F Q
        pure (.cons (.block b) .nil, kEnd)
      -- elaborated once here, for its errors and the names it takes
      let (_, kEnd) ← ElabM.lift (frame (recDepth - 1) fun _ => Prog.recBase)
      modify fun (Γc, _) => (Γc, kEnd)
      pure fun _ => recUnroll Prog.recBase
        (fun n bt => match frame n bt with
          | .ok (Q, _) => Q
          -- unreachable (a frame elaborates as the one checked above);
          -- were it reached, a panic, which no modality accepts
          | .error _ => .cons (.assert (.simple (.bool false))) .nil) recDepth)
  else
    P ← inlinedBody C rc f d ρ (!ctor && !targets && d.endsWithCall) ctor selfFrame scope k₀ Γ Γf
  -- the call's context: the caller's, with `res` pushed when the statement
  -- before the call declares it
  let ⟨ps, as⟩ := targs
  let Γs : NCtx := match res with
    | some (x, p) => if resNew then (x, .val p) :: Γn else Γn
    | none => Γn
  let as := as.wk (← ElabM.lift (Γn.wkTo Γs))
  let call : SStmt C ← match kind with
    | .none =>
      -- several returns of a call that is a statement: declared on entry, at
      -- their defaults
      let (decls, _) := mrets.foldl (fun (acc : SProg C × NCtx) (p, r, _) =>
        (acc.1 ++ [.of acc.2 (.declLocal p r none)], (r, .val p) :: acc.2)) ([], ECtx.toNCtx Γp)
      match recBody with
      | some (n, mk) => pure (.of Γs (.callRec f n as .none (← mk ([] ++ ps) as.names)))
      | none =>
        let ⟨_, b⟩ ← ElabM.lift (SProg.chain as.names ([] ++ ps) (decls ++ P))
        pure (.of Γs (.call f as .none b))
    | .val p r =>
      let res' ← match res with
        | some (x, _) => do pure (some (← ElabM.lift (Γs.idx x (.val p))))
        | none => pure none
      match recBody with
      | some (n, mk) =>
        pure (.of Γs (.callRec f n as (.val p r res') (← mk ([.val p] ++ ps) (r :: as.names))))
      | none =>
        let ⟨_, b⟩ ← ElabM.lift (SProg.chain (r :: as.names) ([.val p] ++ ps) P)
        pure (.of Γs (.call f as (.val p r res') b))
    | .rets l =>
      let ⟨ρs, bs⟩ := Binders.ofList l
      match recBody with
      | some (n, mk) =>
        pure (.of Γs (.callRec f n as (.rets bs) (← mk (ρs ++ ps) (bs.names ++ as.names))))
      | none =>
        let ⟨_, b⟩ ← ElabM.lift (SProg.chain (bs.names ++ as.names) (ρs ++ ps) P)
        pure (.of Γs (.call f as (.rets bs) b))
    | .mem R r =>
      -- a memory return variable: declared on entry, a fresh default object
      let ⟨hm⟩ ← ElabM.lift (memOk R)
      match hd : (Ty.ref R).defaultOkS with
      | true =>
        match recBody with
        | some (n, mk) =>
          pure (.of Γs (.callRec f n as (.mem R r hd hm) (← mk ([.mem R] ++ ps) (r :: as.names))))
        | none =>
          let ⟨_, b⟩ ← ElabM.lift (SProg.chain (r :: as.names) ([.mem R] ++ ps) P)
          pure (.of Γs (.call f as (.mem R r hd hm) b))
      | false => throw s!"{f} returns a {Ty.ref R}, whose default is not well-formed"
    | .storage R r =>
      match recBody with
      | some (n, mk) =>
        pure (.of Γs (.callRec f n as (.storage R r) (← mk ([.alias R] ++ ps) (r :: as.names))))
      | none =>
        let ⟨_, b⟩ ← ElabM.lift (SProg.chain (r :: as.names) ([.alias R] ++ ps) P)
        pure (.of Γs (.call f as (.storage R r) b))
  unless as.separated Γs.names do throw s!"{f}: an argument reads a parameter"
  -- after a repeated callee, the caller's numbering goes on from where it was
  pure ([call], mret.map fun (R, r, storage) => (Γs, R, r, storage), mrets)

/-- `elabCallRet`, outside its `mutual` block (`elabRec`).  A callee all of
whose locals end with the call (not recursive, not the constructor, no
return variable left in the caller) has its locals numbered from where its
first call's were (`CallMemo`), so that its body is one term at every call. -/
def elabCallRetWith (rc : ElabRec C) (f : String) (args : List RawExpr) (res : Option (Var × PrimTy))
    (resW : Nat := 256) (targets : Bool := false) (ctor : Bool := false) (resNew : Bool := false)
    (selfFrame : Bool := false) :
    ElabM (SProg C × Option (NCtx × RefTy × Var × Bool) × List (PrimTy × Var × Nat)) := do
  let sc ← read
  let shared := !ctor && !targets && sc.recs.all (·.name != f) && !isRecursiveC C f &&
    ((sc.funs.find? (·.1 == f)).map (·.2.endsWithCall)).getD false
  let entry ← CallMemo.enter shared f (selfFrame || sc.selfFrame)
  let r ← elabCallRetCore C rc f args res resW targets ctor resNew selfFrame
  CallMemo.leave entry
  pure r

/-- `hoistStmt`, outside its `mutual` block (`elabRec`). -/
def hoistStmtWith (rc : ElabRec C) : RawStmt → ElabM (SProg C × RawStmt) := fun s0 =>
  let hoist := @ElabRec.hoist C rc
  let hoistTop := @ElabRec.hoistTop C rc
  let hoistAssign := @ElabRec.hoistAssign C rc
  let hoistArgs := @ElabRec.hoistArgs C rc
  let hoistCallArgs := @ElabRec.hoistCallArgs C rc
  match s0 with
  | .revertReason m => do
    let (P, m) ← hoist m
    pure (P, .revertReason m)
  | .revertRaw m => do
    let (P, m) ← hoist m
    pure (P, .revertRaw m)
  | .requireReason c m => do
    -- The condition must finish before the reason's allocation or effects.
    let (P, c) ← hoist c
    let (Pc, c) ← forceArg C c
    let (Q, m) ← hoist m
    let x := toString (← freshCapture "mv")
    let R ← rc.elabStmtsP [.declMemory (.named "string") x (some m)]
    pure (P ++ Pc ++ Q ++ R, .requireReason c (.name x))
  | .pushOpAssign op b r => do
    let (P, r) ← hoist r
    let (Pc, r) ← if b.hasIncDec then captureExpr C r else pure ([], r)
    let (Q, b) ← hoist b
    pure (P ++ Pc ++ Q, .pushOpAssign op b r)
  | .pushIncDec op b => do
    let (P, b) ← hoist b
    pure (P, .pushIncDec op b)
  | .assign l r => do
    -- `m = f(a);` to a reference local: its arguments only (`elabStmt1`)
    if let .call f args := r then
      let isRefLocal := match synth C (← nctx) l with
        | .ok (.mpath (.ref _) (.var ..)) | .ok (.path (.ref _) (.alias ..)) => true
        | _ => false
      if (← read).funs.any (·.1 == f) && isRefLocal then
        let (P, args) ← hoistCallArgs f args
        return (P, .assign l (.call f args))
    match r, synth C (← nctx) l with
    | .incDec op e, .ok (.val _ (.simple (.local _))) =>
      let (P, e) ← hoist e
      pure (P, .assignIncDec l op e)
    | .newArr T n, _ =>
      let (P, n) ← hoist n
      let (Pc, n) ← if l.hasIncDec then captureExpr C n else pure ([], n)
      let (Q, l) ← hoist l
      pure (P ++ Pc ++ Q, .assign l (.newArr T n))
    | .call f args, .ok (.val _ (.simple (.local _))) =>
      if (castTy? f).isSome || f == "address" || (lookupBy f C.enums).isSome ||
          ((byteBuiltin f || f == "erc7201" || f.startsWith "#slice" || f.startsWith "#bytesPrefix") &&
            (← read).funs.all (·.1 != f)) then hoistAssign l r
      else
        let (P, args) ← hoistCallArgs f args
        pure (P, .assign l (.call f args))
    | _, _ => hoistAssign l r
  | .decl T x (some (.call f args)) => do
    if (castTy? f).isSome || f == "address" || (lookupBy f C.enums).isSome ||
        ((byteBuiltin f || f == "erc7201" || f.startsWith "#slice" || f.startsWith "#bytesPrefix") &&
            (← read).funs.all (·.1 != f)) then
      let (P, r) ← hoist (.call f args)
      return (P, .decl T x (some r))
    let (P, args) ← hoistCallArgs f args
    pure (P, .decl T x (some (.call f args)))
  | .decl T x (some r) => do
    let (P, r) ← hoistTop r
    pure (P, .decl T x (some r))
  | .declMemory T x (some (.newArr T' n)) => do
    let (P, n) ← hoist n
    pure (P, .declMemory T x (some (.newArr T' n)))
  | .delete target => do
    let (P, e) ← hoist target
    -- A scalar temporary introduced by hoisting is not a source place.
    -- Keep reference targets on their existing path, including effectful
    -- receivers; only a named value local may use assignLocal deletion.
    unless target matches .name _ do
      if let .ok (.val ..) := synth C (← nctx) e then
        throw "`delete` needs a local, storage or memory location"
    pure (P, .delete e)
  -- a statement of one expression: its captures, then the statement
  | s@(.decl ..) | s@(.declStorage ..) | s@(.declMemory ..) | s@(.declStoragePush ..)
  | s@(.declPush ..) | s@(.incDec ..) | s@(.ite ..) | s@(.require _)
  | s@(.requireMsg ..) | s@(.assert _) | s@(.tryCall ..) => do
    -- `T memory x = f(a);`: its arguments only (`elabStmt1`)
    if let .declMemory T x (some (.call f args)) := s then
      if (← read).funs.any (·.1 == f) then
        let (P, args) ← hoistCallArgs f args
        return (P, .declMemory T x (some (.call f args)))
    if let .declStorage T x (some (.call f args)) := s then
      if (← read).funs.any (·.1 == f) then
        let (P, args) ← hoistCallArgs f args
        return (P, .declStorage T x (some (.call f args)))
    let (s, P) ← (s.mapExprsM fun e => do
      let (Q, e) ← hoist e
      modify (· ++ Q)
      pure e : StateT (SProg C) ElabM RawStmt).run []
    pure (P, s)
  | .opAssign op l r => do
    let (P, r) ← hoist r
    let (Pc, r) ← if l.hasIncDec then captureExpr C r else pure ([], r)
    let (Q, l) ← hoist l
    pure (P ++ Pc ++ Q, .opAssign op l r)
  | .assignIncDec x op l => do
    let (P, l) ← hoist l
    pure (P, .assignIncDec x op l)
  | .call (.field e m) args => do
    if let .call f getterArgs := e then
      if m == "push" || m == "pop" then
        let (P, getterArgs) ← hoistCallArgs f getterArgs
        return (P, .call (.field (.call f getterArgs) m) args)
    -- the receiver first, then the arguments
    let (P, e) ← hoist e
    let (Pc, e) ← captureBefore C e args
    let (Q, args) ← hoistArgs args
    pure (P ++ Pc ++ Q, .call (.field e m) args)
  | .call (.name f) args => do
    if (← read).funs.all (·.1 != f) then
      if byteBuiltin f || f == "erc7201" then
        let (P, e) ← hoist (.call f args)
        let (Q, _) ← captureExpr C e
        return (P ++ Q, .eval [])
      if let some op := ModOp.ofName? f then
        let [a, b, k] := args | throw s!"{f} takes three uint arguments"
        let (P, e) ← hoist (.modular op a b k)
        let (Q, _) ← captureExpr C e
        return (P ++ Q, .eval [])
    let (P, args) ← hoistCallArgs f args
    pure (P, .call (.name f) args)
  | .assignPush l b => do
    let (P, b) ← hoist b
    let (Q, l) ← hoist l
    pure (P ++ Q, .assignPush l b)
  | .send T x r a g => do
    -- the receiver first, then the amount, as `transfer`'s
    let (P, r) ← hoist r
    let (Pc, r) ← captureBefore C r [a]
    let (Q, a) ← hoist a
    pure (P ++ Pc ++ Q, .send T x r a g)
  | .eval args => do
    -- Finish each read before the next operand can introduce a guard.
    let (P, _) ← eagerArgsWith C hoist args true
    pure (P, .eval [])
  | s => pure ([], s)

/-- `elabStmtP`, outside its `mutual` block (`elabRec`). -/
def elabStmtPWith (rc : ElabRec C) (s : RawStmt) : ElabM (SProg C) := do
  let hoistStmt := @ElabRec.hoistStmt C rc
  if let .declMemory (.named "#sliceBase") x (some e) := s then
    let (P, e) ← rc.hoist e
    let Γ ← ctx
    let .mpath (.ref R@(.array _)) _ ← ElabM.lift (synth C Γ.toNCtx e)
      | throw "a calldata slice needs a dynamic array base"
    let ws := exprShape C Γ e
    let T := rawTyW ws (.ref R) ""
    let Q ← rc.elabStmtP (.declMemory T x (some e))
    -- Retain source-only markers too (rawTyW intentionally omits enum
    -- identity and whole string metadata). Copies must see them to refuse
    -- unsupported nominal elements instead of treating them as integers.
    declareShape x ws
    return P ++ Q
  -- Tuple decoding must retain its ABI continuation instead of taking
  -- the generic multi-return function-call path.
  let slicedDecode := match s with
    | .tupleAssign ts (.call "#sliceDecode" (view :: rest)) =>
      some (view, fun data => RawStmt.tupleAssign ts (.call "abi.decode" (data :: rest)))
    | .tupleDecl ts (.call "#sliceDecode" (view :: rest)) =>
      some (view, fun data => RawStmt.tupleDecl ts (.call "abi.decode" (data :: rest)))
    | _ => none
  if let some (view, resume) := slicedDecode then
    let t := toString (← freshCapture "mv")
    let (v, pre) ← ElabM.lift (inlineSliceOpen t view)
    let P ← rc.elabStmtsP pre
    let Q ← rc.elabStmtP (resume (.call sliceViewName [.name v.base, v.off, v.len]))
    return P ++ Q
  let literalTarget : RawExpr → Bool
    | .call "#array" _ => true
    | _ => false
  match s with
  | .assign l _ | .opAssign _ l _ | .incDec _ l | .delete l =>
    if literalTarget l then throw "an inline array literal is not an assignment or delete target"
  | _ => pure ()
  let elabStmt1 := @ElabRec.elabStmt1 C rc
  let elabStmtsP := @ElabRec.elabStmtsP C rc
  let s ← ElabM.lift (s.mapExprsM (RawExpr.orderNamed (← read).funs))
  -- custom errors (`revert E(a)`, `require(c, E(a))`): their data only where
  -- a `try` reads it, as `revertMsg`'s
  let self := (← read).selfFrame
  -- Apply implicit byte widening before fnPure/bytesPure erase source widths.
  -- Both require branches evaluate operands at the custom error's types,
  -- including a discarded fixed-byte literal (which is not a memory value).
  let errorArgs (e : String) (args : List RawExpr) : ElabM (List RawExpr) := do
    let some d := lookupBy e C.errors | pure args
    unless d.params.length == args.length do
      throw s!"`{e}` takes {d.params.length} arguments, given {args.length}"
    let Γ ← ctx
    (d.params.zip args).mapM fun ((n, _), a) =>
      ElabM.lift (toBytesAt? C Γ (lookupBy (n ++ "#bytes") d.widths) a a)
  let s ← match s with
    | .revertErr e args => pure (.revertErr e (← errorArgs e args))
    | .requireErr c e args => pure (.requireErr c e (← errorArgs e args))
    | s => pure s
  let s ← match s with
    | .revertErr _ args =>
      pure (if self then s else .block [.eval args, .revert])
    | .requireErr c e args => do
      if (lookupBy e C.errors).isNone then
        pure (RawStmt.requireReason c (.call e args))
      else do
        let total ← args.allM (canDiscardArg C)
        if self then
          pure (.ite c (if total then [] else [.eval args]) [.revertErr e args])
        else pure (if total then .require c else RawStmt.requireWith c args)
    | s => pure s
  match s with
  | .revertReason m | .requireReason _ m => do
    let Γ ← ctx
    -- Validate nested string conversions before bytesPure erases them too.
    let invalid := m.any fun e => match e with
      | .call "string" [_] | .call "string.concat" _ => !stringReason? C Γ e
      | _ => false
    unless stringReason? C Γ m && !invalid do
      throw "a revert reason is a string; convert bytes with string(data)"
  | _ => pure ()
  -- Keep a discarded builtin whole through both source-type passes.
  let s : RawStmt := match s with
    | .call (.field (.name n) g) args =>
      if builtinMember n g then .eval [.call (n ++ "." ++ g) args] else s
    | .call (.name f) args =>
      if (byteBuiltin f || f == "erc7201" || f.startsWith "#slice") && (lookupBy f C.funs).isNone then
        .eval [.call f args]
      else s
    | _ => s
  -- a call statement through a value that is not a name, `s.f(x);`
  -- (`callValueName`); `push`, `pop` and `transfer` are the receivers' own
  let s := match s with
    | .call (.name _) _ => s
    | .call e@(.field _ m) args =>
      if ["push", "pop", "transfer"].contains m then s else .call (.name callValueName) (e :: args)
    | .call e args => .call (.name callValueName) (e :: args)
    | s => s
  -- external function values and their members (`fnPure`)
  let s ← match s with
    | .call (.name f) as =>
      if f == callValueName then do
        let as' ← match ← ElabM.lift (fnPure C (← ctx) (.call f as)) with
          | .call _ as' => pure as'
          | _ => pure as
        pure (.call (.name f) as')
      else ElabM.lift (s.mapExprsM (fnPure C (← ctx)))
    | s => ElabM.lift (s.mapExprsM (fnPure C (← ctx)))
  -- `(T a, U b) = abi.decode(d, (T, U));`: each component decoded from its
  -- word (`#abiDecode`), `d` read once
  let decode? : Option (RawExpr × List RawExpr) := match s with
    | .tupleDecl _ (.call "abi.decode" [d, .tuple ts]) | .tupleAssign _ (.call "abi.decode" [d, .tuple ts]) =>
      some (d, ts)
    | _ => none
  if let some (d, ts) := decode? then
    if (← read).funs.all (·.1 != "abi.decode") then
      let x := toString (← freshCapture "mv")
      let (n, one) := abiDecodeHeads C x ts (if d.isSliceView then d else .name x)
      let rest : List RawStmt ← match s with
        | .tupleDecl vs _ => do
          unless vs.length == ts.length do
            throw s!"abi.decode gives {ts.length} values, not {vs.length}"
          pure (vs.zipIdx.filterMap fun (v, i) => v.map fun (T, y) =>
            match T with
            | .named t =>
              if dynBytesTy t || (C.structName? t).isSome then .declMemory T y (some (one i))
              else .decl T y (some (one i))
            | _ => .declMemory T y (some (one i)))
        | .tupleAssign ls _ => do
          let n := ts.length
          unless ls.length == n do throw s!"abi.decode gives {n} values, not {ls.length}"
          pure (ls.zipIdx.filterMap fun (l, i) => l.map fun l => .assign l (one i))
        | _ => pure []
      return ← elabStmtsP ((if d.isSliceView then [] else [.declMemory (.named "bytes") x (some d)]) ++ rest)
  -- solc's operations on byte types, as the `uint` ones (`bytesPure`)
  let s ← ElabM.lift (bytesStmt C (← ctx) s)
  -- push arithmetic inside `unchecked`: the appended slot starts at `0`, so
  -- `b.push() op= r` pushes `0 op r`, wrapping at the element's width as
  -- `narrowWrapNode` wraps (`small.push() -= 1` at `uint8[]` pushes `255`):
  -- `r` itself for `+=`, `0` for `*=`, `r`'s negation for `-=` (`0` at `0`,
  -- `2^N - r` above it; a signed `r` at the minimum is itself), a literal
  -- folded; `r` is evaluated once, before the push, as the checked
  -- statement reads it
  if (← read).unchecked then
    let push? : Option (BinOp × RawExpr × RawExpr) := match s with
      | .pushOpAssign op b r => some (op, b, r)
      | .pushIncDec op b => some (if op.isIncrement then .add else .sub, b, .num 1)
      | _ => none
    if let some (op, b, r) := push? then
      let ⟨_, t⟩ ← synthM C b
      let .path (.ref (.array (.prim p))) _ := t
        | throw "push arithmetic needs a storage array of primitive numeric elements"
      unless p.isNumeric do throw s!"push arithmetic at {p.toStr}"
      let n := widthIn C (← ctx) (.index b (.num 0))
      let T := tyName p n
      let m : Int := 2 ^ n
      let lit (v : Int) : RawExpr :=
        let w := if p == .int then ((v + m / 2) % m + m) % m - m / 2 else (v % m + m) % m
        if w < 0 then .unop .neg (.num w.natAbs) else .num w.toNat
      let push (pre : List RawStmt) (v : RawExpr) : ElabM (SProg C) :=
        elabStmtsP (pre ++ [.call (.field b "push") [v]])
      match op, r.litVal? with
      | .add, some v => return ← push [] (lit v)
      | .sub, some v => return ← push [] (lit (-v))
      | .mul, some _ => return ← push [] (.num 0)
      | .add, none | .sub, none | .mul, none =>
        -- `r` at the element's type, captured where it is not a name
        let (pre, R) ← if r.isPure then pure ([], RawExpr.call T [r]) else do
          let y := toString (← freshCapture "pa")
          pure ([RawStmt.decl (.named T) y (some r)], RawExpr.name y)
        let v : RawExpr := match op with
          | .add => R
          | .mul => .binop .mul R (.num 0)
          | _ =>
            if p == .int then
              .ternary (.binop .eqB R (.unop .neg (.num (2 ^ (n - 1))))) R (.binop .sub (.num 0) R)
            else
              .ternary (.binop .eqB R (.num 0)) (.num 0)
                (.binop .add (.binop .sub (.num (2 ^ n - 1)) R) (.num 1))
        return ← push pre v
      | _, _ => return ← push [] (.binop op (.num 0) r)
  -- a loop outside a function's body, lowered here (`lowerLoops`)
  if s matches .whileLoop .. | .forLoop .. | .doWhile .. then
    return ← elabStmtsP (← lowerLoops none [s])
  -- a place with a narrow position below it is used through its indices and
  -- members, or whole where its narrow positions are checked against the
  -- target's (`shapeCheck`): a reference local's initializer, a reference
  -- assignment, a push bound to an alias, an argument (`elabCallRet`)
  let Γ ← ctx
  let isRef (l : RawExpr) : Bool := (widthPath? C Γ l).any fun (_, _, t) => t matches .ref _
  let whole ← match s with
    | .declStorage T _ (some e) | .declMemory T _ (some e) => do
      ElabM.lift (shapeCheck C Γ (← ElabM.lift (elabTyW C T)).2 e); pure true
    | .declStoragePush T _ b => do
      ElabM.lift (shapeCheck C Γ (← ElabM.lift (elabTyW C T)).2 (.index b (.num 0))); pure true
    | .assignPush l b =>
      if isRef l then do
        ElabM.lift (shapeCheck C Γ (placeShape C Γ l) (.index b (.num 0))); pure true
      else pure true
    | .assign l r =>
      if isRef l then do
        match synth C Γ.toNCtx l with
        | .ok (.path (.ref _) (.loc _)) => ElabM.lift (storageCopyShape C Γ (placeShape C Γ l) r)
        | _ => ElabM.lift (shapeCheck C Γ (placeShape C Γ l) r)
        pure true
      else pure false
    | .declPush .. => pure true
    | _ => pure false
  -- a call statement's arguments, as a call expression's (`narrowWholeUse?`)
  -- a push's receiver, as a `.push` member's base
  let es : List (RawExpr × Bool) ← match s with
    | .call (.field b "push") [a] =>
      -- Reference values are checked after capture as well; permit their
      -- whole source here without erasing the element-width metadata.
      let funs := (← read).funs
      let refValue : Bool := match synth C Γ.toNCtx b with
        | .ok (.path (.ref (.array (.ref _))) _) => true
        | _ => match b with
          | .call f _ => ((lookupBy f funs).bind (·.ret)).any
              (fun (_, T) => T matches .ref (.array (.ref _)))
          | _ => false
      if refValue then pure [(b, true), (a, true)]
      else pure (s.exprs.map (·, whole))
    | .call (.name f) as => pure [(RawExpr.call f as, whole)]
    | .pushOpAssign _ b r => pure [(b, true), (r, whole)]
    | .pushIncDec _ b => pure [(b, true)]
    | .revertReason m | .revertRaw m => do
      ElabM.lift (shapeCheck C Γ dynBytesRows m)
      pure [(m, true)]
    | .requireReason c m => do
      ElabM.lift (shapeCheck C Γ dynBytesRows m)
      pure [(c, false), (m, true)]
    | s => pure (s.exprs.map (·, whole))
  unless s matches .delete _ do
    for (e, base) in es do
      let w := if base then narrowWholeAt? C Γ e else narrowWholeUse? C Γ e
      if let some w := w then
        throw s!"{w.toStr} has a narrow element, key or value: it is used through an index, \
          `.length`, `.push`, `.pop` or `delete`, or whole where the same narrow positions are \
          expected, not whole"
  let s ← ElabM.lift (s.mapExprsM (narrowPure C (← read).unchecked (← ctx)))
  let (P, s) ← hoistStmt s
  -- Hoisting supplies the independently inferred array shape. Check it
  -- before a target can erase its source widths.
  let Γ' ← ctx
  match s with
  | .declStorage T _ (some e) | .declMemory T _ (some e) =>
    ElabM.lift (shapeCheck C Γ' (← ElabM.lift (elabTyW C T)).2 e)
  | .assign l r =>
    if (widthPath? C Γ' l).any (fun (_, _, t) => t matches .ref _) then
      match synth C Γ'.toNCtx l with
      | .ok (.path (.ref _) (.loc _)) => ElabM.lift (storageCopyShape C Γ' (placeShape C Γ' l) r)
      | _ => ElabM.lift (shapeCheck C Γ' (placeShape C Γ' l) r)
  | _ => pure ()
  let P ← pure (P ++ (← elabStmt1 s))
  -- a reference local's narrow positions (`LocalTy.shape`)
  match s with
  | .declStorage T x _ | .declMemory T x _ | .declStoragePush T x _ =>
    declareShape x (← ElabM.lift (elabTyW C T)).2
  | _ => pure ()
  pure P

/-- `elabStmt1`, outside its `mutual` block (`elabRec`). -/
def elabStmt1With (rc : ElabRec C) : RawStmt → ElabM (SProg C) := fun s0 =>
  let hoistArgs := @ElabRec.hoistArgs C rc
  let elabCall := @ElabRec.elabCall C rc
  let elabMemCall := @ElabRec.elabMemCall C rc
  let elabStorageCall := @ElabRec.elabStorageCall C rc
  let elabCallReceiver := @ElabRec.elabCallReceiver C rc
  let elabCallReceiverPush := @ElabRec.elabCallReceiverPush C rc
  let trySelfBody := @ElabRec.trySelfBody C rc
  let elabValueCall := @ElabRec.elabValueCall C rc
  let elabCtor := @ElabRec.elabCtor C rc
  let elabStmtP := @ElabRec.elabStmtP C rc
  let elabStmt1 := @ElabRec.elabStmt1 C rc
  let loopExpr := @ElabRec.loopExpr C rc
  let loopQ := @ElabRec.loopQ C rc
  let elabStmtsP := @ElabRec.elabStmtsP C rc
  let elabBranch := @ElabRec.elabBranch C rc
  let elabScope := @ElabRec.elabScope C rc
  let elabTuple := @ElabRec.elabTuple C rc
  let memoryRevert (kind : CatchKind) (m : RawExpr) : ElabM (SProg C) := do
    ElabM.lift (shapeCheck C (← ctx) dynBytesRows m)
    let (P, x) ← rc.abiMemBytes m
    let Γ ← nctx
    let p ← ElabM.lift (checkMPath C Γ (.ref bytesR) (.name x))
    match p with
    | .var src _ => pure (P ++ [.of Γ (.revertData [.mem kind src])])
    | .loc _ => throw "internal: revert data was not captured in a memory local"
  match s0 with
  | .pushOpAssign op b r => do
    let ⟨Γ, t⟩ ← synthM C b
    let .path (.ref (.array (.prim p))) path := t
      | throw "push arithmetic needs a storage array of primitive numeric elements"
    -- at a narrow element (`uint8[]`), `r` fits it and the appended slot is
    -- checked after the write, as `narrowPost` checks a variable's
    let n := widthIn C (← ctx) (.index b (.num 0))
    ElabM.lift (fitCheck C (← ctx) p n r)
    match hop : op.hasCompoundAssign, hp : p.isNumeric with
    | true, true => pure (.of Γ (.pushOpAssign op hop hp path (← checkIn C Γ p r)) ::
        (← narrowCheck C p n (pushedSlot b)))
    | false, _ => throw s!"no push compound assignment for {BinOp.sym op}"
    | _, false => throw s!"push arithmetic at {p.toStr}"
  | .pushIncDec op b => do
    let ⟨Γ, t⟩ ← synthM C b
    let .path (.ref (.array (.prim p))) path := t
      | throw "push arithmetic needs a storage array of primitive numeric elements"
    let n := widthIn C (← ctx) (.index b (.num 0))
    match hp : p.isNumeric with
    | true => pure (.of Γ (.pushIncDec op hp path) :: (← narrowCheck C p n (pushedSlot b)))
    | false => throw s!"push increment/decrement at {p.toStr}"
  | .assign l (.newArr T n) => do
    let ⟨R, hR⟩ ← elabNewTy C T
    let (P, ⟨Γ, se⟩) ← elabSize C n
    match ← ElabM.lift (synth C Γ l) with
    | .mpath (.ref R') (.var x _) =>
      if h : R' = R then pure (P ++ [.of Γ (.rebindMem (h ▸ x) (.newArr se hR))])
      else throw "`new` of another type than the memory local's"
    | .mpath T' (.loc ml) =>
      if hT : T' = .ref R then pure (P ++ [.of Γ (.assignNew (.mem (hT ▸ ml)) se hR)])
      else throw "`new` of another type than the member's"
    | .path T' (.loc sl) =>
      if hT : T' = .ref R then pure (P ++ [.of Γ (.assignNew (.store (hT ▸ sl)) se hR)])
      else throw "`new` of another type than the location's"
    | .path _ (.alias _) => throw "a storage pointer bound to a memory array"
    | .val .. => throw "`new` assigned to a value"
  | .assign l (.call f args) => do
    let ⟨Γ, t⟩ ← synthM C l
    match t with
    | .val p (.simple (.local x)) => elabCall f args (some (x.name Γ.names, p)) (widthIn C (← ctx) l)
    | .mpath (.ref R) (.var x _) =>
      let xn := x.name Γ.names
      elabMemCall f args R fun Γ' r hm => do
        let Γr : NCtx := (r, .mem R) :: Γ'
        pure (.of Γr (.rebindMem (← Γr.idx xn (.mem R)) (.alias (.var .here hm))))
    | .path (.ref R) (.alias x) =>
      let xn := x.name Γ.names
      elabStorageCall f args R fun Γ' r => do
        let Γr : NCtx := (r, .alias R) :: Γ'
        pure (.of Γr (.rebind (← Γr.idx xn (.alias R)) (.path (.alias .here))))
    | _ => throw "a call's value is assigned to a stack local"
  | .assign l r => do
    let post ← narrowPost C l r
    let ⟨Γ, t⟩ ← synthM C l
    let P : SProg C ← match t with
      | .val p (.simple (.local x)) => do pure [.of Γ (.assignLocal x (← checkIn C Γ p r))]
      | .val p _ => throw s!"{l.toStr} is a {p.toStr} value, not a place to assign to"
      | .path (.prim p) (.loc l) => do pure [.of Γ (.assign l (.val (← checkIn C Γ p r)))]
      | .path (.ref R) (.loc l) => do
        match ← ElabM.lift (synth C Γ r) with
        | .mpath T mp =>
          if hT : T = .ref R then pure [.of Γ (.assignFromMem l (hT ▸ mp))]
          else pure [.of Γ (.assign l (← ElabM.lift (checkStorageCopy C Γ R r)))]
        | _ => do pure [.of Γ (.assign l (← ElabM.lift (checkStorageCopy C Γ R r)))]
      | .path (.ref R) (.alias x) => do
        pure [.of Γ (.rebind x (.path (← ElabM.lift (checkPath C Γ (.ref R) r))))]
      | .mpath (.ref R) (.var x _) => do pure [.of Γ (.rebindMem x (← ElabM.lift (elabMRhs C Γ R r)))]
      | .mpath (.prim p) (.loc l) => do pure [.of Γ (.assignMem l (.val (← checkIn C Γ p r)))]
      | .mpath (.ref R) (.loc l) => do
        pure [.of Γ (.assignMem l (.ref (← ElabM.lift (checkMPath C Γ (.ref R) r))))]
    pure (P ++ post)
  | .decl T x (some (.call f args)) => do
    let (.prim p, n) ← ElabM.lift (elabDeclTy C T) | throw s!"{x}: a reference type needs a data location"
    let Γ ← nctx
    let P ← elabCall f args (some (Var.ofName x, p)) n (resNew := true)
    declare C x (.val p n)
    declareShape x (← ElabM.lift (bytesRowsOf C T))
    pure (.of Γ (.declLocal p (Var.ofName x) none) :: P)
  | .decl T x init => do
    let (.prim p, n) ← ElabM.lift (elabDeclTy C T) | throw s!"{x}: a reference type needs a data location"
    let Γ ← nctx
    let v ← init.mapM (checkIn C Γ p)
    declare C x (.val p n)
    declareShape x (← ElabM.lift (bytesRowsOf C T))
    let post ← match init with
      | some r => narrowPost C (.name x) r
      | none => pure []
    pure (.of Γ (.declLocal p (Var.ofName x) v) :: post)
  | .declStorage T x (some (.call f args)) => do
    let .ref R ← ElabM.lift ((·.1) <$> elabTyW C T) | throw s!"{x}: `storage` on a value type"
    let P ← elabStorageCall f args R fun Γ r =>
      pure (.of ((r, .alias R) :: Γ) (.declStorage R (Var.ofName x) (some (.path (.alias .here)))))
    declare C x (.alias R)
    pure P
  | .declStorage T x init => do
    let .ref R ← ElabM.lift ((·.1) <$> elabTyW C T) | throw s!"{x}: `storage` on a value type"
    let Γ ← nctx
    let init ← ElabM.lift (init.mapM fun e => ARhs.path <$> checkPath C Γ (.ref R) e)
    declare C x (.alias R)
    pure [.of Γ (.declStorage R (Var.ofName x) init)]
  | .declStoragePush T x b => do
    let .ref R ← ElabM.lift ((·.1) <$> elabTyW C T) | throw s!"{x}: `storage` on a value type"
    let Γ ← nctx
    let r ← ElabM.lift (elabPush C Γ R b)
    declare C x (.alias R)
    pure [.of Γ (.declStorage R (Var.ofName x) (some r))]
  | .declPush T x b => do
    let (.prim p, n) ← ElabM.lift (elabDeclTy C T) | throw s!"{x}: a reference type needs a data location"
    let Γ ← nctx
    let b ← ElabM.lift (elabPrimPush C Γ p b)
    declare C x (.val p n)
    let ⟨Γ', th, ix⟩ ← afterCapture Γ (Var.ofName x) (.val p)
    pure [.of Γ (.declLocal p (Var.ofName x) none),
      .of Γ' (.assignLocalPush ix (b.wk th))]
  | .assignPush l b => do
    let ⟨Γ, t⟩ ← synthM C l
    match t with
    | .path (.ref R) (.alias x) => pure [.of Γ (.rebind x (← ElabM.lift (elabPush C Γ R b)))]
    | .val _ (.simple (.local _)) => do
      let ⟨Γ, .val p (.simple (.local i))⟩ ← synthM C l
        | throw "a pushed primitive's target must remain a value local"
      let b ← ElabM.lift (elabPrimPush C Γ p b)
      pure [.of Γ (.assignLocalPush i b)]
    | _ => throw "`= b.push()` binds a storage pointer or a value local"
  | .declMemory T x (some (.newArr T' n)) => do
    let .ref R ← ElabM.lift ((·.1) <$> elabTyW C T) | throw s!"{x}: `memory` on a value type"
    let ⟨R', hR⟩ ← elabNewTy C T'
    unless R' = R do throw s!"{x}: `new` of another type"
    let (P, ⟨Γ, se⟩) ← elabSize C n
    declare C x (.mem R')
    pure (P ++ [.of Γ (.declMem R' (Var.ofName x) (some (.newArr se hR)) rfl
      (MRhs.newArr (C := C) se hR).mapFree)])
  | .declMemory T x (some (.call f args)) => do
    let .ref R ← ElabM.lift ((·.1) <$> elabTyW C T) | throw s!"{x}: `memory` on a value type"
    let P ← elabMemCall f args R fun Γ r hm =>
      pure (.of ((r, .mem R) :: Γ) (.declMem R (Var.ofName x) (some (.alias (.var .here hm))) rfl hm))
    declare C x (.mem R)
    pure P
  | .declMemory T x init => do
    let .ref R ← ElabM.lift ((·.1) <$> elabTyW C T) | throw s!"{x}: `memory` on a value type"
    let Γ ← nctx
    let s : Stmt C Γ.ctx (.mem R :: Γ.ctx) ← match init with
      | some e =>
        let r ← ElabM.lift (elabMRhs C Γ R e)
        pure (Stmt.declMem R (Var.ofName x) (some r) rfl r.mapFree)
      | none =>
        let ⟨hm⟩ ← ElabM.lift (memOk R)
        match hd : (Ty.ref R).defaultOkS with
        | true => pure (Stmt.declMem R (Var.ofName x) none (by simp only [Option.isSome_none, hd, Bool.or_true]) hm)
        | false => throw s!"{x}: a memory object whose default is not well-formed"
    declare C x (.mem R)
    pure [.of Γ s]
  | .delete e => do
    let ⟨Γ, t⟩ ← synthM C e
    match t with
    | .path T (.loc l) =>
      if T matches .ref (.mapping ..) then throw "a mapping cannot be deleted"
      else pure [.of Γ (.delete l)]
    | .path _ (.alias _) => throw "`delete` on a storage pointer"
    | .mpath T p =>
      match hd : T.defaultOkS with
      | true => pure [.of Γ (.deleteMem p hd)]
      | false => throw "`delete` of a memory object whose default is not well-formed"
    | .val p (.simple (.local i)) =>
      -- Solidity deletes a value local by assigning its type's default.
      -- Reuse assignLocal, retaining the existing run and soundness rule.
      let zero : Val C Γ.ctx p := match p with
        | .bool => .simple (.bool false)
        | .uint => .simple (.lit 0 rfl)
        | .int => .simple (.lit 0 rfl)
      pure [.of Γ (.assignLocal i zero)]
    | .val .. => throw "`delete` needs a local, storage or memory location"
  | .opAssign op l r => do
    -- `&= |= ^= <<= >>=` and a wrapping `+=`: `l = l ⊕ r`, the target's
    -- effects already captured (`hoistStmt`), so reading it twice is safe
    if op.isArith && !op.hasCompoundAssign && op != .pow then
      let e ← ElabM.lift (narrowWrapNode C (← read).unchecked (← ctx) (.binop op l r))
      -- a signed wrap is a cast, captured (`narrowWrapNode`)
      if e matches .call .. then return ← elabStmtP (.assign l e)
      return ← elabStmt1 (.assign l e)
    let (pre, ⟨Γ, p, t⟩) ← elabOpTarget C l
    -- at a narrow target, what `l ⊕ r` may leave the type by is checked after
    let n := widthIn C (← ctx) l
    ElabM.lift (fitCheck C (← ctx) p n r)
    let post ← if (op matches .add | .sub | .mul) || (op == .div && p == .int) then
      narrowCheck C p n l else pure []
    match hop : op.hasCompoundAssign, hp : p.isNumeric with
    | true, true => pure (pre ++ [.of Γ (.opAssign op hop hp t (← checkIn C Γ p r))] ++ post)
    | false, _ => throw s!"no compound assignment for {BinOp.sym op}"
    | _, false => throw s!"a compound assignment at {p.toStr}"
  | .incDec op l => do
    let (pre, ⟨Γ, p, t⟩) ← elabOpTarget C l
    match hp : p.isNumeric with
    | true => pure (pre ++ [.of Γ (.incDec op hp t)] ++ (← narrowCheck C p (widthIn C (← ctx) l) l))
    | false => throw s!"++ or −− at {p.toStr}"
  | .assignIncDec x op l => do
    let (pre, ⟨Γ, p, t, hs⟩) ← elabIncTarget C l
    match ← ElabM.lift (synth C Γ x) with
    | .val q (.simple (.local y)) =>
      ElabM.lift (fitCheck C (← ctx) q (widthIn C (← ctx) x) l)
      match hp : p.isNumeric with
      | true => if h : q = p then
                  pure (pre ++ [.of Γ (.assignIncDec (h ▸ y) op hp t hs)] ++
                    (← narrowCheck C p (widthIn C (← ctx) l) l))
                else throw s!"a {p.toStr} assigned to a {q.toStr}"
      | false => throw s!"++ or −− at {p.toStr}"
    | _ => throw "the result of ++ or −− goes to a stack local"
  | .call (.field (.call f args) "push") values => do
    match values with
    | [] =>
      elabCallReceiver f args fun _ E => do
        match hd : E.defaultOkS with
        | true => pure (.push none (by simp only [Option.isSome_none, hd, Bool.or_true]))
        | false => throw "push() of an element whose default is not well-formed"
    | [a] => elabCallReceiverPush f args a
    | _ => throw "push takes at most one argument"
  | .call (.field (.call f args) "pop") [] =>
    elabCallReceiver f args fun _ _ => pure .pop
  | .call (.field e "push") args => do
    let ⟨Γ, t⟩ ← synthM C e
    let .path (.ref (.array E)) b := t | throw "push on something that is not an array"
    match args with
    | [] =>
      match hd : E.defaultOkS with
      | true => pure [.of Γ (.push b none (by simp only [Option.isSome_none, hd, Bool.or_true]))]
      | false => throw "push() of an element whose default is not well-formed"
    | [a] =>
      match E with
      | .prim p =>
        -- a narrow element: the value converts to it implicitly, so it fits
        ElabM.lift (fitCheck C (← ctx) p (widthIn C (← ctx) (.index e (.num 0))) a)
        pure [.of Γ (.push b (some (.val (← checkIn C Γ p a))) rfl)]
      | .ref R =>
        ElabM.lift (storageCopyShape C (← ctx) (placeShape C (← ctx) (.index e (.num 0))) a)
        pure [.of Γ (.push b (some (← ElabM.lift (checkStorageCopy C Γ R a))) rfl)]
    | _ => throw "push takes at most one argument"
  | .call (.field e "pop") [] => do
    let ⟨Γ, t⟩ ← synthM C e
    let .path (.ref (.array _)) b := t | throw "pop on something that is not an array"
    pure [.of Γ (.pop b)]
  | .call (.field e "transfer") [a] => do
    let Γ ← nctx
    pure [.of Γ (.transfer (← checkIn C Γ .uint e) (← checkIn C Γ .uint a))]
  | .send T x e a g => do
    let Γ ← nctx
    let r ← checkIn C Γ .uint e
    let v ← checkIn C Γ .uint a
    match T, x with
    | some T, .name n =>
      let (.prim .bool, w) ← ElabM.lift (elabDeclTy C T)
        | throw s!"{n}: `send` returns a bool"
      declare C n (.val .bool w)
      let ⟨Γ', th, ix⟩ ← afterCapture Γ (Var.ofName n) (.val .bool)
      if g then
        return [.of Γ (.declLocal .bool (Var.ofName n) none)] ++
          (← elabValueCall Γ' ix (.name n) e a)
      pure [.of Γ (.declLocal .bool (Var.ofName n) none), .of Γ' (.send ix (r.wk th) (v.wk th) g)]
    | some _, _ => throw "`T x = r.send(a);` declares a name"
    | none, x =>
      match ← ElabM.lift (synth C Γ x) with
      | .val .bool (.simple (.local y)) =>
        if g then elabValueCall Γ y x e a else pure [.of Γ (.send y r v g)]
      | _ => throw s!"{x.toStr}: a send's result goes to a bool local"
  | .call (.name "constructor") args => elabCtor args
  | .call (.name f) args => elabCall f args none
  | .call .. => throw "only push, pop and transfer are calls on a receiver"
  | .ret _ => throw "`return` outside a function's body"
  | .brk => throw "`break` outside a loop"
  | .cont => throw "`continue` outside a loop"
  | .hole => throw "`_;` outside a modifier's body"
  | s@(.whileLoop ..) | s@(.forLoop ..) | s@(.doWhile ..) => do elabStmtsP (← lowerLoops none [s])
  | .loop a c body => do
    -- evaluated again each iteration, so it is not captured before the loop
    let Γ ← nctx
    let c ← loopExpr Γ .bool c "condition"
    -- quantified clauses alone: the plain invariant is `true`
    let a := if a.inv.isEmpty && !a.qinv.isEmpty then { a with inv := [.bool true] } else a
    let a : LoopAnn C Γ.ctx ← match a.inv, a.unwind with
      | [], u => do
        if a.dec.isSome then throw "a loop's `decreases` clause without an `invariant`"
        pure (u.map LoopAnn.unwind |>.getD LoopAnn.auto)
      | i :: is, none => do
        let I ← loopExpr Γ .bool (RawExpr.andAll (i :: is).dropLast ((i :: is).getLast?.getD i))
          "invariant"
        pure (.inv I (← a.dec.mapM fun d => loopExpr Γ .uint d "variant") a.brk
          (← a.qinv.mapM (loopQ Γ)))
      | _ :: _, some _ => throw "a loop has an `invariant` or an `unwind` clause, not both"
    pure [.of Γ (.loop a c (← elabScope Γ body).2)]
  | .block b => elabBranch b
  | .tupleAssign ts rhs => elabTuple ts rhs
  | .tupleDecl vs rhs => do
    -- `T x;` for each variable, then the tuple assigned to them
    for (_, x) in vs.filterMap id do
      if rhs.mentions x then throw s!"{rhs.toStr} reads {x}, which the tuple declares"
    let P ← elabStmtsP (vs.filterMap fun v => v.map fun (T, x) => .decl T x none)
    pure (P ++ (← elabTuple (vs.map fun v => v.map fun (_, x) => .name x) rhs (direct := true)))
  | .ite c thn els => do
    let Γ ← nctx
    let c ← checkIn C Γ .bool c
    let thn ← elabScope Γ thn
    let els ← elabScope Γ els
    pure [.of Γ (.ite c thn.2 els.2)]
  | .require c => do
    let Γ ← nctx
    pure [.of Γ (.require (← checkIn C Γ .bool c))]
  | .assert c => do
    let Γ ← nctx
    -- in a self-call's callee, where a `catch` reads it: `Panic(0x01)`'s data
    if (← read).selfFrame then
      return [.of Γ (.ite (← checkIn C Γ .bool c) .nil
        (.cons (.revertData [.bytes (Semantics.encodePanic 1)]) .nil))]
    pure [.of Γ (.assert (← checkIn C Γ .bool c))]
  | .revert => do pure [.of (← nctx) .revert]
  -- revert data, where a `try` reads it: in a self-call's callee
  | .revertMsg m => do
    if (← read).selfFrame then
      pure [.of (← nctx) (.revertData [.bytes (Semantics.encodeError m.toUTF8.toList)])]
    else pure [.of (← nctx) .revert]
  | .revertReason m => memoryRevert .reason m
  | .revertRaw d => memoryRevert .raw d
  | .requireReason c m => elabStmt1 (.ite c [] [.revertReason m])
  | .requireMsg c m => do
    if (← read).selfFrame then elabStmt1 (.ite c [] [.revertMsg m])
    else elabStmt1 (.require c)
  -- `revert E(a, b)`: `E`'s selector, folded as solc folds it
  -- (`errorSignature?`), then each argument's ABI word (a literal's folded)
  | .revertErr e args => do
    -- Each operand is read before the next one's calls or guards. Even
    -- ordinary reverts must preserve an argument's failure before reverting.
    let expected := ((lookupBy e C.errors).map fun d =>
      d.params.map fun (_, T) => match T with | .prim p => some p | _ => none).getD []
    let (P, args) ← eagerArgsWith C rc.hoist args (expected := expected)
    let Γ ← nctx
    if (← read).selfFrame then
      pure (P ++ [.of Γ (.revertData (← revertErrParts C Γ e args))])
    else pure (P ++ [.of Γ .revert])
  | .requireErr c _ args => elabStmt1 (RawStmt.requireWith c args)
  | .assumeFalse => do pure [.of (← nctx) .assumeFalse]
  | .eval _ => pure []
  | .unchecked ss => do
    withReader (fun sc => { sc with unchecked := true }) (elabBranch (← ElabM.lift (uncheckStmts ss)))
  | .checked o ss => do
    -- the guards made once, by the outermost block (`Prog.withOF`)
    match (← read).overflow with
    | some o' =>
      if o' == o then elabBranch ss
      else throw "`checked { … }` and `ignoringOverflow { … }` do not nest in each other"
    | none =>
      let P ← withReader (fun sc => { sc with overflow := some o }) (elabBranch ss)
      let sf := (← read).selfFrame
      pure (P.flatMap (SStmt.withOF o sf))
  | .tryCall e g as rets ok err code pnc other => do
    -- `I(a)` is `a`
    let funs := (← read).funs
    let e := match e with
      | .call h [a] => if funs.any (·.1 == h) then e else a
      | e => e
    let (P, addr) ← simpleOf C .uint e
    let mut Q := P
    let mut args : List ((Γ : NCtx) × ExtArg C Γ.ctx) := []
    for a in as do
      let some ⟨p, _⟩ := (← synthM C a).2.toVal? | throw s!"{a.toStr}: an external call's argument is a value"
      let (Q', ⟨Γa, se⟩) ← simpleOf C p a
      Q := Q ++ Q'
      args := args ++ [⟨Γa, ⟨p, se⟩⟩]
    let mut rets' : List (PrimTy × Var) := []
    let mut retWidths : List Nat := []
    for (T, x) in rets do
      let (.prim p, n) ← ElabM.lift (elabDeclTy C T) | throw s!"{x}: an external call returns a value"
      retWidths := retWidths ++ [n]
      rets' := rets' ++ [(p, Var.ofName x)]
    -- the call is read where its arguments' captures leave
    let Γ ← nctx
    let addr' := addr.2.wk (← ElabM.lift (addr.1.wkTo Γ))
    let args' ← args.mapM fun ⟨Γa, a⟩ => do
      pure (⟨a.1, a.2.wk (← ElabM.lift (Γa.wkTo Γ))⟩ : ExtArg C Γ.ctx)
    let ⟨ρ, bs⟩ := Binders.ofList rets'
    let ⟨κ, cb⟩ := CodeBinder.ofOption (code.map Var.ofName)
    let sb ← trySelfBody g args' ρ
    -- A concrete self frame returns typed numeric values, not encoded ABI
    -- words. Enable narrow returns only on this path; unknown-address bytesN
    -- words need distinct padding/alignment decoding and remain unsupported.
    let staticSelf := match e with
      | .env .selfAddress => true
      | _ => false
    if retWidths.any (· != 256) && !(staticSelf && sb.isSome) then
      throw "a narrow return value of an external call needs a resolved self frame"
    if staticSelf && sb.isSome && !rets.isEmpty then
      let some d := lookupBy g funs | throw "a self-call result needs its callee declaration"
      unless d.rets.length == rets.length do
        throw "a self-call result needs its callee's return arity"
      for ((T, _), (name, actualTy)) in rets.zip d.rets do
        let some actual := (fnRow? d.widths name).orElse fun _ =>
            abiTyName d.widths name actualTy
          | throw "a self-call result needs its source ABI type"
        let (requestedTy, requestedWidths) ← ElabM.lift (elabTyW C T)
        let some requested := (fnRow? requestedWidths "").orElse fun _ =>
            abiTyName requestedWidths "" requestedTy
          | throw "a self-call result needs its requested ABI type"
        unless selfReturnAbiCompatible actual requested do
          throw "a self-call result has incompatible ABI type"
    let (Γe, _) ← get
    let mut decodeChecks : List RawStmt := []
    for (((T, x), (p, _)), n) in (rets.zip rets').zip retWidths do
      declare C x (.val p n)
      -- Retain source observations only on the resolved typed-self path.
      -- Existing full-width world returns keep their existing representation.
      if staticSelf && sb.isSome then
        declareShape x (← ElabM.lift (bytesRowsOf C T))
      if n != 256 then
        -- Decode failure reverts the caller; its try's catches do not handle it.
        decodeChecks := decodeChecks ++ [.require (inTyCond p n (.name x))]
      else if staticSelf && sb.isSome then
        if let .named type := T then
          if type == "address" then
            decodeChecks := decodeChecks ++ [.require (inTyCond .uint 160 (.name x))]
          else if let some members := lookupBy type C.enums then
            decodeChecks := decodeChecks ++ [.require (.binop .lt (.name x) (.num members.length))]
    let ok ← elabStmtsP (decodeChecks ++ ok)
    let ok ← ElabM.lift (SProg.chain (bs.names ++ Γ.names) (ρ ++ Γ.ctx) ok)
    let (_, k) ← get
    set (Γe, k)
    -- a clause naming the data binds it (`Stmt.catchData`), read as the call
    let ⟨ps, Γf, sargs, sbody, self⟩ : (ps : Ctx) × (Γf : Ctx) × Args C Γ.ctx ps ×
        Prog C (ρ ++ ps) Γf × Bool := match sb with
      | some ⟨ps, Γf, sargs, sbody⟩ => ⟨ps, Γf, sargs, sbody, true⟩
      | none => ⟨[], ρ ++ [], .nil, .nil, false⟩
    let call : ExtCall C Γ.ctx := ⟨addr', g, args'⟩
    let clause (ss : List RawStmt) : ElabM (Blk C Γ.ctx) := do
      match RawStmt.catchBinder? ss with
      | (some kind, ss) =>
        ElabM.lift ((← elabScope Γ ss).toCatchData call bs sargs sbody self kind)
      | (none, ss) => elabScope Γ ss
    let err ← clause err
    let (_, k) ← get
    set (Γe, k)
    let pnc : Blk C (κ ++ Γ.ctx) ← match (RawStmt.catchBinder? pnc).1 with
      -- the catch-all's block in the `Panic` clause's place (no code bound)
      | some _ => do
        if h : κ = [] then
          let P ← clause pnc
          pure (by subst h; exact P)
        else throw "a `Panic` clause that binds the data"
      | none => do
        if let some c := code then declare C c (.val .uint)
        let pnc ← elabStmtsP (RawStmt.catchBinder? pnc).2
        ElabM.lift (SProg.chain (cb.names ++ Γ.names) (κ ++ Γ.ctx) pnc)
    let (_, k) ← get
    set (Γe, k)
    let other ← clause other
    pure (Q ++ [.of Γ (.tryCall call bs ok.2 err.2 cb pnc.2 other.2 sargs sbody self)])

end Elab

end Solidity
