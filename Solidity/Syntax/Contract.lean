import Solidity.Syntax.Grammar

/-!
# `contract!{ … }` and quoting

`contract!{ … }`, the contracts, and quoting.

A piece of `Syntax.lean`, whose docstring describes the whole.
-/

namespace Solidity

open Semantics

/-! ## `contract!{ … }`

A contract written as Solidity writes one, less what elaborates away: a
state variable's visibility, a function's visibility and mutability, events
and errors (declared, then dropped), and enums (read as `uint`, a member as
its position).  A modifier is inlined around the body of each function that
applies it (`wrapMods`), as a call is inlined where it is called. -/

declare_syntax_cat sol_member (behavior := both)

/-- A state variable's visibility, dropped. -/
declare_syntax_cat sol_vis (behavior := both)
syntax &"public" : sol_vis
syntax &"private" : sol_vis
syntax &"internal" : sol_vis
syntax &"immutable" : sol_vis
syntax &"constant" : sol_vis

/-- `uint public count;`: a state variable. -/
syntax sol_ty sol_vis* ident ";" : sol_member
/-- `uint x = 5;`: a state variable with an initializer, which the
constructor runs (`Contract.inits`).  A `constant` or an `immutable` is one
too, as solkey reads it: a storage root with an initializer. -/
syntax sol_ty sol_vis* ident " = " sol_expr ";" : sol_member

/-- A parameter, `uint x`. -/
declare_syntax_cat sol_param (behavior := both)
syntax sol_ty ident : sol_param
syntax sol_ty (&"memory" <|> &"storage" <|> &"calldata") ident : sol_param

/-- A function's attribute: its return variables, `returns (uint r)`,
`returns (Person memory p)`, `returns (uint lo, uint hi)`; a visibility or a
mutability (dropped); or a modifier applied, `onlyOwner`,
`inState(State.Created)`. -/
declare_syntax_cat sol_fattr (behavior := both)
syntax (name := solAttrReturns) &"returns" "(" sol_rparam,+ ")" : sol_fattr
syntax (name := solAttrKw) (&"public" <|> &"external" <|> &"internal" <|> &"private" <|> &"view" <|>
  &"pure" <|> &"payable" <|> &"virtual" <|> &"override") : sol_fattr
syntax (name := solAttrMod) ident ("(" sol_expr,* ")")? : sol_fattr

/-- `function f(uint x, uint y) returns (uint r) { r = x + y; }`: an internal
function, which may call the functions declared before it. -/
syntax &"function " ident "(" sol_param,* ")" sol_fattr* ppSpace sol_block : sol_member

/-- `constructor(uint v) payable { … }`: the contract's constructor
(`Contract.ctor`), which only a deployment calls, `constructor(args);`. -/
syntax (name := solConstructor) &"constructor" "(" sol_param,* ")" sol_fattr* ppSpace sol_block :
  sol_member

/-- `modifier inState(State s) { if (state != s) revert(); _; }`: the code
before and after its one `_;`. -/
syntax &"modifier " ident ("(" sol_param,* ")")? ppSpace sol_block : sol_member

/-- An event's or an error's parameter, `address indexed from`. -/
declare_syntax_cat sol_eparam (behavior := both)
syntax sol_ty (&"indexed")? (ppSpace ident)? : sol_eparam

/-- `event Sent(address from, uint amount);`, dropped. -/
syntax &"event " ident "(" sol_eparam,* ")" ";" : sol_member
/-- `error Unauthorized(uint code);`, dropped. -/
syntax &"error " ident "(" sol_eparam,* ")" ";" : sol_member
/-- `enum State { Created, Locked }`: `State.Locked` is `1`. -/
syntax &"enum " ident "{" ident,* "}" : sol_member
/-- `struct S { uint a; T[] xs; }`: a struct of the contract (`Contract.structs`). -/
syntax (name := solStruct) &"struct " ident "{" (sol_ty ident ";")* "}" : sol_member

/-- A clause of the specification, where solkey's NatSpec line stands:
`requires e;` and `ensures e;` above the function they specify (`/// @custom:key
requires e`), `skip;` for a function with no obligation, `invariant e;`
anywhere, a clause of the contract. -/
syntax (name := solRequires) (priority := high) &"requires " spec_expr ";" : sol_member
syntax (name := solEnsures) (priority := high) &"ensures " spec_expr ";" : sol_member
syntax (name := solSkip) (priority := high) &"skip" ";" : sol_member
syntax (name := solInvariant) (priority := high) &"invariant " spec_expr ";" : sol_member
/-- `assignable count, balances[msg.sender];` or `assignable \nothing;`: what
the next function may change (solkey's `@custom:key assignable`). -/
syntax (name := solAssignable) (priority := high) &"assignable " spec_locs ";" : sol_member

/-- `contract!{ uint total; Person alice; mapping(uint => Person) folks; }`:
a contract written as Solidity declares its state, and its functions. -/
syntax "contract!{" sol_member* "}" : term

section
open Lean

/-- The words among a function's attributes that are not modifiers. -/
def attrKeywords : List String :=
  ["public", "external", "internal", "private", "view", "pure", "payable", "virtual", "override"]

/-- What a type is read against in `contract!{ … }`: the contract's enums
(each a `uint`) and its own structs (`Contract.structs`). -/
structure TyEnv where
  enums : List String := []
  structs : List (String × String) := []

/-- A declared type, an enum of the contract read as `uint`, a struct of the
contract by its name in the table. -/
partial def expandMemberTy (env : TyEnv) (T : TSyntax `sol_ty) : MacroM Term :=
  if T.raw.isOfKind ``solFnTy then `(Ty.uint) else
  match T with
  | `(sol_ty| $x:ident) =>
    if env.enums.contains (x.getId.toString false) then `(Ty.uint)
    else match lookupBy (x.getId.toString false) env.structs with
      | some e => `(Ty.struct $(quote e))
      | none => `(ty!($T))
  | `(sol_ty| $E:sol_ty []) => do `(Ty.array $(← expandMemberTy env E))
  | `(sol_ty| $E:sol_ty [ $n:num ]) => do `(Ty.fixed $(← expandMemberTy env E) $n)
  | `(sol_ty| mapping ( $K:sol_ty => $V:sol_ty )) => do
    `(Ty.mapping pty!($K) $(← expandMemberTy env V))
  | _ => `(ty!($T))

/-- A member's type as a struct's name in the table spells it
(`Semantics.StructEnc`): a primitive type by its name, a narrow one as
written, a struct by its name in the table. -/
partial def spellTy (env : TyEnv) (T : TSyntax `sol_ty) : MacroM String := do
  -- a member of function type: its spelling, a `uint` with its marker
  -- (`Semantics.StructEnc.valueRowsOf`)
  if T.raw.isOfKind ``solFnTy then return ← spellFnTy T
  match T with
  -- an `address` as written: a `uint` and its marker
  | `(sol_ty| address payable) => pure "address"
  | `(sol_ty| $x:ident) =>
    let n := (x.getId.toString false)
    if env.enums.contains n then return "uint"
    if let some e := lookupBy n env.structs then return e
    if n == "address" then return n
    match PrimTy.ofName? n with
    | some p => return p.toStr
    | none =>
      -- a narrow integer, a `bytesN` (a `uint` and its marker), `bytes`, `string`
      if (narrowTy? n).isSome || (bytesTy? n).isSome || dynBytesTy n then return n
      if (structDef n).isEmpty then Macro.throwErrorAt x (unknownStructMsg n)
      return n
  | `(sol_ty| $E:sol_ty []) => return (← spellTy env E) ++ "[]"
  | `(sol_ty| $E:sol_ty [ $n:num ]) => return s!"{← spellTy env E}[{n.getNat}]"
  | `(sol_ty| mapping ( $K:sol_ty => $V:sol_ty )) =>
    return s!"mapping({← spellTy env K}=>{← spellTy env V})"
  | _ => Macro.throwUnsupported

/-- The contract's structs, each with its name in the table: the plain name
when the table's struct of that name has these members (and narrow widths),
else the name that spells them.  A struct is spelled once the contract's
structs its members name are; one that names itself, through any chain, is
refused, as the table's rank refuses it (`structDef_rank_lt`). -/
def expandStructs (enums : List String) (decls : Array (Ident × Array (TSyntax `sol_ty × Ident))) :
    MacroM (List (String × String)) := do
  let names := decls.toList.map ((·.1.getId.toString false))
  let mut done : List (String × String) := []
  for _ in [0:decls.size] do
    for (S, ms) in decls do
      let n := (S.getId.toString false)
      if (lookupBy n done).isSome then continue
      let waits := ms.any fun (T, _) => (T.raw.find? fun x =>
        x.isIdent && names.contains (x.getId.toString false) && (lookupBy (x.getId.toString false) done).isNone).isSome
      if waits then continue
      let env : TyEnv := { enums, structs := done }
      let fields ← ms.mapM fun (T, f) => do pure s!"{(f.getId.toString false)}:{← spellTy env T}"
      if fields.isEmpty then Macro.throwErrorAt S s!"struct {n}: a struct has a member"
      let enc := n ++ "{" ++ ";".intercalate fields.toList ++ "}"
      let some fs := Semantics.StructEnc.decode enc |
        Macro.throwErrorAt S s!"struct {n}: its members do not spell a struct: {enc}"
      if let some f := dupKey? fs then
        Macro.throwErrorAt S s!"struct {n}: identifier already declared: member {f}"
      -- the table's structs carry no `address` marker (`addressRows`)
      let ws := (Semantics.StructEnc.widths enc).filter (·.1.endsWith "#address" == false)
      let e := if structDef n == fs && structWidths n == ws then n else enc
      unless structDef e == fs do
        Macro.throwErrorAt S s!"struct {n}: nested past the struct table's rank bound \
          (`structRankCap`)"
      done := done ++ [(n, e)]
  for (S, _) in decls do
    if (lookupBy (S.getId.toString false) done).isNone then
      Macro.throwErrorAt S s!"struct {(S.getId.toString false)} contains itself: no struct of the \
        table does (`structDef_rank_lt`)"
  pure done

/-- `expandMemberTy` where a narrow type may stand: a `uint8` is `Ty.uint` and
its width. -/
def expandMemberTyW (enums : TyEnv) (T : TSyntax `sol_ty) : MacroM (Term × Option Nat) :=
  match T with
  | `(sol_ty| $x:ident) =>
    match narrowTy? (x.getId.toString false) with
    | some (.int, n) => do pure (← `(Ty.int), some n)
    | some (_, n) => do pure (← `(Ty.uint), some n)
    | none => do pure (← expandMemberTy enums T, none)
  | _ => do pure (← expandMemberTy enums T, none)

/-- A state variable's type, where a narrow type may stand inside it too: its
`Ty`, a `uint` or an `int` at each narrow position, and the widths of those
positions keyed by their path below the variable (`Contract.widths` prefixes
the name): `""` the variable, `"[]"` an element or a mapping's value, `"{}"` a
mapping's key (`mapping(uint8 => uint16[]) m` is `[("{}", 8), ("[][]", 16)]`).
A struct's narrow members are its type's (`Semantics.structWidths`).  A
parameter's and a return's type are read so too (`expandParamsW`). -/
partial def expandStateTyW (enums : TyEnv) (T : TSyntax `sol_ty) :
    MacroM (Term × List (String × Nat)) := do
  let narrow? (K : TSyntax `sol_ty) : Option (PrimTy × List (String × Nat)) := match K with
    | `(sol_ty| $x:ident) =>
      if enums.enums.contains (x.getId.toString false) then some (.uint, enumRows)
      else valueRows? (x.getId.toString false)
    | `(sol_ty| address payable) => some (.uint, addressRows)
    | _ => none
  -- a function type: its tag, a `uint`, and its marker (`valueRows?`)
  if T.raw.isOfKind ``solFnTy then
    return (← `(Ty.uint), ((valueRows? (← spellFnTy T)).map (·.2)).getD [])
  match T with
  | `(sol_ty| address payable) => return (← `(Ty.uint), addressRows)
  | `(sol_ty| $x:ident) =>
    if dynBytesTy (x.getId.toString false) then
      return (← `(Ty.array Ty.uint), dynBytesRowsOf (x.getId.toString false))
    -- an enum: a `uint` and its marker (`enumRows`)
    if enums.enums.contains (x.getId.toString false) then return (← `(Ty.uint), enumRows)
    match valueRows? (x.getId.toString false) with
    | some (.int, ws) => pure (← `(Ty.int), ws)
    | some (_, ws) => pure (← `(Ty.uint), ws)
    | none => pure (← expandMemberTy enums T, [])
  | `(sol_ty| $E:sol_ty []) => do
    let (t, ws) ← expandStateTyW enums E
    if ws.isEmpty then return (← expandMemberTy enums T, [])
    pure (← `(Ty.array $t), ws.map fun (k, n) => ("[]" ++ k, n))
  | `(sol_ty| $E:sol_ty [ $m:num ]) => do
    let (t, ws) ← expandStateTyW enums E
    if ws.isEmpty then return (← expandMemberTy enums T, [])
    pure (← `(Ty.fixed $t $m), ws.map fun (k, n) => ("[]" ++ k, n))
  | `(sol_ty| mapping ( $K:sol_ty => $V:sol_ty )) => do
    let (t, ws) ← expandStateTyW enums V
    -- a byte string as a key: its `keccak256`, a `uint` (`hashKeyRows`)
    if let `(sol_ty| $k:ident) := K then
      if dynBytesTy (k.getId.toString false) then
        return (← `(Ty.mapping PrimTy.uint $t), hashKeyRows ++ ws.map fun (k, n) => ("[]" ++ k, n))
    let (kt, kw) ← match narrow? K with
      | some (.int, ws) => pure (← `(PrimTy.int), ws.map fun (k, n) => ("{}" ++ k, n))
      | some (_, ws) => pure (← `(PrimTy.uint), ws.map fun (k, n) => ("{}" ++ k, n))
      | none => pure (← `(pty!($K)), [])
    if ws.isEmpty && kw.isEmpty then return (← expandMemberTy enums T, [])
    pure (← `(Ty.mapping $kt $t), kw ++ ws.map fun (k, n) => ("[]" ++ k, n))
  | _ => pure (← expandMemberTy enums T, [])

/-- A function's parameters, and the rows of `FunDecl.widths` for the narrow
ones and the narrow positions inside one (`expandStateTyW`). -/
def expandParamsW (enums : TyEnv) (ps : Array (TSyntax `sol_param)) :
    MacroM (Array Term × Array Term × Array Term) := do
  let mut rows := #[]
  let mut ws := #[]
  let mut locs := #[]
  for p in ps do
    let (T, x, loc) ← match p with
      | `(sol_param| $T:sol_ty $x:ident) => pure (T, x, none)
      | `(sol_param| $T:sol_ty memory $x:ident) => pure (T, x, some ParamLoc.memory)
      | `(sol_param| $T:sol_ty storage $x:ident) => pure (T, x, some ParamLoc.storage)
      | `(sol_param| $T:sol_ty calldata $x:ident) => pure (T, x, some ParamLoc.calldata)
      | _ => Macro.throwUnsupported
    let (t, w) ← expandStateTyW enums T
    rows := rows.push (← `(($(strLit x), $t)))
    for (k, n) in w do ws := ws.push (← `(($(quote ((x.getId.toString false) ++ k)), $(quote n))))
    if let some loc := loc then
      let l ← match loc with
        | .memory => `(ParamLoc.memory)
        | .storage => `(ParamLoc.storage)
        | .calldata => `(ParamLoc.calldata)
      locs := locs.push (← `(($(strLit x), $l)))
  pure (rows, ws, locs)

/-- A modifier: its name, its parameters, and its body, with a `_;` at least
(solc's "Modifier body does not contain '_'"), anywhere. -/
def expandModifier (enums : TyEnv) (m : Ident) (ps : Array (TSyntax `sol_param))
    (b : TSyntax `sol_block) : MacroM (String × Array Term × Term × Array Term × Array Term) := do
  let `(sol_block| { $[$ss:sol_stmt;]* }) := b | Macro.throwErrorAt b "a modifier's body is a block"
  unless (b.raw.find? (·.isOfKind ``solHole)).isSome do
    Macro.throwErrorAt b "a modifier's body has a `_;`"
  -- a parameter as a function's (`expandParamsW`): a narrow one (`uint8 n`) a
  -- `uint` of its width, a reference one (`uint8[] memory xs`) its location
  -- and its narrow positions (`ModApp.widths`, `ModApp.locs`)
  let (rows, ws, locs) ← expandParamsW enums ps
  pure ((m.getId.toString false), rows, ← `([$(← ss.mapM expandStmt),*]), ws, locs)

/-- A function's declaration, as a term: its return variable and its
modifiers read off its attributes. -/
def expandFun (enums : TyEnv)
    (mods : List (String × Array Term × Term × Array Term × Array Term)) (f : Ident)
    (ps : Array (TSyntax `sol_param)) (attrs : Array (TSyntax `sol_fattr))
    (b : TSyntax `sol_block) (spec : Term) : MacroM Term := do
  -- Keep source locations before expandParamsW replaces parameters by
  -- their typed declarations: only these names establish calldata origin.
  let calldataRoots : List String := ps.toList.filterMap fun p =>
    match p.raw with
    | `(sol_param| $T:sol_ty calldata $x:ident) =>
      let _ := T
      some (x.getId.toString false)
    | _ => none
  let (ps, ws, locs) ← expandParamsW enums ps
  let mut ws := ws
  -- `payable` is an atom of the keyword reading and an identifier of the
  -- modifier reading
  let payable := attrs.any fun a => (a.raw.find? fun s =>
    s.isAtom && s.getAtomVal == "payable" || s.isIdent && s.getId == `payable).isSome
  let mut rets : Array Term := #[]
  let mut retMem := false
  let mut retStorage := false
  let mut apps : Array Term := #[]
  for a in attrs do
    -- `returns (uint)` also reads as a modifier `returns` applied to `uint`,
    -- and `view` as a modifier `view`: take the other reading
    let a := preferReading a.raw (!·.isOfKind ``solAttrMod)
    if a.isOfKind ``solAttrKw then continue
    if a.isOfKind ``solAttrReturns then
      -- Return locations are separate from external try/catch parameters.
      let ps := a[2].getSepArgs
      for i in [0:ps.size] do
        -- A location also reads as the return variable's name: take the location.
        let p := preferReading ps[i]! (!·[1].isNone)
        let n := (p[2].getOptional?.map ((·.getId.toString false))).getD
          (if ps.size == 1 then "_ret" else s!"_ret{i}")
        let (t, w) ← expandStateTyW enums ⟨p[0]⟩
        for (k, b) in w do ws := ws.push (← `(($(quote (n ++ k)), $(quote b))))
        rets := rets.push (← `(($(quote n), $t)))
        retMem := retMem || (p[1].find? fun s => s.isAtom && s.getAtomVal == "memory").isSome
        retStorage := retStorage || (p[1].find? fun s => s.isAtom && s.getAtomVal == "storage").isSome
      continue
    match (⟨a⟩ : TSyntax `sol_fattr) with
    | `(sol_fattr| $m:ident $[( $as:sol_expr,* )]?) =>
      let name := (m.getId.toString false)
      if attrKeywords.contains name then continue
      let some (_, params, mb, mws, mlocs) := mods.find? (·.1 == name) |
        Macro.throwErrorAt m s!"{name} is not a modifier of this contract"
      let args ← match as with
        | some as => as.getElems.mapM expandExpr
        | none => pure #[]
      apps := apps.push (← `(ModApp.mk $(quote name) [$params,*] [$args,*] $mb [$mws,*] [$mlocs,*]))
    | _ => Macro.throwUnsupported
  let body ← expandStmt.expandBlock b
  -- a body with a slice reads it as a view (`RawStmt.sliceViews`, `Syntax/Elab.lean`)
  let body ← if (b.raw.find? fun s => [``solSlice, ``solSliceFrom, ``solSliceTo, ``solSliceAll, ``solCalldataLocal].contains s.getKind).isSome
    then `($(mkIdent `Solidity.RawStmt.sliceViews) $body $(quote calldataRoots)) else pure body
  `(($(strLit f),
    ({ params := [$ps,*], paramLocs := [$locs,*], rets := [$rets,*], retMem := $(quote retMem),
       retStorage := $(quote retStorage), body := $body,
       mods := [$apps,*], spec := $spec, payable := $(quote payable),
       widths := [$ws,*] } : FunDecl)))

end

macro_rules
  | `(contract!{ $ms:sol_member* }) => do
      -- the enums and the modifiers first: a function may apply a modifier
      -- declared after it
      let mut enums : List String := []
      let mut enumRows : Array Lean.Term := #[]
      let mut mods := []
      for m in ms do
        match m with
        | `(sol_member| enum $e:ident { $xs:ident,* }) =>
          enums := enums ++ [(e.getId.toString false)]
          enumRows := enumRows.push (← `(($(strLit e), [$(xs.getElems.map strLit),*])))
        | _ => pure ()
      let mut decls := #[]
      for m in ms do
        match m with
        | `(sol_member| struct $S:ident { $[$Ts:sol_ty $fs:ident ;]* }) =>
          decls := decls.push (S, Ts.zip fs)
        | _ => pure ()
      let structs ← expandStructs enums decls
      let structRows ← structs.toArray.mapM fun (n, e) => `(($(Lean.quote n), $(Lean.quote e)))
      let env : TyEnv := { enums, structs }
      for m in ms do
        match m with
        | `(sol_member| modifier $f:ident $[( $ps:sol_param,* )]? $b:sol_block) =>
          mods := mods ++ [← expandModifier env f ((ps.map (·.getElems)).getD #[]) b]
        | _ => pure ()
      let mut rows := #[]
      let mut widthRows : Array Lean.Term := #[]
      let mut errRows : Array Lean.Term := #[]
      let mut funs := #[]
      -- the clauses read since the last function: they specify the next one
      let mut reqs : Array Lean.Term := #[]
      let mut enss : Array Lean.Term := #[]
      let mut skip := false
      let mut asg : Option Lean.Term := none
      let mut invs : Array Lean.Term := #[]
      let mut ctor : Option Lean.Term := none
      let mut initRows : Array Lean.Term := #[]
      for m in ms do
        -- `requires x;` also reads as a state variable `x` of a type `requires`
        let m : Lean.TSyntax `sol_member := ⟨preferReading m.raw fun a =>
          [``solRequires, ``solEnsures, ``solSkip, ``solInvariant, ``solAssignable].any a.isOfKind⟩
        match m with
        | `(sol_member| requires $e:spec_expr ;) => reqs := reqs.push (← expandSpec e)
        | `(sol_member| ensures $e:spec_expr ;) => enss := enss.push (← expandSpec e)
        | `(sol_member| skip ;) => skip := true
        | `(sol_member| assignable $ls:spec_locs ;) =>
          if asg.isSome then Lean.Macro.throwErrorAt m "one `assignable` clause per function"
          asg := some (← expandSpecLocs ls)
        | `(sol_member| invariant $e:spec_expr ;) => invs := invs.push (← expandSpec e)
        | `(sol_member| $T:sol_ty $_:sol_vis* $x:ident ;) =>
          let (t, ws) ← expandStateTyW env T
          rows := rows.push (← `(($(strLit x), $t)))
          for (k, n) in ws do
            widthRows := widthRows.push (← `(($(Lean.quote ((x.getId.toString false) ++ k)), $(Lean.quote n))))
        | `(sol_member| $T:sol_ty $_:sol_vis* $x:ident = $e:sol_expr ;) =>
          let (t, ws) ← expandStateTyW env T
          rows := rows.push (← `(($(strLit x), $t)))
          for (k, n) in ws do
            widthRows := widthRows.push (← `(($(Lean.quote ((x.getId.toString false) ++ k)), $(Lean.quote n))))
          initRows := initRows.push (← `(($(strLit x), $(← expandExpr e))))
        | `(sol_member| constructor ( $ps:sol_param,* ) $as:sol_fattr* $b:sol_block) =>
          if ctor.isSome then Lean.Macro.throwErrorAt m "a second constructor: a contract declares one"
          for a in as do
            if (preferReading a.raw (!·.isOfKind ``solAttrMod)).isOfKind ``solAttrReturns then
              Lean.Macro.throwErrorAt a "a constructor returns nothing: no `returns`"
          let asgT ← match asg with
            | some ls => `(some $ls)
            | none => `(none)
          let spec ← `(({ requires := [$reqs,*], ensures := [$enss,*], assignable := $asgT,
                          skip := $(Lean.quote skip) } : FunSpec))
          let d ← expandFun env mods (Lean.mkIdent `constructor) ps.getElems as b spec
          ctor := some (← `(some ($d).2))
          reqs := #[]; enss := #[]; skip := false; asg := none
        | `(sol_member| function $f:ident ( $ps:sol_param,* ) $as:sol_fattr* $b:sol_block) =>
          if (f.getId.toString false) == "constructor" then
            Lean.Macro.throwErrorAt f "`constructor` names the constructor, not a function"
          let asgT ← match asg with
            | some ls => `(some $ls)
            | none => `(none)
          let spec ← `(({ requires := [$reqs,*], ensures := [$enss,*], assignable := $asgT,
                          skip := $(Lean.quote skip) } : FunSpec))
          funs := funs.push (← expandFun env mods f ps.getElems as b spec)
          reqs := #[]; enss := #[]; skip := false; asg := none
        | `(sol_member| error $e:ident ( $ps:sol_eparam,* ) ;) =>
          -- its parameters, typed as a function's (`Contract.errors`)
          let mut prs : Array Lean.Term := #[]
          let mut ews : Array Lean.Term := #[]
          let pes := ps.getElems
          for i in [0:pes.size] do
            let n := s!"_e{i}"
            let (t, w) ← expandStateTyW env ⟨pes[i]!.raw[0]⟩
            for (k, b) in w do ews := ews.push (← `(($(Lean.quote (n ++ k)), $(Lean.quote b))))
            prs := prs.push (← `(($(Lean.quote n), $t)))
          errRows := errRows.push
            (← `(($(strLit e), ({ params := [$prs,*], widths := [$ews,*], body := [] } : FunDecl))))
        | `(sol_member| modifier $_:ident $[( $_:sol_param,* )]? $_:sol_block)
        | `(sol_member| event $_:ident ( $_:sol_eparam,* ) ;)
        | `(sol_member| enum $_:ident { $_:ident,* })
        | `(sol_member| struct $_:ident { $[$_:sol_ty $_:ident ;]* }) => pure ()
        | _ => Lean.Macro.throwUnsupported
      unless reqs.isEmpty && enss.isEmpty && !skip && asg.isNone do
        Lean.Macro.throwError
          "a `requires`, `ensures`, `assignable` or `skip` clause after the last function"
      let ctorT ← match ctor with
        | some t => pure t
        | none => `(none)
      `(({ vars := [$rows,*], funs := [$funs,*], enums := [$enumRows,*], inv := [$invs,*],
           widths := [$widthRows,*], ctor := $ctorT, inits := [$initRows,*],
           structs := [$structRows,*], errors := [$errRows,*] } : Contract))
/-! ### The contracts

One per store of `Semantics.lean`, under the store's renames, with
`address` read as `uint` as the interpreter does.  `initStorage_*` there
checks each against its store. -/

/-- `StandardExample.sol`, with the `people` array of the worked examples. -/
def StandardExample : Contract := contract!{
  uint total; uint age; uint owner; uint balance;
  uint[] values;
  mapping(uint => uint) balances;
  mapping(uint => bool) flags;
  mapping(uint => Person) folks;
  uint[][] matrix;
  Person[] persons;
  Person[] people;
  Person alice; Person bob;
  Wallet wallet;
}

/-- `TestSuite.sol`, as ported. -/
def TestSuite : Contract := contract!{
  uint total; uint age; uint owner; uint balance;
  uint[] values; uint[] aux;
  uint[][] matrix;
  mapping(uint => uint) balances;
  mapping(uint => Person) folks;
  mapping(uint => bool) flags;
  mapping(uint => uint) valuesMap;
  mapping(uint => Account) accountMap;
  Person[] persons;
  Person alice; Person bob;
  Ledger ledger;
  Token[] tokens;
  TokenBucket bucket;
  LedgerUse[] ledgerUses;
  bool flag; bool flag2;
  bool[] boolFlags;
  Toggle toggle;
  Token tok;
  TokenBucket[] buckets;
  Basket basketA; Basket basketB;
  int signedTotal;
  uint[3] fixedValues;
  uint[3][] rows;
  Token[2] fixedTokens;
  mapping(uint => uint)[2] fixedMaps;
  FixedTriple triple; FixedTriple triple2;
  mapping(uint => mapping(uint => uint)) grid;
  mapping(uint => Ledger) ledgerMap;
  mapping(uint => uint)[] mapArray;
}

/-- `solc/SolcExpressions.sol`. -/
def SolcExpressions : Contract := contract!{ uint counter; }

/-- `solc/SolcStructs.sol`, less the `Flagged`/`Depth*` family. -/
def SolcStructs : Contract := contract!{
  Simple data1; WithArray withArray; Triple triple;
  uint neighbourBefore; uint neighbourAfter;
  Pair source; Pair target;
  Pair[] pairs1; Pair[] pairs2;
  mapping(uint => Simple) campaigns;
}

/-- `solc/SolcArrays.sol`. -/
def SolcArrays : Contract := contract!{
  uint[] storageArray; uint[][] matrix; Pair[] structs;
}

/-- `solc/SolcMemory.sol`. -/
def SolcMemory : Contract := contract!{
  Outer outerX; Inner innerS; Inner[] inners; uint[] prims;
}

/-- `solc/SolcMappings.sol`. -/
def SolcMappings : Contract := contract!{
  S sBox; WithSub withSub;
  mapping(uint => S) sMap;
  mapping(uint => WithSub) withSubMap;
  mapping(uint => uint) balances;
  mapping(uint => uint[]) arrayMap;
  uint[][] rows;
  Ledger ledger;
}

/-- Internal functions (`Examples/Tactics/Calls.lean`): a function may call the ones
declared before it. -/
def CallsExample : Contract := contract!{
  uint total; uint count;
  mapping(uint => uint) balances;
  function addOne(uint x) returns (uint r) { r = x + 1; }
  function double(uint x) returns (uint) { return x + x; }
  function addTwo(uint x) returns (uint r) { r = addOne(x); r = addOne(r); }
  function credit(uint a, uint v) { balances[a] += v; total += v; }
  function larger(uint a, uint b) returns (uint) { if (a > b) { return a; } else { return b; }; }
  function bump() { count++; }
}

/-- `solc/SolcControlFlow.sol`. -/
def SolcControlFlow : Contract := contract!{
  Pair sx; Pair sy; Pair target; uint[] values;
}



/-! ## Quoting

The elaborated block is turned back into a term by hand, because
`deriving ToExpr` cannot handle an indexed family whose constructors carry
proofs.  The contract is the constant it names, and every proof is spelt
`Eq.refl`, so the kernel re-checks each one by computing `rootType`,
`fieldType` or the Boolean check. -/

deriving instance Lean.ToExpr for PrimTy
deriving instance Lean.ToExpr for RefTy, Ty
deriving instance Lean.ToExpr for BinOp
deriving instance Lean.ToExpr for UnOp
deriving instance Lean.ToExpr for IncDec
deriving instance Lean.ToExpr for EnvKey

section Quote
open Lean (mkAppN mkConst toExpr)

/-- `a = a`. -/
def quoteRefl (α a : Lean.Expr) : Lean.Expr := mkAppN (mkConst ``Eq.refl [1]) #[α, a]

/-- `p = p`, at `PrimTy`. -/
def rflPrim (p : PrimTy) : Lean.Expr := quoteRefl (mkConst ``PrimTy) (toExpr p)

/-- `true = true`: every Boolean side condition. -/
def rflTrue : Lean.Expr := quoteRefl (mkConst ``Bool) (mkConst ``Bool.true)

/-- `some T = some T`: every contract lookup. -/
def rflSome (T : Ty) : Lean.Expr :=
  quoteRefl (mkAppN (mkConst ``Option [0]) #[mkConst ``Ty])
    (mkAppN (mkConst ``Option.some [0]) #[mkConst ``Ty, toExpr T])

def optE (α : Lean.Expr) : Option Lean.Expr → Lean.Expr
  | none => mkAppN (mkConst ``Option.none [0]) #[α]
  | some a => mkAppN (mkConst ``Option.some [0]) #[α, a]

def ArrTy.quote : {R : RefTy} → {E : Ty} → ArrTy R E → Lean.Expr
  | _, _, @ArrTy.dyn E => mkAppN (mkConst ``ArrTy.dyn) #[toExpr E]
  | _, _, @ArrTy.fixed E n => mkAppN (mkConst ``ArrTy.fixed) #[toExpr E, toExpr n]

def IndexTy.quote : {R : RefTy} → {k : PrimTy} → {V : Ty} → IndexTy R k V → Lean.Expr
  | _, _, _, @IndexTy.map k V => mkAppN (mkConst ``IndexTy.map) #[toExpr k, toExpr V]
  | _, _, _, @IndexTy.arr R E a => mkAppN (mkConst ``IndexTy.arr) #[toExpr R, toExpr E, ArrTy.quote a]

end Quote

end Solidity
