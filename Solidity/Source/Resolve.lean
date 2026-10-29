import Solidity.Source.Decls

/-!
# Name resolution (S01)

How a name in a source unit denotes a declaration, a local or a builtin,
over S00's declaration graph (`Solidity/Source/Decls.lean`):

- `Env.linearize`: solc's C3 linearization of a contract's bases
  (`L(C) = C :: merge(L(Bₙ), …, L(B₁), [Bₙ, …, B₁])` for `contract C is B₁, …,
  Bₙ`), `none` when the hierarchy has a cycle or no linearization (both
  compile errors);
- `Env.lookup`: the declarations a name denotes in a contract (its members,
  then its bases' in linearization order, the first that declares it) or at
  file level, as an overload set;
- `Builtin`: the global names and magic members, each classified against
  the profile with its manifest feature (`Builtin.status`), so an excluded
  builtin (`gasleft`, `block.number`, `tx.origin`, `selfdestruct`, …) is
  rejected precisely at resolution;
- `Resolves`: the resolution judgment (locals shadow members, members
  shadow file-level declarations, declarations shadow builtins), with the
  function `Env.resolve` sound and complete for it (`resolve_iff`), hence
  functional (`Resolves.unique`).
-/

namespace Solidity.Source

/-- Whether a declaration is `private` (a state variable or function). -/
def Decl.isPrivate (d : Decl) : Bool :=
  match d.kind, d.top, d.node with
  | .stateVar, _, .stateVar _ (some .priv) _ _ _ _ _ => true
  | .function, _, .function _ _ (some .priv) _ _ _ _ _ _ => true
  | _, _, _ => false

/-- The resolution environment of a source unit: its declarations. -/
structure Env where
  decls : List Decl

/-- The environment of a source unit. -/
def Syn.env (u : Syn .unit) : Env := ⟨u.decls⟩

namespace Env

/-- The direct bases of a contract, in `is` order (each base by the last
component of its path). -/
def bases (E : Env) (c : String) : List String :=
  match E.decls.find? (fun d => d.scope == Option.none && d.name == c &&
      (d.kind == .contract || d.kind == .interface)) with
  | Option.some ⟨.contract, _, _, _, .contract _ _ _ is _⟩ => names is
  | Option.some ⟨.interface, _, _, _, .interface _ is _⟩ => names is
  | _ => []
where
  /-- The last components of the base paths. -/
  names {c : Cat} (is : Syn c) : List String := (inheritPaths is).map fun p => p.tail.getLast?.getD p.head

/-- C3 merge: repeatedly take the first head that occurs in no list's tail. -/
def merge : Nat → List (List String) → Option (List String)
  | 0, _ => Option.none
  | fuel + 1, ls =>
    let ls := ls.filter (· ≠ [])
    if ls.isEmpty then Option.some []
    else
      match ls.findSome? fun l => l.head?.filter fun h => ls.all fun l' => !(l'.drop 1).contains h with
      | Option.none => Option.none
      | Option.some h => (merge fuel (ls.map fun l => l.filter (· ≠ h))).map (h :: ·)

/-- **C3 linearization** of a contract, most derived first; `none` on a cycle
or an inconsistent hierarchy.  `fuel` bounds the depth (the number of
declarations suffices). -/
def linearizeF (E : Env) : Nat → String → Option (List String)
  | 0, _ => Option.none
  | fuel + 1, c =>
    let bs := (E.bases c).reverse
    match bs.mapM (E.linearizeF fuel) with
    | Option.none => Option.none
    | Option.some ls => (merge (E.decls.length * E.decls.length + 2) (ls ++ [bs])).map (c :: ·)

/-- The linearization with enough fuel for every acyclic hierarchy. -/
def linearize (E : Env) (c : String) : Option (List String) := E.linearizeF (E.decls.length + 1) c

/-- The declarations named `x` directly in scope `s`. -/
def declared (E : Env) (s : Option String) (x : String) : List Decl :=
  E.decls.filter fun d => d.scope == s && d.name == x && x != ""

/-- The declarations named `x` in scope `s` visible from `scope`: a base's
`private` members are not. -/
def visible (E : Env) (scope s : Option String) (x : String) : List Decl :=
  (E.declared s x).filter fun d => s == scope || !d.isPrivate

/-- **Lookup** of a name in a contract: the first scope of its
linearization that declares it visibly, else file level.  (Overloads
inherited from several bases are not merged: the first scope's set is the
overload set.) -/
def lookup (E : Env) (scope : Option String) (x : String) : List Decl :=
  let chain : List (Option String) :=
    match scope with
    | Option.none => []
    | Option.some c => ((E.linearize c).getD [c]).map Option.some
  match chain.find? (fun s => !(E.visible scope s x).isEmpty) with
  | Option.some s => E.visible scope s x
  | Option.none => E.declared Option.none x

/-- Whether every base of every contract and interface is a contract or
interface declared earlier at file level (solc: a base precedes its
derived contract; a library is no base; an interface inherits only
interfaces). -/
def basesOK (E : Env) : Bool :=
  (E.decls.zipIdx).all fun (d, i) =>
    !(d.kind == .contract || d.kind == .interface) ||
      (E.bases d.name).all fun b =>
        ((E.decls.zipIdx).take i).any fun (d', _) =>
          d'.scope == Option.none && d'.name == b &&
            (d'.kind == .interface || (d.kind == .contract && d'.kind == .contract))

end Env

/-! ## Builtins -/

/-- Whether a builtin is in the profile, and the manifest feature that
decides it. -/
inductive Status where
  | admitted (feature : String)
  | excluded (feature : String)
  | removed (feature : String)
  deriving DecidableEq, Repr

/-- The global names of Solidity 0.8.38. -/
inductive Builtin where
  | msg | block | tx | abi | this | super
  | keccak256 | sha256 | ripemd160 | ecrecover | addmod | mulmod
  | assert | require | revert | gasleft | blockhash | blobhash | selfdestruct | erc7201
  | now | suicide | sha3
  deriving DecidableEq, Repr

/-- The spelling of a builtin. -/
def Builtin.name : Builtin → String
  | .msg => "msg" | .block => "block" | .tx => "tx" | .abi => "abi" | .this => "this"
  | .super => "super" | .keccak256 => "keccak256" | .sha256 => "sha256"
  | .ripemd160 => "ripemd160" | .ecrecover => "ecrecover" | .addmod => "addmod"
  | .mulmod => "mulmod" | .assert => "assert" | .require => "require" | .revert => "revert"
  | .gasleft => "gasleft" | .blockhash => "blockhash" | .blobhash => "blobhash"
  | .selfdestruct => "selfdestruct" | .erc7201 => "erc7201" | .now => "now"
  | .suicide => "suicide" | .sha3 => "sha3"

/-- Every builtin, for lookup by name. -/
def Builtin.all : List Builtin :=
  [.msg, .block, .tx, .abi, .this, .super, .keccak256, .sha256, .ripemd160, .ecrecover, .addmod,
    .mulmod, .assert, .require, .revert, .gasleft, .blockhash, .blobhash, .selfdestruct,
    .erc7201, .now, .suicide, .sha3]

/-- The builtin of a name. -/
def Builtin.ofName (x : String) : Option Builtin := Builtin.all.find? (·.name == x)

/-- The profile status of a global builtin (G00's manifest). `msg`, `block`,
`tx` are namespaces: their members decide (`Builtin.memberStatus`). -/
def Builtin.status : Builtin → Status
  | .msg => .admitted "msgSender" | .block => .admitted "blockTimestamp"
  | .tx => .admitted "names" | .abi => .admitted "abiEncode" | .this => .admitted "thisAddress"
  | .super => .admitted "internalCalls" | .keccak256 => .admitted "keccakBuiltin"
  | .sha256 => .admitted "sha256Builtin" | .ripemd160 => .admitted "ripemd160Builtin"
  | .ecrecover => .admitted "ecrecoverBuiltin" | .addmod => .admitted "addmodBuiltin"
  | .mulmod => .admitted "mulmodBuiltin" | .assert => .admitted "assertBuiltin"
  | .require => .admitted "requireBuiltin" | .revert => .admitted "revertBuiltin"
  | .gasleft => .excluded "gasleft" | .blockhash => .excluded "blockhashBuiltin"
  | .blobhash => .excluded "blobhashBuiltin" | .selfdestruct => .excluded "selfdestruct"
  | .erc7201 => .admitted "erc7201Builtin"
  | .now | .suicide | .sha3 => .removed "removedAliases"

/-- The profile status of a magic member `g.m`, `none` for a member that
does not exist. -/
def Builtin.memberStatus : Builtin → String → Option Status
  | .msg, "sender" => Option.some (.admitted "msgSender")
  | .msg, "value" => Option.some (.admitted "msgValue")
  | .msg, "data" | .msg, "sig" => Option.some (.excluded "rawCalldata")
  | .msg, "gas" => Option.some (.removed "removedAliases")
  | .block, "timestamp" => Option.some (.admitted "blockTimestamp")
  | .block, "number" => Option.some (.excluded "blockNumber")
  | .block, "basefee" => Option.some (.excluded "blockBasefee")
  | .block, "blobbasefee" => Option.some (.excluded "blockBlobbasefee")
  | .block, "chainid" => Option.some (.excluded "blockChainid")
  | .block, "coinbase" => Option.some (.excluded "blockCoinbase")
  | .block, "difficulty" => Option.some (.excluded "blockDifficulty")
  | .block, "gaslimit" => Option.some (.excluded "blockGaslimit")
  | .block, "prevrandao" => Option.some (.excluded "blockPrevrandao")
  | .block, "slotnum" => Option.some (.excluded "blockSlotnum")
  | .block, "blockhash" => Option.some (.removed "removedAliases")
  | .tx, "origin" => Option.some (.excluded "txOrigin")
  | .tx, "gasprice" => Option.some (.excluded "txGasprice")
  | .abi, "encode" => Option.some (.admitted "abiEncode")
  | .abi, "encodePacked" => Option.some (.admitted "abiEncodePacked")
  | .abi, "encodeWithSelector" => Option.some (.admitted "abiEncodeWithSelector")
  | .abi, "encodeWithSignature" => Option.some (.admitted "abiEncodeWithSignature")
  | .abi, "encodeCall" => Option.some (.admitted "abiEncodeCall")
  | .abi, "decode" => Option.some (.admitted "abiDecode")
  | _, _ => Option.none

/-- The profile status of an address member (`a.m`). -/
def addressMemberStatus : String → Option Status
  | "balance" => Option.some (.admitted "addressBalance")
  | "code" => Option.some (.excluded "addressCode")
  | "codehash" => Option.some (.excluded "addressCodehash")
  | "call" => Option.some (.excluded "lowLevelCall")
  | "delegatecall" => Option.some (.excluded "delegatecall")
  | "staticcall" => Option.some (.excluded "lowLevelStaticcall")
  | "send" | "transfer" => Option.some (.admitted "sendTransfer")
  | "callcode" => Option.some (.removed "removedAliases")
  | _ => Option.none

/-- The profile status of a call option name (`f{name: …}`). -/
def callOptionStatus : String → Option Status
  | "value" => Option.some (.admitted "valueOption")
  | "gas" => Option.some (.excluded "gasOption")
  | "salt" => Option.some (.excluded "create2Salt")
  | _ => Option.none

/-! ## The resolution judgment -/

/-- What a name denotes. -/
inductive Denot where
  /-- The `i`-th local, innermost first. -/
  | loc (i : Nat)
  /-- An overload set of declarations, all with the name. -/
  | decls (ds : List Decl)
  | builtin (b : Builtin)

/-- **The resolution judgment**: a local shadows every declaration; a
declaration found by `lookup` shadows a builtin; a builtin is denoted only
when nothing is declared with its name. -/
inductive Resolves (E : Env) (locals : List String) (scope : Option String) (x : String) :
    Denot → Prop where
  | inLocals (i : Nat) (h : locals.idxOf? x = Option.some i) : Resolves E locals scope x (.loc i)
  | decl (h₁ : locals.idxOf? x = Option.none) (h₂ : E.lookup scope x ≠ []) :
      Resolves E locals scope x (.decls (E.lookup scope x))
  | builtin (b : Builtin) (h₁ : locals.idxOf? x = Option.none) (h₂ : E.lookup scope x = [])
      (h₃ : Builtin.ofName x = Option.some b) : Resolves E locals scope x (.builtin b)

/-- The resolution function. -/
def Env.resolve (E : Env) (locals : List String) (scope : Option String) (x : String) : Option Denot :=
  match locals.idxOf? x with
  | Option.some i => Option.some (.loc i)
  | Option.none =>
    match E.lookup scope x with
    | [] => (Builtin.ofName x).map Denot.builtin
    | ds => Option.some (.decls ds)

theorem Env.resolve_sound {E : Env} {locals : List String} {scope : Option String} {x : String}
    {r : Denot} (h : E.resolve locals scope x = Option.some r) : Resolves E locals scope x r := by
  unfold Env.resolve at h
  cases hi : locals.idxOf? x with
  | some i =>
    rw [hi] at h
    cases h
    exact .inLocals i hi
  | none =>
    rw [hi] at h
    cases hl : E.lookup scope x with
    | nil =>
      rw [hl] at h
      cases hb : Builtin.ofName x with
      | none => rw [hb] at h; cases h
      | some b =>
        rw [hb] at h
        cases h
        exact .builtin b hi hl hb
    | cons d ds =>
      rw [hl] at h
      cases h
      rw [← hl]
      exact .decl hi (by rw [hl]; exact List.cons_ne_nil d ds)

theorem Resolves.resolve {E : Env} {locals : List String} {scope : Option String} {x : String}
    {r : Denot} (h : Resolves E locals scope x r) : E.resolve locals scope x = Option.some r := by
  cases h with
  | inLocals i hi => simp only [Env.resolve, hi]
  | decl h₁ h₂ =>
    unfold Env.resolve
    rw [h₁]
    cases hl : E.lookup scope x with
    | nil => exact absurd hl h₂
    | cons d ds => rfl
  | builtin b h₁ h₂ h₃ => simp only [Env.resolve, h₁, h₂, h₃, Option.map_some]

/-- **Resolution is decided by `Env.resolve`.** -/
theorem resolve_iff {E : Env} {locals : List String} {scope : Option String} {x : String}
    {r : Denot} : Resolves E locals scope x r ↔ E.resolve locals scope x = Option.some r :=
  ⟨Resolves.resolve, Env.resolve_sound⟩

/-- **Resolution is functional**: a name denotes at most one thing. -/
theorem Resolves.unique {E : Env} {locals : List String} {scope : Option String} {x : String}
    {r r' : Denot} (h : Resolves E locals scope x r) (h' : Resolves E locals scope x r') : r = r' := by
  have e := h.resolve
  rw [h'.resolve] at e
  exact (Option.some.inj e).symm

end Solidity.Source
