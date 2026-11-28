import Solidity.Source.Decls


namespace Solidity.Source

def Decl.isPrivate (d : Decl) : Bool :=
  match d.kind, d.top, d.node with
  | .stateVar, _, .stateVar _ (some .priv) _ _ _ _ _ => true
  | .function, _, .function _ _ (some .priv) _ _ _ _ _ _ => true
  | _, _, _ => false

structure Env where
  decls : List Decl

def Syn.env (u : Syn .unit) : Env := ⟨u.decls⟩

namespace Env

def bases (E : Env) (c : String) : List String :=
  match E.decls.find? (fun d => d.scope == Option.none && d.name == c &&
      (d.kind == .contract || d.kind == .interface)) with
  | Option.some ⟨.contract, _, _, _, .contract _ _ _ is _⟩ => names is
  | Option.some ⟨.interface, _, _, _, .interface _ is _⟩ => names is
  | _ => []
where
  names {c : Cat} (is : Syn c) : List String := (inheritPaths is).map fun p => p.tail.getLast?.getD p.head

def merge : Nat → List (List String) → Option (List String)
  | 0, _ => Option.none
  | fuel + 1, ls =>
    let ls := ls.filter (· ≠ [])
    if ls.isEmpty then Option.some []
    else
      match ls.findSome? fun l => l.head?.filter fun h => ls.all fun l' => !(l'.drop 1).contains h with
      | Option.none => Option.none
      | Option.some h => (merge fuel (ls.map fun l => l.filter (· ≠ h))).map (h :: ·)

def linearizeF (E : Env) : Nat → String → Option (List String)
  | 0, _ => Option.none
  | fuel + 1, c =>
    let bs := (E.bases c).reverse
    match bs.mapM (E.linearizeF fuel) with
    | Option.none => Option.none
    | Option.some ls => (merge (E.decls.length * E.decls.length + 2) (ls ++ [bs])).map (c :: ·)

def linearize (E : Env) (c : String) : Option (List String) := E.linearizeF (E.decls.length + 1) c

def declared (E : Env) (s : Option String) (x : String) : List Decl :=
  E.decls.filter fun d => d.scope == s && d.name == x && x != ""

def visible (E : Env) (scope s : Option String) (x : String) : List Decl :=
  (E.declared s x).filter fun d => s == scope || !d.isPrivate

def lookup (E : Env) (scope : Option String) (x : String) : List Decl :=
  let chain : List (Option String) :=
    match scope with
    | Option.none => []
    | Option.some c => ((E.linearize c).getD [c]).map Option.some
  match chain.find? (fun s => !(E.visible scope s x).isEmpty) with
  | Option.some s => E.visible scope s x
  | Option.none => E.declared Option.none x

def basesOK (E : Env) : Bool :=
  (E.decls.zipIdx).all fun (d, i) =>
    !(d.kind == .contract || d.kind == .interface) ||
      (E.bases d.name).all fun b =>
        ((E.decls.zipIdx).take i).any fun (d', _) =>
          d'.scope == Option.none && d'.name == b &&
            (d'.kind == .interface || (d.kind == .contract && d'.kind == .contract))

end Env


inductive Status where
  | admitted (feature : String)
  | excluded (feature : String)
  | removed (feature : String)
  deriving DecidableEq, Repr

inductive Builtin where
  | msg | block | tx | abi | this | super
  | keccak256 | sha256 | ripemd160 | ecrecover | addmod | mulmod
  | assert | require | revert | gasleft | blockhash | blobhash | selfdestruct | erc7201
  | now | suicide | sha3
  deriving DecidableEq, Repr

def Builtin.name : Builtin → String
  | .msg => "msg" | .block => "block" | .tx => "tx" | .abi => "abi" | .this => "this"
  | .super => "super" | .keccak256 => "keccak256" | .sha256 => "sha256"
  | .ripemd160 => "ripemd160" | .ecrecover => "ecrecover" | .addmod => "addmod"
  | .mulmod => "mulmod" | .assert => "assert" | .require => "require" | .revert => "revert"
  | .gasleft => "gasleft" | .blockhash => "blockhash" | .blobhash => "blobhash"
  | .selfdestruct => "selfdestruct" | .erc7201 => "erc7201" | .now => "now"
  | .suicide => "suicide" | .sha3 => "sha3"

def Builtin.all : List Builtin :=
  [.msg, .block, .tx, .abi, .this, .super, .keccak256, .sha256, .ripemd160, .ecrecover, .addmod,
    .mulmod, .assert, .require, .revert, .gasleft, .blockhash, .blobhash, .selfdestruct,
    .erc7201, .now, .suicide, .sha3]

def Builtin.ofName (x : String) : Option Builtin := Builtin.all.find? (·.name == x)

example (b : Builtin) : Builtin.ofName b.name = some b := by
  cases b <;> rfl

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

def callOptionStatus : String → Option Status
  | "value" => Option.some (.admitted "valueOption")
  | "gas" => Option.some (.excluded "gasOption")
  | "salt" => Option.some (.excluded "create2Salt")
  | _ => Option.none


inductive Denot where
  | loc (i : Nat)
  | decls (ds : List Decl)
  | builtin (b : Builtin)

inductive Resolves (E : Env) (locals : List String) (scope : Option String) (x : String) :
    Denot → Prop where
  | inLocals (i : Nat) (h : locals.idxOf? x = Option.some i) : Resolves E locals scope x (.loc i)
  | decl (h₁ : locals.idxOf? x = Option.none) (h₂ : E.lookup scope x ≠ []) :
      Resolves E locals scope x (.decls (E.lookup scope x))
  | builtin (b : Builtin) (h₁ : locals.idxOf? x = Option.none) (h₂ : E.lookup scope x = [])
      (h₃ : Builtin.ofName x = Option.some b) : Resolves E locals scope x (.builtin b)

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

theorem resolve_iff {E : Env} {locals : List String} {scope : Option String} {x : String}
    {r : Denot} : Resolves E locals scope x r ↔ E.resolve locals scope x = Option.some r :=
  ⟨Resolves.resolve, Env.resolve_sound⟩

theorem Resolves.unique {E : Env} {locals : List String} {scope : Option String} {x : String}
    {r r' : Denot} (h : Resolves E locals scope x r) (h' : Resolves E locals scope x r') : r = r' := by
  have e := h.resolve
  rw [h'.resolve] at e
  exact (Option.some.inj e).symm

end Solidity.Source
