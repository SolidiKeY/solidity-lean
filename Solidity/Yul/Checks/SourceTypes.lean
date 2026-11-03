import Solidity.Yul.SourceTypes
namespace Solidity.Yul.Checks.SourceTypes
open Solidity.Source

def kind (ty : STy) : Option ExternalType := (checkDeclaredSourceType ⟨[]⟩ ty).map fun p => p.1

/-- Every legal integer/fixed width and bytes count, not only endpoints. -/
example : ∀ width : Fin 32, kind (.int ⟨false, 8*(width.val+1), by omega⟩) =
    some (.value (.unsigned width)) := by decide
example : ∀ width : Fin 32, kind (.int ⟨true, 8*(width.val+1), by omega⟩) =
    some (.value (.signed width)) := by decide
example : ∀ width : Fin 32, kind (.fixed ⟨false, 8*(width.val+1), 80, by omega⟩) =
    some (.value (.unsigned width)) := by decide
example : ∀ width : Fin 32, kind (.fixed ⟨true, 8*(width.val+1), 0, by omega⟩) =
    some (.value (.signed width)) := by decide
example : ∀ width : Fin 32, kind (.fixedBytes (width.val+1) (by omega)) =
    some (.value (.fixedBytes width)) := by decide

def name : DeclName := ⟨none, "T"⟩
def referenceCases : List (STy × ExternalType) :=
  [(.bytes .memory, .memory), (.string .memory, .memory),
   (.array .memory .bool none, .memory), (.struct .memory name, .memory),
   (.bytes .calldata, .calldataDynamic), (.string .calldata, .calldataDynamic),
   (.array .calldata .bool none, .calldataDynamic),
   (.array .calldata .bool (some 5), .calldataStatic),
   (.struct .calldata name, .calldataStatic),
   (.bytes .storage, .storage true false), (.string .storage, .storage true false),
   (.array .storage .bool none, .storage true false), (.struct .storage name, .storage true false),
   (.mapping (.int .u256) .bool, .storage true false),
   (.fn true [.bool] [.bool] none, .externalFunction),
   (.fn false [.bool] [.bool] none, .internalFunction),
   (.array .calldata (.array .calldata (.int .u256) none) (some 5), .calldataStatic),
   (.struct .calldata ⟨none, "D"⟩, .calldataStatic)]
example : referenceCases.length = 18 := rfl
example : referenceCases.all (fun p => kind p.1 == some p.2) = true := by decide
example : kind .bool = some (.value .boolean) := by decide
example : kind (.address false) = some (.value .address) := by decide
example : kind (.address true) = some (.value .address) := by decide
example : kind (.contract name) = some (.value .address) := by decide
example : kind (.rational (.ofInt 1)) = none := by decide
example : kind (.hexConst (.ofInt 1) 1) = none := by decide
example : kind (.stringLit [65]) = none := by decide
example : kind (.tuple [.bool, .bool]) = none := by decide
example : kind (.enum name) = none := by decide
example : kind (.udvt name) = none := by decide

def enumDecl (n : Nat) : Decl :=
  ⟨.enum, "T", none, true, .enum "T" "e0" ((List.range n).map fun i => "e" ++ toString (i+1))⟩
def udvtDecl (elem : Elem) : Decl := ⟨.udvt, "T", none, true, .udvt "T" elem⟩
def namedKind (decls : List Decl) (ty : STy) : Option ExternalType :=
  (checkDeclaredSourceType ⟨decls⟩ ty).map fun p => p.1

theorem enumNode (n : Nat) : EnumNodeD (enumDecl n).node (n+1) := by
  have d := EnumNodeD.intro (top := true) (name := "T") (first := "e0")
    (rest := (List.range n).map fun i => "e" ++ toString (i+1))
  simpa only [enumDecl, List.length_map, List.length_range] using d

theorem enumAccepted (n : Nat) (range : n+1 ≤ 256) :
    namedKind [enumDecl n] (.enum name) = some (.value (.unsigned 0)) := by
  have d : DeclaredSourceTypeD ⟨[enumDecl n]⟩ (.enum name) (.value (.unsigned 0)) :=
    .enum rfl (enumNode n) range
  unfold namedKind
  rw [d.complete]
  rfl

theorem enumRefused (env : Env) (n : Nat)
    (lookup : env.declOf .enum name = some (enumDecl n)) (large : 256 < n+1) :
    namedKind env.decls (.enum name) = none := by
  change (checkDeclaredSourceType env (.enum name)).map _ = none
  rw [checkDeclaredSourceType_enum_large env name (enumDecl n) (n+1) lookup (enumNode n) large]
  rfl

example : namedKind [enumDecl 0] (.enum name) = some (.value (.unsigned 0)) := by decide
example : namedKind [enumDecl 255] (.enum name) = some (.value (.unsigned 0)) := enumAccepted 255 (by decide)
example : namedKind [enumDecl 256] (.enum name) = none := enumRefused ⟨[enumDecl 256]⟩ 256 rfl (by decide)
example : namedKind [udvtDecl .bool] (.udvt name) = some (.value .boolean) := by decide
example : namedKind [udvtDecl (.int true 128 (by decide))] (.udvt name) =
    some (.value (.signed 15)) := by decide
example : namedKind [udvtDecl (.fixedBytes 32 (by decide))] (.udvt name) =
    some (.value (.fixedBytes 31)) := by decide
example : namedKind [udvtDecl .bytes] (.udvt name) = none := by decide
example : namedKind [udvtDecl .string] (.udvt name) = none := by decide

/-- Found malformed/wrong declaration nodes do not expose a later valid one. -/
def wrongNode : Decl := ⟨.udvt, "T", none, true, .enum "T" "A" []⟩
example : namedKind [wrongNode, udvtDecl .bool] (.udvt name) = none := by decide
example : namedKind [udvtDecl .bool, wrongNode] (.udvt name) = some (.value .boolean) := by decide
example : namedKind [enumDecl 256, enumDecl 0] (.enum name) = none := enumRefused ⟨[enumDecl 256, enumDecl 0]⟩ 256 rfl (by decide)
example : namedKind [enumDecl 0, enumDecl 256] (.enum name) = some (.value (.unsigned 0)) := by decide
example : namedKind [udvtDecl .bool] (.enum name) = none := by decide
example : namedKind [enumDecl 0] (.udvt name) = none := by decide

def ctx : Ctx :=
  {env := ⟨[udvtDecl .bool, enumDecl 2]⟩, scope := none,
   locals := [("blocked", .tuple [.bool]), ("blocked", .int .u256),
     ("small", .int .u8), ("flag", .udvt name), ("choice", .enum name),
     ("data", .array .calldata (.int .u256) none)]}
def localKind (x : String) : Option ExternalType :=
  (checkClassifiedSourceLocal ctx x).map fun d => d.kind
example : localKind "blocked" = none := by decide
example : localKind "small" = some (.value (.unsigned 0)) := by decide
example : localKind "flag" = some (.value .boolean) := by decide
example : localKind "choice" = some (.value (.unsigned 0)) := by decide
example : localKind "data" = some .calldataDynamic := by decide
example : localKind "T" = none := by decide
example : localKind "missing" = none := by decide

def actual := (checkClassifiedSourceLocal ctx "small").get (by decide)
example : actual.ref.index.toNat = 2 := by decide
example : actual.identity.typed.toR = .local actual.ref.index := actual.identity.typed_toR
example : checkClassifiedSourceLocal ctx "small" = some actual := actual.complete


/-- A distinct-name source context inhabits actual declaration-backed inputs.
The duplicate-name context above is a refusal/priority control. -/
def validCtx : Ctx :=
  {env := ⟨[⟨.udvt, "U", none, true, .udvt "U" .bool⟩,
             ⟨.enum, "E", none, true, .enum "E" "A" ["B"]⟩]⟩,
   scope := none, locals := [("flag", .udvt ⟨none, "U"⟩),
     ("choice", .enum ⟨none, "E"⟩), ("small", .int .u8)]}
example : (checkClassifiedSourceLocal validCtx "flag").map (fun d => d.kind) =
    some (.value .boolean) := by decide
example : (checkClassifiedSourceLocal validCtx "choice").map (fun d => d.kind) =
    some (.value (.unsigned 0)) := by decide
example : (checkClassifiedSourceLocal validCtx "small").map (fun d => d.ref.index.toNat) =
    some 2 := by decide

end Solidity.Yul.Checks.SourceTypes
