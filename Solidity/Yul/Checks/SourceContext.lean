import Solidity.Yul.SourceContext
namespace Solidity.Yul.Checks.SourceContext
open Solidity.Source

def libraryDecl : Decl := ⟨.library, "blocked", none, true, .library "blocked" .nil⟩
def ctx : Ctx :=
  {env := ⟨[libraryDecl]⟩, scope := none,
   locals := [("blocked",.tuple [.bool]),("blocked",.int .u8),
     ("small",.int .u8),("flag",.bool),("other",.int .u8),
     ("mem",.bytes .memory),("data",.array .calldata .bool none),
     ("fixedData",.array .calldata .bool (some 5)),
     ("ptr",.array .storage .bool none),
     ("externalFn",.fn true [] [] none),("internalFn",.fn false [] [] none),
     ("keccak256",.bool)]}

def positions := (localExternalMap ctx).map fun mapped =>
  (mapped.source.position,mapped.index.position)
example : positions = [(1,0),(2,1),(3,2),(4,3),(5,4),(6,5),(7,6),
    (8,7),(9,8),(10,9),(11,10)] := by decide
example : (localScalarBindings ctx).map (fun b => (b.source.position,b.ref.position)) =
    [(1,0),(2,1),(3,2),(4,3),(11,10)] := by decide
example : (sourceLocalEntries ctx).length = 11 := by decide
example : (allSourceRefs ctx).length = 12 := by decide
example : globals (localExternalTypes ctx) = [] := localExternalTypes_globals ctx

def selected (name : String) : Option (Nat × Nat) :=
  (checkLocalMapped ctx name).map fun ⟨mapped,_⟩ =>
    (mapped.source.position,mapped.index.position)
example : selected "blocked" = none := by decide
example : selected "small" = some (2,1) := by decide
example : selected "flag" = some (3,2) := by decide
example : selected "other" = some (4,3) := by decide
example : selected "keccak256" = some (11,10) := by decide
example : selected "missing" = none := by decide
example : ctx.resolve "blocked" = some (.loc 0) := rfl
example : ({ctx with locals := []} : Ctx).resolve "blocked" =
    some (.decls [libraryDecl]) := rfl
example : (checkLocalMapped {ctx with locals := []} "blocked").isSome = false := by decide
example : (checkLocalMapped {ctx with locals := ctx.locals.tail} "blocked").isSome = true := by decide

def capable (name : String) (suffix : List String) (write : Bool) : Bool :=
  (checkLocalExternal ctx name suffix write).isSome
example : capable "small" [] false = true := by decide
example : capable "small" [] true = true := by decide
example : capable "small" ["slot"] false = false := by decide
example : capable "blocked" [] false = false := by decide
example : capable "flag" [] true = true := by decide
example : capable "mem" [] false = true := by decide
example : capable "mem" [] true = true := by decide
example : capable "mem" ["length"] false = false := by decide
example : capable "data" [] false = false := by decide
example : capable "data" ["offset"] false = true := by decide
example : capable "data" ["offset"] true = true := by decide
example : capable "data" ["length"] false = true := by decide
example : capable "data" ["length"] true = true := by decide
example : capable "fixedData" ["offset"] false = false := by decide
example : capable "fixedData" [] false = true := by decide
example : capable "fixedData" [] true = true := by decide
example : capable "fixedData" ["length"] false = false := by decide
example : capable "ptr" ["slot"] false = true := by decide
example : capable "ptr" ["slot"] true = true := by decide
example : capable "ptr" ["offset"] false = true := by decide
example : capable "ptr" ["offset"] true = false := by decide
example : capable "ptr" [] false = false := by decide
example : capable "externalFn" ["address"] false = true := by decide
example : capable "externalFn" ["selector"] false = true := by decide
example : capable "externalFn" ["selector"] true = true := by decide
example : capable "externalFn" [] false = false := by decide
/-- Static typing is distinct from admission, which refuses compiler-dependent function words. -/
example : capable "internalFn" [] false = true := by decide
example : admitExternal .A .internalFunction =
    .error (.compilerDependent "internal function address") := rfl
example : capable "small" ["unknown"] false = false := by decide
example : capable "data" ["offset","length"] false = false := by decide
example : capable "missing" [] false = false := by decide

def small := (checkLocalMapped ctx "small").get (by decide)
example : LocalMappedD ctx "small" small.1 := small.2
example : ClassifiedSourceLocal ctx "small" := small.2.classified
def ptr := (checkLocalExternal ctx "ptr" ["slot"] true).get (by decide)
example : LocalExternalD ctx "ptr" ["slot"] true ptr.1 := ptr.2
example : checkLocalExternal ctx "ptr" ["slot"] true = some ptr := ptr.2.complete
example : ScalarBindingsCoherent (localScalarBindings ctx) := localScalarBindings_coherent ctx
example : ((localExternalMap ctx).map fun mapped => mapped.source.position).Nodup := by
  decide

-- A real generated target, with a concrete raw-view agreement witness.
def zeroYul : ScalarView (localExternalTypes ctx) := fun _ => word 0
def zeroSource : SourceScalarView ctx := fun _ => word 0
theorem zeroAgree : ScalarViewsAgree (localScalarBindings ctx) zeroYul zeroSource := by
  intro binding present
  rfl
def targetSmall : ScalarBinding (localExternalTypes ctx) ctx :=
  (localScalarBindings ctx)[1]'(by decide)
theorem targetPresent : targetSmall ∈ localScalarBindings ctx :=
  List.getElem_mem _
example : targetSmall.source.position = 2 := by decide
example : targetSmall.ref.position = 1 := by decide
example : ScalarViewsAgree (localScalarBindings ctx)
    (zeroYul.write targetSmall.ref (word 257))
    (zeroSource.write targetSmall.source (word 257)) :=
  localScalarBindings_write ctx zeroYul zeroSource zeroAgree targetSmall targetPresent (word 257)
example : ((zeroSource.write targetSmall.source (word 257)) targetSmall.source).val = 257 := by decide
example : ((zeroYul.write targetSmall.ref (word 257)) targetSmall.ref).val = 257 := by decide

def empty : Ctx := {env := ⟨[]⟩,scope := none,locals := []}
def unsupported : Ctx :=
  {empty with locals := [("only",.tuple [.bool]),("also",.rational (.ofInt 1))]}
example : localExternalTypes empty = [] := by decide
example : (localExternalMap empty).length = 0 := by decide
example : (localScalarBindings empty).length = 0 := by decide
example : (checkLocalMapped empty "missing").isSome = false := by decide
example : localExternalTypes unsupported = [] := by decide
example : (localExternalMap unsupported).length = 0 := by decide
example : (localScalarBindings unsupported).length = 0 := by decide
example : (checkLocalMapped unsupported "only").isSome = false := by decide
example : (checkLocalExternal unsupported "only" [] false).isSome = false := by decide

end Solidity.Yul.Checks.SourceContext
