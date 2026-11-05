import Solidity.Frontend.QualifiedUnits.References

/-! One typed specimen and literal expected traversal per existing constructor. -/
namespace Solidity.Frontend.QualifiedUnits.ConstructorFixtures
open Solidity.Source

def marker : IdPath := ⟨"N", ["M", "T"]⟩

def specimen_nil : Syn (.list .expr) := .nil

theorem fixture_nil : specimen_nil.ctor = .nil ∧ references specimen_nil = [] := by
  exact ⟨rfl, rfl⟩

def specimen_cons : Syn (.list .expr) := .cons (.ident "leaf") (.cons (.ident "leaf") .nil)

theorem fixture_cons : specimen_cons.ctor = .cons ∧ references specimen_cons = [⟨"leaf", []⟩, ⟨"leaf", []⟩] := by
  exact ⟨rfl, rfl⟩

def specimen_none : Syn (.opt .expr) := .none

theorem fixture_none : specimen_none.ctor = .none ∧ references specimen_none = [] := by
  exact ⟨rfl, rfl⟩

def specimen_some : Syn (.opt .expr) := .some (.ident "leaf")

theorem fixture_some : specimen_some.ctor = .some ∧ references specimen_some = [⟨"leaf", []⟩] := by
  exact ⟨rfl, rfl⟩

def specimen_unit : Syn .unit := .unit (.cons (.topPart (.constant (.userType marker) "v" (.lit (.bool true)))) .nil)

theorem fixture_unit : specimen_unit.ctor = .unit ∧ references specimen_unit = [marker] := by
  exact ⟨rfl, rfl⟩

def specimen_pragma : Syn .top := .pragma []

theorem fixture_pragma : specimen_pragma.ctor = .pragma ∧ references specimen_pragma = [] := by
  exact ⟨rfl, rfl⟩

def specimen_importPath : Syn .top := .importPath "token" none

theorem fixture_importPath : specimen_importPath.ctor = .importPath ∧ references specimen_importPath = [] := by
  exact ⟨rfl, rfl⟩

def specimen_importSymbols : Syn .top := .importSymbols (.importAlias "a" (some "b")) (.cons (.importAlias "a" (some "b")) .nil) "token"

theorem fixture_importSymbols : specimen_importSymbols.ctor = .importSymbols ∧ references specimen_importSymbols = [] := by
  exact ⟨rfl, rfl⟩

def specimen_importStar : Syn .top := .importStar "token" "token"

theorem fixture_importStar : specimen_importStar.ctor = .importStar ∧ references specimen_importStar = [] := by
  exact ⟨rfl, rfl⟩

def specimen_importAlias : Syn .importAlias := .importAlias "token" none

theorem fixture_importAlias : specimen_importAlias.ctor = .importAlias ∧ references specimen_importAlias = [] := by
  exact ⟨rfl, rfl⟩

def specimen_contract : Syn .top := .contract false "token" (.some (.ident "leaf")) (.cons (.inherit marker .none) .nil) (.cons (.struct "S" (.structMember (.userType marker) "v") .nil) .nil)

theorem fixture_contract : specimen_contract.ctor = .contract ∧ references specimen_contract = [⟨"leaf", []⟩, marker, marker] := by
  exact ⟨rfl, rfl⟩

def specimen_interface : Syn .top := .interface "token" (.cons (.inherit marker .none) .nil) (.cons (.struct "S" (.structMember (.userType marker) "v") .nil) .nil)

theorem fixture_interface : specimen_interface.ctor = .interface ∧ references specimen_interface = [marker, marker] := by
  exact ⟨rfl, rfl⟩

def specimen_library : Syn .top := .library "token" (.cons (.struct "S" (.structMember (.userType marker) "v") .nil) .nil)

theorem fixture_library : specimen_library.ctor = .library ∧ references specimen_library = [marker] := by
  exact ⟨rfl, rfl⟩

def specimen_topPart : Syn .top := .topPart (.struct "S" (.structMember (.userType marker) "v") .nil)

theorem fixture_topPart : specimen_topPart.ctor = .topPart ∧ references specimen_topPart = [marker] := by
  exact ⟨rfl, rfl⟩

def specimen_inherit : Syn .inherit := .inherit marker (.some (.positional (.cons (.ident "leaf") .nil)))

theorem fixture_inherit : specimen_inherit.ctor = .inherit ∧ references specimen_inherit = [marker, ⟨"leaf", []⟩] := by
  exact ⟨rfl, rfl⟩

def specimen_constructor : Syn (.part false) := .constructor (.cons (.param (.userType marker) none none) .nil) (.cons (.modInv marker .none) .nil) false none (.block (.cons (.stmtItem (.simpleStmt (.exprStmt (.ident "leaf")))) .nil))

theorem fixture_constructor : specimen_constructor.ctor = .constructor ∧ references specimen_constructor = [marker, marker, ⟨"leaf", []⟩] := by
  exact ⟨rfl, rfl⟩

def specimen_function : Syn (.part false) := .function (.ident "f") (.cons (.param (.userType marker) none none) .nil) none none (.cons (.modInv marker .none) .nil) false (some [marker]) (.cons (.param (.userType marker) none none) .nil) (.some (.block (.cons (.stmtItem (.simpleStmt (.exprStmt (.ident "leaf")))) .nil)))

theorem fixture_function : specimen_function.ctor = .function ∧ references specimen_function = [marker, marker, marker, marker, ⟨"leaf", []⟩] := by
  exact ⟨rfl, rfl⟩

def specimen_modifier : Syn (.part false) := .modifier "token" (.some (.cons (.param (.userType marker) none none) .nil)) false (some [marker]) (.some (.block (.cons (.stmtItem (.simpleStmt (.exprStmt (.ident "leaf")))) .nil)))

theorem fixture_modifier : specimen_modifier.ctor = .modifier ∧ references specimen_modifier = [marker, marker, ⟨"leaf", []⟩] := by
  exact ⟨rfl, rfl⟩

def specimen_fallback : Syn (.part false) := .fallback (.fbParams (.param (.userType marker) none none) .nil .nil) false none (.cons (.modInv marker .none) .nil) false (some [marker]) (.some (.block (.cons (.stmtItem (.simpleStmt (.exprStmt (.ident "leaf")))) .nil)))

theorem fixture_fallback : specimen_fallback.ctor = .fallback ∧ references specimen_fallback = [marker, marker, marker, ⟨"leaf", []⟩] := by
  exact ⟨rfl, rfl⟩

def specimen_fbNoParams : Syn .fallbackSig := .fbNoParams

theorem fixture_fbNoParams : specimen_fbNoParams.ctor = .fbNoParams ∧ references specimen_fbNoParams = [] := by
  exact ⟨rfl, rfl⟩

def specimen_fbParams : Syn .fallbackSig := .fbParams (.param (.userType marker) none none) (.cons (.param (.userType marker) none none) .nil) (.cons (.param (.userType marker) none none) .nil)

theorem fixture_fbParams : specimen_fbParams.ctor = .fbParams ∧ references specimen_fbParams = [marker, marker, marker] := by
  exact ⟨rfl, rfl⟩

def specimen_receive : Syn (.part false) := .receive false false (.cons (.modInv marker .none) .nil) false (some [marker]) (.some (.block (.cons (.stmtItem (.simpleStmt (.exprStmt (.ident "leaf")))) .nil)))

theorem fixture_receive : specimen_receive.ctor = .receive ∧ references specimen_receive = [marker, marker, ⟨"leaf", []⟩] := by
  exact ⟨rfl, rfl⟩

def specimen_struct : Syn (.part false) := .struct "token" (.structMember (.userType marker) "v") (.cons (.structMember (.userType marker) "v") .nil)

theorem fixture_struct : specimen_struct.ctor = .struct ∧ references specimen_struct = [marker, marker] := by
  exact ⟨rfl, rfl⟩

def specimen_structMember : Syn .structMember := .structMember (.userType marker) "token"

theorem fixture_structMember : specimen_structMember.ctor = .structMember ∧ references specimen_structMember = [marker] := by
  exact ⟨rfl, rfl⟩

def specimen_enum : Syn (.part false) := .enum "token" "token" []

theorem fixture_enum : specimen_enum.ctor = .enum ∧ references specimen_enum = [] := by
  exact ⟨rfl, rfl⟩

def specimen_udvt : Syn (.part false) := .udvt "token" .bool

theorem fixture_udvt : specimen_udvt.ctor = .udvt ∧ references specimen_udvt = [] := by
  exact ⟨rfl, rfl⟩

def specimen_stateVar : Syn (.part false) := .stateVar (.userType marker) none none (some [marker]) false "token" (.some (.ident "leaf"))

theorem fixture_stateVar : specimen_stateVar.ctor = .stateVar ∧ references specimen_stateVar = [marker, marker, ⟨"leaf", []⟩] := by
  exact ⟨rfl, rfl⟩

def specimen_constant : Syn (.part true) := .constant (.userType marker) "token" (.ident "leaf")

theorem fixture_constant : specimen_constant.ctor = .constant ∧ references specimen_constant = [marker, ⟨"leaf", []⟩] := by
  exact ⟨rfl, rfl⟩

def specimen_event : Syn (.part false) := .event "token" (.cons (.eventParam (.userType marker) false none) .nil) false

theorem fixture_event : specimen_event.ctor = .event ∧ references specimen_event = [marker] := by
  exact ⟨rfl, rfl⟩

def specimen_eventParam : Syn .eventParam := .eventParam (.userType marker) false none

theorem fixture_eventParam : specimen_eventParam.ctor = .eventParam ∧ references specimen_eventParam = [marker] := by
  exact ⟨rfl, rfl⟩

def specimen_error : Syn (.part false) := .error "token" (.cons (.errorParam (.userType marker) none) .nil)

theorem fixture_error : specimen_error.ctor = .error ∧ references specimen_error = [marker] := by
  exact ⟨rfl, rfl⟩

def specimen_errorParam : Syn .errorParam := .errorParam (.userType marker) none

theorem fixture_errorParam : specimen_errorParam.ctor = .errorParam ∧ references specimen_errorParam = [marker] := by
  exact ⟨rfl, rfl⟩

def specimen_usingPart : Syn (.part false) := .usingPart (.usingPath marker .none false)

theorem fixture_usingPart : specimen_usingPart.ctor = .usingPart ∧ references specimen_usingPart = [marker] := by
  exact ⟨rfl, rfl⟩

def specimen_usingPath : Syn .using := .usingPath marker (.some (.userType marker)) false

theorem fixture_usingPath : specimen_usingPath.ctor = .usingPath ∧ references specimen_usingPath = [marker, marker] := by
  exact ⟨rfl, rfl⟩

def specimen_usingAliases : Syn .using := .usingAliases (.usingAlias marker none) (.cons (.usingAlias marker none) .nil) (.some (.userType marker)) false

theorem fixture_usingAliases : specimen_usingAliases.ctor = .usingAliases ∧ references specimen_usingAliases = [marker, marker, marker] := by
  exact ⟨rfl, rfl⟩

def specimen_usingAlias : Syn .usingAlias := .usingAlias marker none

theorem fixture_usingAlias : specimen_usingAlias.ctor = .usingAlias ∧ references specimen_usingAlias = [marker] := by
  exact ⟨rfl, rfl⟩

def specimen_positional : Syn .callArgs := .positional (.cons (.ident "leaf") .nil)

theorem fixture_positional : specimen_positional.ctor = .positional ∧ references specimen_positional = [⟨"leaf", []⟩] := by
  exact ⟨rfl, rfl⟩

def specimen_named : Syn .callArgs := .named (.cons (.namedArg "v" (.ident "leaf")) .nil)

theorem fixture_named : specimen_named.ctor = .named ∧ references specimen_named = [⟨"leaf", []⟩] := by
  exact ⟨rfl, rfl⟩

def specimen_namedArg : Syn .namedArg := .namedArg "token" (.ident "leaf")

theorem fixture_namedArg : specimen_namedArg.ctor = .namedArg ∧ references specimen_namedArg = [⟨"leaf", []⟩] := by
  exact ⟨rfl, rfl⟩

def specimen_modInv : Syn .modInv := .modInv marker (.some (.positional (.cons (.ident "leaf") .nil)))

theorem fixture_modInv : specimen_modInv.ctor = .modInv ∧ references specimen_modInv = [marker, ⟨"leaf", []⟩] := by
  exact ⟨rfl, rfl⟩

def specimen_param : Syn .param := .param (.userType marker) none none

theorem fixture_param : specimen_param.ctor = .param ∧ references specimen_param = [marker] := by
  exact ⟨rfl, rfl⟩

def specimen_elem : Syn .typeName := .elem .bool

theorem fixture_elem : specimen_elem.ctor = .elem ∧ references specimen_elem = [] := by
  exact ⟨rfl, rfl⟩

def specimen_fnType : Syn .typeName := .fnType (.cons (.param (.userType marker) none none) .nil) none none (.cons (.param (.userType marker) none none) .nil)

theorem fixture_fnType : specimen_fnType.ctor = .fnType ∧ references specimen_fnType = [marker, marker] := by
  exact ⟨rfl, rfl⟩

def specimen_mapping : Syn .typeName := .mapping (.path marker) none (.userType marker) none

theorem fixture_mapping : specimen_mapping.ctor = .mapping ∧ references specimen_mapping = [marker, marker] := by
  exact ⟨rfl, rfl⟩

def specimen_userType : Syn .typeName := .userType marker

theorem fixture_userType : specimen_userType.ctor = .userType ∧ references specimen_userType = [marker] := by
  exact ⟨rfl, rfl⟩

def specimen_array : Syn .typeName := .array (.userType marker) (.some (.ident "leaf"))

theorem fixture_array : specimen_array.ctor = .array ∧ references specimen_array = [marker, ⟨"leaf", []⟩] := by
  exact ⟨rfl, rfl⟩

def specimen_varDecl : Syn .varDecl := .varDecl (.userType marker) none "token"

theorem fixture_varDecl : specimen_varDecl.ctor = .varDecl ∧ references specimen_varDecl = [marker] := by
  exact ⟨rfl, rfl⟩

def specimen_index : Syn .expr := .index (.ident "leaf") (.some (.ident "leaf"))

theorem fixture_index : specimen_index.ctor = .index ∧ references specimen_index = [⟨"leaf", []⟩, ⟨"leaf", []⟩] := by
  exact ⟨rfl, rfl⟩

def specimen_slice : Syn .expr := .slice (.ident "leaf") (.some (.ident "leaf")) (.some (.ident "leaf"))

theorem fixture_slice : specimen_slice.ctor = .slice ∧ references specimen_slice = [⟨"leaf", []⟩, ⟨"leaf", []⟩, ⟨"leaf", []⟩] := by
  exact ⟨rfl, rfl⟩

def specimen_member : Syn .expr := .member (.ident "leaf") "token"

theorem fixture_member : specimen_member.ctor = .member ∧ references specimen_member = [⟨"leaf", ["token"]⟩, ⟨"leaf", []⟩] := by
  constructor
  · rfl
  · simp only [specimen_member, references, expressionPath, expressionPathAny, Option.map, Option.toList, List.nil_append, List.cons_append]

def specimen_callOptions : Syn .expr := .callOptions (.ident "leaf") (.namedArg "v" (.ident "leaf")) (.cons (.namedArg "v" (.ident "leaf")) .nil)

theorem fixture_callOptions : specimen_callOptions.ctor = .callOptions ∧ references specimen_callOptions = [⟨"leaf", []⟩, ⟨"leaf", []⟩, ⟨"leaf", []⟩] := by
  exact ⟨rfl, rfl⟩

def specimen_call : Syn .expr := .call (.ident "leaf") (.positional (.cons (.ident "leaf") .nil))

theorem fixture_call : specimen_call.ctor = .call ∧ references specimen_call = [⟨"leaf", []⟩, ⟨"leaf", []⟩] := by
  exact ⟨rfl, rfl⟩

def specimen_payableConv : Syn .expr := .payableConv (.positional (.cons (.ident "leaf") .nil))

theorem fixture_payableConv : specimen_payableConv.ctor = .payableConv ∧ references specimen_payableConv = [⟨"leaf", []⟩] := by
  exact ⟨rfl, rfl⟩

def specimen_metaType : Syn .expr := .metaType (.userType marker)

theorem fixture_metaType : specimen_metaType.ctor = .metaType ∧ references specimen_metaType = [marker] := by
  exact ⟨rfl, rfl⟩

def specimen_unaryPrefix : Syn .expr := .unaryPrefix .not (.ident "leaf")

theorem fixture_unaryPrefix : specimen_unaryPrefix.ctor = .unaryPrefix ∧ references specimen_unaryPrefix = [⟨"leaf", []⟩] := by
  exact ⟨rfl, rfl⟩

def specimen_unarySuffix : Syn .expr := .unarySuffix .inc (.ident "leaf")

theorem fixture_unarySuffix : specimen_unarySuffix.ctor = .unarySuffix ∧ references specimen_unarySuffix = [⟨"leaf", []⟩] := by
  exact ⟨rfl, rfl⟩

def specimen_exp : Syn .expr := .exp (.ident "leaf") (.ident "leaf")

theorem fixture_exp : specimen_exp.ctor = .exp ∧ references specimen_exp = [⟨"leaf", []⟩, ⟨"leaf", []⟩] := by
  exact ⟨rfl, rfl⟩

def specimen_mulDivMod : Syn .expr := .mulDivMod .mul (.ident "leaf") (.ident "leaf")

theorem fixture_mulDivMod : specimen_mulDivMod.ctor = .mulDivMod ∧ references specimen_mulDivMod = [⟨"leaf", []⟩, ⟨"leaf", []⟩] := by
  exact ⟨rfl, rfl⟩

def specimen_addSub : Syn .expr := .addSub .add (.ident "leaf") (.ident "leaf")

theorem fixture_addSub : specimen_addSub.ctor = .addSub ∧ references specimen_addSub = [⟨"leaf", []⟩, ⟨"leaf", []⟩] := by
  exact ⟨rfl, rfl⟩

def specimen_shift : Syn .expr := .shift .shl (.ident "leaf") (.ident "leaf")

theorem fixture_shift : specimen_shift.ctor = .shift ∧ references specimen_shift = [⟨"leaf", []⟩, ⟨"leaf", []⟩] := by
  exact ⟨rfl, rfl⟩

def specimen_bitAnd : Syn .expr := .bitAnd (.ident "leaf") (.ident "leaf")

theorem fixture_bitAnd : specimen_bitAnd.ctor = .bitAnd ∧ references specimen_bitAnd = [⟨"leaf", []⟩, ⟨"leaf", []⟩] := by
  exact ⟨rfl, rfl⟩

def specimen_bitXor : Syn .expr := .bitXor (.ident "leaf") (.ident "leaf")

theorem fixture_bitXor : specimen_bitXor.ctor = .bitXor ∧ references specimen_bitXor = [⟨"leaf", []⟩, ⟨"leaf", []⟩] := by
  exact ⟨rfl, rfl⟩

def specimen_bitOr : Syn .expr := .bitOr (.ident "leaf") (.ident "leaf")

theorem fixture_bitOr : specimen_bitOr.ctor = .bitOr ∧ references specimen_bitOr = [⟨"leaf", []⟩, ⟨"leaf", []⟩] := by
  exact ⟨rfl, rfl⟩

def specimen_order : Syn .expr := .order .lt (.ident "leaf") (.ident "leaf")

theorem fixture_order : specimen_order.ctor = .order ∧ references specimen_order = [⟨"leaf", []⟩, ⟨"leaf", []⟩] := by
  exact ⟨rfl, rfl⟩

def specimen_equality : Syn .expr := .equality .eq (.ident "leaf") (.ident "leaf")

theorem fixture_equality : specimen_equality.ctor = .equality ∧ references specimen_equality = [⟨"leaf", []⟩, ⟨"leaf", []⟩] := by
  exact ⟨rfl, rfl⟩

def specimen_and : Syn .expr := .and (.ident "leaf") (.ident "leaf")

theorem fixture_and : specimen_and.ctor = .and ∧ references specimen_and = [⟨"leaf", []⟩, ⟨"leaf", []⟩] := by
  exact ⟨rfl, rfl⟩

def specimen_or : Syn .expr := .or (.ident "leaf") (.ident "leaf")

theorem fixture_or : specimen_or.ctor = .or ∧ references specimen_or = [⟨"leaf", []⟩, ⟨"leaf", []⟩] := by
  exact ⟨rfl, rfl⟩

def specimen_cond : Syn .expr := .cond (.ident "leaf") (.ident "leaf") (.ident "leaf")

theorem fixture_cond : specimen_cond.ctor = .cond ∧ references specimen_cond = [⟨"leaf", []⟩, ⟨"leaf", []⟩, ⟨"leaf", []⟩] := by
  exact ⟨rfl, rfl⟩

def specimen_assign : Syn .expr := .assign .assign (.ident "leaf") (.ident "leaf")

theorem fixture_assign : specimen_assign.ctor = .assign ∧ references specimen_assign = [⟨"leaf", []⟩, ⟨"leaf", []⟩] := by
  exact ⟨rfl, rfl⟩

def specimen_new : Syn .expr := .new (.userType marker)

theorem fixture_new : specimen_new.ctor = .new ∧ references specimen_new = [marker] := by
  exact ⟨rfl, rfl⟩

def specimen_tuple : Syn .expr := .tuple (.some (.ident "leaf")) (.cons (.some (.ident "leaf")) .nil)

theorem fixture_tuple : specimen_tuple.ctor = .tuple ∧ references specimen_tuple = [⟨"leaf", []⟩, ⟨"leaf", []⟩] := by
  exact ⟨rfl, rfl⟩

def specimen_inlineArray : Syn .expr := .inlineArray (.ident "leaf") (.cons (.ident "leaf") .nil)

theorem fixture_inlineArray : specimen_inlineArray.ctor = .inlineArray ∧ references specimen_inlineArray = [⟨"leaf", []⟩, ⟨"leaf", []⟩] := by
  exact ⟨rfl, rfl⟩

def specimen_ident : Syn .expr := .ident "token"

theorem fixture_ident : specimen_ident.ctor = .ident ∧ references specimen_ident = [⟨"token", []⟩] := by
  exact ⟨rfl, rfl⟩

def specimen_lit : Syn .expr := .lit (.bool true)

theorem fixture_lit : specimen_lit.ctor = .lit ∧ references specimen_lit = [] := by
  exact ⟨rfl, rfl⟩

def specimen_litUnit : Syn .expr := .litUnit (.dec 1 0 0) .wei

theorem fixture_litUnit : specimen_litUnit.ctor = .litUnit ∧ references specimen_litUnit = [] := by
  exact ⟨rfl, rfl⟩

def specimen_elemType : Syn .expr := .elemType .bool (by decide)

theorem fixture_elemType : specimen_elemType.ctor = .elemType ∧ references specimen_elemType = [] := by
  exact ⟨rfl, rfl⟩

def specimen_declVar : Syn .simple := .declVar (.varDecl (.userType marker) none "v") (.some (.ident "leaf"))

theorem fixture_declVar : specimen_declVar.ctor = .declVar ∧ references specimen_declVar = [marker, ⟨"leaf", []⟩] := by
  exact ⟨rfl, rfl⟩

def specimen_declTuple : Syn .simple := .declTuple 0 (.varDecl (.userType marker) none "v") (.cons (.some (.varDecl (.userType marker) none "v")) .nil) (.ident "leaf")

theorem fixture_declTuple : specimen_declTuple.ctor = .declTuple ∧ references specimen_declTuple = [marker, marker, ⟨"leaf", []⟩] := by
  exact ⟨rfl, rfl⟩

def specimen_exprStmt : Syn .simple := .exprStmt (.ident "leaf")

theorem fixture_exprStmt : specimen_exprStmt.ctor = .exprStmt ∧ references specimen_exprStmt = [⟨"leaf", []⟩] := by
  exact ⟨rfl, rfl⟩

def specimen_blockStmt : Syn (.stmt .body) := .blockStmt (.block (.cons (.stmtItem (.simpleStmt (.exprStmt (.ident "leaf")))) .nil))

theorem fixture_blockStmt : specimen_blockStmt.ctor = .blockStmt ∧ references specimen_blockStmt = [⟨"leaf", []⟩] := by
  exact ⟨rfl, rfl⟩

def specimen_simpleStmt : Syn (.stmt .body) := .simpleStmt (.exprStmt (.ident "leaf"))

theorem fixture_simpleStmt : specimen_simpleStmt.ctor = .simpleStmt ∧ references specimen_simpleStmt = [⟨"leaf", []⟩] := by
  exact ⟨rfl, rfl⟩

def specimen_ifStmt : Syn (.stmt .body) := .ifStmt (.ident "leaf") (.simpleStmt (.exprStmt (.ident "leaf"))) (.some (.simpleStmt (.exprStmt (.ident "leaf"))))

theorem fixture_ifStmt : specimen_ifStmt.ctor = .ifStmt ∧ references specimen_ifStmt = [⟨"leaf", []⟩, ⟨"leaf", []⟩, ⟨"leaf", []⟩] := by
  exact ⟨rfl, rfl⟩

def specimen_forStmt : Syn (.stmt ⟨false, false⟩) := .forStmt (.some (.exprStmt (.ident "leaf"))) (.some (.ident "leaf")) (.some (.ident "leaf")) (.simpleStmt (.exprStmt (.ident "leaf")))

theorem fixture_forStmt : specimen_forStmt.ctor = .forStmt ∧ references specimen_forStmt = [⟨"leaf", []⟩, ⟨"leaf", []⟩, ⟨"leaf", []⟩, ⟨"leaf", []⟩] := by
  exact ⟨rfl, rfl⟩

def specimen_whileStmt : Syn (.stmt ⟨false, false⟩) := .whileStmt (.ident "leaf") (.simpleStmt (.exprStmt (.ident "leaf")))

theorem fixture_whileStmt : specimen_whileStmt.ctor = .whileStmt ∧ references specimen_whileStmt = [⟨"leaf", []⟩, ⟨"leaf", []⟩] := by
  exact ⟨rfl, rfl⟩

def specimen_doWhile : Syn (.stmt ⟨false, false⟩) := .doWhile (.simpleStmt (.exprStmt (.ident "leaf"))) (.ident "leaf")

theorem fixture_doWhile : specimen_doWhile.ctor = .doWhile ∧ references specimen_doWhile = [⟨"leaf", []⟩, ⟨"leaf", []⟩] := by
  exact ⟨rfl, rfl⟩

def specimen_continueStmt : Syn (.stmt ⟨true, false⟩) := .continueStmt

theorem fixture_continueStmt : specimen_continueStmt.ctor = .continueStmt ∧ references specimen_continueStmt = [] := by
  exact ⟨rfl, rfl⟩

def specimen_breakStmt : Syn (.stmt ⟨true, false⟩) := .breakStmt

theorem fixture_breakStmt : specimen_breakStmt.ctor = .breakStmt ∧ references specimen_breakStmt = [] := by
  exact ⟨rfl, rfl⟩

def specimen_tryStmt : Syn (.stmt .body) := .tryStmt (.ident "leaf") (.cons (.param (.userType marker) none none) .nil) (.block (.cons (.stmtItem (.simpleStmt (.exprStmt (.ident "leaf")))) .nil)) (.catchPlain (.block (.cons (.stmtItem (.simpleStmt (.exprStmt (.ident "leaf")))) .nil))) (.cons (.catchPlain (.block (.cons (.stmtItem (.simpleStmt (.exprStmt (.ident "leaf")))) .nil))) .nil)

theorem fixture_tryStmt : specimen_tryStmt.ctor = .tryStmt ∧ references specimen_tryStmt = [⟨"leaf", []⟩, marker, ⟨"leaf", []⟩, ⟨"leaf", []⟩, ⟨"leaf", []⟩] := by
  exact ⟨rfl, rfl⟩

def specimen_catchPlain : Syn (.catchClause .body) := .catchPlain (.block (.cons (.stmtItem (.simpleStmt (.exprStmt (.ident "leaf")))) .nil))

theorem fixture_catchPlain : specimen_catchPlain.ctor = .catchPlain ∧ references specimen_catchPlain = [⟨"leaf", []⟩] := by
  exact ⟨rfl, rfl⟩

def specimen_catchSig : Syn (.catchClause .body) := .catchSig none (.param (.userType marker) none none) (.cons (.param (.userType marker) none none) .nil) (.block (.cons (.stmtItem (.simpleStmt (.exprStmt (.ident "leaf")))) .nil))

theorem fixture_catchSig : specimen_catchSig.ctor = .catchSig ∧ references specimen_catchSig = [marker, marker, ⟨"leaf", []⟩] := by
  exact ⟨rfl, rfl⟩

def specimen_returnStmt : Syn (.stmt .body) := .returnStmt (.some (.ident "leaf"))

theorem fixture_returnStmt : specimen_returnStmt.ctor = .returnStmt ∧ references specimen_returnStmt = [⟨"leaf", []⟩] := by
  exact ⟨rfl, rfl⟩

def specimen_emit : Syn (.stmt .body) := .emit (.ident "leaf") (.positional (.cons (.ident "leaf") .nil))

theorem fixture_emit : specimen_emit.ctor = .emit ∧ references specimen_emit = [⟨"leaf", []⟩, ⟨"leaf", []⟩] := by
  exact ⟨rfl, rfl⟩

def specimen_revert : Syn (.stmt .body) := .revert (.ident "leaf") (.positional (.cons (.ident "leaf") .nil))

theorem fixture_revert : specimen_revert.ctor = .revert ∧ references specimen_revert = [⟨"leaf", []⟩, ⟨"leaf", []⟩] := by
  exact ⟨rfl, rfl⟩

def specimen_assembly : Syn (.stmt .body) := .assembly false [] (.cons (.yulExprStmt (.yulPath "y" ["z"])) .nil)

theorem fixture_assembly : specimen_assembly.ctor = .assembly ∧ references specimen_assembly = [] := by
  exact ⟨rfl, rfl⟩

def specimen_block : Syn (.block .body) := .block (.cons (.stmtItem (.simpleStmt (.exprStmt (.ident "leaf")))) .nil)

theorem fixture_block : specimen_block.ctor = .block ∧ references specimen_block = [⟨"leaf", []⟩] := by
  exact ⟨rfl, rfl⟩

def specimen_stmtItem : Syn (.item .body) := .stmtItem (.simpleStmt (.exprStmt (.ident "leaf")))

theorem fixture_stmtItem : specimen_stmtItem.ctor = .stmtItem ∧ references specimen_stmtItem = [⟨"leaf", []⟩] := by
  exact ⟨rfl, rfl⟩

def specimen_uncheckedItem : Syn (.item ⟨false, false⟩) := .uncheckedItem (.block (.cons (.stmtItem (.simpleStmt (.exprStmt (.ident "leaf")))) .nil))

theorem fixture_uncheckedItem : specimen_uncheckedItem.ctor = .uncheckedItem ∧ references specimen_uncheckedItem = [⟨"leaf", []⟩] := by
  exact ⟨rfl, rfl⟩

def specimen_yulBlock : Syn .yulStmt := .yulBlock (.cons (.yulExprStmt (.yulPath "y" ["z"])) .nil)

theorem fixture_yulBlock : specimen_yulBlock.ctor = .yulBlock ∧ references specimen_yulBlock = [] := by
  exact ⟨rfl, rfl⟩

def specimen_yulLet : Syn .yulStmt := .yulLet "token" [] (.some (.yulPath "y" ["z"]))

theorem fixture_yulLet : specimen_yulLet.ctor = .yulLet ∧ references specimen_yulLet = [] := by
  exact ⟨rfl, rfl⟩

def specimen_yulAssign : Syn .yulStmt := .yulAssign [] [] (.yulPath "y" ["z"])

theorem fixture_yulAssign : specimen_yulAssign.ctor = .yulAssign ∧ references specimen_yulAssign = [] := by
  exact ⟨rfl, rfl⟩

def specimen_yulExprStmt : Syn .yulStmt := .yulExprStmt (.yulPath "y" ["z"])

theorem fixture_yulExprStmt : specimen_yulExprStmt.ctor = .yulExprStmt ∧ references specimen_yulExprStmt = [] := by
  exact ⟨rfl, rfl⟩

def specimen_yulIf : Syn .yulStmt := .yulIf (.yulPath "y" ["z"]) (.cons (.yulExprStmt (.yulPath "y" ["z"])) .nil)

theorem fixture_yulIf : specimen_yulIf.ctor = .yulIf ∧ references specimen_yulIf = [] := by
  exact ⟨rfl, rfl⟩

def specimen_yulFor : Syn .yulStmt := .yulFor (.cons (.yulExprStmt (.yulPath "y" ["z"])) .nil) (.yulPath "y" ["z"]) (.cons (.yulExprStmt (.yulPath "y" ["z"])) .nil) (.cons (.yulExprStmt (.yulPath "y" ["z"])) .nil)

theorem fixture_yulFor : specimen_yulFor.ctor = .yulFor ∧ references specimen_yulFor = [] := by
  exact ⟨rfl, rfl⟩

def specimen_yulSwitch : Syn .yulStmt := .yulSwitch (.yulPath "y" ["z"]) (.cons (.yulCase (.bool true) .nil) .nil) (.some (.cons (.yulExprStmt (.yulPath "y" ["z"])) .nil))

theorem fixture_yulSwitch : specimen_yulSwitch.ctor = .yulSwitch ∧ references specimen_yulSwitch = [] := by
  exact ⟨rfl, rfl⟩

def specimen_yulCase : Syn .yulCase := .yulCase (.bool true) (.cons (.yulExprStmt (.yulPath "y" ["z"])) .nil)

theorem fixture_yulCase : specimen_yulCase.ctor = .yulCase ∧ references specimen_yulCase = [] := by
  exact ⟨rfl, rfl⟩

def specimen_yulLeave : Syn .yulStmt := .yulLeave

theorem fixture_yulLeave : specimen_yulLeave.ctor = .yulLeave ∧ references specimen_yulLeave = [] := by
  exact ⟨rfl, rfl⟩

def specimen_yulBreak : Syn .yulStmt := .yulBreak

theorem fixture_yulBreak : specimen_yulBreak.ctor = .yulBreak ∧ references specimen_yulBreak = [] := by
  exact ⟨rfl, rfl⟩

def specimen_yulContinue : Syn .yulStmt := .yulContinue

theorem fixture_yulContinue : specimen_yulContinue.ctor = .yulContinue ∧ references specimen_yulContinue = [] := by
  exact ⟨rfl, rfl⟩

def specimen_yulFun : Syn .yulStmt := .yulFun "token" [] [] (.cons (.yulExprStmt (.yulPath "y" ["z"])) .nil)

theorem fixture_yulFun : specimen_yulFun.ctor = .yulFun ∧ references specimen_yulFun = [] := by
  exact ⟨rfl, rfl⟩

def specimen_yulPath : Syn .yulExpr := .yulPath "token" []

theorem fixture_yulPath : specimen_yulPath.ctor = .yulPath ∧ references specimen_yulPath = [] := by
  exact ⟨rfl, rfl⟩

def specimen_yulCall : Syn .yulExpr := .yulCall "token" (.cons (.yulPath "y" ["z"]) .nil)

theorem fixture_yulCall : specimen_yulCall.ctor = .yulCall ∧ references specimen_yulCall = [] := by
  exact ⟨rfl, rfl⟩

def specimen_yulLit : Syn .yulExpr := .yulLit (.bool true)

theorem fixture_yulLit : specimen_yulLit.ctor = .yulLit ∧ references specimen_yulLit = [] := by
  exact ⟨rfl, rfl⟩

end Solidity.Frontend.QualifiedUnits.ConstructorFixtures
