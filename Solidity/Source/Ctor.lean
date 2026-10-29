import Solidity.Source.Syntax

/-!
# The constructor index of the source syntax (S00)

`Ctor` names every constructor of `Syn` (`Solidity/Source/Syntax.lean`);
`Ctor.all` lists them and `Ctor.mem_all` proves the list complete.  Each node
of a syntax tree has a constructor and, if it is syntax outside the profile, the
exclusion it triggers (`Syn.excl`, with the manifest's feature ids,
`Excl.id`).  `Syn.rejections` collects them: by `Syn.rejections_of_sub` every
excluded construct anywhere in a tree is named, so a program outside the
profile is rejected with the exact feature.

The mapping from the pinned grammar's rules and labelled alternatives, and
from the manifest's syntax features, to these constructors is in
`Solidity/Source/Upstream.lean`.  The constructor-level definitions
(`Ctor`, `Syn.ctor`, `Syn.children`, `Syn.nodes`) follow `Syn` one line per
constructor.
-/

namespace Solidity.Source

/-- The constructors of `Syn`, one per constructor. -/
inductive Ctor where
  | nil | cons | none | some | unit | pragma
  | importPath | importSymbols | importStar | importAlias | contract | interface
  | library | topPart | inherit | constructor | function | modifier
  | fallback | fbNoParams | fbParams | receive | struct | structMember
  | enum | udvt | stateVar | constant | event | eventParam
  | error | errorParam | usingPart | usingPath | usingAliases | usingAlias
  | positional | named | namedArg | modInv | param | elem
  | fnType | mapping | userType | array | varDecl | index
  | slice | member | callOptions | call | payableConv | metaType
  | unaryPrefix | unarySuffix | exp | mulDivMod | addSub | shift
  | bitAnd | bitXor | bitOr | order | equality | and
  | or | cond | assign | new | tuple | inlineArray
  | ident | lit | litUnit | elemType | declVar | declTuple
  | exprStmt | blockStmt | simpleStmt | ifStmt | forStmt | whileStmt
  | doWhile | continueStmt | breakStmt | tryStmt | catchPlain | catchSig
  | returnStmt | emit | revert | assembly | block | stmtItem
  | uncheckedItem | yulBlock | yulLet | yulAssign | yulExprStmt | yulIf
  | yulFor | yulSwitch | yulCase | yulLeave | yulBreak | yulContinue
  | yulFun | yulPath | yulCall | yulLit
  deriving DecidableEq, Repr

/-- Every constructor, in declaration order. -/
def Ctor.all : List Ctor :=
  [.nil, .cons, .none, .some, .unit, .pragma,
    .importPath, .importSymbols, .importStar, .importAlias, .contract, .interface,
    .library, .topPart, .inherit, .constructor, .function, .modifier,
    .fallback, .fbNoParams, .fbParams, .receive, .struct, .structMember,
    .enum, .udvt, .stateVar, .constant, .event, .eventParam,
    .error, .errorParam, .usingPart, .usingPath, .usingAliases, .usingAlias,
    .positional, .named, .namedArg, .modInv, .param, .elem,
    .fnType, .mapping, .userType, .array, .varDecl, .index,
    .slice, .member, .callOptions, .call, .payableConv, .metaType,
    .unaryPrefix, .unarySuffix, .exp, .mulDivMod, .addSub, .shift,
    .bitAnd, .bitXor, .bitOr, .order, .equality, .and,
    .or, .cond, .assign, .new, .tuple, .inlineArray,
    .ident, .lit, .litUnit, .elemType, .declVar, .declTuple,
    .exprStmt, .blockStmt, .simpleStmt, .ifStmt, .forStmt, .whileStmt,
    .doWhile, .continueStmt, .breakStmt, .tryStmt, .catchPlain, .catchSig,
    .returnStmt, .emit, .revert, .assembly, .block, .stmtItem,
    .uncheckedItem, .yulBlock, .yulLet, .yulAssign, .yulExprStmt, .yulIf,
    .yulFor, .yulSwitch, .yulCase, .yulLeave, .yulBreak, .yulContinue,
    .yulFun, .yulPath, .yulCall, .yulLit]

/-- The syntax-level exclusions of the profile, by manifest feature
(`docs/solidity-features.json`).  `inlineAssembly` and `storageLayout` are
approved exclusions (G00 Q1); the other three are rejected by solc 0.8.38
itself (scope `upstream`). -/
inductive Excl where
  | inlineAssembly
  | storageLayout
  | unsignedRightShift
  | removedUnits
  | removedGenericSolidity
  deriving DecidableEq, Repr

/-- The manifest id of an exclusion. -/
def Excl.id : Excl → String
  | .inlineAssembly => "inlineAssembly"
  | .storageLayout => "storageLayout"
  | .unsignedRightShift => "unsignedRightShift"
  | .removedUnits => "removedUnits"
  | .removedGenericSolidity => "removedGenericSolidity"

/-- A node of a syntax tree: its constructor and the exclusion it
triggers. -/
structure Node where
  ctor : Ctor
  excl : Option Excl
  deriving DecidableEq, Repr

/-- `pragma experimental solidity`, the removed Generic Solidity gate. -/
def pragmaRemoved (text : String) : Bool :=
  (text.splitOn " ").filter (· ≠ "") == ["experimental", "solidity"]

/-- The exclusion the root of a tree triggers: assembly and every Yul
construct, `layout at`, `>>>` and `>>>=`, `years`, and `pragma experimental
solidity`. -/
def Syn.excl : {c : Cat} → Syn c → Option Excl
  | _, .assembly _ _ _ => Option.some .inlineAssembly
  | _, .yulBlock _ => Option.some .inlineAssembly
  | _, .yulLet _ _ _ => Option.some .inlineAssembly
  | _, .yulAssign _ _ _ => Option.some .inlineAssembly
  | _, .yulExprStmt _ => Option.some .inlineAssembly
  | _, .yulIf _ _ => Option.some .inlineAssembly
  | _, .yulFor _ _ _ _ => Option.some .inlineAssembly
  | _, .yulSwitch _ _ _ => Option.some .inlineAssembly
  | _, .yulCase _ _ => Option.some .inlineAssembly
  | _, .yulLeave => Option.some .inlineAssembly
  | _, .yulBreak => Option.some .inlineAssembly
  | _, .yulContinue => Option.some .inlineAssembly
  | _, .yulFun _ _ _ _ => Option.some .inlineAssembly
  | _, .yulPath _ _ => Option.some .inlineAssembly
  | _, .yulCall _ _ => Option.some .inlineAssembly
  | _, .yulLit _ => Option.some .inlineAssembly
  | _, .contract _ _ (.some _) _ _ => Option.some .storageLayout
  | _, .shift .shr _ _ => Option.some .unsignedRightShift
  | _, .assign .shr _ _ => Option.some .unsignedRightShift
  | _, .litUnit _ .years => Option.some .removedUnits
  | _, .pragma text => if pragmaRemoved text then Option.some .removedGenericSolidity else Option.none
  | _, _ => Option.none

/-- The constructor at the root. -/
def Syn.ctor : {c : Cat} → Syn c → Ctor
  | _, .nil => .nil
  | _, .cons _ _ => .cons
  | _, .none => .none
  | _, .some _ => .some
  | _, .unit _ => .unit
  | _, .pragma _ => .pragma
  | _, .importPath _ _ => .importPath
  | _, .importSymbols _ _ _ => .importSymbols
  | _, .importStar _ _ => .importStar
  | _, .importAlias _ _ => .importAlias
  | _, .contract _ _ _ _ _ => .contract
  | _, .interface _ _ _ => .interface
  | _, .library _ _ => .library
  | _, .topPart _ => .topPart
  | _, .inherit _ _ => .inherit
  | _, .constructor _ _ _ _ _ => .constructor
  | _, .function _ _ _ _ _ _ _ _ _ => .function
  | _, .modifier _ _ _ _ _ => .modifier
  | _, .fallback _ _ _ _ _ _ _ => .fallback
  | _, .fbNoParams => .fbNoParams
  | _, .fbParams _ _ _ => .fbParams
  | _, .receive _ _ _ _ _ _ => .receive
  | _, .struct _ _ _ => .struct
  | _, .structMember _ _ => .structMember
  | _, .enum _ _ _ => .enum
  | _, .udvt _ _ => .udvt
  | _, .stateVar _ _ _ _ _ _ _ => .stateVar
  | _, .constant _ _ _ => .constant
  | _, .event _ _ _ => .event
  | _, .eventParam _ _ _ => .eventParam
  | _, .error _ _ => .error
  | _, .errorParam _ _ => .errorParam
  | _, .usingPart _ => .usingPart
  | _, .usingPath _ _ _ => .usingPath
  | _, .usingAliases _ _ _ _ => .usingAliases
  | _, .usingAlias _ _ => .usingAlias
  | _, .positional _ => .positional
  | _, .named _ => .named
  | _, .namedArg _ _ => .namedArg
  | _, .modInv _ _ => .modInv
  | _, .param _ _ _ => .param
  | _, .elem _ => .elem
  | _, .fnType _ _ _ _ => .fnType
  | _, .mapping _ _ _ _ => .mapping
  | _, .userType _ => .userType
  | _, .array _ _ => .array
  | _, .varDecl _ _ _ => .varDecl
  | _, .index _ _ => .index
  | _, .slice _ _ _ => .slice
  | _, .member _ _ => .member
  | _, .callOptions _ _ _ => .callOptions
  | _, .call _ _ => .call
  | _, .payableConv _ => .payableConv
  | _, .metaType _ => .metaType
  | _, .unaryPrefix _ _ => .unaryPrefix
  | _, .unarySuffix _ _ => .unarySuffix
  | _, .exp _ _ => .exp
  | _, .mulDivMod _ _ _ => .mulDivMod
  | _, .addSub _ _ _ => .addSub
  | _, .shift _ _ _ => .shift
  | _, .bitAnd _ _ => .bitAnd
  | _, .bitXor _ _ => .bitXor
  | _, .bitOr _ _ => .bitOr
  | _, .order _ _ _ => .order
  | _, .equality _ _ _ => .equality
  | _, .and _ _ => .and
  | _, .or _ _ => .or
  | _, .cond _ _ _ => .cond
  | _, .assign _ _ _ => .assign
  | _, .new _ => .new
  | _, .tuple _ _ => .tuple
  | _, .inlineArray _ _ => .inlineArray
  | _, .ident _ => .ident
  | _, .lit _ => .lit
  | _, .litUnit _ _ => .litUnit
  | _, .elemType _ _ => .elemType
  | _, .declVar _ _ => .declVar
  | _, .declTuple _ _ _ _ => .declTuple
  | _, .exprStmt _ => .exprStmt
  | _, .blockStmt _ => .blockStmt
  | _, .simpleStmt _ => .simpleStmt
  | _, .ifStmt _ _ _ => .ifStmt
  | _, .forStmt _ _ _ _ => .forStmt
  | _, .whileStmt _ _ => .whileStmt
  | _, .doWhile _ _ => .doWhile
  | _, .continueStmt => .continueStmt
  | _, .breakStmt => .breakStmt
  | _, .tryStmt _ _ _ _ _ => .tryStmt
  | _, .catchPlain _ => .catchPlain
  | _, .catchSig _ _ _ _ => .catchSig
  | _, .returnStmt _ => .returnStmt
  | _, .emit _ _ => .emit
  | _, .revert _ _ => .revert
  | _, .assembly _ _ _ => .assembly
  | _, .block _ => .block
  | _, .stmtItem _ => .stmtItem
  | _, .uncheckedItem _ => .uncheckedItem
  | _, .yulBlock _ => .yulBlock
  | _, .yulLet _ _ _ => .yulLet
  | _, .yulAssign _ _ _ => .yulAssign
  | _, .yulExprStmt _ => .yulExprStmt
  | _, .yulIf _ _ => .yulIf
  | _, .yulFor _ _ _ _ => .yulFor
  | _, .yulSwitch _ _ _ => .yulSwitch
  | _, .yulCase _ _ => .yulCase
  | _, .yulLeave => .yulLeave
  | _, .yulBreak => .yulBreak
  | _, .yulContinue => .yulContinue
  | _, .yulFun _ _ _ _ => .yulFun
  | _, .yulPath _ _ => .yulPath
  | _, .yulCall _ _ => .yulCall
  | _, .yulLit _ => .yulLit

/-- The immediate subterms, with their categories. -/
def Syn.children : {c : Cat} → Syn c → List (Σ c, Syn c)
  | _, .nil => []
  | _, .cons s0 s1 => [⟨_, s0⟩, ⟨_, s1⟩]
  | _, .none => []
  | _, .some s0 => [⟨_, s0⟩]
  | _, .unit s0 => [⟨_, s0⟩]
  | _, .pragma _ => []
  | _, .importPath _ _ => []
  | _, .importSymbols s0 s1 _ => [⟨_, s0⟩, ⟨_, s1⟩]
  | _, .importStar _ _ => []
  | _, .importAlias _ _ => []
  | _, .contract _ _ s2 s3 s4 => [⟨_, s2⟩, ⟨_, s3⟩, ⟨_, s4⟩]
  | _, .interface _ s1 s2 => [⟨_, s1⟩, ⟨_, s2⟩]
  | _, .library _ s1 => [⟨_, s1⟩]
  | _, .topPart s0 => [⟨_, s0⟩]
  | _, .inherit _ s1 => [⟨_, s1⟩]
  | _, .constructor s0 s1 _ _ s4 => [⟨_, s0⟩, ⟨_, s1⟩, ⟨_, s4⟩]
  | _, .function _ s1 _ _ s4 _ _ s7 s8 => [⟨_, s1⟩, ⟨_, s4⟩, ⟨_, s7⟩, ⟨_, s8⟩]
  | _, .modifier _ s1 _ _ s4 => [⟨_, s1⟩, ⟨_, s4⟩]
  | _, .fallback s0 _ _ s3 _ _ s6 => [⟨_, s0⟩, ⟨_, s3⟩, ⟨_, s6⟩]
  | _, .fbNoParams => []
  | _, .fbParams s0 s1 s2 => [⟨_, s0⟩, ⟨_, s1⟩, ⟨_, s2⟩]
  | _, .receive _ _ s2 _ _ s5 => [⟨_, s2⟩, ⟨_, s5⟩]
  | _, .struct _ s1 s2 => [⟨_, s1⟩, ⟨_, s2⟩]
  | _, .structMember s0 _ => [⟨_, s0⟩]
  | _, .enum _ _ _ => []
  | _, .udvt _ _ => []
  | _, .stateVar s0 _ _ _ _ _ s6 => [⟨_, s0⟩, ⟨_, s6⟩]
  | _, .constant s0 _ s2 => [⟨_, s0⟩, ⟨_, s2⟩]
  | _, .event _ s1 _ => [⟨_, s1⟩]
  | _, .eventParam s0 _ _ => [⟨_, s0⟩]
  | _, .error _ s1 => [⟨_, s1⟩]
  | _, .errorParam s0 _ => [⟨_, s0⟩]
  | _, .usingPart s0 => [⟨_, s0⟩]
  | _, .usingPath _ s1 _ => [⟨_, s1⟩]
  | _, .usingAliases s0 s1 s2 _ => [⟨_, s0⟩, ⟨_, s1⟩, ⟨_, s2⟩]
  | _, .usingAlias _ _ => []
  | _, .positional s0 => [⟨_, s0⟩]
  | _, .named s0 => [⟨_, s0⟩]
  | _, .namedArg _ s1 => [⟨_, s1⟩]
  | _, .modInv _ s1 => [⟨_, s1⟩]
  | _, .param s0 _ _ => [⟨_, s0⟩]
  | _, .elem _ => []
  | _, .fnType s0 _ _ s3 => [⟨_, s0⟩, ⟨_, s3⟩]
  | _, .mapping _ _ s2 _ => [⟨_, s2⟩]
  | _, .userType _ => []
  | _, .array s0 s1 => [⟨_, s0⟩, ⟨_, s1⟩]
  | _, .varDecl s0 _ _ => [⟨_, s0⟩]
  | _, .index s0 s1 => [⟨_, s0⟩, ⟨_, s1⟩]
  | _, .slice s0 s1 s2 => [⟨_, s0⟩, ⟨_, s1⟩, ⟨_, s2⟩]
  | _, .member s0 _ => [⟨_, s0⟩]
  | _, .callOptions s0 s1 s2 => [⟨_, s0⟩, ⟨_, s1⟩, ⟨_, s2⟩]
  | _, .call s0 s1 => [⟨_, s0⟩, ⟨_, s1⟩]
  | _, .payableConv s0 => [⟨_, s0⟩]
  | _, .metaType s0 => [⟨_, s0⟩]
  | _, .unaryPrefix _ s1 => [⟨_, s1⟩]
  | _, .unarySuffix _ s1 => [⟨_, s1⟩]
  | _, .exp s0 s1 => [⟨_, s0⟩, ⟨_, s1⟩]
  | _, .mulDivMod _ s1 s2 => [⟨_, s1⟩, ⟨_, s2⟩]
  | _, .addSub _ s1 s2 => [⟨_, s1⟩, ⟨_, s2⟩]
  | _, .shift _ s1 s2 => [⟨_, s1⟩, ⟨_, s2⟩]
  | _, .bitAnd s0 s1 => [⟨_, s0⟩, ⟨_, s1⟩]
  | _, .bitXor s0 s1 => [⟨_, s0⟩, ⟨_, s1⟩]
  | _, .bitOr s0 s1 => [⟨_, s0⟩, ⟨_, s1⟩]
  | _, .order _ s1 s2 => [⟨_, s1⟩, ⟨_, s2⟩]
  | _, .equality _ s1 s2 => [⟨_, s1⟩, ⟨_, s2⟩]
  | _, .and s0 s1 => [⟨_, s0⟩, ⟨_, s1⟩]
  | _, .or s0 s1 => [⟨_, s0⟩, ⟨_, s1⟩]
  | _, .cond s0 s1 s2 => [⟨_, s0⟩, ⟨_, s1⟩, ⟨_, s2⟩]
  | _, .assign _ s1 s2 => [⟨_, s1⟩, ⟨_, s2⟩]
  | _, .new s0 => [⟨_, s0⟩]
  | _, .tuple s0 s1 => [⟨_, s0⟩, ⟨_, s1⟩]
  | _, .inlineArray s0 s1 => [⟨_, s0⟩, ⟨_, s1⟩]
  | _, .ident _ => []
  | _, .lit _ => []
  | _, .litUnit _ _ => []
  | _, .elemType _ _ => []
  | _, .declVar s0 s1 => [⟨_, s0⟩, ⟨_, s1⟩]
  | _, .declTuple _ s1 s2 s3 => [⟨_, s1⟩, ⟨_, s2⟩, ⟨_, s3⟩]
  | _, .exprStmt s0 => [⟨_, s0⟩]
  | _, .blockStmt s0 => [⟨_, s0⟩]
  | _, .simpleStmt s0 => [⟨_, s0⟩]
  | _, .ifStmt s0 s1 s2 => [⟨_, s0⟩, ⟨_, s1⟩, ⟨_, s2⟩]
  | _, .forStmt s0 s1 s2 s3 => [⟨_, s0⟩, ⟨_, s1⟩, ⟨_, s2⟩, ⟨_, s3⟩]
  | _, .whileStmt s0 s1 => [⟨_, s0⟩, ⟨_, s1⟩]
  | _, .doWhile s0 s1 => [⟨_, s0⟩, ⟨_, s1⟩]
  | _, .continueStmt => []
  | _, .breakStmt => []
  | _, .tryStmt s0 s1 s2 s3 s4 => [⟨_, s0⟩, ⟨_, s1⟩, ⟨_, s2⟩, ⟨_, s3⟩, ⟨_, s4⟩]
  | _, .catchPlain s0 => [⟨_, s0⟩]
  | _, .catchSig _ s1 s2 s3 => [⟨_, s1⟩, ⟨_, s2⟩, ⟨_, s3⟩]
  | _, .returnStmt s0 => [⟨_, s0⟩]
  | _, .emit s0 s1 => [⟨_, s0⟩, ⟨_, s1⟩]
  | _, .revert s0 s1 => [⟨_, s0⟩, ⟨_, s1⟩]
  | _, .assembly _ _ s2 => [⟨_, s2⟩]
  | _, .block s0 => [⟨_, s0⟩]
  | _, .stmtItem s0 => [⟨_, s0⟩]
  | _, .uncheckedItem s0 => [⟨_, s0⟩]
  | _, .yulBlock s0 => [⟨_, s0⟩]
  | _, .yulLet _ _ s2 => [⟨_, s2⟩]
  | _, .yulAssign _ _ s2 => [⟨_, s2⟩]
  | _, .yulExprStmt s0 => [⟨_, s0⟩]
  | _, .yulIf s0 s1 => [⟨_, s0⟩, ⟨_, s1⟩]
  | _, .yulFor s0 s1 s2 s3 => [⟨_, s0⟩, ⟨_, s1⟩, ⟨_, s2⟩, ⟨_, s3⟩]
  | _, .yulSwitch s0 s1 s2 => [⟨_, s0⟩, ⟨_, s1⟩, ⟨_, s2⟩]
  | _, .yulCase _ s1 => [⟨_, s1⟩]
  | _, .yulLeave => []
  | _, .yulBreak => []
  | _, .yulContinue => []
  | _, .yulFun _ _ _ s3 => [⟨_, s3⟩]
  | _, .yulPath _ _ => []
  | _, .yulCall _ s1 => [⟨_, s1⟩]
  | _, .yulLit _ => []

/-- The root node. -/
def Syn.node {c : Cat} (s : Syn c) : Node := ⟨s.ctor, s.excl⟩

/-- Every node, root first, with its constructor and the exclusion it
triggers (`Syn.node`). -/
def Syn.nodes : {c : Cat} → Syn c → List Node
  | _, s@(.nil) => s.node :: []
  | _, s@(.cons s0 s1) => s.node :: (s0.nodes ++ s1.nodes)
  | _, s@(.none) => s.node :: []
  | _, s@(.some s0) => s.node :: s0.nodes
  | _, s@(.unit s0) => s.node :: s0.nodes
  | _, s@(.pragma _) => s.node :: []
  | _, s@(.importPath _ _) => s.node :: []
  | _, s@(.importSymbols s0 s1 _) => s.node :: (s0.nodes ++ s1.nodes)
  | _, s@(.importStar _ _) => s.node :: []
  | _, s@(.importAlias _ _) => s.node :: []
  | _, s@(.contract _ _ s2 s3 s4) => s.node :: (s2.nodes ++ s3.nodes ++ s4.nodes)
  | _, s@(.interface _ s1 s2) => s.node :: (s1.nodes ++ s2.nodes)
  | _, s@(.library _ s1) => s.node :: s1.nodes
  | _, s@(.topPart s0) => s.node :: s0.nodes
  | _, s@(.inherit _ s1) => s.node :: s1.nodes
  | _, s@(.constructor s0 s1 _ _ s4) => s.node :: (s0.nodes ++ s1.nodes ++ s4.nodes)
  | _, s@(.function _ s1 _ _ s4 _ _ s7 s8) => s.node :: (s1.nodes ++ s4.nodes ++ s7.nodes ++ s8.nodes)
  | _, s@(.modifier _ s1 _ _ s4) => s.node :: (s1.nodes ++ s4.nodes)
  | _, s@(.fallback s0 _ _ s3 _ _ s6) => s.node :: (s0.nodes ++ s3.nodes ++ s6.nodes)
  | _, s@(.fbNoParams) => s.node :: []
  | _, s@(.fbParams s0 s1 s2) => s.node :: (s0.nodes ++ s1.nodes ++ s2.nodes)
  | _, s@(.receive _ _ s2 _ _ s5) => s.node :: (s2.nodes ++ s5.nodes)
  | _, s@(.struct _ s1 s2) => s.node :: (s1.nodes ++ s2.nodes)
  | _, s@(.structMember s0 _) => s.node :: s0.nodes
  | _, s@(.enum _ _ _) => s.node :: []
  | _, s@(.udvt _ _) => s.node :: []
  | _, s@(.stateVar s0 _ _ _ _ _ s6) => s.node :: (s0.nodes ++ s6.nodes)
  | _, s@(.constant s0 _ s2) => s.node :: (s0.nodes ++ s2.nodes)
  | _, s@(.event _ s1 _) => s.node :: s1.nodes
  | _, s@(.eventParam s0 _ _) => s.node :: s0.nodes
  | _, s@(.error _ s1) => s.node :: s1.nodes
  | _, s@(.errorParam s0 _) => s.node :: s0.nodes
  | _, s@(.usingPart s0) => s.node :: s0.nodes
  | _, s@(.usingPath _ s1 _) => s.node :: s1.nodes
  | _, s@(.usingAliases s0 s1 s2 _) => s.node :: (s0.nodes ++ s1.nodes ++ s2.nodes)
  | _, s@(.usingAlias _ _) => s.node :: []
  | _, s@(.positional s0) => s.node :: s0.nodes
  | _, s@(.named s0) => s.node :: s0.nodes
  | _, s@(.namedArg _ s1) => s.node :: s1.nodes
  | _, s@(.modInv _ s1) => s.node :: s1.nodes
  | _, s@(.param s0 _ _) => s.node :: s0.nodes
  | _, s@(.elem _) => s.node :: []
  | _, s@(.fnType s0 _ _ s3) => s.node :: (s0.nodes ++ s3.nodes)
  | _, s@(.mapping _ _ s2 _) => s.node :: s2.nodes
  | _, s@(.userType _) => s.node :: []
  | _, s@(.array s0 s1) => s.node :: (s0.nodes ++ s1.nodes)
  | _, s@(.varDecl s0 _ _) => s.node :: s0.nodes
  | _, s@(.index s0 s1) => s.node :: (s0.nodes ++ s1.nodes)
  | _, s@(.slice s0 s1 s2) => s.node :: (s0.nodes ++ s1.nodes ++ s2.nodes)
  | _, s@(.member s0 _) => s.node :: s0.nodes
  | _, s@(.callOptions s0 s1 s2) => s.node :: (s0.nodes ++ s1.nodes ++ s2.nodes)
  | _, s@(.call s0 s1) => s.node :: (s0.nodes ++ s1.nodes)
  | _, s@(.payableConv s0) => s.node :: s0.nodes
  | _, s@(.metaType s0) => s.node :: s0.nodes
  | _, s@(.unaryPrefix _ s1) => s.node :: s1.nodes
  | _, s@(.unarySuffix _ s1) => s.node :: s1.nodes
  | _, s@(.exp s0 s1) => s.node :: (s0.nodes ++ s1.nodes)
  | _, s@(.mulDivMod _ s1 s2) => s.node :: (s1.nodes ++ s2.nodes)
  | _, s@(.addSub _ s1 s2) => s.node :: (s1.nodes ++ s2.nodes)
  | _, s@(.shift _ s1 s2) => s.node :: (s1.nodes ++ s2.nodes)
  | _, s@(.bitAnd s0 s1) => s.node :: (s0.nodes ++ s1.nodes)
  | _, s@(.bitXor s0 s1) => s.node :: (s0.nodes ++ s1.nodes)
  | _, s@(.bitOr s0 s1) => s.node :: (s0.nodes ++ s1.nodes)
  | _, s@(.order _ s1 s2) => s.node :: (s1.nodes ++ s2.nodes)
  | _, s@(.equality _ s1 s2) => s.node :: (s1.nodes ++ s2.nodes)
  | _, s@(.and s0 s1) => s.node :: (s0.nodes ++ s1.nodes)
  | _, s@(.or s0 s1) => s.node :: (s0.nodes ++ s1.nodes)
  | _, s@(.cond s0 s1 s2) => s.node :: (s0.nodes ++ s1.nodes ++ s2.nodes)
  | _, s@(.assign _ s1 s2) => s.node :: (s1.nodes ++ s2.nodes)
  | _, s@(.new s0) => s.node :: s0.nodes
  | _, s@(.tuple s0 s1) => s.node :: (s0.nodes ++ s1.nodes)
  | _, s@(.inlineArray s0 s1) => s.node :: (s0.nodes ++ s1.nodes)
  | _, s@(.ident _) => s.node :: []
  | _, s@(.lit _) => s.node :: []
  | _, s@(.litUnit _ _) => s.node :: []
  | _, s@(.elemType _ _) => s.node :: []
  | _, s@(.declVar s0 s1) => s.node :: (s0.nodes ++ s1.nodes)
  | _, s@(.declTuple _ s1 s2 s3) => s.node :: (s1.nodes ++ s2.nodes ++ s3.nodes)
  | _, s@(.exprStmt s0) => s.node :: s0.nodes
  | _, s@(.blockStmt s0) => s.node :: s0.nodes
  | _, s@(.simpleStmt s0) => s.node :: s0.nodes
  | _, s@(.ifStmt s0 s1 s2) => s.node :: (s0.nodes ++ s1.nodes ++ s2.nodes)
  | _, s@(.forStmt s0 s1 s2 s3) => s.node :: (s0.nodes ++ s1.nodes ++ s2.nodes ++ s3.nodes)
  | _, s@(.whileStmt s0 s1) => s.node :: (s0.nodes ++ s1.nodes)
  | _, s@(.doWhile s0 s1) => s.node :: (s0.nodes ++ s1.nodes)
  | _, s@(.continueStmt) => s.node :: []
  | _, s@(.breakStmt) => s.node :: []
  | _, s@(.tryStmt s0 s1 s2 s3 s4) => s.node :: (s0.nodes ++ s1.nodes ++ s2.nodes ++ s3.nodes ++ s4.nodes)
  | _, s@(.catchPlain s0) => s.node :: s0.nodes
  | _, s@(.catchSig _ s1 s2 s3) => s.node :: (s1.nodes ++ s2.nodes ++ s3.nodes)
  | _, s@(.returnStmt s0) => s.node :: s0.nodes
  | _, s@(.emit s0 s1) => s.node :: (s0.nodes ++ s1.nodes)
  | _, s@(.revert s0 s1) => s.node :: (s0.nodes ++ s1.nodes)
  | _, s@(.assembly _ _ s2) => s.node :: s2.nodes
  | _, s@(.block s0) => s.node :: s0.nodes
  | _, s@(.stmtItem s0) => s.node :: s0.nodes
  | _, s@(.uncheckedItem s0) => s.node :: s0.nodes
  | _, s@(.yulBlock s0) => s.node :: s0.nodes
  | _, s@(.yulLet _ _ s2) => s.node :: s2.nodes
  | _, s@(.yulAssign _ _ s2) => s.node :: s2.nodes
  | _, s@(.yulExprStmt s0) => s.node :: s0.nodes
  | _, s@(.yulIf s0 s1) => s.node :: (s0.nodes ++ s1.nodes)
  | _, s@(.yulFor s0 s1 s2 s3) => s.node :: (s0.nodes ++ s1.nodes ++ s2.nodes ++ s3.nodes)
  | _, s@(.yulSwitch s0 s1 s2) => s.node :: (s0.nodes ++ s1.nodes ++ s2.nodes)
  | _, s@(.yulCase _ s1) => s.node :: s1.nodes
  | _, s@(.yulLeave) => s.node :: []
  | _, s@(.yulBreak) => s.node :: []
  | _, s@(.yulContinue) => s.node :: []
  | _, s@(.yulFun _ _ _ s3) => s.node :: s3.nodes
  | _, s@(.yulPath _ _) => s.node :: []
  | _, s@(.yulCall _ s1) => s.node :: s1.nodes
  | _, s@(.yulLit _) => s.node :: []

/-- The exclusions a tree triggers, root first. -/
def Syn.rejections {c : Cat} (s : Syn c) : List Excl := s.nodes.filterMap Node.excl

/-- Syntax inside the profile: no node triggers an exclusion. -/
def Syn.InProfile {c : Cat} (s : Syn c) : Prop := s.rejections = []

instance {c : Cat} (s : Syn c) : Decidable s.InProfile :=
  inferInstanceAs (Decidable (s.rejections = []))

/-! ## The index is complete -/

theorem Ctor.mem_all (k : Ctor) : k ∈ Ctor.all := by
  cases k <;> decide

theorem Ctor.length_all : Ctor.all.length = 112 := rfl

/-! ## Nodes and subterms -/

/-- The nodes of a tree are its root's and its children's. -/
theorem Syn.nodes_eq {c : Cat} (s : Syn c) :
    s.nodes = s.node :: s.children.flatMap fun x => x.2.nodes := by
  cases s <;> simp only [Syn.nodes, Syn.children, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, List.append_assoc]

theorem Syn.node_mem {c : Cat} (s : Syn c) : s.node ∈ s.nodes := by
  rw [Syn.nodes_eq]
  exact List.mem_cons_self ..

/-- `t` is a subterm of `s` (reflexive). -/
inductive Syn.Sub : (Σ c, Syn c) → (Σ c, Syn c) → Prop where
  | refl (x : Σ c, Syn c) : Syn.Sub x x
  | child {x y : Σ c, Syn c} {c : Cat} {s : Syn c} : y ∈ s.children → Syn.Sub x y →
      Syn.Sub x ⟨c, s⟩

theorem Syn.nodes_sub {x y : Σ c, Syn c} (h : Syn.Sub x y) : ∀ n, n ∈ x.2.nodes → n ∈ y.2.nodes := by
  induction h with
  | refl => exact fun _ hn => hn
  | child hy _ ih =>
    intro n hn
    rw [Syn.nodes_eq]
    exact List.mem_cons_of_mem _ (List.mem_flatMap.2 ⟨_, hy, ih n hn⟩)

theorem Syn.mem_rejections {c : Cat} (s : Syn c) (f : Excl) :
    f ∈ s.rejections ↔ ∃ n, n ∈ s.nodes ∧ n.excl = Option.some f := by
  simp only [Syn.rejections, List.mem_filterMap]

/-- **Precise rejection**: an excluded construct anywhere in a tree is among
the tree's rejections, with its feature. -/
theorem Syn.rejections_of_sub {c c' : Cat} {s : Syn c} {t : Syn c'} {f : Excl}
    (h : Syn.Sub ⟨c', t⟩ ⟨c, s⟩) (ht : t.excl = Option.some f) : f ∈ s.rejections :=
  (Syn.mem_rejections s f).2 ⟨t.node, Syn.nodes_sub h _ t.node_mem, ht⟩

/-- **Every rejection is witnessed**: an exclusion among a tree's rejections
is triggered by one of its nodes. -/
theorem Syn.rejections_witnessed {c : Cat} {s : Syn c} {f : Excl} (h : f ∈ s.rejections) :
    ∃ n, n ∈ s.nodes ∧ n.excl = Option.some f :=
  (Syn.mem_rejections s f).1 h

end Solidity.Source
