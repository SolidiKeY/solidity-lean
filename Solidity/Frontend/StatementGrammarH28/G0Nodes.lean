import Solidity.Source.Ctor

/-! Gate G0 node-constructor observation. `Syn.nodes` (`Source/Ctor.lean`)
matches on the indexed family, so kernel-evaluated fixture observers read a
twin by `Syn.casesOn` with a category-generalising motive and structural
recursion, linked to `Syn.nodes` by `g0NodeCtors_eq_nodes`. The order is the
same preorder: root first, then the children left to right. -/
namespace Solidity.Frontend.StatementGrammarH28
open Solidity.Source

private def nodeCtorsAt {category : Cat} (tree : Syn category) : List Ctor := by
  apply Syn.casesOn (motive := fun _ _ => List Ctor) tree
  case nil => intros; exact [Ctor.nil]
  case cons =>
    intros; rename_i s0 s1
    exact Ctor.cons :: (nodeCtorsAt s0 ++ nodeCtorsAt s1)
  case none => intros; exact [Ctor.none]
  case some =>
    intros; rename_i s0
    exact Ctor.some :: (nodeCtorsAt s0)
  case unit =>
    intros; rename_i s0
    exact Ctor.unit :: (nodeCtorsAt s0)
  case pragma => intros; exact [Ctor.pragma]
  case importPath => intros; exact [Ctor.importPath]
  case importSymbols =>
    intros; rename_i s0 s1 _
    exact Ctor.importSymbols :: (nodeCtorsAt s0 ++ nodeCtorsAt s1)
  case importStar => intros; exact [Ctor.importStar]
  case importAlias => intros; exact [Ctor.importAlias]
  case contract =>
    intros; rename_i _ _ s2 s3 s4
    exact Ctor.contract :: (nodeCtorsAt s2 ++ nodeCtorsAt s3 ++ nodeCtorsAt s4)
  case interface =>
    intros; rename_i _ s1 s2
    exact Ctor.interface :: (nodeCtorsAt s1 ++ nodeCtorsAt s2)
  case library =>
    intros; rename_i _ s1
    exact Ctor.library :: (nodeCtorsAt s1)
  case topPart =>
    intros; rename_i s0
    exact Ctor.topPart :: (nodeCtorsAt s0)
  case inherit =>
    intros; rename_i _ s1
    exact Ctor.inherit :: (nodeCtorsAt s1)
  case constructor =>
    intros; rename_i s0 s1 _ _ s4
    exact Ctor.constructor :: (nodeCtorsAt s0 ++ nodeCtorsAt s1 ++ nodeCtorsAt s4)
  case function =>
    intros; rename_i _ s1 _ _ s4 _ _ s7 s8
    exact Ctor.function :: (nodeCtorsAt s1 ++ nodeCtorsAt s4 ++ nodeCtorsAt s7 ++ nodeCtorsAt s8)
  case modifier =>
    intros; rename_i _ s1 _ _ s4
    exact Ctor.modifier :: (nodeCtorsAt s1 ++ nodeCtorsAt s4)
  case fallback =>
    intros; rename_i s0 _ _ s3 _ _ s6
    exact Ctor.fallback :: (nodeCtorsAt s0 ++ nodeCtorsAt s3 ++ nodeCtorsAt s6)
  case fbNoParams => intros; exact [Ctor.fbNoParams]
  case fbParams =>
    intros; rename_i s0 s1 s2
    exact Ctor.fbParams :: (nodeCtorsAt s0 ++ nodeCtorsAt s1 ++ nodeCtorsAt s2)
  case receive =>
    intros; rename_i _ _ s2 _ _ s5
    exact Ctor.receive :: (nodeCtorsAt s2 ++ nodeCtorsAt s5)
  case struct =>
    intros; rename_i _ s1 s2
    exact Ctor.struct :: (nodeCtorsAt s1 ++ nodeCtorsAt s2)
  case structMember =>
    intros; rename_i s0 _
    exact Ctor.structMember :: (nodeCtorsAt s0)
  case enum => intros; exact [Ctor.enum]
  case udvt => intros; exact [Ctor.udvt]
  case stateVar =>
    intros; rename_i s0 _ _ _ _ _ s6
    exact Ctor.stateVar :: (nodeCtorsAt s0 ++ nodeCtorsAt s6)
  case constant =>
    intros; rename_i s0 _ s2
    exact Ctor.constant :: (nodeCtorsAt s0 ++ nodeCtorsAt s2)
  case event =>
    intros; rename_i _ s1 _
    exact Ctor.event :: (nodeCtorsAt s1)
  case eventParam =>
    intros; rename_i s0 _ _
    exact Ctor.eventParam :: (nodeCtorsAt s0)
  case error =>
    intros; rename_i _ s1
    exact Ctor.error :: (nodeCtorsAt s1)
  case errorParam =>
    intros; rename_i s0 _
    exact Ctor.errorParam :: (nodeCtorsAt s0)
  case usingPart =>
    intros; rename_i s0
    exact Ctor.usingPart :: (nodeCtorsAt s0)
  case usingPath =>
    intros; rename_i _ s1 _
    exact Ctor.usingPath :: (nodeCtorsAt s1)
  case usingAliases =>
    intros; rename_i s0 s1 s2 _
    exact Ctor.usingAliases :: (nodeCtorsAt s0 ++ nodeCtorsAt s1 ++ nodeCtorsAt s2)
  case usingAlias => intros; exact [Ctor.usingAlias]
  case positional =>
    intros; rename_i s0
    exact Ctor.positional :: (nodeCtorsAt s0)
  case named =>
    intros; rename_i s0
    exact Ctor.named :: (nodeCtorsAt s0)
  case namedArg =>
    intros; rename_i _ s1
    exact Ctor.namedArg :: (nodeCtorsAt s1)
  case modInv =>
    intros; rename_i _ s1
    exact Ctor.modInv :: (nodeCtorsAt s1)
  case param =>
    intros; rename_i s0 _ _
    exact Ctor.param :: (nodeCtorsAt s0)
  case elem => intros; exact [Ctor.elem]
  case fnType =>
    intros; rename_i s0 _ _ s3
    exact Ctor.fnType :: (nodeCtorsAt s0 ++ nodeCtorsAt s3)
  case mapping =>
    intros; rename_i _ _ s2 _
    exact Ctor.mapping :: (nodeCtorsAt s2)
  case userType => intros; exact [Ctor.userType]
  case array =>
    intros; rename_i s0 s1
    exact Ctor.array :: (nodeCtorsAt s0 ++ nodeCtorsAt s1)
  case varDecl =>
    intros; rename_i s0 _ _
    exact Ctor.varDecl :: (nodeCtorsAt s0)
  case index =>
    intros; rename_i s0 s1
    exact Ctor.index :: (nodeCtorsAt s0 ++ nodeCtorsAt s1)
  case slice =>
    intros; rename_i s0 s1 s2
    exact Ctor.slice :: (nodeCtorsAt s0 ++ nodeCtorsAt s1 ++ nodeCtorsAt s2)
  case member =>
    intros; rename_i s0 _
    exact Ctor.member :: (nodeCtorsAt s0)
  case callOptions =>
    intros; rename_i s0 s1 s2
    exact Ctor.callOptions :: (nodeCtorsAt s0 ++ nodeCtorsAt s1 ++ nodeCtorsAt s2)
  case call =>
    intros; rename_i s0 s1
    exact Ctor.call :: (nodeCtorsAt s0 ++ nodeCtorsAt s1)
  case payableConv =>
    intros; rename_i s0
    exact Ctor.payableConv :: (nodeCtorsAt s0)
  case metaType =>
    intros; rename_i s0
    exact Ctor.metaType :: (nodeCtorsAt s0)
  case unaryPrefix =>
    intros; rename_i _ s1
    exact Ctor.unaryPrefix :: (nodeCtorsAt s1)
  case unarySuffix =>
    intros; rename_i _ s1
    exact Ctor.unarySuffix :: (nodeCtorsAt s1)
  case exp =>
    intros; rename_i s0 s1
    exact Ctor.exp :: (nodeCtorsAt s0 ++ nodeCtorsAt s1)
  case mulDivMod =>
    intros; rename_i _ s1 s2
    exact Ctor.mulDivMod :: (nodeCtorsAt s1 ++ nodeCtorsAt s2)
  case addSub =>
    intros; rename_i _ s1 s2
    exact Ctor.addSub :: (nodeCtorsAt s1 ++ nodeCtorsAt s2)
  case shift =>
    intros; rename_i _ s1 s2
    exact Ctor.shift :: (nodeCtorsAt s1 ++ nodeCtorsAt s2)
  case bitAnd =>
    intros; rename_i s0 s1
    exact Ctor.bitAnd :: (nodeCtorsAt s0 ++ nodeCtorsAt s1)
  case bitXor =>
    intros; rename_i s0 s1
    exact Ctor.bitXor :: (nodeCtorsAt s0 ++ nodeCtorsAt s1)
  case bitOr =>
    intros; rename_i s0 s1
    exact Ctor.bitOr :: (nodeCtorsAt s0 ++ nodeCtorsAt s1)
  case order =>
    intros; rename_i _ s1 s2
    exact Ctor.order :: (nodeCtorsAt s1 ++ nodeCtorsAt s2)
  case equality =>
    intros; rename_i _ s1 s2
    exact Ctor.equality :: (nodeCtorsAt s1 ++ nodeCtorsAt s2)
  case and =>
    intros; rename_i s0 s1
    exact Ctor.and :: (nodeCtorsAt s0 ++ nodeCtorsAt s1)
  case or =>
    intros; rename_i s0 s1
    exact Ctor.or :: (nodeCtorsAt s0 ++ nodeCtorsAt s1)
  case cond =>
    intros; rename_i s0 s1 s2
    exact Ctor.cond :: (nodeCtorsAt s0 ++ nodeCtorsAt s1 ++ nodeCtorsAt s2)
  case assign =>
    intros; rename_i _ s1 s2
    exact Ctor.assign :: (nodeCtorsAt s1 ++ nodeCtorsAt s2)
  case new =>
    intros; rename_i s0
    exact Ctor.new :: (nodeCtorsAt s0)
  case tuple =>
    intros; rename_i s0 s1
    exact Ctor.tuple :: (nodeCtorsAt s0 ++ nodeCtorsAt s1)
  case inlineArray =>
    intros; rename_i s0 s1
    exact Ctor.inlineArray :: (nodeCtorsAt s0 ++ nodeCtorsAt s1)
  case ident => intros; exact [Ctor.ident]
  case lit => intros; exact [Ctor.lit]
  case litUnit => intros; exact [Ctor.litUnit]
  case elemType => intros; exact [Ctor.elemType]
  case declVar =>
    intros; rename_i s0 s1
    exact Ctor.declVar :: (nodeCtorsAt s0 ++ nodeCtorsAt s1)
  case declTuple =>
    intros; rename_i _ s1 s2 s3
    exact Ctor.declTuple :: (nodeCtorsAt s1 ++ nodeCtorsAt s2 ++ nodeCtorsAt s3)
  case exprStmt =>
    intros; rename_i s0
    exact Ctor.exprStmt :: (nodeCtorsAt s0)
  case blockStmt =>
    intros; rename_i s0
    exact Ctor.blockStmt :: (nodeCtorsAt s0)
  case simpleStmt =>
    intros; rename_i s0
    exact Ctor.simpleStmt :: (nodeCtorsAt s0)
  case ifStmt =>
    intros; rename_i s0 s1 s2
    exact Ctor.ifStmt :: (nodeCtorsAt s0 ++ nodeCtorsAt s1 ++ nodeCtorsAt s2)
  case forStmt =>
    intros; rename_i s0 s1 s2 s3
    exact Ctor.forStmt :: (nodeCtorsAt s0 ++ nodeCtorsAt s1 ++ nodeCtorsAt s2 ++ nodeCtorsAt s3)
  case whileStmt =>
    intros; rename_i s0 s1
    exact Ctor.whileStmt :: (nodeCtorsAt s0 ++ nodeCtorsAt s1)
  case doWhile =>
    intros; rename_i s0 s1
    exact Ctor.doWhile :: (nodeCtorsAt s0 ++ nodeCtorsAt s1)
  case continueStmt => intros; exact [Ctor.continueStmt]
  case breakStmt => intros; exact [Ctor.breakStmt]
  case tryStmt =>
    intros; rename_i s0 s1 s2 s3 s4
    exact Ctor.tryStmt :: (nodeCtorsAt s0 ++ nodeCtorsAt s1 ++ nodeCtorsAt s2 ++ nodeCtorsAt s3 ++ nodeCtorsAt s4)
  case catchPlain =>
    intros; rename_i s0
    exact Ctor.catchPlain :: (nodeCtorsAt s0)
  case catchSig =>
    intros; rename_i _ s1 s2 s3
    exact Ctor.catchSig :: (nodeCtorsAt s1 ++ nodeCtorsAt s2 ++ nodeCtorsAt s3)
  case returnStmt =>
    intros; rename_i s0
    exact Ctor.returnStmt :: (nodeCtorsAt s0)
  case emit =>
    intros; rename_i s0 s1
    exact Ctor.emit :: (nodeCtorsAt s0 ++ nodeCtorsAt s1)
  case revert =>
    intros; rename_i s0 s1
    exact Ctor.revert :: (nodeCtorsAt s0 ++ nodeCtorsAt s1)
  case assembly =>
    intros; rename_i _ _ s2
    exact Ctor.assembly :: (nodeCtorsAt s2)
  case block =>
    intros; rename_i s0
    exact Ctor.block :: (nodeCtorsAt s0)
  case stmtItem =>
    intros; rename_i s0
    exact Ctor.stmtItem :: (nodeCtorsAt s0)
  case uncheckedItem =>
    intros; rename_i s0
    exact Ctor.uncheckedItem :: (nodeCtorsAt s0)
  case yulBlock =>
    intros; rename_i s0
    exact Ctor.yulBlock :: (nodeCtorsAt s0)
  case yulLet =>
    intros; rename_i _ _ s2
    exact Ctor.yulLet :: (nodeCtorsAt s2)
  case yulAssign =>
    intros; rename_i _ _ s2
    exact Ctor.yulAssign :: (nodeCtorsAt s2)
  case yulExprStmt =>
    intros; rename_i s0
    exact Ctor.yulExprStmt :: (nodeCtorsAt s0)
  case yulIf =>
    intros; rename_i s0 s1
    exact Ctor.yulIf :: (nodeCtorsAt s0 ++ nodeCtorsAt s1)
  case yulFor =>
    intros; rename_i s0 s1 s2 s3
    exact Ctor.yulFor :: (nodeCtorsAt s0 ++ nodeCtorsAt s1 ++ nodeCtorsAt s2 ++ nodeCtorsAt s3)
  case yulSwitch =>
    intros; rename_i s0 s1 s2
    exact Ctor.yulSwitch :: (nodeCtorsAt s0 ++ nodeCtorsAt s1 ++ nodeCtorsAt s2)
  case yulCase =>
    intros; rename_i _ s1
    exact Ctor.yulCase :: (nodeCtorsAt s1)
  case yulLeave => intros; exact [Ctor.yulLeave]
  case yulBreak => intros; exact [Ctor.yulBreak]
  case yulContinue => intros; exact [Ctor.yulContinue]
  case yulFun =>
    intros; rename_i _ _ _ s3
    exact Ctor.yulFun :: (nodeCtorsAt s3)
  case yulPath => intros; exact [Ctor.yulPath]
  case yulCall =>
    intros; rename_i _ s1
    exact Ctor.yulCall :: (nodeCtorsAt s1)
  case yulLit => intros; exact [Ctor.yulLit]
termination_by structural tree

/-- Every node's constructor, root first, as `Syn.nodes` lists them. -/
def g0NodeCtors {c : Cat} (s : Syn c) : List Ctor := nodeCtorsAt s

/-- The link to the Source observer. -/
theorem g0NodeCtors_eq_nodes {c : Cat} (s : Syn c) :
    g0NodeCtors s = s.nodes.map Node.ctor := by
  suffices h : s.nodes.map Node.ctor = nodeCtorsAt s from h.symm
  induction s
  all_goals (simp only [Syn.nodes, Syn.node, List.map_cons, List.map_append, List.map_nil, *]; rfl)

end Solidity.Frontend.StatementGrammarH28
