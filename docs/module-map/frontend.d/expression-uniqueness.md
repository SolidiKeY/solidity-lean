| `Frontend/ExpressionUniqueness/Accepted.lean` | Accepted expression trees equal every certified tree of their actual tokens The original parseCat_sound certificate supplies the lexical tokens, complete layout witness and precedence. |
| `Frontend/ExpressionUniqueness/AddControls.lean` | Inhabited arbitrary prefix and additive-root controls The old raw-marker countercontrol is handled by the new unfinished-state scan. |
| `Frontend/ExpressionUniqueness/AddFreeAlgebra.lean` | Operand-sensitive additive algebra Expression freedom starts unfinished. |
| `Frontend/ExpressionUniqueness/AddRoot.lean` | Certified additive roots use operand-sensitive last markers This closes the raw-rank-ten marker gap without excluding prefix minus. |
| `Frontend/ExpressionUniqueness/AddScan.lean` | Operand-sensitive additive scans A top-level subtraction is selected only after a completed operand. |
| `Frontend/ExpressionUniqueness/AllRootLevels.lean` | Reconstruct every certified expression precedence level The final level-15/16 boundary follows from the primary spine and the actual primary prefix cut. |
| `Frontend/ExpressionUniqueness/ArgumentIdentity.lean` | Intrinsic argument identity induction steps Actual word-vector and name cuts are derived by the existing span theorems. |
| `Frontend/ExpressionUniqueness/ArgumentSpans.lean` | Positional and named argument constructors reconstruct their word vectors Actual execution supplies comma freedom, nonempty components and the first-token boundary separating positional lists from named braces. |
| `Frontend/ExpressionUniqueness/ArgumentWords.lean` | Actual argument vectors preserve nonempty words and comma boundaries Empty vectors are permitted; empty expression/named-argument component words are not. |
| `Frontend/ExpressionUniqueness/AttributeBalance.lean` | Function-type attribute layout preserves delimiter balance Only the existing token-layout combinators are analyzed. |
| `Frontend/ExpressionUniqueness/AttributeFieldIdentity.lean` | Actual attribute words determine existing function-type fields Arbitrary successful orders reduce to the exact field run. |
| `Frontend/ExpressionUniqueness/AttributeOrderIdentity.lean` | Successful two-field attribute orders are exhaustive Arbitrary layout lists are inverted, not bounded by an assumed length or canonical order. |
| `Frontend/ExpressionUniqueness/AttributeTokens.lean` | Actual function-type attribute tokens belong to their keyword run The original arbitrary layout order is retained. |
| `Frontend/ExpressionUniqueness/AxiomPins.lean` | Exact kernel-reported axiom pins for every source declaration in this lane. |
| `Frontend/ExpressionUniqueness/BinaryControls.lean` | Rank-ten raw-marker limitation is an inhabited arbitrary-family control This is a countercontrol to applying the raw-marker helper at prefix minus, not an ambiguity of certified expression trees. |
| `Frontend/ExpressionUniqueness/BinaryFreeAlgebra.lean` | Parameterized binary marker algebra Marker levels follow the existing Syn.level values. |
| `Frontend/ExpressionUniqueness/BinaryIdentity.lean` | Binary expression identity structural steps Actual certificates determine the root level, constructor and operator. |
| `Frontend/ExpressionUniqueness/BinaryRank.lean` | Certified binary marker classes distinguish lower roots from higher roots The existing root level is classified by exhaustive intrinsic constructors. |
| `Frontend/ExpressionUniqueness/BinaryRoot.lean` | Certified binary root markers follow their associativity Left-associative roots select the last marker of their exact rank; exponentiation selects the first. |
| `Frontend/ExpressionUniqueness/BinarySpans.lean` | Recover binary child words from actual certified printer executions Layouts may differ independently, and may have unconsumed suffixes. |
| `Frontend/ExpressionUniqueness/BoundaryIdentity.lean` | Unary and conditional expression identity steps Certified root levels and actual child-word cuts identify the original constructors/operators. |
| `Frontend/ExpressionUniqueness/Certified.lean` | Certified expression yield uniqueness over the original intrinsic syntax Exhaustive structural induction discharges every actual-child identity premise, including recursive expression/type/parameter/list/optional/argument cycles. |
| `Frontend/ExpressionUniqueness/CertifiedControls.lean` | Inhabited arbitrary-family controls for the complete theorem Arbitrary array depth, parameter counts, optional returns and both attribute orders inhabit a meta-type expression through an array wrapper. |
| `Frontend/ExpressionUniqueness/CommaFreeAlgebra.lean` | Comma-free token algebra for expression spans Every comma-free word below is balanced. |
| `Frontend/ExpressionUniqueness/ConditionalAlgebra.lean` | Conditional balance algebra for successful intrinsic yields Neutral punctuation preserves the question depth. |
| `Frontend/ExpressionUniqueness/ConditionalBalance.lean` | Top-level conditional punctuation balance A delimiter stack hides bracket interiors. |
| `Frontend/ExpressionUniqueness/ConditionalControls.lean` | Arbitrarily nested conditional middle controls Nested true branches contain earlier top-level colons. |
| `Frontend/ExpressionUniqueness/ConditionalSpans.lean` | Recover all three conditional child words from original certificates The first joint low marker reconstructs the condition boundary. |
| `Frontend/ExpressionUniqueness/ContainerControls.lean` | Arbitrary optional-hole vector identity and flattened collision control Full item vectors determine these intrinsic lists against any certified list. |
| `Frontend/ExpressionUniqueness/ContainerIdentity.lean` | Intrinsic list and optional-expression identity steps The only recursive premises are the structural induction predicates for actual children. |
| `Frontend/ExpressionUniqueness/DelimiterReconstruction.lean` | Reconstruct enclosing delimiter boundaries from certified expression tokens The closing delimiter scanner's skip facts are derived from successful balanced execution. |
| `Frontend/ExpressionUniqueness/ElementaryPathPrefix.lean` | Elementary type and path words have maximal prefix cuts The concrete type-atom boundary rejects payable and period continuations. |
| `Frontend/ExpressionUniqueness/ExpressionAddFree.lean` | Certified roots above addition are additively free from an unfinished state The entry bit is false for expressions. |
| `Frontend/ExpressionUniqueness/ExpressionBalance.lean` | Intrinsic expression yields are delimiter-balanced The proof follows the existing indexed syntax through expressions, types, parameters and argument syntax, including their lists and options. |
| `Frontend/ExpressionUniqueness/ExpressionBinaryFree.lean` | Certified higher roots avoid each lower binary marker family The invariant is uniform over binary ranks at least two other than ten. |
| `Frontend/ExpressionUniqueness/ExpressionCommaFree.lean` | Intrinsic expression certificates exclude top-level commas The existing expression/type/argument category closure supplies the separator invariant directly. |
| `Frontend/ExpressionUniqueness/ExpressionConditional.lean` | Existing expression yields pair top-level questions and colons All expression constructors and their type/parameter/call-argument closure are covered without precedence premises. |
| `Frontend/ExpressionUniqueness/ExpressionLowFree.lean` | Certified high-precedence expressions avoid loose-root markers Types and call argument syntax are loose-root-free at their outer level. |
| `Frontend/ExpressionUniqueness/ExpressionMode.lean` | Every successful intrinsic expression yield finishes an operand The completion bit starts arbitrarily. |
| `Frontend/ExpressionUniqueness/ExpressionStart.lean` | Actual expression-category yields never begin with an opening brace All 29 expression constructors and type/parameter/argument closure are covered. |
| `Frontend/ExpressionUniqueness/ExpressionUnaryFree.lean` | Original certified roots above unary operators exclude their outer markers All six prefix and both suffix tokens are absent at delimiter depth zero for roots of level at least15. |
| `Frontend/ExpressionUniqueness/FnTypePrefix.lean` | Function-type words have maximal parameter, attribute and returns cuts The helpers use concrete keyword-run and follower conditions, supplied by actual printer execution and surrounding syntax in the final certificate results. |
| `Frontend/ExpressionUniqueness/FunctionTypeIdentity.lean` | Actual function-type vectors and field identity Successful original printers supply parameter nonemptiness, comma freedom, attribute fields and optional returns boundaries. |
| `Frontend/ExpressionUniqueness/Grouping.lean` | Grouping yield inversion and arbitrary-depth certified controls Parentheses remain the existing one-component tuple. |
| `Frontend/ExpressionUniqueness/LastEnclosure.lean` | Trailing balanced enclosures reconstruct their prefix and payload Mirror the existing token word, use the established first enclosing cut, and mirror back. |
| `Frontend/ExpressionUniqueness/LayoutBoundary.lean` | Successful expression layouts extend and trim The existing printer only pops explicit layout choices. |
| `Frontend/ExpressionUniqueness/LiteralPrefix.lean` | Literal primary words reconstruct their maximal prefix Arbitrary string fragments form a maximal same-kind token run. |
| `Frontend/ExpressionUniqueness/LowControls.lean` | Inhabited loose-root controls with arbitrary conditional middle assignments Every assignment operator and arbitrary prefix depth occurs in the middle of a certified conditional. |
| `Frontend/ExpressionUniqueness/LowFreeAlgebra.lean` | Joint assignment and conditional marker algebra The first loose-root selector includes every assignment operator and question mark. |
| `Frontend/ExpressionUniqueness/LowRoot.lean` | Recover assignment and conditional root marker classes from certificates The first joint loose-root marker is derived from existing recursive precedence and printer certificates. |
| `Frontend/ExpressionUniqueness/MappingIdentity.lean` | Actual intrinsic mapping identity induction step The actual key-name/arrow and value-name fields derive their own maximal-prefix boundaries. |
| `Frontend/ExpressionUniqueness/MappingKeyIdentity.lean` | Existing intrinsic mapping key word reconstruction MapKey is the existing unindexed intrinsic sum. |
| `Frontend/ExpressionUniqueness/MemberSpans.lean` | Member and named-argument names and child words reconstruct The existing special member spelling for address is injective, including all arbitrary identifier strings. |
| `Frontend/ExpressionUniqueness/OperandMode.lean` | Delimiter-aware operand completion state The state contains only the existing delimiter stack and one completion bit. |
| `Frontend/ExpressionUniqueness/OperandModeAlgebra.lean` | Operand-mode algebra for literal fragments, types and attribute layouts Completion is forced by every atom and outer enclosure. |
| `Frontend/ExpressionUniqueness/ParameterIdentity.lean` | Actual parameter fields and recursive identity step The concrete parameter suffix supplies the type-prefix follower boundary internally. |
| `Frontend/ExpressionUniqueness/ParameterWords.lean` | Actual parameter words are nonempty at arbitrary list lengths An empty type word cannot finish an operand from an unfinished state. |
| `Frontend/ExpressionUniqueness/PostfixControls.lean` | Inhabited arbitrary-depth mixed postfix controls Each step includes index, slice, member, options and call. |
| `Frontend/ExpressionUniqueness/PostfixFollowers.lean` | Concrete followers of an existing primary expression The flag is the original primary node's isNew value. |
| `Frontend/ExpressionUniqueness/PostfixIdentity.lean` | Postfix expression identity structural steps Actual certified words identify all five root families and actual child spans. |
| `Frontend/ExpressionUniqueness/PostfixRootKind.lean` | The five postfix constructor families reconstruct from actual words Trailing punctuation separates calls, options, members and square postfixes. |
| `Frontend/ExpressionUniqueness/PostfixSpans.lean` | Actual bracketed postfix children have unique token spans Balanced trailing enclosures reconstruct the existing base and payload words. |
| `Frontend/ExpressionUniqueness/PostfixYieldSplit.lean` | Actual postfix and call-argument printer inversion Recover existing intrinsic children and their successful state executions. |
| `Frontend/ExpressionUniqueness/Primary.lean` | Reconstruction of deterministic primary token yields These results use existing intrinsic constructors and fully consumed layouts. |
| `Frontend/ExpressionUniqueness/PrimaryChildIdentity.lean` | Recursive primary expression identity steps Keyword/enclosure shapes and comma vectors come from actual original yields. |
| `Frontend/ExpressionUniqueness/PrimaryLeafIdentity.lean` | Primary expression leaf identity against every certified competitor Actual certified root levels and token heads derive the family internally. |
| `Frontend/ExpressionUniqueness/PrimaryPrefix.lean` | Reconstruct the complete primary token prefix The certificate supplies the follower through PrimarySpine. |
| `Frontend/ExpressionUniqueness/PrimaryPrefixParts.lean` | Primary word-prefix cuts from actual intrinsic executions Keyword and enclosure boundaries come from successful existing printers. |
| `Frontend/ExpressionUniqueness/PrimarySpine.lean` | Certified high expressions expose an existing primary and actual postfix word The primary is an existing Syn.expr node with level16, never a second AST. |
| `Frontend/ExpressionUniqueness/PrimaryStart.lean` | Actual primary first-token classes The existing unindexed constructor enumeration distinguishes primary families. |
| `Frontend/ExpressionUniqueness/PrimaryYieldSplit.lean` | Actual primary printer components and balanced enclosures Existing intrinsic child nodes and their layout executions are recovered from successful yields. |
| `Frontend/ExpressionUniqueness/RecursiveProperty.lean` | Structural induction predicates over existing intrinsic syntax Word comparison is appropriate for individual expressions/types/arguments. |
| `Frontend/ExpressionUniqueness/ReverseSplit.lean` | Reverse delimiter scanning and last-marker reconstruction Mirroring swaps delimiter directions and reverses token words, preserving the existing token alphabet. |
| `Frontend/ExpressionUniqueness/RootLevelControls.lean` | Arbitrary primary/postfix boundary controls These inhabited families use the original certificates. |
| `Frontend/ExpressionUniqueness/RootLevels.lean` | Original certified root levels agree through unary precedence This combines loose, binary and unary root reconstruction. |
| `Frontend/ExpressionUniqueness/SpanControls.lean` | Arbitrary-family controls for recovered operand spans The additive certificate may contain arbitrarily many unary-minus tokens in its right child. |
| `Frontend/ExpressionUniqueness/StartAlgebra.lean` | Balanced words which do not begin with an opening brace This is a first-token invariant only. |
| `Frontend/ExpressionUniqueness/TypeArrayIdentity.lean` | Reconstruct intrinsic array type roots and recursive identity Balanced dimension words and maximal actual atom prefixes separate arrays from all non-array types, even mapping/function atoms with arbitrary descendants. |
| `Frontend/ExpressionUniqueness/TypeAtomPrefix.lean` | Existing non-array type words reconstruct their maximal prefix Every root and payload property is derived from actual type executions. |
| `Frontend/ExpressionUniqueness/TypeAtomStart.lean` | Non-array type roots distinguish their first token classes The classifiers inspect existing intrinsic nodes and tokens only. |
| `Frontend/ExpressionUniqueness/TypeIdentityControls.lean` | Unconditional identity controls for arbitrary intrinsic type families Structural induction discharges every recursive premise for arbitrary array depths. |
| `Frontend/ExpressionUniqueness/TypeLeafIdentity.lean` | Actual type atom classification and intrinsic leaf identity Array disjointness and actual token heads reconstruct atom families internally. |
| `Frontend/ExpressionUniqueness/TypePrefix.lean` | Arbitrary intrinsic type words reconstruct their maximal prefix Actual execution derives the existing type atom and balanced array spine. |
| `Frontend/ExpressionUniqueness/TypePrefixAlgebra.lean` | Maximal token runs and array-bracket spines These are token boundary lemmas, not a second AST or a producer interface. |
| `Frontend/ExpressionUniqueness/TypePrefixControls.lean` | Type-prefix inhabited families and necessary-boundary countercontrols The raw new-array/direct-new-index token collision is rejected by the ORIGINAL certificate. |
| `Frontend/ExpressionUniqueness/TypeSpine.lean` | Actual type yields decompose into an existing atom and square payload words The atom is an existing intrinsic typeName node. |
| `Frontend/ExpressionUniqueness/TypeYieldSplit.lean` | Invert actual type printer executions All existing fields and layout choices are retained. |
| `Frontend/ExpressionUniqueness/UnaryControls.lean` | Inhabited arbitrary unary-chain controls Every prefix operator has arbitrary direct nesting. |
| `Frontend/ExpressionUniqueness/UnaryFreeAlgebra.lean` | Unary-marker freedom above unary expression roots The selector includes all six prefix tokens and both suffix tokens. |
| `Frontend/ExpressionUniqueness/UnaryRoot.lean` | Unary root reconstruction and actual child spans Prefix tokens select position zero. |
| `Frontend/ExpressionUniqueness/YieldBalance.lean` | Balance algebra for the intrinsic expression printer These token and success-predicate lemmas support the recursive expression/type/ argument category closure. |
| `Frontend/ExpressionUniqueness/YieldShape.lean` | Structural facts about successful intrinsic expression yields A small success-predicate calculus for the existing state printer proves facts about arbitrary inputs and arbitrary remaining layouts. |
| `Frontend/ExpressionUniqueness/YieldSplit.lean` | Invert actual printer executions into successful child executions These are state-printer inversion facts. |
