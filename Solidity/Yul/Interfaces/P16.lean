import Solidity.Yul.RawU8Declaration
import Solidity.Yul.RawIntegerBlock
import Solidity.Yul.RawIntegerSequence
import Solidity.Yul.RawPreparedInteger
import Solidity.Yul.RawCheckedAdapter
import Solidity.Yul.RawTypedScope
import Solidity.Yul.RawControlGrowingBlock
import Solidity.Yul.RawControlGrowingSequence
import Solidity.Yul.RawControlForPost
import Solidity.Yul.RawControlDeclaration
import Solidity.Yul.RawGrowingForPost
import Solidity.Yul.RawGrowingBlock
import Solidity.Yul.RawGrowingSequence
import Solidity.Yul.RawPreparedDeclaration
import Solidity.Yul.RawDeclarationFrame
import Solidity.Yul.RawCheckedInitializedForPost
import Solidity.Yul.RawCheckedForPost
import Solidity.Yul.RawCheckedAdapterAbsent
import Solidity.Yul.RawCheckedAdapterFor
import Solidity.Yul.RawCheckedAdapterDoWhile
import Solidity.Yul.RawCheckedAdapterLoop
import Solidity.Yul.RawCheckedAdapterIfElse
import Solidity.Yul.RawCheckedAdapterSequence
import Solidity.Yul.Syntax
import Solidity.Yul.BlockTyping
import Solidity.Yul.Words
import Solidity.Yul.WordAdapter
import Solidity.Yul.RawFrame
import Solidity.Yul.RawSourceAdapter
import Solidity.Yul.RawSourceVoidReturn

/-!
# Syntax and bounded raw-local Source interface

This import boundary reuses the published declarations without aliases or a
second representation. Expr and Stmt retain their context/arity/control indices.
RawFrame.State keeps raw words beside unchanged intrinsic Source locals.

RawSourceAdapter.Adapter and ItemAdapter are indexed by actual same-context
Source syntax. Their run fields are executable; their correct fields require
coherent input and exact Source execution equality, including the represented
world and control result. A consumer accepting an Adapter must receive both
fields. No instance for arbitrary statements is supplied by this boundary.

These bounded contracts do not establish general assembly admission, arbitrary
dirty-local Solidity readback, context-changing execution or whole-program
Source-to-EVM adequacy. RawSourceVoidReturn exports the existing void-return
slice separately; it does not generalize Adapter's loop-control result.

Concrete inhabited use and refusal/horizon controls already live in
Solidity.Yul.Checks.RawLiteralScope (adapterTrue, mixed, mixedSource, timeouts).
The core import boundary deliberately does not import that checks module.
RawCheckedAdapter.Adapter adds an explicit pipeline parameter and retains
frame.checked=true in its actual Source agreement field. Its block and
conditional factories provide concrete mixed checked-word/control producers;
fromAdapter reuses the older contract without changing it. These factories do
not provide an instance for arbitrary statements. Inhabited uses and selected
flow/Source controls live in Solidity.Yul.Checks.RawCheckedAdapter.
RawCheckedAdapterSequence.Items retains the same checked/coherent contract for
actual Source item syntax. Its concrete cons and block factories compose
checked producers, preserving short-circuit flow and exact frames. Nested
inhabitants are checked in Solidity.Yul.Checks.RawCheckedAdapterSequence.
No arbitrary-statement producer or general assembly admission follows.
RawCheckedAdapterIfElse.adapter composes actual checked statement producers as
branches, including nested sequence/block producers. Its Source law retains
the supplied producer fields, checked-frame and coherence premises. Concrete
nested witnesses live in Solidity.Yul.Checks.RawCheckedAdapterIfElse.
RawCheckedAdapterLoop.loop composes an actual checked body producer as a
fuelled while statement. Its real fuel induction preserves checked/coherent
Source agreement and consumes body break/continue exactly as Source does.
Nested execution and all-fuel controls live in Solidity.Yul.Checks.RawCheckedAdapterLoop.
RawCheckedAdapterDoWhile.adapter composes an actual checked body producer as
a body-first loop. Its real fuel induction preserves Source guard ordering,
control consumption, exact frames and checked/coherent premises. Nested,
body-order and all-fuel controls live in Solidity.Yul.Checks.RawCheckedAdapterDoWhile.
RawCheckedAdapterFor.adapter composes a same-context checked initializer and
body with a present condition and no post statement. It preserves initializer
effects, errors and Source control rejection before iteration. This does not
cover context-growing initialization, omitted conditions or post clauses.
Concrete composition/refusal controls live in Solidity.Yul.Checks.RawCheckedAdapterFor.
-/

/-! RawCheckedAdapterAbsent.adapter transports a supplied concrete literal-true
for producer to the omitted-condition Source index, retaining runtime and the
checked/coherence premises verbatim. Any post clause still requires the actual
matching producer. Concrete initializer-write/break and refusal witnesses are
in Solidity.Yul.Checks.RawCheckedAdapterAbsent. -/

/-! RawCheckedForPost.run/correct provide same-context checked Source.forIter
execution with a present supported boolean condition/post and an actual
checked body producer. Real fuel induction preserves exact error/control
frames and Source observations under checked/coherent premises. Initializer
composition and context-growing initialization are separate obligations.
Concrete normal/continue/post-timeout/break controls are in
Solidity.Yul.Checks.RawCheckedForPost. -/

/-! RawCheckedInitializedForPost.adapter composes actual same-context checked
initializer/body producers with supported Boolean condition/post expressions.
Its concrete Source.execS forLoop law preserves checked/coherent premises,
initializer control/error frames and actual post-iteration observations.
Context-growing declarations and general assembly admission remain separate.
Combination/refusal witnesses are in Solidity.Yul.Checks.RawCheckedInitializedForPost. -/

/-! RawDeclarationFrame bridges existing typed declaration snapshots into the
existing raw frame at the actual named Source context, with exact word view,
clean-backup/world and conditional coherence laws. Its concrete Boolean literal
runner grows ctx.push and retains the original frame on timeout. The Source law
observes the explicit stored-clean projection; it does not imply dirty-read
cleanup, lexical admission, or general context-growing loop composition.
Dirty-word/growth/refusal controls are in Solidity.Yul.Checks.RawDeclarationFrame. -/

/-! RawPreparedDeclaration supplies a concrete literal declaration runner using
existing exact-word preparation. input_words preserves all represented bits;
coherent_result retains the genuine input-coherence premise. dirty_agrees is
full result/frame equality with the existing materialized runner on incoherent
inputs. Source projection is concrete, not a premise. The extended-context
checked-consumer witness is in Solidity.Yul.Checks.RawPreparedDeclaration;
the enclosing growing block/loop composition remains a separate obligation. -/

/-! RawGrowingSequence.run/correct join an actual prepared Boolean declaration
and actual checked Items tail across the grown context, proving concrete
Source.execItems correspondence. Result distinguishes old-context declaration
errors from reached grown frames; project uses actual Source.Out.up for control.
Checked/coherent premises remain explicit. This joins the child laws, while
final block scope closure and general growing-for admission remain separate.
Concrete joined/control/error-prefix witnesses are in Solidity.Yul.Checks.RawGrowingSequence. -/

/-! RawGrowingBlock.adapter closes the single Boolean declaration around an
actual checked Items tail into an existing same-context checked block producer.
Its Source.execS block correspondence concretely composes the growing sequence
with actual scope restoration/Out.close, retaining checked/coherent premises
and reached error state. Drop removes only the bound prefix via typed values.
Mutation/control/dirty-word controls are in Solidity.Yul.Checks.RawGrowingBlock.
General growing-for/declaration-group/frontend admission remains separate. -/

/-! RawGrowingForPost.adapter composes a Boolean literal initializer that grows
the actual context with present supported Boolean condition/post and a concrete
checked body, then restores the enclosing scope. Its Source.execS forLoop law
joins actual declaration/iteration/restoration proofs with checked/coherent
premises; it is not a preparation-only interface. Mutation/control/post-error
witnesses are in Solidity.Yul.Checks.RawGrowingForPost. General initializers,
declaration groups and frontend admission remain separate obligations. -/

/-! RawControlDeclaration.run/correct supplies actual context-growing Boolean
initialization for every existing LocalBoolControl.Supported expression.
The result distinguishes old-context errors from grown success; real partial
expression state is captured in either branch. The complete Source.execS
declaration law requires input coherence and retains actual result/world.
No arbitrary initializer, frontend admission or dirty-read cleanup follows.
Mutation-before-timeout, raw Boolean/narrow-word and scope controls are in
Solidity.Yul.Checks.RawControlDeclaration. -/

/-! RawControlForPost.adapter composes the actual supported Boolean expression
initializer with grown-context supported condition/post and an actual checked
body. Its full Source.execS forLoop law joins initializer partial errors,
iteration and restoration under genuine checked/coherent premises.
Mutation/continue/break/false-guard and initializer/post timeout witnesses are
in Solidity.Yul.Checks.RawControlForPost. Other initializer types, declaration
groups, dirty Source readback and general admission remain separate. -/

/-! RawControlGrowingSequence.run/correct joins an actual supported Boolean
initializer expression with a concrete checked Items tail at ctx.push.
It reuses RawGrowingSequence.Result/Coherent/project and actual Out.up,
retaining old-context initializer errors versus grown tail frames and
checked/coherent Source premises. Mutation, control restoration and both
error prefixes are witnessed in Solidity.Yul.Checks.RawControlGrowingSequence.
Final block closure, other declarations and frontend admission remain separate. -/

/-! RawControlGrowingBlock.adapter closes the actual supported Boolean
initializer/checked Items sequence through existing scope restoration, producing
a same-context checked block adapter. The full Source.execS law retains actual
initializer/tail errors, older effects and checked/coherent premises.
Closed/nested Source computations and control/error-frame witnesses are in
Solidity.Yul.Checks.RawControlGrowingBlock. Other declarations, dirty Source
readback and general frontend admission remain separate. -/

/-! RawTypedScope supplies one typed LOCAL binder drop/closure with actual
Source restore/Out.up/close laws and genuine coherence premises. Its Boolean
specializations are definitionally the existing operations. Signed/unsigned
integer, dirty-word and control witnesses are in Solidity.Yul.Checks.RawTypedScope.
No initializer execution, physical layout or broader admission follows; concrete
integer declaration composition remains a separate obligation. -/

/-! RawPreparedInteger.run exports an intrinsically typed integer-literal declaration
into a named grown raw frame. The real integer range proof is required. Its
Source.execS law projects stored clean locals; output coherence is proved under
genuine input coherence, while dirty older words are retained independently.
Checks.RawPreparedInteger witnesses signed/unsigned bounds, refusals, timeout
identity and an existing checked uint8 consumer followed by typed scope removal.
Enclosing integer-block composition, arbitrary initializers and dirty ordinary
Source readback remain separate obligations. -/

/-! RawIntegerSequence.run/correct composes the real in-range integer literal
initializer with an existing checked Items producer at ctx.push name (.int ty).
Old initializer errors and grown tail frames remain distinct. The concrete
Source.execItems law retains checked-frame and input-coherence premises and
actual Out.up control restoration. Checks.RawIntegerSequence witnesses mutation,
break/continue, signed values, dirty older words and both timeout prefixes.
Final integer-block closure, arbitrary initializers and admission remain open. -/

/-! RawIntegerBlock.adapter closes the actual integer literal/checked Items
sequence through existing RawTypedScope operations. Its concrete Source.execS
block law preserves real range, checked-frame and input-coherence premises.
Checks.RawIntegerBlock witnesses older mutation, nested checked blocks,
break/continue, signed literals, dirty retained words and timeout boundaries.
Arbitrary initializer expressions/groups, dirty ordinary Source readback and
general frontend admission remain separate obligations. -/

/-! RawU8Declaration.run/correct executes existing supported uint8 expressions
as actual context-growing declarations, retaining partial errors and raw values.
The Source.declInit law requires checked/coherent input. Its zero backup is only
metadata for an incoherent result, not truncation or clean-on-write. Checks include
dirty copies, legacy/viaIR partial timeout differences and unsupported subtraction.
General initializer admission and composition with grown Items remain separate. -/
