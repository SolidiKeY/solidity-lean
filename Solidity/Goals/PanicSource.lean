import Solidity.Tools.Goal
import Solidity.Syntax.Elab.Stmt
import Solidity.Syntax.Elab.Panic

/-!
# Source association of the panic producers (plan w3d-panic-dispatch)

Third component of finish-line goal 5 (`runCarriesPanicCodes`): which producer emits which panic, at
the producers themselves. Three clauses, each written against public names only.

* `PanicGuardSources`, `PanicCaptureSources` (clause a): the statements of the theorems of
  `Syntax/Elab/Panic.lean`, `Correctness/Panic/Guards/Arith.lean`, `Guards/State.lean` and `Capture.lean`.
* `PanicDispatchProducers` (clause b): for an arbitrary `rc : PanicProducerRec C`, the exact equations of
  the dispatch and self-call producers of `Syntax/Elab/Stmt.lean`, their transfer to the public names and
  to `elabRec`, and the run of the dispatch fallback.

Not claimed: anything about programs elaborated by `elabStmtsP`, `elabScope`, `elabCallRet` or
`extDispatch` (they stay `partial`; here they are the fields of an arbitrary `rc`), whole-program
instrumentation, or an origin for arbitrary revert data. The fallback fires for every unmatched tag and
carries code `0x51`; an intrinsic origin is stated for the zero tag only, with no validity premise.
-/

namespace Solidity.Goals

open Solidity Semantics Checked

/-- Clause (a), the typed guards: the transparent producers of `Syntax/Elab/Panic.lean` and the guard
families of `Correctness/Panic/Guards/Arith.lean` and `Guards/State.lean`. Each conjunct is the
statement of the theorem of that name. -/
def PanicGuardSources : Prop := ∀ {C : Contract} {Γ : Ctx},
  -- In order: `checking_guard_source`, `withPanics_source_cons`, `uint_divisor_source`, `enum_guard_origin`,
  -- `uint_narrow_guard_origin`, `int_narrow_guard_origin`, `panic_guard_source_failure`,
  -- `panic_guard_source_halt`.
  (∀ {Γ : Ctx} (condition : Val C Γ .bool), OFMode.checking.guardStmt condition true =
    panicStmt Panic.Site.arithmetic.code condition) ∧
  (∀ {Γ Γ₁ Γ₂ : Ctx} (statement : Stmt C Γ Γ₁) (tail : Prog C Γ₁ Γ₂), (Prog.cons statement tail).withPanics =
    statement.panics.foldr (fun (code, condition) rest => .cons (panicStmt code condition) rest)
    (.cons statement.withPanics tail.withPanics)) ∧
  (∀ (σ : State C Γ) (a b : Val C Γ .uint) (x y : PrimTy.uint.Denote) (left : a.evalT σ = .ok x)
    (right : b.evalT σ = .ok y)
    (failed : (Checked.cmpU .neB rfl rfl b (Checked.litU 0 (by decide))).evalT σ = .ok false),
    Checked.divPG .div .uint b =
    [(Panic.Site.zeroDivisor.code, Checked.cmpU .neB rfl rfl b (Checked.litU 0 (by decide)))] ∧ Panic.Origin
    (.binary .div .uint rfl x y) .zeroDivisor ∧ (Val.binop .div rfl rfl a b).evalT σ = .error .revert ∧
    (panicStmt Panic.Site.zeroDivisor.code (Checked.cmpU .neB rfl rfl b (Checked.litU 0 (by decide)))).runR σ =
    .error (THalt.ofData (encodePanic Panic.Site.zeroDivisor.code))) ∧
  (∀ (σ : State C Γ) (captured : Val C Γ .uint) (value : PrimTy.uint.Denote) (members : Nat)
    (range : PrimTy.uint.inRange (members : Int) = true) (read : captured.evalT σ = .ok value)
    (failed : (Checked.cmpU .lt rfl rfl captured (Checked.litU members range)).evalT σ = .ok false),
    Panic.Source.OriginV2 (.original (.enumConversion members value)) .enumConversion) ∧
  (∀ (σ : State C Γ) (expression : Val C Γ .uint) (value : PrimTy.uint.Denote) (width : Nat)
    (narrow : width < 256) (range : PrimTy.uint.inRange (((2 ^ width - 1 : Nat) : Int)) = true)
    (read : expression.evalT σ = .ok value) (failed : (Checked.cmpU .le rfl rfl expression (Checked.litU ((2 ^
    width - 1 : Nat) : Int) range)).evalT σ = .ok false), Panic.Source.OriginV2
    (.narrowing (.unsigned width value)) .arithmetic) ∧
  (∀ (σ : State C Γ) (expression : Val C Γ .int) (value : PrimTy.int.Denote) (width : Nat)
    (narrow : width < 256) (lo : PrimTy.int.inRange (-((2 ^ (width - 1) : Nat) : Int)) = true)
    (hi : PrimTy.int.inRange ((2 ^ (width - 1) - 1 : Nat) : Int) = true) (read : expression.evalT σ = .ok value)
    (failed : (Checked.andB (Checked.cmpI .le rfl rfl (Checked.litI (-((2 ^ (width - 1) : Nat) : Int)) lo)
    expression) (Checked.cmpI .le rfl rfl expression (Checked.litI ((2 ^ (width - 1) - 1 : Nat) : Int)
    hi))).evalT σ = .ok false), Panic.Source.OriginV2 (.narrowing (.signed width value)) .arithmetic) ∧
  (∀ (σ : State C Γ) (condition : Val C Γ .bool) (failed : condition.evalT σ = .ok false) (code : Nat),
    (panicStmt code condition).runR σ = .error (THalt.ofData (encodePanic code))) ∧
  (∀ (σ : State C Γ) (condition : Val C Γ .bool) (halt : THalt) (failed : condition.evalT σ = .error halt)
    (code : Nat), (panicStmt code condition).runR σ = .error halt) ∧
  -- In order: `uint_mod_source`, `int_div_zero_source`, `int_mod_source`, `modular_source`, `assert_source`,
  -- `uint_add_source`, `uint_sub_source`, `uint_mul_source`, `int_div_overflow_source`, `int_neg_source`,
  -- `int_add_source`, `int_sub_source`.
  (∀ (σ : State C Γ) (a b : Val C Γ .uint) (x y : PrimTy.uint.Denote) (left : a.evalT σ = .ok x)
    (right : b.evalT σ = .ok y) (failed : (cmpU .neB rfl rfl b (litU 0 (by decide))).evalT σ = .ok false),
    divPG .mod .uint b = [(Panic.Site.zeroDivisor.code, cmpU .neB rfl rfl b (litU 0 (by decide)))] ∧
    Panic.Origin (.binary .mod .uint rfl x y) .zeroDivisor ∧ (Val.binop .mod rfl rfl a b).evalT σ =
    .error .revert ∧ (panicStmt Panic.Site.zeroDivisor.code (cmpU .neB rfl rfl b (litU 0 (by decide)))).runR σ =
    .error (THalt.ofData (encodePanic Panic.Site.zeroDivisor.code))) ∧
  (∀ (σ : State C Γ) (a b : Val C Γ .int) (x y : PrimTy.int.Denote) (left : a.evalT σ = .ok x)
    (right : b.evalT σ = .ok y) (failed : (cmpI .neB rfl rfl b (litI 0 (by decide))).evalT σ = .ok false),
    divPG .div .int b = [(Panic.Site.zeroDivisor.code, cmpI .neB rfl rfl b (litI 0 (by decide)))] ∧ Panic.Origin
    (.binary .div .int rfl x y) .zeroDivisor ∧ (Val.binop .div rfl rfl a b).evalT σ = .error .revert ∧
    (panicStmt Panic.Site.zeroDivisor.code (cmpI .neB rfl rfl b (litI 0 (by decide)))).runR σ = .error
    (THalt.ofData (encodePanic Panic.Site.zeroDivisor.code))) ∧
  (∀ (σ : State C Γ) (a b : Val C Γ .int) (x y : PrimTy.int.Denote) (left : a.evalT σ = .ok x)
    (right : b.evalT σ = .ok y) (failed : (cmpI .neB rfl rfl b (litI 0 (by decide))).evalT σ = .ok false),
    divPG .mod .int b = [(Panic.Site.zeroDivisor.code, cmpI .neB rfl rfl b (litI 0 (by decide)))] ∧ Panic.Origin
    (.binary .mod .int rfl x y) .zeroDivisor ∧ (Val.binop .mod rfl rfl a b).evalT σ = .error .revert ∧
    (panicStmt Panic.Site.zeroDivisor.code (cmpI .neB rfl rfl b (litI 0 (by decide)))).runR σ = .error
    (THalt.ofData (encodePanic Panic.Site.zeroDivisor.code))) ∧
  (∀ (σ : State C Γ) (op : ModOp) (a b k : Val C Γ .uint) (x y m : PrimTy.uint.Denote) (ra : a.evalT σ = .ok x)
    (rb : b.evalT σ = .ok y) (rk : k.evalT σ = .ok m)
    (failed : (cmpU .neB rfl rfl k (litU 0 (by decide))).evalT σ = .ok false), (Val.modular op a b k).panics =
    a.panics ++ b.panics ++ k.panics ++
    [(Panic.Site.zeroDivisor.code, cmpU .neB rfl rfl k (litU 0 (by decide)))] ∧ Panic.Origin
    (.modular op x y m) .zeroDivisor ∧ (Val.modular op a b k).evalT σ = .error .revert ∧
    (panicStmt Panic.Site.zeroDivisor.code (cmpU .neB rfl rfl k (litU 0 (by decide)))).runR σ = .error
    (THalt.ofData (encodePanic Panic.Site.zeroDivisor.code))) ∧
  (∀ (σ : State C Γ) (c : Val C Γ .bool) (failed : c.evalT σ = .ok false), Panic.Origin
    (.assertion false) .assertion ∧ (Stmt.assert c).runR σ = .error .panic ∧
    (Stmt.ite c .nil (.cons (.revertData [.bytes (Semantics.encodePanic 1)]) .nil)).runR σ = .error
    (THalt.ofData (encodePanic Panic.Site.assertion.code))) ∧
  (∀ (σ : State C Γ) (a b : Val C Γ .uint) (x y : PrimTy.uint.Denote) (left : a.evalT σ = .ok x)
    (right : b.evalT σ = .ok y) (failed : (cmpU .le rfl rfl a (arU .addW rfl rfl a b)).evalT σ = .ok false),
    pg Panic.Site.arithmetic.code (range .add .uint a b) =
    [(Panic.Site.arithmetic.code, cmpU .le rfl rfl a (arU .addW rfl rfl a b))] ∧ Panic.Origin
    (.binary .add .uint rfl x y) .arithmetic ∧ (Val.binop .add rfl rfl a b).evalT σ = .error .revert ∧
    (panicStmt Panic.Site.arithmetic.code (cmpU .le rfl rfl a (arU .addW rfl rfl a b))).runR σ = .error
    (THalt.ofData (encodePanic Panic.Site.arithmetic.code))) ∧
  (∀ (σ : State C Γ) (a b : Val C Γ .uint) (x y : PrimTy.uint.Denote) (left : a.evalT σ = .ok x)
    (right : b.evalT σ = .ok y) (failed : (cmpU .le rfl rfl b a).evalT σ = .ok false),
    pg Panic.Site.arithmetic.code (range .sub .uint a b) =
    [(Panic.Site.arithmetic.code, cmpU .le rfl rfl b a)] ∧ Panic.Origin
    (.binary .sub .uint rfl x y) .arithmetic ∧ (Val.binop .sub rfl rfl a b).evalT σ = .error .revert ∧
    (panicStmt Panic.Site.arithmetic.code (cmpU .le rfl rfl b a)).runR σ = .error
    (THalt.ofData (encodePanic Panic.Site.arithmetic.code))) ∧
  (∀ (σ : State C Γ) (a b : Val C Γ .uint) (x y : PrimTy.uint.Denote) (left : a.evalT σ = .ok x)
    (right : b.evalT σ = .ok y) (failed : (orB (cmpU .eqB rfl rfl a (litU 0 (by decide))) (cmpU .eqB rfl rfl
    (arU .div rfl rfl (arU .mulW rfl rfl a b) a) b)).evalT σ = .ok false), pg Panic.Site.arithmetic.code
    (range .mul .uint a b) = [(Panic.Site.arithmetic.code, orB (cmpU .eqB rfl rfl a (litU 0 (by decide))) (cmpU
    .eqB rfl rfl (arU .div rfl rfl (arU .mulW rfl rfl a b) a) b))] ∧ Panic.Origin
    (.binary .mul .uint rfl x y) .arithmetic ∧ (Val.binop .mul rfl rfl a b).evalT σ = .error .revert ∧
    (panicStmt Panic.Site.arithmetic.code (orB (cmpU .eqB rfl rfl a (litU 0 (by decide))) (cmpU .eqB rfl rfl
    (arU .div rfl rfl (arU .mulW rfl rfl a b) a) b))).runR σ = .error
    (THalt.ofData (encodePanic Panic.Site.arithmetic.code))) ∧
  (∀ (σ : State C Γ) (a b : Val C Γ .int) (x y : PrimTy.int.Denote) (left : a.evalT σ = .ok x)
    (right : b.evalT σ = .ok y) (failed : (notB (andB (cmpI .eqB rfl rfl a (litI minI (by decide))) (cmpI .eqB
    rfl rfl b (litI (-1) (by decide))))).evalT σ = .ok false), pg Panic.Site.arithmetic.code
    (range .div .int a b) = [(Panic.Site.arithmetic.code, notB (andB (cmpI .eqB rfl rfl a (litI minI (by
    decide))) (cmpI .eqB rfl rfl b (litI (-1) (by decide)))))] ∧ Panic.Origin
    (.binary .div .int rfl x y) .arithmetic ∧ (Val.binop .div rfl rfl a b).evalT σ = .error .revert ∧ (panicStmt
    Panic.Site.arithmetic.code (notB (andB (cmpI .eqB rfl rfl a (litI minI (by decide))) (cmpI .eqB rfl rfl b
    (litI (-1) (by decide)))))).runR σ = .error (THalt.ofData (encodePanic Panic.Site.arithmetic.code))) ∧
  (∀ (σ : State C Γ) (a : Val C Γ .int) (x : PrimTy.int.Denote) (read : a.evalT σ = .ok x)
    (failed : (cmpI .neB rfl rfl a (litI minI (by decide))).evalT σ = .ok false), pg Panic.Site.arithmetic.code
    (negRange .int a) = [(Panic.Site.arithmetic.code, cmpI .neB rfl rfl a (litI minI (by decide)))] ∧
    Panic.Origin (.neg x) .arithmetic ∧ (Val.unop .neg rfl rfl a).evalT σ = .error .revert ∧
    (panicStmt Panic.Site.arithmetic.code (cmpI .neB rfl rfl a (litI minI (by decide)))).runR σ = .error
    (THalt.ofData (encodePanic Panic.Site.arithmetic.code))) ∧
  (∀ (σ : State C Γ) (a b : Val C Γ .int) (x y : PrimTy.int.Denote) (left : a.evalT σ = .ok x)
    (right : b.evalT σ = .ok y) (g : Val C Γ .bool) (gen : range .add .int a b = some g)
    (failed : g.evalT σ = .ok false), pg Panic.Site.arithmetic.code (range .add .int a b) =
    [(Panic.Site.arithmetic.code, g)] ∧ Panic.Origin (.binary .add .int rfl x y) .arithmetic ∧
    (Val.binop .add rfl rfl a b).evalT σ = .error .revert ∧ (panicStmt Panic.Site.arithmetic.code g).runR σ =
    .error (THalt.ofData (encodePanic Panic.Site.arithmetic.code))) ∧
  (∀ (σ : State C Γ) (a b : Val C Γ .int) (x y : PrimTy.int.Denote) (left : a.evalT σ = .ok x)
    (right : b.evalT σ = .ok y) (g : Val C Γ .bool) (gen : range .sub .int a b = some g)
    (failed : g.evalT σ = .ok false), pg Panic.Site.arithmetic.code (range .sub .int a b) =
    [(Panic.Site.arithmetic.code, g)] ∧ Panic.Origin (.binary .sub .int rfl x y) .arithmetic ∧
    (Val.binop .sub rfl rfl a b).evalT σ = .error .revert ∧ (panicStmt Panic.Site.arithmetic.code g).runR σ =
    .error (THalt.ofData (encodePanic Panic.Site.arithmetic.code))) ∧
  -- In order: `storage_mapping_index_no_guard`, `storage_dyn_index_source`, `storage_fixed_index_source`,
  -- `memory_dyn_index_source`, `memory_fixed_index_source`, `pop_source`, `guard_under_failed`.
  (∀ {k : PrimTy} {V : Ty} (b : SPath C Γ (.ref (.mapping k V))) (i : Val C Γ k), Checked.idxPG .map b i = []) ∧
  (∀ {E : Ty} (σ : State C Γ) (b : SPath C Γ (.ref (.array E))) (i : Val C Γ .uint)
    (ref : SRef C (.ref (.array E))) (k : PrimTy.uint.Denote) (base : b.resolveT σ = .ok ref)
    (index : i.evalT σ = .ok k) (failed : (Checked.cmpU .lt rfl rfl i (.len b rfl)).evalT σ = .ok false),
    Checked.idxPG (.arr .dyn) b i = [(Panic.Site.bounds.code, Checked.cmpU .lt rfl rfl i (.len b rfl))] ∧
    Panic.Origin (.storageIndex σ.storage ref .dyn k) .bounds ∧ (Loc.index (.arr .dyn) b i).resolveT σ =
    .error .revert ∧ (panicStmt Panic.Site.bounds.code (Checked.cmpU .lt rfl rfl i (.len b rfl))).runR σ =
    .error (THalt.ofData (encodePanic Panic.Site.bounds.code))) ∧
  (∀ {E : Ty} {n : Nat} (σ : State C Γ) (b : SPath C Γ (.ref (.fixed E n))) (i : Val C Γ .uint)
    (ref : SRef C (.ref (.fixed E n))) (k : PrimTy.uint.Denote) (value : SVal (.ref (.fixed E n)))
    (range : PrimTy.uint.inRange (n : Int) = true) (base : b.resolveT σ = .ok ref) (index : i.evalT σ = .ok k)
    (found : σ.storage.find ref = some value)
    (failed : (Checked.cmpU .lt rfl rfl i (Checked.litU n range)).evalT σ = .ok false), Checked.idxPG
    (.arr .fixed) b i = [(Panic.Site.bounds.code, Checked.cmpU .lt rfl rfl i (Checked.litU n range))] ∧
    Panic.Origin (.storageIndex σ.storage ref .fixed k) .bounds ∧ (Loc.index (.arr .fixed) b i).resolveT σ =
    .error .revert ∧
    (panicStmt Panic.Site.bounds.code (Checked.cmpU .lt rfl rfl i (Checked.litU n range))).runR σ = .error
    (THalt.ofData (encodePanic Panic.Site.bounds.code))) ∧
  (∀ {E : Ty} (σ : State C Γ) (b : MPath C Γ (.ref (.array E))) (i : Val C Γ .uint) (ref : HRef σ.H (.array E))
    (k : PrimTy.uint.Denote) (base : b.mvalT σ = .ok ref) (index : i.evalT σ = .ok k)
    (failed : (Checked.cmpU .lt rfl rfl i (.mlen b rfl)).evalT σ = .ok false), Checked.mIdxPG .dyn b i =
    [(Panic.Site.bounds.code, Checked.cmpU .lt rfl rfl i (.mlen b rfl))] ∧ Panic.Origin
    (.index σ.heap ref .dyn k) .bounds ∧ (MPath.loc (.index .dyn b i)).mvalT σ = .error .revert ∧
    (panicStmt Panic.Site.bounds.code (Checked.cmpU .lt rfl rfl i (.mlen b rfl))).runR σ = .error
    (THalt.ofData (encodePanic Panic.Site.bounds.code))) ∧
  (∀ {E : Ty} {n : Nat} (σ : State C Γ) (b : MPath C Γ (.ref (.fixed E n))) (i : Val C Γ .uint)
    (ref : HRef σ.H (.fixed E n)) (k : PrimTy.uint.Denote) (range : PrimTy.uint.inRange (n : Int) = true)
    (base : b.mvalT σ = .ok ref) (index : i.evalT σ = .ok k)
    (failed : (Checked.cmpU .lt rfl rfl i (Checked.litU n range)).evalT σ = .ok false),
    Checked.mIdxPG .fixed b i = [(Panic.Site.bounds.code, Checked.cmpU .lt rfl rfl i (Checked.litU n range))] ∧
    Panic.Origin (.index σ.heap ref .fixed k) .bounds ∧ (MPath.loc (.index .fixed b i)).mvalT σ =
    .error .revert ∧
    (panicStmt Panic.Site.bounds.code (Checked.cmpU .lt rfl rfl i (Checked.litU n range))).runR σ = .error
    (THalt.ofData (encodePanic Panic.Site.bounds.code))) ∧
  (∀ {E : Ty} (σ : State C Γ) (b : SPath C Γ (.array E)) (ref : SRef C (.ref (.array E))) (keep : Bool)
    (base : b.resolveT σ = .ok ref)
    (failed : (Checked.cmpU .gt rfl rfl (.len b rfl) (Checked.litU 0 (by decide))).evalT σ = .ok false),
    (Stmt.pop b).panics = b.panics ++
    [(Panic.Site.emptyPop.code, Checked.cmpU .gt rfl rfl (.len b rfl) (Checked.litU 0 (by decide)))] ∧
    Panic.Origin (.pop σ.storage keep ref) .emptyPop ∧ (Stmt.pop b).runR σ = .error .revert ∧ (panicStmt
    Panic.Site.emptyPop.code (Checked.cmpU .gt rfl rfl (.len b rfl) (Checked.litU 0 (by decide)))).runR σ =
    .error (THalt.ofData (encodePanic Panic.Site.emptyPop.code))) ∧
  (∀ (σ : State C Γ) (c g : Val C Γ .bool) (failed : (Checked.orB (Checked.notB c) g).evalT σ = .ok false),
    c.evalT σ = .ok true ∧ g.evalT σ = .ok false)

/-- Clause (a), captures: the capture linkage and the guard order of `Correctness/Panic/Capture.lean`
(a failed operand read halts before any guard; a guard sees the captured value), and the elaborator's
own producers `narrowCheck`, `enumCapture`, `narrowCapture` and the `assert` arm. -/
def PanicCaptureSources : Prop :=
  (∀ {C : Contract} {Γ Γ' : Ctx},
  -- In order: `capture_linkage`, `capture_decl_halt`, `capture_guard_panic_run`, `enum_capture_panic_run`,
  -- `enum_capture_assert_run`, `uint_narrow_capture_origin`, `int_narrow_capture_origin`.
  (∀ (σ : State C Γ) (p : PrimTy) (name : Var) (value : Val C Γ p) (v : p.Denote)
    (_ : value.evalT σ = .ok v), ∃ out, (Stmt.declLocal p name (some value)).runR σ = .ok out ∧
    (Val.simple (.local Idx.here)).evalT out.st = .ok v) ∧
  (∀ (σ : State C Γ) (p : PrimTy) (name : Var) (value : Val C Γ p) (halt : THalt)
    (_ : value.evalT σ = .error halt), (Stmt.declLocal p name (some value)).runR σ = .error halt) ∧
  (∀ (σ : State C Γ) (p : PrimTy) (name : Var) (value : Val C Γ p) (v : p.Denote) (code : Nat)
    (guard : Val C (.val p :: Γ) .bool) (tail : Prog C (.val p :: Γ) Γ') (_ : value.evalT σ = .ok v)
    (_ : guard.evalT (σ.push (t := .val p) v) = .ok false),
    (Prog.cons (.declLocal p name (some value)) (.cons (panicStmt code guard) tail)).runR σ = .error
    (THalt.ofData (encodePanic code))) ∧
  (∀ (σ : State C Γ) (name : Var) (value : Val C Γ .uint) (v : PrimTy.uint.Denote) (members : Nat)
    (range : PrimTy.uint.inRange (members : Int) = true) (tail : Prog C (.val .uint :: Γ) Γ')
    (_ : value.evalT σ = .ok v) (_ : ¬v.val < (members : Int)), (Prog.cons (.declLocal .uint name (some
    value)) (.cons (panicStmt Panic.Site.enumConversion.code (cmpU .lt rfl rfl (.simple (.local Idx.here)) (litU
    members range))) tail)).runR σ = .error (THalt.ofData (encodePanic Panic.Site.enumConversion.code)) ∧
    Panic.Source.OriginV2 (.original (.enumConversion members v)) .enumConversion) ∧
  (∀ (σ : State C Γ) (name : Var) (value : Val C Γ .uint) (v : PrimTy.uint.Denote) (members : Nat)
    (range : PrimTy.uint.inRange (members : Int) = true) (tail : Prog C (.val .uint :: Γ) Γ')
    (_ : value.evalT σ = .ok v) (_ : ¬v.val < (members : Int)), (Prog.cons (.declLocal .uint name (some
    value)) (.cons (.assert (cmpU .lt rfl rfl (.simple (.local Idx.here)) (litU members range))) tail)).runR σ =
    .error .panic ∧ Panic.Source.OriginV2 (.original (.enumConversion members v)) .enumConversion) ∧
  (∀ (σ : State C Γ) (v : PrimTy.uint.Denote) (width : Nat) (_ : width < 256)
    (range : PrimTy.uint.inRange (((2 ^ width - 1 : Nat) : Int)) = true) (_ : (cmpU .le rfl rfl (.simple
    (.local Idx.here)) (litU ((2 ^ width - 1 : Nat) : Int) range)).evalT (σ.push (t := .val .uint) v) = .ok
    false), Panic.Source.OriginV2 (.narrowing (.unsigned width v)) .arithmetic) ∧
  (∀ (σ : State C Γ) (v : PrimTy.int.Denote) (width : Nat) (_ : width < 256)
    (lo : PrimTy.int.inRange (-((2 ^ (width - 1) : Nat) : Int)) = true)
    (hi : PrimTy.int.inRange ((2 ^ (width - 1) - 1 : Nat) : Int) = true) (_ : (andB (cmpI .le rfl rfl (litI
    (-((2 ^ (width - 1) : Nat) : Int)) lo) (.simple (.local Idx.here))) (cmpI .le rfl rfl (.simple (.local
    Idx.here)) (litI ((2 ^ (width - 1) - 1 : Nat) : Int) hi))).evalT (σ.push (t := .val .int) v) = .ok false),
    Panic.Source.OriginV2 (.narrowing (.signed width v)) .arithmetic)) ∧
  (∀ [FreshNames] (C : Contract),
    -- `narrowCheck_source`: three modes, no evaluation ahead of the full-width bypass.
    (∀ (p : PrimTy) (width : Nat) (expression : RawExpr), narrowCheck C p width expression = (do
      if 256 ≤ width then return []
      let Γ ← nctx
      let condition ← checkIn C Γ .bool (inTyCond p width expression)
      let scope ← read
      let data := scope.selfFrame || scope.retainFailureData
      pure [.of Γ (match (← read).overflow with
        | some mode => mode.guardStmt condition data
        | none => if data then panicStmt Panic.Site.arithmetic.code condition
                  else .require condition)])) ∧
    -- `enumCapture_source`: the operand is captured once, then the captured local is checked.
    (∀ (members : Nat) (expression : RawExpr), enumCapture C members expression = (do
      let Γ ← nctx
      let value ← checkIn C Γ .uint expression
      let name ← captureAs C "se" (.val .uint)
      let captured : RawExpr := .name (toString name)
      let Γ' ← nctx
      let condition ← checkIn C Γ' .bool (.binop .lt captured (.num members))
      let scope ← read
      let check := if scope.selfFrame || scope.retainFailureData then
        panicStmt Panic.Site.enumConversion.code condition else .assert condition
      pure ([.of Γ (.declLocal .uint name (some value)), .of Γ' check], captured))) ∧
    -- `assert_elab_source`: the `assert` arm, for an arbitrary `ElabRec`.
    (∀ (rc : ElabRec C) (c : RawExpr), elabStmt1With C rc (.assert c) = (do
      let Γ ← nctx
      if (← read).selfFrame || (← read).retainFailureData then
        return [.of Γ (.ite (← checkIn C Γ .bool c) .nil
          (.cons (.revertData [.bytes (Semantics.encodePanic 1)]) .nil))]
      pure [.of Γ (.assert (← checkIn C Γ .bool c))])) ∧
    -- `enumCapture_linked`, `narrowCapture_uint_linked`: the producers, run.
    (∀ (members : Nat) (e : RawExpr) (scope : ElabScope) (Γe : ECtx) (k : Nat)
      (value : Val C (ECtx.toNCtx Γe).ctx .uint) (_ : check C (ECtx.toNCtx Γe) .uint e = .ok value)
      (_ : checkFresh C Γe (toString (Var.fresh "se" k)) = .ok ())
      (range : PrimTy.uint.inRange (members : Int) = true), (enumCapture C members e).runFrom scope (Γe, k) = .ok
      (([.of (ECtx.toNCtx Γe) (.declLocal .uint (.fresh "se" k) (some value)), .of (ECtx.toNCtx ((toString
      (Var.fresh "se" k), .val .uint) :: Γe)) (if scope.selfFrame || scope.retainFailureData then panicStmt
      Panic.Site.enumConversion.code (cmpU .lt rfl rfl (.simple (.local Idx.here)) (litU members range)) else
      .assert (cmpU .lt rfl rfl (.simple (.local Idx.here)) (litU members range)))], .name (toString (Var.fresh
      "se" k))), ((toString (Var.fresh "se" k), .val .uint) :: Γe, k + 1))) ∧
    (∀ (e : RawExpr) (width : Nat) (scope : ElabScope) (Γe : ECtx) (k : Nat)
        (value : Val C (ECtx.toNCtx Γe).ctx .uint) (_ : checkedNarrow? C Γe e = some (.uint, width))
        (_ : width < 256) (_ : check C (ECtx.toNCtx Γe) .uint e = .ok value)
        (_ : checkFresh C Γe (toString (Var.fresh "se" k)) = .ok ())
        (range : PrimTy.uint.inRange (((2 ^ width - 1 : Nat) : Int)) = true),
      (narrowCapture C e).runFrom scope (Γe, k) =
        .ok (([.of (ECtx.toNCtx Γe) (.declLocal .uint (.fresh "se" k) (some value)),
               .of (ECtx.toNCtx ((toString (Var.fresh "se" k), .val .uint width) :: Γe))
                (match scope.overflow with
                 | some mode => mode.guardStmt
                     (cmpU .le rfl rfl (.simple (.local Idx.here)) (litU ((2 ^ width - 1 : Nat) : Int) range))
                     (scope.selfFrame || scope.retainFailureData)
                 | none => if scope.selfFrame || scope.retainFailureData then
                     panicStmt Panic.Site.arithmetic.code
                       (cmpU .le rfl rfl (.simple (.local Idx.here)) (litU ((2 ^ width - 1 : Nat) : Int) range))
                   else .require
                     (cmpU .le rfl rfl (.simple (.local Idx.here)) (litU ((2 ^ width - 1 : Nat) : Int) range)))],
              .name (toString (Var.fresh "se" k))),
            ((toString (Var.fresh "se" k), .val .uint width) :: Γe, k + 1))))

/-- Clause (b): the dispatch and self-call producers, for an arbitrary `rc`. The fallback of a call
through a function value is `Panic(0x51)` data exactly when `selfFrame || retainFailureData`, the bare
revert otherwise; `trySelfBodyWith` instruments (`withPanics`) exactly the bodies that are not compiler
getters; `receiveSelfBodyWith` instruments none. -/
def PanicDispatchProducers : Prop := ∀ [FreshNames] (C : Contract),
  -- `fnDispatchWith`: the chain's last arm, `fail`.
  (∀ (rc : PanicProducerRec C) (h ty : String) (args : List RawExpr) (res : Option (Var × PrimTy))
      (resW : Nat) (resNew : Bool), fnDispatchWith C rc h ty args res resW resNew = (do
    let some (ps, rs, ext) := fnParts? ty | throw s!"{h}: the function type {ty}"
    if ext then return ← rc.extDispatch h ty ps rs args res resW resNew
    unless ps.length == args.length do
      throw s!"{h} takes {ps.length} arguments, not {args.length}"
    if let some c := (ps.filter fun c => (fnRefElem? C c).isNone && (fnRefStruct? C c).isNone) ++ rs |>.find? fun c =>
        (fnCompTy? C c).isNone then
      throw s!"{h}(…): a function type with a {c} parameter or return is not modelled \
        (docs/semantic-gaps.md, \"Function types\")"
    let scope := (← read).funs
    let taken := fnTaken C
    let mut cands : List (String × Nat) := []
    for ((g, d), i) in C.funs.zipIdx do
      if fnInternal C g && FunDecl.sigTy? C d == some ty && fnReachable C g then
        if scope.any (·.1 == g) then cands := cands ++ [(g, i + 1)]
        else if taken.contains g then
          throw s!"{h}(…) may call {g}, which is not declared before this function: \
            declare the functions of type {ty} first"
    let (pre, tag, as) ← dispatchCaptures C (.name h) ty ps args
    let call (g : String) : RawStmt := match res with
      | some (x, _) => .assign (.name (toString x)) (.call g as)
      | none => .call (.name g) as
    let (Γ0, _) ← get
    if resNew then
      if let some (x, p) := res then declare C (toString x) (.val p resW)
    let P ← withReader (fun sc => { sc with top := false }) do
      let P ← rc.elabStmtsP pre
      let Γ ← nctx
      let fail : Stmt C Γ.ctx Γ.ctx :=
        if (← read).selfFrame || (← read).retainFailureData then .revertData [.bytes (Semantics.encodePanic 0x51)]
        else .revert
      let mut arms : List (DispatchArm C Γ.ctx) := []
      for (g, t) in cands do
        let c ← checkIn C Γ .bool (.binop .eqB tag (.num t))
        let body ← rc.elabScope Γ [call g]
        arms := arms ++ [{ cond := c, body := body.2 }]
      pure (P ++ [.of Γ (DispatchArm.chain arms fail)])
    modify fun (_, k) => (Γ0, k)
    pure P)) ∧
  -- `fnMemoryDispatchWith`: `failure`, the innermost `else` of the dispatch handed to `rc.elabStmtsP`.
  (∀ (rc : PanicProducerRec C) (h : RawExpr) (ty : String) (args : List RawExpr),
      fnMemoryDispatchWith C rc h ty args = (do
    let some (ps, [r], false) := fnParts? ty
      | throw "memory dispatch needs an internal signature with one memory return"
    let dstTy : RawTy ← if r == "bytesmemory" then pure (.named "bytes") else
      match fnRefElem? C r, fnRefStruct? C r with
      | some (e, false), _ => pure (.array (.named e))
      | none, some (st, false) => pure (.named st)
      | _, _ => throw s!"memory dispatch returns a {r}, not a memory reference"
    unless ps.length == args.length do
      throw s!"memory dispatch takes {ps.length} arguments, not {args.length}"
    if let some c := ps.find? fun c =>
        (fnRefElem? C c).isNone && (fnRefStruct? C c).isNone && (fnCompTy? C c).isNone then
      throw s!"memory dispatch: a function type with a {c} parameter is not modelled"
    let scope := (← read).funs
    let taken := fnTaken C
    let mut cands : List (String × Nat) := []
    for ((g, d), i) in C.funs.zipIdx do
      if fnInternal C g && FunDecl.sigTy? C d == some ty && fnReachable C g then
        if scope.any (·.1 == g) then cands := cands ++ [(g, i + 1)]
        else if taken.contains g then
          throw s!"memory dispatch may call {g}, which is not declared before this function"
    let (pre, tag, as) ← if args.isEmpty then do
        let t := toString (← freshCapture "se")
        pure ([.decl (.named ty) t (some h)], RawExpr.name t, [])
      else dispatchCaptures C h ty ps args
    let dst := toString (← freshCapture "mv")
    let P ← rc.elabStmtsP (pre ++ [.declMemory dstTy dst none])
    let failure := if (← read).selfFrame || (← read).retainFailureData then
        RawStmt.revertRaw (.bytesLit ((Semantics.encodePanic 0x51).map UInt8.toNat)) else RawStmt.revert
    let dispatch := cands.foldr (fun (g, t) rest =>
      RawStmt.ite (.binop .eqB tag (.num t))
        [.assign (.name dst) (.call g as)] [rest]) failure
    let Q ← rc.elabStmtsP [dispatch]
    pure (P ++ Q, .name dst))) ∧
  -- `fnTupleDispatchWith`: likewise.
  (∀ (rc : PanicProducerRec C) (ts : List (Option RawExpr)) (h ty : String) (args : List RawExpr),
      fnTupleDispatchWith C rc ts h ty args = (do
    let some (ps, rs, false) := fnParts? ty
      | throw s!"{h}(…): an external function value in a tuple assignment"
    unless ps.length == args.length do throw s!"{h} takes {ps.length} arguments, not {args.length}"
    unless rs.length == ts.length do throw s!"{h} returns {rs.length} values, not {ts.length}"
    if let some c := ps.find? fun c =>
        (fnRefElem? C c).isNone && (fnRefStruct? C c).isNone && (fnCompTy? C c).isNone then
      throw s!"{h}(…): a function type with a {c} parameter is not modelled"
    if let some c := rs.find? fun c => (fnCompTy? C c).isNone && !fnMemRet C c then
      throw s!"{h}(…): a function value returning a {c} among several values is not modelled \
        (a direct tuple call binds value and full-word memory returns)"
    let scope := (← read).funs
    let taken := fnTaken C
    let mut cands : List (String × Nat) := []
    for ((g, d), i) in C.funs.zipIdx do
      if fnInternal C g && FunDecl.sigTy? C d == some ty && fnReachable C g then
        if scope.any (·.1 == g) then cands := cands ++ [(g, i + 1)]
        else if taken.contains g then
          throw s!"{h}(…) may call {g}, which is not declared before this function: \
            declare the functions of type {ty} first"
    let (pre, tag, as) ← dispatchCaptures C (.name h) ty ps args
    let failure := if (← read).selfFrame || (← read).retainFailureData then
        RawStmt.revertRaw (.bytesLit ((Semantics.encodePanic 0x51).map UInt8.toNat)) else RawStmt.revert
    let dispatch := cands.foldr (fun (g, t) rest =>
      RawStmt.ite (.binop .eqB tag (.num t)) [.tupleAssign ts (.call g as)] [rest]) failure
    rc.elabStmtsP (pre ++ [dispatch]))) ∧
  -- `trySelfBodyWith`: `withPanics` exactly on a body that is not a compiler getter's.
  (∀ (rc : PanicProducerRec C) (g : String) {Γ : NCtx} (args : List (ExtArg C Γ.ctx)) (ρ : Ctx),
      trySelfBodyWith C rc g args ρ = (do
    unless fnExternalEntry C g do return none
    let some (_, d) := (← read).funs.find? (·.1 == g) | pure none
    unless d.params.map (·.2) == args.map (fun a => Ty.prim a.1) do return none
    unless d.rets.all (fun (_, T) => T matches .prim _) do return none
    let raw := args.map fun a => Simple.toRaw C Γ.names a.2
    let targets := !ρ.isEmpty || d.rets.isEmpty
    let r ← tryCatch (do
        let (P, _, _) ← rc.elabCallRet g raw none (targets := targets) (selfFrame := true)
        pure (some P)) fun _ => pure none
    let some [st] := r | pure none
    if h : st.Γ.ctx = Γ.ctx then
      let getter := d.sourceDecl.any fun source => match source.callable with
        | .getter _ => true
        | _ => false
      pure ((Stmt.selfCall? C ρ (h ▸ st.s)).map fun ⟨ps, Γf, sargs, sbody⟩ =>
        ⟨ps, Γf, sargs, if getter then sbody else sbody.withPanics⟩)
    else pure none)) ∧
  -- `receiveSelfBodyWith`: the inlined `receive`, no `withPanics`.
  (∀ (rc : PanicProducerRec C) {Γ : NCtx} (v : RawExpr), receiveSelfBodyWith C rc (Γ := Γ) v = (do
    let funs := (← read).funs
    let some (_, d) := funs.find? (·.1 == "receive") | pure none
    unless d.params.isEmpty && d.rets.isEmpty && d.mods.isEmpty do return none
    let receiveValueParam := "msgValue$"
    let pv := RawExpr.name receiveValueParam
    let ps : List (Name × Ty) := [(receiveValueParam, .prim .uint)]
    let d' : FunDecl := { d with params := ps, body := d.body.map (RawStmt.selfFrame pv) }
    let funs' := funs.map fun (n, e) => if n == "receive" then (n, d') else (n, e)
    let r ← tryCatch (do
        let nested : RawExpr := .name (receiveValueParam ++ "nested")
        let (P, _, _) ← withReader (fun sc => { sc with funs := funs', selfValue := nested })
          (rc.elabCallRet "receive" [v] none (targets := true) (selfFrame := true))
        pure (some P)) fun _ => pure none
    let some [st] := r | pure none
    if h : st.Γ.ctx = Γ.ctx then
      pure (Stmt.selfCall? C [] (h ▸ st.s))
    else pure none)) ∧
  -- Transfer to the public producers and to the callbacks of `elabRec` (the knot's own record).
  (∀ (h ty : String) (args : List RawExpr) (res : Option (Var × PrimTy)) (resW : Nat) (resNew : Bool),
    fnDispatch C h ty args res resW resNew =
      fnDispatchWith C (panicProducerRec C ()) h ty args res resW resNew ∧
    (elabRec C ()).fnDispatch h ty args res resW resNew = fnDispatch C h ty args res resW resNew) ∧
  (∀ (h : RawExpr) (ty : String) (args : List RawExpr),
    fnMemoryDispatch C h ty args = fnMemoryDispatchWith C (panicProducerRec C ()) h ty args ∧
    (elabRec C ()).fnMemoryDispatch h ty args = fnMemoryDispatch C h ty args) ∧
  (∀ (ts : List (Option RawExpr)) (h ty : String) (args : List RawExpr),
    fnTupleDispatch C ts h ty args = fnTupleDispatchWith C (panicProducerRec C ()) ts h ty args) ∧
  (∀ (g : String) {Γ : NCtx} (args : List (ExtArg C Γ.ctx)) (ρ : Ctx),
    trySelfBody C g args ρ = trySelfBodyWith C (panicProducerRec C ()) g args ρ ∧
    (elabRec C ()).trySelfBody g args ρ = trySelfBody C g args ρ) ∧
  (∀ {Γ : NCtx} (v : RawExpr),
    receiveSelfBody C (Γ := Γ) v = receiveSelfBodyWith C (panicProducerRec C ()) (Γ := Γ) v) ∧
  -- The fallback's run: when no arm's guard holds, whatever the tag, the data arm emits exactly
  -- `Panic(0x51)` and the other arm is V1's bare revert. No premise restricts the tag.
  (∀ {Γ : Ctx} (arms : List (DispatchArm C Γ)) (σ : State C Γ),
    (∀ arm ∈ arms, arm.cond.evalT σ = .ok false) →
    (DispatchArm.chain arms (.revertData [.bytes (encodePanic 0x51)])).runR σ =
      .error (THalt.ofData (encodePanic 0x51)) ∧
    (DispatchArm.chain arms .revert).runR σ = .error .revert) ∧
  -- Tag boundary: `0x51` is the zero-function site's code; only the zero tag has that intrinsic origin.
  Panic.Site.zeroInternalFunction.code = 0x51 ∧
  (∀ tag : PrimTy.uint.Denote, tag.val = 0 → Panic.Origin (.internalFunction tag) .zeroInternalFunction)

/-- **Source association of the panic producers**: clauses (a) and (b). -/
@[goal Solidity.Correctness.Panic.source_association "w3d-panic-dispatch"]
def panicSourceAssociation : Prop :=
  PanicGuardSources ∧ PanicCaptureSources ∧ PanicDispatchProducers

end Solidity.Goals
