# Making the model intrinsic

Plan of record for branch `intrinsic` (started 2026-10-07): locals scoped in
the syntax (`Stmt C Γ Γ'`, positional `Idx`), a state typed by its context,
an interpreter with no `stuck`, a compiler total on typed syntax, and the
calculus and closer over typed formulas. Trimmed to a module-map entry at M7.

## Decisions (user, 2026-10-07: "implement all of them")

1. If a speed gate (G0, M6a) fails, the calculus takes Church-typed program
   variables (KeY's `\programVariables`); every other layer stays intrinsic.
2. Locals are block-scoped (popped at the end of `if`/loop/`try`/block), as
   solc; each changed behaviour gets a `docs/solc-alignment.md` row.
3. `uint` values are `{n : Int // p.admits n}` (keeps 56642ee's kernel path).
4. Storage is typed (`SVal : Ty → Type` over `structDef`, M4b).
5. The SolKey reader (side-projects `lean/solkey`) is regenerated on a branch
   there when M6a breaks it.
6. The closer and Decide are ported (M6c); `Fml.erase` is a bridge only.
7. All milestones run; a failed gate takes its stated fallback, not a stop.
8. The bridge (typed `Core` beside the untyped `Stmt`) ends at M4, not M7.

## Milestones

| # | Status | Work |
|---|---|---|
| M0 | | baselines + scratch spike, gate G0 |
| M1 | done | stuck causes that need no index; the elaborator runs the locals check (`wtCheck`) |
| M2 | | `Ctx`/`Idx`/`Thin`, typed `Core` syntax, `resolve` |
| M3 | | `Env Γ`, `State C Γ`, typed run; delete the locals checker |
| M4 | | typed values, storage, heap; delete `stuck`; retire old `Stmt` |
| M5 | | EVM on typed syntax; delete `wtStmt`, `not_stuck` |
| M6a | | calculus: `Fml C Γ`, `Frames`, `Premise`, symex, chains, ProofTree |
| M6b | | `dl!{}`, specs, callbacks |
| M6c | | closer and Decide on typed `Fml` |
| M7 | | cleanup, docs, rule-map rows, review pass |

### M1 notes

- (a) `**` with a negative exponent, and `transfer`/`send` (and the update
  element `.pay`) of a negative amount, revert.  `Simple.lit` carries
  `PrimTy.inRange` (`AST.lean`; `PrimTy.admits` was taken, a `Value`
  predicate in `Update.lean`), discharged by `rfl` in quotes and by
  `litAt` in the elaborator; `Evm.wtSimple` admits every literal.  The
  storage builder writes literals now, so `canon_reachable`/`reachable_iff`
  (`Typing/Constructibility.lean`) and `shape_iff_reachable`/
  `wt_iff_reachable` (`Calculus/Problem.lean`) take `FitsStorage` (every
  word, key and slot in range); `reachable_shape`, `shape_of_reachable`
  and `wt_of_reachable` are the unconditional directions.
  `uint_negative_reachable` is gone (its program no longer elaborates).
- (b) `R.memOk` is `(Ty.ref R).mapFree`, as `MRhs.copy` already used:
  `MPath.var` and `Stmt.declMem` carry it; `deleteMem` needs no field,
  since `MPath.mapFree` derives it for every memory path.  `allocDefault`
  keeps its stuck arm: the closer's `.alloc R`/`.addM R` terms reach it at
  an untyped `R` (to go at M4c).  In the `dl{}` macro a memory local's
  proof is the auto-bound `hmv` (`proofIdent`), a declared one's
  `MRhs.mapFree r`; this moves a struct name before the member name in some
  taclets' implicit binders (`Examples/Notation.lean` pins,
  `SortCheck/Faithfulness.lean`), which the SolKey reader's `GenProved`
  must be regenerated for.
- (c) The seven captures that did not declare their local now do
  (`captureAs`): `elabOpTarget`'s `ie` (two), `elabIncTarget`'s `sp`/`mv`
  (four), `elabSize`'s `se`.  The rest declare it already: `hoist`'s call
  captures after the call, a callee's renamed locals, loop flags and
  modifier parameters when their raw declaration is elaborated, a call's
  arguments and return variables in the callee's own context (`Γf`).
- (d) A storage conditional of references is
  `T storage sp1; if (c) { sp1 = a; } else { sp1 = b; }` (`hoist`; the
  `Syntax.lean` pin).  A memory one still declares its `mv` in each branch:
  `T memory mv1;` would allocate, so it waits for M2's scoped branches.
- (e) `Binding.unset`: `declStorage R x none` binds it, `aliasPath` reverts
  on it.  `storageLocalDeclSkip` is `T storage lsv; ⇝ {lsv := unset} ⟨[ ]⟩`
  (`UpdElem.unset`, printed and read as `lsv := unset`, a keyword in
  `dl!{}`; rule-map deviation row, solc-alignment row).  `Stmt.wt` adds
  `x` at its alias type (`BTy.matchesB` accepts `unset`), the EVM forgets
  it (`Sim.unbind`), and Decide carries it as `SymB.unset`, a read through
  it outside the fragment.  Pins changed: the `Syntax.lean` conditional
  pin and the `StorageCoverage.storageLocalDeclSkip` chain's last line
  (`{ acc := unset } φ`); no `#guard_msgs` output changed.
- (f) `BTy`, `Ctx` and the locals check (`Stmt.wt`, `Prog.wt`, each part's
  `wt`) moved from `Typing/State.lean`/`Typing/Soundness.lean` into
  `Syntax.lean`, below the printer; `Soundness.lean` keeps the theorems.
  `wtCheck` (`Prog.wtFirst`, an error naming the statement) runs in
  `elabProg`/`elabProgAt` (so `sol[C]{}`, `solc_import`, `ctorProg`,
  `Tools/Run`), at a spec's and a constructor problem's call
  (`specPieces`, `Problem.ctor`) and per statement in a `dl!{}` modality,
  from the elaborator's locals (`ECtx.toCtx`).  An `if` now leaves
  `Ctx.join`: the locals both branches declare alike, which the memory
  conditional of references' `mv1` needs (`Ctx.le_join_thn`/`_els` in the
  two `ite` cases, `Soundness.lean`, `Reachability.lean`).  All 449
  TestSuite functions, the corpus and every example pass.  A block's local
  retyped by a later branch (`{ bool x = true; } if (c) { uint x = 1; }`)
  is now an elaboration error (pinned in `Examples/Tactics/Branch.lean`),
  until M2's scoped locals.  Timing (profiler, before → after): the
  TestSuite `solc_import` 1.69 s → 1.71 s, `TestSuite/Derived3.lean`
  (cumulative type checking) 17.1 s → 17.0 s, `Examples/Tactics/Branch.lean` unchanged (each
  declaration within 10 ms).

## Baselines (M0)

(filled by M0)

## Design (from the scoping review, design 3 "staged core")

END STATE (names after the final rename; during migration the typed families live in `namespace Solidity.Core`, and today's `Stmt C` stays as the elaborator's output IR plus the erasure target).

-- AST.lean, merging ECtx/LocalTy (Syntax.lean:2134-2145), BTy/Ctx (Syntax.lean, the locals check) and Evm LTy (Compile.lean:434)
inductive LTy | val (p : PrimTy) | alias (R : RefTy) | mem (R : RefTy) | old | oldNet
abbrev Ctx := List (Var × LTy)              -- innermost first; the Var is a printing label only
inductive Idx : Ctx → LTy → Type            -- data, positional (de Bruijn index)
  | here  : Idx ((x, t) :: Γ) t
  | there : Idx Γ t → Idx ((y, u) :: Γ) t
inductive Thin : Ctx → Ctx → Type           -- order-preserving embedding (scope end / weakening)
  | done : Thin [] []
  | keep : Thin Γ Δ → Thin (b :: Γ) (b :: Δ)
  | drop : Thin Γ Δ → Thin Γ (b :: Δ)
def Idx.name : Idx Γ t → Var                 -- for #wp, pins and FreshNames printing

-- Syntax.lean: every family threads Γ
inductive Simple (C) (Γ : Ctx) : PrimTy → Type
  | lit (n : Int) (h : p.admits n = true) | bool (b : Bool)
  | local (i : Idx Γ (.val p)) | env (k : EnvKey) (hp : p = .uint)
SPath C Γ T (.alias (i : Idx Γ (.alias R))), Loc C Γ T, MPath C Γ T (.var (i : Idx Γ (.mem R)) (hm : R.memOk = true)),
MLoc/Val/Src/ARhs/MRhs/NewLhs/MSrc/OpLoc/ExtCall/LoopAnn C Γ …   -- Γ threaded, nothing else changes
mutual
inductive Stmt (C) : Ctx → Ctx → Type
  | assignLocal (i : Idx Γ (.val p)) (r : Val C Γ p) : Stmt C Γ Γ
  | rebind (i : Idx Γ (.alias R)) (r : ARhs C Γ R) : Stmt C Γ Γ
  | declLocal (x : Var) (p : PrimTy) (init : Option (Val C Γ p)) : Stmt C Γ ((x, .val p) :: Γ)
  | declStorage (x : Var) (R : RefTy) (init : Option (ARhs C Γ R)) : Stmt C Γ ((x, .alias R) :: Γ)
  | declMem (x : Var) (R : RefTy) (hm : R.memOk = true) (init : Option (MRhs C Γ R)) (hd : …) : Stmt C Γ ((x, .mem R) :: Γ)
  | ite (c : Val C Γ .bool) (thn : Prog C Γ Γ₁) (els : Prog C Γ Γ₂) : Stmt C Γ Γ        -- branches scoped
  | loop (a : LoopAnn C Γ) (c : Val C Γ .bool) (body : Prog C Γ Γ₁) : Stmt C Γ Γ         -- popped per iteration
  | call (f : Name) (args : Args C Γ ps) (ret : CallRet C Γ rs Γ') (body : Prog C (rs ++ ps) Γf) : Stmt C Γ Γ'
      -- body closed over its own frame; no hsep/Arg.separatedFrom; ret exports CallRet.rets / mv into Γ'
  | tryCall (e : ExtCall C Γ) (rets : Binders ρ) (ok : Prog C (ρ ++ Γ) Γ₁) (err : Prog C Γ Γ₂)
      (code : Binders κ) (pnc : Prog C (κ ++ Γ) Γ₃) (other : Prog C Γ Γ₄) : Stmt C Γ Γ
  | … the other 20 constructors as today, at Stmt C Γ Γ, with Idx in place of Var
inductive Prog (C) : Ctx → Ctx → Type
  | nil : Prog C Γ Γ
  | cons (s : Stmt C Γ Γ₁) (P : Prog C Γ₁ Γ₂) : Prog C Γ Γ₂   -- output index always a variable: no `++` in constructor results
end
def Prog.thin : Prog C Γ Γ' → Thin Γ Γ'            -- structural, used to pop scopes
def Stmt.wk  : Thin Γ Δ → Stmt C Γ Γ' → Σ Δ', Stmt C Δ Δ'   -- used only on a found statement's own schema variables and once per call expansion

-- Semantics.lean
def LTy.Denote (C) : LTy → Type   -- val p ↦ p.Denote (Bool | {n : Int // p.admits n}); alias R ↦ Option (Path C (.ref R)); mem R ↦ HRef R; old ↦ Storage C; oldNet ↦ Ledger
inductive Env (C) : Ctx → Type | nil : Env C [] | cons (v : t.Denote C) (e : Env C Γ) : Env C ((x, t) :: Γ)
def Env.get : Env C Γ → Idx Γ t → t.Denote C ;  def Env.thin : Thin Γ Δ → Env C Δ → Env C Γ
structure State (C) (Γ : Ctx) where storage : Storage C; heap : Heap C; env : Env C Γ; net; selfBalance; tx
  -- Storage C: HList over C.vars of SVal T (mutual SVal/SFields indexed by Ty via structDef); Heap C: positional typed objects
inductive Halt | revert | panic | diverge          -- `stuck` deleted at M4
def Stmt.run : State C Γ → Stmt C Γ Γ' → Except Halt (State C Γ')
def Prog.run : State C Γ → Prog C Γ Γ' → Except Halt (State C Γ')

-- Calculus: solkey's `c# … #c` as data
inductive BlockKind | block | capture               -- `}` printed, or invisible (a Lean-only scope end for fresh se/sp/ie)
inductive Frames (C) : Ctx → Ctx → Type
  | nil : Frames C Γ Γ
  | seq (ω : Prog C Γ Γ₁) (k : Frames C Γ₁ Γ₀) : Frames C Γ Γ₀
  | pop (b : BlockKind) (h : Thin Γ Γ') (k : Frames C Γ Γ₀) : Frames C Γ' Γ₀
inductive Upd (C) : Ctx → Ctx → Type                 -- assigning elements Γ→Γ, declaring elements Γ→(x,t)::Γ
inductive Fml (C) : Ctx → Type
  | modal (m : Modality) (P : Prog C Γ Γ₁) (k : Frames C Γ₁ Γ₀) (φ : Fml C Γ₀) : Fml C Γ
  | upd (m) (U : Upd C Γ Γ') (φ : Fml C Γ') : Fml C Γ
  | all (x : Var) (p : PrimTy) (φ : Fml C ((x, .val p) :: Γ)) : Fml C Γ | anon (xs : List (Σ t, Idx Γ t)) (φ : Fml C Γ) | …
inductive Premise (C) (Γ Γ' : Ctx)
  | update (U : Upd C Γ Γ') | unfold (P : Prog C Γ Γ'') (h : Thin Γ' Γ'')   -- fresh captures dropped by `pop .capture h`
  | bind (x : Var) (t : LTy) (P : Prog C ((x,t)::Γ) Γ')                         -- `T v = e; ⇝ v = e;` (binder printed invisibly)
  | split (c c' : Fml C Γ) (P : Prog C Γ Γ₁) (Q : Prog C Γ Γ₂)                 -- no cover goal: conditions cannot be stuck
  | …
def Premise.fml : Premise C Γ Γ' → Frames C Γ' Γ₀ → Fml C Γ₀ → Fml C Γ
  -- .unfold P h, k, φ ↦ .modal m P (.pop .capture h k) φ   : ω is never re-typed
inductive Taclet (C) (k : Nat) : Modality → Stmt C Γ Γ' → Premise C Γ Γ' → Prop   -- k only names fresh vars (se1, sp1)
inductive Hyps (C) : Ctx → Ctx → Type                -- telescope: `{U}` and `∀` hypotheses extend scope
inductive Proves : RuleSet → Hyps C [] Γ → Fml C Γ → Prop

-- Evm
abbrev Machine.mem := Nat → Word                     -- local i at level Γ.length - 1 - i
def compileStmt : Stmt C Γ Γ' → List Instr           -- total; frame for a call at levels Γ.length…
def inFrag : Frag Γ → Stmt C Γ Γ' → Option (Frag Γ') -- fragment + fragile aliases only; no scoping conjuncts
theorem compile_correct : inFrag F P = some F' → Sim C F σ m → … (no `not_stuck`: Halt has no stuck)

-- Checker from the existing frontends (kept as the elaborator back end)
def Stmt.resolve (Γ : Ctx) : Syntax.Stmt C → Except String (Σ Γ', Core.Stmt C Γ Γ')   -- Var ↦ Idx by lookup, scopes explicit
theorem resolve_erase : resolve Γ u = .ok ⟨Γ', s⟩ → s.erase = u
theorem run_erase : (s.erase).run σ.erase = (s.run σ).map State.erase  -- modulo EnvAgreeExcept on popped locals; the M2–M6 bridge
---WHAT STAYS
These stay extrinsic, on purpose.

1. **The EVM fragment and fragile aliases** (`inFrag`, `Frag Γ`; Compile.lean:461-566, 449). This is a fact about the compiler target, not a typing fact:
   - `pop`/`delete` leave the Solidity context unchanged (Γ' = Γ) but kill aliases on the EVM side (Correctness.lean:736, 1154).
   - Literal ranges, `binInFrag`, `static`, `wtPush`, and "no memory/send/try/loop" would otherwise either restrict the source language for every layer or need a second copy of the syntax (`FStmt`) with an erasure proof.
   - `compileStmt` is already total. Only `compile_correct` keeps the fragment hypothesis.

2. **Function and modifier bodies in `Contract`** stay `RawStmt` (Syntax.lean:245-276). A typed body would make `Contract` contain `Stmt C`, which is indexed by `C`. The elaborator stays the only checker of declared bodies; each call site's `Stmt.call` body is typed.

3. **Taclet soundness and closer completeness** are theorems by nature (`Taclet.sound`, `Fml.valid_iff_reduce`). The closer's `LFml` is a decision-procedure IR reached by a sound reflection. It is ported last (M6c), and only if its gate passes.

4. **Storage canonicity beyond shape** stays a lemma: map-key uniqueness, a default being a default (Reachability `canon`), and `tight` (Constructibility). Making it intrinsic needs sorted or functional maps, which would undo what `decide +kernel` over association-list stores relies on (Semantics.lean:958-1100, 977-985).

5. **Definite assignment of `T storage p;`.**
   - `LTy.alias R` denotes `Option (Path …)`, and reading an unset alias reverts. solc rejects such reads statically, so no solc-accepted run reaches it.
   - A flow-sensitive "unset" index would need a context meet at every `ite` join. That collides with `ifElseSplit`, whose branches continue into the same ω.
   - It is listed as an optional refinement, not a milestone.

6. **The elaborator's narrow integer widths** (`LocalTy.val p bits`, `fitCheck`/`narrowPost`) stay elaborator-only until `PrimTy` gains widths. That is a language change, not a scoping one.

7. **Divergence** (`Loop.run` via `Classical.choose`, Semantics.lean:1620-1630) is semantics, not typing, and stays.

8. **Fresh-name numbering** (`Taclet C k`, `Hyp.fresh`/maxIdx, Logic.lean:311) is kept only to print `se1`/`sp1` the same way, so pins don't change. It carries no soundness obligation: names are labels on a positional context, so shadowing is harmless.

9. **Fallback if the M0 gate fails** for the calculus: the calculus stops at Church-typed program variables (`Var` carrying its `LTy`, a total typed env, KeY's `\programVariables`). Every other layer is still intrinsic, and only declare-before-use inside formulas stays extrinsic. This matches KeY, where program variables are global.
---
M0 (risk first, 3-5 days, nothing merged except a doc row). Record the baselines that every later milestone is gated on:
- `TestSuite/Derived9-11` (20.2 s, docs/testsuite-proofs.md:1400) and the whole `SolkeyTestSuite`;
- `Examples/ProofTree.lean` (50 `#guard_msgs`) and `Examples/Chains` (188 theorems, 623 links);
- `./scripts/check-corpus.sh`;
- `Evm/Correctness.lean` (stmt_sim at `maxHeartbeats 470000`, :1996) and `Evm/Examples.lean` (21 decide/rfl).

Then build a spike in `Solidity/Scratch/` (never committed): `Idx`/`Thin`/`Env`, six `Stmt C Γ Γ'` constructors, `Frames`, one capture taclet (`storageFieldRead_unfold_rightFst` with `pop .capture`), `ifElseSplit` with `pop .block`, a compiled `symex` with a hand quoter, and kernel `rfl` on a 40-statement program, against the same toy without indices.

Gate G0, to proceed with the positional Idx design:
- kernel check at most 1.3× and quoted Expr size at most 2×;
- no `Meta.reduce` fallback is hit;
- `cases` on `Prog C Γ Γ'` works without generalisation.

If G0 fails, retry with named `lookupBy` Bool witnesses (the c26d16e^ Kernel style). If that fails too, the calculus takes the Church-typed fallback.
M1 (semantic debt, current representation, 1-2 weeks, merge). Remove the stuck causes that need no index.
(a) A negative `**` exponent (Semantics.lean:802, 838) and a negative transfer/send amount (:1471, :1485) revert. `Simple.lit` gets `(h : p.admits n = true)`, the EVM's literal range moved into the syntax.
(b) `R.memOk` proof on `declMem`/`deleteMem`/`MPath.var`, closing the mapping-in-memory hole (`allocDefault` stuck at :674-682).
(c) In the elaborator, `declare` every `freshCapture` (Syntax.lean:2700, 2707, 2724-2729, 2752, 3627).
(d) Lower the reference ternary (hoist :3451-3463) to `T storage sp1; if (c) { sp1 = a; } else { sp1 = b; }`.
(e) Add `Binding.unset`: `declStorage R x none` binds it, and a read of it reverts. `storageLocalDeclSkip` (Rules.lean:336) gets a rule-map deviation row.
(f) The elaborator self-checks `Prog.wt Γparams P` at every `sol{}`/`solc_import`/`spec!` site. The two TestSuite programs (Derived3:69, Derived7:67) and Branch.lean:236-245 must pass.

Gate: pins unchanged except the deviation row, and TestSuite time within 5%.
M2 (typed syntax plus checker, 2-3 weeks, merge). Add `LTy`/`Ctx`/`Idx`/`Thin` to AST.lean and the `Core.*` families to a new `Syntax/Core.lean` (registered in Solidity.lean).
- `Core.Stmt.erase`, `Stmt.resolve`, `resolve_erase`.
- `Core.Prog.quote` (Idx as `.here`/`.there`, no proofs to synthesise except `admits`/`memOk`, which are `Eq.refl`).
- Typed `Stmt.call`, with args closed and the body at `rs ++ ps`. resolve un-inlines the renamed callee locals to frame positions, using `CallRet` and the elaborator's `Γf` at :3655.
- Scoped `ite`/`loop`/`tryCall`/block.

A lint test runs `resolve` on all 449 imported functions and on every `sol{}` site (compiled, through `#guard`).

The bridge rule: `Core.*` and the untyped `Stmt` coexist only until M7, with a dated row in docs/kernel-port.md. This is the one deliberate exception to 'replace in place'; the old Kernel/ was deleted because it lingered. Gate: elaboration time of the sol{} sites within 10%.
M3 (typed interpreter over the locals, 2-3 weeks, merge).
- `Core.State C Γ` with `Env C Γ` (storage and heap still untyped in this milestone), and `Core.Stmt.run`/`Prog.run` with scope pops via `Prog.thin`.
- `run_erase` against `Stmt.run`, modulo `EnvAgreeExcept` on popped locals, reusing Semantics/Agree.lean.
- `Stmt.wt`/`Prog.wt`/`Ctx.has`/`EnvWT` (Syntax.lean's locals check; Soundness.lean) become corollaries of resolve plus run_erase, then are deleted.
- `Stmt.run_wt` is restated as `Core.Stmt.run` preserving the RunWT remainder (storage, heap, heapWf).
- `Reachable` (Reachability.lean:1814) is redefined over `Core.Prog C [] Γ'`. Problem.lean:131/140/169 statements are unchanged.
- The Constructibility builder (:91-183) emits `Core.Prog` (`fill : … → Σ Γ', Core.Prog C Γ Γ'`), and KeepΓ (:990-1202) disappears.

Gate: the Typing build within 20%, and nothing on the calculus path changes.
M4 (typed values, storage and heap, 4-6 weeks, merge in three PRs).
- **4a: `PrimTy.Denote`.** This removes cause B (asInt/asBool, pickBranch, guardOk, the junk arms of checkArith :873-876). uint is `{n : Int // p.admits n}`, with arithmetic still on Int literals, so the kernel never unfolds `Nat.land` (keeps 56642ee).
- **4b: `SVal : Ty → Type`.** It is mutual with `SFields` over `structDef` (exact members by construction), `Storage C` is an HList over `C.vars`, and paths are `Path C T T'`. This removes cause C: find/save/checkIndex/arrayLen/push/pop/copyStToM's map arm. `defaultForTy` gets a structRank-structural definition so the kernel reduces it.
- **4c: a positional typed heap.** `HeapTy.Extends` becomes a returned `Thin`-like extension. `copyMToSt` recurses on Ty, which removes the cycle arm at :710. This removes cause D.

At the end of 4c, `Halt.stuck` is deleted from `Core`. The untyped side keeps its stuck through `run_erase`.

Gates: Corpus `decide +kernel` and the 8 concrete stores (Semantics.lean:958-1100) within 20%. No whnf timeouts on structDef: per-contract stores stay named constants.
M5 (EVM on Core, 2-3 weeks, merge).
- `Machine.mem : Nat → Word` is level-addressed; the 14 `mload`/`mstore` sites compute `Γ.length - 1 - i`.
- `Sim C F σ m` becomes `∀ i : Idx Γ (.val p), ReprV p (σ.env.get i) (m.mem (level i))`.
- `Sim.bindVal`/`bindAlias`/`bindFragile`/`weaken` (Correctness.lean:1052-1160) become `Env.cons` plus a `Thin` restriction.
- `wtStmt` loses its scoping conjuncts and becomes `inFrag : Frag Γ → Stmt C Γ Γ' → Option (Frag Γ')`.
- `not_stuck` (:2460) and `never_stuck` (Theorems.lean:236) are deleted, since the type proves them. The ReprV `_inv` lemmas (:182-200) go.

Gate: `stmt_sim` must pass at 470000 heartbeats or less (AGENTS forbids raising it), and the Evm/Examples decide examples within 20%.
M6a (calculus cutover at the modality boundary, 6-10 weeks, the largest milestone, its own worktree lane).

Typed `Upd C Γ Γ'`, `Fml C Γ` with `Frames`, `Hyps`, `Premise C Γ Γ'`, and `Taclet C k m (s : Core.Stmt C Γ Γ')`. The dl{} macro (RuleSyntax.lean `schemaAt`/`declVar` :600-657) inserts two things itself, so every rule line in Rules.lean stays textually the same:
- `↑` on the found statement's schema variables reused after a capture;
- `pop .capture` for the 54 fresh-declaring rules.

Other rule changes:
- `ifElseSplit` continues into `pop .block`, which lets the table claim solkey's `blockEmpty`. A call's frame claims `functionFrameEmpty`/`functionBodyExpand`, shrinking `RuleShapes.unclaimedTaclets` (:482).
- `localValueDeclInitDrop`/`storageLocalDeclInitDrop`/`memoryLocalDeclInitDrop` use `Premise.bind`, printed as solkey's `⟨[ v = e; ]⟩`.
- `Premise.coverFml` and the `cov` goal (Logic.lean:41, 67) are deleted, giving KeY's two goals.

In this milestone, `Stmt.step`, `Fml.stepAt`, `symex`, the quoters, chains (program links), `Derive.residue` and ProofTree move to Core. The post-modal closer keeps working through `Fml.erase : Fml C Γ → Legacy.Fml C` and one lemma, `holds_erase`.

The SolKey reader breaks here, because LeanShape matches `Stmt.*` arities. It needs the user's go-ahead before regenerating GenProved on a branch in side-projects.

Gate (hard stop): Derived9-11, the chains, and Examples/ProofTree within 20% of M0. Repin the pins once, for `cov` removal and block printing.
M6b (formula-level frontends, 2-3 weeks).
- The dl!{} reader (Notation.lean `elabUpd` :858, `scopeHints` :932-990) produces exact Γ, with default-uint free names as explicit outer `Fml.all`.
- `Post C Γ₀`, so no weakening of φ is ever needed.
- Problem.fml/Spec.lean:478/Frontend/Problems.lean bind parameters as the context.
- spec `old`/`oldNet` get `LTy.old`/`.oldNet`.
- Callbacks: `ExecS I : State C Γ → Stmt C Γ Γ' → COut Γ'`. `iteStuck`/`loopStuck` (Semantics/Callback.lean:168, 224) and the `hI : I.vars = []` hypotheses are deleted, replaced by `Invariant.fml : Fml C []`. `havoc` ranges over typed `Storage C`.
M6c (closer port, optional, behind a gate, 4-8 weeks). Move Close/ReadWrite/UpdateRules/StateParts/Decide*/Closer/ChainRewrites (about 25k lines, about 650 env-API references) from `Legacy.Fml` to typed `Fml C Γ`, module by module, keeping `Fml.erase` until the last module.

If any module is more than 20% slower, it stays on the erased form permanently, and the reflection is documented as the decision procedure's IR.
M7 (cut-over cleanup, 2-3 weeks).
- The elaborator emits Core directly, or keeps today's Stmt as a private IR feeding `resolve`. Pick whichever M2's timings favour.
- Delete untyped `Stmt.run`, `run_erase`, `Typing/Soundness` wt/run_wt, and Semantics/Agree's fresh-name lemmas, which have no users left now that freshness is positional.
- Rename `Core.Stmt` → `Stmt`.
- Run `check-orphans`, `check-doc-paths`, `solkeycheck` and `check-testsuite`.
- Update docs: module-map.md:148, loops.md:116/120/288, solc-validation.md:26/324 (whose 'not stuck' claim becomes true), lean-key-rule-map.md rows for blockEmpty/functionFrameEmpty/capture pop/unset alias.
- Run the read-only review pass (finder plus skeptic per area).
---RISKS
Speed (AGENTS warning, before any edit): this reverses the design choice of 6c174cc/c26d16e. Syntax.lean:17-21 and Typing/Soundness.lean:9-13 kept locals unscoped so that rules could declare se1/sp1 without re-typing ω. The old Γ-indexed port recorded that Meta.reduce through indexed families is about 100× slower, that `cases` fails with 'dependent elimination failed', and that an inner match does not refine indices (c26d16e^:docs/kernel-port.md:214-227). No commit removed the index for measured speed, but it does touch the paths made fast by 7541cad (quoted symex), 2ff6a0f (nospecialize, runCache) and 02f363b (sol_prove by one kernel evaluation). The `pop .capture` frame is the design's answer to the 6c174cc rationale, and M0 must confirm it before anything merges.
The bridge period (M2-M7) has a typed Core beside the untyped Stmt. That conflicts with the 'replace in place, not beside' memory, and the old Kernel/ was deleted for lingering. Mitigation: a dated deletion row, and `run_erase` as the only bridge theorem. If M6a stalls, two syntaxes live on.
Rule fidelity:
- `pop .capture` frames and the invisible binder of `Premise.bind` are Lean-only scope markers, so printers must hide them for `#taclet`/PrintedRules/ProofTree pins to keep solkey's `\find`/`\replacewith` shape. Each needs a rule-map row.
- `storageLocalDeclSkip` (`T storage lsv; ⇝ ⟨[]⟩`) becomes `{lsv := unset}`, a visible deviation.
- On the other side, `blockEmpty`/`functionFrameEmpty`/`functionBodyExpand` become claimed (RuleShapes.lean:450-482), and the `cov` goal (not in KeY) disappears.
The SolKey reader (side-projects lean/solkey) depends on Taclet constructor names and arities and on `Stmt.*` arity in LeanShape. M6a breaks its 590-reference generated `Corresp/Proved.lean`. Regenerating it requires the user's explicit go-ahead (memory: do not touch the side-projects reader unless asked).
Semantic change: scoped blocks and loops pop locals, and today they outlive the branch. This follows solc (≥0.5 C99 scoping) but changes `ifElseSplit`'s continuation (now through a pop frame), loop frames (`Prog.loopFrame`, `Fml.loopAnon`), modifier `_; _;` (commit 9ab7d94) and lowerReturns (Syntax.lean:3064-3110), where the continuation copied into branches may see branch locals. Each needs a solc-alignment.md row.
Dependent elimination: `Prog.cons`'s output stays a variable (no `Δ₂ ++ Δ₁`), but `Thin`/`Suffix` casts in `Env.thin`, `Frames.pop` and Stmt.step's dispatcher (Completeness.lean:531) can still produce 'motive is not type correct' in the about 387 match arms across 28 files. Dispatcher arms must use top-level patterns and `if h :`, as the old port learned.
Typed storage through `structDef` (a String match) may make the kernel whnf structDef in defeq checks. This risks whnf timeouts in Corpus `decide +kernel` and in concrete stores (Semantics.lean:977-985 already records one). uint as a subtype must not make the kernel unfold `Nat.land` (56642ee).
Callee frames: the typed `Stmt.call` body is closed over `rs ++ ps`, so expansion needs `Prog.wk` (O(|body|) once per call). Three return paths must be exported in the caller's output context: `CallRet.val`, `CallRet.rets` re-declared by elabTuple (:4129), and the memory return `mv` (elabMemCall :3583). Getting this wrong would break 449 imported functions at M2's lint.
Memory: Lean workers already use 3-4 GB on Decide.lean and Derived*. M6a touches both, inside the 32 GiB session cap, so at most two Lean agents can run, and only one during the M2/M4 low-module rebuilds.
Scope creep: M6c (about 25k closer lines) may not pay off. The plan allows it to stop at the `Fml.erase` reflection, which leaves the decision-procedure IR extrinsic. Users asking for 'everything intrinsic' should be told this before M6c starts.
