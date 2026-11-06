import Solidity.SolcValidation.IrCensusTransfer

/-!
# Function tables of the parsed Census tree: one definition per name per scope

What the T02 matcher (and G01's relations, once frozen) refer to is a function
*by name* in an object's scope: `fun_<name>_<id>`, `checked_add_t_uint256`, …
That reference is meaningful only if each scope defines each name once.

- `objectGroups` lists every function group of a tree (each block's hoisted
  group, at every depth); `TablesUnique o` says every group has pairwise
  distinct names. `census_tables_unique`/`linked_tables_unique` prove it for the
  fixtures' trees by kernel evaluation. `objectWf` (which both trees pass) is
  stronger: its `declOk` also forbids a nested group from reusing a visible
  function name (no shadowing) and fixes every call to the innermost binder of
  its name (`Expr.wf`); `TablesUnique` is the per-group property stated on its
  own so that a duplicate is visibly a counterexample.
- `Mem.name_unique`: in such a group the name alone fixes the signature and the
  position, so any two calls to the same name are the same function.
- `helpers_named_*`: name lookup (`findFn`, the parser's resolver) in the parsed
  objects' groups lands exactly on the positions the transfer theorems use
  (`SolcValidation/IrCensusTransfer.lean`), so those theorems are about "the
  function named `n` in this object", not about a chosen position.

Negative controls: a text defining `f` twice is refused by the parser
(`parse_rejects_duplicate`), and the two trees that resolve its call `f()` to
the first or the second definition print to the same tokens while differing
(`duplicate_counterexample`): with a duplicate definition the tokens no longer
determine the program, and `TablesUnique` (as well as `objectWf`) is false on
both. A duplicate in a nested block of a child object is refused as well
(`parse_rejects_nested_duplicate`).
- `<group>_unmapped_<obj>`: every function the maps of
  `SolcValidation/IrCensusMaps.lean` send to `none` is absent from the object's
  group, so the lookup lemmas cover every helper the object defines.

Not proved here: that the certificate determines the whole tree (printer
injectivity under `objectWf`, i.e. "the unique parse"); see
`docs/feature-work/fullscope-vt1.md`.
-/
namespace Solidity.SolcValidation.IrSyntax
open Solidity.SolcValidation

/-- Pairwise distinct names, structurally. -/
def namesNodup : List FnSig → Bool
  | [] => true
  | s :: ss => !(ss.any (·.name == s.name)) && namesNodup ss

mutual
def Stmt.groups {F c L} : Stmt F c L → List (List FnSig)
  | .block b => b.groups
  | .discard _ | .assign _ _ => []
  | .if_ _ b => b.groups
  | .switch _ cs => cs.groups
  | .switchDefault _ cs b => cs.groups ++ b.groups
  | .for_ lp => lp.groups
  | .leave | .break_ | .continue_ => []

def Cases.groups {F c L} : Cases F c L → List (List FnSig)
  | .nil => []
  | .cons _ b rest => b.groups ++ rest.groups

def Loop.groups {F c L} : Loop F c L → List (List FnSig)
  | .stmt s rest => s.groups ++ rest.groups
  | .let_ _ _ rest => rest.groups
  | .run _ post body => post.groups ++ body.groups

def Items.groups {F c L g} : Items F c L g → List (List FnSig)
  | .nil => []
  | .stmt s rest => s.groups ++ rest.groups
  | .let_ _ _ rest => rest.groups
  | .fn _ rest => rest.groups

/-- Every function group: the block's own, then those inside its bodies and items. -/
def Block.groups {F c L} : Block F c L → List (List FnSig)
  | .mk ss bodies items => ss :: (bodies.groups ++ items.groups)

def Bodies.groups {F ss} : Bodies F ss → List (List FnSig)
  | .nil => []
  | .cons body rest => body.groups ++ rest.groups
end

mutual
def objectGroups : Object Code → List (List FnSig)
  | .object _ code children => code.groups ++ objectsGroups children
  | .data _ _ => []

def objectsGroups : List (Object Code) → List (List FnSig)
  | [] => []
  | o :: os => objectGroups o ++ objectsGroups os
end

/-- Every scope of the tree defines each function name at most once. -/
def TablesUnique (o : Object Code) : Prop := (objectGroups o).all namesNodup = true

instance (o : Object Code) : Decidable (TablesUnique o) := inferInstanceAs (Decidable (_ = _))

theorem census_tables_unique : TablesUnique censusRoot := by decide +kernel

theorem linked_tables_unique : TablesUnique linkedRoot := by decide +kernel

theorem Mem.toMem {α : Type} {L : List α} {x : α} : Mem L x → x ∈ L
  | .here => List.Mem.head _
  | .there m => List.Mem.tail _ (Mem.toMem m)

/-- In a group with distinct names, the name determines the signature and the
position: two memberships with the same name are the same function. -/
theorem Mem.name_unique : ∀ {F : List FnSig} {s₁ s₂ : FnSig}, namesNodup F = true →
    (m₁ : Mem F s₁) → (m₂ : Mem F s₂) → s₁.name = s₂.name → s₁ = s₂ ∧ m₁.index = m₂.index
  | _ :: _, _, _, _, .here, .here, _ => ⟨rfl, rfl⟩
  | _ :: ss, _, _, h, .there m₁, .there m₂, hn => by
      simp only [namesNodup, Bool.and_eq_true] at h
      have ih : _ ∧ m₁.index = m₂.index := Mem.name_unique h.2 m₁ m₂ hn
      exact ⟨ih.1, by simp only [Mem.index, ih.2]⟩
  | a :: ss, _, s₂, h, .here, .there m₂, hn => by
      simp only [namesNodup, Bool.and_eq_true, Bool.not_eq_true'] at h
      have hin : ss.any (·.name == a.name) = true :=
        List.any_eq_true.mpr ⟨s₂, Mem.toMem m₂, by simp only [hn, beq_self_eq_true]⟩
      rw [hin] at h
      exact absurd h.1 (by decide)
  | a :: ss, s₁, _, h, .there m₁, .here, hn => by
      simp only [namesNodup, Bool.and_eq_true, Bool.not_eq_true'] at h
      have hin : ss.any (·.name == a.name) = true :=
        List.any_eq_true.mpr ⟨s₁, Mem.toMem m₁, by simp only [hn, beq_self_eq_true]⟩
      rw [hin] at h
      exact absurd h.1 (by decide)

theorem cd_names_unique : namesNodup cdSigs = true := by decide +kernel
theorem cc_names_unique : namesNodup ccSigs = true := by decide +kernel
theorem ld_names_unique : namesNodup ldSigs = true := by decide +kernel

/-! ## Name lookup lands on the positions the transfer theorems use -/

theorem helpers_named_cd : ∀ {s : FnSig} (m : Mem (helperSigs ++ []) s) (m' : Mem (cdSigs ++ []) s),
    renHelpersCd m = some m' → (findFn (cdSigs ++ []) s.name).map (fun p => p.2.index) = some m'.index := by
  intro s m m' hm
  repeat' (first
    | (obtain rfl := Option.some.inj hm; decide +kernel)
    | exact Option.noConfusion hm
    | rcases m with _ | m)

theorem helpers_named_ld : ∀ {s : FnSig} (m : Mem (helperSigs ++ []) s) (m' : Mem (ldSigs ++ []) s),
    renHelpersLd m = some m' → (findFn (ldSigs ++ []) s.name).map (fun p => p.2.index) = some m'.index := by
  intro s m m' hm
  repeat' (first
    | (obtain rfl := Option.some.inj hm; decide +kernel)
    | exact Option.noConfusion hm
    | rcases m with _ | m)

theorem exp_named_cd : ∀ {s : FnSig} (m : Mem (expSigs ++ []) s) (m' : Mem (cdSigs ++ []) s),
    renExpCd m = some m' → (findFn (cdSigs ++ []) s.name).map (fun p => p.2.index) = some m'.index := by
  intro s m m' hm
  repeat' (first
    | (obtain rfl := Option.some.inj hm; decide +kernel)
    | exact Option.noConfusion hm
    | rcases m with _ | m)

theorem abi_named_cd : ∀ {s : FnSig} (m : Mem (abiSigs ++ []) s) (m' : Mem (cdSigs ++ []) s),
    renAbiCd m = some m' → (findFn (cdSigs ++ []) s.name).map (fun p => p.2.index) = some m'.index := by
  intro s m m' hm
  repeat' (first
    | (obtain rfl := Option.some.inj hm; decide +kernel)
    | exact Option.noConfusion hm
    | rcases m with _ | m)

theorem abi_named_ld : ∀ {s : FnSig} (m : Mem (abiSigs ++ []) s) (m' : Mem (ldSigs ++ []) s),
    renAbiLd m = some m' → (findFn (ldSigs ++ []) s.name).map (fun p => p.2.index) = some m'.index := by
  intro s m m' hm
  repeat' (first
    | (obtain rfl := Option.some.inj hm; decide +kernel)
    | exact Option.noConfusion hm
    | rcases m with _ | m)

theorem push_named_cd : ∀ {s : FnSig} (m : Mem (pushSigs ++ []) s) (m' : Mem (cdSigs ++ []) s),
    renPushCd m = some m' → (findFn (cdSigs ++ []) s.name).map (fun p => p.2.index) = some m'.index := by
  intro s m m' hm
  repeat' (first
    | (obtain rfl := Option.some.inj hm; decide +kernel)
    | exact Option.noConfusion hm
    | rcases m with _ | m)

theorem push_named_cc : ∀ {s : FnSig} (m : Mem (pushSigs ++ []) s) (m' : Mem (ccSigs ++ []) s),
    renPushCc m = some m' → (findFn (ccSigs ++ []) s.name).map (fun p => p.2.index) = some m'.index := by
  intro s m m' hm
  repeat' (first
    | (obtain rfl := Option.some.inj hm; decide +kernel)
    | exact Option.noConfusion hm
    | rcases m with _ | m)

/-! ## A function the maps leave out is one the object does not define -/

theorem helpers_unmapped_cd : ∀ {s : FnSig} (m : Mem (helperSigs ++ []) s),
    renHelpersCd m = none → (findFn (cdSigs ++ []) s.name).isNone = true := by
  intro s m hm
  repeat' (first
    | (exact Option.noConfusion hm)
    | decide +kernel
    | rcases m with _ | m)

theorem helpers_unmapped_ld : ∀ {s : FnSig} (m : Mem (helperSigs ++ []) s),
    renHelpersLd m = none → (findFn (ldSigs ++ []) s.name).isNone = true := by
  intro s m hm
  repeat' (first
    | (exact Option.noConfusion hm)
    | decide +kernel
    | rcases m with _ | m)

theorem exp_unmapped_cd : ∀ {s : FnSig} (m : Mem (expSigs ++ []) s),
    renExpCd m = none → (findFn (cdSigs ++ []) s.name).isNone = true := by
  intro s m hm
  repeat' (first
    | (exact Option.noConfusion hm)
    | decide +kernel
    | rcases m with _ | m)

theorem abi_unmapped_cd : ∀ {s : FnSig} (m : Mem (abiSigs ++ []) s),
    renAbiCd m = none → (findFn (cdSigs ++ []) s.name).isNone = true := by
  intro s m hm
  repeat' (first
    | (exact Option.noConfusion hm)
    | decide +kernel
    | rcases m with _ | m)

theorem abi_unmapped_ld : ∀ {s : FnSig} (m : Mem (abiSigs ++ []) s),
    renAbiLd m = none → (findFn (ldSigs ++ []) s.name).isNone = true := by
  intro s m hm
  repeat' (first
    | (exact Option.noConfusion hm)
    | decide +kernel
    | rcases m with _ | m)

theorem push_unmapped_cd : ∀ {s : FnSig} (m : Mem (pushSigs ++ []) s),
    renPushCd m = none → (findFn (cdSigs ++ []) s.name).isNone = true := by
  intro s m hm
  repeat' (first
    | (exact Option.noConfusion hm)
    | decide +kernel
    | rcases m with _ | m)

theorem push_unmapped_cc : ∀ {s : FnSig} (m : Mem (pushSigs ++ []) s),
    renPushCc m = none → (findFn (ccSigs ++ []) s.name).isNone = true := by
  intro s m hm
  repeat' (first
    | (exact Option.noConfusion hm)
    | decide +kernel
    | rcases m with _ | m)

/-! ## Negative controls: a duplicate definition -/

/-- A scope defining `f` twice, and calling `f`. -/
def dupText : String := "object \"Dup\" { code { f() function f() { } function f() { } } }"

/-- The parser refuses it, for its scoping check. -/
theorem parse_rejects_duplicate :
    (match parse dupText with | .ok _ => "" | .error e => e) =
      "tree violates scoping or static rules" := by decide +kernel

/-- A duplicate inside a function body's nested block, in a child object. -/
def dupNestedText : String :=
  "object \"A\" { code { } object \"B\" { code { function g() { { function f() { } function f() { } } } } } }"

theorem parse_rejects_nested_duplicate :
    (match parse dupNestedText with | .ok _ => "" | .error e => e) =
      "tree violates scoping or static rules" := by decide +kernel

def dupSigs : List FnSig := [⟨"f", [], []⟩, ⟨"f", [], []⟩]

/-- The tree of `dupText` with the call resolved to a chosen definition. -/
def dupTree (m : Mem (dupSigs ++ []) ⟨"f", [], []⟩) : Object Code :=
  .object "Dup" (.mk dupSigs (.cons (.mk [] .nil .nil) (.cons (.mk [] .nil .nil) .nil))
    (.stmt (.discard (.call m .nil)) (.fn ⟨0, by decide⟩ (.fn ⟨1, by decide⟩ .nil)))) []

/-- With a duplicate definition the token stream no longer fixes the program:
the call resolved to the first or to the second `f` prints the same tokens
(exactly `dupText`'s), yet the trees differ; both fail `TablesUnique` and
`objectWf`. This refutes "the tokens alone determine the tree"; that tokens
together with `objectWf` do (printer injectivity) is not proved. -/
theorem duplicate_counterexample :
    lex dupText = some (objectToks (dupTree .here)) ∧
    objectToks (dupTree .here) = objectToks (dupTree (.there .here)) ∧
    dupTree .here ≠ dupTree (.there .here) ∧
    ¬ TablesUnique (dupTree .here) ∧ ¬ TablesUnique (dupTree (.there .here)) ∧
    objectWf (dupTree .here) = false ∧ objectWf (dupTree (.there .here)) = false := by
  refine ⟨by decide +kernel, by decide +kernel, ?_, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel⟩
  intro h
  simp only [dupTree, Object.object.injEq, Block.mk.injEq] at h
  obtain ⟨-, ⟨-, -, hi⟩, -⟩ := h
  have hi' := eq_of_heq hi
  simp only [Items.stmt.injEq, Stmt.discard.injEq] at hi'
  have hw := congrArg Expr.wf hi'.1
  exact absurd hw (by decide +kernel)

end Solidity.SolcValidation.IrSyntax
