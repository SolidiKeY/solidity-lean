import Solidity.Correctness.Lowering.Total.Versions.Marked

/-!
# Loop lowering: transient state-variable declarations

The declaration component of complete-unit decoding: the model contract's
state variables (`Contract.vars`, in declaration order), each read as a Source
`stateVar` declaration at the elementary type the marked decoder gives it
(`Decode.elemB`, over the width and marker rows of `Contract.widths`), with its
`transient` flag set exactly when its name is a transient root
(`Contract.transientRoots`).

Failure is an error naming the first declaration that has no Source reading
(a reference type, or a primitive the table gives no elementary type): no
declaration is dropped and none is read as persistent storage in place of
transient storage. This component restricts nothing: it is not an admission
check, and the unit-level gaps of `Decode.unitOf` are left to the composer.

## Obligations not discharged by the model metadata

The component reads only `vars`, `transientRoots` and `widths`. What these do
not guarantee, and what the complete-unit decoder or the semantic binding must
still discharge:

* **Initializers.** Solidity rejects an initializer on a `transient` state
  variable, but `Contract.inits` may name a transient root (`transient_ok`
  constrains only the type). The declarations built here carry no initializer;
  the composer must refuse, not drop, such an initializer.
* **Width and marker rows.** Rows of `widths` that name no state variable, or
  marker rows the table does not read, are not inspected here (the composer's
  `keyB` check). Names that look like marker rows (`plainKey`) are not refused
  here either.
* **Root multiplicity.** `transientRoots` may repeat a name; membership is all
  that is read, so a repeat changes nothing here.
* **Compiler version.** `transient` needs a compiler that accepts it (solc
  0.8.28 or later for value types); the unit's pragma is not built here.
* **Storage regions.** That a Source `transient` declaration denotes the model's
  transaction-local root of the joint store (and a persistent one a persistent
  root) is the semantic binding, not shown here.
-/
namespace Solidity.Correctness.Lowering.Total.TransientDecode

open Source (Syn)
open Solidity.Roadmap.G49Final

/-! ## The decoder -/

/-- Why a state variable has no Source declaration. -/
inductive Gap where
  /-- A state variable of a reference type. -/
  | reference
  /-- A primitive the element table gives no elementary type at its width and
  markers. -/
  | noElem (p : PrimTy)
  deriving DecidableEq, Repr

/-- A failed declaration: the state variable's name and why. -/
structure DeclError where
  name : Name
  gap : Gap
  deriving DecidableEq, Repr

/-- The declaration of a state variable `x` of elementary type `e`, transient
or persistent: no visibility, constness, override or initializer. -/
def stateVarDecl (e : Source.Elem) (transient : Bool) (x : Name) : Syn (.part false) :=
  .stateVar (.elem e) none none none transient x .none

/-- One state variable's declaration over an element table `el`, transient
exactly when its name is in `roots`. -/
def declT (el : Name → PrimTy → Option Source.Elem) (roots : List Name) :
    Name × Ty → Except DeclError (Syn (.part false))
  | (x, .prim p) => match el x p with
    | some e => .ok (stateVarDecl e (roots.contains x) x)
    | none => .error ⟨x, .noElem p⟩
  | (x, .ref _) => .error ⟨x, .reference⟩

/-- The declarations of the state variables, in order; the first failure is
the error. -/
def declsT (el : Name → PrimTy → Option Source.Elem) (roots : List Name) :
    List (Name × Ty) → Except DeclError (Syn (.list (.part false)))
  | [] => .ok .nil
  | v :: rest => match declT el roots v, declsT el roots rest with
    | .ok d, .ok ds => .ok (.cons d ds)
    | .error err, _ => .error err
    | .ok _, .error err => .error err

/-- The element table of the marked decoder for a contract. -/
def elemOf (C : Contract) : Name → PrimTy → Option Source.Elem := Decode.elemB C.widths

/-- **The state-variable declarations of a contract**, transient roots marked
`transient`. -/
def decls (C : Contract) : Except DeclError (Syn (.list (.part false))) :=
  declsT (elemOf C) C.transientRoots C.vars

/-! ## The faithfulness relation -/

/-- `parts` declares exactly the state variables `vars`, in order, each at the
elementary type `el` gives it and transient exactly when its name is in
`roots`. -/
inductive Faithful (el : Name → PrimTy → Option Source.Elem) (roots : List Name) :
    List (Name × Ty) → Syn (.list (.part false)) → Prop
  | nil : Faithful el roots [] .nil
  | cons {x : Name} {p : PrimTy} {e : Source.Elem} {rest : List (Name × Ty)}
      {parts : Syn (.list (.part false))} :
      el x p = some e → Faithful el roots rest parts →
      Faithful el roots ((x, .prim p) :: rest) (.cons (stateVarDecl e (roots.contains x) x) parts)

/-- The name, type and transient flag of a state-variable part. -/
def stateView : Syn (.part false) → Option (Name × Syn .typeName × Bool)
  | .stateVar T _ _ _ t x _ => some (x, T, t)
  | _ => none

/-- The views of a part list, in order. -/
def stateViews : Syn (.list (.part false)) → List (Option (Name × Syn .typeName × Bool))
  | .nil => []
  | .cons d ds => stateView d :: stateViews ds

/-! ## Success and inversion -/

theorem declT_prim_ok {el : Name → PrimTy → Option Source.Elem} {roots : List Name}
    {x : Name} {p : PrimTy} {d : Syn (.part false)} :
    declT el roots (x, .prim p) = .ok d ↔
      ∃ e, el x p = some e ∧ d = stateVarDecl e (roots.contains x) x := by
  simp only [declT]
  split <;> rename_i h
  · simp only [Except.ok.injEq]
    exact ⟨fun hd => ⟨_, h, hd.symm⟩, fun ⟨e, he, hd⟩ => by
      rw [h] at he; cases he; exact hd.symm⟩
  · simp only [reduceCtorEq, false_iff, not_exists, not_and]
    intro e he; rw [h] at he; cases he

theorem declT_ref_not_ok {el : Name → PrimTy → Option Source.Elem} {roots : List Name}
    {x : Name} {R : RefTy} {d : Syn (.part false)} : declT el roots (x, .ref R) ≠ .ok d := by
  simp [declT]

/-- **Success is faithfulness**: the decoder succeeds exactly on the part list
that declares every state variable, in order, at its table type and with its
transient flag. -/
theorem declsT_ok_iff {el : Name → PrimTy → Option Source.Elem} {roots : List Name} :
    (vars : List (Name × Ty)) → (parts : Syn (.list (.part false))) →
    (declsT el roots vars = .ok parts ↔ Faithful el roots vars parts)
  | [], parts => by
      simp only [declsT, Except.ok.injEq]
      constructor
      · rintro rfl; exact .nil
      · intro h; cases h; rfl
  | (x, U) :: rest, parts => by
      have ih := declsT_ok_iff (el := el) (roots := roots) rest
      simp only [declsT]
      split
      · rename_i d ds hd hds
        simp only [Except.ok.injEq]
        constructor
        · rintro rfl
          cases U with
          | ref R => exact absurd hd declT_ref_not_ok
          | prim p =>
            obtain ⟨e, he, rfl⟩ := declT_prim_ok.mp hd
            exact .cons he ((ih ds).mp hds)
        · intro h
          cases h with
          | cons he hr =>
            obtain ⟨e', he', rfl⟩ := declT_prim_ok.mp hd
            rw [he] at he'; cases he'
            rw [(ih _).mpr hr] at hds; cases hds; rfl
      · rename_i err _ hd
        simp only [reduceCtorEq, false_iff]
        intro h
        cases h with
        | cons he _ =>
          have := declT_prim_ok (roots := roots) |>.mpr ⟨_, he, rfl⟩
          rw [hd] at this; cases this
      · rename_i d err hd hds
        simp only [reduceCtorEq, false_iff]
        intro h
        cases h with
        | cons _ hr => rw [(ih _).mpr hr] at hds; cases hds

/-- The decoder's success is decided per declaration: it succeeds exactly when
every state variable has a declaration. No failing declaration is skipped. -/
theorem declsT_ok_all {el : Name → PrimTy → Option Source.Elem} {roots : List Name} :
    (vars : List (Name × Ty)) →
    ((∃ parts, declsT el roots vars = .ok parts) ↔ ∀ v ∈ vars, ∃ d, declT el roots v = .ok d)
  | [] => by simp [declsT]
  | v :: rest => by
      have ih := declsT_ok_all (el := el) (roots := roots) rest
      simp only [declsT, List.mem_cons, forall_eq_or_imp]
      split
      · rename_i d ds hd hds
        simp only [Except.ok.injEq, exists_eq', true_iff]
        exact ⟨⟨d, hd⟩, ih.mp ⟨ds, hds⟩⟩
      · rename_i err _ hd
        simp only [reduceCtorEq, exists_false, false_iff, not_and]
        intro ⟨d, h⟩; rw [hd] at h; cases h
      · rename_i d err hd hds
        simp only [reduceCtorEq, exists_false, false_iff, not_and]
        intro _ hall
        obtain ⟨ds, h⟩ := ih.mpr hall
        rw [hds] at h; cases h

/-- **Error inversion**: an error names a declared state variable that has no
Source declaration, for the reason it gives, and every state variable before
it has one. -/
theorem declsT_error {el : Name → PrimTy → Option Source.Elem} {roots : List Name} :
    (vars : List (Name × Ty)) → {err : DeclError} → declsT el roots vars = .error err →
    ∃ pre U post, vars = pre ++ (err.name, U) :: post ∧
      (∀ v ∈ pre, ∃ d, declT el roots v = .ok d) ∧
      match err.gap with
      | .reference => ∃ R, U = .ref R
      | .noElem p => U = .prim p ∧ el err.name p = none
  | [], _, h => by simp [declsT] at h
  | (x, U) :: rest, err, h => by
      simp only [declsT] at h
      split at h
      · cases h
      · rename_i e _ hd
        cases h
        refine ⟨[], U, rest, ?_, by simp, ?_⟩
        · cases U with
          | prim p =>
            simp only [declT] at hd
            split at hd
            · cases hd
            · cases hd; rfl
          | ref R => simp only [declT] at hd; cases hd; rfl
        · cases U with
          | prim p =>
            simp only [declT] at hd
            split at hd
            · cases hd
            · rename_i hn; cases hd; exact ⟨rfl, hn⟩
          | ref R => simp only [declT] at hd; cases hd; exact ⟨R, rfl⟩
      · rename_i d e hd hds
        cases h
        obtain ⟨pre, U', post, rfl, hpre, hgap⟩ := declsT_error rest hds
        exact ⟨(x, U) :: pre, U', post, rfl, by
          simp only [List.mem_cons, forall_eq_or_imp]; exact ⟨⟨d, hd⟩, hpre⟩, hgap⟩

/-! ## What a faithful part list preserves -/

namespace Faithful

variable {el : Name → PrimTy → Option Source.Elem} {roots : List Name}

/-- Every state variable is primitive. -/
theorem prim : {vars : List (Name × Ty)} → {parts : Syn (.list (.part false))} →
    Faithful el roots vars parts → ∀ x U, (x, U) ∈ vars → ∃ p, U = .prim p
  | _, _, .nil, _, _, m => nomatch m
  | _, _, .cons (x := y) (p := q) _ hr, x, U, m => by
      rcases List.mem_cons.mp m with same | m'
      · cases same; exact ⟨q, rfl⟩
      · exact hr.prim x U m'

/-- **Names and order**: the declared names are the state variables' names, in
order, none dropped and none added. -/
theorem names : {vars : List (Name × Ty)} → {parts : Syn (.list (.part false))} →
    Faithful el roots vars parts →
    (stateViews parts).map (Option.map (·.1)) = vars.map (some ·.1)
  | _, _, .nil => rfl
  | _, _, .cons _ hr => by
      simp only [stateViews, stateView, stateVarDecl, List.map_cons, Option.map_some]
      rw [hr.names]

/-- **Transient flags**: each declaration is transient exactly when its state
variable is a root, in order. -/
theorem transient : {vars : List (Name × Ty)} → {parts : Syn (.list (.part false))} →
    Faithful el roots vars parts →
    (stateViews parts).map (Option.map (·.2.2)) = vars.map (some <| roots.contains ·.1)
  | _, _, .nil => rfl
  | _, _, .cons _ hr => by
      simp only [stateViews, stateView, stateVarDecl, List.map_cons, Option.map_some]
      rw [hr.transient]

/-- **Types**: each declaration has the elementary type the table gives its
state variable, in order. -/
theorem types : {vars : List (Name × Ty)} → {parts : Syn (.list (.part false))} →
    Faithful el roots vars parts →
    List.Forall₂ (fun v view => ∃ p e, v.2 = .prim p ∧ el v.1 p = some e ∧
      view = some (v.1, .elem e, roots.contains v.1)) vars (stateViews parts)
  | _, _, .nil => .nil
  | _, _, .cons he hr => .cons ⟨_, _, rfl, he, rfl⟩ hr.types

/-- The number of declarations is the number of state variables. -/
theorem length {vars : List (Name × Ty)} {parts : Syn (.list (.part false))}
    (h : Faithful el roots vars parts) : (stateViews parts).length = vars.length := by
  simpa using congrArg List.length h.names

/-- **The collected declaration** of the state variable the model reads under
`x`: its table type and its transient flag. -/
theorem find (x : Name) (p : PrimTy) : {vars : List (Name × Ty)} →
    {parts : Syn (.list (.part false))} → Faithful el roots vars parts →
    Semantics.lookupBy x vars = some (.prim p) →
    ∃ e, el x p = some e ∧
      (parts.collect (some Decode.contractName)).find?
        (fun d => d.kind == .stateVar && d.scope == some Decode.contractName && d.name == x) =
        some ⟨.stateVar, x, some Decode.contractName, false,
          stateVarDecl e (roots.contains x) x⟩
  | _, _, .nil, hx => by cases hx
  | _, _, .cons (x := y) (p := q) (e := e) he hr, hx => by
      simp only [Semantics.lookupBy] at hx
      by_cases same : x = y
      · subst same
        simp only [if_true, Option.some.injEq, Ty.prim.injEq] at hx
        subst hx
        exact ⟨e, he, by simp [Source.Syn.collect, stateVarDecl]⟩
      · simp only [if_neg same] at hx
        obtain ⟨e', he', found⟩ := hr.find x p hx
        refine ⟨e', he', ?_⟩
        have ne : (y == x) = false := by simpa using fun h => same h.symm
        simp [Source.Syn.collect, stateVarDecl, ne, found]

end Faithful

/-! ## The contract-level component -/

/-- The represented type of a state variable in the marked decoder: what the
width and marker rows say the model cell `x` of primitive `p` is. -/
inductive Represents (widths : List (Name × Nat)) (x : Name) : PrimTy → Source.Elem → Prop
  /-- `bool`, at the full word. -/
  | bool : Semantics.lookupBy (x ++ "#bytes") widths = none → Decode.isAddress widths x = false →
      Decode.stateBits widths x = 256 → Represents widths x .bool .bool
  /-- `uintN`/`intN` at the state variable's own width row (256 without one). -/
  | int {signed : Bool} {h} : Semantics.lookupBy (x ++ "#bytes") widths = none →
      Decode.isAddress widths x = false →
      Represents widths x (if signed then .int else .uint)
        (.int signed (Decode.stateBits widths x) h)
  /-- `address`: a `uint` with the address marker and no width row. -/
  | address : Semantics.lookupBy (x ++ "#bytes") widths = none → Decode.isAddress widths x = true →
      Semantics.lookupBy x widths = none → Represents widths x .uint .address
  /-- `bytesN`: a `uint` of `8N` bits with the bytes marker `N`, not an address. -/
  | fixedBytes {n : Nat} {h} : Semantics.lookupBy (x ++ "#bytes") widths = some n →
      Decode.isAddress widths x = false → Decode.stateBits widths x = 8 * n →
      Represents widths x .uint (.fixedBytes n h)

/-- The marked element table gives each state variable its represented type:
its width row, or its address or bytes marker. -/
theorem elemB_represents {widths : List (Name × Nat)} {x : Name} {p : PrimTy}
    {e : Source.Elem} (h : Decode.elemB widths x p = some e) : Represents widths x p e := by
  unfold Decode.elemB at h
  split at h
  · rename_i n hn
    split at h
    · rename_i ok
      obtain ⟨rfl, bits, addr⟩ := ok
      unfold Decode.bytesElem at h
      split at h
      · cases h; exact .fixedBytes hn addr bits
      · cases h
    · cases h
  · rename_i hn
    unfold Decode.elemA at h
    split at h
    · rename_i addr
      split at h
      · rename_i ok
        obtain ⟨rfl, row⟩ := ok
        cases h; exact .address hn addr row
      · cases h
    · rename_i addr
      have addr : Decode.isAddress widths x = false := by simpa using addr
      cases p with
      | bool =>
        unfold Decode.primElem at h
        split at h
        · rename_i bits; cases h; exact .bool hn addr bits
        · cases h
      | uint =>
        unfold Decode.primElem at h
        split at h
        · cases h; exact .int (signed := false) hn addr
        · cases h
      | int =>
        unfold Decode.primElem at h
        split at h
        · cases h; exact .int (signed := true) hn addr
        · cases h

/-- **Success is faithfulness**, for a contract. -/
theorem decls_ok_iff {C : Contract} {parts : Syn (.list (.part false))} :
    decls C = .ok parts ↔ Faithful (elemOf C) C.transientRoots C.vars parts :=
  declsT_ok_iff _ _

/-- **The declaration of a state variable**: the collected declaration of
each state variable is at its represented type, a primitive slot, and is
transient exactly when the variable is a transient root. -/
theorem decls_find {C : Contract} {parts : Syn (.list (.part false))} (h : decls C = .ok parts)
    {x : Name} {U : Ty} (mem : (x, U) ∈ C.vars) :
    ∃ p e, U = .prim p ∧ Represents C.widths x p e ∧
      Prim p (e.ty .storage) ∧ (e.ty .storage).cell = e.ty .storage ∧
      (parts.collect (some Decode.contractName)).find?
        (fun d => d.kind == .stateVar && d.scope == some Decode.contractName && d.name == x) =
        some ⟨.stateVar, x, some Decode.contractName, false,
          stateVarDecl e (decide (x ∈ C.transientRoots)) x⟩ := by
  have hf := decls_ok_iff.mp h
  obtain ⟨p, rfl⟩ := hf.prim x U mem
  obtain ⟨e, he, found⟩ := hf.find x p (Simulation.lookup_of_mem _ C.vars_nodup x _ mem)
  have hc : C.transientRoots.contains x = decide (x ∈ C.transientRoots) := by
    simp [List.contains_iff_mem]
  rw [hc] at found
  exact ⟨p, e, rfl, elemB_represents he, Version.elemB_prim he, found⟩

/-- **Transient roots stay transient**: every transient root is declared, as
`transient`, never dropped and never read as persistent storage. -/
theorem decls_root {C : Contract} {parts : Syn (.list (.part false))} (h : decls C = .ok parts)
    {r : Name} (root : r ∈ C.transientRoots) :
    ∃ p e, Semantics.lookupBy r C.vars = some (.prim p) ∧ Represents C.widths r p e ∧
      (parts.collect (some Decode.contractName)).find?
        (fun d => d.kind == .stateVar && d.scope == some Decode.contractName && d.name == r) =
        some ⟨.stateVar, r, some Decode.contractName, false, stateVarDecl e true r⟩ := by
  have ok := C.transient_ok
  simp only [List.all_eq_true] at ok
  have hr := ok r root
  split at hr
  · rename_i p hl
    have mem : (r, Ty.prim p) ∈ C.vars := by
      clear ok hr h root
      generalize C.vars = vs at hl
      induction vs with
      | nil => simp [Semantics.lookupBy] at hl
      | cons v vs ih =>
        simp only [Semantics.lookupBy] at hl
        split at hl
        · rename_i same; cases hl; simp at same; subst same; exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (ih hl)
    obtain ⟨p', e, same, rep, _, _, found⟩ := decls_find h mem
    cases same
    simp only [decide_eq_true root] at found
    exact ⟨p', e, hl, rep, found⟩
  · cases hr

/-- **Persistent variables stay persistent**: a state variable that is no
transient root is declared without `transient`. -/
theorem decls_persistent {C : Contract} {parts : Syn (.list (.part false))}
    (h : decls C = .ok parts) {x : Name} {U : Ty} (mem : (x, U) ∈ C.vars)
    (persistent : x ∉ C.transientRoots) :
    ∃ e, (parts.collect (some Decode.contractName)).find?
        (fun d => d.kind == .stateVar && d.scope == some Decode.contractName && d.name == x) =
        some ⟨.stateVar, x, some Decode.contractName, false, stateVarDecl e false x⟩ := by
  obtain ⟨_, e, _, _, _, _, found⟩ := decls_find h mem
  simp only [decide_eq_false persistent] at found
  exact ⟨e, found⟩

/-! ## Agreement with the existing decoder -/

/-- With no transient roots the component is the marked decoder's state
variables (`Decode.stateVarsOf`): the accepted domain and the declarations are
unchanged. -/
theorem declsT_nil_roots (el : Name → PrimTy → Option Source.Elem) :
    (vars : List (Name × Ty)) → (declsT el [] vars).toOption = Decode.stateVarsOf el vars
  | [] => rfl
  | (x, .ref _) :: rest => by simp [declsT, declT, Decode.stateVarsOf, Except.toOption]
  | (x, .prim p) :: rest => by
      have ih := declsT_nil_roots el rest
      simp only [declsT, declT, Decode.stateVarsOf, Option.bind_eq_bind, Option.pure_def]
      cases he : el x p with
      | none => simp [Except.toOption]
      | some e =>
        simp only [Option.bind_some]
        cases hr : declsT el [] rest with
        | ok ds =>
          rw [hr] at ih
          simp only [Except.toOption] at ih ⊢
          rw [← ih]; rfl
        | error err =>
          rw [hr] at ih
          simp only [Except.toOption] at ih ⊢
          rw [← ih]; rfl

/-- The component succeeds on exactly the state-variable lists the marked
decoder reads, whatever the roots: roots change flags, never the domain. -/
theorem declsT_roots_domain (el : Name → PrimTy → Option Source.Elem) (roots : List Name)
    (vars : List (Name × Ty)) :
    (∃ parts, declsT el roots vars = .ok parts) ↔ (∃ parts, declsT el [] vars = .ok parts) := by
  rw [declsT_ok_all, declsT_ok_all]
  refine forall_congr' fun v => forall_congr' fun _ => ?_
  rcases v with ⟨x, p | _⟩
  · simp only [declT_prim_ok]
    exact ⟨fun ⟨_, e, he, _⟩ => ⟨_, e, he, rfl⟩, fun ⟨_, e, he, _⟩ => ⟨_, e, he, rfl⟩⟩
  · exact ⟨fun ⟨_, h⟩ => absurd h declT_ref_not_ok, fun ⟨_, h⟩ => absurd h declT_ref_not_ok⟩

end Solidity.Correctness.Lowering.Total.TransientDecode
