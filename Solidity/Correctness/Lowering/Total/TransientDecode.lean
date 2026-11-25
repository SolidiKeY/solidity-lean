import Solidity.Correctness.Lowering.Total.Versions.Marked

/-!
# Loop lowering: transient state-variable declarations

The declaration component of complete-unit decoding: the state variables
(`Contract.vars`, in order), each a Source `stateVar` at the elementary type
the marked decoder reads from `Contract.widths` (`Decode.elemB`), `transient`
exactly when its name is in `Contract.transientRoots`. An error names the first
variable with no reading (a reference type, no elementary type, or an enum or
function-type marker `elemB` does not read): none is dropped, retyped or made
persistent. An error is a coverage gap, like a `none` of `Decode.unitOf`, not
an admission check. `Represents` restates `elemB`'s reading per case; that it
is the declared Solidity type is the elaborator's contract.

Obligations the metadata (`vars`, `transientRoots`, `widths`) leaves open, for
the unit composer or the semantic binding:
* an initializer of a transient root (`Contract.inits` may name one; Solidity
  rejects it): it must be refused, not dropped;
* width rows of no state variable, rows below a reference and names like marker
  rows (the composer's `keyB` and `plainKey`); `address payable` reads `address`;
* identifier validity and distinctness from the contract's name;
* the pragma (`transient` needs solc 0.8.28 or later);
* that a Source `transient` declaration denotes the model's transaction-local
  root, and a persistent one a persistent root (the semantic binding).
Repeated roots change nothing: only membership is read.
-/
namespace Solidity.Correctness.Lowering.Total.TransientDecode

open Source (Syn)
open Version (Prim)

/-! ## The decoder -/

/-- Why a state variable has no declaration: a reference type, or a primitive
the element table gives no elementary type. -/
inductive Gap where
  | reference
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

/-- Whether the width table carries a marker of `x` the marked decoder does not
read: an enum's (`x#enum`) or a function type's (`x#function(…)`). Such a
state variable is a `uint` in the model but no `uintN` in the source. -/
def unreadMarker (widths : List (Name × Nat)) (x : Name) : Bool :=
  (Semantics.lookupBy (x ++ "#enum") widths).isSome ||
    widths.any fun w => (x ++ "#function(").data.isPrefixOf w.1.data

/-- The element table for a contract: the marked decoder's, refusing a state
variable with a marker it does not read. -/
def elemOf (C : Contract) (x : Name) (p : PrimTy) : Option Source.Elem :=
  if unreadMarker C.widths x then none else Decode.elemB C.widths x p

theorem elemOf_some {C : Contract} {x : Name} {p : PrimTy} {e : Source.Elem}
    (h : elemOf C x p = some e) : unreadMarker C.widths x = false ∧ Decode.elemB C.widths x p = some e := by
  unfold elemOf at h
  split at h
  · cases h
  · rename_i hm; exact ⟨by simpa using hm, h⟩

/-- **The state-variable declarations of a contract**, transient roots marked
`transient`. -/
def decls (C : Contract) : Except DeclError (Syn (.list (.part false))) :=
  declsT (elemOf C) C.transientRoots C.vars

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
          | ref R => simp [declT] at hd
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
        cases U with
        | prim p =>
          simp only [declT] at hd; split at hd
          · cases hd
          · rename_i hn; cases hd; exact ⟨[], _, rest, rfl, by simp, rfl, hn⟩
        | ref R => simp only [declT] at hd; cases hd; exact ⟨[], _, rest, rfl, by simp, R, rfl⟩
      · rename_i d e hd hds
        cases h
        obtain ⟨pre, U', post, rfl, hpre, hgap⟩ := declsT_error rest hds
        exact ⟨(x, U) :: pre, U', post, rfl, by
          simp only [List.mem_cons, forall_eq_or_imp]; exact ⟨⟨d, hd⟩, hpre⟩, hgap⟩

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
  | _, _, .nil => by simp [stateViews]
  | _, _, .cons _ hr => by
      simp only [stateViews, stateView, stateVarDecl, List.map_cons, Option.map_some]
      rw [hr.names]

/-- **Transient flags**: each declaration is transient exactly when its state
variable is a root, in order. -/
theorem transient : {vars : List (Name × Ty)} → {parts : Syn (.list (.part false))} →
    Faithful el roots vars parts →
    (stateViews parts).map (Option.map (·.2.2)) = vars.map (some <| roots.contains ·.1)
  | _, _, .nil => by simp [stateViews]
  | _, _, .cons _ hr => by
      simp only [stateViews, stateView, stateVarDecl, List.map_cons, Option.map_some]
      rw [hr.transient]

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

/-- The represented type of the model cell `x` of primitive `p`: `bool` at the
full word; `uintN`/`intN` at its width row (256 without one); `address`, a
`uint` with the address marker and no width row; `bytesN`, a `uint` of `8N`
bits with the bytes marker `N`. -/
inductive Represents (widths : List (Name × Nat)) (x : Name) : PrimTy → Source.Elem → Prop
  | bool : Semantics.lookupBy (x ++ "#bytes") widths = none → Decode.isAddress widths x = false →
      Decode.stateBits widths x = 256 → Represents widths x .bool .bool
  | int {signed : Bool} {h} : Semantics.lookupBy (x ++ "#bytes") widths = none →
      Decode.isAddress widths x = false →
      Represents widths x (if signed then .int else .uint)
        (.int signed (Decode.stateBits widths x) h)
  | address : Semantics.lookupBy (x ++ "#bytes") widths = none → Decode.isAddress widths x = true →
      Semantics.lookupBy x widths = none → Represents widths x .uint .address
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
      cases p <;> simp only [Decode.primElem] at h <;> split at h <;>
        simp only [Option.some.injEq, reduceCtorEq] at h <;> subst h
      · exact .bool hn addr ‹_›
      · exact .int (signed := false) hn addr
      · exact .int (signed := true) hn addr

/-- **Success is faithfulness**, for a contract. -/
theorem decls_ok_iff {C : Contract} {parts : Syn (.list (.part false))} :
    decls C = .ok parts ↔ Faithful (elemOf C) C.transientRoots C.vars parts :=
  declsT_ok_iff _ _

/-- **The declaration of a state variable**: at its represented type, a
primitive slot, transient exactly when it is a transient root (so a persistent
variable is never declared `transient`). -/
theorem decls_find {C : Contract} {parts : Syn (.list (.part false))} (h : decls C = .ok parts)
    {x : Name} {U : Ty} (mem : (x, U) ∈ C.vars) :
    ∃ p e, U = .prim p ∧ unreadMarker C.widths x = false ∧ Represents C.widths x p e ∧
      Prim p (e.ty .storage) ∧ (e.ty .storage).cell = e.ty .storage ∧
      (parts.collect (some Decode.contractName)).find?
        (fun d => d.kind == .stateVar && d.scope == some Decode.contractName && d.name == x) =
        some ⟨.stateVar, x, some Decode.contractName, false,
          stateVarDecl e (decide (x ∈ C.transientRoots)) x⟩ := by
  have hf := decls_ok_iff.mp h
  obtain ⟨p, rfl⟩ := hf.prim x U mem
  obtain ⟨e, he, found⟩ := hf.find x p (Simulation.lookup_of_mem _ C.vars_nodup x _ mem)
  rw [show C.transientRoots.contains x = decide (x ∈ C.transientRoots) by simp] at found
  obtain ⟨hm, he⟩ := elemOf_some he
  exact ⟨p, e, rfl, hm, elemB_represents he, (Version.elemB_prim he).1,
    (Version.elemB_prim he).2, found⟩

/-- **Transient roots stay transient**: when the component succeeds, every
transient root is declared, as `transient`: none is dropped and none is read as
persistent storage. -/
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
    have mem : (r, Ty.prim p) ∈ C.vars := Semantics.lookupBy_eq_some_mem hl
    obtain ⟨q, e, same, _, rep, _, _, found⟩ := decls_find h mem
    cases same
    simp only [decide_eq_true root] at found
    exact ⟨p, e, hl, rep, found⟩
  · cases hr

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
        cases hr : declsT el [] rest <;> rw [hr] at ih <;>
          simp only [Except.toOption] at ih ⊢ <;> rw [← ih] <;> rfl

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
  · simp [declT]

end Solidity.Correctness.Lowering.Total.TransientDecode
