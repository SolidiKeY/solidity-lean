import Solidity.Yul.Views.InheritedDeclarationReads

namespace Solidity.Yul.Views

inductive LayoutOriginError where
  | hierarchy (reason : InheritedLayoutError) | missingActive | malformedActive
  | outsideProfile | notNumeric | outOfRange | declarations (reason : InheritedLayoutError)
  deriving DecidableEq, Repr

/-- Exact OWNER evaluation, integral range and current literal-base profile.
No modular conversion and no assumed physical layout law. -/
structure ExactLiteralOrigin (e : Source.Syn .expr) where
  value : Roadmap.Word
  constant : Source.Q
  evaluated : e.const = some constant
  fits : constant.FitsInt .u256
  exactValue : (value.val : Int) = constant.toInt
  profile : Source.isLiteralBase e = true

def prepareLiteralOrigin (e : Source.Syn .expr) : Except LayoutOriginError (ExactLiteralOrigin e) :=
  if profile : Source.isLiteralBase e = true then
    match evaluated : e.const with
    | none => .error .notNumeric
    | some q =>
      if fits : q.FitsInt .u256 then
        have lo : 0 ≤ q.toInt := fits.2.1
        have hi : q.toInt ≤ (2^256-1 : Nat) := fits.2.2
        have bound : q.toInt.toNat < 2^256 := by omega
        .ok ⟨⟨q.toInt.toNat,bound⟩,q,evaluated,fits,by dsimp only; omega,profile⟩
      else .error .outOfRange
  else .error .outsideProfile

/-- Read only the selected ACTIVE contract's node. Base clauses are not an
input. Syntax-name mismatch and malformed declaration shapes are diagnosed. -/
def activeDeclarationOrigin (d : Source.Decl) : Except LayoutOriginError Roadmap.Word :=
  match d.kind,d.top,d.node with
  | .contract,true,.contract _ name base _ _ =>
    if name = d.name then
      match base with
      | .none => .ok 0
      | .some e => (prepareLiteralOrigin e).map ExactLiteralOrigin.value
    else .error .malformedActive
  | _,_,_ => .error .malformedActive

structure ActiveLayoutOrigin (E : Source.Env) (active : String) where
  hierarchy : StorageHierarchy E active
  declaration : Source.Decl
  found : E.declOf .contract ⟨none,active⟩ = some declaration
  persistent : Roadmap.Word
  computed : activeDeclarationOrigin declaration = .ok persistent

def prepareActiveOrigin (E : Source.Env) (active : String) : Except LayoutOriginError (ActiveLayoutOrigin E active) := do
  let hierarchy ← (prepareStorageHierarchy E active).mapError LayoutOriginError.hierarchy
  match found : E.declOf .contract ⟨none,active⟩ with
  | none => .error .missingActive
  | some declaration =>
    match computed : activeDeclarationOrigin declaration with
    | .error reason => .error reason
    | .ok word => .ok ⟨hierarchy,declaration,found,word,computed⟩

/-- Custom persistent layout never shifts the independent transient bank. -/
def ActiveLayoutOrigin.forBank {E active} (o : ActiveLayoutOrigin E active) (tr : Bool) : Roadmap.Word :=
  if tr then 0 else o.persistent

theorem ActiveLayoutOrigin.transient_zero {E active} (o : ActiveLayoutOrigin E active) : o.forBank true = 0 := rfl

theorem literalOrigin_integral {e} (o : ExactLiteralOrigin e) :
    o.constant.int? = some (o.value.val : Int) := by
  simp only [Source.Q.int?,o.fits.1,if_true,o.exactValue]

theorem literalOrigin_noWrap {e} (o : ExactLiteralOrigin e) :
    0 ≤ o.constant.toInt ∧ o.constant.toInt < (2^256 : Nat) ∧ (o.value.val : Int) = o.constant.toInt := by
  have lo : 0 ≤ o.constant.toInt := o.fits.2.1
  have hi : o.constant.toInt ≤ (2^256-1 : Nat) := o.fits.2.2
  exact ⟨lo,by omega,o.exactValue⟩

/-- Successful literal conversion retains the ACTUAL profile judgment. -/
theorem literalOrigin_profile {e} (o : ExactLiteralOrigin e) (abstract : Bool) (name : String) (is : Source.Syn (.list .inherit))
    (parts : Source.Syn (.list (.part false))) :
    (Source.Syn.contract abstract name (.some e) is parts).excl = none := by
  simp only [Source.Syn.excl,o.profile,if_true]

end Solidity.Yul.Views
