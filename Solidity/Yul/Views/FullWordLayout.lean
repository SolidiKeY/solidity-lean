import Solidity.Yul.Views.LocatedHash

/-! A checked relation between ACTUAL Source declaration types and the existing
word-granular Storage.STy. This does NOT encode solc packing. Narrow scalars,
bytes/string keys and recursive schemas need their separate owner agreement.
The checker recurses on the supplied finite owner layout, never arbitrary fuel. -/
namespace Solidity.Yul.Views

mutual
inductive FullWordLayout (E : Source.Env) : Source.STy → Storage.STy → Prop where
  | word : FullWordLayout E (.int .u256) .word
  | fixed {τ : Source.STy} {t : Storage.STy} (n : Nat) (element : FullWordLayout E τ t) :
      FullWordLayout E (.array .storage τ (some n)) (.sarr t n)
  | dynamic {τ : Source.STy} {t : Storage.STy} (element : FullWordLayout E τ t) :
      FullWordLayout E (.array .storage τ none) (.darr t)
  | mapping {τ : Source.STy} {t : Storage.STy} (value : FullWordLayout E τ t) :
      FullWordLayout E (.mapping (.int .u256) τ) (.map t)
  | strct (name : Source.DeclName) (fields : List (String × Source.STy)) (types : List Storage.STy)
      (found : E.structFields name .storage = some fields)
      (members : FullWordFields E (fields.map Prod.snd) types) :
      FullWordLayout E (.struct .storage name) (.strct types)
inductive FullWordFields (E : Source.Env) : List Source.STy → List Storage.STy → Prop where
  | nil : FullWordFields E [] []
  | cons {τ τs t ts} (head : FullWordLayout E τ t) (tail : FullWordFields E τs ts) :
      FullWordFields E (τ::τs) (t::ts)
end

mutual
def fullWordLayoutCheck (E : Source.Env) (τ : Source.STy) : Storage.STy → Bool
  | .word => τ == .int .u256
  | .sarr t n => match τ with
    | .array .storage σ (some k) => (k == n) && fullWordLayoutCheck E σ t
    | _ => false
  | .darr t => match τ with
    | .array .storage σ none => fullWordLayoutCheck E σ t
    | _ => false
  | .map t => match τ with
    | .mapping key σ => (key == .int .u256) && fullWordLayoutCheck E σ t
    | _ => false
  | .strct ts => match τ with
    | .struct .storage name => match E.structFields name .storage with
      | some fields => fullWordFieldsCheck E (fields.map Prod.snd) ts
      | none => false
    | _ => false

def fullWordFieldsCheck (E : Source.Env) : List Source.STy → List Storage.STy → Bool
  | [],[] => true
  | τ::τs,t::ts => fullWordLayoutCheck E τ t && fullWordFieldsCheck E τs ts
  | _,_ => false
end

mutual
theorem fullWordLayoutCheck_sound (E : Source.Env) (τ : Source.STy) (t : Storage.STy)
    (checked : fullWordLayoutCheck E τ t = true) : FullWordLayout E τ t := by
  cases t with
  | word =>
    have same : τ = .int .u256 := beq_iff_eq.mp checked
    subst τ
    exact .word
  | sarr t n =>
    cases τ with
    | array loc σ k =>
      cases loc with
      | storage =>
        cases k with
        | none => cases checked
        | some k =>
          have facts : (k == n) = true ∧ fullWordLayoutCheck E σ t = true := by
            simpa only [fullWordLayoutCheck,Bool.and_eq_true] using checked
          have eq : k = n := beq_iff_eq.mp facts.1
          subst k
          exact .fixed n (fullWordLayoutCheck_sound E σ t facts.2)
      | _ => cases checked
    | _ => cases checked
  | darr t =>
    cases τ with
    | array loc σ k =>
      cases loc with
      | storage =>
        cases k with
        | none => exact .dynamic (fullWordLayoutCheck_sound E σ t checked)
        | some k => cases checked
      | _ => cases checked
    | _ => cases checked
  | map t =>
    cases τ with
    | mapping key σ =>
      have facts : (key == .int .u256) = true ∧ fullWordLayoutCheck E σ t = true := by
        simpa only [fullWordLayoutCheck,Bool.and_eq_true] using checked
      have eq : key = .int .u256 := beq_iff_eq.mp facts.1
      subst key
      exact .mapping (fullWordLayoutCheck_sound E σ t facts.2)
    | _ => cases checked
  | strct ts =>
    cases τ with
    | struct loc name =>
      cases loc with
      | storage =>
        cases found : E.structFields name .storage with
        | none => simp only [fullWordLayoutCheck,found] at checked; cases checked
        | some fs =>
          simp only [fullWordLayoutCheck,found] at checked
          exact .strct name fs ts found (fullWordFieldsCheck_sound E _ _ checked)
      | _ => cases checked
    | _ => cases checked
termination_by sizeOf t

theorem fullWordFieldsCheck_sound (E : Source.Env) (τs : List Source.STy) (ts : List Storage.STy)
    (checked : fullWordFieldsCheck E τs ts = true) : FullWordFields E τs ts := by
  cases τs with
  | nil => cases ts with
    | nil => exact .nil
    | cons _ _ => cases checked
  | cons τ τs => cases ts with
    | nil => cases checked
    | cons t ts =>
      have facts : fullWordLayoutCheck E τ t = true ∧ fullWordFieldsCheck E τs ts = true := by
        simpa only [fullWordFieldsCheck,Bool.and_eq_true] using checked
      exact .cons (fullWordLayoutCheck_sound E τ t facts.1) (fullWordFieldsCheck_sound E τs ts facts.2)
termination_by sizeOf ts
end

end Solidity.Yul.Views
