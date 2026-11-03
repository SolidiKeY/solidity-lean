import Solidity.Lowering.V07.AssignmentControls

namespace Solidity.Lowering.V07.LocalFamilyControls
open Source.SemanticsExamples

abbrev Keys := Bool × Bool
abbrev SrcCtx : Source.RCtx := [.int .u8,.int .u8,.int .u8]
abbrev TgtCtx : Ctx := [.val .uint,.val .uint,.val .uint]
def source : Source.EMState E0 SrcCtx :=
  (.cons (.int 7 (by decide)) (.cons (.int 3 (by decide)) (.cons (.int 3 (by decide)) .nil)),s0)
def target : State (default : Contract) TgtCtx :=
  (((State.init default).push (integerValue .u8 3 (by decide))).push
    (integerValue .u8 3 (by decide))).push (integerValue .u8 7 (by decide))
def si : Keys → Source.Idx SrcCtx (.int .u8)
  | (false,false) => .here
  | (false,true) => .there .here
  | (true,false) => .there (.there .here)
  | (true,true) => .there .here
def ti : Keys → Idx TgtCtx (.val .uint)
  | (false,false) => .here
  | (false,true) => .there .here
  | (true,false) => .there (.there .here)
  | (true,true) => .there .here

theorem initial : IntegerLocalFamily .u8 si ti source.1 target.env := by
  constructor
  · intro k; rcases k with ⟨a,b⟩; cases a <;> cases b <;> rfl
  · intro k l; rcases k with ⟨a,b⟩; rcases l with ⟨c,d⟩
    cases a <;> cases b <;> cases c <;> cases d <;> decide

theorem equal_content_distinct_identity :
    source.1.get (si (false,true)) = source.1.get (si (true,false)) ∧
    (si (false,true)).toNat ≠ (si (true,false)).toNat := ⟨rfl,by decide⟩

theorem overlapping_alias_write :
    ((source.1.set (si (false,true)) (source.1.get (si (false,false)))).get (si (true,true))).key = some 7 ∧
    ((source.1.set (si (false,true)) (source.1.get (si (false,false)))).get (si (true,false))).key = some 3 ∧
    IntegerLocalFamily .u8 si ti
      (source.1.set (si (false,true)) (source.1.get (si (false,false))))
      (TEnv.set (ti (false,true)) (TEnv.get (ti (false,false)) target.env) target.env) :=
  ⟨rfl,rfl,initial.write (false,true) (false,false)⟩

def collapsed : Keys → Idx TgtCtx (.val .uint)
  | (false,false) => .here
  | _ => .there .here

theorem collapsed_contents_agree :
    ∀ k, IntValueRel .u8 (source.1.get (si k)) (TEnv.get (collapsed k) target.env) := by
  intro k; rcases k with ⟨a,b⟩; cases a <;> cases b <;> rfl

theorem collapsed_identity_rejected : ¬ IntegerLocalFamily .u8 si collapsed source.1 target.env := by
  intro h
  have e := (h.aliases (false,true) (true,false)).mpr rfl
  change (1 : Nat) = 2 at e
  omega

def written (n : Nat) : Keys := if n = 1 then (false,false) else (false,true)
def rhs (n : Nat) : Keys := if n = 1 then (true,false) else (false,false)

theorem every_prefix (n : Nat) :
    IntegerLocalFamily .u8 si ti (sourceIntegerPrefixes si written rhs source.1 n)
      (targetIntegerPrefixes ti written rhs target.env n) :=
  integer_assignment_prefix_family initial written rhs n

theorem three_reached_writes :
    ((sourceIntegerPrefixes si written rhs source.1 1).get (si (true,true))).key = some 7 ∧
    ((sourceIntegerPrefixes si written rhs source.1 2).get (si (false,false))).key = some 3 ∧
    ((sourceIntegerPrefixes si written rhs source.1 3).get (si (true,true))).key = some 3 := ⟨rfl,rfl,rfl⟩

theorem third_actual_source (p : Roadmap.Pipeline) (fuel : Nat) :
    (Source.evalE (G0 p) F0 (fuel+2)
      (.assign (.local (si (written 2))) (.local (si (rhs 2))))).run
      (sourceIntegerPrefixes si written rhs source.1 2,source.2) =
      (.ok (.val (.int 3 (by decide))),(sourceIntegerPrefixes si written rhs source.1 3,source.2)) :=
  (integer_assignment_prefix_step .u8 si ti (G0 p) F0 fuel 2 source target initial written rhs).1

theorem third_actual_target (p : Roadmap.Pipeline) (fuel : Nat) :
    (assignLocalOperand (ti (written 2)) (ti (rhs 2))).run
      (target.withEnv (targetIntegerPrefixes ti written rhs target.env 2)) =
      .ok (⟨target.withEnv (targetIntegerPrefixes ti written rhs target.env 3),List.prefix_refl _⟩,
        .prim (integerValue .u8 3 (by decide))) :=
  (integer_assignment_prefix_step .u8 si ti (G0 p) F0 fuel 2 source target initial written rhs).2.1

theorem collapsed_write_breaks_contents :
    ¬ IntValueRel .u8
      ((source.1.set (si (false,true)) (source.1.get (si (false,false)))).get (si (true,false)))
      (TEnv.get (collapsed (true,false))
        (TEnv.set (collapsed (false,true)) (TEnv.get (collapsed (false,false)) target.env) target.env)) := by
  change ¬ (some (3 : Int) = some 7)
  decide

theorem mixed_binder_extension {σ : Source.STy} {u : LTy}
    (sv : Source.Val E0.layout σ) (tv : u.TDenote (default : Contract) target.H) :
    IntegerLocalFamily .u8 (fun k => .there (si k)) (fun k => .there (ti k))
      (.cons sv source.1) (tv,target.env) := initial.under_binders sv tv

end Solidity.Lowering.V07.LocalFamilyControls
