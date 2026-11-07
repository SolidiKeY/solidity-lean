import Solidity.Frontend.ExpressionUniqueness.RecursiveProperty
import Solidity.Frontend.ExpressionUniqueness.PostfixRootKind

/-!
# Postfix expression identity structural steps

Actual certified words identify all five root families and actual child spans.
Option/list distinctions remain intrinsic; call-options tails retain item
vectors. Recursive premises are structural facts for the original children.
-/

namespace Solidity.Frontend.ExpressionUniqueness

open Solidity.Source Solidity.Frontend.Checked

theorem index_prec_children (base : Syn .expr) (index : Syn (.opt .expr))
    (hp : (Syn.index base index).prec = true) : base.prec = true ∧ index.prec = true := by
  have hall : (Syn.index base index).all Syn.precNode = true := (Bool.and_eq_true_iff.mp hp).2
  change ((Syn.index base index).precNode && base.all Syn.precNode && index.all Syn.precNode) = true at hall
  exact ⟨all_prec_implies_prec base (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hall).1).2,
    all_prec_implies_prec index (Bool.and_eq_true_iff.mp hall).2⟩

theorem index_word_unique (base : Syn .expr) (index : Syn (.opt .expr))
    (ihBase : WordUnique base) (ihIndex : WordUnique index) : WordUnique (Syn.index base index) := by
  intro other initial final initial' final' items items' hp hp' hy hy' words
  have level : other.level = 15 := (partial_root_levels_equal (Syn.index base index) other
    initial final initial' final' items items' hp hp' hy hy' words).symm
  have kind : postfixRootKind (Syn.index base index) = postfixRootKind other :=
    partial_postfix_root_kinds_equal (Syn.index base index) other initial final initial' final' items items' rfl level hy hy' words
  rcases expr_level_fifteen_cases other level with ⟨base', index', rfl⟩ | ⟨base', start', stop', rfl⟩ |
    ⟨base', name', rfl⟩ | ⟨base', first', args', rfl⟩ | ⟨base', args', rfl⟩
  all_goals first | (cases kind; done) | skip
  obtain ⟨xs, ys, xs', ys', middle, middle', hx, hyr, hx', hyr', bw, rwrd⟩ := index_child_spans base base' index index'
    initial final initial' final' items items' hy hy' words
  obtain ⟨hpb, hpr⟩ := index_prec_children base index hp
  obtain ⟨hpb', hpr'⟩ := index_prec_children base' index' hp'
  have baseEq : base = base' := ihBase base' initial middle initial' middle' xs xs' hpb hpb' hx hx' bw
  have childEq : index = index' := ihIndex index' middle final middle' final' ys ys' hpr hpr' hyr hyr' rwrd
  rw [baseEq, childEq]

theorem slice_prec_children (base : Syn .expr) (start : Syn (.opt .expr)) (stop : Syn (.opt .expr))
    (hp : (Syn.slice base start stop).prec = true) : base.prec = true ∧ start.prec = true ∧ stop.prec = true := by
  have hall : (Syn.slice base start stop).all Syn.precNode = true := (Bool.and_eq_true_iff.mp hp).2
  change ((Syn.slice base start stop).precNode && base.all Syn.precNode && start.all Syn.precNode && stop.all Syn.precNode) = true at hall
  exact ⟨all_prec_implies_prec base (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hall).1).1).2,
    all_prec_implies_prec start (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hall).1).2,
    all_prec_implies_prec stop (Bool.and_eq_true_iff.mp hall).2⟩

theorem slice_word_unique (base : Syn .expr) (start : Syn (.opt .expr)) (stop : Syn (.opt .expr))
    (ihBase : WordUnique base) (ihStart : WordUnique start) (ihStop : WordUnique stop) : WordUnique (Syn.slice base start stop) := by
  intro other initial final initial' final' items items' hp hp' hy hy' words
  have level : other.level = 15 := (partial_root_levels_equal (Syn.slice base start stop) other
    initial final initial' final' items items' hp hp' hy hy' words).symm
  have kind : postfixRootKind (Syn.slice base start stop) = postfixRootKind other :=
    partial_postfix_root_kinds_equal (Syn.slice base start stop) other initial final initial' final' items items' rfl level hy hy' words
  rcases expr_level_fifteen_cases other level with ⟨base', index', rfl⟩ | ⟨base', start', stop', rfl⟩ |
    ⟨base', name', rfl⟩ | ⟨base', first', args', rfl⟩ | ⟨base', args', rfl⟩
  all_goals first | (cases kind; done) | skip
  obtain ⟨xs, ys, zs, xs', ys', zs', middle, next, middle', next', hx, hyb, hz, hx', hyb', hz', bw, yw, zw⟩ := slice_child_spans base base' start stop start' stop'
    initial final initial' final' items items' hy hy' words
  obtain ⟨hpb, hpy, hpz⟩ := slice_prec_children base start stop hp
  obtain ⟨hpb', hpy', hpz'⟩ := slice_prec_children base' start' stop' hp'
  have baseEq : base = base' := ihBase base' initial middle initial' middle' xs xs' hpb hpb' hx hx' bw
  have firstEq : start = start' := ihStart start' middle next middle' next' ys ys' hpy hpy' hyb hyb' yw
  have lastEq : stop = stop' := ihStop stop' next final next' final' zs zs' hpz hpz' hz hz' zw
  rw [baseEq, firstEq, lastEq]

theorem member_prec_children (base : Syn .expr) (name : String)
    (hp : (Syn.member base name).prec = true) : base.prec = true := by
  have hall : (Syn.member base name).all Syn.precNode = true := (Bool.and_eq_true_iff.mp hp).2
  change ((Syn.member base name).precNode && base.all Syn.precNode) = true at hall
  exact all_prec_implies_prec base (Bool.and_eq_true_iff.mp hall).2

theorem member_word_unique (base : Syn .expr) (name : String)
    (ihBase : WordUnique base) : WordUnique (Syn.member base name) := by
  intro other initial final initial' final' items items' hp hp' hy hy' words
  have level : other.level = 15 := (partial_root_levels_equal (Syn.member base name) other
    initial final initial' final' items items' hp hp' hy hy' words).symm
  have kind : postfixRootKind (Syn.member base name) = postfixRootKind other :=
    partial_postfix_root_kinds_equal (Syn.member base name) other initial final initial' final' items items' rfl level hy hy' words
  rcases expr_level_fifteen_cases other level with ⟨base', index', rfl⟩ | ⟨base', start', stop', rfl⟩ |
    ⟨base', name', rfl⟩ | ⟨base', first', args', rfl⟩ | ⟨base', args', rfl⟩
  all_goals first | (cases kind; done) | skip
  obtain ⟨names, xs, ys, hx, hyb, childWords⟩ := member_child_spans base base' name name'
    initial final initial' final' items items' hy hy' words
  have baseEq : base = base' := ihBase base' initial final initial' final' xs ys
    (member_prec_children base name hp) (member_prec_children base' name' hp') hx hyb childWords
  rw [baseEq, names]

theorem callOptions_prec_children (base : Syn .expr) (first : Syn .namedArg) (args : Syn (.list .namedArg))
    (hp : (Syn.callOptions base first args).prec = true) : base.prec = true ∧ first.prec = true ∧ args.prec = true := by
  have hall : (Syn.callOptions base first args).all Syn.precNode = true := (Bool.and_eq_true_iff.mp hp).2
  change ((Syn.callOptions base first args).precNode && base.all Syn.precNode && first.all Syn.precNode && args.all Syn.precNode) = true at hall
  exact ⟨all_prec_implies_prec base (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hall).1).1).2,
    all_prec_implies_prec first (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hall).1).2,
    all_prec_implies_prec args (Bool.and_eq_true_iff.mp hall).2⟩

theorem callOptions_word_unique (base : Syn .expr) (first : Syn .namedArg) (args : Syn (.list .namedArg))
    (ihBase : WordUnique base) (ihFirst : WordUnique first) (ihArgs : VectorUnique args) : WordUnique (Syn.callOptions base first args) := by
  intro other initial final initial' final' items items' hp hp' hy hy' words
  have level : other.level = 15 := (partial_root_levels_equal (Syn.callOptions base first args) other
    initial final initial' final' items items' hp hp' hy hy' words).symm
  have kind : postfixRootKind (Syn.callOptions base first args) = postfixRootKind other :=
    partial_postfix_root_kinds_equal (Syn.callOptions base first args) other initial final initial' final' items items' rfl level hy hy' words
  rcases expr_level_fifteen_cases other level with ⟨base', index', rfl⟩ | ⟨base', start', stop', rfl⟩ |
    ⟨base', name', rfl⟩ | ⟨base', first', args', rfl⟩ | ⟨base', args', rfl⟩
  all_goals first | (cases kind; done) | skip
  obtain ⟨xs, ys, zs, xs', ys', zs', middle, next, middle', next', hx, hyb, hz, hx', hyb', hz', bw, yw, zw⟩ := options_child_spans base base' first first' args args'
    initial final initial' final' items items' hy hy' words
  obtain ⟨hpb, hpy, hpz⟩ := callOptions_prec_children base first args hp
  obtain ⟨hpb', hpy', hpz'⟩ := callOptions_prec_children base' first' args' hp'
  have baseEq : base = base' := ihBase base' initial middle initial' middle' xs xs' hpb hpb' hx hx' bw
  have firstEq : first = first' := ihFirst first' middle next middle' next' ys ys' hpy hpy' hyb hyb' yw
  have lastEq : args = args' := ihArgs args' next final next' final' zs zs' hpz hpz' hz hz' zw
  rw [baseEq, firstEq, lastEq]

theorem call_prec_children (base : Syn .expr) (args : Syn .callArgs)
    (hp : (Syn.call base args).prec = true) : base.prec = true ∧ args.prec = true := by
  have hall : (Syn.call base args).all Syn.precNode = true := (Bool.and_eq_true_iff.mp hp).2
  change ((Syn.call base args).precNode && base.all Syn.precNode && args.all Syn.precNode) = true at hall
  exact ⟨all_prec_implies_prec base (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hall).1).2,
    all_prec_implies_prec args (Bool.and_eq_true_iff.mp hall).2⟩

theorem call_word_unique (base : Syn .expr) (args : Syn .callArgs)
    (ihBase : WordUnique base) (ihArgs : WordUnique args) : WordUnique (Syn.call base args) := by
  intro other initial final initial' final' items items' hp hp' hy hy' words
  have level : other.level = 15 := (partial_root_levels_equal (Syn.call base args) other
    initial final initial' final' items items' hp hp' hy hy' words).symm
  have kind : postfixRootKind (Syn.call base args) = postfixRootKind other :=
    partial_postfix_root_kinds_equal (Syn.call base args) other initial final initial' final' items items' rfl level hy hy' words
  rcases expr_level_fifteen_cases other level with ⟨base', index', rfl⟩ | ⟨base', start', stop', rfl⟩ |
    ⟨base', name', rfl⟩ | ⟨base', first', args', rfl⟩ | ⟨base', args', rfl⟩
  all_goals first | (cases kind; done) | skip
  obtain ⟨xs, ys, xs', ys', middle, middle', hx, hyr, hx', hyr', bw, rwrd⟩ := call_child_spans base base' args args'
    initial final initial' final' items items' hy hy' words
  obtain ⟨hpb, hpr⟩ := call_prec_children base args hp
  obtain ⟨hpb', hpr'⟩ := call_prec_children base' args' hp'
  have baseEq : base = base' := ihBase base' initial middle initial' middle' xs xs' hpb hpb' hx hx' bw
  have childEq : args = args' := ihArgs args' middle final middle' final' ys ys' hpr hpr' hyr hyr' rwrd
  rw [baseEq, childEq]

end Solidity.Frontend.ExpressionUniqueness
