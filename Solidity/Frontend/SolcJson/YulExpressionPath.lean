import Solidity.Frontend.SolcJson.YulExpressionPositions
import Solidity.Yul.TypingLeafPaths

/-! Exact expression-relative grammar/JSON position links. These are static
path relations over existing typed leaves, not another program syntax. -/
namespace Solidity.Frontend.YulJson.ExpressionPath
open Lean (Json)
open Solidity.Yul

inductive ArgumentPath : TypingLeaves.Path → Nat → TypingLeaves.Path → Prop where
  | first (child : TypingLeaves.Path) : ArgumentPath (.first::child) 0 child
  | rest {source index child} : ArgumentPath source index child →
      ArgumentPath (.rest::source) (index+1) child

theorem ArgumentPath.shape {source index child} (route : ArgumentPath source index child) :
    source = List.replicate index .rest ++ .first::child := by
  induction route with
  | first child => rfl
  | rest route ih =>
      rw [List.replicate_succ,List.cons_append,ih]

theorem ArgumentPath.unique {one two index child}
    (first : ArgumentPath one index child) (second : ArgumentPath two index child) : one = two :=
  first.shape.trans second.shape.symm

inductive Link : TypingLeaves.Path → List Occurrences.Edge → Prop where
  | identifier : Link [] []
  | argument {source index child jsonPath} (ordinal : Nat) :
      ArgumentPath source index child → Link child jsonPath →
      Link (.arguments::source) (.field "arguments" ordinal::.array index::jsonPath)

/-- Equal JSON paths force equal original relative grammar paths, independent
of object-map WF. Object ordinal AND argument index remain explicit. -/
theorem Link.json_injective {first second jsonPath}
    (one : Link first jsonPath) (two : Link second jsonPath) : first = second := by
  induction one generalizing second with
  | identifier => cases two; rfl
  | argument ordinal route inside ih =>
      cases two with
      | argument otherOrdinal otherRoute otherInside =>
          have childEq := ih otherInside
          cases childEq
          exact congrArg (List.cons .arguments) (route.unique otherRoute)

def At {F X n E} (node : Json) (entry : TypingLeaves.Path × @TypingLeaves.ReadLeaf F X n E) : Prop :=
  ∃ jsonPath found, Link entry.1 jsonPath ∧
    Occurrences.OccurrenceD node false jsonPath false found ∧
    identifierPath found = .ok (entry.2.name,entry.2.parts)

def ChildAt {F X n E} (nodes : List Json)
    (entry : TypingLeaves.Path × @TypingLeaves.ReadLeaf F X n E) : Prop :=
  ∃ index : Fin nodes.length, ∃ childPath jsonPath found,
    ArgumentPath entry.1 index.val childPath ∧ Link childPath jsonPath ∧
    Occurrences.OccurrenceD nodes[index] false jsonPath false found ∧
    identifierPath found = .ok (entry.2.name,entry.2.parts)

/-- The REAL child-position premise is discharged by decoder fuel induction
in the final theorem; this helper tracks an actual input ordinal, not membership. -/
private theorem arguments_indexed {F X n E} (fuel : Nat)
    (known : ∀ {node term arity}, expressionAux fuel node = .ok term →
      (typed : @ExprD F X n E term arity) →
        TypingLeaves.All (fun path leaf => At node (path,leaf)) (TypingLeaves.reads typed []))
    (nodes : List Json) {trees : List (Solidity.Source.Syn .yulExpr)} {arity : Nat}
    (parsed : nodes.mapM (expressionAux fuel) = .ok trees)
    (typed : ArgsD E (Solidity.Frontend.Checked.toSynList trees) arity) :
    TypingLeaves.All (fun path leaf => ChildAt nodes (path,leaf)) (TypingLeaves.arguments typed []) := by
  induction nodes generalizing trees arity with
  | nil =>
      change (Except.ok [] : Except Error (List (Solidity.Source.Syn .yulExpr))) = .ok trees at parsed
      cases parsed
      cases typed
      intro entry impossible
      cases impossible
  | cons node rest ih =>
      cases headEq : expressionAux fuel node with
      | error reason =>
          simp only [List.mapM_cons,headEq,bind,Except.bind] at parsed
          cases parsed
      | ok headTree =>
          cases tailEq : rest.mapM (expressionAux fuel) with
          | error reason =>
              simp only [List.mapM_cons,headEq,tailEq,bind,Except.bind] at parsed
              cases parsed
          | ok tailTrees =>
              have same : headTree::tailTrees = trees := Except.ok.inj (by
                simpa only [List.mapM_cons,headEq,tailEq,bind,Except.bind,pure,Except.pure] using parsed)
              cases same
              cases typed with
              | cons head tail =>
                  intro entry present
                  change entry ∈ TypingLeaves.reads head [.first] ++
                    TypingLeaves.arguments tail [.rest] at present
                  rcases List.mem_append.mp present with first | later
                  · obtain ⟨relative,member,equal⟩ :=
                      TypingLeaves.mem_reads_rebase head [.first] entry first
                    cases equal
                    obtain ⟨jsonPath,found,link,occurrence,spelled⟩ := known headEq head relative member
                    exact ⟨⟨0,Nat.zero_lt_succ _⟩,relative.1,jsonPath,found,.first _,link,occurrence,spelled⟩
                  · obtain ⟨relative,member,equal⟩ :=
                      TypingLeaves.mem_arguments_rebase tail [.rest] entry later
                    cases equal
                    obtain ⟨index,childPath,jsonPath,found,route,link,occurrence,spelled⟩ :=
                      ih tailEq tail relative member
                    exact ⟨⟨index.val+1,Nat.succ_lt_succ index.isLt⟩,childPath,jsonPath,found,
                      .rest route,link,occurrence,spelled⟩

private theorem array_indexed_occurrence {values : Array Json}
    (index : Fin values.toList.length) {path found}
    (inside : Occurrences.OccurrenceD values.toList[index] false path false found) :
    Occurrences.OccurrenceD (.arr values) false (.array index.val::path) false found := by
  have bound : index.val < values.size := by
    simpa only [Array.length_toList] using index.isLt
  refine Occurrences.OccurrenceD.array ⟨index.val,bound⟩ ?_
  change Occurrences.OccurrenceD (values[index.val]'bound) false path false found
  change Occurrences.OccurrenceD (values.toList[index.val]'index.isLt) false path false found at inside
  simpa only [Array.getElem_toList] using inside

private theorem lift_child {F X n E parent values}
    (kind : string parent "nodeType" = .ok "YulFunctionCall")
    (valuesEq : array parent "arguments" = .ok values)
    (entry : TypingLeaves.Path × @TypingLeaves.ReadLeaf F X n E)
    (child : ChildAt values.toList entry) :
    At parent (.arguments::entry.1,entry.2) := by
  obtain ⟨index,childPath,jsonPath,found,route,link,occurrence,spelled⟩ := child
  have inArray := array_indexed_occurrence index occurrence
  have kindEq := ObjectLookup.kind_of_string kind
  have notIdentifier : Occurrences.isIdentifier parent = false := by
    simp only [Occurrences.isIdentifier,kindEq]
    decide +kernel
  have selected : Occurrences.includeField parent "arguments" = true := by
    simp only [Occurrences.includeField,kindEq,Occurrences.childKeys]
    decide +kernel
  have role : Occurrences.fieldRole parent "arguments" = false := by
    simp only [Occurrences.fieldRole,kindEq]
    decide +kernel
  obtain ⟨ordinal,lifted⟩ := ObjectLookup.field_occurrence
    (start := false) (ObjectLookup.array_field valuesEq) notIdentifier selected
    (by simpa only [role] using inArray)
  exact ⟨.field "arguments" ordinal::.array index.val::jsonPath,found,
    .argument ordinal route link,lifted,spelled⟩

private theorem identifier_paths {F X n E node name parts arity}
    (identified : Occurrences.isIdentifier node = true)
    (parsed : identifierPath node = .ok (name,parts))
    (typed : @ExprD F X n E (.yulPath name parts) arity) :
    TypingLeaves.All (fun path leaf => At node (path,leaf)) (TypingLeaves.reads typed []) := by
  cases typed <;> intro entry present <;>
    rcases List.mem_cons.mp present with same | impossible
  · cases same
    exact ⟨[],node,.identifier,.identifier identified,parsed⟩
  · cases impossible
  · cases same
    exact ⟨[],node,.identifier,.identifier identified,parsed⟩
  · cases impossible

private theorem call_paths {F X n E node name values trees arity} (fuel : Nat)
    (known : ∀ {node term arity}, expressionAux fuel node = .ok term →
      (typed : @ExprD F X n E term arity) →
        TypingLeaves.All (fun path leaf => At node (path,leaf)) (TypingLeaves.reads typed []))
    (kind : string node "nodeType" = .ok "YulFunctionCall")
    (valuesEq : array node "arguments" = .ok values)
    (decoded : values.toList.mapM (expressionAux fuel) = .ok trees)
    (typed : ExprD E (.yulCall name (Solidity.Frontend.Checked.toSynList trees)) arity) :
    TypingLeaves.All (fun path leaf => At node (path,leaf)) (TypingLeaves.reads typed []) := by
  cases typed with
  | builtin builtin spelling arguments =>
      intro entry present
      obtain ⟨relative,member,equal⟩ :=
        TypingLeaves.mem_arguments_rebase arguments [.arguments] entry present
      cases equal
      exact lift_child kind valuesEq relative
        (arguments_indexed fuel known values.toList decoded arguments relative member)
  | call function noBuiltin resolved arguments =>
      intro entry present
      obtain ⟨relative,member,equal⟩ :=
        TypingLeaves.mem_arguments_rebase arguments [.arguments] entry present
      cases equal
      exact lift_child kind valuesEq relative
        (arguments_indexed fuel known values.toList decoded arguments relative member)

/-- Final concrete decoder composition with exact argument indices and
relative grammar/JSON path links. Every helper child law is supplied by the
actual fuel induction, never an assumed alignment interface. -/
theorem decoded_paths {F X n E} (fuel : Nat) {node term arity}
    (parsed : expressionAux fuel node = .ok term) (typed : @ExprD F X n E term arity)
    : TypingLeaves.All (fun path leaf => At node (path,leaf)) (TypingLeaves.reads typed []) := by
  induction fuel generalizing node term arity with
  | zero => cases parsed
  | succ fuel ih =>
      rw [expressionAux] at parsed
      cases kindEq : string node "nodeType" with
      | error reason =>
          simp only [kindEq,bind,Except.bind] at parsed
          cases parsed
      | ok kind =>
          simp only [kindEq,bind,Except.bind] at parsed
          by_cases literalKind : kind = "YulLiteral"
          · rw [if_pos literalKind] at parsed
            cases literalEq : literal node with
            | error reason =>
                simp only [literalEq] at parsed
                cases parsed
            | ok description =>
                simp only [literalEq,pure,Except.pure] at parsed
                cases parsed
                cases typed
                intro entry impossible
                cases impossible
          · rw [if_neg literalKind] at parsed
            by_cases identifierKind : kind = "YulIdentifier"
            · rw [if_pos identifierKind] at parsed
              cases identifierEq : identifierPath node with
              | error reason =>
                  simp only [identifierEq] at parsed
                  cases parsed
              | ok pair =>
                  rcases pair with ⟨name,parts⟩
                  simp only [identifierEq,pure,Except.pure] at parsed
                  cases parsed
                  have identified : Occurrences.isIdentifier node = true := by
                    unfold Occurrences.isIdentifier
                    rw [ObjectLookup.kind_of_string
                      (kindEq.trans (congrArg Except.ok identifierKind))]
                    decide +kernel
                  exact identifier_paths identified identifierEq typed
            · rw [if_neg identifierKind] at parsed
              by_cases callKind : kind = "YulFunctionCall"
              · rw [if_pos callKind] at parsed
                cases functionField : field node "functionName" with
                | error reason =>
                    simp only [functionField] at parsed
                    cases parsed
                | ok functionNode =>
                    simp only [functionField] at parsed
                    cases functionEq : functionName functionNode with
                    | error reason =>
                        simp only [functionEq] at parsed
                        cases parsed
                    | ok name =>
                        simp only [functionEq] at parsed
                        cases valuesEq : array node "arguments" with
                        | error reason =>
                            simp only [valuesEq] at parsed
                            cases parsed
                        | ok values =>
                            simp only [valuesEq] at parsed
                            cases treesEq : values.toList.mapM (expressionAux fuel) with
                            | error reason =>
                                simp only [treesEq] at parsed
                                cases parsed
                            | ok trees =>
                                simp only [treesEq,pure,Except.pure] at parsed
                                cases parsed
                                exact call_paths fuel (fun decoded child =>
                                  ih decoded child)
                                  (kindEq.trans (congrArg Except.ok callKind))
                                  valuesEq treesEq typed
              · rw [if_neg callKind] at parsed
                cases parsed

structure Witness {F X n E} (node : Json)
    (entry : TypingLeaves.Path × @TypingLeaves.ReadLeaf F X n E) where
  path : List Occurrences.Edge
  found : Json
  linked : Link entry.1 path
  occurrence : Occurrences.OccurrenceD node false path false found
  spelled : identifierPath found = .ok (entry.2.name,entry.2.parts)

theorem At.witness {F X n E node entry} (actual : @At F X n E node entry) :
    Nonempty (Witness node entry) := by
  obtain ⟨path,found,linked,occurrence,spelled⟩ := actual
  exact ⟨⟨path,found,linked,occurrence,spelled⟩⟩

/-- An actual JSON position cannot witness two DIFFERENT original read entries.
This uses both grammar-path linkage and real JSON-position determinism, then
the existing intrinsic checker's exact reconstruction law. -/
theorem Witness.position_unique {F X n E node first second}
    (one : @Witness F X n E node first) (two : Witness node second)
    (same : one.path = two.path) : first = second := by
  have pathEq : first.1 = second.1 := one.linked.json_injective (same ▸ two.linked)
  have nodeEq : one.found = two.found :=
    (one.occurrence.deterministic two.occurrence same).2
  have spellingEq : (first.2.name,first.2.parts) = (second.2.name,second.2.parts) :=
    Except.ok.inj (one.spelled.symm.trans
      ((congrArg identifierPath nodeEq).trans two.spelled))
  have leafEq : first.2 = second.2 :=
    first.2.spelling_unique second.2 (congrArg Prod.fst spellingEq) (congrArg Prod.snd spellingEq)
  exact Prod.ext pathEq leafEq

end Solidity.Frontend.YulJson.ExpressionPath
namespace Solidity.Frontend.YulJson
open Solidity.Yul

theorem CheckedExpression.read_path_positions {F X n E bound node}
    (checked : @CheckedExpression F X n E bound node) :
    TypingLeaves.All (fun path leaf => ExpressionPath.At node (path,leaf)) checked.readTrace :=
  ExpressionPath.decoded_paths bound checked.parsed checked.derivation

theorem CheckedExpression.read_path_witnesses {F X n E bound node}
    (checked : @CheckedExpression F X n E bound node)
    (entry : TypingLeaves.Path × TypingLeaves.ReadLeaf E) (present : entry ∈ checked.readTrace) :
    Nonempty (ExpressionPath.Witness node entry) :=
  (checked.read_path_positions entry present).witness

end Solidity.Frontend.YulJson
