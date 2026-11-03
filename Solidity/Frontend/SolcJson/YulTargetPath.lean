import Solidity.Frontend.SolcJson.YulExpressionPath
import Solidity.Yul.TypingTargetPaths

/-! Exact assignment-target array positions from actual identifier decoding
and original intrinsic target certificates. Reverse/block/provenance claims
are separate. -/
namespace Solidity.Frontend.YulJson.TargetPath
open Lean (Json)
open Solidity.Yul
open ExpressionPath (ArgumentPath)

inductive Link : TypingLeaves.Path → List Occurrences.Edge → Prop where
  | target {source index} (ordinal : Nat) : ArgumentPath source index [] →
      Link source [.field "variableNames" ordinal,.array index]

theorem Link.json_injective {first second jsonPath}
    (one : Link first jsonPath) (two : Link second jsonPath) : first = second := by
  cases one with
  | target ordinal route =>
      cases two with
      | target otherOrdinal otherRoute => exact route.unique otherRoute

def ChildAt {X n E} (nodes : List Json) (entry : TypingLeaves.Path × @TypingLeaves.WriteLeaf X n E) : Prop :=
  ∃ index : Fin nodes.length, ArgumentPath entry.1 index.val [] ∧
    identifierPath nodes[index] = .ok (entry.2.name,entry.2.parts)

private theorem targets_indexed {X n E} (nodes : List Json)
    {pairs : List (String × List String)}
    (parsed : nodes.mapM identifierPath = .ok pairs)
    (typed : @TargetsD X n E (pairs.map (fun pair => pair.1::pair.2))) :
    TypingLeaves.All (fun path leaf => ChildAt nodes (path,leaf)) (TypingLeaves.targets typed []) := by
  induction nodes generalizing pairs with
  | nil =>
      change (Except.ok [] : Except Error (List (String × List String))) = .ok pairs at parsed
      cases parsed
      cases typed
      intro entry impossible
      cases impossible
  | cons node rest ih =>
      cases headEq : identifierPath node with
      | error reason =>
          simp only [List.mapM_cons,headEq,bind,Except.bind] at parsed
          cases parsed
      | ok pair =>
          rcases pair with ⟨name,parts⟩
          cases tailEq : rest.mapM identifierPath with
          | error reason =>
              simp only [List.mapM_cons,headEq,tailEq,bind,Except.bind] at parsed
              cases parsed
          | ok tailPairs =>
              have same : (name,parts)::tailPairs = pairs := Except.ok.inj (by
                simpa only [List.mapM_cons,headEq,tailEq,bind,Except.bind,pure,Except.pure] using parsed)
              cases same
              cases typed with
              | cons head tail =>
                  cases head with
                  | path target =>
                      intro entry present
                      change entry ∈ [([.first],⟨name,parts,_,target⟩)] ++
                        TypingLeaves.targets tail [.rest] at present
                      rcases List.mem_append.mp present with first | later
                      · rcases List.mem_cons.mp first with equal | impossible
                        · cases equal
                          exact ⟨⟨0,Nat.zero_lt_succ _⟩,.first [],headEq⟩
                        · cases impossible
                      · obtain ⟨relative,member,equal⟩ :=
                          TypingLeaves.mem_targets_rebase tail [.rest] entry later
                        cases equal
                        obtain ⟨index,route,decoded⟩ := ih tailEq tail relative member
                        exact ⟨⟨index.val+1,Nat.succ_lt_succ index.isLt⟩,.rest route,decoded⟩

private theorem identifier_tag {node : Json} {name parts}
    (decoded : identifierPath node = .ok (name,parts)) :
    Occurrences.isIdentifier node = true := by
  have parsed := decoded
  unfold identifierPath requireNode at parsed
  cases kindEq : string node "nodeType" with
  | error reason => simp only [kindEq,bind,Except.bind] at parsed; cases parsed
  | ok kind =>
      simp only [kindEq,bind,Except.bind] at parsed
      by_cases same : kind = "YulIdentifier"
      · unfold Occurrences.isIdentifier
        rw [ObjectLookup.kind_of_string kindEq,same]
        decide +kernel
      · simp only [same,if_false,throw] at parsed
        cases parsed

def At {X n E} (node : Json) (entry : TypingLeaves.Path × @TypingLeaves.WriteLeaf X n E) : Prop :=
  ∃ jsonPath found, Link entry.1 jsonPath ∧
    Occurrences.OccurrenceD node false jsonPath true found ∧
    identifierPath found = .ok (entry.2.name,entry.2.parts)

/-- Exact target positions from REAL assignment-kind/array/mapM equations.
Final statement-decoder composition below constructs those equations. -/
theorem targets_positions {X n E node values pairs}
    (kind : string node "nodeType" = .ok "YulAssignment")
    (valuesEq : array node "variableNames" = .ok values)
    (parsed : values.toList.mapM identifierPath = .ok pairs)
    (typed : @TargetsD X n E (pairs.map (fun pair => pair.1::pair.2))) :
    TypingLeaves.All (fun path leaf => At node (path,leaf)) (TypingLeaves.targets typed []) := by
  intro entry present
  obtain ⟨index,route,decoded⟩ := targets_indexed values.toList parsed typed entry present
  have bound : index.val < values.size := by
    simpa only [Array.length_toList] using index.isLt
  let current : Fin values.size := ⟨index.val,bound⟩
  have spelled : identifierPath values[current] = .ok (entry.2.name,entry.2.parts) := by
    change identifierPath (values[index.val]'bound) = _
    change identifierPath (values.toList[index.val]'index.isLt) = _ at decoded
    simpa only [Array.getElem_toList] using decoded
  have inArray : Occurrences.OccurrenceD (.arr values) true [.array index.val] true values[current] :=
    .array current (.identifier (identifier_tag spelled))
  have kindEq := ObjectLookup.kind_of_string kind
  have notIdentifier : Occurrences.isIdentifier node = false := by
    simp only [Occurrences.isIdentifier,kindEq]
    decide +kernel
  have selected : Occurrences.includeField node "variableNames" = true := by
    simp only [Occurrences.includeField,kindEq,Occurrences.childKeys]
    decide +kernel
  have role : Occurrences.fieldRole node "variableNames" = true := by
    simp only [Occurrences.fieldRole,kindEq]
    decide +kernel
  obtain ⟨ordinal,lifted⟩ := ObjectLookup.field_occurrence (start := false)
    (ObjectLookup.array_field valuesEq) notIdentifier selected
    (by simpa only [role] using inArray)
  exact ⟨[.field "variableNames" ordinal,.array index.val],values[current],
    .target ordinal route,lifted,spelled⟩

structure Witness {X n E} (node : Json) (entry : TypingLeaves.Path × @TypingLeaves.WriteLeaf X n E) where
  path : List Occurrences.Edge
  found : Json
  linked : Link entry.1 path
  occurrence : Occurrences.OccurrenceD node false path true found
  spelled : identifierPath found = .ok (entry.2.name,entry.2.parts)

theorem At.witness {X n E node entry} (actual : @At X n E node entry) : Nonempty (Witness node entry) := by
  obtain ⟨path,found,linked,occurrence,spelled⟩ := actual
  exact ⟨⟨path,found,linked,occurrence,spelled⟩⟩

theorem Witness.position_unique {X n E node first second}
    (one : @Witness X n E node first) (two : Witness node second)
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

/-- Constructor discrimination for the ACTUAL existing statement decoder. -/
private theorem assignment_kind (fuel : Nat) {node first rest rhs}
    (parsed : statementAux fuel node = .ok (.yulAssign first rest rhs)) :
    string node "nodeType" = .ok "YulAssignment" := by
  cases fuel with
  | zero => cases parsed
  | succ fuel =>
      rw [statementAux] at parsed
      cases kindEq : string node "nodeType" with
      | error reason =>
          simp only [kindEq,bind,Except.bind] at parsed
          cases parsed
      | ok kind =>
          by_cases correct : kind = "YulAssignment"
          · exact congrArg Except.ok correct
          · simp only [kindEq,correct,if_false,bind,Except.bind] at parsed
            by_cases blockKind : kind = "YulBlock"
            · rw [if_pos blockKind] at parsed
              cases equation : (blockAux fuel node) with
              | error reason =>
                  simp only [equation] at parsed
                  cases parsed
              | ok body =>
                  simp only [equation] at parsed
                  cases parsed
            · rw [if_neg blockKind] at parsed
              by_cases letKind : kind = "YulVariableDeclaration"
              · rw [if_pos letKind] at parsed
                cases equation : (names node "variables") with
                | error reason =>
                    simp only [equation] at parsed
                    cases parsed
                | ok variables =>
                    simp only [equation] at parsed
                    cases variables <;>
                      repeat' first | (split at parsed) |
                        (simp only [pure, Except.pure] at parsed) | (cases parsed)
              · rw [if_neg letKind] at parsed
                by_cases expressionKind : kind = "YulExpressionStatement"
                · rw [if_pos expressionKind] at parsed
                  cases equation : (field node "expression") with
                  | error reason =>
                      simp only [equation] at parsed
                      cases parsed
                  | ok value =>
                      simp only [equation] at parsed
                      cases equation : (expressionAux fuel value) with
                      | error reason =>
                          simp only [equation] at parsed
                          cases parsed
                      | ok expression =>
                          simp only [equation] at parsed
                          cases parsed
                · rw [if_neg expressionKind] at parsed
                  by_cases ifKind : kind = "YulIf"
                  · rw [if_pos ifKind] at parsed
                    cases equation : (field node "condition") with
                    | error reason =>
                        simp only [equation] at parsed
                        cases parsed
                    | ok condition =>
                        simp only [equation] at parsed
                        cases equation : (expressionAux fuel condition) with
                        | error reason =>
                            simp only [equation] at parsed
                            cases parsed
                        | ok conditionTree =>
                            simp only [equation] at parsed
                            cases equation : (field node "body") with
                            | error reason =>
                                simp only [equation] at parsed
                                cases parsed
                            | ok body =>
                                simp only [equation] at parsed
                                cases equation : (blockAux fuel body) with
                                | error reason =>
                                    simp only [equation] at parsed
                                    cases parsed
                                | ok bodyTree =>
                                    simp only [equation] at parsed
                                    cases parsed
                  · rw [if_neg ifKind] at parsed
                    by_cases forKind : kind = "YulForLoop"
                    · rw [if_pos forKind] at parsed
                      cases equation : (field node "pre") with
                      | error reason =>
                          simp only [equation] at parsed
                          cases parsed
                      | ok pre =>
                          simp only [equation] at parsed
                          cases equation : (blockAux fuel pre) with
                          | error reason =>
                              simp only [equation] at parsed
                              cases parsed
                          | ok preTree =>
                              simp only [equation] at parsed
                              cases equation : (field node "condition") with
                              | error reason =>
                                  simp only [equation] at parsed
                                  cases parsed
                              | ok condition =>
                                  simp only [equation] at parsed
                                  cases equation : (expressionAux fuel condition) with
                                  | error reason =>
                                      simp only [equation] at parsed
                                      cases parsed
                                  | ok conditionTree =>
                                      simp only [equation] at parsed
                                      cases equation : (field node "post") with
                                      | error reason =>
                                          simp only [equation] at parsed
                                          cases parsed
                                      | ok post =>
                                          simp only [equation] at parsed
                                          cases equation : (blockAux fuel post) with
                                          | error reason =>
                                              simp only [equation] at parsed
                                              cases parsed
                                          | ok postTree =>
                                              simp only [equation] at parsed
                                              cases equation : (field node "body") with
                                              | error reason =>
                                                  simp only [equation] at parsed
                                                  cases parsed
                                              | ok body =>
                                                  simp only [equation] at parsed
                                                  cases equation : (blockAux fuel body) with
                                                  | error reason =>
                                                      simp only [equation] at parsed
                                                      cases parsed
                                                  | ok bodyTree =>
                                                      simp only [equation] at parsed
                                                      cases parsed
                    · rw [if_neg forKind] at parsed
                      by_cases switchKind : kind = "YulSwitch"
                      · rw [if_pos switchKind] at parsed
                        cases equation : (field node "expression") with
                        | error reason =>
                            simp only [equation] at parsed
                            cases parsed
                        | ok selector =>
                            simp only [equation] at parsed
                            cases equation : (expressionAux fuel selector) with
                            | error reason =>
                                simp only [equation] at parsed
                                cases parsed
                            | ok selectorTree =>
                                simp only [equation] at parsed
                                cases equation : (array node "cases") with
                                | error reason =>
                                    simp only [equation] at parsed
                                    cases parsed
                                | ok casesArray =>
                                    simp only [equation] at parsed
                                    split at parsed
                                    · cases parsed
                                    · cases equation : switchCases (blockAux fuel) casesArray.toList [] with
                                      | error reason =>
                                          simp only [equation] at parsed
                                          cases parsed
                                      | ok branches =>
                                          simp only [equation,pure,Except.pure] at parsed
                                          cases parsed
                      · rw [if_neg switchKind] at parsed
                        by_cases functionKind : kind = "YulFunctionDefinition"
                        · rw [if_pos functionKind] at parsed
                          cases equation : (string node "name") with
                          | error reason =>
                              simp only [equation] at parsed
                              cases parsed
                          | ok name =>
                              simp only [equation] at parsed
                              repeat' first | (split at parsed) |
                                (simp only [pure, Except.pure] at parsed) | (cases parsed)
                        · rw [if_neg functionKind] at parsed
                          split at parsed
                          · cases parsed
                          · split at parsed
                            · cases parsed
                            · split at parsed <;> cases parsed

/-- Exact target positions obtained from the actual successful statement decoder,
with the same intrinsic target derivation, without a supplied write-role flag. -/
theorem decoded_targets {X n E} (fuel : Nat) {node first rest rhs}
    (parsed : statementAux fuel node = .ok (.yulAssign first rest rhs))
    (typed : @TargetsD X n E (first::rest)) :
    TypingLeaves.All (fun path leaf => At node (path,leaf)) (TypingLeaves.targets typed []) := by
  have kind := assignment_kind fuel parsed
  cases fuel with
  | zero => cases parsed
  | succ fuel =>
      rw [statementAux] at parsed
      simp only [kind,bind,Except.bind] at parsed
      simp only [show ("YulAssignment" = "YulBlock") = False from propext (by decide),
        show ("YulAssignment" = "YulVariableDeclaration") = False from propext (by decide),
        if_false,if_true] at parsed
      cases valuesEq : array node "variableNames" with
      | error reason =>
          simp only [valuesEq] at parsed
          cases parsed
      | ok values =>
          simp only [valuesEq] at parsed
          cases pairsEq : values.toList.mapM identifierPath with
          | error reason =>
              simp only [pairsEq] at parsed
              cases parsed
          | ok pairs =>
              simp only [pairsEq] at parsed
              cases pathsEq : pairs.map (fun pair => pair.1::pair.2) with
              | nil =>
                  simp only [pathsEq,throw] at parsed
                  cases parsed
              | cons actualFirst actualRest =>
                  simp only [pathsEq] at parsed
                  cases valueEq : field node "value" with
                  | error reason =>
                      simp only [valueEq] at parsed
                      cases parsed
                  | ok value =>
                      simp only [valueEq] at parsed
                      cases rhsEq : expressionAux fuel value with
                      | error reason =>
                          simp only [rhsEq] at parsed
                          cases parsed
                      | ok actualRhs =>
                          simp only [rhsEq,pure,Except.pure] at parsed
                          cases parsed
                          have positions : ∀ paths,
                              pairs.map (fun pair => pair.1::pair.2) = paths →
                              ∀ derivation : TargetsD E paths,
                              TypingLeaves.All (fun path leaf => At node (path,leaf))
                                (TypingLeaves.targets derivation []) := by
                            intro paths same
                            cases same
                            intro derivation
                            exact targets_positions kind valuesEq pairsEq derivation
                          exact positions _ pathsEq typed

/-- Actual assignment decoder inversion. These are concrete successful
decoder facts, not a caller-supplied preparation law. -/
theorem decoded_assignment_fields (fuel : Nat) {node first rest rhs}
    (parsed : statementAux fuel node = .ok (.yulAssign first rest rhs))
    : ∃ childFuel, fuel = childFuel+1 ∧
      string node "nodeType" = .ok "YulAssignment" ∧
      ∃ values pairs value,
        array node "variableNames" = .ok values ∧
        values.toList.mapM identifierPath = .ok pairs ∧
        pairs.map (fun pair => pair.1::pair.2) = first::rest ∧
        field node "value" = .ok value ∧
        expressionAux childFuel value = .ok rhs := by
  have kind := assignment_kind fuel parsed
  cases fuel with
  | zero => cases parsed
  | succ fuel =>
      rw [statementAux] at parsed
      simp only [kind,bind,Except.bind] at parsed
      simp only [show ("YulAssignment" = "YulBlock") = False from propext (by decide),
        show ("YulAssignment" = "YulVariableDeclaration") = False from propext (by decide),
        if_false,if_true] at parsed
      cases valuesEq : array node "variableNames" with
      | error reason =>
          simp only [valuesEq] at parsed
          cases parsed
      | ok values =>
          simp only [valuesEq] at parsed
          cases pairsEq : values.toList.mapM identifierPath with
          | error reason =>
              simp only [pairsEq] at parsed
              cases parsed
          | ok pairs =>
              simp only [pairsEq] at parsed
              cases pathsEq : pairs.map (fun pair => pair.1::pair.2) with
              | nil =>
                  simp only [pathsEq,throw] at parsed
                  cases parsed
              | cons actualFirst actualRest =>
                  simp only [pathsEq] at parsed
                  cases valueEq : field node "value" with
                  | error reason =>
                      simp only [valueEq] at parsed
                      cases parsed
                  | ok value =>
                      simp only [valueEq] at parsed
                      cases rhsEq : expressionAux fuel value with
                      | error reason =>
                          simp only [rhsEq] at parsed
                          cases parsed
                      | ok actualRhs =>
                          simp only [rhsEq,pure,Except.pure] at parsed
                          cases parsed
                          exact ⟨fuel,rfl,kind,values,pairs,value,rfl,pairsEq,pathsEq,rfl,rhsEq⟩

end Solidity.Frontend.YulJson.TargetPath
