import Solidity.Frontend.SolcJson.YulControlFields
import Solidity.Frontend.SolcJson.YulStatementTrace

/-! Concrete child-position composition with the SAME original typed parent.
All contexts/subderivations are extracted from that parent. These are static
positions, not execution, Source provenance or recursive leaf adequacy. -/
namespace Solidity.Frontend.YulJson.TypedChildren
open Lean (Json)
open Solidity.Yul
open Solidity.Yul.BlockTyping (Env)
open Solidity.Yul.ScopedBlockTyping

abbrev Reads {X scope F n E term count} (node : Json)
    (typed : @BlockScope.ExpressionD X F n scope E term count) : Prop :=
  TypingLeaves.All (fun path leaf => Nonempty (ExpressionPath.Witness node (path,leaf)))
    (TypingLeaves.reads (TypingLeaves.expressionInput scope E typed).2 [])

abbrev Blocks {X scope F n E c body} (fuel : Nat) (node : Json)
    (typed : @BlockD X scope F n E c body) : Prop :=
  TypingStatements.All (fun ordinal item => Nonempty (BlockPath.Witness fuel node (ordinal,item)))
    (TypingStatements.block typed)

theorem decoded_reads {X scope F n E term count} (fuel : Nat) {node}
    (parsed : expressionAux fuel node = .ok term)
    (typed : @BlockScope.ExpressionD X F n scope E term count) : Reads node typed := by
  intro entry present
  exact (ExpressionPath.decoded_paths fuel parsed
    (TypingLeaves.expressionInput scope E typed).2 entry present).witness

/-- Nested block statement consumes a decoder edge but retains the same JSON
node. The actual typed child block may hoist its own functions. -/
theorem block_positions {X scope F n E c body} (fuel : Nat) {node}
    (parsed : statementAux fuel node = .ok (.yulBlock body))
    (typed : @StatementD X scope F n E c (.yulBlock body) n E) :
    ∃ childFuel, ∃ child : BlockD scope E c body,
      fuel = childFuel+1 ∧ blockAux childFuel node = .ok body ∧
      typed = .block child ∧ Blocks childFuel node child := by
  cases typed with
  | block child =>
      obtain ⟨childFuel,horizon,_,decoded⟩ := ControlFields.block_fields fuel parsed
      exact ⟨childFuel,child,horizon,decoded,rfl,BlockPath.decoded_block childFuel decoded child⟩

/-- Function child contexts are the original frame and actual globals
projection, including closed scopes staying closed. No reconstructed frame. -/
theorem function_positions {X scope F n E c name args rets body} (fuel : Nat) {node}
    (parsed : statementAux fuel node = .ok (.yulFun name args rets body))
    (typed : @StatementD X scope F n E c (.yulFun name args rets body) n E) :
    ∃ childFuel bodyNode,
    ∃ child : BlockD scope.function (Env.frame E args rets) ⟨true,false⟩ body,
      fuel = childFuel+1 ∧ field node "body" = .ok bodyNode ∧
      blockAux childFuel bodyNode = .ok body ∧ typed = .function child ∧
      Blocks childFuel bodyNode child := by
  cases typed with
  | function child =>
      obtain ⟨childFuel,horizon,_,_,_,_,bodyNode,bodyEq,decoded⟩ :=
        ControlFields.function_fields fuel parsed
      exact ⟨childFuel,bodyNode,child,horizon,bodyEq,decoded,rfl,
        BlockPath.decoded_block childFuel decoded child⟩

/-- The if condition and body retain their actual SAME original parent
subderivations and environment, including the condition's exact arity. -/
theorem if_positions {X scope F n E c condition body} (fuel : Nat) {node}
    (parsed : statementAux fuel node = .ok (.yulIf condition body))
    (typed : @StatementD X scope F n E c (.yulIf condition body) n E) :
    ∃ childFuel conditionNode bodyNode,
    ∃ conditionTyped : BlockScope.ExpressionD scope E condition 1,
    ∃ bodyTyped : BlockD scope E c body,
      fuel = childFuel+1 ∧ field node "condition" = .ok conditionNode ∧
      expressionAux childFuel conditionNode = .ok condition ∧
      field node "body" = .ok bodyNode ∧ blockAux childFuel bodyNode = .ok body ∧
      typed = .if_ conditionTyped bodyTyped ∧
      (TypingLeaves.expressionInput scope E conditionTyped).1 = 1 ∧
      Reads conditionNode conditionTyped ∧ Blocks childFuel bodyNode bodyTyped := by
  cases typed with
  | if_ conditionTyped bodyTyped =>
      obtain ⟨childFuel,horizon,_,conditionNode,bodyNode,conditionEq,conditionDecoded,bodyEq,bodyDecoded⟩ :=
        ControlFields.if_fields fuel parsed
      exact ⟨childFuel,conditionNode,bodyNode,conditionTyped,bodyTyped,
        horizon,conditionEq,conditionDecoded,bodyEq,bodyDecoded,rfl,
        TypingLeaves.expressionInput_count scope E conditionTyped,
        decoded_reads childFuel conditionDecoded conditionTyped,
        BlockPath.decoded_block childFuel bodyDecoded bodyTyped⟩

/-- Expression statement child reads use the actual zero-result parent
subderivation. Decoder success alone does not establish zero-result typing. -/
theorem expression_positions {X scope F n E c value} (fuel : Nat) {node}
    (parsed : statementAux fuel node = .ok (.yulExprStmt value))
    (typed : @StatementD X scope F n E c (.yulExprStmt value) n E) :
    ∃ childFuel expressionNode,
    ∃ child : BlockScope.ExpressionD scope E value 0,
      fuel = childFuel+1 ∧ field node "expression" = .ok expressionNode ∧
      expressionAux childFuel expressionNode = .ok value ∧ typed = .expression child ∧
      (TypingLeaves.expressionInput scope E child).1 = 0 ∧ Reads expressionNode child := by
  cases typed with
  | expression child =>
      obtain ⟨childFuel,horizon,_,expressionNode,fieldEq,decoded⟩ :=
        ControlFields.expression_fields fuel parsed
      exact ⟨childFuel,expressionNode,child,horizon,fieldEq,decoded,rfl,
        TypingLeaves.expressionInput_count scope E child,decoded_reads childFuel decoded child⟩

/-- The original scoped assignment supplies actual read/write environments
and certificates. No abstract assignment coherence premise is introduced. -/
theorem assignment_positions {X scope F n E c first rest rhs} (fuel : Nat) {node}
    (parsed : statementAux fuel node = .ok (.yulAssign first rest rhs))
    (typed : @StatementD X scope F n E c (.yulAssign first rest rhs) n E) :
    ∃ child : BlockScope.AssignmentD scope E (first::rest) rhs,
      typed = .assignment child ∧
      TypingLeaves.All (fun path leaf => Nonempty (AssignmentPath.Witness node (path,leaf)))
        (TypingLeaves.reads (TypingLeaves.assignmentReads scope E child) []) ∧
      TypingLeaves.All (fun path leaf => Nonempty (TargetPath.Witness node (path,leaf)))
        (TypingLeaves.targets (TypingLeaves.assignmentTargets scope E child) []) := by
  cases typed with
  | assignment child =>
      refine ⟨child,rfl,?_,?_⟩
      · intro entry present
        exact (AssignmentPath.decoded_reads fuel parsed
          (TypingLeaves.assignmentReads scope E child) entry present).witness
      · intro entry present
        exact (TargetPath.decoded_targets fuel parsed
          (TypingLeaves.assignmentTargets scope E child) entry present).witness

/-- The selector uses the SAME outer environment and original parent
certificate. Cases, distinct labels and fallback are preserved, not replaced
by newly checked lookalikes. Case-body positions are a separate obligation. -/
theorem switch_selector {X scope F n E c selector cases fallback} (fuel : Nat) {node}
    (parsed : statementAux fuel node = .ok (.yulSwitch selector cases fallback))
    (typed : @StatementD X scope F n E c (.yulSwitch selector cases fallback) n E) :
    ∃ childFuel selectorNode values labels,
    ∃ guard : BlockScope.ExpressionD scope E selector 1,
    ∃ arms : CasesD scope E c cases labels,
    ∃ distinct : labels.Nodup,
    ∃ otherwise : DefaultD scope E c fallback,
      fuel = childFuel+1 ∧
      field node "expression" = .ok selectorNode ∧
      expressionAux childFuel selectorNode = .ok selector ∧
      array node "cases" = .ok values ∧ values.isEmpty = false ∧
      switchCases (blockAux childFuel) values.toList [] = .ok (cases,fallback) ∧
      typed = .switch guard arms distinct otherwise ∧
      (TypingLeaves.expressionInput scope E guard).1 = 1 ∧ Reads selectorNode guard := by
  cases typed with
  | switch guard arms distinct otherwise =>
      obtain ⟨childFuel,horizon,_,selectorNode,values,fieldEq,decoded,valuesEq,nonempty,casesEq⟩ :=
        ControlFields.switch_fields fuel parsed
      exact ⟨childFuel,selectorNode,values,_,guard,arms,distinct,otherwise,
        horizon,fieldEq,decoded,valuesEq,nonempty,casesEq,rfl,
        TypingLeaves.expressionInput_count scope E guard,decoded_reads childFuel decoded guard⟩

/-- Actual positions for a supplied successful default tail. The original
fallback certificate supplies the body context; this does not infer a global
switch-array index or facts about earlier cases. -/
theorem default_positions {X scope F n E c body} (fuel : Nat) {node rest seen}
    (valueEq : field node "value" = .ok (.str "default"))
    (parsed : switchCases (blockAux fuel) (node::rest) seen = .ok (.nil,.some body))
    (typed : @DefaultD X scope F n E c (.some body)) :
    ∃ bodyNode, ∃ child : BlockD scope E c body,
      rest = [] ∧ requireNode node "YulCase" = .ok () ∧
      field node "body" = .ok bodyNode ∧ blockAux fuel bodyNode = .ok body ∧
      typed = .some child ∧ Blocks fuel bodyNode child := by
  cases typed with
  | some child =>
      obtain ⟨last,kind,bodyNode,decodedBody,fieldEq,decoded,_,same⟩ :=
        ControlFields.default_fields fuel valueEq parsed
      cases same
      exact ⟨bodyNode,child,last,kind,fieldEq,decoded,rfl,
        BlockPath.decoded_block fuel decoded child⟩

/-- Ordinary supplied-tail body positions with the original CaseD, including
agreement between the parser's literal word and its independent derivation. -/
theorem case_positions {X scope F n E c label body word remaining fallback}
    (fuel : Nat) {node rest seen value}
    (valueEq : field node "value" = .ok value)
    (ordinary : value ≠ .str "default")
    (parsed : switchCases (blockAux fuel) (node::rest) seen =
      .ok (.cons (.yulCase label body) remaining,fallback))
    (typed : @CaseD X scope F n E c (.yulCase label body) word) :
    ∃ decoded : Literal, ∃ bodyNode,
    ∃ literalTyped : LiteralD label word, ∃ child : BlockD scope E c body,
      requireNode node "YulCase" = .ok () ∧ literal value = .ok decoded ∧
      decoded.tree = label ∧ decoded.value = word ∧
      seen.contains decoded.value = false ∧ field node "body" = .ok bodyNode ∧
      blockAux fuel bodyNode = .ok body ∧
      switchCases (blockAux fuel) rest (decoded.value::seen) = .ok (remaining,fallback) ∧
      typed = .case_ literalTyped child ∧ Blocks fuel bodyNode child := by
  obtain ⟨kind,decoded,bodyNode,decodedBody,decodedRemaining,literalEq,notSeen,
    fieldEq,bodyEq,restEq,same⟩ := ControlFields.case_fields fuel valueEq ordinary parsed
  cases same
  cases typed with
  | case_ literalTyped child =>
      have agrees : decoded.value = word := by
        have same := decoded.derivation.complete.symm.trans literalTyped.complete
        exact congrArg (fun pair => pair.1) (Option.some.inj same)
      exact ⟨decoded,bodyNode,literalTyped,child,kind,literalEq,rfl,agrees,
        notSeen,fieldEq,bodyEq,restEq,rfl,BlockPath.decoded_block fuel bodyEq child⟩

/-- Category-generalized option metadata observer. Only the .some
constructor contributes; no indexed equation-compiler match is generated. -/
def syntaxOptionCount {category} (tree : Solidity.Source.Syn category) : Nat := by
  apply Solidity.Source.Syn.casesOn (motive := fun category _ => Nat) tree
  case some => intros; exact 1
  all_goals intros; exact 0

/-- Metadata count of the optional default syntax, not a runtime value. -/
abbrev defaultCount : Solidity.Source.Syn (.opt (.list .yulStmt)) → Nat :=
  syntaxOptionCount

/-- Actual raw case-array length accounts for the elided default. Labels are
from the original independent CasesD, not a parser-computed replacement. -/
theorem cases_length {X scope F n E c cases labels fallback} (fuel : Nat) (nodes : List Json)
    {seen} (parsed : switchCases (blockAux fuel) nodes seen = .ok (cases,fallback))
    (typed : @CasesD X scope F n E c cases labels) :
    nodes.length = labels.length + defaultCount fallback := by
  induction nodes generalizing seen cases labels fallback with
  | nil =>
      change (Except.ok (.nil,.none) :
        Except Error (Solidity.Source.Syn (.list .yulCase) ×
          Solidity.Source.Syn (.opt (.list .yulStmt)))) = .ok (cases,fallback) at parsed
      cases parsed
      cases typed
      rfl
  | cons node rest ih =>
      obtain ⟨_,value,valueEq⟩ := ControlFields.case_value fuel parsed
      by_cases isDefault : value = .str "default"
      · subst value
        obtain ⟨last,_,_,body,_,_,casesEq,fallbackEq⟩ :=
          ControlFields.default_fields fuel valueEq parsed
        cases last
        cases casesEq
        cases fallbackEq
        cases typed
        rfl
      · obtain ⟨_,decoded,_,body,remaining,_,_,_,_,restEq,casesEq⟩ :=
          ControlFields.case_fields fuel valueEq isDefault parsed
        cases casesEq
        cases typed with
        | cons first tail =>
            have smaller := ih restEq tail
            simp only [List.length_cons]
            omega

/-- Proof membership in the SAME original case-list certificate. This is
metadata over intrinsic CaseD, not another syntax representation. -/
inductive CaseAt {X} (scope : BlockScope.Scope X) {F n}
    (E : Solidity.Yul.BlockTyping.Env F n) (c : Control) :
    {terms : Solidity.Source.Syn (.list .yulCase)} → {labels : List Word} →
    CasesD scope E c terms labels → Nat → {term : Solidity.Source.Syn .yulCase} →
    {word : Word} → CaseD scope E c term word → Prop where
  | head {term word rest words} (first : CaseD scope E c term word)
      (tail : CasesD scope E c rest words) : CaseAt scope E c (.cons first tail) 0 first
  | tail {term word rest words selected selectedWord ordinal}
      (first : CaseD scope E c term word) (tail : CasesD scope E c rest words)
      (chosen : CaseD scope E c selected selectedWord)
      (position : CaseAt scope E c tail ordinal chosen) :
      CaseAt scope E c (.cons first tail) (ordinal+1) chosen

theorem CaseAt.bound {X scope F n E c terms labels ordinal term word}
    {typed : @CasesD X scope F n E c terms labels}
    {chosen : CaseD scope E c term word}
    (position : CaseAt scope E c typed ordinal chosen) : ordinal < labels.length := by
  induction position with
  | head first tail => exact Nat.zero_lt_succ _
  | tail first tail chosen position ih =>
      simp only [List.length_cons]
      omega

/-- Every original typed-label ordinal has a member from that SAME certificate. -/
theorem CaseAt.total {X scope F n E c terms labels}
    (typed : @CasesD X scope F n E c terms labels)
    (ordinal : Nat) (bound : ordinal < labels.length) :
    ∃ term word, ∃ chosen : CaseD scope E c term word, CaseAt scope E c typed ordinal chosen := by
  induction ordinal generalizing terms labels with
  | zero =>
      cases typed with
      | nil => cases bound
      | cons first tail => exact ⟨_,_,first,.head first tail⟩
  | succ ordinal ih =>
      cases typed with
      | nil => cases bound
      | cons first tail =>
          obtain ⟨term,word,chosen,position⟩ := ih tail (Nat.lt_of_succ_lt_succ bound)
          exact ⟨term,word,chosen,.tail first tail chosen position⟩

/-- Exact raw list entry and original intrinsic case/body certificate.
HEq retains the full original certificate while tree records its actual shape.
All positions here are relative to the supplied case list/body. -/
structure CaseWitness {X scope F n E c term word}
    (fuel : Nat) (nodes : List Json) (ordinal : Nat)
    (chosen : @CaseD X scope F n E c term word) where
  index : Fin nodes.length
  position : index.val = ordinal
  valueNode : Json
  kind : requireNode nodes[index] "YulCase" = .ok ()
  valueEq : field nodes[index] "value" = .ok valueNode
  ordinary : valueNode ≠ .str "default"
  decoded : Literal
  literalEq : literal valueNode = .ok decoded
  label : Solidity.Source.YulLit
  body : Solidity.Source.Syn (.list .yulStmt)
  tree : term = .yulCase label body
  labelEq : decoded.tree = label
  wordEq : decoded.value = word
  bodyNode : Json
  fieldEq : field nodes[index] "body" = .ok bodyNode
  decodedBody : blockAux fuel bodyNode = .ok body
  literalTyped : LiteralD label word
  bodyTyped : BlockD scope E c body
  original : HEq chosen (CaseD.case_ literalTyped bodyTyped)
  positions : Blocks fuel bodyNode bodyTyped

/-- Every member of the original case certificate has its actual raw ordinal,
literal word and SAME body certificate, derived from the real decoder. -/
theorem CaseAt.raw {X scope F n E c terms labels ordinal term word}
    {typed : @CasesD X scope F n E c terms labels}
    {chosen : CaseD scope E c term word}
    (position : CaseAt scope E c typed ordinal chosen)
    (fuel : Nat) (nodes : List Json) {seen fallback}
    (parsed : switchCases (blockAux fuel) nodes seen = .ok (terms,fallback)) :
    Nonempty (CaseWitness fuel nodes ordinal chosen) := by
  induction position generalizing nodes seen fallback with
  | head first tail =>
      cases nodes with
      | nil => cases parsed
      | cons node rest =>
          cases first with
          | case_ literalTyped bodyTyped =>
              obtain ⟨value,valueEq,ordinary,_,_,_,_,_,_,_,_,_,_⟩ :=
                ControlFields.cons_fields fuel parsed
              obtain ⟨decoded,bodyNode,labelChild,bodyChild,kind,literalEq,labelEq,wordEq,
                _,fieldEq,decodedBody,_,original,positions⟩ :=
                case_positions fuel valueEq ordinary parsed (.case_ literalTyped bodyTyped)
              exact ⟨{
                index := ⟨0,Nat.zero_lt_succ _⟩,
                position := rfl,
                valueNode := value,
                kind := kind,
                valueEq := valueEq,
                ordinary := ordinary,
                decoded := decoded,
                literalEq := literalEq,
                label := _,
                body := _,
                tree := rfl,
                labelEq := labelEq,
                wordEq := wordEq,
                bodyNode := bodyNode,
                fieldEq := fieldEq,
                decodedBody := decodedBody,
                literalTyped := labelChild,
                bodyTyped := bodyChild,
                original := heq_of_eq original,
                positions := positions}⟩
  | tail first tail chosen position ih =>
      cases nodes with
      | nil => cases parsed
      | cons node rest =>
          obtain ⟨_,_,_,_,_,_,_,_,_,_,_,restEq,_⟩ := ControlFields.cons_fields fuel parsed
          obtain ⟨witness⟩ := ih rest restEq
          exact ⟨{
            index := ⟨witness.index.val+1,Nat.succ_lt_succ witness.index.isLt⟩,
            position := congrArg Nat.succ witness.position,
            valueNode := witness.valueNode,
            kind := witness.kind,
            valueEq := witness.valueEq,
            ordinary := witness.ordinary,
            decoded := witness.decoded,
            literalEq := witness.literalEq,
            label := witness.label,
            body := witness.body,
            tree := witness.tree,
            labelEq := witness.labelEq,
            wordEq := witness.wordEq,
            bodyNode := witness.bodyNode,
            fieldEq := witness.fieldEq,
            decodedBody := witness.decodedBody,
            literalTyped := witness.literalTyped,
            bodyTyped := witness.bodyTyped,
            original := witness.original,
            positions := witness.positions}⟩

/-- Concrete coverage of every original typed-label ordinal. -/
theorem CaseAt.raw_total {X scope F n E c terms labels}
    (typed : @CasesD X scope F n E c terms labels)
    (fuel : Nat) (nodes : List Json) {seen fallback}
    (parsed : switchCases (blockAux fuel) nodes seen = .ok (terms,fallback))
    (ordinal : Nat) (bound : ordinal < labels.length) :
    ∃ term word, ∃ chosen : CaseD scope E c term word,
      CaseAt scope E c typed ordinal chosen ∧ Nonempty (CaseWitness fuel nodes ordinal chosen) := by
  obtain ⟨term,word,chosen,position⟩ := CaseAt.total typed ordinal bound
  exact ⟨term,word,chosen,position,position.raw fuel nodes parsed⟩

/-- Actual parent switch composition for all ordinary cases. The raw list
is exactly the parent's cases array, not a caller-prepared collection. -/
theorem switch_cases {X scope F n E c selector cases fallback} (fuel : Nat) {node}
    (parsed : statementAux fuel node = .ok (.yulSwitch selector cases fallback))
    (typed : @StatementD X scope F n E c (.yulSwitch selector cases fallback) n E) :
    ∃ childFuel selectorNode values labels,
    ∃ guard : BlockScope.ExpressionD scope E selector 1,
    ∃ arms : CasesD scope E c cases labels, ∃ distinct : labels.Nodup,
    ∃ otherwise : DefaultD scope E c fallback,
      fuel = childFuel+1 ∧ field node "expression" = .ok selectorNode ∧
      expressionAux childFuel selectorNode = .ok selector ∧
      array node "cases" = .ok values ∧ values.isEmpty = false ∧
      typed = .switch guard arms distinct otherwise ∧
      Reads selectorNode guard ∧
      (∀ ordinal term word (chosen : CaseD scope E c term word),
        CaseAt scope E c arms ordinal chosen →
        Nonempty (CaseWitness childFuel values.toList ordinal chosen)) ∧
      values.size = labels.length + defaultCount fallback := by
  obtain ⟨childFuel,selectorNode,values,labels,guard,arms,distinct,otherwise,
    horizon,fieldEq,decoded,valuesEq,nonempty,casesEq,parentEq,_,reads⟩ :=
    switch_selector fuel parsed typed
  refine ⟨childFuel,selectorNode,values,labels,guard,arms,distinct,otherwise,
    horizon,fieldEq,decoded,valuesEq,nonempty,parentEq,reads,?_,?_⟩
  · intro ordinal term word chosen position
    exact position.raw childFuel values.toList casesEq
  · simpa only [Array.length_toList] using cases_length childFuel values.toList casesEq arms

/-- Exact raw default ordinal and SAME original fallback/body certificate. -/
structure DefaultWitness {X scope F n E c body}
    (fuel : Nat) (nodes : List Json) (ordinal : Nat)
    (typed : @DefaultD X scope F n E c (.some body)) where
  index : Fin nodes.length
  position : index.val = ordinal
  kind : requireNode nodes[index] "YulCase" = .ok ()
  valueEq : field nodes[index] "value" = .ok (.str "default")
  bodyNode : Json
  fieldEq : field nodes[index] "body" = .ok bodyNode
  decoded : blockAux fuel bodyNode = .ok body
  child : BlockD scope E c body
  original : typed = .some child
  positions : Blocks fuel bodyNode child

/-- The default's actual raw ordinal is the ORIGINAL typed-label count. -/
theorem default_index {X scope F n E c cases labels body}
    (arms : @CasesD X scope F n E c cases labels)
    (typed : DefaultD scope E c (.some body))
    (fuel : Nat) (nodes : List Json) {seen}
    (parsed : switchCases (blockAux fuel) nodes seen = .ok (cases,.some body)) :
    Nonempty (DefaultWitness fuel nodes labels.length typed) := by
  induction labels generalizing cases nodes seen with
  | nil =>
      cases arms
      cases nodes with
      | nil => cases parsed
      | cons node rest =>
          obtain ⟨_,value,valueEq⟩ := ControlFields.case_value fuel parsed
          have isDefault : value = .str "default" := by
            by_cases ordinary : value = .str "default"
            · exact ordinary
            · obtain ⟨_,_,_,_,_,_,_,_,_,_,impossible⟩ :=
                ControlFields.case_fields fuel valueEq ordinary parsed
              cases impossible
          cases isDefault
          obtain ⟨bodyNode,child,last,kind,fieldEq,decoded,original,positions⟩ :=
            default_positions fuel valueEq parsed typed
          cases last
          exact ⟨{
            index := ⟨0,Nat.zero_lt_succ _⟩,
            position := rfl,
            kind := kind,
            valueEq := valueEq,
            bodyNode := bodyNode,
            fieldEq := fieldEq,
            decoded := decoded,
            child := child,
            original := original,
            positions := positions}⟩
  | cons word words ih =>
      cases arms with
      | cons first tail =>
          cases nodes with
          | nil => cases parsed
          | cons node rest =>
              obtain ⟨_,_,_,_,_,_,_,_,_,_,_,restEq,_⟩ :=
                ControlFields.cons_fields fuel parsed
              obtain ⟨witness⟩ := ih tail rest restEq
              exact ⟨{
                index := ⟨witness.index.val+1,Nat.succ_lt_succ witness.index.isLt⟩,
                position := congrArg Nat.succ witness.position,
                kind := witness.kind,
                valueEq := witness.valueEq,
                bodyNode := witness.bodyNode,
                fieldEq := witness.fieldEq,
                decoded := witness.decoded,
                child := witness.child,
                original := witness.original,
                positions := witness.positions}⟩

/-- Ordinary members and the default occupy different actual raw entries. -/
theorem CaseWitness.not_default {X scope F n E c terms labels ordinal term word body fuel nodes}
    {arms : @CasesD X scope F n E c terms labels}
    {chosen : CaseD scope E c term word}
    {typedDefault : DefaultD scope E c (.some body)}
    (member : CaseAt scope E c arms ordinal chosen)
    (one : CaseWitness fuel nodes ordinal chosen)
    (two : DefaultWitness fuel nodes labels.length typedDefault) :
    one.index.val ≠ two.index.val := by
  have bound := member.bound
  have first := one.position
  have last := two.position
  omega

/-- All ordinary cases and the optional-default case are tied to the SAME
actual parent, actual case array and original typing subcertificates. -/
theorem switch_with_default {X scope F n E c selector cases body} (fuel : Nat) {node}
    (parsed : statementAux fuel node = .ok (.yulSwitch selector cases (.some body)))
    (typed : @StatementD X scope F n E c (.yulSwitch selector cases (.some body)) n E) :
    ∃ childFuel selectorNode values labels,
    ∃ guard : BlockScope.ExpressionD scope E selector 1,
    ∃ arms : CasesD scope E c cases labels, ∃ distinct : labels.Nodup,
    ∃ otherwise : DefaultD scope E c (.some body),
      fuel = childFuel+1 ∧ field node "expression" = .ok selectorNode ∧
      expressionAux childFuel selectorNode = .ok selector ∧
      array node "cases" = .ok values ∧ values.isEmpty = false ∧
      typed = .switch guard arms distinct otherwise ∧ Reads selectorNode guard ∧
      (∀ ordinal term word (chosen : CaseD scope E c term word),
        CaseAt scope E c arms ordinal chosen →
        Nonempty (CaseWitness childFuel values.toList ordinal chosen)) ∧
      Nonempty (DefaultWitness childFuel values.toList labels.length otherwise) ∧
      values.size = labels.length+1 := by
  obtain ⟨childFuel,selectorNode,values,labels,guard,arms,distinct,otherwise,
    horizon,fieldEq,decoded,valuesEq,nonempty,casesEq,parentEq,_,reads⟩ :=
    switch_selector fuel parsed typed
  refine ⟨childFuel,selectorNode,values,labels,guard,arms,distinct,otherwise,
    horizon,fieldEq,decoded,valuesEq,nonempty,parentEq,reads,?_,
    default_index arms otherwise childFuel values.toList casesEq,?_⟩
  · intro ordinal term word chosen position
    exact position.raw childFuel values.toList casesEq
  · simpa only [Array.length_toList,defaultCount,syntaxOptionCount] using
      cases_length childFuel values.toList casesEq arms

end Solidity.Frontend.YulJson.TypedChildren
