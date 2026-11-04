import Solidity.Frontend.Source

/-! Structural solc invocation metadata. The checked input is the same profile,
declaration table and call node, not a function-name or purity-only issuer.
Compiler authenticity and Source/native execution correspondence remain outside
this JSON check. Refusal withholds refinement, not an existing call outcome. -/
namespace Solidity.Frontend.CallMetadata
open Lean (Json)

inductive Refusal where
  | profile | callShape | site | declaration | functionKind | name
  | visibility | mutability | arity | receiver
  deriving Repr, DecidableEq

/-- A single-source profile is bound to its original fixture and the existing
provenance reader. Schema-2 units currently withhold this refinement; their
existing ordinary-call admission remains unchanged. -/
structure Profile where
  fixture : Json
  ast : Json
  provenance : Source.Provenance
  astAt : fixture.getObjVal? "ast" = .ok ast
  accepted : Source.read fixture ast = .ok provenance

def readProfile (fixture : Json) : Except Refusal Profile :=
  match ha : fixture.getObjVal? "ast" with
  | .error _ => .error .profile
  | .ok ast => match hp : Source.read fixture ast with
    | .error _ => .error .profile
    | .ok provenance => .ok ⟨fixture,ast,provenance,ha,hp⟩

private def str? (j : Json) (key : String) : Option String :=
  (j.getObjValAs? String key).toOption
private def int? (j : Json) (key : String) : Option Int :=
  (j.getObjValAs? Int key).toOption
private def obj? (j : Json) (key : String) : Option Json := (j.getObjVal? key).toOption
private def arr? (j : Json) (key : String) : Option (Array Json) :=
  (j.getObjValAs? (Array Json) key).toOption
private def ty (j : Json) : String :=
  ((obj? j "typeDescriptions").bind (str? · "typeString")).getD ""

/-- Use total character/list operations: String.splitOn is opaque in kernel
reduction in this toolchain. No parser or proof budget is enlarged. -/
private def words (s : String) : List String :=
  (s.toList.foldr (fun c rest =>
    if c == ' ' then [] :: rest else
      match rest with
      | [] => [[c]]
      | word :: words => (c :: word) :: words) [[]]).map String.mk

/-- Read only the function-type envelope, leaving parameter/return ABI types
uninterpreted. Qualifiers must occupy the outer segment; unknown, duplicate,
contradictory or misplaced qualifiers withhold refinement. -/
def outerQualifiers? (s : String) : Option (List String) := do
  let rec close (stack : List Char) : List Char → Option (List Char)
    | [] => none
    | c :: cs =>
      if c == '(' then close (')' :: stack) cs
      else if c == '[' then close (']' :: stack) cs
      else if c == ')' || c == ']' then
        match stack with
        | [] => none
        | expected :: rest =>
          if c != expected then none else
          if rest.isEmpty then some cs else close rest cs
      else close stack cs
  let trim := fun cs : List Char => cs.dropWhile Char.isWhitespace
  unless s.toList.take 9 == "function ".toList do none
  let '(' :: parameters := trim (s.toList.drop 9) | none
  let rest ← close [')'] parameters
  let text := rest.takeWhile (fun c => c != '(' && c != '[' && c != ')' && c != ']')
  let qualifiers := (words (String.mk text)).filter (· != "")
  let suffix := trim (rest.drop text.length)
  let (qualifiers, returns) ← match suffix with
    | [] => pure (qualifiers,false)
    | '(' :: results => do
      let tail ← close [')'] results
      unless (trim tail).isEmpty do none
      let "returns" :: qualifierTail := qualifiers.reverse | none
      pure (qualifierTail.reverse,true)
    | _ => none
  let valid := match qualifiers with
    | ["external"] => true
    | [mutability,"external"] | ["external",mutability] =>
      ["pure","view","payable"].contains mutability
    | _ => false
  unless valid do none
  return "function" :: qualifiers ++ (if returns then ["returns"] else [])

/-- Pre-Byzantium targets retain CALL even for readonly declarations. Unknown
or historical settings do not establish an operational discriminator. -/
def staticTarget? (p : Profile) : Option Bool := do
  let .analysed _ _ := p.provenance.compilation | none
  let header ← obj? p.fixture "header"
  let settings ← obj? header "settings"
  let evm ← str? settings "evmVersion"
  if ["homestead", "tangerineWhistle", "spuriousDragon"].contains evm then
    return false
  if ["byzantium", "constantinople", "petersburg", "istanbul", "berlin",
      "london", "paris", "shanghai", "cancun", "prague", "osaka"].contains evm then
    return true
  none

structure Info where
  profile : Profile
  call : Json
  declaration : Json
  site : Nat
  declarationId : Int
  sourceName : String
  targetIsStatic : Bool
  targetAt : staticTarget? profile = some targetIsStatic
  mutability : String
  mutabilityAt : (declaration.getObjValAs? String "stateMutability").toOption = some mutability

def Info.isStatic (info : Info) : Bool :=
  info.targetIsStatic && ["pure", "view"].contains info.mutability

private def candidate (profile : Option Profile) (declarations : List Json)
    (call : Json) : Except Refusal { info : Info // info.declaration ∈ declarations } := do
  let some profile := profile | throw .profile
  match ht : staticTarget? profile with
  | none => throw .profile
  | some staticTarget => do
    unless str? call "nodeType" == some "FunctionCall" &&
        str? call "kind" == some "functionCall" do throw .callShape
    let some site := int? call "id" | throw .site
    if site < 0 then throw .site
    let some callee := obj? call "expression" | throw .callShape
    let some tokens := outerQualifiers? (ty callee) | throw .callShape
    unless str? callee "nodeType" == some "MemberAccess" &&
        (ty callee).toList.take 9 == "function ".toList &&
        tokens.contains "external" && !tokens.contains "internal" do throw .callShape
    let some receiver := obj? callee "expression" | throw .receiver
    -- Namespace/library calls are not contract-value STATICCALL sites.
    unless (ty receiver).toList.take 9 == "contract ".toList do throw .receiver
    let some reference := int? callee "referencedDeclaration" | throw .declaration
    if reference < 0 then throw .declaration
    let selectedNodes := declarations.filter (fun d => int? d "id" == some reference)
    let declaration ← match h : selectedNodes with
      | [d] => pure (⟨d, by
          have hm : d ∈ selectedNodes := by simp only [h, List.mem_singleton]
          exact (List.mem_filter.mp hm).1⟩ : { d : Json // d ∈ declarations })
      | _ => throw .declaration
    let selected := declaration.property
    let declaration := declaration.val
    unless str? declaration "nodeType" == some "FunctionDefinition" &&
        str? declaration "kind" == some "function" do throw .functionKind
    let some name := str? declaration "name" | throw .name
    unless !name.isEmpty && str? callee "memberName" == some name do throw .name
    unless [some "external", some "public"].contains (str? declaration "visibility") do
      throw .visibility
    match hm : str? declaration "stateMutability" with
    | none => throw .mutability
    | some mutability => do
      unless ["pure", "view", "nonpayable", "payable"].contains mutability do throw .mutability
      unless tokens.contains "pure" == (mutability == "pure") &&
          tokens.contains "view" == (mutability == "view") &&
          tokens.contains "payable" == (mutability == "payable") do throw .mutability
      let some arguments := arr? call "arguments" | throw .arity
      let some parameters := (obj? declaration "parameters").bind (arr? · "parameters")
        | throw .arity
      unless arguments.size == parameters.size do throw .arity
      return ⟨{
        profile := profile
        call := call
        declaration := declaration
        site := site.toNat
        declarationId := reference
        sourceName := name
        targetIsStatic := staticTarget
        targetAt := ht
        mutability := mutability
        mutabilityAt := hm }, selected⟩


def inspect (profile : Option Profile) (declarations : List Json) (call : Json) :
    Except Refusal Info :=
  (candidate profile declarations call).map (fun result => {result.val with call := call})

theorem inspect_call_exact {p : Option Profile} {ds : List Json} {call : Json} {info : Info}
    (accepted : inspect p ds call = .ok info) : info.call = call := by
  cases h : candidate p ds call with
  | error reason => simp only [inspect,h,Except.map] at accepted; cases accepted
  | ok candidate =>
    simp only [inspect,h,Except.map,Except.ok.injEq] at accepted
    cases accepted
    rfl

theorem inspect_declaration_member {p : Option Profile} {ds : List Json} {call : Json} {info : Info}
    (accepted : inspect p ds call = .ok info) : info.declaration ∈ ds := by
  cases h : candidate p ds call with
  | error reason => simp only [inspect,h,Except.map] at accepted; cases accepted
  | ok result =>
    simp only [inspect,h,Except.map,Except.ok.injEq] at accepted
    cases accepted
    exact result.property

theorem Info.static_declaration (info : Info) (static : info.isStatic = true) :
    (info.declaration.getObjValAs? String "stateMutability").toOption = some "pure" ∨
    (info.declaration.getObjValAs? String "stateMutability").toOption = some "view" := by
  have readonly : ["pure", "view"].contains info.mutability = true :=
    (Bool.and_eq_true_iff.mp static).2
  simp only [List.contains_cons,List.contains_nil,Bool.or_false,Bool.or_eq_true,beq_iff_eq] at readonly
  rcases readonly with h | h
  · exact Or.inl (info.mutabilityAt.trans (congrArg some h))
  · exact Or.inr (info.mutabilityAt.trans (congrArg some h))

theorem Info.static_target (info : Info) (static : info.isStatic = true) :
    staticTarget? info.profile = some true := by
  have target : info.targetIsStatic = true := (Bool.and_eq_true_iff.mp static).1
  exact info.targetAt.trans (congrArg some target)

/-- A certificate binds the exact complete input, not an arbitrary issued Prop.
It certifies structural metadata only, never an execution/frame premise. -/
structure Checked (profile : Option Profile) (declarations : List Json) (call : Json) where
  info : Info
  accepted : inspect profile declarations call = .ok info

def check (profile : Option Profile) (declarations : List Json) (call : Json) :
    Except Refusal (Checked profile declarations call) :=
  match h : inspect profile declarations call with
  | .ok info => .ok ⟨info, h⟩
  | .error reason => .error reason

/-- Conservative historical/unresolved fallback retains the old ordinary rule.
No callback outcome is suppressed merely because a label could not be issued. -/
def keyword (profile : Option Profile) (declarations : List Json) (call : Json) : String :=
  match check profile declarations call with
  | .ok checked => (if checked.info.isStatic then "try_static_at " else "try_call_at ") ++
      toString checked.info.site
  | .error _ => "try"

/-- info: 'Solidity.Frontend.CallMetadata.inspect_declaration_member' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms inspect_declaration_member
end Solidity.Frontend.CallMetadata
