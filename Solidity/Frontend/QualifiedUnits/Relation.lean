import Solidity.Source.Units

/-!
# Independent qualified declaration paths

The specification uses the existing source syntax and identities. Imports
are the existing least-fixpoint `Sees` relation. A declaration can be a
namespace only when its actual node is a contract, interface, or library;
its children retain their positions in the original unit declaration graph.
This static relation does not assign types or evaluate expressions.
-/
namespace Solidity.Frontend.QualifiedUnits
open Solidity.Source

/-- The declaration kinds that introduce declaration namespaces. -/
def Container (k : DeclKind) : Prop :=
  k = .contract ∨ k = .interface ∨ k = .library

instance instDecidableContainer (k : DeclKind) : Decidable (Container k) := by
  unfold Container
  infer_instance

/-- Number of direct graph nodes following a container in source order.
The count comes from that owner's actual intrinsic body. -/
def memberCountSyntax (kind : DeclKind) {c : Cat} (s : Syn c) : Nat :=
  Syn.casesOn (motive := fun c (_ : Syn c) => Nat) s
    («nil» := fun {_} => 0)
    («cons» := fun {_} _ _ => 0)
    («none» := fun {_} => 0)
    («some» := fun {_} _ => 0)
    («unit» := fun _ => 0)
    («pragma» := fun _ => 0)
    («importPath» := fun _ _ => 0)
    («importSymbols» := fun _ _ _ => 0)
    («importStar» := fun _ _ => 0)
    («importAlias» := fun _ _ => 0)
    («contract» := fun _ a1 _ _ a4 => if kind == .contract then (a4.collect (some a1)).length else 0)
    («interface» := fun a0 _ a2 => if kind == .interface then (a2.collect (some a0)).length else 0)
    («library» := fun a0 a1 => if kind == .library then (a1.collect (some a0)).length else 0)
    («topPart» := fun _ => 0)
    («inherit» := fun _ _ => 0)
    («constructor» := fun _ _ _ _ _ => 0)
    («function» := fun {_} _ _ _ _ _ _ _ _ _ => 0)
    («modifier» := fun _ _ _ _ _ => 0)
    («fallback» := fun _ _ _ _ _ _ _ => 0)
    («fbNoParams» := 0)
    («fbParams» := fun _ _ _ => 0)
    («receive» := fun _ _ _ _ _ _ => 0)
    («struct» := fun {_} _ _ _ => 0)
    («structMember» := fun _ _ => 0)
    («enum» := fun {_} _ _ _ => 0)
    («udvt» := fun {_} _ _ => 0)
    («stateVar» := fun _ _ _ _ _ _ _ => 0)
    («constant» := fun _ _ _ => 0)
    («event» := fun {_} _ _ _ => 0)
    («eventParam» := fun _ _ _ => 0)
    («error» := fun {_} _ _ => 0)
    («errorParam» := fun _ _ => 0)
    («usingPart» := fun {_} _ => 0)
    («usingPath» := fun _ _ _ => 0)
    («usingAliases» := fun _ _ _ _ => 0)
    («usingAlias» := fun _ _ => 0)
    («positional» := fun _ => 0)
    («named» := fun _ => 0)
    («namedArg» := fun _ _ => 0)
    («modInv» := fun _ _ => 0)
    («param» := fun _ _ _ => 0)
    («elem» := fun _ => 0)
    («fnType» := fun _ _ _ _ => 0)
    («mapping» := fun _ _ _ _ => 0)
    («userType» := fun _ => 0)
    («array» := fun _ _ => 0)
    («varDecl» := fun _ _ _ => 0)
    («index» := fun _ _ => 0)
    («slice» := fun _ _ _ => 0)
    («member» := fun _ _ => 0)
    («callOptions» := fun _ _ _ => 0)
    («call» := fun _ _ => 0)
    («payableConv» := fun _ => 0)
    («metaType» := fun _ => 0)
    («unaryPrefix» := fun _ _ => 0)
    («unarySuffix» := fun _ _ => 0)
    («exp» := fun _ _ => 0)
    («mulDivMod» := fun _ _ _ => 0)
    («addSub» := fun _ _ _ => 0)
    («shift» := fun _ _ _ => 0)
    («bitAnd» := fun _ _ => 0)
    («bitXor» := fun _ _ => 0)
    («bitOr» := fun _ _ => 0)
    («order» := fun _ _ _ => 0)
    («equality» := fun _ _ _ => 0)
    («and» := fun _ _ => 0)
    («or» := fun _ _ => 0)
    («cond» := fun _ _ _ => 0)
    («assign» := fun _ _ _ => 0)
    («new» := fun _ => 0)
    («tuple» := fun _ _ => 0)
    («inlineArray» := fun _ _ => 0)
    («ident» := fun _ => 0)
    («lit» := fun _ => 0)
    («litUnit» := fun _ _ => 0)
    («elemType» := fun _ _ => 0)
    («declVar» := fun _ _ => 0)
    («declTuple» := fun _ _ _ _ => 0)
    («exprStmt» := fun _ => 0)
    («blockStmt» := fun {_} _ => 0)
    («simpleStmt» := fun {_} _ => 0)
    («ifStmt» := fun {_} _ _ _ => 0)
    («forStmt» := fun {_ _} _ _ _ _ => 0)
    («whileStmt» := fun {_ _} _ _ => 0)
    («doWhile» := fun {_ _} _ _ => 0)
    («continueStmt» := fun {_} => 0)
    («breakStmt» := fun {_} => 0)
    («tryStmt» := fun {_} _ _ _ _ _ => 0)
    («catchPlain» := fun {_} _ => 0)
    («catchSig» := fun {_} _ _ _ _ => 0)
    («returnStmt» := fun {_} _ => 0)
    («emit» := fun {_} _ _ => 0)
    («revert» := fun {_} _ _ => 0)
    («assembly» := fun {_} _ _ _ => 0)
    («block» := fun {_} _ => 0)
    («stmtItem» := fun {_} _ => 0)
    («uncheckedItem» := fun {_} _ => 0)
    («yulBlock» := fun _ => 0)
    («yulLet» := fun _ _ _ => 0)
    («yulAssign» := fun _ _ _ => 0)
    («yulExprStmt» := fun _ => 0)
    («yulIf» := fun _ _ => 0)
    («yulFor» := fun _ _ _ _ => 0)
    («yulSwitch» := fun _ _ _ => 0)
    («yulCase» := fun _ _ => 0)
    («yulLeave» := 0)
    («yulBreak» := 0)
    («yulContinue» := 0)
    («yulFun» := fun _ _ _ _ => 0)
    («yulPath» := fun _ _ => 0)
    («yulCall» := fun _ _ => 0)
    («yulLit» := fun _ => 0)

def memberCount (d : Decl) : Nat := memberCountSyntax d.kind d.node

/-- A named declaration directly inside the identified declaration's scope.
Both identities are checked against the original unit, never against a
flattened or renamed copy. Struct fields and enum values are not graph
nodes (`Syn.collect`); this relation resolves declarations only. -/
inductive Member (P : UnitSet) : DeclId → String → DeclId → Prop where
  | intro {owner child : DeclId} {d e : Decl} {x : String} :
      P.decl? owner = some d → Container d.kind →
      P.decl? child = some e → child.unit = owner.unit →
      e.scope = some d.name → e.name = x → x ≠ "" →
      owner.idx < child.idx → child.idx ≤ owner.idx + memberCount d →
      Member P owner x child

/-- One namespace component, independently of any executable lookup. -/
inductive Step (P : UnitSet) (R : List Remapping) : Sym → String → Sym → Prop where
  | unit {u x : String} {s : Sym} : Sees P R u x s → Step P R (.unit u) x s
  | decl {i j : DeclId} {x : String} : Member P i x j → Step P R (.decl i) x (.decl j)

/-- A finite suffix through namespace symbols. Import cycles occur inside
`Sees`; the number of qualified components is arbitrary and finite. -/
inductive Through (P : UnitSet) (R : List Remapping) : Sym → List String → Sym → Prop where
  | done (s : Sym) : Through P R s [] s
  | next {a b c : Sym} {x : String} {xs : List String} :
      Step P R a x b → Through P R b xs c → Through P R a (x :: xs) c

/-- Resolution of an existing nonempty source identifier path. -/
def Qualified (P : UnitSet) (R : List Remapping) (u : String) (p : IdPath) (s : Sym) : Prop :=
  ∃ first, Sees P R u p.head first ∧ Through P R first p.tail s

/-- Path composition does not change declaration identities. -/
theorem Through.append {P : UnitSet} {R : List Remapping} {a b c : Sym}
    {xs ys : List String} (h : Through P R a xs b) (k : Through P R b ys c) :
    Through P R a (xs ++ ys) c := by
  induction h with
  | done => exact k
  | next hs _ ih => exact .next hs (ih k)

/-- A declaration reached through a nonempty path is an actual graph node. -/
theorem Step.decl_exists {P : UnitSet} {R : List Remapping} {a : Sym}
    {x : String} {i : DeclId} (h : Step P R a x (.decl i)) :
    ∃ d, P.decl? i = some d := by
  cases h with
  | unit hs =>
    generalize e : Sym.decl i = s at hs
    induction hs with
    | @own u x s j d hu hd _ _ _ =>
      cases e
      refine ⟨d, ?_⟩
      simp only [UnitSet.decl?, hu, Option.bind_some]
      exact hd
    | ns _ _ => cases e
    | all _ _ _ ih => exact ih e
    | sym _ _ _ ih => exact ih e
  | decl hm => cases hm with
    | intro _ _ hd _ _ _ _ _ _ => exact ⟨_, hd⟩

end Solidity.Frontend.QualifiedUnits
