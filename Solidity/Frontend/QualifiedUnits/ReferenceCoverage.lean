import Solidity.Frontend.QualifiedUnits.References

/-! Universal preservation of frozen explicit references and all finite
identifier/member paths. No parser or EVM correctness claim is made. -/
namespace Solidity.Frontend.QualifiedUnits
open Solidity.Source

/-- References stored directly on the root constructor. -/
def rootReferences {c : Cat} (s : Syn c) : List IdPath :=
  Syn.casesOn (motive := fun c (_ : Syn c) => List IdPath) s
    («nil» := fun {_} => [])
    («cons» := fun {_} _ _ => [])
    («none» := fun {_} => [])
    («some» := fun {_} _ => [])
    («unit» := fun _ => [])
    («pragma» := fun _ => [])
    («importPath» := fun _ _ => [])
    («importSymbols» := fun _ _ _ => [])
    («importStar» := fun _ _ => [])
    («importAlias» := fun _ _ => [])
    («contract» := fun _ _ _ _ _ => [])
    («interface» := fun _ _ _ => [])
    («library» := fun _ _ => [])
    («topPart» := fun _ => [])
    («inherit» := fun a0 _ => [a0])
    («constructor» := fun _ _ _ _ _ => [])
    («function» := fun {_} _ _ _ _ _ _ a6 _ _ => a6.getD [])
    («modifier» := fun _ _ _ a3 _ => a3.getD [])
    («fallback» := fun _ _ _ _ _ a5 _ => a5.getD [])
    («fbNoParams» := [])
    («fbParams» := fun _ _ _ => [])
    («receive» := fun _ _ _ _ a4 _ => a4.getD [])
    («struct» := fun {_} _ _ _ => [])
    («structMember» := fun _ _ => [])
    («enum» := fun {_} _ _ _ => [])
    («udvt» := fun {_} _ _ => [])
    («stateVar» := fun _ _ _ a3 _ _ _ => a3.getD [])
    («constant» := fun _ _ _ => [])
    («event» := fun {_} _ _ _ => [])
    («eventParam» := fun _ _ _ => [])
    («error» := fun {_} _ _ => [])
    («errorParam» := fun _ _ => [])
    («usingPart» := fun {_} _ => [])
    («usingPath» := fun a0 _ _ => [a0])
    («usingAliases» := fun _ _ _ _ => [])
    («usingAlias» := fun a0 _ => [a0])
    («positional» := fun _ => [])
    («named» := fun _ => [])
    («namedArg» := fun _ _ => [])
    («modInv» := fun a0 _ => [a0])
    («param» := fun _ _ _ => [])
    («elem» := fun _ => [])
    («fnType» := fun _ _ _ _ => [])
    («mapping» := fun a0 _ _ _ => MapKey.paths a0)
    («userType» := fun a0 => [a0])
    («array» := fun _ _ => [])
    («varDecl» := fun _ _ _ => [])
    («index» := fun _ _ => [])
    («slice» := fun _ _ _ => [])
    («member» := fun a0 a1 => (expressionPath (.member a0 a1)).toList)
    («callOptions» := fun _ _ _ => [])
    («call» := fun _ _ => [])
    («payableConv» := fun _ => [])
    («metaType» := fun _ => [])
    («unaryPrefix» := fun _ _ => [])
    («unarySuffix» := fun _ _ => [])
    («exp» := fun _ _ => [])
    («mulDivMod» := fun _ _ _ => [])
    («addSub» := fun _ _ _ => [])
    («shift» := fun _ _ _ => [])
    («bitAnd» := fun _ _ => [])
    («bitXor» := fun _ _ => [])
    («bitOr» := fun _ _ => [])
    («order» := fun _ _ _ => [])
    («equality» := fun _ _ _ => [])
    («and» := fun _ _ => [])
    («or» := fun _ _ => [])
    («cond» := fun _ _ _ => [])
    («assign» := fun _ _ _ => [])
    («new» := fun _ => [])
    («tuple» := fun _ _ => [])
    («inlineArray» := fun _ _ => [])
    («ident» := fun a0 => [⟨a0, []⟩])
    («lit» := fun _ => [])
    («litUnit» := fun _ _ => [])
    («elemType» := fun _ _ => [])
    («declVar» := fun _ _ => [])
    («declTuple» := fun _ _ _ _ => [])
    («exprStmt» := fun _ => [])
    («blockStmt» := fun {_} _ => [])
    («simpleStmt» := fun {_} _ => [])
    («ifStmt» := fun {_} _ _ _ => [])
    («forStmt» := fun {_ _} _ _ _ _ => [])
    («whileStmt» := fun {_ _} _ _ => [])
    («doWhile» := fun {_ _} _ _ => [])
    («continueStmt» := fun {_} => [])
    («breakStmt» := fun {_} => [])
    («tryStmt» := fun {_} _ _ _ _ _ => [])
    («catchPlain» := fun {_} _ => [])
    («catchSig» := fun {_} _ _ _ _ => [])
    («returnStmt» := fun {_} _ => [])
    («emit» := fun {_} _ _ => [])
    («revert» := fun {_} _ _ => [])
    («assembly» := fun {_} _ _ _ => [])
    («block» := fun {_} _ => [])
    («stmtItem» := fun {_} _ => [])
    («uncheckedItem» := fun {_} _ => [])
    («yulBlock» := fun _ => [])
    («yulLet» := fun _ _ _ => [])
    («yulAssign» := fun _ _ _ => [])
    («yulExprStmt» := fun _ => [])
    («yulIf» := fun _ _ => [])
    («yulFor» := fun _ _ _ _ => [])
    («yulSwitch» := fun _ _ _ => [])
    («yulCase» := fun _ _ => [])
    («yulLeave» := [])
    («yulBreak» := [])
    («yulContinue» := [])
    («yulFun» := fun _ _ _ _ => [])
    («yulPath» := fun _ _ => [])
    («yulCall» := fun _ _ => [])
    («yulLit» := fun _ => [])

/-- Every reference is the root's or one of its actual syntax children's. -/
theorem references_eq {c : Cat} (s : Syn c) :
    references s = rootReferences s ++ s.children.flatMap (fun child => references child.2) := by
  cases s <;> simp only [references, rootReferences, Syn.children, List.flatMap_cons,
    List.flatMap_nil, List.append_nil, List.nil_append, List.append_assoc]

/-- Subterm reference monotonicity includes newly recognized member suffixes,
not only the explicit paths of the frozen traversal. -/
theorem references_sub {x y : Σ c, Syn c} (h : Syn.Sub x y) :
    ∀ p, p ∈ references x.2 → p ∈ references y.2 := by
  induction h with
  | refl => exact fun _ hp => hp
  | child hc _ ih =>
    intro p hp
    rw [references_eq]
    exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨_, hc, ih p hp⟩)

theorem append_paths_subset {A B C D : List IdPath}
    (hA : ∀ p, p ∈ A → p ∈ C) (hB : ∀ p, p ∈ B → p ∈ D) :
    ∀ p, p ∈ A ++ B → p ∈ C ++ D := by
  intro p hp
  rcases List.mem_append.mp hp with hp | hp
  · exact List.mem_append_left _ (hA p hp)
  · exact List.mem_append_right _ (hB p hp)

/-- No explicit path or identifier in frozen Syn.paths is lost, for arbitrary
intrinsic syntax. Recursion follows each existing syntax child directly. -/
theorem paths_sub_references : {c : Cat} → (s : Syn c) →
    ∀ p, p ∈ s.paths → p ∈ references s
  | _, .nil, p, hp => by
    rw [Syn.paths] at hp
    rw [references]
    exact (fun _ h => h) p hp
  | _, .cons a0 a1, p, hp => by
    rw [Syn.paths] at hp
    rw [references]
    exact (append_paths_subset (A := (a0.paths)) (B := a1.paths) (C := (references a0)) (D := references a1) (paths_sub_references a0) (paths_sub_references a1)) p hp
  | _, .none, p, hp => by
    rw [Syn.paths] at hp
    rw [references]
    exact (fun _ h => h) p hp
  | _, .some a0, p, hp => by
    rw [Syn.paths] at hp
    rw [references]
    exact (paths_sub_references a0) p hp
  | _, .unit a0, p, hp => by
    rw [Syn.paths] at hp
    rw [references]
    exact (paths_sub_references a0) p hp
  | _, .pragma _, p, hp => by
    rw [Syn.paths] at hp
    rw [references]
    exact (fun _ h => h) p hp
  | _, .importPath _ _, p, hp => by
    rw [Syn.paths] at hp
    rw [references]
    exact (fun _ h => h) p hp
  | _, .importSymbols a0 a1 _, p, hp => by
    rw [Syn.paths] at hp
    rw [references]
    exact (append_paths_subset (A := (a0.paths)) (B := a1.paths) (C := (references a0)) (D := references a1) (paths_sub_references a0) (paths_sub_references a1)) p hp
  | _, .importStar _ _, p, hp => by
    rw [Syn.paths] at hp
    rw [references]
    exact (fun _ h => h) p hp
  | _, .importAlias _ _, p, hp => by
    rw [Syn.paths] at hp
    rw [references]
    exact (fun _ h => h) p hp
  | _, .contract _ _ a2 a3 a4, p, hp => by
    rw [Syn.paths] at hp
    rw [references]
    exact (append_paths_subset (A := (a2.paths) ++ (a3.paths)) (B := a4.paths) (C := (references a2) ++ (references a3)) (D := references a4) (append_paths_subset (A := (a2.paths)) (B := a3.paths) (C := (references a2)) (D := references a3) (paths_sub_references a2) (paths_sub_references a3)) (paths_sub_references a4)) p hp
  | _, .interface _ a1 a2, p, hp => by
    rw [Syn.paths] at hp
    rw [references]
    exact (append_paths_subset (A := (a1.paths)) (B := a2.paths) (C := (references a1)) (D := references a2) (paths_sub_references a1) (paths_sub_references a2)) p hp
  | _, .library _ a1, p, hp => by
    rw [Syn.paths] at hp
    rw [references]
    exact (paths_sub_references a1) p hp
  | _, .topPart a0, p, hp => by
    rw [Syn.paths] at hp
    rw [references]
    exact (paths_sub_references a0) p hp
  | _, .inherit a0 a1, p, hp => by
    rw [Syn.paths] at hp
    rw [references]
    exact (append_paths_subset (A := ([a0])) (B := a1.paths) (C := ([a0])) (D := references a1) (fun _ h => h) (paths_sub_references a1)) p hp
  | _, .constructor a0 a1 _ _ a4, p, hp => by
    rw [Syn.paths] at hp
    rw [references]
    exact (append_paths_subset (A := (a0.paths) ++ (a1.paths)) (B := a4.paths) (C := (references a0) ++ (references a1)) (D := references a4) (append_paths_subset (A := (a0.paths)) (B := a1.paths) (C := (references a0)) (D := references a1) (paths_sub_references a0) (paths_sub_references a1)) (paths_sub_references a4)) p hp
  | _, .function _ a1 _ _ a4 _ a6 a7 a8, p, hp => by
    rw [Syn.paths] at hp
    rw [references]
    exact (append_paths_subset (A := (a6.getD []) ++ (a1.paths) ++ (a4.paths) ++ (a7.paths)) (B := a8.paths) (C := (a6.getD []) ++ (references a1) ++ (references a4) ++ (references a7)) (D := references a8) (append_paths_subset (A := (a6.getD []) ++ (a1.paths) ++ (a4.paths)) (B := a7.paths) (C := (a6.getD []) ++ (references a1) ++ (references a4)) (D := references a7) (append_paths_subset (A := (a6.getD []) ++ (a1.paths)) (B := a4.paths) (C := (a6.getD []) ++ (references a1)) (D := references a4) (append_paths_subset (A := (a6.getD [])) (B := a1.paths) (C := (a6.getD [])) (D := references a1) (fun _ h => h) (paths_sub_references a1)) (paths_sub_references a4)) (paths_sub_references a7)) (paths_sub_references a8)) p hp
  | _, .modifier _ a1 _ a3 a4, p, hp => by
    rw [Syn.paths] at hp
    rw [references]
    exact (append_paths_subset (A := (a3.getD []) ++ (a1.paths)) (B := a4.paths) (C := (a3.getD []) ++ (references a1)) (D := references a4) (append_paths_subset (A := (a3.getD [])) (B := a1.paths) (C := (a3.getD [])) (D := references a1) (fun _ h => h) (paths_sub_references a1)) (paths_sub_references a4)) p hp
  | _, .fallback a0 _ _ a3 _ a5 a6, p, hp => by
    rw [Syn.paths] at hp
    rw [references]
    exact (append_paths_subset (A := (a5.getD []) ++ (a0.paths) ++ (a3.paths)) (B := a6.paths) (C := (a5.getD []) ++ (references a0) ++ (references a3)) (D := references a6) (append_paths_subset (A := (a5.getD []) ++ (a0.paths)) (B := a3.paths) (C := (a5.getD []) ++ (references a0)) (D := references a3) (append_paths_subset (A := (a5.getD [])) (B := a0.paths) (C := (a5.getD [])) (D := references a0) (fun _ h => h) (paths_sub_references a0)) (paths_sub_references a3)) (paths_sub_references a6)) p hp
  | _, .fbNoParams, p, hp => by
    rw [Syn.paths] at hp
    rw [references]
    exact (fun _ h => h) p hp
  | _, .fbParams a0 a1 a2, p, hp => by
    rw [Syn.paths] at hp
    rw [references]
    exact (append_paths_subset (A := (a0.paths) ++ (a1.paths)) (B := a2.paths) (C := (references a0) ++ (references a1)) (D := references a2) (append_paths_subset (A := (a0.paths)) (B := a1.paths) (C := (references a0)) (D := references a1) (paths_sub_references a0) (paths_sub_references a1)) (paths_sub_references a2)) p hp
  | _, .receive _ _ a2 _ a4 a5, p, hp => by
    rw [Syn.paths] at hp
    rw [references]
    exact (append_paths_subset (A := (a4.getD []) ++ (a2.paths)) (B := a5.paths) (C := (a4.getD []) ++ (references a2)) (D := references a5) (append_paths_subset (A := (a4.getD [])) (B := a2.paths) (C := (a4.getD [])) (D := references a2) (fun _ h => h) (paths_sub_references a2)) (paths_sub_references a5)) p hp
  | _, .struct _ a1 a2, p, hp => by
    rw [Syn.paths] at hp
    rw [references]
    exact (append_paths_subset (A := (a1.paths)) (B := a2.paths) (C := (references a1)) (D := references a2) (paths_sub_references a1) (paths_sub_references a2)) p hp
  | _, .structMember a0 _, p, hp => by
    rw [Syn.paths] at hp
    rw [references]
    exact (paths_sub_references a0) p hp
  | _, .enum _ _ _, p, hp => by
    rw [Syn.paths] at hp
    rw [references]
    exact (fun _ h => h) p hp
  | _, .udvt _ _, p, hp => by
    rw [Syn.paths] at hp
    rw [references]
    exact (fun _ h => h) p hp
  | _, .stateVar a0 _ _ a3 _ _ a6, p, hp => by
    rw [Syn.paths] at hp
    rw [references]
    exact (append_paths_subset (A := (a3.getD []) ++ (a0.paths)) (B := a6.paths) (C := (a3.getD []) ++ (references a0)) (D := references a6) (append_paths_subset (A := (a3.getD [])) (B := a0.paths) (C := (a3.getD [])) (D := references a0) (fun _ h => h) (paths_sub_references a0)) (paths_sub_references a6)) p hp
  | _, .constant a0 _ a2, p, hp => by
    rw [Syn.paths] at hp
    rw [references]
    exact (append_paths_subset (A := (a0.paths)) (B := a2.paths) (C := (references a0)) (D := references a2) (paths_sub_references a0) (paths_sub_references a2)) p hp
  | _, .event _ a1 _, p, hp => by
    rw [Syn.paths] at hp
    rw [references]
    exact (paths_sub_references a1) p hp
  | _, .eventParam a0 _ _, p, hp => by
    rw [Syn.paths] at hp
    rw [references]
    exact (paths_sub_references a0) p hp
  | _, .error _ a1, p, hp => by
    rw [Syn.paths] at hp
    rw [references]
    exact (paths_sub_references a1) p hp
  | _, .errorParam a0 _, p, hp => by
    rw [Syn.paths] at hp
    rw [references]
    exact (paths_sub_references a0) p hp
  | _, .usingPart a0, p, hp => by
    rw [Syn.paths] at hp
    rw [references]
    exact (paths_sub_references a0) p hp
  | _, .usingPath a0 a1 _, p, hp => by
    rw [Syn.paths] at hp
    rw [references]
    exact (append_paths_subset (A := ([a0])) (B := a1.paths) (C := ([a0])) (D := references a1) (fun _ h => h) (paths_sub_references a1)) p hp
  | _, .usingAliases a0 a1 a2 _, p, hp => by
    rw [Syn.paths] at hp
    rw [references]
    exact (append_paths_subset (A := (a0.paths) ++ (a1.paths)) (B := a2.paths) (C := (references a0) ++ (references a1)) (D := references a2) (append_paths_subset (A := (a0.paths)) (B := a1.paths) (C := (references a0)) (D := references a1) (paths_sub_references a0) (paths_sub_references a1)) (paths_sub_references a2)) p hp
  | _, .usingAlias a0 _, p, hp => by
    rw [Syn.paths] at hp
    rw [references]
    exact (fun _ h => h) p hp
  | _, .positional a0, p, hp => by
    rw [Syn.paths] at hp
    rw [references]
    exact (paths_sub_references a0) p hp
  | _, .named a0, p, hp => by
    rw [Syn.paths] at hp
    rw [references]
    exact (paths_sub_references a0) p hp
  | _, .namedArg _ a1, p, hp => by
    rw [Syn.paths] at hp
    rw [references]
    exact (paths_sub_references a1) p hp
  | _, .modInv a0 a1, p, hp => by
    rw [Syn.paths] at hp
    rw [references]
    exact (append_paths_subset (A := ([a0])) (B := a1.paths) (C := ([a0])) (D := references a1) (fun _ h => h) (paths_sub_references a1)) p hp
  | _, .param a0 _ _, p, hp => by
    rw [Syn.paths] at hp
    rw [references]
    exact (paths_sub_references a0) p hp
  | _, .elem _, p, hp => by
    rw [Syn.paths] at hp
    rw [references]
    exact (fun _ h => h) p hp
  | _, .fnType a0 _ _ a3, p, hp => by
    rw [Syn.paths] at hp
    rw [references]
    exact (append_paths_subset (A := (a0.paths)) (B := a3.paths) (C := (references a0)) (D := references a3) (paths_sub_references a0) (paths_sub_references a3)) p hp
  | _, .mapping a0 _ a2 _, p, hp => by
    rw [Syn.paths] at hp
    rw [references]
    exact (append_paths_subset (A := (MapKey.paths a0)) (B := a2.paths) (C := (MapKey.paths a0)) (D := references a2) (fun _ h => h) (paths_sub_references a2)) p hp
  | _, .userType a0, p, hp => by
    rw [Syn.paths] at hp
    rw [references]
    exact (fun _ h => h) p hp
  | _, .array a0 a1, p, hp => by
    rw [Syn.paths] at hp
    rw [references]
    exact (append_paths_subset (A := (a0.paths)) (B := a1.paths) (C := (references a0)) (D := references a1) (paths_sub_references a0) (paths_sub_references a1)) p hp
  | _, .varDecl a0 _ _, p, hp => by
    rw [Syn.paths] at hp
    rw [references]
    exact (paths_sub_references a0) p hp
  | _, .index a0 a1, p, hp => by
    rw [Syn.paths] at hp
    rw [references]
    exact (append_paths_subset (A := (a0.paths)) (B := a1.paths) (C := (references a0)) (D := references a1) (paths_sub_references a0) (paths_sub_references a1)) p hp
  | _, .slice a0 a1 a2, p, hp => by
    rw [Syn.paths] at hp
    rw [references]
    exact (append_paths_subset (A := (a0.paths) ++ (a1.paths)) (B := a2.paths) (C := (references a0) ++ (references a1)) (D := references a2) (append_paths_subset (A := (a0.paths)) (B := a1.paths) (C := (references a0)) (D := references a1) (paths_sub_references a0) (paths_sub_references a1)) (paths_sub_references a2)) p hp
  | _, .member a0 _, p, hp => by
    rw [Syn.paths] at hp
    rw [references]
    exact List.mem_append_right _ (paths_sub_references a0 p hp)
  | _, .callOptions a0 a1 a2, p, hp => by
    rw [Syn.paths] at hp
    rw [references]
    exact (append_paths_subset (A := (a0.paths) ++ (a1.paths)) (B := a2.paths) (C := (references a0) ++ (references a1)) (D := references a2) (append_paths_subset (A := (a0.paths)) (B := a1.paths) (C := (references a0)) (D := references a1) (paths_sub_references a0) (paths_sub_references a1)) (paths_sub_references a2)) p hp
  | _, .call a0 a1, p, hp => by
    rw [Syn.paths] at hp
    rw [references]
    exact (append_paths_subset (A := (a0.paths)) (B := a1.paths) (C := (references a0)) (D := references a1) (paths_sub_references a0) (paths_sub_references a1)) p hp
  | _, .payableConv a0, p, hp => by
    rw [Syn.paths] at hp
    rw [references]
    exact (paths_sub_references a0) p hp
  | _, .metaType a0, p, hp => by
    rw [Syn.paths] at hp
    rw [references]
    exact (paths_sub_references a0) p hp
  | _, .unaryPrefix _ a1, p, hp => by
    rw [Syn.paths] at hp
    rw [references]
    exact (paths_sub_references a1) p hp
  | _, .unarySuffix _ a1, p, hp => by
    rw [Syn.paths] at hp
    rw [references]
    exact (paths_sub_references a1) p hp
  | _, .exp a0 a1, p, hp => by
    rw [Syn.paths] at hp
    rw [references]
    exact (append_paths_subset (A := (a0.paths)) (B := a1.paths) (C := (references a0)) (D := references a1) (paths_sub_references a0) (paths_sub_references a1)) p hp
  | _, .mulDivMod _ a1 a2, p, hp => by
    rw [Syn.paths] at hp
    rw [references]
    exact (append_paths_subset (A := (a1.paths)) (B := a2.paths) (C := (references a1)) (D := references a2) (paths_sub_references a1) (paths_sub_references a2)) p hp
  | _, .addSub _ a1 a2, p, hp => by
    rw [Syn.paths] at hp
    rw [references]
    exact (append_paths_subset (A := (a1.paths)) (B := a2.paths) (C := (references a1)) (D := references a2) (paths_sub_references a1) (paths_sub_references a2)) p hp
  | _, .shift _ a1 a2, p, hp => by
    rw [Syn.paths] at hp
    rw [references]
    exact (append_paths_subset (A := (a1.paths)) (B := a2.paths) (C := (references a1)) (D := references a2) (paths_sub_references a1) (paths_sub_references a2)) p hp
  | _, .bitAnd a0 a1, p, hp => by
    rw [Syn.paths] at hp
    rw [references]
    exact (append_paths_subset (A := (a0.paths)) (B := a1.paths) (C := (references a0)) (D := references a1) (paths_sub_references a0) (paths_sub_references a1)) p hp
  | _, .bitXor a0 a1, p, hp => by
    rw [Syn.paths] at hp
    rw [references]
    exact (append_paths_subset (A := (a0.paths)) (B := a1.paths) (C := (references a0)) (D := references a1) (paths_sub_references a0) (paths_sub_references a1)) p hp
  | _, .bitOr a0 a1, p, hp => by
    rw [Syn.paths] at hp
    rw [references]
    exact (append_paths_subset (A := (a0.paths)) (B := a1.paths) (C := (references a0)) (D := references a1) (paths_sub_references a0) (paths_sub_references a1)) p hp
  | _, .order _ a1 a2, p, hp => by
    rw [Syn.paths] at hp
    rw [references]
    exact (append_paths_subset (A := (a1.paths)) (B := a2.paths) (C := (references a1)) (D := references a2) (paths_sub_references a1) (paths_sub_references a2)) p hp
  | _, .equality _ a1 a2, p, hp => by
    rw [Syn.paths] at hp
    rw [references]
    exact (append_paths_subset (A := (a1.paths)) (B := a2.paths) (C := (references a1)) (D := references a2) (paths_sub_references a1) (paths_sub_references a2)) p hp
  | _, .and a0 a1, p, hp => by
    rw [Syn.paths] at hp
    rw [references]
    exact (append_paths_subset (A := (a0.paths)) (B := a1.paths) (C := (references a0)) (D := references a1) (paths_sub_references a0) (paths_sub_references a1)) p hp
  | _, .or a0 a1, p, hp => by
    rw [Syn.paths] at hp
    rw [references]
    exact (append_paths_subset (A := (a0.paths)) (B := a1.paths) (C := (references a0)) (D := references a1) (paths_sub_references a0) (paths_sub_references a1)) p hp
  | _, .cond a0 a1 a2, p, hp => by
    rw [Syn.paths] at hp
    rw [references]
    exact (append_paths_subset (A := (a0.paths) ++ (a1.paths)) (B := a2.paths) (C := (references a0) ++ (references a1)) (D := references a2) (append_paths_subset (A := (a0.paths)) (B := a1.paths) (C := (references a0)) (D := references a1) (paths_sub_references a0) (paths_sub_references a1)) (paths_sub_references a2)) p hp
  | _, .assign _ a1 a2, p, hp => by
    rw [Syn.paths] at hp
    rw [references]
    exact (append_paths_subset (A := (a1.paths)) (B := a2.paths) (C := (references a1)) (D := references a2) (paths_sub_references a1) (paths_sub_references a2)) p hp
  | _, .new a0, p, hp => by
    rw [Syn.paths] at hp
    rw [references]
    exact (paths_sub_references a0) p hp
  | _, .tuple a0 a1, p, hp => by
    rw [Syn.paths] at hp
    rw [references]
    exact (append_paths_subset (A := (a0.paths)) (B := a1.paths) (C := (references a0)) (D := references a1) (paths_sub_references a0) (paths_sub_references a1)) p hp
  | _, .inlineArray a0 a1, p, hp => by
    rw [Syn.paths] at hp
    rw [references]
    exact (append_paths_subset (A := (a0.paths)) (B := a1.paths) (C := (references a0)) (D := references a1) (paths_sub_references a0) (paths_sub_references a1)) p hp
  | _, .ident a0, p, hp => by
    rw [Syn.paths] at hp
    rw [references]
    exact (fun _ h => h) p hp
  | _, .lit _, p, hp => by
    rw [Syn.paths] at hp
    rw [references]
    exact (fun _ h => h) p hp
  | _, .litUnit _ _, p, hp => by
    rw [Syn.paths] at hp
    rw [references]
    exact (fun _ h => h) p hp
  | _, .elemType _ _, p, hp => by
    rw [Syn.paths] at hp
    rw [references]
    exact (fun _ h => h) p hp
  | _, .declVar a0 a1, p, hp => by
    rw [Syn.paths] at hp
    rw [references]
    exact (append_paths_subset (A := (a0.paths)) (B := a1.paths) (C := (references a0)) (D := references a1) (paths_sub_references a0) (paths_sub_references a1)) p hp
  | _, .declTuple _ a1 a2 a3, p, hp => by
    rw [Syn.paths] at hp
    rw [references]
    exact (append_paths_subset (A := (a1.paths) ++ (a2.paths)) (B := a3.paths) (C := (references a1) ++ (references a2)) (D := references a3) (append_paths_subset (A := (a1.paths)) (B := a2.paths) (C := (references a1)) (D := references a2) (paths_sub_references a1) (paths_sub_references a2)) (paths_sub_references a3)) p hp
  | _, .exprStmt a0, p, hp => by
    rw [Syn.paths] at hp
    rw [references]
    exact (paths_sub_references a0) p hp
  | _, .blockStmt a0, p, hp => by
    rw [Syn.paths] at hp
    rw [references]
    exact (paths_sub_references a0) p hp
  | _, .simpleStmt a0, p, hp => by
    rw [Syn.paths] at hp
    rw [references]
    exact (paths_sub_references a0) p hp
  | _, .ifStmt a0 a1 a2, p, hp => by
    rw [Syn.paths] at hp
    rw [references]
    exact (append_paths_subset (A := (a0.paths) ++ (a1.paths)) (B := a2.paths) (C := (references a0) ++ (references a1)) (D := references a2) (append_paths_subset (A := (a0.paths)) (B := a1.paths) (C := (references a0)) (D := references a1) (paths_sub_references a0) (paths_sub_references a1)) (paths_sub_references a2)) p hp
  | _, .forStmt a0 a1 a2 a3, p, hp => by
    rw [Syn.paths] at hp
    rw [references]
    exact (append_paths_subset (A := (a0.paths) ++ (a1.paths) ++ (a2.paths)) (B := a3.paths) (C := (references a0) ++ (references a1) ++ (references a2)) (D := references a3) (append_paths_subset (A := (a0.paths) ++ (a1.paths)) (B := a2.paths) (C := (references a0) ++ (references a1)) (D := references a2) (append_paths_subset (A := (a0.paths)) (B := a1.paths) (C := (references a0)) (D := references a1) (paths_sub_references a0) (paths_sub_references a1)) (paths_sub_references a2)) (paths_sub_references a3)) p hp
  | _, .whileStmt a0 a1, p, hp => by
    rw [Syn.paths] at hp
    rw [references]
    exact (append_paths_subset (A := (a0.paths)) (B := a1.paths) (C := (references a0)) (D := references a1) (paths_sub_references a0) (paths_sub_references a1)) p hp
  | _, .doWhile a0 a1, p, hp => by
    rw [Syn.paths] at hp
    rw [references]
    exact (append_paths_subset (A := (a0.paths)) (B := a1.paths) (C := (references a0)) (D := references a1) (paths_sub_references a0) (paths_sub_references a1)) p hp
  | _, .continueStmt, p, hp => by
    rw [Syn.paths] at hp
    rw [references]
    exact (fun _ h => h) p hp
  | _, .breakStmt, p, hp => by
    rw [Syn.paths] at hp
    rw [references]
    exact (fun _ h => h) p hp
  | _, .tryStmt a0 a1 a2 a3 a4, p, hp => by
    rw [Syn.paths] at hp
    rw [references]
    exact (append_paths_subset (A := (a0.paths) ++ (a1.paths) ++ (a2.paths) ++ (a3.paths)) (B := a4.paths) (C := (references a0) ++ (references a1) ++ (references a2) ++ (references a3)) (D := references a4) (append_paths_subset (A := (a0.paths) ++ (a1.paths) ++ (a2.paths)) (B := a3.paths) (C := (references a0) ++ (references a1) ++ (references a2)) (D := references a3) (append_paths_subset (A := (a0.paths) ++ (a1.paths)) (B := a2.paths) (C := (references a0) ++ (references a1)) (D := references a2) (append_paths_subset (A := (a0.paths)) (B := a1.paths) (C := (references a0)) (D := references a1) (paths_sub_references a0) (paths_sub_references a1)) (paths_sub_references a2)) (paths_sub_references a3)) (paths_sub_references a4)) p hp
  | _, .catchPlain a0, p, hp => by
    rw [Syn.paths] at hp
    rw [references]
    exact (paths_sub_references a0) p hp
  | _, .catchSig _ a1 a2 a3, p, hp => by
    rw [Syn.paths] at hp
    rw [references]
    exact (append_paths_subset (A := (a1.paths) ++ (a2.paths)) (B := a3.paths) (C := (references a1) ++ (references a2)) (D := references a3) (append_paths_subset (A := (a1.paths)) (B := a2.paths) (C := (references a1)) (D := references a2) (paths_sub_references a1) (paths_sub_references a2)) (paths_sub_references a3)) p hp
  | _, .returnStmt a0, p, hp => by
    rw [Syn.paths] at hp
    rw [references]
    exact (paths_sub_references a0) p hp
  | _, .emit a0 a1, p, hp => by
    rw [Syn.paths] at hp
    rw [references]
    exact (append_paths_subset (A := (a0.paths)) (B := a1.paths) (C := (references a0)) (D := references a1) (paths_sub_references a0) (paths_sub_references a1)) p hp
  | _, .revert a0 a1, p, hp => by
    rw [Syn.paths] at hp
    rw [references]
    exact (append_paths_subset (A := (a0.paths)) (B := a1.paths) (C := (references a0)) (D := references a1) (paths_sub_references a0) (paths_sub_references a1)) p hp
  | _, .assembly _ _ a2, p, hp => by
    rw [Syn.paths] at hp
    rw [references]
    exact (paths_sub_references a2) p hp
  | _, .block a0, p, hp => by
    rw [Syn.paths] at hp
    rw [references]
    exact (paths_sub_references a0) p hp
  | _, .stmtItem a0, p, hp => by
    rw [Syn.paths] at hp
    rw [references]
    exact (paths_sub_references a0) p hp
  | _, .uncheckedItem a0, p, hp => by
    rw [Syn.paths] at hp
    rw [references]
    exact (paths_sub_references a0) p hp
  | _, .yulBlock a0, p, hp => by
    rw [Syn.paths] at hp
    rw [references]
    exact (paths_sub_references a0) p hp
  | _, .yulLet _ _ a2, p, hp => by
    rw [Syn.paths] at hp
    rw [references]
    exact (paths_sub_references a2) p hp
  | _, .yulAssign _ _ a2, p, hp => by
    rw [Syn.paths] at hp
    rw [references]
    exact (paths_sub_references a2) p hp
  | _, .yulExprStmt a0, p, hp => by
    rw [Syn.paths] at hp
    rw [references]
    exact (paths_sub_references a0) p hp
  | _, .yulIf a0 a1, p, hp => by
    rw [Syn.paths] at hp
    rw [references]
    exact (append_paths_subset (A := (a0.paths)) (B := a1.paths) (C := (references a0)) (D := references a1) (paths_sub_references a0) (paths_sub_references a1)) p hp
  | _, .yulFor a0 a1 a2 a3, p, hp => by
    rw [Syn.paths] at hp
    rw [references]
    exact (append_paths_subset (A := (a0.paths) ++ (a1.paths) ++ (a2.paths)) (B := a3.paths) (C := (references a0) ++ (references a1) ++ (references a2)) (D := references a3) (append_paths_subset (A := (a0.paths) ++ (a1.paths)) (B := a2.paths) (C := (references a0) ++ (references a1)) (D := references a2) (append_paths_subset (A := (a0.paths)) (B := a1.paths) (C := (references a0)) (D := references a1) (paths_sub_references a0) (paths_sub_references a1)) (paths_sub_references a2)) (paths_sub_references a3)) p hp
  | _, .yulSwitch a0 a1 a2, p, hp => by
    rw [Syn.paths] at hp
    rw [references]
    exact (append_paths_subset (A := (a0.paths) ++ (a1.paths)) (B := a2.paths) (C := (references a0) ++ (references a1)) (D := references a2) (append_paths_subset (A := (a0.paths)) (B := a1.paths) (C := (references a0)) (D := references a1) (paths_sub_references a0) (paths_sub_references a1)) (paths_sub_references a2)) p hp
  | _, .yulCase _ a1, p, hp => by
    rw [Syn.paths] at hp
    rw [references]
    exact (paths_sub_references a1) p hp
  | _, .yulLeave, p, hp => by
    rw [Syn.paths] at hp
    rw [references]
    exact (fun _ h => h) p hp
  | _, .yulBreak, p, hp => by
    rw [Syn.paths] at hp
    rw [references]
    exact (fun _ h => h) p hp
  | _, .yulContinue, p, hp => by
    rw [Syn.paths] at hp
    rw [references]
    exact (fun _ h => h) p hp
  | _, .yulFun _ _ _ a3, p, hp => by
    rw [Syn.paths] at hp
    rw [references]
    exact (paths_sub_references a3) p hp
  | _, .yulPath _ _, p, hp => by
    rw [Syn.paths] at hp
    rw [references]
    exact (fun _ h => h) p hp
  | _, .yulCall _ a1, p, hp => by
    rw [Syn.paths] at hp
    rw [references]
    exact (paths_sub_references a1) p hp
  | _, .yulLit _, p, hp => by
    rw [Syn.paths] at hp
    rw [references]
    exact (fun _ h => h) p hp

/-- Every recognized expression path is collected at its full qualified length. -/
theorem expressionPath_in_references (e : Syn .expr) (p : IdPath)
    (h : expressionPath e = some p) : p ∈ references e := by
  cases e
  case ident name =>
    rw [expressionPath] at h
    cases Option.some.inj h
    rw [references]
    exact List.mem_singleton.mpr rfl
  case member receiver name =>
    rw [references]
    apply List.mem_append_left
    rw [h]
    exact List.mem_singleton.mpr rfl
  all_goals simp only [expressionPath, expressionPathAny, reduceCtorEq] at h

/-- Full qualified paths of expressions nested anywhere in arbitrary source
syntax are collected, with no profile, admission or path-length premise. -/
theorem expressionPath_in_references_of_sub {c : Cat} {s : Syn c} {e : Syn .expr} {p : IdPath}
    (hs : Syn.Sub ⟨.expr, e⟩ ⟨c, s⟩) (hp : expressionPath e = some p) : p ∈ references s :=
  references_sub hs p (expressionPath_in_references e p hp)

end Solidity.Frontend.QualifiedUnits
