import Solidity.Correctness.Elab.Congruence

/-!
# Hash callback agreement

Extracted from the hoist agreement obligations at kept ET3
`87bcfd0b879882f908c33933de73ba8bd84ae61b`; Lower is unchanged from that head.
These are helper equations, not a proof of `elabKernelTotal`.
-/

namespace Solidity.ElabAgree

open Solidity Semantics

variable (C : Contract) [FreshNames]

/-- A hash pipeline agrees through precisely its successful intermediate
outputs. The statement callback sees the name allocated after the byte stage. -/
theorem hashPipeline_agree
    (H K : RawExpr → ElabM (SProg C × RawExpr))
    (B D : RawExpr → ElabM (SProg C × String))
    (S T : List RawStmt → ElabM (SProg C))
    (sc : ElabScope) (a : RawExpr) (ty : String) (kind : HashKind)
    (hh : Agree sc (H a) (K a))
    (hb : ∀ out, Out sc (H a) out → Agree sc (B out.2) (D out.2))
    (hs : ∀ out bytes n, Out sc (H a) out → Out sc (B out.2) bytes →
      Out sc (freshCapture "se") n →
      Agree sc (S [.decl (.named ty) (toString n)
        (some (.field (.name bytes.2) (hashMember kind)))])
        (T [.decl (.named ty) (toString n)
        (some (.field (.name bytes.2) (hashMember kind)))])) :
    Agree (α := SProg C × RawExpr) sc (do
      let (P, a) ← H a
      let (Q, b) ← B a
      let y := toString (← freshCapture "se")
      let R ← S [.decl (.named ty) y (some (.field (.name b) (hashMember kind)))]
      pure (P ++ Q ++ R, .name y))
    (do
      let (P, a) ← K a
      let (Q, b) ← D a
      let y := toString (← freshCapture "se")
      let R ← T [.decl (.named ty) y (some (.field (.name b) (hashMember kind)))]
      pure (P ++ Q ++ R, .name y)) := by
  apply agree_bind hh
  intro out hout
  rcases out with ⟨P, a⟩
  apply agree_bind (hb _ hout)
  intro bytes hbytes
  rcases bytes with ⟨Q, b⟩
  apply agree_bind (agree_refl sc (freshCapture "se"))
  intro n hn
  apply agree_bind (hs _ _ n hout hbytes hn)
  intro R _
  exact agree_refl _ _

/-- Ordinary hashes invoke the hoister at their sole argument, then pass
its output to the byte callback and the allocated declaration to statements. -/
theorem hoistHashWith_single_agree
    (H K : RawExpr → ElabM (SProg C × RawExpr))
    (B D : RawExpr → ElabM (SProg C × String))
    (S T : List RawStmt → ElabM (SProg C))
    (sc : ElabScope) (f : String) (a : RawExpr) (hf : f ≠ "ecrecover")
    (hh : Agree sc (H a) (K a))
    (hb : ∀ out, Out sc (H a) out → Agree sc (B out.2) (D out.2))
    (hs : ∀ out bytes n, Out sc (H a) out → Out sc (B out.2) bytes →
      Out sc (freshCapture "se") n →
      Agree sc (S [.decl (.named (if f == "ripemd160" then "bytes20" else "bytes32"))
        (toString n) (some (.field (.name bytes.2)
          (hashMember ((HashKind.ofName? f).getD .keccak))))])
        (T [.decl (.named (if f == "ripemd160" then "bytes20" else "bytes32"))
        (toString n) (some (.field (.name bytes.2)
          (hashMember ((HashKind.ofName? f).getD .keccak))))])) :
    Agree sc (hoistHashWith C H B S f [a]) (hoistHashWith C K D T f [a]) := by
  simpa only [hoistHashWith, beq_iff_eq, hf, ↓reduceIte] using
    hashPipeline_agree C H K B D S T sc a
      (if f == "ripemd160" then "bytes20" else "bytes32")
      ((HashKind.ofName? f).getD .keccak) hh hb hs

/-- The four ecrecover arguments are hoisted together as `abi.encode`.
No agreement of separate argument callbacks is needed. -/
theorem hoistHashWith_ecrecover_agree
    (H K : RawExpr → ElabM (SProg C × RawExpr))
    (B D : RawExpr → ElabM (SProg C × String))
    (S T : List RawStmt → ElabM (SProg C))
    (sc : ElabScope) (a b c d : RawExpr)
    (hh : Agree sc (H (.call "abi.encode" [a,b,c,d]))
      (K (.call "abi.encode" [a,b,c,d])))
    (hb : ∀ out, Out sc (H (.call "abi.encode" [a,b,c,d])) out →
      Agree sc (B out.2) (D out.2))
    (hs : ∀ out bytes n, Out sc (H (.call "abi.encode" [a,b,c,d])) out →
      Out sc (B out.2) bytes → Out sc (freshCapture "se") n →
      Agree sc (S [.decl (.named "address") (toString n)
        (some (.field (.name bytes.2) (hashMember .ecrecover)))])
        (T [.decl (.named "address") (toString n)
        (some (.field (.name bytes.2) (hashMember .ecrecover)))])) :
    Agree sc (hoistHashWith C H B S "ecrecover" [a,b,c,d])
      (hoistHashWith C K D T "ecrecover" [a,b,c,d]) := by
  simpa only [hoistHashWith, ↓reduceIte, BEq.rfl] using
    hashPipeline_agree C H K B D S T sc (.call "abi.encode" [a,b,c,d])
      "address" .ecrecover hh hb hs

/-- Invalid arities have identical errors, independent of all callbacks. -/
theorem hoistHashWith_bad_arity_agree
    (H K : RawExpr → ElabM (SProg C × RawExpr))
    (B D : RawExpr → ElabM (SProg C × String))
    (S T : List RawStmt → ElabM (SProg C))
    (sc : ElabScope) (f : String) (args : List RawExpr)
    (h : if f = "ecrecover" then args.length ≠ 4 else args.length ≠ 1) :
    Agree sc (hoistHashWith C H B S f args) (hoistHashWith C K D T f args) := by
  by_cases hf : f = "ecrecover"
  · subst f
    simp only [ite_true] at h
    rcases args with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e, rest⟩⟩⟩⟩⟩
    all_goals first
      | exact (h rfl).elim
      | exact agree_refl _ _
  · simp only [if_neg hf] at h
    rcases args with _ | ⟨a, _ | ⟨b, rest⟩⟩
    all_goals first
      | exact (h rfl).elim
      | simp [hoistHashWith, hf, Agree]

omit [FreshNames] in
/-- ERC7201 folds literals without invoking callbacks; otherwise only the
exact nested hashing expression needs callback agreement. Malformed lists
fail identically without a callback premise. -/
theorem hoistERC7201With_agree
    (H K : RawExpr → ElabM (SProg C × RawExpr)) (sc : ElabScope)
    (args : List RawExpr)
    (h : ∀ a, args = [a] → a.bytesLit? = none →
      Agree sc
        (H (.binop .band
          (.call "uint256" [.call "keccak256" [.call "abi.encode"
            [.binop .subW (.call "uint256" [.call "keccak256" [a]]) (.num 1)]]])
          (.num (2 ^ 256 - 256))))
        (K (.binop .band
          (.call "uint256" [.call "keccak256" [.call "abi.encode"
            [.binop .subW (.call "uint256" [.call "keccak256" [a]]) (.num 1)]]])
          (.num (2 ^ 256 - 256))))) :
    Agree sc (hoistERC7201With C H args) (hoistERC7201With C K args) := by
  rcases args with _ | ⟨a, _ | ⟨b, rest⟩⟩
  · exact agree_refl _ _
  · cases he : a.bytesLit? with
    | none => simpa only [hoistERC7201With, he, pure_bind] using h a rfl he
    | some bs =>
      simp only [hoistERC7201With, he]
      exact agree_refl _ _
  · exact agree_refl _ _

end Solidity.ElabAgree
