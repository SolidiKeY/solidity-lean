import Solidity.Calculus.Core.Step
import Solidity.Calculus.Rules

/-!
# Taclets on scoped statements: a first port

Three of `Rules.lean`'s taclets over the scoped syntax (`docs/intrinsic.md`,
"M6a lane"), as the cutover will write all of them: a terminal rule
(`localValueAssign`), a capture (`storageFieldRead_unfold_rightFst`, its
fresh alias in a scope of its own, popped after the statement), and a
branch (`ifElseSplit`, each branch a block).  The constructors are written
out here; at the cutover the `dl{ … }` macro writes them from the same rule
lines as today, inserting the weakenings and the scope end itself.

Their soundness against the scoped interpreter waits for it (M3's
`Core.Stmt.run`).  What holds already: each is the rule `Stmt.step` fires
(`Taclet.step_eq`), and each is an instance of today's rule relation
(`Taclet.erase`).  That is not yet soundness of what a Core taclet proves,
`Core.Premise.fml`.  For `update`, `unfold`, `bind`, `check` and `done` it
follows from `Taclet.sound` given a `holds_erase` lemma; for `split` it does
not, since today's `Premise.fml` has a cover conjunct (under the diamond,
`se = true ∨ se = false`, which untyped states do not guarantee) and
Core's has none: that needs typed boolean locals (M3/M4's `State C Γ`).
-/

namespace Solidity.Core

variable {C : Contract}

/-- `s ⇒ p` on scoped statements: the statement `s` rewrites to the premise
`p`, under the modality `m`, its fresh locals named at index `k`. -/
inductive Taclet (C : Contract) (k : Nat) (m : Modality) :
    {Γ Γ' : Ctx} → Stmt C Γ Γ' → Premise C Γ Γ' → Prop where
  /-- `⟨[ v = se; ]⟩ ⇝ { v := se } ⟨[ ]⟩` -/
  | localValueAssign {Γ : Ctx} {p : PrimTy} {v : Idx Γ (.val p)} {se : Simple C Γ p} :
      Taclet C k m (.assignLocal v (.simple se)) (.setLocal v (.simple se))
  /-- `⟨[ v = nsp.fld; ]⟩ ⇝ ⟨[ T storage sp = nsp; v = sp.fld; ]⟩`: `sp` is
  declared on top of the statement's context, `v` read under it (`↑v`), and
  popped after the statement (the `Ext` of `Premise.unfold`). -/
  | storageFieldRead_unfold_rightFst {Γ : Ctx} {p : PrimTy} {s : Name} {v : Idx Γ (.val p)}
      {nsp : SPath C Γ (.struct s)} {fld : Name} {h : C.fieldType s fld = some (.prim p)}
      (hn : nsp.isSimple = false) :
      Taclet C k m (.assignLocal v (.read (.field nsp fld h)))
        (.unfold (.cons (.declStorage (.struct s) (fsp k) (some (.path nsp)))
          (.cons (.assignLocal v.there (.read (.field (.alias .here) fld h))) .nil)) (.push .refl))
  /-- `⟨[ if (se) thenStm else elseStm; ]⟩ ⇝ se = true ⟹ ⟨[ thenStm ]⟩ ;
  se = false ⟹ ⟨[ elseStm ]⟩`, each branch a block (`Premise.fml` pops it). -/
  | ifElseSplit {Γ Γ₁ Γ₂ : Ctx} {se : Simple C Γ .bool} {thn : Prog C Γ Γ₁} {els : Prog C Γ Γ₂} :
      Taclet C k m (.ite (.simple se) thn els)
        (.split .block (Fml.isBool se.lower true) (Fml.isBool se.lower false) thn els)

/-! ## The rule `Stmt.step` fires -/

/-- Each taclet is the rule the strategy fires on its statement. -/
theorem Taclet.step_eq {k : Nat} {m : Modality} {Γ Γ' : Ctx} {s : Stmt C Γ Γ'}
    {p : Premise C Γ Γ'} (h : Taclet C k m s p) : s.step k m = some p := by
  cases h with
  | localValueAssign => rfl
  | storageFieldRead_unfold_rightFst hn =>
    show (if _ then _ else _) = _
    rw [hn]; rfl
  | ifElseSplit => rfl

/-! ## Erasure: today's taclet -/

/-- `Rules.lean`'s premise, the positions named by `ns`: a capture's scope
and a hidden binder are erased, a branch's block is its statements. -/
def Premise.erase {Γ Γ' : Ctx} (ns : List Var) : Premise C Γ Γ' → Solidity.Premise C
  | .update U => .update (U.erase ns)
  | .unfold P _ => .unfold (P.erase ns)
  | .bind x _ P => .unfold (P.erase (x :: ns))
  | .split _ c c' P Q => .split (c.erase ns) (c'.erase ns) (P.erase ns) (Q.erase ns)
  | .check c => .check (c.erase ns) []
  | .done b => .done b
  | .branches bs => .branches (bs.map fun b => (b.bs.toList, b.P.erase (b.bs.names ++ ns)))
  | .cases fs us => .cases (fs.map (·.erase ns)) (us.map (·.erase ns))
  | .inv I _ _ U c c' _ hb P post =>
    let ms := (U.names ns).drop hb.depth
    .inv (I.erase ns) (U.erase ns) (c.erase (U.names ns)) (c'.erase (U.names ns)) (P.erase ms)
      (post.erase ms)
  | .inline P _ => .unfold (P.erase ns)

/-- **Each taclet is an instance of today's rule relation**: its statement
and premise erase to a `Solidity.Taclet`.  This relates the rules, not what
they prove: a split's `Core.Premise.fml` has no cover conjunct, so
`Taclet.sound` does not cover it (module docstring). -/
theorem Taclet.erase {k : Nat} {m : Modality} {Γ Γ' : Ctx} {s : Stmt C Γ Γ'}
    {p : Premise C Γ Γ'} (h : Taclet C k m s p) (ns : List Var) :
    ∃ s', s.erase ns = [s'] ∧ Solidity.Taclet C k m s' (p.erase ns) := by
  cases h with
  | localValueAssign =>
    rename_i p v se
    refine ⟨_, rfl, ?_⟩
    show Solidity.Taclet C k m (.assignLocal (v.name ns) (.simple (se.erase ns)))
      (.update [.val (v.name ns) (se.lower.erase ns)])
    rw [Simple.lower_erase]
    exact .localValueAssign
  | storageFieldRead_unfold_rightFst hn =>
    rename_i p s v nsp fld h
    refine ⟨_, rfl, ?_⟩
    have hn' : (nsp.erase ns).isSimple = false := by rw [SPath.isSimple_erase]; exact hn
    exact Solidity.Taclet.storageFieldRead_unfold_rightFst (C := C) (k := k) (m := m)
      (lhs := (.local (v.name ns) : Solidity.Hole C (.prim p))) (nsp := nsp.erase ns) (fld := fld)
      (hfld := h) (hnsp := hn')
  | ifElseSplit =>
    rename_i Γ₁ Γ₂ se thn els
    refine ⟨_, rfl, ?_⟩
    show Solidity.Taclet C k m (.ite (.simple (se.erase ns)) (thn.erase ns) (els.erase ns))
      (.split (.eq (se.lower.erase ns) (.app0 (.lit (.bool true))))
        (.eq (se.lower.erase ns) (.app0 (.lit (.bool false)))) (thn.erase ns) (els.erase ns))
    rw [Simple.lower_erase]
    exact .ifElseSplit

end Solidity.Core
