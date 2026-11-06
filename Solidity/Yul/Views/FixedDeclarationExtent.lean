import Solidity.Yul.Views.FixedDeclarationPaths

namespace Solidity.Yul.Views

def fixedElementEnd (child : Nat → Nat) (count cursor : Nat) : Nat :=
  match count with
  | 0 => cursor
  | n+1 => fixedElementEnd child n (child cursor)

mutual
def FixedDeclaration.endByte {E τ} (d : FixedDeclaration E τ) : Nat → Nat := by
  cases d with
  | scalar τ supported =>
    exact fun cursor => let p := ((declarationScalar? E.layout τ).get supported).position cursor
                        p.start+p.field.width
  | array count _ child => exact fun cursor => roundSlot (fixedElementEnd child.endByte count (roundSlot cursor))
  | strct _ _ _ fields => exact fun cursor => roundSlot (fields.endByte (roundSlot cursor))

def FixedDeclarationFields.endByte {E τs} (d : FixedDeclarationFields E τs) : Nat → Nat := by
  cases d with
  | nil => exact id
  | cons head tail => exact fun cursor => tail.endByte (head.endByte cursor)
end

def FixedPackEnd {E} (pack : FixedPackFn E) (endByte : Nat → Nat) : Prop :=
  ∀ path a cursor cs stop, pack path a cursor = .ok (cs,stop) → stop = endByte cursor

theorem fixedScalar_end (E : Source.Env) (τ : Source.STy) (supported : (declarationScalar? E.layout τ).isSome) :
    FixedPackEnd (fun path a cursor => packDeclarationPaths E (fun _ => path) a 0 [("",τ)] cursor)
      (fun cursor => let p := ((declarationScalar? E.layout τ).get supported).position cursor; p.start+p.field.width) := by
  intro path a cursor cs stop success
  let seed := (declarationScalar? E.layout τ).get supported
  have found : declarationScalar? E.layout τ = some seed := Option.get_mem supported
  simp only [packDeclarationPaths,found] at success
  split at success
  · split at success
    · simp only [Except.map,Except.ok.injEq,Prod.mk.injEq] at success
      obtain ⟨rfl,rfl⟩ := success
      rfl
    · cases success
  · cases success

theorem alignFixedPack_end {E} (body : FixedPackFn E) (endByte : Nat → Nat)
    (good : FixedPackEnd body endByte) :
    FixedPackEnd (alignFixedPack body) (fun cursor => roundSlot (endByte (roundSlot cursor))) := by
  intro path a cursor cs stop success
  unfold alignFixedPack at success
  cases encoded : body path a (roundSlot cursor) with
  | error reason => simp only [encoded,Except.map] at success; cases success
  | ok result =>
    rcases result with ⟨out,last⟩
    simp only [encoded,Except.map,Except.ok.injEq,Prod.mk.injEq] at success
    obtain ⟨rfl,rfl⟩ := success
    rw [good _ _ _ _ _ encoded]

theorem packFixedRow_end {E} (step : Nat → Source.Step) (head : FixedPackFn E) (tail : Nat → FixedPackFn E)
    (he te : Nat → Nat) (headGood : FixedPackEnd head he) (tailGood : ∀ i, FixedPackEnd (tail i) te) (index : Nat) :
    FixedPackEnd (packFixedRow step head tail index) (fun cursor => te (he cursor)) := by
  intro path a cursor cs stop success
  unfold packFixedRow at success
  cases first : head (path.go (step index)) a cursor with
  | error reason => simp only [first,Except.bind] at success; cases success
  | ok result =>
    rcases result with ⟨left,middle⟩
    cases second : tail (index+1) path a middle with
    | error reason => simp only [first,second,Except.bind,Except.map] at success; cases success
    | ok result =>
      rcases result with ⟨right,last⟩
      simp only [first,second,Except.bind,Except.map,Except.ok.injEq,Prod.mk.injEq] at success
      obtain ⟨rfl,rfl⟩ := success
      rw [tailGood _ _ _ _ _ _ second,headGood _ _ _ _ _ first]

theorem packFixedElements_end {E} (child : FixedPackFn E) (ce : Nat → Nat)
    (good : FixedPackEnd child ce) (count index : Nat) :
    FixedPackEnd (fun path a cursor => packFixedElements child path a index count cursor) (fixedElementEnd ce count) := by
  induction count generalizing index with
  | zero => intro path a cursor cs stop success; cases success; rfl
  | succ n ih => exact packFixedRow_end Source.Step.index child _ ce (fixedElementEnd ce n) good ih index

mutual
theorem FixedDeclaration.pack_end {E τ} (d : FixedDeclaration E τ) : FixedPackEnd d.pack d.endByte := by
  cases d with
  | scalar τ supported => exact fixedScalar_end E τ supported
  | array count _ child => exact alignFixedPack_end _ _ (packFixedElements_end child.pack child.endByte child.pack_end count 0)
  | strct _ _ _ fields => exact alignFixedPack_end _ _ (fields.pack_end 0)

theorem FixedDeclarationFields.pack_end {E τs} (d : FixedDeclarationFields E τs) (index : Nat) :
    FixedPackEnd (d.pack index) d.endByte := by
  cases d with
  | nil => intro path a cursor cs stop success; cases success; rfl
  | cons head tail => exact packFixedRow_end Source.Step.field head.pack tail.pack head.endByte tail.endByte head.pack_end tail.pack_end index
end

end Solidity.Yul.Views
