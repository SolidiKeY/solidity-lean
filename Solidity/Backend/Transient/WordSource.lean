import Solidity.Backend.Transient.SourceFrames

/-! General actual Source value-word port, with intrinsic type and exact
published Val.word encoding. No cleaning of dirty words or reference encoding
is invented. Layout/preparation and whole-store representation remain separate. -/
namespace Solidity.Backend.Transient

variable {E : Source.Env} {Γ : Source.RCtx} {τ : Source.STy}

def wordValue (path : Source.SPath) (typed : E.cellTy path=τ)
    (value : Source.Val E.layout τ) : Source.Val E.layout (E.cellTy path) := typed.symm ▸ value

def wordSourceWrite (path : Source.SPath) (typed : E.cellTy path=τ)
    (owner : Roadmap.Address) (value : Source.Val E.layout τ) (s : Source.St E) : Source.St E :=
  {s with ex := s.ex.apply (.transient owner fun cells => cells.write path (wordValue path typed value))}

def WordRepresents (path : Source.SPath) (typed : E.cellTy path=τ) (key : Word)
    (owner : Roadmap.Address) (s : Source.EMState E Γ) (t : State) : Prop :=
  ∃ value : Source.Val E.layout τ,
    (s.2.ex.transient.cells owner).read path=some (wordValue path typed value) ∧
    value.word=some (t.bank owner key)

theorem word_write_actual (path : Source.SPath) (typed : E.cellTy path=τ)
    (transient : E.transientRoot path=true) (F : Source.Fr) (normal : F.static=false)
    (value : Source.Val E.layout τ) (s : Source.EMState E Γ) :
    (Source.writeAt F path value).run s=
      (.ok (),(s.1,wordSourceWrite path typed F.this value s.2)) := by
  simp only [Source.writeAt,dif_pos typed.symm,Source.setCell,transient,
    ↓reduceIte,Source.applyOp,normal,Bool.false_eq_true,Source.EM.modSt]
  rfl

theorem word_write_represents (path : Source.SPath) (typed : E.cellTy path=τ)
    (key : Word) (owner : Roadmap.Address) (value : Source.Val E.layout τ)
    (word : Word) (encoded : value.word=some word) (s : Source.EMState E Γ) (t : State) :
    WordRepresents path typed key owner (s.1,wordSourceWrite path typed owner value s.2)
      (write t owner key word) := by
  refine ⟨value,?_,?_⟩
  · change ((s.2.ex.transient.set owner ((s.2.ex.transient.cells owner).write path
        (wordValue path typed value))).cells owner).read path=_
    simp only [Source.Transient.set,dif_pos,Source.Storage.write_read]
  · rw [show (write t owner key word).bank owner key=word from put_same _ _ _ _,encoded]

theorem word_compiled_write (path : Source.SPath) (typed : E.cellTy path=τ)
    (transient : E.transientRoot path=true) (F : Source.Fr) (normal : F.static=false)
    (key : Word) (value : Source.Val E.layout τ) (word : Word) (encoded : value.word=some word)
    (s : Source.EMState E Γ) (t : State) :
    (Source.writeAt F path value).run s=
      (.ok (),(s.1,wordSourceWrite path typed F.this value s.2)) ∧
    run F.this false (storeCode key word) t=.ok (write t F.this key word) ∧
    WordRepresents path typed key F.this (s.1,wordSourceWrite path typed F.this value s.2)
      (write t F.this key word) :=
  ⟨word_write_actual path typed transient F normal value s,store_code F.this t key word,
    word_write_represents path typed key F.this value word encoded s t⟩

theorem word_read_actual (path : Source.SPath) (typed : E.cellTy path=τ)
    (transient : E.transientRoot path=true) (F : Source.Fr) (s : Source.EMState E Γ)
    (value : Source.Val E.layout τ)
    (found : (s.2.ex.transient.cells F.this).read path=some (wordValue path typed value)) :
    (Source.readAt F path τ).run s=(.ok value,s) := by
  have read : (Source.readCell F path : Source.EM E Γ _).run s=(.ok (wordValue path typed value),s) := by
    simp only [Source.readCell,Source.Hoare.run_bind]
    rw [show (Source.EM.st (E:=E) (Γ:=Γ)).run s=(.ok s.2,s) from rfl]
    simp only [transient,↓reduceIte,found]
    rfl
  have cancel (type : Source.STy) (h : type=τ) : h ▸ (h.symm ▸ value)=value := by cases h; rfl
  simp only [Source.readAt,Source.Hoare.run_bind,read,dif_pos typed]
  exact congrArg (fun v : Source.Val E.layout τ => ((Except.ok v : Source.R (Source.Val E.layout τ)),s))
    (cancel _ typed)

theorem word_compiled_read (path : Source.SPath) (typed : E.cellTy path=τ)
    (transient : E.transientRoot path=true) (F : Source.Fr) (key : Word)
    (s : Source.EMState E Γ) (t : State) (relation : WordRepresents path typed key F.this s t) :
    ∃ value : Source.Val E.layout τ, (Source.readAt F path τ).run s=(.ok value,s) ∧
      value.word=some (t.bank F.this key) ∧
      run F.this F.static (loadCode key) t=
        .ok {t with machine := t.machine.push (.val (t.bank F.this key))} := by
  obtain ⟨value,found,encoded⟩ := relation
  exact ⟨value,word_read_actual path typed transient F s value found,encoded,load_code _ _ _ _⟩


theorem word_end_represents (path : Source.SPath) (typed : E.cellTy path=τ)
    (key : Word) (owner : Roadmap.Address) (s : Source.EMState E Γ) (t : State)
    (value : Source.Val E.layout τ) (default : Source.Val.default E.layout τ=some value)
    (zero : value.word=some ⟨0,by decide⟩) :
    WordRepresents path typed key owner (s.1,{s.2 with ex:=s.2.ex.endTx}) (endTx t) := by
  refine ⟨value,?_,zero⟩
  change Source.Val.default E.layout (E.cellTy path)=some (wordValue path typed value)
  have castDefault (type : Source.STy) (h : type=τ) :
      Source.Val.default E.layout type=some (h.symm ▸ value) := by
    cases h
    exact default
  exact castDefault _ typed

/-- Recommended Source-to-target entry: execute real context installation and
actual code, rather than silently equating raw owner with machine.self. Caller
machine restoration is valid for this transient-only body; G42 admission and
fresh callee memory remain separate obligations. -/
theorem word_framed_write (path : Source.SPath) (typed : E.cellTy path=τ)
    (transient : E.transientRoot path=true) (F : Source.Fr) (normal : F.static=false)
    (key : Word) (value : Source.Val E.layout τ) (word : Word) (encoded : value.word=some word)
    (s : Source.EMState E Γ) (t : State) :
    (Source.writeAt F path value).run s=
      (.ok (),(s.1,wordSourceWrite path typed F.this value s.2)) ∧
    (frameMachine F t.machine).self=addressWord F.this ∧
    (frameMachine F t.machine).caller=addressWord F.sender ∧
    (frameMachine F t.machine).callvalue=F.value ∧
    callbackInFrame F (storeCode key word) t=.ok (write t F.this key word) ∧
    WordRepresents path typed key F.this (s.1,wordSourceWrite path typed F.this value s.2)
      (write t F.this key word) :=
  ⟨word_write_actual path typed transient F normal value s,rfl,rfl,rfl,
    framed_store F normal key word t,word_write_represents path typed key F.this value word encoded s t⟩

end Solidity.Backend.Transient
