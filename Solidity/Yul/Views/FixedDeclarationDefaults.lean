import Solidity.Yul.Views.DeclarationDefaults
import Solidity.Yul.Views.RootDeclarations

/-! Default-payload proofs recurse over the existing finite typed declaration
certificates and their actual packing computations. No planner, depth cap,
zero-default policy or transient-aggregate admission is added. -/
namespace Solidity.Yul.Views.FixedDeclarationDefaults

def Payloads {E : Source.Env} {a : Roadmap.Address} (cs : List (ScalarPath E.layout (E.lay a))) : Prop :=
  ∀ c ∈ cs, (Source.Val.default E.layout (E.lay a c.path)).map (fun value => (c.codec.encode value).val)=
    (Source.Val.default E.layout (E.lay a c.path)).map (fun _ => 0)

def PackDefaults {E : Source.Env} (pack : FixedPackFn E) : Prop :=
  ∀ path a cursor cs stop, pack path a cursor=.ok (cs,stop) → Payloads cs

theorem append {E : Source.Env} {a} (left right : List (ScalarPath E.layout (E.lay a)))
    (hl : Payloads left) (hr : Payloads right) : Payloads (left++right) := by
  intro c member
  rcases List.mem_append.mp member with first | next
  · exact hl c first
  · exact hr c next

theorem align {E} (body : FixedPackFn E) (good : PackDefaults body) : PackDefaults (alignFixedPack body) := by
  intro path a cursor cs stop success
  unfold alignFixedPack at success
  cases packed : body path a (roundSlot cursor) with
  | error reason => simp only [packed,Except.map] at success; cases success
  | ok result =>
    rcases result with ⟨out,last⟩
    simp only [packed,Except.map,Except.ok.injEq,Prod.mk.injEq] at success
    obtain ⟨rfl,rfl⟩ := success
    exact good path a (roundSlot cursor) out last packed

theorem row {E} (step : Nat → Source.Step) (head : FixedPackFn E) (tail : Nat → FixedPackFn E)
    (hg : PackDefaults head) (tg : ∀ index, PackDefaults (tail index)) (index : Nat) :
    PackDefaults (packFixedRow step head tail index) := by
  intro path a cursor cs stop success
  unfold packFixedRow at success
  cases first : head (path.go (step index)) a cursor with
  | error reason => simp only [first,Except.bind] at success; cases success
  | ok result =>
    rcases result with ⟨left,middle⟩
    cases next : tail (index+1) path a middle with
    | error reason => simp only [first,next,Except.bind,Except.map] at success; cases success
    | ok result =>
      rcases result with ⟨right,last⟩
      simp only [first,next,Except.bind,Except.map,Except.ok.injEq,Prod.mk.injEq] at success
      obtain ⟨rfl,rfl⟩ := success
      exact append left right (hg _ _ _ _ _ first) (tg _ _ _ _ _ _ next)

theorem elements {E} (body : FixedPackFn E) (good : PackDefaults body) (count index : Nat) :
    PackDefaults (fun path a cursor => packFixedElements body path a index count cursor) := by
  induction count generalizing index with
  | zero => intro path a cursor cs stop success; cases success; intro c member; cases member
  | succ n ih => exact row Source.Step.index body _ good ih index

mutual
theorem fixed {E τ} (d : FixedDeclaration E τ) : PackDefaults d.pack := by
  cases d with
  | scalar τ supported => intro path a cursor cs stop success; exact DeclarationDefaults.packed _ _ _ _ _ _ _ success
  | array count positive child => exact align _ (elements child.pack (fixed child) count 0)
  | strct name types found members => exact align _ (fields members 0)

theorem fields {E τs} (d : FixedDeclarationFields E τs) (index : Nat) : PackDefaults (d.pack index) := by
  cases d with
  | nil => intro path a cursor cs stop success; cases success; intro c member; cases member
  | cons head tail => exact row Source.Step.field head.pack tail.pack (fixed head) (fields tail) index
end

theorem roots {E ds} (d : RootDeclarations E ds) (a cursor cs stop)
    (success : d.pack a cursor=.ok (cs,stop)) : Payloads cs := by
  induction d generalizing cursor cs stop with
  | nil => cases success; intro c member; cases member
  | @cons root τ rest head tail ih =>
    rw [RootDeclarations.pack_cons] at success
    split at success
    · cases first : head.pack ⟨root,[]⟩ a cursor with
      | error reason => simp only [first,Except.bind] at success; cases success
      | ok result =>
        rcases result with ⟨left,middle⟩
        cases next : tail.pack a middle with
        | error reason => simp only [first,next,Except.bind,Except.map] at success; cases success
        | ok result =>
          rcases result with ⟨right,last⟩
          simp only [first,next,Except.bind,Except.map,Except.ok.injEq,Prod.mk.injEq] at success
          obtain ⟨rfl,rfl⟩ := success
          exact append left right (fixed head _ _ _ _ _ first) (ih _ _ _ next)
    · cases success
private theorem check {E : Source.Env} {a : Roadmap.Address} (cs : List (ScalarPath E.layout (E.lay a)))
    (good : Payloads cs) : scalarZeroDefaultCheck cs=cs.all (fun c => (Source.Val.default E.layout (E.lay a c.path)).isSome) := by
  have each : ∀ c ∈ cs, ((Source.Val.default E.layout (E.lay a c.path)).map (fun value => (c.codec.encode value).val) == some 0)=
      (Source.Val.default E.layout (E.lay a c.path)).isSome := by
    intro c member
    rw [good c member]
    cases Source.Val.default E.layout (E.lay a c.path) <;> rfl
  apply Bool.eq_iff_iff.mpr
  simp only [scalarZeroDefaultCheck,List.all_eq_true]
  constructor
  · intro checked c member; rw [←each c member]; exact checked c member
  · intro checked c member; rw [each c member]; exact checked c member

theorem roots_check {E ds} (d : RootDeclarations E ds) (a cursor cs stop)
    (success : d.pack a cursor=.ok (cs,stop)) :
    scalarZeroDefaultCheck cs=cs.all (fun c => (Source.Val.default E.layout (E.lay a c.path)).isSome) :=
  check cs (roots d a cursor cs stop success)

theorem fixed_check {E τ} (d : FixedDeclaration E τ) (path a cursor cs stop)
    (success : d.pack path a cursor=.ok (cs,stop)) :
    scalarZeroDefaultCheck cs=cs.all (fun c => (Source.Val.default E.layout (E.lay a c.path)).isSome) :=
  check cs (fixed d path a cursor cs stop success)

private theorem empty_view {E : Source.Env} {a : Roadmap.Address} (cs : List (ScalarPath E.layout (E.lay a)))
    (good : Payloads cs) (present : ∀ c ∈ cs, (Source.Val.default E.layout (E.lay a c.path)).isSome=true) :
    finiteView cs Source.Storage.empty (fun _ => 0) := by
  intro c member
  have payload := good c member
  change (Source.Val.default E.layout (E.lay a c.path)).map c.codec.encode=some _
  cases actual : Source.Val.default E.layout (E.lay a c.path) with
  | none => have available := present c member; rw [actual] at available; cases available
  | some value =>
    rw [actual] at payload
    apply congrArg some
    apply Fin.ext
    have zero := Option.some.inj payload
    simpa only [Field.findWord,Field.find,Fin.val_zero,Nat.zero_div,Nat.zero_mod] using zero

theorem roots_empty_view {E ds} (d : RootDeclarations E ds) (a cursor cs stop)
    (success : d.pack a cursor=.ok (cs,stop))
    (present : ∀ c ∈ cs, (Source.Val.default E.layout (E.lay a c.path)).isSome=true) :
    finiteView cs Source.Storage.empty (fun _ => 0) := empty_view cs (roots d a cursor cs stop success) present

theorem fixed_empty_view {E τ} (d : FixedDeclaration E τ) (path a cursor cs stop)
    (success : d.pack path a cursor=.ok (cs,stop))
    (present : ∀ c ∈ cs, (Source.Val.default E.layout (E.lay a c.path)).isSome=true) :
    finiteView cs Source.Storage.empty (fun _ => 0) := empty_view cs (fixed d path a cursor cs stop success) present

theorem roots_empty_writeback {E ds} (d : RootDeclarations E ds) (a cursor cs stop)
    (success : d.pack a cursor=.ok (cs,stop))
    (present : ∀ c ∈ cs, (Source.Val.default E.layout (E.lay a c.path)).isSome=true) :
    finiteWriteback cs (fun _ => 0) Source.Storage.empty=some Source.Storage.empty :=
  finiteWriteback_unchanged cs _ _ (roots_empty_view d a cursor cs stop success present)

theorem roots_empty_encode {E ds} (d : RootDeclarations E ds) (a cursor cs stop)
    (success : d.pack a cursor=.ok (cs,stop))
    (present : ∀ c ∈ cs, (Source.Val.default E.layout (E.lay a c.path)).isSome=true) :
    finiteEncode cs Source.Storage.empty (fun _ => 0)=some (fun _ => 0) :=
  finiteEncode_unchanged cs _ _ (roots_empty_view d a cursor cs stop success present)
theorem checked {E ds} (d : RootDeclarations E ds) {scope bank a origin}
    (prepared : CheckedRootDeclarations d scope bank a origin) : Payloads prepared.registrations :=
  roots d a (origin.val*32) prepared.registrations prepared.endByte prepared.packed
end Solidity.Yul.Views.FixedDeclarationDefaults
