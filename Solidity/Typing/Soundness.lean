import Solidity.Typing.State

/-!
# Type soundness: the interpreter preserves `StateWT`

The third layer: type-correctness of the expression mutual block
(`resolveS`/`resolveMBase`/`readM`/`resolveLoc`/`evalValue`/`evalInt`)
and of the location read/write primitives, followed (part 2, below the
mutual block) by the statement/block headline.

`H` is *fixed* throughout this part: nothing inside the expression
block allocates — only the statement level (`memoryDecl`, memory
`delete`, the storage→memory copy arms of assignment) extends the
store typing, which is why the statement theorems conclude
`∃ H', H.Extends H' ∧ …` while the expression theorems keep `H`.

Every theorem is shaped "`StateWT` + `wtExpr` in ⇒ `StateWT` out, and
the result inhabits the expression's annotation". Kind confusion,
out-of-range indices, and shape mismatches are not excluded by
`wtExpr` — they die at runtime (`.stuck`/`.revert`), where the
theorems are vacuous.
-/

namespace Solidity
namespace Semantics

open SemanticsProperties (lookupBy_setBy_self lookupBy_setBy_ne
  HeapWellFormed)

/-! ## Small bridges between the value carriers -/

/-- A stored int only inhabits numeric types. -/
theorem hasTy_int_numeric {ty : Ty} {n : Int}
    (h : (SVal.int n).hasTy ty = true) : isNumericTy ty = true := by
  cases ty with
  | prim pt => cases pt <;> simp_all [SVal.hasTy, isNumericTy,
      PrimTy.isNumeric]
  | ref r => simp [SVal.hasTy] at h

theorem hasTy_bool_eq {ty : Ty} {b : Bool}
    (h : (SVal.bool b).hasTy ty = true) : ty = Ty.bool := by
  cases ty with
  | prim pt => cases pt <;> simp_all [SVal.hasTy]
  | ref r => simp [SVal.hasTy] at h

/-- A primitive memory slot value reads out (`asValue`) as a stack
value of the same type. -/
theorem MVal.asValue_toSVal_hasTy {H : HeapTy} {mv : MVal} {ty : Ty}
    {v : Value} (h : MVal.hasTyH H mv ty = true)
    (hval : mv.asValue = Except.ok v) :
    (Value.toSVal v).hasTy ty = true := by
  cases mv with
  | prim p =>
      cases p with
      | int n =>
          simp only [MVal.asValue] at hval
          cases ty with
          | prim pt =>
              cases pt <;> simp_all [MVal.hasTyH, <- Except.ok.inj hval,
                Value.toSVal, SVal.hasTy]
          | ref r => simp [MVal.hasTyH] at h
      | bool b =>
          simp only [MVal.asValue] at hval
          cases ty with
          | prim pt =>
              cases pt <;> simp_all [MVal.hasTyH, <- Except.ok.inj hval,
                Value.toSVal, SVal.hasTy]
          | ref r => simp [MVal.hasTyH] at h
  | ref id => exact nomatch hval

/-- A typed stack value stores (`toMVal`) as a typed memory slot. -/
theorem Value.toMVal_hasTyH {H : HeapTy} {v : Value} {ty : Ty}
    (h : (Value.toSVal v).hasTy ty = true) :
    MVal.hasTyH H v.toMVal ty = true := by
  cases v with
  | int n =>
      cases ty with
      | prim pt => cases pt <;> simp_all [Value.toSVal, SVal.hasTy,
          Value.toMVal, MVal.hasTyH]
      | ref r => simp [Value.toSVal, SVal.hasTy] at h
  | bool b =>
      cases ty with
      | prim pt => cases pt <;> simp_all [Value.toSVal, SVal.hasTy,
          Value.toMVal, MVal.hasTyH]
      | ref r => simp [Value.toSVal, SVal.hasTy] at h

/-- Non-arithmetic operators produce booleans. -/
theorem applyBinOp_nonarith_bool {op : BinOp} {l r v : Value}
    (hop : op.isArith = false) (h : applyBinOp op l r = Except.ok v) :
    ∃ b, v = Value.bool b := by
  cases op <;> simp only [BinOp.isArith] at hop <;>
    try exact Bool.noConfusion hop
  all_goals simp only [applyBinOp, bind, Except.bind] at h
  all_goals repeat' split at h
  all_goals
    first
    | exact ⟨_, (Except.ok.inj h).symm⟩
    | exact nomatch h

/-! ## Heap-typing lookup/update lemmas (the `MVal` mirrors) -/

theorem mHasTyHFields_lookup {H : HeapTy} {str : Name}
    {fields : List (Name × MVal)} {n : Name} {v : MVal}
    (hwt : MObj.hasTyH.hasTyHFields H str fields = true)
    (hlook : lookupBy n fields = some v) :
    ∃ ty, lookupBy n (structDef str) = some ty ∧
      MVal.hasTyH H v ty = true := by
  induction fields with
  | nil => simp [lookupBy] at hlook
  | cons p rest ih =>
      obtain ⟨n', v'⟩ := p
      simp only [MObj.hasTyH.hasTyHFields, Bool.and_eq_true] at hwt
      by_cases hn : n = n'
      · subst hn
        simp [lookupBy] at hlook
        subst hlook
        cases hdef : lookupBy n (structDef str) with
        | none => rw [hdef] at hwt; exact Bool.noConfusion hwt.1
        | some ty =>
            rw [hdef] at hwt
            try dsimp only at hwt
            exact ⟨ty, rfl, hwt.1⟩
      · simp [lookupBy, hn] at hlook
        exact ih hwt.2 hlook

theorem mHasTyHElems_mem {H : HeapTy} {elem : Ty} {elems : List MVal}
    {v : MVal} (hwt : MObj.hasTyH.hasTyHElems H elem elems = true)
    (hmem : v ∈ elems) : MVal.hasTyH H v elem = true := by
  induction elems with
  | nil => cases hmem
  | cons w rest ih =>
      simp only [MObj.hasTyH.hasTyHElems, Bool.and_eq_true] at hwt
      cases hmem with
      | head => exact hwt.1
      | tail _ hmem => exact ih hwt.2 hmem

theorem mHasTyHFields_setBy {H : HeapTy} {str : Name}
    {fields : List (Name × MVal)} {n : Name} {w : MVal} {tyf : Ty}
    (hwt : MObj.hasTyH.hasTyHFields H str fields = true)
    (hdef : lookupBy n (structDef str) = some tyf)
    (hw : MVal.hasTyH H w tyf = true) :
    MObj.hasTyH.hasTyHFields H str (setBy n w fields) = true := by
  induction fields with
  | nil => simp [setBy, MObj.hasTyH.hasTyHFields, hdef, hw]
  | cons p rest ih =>
      obtain ⟨k, v⟩ := p
      simp only [MObj.hasTyH.hasTyHFields, Bool.and_eq_true] at hwt
      by_cases hn : n = k
      · subst hn
        simp [setBy, MObj.hasTyH.hasTyHFields, hdef, hw, hwt.2]
      · simp [setBy, hn, MObj.hasTyH.hasTyHFields, hwt.1, ih hwt.2]

theorem mHasTyHElems_set {H : HeapTy} {elem : Ty} {elems : List MVal}
    {i : Nat} {w : MVal}
    (hwt : MObj.hasTyH.hasTyHElems H elem elems = true)
    (hw : MVal.hasTyH H w elem = true) :
    MObj.hasTyH.hasTyHElems H elem (elems.set i w) = true := by
  induction elems generalizing i with
  | nil => exact hwt
  | cons v rest ih =>
      simp only [MObj.hasTyH.hasTyHElems, Bool.and_eq_true] at hwt
      cases i with
      | zero =>
          simp only [List.set, MObj.hasTyH.hasTyHElems, Bool.and_eq_true]
          exact ⟨hw, hwt.2⟩
      | succ n =>
          simp only [List.set, MObj.hasTyH.hasTyHElems, Bool.and_eq_true]
          exact ⟨hwt.1, ih hwt.2⟩

/-! ## State-update preservation lemmas -/

/-- Writing a typed object over an existing typed identity keeps the
heap typed (`nodupKeysB H` makes the identity's claim unique). -/
theorem heapTypedB_setObj {H : HeapTy} {heap : List (Nat × MObj)}
    {id : Nat} {tyObj : Ty} {obj' : MObj}
    (hnd : nodupKeysB H = true)
    (hheap : heapTypedB H heap = true)
    (hclaim : lookupBy id H = some tyObj)
    (hobj : obj'.hasTyH H tyObj = true) :
    heapTypedB H (setBy id obj' heap) = true := by
  refine List.all_eq_true.mpr fun r hr => ?_
  show (match lookupBy r.1 (setBy id obj' heap) with
    | some o => o.hasTyH H r.2
    | none => false) = true
  by_cases hid : r.1 = id
  · have : r.2 = tyObj := by
      have hl := lookupBy_eq_of_nodup hnd hr
      rw [hid, hclaim] at hl
      try dsimp only at hl
      exact (Option.some.inj hl).symm
    rw [hid, lookupBy_setBy_self, this]
    exact hobj
  · rw [lookupBy_setBy_ne hid]
    exact List.all_eq_true.mp hheap _ hr

/-- Rows of a `setBy` are the old rows plus (possibly) the new pair. -/
theorem all_setBy [DecidableEq κ] {p : κ × α -> Bool}
    {l : List (κ × α)} {k : κ} {v : α}
    (hall : l.all p = true) (hkv : p (k, v) = true) :
    (setBy k v l).all p = true := by
  induction l with
  | nil => simpa [setBy]
  | cons q rest ih =>
      obtain ⟨k', v'⟩ := q
      simp only [List.all_cons, Bool.and_eq_true] at hall
      by_cases hk : k = k'
      · simp only [setBy, if_pos hk, List.all_cons, Bool.and_eq_true]
        exact ⟨hkv, hall.2⟩
      · simp only [setBy, if_neg hk, List.all_cons, Bool.and_eq_true]
        exact ⟨hall.1, ih hall.2⟩

/-- Rebinding a Γ-tracked name with a binding matching its context
entry keeps the env typed. -/
theorem envTypedB_setEnv {Γ : Ctx} {L : Layout} {H : HeapTy}
    {env : List (Name × Binding)} {name : Name} {bty : BTy}
    {b : Binding}
    (hndΓ : nodupKeysB Γ = true)
    (henv : envTypedB Γ L H env = true)
    (hname : lookupBy name Γ = some bty)
    (hmatch : BTy.matchesB L H bty b = true) :
    envTypedB Γ L H (setBy name b env) = true := by
  simp only [envTypedB, Bool.and_eq_true] at henv ⊢
  constructor
  · refine List.all_eq_true.mpr fun g hg => ?_
    have hold := List.all_eq_true.mp henv.1 g hg
    by_cases hn : g.1 = name
    · have hg2 : g.2 = bty := by
        have hl := lookupBy_eq_of_nodup hndΓ hg
        rw [hn, hname] at hl
        try dsimp only at hl
        exact (Option.some.inj hl).symm
      rw [hn, lookupBy_setBy_self, hg2]
      exact hmatch
    · rw [lookupBy_setBy_ne hn]
      exact hold
  · refine all_setBy henv.2 ?_
    cases b <;> simp [hname]

/-- `setObj` on an already-present identity preserves heap
well-formedness (no key at or above `nextId` appears). -/
theorem HeapWellFormed.setObj {s : State} {id : Nat} {obj : MObj}
    (hwf : HeapWellFormed s) (hpresent : lookupBy id s.heap ≠ none) :
    HeapWellFormed (s.setObj id obj) := by
  intro i hi
  show lookupBy i (setBy id obj s.heap) = none
  have hne : i ≠ id := by
    intro he
    subst he
    exact hpresent (hwf i hi)
  rw [lookupBy_setBy_ne hne]
  exact hwf i hi

/-! ## Location typing and the read/write primitives -/

/-- What a resolved location is typed at. Alias roots
(`storageLocal`/`memoryRoot`) carry no claim: `readLoc`/`writeLoc` are
stuck on them. -/
def LocTy (Γ : Ctx) (H : HeapTy) (L : Layout) : Loc -> Ty -> Prop
  | Loc.stack name, ty => lookupBy name Γ = some (BTy.stack ty)
  | Loc.storage root segs, ty => L.tyAt root segs = some ty
  | Loc.memoryField id fld, ty =>
      ∃ str, lookupBy id H = some (Ty.ref (RefTy.struct str)) ∧
        lookupBy fld (structDef str) = some ty
  | Loc.memoryIndex id _, ty =>
      lookupBy id H = some (Ty.ref (RefTy.array ty))
  | Loc.storageLocal _, _ => True
  | Loc.memoryRoot _, _ => True

/-- Reading a typed location yields a value of its type. -/
theorem readLoc_wt {Γ : Ctx} {H : HeapTy} {L : Layout} {s : State}
    {loc : Loc} {ty : Ty} {v : Value}
    (hwt : StateWT Γ H L s) (hloc : LocTy Γ H L loc ty)
    (hread : readLoc s loc = Except.ok v) :
    (Value.toSVal v).hasTy ty = true := by
  cases loc with
  | stack name =>
      simp only [readLoc, State.getEnv, bind, Except.bind] at hread
      have henv := hwt.env
      simp only [envTypedB, Bool.and_eq_true] at henv
      have hrow := List.all_eq_true.mp henv.1 _
        (lookupBy_eq_some_mem (hloc : lookupBy name Γ = _))
      cases hlook : lookupBy name s.env with
      | none => rw [hlook] at hrow; exact Bool.noConfusion hrow
      | some b =>
          rw [hlook] at hrow hread
          try dsimp only at hread
          cases b with
          | val w =>
              simp only [<- Except.ok.inj hread]
              simpa [BTy.matchesB] using hrow
          | spath root segs => exact nomatch hread
          | mref id => exact nomatch hread
  | storageLocal name => exact nomatch hread
  | memoryRoot name => exact nomatch hread
  | storage root segs =>
      simp only [readLoc, bind, Except.bind] at hread
      cases hfind : s.findStorage root segs with
      | error e => rw [hfind] at hread; exact nomatch hread
      | ok sv =>
          rw [hfind] at hread
          try dsimp only at hread
          have hsty := findStorage_hasTy hwt.storage hloc hfind
          rw [SVal.asValue_toSVal hread]
          exact hsty
  | memoryField id fld =>
      obtain ⟨str, hclaim, hdef⟩ := hloc
      simp only [readLoc, State.getObj, bind, Except.bind] at hread
      have hrow := List.all_eq_true.mp hwt.heap _
        (lookupBy_eq_some_mem hclaim)
      cases hlook : lookupBy id s.heap with
      | none => rw [hlook] at hrow; exact Bool.noConfusion hrow
      | some obj =>
          rw [hlook] at hrow hread
          try dsimp only at hread
          try dsimp only at hread
          cases obj with
          | struct fields =>
              try dsimp only at hread
              cases hf : lookupBy fld fields with
              | none => rw [hf] at hread; exact nomatch hread
              | some mv =>
                  rw [hf] at hread
                  try dsimp only at hread
                  obtain ⟨tyf, hdef', hmv⟩ := mHasTyHFields_lookup
                    (by simpa [MObj.hasTyH] using hrow) hf
                  rw [hdef] at hdef'
                  cases hdef'
                  exact MVal.asValue_toSVal_hasTy hmv hread
          | array elems => exact nomatch hread
  | memoryIndex id i =>
      simp only [readLoc, State.getObj, bind, Except.bind] at hread
      have hrow := List.all_eq_true.mp hwt.heap _
        (lookupBy_eq_some_mem hloc)
      cases hlook : lookupBy id s.heap with
      | none => rw [hlook] at hrow; exact Bool.noConfusion hrow
      | some obj =>
          rw [hlook] at hrow hread
          try dsimp only at hread
          try dsimp only at hread
          cases obj with
          | struct fields => exact nomatch hread
          | array elems =>
              try dsimp only at hread
              split at hread
              · exact MVal.asValue_toSVal_hasTy
                  (mHasTyHElems_mem
                    (by simpa [MObj.hasTyH] using hrow)
                    (elems.get_mem _)) hread
              · exact nomatch hread

/-- Writing a value of the location's type preserves the state
invariant. -/
theorem writeLoc_wt {Γ : Ctx} {H : HeapTy} {L : Layout} {s s' : State}
    {loc : Loc} {ty : Ty} {v : Value}
    (hwt : StateWT Γ H L s) (hloc : LocTy Γ H L loc ty)
    (hv : (Value.toSVal v).hasTy ty = true)
    (hwrite : writeLoc s loc v = Except.ok s') : StateWT Γ H L s' := by
  cases loc with
  | stack name =>
      simp only [writeLoc] at hwrite
      cases Except.ok.inj hwrite
      exact { hwt with
        env := envTypedB_setEnv hwt.ctxNodup hwt.env hloc
          (by simpa [BTy.matchesB] using hv) }
  | storageLocal name => exact nomatch hwrite
  | memoryRoot name => exact nomatch hwrite
  | storage root segs =>
      simp only [writeLoc] at hwrite
      have hst' := State.saveStorage_wellTyped hwt.layoutNodup
        hwt.storage hloc hv hwrite
      obtain ⟨hheap, hnext, henv, _⟩ :=
        SemanticsProperties.State.saveStorage_frame hwrite
      refine { hwt with
                storage := hst', env := ?_, heap := ?_, heapWf := ?_ }
      · rw [henv]; exact hwt.env
      · rw [hheap]; exact hwt.heap
      · intro i hi
        rw [hheap]
        exact hwt.heapWf i (hnext ▸ hi)
  | memoryField id fld =>
      obtain ⟨str, hclaim, hdef⟩ := hloc
      simp only [writeLoc, State.getObj, bind, Except.bind] at hwrite
      have hrow := List.all_eq_true.mp hwt.heap _
        (lookupBy_eq_some_mem hclaim)
      cases hlook : lookupBy id s.heap with
      | none => rw [hlook] at hrow; exact Bool.noConfusion hrow
      | some obj =>
          rw [hlook] at hrow hwrite
          try dsimp only at hwrite
          try dsimp only at hwrite
          cases obj with
          | struct fields =>
              try dsimp only at hwrite
              cases Except.ok.inj hwrite
              refine { hwt with heap := ?_, heapWf := ?_ }
              · exact heapTypedB_setObj hwt.heapTyNodup hwt.heap hclaim
                  (by
                    simp only [MObj.hasTyH]
                    exact mHasTyHFields_setBy
                      (by simpa [MObj.hasTyH] using hrow) hdef
                      (Value.toMVal_hasTyH hv))
              · exact HeapWellFormed.setObj hwt.heapWf (by simp [hlook])
          | array elems => exact nomatch hwrite
  | memoryIndex id i =>
      simp only [writeLoc, State.getObj, bind, Except.bind] at hwrite
      have hrow := List.all_eq_true.mp hwt.heap _
        (lookupBy_eq_some_mem hloc)
      cases hlook : lookupBy id s.heap with
      | none => rw [hlook] at hrow; exact Bool.noConfusion hrow
      | some obj =>
          rw [hlook] at hrow hwrite
          try dsimp only at hwrite
          try dsimp only at hwrite
          cases obj with
          | struct fields => exact nomatch hwrite
          | array elems =>
              try dsimp only at hwrite
              split at hwrite
              · cases Except.ok.inj hwrite
                refine { hwt with heap := ?_, heapWf := ?_ }
                · exact heapTypedB_setObj hwt.heapTyNodup hwt.heap hloc
                    (by
                      simp only [MObj.hasTyH]
                      exact mHasTyHElems_set
                        (by simpa [MObj.hasTyH] using hrow)
                        (Value.toMVal_hasTyH hv))
                · exact HeapWellFormed.setObj hwt.heapWf (by simp [hlook])
              · exact nomatch hwrite

/-- No store typing claims a mapping type: a heap-typed object cannot
inhabit one, so the row check would already have failed. -/
theorem heapTy_claim_not_mapping {H : HeapTy}
    {heap : List (Nat × MObj)} {id : Nat} {k v : Ty}
    (hheap : heapTypedB H heap = true)
    (hclaim : lookupBy id H = some (Ty.ref (RefTy.mapping k v))) :
    False := by
  have hrow := List.all_eq_true.mp hheap _ (lookupBy_eq_some_mem hclaim)
  cases hlook : lookupBy id heap with
  | none => rw [hlook] at hrow; exact Bool.noConfusion hrow
  | some obj =>
      rw [hlook] at hrow
      try dsimp only at hrow
      cases obj <;> simp [MObj.hasTyH] at hrow

/-- Arithmetic operators force an int left operand. -/
theorem applyBinOp_arith_lhs_int {op : BinOp} {l r v : Value}
    (hop : op.isArith = true) (h : applyBinOp op l r = Except.ok v) :
    ∃ n, l = Value.int n := by
  cases op <;> simp only [BinOp.isArith] at hop <;>
    try exact Bool.noConfusion hop
  all_goals
    simp only [applyBinOp, bind, Except.bind] at h
  case add | sub | mul | pow =>
    cases hl : l.asInt with
    | error e => rw [hl] at h; exact nomatch h
    | ok ln =>
        cases l with
        | int n => exact ⟨n, rfl⟩
        | bool b => exact nomatch hl
  case div | mod =>
    cases hr : r.asInt with
    | error e => rw [hr] at h; exact nomatch h
    | ok rn =>
        rw [hr] at h
        try dsimp only at h
        split at h
        · exact nomatch h
        · cases hl : l.asInt with
          | error e =>
              rw [hl] at h
              first
              | (split at h <;> simp_all)
              | simp at h
          | ok ln =>
              cases l with
              | int n => exact ⟨n, rfl⟩
              | bool b => exact nomatch hl

/-- `resolveS` never looks at a field expression's type annotation
(`resolveLoc` re-wraps with `Ty.uint` before delegating). -/
theorem resolveS_field_ty_irrel (s : State) (k : Kind) (ty ty' : Ty)
    (base : WrappedExpr) (fld : Field) :
    resolveS s (WrappedExpr.field k ty base fld) =
      resolveS s (WrappedExpr.field k ty' base fld) := by
  rw [resolveS, resolveS]

/-! ## The expression mutual block preserves the invariant -/

mutual

/-- `resolveS` on a well-annotated place resolves to a path at the
expression's type — and preserves the invariant (the `pushPlace` arm
writes storage). -/
theorem resolveS_wt {Γ : Ctx} {H : HeapTy} {L : Layout} {s : State}
    (e : WrappedExpr) {s' : State} {root : Name} {segs : List Seg}
    (hwt : StateWT Γ H L s) (hexpr : wtExpr Γ L e = true)
    (hres : resolveS s e = Except.ok (s', root, segs)) :
    StateWT Γ H L s' ∧ L.tyAt root segs = some e.ty := by
  cases e with
  | var kind ty fld =>
      rw [resolveS] at hres
      try dsimp only at hres
      cases kind with
      | stack =>
          -- A stack-tracked name is never `spath`-bound, so `resolveS`
          -- is stuck: Γ says `.stack`, and `matchesB` pins the binding.
          simp only [wtExpr, beq_iff_eq] at hexpr
          have henv := hwt.env
          simp only [envTypedB, Bool.and_eq_true] at henv
          have hrow := List.all_eq_true.mp henv.1 _
            (lookupBy_eq_some_mem hexpr)
          cases hlook : lookupBy fld.name s.env with
          | none => rw [hlook] at hrow; exact Bool.noConfusion hrow
          | some b =>
              rw [hlook] at hrow hres
              try dsimp only at hres
              cases b with
              | val v =>
                  exact nomatch hres
              | spath r sg => simp [BTy.matchesB] at hrow
              | mref id => exact nomatch hres
      | memory =>
          simp only [wtExpr, beq_iff_eq] at hexpr
          have henv := hwt.env
          simp only [envTypedB, Bool.and_eq_true] at henv
          have hrow := List.all_eq_true.mp henv.1 _
            (lookupBy_eq_some_mem hexpr)
          cases hlook : lookupBy fld.name s.env with
          | none => rw [hlook] at hrow; exact Bool.noConfusion hrow
          | some b =>
              rw [hlook] at hrow hres
              try dsimp only at hres
              cases b with
              | val v => exact nomatch hres
              | spath r sg => simp [BTy.matchesB] at hrow
              | mref id => exact nomatch hres
      | storage =>
          simp only [wtExpr] at hexpr
          cases hΓ : lookupBy fld.name Γ with
          | none =>
              rw [hΓ] at hexpr
              simp only [Bool.and_eq_true, beq_iff_eq] at hexpr
              cases hlook : lookupBy fld.name s.env with
              | some b =>
                  rw [hlook] at hres
                  try dsimp only at hres
                  cases b with
                  | spath r sg =>
                      -- stray alias: forbidden by `envTypedB`.
                      have henv := hwt.env
                      simp only [envTypedB, Bool.and_eq_true] at henv
                      have := List.all_eq_true.mp henv.2 _
                        (lookupBy_eq_some_mem hlook)
                      simp only [hΓ, Option.isSome_none] at this
                      exact Bool.noConfusion this
                  | val v => exact nomatch hres
                  | mref id => exact nomatch hres
              | none =>
                  rw [hlook] at hres
                  try dsimp only at hres
                  rw [if_pos (by simp [hexpr.1])] at hres
                  simp only [Except.ok.injEq, Prod.mk.injEq] at hres
                  obtain ⟨hs, hroot, hsegs⟩ := hres
                  subst hs hroot hsegs
                  exact ⟨hwt, by
                    simp [Layout.tyAt, hexpr.2, tyAtSegs,
                      WrappedExpr.ty, Typed.WrappedExpr.ty]⟩
          | some bty =>
              rw [hΓ] at hexpr
              cases bty with
              | stack ty' => exact Bool.noConfusion hexpr
              | mem ty' => exact Bool.noConfusion hexpr
              | path ty' =>
                  simp only [Bool.and_eq_true, beq_iff_eq] at hexpr
                  have henv := hwt.env
                  simp only [envTypedB, Bool.and_eq_true] at henv
                  have hrow := List.all_eq_true.mp henv.1 _
                    (lookupBy_eq_some_mem hΓ)
                  cases hlook : lookupBy fld.name s.env with
                  | none => rw [hlook] at hrow; exact Bool.noConfusion hrow
                  | some b =>
                      rw [hlook] at hrow hres
                      try dsimp only at hres
                      cases b with
                      | val v => simp [BTy.matchesB] at hrow
                      | mref id => simp [BTy.matchesB] at hrow
                      | spath r sg =>
                          simp only [Except.ok.injEq, Prod.mk.injEq]
                            at hres
                          obtain ⟨hs, hroot, hsegs⟩ := hres
                          subst hs hroot hsegs
                          simp only [BTy.matchesB, beq_iff_eq] at hrow
                          exact ⟨hwt, by
                            simpa [WrappedExpr.ty, Typed.WrappedExpr.ty,
                              hexpr.1] using hrow⟩
  | field kind ty base fld =>
      simp only [wtExpr, Bool.and_eq_true, beq_iff_eq] at hexpr
      rw [resolveS] at hres
      try dsimp only at hres
      try simp only [bind, Except.bind] at hres
      cases hbase : resolveS s base with
      | error e => rw [hbase] at hres; exact nomatch hres
      | ok out =>
          obtain ⟨s₁, root₁, segs₁⟩ := out
          rw [hbase] at hres
          try dsimp only at hres
          obtain ⟨hwt₁, hty₁⟩ := resolveS_wt base hwt hexpr.1 hbase
          simp only [Except.ok.injEq, Prod.mk.injEq] at hres
          obtain ⟨hs, hroot, hsegs⟩ := hres
          subst hs hroot hsegs
          exact ⟨hwt₁, by
            simpa [WrappedExpr.ty, Typed.WrappedExpr.ty] using
              tyAt_append_seg hty₁ hexpr.2⟩
  | index kind ty base index =>
      simp only [wtExpr, Bool.and_eq_true, beq_iff_eq] at hexpr
      rw [resolveS] at hres
      try dsimp only at hres
      try simp only [bind, Except.bind] at hres
      cases hbase : resolveS s base with
      | error e => rw [hbase] at hres; exact nomatch hres
      | ok out =>
          obtain ⟨s₁, root₁, segs₁⟩ := out
          rw [hbase] at hres
          try dsimp only at hres
          obtain ⟨hwt₁, hty₁⟩ := resolveS_wt base hwt hexpr.1.1 hbase
          cases hidx : evalInt s₁ index with
          | error e => rw [hidx] at hres; exact nomatch hres
          | ok out₂ =>
              obtain ⟨s₂, i⟩ := out₂
              rw [hidx] at hres
              try dsimp only at hres
              obtain ⟨hwt₂, _⟩ := evalInt_wt index hwt₁ hexpr.1.2 hidx
              simp only [Except.ok.injEq, Prod.mk.injEq] at hres
              obtain ⟨hs, hroot, hsegs⟩ := hres
              subst hs hroot hsegs
              refine ⟨hwt₂, ?_⟩
              have hseg : segTy base.ty (Seg.at i) = some ty := by
                rw [segTy_at]
                simpa using hexpr.2
              simpa [WrappedExpr.ty, Typed.WrappedExpr.ty] using
                tyAt_append_seg hty₁ hseg
  | pushPlace target =>
      simp only [wtExpr, Bool.and_eq_true] at hexpr
      rw [resolveS] at hres
      try dsimp only at hres
      try simp only [bind, Except.bind] at hres
      cases htgt : resolveS s target with
      | error e => rw [htgt] at hres; exact nomatch hres
      | ok out =>
          obtain ⟨s₁, root₁, segs₁⟩ := out
          rw [htgt] at hres
          try dsimp only at hres
          obtain ⟨hwt₁, hty₁⟩ := resolveS_wt target hwt hexpr.1 htgt
          cases hfind : s₁.findStorage root₁ segs₁ with
          | error e => rw [hfind] at hres; exact nomatch hres
          | ok arr =>
              rw [hfind] at hres
              try dsimp only at hres
              have harrty := findStorage_hasTy hwt₁.storage hty₁ hfind
              -- The interpreter matches on `arr, target.ty` together.
              split at hres
              case h_2 | h_3 | h_4 | h_5 | h_6 | h_7 => exact nomatch hres
              case h_1 elems shadow elemTy₀ heq =>
                have htty := heq
                try simp only [bind, Except.bind] at hres
                cases hsave : s₁.saveStorage root₁ segs₁
                    (SVal.array (elems ++ [(pushSlot elemTy₀ shadow).1])
                      (pushSlot elemTy₀ shadow).2) with
                | error e => rw [hsave] at hres; exact nomatch hres
                | ok s₂ =>
                    rw [hsave] at hres
                    try dsimp only at hres
                    simp only [Except.ok.injEq, Prod.mk.injEq] at hres
                    obtain ⟨hs, hroot, hsegs⟩ := hres
                    subst hs hroot hsegs
                    rw [htty] at hexpr harrty hty₁
                    have hok : defaultOk elemTy₀ = true := hexpr.2
                    have hext : (SVal.array
                        (elems ++ [(pushSlot elemTy₀ shadow).1])
                        (pushSlot elemTy₀ shadow).2).hasTy
                        (Ty.ref (RefTy.array elemTy₀)) = true := by
                      simp only [SVal.hasTy, Bool.and_eq_true] at harrty ⊢
                      obtain ⟨hslot, hrest⟩ := pushSlot_hasTy harrty.2 hok
                      exact ⟨hasTyElems_append harrty.1
                        (by simpa [SVal.hasTy.hasTyElems] using hslot), hrest⟩
                    have hst₂ := State.saveStorage_wellTyped
                      hwt₁.layoutNodup hwt₁.storage hty₁ hext hsave
                    obtain ⟨hheap, hnext, henv, _⟩ :=
                      SemanticsProperties.State.saveStorage_frame hsave
                    refine ⟨{ hwt₁ with
                                storage := hst₂, env := ?_,
                                heap := ?_, heapWf := ?_ }, ?_⟩
                    · rw [henv]; exact hwt₁.env
                    · rw [hheap]; exact hwt₁.heap
                    · intro i hi
                      rw [hheap]
                      exact hwt₁.heapWf i (hnext ▸ hi)
                    · have : segTy (Ty.ref (RefTy.array elemTy₀))
                          (Seg.at elems.length) = some elemTy₀ := rfl
                      simpa [WrappedExpr.ty, Typed.WrappedExpr.ty, htty,
                        Ty.indexElemTy] using tyAt_append_seg hty₁ this
  | bool b => simp [resolveS] at hres
  | intLit ty v => simp [resolveS] at hres
  | mkCall kind ty name args => simp [resolveS] at hres
  | mkBinop op l r => simp [resolveS] at hres
  | mkUnop op arg => simp [resolveS] at hres
  | mkIncDec op target => simp [resolveS] at hres
  | mkTernary c t e => simp [resolveS] at hres
termination_by 4 * e.size + 0
decreasing_by all_goals
  first
  | omega
  | (simp [Typed.WrappedExpr.size] <;> omega)
  | (subst_vars
     simp [Typed.WrappedExpr.size, Typed.WrappedExpr.sizeList] <;> omega)

/-- `resolveMBase` lands on an identity claimed at the expression's
type. -/
theorem resolveMBase_wt {Γ : Ctx} {H : HeapTy} {L : Layout} {s : State}
    (e : WrappedExpr) {s' : State} {id : Nat}
    (hwt : StateWT Γ H L s) (hexpr : wtExpr Γ L e = true)
    (hres : resolveMBase s e = Except.ok (s', id)) :
    StateWT Γ H L s' ∧
      MVal.hasTyH H (MVal.ref id) e.ty = true := by
  cases e with
  | var kind ty fld =>
      rw [resolveMBase] at hres
      try dsimp only at hres
      simp only [State.getEnv, bind, Except.bind] at hres
      cases kind with
      | memory =>
          simp only [wtExpr, beq_iff_eq] at hexpr
          have henv := hwt.env
          simp only [envTypedB, Bool.and_eq_true] at henv
          have hrow := List.all_eq_true.mp henv.1 _
            (lookupBy_eq_some_mem hexpr)
          cases hlook : lookupBy fld.name s.env with
          | none => rw [hlook] at hrow; exact Bool.noConfusion hrow
          | some b =>
              rw [hlook] at hrow hres
              try dsimp only at hres
              cases b with
              | val v => exact nomatch hres
              | spath r sg => exact nomatch hres
              | mref mid =>
                  simp only [Except.ok.injEq, Prod.mk.injEq] at hres
                  obtain ⟨hs, hid⟩ := hres
                  subst hs hid
                  exact ⟨hwt, by
                    simpa [BTy.matchesB, WrappedExpr.ty,
                      Typed.WrappedExpr.ty] using hrow⟩
      | stack =>
          -- Γ pins the binding to `val`, on which `resolveMBase` is stuck.
          simp only [wtExpr, beq_iff_eq] at hexpr
          have henv := hwt.env
          simp only [envTypedB, Bool.and_eq_true] at henv
          have hrow := List.all_eq_true.mp henv.1 _
            (lookupBy_eq_some_mem hexpr)
          cases hlook : lookupBy fld.name s.env with
          | none => rw [hlook] at hrow; exact Bool.noConfusion hrow
          | some b =>
              rw [hlook] at hrow hres
              try dsimp only at hres
              cases b with
              | val v => exact nomatch hres
              | spath r sg => simp [BTy.matchesB] at hrow
              | mref mid => simp [BTy.matchesB] at hrow
      | storage =>
          simp only [wtExpr] at hexpr
          cases hΓ : lookupBy fld.name Γ with
          | none =>
              cases hlook : lookupBy fld.name s.env with
              | none => rw [hlook] at hres; exact nomatch hres
              | some b =>
                  rw [hlook] at hres
                  try dsimp only at hres
                  cases b with
                  | val v => exact nomatch hres
                  | mref mid =>
                      -- untracked `mref`: forbidden by `envTypedB`.
                      have henv := hwt.env
                      simp only [envTypedB, Bool.and_eq_true] at henv
                      have := List.all_eq_true.mp henv.2 _
                        (lookupBy_eq_some_mem hlook)
                      simp only [hΓ, Option.isSome_none] at this
                      exact Bool.noConfusion this
                  | spath r sg =>
                      have henv := hwt.env
                      simp only [envTypedB, Bool.and_eq_true] at henv
                      have := List.all_eq_true.mp henv.2 _
                        (lookupBy_eq_some_mem hlook)
                      simp only [hΓ, Option.isSome_none] at this
                      exact Bool.noConfusion this
          | some bty =>
              rw [hΓ] at hexpr
              cases bty with
              | stack ty' => exact Bool.noConfusion hexpr
              | mem ty' => exact Bool.noConfusion hexpr
              | path ty' =>
                  simp only [Bool.and_eq_true, beq_iff_eq] at hexpr
                  have henv := hwt.env
                  simp only [envTypedB, Bool.and_eq_true] at henv
                  have hrow := List.all_eq_true.mp henv.1 _
                    (lookupBy_eq_some_mem hΓ)
                  cases hlook : lookupBy fld.name s.env with
                  | none => rw [hlook] at hrow; exact Bool.noConfusion hrow
                  | some b =>
                      rw [hlook] at hrow hres
                      try dsimp only at hres
                      cases b with
                      | val v => simp [BTy.matchesB] at hrow
                      | mref mid => simp [BTy.matchesB] at hrow
                      | spath r sg => exact nomatch hres
  | field kind ty base fld =>
      simp only [wtExpr, Bool.and_eq_true, beq_iff_eq] at hexpr
      rw [resolveMBase] at hres
      try dsimp only at hres
      try simp only [bind, Except.bind] at hres
      cases hbase : resolveMBase s base with
      | error e => rw [hbase] at hres; exact nomatch hres
      | ok out =>
          obtain ⟨s₁, baseId⟩ := out
          rw [hbase] at hres
          try dsimp only at hres
          obtain ⟨hwt₁, hbty⟩ := resolveMBase_wt base hwt hexpr.1 hbase
          simp only [State.getObj, bind, Except.bind] at hres
          -- the claimed base type must be a struct (segTy forces it)
          cases hbt : base.ty with
          | prim pt => rw [hbt] at hexpr; simp [segTy] at hexpr
          | ref r =>
              cases r with
              | array elem => rw [hbt] at hexpr; simp [segTy] at hexpr
              | mapping k v => rw [hbt] at hexpr; simp [segTy] at hexpr
              | struct str =>
                  rw [hbt] at hexpr hbty
                  simp only [MVal.hasTyH, beq_iff_eq] at hbty
                  have hrow := List.all_eq_true.mp hwt₁.heap _
                    (lookupBy_eq_some_mem hbty)
                  cases hlook : lookupBy baseId s₁.heap with
                  | none => rw [hlook] at hrow; exact Bool.noConfusion hrow
                  | some obj =>
                      rw [hlook] at hrow hres
                      try dsimp only at hres
                      cases obj with
                      | array elems => simp [MObj.hasTyH] at hrow
                      | struct fields =>
                          try dsimp only at hres
                          cases hf : lookupBy fld.name fields with
                          | none => rw [hf] at hres; exact nomatch hres
                          | some mv =>
                              rw [hf] at hres
                              try dsimp only at hres
                              obtain ⟨tyf, hdef, hmv⟩ :=
                                mHasTyHFields_lookup
                                  (by simpa [MObj.hasTyH] using hrow) hf
                              have : tyf = ty := by
                                simp only [segTy] at hexpr
                                rw [hdef] at hexpr
                                try dsimp only at hexpr
                                simpa using hexpr.2
                              subst this
                              cases mv with
                              | prim p => exact nomatch hres
                              | ref rid =>
                                  simp only [Except.ok.injEq,
                                    Prod.mk.injEq] at hres
                                  obtain ⟨hs, hid⟩ := hres
                                  subst hs hid
                                  exact ⟨hwt₁, by
                                    simpa [WrappedExpr.ty,
                                      Typed.WrappedExpr.ty] using hmv⟩
  | index kind ty base index =>
      simp only [wtExpr, Bool.and_eq_true, beq_iff_eq] at hexpr
      rw [resolveMBase] at hres
      try dsimp only at hres
      try simp only [bind, Except.bind] at hres
      cases hbase : resolveMBase s base with
      | error e => rw [hbase] at hres; exact nomatch hres
      | ok out =>
          obtain ⟨s₁, baseId⟩ := out
          rw [hbase] at hres
          try dsimp only at hres
          obtain ⟨hwt₁, hbty⟩ := resolveMBase_wt base hwt hexpr.1.1 hbase
          cases hidx : evalInt s₁ index with
          | error e => rw [hidx] at hres; exact nomatch hres
          | ok out₂ =>
              obtain ⟨s₂, i⟩ := out₂
              rw [hidx] at hres
              try dsimp only at hres
              obtain ⟨hwt₂, _⟩ := evalInt_wt index hwt₁ hexpr.1.2 hidx
              simp only [State.getObj, bind, Except.bind] at hres
              cases hbt : base.ty with
              | prim pt => rw [hbt] at hexpr; simp [elemTy] at hexpr
              | ref r =>
                  cases r with
                  | struct str => rw [hbt] at hexpr; simp [elemTy] at hexpr
                  | mapping k v =>
                      rw [hbt] at hbty
                      try dsimp only at hbty
                      simp only [MVal.hasTyH, beq_iff_eq] at hbty
                      exact absurd hbty
                        (fun hc => heapTy_claim_not_mapping hwt₂.heap hc)
                  | array elem =>
                      rw [hbt] at hexpr hbty
                      simp only [MVal.hasTyH, beq_iff_eq] at hbty
                      have hrow := List.all_eq_true.mp hwt₂.heap _
                        (lookupBy_eq_some_mem hbty)
                      cases hlook : lookupBy baseId s₂.heap with
                      | none => rw [hlook] at hrow; exact Bool.noConfusion hrow
                      | some obj =>
                          rw [hlook] at hrow hres
                          try dsimp only at hres
                          cases obj with
                          | struct fields => simp [MObj.hasTyH] at hrow
                          | array elems =>
                              try dsimp only at hres
                              split at hres
                              case isFalse => exact nomatch hres
                              case isTrue hbound =>
                                have helem : elem = ty := by
                                  simp only [elemTy] at hexpr
                                  simpa using hexpr.2
                                subst helem
                                cases hget : elems.get
                                    ⟨i.toNat, hbound.2⟩ with
                                | prim p =>
                                    rw [hget] at hres
                                    try dsimp only at hres
                                    exact nomatch hres
                                | ref rid =>
                                    rw [hget] at hres
                                    try dsimp only at hres
                                    simp only [Except.ok.injEq,
                                      Prod.mk.injEq] at hres
                                    obtain ⟨hs, hid⟩ := hres
                                    subst hs hid
                                    have := mHasTyHElems_mem
                                      (by simpa [MObj.hasTyH] using hrow)
                                      (hget ▸ elems.get_mem _)
                                    exact ⟨hwt₂, by
                                      simpa [WrappedExpr.ty,
                                        Typed.WrappedExpr.ty] using this⟩
  | pushPlace target => simp [resolveMBase] at hres
  | bool b => simp [resolveMBase] at hres
  | intLit ty v => simp [resolveMBase] at hres
  | mkCall kind ty name args => simp [resolveMBase] at hres
  | mkBinop op l r => simp [resolveMBase] at hres
  | mkUnop op arg => simp [resolveMBase] at hres
  | mkIncDec op target => simp [resolveMBase] at hres
  | mkTernary c t e => simp [resolveMBase] at hres
termination_by 4 * e.size + 0
decreasing_by all_goals
  first
  | omega
  | (simp [Typed.WrappedExpr.size] <;> omega)
  | (subst_vars
     simp [Typed.WrappedExpr.size, Typed.WrappedExpr.sizeList] <;> omega)

/-- `readM` yields a slot value of the expression's type. -/
theorem readM_wt {Γ : Ctx} {H : HeapTy} {L : Layout} {s : State}
    (e : WrappedExpr) {s' : State} {mv : MVal}
    (hwt : StateWT Γ H L s) (hexpr : wtExpr Γ L e = true)
    (hres : readM s e = Except.ok (s', mv)) :
    StateWT Γ H L s' ∧ MVal.hasTyH H mv e.ty = true := by
  cases e with
  | var kind ty fld =>
      rw [readM] at hres
      try dsimp only at hres
      simp only [State.getEnv, bind, Except.bind] at hres
      cases kind with
      | memory =>
          simp only [wtExpr, beq_iff_eq] at hexpr
          have henv := hwt.env
          simp only [envTypedB, Bool.and_eq_true] at henv
          have hrow := List.all_eq_true.mp henv.1 _
            (lookupBy_eq_some_mem hexpr)
          cases hlook : lookupBy fld.name s.env with
          | none => rw [hlook] at hrow; exact Bool.noConfusion hrow
          | some b =>
              rw [hlook] at hrow hres
              try dsimp only at hres
              cases b with
              | val v => exact nomatch hres
              | spath r sg => exact nomatch hres
              | mref mid =>
                  simp only [Except.ok.injEq, Prod.mk.injEq] at hres
                  obtain ⟨hs, hmv⟩ := hres
                  subst hs hmv
                  exact ⟨hwt, by
                    simpa [BTy.matchesB, WrappedExpr.ty,
                      Typed.WrappedExpr.ty] using hrow⟩
      | stack =>
          simp only [wtExpr, beq_iff_eq] at hexpr
          have henv := hwt.env
          simp only [envTypedB, Bool.and_eq_true] at henv
          have hrow := List.all_eq_true.mp henv.1 _
            (lookupBy_eq_some_mem hexpr)
          cases hlook : lookupBy fld.name s.env with
          | none => rw [hlook] at hrow; exact Bool.noConfusion hrow
          | some b =>
              rw [hlook] at hrow hres
              try dsimp only at hres
              cases b with
              | val v => exact nomatch hres
              | spath r sg => simp [BTy.matchesB] at hrow
              | mref mid => simp [BTy.matchesB] at hrow
      | storage =>
          simp only [wtExpr] at hexpr
          cases hΓ : lookupBy fld.name Γ with
          | none =>
              rw [hΓ] at hexpr
              cases hlook : lookupBy fld.name s.env with
              | none => rw [hlook] at hres; exact nomatch hres
              | some b =>
                  rw [hlook] at hres
                  try dsimp only at hres
                  cases b with
                  | val v => exact nomatch hres
                  | spath r sg =>
                      have henv := hwt.env
                      simp only [envTypedB, Bool.and_eq_true] at henv
                      have := List.all_eq_true.mp henv.2 _
                        (lookupBy_eq_some_mem hlook)
                      simp only [hΓ, Option.isSome_none] at this
                      exact Bool.noConfusion this
                  | mref mid =>
                      -- untracked `mref`: forbidden by `envTypedB`.
                      have henv := hwt.env
                      simp only [envTypedB, Bool.and_eq_true] at henv
                      have := List.all_eq_true.mp henv.2 _
                        (lookupBy_eq_some_mem hlook)
                      simp only [hΓ, Option.isSome_none] at this
                      exact Bool.noConfusion this
          | some bty =>
              rw [hΓ] at hexpr
              cases bty with
              | stack ty' => exact Bool.noConfusion hexpr
              | mem ty' => exact Bool.noConfusion hexpr
              | path ty' =>
                  simp only [Bool.and_eq_true, beq_iff_eq] at hexpr
                  have henv := hwt.env
                  simp only [envTypedB, Bool.and_eq_true] at henv
                  have hrow := List.all_eq_true.mp henv.1 _
                    (lookupBy_eq_some_mem hΓ)
                  cases hlook : lookupBy fld.name s.env with
                  | none => rw [hlook] at hrow; exact Bool.noConfusion hrow
                  | some b =>
                      rw [hlook] at hrow hres
                      try dsimp only at hres
                      cases b with
                      | val v => simp [BTy.matchesB] at hrow
                      | mref mid => simp [BTy.matchesB] at hrow
                      | spath r sg => exact nomatch hres
  | field kind ty base fld =>
      simp only [wtExpr, Bool.and_eq_true, beq_iff_eq] at hexpr
      rw [readM] at hres
      try dsimp only at hres
      try simp only [bind, Except.bind] at hres
      cases hbase : resolveMBase s base with
      | error e => rw [hbase] at hres; exact nomatch hres
      | ok out =>
          obtain ⟨s₁, baseId⟩ := out
          rw [hbase] at hres
          try dsimp only at hres
          obtain ⟨hwt₁, hbty⟩ := resolveMBase_wt base hwt hexpr.1 hbase
          simp only [State.getObj, bind, Except.bind] at hres
          cases hbt : base.ty with
          | prim pt => rw [hbt] at hexpr; simp [segTy] at hexpr
          | ref r =>
              cases r with
              | array elem => rw [hbt] at hexpr; simp [segTy] at hexpr
              | mapping k v => rw [hbt] at hexpr; simp [segTy] at hexpr
              | struct str =>
                  rw [hbt] at hexpr hbty
                  simp only [MVal.hasTyH, beq_iff_eq] at hbty
                  have hrow := List.all_eq_true.mp hwt₁.heap _
                    (lookupBy_eq_some_mem hbty)
                  cases hlook : lookupBy baseId s₁.heap with
                  | none => rw [hlook] at hrow; exact Bool.noConfusion hrow
                  | some obj =>
                      rw [hlook] at hrow hres
                      try dsimp only at hres
                      cases obj with
                      | array elems => simp [MObj.hasTyH] at hrow
                      | struct fields =>
                          try dsimp only at hres
                          cases hf : lookupBy fld.name fields with
                          | none => rw [hf] at hres; exact nomatch hres
                          | some fv =>
                              rw [hf] at hres
                              try dsimp only at hres
                              simp only [Except.ok.injEq,
                                Prod.mk.injEq] at hres
                              obtain ⟨hs, hmv⟩ := hres
                              subst hs hmv
                              obtain ⟨tyf, hdef, hmv⟩ :=
                                mHasTyHFields_lookup
                                  (by simpa [MObj.hasTyH] using hrow) hf
                              have : tyf = ty := by
                                simp only [segTy] at hexpr
                                rw [hdef] at hexpr
                                try dsimp only at hexpr
                                simpa using hexpr.2
                              subst this
                              exact ⟨hwt₁, by
                                simpa [WrappedExpr.ty,
                                  Typed.WrappedExpr.ty] using hmv⟩
  | index kind ty base index =>
      simp only [wtExpr, Bool.and_eq_true, beq_iff_eq] at hexpr
      rw [readM] at hres
      try dsimp only at hres
      try simp only [bind, Except.bind] at hres
      cases hbase : resolveMBase s base with
      | error e => rw [hbase] at hres; exact nomatch hres
      | ok out =>
          obtain ⟨s₁, baseId⟩ := out
          rw [hbase] at hres
          try dsimp only at hres
          obtain ⟨hwt₁, hbty⟩ := resolveMBase_wt base hwt hexpr.1.1 hbase
          cases hidx : evalInt s₁ index with
          | error e => rw [hidx] at hres; exact nomatch hres
          | ok out₂ =>
              obtain ⟨s₂, i⟩ := out₂
              rw [hidx] at hres
              try dsimp only at hres
              obtain ⟨hwt₂, _⟩ := evalInt_wt index hwt₁ hexpr.1.2 hidx
              simp only [State.getObj, bind, Except.bind] at hres
              cases hbt : base.ty with
              | prim pt => rw [hbt] at hexpr; simp [elemTy] at hexpr
              | ref r =>
                  cases r with
                  | struct str => rw [hbt] at hexpr; simp [elemTy] at hexpr
                  | mapping k v =>
                      rw [hbt] at hbty
                      try dsimp only at hbty
                      simp only [MVal.hasTyH, beq_iff_eq] at hbty
                      exact absurd hbty
                        (fun hc => heapTy_claim_not_mapping hwt₂.heap hc)
                  | array elem =>
                      rw [hbt] at hexpr hbty
                      simp only [MVal.hasTyH, beq_iff_eq] at hbty
                      have hrow := List.all_eq_true.mp hwt₂.heap _
                        (lookupBy_eq_some_mem hbty)
                      cases hlook : lookupBy baseId s₂.heap with
                      | none => rw [hlook] at hrow; exact Bool.noConfusion hrow
                      | some obj =>
                          rw [hlook] at hrow hres
                          try dsimp only at hres
                          cases obj with
                          | struct fields => simp [MObj.hasTyH] at hrow
                          | array elems =>
                              try dsimp only at hres
                              split at hres
                              case isFalse => exact nomatch hres
                              case isTrue hbound =>
                                simp only [Except.ok.injEq,
                                  Prod.mk.injEq] at hres
                                obtain ⟨hs, hmv⟩ := hres
                                subst hs hmv
                                have helem : elem = ty := by
                                  simp only [elemTy] at hexpr
                                  simpa using hexpr.2
                                subst helem
                                exact ⟨hwt₂, by
                                  simpa [WrappedExpr.ty,
                                    Typed.WrappedExpr.ty] using
                                    mHasTyHElems_mem
                                      (by simpa [MObj.hasTyH] using hrow)
                                      (elems.get_mem
                                        ⟨i.toNat, hbound.2⟩)⟩
  | pushPlace target => simp [readM] at hres
  | bool b => simp [readM] at hres
  | intLit ty v => simp [readM] at hres
  | mkCall kind ty name args => simp [readM] at hres
  | mkBinop op l r => simp [readM] at hres
  | mkUnop op arg => simp [readM] at hres
  | mkIncDec op target => simp [readM] at hres
  | mkTernary c t e => simp [readM] at hres
termination_by 4 * e.size + 1
decreasing_by all_goals
  first
  | omega
  | (simp [Typed.WrappedExpr.size] <;> omega)
  | (subst_vars
     simp [Typed.WrappedExpr.size, Typed.WrappedExpr.sizeList] <;> omega)

/-- `resolveLoc` lands on a location typed at the expression's
annotation. -/
theorem resolveLoc_wt {Γ : Ctx} {H : HeapTy} {L : Layout} {s : State}
    (e : WrappedExpr) {s' : State} {loc : Loc}
    (hwt : StateWT Γ H L s) (hexpr : wtExpr Γ L e = true)
    (hres : resolveLoc s e = Except.ok (s', loc)) :
    StateWT Γ H L s' ∧ LocTy Γ H L loc e.ty := by
  cases e with
  | var kind ty fld =>
      cases kind with
      | stack =>
          rw [resolveLoc] at hres
          try dsimp only at hres
          simp only [wtExpr, beq_iff_eq] at hexpr
          simp only [Except.ok.injEq, Prod.mk.injEq] at hres
          obtain ⟨hs, hloc⟩ := hres
          subst hs hloc
          exact ⟨hwt, by
            simpa [LocTy, WrappedExpr.ty, Typed.WrappedExpr.ty]
              using hexpr⟩
      | memory =>
          rw [resolveLoc] at hres
          try dsimp only at hres
          simp only [Except.ok.injEq, Prod.mk.injEq] at hres
          obtain ⟨hs, hloc⟩ := hres
          subst hs hloc
          exact ⟨hwt, trivial⟩
      | storage =>
          rw [resolveLoc] at hres
          try dsimp only at hres
          simp only [wtExpr] at hexpr
          cases hΓ : lookupBy fld.name Γ with
          | none =>
              rw [hΓ] at hexpr
              simp only [Bool.and_eq_true, beq_iff_eq] at hexpr
              rw [if_pos (by simp [hexpr.1])] at hres
              simp only [Except.ok.injEq, Prod.mk.injEq] at hres
              obtain ⟨hs, hloc⟩ := hres
              subst hs hloc
              exact ⟨hwt, by
                simpa [LocTy, Layout.tyAt, hexpr.2, tyAtSegs,
                  WrappedExpr.ty, Typed.WrappedExpr.ty] using rfl⟩
          | some bty =>
              rw [hΓ] at hexpr
              cases bty with
              | stack ty' => exact Bool.noConfusion hexpr
              | mem ty' => exact Bool.noConfusion hexpr
              | path ty' =>
                  simp only [Bool.and_eq_true, beq_iff_eq] at hexpr
                  rw [if_neg (by simp [hexpr.2])] at hres
                  simp only [Except.ok.injEq, Prod.mk.injEq] at hres
                  obtain ⟨hs, hloc⟩ := hres
                  subst hs hloc
                  exact ⟨hwt, trivial⟩
  | field kind ty base fld =>
      cases kind with
      | stack => simp [resolveLoc] at hres
      | storage =>
          rw [resolveLoc] at hres
          try dsimp only at hres
          try simp only [bind, Except.bind] at hres
          rw [resolveS_field_ty_irrel s Kind.storage Ty.uint ty base fld]
            at hres
          cases hrs : resolveS s (WrappedExpr.field Kind.storage ty
              base fld) with
          | error e => rw [hrs] at hres; exact nomatch hres
          | ok out =>
              obtain ⟨s₁, root, segs⟩ := out
              rw [hrs] at hres
              try dsimp only at hres
              obtain ⟨hwt₁, hty₁⟩ := resolveS_wt
                (WrappedExpr.field Kind.storage ty base fld)
                hwt hexpr hrs
              simp only [Except.ok.injEq, Prod.mk.injEq] at hres
              obtain ⟨hs, hloc⟩ := hres
              subst hs hloc
              exact ⟨hwt₁, by
                simpa [LocTy, WrappedExpr.ty, Typed.WrappedExpr.ty]
                  using hty₁⟩
      | memory =>
          rw [resolveLoc] at hres
          try dsimp only at hres
          simp only [wtExpr, Bool.and_eq_true, beq_iff_eq] at hexpr
          try simp only [bind, Except.bind] at hres
          cases hbase : resolveMBase s base with
          | error e => rw [hbase] at hres; exact nomatch hres
          | ok out =>
              obtain ⟨s₁, baseId⟩ := out
              rw [hbase] at hres
              try dsimp only at hres
              obtain ⟨hwt₁, hbty⟩ := resolveMBase_wt base hwt
                hexpr.1 hbase
              simp only [Except.ok.injEq, Prod.mk.injEq] at hres
              obtain ⟨hs, hloc'⟩ := hres
              subst hs hloc'
              refine ⟨hwt₁, ?_⟩
              cases hbt : base.ty with
              | prim pt => rw [hbt] at hexpr; simp [segTy] at hexpr
              | ref r =>
                  cases r with
                  | array elem =>
                      rw [hbt] at hexpr; simp [segTy] at hexpr
                  | mapping k v =>
                      rw [hbt] at hexpr; simp [segTy] at hexpr
                  | struct str =>
                      rw [hbt] at hexpr hbty
                      simp only [MVal.hasTyH, beq_iff_eq] at hbty
                      refine ⟨str, hbty, ?_⟩
                      simp only [segTy] at hexpr
                      simpa [WrappedExpr.ty, Typed.WrappedExpr.ty]
                        using hexpr.2
  | index kind ty base index =>
      cases kind with
      | stack => simp [resolveLoc] at hres
      | storage =>
          rw [resolveLoc] at hres
          try dsimp only at hres
          simp only [wtExpr, Bool.and_eq_true, beq_iff_eq] at hexpr
          try simp only [bind, Except.bind] at hres
          cases hbase : resolveS s base with
          | error e => rw [hbase] at hres; exact nomatch hres
          | ok out =>
              obtain ⟨s₁, root, segs⟩ := out
              rw [hbase] at hres
              try dsimp only at hres
              obtain ⟨hwt₁, hty₁⟩ := resolveS_wt base hwt hexpr.1.1 hbase
              cases hidx : evalInt s₁ index with
              | error e => rw [hidx] at hres; exact nomatch hres
              | ok out₂ =>
                  obtain ⟨s₂, i⟩ := out₂
                  rw [hidx] at hres
                  try dsimp only at hres
                  obtain ⟨hwt₂, _⟩ := evalInt_wt index hwt₁
                    hexpr.1.2 hidx
                  simp only [Except.ok.injEq, Prod.mk.injEq] at hres
                  obtain ⟨hs, hloc⟩ := hres
                  subst hs hloc
                  refine ⟨hwt₂, ?_⟩
                  have hseg : segTy base.ty (Seg.at i) = some ty := by
                    rw [segTy_at]
                    simpa using hexpr.2
                  simpa [LocTy, WrappedExpr.ty, Typed.WrappedExpr.ty]
                    using tyAt_append_seg hty₁ hseg
      | memory =>
          rw [resolveLoc] at hres
          try dsimp only at hres
          simp only [wtExpr, Bool.and_eq_true, beq_iff_eq] at hexpr
          try simp only [bind, Except.bind] at hres
          cases hbase : resolveMBase s base with
          | error e => rw [hbase] at hres; exact nomatch hres
          | ok out =>
              obtain ⟨s₁, baseId⟩ := out
              rw [hbase] at hres
              try dsimp only at hres
              obtain ⟨hwt₁, hbty⟩ := resolveMBase_wt base hwt
                hexpr.1.1 hbase
              cases hidx : evalInt s₁ index with
              | error e => rw [hidx] at hres; exact nomatch hres
              | ok out₂ =>
                  obtain ⟨s₂, i⟩ := out₂
                  rw [hidx] at hres
                  try dsimp only at hres
                  obtain ⟨hwt₂, _⟩ := evalInt_wt index hwt₁
                    hexpr.1.2 hidx
                  simp only [Except.ok.injEq, Prod.mk.injEq] at hres
                  obtain ⟨hs, hloc⟩ := hres
                  subst hs hloc
                  refine ⟨hwt₂, ?_⟩
                  cases hbt : base.ty with
                  | prim pt => rw [hbt] at hexpr; simp [elemTy] at hexpr
                  | ref r =>
                      cases r with
                      | struct str =>
                          rw [hbt] at hexpr; simp [elemTy] at hexpr
                      | mapping k v =>
                          rw [hbt] at hbty
                          try dsimp only at hbty
                          simp only [MVal.hasTyH, beq_iff_eq] at hbty
                          exact absurd hbty (fun hc =>
                            heapTy_claim_not_mapping hwt₂.heap hc)
                      | array elem =>
                          rw [hbt] at hexpr hbty
                          simp only [MVal.hasTyH, beq_iff_eq] at hbty
                          have helem : elem = ty := by
                            simp only [elemTy] at hexpr
                            simpa using hexpr.2
                          subst helem
                          simpa [LocTy, WrappedExpr.ty,
                            Typed.WrappedExpr.ty] using hbty
  | pushPlace target =>
      rw [resolveLoc] at hres
      try dsimp only at hres
      try simp only [bind, Except.bind] at hres
      cases hrs : resolveS s (WrappedExpr.pushPlace target) with
      | error e => rw [hrs] at hres; exact nomatch hres
      | ok out =>
          obtain ⟨s₁, root, segs⟩ := out
          rw [hrs] at hres
          try dsimp only at hres
          obtain ⟨hwt₁, hty₁⟩ := resolveS_wt
            (WrappedExpr.pushPlace target) hwt hexpr hrs
          simp only [Except.ok.injEq, Prod.mk.injEq] at hres
          obtain ⟨hs, hloc⟩ := hres
          subst hs hloc
          exact ⟨hwt₁, hty₁⟩
  | bool b => simp [resolveLoc] at hres
  | intLit ty v => simp [resolveLoc] at hres
  | mkCall kind ty name args => simp [resolveLoc] at hres
  | mkBinop op l r => simp [resolveLoc] at hres
  | mkUnop op arg => simp [resolveLoc] at hres
  | mkIncDec op target => simp [resolveLoc] at hres
  | mkTernary c t e => simp [resolveLoc] at hres
termination_by 4 * e.size + 1
decreasing_by all_goals
  first
  | omega
  | (simp [Typed.WrappedExpr.size] <;> omega)
  | (subst_vars
     simp [Typed.WrappedExpr.size, Typed.WrappedExpr.sizeList] <;> omega)

/-- `evalValue` produces a value inhabiting the expression's
annotation, preserving the invariant (`++`/`--` writes through
`writeLoc_wt`). -/
theorem evalValue_wt {Γ : Ctx} {H : HeapTy} {L : Layout} {s : State}
    (e : WrappedExpr) {s' : State} {v : Value}
    (hwt : StateWT Γ H L s) (hexpr : wtExpr Γ L e = true)
    (hres : evalValue s e = Except.ok (s', v)) :
    StateWT Γ H L s' ∧ (Value.toSVal v).hasTy e.ty = true := by
  cases e with
  | bool b =>
      rw [evalValue] at hres
      try dsimp only at hres
      simp only [Except.ok.injEq, Prod.mk.injEq] at hres
      obtain ⟨hs, hv⟩ := hres
      subst hs hv
      exact ⟨hwt, rfl⟩
  | intLit ty n =>
      rw [evalValue] at hres
      try dsimp only at hres
      simp only [Except.ok.injEq, Prod.mk.injEq] at hres
      obtain ⟨hs, hv⟩ := hres
      subst hs hv
      exact ⟨hwt, by
        simpa [WrappedExpr.ty, Typed.WrappedExpr.ty] using
          int_hasTy_numeric (by simpa [wtExpr] using hexpr) n⟩
  | var kind ty fld =>
      cases kind with
      | stack =>
          rw [evalValue] at hres
          try dsimp only at hres
          simp only [wtExpr, beq_iff_eq] at hexpr
          simp only [State.getEnv, bind, Except.bind] at hres
          have henv := hwt.env
          simp only [envTypedB, Bool.and_eq_true] at henv
          have hrow := List.all_eq_true.mp henv.1 _
            (lookupBy_eq_some_mem hexpr)
          cases hlook : lookupBy fld.name s.env with
          | none => rw [hlook] at hrow; exact Bool.noConfusion hrow
          | some b =>
              rw [hlook] at hrow hres
              try dsimp only at hres
              cases b with
              | val w =>
                  simp only [Except.ok.injEq, Prod.mk.injEq] at hres
                  obtain ⟨hs, hv⟩ := hres
                  subst hs hv
                  exact ⟨hwt, by
                    simpa [BTy.matchesB, WrappedExpr.ty,
                      Typed.WrappedExpr.ty] using hrow⟩
              | spath r sg => exact nomatch hres
              | mref id => exact nomatch hres
      | memory => simp [evalValue] at hres
      | storage =>
          rw [evalValue] at hres
          try dsimp only at hres
          try simp only [bind, Except.bind] at hres
          cases hrs : resolveS s (WrappedExpr.var Kind.storage ty fld)
            with
          | error e => rw [hrs] at hres; exact nomatch hres
          | ok out =>
              obtain ⟨s₁, root, segs⟩ := out
              rw [hrs] at hres
              try dsimp only at hres
              obtain ⟨hwt₁, hty₁⟩ := resolveS_wt
                (WrappedExpr.var Kind.storage ty fld) hwt hexpr hrs
              cases hfind : s₁.findStorage root segs with
              | error e => rw [hfind] at hres; exact nomatch hres
              | ok sv =>
                  rw [hfind] at hres
                  try dsimp only at hres
                  have hsty := findStorage_hasTy hwt₁.storage hty₁ hfind
                  cases hval : sv.asValue with
                  | error e => rw [hval] at hres; exact nomatch hres
                  | ok w =>
                      rw [hval] at hres
                      try dsimp only at hres
                      simp only [Except.ok.injEq, Prod.mk.injEq] at hres
                      obtain ⟨hs, hv⟩ := hres
                      subst hs hv
                      rw [SVal.asValue_toSVal hval]
                      exact ⟨hwt₁, hsty⟩
  | field kind ty base fld =>
      cases kind with
      | stack => simp [evalValue] at hres
      | storage =>
          rw [evalValue] at hres
          try dsimp only at hres
          try simp only [bind, Except.bind] at hres
          cases hrs : resolveS s
              (WrappedExpr.field Kind.storage ty base fld) with
          | error e => rw [hrs] at hres; exact nomatch hres
          | ok out =>
              obtain ⟨s₁, root, segs⟩ := out
              rw [hrs] at hres
              try dsimp only at hres
              obtain ⟨hwt₁, hty₁⟩ := resolveS_wt
                (WrappedExpr.field Kind.storage ty base fld) hwt
                hexpr hrs
              cases hfind : s₁.findStorage root segs with
              | error e => rw [hfind] at hres; exact nomatch hres
              | ok sv =>
                  rw [hfind] at hres
                  try dsimp only at hres
                  have hsty := findStorage_hasTy hwt₁.storage hty₁ hfind
                  cases hval : sv.asValue with
                  | error e => rw [hval] at hres; exact nomatch hres
                  | ok w =>
                      rw [hval] at hres
                      try dsimp only at hres
                      simp only [Except.ok.injEq, Prod.mk.injEq] at hres
                      obtain ⟨hs, hv⟩ := hres
                      subst hs hv
                      rw [SVal.asValue_toSVal hval]
                      exact ⟨hwt₁, hsty⟩
      | memory =>
          rw [evalValue] at hres
          try dsimp only at hres
          try simp only [bind, Except.bind] at hres
          cases hrm : readM s (WrappedExpr.field Kind.memory ty base fld)
            with
          | error e => rw [hrm] at hres; exact nomatch hres
          | ok out =>
              obtain ⟨s₁, mv⟩ := out
              rw [hrm] at hres
              try dsimp only at hres
              obtain ⟨hwt₁, hmty⟩ := readM_wt
                (WrappedExpr.field Kind.memory ty base fld) hwt hexpr hrm
              cases hval : mv.asValue with
              | error e => rw [hval] at hres; exact nomatch hres
              | ok w =>
                  rw [hval] at hres
                  try dsimp only at hres
                  simp only [Except.ok.injEq, Prod.mk.injEq] at hres
                  obtain ⟨hs, hv⟩ := hres
                  subst hs hv
                  exact ⟨hwt₁, MVal.asValue_toSVal_hasTy hmty hval⟩
  | index kind ty base index =>
      cases kind with
      | stack => simp [evalValue] at hres
      | storage =>
          rw [evalValue] at hres
          try dsimp only at hres
          try simp only [bind, Except.bind] at hres
          cases hrs : resolveS s
              (WrappedExpr.index Kind.storage ty base index) with
          | error e => rw [hrs] at hres; exact nomatch hres
          | ok out =>
              obtain ⟨s₁, root, segs⟩ := out
              rw [hrs] at hres
              try dsimp only at hres
              obtain ⟨hwt₁, hty₁⟩ := resolveS_wt
                (WrappedExpr.index Kind.storage ty base index) hwt
                hexpr hrs
              cases hfind : s₁.findStorage root segs with
              | error e => rw [hfind] at hres; exact nomatch hres
              | ok sv =>
                  rw [hfind] at hres
                  try dsimp only at hres
                  have hsty := findStorage_hasTy hwt₁.storage hty₁ hfind
                  cases hval : sv.asValue with
                  | error e => rw [hval] at hres; exact nomatch hres
                  | ok w =>
                      rw [hval] at hres
                      try dsimp only at hres
                      simp only [Except.ok.injEq, Prod.mk.injEq] at hres
                      obtain ⟨hs, hv⟩ := hres
                      subst hs hv
                      rw [SVal.asValue_toSVal hval]
                      exact ⟨hwt₁, hsty⟩
      | memory =>
          rw [evalValue] at hres
          try dsimp only at hres
          try simp only [bind, Except.bind] at hres
          cases hrm : readM s
              (WrappedExpr.index Kind.memory ty base index) with
          | error e => rw [hrm] at hres; exact nomatch hres
          | ok out =>
              obtain ⟨s₁, mv⟩ := out
              rw [hrm] at hres
              try dsimp only at hres
              obtain ⟨hwt₁, hmty⟩ := readM_wt
                (WrappedExpr.index Kind.memory ty base index) hwt
                hexpr hrm
              cases hval : mv.asValue with
              | error e => rw [hval] at hres; exact nomatch hres
              | ok w =>
                  rw [hval] at hres
                  try dsimp only at hres
                  simp only [Except.ok.injEq, Prod.mk.injEq] at hres
                  obtain ⟨hs, hv⟩ := hres
                  subst hs hv
                  exact ⟨hwt₁, MVal.asValue_toSVal_hasTy hmty hval⟩
  | mkBinop op l r =>
      simp only [wtExpr, Bool.and_eq_true] at hexpr
      rw [evalValue] at hres
      try dsimp only at hres
      try simp only [bind, Except.bind] at hres
      cases hl : evalValue s l with
      | error e => rw [hl] at hres; exact nomatch hres
      | ok out =>
          obtain ⟨s₁, lv⟩ := out
          rw [hl] at hres
          try dsimp only at hres
          obtain ⟨hwt₁, hlty⟩ := evalValue_wt l hwt hexpr.1 hl
          split at hres
          -- `&&` short-circuit
          case h_1 =>
            simp only [Except.ok.injEq, Prod.mk.injEq] at hres
            obtain ⟨hs, hv⟩ := hres
            subst hs hv
            exact ⟨hwt₁, by
              simp [WrappedExpr.ty, Typed.WrappedExpr.ty, BinOp.retTy,
                BinOp.isArith, Value.toSVal, SVal.hasTy]⟩
          -- `||` short-circuit
          case h_2 =>
            simp only [Except.ok.injEq, Prod.mk.injEq] at hres
            obtain ⟨hs, hv⟩ := hres
            subst hs hv
            exact ⟨hwt₁, by
              simp [WrappedExpr.ty, Typed.WrappedExpr.ty, BinOp.retTy,
                BinOp.isArith, Value.toSVal, SVal.hasTy]⟩
          case h_3 =>
            try simp only [bind, Except.bind] at hres
            cases hr : evalValue s₁ r with
            | error e => rw [hr] at hres; exact nomatch hres
            | ok out₂ =>
                obtain ⟨s₂, rv⟩ := out₂
                rw [hr] at hres
                try dsimp only at hres
                obtain ⟨hwt₂, hrty⟩ := evalValue_wt r hwt₁ hexpr.2 hr
                cases happ : applyBinOp op lv rv with
                | error e => rw [happ] at hres; exact nomatch hres
                | ok v₀ =>
                    rw [happ] at hres
                    try dsimp only at hres
                    cases hchk : checkArith (op.retTy l.ty) v₀ with
                    | error e => rw [hchk] at hres; exact nomatch hres
                    | ok v₁ =>
                        rw [hchk] at hres
                        try dsimp only at hres
                        simp only [Except.ok.injEq, Prod.mk.injEq]
                          at hres
                        obtain ⟨hs, hv⟩ := hres
                        subst hs hv
                        rw [checkArith_ok_eq hchk]
                        refine ⟨hwt₂, ?_⟩
                        cases hArith : op.isArith with
                        | true =>
                            obtain ⟨n, hn⟩ :=
                              applyBinOp_arith_int hArith happ
                            obtain ⟨m, hm⟩ :=
                              applyBinOp_arith_lhs_int hArith happ
                            subst hn hm
                            have hnum : isNumericTy l.ty = true :=
                              hasTy_int_numeric hlty
                            simpa [WrappedExpr.ty, Typed.WrappedExpr.ty,
                              BinOp.retTy, hArith] using
                              int_hasTy_numeric hnum n
                        | false =>
                            obtain ⟨b, hb⟩ :=
                              applyBinOp_nonarith_bool hArith happ
                            subst hb
                            simp [WrappedExpr.ty, Typed.WrappedExpr.ty,
                              BinOp.retTy, hArith, Value.toSVal,
                              SVal.hasTy]
  | mkUnop op arg =>
      simp only [wtExpr] at hexpr
      rw [evalValue] at hres
      try dsimp only at hres
      try simp only [bind, Except.bind] at hres
      cases ha : evalValue s arg with
      | error e => rw [ha] at hres; exact nomatch hres
      | ok out =>
          obtain ⟨s₁, av⟩ := out
          rw [ha] at hres
          try dsimp only at hres
          obtain ⟨hwt₁, haty⟩ := evalValue_wt arg hwt hexpr ha
          cases happ : applyUnOp op av with
          | error e => rw [happ] at hres; exact nomatch hres
          | ok v₀ =>
              rw [happ] at hres
              try dsimp only at hres
              cases op with
              | not =>
                  -- `!` never goes through `checkArith`: the
                  -- `(neg, int)` arm cannot match.
                  simp only [Except.ok.injEq, Prod.mk.injEq] at hres
                  obtain ⟨hs, hv⟩ := hres
                  subst hs hv
                  simp only [applyUnOp, bind, Except.bind] at happ
                  cases hb : av.asBool with
                  | error e => rw [hb] at happ; exact nomatch happ
                  | ok b =>
                      rw [hb] at happ
                      try dsimp only at happ
                      refine ⟨hwt₁, ?_⟩
                      simp [<- Except.ok.inj happ, WrappedExpr.ty,
                        Typed.WrappedExpr.ty, UnOp.retTy,
                        Value.toSVal, SVal.hasTy]
              | neg =>
                  simp only [applyUnOp, bind, Except.bind] at happ
                  cases hn : av.asInt with
                  | error e => rw [hn] at happ; exact nomatch happ
                  | ok n =>
                      rw [hn] at happ
                      try dsimp only at happ
                      have hav : ∃ m, av = Value.int m := by
                        cases av with
                        | int m => exact ⟨m, rfl⟩
                        | bool b => exact nomatch hn
                      obtain ⟨m, hm⟩ := hav
                      subst hm
                      have hnum : isNumericTy arg.ty = true :=
                        hasTy_int_numeric haty
                      split at hres
                      case h_2 hne =>
                        simp only [Except.ok.injEq, Prod.mk.injEq]
                          at hres
                        obtain ⟨hs, hv⟩ := hres
                        subst hs hv
                        refine ⟨hwt₁, ?_⟩
                        simpa [<- Except.ok.inj happ, WrappedExpr.ty,
                          Typed.WrappedExpr.ty, UnOp.retTy] using
                          int_hasTy_numeric hnum (-n)
                      case h_1 heq =>
                        try simp only [bind, Except.bind] at hres
                        cases hchk : checkArith Ty.int v₀ with
                        | error e => rw [hchk] at hres; exact nomatch hres
                        | ok v₁ =>
                            rw [hchk] at hres
                            try dsimp only at hres
                            simp only [Except.ok.injEq, Prod.mk.injEq]
                              at hres
                            obtain ⟨hs, hv⟩ := hres
                            subst hs hv
                            rw [checkArith_ok_eq hchk]
                            refine ⟨hwt₁, ?_⟩
                            simpa [<- Except.ok.inj happ, WrappedExpr.ty,
                              Typed.WrappedExpr.ty, UnOp.retTy] using
                              int_hasTy_numeric hnum (-n)
  | mkIncDec op target =>
      simp only [wtExpr] at hexpr
      rw [evalValue] at hres
      try dsimp only at hres
      try simp only [bind, Except.bind] at hres
      cases hloc : resolveLoc s target with
      | error e => rw [hloc] at hres; exact nomatch hres
      | ok out =>
          obtain ⟨s₁, loc⟩ := out
          rw [hloc] at hres
          try dsimp only at hres
          obtain ⟨hwt₁, hlocty⟩ := resolveLoc_wt target hwt hexpr hloc
          cases hold : readLoc s₁ loc with
          | error e => rw [hold] at hres; exact nomatch hres
          | ok old =>
              rw [hold] at hres
              try dsimp only at hres
              have holdty := readLoc_wt hwt₁ hlocty hold
              cases hint : old.asInt with
              | error e => rw [hint] at hres; exact nomatch hres
              | ok oldInt =>
                  rw [hint] at hres
                  try dsimp only at hres
                  have hOld : old = Value.int oldInt := by
                    cases old with
                    | int m =>
                        simp only [Value.asInt, Except.ok.injEq] at hint
                        rw [hint]
                    | bool b => exact nomatch hint
                  have hnum : isNumericTy target.ty = true := by
                    subst hOld
                    exact hasTy_int_numeric holdty
                  try simp only [bind, Except.bind] at hres
                  cases hchk : checkArith target.ty
                      (Value.int (if op.isIncrement then oldInt + 1
                        else oldInt - 1)) with
                  | error e => rw [hchk] at hres; exact nomatch hres
                  | ok newVal =>
                      rw [hchk] at hres
                      try dsimp only at hres
                      have hNew := checkArith_ok_eq hchk
                      cases hwr : writeLoc s₁ loc newVal with
                      | error e => rw [hwr] at hres; exact nomatch hres
                      | ok s₂ =>
                          rw [hwr] at hres
                          try dsimp only at hres
                          have hnewty : (Value.toSVal newVal).hasTy
                              target.ty = true := by
                            rw [hNew]
                            exact int_hasTy_numeric hnum _
                          have hwt₂ := writeLoc_wt hwt₁ hlocty hnewty hwr
                          simp only [Except.ok.injEq, Prod.mk.injEq]
                            at hres
                          obtain ⟨hs, hv⟩ := hres
                          subst hs hv
                          refine ⟨hwt₂, ?_⟩
                          split
                          · simpa [WrappedExpr.ty, Typed.WrappedExpr.ty]
                              using hnewty
                          · subst hOld
                            simpa [WrappedExpr.ty, Typed.WrappedExpr.ty]
                              using holdty
  | mkTernary c t els =>
      simp only [wtExpr, Bool.and_eq_true, beq_iff_eq] at hexpr
      rw [evalValue] at hres
      try dsimp only at hres
      try simp only [bind, Except.bind] at hres
      cases hc : evalValue s c with
      | error e => rw [hc] at hres; exact nomatch hres
      | ok out =>
          obtain ⟨s₁, cv⟩ := out
          rw [hc] at hres
          try dsimp only at hres
          obtain ⟨hwt₁, _⟩ := evalValue_wt c hwt hexpr.1.1.1 hc
          cases cv with
          | int n => exact nomatch hres
          | bool b =>
              cases b with
              | true =>
                  obtain ⟨hwt₂, hty⟩ :=
                    evalValue_wt t hwt₁ hexpr.1.1.2 hres
                  exact ⟨hwt₂, by
                    simpa [WrappedExpr.ty, Typed.WrappedExpr.ty]
                      using hty⟩
              | false =>
                  obtain ⟨hwt₂, hty⟩ :=
                    evalValue_wt els hwt₁ hexpr.1.2 hres
                  refine ⟨hwt₂, ?_⟩
                  simpa [WrappedExpr.ty, Typed.WrappedExpr.ty, hexpr.2]
                    using hty
  | mkCall kind ty name args =>
      rw [evalValue.eq_def] at hres
      try dsimp only at hres
      split at hres
      any_goals (rename_i heq'; exact Typed.WrappedExpr.noConfusion heq')
      · rename_i kind₀ ty₀ addr heq'
        injection heq' with hk ht hn ha
        subst hk ht hn ha
        simp only [wtExpr, Bool.and_eq_true] at hexpr
        try simp only [bind, Except.bind] at hres
        cases haddr : evalInt s addr with
        | error e => rw [haddr] at hres; exact nomatch hres
        | ok out =>
            obtain ⟨s₁, a⟩ := out
            rw [haddr] at hres
            try dsimp only at hres
            obtain ⟨hwt₁, _⟩ := evalInt_wt addr hwt hexpr.2 haddr
            simp only [Except.ok.injEq, Prod.mk.injEq] at hres
            obtain ⟨hs, hv⟩ := hres
            subst hs hv
            exact ⟨hwt₁, by
              simpa [WrappedExpr.ty, Typed.WrappedExpr.ty] using
                int_hasTy_numeric hexpr.1 _⟩
      · exact nomatch hres
  | pushPlace target => simp [evalValue] at hres
termination_by 4 * e.size + 2
decreasing_by all_goals
  first
  | omega
  | (simp [Typed.WrappedExpr.size, Typed.WrappedExpr.sizeList] <;> omega)
  | (subst_vars
     simp [Typed.WrappedExpr.size, Typed.WrappedExpr.sizeList] <;> omega)

/-- `evalInt` succeeds only at numeric annotations, preserving the
invariant. -/
theorem evalInt_wt {Γ : Ctx} {H : HeapTy} {L : Layout} {s : State}
    (e : WrappedExpr) {s' : State} {n : Int}
    (hwt : StateWT Γ H L s) (hexpr : wtExpr Γ L e = true)
    (hres : evalInt s e = Except.ok (s', n)) :
    StateWT Γ H L s' ∧ isNumericTy e.ty = true := by
  rw [evalInt] at hres
  try dsimp only at hres
  try simp only [bind, Except.bind] at hres
  cases hv : evalValue s e with
  | error err => rw [hv] at hres; exact nomatch hres
  | ok out =>
      obtain ⟨s₁, v⟩ := out
      rw [hv] at hres
      try dsimp only at hres
      obtain ⟨hwt₁, hty⟩ := evalValue_wt e hwt hexpr hv
      cases v with
      | int m =>
          simp only [Value.asInt, Except.ok.injEq, Prod.mk.injEq] at hres
          obtain ⟨hs, hn⟩ := hres
          subst hs
          exact ⟨hwt₁, hasTy_int_numeric hty⟩
      | bool b => exact nomatch hres
termination_by 4 * e.size + 3
decreasing_by all_goals omega

end

/-! ## Part 2: statement-level soundness

`stmtWt` threads the context: declarations extend Γ (shadowing
replaces — `setBy` keeps Γ and env in lockstep), every component
expression must be well-annotated, and the statement-shape side
conditions (`op.isArith`, `defaultOk` wherever a default value is
manufactured, type agreement across an assignment) are exactly what
the arm proofs consume.

v1 exclusions, documented at their arms: `ite` branches must leave Γ
unchanged (the interpreter has no scoping, so a branch-local
declaration leaks a binding the join cannot type — the KeY rule set
hoists declarations too), and `callStmt` is stuck by design (calls
are inlined before execution). -/

theorem mem_of_mem_setBy_ne [DecidableEq κ] {l : List (κ × α)} {k : κ}
    {v : α} {g : κ × α} (hg : g ∈ setBy k v l) (hne : g.1 ≠ k) :
    g ∈ l := by
  induction l with
  | nil =>
      simp only [setBy] at hg
      cases hg with
      | head => exact absurd rfl hne
      | tail _ h => cases h
  | cons q rest ih =>
      obtain ⟨k', v'⟩ := q
      by_cases hk : k = k'
      · rw [setBy, if_pos hk] at hg
        cases hg with
        | head => exact absurd rfl hne
        | tail _ h => exact List.Mem.tail _ h
      · rw [setBy, if_neg hk] at hg
        cases hg with
        | head => exact List.Mem.head _
        | tail _ h => exact List.Mem.tail _ (ih h)

/-- The write half of `writeLoc_wt` for a full slot value (the nested
memory assignment and memory `delete` write `MVal`s, not just stack
values): struct-field arm. -/
theorem setObjField_wt {Γ : Ctx} {H : HeapTy} {L : Layout} {s : State}
    {id : Nat} {fld : Name} {str : Name} {ty : Ty} {mv : MVal}
    {fields : List (Name × MVal)}
    (hwt : StateWT Γ H L s)
    (hclaim : lookupBy id H = some (Ty.ref (RefTy.struct str)))
    (hdef : lookupBy fld (structDef str) = some ty)
    (hmv : MVal.hasTyH H mv ty = true)
    (hobj : lookupBy id s.heap = some (MObj.struct fields)) :
    StateWT Γ H L (s.setObj id (MObj.struct (setBy fld mv fields))) := by
  have hrow := List.all_eq_true.mp hwt.heap _
    (lookupBy_eq_some_mem hclaim)
  rw [hobj] at hrow
  try dsimp only at hrow
  refine { hwt with heap := ?_, heapWf := ?_ }
  · exact heapTypedB_setObj hwt.heapTyNodup hwt.heap hclaim
      (by
        simp only [MObj.hasTyH]
        exact mHasTyHFields_setBy (by simpa [MObj.hasTyH] using hrow)
          hdef hmv)
  · exact HeapWellFormed.setObj hwt.heapWf (by simp [hobj])

/-- …and the array-element arm. -/
theorem setObjIndex_wt {Γ : Ctx} {H : HeapTy} {L : Layout} {s : State}
    {id : Nat} {i : Nat} {ty : Ty} {mv : MVal} {elems : List MVal}
    (hwt : StateWT Γ H L s)
    (hclaim : lookupBy id H = some (Ty.ref (RefTy.array ty)))
    (hmv : MVal.hasTyH H mv ty = true)
    (hobj : lookupBy id s.heap = some (MObj.array elems)) :
    StateWT Γ H L (s.setObj id (MObj.array (elems.set i mv))) := by
  have hrow := List.all_eq_true.mp hwt.heap _
    (lookupBy_eq_some_mem hclaim)
  rw [hobj] at hrow
  try dsimp only at hrow
  refine { hwt with heap := ?_, heapWf := ?_ }
  · exact heapTypedB_setObj hwt.heapTyNodup hwt.heap hclaim
      (by
        simp only [MObj.hasTyH]
        exact mHasTyHElems_set (by simpa [MObj.hasTyH] using hrow) hmv)
  · exact HeapWellFormed.setObj hwt.heapWf (by simp [hobj])

/-- Transfer the invariant across a `CopyOut` (storage→memory copies
extend the store typing; everything already typed weakens along). -/
theorem StateWT.ofCopyOut {Γ : Ctx} {H H' : HeapTy} {L : Layout}
    {s s' : State} (hwt : StateWT Γ H L s)
    (hout : CopyOut H s H' s') : StateWT Γ H' L s' :=
  { layoutNodup := hwt.layoutNodup
    ctxNodup := hwt.ctxNodup
    heapTyNodup := hout.nodup
    storage := by rw [hout.storage]; exact hwt.storage
    env := by rw [hout.env]; exact envTypedB_mono hout.ext hwt.env
    heap := hout.heap
    heapWf := hout.heapWf }

/-- Rebinding a Γ-tracked name only (no Γ change). -/
theorem StateWT.withEnv {Γ : Ctx} {H : HeapTy} {L : Layout}
    {s : State} {name : Name} {b : Binding}
    (hwt : StateWT Γ H L s)
    (henv : envTypedB Γ L H (setBy name b s.env) = true) :
    StateWT Γ H L (s.setEnv name b) :=
  { hwt with env := henv }

/-- Storage write at a layout-typed path. -/
theorem StateWT.ofSaveStorage {Γ : Ctx} {H : HeapTy} {L : Layout}
    {s s' : State} {root : Name} {segs : List Seg} {ty' : Ty}
    {new : SVal}
    (hwt : StateWT Γ H L s) (hty : L.tyAt root segs = some ty')
    (hnew : new.hasTy ty' = true)
    (hsave : s.saveStorage root segs new = Except.ok s') :
    StateWT Γ H L s' := by
  have hst' := State.saveStorage_wellTyped hwt.layoutNodup hwt.storage
    hty hnew hsave
  obtain ⟨hheap, hnext, henv, _⟩ :=
    SemanticsProperties.State.saveStorage_frame hsave
  refine { hwt with
            storage := hst', env := ?_, heap := ?_, heapWf := ?_ }
  · rw [henv]; exact hwt.env
  · rw [hheap]; exact hwt.heap
  · intro i hi
    rw [hheap]
    exact hwt.heapWf i (hnext ▸ hi)

/-- Declaring a (possibly shadowing) name: extend Γ and env in
lockstep. -/
theorem StateWT.extendCtx {Γ : Ctx} {H : HeapTy} {L : Layout}
    {s : State} {name : Name} {bty : BTy} {b : Binding}
    (hwt : StateWT Γ H L s)
    (hmatch : BTy.matchesB L H bty b = true) :
    StateWT (setBy name bty Γ) H L (s.setEnv name b) := by
  refine { hwt with
            ctxNodup := nodupKeysB_setBy hwt.ctxNodup, env := ?_ }
  have henv := hwt.env
  simp only [envTypedB, Bool.and_eq_true] at henv ⊢
  refine ⟨?_, ?_⟩
  · refine List.all_eq_true.mpr fun g hg => ?_
    show (match lookupBy g.1 (setBy name b s.env) with
      | some b' => BTy.matchesB L H g.2 b'
      | none => false) = true
    by_cases hn : g.1 = name
    · have hg2 : g.2 = bty := by
        have hl := lookupBy_eq_of_nodup
          (nodupKeysB_setBy hwt.ctxNodup) hg
        rw [hn, lookupBy_setBy_self] at hl
        try dsimp only at hl
        exact (Option.some.inj hl).symm
      rw [hn, lookupBy_setBy_self, hg2]
      exact hmatch
    · rw [lookupBy_setBy_ne hn]
      exact List.all_eq_true.mp henv.1 g (mem_of_mem_setBy_ne hg hn)
  · have hlift : (s.env.all fun nb =>
        match nb.2 with
        | Binding.spath _ _ =>
            (lookupBy nb.1 (setBy name bty Γ)).isSome
        | Binding.mref _ =>
            (lookupBy nb.1 (setBy name bty Γ)).isSome
        | _ => true) = true := by
      refine List.all_eq_true.mpr fun nb hnb => ?_
      have hold := List.all_eq_true.mp henv.2 nb hnb
      revert hold
      show (match nb.2 with
          | Binding.spath _ _ => (lookupBy nb.1 Γ).isSome
          | Binding.mref _ => (lookupBy nb.1 Γ).isSome
          | _ => true) = true ->
        (match nb.2 with
          | Binding.spath _ _ =>
              (lookupBy nb.1 (setBy name bty Γ)).isSome
          | Binding.mref _ =>
              (lookupBy nb.1 (setBy name bty Γ)).isSome
          | _ => true) = true
      cases nb.2 with
      | val v => intro _; rfl
      | spath r sg =>
          intro hold
          by_cases hn : nb.1 = name
          · rw [hn, lookupBy_setBy_self]; rfl
          · rw [lookupBy_setBy_ne hn]; exact hold
      | mref id =>
          intro hold
          by_cases hn : nb.1 = name
          · rw [hn, lookupBy_setBy_self]; rfl
          · rw [lookupBy_setBy_ne hn]; exact hold
    refine all_setBy hlift ?_
    cases b <;> simp [lookupBy_setBy_self]

theorem LocTy_mono {Γ : Ctx} {H H' : HeapTy} {L : Layout} {loc : Loc}
    {ty : Ty} (hext : H.Extends H') (h : LocTy Γ H L loc ty) :
    LocTy Γ H' L loc ty := by
  cases loc with
  | stack n => exact h
  | storageLocal n => trivial
  | memoryRoot n => trivial
  | storage r sg => exact h
  | memoryField id fld =>
      obtain ⟨str, hc, hd⟩ := h
      exact ⟨str, hext _ _ hc, hd⟩
  | memoryIndex id i => exact hext _ _ h

/-- `rhsToSVal` produces a storage value of the rhs annotation
(`H`-stable: nothing here allocates). -/
theorem rhsToSVal_wt {Γ : Ctx} {H : HeapTy} {L : Layout} {s s' : State}
    {rhs : WrappedExpr} {sv : SVal}
    (hwt : StateWT Γ H L s) (hrhs : wtExpr Γ L rhs = true)
    (h : rhsToSVal s rhs = Except.ok (s', sv)) :
    StateWT Γ H L s' ∧ sv.hasTy rhs.ty = true := by
  rw [rhsToSVal] at h
  try dsimp only at h
  split at h
  · simp only [bind, Except.bind] at h
    cases hv : evalValue s rhs with
    | error e => rw [hv] at h; exact nomatch h
    | ok out =>
        obtain ⟨s₁, v⟩ := out
        rw [hv] at h
        try dsimp only at h
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨hs, hsv⟩ := h
        subst hs hsv
        exact evalValue_wt rhs hwt hrhs hv
  · split at h
    · split at h
      · exact nomatch h
      · simp only [bind, Except.bind] at h
        cases hrs : resolveS s rhs with
        | error e => rw [hrs] at h; exact nomatch h
        | ok out =>
            obtain ⟨s₁, root, segs⟩ := out
            rw [hrs] at h
            try dsimp only at h
            obtain ⟨hwt₁, hty₁⟩ := resolveS_wt rhs hwt hrhs hrs
            cases hfind : s₁.findStorage root segs with
            | error e => rw [hfind] at h; exact nomatch h
            | ok v =>
                rw [hfind] at h
                try dsimp only at h
                simp only [Except.ok.injEq, Prod.mk.injEq] at h
                obtain ⟨hs, hsv⟩ := h
                subst hs hsv
                exact ⟨hwt₁, findStorage_hasTy hwt₁.storage hty₁ hfind⟩
    · simp only [bind, Except.bind] at h
      cases hrm : readM s rhs with
      | error e => rw [hrm] at h; exact nomatch h
      | ok out =>
          obtain ⟨s₁, mv⟩ := out
          rw [hrm] at h
          try dsimp only at h
          obtain ⟨hwt₁, hmty⟩ := readM_wt rhs hwt hrhs hrm
          cases hcm : copyMem s₁ mv with
          | error e => rw [hcm] at h; exact nomatch h
          | ok sval =>
              rw [hcm] at h
              try dsimp only at h
              simp only [Except.ok.injEq, Prod.mk.injEq] at h
              obtain ⟨hs, hsv⟩ := h
              subst hs hsv
              exact ⟨hwt₁, copyMem_hasTy hwt₁.heap hmty hcm⟩
    · exact nomatch h

/-- `rhsToMVal` produces a slot value of the rhs annotation; the
storage→memory copy arm allocates, so the store typing may extend. -/
theorem rhsToMVal_wt {Γ : Ctx} {H : HeapTy} {L : Layout} {s s' : State}
    {rhs : WrappedExpr} {mv : MVal}
    (hwt : StateWT Γ H L s) (hrhs : wtExpr Γ L rhs = true)
    (h : rhsToMVal s rhs = Except.ok (s', mv)) :
    ∃ H', H.Extends H' ∧ StateWT Γ H' L s' ∧
      MVal.hasTyH H' mv rhs.ty = true := by
  rw [rhsToMVal] at h
  try dsimp only at h
  split at h
  · simp only [bind, Except.bind] at h
    cases hv : evalValue s rhs with
    | error e => rw [hv] at h; exact nomatch h
    | ok out =>
        obtain ⟨s₁, v⟩ := out
        rw [hv] at h
        try dsimp only at h
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨hs, hmv⟩ := h
        subst hs hmv
        obtain ⟨hwt₁, hvty⟩ := evalValue_wt rhs hwt hrhs hv
        exact ⟨H, HeapTy.Extends.refl H, hwt₁, Value.toMVal_hasTyH hvty⟩
  · split at h
    · obtain ⟨hwt₁, hmty⟩ := readM_wt rhs hwt hrhs h
      exact ⟨H, HeapTy.Extends.refl H, hwt₁, hmty⟩
    · simp only [bind, Except.bind] at h
      cases hrs : resolveS s rhs with
      | error e => rw [hrs] at h; exact nomatch h
      | ok out =>
          obtain ⟨s₁, root, segs⟩ := out
          rw [hrs] at h
          try dsimp only at h
          obtain ⟨hwt₁, hty₁⟩ := resolveS_wt rhs hwt hrhs hrs
          cases hfind : s₁.findStorage root segs with
          | error e => rw [hfind] at h; exact nomatch h
          | ok sval =>
              rw [hfind] at h
              try dsimp only at h
              have hsty := findStorage_hasTy hwt₁.storage hty₁ hfind
              obtain ⟨H₁, hout, hmty⟩ := copyStToM_typed
                hwt₁.heapTyNodup hwt₁.heap hwt₁.heapWf hsty h
              exact ⟨H₁, hout.ext, hwt₁.ofCopyOut hout, hmty⟩
    · exact nomatch h

/-- Nested (field/index/push) assignment preserves the invariant. -/
theorem execAssignNested_sound {Γ : Ctx} {H : HeapTy} {L : Layout}
    {s s' : State} {lhsExpr rhs : WrappedExpr}
    (hwt : StateWT Γ H L s)
    (hlhs : wtExpr Γ L lhsExpr = true)
    (hrhs : wtExpr Γ L rhs = true)
    (hty : lhsExpr.ty = rhs.ty)
    (hexec : execAssignNested s lhsExpr rhs = Except.ok s') :
    ∃ H', H.Extends H' ∧ StateWT Γ H' L s' := by
  rw [execAssignNested] at hexec
  try dsimp only at hexec
  split at hexec
  · -- storage target
    try simp only [bind, Except.bind] at hexec
    cases hsv : rhsToSVal s rhs with
    | error e => rw [hsv] at hexec; exact nomatch hexec
    | ok out =>
        obtain ⟨s₁, sv⟩ := out
        rw [hsv] at hexec
        try dsimp only at hexec
        obtain ⟨hwt₁, hsvty⟩ := rhsToSVal_wt hwt hrhs hsv
        cases hloc : resolveLoc s₁ lhsExpr with
        | error e => rw [hloc] at hexec; exact nomatch hexec
        | ok out₂ =>
            obtain ⟨s₂, loc⟩ := out₂
            rw [hloc] at hexec
            try dsimp only at hexec
            obtain ⟨hwt₂, hlocty⟩ := resolveLoc_wt lhsExpr hwt₁
              hlhs hloc
            cases loc with
            | storage root segs =>
                refine ⟨H, HeapTy.Extends.refl H,
                  hwt₂.ofSaveStorage hlocty ?_ hexec⟩
                rw [hty]
                exact hsvty
            | stack n => exact nomatch hexec
            | storageLocal n => exact nomatch hexec
            | memoryRoot n => exact nomatch hexec
            | memoryField id fld => exact nomatch hexec
            | memoryIndex id i => exact nomatch hexec
  · -- memory target
    try simp only [bind, Except.bind] at hexec
    cases hmv : rhsToMVal s rhs with
    | error e => rw [hmv] at hexec; exact nomatch hexec
    | ok out =>
        obtain ⟨s₁, mv⟩ := out
        rw [hmv] at hexec
        try dsimp only at hexec
        obtain ⟨H₁, hext, hwt₁, hmty⟩ := rhsToMVal_wt hwt hrhs hmv
        cases hloc : resolveLoc s₁ lhsExpr with
        | error e => rw [hloc] at hexec; exact nomatch hexec
        | ok out₂ =>
            obtain ⟨s₂, loc⟩ := out₂
            rw [hloc] at hexec
            try dsimp only at hexec
            obtain ⟨hwt₂, hlocty⟩ := resolveLoc_wt lhsExpr hwt₁
              hlhs hloc
            cases loc with
            | stack n => exact nomatch hexec
            | storageLocal n => exact nomatch hexec
            | memoryRoot n => exact nomatch hexec
            | storage root segs => exact nomatch hexec
            | memoryField id fld =>
                obtain ⟨str, hclaim, hdef⟩ := hlocty
                simp only [State.getObj, bind, Except.bind] at hexec
                cases hlook : lookupBy id s₂.heap with
                | none => rw [hlook] at hexec; exact nomatch hexec
                | some obj =>
                    rw [hlook] at hexec
                    try dsimp only at hexec
                    cases obj with
                    | array elems => exact nomatch hexec
                    | struct fields =>
                        cases Except.ok.inj hexec
                        exact ⟨H₁, hext,
                          setObjField_wt hwt₂ hclaim hdef
                            (by rw [<- hty] at hmty; exact hmty)
                            hlook⟩
            | memoryIndex id i =>
                simp only [State.getObj, bind, Except.bind] at hexec
                cases hlook : lookupBy id s₂.heap with
                | none => rw [hlook] at hexec; exact nomatch hexec
                | some obj =>
                    rw [hlook] at hexec
                    try dsimp only at hexec
                    cases obj with
                    | struct fields => exact nomatch hexec
                    | array elems =>
                        try dsimp only at hexec
                        split at hexec
                        · cases Except.ok.inj hexec
                          exact ⟨H₁, hext,
                            setObjIndex_wt hwt₂ hlocty
                              (by rw [<- hty] at hmty; exact hmty)
                              hlook⟩
                        · exact nomatch hexec
  · exact nomatch hexec

/-- `execAssign` preserves the invariant when both sides are
well-annotated and agree in type. -/
theorem execAssign_sound {Γ : Ctx} {H : HeapTy} {L : Layout}
    {s s' : State} {lhs : PlaceExpr} {rhs : WrappedExpr}
    (hwt : StateWT Γ H L s)
    (hlhs : wtExpr Γ L lhs.expr = true)
    (hrhs : wtExpr Γ L rhs = true)
    (hty : lhs.expr.ty = rhs.ty)
    (hexec : execAssign s lhs rhs = Except.ok s') :
    ∃ H', H.Extends H' ∧ StateWT Γ H' L s' := by
  obtain ⟨lexpr, hassign⟩ := lhs
  rw [execAssign] at hexec
  try dsimp only at hexec
  cases lexpr with
  | var kind ty fld =>
      cases kind with
      | stack =>
          simp only [wtExpr, beq_iff_eq] at hlhs
          try simp only [bind, Except.bind] at hexec
          cases hv : evalValue s rhs with
          | error e => rw [hv] at hexec; exact nomatch hexec
          | ok out =>
              obtain ⟨s₁, v⟩ := out
              rw [hv] at hexec
              try dsimp only at hexec
              obtain ⟨hwt₁, hvty⟩ := evalValue_wt rhs hwt hrhs hv
              cases Except.ok.inj hexec
              refine ⟨H, HeapTy.Extends.refl H,
                hwt₁.withEnv (envTypedB_setEnv hwt₁.ctxNodup hwt₁.env
                  hlhs ?_)⟩
              show ((Value.toSVal v).hasTy ty) = true
              rw [show ty = rhs.ty from hty]
              exact hvty
      | storage =>
          try dsimp only at hexec
          simp only [wtExpr] at hlhs
          cases hΓ : lookupBy fld.name Γ with
          | none =>
              rw [hΓ] at hlhs
              simp only [Bool.and_eq_true, beq_iff_eq] at hlhs
              rw [if_pos hlhs.1] at hexec
              try simp only [bind, Except.bind] at hexec
              cases hsv : rhsToSVal s rhs with
              | error e => rw [hsv] at hexec; exact nomatch hexec
              | ok out =>
                  obtain ⟨s₁, sv⟩ := out
                  rw [hsv] at hexec
                  try dsimp only at hexec
                  obtain ⟨hwt₁, hsvty⟩ := rhsToSVal_wt hwt hrhs hsv
                  refine ⟨H, HeapTy.Extends.refl H,
                    hwt₁.ofSaveStorage (ty' := ty) ?_ ?_ hexec⟩
                  · simp [Layout.tyAt, hlhs.2, tyAtSegs]
                  · rw [show ty = rhs.ty from hty]
                    exact hsvty
          | some bty =>
              rw [hΓ] at hlhs
              cases bty with
              | stack ty' => exact Bool.noConfusion hlhs
              | mem ty' => exact Bool.noConfusion hlhs
              | path ty' =>
                  simp only [Bool.and_eq_true, beq_iff_eq] at hlhs
                  rw [if_neg (by simp [hlhs.2])] at hexec
                  try simp only [bind, Except.bind] at hexec
                  cases hrs : resolveS s rhs with
                  | error e => rw [hrs] at hexec; exact nomatch hexec
                  | ok out =>
                      obtain ⟨s₁, root, segs⟩ := out
                      rw [hrs] at hexec
                      try dsimp only at hexec
                      obtain ⟨hwt₁, hty₁⟩ := resolveS_wt rhs hwt hrhs hrs
                      cases Except.ok.inj hexec
                      refine ⟨H, HeapTy.Extends.refl H,
                        hwt₁.withEnv (envTypedB_setEnv hwt₁.ctxNodup
                          hwt₁.env hΓ ?_)⟩
                      show (L.tyAt root segs == some ty') = true
                      rw [hty₁, show rhs.ty = ty from hty.symm, hlhs.1]
                      exact beq_self_eq_true _
      | memory =>
          try dsimp only at hexec
          simp only [wtExpr, beq_iff_eq] at hlhs
          split at hexec
          · simp only [bind, Except.bind] at hexec
            cases hrm : readM s rhs with
            | error e => rw [hrm] at hexec; exact nomatch hexec
            | ok out =>
                obtain ⟨s₁, mv⟩ := out
                rw [hrm] at hexec
                try dsimp only at hexec
                obtain ⟨hwt₁, hmty⟩ := readM_wt rhs hwt hrhs hrm
                cases mv with
                | prim p => exact nomatch hexec
                | ref rid =>
                    cases Except.ok.inj hexec
                    refine ⟨H, HeapTy.Extends.refl H,
                      hwt₁.withEnv (envTypedB_setEnv hwt₁.ctxNodup
                        hwt₁.env hlhs ?_)⟩
                    show MVal.hasTyH H (MVal.ref rid) ty = true
                    rw [show ty = rhs.ty from hty]
                    exact hmty
          · simp only [bind, Except.bind] at hexec
            cases hrs : resolveS s rhs with
            | error e => rw [hrs] at hexec; exact nomatch hexec
            | ok out =>
                obtain ⟨s₁, root, segs⟩ := out
                rw [hrs] at hexec
                try dsimp only at hexec
                obtain ⟨hwt₁, hty₁⟩ := resolveS_wt rhs hwt hrhs hrs
                cases hfind : s₁.findStorage root segs with
                | error e => rw [hfind] at hexec; exact nomatch hexec
                | ok sval =>
                    rw [hfind] at hexec
                    try dsimp only at hexec
                    have hsty := findStorage_hasTy hwt₁.storage hty₁
                      hfind
                    cases hcp : copyStToM s₁ sval with
                    | error e => rw [hcp] at hexec; exact nomatch hexec
                    | ok out₂ =>
                        obtain ⟨s₂, mv⟩ := out₂
                        rw [hcp] at hexec
                        try dsimp only at hexec
                        obtain ⟨H₁, hout, hmty⟩ := copyStToM_typed
                          hwt₁.heapTyNodup hwt₁.heap hwt₁.heapWf
                          hsty hcp
                        cases mv with
                        | prim p => exact nomatch hexec
                        | ref rid =>
                            cases Except.ok.inj hexec
                            have hwt₂ := hwt₁.ofCopyOut hout
                            refine ⟨H₁, hout.ext,
                              hwt₂.withEnv (envTypedB_setEnv
                                hwt₂.ctxNodup hwt₂.env hlhs ?_)⟩
                            show MVal.hasTyH H₁ (MVal.ref rid) ty = true
                            rw [show ty = rhs.ty from hty]
                            exact hmty
          · exact nomatch hexec
  | field fkind fty base ffld =>
      exact execAssignNested_sound hwt hlhs hrhs hty hexec
  | index ikind ity base index =>
      exact execAssignNested_sound hwt hlhs hrhs hty hexec
  | pushPlace target =>
      exact execAssignNested_sound hwt hlhs hrhs hty hexec
  | bool b => exact Bool.noConfusion hassign
  | intLit t v => exact Bool.noConfusion hassign
  | mkCall k t n args => exact Bool.noConfusion hassign
  | mkBinop op l r => exact Bool.noConfusion hassign
  | mkUnop op a => exact Bool.noConfusion hassign
  | mkIncDec op t => exact Bool.noConfusion hassign
  | mkTernary c t e => exact Bool.noConfusion hassign

/-! ## The statement checker -/

mutual

/-- Context-threading statement checker: `some Γ'` = well-typed,
yielding the extended context. -/
def stmtWt (Γ : Ctx) (L : Layout) : Stmt -> Option Ctx
  | Stmt.expr e => if wtExpr Γ L e then some Γ else none
  | Stmt.assign lhs rhs =>
      if wtExpr Γ L lhs.expr && wtExpr Γ L rhs &&
          (lhs.expr.ty == rhs.ty) then some Γ else none
  | Stmt.storageDecl ty name init =>
      match init with
      | none => some Γ
      | some rhs =>
          if wtExpr Γ L rhs && (rhs.ty == ty) then
            some (setBy name (BTy.path ty) Γ) else none
  | Stmt.storagePlaceAlias ty name init =>
      if wtExpr Γ L init && (init.ty == ty) then
        some (setBy name (BTy.path ty) Γ) else none
  | Stmt.memoryDecl ty name init =>
      match init with
      | none =>
          if defaultOk ty then some (setBy name (BTy.mem ty) Γ)
          else none
      | some rhs =>
          if wtExpr Γ L rhs && (rhs.ty == ty) then
            some (setBy name (BTy.mem ty) Γ) else none
  | Stmt.stackDecl ty name init =>
      match init with
      | none =>
          if ty.isPrimitive then some (setBy name (BTy.stack ty) Γ)
          else none
      | some rhs =>
          if wtExpr Γ L rhs && (rhs.ty == ty) then
            some (setBy name (BTy.stack ty) Γ) else none
  | Stmt.delete target =>
      -- v1: storage deletes only. Memory `delete` writes fresh
      -- defaults through a local `writeM`; wiring its var/nested
      -- shapes through `allocDefault_typed`/`setObj*_wt` is routine
      -- but bulky, so it is left to a follow-up.
      if wtExpr Γ L target.expr && (target.expr.kind == Kind.storage)
      then some Γ else none
  | Stmt.push target value =>
      match value with
      | none =>
          if wtExpr Γ L target.expr &&
              (match target.expr.ty with
               | Ty.ref (RefTy.array elem) => defaultOk elem
               | _ => false) then some Γ else none
      | some rhs =>
          if wtExpr Γ L target.expr && wtExpr Γ L rhs &&
              (elemTy target.expr.ty == some rhs.ty) then some Γ
          else none
  | Stmt.pushAssign target value =>
      if wtExpr Γ L (PlaceExpr.pushPlace target).expr &&
          wtExpr Γ L value &&
          ((PlaceExpr.pushPlace target).expr.ty == value.ty) then some Γ
      else none
  | Stmt.pushFieldAssign target fld value =>
      if wtExpr Γ L (PlaceExpr.field Kind.storage fld.ty
            (WrappedExpr.pushPlace target) fld).expr &&
          wtExpr Γ L value && (fld.ty == value.ty) then some Γ
      else none
  | Stmt.pop target => if wtExpr Γ L target.expr then some Γ else none
  | Stmt.revert _ => some Γ
  | Stmt.compoundAssign op lhs rhs =>
      if op.isArith && wtExpr Γ L lhs.expr && wtExpr Γ L rhs then
        some Γ else none
  | Stmt.ite cond thn els =>
      if wtExpr Γ L cond then
        match blockWt Γ L thn, blockWt Γ L els with
        | some Γt, some Γe =>
            -- v1: branches may not (net) declare — the interpreter has
            -- no scoping, so a branch-declared binding would leak past
            -- the join with a context the other branch lacks.
            if Γt = Γ ∧ Γe = Γ then some Γ else none
        | _, _ => none
      else none
  | Stmt.assertStmt c => if wtExpr Γ L c then some Γ else none
  | Stmt.requireStmt c => if wtExpr Γ L c then some Γ else none
  | Stmt.transfer r a =>
      if wtExpr Γ L r && wtExpr Γ L a then some Γ else none
  | Stmt.callStmt _ _ _ => none

def blockWt (Γ : Ctx) (L : Layout) : List Stmt -> Option Ctx
  | [] => some Γ
  | stmt :: rest =>
      match stmtWt Γ L stmt with
      | some Γ₁ => blockWt Γ₁ L rest
      | none => none

end

/-! ## The headline: execution preserves the invariant -/

mutual

/-- **Type soundness, statement level**: executing a `stmtWt`-checked
statement from a well-typed state lands in a well-typed state under the
extended context (and a possibly extended store typing — the
storage→memory copies and fresh memory allocations add claims). The
`wellFormed(storage)` reading is the `storage` projection:
well-typedness of storage is an inductive invariant of execution. -/
theorem execStmt_sound {Γ Γ' : Ctx} {H : HeapTy} {L : Layout}
    {s s' : State} (stmt : Stmt)
    (hwt : StateWT Γ H L s) (hstmt : stmtWt Γ L stmt = some Γ')
    (hexec : execStmt s stmt = Except.ok s') :
    ∃ H', H.Extends H' ∧ StateWT Γ' H' L s' := by
  cases stmt with
  | expr e =>
      simp only [stmtWt] at hstmt
      split at hstmt
      case isFalse => exact nomatch hstmt
      case isTrue hexpr =>
      cases Option.some.inj hstmt
      rw [execStmt.eq_def] at hexec
      try dsimp only at hexec
      try simp only [bind, Except.bind] at hexec
      cases hv : evalValue s e with
      | error err => rw [hv] at hexec; exact nomatch hexec
      | ok out =>
          obtain ⟨s₁, v⟩ := out
          rw [hv] at hexec
          try dsimp only at hexec
          cases Except.ok.inj hexec
          exact ⟨H, HeapTy.Extends.refl H,
            (evalValue_wt e hwt hexpr hv).1⟩
  | assign lhs rhs =>
      simp only [stmtWt] at hstmt
      split at hstmt
      case isFalse => exact nomatch hstmt
      case isTrue hcond =>
      cases Option.some.inj hstmt
      simp only [Bool.and_eq_true, beq_iff_eq] at hcond
      rw [execStmt.eq_def] at hexec
      try dsimp only at hexec
      exact execAssign_sound hwt hcond.1.1 hcond.1.2 hcond.2 hexec
  | storageDecl ty name init =>
      rw [execStmt.eq_def] at hexec
      try dsimp only at hexec
      cases init with
      | none =>
          simp only [stmtWt] at hstmt
          cases Option.some.inj hstmt
          cases Except.ok.inj hexec
          exact ⟨H, HeapTy.Extends.refl H, hwt⟩
      | some rhs =>
          simp only [stmtWt] at hstmt
          split at hstmt
          case isFalse => exact nomatch hstmt
          case isTrue hcond =>
          cases Option.some.inj hstmt
          simp only [Bool.and_eq_true, beq_iff_eq] at hcond
          try simp only [bind, Except.bind] at hexec
          cases hrs : resolveS s rhs with
          | error e => rw [hrs] at hexec; exact nomatch hexec
          | ok out =>
              obtain ⟨s₁, root, segs⟩ := out
              rw [hrs] at hexec
              try dsimp only at hexec
              obtain ⟨hwt₁, hty₁⟩ := resolveS_wt rhs hwt hcond.1 hrs
              cases Except.ok.inj hexec
              refine ⟨H, HeapTy.Extends.refl H, hwt₁.extendCtx ?_⟩
              show (L.tyAt root segs == some ty) = true
              rw [hty₁, hcond.2]
              exact beq_self_eq_true _
  | storagePlaceAlias ty name init =>
      simp only [stmtWt] at hstmt
      split at hstmt
      case isFalse => exact nomatch hstmt
      case isTrue hcond =>
      cases Option.some.inj hstmt
      simp only [Bool.and_eq_true, beq_iff_eq] at hcond
      rw [execStmt.eq_def] at hexec
      try dsimp only at hexec
      try simp only [bind, Except.bind] at hexec
      cases hrs : resolveS s init with
      | error e => rw [hrs] at hexec; exact nomatch hexec
      | ok out =>
          obtain ⟨s₁, root, segs⟩ := out
          rw [hrs] at hexec
          try dsimp only at hexec
          obtain ⟨hwt₁, hty₁⟩ := resolveS_wt init hwt hcond.1 hrs
          cases Except.ok.inj hexec
          refine ⟨H, HeapTy.Extends.refl H, hwt₁.extendCtx ?_⟩
          show (L.tyAt root segs == some ty) = true
          rw [hty₁, hcond.2]
          exact beq_self_eq_true _
  | memoryDecl ty name init =>
      rw [execStmt.eq_def] at hexec
      try dsimp only at hexec
      cases init with
      | none =>
          simp only [stmtWt] at hstmt
          split at hstmt
          case isFalse => exact nomatch hstmt
          case isTrue hok =>
          cases Option.some.inj hstmt
          cases ty with
          | prim pt => exact nomatch hexec
          | ref ref =>
              try simp only [bind, Except.bind] at hexec
              cases hal : allocDefault s ref with
              | error e => rw [hal] at hexec; exact nomatch hexec
              | ok out =>
                  obtain ⟨s₁, id⟩ := out
                  rw [hal] at hexec
                  try dsimp only at hexec
                  obtain ⟨H₁, hout, hmty⟩ := allocDefault_typed
                    hwt.heapTyNodup hwt.heap hwt.heapWf hok hal
                  cases Except.ok.inj hexec
                  exact ⟨H₁, hout.ext,
                    (hwt.ofCopyOut hout).extendCtx hmty⟩
      | some rhs =>
          simp only [stmtWt] at hstmt
          split at hstmt
          case isFalse => exact nomatch hstmt
          case isTrue hcond =>
          cases Option.some.inj hstmt
          simp only [Bool.and_eq_true, beq_iff_eq] at hcond
          try dsimp only at hexec
          split at hexec
          · -- memory alias
            try simp only [bind, Except.bind] at hexec
            cases hrm : readM s rhs with
            | error e => rw [hrm] at hexec; exact nomatch hexec
            | ok out =>
                obtain ⟨s₁, mv⟩ := out
                rw [hrm] at hexec
                try dsimp only at hexec
                obtain ⟨hwt₁, hmty⟩ := readM_wt rhs hwt hcond.1 hrm
                cases mv with
                | prim p => exact nomatch hexec
                | ref rid =>
                    cases Except.ok.inj hexec
                    refine ⟨H, HeapTy.Extends.refl H,
                      hwt₁.extendCtx ?_⟩
                    show MVal.hasTyH H (MVal.ref rid) ty = true
                    rw [<- hcond.2]
                    exact hmty
          · -- storage deep copy
            try simp only [bind, Except.bind] at hexec
            cases hrs : resolveS s rhs with
            | error e => rw [hrs] at hexec; exact nomatch hexec
            | ok out =>
                obtain ⟨s₁, root, segs⟩ := out
                rw [hrs] at hexec
                try dsimp only at hexec
                obtain ⟨hwt₁, hty₁⟩ := resolveS_wt rhs hwt hcond.1 hrs
                cases hfind : s₁.findStorage root segs with
                | error e => rw [hfind] at hexec; exact nomatch hexec
                | ok sval =>
                    rw [hfind] at hexec
                    try dsimp only at hexec
                    have hsty := findStorage_hasTy hwt₁.storage hty₁
                      hfind
                    cases hcp : copyStToM s₁ sval with
                    | error e => rw [hcp] at hexec; exact nomatch hexec
                    | ok out₂ =>
                        obtain ⟨s₂, mv⟩ := out₂
                        rw [hcp] at hexec
                        try dsimp only at hexec
                        obtain ⟨H₁, hout, hmty⟩ := copyStToM_typed
                          hwt₁.heapTyNodup hwt₁.heap hwt₁.heapWf
                          hsty hcp
                        cases mv with
                        | prim p => exact nomatch hexec
                        | ref rid =>
                            cases Except.ok.inj hexec
                            refine ⟨H₁, hout.ext,
                              (hwt₁.ofCopyOut hout).extendCtx ?_⟩
                            show MVal.hasTyH H₁ (MVal.ref rid) ty = true
                            rw [<- hcond.2]
                            exact hmty
          · exact nomatch hexec
  | stackDecl ty name init =>
      rw [execStmt.eq_def] at hexec
      try dsimp only at hexec
      cases init with
      | none =>
          simp only [stmtWt] at hstmt
          split at hstmt
          case isFalse => exact nomatch hstmt
          case isTrue hprim =>
          cases Option.some.inj hstmt
          cases ty with
          | ref r => exact Bool.noConfusion hprim
          | prim pt =>
              cases pt with
              | bool =>
                  cases Except.ok.inj hexec
                  exact ⟨H, HeapTy.Extends.refl H, hwt.extendCtx rfl⟩
              | uint =>
                  cases Except.ok.inj hexec
                  exact ⟨H, HeapTy.Extends.refl H, hwt.extendCtx rfl⟩
              | int =>
                  cases Except.ok.inj hexec
                  exact ⟨H, HeapTy.Extends.refl H, hwt.extendCtx rfl⟩
      | some rhs =>
          simp only [stmtWt] at hstmt
          split at hstmt
          case isFalse => exact nomatch hstmt
          case isTrue hcond =>
          cases Option.some.inj hstmt
          simp only [Bool.and_eq_true, beq_iff_eq] at hcond
          try simp only [bind, Except.bind] at hexec
          cases hv : evalValue s rhs with
          | error e => rw [hv] at hexec; exact nomatch hexec
          | ok out =>
              obtain ⟨s₁, v⟩ := out
              rw [hv] at hexec
              try dsimp only at hexec
              obtain ⟨hwt₁, hvty⟩ := evalValue_wt rhs hwt hcond.1 hv
              cases Except.ok.inj hexec
              refine ⟨H, HeapTy.Extends.refl H, hwt₁.extendCtx ?_⟩
              show ((Value.toSVal v).hasTy ty) = true
              rw [<- hcond.2]
              exact hvty
  | «delete» target =>
      simp only [stmtWt] at hstmt
      split at hstmt
      case isFalse => exact nomatch hstmt
      case isTrue hcond =>
      cases Option.some.inj hstmt
      simp only [Bool.and_eq_true, beq_iff_eq] at hcond
      obtain ⟨hexpr, hkind⟩ := hcond
      rw [execStmt.eq_def] at hexec
      try dsimp only at hexec
      split at hexec
      · -- storage delete
        try simp only [bind, Except.bind] at hexec
        cases hrs : resolveS s target.expr with
        | error e => rw [hrs] at hexec; exact nomatch hexec
        | ok out =>
            obtain ⟨s₁, root, segs⟩ := out
            rw [hrs] at hexec
            try dsimp only at hexec
            obtain ⟨hwt₁, hty₁⟩ := resolveS_wt target.expr hwt hexpr hrs
            cases hfind : s₁.findStorage root segs with
            | error e => rw [hfind] at hexec; exact nomatch hexec
            | ok current =>
                rw [hfind] at hexec
                try dsimp only at hexec
                have hcty := findStorage_hasTy hwt₁.storage hty₁ hfind
                exact ⟨H, HeapTy.Extends.refl H,
                  hwt₁.ofSaveStorage hty₁ (SVal.defaultOf_hasTy hcty)
                    hexec⟩
      · -- memory delete: outside the v1 fragment.
        first
        | (rename_i hkindeq
           rw [hkindeq] at hkind
           exact Kind.noConfusion hkind)
        | simp_all
      · first
        | (rename_i hkindeq
           rw [hkindeq] at hkind
           exact Kind.noConfusion hkind)
        | simp_all
  | push target value =>
      rw [execStmt.eq_def] at hexec
      try dsimp only at hexec
      try simp only [bind, Except.bind] at hexec
      cases hrs : resolveS s target.expr with
      | error e => rw [hrs] at hexec; exact nomatch hexec
      | ok out =>
          obtain ⟨s₁, root, segs⟩ := out
          rw [hrs] at hexec
          try dsimp only at hexec
          cases value with
          | none =>
              simp only [stmtWt] at hstmt
              split at hstmt
              case h_2 => simp at hstmt
              case h_1 elem₀ hty' =>
              split at hstmt
              case isFalse => exact nomatch hstmt
              case isTrue hcond =>
              cases Option.some.inj hstmt
              simp only [Bool.and_eq_true] at hcond
              obtain ⟨hwt₁, hty₁⟩ := resolveS_wt target.expr hwt
                hcond.1 hrs
              cases hfind : s₁.findStorage root segs with
              | error e => rw [hfind] at hexec; exact nomatch hexec
              | ok arr =>
                  rw [hfind] at hexec
                  try dsimp only at hexec
                  have harrty := findStorage_hasTy hwt₁.storage hty₁
                    hfind
                  split at hexec
                  case h_2 | h_3 | h_4 | h_5 | h_6 | h_7 => exact nomatch hexec
                  case h_1 elems elemTy₀ htty =>
                    try simp only [bind, Except.bind] at hexec
                    have helem : elem₀ = elemTy₀ := by
                      rw [hty'] at htty
                      exact RefTy.array.inj (Ty.ref.inj htty)
                    subst helem
                    rw [hty'] at harrty hty₁
                    have hok : defaultOk elem₀ = true := hcond.2
                    refine ⟨H, HeapTy.Extends.refl H,
                      hwt₁.ofSaveStorage hty₁ ?_ hexec⟩
                    simp only [SVal.hasTy, Bool.and_eq_true] at harrty ⊢
                    obtain ⟨hslot, hrest⟩ := pushSlot_hasTy harrty.2 hok
                    exact ⟨hasTyElems_append harrty.1
                      (by simpa [SVal.hasTy.hasTyElems] using hslot), hrest⟩
          | some rhs =>
              simp only [stmtWt] at hstmt
              split at hstmt
              case isFalse => exact nomatch hstmt
              case isTrue hcond =>
              cases Option.some.inj hstmt
              simp only [Bool.and_eq_true, beq_iff_eq] at hcond
              obtain ⟨hwt₁, hty₁⟩ := resolveS_wt target.expr hwt
                hcond.1.1 hrs
              cases hfind : s₁.findStorage root segs with
              | error e => rw [hfind] at hexec; exact nomatch hexec
              | ok arr =>
                  rw [hfind] at hexec
                  try dsimp only at hexec
                  have harrty := findStorage_hasTy hwt₁.storage hty₁
                    hfind
                  split at hexec
                  case h_2 | h_3 | h_4 | h_5 | h_6 | h_7 => exact nomatch hexec
                  case h_1 elems elemTy₀ heq =>
                    have htty := heq
                    try simp only [bind, Except.bind] at hexec
                    rw [htty] at hcond harrty hty₁
                    have helem : elemTy₀ = rhs.ty := by
                      have := hcond.2
                      simp only [elemTy] at this
                      simpa using this
                    cases hsv : rhsToSVal s₁ rhs with
                    | error e => rw [hsv] at hexec; exact nomatch hexec
                    | ok out₂ =>
                        obtain ⟨s₂, newElem⟩ := out₂
                        rw [hsv] at hexec
                        try dsimp only at hexec
                        obtain ⟨hwt₂, hsvty⟩ := rhsToSVal_wt hwt₁
                          hcond.1.2 hsv
                        refine ⟨H, HeapTy.Extends.refl H,
                          hwt₂.ofSaveStorage hty₁ ?_ hexec⟩
                        simp only [SVal.hasTy, Bool.and_eq_true] at harrty ⊢
                        refine ⟨hasTyElems_append harrty.1
                          (by
                            rw [helem]
                            simpa [SVal.hasTy.hasTyElems] using hsvty), ?_⟩
                        exact pushSlot_rest_hasTy harrty.2
  | pushAssign target value =>
      simp only [stmtWt] at hstmt
      split at hstmt
      case isFalse => exact nomatch hstmt
      case isTrue hcond =>
      cases Option.some.inj hstmt
      simp only [Bool.and_eq_true, beq_iff_eq] at hcond
      rw [execStmt.eq_def] at hexec
      try dsimp only at hexec
      exact execAssign_sound hwt hcond.1.1 hcond.1.2 hcond.2 hexec
  | pushFieldAssign target fld value =>
      simp only [stmtWt] at hstmt
      split at hstmt
      case isFalse => exact nomatch hstmt
      case isTrue hcond =>
      cases Option.some.inj hstmt
      simp only [Bool.and_eq_true, beq_iff_eq] at hcond
      rw [execStmt.eq_def] at hexec
      try dsimp only at hexec
      exact execAssign_sound hwt hcond.1.1 hcond.1.2 hcond.2 hexec
  | pop target =>
      simp only [stmtWt] at hstmt
      split at hstmt
      case isFalse => exact nomatch hstmt
      case isTrue hexpr =>
      cases Option.some.inj hstmt
      rw [execStmt.eq_def] at hexec
      try dsimp only at hexec
      try simp only [bind, Except.bind] at hexec
      cases hrs : resolveS s target.expr with
      | error e => rw [hrs] at hexec; exact nomatch hexec
      | ok out =>
          obtain ⟨s₁, root, segs⟩ := out
          rw [hrs] at hexec
          try dsimp only at hexec
          obtain ⟨hwt₁, hty₁⟩ := resolveS_wt target.expr hwt hexpr hrs
          cases hfind : s₁.findStorage root segs with
          | error e => rw [hfind] at hexec; exact nomatch hexec
          | ok arr =>
              rw [hfind] at hexec
              try dsimp only at hexec
              have harrty := findStorage_hasTy hwt₁.storage hty₁ hfind
              cases arr with
              | prim p => exact nomatch hexec
              | struct fields => exact nomatch hexec
              | map entries dflt => exact nomatch hexec
              | array elems =>
                  try dsimp only at hexec
                  cases hrev : elems.reverse with
                  | nil => rw [hrev] at hexec; exact nomatch hexec
                  | cons x restRev =>
                      rw [hrev] at hexec
                      try dsimp only at hexec
                      cases hbt : target.expr.ty with
                      | prim pt =>
                          rw [hbt] at harrty
                          try dsimp only at harrty
                          simp [SVal.hasTy] at harrty
                      | ref r =>
                          cases r with
                          | struct str =>
                              rw [hbt] at harrty
                              try dsimp only at harrty
                              simp [SVal.hasTy] at harrty
                          | mapping k v =>
                              rw [hbt] at harrty
                              try dsimp only at harrty
                              simp [SVal.hasTy] at harrty
                          | array elem =>
                              rw [hbt] at harrty hty₁
                              refine ⟨H, HeapTy.Extends.refl H,
                                hwt₁.ofSaveStorage hty₁ ?_ hexec⟩
                              simp only [SVal.hasTy, Bool.and_eq_true] at harrty ⊢
                              refine ⟨hasTyElems_of_forall_mem
                                fun v hv => ?_, ?_⟩
                              · refine hasTyElems_mem harrty.1 ?_
                                have : v ∈ elems.reverse := by
                                  rw [hrev]
                                  exact List.Mem.tail _
                                    (List.mem_reverse.mp hv)
                                exact List.mem_reverse.mp this
                              · simp only [SVal.hasTy.hasTyElems,
                                  Bool.and_eq_true]
                                refine ⟨SVal.defaultOf_hasTy ?_, harrty.2⟩
                                refine hasTyElems_mem harrty.1 ?_
                                have : x ∈ elems.reverse := by
                                  rw [hrev]; exact List.Mem.head _
                                exact List.mem_reverse.mp this
  | «revert» msg => rw [execStmt.eq_def] at hexec; exact nomatch hexec
  | compoundAssign op lhs rhs =>
      simp only [stmtWt] at hstmt
      split at hstmt
      case isFalse => exact nomatch hstmt
      case isTrue hcond =>
      cases Option.some.inj hstmt
      simp only [Bool.and_eq_true] at hcond
      obtain ⟨⟨hop, hlhs⟩, hrhs⟩ := hcond
      rw [execStmt.eq_def] at hexec
      try dsimp only at hexec
      try simp only [bind, Except.bind] at hexec
      cases hv : evalValue s rhs with
      | error e => rw [hv] at hexec; exact nomatch hexec
      | ok out =>
          obtain ⟨s₁, v⟩ := out
          rw [hv] at hexec
          try dsimp only at hexec
          obtain ⟨hwt₁, _⟩ := evalValue_wt rhs hwt hrhs hv
          cases hloc : resolveLoc s₁ lhs.expr with
          | error e => rw [hloc] at hexec; exact nomatch hexec
          | ok out₂ =>
              obtain ⟨s₂, loc⟩ := out₂
              rw [hloc] at hexec
              try dsimp only at hexec
              obtain ⟨hwt₂, hlocty⟩ := resolveLoc_wt lhs.expr hwt₁
                hlhs hloc
              cases hold : readLoc s₂ loc with
              | error e => rw [hold] at hexec; exact nomatch hexec
              | ok old =>
                  rw [hold] at hexec
                  try dsimp only at hexec
                  have holdty := readLoc_wt hwt₂ hlocty hold
                  cases happ : applyBinOp op old v with
                  | error e => rw [happ] at hexec; exact nomatch hexec
                  | ok new₀ =>
                      rw [happ] at hexec
                      try dsimp only at hexec
                      cases hchk : checkArith lhs.expr.ty new₀ with
                      | error e => rw [hchk] at hexec; exact nomatch hexec
                      | ok new₁ =>
                          rw [hchk] at hexec
                          try dsimp only at hexec
                          obtain ⟨n, hn⟩ := applyBinOp_arith_int hop happ
                          obtain ⟨m, hm⟩ := applyBinOp_arith_lhs_int
                            hop happ
                          subst hn hm
                          have hnum : isNumericTy lhs.expr.ty = true :=
                            hasTy_int_numeric holdty
                          have hnew := checkArith_ok_eq hchk
                          refine ⟨H, HeapTy.Extends.refl H,
                            writeLoc_wt hwt₂ hlocty ?_ hexec⟩
                          rw [hnew]
                          exact int_hasTy_numeric hnum n
  | ite cond thn els =>
      simp only [stmtWt] at hstmt
      split at hstmt
      case isFalse => exact nomatch hstmt
      case isTrue hcond =>
      rw [execStmt.eq_def] at hexec
      try dsimp only at hexec
      try simp only [bind, Except.bind] at hexec
      cases hc : evalValue s cond with
      | error e => rw [hc] at hexec; exact nomatch hexec
      | ok out =>
          obtain ⟨s₁, cv⟩ := out
          rw [hc] at hexec
          try dsimp only at hexec
          obtain ⟨hwt₁, _⟩ := evalValue_wt cond hwt hcond hc
          cases hthn : blockWt Γ L thn with
          | none => rw [hthn] at hstmt; exact nomatch hstmt
          | some Γt =>
              rw [hthn] at hstmt
              try dsimp only at hstmt
              cases hels : blockWt Γ L els with
              | none => rw [hels] at hstmt; exact nomatch hstmt
              | some Γe =>
                  rw [hels] at hstmt
                  try dsimp only at hstmt
                  split at hstmt
                  case isFalse => exact nomatch hstmt
                  case isTrue heq =>
                  cases Option.some.inj hstmt
                  cases cv with
                  | int n => exact nomatch hexec
                  | bool b =>
                      cases b with
                      | true =>
                          obtain ⟨H', hext, hwt'⟩ := execBlock_sound thn
                            hwt₁ hthn hexec
                          rw [heq.1] at hwt'
                          exact ⟨H', hext, hwt'⟩
                      | false =>
                          obtain ⟨H', hext, hwt'⟩ := execBlock_sound els
                            hwt₁ hels hexec
                          rw [heq.2] at hwt'
                          exact ⟨H', hext, hwt'⟩
  | assertStmt cond =>
      simp only [stmtWt] at hstmt
      split at hstmt
      case isFalse => exact nomatch hstmt
      case isTrue hexpr =>
      cases Option.some.inj hstmt
      rw [execStmt.eq_def] at hexec
      try dsimp only at hexec
      try simp only [bind, Except.bind] at hexec
      cases hc : evalValue s cond with
      | error e => rw [hc] at hexec; exact nomatch hexec
      | ok out =>
          obtain ⟨s₁, cv⟩ := out
          rw [hc] at hexec
          try dsimp only at hexec
          obtain ⟨hwt₁, _⟩ := evalValue_wt cond hwt hexpr hc
          cases cv with
          | int n => exact nomatch hexec
          | bool b =>
              cases b with
              | true =>
                  cases Except.ok.inj hexec
                  exact ⟨H, HeapTy.Extends.refl H, hwt₁⟩
              | false => exact nomatch hexec
  | requireStmt cond =>
      simp only [stmtWt] at hstmt
      split at hstmt
      case isFalse => exact nomatch hstmt
      case isTrue hexpr =>
      cases Option.some.inj hstmt
      rw [execStmt.eq_def] at hexec
      try dsimp only at hexec
      try simp only [bind, Except.bind] at hexec
      cases hc : evalValue s cond with
      | error e => rw [hc] at hexec; exact nomatch hexec
      | ok out =>
          obtain ⟨s₁, cv⟩ := out
          rw [hc] at hexec
          try dsimp only at hexec
          obtain ⟨hwt₁, _⟩ := evalValue_wt cond hwt hexpr hc
          cases cv with
          | int n => exact nomatch hexec
          | bool b =>
              cases b with
              | true =>
                  cases Except.ok.inj hexec
                  exact ⟨H, HeapTy.Extends.refl H, hwt₁⟩
              | false => exact nomatch hexec
  | transfer recipient amount =>
      simp only [stmtWt] at hstmt
      split at hstmt
      case isFalse => exact nomatch hstmt
      case isTrue hcond =>
      cases Option.some.inj hstmt
      simp only [Bool.and_eq_true] at hcond
      rw [execStmt.eq_def] at hexec
      try dsimp only at hexec
      try simp only [bind, Except.bind] at hexec
      cases hr : evalInt s recipient with
      | error e => rw [hr] at hexec; exact nomatch hexec
      | ok out =>
          obtain ⟨s₁, addr⟩ := out
          rw [hr] at hexec
          try dsimp only at hexec
          obtain ⟨hwt₁, _⟩ := evalInt_wt recipient hwt hcond.1 hr
          cases ha : evalInt s₁ amount with
          | error e => rw [ha] at hexec; exact nomatch hexec
          | ok out₂ =>
              obtain ⟨s₂, amt⟩ := out₂
              rw [ha] at hexec
              try dsimp only at hexec
              obtain ⟨hwt₂, _⟩ := evalInt_wt amount hwt₁ hcond.2 ha
              split at hexec
              · exact nomatch hexec
              · split at hexec
                · exact nomatch hexec
                · cases Except.ok.inj hexec
                  exact ⟨H, HeapTy.Extends.refl H,
                    { hwt₂ with
                      heapWf := fun i hi => hwt₂.heapWf i hi }⟩
  | callStmt res fn args => exact nomatch hstmt

/-- **Type soundness, block level.** -/
theorem execBlock_sound {Γ Γ' : Ctx} {H : HeapTy} {L : Layout}
    {s s' : State} (stmts : List Stmt)
    (hwt : StateWT Γ H L s) (hblock : blockWt Γ L stmts = some Γ')
    (hexec : execBlock s stmts = Except.ok s') :
    ∃ H', H.Extends H' ∧ StateWT Γ' H' L s' := by
  cases stmts with
  | nil =>
      simp only [blockWt] at hblock
      cases Option.some.inj hblock
      rw [execBlock] at hexec
      try dsimp only at hexec
      cases Except.ok.inj hexec
      exact ⟨H, HeapTy.Extends.refl H, hwt⟩
  | cons stmt rest =>
      simp only [blockWt] at hblock
      rw [execBlock] at hexec
      try dsimp only at hexec
      try simp only [bind, Except.bind] at hexec
      cases hs1 : stmtWt Γ L stmt with
      | none => rw [hs1] at hblock; exact nomatch hblock
      | some Γ₁ =>
          rw [hs1] at hblock
          cases he1 : execStmt s stmt with
          | error e => rw [he1] at hexec; exact nomatch hexec
          | ok s₁ =>
              rw [he1] at hexec
              obtain ⟨H₁, hext₁, hwt₁⟩ := execStmt_sound stmt hwt hs1 he1
              obtain ⟨H₂, hext₂, hwt₂⟩ := execBlock_sound rest hwt₁
                hblock hexec
              exact ⟨H₂, hext₁.trans hext₂, hwt₂⟩

end

/-! ## Corollaries: the `wellFormed` reading -/

/-- **The wellfoundedness theorem**: storage well-typedness is an
inductive invariant of execution — assume `wellFormed(storage)` once
in the proof obligation and it holds at every reachable state. This is
what solkey needs to make the `\hasSort`-family sort annotations
*faithful* (not merely sound) claims about every reachable storage. -/
theorem execBlock_preserves_wellTyped {Γ Γ' : Ctx} {H : HeapTy}
    {L : Layout} {s s' : State} {stmts : List Stmt}
    (hwt : StateWT Γ H L s) (hblock : blockWt Γ L stmts = some Γ')
    (hexec : execBlock s stmts = Except.ok s') :
    wellTypedStorageB L s'.storage = true := by
  obtain ⟨H', _, hwt'⟩ := execBlock_sound stmts hwt hblock hexec
  exact hwt'.storage

/-- The user's original case, end to end: after any well-typed
execution from a well-formed state, `find` at an int-declared path
yields an int — no per-state assumption needed beyond the initial
one. -/
theorem run_then_find_int {Γ Γ' : Ctx} {H : HeapTy} {L : Layout}
    {s s' : State} {stmts : List Stmt} {root : Name} {segs : List Seg}
    {ty : Ty} {v : SVal}
    (hwt : StateWT Γ H L s) (hblock : blockWt Γ L stmts = some Γ')
    (hexec : execBlock s stmts = Except.ok s')
    (hpath : L.tyAt root segs = some ty)
    (hnum : isNumericTy ty = true)
    (hfind : s'.findStorage root segs = Except.ok v) :
    ∃ n, v = SVal.int n := by
  have hst := execBlock_preserves_wellTyped hwt hblock hexec
  exact hasTy_numeric hnum (findStorage_hasTy hst hpath hfind)

/-- Every varcond-resolved taclet read stays faithful across
execution: `generic_read_hasTy` composed with preservation. -/
theorem step_then_read_hasTy {Γ Γ' : Ctx} {H : HeapTy} {L : Layout}
    {s s₁ s₂ : State} {stmt : Stmt} {e : WrappedExpr} {root : Name}
    {segs : List Seg} {v : SVal}
    (hwt : StateWT Γ H L s) (hstmt : stmtWt Γ L stmt = some Γ')
    (hexec : execStmt s stmt = Except.ok s₁)
    (hwtexpr : wtStorageExpr L s₁.env e = true)
    (hres : resolveS s₁ e = Except.ok (s₂, root, segs))
    (hfind : s₂.findStorage root segs = Except.ok v) :
    v.hasTy e.ty = true := by
  obtain ⟨H', _, hwt₁⟩ := execStmt_sound stmt hwt hstmt hexec
  exact generic_read_hasTy hwt₁.storage hwtexpr hres hfind

end Semantics
end Solidity
