import Solidity.Source.LibraryTyping

/-! Statement typing and the public Source typing shim. Existing expression
typing is re-exported from ExpressionTyping without changing its statements.
Library try/Error is additive; v1 declaration premises remain frozen. -/
namespace Solidity.Source

/-! ## Statement typing -/

/-- The context of a function body with the given locals. -/
def Ctx.at (C : Ctx) (L : List (String × STy)) : Ctx := { C with locals := L }

/-- An optional loop condition, typed. -/
inductive OptCond (Γ : Ctx) : Syn (.opt .expr) → Type where
  | none : OptCond Γ .none
  | some {e : Syn .expr} : Typed Γ e .bool → OptCond Γ (.some e)

/-! ### Tuple declarations (lane FU2-B) -/

/-- A slot of a tuple declaration: a declared name with its type (solc's
location rule for an initialized declaration), or a hole (`none`). -/
def Ctx.declSlot (C : Ctx) : Syn (.opt .varDecl) → Option (Option (String × STy))
  | .none => Option.some Option.none
  | .some (.varDecl t l x) =>
    match t.ty C.env C.scope (l.getD .memory) with
    | Option.some τ => if locOK τ l true then Option.some (Option.some (x, τ)) else Option.none
    | Option.none => Option.none

/-- The slots of a list of optional declarations. -/
def Ctx.declSlots (C : Ctx) : Syn (.list (.opt .varDecl)) → Option (List (Option (String × STy)))
  | .nil => Option.some []
  | .cons s ss =>
    match C.declSlot s, C.declSlots ss with
    | Option.some a, Option.some b => Option.some (a :: b)
    | _, _ => Option.none

/-- The slots of `(, , T x, …) = e`: the leading holes, the first
declaration, the remaining slots. -/
def Ctx.tupleSlots (C : Ctx) (holes : Nat) (d : Syn .varDecl) (ds : Syn (.list (.opt .varDecl))) :
    Option (List (Option (String × STy))) :=
  match C.declSlot (.some d), C.declSlots ds with
  | Option.some a, Option.some b => Option.some (List.replicate holes Option.none ++ a :: b)
  | _, _ => Option.none

/-- **The success clause's locals of a `try`** (lane FU2-B): the
function's return types, named by the `returns` parameters (`""` when
unnamed), left to right. -/
def tryLocals : List (Option String) → List STy → List (String × STy)
  | n :: ns, τ :: τs => (n.getD "", τ) :: tryLocals ns τs
  | [], τ :: τs => ("", τ) :: tryLocals [] τs
  | _, [] => []

theorem tryLocals_tys : (ns : List (Option String)) → (rs : List STy) → (tryLocals ns rs).map Prod.snd = rs
  | _ :: ns, _ :: τs => by simp only [tryLocals, List.map_cons, tryLocals_tys ns τs]
  | [], _ :: τs => by simp only [tryLocals, List.map_cons, tryLocals_tys [] τs]
  | _ :: _, [] => rfl
  | [], [] => rfl

/-- **A `catch` clause the source semantics runs** (lane FU2-B), with the
name it binds and its block: `catch { … }` (no binding) or
`catch (bytes memory r) { … }` (the revert data); `Error(string)` and
`Panic(uint)` clauses are not modelled. -/
inductive CatchD {k : SCtx} : Syn (.catchClause k) → Option String → Syn (.list (.item k)) → Prop where
  | plain (b : Syn (.list (.item k))) : CatchD (.catchPlain (.block b)) Option.none b
  | bytes (x : Option String) (b : Syn (.list (.item k))) :
      CatchD (.catchSig Option.none (.param (.elem .bytes) (Option.some .memory) x) .nil (.block b))
        (Option.some (x.getD "")) b

/-- A `catch` clause's locals: the revert data's, if bound. -/
def catchLocals : Option String → List (String × STy) → List (String × STy)
  | Option.none, L => L
  | Option.some x, L => (x, .bytes .memory) :: L

/-- A `catch` clause's local types. -/
def catchCtx : Bool → List STy → List STy
  | true, Γ => .bytes .memory :: Γ
  | false, Γ => Γ

theorem catchLocals_tys (x : Option String) (L : List (String × STy)) :
    (catchLocals x L).map Prod.snd = catchCtx x.isSome (L.map Prod.snd) := by
  cases x <;> rfl

/-- The locals a tuple declaration adds onto `L`, left to right (the last
declared innermost). -/
def pushSlots : List (Option (String × STy)) → List (String × STy) → List (String × STy)
  | [], L => L
  | Option.none :: ss, L => pushSlots ss L
  | Option.some p :: ss, L => pushSlots ss (p :: L)

/-- The types a tuple declaration adds onto a context of types. -/
def pushTys : List (Option STy) → List STy → List STy
  | [], Γ => Γ
  | Option.none :: ss, Γ => pushTys ss Γ
  | Option.some τ :: ss, Γ => pushTys ss (τ :: Γ)

theorem pushSlots_tys : ∀ (slots : List (Option (String × STy))) (L : List (String × STy)),
    (pushSlots slots L).map Prod.snd = pushTys (slots.map (Option.map Prod.snd)) (L.map Prod.snd)
  | [], _ => rfl
  | Option.none :: ss, L => pushSlots_tys ss L
  | Option.some p :: ss, L => pushSlots_tys ss (p :: L)

theorem pushSlots_suffix : ∀ (slots : List (Option (String × STy))) (L : List (String × STy)),
    ∃ ys, pushSlots slots L = ys ++ L
  | [], _ => ⟨[], rfl⟩
  | Option.none :: ss, L => pushSlots_suffix ss L
  | Option.some p :: ss, L => by
    obtain ⟨ys, h⟩ := pushSlots_suffix ss (p :: L)
    exact ⟨ys ++ [p], by simp only [pushSlots, h, List.append_assoc, List.singleton_append]⟩

theorem pushTys_suffix : ∀ (slots : List (Option STy)) (Γ : List STy), ∃ ys, pushTys slots Γ = ys ++ Γ
  | [], _ => ⟨[], rfl⟩
  | Option.none :: ss, Γ => pushTys_suffix ss Γ
  | Option.some τ :: ss, Γ => by
    obtain ⟨ys, h⟩ := pushTys_suffix ss (τ :: Γ)
    exact ⟨ys ++ [τ], by simp only [pushTys, h, List.append_assoc, List.singleton_append]⟩

/-- A component that is not the empty tuple `()`: solc refuses
`(, uint a) = (g(), 1)` for a `g` without returns ("Tuple component
cannot be empty"), holes included. -/
def STy.nonEmpty : STy → Bool
  | .tuple [] => false
  | _ => true

/-- **Each declared slot's component converts implicitly** to its type;
a hole takes any non-empty component; the slots are as many as the
components. -/
def slotsFit (B : DeclName → DeclName → Bool) (M : DeclName → Bool) : List (Option STy) → List STy → Bool
  | [], [] => true
  | Option.none :: ss, σ :: σs => σ.nonEmpty && slotsFit B M ss σs
  | Option.some τ :: ss, σ :: σs => σ.implicit B M τ && slotsFit B M ss σs
  | _, _ => false

/-- An optional loop step, typed at some type. -/
inductive OptExpr (Γ : Ctx) : Syn (.opt .expr) → Type where
  | none : OptExpr Γ .none
  | some {e : Syn .expr} {τ : STy} : Typed Γ e τ → OptExpr Γ (.some e)

mutual

/-- **Statement typing**, as data, in a function body `C` (its environment,
contract, return types, `msg.value` and modifier flags, which no statement
changes): `s` is well typed with locals `L` and leaves locals `L'` (a
declaration adds one; a block's locals end with it). -/
inductive StmtD (C : Ctx) : {k : SCtx} → List (String × STy) → Syn (.stmt k) → List (String × STy) → Type where
  /-- An expression statement; in a modifier, `_;` is the placeholder, not an
  expression. -/
  | expr {k : SCtx} {L : List (String × STy)} {e : Syn .expr} {τ : STy} :
      Typed (C.at L) e τ → (C.inModifier && e.isUnderscore) = false →
      StmtD C (k := k) L (.simpleStmt (.exprStmt e)) L
  /-- `_;` in a modifier body. -/
  | placeholder {k : SCtx} {L : List (String × STy)} : C.inModifier = true →
      StmtD C (k := k) L (.simpleStmt (.exprStmt (.ident "_"))) L
  /-- `T l x;` with solc's location rule. -/
  | declVar {k : SCtx} {L : List (String × STy)} {t : Syn .typeName} {l : Option DataLoc} {x : String}
      {τ : STy} : t.ty C.env C.scope (l.getD .memory) = Option.some τ → locOK τ l false = true →
      StmtD C (k := k) L (.simpleStmt (.declVar (.varDecl t l x) .none)) ((x, τ) :: L)
  /-- `(, T x, , U y) = e;` (lane FU2-B): `e` is a tuple whose components
  convert implicitly to the declared types; holes discard theirs. -/
  | declTuple {k : SCtx} {L : List (String × STy)} {h : Nat} {d : Syn .varDecl}
      {ds : Syn (.list (.opt .varDecl))} {e : Syn .expr} {slots : List (Option (String × STy))}
      {σs : List STy} : C.tupleSlots h d ds = Option.some slots → Typed (C.at L) e (.tuple σs) →
      slotsFit C.isBase C.mapFree (slots.map (Option.map Prod.snd)) σs = true →
      StmtD C (k := k) L (.simpleStmt (.declTuple h d ds e)) (pushSlots slots L)
  /-- `T l x = e;`: `e` converts implicitly to `T`. -/
  | declInit {k : SCtx} {L : List (String × STy)} {t : Syn .typeName} {l : Option DataLoc} {x : String}
      {e : Syn .expr} {τ σ : STy} : t.ty C.env C.scope (l.getD .memory) = Option.some τ →
      locOK τ l true = true → Typed (C.at L) e σ → σ.implicit C.isBase C.mapFree τ = true →
      StmtD C (k := k) L (.simpleStmt (.declVar (.varDecl t l x) (.some e))) ((x, τ) :: L)
  | block {k : SCtx} {L L' : List (String × STy)} {b : Syn (.list (.item k))} :
      ItemsD C L b L' → StmtD C L (.blockStmt (.block b)) L
  | ifThen {k : SCtx} {L L₁ : List (String × STy)} {c : Syn .expr} {s : Syn (.stmt k)} :
      Typed (C.at L) c .bool → s.isDecl = false → StmtD C L s L₁ → StmtD C L (.ifStmt c s .none) L
  | ifElse {k : SCtx} {L L₁ L₂ : List (String × STy)} {c : Syn .expr} {s t : Syn (.stmt k)} :
      Typed (C.at L) c .bool → s.isDecl = false → t.isDecl = false → StmtD C L s L₁ →
      StmtD C L t L₂ → StmtD C L (.ifStmt c s (.some t)) L
  | whileLoop {l u : Bool} {L L₁ : List (String × STy)} {c : Syn .expr} {s : Syn (.stmt ⟨true, u⟩)} :
      Typed (C.at L) c .bool → s.isDecl = false → StmtD C L s L₁ →
      StmtD C (k := ⟨l, u⟩) L (.whileStmt c s) L
  | doWhile {l u : Bool} {L L₁ : List (String × STy)} {c : Syn .expr} {s : Syn (.stmt ⟨true, u⟩)} :
      s.isDecl = false → StmtD C L s L₁ → Typed (C.at L) c .bool →
      StmtD C (k := ⟨l, u⟩) L (.doWhile s c) L
  /-- `for (; cond; post) s`. -/
  | forLoop {l u : Bool} {L L₂ : List (String × STy)} {c post : Syn (.opt .expr)}
      {s : Syn (.stmt ⟨true, u⟩)} : OptCond (C.at L) c → OptExpr (C.at L) post → s.isDecl = false →
      StmtD C L s L₂ → StmtD C (k := ⟨l, u⟩) L (.forStmt .none c post s) L
  /-- `for (init; cond; post) s`: the init's local is in scope of the rest. -/
  | forInit {l u : Bool} {L L₁ L₂ : List (String × STy)} {i : Syn .simple} {c post : Syn (.opt .expr)}
      {s : Syn (.stmt ⟨true, u⟩)} : StmtD C (k := ⟨true, u⟩) L (.simpleStmt i) L₁ →
      OptCond (C.at L₁) c → OptExpr (C.at L₁) post → s.isDecl = false → StmtD C L₁ s L₂ →
      StmtD C (k := ⟨l, u⟩) L (.forStmt (.some i) c post s) L
  | brk {u : Bool} {L : List (String × STy)} : StmtD C (k := ⟨true, u⟩) L .breakStmt L
  | cont {u : Bool} {L : List (String × STy)} : StmtD C (k := ⟨true, u⟩) L .continueStmt L
  /-- `return;` in a function without returns (solc error 6777 otherwise,
  named returns included). -/
  | ret {k : SCtx} {L : List (String × STy)} : C.rets = [] → StmtD C (k := k) L (.returnStmt .none) L
  /-- `return e;`: `e` converts implicitly to the single return type. -/
  | retVal {k : SCtx} {L : List (String × STy)} {e : Syn .expr} {τ σ : STy} : C.rets = [τ] →
      Typed (C.at L) e σ → σ.implicit C.isBase C.mapFree τ = true → StmtD C (k := k) L (.returnStmt (.some e)) L
  /-- `return (a, b, …);`: each component converts to its return type. -/
  | retTuple {k : SCtx} {L : List (String × STy)} {e : Syn .expr} {s : Syn (.list (.opt .expr))}
      {σ : STy} {σs : List STy} : Typed (C.at L) e σ → TypedSlots (C.at L) s σs → σs ≠ [] →
      argsFit C.isBase C.mapFree (σ :: σs) C.rets = true →
      StmtD C (k := k) L (.returnStmt (.some (.tuple (.some e) s))) L
  /-- `emit E(args);`: exactly one event accepts the arguments. -/
  | emit {k : SCtx} {L : List (String × STy)} {ev : String} {args : Syn (.list .expr)} {d : Decl}
      {σs : List STy} : TypedArgs (C.at L) args σs →
      ((C.at L).declsOf .event ev).filter (·.fitsParams C.env C.isBase C.mapFree σs) = [d] →
      StmtD C (k := k) L (.emit (.ident ev) (.positional args)) L
  /-- `revert E(args);`: exactly one error accepts the arguments. -/
  | revertError {k : SCtx} {L : List (String × STy)} {er : String} {args : Syn (.list .expr)} {d : Decl}
      {σs : List STy} : TypedArgs (C.at L) args σs →
      ((C.at L).declsOf .error er).filter (·.fitsParams C.env C.isBase C.mapFree σs) = [d] →
      StmtD C (k := k) L (.revert (.ident er) (.positional args)) L
  /-- `try c.f(args) returns (T₁ x₁, …) { … } catch … { … }` (lane FU2-B):
  an external call without value whose revert runs the one `catch` clause
  (`CatchD`); the `returns` types, when given, are the function's
  (`STy.sameList`); the returns are bound in the success block (unnamed
  without `returns`). -/
  | tryCall {k : SCtx} {L L₁ L₂ : List (String × STy)} {c : Syn .expr} {f : String}
      {args : Syn (.list .expr)} {rets : Syn (.list .param)} {okb : Syn (.list (.item k))}
      {cl : Syn (.catchClause k)} {dn : DeclName} {d : Decl} {ps rs σs tys : List STy}
      {x : Option String} {cb : Syn (.list (.item k))} :
      Typed (C.at L) c (.contract dn) → TypedArgs (C.at L) args σs →
      extOverloads C.env C.isBase C.mapFree dn f σs = [d] → d.fnSig C.env = Option.some (ps, rs) →
      argsFit C.isBase C.mapFree σs ps = true →
      rets.tys C.env C.scope .memory = Option.some tys → (tys.isEmpty || STy.sameList tys rs) = true →
      ItemsD C ((tryLocals rets.paramNames rs).reverse ++ L) okb L₁ →
      CatchD cl x cb → ItemsD C (catchLocals x L) cb L₂ →
      StmtD C L (.tryStmt (.call (.member c f) (.positional args)) rets (.block okb) cl .nil) L
  /-- A public library call, qualified or through a matching `using`, with
  the standard `Error(string memory)` handler. Other selectors propagate. -/
  | tryLibrary {k : SCtx} {L L₁ L₂ : List (String × STy)} {c : Syn .expr} {f : String}
      {args : Syn (.list .expr)} {rets : Syn (.list .param)} {okb cb : Syn (.list (.item k))}
      {name : Option String} {d : Decl} {ps rs sigmas tys : List STy} :
      TypedArgs (C.at L) ((C.at L).libraryArgs c args) sigmas →
      (C.at L).libraryOverloads c f sigmas = [d] → d.fnSig C.env = some (ps, rs) →
      argsFit C.isBase C.mapFree sigmas ps = true → libraryBoundary ps rs = true →
      rets.tys C.env C.scope .memory = some tys → (tys.isEmpty || STy.sameList tys rs) = true →
      ItemsD C ((tryLocals rets.paramNames rs).reverse ++ L) okb L₁ →
      ItemsD C ((name.getD "", .string .memory) :: L) cb L₂ →
      StmtD C L (.tryStmt (.call (.member c f) (.positional args)) rets (.block okb)
        (.catchSig (some "Error") (.param (.elem .string) (some .memory) name) .nil (.block cb)) .nil) L
  /-- The canonical rethrow, of the `bytes memory` local it names
  (`rethrowVar?`). -/
  | rethrow {k : SCtx} {L : List (String × STy)} {fl : List String} {body : Syn (.list .yulStmt)}
      {d : String} {i : Nat} : isRethrow body = true → (C.at L).resolve d = Option.some (.loc i) →
      (L.map Prod.snd)[i]? = Option.some (.bytes .memory) →
      rethrowVar? body = Option.some d →
      StmtD C (k := k) L (.assembly false fl body) L

/-- Typing of a block's items, in order. -/
inductive ItemsD (C : Ctx) : {k : SCtx} → List (String × STy) → Syn (.list (.item k)) →
    List (String × STy) → Type where
  | nil {k : SCtx} {L : List (String × STy)} : ItemsD C (k := k) L .nil L
  | stmt {k : SCtx} {L L₁ L₂ : List (String × STy)} {s : Syn (.stmt k)} {rest : Syn (.list (.item k))} :
      StmtD C L s L₁ → ItemsD C L₁ rest L₂ → ItemsD C L (.cons (.stmtItem s) rest) L₂
  | unchecked {l : Bool} {L L₁ L₂ : List (String × STy)} {b : Syn (.list (.item ⟨l, true⟩))}
      {rest : Syn (.list (.item ⟨l, false⟩))} :
      ItemsD C L b L₁ → ItemsD C L rest L₂ → ItemsD C L (.cons (.uncheckedItem (.block b)) rest) L₂

end

/-- Statement typing as a proposition. -/
def StmtOK {k : SCtx} (C : Ctx) (L : List (String × STy)) (s : Syn (.stmt k))
    (L' : List (String × STy)) : Prop := Nonempty (StmtD C L s L')

/-- Block typing as a proposition. -/
def ItemsOK {k : SCtx} (C : Ctx) (L : List (String × STy)) (b : Syn (.list (.item k)))
    (L' : List (String × STy)) : Prop := Nonempty (ItemsD C L b L')

/-! ## Laws -/

/-- A statement only adds locals. -/
theorem StmtD.locals_suffix {C : Ctx} {k : SCtx} {L L' : List (String × STy)} {s : Syn (.stmt k)}
    (d : StmtD C L s L') : ∃ ys, L' = ys ++ L := by
  cases d <;> first
    | exact ⟨[], rfl⟩
    | exact ⟨[_], rfl⟩
    | exact pushSlots_suffix _ _

/-- **Constants have their value as type**: every constant expression other
than an address literal or a bare hexadecimal literal is typed by its exact
rational. -/
theorem HasType.of_const {Γ : Ctx} {e : Syn .expr} {q : Q} (h : e.const = Option.some q)
    (ha : e.isAddressLit = false) (hx : e.hexLen? = Option.none) : HasType Γ e (.rational q) :=
  ⟨.const h ha hx⟩

end Solidity.Source
