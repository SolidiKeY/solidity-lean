import Solidity.Frontend.Static.Infer

/-!
# Statement checking for S01's `StmtD`/`ItemsD` (G13)

`inferS C s L` computes every S01 statement derivation `StmtD C L s L'`
(and `ItemsD` for blocks) of a statement `s` with locals `L`, in the body
context `C`, as data: sound by construction.  Expressions inside are
checked by `infer` (`Solidity/Frontend/Static/Infer.lean`), at the locals
the statement sees (`C.at L`).  Completeness is
`Solidity/Frontend/Static/InferStmtComplete.lean`.

The walk covers every category, as `infer` does; the locals are an argument,
since a declaration extends them for the rest of its block.  A `for`
initializer is checked as the statement `simpleStmt i` (S01's `forInit`),
and the canonical rethrow's local is searched among the locals.
-/

namespace Solidity.Frontend.Static

open Solidity.Source

/-- Locals, innermost first. -/
abbrev Locals := List (String × STy)

section
variable (C : Ctx)

/-- What `inferS` returns for a tree of category `c` with locals `L`. -/
inductive SRes : (c : Cat) → Syn c → Locals → Type where
  | stmt {k : SCtx} {L L' : Locals} {s : Syn (.stmt k)} : StmtD C L s L' → SRes (.stmt k) s L
  | items {k : SCtx} {L L' : Locals} {b : Syn (.list (.item k))} : ItemsD C L b L' →
      SRes (.list (.item k)) b L
  | block {k : SCtx} {L L' : Locals} {b : Syn (.list (.item k))} : ItemsD C L b L' →
      SRes (.block k) (.block b) L
  | itemS {k : SCtx} {L L' : Locals} {s : Syn (.stmt k)} : StmtD C L s L' →
      SRes (.item k) (.stmtItem s) L
  | itemU {l : Bool} {L L' : Locals} {b : Syn (.list (.item ⟨l, true⟩))} : ItemsD C L b L' →
      SRes (.item ⟨l, false⟩) (.uncheckedItem (.block b)) L
  | someS {k : SCtx} {L L' : Locals} {s : Syn (.stmt k)} : StmtD C L s L' →
      SRes (.opt (.stmt k)) (.some s) L
  | nilList {c : Cat} {L : Locals} : SRes (.list c) .nil L
  | noneOpt {c : Cat} {L : Locals} : SRes (.opt c) .none L

/-- The statement derivations among the results. -/
def stmtsOf {k : SCtx} {s : Syn (.stmt k)} {L : Locals} :
    List (SRes C (.stmt k) s L) → List (Σ L', StmtD C L s L') :=
  List.filterMap fun r =>
    match r with
    | .stmt d => Option.some ⟨_, d⟩

/-- The block-item derivations among the results. -/
def itemsOf {k : SCtx} {b : Syn (.list (.item k))} {L : Locals} :
    List (SRes C (.list (.item k)) b L) → List (Σ L', ItemsD C L b L') :=
  List.filterMap fun r =>
    match r with
    | .items d => Option.some ⟨_, d⟩
    | .nilList => Option.some ⟨_, .nil⟩

/-- One item prepended to the rest of a block, typed at the locals the item
leaves (a statement) or at the same locals (an `unchecked` block). -/
def consS : {c : Cat} → {x : Syn c} → {xs : Syn (.list c)} → {L : Locals} → SRes C c x L →
    ((L' : Locals) → List (SRes C (.list c) xs L')) → List (SRes C (.list c) (.cons x xs) L)
  | _, _, _, _, .itemS (L' := L₁) d, rxs => (itemsOf C (rxs L₁)).map fun p => .items (.stmt d p.2)
  | _, _, _, L, .itemU d, rxs => (itemsOf C (rxs L)).map fun p => .items (.unchecked d p.2)
  | _, _, _, _, _, _ => []

/-- `T l x;`, `T l x = e;`, `e;`, `_;`: a simple statement as a statement. -/
def simpleRes {k : SCtx} (L : Locals) : (i : Syn .simple) → List (Σ L', StmtD C (k := k) L (.simpleStmt i) L')
  | .exprStmt e =>
    ((tysOf (C.at L) (infer (C.at L) e)).map fun p => ⟨L, .expr p.2⟩) ++
    (match e with
     | .ident "_" => if h : C.inModifier = true then [⟨L, .placeholder h⟩] else []
     | _ => [])
  | .declVar (.varDecl t l x) .none =>
    match ht : t.ty C.env C.scope (l.getD .memory) with
    | Option.some τ => if hl : locOK τ l false = true then [⟨(x, τ) :: L, .declVar ht hl⟩] else []
    | Option.none => []
  | .declVar (.varDecl t l x) (.some e) =>
    match ht : t.ty C.env C.scope (l.getD .memory) with
    | Option.some τ =>
      if hl : locOK τ l true = true then
        (tysOf (C.at L) (infer (C.at L) e)).filterMap fun p =>
          if hc : p.1.implicit C.isBase τ = true then Option.some ⟨(x, τ) :: L, .declInit ht hl p.2 hc⟩
          else Option.none
      else []
    | Option.none => []
  | _ => []

/-- An optional loop condition. -/
def condOpt (L : Locals) : (c : Syn (.opt .expr)) → List (OptCond (C.at L) c)
  | .none => [.none]
  | .some e => (tysOf (C.at L) (infer (C.at L) e)).filterMap fun p =>
      match p with
      | ⟨.bool, d⟩ => Option.some (.some d)
      | _ => Option.none

/-- An optional loop step. -/
def exprOpt (L : Locals) : (c : Syn (.opt .expr)) → List (OptExpr (C.at L) c)
  | .none => [.none]
  | .some e => (tysOf (C.at L) (infer (C.at L) e)).map fun p => .some p.2

/-- `return …;`. -/
def returnRes {k : SCtx} (L : Locals) : (o : Syn (.opt .expr)) → List (SRes C (.stmt k) (.returnStmt o) L)
  | .none =>
    match hr : C.rets with
    | [] => [.stmt (.ret hr)]
    | _ => []
  | .some e =>
    (match hr : C.rets with
     | [τ] => (tysOf (C.at L) (infer (C.at L) e)).filterMap fun p =>
         if hc : p.1.implicit C.isBase τ = true then Option.some (.stmt (.retVal hr p.2 hc)) else Option.none
     | _ => []) ++
    (match e with
     | .tuple (.some e0) s0 =>
       (tysOf (C.at L) (infer (C.at L) e0)).flatMap fun p =>
         (slotsOf (C.at L) (infer (C.at L) s0)).filterMap fun q =>
           if hf : argsFit C.isBase (p.1 :: q.1) C.rets = true then Option.some (.stmt (.retTuple p.2 q.2 hf))
           else Option.none
     | _ => [])

/-- `emit E(args);`. -/
def emitRes {k : SCtx} (L : Locals) : (ev : Syn .expr) → (a : Syn .callArgs) →
    List (SRes C (.stmt k) (.emit ev a) L)
  | .ident ev, .positional args =>
    (argsOf (C.at L) (infer (C.at L) args)).flatMap fun p =>
      match hf : ((C.at L).declsOf .event ev).filter (·.fitsParams C.env C.isBase p.1) with
      | [_] => [.stmt (.emit p.2 hf)]
      | _ => []
  | _, _ => []

/-- `revert E(args);`. -/
def revertRes {k : SCtx} (L : Locals) : (er : Syn .expr) → (a : Syn .callArgs) →
    List (SRes C (.stmt k) (.revert er a) L)
  | .ident er, .positional args =>
    (argsOf (C.at L) (infer (C.at L) args)).flatMap fun p =>
      match hf : ((C.at L).declsOf .error er).filter (·.fitsParams C.env C.isBase p.1) with
      | [_] => [.stmt (.revertError p.2 hf)]
      | _ => []
  | _, _ => []

/-- The canonical rethrow, of a `bytes memory` local. -/
def rethrowRes {k : SCtx} (L : Locals) (fl : List String) (body : Syn (.list .yulStmt)) :
    List (SRes C (.stmt k) (.assembly false fl body) L) :=
  if hb : isRethrow body = true then
    (L.map Prod.fst).filterMap fun d =>
      match hr : (C.at L).resolve d with
      | Option.some (.loc i) =>
        match ht : (L.map Prod.snd)[i]? with
        | Option.some (.bytes .memory) =>
          if hp : (body.paths.map IdPath.last).all (· == d) = true then
            Option.some (.stmt (.rethrow hb hr ht hp))
          else Option.none
        | _ => Option.none
      | _ => Option.none
  else []

/-- **Statement checking**: every derivation S01 gives the tree with the
locals `L`, by rule. -/
def inferS : {c : Cat} → (s : Syn c) → (L : Locals) → List (SRes C c s L)
  | _, .nil, _ => [.nilList]
  | _, .none, _ => [.noneOpt]
  | _, .cons x xs, L => (inferS x L).flatMap fun r => consS C r (fun L' => inferS xs L')
  | _, .some s, L => (inferS s L).filterMap fun r =>
      match r with
      | .stmt d => Option.some (.someS d)
      | _ => Option.none
  | _, .block b, L => (itemsOf C (inferS b L)).map fun p => .block p.2
  | _, .stmtItem s, L => (inferS s L).filterMap fun r =>
      match r with
      | .stmt d => Option.some (.itemS d)
  | _, .uncheckedItem bl, L => (inferS bl L).filterMap fun r =>
      match r with
      | .block d => Option.some (.itemU d)
  | _, .simpleStmt i, L => (simpleRes C L i).map fun p => .stmt p.2
  | _, .blockStmt bl, L => (inferS bl L).filterMap fun r =>
      match r with
      | .block d => Option.some (.stmt (.block d))
  | _, .ifStmt c s o, L =>
    (tysOf (C.at L) (infer (C.at L) c)).flatMap fun pc =>
      match pc with
      | ⟨.bool, dc⟩ =>
        if hs : s.isDecl = false then
          (inferS s L).flatMap fun r =>
            match r with
            | .stmt ds => (inferS o L).filterMap fun r' =>
                match r' with
                | .noneOpt => Option.some (.stmt (.ifThen dc hs ds))
                | .someS (s := t) dt =>
                  if ht : t.isDecl = false then Option.some (.stmt (.ifElse dc hs ht ds dt)) else Option.none
        else []
      | _ => []
  | _, .whileStmt c s, L =>
    (tysOf (C.at L) (infer (C.at L) c)).flatMap fun pc =>
      match pc with
      | ⟨.bool, dc⟩ =>
        if hs : s.isDecl = false then
          (inferS s L).filterMap fun r =>
            match r with
            | .stmt ds => Option.some (.stmt (.whileLoop dc hs ds))
        else []
      | _ => []
  | _, .doWhile s c, L =>
    (tysOf (C.at L) (infer (C.at L) c)).flatMap fun pc =>
      match pc with
      | ⟨.bool, dc⟩ =>
        if hs : s.isDecl = false then
          (inferS s L).filterMap fun r =>
            match r with
            | .stmt ds => Option.some (.stmt (.doWhile hs ds dc))
        else []
      | _ => []
  | _, .forStmt (u := u) .none c post s, L =>
    if hs : s.isDecl = false then
      (condOpt C L c).flatMap fun dc => (exprOpt C L post).flatMap fun dp =>
        (inferS s L).filterMap fun r =>
          match r with
          | .stmt ds => Option.some (.stmt (.forLoop dc dp hs ds))
    else []
  | _, .forStmt (u := u) (.some i) c post s, L =>
    if hs : s.isDecl = false then
      (simpleRes C (k := ⟨true, u⟩) L i).flatMap fun pi =>
        (condOpt C pi.1 c).flatMap fun dc => (exprOpt C pi.1 post).flatMap fun dp =>
          (inferS s pi.1).filterMap fun r =>
            match r with
            | .stmt ds => Option.some (.stmt (.forInit pi.2 dc dp hs ds))
    else []
  | _, .breakStmt, _ => [.stmt .brk]
  | _, .continueStmt, _ => [.stmt .cont]
  | _, .returnStmt o, L => returnRes C L o
  | _, .emit ev a, L => emitRes C L ev a
  | _, .revert er a, L => revertRes C L er a
  | _, .assembly false fl body, L => rethrowRes C L fl body
  | _, _, _ => []

end

/-- The locals a statement can leave, as checked. -/
def stmtLocals (C : Ctx) {k : SCtx} (s : Syn (.stmt k)) (L : Locals) : List Locals :=
  (stmtsOf C (inferS C s L)).map Sigma.fst

/-- The locals a block can leave, as checked. -/
def itemsLocals (C : Ctx) {k : SCtx} (b : Syn (.list (.item k))) (L : Locals) : List Locals :=
  (itemsOf C (inferS C b L)).map Sigma.fst

end Solidity.Frontend.Static
