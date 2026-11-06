
import Solidity.Yul.FunctionScope

/-! Finite lexical function environments for the no-Solidity-externals backfill.
Bodies retain their actual intrinsic signature and own local context. This does
not execute statements or prove source embedding, and is not a replacement for
the remaining full-context function semantics. -/
namespace Solidity.Yul.Closed

/-- Peel membership without matching an indexed family in evaluated code. -/
def Peel (context : List Sig) (sig : Sig) : Type :=
  match context with
  | [] => PEmpty
  | head :: rest => Sum (Member [head] sig) (Member rest sig)

def peelMember {context sig} (i : Member context sig) : Peel context sig :=
  Member.casesOn (motive := fun context sig _ => Peel context sig) i
    (here := .inl .here)
    (there := fun j => .inr j)

def splitMember (pre post : List Sig) {sig} (i : Member (pre ++ post) sig) :
    Sum (Member pre sig) (Member post sig) :=
  match pre with
  | [] => .inr i
  | _head :: rest =>
    match peelMember i with
    | .inl first => .inl (first.append rest)
    | .inr tail =>
      match splitMember rest post tail with
      | .inl j => .inl (.there j)
      | .inr j => .inr j

/-- A group's bodies store code and its older lexical function environment.
No enclosing local-word vector is stored or available for capture. -/
inductive FunctionEnv : List Sig → Type where
  | nil : FunctionEnv []
  | group {F : List Sig} (signatures : List Sig) (outer : FunctionEnv F) :
      Bodies (signatures ++ F) [] signatures → FunctionEnv (signatures ++ F)

/-- Every closure stores a body typed at its own argument and return slots.
The lexical function context is existential, but the call arity is intrinsic. -/
structure Closure (sig : Sig) where
  functions : List Sig
  environment : FunctionEnv functions
  body : Stmt functions [] ⟨true, false⟩ (sig.args + sig.rets)

def BodyHead (F : List Sig) (G : List ExternalType) (signatures : List Sig) : Type :=
  match signatures with
  | [] => Unit
  | sig :: _ => Stmt F G ⟨true, false⟩ (sig.args + sig.rets)

def BodyTail (F : List Sig) (G : List ExternalType) (signatures : List Sig) : Type :=
  match signatures with
  | [] => Unit
  | _ :: rest => Bodies F G rest

def bodyHead {F G signatures} (bodies : Bodies F G signatures) : BodyHead F G signatures :=
  Bodies.casesOn (motive_3 := fun F G signatures _ => BodyHead F G signatures) bodies
    (nil := ())
    (cons := fun body _ => body)

def bodyTail {F G signatures} (bodies : Bodies F G signatures) : BodyTail F G signatures :=
  Bodies.casesOn (motive_3 := fun F G signatures _ => BodyTail F G signatures) bodies
    (nil := ())
    (cons := fun _ rest => rest)

/-- Select the exact signature-indexed body via a generalized member recursor. -/
def bodyAt {F G signatures sig} (i : Member signatures sig) (bodies : Bodies F G signatures) :
    Stmt F G ⟨true, false⟩ (sig.args + sig.rets) :=
  Member.casesOn
    (motive := fun signatures sig _ => Bodies F G signatures →
      Stmt F G ⟨true, false⟩ (sig.args + sig.rets)) i
    (here := fun bodies => bodyHead bodies)
    (there := fun j bodies => bodyAt j (bodyTail bodies))
    bodies
termination_by structural i

/-- New bodies capture the complete recursive group. Older bodies retain their
older lexical environment; subsequent declarations do not retarget their calls. -/
def lookup {F} (environment : FunctionEnv F) {sig} (i : Member F sig) : Closure sig :=
  FunctionEnv.casesOn
    (motive := fun F _ => {sig : Sig} → Member F sig → Closure sig) environment
    (nil := fun {_} i => PEmpty.elim (peelMember i))
    (group := fun {F} signatures outer bodies {_sig} i =>
      match splitMember signatures F i with
      | .inl j => ⟨_, .group signatures outer bodies, bodyAt j bodies⟩
      | .inr j => lookup outer j)
    i
termination_by structural environment


theorem splitMember_append {pre sig} (post : List Sig) (i : Member pre sig) :
    splitMember pre post (i.append post) = .inl i := by
  induction i with
  | here => rfl
  | @there a b rest j ih =>
      change ((match splitMember rest post (j.append post) with
        | .inl k => Sum.inl (Member.there k) | .inr k => Sum.inr k) :
        Sum (Member (b :: rest) a) (Member post a)) = .inl (.there j)
      rw [ih]

theorem splitMember_prefix (pre : List Sig) {post sig} (i : Member post sig) :
    splitMember pre post (i.prefix pre) = .inr i := by
  induction pre with
  | nil => rfl
  | cons head rest ih =>
      change ((match splitMember rest post (i.prefix rest) with
        | .inl k => Sum.inl (Member.there k) | .inr k => Sum.inr k) :
        Sum (Member (head :: rest) sig) (Member post sig)) = .inr i
      rw [ih]

theorem bodyAt_here {F G sig signatures}
    (body : Stmt F G ⟨true, false⟩ (sig.args + sig.rets)) (rest : Bodies F G signatures) :
    bodyAt (.here : Member (sig :: signatures) sig) (.cons body rest) = body := rfl

theorem bodyAt_there {F G sig signatures} {other : Sig}
    (body : Stmt F G ⟨true, false⟩ (other.args + other.rets)) (rest : Bodies F G signatures)
    (i : Member signatures sig) : bodyAt (.there i) (.cons body rest) = bodyAt i rest := rfl

theorem lookup_group {F signatures sig} (outer : FunctionEnv F)
    (bodies : Bodies (signatures ++ F) [] signatures) (i : Member (signatures ++ F) sig) :
    lookup (.group signatures outer bodies) i =
      (match splitMember signatures F i with
       | .inl j => ⟨_, .group signatures outer bodies, bodyAt j bodies⟩
       | .inr j => lookup outer j) := rfl

/-- A new function closes over the complete group, enabling mutual recursion. -/
theorem lookup_new {F signatures sig} (outer : FunctionEnv F)
    (bodies : Bodies (signatures ++ F) [] signatures) (i : Member signatures sig) :
    lookup (.group signatures outer bodies) (i.append F) =
      ⟨_, .group signatures outer bodies, bodyAt i bodies⟩ := by
  rw [lookup_group, splitMember_append]

/-- An older function is not rebound to the new group's environment. -/
theorem lookup_old {F signatures sig} (outer : FunctionEnv F)
    (bodies : Bodies (signatures ++ F) [] signatures) (i : Member F sig) :
    lookup (.group signatures outer bodies) (i.prefix signatures) = lookup outer i := by
  rw [lookup_group, splitMember_prefix]


end Solidity.Yul.Closed
