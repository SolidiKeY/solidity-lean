import Solidity.Source.Typing


namespace Solidity.Source

def Env.chain (E : Env) (c : String) : List String := (E.linearize c).getD [c]

def Env.visibleFns (E : Env) (c b x : String) : List Decl :=
  (E.visible (Option.some c) (Option.some b) x).filter fun d =>
    d.kind == .function && d.callableFrom (Option.some c)

def Decl.sameParams (E : Env) (d d' : Decl) : Bool :=
  match d.fnSig E, d'.fnSig E with
  | Option.some (ps, _), Option.some (ps', _) => STy.sameList ps ps'
  | _, _ => false

example (E : Env) (d d' : Decl) (missing : d.fnSig E = none) :
    d.sameParams E d' = false := by
  simp [Decl.sameParams, missing]

example (E : Env) (d d' : Decl) (missing : d'.fnSig E = none) :
    d.sameParams E d' = false := by
  cases signature : d.fnSig E <;> simp [Decl.sameParams, signature, missing]

def InheritedFn (E : Env) (c x : String) (d : Decl) : Prop :=
  ∃ pre b post, E.chain c = pre ++ b :: post ∧ d ∈ E.visibleFns c b x ∧
    ∀ b', b' ∈ pre → ∀ d', d' ∈ E.visibleFns c b' x → d'.sameParams E d = false

end Solidity.Source
