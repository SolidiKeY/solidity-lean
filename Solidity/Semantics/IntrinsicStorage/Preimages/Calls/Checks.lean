import Solidity.Semantics.IntrinsicStorage.Preimages.Calls

/-! Frame observers: a finished observation is the actual result; a failed frame keeps its inputs. -/
open Solidity Solidity.Semantics Solidity.Semantics.IntrinsicStorage ContractWorld Frame
variable {K : Type} [DecidableEq K] {contracts : K → Contract} (n : Nat) (w : World contracts)

example {k : K} {α : Type} (r : Handle k) (entry : Entry (contracts k) α) (ctx : Context)
    (fin : (call n w r entry ctx).result ≠ .error .diverge) {e : THalt}
    (h : w.call r entry ctx = .error e) :
    atomic w (call n w r entry ctx) = ((w, .error e), (call n w r entry ctx).inputs) :=
  atomic_failed w _ (((call_approx n w r entry ctx).eq fin).trans h)

example (k : K) (self : Address) (ctor : Prog (contracts k) [] []) (ctx : Context)
    (fin : (create n w k self ctor ctx).result ≠ .error .diverge) :
    (create n w k self ctor ctx).result = w.create k self ctor ctx :=
  (create_approx n w k self ctor ctx).eq fin
