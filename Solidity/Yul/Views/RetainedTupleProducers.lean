import Solidity.Yul.Views.RetainedRuntimeRun

namespace Solidity.Yul.Views

/-- Owner tuple expression, observing the actual argument-producing sequence.
Successful earlier arguments remain captured if a later argument halts. Nested
successful runtime tuples are traversed by runtimeStoragePaths. Intermediates
inside arbitrary head expressions are not thereby instrumented. -/
def captureTupleRun {E Γ types} (G : Source.Glob E) (F : Source.Fr) (n : Nat)
    (es : Source.RArgs E Γ types) (prior : List (EntryReferenceScope E)) (s : Source.EMState E Γ) :=
  match n with
  | 0 => captureRuntimeRun F prior (Source.evalE G F 0 (.tuple es)) s
  | n+1 =>
    let args := captureArgumentsRun G F n es prior s
    ((args.1.1.map Source.RVal.tuple,args.1.2),args.2)

theorem captureTupleRun_source {E Γ types} (G : Source.Glob E) (F : Source.Fr) (n : Nat)
    (es : Source.RArgs E Γ types) (prior) (s : Source.EMState E Γ) :
    (captureTupleRun G F n es prior s).1=(Source.evalE G F n (.tuple es)).run s := by
  cases n with
  | zero => rfl
  | succ n =>
    change ((captureArgumentsRun G F n es prior s).1.1.map Source.RVal.tuple,
      (captureArgumentsRun G F n es prior s).1.2)=
        ((Source.evalArgs G F n es) >>= fun vs => pure (Source.RVal.tuple vs)).run s
    rw [captureArgumentsRun_source G F n es prior s,Source.Hoare.run_bind]
    cases (Source.evalArgs G F n es).run s with
    | mk result after => cases result <;> rfl

theorem captureTupleRun_covers {E Γ types} (G : Source.Glob E) (F : Source.Fr) (n : Nat)
    (es : Source.RArgs E Γ types) (prior) (s after : Source.EMState E Γ) (values : Source.RVals E.layout types)
    (run : (Source.evalArgs G F n es).run s=(.ok values,after)) (p) (inside : p ∈ runtimeValuesPaths values) :
    ∃ scope ∈ (captureTupleRun G F (n+1) es prior s).2, scope.account=F.this ∧ p ∈ scope.paths :=
  captureArgumentsRun_covers G F n es prior s after values run p inside

/-- Exact all-horizon local producer, without getV and its tuple rejection. -/
theorem captureRuntime_local {E Γ σ} (G : Source.Glob E) (F : Source.Fr) (n : Nat)
    (i : Source.Idx Γ σ) (prior : List (EntryReferenceScope E)) (s : Source.EMState E Γ) :
    captureRuntimeRun F prior (Source.evalE G F (n+1) (.local i)) s =
      ((Except.ok (.val (s.1.get i)),s),prior++[entryLocalScope F s.1,entryLocalScope F s.1]++[⟨F.this,valueStoragePaths (s.1.get i)⟩]) := rfl

theorem localStoragePaths_getAt {D Γ σ} (locals : Source.Locals D Γ) (k : Nat)
    (value : Source.Val D σ) (found : locals.getAt k σ=.ok value)
    (p) (inside : p ∈ valueStoragePaths value) : p ∈ localStoragePaths locals := by
  induction k generalizing Γ with
  | zero =>
    cases locals with
    | nil => cases found
    | cons v rest =>
      unfold Source.Locals.getAt at found
      split at found
      · rename_i same
        subst σ
        cases found
        exact List.mem_append_left _ inside
      · cases found
  | succ k ih =>
    cases locals with
    | nil => cases found
    | cons v rest => exact List.mem_append_right _ (ih rest found)

/-- Successful actual retVals extraction accounts for its precise reverse-local
slot ordering and getAt type/index failures. No supplied membership law. -/
theorem retVals_paths_from_locals {D Γ} (locals : Source.Locals D Γ) (base : Nat)
    (types : List Source.STy) (values : Source.RVals D types)
    (run : Source.retVals locals base types=.ok values) (p)
    (inside : p ∈ runtimeValuesPaths values) : p ∈ localStoragePaths locals := by
  induction types with
  | nil => cases run; cases inside
  | cons first rest ih =>
    unfold Source.retVals at run
    cases head : locals.getAt (base+rest.length) first with
    | error error => rw [head] at run; cases run
    | ok value =>
      rw [head] at run
      cases tail : Source.retVals locals base rest with
      | error error => rw [tail] at run; cases run
      | ok next =>
        rw [tail] at run
        cases run
        rcases (runtime_cons_member (.val value) next p).mp inside with here | later
        · exact localStoragePaths_getAt locals _ value head p here
        · exact ih next tail later

/-- Invoke the ENTIRE actual internal call (dispatch, zeroVals, checked runMods,
retVals/mkRet, failures and horizon) unchanged. Input/saved caller provenance is
retained separately from runtime returns. Does not scan all modifier/body or
nested-call intermediate values. Same-frame account attribution is contextual. -/
def captureInternalReturn {E ps} (G : Source.Glob E) (F : Source.Fr) (n : Nat) (d : Source.Decl)
    (values : Source.Vals E.layout ps) (rs : List Source.STy)
    (prior : List (EntryReferenceScope E)) (s : Source.EMState E []) :=
  captureRuntimeRun F (prior++[entryReturnScope F values]) (Source.callInternal G F n d values rs) s

theorem captureInternalReturn_source {E ps} (G : Source.Glob E) (F : Source.Fr) (n : Nat) (d : Source.Decl)
    (values : Source.Vals E.layout ps) (rs : List Source.STy) (prior) (s : Source.EMState E []) :
    (captureInternalReturn G F n d values rs prior s).1=(Source.callInternal G F n d values rs).run s := rfl

def captureInternalFromCaller {E Γ ps} (G : Source.Glob E) (F : Source.Fr) (n : Nat) (d : Source.Decl)
    (values : Source.Vals E.layout ps) (rs : List Source.STy) (prior : List (EntryReferenceScope E))
    (s : Source.EMState E Γ) :=
  ((Source.EM.sub (Γ := Γ) Source.Locals.nil (Source.callInternal G F n d values rs)).run s,
    (captureInternalReturn G F n d values rs (prior++[entryLocalScope F s.1]) (Source.Locals.nil,s.2)).2)

theorem captureInternalFromCaller_keeps_caller {E Γ ps} (G : Source.Glob E) (F : Source.Fr) (n : Nat) (d : Source.Decl)
    (values : Source.Vals E.layout ps) (rs : List Source.STy) (prior) (s : Source.EMState E Γ) :
    entryLocalScope F s.1 ∈ (captureInternalFromCaller G F n d values rs prior s).2 := by
  apply captureRuntimeRun_prefix
  exact List.mem_append_left _ (List.mem_append_right _ List.mem_cons_self)

theorem captureInternalReturn_covers {E ps} (G : Source.Glob E) (F : Source.Fr) (n : Nat) (d : Source.Decl)
    (values : Source.Vals E.layout ps) (rs : List Source.STy) (prior)
    (s after : Source.EMState E []) (result : Source.RVal E.layout (Source.STy.ret rs))
    (run : (Source.callInternal G F n d values rs).run s=(.ok result,after))
    (p) (inside : p ∈ runtimeStoragePaths result) :
    ∃ scope ∈ (captureInternalReturn G F n d values rs prior s).2, scope.account=F.this ∧ p ∈ scope.paths := by
  exact ⟨runtimeScope F result,captureRuntimeRun_return F _ _ _ _ result run,rfl,inside⟩

theorem captureInternalFromCaller_source {E Γ ps} (G : Source.Glob E) (F : Source.Fr) (n : Nat) (d : Source.Decl)
    (values : Source.Vals E.layout ps) (rs : List Source.STy) (prior) (s : Source.EMState E Γ) :
    (captureInternalFromCaller G F n d values rs prior s).1=
      (Source.EM.sub Source.Locals.nil (Source.callInternal G F n d values rs)).run s := rfl

theorem captureInternalFromCaller_success {E Γ ps} (G : Source.Glob E) (F : Source.Fr) (n : Nat) (d : Source.Decl)
    (values : Source.Vals E.layout ps) (rs : List Source.STy) (prior)
    (s : Source.EMState E Γ) (after : Source.EMState E []) (result : Source.RVal E.layout (Source.STy.ret rs))
    (run : (Source.callInternal G F n d values rs).run (Source.Locals.nil,s.2)=(.ok result,after)) :
    (captureInternalFromCaller G F n d values rs prior s).1=(Except.ok (result,after.1),(s.1,after.2)) ∧
      runtimeScope F result ∈ (captureInternalFromCaller G F n d values rs prior s).2 := by
  constructor
  · rw [captureInternalFromCaller_source,actualSub_endpoints,run]
  · exact captureRuntimeRun_return F _ _ _ _ result run

end Solidity.Yul.Views
