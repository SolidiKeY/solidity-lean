import Solidity.Yul.Views.RetainedTupleProducers

/-! Caller-boundary consumers of the published tuple/internal-return API.
Actual Source sub restores saved caller locals on success and halt. Parameter,
caller and return scopes retain separate provenance, with same-frame account
attribution. These proofs do not instrument arbitrary body/modifier/nested-call
intermediates or infer reachability from well-typed incoming references. -/
namespace Solidity.Yul.Views.RetainedCallerBoundaries

/-- All previous scopes survive the entire actual internal call. -/
theorem keeps_prefix {E Γ ps} (G : Source.Glob E) (F : Source.Fr) (n : Nat) (d : Source.Decl)
    (values : Source.Vals E.layout ps) (rs : List Source.STy) (prior)
    (s : Source.EMState E Γ) (scope : EntryReferenceScope E) (member : scope∈prior) :
    scope∈(captureInternalFromCaller G F n d values rs prior s).2 := by
  first | (simp only;done) | decide | omega | rfl | skip
  apply captureRuntimeRun_prefix
  exact List.mem_append_left _ (List.mem_append_left _ member)

/-- Incoming argument values are retained even when dispatch/frame setup halts. -/
theorem parameters {E Γ ps} (G : Source.Glob E) (F : Source.Fr) (n : Nat) (d : Source.Decl)
    (values : Source.Vals E.layout ps) (rs : List Source.STy) (prior) (s : Source.EMState E Γ) :
    entryReturnScope F values∈(captureInternalFromCaller G F n d values rs prior s).2 := by
  first | (simp only;done) | decide | omega | rfl | skip
  apply captureRuntimeRun_prefix
  exact List.mem_append_right _ List.mem_cons_self

theorem parameter_paths {E Γ ps} (G : Source.Glob E) (F : Source.Fr) (n : Nat) (d : Source.Decl)
    (values : Source.Vals E.layout ps) (rs : List Source.STy) (prior) (s : Source.EMState E Γ)
    (path : Source.SPath) (inside : path∈returnStoragePaths values) :
    ∃ scope∈(captureInternalFromCaller G F n d values rs prior s).2,
      scope.account=F.this ∧ path∈scope.paths := by
  first | omega | decide | skip
  exact ⟨entryReturnScope F values,parameters G F n d values rs prior s,rfl,inside⟩

theorem caller_paths {E Γ ps} (G : Source.Glob E) (F : Source.Fr) (n : Nat) (d : Source.Decl)
    (values : Source.Vals E.layout ps) (rs : List Source.STy) (prior) (s : Source.EMState E Γ)
    (path : Source.SPath) (inside : path∈localStoragePaths s.1) :
    ∃ scope∈(captureInternalFromCaller G F n d values rs prior s).2,
      scope.account=F.this ∧ path∈scope.paths := by
  first | omega | decide | skip
  exact ⟨entryLocalScope F s.1,captureInternalFromCaller_keeps_caller G F n d values rs prior s,rfl,inside⟩

/-- The actual callee's dirty store is passed through; saved caller locals are
restored even when the call halts. No rollback or empty-caller premise. -/
theorem halt {E Γ ps} (G : Source.Glob E) (F : Source.Fr) (n : Nat) (d : Source.Decl)
    (values : Source.Vals E.layout ps) (rs : List Source.STy) (prior)
    (s : Source.EMState E Γ) (after : Source.EMState E []) (error : Source.Halt)
    (run : (Source.callInternal G F n d values rs).run (Source.Locals.nil,s.2)=(.error error,after)) :
    (captureInternalFromCaller G F n d values rs prior s).1=(.error error,(s.1,after.2)) := by
  first | (simp only;done) | decide | omega | rfl | skip
  rw [captureInternalFromCaller_source,actualSub_endpoints,run]

/-- Every constituent of an actual runtime return, including nested tuples,
is retained at the caller boundary without a getV conversion. -/
theorem returned_paths {E Γ ps} (G : Source.Glob E) (F : Source.Fr) (n : Nat) (d : Source.Decl)
    (values : Source.Vals E.layout ps) (rs : List Source.STy) (prior)
    (s : Source.EMState E Γ) (after : Source.EMState E []) (result : Source.RVal E.layout (Source.STy.ret rs))
    (run : (Source.callInternal G F n d values rs).run (Source.Locals.nil,s.2)=(.ok result,after))
    (path : Source.SPath) (inside : path∈runtimeStoragePaths result) :
    ∃ scope∈(captureInternalFromCaller G F n d values rs prior s).2,
      scope.account=F.this ∧ path∈scope.paths := by
  first | omega | decide | skip
  exact ⟨runtimeScope F result,(captureInternalFromCaller_success G F n d values rs prior s after result run).2,rfl,inside⟩
end Solidity.Yul.Views.RetainedCallerBoundaries
