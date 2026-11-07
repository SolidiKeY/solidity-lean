import Solidity.Lowering.StorageOps.SourceCapturedByteCommit
import Solidity.Lowering.StorageOps.SourceCopyFrames
import Solidity.Lowering.StorageOps.SourceCopyReadbacks
import Solidity.Lowering.StorageOps.SourceReadFrames

/-! Operation-generated nested-byte frames over existing Source paths and Op
logs. These proofs derive untouched OLD reads through actual prefix updates;
no physical location relation, compiler or rollback fact is assumed. -/
namespace Solidity.Lowering.StorageOps.SourceByteCommitFrames
open Solidity Solidity.Backend.StorageOps

theorem byteWrites_other : ∀ {E : Solidity.Source.Env} (frame : Solidity.Source.Fr) (path query : Solidity.Source.SPath)
 (typed : ∀ j, (.fixedBytes 1 (by decide) : Solidity.Source.STy)=E.cellTy (path.go (.index j)))
 (start : Nat) (bs : List UInt8) (state : Solidity.Source.ExecState E.layout E.lay E.lay)
 (_apart : ∀ j<bs.length,query≠path.go (.index (start+j))),
 ((state.run (Solidity.Lowering.StorageOps.SourceByteStorageCopy.byteWrites frame path typed start bs)).world.accounts frame.this).storage.read query=
 (state.world.accounts frame.this).storage.read query ∧
 ((state.run (Solidity.Lowering.StorageOps.SourceByteStorageCopy.byteWrites frame path typed start bs)).transient.cells frame.this).read query=
 (state.transient.cells frame.this).read query := by
 intro E frame path query typed start bs state apart
 induction bs generalizing start state with
 | nil => exact ⟨rfl,rfl⟩
 | cons b bs ih =>
   have first := SourceCopyFrames.cell_other (E:=E) frame state (path.go (.index start)) query
     (some ((typed start) ▸ Source.Val.fixedBytes (n:=1) (h:=by decide) [b] rfl)) (by
       have h := apart 0 (by simp only [List.length_cons]; omega)
       simpa only [Nat.add_zero] using h)
   have rest := ih (start+1)
     (state.apply (SourceStorageCopy.cellOp E frame (path.go (.index start))
       (some ((typed start) ▸ Source.Val.fixedBytes (n:=1) (h:=by decide) [b] rfl)))) (by
       intro j member
       have h := apart (j+1) (by simp only [List.length_cons]; omega)
       have index : start+(j+1)=(start+1)+j := by omega
       rw [index] at h
       exact h)
   exact ⟨rest.1.trans first.1,rest.2.trans first.2⟩

/-- info: 'Solidity.Lowering.StorageOps.SourceByteCommitFrames.byteWrites_other' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms byteWrites_other


theorem phase_other : ∀ {E : Solidity.Source.Env} (frame : Solidity.Source.Fr) (path query : Solidity.Source.SPath)
 (typed : ∀ j, (.fixedBytes 1 (by decide) : Solidity.Source.STy)=E.cellTy (path.go (.index j)))
 (headerTyped : (.int Solidity.Source.IntTy.u256 : Solidity.Source.STy)=E.cellTy path)
 (bs : List UInt8) (oldLength padding : Nat) (state : Solidity.Source.ExecState E.layout E.lay E.lay)
 (_headerApart : query≠path) (_byteApart : ∀ j,query≠path.go (.index j)),
 ((state.run (Solidity.Lowering.StorageOps.SourceByteStoragePrepared.phaseLog frame path typed headerTyped bs oldLength padding)).world.accounts frame.this).storage.read query=
 (state.world.accounts frame.this).storage.read query ∧
 ((state.run (Solidity.Lowering.StorageOps.SourceByteStoragePrepared.phaseLog frame path typed headerTyped bs oldLength padding)).transient.cells frame.this).read query=
 (state.transient.cells frame.this).read query := by
 intro E frame path query typed headerTyped bs oldLength padding state headerApart byteApart
 have written := byteWrites_other frame path query typed 0 bs state (by
   intro j member
   simpa only [Nat.zero_add] using byteApart j)
 have cleared := SourceScalarDeleteLog.clear_log_other (E:=E) frame
   (state.run (SourceByteStorageCopy.byteWrites frame path typed 0 bs)) path query
   (List.range' bs.length (min (oldLength-bs.length) (bs.length+padding))) (by
     intro j member
     exact byteApart j)
 have final := SourceCopyFrames.cell_other (E:=E) frame
   ((state.run (SourceByteStorageCopy.byteWrites frame path typed 0 bs)).run
     ((List.range' bs.length (min (oldLength-bs.length) (bs.length+padding))).map
       (fun j=>SourceScalarDeleteLog.clearOp E frame (path.go (.index j))))) path query
   (some (headerTyped ▸ Source.intWrap Source.IntTy.u256 bs.length)) headerApart
 unfold SourceByteStoragePrepared.phaseLog
 rw [Source.run_append,Source.run_append]
 by_cases done : oldLength-bs.length≤bs.length+padding
 · simp only [if_pos done]
   exact ⟨final.1.trans (cleared.1.trans written.1),final.2.trans (cleared.2.trans written.2)⟩
 · simp only [if_neg done]
   exact ⟨cleared.1.trans written.1,cleared.2.trans written.2⟩

/-- info: 'Solidity.Lowering.StorageOps.SourceByteCommitFrames.phase_other' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms phase_other


theorem plans_prefix_other : ∀ {E : Solidity.Source.Env} (frame : Solidity.Source.Fr) (dst query : Solidity.Source.SPath)
 (typed : ∀ i j, (.fixedBytes 1 (by decide) : Solidity.Source.STy)=E.cellTy ((dst.go (.index i)).go (.index j)))
 (headerTyped : ∀ i, (.int Solidity.Source.IntTy.u256 : Solidity.Source.STy)=E.cellTy (dst.go (.index i)))
 (payload : Nat → List UInt8) (oldLength : Nat → Nat) (budget start count visits : Nat)
 (state : Solidity.Source.ExecState E.layout E.lay E.lay) (_within : visits≤count)
 (_headersApart : ∀ j<visits,query≠dst.go (.index (start+j)))
 (_bytesApart : ∀ j<visits,∀ k,query≠(dst.go (.index (start+j))).go (.index k)),
 ((state.run ((Solidity.Lowering.StorageOps.SourceCapturedByteCommit.plans frame dst typed headerTyped payload oldLength budget start count).take visits).flatten).world.accounts frame.this).storage.read query=
 (state.world.accounts frame.this).storage.read query ∧
 ((state.run ((Solidity.Lowering.StorageOps.SourceCapturedByteCommit.plans frame dst typed headerTyped payload oldLength budget start count).take visits).flatten).transient.cells frame.this).read query=
 (state.transient.cells frame.this).read query := by
 intro E frame dst query typed headerTyped payload oldLength budget start count visits state within headersApart bytesApart
 induction count generalizing start visits state with
 | zero =>
   have empty : visits=0 := by omega
   subst visits
   exact ⟨rfl,rfl⟩
 | succ count ih =>
   cases visits with
   | zero => exact ⟨rfl,rfl⟩
   | succ visits =>
     let head := SourceByteStoragePrepared.phaseLog frame (dst.go (.index start)) (typed start) (headerTyped start)
       (payload start) (oldLength start) (count+1+budget-(payload start).length)
     have first := phase_other frame (dst.go (.index start)) query (typed start) (headerTyped start)
       (payload start) (oldLength start) (count+1+budget-(payload start).length) state (by
         simpa only [Nat.add_zero] using headersApart 0 (by omega)) (by
         intro k
         simpa only [Nat.add_zero] using bytesApart 0 (by omega) k)
     have rest := ih (start+1) visits (state.run head) (by omega) (by
       intro j member
       have h := headersApart (j+1) (by omega)
       have index : start+(j+1)=(start+1)+j := by omega
       rw [index] at h
       exact h) (by
       intro j member k
       have h := bytesApart (j+1) (by omega) k
       have index : start+(j+1)=(start+1)+j := by omega
       rw [index] at h
       exact h)
     simp only [SourceCapturedByteCommit.plans,List.take_succ_cons,List.flatten_cons,Source.run_append]
     exact ⟨rest.1.trans first.1,rest.2.trans first.2⟩

/-- info: 'Solidity.Lowering.StorageOps.SourceByteCommitFrames.plans_prefix_other' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms plans_prefix_other


/-- The next sibling header is outside all earlier child writes and clears.
This transports its actual OLD outcome, without assuming that outcome succeeds. -/
theorem prefix_header : ∀ {E : Solidity.Source.Env} {Γ : Solidity.Source.RCtx} (frame : Solidity.Source.Fr) (dst : Solidity.Source.SPath)
 (typed : ∀ i j, (.fixedBytes 1 (by decide) : Solidity.Source.STy)=E.cellTy ((dst.go (.index i)).go (.index j)))
 (headerTyped : ∀ i, (.int Solidity.Source.IntTy.u256 : Solidity.Source.STy)=E.cellTy (dst.go (.index i)))
 (payload : Nat → List UInt8) (oldLength : Nat → Nat) (budget start count visits : Nat)
 (locals : Solidity.Source.Locals E.layout Γ) (state : Solidity.Source.St E) (_within : visits≤count),
 (Solidity.Source.readLen (E:=E) (Γ:=Γ) frame (dst.go (.index (start+visits)))).run
 (locals,{state with ex:=state.ex.run ((Solidity.Lowering.StorageOps.SourceCapturedByteCommit.plans frame dst typed headerTyped payload oldLength budget start count).take visits).flatten})=
 (((Solidity.Source.readLen (E:=E) (Γ:=Γ) frame (dst.go (.index (start+visits)))).run (locals,state)).1,
 (locals,{state with ex:=state.ex.run ((Solidity.Lowering.StorageOps.SourceCapturedByteCommit.plans frame dst typed headerTyped payload oldLength budget start count).take visits).flatten})) := by
 intro E Γ frame dst typed headerTyped payload oldLength budget start count visits locals state within
 have untouched := plans_prefix_other frame dst (dst.go (.index (start+visits))) typed headerTyped
   payload oldLength budget start count visits state.ex within (by
     intro j member
     exact SourceCopyReadbacks.index_ne_index dst (by omega)) (by
     intro j member k same
     have lengths := congrArg (fun p : Source.SPath=>p.steps.length) same
     simp only [Source.SPath.go,List.length_append,List.length_singleton] at lengths
     omega)
 exact SourceReadFrames.readLen_transport frame (dst.go (.index (start+visits))) locals state _ untouched.1 untouched.2

/-- info: 'Solidity.Lowering.StorageOps.SourceByteCommitFrames.prefix_header' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms prefix_header

end Solidity.Lowering.StorageOps.SourceByteCommitFrames
