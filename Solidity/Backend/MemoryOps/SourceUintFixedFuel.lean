import Solidity.Backend.MemoryOps.SourceUintFixedDeclaration

/-! Caller-fuel slack for the actual fixed Source default evaluator. Fuel is
execution data; these laws neither increase proof budgets nor grant admission. -/
namespace Solidity.Backend.MemoryOps

theorem source_uint_zeroElems_slack {E : Source.Env} {Γ : Source.RCtx} (y : Source.EMState E Γ) (n extra : Nat) :
    (Source.zeroElems (E := E) (Γ := Γ) (n+extra+1) (.int .u256) n).run y=
      (.ok (fun _ => Source.Data.val (D := E.layout) (sourceUint (PrimTy.dflt .uint))),y) := by
  induction n with
  | zero =>
    have hf : (Fin.elim0 : Fin 0 → Source.Data E.layout (.int .u256))=
        (fun _ => Source.Data.val (D := E.layout) (sourceUint (PrimTy.dflt .uint))) := by
      funext i;exact i.elim0
    change (Except.ok Fin.elim0,y)=_
    rw [hf]
  | succ n ih =>
    rw [Source.zeroElems,Source.Hoare.run_bind]
    rw [show n+1+extra=n+extra+1 by omega]
    rw [show (Source.zeroVal (E := E) (Γ := Γ) (n+extra+1) (.int .u256)).run y=(.ok (sourceUint (PrimTy.dflt .uint)),y) from rfl]
    change (Source.zeroElems (n+extra+1) (.int .u256) n >>= fun f =>
      pure (Source.finCons (Source.Data.val (D := E.layout) (sourceUint (PrimTy.dflt .uint))) f)).run y=_
    rw [Source.Hoare.run_bind,ih]
    have hf : Source.finCons (Source.Data.val (D := E.layout) (sourceUint (PrimTy.dflt .uint)))
        (fun _ : Fin n => Source.Data.val (D := E.layout) (sourceUint (PrimTy.dflt .uint)))=
        (fun _ : Fin (n+1) => Source.Data.val (D := E.layout) (sourceUint (PrimTy.dflt .uint))) := by
      funext i
      unfold Source.finCons
      split <;> rfl
    change (Except.ok (Source.finCons _ _),y)=_
    rw [hf]

theorem source_uint_fixed_zeroVal_slack {E : Source.Env} {Γ : Source.RCtx}
    (y : Source.EMState E Γ) (n extra : Nat) :
    (Source.zeroVal (E := E) (Γ := Γ) (n+extra+3) (.array .memory (.int .u256) (some n))).run y=
      (.ok (.memRef rfl y.2.heap.next),
        (y.1,{y.2 with heap := (y.2.heap.alloc ⟨.array .memory (.int .u256) (some n),sourceUintFixedZero n⟩).1})) := by
  rw [Source.zeroVal]
  change (Source.zeroData (n+extra+2) (.array .memory (.int .u256) (some n)) >>= fun x => Source.allocRef x).run y=_
  rw [Source.Hoare.run_bind,Source.zeroData,Source.Hoare.run_bind,source_uint_zeroElems_slack]
  rfl

/-- info: 'Solidity.Backend.MemoryOps.source_uint_zeroElems_slack' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_uint_zeroElems_slack
/-- info: 'Solidity.Backend.MemoryOps.source_uint_fixed_zeroVal_slack' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_uint_fixed_zeroVal_slack
end Solidity.Backend.MemoryOps
