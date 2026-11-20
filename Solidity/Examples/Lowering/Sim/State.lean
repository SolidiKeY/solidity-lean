import Solidity.Correctness.Lowering.Sim.State.Calls
import Solidity.Correctness.Lowering.Sim.State.Storage

/-!
# The state cases of the lowering diagram, used

`StateCases` on its call arm (`elabCallRetWith`): every run is an output of
the arm at a record that meets `RecSim`, so the call conjunct is `SiteSim` of
every run and `StateCases` alone implies `diagram.Simulates`. Its storage
declaration and state statement leaves, on concrete arms.
-/
namespace Solidity.Examples.Lowering.Sim.State

open Solidity.Goals (ElabRan elabKernelTotal)
open Solidity.Correctness.Lowering.Sim

variable [FreshNames]

/-- The call arm at `freeRec`: the empty parts with the counter moved, from
any scope and state, under a record that meets `RecSim`. -/
example (C : Contract) (sc : ElabScope) (st : ECtx × Nat) :
    RecSim C (freeRec C [] (st.1, st.2 + 1)) ∧
    ElabRan (elabCallRetWith C (freeRec C [] (st.1, st.2 + 1)) callValueName [.num 0]
      (some (.fresh "" 0, .uint)) 256 false false false false) sc st ([], none, [])
      (st.1, st.2 + 1) :=
  ⟨freeRec_sim C _ _, freeRec_ran C _ sc st _ _⟩

/-- The state leaf of `StateCases` for `elabStmt1With` on `delete x;`, at every
record: its site obligation holds of no body. -/
example (C : Contract) (rc : ElabRec C) (sc : ElabScope) (st st' : ECtx × Nat) (P : SProg C)
    (ran : ElabRan (elabStmt1With C rc (.delete (.name "x"))) sc st P st') :
    stmtQ C (.delete (.name "x")) sc st P st' :=
  (state_arm C rc).2 _ rfl sc st P st' ran

/-- The storage-declaration leaves, at every record. -/
example (C : Contract) (rc : ElabRec C) : StmtArm C rc .declStorage := declStorage_arm C rc

/-- `StateCases` on the call arm of one contract: `SiteSim` of every run. -/
example (kernel : elabKernelTotal) (states : StateCases) (C : Contract) (raw : List RawStmt)
    (sc : ElabScope) (st : ECtx × Nat) (P : SProg C) (st' : ECtx × Nat) :
    SiteSim C raw sc st P st' :=
  site_of_callRet C (fun rc sim => (states kernel C rc sim).2.2.2.2) raw sc st P st'

/-- `StateCases` alone implies `diagram.Simulates`. -/
example (kernel : elabKernelTotal) (states : StateCases) : diagram.Simulates :=
  simulates_of_state_cases kernel states

end Solidity.Examples.Lowering.Sim.State
