#!/usr/bin/env python3
"""Proof-only planned constructor transport, bound to exact HorizonDeploy bytes."""
from pathlib import Path
import argparse
import hashlib
import re
p=argparse.ArgumentParser(description=__doc__)
p.add_argument('--check',action='store_true')
p.add_argument('--output',default='Solidity/Source/FailureDeploymentHorizon.lean')
a=p.parse_args()
raw=Path('Solidity/Source/HorizonDeploy.lean').read_bytes()
s=raw.decode()
body=s[s.index('theorem runInits_grow'):s.index('theorem deploy_approx')]
body=body.replace('growAt G n','PlannedGrow.growAt G (points := points) n')
body=body.replace('approxAt G n','PlannedApprox.approxAt G (points := points) n')
for f in ['runInits','giveArgs','collectArgs','runCtorBody','construct','deploy']:
 body=re.sub(r'(?<![\w.])'+f+r'(?= G\b)',f+' (plan := some points)',body)
body=body.replace('grow_go [','grow_go [check_grow, frame_grow, ')
header='''import Solidity.Source.FailureEvaluatorApprox
import Solidity.Source.HorizonDeploy

/-! Actual fixed-plan initializer, base-argument, modifier-body and deployment
horizon transport. No alternate semantics or execution oracle. This does not
consume the deployment transaction-fate ordinal or prove session/P8 adequacy.
Proof basis: Source/HorizonDeploy.lean SHA256 BASIS. -/
namespace Solidity.Source.FailureExecution.PlannedDeploy
open EM
open Solidity.Roadmap (Address Word Bytes)
variable {E : Env} {points : Roadmap.Evm.FailurePoints}

'''.replace('BASIS',hashlib.sha256(raw).hexdigest())
tail='''
theorem deploy_approx (G : Glob E) (n : Nat) (c : String) (addr sender : Address)
    (value : Word) (args : Bytes) :
    Approx (deploy (plan := some points) G n c addr sender value args)
      (deploy (plan := some points) G (n+1) c addr sender value args) := by
  unfold deploy
  dsimp only
  refine Approx.bind (Approx.refl mark_grow) fun saved => ?_
  refine Approx.bind (Approx.refl Grow.st) fun state => ?_
  split <;> refine Approx.bind (Approx.refl (by grow_go [])) fun _ => ?_ <;>
    refine Approx.attempt_bind (frame_approx _ ?_)
      (fun _ => Approx.refl (by grow_go [check_grow, rollbackTo_grow])) (fun _ => ⟨rfl,rfl⟩) <;>
    split <;> refine Approx.bind (Approx.refl (by grow_go [])) fun _ => ?_ <;>
    split <;> refine Approx.bind (Approx.refl (by grow_go [])) fun _ => ?_ <;>
    refine Approx.bind (Approx.refl (decodeArgs_grow _ _ _)) fun _ => ?_ <;>
    split <;> first | exact construct_approx G _ n c _ | exact Approx.refl (Grow.halt _)

theorem deploy_events_mono (G : Glob E) (c : String) (addr sender : Address)
    (value : Word) (args : Bytes) (locals : Locals E.layout []) (state : St E)
    {horizon later : Nat} (more : horizon ≤ later) :
    ((deploy (plan := some points) G horizon c addr sender value args).run (locals,state)).2.2.events <+:
      ((deploy (plan := some points) G later c addr sender value args).run (locals,state)).2.2.events := by
  have approx := Approx.mono (fun n => deploy_approx (points := points) G n c addr sender value args)
    (fun n => deploy_grow (points := points) G n c addr sender value args) more
  rcases approx.2.2 (locals,state) with cut | same
  · exact cut.2
  · rw [same]
    exact List.prefix_refl _

theorem deploy_stable (G : Glob E) (c : String) (addr sender : Address)
    (value : Word) (args : Bytes) (locals : Locals E.layout []) (state : St E)
    {horizon later : Nat} (more : horizon ≤ later)
    (completed : ((deploy (plan := some points) G horizon c addr sender value args).run
      (locals,state)).1 ≠ .error .timeout) :
    (deploy (plan := some points) G later c addr sender value args).run (locals,state) =
      (deploy (plan := some points) G horizon c addr sender value args).run (locals,state) := by
  have approx := Approx.mono (fun n => deploy_approx (points := points) G n c addr sender value args)
    (fun n => deploy_grow (points := points) G n c addr sender value args) more
  rcases approx.2.2 (locals,state) with cut | same
  · exact False.elim (completed cut.1)
  · exact same.symm

end Solidity.Source.FailureExecution.PlannedDeploy
'''
expected=(header+body+tail).encode();out=Path(a.output)
if a.check:
 if not out.is_file() or out.read_bytes()!=expected: raise SystemExit('FAIL: stale generated planned deployment proof')
 print('PASS: planned deployment proof matches exact basis bytes')
else: out.write_bytes(expected)
