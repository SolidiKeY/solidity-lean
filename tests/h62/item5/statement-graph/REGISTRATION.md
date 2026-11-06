# Coordinator registration fragment

Keep the exporter optional and outside every intrinsic/core import chain.
It currently lives in the authorized test directory and is compiled explicitly;
no root/module-map registration is necessary for this standalone checkpoint.

If its destination is approved later, register it only as an optional tools/test
module, never in a core layer. Suggested module-map description:

| Module | Purpose |
|---|---|
| `H62.Exporter` (destination pending owner approval) | Elaborated-type statement/premise graph export and read-only imported-declaration tags; imports Lean, never imported by core. |

Preserve this lane's standalone import path until the coordinator approves an
area module and performs root/map registration. Production overlay modules must
import the unchanged producer module and exporter; their exact declaration list,
owner references, binder roles and typed witness mapping require H55-G49 input.
No theorem source modification is requested or authorized by this fragment.
