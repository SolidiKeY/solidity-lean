| `Goals/LoweringDiagram.lean` | The `Shrink.Lowering` simulation-diagram vocabulary (`Diagram`, `CallerBound`, `productionNames`, …) that `loweringBySimulation` is stated over; no goal. |
| `Goals/LoweringSim.lean` | `loweringBySimulation`: the H517 lowering shrink goal, open (one simulation diagram over the actual production lowering on t0's fragment; session lift deferred by H556). |
| `Examples/Goals/{LoweringSim,YulLayoutView,YulLayoutPilot}.lean` | One pinned `#roadmap_goal` open check per shrink goal; `Examples/Goals/Shrink.lean` imports the three. |
