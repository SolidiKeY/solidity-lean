# G25-IMUL-CHECKED-1105

Work in progress. Published base b86ae4568cef6d6226f4d170360bbb089debe3fb. Existing expression-uniqueness branch and sealed proofs retained. Source success/overflow proof draft adapts the actual CheckedAdd evaluator proof to signed multiplication; NOT YET CHECKED. Existing Evm.Signed.smul_ok and smul_tail already cover signed classification and minimum-times-minus-one guard; reuse them through selected code rather than duplicate arithmetic producers.

Open: selected packet, target and agreement proofs, arbitrary saved-stack populated-frame controls including both operand orders of min*-1, positive/negative controls, bounded VM gates/axiom inventory, finder/skeptic review, cache pack and sealed short commit. No completion claim.

Continuation: fetched origin/master8bf8321873befa3f35ca31e97e5339a1baee93e6 without altering proof branch. Saved Selected, Target and Agreement proof drafts. These remain unchecked; no gate/review/commit claim. Signed range conversion and full selected execution require validation before acceptance.

Fetched3ad22f66d8fc6431378c22e71823436c79dede7f; relevant Signed/MemoryCompile/ValueCertificate unchanged from8bf83218. Added Controls proof draft: both min*-1 orders, lower/upper overflow, signed regular products, boundary identities and arbitrary-integer zero family. These are range controls only; selected-code boundary execution controls and every validation/review obligation remain open.
