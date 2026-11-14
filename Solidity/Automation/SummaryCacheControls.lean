import Solidity.Automation.SummaryCache

/-! Collision, invalidation and retry controls for the verdict cache. -/
namespace Solidity.Automation.Summary.Controls

private def key : Key := ⟨"f", "ensures result = 1", "layout-v1", ["g/body/spec"]⟩
private def valid (k : Key) : Prop := k.function = "f"
private def collisionCache : Cache valid := { fingerprint := fun _ => 0 }
private def positive : Verdict valid key := .proved rfl
private def saved := collisionCache.insert key positive

-- A hit must skip the checker even when that checker would return unknown.
#guard (saved.check key (fun _ => none)).2.2 == false
#guard (saved.lookup key).isSome
-- Changing any semantic input invalidates the hit, despite identical hashes.
#guard (saved.lookup { key with function := "other" }).isNone
#guard (saved.lookup { key with specification := "ensures result = 2" }).isNone
#guard (saved.lookup { key with context := "layout-v2" }).isNone
#guard (saved.lookup { key with dependencies := ["g/changed-body/spec"] }).isNone

private def negativeKey : Key := { key with function := "other" }
private def negative : Verdict valid negativeKey := .refuted (by change ¬ ("other" : String) = "f"; decide)
private def both := saved.insert negativeKey negative
-- Distinct entries in one bucket retain their respective certificates.
#guard (both.lookup key).isSome
#guard (both.lookup negativeKey).isSome
#guard (both.check negativeKey (fun _ => none)).2.2 == false

private def verify (k : Key) : Option (Verdict valid k) :=
  if h : k.function = "f" then some (.proved h) else none

-- Repeated unchanged functions are checked once; unknowns remain retryable.
#guard (collisionCache.checkAll verify [key, key, key]).2.2 == 1
#guard (collisionCache.checkAll verify [negativeKey, negativeKey]).2.2 == 2
#guard (saved.checkAll verify [key, { key with specification := "new" }, key]).2.2 == 1
#guard (saved.checkAll verify [key, { key with dependencies := ["new"] }, key]).2.2 == 1

private def retry := (collisionCache.check key (fun _ => none)).2.1
private def succeeded := retry.check key verify
#guard succeeded.1.isSome
#guard succeeded.2.2 == true
#guard (succeeded.2.1.check key (fun _ => none)).2.2 == false

end Solidity.Automation.Summary.Controls
