import Lean

/-!
# Proof-carrying function verdict cache

Hashes select buckets only. Exact input equality, including the semantic
context and dependency encodings, is required for reuse. A timeout or
unsupported input is represented by `none` and is never saved as a verdict.
The caller supplies canonical inputs and a proposition indexed by those inputs;
this layer does not assert that arbitrary serialized text denotes a program.
-/

namespace Solidity.Automation.Summary

/-- All semantic inputs to a function verdict. Dependency entries must include
transitive inputs (or an exact canonical dependency tree), not just names. -/
structure Key where
  /-- Complete canonical declaration, including body and signature; never just a name. -/
  function : String
  specification : String
  context : String
  dependencies : List String
  deriving DecidableEq, BEq, Hashable, Repr

/-- Both verdicts carry evidence for the exact input. Search failure is neither. -/
inductive Verdict (valid : Key → Prop) (key : Key) where
  | proved (proof : valid key)
  | refuted (proof : ¬ valid key)

/-- A cache entry retains its complete key to reject hash collisions. -/
structure Entry (valid : Key → Prop) where
  key : Key
  verdict : Verdict valid key

/-- The hash is an index, never a trusted certificate. It is configurable so
collision behavior can be exercised with a constant hash in controls. -/
structure Cache (valid : Key → Prop) where
  fingerprint : Key → UInt64 := hash
  buckets : Std.HashMap UInt64 (List (Entry valid)) := {}

private def findEntry {valid : Key → Prop} (key : Key) :
    List (Entry valid) → Option (Verdict valid key)
  | [] => none
  | entry :: rest =>
    if h : entry.key = key then some (h ▸ entry.verdict)
    else findEntry key rest

/-- An exact hit returns a certificate at the requested key. -/
def Cache.lookup {valid : Key → Prop} (cache : Cache valid) (key : Key) :
    Option (Verdict valid key) :=
  findEntry key (cache.buckets.getD (cache.fingerprint key) [])

/-- Insert only a checked positive or negative verdict. -/
def Cache.insert {valid : Key → Prop} (cache : Cache valid) (key : Key)
    (verdict : Verdict valid key) : Cache valid :=
  let bucket := cache.fingerprint key
  { cache with buckets := (cache.buckets.insert bucket
      (⟨key, verdict⟩ :: cache.buckets.getD bucket [])) }

/-- Inserting a certificate makes it reusable, even with a constant hash. -/
theorem Cache.lookup_insert {valid : Key → Prop} (cache : Cache valid) (key : Key)
    (verdict : Verdict valid key) :
    (cache.insert key verdict).lookup key = some verdict := by
  simp only [Cache.lookup, Cache.insert, Std.HashMap.getD_insert_self, findEntry,
    dite_true]

/-- A hit incurs no checker call; a miss invokes the checker exactly once.
The final Boolean records whether the checker was invoked, including failure. -/
def Cache.check {valid : Key → Prop} (cache : Cache valid) (key : Key)
    (verify : (key : Key) → Option (Verdict valid key)) :
    Option (Verdict valid key) × Cache valid × Bool :=
  match cache.lookup key with
  | some verdict => (some verdict, cache, false)
  | none => match verify key with
    | some verdict => (some verdict, cache.insert key verdict, true)
    | none => (none, cache, true)

/-- Reuse skips search entirely; the theorem does not assume hash injectivity. -/
theorem Cache.check_hit {valid : Key → Prop} (cache : Cache valid) (key : Key)
    (verify : (key : Key) → Option (Verdict valid key))
    (verdict : Verdict valid key) (hit : cache.lookup key = some verdict) :
    cache.check key verify = (some verdict, cache, false) := by
  simp only [Cache.check, hit]

/-- Failure leaves the cache unchanged, allowing a later attempt to succeed. -/
theorem Cache.check_unknown {valid : Key → Prop} (cache : Cache valid) (key : Key)
    (verify : (key : Key) → Option (Verdict valid key))
    (miss : cache.lookup key = none) (unknown : verify key = none) :
    cache.check key verify = (none, cache, true) := by
  simp only [Cache.check, miss, unknown]

/-- A batch preserves order and counts actual checker invocations, rather than
pretending failed or unsupported functions cost zero. -/
def Cache.checkAll {valid : Key → Prop} (cache : Cache valid)
    (verify : (key : Key) → Option (Verdict valid key)) :
    (keys : List Key) → List (Option (Entry valid)) × Cache valid × Nat
  | [] => ([], cache, 0)
  | key :: keys =>
    let (verdict, next, checked) := cache.check key verify
    let (verdicts, final, count) := next.checkAll verify keys
    (verdict.map (fun v => ⟨key, v⟩) :: verdicts, final,
      (if checked then 1 else 0) + count)

end Solidity.Automation.Summary

/-! Collision, invalidation and retry controls for the verdict cache. -/
namespace Solidity.Automation.Summary.Controls

private def key : Key := ⟨"f", "ensures result = 1", "layout-v1", ["g/body/spec"]⟩
private def valid (k : Key) : Prop := k.function = "f"
private def collisionCache : Cache valid := { fingerprint := fun _ => 0 }
private def positive : Verdict valid key := .proved rfl
private def saved := Cache.insert collisionCache key positive

-- A hit must skip the checker even when that checker would return unknown.
#guard (Cache.check saved key (fun _ => none)).2.2 == false
#guard (Cache.lookup saved key).isSome
-- Changing any semantic input invalidates the hit, despite identical hashes.
#guard (Cache.lookup saved { key with function := "other" }).isNone
#guard (Cache.lookup saved { key with specification := "ensures result = 2" }).isNone
#guard (Cache.lookup saved { key with context := "layout-v2" }).isNone
#guard (Cache.lookup saved { key with dependencies := ["g/changed-body/spec"] }).isNone

private def negativeKey : Key := { key with function := "other" }
private def negative : Verdict valid negativeKey := .refuted (by change ¬ ("other" : String) = "f"; decide)
private def both := Cache.insert saved negativeKey negative
-- Distinct entries in one bucket retain their respective certificates.
#guard (Cache.lookup both key).isSome
#guard (Cache.lookup both negativeKey).isSome
#guard (Cache.check both negativeKey (fun _ => none)).2.2 == false

private def verify (k : Key) : Option (Verdict valid k) :=
  if h : k.function = "f" then some (.proved h) else none

-- Repeated unchanged functions are checked once; unknowns remain retryable.
#guard (Cache.checkAll collisionCache verify [key, key, key]).2.2 == 1
#guard (Cache.checkAll collisionCache verify [negativeKey, negativeKey]).2.2 == 2
#guard (Cache.checkAll saved verify [key, { key with specification := "new" }, key]).2.2 == 1
#guard (Cache.checkAll saved verify [key, { key with dependencies := ["new"] }, key]).2.2 == 1

private def retry := (Cache.check collisionCache key (fun _ => none)).2.1
private def succeeded := Cache.check retry key verify
#guard succeeded.1.isSome
#guard succeeded.2.2 == true
#guard (Cache.check succeeded.2.1 key (fun _ => none)).2.2 == false

end Solidity.Automation.Summary.Controls
