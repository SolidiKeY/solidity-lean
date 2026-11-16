import Solidity.Tools.Goal

namespace Solidity.Goals.AuditData

/-- Historical audit inventory provenance: 38 shards, 6,452,407 bytes.
This revision is distinct from producer input pins. -/
def historicalAuditRevision : String := "dfdfa238b5bf63955048999fefd291d9d55dbd56"

structure Record where
  path : String
  bytes : List UInt8
  deriving BEq, Repr

/-- Lookup keeps a missing file distinct from a file with no bytes. -/
def contents (files : List Record) (path : String) : Option (List UInt8) :=
  (files.find? fun file => file.path == path).map Record.bytes

def paths (records : List Record) : List String := records.map Record.path

def unique (ps : List String) : Bool := ps.eraseDups.length == ps.length

def recordMatches (files : List Record) (original : Record) : Bool :=
  contents files original.path == some original.bytes

/-- Checks the complete deletion inventory and retained records against full bytes. -/
def regenerationCheck (inventory retained : List Record) (manifest : List String)
    (files : List Record) : Bool :=
  unique (paths inventory) && unique (paths retained) && unique (paths files) &&
  unique manifest && manifest.length == inventory.length &&
  manifest.all (fun path => (paths inventory).contains path) &&
  manifest.all (fun path => !(paths retained).contains path) &&
  inventory.all (recordMatches files) && retained.all (recordMatches files)

end Solidity.Goals.AuditData

namespace Solidity.Goals

open Solidity.Goal

/-- This finite-check statement does not run producers or establish Git facts.
Extracting the 38-path historical inventory, running producers on pinned inputs,
comparing bytes, and checking the deletion diff are executable acceptance evidence
for r1-regen-out-of-git. -/
@[goal Solidity.AuditData.regeneration_check_sound "r1-regen-out-of-git"]
def auditDataRegenerable : Prop :=
  ∀ (inventory retained : List AuditData.Record) (manifest : List String)
    (files : List AuditData.Record),
    AuditData.regenerationCheck inventory retained manifest files = true →
    (∀ original ∈ inventory, AuditData.contents files original.path = some original.bytes) ∧
    (∀ original ∈ retained, AuditData.contents files original.path = some original.bytes)

end Solidity.Goals
