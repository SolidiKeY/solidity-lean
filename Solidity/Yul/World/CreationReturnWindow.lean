import Solidity.Backend.Executable.CreationReturnInterfaceV1
import Solidity.Yul.World.Raw

/-! Conditional consumer of published P14 constructor-return observations.
This inspects linked-address bytes in returned RUNTIME, not the created address
and not the caller's last-returndata after successful CREATE (which is empty).
No Source/CREATE/account/resource correspondence or Producer instance is supplied. -/
namespace Solidity.Yul.World.CreationReturnWindow
open Solidity.Backend Solidity.Backend.Creation
open Solidity.Backend.Executable.CreationReturnInterfaceV1

/-- Strict bounded window derived from the exact returned-address field and
actual constructor Exec premise. Bounds are derived, not assumed separately. -/
theorem returned_window (producer : Producer) {Lib Key : Type}
    (a : Artifact Lib) (links : LinkTable a) (table : ImmutableTable a.runtime.length Key)
    (addresses : Lib → Vector UInt8 20) (h : compatible table links.sites = true)
    (site : LinkSite a.runtime.length Lib) (present : site ∈ links.sites) (output : List UInt8)
    (actual : let b := combinedArtifact a links table addresses h
      Exec b.payload b.payload [] [] (.returned output)) :
    site.location.offset+20 ≤ output.length ∧
    returnWindow output site.location.offset 20 = some (addresses site.library).toList := by
  have image := producer.returned_address a links table addresses h site present output actual
  have length := congrArg List.length image
  simp only [List.length_take,List.length_drop,Vector.length_toList] at length
  have bound : site.location.offset+20 ≤ output.length := by omega
  exact ⟨bound,by rw [returnWindow,if_pos bound,image]⟩

/-- The producer's own witness requires genuinely nonempty runtime/arguments
and immutable patches. It is not an existence theorem for Producer. -/
theorem witnessed (producer : Producer) :
    let w := producer.witness
    let b := combinedArtifact w.artifact w.links w.table w.addresses w.compatible
    w.artifact.runtime ≠ [] ∧ w.artifact.args ≠ [] ∧ w.table.patches ≠ [] ∧
      returnWindow b.runtime w.site.location.offset 20 = some (w.addresses w.site.library).toList := by
  exact ⟨producer.witness.runtime_nonempty,producer.witness.args_nonempty,
    producer.witness.immutable_nonempty,(returned_window producer _ _ _ _ _ _
      producer.witness.present _ producer.witness.executed).2⟩
end Solidity.Yul.World.CreationReturnWindow
