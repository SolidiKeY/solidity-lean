import Solidity.Source.Preservation.ArrayLiteralControls
import Solidity.Source.Preservation.FragmentControls
import Solidity.Source.Preservation.AllocationControls
import Solidity.Source.Preservation.CallerReferenceControls
import Solidity.Source.Preservation.StorageCopyControls

/-! Checked allocation/frame and joint Hoare preservation controls.
The fragment and call-admission boundaries remain explicit. -/
