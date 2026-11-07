import Solidity.Yul.Views.FixedDeclarationDefaults
import Solidity.Yul.Views.FixedDeclarationControls
import Solidity.Yul.Views.RootDeclarationControls

/-! Actual Inner[2][2]/uint128[3] and multi-root declarations derive available
zero defaults through the recursive packer. Empty Source cells stay unwritten;
explicitly written defaults stay explicit under unchanged view preparation. -/
namespace Solidity.Yul.Views.Controls

theorem fdd_recursive_available : (recursiveRegistry account).all
    (fun c => (Source.Val.default recursiveDeclEnv.layout (recursiveDeclEnv.lay account c.path)).isSome)=true := by decide

theorem fdd_recursive_check : scalarZeroDefaultCheck (recursiveRegistry account)=true := by
  change scalarZeroDefaultCheck recursiveChecked.registrations=true
  rw [FixedDeclarationDefaults.fixed_check recursiveLayout ⟨recursiveRoot,[]⟩ account (8*32) _ _ recursiveChecked.packed]
  exact fdd_recursive_available

theorem fdd_recursive_view : finiteView (recursiveRegistry account) Source.Storage.empty (fun _ => 0) :=
  FixedDeclarationDefaults.fixed_empty_view recursiveLayout ⟨recursiveRoot,[]⟩ account (8*32) _ _ recursiveChecked.packed
    (List.all_eq_true.mp fdd_recursive_available)

theorem fdd_recursive_unchanged : finiteWriteback (recursiveRegistry account) (fun _ => 0) Source.Storage.empty=some Source.Storage.empty :=
  finiteWriteback_unchanged _ _ _ fdd_recursive_view

theorem fdd_recursive_encode : finiteEncode (recursiveRegistry account) Source.Storage.empty (fun _ => 0)=some (fun _ => 0) :=
  finiteEncode_unchanged _ _ _ fdd_recursive_view

theorem fdd_checked_payloads : FixedDeclarationDefaults.Payloads (rootRegistry account) :=
  FixedDeclarationDefaults.checked rootDeclarations rootChecked

theorem fdd_roots_unchanged : finiteWriteback (rootRegistry account) (fun _ => 0) Source.Storage.empty=some Source.Storage.empty :=
  FixedDeclarationDefaults.roots_empty_writeback rootDeclarations account 0 _ _ rootChecked.packed
    (List.all_eq_true.mp (by decide))

def fddWritten : Source.Storage recursiveDeclEnv.layout (recursiveDeclEnv.lay account) :=
  Source.Storage.empty.write (recursiveGridPath 0 0 0) (.bool false)

theorem fdd_same_read (path : Source.SPath) : fddWritten.read path=(Source.Storage.empty : Source.Storage recursiveDeclEnv.layout (recursiveDeclEnv.lay account)).read path := by
  first | (simp only;done) | skip
  by_cases same : path=recursiveGridPath 0 0 0
  · subst path
    rw [fddWritten,Source.Storage.write_read]
    rfl
  · exact Source.Storage.write_other _ same _

theorem fdd_written_view : finiteView (recursiveRegistry account) fddWritten (fun _ => 0) := by
  intro c member
  unfold scalarPathView
  rw [fdd_same_read]
  exact fdd_recursive_view c member

theorem fdd_written_unchanged : finiteWriteback (recursiveRegistry account) (fun _ => 0) fddWritten=some fddWritten :=
  finiteWriteback_unchanged _ _ _ fdd_written_view

theorem fdd_cell_distinction :
    (Source.Storage.empty : Source.Storage recursiveDeclEnv.layout (recursiveDeclEnv.lay account)).cell (recursiveGridPath 0 0 0)=none ∧
    fddWritten.cell (recursiveGridPath 0 0 0)=some (.bool false) := ⟨rfl,by simp only [fddWritten,Source.Storage.write,Source.Storage.set,dif_pos]⟩
end Solidity.Yul.Views.Controls
