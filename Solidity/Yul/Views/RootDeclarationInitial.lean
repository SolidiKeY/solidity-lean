import Solidity.Yul.Views.RootDeclarationReadback

namespace Solidity.Yul.Views.Controls

def rootInitialPhysical (q : Roadmap.Word) : Roadmap.Word :=
  if q = 0 then ⟨0x0000000000000000000000000000000000000000000000000000000000000000,by decide⟩ else if q = 1 then ⟨0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa00,by decide⟩ else if q = 2 then ⟨0xbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb000000,by decide⟩ else if q = 3 then ⟨0xbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb000000,by decide⟩ else if q = 4 then ⟨0xee00000000000000000000000000000000000000000000000000000000000000,by decide⟩ else if q = 5 then ⟨0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc0000,by decide⟩ else if q = 6 then ⟨0x0000000000000000000000000000000000000000000000000000000000000037,by decide⟩ else rootInitialRaw q

theorem root_complement_zero (owns : Fin 32 → Bool) : complementWord owns 0 = 0 := by
  apply word_eq_of_lowBytes
  intro i
  have zero : lowByte (0 : Roadmap.Word) i = 0 := by
    change UInt8.ofNat (0 / 256 ^ (31-(reverseByteIndex 32 i).val)) = 0
    rw [Nat.zero_div]
    rfl
  simp only [complementWord_byte,zero,ite_self]

theorem root_initial_values_match_constructor :
    rootInitialStore.read (rootPath "a") = some (.int 0 (by decide)) ∧
    rootInitialStore.read (rootPath "c") = some (.bool false) ∧
    rootInitialStore.read (rootPath "marker") = some (.int 55 (by decide)) := ⟨rfl,rfl,rfl⟩

theorem root_initial_fields_view : finiteView rootChecked.registrations rootInitialStore rootInitialPhysical :=
  (finiteViewBool_iff _ _ _).mp (by decide)

theorem root_snapshot_eq_seed : rootSnapshot = rootInitialRaw := by
  funext q
  by_cases h0 : q = 0
  · simp only [rootSnapshot,rootInitialRaw,if_pos h0]
  ·
    by_cases h1 : q = 1
    · simp only [rootSnapshot,rootInitialRaw,if_neg h0,if_pos h1]
    ·
      by_cases h2 : q = 2
      · simp only [rootSnapshot,rootInitialRaw,if_neg h0,if_neg h1,if_pos h2]
      ·
        by_cases h3 : q = 3
        · simp only [rootSnapshot,rootInitialRaw,if_neg h0,if_neg h1,if_neg h2,if_pos h3]
        ·
          by_cases h4 : q = 4
          · simp only [rootSnapshot,rootInitialRaw,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_pos h4]
          ·
            by_cases h5 : q = 5
            · simp only [rootSnapshot,rootInitialRaw,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_pos h5]
            ·
              by_cases h6 : q = 6
              · simp only [rootSnapshot,rootInitialRaw,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_pos h6]
              ·
                simp only [rootSnapshot,rootInitialRaw,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_neg h6]

theorem root_initial_mask : packedMask rootChecked.registrations rootInitialPhysical = packedMask rootChecked.registrations rootSnapshot := by
  funext q
  by_cases h0 : q = 0
  · subst q; rfl
  ·
    by_cases h1 : q = 1
    · subst q; rfl
    ·
      by_cases h2 : q = 2
      · subst q; rfl
      ·
        by_cases h3 : q = 3
        · subst q; rfl
        ·
          by_cases h4 : q = 4
          · subst q; rfl
          ·
            by_cases h5 : q = 5
            · subst q; rfl
            ·
              by_cases h6 : q = 6
              · subst q; rfl
              ·
                change complementWord (packedOwnsByte rootChecked.registrations q) (rootInitialPhysical q) =
                  complementWord (packedOwnsByte rootChecked.registrations q) (rootSnapshot q)
                simp only [rootInitialPhysical,rootSnapshot,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_neg h6]

theorem root_initial_actual_residual :
    (fun q => rootInitialCore.residual.cells (complementKey false account q)) = packedMask rootChecked.registrations rootInitialPhysical := by
  funext q
  change packedMask rootChecked.registrations rootInitialRaw q = _
  rw [root_initial_mask,root_snapshot_eq_seed]

theorem root_initial_whole_physical : finiteEncode rootChecked.registrations rootInitialStore
    (fun q => rootInitialCore.residual.cells (complementKey false account q)) = some rootInitialPhysical := by
  rw [root_initial_actual_residual]
  exact packedStoreWriteback_reencode _ _ _ _ _ rootChecked.separated
    (rootChecked.store_unchanged _ _ root_initial_fields_view)

theorem root_all_residual_padding_unchanged :
    (fun q => rootCallerCore.residual.cells (complementKey false account q)) =
      (fun q => rootInitialCore.residual.cells (complementKey false account q)) := by
  rw [root_actual_residual_snapshot]
  funext q
  change packedMask rootChecked.registrations rootSnapshot q = packedMask rootChecked.registrations rootInitialRaw q
  rw [root_snapshot_eq_seed]

theorem root_marker_administratively_unchanged :
    (rootFrame6.1.2.2.ex.world.accounts account).storage.cell (rootPath "marker") =
      (rootState.2.ex.world.accounts account).storage.cell (rootPath "marker") := rfl

theorem root_reverse_pure_field_writeback :
    finiteWriteback rootChecked.registrations.reverse rootSnapshot rootInitialStore =
      finiteWriteback rootChecked.registrations rootSnapshot rootInitialStore :=
  finiteWriteback_reverse _ _ _ rootChecked.separated

theorem root_initial_transient_residual_zero (q : Roadmap.Word) :
    rootInitialCore.residual.cells (complementKey true account q) = 0 :=
  root_complement_zero _

theorem root_initial_transient_source_zero :
    (Source.readLoc (E := rootEnv) (Γ := []) packedStepFrame (τ := .int unsigned16) (.stor (rootPath "temp"))).run rootState =
      (.ok (.int 0 (by decide)),rootState) := rfl

end Solidity.Yul.Views.Controls
