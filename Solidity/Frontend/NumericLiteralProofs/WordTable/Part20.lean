import Solidity.Frontend.NumericLiteralProofs.WordTable.Part19

/-! # Generated direct structural word-table proof.
No scanner changes, equation generation, or raised budgets. -/
namespace Solidity.Frontend.NumericLiteralProofs
open Solidity.Frontend.Checked Solidity.Source

theorem table_prefix_102_105_110 (r : Bytes) (n : NumLit) :
    solWordTable ([102, 105, 110] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h97 : b = 97
    · subst b
      exact table_prefix_102_105_110_97 r n h
    ·
      delta solWordTable solWordTable.match_1 at h
      change (dite (b = 97) (fun _ => _) (fun _ => (.other : WordClass))) = .tok (.num n) at h
      rw [dif_neg h97] at h
      cases h

theorem table_prefix_102_111_114 (r : Bytes) (n : NumLit) :
    solWordTable ([102, 111, 114] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.tok (.kw .for_) : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h

theorem table_prefix_102_117_110 (r : Bytes) (n : NumLit) :
    solWordTable ([102, 117, 110] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h99 : b = 99
    · subst b
      exact table_prefix_102_117_110_99 r n h
    ·
      delta solWordTable solWordTable.match_1 at h
      change (dite (b = 99) (fun _ => _) (fun _ => (.other : WordClass))) = .tok (.num n) at h
      rw [dif_neg h99] at h
      cases h

theorem table_prefix_103_119_101 (r : Bytes) (n : NumLit) :
    solWordTable ([103, 119, 101] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h105 : b = 105
    · subst b
      exact table_prefix_103_119_101_105 r n h
    ·
      delta solWordTable solWordTable.match_1 at h
      change (dite (b = 105) (fun _ => _) (fun _ => (.other : WordClass))) = .tok (.num n) at h
      rw [dif_neg h105] at h
      cases h

theorem table_prefix_104_101_120 (r : Bytes) (n : NumLit) :
    solWordTable ([104, 101, 120] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.tok (.kw .hex) : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h

theorem table_prefix_104_111_117 (r : Bytes) (n : NumLit) :
    solWordTable ([104, 111, 117] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h114 : b = 114
    · subst b
      exact table_prefix_104_111_117_114 r n h
    ·
      delta solWordTable solWordTable.match_1 at h
      change (dite (b = 114) (fun _ => _) (fun _ => (.other : WordClass))) = .tok (.num n) at h
      rw [dif_neg h114] at h
      cases h

theorem table_prefix_105_109_109 (r : Bytes) (n : NumLit) :
    solWordTable ([105, 109, 109] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h117 : b = 117
    · subst b
      exact table_prefix_105_109_109_117 r n h
    ·
      delta solWordTable solWordTable.match_1 at h
      change (dite (b = 117) (fun _ => _) (fun _ => (.other : WordClass))) = .tok (.num n) at h
      rw [dif_neg h117] at h
      cases h

theorem table_prefix_105_109_112 (r : Bytes) (n : NumLit) :
    solWordTable ([105, 109, 112] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h111 : b = 111
    · subst b
      exact table_prefix_105_109_112_111 r n h
    ·
      by_cases h108 : b = 108
      · subst b
        exact table_prefix_105_109_112_108 r n h
      ·
        delta solWordTable solWordTable.match_1 at h
        change (dite (b = 111) (fun _ => _) (fun _ => (dite (b = 108) (fun _ => _) (fun _ => (.other : WordClass))))) = .tok (.num n) at h
        rw [dif_neg h111, dif_neg h108] at h
        cases h

theorem table_prefix_105_110_100 (r : Bytes) (n : NumLit) :
    solWordTable ([105, 110, 100] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h101 : b = 101
    · subst b
      exact table_prefix_105_110_100_101 r n h
    ·
      delta solWordTable solWordTable.match_1 at h
      change (dite (b = 101) (fun _ => _) (fun _ => (.other : WordClass))) = .tok (.num n) at h
      rw [dif_neg h101] at h
      cases h

theorem table_prefix_105_110_108 (r : Bytes) (n : NumLit) :
    solWordTable ([105, 110, 108] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h105 : b = 105
    · subst b
      exact table_prefix_105_110_108_105 r n h
    ·
      delta solWordTable solWordTable.match_1 at h
      change (dite (b = 105) (fun _ => _) (fun _ => (.other : WordClass))) = .tok (.num n) at h
      rw [dif_neg h105] at h
      cases h

theorem table_prefix_105_110_116 (r : Bytes) (n : NumLit) :
    solWordTable ([105, 110, 116] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h101 : b = 101
    · subst b
      exact table_prefix_105_110_116_101 r n h
    ·
      delta solWordTable solWordTable.match_1 at h
      change (dite (b = 101) (fun _ => _) (fun _ => (.other : WordClass))) = .tok (.num n) at h
      rw [dif_neg h101] at h
      cases h

theorem table_prefix_108_101_116 (r : Bytes) (n : NumLit) :
    solWordTable ([108, 101, 116] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.reserved : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h

theorem table_prefix_108_105_98 (r : Bytes) (n : NumLit) :
    solWordTable ([108, 105, 98] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h114 : b = 114
    · subst b
      exact table_prefix_108_105_98_114 r n h
    ·
      delta solWordTable solWordTable.match_1 at h
      change (dite (b = 114) (fun _ => _) (fun _ => (.other : WordClass))) = .tok (.num n) at h
      rw [dif_neg h114] at h
      cases h

theorem table_prefix_109_97_99 (r : Bytes) (n : NumLit) :
    solWordTable ([109, 97, 99] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h114 : b = 114
    · subst b
      exact table_prefix_109_97_99_114 r n h
    ·
      delta solWordTable solWordTable.match_1 at h
      change (dite (b = 114) (fun _ => _) (fun _ => (.other : WordClass))) = .tok (.num n) at h
      rw [dif_neg h114] at h
      cases h

theorem table_prefix_109_97_112 (r : Bytes) (n : NumLit) :
    solWordTable ([109, 97, 112] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h112 : b = 112
    · subst b
      exact table_prefix_109_97_112_112 r n h
    ·
      delta solWordTable solWordTable.match_1 at h
      change (dite (b = 112) (fun _ => _) (fun _ => (.other : WordClass))) = .tok (.num n) at h
      rw [dif_neg h112] at h
      cases h

end Solidity.Frontend.NumericLiteralProofs
