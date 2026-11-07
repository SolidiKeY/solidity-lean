import Solidity.Frontend.NumericLiteralProofs.WordTable.Part10

/-! # Generated direct structural word-table proof.
No scanner changes, equation generation, or raised budgets. -/
namespace Solidity.Frontend.NumericLiteralProofs
open Solidity.Frontend.Checked Solidity.Source

theorem table_prefix_109_117_116_97_98 (r : Bytes) (n : NumLit) :
    solWordTable ([109, 117, 116, 97, 98] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h108 : b = 108
    · subst b
      exact table_prefix_109_117_116_97_98_108 r n h
    ·
      delta solWordTable solWordTable.match_1 at h
      change (dite (b = 108) (fun _ => _) (fun _ => (.other : WordClass))) = .tok (.num n) at h
      rw [dif_neg h108] at h
      cases h

theorem table_prefix_111_118_101_114_114 (r : Bytes) (n : NumLit) :
    solWordTable ([111, 118, 101, 114, 114] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h105 : b = 105
    · subst b
      exact table_prefix_111_118_101_114_114_105 r n h
    ·
      delta solWordTable solWordTable.match_1 at h
      change (dite (b = 105) (fun _ => _) (fun _ => (.other : WordClass))) = .tok (.num n) at h
      rw [dif_neg h105] at h
      cases h

theorem table_prefix_112_97_114_116_105 (r : Bytes) (n : NumLit) :
    solWordTable ([112, 97, 114, 116, 105] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h97 : b = 97
    · subst b
      exact table_prefix_112_97_114_116_105_97 r n h
    ·
      delta solWordTable solWordTable.match_1 at h
      change (dite (b = 97) (fun _ => _) (fun _ => (.other : WordClass))) = .tok (.num n) at h
      rw [dif_neg h97] at h
      cases h

theorem table_prefix_112_97_121_97_98 (r : Bytes) (n : NumLit) :
    solWordTable ([112, 97, 121, 97, 98] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h108 : b = 108
    · subst b
      exact table_prefix_112_97_121_97_98_108 r n h
    ·
      delta solWordTable solWordTable.match_1 at h
      change (dite (b = 108) (fun _ => _) (fun _ => (.other : WordClass))) = .tok (.num n) at h
      rw [dif_neg h108] at h
      cases h

theorem table_prefix_112_114_97_103_109 (r : Bytes) (n : NumLit) :
    solWordTable ([112, 114, 97, 103, 109] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h97 : b = 97
    · subst b
      exact table_prefix_112_114_97_103_109_97 r n h
    ·
      delta solWordTable solWordTable.match_1 at h
      change (dite (b = 97) (fun _ => _) (fun _ => (.other : WordClass))) = .tok (.num n) at h
      rw [dif_neg h97] at h
      cases h

theorem table_prefix_112_114_105_118_97 (r : Bytes) (n : NumLit) :
    solWordTable ([112, 114, 105, 118, 97] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h116 : b = 116
    · subst b
      exact table_prefix_112_114_105_118_97_116 r n h
    ·
      delta solWordTable solWordTable.match_1 at h
      change (dite (b = 116) (fun _ => _) (fun _ => (.other : WordClass))) = .tok (.num n) at h
      rw [dif_neg h116] at h
      cases h

theorem table_prefix_112_114_111_109_105 (r : Bytes) (n : NumLit) :
    solWordTable ([112, 114, 111, 109, 105] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h115 : b = 115
    · subst b
      exact table_prefix_112_114_111_109_105_115 r n h
    ·
      delta solWordTable solWordTable.match_1 at h
      change (dite (b = 115) (fun _ => _) (fun _ => (.other : WordClass))) = .tok (.num n) at h
      rw [dif_neg h115] at h
      cases h

theorem table_prefix_112_117_98_108_105 (r : Bytes) (n : NumLit) :
    solWordTable ([112, 117, 98, 108, 105] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h99 : b = 99
    · subst b
      exact table_prefix_112_117_98_108_105_99 r n h
    ·
      delta solWordTable solWordTable.match_1 at h
      change (dite (b = 99) (fun _ => _) (fun _ => (.other : WordClass))) = .tok (.num n) at h
      rw [dif_neg h99] at h
      cases h

theorem table_prefix_114_101_99_101_105 (r : Bytes) (n : NumLit) :
    solWordTable ([114, 101, 99, 101, 105] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h118 : b = 118
    · subst b
      exact table_prefix_114_101_99_101_105_118 r n h
    ·
      delta solWordTable solWordTable.match_1 at h
      change (dite (b = 118) (fun _ => _) (fun _ => (.other : WordClass))) = .tok (.num n) at h
      rw [dif_neg h118] at h
      cases h

theorem table_prefix_114_101_102_101_114 (r : Bytes) (n : NumLit) :
    solWordTable ([114, 101, 102, 101, 114] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h101 : b = 101
    · subst b
      exact table_prefix_114_101_102_101_114_101 r n h
    ·
      delta solWordTable solWordTable.match_1 at h
      change (dite (b = 101) (fun _ => _) (fun _ => (.other : WordClass))) = .tok (.num n) at h
      rw [dif_neg h101] at h
      cases h

theorem table_prefix_114_101_108_111_99 (r : Bytes) (n : NumLit) :
    solWordTable ([114, 101, 108, 111, 99] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h97 : b = 97
    · subst b
      exact table_prefix_114_101_108_111_99_97 r n h
    ·
      delta solWordTable solWordTable.match_1 at h
      change (dite (b = 97) (fun _ => _) (fun _ => (.other : WordClass))) = .tok (.num n) at h
      rw [dif_neg h97] at h
      cases h

theorem table_prefix_114_101_116_117_114 (r : Bytes) (n : NumLit) :
    solWordTable ([114, 101, 116, 117, 114] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h110 : b = 110
    · subst b
      exact table_prefix_114_101_116_117_114_110 r n h
    ·
      delta solWordTable solWordTable.match_1 at h
      change (dite (b = 110) (fun _ => _) (fun _ => (.other : WordClass))) = .tok (.num n) at h
      rw [dif_neg h110] at h
      cases h

theorem table_prefix_115_101_97_108_101 (r : Bytes) (n : NumLit) :
    solWordTable ([115, 101, 97, 108, 101] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h100 : b = 100
    · subst b
      exact table_prefix_115_101_97_108_101_100 r n h
    ·
      delta solWordTable solWordTable.match_1 at h
      change (dite (b = 100) (fun _ => _) (fun _ => (.other : WordClass))) = .tok (.num n) at h
      rw [dif_neg h100] at h
      cases h

theorem table_prefix_115_101_99_111_110 (r : Bytes) (n : NumLit) :
    solWordTable ([115, 101, 99, 111, 110] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h100 : b = 100
    · subst b
      exact table_prefix_115_101_99_111_110_100 r n h
    ·
      delta solWordTable solWordTable.match_1 at h
      change (dite (b = 100) (fun _ => _) (fun _ => (.other : WordClass))) = .tok (.num n) at h
      rw [dif_neg h100] at h
      cases h

theorem table_prefix_115_105_122_101_111 (r : Bytes) (n : NumLit) :
    solWordTable ([115, 105, 122, 101, 111] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h102 : b = 102
    · subst b
      exact table_prefix_115_105_122_101_111_102 r n h
    ·
      delta solWordTable solWordTable.match_1 at h
      change (dite (b = 102) (fun _ => _) (fun _ => (.other : WordClass))) = .tok (.num n) at h
      rw [dif_neg h102] at h
      cases h

end Solidity.Frontend.NumericLiteralProofs
