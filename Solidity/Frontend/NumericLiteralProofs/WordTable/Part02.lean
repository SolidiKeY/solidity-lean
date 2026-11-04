import Solidity.Frontend.NumericLiteralProofs.WordTable.Part01

/-! # Generated direct structural word-table proof.
No scanner changes, equation generation, or raised budgets. -/
namespace Solidity.Frontend.NumericLiteralProofs
open Solidity.Frontend.Checked Solidity.Source

theorem table_prefix_114_101_102_101_114_101_110_99 (r : Bytes) (n : NumLit) :
    solWordTable ([114, 101, 102, 101, 114, 101, 110, 99] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h101 : b = 101
    · subst b
      exact table_prefix_114_101_102_101_114_101_110_99_101 r n h
    ·
      delta solWordTable solWordTable.match_1 at h
      change (dite (b = 101) (fun _ => _) (fun _ => (.other : WordClass))) = .tok (.num n) at h
      rw [dif_neg h101] at h
      cases h

theorem table_prefix_114_101_108_111_99_97_116_97 (r : Bytes) (n : NumLit) :
    solWordTable ([114, 101, 108, 111, 99, 97, 116, 97] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h98 : b = 98
    · subst b
      exact table_prefix_114_101_108_111_99_97_116_97_98 r n h
    ·
      delta solWordTable solWordTable.match_1 at h
      change (dite (b = 98) (fun _ => _) (fun _ => (.other : WordClass))) = .tok (.num n) at h
      rw [dif_neg h98] at h
      cases h

theorem table_prefix_115_117_112_112_111_114_116_115 (r : Bytes) (n : NumLit) :
    solWordTable ([115, 117, 112, 112, 111, 114, 116, 115] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.reserved : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h

theorem table_prefix_117_110_99_104_101_99_107_101 (r : Bytes) (n : NumLit) :
    solWordTable ([117, 110, 99, 104, 101, 99, 107, 101] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h100 : b = 100
    · subst b
      exact table_prefix_117_110_99_104_101_99_107_101_100 r n h
    ·
      delta solWordTable solWordTable.match_1 at h
      change (dite (b = 100) (fun _ => _) (fun _ => (.other : WordClass))) = .tok (.num n) at h
      rw [dif_neg h100] at h
      cases h

theorem table_prefix_97_98_115_116_114_97_99 (r : Bytes) (n : NumLit) :
    solWordTable ([97, 98, 115, 116, 114, 97, 99] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h116 : b = 116
    · subst b
      exact table_prefix_97_98_115_116_114_97_99_116 r n h
    ·
      delta solWordTable solWordTable.match_1 at h
      change (dite (b = 116) (fun _ => _) (fun _ => (.other : WordClass))) = .tok (.num n) at h
      rw [dif_neg h116] at h
      cases h

theorem table_prefix_97_100_100_114_101_115_115 (r : Bytes) (n : NumLit) :
    solWordTable ([97, 100, 100, 114, 101, 115, 115] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.tok (.elem .address) : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h

theorem table_prefix_97_110_111_110_121_109_111 (r : Bytes) (n : NumLit) :
    solWordTable ([97, 110, 111, 110, 121, 109, 111] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h117 : b = 117
    · subst b
      exact table_prefix_97_110_111_110_121_109_111_117 r n h
    ·
      delta solWordTable solWordTable.match_1 at h
      change (dite (b = 117) (fun _ => _) (fun _ => (.other : WordClass))) = .tok (.num n) at h
      rw [dif_neg h117] at h
      cases h

theorem table_prefix_97_115_115_101_109_98_108 (r : Bytes) (n : NumLit) :
    solWordTable ([97, 115, 115, 101, 109, 98, 108] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h121 : b = 121
    · subst b
      exact table_prefix_97_115_115_101_109_98_108_121 r n h
    ·
      delta solWordTable solWordTable.match_1 at h
      change (dite (b = 121) (fun _ => _) (fun _ => (.other : WordClass))) = .tok (.num n) at h
      rw [dif_neg h121] at h
      cases h

theorem table_prefix_99_97_108_108_100_97_116 (r : Bytes) (n : NumLit) :
    solWordTable ([99, 97, 108, 108, 100, 97, 116] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h97 : b = 97
    · subst b
      exact table_prefix_99_97_108_108_100_97_116_97 r n h
    ·
      delta solWordTable solWordTable.match_1 at h
      change (dite (b = 97) (fun _ => _) (fun _ => (.other : WordClass))) = .tok (.num n) at h
      rw [dif_neg h97] at h
      cases h

theorem table_prefix_99_111_110_115_116_97_110 (r : Bytes) (n : NumLit) :
    solWordTable ([99, 111, 110, 115, 116, 97, 110] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h116 : b = 116
    · subst b
      exact table_prefix_99_111_110_115_116_97_110_116 r n h
    ·
      delta solWordTable solWordTable.match_1 at h
      change (dite (b = 116) (fun _ => _) (fun _ => (.other : WordClass))) = .tok (.num n) at h
      rw [dif_neg h116] at h
      cases h

theorem table_prefix_99_111_110_115_116_114_117 (r : Bytes) (n : NumLit) :
    solWordTable ([99, 111, 110, 115, 116, 114, 117] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h99 : b = 99
    · subst b
      exact table_prefix_99_111_110_115_116_114_117_99 r n h
    ·
      delta solWordTable solWordTable.match_1 at h
      change (dite (b = 99) (fun _ => _) (fun _ => (.other : WordClass))) = .tok (.num n) at h
      rw [dif_neg h99] at h
      cases h

theorem table_prefix_99_111_110_116_105_110_117 (r : Bytes) (n : NumLit) :
    solWordTable ([99, 111, 110, 116, 105, 110, 117] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h101 : b = 101
    · subst b
      exact table_prefix_99_111_110_116_105_110_117_101 r n h
    ·
      delta solWordTable solWordTable.match_1 at h
      change (dite (b = 101) (fun _ => _) (fun _ => (.other : WordClass))) = .tok (.num n) at h
      rw [dif_neg h101] at h
      cases h

theorem table_prefix_99_111_110_116_114_97_99 (r : Bytes) (n : NumLit) :
    solWordTable ([99, 111, 110, 116, 114, 97, 99] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h116 : b = 116
    · subst b
      exact table_prefix_99_111_110_116_114_97_99_116 r n h
    ·
      delta solWordTable solWordTable.match_1 at h
      change (dite (b = 116) (fun _ => _) (fun _ => (.other : WordClass))) = .tok (.num n) at h
      rw [dif_neg h116] at h
      cases h

theorem table_prefix_100_101_102_97_117_108_116 (r : Bytes) (n : NumLit) :
    solWordTable ([100, 101, 102, 97, 117, 108, 116] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.reserved : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h

theorem table_prefix_101_120_116_101_114_110_97 (r : Bytes) (n : NumLit) :
    solWordTable ([101, 120, 116, 101, 114, 110, 97] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h108 : b = 108
    · subst b
      exact table_prefix_101_120_116_101_114_110_97_108 r n h
    ·
      delta solWordTable solWordTable.match_1 at h
      change (dite (b = 108) (fun _ => _) (fun _ => (.other : WordClass))) = .tok (.num n) at h
      rw [dif_neg h108] at h
      cases h

end Solidity.Frontend.NumericLiteralProofs
