import Solidity.Frontend.NumericLiteralProofs.WordTable.Part06

/-! # Generated direct structural word-table proof.
No scanner changes, equation generation, or raised budgets. -/
namespace Solidity.Frontend.NumericLiteralProofs
open Solidity.Frontend.Checked Solidity.Source

theorem table_prefix_112_114_97_103_109_97 (r : Bytes) (n : NumLit) :
    solWordTable ([112, 114, 97, 103, 109, 97] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.tok (.kw .pragma) : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h

theorem table_prefix_112_114_105_118_97_116 (r : Bytes) (n : NumLit) :
    solWordTable ([112, 114, 105, 118, 97, 116] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h101 : b = 101
    · subst b
      exact table_prefix_112_114_105_118_97_116_101 r n h
    ·
      delta solWordTable solWordTable.match_1 at h
      change (dite (b = 101) (fun _ => _) (fun _ => (.other : WordClass))) = .tok (.num n) at h
      rw [dif_neg h101] at h
      cases h

theorem table_prefix_112_114_111_109_105_115 (r : Bytes) (n : NumLit) :
    solWordTable ([112, 114, 111, 109, 105, 115] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h101 : b = 101
    · subst b
      exact table_prefix_112_114_111_109_105_115_101 r n h
    ·
      delta solWordTable solWordTable.match_1 at h
      change (dite (b = 101) (fun _ => _) (fun _ => (.other : WordClass))) = .tok (.num n) at h
      rw [dif_neg h101] at h
      cases h

theorem table_prefix_112_117_98_108_105_99 (r : Bytes) (n : NumLit) :
    solWordTable ([112, 117, 98, 108, 105, 99] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.tok (.kw .public_) : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h

theorem table_prefix_114_101_99_101_105_118 (r : Bytes) (n : NumLit) :
    solWordTable ([114, 101, 99, 101, 105, 118] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h101 : b = 101
    · subst b
      exact table_prefix_114_101_99_101_105_118_101 r n h
    ·
      delta solWordTable solWordTable.match_1 at h
      change (dite (b = 101) (fun _ => _) (fun _ => (.other : WordClass))) = .tok (.num n) at h
      rw [dif_neg h101] at h
      cases h

theorem table_prefix_114_101_102_101_114_101 (r : Bytes) (n : NumLit) :
    solWordTable ([114, 101, 102, 101, 114, 101] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h110 : b = 110
    · subst b
      exact table_prefix_114_101_102_101_114_101_110 r n h
    ·
      delta solWordTable solWordTable.match_1 at h
      change (dite (b = 110) (fun _ => _) (fun _ => (.other : WordClass))) = .tok (.num n) at h
      rw [dif_neg h110] at h
      cases h

theorem table_prefix_114_101_108_111_99_97 (r : Bytes) (n : NumLit) :
    solWordTable ([114, 101, 108, 111, 99, 97] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h116 : b = 116
    · subst b
      exact table_prefix_114_101_108_111_99_97_116 r n h
    ·
      delta solWordTable solWordTable.match_1 at h
      change (dite (b = 116) (fun _ => _) (fun _ => (.other : WordClass))) = .tok (.num n) at h
      rw [dif_neg h116] at h
      cases h

theorem table_prefix_114_101_116_117_114_110 (r : Bytes) (n : NumLit) :
    solWordTable ([114, 101, 116, 117, 114, 110] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.tok (.kw .return_) : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h115 : b = 115
    · subst b
      exact table_prefix_114_101_116_117_114_110_115 r n h
    ·
      delta solWordTable solWordTable.match_1 at h
      change (dite (b = 115) (fun _ => _) (fun _ => (.other : WordClass))) = .tok (.num n) at h
      rw [dif_neg h115] at h
      cases h

theorem table_prefix_115_101_97_108_101_100 (r : Bytes) (n : NumLit) :
    solWordTable ([115, 101, 97, 108, 101, 100] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.reserved : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h

theorem table_prefix_115_101_99_111_110_100 (r : Bytes) (n : NumLit) :
    solWordTable ([115, 101, 99, 111, 110, 100] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h115 : b = 115
    · subst b
      exact table_prefix_115_101_99_111_110_100_115 r n h
    ·
      delta solWordTable solWordTable.match_1 at h
      change (dite (b = 115) (fun _ => _) (fun _ => (.other : WordClass))) = .tok (.num n) at h
      rw [dif_neg h115] at h
      cases h

theorem table_prefix_115_105_122_101_111_102 (r : Bytes) (n : NumLit) :
    solWordTable ([115, 105, 122, 101, 111, 102] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.reserved : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h

theorem table_prefix_115_116_97_116_105_99 (r : Bytes) (n : NumLit) :
    solWordTable ([115, 116, 97, 116, 105, 99] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.reserved : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h

theorem table_prefix_115_116_111_114_97_103 (r : Bytes) (n : NumLit) :
    solWordTable ([115, 116, 111, 114, 97, 103] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h101 : b = 101
    · subst b
      exact table_prefix_115_116_111_114_97_103_101 r n h
    ·
      delta solWordTable solWordTable.match_1 at h
      change (dite (b = 101) (fun _ => _) (fun _ => (.other : WordClass))) = .tok (.num n) at h
      rw [dif_neg h101] at h
      cases h

theorem table_prefix_115_116_114_105_110_103 (r : Bytes) (n : NumLit) :
    solWordTable ([115, 116, 114, 105, 110, 103] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.tok (.elem .string) : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h

theorem table_prefix_115_116_114_117_99_116 (r : Bytes) (n : NumLit) :
    solWordTable ([115, 116, 114, 117, 99, 116] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.tok (.kw .struct) : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h

end Solidity.Frontend.NumericLiteralProofs
