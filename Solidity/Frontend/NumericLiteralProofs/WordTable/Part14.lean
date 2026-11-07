import Solidity.Frontend.NumericLiteralProofs.WordTable.Part13

/-! # Generated direct structural word-table proof.
No scanner changes, equation generation, or raised budgets. -/
namespace Solidity.Frontend.NumericLiteralProofs
open Solidity.Frontend.Checked Solidity.Source

theorem table_prefix_99_111_110_116 (r : Bytes) (n : NumLit) :
    solWordTable ([99, 111, 110, 116] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h105 : b = 105
    · subst b
      exact table_prefix_99_111_110_116_105 r n h
    ·
      by_cases h114 : b = 114
      · subst b
        exact table_prefix_99_111_110_116_114 r n h
      ·
        delta solWordTable solWordTable.match_1 at h
        change (dite (b = 105) (fun _ => _) (fun _ => (dite (b = 114) (fun _ => _) (fun _ => (.other : WordClass))))) = .tok (.num n) at h
        rw [dif_neg h105, dif_neg h114] at h
        cases h

theorem table_prefix_99_111_112_121 (r : Bytes) (n : NumLit) :
    solWordTable ([99, 111, 112, 121] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h111 : b = 111
    · subst b
      exact table_prefix_99_111_112_121_111 r n h
    ·
      delta solWordTable solWordTable.match_1 at h
      change (dite (b = 111) (fun _ => _) (fun _ => (.other : WordClass))) = .tok (.num n) at h
      rw [dif_neg h111] at h
      cases h

theorem table_prefix_100_97_121_115 (r : Bytes) (n : NumLit) :
    solWordTable ([100, 97, 121, 115] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.tok (.denom .days) : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h

theorem table_prefix_100_101_102_97 (r : Bytes) (n : NumLit) :
    solWordTable ([100, 101, 102, 97] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h117 : b = 117
    · subst b
      exact table_prefix_100_101_102_97_117 r n h
    ·
      delta solWordTable solWordTable.match_1 at h
      change (dite (b = 117) (fun _ => _) (fun _ => (.other : WordClass))) = .tok (.num n) at h
      rw [dif_neg h117] at h
      cases h

theorem table_prefix_100_101_102_105 (r : Bytes) (n : NumLit) :
    solWordTable ([100, 101, 102, 105] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h110 : b = 110
    · subst b
      exact table_prefix_100_101_102_105_110 r n h
    ·
      delta solWordTable solWordTable.match_1 at h
      change (dite (b = 110) (fun _ => _) (fun _ => (.other : WordClass))) = .tok (.num n) at h
      rw [dif_neg h110] at h
      cases h

theorem table_prefix_100_101_108_101 (r : Bytes) (n : NumLit) :
    solWordTable ([100, 101, 108, 101] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h116 : b = 116
    · subst b
      exact table_prefix_100_101_108_101_116 r n h
    ·
      delta solWordTable solWordTable.match_1 at h
      change (dite (b = 116) (fun _ => _) (fun _ => (.other : WordClass))) = .tok (.num n) at h
      rw [dif_neg h116] at h
      cases h

theorem table_prefix_101_108_115_101 (r : Bytes) (n : NumLit) :
    solWordTable ([101, 108, 115, 101] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.tok (.kw .else_) : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h

theorem table_prefix_101_109_105_116 (r : Bytes) (n : NumLit) :
    solWordTable ([101, 109, 105, 116] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.tok (.kw .emit) : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h

theorem table_prefix_101_110_117_109 (r : Bytes) (n : NumLit) :
    solWordTable ([101, 110, 117, 109] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.tok (.kw .enum) : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h

theorem table_prefix_101_116_104_101 (r : Bytes) (n : NumLit) :
    solWordTable ([101, 116, 104, 101] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h114 : b = 114
    · subst b
      exact table_prefix_101_116_104_101_114 r n h
    ·
      delta solWordTable solWordTable.match_1 at h
      change (dite (b = 114) (fun _ => _) (fun _ => (.other : WordClass))) = .tok (.num n) at h
      rw [dif_neg h114] at h
      cases h

theorem table_prefix_101_118_101_110 (r : Bytes) (n : NumLit) :
    solWordTable ([101, 118, 101, 110] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h116 : b = 116
    · subst b
      exact table_prefix_101_118_101_110_116 r n h
    ·
      delta solWordTable solWordTable.match_1 at h
      change (dite (b = 116) (fun _ => _) (fun _ => (.other : WordClass))) = .tok (.num n) at h
      rw [dif_neg h116] at h
      cases h

theorem table_prefix_101_120_116_101 (r : Bytes) (n : NumLit) :
    solWordTable ([101, 120, 116, 101] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h114 : b = 114
    · subst b
      exact table_prefix_101_120_116_101_114 r n h
    ·
      delta solWordTable solWordTable.match_1 at h
      change (dite (b = 114) (fun _ => _) (fun _ => (.other : WordClass))) = .tok (.num n) at h
      rw [dif_neg h114] at h
      cases h

theorem table_prefix_102_97_108_108 (r : Bytes) (n : NumLit) :
    solWordTable ([102, 97, 108, 108] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h98 : b = 98
    · subst b
      exact table_prefix_102_97_108_108_98 r n h
    ·
      delta solWordTable solWordTable.match_1 at h
      change (dite (b = 98) (fun _ => _) (fun _ => (.other : WordClass))) = .tok (.num n) at h
      rw [dif_neg h98] at h
      cases h

theorem table_prefix_102_97_108_115 (r : Bytes) (n : NumLit) :
    solWordTable ([102, 97, 108, 115] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h101 : b = 101
    · subst b
      exact table_prefix_102_97_108_115_101 r n h
    ·
      delta solWordTable solWordTable.match_1 at h
      change (dite (b = 101) (fun _ => _) (fun _ => (.other : WordClass))) = .tok (.num n) at h
      rw [dif_neg h101] at h
      cases h

theorem table_prefix_102_105_110_97 (r : Bytes) (n : NumLit) :
    solWordTable ([102, 105, 110, 97] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h108 : b = 108
    · subst b
      exact table_prefix_102_105_110_97_108 r n h
    ·
      delta solWordTable solWordTable.match_1 at h
      change (dite (b = 108) (fun _ => _) (fun _ => (.other : WordClass))) = .tok (.num n) at h
      rw [dif_neg h108] at h
      cases h

end Solidity.Frontend.NumericLiteralProofs
