import Solidity.Frontend.NumericLiteralProofs.WordTable.Part09

/-! # Generated direct structural word-table proof.
No scanner changes, equation generation, or raised budgets. -/
namespace Solidity.Frontend.NumericLiteralProofs
open Solidity.Frontend.Checked Solidity.Source

theorem table_prefix_102_117_110_99_116 (r : Bytes) (n : NumLit) :
    solWordTable ([102, 117, 110, 99, 116] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h105 : b = 105
    · subst b
      exact table_prefix_102_117_110_99_116_105 r n h
    ·
      delta solWordTable solWordTable.match_1 at h
      change (dite (b = 105) (fun _ => _) (fun _ => (.other : WordClass))) = .tok (.num n) at h
      rw [dif_neg h105] at h
      cases h

theorem table_prefix_104_111_117_114_115 (r : Bytes) (n : NumLit) :
    solWordTable ([104, 111, 117, 114, 115] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.tok (.denom .hours) : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h

theorem table_prefix_105_109_109_117_116 (r : Bytes) (n : NumLit) :
    solWordTable ([105, 109, 109, 117, 116] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h97 : b = 97
    · subst b
      exact table_prefix_105_109_109_117_116_97 r n h
    ·
      delta solWordTable solWordTable.match_1 at h
      change (dite (b = 97) (fun _ => _) (fun _ => (.other : WordClass))) = .tok (.num n) at h
      rw [dif_neg h97] at h
      cases h

theorem table_prefix_105_109_112_108_101 (r : Bytes) (n : NumLit) :
    solWordTable ([105, 109, 112, 108, 101] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h109 : b = 109
    · subst b
      exact table_prefix_105_109_112_108_101_109 r n h
    ·
      delta solWordTable solWordTable.match_1 at h
      change (dite (b = 109) (fun _ => _) (fun _ => (.other : WordClass))) = .tok (.num n) at h
      rw [dif_neg h109] at h
      cases h

theorem table_prefix_105_109_112_111_114 (r : Bytes) (n : NumLit) :
    solWordTable ([105, 109, 112, 111, 114] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h116 : b = 116
    · subst b
      exact table_prefix_105_109_112_111_114_116 r n h
    ·
      delta solWordTable solWordTable.match_1 at h
      change (dite (b = 116) (fun _ => _) (fun _ => (.other : WordClass))) = .tok (.num n) at h
      rw [dif_neg h116] at h
      cases h

theorem table_prefix_105_110_100_101_120 (r : Bytes) (n : NumLit) :
    solWordTable ([105, 110, 100, 101, 120] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h101 : b = 101
    · subst b
      exact table_prefix_105_110_100_101_120_101 r n h
    ·
      delta solWordTable solWordTable.match_1 at h
      change (dite (b = 101) (fun _ => _) (fun _ => (.other : WordClass))) = .tok (.num n) at h
      rw [dif_neg h101] at h
      cases h

theorem table_prefix_105_110_108_105_110 (r : Bytes) (n : NumLit) :
    solWordTable ([105, 110, 108, 105, 110] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h101 : b = 101
    · subst b
      exact table_prefix_105_110_108_105_110_101 r n h
    ·
      delta solWordTable solWordTable.match_1 at h
      change (dite (b = 101) (fun _ => _) (fun _ => (.other : WordClass))) = .tok (.num n) at h
      rw [dif_neg h101] at h
      cases h

theorem table_prefix_105_110_116_101_114 (r : Bytes) (n : NumLit) :
    solWordTable ([105, 110, 116, 101, 114] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h102 : b = 102
    · subst b
      exact table_prefix_105_110_116_101_114_102 r n h
    ·
      by_cases h110 : b = 110
      · subst b
        exact table_prefix_105_110_116_101_114_110 r n h
      ·
        delta solWordTable solWordTable.match_1 at h
        change (dite (b = 102) (fun _ => _) (fun _ => (dite (b = 110) (fun _ => _) (fun _ => (.other : WordClass))))) = .tok (.num n) at h
        rw [dif_neg h102, dif_neg h110] at h
        cases h

theorem table_prefix_108_105_98_114_97 (r : Bytes) (n : NumLit) :
    solWordTable ([108, 105, 98, 114, 97] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h114 : b = 114
    · subst b
      exact table_prefix_108_105_98_114_97_114 r n h
    ·
      delta solWordTable solWordTable.match_1 at h
      change (dite (b = 114) (fun _ => _) (fun _ => (.other : WordClass))) = .tok (.num n) at h
      rw [dif_neg h114] at h
      cases h

theorem table_prefix_109_97_99_114_111 (r : Bytes) (n : NumLit) :
    solWordTable ([109, 97, 99, 114, 111] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.reserved : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h

theorem table_prefix_109_97_112_112_105 (r : Bytes) (n : NumLit) :
    solWordTable ([109, 97, 112, 112, 105] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h110 : b = 110
    · subst b
      exact table_prefix_109_97_112_112_105_110 r n h
    ·
      delta solWordTable solWordTable.match_1 at h
      change (dite (b = 110) (fun _ => _) (fun _ => (.other : WordClass))) = .tok (.num n) at h
      rw [dif_neg h110] at h
      cases h

theorem table_prefix_109_97_116_99_104 (r : Bytes) (n : NumLit) :
    solWordTable ([109, 97, 116, 99, 104] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.reserved : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h

theorem table_prefix_109_101_109_111_114 (r : Bytes) (n : NumLit) :
    solWordTable ([109, 101, 109, 111, 114] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h121 : b = 121
    · subst b
      exact table_prefix_109_101_109_111_114_121 r n h
    ·
      delta solWordTable solWordTable.match_1 at h
      change (dite (b = 121) (fun _ => _) (fun _ => (.other : WordClass))) = .tok (.num n) at h
      rw [dif_neg h121] at h
      cases h

theorem table_prefix_109_105_110_117_116 (r : Bytes) (n : NumLit) :
    solWordTable ([109, 105, 110, 117, 116] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h101 : b = 101
    · subst b
      exact table_prefix_109_105_110_117_116_101 r n h
    ·
      delta solWordTable solWordTable.match_1 at h
      change (dite (b = 101) (fun _ => _) (fun _ => (.other : WordClass))) = .tok (.num n) at h
      rw [dif_neg h101] at h
      cases h

theorem table_prefix_109_111_100_105_102 (r : Bytes) (n : NumLit) :
    solWordTable ([109, 111, 100, 105, 102] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h105 : b = 105
    · subst b
      exact table_prefix_109_111_100_105_102_105 r n h
    ·
      delta solWordTable solWordTable.match_1 at h
      change (dite (b = 105) (fun _ => _) (fun _ => (.other : WordClass))) = .tok (.num n) at h
      rw [dif_neg h105] at h
      cases h

end Solidity.Frontend.NumericLiteralProofs
