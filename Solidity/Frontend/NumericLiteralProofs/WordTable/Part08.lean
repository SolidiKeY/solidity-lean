import Solidity.Frontend.NumericLiteralProofs.WordTable.Part07

/-! # Generated direct structural word-table proof.
No scanner changes, equation generation, or raised budgets. -/
namespace Solidity.Frontend.NumericLiteralProofs
open Solidity.Frontend.Checked Solidity.Source

theorem table_prefix_115_117_112_112_111_114 (r : Bytes) (n : NumLit) :
    solWordTable ([115, 117, 112, 112, 111, 114] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h116 : b = 116
    · subst b
      exact table_prefix_115_117_112_112_111_114_116 r n h
    ·
      delta solWordTable solWordTable.match_1 at h
      change (dite (b = 116) (fun _ => _) (fun _ => (.other : WordClass))) = .tok (.num n) at h
      rw [dif_neg h116] at h
      cases h

theorem table_prefix_115_119_105_116_99_104 (r : Bytes) (n : NumLit) :
    solWordTable ([115, 119, 105, 116, 99, 104] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.reserved : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h

theorem table_prefix_116_121_112_101_100_101 (r : Bytes) (n : NumLit) :
    solWordTable ([116, 121, 112, 101, 100, 101] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h102 : b = 102
    · subst b
      exact table_prefix_116_121_112_101_100_101_102 r n h
    ·
      delta solWordTable solWordTable.match_1 at h
      change (dite (b = 102) (fun _ => _) (fun _ => (.other : WordClass))) = .tok (.num n) at h
      rw [dif_neg h102] at h
      cases h

theorem table_prefix_116_121_112_101_111_102 (r : Bytes) (n : NumLit) :
    solWordTable ([116, 121, 112, 101, 111, 102] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.reserved : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h

theorem table_prefix_117_110_99_104_101_99 (r : Bytes) (n : NumLit) :
    solWordTable ([117, 110, 99, 104, 101, 99] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h107 : b = 107
    · subst b
      exact table_prefix_117_110_99_104_101_99_107 r n h
    ·
      delta solWordTable solWordTable.match_1 at h
      change (dite (b = 107) (fun _ => _) (fun _ => (.other : WordClass))) = .tok (.num n) at h
      rw [dif_neg h107] at h
      cases h

theorem table_prefix_117_110_105_99_111_100 (r : Bytes) (n : NumLit) :
    solWordTable ([117, 110, 105, 99, 111, 100] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h101 : b = 101
    · subst b
      exact table_prefix_117_110_105_99_111_100_101 r n h
    ·
      delta solWordTable solWordTable.match_1 at h
      change (dite (b = 101) (fun _ => _) (fun _ => (.other : WordClass))) = .tok (.num n) at h
      rw [dif_neg h101] at h
      cases h

theorem table_prefix_118_105_114_116_117_97 (r : Bytes) (n : NumLit) :
    solWordTable ([118, 105, 114, 116, 117, 97] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h108 : b = 108
    · subst b
      exact table_prefix_118_105_114_116_117_97_108 r n h
    ·
      delta solWordTable solWordTable.match_1 at h
      change (dite (b = 108) (fun _ => _) (fun _ => (.other : WordClass))) = .tok (.num n) at h
      rw [dif_neg h108] at h
      cases h

theorem table_prefix_97_98_115_116_114 (r : Bytes) (n : NumLit) :
    solWordTable ([97, 98, 115, 116, 114] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h97 : b = 97
    · subst b
      exact table_prefix_97_98_115_116_114_97 r n h
    ·
      delta solWordTable solWordTable.match_1 at h
      change (dite (b = 97) (fun _ => _) (fun _ => (.other : WordClass))) = .tok (.num n) at h
      rw [dif_neg h97] at h
      cases h

theorem table_prefix_97_100_100_114_101 (r : Bytes) (n : NumLit) :
    solWordTable ([97, 100, 100, 114, 101] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h115 : b = 115
    · subst b
      exact table_prefix_97_100_100_114_101_115 r n h
    ·
      delta solWordTable solWordTable.match_1 at h
      change (dite (b = 115) (fun _ => _) (fun _ => (.other : WordClass))) = .tok (.num n) at h
      rw [dif_neg h115] at h
      cases h

theorem table_prefix_97_102_116_101_114 (r : Bytes) (n : NumLit) :
    solWordTable ([97, 102, 116, 101, 114] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.reserved : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h

theorem table_prefix_97_108_105_97_115 (r : Bytes) (n : NumLit) :
    solWordTable ([97, 108, 105, 97, 115] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.reserved : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h

theorem table_prefix_97_110_111_110_121 (r : Bytes) (n : NumLit) :
    solWordTable ([97, 110, 111, 110, 121] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h109 : b = 109
    · subst b
      exact table_prefix_97_110_111_110_121_109 r n h
    ·
      delta solWordTable solWordTable.match_1 at h
      change (dite (b = 109) (fun _ => _) (fun _ => (.other : WordClass))) = .tok (.num n) at h
      rw [dif_neg h109] at h
      cases h

theorem table_prefix_97_112_112_108_121 (r : Bytes) (n : NumLit) :
    solWordTable ([97, 112, 112, 108, 121] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.reserved : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h

theorem table_prefix_97_115_115_101_109 (r : Bytes) (n : NumLit) :
    solWordTable ([97, 115, 115, 101, 109] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h98 : b = 98
    · subst b
      exact table_prefix_97_115_115_101_109_98 r n h
    ·
      delta solWordTable solWordTable.match_1 at h
      change (dite (b = 98) (fun _ => _) (fun _ => (.other : WordClass))) = .tok (.num n) at h
      rw [dif_neg h98] at h
      cases h

theorem table_prefix_98_114_101_97_107 (r : Bytes) (n : NumLit) :
    solWordTable ([98, 114, 101, 97, 107] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.tok (.kw .break_) : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h

end Solidity.Frontend.NumericLiteralProofs
