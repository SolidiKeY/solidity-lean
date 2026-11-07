import Solidity.Frontend.NumericLiteralProofs.WordTable.Part12

/-! # Generated direct structural word-table proof.
No scanner changes, equation generation, or raised budgets. -/
namespace Solidity.Frontend.NumericLiteralProofs
open Solidity.Frontend.Checked Solidity.Source

theorem table_prefix_97_98_115_116 (r : Bytes) (n : NumLit) :
    solWordTable ([97, 98, 115, 116] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h114 : b = 114
    · subst b
      exact table_prefix_97_98_115_116_114 r n h
    ·
      delta solWordTable solWordTable.match_1 at h
      change (dite (b = 114) (fun _ => _) (fun _ => (.other : WordClass))) = .tok (.num n) at h
      rw [dif_neg h114] at h
      cases h

theorem table_prefix_97_100_100_114 (r : Bytes) (n : NumLit) :
    solWordTable ([97, 100, 100, 114] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h101 : b = 101
    · subst b
      exact table_prefix_97_100_100_114_101 r n h
    ·
      delta solWordTable solWordTable.match_1 at h
      change (dite (b = 101) (fun _ => _) (fun _ => (.other : WordClass))) = .tok (.num n) at h
      rw [dif_neg h101] at h
      cases h

theorem table_prefix_97_102_116_101 (r : Bytes) (n : NumLit) :
    solWordTable ([97, 102, 116, 101] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h114 : b = 114
    · subst b
      exact table_prefix_97_102_116_101_114 r n h
    ·
      delta solWordTable solWordTable.match_1 at h
      change (dite (b = 114) (fun _ => _) (fun _ => (.other : WordClass))) = .tok (.num n) at h
      rw [dif_neg h114] at h
      cases h

theorem table_prefix_97_108_105_97 (r : Bytes) (n : NumLit) :
    solWordTable ([97, 108, 105, 97] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h115 : b = 115
    · subst b
      exact table_prefix_97_108_105_97_115 r n h
    ·
      delta solWordTable solWordTable.match_1 at h
      change (dite (b = 115) (fun _ => _) (fun _ => (.other : WordClass))) = .tok (.num n) at h
      rw [dif_neg h115] at h
      cases h

theorem table_prefix_97_110_111_110 (r : Bytes) (n : NumLit) :
    solWordTable ([97, 110, 111, 110] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h121 : b = 121
    · subst b
      exact table_prefix_97_110_111_110_121 r n h
    ·
      delta solWordTable solWordTable.match_1 at h
      change (dite (b = 121) (fun _ => _) (fun _ => (.other : WordClass))) = .tok (.num n) at h
      rw [dif_neg h121] at h
      cases h

theorem table_prefix_97_112_112_108 (r : Bytes) (n : NumLit) :
    solWordTable ([97, 112, 112, 108] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h121 : b = 121
    · subst b
      exact table_prefix_97_112_112_108_121 r n h
    ·
      delta solWordTable solWordTable.match_1 at h
      change (dite (b = 121) (fun _ => _) (fun _ => (.other : WordClass))) = .tok (.num n) at h
      rw [dif_neg h121] at h
      cases h

theorem table_prefix_97_115_115_101 (r : Bytes) (n : NumLit) :
    solWordTable ([97, 115, 115, 101] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h109 : b = 109
    · subst b
      exact table_prefix_97_115_115_101_109 r n h
    ·
      delta solWordTable solWordTable.match_1 at h
      change (dite (b = 109) (fun _ => _) (fun _ => (.other : WordClass))) = .tok (.num n) at h
      rw [dif_neg h109] at h
      cases h

theorem table_prefix_97_117_116_111 (r : Bytes) (n : NumLit) :
    solWordTable ([97, 117, 116, 111] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.reserved : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h

theorem table_prefix_98_111_111_108 (r : Bytes) (n : NumLit) :
    solWordTable ([98, 111, 111, 108] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.tok (.elem .bool) : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h

theorem table_prefix_98_114_101_97 (r : Bytes) (n : NumLit) :
    solWordTable ([98, 114, 101, 97] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h107 : b = 107
    · subst b
      exact table_prefix_98_114_101_97_107 r n h
    ·
      delta solWordTable solWordTable.match_1 at h
      change (dite (b = 107) (fun _ => _) (fun _ => (.other : WordClass))) = .tok (.num n) at h
      rw [dif_neg h107] at h
      cases h

theorem table_prefix_98_121_116_101 (r : Bytes) (n : NumLit) :
    solWordTable ([98, 121, 116, 101] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.reserved : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h

theorem table_prefix_99_97_108_108 (r : Bytes) (n : NumLit) :
    solWordTable ([99, 97, 108, 108] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h100 : b = 100
    · subst b
      exact table_prefix_99_97_108_108_100 r n h
    ·
      delta solWordTable solWordTable.match_1 at h
      change (dite (b = 100) (fun _ => _) (fun _ => (.other : WordClass))) = .tok (.num n) at h
      rw [dif_neg h100] at h
      cases h

theorem table_prefix_99_97_115_101 (r : Bytes) (n : NumLit) :
    solWordTable ([99, 97, 115, 101] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.reserved : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h

theorem table_prefix_99_97_116_99 (r : Bytes) (n : NumLit) :
    solWordTable ([99, 97, 116, 99] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h104 : b = 104
    · subst b
      exact table_prefix_99_97_116_99_104 r n h
    ·
      delta solWordTable solWordTable.match_1 at h
      change (dite (b = 104) (fun _ => _) (fun _ => (.other : WordClass))) = .tok (.num n) at h
      rw [dif_neg h104] at h
      cases h

theorem table_prefix_99_111_110_115 (r : Bytes) (n : NumLit) :
    solWordTable ([99, 111, 110, 115] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h116 : b = 116
    · subst b
      exact table_prefix_99_111_110_115_116 r n h
    ·
      delta solWordTable solWordTable.match_1 at h
      change (dite (b = 116) (fun _ => _) (fun _ => (.other : WordClass))) = .tok (.num n) at h
      rw [dif_neg h116] at h
      cases h

end Solidity.Frontend.NumericLiteralProofs
