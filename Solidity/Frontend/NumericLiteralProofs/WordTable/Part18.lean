import Solidity.Frontend.NumericLiteralProofs.WordTable.Part17

/-! # Generated direct structural word-table proof.
No scanner changes, equation generation, or raised budgets. -/
namespace Solidity.Frontend.NumericLiteralProofs
open Solidity.Frontend.Checked Solidity.Source

theorem table_prefix_118_105_114_116 (r : Bytes) (n : NumLit) :
    solWordTable ([118, 105, 114, 116] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h117 : b = 117
    · subst b
      exact table_prefix_118_105_114_116_117 r n h
    ·
      delta solWordTable solWordTable.match_1 at h
      change (dite (b = 117) (fun _ => _) (fun _ => (.other : WordClass))) = .tok (.num n) at h
      rw [dif_neg h117] at h
      cases h

theorem table_prefix_119_101_101_107 (r : Bytes) (n : NumLit) :
    solWordTable ([119, 101, 101, 107] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h115 : b = 115
    · subst b
      exact table_prefix_119_101_101_107_115 r n h
    ·
      delta solWordTable solWordTable.match_1 at h
      change (dite (b = 115) (fun _ => _) (fun _ => (.other : WordClass))) = .tok (.num n) at h
      rw [dif_neg h115] at h
      cases h

theorem table_prefix_119_104_105_108 (r : Bytes) (n : NumLit) :
    solWordTable ([119, 104, 105, 108] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h101 : b = 101
    · subst b
      exact table_prefix_119_104_105_108_101 r n h
    ·
      delta solWordTable solWordTable.match_1 at h
      change (dite (b = 101) (fun _ => _) (fun _ => (.other : WordClass))) = .tok (.num n) at h
      rw [dif_neg h101] at h
      cases h

theorem table_prefix_121_101_97_114 (r : Bytes) (n : NumLit) :
    solWordTable ([121, 101, 97, 114] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h115 : b = 115
    · subst b
      exact table_prefix_121_101_97_114_115 r n h
    ·
      delta solWordTable solWordTable.match_1 at h
      change (dite (b = 115) (fun _ => _) (fun _ => (.other : WordClass))) = .tok (.num n) at h
      rw [dif_neg h115] at h
      cases h

theorem table_prefix_97_98_115 (r : Bytes) (n : NumLit) :
    solWordTable ([97, 98, 115] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h116 : b = 116
    · subst b
      exact table_prefix_97_98_115_116 r n h
    ·
      delta solWordTable solWordTable.match_1 at h
      change (dite (b = 116) (fun _ => _) (fun _ => (.other : WordClass))) = .tok (.num n) at h
      rw [dif_neg h116] at h
      cases h

theorem table_prefix_97_100_100 (r : Bytes) (n : NumLit) :
    solWordTable ([97, 100, 100] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h114 : b = 114
    · subst b
      exact table_prefix_97_100_100_114 r n h
    ·
      delta solWordTable solWordTable.match_1 at h
      change (dite (b = 114) (fun _ => _) (fun _ => (.other : WordClass))) = .tok (.num n) at h
      rw [dif_neg h114] at h
      cases h

theorem table_prefix_97_102_116 (r : Bytes) (n : NumLit) :
    solWordTable ([97, 102, 116] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h101 : b = 101
    · subst b
      exact table_prefix_97_102_116_101 r n h
    ·
      delta solWordTable solWordTable.match_1 at h
      change (dite (b = 101) (fun _ => _) (fun _ => (.other : WordClass))) = .tok (.num n) at h
      rw [dif_neg h101] at h
      cases h

theorem table_prefix_97_108_105 (r : Bytes) (n : NumLit) :
    solWordTable ([97, 108, 105] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h97 : b = 97
    · subst b
      exact table_prefix_97_108_105_97 r n h
    ·
      delta solWordTable solWordTable.match_1 at h
      change (dite (b = 97) (fun _ => _) (fun _ => (.other : WordClass))) = .tok (.num n) at h
      rw [dif_neg h97] at h
      cases h

theorem table_prefix_97_110_111 (r : Bytes) (n : NumLit) :
    solWordTable ([97, 110, 111] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h110 : b = 110
    · subst b
      exact table_prefix_97_110_111_110 r n h
    ·
      delta solWordTable solWordTable.match_1 at h
      change (dite (b = 110) (fun _ => _) (fun _ => (.other : WordClass))) = .tok (.num n) at h
      rw [dif_neg h110] at h
      cases h

theorem table_prefix_97_112_112 (r : Bytes) (n : NumLit) :
    solWordTable ([97, 112, 112] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h108 : b = 108
    · subst b
      exact table_prefix_97_112_112_108 r n h
    ·
      delta solWordTable solWordTable.match_1 at h
      change (dite (b = 108) (fun _ => _) (fun _ => (.other : WordClass))) = .tok (.num n) at h
      rw [dif_neg h108] at h
      cases h

theorem table_prefix_97_115_115 (r : Bytes) (n : NumLit) :
    solWordTable ([97, 115, 115] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h101 : b = 101
    · subst b
      exact table_prefix_97_115_115_101 r n h
    ·
      delta solWordTable solWordTable.match_1 at h
      change (dite (b = 101) (fun _ => _) (fun _ => (.other : WordClass))) = .tok (.num n) at h
      rw [dif_neg h101] at h
      cases h

theorem table_prefix_97_117_116 (r : Bytes) (n : NumLit) :
    solWordTable ([97, 117, 116] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h111 : b = 111
    · subst b
      exact table_prefix_97_117_116_111 r n h
    ·
      delta solWordTable solWordTable.match_1 at h
      change (dite (b = 111) (fun _ => _) (fun _ => (.other : WordClass))) = .tok (.num n) at h
      rw [dif_neg h111] at h
      cases h

theorem table_prefix_98_111_111 (r : Bytes) (n : NumLit) :
    solWordTable ([98, 111, 111] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h108 : b = 108
    · subst b
      exact table_prefix_98_111_111_108 r n h
    ·
      delta solWordTable solWordTable.match_1 at h
      change (dite (b = 108) (fun _ => _) (fun _ => (.other : WordClass))) = .tok (.num n) at h
      rw [dif_neg h108] at h
      cases h

theorem table_prefix_98_114_101 (r : Bytes) (n : NumLit) :
    solWordTable ([98, 114, 101] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h97 : b = 97
    · subst b
      exact table_prefix_98_114_101_97 r n h
    ·
      delta solWordTable solWordTable.match_1 at h
      change (dite (b = 97) (fun _ => _) (fun _ => (.other : WordClass))) = .tok (.num n) at h
      rw [dif_neg h97] at h
      cases h

theorem table_prefix_98_121_116 (r : Bytes) (n : NumLit) :
    solWordTable ([98, 121, 116] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h101 : b = 101
    · subst b
      exact table_prefix_98_121_116_101 r n h
    ·
      delta solWordTable solWordTable.match_1 at h
      change (dite (b = 101) (fun _ => _) (fun _ => (.other : WordClass))) = .tok (.num n) at h
      rw [dif_neg h101] at h
      cases h

end Solidity.Frontend.NumericLiteralProofs
