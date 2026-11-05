import Solidity.Frontend.NumericLiteralProofs.WordTable.Part16

/-! # Generated direct structural word-table proof.
No scanner changes, equation generation, or raised budgets. -/
namespace Solidity.Frontend.NumericLiteralProofs
open Solidity.Frontend.Checked Solidity.Source

theorem table_prefix_115_101_97_108 (r : Bytes) (n : NumLit) :
    solWordTable ([115, 101, 97, 108] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h101 : b = 101
    · subst b
      exact table_prefix_115_101_97_108_101 r n h
    ·
      delta solWordTable solWordTable.match_1 at h
      change (dite (b = 101) (fun _ => _) (fun _ => (.other : WordClass))) = .tok (.num n) at h
      rw [dif_neg h101] at h
      cases h

theorem table_prefix_115_101_99_111 (r : Bytes) (n : NumLit) :
    solWordTable ([115, 101, 99, 111] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h110 : b = 110
    · subst b
      exact table_prefix_115_101_99_111_110 r n h
    ·
      delta solWordTable solWordTable.match_1 at h
      change (dite (b = 110) (fun _ => _) (fun _ => (.other : WordClass))) = .tok (.num n) at h
      rw [dif_neg h110] at h
      cases h

theorem table_prefix_115_105_122_101 (r : Bytes) (n : NumLit) :
    solWordTable ([115, 105, 122, 101] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h111 : b = 111
    · subst b
      exact table_prefix_115_105_122_101_111 r n h
    ·
      delta solWordTable solWordTable.match_1 at h
      change (dite (b = 111) (fun _ => _) (fun _ => (.other : WordClass))) = .tok (.num n) at h
      rw [dif_neg h111] at h
      cases h

theorem table_prefix_115_116_97_116 (r : Bytes) (n : NumLit) :
    solWordTable ([115, 116, 97, 116] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h105 : b = 105
    · subst b
      exact table_prefix_115_116_97_116_105 r n h
    ·
      delta solWordTable solWordTable.match_1 at h
      change (dite (b = 105) (fun _ => _) (fun _ => (.other : WordClass))) = .tok (.num n) at h
      rw [dif_neg h105] at h
      cases h

theorem table_prefix_115_116_111_114 (r : Bytes) (n : NumLit) :
    solWordTable ([115, 116, 111, 114] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h97 : b = 97
    · subst b
      exact table_prefix_115_116_111_114_97 r n h
    ·
      delta solWordTable solWordTable.match_1 at h
      change (dite (b = 97) (fun _ => _) (fun _ => (.other : WordClass))) = .tok (.num n) at h
      rw [dif_neg h97] at h
      cases h

theorem table_prefix_115_116_114_105 (r : Bytes) (n : NumLit) :
    solWordTable ([115, 116, 114, 105] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h110 : b = 110
    · subst b
      exact table_prefix_115_116_114_105_110 r n h
    ·
      delta solWordTable solWordTable.match_1 at h
      change (dite (b = 110) (fun _ => _) (fun _ => (.other : WordClass))) = .tok (.num n) at h
      rw [dif_neg h110] at h
      cases h

theorem table_prefix_115_116_114_117 (r : Bytes) (n : NumLit) :
    solWordTable ([115, 116, 114, 117] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h99 : b = 99
    · subst b
      exact table_prefix_115_116_114_117_99 r n h
    ·
      delta solWordTable solWordTable.match_1 at h
      change (dite (b = 99) (fun _ => _) (fun _ => (.other : WordClass))) = .tok (.num n) at h
      rw [dif_neg h99] at h
      cases h

theorem table_prefix_115_117_112_112 (r : Bytes) (n : NumLit) :
    solWordTable ([115, 117, 112, 112] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h111 : b = 111
    · subst b
      exact table_prefix_115_117_112_112_111 r n h
    ·
      delta solWordTable solWordTable.match_1 at h
      change (dite (b = 111) (fun _ => _) (fun _ => (.other : WordClass))) = .tok (.num n) at h
      rw [dif_neg h111] at h
      cases h

theorem table_prefix_115_119_105_116 (r : Bytes) (n : NumLit) :
    solWordTable ([115, 119, 105, 116] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h99 : b = 99
    · subst b
      exact table_prefix_115_119_105_116_99 r n h
    ·
      delta solWordTable solWordTable.match_1 at h
      change (dite (b = 99) (fun _ => _) (fun _ => (.other : WordClass))) = .tok (.num n) at h
      rw [dif_neg h99] at h
      cases h

theorem table_prefix_116_114_117_101 (r : Bytes) (n : NumLit) :
    solWordTable ([116, 114, 117, 101] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.tok (.bool true) : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h

theorem table_prefix_116_121_112_101 (r : Bytes) (n : NumLit) :
    solWordTable ([116, 121, 112, 101] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.tok (.kw .type_) : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h100 : b = 100
    · subst b
      exact table_prefix_116_121_112_101_100 r n h
    ·
      by_cases h111 : b = 111
      · subst b
        exact table_prefix_116_121_112_101_111 r n h
      ·
        delta solWordTable solWordTable.match_1 at h
        change (dite (b = 100) (fun _ => _) (fun _ => (dite (b = 111) (fun _ => _) (fun _ => (.other : WordClass))))) = .tok (.num n) at h
        rw [dif_neg h100, dif_neg h111] at h
        cases h

theorem table_prefix_117_110_99_104 (r : Bytes) (n : NumLit) :
    solWordTable ([117, 110, 99, 104] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h101 : b = 101
    · subst b
      exact table_prefix_117_110_99_104_101 r n h
    ·
      delta solWordTable solWordTable.match_1 at h
      change (dite (b = 101) (fun _ => _) (fun _ => (.other : WordClass))) = .tok (.num n) at h
      rw [dif_neg h101] at h
      cases h

theorem table_prefix_117_110_105_99 (r : Bytes) (n : NumLit) :
    solWordTable ([117, 110, 105, 99] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h111 : b = 111
    · subst b
      exact table_prefix_117_110_105_99_111 r n h
    ·
      delta solWordTable solWordTable.match_1 at h
      change (dite (b = 111) (fun _ => _) (fun _ => (.other : WordClass))) = .tok (.num n) at h
      rw [dif_neg h111] at h
      cases h

theorem table_prefix_117_115_105_110 (r : Bytes) (n : NumLit) :
    solWordTable ([117, 115, 105, 110] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h103 : b = 103
    · subst b
      exact table_prefix_117_115_105_110_103 r n h
    ·
      delta solWordTable solWordTable.match_1 at h
      change (dite (b = 103) (fun _ => _) (fun _ => (.other : WordClass))) = .tok (.num n) at h
      rw [dif_neg h103] at h
      cases h

theorem table_prefix_118_105_101_119 (r : Bytes) (n : NumLit) :
    solWordTable ([118, 105, 101, 119] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.tok (.kw .view) : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h

end Solidity.Frontend.NumericLiteralProofs
