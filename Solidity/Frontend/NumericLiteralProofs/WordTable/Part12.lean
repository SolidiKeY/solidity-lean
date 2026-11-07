import Solidity.Frontend.NumericLiteralProofs.WordTable.Part11

/-! # Generated direct structural word-table proof.
No scanner changes, equation generation, or raised budgets. -/
namespace Solidity.Frontend.NumericLiteralProofs
open Solidity.Frontend.Checked Solidity.Source

theorem table_prefix_115_116_97_116_105 (r : Bytes) (n : NumLit) :
    solWordTable ([115, 116, 97, 116, 105] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h99 : b = 99
    · subst b
      exact table_prefix_115_116_97_116_105_99 r n h
    ·
      delta solWordTable solWordTable.match_1 at h
      change (dite (b = 99) (fun _ => _) (fun _ => (.other : WordClass))) = .tok (.num n) at h
      rw [dif_neg h99] at h
      cases h

theorem table_prefix_115_116_111_114_97 (r : Bytes) (n : NumLit) :
    solWordTable ([115, 116, 111, 114, 97] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h103 : b = 103
    · subst b
      exact table_prefix_115_116_111_114_97_103 r n h
    ·
      delta solWordTable solWordTable.match_1 at h
      change (dite (b = 103) (fun _ => _) (fun _ => (.other : WordClass))) = .tok (.num n) at h
      rw [dif_neg h103] at h
      cases h

theorem table_prefix_115_116_114_105_110 (r : Bytes) (n : NumLit) :
    solWordTable ([115, 116, 114, 105, 110] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h103 : b = 103
    · subst b
      exact table_prefix_115_116_114_105_110_103 r n h
    ·
      delta solWordTable solWordTable.match_1 at h
      change (dite (b = 103) (fun _ => _) (fun _ => (.other : WordClass))) = .tok (.num n) at h
      rw [dif_neg h103] at h
      cases h

theorem table_prefix_115_116_114_117_99 (r : Bytes) (n : NumLit) :
    solWordTable ([115, 116, 114, 117, 99] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h116 : b = 116
    · subst b
      exact table_prefix_115_116_114_117_99_116 r n h
    ·
      delta solWordTable solWordTable.match_1 at h
      change (dite (b = 116) (fun _ => _) (fun _ => (.other : WordClass))) = .tok (.num n) at h
      rw [dif_neg h116] at h
      cases h

theorem table_prefix_115_117_112_112_111 (r : Bytes) (n : NumLit) :
    solWordTable ([115, 117, 112, 112, 111] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h114 : b = 114
    · subst b
      exact table_prefix_115_117_112_112_111_114 r n h
    ·
      delta solWordTable solWordTable.match_1 at h
      change (dite (b = 114) (fun _ => _) (fun _ => (.other : WordClass))) = .tok (.num n) at h
      rw [dif_neg h114] at h
      cases h

theorem table_prefix_115_119_105_116_99 (r : Bytes) (n : NumLit) :
    solWordTable ([115, 119, 105, 116, 99] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h104 : b = 104
    · subst b
      exact table_prefix_115_119_105_116_99_104 r n h
    ·
      delta solWordTable solWordTable.match_1 at h
      change (dite (b = 104) (fun _ => _) (fun _ => (.other : WordClass))) = .tok (.num n) at h
      rw [dif_neg h104] at h
      cases h

theorem table_prefix_116_121_112_101_100 (r : Bytes) (n : NumLit) :
    solWordTable ([116, 121, 112, 101, 100] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h101 : b = 101
    · subst b
      exact table_prefix_116_121_112_101_100_101 r n h
    ·
      delta solWordTable solWordTable.match_1 at h
      change (dite (b = 101) (fun _ => _) (fun _ => (.other : WordClass))) = .tok (.num n) at h
      rw [dif_neg h101] at h
      cases h

theorem table_prefix_116_121_112_101_111 (r : Bytes) (n : NumLit) :
    solWordTable ([116, 121, 112, 101, 111] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h102 : b = 102
    · subst b
      exact table_prefix_116_121_112_101_111_102 r n h
    ·
      delta solWordTable solWordTable.match_1 at h
      change (dite (b = 102) (fun _ => _) (fun _ => (.other : WordClass))) = .tok (.num n) at h
      rw [dif_neg h102] at h
      cases h

theorem table_prefix_117_110_99_104_101 (r : Bytes) (n : NumLit) :
    solWordTable ([117, 110, 99, 104, 101] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h99 : b = 99
    · subst b
      exact table_prefix_117_110_99_104_101_99 r n h
    ·
      delta solWordTable solWordTable.match_1 at h
      change (dite (b = 99) (fun _ => _) (fun _ => (.other : WordClass))) = .tok (.num n) at h
      rw [dif_neg h99] at h
      cases h

theorem table_prefix_117_110_105_99_111 (r : Bytes) (n : NumLit) :
    solWordTable ([117, 110, 105, 99, 111] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h100 : b = 100
    · subst b
      exact table_prefix_117_110_105_99_111_100 r n h
    ·
      delta solWordTable solWordTable.match_1 at h
      change (dite (b = 100) (fun _ => _) (fun _ => (.other : WordClass))) = .tok (.num n) at h
      rw [dif_neg h100] at h
      cases h

theorem table_prefix_117_115_105_110_103 (r : Bytes) (n : NumLit) :
    solWordTable ([117, 115, 105, 110, 103] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.tok (.kw .using) : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h

theorem table_prefix_118_105_114_116_117 (r : Bytes) (n : NumLit) :
    solWordTable ([118, 105, 114, 116, 117] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h97 : b = 97
    · subst b
      exact table_prefix_118_105_114_116_117_97 r n h
    ·
      delta solWordTable solWordTable.match_1 at h
      change (dite (b = 97) (fun _ => _) (fun _ => (.other : WordClass))) = .tok (.num n) at h
      rw [dif_neg h97] at h
      cases h

theorem table_prefix_119_101_101_107_115 (r : Bytes) (n : NumLit) :
    solWordTable ([119, 101, 101, 107, 115] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.tok (.denom .weeks) : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h

theorem table_prefix_119_104_105_108_101 (r : Bytes) (n : NumLit) :
    solWordTable ([119, 104, 105, 108, 101] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.tok (.kw .while_) : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h

theorem table_prefix_121_101_97_114_115 (r : Bytes) (n : NumLit) :
    solWordTable ([121, 101, 97, 114, 115] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.tok (.denom .years) : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h

end Solidity.Frontend.NumericLiteralProofs
