import Solidity.Frontend.Checked.Lexer

/-! # Generated direct structural word-table proof.
No scanner changes, equation generation, or raised budgets. -/
namespace Solidity.Frontend.NumericLiteralProofs
open Solidity.Frontend.Checked Solidity.Source

theorem table_prefix_99_111_110_115_116_114_117_99_116_111_114 (r : Bytes) (n : NumLit) :
    solWordTable ([99, 111, 110, 115, 116, 114, 117, 99, 116, 111, 114] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.tok (.kw .constructor) : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h

theorem table_prefix_114_101_108_111_99_97_116_97_98_108_101 (r : Bytes) (n : NumLit) :
    solWordTable ([114, 101, 108, 111, 99, 97, 116, 97, 98, 108, 101] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.reserved : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h

theorem table_prefix_99_111_110_115_116_114_117_99_116_111 (r : Bytes) (n : NumLit) :
    solWordTable ([99, 111, 110, 115, 116, 114, 117, 99, 116, 111] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h114 : b = 114
    · subst b
      exact table_prefix_99_111_110_115_116_114_117_99_116_111_114 r n h
    ·
      delta solWordTable solWordTable.match_1 at h
      change (dite (b = 114) (fun _ => _) (fun _ => (.other : WordClass))) = .tok (.num n) at h
      rw [dif_neg h114] at h
      cases h

theorem table_prefix_105_109_112_108_101_109_101_110_116_115 (r : Bytes) (n : NumLit) :
    solWordTable ([105, 109, 112, 108, 101, 109, 101, 110, 116, 115] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.reserved : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h

theorem table_prefix_114_101_108_111_99_97_116_97_98_108 (r : Bytes) (n : NumLit) :
    solWordTable ([114, 101, 108, 111, 99, 97, 116, 97, 98, 108] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h101 : b = 101
    · subst b
      exact table_prefix_114_101_108_111_99_97_116_97_98_108_101 r n h
    ·
      delta solWordTable solWordTable.match_1 at h
      change (dite (b = 101) (fun _ => _) (fun _ => (.other : WordClass))) = .tok (.num n) at h
      rw [dif_neg h101] at h
      cases h

theorem table_prefix_97_110_111_110_121_109_111_117_115 (r : Bytes) (n : NumLit) :
    solWordTable ([97, 110, 111, 110, 121, 109, 111, 117, 115] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.tok (.kw .anonymous) : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h

theorem table_prefix_99_111_110_115_116_114_117_99_116 (r : Bytes) (n : NumLit) :
    solWordTable ([99, 111, 110, 115, 116, 114, 117, 99, 116] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h111 : b = 111
    · subst b
      exact table_prefix_99_111_110_115_116_114_117_99_116_111 r n h
    ·
      delta solWordTable solWordTable.match_1 at h
      change (dite (b = 111) (fun _ => _) (fun _ => (.other : WordClass))) = .tok (.num n) at h
      rw [dif_neg h111] at h
      cases h

theorem table_prefix_105_109_109_117_116_97_98_108_101 (r : Bytes) (n : NumLit) :
    solWordTable ([105, 109, 109, 117, 116, 97, 98, 108, 101] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.tok (.kw .immutable) : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h

theorem table_prefix_105_109_112_108_101_109_101_110_116 (r : Bytes) (n : NumLit) :
    solWordTable ([105, 109, 112, 108, 101, 109, 101, 110, 116] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h115 : b = 115
    · subst b
      exact table_prefix_105_109_112_108_101_109_101_110_116_115 r n h
    ·
      delta solWordTable solWordTable.match_1 at h
      change (dite (b = 115) (fun _ => _) (fun _ => (.other : WordClass))) = .tok (.num n) at h
      rw [dif_neg h115] at h
      cases h

theorem table_prefix_105_110_116_101_114_102_97_99_101 (r : Bytes) (n : NumLit) :
    solWordTable ([105, 110, 116, 101, 114, 102, 97, 99, 101] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.tok (.kw .interface) : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h

theorem table_prefix_114_101_102_101_114_101_110_99_101 (r : Bytes) (n : NumLit) :
    solWordTable ([114, 101, 102, 101, 114, 101, 110, 99, 101] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.reserved : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h

theorem table_prefix_114_101_108_111_99_97_116_97_98 (r : Bytes) (n : NumLit) :
    solWordTable ([114, 101, 108, 111, 99, 97, 116, 97, 98] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h108 : b = 108
    · subst b
      exact table_prefix_114_101_108_111_99_97_116_97_98_108 r n h
    ·
      delta solWordTable solWordTable.match_1 at h
      change (dite (b = 108) (fun _ => _) (fun _ => (.other : WordClass))) = .tok (.num n) at h
      rw [dif_neg h108] at h
      cases h

theorem table_prefix_117_110_99_104_101_99_107_101_100 (r : Bytes) (n : NumLit) :
    solWordTable ([117, 110, 99, 104, 101, 99, 107, 101, 100] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.tok (.kw .unchecked) : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h

theorem table_prefix_97_98_115_116_114_97_99_116 (r : Bytes) (n : NumLit) :
    solWordTable ([97, 98, 115, 116, 114, 97, 99, 116] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.tok (.kw .abstract) : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h

theorem table_prefix_97_110_111_110_121_109_111_117 (r : Bytes) (n : NumLit) :
    solWordTable ([97, 110, 111, 110, 121, 109, 111, 117] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h115 : b = 115
    · subst b
      exact table_prefix_97_110_111_110_121_109_111_117_115 r n h
    ·
      delta solWordTable solWordTable.match_1 at h
      change (dite (b = 115) (fun _ => _) (fun _ => (.other : WordClass))) = .tok (.num n) at h
      rw [dif_neg h115] at h
      cases h

end Solidity.Frontend.NumericLiteralProofs
