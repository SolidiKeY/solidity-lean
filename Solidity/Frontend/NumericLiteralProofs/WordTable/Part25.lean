import Solidity.Frontend.NumericLiteralProofs.WordTable.Part24

/-! # Generated direct structural word-table proof.
No scanner changes, equation generation, or raised budgets. -/
namespace Solidity.Frontend.NumericLiteralProofs
open Solidity.Frontend.Checked Solidity.Source

theorem table_prefix_101_118 (r : Bytes) (n : NumLit) :
    solWordTable ([101, 118] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h101 : b = 101
    · subst b
      exact table_prefix_101_118_101 r n h
    ·
      delta solWordTable solWordTable.match_1 at h
      change (dite (b = 101) (fun _ => _) (fun _ => (.other : WordClass))) = .tok (.num n) at h
      rw [dif_neg h101] at h
      cases h

theorem table_prefix_101_120 (r : Bytes) (n : NumLit) :
    solWordTable ([101, 120] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h116 : b = 116
    · subst b
      exact table_prefix_101_120_116 r n h
    ·
      delta solWordTable solWordTable.match_1 at h
      change (dite (b = 116) (fun _ => _) (fun _ => (.other : WordClass))) = .tok (.num n) at h
      rw [dif_neg h116] at h
      cases h

theorem table_prefix_102_97 (r : Bytes) (n : NumLit) :
    solWordTable ([102, 97] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h108 : b = 108
    · subst b
      exact table_prefix_102_97_108 r n h
    ·
      delta solWordTable solWordTable.match_1 at h
      change (dite (b = 108) (fun _ => _) (fun _ => (.other : WordClass))) = .tok (.num n) at h
      rw [dif_neg h108] at h
      cases h

theorem table_prefix_102_105 (r : Bytes) (n : NumLit) :
    solWordTable ([102, 105] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h110 : b = 110
    · subst b
      exact table_prefix_102_105_110 r n h
    ·
      delta solWordTable solWordTable.match_1 at h
      change (dite (b = 110) (fun _ => _) (fun _ => (.other : WordClass))) = .tok (.num n) at h
      rw [dif_neg h110] at h
      cases h

theorem table_prefix_102_111 (r : Bytes) (n : NumLit) :
    solWordTable ([102, 111] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h114 : b = 114
    · subst b
      exact table_prefix_102_111_114 r n h
    ·
      delta solWordTable solWordTable.match_1 at h
      change (dite (b = 114) (fun _ => _) (fun _ => (.other : WordClass))) = .tok (.num n) at h
      rw [dif_neg h114] at h
      cases h

theorem table_prefix_102_117 (r : Bytes) (n : NumLit) :
    solWordTable ([102, 117] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h110 : b = 110
    · subst b
      exact table_prefix_102_117_110 r n h
    ·
      delta solWordTable solWordTable.match_1 at h
      change (dite (b = 110) (fun _ => _) (fun _ => (.other : WordClass))) = .tok (.num n) at h
      rw [dif_neg h110] at h
      cases h

theorem table_prefix_103_119 (r : Bytes) (n : NumLit) :
    solWordTable ([103, 119] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h101 : b = 101
    · subst b
      exact table_prefix_103_119_101 r n h
    ·
      delta solWordTable solWordTable.match_1 at h
      change (dite (b = 101) (fun _ => _) (fun _ => (.other : WordClass))) = .tok (.num n) at h
      rw [dif_neg h101] at h
      cases h

theorem table_prefix_104_101 (r : Bytes) (n : NumLit) :
    solWordTable ([104, 101] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h120 : b = 120
    · subst b
      exact table_prefix_104_101_120 r n h
    ·
      delta solWordTable solWordTable.match_1 at h
      change (dite (b = 120) (fun _ => _) (fun _ => (.other : WordClass))) = .tok (.num n) at h
      rw [dif_neg h120] at h
      cases h

theorem table_prefix_104_111 (r : Bytes) (n : NumLit) :
    solWordTable ([104, 111] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h117 : b = 117
    · subst b
      exact table_prefix_104_111_117 r n h
    ·
      delta solWordTable solWordTable.match_1 at h
      change (dite (b = 117) (fun _ => _) (fun _ => (.other : WordClass))) = .tok (.num n) at h
      rw [dif_neg h117] at h
      cases h

theorem table_prefix_105_102 (r : Bytes) (n : NumLit) :
    solWordTable ([105, 102] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.tok (.kw .if_) : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h

theorem table_prefix_105_109 (r : Bytes) (n : NumLit) :
    solWordTable ([105, 109] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h109 : b = 109
    · subst b
      exact table_prefix_105_109_109 r n h
    ·
      by_cases h112 : b = 112
      · subst b
        exact table_prefix_105_109_112 r n h
      ·
        delta solWordTable solWordTable.match_1 at h
        change (dite (b = 109) (fun _ => _) (fun _ => (dite (b = 112) (fun _ => _) (fun _ => (.other : WordClass))))) = .tok (.num n) at h
        rw [dif_neg h109, dif_neg h112] at h
        cases h

theorem table_prefix_105_110 (r : Bytes) (n : NumLit) :
    solWordTable ([105, 110] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.reserved : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h100 : b = 100
    · subst b
      exact table_prefix_105_110_100 r n h
    ·
      by_cases h116 : b = 116
      · subst b
        exact table_prefix_105_110_116 r n h
      ·
        by_cases h108 : b = 108
        · subst b
          exact table_prefix_105_110_108 r n h
        ·
          delta solWordTable solWordTable.match_1 at h
          change (dite (b = 100) (fun _ => _) (fun _ => (dite (b = 116) (fun _ => _) (fun _ => (dite (b = 108) (fun _ => _) (fun _ => (.other : WordClass))))))) = .tok (.num n) at h
          rw [dif_neg h100, dif_neg h116, dif_neg h108] at h
          cases h

theorem table_prefix_105_115 (r : Bytes) (n : NumLit) :
    solWordTable ([105, 115] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.tok (.kw .is) : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h

theorem table_prefix_108_101 (r : Bytes) (n : NumLit) :
    solWordTable ([108, 101] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h116 : b = 116
    · subst b
      exact table_prefix_108_101_116 r n h
    ·
      delta solWordTable solWordTable.match_1 at h
      change (dite (b = 116) (fun _ => _) (fun _ => (.other : WordClass))) = .tok (.num n) at h
      rw [dif_neg h116] at h
      cases h

theorem table_prefix_108_105 (r : Bytes) (n : NumLit) :
    solWordTable ([108, 105] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h98 : b = 98
    · subst b
      exact table_prefix_108_105_98 r n h
    ·
      delta solWordTable solWordTable.match_1 at h
      change (dite (b = 98) (fun _ => _) (fun _ => (.other : WordClass))) = .tok (.num n) at h
      rw [dif_neg h98] at h
      cases h

end Solidity.Frontend.NumericLiteralProofs
