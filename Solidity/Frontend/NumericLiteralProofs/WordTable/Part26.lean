import Solidity.Frontend.NumericLiteralProofs.WordTable.Part25

/-! # Generated direct structural word-table proof.
No scanner changes, equation generation, or raised budgets. -/
namespace Solidity.Frontend.NumericLiteralProofs
open Solidity.Frontend.Checked Solidity.Source

theorem table_prefix_109_97 (r : Bytes) (n : NumLit) :
    solWordTable ([109, 97] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h112 : b = 112
    · subst b
      exact table_prefix_109_97_112 r n h
    ·
      by_cases h99 : b = 99
      · subst b
        exact table_prefix_109_97_99 r n h
      ·
        by_cases h116 : b = 116
        · subst b
          exact table_prefix_109_97_116 r n h
        ·
          delta solWordTable solWordTable.match_1 at h
          change (dite (b = 112) (fun _ => _) (fun _ => (dite (b = 99) (fun _ => _) (fun _ => (dite (b = 116) (fun _ => _) (fun _ => (.other : WordClass))))))) = .tok (.num n) at h
          rw [dif_neg h112, dif_neg h99, dif_neg h116] at h
          cases h

theorem table_prefix_109_101 (r : Bytes) (n : NumLit) :
    solWordTable ([109, 101] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h109 : b = 109
    · subst b
      exact table_prefix_109_101_109 r n h
    ·
      delta solWordTable solWordTable.match_1 at h
      change (dite (b = 109) (fun _ => _) (fun _ => (.other : WordClass))) = .tok (.num n) at h
      rw [dif_neg h109] at h
      cases h

theorem table_prefix_109_105 (r : Bytes) (n : NumLit) :
    solWordTable ([109, 105] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h110 : b = 110
    · subst b
      exact table_prefix_109_105_110 r n h
    ·
      delta solWordTable solWordTable.match_1 at h
      change (dite (b = 110) (fun _ => _) (fun _ => (.other : WordClass))) = .tok (.num n) at h
      rw [dif_neg h110] at h
      cases h

theorem table_prefix_109_111 (r : Bytes) (n : NumLit) :
    solWordTable ([109, 111] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h100 : b = 100
    · subst b
      exact table_prefix_109_111_100 r n h
    ·
      delta solWordTable solWordTable.match_1 at h
      change (dite (b = 100) (fun _ => _) (fun _ => (.other : WordClass))) = .tok (.num n) at h
      rw [dif_neg h100] at h
      cases h

theorem table_prefix_109_117 (r : Bytes) (n : NumLit) :
    solWordTable ([109, 117] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h116 : b = 116
    · subst b
      exact table_prefix_109_117_116 r n h
    ·
      delta solWordTable solWordTable.match_1 at h
      change (dite (b = 116) (fun _ => _) (fun _ => (.other : WordClass))) = .tok (.num n) at h
      rw [dif_neg h116] at h
      cases h

theorem table_prefix_110_101 (r : Bytes) (n : NumLit) :
    solWordTable ([110, 101] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h119 : b = 119
    · subst b
      exact table_prefix_110_101_119 r n h
    ·
      delta solWordTable solWordTable.match_1 at h
      change (dite (b = 119) (fun _ => _) (fun _ => (.other : WordClass))) = .tok (.num n) at h
      rw [dif_neg h119] at h
      cases h

theorem table_prefix_110_117 (r : Bytes) (n : NumLit) :
    solWordTable ([110, 117] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h108 : b = 108
    · subst b
      exact table_prefix_110_117_108 r n h
    ·
      delta solWordTable solWordTable.match_1 at h
      change (dite (b = 108) (fun _ => _) (fun _ => (.other : WordClass))) = .tok (.num n) at h
      rw [dif_neg h108] at h
      cases h

theorem table_prefix_111_102 (r : Bytes) (n : NumLit) :
    solWordTable ([111, 102] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.reserved : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h

theorem table_prefix_111_118 (r : Bytes) (n : NumLit) :
    solWordTable ([111, 118] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h101 : b = 101
    · subst b
      exact table_prefix_111_118_101 r n h
    ·
      delta solWordTable solWordTable.match_1 at h
      change (dite (b = 101) (fun _ => _) (fun _ => (.other : WordClass))) = .tok (.num n) at h
      rw [dif_neg h101] at h
      cases h

theorem table_prefix_112_97 (r : Bytes) (n : NumLit) :
    solWordTable ([112, 97] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h121 : b = 121
    · subst b
      exact table_prefix_112_97_121 r n h
    ·
      by_cases h114 : b = 114
      · subst b
        exact table_prefix_112_97_114 r n h
      ·
        delta solWordTable solWordTable.match_1 at h
        change (dite (b = 121) (fun _ => _) (fun _ => (dite (b = 114) (fun _ => _) (fun _ => (.other : WordClass))))) = .tok (.num n) at h
        rw [dif_neg h121, dif_neg h114] at h
        cases h

theorem table_prefix_112_114 (r : Bytes) (n : NumLit) :
    solWordTable ([112, 114] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h97 : b = 97
    · subst b
      exact table_prefix_112_114_97 r n h
    ·
      by_cases h105 : b = 105
      · subst b
        exact table_prefix_112_114_105 r n h
      ·
        by_cases h111 : b = 111
        · subst b
          exact table_prefix_112_114_111 r n h
        ·
          delta solWordTable solWordTable.match_1 at h
          change (dite (b = 97) (fun _ => _) (fun _ => (dite (b = 105) (fun _ => _) (fun _ => (dite (b = 111) (fun _ => _) (fun _ => (.other : WordClass))))))) = .tok (.num n) at h
          rw [dif_neg h97, dif_neg h105, dif_neg h111] at h
          cases h

theorem table_prefix_112_117 (r : Bytes) (n : NumLit) :
    solWordTable ([112, 117] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h98 : b = 98
    · subst b
      exact table_prefix_112_117_98 r n h
    ·
      by_cases h114 : b = 114
      · subst b
        exact table_prefix_112_117_114 r n h
      ·
        delta solWordTable solWordTable.match_1 at h
        change (dite (b = 98) (fun _ => _) (fun _ => (dite (b = 114) (fun _ => _) (fun _ => (.other : WordClass))))) = .tok (.num n) at h
        rw [dif_neg h98, dif_neg h114] at h
        cases h

theorem table_prefix_114_101 (r : Bytes) (n : NumLit) :
    solWordTable ([114, 101] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h99 : b = 99
    · subst b
      exact table_prefix_114_101_99 r n h
    ·
      by_cases h116 : b = 116
      · subst b
        exact table_prefix_114_101_116 r n h
      ·
        by_cases h102 : b = 102
        · subst b
          exact table_prefix_114_101_102 r n h
        ·
          by_cases h108 : b = 108
          · subst b
            exact table_prefix_114_101_108 r n h
          ·
            delta solWordTable solWordTable.match_1 at h
            change (dite (b = 99) (fun _ => _) (fun _ => (dite (b = 116) (fun _ => _) (fun _ => (dite (b = 102) (fun _ => _) (fun _ => (dite (b = 108) (fun _ => _) (fun _ => (.other : WordClass))))))))) = .tok (.num n) at h
            rw [dif_neg h99, dif_neg h116, dif_neg h102, dif_neg h108] at h
            cases h

theorem table_prefix_115_101 (r : Bytes) (n : NumLit) :
    solWordTable ([115, 101] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h99 : b = 99
    · subst b
      exact table_prefix_115_101_99 r n h
    ·
      by_cases h97 : b = 97
      · subst b
        exact table_prefix_115_101_97 r n h
      ·
        delta solWordTable solWordTable.match_1 at h
        change (dite (b = 99) (fun _ => _) (fun _ => (dite (b = 97) (fun _ => _) (fun _ => (.other : WordClass))))) = .tok (.num n) at h
        rw [dif_neg h99, dif_neg h97] at h
        cases h

theorem table_prefix_115_105 (r : Bytes) (n : NumLit) :
    solWordTable ([115, 105] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h122 : b = 122
    · subst b
      exact table_prefix_115_105_122 r n h
    ·
      delta solWordTable solWordTable.match_1 at h
      change (dite (b = 122) (fun _ => _) (fun _ => (.other : WordClass))) = .tok (.num n) at h
      rw [dif_neg h122] at h
      cases h

end Solidity.Frontend.NumericLiteralProofs
