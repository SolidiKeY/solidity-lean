import Solidity.Frontend.NumericLiteralProofs.WordTable.Part27

/-! # Generated direct structural word-table proof.
No scanner changes, equation generation, or raised budgets. -/
namespace Solidity.Frontend.NumericLiteralProofs
open Solidity.Frontend.Checked Solidity.Source

theorem table_prefix_100 (r : Bytes) (n : NumLit) :
    solWordTable ([100] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h101 : b = 101
    · subst b
      exact table_prefix_100_101 r n h
    ·
      by_cases h111 : b = 111
      · subst b
        exact table_prefix_100_111 r n h
      ·
        by_cases h97 : b = 97
        · subst b
          exact table_prefix_100_97 r n h
        ·
          delta solWordTable solWordTable.match_1 at h
          change (dite (b = 101) (fun _ => _) (fun _ => (dite (b = 111) (fun _ => _) (fun _ => (dite (b = 97) (fun _ => _) (fun _ => (.other : WordClass))))))) = .tok (.num n) at h
          rw [dif_neg h101, dif_neg h111, dif_neg h97] at h
          cases h

theorem table_prefix_101 (r : Bytes) (n : NumLit) :
    solWordTable ([101] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h108 : b = 108
    · subst b
      exact table_prefix_101_108 r n h
    ·
      by_cases h109 : b = 109
      · subst b
        exact table_prefix_101_109 r n h
      ·
        by_cases h110 : b = 110
        · subst b
          exact table_prefix_101_110 r n h
        ·
          by_cases h118 : b = 118
          · subst b
            exact table_prefix_101_118 r n h
          ·
            by_cases h120 : b = 120
            · subst b
              exact table_prefix_101_120 r n h
            ·
              by_cases h116 : b = 116
              · subst b
                exact table_prefix_101_116 r n h
              ·
                delta solWordTable solWordTable.match_1 at h
                change (dite (b = 108) (fun _ => _) (fun _ => (dite (b = 109) (fun _ => _) (fun _ => (dite (b = 110) (fun _ => _) (fun _ => (dite (b = 118) (fun _ => _) (fun _ => (dite (b = 120) (fun _ => _) (fun _ => (dite (b = 116) (fun _ => _) (fun _ => (.other : WordClass))))))))))))) = .tok (.num n) at h
                rw [dif_neg h108, dif_neg h109, dif_neg h110, dif_neg h118, dif_neg h120, dif_neg h116] at h
                cases h

theorem table_prefix_102 (r : Bytes) (n : NumLit) :
    solWordTable ([102] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h97 : b = 97
    · subst b
      exact table_prefix_102_97 r n h
    ·
      by_cases h111 : b = 111
      · subst b
        exact table_prefix_102_111 r n h
      ·
        by_cases h117 : b = 117
        · subst b
          exact table_prefix_102_117 r n h
        ·
          by_cases h105 : b = 105
          · subst b
            exact table_prefix_102_105 r n h
          ·
            delta solWordTable solWordTable.match_1 at h
            change (dite (b = 97) (fun _ => _) (fun _ => (dite (b = 111) (fun _ => _) (fun _ => (dite (b = 117) (fun _ => _) (fun _ => (dite (b = 105) (fun _ => _) (fun _ => (.other : WordClass))))))))) = .tok (.num n) at h
            rw [dif_neg h97, dif_neg h111, dif_neg h117, dif_neg h105] at h
            cases h

theorem table_prefix_103 (r : Bytes) (n : NumLit) :
    solWordTable ([103] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h119 : b = 119
    · subst b
      exact table_prefix_103_119 r n h
    ·
      delta solWordTable solWordTable.match_1 at h
      change (dite (b = 119) (fun _ => _) (fun _ => (.other : WordClass))) = .tok (.num n) at h
      rw [dif_neg h119] at h
      cases h

theorem table_prefix_104 (r : Bytes) (n : NumLit) :
    solWordTable ([104] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h101 : b = 101
    · subst b
      exact table_prefix_104_101 r n h
    ·
      by_cases h111 : b = 111
      · subst b
        exact table_prefix_104_111 r n h
      ·
        delta solWordTable solWordTable.match_1 at h
        change (dite (b = 101) (fun _ => _) (fun _ => (dite (b = 111) (fun _ => _) (fun _ => (.other : WordClass))))) = .tok (.num n) at h
        rw [dif_neg h101, dif_neg h111] at h
        cases h

theorem table_prefix_105 (r : Bytes) (n : NumLit) :
    solWordTable ([105] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h102 : b = 102
    · subst b
      exact table_prefix_105_102 r n h
    ·
      by_cases h109 : b = 109
      · subst b
        exact table_prefix_105_109 r n h
      ·
        by_cases h110 : b = 110
        · subst b
          exact table_prefix_105_110 r n h
        ·
          by_cases h115 : b = 115
          · subst b
            exact table_prefix_105_115 r n h
          ·
            delta solWordTable solWordTable.match_1 at h
            change (dite (b = 102) (fun _ => _) (fun _ => (dite (b = 109) (fun _ => _) (fun _ => (dite (b = 110) (fun _ => _) (fun _ => (dite (b = 115) (fun _ => _) (fun _ => (.other : WordClass))))))))) = .tok (.num n) at h
            rw [dif_neg h102, dif_neg h109, dif_neg h110, dif_neg h115] at h
            cases h

theorem table_prefix_108 (r : Bytes) (n : NumLit) :
    solWordTable ([108] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h105 : b = 105
    · subst b
      exact table_prefix_108_105 r n h
    ·
      by_cases h101 : b = 101
      · subst b
        exact table_prefix_108_101 r n h
      ·
        delta solWordTable solWordTable.match_1 at h
        change (dite (b = 105) (fun _ => _) (fun _ => (dite (b = 101) (fun _ => _) (fun _ => (.other : WordClass))))) = .tok (.num n) at h
        rw [dif_neg h105, dif_neg h101] at h
        cases h

theorem table_prefix_109 (r : Bytes) (n : NumLit) :
    solWordTable ([109] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h97 : b = 97
    · subst b
      exact table_prefix_109_97 r n h
    ·
      by_cases h101 : b = 101
      · subst b
        exact table_prefix_109_101 r n h
      ·
        by_cases h111 : b = 111
        · subst b
          exact table_prefix_109_111 r n h
        ·
          by_cases h105 : b = 105
          · subst b
            exact table_prefix_109_105 r n h
          ·
            by_cases h117 : b = 117
            · subst b
              exact table_prefix_109_117 r n h
            ·
              delta solWordTable solWordTable.match_1 at h
              change (dite (b = 97) (fun _ => _) (fun _ => (dite (b = 101) (fun _ => _) (fun _ => (dite (b = 111) (fun _ => _) (fun _ => (dite (b = 105) (fun _ => _) (fun _ => (dite (b = 117) (fun _ => _) (fun _ => (.other : WordClass))))))))))) = .tok (.num n) at h
              rw [dif_neg h97, dif_neg h101, dif_neg h111, dif_neg h105, dif_neg h117] at h
              cases h

theorem table_prefix_110 (r : Bytes) (n : NumLit) :
    solWordTable ([110] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h101 : b = 101
    · subst b
      exact table_prefix_110_101 r n h
    ·
      by_cases h117 : b = 117
      · subst b
        exact table_prefix_110_117 r n h
      ·
        delta solWordTable solWordTable.match_1 at h
        change (dite (b = 101) (fun _ => _) (fun _ => (dite (b = 117) (fun _ => _) (fun _ => (.other : WordClass))))) = .tok (.num n) at h
        rw [dif_neg h101, dif_neg h117] at h
        cases h

theorem table_prefix_111 (r : Bytes) (n : NumLit) :
    solWordTable ([111] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h118 : b = 118
    · subst b
      exact table_prefix_111_118 r n h
    ·
      by_cases h102 : b = 102
      · subst b
        exact table_prefix_111_102 r n h
      ·
        delta solWordTable solWordTable.match_1 at h
        change (dite (b = 118) (fun _ => _) (fun _ => (dite (b = 102) (fun _ => _) (fun _ => (.other : WordClass))))) = .tok (.num n) at h
        rw [dif_neg h118, dif_neg h102] at h
        cases h

theorem table_prefix_112 (r : Bytes) (n : NumLit) :
    solWordTable ([112] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h97 : b = 97
    · subst b
      exact table_prefix_112_97 r n h
    ·
      by_cases h114 : b = 114
      · subst b
        exact table_prefix_112_114 r n h
      ·
        by_cases h117 : b = 117
        · subst b
          exact table_prefix_112_117 r n h
        ·
          delta solWordTable solWordTable.match_1 at h
          change (dite (b = 97) (fun _ => _) (fun _ => (dite (b = 114) (fun _ => _) (fun _ => (dite (b = 117) (fun _ => _) (fun _ => (.other : WordClass))))))) = .tok (.num n) at h
          rw [dif_neg h97, dif_neg h114, dif_neg h117] at h
          cases h

theorem table_prefix_114 (r : Bytes) (n : NumLit) :
    solWordTable ([114] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h101 : b = 101
    · subst b
      exact table_prefix_114_101 r n h
    ·
      delta solWordTable solWordTable.match_1 at h
      change (dite (b = 101) (fun _ => _) (fun _ => (.other : WordClass))) = .tok (.num n) at h
      rw [dif_neg h101] at h
      cases h

theorem table_prefix_115 (r : Bytes) (n : NumLit) :
    solWordTable ([115] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h116 : b = 116
    · subst b
      exact table_prefix_115_116 r n h
    ·
      by_cases h101 : b = 101
      · subst b
        exact table_prefix_115_101 r n h
      ·
        by_cases h105 : b = 105
        · subst b
          exact table_prefix_115_105 r n h
        ·
          by_cases h117 : b = 117
          · subst b
            exact table_prefix_115_117 r n h
          ·
            by_cases h119 : b = 119
            · subst b
              exact table_prefix_115_119 r n h
            ·
              delta solWordTable solWordTable.match_1 at h
              change (dite (b = 116) (fun _ => _) (fun _ => (dite (b = 101) (fun _ => _) (fun _ => (dite (b = 105) (fun _ => _) (fun _ => (dite (b = 117) (fun _ => _) (fun _ => (dite (b = 119) (fun _ => _) (fun _ => (.other : WordClass))))))))))) = .tok (.num n) at h
              rw [dif_neg h116, dif_neg h101, dif_neg h105, dif_neg h117, dif_neg h119] at h
              cases h

theorem table_prefix_116 (r : Bytes) (n : NumLit) :
    solWordTable ([116] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h114 : b = 114
    · subst b
      exact table_prefix_116_114 r n h
    ·
      by_cases h121 : b = 121
      · subst b
        exact table_prefix_116_121 r n h
      ·
        delta solWordTable solWordTable.match_1 at h
        change (dite (b = 114) (fun _ => _) (fun _ => (dite (b = 121) (fun _ => _) (fun _ => (.other : WordClass))))) = .tok (.num n) at h
        rw [dif_neg h114, dif_neg h121] at h
        cases h

theorem table_prefix_117 (r : Bytes) (n : NumLit) :
    solWordTable ([117] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h110 : b = 110
    · subst b
      exact table_prefix_117_110 r n h
    ·
      by_cases h115 : b = 115
      · subst b
        exact table_prefix_117_115 r n h
      ·
        delta solWordTable solWordTable.match_1 at h
        change (dite (b = 110) (fun _ => _) (fun _ => (dite (b = 115) (fun _ => _) (fun _ => (.other : WordClass))))) = .tok (.num n) at h
        rw [dif_neg h110, dif_neg h115] at h
        cases h

end Solidity.Frontend.NumericLiteralProofs
