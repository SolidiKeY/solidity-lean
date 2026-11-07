import Solidity.Frontend.NumericLiteralProofs.WordTable.Part26

/-! # Generated direct structural word-table proof.
No scanner changes, equation generation, or raised budgets. -/
namespace Solidity.Frontend.NumericLiteralProofs
open Solidity.Frontend.Checked Solidity.Source

theorem table_prefix_115_116 (r : Bytes) (n : NumLit) :
    solWordTable ([115, 116] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h111 : b = 111
    · subst b
      exact table_prefix_115_116_111 r n h
    ·
      by_cases h114 : b = 114
      · subst b
        exact table_prefix_115_116_114 r n h
      ·
        by_cases h97 : b = 97
        · subst b
          exact table_prefix_115_116_97 r n h
        ·
          delta solWordTable solWordTable.match_1 at h
          change (dite (b = 111) (fun _ => _) (fun _ => (dite (b = 114) (fun _ => _) (fun _ => (dite (b = 97) (fun _ => _) (fun _ => (.other : WordClass))))))) = .tok (.num n) at h
          rw [dif_neg h111, dif_neg h114, dif_neg h97] at h
          cases h

theorem table_prefix_115_117 (r : Bytes) (n : NumLit) :
    solWordTable ([115, 117] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h112 : b = 112
    · subst b
      exact table_prefix_115_117_112 r n h
    ·
      delta solWordTable solWordTable.match_1 at h
      change (dite (b = 112) (fun _ => _) (fun _ => (.other : WordClass))) = .tok (.num n) at h
      rw [dif_neg h112] at h
      cases h

theorem table_prefix_115_119 (r : Bytes) (n : NumLit) :
    solWordTable ([115, 119] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h105 : b = 105
    · subst b
      exact table_prefix_115_119_105 r n h
    ·
      delta solWordTable solWordTable.match_1 at h
      change (dite (b = 105) (fun _ => _) (fun _ => (.other : WordClass))) = .tok (.num n) at h
      rw [dif_neg h105] at h
      cases h

theorem table_prefix_116_114 (r : Bytes) (n : NumLit) :
    solWordTable ([116, 114] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h121 : b = 121
    · subst b
      exact table_prefix_116_114_121 r n h
    ·
      by_cases h117 : b = 117
      · subst b
        exact table_prefix_116_114_117 r n h
      ·
        delta solWordTable solWordTable.match_1 at h
        change (dite (b = 121) (fun _ => _) (fun _ => (dite (b = 117) (fun _ => _) (fun _ => (.other : WordClass))))) = .tok (.num n) at h
        rw [dif_neg h121, dif_neg h117] at h
        cases h

theorem table_prefix_116_121 (r : Bytes) (n : NumLit) :
    solWordTable ([116, 121] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h112 : b = 112
    · subst b
      exact table_prefix_116_121_112 r n h
    ·
      delta solWordTable solWordTable.match_1 at h
      change (dite (b = 112) (fun _ => _) (fun _ => (.other : WordClass))) = .tok (.num n) at h
      rw [dif_neg h112] at h
      cases h

theorem table_prefix_117_110 (r : Bytes) (n : NumLit) :
    solWordTable ([117, 110] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h99 : b = 99
    · subst b
      exact table_prefix_117_110_99 r n h
    ·
      by_cases h105 : b = 105
      · subst b
        exact table_prefix_117_110_105 r n h
      ·
        delta solWordTable solWordTable.match_1 at h
        change (dite (b = 99) (fun _ => _) (fun _ => (dite (b = 105) (fun _ => _) (fun _ => (.other : WordClass))))) = .tok (.num n) at h
        rw [dif_neg h99, dif_neg h105] at h
        cases h

theorem table_prefix_117_115 (r : Bytes) (n : NumLit) :
    solWordTable ([117, 115] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h105 : b = 105
    · subst b
      exact table_prefix_117_115_105 r n h
    ·
      delta solWordTable solWordTable.match_1 at h
      change (dite (b = 105) (fun _ => _) (fun _ => (.other : WordClass))) = .tok (.num n) at h
      rw [dif_neg h105] at h
      cases h

theorem table_prefix_118_97 (r : Bytes) (n : NumLit) :
    solWordTable ([118, 97] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h114 : b = 114
    · subst b
      exact table_prefix_118_97_114 r n h
    ·
      delta solWordTable solWordTable.match_1 at h
      change (dite (b = 114) (fun _ => _) (fun _ => (.other : WordClass))) = .tok (.num n) at h
      rw [dif_neg h114] at h
      cases h

theorem table_prefix_118_105 (r : Bytes) (n : NumLit) :
    solWordTable ([118, 105] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h101 : b = 101
    · subst b
      exact table_prefix_118_105_101 r n h
    ·
      by_cases h114 : b = 114
      · subst b
        exact table_prefix_118_105_114 r n h
      ·
        delta solWordTable solWordTable.match_1 at h
        change (dite (b = 101) (fun _ => _) (fun _ => (dite (b = 114) (fun _ => _) (fun _ => (.other : WordClass))))) = .tok (.num n) at h
        rw [dif_neg h101, dif_neg h114] at h
        cases h

theorem table_prefix_119_101 (r : Bytes) (n : NumLit) :
    solWordTable ([119, 101] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h105 : b = 105
    · subst b
      exact table_prefix_119_101_105 r n h
    ·
      by_cases h101 : b = 101
      · subst b
        exact table_prefix_119_101_101 r n h
      ·
        delta solWordTable solWordTable.match_1 at h
        change (dite (b = 105) (fun _ => _) (fun _ => (dite (b = 101) (fun _ => _) (fun _ => (.other : WordClass))))) = .tok (.num n) at h
        rw [dif_neg h105, dif_neg h101] at h
        cases h

theorem table_prefix_119_104 (r : Bytes) (n : NumLit) :
    solWordTable ([119, 104] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h105 : b = 105
    · subst b
      exact table_prefix_119_104_105 r n h
    ·
      delta solWordTable solWordTable.match_1 at h
      change (dite (b = 105) (fun _ => _) (fun _ => (.other : WordClass))) = .tok (.num n) at h
      rw [dif_neg h105] at h
      cases h

theorem table_prefix_121_101 (r : Bytes) (n : NumLit) :
    solWordTable ([121, 101] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h97 : b = 97
    · subst b
      exact table_prefix_121_101_97 r n h
    ·
      delta solWordTable solWordTable.match_1 at h
      change (dite (b = 97) (fun _ => _) (fun _ => (.other : WordClass))) = .tok (.num n) at h
      rw [dif_neg h97] at h
      cases h

theorem table_prefix_97 (r : Bytes) (n : NumLit) :
    solWordTable ([97] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h98 : b = 98
    · subst b
      exact table_prefix_97_98 r n h
    ·
      by_cases h110 : b = 110
      · subst b
        exact table_prefix_97_110 r n h
      ·
        by_cases h115 : b = 115
        · subst b
          exact table_prefix_97_115 r n h
        ·
          by_cases h100 : b = 100
          · subst b
            exact table_prefix_97_100 r n h
          ·
            by_cases h102 : b = 102
            · subst b
              exact table_prefix_97_102 r n h
            ·
              by_cases h108 : b = 108
              · subst b
                exact table_prefix_97_108 r n h
              ·
                by_cases h112 : b = 112
                · subst b
                  exact table_prefix_97_112 r n h
                ·
                  by_cases h117 : b = 117
                  · subst b
                    exact table_prefix_97_117 r n h
                  ·
                    delta solWordTable solWordTable.match_1 at h
                    change (dite (b = 98) (fun _ => _) (fun _ => (dite (b = 110) (fun _ => _) (fun _ => (dite (b = 115) (fun _ => _) (fun _ => (dite (b = 100) (fun _ => _) (fun _ => (dite (b = 102) (fun _ => _) (fun _ => (dite (b = 108) (fun _ => _) (fun _ => (dite (b = 112) (fun _ => _) (fun _ => (dite (b = 117) (fun _ => _) (fun _ => (.other : WordClass))))))))))))))))) = .tok (.num n) at h
                    rw [dif_neg h98, dif_neg h110, dif_neg h115, dif_neg h100, dif_neg h102, dif_neg h108, dif_neg h112, dif_neg h117] at h
                    cases h

theorem table_prefix_98 (r : Bytes) (n : NumLit) :
    solWordTable ([98] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h114 : b = 114
    · subst b
      exact table_prefix_98_114 r n h
    ·
      by_cases h111 : b = 111
      · subst b
        exact table_prefix_98_111 r n h
      ·
        by_cases h121 : b = 121
        · subst b
          exact table_prefix_98_121 r n h
        ·
          delta solWordTable solWordTable.match_1 at h
          change (dite (b = 114) (fun _ => _) (fun _ => (dite (b = 111) (fun _ => _) (fun _ => (dite (b = 121) (fun _ => _) (fun _ => (.other : WordClass))))))) = .tok (.num n) at h
          rw [dif_neg h114, dif_neg h111, dif_neg h121] at h
          cases h

theorem table_prefix_99 (r : Bytes) (n : NumLit) :
    solWordTable ([99] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h97 : b = 97
    · subst b
      exact table_prefix_99_97 r n h
    ·
      by_cases h111 : b = 111
      · subst b
        exact table_prefix_99_111 r n h
      ·
        delta solWordTable solWordTable.match_1 at h
        change (dite (b = 97) (fun _ => _) (fun _ => (dite (b = 111) (fun _ => _) (fun _ => (.other : WordClass))))) = .tok (.num n) at h
        rw [dif_neg h97, dif_neg h111] at h
        cases h

end Solidity.Frontend.NumericLiteralProofs
