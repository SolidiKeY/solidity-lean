import Solidity.Frontend.NumericLiteralProofs.WordTable.Part23

/-! # Generated direct structural word-table proof.
No scanner changes, equation generation, or raised budgets. -/
namespace Solidity.Frontend.NumericLiteralProofs
open Solidity.Frontend.Checked Solidity.Source

theorem table_prefix_97_112 (r : Bytes) (n : NumLit) :
    solWordTable ([97, 112] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h112 : b = 112
    · subst b
      exact table_prefix_97_112_112 r n h
    ·
      delta solWordTable solWordTable.match_1 at h
      change (dite (b = 112) (fun _ => _) (fun _ => (.other : WordClass))) = .tok (.num n) at h
      rw [dif_neg h112] at h
      cases h

theorem table_prefix_97_115 (r : Bytes) (n : NumLit) :
    solWordTable ([97, 115] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.tok (.kw .as_) : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h115 : b = 115
    · subst b
      exact table_prefix_97_115_115 r n h
    ·
      delta solWordTable solWordTable.match_1 at h
      change (dite (b = 115) (fun _ => _) (fun _ => (.other : WordClass))) = .tok (.num n) at h
      rw [dif_neg h115] at h
      cases h

theorem table_prefix_97_117 (r : Bytes) (n : NumLit) :
    solWordTable ([97, 117] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h116 : b = 116
    · subst b
      exact table_prefix_97_117_116 r n h
    ·
      delta solWordTable solWordTable.match_1 at h
      change (dite (b = 116) (fun _ => _) (fun _ => (.other : WordClass))) = .tok (.num n) at h
      rw [dif_neg h116] at h
      cases h

theorem table_prefix_98_111 (r : Bytes) (n : NumLit) :
    solWordTable ([98, 111] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h111 : b = 111
    · subst b
      exact table_prefix_98_111_111 r n h
    ·
      delta solWordTable solWordTable.match_1 at h
      change (dite (b = 111) (fun _ => _) (fun _ => (.other : WordClass))) = .tok (.num n) at h
      rw [dif_neg h111] at h
      cases h

theorem table_prefix_98_114 (r : Bytes) (n : NumLit) :
    solWordTable ([98, 114] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h101 : b = 101
    · subst b
      exact table_prefix_98_114_101 r n h
    ·
      delta solWordTable solWordTable.match_1 at h
      change (dite (b = 101) (fun _ => _) (fun _ => (.other : WordClass))) = .tok (.num n) at h
      rw [dif_neg h101] at h
      cases h

theorem table_prefix_98_121 (r : Bytes) (n : NumLit) :
    solWordTable ([98, 121] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h116 : b = 116
    · subst b
      exact table_prefix_98_121_116 r n h
    ·
      delta solWordTable solWordTable.match_1 at h
      change (dite (b = 116) (fun _ => _) (fun _ => (.other : WordClass))) = .tok (.num n) at h
      rw [dif_neg h116] at h
      cases h

theorem table_prefix_99_97 (r : Bytes) (n : NumLit) :
    solWordTable ([99, 97] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h108 : b = 108
    · subst b
      exact table_prefix_99_97_108 r n h
    ·
      by_cases h116 : b = 116
      · subst b
        exact table_prefix_99_97_116 r n h
      ·
        by_cases h115 : b = 115
        · subst b
          exact table_prefix_99_97_115 r n h
        ·
          delta solWordTable solWordTable.match_1 at h
          change (dite (b = 108) (fun _ => _) (fun _ => (dite (b = 116) (fun _ => _) (fun _ => (dite (b = 115) (fun _ => _) (fun _ => (.other : WordClass))))))) = .tok (.num n) at h
          rw [dif_neg h108, dif_neg h116, dif_neg h115] at h
          cases h

theorem table_prefix_99_111 (r : Bytes) (n : NumLit) :
    solWordTable ([99, 111] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h110 : b = 110
    · subst b
      exact table_prefix_99_111_110 r n h
    ·
      by_cases h112 : b = 112
      · subst b
        exact table_prefix_99_111_112 r n h
      ·
        delta solWordTable solWordTable.match_1 at h
        change (dite (b = 110) (fun _ => _) (fun _ => (dite (b = 112) (fun _ => _) (fun _ => (.other : WordClass))))) = .tok (.num n) at h
        rw [dif_neg h110, dif_neg h112] at h
        cases h

theorem table_prefix_100_97 (r : Bytes) (n : NumLit) :
    solWordTable ([100, 97] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h121 : b = 121
    · subst b
      exact table_prefix_100_97_121 r n h
    ·
      delta solWordTable solWordTable.match_1 at h
      change (dite (b = 121) (fun _ => _) (fun _ => (.other : WordClass))) = .tok (.num n) at h
      rw [dif_neg h121] at h
      cases h

theorem table_prefix_100_101 (r : Bytes) (n : NumLit) :
    solWordTable ([100, 101] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h108 : b = 108
    · subst b
      exact table_prefix_100_101_108 r n h
    ·
      by_cases h102 : b = 102
      · subst b
        exact table_prefix_100_101_102 r n h
      ·
        delta solWordTable solWordTable.match_1 at h
        change (dite (b = 108) (fun _ => _) (fun _ => (dite (b = 102) (fun _ => _) (fun _ => (.other : WordClass))))) = .tok (.num n) at h
        rw [dif_neg h108, dif_neg h102] at h
        cases h

theorem table_prefix_100_111 (r : Bytes) (n : NumLit) :
    solWordTable ([100, 111] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.tok (.kw .do_) : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h

theorem table_prefix_101_108 (r : Bytes) (n : NumLit) :
    solWordTable ([101, 108] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h115 : b = 115
    · subst b
      exact table_prefix_101_108_115 r n h
    ·
      delta solWordTable solWordTable.match_1 at h
      change (dite (b = 115) (fun _ => _) (fun _ => (.other : WordClass))) = .tok (.num n) at h
      rw [dif_neg h115] at h
      cases h

theorem table_prefix_101_109 (r : Bytes) (n : NumLit) :
    solWordTable ([101, 109] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h105 : b = 105
    · subst b
      exact table_prefix_101_109_105 r n h
    ·
      delta solWordTable solWordTable.match_1 at h
      change (dite (b = 105) (fun _ => _) (fun _ => (.other : WordClass))) = .tok (.num n) at h
      rw [dif_neg h105] at h
      cases h

theorem table_prefix_101_110 (r : Bytes) (n : NumLit) :
    solWordTable ([101, 110] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h117 : b = 117
    · subst b
      exact table_prefix_101_110_117 r n h
    ·
      delta solWordTable solWordTable.match_1 at h
      change (dite (b = 117) (fun _ => _) (fun _ => (.other : WordClass))) = .tok (.num n) at h
      rw [dif_neg h117] at h
      cases h

theorem table_prefix_101_116 (r : Bytes) (n : NumLit) :
    solWordTable ([101, 116] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h104 : b = 104
    · subst b
      exact table_prefix_101_116_104 r n h
    ·
      delta solWordTable solWordTable.match_1 at h
      change (dite (b = 104) (fun _ => _) (fun _ => (.other : WordClass))) = .tok (.num n) at h
      rw [dif_neg h104] at h
      cases h

end Solidity.Frontend.NumericLiteralProofs
