import Solidity.Frontend.NumericLiteralProofs.WordTable.Part28

/-! # Generated direct structural word-table proof.
No scanner changes, equation generation, or raised budgets. -/
namespace Solidity.Frontend.NumericLiteralProofs
open Solidity.Frontend.Checked Solidity.Source

theorem table_prefix_118 (r : Bytes) (n : NumLit) :
    solWordTable ([118] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h105 : b = 105
    · subst b
      exact table_prefix_118_105 r n h
    ·
      by_cases h97 : b = 97
      · subst b
        exact table_prefix_118_97 r n h
      ·
        delta solWordTable solWordTable.match_1 at h
        change (dite (b = 105) (fun _ => _) (fun _ => (dite (b = 97) (fun _ => _) (fun _ => (.other : WordClass))))) = .tok (.num n) at h
        rw [dif_neg h105, dif_neg h97] at h
        cases h

theorem table_prefix_119 (r : Bytes) (n : NumLit) :
    solWordTable ([119] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h104 : b = 104
    · subst b
      exact table_prefix_119_104 r n h
    ·
      by_cases h101 : b = 101
      · subst b
        exact table_prefix_119_101 r n h
      ·
        delta solWordTable solWordTable.match_1 at h
        change (dite (b = 104) (fun _ => _) (fun _ => (dite (b = 101) (fun _ => _) (fun _ => (.other : WordClass))))) = .tok (.num n) at h
        rw [dif_neg h104, dif_neg h101] at h
        cases h

theorem table_prefix_121 (r : Bytes) (n : NumLit) :
    solWordTable ([121] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h101 : b = 101
    · subst b
      exact table_prefix_121_101 r n h
    ·
      delta solWordTable solWordTable.match_1 at h
      change (dite (b = 101) (fun _ => _) (fun _ => (.other : WordClass))) = .tok (.num n) at h
      rw [dif_neg h101] at h
      cases h

theorem table_prefix_root (r : Bytes) (n : NumLit) :
    solWordTable ([] ++ r) ≠ .tok (.num n) := by
  intro h
  cases r with
  | nil =>
    with_unfolding_all change (.other : WordClass) = .tok (.num n) at h
    cases h
  | cons b r =>
    by_cases h97 : b = 97
    · subst b
      exact table_prefix_97 r n h
    ·
      by_cases h98 : b = 98
      · subst b
        exact table_prefix_98 r n h
      ·
        by_cases h99 : b = 99
        · subst b
          exact table_prefix_99 r n h
        ·
          by_cases h100 : b = 100
          · subst b
            exact table_prefix_100 r n h
          ·
            by_cases h101 : b = 101
            · subst b
              exact table_prefix_101 r n h
            ·
              by_cases h102 : b = 102
              · subst b
                exact table_prefix_102 r n h
              ·
                by_cases h104 : b = 104
                · subst b
                  exact table_prefix_104 r n h
                ·
                  by_cases h105 : b = 105
                  · subst b
                    exact table_prefix_105 r n h
                  ·
                    by_cases h108 : b = 108
                    · subst b
                      exact table_prefix_108 r n h
                    ·
                      by_cases h109 : b = 109
                      · subst b
                        exact table_prefix_109 r n h
                      ·
                        by_cases h110 : b = 110
                        · subst b
                          exact table_prefix_110 r n h
                        ·
                          by_cases h111 : b = 111
                          · subst b
                            exact table_prefix_111 r n h
                          ·
                            by_cases h112 : b = 112
                            · subst b
                              exact table_prefix_112 r n h
                            ·
                              by_cases h114 : b = 114
                              · subst b
                                exact table_prefix_114 r n h
                              ·
                                by_cases h115 : b = 115
                                · subst b
                                  exact table_prefix_115 r n h
                                ·
                                  by_cases h116 : b = 116
                                  · subst b
                                    exact table_prefix_116 r n h
                                  ·
                                    by_cases h117 : b = 117
                                    · subst b
                                      exact table_prefix_117 r n h
                                    ·
                                      by_cases h118 : b = 118
                                      · subst b
                                        exact table_prefix_118 r n h
                                      ·
                                        by_cases h119 : b = 119
                                        · subst b
                                          exact table_prefix_119 r n h
                                        ·
                                          by_cases h103 : b = 103
                                          · subst b
                                            exact table_prefix_103 r n h
                                          ·
                                            by_cases h121 : b = 121
                                            · subst b
                                              exact table_prefix_121 r n h
                                            ·
                                              delta solWordTable solWordTable.match_1 at h
                                              change (dite (b = 97) (fun _ => _) (fun _ => (dite (b = 98) (fun _ => _) (fun _ => (dite (b = 99) (fun _ => _) (fun _ => (dite (b = 100) (fun _ => _) (fun _ => (dite (b = 101) (fun _ => _) (fun _ => (dite (b = 102) (fun _ => _) (fun _ => (dite (b = 104) (fun _ => _) (fun _ => (dite (b = 105) (fun _ => _) (fun _ => (dite (b = 108) (fun _ => _) (fun _ => (dite (b = 109) (fun _ => _) (fun _ => (dite (b = 110) (fun _ => _) (fun _ => (dite (b = 111) (fun _ => _) (fun _ => (dite (b = 112) (fun _ => _) (fun _ => (dite (b = 114) (fun _ => _) (fun _ => (dite (b = 115) (fun _ => _) (fun _ => (dite (b = 116) (fun _ => _) (fun _ => (dite (b = 117) (fun _ => _) (fun _ => (dite (b = 118) (fun _ => _) (fun _ => (dite (b = 119) (fun _ => _) (fun _ => (dite (b = 103) (fun _ => _) (fun _ => (dite (b = 121) (fun _ => _) (fun _ => (.other : WordClass))))))))))))))))))))))))))))))))))))))))))) = .tok (.num n) at h
                                              rw [dif_neg h97, dif_neg h98, dif_neg h99, dif_neg h100, dif_neg h101, dif_neg h102, dif_neg h104, dif_neg h105, dif_neg h108, dif_neg h109, dif_neg h110, dif_neg h111, dif_neg h112, dif_neg h114, dif_neg h115, dif_neg h116, dif_neg h117, dif_neg h118, dif_neg h119, dif_neg h103, dif_neg h121] at h
                                              cases h

end Solidity.Frontend.NumericLiteralProofs
