import Jsp000404.MixedStarExclusion

/-! Exact seven-nonanchor terminal. All branches below are ordinary Lean
linear-arithmetic proofs. The diagnostic only selected which triangle
disjunctions to split; no solver result or external certificate is trusted. -/

namespace Jsp404.N3R01Terminal

structure SevenModel where
  lam : ℝ
  p : ℝ
  hlam : 0 < lam
  hp : 3 * lam ≤ p ∧ p < 4 * lam
  t : Fin 7 → ℝ
  ht : StrictMono t
  ht0 : 0 ≤ t 0
  ht6 : t 6 ≤ p - 3 * lam
  d : Fin 7 → Fin 7 → ℝ
  hcor : ∀ i j : Fin 7, i < j → t i + lam ≤ d i j ∧ d i j ≤ p - lam + t j
  htr : ∀ i j k : Fin 7, i < j → j < k →
    (d i j + lam ≤ d j k ∧ d i j < d i k ∧ d i k < d j k) ∨
    (d j k + lam ≤ d i j ∧ d j k < d i k ∧ d i k < d i j)

set_option maxHeartbeats 4000000 in
theorem seven_model_impossible (m : SevenModel) : False := by
  have hlam := m.hlam
  have hp0 := m.hp.1
  have hp1 := m.hp.2
  have ht0 := m.ht0
  have ht6 := m.ht6
  have ht01 := m.ht (show (0 : Fin 7) < 1 from by decide)
  have ht12 := m.ht (show (1 : Fin 7) < 2 from by decide)
  have ht23 := m.ht (show (2 : Fin 7) < 3 from by decide)
  have ht34 := m.ht (show (3 : Fin 7) < 4 from by decide)
  have ht45 := m.ht (show (4 : Fin 7) < 5 from by decide)
  have ht56 := m.ht (show (5 : Fin 7) < 6 from by decide)
  obtain ⟨hc56a, hc56b⟩ := m.hcor 5 6 (by decide)
  obtain ⟨hc34a, hc34b⟩ := m.hcor 3 4 (by decide)
  obtain ⟨hc01a, hc01b⟩ := m.hcor 0 1 (by decide)
  obtain ⟨hc12a, hc12b⟩ := m.hcor 1 2 (by decide)
  obtain ⟨hc23a, hc23b⟩ := m.hcor 2 3 (by decide)
  obtain ⟨hc45a, hc45b⟩ := m.hcor 4 5 (by decide)
  rcases m.htr 1 2 4 (by decide) (by decide) with
    ⟨h124a, h124b, h124c⟩ | ⟨h124a, h124b, h124c⟩
  ·
    rcases m.htr 3 5 6 (by decide) (by decide) with
      ⟨h356a, h356b, h356c⟩ | ⟨h356a, h356b, h356c⟩
    ·
      rcases m.htr 1 2 3 (by decide) (by decide) with
        ⟨h123a, h123b, h123c⟩ | ⟨h123a, h123b, h123c⟩
      ·
        rcases m.htr 1 3 4 (by decide) (by decide) with
          ⟨h134a, h134b, h134c⟩ | ⟨h134a, h134b, h134c⟩
        ·
          rcases m.htr 1 3 5 (by decide) (by decide) with
            ⟨h135a, h135b, h135c⟩ | ⟨h135a, h135b, h135c⟩
          ·
            rcases m.htr 2 3 5 (by decide) (by decide) with
              ⟨h235a, h235b, h235c⟩ | ⟨h235a, h235b, h235c⟩
            ·
              linarith
            ·
              rcases m.htr 2 3 4 (by decide) (by decide) with
                ⟨h234a, h234b, h234c⟩ | ⟨h234a, h234b, h234c⟩
              ·
                linarith
              ·
                rcases m.htr 2 4 5 (by decide) (by decide) with
                  ⟨h245a, h245b, h245c⟩ | ⟨h245a, h245b, h245c⟩
                ·
                  rcases m.htr 3 4 5 (by decide) (by decide) with
                    ⟨h345a, h345b, h345c⟩ | ⟨h345a, h345b, h345c⟩
                  ·
                    rcases m.htr 4 5 6 (by decide) (by decide) with
                      ⟨h456a, h456b, h456c⟩ | ⟨h456a, h456b, h456c⟩
                    ·
                      linarith
                    ·
                      linarith
                  ·
                    linarith
                ·
                  rcases m.htr 3 4 5 (by decide) (by decide) with
                    ⟨h345a, h345b, h345c⟩ | ⟨h345a, h345b, h345c⟩
                  ·
                    linarith
                  ·
                    linarith
          ·
            rcases m.htr 2 3 5 (by decide) (by decide) with
              ⟨h235a, h235b, h235c⟩ | ⟨h235a, h235b, h235c⟩
            ·
              linarith
            ·
              rcases m.htr 2 3 4 (by decide) (by decide) with
                ⟨h234a, h234b, h234c⟩ | ⟨h234a, h234b, h234c⟩
              ·
                rcases m.htr 2 4 5 (by decide) (by decide) with
                  ⟨h245a, h245b, h245c⟩ | ⟨h245a, h245b, h245c⟩
                ·
                  linarith
                ·
                  rcases m.htr 3 4 5 (by decide) (by decide) with
                    ⟨h345a, h345b, h345c⟩ | ⟨h345a, h345b, h345c⟩
                  ·
                    linarith
                  ·
                    linarith
              ·
                rcases m.htr 2 4 5 (by decide) (by decide) with
                  ⟨h245a, h245b, h245c⟩ | ⟨h245a, h245b, h245c⟩
                ·
                  rcases m.htr 3 4 5 (by decide) (by decide) with
                    ⟨h345a, h345b, h345c⟩ | ⟨h345a, h345b, h345c⟩
                  ·
                    linarith
                  ·
                    linarith
                ·
                  rcases m.htr 3 4 5 (by decide) (by decide) with
                    ⟨h345a, h345b, h345c⟩ | ⟨h345a, h345b, h345c⟩
                  ·
                    linarith
                  ·
                    linarith
        ·
          rcases m.htr 1 3 5 (by decide) (by decide) with
            ⟨h135a, h135b, h135c⟩ | ⟨h135a, h135b, h135c⟩
          ·
            linarith
          ·
            rcases m.htr 2 3 5 (by decide) (by decide) with
              ⟨h235a, h235b, h235c⟩ | ⟨h235a, h235b, h235c⟩
            ·
              linarith
            ·
              rcases m.htr 2 3 4 (by decide) (by decide) with
                ⟨h234a, h234b, h234c⟩ | ⟨h234a, h234b, h234c⟩
              ·
                linarith
              ·
                rcases m.htr 2 4 5 (by decide) (by decide) with
                  ⟨h245a, h245b, h245c⟩ | ⟨h245a, h245b, h245c⟩
                ·
                  rcases m.htr 3 4 5 (by decide) (by decide) with
                    ⟨h345a, h345b, h345c⟩ | ⟨h345a, h345b, h345c⟩
                  ·
                    rcases m.htr 4 5 6 (by decide) (by decide) with
                      ⟨h456a, h456b, h456c⟩ | ⟨h456a, h456b, h456c⟩
                    ·
                      linarith
                    ·
                      rcases m.htr 0 1 3 (by decide) (by decide) with
                        ⟨h013a, h013b, h013c⟩ | ⟨h013a, h013b, h013c⟩
                      ·
                        rcases m.htr 0 1 2 (by decide) (by decide) with
                          ⟨h012a, h012b, h012c⟩ | ⟨h012a, h012b, h012c⟩
                        ·
                          linarith
                        ·
                          rcases m.htr 0 1 4 (by decide) (by decide) with
                            ⟨h014a, h014b, h014c⟩ | ⟨h014a, h014b, h014c⟩
                          ·
                            linarith
                          ·
                            linarith
                      ·
                        linarith
                  ·
                    linarith
                ·
                  rcases m.htr 3 4 5 (by decide) (by decide) with
                    ⟨h345a, h345b, h345c⟩ | ⟨h345a, h345b, h345c⟩
                  ·
                    linarith
                  ·
                    linarith
      ·
        rcases m.htr 1 3 4 (by decide) (by decide) with
          ⟨h134a, h134b, h134c⟩ | ⟨h134a, h134b, h134c⟩
        ·
          rcases m.htr 1 3 5 (by decide) (by decide) with
            ⟨h135a, h135b, h135c⟩ | ⟨h135a, h135b, h135c⟩
          ·
            rcases m.htr 2 3 5 (by decide) (by decide) with
              ⟨h235a, h235b, h235c⟩ | ⟨h235a, h235b, h235c⟩
            ·
              rcases m.htr 2 3 4 (by decide) (by decide) with
                ⟨h234a, h234b, h234c⟩ | ⟨h234a, h234b, h234c⟩
              ·
                rcases m.htr 2 4 5 (by decide) (by decide) with
                  ⟨h245a, h245b, h245c⟩ | ⟨h245a, h245b, h245c⟩
                ·
                  linarith
                ·
                  rcases m.htr 3 4 5 (by decide) (by decide) with
                    ⟨h345a, h345b, h345c⟩ | ⟨h345a, h345b, h345c⟩
                  ·
                    linarith
                  ·
                    rcases m.htr 4 5 6 (by decide) (by decide) with
                      ⟨h456a, h456b, h456c⟩ | ⟨h456a, h456b, h456c⟩
                    ·
                      rcases m.htr 0 1 3 (by decide) (by decide) with
                        ⟨h013a, h013b, h013c⟩ | ⟨h013a, h013b, h013c⟩
                      ·
                        linarith
                      ·
                        rcases m.htr 0 1 2 (by decide) (by decide) with
                          ⟨h012a, h012b, h012c⟩ | ⟨h012a, h012b, h012c⟩
                        ·
                          linarith
                        ·
                          linarith
                    ·
                      linarith
              ·
                linarith
            ·
              linarith
          ·
            rcases m.htr 2 3 5 (by decide) (by decide) with
              ⟨h235a, h235b, h235c⟩ | ⟨h235a, h235b, h235c⟩
            ·
              linarith
            ·
              rcases m.htr 2 3 4 (by decide) (by decide) with
                ⟨h234a, h234b, h234c⟩ | ⟨h234a, h234b, h234c⟩
              ·
                rcases m.htr 2 4 5 (by decide) (by decide) with
                  ⟨h245a, h245b, h245c⟩ | ⟨h245a, h245b, h245c⟩
                ·
                  linarith
                ·
                  linarith
              ·
                linarith
        ·
          linarith
    ·
      rcases m.htr 1 2 3 (by decide) (by decide) with
        ⟨h123a, h123b, h123c⟩ | ⟨h123a, h123b, h123c⟩
      ·
        rcases m.htr 1 3 4 (by decide) (by decide) with
          ⟨h134a, h134b, h134c⟩ | ⟨h134a, h134b, h134c⟩
        ·
          rcases m.htr 1 3 5 (by decide) (by decide) with
            ⟨h135a, h135b, h135c⟩ | ⟨h135a, h135b, h135c⟩
          ·
            rcases m.htr 2 3 5 (by decide) (by decide) with
              ⟨h235a, h235b, h235c⟩ | ⟨h235a, h235b, h235c⟩
            ·
              rcases m.htr 2 3 4 (by decide) (by decide) with
                ⟨h234a, h234b, h234c⟩ | ⟨h234a, h234b, h234c⟩
              ·
                rcases m.htr 2 4 5 (by decide) (by decide) with
                  ⟨h245a, h245b, h245c⟩ | ⟨h245a, h245b, h245c⟩
                ·
                  rcases m.htr 3 4 5 (by decide) (by decide) with
                    ⟨h345a, h345b, h345c⟩ | ⟨h345a, h345b, h345c⟩
                  ·
                    linarith
                  ·
                    linarith
                ·
                  rcases m.htr 3 4 5 (by decide) (by decide) with
                    ⟨h345a, h345b, h345c⟩ | ⟨h345a, h345b, h345c⟩
                  ·
                    linarith
                  ·
                    rcases m.htr 4 5 6 (by decide) (by decide) with
                      ⟨h456a, h456b, h456c⟩ | ⟨h456a, h456b, h456c⟩
                    ·
                      linarith
                    ·
                      linarith
              ·
                rcases m.htr 2 4 5 (by decide) (by decide) with
                  ⟨h245a, h245b, h245c⟩ | ⟨h245a, h245b, h245c⟩
                ·
                  rcases m.htr 3 4 5 (by decide) (by decide) with
                    ⟨h345a, h345b, h345c⟩ | ⟨h345a, h345b, h345c⟩
                  ·
                    linarith
                  ·
                    linarith
                ·
                  linarith
            ·
              linarith
          ·
            linarith
        ·
          rcases m.htr 1 3 5 (by decide) (by decide) with
            ⟨h135a, h135b, h135c⟩ | ⟨h135a, h135b, h135c⟩
          ·
            rcases m.htr 2 3 5 (by decide) (by decide) with
              ⟨h235a, h235b, h235c⟩ | ⟨h235a, h235b, h235c⟩
            ·
              rcases m.htr 2 3 4 (by decide) (by decide) with
                ⟨h234a, h234b, h234c⟩ | ⟨h234a, h234b, h234c⟩
              ·
                linarith
              ·
                rcases m.htr 2 4 5 (by decide) (by decide) with
                  ⟨h245a, h245b, h245c⟩ | ⟨h245a, h245b, h245c⟩
                ·
                  rcases m.htr 3 4 5 (by decide) (by decide) with
                    ⟨h345a, h345b, h345c⟩ | ⟨h345a, h345b, h345c⟩
                  ·
                    rcases m.htr 4 5 6 (by decide) (by decide) with
                      ⟨h456a, h456b, h456c⟩ | ⟨h456a, h456b, h456c⟩
                    ·
                      linarith
                    ·
                      rcases m.htr 0 1 3 (by decide) (by decide) with
                        ⟨h013a, h013b, h013c⟩ | ⟨h013a, h013b, h013c⟩
                      ·
                        rcases m.htr 0 1 2 (by decide) (by decide) with
                          ⟨h012a, h012b, h012c⟩ | ⟨h012a, h012b, h012c⟩
                        ·
                          linarith
                        ·
                          linarith
                      ·
                        linarith
                  ·
                    linarith
                ·
                  linarith
            ·
              linarith
          ·
            linarith
      ·
        rcases m.htr 1 3 4 (by decide) (by decide) with
          ⟨h134a, h134b, h134c⟩ | ⟨h134a, h134b, h134c⟩
        ·
          rcases m.htr 1 3 5 (by decide) (by decide) with
            ⟨h135a, h135b, h135c⟩ | ⟨h135a, h135b, h135c⟩
          ·
            rcases m.htr 2 3 5 (by decide) (by decide) with
              ⟨h235a, h235b, h235c⟩ | ⟨h235a, h235b, h235c⟩
            ·
              rcases m.htr 2 3 4 (by decide) (by decide) with
                ⟨h234a, h234b, h234c⟩ | ⟨h234a, h234b, h234c⟩
              ·
                rcases m.htr 2 4 5 (by decide) (by decide) with
                  ⟨h245a, h245b, h245c⟩ | ⟨h245a, h245b, h245c⟩
                ·
                  linarith
                ·
                  rcases m.htr 3 4 5 (by decide) (by decide) with
                    ⟨h345a, h345b, h345c⟩ | ⟨h345a, h345b, h345c⟩
                  ·
                    linarith
                  ·
                    rcases m.htr 4 5 6 (by decide) (by decide) with
                      ⟨h456a, h456b, h456c⟩ | ⟨h456a, h456b, h456c⟩
                    ·
                      linarith
                    ·
                      linarith
              ·
                linarith
            ·
              linarith
          ·
            linarith
        ·
          linarith
  ·
    rcases m.htr 3 5 6 (by decide) (by decide) with
      ⟨h356a, h356b, h356c⟩ | ⟨h356a, h356b, h356c⟩
    ·
      rcases m.htr 1 2 3 (by decide) (by decide) with
        ⟨h123a, h123b, h123c⟩ | ⟨h123a, h123b, h123c⟩
      ·
        rcases m.htr 1 3 4 (by decide) (by decide) with
          ⟨h134a, h134b, h134c⟩ | ⟨h134a, h134b, h134c⟩
        ·
          linarith
        ·
          rcases m.htr 1 3 5 (by decide) (by decide) with
            ⟨h135a, h135b, h135c⟩ | ⟨h135a, h135b, h135c⟩
          ·
            linarith
          ·
            rcases m.htr 2 3 5 (by decide) (by decide) with
              ⟨h235a, h235b, h235c⟩ | ⟨h235a, h235b, h235c⟩
            ·
              linarith
            ·
              rcases m.htr 2 3 4 (by decide) (by decide) with
                ⟨h234a, h234b, h234c⟩ | ⟨h234a, h234b, h234c⟩
              ·
                linarith
              ·
                linarith
      ·
        rcases m.htr 1 3 4 (by decide) (by decide) with
          ⟨h134a, h134b, h134c⟩ | ⟨h134a, h134b, h134c⟩
        ·
          rcases m.htr 1 3 5 (by decide) (by decide) with
            ⟨h135a, h135b, h135c⟩ | ⟨h135a, h135b, h135c⟩
          ·
            rcases m.htr 2 3 5 (by decide) (by decide) with
              ⟨h235a, h235b, h235c⟩ | ⟨h235a, h235b, h235c⟩
            ·
              rcases m.htr 2 3 4 (by decide) (by decide) with
                ⟨h234a, h234b, h234c⟩ | ⟨h234a, h234b, h234c⟩
              ·
                rcases m.htr 2 4 5 (by decide) (by decide) with
                  ⟨h245a, h245b, h245c⟩ | ⟨h245a, h245b, h245c⟩
                ·
                  rcases m.htr 3 4 5 (by decide) (by decide) with
                    ⟨h345a, h345b, h345c⟩ | ⟨h345a, h345b, h345c⟩
                  ·
                    rcases m.htr 4 5 6 (by decide) (by decide) with
                      ⟨h456a, h456b, h456c⟩ | ⟨h456a, h456b, h456c⟩
                    ·
                      linarith
                    ·
                      linarith
                  ·
                    rcases m.htr 4 5 6 (by decide) (by decide) with
                      ⟨h456a, h456b, h456c⟩ | ⟨h456a, h456b, h456c⟩
                    ·
                      rcases m.htr 0 1 3 (by decide) (by decide) with
                        ⟨h013a, h013b, h013c⟩ | ⟨h013a, h013b, h013c⟩
                      ·
                        linarith
                      ·
                        rcases m.htr 0 1 2 (by decide) (by decide) with
                          ⟨h012a, h012b, h012c⟩ | ⟨h012a, h012b, h012c⟩
                        ·
                          linarith
                        ·
                          linarith
                    ·
                      linarith
                ·
                  linarith
              ·
                linarith
            ·
              linarith
          ·
            rcases m.htr 2 3 5 (by decide) (by decide) with
              ⟨h235a, h235b, h235c⟩ | ⟨h235a, h235b, h235c⟩
            ·
              linarith
            ·
              rcases m.htr 2 3 4 (by decide) (by decide) with
                ⟨h234a, h234b, h234c⟩ | ⟨h234a, h234b, h234c⟩
              ·
                rcases m.htr 2 4 5 (by decide) (by decide) with
                  ⟨h245a, h245b, h245c⟩ | ⟨h245a, h245b, h245c⟩
                ·
                  linarith
                ·
                  linarith
              ·
                linarith
        ·
          rcases m.htr 1 3 5 (by decide) (by decide) with
            ⟨h135a, h135b, h135c⟩ | ⟨h135a, h135b, h135c⟩
          ·
            linarith
          ·
            rcases m.htr 2 3 5 (by decide) (by decide) with
              ⟨h235a, h235b, h235c⟩ | ⟨h235a, h235b, h235c⟩
            ·
              linarith
            ·
              rcases m.htr 2 3 4 (by decide) (by decide) with
                ⟨h234a, h234b, h234c⟩ | ⟨h234a, h234b, h234c⟩
              ·
                linarith
              ·
                linarith
    ·
      rcases m.htr 1 2 3 (by decide) (by decide) with
        ⟨h123a, h123b, h123c⟩ | ⟨h123a, h123b, h123c⟩
      ·
        rcases m.htr 1 3 4 (by decide) (by decide) with
          ⟨h134a, h134b, h134c⟩ | ⟨h134a, h134b, h134c⟩
        ·
          linarith
        ·
          rcases m.htr 1 3 5 (by decide) (by decide) with
            ⟨h135a, h135b, h135c⟩ | ⟨h135a, h135b, h135c⟩
          ·
            rcases m.htr 2 3 5 (by decide) (by decide) with
              ⟨h235a, h235b, h235c⟩ | ⟨h235a, h235b, h235c⟩
            ·
              rcases m.htr 2 3 4 (by decide) (by decide) with
                ⟨h234a, h234b, h234c⟩ | ⟨h234a, h234b, h234c⟩
              ·
                linarith
              ·
                linarith
            ·
              linarith
          ·
            linarith
      ·
        rcases m.htr 1 3 4 (by decide) (by decide) with
          ⟨h134a, h134b, h134c⟩ | ⟨h134a, h134b, h134c⟩
        ·
          rcases m.htr 1 3 5 (by decide) (by decide) with
            ⟨h135a, h135b, h135c⟩ | ⟨h135a, h135b, h135c⟩
          ·
            rcases m.htr 2 3 5 (by decide) (by decide) with
              ⟨h235a, h235b, h235c⟩ | ⟨h235a, h235b, h235c⟩
            ·
              rcases m.htr 2 3 4 (by decide) (by decide) with
                ⟨h234a, h234b, h234c⟩ | ⟨h234a, h234b, h234c⟩
              ·
                rcases m.htr 2 4 5 (by decide) (by decide) with
                  ⟨h245a, h245b, h245c⟩ | ⟨h245a, h245b, h245c⟩
                ·
                  rcases m.htr 3 4 5 (by decide) (by decide) with
                    ⟨h345a, h345b, h345c⟩ | ⟨h345a, h345b, h345c⟩
                  ·
                    rcases m.htr 4 5 6 (by decide) (by decide) with
                      ⟨h456a, h456b, h456c⟩ | ⟨h456a, h456b, h456c⟩
                    ·
                      linarith
                    ·
                      rcases m.htr 0 1 3 (by decide) (by decide) with
                        ⟨h013a, h013b, h013c⟩ | ⟨h013a, h013b, h013c⟩
                      ·
                        linarith
                      ·
                        rcases m.htr 0 1 2 (by decide) (by decide) with
                          ⟨h012a, h012b, h012c⟩ | ⟨h012a, h012b, h012c⟩
                        ·
                          linarith
                        ·
                          linarith
                  ·
                    rcases m.htr 4 5 6 (by decide) (by decide) with
                      ⟨h456a, h456b, h456c⟩ | ⟨h456a, h456b, h456c⟩
                    ·
                      linarith
                    ·
                      linarith
                ·
                  linarith
              ·
                linarith
            ·
              linarith
          ·
            linarith
        ·
          rcases m.htr 1 3 5 (by decide) (by decide) with
            ⟨h135a, h135b, h135c⟩ | ⟨h135a, h135b, h135c⟩
          ·
            rcases m.htr 2 3 5 (by decide) (by decide) with
              ⟨h235a, h235b, h235c⟩ | ⟨h235a, h235b, h235c⟩
            ·
              rcases m.htr 2 3 4 (by decide) (by decide) with
                ⟨h234a, h234b, h234c⟩ | ⟨h234a, h234b, h234c⟩
              ·
                linarith
              ·
                linarith
            ·
              linarith
          ·
            linarith

#print axioms seven_model_impossible

/-- Six non-anchor centres with actual sorted chord rows. -/
structure SixModel where
  lam : ℝ
  p : ℝ
  hlam : 0 < lam
  hp : 3 * lam ≤ p ∧ p < 4 * lam
  t : Fin 6 → ℝ
  ht : StrictMono t
  ht0 : 0 ≤ t 0
  ht5 : t 5 ≤ p - 3 * lam
  d : Fin 6 → Fin 6 → ℝ
  symm : ∀ i j, i ≠ j → d i j = d j i
  hcor : ∀ i j : Fin 6, i < j → t i + lam ≤ d i j ∧ d i j ≤ p - lam + t j
  htr : ∀ i j k : Fin 6, i < j → j < k →
    (d i j + lam ≤ d j k ∧ d i j < d i k ∧ d i k < d j k) ∨
    (d j k + lam ≤ d i j ∧ d j k < d i k ∧ d i k < d i j)
  rowxs : Fin 6 → List ℝ
  row_sorted : ∀ i, (rowxs i).Pairwise (· ≤ ·)
  row_perm : ∀ i, (rowxs i).Perm (((List.finRange 6).erase i).map (d i))

lemma gapScore_zero_of_small {lam g : ℝ} (hlam : 0 < lam)
    (hg0 : 0 ≤ g) (hg2 : g < 2 * lam) : gapScore lam g = 0 := by
  unfold gapScore
  have hf : ⌊g / lam⌋₊ < 2 := by
    rw [Nat.floor_lt (div_nonneg hg0 hlam.le)]
    rw [div_lt_iff₀ hlam]
    norm_num
    exact hg2
  omega

set_option maxHeartbeats 20000000 in
theorem six_model_rows_zero (m : SixModel) (i : Fin 6) :
    linearGapScore m.lam (m.t i) (m.t i + m.p) (m.rowxs i) = 0 := by
  have hlam := m.hlam
  have hp0 := m.hp.1
  have hp1 := m.hp.2
  have ht0 := m.ht0
  have ht5 := m.ht5
  have ht01 := m.ht (show (0 : Fin 6) < 1 from by decide)
  have ht12 := m.ht (show (1 : Fin 6) < 2 from by decide)
  have ht23 := m.ht (show (2 : Fin 6) < 3 from by decide)
  have ht34 := m.ht (show (3 : Fin 6) < 4 from by decide)
  have ht45 := m.ht (show (4 : Fin 6) < 5 from by decide)
  obtain ⟨hc01a, hc01b⟩ := m.hcor 0 1 (by decide)
  obtain ⟨hc02a, hc02b⟩ := m.hcor 0 2 (by decide)
  obtain ⟨hc03a, hc03b⟩ := m.hcor 0 3 (by decide)
  obtain ⟨hc04a, hc04b⟩ := m.hcor 0 4 (by decide)
  obtain ⟨hc05a, hc05b⟩ := m.hcor 0 5 (by decide)
  obtain ⟨hc12a, hc12b⟩ := m.hcor 1 2 (by decide)
  obtain ⟨hc13a, hc13b⟩ := m.hcor 1 3 (by decide)
  obtain ⟨hc14a, hc14b⟩ := m.hcor 1 4 (by decide)
  obtain ⟨hc15a, hc15b⟩ := m.hcor 1 5 (by decide)
  obtain ⟨hc23a, hc23b⟩ := m.hcor 2 3 (by decide)
  obtain ⟨hc24a, hc24b⟩ := m.hcor 2 4 (by decide)
  obtain ⟨hc25a, hc25b⟩ := m.hcor 2 5 (by decide)
  obtain ⟨hc34a, hc34b⟩ := m.hcor 3 4 (by decide)
  obtain ⟨hc35a, hc35b⟩ := m.hcor 3 5 (by decide)
  obtain ⟨hc45a, hc45b⟩ := m.hcor 4 5 (by decide)
  rcases m.htr 0 1 2 (by decide) (by decide) with
    ⟨h012a, h012b, h012c⟩ | ⟨h012a, h012b, h012c⟩
  ·
    rcases m.htr 0 1 3 (by decide) (by decide) with
      ⟨h013a, h013b, h013c⟩ | ⟨h013a, h013b, h013c⟩
    ·
      rcases m.htr 0 1 4 (by decide) (by decide) with
        ⟨h014a, h014b, h014c⟩ | ⟨h014a, h014b, h014c⟩
      ·
        rcases m.htr 0 1 5 (by decide) (by decide) with
          ⟨h015a, h015b, h015c⟩ | ⟨h015a, h015b, h015c⟩
        ·
          rcases m.htr 0 2 3 (by decide) (by decide) with
            ⟨h023a, h023b, h023c⟩ | ⟨h023a, h023b, h023c⟩
          ·
            rcases m.htr 0 2 4 (by decide) (by decide) with
              ⟨h024a, h024b, h024c⟩ | ⟨h024a, h024b, h024c⟩
            ·
              rcases m.htr 0 2 5 (by decide) (by decide) with
                ⟨h025a, h025b, h025c⟩ | ⟨h025a, h025b, h025c⟩
              ·
                rcases m.htr 0 3 4 (by decide) (by decide) with
                  ⟨h034a, h034b, h034c⟩ | ⟨h034a, h034b, h034c⟩
                ·
                  rcases m.htr 0 3 5 (by decide) (by decide) with
                    ⟨h035a, h035b, h035c⟩ | ⟨h035a, h035b, h035c⟩
                  ·
                    rcases m.htr 0 4 5 (by decide) (by decide) with
                      ⟨h045a, h045b, h045c⟩ | ⟨h045a, h045b, h045c⟩
                    ·
                      rcases m.htr 1 2 3 (by decide) (by decide) with
                        ⟨h123a, h123b, h123c⟩ | ⟨h123a, h123b, h123c⟩
                      ·
                        rcases m.htr 1 2 4 (by decide) (by decide) with
                          ⟨h124a, h124b, h124c⟩ | ⟨h124a, h124b, h124c⟩
                        ·
                          rcases m.htr 1 2 5 (by decide) (by decide) with
                            ⟨h125a, h125b, h125c⟩ | ⟨h125a, h125b, h125c⟩
                          ·
                            rcases m.htr 1 3 4 (by decide) (by decide) with
                              ⟨h134a, h134b, h134c⟩ | ⟨h134a, h134b, h134c⟩
                            ·
                              rcases m.htr 1 3 5 (by decide) (by decide) with
                                ⟨h135a, h135b, h135c⟩ | ⟨h135a, h135b, h135c⟩
                              ·
                                rcases m.htr 1 4 5 (by decide) (by decide) with
                                  ⟨h145a, h145b, h145c⟩ | ⟨h145a, h145b, h145c⟩
                                ·
                                  rcases m.htr 2 3 4 (by decide) (by decide) with
                                    ⟨h234a, h234b, h234c⟩ | ⟨h234a, h234b, h234c⟩
                                  ·
                                    exfalso; linarith only [hp1, ht0, ht5, ht45, hc01a, hc34b, h012a, h123a, h234a]
                                  ·
                                    exfalso; linarith only [hp1, h134a, h123b, hc23b, hc01a, ht45, ht34, h234a, ht5, ht0, h012a]
                                ·
                                  rcases m.htr 2 3 4 (by decide) (by decide) with
                                    ⟨h234a, h234b, h234c⟩ | ⟨h234a, h234b, h234c⟩
                                  ·
                                    exfalso; linarith only [h012a, hc34b, hp1, h123a, ht45, h234a, ht5, hc01a, ht0]
                                  ·
                                    exfalso; linarith only [h134c, ht45, h145a, h034b, h012b, hp1, h045a, h234a, ht34, hc01a, h023b, ht0, ht5, hc23b]
                              ·
                                exfalso; linarith only [ht5, ht0, ht45, h135a, h035a, hp1, h012b, hc34b, h134a, h023b, hc01a]
                            ·
                              rcases m.htr 1 3 5 (by decide) (by decide) with
                                ⟨h135a, h135b, h135c⟩ | ⟨h135a, h135b, h135c⟩
                              ·
                                exfalso; linarith only [ht0, hc35b, h023b, hp1, h135a, h012b, h134a, hc01a, h034a, ht5]
                              ·
                                rcases m.htr 1 4 5 (by decide) (by decide) with
                                  ⟨h145a, h145b, h145c⟩ | ⟨h145a, h145b, h145c⟩
                                ·
                                  rcases m.htr 2 3 4 (by decide) (by decide) with
                                    ⟨h234a, h234b, h234c⟩ | ⟨h234a, h234b, h234c⟩
                                  ·
                                    exfalso; linarith only [ht5, ht34, hp1, h134a, hc01a, h023b, hc23b, h123c, ht0, h234a, ht45, h012b, h034a]
                                  ·
                                    rcases m.htr 2 3 5 (by decide) (by decide) with
                                      ⟨h235a, h235b, h235c⟩ | ⟨h235a, h235b, h235c⟩
                                    ·
                                      exfalso; linarith only [ht5, h123c, hc35b, h023b, h134a, hp1, ht0, hc01a, h034a, h012b, h235a]
                                    ·
                                      rcases m.htr 2 4 5 (by decide) (by decide) with
                                        ⟨h245a, h245b, h245c⟩ | ⟨h245a, h245b, h245c⟩
                                      ·
                                        exfalso; linarith only [hp1, ht5, hc01a, ht0, h124a, h012a, hc45b, h245a]
                                      ·
                                        exfalso; linarith only [h145a, hp1, hc01a, ht5, ht45, h012b, h245a, h134b, h023b, ht0, h034a, hc24b]
                                ·
                                  rcases m.htr 2 3 4 (by decide) (by decide) with
                                    ⟨h234a, h234b, h234c⟩ | ⟨h234a, h234b, h234c⟩
                                  ·
                                    exfalso; linarith only [h134a, hc23b, h123c, hc01a, h134c, h045a, ht34, ht5, hp1, h145a, h034b, h234a, ht45, h023b, ht0, h012b]
                                  ·
                                    rcases m.htr 2 3 5 (by decide) (by decide) with
                                      ⟨h235a, h235b, h235c⟩ | ⟨h235a, h235b, h235c⟩
                                    ·
                                      exfalso; linarith only [h145a, h023b, h134c, ht0, h045a, h123c, hc35b, ht5, hc01a, hp1, h034b, h235a, h012b]
                                    ·
                                      rcases m.htr 2 4 5 (by decide) (by decide) with
                                        ⟨h245a, h245b, h245c⟩ | ⟨h245a, h245b, h245c⟩
                                      ·
                                        exfalso; linarith only [h045a, ht34, hc01a, h124c, h123c, h145a, h023b, h134c, hp1, ht45, ht0, h245a, hc23b, h012b, h034b, ht5]
                                      ·
                                        rcases m.htr 3 4 5 (by decide) (by decide) with
                                          ⟨h345a, h345b, h345c⟩ | ⟨h345a, h345b, h345c⟩
                                        ·
                                          exfalso; linarith only [h123c, hc23b, hp1, hc34a, h134c, h145a, h345a]
                                        ·
                                          exfalso; linarith only [hc01a, h012b, h345a, h034b, h045a, h023b, h134a, hp1, ht34, hc23b, h123c, ht0, ht5, ht45]
                          ·
                            exfalso; linarith only [ht5, ht0, h025a, h123a, h125a, hp1, hc01a, ht45, ht34, hc23b, h012b]
                        ·
                          exfalso; linarith only [ht0, ht5, hc01a, h123a, hp1, h012b, h024a, h124a, ht45, hc23b, ht34]
                      ·
                        rcases m.htr 1 2 4 (by decide) (by decide) with
                          ⟨h124a, h124b, h124c⟩ | ⟨h124a, h124b, h124c⟩
                        ·
                          exfalso; linarith only [ht5, ht0, hp1, ht45, h023a, h124a, hc24b, h123a, h012b, hc01a]
                        ·
                          rcases m.htr 1 2 5 (by decide) (by decide) with
                            ⟨h125a, h125b, h125c⟩ | ⟨h125a, h125b, h125c⟩
                          ·
                            exfalso; linarith only [hc25b, hp1, h125a, ht5, ht0, h012b, h023a, h123a, hc01a]
                          ·
                            rcases m.htr 1 3 4 (by decide) (by decide) with
                              ⟨h134a, h134b, h134c⟩ | ⟨h134a, h134b, h134c⟩
                            ·
                              rcases m.htr 1 3 5 (by decide) (by decide) with
                                ⟨h135a, h135b, h135c⟩ | ⟨h135a, h135b, h135c⟩
                              ·
                                rcases m.htr 1 4 5 (by decide) (by decide) with
                                  ⟨h145a, h145b, h145c⟩ | ⟨h145a, h145b, h145c⟩
                                ·
                                  rcases m.htr 2 3 4 (by decide) (by decide) with
                                    ⟨h234a, h234b, h234c⟩ | ⟨h234a, h234b, h234c⟩
                                  ·
                                    rcases m.htr 2 3 5 (by decide) (by decide) with
                                      ⟨h235a, h235b, h235c⟩ | ⟨h235a, h235b, h235c⟩
                                    ·
                                      rcases m.htr 2 4 5 (by decide) (by decide) with
                                        ⟨h245a, h245b, h245c⟩ | ⟨h245a, h245b, h245c⟩
                                      ·
                                        rcases m.htr 3 4 5 (by decide) (by decide) with
                                          ⟨h345a, h345b, h345c⟩ | ⟨h345a, h345b, h345c⟩
                                        ·
                                          exfalso; linarith only [h134a, ht0, hc45b, hp1, h023a, hc01a, h012b, h123b, h345a, ht5]
                                        ·
                                          exfalso; linarith only [h123b, hc01a, hp1, h134b, ht5, h145a, ht0, h345a, h023a, h012b, hc34b, ht45]
                                      ·
                                        exfalso; linarith only [h234b, ht23, h124a, h123b, hp1, h145a, h023a, ht45, ht34, hc01a, hc12b, h012b, ht5, h245a, h134b, ht0]
                                    ·
                                      exfalso; linarith only [h023a, ht23, h123b, ht0, h124a, hc12b, h012b, hc01a, ht34, hp1, ht45, h234b, ht5, h135a, h235a]
                                  ·
                                    exfalso; linarith only [h234a, ht0, ht45, h123b, hp1, ht01, ht34, ht5, h134a, ht23, ht12]
                                ·
                                  rcases m.htr 2 3 4 (by decide) (by decide) with
                                    ⟨h234a, h234b, h234c⟩ | ⟨h234a, h234b, h234c⟩
                                  ·
                                    rcases m.htr 2 3 5 (by decide) (by decide) with
                                      ⟨h235a, h235b, h235c⟩ | ⟨h235a, h235b, h235c⟩
                                    ·
                                      rcases m.htr 2 4 5 (by decide) (by decide) with
                                        ⟨h245a, h245b, h245c⟩ | ⟨h245a, h245b, h245c⟩
                                      ·
                                        exfalso; linarith only [h023a, hc12b, h234b, hp1, h145a, h012b, ht45, h245a, h124c, ht5, ht23, ht0, ht34, hc01a]
                                      ·
                                        exfalso; linarith only [ht23, ht34, ht0, h045a, hc01a, hc12b, ht5, h034b, hp1, h012b, h124a, ht45, h023b, h245a]
                                    ·
                                      exfalso; linarith only [ht0, ht23, ht45, hc12b, h034b, h145a, hc01a, hp1, h045a, h123b, h124c, h235a, ht34, h135a, h023b, ht5, h012b]
                                  ·
                                    exfalso; linarith only [ht34, h234a, ht45, h123b, h034b, ht0, h145a, h134c, h023b, h012b, h045a, hp1, ht5, hc01a, hc13b]
                              ·
                                exfalso; linarith only [ht0, ht45, h134a, hp1, h023b, ht5, h012b, hc34b, h135a, h035a, hc01a]
                            ·
                              rcases m.htr 1 3 5 (by decide) (by decide) with
                                ⟨h135a, h135b, h135c⟩ | ⟨h135a, h135b, h135c⟩
                              ·
                                exfalso; linarith only [h134a, hc35b, h135a, ht5, hc01a, hp1, h034a, h023b, h012b, ht0]
                              ·
                                rcases m.htr 1 4 5 (by decide) (by decide) with
                                  ⟨h145a, h145b, h145c⟩ | ⟨h145a, h145b, h145c⟩
                                ·
                                  rcases m.htr 2 3 4 (by decide) (by decide) with
                                    ⟨h234a, h234b, h234c⟩ | ⟨h234a, h234b, h234c⟩
                                  ·
                                    exfalso; linarith only [h234a, ht0, h134a, h023a, ht34, hp1, ht23, h012b, hc01a, hc12b, ht5, h123c, ht45]
                                  ·
                                    exfalso; linarith only [h123a, h034a, ht5, hp1, hc01a, h023b, ht45, ht0, ht34, ht23, h234a, hc12b, h012b]
                                ·
                                  rcases m.htr 2 3 4 (by decide) (by decide) with
                                    ⟨h234a, h234b, h234c⟩ | ⟨h234a, h234b, h234c⟩
                                  ·
                                    exfalso; linarith only [h023a, ht0, h123c, ht34, ht45, h134a, hc12b, h012b, ht5, hp1, hc01a, ht23, h234a]
                                  ·
                                    exfalso; linarith only [hc01a, ht23, ht34, ht45, ht5, hp1, h012b, h023b, h234a, ht0, h034a, h123a, hc12b]
                    ·
                      rcases m.htr 1 2 3 (by decide) (by decide) with
                        ⟨h123a, h123b, h123c⟩ | ⟨h123a, h123b, h123c⟩
                      ·
                        rcases m.htr 1 2 4 (by decide) (by decide) with
                          ⟨h124a, h124b, h124c⟩ | ⟨h124a, h124b, h124c⟩
                        ·
                          rcases m.htr 1 2 5 (by decide) (by decide) with
                            ⟨h125a, h125b, h125c⟩ | ⟨h125a, h125b, h125c⟩
                          ·
                            rcases m.htr 1 3 4 (by decide) (by decide) with
                              ⟨h134a, h134b, h134c⟩ | ⟨h134a, h134b, h134c⟩
                            ·
                              rcases m.htr 1 3 5 (by decide) (by decide) with
                                ⟨h135a, h135b, h135c⟩ | ⟨h135a, h135b, h135c⟩
                              ·
                                rcases m.htr 1 4 5 (by decide) (by decide) with
                                  ⟨h145a, h145b, h145c⟩ | ⟨h145a, h145b, h145c⟩
                                ·
                                  exfalso; linarith only [ht23, h045a, h014c, ht01, hp1, ht34, ht12, h145a, ht45, ht0, ht5]
                                ·
                                  rcases m.htr 2 3 4 (by decide) (by decide) with
                                    ⟨h234a, h234b, h234c⟩ | ⟨h234a, h234b, h234c⟩
                                  ·
                                    exfalso; linarith only [hc01a, hp1, ht0, ht45, hc34b, ht5, h234a, h012a, h123a]
                                  ·
                                    exfalso; linarith only [h012a, hp1, h134a, h123b, ht45, hc23b, ht0, hc01a, ht34, h234a, ht5]
                              ·
                                exfalso; linarith only [h012b, h035a, ht5, h135a, hp1, ht45, h134a, ht0, hc34b, hc01a, h023b]
                            ·
                              exfalso; linarith only [h034c, h045a, hc13b, hp1, hc45a, h134a, ht34]
                          ·
                            exfalso; linarith only [h125a, hc01a, ht5, hc23b, hp1, ht34, h123a, h025a, ht0, h012b, ht45]
                        ·
                          exfalso; linarith only [ht23, hc45a, hp1, ht34, h024c, hc12b, h045a, h124a]
                      ·
                        rcases m.htr 1 2 4 (by decide) (by decide) with
                          ⟨h124a, h124b, h124c⟩ | ⟨h124a, h124b, h124c⟩
                        ·
                          exfalso; linarith only [h023a, hp1, ht45, h123a, hc01a, ht0, ht5, h124a, h012b, hc24b]
                        ·
                          exfalso; linarith only [ht34, h045a, hp1, hc12b, ht23, h124a, h024c, hc45a]
                  ·
                    rcases m.htr 0 4 5 (by decide) (by decide) with
                      ⟨h045a, h045b, h045c⟩ | ⟨h045a, h045b, h045c⟩
                    ·
                      exfalso; linarith only [h045b, h034b, h035c]
                    ·
                      rcases m.htr 1 2 3 (by decide) (by decide) with
                        ⟨h123a, h123b, h123c⟩ | ⟨h123a, h123b, h123c⟩
                      ·
                        rcases m.htr 1 2 4 (by decide) (by decide) with
                          ⟨h124a, h124b, h124c⟩ | ⟨h124a, h124b, h124c⟩
                        ·
                          rcases m.htr 1 2 5 (by decide) (by decide) with
                            ⟨h125a, h125b, h125c⟩ | ⟨h125a, h125b, h125c⟩
                          ·
                            rcases m.htr 1 3 4 (by decide) (by decide) with
                              ⟨h134a, h134b, h134c⟩ | ⟨h134a, h134b, h134c⟩
                            ·
                              rcases m.htr 1 3 5 (by decide) (by decide) with
                                ⟨h135a, h135b, h135c⟩ | ⟨h135a, h135b, h135c⟩
                              ·
                                exfalso; linarith only [hp1, h135a, h013c, h035a, ht12, ht0, ht45, hc35a, ht5, ht23, hc34b, ht01, h134a]
                              ·
                                rcases m.htr 1 4 5 (by decide) (by decide) with
                                  ⟨h145a, h145b, h145c⟩ | ⟨h145a, h145b, h145c⟩
                                ·
                                  exfalso; linarith only [h134a, h045a, ht45, hc34b, h145a, hp1, hc35a, h013c, ht23, ht01, h035a, ht0, ht12, h014c, ht5]
                                ·
                                  rcases m.htr 2 3 4 (by decide) (by decide) with
                                    ⟨h234a, h234b, h234c⟩ | ⟨h234a, h234b, h234c⟩
                                  ·
                                    exfalso; linarith only [ht0, h123a, ht45, h234a, hp1, h012a, hc34b, ht5, hc01a]
                                  ·
                                    exfalso; linarith only [ht01, hc34b, hc23b, h013c, hc35a, ht45, hp1, ht0, ht12, ht23, ht5, h134a, h035a, h234a]
                            ·
                              exfalso; linarith only [ht0, ht5, h034a, ht01, ht23, hp1, ht12, h035a, ht45, hc13b, ht34, h134a, hc35a]
                          ·
                            exfalso; linarith only [h123a, hc23b, hp1, h125a, ht45, hc01a, ht0, ht34, h025a, ht5, h012b]
                        ·
                          exfalso; linarith only [ht23, h034b, hc12b, hp1, h124a, h024c, h035a, hc35a]
                      ·
                        exfalso; linarith only [hp1, hc35a, ht23, h023c, h123a, h035a, hc12b]
                ·
                  rcases m.htr 0 3 5 (by decide) (by decide) with
                    ⟨h035a, h035b, h035c⟩ | ⟨h035a, h035b, h035c⟩
                  ·
                    rcases m.htr 0 4 5 (by decide) (by decide) with
                      ⟨h045a, h045b, h045c⟩ | ⟨h045a, h045b, h045c⟩
                    ·
                      rcases m.htr 1 2 3 (by decide) (by decide) with
                        ⟨h123a, h123b, h123c⟩ | ⟨h123a, h123b, h123c⟩
                      ·
                        rcases m.htr 1 2 4 (by decide) (by decide) with
                          ⟨h124a, h124b, h124c⟩ | ⟨h124a, h124b, h124c⟩
                        ·
                          rcases m.htr 1 2 5 (by decide) (by decide) with
                            ⟨h125a, h125b, h125c⟩ | ⟨h125a, h125b, h125c⟩
                          ·
                            rcases m.htr 1 3 4 (by decide) (by decide) with
                              ⟨h134a, h134b, h134c⟩ | ⟨h134a, h134b, h134c⟩
                            ·
                              exfalso; linarith only [ht45, h134a, ht12, hp1, ht5, ht23, h034a, ht0, h013c, ht01, ht34]
                            ·
                              rcases m.htr 1 3 5 (by decide) (by decide) with
                                ⟨h135a, h135b, h135c⟩ | ⟨h135a, h135b, h135c⟩
                              ·
                                rcases m.htr 1 4 5 (by decide) (by decide) with
                                  ⟨h145a, h145b, h145c⟩ | ⟨h145a, h145b, h145c⟩
                                ·
                                  rcases m.htr 2 3 4 (by decide) (by decide) with
                                    ⟨h234a, h234b, h234c⟩ | ⟨h234a, h234b, h234c⟩
                                  ·
                                    exfalso; linarith only [ht5, ht34, hp1, hc03b, h123a, ht23, h012a, hc01a, h034a, ht01, h234a, ht45, ht0, ht12]
                                  ·
                                    rcases m.htr 2 3 5 (by decide) (by decide) with
                                      ⟨h235a, h235b, h235c⟩ | ⟨h235a, h235b, h235c⟩
                                    ·
                                      exfalso; linarith only [hc01a, h234c, ht0, h012a, ht5, h124a, h235a, hp1, hc35b]
                                    ·
                                      exfalso; linarith only [hp1, ht01, ht34, ht12, hc34a, h235a, h013c, ht5, ht23, ht0, h034a, hc23b, ht45, h135a]
                                ·
                                  exfalso; linarith only [h045c, h034a, hc13b, h035b, hc34a, h134c, hp1, h145a]
                              ·
                                exfalso; linarith only [hp1, ht45, h135a, ht5, hc13b, ht34, ht12, hc34a, h035a, ht23, ht0, ht01, h034a]
                          ·
                            exfalso; linarith only [h035b, ht23, hc12b, h025c, h034a, hp1, hc34a, h125a]
                        ·
                          exfalso; linarith only [h124a, h123a, hp1, hc23b, ht45, hc01a, ht34, ht0, h012b, h024a, ht5]
                      ·
                        exfalso; linarith only [h123a, hp1, hc12b, h034a, h023c, ht23, hc34a]
                    ·
                      exfalso; linarith only [h035b, h045c, h034c]
                  ·
                    rcases m.htr 0 4 5 (by decide) (by decide) with
                      ⟨h045a, h045b, h045c⟩ | ⟨h045a, h045b, h045c⟩
                    ·
                      rcases m.htr 1 2 3 (by decide) (by decide) with
                        ⟨h123a, h123b, h123c⟩ | ⟨h123a, h123b, h123c⟩
                      ·
                        rcases m.htr 1 2 4 (by decide) (by decide) with
                          ⟨h124a, h124b, h124c⟩ | ⟨h124a, h124b, h124c⟩
                        ·
                          rcases m.htr 1 2 5 (by decide) (by decide) with
                            ⟨h125a, h125b, h125c⟩ | ⟨h125a, h125b, h125c⟩
                          ·
                            rcases m.htr 1 3 4 (by decide) (by decide) with
                              ⟨h134a, h134b, h134c⟩ | ⟨h134a, h134b, h134c⟩
                            ·
                              exfalso; linarith only [ht0, ht45, ht01, h134a, ht23, h034a, ht34, ht12, ht5, hp1, h013c]
                            ·
                              rcases m.htr 1 3 5 (by decide) (by decide) with
                                ⟨h135a, h135b, h135c⟩ | ⟨h135a, h135b, h135c⟩
                              ·
                                exfalso; linarith only [ht34, h035a, ht12, ht0, ht45, hp1, ht5, ht01, ht23, h135a, h013c]
                              ·
                                rcases m.htr 1 4 5 (by decide) (by decide) with
                                  ⟨h145a, h145b, h145c⟩ | ⟨h145a, h145b, h145c⟩
                                ·
                                  rcases m.htr 2 3 4 (by decide) (by decide) with
                                    ⟨h234a, h234b, h234c⟩ | ⟨h234a, h234b, h234c⟩
                                  ·
                                    exfalso; linarith only [ht34, h034a, hc03b, ht5, h123a, ht12, h012a, hp1, hc01a, ht01, h234a, ht45, ht0, ht23]
                                  ·
                                    rcases m.htr 2 3 5 (by decide) (by decide) with
                                      ⟨h235a, h235b, h235c⟩ | ⟨h235a, h235b, h235c⟩
                                    ·
                                      exfalso; linarith only [ht0, h012a, hc01a, h235a, h124a, ht5, hp1, hc35b, h234c]
                                    ·
                                      rcases m.htr 2 4 5 (by decide) (by decide) with
                                        ⟨h245a, h245b, h245c⟩ | ⟨h245a, h245b, h245c⟩
                                      ·
                                        exfalso; linarith only [ht5, hp1, h012a, ht0, h245a, hc45b, h124a, hc01a]
                                      ·
                                        exfalso; linarith only [hp1, h234c, h012a, hc23b, ht0, h145a, ht45, h245a, ht34, ht5, hc01a, h124b]
                                ·
                                  exfalso; linarith only [hc34a, h134c, hp1, h145a, h034b, hc13b, h045a]
                          ·
                            exfalso; linarith only [ht5, h125a, ht45, hp1, hc23b, ht0, h012b, h123a, ht34, h025a, hc01a]
                        ·
                          exfalso; linarith only [hc23b, ht5, hp1, ht34, ht45, h024a, h012b, h124a, ht0, h123a, hc01a]
                      ·
                        exfalso; linarith only [h123a, hp1, hc34a, h034a, ht23, h023c, hc12b]
                    ·
                      rcases m.htr 1 2 3 (by decide) (by decide) with
                        ⟨h123a, h123b, h123c⟩ | ⟨h123a, h123b, h123c⟩
                      ·
                        rcases m.htr 1 2 4 (by decide) (by decide) with
                          ⟨h124a, h124b, h124c⟩ | ⟨h124a, h124b, h124c⟩
                        ·
                          rcases m.htr 1 2 5 (by decide) (by decide) with
                            ⟨h125a, h125b, h125c⟩ | ⟨h125a, h125b, h125c⟩
                          ·
                            rcases m.htr 1 3 4 (by decide) (by decide) with
                              ⟨h134a, h134b, h134c⟩ | ⟨h134a, h134b, h134c⟩
                            ·
                              exfalso; linarith only [hp1, hc34b, h013c, h134a, h045a, h034c, hc45a]
                            ·
                              rcases m.htr 1 3 5 (by decide) (by decide) with
                                ⟨h135a, h135b, h135c⟩ | ⟨h135a, h135b, h135c⟩
                              ·
                                exfalso; linarith only [h045a, hc45a, ht23, h135a, ht01, ht12, ht5, hp1, ht0, h035a, h013c, ht34, hc35b, h034c]
                              ·
                                rcases m.htr 1 4 5 (by decide) (by decide) with
                                  ⟨h145a, h145b, h145c⟩ | ⟨h145a, h145b, h145c⟩
                                ·
                                  exfalso; linarith only [h045a, ht0, h145a, ht45, ht34, h014c, ht01, hp1, ht12, ht5, ht23]
                                ·
                                  rcases m.htr 2 3 4 (by decide) (by decide) with
                                    ⟨h234a, h234b, h234c⟩ | ⟨h234a, h234b, h234c⟩
                                  ·
                                    exfalso; linarith only [hp1, h123c, hc34b, hc45a, h234a, h034c, h013c, h045a]
                                  ·
                                    rcases m.htr 2 3 5 (by decide) (by decide) with
                                      ⟨h235a, h235b, h235c⟩ | ⟨h235a, h235b, h235c⟩
                                    ·
                                      exfalso; linarith only [h235a, hc45a, hc35b, ht01, ht34, hp1, ht5, ht12, ht23, h045a, h035a, h034c, ht0, h123c, h013c]
                                    ·
                                      rcases m.htr 2 4 5 (by decide) (by decide) with
                                        ⟨h245a, h245b, h245c⟩ | ⟨h245a, h245b, h245c⟩
                                      ·
                                        exfalso; linarith only [ht45, ht0, hc03b, h245a, hp1, h045a, ht5, h124a, h034c, ht34, ht23, h012a, hc01a, ht12, ht01]
                                      ·
                                        rcases m.htr 3 4 5 (by decide) (by decide) with
                                          ⟨h345a, h345b, h345c⟩ | ⟨h345a, h345b, h345c⟩
                                        ·
                                          exfalso; linarith only [hc03b, hp1, h045a, h345a, hc34a, h034c]
                                        ·
                                          exfalso; linarith only [h345a, ht34, hc03b, h034a, hp1, hc45a]
                          ·
                            exfalso; linarith only [ht5, h012b, ht45, h125a, h124a, hp1, h025a, ht0, hc01a, hc24b]
                        ·
                          exfalso; linarith only [hc45a, ht34, hc12b, h124a, h024c, hp1, h045a, ht23]
                      ·
                        exfalso; linarith only [hp1, h023c, ht34, h123a, hc12b, hc45a, h045a, h034c, ht23]
              ·
                rcases m.htr 0 3 4 (by decide) (by decide) with
                  ⟨h034a, h034b, h034c⟩ | ⟨h034a, h034b, h034c⟩
                ·
                  rcases m.htr 0 3 5 (by decide) (by decide) with
                    ⟨h035a, h035b, h035c⟩ | ⟨h035a, h035b, h035c⟩
                  ·
                    exfalso; linarith only [h035b, h023b, h025c]
                  ·
                    rcases m.htr 0 4 5 (by decide) (by decide) with
                      ⟨h045a, h045b, h045c⟩ | ⟨h045a, h045b, h045c⟩
                    ·
                      exfalso; linarith only [h034b, h025c, h045b, h023b]
                    ·
                      rcases m.htr 1 2 3 (by decide) (by decide) with
                        ⟨h123a, h123b, h123c⟩ | ⟨h123a, h123b, h123c⟩
                      ·
                        rcases m.htr 1 2 4 (by decide) (by decide) with
                          ⟨h124a, h124b, h124c⟩ | ⟨h124a, h124b, h124c⟩
                        ·
                          rcases m.htr 1 2 5 (by decide) (by decide) with
                            ⟨h125a, h125b, h125c⟩ | ⟨h125a, h125b, h125c⟩
                          ·
                            exfalso; linarith only [ht45, hc23b, ht34, ht5, h123a, hp1, ht0, hc25a, ht12, h025a, h012c, ht01, h125a]
                          ·
                            rcases m.htr 1 3 4 (by decide) (by decide) with
                              ⟨h134a, h134b, h134c⟩ | ⟨h134a, h134b, h134c⟩
                            ·
                              rcases m.htr 1 3 5 (by decide) (by decide) with
                                ⟨h135a, h135b, h135c⟩ | ⟨h135a, h135b, h135c⟩
                              ·
                                exfalso; linarith only [hc34b, ht01, h123a, h135a, ht5, hp1, ht12, hc23b, h013c, h025a, hc35a, hc25a, h134a, ht0, ht45, h035a, h012c]
                              ·
                                rcases m.htr 1 4 5 (by decide) (by decide) with
                                  ⟨h145a, h145b, h145c⟩ | ⟨h145a, h145b, h145c⟩
                                ·
                                  exfalso; linarith only [h013c, hc23b, h012c, hc35a, h014c, ht0, h123a, h035a, hc34b, ht45, h045a, h025a, ht12, hp1, h145a, h134a, hc25a, ht5, ht01]
                                ·
                                  rcases m.htr 2 3 4 (by decide) (by decide) with
                                    ⟨h234a, h234b, h234c⟩ | ⟨h234a, h234b, h234c⟩
                                  ·
                                    exfalso; linarith only [hc25a, ht5, h234a, h012c, ht0, h025a, h123a, hp1, ht45, hc34b, ht01, ht12]
                                  ·
                                    exfalso; linarith only [hc35a, hp1, hc34b, hc23b, h234a, h035a, ht45, h013c, h134a, h012c, ht12, h123a, hc25a, h025a, ht01, ht0, ht5]
                            ·
                              exfalso; linarith only [hc13b, ht34, ht0, ht45, h034a, hc35a, h035a, hp1, ht12, ht01, h025a, h134a, ht5, hc23b, hc25a, h123a, h012c]
                        ·
                          exfalso; linarith only [hc25a, hc23b, ht0, ht45, ht5, ht34, ht12, h123a, h124a, h025a, hp1, h024a, ht01, h012c]
                      ·
                        exfalso; linarith only [ht0, hc12b, ht5, h023a, hc25a, hp1, ht45, ht12, h123a, ht01, ht34, h025a, ht23]
                ·
                  rcases m.htr 0 3 5 (by decide) (by decide) with
                    ⟨h035a, h035b, h035c⟩ | ⟨h035a, h035b, h035c⟩
                  ·
                    exfalso; linarith only [h034c, h025c, h035b, h024b]
                  ·
                    rcases m.htr 0 4 5 (by decide) (by decide) with
                      ⟨h045a, h045b, h045c⟩ | ⟨h045a, h045b, h045c⟩
                    ·
                      exfalso; linarith only [h024b, h045b, h025c]
                    ·
                      rcases m.htr 1 2 3 (by decide) (by decide) with
                        ⟨h123a, h123b, h123c⟩ | ⟨h123a, h123b, h123c⟩
                      ·
                        rcases m.htr 1 2 4 (by decide) (by decide) with
                          ⟨h124a, h124b, h124c⟩ | ⟨h124a, h124b, h124c⟩
                        ·
                          rcases m.htr 1 2 5 (by decide) (by decide) with
                            ⟨h125a, h125b, h125c⟩ | ⟨h125a, h125b, h125c⟩
                          ·
                            exfalso; linarith only [hc25a, h012c, ht12, ht34, h025a, hc23b, h123a, ht5, hp1, ht01, h125a, ht45, ht0]
                          ·
                            rcases m.htr 1 3 4 (by decide) (by decide) with
                              ⟨h134a, h134b, h134c⟩ | ⟨h134a, h134b, h134c⟩
                            ·
                              exfalso; linarith only [h045a, hc45a, hp1, h134a, h013c, h034c, hc34b]
                            ·
                              rcases m.htr 1 3 5 (by decide) (by decide) with
                                ⟨h135a, h135b, h135c⟩ | ⟨h135a, h135b, h135c⟩
                              ·
                                exfalso; linarith only [ht01, hc35b, h135a, ht5, ht12, h045a, hp1, hc45a, hc23b, h123a, ht34, h013c, h035a, hc25a, h012c, h034c, h025a, ht0]
                              ·
                                rcases m.htr 1 4 5 (by decide) (by decide) with
                                  ⟨h145a, h145b, h145c⟩ | ⟨h145a, h145b, h145c⟩
                                ·
                                  exfalso; linarith only [ht5, ht12, h123a, h012c, hc23b, ht0, h145a, ht01, hp1, ht34, h045a, hc25a, h025a, ht45, h014c]
                                ·
                                  rcases m.htr 2 3 4 (by decide) (by decide) with
                                    ⟨h234a, h234b, h234c⟩ | ⟨h234a, h234b, h234c⟩
                                  ·
                                    exfalso; linarith only [ht0, ht45, ht5, h123a, h025a, hc25a, hp1, h234a, hc34b, ht12, ht01, h012c]
                                  ·
                                    rcases m.htr 2 3 5 (by decide) (by decide) with
                                      ⟨h235a, h235b, h235c⟩ | ⟨h235a, h235b, h235c⟩
                                    ·
                                      exfalso; linarith only [ht0, h012c, hc35b, hp1, ht12, h025a, ht01, h234c, hc25a, ht5, h124a, h235a]
                                    ·
                                      exfalso; linarith only [h234c, hc35a, h124a, hp1, hc23b, h012c, h025a, h235b]
                        ·
                          exfalso; linarith only [hc25a, h024a, ht45, hp1, ht34, ht01, h025a, h012c, ht0, ht5, hc23b, h124a, h123a, ht12]
                      ·
                        exfalso; linarith only [ht0, ht5, h023a, ht34, h123a, ht01, hp1, hc12b, ht45, hc25a, ht23, h025a, ht12]
            ·
              rcases m.htr 0 2 5 (by decide) (by decide) with
                ⟨h025a, h025b, h025c⟩ | ⟨h025a, h025b, h025c⟩
              ·
                rcases m.htr 0 3 4 (by decide) (by decide) with
                  ⟨h034a, h034b, h034c⟩ | ⟨h034a, h034b, h034c⟩
                ·
                  exfalso; linarith only [h034b, h023b, h024c]
                ·
                  rcases m.htr 0 3 5 (by decide) (by decide) with
                    ⟨h035a, h035b, h035c⟩ | ⟨h035a, h035b, h035c⟩
                  ·
                    rcases m.htr 0 4 5 (by decide) (by decide) with
                      ⟨h045a, h045b, h045c⟩ | ⟨h045a, h045b, h045c⟩
                    ·
                      rcases m.htr 1 2 3 (by decide) (by decide) with
                        ⟨h123a, h123b, h123c⟩ | ⟨h123a, h123b, h123c⟩
                      ·
                        rcases m.htr 1 2 4 (by decide) (by decide) with
                          ⟨h124a, h124b, h124c⟩ | ⟨h124a, h124b, h124c⟩
                        ·
                          exfalso; linarith only [h024a, hp1, h012c, ht12, ht34, ht0, ht01, hc23b, h124a, hc24a, ht45, ht5, h123a]
                        ·
                          rcases m.htr 1 2 5 (by decide) (by decide) with
                            ⟨h125a, h125b, h125c⟩ | ⟨h125a, h125b, h125c⟩
                          ·
                            rcases m.htr 1 3 4 (by decide) (by decide) with
                              ⟨h134a, h134b, h134c⟩ | ⟨h134a, h134b, h134c⟩
                            ·
                              exfalso; linarith only [ht12, ht45, hc23b, ht34, ht5, ht0, ht01, hc24a, h134a, h024a, h123a, hp1, h012c, h034a, h013c]
                            ·
                              rcases m.htr 1 3 5 (by decide) (by decide) with
                                ⟨h135a, h135b, h135c⟩ | ⟨h135a, h135b, h135c⟩
                              ·
                                rcases m.htr 1 4 5 (by decide) (by decide) with
                                  ⟨h145a, h145b, h145c⟩ | ⟨h145a, h145b, h145c⟩
                                ·
                                  rcases m.htr 2 3 4 (by decide) (by decide) with
                                    ⟨h234a, h234b, h234c⟩ | ⟨h234a, h234b, h234c⟩
                                  ·
                                    exfalso; linarith only [h012c, hc24a, ht0, h123a, h024a, h234a, hp1, hc03b, ht5, h034a, ht12, ht01, hc23b, ht34, ht45]
                                  ·
                                    exfalso; linarith only [hc23b, hp1, h234b, h024a, h012c, h123a, hc34a]
                                ·
                                  exfalso; linarith only [hc23b, h012c, h124c, h045c, ht45, ht0, hc14b, h034a, h024a, hc24a, ht12, hc34a, h035b, hp1, h145a, ht01, ht5, h123a]
                              ·
                                exfalso; linarith only [ht5, ht0, hc13b, hc23b, ht12, ht34, hc34a, hp1, hc24a, h024a, h123a, h135a, h034a, ht01, h012c, ht45, h035a]
                          ·
                            exfalso; linarith only [h123a, ht45, ht5, h024a, h012c, h125a, hc24a, hc23b, h025a, ht0, hp1, ht01, ht12, ht34]
                      ·
                        exfalso; linarith only [ht0, ht5, hc24a, ht01, h023a, hp1, h123a, ht12, ht34, h024a, hc12b, ht23, ht45]
                    ·
                      exfalso; linarith only [h024c, hp1, h045a, ht34, hc23b, hc45a, h023a]
                  ·
                    rcases m.htr 0 4 5 (by decide) (by decide) with
                      ⟨h045a, h045b, h045c⟩ | ⟨h045a, h045b, h045c⟩
                    ·
                      rcases m.htr 1 2 3 (by decide) (by decide) with
                        ⟨h123a, h123b, h123c⟩ | ⟨h123a, h123b, h123c⟩
                      ·
                        rcases m.htr 1 2 4 (by decide) (by decide) with
                          ⟨h124a, h124b, h124c⟩ | ⟨h124a, h124b, h124c⟩
                        ·
                          exfalso; linarith only [ht45, h123a, hc24a, ht34, h024a, ht01, h012c, hp1, hc23b, ht12, ht5, h124a, ht0]
                        ·
                          rcases m.htr 1 2 5 (by decide) (by decide) with
                            ⟨h125a, h125b, h125c⟩ | ⟨h125a, h125b, h125c⟩
                          ·
                            rcases m.htr 1 3 4 (by decide) (by decide) with
                              ⟨h134a, h134b, h134c⟩ | ⟨h134a, h134b, h134c⟩
                            ·
                              exfalso; linarith only [h035c, ht5, hp1, h045a, h024a, hc24a, hc45b, h134a, h013c, ht0, ht01, h034b, h025b, ht12]
                            ·
                              rcases m.htr 1 3 5 (by decide) (by decide) with
                                ⟨h135a, h135b, h135c⟩ | ⟨h135a, h135b, h135c⟩
                              ·
                                exfalso; linarith only [h024a, ht0, ht12, ht34, hc24a, h012c, hp1, h123a, ht45, ht5, h035a, h013c, h135a, ht01, hc23b]
                              ·
                                rcases m.htr 1 4 5 (by decide) (by decide) with
                                  ⟨h145a, h145b, h145c⟩ | ⟨h145a, h145b, h145c⟩
                                ·
                                  rcases m.htr 2 3 4 (by decide) (by decide) with
                                    ⟨h234a, h234b, h234c⟩ | ⟨h234a, h234b, h234c⟩
                                  ·
                                    exfalso; linarith only [hc24a, ht12, ht0, h234a, ht01, hc04b, hp1, h123a, h034b, ht5, h012c, ht45, h024a]
                                  ·
                                    exfalso; linarith only [h012c, h123a, hc34a, hp1, h234b, hc23b, h024a]
                                ·
                                  exfalso; linarith only [h024a, ht0, hc34a, h034b, h012c, h145a, ht01, hp1, h124c, ht12, hc23b, hc24a, h045a, ht45, ht5, h123a, hc14b]
                          ·
                            exfalso; linarith only [hc23b, ht0, h025a, h125a, ht45, ht12, ht5, ht01, h123a, hp1, ht34, h024a, h012c, hc24a]
                      ·
                        exfalso; linarith only [hc24a, ht0, hc12b, ht34, ht45, ht23, h123a, hp1, ht01, h023a, ht12, ht5, h024a]
                    ·
                      exfalso; linarith only [h023a, hp1, h045a, hc23b, ht34, hc45a, h024c]
              ·
                rcases m.htr 0 3 4 (by decide) (by decide) with
                  ⟨h034a, h034b, h034c⟩ | ⟨h034a, h034b, h034c⟩
                ·
                  exfalso; linarith only [h034b, h023b, h024c]
                ·
                  rcases m.htr 0 3 5 (by decide) (by decide) with
                    ⟨h035a, h035b, h035c⟩ | ⟨h035a, h035b, h035c⟩
                  ·
                    exfalso; linarith only [h035b, h023b, h025c]
                  ·
                    rcases m.htr 0 4 5 (by decide) (by decide) with
                      ⟨h045a, h045b, h045c⟩ | ⟨h045a, h045b, h045c⟩
                    ·
                      rcases m.htr 1 2 3 (by decide) (by decide) with
                        ⟨h123a, h123b, h123c⟩ | ⟨h123a, h123b, h123c⟩
                      ·
                        rcases m.htr 1 2 4 (by decide) (by decide) with
                          ⟨h124a, h124b, h124c⟩ | ⟨h124a, h124b, h124c⟩
                        ·
                          exfalso; linarith only [ht01, h124a, ht45, ht0, ht5, ht12, h123a, hc23b, h012c, h024a, hp1, ht34, hc24a]
                        ·
                          rcases m.htr 1 2 5 (by decide) (by decide) with
                            ⟨h125a, h125b, h125c⟩ | ⟨h125a, h125b, h125c⟩
                          ·
                            exfalso; linarith only [h125a, hc23b, ht45, h123a, ht0, hp1, hc24a, h012c, ht34, ht5, h024a, ht01, ht12, h025a]
                          ·
                            rcases m.htr 1 3 4 (by decide) (by decide) with
                              ⟨h134a, h134b, h134c⟩ | ⟨h134a, h134b, h134c⟩
                            ·
                              exfalso; linarith only [h034a, ht0, h134a, ht01, h123a, hp1, ht45, hc24a, h013c, h024a, hc23b, ht5, ht12, h012c, ht34]
                            ·
                              rcases m.htr 1 3 5 (by decide) (by decide) with
                                ⟨h135a, h135b, h135c⟩ | ⟨h135a, h135b, h135c⟩
                              ·
                                exfalso; linarith only [ht0, h012c, ht12, ht01, hc24a, ht45, hc23b, ht5, hp1, h013c, h024a, h135a, h123a, ht34, h035a]
                              ·
                                rcases m.htr 1 4 5 (by decide) (by decide) with
                                  ⟨h145a, h145b, h145c⟩ | ⟨h145a, h145b, h145c⟩
                                ·
                                  rcases m.htr 2 3 4 (by decide) (by decide) with
                                    ⟨h234a, h234b, h234c⟩ | ⟨h234a, h234b, h234c⟩
                                  ·
                                    exfalso; linarith only [h123a, hc23b, hc24a, ht45, ht0, ht01, hc03b, hp1, h234a, ht5, ht34, h024a, ht12, h012c, h034a]
                                  ·
                                    exfalso; linarith only [hc23b, h024a, hp1, h012c, h123a, hc34a, h234b]
                                ·
                                  exfalso; linarith only [hc24a, ht5, h024a, ht01, h123a, h124c, h045a, ht45, hc23b, h034b, ht0, hc14b, hp1, h145a, hc34a, ht12, h012c]
                      ·
                        exfalso; linarith only [h023a, ht0, ht5, ht12, ht34, ht45, hp1, ht23, h123a, ht01, hc24a, hc12b, h024a]
                    ·
                      exfalso; linarith only [ht34, h045a, h023a, hp1, h024c, hc45a, hc23b]
          ·
            rcases m.htr 0 2 4 (by decide) (by decide) with
              ⟨h024a, h024b, h024c⟩ | ⟨h024a, h024b, h024c⟩
            ·
              rcases m.htr 0 2 5 (by decide) (by decide) with
                ⟨h025a, h025b, h025c⟩ | ⟨h025a, h025b, h025c⟩
              ·
                rcases m.htr 0 3 4 (by decide) (by decide) with
                  ⟨h034a, h034b, h034c⟩ | ⟨h034a, h034b, h034c⟩
                ·
                  rcases m.htr 0 3 5 (by decide) (by decide) with
                    ⟨h035a, h035b, h035c⟩ | ⟨h035a, h035b, h035c⟩
                  ·
                    rcases m.htr 0 4 5 (by decide) (by decide) with
                      ⟨h045a, h045b, h045c⟩ | ⟨h045a, h045b, h045c⟩
                    ·
                      rcases m.htr 1 2 3 (by decide) (by decide) with
                        ⟨h123a, h123b, h123c⟩ | ⟨h123a, h123b, h123c⟩
                      ·
                        exfalso; linarith only [ht45, ht5, ht0, ht34, ht12, ht01, ht23, h023a, h012c, hp1, h123a]
                      ·
                        rcases m.htr 1 2 4 (by decide) (by decide) with
                          ⟨h124a, h124b, h124c⟩ | ⟨h124a, h124b, h124c⟩
                        ·
                          rcases m.htr 1 2 5 (by decide) (by decide) with
                            ⟨h125a, h125b, h125c⟩ | ⟨h125a, h125b, h125c⟩
                          ·
                            rcases m.htr 1 3 4 (by decide) (by decide) with
                              ⟨h134a, h134b, h134c⟩ | ⟨h134a, h134b, h134c⟩
                            ·
                              rcases m.htr 1 3 5 (by decide) (by decide) with
                                ⟨h135a, h135b, h135c⟩ | ⟨h135a, h135b, h135c⟩
                              ·
                                rcases m.htr 1 4 5 (by decide) (by decide) with
                                  ⟨h145a, h145b, h145c⟩ | ⟨h145a, h145b, h145c⟩
                                ·
                                  rcases m.htr 2 3 4 (by decide) (by decide) with
                                    ⟨h234a, h234b, h234c⟩ | ⟨h234a, h234b, h234c⟩
                                  ·
                                    rcases m.htr 2 3 5 (by decide) (by decide) with
                                      ⟨h235a, h235b, h235c⟩ | ⟨h235a, h235b, h235c⟩
                                    ·
                                      rcases m.htr 2 4 5 (by decide) (by decide) with
                                        ⟨h245a, h245b, h245c⟩ | ⟨h245a, h245b, h245c⟩
                                      ·
                                        exfalso; linarith only [ht5, hc45b, hc23a, ht12, ht01, hp1, h124a, h245a, h023a, h012c, ht0]
                                      ·
                                        exfalso; linarith only [ht12, h145a, h245a, hp1, h234c, ht45, hc23a, h023a, h024b, hc34b, ht0, h014c, ht01, ht5]
                                    ·
                                      exfalso; linarith only [ht0, hc34b, h234c, h135a, ht12, hp1, ht5, h124a, h235a, h013a, ht01, hc01a, hc23a, h023a, ht45, h012c]
                                  ·
                                    exfalso; linarith only [ht34, hc01a, ht23, ht01, ht0, h134a, ht45, ht12, h013a, h023a, ht5, h234a, hp1, hc02b]
                                ·
                                  exfalso; linarith only [ht01, ht0, h145a, hc23a, h024b, h045a, hp1, ht45, ht12, h023a, ht5, hc14b]
                              ·
                                exfalso; linarith only [ht12, h024b, h023a, hp1, ht0, h045b, hc34b, h135a, ht01, h035c, hc23a, ht45, ht5, h134a]
                            ·
                              exfalso; linarith only [h023a, h034c, hc12b, h123c, hc23a, h024b, hp1, h134a]
                          ·
                            exfalso; linarith only [ht01, hp1, h025a, h023a, ht5, ht23, ht12, hc23a, h125a, hc12b, ht45, ht0, ht34]
                        ·
                          exfalso; linarith only [ht12, h124a, h024a, hc23a, ht0, h023a, hp1, ht01, ht45, ht5, ht23, ht34, hc12b]
                    ·
                      rcases m.htr 1 2 3 (by decide) (by decide) with
                        ⟨h123a, h123b, h123c⟩ | ⟨h123a, h123b, h123c⟩
                      ·
                        exfalso; linarith only [hp1, h012c, ht34, h123a, ht45, ht23, ht0, ht01, ht12, ht5, h023a]
                      ·
                        rcases m.htr 1 2 4 (by decide) (by decide) with
                          ⟨h124a, h124b, h124c⟩ | ⟨h124a, h124b, h124c⟩
                        ·
                          rcases m.htr 1 2 5 (by decide) (by decide) with
                            ⟨h125a, h125b, h125c⟩ | ⟨h125a, h125b, h125c⟩
                          ·
                            rcases m.htr 1 3 4 (by decide) (by decide) with
                              ⟨h134a, h134b, h134c⟩ | ⟨h134a, h134b, h134c⟩
                            ·
                              rcases m.htr 1 3 5 (by decide) (by decide) with
                                ⟨h135a, h135b, h135c⟩ | ⟨h135a, h135b, h135c⟩
                              ·
                                rcases m.htr 1 4 5 (by decide) (by decide) with
                                  ⟨h145a, h145b, h145c⟩ | ⟨h145a, h145b, h145c⟩
                                ·
                                  exfalso; linarith only [ht5, ht45, h045a, hp1, ht12, ht34, ht0, h145a, ht23, ht01, h014c]
                                ·
                                  rcases m.htr 2 3 4 (by decide) (by decide) with
                                    ⟨h234a, h234b, h234c⟩ | ⟨h234a, h234b, h234c⟩
                                  ·
                                    rcases m.htr 2 3 5 (by decide) (by decide) with
                                      ⟨h235a, h235b, h235c⟩ | ⟨h235a, h235b, h235c⟩
                                    ·
                                      rcases m.htr 2 4 5 (by decide) (by decide) with
                                        ⟨h245a, h245b, h245c⟩ | ⟨h245a, h245b, h245c⟩
                                      ·
                                        exfalso; linarith only [hc34b, h045a, h012c, ht0, h124a, ht45, h234c, hp1, h023a, h245a, hc23a, ht5, hc04b, ht12, ht01]
                                      ·
                                        rcases m.htr 3 4 5 (by decide) (by decide) with
                                          ⟨h345a, h345b, h345c⟩ | ⟨h345a, h345b, h345c⟩
                                        ·
                                          exfalso; linarith only [hc34b, h345a, ht0, ht12, h023a, h245c, ht01, ht5, hp1, hc04b, h125a, ht45, h012c, h234c, h045a, hc23a]
                                        ·
                                          fin_cases i
                                          ·
                                            change linearGapScore m.lam (m.t 0) (m.t 0 + m.p) (m.rowxs 0) = 0
                                            have hpidx : (((List.finRange 6).erase (0 : Fin 6))).Perm
                                                ([1, 3, 2, 5, 4] : List (Fin 6)) := by decide
                                            have hperm := (m.row_perm 0).trans (hpidx.map (m.d 0))
                                            change (m.rowxs 0).Perm [m.d 0 1, m.d 0 3, m.d 0 2, m.d 0 5, m.d 0 4] at hperm
                                            have heq := hperm.eq_of_pairwise' (m.row_sorted _) (by
                                              simp only [List.pairwise_cons, List.mem_cons,
                                                List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, false_implies, implies_true, and_true, List.Pairwise.nil]
                                              (repeat' constructor) <;> linarith only [h012b, h013b, h014b, h015b, h023c, h024b, h025b, h034b, h035b, h045c])
                                            rw [heq]
                                            simp only [linearGapScore]
                                            rw [gapScore_zero_of_small m.hlam (by linarith only [ht12, ht0, ht45, ht23, hp1, ht01, ht34, hc01a, ht5]) (by linarith only [hp1, h245c, ht5, ht45, h012a, hc34b, h234c, ht0, h125a])]
                                            rw [gapScore_zero_of_small m.hlam (by linarith only [h013b]) (by linarith only [hc34b, h234c, ht45, h245c, hp1, h012c, ht0, h125a, h023c, hc01a, ht5])]
                                            rw [gapScore_zero_of_small m.hlam (by linarith only [h023c]) (by linarith only [h012c, hp1, ht5, ht12, h234c, h023b, ht0, hc34b, ht45, ht01, h125a, h245c, hc23a])]
                                            rw [gapScore_zero_of_small m.hlam (by linarith only [h025b]) (by linarith only [hc23a, ht12, ht0, hp1, ht01, ht5, h023a, hc05b])]
                                            rw [gapScore_zero_of_small m.hlam (by linarith only [h045c]) (by linarith only [ht01, hp1, hc04b, ht5, ht0, hc23a, ht45, ht12, h023a, h025b])]
                                            rw [gapScore_zero_of_small m.hlam (by linarith only [hp1, ht45, ht5, hc04b, ht0]) (by linarith only [h012c, ht01, hp1, h045a, hc45a, h245c, hc34b, h234c, h023a, ht12, h125a, hc23a])]
                                            try norm_num
                                          ·
                                            change linearGapScore m.lam (m.t 1) (m.t 1 + m.p) (m.rowxs 1) = 0
                                            have hpidx : (((List.finRange 6).erase (1 : Fin 6))).Perm
                                                ([0, 3, 2, 5, 4] : List (Fin 6)) := by decide
                                            have hperm := (m.row_perm 1).trans (hpidx.map (m.d 1))
                                            change (m.rowxs 1).Perm [m.d 1 0, m.d 1 3, m.d 1 2, m.d 1 5, m.d 1 4] at hperm
                                            rw [m.symm 1 0 (by decide)] at hperm
                                            have heq := hperm.eq_of_pairwise' (m.row_sorted _) (by
                                              simp only [List.pairwise_cons, List.mem_cons,
                                                List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, false_implies, implies_true, and_true, List.Pairwise.nil]
                                              (repeat' constructor) <;> linarith only [h012a, h012c, h013a, h014c, h015c, h023a, h025b, h045a, h123c, h124b, h125a, h125b, h134b, h135b, h145c, h234c, h245c, hc12b, hc13b, hc23a, hc34b, hc45a, hp1, ht0, ht01, ht12, ht23, ht34, ht45, ht5])
                                            rw [heq]
                                            simp only [linearGapScore]
                                            rw [gapScore_zero_of_small m.hlam (by linarith only [ht45, ht34, ht12, hp1, ht23, hc01a, ht5, ht0]) (by linarith only [ht5, h234c, h245c, hc34b, ht0, h012a, h125a, ht45, hp1, ht01])]
                                            rw [gapScore_zero_of_small m.hlam (by linarith only [ht01, hp1, ht5, ht34, h013a, ht12, ht0, ht23, ht45]) (by linarith only [hp1, h123c, h234c, ht45, h245c, h125a, ht5, hc01a, hc34b, ht0])]
                                            rw [gapScore_zero_of_small m.hlam (by linarith only [h123c]) (by linarith only [h012c, ht5, hc01a, h125a, ht0, hc34b, hp1, ht45, h013a, hc23a, h023a, h245c, ht12, ht01, h234c])]
                                            rw [gapScore_zero_of_small m.hlam (by linarith only [h125b]) (by linarith only [ht01, hc15b, h012c, hp1, ht12, h023a, hc23a, ht0, ht5])]
                                            rw [gapScore_zero_of_small m.hlam (by linarith only [h145c]) (by linarith only [ht12, hc23a, hc14b, ht01, ht5, ht0, h025b, ht45, hp1, h023a, h015c])]
                                            rw [gapScore_zero_of_small m.hlam (by linarith only [ht0, hp1, hc14b, ht45, ht5, ht01]) (by linarith only [ht12, h125a, h012c, hc23a, hc45a, h245c, h234c, h014c, hc34b, h045a, hp1, h023a])]
                                            try norm_num
                                          ·
                                            change linearGapScore m.lam (m.t 2) (m.t 2 + m.p) (m.rowxs 2) = 0
                                            have hpidx : (((List.finRange 6).erase (2 : Fin 6))).Perm
                                                ([3, 0, 1, 5, 4] : List (Fin 6)) := by decide
                                            have hperm := (m.row_perm 2).trans (hpidx.map (m.d 2))
                                            change (m.rowxs 2).Perm [m.d 2 3, m.d 2 0, m.d 2 1, m.d 2 5, m.d 2 4] at hperm
                                            rw [m.symm 2 0 (by decide)] at hperm
                                            rw [m.symm 2 1 (by decide)] at hperm
                                            have heq := hperm.eq_of_pairwise' (m.row_sorted _) (by
                                              simp only [List.pairwise_cons, List.mem_cons,
                                                List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, false_implies, implies_true, and_true, List.Pairwise.nil]
                                              (repeat' constructor) <;> linarith only [h012c, h023a, h125a, h234b, h234c, h235b, h245c, hc23a, hc34b, hp1, ht0, ht01, ht12, ht23, ht34, ht45, ht5])
                                            rw [heq]
                                            simp only [linearGapScore]
                                            rw [gapScore_zero_of_small m.hlam (by linarith only [hc23a, ht45, h012c, h234c, h245c, ht01, ht0, ht5, hp1, hc34b, ht12, h023a, h125a]) (by linarith only [ht01, ht45, h245c, ht12, h125a, ht0, hc34b, hp1, h234c, ht5, h012c, h023a])]
                                            rw [gapScore_zero_of_small m.hlam (by linarith only [hp1, ht5, h125a, hc23a, ht01, hc34b, h012c, h234c, h245c, h023a, ht12, ht45, ht0]) (by linarith only [h234c, h012c, ht0, hc34b, hp1, ht5, ht45, ht01, h125a, ht12, hc23a, h245c])]
                                            rw [gapScore_zero_of_small m.hlam (by linarith only [h012c]) (by linarith only [ht0, ht01, h012c, hc34b, h125a, ht12, ht5, hc23a, hp1, h245c, h023a, ht45, h234c])]
                                            rw [gapScore_zero_of_small m.hlam (by linarith only [ht0, ht5, ht12, hp1, ht01, hc23a, ht45, h245c, hc34b, h023a, h125a, h234c, h012c]) (by linarith only [h234c, ht45, h245c, h012c, ht5, hp1, hc34b, ht12, ht0, h023a, ht01, hc23a])]
                                            rw [gapScore_zero_of_small m.hlam (by linarith only [h245c]) (by linarith only [h125a, hc34b, ht01, h245c, h012c, ht5, ht12, ht45, h023a, ht0, hp1, hc23a, h234c])]
                                            rw [gapScore_zero_of_small m.hlam (by linarith only [hp1, ht5, ht01, ht0, hc24b, ht45, ht12]) (by linarith only [h234c, h012c, ht01, ht0, hc34b, h245c, hc23a, ht45, h023a, hp1, h125a, ht12, ht5])]
                                            try norm_num
                                          ·
                                            change linearGapScore m.lam (m.t 3) (m.t 3 + m.p) (m.rowxs 3) = 0
                                            have hpidx : (((List.finRange 6).erase (3 : Fin 6))).Perm
                                                ([2, 0, 1, 5, 4] : List (Fin 6)) := by decide
                                            have hperm := (m.row_perm 3).trans (hpidx.map (m.d 3))
                                            change (m.rowxs 3).Perm [m.d 3 2, m.d 3 0, m.d 3 1, m.d 3 5, m.d 3 4] at hperm
                                            rw [m.symm 3 2 (by decide)] at hperm
                                            rw [m.symm 3 0 (by decide)] at hperm
                                            rw [m.symm 3 1 (by decide)] at hperm
                                            have heq := hperm.eq_of_pairwise' (m.row_sorted _) (by
                                              simp only [List.pairwise_cons, List.mem_cons,
                                                List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, false_implies, implies_true, and_true, List.Pairwise.nil]
                                              (repeat' constructor) <;> linarith only [h012c, h013c, h023a, h023b, h023c, h035a, h123b, h123c, h125a, h234c, h235c, h245c, h345c, hc13b, hc23a, hc34b, hp1, ht0, ht01, ht12, ht23, ht34, ht45, ht5])
                                            rw [heq]
                                            simp only [linearGapScore]
                                            rw [gapScore_zero_of_small m.hlam (by linarith only [ht5, hc23a, ht34, hp1, ht45, ht12, ht01, ht0]) (by linarith only [hp1, h012c, h234c, h125a, ht01, ht12, ht0, ht5, h023a, ht23, ht45, hc34b, h245c])]
                                            rw [gapScore_zero_of_small m.hlam (by linarith only [h023b]) (by linarith only [hc23a, h245c, ht0, h012c, ht01, hp1, ht45, ht5, h234c, ht12, h125a, hc34b, h023c])]
                                            rw [gapScore_zero_of_small m.hlam (by linarith only [h013c]) (by linarith only [ht12, hc23a, ht01, hc34b, hp1, ht5, h234c, h123c, h245c, ht0, h023b, ht45, h125a])]
                                            rw [gapScore_zero_of_small m.hlam (by linarith only [ht5, hc23a, h235c, h125a, ht34, hp1, ht0, ht45, h023a, h012c, hc13b, ht12, ht01, h123c]) (by linarith only [ht5, hc01a, hp1, ht0, h013a, hc35b])]
                                            rw [gapScore_zero_of_small m.hlam (by linarith only [h345c]) (by linarith only [hp1, h012c, ht01, h023a, h235c, ht12, hc34b, h245c, ht5, h125a, ht45, h234c, ht0, hc23a])]
                                            rw [gapScore_zero_of_small m.hlam (by linarith only [ht0, ht5, ht23, hp1, ht01, ht12, ht45, hc34b]) (by linarith only [h023a, hc23a, ht34, ht01, h245c, ht5, h234c, h012c, h125a, ht45, ht0, ht12, hp1])]
                                            try norm_num
                                          ·
                                            change linearGapScore m.lam (m.t 4) (m.t 4 + m.p) (m.rowxs 4) = 0
                                            have hpidx : (((List.finRange 6).erase (4 : Fin 6))).Perm
                                                ([5, 0, 1, 2, 3] : List (Fin 6)) := by decide
                                            have hperm := (m.row_perm 4).trans (hpidx.map (m.d 4))
                                            change (m.rowxs 4).Perm [m.d 4 5, m.d 4 0, m.d 4 1, m.d 4 2, m.d 4 3] at hperm
                                            rw [m.symm 4 0 (by decide)] at hperm
                                            rw [m.symm 4 1 (by decide)] at hperm
                                            rw [m.symm 4 2 (by decide)] at hperm
                                            rw [m.symm 4 3 (by decide)] at hperm
                                            have heq := hperm.eq_of_pairwise' (m.row_sorted _) (by
                                              simp only [List.pairwise_cons, List.mem_cons,
                                                List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, false_implies, implies_true, and_true, List.Pairwise.nil]
                                              (repeat' constructor) <;> linarith only [h012c, h014c, h023a, h024c, h034c, h045a, h124c, h125a, h134c, h234c, h245c, hc04b, hc23a, hc34b, hp1, ht0, ht01, ht12, ht23, ht34, ht45, ht5])
                                            rw [heq]
                                            simp only [linearGapScore]
                                            rw [gapScore_zero_of_small m.hlam (by linarith only [h012c, hc34b, h023a, ht5, hc45a, h234c, ht12, hp1, h125a, hc23a, ht01, h245c, ht45, ht0]) (by linarith only [h045a, hc04b, hp1])]
                                            rw [gapScore_zero_of_small m.hlam (by linarith only [h125a, h012c, ht12, ht01, h234c, hc23a, hc34b, ht0, ht5, h023a, h045a, ht45, hp1, h245c]) (by linarith only [hc04b, hp1, hc45a])]
                                            rw [gapScore_zero_of_small m.hlam (by linarith only [h014c]) (by linarith only [ht45, ht12, hc23a, hp1, ht0, h125a, h245c, hc34b, ht01, hc45a, h023a, hc14b, h045a, ht5, h012c, h234c])]
                                            rw [gapScore_zero_of_small m.hlam (by linarith only [h124c]) (by linarith only [ht01, hc23a, h234c, h125a, ht0, hc34b, h245c, h012c, h023a, ht12, ht5, hp1, ht45, h014c, h045a, hc45a])]
                                            rw [gapScore_zero_of_small m.hlam (by linarith only [h234c]) (by linarith only [hc23a, h245c, ht45, h023a, h012c, hc34b, ht5, ht01, ht12, hp1, h234c, h125a, ht0])]
                                            rw [gapScore_zero_of_small m.hlam (by linarith only [ht5, ht34, ht23, ht0, hp1, ht01, ht45, ht12, hc34b]) (by linarith only [ht12, ht5, hp1, h023a, h012c, hc23a, h245c, h234c, ht45, h125a, ht01, ht0])]
                                            try norm_num
                                          ·
                                            change linearGapScore m.lam (m.t 5) (m.t 5 + m.p) (m.rowxs 5) = 0
                                            have hpidx : (((List.finRange 6).erase (5 : Fin 6))).Perm
                                                ([4, 0, 1, 2, 3] : List (Fin 6)) := by decide
                                            have hperm := (m.row_perm 5).trans (hpidx.map (m.d 5))
                                            change (m.rowxs 5).Perm [m.d 5 4, m.d 5 0, m.d 5 1, m.d 5 2, m.d 5 3] at hperm
                                            rw [m.symm 5 4 (by decide)] at hperm
                                            rw [m.symm 5 0 (by decide)] at hperm
                                            rw [m.symm 5 1 (by decide)] at hperm
                                            rw [m.symm 5 2 (by decide)] at hperm
                                            rw [m.symm 5 3 (by decide)] at hperm
                                            have heq := hperm.eq_of_pairwise' (m.row_sorted _) (by
                                              simp only [List.pairwise_cons, List.mem_cons,
                                                List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, false_implies, implies_true, and_true, List.Pairwise.nil]
                                              (repeat' constructor) <;> linarith only [h015c, h025c, h035c, h045b, h125c, h135c, h145b, h235c, h245b, h345b])
                                            rw [heq]
                                            simp only [linearGapScore]
                                            rw [gapScore_zero_of_small m.hlam (by linarith only [ht01, ht0, ht5, hp1, ht12, hc45a, ht34, ht23]) (by linarith only [hp1, hc04b, ht45, h045a])]
                                            rw [gapScore_zero_of_small m.hlam (by linarith only [h045b]) (by linarith only [hp1, h025c, hc34b, h234c, h245c, hc45a])]
                                            rw [gapScore_zero_of_small m.hlam (by linarith only [h015c]) (by linarith only [hp1, h025b, h023a, ht5, ht12, ht01, ht0, hc15b, hc23a])]
                                            rw [gapScore_zero_of_small m.hlam (by linarith only [h125c]) (by linarith only [h245c, h023a, h234c, h025b, h015c, hp1, ht01, hc34b, ht45, ht12, ht0, hc23a, ht5])]
                                            rw [gapScore_zero_of_small m.hlam (by linarith only [h235c]) (by linarith only [hp1, ht01, hc34b, ht0, ht12, h023a, h012c, ht45, h125a, hc23a, h234c, hc35b, ht5, h245c])]
                                            rw [gapScore_zero_of_small m.hlam (by linarith only [ht01, ht34, hp1, hc35b, ht45, ht23, ht0, ht5, ht12]) (by linarith only [hp1, h012c, hc23a, h235c, h125a, ht01, h023a, ht0, ht5, ht12])]
                                            try norm_num
                                    ·
                                      exfalso; linarith only [hc34b, hc01a, ht45, h013a, ht01, hp1, ht5, h012c, h135a, h235a, h234c, h023a, ht0, hc23a, h124a, ht12]
                                  ·
                                    exfalso; linarith only [h134a, ht0, hc02b, ht12, ht23, h023a, ht01, ht34, hp1, ht5, h013a, h234a, hc01a, ht45]
                              ·
                                exfalso; linarith only [ht0, hc34b, ht5, ht12, h135a, hc23a, h025b, h023a, ht01, hp1, ht45, h134a, h035c]
                            ·
                              exfalso; linarith only [h045a, h034c, h134a, hc13b, hp1, ht34, hc45a]
                          ·
                            exfalso; linarith only [ht45, ht5, ht0, hc12b, h125a, h025a, ht12, ht01, hp1, ht34, ht23, h023a, hc23a]
                        ·
                          exfalso; linarith only [ht12, ht34, ht45, h024a, ht01, ht5, hp1, ht0, ht23, h124a, h023a, hc23a, hc12b]
                  ·
                    exfalso; linarith only [h023c, h035c, h025b]
                ·
                  exfalso; linarith only [h024b, h023c, h034c]
              ·
                rcases m.htr 0 3 4 (by decide) (by decide) with
                  ⟨h034a, h034b, h034c⟩ | ⟨h034a, h034b, h034c⟩
                ·
                  rcases m.htr 0 3 5 (by decide) (by decide) with
                    ⟨h035a, h035b, h035c⟩ | ⟨h035a, h035b, h035c⟩
                  ·
                    rcases m.htr 0 4 5 (by decide) (by decide) with
                      ⟨h045a, h045b, h045c⟩ | ⟨h045a, h045b, h045c⟩
                    ·
                      exfalso; linarith only [h025c, h045b, h024b]
                    ·
                      rcases m.htr 1 2 3 (by decide) (by decide) with
                        ⟨h123a, h123b, h123c⟩ | ⟨h123a, h123b, h123c⟩
                      ·
                        exfalso; linarith only [ht01, ht5, ht0, ht34, ht23, ht45, h123a, h012c, ht12, h023a, hp1]
                      ·
                        rcases m.htr 1 2 4 (by decide) (by decide) with
                          ⟨h124a, h124b, h124c⟩ | ⟨h124a, h124b, h124c⟩
                        ·
                          rcases m.htr 1 2 5 (by decide) (by decide) with
                            ⟨h125a, h125b, h125c⟩ | ⟨h125a, h125b, h125c⟩
                          ·
                            exfalso; linarith only [ht12, hp1, ht01, ht34, ht23, ht0, ht5, h025a, h125a, ht45, h012c]
                          ·
                            rcases m.htr 1 3 4 (by decide) (by decide) with
                              ⟨h134a, h134b, h134c⟩ | ⟨h134a, h134b, h134c⟩
                            ·
                              rcases m.htr 1 3 5 (by decide) (by decide) with
                                ⟨h135a, h135b, h135c⟩ | ⟨h135a, h135b, h135c⟩
                              ·
                                rcases m.htr 1 4 5 (by decide) (by decide) with
                                  ⟨h145a, h145b, h145c⟩ | ⟨h145a, h145b, h145c⟩
                                ·
                                  exfalso; linarith only [ht34, h045a, hp1, ht23, ht12, ht01, ht0, ht45, h014c, h145a, ht5]
                                ·
                                  rcases m.htr 2 3 4 (by decide) (by decide) with
                                    ⟨h234a, h234b, h234c⟩ | ⟨h234a, h234b, h234c⟩
                                  ·
                                    rcases m.htr 2 3 5 (by decide) (by decide) with
                                      ⟨h235a, h235b, h235c⟩ | ⟨h235a, h235b, h235c⟩
                                    ·
                                      rcases m.htr 2 4 5 (by decide) (by decide) with
                                        ⟨h245a, h245b, h245c⟩ | ⟨h245a, h245b, h245c⟩
                                      ·
                                        exfalso; linarith only [h235b, h234c, h124a, h012c, h045a, ht01, hp1, ht45, hc04b, ht5, ht0, hc23a, ht12, h245a, h025a, hc34b]
                                      ·
                                        exfalso; linarith only [hc45a, h012c, h245b, hp1, h234c, h025a, h124a, hc34b]
                                    ·
                                      exfalso; linarith only [h013a, h012c, h124a, h023a, hc34b, hp1, ht5, ht01, h235a, h234c, hc23a, ht0, h135a, ht12, ht45, hc01a]
                                  ·
                                    exfalso; linarith only [ht0, ht34, h134a, ht45, hp1, h023a, ht12, hc01a, ht01, ht23, h013a, ht5, h234a, hc02b]
                              ·
                                exfalso; linarith only [hc34b, ht0, hc23a, ht12, ht5, hp1, ht45, h035a, h023b, ht01, h135a, h134a]
                            ·
                              exfalso; linarith only [hc13b, h045a, h034c, hc45a, hp1, h134a, ht34]
                        ·
                          exfalso; linarith only [h024a, ht23, hc12b, h023a, ht45, ht34, ht12, ht01, ht5, hp1, h124a, ht0, hc23a]
                  ·
                    rcases m.htr 0 4 5 (by decide) (by decide) with
                      ⟨h045a, h045b, h045c⟩ | ⟨h045a, h045b, h045c⟩
                    ·
                      exfalso; linarith only [h025c, h024b, h045b]
                    ·
                      rcases m.htr 1 2 3 (by decide) (by decide) with
                        ⟨h123a, h123b, h123c⟩ | ⟨h123a, h123b, h123c⟩
                      ·
                        exfalso; linarith only [h023c, hc23b, h123a, h035a, hc35a, h012c, hp1]
                      ·
                        rcases m.htr 1 2 4 (by decide) (by decide) with
                          ⟨h124a, h124b, h124c⟩ | ⟨h124a, h124b, h124c⟩
                        ·
                          rcases m.htr 1 2 5 (by decide) (by decide) with
                            ⟨h125a, h125b, h125c⟩ | ⟨h125a, h125b, h125c⟩
                          ·
                            exfalso; linarith only [ht01, h025a, h023c, ht0, ht23, h012c, ht12, h035a, hc35a, hp1, hc24b, h125a, ht45, ht5, h124a]
                          ·
                            rcases m.htr 1 3 4 (by decide) (by decide) with
                              ⟨h134a, h134b, h134c⟩ | ⟨h134a, h134b, h134c⟩
                            ·
                              rcases m.htr 1 3 5 (by decide) (by decide) with
                                ⟨h135a, h135b, h135c⟩ | ⟨h135a, h135b, h135c⟩
                              ·
                                exfalso; linarith only [hc24b, h124a, ht0, ht45, h035a, ht01, h023c, ht12, h135a, ht23, hp1, h013c, hc35a, ht5, h012c]
                              ·
                                rcases m.htr 1 4 5 (by decide) (by decide) with
                                  ⟨h145a, h145b, h145c⟩ | ⟨h145a, h145b, h145c⟩
                                ·
                                  exfalso; linarith only [ht5, ht0, ht01, h035a, hp1, h014c, h124a, ht45, h012c, hc24b, h145a, ht12, h023c, ht23, hc35a, h045a]
                                ·
                                  rcases m.htr 2 3 4 (by decide) (by decide) with
                                    ⟨h234a, h234b, h234c⟩ | ⟨h234a, h234b, h234c⟩
                                  ·
                                    rcases m.htr 2 3 5 (by decide) (by decide) with
                                      ⟨h235a, h235b, h235c⟩ | ⟨h235a, h235b, h235c⟩
                                    ·
                                      exfalso; linarith only [ht01, ht0, ht12, h234c, h023c, h124a, hp1, h035a, ht5, h012c, h235a, ht45, hc34b, hc23a]
                                    ·
                                      exfalso; linarith only [hc35a, ht0, h023a, h234c, h012c, ht01, hp1, hc34b, ht23, ht12, ht45, ht5, h235a, h124a]
                                  ·
                                    exfalso; linarith only [ht0, ht12, h035a, ht01, h234a, hc24b, h012c, hc23b, h134a, hc35a, ht23, hp1, ht45, h124a, h023c, h013c, ht5]
                            ·
                              exfalso; linarith only [hc24b, ht0, h034a, ht5, h124a, ht01, hc35a, ht45, h012c, hp1, h134a, h023c, ht12, h035a, ht23, hc13b]
                        ·
                          exfalso; linarith only [ht23, ht5, hc35a, hc12b, ht0, h023c, ht12, hp1, h024a, h124a, ht01, ht45, h035a, hc24b]
                ·
                  exfalso; linarith only [h024b, h034c, h023c]
            ·
              rcases m.htr 0 2 5 (by decide) (by decide) with
                ⟨h025a, h025b, h025c⟩ | ⟨h025a, h025b, h025c⟩
              ·
                rcases m.htr 0 3 4 (by decide) (by decide) with
                  ⟨h034a, h034b, h034c⟩ | ⟨h034a, h034b, h034c⟩
                ·
                  rcases m.htr 0 3 5 (by decide) (by decide) with
                    ⟨h035a, h035b, h035c⟩ | ⟨h035a, h035b, h035c⟩
                  ·
                    rcases m.htr 0 4 5 (by decide) (by decide) with
                      ⟨h045a, h045b, h045c⟩ | ⟨h045a, h045b, h045c⟩
                    ·
                      rcases m.htr 1 2 3 (by decide) (by decide) with
                        ⟨h123a, h123b, h123c⟩ | ⟨h123a, h123b, h123c⟩
                      ·
                        exfalso; linarith only [ht12, h023a, h123a, hp1, ht23, ht01, h012c, ht34, ht45, ht0, ht5]
                      ·
                        rcases m.htr 1 2 4 (by decide) (by decide) with
                          ⟨h124a, h124b, h124c⟩ | ⟨h124a, h124b, h124c⟩
                        ·
                          exfalso; linarith only [ht23, ht12, ht34, h012c, h124a, ht0, ht5, hp1, h024a, ht45, ht01]
                        ·
                          rcases m.htr 1 2 5 (by decide) (by decide) with
                            ⟨h125a, h125b, h125c⟩ | ⟨h125a, h125b, h125c⟩
                          ·
                            rcases m.htr 1 3 4 (by decide) (by decide) with
                              ⟨h134a, h134b, h134c⟩ | ⟨h134a, h134b, h134c⟩
                            ·
                              rcases m.htr 1 3 5 (by decide) (by decide) with
                                ⟨h135a, h135b, h135c⟩ | ⟨h135a, h135b, h135c⟩
                              ·
                                rcases m.htr 1 4 5 (by decide) (by decide) with
                                  ⟨h145a, h145b, h145c⟩ | ⟨h145a, h145b, h145c⟩
                                ·
                                  rcases m.htr 2 3 4 (by decide) (by decide) with
                                    ⟨h234a, h234b, h234c⟩ | ⟨h234a, h234b, h234c⟩
                                  ·
                                    rcases m.htr 2 3 5 (by decide) (by decide) with
                                      ⟨h235a, h235b, h235c⟩ | ⟨h235a, h235b, h235c⟩
                                    ·
                                      rcases m.htr 2 4 5 (by decide) (by decide) with
                                        ⟨h245a, h245b, h245c⟩ | ⟨h245a, h245b, h245c⟩
                                      ·
                                        rcases m.htr 3 4 5 (by decide) (by decide) with
                                          ⟨h345a, h345b, h345c⟩ | ⟨h345a, h345b, h345c⟩
                                        ·
                                          exfalso; linarith only [h134a, h013a, hp1, ht5, h345a, ht0, hc45b, hc01a]
                                        ·
                                          exfalso; linarith only [hp1, h012c, h245c, hc34b, h125a, ht5, ht45, h345a, ht12, ht0, ht01, h024a, hc23a, h234b]
                                      ·
                                        exfalso; linarith only [ht0, h145a, h024a, h125a, ht12, h235c, hc23a, ht01, hp1, h134b, h234b, ht5, h245a, h013a, hc01a, h012c, hc35b]
                                    ·
                                      exfalso; linarith only [h235a, ht0, ht5, ht01, ht12, ht23, h013a, hp1, ht34, h024a, h234b, ht45, h135a, hc01a, hc02b]
                                  ·
                                    exfalso; linarith only [hc01a, h013a, ht0, ht12, h023a, h234a, ht23, h134a, ht45, ht01, hp1, hc02b, ht34, ht5]
                                ·
                                  exfalso; linarith only [h145a, hc23a, h124c, h034b, hp1, h023b, hc12b, h045a]
                              ·
                                exfalso; linarith only [hp1, ht01, hc34b, h035c, h023a, ht45, h135a, ht0, h025b, ht5, ht12, hc23a, h134a]
                            ·
                              exfalso; linarith only [hc12b, h023b, h134a, hc23a, h034a, h123c, hp1]
                          ·
                            exfalso; linarith only [ht5, hc12b, hp1, ht34, h125a, ht0, ht01, ht45, ht12, h025a, ht23, h023a, hc23a]
                    ·
                      exfalso; linarith only [h024c, h025b, h045c]
                  ·
                    exfalso; linarith only [h035c, h025b, h024c, h034b]
                ·
                  rcases m.htr 0 3 5 (by decide) (by decide) with
                    ⟨h035a, h035b, h035c⟩ | ⟨h035a, h035b, h035c⟩
                  ·
                    rcases m.htr 0 4 5 (by decide) (by decide) with
                      ⟨h045a, h045b, h045c⟩ | ⟨h045a, h045b, h045c⟩
                    ·
                      rcases m.htr 1 2 3 (by decide) (by decide) with
                        ⟨h123a, h123b, h123c⟩ | ⟨h123a, h123b, h123c⟩
                      ·
                        exfalso; linarith only [hp1, h123a, h012c, h034a, hc34a, hc23b, h023c]
                      ·
                        rcases m.htr 1 2 4 (by decide) (by decide) with
                          ⟨h124a, h124b, h124c⟩ | ⟨h124a, h124b, h124c⟩
                        ·
                          exfalso; linarith only [hc24b, ht45, ht01, ht12, hp1, h012c, hc34a, ht5, h124a, h024a, ht0, h034a, ht23, h023c]
                        ·
                          rcases m.htr 1 2 5 (by decide) (by decide) with
                            ⟨h125a, h125b, h125c⟩ | ⟨h125a, h125b, h125c⟩
                          ·
                            rcases m.htr 1 3 4 (by decide) (by decide) with
                              ⟨h134a, h134b, h134c⟩ | ⟨h134a, h134b, h134c⟩
                            ·
                              exfalso; linarith only [ht0, h134a, h034a, h013c, hp1, h125a, ht12, h023c, hc25b, ht5, ht01, hc34a, ht23, h012c]
                            ·
                              rcases m.htr 1 3 5 (by decide) (by decide) with
                                ⟨h135a, h135b, h135c⟩ | ⟨h135a, h135b, h135c⟩
                              ·
                                rcases m.htr 1 4 5 (by decide) (by decide) with
                                  ⟨h145a, h145b, h145c⟩ | ⟨h145a, h145b, h145c⟩
                                ·
                                  rcases m.htr 2 3 4 (by decide) (by decide) with
                                    ⟨h234a, h234b, h234c⟩ | ⟨h234a, h234b, h234c⟩
                                  ·
                                    exfalso; linarith only [ht0, hc25b, ht5, ht12, h125a, h023c, hp1, h234a, hc23a, ht01, h034a, h012c]
                                  ·
                                    exfalso; linarith only [hc25b, ht23, h125a, hp1, h012c, h234a, ht01, hc34a, ht0, ht12, ht5, h023a]
                                ·
                                  exfalso; linarith only [hp1, h045c, hc34a, h023c, hc12b, h124c, h025b, ht23, h145a, h034a]
                              ·
                                exfalso; linarith only [h125a, ht01, hp1, hc13b, ht12, h023c, h034a, h035a, ht23, hc34a, hc25b, h135a, ht5, ht0, h012c]
                          ·
                            exfalso; linarith only [h023c, ht0, ht23, hc12b, h125a, ht5, hc34a, h025a, hp1, h034a, ht12, ht45, ht01, ht34]
                    ·
                      exfalso; linarith only [h025b, h034c, h023c, h045c]
                  ·
                    exfalso; linarith only [h023c, h035c, h025b]
              ·
                rcases m.htr 0 3 4 (by decide) (by decide) with
                  ⟨h034a, h034b, h034c⟩ | ⟨h034a, h034b, h034c⟩
                ·
                  rcases m.htr 0 3 5 (by decide) (by decide) with
                    ⟨h035a, h035b, h035c⟩ | ⟨h035a, h035b, h035c⟩
                  ·
                    rcases m.htr 0 4 5 (by decide) (by decide) with
                      ⟨h045a, h045b, h045c⟩ | ⟨h045a, h045b, h045c⟩
                    ·
                      rcases m.htr 1 2 3 (by decide) (by decide) with
                        ⟨h123a, h123b, h123c⟩ | ⟨h123a, h123b, h123c⟩
                      ·
                        exfalso; linarith only [h012c, ht34, ht5, ht45, ht01, ht23, ht12, ht0, h023a, hp1, h123a]
                      ·
                        rcases m.htr 1 2 4 (by decide) (by decide) with
                          ⟨h124a, h124b, h124c⟩ | ⟨h124a, h124b, h124c⟩
                        ·
                          exfalso; linarith only [h124a, ht01, ht45, hp1, h024a, ht34, ht0, h012c, ht12, ht23, ht5]
                        ·
                          rcases m.htr 1 2 5 (by decide) (by decide) with
                            ⟨h125a, h125b, h125c⟩ | ⟨h125a, h125b, h125c⟩
                          ·
                            exfalso; linarith only [ht34, h025a, ht23, hp1, ht5, ht0, h125a, ht45, ht01, h012c, ht12]
                          ·
                            rcases m.htr 1 3 4 (by decide) (by decide) with
                              ⟨h134a, h134b, h134c⟩ | ⟨h134a, h134b, h134c⟩
                            ·
                              rcases m.htr 1 3 5 (by decide) (by decide) with
                                ⟨h135a, h135b, h135c⟩ | ⟨h135a, h135b, h135c⟩
                              ·
                                rcases m.htr 1 4 5 (by decide) (by decide) with
                                  ⟨h145a, h145b, h145c⟩ | ⟨h145a, h145b, h145c⟩
                                ·
                                  rcases m.htr 2 3 4 (by decide) (by decide) with
                                    ⟨h234a, h234b, h234c⟩ | ⟨h234a, h234b, h234c⟩
                                  ·
                                    rcases m.htr 2 3 5 (by decide) (by decide) with
                                      ⟨h235a, h235b, h235c⟩ | ⟨h235a, h235b, h235c⟩
                                    ·
                                      rcases m.htr 2 4 5 (by decide) (by decide) with
                                        ⟨h245a, h245b, h245c⟩ | ⟨h245a, h245b, h245c⟩
                                      ·
                                        rcases m.htr 3 4 5 (by decide) (by decide) with
                                          ⟨h345a, h345b, h345c⟩ | ⟨h345a, h345b, h345c⟩
                                        ·
                                          exfalso; linarith only [h345a, ht0, hc01a, h013a, hp1, h134a, hc45b, ht5]
                                        ·
                                          exfalso; linarith only [ht0, hp1, hc34b, h134b, h013a, ht45, h345a, hc01a, h145a, ht5]
                                      ·
                                        exfalso; linarith only [hc02b, h145a, hp1, ht23, ht45, h245a, ht5, ht34, h024a, ht01, hc01a, h134b, ht0, h013a, ht12]
                                    ·
                                      exfalso; linarith only [ht45, ht5, h235a, ht01, ht0, h135a, h013a, ht34, hp1, hc02b, h234b, h024a, ht23, hc01a, ht12]
                                  ·
                                    exfalso; linarith only [h234a, ht0, ht34, ht12, h134a, hp1, h013a, h023a, hc01a, hc02b, ht01, ht23, ht5, ht45]
                                ·
                                  exfalso; linarith only [hp1, hc23a, h124c, hc12b, h145a, h023b, h034b, h045a]
                              ·
                                exfalso; linarith only [hc23a, ht01, h134a, ht0, hp1, hc34b, h135a, ht5, h023b, ht12, ht45, h035a]
                            ·
                              exfalso; linarith only [h134a, h123c, hp1, hc12b, hc23a, h023b, h034a]
                    ·
                      rcases m.htr 1 2 3 (by decide) (by decide) with
                        ⟨h123a, h123b, h123c⟩ | ⟨h123a, h123b, h123c⟩
                      ·
                        exfalso; linarith only [h012c, hp1, h023b, h024c, hc45a, h045a, h123a, hc03b, ht34]
                      ·
                        rcases m.htr 1 2 4 (by decide) (by decide) with
                          ⟨h124a, h124b, h124c⟩ | ⟨h124a, h124b, h124c⟩
                        ·
                          exfalso; linarith only [h024c, hp1, hc24b, h012c, hc45a, h124a, h045a]
                        ·
                          rcases m.htr 1 2 5 (by decide) (by decide) with
                            ⟨h125a, h125b, h125c⟩ | ⟨h125a, h125b, h125c⟩
                          ·
                            exfalso; linarith only [h045a, h125a, h024c, ht23, ht01, ht34, hp1, ht0, ht5, h025a, hc45a, hc25b, h012c, ht12]
                          ·
                            rcases m.htr 1 3 4 (by decide) (by decide) with
                              ⟨h134a, h134b, h134c⟩ | ⟨h134a, h134b, h134c⟩
                            ·
                              rcases m.htr 1 3 5 (by decide) (by decide) with
                                ⟨h135a, h135b, h135c⟩ | ⟨h135a, h135b, h135c⟩
                              ·
                                rcases m.htr 1 4 5 (by decide) (by decide) with
                                  ⟨h145a, h145b, h145c⟩ | ⟨h145a, h145b, h145c⟩
                                ·
                                  exfalso; linarith only [ht34, ht0, h014c, ht12, h145a, ht45, ht5, ht23, h045a, hp1, ht01]
                                ·
                                  rcases m.htr 2 3 4 (by decide) (by decide) with
                                    ⟨h234a, h234b, h234c⟩ | ⟨h234a, h234b, h234c⟩
                                  ·
                                    rcases m.htr 2 3 5 (by decide) (by decide) with
                                      ⟨h235a, h235b, h235c⟩ | ⟨h235a, h235b, h235c⟩
                                    ·
                                      rcases m.htr 2 4 5 (by decide) (by decide) with
                                        ⟨h245a, h245b, h245c⟩ | ⟨h245a, h245b, h245c⟩
                                      ·
                                        exfalso; linarith only [h024c, h245a, hp1, h045a, h234b, hc23a, hc02b]
                                      ·
                                        exfalso; linarith only [ht23, h245a, ht34, hp1, hc45a, h024a, hc02b]
                                    ·
                                      exfalso; linarith only [ht5, h135a, ht34, h023b, hc03b, hc01a, h235a, hp1, ht45, h013a, ht0]
                                  ·
                                    exfalso; linarith only [ht0, hc01a, ht5, h134a, ht45, hp1, h013a, ht34, h023b, h234a, hc03b]
                              ·
                                exfalso; linarith only [h035a, ht01, ht5, h135a, hp1, ht0, ht45, h134a, hc23a, ht12, hc34b, h023b]
                            ·
                              exfalso; linarith only [h045a, h134a, hc13b, ht34, hp1, hc45a, h034c]
                  ·
                    rcases m.htr 0 4 5 (by decide) (by decide) with
                      ⟨h045a, h045b, h045c⟩ | ⟨h045a, h045b, h045c⟩
                    ·
                      exfalso; linarith only [h035c, h045b, h034b]
                    ·
                      rcases m.htr 1 2 3 (by decide) (by decide) with
                        ⟨h123a, h123b, h123c⟩ | ⟨h123a, h123b, h123c⟩
                      ·
                        exfalso; linarith only [h034b, h035a, hp1, h012c, h024c, hc23b, hc35a, h123a]
                      ·
                        rcases m.htr 1 2 4 (by decide) (by decide) with
                          ⟨h124a, h124b, h124c⟩ | ⟨h124a, h124b, h124c⟩
                        ·
                          exfalso; linarith only [hc24b, h024a, hp1, ht5, ht0, ht23, h034b, h124a, h012c, hc35a, h024c, h035a, ht01, ht12, ht45]
                        ·
                          rcases m.htr 1 2 5 (by decide) (by decide) with
                            ⟨h125a, h125b, h125c⟩ | ⟨h125a, h125b, h125c⟩
                          ·
                            exfalso; linarith only [ht0, h024c, ht01, ht5, hp1, h125a, ht12, h034b, hc35a, h025a, hc25b, ht23, h035a, h012c]
                          ·
                            rcases m.htr 1 3 4 (by decide) (by decide) with
                              ⟨h134a, h134b, h134c⟩ | ⟨h134a, h134b, h134c⟩
                            ·
                              rcases m.htr 1 3 5 (by decide) (by decide) with
                                ⟨h135a, h135b, h135c⟩ | ⟨h135a, h135b, h135c⟩
                              ·
                                exfalso; linarith only [hc35a, ht45, ht12, ht01, ht0, ht23, h134a, hp1, hc34b, h035a, h135a, h013c, ht5]
                              ·
                                rcases m.htr 1 4 5 (by decide) (by decide) with
                                  ⟨h145a, h145b, h145c⟩ | ⟨h145a, h145b, h145c⟩
                                ·
                                  exfalso; linarith only [ht5, hc35a, ht0, hc34b, h045a, hp1, h014c, h013c, ht45, ht23, ht01, ht12, h134a, h035a, h145a]
                                ·
                                  rcases m.htr 2 3 4 (by decide) (by decide) with
                                    ⟨h234a, h234b, h234c⟩ | ⟨h234a, h234b, h234c⟩
                                  ·
                                    rcases m.htr 2 3 5 (by decide) (by decide) with
                                      ⟨h235a, h235b, h235c⟩ | ⟨h235a, h235b, h235c⟩
                                    ·
                                      exfalso; linarith only [ht12, ht45, ht0, ht5, h035a, h134a, h013c, ht01, hc34b, hp1, h235a, hc23a]
                                    ·
                                      exfalso; linarith only [hc02b, h023a, h235a, ht23, hp1, hc35a]
                                  ·
                                    exfalso; linarith only [ht23, hp1, h035a, h234a, ht12, h134a, ht5, ht0, hc35a, hc23b, ht45, hc34b, ht01, h013c]
                            ·
                              exfalso; linarith only [ht0, ht45, ht23, h034a, ht5, ht12, h035a, h134a, ht34, hp1, hc35a, ht01, hc13b]
                ·
                  rcases m.htr 0 3 5 (by decide) (by decide) with
                    ⟨h035a, h035b, h035c⟩ | ⟨h035a, h035b, h035c⟩
                  ·
                    rcases m.htr 0 4 5 (by decide) (by decide) with
                      ⟨h045a, h045b, h045c⟩ | ⟨h045a, h045b, h045c⟩
                    ·
                      rcases m.htr 1 2 3 (by decide) (by decide) with
                        ⟨h123a, h123b, h123c⟩ | ⟨h123a, h123b, h123c⟩
                      ·
                        exfalso; linarith only [hp1, h034a, h012c, hc23b, h025c, h035b, h123a, hc34a]
                      ·
                        rcases m.htr 1 2 4 (by decide) (by decide) with
                          ⟨h124a, h124b, h124c⟩ | ⟨h124a, h124b, h124c⟩
                        ·
                          exfalso; linarith only [h024a, h035b, ht0, hp1, h034a, h124a, ht23, ht12, ht5, hc34a, hc24b, h012c, ht01, h025c, ht45]
                        ·
                          rcases m.htr 1 2 5 (by decide) (by decide) with
                            ⟨h125a, h125b, h125c⟩ | ⟨h125a, h125b, h125c⟩
                          ·
                            exfalso; linarith only [h025c, ht23, ht0, ht12, hc25b, hp1, h125a, hc34a, ht5, ht01, h012c, h034a, h025a, h035b]
                          ·
                            rcases m.htr 1 3 4 (by decide) (by decide) with
                              ⟨h134a, h134b, h134c⟩ | ⟨h134a, h134b, h134c⟩
                            ·
                              exfalso; linarith only [ht0, h013c, ht12, h034a, ht23, ht5, h134a, hp1, ht45, ht01, ht34]
                            ·
                              rcases m.htr 1 3 5 (by decide) (by decide) with
                                ⟨h135a, h135b, h135c⟩ | ⟨h135a, h135b, h135c⟩
                              ·
                                rcases m.htr 1 4 5 (by decide) (by decide) with
                                  ⟨h145a, h145b, h145c⟩ | ⟨h145a, h145b, h145c⟩
                                ·
                                  rcases m.htr 2 3 4 (by decide) (by decide) with
                                    ⟨h234a, h234b, h234c⟩ | ⟨h234a, h234b, h234c⟩
                                  ·
                                    exfalso; linarith only [h234a, hc23a, h025c, hp1, h034a, h035b, hc02b]
                                  ·
                                    exfalso; linarith only [hp1, ht23, hc02b, h023a, h234a, hc34a]
                                ·
                                  exfalso; linarith only [h124c, h035b, h034a, hc34a, hc12b, ht23, h145a, h045c, hp1]
                              ·
                                exfalso; linarith only [hp1, ht34, ht23, ht5, hc13b, ht45, ht0, ht12, ht01, h035a, hc34a, h034a, h135a]
                    ·
                      exfalso; linarith only [h034c, h045c, h035b]
                  ·
                    rcases m.htr 0 4 5 (by decide) (by decide) with
                      ⟨h045a, h045b, h045c⟩ | ⟨h045a, h045b, h045c⟩
                    ·
                      rcases m.htr 1 2 3 (by decide) (by decide) with
                        ⟨h123a, h123b, h123c⟩ | ⟨h123a, h123b, h123c⟩
                      ·
                        exfalso; linarith only [h023c, hc23b, hc34a, h012c, h123a, h034a, hp1]
                      ·
                        rcases m.htr 1 2 4 (by decide) (by decide) with
                          ⟨h124a, h124b, h124c⟩ | ⟨h124a, h124b, h124c⟩
                        ·
                          exfalso; linarith only [h034a, hc24b, hc34a, ht5, ht23, ht0, hp1, h024a, ht45, h124a, h012c, h023c, ht12, ht01]
                        ·
                          rcases m.htr 1 2 5 (by decide) (by decide) with
                            ⟨h125a, h125b, h125c⟩ | ⟨h125a, h125b, h125c⟩
                          ·
                            exfalso; linarith only [h025a, ht0, h012c, ht5, h023c, ht01, h034a, ht23, hc25b, hp1, h125a, hc34a, ht12]
                          ·
                            rcases m.htr 1 3 4 (by decide) (by decide) with
                              ⟨h134a, h134b, h134c⟩ | ⟨h134a, h134b, h134c⟩
                            ·
                              exfalso; linarith only [ht12, ht01, ht45, ht0, h134a, ht23, hp1, h034a, ht5, h013c, ht34]
                            ·
                              rcases m.htr 1 3 5 (by decide) (by decide) with
                                ⟨h135a, h135b, h135c⟩ | ⟨h135a, h135b, h135c⟩
                              ·
                                exfalso; linarith only [h013c, ht0, hp1, ht23, ht12, ht34, ht45, h035a, ht01, h135a, ht5]
                              ·
                                rcases m.htr 1 4 5 (by decide) (by decide) with
                                  ⟨h145a, h145b, h145c⟩ | ⟨h145a, h145b, h145c⟩
                                ·
                                  rcases m.htr 2 3 4 (by decide) (by decide) with
                                    ⟨h234a, h234b, h234c⟩ | ⟨h234a, h234b, h234c⟩
                                  ·
                                    exfalso; linarith only [hc02b, h234a, hp1, h023c, hc23a, h034a]
                                  ·
                                    exfalso; linarith only [hc34a, h234a, hp1, hc02b, h023a, ht23]
                                ·
                                  exfalso; linarith only [h034b, hc34a, h045a, hc12b, ht23, hp1, h145a, h124c]
                    ·
                      rcases m.htr 1 2 3 (by decide) (by decide) with
                        ⟨h123a, h123b, h123c⟩ | ⟨h123a, h123b, h123c⟩
                      ·
                        exfalso; linarith only [h034c, ht34, h012c, h023c, hp1, hc45a, h045a, hc23b, h123a]
                      ·
                        rcases m.htr 1 2 4 (by decide) (by decide) with
                          ⟨h124a, h124b, h124c⟩ | ⟨h124a, h124b, h124c⟩
                        ·
                          exfalso; linarith only [h034c, hp1, h012c, hc45a, h124a, hc24b, h045a, h023c]
                        ·
                          rcases m.htr 1 2 5 (by decide) (by decide) with
                            ⟨h125a, h125b, h125c⟩ | ⟨h125a, h125b, h125c⟩
                          ·
                            exfalso; linarith only [ht23, h125a, hc25b, hp1, h034c, ht5, ht34, h012c, h023c, hc45a, ht0, h045a, h025a, ht12, ht01]
                          ·
                            rcases m.htr 1 3 4 (by decide) (by decide) with
                              ⟨h134a, h134b, h134c⟩ | ⟨h134a, h134b, h134c⟩
                            ·
                              exfalso; linarith only [hc45a, hp1, h034c, h013c, h134a, h045a, hc34b]
                            ·
                              rcases m.htr 1 3 5 (by decide) (by decide) with
                                ⟨h135a, h135b, h135c⟩ | ⟨h135a, h135b, h135c⟩
                              ·
                                exfalso; linarith only [h034c, ht23, h045a, ht12, h035a, ht01, hc45a, h013c, ht0, ht34, hc35b, h135a, hp1, ht5]
                              ·
                                rcases m.htr 1 4 5 (by decide) (by decide) with
                                  ⟨h145a, h145b, h145c⟩ | ⟨h145a, h145b, h145c⟩
                                ·
                                  exfalso; linarith only [h045a, ht0, ht12, ht01, ht5, ht23, ht34, hp1, h145a, ht45, h014c]
                                ·
                                  rcases m.htr 2 3 4 (by decide) (by decide) with
                                    ⟨h234a, h234b, h234c⟩ | ⟨h234a, h234b, h234c⟩
                                  ·
                                    exfalso; linarith only [h023c, hp1, hc23a, h234a, hc02b, h034a]
                                  ·
                                    exfalso; linarith only [h023a, hc02b, h234a, ht23, hc34a, hp1]
        ·
          rcases m.htr 0 2 3 (by decide) (by decide) with
            ⟨h023a, h023b, h023c⟩ | ⟨h023a, h023b, h023c⟩
          ·
            rcases m.htr 0 2 4 (by decide) (by decide) with
              ⟨h024a, h024b, h024c⟩ | ⟨h024a, h024b, h024c⟩
            ·
              rcases m.htr 0 2 5 (by decide) (by decide) with
                ⟨h025a, h025b, h025c⟩ | ⟨h025a, h025b, h025c⟩
              ·
                exfalso; linarith only [h012b, h025b, h015c]
              ·
                rcases m.htr 0 3 4 (by decide) (by decide) with
                  ⟨h034a, h034b, h034c⟩ | ⟨h034a, h034b, h034c⟩
                ·
                  rcases m.htr 0 3 5 (by decide) (by decide) with
                    ⟨h035a, h035b, h035c⟩ | ⟨h035a, h035b, h035c⟩
                  ·
                    exfalso; linarith only [h035b, h015c, h012b, h023b]
                  ·
                    rcases m.htr 0 4 5 (by decide) (by decide) with
                      ⟨h045a, h045b, h045c⟩ | ⟨h045a, h045b, h045c⟩
                    ·
                      exfalso; linarith only [h015c, h012b, h034b, h023b, h045b]
                    ·
                      rcases m.htr 1 2 3 (by decide) (by decide) with
                        ⟨h123a, h123b, h123c⟩ | ⟨h123a, h123b, h123c⟩
                      ·
                        exfalso; linarith only [hc23b, h015a, hp1, ht34, h012a, ht5, h123a, ht01, hc15a, ht45, ht0]
                      ·
                        exfalso; linarith only [ht5, ht34, h015a, hp1, h123a, ht01, ht0, hc15a, ht23, h012b, ht45, hc12b, h023a]
                ·
                  rcases m.htr 0 3 5 (by decide) (by decide) with
                    ⟨h035a, h035b, h035c⟩ | ⟨h035a, h035b, h035c⟩
                  ·
                    exfalso; linarith only [h024b, h012b, h034c, h015c, h035b]
                  ·
                    rcases m.htr 0 4 5 (by decide) (by decide) with
                      ⟨h045a, h045b, h045c⟩ | ⟨h045a, h045b, h045c⟩
                    ·
                      exfalso; linarith only [h024b, h045b, h015c, h012b]
                    ·
                      rcases m.htr 1 2 3 (by decide) (by decide) with
                        ⟨h123a, h123b, h123c⟩ | ⟨h123a, h123b, h123c⟩
                      ·
                        exfalso; linarith only [h015a, h012a, ht5, ht01, hc15a, hc23b, ht45, hp1, h123a, ht34, ht0]
                      ·
                        exfalso; linarith only [hc15a, h023a, ht34, h012b, hp1, ht0, h015a, hc12b, h123a, ht01, ht23, ht5, ht45]
            ·
              rcases m.htr 0 2 5 (by decide) (by decide) with
                ⟨h025a, h025b, h025c⟩ | ⟨h025a, h025b, h025c⟩
              ·
                exfalso; linarith only [h025b, h024c, h015c, h014b]
              ·
                rcases m.htr 0 3 4 (by decide) (by decide) with
                  ⟨h034a, h034b, h034c⟩ | ⟨h034a, h034b, h034c⟩
                ·
                  exfalso; linarith only [h024c, h034b, h023b]
                ·
                  rcases m.htr 0 3 5 (by decide) (by decide) with
                    ⟨h035a, h035b, h035c⟩ | ⟨h035a, h035b, h035c⟩
                  ·
                    exfalso; linarith only [h035b, h015c, h014b, h023b, h024c]
                  ·
                    rcases m.htr 0 4 5 (by decide) (by decide) with
                      ⟨h045a, h045b, h045c⟩ | ⟨h045a, h045b, h045c⟩
                    ·
                      exfalso; linarith only [h045b, h014b, h015c]
                    ·
                      exfalso; linarith only [hc45a, hc23b, h023a, ht34, h045a, h024c, hp1]
          ·
            rcases m.htr 0 2 4 (by decide) (by decide) with
              ⟨h024a, h024b, h024c⟩ | ⟨h024a, h024b, h024c⟩
            ·
              rcases m.htr 0 2 5 (by decide) (by decide) with
                ⟨h025a, h025b, h025c⟩ | ⟨h025a, h025b, h025c⟩
              ·
                exfalso; linarith only [h015c, h013b, h023c, h025b]
              ·
                rcases m.htr 0 3 4 (by decide) (by decide) with
                  ⟨h034a, h034b, h034c⟩ | ⟨h034a, h034b, h034c⟩
                ·
                  rcases m.htr 0 3 5 (by decide) (by decide) with
                    ⟨h035a, h035b, h035c⟩ | ⟨h035a, h035b, h035c⟩
                  ·
                    exfalso; linarith only [h035b, h015c, h013b]
                  ·
                    rcases m.htr 0 4 5 (by decide) (by decide) with
                      ⟨h045a, h045b, h045c⟩ | ⟨h045a, h045b, h045c⟩
                    ·
                      exfalso; linarith only [h015c, hc35a, h024b, h012a, ht23, h045b, hc12b, hp1, h023c, h035a]
                    ·
                      rcases m.htr 1 2 3 (by decide) (by decide) with
                        ⟨h123a, h123b, h123c⟩ | ⟨h123a, h123b, h123c⟩
                      ·
                        exfalso; linarith only [hc23b, hp1, ht5, h123a, hc15a, ht0, ht01, hc24b, h035a, h024a, h015a, hc35a, ht45, h023c, h012a]
                      ·
                        rcases m.htr 1 2 4 (by decide) (by decide) with
                          ⟨h124a, h124b, h124c⟩ | ⟨h124a, h124b, h124c⟩
                        ·
                          exfalso; linarith only [h013a, hc24b, ht0, h015a, ht45, ht5, h123c, hc15a, h124a, hp1, ht01]
                        ·
                          exfalso; linarith only [h024a, hc35a, hc15a, hp1, h013a, h023c, ht45, hc24b, ht0, h124a, ht01, ht23, ht5, h123c, h035a, h015a, hc12b]
                ·
                  exfalso; linarith only [h024b, h034c, h023c]
            ·
              rcases m.htr 0 2 5 (by decide) (by decide) with
                ⟨h025a, h025b, h025c⟩ | ⟨h025a, h025b, h025c⟩
              ·
                exfalso; linarith only [h013b, h015c, h025b, h023c]
              ·
                rcases m.htr 0 3 4 (by decide) (by decide) with
                  ⟨h034a, h034b, h034c⟩ | ⟨h034a, h034b, h034c⟩
                ·
                  rcases m.htr 0 3 5 (by decide) (by decide) with
                    ⟨h035a, h035b, h035c⟩ | ⟨h035a, h035b, h035c⟩
                  ·
                    exfalso; linarith only [h035b, h015c, h013b]
                  ·
                    rcases m.htr 0 4 5 (by decide) (by decide) with
                      ⟨h045a, h045b, h045c⟩ | ⟨h045a, h045b, h045c⟩
                    ·
                      exfalso; linarith only [ht23, h034b, h045b, hp1, h015c, hc35a, hc12b, h035a, h012a]
                    ·
                      rcases m.htr 1 2 3 (by decide) (by decide) with
                        ⟨h123a, h123b, h123c⟩ | ⟨h123a, h123b, h123c⟩
                      ·
                        exfalso; linarith only [h012a, hp1, h123a, ht0, ht5, h015a, ht34, hc15a, ht01, hc23b, ht45]
                      ·
                        rcases m.htr 1 2 4 (by decide) (by decide) with
                          ⟨h124a, h124b, h124c⟩ | ⟨h124a, h124b, h124c⟩
                        ·
                          exfalso; linarith only [ht45, hc24b, hp1, ht5, h013a, ht01, h123c, ht0, hc15a, h015a, h124a]
                        ·
                          rcases m.htr 1 2 5 (by decide) (by decide) with
                            ⟨h125a, h125b, h125c⟩ | ⟨h125a, h125b, h125c⟩
                          ·
                            exfalso; linarith only [ht0, hp1, ht5, hc15a, h125a, h015a, h013a, hc25b, ht01, h123c]
                          ·
                            exfalso; linarith only [hc12b, hc25a, h125b, hp1, h123c, h013a, h015a]
                ·
                  rcases m.htr 0 3 5 (by decide) (by decide) with
                    ⟨h035a, h035b, h035c⟩ | ⟨h035a, h035b, h035c⟩
                  ·
                    exfalso; linarith only [hc34a, h034a, hp1, h012a, ht23, hc12b, h035b, h015c]
                  ·
                    rcases m.htr 0 4 5 (by decide) (by decide) with
                      ⟨h045a, h045b, h045c⟩ | ⟨h045a, h045b, h045c⟩
                    ·
                      exfalso; linarith only [h015c, h014b, h045b]
                    ·
                      rcases m.htr 1 2 3 (by decide) (by decide) with
                        ⟨h123a, h123b, h123c⟩ | ⟨h123a, h123b, h123c⟩
                      ·
                        exfalso; linarith only [h123a, ht5, ht45, ht0, hc23b, hc15a, ht01, hp1, h015a, h012a, ht34]
                      ·
                        rcases m.htr 1 2 4 (by decide) (by decide) with
                          ⟨h124a, h124b, h124c⟩ | ⟨h124a, h124b, h124c⟩
                        ·
                          exfalso; linarith only [h123c, ht5, ht45, hp1, h124a, ht0, h013a, ht01, h015a, hc15a, hc24b]
                        ·
                          rcases m.htr 1 2 5 (by decide) (by decide) with
                            ⟨h125a, h125b, h125c⟩ | ⟨h125a, h125b, h125c⟩
                          ·
                            exfalso; linarith only [h013a, hc15a, hp1, h123c, ht01, h125a, ht5, hc25b, ht0, h015a]
                          ·
                            exfalso; linarith only [h013a, hp1, h125b, h015a, hc25a, h123c, hc12b]
      ·
        rcases m.htr 0 1 5 (by decide) (by decide) with
          ⟨h015a, h015b, h015c⟩ | ⟨h015a, h015b, h015c⟩
        ·
          rcases m.htr 0 2 3 (by decide) (by decide) with
            ⟨h023a, h023b, h023c⟩ | ⟨h023a, h023b, h023c⟩
          ·
            rcases m.htr 0 2 4 (by decide) (by decide) with
              ⟨h024a, h024b, h024c⟩ | ⟨h024a, h024b, h024c⟩
            ·
              exfalso; linarith only [h014c, h024b, h012b]
            ·
              rcases m.htr 0 2 5 (by decide) (by decide) with
                ⟨h025a, h025b, h025c⟩ | ⟨h025a, h025b, h025c⟩
              ·
                rcases m.htr 0 3 4 (by decide) (by decide) with
                  ⟨h034a, h034b, h034c⟩ | ⟨h034a, h034b, h034c⟩
                ·
                  exfalso; linarith only [h034b, h014c, h023b, h012b]
                ·
                  rcases m.htr 0 3 5 (by decide) (by decide) with
                    ⟨h035a, h035b, h035c⟩ | ⟨h035a, h035b, h035c⟩
                  ·
                    rcases m.htr 0 4 5 (by decide) (by decide) with
                      ⟨h045a, h045b, h045c⟩ | ⟨h045a, h045b, h045c⟩
                    ·
                      rcases m.htr 1 2 3 (by decide) (by decide) with
                        ⟨h123a, h123b, h123c⟩ | ⟨h123a, h123b, h123c⟩
                      ·
                        exfalso; linarith only [h014a, h123a, hp1, ht34, hc14a, ht01, ht5, ht0, ht45, hc23b, h012a]
                      ·
                        exfalso; linarith only [ht34, ht45, h014a, ht0, hp1, ht23, h012b, h123a, h023a, hc14a, ht5, hc12b, ht01]
                    ·
                      exfalso; linarith only [h045a, hp1, h012a, hc45a, ht34, h014c, hc12b, ht23]
                  ·
                    rcases m.htr 0 4 5 (by decide) (by decide) with
                      ⟨h045a, h045b, h045c⟩ | ⟨h045a, h045b, h045c⟩
                    ·
                      rcases m.htr 1 2 3 (by decide) (by decide) with
                        ⟨h123a, h123b, h123c⟩ | ⟨h123a, h123b, h123c⟩
                      ·
                        exfalso; linarith only [hp1, h123a, ht01, hc14a, ht0, h014a, hc23b, h012a, ht5, ht45, ht34]
                      ·
                        exfalso; linarith only [ht45, h014a, hp1, ht0, hc12b, h012b, hc14a, ht5, h023a, ht34, ht23, h123a, ht01]
                    ·
                      exfalso; linarith only [hc12b, h045a, h012a, ht23, hp1, h014c, ht34, hc45a]
              ·
                rcases m.htr 0 3 4 (by decide) (by decide) with
                  ⟨h034a, h034b, h034c⟩ | ⟨h034a, h034b, h034c⟩
                ·
                  exfalso; linarith only [h014c, h034b, h015b, h023b, h025c]
                ·
                  rcases m.htr 0 3 5 (by decide) (by decide) with
                    ⟨h035a, h035b, h035c⟩ | ⟨h035a, h035b, h035c⟩
                  ·
                    exfalso; linarith only [h025c, h035b, h023b]
                  ·
                    rcases m.htr 0 4 5 (by decide) (by decide) with
                      ⟨h045a, h045b, h045c⟩ | ⟨h045a, h045b, h045c⟩
                    ·
                      rcases m.htr 1 2 3 (by decide) (by decide) with
                        ⟨h123a, h123b, h123c⟩ | ⟨h123a, h123b, h123c⟩
                      ·
                        exfalso; linarith only [ht0, hc14a, ht01, hp1, h014a, h012a, h123a, hc23b, ht45, ht34, ht5]
                      ·
                        exfalso; linarith only [h014a, ht45, ht01, hc14a, hp1, hc12b, ht34, h015b, ht0, ht23, h025c, h123a, h023a, ht5]
                    ·
                      exfalso; linarith only [hc23b, hc45a, h025c, h014c, ht34, hp1, h023a, h015b, h045a]
          ·
            rcases m.htr 0 2 4 (by decide) (by decide) with
              ⟨h024a, h024b, h024c⟩ | ⟨h024a, h024b, h024c⟩
            ·
              exfalso; linarith only [h024b, h013b, h023c, h014c]
            ·
              rcases m.htr 0 2 5 (by decide) (by decide) with
                ⟨h025a, h025b, h025c⟩ | ⟨h025a, h025b, h025c⟩
              ·
                rcases m.htr 0 3 4 (by decide) (by decide) with
                  ⟨h034a, h034b, h034c⟩ | ⟨h034a, h034b, h034c⟩
                ·
                  exfalso; linarith only [h034b, h014c, h013b]
                ·
                  rcases m.htr 0 3 5 (by decide) (by decide) with
                    ⟨h035a, h035b, h035c⟩ | ⟨h035a, h035b, h035c⟩
                  ·
                    rcases m.htr 0 4 5 (by decide) (by decide) with
                      ⟨h045a, h045b, h045c⟩ | ⟨h045a, h045b, h045c⟩
                    ·
                      rcases m.htr 1 2 3 (by decide) (by decide) with
                        ⟨h123a, h123b, h123c⟩ | ⟨h123a, h123b, h123c⟩
                      ·
                        exfalso; linarith only [hc23b, ht34, ht01, h123a, ht45, h014a, h012a, hp1, hc14a, ht0, ht5]
                      ·
                        rcases m.htr 1 2 4 (by decide) (by decide) with
                          ⟨h124a, h124b, h124c⟩ | ⟨h124a, h124b, h124c⟩
                        ·
                          exfalso; linarith only [ht01, ht0, hc14a, h123c, ht5, hp1, h013a, h124a, hc24b, ht45, h014a]
                        ·
                          exfalso; linarith only [hp1, h014a, h124b, hc24a, hc12b, h013a, h123c]
                    ·
                      exfalso; linarith only [h012a, h045a, hc12b, h014c, ht34, ht23, hc45a, hp1]
                  ·
                    exfalso; linarith only [h025b, h023c, h035c]
              ·
                rcases m.htr 0 3 4 (by decide) (by decide) with
                  ⟨h034a, h034b, h034c⟩ | ⟨h034a, h034b, h034c⟩
                ·
                  exfalso; linarith only [h034b, h013b, h014c]
                ·
                  rcases m.htr 0 3 5 (by decide) (by decide) with
                    ⟨h035a, h035b, h035c⟩ | ⟨h035a, h035b, h035c⟩
                  ·
                    rcases m.htr 0 4 5 (by decide) (by decide) with
                      ⟨h045a, h045b, h045c⟩ | ⟨h045a, h045b, h045c⟩
                    ·
                      rcases m.htr 1 2 3 (by decide) (by decide) with
                        ⟨h123a, h123b, h123c⟩ | ⟨h123a, h123b, h123c⟩
                      ·
                        exfalso; linarith only [ht0, h012a, h123a, hc14a, hp1, ht45, hc23b, ht34, ht5, h014a, ht01]
                      ·
                        rcases m.htr 1 2 4 (by decide) (by decide) with
                          ⟨h124a, h124b, h124c⟩ | ⟨h124a, h124b, h124c⟩
                        ·
                          exfalso; linarith only [h124a, ht5, h014a, hc24b, ht01, ht45, ht0, hc14a, hp1, h013a, h123c]
                        ·
                          exfalso; linarith only [hc24a, hp1, h123c, h014a, h124b, hc12b, h013a]
                    ·
                      exfalso; linarith only [h012a, hc12b, hc45a, h014c, h045a, ht23, ht34, hp1]
                  ·
                    rcases m.htr 0 4 5 (by decide) (by decide) with
                      ⟨h045a, h045b, h045c⟩ | ⟨h045a, h045b, h045c⟩
                    ·
                      rcases m.htr 1 2 3 (by decide) (by decide) with
                        ⟨h123a, h123b, h123c⟩ | ⟨h123a, h123b, h123c⟩
                      ·
                        exfalso; linarith only [ht34, ht5, h012a, h123a, hc23b, hp1, ht45, hc14a, ht0, h014a, ht01]
                      ·
                        rcases m.htr 1 2 4 (by decide) (by decide) with
                          ⟨h124a, h124b, h124c⟩ | ⟨h124a, h124b, h124c⟩
                        ·
                          exfalso; linarith only [ht5, hp1, h014a, hc14a, ht01, ht45, h013a, ht0, hc24b, h123c, h124a]
                        ·
                          exfalso; linarith only [hc12b, hp1, h014a, h123c, hc24a, h124b, h013a]
                    ·
                      exfalso; linarith only [h014c, hc45a, ht34, h012a, hc12b, ht23, hp1, h045a]
        ·
          rcases m.htr 0 2 3 (by decide) (by decide) with
            ⟨h023a, h023b, h023c⟩ | ⟨h023a, h023b, h023c⟩
          ·
            rcases m.htr 0 2 4 (by decide) (by decide) with
              ⟨h024a, h024b, h024c⟩ | ⟨h024a, h024b, h024c⟩
            ·
              exfalso; linarith only [h014c, h012b, h024b]
            ·
              rcases m.htr 0 2 5 (by decide) (by decide) with
                ⟨h025a, h025b, h025c⟩ | ⟨h025a, h025b, h025c⟩
              ·
                exfalso; linarith only [h015c, h012b, h025b]
              ·
                rcases m.htr 0 3 4 (by decide) (by decide) with
                  ⟨h034a, h034b, h034c⟩ | ⟨h034a, h034b, h034c⟩
                ·
                  exfalso; linarith only [h023b, h012b, h014c, h034b]
                ·
                  rcases m.htr 0 3 5 (by decide) (by decide) with
                    ⟨h035a, h035b, h035c⟩ | ⟨h035a, h035b, h035c⟩
                  ·
                    exfalso; linarith only [h015c, h035b, h023b, h012b]
                  ·
                    rcases m.htr 0 4 5 (by decide) (by decide) with
                      ⟨h045a, h045b, h045c⟩ | ⟨h045a, h045b, h045c⟩
                    ·
                      rcases m.htr 1 2 3 (by decide) (by decide) with
                        ⟨h123a, h123b, h123c⟩ | ⟨h123a, h123b, h123c⟩
                      ·
                        exfalso; linarith only [ht01, hp1, hc14a, ht5, hc23b, ht45, ht0, ht34, h123a, h014a, h012a]
                      ·
                        exfalso; linarith only [h014a, ht0, hc12b, hc14a, hp1, h023a, h123a, h012b, ht5, ht23, ht01, ht45, ht34]
                    ·
                      exfalso; linarith only [h014c, hc12b, ht34, hc45a, ht23, hp1, h045a, h012a]
          ·
            rcases m.htr 0 2 4 (by decide) (by decide) with
              ⟨h024a, h024b, h024c⟩ | ⟨h024a, h024b, h024c⟩
            ·
              exfalso; linarith only [h023c, h024b, h014c, h013b]
            ·
              rcases m.htr 0 2 5 (by decide) (by decide) with
                ⟨h025a, h025b, h025c⟩ | ⟨h025a, h025b, h025c⟩
              ·
                exfalso; linarith only [h013b, h025b, h023c, h015c]
              ·
                rcases m.htr 0 3 4 (by decide) (by decide) with
                  ⟨h034a, h034b, h034c⟩ | ⟨h034a, h034b, h034c⟩
                ·
                  exfalso; linarith only [h013b, h034b, h014c]
                ·
                  rcases m.htr 0 3 5 (by decide) (by decide) with
                    ⟨h035a, h035b, h035c⟩ | ⟨h035a, h035b, h035c⟩
                  ·
                    exfalso; linarith only [hc12b, hp1, h012a, h015c, h034a, ht23, hc34a, h035b]
                  ·
                    rcases m.htr 0 4 5 (by decide) (by decide) with
                      ⟨h045a, h045b, h045c⟩ | ⟨h045a, h045b, h045c⟩
                    ·
                      rcases m.htr 1 2 3 (by decide) (by decide) with
                        ⟨h123a, h123b, h123c⟩ | ⟨h123a, h123b, h123c⟩
                      ·
                        exfalso; linarith only [hp1, h012a, h014a, hc23b, ht34, ht5, ht01, ht0, hc14a, h123a, ht45]
                      ·
                        rcases m.htr 1 2 4 (by decide) (by decide) with
                          ⟨h124a, h124b, h124c⟩ | ⟨h124a, h124b, h124c⟩
                        ·
                          exfalso; linarith only [hc14a, h123c, ht5, hp1, hc24b, h013a, ht0, h014a, h124a, ht01, ht45]
                        ·
                          exfalso; linarith only [h014a, h124b, hp1, hc12b, h123c, hc24a, h013a]
                    ·
                      exfalso; linarith only [hc45a, h012a, h014c, h045a, ht23, hp1, hc12b, ht34]
    ·
      rcases m.htr 0 1 4 (by decide) (by decide) with
        ⟨h014a, h014b, h014c⟩ | ⟨h014a, h014b, h014c⟩
      ·
        rcases m.htr 0 1 5 (by decide) (by decide) with
          ⟨h015a, h015b, h015c⟩ | ⟨h015a, h015b, h015c⟩
        ·
          rcases m.htr 0 2 3 (by decide) (by decide) with
            ⟨h023a, h023b, h023c⟩ | ⟨h023a, h023b, h023c⟩
          ·
            exfalso; linarith only [h012b, h023b, h013c]
          ·
            rcases m.htr 0 2 4 (by decide) (by decide) with
              ⟨h024a, h024b, h024c⟩ | ⟨h024a, h024b, h024c⟩
            ·
              rcases m.htr 0 2 5 (by decide) (by decide) with
                ⟨h025a, h025b, h025c⟩ | ⟨h025a, h025b, h025c⟩
              ·
                rcases m.htr 0 3 4 (by decide) (by decide) with
                  ⟨h034a, h034b, h034c⟩ | ⟨h034a, h034b, h034c⟩
                ·
                  rcases m.htr 0 3 5 (by decide) (by decide) with
                    ⟨h035a, h035b, h035c⟩ | ⟨h035a, h035b, h035c⟩
                  ·
                    rcases m.htr 0 4 5 (by decide) (by decide) with
                      ⟨h045a, h045b, h045c⟩ | ⟨h045a, h045b, h045c⟩
                    ·
                      rcases m.htr 1 2 3 (by decide) (by decide) with
                        ⟨h123a, h123b, h123c⟩ | ⟨h123a, h123b, h123c⟩
                      ·
                        exfalso; linarith only [hp1, ht0, h013a, ht34, ht5, h123a, hc13a, ht45, ht01, hc03b, h012a, h023b]
                      ·
                        exfalso; linarith only [hc23a, hp1, h013a, hc12b, h123b, h012a]
                    ·
                      rcases m.htr 1 2 3 (by decide) (by decide) with
                        ⟨h123a, h123b, h123c⟩ | ⟨h123a, h123b, h123c⟩
                      ·
                        exfalso; linarith only [ht45, h023b, h012a, hc13a, h013a, ht0, hp1, h123a, ht01, ht34, ht5, hc03b]
                      ·
                        exfalso; linarith only [hc23a, hp1, h013a, hc12b, h012a, h123b]
                  ·
                    exfalso; linarith only [h013c, hc12b, h012a, h035a, ht23, hc35a, hp1]
                ·
                  exfalso; linarith only [hp1, hc34a, h012a, hc12b, h034a, ht23, h013c]
              ·
                rcases m.htr 0 3 4 (by decide) (by decide) with
                  ⟨h034a, h034b, h034c⟩ | ⟨h034a, h034b, h034c⟩
                ·
                  rcases m.htr 0 3 5 (by decide) (by decide) with
                    ⟨h035a, h035b, h035c⟩ | ⟨h035a, h035b, h035c⟩
                  ·
                    rcases m.htr 0 4 5 (by decide) (by decide) with
                      ⟨h045a, h045b, h045c⟩ | ⟨h045a, h045b, h045c⟩
                    ·
                      exfalso; linarith only [h024b, h045b, h025c]
                    ·
                      rcases m.htr 1 2 3 (by decide) (by decide) with
                        ⟨h123a, h123b, h123c⟩ | ⟨h123a, h123b, h123c⟩
                      ·
                        exfalso; linarith only [hp1, h023b, h013a, hc13a, h012a, h123a, ht45, ht0, hc03b, ht34, ht5, ht01]
                      ·
                        exfalso; linarith only [h012a, hp1, h123b, h013a, hc12b, hc23a]
                  ·
                    exfalso; linarith only [h013c, hc35a, hc12b, h035a, hp1, h012a, ht23]
                ·
                  exfalso; linarith only [hc34a, hc12b, hp1, ht23, h013c, h012a, h034a]
            ·
              rcases m.htr 0 2 5 (by decide) (by decide) with
                ⟨h025a, h025b, h025c⟩ | ⟨h025a, h025b, h025c⟩
              ·
                rcases m.htr 0 3 4 (by decide) (by decide) with
                  ⟨h034a, h034b, h034c⟩ | ⟨h034a, h034b, h034c⟩
                ·
                  rcases m.htr 0 3 5 (by decide) (by decide) with
                    ⟨h035a, h035b, h035c⟩ | ⟨h035a, h035b, h035c⟩
                  ·
                    rcases m.htr 0 4 5 (by decide) (by decide) with
                      ⟨h045a, h045b, h045c⟩ | ⟨h045a, h045b, h045c⟩
                    ·
                      rcases m.htr 1 2 3 (by decide) (by decide) with
                        ⟨h123a, h123b, h123c⟩ | ⟨h123a, h123b, h123c⟩
                      ·
                        exfalso; linarith only [ht45, h012a, ht34, hc13a, ht01, ht0, hp1, ht5, h023b, h123a, hc03b, h013a]
                      ·
                        exfalso; linarith only [h012a, hp1, hc12b, h123b, hc23a, h013a]
                    ·
                      exfalso; linarith only [h045c, h024c, h025b]
                  ·
                    exfalso; linarith only [hc12b, ht23, h012a, hc35a, h013c, h035a, hp1]
                ·
                  exfalso; linarith only [hc12b, h034a, hp1, h013c, hc34a, h012a, ht23]
              ·
                rcases m.htr 0 3 4 (by decide) (by decide) with
                  ⟨h034a, h034b, h034c⟩ | ⟨h034a, h034b, h034c⟩
                ·
                  rcases m.htr 0 3 5 (by decide) (by decide) with
                    ⟨h035a, h035b, h035c⟩ | ⟨h035a, h035b, h035c⟩
                  ·
                    rcases m.htr 0 4 5 (by decide) (by decide) with
                      ⟨h045a, h045b, h045c⟩ | ⟨h045a, h045b, h045c⟩
                    ·
                      rcases m.htr 1 2 3 (by decide) (by decide) with
                        ⟨h123a, h123b, h123c⟩ | ⟨h123a, h123b, h123c⟩
                      ·
                        exfalso; linarith only [hp1, ht5, h023b, ht0, h012a, ht01, hc13a, hc03b, ht45, h013a, ht34, h123a]
                      ·
                        exfalso; linarith only [h012a, h123b, h013a, hp1, hc12b, hc23a]
                    ·
                      rcases m.htr 1 2 3 (by decide) (by decide) with
                        ⟨h123a, h123b, h123c⟩ | ⟨h123a, h123b, h123c⟩
                      ·
                        exfalso; linarith only [h013a, hc13a, hc03b, ht5, hp1, ht34, ht0, h012a, ht45, ht01, h123a, h023b]
                      ·
                        exfalso; linarith only [h012a, h123b, hc23a, hp1, h013a, hc12b]
                  ·
                    exfalso; linarith only [h012a, hp1, h013c, hc12b, h035a, hc35a, ht23]
                ·
                  exfalso; linarith only [hc34a, h034a, hp1, h012a, h013c, hc12b, ht23]
        ·
          rcases m.htr 0 2 3 (by decide) (by decide) with
            ⟨h023a, h023b, h023c⟩ | ⟨h023a, h023b, h023c⟩
          ·
            exfalso; linarith only [h023b, h013c, h012b]
          ·
            rcases m.htr 0 2 4 (by decide) (by decide) with
              ⟨h024a, h024b, h024c⟩ | ⟨h024a, h024b, h024c⟩
            ·
              rcases m.htr 0 2 5 (by decide) (by decide) with
                ⟨h025a, h025b, h025c⟩ | ⟨h025a, h025b, h025c⟩
              ·
                exfalso; linarith only [h025b, h015c, h012b]
              ·
                rcases m.htr 0 3 4 (by decide) (by decide) with
                  ⟨h034a, h034b, h034c⟩ | ⟨h034a, h034b, h034c⟩
                ·
                  rcases m.htr 0 3 5 (by decide) (by decide) with
                    ⟨h035a, h035b, h035c⟩ | ⟨h035a, h035b, h035c⟩
                  ·
                    rcases m.htr 0 4 5 (by decide) (by decide) with
                      ⟨h045a, h045b, h045c⟩ | ⟨h045a, h045b, h045c⟩
                    ·
                      exfalso; linarith only [h045b, h015c, h012b, h024b]
                    ·
                      rcases m.htr 1 2 3 (by decide) (by decide) with
                        ⟨h123a, h123b, h123c⟩ | ⟨h123a, h123b, h123c⟩
                      ·
                        exfalso; linarith only [ht34, h123a, ht0, ht01, hc03b, ht5, hp1, ht45, hc13a, h023b, h012a, h013a]
                      ·
                        exfalso; linarith only [hp1, h012a, hc12b, h123b, hc23a, h013a]
                  ·
                    exfalso; linarith only [hc12b, h035a, hc35a, hp1, h013c, h012a, ht23]
                ·
                  exfalso; linarith only [h012a, h013c, hc34a, ht23, hc12b, h034a, hp1]
            ·
              rcases m.htr 0 2 5 (by decide) (by decide) with
                ⟨h025a, h025b, h025c⟩ | ⟨h025a, h025b, h025c⟩
              ·
                exfalso; linarith only [h025b, h024c, h014b, h015c]
              ·
                rcases m.htr 0 3 4 (by decide) (by decide) with
                  ⟨h034a, h034b, h034c⟩ | ⟨h034a, h034b, h034c⟩
                ·
                  rcases m.htr 0 3 5 (by decide) (by decide) with
                    ⟨h035a, h035b, h035c⟩ | ⟨h035a, h035b, h035c⟩
                  ·
                    rcases m.htr 0 4 5 (by decide) (by decide) with
                      ⟨h045a, h045b, h045c⟩ | ⟨h045a, h045b, h045c⟩
                    ·
                      exfalso; linarith only [h015c, h045b, h014b]
                    ·
                      rcases m.htr 1 2 3 (by decide) (by decide) with
                        ⟨h123a, h123b, h123c⟩ | ⟨h123a, h123b, h123c⟩
                      ·
                        exfalso; linarith only [ht5, ht45, h023b, h013a, ht0, h123a, h012a, ht34, ht01, hc13a, hp1, hc03b]
                      ·
                        exfalso; linarith only [hc12b, h013a, h012a, hp1, h123b, hc23a]
                  ·
                    exfalso; linarith only [hp1, h013c, ht23, h035a, hc12b, hc35a, h012a]
                ·
                  exfalso; linarith only [h013c, hc12b, h012a, h034a, hc34a, hp1, ht23]
      ·
        rcases m.htr 0 1 5 (by decide) (by decide) with
          ⟨h015a, h015b, h015c⟩ | ⟨h015a, h015b, h015c⟩
        ·
          rcases m.htr 0 2 3 (by decide) (by decide) with
            ⟨h023a, h023b, h023c⟩ | ⟨h023a, h023b, h023c⟩
          ·
            exfalso; linarith only [h012b, h013c, h023b]
          ·
            rcases m.htr 0 2 4 (by decide) (by decide) with
              ⟨h024a, h024b, h024c⟩ | ⟨h024a, h024b, h024c⟩
            ·
              exfalso; linarith only [h024b, h012b, h014c]
            ·
              rcases m.htr 0 2 5 (by decide) (by decide) with
                ⟨h025a, h025b, h025c⟩ | ⟨h025a, h025b, h025c⟩
              ·
                rcases m.htr 0 3 4 (by decide) (by decide) with
                  ⟨h034a, h034b, h034c⟩ | ⟨h034a, h034b, h034c⟩
                ·
                  rcases m.htr 0 3 5 (by decide) (by decide) with
                    ⟨h035a, h035b, h035c⟩ | ⟨h035a, h035b, h035c⟩
                  ·
                    rcases m.htr 0 4 5 (by decide) (by decide) with
                      ⟨h045a, h045b, h045c⟩ | ⟨h045a, h045b, h045c⟩
                    ·
                      rcases m.htr 1 2 3 (by decide) (by decide) with
                        ⟨h123a, h123b, h123c⟩ | ⟨h123a, h123b, h123c⟩
                      ·
                        exfalso; linarith only [h123a, h012a, hc03b, ht5, ht0, ht45, h013a, h023b, hp1, ht01, ht34, hc13a]
                      ·
                        exfalso; linarith only [h123b, h012a, hp1, h013a, hc12b, hc23a]
                    ·
                      exfalso; linarith only [h012a, ht34, h014c, hp1, ht23, h045a, hc12b, hc45a]
                  ·
                    exfalso; linarith only [hp1, hc35a, ht23, h013c, h012a, h035a, hc12b]
                ·
                  exfalso; linarith only [h034a, h012a, h013c, hc34a, hc12b, ht23, hp1]
              ·
                rcases m.htr 0 3 4 (by decide) (by decide) with
                  ⟨h034a, h034b, h034c⟩ | ⟨h034a, h034b, h034c⟩
                ·
                  rcases m.htr 0 3 5 (by decide) (by decide) with
                    ⟨h035a, h035b, h035c⟩ | ⟨h035a, h035b, h035c⟩
                  ·
                    rcases m.htr 0 4 5 (by decide) (by decide) with
                      ⟨h045a, h045b, h045c⟩ | ⟨h045a, h045b, h045c⟩
                    ·
                      rcases m.htr 1 2 3 (by decide) (by decide) with
                        ⟨h123a, h123b, h123c⟩ | ⟨h123a, h123b, h123c⟩
                      ·
                        exfalso; linarith only [ht0, ht01, h123a, hc13a, h012a, ht45, h013a, ht34, h023b, hc03b, hp1, ht5]
                      ·
                        exfalso; linarith only [hc12b, h123b, h013a, hc23a, hp1, h012a]
                    ·
                      exfalso; linarith only [hp1, h014c, h045a, h012a, hc45a, ht34, hc12b, ht23]
                  ·
                    exfalso; linarith only [h013c, hp1, h035a, ht23, hc12b, h012a, hc35a]
                ·
                  exfalso; linarith only [hp1, h012a, hc12b, ht23, hc34a, h013c, h034a]
        ·
          rcases m.htr 0 2 3 (by decide) (by decide) with
            ⟨h023a, h023b, h023c⟩ | ⟨h023a, h023b, h023c⟩
          ·
            exfalso; linarith only [h013c, h023b, h012b]
          ·
            rcases m.htr 0 2 4 (by decide) (by decide) with
              ⟨h024a, h024b, h024c⟩ | ⟨h024a, h024b, h024c⟩
            ·
              exfalso; linarith only [h024b, h012b, h014c]
            ·
              rcases m.htr 0 2 5 (by decide) (by decide) with
                ⟨h025a, h025b, h025c⟩ | ⟨h025a, h025b, h025c⟩
              ·
                exfalso; linarith only [h025b, h015c, h012b]
              ·
                rcases m.htr 0 3 4 (by decide) (by decide) with
                  ⟨h034a, h034b, h034c⟩ | ⟨h034a, h034b, h034c⟩
                ·
                  rcases m.htr 0 3 5 (by decide) (by decide) with
                    ⟨h035a, h035b, h035c⟩ | ⟨h035a, h035b, h035c⟩
                  ·
                    rcases m.htr 0 4 5 (by decide) (by decide) with
                      ⟨h045a, h045b, h045c⟩ | ⟨h045a, h045b, h045c⟩
                    ·
                      rcases m.htr 1 2 3 (by decide) (by decide) with
                        ⟨h123a, h123b, h123c⟩ | ⟨h123a, h123b, h123c⟩
                      ·
                        exfalso; linarith only [ht0, h012a, h123a, ht45, hp1, hc03b, h023b, hc13a, ht34, h013a, ht5, ht01]
                      ·
                        exfalso; linarith only [h012a, hp1, hc12b, h013a, h123b, hc23a]
                    ·
                      exfalso; linarith only [hc12b, h014c, hp1, h012a, ht23, h045a, hc45a, ht34]
                  ·
                    exfalso; linarith only [hc12b, hp1, h012a, hc35a, h013c, ht23, h035a]
                ·
                  exfalso; linarith only [hc12b, hp1, ht23, h013c, hc34a, h034a, h012a]
  ·
    rcases m.htr 0 1 3 (by decide) (by decide) with
      ⟨h013a, h013b, h013c⟩ | ⟨h013a, h013b, h013c⟩
    ·
      rcases m.htr 0 1 4 (by decide) (by decide) with
        ⟨h014a, h014b, h014c⟩ | ⟨h014a, h014b, h014c⟩
      ·
        rcases m.htr 0 1 5 (by decide) (by decide) with
          ⟨h015a, h015b, h015c⟩ | ⟨h015a, h015b, h015c⟩
        ·
          rcases m.htr 0 2 3 (by decide) (by decide) with
            ⟨h023a, h023b, h023c⟩ | ⟨h023a, h023b, h023c⟩
          ·
            rcases m.htr 0 2 4 (by decide) (by decide) with
              ⟨h024a, h024b, h024c⟩ | ⟨h024a, h024b, h024c⟩
            ·
              rcases m.htr 0 2 5 (by decide) (by decide) with
                ⟨h025a, h025b, h025c⟩ | ⟨h025a, h025b, h025c⟩
              ·
                rcases m.htr 0 3 4 (by decide) (by decide) with
                  ⟨h034a, h034b, h034c⟩ | ⟨h034a, h034b, h034c⟩
                ·
                  rcases m.htr 0 3 5 (by decide) (by decide) with
                    ⟨h035a, h035b, h035c⟩ | ⟨h035a, h035b, h035c⟩
                  ·
                    rcases m.htr 0 4 5 (by decide) (by decide) with
                      ⟨h045a, h045b, h045c⟩ | ⟨h045a, h045b, h045c⟩
                    ·
                      rcases m.htr 1 2 3 (by decide) (by decide) with
                        ⟨h123a, h123b, h123c⟩ | ⟨h123a, h123b, h123c⟩
                      ·
                        rcases m.htr 1 2 4 (by decide) (by decide) with
                          ⟨h124a, h124b, h124c⟩ | ⟨h124a, h124b, h124c⟩
                        ·
                          rcases m.htr 1 2 5 (by decide) (by decide) with
                            ⟨h125a, h125b, h125c⟩ | ⟨h125a, h125b, h125c⟩
                          ·
                            rcases m.htr 1 3 4 (by decide) (by decide) with
                              ⟨h134a, h134b, h134c⟩ | ⟨h134a, h134b, h134c⟩
                            ·
                              exfalso; linarith only [h134a, h012a, hp1, ht01, hc12a, ht5, ht0, h013a, ht45, hc34b]
                            ·
                              exfalso; linarith only [h134a, hc13b, ht45, ht0, hp1, h012a, ht34, ht01, hc12a, h013b, h034a, ht5]
                          ·
                            exfalso; linarith only [h025c, ht45, ht01, hp1, h125a, ht34, ht12, ht0, h045b, ht5, h012a, h013b, ht23, h034b]
                        ·
                          exfalso; linarith only [ht0, ht12, ht45, ht23, h024c, h034b, hp1, ht34, h013b, ht01, h012a, h124a, ht5]
                      ·
                        exfalso; linarith only [h012a, hp1, h123a, ht23, ht0, ht12, ht5, h023c, h013b, ht34, ht01, ht45]
                    ·
                      rcases m.htr 1 2 3 (by decide) (by decide) with
                        ⟨h123a, h123b, h123c⟩ | ⟨h123a, h123b, h123c⟩
                      ·
                        rcases m.htr 1 2 4 (by decide) (by decide) with
                          ⟨h124a, h124b, h124c⟩ | ⟨h124a, h124b, h124c⟩
                        ·
                          rcases m.htr 1 2 5 (by decide) (by decide) with
                            ⟨h125a, h125b, h125c⟩ | ⟨h125a, h125b, h125c⟩
                          ·
                            rcases m.htr 1 3 4 (by decide) (by decide) with
                              ⟨h134a, h134b, h134c⟩ | ⟨h134a, h134b, h134c⟩
                            ·
                              exfalso; linarith only [ht01, h012a, hc34b, ht0, hp1, hc12a, h134a, ht5, ht45, h013a]
                            ·
                              exfalso; linarith only [ht34, h134a, hp1, h012a, ht45, ht0, hc13b, ht01, ht5, hc12a, h013b, h034a]
                          ·
                            exfalso; linarith only [ht12, ht0, ht23, hp1, h013b, ht5, ht45, h035b, h125a, ht01, h025c, ht34, h012a]
                        ·
                          exfalso; linarith only [ht34, h124a, h012a, h045a, ht0, hp1, ht12, ht5, ht45, ht23, h024c, ht01, hc01b, hc45a]
                      ·
                        exfalso; linarith only [ht0, ht23, ht45, hp1, ht12, h013b, h012a, h023c, ht5, ht34, h123a, ht01]
                  ·
                    rcases m.htr 0 4 5 (by decide) (by decide) with
                      ⟨h045a, h045b, h045c⟩ | ⟨h045a, h045b, h045c⟩
                    ·
                      exfalso; linarith only [h034b, h045b, h035c]
                    ·
                      rcases m.htr 1 2 3 (by decide) (by decide) with
                        ⟨h123a, h123b, h123c⟩ | ⟨h123a, h123b, h123c⟩
                      ·
                        rcases m.htr 1 2 4 (by decide) (by decide) with
                          ⟨h124a, h124b, h124c⟩ | ⟨h124a, h124b, h124c⟩
                        ·
                          rcases m.htr 1 2 5 (by decide) (by decide) with
                            ⟨h125a, h125b, h125c⟩ | ⟨h125a, h125b, h125c⟩
                          ·
                            rcases m.htr 1 3 4 (by decide) (by decide) with
                              ⟨h134a, h134b, h134c⟩ | ⟨h134a, h134b, h134c⟩
                            ·
                              exfalso; linarith only [hp1, ht01, ht0, h134a, ht45, hc34b, hc12a, h012a, h013a, ht5]
                            ·
                              exfalso; linarith only [ht01, ht5, hp1, ht0, ht23, h035a, hc13b, ht12, hc35a, h134a, ht45, h034a, ht34]
                          ·
                            exfalso; linarith only [ht34, h125a, h025c, h012a, hp1, ht45, ht0, ht5, ht01, ht12, ht23, h015b]
                        ·
                          exfalso; linarith only [hc35a, h012a, h124a, h035a, h024c, ht23, h034b, ht5, ht0, hp1, ht01, ht45, ht12, ht34, hc01b]
                      ·
                        exfalso; linarith only [h123a, ht23, ht34, h012a, ht0, h023c, hp1, ht45, ht12, hc35a, h035a, ht5, ht01, hc01b]
                ·
                  rcases m.htr 0 3 5 (by decide) (by decide) with
                    ⟨h035a, h035b, h035c⟩ | ⟨h035a, h035b, h035c⟩
                  ·
                    rcases m.htr 0 4 5 (by decide) (by decide) with
                      ⟨h045a, h045b, h045c⟩ | ⟨h045a, h045b, h045c⟩
                    ·
                      rcases m.htr 1 2 3 (by decide) (by decide) with
                        ⟨h123a, h123b, h123c⟩ | ⟨h123a, h123b, h123c⟩
                      ·
                        rcases m.htr 1 2 4 (by decide) (by decide) with
                          ⟨h124a, h124b, h124c⟩ | ⟨h124a, h124b, h124c⟩
                        ·
                          rcases m.htr 1 2 5 (by decide) (by decide) with
                            ⟨h125a, h125b, h125c⟩ | ⟨h125a, h125b, h125c⟩
                          ·
                            rcases m.htr 1 3 4 (by decide) (by decide) with
                              ⟨h134a, h134b, h134c⟩ | ⟨h134a, h134b, h134c⟩
                            ·
                              exfalso; linarith only [ht0, hc03b, ht5, ht34, h034a, h134a, hp1, ht23, h013a, ht01, ht45, hc12a, h012a, ht12]
                            ·
                              rcases m.htr 1 3 5 (by decide) (by decide) with
                                ⟨h135a, h135b, h135c⟩ | ⟨h135a, h135b, h135c⟩
                              ·
                                exfalso; linarith only [ht0, h014a, ht01, hp1, ht5, h012a, h134c, h135a, hc12a, hc35b]
                              ·
                                exfalso; linarith only [ht0, ht45, ht5, h012a, hc12a, hp1, h014a, h123c, ht01, h134c, hc23b, h135a, h034a, h035a, ht34, hc34a]
                          ·
                            exfalso; linarith only [ht5, h025c, ht23, ht01, ht34, ht0, h125a, ht12, h034a, h035b, hp1, hc01b, hc34a, ht45, h012a]
                        ·
                          exfalso; linarith only [ht0, ht12, ht5, h014b, ht45, hp1, ht23, h124a, h012a, ht01, ht34, h024c]
                      ·
                        exfalso; linarith only [h034a, ht12, hp1, h012a, h123a, h023c, ht5, hc01b, ht34, ht01, hc34a, ht23, ht45, ht0]
                    ·
                      exfalso; linarith only [h034c, h045c, h035b]
                  ·
                    rcases m.htr 0 4 5 (by decide) (by decide) with
                      ⟨h045a, h045b, h045c⟩ | ⟨h045a, h045b, h045c⟩
                    ·
                      rcases m.htr 1 2 3 (by decide) (by decide) with
                        ⟨h123a, h123b, h123c⟩ | ⟨h123a, h123b, h123c⟩
                      ·
                        rcases m.htr 1 2 4 (by decide) (by decide) with
                          ⟨h124a, h124b, h124c⟩ | ⟨h124a, h124b, h124c⟩
                        ·
                          rcases m.htr 1 2 5 (by decide) (by decide) with
                            ⟨h125a, h125b, h125c⟩ | ⟨h125a, h125b, h125c⟩
                          ·
                            rcases m.htr 1 3 4 (by decide) (by decide) with
                              ⟨h134a, h134b, h134c⟩ | ⟨h134a, h134b, h134c⟩
                            ·
                              exfalso; linarith only [hp1, ht01, hc12a, h013a, h012a, ht5, ht45, h134a, ht0, hc34b]
                            ·
                              rcases m.htr 1 3 5 (by decide) (by decide) with
                                ⟨h135a, h135b, h135c⟩ | ⟨h135a, h135b, h135c⟩
                              ·
                                exfalso; linarith only [ht5, ht0, h134c, h012a, hp1, hc12a, h135a, hc35b, h014a, ht01]
                              ·
                                rcases m.htr 1 4 5 (by decide) (by decide) with
                                  ⟨h145a, h145b, h145c⟩ | ⟨h145a, h145b, h145c⟩
                                ·
                                  exfalso; linarith only [h012a, hp1, hc12a, hc45b, h014a, ht5, ht01, ht0, h145a]
                                ·
                                  exfalso; linarith only [ht5, ht01, h134c, hp1, hc12a, h145a, ht34, hc23b, h123c, h045a, h014b, ht0, h012a, ht45]
                          ·
                            exfalso; linarith only [ht0, ht23, h045b, hp1, ht45, h012a, h025c, h014b, ht12, ht01, ht5, h125a, ht34]
                        ·
                          exfalso; linarith only [ht01, ht12, hp1, h012a, ht45, ht34, h124a, h014b, h024c, ht5, ht0, ht23]
                      ·
                        exfalso; linarith only [ht0, ht01, h123a, h023c, ht12, h014b, hp1, h045b, ht34, h035c, ht5, h012a, ht23, ht45]
                    ·
                      rcases m.htr 1 2 3 (by decide) (by decide) with
                        ⟨h123a, h123b, h123c⟩ | ⟨h123a, h123b, h123c⟩
                      ·
                        rcases m.htr 1 2 4 (by decide) (by decide) with
                          ⟨h124a, h124b, h124c⟩ | ⟨h124a, h124b, h124c⟩
                        ·
                          rcases m.htr 1 2 5 (by decide) (by decide) with
                            ⟨h125a, h125b, h125c⟩ | ⟨h125a, h125b, h125c⟩
                          ·
                            rcases m.htr 1 3 4 (by decide) (by decide) with
                              ⟨h134a, h134b, h134c⟩ | ⟨h134a, h134b, h134c⟩
                            ·
                              exfalso; linarith only [ht0, hc34b, ht45, h012a, hp1, h134a, hc12a, h013a, ht5, ht01]
                            ·
                              rcases m.htr 1 3 5 (by decide) (by decide) with
                                ⟨h135a, h135b, h135c⟩ | ⟨h135a, h135b, h135c⟩
                              ·
                                exfalso; linarith only [ht0, ht01, h012a, ht5, hp1, h135a, h014a, hc35b, h134c, hc12a]
                              ·
                                rcases m.htr 1 4 5 (by decide) (by decide) with
                                  ⟨h145a, h145b, h145c⟩ | ⟨h145a, h145b, h145c⟩
                                ·
                                  exfalso; linarith only [h134c, hp1, ht45, hc12a, h034c, h014a, ht0, ht5, hc03b, ht01, ht34, h145a, hc23b, h012a, h123c, h045a]
                                ·
                                  rcases m.htr 2 3 4 (by decide) (by decide) with
                                    ⟨h234a, h234b, h234c⟩ | ⟨h234a, h234b, h234c⟩
                                  ·
                                    exfalso; linarith only [h134c, ht0, h015a, ht45, h123c, hp1, ht01, hc12a, hc34b, ht5, h012a, h145c, h234a]
                                  ·
                                    rcases m.htr 2 3 5 (by decide) (by decide) with
                                      ⟨h235a, h235b, h235c⟩ | ⟨h235a, h235b, h235c⟩
                                    ·
                                      exfalso; linarith only [h235a, ht5, h015a, hc12a, h012a, hp1, hc35b, h145c, h123c, h134c, ht0, ht01]
                                    ·
                                      rcases m.htr 2 4 5 (by decide) (by decide) with
                                        ⟨h245a, h245b, h245c⟩ | ⟨h245a, h245b, h245c⟩
                                      ·
                                        exfalso; linarith only [ht34, hc03b, h015a, hc12a, h123c, h124c, h134c, ht45, hp1, ht01, ht0, h245a, h045a, hc23b, h012a, h034c, h145c, ht5]
                                      ·
                                        rcases m.htr 3 4 5 (by decide) (by decide) with
                                          ⟨h345a, h345b, h345c⟩ | ⟨h345a, h345b, h345c⟩
                                        ·
                                          exfalso; linarith only [h345a, h045a, hc03b, hp1, h034c, hc34a]
                                        ·
                                          exfalso; linarith only [h034a, hc03b, hp1, h345a, hc45a, ht34]
                          ·
                            exfalso; linarith only [h125a, ht34, ht0, h015b, ht01, h025c, ht23, ht45, ht5, h012a, hp1, ht12]
                        ·
                          exfalso; linarith only [ht0, ht01, ht23, hc45a, h045a, h012a, hc01b, ht12, hp1, ht5, h124a, ht45, h024c, ht34]
                      ·
                        exfalso; linarith only [ht23, h045a, ht0, h123a, hc01b, ht34, h023c, ht12, hp1, ht5, h012a, ht45, hc45a, h034c, ht01]
              ·
                exfalso; linarith only [h012c, h025c, h015b]
            ·
              exfalso; linarith only [h024c, h012c, h014b]
          ·
            exfalso; linarith only [h023c, h013b, h012c]
        ·
          rcases m.htr 0 2 3 (by decide) (by decide) with
            ⟨h023a, h023b, h023c⟩ | ⟨h023a, h023b, h023c⟩
          ·
            rcases m.htr 0 2 4 (by decide) (by decide) with
              ⟨h024a, h024b, h024c⟩ | ⟨h024a, h024b, h024c⟩
            ·
              rcases m.htr 0 2 5 (by decide) (by decide) with
                ⟨h025a, h025b, h025c⟩ | ⟨h025a, h025b, h025c⟩
              ·
                rcases m.htr 0 3 4 (by decide) (by decide) with
                  ⟨h034a, h034b, h034c⟩ | ⟨h034a, h034b, h034c⟩
                ·
                  rcases m.htr 0 3 5 (by decide) (by decide) with
                    ⟨h035a, h035b, h035c⟩ | ⟨h035a, h035b, h035c⟩
                  ·
                    exfalso; linarith only [h013b, h015c, h035b]
                  ·
                    rcases m.htr 0 4 5 (by decide) (by decide) with
                      ⟨h045a, h045b, h045c⟩ | ⟨h045a, h045b, h045c⟩
                    ·
                      exfalso; linarith only [h045b, h015c, hp1, h013a, h035a, h034b, hc35a, hc13b]
                    ·
                      rcases m.htr 1 2 3 (by decide) (by decide) with
                        ⟨h123a, h123b, h123c⟩ | ⟨h123a, h123b, h123c⟩
                      ·
                        rcases m.htr 1 2 4 (by decide) (by decide) with
                          ⟨h124a, h124b, h124c⟩ | ⟨h124a, h124b, h124c⟩
                        ·
                          rcases m.htr 1 2 5 (by decide) (by decide) with
                            ⟨h125a, h125b, h125c⟩ | ⟨h125a, h125b, h125c⟩
                          ·
                            rcases m.htr 1 3 4 (by decide) (by decide) with
                              ⟨h134a, h134b, h134c⟩ | ⟨h134a, h134b, h134c⟩
                            ·
                              exfalso; linarith only [h125b, hp1, h013a, h015a, ht5, hc34b, ht0, h134a, hc12a, ht45, ht01]
                            ·
                              exfalso; linarith only [hc23b, h035a, hp1, ht01, h125b, ht0, ht45, h123c, ht5, h015a, h013a, h034a, ht34, hc12a, hc35a, h134a]
                          ·
                            exfalso; linarith only [ht0, ht45, ht5, hp1, ht23, ht01, h125a, ht34, h012b, h025a, ht12]
                        ·
                          exfalso; linarith only [hc01b, ht5, h034b, ht23, h035a, ht01, ht12, hp1, h012a, ht0, h024c, ht34, hc35a, h124a, ht45]
                      ·
                        exfalso; linarith only [ht0, ht34, h035a, hc01b, ht5, h012a, ht01, hp1, ht45, ht12, ht23, hc35a, h023c, h123a]
                ·
                  rcases m.htr 0 3 5 (by decide) (by decide) with
                    ⟨h035a, h035b, h035c⟩ | ⟨h035a, h035b, h035c⟩
                  ·
                    exfalso; linarith only [h034a, h015c, hc13b, hp1, h013a, hc34a, h035b]
                  ·
                    rcases m.htr 0 4 5 (by decide) (by decide) with
                      ⟨h045a, h045b, h045c⟩ | ⟨h045a, h045b, h045c⟩
                    ·
                      exfalso; linarith only [h015c, h045b, h014b]
                    ·
                      rcases m.htr 1 2 3 (by decide) (by decide) with
                        ⟨h123a, h123b, h123c⟩ | ⟨h123a, h123b, h123c⟩
                      ·
                        rcases m.htr 1 2 4 (by decide) (by decide) with
                          ⟨h124a, h124b, h124c⟩ | ⟨h124a, h124b, h124c⟩
                        ·
                          rcases m.htr 1 2 5 (by decide) (by decide) with
                            ⟨h125a, h125b, h125c⟩ | ⟨h125a, h125b, h125c⟩
                          ·
                            rcases m.htr 1 3 4 (by decide) (by decide) with
                              ⟨h134a, h134b, h134c⟩ | ⟨h134a, h134b, h134c⟩
                            ·
                              exfalso; linarith only [h015a, hc34b, hp1, ht5, ht01, hc12a, ht0, h013a, h125b, ht45, h134a]
                            ·
                              rcases m.htr 1 3 5 (by decide) (by decide) with
                                ⟨h135a, h135b, h135c⟩ | ⟨h135a, h135b, h135c⟩
                              ·
                                exfalso; linarith only [h014a, hc12a, hp1, h125b, h135a, h015a, hc35b, ht0, ht5, h134c, ht01]
                              ·
                                exfalso; linarith only [h135b, h014a, hc23b, hp1, h134c, h015a, hc35a, h123c]
                          ·
                            exfalso; linarith only [h125a, ht0, ht23, hp1, h025a, ht45, h012b, ht34, ht12, ht5, ht01]
                        ·
                          exfalso; linarith only [ht12, hp1, hc01b, ht45, h024c, hc45a, ht0, ht34, h045a, ht23, h012a, ht01, h124a, ht5]
                      ·
                        exfalso; linarith only [hc01b, ht0, ht34, h045a, ht5, ht12, ht45, ht01, ht23, h123a, h012a, hp1, h023c, h034c, hc45a]
              ·
                rcases m.htr 0 3 4 (by decide) (by decide) with
                  ⟨h034a, h034b, h034c⟩ | ⟨h034a, h034b, h034c⟩
                ·
                  rcases m.htr 0 3 5 (by decide) (by decide) with
                    ⟨h035a, h035b, h035c⟩ | ⟨h035a, h035b, h035c⟩
                  ·
                    exfalso; linarith only [h035b, h013b, h015c]
                  ·
                    rcases m.htr 0 4 5 (by decide) (by decide) with
                      ⟨h045a, h045b, h045c⟩ | ⟨h045a, h045b, h045c⟩
                    ·
                      exfalso; linarith only [h034b, h013b, h015c, h045b]
                    ·
                      rcases m.htr 1 2 3 (by decide) (by decide) with
                        ⟨h123a, h123b, h123c⟩ | ⟨h123a, h123b, h123c⟩
                      ·
                        rcases m.htr 1 2 4 (by decide) (by decide) with
                          ⟨h124a, h124b, h124c⟩ | ⟨h124a, h124b, h124c⟩
                        ·
                          rcases m.htr 1 2 5 (by decide) (by decide) with
                            ⟨h125a, h125b, h125c⟩ | ⟨h125a, h125b, h125c⟩
                          ·
                            exfalso; linarith only [h013a, h125a, ht45, h012c, ht0, h123c, ht01, hp1, ht34, hc12a, h025a, ht5, hc23b]
                          ·
                            exfalso; linarith only [h123c, h125a, ht12, ht01, ht34, h013a, hc25a, hp1, hc23b, ht5, h012a, ht0, ht45]
                        ·
                          exfalso; linarith only [ht5, ht45, hc23b, hc25a, h123c, hp1, h025a, ht0, ht34, h024a, h012c, ht12, ht01, h124a, h013a, h012a]
                      ·
                        exfalso; linarith only [ht0, ht12, h013a, ht01, h123a, ht45, hp1, h012c, ht5, hc12b, h023a, hc25a, h025a, ht34, hc13b]
                ·
                  rcases m.htr 0 3 5 (by decide) (by decide) with
                    ⟨h035a, h035b, h035c⟩ | ⟨h035a, h035b, h035c⟩
                  ·
                    exfalso; linarith only [h034c, h014b, h035b, h015c]
                  ·
                    rcases m.htr 0 4 5 (by decide) (by decide) with
                      ⟨h045a, h045b, h045c⟩ | ⟨h045a, h045b, h045c⟩
                    ·
                      exfalso; linarith only [h015c, h014b, h045b]
                    ·
                      rcases m.htr 1 2 3 (by decide) (by decide) with
                        ⟨h123a, h123b, h123c⟩ | ⟨h123a, h123b, h123c⟩
                      ·
                        rcases m.htr 1 2 4 (by decide) (by decide) with
                          ⟨h124a, h124b, h124c⟩ | ⟨h124a, h124b, h124c⟩
                        ·
                          rcases m.htr 1 2 5 (by decide) (by decide) with
                            ⟨h125a, h125b, h125c⟩ | ⟨h125a, h125b, h125c⟩
                          ·
                            exfalso; linarith only [h125a, h012c, hp1, hc23b, ht5, ht01, ht45, h025a, h123c, hc12a, ht34, h013a, ht0]
                          ·
                            exfalso; linarith only [hc23b, ht5, hc25a, ht45, h013a, hp1, h123c, ht34, ht0, h012a, ht01, ht12, h125a]
                        ·
                          exfalso; linarith only [ht5, h024a, h025a, ht34, ht45, ht12, ht0, h012c, hc25a, h012a, ht01, hc23b, h123c, hp1, h124a, h013a]
                      ·
                        exfalso; linarith only [ht0, h012c, ht01, h023a, h123a, ht34, hp1, ht45, hc13b, h025a, ht12, ht5, h013a, hc25a, hc12b]
            ·
              exfalso; linarith only [h024c, h012c, h014b]
          ·
            exfalso; linarith only [h013b, h023c, h012c]
      ·
        rcases m.htr 0 1 5 (by decide) (by decide) with
          ⟨h015a, h015b, h015c⟩ | ⟨h015a, h015b, h015c⟩
        ·
          rcases m.htr 0 2 3 (by decide) (by decide) with
            ⟨h023a, h023b, h023c⟩ | ⟨h023a, h023b, h023c⟩
          ·
            rcases m.htr 0 2 4 (by decide) (by decide) with
              ⟨h024a, h024b, h024c⟩ | ⟨h024a, h024b, h024c⟩
            ·
              rcases m.htr 0 2 5 (by decide) (by decide) with
                ⟨h025a, h025b, h025c⟩ | ⟨h025a, h025b, h025c⟩
              ·
                rcases m.htr 0 3 4 (by decide) (by decide) with
                  ⟨h034a, h034b, h034c⟩ | ⟨h034a, h034b, h034c⟩
                ·
                  exfalso; linarith only [h013b, h034b, h014c]
                ·
                  rcases m.htr 0 3 5 (by decide) (by decide) with
                    ⟨h035a, h035b, h035c⟩ | ⟨h035a, h035b, h035c⟩
                  ·
                    rcases m.htr 0 4 5 (by decide) (by decide) with
                      ⟨h045a, h045b, h045c⟩ | ⟨h045a, h045b, h045c⟩
                    ·
                      rcases m.htr 1 2 3 (by decide) (by decide) with
                        ⟨h123a, h123b, h123c⟩ | ⟨h123a, h123b, h123c⟩
                      ·
                        rcases m.htr 1 2 4 (by decide) (by decide) with
                          ⟨h124a, h124b, h124c⟩ | ⟨h124a, h124b, h124c⟩
                        ·
                          rcases m.htr 1 2 5 (by decide) (by decide) with
                            ⟨h125a, h125b, h125c⟩ | ⟨h125a, h125b, h125c⟩
                          ·
                            rcases m.htr 1 3 4 (by decide) (by decide) with
                              ⟨h134a, h134b, h134c⟩ | ⟨h134a, h134b, h134c⟩
                            ·
                              exfalso; linarith only [hp1, ht45, ht34, h134a, ht0, h013a, hc23b, hc03b, ht5, hc12a, ht01, h034a, h124b, h014a, h123c]
                            ·
                              exfalso; linarith only [h123c, hc23b, h134b, hc34a, h014a, hp1, h013a]
                          ·
                            exfalso; linarith only [ht01, h034a, h035b, h013a, h025c, h014a, ht34, ht45, hc34a, h124b, hp1, h125a, h123c, hc12a, ht5, ht0, hc23b]
                        ·
                          exfalso; linarith only [ht45, h124a, ht0, ht34, hp1, ht23, ht5, h024a, h012b, ht01, ht12]
                      ·
                        exfalso; linarith only [ht23, ht01, hp1, h034a, h123a, ht34, ht45, ht5, ht0, hc01b, h023c, h012a, hc34a, ht12]
                    ·
                      exfalso; linarith only [hc45a, hc13b, h045a, hp1, ht34, h013a, h014c]
                  ·
                    rcases m.htr 0 4 5 (by decide) (by decide) with
                      ⟨h045a, h045b, h045c⟩ | ⟨h045a, h045b, h045c⟩
                    ·
                      rcases m.htr 1 2 3 (by decide) (by decide) with
                        ⟨h123a, h123b, h123c⟩ | ⟨h123a, h123b, h123c⟩
                      ·
                        rcases m.htr 1 2 4 (by decide) (by decide) with
                          ⟨h124a, h124b, h124c⟩ | ⟨h124a, h124b, h124c⟩
                        ·
                          rcases m.htr 1 2 5 (by decide) (by decide) with
                            ⟨h125a, h125b, h125c⟩ | ⟨h125a, h125b, h125c⟩
                          ·
                            rcases m.htr 1 3 4 (by decide) (by decide) with
                              ⟨h134a, h134b, h134c⟩ | ⟨h134a, h134b, h134c⟩
                            ·
                              exfalso; linarith only [hc23b, h013a, h123c, ht01, ht34, ht0, h014a, hp1, hc12a, hc03b, h124b, h034a, h134a, ht45, ht5]
                            ·
                              exfalso; linarith only [hc34a, h014a, hp1, hc23b, h134b, h123c, h013a]
                          ·
                            exfalso; linarith only [ht0, h124b, h025c, h014a, h015b, h125a, ht34, h013a, ht01, ht5, ht45, hc23b, hp1, hc12a, h123c]
                        ·
                          exfalso; linarith only [ht23, h024a, ht0, ht12, h012b, ht34, hp1, ht01, h124a, ht5, ht45]
                      ·
                        exfalso; linarith only [h123a, ht0, h012a, ht45, h034a, hp1, ht01, h023c, ht23, ht34, hc34a, ht5, hc01b, ht12]
                    ·
                      exfalso; linarith only [h013a, ht34, hc13b, h045a, h014c, hp1, hc45a]
              ·
                exfalso; linarith only [h024b, h015b, h025c, h014c]
            ·
              rcases m.htr 0 2 5 (by decide) (by decide) with
                ⟨h025a, h025b, h025c⟩ | ⟨h025a, h025b, h025c⟩
              ·
                rcases m.htr 0 3 4 (by decide) (by decide) with
                  ⟨h034a, h034b, h034c⟩ | ⟨h034a, h034b, h034c⟩
                ·
                  exfalso; linarith only [h013b, h014c, h034b]
                ·
                  rcases m.htr 0 3 5 (by decide) (by decide) with
                    ⟨h035a, h035b, h035c⟩ | ⟨h035a, h035b, h035c⟩
                  ·
                    rcases m.htr 0 4 5 (by decide) (by decide) with
                      ⟨h045a, h045b, h045c⟩ | ⟨h045a, h045b, h045c⟩
                    ·
                      rcases m.htr 1 2 3 (by decide) (by decide) with
                        ⟨h123a, h123b, h123c⟩ | ⟨h123a, h123b, h123c⟩
                      ·
                        rcases m.htr 1 2 4 (by decide) (by decide) with
                          ⟨h124a, h124b, h124c⟩ | ⟨h124a, h124b, h124c⟩
                        ·
                          exfalso; linarith only [hc23b, ht34, hc12a, h123c, h024a, ht5, h012c, h013a, ht45, ht0, ht01, h124a, hp1]
                        ·
                          exfalso; linarith only [hc23b, h123c, ht5, ht0, hc24a, ht34, hp1, ht45, h124a, ht12, h013a, ht01, h012a]
                      ·
                        exfalso; linarith only [ht0, ht45, h023a, ht5, h123a, h024a, hc12b, h012c, ht01, hp1, hc13b, hc24a, h013a, ht34, ht12]
                    ·
                      exfalso; linarith only [h014c, hc45a, hc13b, hp1, h045a, h013a, ht34]
                  ·
                    rcases m.htr 0 4 5 (by decide) (by decide) with
                      ⟨h045a, h045b, h045c⟩ | ⟨h045a, h045b, h045c⟩
                    ·
                      rcases m.htr 1 2 3 (by decide) (by decide) with
                        ⟨h123a, h123b, h123c⟩ | ⟨h123a, h123b, h123c⟩
                      ·
                        rcases m.htr 1 2 4 (by decide) (by decide) with
                          ⟨h124a, h124b, h124c⟩ | ⟨h124a, h124b, h124c⟩
                        ·
                          exfalso; linarith only [ht34, hc12a, ht01, ht0, h012c, h123c, h013a, h024a, hp1, h124a, ht45, ht5, hc23b]
                        ·
                          exfalso; linarith only [h123c, h012a, ht45, ht34, hp1, hc23b, ht12, h124a, h013a, ht5, ht0, hc24a, ht01]
                      ·
                        exfalso; linarith only [hc12b, ht45, ht12, ht5, h023a, hp1, ht34, h012c, h013a, h123a, hc24a, h024a, ht0, hc13b, ht01]
                    ·
                      exfalso; linarith only [hc13b, h014c, ht34, h013a, h045a, hp1, hc45a]
              ·
                exfalso; linarith only [h015b, h012c, h025c]
          ·
            exfalso; linarith only [h023c, h012c, h013b]
        ·
          rcases m.htr 0 2 3 (by decide) (by decide) with
            ⟨h023a, h023b, h023c⟩ | ⟨h023a, h023b, h023c⟩
          ·
            rcases m.htr 0 2 4 (by decide) (by decide) with
              ⟨h024a, h024b, h024c⟩ | ⟨h024a, h024b, h024c⟩
            ·
              rcases m.htr 0 2 5 (by decide) (by decide) with
                ⟨h025a, h025b, h025c⟩ | ⟨h025a, h025b, h025c⟩
              ·
                rcases m.htr 0 3 4 (by decide) (by decide) with
                  ⟨h034a, h034b, h034c⟩ | ⟨h034a, h034b, h034c⟩
                ·
                  exfalso; linarith only [h014c, h034b, h013b]
                ·
                  rcases m.htr 0 3 5 (by decide) (by decide) with
                    ⟨h035a, h035b, h035c⟩ | ⟨h035a, h035b, h035c⟩
                  ·
                    exfalso; linarith only [h034a, hp1, hc34a, h013a, h015c, h035b, hc13b]
                  ·
                    rcases m.htr 0 4 5 (by decide) (by decide) with
                      ⟨h045a, h045b, h045c⟩ | ⟨h045a, h045b, h045c⟩
                    ·
                      rcases m.htr 1 2 3 (by decide) (by decide) with
                        ⟨h123a, h123b, h123c⟩ | ⟨h123a, h123b, h123c⟩
                      ·
                        rcases m.htr 1 2 4 (by decide) (by decide) with
                          ⟨h124a, h124b, h124c⟩ | ⟨h124a, h124b, h124c⟩
                        ·
                          rcases m.htr 1 2 5 (by decide) (by decide) with
                            ⟨h125a, h125b, h125c⟩ | ⟨h125a, h125b, h125c⟩
                          ·
                            rcases m.htr 1 3 4 (by decide) (by decide) with
                              ⟨h134a, h134b, h134c⟩ | ⟨h134a, h134b, h134c⟩
                            ·
                              exfalso; linarith only [hp1, ht01, h034a, h134a, ht5, hc03b, hc23b, h013a, ht34, ht45, hc12a, ht0, h014a, h124b, h123c]
                            ·
                              exfalso; linarith only [h014a, hp1, h134b, hc23b, hc34a, h123c, h013a]
                          ·
                            exfalso; linarith only [ht0, h012b, h014a, hp1, h124b, hc12a, h125a, h025a, h013a, h123c, ht45, ht34, ht5, hc23b, ht01]
                        ·
                          exfalso; linarith only [ht0, ht23, ht5, h012b, h024a, hp1, ht12, ht34, ht45, ht01, h124a]
                      ·
                        exfalso; linarith only [ht0, ht45, ht5, hc34a, ht12, hp1, h012a, ht01, h034a, h023c, ht34, ht23, hc01b, h123a]
                    ·
                      exfalso; linarith only [h013a, h014c, h045a, hc13b, hp1, hc45a, ht34]
              ·
                rcases m.htr 0 3 4 (by decide) (by decide) with
                  ⟨h034a, h034b, h034c⟩ | ⟨h034a, h034b, h034c⟩
                ·
                  exfalso; linarith only [h034b, h014c, h013b]
                ·
                  rcases m.htr 0 3 5 (by decide) (by decide) with
                    ⟨h035a, h035b, h035c⟩ | ⟨h035a, h035b, h035c⟩
                  ·
                    exfalso; linarith only [h035b, h015c, h013b]
                  ·
                    rcases m.htr 0 4 5 (by decide) (by decide) with
                      ⟨h045a, h045b, h045c⟩ | ⟨h045a, h045b, h045c⟩
                    ·
                      exfalso; linarith only [h045b, h024b, h025c]
                    ·
                      exfalso; linarith only [hp1, ht34, hc45a, h014c, h013a, hc13b, h045a]
            ·
              rcases m.htr 0 2 5 (by decide) (by decide) with
                ⟨h025a, h025b, h025c⟩ | ⟨h025a, h025b, h025c⟩
              ·
                rcases m.htr 0 3 4 (by decide) (by decide) with
                  ⟨h034a, h034b, h034c⟩ | ⟨h034a, h034b, h034c⟩
                ·
                  exfalso; linarith only [h014c, h013b, h034b]
                ·
                  rcases m.htr 0 3 5 (by decide) (by decide) with
                    ⟨h035a, h035b, h035c⟩ | ⟨h035a, h035b, h035c⟩
                  ·
                    exfalso; linarith only [h035b, h013b, h015c]
                  ·
                    rcases m.htr 0 4 5 (by decide) (by decide) with
                      ⟨h045a, h045b, h045c⟩ | ⟨h045a, h045b, h045c⟩
                    ·
                      rcases m.htr 1 2 3 (by decide) (by decide) with
                        ⟨h123a, h123b, h123c⟩ | ⟨h123a, h123b, h123c⟩
                      ·
                        rcases m.htr 1 2 4 (by decide) (by decide) with
                          ⟨h124a, h124b, h124c⟩ | ⟨h124a, h124b, h124c⟩
                        ·
                          exfalso; linarith only [ht0, h013a, hp1, h025b, ht01, hc12a, ht5, hc23b, h015c, ht34, ht45, h123c, h124a, h024a]
                        ·
                          exfalso; linarith only [ht0, ht45, hc24a, ht34, h124a, h123c, hp1, h012a, ht12, ht01, ht5, hc23b, h013a]
                      ·
                        exfalso; linarith only [h023a, h024a, h013a, hc13b, ht01, hc12b, hc24a, hp1, h015c, h123a, ht45, ht34, ht12, h025b, ht0, ht5]
                    ·
                      exfalso; linarith only [hc45a, h013a, hc13b, h045a, ht34, hp1, h014c]
              ·
                rcases m.htr 0 3 4 (by decide) (by decide) with
                  ⟨h034a, h034b, h034c⟩ | ⟨h034a, h034b, h034c⟩
                ·
                  exfalso; linarith only [h013b, h014c, h034b]
                ·
                  rcases m.htr 0 3 5 (by decide) (by decide) with
                    ⟨h035a, h035b, h035c⟩ | ⟨h035a, h035b, h035c⟩
                  ·
                    exfalso; linarith only [h015c, h013b, h035b]
                  ·
                    rcases m.htr 0 4 5 (by decide) (by decide) with
                      ⟨h045a, h045b, h045c⟩ | ⟨h045a, h045b, h045c⟩
                    ·
                      rcases m.htr 1 2 3 (by decide) (by decide) with
                        ⟨h123a, h123b, h123c⟩ | ⟨h123a, h123b, h123c⟩
                      ·
                        rcases m.htr 1 2 4 (by decide) (by decide) with
                          ⟨h124a, h124b, h124c⟩ | ⟨h124a, h124b, h124c⟩
                        ·
                          exfalso; linarith only [h123c, h013a, ht5, h124a, hc23b, hp1, h012c, hc12a, h024a, ht0, ht34, ht01, ht45]
                        ·
                          exfalso; linarith only [h124a, ht34, ht45, ht01, ht12, ht5, hp1, h013a, hc23b, h012a, ht0, hc24a, h123c]
                      ·
                        exfalso; linarith only [h013a, ht5, hp1, ht01, hc24a, ht12, h123a, ht34, h023a, hc13b, ht45, ht0, h024a, h012c, hc12b]
                    ·
                      exfalso; linarith only [hc13b, h013a, ht34, hc45a, hp1, h014c, h045a]
          ·
            exfalso; linarith only [h012c, h013b, h023c]
    ·
      rcases m.htr 0 1 4 (by decide) (by decide) with
        ⟨h014a, h014b, h014c⟩ | ⟨h014a, h014b, h014c⟩
      ·
        rcases m.htr 0 1 5 (by decide) (by decide) with
          ⟨h015a, h015b, h015c⟩ | ⟨h015a, h015b, h015c⟩
        ·
          rcases m.htr 0 2 3 (by decide) (by decide) with
            ⟨h023a, h023b, h023c⟩ | ⟨h023a, h023b, h023c⟩
          ·
            rcases m.htr 0 2 4 (by decide) (by decide) with
              ⟨h024a, h024b, h024c⟩ | ⟨h024a, h024b, h024c⟩
            ·
              rcases m.htr 0 2 5 (by decide) (by decide) with
                ⟨h025a, h025b, h025c⟩ | ⟨h025a, h025b, h025c⟩
              ·
                rcases m.htr 0 3 4 (by decide) (by decide) with
                  ⟨h034a, h034b, h034c⟩ | ⟨h034a, h034b, h034c⟩
                ·
                  rcases m.htr 0 3 5 (by decide) (by decide) with
                    ⟨h035a, h035b, h035c⟩ | ⟨h035a, h035b, h035c⟩
                  ·
                    rcases m.htr 0 4 5 (by decide) (by decide) with
                      ⟨h045a, h045b, h045c⟩ | ⟨h045a, h045b, h045c⟩
                    ·
                      rcases m.htr 1 2 3 (by decide) (by decide) with
                        ⟨h123a, h123b, h123c⟩ | ⟨h123a, h123b, h123c⟩
                      ·
                        rcases m.htr 1 2 4 (by decide) (by decide) with
                          ⟨h124a, h124b, h124c⟩ | ⟨h124a, h124b, h124c⟩
                        ·
                          rcases m.htr 1 2 5 (by decide) (by decide) with
                            ⟨h125a, h125b, h125c⟩ | ⟨h125a, h125b, h125c⟩
                          ·
                            rcases m.htr 1 3 4 (by decide) (by decide) with
                              ⟨h134a, h134b, h134c⟩ | ⟨h134a, h134b, h134c⟩
                            ·
                              rcases m.htr 1 3 5 (by decide) (by decide) with
                                ⟨h135a, h135b, h135c⟩ | ⟨h135a, h135b, h135c⟩
                              ·
                                rcases m.htr 1 4 5 (by decide) (by decide) with
                                  ⟨h145a, h145b, h145c⟩ | ⟨h145a, h145b, h145c⟩
                                ·
                                  exfalso; linarith only [h013a, h145a, hc45b, ht0, hc12a, hp1, h123b, h014a, ht5, ht01]
                                ·
                                  exfalso; linarith only [ht45, ht01, ht0, h013a, hc14b, h045a, h123b, ht5, hp1, h014b, h145a, hc12a]
                              ·
                                exfalso; linarith only [ht0, h035c, ht12, ht45, hp1, ht5, ht23, h135a, ht01, h045b, ht34, h013a, h014b]
                            ·
                              exfalso; linarith only [ht45, h134a, hp1, h014b, ht5, ht12, h034c, ht01, ht34, ht23, h013a, ht0]
                          ·
                            exfalso; linarith only [ht0, h025c, ht5, h013a, h123b, h045b, ht34, ht45, h014b, ht23, hp1, ht01, ht12, h125a]
                        ·
                          exfalso; linarith only [ht0, ht5, ht23, ht45, ht12, hp1, ht34, h123b, ht01, h014b, h013a, h024c, h124a]
                      ·
                        exfalso; linarith only [ht45, ht23, h023a, ht5, ht12, h123a, hp1, ht0, ht34, h012b, ht01]
                    ·
                      rcases m.htr 1 2 3 (by decide) (by decide) with
                        ⟨h123a, h123b, h123c⟩ | ⟨h123a, h123b, h123c⟩
                      ·
                        rcases m.htr 1 2 4 (by decide) (by decide) with
                          ⟨h124a, h124b, h124c⟩ | ⟨h124a, h124b, h124c⟩
                        ·
                          rcases m.htr 1 2 5 (by decide) (by decide) with
                            ⟨h125a, h125b, h125c⟩ | ⟨h125a, h125b, h125c⟩
                          ·
                            rcases m.htr 1 3 4 (by decide) (by decide) with
                              ⟨h134a, h134b, h134c⟩ | ⟨h134a, h134b, h134c⟩
                            ·
                              rcases m.htr 1 3 5 (by decide) (by decide) with
                                ⟨h135a, h135b, h135c⟩ | ⟨h135a, h135b, h135c⟩
                              ·
                                rcases m.htr 1 4 5 (by decide) (by decide) with
                                  ⟨h145a, h145b, h145c⟩ | ⟨h145a, h145b, h145c⟩
                                ·
                                  exfalso; linarith only [ht01, ht45, hc04b, ht0, ht23, h045a, ht5, hp1, ht34, ht12, h014a, h013a, h145a, hc12a, h123b]
                                ·
                                  rcases m.htr 2 3 4 (by decide) (by decide) with
                                    ⟨h234a, h234b, h234c⟩ | ⟨h234a, h234b, h234c⟩
                                  ·
                                    rcases m.htr 2 3 5 (by decide) (by decide) with
                                      ⟨h235a, h235b, h235c⟩ | ⟨h235a, h235b, h235c⟩
                                    ·
                                      rcases m.htr 2 4 5 (by decide) (by decide) with
                                        ⟨h245a, h245b, h245c⟩ | ⟨h245a, h245b, h245c⟩
                                      ·
                                        exfalso; linarith only [ht0, hc34b, hp1, h123b, hc12a, h045a, ht45, h145c, h124c, h013a, ht5, h234c, h245a, hc04b, h015a, ht01]
                                      ·
                                        rcases m.htr 3 4 5 (by decide) (by decide) with
                                          ⟨h345a, h345b, h345c⟩ | ⟨h345a, h345b, h345c⟩
                                        ·
                                          exfalso; linarith only [h123b, h124c, h045a, h234c, ht01, ht0, h015a, h345a, h145c, ht5, hp1, h013a, ht45, hc34b, hc12a, hc04b]
                                        ·
                                          fin_cases i
                                          ·
                                            change linearGapScore m.lam (m.t 0) (m.t 0 + m.p) (m.rowxs 0) = 0
                                            have hpidx : (((List.finRange 6).erase (0 : Fin 6))).Perm
                                                ([2, 3, 1, 5, 4] : List (Fin 6)) := by decide
                                            have hperm := (m.row_perm 0).trans (hpidx.map (m.d 0))
                                            change (m.rowxs 0).Perm [m.d 0 2, m.d 0 3, m.d 0 1, m.d 0 5, m.d 0 4] at hperm
                                            have heq := hperm.eq_of_pairwise' (m.row_sorted _) (by
                                              simp only [List.pairwise_cons, List.mem_cons,
                                                List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, false_implies, implies_true, and_true, List.Pairwise.nil]
                                              (repeat' constructor) <;> linarith only [h012c, h013c, h014b, h015b, h023b, h024b, h025b, h034b, h035b, h045c])
                                            rw [heq]
                                            simp only [linearGapScore]
                                            rw [gapScore_zero_of_small m.hlam (by linarith only [ht45, ht23, hc02a, ht5, ht0, hp1, ht01, ht34, ht12]) (by linarith only [h234a, ht0, hp1, ht45, h023a, hc34b, ht5])]
                                            rw [gapScore_zero_of_small m.hlam (by linarith only [h023b]) (by linarith only [h012b, ht5, h234c, hp1, hc34b, h124c, h013c, h015a, ht45, hc12a, ht01, ht0, h145c])]
                                            rw [gapScore_zero_of_small m.hlam (by linarith only [h013c]) (by linarith only [ht0, hc34b, hc12a, h234c, ht01, h012b, hp1, h015a, ht5, h145c, h023b, h124c, ht45])]
                                            rw [gapScore_zero_of_small m.hlam (by linarith only [h015b]) (by linarith only [hp1, h013a, ht01, ht0, h123b, hc12a, ht5, hc05b])]
                                            rw [gapScore_zero_of_small m.hlam (by linarith only [h045c]) (by linarith only [hc12a, h013a, ht45, ht5, hc04b, ht01, h015b, ht0, hp1, h123b])]
                                            rw [gapScore_zero_of_small m.hlam (by linarith only [hp1, ht45, hc04b, ht5, ht0]) (by linarith only [ht01, hc45a, h045a, hc34b, h013a, hp1, h124c, h234c, h145c, h123b, h015a, hc12a])]
                                            try norm_num
                                          ·
                                            change linearGapScore m.lam (m.t 1) (m.t 1 + m.p) (m.rowxs 1) = 0
                                            have hpidx : (((List.finRange 6).erase (1 : Fin 6))).Perm
                                                ([2, 3, 0, 5, 4] : List (Fin 6)) := by decide
                                            have hperm := (m.row_perm 1).trans (hpidx.map (m.d 1))
                                            change (m.rowxs 1).Perm [m.d 1 2, m.d 1 3, m.d 1 0, m.d 1 5, m.d 1 4] at hperm
                                            rw [m.symm 1 0 (by decide)] at hperm
                                            have heq := hperm.eq_of_pairwise' (m.row_sorted _) (by
                                              simp only [List.pairwise_cons, List.mem_cons,
                                                List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, false_implies, implies_true, and_true, List.Pairwise.nil]
                                              (repeat' constructor) <;> linarith only [h012a, h013a, h015a, h123b, h124b, h124c, h125b, h134b, h135b, h145c, h234c, hc12a, hc34b, hp1, ht0, ht01, ht12, ht23, ht34, ht45, ht5])
                                            rw [heq]
                                            simp only [linearGapScore]
                                            rw [gapScore_zero_of_small m.hlam (by linarith only [ht45, ht23, hc12a, hp1, ht01, ht5, ht12, ht0, ht34]) (by linarith only [h234c, ht45, hp1, ht01, h123b, h124c, h145c, hc34b, h013a, ht5, h015a, ht0])]
                                            rw [gapScore_zero_of_small m.hlam (by linarith only [h123b]) (by linarith only [hc12a, hp1, h015a, h145c, hc34b, h123b, ht45, ht5, h013a, h234c, h124c, ht01, ht0])]
                                            rw [gapScore_zero_of_small m.hlam (by linarith only [ht0, hp1, ht5, ht01, ht45, ht23, ht34, ht12, h013a]) (by linarith only [ht01, hp1, h123b, h015a, hc34b, h124c, ht45, h145c, h234c, ht0, hc12a, ht5])]
                                            rw [gapScore_zero_of_small m.hlam (by linarith only [h234c, hp1, hc34b, h013a, ht5, ht45, h145c, h015a, hc12a, h124c, ht01, ht0, h123b]) (by linarith only [hc12a, ht5, hp1, ht01, h013a, h124c, h234c, ht0, hc34b, h123b, h145c, ht45])]
                                            rw [gapScore_zero_of_small m.hlam (by linarith only [h145c]) (by linarith only [h145c, h123b, h234c, h013a, ht5, ht01, hc12a, ht45, h015a, hc34b, ht0, hp1, h124c])]
                                            rw [gapScore_zero_of_small m.hlam (by linarith only [ht01, ht45, hp1, hc14b, ht5, ht0]) (by linarith only [hc12a, ht5, hc34b, ht0, h123b, h234c, h145c, ht45, h013a, h124c, ht01, hp1, h015a])]
                                            try norm_num
                                          ·
                                            change linearGapScore m.lam (m.t 2) (m.t 2 + m.p) (m.rowxs 2) = 0
                                            have hpidx : (((List.finRange 6).erase (2 : Fin 6))).Perm
                                                ([1, 0, 3, 5, 4] : List (Fin 6)) := by decide
                                            have hperm := (m.row_perm 2).trans (hpidx.map (m.d 2))
                                            change (m.rowxs 2).Perm [m.d 2 1, m.d 2 0, m.d 2 3, m.d 2 5, m.d 2 4] at hperm
                                            rw [m.symm 2 1 (by decide)] at hperm
                                            rw [m.symm 2 0 (by decide)] at hperm
                                            have heq := hperm.eq_of_pairwise' (m.row_sorted _) (by
                                              simp only [List.pairwise_cons, List.mem_cons,
                                                List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, false_implies, implies_true, and_true, List.Pairwise.nil]
                                              (repeat' constructor) <;> linarith only [h012b, h013a, h015a, h023a, h025a, h123b, h124c, h125c, h145c, h234b, h234c, h235b, h245c, hc12a, hc23b, hc34b, hp1, ht0, ht01, ht12, ht23, ht34, ht45, ht5])
                                            rw [heq]
                                            simp only [linearGapScore]
                                            rw [gapScore_zero_of_small m.hlam (by linarith only [ht23, hp1, ht5, hc12a, ht01, ht34, ht0, ht45]) (by linarith only [ht5, h124c, ht01, ht12, h234c, hc34b, hp1, h145c, h015a, h013a, ht45, h123b, ht0])]
                                            rw [gapScore_zero_of_small m.hlam (by linarith only [h012b]) (by linarith only [hc12a, ht34, h023a, ht0, hc23b, ht5, ht45, ht01, hp1])]
                                            rw [gapScore_zero_of_small m.hlam (by linarith only [hp1, ht5, ht45, ht34, ht01, h023a, ht12, ht0, ht23]) (by linarith only [ht5, hp1, ht0, hc12a, hc34b, ht01, h012b, ht45, h234a])]
                                            rw [gapScore_zero_of_small m.hlam (by linarith only [h235b]) (by linarith only [hc12a, ht0, ht5, hc25b, h023a, ht01, hp1, h012b])]
                                            rw [gapScore_zero_of_small m.hlam (by linarith only [h245c]) (by linarith only [ht01, hp1, ht0, h124c, h013a, ht45, h015a, hc34b, h125c, h123b, h234c, hc12a, ht5, h145c])]
                                            rw [gapScore_zero_of_small m.hlam (by linarith only [ht0, ht5, ht12, hp1, ht45, hc24b, ht01]) (by linarith only [h015a, hp1, ht01, ht0, hc12a, ht5, ht34, ht23, h013a, h124c, h123b, ht45, h145c])]
                                            try norm_num
                                          ·
                                            change linearGapScore m.lam (m.t 3) (m.t 3 + m.p) (m.rowxs 3) = 0
                                            have hpidx : (((List.finRange 6).erase (3 : Fin 6))).Perm
                                                ([1, 0, 2, 5, 4] : List (Fin 6)) := by decide
                                            have hperm := (m.row_perm 3).trans (hpidx.map (m.d 3))
                                            change (m.rowxs 3).Perm [m.d 3 1, m.d 3 0, m.d 3 2, m.d 3 5, m.d 3 4] at hperm
                                            rw [m.symm 3 1 (by decide)] at hperm
                                            rw [m.symm 3 0 (by decide)] at hperm
                                            rw [m.symm 3 2 (by decide)] at hperm
                                            have heq := hperm.eq_of_pairwise' (m.row_sorted _) (by
                                              simp only [List.pairwise_cons, List.mem_cons,
                                                List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, false_implies, implies_true, and_true, List.Pairwise.nil]
                                              (repeat' constructor) <;> linarith only [h013a, h013b, h013c, h015a, h023c, h035a, h123b, h123c, h124c, h125c, h145c, h234a, h234c, h235c, h345c, hc03b, hc12a, hc23b, hc34b, hp1, ht0, ht01, ht12, ht23, ht34, ht45, ht5])
                                            rw [heq]
                                            simp only [linearGapScore]
                                            rw [gapScore_zero_of_small m.hlam (by linarith only [hc12a, hp1, ht0, ht34, ht01, h123b, ht5, ht45]) (by linarith only [h145c, h015a, h013a, h234c, ht5, hp1, ht45, h124c, ht12, ht0, ht23, ht01, hc34b])]
                                            rw [gapScore_zero_of_small m.hlam (by linarith only [h013b]) (by linarith only [h234c, ht5, h145c, ht01, hc12a, h124c, h013c, hp1, ht45, h123b, h015a, hc34b, ht0])]
                                            rw [gapScore_zero_of_small m.hlam (by linarith only [h023c]) (by linarith only [hc34b, hc12a, hp1, ht01, ht45, ht5, ht0, h012b, h234a, h023b])]
                                            rw [gapScore_zero_of_small m.hlam (by linarith only [h235c, ht5, h123b, hp1, h015a, ht01, hc12a, h125c, h234a, h013a, ht45, hc34b, ht0]) (by linarith only [ht0, h012b, hp1, ht01, hc35b, h023a, ht5, hc12a])]
                                            rw [gapScore_zero_of_small m.hlam (by linarith only [h345c]) (by linarith only [hc12a, h123b, h015a, h234c, ht0, ht5, ht45, hc34b, h013a, h145c, ht01, h124c, h125c, h235c, hp1])]
                                            rw [gapScore_zero_of_small m.hlam (by linarith only [ht5, ht0, ht23, ht45, hc34b, hp1, ht01, ht12]) (by linarith only [h123b, ht0, hp1, h145c, ht5, h124c, h013a, hc12a, h015a, ht01, ht45, h234c, ht34])]
                                            try norm_num
                                          ·
                                            change linearGapScore m.lam (m.t 4) (m.t 4 + m.p) (m.rowxs 4) = 0
                                            have hpidx : (((List.finRange 6).erase (4 : Fin 6))).Perm
                                                ([5, 0, 1, 2, 3] : List (Fin 6)) := by decide
                                            have hperm := (m.row_perm 4).trans (hpidx.map (m.d 4))
                                            change (m.rowxs 4).Perm [m.d 4 5, m.d 4 0, m.d 4 1, m.d 4 2, m.d 4 3] at hperm
                                            rw [m.symm 4 0 (by decide)] at hperm
                                            rw [m.symm 4 1 (by decide)] at hperm
                                            rw [m.symm 4 2 (by decide)] at hperm
                                            rw [m.symm 4 3 (by decide)] at hperm
                                            have heq := hperm.eq_of_pairwise' (m.row_sorted _) (by
                                              simp only [List.pairwise_cons, List.mem_cons,
                                                List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, false_implies, implies_true, and_true, List.Pairwise.nil]
                                              (repeat' constructor) <;> linarith only [h012b, h013a, h014c, h015a, h023b, h024c, h034a, h034c, h045a, h123b, h124c, h134c, h145c, h234c, hc04b, hc12a, hc24b, hc34b, hp1, ht0, ht01, ht45, ht5])
                                            rw [heq]
                                            simp only [linearGapScore]
                                            rw [gapScore_zero_of_small m.hlam (by linarith only [ht0, hc12a, h145c, h124c, hp1, h123b, hc45a, hc34b, h234c, ht5, ht01, ht45, h015a, h013a]) (by linarith only [h045a, hp1, hc04b])]
                                            rw [gapScore_zero_of_small m.hlam (by linarith only [h013a, ht01, hc12a, ht0, h123b, h234c, ht5, h145c, h015a, h124c, hc34b, h045a, ht45, hp1]) (by linarith only [hp1, hc04b, hc45a])]
                                            rw [gapScore_zero_of_small m.hlam (by linarith only [h014c]) (by linarith only [hc12a, h015a, ht5, h045a, h013a, hc34b, ht45, h234c, hp1, ht01, h145c, ht0, hc45a, h123b, h124c])]
                                            rw [gapScore_zero_of_small m.hlam (by linarith only [h124c]) (by linarith only [h145c, ht01, hc12a, hp1, hc34b, h015a, ht45, ht5, h234c, h123b, h124c, h013a, ht0])]
                                            rw [gapScore_zero_of_small m.hlam (by linarith only [h234c]) (by linarith only [h145c, h234c, ht01, h015a, h124c, hc34b, hc12a, ht5, h123b, hp1, ht0, ht45, h013a])]
                                            rw [gapScore_zero_of_small m.hlam (by linarith only [ht01, ht23, ht12, ht0, hp1, ht5, ht34, ht45, hc34b]) (by linarith only [hp1, h234c, h123b, h124c, h013a, ht45, ht5, hc12a, h145c, ht01, ht0, h015a])]
                                            try norm_num
                                          ·
                                            change linearGapScore m.lam (m.t 5) (m.t 5 + m.p) (m.rowxs 5) = 0
                                            have hpidx : (((List.finRange 6).erase (5 : Fin 6))).Perm
                                                ([4, 0, 1, 2, 3] : List (Fin 6)) := by decide
                                            have hperm := (m.row_perm 5).trans (hpidx.map (m.d 5))
                                            change (m.rowxs 5).Perm [m.d 5 4, m.d 5 0, m.d 5 1, m.d 5 2, m.d 5 3] at hperm
                                            rw [m.symm 5 4 (by decide)] at hperm
                                            rw [m.symm 5 0 (by decide)] at hperm
                                            rw [m.symm 5 1 (by decide)] at hperm
                                            rw [m.symm 5 2 (by decide)] at hperm
                                            rw [m.symm 5 3 (by decide)] at hperm
                                            have heq := hperm.eq_of_pairwise' (m.row_sorted _) (by
                                              simp only [List.pairwise_cons, List.mem_cons,
                                                List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, false_implies, implies_true, and_true, List.Pairwise.nil]
                                              (repeat' constructor) <;> linarith only [h015c, h025c, h035c, h045b, h125c, h135c, h145b, h235c, h245b, h345b])
                                            rw [heq]
                                            simp only [linearGapScore]
                                            rw [gapScore_zero_of_small m.hlam (by linarith only [ht5, ht34, ht12, hp1, ht23, hc45a, ht0, ht01]) (by linarith only [hp1, ht45, h045a, hc04b])]
                                            rw [gapScore_zero_of_small m.hlam (by linarith only [h045b]) (by linarith only [h234c, hc34b, h015c, hc45a, h145c, h124c, hp1])]
                                            rw [gapScore_zero_of_small m.hlam (by linarith only [h015c]) (by linarith only [ht01, h123b, h234c, hp1, ht0, h013a, ht45, h145c, ht5, hc12a, h124c, hc34b, h015b])]
                                            rw [gapScore_zero_of_small m.hlam (by linarith only [h125c]) (by linarith only [ht01, h145c, ht0, h013a, hc34b, h124c, h234c, hc25b, h123b, ht5, h015a, hc12a, ht45, hp1])]
                                            rw [gapScore_zero_of_small m.hlam (by linarith only [h235c]) (by linarith only [hc34b, hc12a, ht5, ht01, h234c, h145c, hc35b, hp1, ht45, h124c, h013a, h125c, h123b, ht0, h015a])]
                                            rw [gapScore_zero_of_small m.hlam (by linarith only [ht0, ht23, ht45, ht5, hp1, ht01, ht34, hc35b, ht12]) (by linarith only [h015a, hp1, hc12a, ht5, h013a, ht01, h123b, h125c, h235c, ht0])]
                                            try norm_num
                                    ·
                                      exfalso; linarith only [ht45, h013a, ht01, hp1, h135c, ht34, h015a, h123b, ht0, h235a, ht5, hc12a, hc23b]
                                  ·
                                    exfalso; linarith only [ht45, h013a, hc23b, ht0, h015a, hp1, h145c, ht34, h234a, ht5, ht01, h123b, h134c, hc12a]
                              ·
                                exfalso; linarith only [ht0, ht23, h035c, hp1, h135a, ht5, ht01, h015b, ht12, ht45, ht34, h013a]
                            ·
                              exfalso; linarith only [ht0, ht01, ht23, ht45, hp1, hc45a, h013a, ht34, h134a, ht5, hc01b, h034c, ht12, h045a]
                          ·
                            exfalso; linarith only [ht0, h013a, h025c, h123b, h015b, ht45, h125a, ht34, ht01, hp1, ht23, ht5, ht12]
                        ·
                          exfalso; linarith only [h124a, h045a, h123b, h013a, hp1, ht5, ht23, ht45, hc45a, ht34, ht0, ht01, hc01b, ht12, h024c]
                      ·
                        exfalso; linarith only [ht5, ht23, ht0, ht34, ht01, ht12, h012b, hp1, h023a, ht45, h123a]
                  ·
                    exfalso; linarith only [h035c, h013c, h015b]
                ·
                  exfalso; linarith only [h013c, h034c, h014b]
              ·
                exfalso; linarith only [h025c, h023b, h013c, h015b]
            ·
              exfalso; linarith only [h024c, h013c, h023b, h014b]
          ·
            rcases m.htr 0 2 4 (by decide) (by decide) with
              ⟨h024a, h024b, h024c⟩ | ⟨h024a, h024b, h024c⟩
            ·
              rcases m.htr 0 2 5 (by decide) (by decide) with
                ⟨h025a, h025b, h025c⟩ | ⟨h025a, h025b, h025c⟩
              ·
                rcases m.htr 0 3 4 (by decide) (by decide) with
                  ⟨h034a, h034b, h034c⟩ | ⟨h034a, h034b, h034c⟩
                ·
                  rcases m.htr 0 3 5 (by decide) (by decide) with
                    ⟨h035a, h035b, h035c⟩ | ⟨h035a, h035b, h035c⟩
                  ·
                    rcases m.htr 0 4 5 (by decide) (by decide) with
                      ⟨h045a, h045b, h045c⟩ | ⟨h045a, h045b, h045c⟩
                    ·
                      rcases m.htr 1 2 3 (by decide) (by decide) with
                        ⟨h123a, h123b, h123c⟩ | ⟨h123a, h123b, h123c⟩
                      ·
                        exfalso; linarith only [hp1, h023a, hc01b, h012c, hc12a, h123a]
                      ·
                        exfalso; linarith only [hp1, hc01b, ht12, h012a, hc23a, h123a]
                    ·
                      rcases m.htr 1 2 3 (by decide) (by decide) with
                        ⟨h123a, h123b, h123c⟩ | ⟨h123a, h123b, h123c⟩
                      ·
                        exfalso; linarith only [h012c, h023a, hc01b, hp1, h123a, hc12a]
                      ·
                        exfalso; linarith only [hp1, h012a, h123a, ht12, hc01b, hc23a]
                  ·
                    exfalso; linarith only [h023c, h035c, h015b, h012c]
                ·
                  exfalso; linarith only [h014b, h023c, h012c, h034c]
              ·
                exfalso; linarith only [h015b, h025c, h012c]
            ·
              exfalso; linarith only [h012c, h014b, h024c]
        ·
          rcases m.htr 0 2 3 (by decide) (by decide) with
            ⟨h023a, h023b, h023c⟩ | ⟨h023a, h023b, h023c⟩
          ·
            rcases m.htr 0 2 4 (by decide) (by decide) with
              ⟨h024a, h024b, h024c⟩ | ⟨h024a, h024b, h024c⟩
            ·
              rcases m.htr 0 2 5 (by decide) (by decide) with
                ⟨h025a, h025b, h025c⟩ | ⟨h025a, h025b, h025c⟩
              ·
                rcases m.htr 0 3 4 (by decide) (by decide) with
                  ⟨h034a, h034b, h034c⟩ | ⟨h034a, h034b, h034c⟩
                ·
                  rcases m.htr 0 3 5 (by decide) (by decide) with
                    ⟨h035a, h035b, h035c⟩ | ⟨h035a, h035b, h035c⟩
                  ·
                    rcases m.htr 0 4 5 (by decide) (by decide) with
                      ⟨h045a, h045b, h045c⟩ | ⟨h045a, h045b, h045c⟩
                    ·
                      exfalso; linarith only [h014b, h015c, h045b]
                    ·
                      rcases m.htr 1 2 3 (by decide) (by decide) with
                        ⟨h123a, h123b, h123c⟩ | ⟨h123a, h123b, h123c⟩
                      ·
                        rcases m.htr 1 2 4 (by decide) (by decide) with
                          ⟨h124a, h124b, h124c⟩ | ⟨h124a, h124b, h124c⟩
                        ·
                          rcases m.htr 1 2 5 (by decide) (by decide) with
                            ⟨h125a, h125b, h125c⟩ | ⟨h125a, h125b, h125c⟩
                          ·
                            rcases m.htr 1 3 4 (by decide) (by decide) with
                              ⟨h134a, h134b, h134c⟩ | ⟨h134a, h134b, h134c⟩
                            ·
                              rcases m.htr 1 3 5 (by decide) (by decide) with
                                ⟨h135a, h135b, h135c⟩ | ⟨h135a, h135b, h135c⟩
                              ·
                                rcases m.htr 1 4 5 (by decide) (by decide) with
                                  ⟨h145a, h145b, h145c⟩ | ⟨h145a, h145b, h145c⟩
                                ·
                                  exfalso; linarith only [ht45, hc24b, h135b, h045a, h014a, ht01, ht5, hc04b, h123b, h015a, hp1, h124c, ht0, hc12a, h145a]
                                ·
                                  exfalso; linarith only [h014a, hc45a, h015a, hp1, hc24b, h124c, h145b]
                              ·
                                exfalso; linarith only [h012b, h023b, hp1, ht23, ht12, h035a, ht01, ht0, h135a, ht45, h013a, hc01b, ht5, ht34, hc12a]
                            ·
                              exfalso; linarith only [ht23, ht0, h134a, ht34, hc45a, ht01, hp1, h034c, ht5, h013a, h045a, hc01b, ht12, ht45]
                          ·
                            exfalso; linarith only [ht0, h012b, ht23, ht45, ht5, hp1, h125a, ht34, ht01, h025a, ht12]
                        ·
                          exfalso; linarith only [ht23, ht0, ht45, h013a, h124a, hp1, ht5, ht01, hc01b, ht34, ht12, hc45a, h024c, h123b, h045a]
                      ·
                        exfalso; linarith only [ht0, ht45, ht34, h012b, hp1, ht12, h123a, ht5, ht23, h023a, ht01]
                  ·
                    rcases m.htr 0 4 5 (by decide) (by decide) with
                      ⟨h045a, h045b, h045c⟩ | ⟨h045a, h045b, h045c⟩
                    ·
                      exfalso; linarith only [h015c, h014b, h045b]
                    ·
                      rcases m.htr 1 2 3 (by decide) (by decide) with
                        ⟨h123a, h123b, h123c⟩ | ⟨h123a, h123b, h123c⟩
                      ·
                        rcases m.htr 1 2 4 (by decide) (by decide) with
                          ⟨h124a, h124b, h124c⟩ | ⟨h124a, h124b, h124c⟩
                        ·
                          rcases m.htr 1 2 5 (by decide) (by decide) with
                            ⟨h125a, h125b, h125c⟩ | ⟨h125a, h125b, h125c⟩
                          ·
                            rcases m.htr 1 3 4 (by decide) (by decide) with
                              ⟨h134a, h134b, h134c⟩ | ⟨h134a, h134b, h134c⟩
                            ·
                              rcases m.htr 1 3 5 (by decide) (by decide) with
                                ⟨h135a, h135b, h135c⟩ | ⟨h135a, h135b, h135c⟩
                              ·
                                exfalso; linarith only [h014a, hc12a, hp1, hc24b, h013c, h035a, ht01, h123b, ht45, ht5, ht0, h124c, h135a]
                              ·
                                exfalso; linarith only [h014a, ht12, h135a, ht45, ht23, hc24b, hc35a, ht01, hp1, h124c, ht0, ht5, h013a]
                            ·
                              exfalso; linarith only [hc13b, ht0, h014a, h013c, ht45, h035a, ht12, hc24b, hp1, h124c, hc35a, ht23, ht5, h134a, h034a, ht01]
                          ·
                            exfalso; linarith only [h125a, ht0, ht01, ht23, h014a, h012b, h124c, h025a, ht12, hc35a, ht45, h013c, hp1, h035a, hc24b, ht5]
                        ·
                          exfalso; linarith only [h035a, h124a, h013c, hp1, hc35a, h012b, hc02b, h014b, h024c, ht23]
                      ·
                        exfalso; linarith only [h123a, hp1, hc35a, ht23, h012b, hc02b, h035a, h023c]
                ·
                  exfalso; linarith only [h034c, h013c, h014b]
              ·
                rcases m.htr 0 3 4 (by decide) (by decide) with
                  ⟨h034a, h034b, h034c⟩ | ⟨h034a, h034b, h034c⟩
                ·
                  rcases m.htr 0 3 5 (by decide) (by decide) with
                    ⟨h035a, h035b, h035c⟩ | ⟨h035a, h035b, h035c⟩
                  ·
                    exfalso; linarith only [h035b, h023b, h025c]
                  ·
                    rcases m.htr 0 4 5 (by decide) (by decide) with
                      ⟨h045a, h045b, h045c⟩ | ⟨h045a, h045b, h045c⟩
                    ·
                      exfalso; linarith only [h015c, h014b, h045b]
                    ·
                      rcases m.htr 1 2 3 (by decide) (by decide) with
                        ⟨h123a, h123b, h123c⟩ | ⟨h123a, h123b, h123c⟩
                      ·
                        rcases m.htr 1 2 4 (by decide) (by decide) with
                          ⟨h124a, h124b, h124c⟩ | ⟨h124a, h124b, h124c⟩
                        ·
                          rcases m.htr 1 2 5 (by decide) (by decide) with
                            ⟨h125a, h125b, h125c⟩ | ⟨h125a, h125b, h125c⟩
                          ·
                            exfalso; linarith only [ht0, h124c, hp1, ht01, h013c, h025a, hc12a, hc24b, ht45, h014a, ht5, h023b, h125a]
                          ·
                            exfalso; linarith only [hc25a, h125a, h124c, ht01, ht5, hp1, hc24b, ht45, ht0, h012a, h014a, ht12]
                        ·
                          exfalso; linarith only [h025a, h124a, ht5, hp1, h024a, ht12, h014a, ht0, hc14b, h023b, hc12b, hc25a, ht01, h013c, ht45]
                      ·
                        exfalso; linarith only [ht01, h123a, hc12b, ht0, ht5, hc25a, h023b, hp1, h023a, h025a, h014a, h013c, ht45, hc14b, ht12]
                ·
                  exfalso; linarith only [h034c, h013c, h014b]
            ·
              exfalso; linarith only [h013c, h014b, h023b, h024c]
          ·
            rcases m.htr 0 2 4 (by decide) (by decide) with
              ⟨h024a, h024b, h024c⟩ | ⟨h024a, h024b, h024c⟩
            ·
              rcases m.htr 0 2 5 (by decide) (by decide) with
                ⟨h025a, h025b, h025c⟩ | ⟨h025a, h025b, h025c⟩
              ·
                rcases m.htr 0 3 4 (by decide) (by decide) with
                  ⟨h034a, h034b, h034c⟩ | ⟨h034a, h034b, h034c⟩
                ·
                  rcases m.htr 0 3 5 (by decide) (by decide) with
                    ⟨h035a, h035b, h035c⟩ | ⟨h035a, h035b, h035c⟩
                  ·
                    rcases m.htr 0 4 5 (by decide) (by decide) with
                      ⟨h045a, h045b, h045c⟩ | ⟨h045a, h045b, h045c⟩
                    ·
                      exfalso; linarith only [h045b, h014b, h015c]
                    ·
                      rcases m.htr 1 2 3 (by decide) (by decide) with
                        ⟨h123a, h123b, h123c⟩ | ⟨h123a, h123b, h123c⟩
                      ·
                        exfalso; linarith only [h015c, h023a, ht01, h025b, hp1, h014a, ht45, ht5, hc12a, h123a, hc14b, ht0]
                      ·
                        exfalso; linarith only [ht0, ht5, ht45, hc23a, hc14b, hp1, ht12, h014a, ht01, h012a, h123a]
                  ·
                    exfalso; linarith only [h025b, h035c, h023c]
                ·
                  exfalso; linarith only [h023c, h025b, h015c, h034c, h014b]
              ·
                rcases m.htr 0 3 4 (by decide) (by decide) with
                  ⟨h034a, h034b, h034c⟩ | ⟨h034a, h034b, h034c⟩
                ·
                  rcases m.htr 0 3 5 (by decide) (by decide) with
                    ⟨h035a, h035b, h035c⟩ | ⟨h035a, h035b, h035c⟩
                  ·
                    rcases m.htr 0 4 5 (by decide) (by decide) with
                      ⟨h045a, h045b, h045c⟩ | ⟨h045a, h045b, h045c⟩
                    ·
                      exfalso; linarith only [h045b, h015c, h014b]
                    ·
                      rcases m.htr 1 2 3 (by decide) (by decide) with
                        ⟨h123a, h123b, h123c⟩ | ⟨h123a, h123b, h123c⟩
                      ·
                        exfalso; linarith only [h023a, h123a, hc12a, h012c, hp1, hc01b]
                      ·
                        exfalso; linarith only [h123a, hc01b, hp1, h012a, ht12, hc23a]
                  ·
                    rcases m.htr 0 4 5 (by decide) (by decide) with
                      ⟨h045a, h045b, h045c⟩ | ⟨h045a, h045b, h045c⟩
                    ·
                      exfalso; linarith only [h014b, h045b, h015c]
                    ·
                      rcases m.htr 1 2 3 (by decide) (by decide) with
                        ⟨h123a, h123b, h123c⟩ | ⟨h123a, h123b, h123c⟩
                      ·
                        exfalso; linarith only [hc14b, ht0, ht5, h012c, ht45, hc12a, ht01, hp1, h023a, h014a, h123a]
                      ·
                        exfalso; linarith only [hc23a, hc14b, ht0, hp1, h014a, h012a, ht45, h123a, ht5, ht01, ht12]
                ·
                  exfalso; linarith only [h012c, h014b, h034c, h023c]
            ·
              exfalso; linarith only [h012c, h024c, h014b]
      ·
        rcases m.htr 0 1 5 (by decide) (by decide) with
          ⟨h015a, h015b, h015c⟩ | ⟨h015a, h015b, h015c⟩
        ·
          rcases m.htr 0 2 3 (by decide) (by decide) with
            ⟨h023a, h023b, h023c⟩ | ⟨h023a, h023b, h023c⟩
          ·
            rcases m.htr 0 2 4 (by decide) (by decide) with
              ⟨h024a, h024b, h024c⟩ | ⟨h024a, h024b, h024c⟩
            ·
              rcases m.htr 0 2 5 (by decide) (by decide) with
                ⟨h025a, h025b, h025c⟩ | ⟨h025a, h025b, h025c⟩
              ·
                rcases m.htr 0 3 4 (by decide) (by decide) with
                  ⟨h034a, h034b, h034c⟩ | ⟨h034a, h034b, h034c⟩
                ·
                  rcases m.htr 0 3 5 (by decide) (by decide) with
                    ⟨h035a, h035b, h035c⟩ | ⟨h035a, h035b, h035c⟩
                  ·
                    rcases m.htr 0 4 5 (by decide) (by decide) with
                      ⟨h045a, h045b, h045c⟩ | ⟨h045a, h045b, h045c⟩
                    ·
                      rcases m.htr 1 2 3 (by decide) (by decide) with
                        ⟨h123a, h123b, h123c⟩ | ⟨h123a, h123b, h123c⟩
                      ·
                        rcases m.htr 1 2 4 (by decide) (by decide) with
                          ⟨h124a, h124b, h124c⟩ | ⟨h124a, h124b, h124c⟩
                        ·
                          rcases m.htr 1 2 5 (by decide) (by decide) with
                            ⟨h125a, h125b, h125c⟩ | ⟨h125a, h125b, h125c⟩
                          ·
                            rcases m.htr 1 3 4 (by decide) (by decide) with
                              ⟨h134a, h134b, h134c⟩ | ⟨h134a, h134b, h134c⟩
                            ·
                              rcases m.htr 1 3 5 (by decide) (by decide) with
                                ⟨h135a, h135b, h135c⟩ | ⟨h135a, h135b, h135c⟩
                              ·
                                rcases m.htr 1 4 5 (by decide) (by decide) with
                                  ⟨h145a, h145b, h145c⟩ | ⟨h145a, h145b, h145c⟩
                                ·
                                  rcases m.htr 2 3 4 (by decide) (by decide) with
                                    ⟨h234a, h234b, h234c⟩ | ⟨h234a, h234b, h234c⟩
                                  ·
                                    rcases m.htr 2 3 5 (by decide) (by decide) with
                                      ⟨h235a, h235b, h235c⟩ | ⟨h235a, h235b, h235c⟩
                                    ·
                                      rcases m.htr 2 4 5 (by decide) (by decide) with
                                        ⟨h245a, h245b, h245c⟩ | ⟨h245a, h245b, h245c⟩
                                      ·
                                        rcases m.htr 3 4 5 (by decide) (by decide) with
                                          ⟨h345a, h345b, h345c⟩ | ⟨h345a, h345b, h345c⟩
                                        ·
                                          exfalso; linarith only [ht01, h012b, h345a, h023a, h234a, ht5, hp1, ht0, hc45b, hc12a]
                                        ·
                                          exfalso; linarith only [ht01, h014a, hp1, hc12a, h245c, h345a, ht0, ht5, h123b, h125c, h134b, h015a, ht45, hc34b]
                                      ·
                                        exfalso; linarith only [h245a, ht0, hc12a, h015a, h134b, ht01, hc24b, hp1, ht5, h145c, h014a, h123b, ht45]
                                    ·
                                      exfalso; linarith only [h123b, ht45, h014a, h134b, hp1, h235a, ht34, h135c, hc23b, h015a, ht0, ht5, ht01, hc12a]
                                  ·
                                    rcases m.htr 2 3 5 (by decide) (by decide) with
                                      ⟨h235a, h235b, h235c⟩ | ⟨h235a, h235b, h235c⟩
                                    ·
                                      exfalso; linarith only [ht0, ht5, hc35b, hp1, hc12a, h034a, ht01, h234a, h235a, h023b, h012b]
                                    ·
                                      exfalso; linarith only [hc23b, h123b, ht01, hc12a, h014a, ht45, ht5, ht34, hp1, h015a, ht0, h235a, h134b, h135c]
                                ·
                                  exfalso; linarith only [ht0, ht5, ht34, ht45, hp1, ht12, h014a, ht23, ht01, h015b, h145a, h045c]
                              ·
                                exfalso; linarith only [ht34, ht45, ht5, hp1, ht01, ht23, h135a, ht12, h035c, ht0, h014a, h134b, h015b]
                            ·
                              exfalso; linarith only [ht45, h013a, ht01, ht0, hc12a, h012b, ht5, ht34, hp1, h134a, h023b, hc01b, h034a, ht12, ht23]
                          ·
                            exfalso; linarith only [ht0, ht5, h125a, ht01, ht34, hp1, ht45, h013a, h123b, ht23, h015b, h025c, ht12]
                        ·
                          exfalso; linarith only [ht34, ht01, ht45, hp1, ht5, h012b, ht12, ht23, h024a, h124a, ht0]
                      ·
                        exfalso; linarith only [ht5, ht01, hp1, ht12, ht34, h123a, ht0, ht23, h023a, h012b, ht45]
                    ·
                      exfalso; linarith only [h015b, h014c, h045c]
                  ·
                    exfalso; linarith only [h014c, h035c, h015b, h034b]
                ·
                  rcases m.htr 0 3 5 (by decide) (by decide) with
                    ⟨h035a, h035b, h035c⟩ | ⟨h035a, h035b, h035c⟩
                  ·
                    rcases m.htr 0 4 5 (by decide) (by decide) with
                      ⟨h045a, h045b, h045c⟩ | ⟨h045a, h045b, h045c⟩
                    ·
                      rcases m.htr 1 2 3 (by decide) (by decide) with
                        ⟨h123a, h123b, h123c⟩ | ⟨h123a, h123b, h123c⟩
                      ·
                        rcases m.htr 1 2 4 (by decide) (by decide) with
                          ⟨h124a, h124b, h124c⟩ | ⟨h124a, h124b, h124c⟩
                        ·
                          rcases m.htr 1 2 5 (by decide) (by decide) with
                            ⟨h125a, h125b, h125c⟩ | ⟨h125a, h125b, h125c⟩
                          ·
                            rcases m.htr 1 3 4 (by decide) (by decide) with
                              ⟨h134a, h134b, h134c⟩ | ⟨h134a, h134b, h134c⟩
                            ·
                              exfalso; linarith only [h015a, hc12a, h134a, h125c, ht01, h123b, h013c, h034a, hp1, hc25b, ht5, ht0]
                            ·
                              exfalso; linarith only [h134a, hp1, hc25b, h013a, ht0, hc34a, h125c, ht23, ht01, ht5, h015a, ht12]
                          ·
                            exfalso; linarith only [h025c, ht23, h015b, hc34a, h013c, hp1, h125a, h034a, hc02b, h012b]
                        ·
                          exfalso; linarith only [hp1, ht01, h012b, ht34, h024a, ht5, ht0, ht12, h124a, ht45, ht23]
                      ·
                        exfalso; linarith only [h123a, hc34a, h023c, ht23, hp1, h034a, h012b, hc02b]
                    ·
                      exfalso; linarith only [h013c, h045c, h015b, h034c]
                  ·
                    exfalso; linarith only [h013c, h015b, h035c]
              ·
                exfalso; linarith only [h025c, h023b, h015b, h013c]
            ·
              rcases m.htr 0 2 5 (by decide) (by decide) with
                ⟨h025a, h025b, h025c⟩ | ⟨h025a, h025b, h025c⟩
              ·
                rcases m.htr 0 3 4 (by decide) (by decide) with
                  ⟨h034a, h034b, h034c⟩ | ⟨h034a, h034b, h034c⟩
                ·
                  exfalso; linarith only [h023b, h024c, h034b]
                ·
                  rcases m.htr 0 3 5 (by decide) (by decide) with
                    ⟨h035a, h035b, h035c⟩ | ⟨h035a, h035b, h035c⟩
                  ·
                    rcases m.htr 0 4 5 (by decide) (by decide) with
                      ⟨h045a, h045b, h045c⟩ | ⟨h045a, h045b, h045c⟩
                    ·
                      rcases m.htr 1 2 3 (by decide) (by decide) with
                        ⟨h123a, h123b, h123c⟩ | ⟨h123a, h123b, h123c⟩
                      ·
                        rcases m.htr 1 2 4 (by decide) (by decide) with
                          ⟨h124a, h124b, h124c⟩ | ⟨h124a, h124b, h124c⟩
                        ·
                          exfalso; linarith only [h013c, h124a, h023b, hp1, hc01b, hc12a, h024a]
                        ·
                          exfalso; linarith only [ht12, hc01b, hc24a, h124a, hp1, h012a]
                      ·
                        exfalso; linarith only [ht45, ht23, ht12, ht01, h023a, h123a, ht34, hp1, ht5, hc12b, hc24a, h024a, ht0]
                    ·
                      exfalso; linarith only [h024c, hp1, h023a, ht34, h045a, hc23b, hc45a]
                  ·
                    exfalso; linarith only [h035c, h013c, h015b]
              ·
                exfalso; linarith only [h015b, h013c, h025c, h023b]
          ·
            rcases m.htr 0 2 4 (by decide) (by decide) with
              ⟨h024a, h024b, h024c⟩ | ⟨h024a, h024b, h024c⟩
            ·
              rcases m.htr 0 2 5 (by decide) (by decide) with
                ⟨h025a, h025b, h025c⟩ | ⟨h025a, h025b, h025c⟩
              ·
                rcases m.htr 0 3 4 (by decide) (by decide) with
                  ⟨h034a, h034b, h034c⟩ | ⟨h034a, h034b, h034c⟩
                ·
                  rcases m.htr 0 3 5 (by decide) (by decide) with
                    ⟨h035a, h035b, h035c⟩ | ⟨h035a, h035b, h035c⟩
                  ·
                    rcases m.htr 0 4 5 (by decide) (by decide) with
                      ⟨h045a, h045b, h045c⟩ | ⟨h045a, h045b, h045c⟩
                    ·
                      rcases m.htr 1 2 3 (by decide) (by decide) with
                        ⟨h123a, h123b, h123c⟩ | ⟨h123a, h123b, h123c⟩
                      ·
                        exfalso; linarith only [h123a, h014c, h023a, hc01b, hc12a, h024b, hp1]
                      ·
                        exfalso; linarith only [h012a, hp1, ht12, hc01b, h123a, hc23a]
                    ·
                      exfalso; linarith only [h014c, h015b, h045c]
                  ·
                    exfalso; linarith only [h023c, h035c, h024b, h015b, h014c]
                ·
                  exfalso; linarith only [h023c, h034c, h024b]
              ·
                exfalso; linarith only [h014c, h025c, h015b, h024b]
            ·
              rcases m.htr 0 2 5 (by decide) (by decide) with
                ⟨h025a, h025b, h025c⟩ | ⟨h025a, h025b, h025c⟩
              ·
                rcases m.htr 0 3 4 (by decide) (by decide) with
                  ⟨h034a, h034b, h034c⟩ | ⟨h034a, h034b, h034c⟩
                ·
                  rcases m.htr 0 3 5 (by decide) (by decide) with
                    ⟨h035a, h035b, h035c⟩ | ⟨h035a, h035b, h035c⟩
                  ·
                    rcases m.htr 0 4 5 (by decide) (by decide) with
                      ⟨h045a, h045b, h045c⟩ | ⟨h045a, h045b, h045c⟩
                    ·
                      rcases m.htr 1 2 3 (by decide) (by decide) with
                        ⟨h123a, h123b, h123c⟩ | ⟨h123a, h123b, h123c⟩
                      ·
                        exfalso; linarith only [h023a, h123a, hc01b, hp1, h012c, hc12a]
                      ·
                        exfalso; linarith only [ht12, h012a, hp1, h123a, hc01b, hc23a]
                    ·
                      exfalso; linarith only [h012c, h015b, h024c, h045c]
                  ·
                    exfalso; linarith only [h015b, h034b, h024c, h035c, h012c]
                ·
                  rcases m.htr 0 3 5 (by decide) (by decide) with
                    ⟨h035a, h035b, h035c⟩ | ⟨h035a, h035b, h035c⟩
                  ·
                    rcases m.htr 0 4 5 (by decide) (by decide) with
                      ⟨h045a, h045b, h045c⟩ | ⟨h045a, h045b, h045c⟩
                    ·
                      rcases m.htr 1 2 3 (by decide) (by decide) with
                        ⟨h123a, h123b, h123c⟩ | ⟨h123a, h123b, h123c⟩
                      ·
                        exfalso; linarith only [h023a, ht0, ht5, h012c, hc15b, hp1, ht01, hc12a, h123a, h015a]
                      ·
                        exfalso; linarith only [ht5, h123a, hc23a, hc15b, hp1, ht01, h012a, ht12, h015a, ht0]
                    ·
                      exfalso; linarith only [h015b, h045c, h034c, h023c, h012c]
                  ·
                    exfalso; linarith only [h035c, h012c, h023c, h015b]
              ·
                exfalso; linarith only [h025c, h012c, h015b]
        ·
          rcases m.htr 0 2 3 (by decide) (by decide) with
            ⟨h023a, h023b, h023c⟩ | ⟨h023a, h023b, h023c⟩
          ·
            rcases m.htr 0 2 4 (by decide) (by decide) with
              ⟨h024a, h024b, h024c⟩ | ⟨h024a, h024b, h024c⟩
            ·
              rcases m.htr 0 2 5 (by decide) (by decide) with
                ⟨h025a, h025b, h025c⟩ | ⟨h025a, h025b, h025c⟩
              ·
                rcases m.htr 0 3 4 (by decide) (by decide) with
                  ⟨h034a, h034b, h034c⟩ | ⟨h034a, h034b, h034c⟩
                ·
                  rcases m.htr 0 3 5 (by decide) (by decide) with
                    ⟨h035a, h035b, h035c⟩ | ⟨h035a, h035b, h035c⟩
                  ·
                    rcases m.htr 0 4 5 (by decide) (by decide) with
                      ⟨h045a, h045b, h045c⟩ | ⟨h045a, h045b, h045c⟩
                    ·
                      rcases m.htr 1 2 3 (by decide) (by decide) with
                        ⟨h123a, h123b, h123c⟩ | ⟨h123a, h123b, h123c⟩
                      ·
                        rcases m.htr 1 2 4 (by decide) (by decide) with
                          ⟨h124a, h124b, h124c⟩ | ⟨h124a, h124b, h124c⟩
                        ·
                          rcases m.htr 1 2 5 (by decide) (by decide) with
                            ⟨h125a, h125b, h125c⟩ | ⟨h125a, h125b, h125c⟩
                          ·
                            rcases m.htr 1 3 4 (by decide) (by decide) with
                              ⟨h134a, h134b, h134c⟩ | ⟨h134a, h134b, h134c⟩
                            ·
                              rcases m.htr 1 3 5 (by decide) (by decide) with
                                ⟨h135a, h135b, h135c⟩ | ⟨h135a, h135b, h135c⟩
                              ·
                                rcases m.htr 1 4 5 (by decide) (by decide) with
                                  ⟨h145a, h145b, h145c⟩ | ⟨h145a, h145b, h145c⟩
                                ·
                                  rcases m.htr 2 3 4 (by decide) (by decide) with
                                    ⟨h234a, h234b, h234c⟩ | ⟨h234a, h234b, h234c⟩
                                  ·
                                    rcases m.htr 2 3 5 (by decide) (by decide) with
                                      ⟨h235a, h235b, h235c⟩ | ⟨h235a, h235b, h235c⟩
                                    ·
                                      rcases m.htr 2 4 5 (by decide) (by decide) with
                                        ⟨h245a, h245b, h245c⟩ | ⟨h245a, h245b, h245c⟩
                                      ·
                                        rcases m.htr 3 4 5 (by decide) (by decide) with
                                          ⟨h345a, h345b, h345c⟩ | ⟨h345a, h345b, h345c⟩
                                        ·
                                          exfalso; linarith only [ht01, h023a, h345a, ht5, hp1, hc45b, h012b, ht0, hc12a, h234a]
                                        ·
                                          exfalso; linarith only [hc34b, h234b, ht5, hp1, hc12a, ht0, h023a, h245a, h345a, ht01, ht45, h012b]
                                      ·
                                        rcases m.htr 3 4 5 (by decide) (by decide) with
                                          ⟨h345a, h345b, h345c⟩ | ⟨h345a, h345b, h345c⟩
                                        ·
                                          exfalso; linarith only [ht0, h234c, h345a, hc12a, hp1, h023b, ht45, hc34b, h012b, h245a, h045a, ht5, ht01, h034b]
                                        ·
                                          fin_cases i
                                          ·
                                            change linearGapScore m.lam (m.t 0) (m.t 0 + m.p) (m.rowxs 0) = 0
                                            have hpidx : (((List.finRange 6).erase (0 : Fin 6))).Perm
                                                ([2, 3, 4, 5, 1] : List (Fin 6)) := by decide
                                            have hperm := (m.row_perm 0).trans (hpidx.map (m.d 0))
                                            change (m.rowxs 0).Perm [m.d 0 2, m.d 0 3, m.d 0 4, m.d 0 5, m.d 0 1] at hperm
                                            have heq := hperm.eq_of_pairwise' (m.row_sorted _) (by
                                              simp only [List.pairwise_cons, List.mem_cons,
                                                List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, false_implies, implies_true, and_true, List.Pairwise.nil]
                                              (repeat' constructor) <;> linarith only [h012c, h013c, h014c, h015c, h023b, h024b, h025b, h034b, h035b, h045b])
                                            rw [heq]
                                            simp only [linearGapScore]
                                            rw [gapScore_zero_of_small m.hlam (by linarith only [ht12, ht5, ht23, ht45, hp1, ht0, ht34, hc02a, ht01]) (by linarith only [ht0, hp1, h045a, hc34b, h023b, h245a, h234c, h034b, ht5, ht45])]
                                            rw [gapScore_zero_of_small m.hlam (by linarith only [h023b]) (by linarith only [hp1, h034b, h012b, hc12a, ht01, h045a, hc34b, h023b, ht0, ht45, h234c, h245a, ht5])]
                                            rw [gapScore_zero_of_small m.hlam (by linarith only [h034b]) (by linarith only [h034b, ht0, ht01, h023b, hp1, h045a, ht45, h245a, ht5, hc34b, h234c, hc12a, h012b])]
                                            rw [gapScore_zero_of_small m.hlam (by linarith only [h045b]) (by linarith only [h012b, h015c, hc12a, hc01b, h034b, hp1, h023b])]
                                            rw [gapScore_zero_of_small m.hlam (by linarith only [h015c]) (by linarith only [h023b, h045b, h012b, hc01b, h034b, hc12a, hp1])]
                                            rw [gapScore_zero_of_small m.hlam (by linarith only [ht34, ht45, ht5, hp1, ht12, ht0, ht23, hc01b]) (by linarith only [hc12a, h015a, hp1, ht01, h134b, h145b, h123b])]
                                            try norm_num
                                          ·
                                            change linearGapScore m.lam (m.t 1) (m.t 1 + m.p) (m.rowxs 1) = 0
                                            have hpidx : (((List.finRange 6).erase (1 : Fin 6))).Perm
                                                ([2, 3, 4, 5, 0] : List (Fin 6)) := by decide
                                            have hperm := (m.row_perm 1).trans (hpidx.map (m.d 1))
                                            change (m.rowxs 1).Perm [m.d 1 2, m.d 1 3, m.d 1 4, m.d 1 5, m.d 1 0] at hperm
                                            rw [m.symm 1 0 (by decide)] at hperm
                                            have heq := hperm.eq_of_pairwise' (m.row_sorted _) (by
                                              simp only [List.pairwise_cons, List.mem_cons,
                                                List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, false_implies, implies_true, and_true, List.Pairwise.nil]
                                              (repeat' constructor) <;> linarith only [h012a, h013a, h014a, h015a, h123b, h124b, h125b, h134b, h135b, h145b, hp1, ht0, ht01, ht12, ht23, ht34, ht45, ht5])
                                            rw [heq]
                                            simp only [linearGapScore]
                                            rw [gapScore_zero_of_small m.hlam (by linarith only [ht34, hc12a, hp1, ht01, ht23, ht5, ht12, ht45, ht0]) (by linarith only [h034b, hp1, ht5, ht0, h234c, h245a, h012b, hc34b, h045a, ht01, h023b, ht45])]
                                            rw [gapScore_zero_of_small m.hlam (by linarith only [h123b]) (by linarith only [ht5, hc12a, ht0, h245a, hc01b, h023b, hc34b, ht01, h134b, h145b, h015a, h012b, h034b, hp1, ht45, h234c, h045a])]
                                            rw [gapScore_zero_of_small m.hlam (by linarith only [h134b]) (by linarith only [ht45, h245a, hc01b, hc34b, h034b, hc12a, h012b, ht0, h123b, ht5, h234c, h045a, h015a, hp1, ht01, h145b, h023b])]
                                            rw [gapScore_zero_of_small m.hlam (by linarith only [h145b]) (by linarith only [hc34b, hc12a, ht01, h245a, h023b, ht5, h045a, ht0, hp1, ht45, hc01b, h034b, h234c, h015a, h123b, h134b, h012b])]
                                            rw [gapScore_zero_of_small m.hlam (by linarith only [ht34, ht5, ht45, ht23, ht0, ht12, h015a, hp1, ht01]) (by linarith only [hp1, h123b, h134b, hc12a, h145b, hc01b])]
                                            rw [gapScore_zero_of_small m.hlam (by linarith only [ht0, hp1, ht12, ht5, ht01, hc01b, ht34, ht45, ht23]) (by linarith only [hp1, h015a, h145b, h123b, h134b, hc12a])]
                                            try norm_num
                                          ·
                                            change linearGapScore m.lam (m.t 2) (m.t 2 + m.p) (m.rowxs 2) = 0
                                            have hpidx : (((List.finRange 6).erase (2 : Fin 6))).Perm
                                                ([1, 0, 3, 5, 4] : List (Fin 6)) := by decide
                                            have hperm := (m.row_perm 2).trans (hpidx.map (m.d 2))
                                            change (m.rowxs 2).Perm [m.d 2 1, m.d 2 0, m.d 2 3, m.d 2 5, m.d 2 4] at hperm
                                            rw [m.symm 2 1 (by decide)] at hperm
                                            rw [m.symm 2 0 (by decide)] at hperm
                                            have heq := hperm.eq_of_pairwise' (m.row_sorted _) (by
                                              simp only [List.pairwise_cons, List.mem_cons,
                                                List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, false_implies, implies_true, and_true, List.Pairwise.nil]
                                              (repeat' constructor) <;> linarith only [h012b, h023a, h023b, h025a, h034b, h045a, h234b, h234c, h235b, h245a, h245b, h245c, hc12a, hc34b, hp1, ht0, ht01, ht12, ht23, ht34, ht45, ht5])
                                            rw [heq]
                                            simp only [linearGapScore]
                                            rw [gapScore_zero_of_small m.hlam (by linarith only [hc12a, ht34, ht23, ht5, ht45, ht01, hp1, ht0]) (by linarith only [h012b, h045a, ht12, ht0, ht01, h245a, ht45, ht5, hp1, h023b, h034b, h234c, hc34b])]
                                            rw [gapScore_zero_of_small m.hlam (by linarith only [h012b]) (by linarith only [ht0, ht01, hc12a, h234c, hc34b, h012b, ht5, h034b, h245a, ht45, hp1, h023b, h045a])]
                                            rw [gapScore_zero_of_small m.hlam (by linarith only [ht34, h023a, ht23, ht45, ht12, hp1, ht01, ht0, ht5]) (by linarith only [hp1, hc35b, ht5, hc12a, h012b, ht01, h235a, ht0])]
                                            rw [gapScore_zero_of_small m.hlam (by linarith only [h235b]) (by linarith only [ht5, hp1, ht0, ht01, h012b, hc12a, hc25b, h023a])]
                                            rw [gapScore_zero_of_small m.hlam (by linarith only [h245c]) (by linarith only [ht0, h023b, h045a, h245b, h012b, ht45, h234c, hc12a, hp1, ht5, h034b, hc34b, ht01])]
                                            rw [gapScore_zero_of_small m.hlam (by linarith only [ht5, ht45, ht0, ht01, ht12, hp1, hc24b]) (by linarith only [ht45, hc12a, h245a, h023b, ht0, ht01, h012b, ht34, h034b, ht5, h045a, hp1, ht23])]
                                            try norm_num
                                          ·
                                            change linearGapScore m.lam (m.t 3) (m.t 3 + m.p) (m.rowxs 3) = 0
                                            have hpidx : (((List.finRange 6).erase (3 : Fin 6))).Perm
                                                ([1, 0, 2, 5, 4] : List (Fin 6)) := by decide
                                            have hperm := (m.row_perm 3).trans (hpidx.map (m.d 3))
                                            change (m.rowxs 3).Perm [m.d 3 1, m.d 3 0, m.d 3 2, m.d 3 5, m.d 3 4] at hperm
                                            rw [m.symm 3 1 (by decide)] at hperm
                                            rw [m.symm 3 0 (by decide)] at hperm
                                            rw [m.symm 3 2 (by decide)] at hperm
                                            have heq := hperm.eq_of_pairwise' (m.row_sorted _) (by
                                              simp only [List.pairwise_cons, List.mem_cons,
                                                List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, false_implies, implies_true, and_true, List.Pairwise.nil]
                                              (repeat' constructor) <;> linarith only [h012b, h013b, h015a, h023a, h023b, h023c, h034b, h035a, h045a, h123c, h134b, h145b, h234c, h235a, h245a, h345c, hc01b, hc12a, hc34b, hc35b, hp1, ht0, ht01, ht12, ht23, ht34, ht45, ht5])
                                            rw [heq]
                                            simp only [linearGapScore]
                                            rw [gapScore_zero_of_small m.hlam (by linarith only [h123b, hc12a, ht45, ht0, ht34, ht01, hp1, ht5]) (by linarith only [ht12, h145b, hc01b, h015a, ht23, h134b, hp1])]
                                            rw [gapScore_zero_of_small m.hlam (by linarith only [h013b]) (by linarith only [hp1, h245a, ht01, ht5, hc34b, h023b, hc12a, h234c, h012b, h123b, h045a, h034b, ht45, ht0])]
                                            rw [gapScore_zero_of_small m.hlam (by linarith only [h023c]) (by linarith only [hp1, h023b, hc35b, ht5, ht01, ht0, hc12a, h012b, h235a])]
                                            rw [gapScore_zero_of_small m.hlam (by linarith only [h234c, hp1, hc12a, h012b, h245a, h235a, ht5, h045a, h023b, ht01, ht0, h034b, hc34b, ht45]) (by linarith only [ht0, ht5, hp1, h023a, h012b, hc35b, ht01, hc12a])]
                                            rw [gapScore_zero_of_small m.hlam (by linarith only [h345c]) (by linarith only [hc34b, ht01, h023b, h023a, h045a, h245a, hc12a, ht45, h234c, h034b, hp1, ht5, h235a, ht0, h012b])]
                                            rw [gapScore_zero_of_small m.hlam (by linarith only [ht0, ht5, hp1, ht45, hc34b, ht01, ht12, ht23]) (by linarith only [ht45, ht0, h034b, h045a, hc12a, h023b, h012b, ht01, h245a, ht5, ht34, hp1, h234c])]
                                            try norm_num
                                          ·
                                            change linearGapScore m.lam (m.t 4) (m.t 4 + m.p) (m.rowxs 4) = 0
                                            have hpidx : (((List.finRange 6).erase (4 : Fin 6))).Perm
                                                ([1, 0, 5, 2, 3] : List (Fin 6)) := by decide
                                            have hperm := (m.row_perm 4).trans (hpidx.map (m.d 4))
                                            change (m.rowxs 4).Perm [m.d 4 1, m.d 4 0, m.d 4 5, m.d 4 2, m.d 4 3] at hperm
                                            rw [m.symm 4 1 (by decide)] at hperm
                                            rw [m.symm 4 0 (by decide)] at hperm
                                            rw [m.symm 4 2 (by decide)] at hperm
                                            rw [m.symm 4 3 (by decide)] at hperm
                                            have heq := hperm.eq_of_pairwise' (m.row_sorted _) (by
                                              simp only [List.pairwise_cons, List.mem_cons,
                                                List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, false_implies, implies_true, and_true, List.Pairwise.nil]
                                              (repeat' constructor) <;> linarith only [h012b, h014b, h023a, h023b, h024c, h034b, h034c, h045a, h124c, h134c, h234a, h234c, h245a, hc12a, hc24b, hc34b, hp1, ht0, ht01, ht12, ht23, ht34, ht45, ht5])
                                            rw [heq]
                                            simp only [linearGapScore]
                                            rw [gapScore_zero_of_small m.hlam (by linarith only [h123b, hp1, hc12a, ht5, ht0, ht01, h134b, ht45]) (by linarith only [h023b, h234c, hc01b, hp1, h145b, h015a, hc12a, h045a, hc34b, h034b, h245a, h012b])]
                                            rw [gapScore_zero_of_small m.hlam (by linarith only [h014b]) (by linarith only [h245a, hp1, ht0, hc12a, ht45, ht5, hc34b, h012b, ht01, h234c, h134b, h045a, h034b, h023b, h123b])]
                                            rw [gapScore_zero_of_small m.hlam (by linarith only [ht0, ht5, h045a, ht23, hp1, ht45, ht01, ht34, ht12]) (by linarith only [hp1, ht01, h234c, h023b, ht0, h034b, h012b, hc12a, h245a, ht5, hc34b, ht45])]
                                            rw [gapScore_zero_of_small m.hlam (by linarith only [h023b, h234c, ht5, h045a, hp1, h245a, h034b, ht45, h012b, hc34b, ht0, ht01, hc12a]) (by linarith only [h012b, ht45, ht01, h234c, h034b, hp1, hc34b, ht0, h023b, ht5, h045a, hc12a])]
                                            rw [gapScore_zero_of_small m.hlam (by linarith only [h234c]) (by linarith only [ht0, ht45, h045a, hc34b, hp1, h012b, h234c, ht01, hc12a, ht5, h034b, h245a, h023b])]
                                            rw [gapScore_zero_of_small m.hlam (by linarith only [ht0, ht12, hp1, ht34, ht5, ht01, hc34b, ht23, ht45]) (by linarith only [ht45, ht01, h012b, ht0, hp1, h023b, h245a, h034b, h234c, h045a, hc12a, ht5])]
                                            try norm_num
                                          ·
                                            change linearGapScore m.lam (m.t 5) (m.t 5 + m.p) (m.rowxs 5) = 0
                                            have hpidx : (((List.finRange 6).erase (5 : Fin 6))).Perm
                                                ([1, 0, 4, 2, 3] : List (Fin 6)) := by decide
                                            have hperm := (m.row_perm 5).trans (hpidx.map (m.d 5))
                                            change (m.rowxs 5).Perm [m.d 5 1, m.d 5 0, m.d 5 4, m.d 5 2, m.d 5 3] at hperm
                                            rw [m.symm 5 1 (by decide)] at hperm
                                            rw [m.symm 5 0 (by decide)] at hperm
                                            rw [m.symm 5 4 (by decide)] at hperm
                                            rw [m.symm 5 2 (by decide)] at hperm
                                            rw [m.symm 5 3 (by decide)] at hperm
                                            have heq := hperm.eq_of_pairwise' (m.row_sorted _) (by
                                              simp only [List.pairwise_cons, List.mem_cons,
                                                List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, false_implies, implies_true, and_true, List.Pairwise.nil]
                                              (repeat' constructor) <;> linarith only [h015b, h025c, h035c, h045c, h125c, h135c, h145c, h235c, h245b, h345b])
                                            rw [heq]
                                            simp only [linearGapScore]
                                            rw [gapScore_zero_of_small m.hlam (by linarith only [ht01, ht0, ht5, hp1, hc15a]) (by linarith only [hp1, hc01b, hc34b, hc12a, h015a, h034b, ht45, h234c, h245a, h045a, h012b, h023b])]
                                            rw [gapScore_zero_of_small m.hlam (by linarith only [h015b]) (by linarith only [h015c, hc12a, h123b, hc01b, hp1, h134b, h145b])]
                                            rw [gapScore_zero_of_small m.hlam (by linarith only [h045c]) (by linarith only [hp1, h245a, hc12a, ht5, h023b, h234c, h012b, ht0, ht01, h034b, h045b, hc34b, ht45])]
                                            rw [gapScore_zero_of_small m.hlam (by linarith only [h245b]) (by linarith only [ht0, ht5, h012b, ht01, h034b, hc12a, hc25b, h023b, hp1, h045a])]
                                            rw [gapScore_zero_of_small m.hlam (by linarith only [h235c]) (by linarith only [ht01, h012b, h245b, h045a, h034b, ht0, ht5, hp1, hc35b, hc12a, h023b])]
                                            rw [gapScore_zero_of_small m.hlam (by linarith only [ht45, hc35b, ht23, hp1, ht12, ht5, ht01, ht0, ht34]) (by linarith only [hp1, ht0, ht5, h023a, ht01, h235a, hc12a, h012b])]
                                            try norm_num
                                    ·
                                      exfalso; linarith only [h235a, hc34b, hc12a, h012b, hp1, ht45, ht0, h234a, ht5, h035a, h023b, ht01]
                                  ·
                                    rcases m.htr 2 3 5 (by decide) (by decide) with
                                      ⟨h235a, h235b, h235c⟩ | ⟨h235a, h235b, h235c⟩
                                    ·
                                      exfalso; linarith only [hp1, h235a, hc35b, h234a, h012b, ht5, hc12a, ht0, h034a, h023b, ht01]
                                    ·
                                      rcases m.htr 2 4 5 (by decide) (by decide) with
                                        ⟨h245a, h245b, h245c⟩ | ⟨h245a, h245b, h245c⟩
                                      ·
                                        rcases m.htr 3 4 5 (by decide) (by decide) with
                                          ⟨h345a, h345b, h345c⟩ | ⟨h345a, h345b, h345c⟩
                                        ·
                                          fin_cases i
                                          ·
                                            change linearGapScore m.lam (m.t 0) (m.t 0 + m.p) (m.rowxs 0) = 0
                                            have hpidx : (((List.finRange 6).erase (0 : Fin 6))).Perm
                                                ([2, 3, 4, 5, 1] : List (Fin 6)) := by decide
                                            have hperm := (m.row_perm 0).trans (hpidx.map (m.d 0))
                                            change (m.rowxs 0).Perm [m.d 0 2, m.d 0 3, m.d 0 4, m.d 0 5, m.d 0 1] at hperm
                                            have heq := hperm.eq_of_pairwise' (m.row_sorted _) (by
                                              simp only [List.pairwise_cons, List.mem_cons,
                                                List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, false_implies, implies_true, and_true, List.Pairwise.nil]
                                              (repeat' constructor) <;> linarith only [h012c, h013c, h014c, h015c, h023b, h024b, h025b, h034b, h035b, h045b])
                                            rw [heq]
                                            simp only [linearGapScore]
                                            rw [gapScore_zero_of_small m.hlam (by linarith only [ht12, ht5, hc02a, ht01, ht23, ht0, hp1, ht34, ht45]) (by linarith only [hp1, ht0, h235a, hc23b, h034a, ht5, h023b, h345b, ht45, ht34])]
                                            rw [gapScore_zero_of_small m.hlam (by linarith only [h023b]) (by linarith only [hc12a, h034a, h012b, ht0, hp1, ht34, ht45, ht01, hc23b, h023b, h345b, h235a, ht5])]
                                            rw [gapScore_zero_of_small m.hlam (by linarith only [h034b]) (by linarith only [h014c, hp1, hc12a, hc01b, h012b, h023b])]
                                            rw [gapScore_zero_of_small m.hlam (by linarith only [h045b]) (by linarith only [h015c, h023b, h012b, hc01b, h034b, hp1, hc12a])]
                                            rw [gapScore_zero_of_small m.hlam (by linarith only [h015c]) (by linarith only [h012b, h034b, hp1, hc12a, hc01b, h045b, h023b])]
                                            rw [gapScore_zero_of_small m.hlam (by linarith only [ht23, ht0, hp1, hc01b, ht45, ht5, ht34, ht12]) (by linarith only [h123b, hp1, h145b, hc12a, h134b, ht01, h015a])]
                                            try norm_num
                                          ·
                                            change linearGapScore m.lam (m.t 1) (m.t 1 + m.p) (m.rowxs 1) = 0
                                            have hpidx : (((List.finRange 6).erase (1 : Fin 6))).Perm
                                                ([2, 3, 4, 5, 0] : List (Fin 6)) := by decide
                                            have hperm := (m.row_perm 1).trans (hpidx.map (m.d 1))
                                            change (m.rowxs 1).Perm [m.d 1 2, m.d 1 3, m.d 1 4, m.d 1 5, m.d 1 0] at hperm
                                            rw [m.symm 1 0 (by decide)] at hperm
                                            have heq := hperm.eq_of_pairwise' (m.row_sorted _) (by
                                              simp only [List.pairwise_cons, List.mem_cons,
                                                List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, false_implies, implies_true, and_true, List.Pairwise.nil]
                                              (repeat' constructor) <;> linarith only [h012a, h013a, h014a, h015a, h123b, h124b, h125b, h134b, h135b, h145b, hp1, ht0, ht01, ht12, ht23, ht34, ht45, ht5])
                                            rw [heq]
                                            simp only [linearGapScore]
                                            rw [gapScore_zero_of_small m.hlam (by linarith only [hp1, ht34, hc12a, ht12, ht45, ht0, ht01, ht5, ht23]) (by linarith only [hp1, h023b, h012b, ht01, h235a, ht34, h345b, h034a, ht0, ht45, hc23b, ht5])]
                                            rw [gapScore_zero_of_small m.hlam (by linarith only [h123b]) (by linarith only [h235a, hc23b, h034a, hp1, ht45, h015a, ht5, h023b, hc12a, hc01b, h012b, ht34, h145b, ht01, h134b, h345b, ht0])]
                                            rw [gapScore_zero_of_small m.hlam (by linarith only [h134b]) (by linarith only [h123b, h015a, hp1, h235a, h012b, ht0, ht01, hc23b, h034a, h345b, h145b, ht34, hc12a, ht5, h023b, hc01b, ht45])]
                                            rw [gapScore_zero_of_small m.hlam (by linarith only [h145b]) (by linarith only [ht0, ht34, h023b, ht01, h123b, h012b, h034a, h015a, hc23b, ht45, hc12a, h134b, hc01b, h345b, h235a, hp1, ht5])]
                                            rw [gapScore_zero_of_small m.hlam (by linarith only [ht5, ht12, ht0, ht45, ht23, ht01, hp1, ht34, h015a]) (by linarith only [hp1, h134b, h123b, h145b, hc01b, hc12a])]
                                            rw [gapScore_zero_of_small m.hlam (by linarith only [ht23, ht0, hp1, ht34, hc01b, ht01, ht12, ht45, ht5]) (by linarith only [hp1, hc12a, h015a, h123b, h145b, h134b])]
                                            try norm_num
                                          ·
                                            change linearGapScore m.lam (m.t 2) (m.t 2 + m.p) (m.rowxs 2) = 0
                                            have hpidx : (((List.finRange 6).erase (2 : Fin 6))).Perm
                                                ([1, 0, 4, 5, 3] : List (Fin 6)) := by decide
                                            have hperm := (m.row_perm 2).trans (hpidx.map (m.d 2))
                                            change (m.rowxs 2).Perm [m.d 2 1, m.d 2 0, m.d 2 4, m.d 2 5, m.d 2 3] at hperm
                                            rw [m.symm 2 1 (by decide)] at hperm
                                            rw [m.symm 2 0 (by decide)] at hperm
                                            have heq := hperm.eq_of_pairwise' (m.row_sorted _) (by
                                              simp only [List.pairwise_cons, List.mem_cons,
                                                List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, false_implies, implies_true, and_true, List.Pairwise.nil]
                                              (repeat' constructor) <;> linarith only [h012b, h023a, h023b, h025a, h034a, h234b, h234c, h235a, h235c, h245b, h345b, hc12a, hc23b, hp1, ht0, ht01, ht12, ht23, ht34, ht45, ht5])
                                            rw [heq]
                                            simp only [linearGapScore]
                                            rw [gapScore_zero_of_small m.hlam (by linarith only [ht01, ht23, ht5, ht34, ht0, ht45, hp1, hc12a]) (by linarith only [ht0, ht12, h345b, hc23b, ht34, ht45, ht5, h235a, h012b, ht01, hp1, h023b, h034a])]
                                            rw [gapScore_zero_of_small m.hlam (by linarith only [h012b]) (by linarith only [h235a, hp1, h023b, ht0, h345b, h034a, h012b, hc12a, ht45, ht5, ht34, ht01, hc23b])]
                                            rw [gapScore_zero_of_small m.hlam (by linarith only [ht0, hc12a, h034a, h012b, hp1, h235a, hc23b, h345b, ht45, h234b, h023b, ht01, ht5, ht34]) (by linarith only [hc45b, hp1, ht0, hc12a, h245a, h012b, ht01, ht5])]
                                            rw [gapScore_zero_of_small m.hlam (by linarith only [h245b]) (by linarith only [ht0, ht5, h023b, h012b, h034a, hc12a, hp1, h234b, hc25b, ht01])]
                                            rw [gapScore_zero_of_small m.hlam (by linarith only [h235c]) (by linarith only [ht01, h012b, h023b, h245b, h034a, hc12a, ht0, h234b, hc23b, ht45, hp1, ht5, ht34])]
                                            rw [gapScore_zero_of_small m.hlam (by linarith only [ht45, ht0, hp1, ht12, ht34, hc23b, ht01, ht5]) (by linarith only [h345b, ht0, ht01, h012b, hp1, ht23, hc12a, ht5, h034a, h235a, ht34, ht45, h023b])]
                                            try norm_num
                                          ·
                                            change linearGapScore m.lam (m.t 3) (m.t 3 + m.p) (m.rowxs 3) = 0
                                            have hpidx : (((List.finRange 6).erase (3 : Fin 6))).Perm
                                                ([1, 0, 4, 5, 2] : List (Fin 6)) := by decide
                                            have hperm := (m.row_perm 3).trans (hpidx.map (m.d 3))
                                            change (m.rowxs 3).Perm [m.d 3 1, m.d 3 0, m.d 3 4, m.d 3 5, m.d 3 2] at hperm
                                            rw [m.symm 3 1 (by decide)] at hperm
                                            rw [m.symm 3 0 (by decide)] at hperm
                                            rw [m.symm 3 2 (by decide)] at hperm
                                            have heq := hperm.eq_of_pairwise' (m.row_sorted _) (by
                                              simp only [List.pairwise_cons, List.mem_cons,
                                                List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, false_implies, implies_true, and_true, List.Pairwise.nil]
                                              (repeat' constructor) <;> linarith only [h012b, h013b, h015a, h023b, h023c, h034a, h035a, h123c, h134b, h145b, h234a, h235a, h345b, hc01b, hc12a, hc23b, hp1, ht0, ht01, ht12, ht23, ht34, ht45, ht5])
                                            rw [heq]
                                            simp only [linearGapScore]
                                            rw [gapScore_zero_of_small m.hlam (by linarith only [hp1, ht0, hc12a, ht5, ht45, ht34, ht01, h123b]) (by linarith only [hc01b, hc12a, h145b, h345b, h134b, h034a, h235a, h012b, hc23b, hp1, h015a, h023b])]
                                            rw [gapScore_zero_of_small m.hlam (by linarith only [h013b]) (by linarith only [ht01, h023b, ht5, hc12a, h034a, h012b, h235a, hc23b, h123b, ht34, ht0, hp1, h345b, ht45])]
                                            rw [gapScore_zero_of_small m.hlam (by linarith only [h034a, ht5, ht45, h012b, hp1, ht01, hc23b, h023b, ht0, h235a, h345b, hc12a, ht34]) (by linarith only [ht0, h023b, hc12a, hc23b, ht5, ht45, h235a, hp1, h345b, ht34, ht01, h012b])]
                                            rw [gapScore_zero_of_small m.hlam (by linarith only [h345b]) (by linarith only [ht5, h012b, h345b, h034a, h235a, h023b, ht01, hp1, ht0, ht34, hc23b, hc12a, ht45])]
                                            rw [gapScore_zero_of_small m.hlam (by linarith only [h034a, h235a, h023b, h234a, ht34, h012b, ht01, ht45, hc12a, hp1, ht0, ht5, hc23b]) (by linarith only [hc12a, ht01, hp1, h023b, ht5, ht34, h034a, ht45, ht0, h012b, hc23b, h345b])]
                                            rw [gapScore_zero_of_small m.hlam (by linarith only [ht23, hp1, ht12, ht5, ht34, ht01, ht45, ht0, hc23b]) (by linarith only [hp1, h235a, h034a, ht5, h345b, ht01, h012b, h023b, hc12a, ht45, ht0, ht34])]
                                            try norm_num
                                          ·
                                            change linearGapScore m.lam (m.t 4) (m.t 4 + m.p) (m.rowxs 4) = 0
                                            have hpidx : (((List.finRange 6).erase (4 : Fin 6))).Perm
                                                ([1, 0, 3, 2, 5] : List (Fin 6)) := by decide
                                            have hperm := (m.row_perm 4).trans (hpidx.map (m.d 4))
                                            change (m.rowxs 4).Perm [m.d 4 1, m.d 4 0, m.d 4 3, m.d 4 2, m.d 4 5] at hperm
                                            rw [m.symm 4 1 (by decide)] at hperm
                                            rw [m.symm 4 0 (by decide)] at hperm
                                            rw [m.symm 4 3 (by decide)] at hperm
                                            rw [m.symm 4 2 (by decide)] at hperm
                                            have heq := hperm.eq_of_pairwise' (m.row_sorted _) (by
                                              simp only [List.pairwise_cons, List.mem_cons,
                                                List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, false_implies, implies_true, and_true, List.Pairwise.nil]
                                              (repeat' constructor) <;> linarith only [h012b, h014b, h023b, h024c, h034a, h034c, h045a, h124c, h134c, h234b, h235a, h245a, h345b, hc12a, hc23b, hp1, ht0, ht01, ht12, ht23, ht34, ht45, ht5])
                                            rw [heq]
                                            simp only [linearGapScore]
                                            rw [gapScore_zero_of_small m.hlam (by linarith only [ht45, ht01, h123b, hp1, h134b, ht5, ht0, hc12a]) (by linarith only [h145b, ht34, hp1, h235a, hc12a, h034a, hc23b, h345b, hc01b, h023b, h012b, h015a])]
                                            rw [gapScore_zero_of_small m.hlam (by linarith only [h014b]) (by linarith only [hp1, h123b, hc12a, h014c, hc01b, h134b])]
                                            rw [gapScore_zero_of_small m.hlam (by linarith only [h034c]) (by linarith only [ht0, ht34, ht45, h034b, hc23b, h235a, hc12a, hp1, h345b, h012b, h023b, ht01, ht5])]
                                            rw [gapScore_zero_of_small m.hlam (by linarith only [h234b]) (by linarith only [ht45, h023b, hc24b, ht5, ht0, ht01, hc12a, h012b, hp1, h034a])]
                                            rw [gapScore_zero_of_small m.hlam (by linarith only [ht45, hp1, ht5, hc12a, ht01, h034a, ht0, h345b, h023b, ht34, hc23b, h245a, h235a, h012b]) (by linarith only [hc45b, h023b, ht01, h012b, hp1, h034a, h234b, ht0, hc12a, ht5])]
                                            rw [gapScore_zero_of_small m.hlam (by linarith only [ht5, ht0, hc45b, hp1, ht23, ht01, ht12, ht34]) (by linarith only [hp1, h245a, h034a, h023b, ht01, h012b, h234b, ht45, hc12a, ht5, ht0])]
                                            try norm_num
                                          ·
                                            change linearGapScore m.lam (m.t 5) (m.t 5 + m.p) (m.rowxs 5) = 0
                                            have hpidx : (((List.finRange 6).erase (5 : Fin 6))).Perm
                                                ([1, 0, 3, 2, 4] : List (Fin 6)) := by decide
                                            have hperm := (m.row_perm 5).trans (hpidx.map (m.d 5))
                                            change (m.rowxs 5).Perm [m.d 5 1, m.d 5 0, m.d 5 3, m.d 5 2, m.d 5 4] at hperm
                                            rw [m.symm 5 1 (by decide)] at hperm
                                            rw [m.symm 5 0 (by decide)] at hperm
                                            rw [m.symm 5 3 (by decide)] at hperm
                                            rw [m.symm 5 2 (by decide)] at hperm
                                            rw [m.symm 5 4 (by decide)] at hperm
                                            have heq := hperm.eq_of_pairwise' (m.row_sorted _) (by
                                              simp only [List.pairwise_cons, List.mem_cons,
                                                List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, false_implies, implies_true, and_true, List.Pairwise.nil]
                                              (repeat' constructor) <;> linarith only [h015b, h025c, h035c, h045c, h125c, h135c, h145c, h235b, h245c, h345c])
                                            rw [heq]
                                            simp only [linearGapScore]
                                            rw [gapScore_zero_of_small m.hlam (by linarith only [ht0, hc15a, ht5, ht01, hp1]) (by linarith only [hc12a, h345b, hc23b, ht45, hp1, h023b, h015a, h012b, hc01b, ht34, h235a, h034a])]
                                            rw [gapScore_zero_of_small m.hlam (by linarith only [h015b]) (by linarith only [h015c, h123b, hp1, h134b, hc12a, hc01b, h145b])]
                                            rw [gapScore_zero_of_small m.hlam (by linarith only [h035c]) (by linarith only [ht45, hc23b, hc12a, h012b, ht5, h045b, h034b, ht0, hp1, ht01, h235a, h023b, ht34])]
                                            rw [gapScore_zero_of_small m.hlam (by linarith only [h235b]) (by linarith only [h034a, ht5, hc25b, hp1, hc12a, ht01, ht0, h012b, h023b, h345b])]
                                            rw [gapScore_zero_of_small m.hlam (by linarith only [h245c]) (by linarith only [hc45b, h023b, h245b, hp1, h034a, ht01, h012b, hc12a, ht0, h234b, ht5])]
                                            rw [gapScore_zero_of_small m.hlam (by linarith only [ht12, hp1, ht45, ht5, ht0, ht23, ht01, ht34, hc45b]) (by linarith only [hp1, h234b, ht5, h023b, h012b, ht0, h034a, ht01, hc12a, h245a])]
                                            try norm_num
                                        ·
                                          exfalso; linarith only [h023b, ht0, hp1, h245a, ht01, h034a, h234b, h234a, h345a, hc23b, ht34, ht5, ht45, h012b, hc12a]
                                      ·
                                        rcases m.htr 3 4 5 (by decide) (by decide) with
                                          ⟨h345a, h345b, h345c⟩ | ⟨h345a, h345b, h345c⟩
                                        ·
                                          exfalso; linarith only [ht45, ht0, h023b, h012b, hc23b, h245a, hp1, ht34, ht5, hc12a, ht01, h234c, h345a, h034a]
                                        ·
                                          exfalso; linarith only [h034b, h234a, hc12a, ht0, hc23b, h023b, hp1, ht45, h012b, ht01, ht34, h045a, h345a, ht5]
                                ·
                                  exfalso; linarith only [ht0, h014a, ht34, ht5, ht01, ht12, hp1, hc12a, h034b, hc01b, ht23, h023b, h012b, h145a, ht45, h045a]
                              ·
                                exfalso; linarith only [ht01, ht0, h014a, ht34, hc12a, hp1, ht5, h012b, h035a, h023b, hc01b, h134b, ht12, h135a, ht45, ht23]
                            ·
                              exfalso; linarith only [h012b, ht12, h023b, h034a, ht34, ht0, ht23, ht45, hc01b, ht01, hp1, h013a, h134a, hc12a, ht5]
                          ·
                            exfalso; linarith only [h025a, ht5, ht0, ht45, hp1, ht34, h125a, ht01, ht23, ht12, h012b]
                        ·
                          exfalso; linarith only [ht5, ht34, ht01, h024a, ht23, hp1, h124a, ht0, ht12, h012b, ht45]
                      ·
                        exfalso; linarith only [ht12, hp1, h123a, ht5, ht34, h023a, ht01, ht23, h012b, ht0, ht45]
                    ·
                      rcases m.htr 1 2 3 (by decide) (by decide) with
                        ⟨h123a, h123b, h123c⟩ | ⟨h123a, h123b, h123c⟩
                      ·
                        rcases m.htr 1 2 4 (by decide) (by decide) with
                          ⟨h124a, h124b, h124c⟩ | ⟨h124a, h124b, h124c⟩
                        ·
                          rcases m.htr 1 2 5 (by decide) (by decide) with
                            ⟨h125a, h125b, h125c⟩ | ⟨h125a, h125b, h125c⟩
                          ·
                            rcases m.htr 1 3 4 (by decide) (by decide) with
                              ⟨h134a, h134b, h134c⟩ | ⟨h134a, h134b, h134c⟩
                            ·
                              rcases m.htr 1 3 5 (by decide) (by decide) with
                                ⟨h135a, h135b, h135c⟩ | ⟨h135a, h135b, h135c⟩
                              ·
                                rcases m.htr 1 4 5 (by decide) (by decide) with
                                  ⟨h145a, h145b, h145c⟩ | ⟨h145a, h145b, h145c⟩
                                ·
                                  exfalso; linarith only [h145a, h014c, hp1, h045a, hc12a, h123b, h134b, hc01b]
                                ·
                                  exfalso; linarith only [hp1, h145a, ht23, ht34, hc01b, hc45a, ht12, h014a]
                              ·
                                exfalso; linarith only [hc13b, ht5, h023b, ht0, hp1, h135a, ht34, hc12a, ht45, h012b, ht01, h013a, hc01b, h035a]
                            ·
                              exfalso; linarith only [h134a, hp1, hc13b, h034c, ht34, h045a, hc45a]
                          ·
                            exfalso; linarith only [ht45, ht01, ht0, hp1, ht5, h125a, ht23, h025a, ht34, h012b, ht12]
                        ·
                          exfalso; linarith only [h024c, ht34, h045a, hp1, h012b, hc02b, hc45a, ht23, h124a]
                      ·
                        exfalso; linarith only [ht45, h123a, ht01, h023a, hp1, ht5, h012b, ht23, ht12, ht0, ht34]
                  ·
                    rcases m.htr 0 4 5 (by decide) (by decide) with
                      ⟨h045a, h045b, h045c⟩ | ⟨h045a, h045b, h045c⟩
                    ·
                      exfalso; linarith only [h034b, h035c, h045b]
                    ·
                      rcases m.htr 1 2 3 (by decide) (by decide) with
                        ⟨h123a, h123b, h123c⟩ | ⟨h123a, h123b, h123c⟩
                      ·
                        rcases m.htr 1 2 4 (by decide) (by decide) with
                          ⟨h124a, h124b, h124c⟩ | ⟨h124a, h124b, h124c⟩
                        ·
                          rcases m.htr 1 2 5 (by decide) (by decide) with
                            ⟨h125a, h125b, h125c⟩ | ⟨h125a, h125b, h125c⟩
                          ·
                            rcases m.htr 1 3 4 (by decide) (by decide) with
                              ⟨h134a, h134b, h134c⟩ | ⟨h134a, h134b, h134c⟩
                            ·
                              rcases m.htr 1 3 5 (by decide) (by decide) with
                                ⟨h135a, h135b, h135c⟩ | ⟨h135a, h135b, h135c⟩
                              ·
                                exfalso; linarith only [hp1, h135a, h034b, h014c, hc12a, hc01b, h035a, h123b]
                              ·
                                exfalso; linarith only [hc01b, hp1, hc35a, h135a, h013a, ht12, ht23]
                            ·
                              exfalso; linarith only [ht34, ht5, hc13b, ht0, h134a, h035a, hc35a, ht01, hp1, ht12, h034a, ht45, ht23]
                          ·
                            exfalso; linarith only [ht45, ht34, ht12, hp1, h025a, h012b, ht0, h125a, ht01, ht23, ht5]
                        ·
                          exfalso; linarith only [h012b, h024c, hp1, h034b, ht23, h124a, hc02b, hc35a, h035a]
                      ·
                        exfalso; linarith only [hp1, ht23, h023c, h035a, h012b, hc35a, h123a, hc02b]
                ·
                  rcases m.htr 0 3 5 (by decide) (by decide) with
                    ⟨h035a, h035b, h035c⟩ | ⟨h035a, h035b, h035c⟩
                  ·
                    rcases m.htr 0 4 5 (by decide) (by decide) with
                      ⟨h045a, h045b, h045c⟩ | ⟨h045a, h045b, h045c⟩
                    ·
                      rcases m.htr 1 2 3 (by decide) (by decide) with
                        ⟨h123a, h123b, h123c⟩ | ⟨h123a, h123b, h123c⟩
                      ·
                        rcases m.htr 1 2 4 (by decide) (by decide) with
                          ⟨h124a, h124b, h124c⟩ | ⟨h124a, h124b, h124c⟩
                        ·
                          rcases m.htr 1 2 5 (by decide) (by decide) with
                            ⟨h125a, h125b, h125c⟩ | ⟨h125a, h125b, h125c⟩
                          ·
                            rcases m.htr 1 3 4 (by decide) (by decide) with
                              ⟨h134a, h134b, h134c⟩ | ⟨h134a, h134b, h134c⟩
                            ·
                              exfalso; linarith only [h034a, h035b, hp1, h123b, h015c, h134a, hc01b, hc12a]
                            ·
                              exfalso; linarith only [ht12, hp1, h134a, ht23, hc34a, hc01b, h013a]
                          ·
                            exfalso; linarith only [h034a, hp1, h012b, hc02b, h125a, h035b, h025c, ht23, hc34a]
                        ·
                          exfalso; linarith only [h012b, hp1, ht5, h024a, ht0, h124a, ht01, ht23, ht45, ht12, ht34]
                      ·
                        exfalso; linarith only [ht23, h012b, hp1, h034a, hc34a, h023c, hc02b, h123a]
                    ·
                      exfalso; linarith only [h035b, h045c, h034c]
                  ·
                    rcases m.htr 0 4 5 (by decide) (by decide) with
                      ⟨h045a, h045b, h045c⟩ | ⟨h045a, h045b, h045c⟩
                    ·
                      rcases m.htr 1 2 3 (by decide) (by decide) with
                        ⟨h123a, h123b, h123c⟩ | ⟨h123a, h123b, h123c⟩
                      ·
                        rcases m.htr 1 2 4 (by decide) (by decide) with
                          ⟨h124a, h124b, h124c⟩ | ⟨h124a, h124b, h124c⟩
                        ·
                          rcases m.htr 1 2 5 (by decide) (by decide) with
                            ⟨h125a, h125b, h125c⟩ | ⟨h125a, h125b, h125c⟩
                          ·
                            rcases m.htr 1 3 4 (by decide) (by decide) with
                              ⟨h134a, h134b, h134c⟩ | ⟨h134a, h134b, h134c⟩
                            ·
                              exfalso; linarith only [h013c, hp1, hc01b, h134a, h034a, hc12a, h123b]
                            ·
                              exfalso; linarith only [hc34a, h134a, ht23, h013a, hc01b, ht12, hp1]
                          ·
                            exfalso; linarith only [ht01, ht12, ht45, ht34, ht0, h125a, hp1, h025a, ht5, ht23, h012b]
                        ·
                          exfalso; linarith only [ht23, ht5, ht45, h124a, ht34, ht12, hp1, ht01, h012b, ht0, h024a]
                      ·
                        exfalso; linarith only [h123a, hp1, hc34a, h034a, h023c, h012b, ht23, hc02b]
                    ·
                      rcases m.htr 1 2 3 (by decide) (by decide) with
                        ⟨h123a, h123b, h123c⟩ | ⟨h123a, h123b, h123c⟩
                      ·
                        rcases m.htr 1 2 4 (by decide) (by decide) with
                          ⟨h124a, h124b, h124c⟩ | ⟨h124a, h124b, h124c⟩
                        ·
                          rcases m.htr 1 2 5 (by decide) (by decide) with
                            ⟨h125a, h125b, h125c⟩ | ⟨h125a, h125b, h125c⟩
                          ·
                            rcases m.htr 1 3 4 (by decide) (by decide) with
                              ⟨h134a, h134b, h134c⟩ | ⟨h134a, h134b, h134c⟩
                            ·
                              exfalso; linarith only [hp1, h034a, hc01b, h013c, hc12a, h134a, h123b]
                            ·
                              exfalso; linarith only [ht23, hc01b, hp1, h134a, ht12, hc34a, h013a]
                          ·
                            exfalso; linarith only [ht12, ht01, ht0, ht23, ht34, h012b, ht45, h025a, ht5, h125a, hp1]
                        ·
                          exfalso; linarith only [hp1, h045a, ht34, ht23, h024c, hc45a, h012b, hc02b, h124a]
                      ·
                        exfalso; linarith only [ht23, hp1, h045a, h034c, ht34, h012b, h023c, h123a, hc02b, hc45a]
              ·
                rcases m.htr 0 3 4 (by decide) (by decide) with
                  ⟨h034a, h034b, h034c⟩ | ⟨h034a, h034b, h034c⟩
                ·
                  rcases m.htr 0 3 5 (by decide) (by decide) with
                    ⟨h035a, h035b, h035c⟩ | ⟨h035a, h035b, h035c⟩
                  ·
                    exfalso; linarith only [h023b, h025c, h035b]
                  ·
                    rcases m.htr 0 4 5 (by decide) (by decide) with
                      ⟨h045a, h045b, h045c⟩ | ⟨h045a, h045b, h045c⟩
                    ·
                      exfalso; linarith only [h023b, h034b, h025c, h045b]
                    ·
                      rcases m.htr 1 2 3 (by decide) (by decide) with
                        ⟨h123a, h123b, h123c⟩ | ⟨h123a, h123b, h123c⟩
                      ·
                        rcases m.htr 1 2 4 (by decide) (by decide) with
                          ⟨h124a, h124b, h124c⟩ | ⟨h124a, h124b, h124c⟩
                        ·
                          rcases m.htr 1 2 5 (by decide) (by decide) with
                            ⟨h125a, h125b, h125c⟩ | ⟨h125a, h125b, h125c⟩
                          ·
                            exfalso; linarith only [h025a, h034b, hc12a, h125a, hc01b, h014c, h023b, hp1]
                          ·
                            exfalso; linarith only [hp1, h125a, ht12, hc01b, h012a, hc25a]
                        ·
                          exfalso; linarith only [ht23, hc12b, ht01, ht5, h025a, h124a, h024a, ht34, hc25a, ht12, hp1, ht0, ht45]
                      ·
                        exfalso; linarith only [ht0, ht34, hc12b, ht12, ht45, ht5, h123a, hp1, ht23, h023a, hc25a, ht01, h025a]
                ·
                  rcases m.htr 0 3 5 (by decide) (by decide) with
                    ⟨h035a, h035b, h035c⟩ | ⟨h035a, h035b, h035c⟩
                  ·
                    exfalso; linarith only [h025c, h035b, h034c, h024b]
                  ·
                    rcases m.htr 0 4 5 (by decide) (by decide) with
                      ⟨h045a, h045b, h045c⟩ | ⟨h045a, h045b, h045c⟩
                    ·
                      exfalso; linarith only [h045b, h025c, h024b]
                    ·
                      rcases m.htr 1 2 3 (by decide) (by decide) with
                        ⟨h123a, h123b, h123c⟩ | ⟨h123a, h123b, h123c⟩
                      ·
                        rcases m.htr 1 2 4 (by decide) (by decide) with
                          ⟨h124a, h124b, h124c⟩ | ⟨h124a, h124b, h124c⟩
                        ·
                          rcases m.htr 1 2 5 (by decide) (by decide) with
                            ⟨h125a, h125b, h125c⟩ | ⟨h125a, h125b, h125c⟩
                          ·
                            exfalso; linarith only [h025a, ht45, ht01, h023a, hp1, h125a, ht5, hc12a, ht0, ht34, hc23b]
                          ·
                            exfalso; linarith only [h125a, hp1, hc25a, h012a, hc01b, ht12]
                        ·
                          exfalso; linarith only [hc25a, h024a, ht01, ht0, ht34, hc12b, h124a, ht5, ht23, ht45, hp1, ht12, h025a]
                      ·
                        exfalso; linarith only [ht34, ht01, hc12b, hc25a, hp1, ht12, h023a, ht5, ht45, h025a, h123a, ht23, ht0]
            ·
              rcases m.htr 0 2 5 (by decide) (by decide) with
                ⟨h025a, h025b, h025c⟩ | ⟨h025a, h025b, h025c⟩
              ·
                rcases m.htr 0 3 4 (by decide) (by decide) with
                  ⟨h034a, h034b, h034c⟩ | ⟨h034a, h034b, h034c⟩
                ·
                  exfalso; linarith only [h023b, h024c, h034b]
                ·
                  rcases m.htr 0 3 5 (by decide) (by decide) with
                    ⟨h035a, h035b, h035c⟩ | ⟨h035a, h035b, h035c⟩
                  ·
                    rcases m.htr 0 4 5 (by decide) (by decide) with
                      ⟨h045a, h045b, h045c⟩ | ⟨h045a, h045b, h045c⟩
                    ·
                      rcases m.htr 1 2 3 (by decide) (by decide) with
                        ⟨h123a, h123b, h123c⟩ | ⟨h123a, h123b, h123c⟩
                      ·
                        rcases m.htr 1 2 4 (by decide) (by decide) with
                          ⟨h124a, h124b, h124c⟩ | ⟨h124a, h124b, h124c⟩
                        ·
                          exfalso; linarith only [hc01b, h024a, hc12a, h015c, h023b, hp1, h035b, h124a]
                        ·
                          exfalso; linarith only [hc24a, hp1, hc01b, ht12, h124a, h012a]
                      ·
                        exfalso; linarith only [ht34, ht0, h024a, ht23, ht12, hp1, ht5, ht45, hc24a, h123a, h023a, ht01, hc12b]
                    ·
                      exfalso; linarith only [h045a, hc23b, h024c, h023a, hc45a, ht34, hp1]
                  ·
                    rcases m.htr 0 4 5 (by decide) (by decide) with
                      ⟨h045a, h045b, h045c⟩ | ⟨h045a, h045b, h045c⟩
                    ·
                      rcases m.htr 1 2 3 (by decide) (by decide) with
                        ⟨h123a, h123b, h123c⟩ | ⟨h123a, h123b, h123c⟩
                      ·
                        rcases m.htr 1 2 4 (by decide) (by decide) with
                          ⟨h124a, h124b, h124c⟩ | ⟨h124a, h124b, h124c⟩
                        ·
                          exfalso; linarith only [h024a, h013c, hp1, h124a, hc12a, h025b, h035c, hc01b]
                        ·
                          exfalso; linarith only [hp1, h124a, ht12, h012a, hc24a, hc01b]
                      ·
                        exfalso; linarith only [ht5, hp1, ht01, ht45, ht12, ht23, ht0, ht34, hc12b, h123a, h024a, hc24a, h023a]
                    ·
                      exfalso; linarith only [h024c, hp1, h023a, h045a, hc23b, hc45a, ht34]
              ·
                rcases m.htr 0 3 4 (by decide) (by decide) with
                  ⟨h034a, h034b, h034c⟩ | ⟨h034a, h034b, h034c⟩
                ·
                  exfalso; linarith only [h024c, h034b, h023b]
                ·
                  rcases m.htr 0 3 5 (by decide) (by decide) with
                    ⟨h035a, h035b, h035c⟩ | ⟨h035a, h035b, h035c⟩
                  ·
                    exfalso; linarith only [h023b, h035b, h025c]
                  ·
                    rcases m.htr 0 4 5 (by decide) (by decide) with
                      ⟨h045a, h045b, h045c⟩ | ⟨h045a, h045b, h045c⟩
                    ·
                      rcases m.htr 1 2 3 (by decide) (by decide) with
                        ⟨h123a, h123b, h123c⟩ | ⟨h123a, h123b, h123c⟩
                      ·
                        rcases m.htr 1 2 4 (by decide) (by decide) with
                          ⟨h124a, h124b, h124c⟩ | ⟨h124a, h124b, h124c⟩
                        ·
                          exfalso; linarith only [hc01b, h013c, hp1, h023b, h024a, hc12a, h124a]
                        ·
                          exfalso; linarith only [ht12, h012a, hc01b, hc24a, hp1, h124a]
                      ·
                        exfalso; linarith only [hp1, ht45, ht01, ht0, hc12b, h023a, h024a, ht12, h123a, ht23, ht5, ht34, hc24a]
                    ·
                      exfalso; linarith only [h024c, h023a, hc45a, h045a, ht34, hp1, hc23b]
          ·
            rcases m.htr 0 2 4 (by decide) (by decide) with
              ⟨h024a, h024b, h024c⟩ | ⟨h024a, h024b, h024c⟩
            ·
              rcases m.htr 0 2 5 (by decide) (by decide) with
                ⟨h025a, h025b, h025c⟩ | ⟨h025a, h025b, h025c⟩
              ·
                rcases m.htr 0 3 4 (by decide) (by decide) with
                  ⟨h034a, h034b, h034c⟩ | ⟨h034a, h034b, h034c⟩
                ·
                  rcases m.htr 0 3 5 (by decide) (by decide) with
                    ⟨h035a, h035b, h035c⟩ | ⟨h035a, h035b, h035c⟩
                  ·
                    rcases m.htr 0 4 5 (by decide) (by decide) with
                      ⟨h045a, h045b, h045c⟩ | ⟨h045a, h045b, h045c⟩
                    ·
                      rcases m.htr 1 2 3 (by decide) (by decide) with
                        ⟨h123a, h123b, h123c⟩ | ⟨h123a, h123b, h123c⟩
                      ·
                        exfalso; linarith only [h024b, h123a, h023a, h015c, hc01b, hc12a, h045b, hp1]
                      ·
                        exfalso; linarith only [hp1, hc23a, hc01b, ht12, h123a, h012a]
                    ·
                      rcases m.htr 1 2 3 (by decide) (by decide) with
                        ⟨h123a, h123b, h123c⟩ | ⟨h123a, h123b, h123c⟩
                      ·
                        exfalso; linarith only [h024a, ht0, hp1, ht5, h023a, ht45, ht01, hc24b, hc12a, h123a]
                      ·
                        exfalso; linarith only [hc01b, hp1, hc23a, h123a, h012a, ht12]
                  ·
                    exfalso; linarith only [h025b, h023c, h035c]
                ·
                  exfalso; linarith only [h023c, h034c, h024b]
              ·
                rcases m.htr 0 3 4 (by decide) (by decide) with
                  ⟨h034a, h034b, h034c⟩ | ⟨h034a, h034b, h034c⟩
                ·
                  rcases m.htr 0 3 5 (by decide) (by decide) with
                    ⟨h035a, h035b, h035c⟩ | ⟨h035a, h035b, h035c⟩
                  ·
                    rcases m.htr 0 4 5 (by decide) (by decide) with
                      ⟨h045a, h045b, h045c⟩ | ⟨h045a, h045b, h045c⟩
                    ·
                      exfalso; linarith only [h025c, h024b, h045b]
                    ·
                      rcases m.htr 1 2 3 (by decide) (by decide) with
                        ⟨h123a, h123b, h123c⟩ | ⟨h123a, h123b, h123c⟩
                      ·
                        exfalso; linarith only [h123a, ht45, hp1, ht0, hc24b, ht01, hc12a, h024a, ht5, h023a]
                      ·
                        exfalso; linarith only [hp1, hc23a, ht12, hc01b, h012a, h123a]
                  ·
                    rcases m.htr 0 4 5 (by decide) (by decide) with
                      ⟨h045a, h045b, h045c⟩ | ⟨h045a, h045b, h045c⟩
                    ·
                      exfalso; linarith only [h025c, h024b, h045b]
                    ·
                      rcases m.htr 1 2 3 (by decide) (by decide) with
                        ⟨h123a, h123b, h123c⟩ | ⟨h123a, h123b, h123c⟩
                      ·
                        exfalso; linarith only [hc12a, ht01, hc24b, ht45, h123a, ht5, hp1, h024a, h023a, ht0]
                      ·
                        exfalso; linarith only [hp1, h123a, hc01b, ht12, hc23a, h012a]
                ·
                  exfalso; linarith only [h023c, h024b, h034c]
            ·
              rcases m.htr 0 2 5 (by decide) (by decide) with
                ⟨h025a, h025b, h025c⟩ | ⟨h025a, h025b, h025c⟩
              ·
                rcases m.htr 0 3 4 (by decide) (by decide) with
                  ⟨h034a, h034b, h034c⟩ | ⟨h034a, h034b, h034c⟩
                ·
                  rcases m.htr 0 3 5 (by decide) (by decide) with
                    ⟨h035a, h035b, h035c⟩ | ⟨h035a, h035b, h035c⟩
                  ·
                    rcases m.htr 0 4 5 (by decide) (by decide) with
                      ⟨h045a, h045b, h045c⟩ | ⟨h045a, h045b, h045c⟩
                    ·
                      rcases m.htr 1 2 3 (by decide) (by decide) with
                        ⟨h123a, h123b, h123c⟩ | ⟨h123a, h123b, h123c⟩
                      ·
                        exfalso; linarith only [h025b, h015c, hc01b, hc12a, h023a, h123a, hp1]
                      ·
                        exfalso; linarith only [h123a, hc23a, h012a, hc01b, hp1, ht12]
                    ·
                      exfalso; linarith only [h045c, h025b, h024c]
                  ·
                    exfalso; linarith only [h024c, h035c, h034b, h025b]
                ·
                  rcases m.htr 0 3 5 (by decide) (by decide) with
                    ⟨h035a, h035b, h035c⟩ | ⟨h035a, h035b, h035c⟩
                  ·
                    rcases m.htr 0 4 5 (by decide) (by decide) with
                      ⟨h045a, h045b, h045c⟩ | ⟨h045a, h045b, h045c⟩
                    ·
                      rcases m.htr 1 2 3 (by decide) (by decide) with
                        ⟨h123a, h123b, h123c⟩ | ⟨h123a, h123b, h123c⟩
                      ·
                        exfalso; linarith only [h123a, h015c, h023a, hc12a, h025b, hp1, hc01b]
                      ·
                        exfalso; linarith only [h123a, h012a, ht12, hc01b, hc23a, hp1]
                    ·
                      exfalso; linarith only [h034c, h023c, h045c, h025b]
                  ·
                    exfalso; linarith only [h035c, h025b, h023c]
              ·
                rcases m.htr 0 3 4 (by decide) (by decide) with
                  ⟨h034a, h034b, h034c⟩ | ⟨h034a, h034b, h034c⟩
                ·
                  rcases m.htr 0 3 5 (by decide) (by decide) with
                    ⟨h035a, h035b, h035c⟩ | ⟨h035a, h035b, h035c⟩
                  ·
                    rcases m.htr 0 4 5 (by decide) (by decide) with
                      ⟨h045a, h045b, h045c⟩ | ⟨h045a, h045b, h045c⟩
                    ·
                      rcases m.htr 1 2 3 (by decide) (by decide) with
                        ⟨h123a, h123b, h123c⟩ | ⟨h123a, h123b, h123c⟩
                      ·
                        exfalso; linarith only [hc12a, h023a, h012c, hc01b, h123a, hp1]
                      ·
                        exfalso; linarith only [hc01b, h012a, hp1, hc23a, ht12, h123a]
                    ·
                      rcases m.htr 1 2 3 (by decide) (by decide) with
                        ⟨h123a, h123b, h123c⟩ | ⟨h123a, h123b, h123c⟩
                      ·
                        exfalso; linarith only [h012c, h023a, hp1, hc01b, h123a, hc12a]
                      ·
                        exfalso; linarith only [hc23a, hc01b, hp1, h012a, h123a, ht12]
                  ·
                    rcases m.htr 0 4 5 (by decide) (by decide) with
                      ⟨h045a, h045b, h045c⟩ | ⟨h045a, h045b, h045c⟩
                    ·
                      exfalso; linarith only [h034b, h045b, h035c]
                    ·
                      rcases m.htr 1 2 3 (by decide) (by decide) with
                        ⟨h123a, h123b, h123c⟩ | ⟨h123a, h123b, h123c⟩
                      ·
                        exfalso; linarith only [h012c, hc01b, h023a, h123a, hp1, hc12a]
                      ·
                        exfalso; linarith only [h123a, ht12, hc01b, h012a, hp1, hc23a]
                ·
                  rcases m.htr 0 3 5 (by decide) (by decide) with
                    ⟨h035a, h035b, h035c⟩ | ⟨h035a, h035b, h035c⟩
                  ·
                    rcases m.htr 0 4 5 (by decide) (by decide) with
                      ⟨h045a, h045b, h045c⟩ | ⟨h045a, h045b, h045c⟩
                    ·
                      rcases m.htr 1 2 3 (by decide) (by decide) with
                        ⟨h123a, h123b, h123c⟩ | ⟨h123a, h123b, h123c⟩
                      ·
                        exfalso; linarith only [h123a, h023a, hp1, h012c, hc01b, hc12a]
                      ·
                        exfalso; linarith only [h012a, h123a, hp1, ht12, hc23a, hc01b]
                    ·
                      exfalso; linarith only [h045c, h035b, h034c]
                  ·
                    rcases m.htr 0 4 5 (by decide) (by decide) with
                      ⟨h045a, h045b, h045c⟩ | ⟨h045a, h045b, h045c⟩
                    ·
                      rcases m.htr 1 2 3 (by decide) (by decide) with
                        ⟨h123a, h123b, h123c⟩ | ⟨h123a, h123b, h123c⟩
                      ·
                        exfalso; linarith only [hc12a, h023a, hp1, hc01b, h123a, h012c]
                      ·
                        exfalso; linarith only [ht12, hc23a, hc01b, h123a, h012a, hp1]
                    ·
                      rcases m.htr 1 2 3 (by decide) (by decide) with
                        ⟨h123a, h123b, h123c⟩ | ⟨h123a, h123b, h123c⟩
                      ·
                        exfalso; linarith only [hp1, h123a, hc12a, h023a, h012c, hc01b]
                      ·
                        exfalso; linarith only [hp1, ht12, h123a, h012a, hc23a, hc01b]

#print axioms six_model_rows_zero
end Jsp404.N3R01Terminal
