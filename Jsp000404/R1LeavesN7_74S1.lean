import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_74S0

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_10_12_13_25_L_0_L_I_L_R_H_I_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_0 m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc05 := m.hcor 0 5 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h3ehi := hb3.1
  have h5bigk := hb5.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 2 5 (by decide) (by decide) with h332 | h332
  · rcases m.htr 0 3 4 (by decide) (by decide) with h333 | h333
    · rcases m.htr 0 3 5 (by decide) (by decide) with h334 | h334
      · rcases m.htr 0 4 5 (by decide) (by decide) with h335 | h335
        · rcases m.htr 1 3 5 (by decide) (by decide) with h336 | h336
          · rcases m.htr 2 3 4 (by decide) (by decide) with h337 | h337
            · rcases m.htr 2 3 5 (by decide) (by decide) with h338 | h338
              · rcases m.htr 2 4 5 (by decide) (by decide) with h339 | h339
                · rcases m.htr 3 4 5 (by decide) (by decide) with h340 | h340
                  · rcases h5bigk with h341c | h341c | h341c | h341c | h341c | h341c | h341c | h341c | h341c | h341c | h341c | h341c | h341c | h341c | h341c | h341c | h341c | h341c | h341c | h341c | h341c | h341c | h341c | h341c | h341c
                    · have p341_0 := h341c.1
                      have p341_1 := h341c.2.1
                      have p341_2 := h341c.2.2.1
                      have p341_3 := h341c.2.2.2
                      linarith only [hlam, p341_0]
                    · have p341_0 := h341c.1
                      have p341_1 := h341c.2.1
                      have p341_2 := h341c.2.2.1
                      have p341_3 := h341c.2.2.2
                      linarith only [h0, hlam, p341_1]
                    · have p341_0 := h341c.1
                      have p341_1 := h341c.2.1
                      have p341_2 := h341c.2.2.1
                      have p341_3 := h341c.2.2.2
                      linarith only [h335, hc25, hlam, hphi, ht0b, ht5b, p341_1, u0elo3]
                    · have p341_0 := h341c.1
                      have p341_1 := h341c.2.1
                      have p341_2 := h341c.2.2.1
                      have p341_3 := h341c.2.2.2
                      linarith only [h333, h335, hlam, hphi, ht0b, ht34, ht45, ht5b, p341_1, u0elo2, u3ehi4]
                    · have p341_0 := h341c.1
                      have p341_1 := h341c.2.1
                      have p341_2 := h341c.2.2.1
                      have p341_3 := h341c.2.2.2
                      linarith only [h333, h335, hc45, hlam, hphi, ht0b, ht5b, p341_1, u0elo2]
                    · have p341_0 := h341c.1
                      have p341_1 := h341c.2.1
                      have p341_2 := h341c.2.2.1
                      have p341_3 := h341c.2.2.2
                      linarith only [h0, h336, hc01, hc13, hlam, hphi, p341_1]
                    · have p341_0 := h341c.1
                      have p341_1 := h341c.2.1
                      have p341_2 := h341c.2.2.1
                      have p341_3 := h341c.2.2.2
                      linarith only [hlam, p341_0]
                    · have p341_0 := h341c.1
                      have p341_1 := h341c.2.1
                      have p341_2 := h341c.2.2.1
                      have p341_3 := h341c.2.2.2
                      linarith only [h336, h338, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p341_1, u3ehi4]
                    · have p341_0 := h341c.1
                      have p341_1 := h341c.2.1
                      have p341_2 := h341c.2.2.1
                      have p341_3 := h341c.2.2.2
                      linarith only [h336, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p341_1, u3ehi4]
                    · have p341_0 := h341c.1
                      have p341_1 := h341c.2.1
                      have p341_2 := h341c.2.2.1
                      have p341_3 := h341c.2.2.2
                      rcases p341_3 (m.d 0 5) (by simp) with h351 | h351
                      · linarith only [h0, h351, hlam]
                      · linarith only [h335, h351, hlam]
                    · have p341_0 := h341c.1
                      have p341_1 := h341c.2.1
                      have p341_2 := h341c.2.2.1
                      have p341_3 := h341c.2.2.2
                      linarith only [h332, hlam, p341_1]
                    · have p341_0 := h341c.1
                      have p341_1 := h341c.2.1
                      have p341_2 := h341c.2.2.1
                      have p341_3 := h341c.2.2.2
                      linarith only [h332, hc15, hlam, hphi, ht0b, ht5b, p341_1, u0elo4]
                    · have p341_0 := h341c.1
                      have p341_1 := h341c.2.1
                      have p341_2 := h341c.2.2.1
                      have p341_3 := h341c.2.2.2
                      linarith only [hlam, p341_0]
                    · have p341_0 := h341c.1
                      have p341_1 := h341c.2.1
                      have p341_2 := h341c.2.2.1
                      have p341_3 := h341c.2.2.2
                      linarith only [hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p341_1, u3ehi4]
                    · have p341_0 := h341c.1
                      have p341_1 := h341c.2.1
                      have p341_2 := h341c.2.2.1
                      have p341_3 := h341c.2.2.2
                      linarith only [h332, hc45, hlam, hphi, ht0b, ht5b, p341_1, u0elo4]
                    · have p341_0 := h341c.1
                      have p341_1 := h341c.2.1
                      have p341_2 := h341c.2.2.1
                      have p341_3 := h341c.2.2.2
                      linarith only [h334, hlam, p341_0]
                    · have p341_0 := h341c.1
                      have p341_1 := h341c.2.1
                      have p341_2 := h341c.2.2.1
                      have p341_3 := h341c.2.2.2
                      linarith only [h336, hlam, p341_0]
                    · have p341_0 := h341c.1
                      have p341_1 := h341c.2.1
                      have p341_2 := h341c.2.2.1
                      have p341_3 := h341c.2.2.2
                      linarith only [h338, hlam, p341_0]
                    · have p341_0 := h341c.1
                      have p341_1 := h341c.2.1
                      have p341_2 := h341c.2.2.1
                      have p341_3 := h341c.2.2.2
                      linarith only [hlam, p341_0]
                    · have p341_0 := h341c.1
                      have p341_1 := h341c.2.1
                      have p341_2 := h341c.2.2.1
                      have p341_3 := h341c.2.2.2
                      linarith only [h334, hc45, hlam, hphi, ht0b, ht5b, p341_1, u0elo2]
                    · have p341_0 := h341c.1
                      have p341_1 := h341c.2.1
                      have p341_2 := h341c.2.2.1
                      have p341_3 := h341c.2.2.2
                      linarith only [h335, hlam, p341_0]
                    · have p341_0 := h341c.1
                      have p341_1 := h341c.2.1
                      have p341_2 := h341c.2.2.1
                      have p341_3 := h341c.2.2.2
                      linarith only [h0, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p341_1]
                    · have p341_0 := h341c.1
                      have p341_1 := h341c.2.1
                      have p341_2 := h341c.2.2.1
                      have p341_3 := h341c.2.2.2
                      linarith only [h339, hlam, p341_0]
                    · have p341_0 := h341c.1
                      have p341_1 := h341c.2.1
                      have p341_2 := h341c.2.2.1
                      have p341_3 := h341c.2.2.2
                      linarith only [h340, hlam, p341_0]
                    · have p341_0 := h341c.1
                      have p341_1 := h341c.2.1
                      have p341_2 := h341c.2.2.1
                      have p341_3 := h341c.2.2.2
                      linarith only [hlam, p341_0]
                  · linarith only [h333, h335, h340, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi3]
                · linarith only [h333, h335, h337, h339, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi3]
              · linarith only [h337, h338, hc35, hlam, hphi, u3ehi3]
            · linarith only [h333, h337, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi2]
          · linarith only [h334, h336, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi1]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h374 | h374
          · rcases m.htr 2 3 4 (by decide) (by decide) with h375 | h375
            · rcases m.htr 2 3 5 (by decide) (by decide) with h376 | h376
              · rcases m.htr 2 4 5 (by decide) (by decide) with h377 | h377
                · linarith only [h332, h333, h335, h377, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi3]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h379 | h379
                  · linarith only [h333, h335, h379, hlam]
                  · rcases h5bigk with h381c | h381c | h381c | h381c | h381c | h381c | h381c | h381c | h381c | h381c | h381c | h381c | h381c | h381c | h381c | h381c | h381c | h381c | h381c | h381c | h381c | h381c | h381c | h381c | h381c
                    · have p381_0 := h381c.1
                      have p381_1 := h381c.2.1
                      have p381_2 := h381c.2.2.1
                      have p381_3 := h381c.2.2.2
                      linarith only [hlam, p381_0]
                    · have p381_0 := h381c.1
                      have p381_1 := h381c.2.1
                      have p381_2 := h381c.2.2.1
                      have p381_3 := h381c.2.2.2
                      linarith only [h0, hlam, p381_1]
                    · have p381_0 := h381c.1
                      have p381_1 := h381c.2.1
                      have p381_2 := h381c.2.2.1
                      have p381_3 := h381c.2.2.2
                      linarith only [hc25, hlam, hphi, ht0b, ht5b, p381_1, u0elo4]
                    · have p381_0 := h381c.1
                      have p381_1 := h381c.2.1
                      have p381_2 := h381c.2.2.1
                      have p381_3 := h381c.2.2.2
                      linarith only [h332, hlam, hphi, ht0b, ht34, ht45, ht5b, p381_1, u0elo1, u3ehi4]
                    · have p381_0 := h381c.1
                      have p381_1 := h381c.2.1
                      have p381_2 := h381c.2.2.1
                      have p381_3 := h381c.2.2.2
                      linarith only [h335, hlam, p381_1]
                    · have p381_0 := h381c.1
                      have p381_1 := h381c.2.1
                      have p381_2 := h381c.2.2.1
                      have p381_3 := h381c.2.2.2
                      linarith only [h0, hc01, hc15, hlam, hphi, p381_1]
                    · have p381_0 := h381c.1
                      have p381_1 := h381c.2.1
                      have p381_2 := h381c.2.2.1
                      have p381_3 := h381c.2.2.2
                      linarith only [hlam, p381_0]
                    · have p381_0 := h381c.1
                      have p381_1 := h381c.2.1
                      have p381_2 := h381c.2.2.1
                      have p381_3 := h381c.2.2.2
                      linarith only [h374, h375, h377, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p381_1, u3ehi3]
                    · have p381_0 := h381c.1
                      have p381_1 := h381c.2.1
                      have p381_2 := h381c.2.2.1
                      have p381_3 := h381c.2.2.2
                      linarith only [h374, h379, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p381_1, u3ehi3]
                    · have p381_0 := h381c.1
                      have p381_1 := h381c.2.1
                      have p381_2 := h381c.2.2.1
                      have p381_3 := h381c.2.2.2
                      linarith only [h333, h335, h374, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p381_1, u3ehi3]
                    · have p381_0 := h381c.1
                      have p381_1 := h381c.2.1
                      have p381_2 := h381c.2.2.1
                      have p381_3 := h381c.2.2.2
                      linarith only [h332, hlam, p381_1]
                    · have p381_0 := h381c.1
                      have p381_1 := h381c.2.1
                      have p381_2 := h381c.2.2.1
                      have p381_3 := h381c.2.2.2
                      linarith only [h332, hc15, hlam, hphi, ht0b, ht5b, p381_1, u0elo4]
                    · have p381_0 := h381c.1
                      have p381_1 := h381c.2.1
                      have p381_2 := h381c.2.2.1
                      have p381_3 := h381c.2.2.2
                      linarith only [hlam, p381_0]
                    · have p381_0 := h381c.1
                      have p381_1 := h381c.2.1
                      have p381_2 := h381c.2.2.1
                      have p381_3 := h381c.2.2.2
                      linarith only [h332, h379, hlam, hphi, ht0b, ht34, ht45, ht5b, p381_1, u0elo1, u3ehi3]
                    · have p381_0 := h381c.1
                      have p381_1 := h381c.2.1
                      have p381_2 := h381c.2.2.1
                      have p381_3 := h381c.2.2.2
                      linarith only [h377, hlam, p381_1]
                    · have p381_0 := h381c.1
                      have p381_1 := h381c.2.1
                      have p381_2 := h381c.2.2.1
                      have p381_3 := h381c.2.2.2
                      linarith only [h334, hlam, p381_0]
                    · have p381_0 := h381c.1
                      have p381_1 := h381c.2.1
                      have p381_2 := h381c.2.2.1
                      have p381_3 := h381c.2.2.2
                      linarith only [h374, hlam, p381_0]
                    · have p381_0 := h381c.1
                      have p381_1 := h381c.2.1
                      have p381_2 := h381c.2.2.1
                      have p381_3 := h381c.2.2.2
                      linarith only [h376, hlam, p381_0]
                    · have p381_0 := h381c.1
                      have p381_1 := h381c.2.1
                      have p381_2 := h381c.2.2.1
                      have p381_3 := h381c.2.2.2
                      linarith only [hlam, p381_0]
                    · have p381_0 := h381c.1
                      have p381_1 := h381c.2.1
                      have p381_2 := h381c.2.2.1
                      have p381_3 := h381c.2.2.2
                      linarith only [h379, hlam, p381_1]
                    · have p381_0 := h381c.1
                      have p381_1 := h381c.2.1
                      have p381_2 := h381c.2.2.1
                      have p381_3 := h381c.2.2.2
                      linarith only [h0, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p381_1]
                    · have p381_0 := h381c.1
                      have p381_1 := h381c.2.1
                      have p381_2 := h381c.2.2.1
                      have p381_3 := h381c.2.2.2
                      linarith only [h0, h332, h376, h379, hc45, hlam, hphi, ht34, p381_1, u3ehi3]
                    · have p381_0 := h381c.1
                      have p381_1 := h381c.2.1
                      have p381_2 := h381c.2.2.1
                      have p381_3 := h381c.2.2.2
                      linarith only [h376, h379, hc45, hlam, hphi, ht34, p381_1, u3ehi3]
                    · have p381_0 := h381c.1
                      have p381_1 := h381c.2.1
                      have p381_2 := h381c.2.2.1
                      have p381_3 := h381c.2.2.2
                      linarith only [h379, hc45, hlam, hphi, ht34, p381_1, u3ehi3]
                    · have p381_0 := h381c.1
                      have p381_1 := h381c.2.1
                      have p381_2 := h381c.2.2.1
                      have p381_3 := h381c.2.2.2
                      linarith only [hlam, p381_0]
              · linarith only [h334, h376, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi2]
            · linarith only [h333, h375, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi2]
          · linarith only [h334, h374, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi1]
      · linarith only [h333, h334, hc35, hlam, hphi, u3ehi3]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h411 | h411
      · linarith only [h333, h411, hc34, hlam, hphi, u3ehi4]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h413 | h413
        · rcases m.htr 1 3 5 (by decide) (by decide) with h414 | h414
          · rcases m.htr 2 3 4 (by decide) (by decide) with h415 | h415
            · rcases m.htr 2 3 5 (by decide) (by decide) with h416 | h416
              · linarith only [h332, h411, h416, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi0]
              · linarith only [h415, h416, hc35, hlam, hphi, u3ehi3]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h419 | h419
              · linarith only [h411, h415, h419, hc34, hlam, hphi, u3ehi0]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h421 | h421
                · rcases m.htr 3 4 5 (by decide) (by decide) with h422 | h422
                  · rcases h5bigk with h423c | h423c | h423c | h423c | h423c | h423c | h423c | h423c | h423c | h423c | h423c | h423c | h423c | h423c | h423c | h423c | h423c | h423c | h423c | h423c | h423c | h423c | h423c | h423c | h423c
                    · have p423_0 := h423c.1
                      have p423_1 := h423c.2.1
                      have p423_2 := h423c.2.2.1
                      have p423_3 := h423c.2.2.2
                      linarith only [hlam, p423_0]
                    · have p423_0 := h423c.1
                      have p423_1 := h423c.2.1
                      have p423_2 := h423c.2.2.1
                      have p423_3 := h423c.2.2.2
                      linarith only [h0, hlam, p423_1]
                    · have p423_0 := h423c.1
                      have p423_1 := h423c.2.1
                      have p423_2 := h423c.2.2.1
                      have p423_3 := h423c.2.2.2
                      linarith only [h413, h419, hlam, hphi, ht0b, ht34, ht45, ht5b, p423_1, u0elo3, u3ehi2]
                    · have p423_0 := h423c.1
                      have p423_1 := h423c.2.1
                      have p423_2 := h423c.2.2.1
                      have p423_3 := h423c.2.2.2
                      linarith only [h411, hlam, p423_1]
                    · have p423_0 := h423c.1
                      have p423_1 := h423c.2.1
                      have p423_2 := h423c.2.2.1
                      have p423_3 := h423c.2.2.2
                      linarith only [hc45, hlam, hphi, ht0b, ht5b, p423_1, u0elo4]
                    · have p423_0 := h423c.1
                      have p423_1 := h423c.2.1
                      have p423_2 := h423c.2.2.1
                      have p423_3 := h423c.2.2.2
                      linarith only [h0, h414, hc01, hc13, hlam, hphi, p423_1]
                    · have p423_0 := h423c.1
                      have p423_1 := h423c.2.1
                      have p423_2 := h423c.2.2.1
                      have p423_3 := h423c.2.2.2
                      linarith only [hlam, p423_0]
                    · have p423_0 := h423c.1
                      have p423_1 := h423c.2.1
                      have p423_2 := h423c.2.2.1
                      have p423_3 := h423c.2.2.2
                      linarith only [h414, h419, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p423_1, u3ehi2]
                    · have p423_0 := h423c.1
                      have p423_1 := h423c.2.1
                      have p423_2 := h423c.2.2.1
                      have p423_3 := h423c.2.2.2
                      linarith only [h411, h414, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p423_1, u3ehi0]
                    · have p423_0 := h423c.1
                      have p423_1 := h423c.2.1
                      have p423_2 := h423c.2.2.1
                      have p423_3 := h423c.2.2.2
                      rcases p423_3 (m.d 0 5) (by simp) with h433 | h433
                      · linarith only [h0, h433, hlam]
                      · linarith only [h413, h433, hlam]
                    · have p423_0 := h423c.1
                      have p423_1 := h423c.2.1
                      have p423_2 := h423c.2.2.1
                      have p423_3 := h423c.2.2.2
                      linarith only [h332, hlam, p423_1]
                    · have p423_0 := h423c.1
                      have p423_1 := h423c.2.1
                      have p423_2 := h423c.2.2.1
                      have p423_3 := h423c.2.2.2
                      linarith only [h332, hc15, hlam, hphi, ht0b, ht5b, p423_1, u0elo4]
                    · have p423_0 := h423c.1
                      have p423_1 := h423c.2.1
                      have p423_2 := h423c.2.2.1
                      have p423_3 := h423c.2.2.2
                      linarith only [hlam, p423_0]
                    · have p423_0 := h423c.1
                      have p423_1 := h423c.2.1
                      have p423_2 := h423c.2.2.1
                      have p423_3 := h423c.2.2.2
                      linarith only [h419, hlam, p423_1]
                    · have p423_0 := h423c.1
                      have p423_1 := h423c.2.1
                      have p423_2 := h423c.2.2.1
                      have p423_3 := h423c.2.2.2
                      linarith only [h332, hc45, hlam, hphi, ht0b, ht5b, p423_1, u0elo1]
                    · have p423_0 := h423c.1
                      have p423_1 := h423c.2.1
                      have p423_2 := h423c.2.2.1
                      have p423_3 := h423c.2.2.2
                      linarith only [h414, hc05, hc13, hlam, hphi, ht01, ht0b, ht5b, p423_1]
                    · have p423_0 := h423c.1
                      have p423_1 := h423c.2.1
                      have p423_2 := h423c.2.2.1
                      have p423_3 := h423c.2.2.2
                      linarith only [h414, hlam, p423_0]
                    · have p423_0 := h423c.1
                      have p423_1 := h423c.2.1
                      have p423_2 := h423c.2.2.1
                      have p423_3 := h423c.2.2.2
                      linarith only [h414, hc13, hc25, hlam, hphi, ht01, ht0b, ht5b, p423_1]
                    · have p423_0 := h423c.1
                      have p423_1 := h423c.2.1
                      have p423_2 := h423c.2.2.1
                      have p423_3 := h423c.2.2.2
                      linarith only [hlam, p423_0]
                    · have p423_0 := h423c.1
                      have p423_1 := h423c.2.1
                      have p423_2 := h423c.2.2.1
                      have p423_3 := h423c.2.2.2
                      linarith only [h414, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p423_1]
                    · have p423_0 := h423c.1
                      have p423_1 := h423c.2.1
                      have p423_2 := h423c.2.2.1
                      have p423_3 := h423c.2.2.2
                      linarith only [h413, hlam, p423_0]
                    · have p423_0 := h423c.1
                      have p423_1 := h423c.2.1
                      have p423_2 := h423c.2.2.1
                      have p423_3 := h423c.2.2.2
                      linarith only [h414, hc45, hlam, hphi, ht34, p423_1, u3ehi4]
                    · have p423_0 := h423c.1
                      have p423_1 := h423c.2.1
                      have p423_2 := h423c.2.2.1
                      have p423_3 := h423c.2.2.2
                      linarith only [h421, hlam, p423_0]
                    · have p423_0 := h423c.1
                      have p423_1 := h423c.2.1
                      have p423_2 := h423c.2.2.1
                      have p423_3 := h423c.2.2.2
                      linarith only [h422, hlam, p423_0]
                    · have p423_0 := h423c.1
                      have p423_1 := h423c.2.1
                      have p423_2 := h423c.2.2.1
                      have p423_3 := h423c.2.2.2
                      linarith only [hlam, p423_0]
                  · linarith only [h332, h421, h422, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi3]
                · linarith only [h413, h415, h421, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3, u3ehi2]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h453 | h453
            · rcases m.htr 2 3 5 (by decide) (by decide) with h454 | h454
              · linarith only [h332, h411, h454, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi0]
              · linarith only [h453, h454, hc35, hlam, hphi, u3ehi3]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h457 | h457
              · linarith only [h414, h453, h457, hc34, hlam, hphi, u3ehi1]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h459 | h459
                · rcases m.htr 3 4 5 (by decide) (by decide) with h460 | h460
                  · rcases h5bigk with h461c | h461c | h461c | h461c | h461c | h461c | h461c | h461c | h461c | h461c | h461c | h461c | h461c | h461c | h461c | h461c | h461c | h461c | h461c | h461c | h461c | h461c | h461c | h461c | h461c
                    · have p461_0 := h461c.1
                      have p461_1 := h461c.2.1
                      have p461_2 := h461c.2.2.1
                      have p461_3 := h461c.2.2.2
                      linarith only [hlam, p461_0]
                    · have p461_0 := h461c.1
                      have p461_1 := h461c.2.1
                      have p461_2 := h461c.2.2.1
                      have p461_3 := h461c.2.2.2
                      linarith only [h0, hlam, p461_1]
                    · have p461_0 := h461c.1
                      have p461_1 := h461c.2.1
                      have p461_2 := h461c.2.2.1
                      have p461_3 := h461c.2.2.2
                      linarith only [h413, hc25, hlam, hphi, ht0b, ht5b, p461_1, u0elo3]
                    · have p461_0 := h461c.1
                      have p461_1 := h461c.2.1
                      have p461_2 := h461c.2.2.1
                      have p461_3 := h461c.2.2.2
                      linarith only [h411, hlam, p461_1]
                    · have p461_0 := h461c.1
                      have p461_1 := h461c.2.1
                      have p461_2 := h461c.2.2.1
                      have p461_3 := h461c.2.2.2
                      linarith only [hc45, hlam, hphi, ht0b, ht5b, p461_1, u0elo4]
                    · have p461_0 := h461c.1
                      have p461_1 := h461c.2.1
                      have p461_2 := h461c.2.2.1
                      have p461_3 := h461c.2.2.2
                      linarith only [h0, h414, hc01, hc35, hlam, hphi, ht12, ht23, p461_1]
                    · have p461_0 := h461c.1
                      have p461_1 := h461c.2.1
                      have p461_2 := h461c.2.2.1
                      have p461_3 := h461c.2.2.2
                      linarith only [hlam, p461_0]
                    · have p461_0 := h461c.1
                      have p461_1 := h461c.2.1
                      have p461_2 := h461c.2.2.1
                      have p461_3 := h461c.2.2.2
                      linarith only [h414, h457, h460, hc34, hlam, hphi, p461_1, u3ehi2]
                    · have p461_0 := h461c.1
                      have p461_1 := h461c.2.1
                      have p461_2 := h461c.2.2.1
                      have p461_3 := h461c.2.2.2
                      linarith only [h414, hlam, p461_1]
                    · have p461_0 := h461c.1
                      have p461_1 := h461c.2.1
                      have p461_2 := h461c.2.2.1
                      have p461_3 := h461c.2.2.2
                      rcases p461_3 (m.d 0 5) (by simp) with h471 | h471
                      · linarith only [h0, h471, hlam]
                      · linarith only [h413, h471, hlam]
                    · have p461_0 := h461c.1
                      have p461_1 := h461c.2.1
                      have p461_2 := h461c.2.2.1
                      have p461_3 := h461c.2.2.2
                      linarith only [h332, hlam, p461_1]
                    · have p461_0 := h461c.1
                      have p461_1 := h461c.2.1
                      have p461_2 := h461c.2.2.1
                      have p461_3 := h461c.2.2.2
                      linarith only [h332, hc15, hlam, hphi, ht0b, ht5b, p461_1, u0elo4]
                    · have p461_0 := h461c.1
                      have p461_1 := h461c.2.1
                      have p461_2 := h461c.2.2.1
                      have p461_3 := h461c.2.2.2
                      linarith only [hlam, p461_0]
                    · have p461_0 := h461c.1
                      have p461_1 := h461c.2.1
                      have p461_2 := h461c.2.2.1
                      have p461_3 := h461c.2.2.2
                      linarith only [h457, hlam, p461_1]
                    · have p461_0 := h461c.1
                      have p461_1 := h461c.2.1
                      have p461_2 := h461c.2.2.1
                      have p461_3 := h461c.2.2.2
                      linarith only [h332, hc45, hlam, hphi, ht0b, ht5b, p461_1, u0elo1]
                    · have p461_0 := h461c.1
                      have p461_1 := h461c.2.1
                      have p461_2 := h461c.2.2.1
                      have p461_3 := h461c.2.2.2
                      linarith only [h0, h460, hc01, hc34, hlam, hphi, ht12, ht23, p461_1]
                    · have p461_0 := h461c.1
                      have p461_1 := h461c.2.1
                      have p461_2 := h461c.2.2.1
                      have p461_3 := h461c.2.2.2
                      linarith only [h0, h460, hc01, hc34, hlam, hphi, ht12, ht23, p461_1]
                    · have p461_0 := h461c.1
                      have p461_1 := h461c.2.1
                      have p461_2 := h461c.2.2.1
                      have p461_3 := h461c.2.2.2
                      linarith only [h457, h460, hc34, hlam, hphi, p461_1, u3ehi2]
                    · have p461_0 := h461c.1
                      have p461_1 := h461c.2.1
                      have p461_2 := h461c.2.2.1
                      have p461_3 := h461c.2.2.2
                      linarith only [hlam, p461_0]
                    · have p461_0 := h461c.1
                      have p461_1 := h461c.2.1
                      have p461_2 := h461c.2.2.1
                      have p461_3 := h461c.2.2.2
                      rcases p461_3 (m.d 0 5) (by simp) with h483 | h483
                      · linarith only [h411, h483, hlam]
                      · linarith only [h413, h483, hlam]
                    · have p461_0 := h461c.1
                      have p461_1 := h461c.2.1
                      have p461_2 := h461c.2.2.1
                      have p461_3 := h461c.2.2.2
                      linarith only [h413, hlam, p461_0]
                    · have p461_0 := h461c.1
                      have p461_1 := h461c.2.1
                      have p461_2 := h461c.2.2.1
                      have p461_3 := h461c.2.2.2
                      linarith only [h0, h332, h457, hc45, hlam, hphi, ht34, p461_1, u3ehi2]
                    · have p461_0 := h461c.1
                      have p461_1 := h461c.2.1
                      have p461_2 := h461c.2.2.1
                      have p461_3 := h461c.2.2.2
                      linarith only [h459, hlam, p461_0]
                    · have p461_0 := h461c.1
                      have p461_1 := h461c.2.1
                      have p461_2 := h461c.2.2.1
                      have p461_3 := h461c.2.2.2
                      linarith only [h460, hlam, p461_0]
                    · have p461_0 := h461c.1
                      have p461_1 := h461c.2.1
                      have p461_2 := h461c.2.2.1
                      have p461_3 := h461c.2.2.2
                      linarith only [hlam, p461_0]
                  · linarith only [h332, h459, h460, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi3]
                · linarith only [h413, h453, h459, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3, u3ehi2]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h493 | h493
          · rcases m.htr 2 3 4 (by decide) (by decide) with h494 | h494
            · rcases m.htr 2 3 5 (by decide) (by decide) with h495 | h495
              · linarith only [h332, h411, h495, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi0]
              · linarith only [h494, h495, hc35, hlam, hphi, u3ehi3]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h498 | h498
              · linarith only [h494, h498, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h500 | h500
                · linarith only [h333, h413, h494, h500, hc34, hlam, hphi, u3ehi0]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h502 | h502
                  · linarith only [h333, h413, h502, hc34, hlam, hphi, u3ehi0]
                  · linarith only [h333, h502, hc45, hlam, hphi, ht34, u3ehi0]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h505 | h505
            · rcases m.htr 2 3 5 (by decide) (by decide) with h506 | h506
              · linarith only [h332, h411, h506, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi0]
              · linarith only [h333, h505, h506, hc35, hlam, hphi, u3ehi0]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h509 | h509
              · linarith only [h493, h505, h509, hc34, hlam, hphi, u3ehi1]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h511 | h511
                · linarith only [h333, h413, h505, h511, hc34, hlam, hphi, u3ehi0]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h513 | h513
                  · linarith only [h333, h413, h513, hc34, hlam, hphi, u3ehi0]
                  · linarith only [h333, h513, hc45, hlam, hphi, ht34, u3ehi0]
  · rcases m.htr 0 3 4 (by decide) (by decide) with h516 | h516
    · rcases m.htr 0 3 5 (by decide) (by decide) with h517 | h517
      · rcases m.htr 0 4 5 (by decide) (by decide) with h518 | h518
        · rcases m.htr 1 3 5 (by decide) (by decide) with h519 | h519
          · rcases m.htr 2 3 4 (by decide) (by decide) with h520 | h520
            · rcases m.htr 2 3 5 (by decide) (by decide) with h521 | h521
              · rcases m.htr 2 4 5 (by decide) (by decide) with h522 | h522
                · rcases m.htr 3 4 5 (by decide) (by decide) with h523 | h523
                  · rcases h5bigk with h524c | h524c | h524c | h524c | h524c | h524c | h524c | h524c | h524c | h524c | h524c | h524c | h524c | h524c | h524c | h524c | h524c | h524c | h524c | h524c | h524c | h524c | h524c | h524c | h524c
                    · have p524_0 := h524c.1
                      have p524_1 := h524c.2.1
                      have p524_2 := h524c.2.2.1
                      have p524_3 := h524c.2.2.2
                      linarith only [hlam, p524_0]
                    · have p524_0 := h524c.1
                      have p524_1 := h524c.2.1
                      have p524_2 := h524c.2.2.1
                      have p524_3 := h524c.2.2.2
                      linarith only [h0, hlam, p524_1]
                    · have p524_0 := h524c.1
                      have p524_1 := h524c.2.1
                      have p524_2 := h524c.2.2.1
                      have p524_3 := h524c.2.2.2
                      linarith only [h332, hlam, p524_0]
                    · have p524_0 := h524c.1
                      have p524_1 := h524c.2.1
                      have p524_2 := h524c.2.2.1
                      have p524_3 := h524c.2.2.2
                      linarith only [hc35, hlam, hphi, ht0b, ht5b, p524_1, u0elo4]
                    · have p524_0 := h524c.1
                      have p524_1 := h524c.2.1
                      have p524_2 := h524c.2.2.1
                      have p524_3 := h524c.2.2.2
                      linarith only [h516, h518, hc45, hlam, hphi, ht0b, ht5b, p524_1, u0elo2]
                    · have p524_0 := h524c.1
                      have p524_1 := h524c.2.1
                      have p524_2 := h524c.2.2.1
                      have p524_3 := h524c.2.2.2
                      linarith only [h0, hc01, hc15, hlam, hphi, p524_1]
                    · have p524_0 := h524c.1
                      have p524_1 := h524c.2.1
                      have p524_2 := h524c.2.2.1
                      have p524_3 := h524c.2.2.2
                      linarith only [hlam, p524_0]
                    · have p524_0 := h524c.1
                      have p524_1 := h524c.2.1
                      have p524_2 := h524c.2.2.1
                      have p524_3 := h524c.2.2.2
                      linarith only [h332, h517, h519, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p524_1, u3ehi4]
                    · have p524_0 := h524c.1
                      have p524_1 := h524c.2.1
                      have p524_2 := h524c.2.2.1
                      have p524_3 := h524c.2.2.2
                      linarith only [h519, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p524_1, u3ehi4]
                    · have p524_0 := h524c.1
                      have p524_1 := h524c.2.1
                      have p524_2 := h524c.2.2.1
                      have p524_3 := h524c.2.2.2
                      rcases p524_3 (m.d 0 5) (by simp) with h534 | h534
                      · linarith only [h0, h534, hlam]
                      · linarith only [h518, h534, hlam]
                    · have p524_0 := h524c.1
                      have p524_1 := h524c.2.1
                      have p524_2 := h524c.2.2.1
                      have p524_3 := h524c.2.2.2
                      linarith only [h517, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p524_1, u3ehi4]
                    · have p524_0 := h524c.1
                      have p524_1 := h524c.2.1
                      have p524_2 := h524c.2.2.1
                      have p524_3 := h524c.2.2.2
                      linarith only [h0, h520, h522, hc01, hc23, hlam, hphi, ht12, p524_1]
                    · have p524_0 := h524c.1
                      have p524_1 := h524c.2.1
                      have p524_2 := h524c.2.2.1
                      have p524_3 := h524c.2.2.2
                      linarith only [hlam, p524_0]
                    · have p524_0 := h524c.1
                      have p524_1 := h524c.2.1
                      have p524_2 := h524c.2.2.1
                      have p524_3 := h524c.2.2.2
                      linarith only [h520, h522, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p524_1, u3ehi4]
                    · have p524_0 := h524c.1
                      have p524_1 := h524c.2.1
                      have p524_2 := h524c.2.2.1
                      have p524_3 := h524c.2.2.2
                      rcases p524_3 (m.d 0 5) (by simp) with h541 | h541
                      · linarith only [h332, h541, hlam]
                      · linarith only [h518, h541, hlam]
                    · have p524_0 := h524c.1
                      have p524_1 := h524c.2.1
                      have p524_2 := h524c.2.2.1
                      have p524_3 := h524c.2.2.2
                      linarith only [h517, hlam, p524_0]
                    · have p524_0 := h524c.1
                      have p524_1 := h524c.2.1
                      have p524_2 := h524c.2.2.1
                      have p524_3 := h524c.2.2.2
                      linarith only [h519, hlam, p524_0]
                    · have p524_0 := h524c.1
                      have p524_1 := h524c.2.1
                      have p524_2 := h524c.2.2.1
                      have p524_3 := h524c.2.2.2
                      linarith only [h521, hlam, p524_0]
                    · have p524_0 := h524c.1
                      have p524_1 := h524c.2.1
                      have p524_2 := h524c.2.2.1
                      have p524_3 := h524c.2.2.2
                      linarith only [hlam, p524_0]
                    · have p524_0 := h524c.1
                      have p524_1 := h524c.2.1
                      have p524_2 := h524c.2.2.1
                      have p524_3 := h524c.2.2.2
                      linarith only [h517, hc45, hlam, hphi, ht0b, ht5b, p524_1, u0elo4]
                    · have p524_0 := h524c.1
                      have p524_1 := h524c.2.1
                      have p524_2 := h524c.2.2.1
                      have p524_3 := h524c.2.2.2
                      linarith only [h518, hlam, p524_0]
                    · have p524_0 := h524c.1
                      have p524_1 := h524c.2.1
                      have p524_2 := h524c.2.2.1
                      have p524_3 := h524c.2.2.2
                      linarith only [h0, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p524_1]
                    · have p524_0 := h524c.1
                      have p524_1 := h524c.2.1
                      have p524_2 := h524c.2.2.1
                      have p524_3 := h524c.2.2.2
                      linarith only [h522, hlam, p524_0]
                    · have p524_0 := h524c.1
                      have p524_1 := h524c.2.1
                      have p524_2 := h524c.2.2.1
                      have p524_3 := h524c.2.2.2
                      linarith only [h523, hlam, p524_0]
                    · have p524_0 := h524c.1
                      have p524_1 := h524c.2.1
                      have p524_2 := h524c.2.2.1
                      have p524_3 := h524c.2.2.2
                      linarith only [hlam, p524_0]
                  · linarith only [h516, h518, h523, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi3]
                · linarith only [h516, h518, h520, h522, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi3]
              · linarith only [h517, h521, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi2]
            · linarith only [h516, h520, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi2]
          · linarith only [h517, h519, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi1]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h559 | h559
          · rcases m.htr 2 3 4 (by decide) (by decide) with h560 | h560
            · rcases m.htr 2 3 5 (by decide) (by decide) with h561 | h561
              · rcases m.htr 2 4 5 (by decide) (by decide) with h562 | h562
                · rcases m.htr 3 4 5 (by decide) (by decide) with h563 | h563
                  · linarith only [h516, h517, h518, h563, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi4]
                  · rcases h5bigk with h565c | h565c | h565c | h565c | h565c | h565c | h565c | h565c | h565c | h565c | h565c | h565c | h565c | h565c | h565c | h565c | h565c | h565c | h565c | h565c | h565c | h565c | h565c | h565c | h565c
                    · have p565_0 := h565c.1
                      have p565_1 := h565c.2.1
                      have p565_2 := h565c.2.2.1
                      have p565_3 := h565c.2.2.2
                      linarith only [hlam, p565_0]
                    · have p565_0 := h565c.1
                      have p565_1 := h565c.2.1
                      have p565_2 := h565c.2.2.1
                      have p565_3 := h565c.2.2.2
                      linarith only [h0, hlam, p565_1]
                    · have p565_0 := h565c.1
                      have p565_1 := h565c.2.1
                      have p565_2 := h565c.2.2.1
                      have p565_3 := h565c.2.2.2
                      linarith only [h332, hlam, p565_0]
                    · have p565_0 := h565c.1
                      have p565_1 := h565c.2.1
                      have p565_2 := h565c.2.2.1
                      have p565_3 := h565c.2.2.2
                      linarith only [hc35, hlam, hphi, ht0b, ht5b, p565_1, u0elo4]
                    · have p565_0 := h565c.1
                      have p565_1 := h565c.2.1
                      have p565_2 := h565c.2.2.1
                      have p565_3 := h565c.2.2.2
                      linarith only [h518, hlam, p565_1]
                    · have p565_0 := h565c.1
                      have p565_1 := h565c.2.1
                      have p565_2 := h565c.2.2.1
                      have p565_3 := h565c.2.2.2
                      linarith only [h0, hc01, hc15, hlam, hphi, p565_1]
                    · have p565_0 := h565c.1
                      have p565_1 := h565c.2.1
                      have p565_2 := h565c.2.2.1
                      have p565_3 := h565c.2.2.2
                      linarith only [hlam, p565_0]
                    · have p565_0 := h565c.1
                      have p565_1 := h565c.2.1
                      have p565_2 := h565c.2.2.1
                      have p565_3 := h565c.2.2.2
                      linarith only [h516, h518, h559, h562, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p565_1, u3ehi3]
                    · have p565_0 := h565c.1
                      have p565_1 := h565c.2.1
                      have p565_2 := h565c.2.2.1
                      have p565_3 := h565c.2.2.2
                      linarith only [h559, h563, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p565_1, u3ehi3]
                    · have p565_0 := h565c.1
                      have p565_1 := h565c.2.1
                      have p565_2 := h565c.2.2.1
                      have p565_3 := h565c.2.2.2
                      linarith only [h516, h518, h559, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p565_1, u3ehi3]
                    · have p565_0 := h565c.1
                      have p565_1 := h565c.2.1
                      have p565_2 := h565c.2.2.1
                      have p565_3 := h565c.2.2.2
                      linarith only [h516, h518, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p565_1, u3ehi3]
                    · have p565_0 := h565c.1
                      have p565_1 := h565c.2.1
                      have p565_2 := h565c.2.2.1
                      have p565_3 := h565c.2.2.2
                      linarith only [h0, h560, h562, hc01, hc23, hlam, hphi, ht12, p565_1]
                    · have p565_0 := h565c.1
                      have p565_1 := h565c.2.1
                      have p565_2 := h565c.2.2.1
                      have p565_3 := h565c.2.2.2
                      linarith only [hlam, p565_0]
                    · have p565_0 := h565c.1
                      have p565_1 := h565c.2.1
                      have p565_2 := h565c.2.2.1
                      have p565_3 := h565c.2.2.2
                      linarith only [h560, h562, h563, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p565_1, u3ehi3]
                    · have p565_0 := h565c.1
                      have p565_1 := h565c.2.1
                      have p565_2 := h565c.2.2.1
                      have p565_3 := h565c.2.2.2
                      linarith only [h516, h518, h560, h562, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p565_1, u3ehi3]
                    · have p565_0 := h565c.1
                      have p565_1 := h565c.2.1
                      have p565_2 := h565c.2.2.1
                      have p565_3 := h565c.2.2.2
                      linarith only [h517, hlam, p565_0]
                    · have p565_0 := h565c.1
                      have p565_1 := h565c.2.1
                      have p565_2 := h565c.2.2.1
                      have p565_3 := h565c.2.2.2
                      linarith only [h559, hlam, p565_0]
                    · have p565_0 := h565c.1
                      have p565_1 := h565c.2.1
                      have p565_2 := h565c.2.2.1
                      have p565_3 := h565c.2.2.2
                      linarith only [h561, hlam, p565_0]
                    · have p565_0 := h565c.1
                      have p565_1 := h565c.2.1
                      have p565_2 := h565c.2.2.1
                      have p565_3 := h565c.2.2.2
                      linarith only [hlam, p565_0]
                    · have p565_0 := h565c.1
                      have p565_1 := h565c.2.1
                      have p565_2 := h565c.2.2.1
                      have p565_3 := h565c.2.2.2
                      linarith only [h563, hlam, p565_1]
                    · have p565_0 := h565c.1
                      have p565_1 := h565c.2.1
                      have p565_2 := h565c.2.2.1
                      have p565_3 := h565c.2.2.2
                      linarith only [h516, h518, hc45, hlam, hphi, ht34, p565_1, u3ehi3]
                    · have p565_0 := h565c.1
                      have p565_1 := h565c.2.1
                      have p565_2 := h565c.2.2.1
                      have p565_3 := h565c.2.2.2
                      linarith only [h0, h560, h562, hc01, hc23, hlam, hphi, ht12, p565_1]
                    · have p565_0 := h565c.1
                      have p565_1 := h565c.2.1
                      have p565_2 := h565c.2.2.1
                      have p565_3 := h565c.2.2.2
                      linarith only [h562, hlam, p565_0]
                    · have p565_0 := h565c.1
                      have p565_1 := h565c.2.1
                      have p565_2 := h565c.2.2.1
                      have p565_3 := h565c.2.2.2
                      linarith only [h560, h562, h563, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p565_1, u3ehi3]
                    · have p565_0 := h565c.1
                      have p565_1 := h565c.2.1
                      have p565_2 := h565c.2.2.1
                      have p565_3 := h565c.2.2.2
                      linarith only [hlam, p565_0]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h591 | h591
                  · linarith only [h332, h516, h518, h562, h591, hlam]
                  · rcases h5bigk with h593c | h593c | h593c | h593c | h593c | h593c | h593c | h593c | h593c | h593c | h593c | h593c | h593c | h593c | h593c | h593c | h593c | h593c | h593c | h593c | h593c | h593c | h593c | h593c | h593c
                    · have p593_0 := h593c.1
                      have p593_1 := h593c.2.1
                      have p593_2 := h593c.2.2.1
                      have p593_3 := h593c.2.2.2
                      linarith only [hlam, p593_0]
                    · have p593_0 := h593c.1
                      have p593_1 := h593c.2.1
                      have p593_2 := h593c.2.2.1
                      have p593_3 := h593c.2.2.2
                      linarith only [h0, hlam, p593_1]
                    · have p593_0 := h593c.1
                      have p593_1 := h593c.2.1
                      have p593_2 := h593c.2.2.1
                      have p593_3 := h593c.2.2.2
                      linarith only [h332, hlam, p593_0]
                    · have p593_0 := h593c.1
                      have p593_1 := h593c.2.1
                      have p593_2 := h593c.2.2.1
                      have p593_3 := h593c.2.2.2
                      linarith only [h591, hc34, hlam, hphi, ht0b, ht45, ht5b, p593_1, u0elo4]
                    · have p593_0 := h593c.1
                      have p593_1 := h593c.2.1
                      have p593_2 := h593c.2.2.1
                      have p593_3 := h593c.2.2.2
                      linarith only [h518, hlam, p593_1]
                    · have p593_0 := h593c.1
                      have p593_1 := h593c.2.1
                      have p593_2 := h593c.2.2.1
                      have p593_3 := h593c.2.2.2
                      linarith only [h0, hc01, hc15, hlam, hphi, p593_1]
                    · have p593_0 := h593c.1
                      have p593_1 := h593c.2.1
                      have p593_2 := h593c.2.2.1
                      have p593_3 := h593c.2.2.2
                      linarith only [hlam, p593_0]
                    · have p593_0 := h593c.1
                      have p593_1 := h593c.2.1
                      have p593_2 := h593c.2.2.1
                      have p593_3 := h593c.2.2.2
                      linarith only [h332, h517, h559, h591, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p593_1, u3ehi3]
                    · have p593_0 := h593c.1
                      have p593_1 := h593c.2.1
                      have p593_2 := h593c.2.2.1
                      have p593_3 := h593c.2.2.2
                      linarith only [h559, h591, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p593_1, u3ehi3]
                    · have p593_0 := h593c.1
                      have p593_1 := h593c.2.1
                      have p593_2 := h593c.2.2.1
                      have p593_3 := h593c.2.2.2
                      linarith only [h516, h518, h559, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p593_1, u3ehi3]
                    · have p593_0 := h593c.1
                      have p593_1 := h593c.2.1
                      have p593_2 := h593c.2.2.1
                      have p593_3 := h593c.2.2.2
                      linarith only [h517, h591, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p593_1, u3ehi3]
                    · have p593_0 := h593c.1
                      have p593_1 := h593c.2.1
                      have p593_2 := h593c.2.2.1
                      have p593_3 := h593c.2.2.2
                      linarith only [h0, h562, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p593_1]
                    · have p593_0 := h593c.1
                      have p593_1 := h593c.2.1
                      have p593_2 := h593c.2.2.1
                      have p593_3 := h593c.2.2.2
                      linarith only [hlam, p593_0]
                    · have p593_0 := h593c.1
                      have p593_1 := h593c.2.1
                      have p593_2 := h593c.2.2.1
                      have p593_3 := h593c.2.2.2
                      linarith only [h562, h591, hc45, hlam, hphi, ht34, p593_1, u3ehi3]
                    · have p593_0 := h593c.1
                      have p593_1 := h593c.2.1
                      have p593_2 := h593c.2.2.1
                      have p593_3 := h593c.2.2.2
                      linarith only [h562, hlam, p593_1]
                    · have p593_0 := h593c.1
                      have p593_1 := h593c.2.1
                      have p593_2 := h593c.2.2.1
                      have p593_3 := h593c.2.2.2
                      linarith only [h517, hlam, p593_0]
                    · have p593_0 := h593c.1
                      have p593_1 := h593c.2.1
                      have p593_2 := h593c.2.2.1
                      have p593_3 := h593c.2.2.2
                      linarith only [h559, hlam, p593_0]
                    · have p593_0 := h593c.1
                      have p593_1 := h593c.2.1
                      have p593_2 := h593c.2.2.1
                      have p593_3 := h593c.2.2.2
                      linarith only [h561, hlam, p593_0]
                    · have p593_0 := h593c.1
                      have p593_1 := h593c.2.1
                      have p593_2 := h593c.2.2.1
                      have p593_3 := h593c.2.2.2
                      linarith only [hlam, p593_0]
                    · have p593_0 := h593c.1
                      have p593_1 := h593c.2.1
                      have p593_2 := h593c.2.2.1
                      have p593_3 := h593c.2.2.2
                      linarith only [h591, hlam, p593_1]
                    · have p593_0 := h593c.1
                      have p593_1 := h593c.2.1
                      have p593_2 := h593c.2.2.1
                      have p593_3 := h593c.2.2.2
                      linarith only [h517, h591, hc45, hlam, hphi, ht34, p593_1, u3ehi3]
                    · have p593_0 := h593c.1
                      have p593_1 := h593c.2.1
                      have p593_2 := h593c.2.2.1
                      have p593_3 := h593c.2.2.2
                      linarith only [h0, h517, h591, hc45, hlam, hphi, ht34, p593_1, u3ehi3]
                    · have p593_0 := h593c.1
                      have p593_1 := h593c.2.1
                      have p593_2 := h593c.2.2.1
                      have p593_3 := h593c.2.2.2
                      linarith only [h332, hc02, hc45, hlam, hphi, ht23, ht34, p593_1]
                    · have p593_0 := h593c.1
                      have p593_1 := h593c.2.1
                      have p593_2 := h593c.2.2.1
                      have p593_3 := h593c.2.2.2
                      linarith only [h591, hc45, hlam, hphi, ht34, p593_1, u3ehi3]
                    · have p593_0 := h593c.1
                      have p593_1 := h593c.2.1
                      have p593_2 := h593c.2.2.1
                      have p593_3 := h593c.2.2.2
                      linarith only [hlam, p593_0]
              · linarith only [h517, h561, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi2]
            · linarith only [h516, h560, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi2]
          · linarith only [h517, h559, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi1]
      · linarith only [h516, h517, hc35, hlam, hphi, u3ehi3]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h623 | h623
      · linarith only [h516, h623, hc34, hlam, hphi, u3ehi4]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h625 | h625
        · rcases m.htr 1 3 5 (by decide) (by decide) with h626 | h626
          · rcases m.htr 2 3 4 (by decide) (by decide) with h627 | h627
            · rcases m.htr 2 3 5 (by decide) (by decide) with h628 | h628
              · rcases m.htr 2 4 5 (by decide) (by decide) with h629 | h629
                · rcases m.htr 3 4 5 (by decide) (by decide) with h630 | h630
                  · rcases h5bigk with h631c | h631c | h631c | h631c | h631c | h631c | h631c | h631c | h631c | h631c | h631c | h631c | h631c | h631c | h631c | h631c | h631c | h631c | h631c | h631c | h631c | h631c | h631c | h631c | h631c
                    · have p631_0 := h631c.1
                      have p631_1 := h631c.2.1
                      have p631_2 := h631c.2.2.1
                      have p631_3 := h631c.2.2.2
                      linarith only [hlam, p631_0]
                    · have p631_0 := h631c.1
                      have p631_1 := h631c.2.1
                      have p631_2 := h631c.2.2.1
                      have p631_3 := h631c.2.2.2
                      linarith only [h0, hlam, p631_1]
                    · have p631_0 := h631c.1
                      have p631_1 := h631c.2.1
                      have p631_2 := h631c.2.2.1
                      have p631_3 := h631c.2.2.2
                      linarith only [h332, hlam, p631_0]
                    · have p631_0 := h631c.1
                      have p631_1 := h631c.2.1
                      have p631_2 := h631c.2.2.1
                      have p631_3 := h631c.2.2.2
                      linarith only [h623, hlam, p631_1]
                    · have p631_0 := h631c.1
                      have p631_1 := h631c.2.1
                      have p631_2 := h631c.2.2.1
                      have p631_3 := h631c.2.2.2
                      linarith only [h625, hc45, hlam, hphi, ht0b, ht5b, p631_1, u0elo3]
                    · have p631_0 := h631c.1
                      have p631_1 := h631c.2.1
                      have p631_2 := h631c.2.2.1
                      have p631_3 := h631c.2.2.2
                      linarith only [h0, hc01, hc15, hlam, hphi, p631_1]
                    · have p631_0 := h631c.1
                      have p631_1 := h631c.2.1
                      have p631_2 := h631c.2.2.1
                      have p631_3 := h631c.2.2.2
                      linarith only [hlam, p631_0]
                    · have p631_0 := h631c.1
                      have p631_1 := h631c.2.1
                      have p631_2 := h631c.2.2.1
                      have p631_3 := h631c.2.2.2
                      linarith only [h623, h626, h628, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p631_1, u3ehi0]
                    · have p631_0 := h631c.1
                      have p631_1 := h631c.2.1
                      have p631_2 := h631c.2.2.1
                      have p631_3 := h631c.2.2.2
                      linarith only [h623, h626, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p631_1, u3ehi0]
                    · have p631_0 := h631c.1
                      have p631_1 := h631c.2.1
                      have p631_2 := h631c.2.2.1
                      have p631_3 := h631c.2.2.2
                      rcases p631_3 (m.d 0 5) (by simp) with h641 | h641
                      · linarith only [h0, h641, hlam]
                      · linarith only [h625, h641, hlam]
                    · have p631_0 := h631c.1
                      have p631_1 := h631c.2.1
                      have p631_2 := h631c.2.2.1
                      have p631_3 := h631c.2.2.2
                      linarith only [h623, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p631_1, u3ehi0]
                    · have p631_0 := h631c.1
                      have p631_1 := h631c.2.1
                      have p631_2 := h631c.2.2.1
                      have p631_3 := h631c.2.2.2
                      linarith only [h0, h627, h629, hc01, hc23, hlam, hphi, ht12, p631_1]
                    · have p631_0 := h631c.1
                      have p631_1 := h631c.2.1
                      have p631_2 := h631c.2.2.1
                      have p631_3 := h631c.2.2.2
                      linarith only [hlam, p631_0]
                    · have p631_0 := h631c.1
                      have p631_1 := h631c.2.1
                      have p631_2 := h631c.2.2.1
                      have p631_3 := h631c.2.2.2
                      linarith only [h623, h627, h629, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p631_1, u3ehi0]
                    · have p631_0 := h631c.1
                      have p631_1 := h631c.2.1
                      have p631_2 := h631c.2.2.1
                      have p631_3 := h631c.2.2.2
                      rcases p631_3 (m.d 0 5) (by simp) with h648 | h648
                      · linarith only [h332, h648, hlam]
                      · linarith only [h625, h648, hlam]
                    · have p631_0 := h631c.1
                      have p631_1 := h631c.2.1
                      have p631_2 := h631c.2.2.1
                      have p631_3 := h631c.2.2.2
                      linarith only [h623, h626, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p631_1, u3ehi0]
                    · have p631_0 := h631c.1
                      have p631_1 := h631c.2.1
                      have p631_2 := h631c.2.2.1
                      have p631_3 := h631c.2.2.2
                      linarith only [h626, hlam, p631_0]
                    · have p631_0 := h631c.1
                      have p631_1 := h631c.2.1
                      have p631_2 := h631c.2.2.1
                      have p631_3 := h631c.2.2.2
                      linarith only [h628, hlam, p631_0]
                    · have p631_0 := h631c.1
                      have p631_1 := h631c.2.1
                      have p631_2 := h631c.2.2.1
                      have p631_3 := h631c.2.2.2
                      linarith only [hlam, p631_0]
                    · have p631_0 := h631c.1
                      have p631_1 := h631c.2.1
                      have p631_2 := h631c.2.2.1
                      have p631_3 := h631c.2.2.2
                      linarith only [h627, h630, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p631_1]
                    · have p631_0 := h631c.1
                      have p631_1 := h631c.2.1
                      have p631_2 := h631c.2.2.1
                      have p631_3 := h631c.2.2.2
                      linarith only [h625, hlam, p631_0]
                    · have p631_0 := h631c.1
                      have p631_1 := h631c.2.1
                      have p631_2 := h631c.2.2.1
                      have p631_3 := h631c.2.2.2
                      linarith only [h0, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p631_1]
                    · have p631_0 := h631c.1
                      have p631_1 := h631c.2.1
                      have p631_2 := h631c.2.2.1
                      have p631_3 := h631c.2.2.2
                      linarith only [h629, hlam, p631_0]
                    · have p631_0 := h631c.1
                      have p631_1 := h631c.2.1
                      have p631_2 := h631c.2.2.1
                      have p631_3 := h631c.2.2.2
                      linarith only [h630, hlam, p631_0]
                    · have p631_0 := h631c.1
                      have p631_1 := h631c.2.1
                      have p631_2 := h631c.2.2.1
                      have p631_3 := h631c.2.2.2
                      linarith only [hlam, p631_0]
                  · linarith only [h516, h625, h630, hlam]
                · linarith only [h516, h625, h627, h629, hlam]
              · linarith only [h627, h628, hc35, hlam, hphi, u3ehi3]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h664 | h664
              · linarith only [h627, h664, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h666 | h666
                · rcases m.htr 3 4 5 (by decide) (by decide) with h667 | h667
                  · rcases h5bigk with h668c | h668c | h668c | h668c | h668c | h668c | h668c | h668c | h668c | h668c | h668c | h668c | h668c | h668c | h668c | h668c | h668c | h668c | h668c | h668c | h668c | h668c | h668c | h668c | h668c
                    · have p668_0 := h668c.1
                      have p668_1 := h668c.2.1
                      have p668_2 := h668c.2.2.1
                      have p668_3 := h668c.2.2.2
                      linarith only [hlam, p668_0]
                    · have p668_0 := h668c.1
                      have p668_1 := h668c.2.1
                      have p668_2 := h668c.2.2.1
                      have p668_3 := h668c.2.2.2
                      linarith only [h0, hlam, p668_1]
                    · have p668_0 := h668c.1
                      have p668_1 := h668c.2.1
                      have p668_2 := h668c.2.2.1
                      have p668_3 := h668c.2.2.2
                      linarith only [h332, hlam, p668_0]
                    · have p668_0 := h668c.1
                      have p668_1 := h668c.2.1
                      have p668_2 := h668c.2.2.1
                      have p668_3 := h668c.2.2.2
                      linarith only [h623, hlam, p668_1]
                    · have p668_0 := h668c.1
                      have p668_1 := h668c.2.1
                      have p668_2 := h668c.2.2.1
                      have p668_3 := h668c.2.2.2
                      linarith only [h625, hc45, hlam, hphi, ht0b, ht5b, p668_1, u0elo3]
                    · have p668_0 := h668c.1
                      have p668_1 := h668c.2.1
                      have p668_2 := h668c.2.2.1
                      have p668_3 := h668c.2.2.2
                      linarith only [h0, h626, hc01, hc13, hlam, hphi, p668_1]
                    · have p668_0 := h668c.1
                      have p668_1 := h668c.2.1
                      have p668_2 := h668c.2.2.1
                      have p668_3 := h668c.2.2.2
                      linarith only [hlam, p668_0]
                    · have p668_0 := h668c.1
                      have p668_1 := h668c.2.1
                      have p668_2 := h668c.2.2.1
                      have p668_3 := h668c.2.2.2
                      linarith only [h332, h626, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p668_1]
                    · have p668_0 := h668c.1
                      have p668_1 := h668c.2.1
                      have p668_2 := h668c.2.2.1
                      have p668_3 := h668c.2.2.2
                      linarith only [h623, h626, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p668_1, u3ehi0]
                    · have p668_0 := h668c.1
                      have p668_1 := h668c.2.1
                      have p668_2 := h668c.2.2.1
                      have p668_3 := h668c.2.2.2
                      rcases p668_3 (m.d 0 5) (by simp) with h678 | h678
                      · linarith only [h0, h678, hlam]
                      · linarith only [h625, h678, hlam]
                    · have p668_0 := h668c.1
                      have p668_1 := h668c.2.1
                      have p668_2 := h668c.2.2.1
                      have p668_3 := h668c.2.2.2
                      linarith only [h623, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p668_1, u3ehi0]
                    · have p668_0 := h668c.1
                      have p668_1 := h668c.2.1
                      have p668_2 := h668c.2.2.1
                      have p668_3 := h668c.2.2.2
                      linarith only [h0, hc01, hc25, hlam, hphi, ht12, p668_1]
                    · have p668_0 := h668c.1
                      have p668_1 := h668c.2.1
                      have p668_2 := h668c.2.2.1
                      have p668_3 := h668c.2.2.2
                      linarith only [hlam, p668_0]
                    · have p668_0 := h668c.1
                      have p668_1 := h668c.2.1
                      have p668_2 := h668c.2.2.1
                      have p668_3 := h668c.2.2.2
                      linarith only [h664, hlam, p668_1]
                    · have p668_0 := h668c.1
                      have p668_1 := h668c.2.1
                      have p668_2 := h668c.2.2.1
                      have p668_3 := h668c.2.2.2
                      linarith only [h626, h664, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p668_1]
                    · have p668_0 := h668c.1
                      have p668_1 := h668c.2.1
                      have p668_2 := h668c.2.2.1
                      have p668_3 := h668c.2.2.2
                      linarith only [h623, h626, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p668_1, u3ehi0]
                    · have p668_0 := h668c.1
                      have p668_1 := h668c.2.1
                      have p668_2 := h668c.2.2.1
                      have p668_3 := h668c.2.2.2
                      linarith only [h626, hlam, p668_0]
                    · have p668_0 := h668c.1
                      have p668_1 := h668c.2.1
                      have p668_2 := h668c.2.2.1
                      have p668_3 := h668c.2.2.2
                      linarith only [h626, hc13, hc25, hlam, hphi, ht01, ht0b, ht5b, p668_1]
                    · have p668_0 := h668c.1
                      have p668_1 := h668c.2.1
                      have p668_2 := h668c.2.2.1
                      have p668_3 := h668c.2.2.2
                      linarith only [hlam, p668_0]
                    · have p668_0 := h668c.1
                      have p668_1 := h668c.2.1
                      have p668_2 := h668c.2.2.1
                      have p668_3 := h668c.2.2.2
                      linarith only [h626, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p668_1]
                    · have p668_0 := h668c.1
                      have p668_1 := h668c.2.1
                      have p668_2 := h668c.2.2.1
                      have p668_3 := h668c.2.2.2
                      linarith only [h625, hlam, p668_0]
                    · have p668_0 := h668c.1
                      have p668_1 := h668c.2.1
                      have p668_2 := h668c.2.2.1
                      have p668_3 := h668c.2.2.2
                      linarith only [h626, hc45, hlam, hphi, ht34, p668_1, u3ehi4]
                    · have p668_0 := h668c.1
                      have p668_1 := h668c.2.1
                      have p668_2 := h668c.2.2.1
                      have p668_3 := h668c.2.2.2
                      linarith only [h666, hlam, p668_0]
                    · have p668_0 := h668c.1
                      have p668_1 := h668c.2.1
                      have p668_2 := h668c.2.2.1
                      have p668_3 := h668c.2.2.2
                      linarith only [h667, hlam, p668_0]
                    · have p668_0 := h668c.1
                      have p668_1 := h668c.2.1
                      have p668_2 := h668c.2.2.1
                      have p668_3 := h668c.2.2.2
                      linarith only [hlam, p668_0]
                  · linarith only [h516, h625, h667, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo4, u3ehi0]
                · linarith only [h625, h627, h666, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3, u3ehi2]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h698 | h698
            · rcases m.htr 2 3 5 (by decide) (by decide) with h699 | h699
              · rcases m.htr 2 4 5 (by decide) (by decide) with h700 | h700
                · rcases m.htr 3 4 5 (by decide) (by decide) with h701 | h701
                  · rcases h5bigk with h702c | h702c | h702c | h702c | h702c | h702c | h702c | h702c | h702c | h702c | h702c | h702c | h702c | h702c | h702c | h702c | h702c | h702c | h702c | h702c | h702c | h702c | h702c | h702c | h702c
                    · have p702_0 := h702c.1
                      have p702_1 := h702c.2.1
                      have p702_2 := h702c.2.2.1
                      have p702_3 := h702c.2.2.2
                      linarith only [hlam, p702_0]
                    · have p702_0 := h702c.1
                      have p702_1 := h702c.2.1
                      have p702_2 := h702c.2.2.1
                      have p702_3 := h702c.2.2.2
                      linarith only [h0, hlam, p702_1]
                    · have p702_0 := h702c.1
                      have p702_1 := h702c.2.1
                      have p702_2 := h702c.2.2.1
                      have p702_3 := h702c.2.2.2
                      linarith only [h332, hlam, p702_0]
                    · have p702_0 := h702c.1
                      have p702_1 := h702c.2.1
                      have p702_2 := h702c.2.2.1
                      have p702_3 := h702c.2.2.2
                      linarith only [h623, hlam, p702_1]
                    · have p702_0 := h702c.1
                      have p702_1 := h702c.2.1
                      have p702_2 := h702c.2.2.1
                      have p702_3 := h702c.2.2.2
                      linarith only [hc45, hlam, hphi, ht0b, ht5b, p702_1, u0elo4]
                    · have p702_0 := h702c.1
                      have p702_1 := h702c.2.1
                      have p702_2 := h702c.2.2.1
                      have p702_3 := h702c.2.2.2
                      linarith only [h0, h626, h699, hc01, hc25, hlam, hphi, ht12, p702_1]
                    · have p702_0 := h702c.1
                      have p702_1 := h702c.2.1
                      have p702_2 := h702c.2.2.1
                      have p702_3 := h702c.2.2.2
                      linarith only [hlam, p702_0]
                    · have p702_0 := h702c.1
                      have p702_1 := h702c.2.1
                      have p702_2 := h702c.2.2.1
                      have p702_3 := h702c.2.2.2
                      linarith only [h626, h698, h701, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p702_1]
                    · have p702_0 := h702c.1
                      have p702_1 := h702c.2.1
                      have p702_2 := h702c.2.2.1
                      have p702_3 := h702c.2.2.2
                      linarith only [h626, hlam, p702_1]
                    · have p702_0 := h702c.1
                      have p702_1 := h702c.2.1
                      have p702_2 := h702c.2.2.1
                      have p702_3 := h702c.2.2.2
                      linarith only [h626, h698, h701, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p702_1]
                    · have p702_0 := h702c.1
                      have p702_1 := h702c.2.1
                      have p702_2 := h702c.2.2.1
                      have p702_3 := h702c.2.2.2
                      linarith only [h623, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p702_1, u3ehi0]
                    · have p702_0 := h702c.1
                      have p702_1 := h702c.2.1
                      have p702_2 := h702c.2.2.1
                      have p702_3 := h702c.2.2.2
                      linarith only [h0, h698, h700, hc01, hc23, hlam, hphi, ht12, p702_1]
                    · have p702_0 := h702c.1
                      have p702_1 := h702c.2.1
                      have p702_2 := h702c.2.2.1
                      have p702_3 := h702c.2.2.2
                      linarith only [hlam, p702_0]
                    · have p702_0 := h702c.1
                      have p702_1 := h702c.2.1
                      have p702_2 := h702c.2.2.1
                      have p702_3 := h702c.2.2.2
                      linarith only [h626, h698, h700, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p702_1, u3ehi1]
                    · have p702_0 := h702c.1
                      have p702_1 := h702c.2.1
                      have p702_2 := h702c.2.2.1
                      have p702_3 := h702c.2.2.2
                      rcases p702_3 (m.d 0 5) (by simp) with h717 | h717
                      · linarith only [h332, h717, hlam]
                      · linarith only [h625, h717, hlam]
                    · have p702_0 := h702c.1
                      have p702_1 := h702c.2.1
                      have p702_2 := h702c.2.2.1
                      have p702_3 := h702c.2.2.2
                      linarith only [h623, hc35, hlam, hphi, p702_1, u3ehi0]
                    · have p702_0 := h702c.1
                      have p702_1 := h702c.2.1
                      have p702_2 := h702c.2.2.1
                      have p702_3 := h702c.2.2.2
                      linarith only [h0, hc01, hc35, hlam, hphi, ht12, ht23, p702_1]
                    · have p702_0 := h702c.1
                      have p702_1 := h702c.2.1
                      have p702_2 := h702c.2.2.1
                      have p702_3 := h702c.2.2.2
                      linarith only [h699, hlam, p702_0]
                    · have p702_0 := h702c.1
                      have p702_1 := h702c.2.1
                      have p702_2 := h702c.2.2.1
                      have p702_3 := h702c.2.2.2
                      linarith only [hlam, p702_0]
                    · have p702_0 := h702c.1
                      have p702_1 := h702c.2.1
                      have p702_2 := h702c.2.2.1
                      have p702_3 := h702c.2.2.2
                      linarith only [h698, h701, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p702_1]
                    · have p702_0 := h702c.1
                      have p702_1 := h702c.2.1
                      have p702_2 := h702c.2.2.1
                      have p702_3 := h702c.2.2.2
                      linarith only [h625, hlam, p702_0]
                    · have p702_0 := h702c.1
                      have p702_1 := h702c.2.1
                      have p702_2 := h702c.2.2.1
                      have p702_3 := h702c.2.2.2
                      linarith only [h0, h623, h698, h701, hc01, hc23, hc45, hlam, hphi, ht12, ht34, p702_1, u3ehi0]
                    · have p702_0 := h702c.1
                      have p702_1 := h702c.2.1
                      have p702_2 := h702c.2.2.1
                      have p702_3 := h702c.2.2.2
                      linarith only [h700, hlam, p702_0]
                    · have p702_0 := h702c.1
                      have p702_1 := h702c.2.1
                      have p702_2 := h702c.2.2.1
                      have p702_3 := h702c.2.2.2
                      linarith only [h701, hlam, p702_0]
                    · have p702_0 := h702c.1
                      have p702_1 := h702c.2.1
                      have p702_2 := h702c.2.2.1
                      have p702_3 := h702c.2.2.2
                      linarith only [hlam, p702_0]
                  · linarith only [h516, h625, h701, hlam]
                · linarith only [h516, h625, h698, h700, hlam]
              · linarith only [h698, h699, hc35, hlam, hphi, u3ehi3]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h733 | h733
              · linarith only [h698, h733, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h735 | h735
                · rcases m.htr 3 4 5 (by decide) (by decide) with h736 | h736
                  · rcases h5bigk with h737c | h737c | h737c | h737c | h737c | h737c | h737c | h737c | h737c | h737c | h737c | h737c | h737c | h737c | h737c | h737c | h737c | h737c | h737c | h737c | h737c | h737c | h737c | h737c | h737c
                    · have p737_0 := h737c.1
                      have p737_1 := h737c.2.1
                      have p737_2 := h737c.2.2.1
                      have p737_3 := h737c.2.2.2
                      linarith only [hlam, p737_0]
                    · have p737_0 := h737c.1
                      have p737_1 := h737c.2.1
                      have p737_2 := h737c.2.2.1
                      have p737_3 := h737c.2.2.2
                      linarith only [h0, hlam, p737_1]
                    · have p737_0 := h737c.1
                      have p737_1 := h737c.2.1
                      have p737_2 := h737c.2.2.1
                      have p737_3 := h737c.2.2.2
                      linarith only [h332, hlam, p737_0]
                    · have p737_0 := h737c.1
                      have p737_1 := h737c.2.1
                      have p737_2 := h737c.2.2.1
                      have p737_3 := h737c.2.2.2
                      linarith only [h623, hlam, p737_1]
                    · have p737_0 := h737c.1
                      have p737_1 := h737c.2.1
                      have p737_2 := h737c.2.2.1
                      have p737_3 := h737c.2.2.2
                      linarith only [hc45, hlam, hphi, ht0b, ht5b, p737_1, u0elo4]
                    · have p737_0 := h737c.1
                      have p737_1 := h737c.2.1
                      have p737_2 := h737c.2.2.1
                      have p737_3 := h737c.2.2.2
                      linarith only [h0, hc01, hc15, hlam, hphi, p737_1]
                    · have p737_0 := h737c.1
                      have p737_1 := h737c.2.1
                      have p737_2 := h737c.2.2.1
                      have p737_3 := h737c.2.2.2
                      linarith only [hlam, p737_0]
                    · have p737_0 := h737c.1
                      have p737_1 := h737c.2.1
                      have p737_2 := h737c.2.2.1
                      have p737_3 := h737c.2.2.2
                      linarith only [h332, h626, h736, hc02, hc34, hlam, hphi, ht23, p737_1]
                    · have p737_0 := h737c.1
                      have p737_1 := h737c.2.1
                      have p737_2 := h737c.2.2.1
                      have p737_3 := h737c.2.2.2
                      linarith only [h626, hlam, p737_1]
                    · have p737_0 := h737c.1
                      have p737_1 := h737c.2.1
                      have p737_2 := h737c.2.2.1
                      have p737_3 := h737c.2.2.2
                      rcases p737_3 (m.d 0 5) (by simp) with h747 | h747
                      · linarith only [h0, h747, hlam]
                      · linarith only [h625, h747, hlam]
                    · have p737_0 := h737c.1
                      have p737_1 := h737c.2.1
                      have p737_2 := h737c.2.2.1
                      have p737_3 := h737c.2.2.2
                      linarith only [h623, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p737_1, u3ehi0]
                    · have p737_0 := h737c.1
                      have p737_1 := h737c.2.1
                      have p737_2 := h737c.2.2.1
                      have p737_3 := h737c.2.2.2
                      linarith only [h0, h733, h736, hc01, hc34, hlam, hphi, ht12, ht23, p737_1]
                    · have p737_0 := h737c.1
                      have p737_1 := h737c.2.1
                      have p737_2 := h737c.2.2.1
                      have p737_3 := h737c.2.2.2
                      linarith only [hlam, p737_0]
                    · have p737_0 := h737c.1
                      have p737_1 := h737c.2.1
                      have p737_2 := h737c.2.2.1
                      have p737_3 := h737c.2.2.2
                      linarith only [h733, hlam, p737_1]
                    · have p737_0 := h737c.1
                      have p737_1 := h737c.2.1
                      have p737_2 := h737c.2.2.1
                      have p737_3 := h737c.2.2.2
                      rcases p737_3 (m.d 0 5) (by simp) with h754 | h754
                      · linarith only [h332, h754, hlam]
                      · linarith only [h625, h754, hlam]
                    · have p737_0 := h737c.1
                      have p737_1 := h737c.2.1
                      have p737_2 := h737c.2.2.1
                      have p737_3 := h737c.2.2.2
                      linarith only [h623, h736, hc34, hlam, hphi, p737_1, u3ehi0]
                    · have p737_0 := h737c.1
                      have p737_1 := h737c.2.1
                      have p737_2 := h737c.2.2.1
                      have p737_3 := h737c.2.2.2
                      linarith only [h0, h736, hc01, hc34, hlam, hphi, ht12, ht23, p737_1]
                    · have p737_0 := h737c.1
                      have p737_1 := h737c.2.1
                      have p737_2 := h737c.2.2.1
                      have p737_3 := h737c.2.2.2
                      linarith only [h332, h736, hc02, hc34, hlam, hphi, ht23, p737_1]
                    · have p737_0 := h737c.1
                      have p737_1 := h737c.2.1
                      have p737_2 := h737c.2.2.1
                      have p737_3 := h737c.2.2.2
                      linarith only [hlam, p737_0]
                    · have p737_0 := h737c.1
                      have p737_1 := h737c.2.1
                      have p737_2 := h737c.2.2.1
                      have p737_3 := h737c.2.2.2
                      rcases p737_3 (m.d 0 5) (by simp) with h761 | h761
                      · linarith only [h623, h761, hlam]
                      · linarith only [h625, h761, hlam]
                    · have p737_0 := h737c.1
                      have p737_1 := h737c.2.1
                      have p737_2 := h737c.2.2.1
                      have p737_3 := h737c.2.2.2
                      linarith only [h625, hlam, p737_0]
                    · have p737_0 := h737c.1
                      have p737_1 := h737c.2.1
                      have p737_2 := h737c.2.2.1
                      have p737_3 := h737c.2.2.2
                      linarith only [h0, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p737_1]
                    · have p737_0 := h737c.1
                      have p737_1 := h737c.2.1
                      have p737_2 := h737c.2.2.1
                      have p737_3 := h737c.2.2.2
                      linarith only [h735, hlam, p737_0]
                    · have p737_0 := h737c.1
                      have p737_1 := h737c.2.1
                      have p737_2 := h737c.2.2.1
                      have p737_3 := h737c.2.2.2
                      linarith only [h736, hlam, p737_0]
                    · have p737_0 := h737c.1
                      have p737_1 := h737c.2.1
                      have p737_2 := h737c.2.2.1
                      have p737_3 := h737c.2.2.2
                      linarith only [hlam, p737_0]
                  · linarith only [h516, h625, h736, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo4, u3ehi0]
                · linarith only [h625, h698, h735, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3, u3ehi2]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h771 | h771
          · rcases m.htr 2 3 4 (by decide) (by decide) with h772 | h772
            · rcases m.htr 2 3 5 (by decide) (by decide) with h773 | h773
              · rcases m.htr 2 4 5 (by decide) (by decide) with h774 | h774
                · rcases m.htr 3 4 5 (by decide) (by decide) with h775 | h775
                  · linarith only [h516, h625, h775, hc34, hlam, hphi, u3ehi0]
                  · linarith only [h516, h772, h774, h775, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi0]
                · linarith only [h516, h772, h774, hc45, hlam, hphi, ht34, u3ehi0]
              · linarith only [h516, h771, h772, h773, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi0]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h780 | h780
              · linarith only [h772, h780, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h782 | h782
                · linarith only [h516, h625, h772, h782, hc34, hlam, hphi, u3ehi0]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h784 | h784
                  · linarith only [h772, h782, h784, hc34, hlam, hphi, u3ehi2]
                  · linarith only [h516, h784, hc45, hlam, hphi, ht34, u3ehi0]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h787 | h787
            · rcases m.htr 2 3 5 (by decide) (by decide) with h788 | h788
              · rcases m.htr 2 4 5 (by decide) (by decide) with h789 | h789
                · rcases m.htr 3 4 5 (by decide) (by decide) with h790 | h790
                  · linarith only [h516, h625, h790, hc34, hlam, hphi, u3ehi0]
                  · linarith only [h516, h787, h789, h790, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi0]
                · linarith only [h516, h787, h789, hc45, hlam, hphi, ht34, u3ehi0]
              · linarith only [h516, h787, h788, hc35, hlam, hphi, u3ehi0]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h795 | h795
              · linarith only [h771, h787, h795, hc34, hlam, hphi, u3ehi1]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h797 | h797
                · linarith only [h516, h625, h787, h797, hc34, hlam, hphi, u3ehi0]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h799 | h799
                  · linarith only [h516, h625, h799, hc34, hlam, hphi, u3ehi0]
                  · linarith only [h516, h799, hc45, hlam, hphi, ht34, u3ehi0]

theorem r1l7_10_12_13_25_L_0_L_I_L_R_H_I (m : N7Model)
    (hb0 : CMSig1_7_L_0 m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc05 := m.hcor 0 5 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h3ehi := hb3.1
  have h5bigk := hb5.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h0 | h0
  · exact r1l7_10_12_13_25_L_0_L_I_L_R_H_I_x0 m hb0 hb2 hb3 hb5 h0
  · exact r1l7_10_12_13_25_L_0_L_I_L_R_H_I_x1 m hb0 hb2 hb3 hb5 h0

end R2N4
