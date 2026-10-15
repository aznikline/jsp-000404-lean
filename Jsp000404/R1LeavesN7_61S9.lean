import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_61S8

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 3294000 in
set_option maxHeartbeats 3294000 in
theorem r1l7_20_12_13_15_H_I_L_0_L_I_L_R_x0_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc05 := m.hcor 0 5 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0bigk := hb0.1
  have h2elo := hb2.1
  have h5ehi := hb5.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 2 4 (by decide) (by decide) with h352 | h352
  · rcases m.htr 0 2 5 (by decide) (by decide) with h353 | h353
    · linarith only [h353, h4, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h355 | h355
      · rcases m.htr 0 3 5 (by decide) (by decide) with h356 | h356
        · rcases m.htr 0 4 5 (by decide) (by decide) with h357 | h357
          · linarith only [h352, h357, h4, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi4]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h359 | h359
            · linarith only [h0, h353, h359, hlam]
            · rcases h0bigk with h361c | h361c | h361c | h361c | h361c | h361c | h361c | h361c | h361c | h361c | h361c | h361c | h361c | h361c | h361c | h361c | h361c | h361c | h361c | h361c | h361c | h361c | h361c | h361c | h361c
              · have p361_0 := h361c.1
                have p361_1 := h361c.2.1
                have p361_2 := h361c.2.2.1
                have p361_3 := h361c.2.2.2
                linarith only [hlam, p361_0]
              · have p361_0 := h361c.1
                have p361_1 := h361c.2.1
                have p361_2 := h361c.2.2.1
                have p361_3 := h361c.2.2.2
                linarith only [h352, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p361_1]
              · have p361_0 := h361c.1
                have p361_1 := h361c.2.1
                have p361_2 := h361c.2.2.1
                have p361_3 := h361c.2.2.2
                linarith only [h356, hc01, hlam, hphi, ht0b, ht5b, p361_1, u5ehi3]
              · have p361_0 := h361c.1
                have p361_1 := h361c.2.1
                have p361_2 := h361c.2.2.1
                have p361_3 := h361c.2.2.2
                rcases p361_3 (m.d 0 1) (by simp) with h365 | h365
                · rcases p361_3 (m.d 0 2) (by simp) with h366 | h366
                  · linarith only [h0, h366, hlam]
                  · linarith only [h352, h366, hlam]
                · linarith only [h2, h365, hlam]
              · have p361_0 := h361c.1
                have p361_1 := h361c.2.1
                have p361_2 := h361c.2.2.1
                have p361_3 := h361c.2.2.2
                linarith only [hc01, hlam, hphi, ht0b, ht5b, p361_1, u5ehi0]
              · have p361_0 := h361c.1
                have p361_1 := h361c.2.1
                have p361_2 := h361c.2.2.1
                have p361_3 := h361c.2.2.2
                linarith only [h0, hlam, p361_0]
              · have p361_0 := h361c.1
                have p361_1 := h361c.2.1
                have p361_2 := h361c.2.2.1
                have p361_3 := h361c.2.2.2
                linarith only [hlam, p361_0]
              · have p361_0 := h361c.1
                have p361_1 := h361c.2.1
                have p361_2 := h361c.2.2.1
                have p361_3 := h361c.2.2.2
                linarith only [h4, hlam, p361_0]
              · have p361_0 := h361c.1
                have p361_1 := h361c.2.1
                have p361_2 := h361c.2.2.1
                have p361_3 := h361c.2.2.2
                linarith only [h4, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p361_1, u2elo2]
              · have p361_0 := h361c.1
                have p361_1 := h361c.2.1
                have p361_2 := h361c.2.2.1
                have p361_3 := h361c.2.2.2
                linarith only [h353, hlam, p361_0]
              · have p361_0 := h361c.1
                have p361_1 := h361c.2.1
                have p361_2 := h361c.2.2.1
                have p361_3 := h361c.2.2.2
                linarith only [h1, hlam, p361_1]
              · have p361_0 := h361c.1
                have p361_1 := h361c.2.1
                have p361_2 := h361c.2.2.1
                have p361_3 := h361c.2.2.2
                linarith only [h0, h4, hc12, hlam, hphi, p361_1, u2elo2]
              · have p361_0 := h361c.1
                have p361_1 := h361c.2.1
                have p361_2 := h361c.2.2.1
                have p361_3 := h361c.2.2.2
                linarith only [hlam, p361_0]
              · have p361_0 := h361c.1
                have p361_1 := h361c.2.1
                have p361_2 := h361c.2.2.1
                have p361_3 := h361c.2.2.2
                linarith only [h355, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p361_1, u2elo2]
              · have p361_0 := h361c.1
                have p361_1 := h361c.2.1
                have p361_2 := h361c.2.2.1
                have p361_3 := h361c.2.2.2
                linarith only [h352, h353, h4, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p361_1, u2elo2]
              · have p361_0 := h361c.1
                have p361_1 := h361c.2.1
                have p361_2 := h361c.2.2.1
                have p361_3 := h361c.2.2.2
                linarith only [h2, hlam, p361_0]
              · have p361_0 := h361c.1
                have p361_1 := h361c.2.1
                have p361_2 := h361c.2.2.1
                have p361_3 := h361c.2.2.2
                linarith only [h352, hlam, p361_0]
              · have p361_0 := h361c.1
                have p361_1 := h361c.2.1
                have p361_2 := h361c.2.2.1
                have p361_3 := h361c.2.2.2
                linarith only [h355, hlam, p361_0]
              · have p361_0 := h361c.1
                have p361_1 := h361c.2.1
                have p361_2 := h361c.2.2.1
                have p361_3 := h361c.2.2.2
                linarith only [hlam, p361_0]
              · have p361_0 := h361c.1
                have p361_1 := h361c.2.1
                have p361_2 := h361c.2.2.1
                have p361_3 := h361c.2.2.2
                linarith only [h357, hlam, p361_0]
              · have p361_0 := h361c.1
                have p361_1 := h361c.2.1
                have p361_2 := h361c.2.2.1
                have p361_3 := h361c.2.2.2
                linarith only [h3, hlam, p361_0]
              · have p361_0 := h361c.1
                have p361_1 := h361c.2.1
                have p361_2 := h361c.2.2.1
                have p361_3 := h361c.2.2.2
                linarith only [h352, hc05, hc24, hlam, hphi, ht0b, ht45, ht5b, p361_1]
              · have p361_0 := h361c.1
                have p361_1 := h361c.2.1
                have p361_2 := h361c.2.2.1
                have p361_3 := h361c.2.2.2
                linarith only [h356, hlam, p361_0]
              · have p361_0 := h361c.1
                have p361_1 := h361c.2.1
                have p361_2 := h361c.2.2.1
                have p361_3 := h361c.2.2.2
                linarith only [h355, h356, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p361_1, u2elo2]
              · have p361_0 := h361c.1
                have p361_1 := h361c.2.1
                have p361_2 := h361c.2.2.1
                have p361_3 := h361c.2.2.2
                linarith only [hlam, p361_0]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h391 | h391
          · linarith only [h352, h391, h4, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi4]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h393 | h393
            · linarith only [h0, h353, h393, h4, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi0]
            · rcases h0bigk with h395c | h395c | h395c | h395c | h395c | h395c | h395c | h395c | h395c | h395c | h395c | h395c | h395c | h395c | h395c | h395c | h395c | h395c | h395c | h395c | h395c | h395c | h395c | h395c | h395c
              · have p395_0 := h395c.1
                have p395_1 := h395c.2.1
                have p395_2 := h395c.2.2.1
                have p395_3 := h395c.2.2.2
                linarith only [hlam, p395_0]
              · have p395_0 := h395c.1
                have p395_1 := h395c.2.1
                have p395_2 := h395c.2.2.1
                have p395_3 := h395c.2.2.2
                linarith only [h352, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p395_1]
              · have p395_0 := h395c.1
                have p395_1 := h395c.2.1
                have p395_2 := h395c.2.2.1
                have p395_3 := h395c.2.2.2
                linarith only [h352, h4, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p395_1]
              · have p395_0 := h395c.1
                have p395_1 := h395c.2.1
                have p395_2 := h395c.2.2.1
                have p395_3 := h395c.2.2.2
                rcases p395_3 (m.d 0 1) (by simp) with h399 | h399
                · rcases p395_3 (m.d 0 2) (by simp) with h400 | h400
                  · linarith only [h0, h400, hlam]
                  · linarith only [h352, h400, hlam]
                · linarith only [h2, h399, hlam]
              · have p395_0 := h395c.1
                have p395_1 := h395c.2.1
                have p395_2 := h395c.2.2.1
                have p395_3 := h395c.2.2.2
                linarith only [h352, h356, h4, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p395_1]
              · have p395_0 := h395c.1
                have p395_1 := h395c.2.1
                have p395_2 := h395c.2.2.1
                have p395_3 := h395c.2.2.2
                linarith only [h0, hlam, p395_0]
              · have p395_0 := h395c.1
                have p395_1 := h395c.2.1
                have p395_2 := h395c.2.2.1
                have p395_3 := h395c.2.2.2
                linarith only [hlam, p395_0]
              · have p395_0 := h395c.1
                have p395_1 := h395c.2.1
                have p395_2 := h395c.2.2.1
                have p395_3 := h395c.2.2.2
                linarith only [h4, hlam, p395_0]
              · have p395_0 := h395c.1
                have p395_1 := h395c.2.1
                have p395_2 := h395c.2.2.1
                have p395_3 := h395c.2.2.2
                linarith only [h4, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p395_1, u2elo2]
              · have p395_0 := h395c.1
                have p395_1 := h395c.2.1
                have p395_2 := h395c.2.2.1
                have p395_3 := h395c.2.2.2
                linarith only [h353, hlam, p395_0]
              · have p395_0 := h395c.1
                have p395_1 := h395c.2.1
                have p395_2 := h395c.2.2.1
                have p395_3 := h395c.2.2.2
                linarith only [h1, hlam, p395_1]
              · have p395_0 := h395c.1
                have p395_1 := h395c.2.1
                have p395_2 := h395c.2.2.1
                have p395_3 := h395c.2.2.2
                linarith only [h356, hc02, hc35, hlam, hphi, ht23, p395_1]
              · have p395_0 := h395c.1
                have p395_1 := h395c.2.1
                have p395_2 := h395c.2.2.1
                have p395_3 := h395c.2.2.2
                linarith only [hlam, p395_0]
              · have p395_0 := h395c.1
                have p395_1 := h395c.2.1
                have p395_2 := h395c.2.2.1
                have p395_3 := h395c.2.2.2
                linarith only [h2, h356, hc14, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p395_1]
              · have p395_0 := h395c.1
                have p395_1 := h395c.2.1
                have p395_2 := h395c.2.2.1
                have p395_3 := h395c.2.2.2
                linarith only [h356, hlam, p395_1]
              · have p395_0 := h395c.1
                have p395_1 := h395c.2.1
                have p395_2 := h395c.2.2.1
                have p395_3 := h395c.2.2.2
                linarith only [h2, hlam, p395_0]
              · have p395_0 := h395c.1
                have p395_1 := h395c.2.1
                have p395_2 := h395c.2.2.1
                have p395_3 := h395c.2.2.2
                linarith only [h352, hlam, p395_0]
              · have p395_0 := h395c.1
                have p395_1 := h395c.2.1
                have p395_2 := h395c.2.2.1
                have p395_3 := h395c.2.2.2
                linarith only [h355, hlam, p395_0]
              · have p395_0 := h395c.1
                have p395_1 := h395c.2.1
                have p395_2 := h395c.2.2.1
                have p395_3 := h395c.2.2.2
                linarith only [hlam, p395_0]
              · have p395_0 := h395c.1
                have p395_1 := h395c.2.1
                have p395_2 := h395c.2.2.1
                have p395_3 := h395c.2.2.2
                linarith only [h391, hlam, p395_0]
              · have p395_0 := h395c.1
                have p395_1 := h395c.2.1
                have p395_2 := h395c.2.2.1
                have p395_3 := h395c.2.2.2
                linarith only [h3, hlam, p395_0]
              · have p395_0 := h395c.1
                have p395_1 := h395c.2.1
                have p395_2 := h395c.2.2.1
                have p395_3 := h395c.2.2.2
                linarith only [h352, h353, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p395_1, u2elo4]
              · have p395_0 := h395c.1
                have p395_1 := h395c.2.1
                have p395_2 := h395c.2.2.1
                have p395_3 := h395c.2.2.2
                linarith only [h353, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p395_1, u2elo4]
              · have p395_0 := h395c.1
                have p395_1 := h395c.2.1
                have p395_2 := h395c.2.2.1
                have p395_3 := h395c.2.2.2
                linarith only [h2, h353, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p395_1, u2elo4]
              · have p395_0 := h395c.1
                have p395_1 := h395c.2.1
                have p395_2 := h395c.2.2.1
                have p395_3 := h395c.2.2.2
                linarith only [hlam, p395_0]
      · linarith only [h352, h355, h4, hlam]
  · rcases m.htr 0 2 5 (by decide) (by decide) with h426 | h426
    · linarith only [h4, h426, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h428 | h428
      · rcases m.htr 0 3 5 (by decide) (by decide) with h429 | h429
        · rcases m.htr 0 4 5 (by decide) (by decide) with h430 | h430
          · rcases m.htr 1 2 5 (by decide) (by decide) with h431 | h431
            · linarith only [h426, h431, hc02, hlam, hphi, u2elo1]
            · rcases h0bigk with h433c | h433c | h433c | h433c | h433c | h433c | h433c | h433c | h433c | h433c | h433c | h433c | h433c | h433c | h433c | h433c | h433c | h433c | h433c | h433c | h433c | h433c | h433c | h433c | h433c
              · have p433_0 := h433c.1
                have p433_1 := h433c.2.1
                have p433_2 := h433c.2.2.1
                have p433_3 := h433c.2.2.2
                linarith only [hlam, p433_0]
              · have p433_0 := h433c.1
                have p433_1 := h433c.2.1
                have p433_2 := h433c.2.2.1
                have p433_3 := h433c.2.2.2
                rcases p433_3 (m.d 0 1) (by simp) with h435 | h435
                · rcases p433_3 (m.d 0 2) (by simp) with h436 | h436
                  · linarith only [h0, h436, hlam]
                  · rcases p433_3 (m.d 0 3) (by simp) with h438 | h438
                    · linarith only [h1, h438, hlam]
                    · linarith only [h4, h438, hlam]
                · linarith only [h0, h435, hlam]
              · have p433_0 := h433c.1
                have p433_1 := h433c.2.1
                have p433_2 := h433c.2.2.1
                have p433_3 := h433c.2.2.2
                linarith only [h428, h430, hc01, hlam, hphi, ht0b, ht5b, p433_1, u5ehi4]
              · have p433_0 := h433c.1
                have p433_1 := h433c.2.1
                have p433_2 := h433c.2.2.1
                have p433_3 := h433c.2.2.2
                linarith only [h430, hc01, hlam, hphi, ht0b, ht5b, p433_1, u5ehi4]
              · have p433_0 := h433c.1
                have p433_1 := h433c.2.1
                have p433_2 := h433c.2.2.1
                have p433_3 := h433c.2.2.2
                linarith only [hc01, hlam, hphi, ht0b, ht5b, p433_1, u5ehi0]
              · have p433_0 := h433c.1
                have p433_1 := h433c.2.1
                have p433_2 := h433c.2.2.1
                have p433_3 := h433c.2.2.2
                linarith only [h0, hlam, p433_0]
              · have p433_0 := h433c.1
                have p433_1 := h433c.2.1
                have p433_2 := h433c.2.2.1
                have p433_3 := h433c.2.2.2
                linarith only [hlam, p433_0]
              · have p433_0 := h433c.1
                have p433_1 := h433c.2.1
                have p433_2 := h433c.2.2.1
                have p433_3 := h433c.2.2.2
                linarith only [h4, hlam, p433_0]
              · have p433_0 := h433c.1
                have p433_1 := h433c.2.1
                have p433_2 := h433c.2.2.1
                have p433_3 := h433c.2.2.2
                linarith only [h352, hlam, p433_1]
              · have p433_0 := h433c.1
                have p433_1 := h433c.2.1
                have p433_2 := h433c.2.2.1
                have p433_3 := h433c.2.2.2
                linarith only [h426, hlam, p433_0]
              · have p433_0 := h433c.1
                have p433_1 := h433c.2.1
                have p433_2 := h433c.2.2.1
                have p433_3 := h433c.2.2.2
                linarith only [h1, hlam, p433_1]
              · have p433_0 := h433c.1
                have p433_1 := h433c.2.1
                have p433_2 := h433c.2.2.1
                have p433_3 := h433c.2.2.2
                linarith only [h0, h4, hc12, hlam, hphi, p433_1, u2elo2]
              · have p433_0 := h433c.1
                have p433_1 := h433c.2.1
                have p433_2 := h433c.2.2.1
                have p433_3 := h433c.2.2.2
                linarith only [hlam, p433_0]
              · have p433_0 := h433c.1
                have p433_1 := h433c.2.1
                have p433_2 := h433c.2.2.1
                have p433_3 := h433c.2.2.2
                linarith only [h4, h430, hlam, hphi, ht01, ht0b, ht12, ht5b, p433_1, u2elo2, u5ehi4]
              · have p433_0 := h433c.1
                have p433_1 := h433c.2.1
                have p433_2 := h433c.2.2.1
                have p433_3 := h433c.2.2.2
                linarith only [h3, h4, hlam, hphi, ht01, ht0b, ht12, ht5b, p433_1, u2elo2, u5ehi1]
              · have p433_0 := h433c.1
                have p433_1 := h433c.2.1
                have p433_2 := h433c.2.2.1
                have p433_3 := h433c.2.2.2
                linarith only [h2, hlam, p433_0]
              · have p433_0 := h433c.1
                have p433_1 := h433c.2.1
                have p433_2 := h433c.2.2.1
                have p433_3 := h433c.2.2.2
                linarith only [h0, h352, hc12, hlam, hphi, p433_1, u2elo3]
              · have p433_0 := h433c.1
                have p433_1 := h433c.2.1
                have p433_2 := h433c.2.2.1
                have p433_3 := h433c.2.2.2
                linarith only [h428, hlam, p433_0]
              · have p433_0 := h433c.1
                have p433_1 := h433c.2.1
                have p433_2 := h433c.2.2.1
                have p433_3 := h433c.2.2.2
                linarith only [hlam, p433_0]
              · have p433_0 := h433c.1
                have p433_1 := h433c.2.1
                have p433_2 := h433c.2.2.1
                have p433_3 := h433c.2.2.2
                linarith only [h3, h4, h428, hlam, hphi, ht01, ht0b, ht12, ht5b, p433_1, u2elo2, u5ehi1]
              · have p433_0 := h433c.1
                have p433_1 := h433c.2.1
                have p433_2 := h433c.2.2.1
                have p433_3 := h433c.2.2.2
                linarith only [h3, hlam, p433_0]
              · have p433_0 := h433c.1
                have p433_1 := h433c.2.1
                have p433_2 := h433c.2.2.1
                have p433_3 := h433c.2.2.2
                linarith only [h0, h426, hc12, hlam, hphi, p433_1, u2elo4]
              · have p433_0 := h433c.1
                have p433_1 := h433c.2.1
                have p433_2 := h433c.2.2.1
                have p433_3 := h433c.2.2.2
                linarith only [h429, hlam, p433_0]
              · have p433_0 := h433c.1
                have p433_1 := h433c.2.1
                have p433_2 := h433c.2.2.1
                have p433_3 := h433c.2.2.2
                linarith only [h430, hlam, p433_1]
              · have p433_0 := h433c.1
                have p433_1 := h433c.2.1
                have p433_2 := h433c.2.2.1
                have p433_3 := h433c.2.2.2
                linarith only [hlam, p433_0]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h465 | h465
            · linarith only [h0, h4, h465, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
            · rcases h0bigk with h467c | h467c | h467c | h467c | h467c | h467c | h467c | h467c | h467c | h467c | h467c | h467c | h467c | h467c | h467c | h467c | h467c | h467c | h467c | h467c | h467c | h467c | h467c | h467c | h467c
              · have p467_0 := h467c.1
                have p467_1 := h467c.2.1
                have p467_2 := h467c.2.2.1
                have p467_3 := h467c.2.2.2
                linarith only [hlam, p467_0]
              · have p467_0 := h467c.1
                have p467_1 := h467c.2.1
                have p467_2 := h467c.2.2.1
                have p467_3 := h467c.2.2.2
                rcases p467_3 (m.d 0 1) (by simp) with h469 | h469
                · rcases p467_3 (m.d 0 2) (by simp) with h470 | h470
                  · linarith only [h0, h470, hlam]
                  · rcases p467_3 (m.d 0 3) (by simp) with h472 | h472
                    · linarith only [h1, h472, hlam]
                    · linarith only [h4, h472, hlam]
                · linarith only [h0, h469, hlam]
              · have p467_0 := h467c.1
                have p467_1 := h467c.2.1
                have p467_2 := h467c.2.2.1
                have p467_3 := h467c.2.2.2
                linarith only [h429, hc01, hlam, hphi, ht0b, ht5b, p467_1, u5ehi3]
              · have p467_0 := h467c.1
                have p467_1 := h467c.2.1
                have p467_2 := h467c.2.2.1
                have p467_3 := h467c.2.2.2
                rcases p467_3 (m.d 0 1) (by simp) with h477 | h477
                · rcases p467_3 (m.d 0 2) (by simp) with h478 | h478
                  · linarith only [h0, h478, hlam]
                  · rcases p467_3 (m.d 0 3) (by simp) with h480 | h480
                    · linarith only [h1, h480, hlam]
                    · linarith only [h428, h480, hlam]
                · linarith only [h2, h477, hlam]
              · have p467_0 := h467c.1
                have p467_1 := h467c.2.1
                have p467_2 := h467c.2.2.1
                have p467_3 := h467c.2.2.2
                linarith only [hc01, hlam, hphi, ht0b, ht5b, p467_1, u5ehi0]
              · have p467_0 := h467c.1
                have p467_1 := h467c.2.1
                have p467_2 := h467c.2.2.1
                have p467_3 := h467c.2.2.2
                linarith only [h0, hlam, p467_0]
              · have p467_0 := h467c.1
                have p467_1 := h467c.2.1
                have p467_2 := h467c.2.2.1
                have p467_3 := h467c.2.2.2
                linarith only [hlam, p467_0]
              · have p467_0 := h467c.1
                have p467_1 := h467c.2.1
                have p467_2 := h467c.2.2.1
                have p467_3 := h467c.2.2.2
                linarith only [h4, hlam, p467_0]
              · have p467_0 := h467c.1
                have p467_1 := h467c.2.1
                have p467_2 := h467c.2.2.1
                have p467_3 := h467c.2.2.2
                linarith only [h352, hlam, p467_1]
              · have p467_0 := h467c.1
                have p467_1 := h467c.2.1
                have p467_2 := h467c.2.2.1
                have p467_3 := h467c.2.2.2
                linarith only [h426, hlam, p467_0]
              · have p467_0 := h467c.1
                have p467_1 := h467c.2.1
                have p467_2 := h467c.2.2.1
                have p467_3 := h467c.2.2.2
                linarith only [h1, hlam, p467_1]
              · have p467_0 := h467c.1
                have p467_1 := h467c.2.1
                have p467_2 := h467c.2.2.1
                have p467_3 := h467c.2.2.2
                linarith only [h4, hc02, hlam, hphi, p467_1, u2elo2]
              · have p467_0 := h467c.1
                have p467_1 := h467c.2.1
                have p467_2 := h467c.2.2.1
                have p467_3 := h467c.2.2.2
                linarith only [hlam, p467_0]
              · have p467_0 := h467c.1
                have p467_1 := h467c.2.1
                have p467_2 := h467c.2.2.1
                have p467_3 := h467c.2.2.2
                linarith only [h0, h352, h4, hc12, hlam, hphi, p467_1, u2elo2]
              · have p467_0 := h467c.1
                have p467_1 := h467c.2.1
                have p467_2 := h467c.2.2.1
                have p467_3 := h467c.2.2.2
                linarith only [h3, h4, hlam, hphi, ht01, ht0b, ht12, ht5b, p467_1, u2elo2, u5ehi1]
              · have p467_0 := h467c.1
                have p467_1 := h467c.2.1
                have p467_2 := h467c.2.2.1
                have p467_3 := h467c.2.2.2
                linarith only [h2, hlam, p467_0]
              · have p467_0 := h467c.1
                have p467_1 := h467c.2.1
                have p467_2 := h467c.2.2.1
                have p467_3 := h467c.2.2.2
                linarith only [h0, h352, hc12, hlam, hphi, p467_1, u2elo3]
              · have p467_0 := h467c.1
                have p467_1 := h467c.2.1
                have p467_2 := h467c.2.2.1
                have p467_3 := h467c.2.2.2
                linarith only [h428, hlam, p467_0]
              · have p467_0 := h467c.1
                have p467_1 := h467c.2.1
                have p467_2 := h467c.2.2.1
                have p467_3 := h467c.2.2.2
                linarith only [hlam, p467_0]
              · have p467_0 := h467c.1
                have p467_1 := h467c.2.1
                have p467_2 := h467c.2.2.1
                have p467_3 := h467c.2.2.2
                linarith only [h430, hlam, p467_0]
              · have p467_0 := h467c.1
                have p467_1 := h467c.2.1
                have p467_2 := h467c.2.2.1
                have p467_3 := h467c.2.2.2
                linarith only [h3, hlam, p467_0]
              · have p467_0 := h467c.1
                have p467_1 := h467c.2.1
                have p467_2 := h467c.2.2.1
                have p467_3 := h467c.2.2.2
                linarith only [h0, h430, hc12, hc45, hlam, hphi, ht23, ht34, p467_1]
              · have p467_0 := h467c.1
                have p467_1 := h467c.2.1
                have p467_2 := h467c.2.2.1
                have p467_3 := h467c.2.2.2
                linarith only [h429, hlam, p467_0]
              · have p467_0 := h467c.1
                have p467_1 := h467c.2.1
                have p467_2 := h467c.2.2.1
                have p467_3 := h467c.2.2.2
                linarith only [h4, h429, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p467_1, u2elo2]
              · have p467_0 := h467c.1
                have p467_1 := h467c.2.1
                have p467_2 := h467c.2.2.1
                have p467_3 := h467c.2.2.2
                linarith only [hlam, p467_0]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h505 | h505
          · linarith only [h428, h429, h505, hlam]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h507 | h507
            · linarith only [h0, h4, h507, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
            · rcases h0bigk with h509c | h509c | h509c | h509c | h509c | h509c | h509c | h509c | h509c | h509c | h509c | h509c | h509c | h509c | h509c | h509c | h509c | h509c | h509c | h509c | h509c | h509c | h509c | h509c | h509c
              · have p509_0 := h509c.1
                have p509_1 := h509c.2.1
                have p509_2 := h509c.2.2.1
                have p509_3 := h509c.2.2.2
                linarith only [hlam, p509_0]
              · have p509_0 := h509c.1
                have p509_1 := h509c.2.1
                have p509_2 := h509c.2.2.1
                have p509_3 := h509c.2.2.2
                rcases p509_3 (m.d 0 1) (by simp) with h511 | h511
                · rcases p509_3 (m.d 0 2) (by simp) with h512 | h512
                  · linarith only [h0, h512, hlam]
                  · rcases p509_3 (m.d 0 3) (by simp) with h514 | h514
                    · linarith only [h1, h514, hlam]
                    · linarith only [h4, h514, hlam]
                · linarith only [h0, h511, hlam]
              · have p509_0 := h509c.1
                have p509_1 := h509c.2.1
                have p509_2 := h509c.2.2.1
                have p509_3 := h509c.2.2.2
                linarith only [h428, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p509_1]
              · have p509_0 := h509c.1
                have p509_1 := h509c.2.1
                have p509_2 := h509c.2.2.1
                have p509_3 := h509c.2.2.2
                rcases p509_3 (m.d 0 1) (by simp) with h519 | h519
                · rcases p509_3 (m.d 0 2) (by simp) with h520 | h520
                  · linarith only [h0, h520, hlam]
                  · rcases p509_3 (m.d 0 3) (by simp) with h522 | h522
                    · linarith only [h1, h522, hlam]
                    · linarith only [h428, h522, hlam]
                · linarith only [h2, h519, hlam]
              · have p509_0 := h509c.1
                have p509_1 := h509c.2.1
                have p509_2 := h509c.2.2.1
                have p509_3 := h509c.2.2.2
                linarith only [hc01, hlam, hphi, ht0b, ht5b, p509_1, u5ehi0]
              · have p509_0 := h509c.1
                have p509_1 := h509c.2.1
                have p509_2 := h509c.2.2.1
                have p509_3 := h509c.2.2.2
                linarith only [h0, hlam, p509_0]
              · have p509_0 := h509c.1
                have p509_1 := h509c.2.1
                have p509_2 := h509c.2.2.1
                have p509_3 := h509c.2.2.2
                linarith only [hlam, p509_0]
              · have p509_0 := h509c.1
                have p509_1 := h509c.2.1
                have p509_2 := h509c.2.2.1
                have p509_3 := h509c.2.2.2
                linarith only [h4, hlam, p509_0]
              · have p509_0 := h509c.1
                have p509_1 := h509c.2.1
                have p509_2 := h509c.2.2.1
                have p509_3 := h509c.2.2.2
                linarith only [h352, hlam, p509_1]
              · have p509_0 := h509c.1
                have p509_1 := h509c.2.1
                have p509_2 := h509c.2.2.1
                have p509_3 := h509c.2.2.2
                linarith only [h426, hlam, p509_0]
              · have p509_0 := h509c.1
                have p509_1 := h509c.2.1
                have p509_2 := h509c.2.2.1
                have p509_3 := h509c.2.2.2
                linarith only [h1, hlam, p509_1]
              · have p509_0 := h509c.1
                have p509_1 := h509c.2.1
                have p509_2 := h509c.2.2.1
                have p509_3 := h509c.2.2.2
                linarith only [h0, h4, hc12, hlam, hphi, p509_1, u2elo2]
              · have p509_0 := h509c.1
                have p509_1 := h509c.2.1
                have p509_2 := h509c.2.2.1
                have p509_3 := h509c.2.2.2
                linarith only [hlam, p509_0]
              · have p509_0 := h509c.1
                have p509_1 := h509c.2.1
                have p509_2 := h509c.2.2.1
                have p509_3 := h509c.2.2.2
                linarith only [h0, h352, h4, hc12, hlam, hphi, p509_1, u2elo2]
              · have p509_0 := h509c.1
                have p509_1 := h509c.2.1
                have p509_2 := h509c.2.2.1
                have p509_3 := h509c.2.2.2
                linarith only [h429, hlam, p509_1]
              · have p509_0 := h509c.1
                have p509_1 := h509c.2.1
                have p509_2 := h509c.2.2.1
                have p509_3 := h509c.2.2.2
                linarith only [h2, hlam, p509_0]
              · have p509_0 := h509c.1
                have p509_1 := h509c.2.1
                have p509_2 := h509c.2.2.1
                have p509_3 := h509c.2.2.2
                linarith only [h0, h352, hc12, hlam, hphi, p509_1, u2elo3]
              · have p509_0 := h509c.1
                have p509_1 := h509c.2.1
                have p509_2 := h509c.2.2.1
                have p509_3 := h509c.2.2.2
                linarith only [h428, hlam, p509_0]
              · have p509_0 := h509c.1
                have p509_1 := h509c.2.1
                have p509_2 := h509c.2.2.1
                have p509_3 := h509c.2.2.2
                linarith only [hlam, p509_0]
              · have p509_0 := h509c.1
                have p509_1 := h509c.2.1
                have p509_2 := h509c.2.2.1
                have p509_3 := h509c.2.2.2
                linarith only [h505, hlam, p509_0]
              · have p509_0 := h509c.1
                have p509_1 := h509c.2.1
                have p509_2 := h509c.2.2.1
                have p509_3 := h509c.2.2.2
                linarith only [h3, hlam, p509_0]
              · have p509_0 := h509c.1
                have p509_1 := h509c.2.1
                have p509_2 := h509c.2.2.1
                have p509_3 := h509c.2.2.2
                linarith only [h0, h429, hc12, hc35, hlam, hphi, ht23, p509_1]
              · have p509_0 := h509c.1
                have p509_1 := h509c.2.1
                have p509_2 := h509c.2.2.1
                have p509_3 := h509c.2.2.2
                linarith only [h426, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p509_1, u2elo4]
              · have p509_0 := h509c.1
                have p509_1 := h509c.2.1
                have p509_2 := h509c.2.2.1
                have p509_3 := h509c.2.2.2
                linarith only [h0, h352, h426, hc12, hlam, hphi, p509_1, u2elo4]
              · have p509_0 := h509c.1
                have p509_1 := h509c.2.1
                have p509_2 := h509c.2.2.1
                have p509_3 := h509c.2.2.2
                linarith only [hlam, p509_0]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h547 | h547
        · rcases m.htr 0 4 5 (by decide) (by decide) with h548 | h548
          · rcases m.htr 1 2 5 (by decide) (by decide) with h549 | h549
            · linarith only [h0, h4, h549, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
            · rcases h0bigk with h551c | h551c | h551c | h551c | h551c | h551c | h551c | h551c | h551c | h551c | h551c | h551c | h551c | h551c | h551c | h551c | h551c | h551c | h551c | h551c | h551c | h551c | h551c | h551c | h551c
              · have p551_0 := h551c.1
                have p551_1 := h551c.2.1
                have p551_2 := h551c.2.2.1
                have p551_3 := h551c.2.2.2
                linarith only [hlam, p551_0]
              · have p551_0 := h551c.1
                have p551_1 := h551c.2.1
                have p551_2 := h551c.2.2.1
                have p551_3 := h551c.2.2.2
                rcases p551_3 (m.d 0 1) (by simp) with h553 | h553
                · rcases p551_3 (m.d 0 2) (by simp) with h554 | h554
                  · linarith only [h0, h554, hlam]
                  · rcases p551_3 (m.d 0 3) (by simp) with h556 | h556
                    · linarith only [h1, h556, hlam]
                    · linarith only [h4, h556, hlam]
                · linarith only [h0, h553, hlam]
              · have p551_0 := h551c.1
                have p551_1 := h551c.2.1
                have p551_2 := h551c.2.2.1
                have p551_3 := h551c.2.2.2
                linarith only [h547, hc01, hlam, hphi, ht0b, ht5b, p551_1, u5ehi3]
              · have p551_0 := h551c.1
                have p551_1 := h551c.2.1
                have p551_2 := h551c.2.2.1
                have p551_3 := h551c.2.2.2
                linarith only [h428, h547, hc01, hlam, hphi, ht0b, ht5b, p551_1, u5ehi3]
              · have p551_0 := h551c.1
                have p551_1 := h551c.2.1
                have p551_2 := h551c.2.2.1
                have p551_3 := h551c.2.2.2
                linarith only [hc01, hlam, hphi, ht0b, ht5b, p551_1, u5ehi0]
              · have p551_0 := h551c.1
                have p551_1 := h551c.2.1
                have p551_2 := h551c.2.2.1
                have p551_3 := h551c.2.2.2
                linarith only [h0, hlam, p551_0]
              · have p551_0 := h551c.1
                have p551_1 := h551c.2.1
                have p551_2 := h551c.2.2.1
                have p551_3 := h551c.2.2.2
                linarith only [hlam, p551_0]
              · have p551_0 := h551c.1
                have p551_1 := h551c.2.1
                have p551_2 := h551c.2.2.1
                have p551_3 := h551c.2.2.2
                linarith only [h4, hlam, p551_0]
              · have p551_0 := h551c.1
                have p551_1 := h551c.2.1
                have p551_2 := h551c.2.2.1
                have p551_3 := h551c.2.2.2
                linarith only [h352, hlam, p551_1]
              · have p551_0 := h551c.1
                have p551_1 := h551c.2.1
                have p551_2 := h551c.2.2.1
                have p551_3 := h551c.2.2.2
                linarith only [h426, hlam, p551_0]
              · have p551_0 := h551c.1
                have p551_1 := h551c.2.1
                have p551_2 := h551c.2.2.1
                have p551_3 := h551c.2.2.2
                linarith only [h1, hlam, p551_1]
              · have p551_0 := h551c.1
                have p551_1 := h551c.2.1
                have p551_2 := h551c.2.2.1
                have p551_3 := h551c.2.2.2
                linarith only [h0, h4, hc12, hlam, hphi, p551_1, u2elo2]
              · have p551_0 := h551c.1
                have p551_1 := h551c.2.1
                have p551_2 := h551c.2.2.1
                have p551_3 := h551c.2.2.2
                linarith only [hlam, p551_0]
              · have p551_0 := h551c.1
                have p551_1 := h551c.2.1
                have p551_2 := h551c.2.2.1
                have p551_3 := h551c.2.2.2
                linarith only [h428, hlam, p551_1]
              · have p551_0 := h551c.1
                have p551_1 := h551c.2.1
                have p551_2 := h551c.2.2.1
                have p551_3 := h551c.2.2.2
                linarith only [h3, h352, h428, hlam, hphi, ht01, ht0b, ht12, ht5b, p551_1, u2elo3, u5ehi1]
              · have p551_0 := h551c.1
                have p551_1 := h551c.2.1
                have p551_2 := h551c.2.2.1
                have p551_3 := h551c.2.2.2
                linarith only [h2, hlam, p551_0]
              · have p551_0 := h551c.1
                have p551_1 := h551c.2.1
                have p551_2 := h551c.2.2.1
                have p551_3 := h551c.2.2.2
                linarith only [h0, h352, hc12, hlam, hphi, p551_1, u2elo3]
              · have p551_0 := h551c.1
                have p551_1 := h551c.2.1
                have p551_2 := h551c.2.2.1
                have p551_3 := h551c.2.2.2
                linarith only [h352, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p551_1, u2elo3]
              · have p551_0 := h551c.1
                have p551_1 := h551c.2.1
                have p551_2 := h551c.2.2.1
                have p551_3 := h551c.2.2.2
                linarith only [hlam, p551_0]
              · have p551_0 := h551c.1
                have p551_1 := h551c.2.1
                have p551_2 := h551c.2.2.1
                have p551_3 := h551c.2.2.2
                linarith only [h3, h352, hlam, hphi, ht01, ht0b, ht12, ht5b, p551_1, u2elo3, u5ehi1]
              · have p551_0 := h551c.1
                have p551_1 := h551c.2.1
                have p551_2 := h551c.2.2.1
                have p551_3 := h551c.2.2.2
                linarith only [h3, hlam, p551_0]
              · have p551_0 := h551c.1
                have p551_1 := h551c.2.1
                have p551_2 := h551c.2.2.1
                have p551_3 := h551c.2.2.2
                linarith only [h0, h426, hc12, hlam, hphi, p551_1, u2elo4]
              · have p551_0 := h551c.1
                have p551_1 := h551c.2.1
                have p551_2 := h551c.2.2.1
                have p551_3 := h551c.2.2.2
                linarith only [h547, hlam, p551_0]
              · have p551_0 := h551c.1
                have p551_1 := h551c.2.1
                have p551_2 := h551c.2.2.1
                have p551_3 := h551c.2.2.2
                linarith only [h548, hlam, p551_1]
              · have p551_0 := h551c.1
                have p551_1 := h551c.2.1
                have p551_2 := h551c.2.2.1
                have p551_3 := h551c.2.2.2
                linarith only [hlam, p551_0]
          · linarith only [h428, h547, h548, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h584 | h584
          · rcases m.htr 1 2 5 (by decide) (by decide) with h585 | h585
            · linarith only [h0, h4, h585, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
            · rcases h0bigk with h587c | h587c | h587c | h587c | h587c | h587c | h587c | h587c | h587c | h587c | h587c | h587c | h587c | h587c | h587c | h587c | h587c | h587c | h587c | h587c | h587c | h587c | h587c | h587c | h587c
              · have p587_0 := h587c.1
                have p587_1 := h587c.2.1
                have p587_2 := h587c.2.2.1
                have p587_3 := h587c.2.2.2
                linarith only [hlam, p587_0]
              · have p587_0 := h587c.1
                have p587_1 := h587c.2.1
                have p587_2 := h587c.2.2.1
                have p587_3 := h587c.2.2.2
                rcases p587_3 (m.d 0 1) (by simp) with h589 | h589
                · rcases p587_3 (m.d 0 2) (by simp) with h590 | h590
                  · linarith only [h0, h590, hlam]
                  · rcases p587_3 (m.d 0 3) (by simp) with h592 | h592
                    · linarith only [h1, h592, hlam]
                    · linarith only [h4, h592, hlam]
                · linarith only [h0, h589, hlam]
              · have p587_0 := h587c.1
                have p587_1 := h587c.2.1
                have p587_2 := h587c.2.2.1
                have p587_3 := h587c.2.2.2
                rcases p587_3 (m.d 0 1) (by simp) with h596 | h596
                · rcases p587_3 (m.d 0 2) (by simp) with h597 | h597
                  · linarith only [h0, h597, hlam]
                  · rcases p587_3 (m.d 0 3) (by simp) with h599 | h599
                    · linarith only [h1, h599, hlam]
                    · rcases p587_3 (m.d 0 4) (by simp) with h601 | h601
                      · linarith only [h2, h601, hlam]
                      · linarith only [h428, h601, hlam]
                · linarith only [h1, h596, hlam]
              · have p587_0 := h587c.1
                have p587_1 := h587c.2.1
                have p587_2 := h587c.2.2.1
                have p587_3 := h587c.2.2.2
                linarith only [h584, hc01, hlam, hphi, ht0b, ht5b, p587_1, u5ehi0]
              · have p587_0 := h587c.1
                have p587_1 := h587c.2.1
                have p587_2 := h587c.2.2.1
                have p587_3 := h587c.2.2.2
                linarith only [hc01, hlam, hphi, ht0b, ht5b, p587_1, u5ehi0]
              · have p587_0 := h587c.1
                have p587_1 := h587c.2.1
                have p587_2 := h587c.2.2.1
                have p587_3 := h587c.2.2.2
                linarith only [h0, hlam, p587_0]
              · have p587_0 := h587c.1
                have p587_1 := h587c.2.1
                have p587_2 := h587c.2.2.1
                have p587_3 := h587c.2.2.2
                linarith only [hlam, p587_0]
              · have p587_0 := h587c.1
                have p587_1 := h587c.2.1
                have p587_2 := h587c.2.2.1
                have p587_3 := h587c.2.2.2
                linarith only [h4, hlam, p587_0]
              · have p587_0 := h587c.1
                have p587_1 := h587c.2.1
                have p587_2 := h587c.2.2.1
                have p587_3 := h587c.2.2.2
                linarith only [h352, hlam, p587_1]
              · have p587_0 := h587c.1
                have p587_1 := h587c.2.1
                have p587_2 := h587c.2.2.1
                have p587_3 := h587c.2.2.2
                linarith only [h426, hlam, p587_0]
              · have p587_0 := h587c.1
                have p587_1 := h587c.2.1
                have p587_2 := h587c.2.2.1
                have p587_3 := h587c.2.2.2
                linarith only [h1, hlam, p587_1]
              · have p587_0 := h587c.1
                have p587_1 := h587c.2.1
                have p587_2 := h587c.2.2.1
                have p587_3 := h587c.2.2.2
                linarith only [h0, h4, hc12, hlam, hphi, p587_1, u2elo2]
              · have p587_0 := h587c.1
                have p587_1 := h587c.2.1
                have p587_2 := h587c.2.2.1
                have p587_3 := h587c.2.2.2
                linarith only [hlam, p587_0]
              · have p587_0 := h587c.1
                have p587_1 := h587c.2.1
                have p587_2 := h587c.2.2.1
                have p587_3 := h587c.2.2.2
                linarith only [h428, hlam, p587_1]
              · have p587_0 := h587c.1
                have p587_1 := h587c.2.1
                have p587_2 := h587c.2.2.1
                have p587_3 := h587c.2.2.2
                linarith only [h547, hlam, p587_1]
              · have p587_0 := h587c.1
                have p587_1 := h587c.2.1
                have p587_2 := h587c.2.2.1
                have p587_3 := h587c.2.2.2
                linarith only [h2, hlam, p587_0]
              · have p587_0 := h587c.1
                have p587_1 := h587c.2.1
                have p587_2 := h587c.2.2.1
                have p587_3 := h587c.2.2.2
                linarith only [h0, h352, hc12, hlam, hphi, p587_1, u2elo3]
              · have p587_0 := h587c.1
                have p587_1 := h587c.2.1
                have p587_2 := h587c.2.2.1
                have p587_3 := h587c.2.2.2
                linarith only [h352, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p587_1, u2elo3]
              · have p587_0 := h587c.1
                have p587_1 := h587c.2.1
                have p587_2 := h587c.2.2.1
                have p587_3 := h587c.2.2.2
                linarith only [hlam, p587_0]
              · have p587_0 := h587c.1
                have p587_1 := h587c.2.1
                have p587_2 := h587c.2.2.1
                have p587_3 := h587c.2.2.2
                linarith only [h3, h352, hlam, hphi, ht01, ht0b, ht12, ht5b, p587_1, u2elo3, u5ehi1]
              · have p587_0 := h587c.1
                have p587_1 := h587c.2.1
                have p587_2 := h587c.2.2.1
                have p587_3 := h587c.2.2.2
                linarith only [h3, hlam, p587_0]
              · have p587_0 := h587c.1
                have p587_1 := h587c.2.1
                have p587_2 := h587c.2.2.1
                have p587_3 := h587c.2.2.2
                linarith only [h0, h426, hc12, hlam, hphi, p587_1, u2elo4]
              · have p587_0 := h587c.1
                have p587_1 := h587c.2.1
                have p587_2 := h587c.2.2.1
                have p587_3 := h587c.2.2.2
                linarith only [h0, h4, h426, hc12, hlam, hphi, p587_1, u2elo4]
              · have p587_0 := h587c.1
                have p587_1 := h587c.2.1
                have p587_2 := h587c.2.2.1
                have p587_3 := h587c.2.2.2
                linarith only [h584, hlam, p587_1]
              · have p587_0 := h587c.1
                have p587_1 := h587c.2.1
                have p587_2 := h587c.2.2.1
                have p587_3 := h587c.2.2.2
                linarith only [hlam, p587_0]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h627 | h627
            · linarith only [h0, h3, h4, h426, h627, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi1]
            · rcases h0bigk with h629c | h629c | h629c | h629c | h629c | h629c | h629c | h629c | h629c | h629c | h629c | h629c | h629c | h629c | h629c | h629c | h629c | h629c | h629c | h629c | h629c | h629c | h629c | h629c | h629c
              · have p629_0 := h629c.1
                have p629_1 := h629c.2.1
                have p629_2 := h629c.2.2.1
                have p629_3 := h629c.2.2.2
                linarith only [hlam, p629_0]
              · have p629_0 := h629c.1
                have p629_1 := h629c.2.1
                have p629_2 := h629c.2.2.1
                have p629_3 := h629c.2.2.2
                rcases p629_3 (m.d 0 1) (by simp) with h631 | h631
                · rcases p629_3 (m.d 0 2) (by simp) with h632 | h632
                  · linarith only [h0, h632, hlam]
                  · rcases p629_3 (m.d 0 3) (by simp) with h634 | h634
                    · linarith only [h1, h634, hlam]
                    · linarith only [h4, h634, hlam]
                · linarith only [h0, h631, hlam]
              · have p629_0 := h629c.1
                have p629_1 := h629c.2.1
                have p629_2 := h629c.2.2.1
                have p629_3 := h629c.2.2.2
                rcases p629_3 (m.d 0 1) (by simp) with h638 | h638
                · rcases p629_3 (m.d 0 2) (by simp) with h639 | h639
                  · linarith only [h0, h639, hlam]
                  · rcases p629_3 (m.d 0 3) (by simp) with h641 | h641
                    · linarith only [h1, h641, hlam]
                    · rcases p629_3 (m.d 0 4) (by simp) with h643 | h643
                      · linarith only [h2, h643, hlam]
                      · linarith only [h428, h643, hlam]
                · linarith only [h1, h638, hlam]
              · have p629_0 := h629c.1
                have p629_1 := h629c.2.1
                have p629_2 := h629c.2.2.1
                have p629_3 := h629c.2.2.2
                rcases p629_3 (m.d 0 1) (by simp) with h647 | h647
                · rcases p629_3 (m.d 0 2) (by simp) with h648 | h648
                  · linarith only [h0, h648, hlam]
                  · rcases p629_3 (m.d 0 3) (by simp) with h650 | h650
                    · linarith only [h1, h650, hlam]
                    · rcases p629_3 (m.d 0 4) (by simp) with h652 | h652
                      · linarith only [h2, h652, hlam]
                      · rcases p629_3 (m.d 0 5) (by simp) with h654 | h654
                        · linarith only [h3, h654, hlam]
                        · linarith only [h584, h654, hlam]
                · linarith only [h2, h647, hlam]
              · have p629_0 := h629c.1
                have p629_1 := h629c.2.1
                have p629_2 := h629c.2.2.1
                have p629_3 := h629c.2.2.2
                linarith only [h3, hc01, hlam, hphi, ht0b, ht5b, p629_1, u5ehi1]
              · have p629_0 := h629c.1
                have p629_1 := h629c.2.1
                have p629_2 := h629c.2.2.1
                have p629_3 := h629c.2.2.2
                linarith only [h0, hlam, p629_0]
              · have p629_0 := h629c.1
                have p629_1 := h629c.2.1
                have p629_2 := h629c.2.2.1
                have p629_3 := h629c.2.2.2
                linarith only [hlam, p629_0]
              · have p629_0 := h629c.1
                have p629_1 := h629c.2.1
                have p629_2 := h629c.2.2.1
                have p629_3 := h629c.2.2.2
                linarith only [h4, hlam, p629_0]
              · have p629_0 := h629c.1
                have p629_1 := h629c.2.1
                have p629_2 := h629c.2.2.1
                have p629_3 := h629c.2.2.2
                linarith only [h352, hlam, p629_1]
              · have p629_0 := h629c.1
                have p629_1 := h629c.2.1
                have p629_2 := h629c.2.2.1
                have p629_3 := h629c.2.2.2
                linarith only [h426, hlam, p629_0]
              · have p629_0 := h629c.1
                have p629_1 := h629c.2.1
                have p629_2 := h629c.2.2.1
                have p629_3 := h629c.2.2.2
                linarith only [h1, hlam, p629_1]
              · have p629_0 := h629c.1
                have p629_1 := h629c.2.1
                have p629_2 := h629c.2.2.1
                have p629_3 := h629c.2.2.2
                linarith only [h0, h547, hc12, hc35, hlam, hphi, ht23, p629_1]
              · have p629_0 := h629c.1
                have p629_1 := h629c.2.1
                have p629_2 := h629c.2.2.1
                have p629_3 := h629c.2.2.2
                linarith only [hlam, p629_0]
              · have p629_0 := h629c.1
                have p629_1 := h629c.2.1
                have p629_2 := h629c.2.2.1
                have p629_3 := h629c.2.2.2
                linarith only [h428, hlam, p629_1]
              · have p629_0 := h629c.1
                have p629_1 := h629c.2.1
                have p629_2 := h629c.2.2.1
                have p629_3 := h629c.2.2.2
                linarith only [h547, hlam, p629_1]
              · have p629_0 := h629c.1
                have p629_1 := h629c.2.1
                have p629_2 := h629c.2.2.1
                have p629_3 := h629c.2.2.2
                linarith only [h2, hlam, p629_0]
              · have p629_0 := h629c.1
                have p629_1 := h629c.2.1
                have p629_2 := h629c.2.2.1
                have p629_3 := h629c.2.2.2
                linarith only [h0, h352, hc12, hlam, hphi, p629_1, u2elo3]
              · have p629_0 := h629c.1
                have p629_1 := h629c.2.1
                have p629_2 := h629c.2.2.1
                have p629_3 := h629c.2.2.2
                linarith only [h352, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p629_1, u2elo3]
              · have p629_0 := h629c.1
                have p629_1 := h629c.2.1
                have p629_2 := h629c.2.2.1
                have p629_3 := h629c.2.2.2
                linarith only [hlam, p629_0]
              · have p629_0 := h629c.1
                have p629_1 := h629c.2.1
                have p629_2 := h629c.2.2.1
                have p629_3 := h629c.2.2.2
                linarith only [h584, hlam, p629_0]
              · have p629_0 := h629c.1
                have p629_1 := h629c.2.1
                have p629_2 := h629c.2.2.1
                have p629_3 := h629c.2.2.2
                linarith only [h3, hlam, p629_0]
              · have p629_0 := h629c.1
                have p629_1 := h629c.2.1
                have p629_2 := h629c.2.2.1
                have p629_3 := h629c.2.2.2
                linarith only [h0, h426, hc12, hlam, hphi, p629_1, u2elo4]
              · have p629_0 := h629c.1
                have p629_1 := h629c.2.1
                have p629_2 := h629c.2.2.1
                have p629_3 := h629c.2.2.2
                linarith only [h0, h4, h426, hc12, hlam, hphi, p629_1, u2elo4]
              · have p629_0 := h629c.1
                have p629_1 := h629c.2.1
                have p629_2 := h629c.2.2.1
                have p629_3 := h629c.2.2.2
                linarith only [h426, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p629_1, u2elo4]
              · have p629_0 := h629c.1
                have p629_1 := h629c.2.1
                have p629_2 := h629c.2.2.1
                have p629_3 := h629c.2.2.2
                linarith only [hlam, p629_0]

set_option maxHeartbeats 3294000 in
set_option maxHeartbeats 3294000 in
theorem r1l7_20_12_13_15_H_I_L_0_L_I_L_R_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc05 := m.hcor 0 5 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0bigk := hb0.1
  have h2elo := hb2.1
  have h5ehi := hb5.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h4 | h4
  · exact r1l7_20_12_13_15_H_I_L_0_L_I_L_R_x0_x0_x0_x0_x0 m hb0 hb2 hb3 hb5 h0 h1 h2 h3 h4
  · exact r1l7_20_12_13_15_H_I_L_0_L_I_L_R_x0_x0_x0_x0_x1 m hb0 hb2 hb3 hb5 h0 h1 h2 h3 h4

set_option maxHeartbeats 3294000 in
set_option maxHeartbeats 3294000 in
theorem r1l7_20_12_13_15_H_I_L_0_L_I_L_R_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc05 := m.hcor 0 5 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0bigk := hb0.1
  have h2elo := hb2.1
  have h5ehi := hb5.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h679 | h679
  · rcases m.htr 0 2 4 (by decide) (by decide) with h680 | h680
    · rcases m.htr 0 2 5 (by decide) (by decide) with h681 | h681
      · linarith only [h0, h3, h681, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h683 | h683
        · rcases m.htr 0 3 5 (by decide) (by decide) with h684 | h684
          · linarith only [h679, h681, h684, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi3]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h686 | h686
            · linarith only [h680, h681, h686, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi4]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h688 | h688
              · linarith only [h681, h688, hc02, hlam, hphi, u2elo1]
              · linarith only [h0, h3, h688, hc12, hlam, hphi, u2elo4]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h691 | h691
          · linarith only [h680, h681, h683, h691, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi3]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h693 | h693
            · linarith only [h680, h681, h693, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi4]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h695 | h695
              · linarith only [h0, h3, h681, h695, hc02, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
              · linarith only [h0, h3, h695, hc12, hlam, hphi, u2elo4]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h698 | h698
      · linarith only [h680, h698, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi2]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h700 | h700
        · linarith only [h679, h680, h700, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h702 | h702
          · linarith only [h679, h680, h702, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi3]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h704 | h704
            · linarith only [h2, h3, h704, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h706 | h706
              · linarith only [h0, h3, h706, hc15, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
              · linarith only [h0, h3, h706, hc12, hlam, hphi, u2elo4]
  · rcases m.htr 0 2 4 (by decide) (by decide) with h709 | h709
    · rcases m.htr 0 2 5 (by decide) (by decide) with h710 | h710
      · linarith only [h679, h710, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h712 | h712
        · rcases m.htr 0 3 5 (by decide) (by decide) with h713 | h713
          · linarith only [h1, h3, h713, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h715 | h715
            · linarith only [h679, h709, h715, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi4]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h717 | h717
              · linarith only [h709, h710, h717, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
              · linarith only [h0, h3, h717, hc12, hlam, hphi, u2elo4]
        · linarith only [h679, h709, h712, hlam]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h721 | h721
      · linarith only [h709, h721, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi2]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h723 | h723
        · rcases m.htr 0 3 5 (by decide) (by decide) with h724 | h724
          · linarith only [h1, h3, h724, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h726 | h726
            · linarith only [h1, h3, h723, h726, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h728 | h728
              · linarith only [h0, h3, h728, hc15, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
              · linarith only [h0, h3, h728, hc12, hlam, hphi, u2elo4]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h731 | h731
          · linarith only [h2, h3, h723, h731, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h733 | h733
            · linarith only [h2, h3, h733, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h735 | h735
              · linarith only [h0, h3, h735, hc15, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
              · linarith only [h0, h3, h735, hc12, hlam, hphi, u2elo4]

set_option maxHeartbeats 3294000 in
set_option maxHeartbeats 3294000 in
theorem r1l7_20_12_13_15_H_I_L_0_L_I_L_R_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc05 := m.hcor 0 5 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0bigk := hb0.1
  have h2elo := hb2.1
  have h5ehi := hb5.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
  · exact r1l7_20_12_13_15_H_I_L_0_L_I_L_R_x0_x0_x0_x0 m hb0 hb2 hb3 hb5 h0 h1 h2 h3
  · exact r1l7_20_12_13_15_H_I_L_0_L_I_L_R_x0_x0_x0_x1 m hb0 hb2 hb3 hb5 h0 h1 h2 h3

set_option maxHeartbeats 3294000 in
set_option maxHeartbeats 3294000 in
theorem r1l7_20_12_13_15_H_I_L_0_L_I_L_R_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc05 := m.hcor 0 5 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0bigk := hb0.1
  have h2elo := hb2.1
  have h5ehi := hb5.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h738 | h738
  · rcases m.htr 0 2 3 (by decide) (by decide) with h739 | h739
    · rcases m.htr 0 2 4 (by decide) (by decide) with h740 | h740
      · linarith only [h0, h2, h740, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h742 | h742
        · linarith only [h740, h742, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi2]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h744 | h744
          · linarith only [h1, h2, h744, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h746 | h746
            · linarith only [h739, h740, h746, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi3]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h748 | h748
              · rcases m.htr 1 2 5 (by decide) (by decide) with h749 | h749
                · linarith only [h742, h749, hc02, hlam, hphi, u2elo1]
                · rcases h0bigk with h751c | h751c | h751c | h751c | h751c | h751c | h751c | h751c | h751c | h751c | h751c | h751c | h751c | h751c | h751c | h751c | h751c | h751c | h751c | h751c | h751c | h751c | h751c | h751c | h751c
                  · have p751_0 := h751c.1
                    have p751_1 := h751c.2.1
                    have p751_2 := h751c.2.2.1
                    have p751_3 := h751c.2.2.2
                    linarith only [hlam, p751_0]
                  · have p751_0 := h751c.1
                    have p751_1 := h751c.2.1
                    have p751_2 := h751c.2.2.1
                    have p751_3 := h751c.2.2.2
                    linarith only [h739, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p751_1]
                  · have p751_0 := h751c.1
                    have p751_1 := h751c.2.1
                    have p751_2 := h751c.2.2.1
                    have p751_3 := h751c.2.2.2
                    linarith only [h2, hc03, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p751_1]
                  · have p751_0 := h751c.1
                    have p751_1 := h751c.2.1
                    have p751_2 := h751c.2.2.1
                    have p751_3 := h751c.2.2.2
                    linarith only [h2, hlam, p751_1]
                  · have p751_0 := h751c.1
                    have p751_1 := h751c.2.1
                    have p751_2 := h751c.2.2.1
                    have p751_3 := h751c.2.2.2
                    linarith only [h2, hc14, hlam, hphi, ht01, ht0b, ht5b, p751_1, u5ehi0]
                  · have p751_0 := h751c.1
                    have p751_1 := h751c.2.1
                    have p751_2 := h751c.2.2.1
                    have p751_3 := h751c.2.2.2
                    linarith only [h0, hlam, p751_0]
                  · have p751_0 := h751c.1
                    have p751_1 := h751c.2.1
                    have p751_2 := h751c.2.2.1
                    have p751_3 := h751c.2.2.2
                    linarith only [hlam, p751_0]
                  · have p751_0 := h751c.1
                    have p751_1 := h751c.2.1
                    have p751_2 := h751c.2.2.1
                    have p751_3 := h751c.2.2.2
                    linarith only [h1, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p751_1, u2elo0]
                  · have p751_0 := h751c.1
                    have p751_1 := h751c.2.1
                    have p751_2 := h751c.2.2.1
                    have p751_3 := h751c.2.2.2
                    linarith only [h740, hlam, p751_1]
                  · have p751_0 := h751c.1
                    have p751_1 := h751c.2.1
                    have p751_2 := h751c.2.2.1
                    have p751_3 := h751c.2.2.2
                    linarith only [h742, hlam, p751_0]
                  · have p751_0 := h751c.1
                    have p751_1 := h751c.2.1
                    have p751_2 := h751c.2.2.1
                    have p751_3 := h751c.2.2.2
                    linarith only [h1, hlam, p751_1]
                  · have p751_0 := h751c.1
                    have p751_1 := h751c.2.1
                    have p751_2 := h751c.2.2.1
                    have p751_3 := h751c.2.2.2
                    linarith only [h739, hlam, p751_1]
                  · have p751_0 := h751c.1
                    have p751_1 := h751c.2.1
                    have p751_2 := h751c.2.2.1
                    have p751_3 := h751c.2.2.2
                    linarith only [hlam, p751_0]
                  · have p751_0 := h751c.1
                    have p751_1 := h751c.2.1
                    have p751_2 := h751c.2.2.1
                    have p751_3 := h751c.2.2.2
                    linarith only [h744, hlam, p751_1]
                  · have p751_0 := h751c.1
                    have p751_1 := h751c.2.1
                    have p751_2 := h751c.2.2.1
                    have p751_3 := h751c.2.2.2
                    linarith only [h746, hlam, p751_1]
                  · have p751_0 := h751c.1
                    have p751_1 := h751c.2.1
                    have p751_2 := h751c.2.2.1
                    have p751_3 := h751c.2.2.2
                    linarith only [h744, hc01, hc34, hlam, hphi, ht12, ht23, p751_1]
                  · have p751_0 := h751c.1
                    have p751_1 := h751c.2.1
                    have p751_2 := h751c.2.2.1
                    have p751_3 := h751c.2.2.2
                    linarith only [h740, hc02, hlam, hphi, p751_1, u2elo3]
                  · have p751_0 := h751c.1
                    have p751_1 := h751c.2.1
                    have p751_2 := h751c.2.2.1
                    have p751_3 := h751c.2.2.2
                    linarith only [h1, h740, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p751_1, u2elo3]
                  · have p751_0 := h751c.1
                    have p751_1 := h751c.2.1
                    have p751_2 := h751c.2.2.1
                    have p751_3 := h751c.2.2.2
                    linarith only [hlam, p751_0]
                  · have p751_0 := h751c.1
                    have p751_1 := h751c.2.1
                    have p751_2 := h751c.2.2.1
                    have p751_3 := h751c.2.2.2
                    linarith only [h739, h740, h742, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p751_1, u2elo3]
                  · have p751_0 := h751c.1
                    have p751_1 := h751c.2.1
                    have p751_2 := h751c.2.2.1
                    have p751_3 := h751c.2.2.2
                    linarith only [h738, hlam, p751_0]
                  · have p751_0 := h751c.1
                    have p751_1 := h751c.2.1
                    have p751_2 := h751c.2.2.1
                    have p751_3 := h751c.2.2.2
                    linarith only [h739, hc05, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p751_1]
                  · have p751_0 := h751c.1
                    have p751_1 := h751c.2.1
                    have p751_2 := h751c.2.2.1
                    have p751_3 := h751c.2.2.2
                    linarith only [h1, h2, h738, hc13, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p751_1]
                  · have p751_0 := h751c.1
                    have p751_1 := h751c.2.1
                    have p751_2 := h751c.2.2.1
                    have p751_3 := h751c.2.2.2
                    linarith only [h748, hlam, p751_1]
                  · have p751_0 := h751c.1
                    have p751_1 := h751c.2.1
                    have p751_2 := h751c.2.2.1
                    have p751_3 := h751c.2.2.2
                    linarith only [hlam, p751_0]
              · linarith only [h2, h738, h748, hlam]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h778 | h778
      · linarith only [h2, h738, h739, h778, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi1]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h780 | h780
        · linarith only [h739, h780, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h782 | h782
          · linarith only [h1, h2, h782, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h784 | h784
            · rcases m.htr 0 4 5 (by decide) (by decide) with h785 | h785
              · rcases m.htr 1 2 5 (by decide) (by decide) with h786 | h786
                · linarith only [h780, h786, hc02, hlam, hphi, u2elo1]
                · rcases h0bigk with h788c | h788c | h788c | h788c | h788c | h788c | h788c | h788c | h788c | h788c | h788c | h788c | h788c | h788c | h788c | h788c | h788c | h788c | h788c | h788c | h788c | h788c | h788c | h788c | h788c
                  · have p788_0 := h788c.1
                    have p788_1 := h788c.2.1
                    have p788_2 := h788c.2.2.1
                    have p788_3 := h788c.2.2.2
                    linarith only [hlam, p788_0]
                  · have p788_0 := h788c.1
                    have p788_1 := h788c.2.1
                    have p788_2 := h788c.2.2.1
                    have p788_3 := h788c.2.2.2
                    linarith only [h0, h2, h778, hc12, hlam, hphi, p788_1, u2elo3]
                  · have p788_0 := h788c.1
                    have p788_1 := h788c.2.1
                    have p788_2 := h788c.2.2.1
                    have p788_3 := h788c.2.2.2
                    linarith only [h2, h778, h784, hlam, hphi, ht01, ht0b, ht12, ht5b, p788_1, u2elo3, u5ehi3]
                  · have p788_0 := h788c.1
                    have p788_1 := h788c.2.1
                    have p788_2 := h788c.2.2.1
                    have p788_3 := h788c.2.2.2
                    linarith only [h2, hlam, p788_1]
                  · have p788_0 := h788c.1
                    have p788_1 := h788c.2.1
                    have p788_2 := h788c.2.2.1
                    have p788_3 := h788c.2.2.2
                    linarith only [h2, h778, hlam, hphi, ht01, ht0b, ht12, ht5b, p788_1, u2elo3, u5ehi0]
                  · have p788_0 := h788c.1
                    have p788_1 := h788c.2.1
                    have p788_2 := h788c.2.2.1
                    have p788_3 := h788c.2.2.2
                    linarith only [h0, hlam, p788_0]
                  · have p788_0 := h788c.1
                    have p788_1 := h788c.2.1
                    have p788_2 := h788c.2.2.1
                    have p788_3 := h788c.2.2.2
                    linarith only [hlam, p788_0]
                  · have p788_0 := h788c.1
                    have p788_1 := h788c.2.1
                    have p788_2 := h788c.2.2.1
                    have p788_3 := h788c.2.2.2
                    linarith only [h739, hlam, p788_0]
                  · have p788_0 := h788c.1
                    have p788_1 := h788c.2.1
                    have p788_2 := h788c.2.2.1
                    have p788_3 := h788c.2.2.2
                    linarith only [h778, hlam, p788_1]
                  · have p788_0 := h788c.1
                    have p788_1 := h788c.2.1
                    have p788_2 := h788c.2.2.1
                    have p788_3 := h788c.2.2.2
                    linarith only [h780, hlam, p788_0]
                  · have p788_0 := h788c.1
                    have p788_1 := h788c.2.1
                    have p788_2 := h788c.2.2.1
                    have p788_3 := h788c.2.2.2
                    linarith only [h1, hlam, p788_1]
                  · have p788_0 := h788c.1
                    have p788_1 := h788c.2.1
                    have p788_2 := h788c.2.2.1
                    have p788_3 := h788c.2.2.2
                    linarith only [h0, h782, hc12, hc34, hlam, hphi, ht23, p788_1]
                  · have p788_0 := h788c.1
                    have p788_1 := h788c.2.1
                    have p788_2 := h788c.2.2.1
                    have p788_3 := h788c.2.2.2
                    linarith only [hlam, p788_0]
                  · have p788_0 := h788c.1
                    have p788_1 := h788c.2.1
                    have p788_2 := h788c.2.2.1
                    have p788_3 := h788c.2.2.2
                    linarith only [h782, hlam, p788_1]
                  · have p788_0 := h788c.1
                    have p788_1 := h788c.2.1
                    have p788_2 := h788c.2.2.1
                    have p788_3 := h788c.2.2.2
                    linarith only [h1, h2, h738, h778, hlam, hphi, ht01, ht0b, ht12, ht5b, p788_1, u2elo3, u5ehi1]
                  · have p788_0 := h788c.1
                    have p788_1 := h788c.2.1
                    have p788_2 := h788c.2.2.1
                    have p788_3 := h788c.2.2.2
                    linarith only [h778, hc01, hlam, hphi, ht12, p788_1, u2elo3]
                  · have p788_0 := h788c.1
                    have p788_1 := h788c.2.1
                    have p788_2 := h788c.2.2.1
                    have p788_3 := h788c.2.2.2
                    linarith only [h0, h778, hc12, hlam, hphi, p788_1, u2elo3]
                  · have p788_0 := h788c.1
                    have p788_1 := h788c.2.1
                    have p788_2 := h788c.2.2.1
                    have p788_3 := h788c.2.2.2
                    linarith only [h778, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p788_1, u2elo3]
                  · have p788_0 := h788c.1
                    have p788_1 := h788c.2.1
                    have p788_2 := h788c.2.2.1
                    have p788_3 := h788c.2.2.2
                    linarith only [hlam, p788_0]
                  · have p788_0 := h788c.1
                    have p788_1 := h788c.2.1
                    have p788_2 := h788c.2.2.1
                    have p788_3 := h788c.2.2.2
                    linarith only [h738, h778, hlam, hphi, ht01, ht0b, ht12, ht5b, p788_1, u2elo3, u5ehi1]
                  · have p788_0 := h788c.1
                    have p788_1 := h788c.2.1
                    have p788_2 := h788c.2.2.1
                    have p788_3 := h788c.2.2.2
                    linarith only [h738, hlam, p788_0]
                  · have p788_0 := h788c.1
                    have p788_1 := h788c.2.1
                    have p788_2 := h788c.2.2.1
                    have p788_3 := h788c.2.2.2
                    linarith only [h0, h2, h738, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p788_1]
                  · have p788_0 := h788c.1
                    have p788_1 := h788c.2.1
                    have p788_2 := h788c.2.2.1
                    have p788_3 := h788c.2.2.2
                    linarith only [h784, hlam, p788_0]
                  · have p788_0 := h788c.1
                    have p788_1 := h788c.2.1
                    have p788_2 := h788c.2.2.1
                    have p788_3 := h788c.2.2.2
                    linarith only [h785, hlam, p788_1]
                  · have p788_0 := h788c.1
                    have p788_1 := h788c.2.1
                    have p788_2 := h788c.2.2.1
                    have p788_3 := h788c.2.2.2
                    linarith only [hlam, p788_0]
              · linarith only [h1, h2, h784, h785, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h815 | h815
              · rcases m.htr 1 2 5 (by decide) (by decide) with h816 | h816
                · linarith only [h0, h2, h780, h816, hc14, hlam, hphi, ht01, ht0b, ht5b, u5ehi0]
                · rcases h0bigk with h818c | h818c | h818c | h818c | h818c | h818c | h818c | h818c | h818c | h818c | h818c | h818c | h818c | h818c | h818c | h818c | h818c | h818c | h818c | h818c | h818c | h818c | h818c | h818c | h818c
                  · have p818_0 := h818c.1
                    have p818_1 := h818c.2.1
                    have p818_2 := h818c.2.2.1
                    have p818_3 := h818c.2.2.2
                    linarith only [hlam, p818_0]
                  · have p818_0 := h818c.1
                    have p818_1 := h818c.2.1
                    have p818_2 := h818c.2.2.1
                    have p818_3 := h818c.2.2.2
                    linarith only [h0, h2, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p818_1]
                  · have p818_0 := h818c.1
                    have p818_1 := h818c.2.1
                    have p818_2 := h818c.2.2.1
                    have p818_3 := h818c.2.2.2
                    linarith only [h0, h2, h739, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p818_1]
                  · have p818_0 := h818c.1
                    have p818_1 := h818c.2.1
                    have p818_2 := h818c.2.2.1
                    have p818_3 := h818c.2.2.2
                    linarith only [h2, hlam, p818_1]
                  · have p818_0 := h818c.1
                    have p818_1 := h818c.2.1
                    have p818_2 := h818c.2.2.1
                    have p818_3 := h818c.2.2.2
                    linarith only [h2, h738, h778, hlam, hphi, ht01, ht0b, ht12, ht5b, p818_1, u2elo3, u5ehi1]
                  · have p818_0 := h818c.1
                    have p818_1 := h818c.2.1
                    have p818_2 := h818c.2.2.1
                    have p818_3 := h818c.2.2.2
                    linarith only [h0, hlam, p818_0]
                  · have p818_0 := h818c.1
                    have p818_1 := h818c.2.1
                    have p818_2 := h818c.2.2.1
                    have p818_3 := h818c.2.2.2
                    linarith only [hlam, p818_0]
                  · have p818_0 := h818c.1
                    have p818_1 := h818c.2.1
                    have p818_2 := h818c.2.2.1
                    have p818_3 := h818c.2.2.2
                    linarith only [h739, hlam, p818_0]
                  · have p818_0 := h818c.1
                    have p818_1 := h818c.2.1
                    have p818_2 := h818c.2.2.1
                    have p818_3 := h818c.2.2.2
                    linarith only [h778, hlam, p818_1]
                  · have p818_0 := h818c.1
                    have p818_1 := h818c.2.1
                    have p818_2 := h818c.2.2.1
                    have p818_3 := h818c.2.2.2
                    linarith only [h780, hlam, p818_0]
                  · have p818_0 := h818c.1
                    have p818_1 := h818c.2.1
                    have p818_2 := h818c.2.2.1
                    have p818_3 := h818c.2.2.2
                    linarith only [h1, hlam, p818_1]
                  · have p818_0 := h818c.1
                    have p818_1 := h818c.2.1
                    have p818_2 := h818c.2.2.1
                    have p818_3 := h818c.2.2.2
                    linarith only [h0, h784, hc12, hc35, hlam, hphi, ht23, p818_1]
                  · have p818_0 := h818c.1
                    have p818_1 := h818c.2.1
                    have p818_2 := h818c.2.2.1
                    have p818_3 := h818c.2.2.2
                    linarith only [hlam, p818_0]
                  · have p818_0 := h818c.1
                    have p818_1 := h818c.2.1
                    have p818_2 := h818c.2.2.1
                    have p818_3 := h818c.2.2.2
                    linarith only [h782, hlam, p818_1]
                  · have p818_0 := h818c.1
                    have p818_1 := h818c.2.1
                    have p818_2 := h818c.2.2.1
                    have p818_3 := h818c.2.2.2
                    linarith only [h784, hlam, p818_1]
                  · have p818_0 := h818c.1
                    have p818_1 := h818c.2.1
                    have p818_2 := h818c.2.2.1
                    have p818_3 := h818c.2.2.2
                    linarith only [h778, hc01, hlam, hphi, ht12, p818_1, u2elo3]
                  · have p818_0 := h818c.1
                    have p818_1 := h818c.2.1
                    have p818_2 := h818c.2.2.1
                    have p818_3 := h818c.2.2.2
                    linarith only [h0, h778, hc12, hlam, hphi, p818_1, u2elo3]
                  · have p818_0 := h818c.1
                    have p818_1 := h818c.2.1
                    have p818_2 := h818c.2.2.1
                    have p818_3 := h818c.2.2.2
                    linarith only [h778, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p818_1, u2elo3]
                  · have p818_0 := h818c.1
                    have p818_1 := h818c.2.1
                    have p818_2 := h818c.2.2.1
                    have p818_3 := h818c.2.2.2
                    linarith only [hlam, p818_0]
                  · have p818_0 := h818c.1
                    have p818_1 := h818c.2.1
                    have p818_2 := h818c.2.2.1
                    have p818_3 := h818c.2.2.2
                    linarith only [h738, h778, hlam, hphi, ht01, ht0b, ht12, ht5b, p818_1, u2elo3, u5ehi1]
                  · have p818_0 := h818c.1
                    have p818_1 := h818c.2.1
                    have p818_2 := h818c.2.2.1
                    have p818_3 := h818c.2.2.2
                    linarith only [h738, hlam, p818_0]
                  · have p818_0 := h818c.1
                    have p818_1 := h818c.2.1
                    have p818_2 := h818c.2.2.1
                    have p818_3 := h818c.2.2.2
                    linarith only [h0, h2, h738, h778, hc12, hlam, hphi, p818_1, u2elo3]
                  · have p818_0 := h818c.1
                    have p818_1 := h818c.2.1
                    have p818_2 := h818c.2.2.1
                    have p818_3 := h818c.2.2.2
                    linarith only [h0, h2, h738, h739, h778, hc12, hlam, hphi, p818_1, u2elo3]
                  · have p818_0 := h818c.1
                    have p818_1 := h818c.2.1
                    have p818_2 := h818c.2.2.1
                    have p818_3 := h818c.2.2.2
                    linarith only [h815, hlam, p818_1]
                  · have p818_0 := h818c.1
                    have p818_1 := h818c.2.1
                    have p818_2 := h818c.2.2.1
                    have p818_3 := h818c.2.2.2
                    linarith only [hlam, p818_0]
              · linarith only [h2, h738, h815, hlam]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h845 | h845
    · rcases m.htr 0 2 4 (by decide) (by decide) with h846 | h846
      · linarith only [h0, h2, h846, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h848 | h848
        · linarith only [h846, h848, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi2]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h850 | h850
          · linarith only [h1, h2, h850, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h852 | h852
            · linarith only [h845, h846, h852, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi3]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h854 | h854
              · rcases m.htr 1 2 5 (by decide) (by decide) with h855 | h855
                · linarith only [h848, h855, hc02, hlam, hphi, u2elo1]
                · linarith only [h0, h738, h855, hc12, hlam, hphi, u2elo4]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h858 | h858
                · linarith only [h0, h738, h858, hc15, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                · linarith only [h0, h738, h858, hc12, hlam, hphi, u2elo4]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h861 | h861
      · linarith only [h0, h2, h845, h861, hc12, hlam, hphi, u2elo2]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h863 | h863
        · linarith only [h861, h863, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi2]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h865 | h865
          · linarith only [h1, h2, h865, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h867 | h867
            · linarith only [h1, h738, h867, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h869 | h869
              · rcases m.htr 1 2 5 (by decide) (by decide) with h870 | h870
                · linarith only [h0, h738, h870, hc15, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                · linarith only [h0, h738, h870, hc12, hlam, hphi, u2elo4]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h873 | h873
                · linarith only [h0, h2, h869, h873, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi2]
                · linarith only [h0, h738, h873, hc12, hlam, hphi, u2elo4]

set_option maxHeartbeats 3294000 in
set_option maxHeartbeats 3294000 in
theorem r1l7_20_12_13_15_H_I_L_0_L_I_L_R_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc05 := m.hcor 0 5 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0bigk := hb0.1
  have h2elo := hb2.1
  have h5ehi := hb5.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
  · exact r1l7_20_12_13_15_H_I_L_0_L_I_L_R_x0_x0_x0 m hb0 hb2 hb3 hb5 h0 h1 h2
  · exact r1l7_20_12_13_15_H_I_L_0_L_I_L_R_x0_x0_x1 m hb0 hb2 hb3 hb5 h0 h1 h2

end R2N4
