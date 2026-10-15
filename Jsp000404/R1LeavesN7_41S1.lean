import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_41S0

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6812000 in
theorem r1l7_11_12_25_L_0_L_I_H_I_x0_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h1 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h2 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h3 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc05 := m.hcor 0 5 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1elo := hb1.1
  have h5bigk := hb5.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  rcases m.htr 1 3 5 (by decide) (by decide) with h406 | h406
  · rcases m.htr 1 4 5 (by decide) (by decide) with h407 | h407
    · rcases m.htr 2 3 4 (by decide) (by decide) with h408 | h408
      · rcases m.htr 2 3 5 (by decide) (by decide) with h409 | h409
        · rcases m.htr 2 4 5 (by decide) (by decide) with h410 | h410
          · rcases m.htr 3 4 5 (by decide) (by decide) with h411 | h411
            · rcases h5bigk with h412c | h412c | h412c | h412c | h412c | h412c | h412c | h412c | h412c | h412c | h412c | h412c | h412c | h412c | h412c | h412c | h412c | h412c | h412c | h412c | h412c | h412c | h412c | h412c | h412c
              · have p412_0 := h412c.1
                have p412_1 := h412c.2.1
                have p412_2 := h412c.2.2.1
                have p412_3 := h412c.2.2.2
                linarith only [hlam, p412_0]
              · have p412_0 := h412c.1
                have p412_1 := h412c.2.1
                have p412_2 := h412c.2.2.1
                have p412_3 := h412c.2.2.2
                linarith only [h0, hc15, hlam, hphi, ht01, ht0b, ht5b, p412_1, u1elo0]
              · have p412_0 := h412c.1
                have p412_1 := h412c.2.1
                have p412_2 := h412c.2.2.1
                have p412_3 := h412c.2.2.2
                linarith only [h0, h3, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p412_1, u1elo0]
              · have p412_0 := h412c.1
                have p412_1 := h412c.2.1
                have p412_2 := h412c.2.2.1
                have p412_3 := h412c.2.2.2
                linarith only [h0, h411, hc45, hlam, hphi, ht01, ht0b, ht5b, p412_1, u1elo0]
              · have p412_0 := h412c.1
                have p412_1 := h412c.2.1
                have p412_2 := h412c.2.2.1
                have p412_3 := h412c.2.2.2
                linarith only [h0, hc45, hlam, hphi, ht01, ht0b, ht5b, p412_1, u1elo0]
              · have p412_0 := h412c.1
                have p412_1 := h412c.2.1
                have p412_2 := h412c.2.2.1
                have p412_3 := h412c.2.2.2
                linarith only [h0, hlam, p412_0]
              · have p412_0 := h412c.1
                have p412_1 := h412c.2.1
                have p412_2 := h412c.2.2.1
                have p412_3 := h412c.2.2.2
                linarith only [hlam, p412_0]
              · have p412_0 := h412c.1
                have p412_1 := h412c.2.1
                have p412_2 := h412c.2.2.1
                have p412_3 := h412c.2.2.2
                linarith only [h3, hlam, p412_0]
              · have p412_0 := h412c.1
                have p412_1 := h412c.2.1
                have p412_2 := h412c.2.2.1
                have p412_3 := h412c.2.2.2
                linarith only [h411, hc45, hlam, hphi, ht01, ht0b, ht5b, p412_1, u1elo4]
              · have p412_0 := h412c.1
                have p412_1 := h412c.2.1
                have p412_2 := h412c.2.2.1
                have p412_3 := h412c.2.2.2
                linarith only [h406, hc45, hlam, hphi, ht01, ht0b, ht5b, p412_1, u1elo2]
              · have p412_0 := h412c.1
                have p412_1 := h412c.2.1
                have p412_2 := h412c.2.2.1
                have p412_3 := h412c.2.2.2
                linarith only [h1, hlam, p412_1]
              · have p412_0 := h412c.1
                have p412_1 := h412c.2.1
                have p412_2 := h412c.2.2.1
                have p412_3 := h412c.2.2.2
                linarith only [h1, hc02, hc15, hlam, hphi, ht0b, ht5b, p412_1]
              · have p412_0 := h412c.1
                have p412_1 := h412c.2.1
                have p412_2 := h412c.2.2.1
                have p412_3 := h412c.2.2.2
                linarith only [hlam, p412_0]
              · have p412_0 := h412c.1
                have p412_1 := h412c.2.1
                have p412_2 := h412c.2.2.1
                have p412_3 := h412c.2.2.2
                linarith only [h1, h411, hc02, hc45, hlam, hphi, ht0b, ht5b, p412_1]
              · have p412_0 := h412c.1
                have p412_1 := h412c.2.1
                have p412_2 := h412c.2.2.1
                have p412_3 := h412c.2.2.2
                linarith only [h0, h1, hc45, hlam, hphi, ht01, ht0b, ht5b, p412_1, u1elo0]
              · have p412_0 := h412c.1
                have p412_1 := h412c.2.1
                have p412_2 := h412c.2.2.1
                have p412_3 := h412c.2.2.2
                linarith only [h0, h3, hc12, hc35, hlam, hphi, ht23, p412_1]
              · have p412_0 := h412c.1
                have p412_1 := h412c.2.1
                have p412_2 := h412c.2.2.1
                have p412_3 := h412c.2.2.2
                linarith only [h406, hlam, p412_1]
              · have p412_0 := h412c.1
                have p412_1 := h412c.2.1
                have p412_2 := h412c.2.2.1
                have p412_3 := h412c.2.2.2
                linarith only [h409, hlam, p412_0]
              · have p412_0 := h412c.1
                have p412_1 := h412c.2.1
                have p412_2 := h412c.2.2.1
                have p412_3 := h412c.2.2.2
                linarith only [hlam, p412_0]
              · have p412_0 := h412c.1
                have p412_1 := h412c.2.1
                have p412_2 := h412c.2.2.1
                have p412_3 := h412c.2.2.2
                linarith only [h406, hc45, hlam, hphi, ht01, ht0b, ht5b, p412_1, u1elo4]
              · have p412_0 := h412c.1
                have p412_1 := h412c.2.1
                have p412_2 := h412c.2.2.1
                have p412_3 := h412c.2.2.2
                linarith only [h2, hlam, p412_1]
              · have p412_0 := h412c.1
                have p412_1 := h412c.2.1
                have p412_2 := h412c.2.2.1
                have p412_3 := h412c.2.2.2
                linarith only [h407, hlam, p412_1]
              · have p412_0 := h412c.1
                have p412_1 := h412c.2.1
                have p412_2 := h412c.2.2.1
                have p412_3 := h412c.2.2.2
                linarith only [h410, hlam, p412_1]
              · have p412_0 := h412c.1
                have p412_1 := h412c.2.1
                have p412_2 := h412c.2.2.1
                have p412_3 := h412c.2.2.2
                linarith only [h411, hlam, p412_1]
              · have p412_0 := h412c.1
                have p412_1 := h412c.2.1
                have p412_2 := h412c.2.2.1
                have p412_3 := h412c.2.2.2
                linarith only [hlam, p412_0]
            · rcases h5bigk with h438c | h438c | h438c | h438c | h438c | h438c | h438c | h438c | h438c | h438c | h438c | h438c | h438c | h438c | h438c | h438c | h438c | h438c | h438c | h438c | h438c | h438c | h438c | h438c | h438c
              · have p438_0 := h438c.1
                have p438_1 := h438c.2.1
                have p438_2 := h438c.2.2.1
                have p438_3 := h438c.2.2.2
                linarith only [hlam, p438_0]
              · have p438_0 := h438c.1
                have p438_1 := h438c.2.1
                have p438_2 := h438c.2.2.1
                have p438_3 := h438c.2.2.2
                linarith only [h0, hc15, hlam, hphi, ht01, ht0b, ht5b, p438_1, u1elo0]
              · have p438_0 := h438c.1
                have p438_1 := h438c.2.1
                have p438_2 := h438c.2.2.1
                have p438_3 := h438c.2.2.2
                linarith only [h0, h3, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p438_1, u1elo0]
              · have p438_0 := h438c.1
                have p438_1 := h438c.2.1
                have p438_2 := h438c.2.2.1
                have p438_3 := h438c.2.2.2
                linarith only [h0, hc35, hlam, hphi, ht01, ht0b, ht5b, p438_1, u1elo0]
              · have p438_0 := h438c.1
                have p438_1 := h438c.2.1
                have p438_2 := h438c.2.2.1
                have p438_3 := h438c.2.2.2
                linarith only [h0, h411, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p438_1, u1elo0]
              · have p438_0 := h438c.1
                have p438_1 := h438c.2.1
                have p438_2 := h438c.2.2.1
                have p438_3 := h438c.2.2.2
                linarith only [h0, hlam, p438_0]
              · have p438_0 := h438c.1
                have p438_1 := h438c.2.1
                have p438_2 := h438c.2.2.1
                have p438_3 := h438c.2.2.2
                linarith only [hlam, p438_0]
              · have p438_0 := h438c.1
                have p438_1 := h438c.2.1
                have p438_2 := h438c.2.2.1
                have p438_3 := h438c.2.2.2
                linarith only [h3, hlam, p438_0]
              · have p438_0 := h438c.1
                have p438_1 := h438c.2.1
                have p438_2 := h438c.2.2.1
                have p438_3 := h438c.2.2.2
                linarith only [hc35, hlam, hphi, ht01, ht0b, ht5b, p438_1, u1elo4]
              · have p438_0 := h438c.1
                have p438_1 := h438c.2.1
                have p438_2 := h438c.2.2.1
                have p438_3 := h438c.2.2.2
                linarith only [h0, h411, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p438_1, u1elo0]
              · have p438_0 := h438c.1
                have p438_1 := h438c.2.1
                have p438_2 := h438c.2.2.1
                have p438_3 := h438c.2.2.2
                linarith only [h1, hlam, p438_1]
              · have p438_0 := h438c.1
                have p438_1 := h438c.2.1
                have p438_2 := h438c.2.2.1
                have p438_3 := h438c.2.2.2
                linarith only [h1, hc02, hc15, hlam, hphi, ht0b, ht5b, p438_1]
              · have p438_0 := h438c.1
                have p438_1 := h438c.2.1
                have p438_2 := h438c.2.2.1
                have p438_3 := h438c.2.2.2
                linarith only [hlam, p438_0]
              · have p438_0 := h438c.1
                have p438_1 := h438c.2.1
                have p438_2 := h438c.2.2.1
                have p438_3 := h438c.2.2.2
                linarith only [h0, h1, hc35, hlam, hphi, ht01, ht0b, ht5b, p438_1, u1elo0]
              · have p438_0 := h438c.1
                have p438_1 := h438c.2.1
                have p438_2 := h438c.2.2.1
                have p438_3 := h438c.2.2.2
                linarith only [h0, h1, h411, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p438_1, u1elo0]
              · have p438_0 := h438c.1
                have p438_1 := h438c.2.1
                have p438_2 := h438c.2.2.1
                have p438_3 := h438c.2.2.2
                linarith only [h0, h407, h411, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p438_1]
              · have p438_0 := h438c.1
                have p438_1 := h438c.2.1
                have p438_2 := h438c.2.2.1
                have p438_3 := h438c.2.2.2
                linarith only [h406, hlam, p438_1]
              · have p438_0 := h438c.1
                have p438_1 := h438c.2.1
                have p438_2 := h438c.2.2.1
                have p438_3 := h438c.2.2.2
                linarith only [h409, hlam, p438_0]
              · have p438_0 := h438c.1
                have p438_1 := h438c.2.1
                have p438_2 := h438c.2.2.1
                have p438_3 := h438c.2.2.2
                linarith only [hlam, p438_0]
              · have p438_0 := h438c.1
                have p438_1 := h438c.2.1
                have p438_2 := h438c.2.2.1
                have p438_3 := h438c.2.2.2
                linarith only [h411, hlam, p438_0]
              · have p438_0 := h438c.1
                have p438_1 := h438c.2.1
                have p438_2 := h438c.2.2.1
                have p438_3 := h438c.2.2.2
                linarith only [h2, hlam, p438_1]
              · have p438_0 := h438c.1
                have p438_1 := h438c.2.1
                have p438_2 := h438c.2.2.1
                have p438_3 := h438c.2.2.2
                linarith only [h407, hlam, p438_1]
              · have p438_0 := h438c.1
                have p438_1 := h438c.2.1
                have p438_2 := h438c.2.2.1
                have p438_3 := h438c.2.2.2
                linarith only [h410, hlam, p438_1]
              · have p438_0 := h438c.1
                have p438_1 := h438c.2.1
                have p438_2 := h438c.2.2.1
                have p438_3 := h438c.2.2.2
                linarith only [h407, hc35, hlam, hphi, ht01, ht0b, ht5b, p438_1, u1elo4]
              · have p438_0 := h438c.1
                have p438_1 := h438c.2.1
                have p438_2 := h438c.2.2.1
                have p438_3 := h438c.2.2.2
                linarith only [hlam, p438_0]
          · linarith only [h3, h407, h410, hlam]
        · linarith only [h0, h406, h408, h409, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
      · rcases m.htr 2 3 5 (by decide) (by decide) with h466 | h466
        · rcases m.htr 2 4 5 (by decide) (by decide) with h467 | h467
          · rcases m.htr 3 4 5 (by decide) (by decide) with h468 | h468
            · rcases h5bigk with h469c | h469c | h469c | h469c | h469c | h469c | h469c | h469c | h469c | h469c | h469c | h469c | h469c | h469c | h469c | h469c | h469c | h469c | h469c | h469c | h469c | h469c | h469c | h469c | h469c
              · have p469_0 := h469c.1
                have p469_1 := h469c.2.1
                have p469_2 := h469c.2.2.1
                have p469_3 := h469c.2.2.2
                linarith only [hlam, p469_0]
              · have p469_0 := h469c.1
                have p469_1 := h469c.2.1
                have p469_2 := h469c.2.2.1
                have p469_3 := h469c.2.2.2
                linarith only [h0, hc15, hlam, hphi, ht01, ht0b, ht5b, p469_1, u1elo0]
              · have p469_0 := h469c.1
                have p469_1 := h469c.2.1
                have p469_2 := h469c.2.2.1
                have p469_3 := h469c.2.2.2
                linarith only [h0, h3, hc15, hlam, hphi, ht01, ht0b, ht5b, p469_1, u1elo0]
              · have p469_0 := h469c.1
                have p469_1 := h469c.2.1
                have p469_2 := h469c.2.2.1
                have p469_3 := h469c.2.2.2
                linarith only [h0, hc35, hlam, hphi, ht01, ht0b, ht5b, p469_1, u1elo0]
              · have p469_0 := h469c.1
                have p469_1 := h469c.2.1
                have p469_2 := h469c.2.2.1
                have p469_3 := h469c.2.2.2
                linarith only [h0, hc45, hlam, hphi, ht01, ht0b, ht5b, p469_1, u1elo0]
              · have p469_0 := h469c.1
                have p469_1 := h469c.2.1
                have p469_2 := h469c.2.2.1
                have p469_3 := h469c.2.2.2
                linarith only [h0, hlam, p469_0]
              · have p469_0 := h469c.1
                have p469_1 := h469c.2.1
                have p469_2 := h469c.2.2.1
                have p469_3 := h469c.2.2.2
                linarith only [hlam, p469_0]
              · have p469_0 := h469c.1
                have p469_1 := h469c.2.1
                have p469_2 := h469c.2.2.1
                have p469_3 := h469c.2.2.2
                linarith only [h3, hlam, p469_0]
              · have p469_0 := h469c.1
                have p469_1 := h469c.2.1
                have p469_2 := h469c.2.2.1
                have p469_3 := h469c.2.2.2
                linarith only [h468, hc45, hlam, hphi, ht01, ht0b, ht5b, p469_1, u1elo4]
              · have p469_0 := h469c.1
                have p469_1 := h469c.2.1
                have p469_2 := h469c.2.2.1
                have p469_3 := h469c.2.2.2
                linarith only [hc45, hlam, hphi, ht01, ht0b, ht5b, p469_1, u1elo4]
              · have p469_0 := h469c.1
                have p469_1 := h469c.2.1
                have p469_2 := h469c.2.2.1
                have p469_3 := h469c.2.2.2
                linarith only [h1, hlam, p469_1]
              · have p469_0 := h469c.1
                have p469_1 := h469c.2.1
                have p469_2 := h469c.2.2.1
                have p469_3 := h469c.2.2.2
                linarith only [h1, hc02, hc15, hlam, hphi, ht0b, ht5b, p469_1]
              · have p469_0 := h469c.1
                have p469_1 := h469c.2.1
                have p469_2 := h469c.2.2.1
                have p469_3 := h469c.2.2.2
                linarith only [hlam, p469_0]
              · have p469_0 := h469c.1
                have p469_1 := h469c.2.1
                have p469_2 := h469c.2.2.1
                have p469_3 := h469c.2.2.2
                linarith only [h408, h466, h468, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p469_1]
              · have p469_0 := h469c.1
                have p469_1 := h469c.2.1
                have p469_2 := h469c.2.2.1
                have p469_3 := h469c.2.2.2
                linarith only [h408, h466, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p469_1]
              · have p469_0 := h469c.1
                have p469_1 := h469c.2.1
                have p469_2 := h469c.2.2.1
                have p469_3 := h469c.2.2.2
                linarith only [h0, h3, hc12, hc35, hlam, hphi, ht23, p469_1]
              · have p469_0 := h469c.1
                have p469_1 := h469c.2.1
                have p469_2 := h469c.2.2.1
                have p469_3 := h469c.2.2.2
                linarith only [h406, hlam, p469_1]
              · have p469_0 := h469c.1
                have p469_1 := h469c.2.1
                have p469_2 := h469c.2.2.1
                have p469_3 := h469c.2.2.2
                linarith only [h466, hlam, p469_0]
              · have p469_0 := h469c.1
                have p469_1 := h469c.2.1
                have p469_2 := h469c.2.2.1
                have p469_3 := h469c.2.2.2
                linarith only [hlam, p469_0]
              · have p469_0 := h469c.1
                have p469_1 := h469c.2.1
                have p469_2 := h469c.2.2.1
                have p469_3 := h469c.2.2.2
                linarith only [h406, hc45, hlam, hphi, ht01, ht0b, ht5b, p469_1, u1elo4]
              · have p469_0 := h469c.1
                have p469_1 := h469c.2.1
                have p469_2 := h469c.2.2.1
                have p469_3 := h469c.2.2.2
                linarith only [h2, hlam, p469_1]
              · have p469_0 := h469c.1
                have p469_1 := h469c.2.1
                have p469_2 := h469c.2.2.1
                have p469_3 := h469c.2.2.2
                linarith only [h407, hlam, p469_1]
              · have p469_0 := h469c.1
                have p469_1 := h469c.2.1
                have p469_2 := h469c.2.2.1
                have p469_3 := h469c.2.2.2
                linarith only [h467, hlam, p469_1]
              · have p469_0 := h469c.1
                have p469_1 := h469c.2.1
                have p469_2 := h469c.2.2.1
                have p469_3 := h469c.2.2.2
                linarith only [h468, hlam, p469_1]
              · have p469_0 := h469c.1
                have p469_1 := h469c.2.1
                have p469_2 := h469c.2.2.1
                have p469_3 := h469c.2.2.2
                linarith only [hlam, p469_0]
            · linarith only [h2, h408, h466, h468, hc04, hc35, hlam, hphi, ht0b, ht5b]
          · linarith only [h0, h3, h407, h408, h466, h467, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
        · linarith only [h3, h406, h466, hlam]
    · rcases m.htr 2 3 4 (by decide) (by decide) with h498 | h498
      · rcases m.htr 2 3 5 (by decide) (by decide) with h499 | h499
        · rcases m.htr 2 4 5 (by decide) (by decide) with h500 | h500
          · rcases m.htr 3 4 5 (by decide) (by decide) with h501 | h501
            · linarith only [h406, h407, h501, hlam]
            · rcases h5bigk with h503c | h503c | h503c | h503c | h503c | h503c | h503c | h503c | h503c | h503c | h503c | h503c | h503c | h503c | h503c | h503c | h503c | h503c | h503c | h503c | h503c | h503c | h503c | h503c | h503c
              · have p503_0 := h503c.1
                have p503_1 := h503c.2.1
                have p503_2 := h503c.2.2.1
                have p503_3 := h503c.2.2.2
                linarith only [hlam, p503_0]
              · have p503_0 := h503c.1
                have p503_1 := h503c.2.1
                have p503_2 := h503c.2.2.1
                have p503_3 := h503c.2.2.2
                linarith only [h0, hc15, hlam, hphi, ht01, ht0b, ht5b, p503_1, u1elo0]
              · have p503_0 := h503c.1
                have p503_1 := h503c.2.1
                have p503_2 := h503c.2.2.1
                have p503_3 := h503c.2.2.2
                linarith only [h0, h407, h500, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p503_1, u1elo0]
              · have p503_0 := h503c.1
                have p503_1 := h503c.2.1
                have p503_2 := h503c.2.2.1
                have p503_3 := h503c.2.2.2
                linarith only [h0, h501, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p503_1, u1elo0]
              · have p503_0 := h503c.1
                have p503_1 := h503c.2.1
                have p503_2 := h503c.2.2.1
                have p503_3 := h503c.2.2.2
                linarith only [h0, h407, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p503_1, u1elo0]
              · have p503_0 := h503c.1
                have p503_1 := h503c.2.1
                have p503_2 := h503c.2.2.1
                have p503_3 := h503c.2.2.2
                linarith only [h0, hlam, p503_0]
              · have p503_0 := h503c.1
                have p503_1 := h503c.2.1
                have p503_2 := h503c.2.2.1
                have p503_3 := h503c.2.2.2
                linarith only [hlam, p503_0]
              · have p503_0 := h503c.1
                have p503_1 := h503c.2.1
                have p503_2 := h503c.2.2.1
                have p503_3 := h503c.2.2.2
                linarith only [h3, hlam, p503_0]
              · have p503_0 := h503c.1
                have p503_1 := h503c.2.1
                have p503_2 := h503c.2.2.1
                have p503_3 := h503c.2.2.2
                linarith only [h501, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p503_1, u1elo4]
              · have p503_0 := h503c.1
                have p503_1 := h503c.2.1
                have p503_2 := h503c.2.2.1
                have p503_3 := h503c.2.2.2
                linarith only [h407, hlam, p503_0]
              · have p503_0 := h503c.1
                have p503_1 := h503c.2.1
                have p503_2 := h503c.2.2.1
                have p503_3 := h503c.2.2.2
                linarith only [h1, hlam, p503_1]
              · have p503_0 := h503c.1
                have p503_1 := h503c.2.1
                have p503_2 := h503c.2.2.1
                have p503_3 := h503c.2.2.2
                linarith only [h1, hc02, hc15, hlam, hphi, ht0b, ht5b, p503_1]
              · have p503_0 := h503c.1
                have p503_1 := h503c.2.1
                have p503_2 := h503c.2.2.1
                have p503_3 := h503c.2.2.2
                linarith only [hlam, p503_0]
              · have p503_0 := h503c.1
                have p503_1 := h503c.2.1
                have p503_2 := h503c.2.2.1
                have p503_3 := h503c.2.2.2
                linarith only [h0, h1, h501, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p503_1, u1elo0]
              · have p503_0 := h503c.1
                have p503_1 := h503c.2.1
                have p503_2 := h503c.2.2.1
                have p503_3 := h503c.2.2.2
                linarith only [h0, h1, h407, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p503_1, u1elo0]
              · have p503_0 := h503c.1
                have p503_1 := h503c.2.1
                have p503_2 := h503c.2.2.1
                have p503_3 := h503c.2.2.2
                linarith only [h0, h3, hc12, hc35, hlam, hphi, ht23, p503_1]
              · have p503_0 := h503c.1
                have p503_1 := h503c.2.1
                have p503_2 := h503c.2.2.1
                have p503_3 := h503c.2.2.2
                linarith only [h406, hlam, p503_1]
              · have p503_0 := h503c.1
                have p503_1 := h503c.2.1
                have p503_2 := h503c.2.2.1
                have p503_3 := h503c.2.2.2
                linarith only [h499, hlam, p503_0]
              · have p503_0 := h503c.1
                have p503_1 := h503c.2.1
                have p503_2 := h503c.2.2.1
                have p503_3 := h503c.2.2.2
                linarith only [hlam, p503_0]
              · have p503_0 := h503c.1
                have p503_1 := h503c.2.1
                have p503_2 := h503c.2.2.1
                have p503_3 := h503c.2.2.2
                linarith only [h501, hlam, p503_0]
              · have p503_0 := h503c.1
                have p503_1 := h503c.2.1
                have p503_2 := h503c.2.2.1
                have p503_3 := h503c.2.2.2
                linarith only [h2, hlam, p503_1]
              · have p503_0 := h503c.1
                have p503_1 := h503c.2.1
                have p503_2 := h503c.2.2.1
                have p503_3 := h503c.2.2.2
                linarith only [h3, hc12, hc45, hlam, hphi, ht23, ht34, p503_1]
              · have p503_0 := h503c.1
                have p503_1 := h503c.2.1
                have p503_2 := h503c.2.2.1
                have p503_3 := h503c.2.2.2
                linarith only [h500, hlam, p503_1]
              · have p503_0 := h503c.1
                have p503_1 := h503c.2.1
                have p503_2 := h503c.2.2.1
                have p503_3 := h503c.2.2.2
                linarith only [h0, h1, h500, hc35, hlam, hphi, ht01, ht0b, ht5b, p503_1, u1elo0]
              · have p503_0 := h503c.1
                have p503_1 := h503c.2.1
                have p503_2 := h503c.2.2.1
                have p503_3 := h503c.2.2.2
                linarith only [hlam, p503_0]
          · rcases m.htr 3 4 5 (by decide) (by decide) with h529 | h529
            · linarith only [h3, h498, h500, h529, hc12, hc23, hlam, hphi]
            · rcases h5bigk with h531c | h531c | h531c | h531c | h531c | h531c | h531c | h531c | h531c | h531c | h531c | h531c | h531c | h531c | h531c | h531c | h531c | h531c | h531c | h531c | h531c | h531c | h531c | h531c | h531c
              · have p531_0 := h531c.1
                have p531_1 := h531c.2.1
                have p531_2 := h531c.2.2.1
                have p531_3 := h531c.2.2.2
                linarith only [hlam, p531_0]
              · have p531_0 := h531c.1
                have p531_1 := h531c.2.1
                have p531_2 := h531c.2.2.1
                have p531_3 := h531c.2.2.2
                linarith only [h0, h3, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p531_1, u1elo0]
              · have p531_0 := h531c.1
                have p531_1 := h531c.2.1
                have p531_2 := h531c.2.2.1
                have p531_3 := h531c.2.2.2
                linarith only [h0, h3, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p531_1, u1elo0]
              · have p531_0 := h531c.1
                have p531_1 := h531c.2.1
                have p531_2 := h531c.2.2.1
                have p531_3 := h531c.2.2.2
                linarith only [h0, h529, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p531_1, u1elo0]
              · have p531_0 := h531c.1
                have p531_1 := h531c.2.1
                have p531_2 := h531c.2.2.1
                have p531_3 := h531c.2.2.2
                linarith only [h0, h3, h500, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p531_1, u1elo0]
              · have p531_0 := h531c.1
                have p531_1 := h531c.2.1
                have p531_2 := h531c.2.2.1
                have p531_3 := h531c.2.2.2
                linarith only [h0, hlam, p531_0]
              · have p531_0 := h531c.1
                have p531_1 := h531c.2.1
                have p531_2 := h531c.2.2.1
                have p531_3 := h531c.2.2.2
                linarith only [hlam, p531_0]
              · have p531_0 := h531c.1
                have p531_1 := h531c.2.1
                have p531_2 := h531c.2.2.1
                have p531_3 := h531c.2.2.2
                linarith only [h3, hlam, p531_0]
              · have p531_0 := h531c.1
                have p531_1 := h531c.2.1
                have p531_2 := h531c.2.2.1
                have p531_3 := h531c.2.2.2
                linarith only [h529, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p531_1, u1elo4]
              · have p531_0 := h531c.1
                have p531_1 := h531c.2.1
                have p531_2 := h531c.2.2.1
                have p531_3 := h531c.2.2.2
                linarith only [h407, hlam, p531_0]
              · have p531_0 := h531c.1
                have p531_1 := h531c.2.1
                have p531_2 := h531c.2.2.1
                have p531_3 := h531c.2.2.2
                linarith only [h1, hlam, p531_1]
              · have p531_0 := h531c.1
                have p531_1 := h531c.2.1
                have p531_2 := h531c.2.2.1
                have p531_3 := h531c.2.2.2
                linarith only [h1, hc02, hc15, hlam, hphi, ht0b, ht5b, p531_1]
              · have p531_0 := h531c.1
                have p531_1 := h531c.2.1
                have p531_2 := h531c.2.2.1
                have p531_3 := h531c.2.2.2
                linarith only [hlam, p531_0]
              · have p531_0 := h531c.1
                have p531_1 := h531c.2.1
                have p531_2 := h531c.2.2.1
                have p531_3 := h531c.2.2.2
                linarith only [h0, h2, h500, h529, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p531_1, u1elo0]
              · have p531_0 := h531c.1
                have p531_1 := h531c.2.1
                have p531_2 := h531c.2.2.1
                have p531_3 := h531c.2.2.2
                linarith only [h500, hlam, p531_0]
              · have p531_0 := h531c.1
                have p531_1 := h531c.2.1
                have p531_2 := h531c.2.2.1
                have p531_3 := h531c.2.2.2
                linarith only [h2, h500, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p531_1]
              · have p531_0 := h531c.1
                have p531_1 := h531c.2.1
                have p531_2 := h531c.2.2.1
                have p531_3 := h531c.2.2.2
                linarith only [h406, hlam, p531_1]
              · have p531_0 := h531c.1
                have p531_1 := h531c.2.1
                have p531_2 := h531c.2.2.1
                have p531_3 := h531c.2.2.2
                linarith only [h499, hlam, p531_0]
              · have p531_0 := h531c.1
                have p531_1 := h531c.2.1
                have p531_2 := h531c.2.2.1
                have p531_3 := h531c.2.2.2
                linarith only [hlam, p531_0]
              · have p531_0 := h531c.1
                have p531_1 := h531c.2.1
                have p531_2 := h531c.2.2.1
                have p531_3 := h531c.2.2.2
                linarith only [h529, hlam, p531_0]
              · have p531_0 := h531c.1
                have p531_1 := h531c.2.1
                have p531_2 := h531c.2.2.1
                have p531_3 := h531c.2.2.2
                linarith only [h2, hlam, p531_1]
              · have p531_0 := h531c.1
                have p531_1 := h531c.2.1
                have p531_2 := h531c.2.2.1
                have p531_3 := h531c.2.2.2
                linarith only [h0, h2, h3, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p531_1, u1elo0]
              · have p531_0 := h531c.1
                have p531_1 := h531c.2.1
                have p531_2 := h531c.2.2.1
                have p531_3 := h531c.2.2.2
                linarith only [h0, h2, hc25, hlam, hphi, ht01, ht0b, ht5b, p531_1, u1elo0]
              · have p531_0 := h531c.1
                have p531_1 := h531c.2.1
                have p531_2 := h531c.2.2.1
                have p531_3 := h531c.2.2.2
                linarith only [h0, h2, hc35, hlam, hphi, ht01, ht0b, ht5b, p531_1, u1elo0]
              · have p531_0 := h531c.1
                have p531_1 := h531c.2.1
                have p531_2 := h531c.2.2.1
                have p531_3 := h531c.2.2.2
                linarith only [hlam, p531_0]
        · linarith only [h0, h406, h498, h499, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
      · rcases m.htr 2 3 5 (by decide) (by decide) with h558 | h558
        · rcases m.htr 2 4 5 (by decide) (by decide) with h559 | h559
          · rcases m.htr 3 4 5 (by decide) (by decide) with h560 | h560
            · linarith only [h406, h407, h560, hlam]
            · linarith only [h1, h498, h558, h559, h560, hc02, hc35, hlam, hphi, ht0b, ht5b]
          · linarith only [h498, h558, h559, hlam]
        · linarith only [h3, h406, h558, hlam]
  · rcases m.htr 1 4 5 (by decide) (by decide) with h565 | h565
    · rcases m.htr 2 3 4 (by decide) (by decide) with h566 | h566
      · rcases m.htr 2 3 5 (by decide) (by decide) with h567 | h567
        · rcases m.htr 2 4 5 (by decide) (by decide) with h568 | h568
          · rcases m.htr 3 4 5 (by decide) (by decide) with h569 | h569
            · rcases h5bigk with h570c | h570c | h570c | h570c | h570c | h570c | h570c | h570c | h570c | h570c | h570c | h570c | h570c | h570c | h570c | h570c | h570c | h570c | h570c | h570c | h570c | h570c | h570c | h570c | h570c
              · have p570_0 := h570c.1
                have p570_1 := h570c.2.1
                have p570_2 := h570c.2.2.1
                have p570_3 := h570c.2.2.2
                linarith only [hlam, p570_0]
              · have p570_0 := h570c.1
                have p570_1 := h570c.2.1
                have p570_2 := h570c.2.2.1
                have p570_3 := h570c.2.2.2
                linarith only [h0, hc15, hlam, hphi, ht01, ht0b, ht5b, p570_1, u1elo0]
              · have p570_0 := h570c.1
                have p570_1 := h570c.2.1
                have p570_2 := h570c.2.2.1
                have p570_3 := h570c.2.2.2
                linarith only [h0, h406, h567, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p570_1, u1elo0]
              · have p570_0 := h570c.1
                have p570_1 := h570c.2.1
                have p570_2 := h570c.2.2.1
                have p570_3 := h570c.2.2.2
                linarith only [h0, h406, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p570_1, u1elo0]
              · have p570_0 := h570c.1
                have p570_1 := h570c.2.1
                have p570_2 := h570c.2.2.1
                have p570_3 := h570c.2.2.2
                linarith only [h0, hc45, hlam, hphi, ht01, ht0b, ht5b, p570_1, u1elo0]
              · have p570_0 := h570c.1
                have p570_1 := h570c.2.1
                have p570_2 := h570c.2.2.1
                have p570_3 := h570c.2.2.2
                linarith only [h0, hlam, p570_0]
              · have p570_0 := h570c.1
                have p570_1 := h570c.2.1
                have p570_2 := h570c.2.2.1
                have p570_3 := h570c.2.2.2
                linarith only [hlam, p570_0]
              · have p570_0 := h570c.1
                have p570_1 := h570c.2.1
                have p570_2 := h570c.2.2.1
                have p570_3 := h570c.2.2.2
                linarith only [h3, hlam, p570_0]
              · have p570_0 := h570c.1
                have p570_1 := h570c.2.1
                have p570_2 := h570c.2.2.1
                have p570_3 := h570c.2.2.2
                linarith only [h406, hlam, p570_0]
              · have p570_0 := h570c.1
                have p570_1 := h570c.2.1
                have p570_2 := h570c.2.2.1
                have p570_3 := h570c.2.2.2
                linarith only [hc45, hlam, hphi, ht01, ht0b, ht5b, p570_1, u1elo4]
              · have p570_0 := h570c.1
                have p570_1 := h570c.2.1
                have p570_2 := h570c.2.2.1
                have p570_3 := h570c.2.2.2
                linarith only [h1, hlam, p570_1]
              · have p570_0 := h570c.1
                have p570_1 := h570c.2.1
                have p570_2 := h570c.2.2.1
                have p570_3 := h570c.2.2.2
                linarith only [h1, hc02, hc15, hlam, hphi, ht0b, ht5b, p570_1]
              · have p570_0 := h570c.1
                have p570_1 := h570c.2.1
                have p570_2 := h570c.2.2.1
                have p570_3 := h570c.2.2.2
                linarith only [hlam, p570_0]
              · have p570_0 := h570c.1
                have p570_1 := h570c.2.1
                have p570_2 := h570c.2.2.1
                have p570_3 := h570c.2.2.2
                linarith only [h0, h1, h406, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p570_1, u1elo0]
              · have p570_0 := h570c.1
                have p570_1 := h570c.2.1
                have p570_2 := h570c.2.2.1
                have p570_3 := h570c.2.2.2
                linarith only [h0, h1, hc45, hlam, hphi, ht01, ht0b, ht5b, p570_1, u1elo0]
              · have p570_0 := h570c.1
                have p570_1 := h570c.2.1
                have p570_2 := h570c.2.2.1
                have p570_3 := h570c.2.2.2
                linarith only [h0, h3, h569, hc12, hc34, hlam, hphi, ht23, p570_1]
              · have p570_0 := h570c.1
                have p570_1 := h570c.2.1
                have p570_2 := h570c.2.2.1
                have p570_3 := h570c.2.2.2
                linarith only [h3, h569, hc12, hc34, hlam, hphi, ht23, p570_1]
              · have p570_0 := h570c.1
                have p570_1 := h570c.2.1
                have p570_2 := h570c.2.2.1
                have p570_3 := h570c.2.2.2
                linarith only [h567, hlam, p570_0]
              · have p570_0 := h570c.1
                have p570_1 := h570c.2.1
                have p570_2 := h570c.2.2.1
                have p570_3 := h570c.2.2.2
                linarith only [hlam, p570_0]
              · have p570_0 := h570c.1
                have p570_1 := h570c.2.1
                have p570_2 := h570c.2.2.1
                have p570_3 := h570c.2.2.2
                linarith only [h0, h1, h567, hc45, hlam, hphi, ht01, ht0b, ht5b, p570_1, u1elo0]
              · have p570_0 := h570c.1
                have p570_1 := h570c.2.1
                have p570_2 := h570c.2.2.1
                have p570_3 := h570c.2.2.2
                linarith only [h2, hlam, p570_1]
              · have p570_0 := h570c.1
                have p570_1 := h570c.2.1
                have p570_2 := h570c.2.2.1
                have p570_3 := h570c.2.2.2
                linarith only [h565, hlam, p570_1]
              · have p570_0 := h570c.1
                have p570_1 := h570c.2.1
                have p570_2 := h570c.2.2.1
                have p570_3 := h570c.2.2.2
                linarith only [h568, hlam, p570_1]
              · have p570_0 := h570c.1
                have p570_1 := h570c.2.1
                have p570_2 := h570c.2.2.1
                have p570_3 := h570c.2.2.2
                linarith only [h569, hlam, p570_1]
              · have p570_0 := h570c.1
                have p570_1 := h570c.2.1
                have p570_2 := h570c.2.2.1
                have p570_3 := h570c.2.2.2
                linarith only [hlam, p570_0]
            · linarith only [h406, h565, h569, hlam]
          · linarith only [h3, h565, h568, hlam]
        · rcases m.htr 2 4 5 (by decide) (by decide) with h598 | h598
          · linarith only [h566, h567, h598, hlam]
          · linarith only [h3, h565, h598, hlam]
      · rcases m.htr 2 3 5 (by decide) (by decide) with h601 | h601
        · linarith only [h406, h566, h601, hc13, hc34, hlam, hphi]
        · rcases m.htr 2 4 5 (by decide) (by decide) with h603 | h603
          · rcases m.htr 3 4 5 (by decide) (by decide) with h604 | h604
            · rcases h5bigk with h605c | h605c | h605c | h605c | h605c | h605c | h605c | h605c | h605c | h605c | h605c | h605c | h605c | h605c | h605c | h605c | h605c | h605c | h605c | h605c | h605c | h605c | h605c | h605c | h605c
              · have p605_0 := h605c.1
                have p605_1 := h605c.2.1
                have p605_2 := h605c.2.2.1
                have p605_3 := h605c.2.2.2
                linarith only [hlam, p605_0]
              · have p605_0 := h605c.1
                have p605_1 := h605c.2.1
                have p605_2 := h605c.2.2.1
                have p605_3 := h605c.2.2.2
                linarith only [h0, hc15, hlam, hphi, ht01, ht0b, ht5b, p605_1, u1elo0]
              · have p605_0 := h605c.1
                have p605_1 := h605c.2.1
                have p605_2 := h605c.2.2.1
                have p605_3 := h605c.2.2.2
                linarith only [h0, h601, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p605_1, u1elo0]
              · have p605_0 := h605c.1
                have p605_1 := h605c.2.1
                have p605_2 := h605c.2.2.1
                have p605_3 := h605c.2.2.2
                linarith only [h0, h3, h601, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p605_1, u1elo0]
              · have p605_0 := h605c.1
                have p605_1 := h605c.2.1
                have p605_2 := h605c.2.2.1
                have p605_3 := h605c.2.2.2
                linarith only [h0, hc45, hlam, hphi, ht01, ht0b, ht5b, p605_1, u1elo0]
              · have p605_0 := h605c.1
                have p605_1 := h605c.2.1
                have p605_2 := h605c.2.2.1
                have p605_3 := h605c.2.2.2
                linarith only [h0, hlam, p605_0]
              · have p605_0 := h605c.1
                have p605_1 := h605c.2.1
                have p605_2 := h605c.2.2.1
                have p605_3 := h605c.2.2.2
                linarith only [hlam, p605_0]
              · have p605_0 := h605c.1
                have p605_1 := h605c.2.1
                have p605_2 := h605c.2.2.1
                have p605_3 := h605c.2.2.2
                linarith only [h3, hlam, p605_0]
              · have p605_0 := h605c.1
                have p605_1 := h605c.2.1
                have p605_2 := h605c.2.2.1
                have p605_3 := h605c.2.2.2
                linarith only [h406, hlam, p605_0]
              · have p605_0 := h605c.1
                have p605_1 := h605c.2.1
                have p605_2 := h605c.2.2.1
                have p605_3 := h605c.2.2.2
                linarith only [hc45, hlam, hphi, ht01, ht0b, ht5b, p605_1, u1elo4]
              · have p605_0 := h605c.1
                have p605_1 := h605c.2.1
                have p605_2 := h605c.2.2.1
                have p605_3 := h605c.2.2.2
                linarith only [h1, hlam, p605_1]
              · have p605_0 := h605c.1
                have p605_1 := h605c.2.1
                have p605_2 := h605c.2.2.1
                have p605_3 := h605c.2.2.2
                linarith only [h1, hc02, hc15, hlam, hphi, ht0b, ht5b, p605_1]
              · have p605_0 := h605c.1
                have p605_1 := h605c.2.1
                have p605_2 := h605c.2.2.1
                have p605_3 := h605c.2.2.2
                linarith only [hlam, p605_0]
              · have p605_0 := h605c.1
                have p605_1 := h605c.2.1
                have p605_2 := h605c.2.2.1
                have p605_3 := h605c.2.2.2
                linarith only [h601, hlam, p605_1]
              · have p605_0 := h605c.1
                have p605_1 := h605c.2.1
                have p605_2 := h605c.2.2.1
                have p605_3 := h605c.2.2.2
                linarith only [h0, h1, hc45, hlam, hphi, ht01, ht0b, ht5b, p605_1, u1elo0]
              · have p605_0 := h605c.1
                have p605_1 := h605c.2.1
                have p605_2 := h605c.2.2.1
                have p605_3 := h605c.2.2.2
                linarith only [h0, h3, hc12, hc35, hlam, hphi, ht23, p605_1]
              · have p605_0 := h605c.1
                have p605_1 := h605c.2.1
                have p605_2 := h605c.2.2.1
                have p605_3 := h605c.2.2.2
                linarith only [h3, hc12, hc35, hlam, hphi, ht23, p605_1]
              · have p605_0 := h605c.1
                have p605_1 := h605c.2.1
                have p605_2 := h605c.2.2.1
                have p605_3 := h605c.2.2.2
                linarith only [h3, hc12, hc35, hlam, hphi, ht23, p605_1]
              · have p605_0 := h605c.1
                have p605_1 := h605c.2.1
                have p605_2 := h605c.2.2.1
                have p605_3 := h605c.2.2.2
                linarith only [hlam, p605_0]
              · have p605_0 := h605c.1
                have p605_1 := h605c.2.1
                have p605_2 := h605c.2.2.1
                have p605_3 := h605c.2.2.2
                rcases p605_3 (m.d 0 5) (by simp) with h625 | h625
                · linarith only [h0, h625, hc45, hlam, hphi, ht01, ht0b, ht5b, p605_1, u1elo0]
                · linarith only [h2, h625, hlam]
              · have p605_0 := h605c.1
                have p605_1 := h605c.2.1
                have p605_2 := h605c.2.2.1
                have p605_3 := h605c.2.2.2
                linarith only [h2, hlam, p605_1]
              · have p605_0 := h605c.1
                have p605_1 := h605c.2.1
                have p605_2 := h605c.2.2.1
                have p605_3 := h605c.2.2.2
                linarith only [h565, hlam, p605_1]
              · have p605_0 := h605c.1
                have p605_1 := h605c.2.1
                have p605_2 := h605c.2.2.1
                have p605_3 := h605c.2.2.2
                linarith only [h603, hlam, p605_1]
              · have p605_0 := h605c.1
                have p605_1 := h605c.2.1
                have p605_2 := h605c.2.2.1
                have p605_3 := h605c.2.2.2
                linarith only [h604, hlam, p605_1]
              · have p605_0 := h605c.1
                have p605_1 := h605c.2.1
                have p605_2 := h605c.2.2.1
                have p605_3 := h605c.2.2.2
                linarith only [hlam, p605_0]
            · linarith only [h0, h565, h566, h604, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
          · linarith only [h3, h565, h603, hlam]
    · rcases m.htr 2 3 4 (by decide) (by decide) with h635 | h635
      · rcases m.htr 2 3 5 (by decide) (by decide) with h636 | h636
        · rcases m.htr 2 4 5 (by decide) (by decide) with h637 | h637
          · rcases m.htr 3 4 5 (by decide) (by decide) with h638 | h638
            · rcases h5bigk with h639c | h639c | h639c | h639c | h639c | h639c | h639c | h639c | h639c | h639c | h639c | h639c | h639c | h639c | h639c | h639c | h639c | h639c | h639c | h639c | h639c | h639c | h639c | h639c | h639c
              · have p639_0 := h639c.1
                have p639_1 := h639c.2.1
                have p639_2 := h639c.2.2.1
                have p639_3 := h639c.2.2.2
                linarith only [hlam, p639_0]
              · have p639_0 := h639c.1
                have p639_1 := h639c.2.1
                have p639_2 := h639c.2.2.1
                have p639_3 := h639c.2.2.2
                linarith only [h0, hc15, hlam, hphi, ht01, ht0b, ht5b, p639_1, u1elo0]
              · have p639_0 := h639c.1
                have p639_1 := h639c.2.1
                have p639_2 := h639c.2.2.1
                have p639_3 := h639c.2.2.2
                linarith only [h0, hc25, hlam, hphi, ht01, ht0b, ht5b, p639_1, u1elo0]
              · have p639_0 := h639c.1
                have p639_1 := h639c.2.1
                have p639_2 := h639c.2.2.1
                have p639_3 := h639c.2.2.2
                linarith only [h0, h565, h638, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p639_1, u1elo0]
              · have p639_0 := h639c.1
                have p639_1 := h639c.2.1
                have p639_2 := h639c.2.2.1
                have p639_3 := h639c.2.2.2
                linarith only [h0, h565, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p639_1, u1elo0]
              · have p639_0 := h639c.1
                have p639_1 := h639c.2.1
                have p639_2 := h639c.2.2.1
                have p639_3 := h639c.2.2.2
                linarith only [h0, hlam, p639_0]
              · have p639_0 := h639c.1
                have p639_1 := h639c.2.1
                have p639_2 := h639c.2.2.1
                have p639_3 := h639c.2.2.2
                linarith only [hlam, p639_0]
              · have p639_0 := h639c.1
                have p639_1 := h639c.2.1
                have p639_2 := h639c.2.2.1
                have p639_3 := h639c.2.2.2
                linarith only [h3, hlam, p639_0]
              · have p639_0 := h639c.1
                have p639_1 := h639c.2.1
                have p639_2 := h639c.2.2.1
                have p639_3 := h639c.2.2.2
                linarith only [h406, hlam, p639_0]
              · have p639_0 := h639c.1
                have p639_1 := h639c.2.1
                have p639_2 := h639c.2.2.1
                have p639_3 := h639c.2.2.2
                linarith only [h565, hlam, p639_0]
              · have p639_0 := h639c.1
                have p639_1 := h639c.2.1
                have p639_2 := h639c.2.2.1
                have p639_3 := h639c.2.2.2
                linarith only [h1, hlam, p639_1]
              · have p639_0 := h639c.1
                have p639_1 := h639c.2.1
                have p639_2 := h639c.2.2.1
                have p639_3 := h639c.2.2.2
                linarith only [h3, hc12, hc25, hlam, hphi, p639_1]
              · have p639_0 := h639c.1
                have p639_1 := h639c.2.1
                have p639_2 := h639c.2.2.1
                have p639_3 := h639c.2.2.2
                linarith only [hlam, p639_0]
              · have p639_0 := h639c.1
                have p639_1 := h639c.2.1
                have p639_2 := h639c.2.2.1
                have p639_3 := h639c.2.2.2
                linarith only [h0, h1, h565, h638, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p639_1, u1elo0]
              · have p639_0 := h639c.1
                have p639_1 := h639c.2.1
                have p639_2 := h639c.2.2.1
                have p639_3 := h639c.2.2.2
                linarith only [h0, h1, h565, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p639_1, u1elo0]
              · have p639_0 := h639c.1
                have p639_1 := h639c.2.1
                have p639_2 := h639c.2.2.1
                have p639_3 := h639c.2.2.2
                linarith only [h0, h3, hc12, hc35, hlam, hphi, ht23, p639_1]
              · have p639_0 := h639c.1
                have p639_1 := h639c.2.1
                have p639_2 := h639c.2.2.1
                have p639_3 := h639c.2.2.2
                linarith only [h0, h1, h3, h636, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p639_1, u1elo0]
              · have p639_0 := h639c.1
                have p639_1 := h639c.2.1
                have p639_2 := h639c.2.2.1
                have p639_3 := h639c.2.2.2
                linarith only [h636, hlam, p639_0]
              · have p639_0 := h639c.1
                have p639_1 := h639c.2.1
                have p639_2 := h639c.2.2.1
                have p639_3 := h639c.2.2.2
                linarith only [hlam, p639_0]
              · have p639_0 := h639c.1
                have p639_1 := h639c.2.1
                have p639_2 := h639c.2.2.1
                have p639_3 := h639c.2.2.2
                linarith only [h565, h635, h638, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p639_1]
              · have p639_0 := h639c.1
                have p639_1 := h639c.2.1
                have p639_2 := h639c.2.2.1
                have p639_3 := h639c.2.2.2
                linarith only [h2, hlam, p639_1]
              · have p639_0 := h639c.1
                have p639_1 := h639c.2.1
                have p639_2 := h639c.2.2.1
                have p639_3 := h639c.2.2.2
                linarith only [h3, hc12, hc45, hlam, hphi, ht23, ht34, p639_1]
              · have p639_0 := h639c.1
                have p639_1 := h639c.2.1
                have p639_2 := h639c.2.2.1
                have p639_3 := h639c.2.2.2
                linarith only [h637, hlam, p639_1]
              · have p639_0 := h639c.1
                have p639_1 := h639c.2.1
                have p639_2 := h639c.2.2.1
                have p639_3 := h639c.2.2.2
                linarith only [h638, hlam, p639_1]
              · have p639_0 := h639c.1
                have p639_1 := h639c.2.1
                have p639_2 := h639c.2.2.1
                have p639_3 := h639c.2.2.2
                linarith only [hlam, p639_0]
            · rcases h5bigk with h665c | h665c | h665c | h665c | h665c | h665c | h665c | h665c | h665c | h665c | h665c | h665c | h665c | h665c | h665c | h665c | h665c | h665c | h665c | h665c | h665c | h665c | h665c | h665c | h665c
              · have p665_0 := h665c.1
                have p665_1 := h665c.2.1
                have p665_2 := h665c.2.2.1
                have p665_3 := h665c.2.2.2
                linarith only [hlam, p665_0]
              · have p665_0 := h665c.1
                have p665_1 := h665c.2.1
                have p665_2 := h665c.2.2.1
                have p665_3 := h665c.2.2.2
                linarith only [h0, h3, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p665_1, u1elo0]
              · have p665_0 := h665c.1
                have p665_1 := h665c.2.1
                have p665_2 := h665c.2.2.1
                have p665_3 := h665c.2.2.2
                linarith only [h0, hc25, hlam, hphi, ht01, ht0b, ht5b, p665_1, u1elo0]
              · have p665_0 := h665c.1
                have p665_1 := h665c.2.1
                have p665_2 := h665c.2.2.1
                have p665_3 := h665c.2.2.2
                linarith only [h0, h406, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p665_1, u1elo0]
              · have p665_0 := h665c.1
                have p665_1 := h665c.2.1
                have p665_2 := h665c.2.2.1
                have p665_3 := h665c.2.2.2
                linarith only [h0, h406, h638, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p665_1, u1elo0]
              · have p665_0 := h665c.1
                have p665_1 := h665c.2.1
                have p665_2 := h665c.2.2.1
                have p665_3 := h665c.2.2.2
                linarith only [h0, hlam, p665_0]
              · have p665_0 := h665c.1
                have p665_1 := h665c.2.1
                have p665_2 := h665c.2.2.1
                have p665_3 := h665c.2.2.2
                linarith only [hlam, p665_0]
              · have p665_0 := h665c.1
                have p665_1 := h665c.2.1
                have p665_2 := h665c.2.2.1
                have p665_3 := h665c.2.2.2
                linarith only [h3, hlam, p665_0]
              · have p665_0 := h665c.1
                have p665_1 := h665c.2.1
                have p665_2 := h665c.2.2.1
                have p665_3 := h665c.2.2.2
                linarith only [h406, hlam, p665_0]
              · have p665_0 := h665c.1
                have p665_1 := h665c.2.1
                have p665_2 := h665c.2.2.1
                have p665_3 := h665c.2.2.2
                linarith only [h565, hlam, p665_0]
              · have p665_0 := h665c.1
                have p665_1 := h665c.2.1
                have p665_2 := h665c.2.2.1
                have p665_3 := h665c.2.2.2
                linarith only [h1, hlam, p665_1]
              · have p665_0 := h665c.1
                have p665_1 := h665c.2.1
                have p665_2 := h665c.2.2.1
                have p665_3 := h665c.2.2.2
                linarith only [h3, hc12, hc25, hlam, hphi, p665_1]
              · have p665_0 := h665c.1
                have p665_1 := h665c.2.1
                have p665_2 := h665c.2.2.1
                have p665_3 := h665c.2.2.2
                linarith only [hlam, p665_0]
              · have p665_0 := h665c.1
                have p665_1 := h665c.2.1
                have p665_2 := h665c.2.2.1
                have p665_3 := h665c.2.2.2
                linarith only [h0, h1, h406, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p665_1, u1elo0]
              · have p665_0 := h665c.1
                have p665_1 := h665c.2.1
                have p665_2 := h665c.2.2.1
                have p665_3 := h665c.2.2.2
                linarith only [h0, h1, h406, h638, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p665_1, u1elo0]
              · have p665_0 := h665c.1
                have p665_1 := h665c.2.1
                have p665_2 := h665c.2.2.1
                have p665_3 := h665c.2.2.2
                linarith only [h0, h3, h638, hc12, hc45, hlam, hphi, ht23, ht34, p665_1]
              · have p665_0 := h665c.1
                have p665_1 := h665c.2.1
                have p665_2 := h665c.2.2.1
                have p665_3 := h665c.2.2.2
                linarith only [h0, h2, h3, h638, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p665_1, u1elo0]
              · have p665_0 := h665c.1
                have p665_1 := h665c.2.1
                have p665_2 := h665c.2.2.1
                have p665_3 := h665c.2.2.2
                linarith only [h636, hlam, p665_0]
              · have p665_0 := h665c.1
                have p665_1 := h665c.2.1
                have p665_2 := h665c.2.2.1
                have p665_3 := h665c.2.2.2
                linarith only [hlam, p665_0]
              · have p665_0 := h665c.1
                have p665_1 := h665c.2.1
                have p665_2 := h665c.2.2.1
                have p665_3 := h665c.2.2.2
                linarith only [h638, hlam, p665_0]
              · have p665_0 := h665c.1
                have p665_1 := h665c.2.1
                have p665_2 := h665c.2.2.1
                have p665_3 := h665c.2.2.2
                linarith only [h2, hlam, p665_1]
              · have p665_0 := h665c.1
                have p665_1 := h665c.2.1
                have p665_2 := h665c.2.2.1
                have p665_3 := h665c.2.2.2
                linarith only [h0, h2, h3, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p665_1, u1elo0]
              · have p665_0 := h665c.1
                have p665_1 := h665c.2.1
                have p665_2 := h665c.2.2.1
                have p665_3 := h665c.2.2.2
                linarith only [h637, hlam, p665_1]
              · have p665_0 := h665c.1
                have p665_1 := h665c.2.1
                have p665_2 := h665c.2.2.1
                have p665_3 := h665c.2.2.2
                linarith only [h0, h2, hc35, hlam, hphi, ht01, ht0b, ht5b, p665_1, u1elo0]
              · have p665_0 := h665c.1
                have p665_1 := h665c.2.1
                have p665_2 := h665c.2.2.1
                have p665_3 := h665c.2.2.2
                linarith only [hlam, p665_0]
          · rcases m.htr 3 4 5 (by decide) (by decide) with h691 | h691
            · linarith only [h3, h635, h637, h691, hc12, hc23, hlam, hphi]
            · rcases h5bigk with h693c | h693c | h693c | h693c | h693c | h693c | h693c | h693c | h693c | h693c | h693c | h693c | h693c | h693c | h693c | h693c | h693c | h693c | h693c | h693c | h693c | h693c | h693c | h693c | h693c
              · have p693_0 := h693c.1
                have p693_1 := h693c.2.1
                have p693_2 := h693c.2.2.1
                have p693_3 := h693c.2.2.2
                linarith only [hlam, p693_0]
              · have p693_0 := h693c.1
                have p693_1 := h693c.2.1
                have p693_2 := h693c.2.2.1
                have p693_3 := h693c.2.2.2
                linarith only [h0, h3, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p693_1, u1elo0]
              · have p693_0 := h693c.1
                have p693_1 := h693c.2.1
                have p693_2 := h693c.2.2.1
                have p693_3 := h693c.2.2.2
                linarith only [h0, h3, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p693_1, u1elo0]
              · have p693_0 := h693c.1
                have p693_1 := h693c.2.1
                have p693_2 := h693c.2.2.1
                have p693_3 := h693c.2.2.2
                linarith only [h0, h406, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p693_1, u1elo0]
              · have p693_0 := h693c.1
                have p693_1 := h693c.2.1
                have p693_2 := h693c.2.2.1
                have p693_3 := h693c.2.2.2
                linarith only [h0, hc45, hlam, hphi, ht01, ht0b, ht5b, p693_1, u1elo0]
              · have p693_0 := h693c.1
                have p693_1 := h693c.2.1
                have p693_2 := h693c.2.2.1
                have p693_3 := h693c.2.2.2
                linarith only [h0, hlam, p693_0]
              · have p693_0 := h693c.1
                have p693_1 := h693c.2.1
                have p693_2 := h693c.2.2.1
                have p693_3 := h693c.2.2.2
                linarith only [hlam, p693_0]
              · have p693_0 := h693c.1
                have p693_1 := h693c.2.1
                have p693_2 := h693c.2.2.1
                have p693_3 := h693c.2.2.2
                linarith only [h3, hlam, p693_0]
              · have p693_0 := h693c.1
                have p693_1 := h693c.2.1
                have p693_2 := h693c.2.2.1
                have p693_3 := h693c.2.2.2
                linarith only [h406, hlam, p693_0]
              · have p693_0 := h693c.1
                have p693_1 := h693c.2.1
                have p693_2 := h693c.2.2.1
                have p693_3 := h693c.2.2.2
                linarith only [h565, hlam, p693_0]
              · have p693_0 := h693c.1
                have p693_1 := h693c.2.1
                have p693_2 := h693c.2.2.1
                have p693_3 := h693c.2.2.2
                linarith only [h1, hlam, p693_1]
              · have p693_0 := h693c.1
                have p693_1 := h693c.2.1
                have p693_2 := h693c.2.2.1
                have p693_3 := h693c.2.2.2
                linarith only [h3, hc12, hc25, hlam, hphi, p693_1]
              · have p693_0 := h693c.1
                have p693_1 := h693c.2.1
                have p693_2 := h693c.2.2.1
                have p693_3 := h693c.2.2.2
                linarith only [hlam, p693_0]
              · have p693_0 := h693c.1
                have p693_1 := h693c.2.1
                have p693_2 := h693c.2.2.1
                have p693_3 := h693c.2.2.2
                linarith only [h0, h1, h406, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p693_1, u1elo0]
              · have p693_0 := h693c.1
                have p693_1 := h693c.2.1
                have p693_2 := h693c.2.2.1
                have p693_3 := h693c.2.2.2
                linarith only [h637, hlam, p693_0]
              · have p693_0 := h693c.1
                have p693_1 := h693c.2.1
                have p693_2 := h693c.2.2.1
                have p693_3 := h693c.2.2.2
                linarith only [h0, h3, hc12, hc35, hlam, hphi, ht23, p693_1]
              · have p693_0 := h693c.1
                have p693_1 := h693c.2.1
                have p693_2 := h693c.2.2.1
                have p693_3 := h693c.2.2.2
                linarith only [h3, hc12, hc35, hlam, hphi, ht23, p693_1]
              · have p693_0 := h693c.1
                have p693_1 := h693c.2.1
                have p693_2 := h693c.2.2.1
                have p693_3 := h693c.2.2.2
                linarith only [h636, hlam, p693_0]
              · have p693_0 := h693c.1
                have p693_1 := h693c.2.1
                have p693_2 := h693c.2.2.1
                have p693_3 := h693c.2.2.2
                linarith only [hlam, p693_0]
              · have p693_0 := h693c.1
                have p693_1 := h693c.2.1
                have p693_2 := h693c.2.2.1
                have p693_3 := h693c.2.2.2
                linarith only [h691, hlam, p693_0]
              · have p693_0 := h693c.1
                have p693_1 := h693c.2.1
                have p693_2 := h693c.2.2.1
                have p693_3 := h693c.2.2.2
                linarith only [h2, hlam, p693_1]
              · have p693_0 := h693c.1
                have p693_1 := h693c.2.1
                have p693_2 := h693c.2.2.1
                have p693_3 := h693c.2.2.2
                linarith only [h3, hc12, hc45, hlam, hphi, ht23, ht34, p693_1]
              · have p693_0 := h693c.1
                have p693_1 := h693c.2.1
                have p693_2 := h693c.2.2.1
                have p693_3 := h693c.2.2.2
                linarith only [h0, h2, h3, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p693_1, u1elo0]
              · have p693_0 := h693c.1
                have p693_1 := h693c.2.1
                have p693_2 := h693c.2.2.1
                have p693_3 := h693c.2.2.2
                linarith only [h0, h2, hc35, hlam, hphi, ht01, ht0b, ht5b, p693_1, u1elo0]
              · have p693_0 := h693c.1
                have p693_1 := h693c.2.1
                have p693_2 := h693c.2.2.1
                have p693_3 := h693c.2.2.2
                linarith only [hlam, p693_0]
        · rcases m.htr 2 4 5 (by decide) (by decide) with h719 | h719
          · linarith only [h635, h636, h719, hlam]
          · rcases m.htr 3 4 5 (by decide) (by decide) with h721 | h721
            · linarith only [h635, h636, h719, h721, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
            · rcases h5bigk with h723c | h723c | h723c | h723c | h723c | h723c | h723c | h723c | h723c | h723c | h723c | h723c | h723c | h723c | h723c | h723c | h723c | h723c | h723c | h723c | h723c | h723c | h723c | h723c | h723c
              · have p723_0 := h723c.1
                have p723_1 := h723c.2.1
                have p723_2 := h723c.2.2.1
                have p723_3 := h723c.2.2.2
                linarith only [hlam, p723_0]
              · have p723_0 := h723c.1
                have p723_1 := h723c.2.1
                have p723_2 := h723c.2.2.1
                have p723_3 := h723c.2.2.2
                linarith only [h0, h3, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p723_1, u1elo0]
              · have p723_0 := h723c.1
                have p723_1 := h723c.2.1
                have p723_2 := h723c.2.2.1
                have p723_3 := h723c.2.2.2
                linarith only [h0, hc25, hlam, hphi, ht01, ht0b, ht5b, p723_1, u1elo0]
              · have p723_0 := h723c.1
                have p723_1 := h723c.2.1
                have p723_2 := h723c.2.2.1
                have p723_3 := h723c.2.2.2
                linarith only [h0, hc35, hlam, hphi, ht01, ht0b, ht5b, p723_1, u1elo0]
              · have p723_0 := h723c.1
                have p723_1 := h723c.2.1
                have p723_2 := h723c.2.2.1
                have p723_3 := h723c.2.2.2
                linarith only [h0, hc45, hlam, hphi, ht01, ht0b, ht5b, p723_1, u1elo0]
              · have p723_0 := h723c.1
                have p723_1 := h723c.2.1
                have p723_2 := h723c.2.2.1
                have p723_3 := h723c.2.2.2
                linarith only [h0, hlam, p723_0]
              · have p723_0 := h723c.1
                have p723_1 := h723c.2.1
                have p723_2 := h723c.2.2.1
                have p723_3 := h723c.2.2.2
                linarith only [hlam, p723_0]
              · have p723_0 := h723c.1
                have p723_1 := h723c.2.1
                have p723_2 := h723c.2.2.1
                have p723_3 := h723c.2.2.2
                linarith only [h3, hlam, p723_0]
              · have p723_0 := h723c.1
                have p723_1 := h723c.2.1
                have p723_2 := h723c.2.2.1
                have p723_3 := h723c.2.2.2
                linarith only [h406, hlam, p723_0]
              · have p723_0 := h723c.1
                have p723_1 := h723c.2.1
                have p723_2 := h723c.2.2.1
                have p723_3 := h723c.2.2.2
                linarith only [h565, hlam, p723_0]
              · have p723_0 := h723c.1
                have p723_1 := h723c.2.1
                have p723_2 := h723c.2.2.1
                have p723_3 := h723c.2.2.2
                linarith only [h1, hlam, p723_1]
              · have p723_0 := h723c.1
                have p723_1 := h723c.2.1
                have p723_2 := h723c.2.2.1
                have p723_3 := h723c.2.2.2
                linarith only [h3, hc12, hc25, hlam, hphi, p723_1]
              · have p723_0 := h723c.1
                have p723_1 := h723c.2.1
                have p723_2 := h723c.2.2.1
                have p723_3 := h723c.2.2.2
                linarith only [hlam, p723_0]
              · have p723_0 := h723c.1
                have p723_1 := h723c.2.1
                have p723_2 := h723c.2.2.1
                have p723_3 := h723c.2.2.2
                linarith only [h636, hlam, p723_1]
              · have p723_0 := h723c.1
                have p723_1 := h723c.2.1
                have p723_2 := h723c.2.2.1
                have p723_3 := h723c.2.2.2
                linarith only [h719, hlam, p723_0]
              · have p723_0 := h723c.1
                have p723_1 := h723c.2.1
                have p723_2 := h723c.2.2.1
                have p723_3 := h723c.2.2.2
                linarith only [h2, h721, hlam, p723_1]
              · have p723_0 := h723c.1
                have p723_1 := h723c.2.1
                have p723_2 := h723c.2.2.1
                have p723_3 := h723c.2.2.2
                linarith only [h0, h2, h3, h721, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p723_1, u1elo0]
              · have p723_0 := h723c.1
                have p723_1 := h723c.2.1
                have p723_2 := h723c.2.2.1
                have p723_3 := h723c.2.2.2
                linarith only [h0, h2, h721, hc25, hlam, hphi, ht01, ht0b, ht5b, p723_1, u1elo0]
              · have p723_0 := h723c.1
                have p723_1 := h723c.2.1
                have p723_2 := h723c.2.2.1
                have p723_3 := h723c.2.2.2
                linarith only [hlam, p723_0]
              · have p723_0 := h723c.1
                have p723_1 := h723c.2.1
                have p723_2 := h723c.2.2.1
                have p723_3 := h723c.2.2.2
                linarith only [h721, hlam, p723_0]
              · have p723_0 := h723c.1
                have p723_1 := h723c.2.1
                have p723_2 := h723c.2.2.1
                have p723_3 := h723c.2.2.2
                linarith only [h2, hlam, p723_1]
              · have p723_0 := h723c.1
                have p723_1 := h723c.2.1
                have p723_2 := h723c.2.2.1
                have p723_3 := h723c.2.2.2
                linarith only [h0, h2, h3, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p723_1, u1elo0]
              · have p723_0 := h723c.1
                have p723_1 := h723c.2.1
                have p723_2 := h723c.2.2.1
                have p723_3 := h723c.2.2.2
                linarith only [h0, h2, h3, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p723_1, u1elo0]
              · have p723_0 := h723c.1
                have p723_1 := h723c.2.1
                have p723_2 := h723c.2.2.1
                have p723_3 := h723c.2.2.2
                linarith only [h0, h2, hc35, hlam, hphi, ht01, ht0b, ht5b, p723_1, u1elo0]
              · have p723_0 := h723c.1
                have p723_1 := h723c.2.1
                have p723_2 := h723c.2.2.1
                have p723_3 := h723c.2.2.2
                linarith only [hlam, p723_0]
      · rcases m.htr 2 3 5 (by decide) (by decide) with h749 | h749
        · linarith only [h406, h635, h749, hc13, hc34, hlam, hphi]
        · rcases m.htr 2 4 5 (by decide) (by decide) with h751 | h751
          · rcases m.htr 3 4 5 (by decide) (by decide) with h752 | h752
            · rcases h5bigk with h753c | h753c | h753c | h753c | h753c | h753c | h753c | h753c | h753c | h753c | h753c | h753c | h753c | h753c | h753c | h753c | h753c | h753c | h753c | h753c | h753c | h753c | h753c | h753c | h753c
              · have p753_0 := h753c.1
                have p753_1 := h753c.2.1
                have p753_2 := h753c.2.2.1
                have p753_3 := h753c.2.2.2
                linarith only [hlam, p753_0]
              · have p753_0 := h753c.1
                have p753_1 := h753c.2.1
                have p753_2 := h753c.2.2.1
                have p753_3 := h753c.2.2.2
                linarith only [h0, h3, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p753_1, u1elo0]
              · have p753_0 := h753c.1
                have p753_1 := h753c.2.1
                have p753_2 := h753c.2.2.1
                have p753_3 := h753c.2.2.2
                linarith only [h0, h749, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p753_1, u1elo0]
              · have p753_0 := h753c.1
                have p753_1 := h753c.2.1
                have p753_2 := h753c.2.2.1
                have p753_3 := h753c.2.2.2
                linarith only [h0, hc35, hlam, hphi, ht01, ht0b, ht5b, p753_1, u1elo0]
              · have p753_0 := h753c.1
                have p753_1 := h753c.2.1
                have p753_2 := h753c.2.2.1
                have p753_3 := h753c.2.2.2
                linarith only [h0, hc45, hlam, hphi, ht01, ht0b, ht5b, p753_1, u1elo0]
              · have p753_0 := h753c.1
                have p753_1 := h753c.2.1
                have p753_2 := h753c.2.2.1
                have p753_3 := h753c.2.2.2
                linarith only [h0, hlam, p753_0]
              · have p753_0 := h753c.1
                have p753_1 := h753c.2.1
                have p753_2 := h753c.2.2.1
                have p753_3 := h753c.2.2.2
                linarith only [hlam, p753_0]
              · have p753_0 := h753c.1
                have p753_1 := h753c.2.1
                have p753_2 := h753c.2.2.1
                have p753_3 := h753c.2.2.2
                linarith only [h3, hlam, p753_0]
              · have p753_0 := h753c.1
                have p753_1 := h753c.2.1
                have p753_2 := h753c.2.2.1
                have p753_3 := h753c.2.2.2
                linarith only [h406, hlam, p753_0]
              · have p753_0 := h753c.1
                have p753_1 := h753c.2.1
                have p753_2 := h753c.2.2.1
                have p753_3 := h753c.2.2.2
                linarith only [h565, hlam, p753_0]
              · have p753_0 := h753c.1
                have p753_1 := h753c.2.1
                have p753_2 := h753c.2.2.1
                have p753_3 := h753c.2.2.2
                linarith only [h1, hlam, p753_1]
              · have p753_0 := h753c.1
                have p753_1 := h753c.2.1
                have p753_2 := h753c.2.2.1
                have p753_3 := h753c.2.2.2
                linarith only [h3, hc12, hc25, hlam, hphi, p753_1]
              · have p753_0 := h753c.1
                have p753_1 := h753c.2.1
                have p753_2 := h753c.2.2.1
                have p753_3 := h753c.2.2.2
                linarith only [hlam, p753_0]
              · have p753_0 := h753c.1
                have p753_1 := h753c.2.1
                have p753_2 := h753c.2.2.1
                have p753_3 := h753c.2.2.2
                linarith only [h749, hlam, p753_1]
              · have p753_0 := h753c.1
                have p753_1 := h753c.2.1
                have p753_2 := h753c.2.2.1
                have p753_3 := h753c.2.2.2
                linarith only [h0, h1, h565, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p753_1, u1elo0]
              · have p753_0 := h753c.1
                have p753_1 := h753c.2.1
                have p753_2 := h753c.2.2.1
                have p753_3 := h753c.2.2.2
                linarith only [h0, h3, hc12, hc35, hlam, hphi, ht23, p753_1]
              · have p753_0 := h753c.1
                have p753_1 := h753c.2.1
                have p753_2 := h753c.2.2.1
                have p753_3 := h753c.2.2.2
                linarith only [h3, hc12, hc35, hlam, hphi, ht23, p753_1]
              · have p753_0 := h753c.1
                have p753_1 := h753c.2.1
                have p753_2 := h753c.2.2.1
                have p753_3 := h753c.2.2.2
                linarith only [h3, hc12, hc35, hlam, hphi, ht23, p753_1]
              · have p753_0 := h753c.1
                have p753_1 := h753c.2.1
                have p753_2 := h753c.2.2.1
                have p753_3 := h753c.2.2.2
                linarith only [hlam, p753_0]
              · have p753_0 := h753c.1
                have p753_1 := h753c.2.1
                have p753_2 := h753c.2.2.1
                have p753_3 := h753c.2.2.2
                linarith only [h565, h752, hc14, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p753_1]
              · have p753_0 := h753c.1
                have p753_1 := h753c.2.1
                have p753_2 := h753c.2.2.1
                have p753_3 := h753c.2.2.2
                linarith only [h2, hlam, p753_1]
              · have p753_0 := h753c.1
                have p753_1 := h753c.2.1
                have p753_2 := h753c.2.2.1
                have p753_3 := h753c.2.2.2
                linarith only [h3, hc12, hc45, hlam, hphi, ht23, ht34, p753_1]
              · have p753_0 := h753c.1
                have p753_1 := h753c.2.1
                have p753_2 := h753c.2.2.1
                have p753_3 := h753c.2.2.2
                linarith only [h751, hlam, p753_1]
              · have p753_0 := h753c.1
                have p753_1 := h753c.2.1
                have p753_2 := h753c.2.2.1
                have p753_3 := h753c.2.2.2
                linarith only [h752, hlam, p753_1]
              · have p753_0 := h753c.1
                have p753_1 := h753c.2.1
                have p753_2 := h753c.2.2.1
                have p753_3 := h753c.2.2.2
                linarith only [hlam, p753_0]
            · linarith only [h635, h751, h752, hlam]
          · rcases m.htr 3 4 5 (by decide) (by decide) with h780 | h780
            · rcases h5bigk with h781c | h781c | h781c | h781c | h781c | h781c | h781c | h781c | h781c | h781c | h781c | h781c | h781c | h781c | h781c | h781c | h781c | h781c | h781c | h781c | h781c | h781c | h781c | h781c | h781c
              · have p781_0 := h781c.1
                have p781_1 := h781c.2.1
                have p781_2 := h781c.2.2.1
                have p781_3 := h781c.2.2.2
                linarith only [hlam, p781_0]
              · have p781_0 := h781c.1
                have p781_1 := h781c.2.1
                have p781_2 := h781c.2.2.1
                have p781_3 := h781c.2.2.2
                linarith only [h0, h3, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p781_1, u1elo0]
              · have p781_0 := h781c.1
                have p781_1 := h781c.2.1
                have p781_2 := h781c.2.2.1
                have p781_3 := h781c.2.2.2
                linarith only [h0, hc25, hlam, hphi, ht01, ht0b, ht5b, p781_1, u1elo0]
              · have p781_0 := h781c.1
                have p781_1 := h781c.2.1
                have p781_2 := h781c.2.2.1
                have p781_3 := h781c.2.2.2
                linarith only [h0, hc35, hlam, hphi, ht01, ht0b, ht5b, p781_1, u1elo0]
              · have p781_0 := h781c.1
                have p781_1 := h781c.2.1
                have p781_2 := h781c.2.2.1
                have p781_3 := h781c.2.2.2
                linarith only [h0, h751, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p781_1, u1elo0]
              · have p781_0 := h781c.1
                have p781_1 := h781c.2.1
                have p781_2 := h781c.2.2.1
                have p781_3 := h781c.2.2.2
                linarith only [h0, hlam, p781_0]
              · have p781_0 := h781c.1
                have p781_1 := h781c.2.1
                have p781_2 := h781c.2.2.1
                have p781_3 := h781c.2.2.2
                linarith only [hlam, p781_0]
              · have p781_0 := h781c.1
                have p781_1 := h781c.2.1
                have p781_2 := h781c.2.2.1
                have p781_3 := h781c.2.2.2
                linarith only [h3, hlam, p781_0]
              · have p781_0 := h781c.1
                have p781_1 := h781c.2.1
                have p781_2 := h781c.2.2.1
                have p781_3 := h781c.2.2.2
                linarith only [h406, hlam, p781_0]
              · have p781_0 := h781c.1
                have p781_1 := h781c.2.1
                have p781_2 := h781c.2.2.1
                have p781_3 := h781c.2.2.2
                linarith only [h565, hlam, p781_0]
              · have p781_0 := h781c.1
                have p781_1 := h781c.2.1
                have p781_2 := h781c.2.2.1
                have p781_3 := h781c.2.2.2
                linarith only [h1, hlam, p781_1]
              · have p781_0 := h781c.1
                have p781_1 := h781c.2.1
                have p781_2 := h781c.2.2.1
                have p781_3 := h781c.2.2.2
                linarith only [h3, hc12, hc25, hlam, hphi, p781_1]
              · have p781_0 := h781c.1
                have p781_1 := h781c.2.1
                have p781_2 := h781c.2.2.1
                have p781_3 := h781c.2.2.2
                linarith only [hlam, p781_0]
              · have p781_0 := h781c.1
                have p781_1 := h781c.2.1
                have p781_2 := h781c.2.2.1
                have p781_3 := h781c.2.2.2
                linarith only [h749, hlam, p781_1]
              · have p781_0 := h781c.1
                have p781_1 := h781c.2.1
                have p781_2 := h781c.2.2.1
                have p781_3 := h781c.2.2.2
                linarith only [h751, hlam, p781_0]
              · have p781_0 := h781c.1
                have p781_1 := h781c.2.1
                have p781_2 := h781c.2.2.1
                have p781_3 := h781c.2.2.2
                linarith only [h0, h3, hc12, hc35, hlam, hphi, ht23, p781_1]
              · have p781_0 := h781c.1
                have p781_1 := h781c.2.1
                have p781_2 := h781c.2.2.1
                have p781_3 := h781c.2.2.2
                linarith only [h3, hc12, hc35, hlam, hphi, ht23, p781_1]
              · have p781_0 := h781c.1
                have p781_1 := h781c.2.1
                have p781_2 := h781c.2.2.1
                have p781_3 := h781c.2.2.2
                linarith only [h3, hc12, hc35, hlam, hphi, ht23, p781_1]
              · have p781_0 := h781c.1
                have p781_1 := h781c.2.1
                have p781_2 := h781c.2.2.1
                have p781_3 := h781c.2.2.2
                linarith only [hlam, p781_0]
              · have p781_0 := h781c.1
                have p781_1 := h781c.2.1
                have p781_2 := h781c.2.2.1
                have p781_3 := h781c.2.2.2
                linarith only [h565, h780, hc14, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p781_1]
              · have p781_0 := h781c.1
                have p781_1 := h781c.2.1
                have p781_2 := h781c.2.2.1
                have p781_3 := h781c.2.2.2
                linarith only [h2, hlam, p781_1]
              · have p781_0 := h781c.1
                have p781_1 := h781c.2.1
                have p781_2 := h781c.2.2.1
                have p781_3 := h781c.2.2.2
                linarith only [h3, hc12, hc45, hlam, hphi, ht23, ht34, p781_1]
              · have p781_0 := h781c.1
                have p781_1 := h781c.2.1
                have p781_2 := h781c.2.2.1
                have p781_3 := h781c.2.2.2
                linarith only [h0, h2, h3, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p781_1, u1elo0]
              · have p781_0 := h781c.1
                have p781_1 := h781c.2.1
                have p781_2 := h781c.2.2.1
                have p781_3 := h781c.2.2.2
                linarith only [h780, hlam, p781_1]
              · have p781_0 := h781c.1
                have p781_1 := h781c.2.1
                have p781_2 := h781c.2.2.1
                have p781_3 := h781c.2.2.2
                linarith only [hlam, p781_0]
            · rcases h5bigk with h807c | h807c | h807c | h807c | h807c | h807c | h807c | h807c | h807c | h807c | h807c | h807c | h807c | h807c | h807c | h807c | h807c | h807c | h807c | h807c | h807c | h807c | h807c | h807c | h807c
              · have p807_0 := h807c.1
                have p807_1 := h807c.2.1
                have p807_2 := h807c.2.2.1
                have p807_3 := h807c.2.2.2
                linarith only [hlam, p807_0]
              · have p807_0 := h807c.1
                have p807_1 := h807c.2.1
                have p807_2 := h807c.2.2.1
                have p807_3 := h807c.2.2.2
                linarith only [h0, h3, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p807_1, u1elo0]
              · have p807_0 := h807c.1
                have p807_1 := h807c.2.1
                have p807_2 := h807c.2.2.1
                have p807_3 := h807c.2.2.2
                linarith only [h0, h3, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p807_1, u1elo0]
              · have p807_0 := h807c.1
                have p807_1 := h807c.2.1
                have p807_2 := h807c.2.2.1
                have p807_3 := h807c.2.2.2
                linarith only [h0, hc35, hlam, hphi, ht01, ht0b, ht5b, p807_1, u1elo0]
              · have p807_0 := h807c.1
                have p807_1 := h807c.2.1
                have p807_2 := h807c.2.2.1
                have p807_3 := h807c.2.2.2
                linarith only [h0, h780, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p807_1, u1elo0]
              · have p807_0 := h807c.1
                have p807_1 := h807c.2.1
                have p807_2 := h807c.2.2.1
                have p807_3 := h807c.2.2.2
                linarith only [h0, hlam, p807_0]
              · have p807_0 := h807c.1
                have p807_1 := h807c.2.1
                have p807_2 := h807c.2.2.1
                have p807_3 := h807c.2.2.2
                linarith only [hlam, p807_0]
              · have p807_0 := h807c.1
                have p807_1 := h807c.2.1
                have p807_2 := h807c.2.2.1
                have p807_3 := h807c.2.2.2
                linarith only [h3, hlam, p807_0]
              · have p807_0 := h807c.1
                have p807_1 := h807c.2.1
                have p807_2 := h807c.2.2.1
                have p807_3 := h807c.2.2.2
                linarith only [h406, hlam, p807_0]
              · have p807_0 := h807c.1
                have p807_1 := h807c.2.1
                have p807_2 := h807c.2.2.1
                have p807_3 := h807c.2.2.2
                linarith only [h565, hlam, p807_0]
              · have p807_0 := h807c.1
                have p807_1 := h807c.2.1
                have p807_2 := h807c.2.2.1
                have p807_3 := h807c.2.2.2
                linarith only [h1, hlam, p807_1]
              · have p807_0 := h807c.1
                have p807_1 := h807c.2.1
                have p807_2 := h807c.2.2.1
                have p807_3 := h807c.2.2.2
                linarith only [h3, hc12, hc25, hlam, hphi, p807_1]
              · have p807_0 := h807c.1
                have p807_1 := h807c.2.1
                have p807_2 := h807c.2.2.1
                have p807_3 := h807c.2.2.2
                linarith only [hlam, p807_0]
              · have p807_0 := h807c.1
                have p807_1 := h807c.2.1
                have p807_2 := h807c.2.2.1
                have p807_3 := h807c.2.2.2
                linarith only [h749, hlam, p807_1]
              · have p807_0 := h807c.1
                have p807_1 := h807c.2.1
                have p807_2 := h807c.2.2.1
                have p807_3 := h807c.2.2.2
                linarith only [h751, hlam, p807_0]
              · have p807_0 := h807c.1
                have p807_1 := h807c.2.1
                have p807_2 := h807c.2.2.1
                have p807_3 := h807c.2.2.2
                linarith only [h2, h780, hlam, p807_1]
              · have p807_0 := h807c.1
                have p807_1 := h807c.2.1
                have p807_2 := h807c.2.2.1
                have p807_3 := h807c.2.2.2
                linarith only [h0, h2, h3, h780, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p807_1, u1elo0]
              · have p807_0 := h807c.1
                have p807_1 := h807c.2.1
                have p807_2 := h807c.2.2.1
                have p807_3 := h807c.2.2.2
                linarith only [h0, h2, h780, hc25, hlam, hphi, ht01, ht0b, ht5b, p807_1, u1elo0]
              · have p807_0 := h807c.1
                have p807_1 := h807c.2.1
                have p807_2 := h807c.2.2.1
                have p807_3 := h807c.2.2.2
                linarith only [hlam, p807_0]
              · have p807_0 := h807c.1
                have p807_1 := h807c.2.1
                have p807_2 := h807c.2.2.1
                have p807_3 := h807c.2.2.2
                linarith only [h780, hlam, p807_0]
              · have p807_0 := h807c.1
                have p807_1 := h807c.2.1
                have p807_2 := h807c.2.2.1
                have p807_3 := h807c.2.2.2
                linarith only [h2, hlam, p807_1]
              · have p807_0 := h807c.1
                have p807_1 := h807c.2.1
                have p807_2 := h807c.2.2.1
                have p807_3 := h807c.2.2.2
                linarith only [h0, h2, h3, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p807_1, u1elo0]
              · have p807_0 := h807c.1
                have p807_1 := h807c.2.1
                have p807_2 := h807c.2.2.1
                have p807_3 := h807c.2.2.2
                linarith only [h0, h2, h3, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p807_1, u1elo0]
              · have p807_0 := h807c.1
                have p807_1 := h807c.2.1
                have p807_2 := h807c.2.2.1
                have p807_3 := h807c.2.2.2
                linarith only [h0, h2, hc35, hlam, hphi, ht01, ht0b, ht5b, p807_1, u1elo0]
              · have p807_0 := h807c.1
                have p807_1 := h807c.2.1
                have p807_2 := h807c.2.2.1
                have p807_3 := h807c.2.2.2
                linarith only [hlam, p807_0]

set_option maxHeartbeats 6812000 in
theorem r1l7_11_12_25_L_0_L_I_H_I_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h1 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h2 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc05 := m.hcor 0 5 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1elo := hb1.1
  have h5bigk := hb5.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  rcases m.htr 1 2 5 (by decide) (by decide) with h3 | h3
  · exact r1l7_11_12_25_L_0_L_I_H_I_x0_x0_x0_x0 m hb1 hb2 hb5 h0 h1 h2 h3
  · exact r1l7_11_12_25_L_0_L_I_H_I_x0_x0_x0_x1 m hb1 hb2 hb5 h0 h1 h2 h3

end R2N4
