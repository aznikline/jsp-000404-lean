import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_71S0

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_10_12_13_25_L_0_L_0_L_0_H_I_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_0 m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
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
  have hc13 := m.hcor 1 3 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
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
  have h0elo := hb0.1
  have h2elo := hb2.1
  have h3elo := hb3.1
  have h5bigk := hb5.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 2 5 (by decide) (by decide) with h497 | h497
  · rcases m.htr 0 3 5 (by decide) (by decide) with h498 | h498
    · rcases m.htr 0 4 5 (by decide) (by decide) with h499 | h499
      · rcases m.htr 1 3 5 (by decide) (by decide) with h500 | h500
        · rcases m.htr 2 4 5 (by decide) (by decide) with h501 | h501
          · rcases m.htr 3 4 5 (by decide) (by decide) with h502 | h502
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
                linarith only [h0, hlam, p503_1]
              · have p503_0 := h503c.1
                have p503_1 := h503c.2.1
                have p503_2 := h503c.2.2.1
                have p503_3 := h503c.2.2.2
                linarith only [h501, hc45, hlam, hphi, ht0b, ht5b, p503_1, u0elo4]
              · have p503_0 := h503c.1
                have p503_1 := h503c.2.1
                have p503_2 := h503c.2.2.1
                have p503_3 := h503c.2.2.2
                linarith only [h0, h500, h502, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p503_1, u3elo1]
              · have p503_0 := h503c.1
                have p503_1 := h503c.2.1
                have p503_2 := h503c.2.2.1
                have p503_3 := h503c.2.2.2
                linarith only [h0, h500, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p503_1, u3elo1]
              · have p503_0 := h503c.1
                have p503_1 := h503c.2.1
                have p503_2 := h503c.2.2.1
                have p503_3 := h503c.2.2.2
                linarith only [h500, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p503_1, u3elo1]
              · have p503_0 := h503c.1
                have p503_1 := h503c.2.1
                have p503_2 := h503c.2.2.1
                have p503_3 := h503c.2.2.2
                linarith only [hlam, p503_0]
              · have p503_0 := h503c.1
                have p503_1 := h503c.2.1
                have p503_2 := h503c.2.2.1
                have p503_3 := h503c.2.2.2
                linarith only [h500, h501, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p503_1, u3elo1]
              · have p503_0 := h503c.1
                have p503_1 := h503c.2.1
                have p503_2 := h503c.2.2.1
                have p503_3 := h503c.2.2.2
                linarith only [h500, h502, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p503_1, u3elo1]
              · have p503_0 := h503c.1
                have p503_1 := h503c.2.1
                have p503_2 := h503c.2.2.1
                have p503_3 := h503c.2.2.2
                linarith only [h500, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p503_1, u3elo1]
              · have p503_0 := h503c.1
                have p503_1 := h503c.2.1
                have p503_2 := h503c.2.2.1
                have p503_3 := h503c.2.2.2
                linarith only [h497, hlam, p503_1]
              · have p503_0 := h503c.1
                have p503_1 := h503c.2.1
                have p503_2 := h503c.2.2.1
                have p503_3 := h503c.2.2.2
                linarith only [h497, hc15, hlam, hphi, ht0b, ht5b, p503_1, u0elo1]
              · have p503_0 := h503c.1
                have p503_1 := h503c.2.1
                have p503_2 := h503c.2.2.1
                have p503_3 := h503c.2.2.2
                linarith only [hlam, p503_0]
              · have p503_0 := h503c.1
                have p503_1 := h503c.2.1
                have p503_2 := h503c.2.2.1
                have p503_3 := h503c.2.2.2
                linarith only [h497, h502, hc45, hlam, hphi, ht0b, ht5b, p503_1, u0elo4]
              · have p503_0 := h503c.1
                have p503_1 := h503c.2.1
                have p503_2 := h503c.2.2.1
                have p503_3 := h503c.2.2.2
                linarith only [h497, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p503_1, u2elo0]
              · have p503_0 := h503c.1
                have p503_1 := h503c.2.1
                have p503_2 := h503c.2.2.1
                have p503_3 := h503c.2.2.2
                linarith only [h498, hlam, p503_0]
              · have p503_0 := h503c.1
                have p503_1 := h503c.2.1
                have p503_2 := h503c.2.2.1
                have p503_3 := h503c.2.2.2
                linarith only [h500, hlam, p503_0]
              · have p503_0 := h503c.1
                have p503_1 := h503c.2.1
                have p503_2 := h503c.2.2.1
                have p503_3 := h503c.2.2.2
                linarith only [hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p503_1, u3elo4]
              · have p503_0 := h503c.1
                have p503_1 := h503c.2.1
                have p503_2 := h503c.2.2.1
                have p503_3 := h503c.2.2.2
                linarith only [hlam, p503_0]
              · have p503_0 := h503c.1
                have p503_1 := h503c.2.1
                have p503_2 := h503c.2.2.1
                have p503_3 := h503c.2.2.2
                linarith only [h498, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p503_1, u3elo0]
              · have p503_0 := h503c.1
                have p503_1 := h503c.2.1
                have p503_2 := h503c.2.2.1
                have p503_3 := h503c.2.2.2
                linarith only [h499, hlam, p503_0]
              · have p503_0 := h503c.1
                have p503_1 := h503c.2.1
                have p503_2 := h503c.2.2.1
                have p503_3 := h503c.2.2.2
                linarith only [h0, h501, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p503_1, u2elo3]
              · have p503_0 := h503c.1
                have p503_1 := h503c.2.1
                have p503_2 := h503c.2.2.1
                have p503_3 := h503c.2.2.2
                linarith only [h501, hlam, p503_0]
              · have p503_0 := h503c.1
                have p503_1 := h503c.2.1
                have p503_2 := h503c.2.2.1
                have p503_3 := h503c.2.2.2
                linarith only [h502, hlam, p503_0]
              · have p503_0 := h503c.1
                have p503_1 := h503c.2.1
                have p503_2 := h503c.2.2.1
                have p503_3 := h503c.2.2.2
                linarith only [hlam, p503_0]
            · rcases h5bigk with h529c | h529c | h529c | h529c | h529c | h529c | h529c | h529c | h529c | h529c | h529c | h529c | h529c | h529c | h529c | h529c | h529c | h529c | h529c | h529c | h529c | h529c | h529c | h529c | h529c
              · have p529_0 := h529c.1
                have p529_1 := h529c.2.1
                have p529_2 := h529c.2.2.1
                have p529_3 := h529c.2.2.2
                linarith only [hlam, p529_0]
              · have p529_0 := h529c.1
                have p529_1 := h529c.2.1
                have p529_2 := h529c.2.2.1
                have p529_3 := h529c.2.2.2
                linarith only [h0, hlam, p529_1]
              · have p529_0 := h529c.1
                have p529_1 := h529c.2.1
                have p529_2 := h529c.2.2.1
                have p529_3 := h529c.2.2.2
                linarith only [hc25, hlam, hphi, ht0b, ht5b, p529_1, u0elo4]
              · have p529_0 := h529c.1
                have p529_1 := h529c.2.1
                have p529_2 := h529c.2.2.1
                have p529_3 := h529c.2.2.2
                linarith only [h498, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p529_1, u3elo0]
              · have p529_0 := h529c.1
                have p529_1 := h529c.2.1
                have p529_2 := h529c.2.2.1
                have p529_3 := h529c.2.2.2
                linarith only [h498, h502, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p529_1, u3elo0]
              · have p529_0 := h529c.1
                have p529_1 := h529c.2.1
                have p529_2 := h529c.2.2.1
                have p529_3 := h529c.2.2.2
                linarith only [h0, hc01, hc15, hlam, hphi, p529_1]
              · have p529_0 := h529c.1
                have p529_1 := h529c.2.1
                have p529_2 := h529c.2.2.1
                have p529_3 := h529c.2.2.2
                linarith only [hlam, p529_0]
              · have p529_0 := h529c.1
                have p529_1 := h529c.2.1
                have p529_2 := h529c.2.2.1
                have p529_3 := h529c.2.2.2
                linarith only [h500, h501, h502, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p529_1, u3elo1]
              · have p529_0 := h529c.1
                have p529_1 := h529c.2.1
                have p529_2 := h529c.2.2.1
                have p529_3 := h529c.2.2.2
                linarith only [h500, h502, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p529_1, u3elo1]
              · have p529_0 := h529c.1
                have p529_1 := h529c.2.1
                have p529_2 := h529c.2.2.1
                have p529_3 := h529c.2.2.2
                linarith only [h500, h502, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p529_1, u3elo1]
              · have p529_0 := h529c.1
                have p529_1 := h529c.2.1
                have p529_2 := h529c.2.2.1
                have p529_3 := h529c.2.2.2
                linarith only [h497, hlam, p529_1]
              · have p529_0 := h529c.1
                have p529_1 := h529c.2.1
                have p529_2 := h529c.2.2.1
                have p529_3 := h529c.2.2.2
                linarith only [h497, hc15, hlam, hphi, ht0b, ht5b, p529_1, u0elo4]
              · have p529_0 := h529c.1
                have p529_1 := h529c.2.1
                have p529_2 := h529c.2.2.1
                have p529_3 := h529c.2.2.2
                linarith only [hlam, p529_0]
              · have p529_0 := h529c.1
                have p529_1 := h529c.2.1
                have p529_2 := h529c.2.2.1
                have p529_3 := h529c.2.2.2
                linarith only [h497, h502, hc34, hlam, hphi, ht0b, ht45, ht5b, p529_1, u0elo4]
              · have p529_0 := h529c.1
                have p529_1 := h529c.2.1
                have p529_2 := h529c.2.2.1
                have p529_3 := h529c.2.2.2
                linarith only [h497, h502, hc34, hlam, hphi, ht0b, ht45, ht5b, p529_1, u0elo4]
              · have p529_0 := h529c.1
                have p529_1 := h529c.2.1
                have p529_2 := h529c.2.2.1
                have p529_3 := h529c.2.2.2
                linarith only [h498, hlam, p529_0]
              · have p529_0 := h529c.1
                have p529_1 := h529c.2.1
                have p529_2 := h529c.2.2.1
                have p529_3 := h529c.2.2.2
                linarith only [h500, hlam, p529_0]
              · have p529_0 := h529c.1
                have p529_1 := h529c.2.1
                have p529_2 := h529c.2.2.1
                have p529_3 := h529c.2.2.2
                linarith only [hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p529_1, u3elo4]
              · have p529_0 := h529c.1
                have p529_1 := h529c.2.1
                have p529_2 := h529c.2.2.1
                have p529_3 := h529c.2.2.2
                linarith only [hlam, p529_0]
              · have p529_0 := h529c.1
                have p529_1 := h529c.2.1
                have p529_2 := h529c.2.2.1
                have p529_3 := h529c.2.2.2
                linarith only [h502, hlam, p529_1]
              · have p529_0 := h529c.1
                have p529_1 := h529c.2.1
                have p529_2 := h529c.2.2.1
                have p529_3 := h529c.2.2.2
                linarith only [h499, hlam, p529_0]
              · have p529_0 := h529c.1
                have p529_1 := h529c.2.1
                have p529_2 := h529c.2.2.1
                have p529_3 := h529c.2.2.2
                linarith only [h0, h501, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p529_1, u2elo4]
              · have p529_0 := h529c.1
                have p529_1 := h529c.2.1
                have p529_2 := h529c.2.2.1
                have p529_3 := h529c.2.2.2
                linarith only [h501, hlam, p529_0]
              · have p529_0 := h529c.1
                have p529_1 := h529c.2.1
                have p529_2 := h529c.2.2.1
                have p529_3 := h529c.2.2.2
                linarith only [h497, h501, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p529_1, u2elo0]
              · have p529_0 := h529c.1
                have p529_1 := h529c.2.1
                have p529_2 := h529c.2.2.1
                have p529_3 := h529c.2.2.2
                linarith only [hlam, p529_0]
          · rcases m.htr 3 4 5 (by decide) (by decide) with h555 | h555
            · rcases h5bigk with h556c | h556c | h556c | h556c | h556c | h556c | h556c | h556c | h556c | h556c | h556c | h556c | h556c | h556c | h556c | h556c | h556c | h556c | h556c | h556c | h556c | h556c | h556c | h556c | h556c
              · have p556_0 := h556c.1
                have p556_1 := h556c.2.1
                have p556_2 := h556c.2.2.1
                have p556_3 := h556c.2.2.2
                linarith only [hlam, p556_0]
              · have p556_0 := h556c.1
                have p556_1 := h556c.2.1
                have p556_2 := h556c.2.2.1
                have p556_3 := h556c.2.2.2
                linarith only [h0, hlam, p556_1]
              · have p556_0 := h556c.1
                have p556_1 := h556c.2.1
                have p556_2 := h556c.2.2.1
                have p556_3 := h556c.2.2.2
                linarith only [hc25, hlam, hphi, ht0b, ht5b, p556_1, u0elo4]
              · have p556_0 := h556c.1
                have p556_1 := h556c.2.1
                have p556_2 := h556c.2.2.1
                have p556_3 := h556c.2.2.2
                linarith only [h498, h501, h555, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p556_1, u3elo0]
              · have p556_0 := h556c.1
                have p556_1 := h556c.2.1
                have p556_2 := h556c.2.2.1
                have p556_3 := h556c.2.2.2
                linarith only [h498, h501, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p556_1, u3elo0]
              · have p556_0 := h556c.1
                have p556_1 := h556c.2.1
                have p556_2 := h556c.2.2.1
                have p556_3 := h556c.2.2.2
                linarith only [h0, hc01, hc15, hlam, hphi, p556_1]
              · have p556_0 := h556c.1
                have p556_1 := h556c.2.1
                have p556_2 := h556c.2.2.1
                have p556_3 := h556c.2.2.2
                linarith only [hlam, p556_0]
              · have p556_0 := h556c.1
                have p556_1 := h556c.2.1
                have p556_2 := h556c.2.2.1
                have p556_3 := h556c.2.2.2
                linarith only [h500, h501, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p556_1, u3elo1]
              · have p556_0 := h556c.1
                have p556_1 := h556c.2.1
                have p556_2 := h556c.2.2.1
                have p556_3 := h556c.2.2.2
                linarith only [h500, h501, h555, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p556_1, u3elo1]
              · have p556_0 := h556c.1
                have p556_1 := h556c.2.1
                have p556_2 := h556c.2.2.1
                have p556_3 := h556c.2.2.2
                linarith only [h500, h501, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p556_1, u3elo1]
              · have p556_0 := h556c.1
                have p556_1 := h556c.2.1
                have p556_2 := h556c.2.2.1
                have p556_3 := h556c.2.2.2
                linarith only [h497, hlam, p556_1]
              · have p556_0 := h556c.1
                have p556_1 := h556c.2.1
                have p556_2 := h556c.2.2.1
                have p556_3 := h556c.2.2.2
                linarith only [hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p556_1, u2elo4]
              · have p556_0 := h556c.1
                have p556_1 := h556c.2.1
                have p556_2 := h556c.2.2.1
                have p556_3 := h556c.2.2.2
                linarith only [hlam, p556_0]
              · have p556_0 := h556c.1
                have p556_1 := h556c.2.1
                have p556_2 := h556c.2.2.1
                have p556_3 := h556c.2.2.2
                linarith only [h501, h555, hlam, p556_1]
              · have p556_0 := h556c.1
                have p556_1 := h556c.2.1
                have p556_2 := h556c.2.2.1
                have p556_3 := h556c.2.2.2
                linarith only [h501, hlam, p556_1]
              · have p556_0 := h556c.1
                have p556_1 := h556c.2.1
                have p556_2 := h556c.2.2.1
                have p556_3 := h556c.2.2.2
                linarith only [h498, hlam, p556_0]
              · have p556_0 := h556c.1
                have p556_1 := h556c.2.1
                have p556_2 := h556c.2.2.1
                have p556_3 := h556c.2.2.2
                linarith only [h500, hlam, p556_0]
              · have p556_0 := h556c.1
                have p556_1 := h556c.2.1
                have p556_2 := h556c.2.2.1
                have p556_3 := h556c.2.2.2
                linarith only [h498, hc25, hlam, hphi, ht0b, ht5b, p556_1, u0elo4]
              · have p556_0 := h556c.1
                have p556_1 := h556c.2.1
                have p556_2 := h556c.2.2.1
                have p556_3 := h556c.2.2.2
                linarith only [hlam, p556_0]
              · have p556_0 := h556c.1
                have p556_1 := h556c.2.1
                have p556_2 := h556c.2.2.1
                have p556_3 := h556c.2.2.2
                linarith only [h498, h501, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p556_1, u3elo0]
              · have p556_0 := h556c.1
                have p556_1 := h556c.2.1
                have p556_2 := h556c.2.2.1
                have p556_3 := h556c.2.2.2
                linarith only [h499, hlam, p556_0]
              · have p556_0 := h556c.1
                have p556_1 := h556c.2.1
                have p556_2 := h556c.2.2.1
                have p556_3 := h556c.2.2.2
                linarith only [h0, h555, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p556_1, u3elo3]
              · have p556_0 := h556c.1
                have p556_1 := h556c.2.1
                have p556_2 := h556c.2.2.1
                have p556_3 := h556c.2.2.2
                linarith only [h501, h555, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p556_1, u3elo3]
              · have p556_0 := h556c.1
                have p556_1 := h556c.2.1
                have p556_2 := h556c.2.2.1
                have p556_3 := h556c.2.2.2
                linarith only [h555, hlam, p556_0]
              · have p556_0 := h556c.1
                have p556_1 := h556c.2.1
                have p556_2 := h556c.2.2.1
                have p556_3 := h556c.2.2.2
                linarith only [hlam, p556_0]
            · rcases h5bigk with h582c | h582c | h582c | h582c | h582c | h582c | h582c | h582c | h582c | h582c | h582c | h582c | h582c | h582c | h582c | h582c | h582c | h582c | h582c | h582c | h582c | h582c | h582c | h582c | h582c
              · have p582_0 := h582c.1
                have p582_1 := h582c.2.1
                have p582_2 := h582c.2.2.1
                have p582_3 := h582c.2.2.2
                linarith only [hlam, p582_0]
              · have p582_0 := h582c.1
                have p582_1 := h582c.2.1
                have p582_2 := h582c.2.2.1
                have p582_3 := h582c.2.2.2
                linarith only [h0, hlam, p582_1]
              · have p582_0 := h582c.1
                have p582_1 := h582c.2.1
                have p582_2 := h582c.2.2.1
                have p582_3 := h582c.2.2.2
                linarith only [h501, hc24, hlam, hphi, ht0b, ht45, ht5b, p582_1, u0elo4]
              · have p582_0 := h582c.1
                have p582_1 := h582c.2.1
                have p582_2 := h582c.2.2.1
                have p582_3 := h582c.2.2.2
                linarith only [h498, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p582_1, u3elo0]
              · have p582_0 := h582c.1
                have p582_1 := h582c.2.1
                have p582_2 := h582c.2.2.1
                have p582_3 := h582c.2.2.2
                linarith only [h498, h555, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p582_1, u3elo0]
              · have p582_0 := h582c.1
                have p582_1 := h582c.2.1
                have p582_2 := h582c.2.2.1
                have p582_3 := h582c.2.2.2
                linarith only [h0, hc01, hc15, hlam, hphi, p582_1]
              · have p582_0 := h582c.1
                have p582_1 := h582c.2.1
                have p582_2 := h582c.2.2.1
                have p582_3 := h582c.2.2.2
                linarith only [hlam, p582_0]
              · have p582_0 := h582c.1
                have p582_1 := h582c.2.1
                have p582_2 := h582c.2.2.1
                have p582_3 := h582c.2.2.2
                linarith only [h500, h501, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p582_1, u3elo1]
              · have p582_0 := h582c.1
                have p582_1 := h582c.2.1
                have p582_2 := h582c.2.2.1
                have p582_3 := h582c.2.2.2
                linarith only [h500, h555, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p582_1, u3elo1]
              · have p582_0 := h582c.1
                have p582_1 := h582c.2.1
                have p582_2 := h582c.2.2.1
                have p582_3 := h582c.2.2.2
                linarith only [h500, h555, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p582_1, u3elo1]
              · have p582_0 := h582c.1
                have p582_1 := h582c.2.1
                have p582_2 := h582c.2.2.1
                have p582_3 := h582c.2.2.2
                linarith only [h497, hlam, p582_1]
              · have p582_0 := h582c.1
                have p582_1 := h582c.2.1
                have p582_2 := h582c.2.2.1
                have p582_3 := h582c.2.2.2
                linarith only [hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p582_1, u2elo4]
              · have p582_0 := h582c.1
                have p582_1 := h582c.2.1
                have p582_2 := h582c.2.2.1
                have p582_3 := h582c.2.2.2
                linarith only [hlam, p582_0]
              · have p582_0 := h582c.1
                have p582_1 := h582c.2.1
                have p582_2 := h582c.2.2.1
                have p582_3 := h582c.2.2.2
                linarith only [h499, h501, h555, hc34, hlam, hphi, ht0b, ht45, ht5b, p582_1, u0elo3]
              · have p582_0 := h582c.1
                have p582_1 := h582c.2.1
                have p582_2 := h582c.2.2.1
                have p582_3 := h582c.2.2.2
                linarith only [h501, hlam, p582_1]
              · have p582_0 := h582c.1
                have p582_1 := h582c.2.1
                have p582_2 := h582c.2.2.1
                have p582_3 := h582c.2.2.2
                linarith only [h498, hlam, p582_0]
              · have p582_0 := h582c.1
                have p582_1 := h582c.2.1
                have p582_2 := h582c.2.2.1
                have p582_3 := h582c.2.2.2
                linarith only [h500, hlam, p582_0]
              · have p582_0 := h582c.1
                have p582_1 := h582c.2.1
                have p582_2 := h582c.2.2.1
                have p582_3 := h582c.2.2.2
                linarith only [hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p582_1, u3elo4]
              · have p582_0 := h582c.1
                have p582_1 := h582c.2.1
                have p582_2 := h582c.2.2.1
                have p582_3 := h582c.2.2.2
                linarith only [hlam, p582_0]
              · have p582_0 := h582c.1
                have p582_1 := h582c.2.1
                have p582_2 := h582c.2.2.1
                have p582_3 := h582c.2.2.2
                linarith only [h555, hlam, p582_1]
              · have p582_0 := h582c.1
                have p582_1 := h582c.2.1
                have p582_2 := h582c.2.2.1
                have p582_3 := h582c.2.2.2
                linarith only [h499, hlam, p582_0]
              · have p582_0 := h582c.1
                have p582_1 := h582c.2.1
                have p582_2 := h582c.2.2.1
                have p582_3 := h582c.2.2.2
                linarith only [h0, h499, hlam, p582_1]
              · have p582_0 := h582c.1
                have p582_1 := h582c.2.1
                have p582_2 := h582c.2.2.1
                have p582_3 := h582c.2.2.2
                linarith only [h499, h501, hc24, hlam, hphi, ht0b, ht45, ht5b, p582_1, u0elo3]
              · have p582_0 := h582c.1
                have p582_1 := h582c.2.1
                have p582_2 := h582c.2.2.1
                have p582_3 := h582c.2.2.2
                linarith only [h499, hc35, hlam, hphi, ht0b, ht5b, p582_1, u0elo3]
              · have p582_0 := h582c.1
                have p582_1 := h582c.2.1
                have p582_2 := h582c.2.2.1
                have p582_3 := h582c.2.2.2
                linarith only [hlam, p582_0]
        · linarith only [h498, h500, hc13, hlam, hphi, u3elo0]
      · rcases m.htr 1 3 5 (by decide) (by decide) with h609 | h609
        · rcases m.htr 2 4 5 (by decide) (by decide) with h610 | h610
          · linarith only [h497, h499, h610, hlam]
          · rcases m.htr 3 4 5 (by decide) (by decide) with h612 | h612
            · linarith only [h498, h499, h612, hlam]
            · rcases h5bigk with h614c | h614c | h614c | h614c | h614c | h614c | h614c | h614c | h614c | h614c | h614c | h614c | h614c | h614c | h614c | h614c | h614c | h614c | h614c | h614c | h614c | h614c | h614c | h614c | h614c
              · have p614_0 := h614c.1
                have p614_1 := h614c.2.1
                have p614_2 := h614c.2.2.1
                have p614_3 := h614c.2.2.2
                linarith only [hlam, p614_0]
              · have p614_0 := h614c.1
                have p614_1 := h614c.2.1
                have p614_2 := h614c.2.2.1
                have p614_3 := h614c.2.2.2
                linarith only [h0, hlam, p614_1]
              · have p614_0 := h614c.1
                have p614_1 := h614c.2.1
                have p614_2 := h614c.2.2.1
                have p614_3 := h614c.2.2.2
                linarith only [hc25, hlam, hphi, ht0b, ht5b, p614_1, u0elo4]
              · have p614_0 := h614c.1
                have p614_1 := h614c.2.1
                have p614_2 := h614c.2.2.1
                have p614_3 := h614c.2.2.2
                linarith only [hc35, hlam, hphi, ht0b, ht5b, p614_1, u0elo4]
              · have p614_0 := h614c.1
                have p614_1 := h614c.2.1
                have p614_2 := h614c.2.2.1
                have p614_3 := h614c.2.2.2
                linarith only [h499, hlam, p614_1]
              · have p614_0 := h614c.1
                have p614_1 := h614c.2.1
                have p614_2 := h614c.2.2.1
                have p614_3 := h614c.2.2.2
                linarith only [h0, hc01, hc15, hlam, hphi, p614_1]
              · have p614_0 := h614c.1
                have p614_1 := h614c.2.1
                have p614_2 := h614c.2.2.1
                have p614_3 := h614c.2.2.2
                linarith only [hlam, p614_0]
              · have p614_0 := h614c.1
                have p614_1 := h614c.2.1
                have p614_2 := h614c.2.2.1
                have p614_3 := h614c.2.2.2
                linarith only [h609, h610, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p614_1, u3elo1]
              · have p614_0 := h614c.1
                have p614_1 := h614c.2.1
                have p614_2 := h614c.2.2.1
                have p614_3 := h614c.2.2.2
                linarith only [h609, h612, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p614_1, u3elo1]
              · have p614_0 := h614c.1
                have p614_1 := h614c.2.1
                have p614_2 := h614c.2.2.1
                have p614_3 := h614c.2.2.2
                linarith only [h609, h610, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p614_1, u3elo1]
              · have p614_0 := h614c.1
                have p614_1 := h614c.2.1
                have p614_2 := h614c.2.2.1
                have p614_3 := h614c.2.2.2
                linarith only [h497, hlam, p614_1]
              · have p614_0 := h614c.1
                have p614_1 := h614c.2.1
                have p614_2 := h614c.2.2.1
                have p614_3 := h614c.2.2.2
                linarith only [hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p614_1, u2elo4]
              · have p614_0 := h614c.1
                have p614_1 := h614c.2.1
                have p614_2 := h614c.2.2.1
                have p614_3 := h614c.2.2.2
                linarith only [hlam, p614_0]
              · have p614_0 := h614c.1
                have p614_1 := h614c.2.1
                have p614_2 := h614c.2.2.1
                have p614_3 := h614c.2.2.2
                linarith only [h497, h612, hc34, hlam, hphi, ht0b, ht45, ht5b, p614_1, u0elo4]
              · have p614_0 := h614c.1
                have p614_1 := h614c.2.1
                have p614_2 := h614c.2.2.1
                have p614_3 := h614c.2.2.2
                linarith only [h610, hlam, p614_1]
              · have p614_0 := h614c.1
                have p614_1 := h614c.2.1
                have p614_2 := h614c.2.2.1
                have p614_3 := h614c.2.2.2
                linarith only [h498, hlam, p614_0]
              · have p614_0 := h614c.1
                have p614_1 := h614c.2.1
                have p614_2 := h614c.2.2.1
                have p614_3 := h614c.2.2.2
                linarith only [h609, hlam, p614_0]
              · have p614_0 := h614c.1
                have p614_1 := h614c.2.1
                have p614_2 := h614c.2.2.1
                have p614_3 := h614c.2.2.2
                linarith only [hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p614_1, u3elo4]
              · have p614_0 := h614c.1
                have p614_1 := h614c.2.1
                have p614_2 := h614c.2.2.1
                have p614_3 := h614c.2.2.2
                linarith only [hlam, p614_0]
              · have p614_0 := h614c.1
                have p614_1 := h614c.2.1
                have p614_2 := h614c.2.2.1
                have p614_3 := h614c.2.2.2
                linarith only [h612, hlam, p614_1]
              · have p614_0 := h614c.1
                have p614_1 := h614c.2.1
                have p614_2 := h614c.2.2.1
                have p614_3 := h614c.2.2.2
                linarith only [h0, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p614_1]
              · have p614_0 := h614c.1
                have p614_1 := h614c.2.1
                have p614_2 := h614c.2.2.1
                have p614_3 := h614c.2.2.2
                linarith only [h0, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p614_1]
              · have p614_0 := h614c.1
                have p614_1 := h614c.2.1
                have p614_2 := h614c.2.2.1
                have p614_3 := h614c.2.2.2
                linarith only [h610, hc24, hc45, hlam, hphi, p614_1]
              · have p614_0 := h614c.1
                have p614_1 := h614c.2.1
                have p614_2 := h614c.2.2.1
                have p614_3 := h614c.2.2.2
                linarith only [h612, hc34, hc45, hlam, hphi, p614_1]
              · have p614_0 := h614c.1
                have p614_1 := h614c.2.1
                have p614_2 := h614c.2.2.1
                have p614_3 := h614c.2.2.2
                linarith only [hlam, p614_0]
        · linarith only [h498, h609, hc13, hlam, hphi, u3elo0]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h641 | h641
      · rcases m.htr 1 3 5 (by decide) (by decide) with h642 | h642
        · linarith only [h498, h642, hc03, hlam, hphi, u3elo1]
        · rcases m.htr 2 4 5 (by decide) (by decide) with h644 | h644
          · rcases m.htr 3 4 5 (by decide) (by decide) with h645 | h645
            · rcases h5bigk with h646c | h646c | h646c | h646c | h646c | h646c | h646c | h646c | h646c | h646c | h646c | h646c | h646c | h646c | h646c | h646c | h646c | h646c | h646c | h646c | h646c | h646c | h646c | h646c | h646c
              · have p646_0 := h646c.1
                have p646_1 := h646c.2.1
                have p646_2 := h646c.2.2.1
                have p646_3 := h646c.2.2.2
                linarith only [hlam, p646_0]
              · have p646_0 := h646c.1
                have p646_1 := h646c.2.1
                have p646_2 := h646c.2.2.1
                have p646_3 := h646c.2.2.2
                linarith only [h0, hlam, p646_1]
              · have p646_0 := h646c.1
                have p646_1 := h646c.2.1
                have p646_2 := h646c.2.2.1
                have p646_3 := h646c.2.2.2
                linarith only [hc25, hlam, hphi, ht0b, ht5b, p646_1, u0elo4]
              · have p646_0 := h646c.1
                have p646_1 := h646c.2.1
                have p646_2 := h646c.2.2.1
                have p646_3 := h646c.2.2.2
                linarith only [h498, hlam, p646_1]
              · have p646_0 := h646c.1
                have p646_1 := h646c.2.1
                have p646_2 := h646c.2.2.1
                have p646_3 := h646c.2.2.2
                linarith only [h641, hc45, hlam, hphi, ht0b, ht5b, p646_1, u0elo3]
              · have p646_0 := h646c.1
                have p646_1 := h646c.2.1
                have p646_2 := h646c.2.2.1
                have p646_3 := h646c.2.2.2
                linarith only [h642, h645, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p646_1, u3elo3]
              · have p646_0 := h646c.1
                have p646_1 := h646c.2.1
                have p646_2 := h646c.2.2.1
                have p646_3 := h646c.2.2.2
                linarith only [hlam, p646_0]
              · have p646_0 := h646c.1
                have p646_1 := h646c.2.1
                have p646_2 := h646c.2.2.1
                have p646_3 := h646c.2.2.2
                linarith only [h642, h644, h645, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p646_1, u3elo3]
              · have p646_0 := h646c.1
                have p646_1 := h646c.2.1
                have p646_2 := h646c.2.2.1
                have p646_3 := h646c.2.2.2
                linarith only [h642, hlam, p646_1]
              · have p646_0 := h646c.1
                have p646_1 := h646c.2.1
                have p646_2 := h646c.2.2.1
                have p646_3 := h646c.2.2.2
                linarith only [h642, h645, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p646_1, u3elo3]
              · have p646_0 := h646c.1
                have p646_1 := h646c.2.1
                have p646_2 := h646c.2.2.1
                have p646_3 := h646c.2.2.2
                linarith only [h497, hlam, p646_1]
              · have p646_0 := h646c.1
                have p646_1 := h646c.2.1
                have p646_2 := h646c.2.2.1
                have p646_3 := h646c.2.2.2
                linarith only [hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p646_1, u2elo4]
              · have p646_0 := h646c.1
                have p646_1 := h646c.2.1
                have p646_2 := h646c.2.2.1
                have p646_3 := h646c.2.2.2
                linarith only [hlam, p646_0]
              · have p646_0 := h646c.1
                have p646_1 := h646c.2.1
                have p646_2 := h646c.2.2.1
                have p646_3 := h646c.2.2.2
                linarith only [h497, h642, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p646_1, u0elo4]
              · have p646_0 := h646c.1
                have p646_1 := h646c.2.1
                have p646_2 := h646c.2.2.1
                have p646_3 := h646c.2.2.2
                linarith only [h497, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p646_1, u2elo0]
              · have p646_0 := h646c.1
                have p646_1 := h646c.2.1
                have p646_2 := h646c.2.2.1
                have p646_3 := h646c.2.2.2
                linarith only [hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p646_1, u3elo4]
              · have p646_0 := h646c.1
                have p646_1 := h646c.2.1
                have p646_2 := h646c.2.2.1
                have p646_3 := h646c.2.2.2
                linarith only [h0, hc01, hlam, hphi, ht12, ht23, p646_1, u3elo4]
              · have p646_0 := h646c.1
                have p646_1 := h646c.2.1
                have p646_2 := h646c.2.2.1
                have p646_3 := h646c.2.2.2
                linarith only [h644, h645, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p646_1, u3elo3]
              · have p646_0 := h646c.1
                have p646_1 := h646c.2.1
                have p646_2 := h646c.2.2.1
                have p646_3 := h646c.2.2.2
                linarith only [hlam, p646_0]
              · have p646_0 := h646c.1
                have p646_1 := h646c.2.1
                have p646_2 := h646c.2.2.1
                have p646_3 := h646c.2.2.2
                linarith only [h645, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p646_1, u3elo3]
              · have p646_0 := h646c.1
                have p646_1 := h646c.2.1
                have p646_2 := h646c.2.2.1
                have p646_3 := h646c.2.2.2
                linarith only [h641, hlam, p646_0]
              · have p646_0 := h646c.1
                have p646_1 := h646c.2.1
                have p646_2 := h646c.2.2.1
                have p646_3 := h646c.2.2.2
                linarith only [h0, h644, hc01, hlam, hphi, ht12, p646_1, u2elo3]
              · have p646_0 := h646c.1
                have p646_1 := h646c.2.1
                have p646_2 := h646c.2.2.1
                have p646_3 := h646c.2.2.2
                linarith only [h644, hlam, p646_0]
              · have p646_0 := h646c.1
                have p646_1 := h646c.2.1
                have p646_2 := h646c.2.2.1
                have p646_3 := h646c.2.2.2
                linarith only [h645, hlam, p646_0]
              · have p646_0 := h646c.1
                have p646_1 := h646c.2.1
                have p646_2 := h646c.2.2.1
                have p646_3 := h646c.2.2.2
                linarith only [hlam, p646_0]
            · linarith only [h497, h498, h644, h645, hlam]
          · rcases m.htr 3 4 5 (by decide) (by decide) with h673 | h673
            · rcases h5bigk with h674c | h674c | h674c | h674c | h674c | h674c | h674c | h674c | h674c | h674c | h674c | h674c | h674c | h674c | h674c | h674c | h674c | h674c | h674c | h674c | h674c | h674c | h674c | h674c | h674c
              · have p674_0 := h674c.1
                have p674_1 := h674c.2.1
                have p674_2 := h674c.2.2.1
                have p674_3 := h674c.2.2.2
                linarith only [hlam, p674_0]
              · have p674_0 := h674c.1
                have p674_1 := h674c.2.1
                have p674_2 := h674c.2.2.1
                have p674_3 := h674c.2.2.2
                linarith only [h0, hlam, p674_1]
              · have p674_0 := h674c.1
                have p674_1 := h674c.2.1
                have p674_2 := h674c.2.2.1
                have p674_3 := h674c.2.2.2
                linarith only [hc25, hlam, hphi, ht0b, ht5b, p674_1, u0elo4]
              · have p674_0 := h674c.1
                have p674_1 := h674c.2.1
                have p674_2 := h674c.2.2.1
                have p674_3 := h674c.2.2.2
                linarith only [h498, hlam, p674_1]
              · have p674_0 := h674c.1
                have p674_1 := h674c.2.1
                have p674_2 := h674c.2.2.1
                have p674_3 := h674c.2.2.2
                linarith only [h644, hc24, hlam, hphi, ht0b, ht45, ht5b, p674_1, u0elo4]
              · have p674_0 := h674c.1
                have p674_1 := h674c.2.1
                have p674_2 := h674c.2.2.1
                have p674_3 := h674c.2.2.2
                linarith only [h642, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p674_1, u3elo4]
              · have p674_0 := h674c.1
                have p674_1 := h674c.2.1
                have p674_2 := h674c.2.2.1
                have p674_3 := h674c.2.2.2
                linarith only [hlam, p674_0]
              · have p674_0 := h674c.1
                have p674_1 := h674c.2.1
                have p674_2 := h674c.2.2.1
                have p674_3 := h674c.2.2.2
                linarith only [h642, h644, h673, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p674_1, u3elo3]
              · have p674_0 := h674c.1
                have p674_1 := h674c.2.1
                have p674_2 := h674c.2.2.1
                have p674_3 := h674c.2.2.2
                linarith only [h642, hlam, p674_1]
              · have p674_0 := h674c.1
                have p674_1 := h674c.2.1
                have p674_2 := h674c.2.2.1
                have p674_3 := h674c.2.2.2
                linarith only [h642, h644, h673, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p674_1, u3elo3]
              · have p674_0 := h674c.1
                have p674_1 := h674c.2.1
                have p674_2 := h674c.2.2.1
                have p674_3 := h674c.2.2.2
                linarith only [h497, hlam, p674_1]
              · have p674_0 := h674c.1
                have p674_1 := h674c.2.1
                have p674_2 := h674c.2.2.1
                have p674_3 := h674c.2.2.2
                linarith only [hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p674_1, u2elo4]
              · have p674_0 := h674c.1
                have p674_1 := h674c.2.1
                have p674_2 := h674c.2.2.1
                have p674_3 := h674c.2.2.2
                linarith only [hlam, p674_0]
              · have p674_0 := h674c.1
                have p674_1 := h674c.2.1
                have p674_2 := h674c.2.2.1
                have p674_3 := h674c.2.2.2
                linarith only [h641, h644, hc35, hlam, hphi, ht0b, ht5b, p674_1, u0elo4]
              · have p674_0 := h674c.1
                have p674_1 := h674c.2.1
                have p674_2 := h674c.2.2.1
                have p674_3 := h674c.2.2.2
                linarith only [h644, hlam, p674_1]
              · have p674_0 := h674c.1
                have p674_1 := h674c.2.1
                have p674_2 := h674c.2.2.1
                have p674_3 := h674c.2.2.2
                linarith only [h641, h644, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p674_1, u3elo4]
              · have p674_0 := h674c.1
                have p674_1 := h674c.2.1
                have p674_2 := h674c.2.2.1
                have p674_3 := h674c.2.2.2
                linarith only [h0, hc01, hlam, hphi, ht12, ht23, p674_1, u3elo4]
              · have p674_0 := h674c.1
                have p674_1 := h674c.2.1
                have p674_2 := h674c.2.2.1
                have p674_3 := h674c.2.2.2
                linarith only [h644, h673, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p674_1, u3elo3]
              · have p674_0 := h674c.1
                have p674_1 := h674c.2.1
                have p674_2 := h674c.2.2.1
                have p674_3 := h674c.2.2.2
                linarith only [hlam, p674_0]
              · have p674_0 := h674c.1
                have p674_1 := h674c.2.1
                have p674_2 := h674c.2.2.1
                have p674_3 := h674c.2.2.2
                linarith only [h644, h673, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p674_1, u3elo3]
              · have p674_0 := h674c.1
                have p674_1 := h674c.2.1
                have p674_2 := h674c.2.2.1
                have p674_3 := h674c.2.2.2
                linarith only [h641, hlam, p674_0]
              · have p674_0 := h674c.1
                have p674_1 := h674c.2.1
                have p674_2 := h674c.2.2.1
                have p674_3 := h674c.2.2.2
                linarith only [h0, h641, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p674_1, u0elo4]
              · have p674_0 := h674c.1
                have p674_1 := h674c.2.1
                have p674_2 := h674c.2.2.1
                have p674_3 := h674c.2.2.2
                linarith only [h641, h644, hc24, hlam, hphi, ht0b, ht45, ht5b, p674_1, u0elo3]
              · have p674_0 := h674c.1
                have p674_1 := h674c.2.1
                have p674_2 := h674c.2.2.1
                have p674_3 := h674c.2.2.2
                linarith only [h673, hlam, p674_0]
              · have p674_0 := h674c.1
                have p674_1 := h674c.2.1
                have p674_2 := h674c.2.2.1
                have p674_3 := h674c.2.2.2
                linarith only [hlam, p674_0]
            · linarith only [h0, h641, h642, h673, hlam]
      · rcases m.htr 1 3 5 (by decide) (by decide) with h701 | h701
        · linarith only [h498, h701, hc03, hlam, hphi, u3elo1]
        · rcases m.htr 2 4 5 (by decide) (by decide) with h703 | h703
          · linarith only [h497, h641, h703, hlam]
          · rcases m.htr 3 4 5 (by decide) (by decide) with h705 | h705
            · rcases h5bigk with h706c | h706c | h706c | h706c | h706c | h706c | h706c | h706c | h706c | h706c | h706c | h706c | h706c | h706c | h706c | h706c | h706c | h706c | h706c | h706c | h706c | h706c | h706c | h706c | h706c
              · have p706_0 := h706c.1
                have p706_1 := h706c.2.1
                have p706_2 := h706c.2.2.1
                have p706_3 := h706c.2.2.2
                linarith only [hlam, p706_0]
              · have p706_0 := h706c.1
                have p706_1 := h706c.2.1
                have p706_2 := h706c.2.2.1
                have p706_3 := h706c.2.2.2
                linarith only [h0, hlam, p706_1]
              · have p706_0 := h706c.1
                have p706_1 := h706c.2.1
                have p706_2 := h706c.2.2.1
                have p706_3 := h706c.2.2.2
                linarith only [hc25, hlam, hphi, ht0b, ht5b, p706_1, u0elo4]
              · have p706_0 := h706c.1
                have p706_1 := h706c.2.1
                have p706_2 := h706c.2.2.1
                have p706_3 := h706c.2.2.2
                linarith only [h498, hlam, p706_1]
              · have p706_0 := h706c.1
                have p706_1 := h706c.2.1
                have p706_2 := h706c.2.2.1
                have p706_3 := h706c.2.2.2
                linarith only [h641, hlam, p706_1]
              · have p706_0 := h706c.1
                have p706_1 := h706c.2.1
                have p706_2 := h706c.2.2.1
                have p706_3 := h706c.2.2.2
                linarith only [h701, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p706_1, u3elo4]
              · have p706_0 := h706c.1
                have p706_1 := h706c.2.1
                have p706_2 := h706c.2.2.1
                have p706_3 := h706c.2.2.2
                linarith only [hlam, p706_0]
              · have p706_0 := h706c.1
                have p706_1 := h706c.2.1
                have p706_2 := h706c.2.2.1
                have p706_3 := h706c.2.2.2
                linarith only [h701, h703, h705, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p706_1, u3elo3]
              · have p706_0 := h706c.1
                have p706_1 := h706c.2.1
                have p706_2 := h706c.2.2.1
                have p706_3 := h706c.2.2.2
                linarith only [h701, hlam, p706_1]
              · have p706_0 := h706c.1
                have p706_1 := h706c.2.1
                have p706_2 := h706c.2.2.1
                have p706_3 := h706c.2.2.2
                linarith only [h641, h701, h705, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p706_1, u3elo3]
              · have p706_0 := h706c.1
                have p706_1 := h706c.2.1
                have p706_2 := h706c.2.2.1
                have p706_3 := h706c.2.2.2
                linarith only [h497, hlam, p706_1]
              · have p706_0 := h706c.1
                have p706_1 := h706c.2.1
                have p706_2 := h706c.2.2.1
                have p706_3 := h706c.2.2.2
                linarith only [hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p706_1, u2elo4]
              · have p706_0 := h706c.1
                have p706_1 := h706c.2.1
                have p706_2 := h706c.2.2.1
                have p706_3 := h706c.2.2.2
                linarith only [hlam, p706_0]
              · have p706_0 := h706c.1
                have p706_1 := h706c.2.1
                have p706_2 := h706c.2.2.1
                have p706_3 := h706c.2.2.2
                linarith only [h497, h701, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p706_1, u0elo4]
              · have p706_0 := h706c.1
                have p706_1 := h706c.2.1
                have p706_2 := h706c.2.2.1
                have p706_3 := h706c.2.2.2
                linarith only [h703, hlam, p706_1]
              · have p706_0 := h706c.1
                have p706_1 := h706c.2.1
                have p706_2 := h706c.2.2.1
                have p706_3 := h706c.2.2.2
                linarith only [hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p706_1, u3elo4]
              · have p706_0 := h706c.1
                have p706_1 := h706c.2.1
                have p706_2 := h706c.2.2.1
                have p706_3 := h706c.2.2.2
                linarith only [h0, hc01, hlam, hphi, ht12, ht23, p706_1, u3elo4]
              · have p706_0 := h706c.1
                have p706_1 := h706c.2.1
                have p706_2 := h706c.2.2.1
                have p706_3 := h706c.2.2.2
                linarith only [h705, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p706_1, u3elo3]
              · have p706_0 := h706c.1
                have p706_1 := h706c.2.1
                have p706_2 := h706c.2.2.1
                have p706_3 := h706c.2.2.2
                linarith only [hlam, p706_0]
              · have p706_0 := h706c.1
                have p706_1 := h706c.2.1
                have p706_2 := h706c.2.2.1
                have p706_3 := h706c.2.2.2
                linarith only [h641, h705, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p706_1, u3elo3]
              · have p706_0 := h706c.1
                have p706_1 := h706c.2.1
                have p706_2 := h706c.2.2.1
                have p706_3 := h706c.2.2.2
                linarith only [h0, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p706_1]
              · have p706_0 := h706c.1
                have p706_1 := h706c.2.1
                have p706_2 := h706c.2.2.1
                have p706_3 := h706c.2.2.2
                linarith only [h0, h705, hc01, hlam, hphi, ht12, ht23, p706_1, u3elo3]
              · have p706_0 := h706c.1
                have p706_1 := h706c.2.1
                have p706_2 := h706c.2.2.1
                have p706_3 := h706c.2.2.2
                linarith only [h703, h705, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p706_1, u3elo3]
              · have p706_0 := h706c.1
                have p706_1 := h706c.2.1
                have p706_2 := h706c.2.2.1
                have p706_3 := h706c.2.2.2
                linarith only [h705, hlam, p706_0]
              · have p706_0 := h706c.1
                have p706_1 := h706c.2.1
                have p706_2 := h706c.2.2.1
                have p706_3 := h706c.2.2.2
                linarith only [hlam, p706_0]
            · rcases h5bigk with h732c | h732c | h732c | h732c | h732c | h732c | h732c | h732c | h732c | h732c | h732c | h732c | h732c | h732c | h732c | h732c | h732c | h732c | h732c | h732c | h732c | h732c | h732c | h732c | h732c
              · have p732_0 := h732c.1
                have p732_1 := h732c.2.1
                have p732_2 := h732c.2.2.1
                have p732_3 := h732c.2.2.2
                linarith only [hlam, p732_0]
              · have p732_0 := h732c.1
                have p732_1 := h732c.2.1
                have p732_2 := h732c.2.2.1
                have p732_3 := h732c.2.2.2
                linarith only [h0, hlam, p732_1]
              · have p732_0 := h732c.1
                have p732_1 := h732c.2.1
                have p732_2 := h732c.2.2.1
                have p732_3 := h732c.2.2.2
                linarith only [h703, hc24, hlam, hphi, ht0b, ht45, ht5b, p732_1, u0elo4]
              · have p732_0 := h732c.1
                have p732_1 := h732c.2.1
                have p732_2 := h732c.2.2.1
                have p732_3 := h732c.2.2.2
                linarith only [h498, hlam, p732_1]
              · have p732_0 := h732c.1
                have p732_1 := h732c.2.1
                have p732_2 := h732c.2.2.1
                have p732_3 := h732c.2.2.2
                linarith only [h641, hlam, p732_1]
              · have p732_0 := h732c.1
                have p732_1 := h732c.2.1
                have p732_2 := h732c.2.2.1
                have p732_3 := h732c.2.2.2
                linarith only [h0, hc01, hc15, hlam, hphi, p732_1]
              · have p732_0 := h732c.1
                have p732_1 := h732c.2.1
                have p732_2 := h732c.2.2.1
                have p732_3 := h732c.2.2.2
                linarith only [hlam, p732_0]
              · have p732_0 := h732c.1
                have p732_1 := h732c.2.1
                have p732_2 := h732c.2.2.1
                have p732_3 := h732c.2.2.2
                linarith only [h701, h703, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p732_1, u3elo4]
              · have p732_0 := h732c.1
                have p732_1 := h732c.2.1
                have p732_2 := h732c.2.2.1
                have p732_3 := h732c.2.2.2
                linarith only [h701, hlam, p732_1]
              · have p732_0 := h732c.1
                have p732_1 := h732c.2.1
                have p732_2 := h732c.2.2.1
                have p732_3 := h732c.2.2.2
                linarith only [h701, h705, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p732_1, u3elo4]
              · have p732_0 := h732c.1
                have p732_1 := h732c.2.1
                have p732_2 := h732c.2.2.1
                have p732_3 := h732c.2.2.2
                linarith only [h497, hlam, p732_1]
              · have p732_0 := h732c.1
                have p732_1 := h732c.2.1
                have p732_2 := h732c.2.2.1
                have p732_3 := h732c.2.2.2
                linarith only [hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p732_1, u2elo4]
              · have p732_0 := h732c.1
                have p732_1 := h732c.2.1
                have p732_2 := h732c.2.2.1
                have p732_3 := h732c.2.2.2
                linarith only [hlam, p732_0]
              · have p732_0 := h732c.1
                have p732_1 := h732c.2.1
                have p732_2 := h732c.2.2.1
                have p732_3 := h732c.2.2.2
                linarith only [hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p732_1, u2elo4]
              · have p732_0 := h732c.1
                have p732_1 := h732c.2.1
                have p732_2 := h732c.2.2.1
                have p732_3 := h732c.2.2.2
                linarith only [h703, hlam, p732_1]
              · have p732_0 := h732c.1
                have p732_1 := h732c.2.1
                have p732_2 := h732c.2.2.1
                have p732_3 := h732c.2.2.2
                linarith only [hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p732_1, u3elo4]
              · have p732_0 := h732c.1
                have p732_1 := h732c.2.1
                have p732_2 := h732c.2.2.1
                have p732_3 := h732c.2.2.2
                linarith only [h0, hc01, hlam, hphi, ht12, ht23, p732_1, u3elo4]
              · have p732_0 := h732c.1
                have p732_1 := h732c.2.1
                have p732_2 := h732c.2.2.1
                have p732_3 := h732c.2.2.2
                linarith only [h703, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p732_1, u3elo4]
              · have p732_0 := h732c.1
                have p732_1 := h732c.2.1
                have p732_2 := h732c.2.2.1
                have p732_3 := h732c.2.2.2
                linarith only [hlam, p732_0]
              · have p732_0 := h732c.1
                have p732_1 := h732c.2.1
                have p732_2 := h732c.2.2.1
                have p732_3 := h732c.2.2.2
                linarith only [h705, hlam, p732_1]
              · have p732_0 := h732c.1
                have p732_1 := h732c.2.1
                have p732_2 := h732c.2.2.1
                have p732_3 := h732c.2.2.2
                linarith only [h0, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p732_1]
              · have p732_0 := h732c.1
                have p732_1 := h732c.2.1
                have p732_2 := h732c.2.2.1
                have p732_3 := h732c.2.2.2
                linarith only [h0, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p732_1]
              · have p732_0 := h732c.1
                have p732_1 := h732c.2.1
                have p732_2 := h732c.2.2.1
                have p732_3 := h732c.2.2.2
                linarith only [h703, hc24, hc45, hlam, hphi, p732_1]
              · have p732_0 := h732c.1
                have p732_1 := h732c.2.1
                have p732_2 := h732c.2.2.1
                have p732_3 := h732c.2.2.2
                linarith only [h498, hc03, hc45, hlam, hphi, ht34, p732_1]
              · have p732_0 := h732c.1
                have p732_1 := h732c.2.1
                have p732_2 := h732c.2.2.1
                have p732_3 := h732c.2.2.2
                linarith only [hlam, p732_0]
  · rcases m.htr 0 3 5 (by decide) (by decide) with h758 | h758
    · rcases m.htr 0 4 5 (by decide) (by decide) with h759 | h759
      · rcases m.htr 1 3 5 (by decide) (by decide) with h760 | h760
        · rcases m.htr 2 4 5 (by decide) (by decide) with h761 | h761
          · rcases m.htr 3 4 5 (by decide) (by decide) with h762 | h762
            · rcases h5bigk with h763c | h763c | h763c | h763c | h763c | h763c | h763c | h763c | h763c | h763c | h763c | h763c | h763c | h763c | h763c | h763c | h763c | h763c | h763c | h763c | h763c | h763c | h763c | h763c | h763c
              · have p763_0 := h763c.1
                have p763_1 := h763c.2.1
                have p763_2 := h763c.2.2.1
                have p763_3 := h763c.2.2.2
                linarith only [hlam, p763_0]
              · have p763_0 := h763c.1
                have p763_1 := h763c.2.1
                have p763_2 := h763c.2.2.1
                have p763_3 := h763c.2.2.2
                linarith only [h0, hlam, p763_1]
              · have p763_0 := h763c.1
                have p763_1 := h763c.2.1
                have p763_2 := h763c.2.2.1
                have p763_3 := h763c.2.2.2
                linarith only [h497, hlam, p763_0]
              · have p763_0 := h763c.1
                have p763_1 := h763c.2.1
                have p763_2 := h763c.2.2.1
                have p763_3 := h763c.2.2.2
                linarith only [h762, hc45, hlam, hphi, ht0b, ht5b, p763_1, u0elo4]
              · have p763_0 := h763c.1
                have p763_1 := h763c.2.1
                have p763_2 := h763c.2.2.1
                have p763_3 := h763c.2.2.2
                linarith only [h0, h760, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p763_1, u3elo1]
              · have p763_0 := h763c.1
                have p763_1 := h763c.2.1
                have p763_2 := h763c.2.2.1
                have p763_3 := h763c.2.2.2
                linarith only [h760, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p763_1, u3elo1]
              · have p763_0 := h763c.1
                have p763_1 := h763c.2.1
                have p763_2 := h763c.2.2.1
                have p763_3 := h763c.2.2.2
                linarith only [hlam, p763_0]
              · have p763_0 := h763c.1
                have p763_1 := h763c.2.1
                have p763_2 := h763c.2.2.1
                have p763_3 := h763c.2.2.2
                linarith only [h760, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p763_1, u3elo1]
              · have p763_0 := h763c.1
                have p763_1 := h763c.2.1
                have p763_2 := h763c.2.2.1
                have p763_3 := h763c.2.2.2
                linarith only [h760, h762, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p763_1, u3elo1]
              · have p763_0 := h763c.1
                have p763_1 := h763c.2.1
                have p763_2 := h763c.2.2.1
                have p763_3 := h763c.2.2.2
                linarith only [h760, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p763_1, u3elo1]
              · have p763_0 := h763c.1
                have p763_1 := h763c.2.1
                have p763_2 := h763c.2.2.1
                have p763_3 := h763c.2.2.2
                linarith only [h0, hc01, hlam, hphi, ht12, p763_1, u2elo4]
              · have p763_0 := h763c.1
                have p763_1 := h763c.2.1
                have p763_2 := h763c.2.2.1
                have p763_3 := h763c.2.2.2
                linarith only [h761, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p763_1, u2elo3]
              · have p763_0 := h763c.1
                have p763_1 := h763c.2.1
                have p763_2 := h763c.2.2.1
                have p763_3 := h763c.2.2.2
                linarith only [hlam, p763_0]
              · have p763_0 := h763c.1
                have p763_1 := h763c.2.1
                have p763_2 := h763c.2.2.1
                have p763_3 := h763c.2.2.2
                linarith only [h761, h762, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p763_1, u2elo3]
              · have p763_0 := h763c.1
                have p763_1 := h763c.2.1
                have p763_2 := h763c.2.2.1
                have p763_3 := h763c.2.2.2
                linarith only [h761, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p763_1, u2elo3]
              · have p763_0 := h763c.1
                have p763_1 := h763c.2.1
                have p763_2 := h763c.2.2.1
                have p763_3 := h763c.2.2.2
                linarith only [h758, hlam, p763_0]
              · have p763_0 := h763c.1
                have p763_1 := h763c.2.1
                have p763_2 := h763c.2.2.1
                have p763_3 := h763c.2.2.2
                linarith only [h760, hlam, p763_0]
              · have p763_0 := h763c.1
                have p763_1 := h763c.2.1
                have p763_2 := h763c.2.2.1
                have p763_3 := h763c.2.2.2
                linarith only [h758, hc25, hlam, hphi, ht0b, ht5b, p763_1, u0elo2]
              · have p763_0 := h763c.1
                have p763_1 := h763c.2.1
                have p763_2 := h763c.2.2.1
                have p763_3 := h763c.2.2.2
                linarith only [hlam, p763_0]
              · have p763_0 := h763c.1
                have p763_1 := h763c.2.1
                have p763_2 := h763c.2.2.1
                have p763_3 := h763c.2.2.2
                linarith only [h758, hc45, hlam, hphi, ht0b, ht5b, p763_1, u0elo4]
              · have p763_0 := h763c.1
                have p763_1 := h763c.2.1
                have p763_2 := h763c.2.2.1
                have p763_3 := h763c.2.2.2
                linarith only [h759, hlam, p763_0]
              · have p763_0 := h763c.1
                have p763_1 := h763c.2.1
                have p763_2 := h763c.2.2.1
                have p763_3 := h763c.2.2.2
                linarith only [h0, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p763_1]
              · have p763_0 := h763c.1
                have p763_1 := h763c.2.1
                have p763_2 := h763c.2.2.1
                have p763_3 := h763c.2.2.2
                linarith only [h761, hlam, p763_0]
              · have p763_0 := h763c.1
                have p763_1 := h763c.2.1
                have p763_2 := h763c.2.2.1
                have p763_3 := h763c.2.2.2
                linarith only [h762, hlam, p763_0]
              · have p763_0 := h763c.1
                have p763_1 := h763c.2.1
                have p763_2 := h763c.2.2.1
                have p763_3 := h763c.2.2.2
                linarith only [hlam, p763_0]
            · rcases h5bigk with h789c | h789c | h789c | h789c | h789c | h789c | h789c | h789c | h789c | h789c | h789c | h789c | h789c | h789c | h789c | h789c | h789c | h789c | h789c | h789c | h789c | h789c | h789c | h789c | h789c
              · have p789_0 := h789c.1
                have p789_1 := h789c.2.1
                have p789_2 := h789c.2.2.1
                have p789_3 := h789c.2.2.2
                linarith only [hlam, p789_0]
              · have p789_0 := h789c.1
                have p789_1 := h789c.2.1
                have p789_2 := h789c.2.2.1
                have p789_3 := h789c.2.2.2
                linarith only [h0, hlam, p789_1]
              · have p789_0 := h789c.1
                have p789_1 := h789c.2.1
                have p789_2 := h789c.2.2.1
                have p789_3 := h789c.2.2.2
                linarith only [h497, hlam, p789_0]
              · have p789_0 := h789c.1
                have p789_1 := h789c.2.1
                have p789_2 := h789c.2.2.1
                have p789_3 := h789c.2.2.2
                linarith only [hc35, hlam, hphi, ht0b, ht5b, p789_1, u0elo4]
              · have p789_0 := h789c.1
                have p789_1 := h789c.2.1
                have p789_2 := h789c.2.2.1
                have p789_3 := h789c.2.2.2
                linarith only [h497, h761, h762, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p789_1, u2elo3]
              · have p789_0 := h789c.1
                have p789_1 := h789c.2.1
                have p789_2 := h789c.2.2.1
                have p789_3 := h789c.2.2.2
                linarith only [h0, hc01, hc15, hlam, hphi, p789_1]
              · have p789_0 := h789c.1
                have p789_1 := h789c.2.1
                have p789_2 := h789c.2.2.1
                have p789_3 := h789c.2.2.2
                linarith only [hlam, p789_0]
              · have p789_0 := h789c.1
                have p789_1 := h789c.2.1
                have p789_2 := h789c.2.2.1
                have p789_3 := h789c.2.2.2
                linarith only [h760, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p789_1, u3elo1]
              · have p789_0 := h789c.1
                have p789_1 := h789c.2.1
                have p789_2 := h789c.2.2.1
                have p789_3 := h789c.2.2.2
                linarith only [h760, h762, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p789_1, u3elo1]
              · have p789_0 := h789c.1
                have p789_1 := h789c.2.1
                have p789_2 := h789c.2.2.1
                have p789_3 := h789c.2.2.2
                linarith only [h760, h762, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p789_1, u3elo1]
              · have p789_0 := h789c.1
                have p789_1 := h789c.2.1
                have p789_2 := h789c.2.2.1
                have p789_3 := h789c.2.2.2
                linarith only [h759, h762, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p789_1, u2elo4]
              · have p789_0 := h789c.1
                have p789_1 := h789c.2.1
                have p789_2 := h789c.2.2.1
                have p789_3 := h789c.2.2.2
                linarith only [h761, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p789_1, u2elo3]
              · have p789_0 := h789c.1
                have p789_1 := h789c.2.1
                have p789_2 := h789c.2.2.1
                have p789_3 := h789c.2.2.2
                linarith only [hlam, p789_0]
              · have p789_0 := h789c.1
                have p789_1 := h789c.2.1
                have p789_2 := h789c.2.2.1
                have p789_3 := h789c.2.2.2
                linarith only [h761, h762, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p789_1, u2elo3]
              · have p789_0 := h789c.1
                have p789_1 := h789c.2.1
                have p789_2 := h789c.2.2.1
                have p789_3 := h789c.2.2.2
                linarith only [h761, h762, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p789_1, u2elo3]
              · have p789_0 := h789c.1
                have p789_1 := h789c.2.1
                have p789_2 := h789c.2.2.1
                have p789_3 := h789c.2.2.2
                linarith only [h758, hlam, p789_0]
              · have p789_0 := h789c.1
                have p789_1 := h789c.2.1
                have p789_2 := h789c.2.2.1
                have p789_3 := h789c.2.2.2
                linarith only [h760, hlam, p789_0]
              · have p789_0 := h789c.1
                have p789_1 := h789c.2.1
                have p789_2 := h789c.2.2.1
                have p789_3 := h789c.2.2.2
                linarith only [hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p789_1, u3elo4]
              · have p789_0 := h789c.1
                have p789_1 := h789c.2.1
                have p789_2 := h789c.2.2.1
                have p789_3 := h789c.2.2.2
                linarith only [hlam, p789_0]
              · have p789_0 := h789c.1
                have p789_1 := h789c.2.1
                have p789_2 := h789c.2.2.1
                have p789_3 := h789c.2.2.2
                linarith only [h762, hlam, p789_1]
              · have p789_0 := h789c.1
                have p789_1 := h789c.2.1
                have p789_2 := h789c.2.2.1
                have p789_3 := h789c.2.2.2
                linarith only [h759, hlam, p789_0]
              · have p789_0 := h789c.1
                have p789_1 := h789c.2.1
                have p789_2 := h789c.2.2.1
                have p789_3 := h789c.2.2.2
                linarith only [h0, h759, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p789_1, u0elo4]
              · have p789_0 := h789c.1
                have p789_1 := h789c.2.1
                have p789_2 := h789c.2.2.1
                have p789_3 := h789c.2.2.2
                linarith only [h761, hlam, p789_0]
              · have p789_0 := h789c.1
                have p789_1 := h789c.2.1
                have p789_2 := h789c.2.2.1
                have p789_3 := h789c.2.2.2
                linarith only [h759, hc35, hlam, hphi, ht0b, ht5b, p789_1, u0elo4]
              · have p789_0 := h789c.1
                have p789_1 := h789c.2.1
                have p789_2 := h789c.2.2.1
                have p789_3 := h789c.2.2.2
                linarith only [hlam, p789_0]
          · linarith only [h497, h759, h761, hlam]
        · linarith only [h758, h760, hc13, hlam, hphi, u3elo0]
      · rcases m.htr 1 3 5 (by decide) (by decide) with h817 | h817
        · rcases m.htr 2 4 5 (by decide) (by decide) with h818 | h818
          · rcases m.htr 3 4 5 (by decide) (by decide) with h819 | h819
            · linarith only [h758, h759, h819, hlam]
            · rcases h5bigk with h821c | h821c | h821c | h821c | h821c | h821c | h821c | h821c | h821c | h821c | h821c | h821c | h821c | h821c | h821c | h821c | h821c | h821c | h821c | h821c | h821c | h821c | h821c | h821c | h821c
              · have p821_0 := h821c.1
                have p821_1 := h821c.2.1
                have p821_2 := h821c.2.2.1
                have p821_3 := h821c.2.2.2
                linarith only [hlam, p821_0]
              · have p821_0 := h821c.1
                have p821_1 := h821c.2.1
                have p821_2 := h821c.2.2.1
                have p821_3 := h821c.2.2.2
                linarith only [h0, hlam, p821_1]
              · have p821_0 := h821c.1
                have p821_1 := h821c.2.1
                have p821_2 := h821c.2.2.1
                have p821_3 := h821c.2.2.2
                linarith only [h497, hlam, p821_0]
              · have p821_0 := h821c.1
                have p821_1 := h821c.2.1
                have p821_2 := h821c.2.2.1
                have p821_3 := h821c.2.2.2
                linarith only [hc35, hlam, hphi, ht0b, ht5b, p821_1, u0elo4]
              · have p821_0 := h821c.1
                have p821_1 := h821c.2.1
                have p821_2 := h821c.2.2.1
                have p821_3 := h821c.2.2.2
                linarith only [h759, hlam, p821_1]
              · have p821_0 := h821c.1
                have p821_1 := h821c.2.1
                have p821_2 := h821c.2.2.1
                have p821_3 := h821c.2.2.2
                linarith only [h0, hc01, hc15, hlam, hphi, p821_1]
              · have p821_0 := h821c.1
                have p821_1 := h821c.2.1
                have p821_2 := h821c.2.2.1
                have p821_3 := h821c.2.2.2
                linarith only [hlam, p821_0]
              · have p821_0 := h821c.1
                have p821_1 := h821c.2.1
                have p821_2 := h821c.2.2.1
                have p821_3 := h821c.2.2.2
                linarith only [h817, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p821_1, u3elo1]
              · have p821_0 := h821c.1
                have p821_1 := h821c.2.1
                have p821_2 := h821c.2.2.1
                have p821_3 := h821c.2.2.2
                linarith only [h817, h819, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p821_1, u3elo1]
              · have p821_0 := h821c.1
                have p821_1 := h821c.2.1
                have p821_2 := h821c.2.2.1
                have p821_3 := h821c.2.2.2
                linarith only [h759, h817, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p821_1, u3elo1]
              · have p821_0 := h821c.1
                have p821_1 := h821c.2.1
                have p821_2 := h821c.2.2.1
                have p821_3 := h821c.2.2.2
                linarith only [h0, hc01, hlam, hphi, ht12, p821_1, u2elo4]
              · have p821_0 := h821c.1
                have p821_1 := h821c.2.1
                have p821_2 := h821c.2.2.1
                have p821_3 := h821c.2.2.2
                linarith only [h818, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p821_1, u2elo3]
              · have p821_0 := h821c.1
                have p821_1 := h821c.2.1
                have p821_2 := h821c.2.2.1
                have p821_3 := h821c.2.2.2
                linarith only [hlam, p821_0]
              · have p821_0 := h821c.1
                have p821_1 := h821c.2.1
                have p821_2 := h821c.2.2.1
                have p821_3 := h821c.2.2.2
                linarith only [h818, h819, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p821_1, u2elo3]
              · have p821_0 := h821c.1
                have p821_1 := h821c.2.1
                have p821_2 := h821c.2.2.1
                have p821_3 := h821c.2.2.2
                linarith only [h759, h818, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p821_1, u2elo3]
              · have p821_0 := h821c.1
                have p821_1 := h821c.2.1
                have p821_2 := h821c.2.2.1
                have p821_3 := h821c.2.2.2
                linarith only [h758, hlam, p821_0]
              · have p821_0 := h821c.1
                have p821_1 := h821c.2.1
                have p821_2 := h821c.2.2.1
                have p821_3 := h821c.2.2.2
                linarith only [h817, hlam, p821_0]
              · have p821_0 := h821c.1
                have p821_1 := h821c.2.1
                have p821_2 := h821c.2.2.1
                have p821_3 := h821c.2.2.2
                linarith only [hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p821_1, u3elo4]
              · have p821_0 := h821c.1
                have p821_1 := h821c.2.1
                have p821_2 := h821c.2.2.1
                have p821_3 := h821c.2.2.2
                linarith only [hlam, p821_0]
              · have p821_0 := h821c.1
                have p821_1 := h821c.2.1
                have p821_2 := h821c.2.2.1
                have p821_3 := h821c.2.2.2
                linarith only [h819, hlam, p821_1]
              · have p821_0 := h821c.1
                have p821_1 := h821c.2.1
                have p821_2 := h821c.2.2.1
                have p821_3 := h821c.2.2.2
                linarith only [h0, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p821_1]
              · have p821_0 := h821c.1
                have p821_1 := h821c.2.1
                have p821_2 := h821c.2.2.1
                have p821_3 := h821c.2.2.2
                linarith only [h0, h818, hc01, hlam, hphi, ht12, p821_1, u2elo3]
              · have p821_0 := h821c.1
                have p821_1 := h821c.2.1
                have p821_2 := h821c.2.2.1
                have p821_3 := h821c.2.2.2
                linarith only [h818, hlam, p821_0]
              · have p821_0 := h821c.1
                have p821_1 := h821c.2.1
                have p821_2 := h821c.2.2.1
                have p821_3 := h821c.2.2.2
                linarith only [h818, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p821_1, u2elo3]
              · have p821_0 := h821c.1
                have p821_1 := h821c.2.1
                have p821_2 := h821c.2.2.1
                have p821_3 := h821c.2.2.2
                linarith only [hlam, p821_0]
          · rcases m.htr 3 4 5 (by decide) (by decide) with h847 | h847
            · linarith only [h497, h818, h847, hc02, hlam, hphi, ht23, u3elo3]
            · rcases h5bigk with h849c | h849c | h849c | h849c | h849c | h849c | h849c | h849c | h849c | h849c | h849c | h849c | h849c | h849c | h849c | h849c | h849c | h849c | h849c | h849c | h849c | h849c | h849c | h849c | h849c
              · have p849_0 := h849c.1
                have p849_1 := h849c.2.1
                have p849_2 := h849c.2.2.1
                have p849_3 := h849c.2.2.2
                linarith only [hlam, p849_0]
              · have p849_0 := h849c.1
                have p849_1 := h849c.2.1
                have p849_2 := h849c.2.2.1
                have p849_3 := h849c.2.2.2
                linarith only [h0, hlam, p849_1]
              · have p849_0 := h849c.1
                have p849_1 := h849c.2.1
                have p849_2 := h849c.2.2.1
                have p849_3 := h849c.2.2.2
                linarith only [h497, hlam, p849_0]
              · have p849_0 := h849c.1
                have p849_1 := h849c.2.1
                have p849_2 := h849c.2.2.1
                have p849_3 := h849c.2.2.2
                linarith only [h847, hc34, hlam, hphi, ht0b, ht45, ht5b, p849_1, u0elo4]
              · have p849_0 := h849c.1
                have p849_1 := h849c.2.1
                have p849_2 := h849c.2.2.1
                have p849_3 := h849c.2.2.2
                linarith only [h759, hlam, p849_1]
              · have p849_0 := h849c.1
                have p849_1 := h849c.2.1
                have p849_2 := h849c.2.2.1
                have p849_3 := h849c.2.2.2
                linarith only [h0, hc01, hc15, hlam, hphi, p849_1]
              · have p849_0 := h849c.1
                have p849_1 := h849c.2.1
                have p849_2 := h849c.2.2.1
                have p849_3 := h849c.2.2.2
                linarith only [hlam, p849_0]
              · have p849_0 := h849c.1
                have p849_1 := h849c.2.1
                have p849_2 := h849c.2.2.1
                have p849_3 := h849c.2.2.2
                linarith only [h497, h817, hc02, hlam, hphi, ht23, p849_1, u3elo1]
              · have p849_0 := h849c.1
                have p849_1 := h849c.2.1
                have p849_2 := h849c.2.2.1
                have p849_3 := h849c.2.2.2
                linarith only [h817, h847, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p849_1, u3elo1]
              · have p849_0 := h849c.1
                have p849_1 := h849c.2.1
                have p849_2 := h849c.2.2.1
                have p849_3 := h849c.2.2.2
                linarith only [h497, h817, h818, hc02, hlam, hphi, ht23, p849_1, u3elo1]
              · have p849_0 := h849c.1
                have p849_1 := h849c.2.1
                have p849_2 := h849c.2.2.1
                have p849_3 := h849c.2.2.2
                linarith only [h0, hc01, hlam, hphi, ht12, p849_1, u2elo4]
              · have p849_0 := h849c.1
                have p849_1 := h849c.2.1
                have p849_2 := h849c.2.2.1
                have p849_3 := h849c.2.2.2
                linarith only [hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p849_1, u2elo4]
              · have p849_0 := h849c.1
                have p849_1 := h849c.2.1
                have p849_2 := h849c.2.2.1
                have p849_3 := h849c.2.2.2
                linarith only [hlam, p849_0]
              · have p849_0 := h849c.1
                have p849_1 := h849c.2.1
                have p849_2 := h849c.2.2.1
                have p849_3 := h849c.2.2.2
                linarith only [h847, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p849_1, u2elo4]
              · have p849_0 := h849c.1
                have p849_1 := h849c.2.1
                have p849_2 := h849c.2.2.1
                have p849_3 := h849c.2.2.2
                linarith only [h818, hlam, p849_1]
              · have p849_0 := h849c.1
                have p849_1 := h849c.2.1
                have p849_2 := h849c.2.2.1
                have p849_3 := h849c.2.2.2
                linarith only [h758, hlam, p849_0]
              · have p849_0 := h849c.1
                have p849_1 := h849c.2.1
                have p849_2 := h849c.2.2.1
                have p849_3 := h849c.2.2.2
                linarith only [h817, hlam, p849_0]
              · have p849_0 := h849c.1
                have p849_1 := h849c.2.1
                have p849_2 := h849c.2.2.1
                have p849_3 := h849c.2.2.2
                linarith only [hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p849_1, u3elo4]
              · have p849_0 := h849c.1
                have p849_1 := h849c.2.1
                have p849_2 := h849c.2.2.1
                have p849_3 := h849c.2.2.2
                linarith only [hlam, p849_0]
              · have p849_0 := h849c.1
                have p849_1 := h849c.2.1
                have p849_2 := h849c.2.2.1
                have p849_3 := h849c.2.2.2
                linarith only [h847, hlam, p849_1]
              · have p849_0 := h849c.1
                have p849_1 := h849c.2.1
                have p849_2 := h849c.2.2.1
                have p849_3 := h849c.2.2.2
                linarith only [h0, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p849_1]
              · have p849_0 := h849c.1
                have p849_1 := h849c.2.1
                have p849_2 := h849c.2.2.1
                have p849_3 := h849c.2.2.2
                linarith only [h0, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p849_1]
              · have p849_0 := h849c.1
                have p849_1 := h849c.2.1
                have p849_2 := h849c.2.2.1
                have p849_3 := h849c.2.2.2
                linarith only [h497, hc02, hc45, hlam, hphi, ht23, ht34, p849_1]
              · have p849_0 := h849c.1
                have p849_1 := h849c.2.1
                have p849_2 := h849c.2.2.1
                have p849_3 := h849c.2.2.2
                linarith only [h847, hc34, hc45, hlam, hphi, p849_1]
              · have p849_0 := h849c.1
                have p849_1 := h849c.2.1
                have p849_2 := h849c.2.2.1
                have p849_3 := h849c.2.2.2
                linarith only [hlam, p849_0]
        · linarith only [h758, h817, hc13, hlam, hphi, u3elo0]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h876 | h876
      · rcases m.htr 1 3 5 (by decide) (by decide) with h877 | h877
        · linarith only [h758, h877, hc03, hlam, hphi, u3elo1]
        · rcases m.htr 2 4 5 (by decide) (by decide) with h879 | h879
          · rcases m.htr 3 4 5 (by decide) (by decide) with h880 | h880
            · rcases h5bigk with h881c | h881c | h881c | h881c | h881c | h881c | h881c | h881c | h881c | h881c | h881c | h881c | h881c | h881c | h881c | h881c | h881c | h881c | h881c | h881c | h881c | h881c | h881c | h881c | h881c
              · have p881_0 := h881c.1
                have p881_1 := h881c.2.1
                have p881_2 := h881c.2.2.1
                have p881_3 := h881c.2.2.2
                linarith only [hlam, p881_0]
              · have p881_0 := h881c.1
                have p881_1 := h881c.2.1
                have p881_2 := h881c.2.2.1
                have p881_3 := h881c.2.2.2
                linarith only [h0, hlam, p881_1]
              · have p881_0 := h881c.1
                have p881_1 := h881c.2.1
                have p881_2 := h881c.2.2.1
                have p881_3 := h881c.2.2.2
                linarith only [h497, hlam, p881_0]
              · have p881_0 := h881c.1
                have p881_1 := h881c.2.1
                have p881_2 := h881c.2.2.1
                have p881_3 := h881c.2.2.2
                linarith only [h758, hlam, p881_1]
              · have p881_0 := h881c.1
                have p881_1 := h881c.2.1
                have p881_2 := h881c.2.2.1
                have p881_3 := h881c.2.2.2
                linarith only [hc45, hlam, hphi, ht0b, ht5b, p881_1, u0elo4]
              · have p881_0 := h881c.1
                have p881_1 := h881c.2.1
                have p881_2 := h881c.2.2.1
                have p881_3 := h881c.2.2.2
                linarith only [h877, h880, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p881_1, u3elo3]
              · have p881_0 := h881c.1
                have p881_1 := h881c.2.1
                have p881_2 := h881c.2.2.1
                have p881_3 := h881c.2.2.2
                linarith only [hlam, p881_0]
              · have p881_0 := h881c.1
                have p881_1 := h881c.2.1
                have p881_2 := h881c.2.2.1
                have p881_3 := h881c.2.2.2
                linarith only [h497, h877, h880, hc02, hlam, hphi, ht23, p881_1, u3elo3]
              · have p881_0 := h881c.1
                have p881_1 := h881c.2.1
                have p881_2 := h881c.2.2.1
                have p881_3 := h881c.2.2.2
                linarith only [h877, hlam, p881_1]
              · have p881_0 := h881c.1
                have p881_1 := h881c.2.1
                have p881_2 := h881c.2.2.1
                have p881_3 := h881c.2.2.2
                linarith only [h877, h880, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p881_1, u3elo3]
              · have p881_0 := h881c.1
                have p881_1 := h881c.2.1
                have p881_2 := h881c.2.2.1
                have p881_3 := h881c.2.2.2
                linarith only [h0, h879, hc01, hlam, hphi, ht12, p881_1, u2elo3]
              · have p881_0 := h881c.1
                have p881_1 := h881c.2.1
                have p881_2 := h881c.2.2.1
                have p881_3 := h881c.2.2.2
                linarith only [h879, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p881_1, u2elo3]
              · have p881_0 := h881c.1
                have p881_1 := h881c.2.1
                have p881_2 := h881c.2.2.1
                have p881_3 := h881c.2.2.2
                linarith only [hlam, p881_0]
              · have p881_0 := h881c.1
                have p881_1 := h881c.2.1
                have p881_2 := h881c.2.2.1
                have p881_3 := h881c.2.2.2
                linarith only [h877, h879, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p881_1, u2elo3]
              · have p881_0 := h881c.1
                have p881_1 := h881c.2.1
                have p881_2 := h881c.2.2.1
                have p881_3 := h881c.2.2.2
                linarith only [h879, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p881_1, u2elo3]
              · have p881_0 := h881c.1
                have p881_1 := h881c.2.1
                have p881_2 := h881c.2.2.1
                have p881_3 := h881c.2.2.2
                linarith only [h0, hc01, hlam, hphi, ht12, ht23, p881_1, u3elo4]
              · have p881_0 := h881c.1
                have p881_1 := h881c.2.1
                have p881_2 := h881c.2.2.1
                have p881_3 := h881c.2.2.2
                linarith only [h0, hc01, hlam, hphi, ht12, ht23, p881_1, u3elo4]
              · have p881_0 := h881c.1
                have p881_1 := h881c.2.1
                have p881_2 := h881c.2.2.1
                have p881_3 := h881c.2.2.2
                linarith only [h880, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p881_1, u3elo3]
              · have p881_0 := h881c.1
                have p881_1 := h881c.2.1
                have p881_2 := h881c.2.2.1
                have p881_3 := h881c.2.2.2
                linarith only [hlam, p881_0]
              · have p881_0 := h881c.1
                have p881_1 := h881c.2.1
                have p881_2 := h881c.2.2.1
                have p881_3 := h881c.2.2.2
                linarith only [h880, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p881_1, u3elo3]
              · have p881_0 := h881c.1
                have p881_1 := h881c.2.1
                have p881_2 := h881c.2.2.1
                have p881_3 := h881c.2.2.2
                linarith only [h876, hlam, p881_0]
              · have p881_0 := h881c.1
                have p881_1 := h881c.2.1
                have p881_2 := h881c.2.2.1
                have p881_3 := h881c.2.2.2
                linarith only [h0, h876, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p881_1, u0elo3]
              · have p881_0 := h881c.1
                have p881_1 := h881c.2.1
                have p881_2 := h881c.2.2.1
                have p881_3 := h881c.2.2.2
                linarith only [h879, hlam, p881_0]
              · have p881_0 := h881c.1
                have p881_1 := h881c.2.1
                have p881_2 := h881c.2.2.1
                have p881_3 := h881c.2.2.2
                linarith only [h880, hlam, p881_0]
              · have p881_0 := h881c.1
                have p881_1 := h881c.2.1
                have p881_2 := h881c.2.2.1
                have p881_3 := h881c.2.2.2
                linarith only [hlam, p881_0]
            · linarith only [h758, h876, h880, hlam]
          · linarith only [h497, h876, h879, hlam]
      · rcases m.htr 1 3 5 (by decide) (by decide) with h909 | h909
        · linarith only [h758, h909, hc03, hlam, hphi, u3elo1]
        · rcases m.htr 2 4 5 (by decide) (by decide) with h911 | h911
          · rcases m.htr 3 4 5 (by decide) (by decide) with h912 | h912
            · rcases h5bigk with h913c | h913c | h913c | h913c | h913c | h913c | h913c | h913c | h913c | h913c | h913c | h913c | h913c | h913c | h913c | h913c | h913c | h913c | h913c | h913c | h913c | h913c | h913c | h913c | h913c
              · have p913_0 := h913c.1
                have p913_1 := h913c.2.1
                have p913_2 := h913c.2.2.1
                have p913_3 := h913c.2.2.2
                linarith only [hlam, p913_0]
              · have p913_0 := h913c.1
                have p913_1 := h913c.2.1
                have p913_2 := h913c.2.2.1
                have p913_3 := h913c.2.2.2
                linarith only [h0, hlam, p913_1]
              · have p913_0 := h913c.1
                have p913_1 := h913c.2.1
                have p913_2 := h913c.2.2.1
                have p913_3 := h913c.2.2.2
                linarith only [h497, hlam, p913_0]
              · have p913_0 := h913c.1
                have p913_1 := h913c.2.1
                have p913_2 := h913c.2.2.1
                have p913_3 := h913c.2.2.2
                linarith only [h758, hlam, p913_1]
              · have p913_0 := h913c.1
                have p913_1 := h913c.2.1
                have p913_2 := h913c.2.2.1
                have p913_3 := h913c.2.2.2
                linarith only [h876, hlam, p913_1]
              · have p913_0 := h913c.1
                have p913_1 := h913c.2.1
                have p913_2 := h913c.2.2.1
                have p913_3 := h913c.2.2.2
                linarith only [h909, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p913_1, u3elo4]
              · have p913_0 := h913c.1
                have p913_1 := h913c.2.1
                have p913_2 := h913c.2.2.1
                have p913_3 := h913c.2.2.2
                linarith only [hlam, p913_0]
              · have p913_0 := h913c.1
                have p913_1 := h913c.2.1
                have p913_2 := h913c.2.2.1
                have p913_3 := h913c.2.2.2
                linarith only [h497, h909, h912, hc02, hlam, hphi, ht23, p913_1, u3elo3]
              · have p913_0 := h913c.1
                have p913_1 := h913c.2.1
                have p913_2 := h913c.2.2.1
                have p913_3 := h913c.2.2.2
                linarith only [h909, hlam, p913_1]
              · have p913_0 := h913c.1
                have p913_1 := h913c.2.1
                have p913_2 := h913c.2.2.1
                have p913_3 := h913c.2.2.2
                linarith only [h876, h909, h912, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p913_1, u3elo3]
              · have p913_0 := h913c.1
                have p913_1 := h913c.2.1
                have p913_2 := h913c.2.2.1
                have p913_3 := h913c.2.2.2
                linarith only [h0, hc01, hlam, hphi, ht12, p913_1, u2elo4]
              · have p913_0 := h913c.1
                have p913_1 := h913c.2.1
                have p913_2 := h913c.2.2.1
                have p913_3 := h913c.2.2.2
                linarith only [h911, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p913_1, u2elo3]
              · have p913_0 := h913c.1
                have p913_1 := h913c.2.1
                have p913_2 := h913c.2.2.1
                have p913_3 := h913c.2.2.2
                linarith only [hlam, p913_0]
              · have p913_0 := h913c.1
                have p913_1 := h913c.2.1
                have p913_2 := h913c.2.2.1
                have p913_3 := h913c.2.2.2
                linarith only [h909, h911, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p913_1, u2elo3]
              · have p913_0 := h913c.1
                have p913_1 := h913c.2.1
                have p913_2 := h913c.2.2.1
                have p913_3 := h913c.2.2.2
                linarith only [h876, h911, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p913_1, u2elo3]
              · have p913_0 := h913c.1
                have p913_1 := h913c.2.1
                have p913_2 := h913c.2.2.1
                have p913_3 := h913c.2.2.2
                linarith only [h0, hc01, hlam, hphi, ht12, ht23, p913_1, u3elo4]
              · have p913_0 := h913c.1
                have p913_1 := h913c.2.1
                have p913_2 := h913c.2.2.1
                have p913_3 := h913c.2.2.2
                linarith only [h0, hc01, hlam, hphi, ht12, ht23, p913_1, u3elo4]
              · have p913_0 := h913c.1
                have p913_1 := h913c.2.1
                have p913_2 := h913c.2.2.1
                have p913_3 := h913c.2.2.2
                linarith only [h912, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p913_1, u3elo3]
              · have p913_0 := h913c.1
                have p913_1 := h913c.2.1
                have p913_2 := h913c.2.2.1
                have p913_3 := h913c.2.2.2
                linarith only [hlam, p913_0]
              · have p913_0 := h913c.1
                have p913_1 := h913c.2.1
                have p913_2 := h913c.2.2.1
                have p913_3 := h913c.2.2.2
                linarith only [h876, h912, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p913_1, u3elo3]
              · have p913_0 := h913c.1
                have p913_1 := h913c.2.1
                have p913_2 := h913c.2.2.1
                have p913_3 := h913c.2.2.2
                linarith only [h0, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p913_1]
              · have p913_0 := h913c.1
                have p913_1 := h913c.2.1
                have p913_2 := h913c.2.2.1
                have p913_3 := h913c.2.2.2
                linarith only [h0, h912, hc01, hlam, hphi, ht12, ht23, p913_1, u3elo3]
              · have p913_0 := h913c.1
                have p913_1 := h913c.2.1
                have p913_2 := h913c.2.2.1
                have p913_3 := h913c.2.2.2
                linarith only [h911, hlam, p913_0]
              · have p913_0 := h913c.1
                have p913_1 := h913c.2.1
                have p913_2 := h913c.2.2.1
                have p913_3 := h913c.2.2.2
                linarith only [h912, hlam, p913_0]
              · have p913_0 := h913c.1
                have p913_1 := h913c.2.1
                have p913_2 := h913c.2.2.1
                have p913_3 := h913c.2.2.2
                linarith only [hlam, p913_0]
            · linarith only [h0, h909, h911, h912, hc01, hlam, hphi, ht12, u2elo3]
          · rcases m.htr 3 4 5 (by decide) (by decide) with h940 | h940
            · linarith only [h497, h911, h940, hc02, hlam, hphi, ht23, u3elo3]
            · rcases h5bigk with h942c | h942c | h942c | h942c | h942c | h942c | h942c | h942c | h942c | h942c | h942c | h942c | h942c | h942c | h942c | h942c | h942c | h942c | h942c | h942c | h942c | h942c | h942c | h942c | h942c
              · have p942_0 := h942c.1
                have p942_1 := h942c.2.1
                have p942_2 := h942c.2.2.1
                have p942_3 := h942c.2.2.2
                linarith only [hlam, p942_0]
              · have p942_0 := h942c.1
                have p942_1 := h942c.2.1
                have p942_2 := h942c.2.2.1
                have p942_3 := h942c.2.2.2
                linarith only [h0, hlam, p942_1]
              · have p942_0 := h942c.1
                have p942_1 := h942c.2.1
                have p942_2 := h942c.2.2.1
                have p942_3 := h942c.2.2.2
                linarith only [h497, hlam, p942_0]
              · have p942_0 := h942c.1
                have p942_1 := h942c.2.1
                have p942_2 := h942c.2.2.1
                have p942_3 := h942c.2.2.2
                linarith only [h758, hlam, p942_1]
              · have p942_0 := h942c.1
                have p942_1 := h942c.2.1
                have p942_2 := h942c.2.2.1
                have p942_3 := h942c.2.2.2
                linarith only [h876, hlam, p942_1]
              · have p942_0 := h942c.1
                have p942_1 := h942c.2.1
                have p942_2 := h942c.2.2.1
                have p942_3 := h942c.2.2.2
                linarith only [h0, hc01, hc15, hlam, hphi, p942_1]
              · have p942_0 := h942c.1
                have p942_1 := h942c.2.1
                have p942_2 := h942c.2.2.1
                have p942_3 := h942c.2.2.2
                linarith only [hlam, p942_0]
              · have p942_0 := h942c.1
                have p942_1 := h942c.2.1
                have p942_2 := h942c.2.2.1
                have p942_3 := h942c.2.2.2
                linarith only [h497, h909, hc02, hlam, hphi, ht23, p942_1, u3elo4]
              · have p942_0 := h942c.1
                have p942_1 := h942c.2.1
                have p942_2 := h942c.2.2.1
                have p942_3 := h942c.2.2.2
                linarith only [h909, hlam, p942_1]
              · have p942_0 := h942c.1
                have p942_1 := h942c.2.1
                have p942_2 := h942c.2.2.1
                have p942_3 := h942c.2.2.2
                linarith only [h909, h940, hlam, p942_1]
              · have p942_0 := h942c.1
                have p942_1 := h942c.2.1
                have p942_2 := h942c.2.2.1
                have p942_3 := h942c.2.2.2
                linarith only [h0, hc01, hlam, hphi, ht12, p942_1, u2elo4]
              · have p942_0 := h942c.1
                have p942_1 := h942c.2.1
                have p942_2 := h942c.2.2.1
                have p942_3 := h942c.2.2.2
                linarith only [hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p942_1, u2elo4]
              · have p942_0 := h942c.1
                have p942_1 := h942c.2.1
                have p942_2 := h942c.2.2.1
                have p942_3 := h942c.2.2.2
                linarith only [hlam, p942_0]
              · have p942_0 := h942c.1
                have p942_1 := h942c.2.1
                have p942_2 := h942c.2.2.1
                have p942_3 := h942c.2.2.2
                linarith only [hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p942_1, u2elo4]
              · have p942_0 := h942c.1
                have p942_1 := h942c.2.1
                have p942_2 := h942c.2.2.1
                have p942_3 := h942c.2.2.2
                linarith only [h911, hlam, p942_1]
              · have p942_0 := h942c.1
                have p942_1 := h942c.2.1
                have p942_2 := h942c.2.2.1
                have p942_3 := h942c.2.2.2
                linarith only [h0, hc01, hlam, hphi, ht12, ht23, p942_1, u3elo4]
              · have p942_0 := h942c.1
                have p942_1 := h942c.2.1
                have p942_2 := h942c.2.2.1
                have p942_3 := h942c.2.2.2
                linarith only [h0, hc01, hlam, hphi, ht12, ht23, p942_1, u3elo4]
              · have p942_0 := h942c.1
                have p942_1 := h942c.2.1
                have p942_2 := h942c.2.2.1
                have p942_3 := h942c.2.2.2
                linarith only [h497, hc02, hlam, hphi, ht23, p942_1, u3elo4]
              · have p942_0 := h942c.1
                have p942_1 := h942c.2.1
                have p942_2 := h942c.2.2.1
                have p942_3 := h942c.2.2.2
                linarith only [hlam, p942_0]
              · have p942_0 := h942c.1
                have p942_1 := h942c.2.1
                have p942_2 := h942c.2.2.1
                have p942_3 := h942c.2.2.2
                linarith only [h940, hlam, p942_1]
              · have p942_0 := h942c.1
                have p942_1 := h942c.2.1
                have p942_2 := h942c.2.2.1
                have p942_3 := h942c.2.2.2
                linarith only [h0, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p942_1]
              · have p942_0 := h942c.1
                have p942_1 := h942c.2.1
                have p942_2 := h942c.2.2.1
                have p942_3 := h942c.2.2.2
                linarith only [h0, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p942_1]
              · have p942_0 := h942c.1
                have p942_1 := h942c.2.1
                have p942_2 := h942c.2.2.1
                have p942_3 := h942c.2.2.2
                linarith only [h497, hc02, hc45, hlam, hphi, ht23, ht34, p942_1]
              · have p942_0 := h942c.1
                have p942_1 := h942c.2.1
                have p942_2 := h942c.2.2.1
                have p942_3 := h942c.2.2.2
                linarith only [h758, hc03, hc45, hlam, hphi, ht34, p942_1]
              · have p942_0 := h942c.1
                have p942_1 := h942c.2.1
                have p942_2 := h942c.2.2.1
                have p942_3 := h942c.2.2.2
                linarith only [hlam, p942_0]

theorem r1l7_10_12_13_25_L_0_L_0_L_0_H_I (m : N7Model)
    (hb0 : CMSig1_7_L_0 m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have hc13 := m.hcor 1 3 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
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
  have h0elo := hb0.1
  have h2elo := hb2.1
  have h3elo := hb3.1
  have h5bigk := hb5.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h0 | h0
  · exact r1l7_10_12_13_25_L_0_L_0_L_0_H_I_x0 m hb0 hb2 hb3 hb5 h0
  · exact r1l7_10_12_13_25_L_0_L_0_L_0_H_I_x1 m hb0 hb2 hb3 hb5 h0

end R2N4
