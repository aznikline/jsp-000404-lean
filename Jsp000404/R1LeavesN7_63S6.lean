import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_63S4
import Jsp000404.R1LeavesN7_63S5

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 3012000 in
set_option maxHeartbeats 3012000 in
theorem r1l7_11_25_L_0_M_LI (m : N7Model)
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
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
  have h5elo := hb5.1
  have h5bigk := hb5.2.2.2
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · exact r1l7_11_25_L_0_M_LI_x0 m hb1 hb5 h0
  · exact r1l7_11_25_L_0_M_LI_x1 m hb1 hb5 h0

theorem r1l7_12_24_L_0_H_I_x0_x0 (m : N7Model)
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h1 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
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
  have h2elo := hb2.1
  have h4bigk := hb4.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  rcases m.htr 0 2 4 (by decide) (by decide) with h2 | h2
  · rcases m.htr 0 2 5 (by decide) (by decide) with h3 | h3
    · rcases m.htr 0 3 4 (by decide) (by decide) with h4 | h4
      · rcases m.htr 0 4 5 (by decide) (by decide) with h5 | h5
        · rcases m.htr 1 2 4 (by decide) (by decide) with h6 | h6
          · rcases m.htr 1 2 5 (by decide) (by decide) with h7 | h7
            · rcases m.htr 1 4 5 (by decide) (by decide) with h8 | h8
              · rcases m.htr 2 3 4 (by decide) (by decide) with h9 | h9
                · rcases m.htr 2 4 5 (by decide) (by decide) with h10 | h10
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h11 | h11
                    · linarith only [h1, h11, h9, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0]
                    · linarith only [h1, h10, h11, h9, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h14 | h14
                    · linarith only [h1, h10, h14, h4, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                    · rcases h4bigk with h16c | h16c | h16c | h16c | h16c | h16c | h16c | h16c | h16c | h16c | h16c | h16c | h16c | h16c | h16c | h16c | h16c | h16c | h16c | h16c | h16c | h16c | h16c | h16c | h16c
                      · have p16_0 := h16c.1
                        have p16_1 := h16c.2.1
                        have p16_2 := h16c.2.2.1
                        have p16_3 := h16c.2.2.2
                        linarith only [hlam, p16_0]
                      · have p16_0 := h16c.1
                        have p16_1 := h16c.2.1
                        have p16_2 := h16c.2.2.1
                        have p16_3 := h16c.2.2.2
                        linarith only [h1, h4, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p16_1, u2elo0]
                      · have p16_0 := h16c.1
                        have p16_1 := h16c.2.1
                        have p16_2 := h16c.2.2.1
                        have p16_3 := h16c.2.2.2
                        linarith only [h1, h4, h9, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p16_1, u2elo0]
                      · have p16_0 := h16c.1
                        have p16_1 := h16c.2.1
                        have p16_2 := h16c.2.2.1
                        have p16_3 := h16c.2.2.2
                        linarith only [h1, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p16_1, u2elo0]
                      · have p16_0 := h16c.1
                        have p16_1 := h16c.2.1
                        have p16_2 := h16c.2.2.1
                        have p16_3 := h16c.2.2.2
                        linarith only [h1, h10, h4, h9, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p16_1, u2elo0]
                      · have p16_0 := h16c.1
                        have p16_1 := h16c.2.1
                        have p16_2 := h16c.2.2.1
                        have p16_3 := h16c.2.2.2
                        linarith only [h0, hlam, p16_0]
                      · have p16_0 := h16c.1
                        have p16_1 := h16c.2.1
                        have p16_2 := h16c.2.2.1
                        have p16_3 := h16c.2.2.2
                        linarith only [hlam, p16_0]
                      · have p16_0 := h16c.1
                        have p16_1 := h16c.2.1
                        have p16_2 := h16c.2.2.1
                        have p16_3 := h16c.2.2.2
                        linarith only [h0, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p16_1]
                      · have p16_0 := h16c.1
                        have p16_1 := h16c.2.1
                        have p16_2 := h16c.2.2.1
                        have p16_3 := h16c.2.2.2
                        linarith only [h0, h1, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p16_1, u2elo0]
                      · have p16_0 := h16c.1
                        have p16_1 := h16c.2.1
                        have p16_2 := h16c.2.2.1
                        have p16_3 := h16c.2.2.2
                        linarith only [h0, h1, h10, h4, h9, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p16_1, u2elo0]
                      · have p16_0 := h16c.1
                        have p16_1 := h16c.2.1
                        have p16_2 := h16c.2.2.1
                        have p16_3 := h16c.2.2.2
                        linarith only [h2, hlam, p16_0]
                      · have p16_0 := h16c.1
                        have p16_1 := h16c.2.1
                        have p16_2 := h16c.2.2.1
                        have p16_3 := h16c.2.2.2
                        linarith only [h6, hlam, p16_0]
                      · have p16_0 := h16c.1
                        have p16_1 := h16c.2.1
                        have p16_2 := h16c.2.2.1
                        have p16_3 := h16c.2.2.2
                        linarith only [hlam, p16_0]
                      · have p16_0 := h16c.1
                        have p16_1 := h16c.2.1
                        have p16_2 := h16c.2.2.1
                        have p16_3 := h16c.2.2.2
                        linarith only [hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p16_1, u2elo3]
                      · have p16_0 := h16c.1
                        have p16_1 := h16c.2.1
                        have p16_2 := h16c.2.2.1
                        have p16_3 := h16c.2.2.2
                        linarith only [h10, hlam, p16_0]
                      · have p16_0 := h16c.1
                        have p16_1 := h16c.2.1
                        have p16_2 := h16c.2.2.1
                        have p16_3 := h16c.2.2.2
                        linarith only [h4, hlam, p16_0]
                      · have p16_0 := h16c.1
                        have p16_1 := h16c.2.1
                        have p16_2 := h16c.2.2.1
                        have p16_3 := h16c.2.2.2
                        linarith only [h10, h8, h9, hlam, p16_1]
                      · have p16_0 := h16c.1
                        have p16_1 := h16c.2.1
                        have p16_2 := h16c.2.2.1
                        have p16_3 := h16c.2.2.2
                        linarith only [h9, hlam, p16_0]
                      · have p16_0 := h16c.1
                        have p16_1 := h16c.2.1
                        have p16_2 := h16c.2.2.1
                        have p16_3 := h16c.2.2.2
                        linarith only [hlam, p16_0]
                      · have p16_0 := h16c.1
                        have p16_1 := h16c.2.1
                        have p16_2 := h16c.2.2.1
                        have p16_3 := h16c.2.2.2
                        linarith only [h14, hlam, p16_0]
                      · have p16_0 := h16c.1
                        have p16_1 := h16c.2.1
                        have p16_2 := h16c.2.2.1
                        have p16_3 := h16c.2.2.2
                        linarith only [h5, hlam, p16_0]
                      · have p16_0 := h16c.1
                        have p16_1 := h16c.2.1
                        have p16_2 := h16c.2.2.1
                        have p16_3 := h16c.2.2.2
                        linarith only [h8, hlam, p16_0]
                      · have p16_0 := h16c.1
                        have p16_1 := h16c.2.1
                        have p16_2 := h16c.2.2.1
                        have p16_3 := h16c.2.2.2
                        linarith only [h0, h1, h4, h8, h9, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p16_1, u2elo0]
                      · have p16_0 := h16c.1
                        have p16_1 := h16c.2.1
                        have p16_2 := h16c.2.2.1
                        have p16_3 := h16c.2.2.2
                        linarith only [h0, h1, h4, h8, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p16_1, u2elo0]
                      · have p16_0 := h16c.1
                        have p16_1 := h16c.2.1
                        have p16_2 := h16c.2.2.1
                        have p16_3 := h16c.2.2.2
                        linarith only [hlam, p16_0]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h42 | h42
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h43 | h43
                    · rcases h4bigk with h44c | h44c | h44c | h44c | h44c | h44c | h44c | h44c | h44c | h44c | h44c | h44c | h44c | h44c | h44c | h44c | h44c | h44c | h44c | h44c | h44c | h44c | h44c | h44c | h44c
                      · have p44_0 := h44c.1
                        have p44_1 := h44c.2.1
                        have p44_2 := h44c.2.2.1
                        have p44_3 := h44c.2.2.2
                        linarith only [hlam, p44_0]
                      · have p44_0 := h44c.1
                        have p44_1 := h44c.2.1
                        have p44_2 := h44c.2.2.1
                        have p44_3 := h44c.2.2.2
                        linarith only [h1, h4, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p44_1, u2elo0]
                      · have p44_0 := h44c.1
                        have p44_1 := h44c.2.1
                        have p44_2 := h44c.2.2.1
                        have p44_3 := h44c.2.2.2
                        linarith only [h1, h4, h42, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p44_1, u2elo0]
                      · have p44_0 := h44c.1
                        have p44_1 := h44c.2.1
                        have p44_2 := h44c.2.2.1
                        have p44_3 := h44c.2.2.2
                        linarith only [h1, h4, h9, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p44_1, u2elo0]
                      · have p44_0 := h44c.1
                        have p44_1 := h44c.2.1
                        have p44_2 := h44c.2.2.1
                        have p44_3 := h44c.2.2.2
                        linarith only [h1, h4, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p44_1, u2elo0]
                      · have p44_0 := h44c.1
                        have p44_1 := h44c.2.1
                        have p44_2 := h44c.2.2.1
                        have p44_3 := h44c.2.2.2
                        linarith only [h0, hlam, p44_0]
                      · have p44_0 := h44c.1
                        have p44_1 := h44c.2.1
                        have p44_2 := h44c.2.2.1
                        have p44_3 := h44c.2.2.2
                        linarith only [hlam, p44_0]
                      · have p44_0 := h44c.1
                        have p44_1 := h44c.2.1
                        have p44_2 := h44c.2.2.1
                        have p44_3 := h44c.2.2.2
                        linarith only [h42, hc14, hc45, hlam, hphi, ht01, ht0b, ht5b, p44_1]
                      · have p44_0 := h44c.1
                        have p44_1 := h44c.2.1
                        have p44_2 := h44c.2.2.1
                        have p44_3 := h44c.2.2.2
                        linarith only [h0, h1, h4, h9, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p44_1, u2elo0]
                      · have p44_0 := h44c.1
                        have p44_1 := h44c.2.1
                        have p44_2 := h44c.2.2.1
                        have p44_3 := h44c.2.2.2
                        linarith only [h0, h1, h4, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p44_1, u2elo0]
                      · have p44_0 := h44c.1
                        have p44_1 := h44c.2.1
                        have p44_2 := h44c.2.2.1
                        have p44_3 := h44c.2.2.2
                        linarith only [h2, hlam, p44_0]
                      · have p44_0 := h44c.1
                        have p44_1 := h44c.2.1
                        have p44_2 := h44c.2.2.1
                        have p44_3 := h44c.2.2.2
                        linarith only [h6, hlam, p44_0]
                      · have p44_0 := h44c.1
                        have p44_1 := h44c.2.1
                        have p44_2 := h44c.2.2.1
                        have p44_3 := h44c.2.2.2
                        linarith only [hlam, p44_0]
                      · have p44_0 := h44c.1
                        have p44_1 := h44c.2.1
                        have p44_2 := h44c.2.2.1
                        have p44_3 := h44c.2.2.2
                        linarith only [h9, hlam, p44_1]
                      · have p44_0 := h44c.1
                        have p44_1 := h44c.2.1
                        have p44_2 := h44c.2.2.1
                        have p44_3 := h44c.2.2.2
                        linarith only [hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p44_1, u2elo3]
                      · have p44_0 := h44c.1
                        have p44_1 := h44c.2.1
                        have p44_2 := h44c.2.2.1
                        have p44_3 := h44c.2.2.2
                        linarith only [h4, hlam, p44_0]
                      · have p44_0 := h44c.1
                        have p44_1 := h44c.2.1
                        have p44_2 := h44c.2.2.1
                        have p44_3 := h44c.2.2.2
                        linarith only [h1, h4, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p44_1, u2elo0]
                      · have p44_0 := h44c.1
                        have p44_1 := h44c.2.1
                        have p44_2 := h44c.2.2.1
                        have p44_3 := h44c.2.2.2
                        linarith only [h1, h4, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p44_1, u2elo0]
                      · have p44_0 := h44c.1
                        have p44_1 := h44c.2.1
                        have p44_2 := h44c.2.2.1
                        have p44_3 := h44c.2.2.2
                        linarith only [hlam, p44_0]
                      · have p44_0 := h44c.1
                        have p44_1 := h44c.2.1
                        have p44_2 := h44c.2.2.1
                        have p44_3 := h44c.2.2.2
                        linarith only [h1, h4, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p44_1, u2elo0]
                      · have p44_0 := h44c.1
                        have p44_1 := h44c.2.1
                        have p44_2 := h44c.2.2.1
                        have p44_3 := h44c.2.2.2
                        linarith only [h5, hlam, p44_0]
                      · have p44_0 := h44c.1
                        have p44_1 := h44c.2.1
                        have p44_2 := h44c.2.2.1
                        have p44_3 := h44c.2.2.2
                        linarith only [h8, hlam, p44_0]
                      · have p44_0 := h44c.1
                        have p44_1 := h44c.2.1
                        have p44_2 := h44c.2.2.1
                        have p44_3 := h44c.2.2.2
                        linarith only [h42, hlam, p44_0]
                      · have p44_0 := h44c.1
                        have p44_1 := h44c.2.1
                        have p44_2 := h44c.2.2.1
                        have p44_3 := h44c.2.2.2
                        linarith only [h43, hlam, p44_0]
                      · have p44_0 := h44c.1
                        have p44_1 := h44c.2.1
                        have p44_2 := h44c.2.2.1
                        have p44_3 := h44c.2.2.2
                        linarith only [hlam, p44_0]
                    · linarith only [h2, h42, h43, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h71 | h71
                    · linarith only [h1, h4, h42, h71, h9, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                    · linarith only [h1, h4, h5, h71, h9, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h74 | h74
                · rcases m.htr 2 4 5 (by decide) (by decide) with h75 | h75
                  · linarith only [h2, h75, h8, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h77 | h77
                    · linarith only [h6, h74, h77, h8, hlam]
                    · rcases h4bigk with h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c
                      · have p79_0 := h79c.1
                        have p79_1 := h79c.2.1
                        have p79_2 := h79c.2.2.1
                        have p79_3 := h79c.2.2.2
                        linarith only [hlam, p79_0]
                      · have p79_0 := h79c.1
                        have p79_1 := h79c.2.1
                        have p79_2 := h79c.2.2.1
                        have p79_3 := h79c.2.2.2
                        linarith only [h1, h4, h6, h74, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p79_1, u2elo0]
                      · have p79_0 := h79c.1
                        have p79_1 := h79c.2.1
                        have p79_2 := h79c.2.2.1
                        have p79_3 := h79c.2.2.2
                        linarith only [h1, h4, h74, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p79_1, u2elo0]
                      · have p79_0 := h79c.1
                        have p79_1 := h79c.2.1
                        have p79_2 := h79c.2.2.1
                        have p79_3 := h79c.2.2.2
                        linarith only [h1, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p79_1, u2elo0]
                      · have p79_0 := h79c.1
                        have p79_1 := h79c.2.1
                        have p79_2 := h79c.2.2.1
                        have p79_3 := h79c.2.2.2
                        linarith only [h1, h4, h6, h74, h8, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p79_1, u2elo0]
                      · have p79_0 := h79c.1
                        have p79_1 := h79c.2.1
                        have p79_2 := h79c.2.2.1
                        have p79_3 := h79c.2.2.2
                        linarith only [h0, hlam, p79_0]
                      · have p79_0 := h79c.1
                        have p79_1 := h79c.2.1
                        have p79_2 := h79c.2.2.1
                        have p79_3 := h79c.2.2.2
                        linarith only [hlam, p79_0]
                      · have p79_0 := h79c.1
                        have p79_1 := h79c.2.1
                        have p79_2 := h79c.2.2.1
                        have p79_3 := h79c.2.2.2
                        linarith only [h74, h8, hc34, hc45, hlam, hphi, p79_1]
                      · have p79_0 := h79c.1
                        have p79_1 := h79c.2.1
                        have p79_2 := h79c.2.2.1
                        have p79_3 := h79c.2.2.2
                        linarith only [h1, h4, h5, h8, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p79_1, u2elo0]
                      · have p79_0 := h79c.1
                        have p79_1 := h79c.2.1
                        have p79_2 := h79c.2.2.1
                        have p79_3 := h79c.2.2.2
                        linarith only [h8, hlam, p79_0]
                      · have p79_0 := h79c.1
                        have p79_1 := h79c.2.1
                        have p79_2 := h79c.2.2.1
                        have p79_3 := h79c.2.2.2
                        linarith only [h2, hlam, p79_0]
                      · have p79_0 := h79c.1
                        have p79_1 := h79c.2.1
                        have p79_2 := h79c.2.2.1
                        have p79_3 := h79c.2.2.2
                        linarith only [h6, hlam, p79_0]
                      · have p79_0 := h79c.1
                        have p79_1 := h79c.2.1
                        have p79_2 := h79c.2.2.1
                        have p79_3 := h79c.2.2.2
                        linarith only [hlam, p79_0]
                      · have p79_0 := h79c.1
                        have p79_1 := h79c.2.1
                        have p79_2 := h79c.2.2.1
                        have p79_3 := h79c.2.2.2
                        linarith only [hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p79_1, u2elo3]
                      · have p79_0 := h79c.1
                        have p79_1 := h79c.2.1
                        have p79_2 := h79c.2.2.1
                        have p79_3 := h79c.2.2.2
                        linarith only [h75, hlam, p79_0]
                      · have p79_0 := h79c.1
                        have p79_1 := h79c.2.1
                        have p79_2 := h79c.2.2.1
                        have p79_3 := h79c.2.2.2
                        linarith only [h4, hlam, p79_0]
                      · have p79_0 := h79c.1
                        have p79_1 := h79c.2.1
                        have p79_2 := h79c.2.2.1
                        have p79_3 := h79c.2.2.2
                        linarith only [h74, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p79_1, u2elo2]
                      · have p79_0 := h79c.1
                        have p79_1 := h79c.2.1
                        have p79_2 := h79c.2.2.1
                        have p79_3 := h79c.2.2.2
                        linarith only [h74, hlam, p79_0]
                      · have p79_0 := h79c.1
                        have p79_1 := h79c.2.1
                        have p79_2 := h79c.2.2.1
                        have p79_3 := h79c.2.2.2
                        linarith only [hlam, p79_0]
                      · have p79_0 := h79c.1
                        have p79_1 := h79c.2.1
                        have p79_2 := h79c.2.2.1
                        have p79_3 := h79c.2.2.2
                        linarith only [h77, hlam, p79_0]
                      · have p79_0 := h79c.1
                        have p79_1 := h79c.2.1
                        have p79_2 := h79c.2.2.1
                        have p79_3 := h79c.2.2.2
                        linarith only [h5, hlam, p79_0]
                      · have p79_0 := h79c.1
                        have p79_1 := h79c.2.1
                        have p79_2 := h79c.2.2.1
                        have p79_3 := h79c.2.2.2
                        linarith only [h1, h4, h5, h6, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p79_1, u2elo0]
                      · have p79_0 := h79c.1
                        have p79_1 := h79c.2.1
                        have p79_2 := h79c.2.2.1
                        have p79_3 := h79c.2.2.2
                        linarith only [h1, h4, h5, h74, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p79_1, u2elo0]
                      · have p79_0 := h79c.1
                        have p79_1 := h79c.2.1
                        have p79_2 := h79c.2.2.1
                        have p79_3 := h79c.2.2.2
                        linarith only [h1, h4, h5, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p79_1, u2elo0]
                      · have p79_0 := h79c.1
                        have p79_1 := h79c.2.1
                        have p79_2 := h79c.2.2.1
                        have p79_3 := h79c.2.2.2
                        linarith only [hlam, p79_0]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h105 | h105
                  · linarith only [h105, h2, h8, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h107 | h107
                    · linarith only [h1, h107, h4, h6, h74, h8, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                    · linarith only [h1, h107, h4, h5, h74, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
            · linarith only [h3, h7, hc12, hlam, hphi, u2elo0]
          · linarith only [h2, h6, hc12, hlam, hphi, u2elo0]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h112 | h112
          · rcases m.htr 1 2 5 (by decide) (by decide) with h113 | h113
            · rcases m.htr 1 4 5 (by decide) (by decide) with h114 | h114
              · linarith only [h0, h114, h5, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h116 | h116
                · rcases m.htr 2 4 5 (by decide) (by decide) with h117 | h117
                  · linarith only [h0, h112, h117, h5, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h119 | h119
                    · linarith only [h116, h119, h5, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                    · rcases h4bigk with h121c | h121c | h121c | h121c | h121c | h121c | h121c | h121c | h121c | h121c | h121c | h121c | h121c | h121c | h121c | h121c | h121c | h121c | h121c | h121c | h121c | h121c | h121c | h121c | h121c
                      · have p121_0 := h121c.1
                        have p121_1 := h121c.2.1
                        have p121_2 := h121c.2.2.1
                        have p121_3 := h121c.2.2.2
                        linarith only [hlam, p121_0]
                      · have p121_0 := h121c.1
                        have p121_1 := h121c.2.1
                        have p121_2 := h121c.2.2.1
                        have p121_3 := h121c.2.2.2
                        linarith only [h112, h116, h5, hc34, hc45, hlam, hphi, p121_1]
                      · have p121_0 := h121c.1
                        have p121_1 := h121c.2.1
                        have p121_2 := h121c.2.2.1
                        have p121_3 := h121c.2.2.2
                        linarith only [h116, h5, hc34, hc45, hlam, hphi, p121_1]
                      · have p121_0 := h121c.1
                        have p121_1 := h121c.2.1
                        have p121_2 := h121c.2.2.1
                        have p121_3 := h121c.2.2.2
                        linarith only [h1, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p121_1, u2elo0]
                      · have p121_0 := h121c.1
                        have p121_1 := h121c.2.1
                        have p121_2 := h121c.2.2.1
                        have p121_3 := h121c.2.2.2
                        linarith only [h5, hlam, p121_0]
                      · have p121_0 := h121c.1
                        have p121_1 := h121c.2.1
                        have p121_2 := h121c.2.2.1
                        have p121_3 := h121c.2.2.2
                        linarith only [h0, hlam, p121_0]
                      · have p121_0 := h121c.1
                        have p121_1 := h121c.2.1
                        have p121_2 := h121c.2.2.1
                        have p121_3 := h121c.2.2.2
                        linarith only [hlam, p121_0]
                      · have p121_0 := h121c.1
                        have p121_1 := h121c.2.1
                        have p121_2 := h121c.2.2.1
                        have p121_3 := h121c.2.2.2
                        linarith only [h0, h116, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p121_1]
                      · have p121_0 := h121c.1
                        have p121_1 := h121c.2.1
                        have p121_2 := h121c.2.2.1
                        have p121_3 := h121c.2.2.2
                        linarith only [h113, h114, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p121_1, u2elo1]
                      · have p121_0 := h121c.1
                        have p121_1 := h121c.2.1
                        have p121_2 := h121c.2.2.1
                        have p121_3 := h121c.2.2.2
                        linarith only [h114, hlam, p121_0]
                      · have p121_0 := h121c.1
                        have p121_1 := h121c.2.1
                        have p121_2 := h121c.2.2.1
                        have p121_3 := h121c.2.2.2
                        linarith only [h2, hlam, p121_0]
                      · have p121_0 := h121c.1
                        have p121_1 := h121c.2.1
                        have p121_2 := h121c.2.2.1
                        have p121_3 := h121c.2.2.2
                        linarith only [h112, hlam, p121_0]
                      · have p121_0 := h121c.1
                        have p121_1 := h121c.2.1
                        have p121_2 := h121c.2.2.1
                        have p121_3 := h121c.2.2.2
                        linarith only [hlam, p121_0]
                      · have p121_0 := h121c.1
                        have p121_1 := h121c.2.1
                        have p121_2 := h121c.2.2.1
                        have p121_3 := h121c.2.2.2
                        linarith only [hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p121_1, u2elo3]
                      · have p121_0 := h121c.1
                        have p121_1 := h121c.2.1
                        have p121_2 := h121c.2.2.1
                        have p121_3 := h121c.2.2.2
                        linarith only [h117, hlam, p121_0]
                      · have p121_0 := h121c.1
                        have p121_1 := h121c.2.1
                        have p121_2 := h121c.2.2.1
                        have p121_3 := h121c.2.2.2
                        linarith only [h4, hlam, p121_0]
                      · have p121_0 := h121c.1
                        have p121_1 := h121c.2.1
                        have p121_2 := h121c.2.2.1
                        have p121_3 := h121c.2.2.2
                        linarith only [h1, h4, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p121_1, u2elo0]
                      · have p121_0 := h121c.1
                        have p121_1 := h121c.2.1
                        have p121_2 := h121c.2.2.1
                        have p121_3 := h121c.2.2.2
                        linarith only [h116, hlam, p121_0]
                      · have p121_0 := h121c.1
                        have p121_1 := h121c.2.1
                        have p121_2 := h121c.2.2.1
                        have p121_3 := h121c.2.2.2
                        linarith only [hlam, p121_0]
                      · have p121_0 := h121c.1
                        have p121_1 := h121c.2.1
                        have p121_2 := h121c.2.2.1
                        have p121_3 := h121c.2.2.2
                        linarith only [h119, hlam, p121_0]
                      · have p121_0 := h121c.1
                        have p121_1 := h121c.2.1
                        have p121_2 := h121c.2.2.1
                        have p121_3 := h121c.2.2.2
                        linarith only [hc04, hc45, hlam, hphi, p121_1]
                      · have p121_0 := h121c.1
                        have p121_1 := h121c.2.1
                        have p121_2 := h121c.2.2.1
                        have p121_3 := h121c.2.2.2
                        linarith only [hc14, hc45, hlam, hphi, p121_1]
                      · have p121_0 := h121c.1
                        have p121_1 := h121c.2.1
                        have p121_2 := h121c.2.2.1
                        have p121_3 := h121c.2.2.2
                        linarith only [h116, hc34, hc45, hlam, hphi, p121_1]
                      · have p121_0 := h121c.1
                        have p121_1 := h121c.2.1
                        have p121_2 := h121c.2.2.1
                        have p121_3 := h121c.2.2.2
                        linarith only [hc34, hc45, hlam, hphi, p121_1]
                      · have p121_0 := h121c.1
                        have p121_1 := h121c.2.1
                        have p121_2 := h121c.2.2.1
                        have p121_3 := h121c.2.2.2
                        linarith only [hlam, p121_0]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h147 | h147
                  · linarith only [h116, h147, h4, h5, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h149 | h149
                    · linarith only [h1, h149, h4, h5, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                    · rcases h4bigk with h151c | h151c | h151c | h151c | h151c | h151c | h151c | h151c | h151c | h151c | h151c | h151c | h151c | h151c | h151c | h151c | h151c | h151c | h151c | h151c | h151c | h151c | h151c | h151c | h151c
                      · have p151_0 := h151c.1
                        have p151_1 := h151c.2.1
                        have p151_2 := h151c.2.2.1
                        have p151_3 := h151c.2.2.2
                        linarith only [hlam, p151_0]
                      · have p151_0 := h151c.1
                        have p151_1 := h151c.2.1
                        have p151_2 := h151c.2.2.1
                        have p151_3 := h151c.2.2.2
                        linarith only [h112, h5, hc24, hc45, hlam, hphi, p151_1]
                      · have p151_0 := h151c.1
                        have p151_1 := h151c.2.1
                        have p151_2 := h151c.2.2.1
                        have p151_3 := h151c.2.2.2
                        linarith only [h5, hc24, hc45, hlam, hphi, p151_1]
                      · have p151_0 := h151c.1
                        have p151_1 := h151c.2.1
                        have p151_2 := h151c.2.2.1
                        have p151_3 := h151c.2.2.2
                        linarith only [h116, h5, hc23, hc45, hlam, hphi, ht34, p151_1]
                      · have p151_0 := h151c.1
                        have p151_1 := h151c.2.1
                        have p151_2 := h151c.2.2.1
                        have p151_3 := h151c.2.2.2
                        linarith only [h5, hlam, p151_0]
                      · have p151_0 := h151c.1
                        have p151_1 := h151c.2.1
                        have p151_2 := h151c.2.2.1
                        have p151_3 := h151c.2.2.2
                        linarith only [h0, hlam, p151_0]
                      · have p151_0 := h151c.1
                        have p151_1 := h151c.2.1
                        have p151_2 := h151c.2.2.1
                        have p151_3 := h151c.2.2.2
                        linarith only [hlam, p151_0]
                      · have p151_0 := h151c.1
                        have p151_1 := h151c.2.1
                        have p151_2 := h151c.2.2.1
                        have p151_3 := h151c.2.2.2
                        linarith only [h0, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p151_1]
                      · have p151_0 := h151c.1
                        have p151_1 := h151c.2.1
                        have p151_2 := h151c.2.2.1
                        have p151_3 := h151c.2.2.2
                        linarith only [h0, h116, h5, hc23, hc45, hlam, hphi, ht34, p151_1]
                      · have p151_0 := h151c.1
                        have p151_1 := h151c.2.1
                        have p151_2 := h151c.2.2.1
                        have p151_3 := h151c.2.2.2
                        linarith only [h114, hlam, p151_0]
                      · have p151_0 := h151c.1
                        have p151_1 := h151c.2.1
                        have p151_2 := h151c.2.2.1
                        have p151_3 := h151c.2.2.2
                        linarith only [h2, hlam, p151_0]
                      · have p151_0 := h151c.1
                        have p151_1 := h151c.2.1
                        have p151_2 := h151c.2.2.1
                        have p151_3 := h151c.2.2.2
                        linarith only [h112, hlam, p151_0]
                      · have p151_0 := h151c.1
                        have p151_1 := h151c.2.1
                        have p151_2 := h151c.2.2.1
                        have p151_3 := h151c.2.2.2
                        linarith only [hlam, p151_0]
                      · have p151_0 := h151c.1
                        have p151_1 := h151c.2.1
                        have p151_2 := h151c.2.2.1
                        have p151_3 := h151c.2.2.2
                        linarith only [h116, hlam, p151_1]
                      · have p151_0 := h151c.1
                        have p151_1 := h151c.2.1
                        have p151_2 := h151c.2.2.1
                        have p151_3 := h151c.2.2.2
                        linarith only [h147, hlam, p151_0]
                      · have p151_0 := h151c.1
                        have p151_1 := h151c.2.1
                        have p151_2 := h151c.2.2.1
                        have p151_3 := h151c.2.2.2
                        linarith only [h4, hlam, p151_0]
                      · have p151_0 := h151c.1
                        have p151_1 := h151c.2.1
                        have p151_2 := h151c.2.2.1
                        have p151_3 := h151c.2.2.2
                        linarith only [h1, h4, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p151_1, u2elo0]
                      · have p151_0 := h151c.1
                        have p151_1 := h151c.2.1
                        have p151_2 := h151c.2.2.1
                        have p151_3 := h151c.2.2.2
                        linarith only [h1, h116, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p151_1, u2elo0]
                      · have p151_0 := h151c.1
                        have p151_1 := h151c.2.1
                        have p151_2 := h151c.2.2.1
                        have p151_3 := h151c.2.2.2
                        linarith only [hlam, p151_0]
                      · have p151_0 := h151c.1
                        have p151_1 := h151c.2.1
                        have p151_2 := h151c.2.2.1
                        have p151_3 := h151c.2.2.2
                        linarith only [h149, hlam, p151_0]
                      · have p151_0 := h151c.1
                        have p151_1 := h151c.2.1
                        have p151_2 := h151c.2.2.1
                        have p151_3 := h151c.2.2.2
                        linarith only [hc04, hc45, hlam, hphi, p151_1]
                      · have p151_0 := h151c.1
                        have p151_1 := h151c.2.1
                        have p151_2 := h151c.2.2.1
                        have p151_3 := h151c.2.2.2
                        linarith only [h112, h116, hc23, hc45, hlam, hphi, ht34, p151_1]
                      · have p151_0 := h151c.1
                        have p151_1 := h151c.2.1
                        have p151_2 := h151c.2.2.1
                        have p151_3 := h151c.2.2.2
                        linarith only [h116, hc23, hc45, hlam, hphi, ht34, p151_1]
                      · have p151_0 := h151c.1
                        have p151_1 := h151c.2.1
                        have p151_2 := h151c.2.2.1
                        have p151_3 := h151c.2.2.2
                        linarith only [h116, hc23, hc45, hlam, hphi, ht34, p151_1]
                      · have p151_0 := h151c.1
                        have p151_1 := h151c.2.1
                        have p151_2 := h151c.2.2.1
                        have p151_3 := h151c.2.2.2
                        linarith only [hlam, p151_0]
            · linarith only [h113, h3, hc12, hlam, hphi, u2elo0]
          · linarith only [h112, h2, hc12, hlam, hphi, u2elo0]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h179 | h179
        · rcases m.htr 1 2 4 (by decide) (by decide) with h180 | h180
          · rcases m.htr 1 2 5 (by decide) (by decide) with h181 | h181
            · rcases m.htr 1 4 5 (by decide) (by decide) with h182 | h182
              · rcases m.htr 2 3 4 (by decide) (by decide) with h183 | h183
                · linarith only [h1, h183, h4, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h185 | h185
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h186 | h186
                    · rcases h4bigk with h187c | h187c | h187c | h187c | h187c | h187c | h187c | h187c | h187c | h187c | h187c | h187c | h187c | h187c | h187c | h187c | h187c | h187c | h187c | h187c | h187c | h187c | h187c | h187c | h187c
                      · have p187_0 := h187c.1
                        have p187_1 := h187c.2.1
                        have p187_2 := h187c.2.2.1
                        have p187_3 := h187c.2.2.2
                        linarith only [hlam, p187_0]
                      · have p187_0 := h187c.1
                        have p187_1 := h187c.2.1
                        have p187_2 := h187c.2.2.1
                        have p187_3 := h187c.2.2.2
                        linarith only [h180, h185, hc04, hc45, hlam, hphi, ht0b, ht5b, p187_1]
                      · have p187_0 := h187c.1
                        have p187_1 := h187c.2.1
                        have p187_2 := h187c.2.2.1
                        have p187_3 := h187c.2.2.2
                        linarith only [h185, h2, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p187_1, u2elo0]
                      · have p187_0 := h187c.1
                        have p187_1 := h187c.2.1
                        have p187_2 := h187c.2.2.1
                        have p187_3 := h187c.2.2.2
                        linarith only [h4, hlam, p187_1]
                      · have p187_0 := h187c.1
                        have p187_1 := h187c.2.1
                        have p187_2 := h187c.2.2.1
                        have p187_3 := h187c.2.2.2
                        linarith only [h2, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p187_1, u2elo0]
                      · have p187_0 := h187c.1
                        have p187_1 := h187c.2.1
                        have p187_2 := h187c.2.2.1
                        have p187_3 := h187c.2.2.2
                        linarith only [h0, hlam, p187_0]
                      · have p187_0 := h187c.1
                        have p187_1 := h187c.2.1
                        have p187_2 := h187c.2.2.1
                        have p187_3 := h187c.2.2.2
                        linarith only [hlam, p187_0]
                      · have p187_0 := h187c.1
                        have p187_1 := h187c.2.1
                        have p187_2 := h187c.2.2.1
                        have p187_3 := h187c.2.2.2
                        linarith only [h185, hc14, hc45, hlam, hphi, ht01, ht0b, ht5b, p187_1]
                      · have p187_0 := h187c.1
                        have p187_1 := h187c.2.1
                        have p187_2 := h187c.2.2.1
                        have p187_3 := h187c.2.2.2
                        linarith only [h0, h2, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p187_1, u2elo0]
                      · have p187_0 := h187c.1
                        have p187_1 := h187c.2.1
                        have p187_2 := h187c.2.2.1
                        have p187_3 := h187c.2.2.2
                        linarith only [h0, h2, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p187_1, u2elo0]
                      · have p187_0 := h187c.1
                        have p187_1 := h187c.2.1
                        have p187_2 := h187c.2.2.1
                        have p187_3 := h187c.2.2.2
                        linarith only [h2, hlam, p187_0]
                      · have p187_0 := h187c.1
                        have p187_1 := h187c.2.1
                        have p187_2 := h187c.2.2.1
                        have p187_3 := h187c.2.2.2
                        linarith only [h180, hlam, p187_0]
                      · have p187_0 := h187c.1
                        have p187_1 := h187c.2.1
                        have p187_2 := h187c.2.2.1
                        have p187_3 := h187c.2.2.2
                        linarith only [hlam, p187_0]
                      · have p187_0 := h187c.1
                        have p187_1 := h187c.2.1
                        have p187_2 := h187c.2.2.1
                        have p187_3 := h187c.2.2.2
                        linarith only [h183, hlam, p187_1]
                      · have p187_0 := h187c.1
                        have p187_1 := h187c.2.1
                        have p187_2 := h187c.2.2.1
                        have p187_3 := h187c.2.2.2
                        linarith only [h2, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p187_1, u2elo0]
                      · have p187_0 := h187c.1
                        have p187_1 := h187c.2.1
                        have p187_2 := h187c.2.2.1
                        have p187_3 := h187c.2.2.2
                        linarith only [h1, h4, hc23, hc34, hlam, hphi, p187_1]
                      · have p187_0 := h187c.1
                        have p187_1 := h187c.2.1
                        have p187_2 := h187c.2.2.1
                        have p187_3 := h187c.2.2.2
                        linarith only [h180, h185, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p187_1]
                      · have p187_0 := h187c.1
                        have p187_1 := h187c.2.1
                        have p187_2 := h187c.2.2.1
                        have p187_3 := h187c.2.2.2
                        linarith only [h185, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p187_1]
                      · have p187_0 := h187c.1
                        have p187_1 := h187c.2.1
                        have p187_2 := h187c.2.2.1
                        have p187_3 := h187c.2.2.2
                        linarith only [hlam, p187_0]
                      · have p187_0 := h187c.1
                        have p187_1 := h187c.2.1
                        have p187_2 := h187c.2.2.1
                        have p187_3 := h187c.2.2.2
                        rcases p187_3 (m.d 0 4) (by simp) with h207 | h207
                        · linarith only [h207, h4, hlam]
                        · linarith only [h179, h207, hlam]
                      · have p187_0 := h187c.1
                        have p187_1 := h187c.2.1
                        have p187_2 := h187c.2.2.1
                        have p187_3 := h187c.2.2.2
                        linarith only [h179, hlam, p187_0]
                      · have p187_0 := h187c.1
                        have p187_1 := h187c.2.1
                        have p187_2 := h187c.2.2.1
                        have p187_3 := h187c.2.2.2
                        linarith only [h182, hlam, p187_0]
                      · have p187_0 := h187c.1
                        have p187_1 := h187c.2.1
                        have p187_2 := h187c.2.2.1
                        have p187_3 := h187c.2.2.2
                        linarith only [h185, hlam, p187_0]
                      · have p187_0 := h187c.1
                        have p187_1 := h187c.2.1
                        have p187_2 := h187c.2.2.1
                        have p187_3 := h187c.2.2.2
                        linarith only [h186, hlam, p187_0]
                      · have p187_0 := h187c.1
                        have p187_1 := h187c.2.1
                        have p187_2 := h187c.2.2.1
                        have p187_3 := h187c.2.2.2
                        linarith only [hlam, p187_0]
                    · linarith only [h180, h185, h186, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h216 | h216
                    · rcases h4bigk with h217c | h217c | h217c | h217c | h217c | h217c | h217c | h217c | h217c | h217c | h217c | h217c | h217c | h217c | h217c | h217c | h217c | h217c | h217c | h217c | h217c | h217c | h217c | h217c | h217c
                      · have p217_0 := h217c.1
                        have p217_1 := h217c.2.1
                        have p217_2 := h217c.2.2.1
                        have p217_3 := h217c.2.2.2
                        linarith only [hlam, p217_0]
                      · have p217_0 := h217c.1
                        have p217_1 := h217c.2.1
                        have p217_2 := h217c.2.2.1
                        have p217_3 := h217c.2.2.2
                        linarith only [h182, h183, h185, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p217_1]
                      · have p217_0 := h217c.1
                        have p217_1 := h217c.2.1
                        have p217_2 := h217c.2.2.1
                        have p217_3 := h217c.2.2.2
                        linarith only [h183, h2, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p217_1, u2elo0]
                      · have p217_0 := h217c.1
                        have p217_1 := h217c.2.1
                        have p217_2 := h217c.2.2.1
                        have p217_3 := h217c.2.2.2
                        linarith only [h4, hlam, p217_1]
                      · have p217_0 := h217c.1
                        have p217_1 := h217c.2.1
                        have p217_2 := h217c.2.2.1
                        have p217_3 := h217c.2.2.2
                        linarith only [h183, h185, h2, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p217_1, u2elo0]
                      · have p217_0 := h217c.1
                        have p217_1 := h217c.2.1
                        have p217_2 := h217c.2.2.1
                        have p217_3 := h217c.2.2.2
                        linarith only [h0, hlam, p217_0]
                      · have p217_0 := h217c.1
                        have p217_1 := h217c.2.1
                        have p217_2 := h217c.2.2.1
                        have p217_3 := h217c.2.2.2
                        linarith only [hlam, p217_0]
                      · have p217_0 := h217c.1
                        have p217_1 := h217c.2.1
                        have p217_2 := h217c.2.2.1
                        have p217_3 := h217c.2.2.2
                        linarith only [h0, h183, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p217_1]
                      · have p217_0 := h217c.1
                        have p217_1 := h217c.2.1
                        have p217_2 := h217c.2.2.1
                        have p217_3 := h217c.2.2.2
                        linarith only [h0, h2, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p217_1, u2elo0]
                      · have p217_0 := h217c.1
                        have p217_1 := h217c.2.1
                        have p217_2 := h217c.2.2.1
                        have p217_3 := h217c.2.2.2
                        linarith only [h0, h183, h185, h2, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p217_1, u2elo0]
                      · have p217_0 := h217c.1
                        have p217_1 := h217c.2.1
                        have p217_2 := h217c.2.2.1
                        have p217_3 := h217c.2.2.2
                        linarith only [h2, hlam, p217_0]
                      · have p217_0 := h217c.1
                        have p217_1 := h217c.2.1
                        have p217_2 := h217c.2.2.1
                        have p217_3 := h217c.2.2.2
                        linarith only [h180, hlam, p217_0]
                      · have p217_0 := h217c.1
                        have p217_1 := h217c.2.1
                        have p217_2 := h217c.2.2.1
                        have p217_3 := h217c.2.2.2
                        linarith only [hlam, p217_0]
                      · have p217_0 := h217c.1
                        have p217_1 := h217c.2.1
                        have p217_2 := h217c.2.2.1
                        have p217_3 := h217c.2.2.2
                        linarith only [h183, hlam, p217_1]
                      · have p217_0 := h217c.1
                        have p217_1 := h217c.2.1
                        have p217_2 := h217c.2.2.1
                        have p217_3 := h217c.2.2.2
                        linarith only [h185, hlam, p217_0]
                      · have p217_0 := h217c.1
                        have p217_1 := h217c.2.1
                        have p217_2 := h217c.2.2.1
                        have p217_3 := h217c.2.2.2
                        linarith only [h183, h2, hc23, hc34, hlam, hphi, p217_1]
                      · have p217_0 := h217c.1
                        have p217_1 := h217c.2.1
                        have p217_2 := h217c.2.2.1
                        have p217_3 := h217c.2.2.2
                        linarith only [h182, h183, h185, hc23, hc34, hlam, hphi, p217_1]
                      · have p217_0 := h217c.1
                        have p217_1 := h217c.2.1
                        have p217_2 := h217c.2.2.1
                        have p217_3 := h217c.2.2.2
                        linarith only [h183, hc23, hc34, hlam, hphi, p217_1]
                      · have p217_0 := h217c.1
                        have p217_1 := h217c.2.1
                        have p217_2 := h217c.2.2.1
                        have p217_3 := h217c.2.2.2
                        linarith only [hlam, p217_0]
                      · have p217_0 := h217c.1
                        have p217_1 := h217c.2.1
                        have p217_2 := h217c.2.2.1
                        have p217_3 := h217c.2.2.2
                        linarith only [h183, h185, hc23, hc34, hlam, hphi, p217_1]
                      · have p217_0 := h217c.1
                        have p217_1 := h217c.2.1
                        have p217_2 := h217c.2.2.1
                        have p217_3 := h217c.2.2.2
                        linarith only [h179, hlam, p217_0]
                      · have p217_0 := h217c.1
                        have p217_1 := h217c.2.1
                        have p217_2 := h217c.2.2.1
                        have p217_3 := h217c.2.2.2
                        linarith only [h182, hlam, p217_0]
                      · have p217_0 := h217c.1
                        have p217_1 := h217c.2.1
                        have p217_2 := h217c.2.2.1
                        have p217_3 := h217c.2.2.2
                        linarith only [h0, h182, h183, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p217_1]
                      · have p217_0 := h217c.1
                        have p217_1 := h217c.2.1
                        have p217_2 := h217c.2.2.1
                        have p217_3 := h217c.2.2.2
                        linarith only [h216, hlam, p217_0]
                      · have p217_0 := h217c.1
                        have p217_1 := h217c.2.1
                        have p217_2 := h217c.2.2.1
                        have p217_3 := h217c.2.2.2
                        linarith only [hlam, p217_0]
                    · linarith only [h0, h1, h182, h2, h216, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h244 | h244
                · linarith only [h179, h182, h244, h4, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h246 | h246
                  · linarith only [h180, h182, h246, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h248 | h248
                    · rcases h4bigk with h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c
                      · have p249_0 := h249c.1
                        have p249_1 := h249c.2.1
                        have p249_2 := h249c.2.2.1
                        have p249_3 := h249c.2.2.2
                        linarith only [hlam, p249_0]
                      · have p249_0 := h249c.1
                        have p249_1 := h249c.2.1
                        have p249_2 := h249c.2.2.1
                        have p249_3 := h249c.2.2.2
                        linarith only [h180, h244, h4, hc23, hc34, hlam, hphi, p249_1]
                      · have p249_0 := h249c.1
                        have p249_1 := h249c.2.1
                        have p249_2 := h249c.2.2.1
                        have p249_3 := h249c.2.2.2
                        linarith only [h2, h244, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p249_1, u2elo0]
                      · have p249_0 := h249c.1
                        have p249_1 := h249c.2.1
                        have p249_2 := h249c.2.2.1
                        have p249_3 := h249c.2.2.2
                        linarith only [h4, hlam, p249_1]
                      · have p249_0 := h249c.1
                        have p249_1 := h249c.2.1
                        have p249_2 := h249c.2.2.1
                        have p249_3 := h249c.2.2.2
                        linarith only [h180, h182, h2, h244, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p249_1, u2elo0]
                      · have p249_0 := h249c.1
                        have p249_1 := h249c.2.1
                        have p249_2 := h249c.2.2.1
                        have p249_3 := h249c.2.2.2
                        linarith only [h0, hlam, p249_0]
                      · have p249_0 := h249c.1
                        have p249_1 := h249c.2.1
                        have p249_2 := h249c.2.2.1
                        have p249_3 := h249c.2.2.2
                        linarith only [hlam, p249_0]
                      · have p249_0 := h249c.1
                        have p249_1 := h249c.2.1
                        have p249_2 := h249c.2.2.1
                        have p249_3 := h249c.2.2.2
                        linarith only [h182, h244, hc23, hc45, hlam, hphi, ht34, p249_1]
                      · have p249_0 := h249c.1
                        have p249_1 := h249c.2.1
                        have p249_2 := h249c.2.2.1
                        have p249_3 := h249c.2.2.2
                        linarith only [h179, h182, h2, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p249_1, u2elo0]
                      · have p249_0 := h249c.1
                        have p249_1 := h249c.2.1
                        have p249_2 := h249c.2.2.1
                        have p249_3 := h249c.2.2.2
                        linarith only [h182, hlam, p249_0]
                      · have p249_0 := h249c.1
                        have p249_1 := h249c.2.1
                        have p249_2 := h249c.2.2.1
                        have p249_3 := h249c.2.2.2
                        linarith only [h2, hlam, p249_0]
                      · have p249_0 := h249c.1
                        have p249_1 := h249c.2.1
                        have p249_2 := h249c.2.2.1
                        have p249_3 := h249c.2.2.2
                        linarith only [h180, hlam, p249_0]
                      · have p249_0 := h249c.1
                        have p249_1 := h249c.2.1
                        have p249_2 := h249c.2.2.1
                        have p249_3 := h249c.2.2.2
                        linarith only [hlam, p249_0]
                      · have p249_0 := h249c.1
                        have p249_1 := h249c.2.1
                        have p249_2 := h249c.2.2.1
                        have p249_3 := h249c.2.2.2
                        linarith only [h244, hlam, p249_1]
                      · have p249_0 := h249c.1
                        have p249_1 := h249c.2.1
                        have p249_2 := h249c.2.2.1
                        have p249_3 := h249c.2.2.2
                        linarith only [h246, hlam, p249_0]
                      · have p249_0 := h249c.1
                        have p249_1 := h249c.2.1
                        have p249_2 := h249c.2.2.1
                        have p249_3 := h249c.2.2.2
                        linarith only [h179, h182, hc14, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p249_1]
                      · have p249_0 := h249c.1
                        have p249_1 := h249c.2.1
                        have p249_2 := h249c.2.2.1
                        have p249_3 := h249c.2.2.2
                        linarith only [h180, h244, hc23, hc34, hlam, hphi, p249_1]
                      · have p249_0 := h249c.1
                        have p249_1 := h249c.2.1
                        have p249_2 := h249c.2.2.1
                        have p249_3 := h249c.2.2.2
                        linarith only [h244, hc23, hc34, hlam, hphi, p249_1]
                      · have p249_0 := h249c.1
                        have p249_1 := h249c.2.1
                        have p249_2 := h249c.2.2.1
                        have p249_3 := h249c.2.2.2
                        linarith only [hlam, p249_0]
                      · have p249_0 := h249c.1
                        have p249_1 := h249c.2.1
                        have p249_2 := h249c.2.2.1
                        have p249_3 := h249c.2.2.2
                        linarith only [h180, h182, h244, hc23, hc34, hlam, hphi, p249_1]
                      · have p249_0 := h249c.1
                        have p249_1 := h249c.2.1
                        have p249_2 := h249c.2.2.1
                        have p249_3 := h249c.2.2.2
                        linarith only [h179, hlam, p249_0]
                      · have p249_0 := h249c.1
                        have p249_1 := h249c.2.1
                        have p249_2 := h249c.2.2.1
                        have p249_3 := h249c.2.2.2
                        linarith only [h179, h180, h2, h244, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p249_1]
                      · have p249_0 := h249c.1
                        have p249_1 := h249c.2.1
                        have p249_2 := h249c.2.2.1
                        have p249_3 := h249c.2.2.2
                        linarith only [h179, h2, h244, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p249_1, u2elo0]
                      · have p249_0 := h249c.1
                        have p249_1 := h249c.2.1
                        have p249_2 := h249c.2.2.1
                        have p249_3 := h249c.2.2.2
                        linarith only [h248, hlam, p249_0]
                      · have p249_0 := h249c.1
                        have p249_1 := h249c.2.1
                        have p249_2 := h249c.2.2.1
                        have p249_3 := h249c.2.2.2
                        linarith only [hlam, p249_0]
                    · linarith only [h1, h179, h2, h248, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
            · linarith only [h181, h3, hc12, hlam, hphi, u2elo0]
          · linarith only [h180, h2, hc12, hlam, hphi, u2elo0]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h278 | h278
          · rcases m.htr 1 2 5 (by decide) (by decide) with h279 | h279
            · rcases m.htr 1 4 5 (by decide) (by decide) with h280 | h280
              · linarith only [h0, h179, h280, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h282 | h282
                · linarith only [h1, h282, h4, hlam]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h284 | h284
                  · linarith only [h0, h179, h278, h284, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h286 | h286
                    · rcases h4bigk with h287c | h287c | h287c | h287c | h287c | h287c | h287c | h287c | h287c | h287c | h287c | h287c | h287c | h287c | h287c | h287c | h287c | h287c | h287c | h287c | h287c | h287c | h287c | h287c | h287c
                      · have p287_0 := h287c.1
                        have p287_1 := h287c.2.1
                        have p287_2 := h287c.2.2.1
                        have p287_3 := h287c.2.2.2
                        linarith only [hlam, p287_0]
                      · have p287_0 := h287c.1
                        have p287_1 := h287c.2.1
                        have p287_2 := h287c.2.2.1
                        have p287_3 := h287c.2.2.2
                        linarith only [h179, h278, h286, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p287_1]
                      · have p287_0 := h287c.1
                        have p287_1 := h287c.2.1
                        have p287_2 := h287c.2.2.1
                        have p287_3 := h287c.2.2.2
                        linarith only [h179, h286, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p287_1]
                      · have p287_0 := h287c.1
                        have p287_1 := h287c.2.1
                        have p287_2 := h287c.2.2.1
                        have p287_3 := h287c.2.2.2
                        linarith only [h4, hlam, p287_1]
                      · have p287_0 := h287c.1
                        have p287_1 := h287c.2.1
                        have p287_2 := h287c.2.2.1
                        have p287_3 := h287c.2.2.2
                        linarith only [h179, hlam, p287_0]
                      · have p287_0 := h287c.1
                        have p287_1 := h287c.2.1
                        have p287_2 := h287c.2.2.1
                        have p287_3 := h287c.2.2.2
                        linarith only [h0, hlam, p287_0]
                      · have p287_0 := h287c.1
                        have p287_1 := h287c.2.1
                        have p287_2 := h287c.2.2.1
                        have p287_3 := h287c.2.2.2
                        linarith only [hlam, p287_0]
                      · have p287_0 := h287c.1
                        have p287_1 := h287c.2.1
                        have p287_2 := h287c.2.2.1
                        have p287_3 := h287c.2.2.2
                        linarith only [h0, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p287_1]
                      · have p287_0 := h287c.1
                        have p287_1 := h287c.2.1
                        have p287_2 := h287c.2.2.1
                        have p287_3 := h287c.2.2.2
                        linarith only [h0, h179, h286, hlam, p287_1]
                      · have p287_0 := h287c.1
                        have p287_1 := h287c.2.1
                        have p287_2 := h287c.2.2.1
                        have p287_3 := h287c.2.2.2
                        linarith only [h280, hlam, p287_0]
                      · have p287_0 := h287c.1
                        have p287_1 := h287c.2.1
                        have p287_2 := h287c.2.2.1
                        have p287_3 := h287c.2.2.2
                        linarith only [h2, hlam, p287_0]
                      · have p287_0 := h287c.1
                        have p287_1 := h287c.2.1
                        have p287_2 := h287c.2.2.1
                        have p287_3 := h287c.2.2.2
                        linarith only [h278, hlam, p287_0]
                      · have p287_0 := h287c.1
                        have p287_1 := h287c.2.1
                        have p287_2 := h287c.2.2.1
                        have p287_3 := h287c.2.2.2
                        linarith only [hlam, p287_0]
                      · have p287_0 := h287c.1
                        have p287_1 := h287c.2.1
                        have p287_2 := h287c.2.2.1
                        have p287_3 := h287c.2.2.2
                        linarith only [h282, hlam, p287_1]
                      · have p287_0 := h287c.1
                        have p287_1 := h287c.2.1
                        have p287_2 := h287c.2.2.1
                        have p287_3 := h287c.2.2.2
                        linarith only [h284, hlam, p287_0]
                      · have p287_0 := h287c.1
                        have p287_1 := h287c.2.1
                        have p287_2 := h287c.2.2.1
                        have p287_3 := h287c.2.2.2
                        linarith only [h2, h282, hc23, hc34, hlam, hphi, p287_1]
                      · have p287_0 := h287c.1
                        have p287_1 := h287c.2.1
                        have p287_2 := h287c.2.2.1
                        have p287_3 := h287c.2.2.2
                        linarith only [h278, h282, hc23, hc34, hlam, hphi, p287_1]
                      · have p287_0 := h287c.1
                        have p287_1 := h287c.2.1
                        have p287_2 := h287c.2.2.1
                        have p287_3 := h287c.2.2.2
                        linarith only [h282, hc23, hc34, hlam, hphi, p287_1]
                      · have p287_0 := h287c.1
                        have p287_1 := h287c.2.1
                        have p287_2 := h287c.2.2.1
                        have p287_3 := h287c.2.2.2
                        linarith only [hlam, p287_0]
                      · have p287_0 := h287c.1
                        have p287_1 := h287c.2.1
                        have p287_2 := h287c.2.2.1
                        have p287_3 := h287c.2.2.2
                        linarith only [h0, h179, h278, h282, hc23, hc34, hlam, hphi, p287_1]
                      · have p287_0 := h287c.1
                        have p287_1 := h287c.2.1
                        have p287_2 := h287c.2.2.1
                        have p287_3 := h287c.2.2.2
                        linarith only [h0, h278, h282, hc23, hc45, hlam, hphi, ht34, p287_1]
                      · have p287_0 := h287c.1
                        have p287_1 := h287c.2.1
                        have p287_2 := h287c.2.2.1
                        have p287_3 := h287c.2.2.2
                        linarith only [h278, h282, hc23, hc45, hlam, hphi, ht34, p287_1]
                      · have p287_0 := h287c.1
                        have p287_1 := h287c.2.1
                        have p287_2 := h287c.2.2.1
                        have p287_3 := h287c.2.2.2
                        linarith only [h282, hc23, hc45, hlam, hphi, ht34, p287_1]
                      · have p287_0 := h287c.1
                        have p287_1 := h287c.2.1
                        have p287_2 := h287c.2.2.1
                        have p287_3 := h287c.2.2.2
                        linarith only [h286, hlam, p287_0]
                      · have p287_0 := h287c.1
                        have p287_1 := h287c.2.1
                        have p287_2 := h287c.2.2.1
                        have p287_3 := h287c.2.2.2
                        linarith only [hlam, p287_0]
                    · rcases h4bigk with h313c | h313c | h313c | h313c | h313c | h313c | h313c | h313c | h313c | h313c | h313c | h313c | h313c | h313c | h313c | h313c | h313c | h313c | h313c | h313c | h313c | h313c | h313c | h313c | h313c
                      · have p313_0 := h313c.1
                        have p313_1 := h313c.2.1
                        have p313_2 := h313c.2.2.1
                        have p313_3 := h313c.2.2.2
                        linarith only [hlam, p313_0]
                      · have p313_0 := h313c.1
                        have p313_1 := h313c.2.1
                        have p313_2 := h313c.2.2.1
                        have p313_3 := h313c.2.2.2
                        linarith only [h2, h278, h282, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p313_1, u2elo0]
                      · have p313_0 := h313c.1
                        have p313_1 := h313c.2.1
                        have p313_2 := h313c.2.2.1
                        have p313_3 := h313c.2.2.2
                        linarith only [h2, h282, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p313_1, u2elo0]
                      · have p313_0 := h313c.1
                        have p313_1 := h313c.2.1
                        have p313_2 := h313c.2.2.1
                        have p313_3 := h313c.2.2.2
                        linarith only [h4, hlam, p313_1]
                      · have p313_0 := h313c.1
                        have p313_1 := h313c.2.1
                        have p313_2 := h313c.2.2.1
                        have p313_3 := h313c.2.2.2
                        linarith only [h179, hlam, p313_0]
                      · have p313_0 := h313c.1
                        have p313_1 := h313c.2.1
                        have p313_2 := h313c.2.2.1
                        have p313_3 := h313c.2.2.2
                        linarith only [h0, hlam, p313_0]
                      · have p313_0 := h313c.1
                        have p313_1 := h313c.2.1
                        have p313_2 := h313c.2.2.1
                        have p313_3 := h313c.2.2.2
                        linarith only [hlam, p313_0]
                      · have p313_0 := h313c.1
                        have p313_1 := h313c.2.1
                        have p313_2 := h313c.2.2.1
                        have p313_3 := h313c.2.2.2
                        linarith only [h0, h282, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p313_1]
                      · have p313_0 := h313c.1
                        have p313_1 := h313c.2.1
                        have p313_2 := h313c.2.2.1
                        have p313_3 := h313c.2.2.2
                        linarith only [h0, h4, hlam, p313_1]
                      · have p313_0 := h313c.1
                        have p313_1 := h313c.2.1
                        have p313_2 := h313c.2.2.1
                        have p313_3 := h313c.2.2.2
                        linarith only [h280, hlam, p313_0]
                      · have p313_0 := h313c.1
                        have p313_1 := h313c.2.1
                        have p313_2 := h313c.2.2.1
                        have p313_3 := h313c.2.2.2
                        linarith only [h2, hlam, p313_0]
                      · have p313_0 := h313c.1
                        have p313_1 := h313c.2.1
                        have p313_2 := h313c.2.2.1
                        have p313_3 := h313c.2.2.2
                        linarith only [h278, hlam, p313_0]
                      · have p313_0 := h313c.1
                        have p313_1 := h313c.2.1
                        have p313_2 := h313c.2.2.1
                        have p313_3 := h313c.2.2.2
                        linarith only [hlam, p313_0]
                      · have p313_0 := h313c.1
                        have p313_1 := h313c.2.1
                        have p313_2 := h313c.2.2.1
                        have p313_3 := h313c.2.2.2
                        linarith only [h282, hlam, p313_1]
                      · have p313_0 := h313c.1
                        have p313_1 := h313c.2.1
                        have p313_2 := h313c.2.2.1
                        have p313_3 := h313c.2.2.2
                        linarith only [h284, hlam, p313_0]
                      · have p313_0 := h313c.1
                        have p313_1 := h313c.2.1
                        have p313_2 := h313c.2.2.1
                        have p313_3 := h313c.2.2.2
                        linarith only [h286, hc04, hc45, hlam, hphi, p313_1]
                      · have p313_0 := h313c.1
                        have p313_1 := h313c.2.1
                        have p313_2 := h313c.2.2.1
                        have p313_3 := h313c.2.2.2
                        linarith only [h278, h282, h286, hc23, hc45, hlam, hphi, ht34, p313_1]
                      · have p313_0 := h313c.1
                        have p313_1 := h313c.2.1
                        have p313_2 := h313c.2.2.1
                        have p313_3 := h313c.2.2.2
                        linarith only [h282, h286, hc23, hc45, hlam, hphi, ht34, p313_1]
                      · have p313_0 := h313c.1
                        have p313_1 := h313c.2.1
                        have p313_2 := h313c.2.2.1
                        have p313_3 := h313c.2.2.2
                        linarith only [hlam, p313_0]
                      · have p313_0 := h313c.1
                        have p313_1 := h313c.2.1
                        have p313_2 := h313c.2.2.1
                        have p313_3 := h313c.2.2.2
                        linarith only [h286, hlam, p313_0]
                      · have p313_0 := h313c.1
                        have p313_1 := h313c.2.1
                        have p313_2 := h313c.2.2.1
                        have p313_3 := h313c.2.2.2
                        linarith only [h0, h278, h282, hc23, hc45, hlam, hphi, ht34, p313_1]
                      · have p313_0 := h313c.1
                        have p313_1 := h313c.2.1
                        have p313_2 := h313c.2.2.1
                        have p313_3 := h313c.2.2.2
                        linarith only [h278, h282, hc23, hc45, hlam, hphi, ht34, p313_1]
                      · have p313_0 := h313c.1
                        have p313_1 := h313c.2.1
                        have p313_2 := h313c.2.2.1
                        have p313_3 := h313c.2.2.2
                        linarith only [h282, hc23, hc45, hlam, hphi, ht34, p313_1]
                      · have p313_0 := h313c.1
                        have p313_1 := h313c.2.1
                        have p313_2 := h313c.2.2.1
                        have p313_3 := h313c.2.2.2
                        linarith only [hc34, hc45, hlam, hphi, p313_1]
                      · have p313_0 := h313c.1
                        have p313_1 := h313c.2.1
                        have p313_2 := h313c.2.2.1
                        have p313_3 := h313c.2.2.2
                        linarith only [hlam, p313_0]
            · linarith only [h279, h3, hc12, hlam, hphi, u2elo0]
          · linarith only [h2, h278, hc12, hlam, hphi, u2elo0]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h341 | h341
      · rcases m.htr 0 4 5 (by decide) (by decide) with h342 | h342
        · linarith only [h2, h3, h342, hlam]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h344 | h344
          · rcases m.htr 1 2 5 (by decide) (by decide) with h345 | h345
            · linarith only [h1, h3, h345, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h347 | h347
              · linarith only [h0, h342, h347, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h349 | h349
                · linarith only [h1, h3, h349, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4]
                · linarith only [h1, h3, h341, h349, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
          · linarith only [h2, h3, h344, hc12, hlam, hphi, u2elo4]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h353 | h353
        · linarith only [h2, h3, h353, hlam]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h355 | h355
          · rcases m.htr 1 2 5 (by decide) (by decide) with h356 | h356
            · linarith only [h3, h356, hc02, hlam, hphi, u2elo1]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h358 | h358
              · linarith only [h0, h353, h358, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h360 | h360
                · linarith only [h1, h341, h360, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h362 | h362
                  · linarith only [h2, h3, h362, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h364 | h364
                    · linarith only [h1, h3, h362, h364, hc23, hc34, hlam, hphi]
                    · rcases h4bigk with h366c | h366c | h366c | h366c | h366c | h366c | h366c | h366c | h366c | h366c | h366c | h366c | h366c | h366c | h366c | h366c | h366c | h366c | h366c | h366c | h366c | h366c | h366c | h366c | h366c
                      · have p366_0 := h366c.1
                        have p366_1 := h366c.2.1
                        have p366_2 := h366c.2.2.1
                        have p366_3 := h366c.2.2.2
                        linarith only [hlam, p366_0]
                      · have p366_0 := h366c.1
                        have p366_1 := h366c.2.1
                        have p366_2 := h366c.2.2.1
                        have p366_3 := h366c.2.2.2
                        linarith only [h2, h3, h355, h360, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p366_1, u2elo4]
                      · have p366_0 := h366c.1
                        have p366_1 := h366c.2.1
                        have p366_2 := h366c.2.2.1
                        have p366_3 := h366c.2.2.2
                        linarith only [h2, h3, h360, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p366_1, u2elo4]
                      · have p366_0 := h366c.1
                        have p366_1 := h366c.2.1
                        have p366_2 := h366c.2.2.1
                        have p366_3 := h366c.2.2.2
                        linarith only [h341, hlam, p366_1]
                      · have p366_0 := h366c.1
                        have p366_1 := h366c.2.1
                        have p366_2 := h366c.2.2.1
                        have p366_3 := h366c.2.2.2
                        linarith only [h353, hlam, p366_0]
                      · have p366_0 := h366c.1
                        have p366_1 := h366c.2.1
                        have p366_2 := h366c.2.2.1
                        have p366_3 := h366c.2.2.2
                        linarith only [h0, hlam, p366_0]
                      · have p366_0 := h366c.1
                        have p366_1 := h366c.2.1
                        have p366_2 := h366c.2.2.1
                        have p366_3 := h366c.2.2.2
                        linarith only [hlam, p366_0]
                      · have p366_0 := h366c.1
                        have p366_1 := h366c.2.1
                        have p366_2 := h366c.2.2.1
                        have p366_3 := h366c.2.2.2
                        linarith only [h0, h360, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p366_1]
                      · have p366_0 := h366c.1
                        have p366_1 := h366c.2.1
                        have p366_2 := h366c.2.2.1
                        have p366_3 := h366c.2.2.2
                        linarith only [h0, h2, h3, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p366_1, u2elo4]
                      · have p366_0 := h366c.1
                        have p366_1 := h366c.2.1
                        have p366_2 := h366c.2.2.1
                        have p366_3 := h366c.2.2.2
                        linarith only [h358, hlam, p366_0]
                      · have p366_0 := h366c.1
                        have p366_1 := h366c.2.1
                        have p366_2 := h366c.2.2.1
                        have p366_3 := h366c.2.2.2
                        linarith only [h2, hlam, p366_0]
                      · have p366_0 := h366c.1
                        have p366_1 := h366c.2.1
                        have p366_2 := h366c.2.2.1
                        have p366_3 := h366c.2.2.2
                        linarith only [h355, hlam, p366_0]
                      · have p366_0 := h366c.1
                        have p366_1 := h366c.2.1
                        have p366_2 := h366c.2.2.1
                        have p366_3 := h366c.2.2.2
                        linarith only [hlam, p366_0]
                      · have p366_0 := h366c.1
                        have p366_1 := h366c.2.1
                        have p366_2 := h366c.2.2.1
                        have p366_3 := h366c.2.2.2
                        linarith only [h360, hlam, p366_1]
                      · have p366_0 := h366c.1
                        have p366_1 := h366c.2.1
                        have p366_2 := h366c.2.2.1
                        have p366_3 := h366c.2.2.2
                        linarith only [h362, hlam, p366_0]
                      · have p366_0 := h366c.1
                        have p366_1 := h366c.2.1
                        have p366_2 := h366c.2.2.1
                        have p366_3 := h366c.2.2.2
                        linarith only [h2, h360, hc23, hc34, hlam, hphi, p366_1]
                      · have p366_0 := h366c.1
                        have p366_1 := h366c.2.1
                        have p366_2 := h366c.2.2.1
                        have p366_3 := h366c.2.2.2
                        linarith only [h355, h360, h364, hc23, hc45, hlam, hphi, ht34, p366_1]
                      · have p366_0 := h366c.1
                        have p366_1 := h366c.2.1
                        have p366_2 := h366c.2.2.1
                        have p366_3 := h366c.2.2.2
                        linarith only [h360, h364, hc23, hc45, hlam, hphi, ht34, p366_1]
                      · have p366_0 := h366c.1
                        have p366_1 := h366c.2.1
                        have p366_2 := h366c.2.2.1
                        have p366_3 := h366c.2.2.2
                        linarith only [hlam, p366_0]
                      · have p366_0 := h366c.1
                        have p366_1 := h366c.2.1
                        have p366_2 := h366c.2.2.1
                        have p366_3 := h366c.2.2.2
                        linarith only [h364, hlam, p366_0]
                      · have p366_0 := h366c.1
                        have p366_1 := h366c.2.1
                        have p366_2 := h366c.2.2.1
                        have p366_3 := h366c.2.2.2
                        linarith only [h0, h355, h360, hc23, hc45, hlam, hphi, ht34, p366_1]
                      · have p366_0 := h366c.1
                        have p366_1 := h366c.2.1
                        have p366_2 := h366c.2.2.1
                        have p366_3 := h366c.2.2.2
                        linarith only [h355, h360, hc23, hc45, hlam, hphi, ht34, p366_1]
                      · have p366_0 := h366c.1
                        have p366_1 := h366c.2.1
                        have p366_2 := h366c.2.2.1
                        have p366_3 := h366c.2.2.2
                        linarith only [h360, hc23, hc45, hlam, hphi, ht34, p366_1]
                      · have p366_0 := h366c.1
                        have p366_1 := h366c.2.1
                        have p366_2 := h366c.2.2.1
                        have p366_3 := h366c.2.2.2
                        linarith only [hc34, hc45, hlam, hphi, p366_1]
                      · have p366_0 := h366c.1
                        have p366_1 := h366c.2.1
                        have p366_2 := h366c.2.2.1
                        have p366_3 := h366c.2.2.2
                        linarith only [hlam, p366_0]
          · linarith only [h2, h3, h355, hc12, hlam, hphi, u2elo4]
  · rcases m.htr 0 2 5 (by decide) (by decide) with h393 | h393
    · rcases m.htr 0 3 4 (by decide) (by decide) with h394 | h394
      · linarith only [h1, h2, h394, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h396 | h396
        · rcases m.htr 1 2 4 (by decide) (by decide) with h397 | h397
          · linarith only [h2, h397, hc02, hlam, hphi, u2elo1]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h399 | h399
            · rcases m.htr 1 4 5 (by decide) (by decide) with h400 | h400
              · rcases m.htr 2 3 4 (by decide) (by decide) with h401 | h401
                · linarith only [h1, h2, h394, h401, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h403 | h403
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h404 | h404
                    · rcases h4bigk with h405c | h405c | h405c | h405c | h405c | h405c | h405c | h405c | h405c | h405c | h405c | h405c | h405c | h405c | h405c | h405c | h405c | h405c | h405c | h405c | h405c | h405c | h405c | h405c | h405c
                      · have p405_0 := h405c.1
                        have p405_1 := h405c.2.1
                        have p405_2 := h405c.2.2.1
                        have p405_3 := h405c.2.2.2
                        linarith only [hlam, p405_0]
                      · have p405_0 := h405c.1
                        have p405_1 := h405c.2.1
                        have p405_2 := h405c.2.2.1
                        have p405_3 := h405c.2.2.2
                        linarith only [h397, h399, hc04, hc25, hlam, hphi, ht0b, ht5b, p405_1]
                      · have p405_0 := h405c.1
                        have p405_1 := h405c.2.1
                        have p405_2 := h405c.2.2.1
                        have p405_3 := h405c.2.2.2
                        linarith only [h2, hlam, p405_1]
                      · have p405_0 := h405c.1
                        have p405_1 := h405c.2.1
                        have p405_2 := h405c.2.2.1
                        have p405_3 := h405c.2.2.2
                        linarith only [h394, hlam, p405_1]
                      · have p405_0 := h405c.1
                        have p405_1 := h405c.2.1
                        have p405_2 := h405c.2.2.1
                        have p405_3 := h405c.2.2.2
                        linarith only [h2, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p405_1, u2elo3]
                      · have p405_0 := h405c.1
                        have p405_1 := h405c.2.1
                        have p405_2 := h405c.2.2.1
                        have p405_3 := h405c.2.2.2
                        linarith only [h0, hlam, p405_0]
                      · have p405_0 := h405c.1
                        have p405_1 := h405c.2.1
                        have p405_2 := h405c.2.2.1
                        have p405_3 := h405c.2.2.2
                        linarith only [hlam, p405_0]
                      · have p405_0 := h405c.1
                        have p405_1 := h405c.2.1
                        have p405_2 := h405c.2.2.1
                        have p405_3 := h405c.2.2.2
                        linarith only [h397, hlam, p405_1]
                      · have p405_0 := h405c.1
                        have p405_1 := h405c.2.1
                        have p405_2 := h405c.2.2.1
                        have p405_3 := h405c.2.2.2
                        linarith only [h2, h401, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p405_1]
                      · have p405_0 := h405c.1
                        have p405_1 := h405c.2.1
                        have p405_2 := h405c.2.2.1
                        have p405_3 := h405c.2.2.2
                        linarith only [h0, h2, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p405_1, u2elo3]
                      · have p405_0 := h405c.1
                        have p405_1 := h405c.2.1
                        have p405_2 := h405c.2.2.1
                        have p405_3 := h405c.2.2.2
                        linarith only [hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p405_1, u2elo3]
                      · have p405_0 := h405c.1
                        have p405_1 := h405c.2.1
                        have p405_2 := h405c.2.2.1
                        have p405_3 := h405c.2.2.2
                        linarith only [hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p405_1, u2elo3]
                      · have p405_0 := h405c.1
                        have p405_1 := h405c.2.1
                        have p405_2 := h405c.2.2.1
                        have p405_3 := h405c.2.2.2
                        linarith only [hlam, p405_0]
                      · have p405_0 := h405c.1
                        have p405_1 := h405c.2.1
                        have p405_2 := h405c.2.2.1
                        have p405_3 := h405c.2.2.2
                        linarith only [h401, hlam, p405_1]
                      · have p405_0 := h405c.1
                        have p405_1 := h405c.2.1
                        have p405_2 := h405c.2.2.1
                        have p405_3 := h405c.2.2.2
                        linarith only [hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p405_1, u2elo3]
                      · have p405_0 := h405c.1
                        have p405_1 := h405c.2.1
                        have p405_2 := h405c.2.2.1
                        have p405_3 := h405c.2.2.2
                        linarith only [h1, h2, hc23, hc34, hlam, hphi, p405_1]
                      · have p405_0 := h405c.1
                        have p405_1 := h405c.2.1
                        have p405_2 := h405c.2.2.1
                        have p405_3 := h405c.2.2.2
                        linarith only [h397, h399, h403, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p405_1]
                      · have p405_0 := h405c.1
                        have p405_1 := h405c.2.1
                        have p405_2 := h405c.2.2.1
                        have p405_3 := h405c.2.2.2
                        linarith only [h1, h2, hc23, hc34, hlam, hphi, p405_1]
                      · have p405_0 := h405c.1
                        have p405_1 := h405c.2.1
                        have p405_2 := h405c.2.2.1
                        have p405_3 := h405c.2.2.2
                        linarith only [hlam, p405_0]
                      · have p405_0 := h405c.1
                        have p405_1 := h405c.2.1
                        have p405_2 := h405c.2.2.1
                        have p405_3 := h405c.2.2.2
                        rcases p405_3 (m.d 0 4) (by simp) with h425 | h425
                        · linarith only [h394, h425, hlam]
                        · linarith only [h396, h425, hlam]
                      · have p405_0 := h405c.1
                        have p405_1 := h405c.2.1
                        have p405_2 := h405c.2.2.1
                        have p405_3 := h405c.2.2.2
                        linarith only [h396, hlam, p405_0]
                      · have p405_0 := h405c.1
                        have p405_1 := h405c.2.1
                        have p405_2 := h405c.2.2.1
                        have p405_3 := h405c.2.2.2
                        linarith only [h400, hlam, p405_0]
                      · have p405_0 := h405c.1
                        have p405_1 := h405c.2.1
                        have p405_2 := h405c.2.2.1
                        have p405_3 := h405c.2.2.2
                        linarith only [h403, hlam, p405_0]
                      · have p405_0 := h405c.1
                        have p405_1 := h405c.2.1
                        have p405_2 := h405c.2.2.1
                        have p405_3 := h405c.2.2.2
                        linarith only [h404, hlam, p405_0]
                      · have p405_0 := h405c.1
                        have p405_1 := h405c.2.1
                        have p405_2 := h405c.2.2.1
                        have p405_3 := h405c.2.2.2
                        linarith only [hlam, p405_0]
                    · linarith only [h2, h393, h403, h404, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3]
                  · linarith only [h1, h2, h403, hc23, hc45, hlam, hphi, ht34]
              · linarith only [h2, h393, h396, h397, h400, hc12, hlam, hphi, u2elo3]
            · linarith only [h2, h393, h399, hc12, hlam, hphi, u2elo3]
        · linarith only [h2, h393, h396, hlam]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h438 | h438
      · linarith only [h1, h2, h438, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h440 | h440
        · rcases m.htr 1 2 4 (by decide) (by decide) with h441 | h441
          · linarith only [h2, h441, hc02, hlam, hphi, u2elo1]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h443 | h443
            · linarith only [h1, h393, h443, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h445 | h445
              · rcases m.htr 2 3 4 (by decide) (by decide) with h446 | h446
                · linarith only [h1, h393, h438, h446, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h448 | h448
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h449 | h449
                    · rcases h4bigk with h450c | h450c | h450c | h450c | h450c | h450c | h450c | h450c | h450c | h450c | h450c | h450c | h450c | h450c | h450c | h450c | h450c | h450c | h450c | h450c | h450c | h450c | h450c | h450c | h450c
                      · have p450_0 := h450c.1
                        have p450_1 := h450c.2.1
                        have p450_2 := h450c.2.2.1
                        have p450_3 := h450c.2.2.2
                        linarith only [hlam, p450_0]
                      · have p450_0 := h450c.1
                        have p450_1 := h450c.2.1
                        have p450_2 := h450c.2.2.1
                        have p450_3 := h450c.2.2.2
                        linarith only [h2, h443, h445, hc12, hlam, hphi, p450_1, u2elo3]
                      · have p450_0 := h450c.1
                        have p450_1 := h450c.2.1
                        have p450_2 := h450c.2.2.1
                        have p450_3 := h450c.2.2.2
                        linarith only [h2, hlam, p450_1]
                      · have p450_0 := h450c.1
                        have p450_1 := h450c.2.1
                        have p450_2 := h450c.2.2.1
                        have p450_3 := h450c.2.2.2
                        linarith only [h438, hlam, p450_1]
                      · have p450_0 := h450c.1
                        have p450_1 := h450c.2.1
                        have p450_2 := h450c.2.2.1
                        have p450_3 := h450c.2.2.2
                        linarith only [h2, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p450_1, u2elo3]
                      · have p450_0 := h450c.1
                        have p450_1 := h450c.2.1
                        have p450_2 := h450c.2.2.1
                        have p450_3 := h450c.2.2.2
                        linarith only [h0, hlam, p450_0]
                      · have p450_0 := h450c.1
                        have p450_1 := h450c.2.1
                        have p450_2 := h450c.2.2.1
                        have p450_3 := h450c.2.2.2
                        linarith only [hlam, p450_0]
                      · have p450_0 := h450c.1
                        have p450_1 := h450c.2.1
                        have p450_2 := h450c.2.2.1
                        have p450_3 := h450c.2.2.2
                        linarith only [h441, hlam, p450_1]
                      · have p450_0 := h450c.1
                        have p450_1 := h450c.2.1
                        have p450_2 := h450c.2.2.1
                        have p450_3 := h450c.2.2.2
                        linarith only [h393, h446, h448, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p450_1]
                      · have p450_0 := h450c.1
                        have p450_1 := h450c.2.1
                        have p450_2 := h450c.2.2.1
                        have p450_3 := h450c.2.2.2
                        linarith only [h0, hc01, hc45, hlam, hphi, ht0b, ht5b, p450_1]
                      · have p450_0 := h450c.1
                        have p450_1 := h450c.2.1
                        have p450_2 := h450c.2.2.1
                        have p450_3 := h450c.2.2.2
                        linarith only [h1, h393, h440, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p450_1, u2elo3]
                      · have p450_0 := h450c.1
                        have p450_1 := h450c.2.1
                        have p450_2 := h450c.2.2.1
                        have p450_3 := h450c.2.2.2
                        linarith only [hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p450_1, u2elo3]
                      · have p450_0 := h450c.1
                        have p450_1 := h450c.2.1
                        have p450_2 := h450c.2.2.1
                        have p450_3 := h450c.2.2.2
                        linarith only [hlam, p450_0]
                      · have p450_0 := h450c.1
                        have p450_1 := h450c.2.1
                        have p450_2 := h450c.2.2.1
                        have p450_3 := h450c.2.2.2
                        linarith only [h446, hlam, p450_1]
                      · have p450_0 := h450c.1
                        have p450_1 := h450c.2.1
                        have p450_2 := h450c.2.2.1
                        have p450_3 := h450c.2.2.2
                        linarith only [hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p450_1, u2elo3]
                      · have p450_0 := h450c.1
                        have p450_1 := h450c.2.1
                        have p450_2 := h450c.2.2.1
                        have p450_3 := h450c.2.2.2
                        linarith only [h1, h393, h440, hc23, hc34, hlam, hphi, p450_1]
                      · have p450_0 := h450c.1
                        have p450_1 := h450c.2.1
                        have p450_2 := h450c.2.2.1
                        have p450_3 := h450c.2.2.2
                        linarith only [h445, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p450_1]
                      · have p450_0 := h450c.1
                        have p450_1 := h450c.2.1
                        have p450_2 := h450c.2.2.1
                        have p450_3 := h450c.2.2.2
                        linarith only [h1, h2, hc23, hc34, hlam, hphi, p450_1]
                      · have p450_0 := h450c.1
                        have p450_1 := h450c.2.1
                        have p450_2 := h450c.2.2.1
                        have p450_3 := h450c.2.2.2
                        linarith only [hlam, p450_0]
                      · have p450_0 := h450c.1
                        have p450_1 := h450c.2.1
                        have p450_2 := h450c.2.2.1
                        have p450_3 := h450c.2.2.2
                        rcases p450_3 (m.d 0 4) (by simp) with h470 | h470
                        · linarith only [h438, h470, hlam]
                        · linarith only [h440, h470, hlam]
                      · have p450_0 := h450c.1
                        have p450_1 := h450c.2.1
                        have p450_2 := h450c.2.2.1
                        have p450_3 := h450c.2.2.2
                        linarith only [h440, hlam, p450_0]
                      · have p450_0 := h450c.1
                        have p450_1 := h450c.2.1
                        have p450_2 := h450c.2.2.1
                        have p450_3 := h450c.2.2.2
                        linarith only [h445, hlam, p450_0]
                      · have p450_0 := h450c.1
                        have p450_1 := h450c.2.1
                        have p450_2 := h450c.2.2.1
                        have p450_3 := h450c.2.2.2
                        linarith only [h448, hlam, p450_0]
                      · have p450_0 := h450c.1
                        have p450_1 := h450c.2.1
                        have p450_2 := h450c.2.2.1
                        have p450_3 := h450c.2.2.2
                        linarith only [h449, hlam, p450_0]
                      · have p450_0 := h450c.1
                        have p450_1 := h450c.2.1
                        have p450_2 := h450c.2.2.1
                        have p450_3 := h450c.2.2.2
                        linarith only [hlam, p450_0]
                    · linarith only [h0, h1, h438, h445, h449, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                  · linarith only [h0, h1, h2, h445, h448, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
              · linarith only [h2, h440, h441, h445, hc12, hlam, hphi, u2elo3]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h481 | h481
          · linarith only [h1, h2, h481, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h483 | h483
            · linarith only [h1, h393, h483, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h485 | h485
              · linarith only [h0, h440, h485, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h487 | h487
                · linarith only [h1, h2, h487, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h489 | h489
                  · linarith only [h2, h440, h489, hc02, hlam, hphi, u2elo3]
                  · linarith only [h1, h2, h489, hc23, hc45, hlam, hphi, ht34]

end R2N4
