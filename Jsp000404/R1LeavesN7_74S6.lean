import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_12_23_L_0_H_I_x0 (m : N7Model)
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
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
  have h3bigk := hb3.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
  · rcases m.htr 0 2 3 (by decide) (by decide) with h2 | h2
    · rcases m.htr 0 3 4 (by decide) (by decide) with h3 | h3
      · rcases m.htr 0 3 5 (by decide) (by decide) with h4 | h4
        · rcases m.htr 1 2 3 (by decide) (by decide) with h5 | h5
          · rcases m.htr 1 3 4 (by decide) (by decide) with h6 | h6
            · rcases m.htr 1 3 5 (by decide) (by decide) with h7 | h7
              · rcases m.htr 2 3 4 (by decide) (by decide) with h8 | h8
                · rcases m.htr 2 3 5 (by decide) (by decide) with h9 | h9
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h10 | h10
                    · linarith only [h0, h10, h5, h8, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0]
                    · rcases h3bigk with h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c
                      · have p12_0 := h12c.1
                        have p12_1 := h12c.2.1
                        have p12_2 := h12c.2.2.1
                        have p12_3 := h12c.2.2.2
                        linarith only [hlam, p12_0]
                      · have p12_0 := h12c.1
                        have p12_1 := h12c.2.1
                        have p12_2 := h12c.2.2.1
                        have p12_3 := h12c.2.2.2
                        linarith only [h2, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p12_1, u2elo0]
                      · have p12_0 := h12c.1
                        have p12_1 := h12c.2.1
                        have p12_2 := h12c.2.2.1
                        have p12_3 := h12c.2.2.2
                        linarith only [h2, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p12_1, u2elo0]
                      · have p12_0 := h12c.1
                        have p12_1 := h12c.2.1
                        have p12_2 := h12c.2.2.1
                        have p12_3 := h12c.2.2.2
                        linarith only [h2, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p12_1, u2elo0]
                      · have p12_0 := h12c.1
                        have p12_1 := h12c.2.1
                        have p12_2 := h12c.2.2.1
                        have p12_3 := h12c.2.2.2
                        linarith only [h10, h2, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p12_1, u2elo0]
                      · have p12_0 := h12c.1
                        have p12_1 := h12c.2.1
                        have p12_2 := h12c.2.2.1
                        have p12_3 := h12c.2.2.2
                        linarith only [h1, hlam, p12_0]
                      · have p12_0 := h12c.1
                        have p12_1 := h12c.2.1
                        have p12_2 := h12c.2.2.1
                        have p12_3 := h12c.2.2.2
                        linarith only [hlam, p12_0]
                      · have p12_0 := h12c.1
                        have p12_1 := h12c.2.1
                        have p12_2 := h12c.2.2.1
                        have p12_3 := h12c.2.2.2
                        linarith only [h10, h9, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p12_1]
                      · have p12_0 := h12c.1
                        have p12_1 := h12c.2.1
                        have p12_2 := h12c.2.2.1
                        have p12_3 := h12c.2.2.2
                        linarith only [h1, h2, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p12_1, u2elo0]
                      · have p12_0 := h12c.1
                        have p12_1 := h12c.2.1
                        have p12_2 := h12c.2.2.1
                        have p12_3 := h12c.2.2.2
                        linarith only [h1, h10, h2, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p12_1, u2elo0]
                      · have p12_0 := h12c.1
                        have p12_1 := h12c.2.1
                        have p12_2 := h12c.2.2.1
                        have p12_3 := h12c.2.2.2
                        linarith only [h2, hlam, p12_0]
                      · have p12_0 := h12c.1
                        have p12_1 := h12c.2.1
                        have p12_2 := h12c.2.2.1
                        have p12_3 := h12c.2.2.2
                        linarith only [h5, hlam, p12_0]
                      · have p12_0 := h12c.1
                        have p12_1 := h12c.2.1
                        have p12_2 := h12c.2.2.1
                        have p12_3 := h12c.2.2.2
                        linarith only [hlam, p12_0]
                      · have p12_0 := h12c.1
                        have p12_1 := h12c.2.1
                        have p12_2 := h12c.2.2.1
                        have p12_3 := h12c.2.2.2
                        linarith only [hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p12_1, u2elo2]
                      · have p12_0 := h12c.1
                        have p12_1 := h12c.2.1
                        have p12_2 := h12c.2.2.1
                        have p12_3 := h12c.2.2.2
                        linarith only [h0, h10, h5, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p12_1, u2elo0]
                      · have p12_0 := h12c.1
                        have p12_1 := h12c.2.1
                        have p12_2 := h12c.2.2.1
                        have p12_3 := h12c.2.2.2
                        linarith only [h3, hlam, p12_0]
                      · have p12_0 := h12c.1
                        have p12_1 := h12c.2.1
                        have p12_2 := h12c.2.2.1
                        have p12_3 := h12c.2.2.2
                        linarith only [h6, hlam, p12_0]
                      · have p12_0 := h12c.1
                        have p12_1 := h12c.2.1
                        have p12_2 := h12c.2.2.1
                        have p12_3 := h12c.2.2.2
                        linarith only [h8, hlam, p12_0]
                      · have p12_0 := h12c.1
                        have p12_1 := h12c.2.1
                        have p12_2 := h12c.2.2.1
                        have p12_3 := h12c.2.2.2
                        linarith only [hlam, p12_0]
                      · have p12_0 := h12c.1
                        have p12_1 := h12c.2.1
                        have p12_2 := h12c.2.2.1
                        have p12_3 := h12c.2.2.2
                        linarith only [h10, hlam, p12_1]
                      · have p12_0 := h12c.1
                        have p12_1 := h12c.2.1
                        have p12_2 := h12c.2.2.1
                        have p12_3 := h12c.2.2.2
                        linarith only [h4, hlam, p12_0]
                      · have p12_0 := h12c.1
                        have p12_1 := h12c.2.1
                        have p12_2 := h12c.2.2.1
                        have p12_3 := h12c.2.2.2
                        linarith only [h7, hlam, p12_0]
                      · have p12_0 := h12c.1
                        have p12_1 := h12c.2.1
                        have p12_2 := h12c.2.2.1
                        have p12_3 := h12c.2.2.2
                        linarith only [h9, hlam, p12_0]
                      · have p12_0 := h12c.1
                        have p12_1 := h12c.2.1
                        have p12_2 := h12c.2.2.1
                        have p12_3 := h12c.2.2.2
                        linarith only [h2, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p12_1, u2elo0]
                      · have p12_0 := h12c.1
                        have p12_1 := h12c.2.1
                        have p12_2 := h12c.2.2.1
                        have p12_3 := h12c.2.2.2
                        linarith only [hlam, p12_0]
                  · linarith only [h1, h2, h7, h8, h9, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h39 | h39
                  · linarith only [h2, h3, h39, h8, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h41 | h41
                    · rcases h3bigk with h42c | h42c | h42c | h42c | h42c | h42c | h42c | h42c | h42c | h42c | h42c | h42c | h42c | h42c | h42c | h42c | h42c | h42c | h42c | h42c | h42c | h42c | h42c | h42c | h42c
                      · have p42_0 := h42c.1
                        have p42_1 := h42c.2.1
                        have p42_2 := h42c.2.2.1
                        have p42_3 := h42c.2.2.2
                        linarith only [hlam, p42_0]
                      · have p42_0 := h42c.1
                        have p42_1 := h42c.2.1
                        have p42_2 := h42c.2.2.1
                        have p42_3 := h42c.2.2.2
                        linarith only [h2, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p42_1, u2elo0]
                      · have p42_0 := h42c.1
                        have p42_1 := h42c.2.1
                        have p42_2 := h42c.2.2.1
                        have p42_3 := h42c.2.2.2
                        linarith only [h2, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p42_1, u2elo0]
                      · have p42_0 := h42c.1
                        have p42_1 := h42c.2.1
                        have p42_2 := h42c.2.2.1
                        have p42_3 := h42c.2.2.2
                        linarith only [h2, h39, h41, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p42_1, u2elo0]
                      · have p42_0 := h42c.1
                        have p42_1 := h42c.2.1
                        have p42_2 := h42c.2.2.1
                        have p42_3 := h42c.2.2.2
                        linarith only [h2, h39, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p42_1, u2elo0]
                      · have p42_0 := h42c.1
                        have p42_1 := h42c.2.1
                        have p42_2 := h42c.2.2.1
                        have p42_3 := h42c.2.2.2
                        linarith only [h1, hlam, p42_0]
                      · have p42_0 := h42c.1
                        have p42_1 := h42c.2.1
                        have p42_2 := h42c.2.2.1
                        have p42_3 := h42c.2.2.2
                        linarith only [hlam, p42_0]
                      · have p42_0 := h42c.1
                        have p42_1 := h42c.2.1
                        have p42_2 := h42c.2.2.1
                        have p42_3 := h42c.2.2.2
                        linarith only [h1, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p42_1]
                      · have p42_0 := h42c.1
                        have p42_1 := h42c.2.1
                        have p42_2 := h42c.2.2.1
                        have p42_3 := h42c.2.2.2
                        linarith only [h1, h2, h39, h41, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p42_1, u2elo0]
                      · have p42_0 := h42c.1
                        have p42_1 := h42c.2.1
                        have p42_2 := h42c.2.2.1
                        have p42_3 := h42c.2.2.2
                        linarith only [h1, h2, h39, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p42_1, u2elo0]
                      · have p42_0 := h42c.1
                        have p42_1 := h42c.2.1
                        have p42_2 := h42c.2.2.1
                        have p42_3 := h42c.2.2.2
                        linarith only [h2, hlam, p42_0]
                      · have p42_0 := h42c.1
                        have p42_1 := h42c.2.1
                        have p42_2 := h42c.2.2.1
                        have p42_3 := h42c.2.2.2
                        linarith only [h5, hlam, p42_0]
                      · have p42_0 := h42c.1
                        have p42_1 := h42c.2.1
                        have p42_2 := h42c.2.2.1
                        have p42_3 := h42c.2.2.2
                        linarith only [hlam, p42_0]
                      · have p42_0 := h42c.1
                        have p42_1 := h42c.2.1
                        have p42_2 := h42c.2.2.1
                        have p42_3 := h42c.2.2.2
                        linarith only [h8, hlam, p42_0]
                      · have p42_0 := h42c.1
                        have p42_1 := h42c.2.1
                        have p42_2 := h42c.2.2.1
                        have p42_3 := h42c.2.2.2
                        linarith only [h39, hlam, p42_0]
                      · have p42_0 := h42c.1
                        have p42_1 := h42c.2.1
                        have p42_2 := h42c.2.2.1
                        have p42_3 := h42c.2.2.2
                        linarith only [h3, hlam, p42_0]
                      · have p42_0 := h42c.1
                        have p42_1 := h42c.2.1
                        have p42_2 := h42c.2.2.1
                        have p42_3 := h42c.2.2.2
                        linarith only [h6, hlam, p42_0]
                      · have p42_0 := h42c.1
                        have p42_1 := h42c.2.1
                        have p42_2 := h42c.2.2.1
                        have p42_3 := h42c.2.2.2
                        linarith only [hc23, hc34, hlam, hphi, p42_1]
                      · have p42_0 := h42c.1
                        have p42_1 := h42c.2.1
                        have p42_2 := h42c.2.2.1
                        have p42_3 := h42c.2.2.2
                        linarith only [hlam, p42_0]
                      · have p42_0 := h42c.1
                        have p42_1 := h42c.2.1
                        have p42_2 := h42c.2.2.1
                        have p42_3 := h42c.2.2.2
                        linarith only [h1, h2, h39, h6, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p42_1, u2elo0]
                      · have p42_0 := h42c.1
                        have p42_1 := h42c.2.1
                        have p42_2 := h42c.2.2.1
                        have p42_3 := h42c.2.2.2
                        linarith only [h4, hlam, p42_0]
                      · have p42_0 := h42c.1
                        have p42_1 := h42c.2.1
                        have p42_2 := h42c.2.2.1
                        have p42_3 := h42c.2.2.2
                        linarith only [h7, hlam, p42_0]
                      · have p42_0 := h42c.1
                        have p42_1 := h42c.2.1
                        have p42_2 := h42c.2.2.1
                        have p42_3 := h42c.2.2.2
                        linarith only [hc23, hc35, hlam, hphi, p42_1]
                      · have p42_0 := h42c.1
                        have p42_1 := h42c.2.1
                        have p42_2 := h42c.2.2.1
                        have p42_3 := h42c.2.2.2
                        linarith only [h41, hlam, p42_0]
                      · have p42_0 := h42c.1
                        have p42_1 := h42c.2.1
                        have p42_2 := h42c.2.2.1
                        have p42_3 := h42c.2.2.2
                        linarith only [hlam, p42_0]
                    · rcases h3bigk with h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c
                      · have p68_0 := h68c.1
                        have p68_1 := h68c.2.1
                        have p68_2 := h68c.2.2.1
                        have p68_3 := h68c.2.2.2
                        linarith only [hlam, p68_0]
                      · have p68_0 := h68c.1
                        have p68_1 := h68c.2.1
                        have p68_2 := h68c.2.2.1
                        have p68_3 := h68c.2.2.2
                        linarith only [h2, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p68_1, u2elo0]
                      · have p68_0 := h68c.1
                        have p68_1 := h68c.2.1
                        have p68_2 := h68c.2.2.1
                        have p68_3 := h68c.2.2.2
                        linarith only [h2, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p68_1, u2elo0]
                      · have p68_0 := h68c.1
                        have p68_1 := h68c.2.1
                        have p68_2 := h68c.2.2.1
                        have p68_3 := h68c.2.2.2
                        linarith only [h2, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p68_1, u2elo0]
                      · have p68_0 := h68c.1
                        have p68_1 := h68c.2.1
                        have p68_2 := h68c.2.2.1
                        have p68_3 := h68c.2.2.2
                        linarith only [h2, h41, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p68_1, u2elo0]
                      · have p68_0 := h68c.1
                        have p68_1 := h68c.2.1
                        have p68_2 := h68c.2.2.1
                        have p68_3 := h68c.2.2.2
                        linarith only [h1, hlam, p68_0]
                      · have p68_0 := h68c.1
                        have p68_1 := h68c.2.1
                        have p68_2 := h68c.2.2.1
                        have p68_3 := h68c.2.2.2
                        linarith only [hlam, p68_0]
                      · have p68_0 := h68c.1
                        have p68_1 := h68c.2.1
                        have p68_2 := h68c.2.2.1
                        have p68_3 := h68c.2.2.2
                        linarith only [h1, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p68_1]
                      · have p68_0 := h68c.1
                        have p68_1 := h68c.2.1
                        have p68_2 := h68c.2.2.1
                        have p68_3 := h68c.2.2.2
                        linarith only [h1, h2, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p68_1, u2elo0]
                      · have p68_0 := h68c.1
                        have p68_1 := h68c.2.1
                        have p68_2 := h68c.2.2.1
                        have p68_3 := h68c.2.2.2
                        linarith only [h1, h2, h41, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p68_1, u2elo0]
                      · have p68_0 := h68c.1
                        have p68_1 := h68c.2.1
                        have p68_2 := h68c.2.2.1
                        have p68_3 := h68c.2.2.2
                        linarith only [h2, hlam, p68_0]
                      · have p68_0 := h68c.1
                        have p68_1 := h68c.2.1
                        have p68_2 := h68c.2.2.1
                        have p68_3 := h68c.2.2.2
                        linarith only [h5, hlam, p68_0]
                      · have p68_0 := h68c.1
                        have p68_1 := h68c.2.1
                        have p68_2 := h68c.2.2.1
                        have p68_3 := h68c.2.2.2
                        linarith only [hlam, p68_0]
                      · have p68_0 := h68c.1
                        have p68_1 := h68c.2.1
                        have p68_2 := h68c.2.2.1
                        have p68_3 := h68c.2.2.2
                        linarith only [h8, hlam, p68_0]
                      · have p68_0 := h68c.1
                        have p68_1 := h68c.2.1
                        have p68_2 := h68c.2.2.1
                        have p68_3 := h68c.2.2.2
                        linarith only [h39, hlam, p68_0]
                      · have p68_0 := h68c.1
                        have p68_1 := h68c.2.1
                        have p68_2 := h68c.2.2.1
                        have p68_3 := h68c.2.2.2
                        linarith only [h3, hlam, p68_0]
                      · have p68_0 := h68c.1
                        have p68_1 := h68c.2.1
                        have p68_2 := h68c.2.2.1
                        have p68_3 := h68c.2.2.2
                        linarith only [h6, hlam, p68_0]
                      · have p68_0 := h68c.1
                        have p68_1 := h68c.2.1
                        have p68_2 := h68c.2.2.1
                        have p68_3 := h68c.2.2.2
                        linarith only [hc23, hc34, hlam, hphi, p68_1]
                      · have p68_0 := h68c.1
                        have p68_1 := h68c.2.1
                        have p68_2 := h68c.2.2.1
                        have p68_3 := h68c.2.2.2
                        linarith only [hlam, p68_0]
                      · have p68_0 := h68c.1
                        have p68_1 := h68c.2.1
                        have p68_2 := h68c.2.2.1
                        have p68_3 := h68c.2.2.2
                        linarith only [h41, hlam, p68_1]
                      · have p68_0 := h68c.1
                        have p68_1 := h68c.2.1
                        have p68_2 := h68c.2.2.1
                        have p68_3 := h68c.2.2.2
                        linarith only [h4, hlam, p68_0]
                      · have p68_0 := h68c.1
                        have p68_1 := h68c.2.1
                        have p68_2 := h68c.2.2.1
                        have p68_3 := h68c.2.2.2
                        linarith only [h7, hlam, p68_0]
                      · have p68_0 := h68c.1
                        have p68_1 := h68c.2.1
                        have p68_2 := h68c.2.2.1
                        have p68_3 := h68c.2.2.2
                        linarith only [h1, h2, h7, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p68_1, u2elo0]
                      · have p68_0 := h68c.1
                        have p68_1 := h68c.2.1
                        have p68_2 := h68c.2.2.1
                        have p68_3 := h68c.2.2.2
                        linarith only [h1, h2, h7, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p68_1, u2elo0]
                      · have p68_0 := h68c.1
                        have p68_1 := h68c.2.1
                        have p68_2 := h68c.2.2.1
                        have p68_3 := h68c.2.2.2
                        linarith only [hlam, p68_0]
              · linarith only [h2, h4, h6, h7, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h95 | h95
              · linarith only [h2, h3, h6, h95, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h97 | h97
                · linarith only [h2, h6, h97, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h99 | h99
                  · linarith only [h5, h95, h99, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h101 | h101
                    · rcases h3bigk with h102c | h102c | h102c | h102c | h102c | h102c | h102c | h102c | h102c | h102c | h102c | h102c | h102c | h102c | h102c | h102c | h102c | h102c | h102c | h102c | h102c | h102c | h102c | h102c | h102c
                      · have p102_0 := h102c.1
                        have p102_1 := h102c.2.1
                        have p102_2 := h102c.2.2.1
                        have p102_3 := h102c.2.2.2
                        linarith only [hlam, p102_0]
                      · have p102_0 := h102c.1
                        have p102_1 := h102c.2.1
                        have p102_2 := h102c.2.2.1
                        have p102_3 := h102c.2.2.2
                        linarith only [h2, h5, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p102_1, u2elo0]
                      · have p102_0 := h102c.1
                        have p102_1 := h102c.2.1
                        have p102_2 := h102c.2.2.1
                        have p102_3 := h102c.2.2.2
                        linarith only [h2, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p102_1, u2elo0]
                      · have p102_0 := h102c.1
                        have p102_1 := h102c.2.1
                        have p102_2 := h102c.2.2.1
                        have p102_3 := h102c.2.2.2
                        linarith only [h101, h2, h5, h95, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p102_1, u2elo0]
                      · have p102_0 := h102c.1
                        have p102_1 := h102c.2.1
                        have p102_2 := h102c.2.2.1
                        have p102_3 := h102c.2.2.2
                        linarith only [h2, h5, h95, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p102_1, u2elo0]
                      · have p102_0 := h102c.1
                        have p102_1 := h102c.2.1
                        have p102_2 := h102c.2.2.1
                        have p102_3 := h102c.2.2.2
                        linarith only [h1, hlam, p102_0]
                      · have p102_0 := h102c.1
                        have p102_1 := h102c.2.1
                        have p102_2 := h102c.2.2.1
                        have p102_3 := h102c.2.2.2
                        linarith only [hlam, p102_0]
                      · have p102_0 := h102c.1
                        have p102_1 := h102c.2.1
                        have p102_2 := h102c.2.2.1
                        have p102_3 := h102c.2.2.2
                        linarith only [h101, h95, hc23, hc34, hlam, hphi, p102_1]
                      · have p102_0 := h102c.1
                        have p102_1 := h102c.2.1
                        have p102_2 := h102c.2.2.1
                        have p102_3 := h102c.2.2.2
                        linarith only [h6, hlam, p102_0]
                      · have p102_0 := h102c.1
                        have p102_1 := h102c.2.1
                        have p102_2 := h102c.2.2.1
                        have p102_3 := h102c.2.2.2
                        linarith only [h95, hlam, p102_0]
                      · have p102_0 := h102c.1
                        have p102_1 := h102c.2.1
                        have p102_2 := h102c.2.2.1
                        have p102_3 := h102c.2.2.2
                        linarith only [h2, hlam, p102_0]
                      · have p102_0 := h102c.1
                        have p102_1 := h102c.2.1
                        have p102_2 := h102c.2.2.1
                        have p102_3 := h102c.2.2.2
                        linarith only [h5, hlam, p102_0]
                      · have p102_0 := h102c.1
                        have p102_1 := h102c.2.1
                        have p102_2 := h102c.2.2.1
                        have p102_3 := h102c.2.2.2
                        linarith only [hlam, p102_0]
                      · have p102_0 := h102c.1
                        have p102_1 := h102c.2.1
                        have p102_2 := h102c.2.2.1
                        have p102_3 := h102c.2.2.2
                        linarith only [h97, hlam, p102_0]
                      · have p102_0 := h102c.1
                        have p102_1 := h102c.2.1
                        have p102_2 := h102c.2.2.1
                        have p102_3 := h102c.2.2.2
                        linarith only [h99, hlam, p102_0]
                      · have p102_0 := h102c.1
                        have p102_1 := h102c.2.1
                        have p102_2 := h102c.2.2.1
                        have p102_3 := h102c.2.2.2
                        linarith only [h3, hlam, p102_0]
                      · have p102_0 := h102c.1
                        have p102_1 := h102c.2.1
                        have p102_2 := h102c.2.2.1
                        have p102_3 := h102c.2.2.2
                        linarith only [h2, h3, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p102_1, u2elo0]
                      · have p102_0 := h102c.1
                        have p102_1 := h102c.2.1
                        have p102_2 := h102c.2.2.1
                        have p102_3 := h102c.2.2.2
                        linarith only [h2, h3, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p102_1, u2elo0]
                      · have p102_0 := h102c.1
                        have p102_1 := h102c.2.1
                        have p102_2 := h102c.2.2.1
                        have p102_3 := h102c.2.2.2
                        linarith only [hlam, p102_0]
                      · have p102_0 := h102c.1
                        have p102_1 := h102c.2.1
                        have p102_2 := h102c.2.2.1
                        have p102_3 := h102c.2.2.2
                        linarith only [h2, h3, h95, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p102_1, u2elo0]
                      · have p102_0 := h102c.1
                        have p102_1 := h102c.2.1
                        have p102_2 := h102c.2.2.1
                        have p102_3 := h102c.2.2.2
                        linarith only [h4, hlam, p102_0]
                      · have p102_0 := h102c.1
                        have p102_1 := h102c.2.1
                        have p102_2 := h102c.2.2.1
                        have p102_3 := h102c.2.2.2
                        linarith only [h5, hc23, hc35, hlam, hphi, p102_1]
                      · have p102_0 := h102c.1
                        have p102_1 := h102c.2.1
                        have p102_2 := h102c.2.2.1
                        have p102_3 := h102c.2.2.2
                        linarith only [h2, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p102_1, u2elo0]
                      · have p102_0 := h102c.1
                        have p102_1 := h102c.2.1
                        have p102_2 := h102c.2.2.1
                        have p102_3 := h102c.2.2.2
                        linarith only [h101, hlam, p102_0]
                      · have p102_0 := h102c.1
                        have p102_1 := h102c.2.1
                        have p102_2 := h102c.2.2.1
                        have p102_3 := h102c.2.2.2
                        linarith only [hlam, p102_0]
                    · rcases h3bigk with h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c
                      · have p128_0 := h128c.1
                        have p128_1 := h128c.2.1
                        have p128_2 := h128c.2.2.1
                        have p128_3 := h128c.2.2.2
                        linarith only [hlam, p128_0]
                      · have p128_0 := h128c.1
                        have p128_1 := h128c.2.1
                        have p128_2 := h128c.2.2.1
                        have p128_3 := h128c.2.2.2
                        linarith only [h2, h5, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p128_1, u2elo0]
                      · have p128_0 := h128c.1
                        have p128_1 := h128c.2.1
                        have p128_2 := h128c.2.2.1
                        have p128_3 := h128c.2.2.2
                        linarith only [h2, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p128_1, u2elo0]
                      · have p128_0 := h128c.1
                        have p128_1 := h128c.2.1
                        have p128_2 := h128c.2.2.1
                        have p128_3 := h128c.2.2.2
                        linarith only [h2, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p128_1, u2elo0]
                      · have p128_0 := h128c.1
                        have p128_1 := h128c.2.1
                        have p128_2 := h128c.2.2.1
                        have p128_3 := h128c.2.2.2
                        linarith only [h2, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p128_1, u2elo0]
                      · have p128_0 := h128c.1
                        have p128_1 := h128c.2.1
                        have p128_2 := h128c.2.2.1
                        have p128_3 := h128c.2.2.2
                        linarith only [h1, hlam, p128_0]
                      · have p128_0 := h128c.1
                        have p128_1 := h128c.2.1
                        have p128_2 := h128c.2.2.1
                        have p128_3 := h128c.2.2.2
                        linarith only [hlam, p128_0]
                      · have p128_0 := h128c.1
                        have p128_1 := h128c.2.1
                        have p128_2 := h128c.2.2.1
                        have p128_3 := h128c.2.2.2
                        linarith only [h1, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p128_1]
                      · have p128_0 := h128c.1
                        have p128_1 := h128c.2.1
                        have p128_2 := h128c.2.2.1
                        have p128_3 := h128c.2.2.2
                        linarith only [h6, hlam, p128_0]
                      · have p128_0 := h128c.1
                        have p128_1 := h128c.2.1
                        have p128_2 := h128c.2.2.1
                        have p128_3 := h128c.2.2.2
                        linarith only [h95, hlam, p128_0]
                      · have p128_0 := h128c.1
                        have p128_1 := h128c.2.1
                        have p128_2 := h128c.2.2.1
                        have p128_3 := h128c.2.2.2
                        linarith only [h2, hlam, p128_0]
                      · have p128_0 := h128c.1
                        have p128_1 := h128c.2.1
                        have p128_2 := h128c.2.2.1
                        have p128_3 := h128c.2.2.2
                        linarith only [h5, hlam, p128_0]
                      · have p128_0 := h128c.1
                        have p128_1 := h128c.2.1
                        have p128_2 := h128c.2.2.1
                        have p128_3 := h128c.2.2.2
                        linarith only [hlam, p128_0]
                      · have p128_0 := h128c.1
                        have p128_1 := h128c.2.1
                        have p128_2 := h128c.2.2.1
                        have p128_3 := h128c.2.2.2
                        linarith only [h97, hlam, p128_0]
                      · have p128_0 := h128c.1
                        have p128_1 := h128c.2.1
                        have p128_2 := h128c.2.2.1
                        have p128_3 := h128c.2.2.2
                        linarith only [h99, hlam, p128_0]
                      · have p128_0 := h128c.1
                        have p128_1 := h128c.2.1
                        have p128_2 := h128c.2.2.1
                        have p128_3 := h128c.2.2.2
                        linarith only [h3, hlam, p128_0]
                      · have p128_0 := h128c.1
                        have p128_1 := h128c.2.1
                        have p128_2 := h128c.2.2.1
                        have p128_3 := h128c.2.2.2
                        linarith only [hc13, hc34, hlam, hphi, p128_1]
                      · have p128_0 := h128c.1
                        have p128_1 := h128c.2.1
                        have p128_2 := h128c.2.2.1
                        have p128_3 := h128c.2.2.2
                        linarith only [h2, h3, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p128_1, u2elo0]
                      · have p128_0 := h128c.1
                        have p128_1 := h128c.2.1
                        have p128_2 := h128c.2.2.1
                        have p128_3 := h128c.2.2.2
                        linarith only [hlam, p128_0]
                      · have p128_0 := h128c.1
                        have p128_1 := h128c.2.1
                        have p128_2 := h128c.2.2.1
                        have p128_3 := h128c.2.2.2
                        linarith only [h101, hlam, p128_1]
                      · have p128_0 := h128c.1
                        have p128_1 := h128c.2.1
                        have p128_2 := h128c.2.2.1
                        have p128_3 := h128c.2.2.2
                        linarith only [h4, hlam, p128_0]
                      · have p128_0 := h128c.1
                        have p128_1 := h128c.2.1
                        have p128_2 := h128c.2.2.1
                        have p128_3 := h128c.2.2.2
                        linarith only [hc13, hc35, hlam, hphi, p128_1]
                      · have p128_0 := h128c.1
                        have p128_1 := h128c.2.1
                        have p128_2 := h128c.2.2.1
                        have p128_3 := h128c.2.2.2
                        linarith only [h2, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p128_1, u2elo0]
                      · have p128_0 := h128c.1
                        have p128_1 := h128c.2.1
                        have p128_2 := h128c.2.2.1
                        have p128_3 := h128c.2.2.2
                        linarith only [h2, h4, h6, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p128_1, u2elo0]
                      · have p128_0 := h128c.1
                        have p128_1 := h128c.2.1
                        have p128_2 := h128c.2.2.1
                        have p128_3 := h128c.2.2.2
                        linarith only [hlam, p128_0]
          · linarith only [h2, h5, hc12, hlam, hphi, u2elo0]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h155 | h155
          · rcases m.htr 1 3 4 (by decide) (by decide) with h156 | h156
            · rcases m.htr 1 3 5 (by decide) (by decide) with h157 | h157
              · linarith only [h1, h157, h4, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h159 | h159
                · rcases m.htr 2 3 5 (by decide) (by decide) with h160 | h160
                  · linarith only [h1, h155, h160, h4, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h162 | h162
                    · linarith only [h0, h155, h159, h162, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0]
                    · rcases h3bigk with h164c | h164c | h164c | h164c | h164c | h164c | h164c | h164c | h164c | h164c | h164c | h164c | h164c | h164c | h164c | h164c | h164c | h164c | h164c | h164c | h164c | h164c | h164c | h164c | h164c
                      · have p164_0 := h164c.1
                        have p164_1 := h164c.2.1
                        have p164_2 := h164c.2.2.1
                        have p164_3 := h164c.2.2.2
                        linarith only [hlam, p164_0]
                      · have p164_0 := h164c.1
                        have p164_1 := h164c.2.1
                        have p164_2 := h164c.2.2.1
                        have p164_3 := h164c.2.2.2
                        linarith only [h155, h159, h4, hc05, hc34, hlam, hphi, ht0b, ht45, ht5b, p164_1]
                      · have p164_0 := h164c.1
                        have p164_1 := h164c.2.1
                        have p164_2 := h164c.2.2.1
                        have p164_3 := h164c.2.2.2
                        linarith only [h159, h162, h4, hc34, hc45, hlam, hphi, p164_1]
                      · have p164_0 := h164c.1
                        have p164_1 := h164c.2.1
                        have p164_2 := h164c.2.2.1
                        have p164_3 := h164c.2.2.2
                        linarith only [h162, h4, hc34, hc45, hlam, hphi, p164_1]
                      · have p164_0 := h164c.1
                        have p164_1 := h164c.2.1
                        have p164_2 := h164c.2.2.1
                        have p164_3 := h164c.2.2.2
                        linarith only [h4, hlam, p164_0]
                      · have p164_0 := h164c.1
                        have p164_1 := h164c.2.1
                        have p164_2 := h164c.2.2.1
                        have p164_3 := h164c.2.2.2
                        linarith only [h1, hlam, p164_0]
                      · have p164_0 := h164c.1
                        have p164_1 := h164c.2.1
                        have p164_2 := h164c.2.2.1
                        have p164_3 := h164c.2.2.2
                        linarith only [hlam, p164_0]
                      · have p164_0 := h164c.1
                        have p164_1 := h164c.2.1
                        have p164_2 := h164c.2.2.1
                        have p164_3 := h164c.2.2.2
                        linarith only [h159, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p164_1]
                      · have p164_0 := h164c.1
                        have p164_1 := h164c.2.1
                        have p164_2 := h164c.2.2.1
                        have p164_3 := h164c.2.2.2
                        linarith only [h1, h162, h4, hc34, hc45, hlam, hphi, p164_1]
                      · have p164_0 := h164c.1
                        have p164_1 := h164c.2.1
                        have p164_2 := h164c.2.2.1
                        have p164_3 := h164c.2.2.2
                        linarith only [h157, hlam, p164_0]
                      · have p164_0 := h164c.1
                        have p164_1 := h164c.2.1
                        have p164_2 := h164c.2.2.1
                        have p164_3 := h164c.2.2.2
                        linarith only [h2, hlam, p164_0]
                      · have p164_0 := h164c.1
                        have p164_1 := h164c.2.1
                        have p164_2 := h164c.2.2.1
                        have p164_3 := h164c.2.2.2
                        linarith only [h155, hlam, p164_0]
                      · have p164_0 := h164c.1
                        have p164_1 := h164c.2.1
                        have p164_2 := h164c.2.2.1
                        have p164_3 := h164c.2.2.2
                        linarith only [hlam, p164_0]
                      · have p164_0 := h164c.1
                        have p164_1 := h164c.2.1
                        have p164_2 := h164c.2.2.1
                        have p164_3 := h164c.2.2.2
                        linarith only [h0, h155, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p164_1]
                      · have p164_0 := h164c.1
                        have p164_1 := h164c.2.1
                        have p164_2 := h164c.2.2.1
                        have p164_3 := h164c.2.2.2
                        linarith only [h160, hlam, p164_0]
                      · have p164_0 := h164c.1
                        have p164_1 := h164c.2.1
                        have p164_2 := h164c.2.2.1
                        have p164_3 := h164c.2.2.2
                        linarith only [h3, hlam, p164_0]
                      · have p164_0 := h164c.1
                        have p164_1 := h164c.2.1
                        have p164_2 := h164c.2.2.1
                        have p164_3 := h164c.2.2.2
                        linarith only [h156, hlam, p164_0]
                      · have p164_0 := h164c.1
                        have p164_1 := h164c.2.1
                        have p164_2 := h164c.2.2.1
                        have p164_3 := h164c.2.2.2
                        linarith only [h159, hlam, p164_0]
                      · have p164_0 := h164c.1
                        have p164_1 := h164c.2.1
                        have p164_2 := h164c.2.2.1
                        have p164_3 := h164c.2.2.2
                        linarith only [hlam, p164_0]
                      · have p164_0 := h164c.1
                        have p164_1 := h164c.2.1
                        have p164_2 := h164c.2.2.1
                        have p164_3 := h164c.2.2.2
                        linarith only [h162, hlam, p164_1]
                      · have p164_0 := h164c.1
                        have p164_1 := h164c.2.1
                        have p164_2 := h164c.2.2.1
                        have p164_3 := h164c.2.2.2
                        linarith only [h162, hc03, hc45, hlam, hphi, ht34, p164_1]
                      · have p164_0 := h164c.1
                        have p164_1 := h164c.2.1
                        have p164_2 := h164c.2.2.1
                        have p164_3 := h164c.2.2.2
                        linarith only [h156, h162, hc34, hc45, hlam, hphi, p164_1]
                      · have p164_0 := h164c.1
                        have p164_1 := h164c.2.1
                        have p164_2 := h164c.2.2.1
                        have p164_3 := h164c.2.2.2
                        linarith only [h159, h162, hc34, hc45, hlam, hphi, p164_1]
                      · have p164_0 := h164c.1
                        have p164_1 := h164c.2.1
                        have p164_2 := h164c.2.2.1
                        have p164_3 := h164c.2.2.2
                        linarith only [h162, hc34, hc45, hlam, hphi, p164_1]
                      · have p164_0 := h164c.1
                        have p164_1 := h164c.2.1
                        have p164_2 := h164c.2.2.1
                        have p164_3 := h164c.2.2.2
                        linarith only [hlam, p164_0]
                · linarith only [h159, h3, h4, hc23, hc35, hlam, hphi]
            · linarith only [h156, h3, h4, hc13, hc35, hlam, hphi]
          · linarith only [h155, h2, hc12, hlam, hphi, u2elo0]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h193 | h193
        · rcases m.htr 1 2 3 (by decide) (by decide) with h194 | h194
          · rcases m.htr 1 3 4 (by decide) (by decide) with h195 | h195
            · linarith only [h1, h193, h195, h3, hc01, hc35, hlam, hphi, ht0b, ht5b]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h197 | h197
              · rcases m.htr 2 3 4 (by decide) (by decide) with h198 | h198
                · linarith only [h1, h194, h197, h198, h3, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h200 | h200
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h201 | h201
                    · rcases h3bigk with h202c | h202c | h202c | h202c | h202c | h202c | h202c | h202c | h202c | h202c | h202c | h202c | h202c | h202c | h202c | h202c | h202c | h202c | h202c | h202c | h202c | h202c | h202c | h202c | h202c
                      · have p202_0 := h202c.1
                        have p202_1 := h202c.2.1
                        have p202_2 := h202c.2.2.1
                        have p202_3 := h202c.2.2.2
                        linarith only [hlam, p202_0]
                      · have p202_0 := h202c.1
                        have p202_1 := h202c.2.1
                        have p202_2 := h202c.2.2.1
                        have p202_3 := h202c.2.2.2
                        linarith only [h194, h200, h201, hc03, hc45, hlam, hphi, ht0b, ht5b, p202_1]
                      · have p202_0 := h202c.1
                        have p202_1 := h202c.2.1
                        have p202_2 := h202c.2.2.1
                        have p202_3 := h202c.2.2.2
                        linarith only [h200, h201, h3, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p202_1]
                      · have p202_0 := h202c.1
                        have p202_1 := h202c.2.1
                        have p202_2 := h202c.2.2.1
                        have p202_3 := h202c.2.2.2
                        linarith only [h3, hlam, p202_0]
                      · have p202_0 := h202c.1
                        have p202_1 := h202c.2.1
                        have p202_2 := h202c.2.2.1
                        have p202_3 := h202c.2.2.2
                        linarith only [h201, h3, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p202_1]
                      · have p202_0 := h202c.1
                        have p202_1 := h202c.2.1
                        have p202_2 := h202c.2.2.1
                        have p202_3 := h202c.2.2.2
                        linarith only [h1, hlam, p202_0]
                      · have p202_0 := h202c.1
                        have p202_1 := h202c.2.1
                        have p202_2 := h202c.2.2.1
                        have p202_3 := h202c.2.2.2
                        linarith only [hlam, p202_0]
                      · have p202_0 := h202c.1
                        have p202_1 := h202c.2.1
                        have p202_2 := h202c.2.2.1
                        have p202_3 := h202c.2.2.2
                        linarith only [h200, h201, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p202_1]
                      · have p202_0 := h202c.1
                        have p202_1 := h202c.2.1
                        have p202_2 := h202c.2.2.1
                        have p202_3 := h202c.2.2.2
                        linarith only [h195, hlam, p202_0]
                      · have p202_0 := h202c.1
                        have p202_1 := h202c.2.1
                        have p202_2 := h202c.2.2.1
                        have p202_3 := h202c.2.2.2
                        linarith only [h1, h201, h3, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p202_1]
                      · have p202_0 := h202c.1
                        have p202_1 := h202c.2.1
                        have p202_2 := h202c.2.2.1
                        have p202_3 := h202c.2.2.2
                        linarith only [h2, hlam, p202_0]
                      · have p202_0 := h202c.1
                        have p202_1 := h202c.2.1
                        have p202_2 := h202c.2.2.1
                        have p202_3 := h202c.2.2.2
                        linarith only [h194, hlam, p202_0]
                      · have p202_0 := h202c.1
                        have p202_1 := h202c.2.1
                        have p202_2 := h202c.2.2.1
                        have p202_3 := h202c.2.2.2
                        linarith only [hlam, p202_0]
                      · have p202_0 := h202c.1
                        have p202_1 := h202c.2.1
                        have p202_2 := h202c.2.2.1
                        have p202_3 := h202c.2.2.2
                        linarith only [h198, hlam, p202_0]
                      · have p202_0 := h202c.1
                        have p202_1 := h202c.2.1
                        have p202_2 := h202c.2.2.1
                        have p202_3 := h202c.2.2.2
                        linarith only [h201, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p202_1, u2elo2]
                      · have p202_0 := h202c.1
                        have p202_1 := h202c.2.1
                        have p202_2 := h202c.2.2.1
                        have p202_3 := h202c.2.2.2
                        linarith only [hc03, hc34, hlam, hphi, p202_1]
                      · have p202_0 := h202c.1
                        have p202_1 := h202c.2.1
                        have p202_2 := h202c.2.2.1
                        have p202_3 := h202c.2.2.2
                        linarith only [hc13, hc34, hlam, hphi, p202_1]
                      · have p202_0 := h202c.1
                        have p202_1 := h202c.2.1
                        have p202_2 := h202c.2.2.1
                        have p202_3 := h202c.2.2.2
                        linarith only [hc23, hc34, hlam, hphi, p202_1]
                      · have p202_0 := h202c.1
                        have p202_1 := h202c.2.1
                        have p202_2 := h202c.2.2.1
                        have p202_3 := h202c.2.2.2
                        linarith only [hlam, p202_0]
                      · have p202_0 := h202c.1
                        have p202_1 := h202c.2.1
                        have p202_2 := h202c.2.2.1
                        have p202_3 := h202c.2.2.2
                        rcases p202_3 (m.d 0 3) (by simp) with h222 | h222
                        · linarith only [h222, h3, hlam]
                        · linarith only [h193, h222, hlam]
                      · have p202_0 := h202c.1
                        have p202_1 := h202c.2.1
                        have p202_2 := h202c.2.2.1
                        have p202_3 := h202c.2.2.2
                        linarith only [h193, hlam, p202_0]
                      · have p202_0 := h202c.1
                        have p202_1 := h202c.2.1
                        have p202_2 := h202c.2.2.1
                        have p202_3 := h202c.2.2.2
                        linarith only [h197, hlam, p202_0]
                      · have p202_0 := h202c.1
                        have p202_1 := h202c.2.1
                        have p202_2 := h202c.2.2.1
                        have p202_3 := h202c.2.2.2
                        linarith only [h200, hlam, p202_0]
                      · have p202_0 := h202c.1
                        have p202_1 := h202c.2.1
                        have p202_2 := h202c.2.2.1
                        have p202_3 := h202c.2.2.2
                        linarith only [h201, hlam, p202_0]
                      · have p202_0 := h202c.1
                        have p202_1 := h202c.2.1
                        have p202_2 := h202c.2.2.1
                        have p202_3 := h202c.2.2.2
                        linarith only [hlam, p202_0]
                    · linarith only [h1, h194, h200, h201, h3, hlam]
                  · linarith only [h193, h200, h3, hc23, hc34, hlam, hphi]
              · linarith only [h193, h197, h3, hc13, hc34, hlam, hphi]
          · linarith only [h194, h2, hc12, hlam, hphi, u2elo0]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h234 | h234
          · rcases m.htr 1 3 4 (by decide) (by decide) with h235 | h235
            · linarith only [h1, h235, h3, hlam]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h237 | h237
              · linarith only [h1, h193, h237, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h239 | h239
                · linarith only [h1, h234, h239, h3, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h241 | h241
                  · linarith only [h1, h193, h234, h241, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h243 | h243
                    · rcases h3bigk with h244c | h244c | h244c | h244c | h244c | h244c | h244c | h244c | h244c | h244c | h244c | h244c | h244c | h244c | h244c | h244c | h244c | h244c | h244c | h244c | h244c | h244c | h244c | h244c | h244c
                      · have p244_0 := h244c.1
                        have p244_1 := h244c.2.1
                        have p244_2 := h244c.2.2.1
                        have p244_3 := h244c.2.2.2
                        linarith only [hlam, p244_0]
                      · have p244_0 := h244c.1
                        have p244_1 := h244c.2.1
                        have p244_2 := h244c.2.2.1
                        have p244_3 := h244c.2.2.2
                        linarith only [h193, h243, hc13, hc34, hlam, hphi, p244_1]
                      · have p244_0 := h244c.1
                        have p244_1 := h244c.2.1
                        have p244_2 := h244c.2.2.1
                        have p244_3 := h244c.2.2.2
                        linarith only [h193, h243, hc23, hc34, hlam, hphi, p244_1]
                      · have p244_0 := h244c.1
                        have p244_1 := h244c.2.1
                        have p244_2 := h244c.2.2.1
                        have p244_3 := h244c.2.2.2
                        linarith only [h3, hlam, p244_0]
                      · have p244_0 := h244c.1
                        have p244_1 := h244c.2.1
                        have p244_2 := h244c.2.2.1
                        have p244_3 := h244c.2.2.2
                        linarith only [h193, hlam, p244_0]
                      · have p244_0 := h244c.1
                        have p244_1 := h244c.2.1
                        have p244_2 := h244c.2.2.1
                        have p244_3 := h244c.2.2.2
                        linarith only [h1, hlam, p244_0]
                      · have p244_0 := h244c.1
                        have p244_1 := h244c.2.1
                        have p244_2 := h244c.2.2.1
                        have p244_3 := h244c.2.2.2
                        linarith only [hlam, p244_0]
                      · have p244_0 := h244c.1
                        have p244_1 := h244c.2.1
                        have p244_2 := h244c.2.2.1
                        have p244_3 := h244c.2.2.2
                        linarith only [h1, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p244_1]
                      · have p244_0 := h244c.1
                        have p244_1 := h244c.2.1
                        have p244_2 := h244c.2.2.1
                        have p244_3 := h244c.2.2.2
                        linarith only [h235, hlam, p244_0]
                      · have p244_0 := h244c.1
                        have p244_1 := h244c.2.1
                        have p244_2 := h244c.2.2.1
                        have p244_3 := h244c.2.2.2
                        linarith only [h237, hlam, p244_0]
                      · have p244_0 := h244c.1
                        have p244_1 := h244c.2.1
                        have p244_2 := h244c.2.2.1
                        have p244_3 := h244c.2.2.2
                        linarith only [h2, hlam, p244_0]
                      · have p244_0 := h244c.1
                        have p244_1 := h244c.2.1
                        have p244_2 := h244c.2.2.1
                        have p244_3 := h244c.2.2.2
                        linarith only [h234, hlam, p244_0]
                      · have p244_0 := h244c.1
                        have p244_1 := h244c.2.1
                        have p244_2 := h244c.2.2.1
                        have p244_3 := h244c.2.2.2
                        linarith only [hlam, p244_0]
                      · have p244_0 := h244c.1
                        have p244_1 := h244c.2.1
                        have p244_2 := h244c.2.2.1
                        have p244_3 := h244c.2.2.2
                        linarith only [h239, hlam, p244_0]
                      · have p244_0 := h244c.1
                        have p244_1 := h244c.2.1
                        have p244_2 := h244c.2.2.1
                        have p244_3 := h244c.2.2.2
                        linarith only [h241, hlam, p244_0]
                      · have p244_0 := h244c.1
                        have p244_1 := h244c.2.1
                        have p244_2 := h244c.2.2.1
                        have p244_3 := h244c.2.2.2
                        linarith only [hc03, hc34, hlam, hphi, p244_1]
                      · have p244_0 := h244c.1
                        have p244_1 := h244c.2.1
                        have p244_2 := h244c.2.2.1
                        have p244_3 := h244c.2.2.2
                        linarith only [h234, hc23, hc34, hlam, hphi, p244_1]
                      · have p244_0 := h244c.1
                        have p244_1 := h244c.2.1
                        have p244_2 := h244c.2.2.1
                        have p244_3 := h244c.2.2.2
                        linarith only [hc23, hc34, hlam, hphi, p244_1]
                      · have p244_0 := h244c.1
                        have p244_1 := h244c.2.1
                        have p244_2 := h244c.2.2.1
                        have p244_3 := h244c.2.2.2
                        linarith only [hlam, p244_0]
                      · have p244_0 := h244c.1
                        have p244_1 := h244c.2.1
                        have p244_2 := h244c.2.2.1
                        have p244_3 := h244c.2.2.2
                        linarith only [h1, h193, h234, hc23, hc34, hlam, hphi, p244_1]
                      · have p244_0 := h244c.1
                        have p244_1 := h244c.2.1
                        have p244_2 := h244c.2.2.1
                        have p244_3 := h244c.2.2.2
                        linarith only [h1, h234, hc23, hc35, hlam, hphi, p244_1]
                      · have p244_0 := h244c.1
                        have p244_1 := h244c.2.1
                        have p244_2 := h244c.2.2.1
                        have p244_3 := h244c.2.2.2
                        linarith only [h234, hc23, hc35, hlam, hphi, p244_1]
                      · have p244_0 := h244c.1
                        have p244_1 := h244c.2.1
                        have p244_2 := h244c.2.2.1
                        have p244_3 := h244c.2.2.2
                        linarith only [hc23, hc35, hlam, hphi, p244_1]
                      · have p244_0 := h244c.1
                        have p244_1 := h244c.2.1
                        have p244_2 := h244c.2.2.1
                        have p244_3 := h244c.2.2.2
                        linarith only [h243, hlam, p244_0]
                      · have p244_0 := h244c.1
                        have p244_1 := h244c.2.1
                        have p244_2 := h244c.2.2.1
                        have p244_3 := h244c.2.2.2
                        linarith only [hlam, p244_0]
                    · rcases h3bigk with h270c | h270c | h270c | h270c | h270c | h270c | h270c | h270c | h270c | h270c | h270c | h270c | h270c | h270c | h270c | h270c | h270c | h270c | h270c | h270c | h270c | h270c | h270c | h270c | h270c
                      · have p270_0 := h270c.1
                        have p270_1 := h270c.2.1
                        have p270_2 := h270c.2.2.1
                        have p270_3 := h270c.2.2.2
                        linarith only [hlam, p270_0]
                      · have p270_0 := h270c.1
                        have p270_1 := h270c.2.1
                        have p270_2 := h270c.2.2.1
                        have p270_3 := h270c.2.2.2
                        linarith only [h2, h234, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p270_1, u2elo0]
                      · have p270_0 := h270c.1
                        have p270_1 := h270c.2.1
                        have p270_2 := h270c.2.2.1
                        have p270_3 := h270c.2.2.2
                        linarith only [h2, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p270_1, u2elo0]
                      · have p270_0 := h270c.1
                        have p270_1 := h270c.2.1
                        have p270_2 := h270c.2.2.1
                        have p270_3 := h270c.2.2.2
                        linarith only [h3, hlam, p270_0]
                      · have p270_0 := h270c.1
                        have p270_1 := h270c.2.1
                        have p270_2 := h270c.2.2.1
                        have p270_3 := h270c.2.2.2
                        linarith only [h193, hlam, p270_0]
                      · have p270_0 := h270c.1
                        have p270_1 := h270c.2.1
                        have p270_2 := h270c.2.2.1
                        have p270_3 := h270c.2.2.2
                        linarith only [h1, hlam, p270_0]
                      · have p270_0 := h270c.1
                        have p270_1 := h270c.2.1
                        have p270_2 := h270c.2.2.1
                        have p270_3 := h270c.2.2.2
                        linarith only [hlam, p270_0]
                      · have p270_0 := h270c.1
                        have p270_1 := h270c.2.1
                        have p270_2 := h270c.2.2.1
                        have p270_3 := h270c.2.2.2
                        linarith only [h1, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p270_1]
                      · have p270_0 := h270c.1
                        have p270_1 := h270c.2.1
                        have p270_2 := h270c.2.2.1
                        have p270_3 := h270c.2.2.2
                        linarith only [h235, hlam, p270_0]
                      · have p270_0 := h270c.1
                        have p270_1 := h270c.2.1
                        have p270_2 := h270c.2.2.1
                        have p270_3 := h270c.2.2.2
                        linarith only [h237, hlam, p270_0]
                      · have p270_0 := h270c.1
                        have p270_1 := h270c.2.1
                        have p270_2 := h270c.2.2.1
                        have p270_3 := h270c.2.2.2
                        linarith only [h2, hlam, p270_0]
                      · have p270_0 := h270c.1
                        have p270_1 := h270c.2.1
                        have p270_2 := h270c.2.2.1
                        have p270_3 := h270c.2.2.2
                        linarith only [h234, hlam, p270_0]
                      · have p270_0 := h270c.1
                        have p270_1 := h270c.2.1
                        have p270_2 := h270c.2.2.1
                        have p270_3 := h270c.2.2.2
                        linarith only [hlam, p270_0]
                      · have p270_0 := h270c.1
                        have p270_1 := h270c.2.1
                        have p270_2 := h270c.2.2.1
                        have p270_3 := h270c.2.2.2
                        linarith only [h239, hlam, p270_0]
                      · have p270_0 := h270c.1
                        have p270_1 := h270c.2.1
                        have p270_2 := h270c.2.2.1
                        have p270_3 := h270c.2.2.2
                        linarith only [h241, hlam, p270_0]
                      · have p270_0 := h270c.1
                        have p270_1 := h270c.2.1
                        have p270_2 := h270c.2.2.1
                        have p270_3 := h270c.2.2.2
                        linarith only [h243, hc03, hc45, hlam, hphi, ht34, p270_1]
                      · have p270_0 := h270c.1
                        have p270_1 := h270c.2.1
                        have p270_2 := h270c.2.2.1
                        have p270_3 := h270c.2.2.2
                        linarith only [h234, h243, hc23, hc45, hlam, hphi, ht34, p270_1]
                      · have p270_0 := h270c.1
                        have p270_1 := h270c.2.1
                        have p270_2 := h270c.2.2.1
                        have p270_3 := h270c.2.2.2
                        linarith only [h243, hc23, hc45, hlam, hphi, ht34, p270_1]
                      · have p270_0 := h270c.1
                        have p270_1 := h270c.2.1
                        have p270_2 := h270c.2.2.1
                        have p270_3 := h270c.2.2.2
                        linarith only [hlam, p270_0]
                      · have p270_0 := h270c.1
                        have p270_1 := h270c.2.1
                        have p270_2 := h270c.2.2.1
                        have p270_3 := h270c.2.2.2
                        linarith only [h243, hlam, p270_1]
                      · have p270_0 := h270c.1
                        have p270_1 := h270c.2.1
                        have p270_2 := h270c.2.2.1
                        have p270_3 := h270c.2.2.2
                        linarith only [h1, h234, h243, hc23, hc45, hlam, hphi, ht34, p270_1]
                      · have p270_0 := h270c.1
                        have p270_1 := h270c.2.1
                        have p270_2 := h270c.2.2.1
                        have p270_3 := h270c.2.2.2
                        linarith only [h234, h243, hc23, hc45, hlam, hphi, ht34, p270_1]
                      · have p270_0 := h270c.1
                        have p270_1 := h270c.2.1
                        have p270_2 := h270c.2.2.1
                        have p270_3 := h270c.2.2.2
                        linarith only [h243, hc23, hc45, hlam, hphi, ht34, p270_1]
                      · have p270_0 := h270c.1
                        have p270_1 := h270c.2.1
                        have p270_2 := h270c.2.2.1
                        have p270_3 := h270c.2.2.2
                        linarith only [h243, h3, hc04, hc45, hlam, hphi, p270_1]
                      · have p270_0 := h270c.1
                        have p270_1 := h270c.2.1
                        have p270_2 := h270c.2.2.1
                        have p270_3 := h270c.2.2.2
                        linarith only [hlam, p270_0]
          · linarith only [h2, h234, hc12, hlam, hphi, u2elo0]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h297 | h297
      · rcases m.htr 0 3 5 (by decide) (by decide) with h298 | h298
        · rcases m.htr 1 2 3 (by decide) (by decide) with h299 | h299
          · linarith only [h0, h2, h299, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h301 | h301
            · rcases m.htr 1 3 5 (by decide) (by decide) with h302 | h302
              · rcases m.htr 2 3 4 (by decide) (by decide) with h303 | h303
                · rcases m.htr 2 3 5 (by decide) (by decide) with h304 | h304
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h305 | h305
                    · rcases h3bigk with h306c | h306c | h306c | h306c | h306c | h306c | h306c | h306c | h306c | h306c | h306c | h306c | h306c | h306c | h306c | h306c | h306c | h306c | h306c | h306c | h306c | h306c | h306c | h306c | h306c
                      · have p306_0 := h306c.1
                        have p306_1 := h306c.2.1
                        have p306_2 := h306c.2.2.1
                        have p306_3 := h306c.2.2.2
                        linarith only [hlam, p306_0]
                      · have p306_0 := h306c.1
                        have p306_1 := h306c.2.1
                        have p306_2 := h306c.2.2.1
                        have p306_3 := h306c.2.2.2
                        linarith only [h301, h305, hc03, hc45, hlam, hphi, ht0b, ht5b, p306_1]
                      · have p306_0 := h306c.1
                        have p306_1 := h306c.2.1
                        have p306_2 := h306c.2.2.1
                        have p306_3 := h306c.2.2.2
                        linarith only [h2, hlam, p306_1]
                      · have p306_0 := h306c.1
                        have p306_1 := h306c.2.1
                        have p306_2 := h306c.2.2.1
                        have p306_3 := h306c.2.2.2
                        linarith only [h2, h305, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p306_1, u2elo2]
                      · have p306_0 := h306c.1
                        have p306_1 := h306c.2.1
                        have p306_2 := h306c.2.2.1
                        have p306_3 := h306c.2.2.2
                        linarith only [h2, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p306_1, u2elo2]
                      · have p306_0 := h306c.1
                        have p306_1 := h306c.2.1
                        have p306_2 := h306c.2.2.1
                        have p306_3 := h306c.2.2.2
                        linarith only [h1, hlam, p306_0]
                      · have p306_0 := h306c.1
                        have p306_1 := h306c.2.1
                        have p306_2 := h306c.2.2.1
                        have p306_3 := h306c.2.2.2
                        linarith only [hlam, p306_0]
                      · have p306_0 := h306c.1
                        have p306_1 := h306c.2.1
                        have p306_2 := h306c.2.2.1
                        have p306_3 := h306c.2.2.2
                        linarith only [h299, hlam, p306_1]
                      · have p306_0 := h306c.1
                        have p306_1 := h306c.2.1
                        have p306_2 := h306c.2.2.1
                        have p306_3 := h306c.2.2.2
                        linarith only [h305, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p306_1]
                      · have p306_0 := h306c.1
                        have p306_1 := h306c.2.1
                        have p306_2 := h306c.2.2.1
                        have p306_3 := h306c.2.2.2
                        linarith only [h1, h2, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p306_1, u2elo2]
                      · have p306_0 := h306c.1
                        have p306_1 := h306c.2.1
                        have p306_2 := h306c.2.2.1
                        have p306_3 := h306c.2.2.2
                        linarith only [hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p306_1, u2elo2]
                      · have p306_0 := h306c.1
                        have p306_1 := h306c.2.1
                        have p306_2 := h306c.2.2.1
                        have p306_3 := h306c.2.2.2
                        linarith only [hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p306_1, u2elo2]
                      · have p306_0 := h306c.1
                        have p306_1 := h306c.2.1
                        have p306_2 := h306c.2.2.1
                        have p306_3 := h306c.2.2.2
                        linarith only [hlam, p306_0]
                      · have p306_0 := h306c.1
                        have p306_1 := h306c.2.1
                        have p306_2 := h306c.2.2.1
                        have p306_3 := h306c.2.2.2
                        linarith only [h305, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p306_1, u2elo2]
                      · have p306_0 := h306c.1
                        have p306_1 := h306c.2.1
                        have p306_2 := h306c.2.2.1
                        have p306_3 := h306c.2.2.2
                        linarith only [hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p306_1, u2elo2]
                      · have p306_0 := h306c.1
                        have p306_1 := h306c.2.1
                        have p306_2 := h306c.2.2.1
                        have p306_3 := h306c.2.2.2
                        linarith only [h297, hlam, p306_0]
                      · have p306_0 := h306c.1
                        have p306_1 := h306c.2.1
                        have p306_2 := h306c.2.2.1
                        have p306_3 := h306c.2.2.2
                        linarith only [h301, hlam, p306_0]
                      · have p306_0 := h306c.1
                        have p306_1 := h306c.2.1
                        have p306_2 := h306c.2.2.1
                        have p306_3 := h306c.2.2.2
                        linarith only [h303, hlam, p306_0]
                      · have p306_0 := h306c.1
                        have p306_1 := h306c.2.1
                        have p306_2 := h306c.2.2.1
                        have p306_3 := h306c.2.2.2
                        linarith only [hlam, p306_0]
                      · have p306_0 := h306c.1
                        have p306_1 := h306c.2.1
                        have p306_2 := h306c.2.2.1
                        have p306_3 := h306c.2.2.2
                        linarith only [h1, h301, hc03, hc35, hlam, hphi, ht0b, ht5b, p306_1]
                      · have p306_0 := h306c.1
                        have p306_1 := h306c.2.1
                        have p306_2 := h306c.2.2.1
                        have p306_3 := h306c.2.2.2
                        linarith only [h298, hlam, p306_0]
                      · have p306_0 := h306c.1
                        have p306_1 := h306c.2.1
                        have p306_2 := h306c.2.2.1
                        have p306_3 := h306c.2.2.2
                        linarith only [h302, hlam, p306_0]
                      · have p306_0 := h306c.1
                        have p306_1 := h306c.2.1
                        have p306_2 := h306c.2.2.1
                        have p306_3 := h306c.2.2.2
                        linarith only [h304, hlam, p306_0]
                      · have p306_0 := h306c.1
                        have p306_1 := h306c.2.1
                        have p306_2 := h306c.2.2.1
                        have p306_3 := h306c.2.2.2
                        linarith only [h305, hlam, p306_0]
                      · have p306_0 := h306c.1
                        have p306_1 := h306c.2.1
                        have p306_2 := h306c.2.2.1
                        have p306_3 := h306c.2.2.2
                        linarith only [hlam, p306_0]
                    · rcases h3bigk with h332c | h332c | h332c | h332c | h332c | h332c | h332c | h332c | h332c | h332c | h332c | h332c | h332c | h332c | h332c | h332c | h332c | h332c | h332c | h332c | h332c | h332c | h332c | h332c | h332c
                      · have p332_0 := h332c.1
                        have p332_1 := h332c.2.1
                        have p332_2 := h332c.2.2.1
                        have p332_3 := h332c.2.2.2
                        linarith only [hlam, p332_0]
                      · have p332_0 := h332c.1
                        have p332_1 := h332c.2.1
                        have p332_2 := h332c.2.2.1
                        have p332_3 := h332c.2.2.2
                        linarith only [h2, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p332_1, u2elo2]
                      · have p332_0 := h332c.1
                        have p332_1 := h332c.2.1
                        have p332_2 := h332c.2.2.1
                        have p332_3 := h332c.2.2.2
                        linarith only [h2, hlam, p332_1]
                      · have p332_0 := h332c.1
                        have p332_1 := h332c.2.1
                        have p332_2 := h332c.2.2.1
                        have p332_3 := h332c.2.2.2
                        linarith only [h2, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p332_1, u2elo2]
                      · have p332_0 := h332c.1
                        have p332_1 := h332c.2.1
                        have p332_2 := h332c.2.2.1
                        have p332_3 := h332c.2.2.2
                        linarith only [h2, h305, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p332_1, u2elo2]
                      · have p332_0 := h332c.1
                        have p332_1 := h332c.2.1
                        have p332_2 := h332c.2.2.1
                        have p332_3 := h332c.2.2.2
                        linarith only [h1, hlam, p332_0]
                      · have p332_0 := h332c.1
                        have p332_1 := h332c.2.1
                        have p332_2 := h332c.2.2.1
                        have p332_3 := h332c.2.2.2
                        linarith only [hlam, p332_0]
                      · have p332_0 := h332c.1
                        have p332_1 := h332c.2.1
                        have p332_2 := h332c.2.2.1
                        have p332_3 := h332c.2.2.2
                        linarith only [h299, hlam, p332_1]
                      · have p332_0 := h332c.1
                        have p332_1 := h332c.2.1
                        have p332_2 := h332c.2.2.1
                        have p332_3 := h332c.2.2.2
                        linarith only [h1, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p332_1]
                      · have p332_0 := h332c.1
                        have p332_1 := h332c.2.1
                        have p332_2 := h332c.2.2.1
                        have p332_3 := h332c.2.2.2
                        linarith only [h1, h2, h305, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p332_1, u2elo2]
                      · have p332_0 := h332c.1
                        have p332_1 := h332c.2.1
                        have p332_2 := h332c.2.2.1
                        have p332_3 := h332c.2.2.2
                        linarith only [hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p332_1, u2elo2]
                      · have p332_0 := h332c.1
                        have p332_1 := h332c.2.1
                        have p332_2 := h332c.2.2.1
                        have p332_3 := h332c.2.2.2
                        linarith only [hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p332_1, u2elo2]
                      · have p332_0 := h332c.1
                        have p332_1 := h332c.2.1
                        have p332_2 := h332c.2.2.1
                        have p332_3 := h332c.2.2.2
                        linarith only [hlam, p332_0]
                      · have p332_0 := h332c.1
                        have p332_1 := h332c.2.1
                        have p332_2 := h332c.2.2.1
                        have p332_3 := h332c.2.2.2
                        linarith only [hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p332_1, u2elo2]
                      · have p332_0 := h332c.1
                        have p332_1 := h332c.2.1
                        have p332_2 := h332c.2.2.1
                        have p332_3 := h332c.2.2.2
                        linarith only [h305, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p332_1, u2elo2]
                      · have p332_0 := h332c.1
                        have p332_1 := h332c.2.1
                        have p332_2 := h332c.2.2.1
                        have p332_3 := h332c.2.2.2
                        linarith only [h297, hlam, p332_0]
                      · have p332_0 := h332c.1
                        have p332_1 := h332c.2.1
                        have p332_2 := h332c.2.2.1
                        have p332_3 := h332c.2.2.2
                        linarith only [h301, hlam, p332_0]
                      · have p332_0 := h332c.1
                        have p332_1 := h332c.2.1
                        have p332_2 := h332c.2.2.1
                        have p332_3 := h332c.2.2.2
                        linarith only [h303, hlam, p332_0]
                      · have p332_0 := h332c.1
                        have p332_1 := h332c.2.1
                        have p332_2 := h332c.2.2.1
                        have p332_3 := h332c.2.2.2
                        linarith only [hlam, p332_0]
                      · have p332_0 := h332c.1
                        have p332_1 := h332c.2.1
                        have p332_2 := h332c.2.2.1
                        have p332_3 := h332c.2.2.2
                        linarith only [h305, hlam, p332_1]
                      · have p332_0 := h332c.1
                        have p332_1 := h332c.2.1
                        have p332_2 := h332c.2.2.1
                        have p332_3 := h332c.2.2.2
                        linarith only [h298, hlam, p332_0]
                      · have p332_0 := h332c.1
                        have p332_1 := h332c.2.1
                        have p332_2 := h332c.2.2.1
                        have p332_3 := h332c.2.2.2
                        linarith only [h302, hlam, p332_0]
                      · have p332_0 := h332c.1
                        have p332_1 := h332c.2.1
                        have p332_2 := h332c.2.2.1
                        have p332_3 := h332c.2.2.2
                        linarith only [h304, hlam, p332_0]
                      · have p332_0 := h332c.1
                        have p332_1 := h332c.2.1
                        have p332_2 := h332c.2.2.1
                        have p332_3 := h332c.2.2.2
                        linarith only [h1, h302, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p332_1]
                      · have p332_0 := h332c.1
                        have p332_1 := h332c.2.1
                        have p332_2 := h332c.2.2.1
                        have p332_3 := h332c.2.2.2
                        linarith only [hlam, p332_0]
                  · linarith only [h1, h2, h302, h304, hlam]
                · linarith only [h2, h297, h303, hlam]
              · linarith only [h2, h298, h301, h302, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
            · linarith only [h2, h297, h299, h301, hc12, hlam, hphi, u2elo2]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h362 | h362
          · linarith only [h0, h2, h362, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h364 | h364
            · rcases m.htr 1 3 5 (by decide) (by decide) with h365 | h365
              · linarith only [h1, h298, h365, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h367 | h367
                · rcases m.htr 2 3 5 (by decide) (by decide) with h368 | h368
                  · linarith only [h1, h298, h364, h368, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h370 | h370
                    · linarith only [h0, h1, h2, h364, h368, h370, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                    · rcases h3bigk with h372c | h372c | h372c | h372c | h372c | h372c | h372c | h372c | h372c | h372c | h372c | h372c | h372c | h372c | h372c | h372c | h372c | h372c | h372c | h372c | h372c | h372c | h372c | h372c | h372c
                      · have p372_0 := h372c.1
                        have p372_1 := h372c.2.1
                        have p372_2 := h372c.2.2.1
                        have p372_3 := h372c.2.2.2
                        linarith only [hlam, p372_0]
                      · have p372_0 := h372c.1
                        have p372_1 := h372c.2.1
                        have p372_2 := h372c.2.2.1
                        have p372_3 := h372c.2.2.2
                        linarith only [h2, h368, h370, hc13, hc45, hlam, hphi, ht34, p372_1]
                      · have p372_0 := h372c.1
                        have p372_1 := h372c.2.1
                        have p372_2 := h372c.2.2.1
                        have p372_3 := h372c.2.2.2
                        linarith only [h2, hlam, p372_1]
                      · have p372_0 := h372c.1
                        have p372_1 := h372c.2.1
                        have p372_2 := h372c.2.2.1
                        have p372_3 := h372c.2.2.2
                        linarith only [h2, h368, h370, hc34, hc45, hlam, hphi, p372_1]
                      · have p372_0 := h372c.1
                        have p372_1 := h372c.2.1
                        have p372_2 := h372c.2.2.1
                        have p372_3 := h372c.2.2.2
                        linarith only [h298, hlam, p372_0]
                      · have p372_0 := h372c.1
                        have p372_1 := h372c.2.1
                        have p372_2 := h372c.2.2.1
                        have p372_3 := h372c.2.2.2
                        linarith only [h1, hlam, p372_0]
                      · have p372_0 := h372c.1
                        have p372_1 := h372c.2.1
                        have p372_2 := h372c.2.2.1
                        have p372_3 := h372c.2.2.2
                        linarith only [hlam, p372_0]
                      · have p372_0 := h372c.1
                        have p372_1 := h372c.2.1
                        have p372_2 := h372c.2.2.1
                        have p372_3 := h372c.2.2.2
                        linarith only [h362, hlam, p372_1]
                      · have p372_0 := h372c.1
                        have p372_1 := h372c.2.1
                        have p372_2 := h372c.2.2.1
                        have p372_3 := h372c.2.2.2
                        linarith only [h1, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p372_1]
                      · have p372_0 := h372c.1
                        have p372_1 := h372c.2.1
                        have p372_2 := h372c.2.2.1
                        have p372_3 := h372c.2.2.2
                        linarith only [h365, hlam, p372_0]
                      · have p372_0 := h372c.1
                        have p372_1 := h372c.2.1
                        have p372_2 := h372c.2.2.1
                        have p372_3 := h372c.2.2.2
                        linarith only [h368, h370, hc03, hc45, hlam, hphi, ht34, p372_1]
                      · have p372_0 := h372c.1
                        have p372_1 := h372c.2.1
                        have p372_2 := h372c.2.2.1
                        have p372_3 := h372c.2.2.2
                        linarith only [h368, h370, hc13, hc45, hlam, hphi, ht34, p372_1]
                      · have p372_0 := h372c.1
                        have p372_1 := h372c.2.1
                        have p372_2 := h372c.2.2.1
                        have p372_3 := h372c.2.2.2
                        linarith only [hlam, p372_0]
                      · have p372_0 := h372c.1
                        have p372_1 := h372c.2.1
                        have p372_2 := h372c.2.2.1
                        have p372_3 := h372c.2.2.2
                        linarith only [h368, h370, hc34, hc45, hlam, hphi, p372_1]
                      · have p372_0 := h372c.1
                        have p372_1 := h372c.2.1
                        have p372_2 := h372c.2.2.1
                        have p372_3 := h372c.2.2.2
                        linarith only [h368, hlam, p372_0]
                      · have p372_0 := h372c.1
                        have p372_1 := h372c.2.1
                        have p372_2 := h372c.2.2.1
                        have p372_3 := h372c.2.2.2
                        linarith only [h297, hlam, p372_0]
                      · have p372_0 := h372c.1
                        have p372_1 := h372c.2.1
                        have p372_2 := h372c.2.2.1
                        have p372_3 := h372c.2.2.2
                        linarith only [h364, hlam, p372_0]
                      · have p372_0 := h372c.1
                        have p372_1 := h372c.2.1
                        have p372_2 := h372c.2.2.1
                        have p372_3 := h372c.2.2.2
                        linarith only [h367, hlam, p372_0]
                      · have p372_0 := h372c.1
                        have p372_1 := h372c.2.1
                        have p372_2 := h372c.2.2.1
                        have p372_3 := h372c.2.2.2
                        linarith only [hlam, p372_0]
                      · have p372_0 := h372c.1
                        have p372_1 := h372c.2.1
                        have p372_2 := h372c.2.2.1
                        have p372_3 := h372c.2.2.2
                        linarith only [h370, hlam, p372_1]
                      · have p372_0 := h372c.1
                        have p372_1 := h372c.2.1
                        have p372_2 := h372c.2.2.1
                        have p372_3 := h372c.2.2.2
                        linarith only [h370, hc03, hc45, hlam, hphi, ht34, p372_1]
                      · have p372_0 := h372c.1
                        have p372_1 := h372c.2.1
                        have p372_2 := h372c.2.2.1
                        have p372_3 := h372c.2.2.2
                        linarith only [h364, h370, hc34, hc45, hlam, hphi, p372_1]
                      · have p372_0 := h372c.1
                        have p372_1 := h372c.2.1
                        have p372_2 := h372c.2.2.1
                        have p372_3 := h372c.2.2.2
                        linarith only [h370, hc23, hc45, hlam, hphi, ht34, p372_1]
                      · have p372_0 := h372c.1
                        have p372_1 := h372c.2.1
                        have p372_2 := h372c.2.2.1
                        have p372_3 := h372c.2.2.2
                        linarith only [h370, hc34, hc45, hlam, hphi, p372_1]
                      · have p372_0 := h372c.1
                        have p372_1 := h372c.2.1
                        have p372_2 := h372c.2.2.1
                        have p372_3 := h372c.2.2.2
                        linarith only [hlam, p372_0]
                · linarith only [h0, h1, h2, h364, h367, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
            · linarith only [h297, h298, h364, hc13, hc35, hlam, hphi]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h400 | h400
        · rcases m.htr 1 2 3 (by decide) (by decide) with h401 | h401
          · linarith only [h0, h2, h401, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h403 | h403
            · linarith only [h1, h297, h400, h403, hc01, hc35, hlam, hphi, ht0b, ht5b]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h405 | h405
              · rcases m.htr 2 3 4 (by decide) (by decide) with h406 | h406
                · linarith only [h0, h2, h297, h406, hc12, hlam, hphi, u2elo2]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h408 | h408
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h409 | h409
                    · rcases h3bigk with h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c
                      · have p410_0 := h410c.1
                        have p410_1 := h410c.2.1
                        have p410_2 := h410c.2.2.1
                        have p410_3 := h410c.2.2.2
                        linarith only [hlam, p410_0]
                      · have p410_0 := h410c.1
                        have p410_1 := h410c.2.1
                        have p410_2 := h410c.2.2.1
                        have p410_3 := h410c.2.2.2
                        linarith only [h405, h409, hc03, hc45, hlam, hphi, ht0b, ht5b, p410_1]
                      · have p410_0 := h410c.1
                        have p410_1 := h410c.2.1
                        have p410_2 := h410c.2.2.1
                        have p410_3 := h410c.2.2.2
                        linarith only [h2, hlam, p410_1]
                      · have p410_0 := h410c.1
                        have p410_1 := h410c.2.1
                        have p410_2 := h410c.2.2.1
                        have p410_3 := h410c.2.2.2
                        linarith only [h297, hlam, p410_0]
                      · have p410_0 := h410c.1
                        have p410_1 := h410c.2.1
                        have p410_2 := h410c.2.2.1
                        have p410_3 := h410c.2.2.2
                        linarith only [h2, h409, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p410_1, u2elo2]
                      · have p410_0 := h410c.1
                        have p410_1 := h410c.2.1
                        have p410_2 := h410c.2.2.1
                        have p410_3 := h410c.2.2.2
                        linarith only [h1, hlam, p410_0]
                      · have p410_0 := h410c.1
                        have p410_1 := h410c.2.1
                        have p410_2 := h410c.2.2.1
                        have p410_3 := h410c.2.2.2
                        linarith only [hlam, p410_0]
                      · have p410_0 := h410c.1
                        have p410_1 := h410c.2.1
                        have p410_2 := h410c.2.2.1
                        have p410_3 := h410c.2.2.2
                        linarith only [h401, hlam, p410_1]
                      · have p410_0 := h410c.1
                        have p410_1 := h410c.2.1
                        have p410_2 := h410c.2.2.1
                        have p410_3 := h410c.2.2.2
                        linarith only [h403, hlam, p410_0]
                      · have p410_0 := h410c.1
                        have p410_1 := h410c.2.1
                        have p410_2 := h410c.2.2.1
                        have p410_3 := h410c.2.2.2
                        linarith only [h1, h409, hc01, hc45, hlam, hphi, ht0b, ht5b, p410_1]
                      · have p410_0 := h410c.1
                        have p410_1 := h410c.2.1
                        have p410_2 := h410c.2.2.1
                        have p410_3 := h410c.2.2.2
                        linarith only [hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p410_1, u2elo2]
                      · have p410_0 := h410c.1
                        have p410_1 := h410c.2.1
                        have p410_2 := h410c.2.2.1
                        have p410_3 := h410c.2.2.2
                        linarith only [h406, hc13, hc34, hlam, hphi, p410_1]
                      · have p410_0 := h410c.1
                        have p410_1 := h410c.2.1
                        have p410_2 := h410c.2.2.1
                        have p410_3 := h410c.2.2.2
                        linarith only [hlam, p410_0]
                      · have p410_0 := h410c.1
                        have p410_1 := h410c.2.1
                        have p410_2 := h410c.2.2.1
                        have p410_3 := h410c.2.2.2
                        linarith only [h406, hlam, p410_0]
                      · have p410_0 := h410c.1
                        have p410_1 := h410c.2.1
                        have p410_2 := h410c.2.2.1
                        have p410_3 := h410c.2.2.2
                        linarith only [h406, h409, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p410_1, u2elo3]
                      · have p410_0 := h410c.1
                        have p410_1 := h410c.2.1
                        have p410_2 := h410c.2.2.1
                        have p410_3 := h410c.2.2.2
                        linarith only [h2, hc02, hc34, hlam, hphi, ht23, p410_1]
                      · have p410_0 := h410c.1
                        have p410_1 := h410c.2.1
                        have p410_2 := h410c.2.2.1
                        have p410_3 := h410c.2.2.2
                        linarith only [h405, h409, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p410_1]
                      · have p410_0 := h410c.1
                        have p410_1 := h410c.2.1
                        have p410_2 := h410c.2.2.1
                        have p410_3 := h410c.2.2.2
                        linarith only [hc23, hc34, hlam, hphi, p410_1]
                      · have p410_0 := h410c.1
                        have p410_1 := h410c.2.1
                        have p410_2 := h410c.2.2.1
                        have p410_3 := h410c.2.2.2
                        linarith only [hlam, p410_0]
                      · have p410_0 := h410c.1
                        have p410_1 := h410c.2.1
                        have p410_2 := h410c.2.2.1
                        have p410_3 := h410c.2.2.2
                        rcases p410_3 (m.d 0 3) (by simp) with h430 | h430
                        · linarith only [h297, h430, hlam]
                        · linarith only [h400, h430, hlam]
                      · have p410_0 := h410c.1
                        have p410_1 := h410c.2.1
                        have p410_2 := h410c.2.2.1
                        have p410_3 := h410c.2.2.2
                        linarith only [h400, hlam, p410_0]
                      · have p410_0 := h410c.1
                        have p410_1 := h410c.2.1
                        have p410_2 := h410c.2.2.1
                        have p410_3 := h410c.2.2.2
                        linarith only [h405, hlam, p410_0]
                      · have p410_0 := h410c.1
                        have p410_1 := h410c.2.1
                        have p410_2 := h410c.2.2.1
                        have p410_3 := h410c.2.2.2
                        linarith only [h408, hlam, p410_0]
                      · have p410_0 := h410c.1
                        have p410_1 := h410c.2.1
                        have p410_2 := h410c.2.2.1
                        have p410_3 := h410c.2.2.2
                        linarith only [h409, hlam, p410_0]
                      · have p410_0 := h410c.1
                        have p410_1 := h410c.2.1
                        have p410_2 := h410c.2.2.1
                        have p410_3 := h410c.2.2.2
                        linarith only [hlam, p410_0]
                    · linarith only [h0, h2, h406, h409, hc12, hc45, hlam, hphi, ht23, ht34]
                  · linarith only [h0, h1, h2, h405, h408, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
              · linarith only [h297, h400, h405, hc13, hc34, hlam, hphi]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h441 | h441
          · linarith only [h0, h2, h441, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h443 | h443
            · linarith only [h1, h297, h443, hlam]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h445 | h445
              · linarith only [h1, h400, h445, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h447 | h447
                · linarith only [h2, h297, h447, hc02, hlam, hphi, u2elo2]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h449 | h449
                  · linarith only [h400, h447, h449, hc03, hc34, hlam, hphi]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h451 | h451
                    · rcases h3bigk with h452c | h452c | h452c | h452c | h452c | h452c | h452c | h452c | h452c | h452c | h452c | h452c | h452c | h452c | h452c | h452c | h452c | h452c | h452c | h452c | h452c | h452c | h452c | h452c | h452c
                      · have p452_0 := h452c.1
                        have p452_1 := h452c.2.1
                        have p452_2 := h452c.2.2.1
                        have p452_3 := h452c.2.2.2
                        linarith only [hlam, p452_0]
                      · have p452_0 := h452c.1
                        have p452_1 := h452c.2.1
                        have p452_2 := h452c.2.2.1
                        have p452_3 := h452c.2.2.2
                        linarith only [h2, h441, hc12, hlam, hphi, p452_1, u2elo2]
                      · have p452_0 := h452c.1
                        have p452_1 := h452c.2.1
                        have p452_2 := h452c.2.2.1
                        have p452_3 := h452c.2.2.2
                        linarith only [h2, hlam, p452_1]
                      · have p452_0 := h452c.1
                        have p452_1 := h452c.2.1
                        have p452_2 := h452c.2.2.1
                        have p452_3 := h452c.2.2.2
                        linarith only [h297, hlam, p452_0]
                      · have p452_0 := h452c.1
                        have p452_1 := h452c.2.1
                        have p452_2 := h452c.2.2.1
                        have p452_3 := h452c.2.2.2
                        linarith only [h400, hlam, p452_0]
                      · have p452_0 := h452c.1
                        have p452_1 := h452c.2.1
                        have p452_2 := h452c.2.2.1
                        have p452_3 := h452c.2.2.2
                        linarith only [h1, hlam, p452_0]
                      · have p452_0 := h452c.1
                        have p452_1 := h452c.2.1
                        have p452_2 := h452c.2.2.1
                        have p452_3 := h452c.2.2.2
                        linarith only [hlam, p452_0]
                      · have p452_0 := h452c.1
                        have p452_1 := h452c.2.1
                        have p452_2 := h452c.2.2.1
                        have p452_3 := h452c.2.2.2
                        linarith only [h441, hlam, p452_1]
                      · have p452_0 := h452c.1
                        have p452_1 := h452c.2.1
                        have p452_2 := h452c.2.2.1
                        have p452_3 := h452c.2.2.2
                        linarith only [h443, hlam, p452_0]
                      · have p452_0 := h452c.1
                        have p452_1 := h452c.2.1
                        have p452_2 := h452c.2.2.1
                        have p452_3 := h452c.2.2.2
                        linarith only [h445, hlam, p452_0]
                      · have p452_0 := h452c.1
                        have p452_1 := h452c.2.1
                        have p452_2 := h452c.2.2.1
                        have p452_3 := h452c.2.2.2
                        linarith only [hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p452_1, u2elo2]
                      · have p452_0 := h452c.1
                        have p452_1 := h452c.2.1
                        have p452_2 := h452c.2.2.1
                        have p452_3 := h452c.2.2.2
                        linarith only [h441, h449, hc12, hc35, hlam, hphi, ht23, p452_1]
                      · have p452_0 := h452c.1
                        have p452_1 := h452c.2.1
                        have p452_2 := h452c.2.2.1
                        have p452_3 := h452c.2.2.2
                        linarith only [hlam, p452_0]
                      · have p452_0 := h452c.1
                        have p452_1 := h452c.2.1
                        have p452_2 := h452c.2.2.1
                        have p452_3 := h452c.2.2.2
                        linarith only [h447, hlam, p452_0]
                      · have p452_0 := h452c.1
                        have p452_1 := h452c.2.1
                        have p452_2 := h452c.2.2.1
                        have p452_3 := h452c.2.2.2
                        linarith only [h449, hlam, p452_0]
                      · have p452_0 := h452c.1
                        have p452_1 := h452c.2.1
                        have p452_2 := h452c.2.2.1
                        have p452_3 := h452c.2.2.2
                        linarith only [h1, h441, hc12, hc34, hlam, hphi, ht23, p452_1]
                      · have p452_0 := h452c.1
                        have p452_1 := h452c.2.1
                        have p452_2 := h452c.2.2.1
                        have p452_3 := h452c.2.2.2
                        linarith only [h441, hc12, hc34, hlam, hphi, ht23, p452_1]
                      · have p452_0 := h452c.1
                        have p452_1 := h452c.2.1
                        have p452_2 := h452c.2.2.1
                        have p452_3 := h452c.2.2.2
                        linarith only [hc23, hc34, hlam, hphi, p452_1]
                      · have p452_0 := h452c.1
                        have p452_1 := h452c.2.1
                        have p452_2 := h452c.2.2.1
                        have p452_3 := h452c.2.2.2
                        linarith only [hlam, p452_0]
                      · have p452_0 := h452c.1
                        have p452_1 := h452c.2.1
                        have p452_2 := h452c.2.2.1
                        have p452_3 := h452c.2.2.2
                        linarith only [h1, h400, h441, hc12, hc34, hlam, hphi, ht23, p452_1]
                      · have p452_0 := h452c.1
                        have p452_1 := h452c.2.1
                        have p452_2 := h452c.2.2.1
                        have p452_3 := h452c.2.2.2
                        linarith only [h1, h441, hc12, hc35, hlam, hphi, ht23, p452_1]
                      · have p452_0 := h452c.1
                        have p452_1 := h452c.2.1
                        have p452_2 := h452c.2.2.1
                        have p452_3 := h452c.2.2.2
                        linarith only [h441, hc12, hc35, hlam, hphi, ht23, p452_1]
                      · have p452_0 := h452c.1
                        have p452_1 := h452c.2.1
                        have p452_2 := h452c.2.2.1
                        have p452_3 := h452c.2.2.2
                        linarith only [h0, h2, hc12, hc35, hlam, hphi, ht23, p452_1]
                      · have p452_0 := h452c.1
                        have p452_1 := h452c.2.1
                        have p452_2 := h452c.2.2.1
                        have p452_3 := h452c.2.2.2
                        linarith only [h451, hlam, p452_0]
                      · have p452_0 := h452c.1
                        have p452_1 := h452c.2.1
                        have p452_2 := h452c.2.2.1
                        have p452_3 := h452c.2.2.2
                        linarith only [hlam, p452_0]
                    · linarith only [h0, h2, h447, h451, hc12, hc45, hlam, hphi, ht23, ht34]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h479 | h479
    · linarith only [h0, h1, h479, hlam]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h481 | h481
      · rcases m.htr 0 3 5 (by decide) (by decide) with h482 | h482
        · rcases m.htr 1 2 3 (by decide) (by decide) with h483 | h483
          · linarith only [h479, h483, hc02, hlam, hphi, u2elo1]
          · linarith only [h0, h1, h483, hc12, hlam, hphi, u2elo2]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h486 | h486
          · linarith only [h0, h1, h479, h481, h486, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
          · linarith only [h0, h1, h486, hc12, hlam, hphi, u2elo2]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h489 | h489
        · rcases m.htr 1 2 3 (by decide) (by decide) with h490 | h490
          · linarith only [h0, h1, h481, h490, hc23, hc34, hlam, hphi]
          · linarith only [h0, h1, h490, hc12, hlam, hphi, u2elo2]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h493 | h493
          · linarith only [h0, h1, h481, h493, hc23, hc34, hlam, hphi]
          · linarith only [h0, h1, h493, hc12, hlam, hphi, u2elo2]

end R2N4
