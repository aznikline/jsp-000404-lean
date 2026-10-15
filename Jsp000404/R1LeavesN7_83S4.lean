import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_10_12_23_L_R_L_0_H_I (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0ehi := hb0.1
  have h2elo := hb2.1
  have h3bigk := hb3.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 2 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 3 4 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 3 5 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 2 3 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 3 4 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 3 5 (by decide) (by decide) with h7 | h7
                · rcases m.htr 2 3 4 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h10 | h10
                      · linarith only [h1, h10, h8, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0]
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
                          linarith only [h1, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p12_1, u2elo0]
                        · have p12_0 := h12c.1
                          have p12_1 := h12c.2.1
                          have p12_2 := h12c.2.2.1
                          have p12_3 := h12c.2.2.2
                          linarith only [h1, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p12_1, u2elo0]
                        · have p12_0 := h12c.1
                          have p12_1 := h12c.2.1
                          have p12_2 := h12c.2.2.1
                          have p12_3 := h12c.2.2.2
                          linarith only [h1, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p12_1, u2elo0]
                        · have p12_0 := h12c.1
                          have p12_1 := h12c.2.1
                          have p12_2 := h12c.2.2.1
                          have p12_3 := h12c.2.2.2
                          linarith only [h1, h10, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p12_1, u2elo0]
                        · have p12_0 := h12c.1
                          have p12_1 := h12c.2.1
                          have p12_2 := h12c.2.2.1
                          have p12_3 := h12c.2.2.2
                          linarith only [h0, hlam, p12_0]
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
                          linarith only [h0, h1, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p12_1, u2elo0]
                        · have p12_0 := h12c.1
                          have p12_1 := h12c.2.1
                          have p12_2 := h12c.2.2.1
                          have p12_3 := h12c.2.2.2
                          linarith only [h0, h1, h10, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p12_1, u2elo0]
                        · have p12_0 := h12c.1
                          have p12_1 := h12c.2.1
                          have p12_2 := h12c.2.2.1
                          have p12_3 := h12c.2.2.2
                          linarith only [h1, hlam, p12_0]
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
                          linarith only [h1, h10, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p12_1, u2elo0]
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
                          linarith only [h1, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p12_1, u2elo0]
                        · have p12_0 := h12c.1
                          have p12_1 := h12c.2.1
                          have p12_2 := h12c.2.2.1
                          have p12_3 := h12c.2.2.2
                          linarith only [hlam, p12_0]
                    · linarith only [h0, h1, h7, h8, h9, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h39 | h39
                    · linarith only [h1, h3, h39, h8, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0]
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
                          linarith only [h1, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p42_1, u2elo0]
                        · have p42_0 := h42c.1
                          have p42_1 := h42c.2.1
                          have p42_2 := h42c.2.2.1
                          have p42_3 := h42c.2.2.2
                          linarith only [h1, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p42_1, u2elo0]
                        · have p42_0 := h42c.1
                          have p42_1 := h42c.2.1
                          have p42_2 := h42c.2.2.1
                          have p42_3 := h42c.2.2.2
                          linarith only [h1, h39, h41, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p42_1, u2elo0]
                        · have p42_0 := h42c.1
                          have p42_1 := h42c.2.1
                          have p42_2 := h42c.2.2.1
                          have p42_3 := h42c.2.2.2
                          linarith only [h1, h39, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p42_1, u2elo0]
                        · have p42_0 := h42c.1
                          have p42_1 := h42c.2.1
                          have p42_2 := h42c.2.2.1
                          have p42_3 := h42c.2.2.2
                          linarith only [h0, hlam, p42_0]
                        · have p42_0 := h42c.1
                          have p42_1 := h42c.2.1
                          have p42_2 := h42c.2.2.1
                          have p42_3 := h42c.2.2.2
                          linarith only [hlam, p42_0]
                        · have p42_0 := h42c.1
                          have p42_1 := h42c.2.1
                          have p42_2 := h42c.2.2.1
                          have p42_3 := h42c.2.2.2
                          linarith only [h0, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p42_1]
                        · have p42_0 := h42c.1
                          have p42_1 := h42c.2.1
                          have p42_2 := h42c.2.2.1
                          have p42_3 := h42c.2.2.2
                          linarith only [h0, h1, h39, h41, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p42_1, u2elo0]
                        · have p42_0 := h42c.1
                          have p42_1 := h42c.2.1
                          have p42_2 := h42c.2.2.1
                          have p42_3 := h42c.2.2.2
                          linarith only [h0, h1, h39, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p42_1, u2elo0]
                        · have p42_0 := h42c.1
                          have p42_1 := h42c.2.1
                          have p42_2 := h42c.2.2.1
                          have p42_3 := h42c.2.2.2
                          linarith only [h1, hlam, p42_0]
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
                          linarith only [h0, h1, h39, h6, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p42_1, u2elo0]
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
                          linarith only [h1, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p68_1, u2elo0]
                        · have p68_0 := h68c.1
                          have p68_1 := h68c.2.1
                          have p68_2 := h68c.2.2.1
                          have p68_3 := h68c.2.2.2
                          linarith only [h1, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p68_1, u2elo0]
                        · have p68_0 := h68c.1
                          have p68_1 := h68c.2.1
                          have p68_2 := h68c.2.2.1
                          have p68_3 := h68c.2.2.2
                          linarith only [h1, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p68_1, u2elo0]
                        · have p68_0 := h68c.1
                          have p68_1 := h68c.2.1
                          have p68_2 := h68c.2.2.1
                          have p68_3 := h68c.2.2.2
                          linarith only [h1, h41, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p68_1, u2elo0]
                        · have p68_0 := h68c.1
                          have p68_1 := h68c.2.1
                          have p68_2 := h68c.2.2.1
                          have p68_3 := h68c.2.2.2
                          linarith only [h0, hlam, p68_0]
                        · have p68_0 := h68c.1
                          have p68_1 := h68c.2.1
                          have p68_2 := h68c.2.2.1
                          have p68_3 := h68c.2.2.2
                          linarith only [hlam, p68_0]
                        · have p68_0 := h68c.1
                          have p68_1 := h68c.2.1
                          have p68_2 := h68c.2.2.1
                          have p68_3 := h68c.2.2.2
                          linarith only [h0, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p68_1]
                        · have p68_0 := h68c.1
                          have p68_1 := h68c.2.1
                          have p68_2 := h68c.2.2.1
                          have p68_3 := h68c.2.2.2
                          linarith only [h0, h1, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p68_1, u2elo0]
                        · have p68_0 := h68c.1
                          have p68_1 := h68c.2.1
                          have p68_2 := h68c.2.2.1
                          have p68_3 := h68c.2.2.2
                          linarith only [h0, h1, h41, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p68_1, u2elo0]
                        · have p68_0 := h68c.1
                          have p68_1 := h68c.2.1
                          have p68_2 := h68c.2.2.1
                          have p68_3 := h68c.2.2.2
                          linarith only [h1, hlam, p68_0]
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
                          linarith only [h0, h1, h7, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p68_1, u2elo0]
                        · have p68_0 := h68c.1
                          have p68_1 := h68c.2.1
                          have p68_2 := h68c.2.2.1
                          have p68_3 := h68c.2.2.2
                          linarith only [h0, h1, h7, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p68_1, u2elo0]
                        · have p68_0 := h68c.1
                          have p68_1 := h68c.2.1
                          have p68_2 := h68c.2.2.1
                          have p68_3 := h68c.2.2.2
                          linarith only [hlam, p68_0]
                · linarith only [h1, h4, h6, h7, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h95 | h95
                · linarith only [h1, h3, h6, h95, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h97 | h97
                  · linarith only [h1, h6, h97, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
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
                          linarith only [h1, h5, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p102_1, u2elo0]
                        · have p102_0 := h102c.1
                          have p102_1 := h102c.2.1
                          have p102_2 := h102c.2.2.1
                          have p102_3 := h102c.2.2.2
                          linarith only [h1, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p102_1, u2elo0]
                        · have p102_0 := h102c.1
                          have p102_1 := h102c.2.1
                          have p102_2 := h102c.2.2.1
                          have p102_3 := h102c.2.2.2
                          linarith only [h1, h101, h5, h95, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p102_1, u2elo0]
                        · have p102_0 := h102c.1
                          have p102_1 := h102c.2.1
                          have p102_2 := h102c.2.2.1
                          have p102_3 := h102c.2.2.2
                          linarith only [h1, h5, h95, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p102_1, u2elo0]
                        · have p102_0 := h102c.1
                          have p102_1 := h102c.2.1
                          have p102_2 := h102c.2.2.1
                          have p102_3 := h102c.2.2.2
                          linarith only [h0, hlam, p102_0]
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
                          linarith only [h1, hlam, p102_0]
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
                          linarith only [h1, h3, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p102_1, u2elo0]
                        · have p102_0 := h102c.1
                          have p102_1 := h102c.2.1
                          have p102_2 := h102c.2.2.1
                          have p102_3 := h102c.2.2.2
                          linarith only [h1, h3, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p102_1, u2elo0]
                        · have p102_0 := h102c.1
                          have p102_1 := h102c.2.1
                          have p102_2 := h102c.2.2.1
                          have p102_3 := h102c.2.2.2
                          linarith only [hlam, p102_0]
                        · have p102_0 := h102c.1
                          have p102_1 := h102c.2.1
                          have p102_2 := h102c.2.2.1
                          have p102_3 := h102c.2.2.2
                          linarith only [h1, h3, h95, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p102_1, u2elo0]
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
                          linarith only [h1, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p102_1, u2elo0]
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
                          linarith only [h1, h5, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p128_1, u2elo0]
                        · have p128_0 := h128c.1
                          have p128_1 := h128c.2.1
                          have p128_2 := h128c.2.2.1
                          have p128_3 := h128c.2.2.2
                          linarith only [h1, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p128_1, u2elo0]
                        · have p128_0 := h128c.1
                          have p128_1 := h128c.2.1
                          have p128_2 := h128c.2.2.1
                          have p128_3 := h128c.2.2.2
                          linarith only [h1, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p128_1, u2elo0]
                        · have p128_0 := h128c.1
                          have p128_1 := h128c.2.1
                          have p128_2 := h128c.2.2.1
                          have p128_3 := h128c.2.2.2
                          linarith only [h1, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p128_1, u2elo0]
                        · have p128_0 := h128c.1
                          have p128_1 := h128c.2.1
                          have p128_2 := h128c.2.2.1
                          have p128_3 := h128c.2.2.2
                          linarith only [h0, hlam, p128_0]
                        · have p128_0 := h128c.1
                          have p128_1 := h128c.2.1
                          have p128_2 := h128c.2.2.1
                          have p128_3 := h128c.2.2.2
                          linarith only [hlam, p128_0]
                        · have p128_0 := h128c.1
                          have p128_1 := h128c.2.1
                          have p128_2 := h128c.2.2.1
                          have p128_3 := h128c.2.2.2
                          linarith only [h0, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p128_1]
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
                          linarith only [h1, hlam, p128_0]
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
                          linarith only [h1, h3, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p128_1, u2elo0]
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
                          linarith only [h1, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p128_1, u2elo0]
                        · have p128_0 := h128c.1
                          have p128_1 := h128c.2.1
                          have p128_2 := h128c.2.2.1
                          have p128_3 := h128c.2.2.2
                          linarith only [h1, h4, h6, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p128_1, u2elo0]
                        · have p128_0 := h128c.1
                          have p128_1 := h128c.2.1
                          have p128_2 := h128c.2.2.1
                          have p128_3 := h128c.2.2.2
                          linarith only [hlam, p128_0]
            · linarith only [h1, h5, hc12, hlam, hphi, u2elo0]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h155 | h155
            · rcases m.htr 1 3 4 (by decide) (by decide) with h156 | h156
              · rcases m.htr 1 3 5 (by decide) (by decide) with h157 | h157
                · linarith only [h157, h4, hc13, hlam, hphi, ht01, u0ehi2]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h159 | h159
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h160 | h160
                    · linarith only [h1, h160, h3, h4, hlam, hphi, ht01, ht12, u0ehi3, u2elo0]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h162 | h162
                      · linarith only [h1, h159, h162, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0]
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
                          linarith only [h162, h4, hc13, hc45, hlam, hphi, ht34, p164_1]
                        · have p164_0 := h164c.1
                          have p164_1 := h164c.2.1
                          have p164_2 := h164c.2.2.1
                          have p164_3 := h164c.2.2.2
                          linarith only [h162, h4, hc23, hc45, hlam, hphi, ht34, p164_1]
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
                          linarith only [h0, hlam, p164_0]
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
                          linarith only [h0, h162, h4, hc34, hc45, hlam, hphi, p164_1]
                        · have p164_0 := h164c.1
                          have p164_1 := h164c.2.1
                          have p164_2 := h164c.2.2.1
                          have p164_3 := h164c.2.2.2
                          linarith only [h157, hlam, p164_0]
                        · have p164_0 := h164c.1
                          have p164_1 := h164c.2.1
                          have p164_2 := h164c.2.2.1
                          have p164_3 := h164c.2.2.2
                          linarith only [h1, hlam, p164_0]
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
                          linarith only [h1, h162, h3, h4, hc02, hc34, hc45, hlam, hphi, p164_1, u0ehi3]
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
                          linarith only [h162, h3, hc45, hlam, hphi, ht01, ht12, ht23, ht34, p164_1, u0ehi3]
                        · have p164_0 := h164c.1
                          have p164_1 := h164c.2.1
                          have p164_2 := h164c.2.2.1
                          have p164_3 := h164c.2.2.2
                          linarith only [h162, hc13, hc45, hlam, hphi, ht34, p164_1]
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
            · linarith only [h1, h155, hc12, hlam, hphi, u2elo0]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h193 | h193
          · rcases m.htr 1 2 3 (by decide) (by decide) with h194 | h194
            · rcases m.htr 1 3 4 (by decide) (by decide) with h195 | h195
              · linarith only [h195, h3, hc13, hlam, hphi, ht01, u0ehi2]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h197 | h197
                · rcases m.htr 2 3 4 (by decide) (by decide) with h198 | h198
                  · linarith only [h1, h193, h198, h3, hlam, hphi, ht01, ht12, u0ehi4, u2elo0]
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
                          linarith only [h3, hc13, hc34, hlam, hphi, p202_1]
                        · have p202_0 := h202c.1
                          have p202_1 := h202c.2.1
                          have p202_2 := h202c.2.2.1
                          have p202_3 := h202c.2.2.2
                          linarith only [h3, hc23, hc34, hlam, hphi, p202_1]
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
                          linarith only [h0, hlam, p202_0]
                        · have p202_0 := h202c.1
                          have p202_1 := h202c.2.1
                          have p202_2 := h202c.2.2.1
                          have p202_3 := h202c.2.2.2
                          linarith only [hlam, p202_0]
                        · have p202_0 := h202c.1
                          have p202_1 := h202c.2.1
                          have p202_2 := h202c.2.2.1
                          have p202_3 := h202c.2.2.2
                          linarith only [h0, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p202_1]
                        · have p202_0 := h202c.1
                          have p202_1 := h202c.2.1
                          have p202_2 := h202c.2.2.1
                          have p202_3 := h202c.2.2.2
                          linarith only [h195, hlam, p202_0]
                        · have p202_0 := h202c.1
                          have p202_1 := h202c.2.1
                          have p202_2 := h202c.2.2.1
                          have p202_3 := h202c.2.2.2
                          linarith only [h0, h2, h201, h3, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p202_1, u2elo0]
                        · have p202_0 := h202c.1
                          have p202_1 := h202c.2.1
                          have p202_2 := h202c.2.2.1
                          have p202_3 := h202c.2.2.2
                          linarith only [h1, hlam, p202_0]
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
                          linarith only [h194, hc23, hc34, hlam, hphi, p202_1]
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
                      · linarith only [h193, h201, h3, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi4]
                    · linarith only [h193, h200, h3, hc23, hc34, hlam, hphi]
                · linarith only [h193, h197, h3, hc13, hc34, hlam, hphi]
            · linarith only [h1, h194, hc12, hlam, hphi, u2elo0]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h234 | h234
            · rcases m.htr 1 3 4 (by decide) (by decide) with h235 | h235
              · linarith only [h235, h3, hc13, hlam, hphi, ht01, u0ehi2]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h237 | h237
                · linarith only [h0, h193, h237, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h239 | h239
                  · linarith only [h1, h239, h3, hlam, hphi, ht01, ht12, u0ehi2, u2elo0]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h241 | h241
                    · linarith only [h193, h2, h239, h241, hlam, hphi, ht01, ht12, u0ehi2, u2elo0]
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
                          linarith only [h0, hlam, p244_0]
                        · have p244_0 := h244c.1
                          have p244_1 := h244c.2.1
                          have p244_2 := h244c.2.2.1
                          have p244_3 := h244c.2.2.2
                          linarith only [hlam, p244_0]
                        · have p244_0 := h244c.1
                          have p244_1 := h244c.2.1
                          have p244_2 := h244c.2.2.1
                          have p244_3 := h244c.2.2.2
                          linarith only [h0, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p244_1]
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
                          linarith only [h1, hlam, p244_0]
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
                          linarith only [h193, hc34, hlam, hphi, ht01, ht12, ht23, p244_1, u0ehi2]
                        · have p244_0 := h244c.1
                          have p244_1 := h244c.2.1
                          have p244_2 := h244c.2.2.1
                          have p244_3 := h244c.2.2.2
                          linarith only [hc35, hlam, hphi, ht01, ht12, ht23, p244_1, u0ehi2]
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
                      · linarith only [h243, h3, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi2]
            · linarith only [h1, h234, hc12, hlam, hphi, u2elo0]
      · linarith only [h2, hlam, hphi, ht01, ht12, u0ehi1, u2elo3]
    · linarith only [h1, hlam, hphi, ht01, ht12, u0ehi1, u2elo2]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h274 | h274
    · rcases m.htr 0 2 4 (by decide) (by decide) with h275 | h275
      · rcases m.htr 0 3 4 (by decide) (by decide) with h276 | h276
        · rcases m.htr 0 3 5 (by decide) (by decide) with h277 | h277
          · rcases m.htr 1 2 3 (by decide) (by decide) with h278 | h278
            · linarith only [h0, h278, hlam, hphi, ht01, ht12, u0ehi0, u2elo1]
            · linarith only [h274, h278, hc12, hlam, hphi, u2elo0]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h281 | h281
            · linarith only [h0, h281, hlam, hphi, ht01, ht12, u0ehi0, u2elo1]
            · linarith only [h274, h281, hc12, hlam, hphi, u2elo0]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h284 | h284
          · rcases m.htr 1 2 3 (by decide) (by decide) with h285 | h285
            · linarith only [h0, h285, hlam, hphi, ht01, ht12, u0ehi0, u2elo1]
            · linarith only [h274, h285, hc12, hlam, hphi, u2elo0]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h288 | h288
            · linarith only [h0, h288, hlam, hphi, ht01, ht12, u0ehi0, u2elo1]
            · linarith only [h274, h288, hc12, hlam, hphi, u2elo0]
      · linarith only [h275, hlam, hphi, ht01, ht12, u0ehi1, u2elo3]
    · linarith only [h274, hlam, hphi, ht01, ht12, u0ehi1, u2elo2]

theorem r1l7_11_12_14_25_L_I_L_0_L_0_H_L (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
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
  have h1bigk := hb1.1
  have h2elo := hb2.1
  have h4elo := hb4.1
  have h5elo := hb5.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 2 3 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 3 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 2 3 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 2 4 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 2 5 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h10 | h10
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h11 | h11
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h12 | h12
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h13 | h13
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h14 | h14
                              · linarith only [h0, h12, h14, h6, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0]
                              · linarith only [h14, hc34, hlam, hphi, ht45, u5elo4]
                            · linarith only [h13, hc23, hlam, hphi, ht34, ht45, u5elo3]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h18 | h18
                            · linarith only [h1, h12, h18, h4, h9, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0]
                            · linarith only [h18, hc23, hlam, hphi, ht34, ht45, u5elo3]
                        · linarith only [h11, hc14, hlam, hphi, ht45, u5elo4]
                      · linarith only [h10, hc13, hlam, hphi, ht34, ht45, u5elo3]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h23 | h23
                      · linarith only [h23, h4, h5, h9, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0]
                      · linarith only [h23, h6, hc23, hlam, hphi, ht34, ht45, u5elo3]
                  · linarith only [h8, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                · linarith only [h6, h7, hc23, hlam, hphi, ht34, u4elo2]
              · linarith only [h4, h6, hc12, hlam, hphi, u2elo0]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h29 | h29
              · rcases m.htr 1 2 4 (by decide) (by decide) with h30 | h30
                · rcases m.htr 1 2 5 (by decide) (by decide) with h31 | h31
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h32 | h32
                    · linarith only [h1, h32, h5, hlam]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h34 | h34
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h35 | h35
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h36 | h36
                          · linarith only [h1, h29, h34, h36, h5, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h38 | h38
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h39 | h39
                              · rcases h1bigk with h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c
                                · have p40_0 := h40c.1
                                  have p40_1 := h40c.2.1
                                  have p40_2 := h40c.2.2.1
                                  have p40_3 := h40c.2.2.2
                                  linarith only [hlam, p40_0]
                                · have p40_0 := h40c.1
                                  have p40_1 := h40c.2.1
                                  have p40_2 := h40c.2.2.1
                                  have p40_3 := h40c.2.2.2
                                  linarith only [h29, h38, h39, hc01, hc45, hlam, hphi, ht0b, ht5b, p40_1]
                                · have p40_0 := h40c.1
                                  have p40_1 := h40c.2.1
                                  have p40_2 := h40c.2.2.1
                                  have p40_3 := h40c.2.2.2
                                  rcases p40_3 (m.d 0 1) (by simp) with h43 | h43
                                  · rcases p40_3 (m.d 1 2) (by simp) with h44 | h44
                                    · linarith only [h0, h44, hlam]
                                    · linarith only [h29, h44, hlam]
                                  · linarith only [h43, hlam, p40_0]
                                · have p40_0 := h40c.1
                                  have p40_1 := h40c.2.1
                                  have p40_2 := h40c.2.2.1
                                  have p40_3 := h40c.2.2.2
                                  rcases p40_3 (m.d 0 1) (by simp) with h48 | h48
                                  · rcases p40_3 (m.d 1 2) (by simp) with h49 | h49
                                    · linarith only [h0, h49, hlam]
                                    · linarith only [h30, h49, hlam]
                                  · linarith only [h48, hlam, p40_0]
                                · have p40_0 := h40c.1
                                  have p40_1 := h40c.2.1
                                  have p40_2 := h40c.2.2.1
                                  have p40_3 := h40c.2.2.2
                                  rcases p40_3 (m.d 0 1) (by simp) with h53 | h53
                                  · rcases p40_3 (m.d 1 2) (by simp) with h54 | h54
                                    · linarith only [h0, h54, hlam]
                                    · linarith only [h31, h54, hlam]
                                  · linarith only [h53, hlam, p40_0]
                                · have p40_0 := h40c.1
                                  have p40_1 := h40c.2.1
                                  have p40_2 := h40c.2.2.1
                                  have p40_3 := h40c.2.2.2
                                  linarith only [h0, hlam, p40_0]
                                · have p40_0 := h40c.1
                                  have p40_1 := h40c.2.1
                                  have p40_2 := h40c.2.2.1
                                  have p40_3 := h40c.2.2.2
                                  linarith only [hlam, p40_0]
                                · have p40_0 := h40c.1
                                  have p40_1 := h40c.2.1
                                  have p40_2 := h40c.2.2.1
                                  have p40_3 := h40c.2.2.2
                                  linarith only [h29, h38, h39, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p40_1, u2elo1]
                                · have p40_0 := h40c.1
                                  have p40_1 := h40c.2.1
                                  have p40_2 := h40c.2.2.1
                                  have p40_3 := h40c.2.2.2
                                  linarith only [h0, h29, h32, h38, h39, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p40_1, u2elo0]
                                · have p40_0 := h40c.1
                                  have p40_1 := h40c.2.1
                                  have p40_2 := h40c.2.2.1
                                  have p40_3 := h40c.2.2.2
                                  rcases p40_3 (m.d 0 1) (by simp) with h62 | h62
                                  · rcases p40_3 (m.d 1 2) (by simp) with h63 | h63
                                    · rcases p40_3 (m.d 1 3) (by simp) with h64 | h64
                                      · linarith only [h29, h64, hlam]
                                      · linarith only [h34, h64, hlam]
                                    · linarith only [h31, h63, hlam]
                                  · linarith only [h3, h62, hlam]
                                · have p40_0 := h40c.1
                                  have p40_1 := h40c.2.1
                                  have p40_2 := h40c.2.2.1
                                  have p40_3 := h40c.2.2.2
                                  linarith only [h1, hlam, p40_0]
                                · have p40_0 := h40c.1
                                  have p40_1 := h40c.2.1
                                  have p40_2 := h40c.2.2.1
                                  have p40_3 := h40c.2.2.2
                                  linarith only [h29, hlam, p40_0]
                                · have p40_0 := h40c.1
                                  have p40_1 := h40c.2.1
                                  have p40_2 := h40c.2.2.1
                                  have p40_3 := h40c.2.2.2
                                  linarith only [hlam, p40_0]
                                · have p40_0 := h40c.1
                                  have p40_1 := h40c.2.1
                                  have p40_2 := h40c.2.2.1
                                  have p40_3 := h40c.2.2.2
                                  linarith only [h32, hlam, p40_0]
                                · have p40_0 := h40c.1
                                  have p40_1 := h40c.2.1
                                  have p40_2 := h40c.2.2.1
                                  have p40_3 := h40c.2.2.2
                                  linarith only [h1, h31, h38, h39, h5, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p40_1, u4elo3]
                                · have p40_0 := h40c.1
                                  have p40_1 := h40c.2.1
                                  have p40_2 := h40c.2.2.1
                                  have p40_3 := h40c.2.2.2
                                  linarith only [h2, hlam, p40_0]
                                · have p40_0 := h40c.1
                                  have p40_1 := h40c.2.1
                                  have p40_2 := h40c.2.2.1
                                  have p40_3 := h40c.2.2.2
                                  linarith only [h30, hlam, p40_0]
                                · have p40_0 := h40c.1
                                  have p40_1 := h40c.2.1
                                  have p40_2 := h40c.2.2.1
                                  have p40_3 := h40c.2.2.2
                                  linarith only [hc13, hlam, hphi, ht34, p40_1, u4elo1]
                                · have p40_0 := h40c.1
                                  have p40_1 := h40c.2.1
                                  have p40_2 := h40c.2.2.1
                                  have p40_3 := h40c.2.2.2
                                  linarith only [hlam, p40_0]
                                · have p40_0 := h40c.1
                                  have p40_1 := h40c.2.1
                                  have p40_2 := h40c.2.2.1
                                  have p40_3 := h40c.2.2.2
                                  rcases p40_3 (m.d 0 1) (by simp) with h78 | h78
                                  · rcases p40_3 (m.d 1 2) (by simp) with h79 | h79
                                    · rcases p40_3 (m.d 1 3) (by simp) with h80 | h80
                                      · linarith only [h32, h80, hlam]
                                      · linarith only [h34, h80, hlam]
                                    · linarith only [h31, h79, hlam]
                                  · linarith only [h3, h78, hlam]
                                · have p40_0 := h40c.1
                                  have p40_1 := h40c.2.1
                                  have p40_2 := h40c.2.2.1
                                  have p40_3 := h40c.2.2.2
                                  linarith only [h3, hlam, p40_0]
                                · have p40_0 := h40c.1
                                  have p40_1 := h40c.2.1
                                  have p40_2 := h40c.2.2.1
                                  have p40_3 := h40c.2.2.2
                                  linarith only [h31, hlam, p40_0]
                                · have p40_0 := h40c.1
                                  have p40_1 := h40c.2.1
                                  have p40_2 := h40c.2.2.1
                                  have p40_3 := h40c.2.2.2
                                  linarith only [h34, hlam, p40_0]
                                · have p40_0 := h40c.1
                                  have p40_1 := h40c.2.1
                                  have p40_2 := h40c.2.2.1
                                  have p40_3 := h40c.2.2.2
                                  linarith only [h35, hlam, p40_0]
                                · have p40_0 := h40c.1
                                  have p40_1 := h40c.2.1
                                  have p40_2 := h40c.2.2.1
                                  have p40_3 := h40c.2.2.2
                                  linarith only [hlam, p40_0]
                              · linarith only [h39, h5, hc03, hlam, hphi, ht34, u4elo4]
                            · linarith only [h1, h34, h38, h5, hc23, hc34, hlam, hphi]
                        · linarith only [h1, h34, h35, h5, hc14, hc35, hlam, hphi, u4elo3, u5elo4]
                      · linarith only [h34, hc13, hlam, hphi, ht34, ht45, u5elo3]
                  · linarith only [h31, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                · linarith only [h29, h30, hc23, hlam, hphi, ht34, u4elo2]
              · linarith only [h29, h4, hc12, hlam, hphi, u2elo0]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h97 | h97
            · rcases m.htr 1 2 3 (by decide) (by decide) with h98 | h98
              · linarith only [h4, h98, hc02, hlam, hphi, u2elo1]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h100 | h100
                · rcases m.htr 1 2 5 (by decide) (by decide) with h101 | h101
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h102 | h102
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h103 | h103
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h104 | h104
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h105 | h105
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h106 | h106
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h107 | h107
                              · linarith only [h0, h100, h105, h107, h4, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                              · linarith only [h104, h107, hc34, hlam, hphi, u4elo1]
                            · linarith only [h106, h4, hc02, hlam, hphi, ht23, ht34, ht45, u5elo3]
                          · linarith only [h0, h100, h105, h4, hc24, hlam, hphi, u4elo3]
                        · linarith only [h104, hc14, hlam, hphi, ht45, u5elo4]
                      · linarith only [h100, h103, h98, hc24, hlam, hphi, ht45, u5elo3]
                    · linarith only [h100, h102, h98, hc24, hlam, hphi, u4elo3]
                  · linarith only [h100, h101, hc24, hlam, hphi, ht45, u5elo2]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h116 | h116
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h117 | h117
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h118 | h118
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h119 | h119
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h120 | h120
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h121 | h121
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h122 | h122
                              · rcases h1bigk with h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c
                                · have p123_0 := h123c.1
                                  have p123_1 := h123c.2.1
                                  have p123_2 := h123c.2.2.1
                                  have p123_3 := h123c.2.2.2
                                  linarith only [hlam, p123_0]
                                · have p123_0 := h123c.1
                                  have p123_1 := h123c.2.1
                                  have p123_2 := h123c.2.2.1
                                  have p123_3 := h123c.2.2.2
                                  rcases p123_3 (m.d 0 1) (by simp) with h125 | h125
                                  · rcases p123_3 (m.d 1 2) (by simp) with h126 | h126
                                    · linarith only [h126, hlam, p123_0]
                                    · rcases p123_3 (m.d 1 3) (by simp) with h128 | h128
                                      · linarith only [h1, h128, hlam]
                                      · linarith only [h128, h98, hlam]
                                  · linarith only [h125, hlam, p123_0]
                                · have p123_0 := h123c.1
                                  have p123_1 := h123c.2.1
                                  have p123_2 := h123c.2.2.1
                                  have p123_3 := h123c.2.2.2
                                  linarith only [h117, h122, hc01, hc45, hlam, hphi, ht0b, ht5b, p123_1]
                                · have p123_0 := h123c.1
                                  have p123_1 := h123c.2.1
                                  have p123_2 := h123c.2.2.1
                                  have p123_3 := h123c.2.2.2
                                  rcases p123_3 (m.d 0 1) (by simp) with h133 | h133
                                  · rcases p123_3 (m.d 1 2) (by simp) with h134 | h134
                                    · linarith only [h0, h134, hlam]
                                    · rcases p123_3 (m.d 1 3) (by simp) with h136 | h136
                                      · linarith only [h1, h136, hlam]
                                      · linarith only [h117, h136, hlam]
                                  · linarith only [h133, hlam, p123_0]
                                · have p123_0 := h123c.1
                                  have p123_1 := h123c.2.1
                                  have p123_2 := h123c.2.2.1
                                  have p123_3 := h123c.2.2.2
                                  rcases p123_3 (m.d 0 1) (by simp) with h140 | h140
                                  · rcases p123_3 (m.d 1 2) (by simp) with h141 | h141
                                    · linarith only [h0, h141, hlam]
                                    · linarith only [h116, h141, hlam]
                                  · linarith only [h140, hlam, p123_0]
                                · have p123_0 := h123c.1
                                  have p123_1 := h123c.2.1
                                  have p123_2 := h123c.2.2.1
                                  have p123_3 := h123c.2.2.2
                                  linarith only [h0, hlam, p123_0]
                                · have p123_0 := h123c.1
                                  have p123_1 := h123c.2.1
                                  have p123_2 := h123c.2.2.1
                                  have p123_3 := h123c.2.2.2
                                  linarith only [hlam, p123_0]
                                · have p123_0 := h123c.1
                                  have p123_1 := h123c.2.1
                                  have p123_2 := h123c.2.2.1
                                  have p123_3 := h123c.2.2.2
                                  linarith only [h98, hlam, p123_1]
                                · have p123_0 := h123c.1
                                  have p123_1 := h123c.2.1
                                  have p123_2 := h123c.2.2.1
                                  have p123_3 := h123c.2.2.2
                                  linarith only [h100, hlam, p123_1]
                                · have p123_0 := h123c.1
                                  have p123_1 := h123c.2.1
                                  have p123_2 := h123c.2.2.1
                                  have p123_3 := h123c.2.2.2
                                  linarith only [h100, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p123_1, u4elo2]
                                · have p123_0 := h123c.1
                                  have p123_1 := h123c.2.1
                                  have p123_2 := h123c.2.2.1
                                  have p123_3 := h123c.2.2.2
                                  linarith only [h1, hlam, p123_0]
                                · have p123_0 := h123c.1
                                  have p123_1 := h123c.2.1
                                  have p123_2 := h123c.2.2.1
                                  have p123_3 := h123c.2.2.2
                                  linarith only [h1, h116, hc01, hc25, hlam, hphi, ht0b, ht5b, p123_1]
                                · have p123_0 := h123c.1
                                  have p123_1 := h123c.2.1
                                  have p123_2 := h123c.2.2.1
                                  have p123_3 := h123c.2.2.2
                                  linarith only [hlam, p123_0]
                                · have p123_0 := h123c.1
                                  have p123_1 := h123c.2.1
                                  have p123_2 := h123c.2.2.1
                                  have p123_3 := h123c.2.2.2
                                  linarith only [h1, h100, h116, h121, h4, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p123_1, u2elo2]
                                · have p123_0 := h123c.1
                                  have p123_1 := h123c.2.1
                                  have p123_2 := h123c.2.2.1
                                  have p123_3 := h123c.2.2.2
                                  rcases p123_3 (m.d 0 1) (by simp) with h154 | h154
                                  · rcases p123_3 (m.d 1 2) (by simp) with h155 | h155
                                    · linarith only [h155, h98, hlam]
                                    · linarith only [h116, h155, hlam]
                                  · linarith only [h154, h3, hlam]
                                · have p123_0 := h123c.1
                                  have p123_1 := h123c.2.1
                                  have p123_2 := h123c.2.2.1
                                  have p123_3 := h123c.2.2.2
                                  linarith only [h2, hlam, p123_0]
                                · have p123_0 := h123c.1
                                  have p123_1 := h123c.2.1
                                  have p123_2 := h123c.2.2.1
                                  have p123_3 := h123c.2.2.2
                                  linarith only [h116, h121, h122, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p123_1, u4elo1]
                                · have p123_0 := h123c.1
                                  have p123_1 := h123c.2.1
                                  have p123_2 := h123c.2.2.1
                                  have p123_3 := h123c.2.2.2
                                  linarith only [h117, hlam, p123_1]
                                · have p123_0 := h123c.1
                                  have p123_1 := h123c.2.1
                                  have p123_2 := h123c.2.2.1
                                  have p123_3 := h123c.2.2.2
                                  linarith only [hlam, p123_0]
                                · have p123_0 := h123c.1
                                  have p123_1 := h123c.2.1
                                  have p123_2 := h123c.2.2.1
                                  have p123_3 := h123c.2.2.2
                                  rcases p123_3 (m.d 0 1) (by simp) with h163 | h163
                                  · rcases p123_3 (m.d 1 2) (by simp) with h164 | h164
                                    · linarith only [h100, h164, hlam]
                                    · linarith only [h116, h164, hlam]
                                  · linarith only [h163, h3, hlam]
                                · have p123_0 := h123c.1
                                  have p123_1 := h123c.2.1
                                  have p123_2 := h123c.2.2.1
                                  have p123_3 := h123c.2.2.2
                                  linarith only [h3, hlam, p123_0]
                                · have p123_0 := h123c.1
                                  have p123_1 := h123c.2.1
                                  have p123_2 := h123c.2.2.1
                                  have p123_3 := h123c.2.2.2
                                  linarith only [h116, hlam, p123_0]
                                · have p123_0 := h123c.1
                                  have p123_1 := h123c.2.1
                                  have p123_2 := h123c.2.2.1
                                  have p123_3 := h123c.2.2.2
                                  linarith only [h118, hlam, p123_0]
                                · have p123_0 := h123c.1
                                  have p123_1 := h123c.2.1
                                  have p123_2 := h123c.2.2.1
                                  have p123_3 := h123c.2.2.2
                                  linarith only [h119, hlam, p123_0]
                                · have p123_0 := h123c.1
                                  have p123_1 := h123c.2.1
                                  have p123_2 := h123c.2.2.1
                                  have p123_3 := h123c.2.2.2
                                  linarith only [hlam, p123_0]
                              · linarith only [h122, hc34, hlam, hphi, ht45, u5elo4]
                            · linarith only [h121, h4, hc03, hlam, hphi, ht34, ht45, u5elo3]
                          · linarith only [h0, h116, h120, h4, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo3]
                        · linarith only [h119, hc14, hlam, hphi, ht45, u5elo4]
                      · linarith only [h118, hc13, hlam, hphi, ht34, ht45, u5elo3]
                    · linarith only [h116, h117, h4, h97, h98, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                  · linarith only [h116, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h180 | h180
              · linarith only [h0, h180, h4, hlam]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h182 | h182
                · linarith only [h0, h182, h4, h97, hc24, hlam, hphi, u4elo3]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h184 | h184
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h185 | h185
                    · linarith only [h0, h1, h184, h185, h4, h97, hc01, hc25, hlam, hphi, ht0b, ht5b]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h187 | h187
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h188 | h188
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h189 | h189
                          · linarith only [h0, h184, h189, h4, h97, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                          · linarith only [h0, h184, h189, h4, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo3]
                        · linarith only [h180, h184, h185, h188, hc25, hlam, hphi, u5elo4]
                      · linarith only [h180, h184, h187, hc25, hlam, hphi, u5elo3]
                  · linarith only [h184, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
        · linarith only [h3, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo1]
      · linarith only [h0, h2, hc12, hlam, hphi, ht23, ht34, u4elo1]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h197 | h197
      · rcases m.htr 0 1 5 (by decide) (by decide) with h198 | h198
        · rcases m.htr 0 2 3 (by decide) (by decide) with h199 | h199
          · linarith only [h0, h1, h199, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h201 | h201
            · rcases m.htr 1 2 3 (by decide) (by decide) with h202 | h202
              · linarith only [h0, h1, h199, h202, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
              · linarith only [h0, h1, h202, hc12, hlam, hphi, u2elo2]
            · linarith only [h0, h1, h201, hc12, hlam, hphi, ht23, ht34, u4elo3]
        · linarith only [h0, h198, hc12, hlam, hphi, ht23, ht34, ht45, u5elo1]
      · linarith only [h0, h197, hc12, hlam, hphi, ht23, ht34, u4elo1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h208 | h208
    · rcases m.htr 0 1 4 (by decide) (by decide) with h209 | h209
      · rcases m.htr 0 1 5 (by decide) (by decide) with h210 | h210
        · rcases m.htr 0 2 3 (by decide) (by decide) with h211 | h211
          · rcases m.htr 0 3 4 (by decide) (by decide) with h212 | h212
            · rcases m.htr 1 2 3 (by decide) (by decide) with h213 | h213
              · rcases m.htr 1 2 4 (by decide) (by decide) with h214 | h214
                · rcases m.htr 1 2 5 (by decide) (by decide) with h215 | h215
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h216 | h216
                    · linarith only [h0, h208, h216, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                    · linarith only [h0, h208, h212, h213, h216, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                  · linarith only [h0, h215, hc01, hlam, hphi, ht12, u2elo4]
                · linarith only [h0, h208, h213, h214, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
              · linarith only [h0, h208, h213, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h222 | h222
              · rcases m.htr 1 2 4 (by decide) (by decide) with h223 | h223
                · rcases m.htr 1 2 5 (by decide) (by decide) with h224 | h224
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h225 | h225
                    · linarith only [h0, h208, h212, h225, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h227 | h227
                      · linarith only [h0, h208, h227, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                      · linarith only [h222, h227, hc23, hlam, hphi, ht34, ht45, u5elo3]
                  · linarith only [h0, h208, h222, h224, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                · linarith only [h0, h208, h222, h223, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
              · linarith only [h0, h222, hc01, hlam, hphi, ht12, u2elo2]
          · linarith only [h0, h208, h211, hlam]
        · linarith only [h208, h210, hc13, hlam, hphi, ht34, ht45, u5elo1]
      · linarith only [h208, h209, hc13, hlam, hphi, ht34, u4elo1]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h236 | h236
      · rcases m.htr 0 1 5 (by decide) (by decide) with h237 | h237
        · rcases m.htr 0 2 3 (by decide) (by decide) with h238 | h238
          · rcases m.htr 0 3 4 (by decide) (by decide) with h239 | h239
            · rcases m.htr 1 2 3 (by decide) (by decide) with h240 | h240
              · rcases m.htr 1 2 4 (by decide) (by decide) with h241 | h241
                · rcases m.htr 1 2 5 (by decide) (by decide) with h242 | h242
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h243 | h243
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h244 | h244
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h245 | h245
                        · linarith only [h208, h236, h240, h245, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                        · linarith only [h245, hc14, hlam, hphi, ht45, u5elo4]
                      · linarith only [h208, h244, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                    · linarith only [h208, h236, h241, h243, hc24, hlam, hphi, u4elo3]
                  · linarith only [h208, h236, h240, h241, h242, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4]
                · linarith only [h208, h240, h241, hc01, hlam, hphi, ht12, u2elo3]
              · linarith only [h238, h240, hc12, hlam, hphi, u2elo0]
            · linarith only [h208, h236, h239, hc14, hlam, hphi, u4elo3]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h254 | h254
            · rcases m.htr 1 2 3 (by decide) (by decide) with h255 | h255
              · linarith only [h238, h255, hc02, hlam, hphi, u2elo1]
              · linarith only [h0, h236, h255, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
            · linarith only [h0, h236, h238, h254, hc14, hlam, hphi, u4elo3]
        · linarith only [h236, h237, hc14, hlam, hphi, ht45, u5elo1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h260 | h260
        · rcases m.htr 0 2 3 (by decide) (by decide) with h261 | h261
          · rcases m.htr 0 3 4 (by decide) (by decide) with h262 | h262
            · rcases m.htr 1 2 3 (by decide) (by decide) with h263 | h263
              · rcases m.htr 1 2 4 (by decide) (by decide) with h264 | h264
                · rcases m.htr 1 2 5 (by decide) (by decide) with h265 | h265
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h266 | h266
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h267 | h267
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h268 | h268
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h269 | h269
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h270 | h270
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h271 | h271
                              · linarith only [h261, h269, h271, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0]
                              · linarith only [h236, h260, h265, h271, hc25, hc34, hlam, hphi, u4elo1, u5elo4]
                            · linarith only [h236, h260, h265, h269, h270, hc25, hc34, hlam, hphi, u4elo1, u5elo3]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h275 | h275
                            · linarith only [h0, h261, h262, h269, h275, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                            · linarith only [h236, h260, h265, h275, hc23, hc25, hlam, hphi, ht34, u4elo1, u5elo3]
                        · linarith only [h236, h260, h265, h268, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo4]
                      · linarith only [h208, h236, h260, h265, h267, hc03, hc25, hlam, hphi, ht34, u4elo1, u5elo3]
                    · linarith only [h208, h260, h265, h266, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo3]
                  · linarith only [h0, h265, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
                · linarith only [h208, h260, h263, h264, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3]
              · linarith only [h0, h260, h263, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h284 | h284
              · rcases m.htr 1 2 4 (by decide) (by decide) with h285 | h285
                · rcases m.htr 1 2 5 (by decide) (by decide) with h286 | h286
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h287 | h287
                    · linarith only [h208, h260, h262, h284, h286, h287, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                    · linarith only [h208, h260, h286, h287, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo3]
                  · linarith only [h286, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                · linarith only [h208, h260, h284, h285, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3]
              · linarith only [h261, h284, hc12, hlam, hphi, u2elo0]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h293 | h293
            · rcases m.htr 1 2 3 (by decide) (by decide) with h294 | h294
              · linarith only [h261, h294, hc02, hlam, hphi, u2elo1]
              · linarith only [h0, h260, h294, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h297 | h297
              · linarith only [h0, h260, h261, h297, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
              · linarith only [h0, h260, h297, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
        · linarith only [h260, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo1]

theorem r1l7_11_12_14_25_L_R_L_I_L_R_H_R (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc05 := m.hcor 0 5 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
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
  have h1ehi := hb1.1
  have h2bigk := hb2.1
  have h4ehi := hb4.1
  have h5ehi := hb5.1
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 2 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 2 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 1 2 3 (by decide) (by decide) with h3 | h3
        · rcases m.htr 1 2 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 2 5 (by decide) (by decide) with h5 | h5
            · linarith only [h0, h5, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
            · linarith only [h0, h2, h4, h5, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h8 | h8
            · linarith only [h4, h8, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h10 | h10
              · linarith only [h0, h1, h10, h3, h4, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h12 | h12
                · linarith only [h0, h1, h12, h3, h4, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h14 | h14
                  · linarith only [h0, h1, h14, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                  · linarith only [h14, h3, h4, hc23, hc45, hlam, hphi, ht34]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h17 | h17
          · rcases m.htr 1 2 5 (by decide) (by decide) with h18 | h18
            · linarith only [h18, h3, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
            · linarith only [h0, h17, h18, h2, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h21 | h21
            · linarith only [h21, h3, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h23 | h23
              · rcases m.htr 2 3 5 (by decide) (by decide) with h24 | h24
                · rcases m.htr 2 4 5 (by decide) (by decide) with h25 | h25
                  · linarith only [h0, h1, h25, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                  · linarith only [h17, h25, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi1]
                · linarith only [h24, h3, hc35, hlam, hphi, ht12, ht23, u1ehi1]
              · linarith only [h23, h3, hc34, hlam, hphi, ht12, ht23, u1ehi1]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h30 | h30
        · rcases m.htr 1 2 4 (by decide) (by decide) with h31 | h31
          · rcases m.htr 1 2 5 (by decide) (by decide) with h32 | h32
            · linarith only [h0, h1, h2, h32, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h34 | h34
              · linarith only [h0, h2, h30, h34, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h36 | h36
                · linarith only [h0, h2, h31, h34, h36, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h38 | h38
                  · linarith only [h0, h2, h31, h36, h38, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                  · linarith only [h0, h2, h31, h38, hc45, hlam, hphi, u4ehi2]
          · linarith only [h1, h2, h31, hc12, hc25, hlam, hphi]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h42 | h42
          · rcases m.htr 1 2 5 (by decide) (by decide) with h43 | h43
            · linarith only [h2, h30, h43, hc02, hc23, hlam, hphi]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h45 | h45
              · rcases m.htr 2 3 5 (by decide) (by decide) with h46 | h46
                · rcases m.htr 2 4 5 (by decide) (by decide) with h47 | h47
                  · linarith only [h0, h2, h42, h46, h47, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                  · linarith only [h0, h2, h42, h45, h47, hc45, hlam, hphi, u4ehi3]
                · linarith only [h30, h42, h45, h46, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi3]
              · linarith only [h30, h42, h45, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi2]
          · linarith only [h1, h2, h42, hc25, hlam, hphi, ht12, u1ehi1]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h53 | h53
      · linarith only [h1, h53, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h55 | h55
        · rcases m.htr 1 2 4 (by decide) (by decide) with h56 | h56
          · linarith only [h0, h1, h56, hlam]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h58 | h58
            · linarith only [h0, h1, h53, h58, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi0]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h60 | h60
              · linarith only [h0, h1, h55, h60, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h62 | h62
                · linarith only [h0, h1, h55, h60, h62, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h64 | h64
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h65 | h65
                    · rcases h2bigk with h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c
                      · have p66_0 := h66c.1
                        have p66_1 := h66c.2.1
                        have p66_2 := h66c.2.2.1
                        have p66_3 := h66c.2.2.2
                        linarith only [hlam, p66_0]
                      · have p66_0 := h66c.1
                        have p66_1 := h66c.2.1
                        have p66_2 := h66c.2.2.1
                        have p66_3 := h66c.2.2.2
                        linarith only [h53, h60, h64, hc12, hc34, hlam, hphi, ht23, p66_1]
                      · have p66_0 := h66c.1
                        have p66_1 := h66c.2.1
                        have p66_2 := h66c.2.2.1
                        have p66_3 := h66c.2.2.2
                        linarith only [h53, h60, h64, hc23, hc34, hlam, hphi, p66_1]
                      · have p66_0 := h66c.1
                        have p66_1 := h66c.2.1
                        have p66_2 := h66c.2.2.1
                        have p66_3 := h66c.2.2.2
                        linarith only [h1, hlam, p66_0]
                      · have p66_0 := h66c.1
                        have p66_1 := h66c.2.1
                        have p66_2 := h66c.2.2.1
                        have p66_3 := h66c.2.2.2
                        linarith only [h53, hlam, p66_0]
                      · have p66_0 := h66c.1
                        have p66_1 := h66c.2.1
                        have p66_2 := h66c.2.2.1
                        have p66_3 := h66c.2.2.2
                        linarith only [h0, hlam, p66_1]
                      · have p66_0 := h66c.1
                        have p66_1 := h66c.2.1
                        have p66_2 := h66c.2.2.1
                        have p66_3 := h66c.2.2.2
                        linarith only [hlam, p66_0]
                      · have p66_0 := h66c.1
                        have p66_1 := h66c.2.1
                        have p66_2 := h66c.2.2.1
                        have p66_3 := h66c.2.2.2
                        linarith only [h0, h53, h60, h64, hc23, hc34, hlam, hphi, p66_1]
                      · have p66_0 := h66c.1
                        have p66_1 := h66c.2.1
                        have p66_2 := h66c.2.2.1
                        have p66_3 := h66c.2.2.2
                        linarith only [h56, hlam, p66_0]
                      · have p66_0 := h66c.1
                        have p66_1 := h66c.2.1
                        have p66_2 := h66c.2.2.1
                        have p66_3 := h66c.2.2.2
                        linarith only [h58, hlam, p66_0]
                      · have p66_0 := h66c.1
                        have p66_1 := h66c.2.1
                        have p66_2 := h66c.2.2.1
                        have p66_3 := h66c.2.2.2
                        linarith only [h0, hc23, hlam, hphi, ht12, p66_1, u1ehi1]
                      · have p66_0 := h66c.1
                        have p66_1 := h66c.2.1
                        have p66_2 := h66c.2.2.1
                        have p66_3 := h66c.2.2.2
                        linarith only [h55, hlam, p66_0]
                      · have p66_0 := h66c.1
                        have p66_1 := h66c.2.1
                        have p66_2 := h66c.2.2.1
                        have p66_3 := h66c.2.2.2
                        linarith only [hlam, p66_0]
                      · have p66_0 := h66c.1
                        have p66_1 := h66c.2.1
                        have p66_2 := h66c.2.2.1
                        have p66_3 := h66c.2.2.2
                        linarith only [h60, hlam, p66_1]
                      · have p66_0 := h66c.1
                        have p66_1 := h66c.2.1
                        have p66_2 := h66c.2.2.1
                        have p66_3 := h66c.2.2.2
                        linarith only [h62, hlam, p66_1]
                      · have p66_0 := h66c.1
                        have p66_1 := h66c.2.1
                        have p66_2 := h66c.2.2.1
                        have p66_3 := h66c.2.2.2
                        linarith only [h0, h60, hc34, hlam, hphi, ht12, ht23, p66_1, u1ehi1]
                      · have p66_0 := h66c.1
                        have p66_1 := h66c.2.1
                        have p66_2 := h66c.2.2.1
                        have p66_3 := h66c.2.2.2
                        linarith only [h55, h60, hc34, hlam, hphi, ht12, ht23, p66_1, u1ehi2]
                      · have p66_0 := h66c.1
                        have p66_1 := h66c.2.1
                        have p66_2 := h66c.2.2.1
                        have p66_3 := h66c.2.2.2
                        rcases p66_3 (m.d 0 2) (by simp) with h84 | h84
                        · linarith only [h1, h84, hlam]
                        · linarith only [h0, h55, h84, hlam]
                      · have p66_0 := h66c.1
                        have p66_1 := h66c.2.1
                        have p66_2 := h66c.2.2.1
                        have p66_3 := h66c.2.2.2
                        linarith only [hlam, p66_0]
                      · have p66_0 := h66c.1
                        have p66_1 := h66c.2.1
                        have p66_2 := h66c.2.2.1
                        have p66_3 := h66c.2.2.2
                        linarith only [h60, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p66_1, u5ehi2]
                      · have p66_0 := h66c.1
                        have p66_1 := h66c.2.1
                        have p66_2 := h66c.2.2.1
                        have p66_3 := h66c.2.2.2
                        linarith only [h0, h55, hc25, hlam, hphi, ht12, p66_1, u1ehi2]
                      · have p66_0 := h66c.1
                        have p66_1 := h66c.2.1
                        have p66_2 := h66c.2.2.1
                        have p66_3 := h66c.2.2.2
                        linarith only [h55, h62, hc35, hlam, hphi, ht12, ht23, p66_1, u1ehi2]
                      · have p66_0 := h66c.1
                        have p66_1 := h66c.2.1
                        have p66_2 := h66c.2.2.1
                        have p66_3 := h66c.2.2.2
                        rcases p66_3 (m.d 0 2) (by simp) with h91 | h91
                        · linarith only [h53, h91, hlam]
                        · linarith only [h0, h55, h91, hlam]
                      · have p66_0 := h66c.1
                        have p66_1 := h66c.2.1
                        have p66_2 := h66c.2.2.1
                        have p66_3 := h66c.2.2.2
                        linarith only [h64, hlam, p66_1]
                      · have p66_0 := h66c.1
                        have p66_1 := h66c.2.1
                        have p66_2 := h66c.2.2.1
                        have p66_3 := h66c.2.2.2
                        linarith only [hlam, p66_0]
                    · linarith only [h60, h64, h65, hlam]
                  · linarith only [h0, h1, h55, h64, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h98 | h98
          · linarith only [h0, h1, h98, hlam]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h100 | h100
            · linarith only [h100, h55, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h102 | h102
              · rcases m.htr 2 3 5 (by decide) (by decide) with h103 | h103
                · rcases m.htr 2 4 5 (by decide) (by decide) with h104 | h104
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h105 | h105
                    · linarith only [h102, h105, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                    · rcases h2bigk with h107c | h107c | h107c | h107c | h107c | h107c | h107c | h107c | h107c | h107c | h107c | h107c | h107c | h107c | h107c | h107c | h107c | h107c | h107c | h107c | h107c | h107c | h107c | h107c | h107c
                      · have p107_0 := h107c.1
                        have p107_1 := h107c.2.1
                        have p107_2 := h107c.2.2.1
                        have p107_3 := h107c.2.2.2
                        linarith only [hlam, p107_0]
                      · have p107_0 := h107c.1
                        have p107_1 := h107c.2.1
                        have p107_2 := h107c.2.2.1
                        have p107_3 := h107c.2.2.2
                        linarith only [h53, hc12, hc25, hlam, hphi, p107_1]
                      · have p107_0 := h107c.1
                        have p107_1 := h107c.2.1
                        have p107_2 := h107c.2.2.1
                        have p107_3 := h107c.2.2.2
                        linarith only [h104, h53, h55, hc24, hlam, hphi, ht12, p107_1, u1ehi1]
                      · have p107_0 := h107c.1
                        have p107_1 := h107c.2.1
                        have p107_2 := h107c.2.2.1
                        have p107_3 := h107c.2.2.2
                        linarith only [h1, hlam, p107_0]
                      · have p107_0 := h107c.1
                        have p107_1 := h107c.2.1
                        have p107_2 := h107c.2.2.1
                        have p107_3 := h107c.2.2.2
                        linarith only [h53, hlam, p107_0]
                      · have p107_0 := h107c.1
                        have p107_1 := h107c.2.1
                        have p107_2 := h107c.2.2.1
                        have p107_3 := h107c.2.2.2
                        linarith only [h0, hlam, p107_1]
                      · have p107_0 := h107c.1
                        have p107_1 := h107c.2.1
                        have p107_2 := h107c.2.2.1
                        have p107_3 := h107c.2.2.2
                        linarith only [hlam, p107_0]
                      · have p107_0 := h107c.1
                        have p107_1 := h107c.2.1
                        have p107_2 := h107c.2.2.1
                        have p107_3 := h107c.2.2.2
                        linarith only [h55, hlam, p107_0]
                      · have p107_0 := h107c.1
                        have p107_1 := h107c.2.1
                        have p107_2 := h107c.2.2.1
                        have p107_3 := h107c.2.2.2
                        linarith only [h98, hlam, p107_0]
                      · have p107_0 := h107c.1
                        have p107_1 := h107c.2.1
                        have p107_2 := h107c.2.2.1
                        have p107_3 := h107c.2.2.2
                        linarith only [h100, hlam, p107_0]
                      · have p107_0 := h107c.1
                        have p107_1 := h107c.2.1
                        have p107_2 := h107c.2.2.1
                        have p107_3 := h107c.2.2.2
                        linarith only [h0, hc23, hlam, hphi, ht12, p107_1, u1ehi1]
                      · have p107_0 := h107c.1
                        have p107_1 := h107c.2.1
                        have p107_2 := h107c.2.2.1
                        have p107_3 := h107c.2.2.2
                        linarith only [hc23, hlam, hphi, ht12, p107_1, u1ehi1]
                      · have p107_0 := h107c.1
                        have p107_1 := h107c.2.1
                        have p107_2 := h107c.2.2.1
                        have p107_3 := h107c.2.2.2
                        linarith only [hlam, p107_0]
                      · have p107_0 := h107c.1
                        have p107_1 := h107c.2.1
                        have p107_2 := h107c.2.2.1
                        have p107_3 := h107c.2.2.2
                        linarith only [h104, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p107_1, u5ehi2]
                      · have p107_0 := h107c.1
                        have p107_1 := h107c.2.1
                        have p107_2 := h107c.2.2.1
                        have p107_3 := h107c.2.2.2
                        linarith only [h0, h53, hc23, hlam, hphi, ht12, p107_1, u1ehi1]
                      · have p107_0 := h107c.1
                        have p107_1 := h107c.2.1
                        have p107_2 := h107c.2.2.1
                        have p107_3 := h107c.2.2.2
                        linarith only [h0, hc24, hlam, hphi, ht12, p107_1, u1ehi1]
                      · have p107_0 := h107c.1
                        have p107_1 := h107c.2.1
                        have p107_2 := h107c.2.2.1
                        have p107_3 := h107c.2.2.2
                        linarith only [hc24, hlam, hphi, ht12, p107_1, u1ehi1]
                      · have p107_0 := h107c.1
                        have p107_1 := h107c.2.1
                        have p107_2 := h107c.2.2.1
                        have p107_3 := h107c.2.2.2
                        linarith only [h102, hlam, p107_0]
                      · have p107_0 := h107c.1
                        have p107_1 := h107c.2.1
                        have p107_2 := h107c.2.2.1
                        have p107_3 := h107c.2.2.2
                        linarith only [hlam, p107_0]
                      · have p107_0 := h107c.1
                        have p107_1 := h107c.2.1
                        have p107_2 := h107c.2.2.1
                        have p107_3 := h107c.2.2.2
                        linarith only [h0, h102, h53, hc23, hlam, hphi, ht12, p107_1, u1ehi1]
                      · have p107_0 := h107c.1
                        have p107_1 := h107c.2.1
                        have p107_2 := h107c.2.2.1
                        have p107_3 := h107c.2.2.2
                        linarith only [h0, hc25, hlam, hphi, ht12, p107_1, u1ehi1]
                      · have p107_0 := h107c.1
                        have p107_1 := h107c.2.1
                        have p107_2 := h107c.2.2.1
                        have p107_3 := h107c.2.2.2
                        linarith only [hc25, hlam, hphi, ht12, p107_1, u1ehi1]
                      · have p107_0 := h107c.1
                        have p107_1 := h107c.2.1
                        have p107_2 := h107c.2.2.1
                        have p107_3 := h107c.2.2.2
                        linarith only [h103, hlam, p107_0]
                      · have p107_0 := h107c.1
                        have p107_1 := h107c.2.1
                        have p107_2 := h107c.2.2.1
                        have p107_3 := h107c.2.2.2
                        linarith only [h104, hlam, p107_1]
                      · have p107_0 := h107c.1
                        have p107_1 := h107c.2.1
                        have p107_2 := h107c.2.2.1
                        have p107_3 := h107c.2.2.2
                        linarith only [hlam, p107_0]
                  · linarith only [h0, h1, h104, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi1]
                · linarith only [h103, h55, hc35, hlam, hphi, ht12, ht23, u1ehi1]
              · linarith only [h102, h55, hc34, hlam, hphi, ht12, ht23, u1ehi1]
  · rcases m.htr 0 2 4 (by decide) (by decide) with h136 | h136
    · rcases m.htr 0 2 5 (by decide) (by decide) with h137 | h137
      · rcases m.htr 1 2 3 (by decide) (by decide) with h138 | h138
        · rcases m.htr 1 2 4 (by decide) (by decide) with h139 | h139
          · rcases m.htr 1 2 5 (by decide) (by decide) with h140 | h140
            · rcases m.htr 2 3 4 (by decide) (by decide) with h141 | h141
              · rcases m.htr 2 3 5 (by decide) (by decide) with h142 | h142
                · linarith only [h138, h142, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h144 | h144
                  · linarith only [h136, h144, hc02, hlam, hphi, ht0b, ht5b, u5ehi4]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h146 | h146
                    · linarith only [h137, h141, h142, h144, h146, hc05, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                    · linarith only [h141, h142, h146, hc45, hlam, hphi, u4ehi3]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h149 | h149
                · linarith only [h141, h149, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h151 | h151
                  · linarith only [h0, h136, h151, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h153 | h153
                    · rcases h2bigk with h154c | h154c | h154c | h154c | h154c | h154c | h154c | h154c | h154c | h154c | h154c | h154c | h154c | h154c | h154c | h154c | h154c | h154c | h154c | h154c | h154c | h154c | h154c | h154c | h154c
                      · have p154_0 := h154c.1
                        have p154_1 := h154c.2.1
                        have p154_2 := h154c.2.2.1
                        have p154_3 := h154c.2.2.2
                        linarith only [hlam, p154_0]
                      · have p154_0 := h154c.1
                        have p154_1 := h154c.2.1
                        have p154_2 := h154c.2.2.1
                        have p154_3 := h154c.2.2.2
                        linarith only [h0, hlam, p154_0]
                      · have p154_0 := h154c.1
                        have p154_1 := h154c.2.1
                        have p154_2 := h154c.2.2.1
                        have p154_3 := h154c.2.2.2
                        rcases p154_3 (m.d 0 2) (by simp) with h157 | h157
                        · rcases p154_3 (m.d 1 2) (by simp) with h158 | h158
                          · rcases p154_3 (m.d 2 3) (by simp) with h159 | h159
                            · linarith only [h159, hlam, p154_0]
                            · rcases p154_3 (m.d 2 4) (by simp) with h161 | h161
                              · linarith only [h136, h161, hlam]
                              · linarith only [h141, h161, hlam]
                          · linarith only [h138, h158, hlam]
                        · linarith only [h157, hlam, p154_0]
                      · have p154_0 := h154c.1
                        have p154_1 := h154c.2.1
                        have p154_2 := h154c.2.2.1
                        have p154_3 := h154c.2.2.2
                        rcases p154_3 (m.d 0 2) (by simp) with h166 | h166
                        · rcases p154_3 (m.d 1 2) (by simp) with h167 | h167
                          · rcases p154_3 (m.d 2 3) (by simp) with h168 | h168
                            · linarith only [h137, h141, h151, h153, h168, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi0]
                            · rcases p154_3 (m.d 2 4) (by simp) with h170 | h170
                              · linarith only [h170, hlam, p154_0]
                              · rcases p154_3 (m.d 2 5) (by simp) with h172 | h172
                                · linarith only [h137, h172, hlam]
                                · linarith only [h151, h172, hlam]
                          · linarith only [h139, h167, hlam]
                        · linarith only [h166, hlam, p154_0]
                      · have p154_0 := h154c.1
                        have p154_1 := h154c.2.1
                        have p154_2 := h154c.2.2.1
                        have p154_3 := h154c.2.2.2
                        linarith only [hc02, hlam, hphi, ht0b, ht5b, p154_1, u5ehi2]
                      · have p154_0 := h154c.1
                        have p154_1 := h154c.2.1
                        have p154_2 := h154c.2.2.1
                        have p154_3 := h154c.2.2.2
                        linarith only [h0, hc12, hlam, hphi, p154_1, u1ehi0]
                      · have p154_0 := h154c.1
                        have p154_1 := h154c.2.1
                        have p154_2 := h154c.2.2.1
                        have p154_3 := h154c.2.2.2
                        linarith only [hlam, p154_0]
                      · have p154_0 := h154c.1
                        have p154_1 := h154c.2.1
                        have p154_2 := h154c.2.2.1
                        have p154_3 := h154c.2.2.2
                        rcases p154_3 (m.d 0 2) (by simp) with h180 | h180
                        · linarith only [h0, h180, hlam]
                        · linarith only [h137, h141, h151, h153, h180, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                      · have p154_0 := h154c.1
                        have p154_1 := h154c.2.1
                        have p154_2 := h154c.2.2.1
                        have p154_3 := h154c.2.2.2
                        rcases p154_3 (m.d 0 2) (by simp) with h183 | h183
                        · linarith only [h0, h183, hlam]
                        · linarith only [h136, h183, hlam]
                      · have p154_0 := h154c.1
                        have p154_1 := h154c.2.1
                        have p154_2 := h154c.2.2.1
                        have p154_3 := h154c.2.2.2
                        linarith only [hc12, hlam, hphi, ht01, ht0b, ht5b, p154_1, u5ehi2]
                      · have p154_0 := h154c.1
                        have p154_1 := h154c.2.1
                        have p154_2 := h154c.2.2.1
                        have p154_3 := h154c.2.2.2
                        linarith only [h137, h141, h151, h153, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p154_1, u5ehi2]
                      · have p154_0 := h154c.1
                        have p154_1 := h154c.2.1
                        have p154_2 := h154c.2.2.1
                        have p154_3 := h154c.2.2.2
                        linarith only [h138, hlam, p154_0]
                      · have p154_0 := h154c.1
                        have p154_1 := h154c.2.1
                        have p154_2 := h154c.2.2.1
                        have p154_3 := h154c.2.2.2
                        linarith only [hlam, p154_0]
                      · have p154_0 := h154c.1
                        have p154_1 := h154c.2.1
                        have p154_2 := h154c.2.2.1
                        have p154_3 := h154c.2.2.2
                        linarith only [h141, hlam, p154_1]
                      · have p154_0 := h154c.1
                        have p154_1 := h154c.2.1
                        have p154_2 := h154c.2.2.1
                        have p154_3 := h154c.2.2.2
                        linarith only [h149, hlam, p154_1]
                      · have p154_0 := h154c.1
                        have p154_1 := h154c.2.1
                        have p154_2 := h154c.2.2.1
                        have p154_3 := h154c.2.2.2
                        linarith only [h136, hlam, p154_0]
                      · have p154_0 := h154c.1
                        have p154_1 := h154c.2.1
                        have p154_2 := h154c.2.2.1
                        have p154_3 := h154c.2.2.2
                        linarith only [h139, hlam, p154_0]
                      · have p154_0 := h154c.1
                        have p154_1 := h154c.2.1
                        have p154_2 := h154c.2.2.1
                        have p154_3 := h154c.2.2.2
                        linarith only [h151, h153, hc23, hc34, hlam, hphi, p154_1]
                      · have p154_0 := h154c.1
                        have p154_1 := h154c.2.1
                        have p154_2 := h154c.2.2.1
                        have p154_3 := h154c.2.2.2
                        linarith only [hlam, p154_0]
                      · have p154_0 := h154c.1
                        have p154_1 := h154c.2.1
                        have p154_2 := h154c.2.2.1
                        have p154_3 := h154c.2.2.2
                        linarith only [h151, hlam, p154_0]
                      · have p154_0 := h154c.1
                        have p154_1 := h154c.2.1
                        have p154_2 := h154c.2.2.1
                        have p154_3 := h154c.2.2.2
                        linarith only [h137, hlam, p154_0]
                      · have p154_0 := h154c.1
                        have p154_1 := h154c.2.1
                        have p154_2 := h154c.2.2.1
                        have p154_3 := h154c.2.2.2
                        linarith only [h140, hlam, p154_0]
                      · have p154_0 := h154c.1
                        have p154_1 := h154c.2.1
                        have p154_2 := h154c.2.2.1
                        have p154_3 := h154c.2.2.2
                        linarith only [h151, h153, hc23, hc34, hlam, hphi, p154_1]
                      · have p154_0 := h154c.1
                        have p154_1 := h154c.2.1
                        have p154_2 := h154c.2.2.1
                        have p154_3 := h154c.2.2.2
                        linarith only [h151, h153, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p154_1, u4ehi2]
                      · have p154_0 := h154c.1
                        have p154_1 := h154c.2.1
                        have p154_2 := h154c.2.2.1
                        have p154_3 := h154c.2.2.2
                        linarith only [hlam, p154_0]
                    · rcases h2bigk with h202c | h202c | h202c | h202c | h202c | h202c | h202c | h202c | h202c | h202c | h202c | h202c | h202c | h202c | h202c | h202c | h202c | h202c | h202c | h202c | h202c | h202c | h202c | h202c | h202c
                      · have p202_0 := h202c.1
                        have p202_1 := h202c.2.1
                        have p202_2 := h202c.2.2.1
                        have p202_3 := h202c.2.2.2
                        linarith only [hlam, p202_0]
                      · have p202_0 := h202c.1
                        have p202_1 := h202c.2.1
                        have p202_2 := h202c.2.2.1
                        have p202_3 := h202c.2.2.2
                        linarith only [h0, hlam, p202_0]
                      · have p202_0 := h202c.1
                        have p202_1 := h202c.2.1
                        have p202_2 := h202c.2.2.1
                        have p202_3 := h202c.2.2.2
                        rcases p202_3 (m.d 0 2) (by simp) with h205 | h205
                        · rcases p202_3 (m.d 1 2) (by simp) with h206 | h206
                          · rcases p202_3 (m.d 2 3) (by simp) with h207 | h207
                            · linarith only [h207, hlam, p202_0]
                            · rcases p202_3 (m.d 2 4) (by simp) with h209 | h209
                              · linarith only [h136, h209, hlam]
                              · linarith only [h141, h209, hlam]
                          · linarith only [h138, h206, hlam]
                        · linarith only [h205, hlam, p202_0]
                      · have p202_0 := h202c.1
                        have p202_1 := h202c.2.1
                        have p202_2 := h202c.2.2.1
                        have p202_3 := h202c.2.2.2
                        rcases p202_3 (m.d 0 2) (by simp) with h214 | h214
                        · rcases p202_3 (m.d 1 2) (by simp) with h215 | h215
                          · rcases p202_3 (m.d 2 3) (by simp) with h216 | h216
                            · linarith only [h137, h138, h216, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                            · rcases p202_3 (m.d 2 4) (by simp) with h218 | h218
                              · linarith only [h218, hlam, p202_0]
                              · rcases p202_3 (m.d 2 5) (by simp) with h220 | h220
                                · linarith only [h137, h220, hlam]
                                · linarith only [h151, h220, hlam]
                          · linarith only [h139, h215, hlam]
                        · linarith only [h214, hlam, p202_0]
                      · have p202_0 := h202c.1
                        have p202_1 := h202c.2.1
                        have p202_2 := h202c.2.2.1
                        have p202_3 := h202c.2.2.2
                        linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht5b, p202_1, u5ehi2]
                      · have p202_0 := h202c.1
                        have p202_1 := h202c.2.1
                        have p202_2 := h202c.2.2.1
                        have p202_3 := h202c.2.2.2
                        linarith only [h0, hc12, hlam, hphi, p202_1, u1ehi0]
                      · have p202_0 := h202c.1
                        have p202_1 := h202c.2.1
                        have p202_2 := h202c.2.2.1
                        have p202_3 := h202c.2.2.2
                        linarith only [hlam, p202_0]
                      · have p202_0 := h202c.1
                        have p202_1 := h202c.2.1
                        have p202_2 := h202c.2.2.1
                        have p202_3 := h202c.2.2.2
                        rcases p202_3 (m.d 0 2) (by simp) with h228 | h228
                        · linarith only [h0, h228, hlam]
                        · linarith only [h137, h141, h153, h228, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi2]
                      · have p202_0 := h202c.1
                        have p202_1 := h202c.2.1
                        have p202_2 := h202c.2.2.1
                        have p202_3 := h202c.2.2.2
                        rcases p202_3 (m.d 0 2) (by simp) with h231 | h231
                        · linarith only [h0, h231, hlam]
                        · linarith only [h136, h231, hlam]
                      · have p202_0 := h202c.1
                        have p202_1 := h202c.2.1
                        have p202_2 := h202c.2.2.1
                        have p202_3 := h202c.2.2.2
                        linarith only [hc12, hlam, hphi, ht01, ht0b, ht5b, p202_1, u5ehi2]
                      · have p202_0 := h202c.1
                        have p202_1 := h202c.2.1
                        have p202_2 := h202c.2.2.1
                        have p202_3 := h202c.2.2.2
                        linarith only [h137, h141, h153, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p202_1, u5ehi2]
                      · have p202_0 := h202c.1
                        have p202_1 := h202c.2.1
                        have p202_2 := h202c.2.2.1
                        have p202_3 := h202c.2.2.2
                        linarith only [h138, hlam, p202_0]
                      · have p202_0 := h202c.1
                        have p202_1 := h202c.2.1
                        have p202_2 := h202c.2.2.1
                        have p202_3 := h202c.2.2.2
                        linarith only [hlam, p202_0]
                      · have p202_0 := h202c.1
                        have p202_1 := h202c.2.1
                        have p202_2 := h202c.2.2.1
                        have p202_3 := h202c.2.2.2
                        linarith only [h141, hlam, p202_1]
                      · have p202_0 := h202c.1
                        have p202_1 := h202c.2.1
                        have p202_2 := h202c.2.2.1
                        have p202_3 := h202c.2.2.2
                        linarith only [h149, hlam, p202_1]
                      · have p202_0 := h202c.1
                        have p202_1 := h202c.2.1
                        have p202_2 := h202c.2.2.1
                        have p202_3 := h202c.2.2.2
                        linarith only [h136, hlam, p202_0]
                      · have p202_0 := h202c.1
                        have p202_1 := h202c.2.1
                        have p202_2 := h202c.2.2.1
                        have p202_3 := h202c.2.2.2
                        linarith only [h139, hlam, p202_0]
                      · have p202_0 := h202c.1
                        have p202_1 := h202c.2.1
                        have p202_2 := h202c.2.2.1
                        have p202_3 := h202c.2.2.2
                        linarith only [h141, h153, hc23, hc45, hlam, hphi, ht34, p202_1]
                      · have p202_0 := h202c.1
                        have p202_1 := h202c.2.1
                        have p202_2 := h202c.2.2.1
                        have p202_3 := h202c.2.2.2
                        linarith only [hlam, p202_0]
                      · have p202_0 := h202c.1
                        have p202_1 := h202c.2.1
                        have p202_2 := h202c.2.2.1
                        have p202_3 := h202c.2.2.2
                        linarith only [h151, hlam, p202_0]
                      · have p202_0 := h202c.1
                        have p202_1 := h202c.2.1
                        have p202_2 := h202c.2.2.1
                        have p202_3 := h202c.2.2.2
                        linarith only [h137, hlam, p202_0]
                      · have p202_0 := h202c.1
                        have p202_1 := h202c.2.1
                        have p202_2 := h202c.2.2.1
                        have p202_3 := h202c.2.2.2
                        linarith only [h140, hlam, p202_0]
                      · have p202_0 := h202c.1
                        have p202_1 := h202c.2.1
                        have p202_2 := h202c.2.2.1
                        have p202_3 := h202c.2.2.2
                        rcases p202_3 (m.d 0 2) (by simp) with h247 | h247
                        · rcases p202_3 (m.d 1 2) (by simp) with h248 | h248
                          · rcases p202_3 (m.d 2 3) (by simp) with h249 | h249
                            · linarith only [h149, h249, hlam]
                            · rcases p202_3 (m.d 2 4) (by simp) with h251 | h251
                              · linarith only [h151, h251, hlam]
                              · linarith only [h141, h251, hlam]
                          · linarith only [h138, h248, hlam]
                        · linarith only [h137, h247, hlam, p202_1]
                      · have p202_0 := h202c.1
                        have p202_1 := h202c.2.1
                        have p202_2 := h202c.2.2.1
                        have p202_3 := h202c.2.2.2
                        linarith only [h137, hc02, hlam, hphi, ht0b, ht45, ht5b, p202_1, u4ehi2]
                      · have p202_0 := h202c.1
                        have p202_1 := h202c.2.1
                        have p202_2 := h202c.2.2.1
                        have p202_3 := h202c.2.2.2
                        linarith only [hlam, p202_0]
            · linarith only [h0, h137, h140, hlam]
          · linarith only [h0, h137, h139, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
        · linarith only [h0, h137, h138, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h261 | h261
        · rcases m.htr 1 2 4 (by decide) (by decide) with h262 | h262
          · rcases m.htr 1 2 5 (by decide) (by decide) with h263 | h263
            · linarith only [h136, h137, h263, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
            · linarith only [h0, h263, hc25, hlam, hphi, ht12, u1ehi0]
          · linarith only [h0, h136, h262, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi0]
        · linarith only [h0, h261, hc23, hlam, hphi, ht12, u1ehi0]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h268 | h268
      · linarith only [h136, h268, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h270 | h270
        · rcases m.htr 1 2 4 (by decide) (by decide) with h271 | h271
          · linarith only [h0, h136, h271, hc12, hlam, hphi, u1ehi0]
          · linarith only [h0, h271, hc24, hlam, hphi, ht12, u1ehi0]
        · linarith only [h0, h270, hc23, hlam, hphi, ht12, u1ehi0]

end R2N4
