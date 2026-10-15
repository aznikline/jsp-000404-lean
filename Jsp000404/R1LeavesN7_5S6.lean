import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 8910000 in
set_option maxHeartbeats 8910000 in
theorem r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s3_x0_x0_x0_x1_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h7 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h238 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
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
  have h0emin := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 0 4 5 (by decide) (by decide) with h239 | h239
  · rcases m.htr 1 2 3 (by decide) (by decide) with h240 | h240
    · rcases m.htr 1 2 4 (by decide) (by decide) with h241 | h241
      · rcases m.htr 1 2 5 (by decide) (by decide) with h242 | h242
        · rcases m.htr 1 3 4 (by decide) (by decide) with h243 | h243
          · linarith only [h1, h243, h7, hlam]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h245 | h245
            · rcases m.htr 1 4 5 (by decide) (by decide) with h246 | h246
              · rcases m.htr 2 3 4 (by decide) (by decide) with h247 | h247
                · linarith only [h0, h240, h247, h7, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h249 | h249
                  · linarith only [h0, h240, h249, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
                  · linarith only [h1, h245, h249, h7, hc23, hc34, hlam, hphi]
              · linarith only [h0, h239, h243, h245, h246, h5, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
            · linarith only [h238, h245, h7, hc13, hc34, hlam, hphi]
        · linarith only [h0, h240, h242, h6, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
      · linarith only [h0, h240, h241, h5, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
    · rcases m.htr 1 2 4 (by decide) (by decide) with h256 | h256
      · linarith only [h0, h240, h256, h4, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h258 | h258
        · linarith only [h0, h240, h258, h4, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h260 | h260
          · linarith only [h1, h260, h7, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h262 | h262
            · rcases m.htr 1 4 5 (by decide) (by decide) with h263 | h263
              · rcases m.htr 2 3 4 (by decide) (by decide) with h264 | h264
                · linarith only [h0, h264, h4, h7, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h266 | h266
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h267 | h267
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h268 | h268
                      · rcases h0bigk with h269c | h269c | h269c | h269c | h269c | h269c | h269c | h269c | h269c | h269c | h269c | h269c | h269c | h269c | h269c | h269c | h269c | h269c | h269c | h269c | h269c | h269c | h269c | h269c | h269c
                        · have p269_0 := h269c.1
                          have p269_1 := h269c.2.1
                          have p269_2 := h269c.2.2.1
                          have p269_3 := h269c.2.2.2
                          linarith only [hlam, p269_0]
                        · have p269_0 := h269c.1
                          have p269_1 := h269c.2.1
                          have p269_2 := h269c.2.2.1
                          have p269_3 := h269c.2.2.2
                          linarith only [h2, h260, h262, h268, h5, hc45, hlam, hphi, ht0b, ht5b, p269_1, u0elo0]
                        · have p269_0 := h269c.1
                          have p269_1 := h269c.2.1
                          have p269_2 := h269c.2.2.1
                          have p269_3 := h269c.2.2.2
                          linarith only [h238, h258, h6, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p269_1, u0elo0]
                        · have p269_0 := h269c.1
                          have p269_1 := h269c.2.1
                          have p269_2 := h269c.2.2.1
                          have p269_3 := h269c.2.2.2
                          linarith only [h2, h260, h262, h268, hc45, hlam, hphi, ht0b, ht5b, p269_1, u0elo0]
                        · have p269_0 := h269c.1
                          have p269_1 := h269c.2.1
                          have p269_2 := h269c.2.2.1
                          have p269_3 := h269c.2.2.2
                          linarith only [h258, h6, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p269_1, u0elo0]
                        · have p269_0 := h269c.1
                          have p269_1 := h269c.2.1
                          have p269_2 := h269c.2.2.1
                          have p269_3 := h269c.2.2.2
                          linarith only [h0, hlam, p269_0]
                        · have p269_0 := h269c.1
                          have p269_1 := h269c.2.1
                          have p269_2 := h269c.2.2.1
                          have p269_3 := h269c.2.2.2
                          linarith only [hlam, p269_0]
                        · have p269_0 := h269c.1
                          have p269_1 := h269c.2.1
                          have p269_2 := h269c.2.2.1
                          have p269_3 := h269c.2.2.2
                          linarith only [h238, h258, h6, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p269_1, u0elo1]
                        · have p269_0 := h269c.1
                          have p269_1 := h269c.2.1
                          have p269_2 := h269c.2.2.1
                          have p269_3 := h269c.2.2.2
                          linarith only [h0, h2, h260, h262, h268, hc45, hlam, hphi, ht0b, ht5b, p269_1, u0elo0]
                        · have p269_0 := h269c.1
                          have p269_1 := h269c.2.1
                          have p269_2 := h269c.2.2.1
                          have p269_3 := h269c.2.2.2
                          linarith only [h0, h258, h6, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p269_1, u0elo0]
                        · have p269_0 := h269c.1
                          have p269_1 := h269c.2.1
                          have p269_2 := h269c.2.2.1
                          have p269_3 := h269c.2.2.2
                          linarith only [h1, hlam, p269_1]
                        · have p269_0 := h269c.1
                          have p269_1 := h269c.2.1
                          have p269_2 := h269c.2.2.1
                          have p269_3 := h269c.2.2.2
                          linarith only [h4, hlam, p269_1]
                        · have p269_0 := h269c.1
                          have p269_1 := h269c.2.1
                          have p269_2 := h269c.2.2.1
                          have p269_3 := h269c.2.2.2
                          linarith only [hlam, p269_0]
                        · have p269_0 := h269c.1
                          have p269_1 := h269c.2.1
                          have p269_2 := h269c.2.2.1
                          have p269_3 := h269c.2.2.2
                          linarith only [h7, hlam, p269_1]
                        · have p269_0 := h269c.1
                          have p269_1 := h269c.2.1
                          have p269_2 := h269c.2.2.1
                          have p269_3 := h269c.2.2.2
                          linarith only [h258, h6, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p269_1, u0elo2]
                        · have p269_0 := h269c.1
                          have p269_1 := h269c.2.1
                          have p269_2 := h269c.2.2.1
                          have p269_3 := h269c.2.2.2
                          linarith only [h2, hlam, p269_0]
                        · have p269_0 := h269c.1
                          have p269_1 := h269c.2.1
                          have p269_2 := h269c.2.2.1
                          have p269_3 := h269c.2.2.2
                          linarith only [h5, hlam, p269_0]
                        · have p269_0 := h269c.1
                          have p269_1 := h269c.2.1
                          have p269_2 := h269c.2.2.1
                          have p269_3 := h269c.2.2.2
                          linarith only [h0, h1, h262, h268, h5, hc45, hlam, hphi, ht0b, ht5b, p269_1, u0elo0]
                        · have p269_0 := h269c.1
                          have p269_1 := h269c.2.1
                          have p269_2 := h269c.2.2.1
                          have p269_3 := h269c.2.2.2
                          linarith only [hlam, p269_0]
                        · have p269_0 := h269c.1
                          have p269_1 := h269c.2.1
                          have p269_2 := h269c.2.2.1
                          have p269_3 := h269c.2.2.2
                          linarith only [h0, h258, h5, h6, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p269_1, u0elo0]
                        · have p269_0 := h269c.1
                          have p269_1 := h269c.2.1
                          have p269_2 := h269c.2.2.1
                          have p269_3 := h269c.2.2.2
                          linarith only [h3, hlam, p269_0]
                        · have p269_0 := h269c.1
                          have p269_1 := h269c.2.1
                          have p269_2 := h269c.2.2.1
                          have p269_3 := h269c.2.2.2
                          linarith only [h6, hlam, p269_1]
                        · have p269_0 := h269c.1
                          have p269_1 := h269c.2.1
                          have p269_2 := h269c.2.2.1
                          have p269_3 := h269c.2.2.2
                          linarith only [h238, hlam, p269_0]
                        · have p269_0 := h269c.1
                          have p269_1 := h269c.2.1
                          have p269_2 := h269c.2.2.1
                          have p269_3 := h269c.2.2.2
                          linarith only [h239, hlam, p269_1]
                        · have p269_0 := h269c.1
                          have p269_1 := h269c.2.1
                          have p269_2 := h269c.2.2.1
                          have p269_3 := h269c.2.2.2
                          linarith only [hlam, p269_0]
                      · linarith only [h238, h258, h268, h6, h7, hc12, hc45, hlam, hphi, ht23, ht34]
                    · linarith only [h238, h256, h263, h267, h3, h7, hc12, hc34, hlam, hphi, ht23]
                  · linarith only [h0, h256, h260, h262, h266, h5, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
              · linarith only [h0, h239, h260, h262, h263, h5, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
            · linarith only [h238, h262, h7, hc13, hc34, hlam, hphi]
  · linarith only [h238, h239, h7, hlam]

end R2N4
