import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5616000 in
set_option maxHeartbeats 5616000 in
theorem r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s13_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6310 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg6311 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg6312 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg6313 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg6314 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6315 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h6316 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
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
  have h0elo := hb0.1
  have h0emin := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h6310 := hg6310
  have h6311 := hg6311
  have h6312 := hg6312
  have h6313 := hg6313
  have h6314 := hg6314
  have h6315 := hg6315
  rcases m.htr 0 3 5 (by decide) (by decide) with h6317 | h6317
  · rcases m.htr 0 4 5 (by decide) (by decide) with h6318 | h6318
    · rcases m.htr 1 2 3 (by decide) (by decide) with h6319 | h6319
      · rcases m.htr 1 2 4 (by decide) (by decide) with h6320 | h6320
        · rcases m.htr 1 2 5 (by decide) (by decide) with h6321 | h6321
          · rcases m.htr 1 3 4 (by decide) (by decide) with h6322 | h6322
            · rcases m.htr 1 3 5 (by decide) (by decide) with h6323 | h6323
              · rcases m.htr 1 4 5 (by decide) (by decide) with h6324 | h6324
                · rcases m.htr 2 3 4 (by decide) (by decide) with h6325 | h6325
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h6326 | h6326
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h6327 | h6327
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h6328 | h6328
                        · linarith only [h6310, h6319, h6325, h6328, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                        · linarith only [h0, h6310, h6322, h6324, h6328, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                      · linarith only [h0, h6310, h6322, h6324, h6327, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                    · linarith only [h0, h6310, h6323, h6326, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                  · linarith only [h0, h6310, h6322, h6325, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h6334 | h6334
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h6335 | h6335
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h6336 | h6336
                      · linarith only [h6314, h6324, h6336, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h6338 | h6338
                        · linarith only [h6320, h6324, h6334, h6338, hlam]
                        · rcases h0bigk with h6340c | h6340c | h6340c | h6340c | h6340c | h6340c | h6340c | h6340c | h6340c | h6340c | h6340c | h6340c | h6340c | h6340c | h6340c | h6340c | h6340c | h6340c | h6340c | h6340c | h6340c | h6340c | h6340c | h6340c | h6340c
                          · have p6340_0 := h6340c.1
                            have p6340_1 := h6340c.2.1
                            have p6340_2 := h6340c.2.2.1
                            have p6340_3 := h6340c.2.2.2
                            linarith only [hlam, p6340_0]
                          · have p6340_0 := h6340c.1
                            have p6340_1 := h6340c.2.1
                            have p6340_2 := h6340c.2.2.1
                            have p6340_3 := h6340c.2.2.2
                            linarith only [h0, hlam, p6340_1]
                          · have p6340_0 := h6340c.1
                            have p6340_1 := h6340c.2.1
                            have p6340_2 := h6340c.2.2.1
                            have p6340_3 := h6340c.2.2.2
                            linarith only [h0, h6313, h6335, h6338, hc34, hlam, hphi, ht0b, ht45, ht5b, p6340_1, u0elo1]
                          · have p6340_0 := h6340c.1
                            have p6340_1 := h6340c.2.1
                            have p6340_2 := h6340c.2.2.1
                            have p6340_3 := h6340c.2.2.2
                            linarith only [h0, h6318, h6320, h6324, h6334, hc34, hlam, hphi, ht0b, ht45, ht5b, p6340_1, u0elo1]
                          · have p6340_0 := h6340c.1
                            have p6340_1 := h6340c.2.1
                            have p6340_2 := h6340c.2.2.1
                            have p6340_3 := h6340c.2.2.2
                            linarith only [h0, h6318, h6320, h6324, h6334, hc34, hlam, hphi, ht0b, ht45, ht5b, p6340_1, u0elo1]
                          · have p6340_0 := h6340c.1
                            have p6340_1 := h6340c.2.1
                            have p6340_2 := h6340c.2.2.1
                            have p6340_3 := h6340c.2.2.2
                            linarith only [h6310, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p6340_1, u0elo1]
                          · have p6340_0 := h6340c.1
                            have p6340_1 := h6340c.2.1
                            have p6340_2 := h6340c.2.2.1
                            have p6340_3 := h6340c.2.2.2
                            linarith only [hlam, p6340_0]
                          · have p6340_0 := h6340c.1
                            have p6340_1 := h6340c.2.1
                            have p6340_2 := h6340c.2.2.1
                            have p6340_3 := h6340c.2.2.2
                            linarith only [h6316, h6318, h6320, h6324, h6334, hc34, hlam, hphi, ht0b, ht45, ht5b, p6340_1, u0elo1]
                          · have p6340_0 := h6340c.1
                            have p6340_1 := h6340c.2.1
                            have p6340_2 := h6340c.2.2.1
                            have p6340_3 := h6340c.2.2.2
                            linarith only [h6318, h6320, h6324, h6334, hc34, hlam, hphi, ht0b, ht45, ht5b, p6340_1, u0elo1]
                          · have p6340_0 := h6340c.1
                            have p6340_1 := h6340c.2.1
                            have p6340_2 := h6340c.2.2.1
                            have p6340_3 := h6340c.2.2.2
                            linarith only [h6318, h6320, h6324, h6334, hc34, hlam, hphi, ht0b, ht45, ht5b, p6340_1, u0elo1]
                          · have p6340_0 := h6340c.1
                            have p6340_1 := h6340c.2.1
                            have p6340_2 := h6340c.2.2.1
                            have p6340_3 := h6340c.2.2.2
                            linarith only [h6310, hlam, p6340_1]
                          · have p6340_0 := h6340c.1
                            have p6340_1 := h6340c.2.1
                            have p6340_2 := h6340c.2.2.1
                            have p6340_3 := h6340c.2.2.2
                            linarith only [h6313, hlam, p6340_1]
                          · have p6340_0 := h6340c.1
                            have p6340_1 := h6340c.2.1
                            have p6340_2 := h6340c.2.2.1
                            have p6340_3 := h6340c.2.2.2
                            linarith only [hlam, p6340_0]
                          · have p6340_0 := h6340c.1
                            have p6340_1 := h6340c.2.1
                            have p6340_2 := h6340c.2.2.1
                            have p6340_3 := h6340c.2.2.2
                            linarith only [h6310, h6318, h6320, h6324, h6334, hc34, hlam, hphi, ht0b, ht45, ht5b, p6340_1, u0elo0]
                          · have p6340_0 := h6340c.1
                            have p6340_1 := h6340c.2.1
                            have p6340_2 := h6340c.2.2.1
                            have p6340_3 := h6340c.2.2.2
                            linarith only [h0, h6310, h6318, h6320, h6324, h6334, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p6340_1]
                          · have p6340_0 := h6340c.1
                            have p6340_1 := h6340c.2.1
                            have p6340_2 := h6340c.2.2.1
                            have p6340_3 := h6340c.2.2.2
                            linarith only [h6311, hlam, p6340_0]
                          · have p6340_0 := h6340c.1
                            have p6340_1 := h6340c.2.1
                            have p6340_2 := h6340c.2.2.1
                            have p6340_3 := h6340c.2.2.2
                            linarith only [h6314, hlam, p6340_0]
                          · have p6340_0 := h6340c.1
                            have p6340_1 := h6340c.2.1
                            have p6340_2 := h6340c.2.2.1
                            have p6340_3 := h6340c.2.2.2
                            linarith only [h6316, hlam, p6340_0]
                          · have p6340_0 := h6340c.1
                            have p6340_1 := h6340c.2.1
                            have p6340_2 := h6340c.2.2.1
                            have p6340_3 := h6340c.2.2.2
                            linarith only [hlam, p6340_0]
                          · have p6340_0 := h6340c.1
                            have p6340_1 := h6340c.2.1
                            have p6340_2 := h6340c.2.2.1
                            have p6340_3 := h6340c.2.2.2
                            linarith only [h6318, h6320, h6324, h6334, hc34, hlam, hphi, ht0b, ht45, ht5b, p6340_1, u0elo3]
                          · have p6340_0 := h6340c.1
                            have p6340_1 := h6340c.2.1
                            have p6340_2 := h6340c.2.2.1
                            have p6340_3 := h6340c.2.2.2
                            linarith only [h6312, hlam, p6340_0]
                          · have p6340_0 := h6340c.1
                            have p6340_1 := h6340c.2.1
                            have p6340_2 := h6340c.2.2.1
                            have p6340_3 := h6340c.2.2.2
                            linarith only [h6315, hlam, p6340_1]
                          · have p6340_0 := h6340c.1
                            have p6340_1 := h6340c.2.1
                            have p6340_2 := h6340c.2.2.1
                            have p6340_3 := h6340c.2.2.2
                            linarith only [h6317, hlam, p6340_0]
                          · have p6340_0 := h6340c.1
                            have p6340_1 := h6340c.2.1
                            have p6340_2 := h6340c.2.2.1
                            have p6340_3 := h6340c.2.2.2
                            linarith only [h6318, hlam, p6340_1]
                          · have p6340_0 := h6340c.1
                            have p6340_1 := h6340c.2.1
                            have p6340_2 := h6340c.2.2.1
                            have p6340_3 := h6340c.2.2.2
                            linarith only [hlam, p6340_0]
                    · linarith only [h0, h6310, h6317, h6334, h6335, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                  · linarith only [h0, h6310, h6322, h6334, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
              · linarith only [h0, h6310, h6317, h6322, h6323, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h6369 | h6369
              · linarith only [h0, h6310, h6316, h6322, h6369, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h6371 | h6371
                · rcases m.htr 2 3 4 (by decide) (by decide) with h6372 | h6372
                  · linarith only [h6313, h6322, h6372, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h6374 | h6374
                    · linarith only [h6319, h6369, h6374, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h6376 | h6376
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h6377 | h6377
                        · rcases h0bigk with h6378c | h6378c | h6378c | h6378c | h6378c | h6378c | h6378c | h6378c | h6378c | h6378c | h6378c | h6378c | h6378c | h6378c | h6378c | h6378c | h6378c | h6378c | h6378c | h6378c | h6378c | h6378c | h6378c | h6378c | h6378c
                          · have p6378_0 := h6378c.1
                            have p6378_1 := h6378c.2.1
                            have p6378_2 := h6378c.2.2.1
                            have p6378_3 := h6378c.2.2.2
                            linarith only [hlam, p6378_0]
                          · have p6378_0 := h6378c.1
                            have p6378_1 := h6378c.2.1
                            have p6378_2 := h6378c.2.2.1
                            have p6378_3 := h6378c.2.2.2
                            linarith only [h0, hlam, p6378_1]
                          · have p6378_0 := h6378c.1
                            have p6378_1 := h6378c.2.1
                            have p6378_2 := h6378c.2.2.1
                            have p6378_3 := h6378c.2.2.2
                            linarith only [h0, h6311, h6316, h6320, h6376, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p6378_1]
                          · have p6378_0 := h6378c.1
                            have p6378_1 := h6378c.2.1
                            have p6378_2 := h6378c.2.2.1
                            have p6378_3 := h6378c.2.2.2
                            linarith only [h0, h6311, h6320, h6376, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p6378_1]
                          · have p6378_0 := h6378c.1
                            have p6378_1 := h6378c.2.1
                            have p6378_2 := h6378c.2.2.1
                            have p6378_3 := h6378c.2.2.2
                            linarith only [h0, h6317, h6319, h6369, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6378_1]
                          · have p6378_0 := h6378c.1
                            have p6378_1 := h6378c.2.1
                            have p6378_2 := h6378c.2.2.1
                            have p6378_3 := h6378c.2.2.2
                            linarith only [h6310, h6319, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6378_1, u0elo1]
                          · have p6378_0 := h6378c.1
                            have p6378_1 := h6378c.2.1
                            have p6378_2 := h6378c.2.2.1
                            have p6378_3 := h6378c.2.2.2
                            linarith only [hlam, p6378_0]
                          · have p6378_0 := h6378c.1
                            have p6378_1 := h6378c.2.1
                            have p6378_2 := h6378c.2.2.1
                            have p6378_3 := h6378c.2.2.2
                            linarith only [h6311, h6316, h6320, h6376, hc45, hlam, hphi, ht0b, ht5b, p6378_1, u0elo1]
                          · have p6378_0 := h6378c.1
                            have p6378_1 := h6378c.2.1
                            have p6378_2 := h6378c.2.2.1
                            have p6378_3 := h6378c.2.2.2
                            linarith only [h6311, h6320, h6376, hc45, hlam, hphi, ht0b, ht5b, p6378_1, u0elo1]
                          · have p6378_0 := h6378c.1
                            have p6378_1 := h6378c.2.1
                            have p6378_2 := h6378c.2.2.1
                            have p6378_3 := h6378c.2.2.2
                            linarith only [h6317, h6319, h6369, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6378_1, u0elo1]
                          · have p6378_0 := h6378c.1
                            have p6378_1 := h6378c.2.1
                            have p6378_2 := h6378c.2.2.1
                            have p6378_3 := h6378c.2.2.2
                            linarith only [h6310, hlam, p6378_1]
                          · have p6378_0 := h6378c.1
                            have p6378_1 := h6378c.2.1
                            have p6378_2 := h6378c.2.2.1
                            have p6378_3 := h6378c.2.2.2
                            linarith only [h6313, hlam, p6378_1]
                          · have p6378_0 := h6378c.1
                            have p6378_1 := h6378c.2.1
                            have p6378_2 := h6378c.2.2.1
                            have p6378_3 := h6378c.2.2.2
                            linarith only [hlam, p6378_0]
                          · have p6378_0 := h6378c.1
                            have p6378_1 := h6378c.2.1
                            have p6378_2 := h6378c.2.2.1
                            have p6378_3 := h6378c.2.2.2
                            linarith only [h6311, h6320, h6376, hc45, hlam, hphi, ht0b, ht5b, p6378_1, u0elo2]
                          · have p6378_0 := h6378c.1
                            have p6378_1 := h6378c.2.1
                            have p6378_2 := h6378c.2.2.1
                            have p6378_3 := h6378c.2.2.2
                            linarith only [h0, h6310, h6317, h6319, h6369, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6378_1]
                          · have p6378_0 := h6378c.1
                            have p6378_1 := h6378c.2.1
                            have p6378_2 := h6378c.2.2.1
                            have p6378_3 := h6378c.2.2.2
                            linarith only [h6311, hlam, p6378_0]
                          · have p6378_0 := h6378c.1
                            have p6378_1 := h6378c.2.1
                            have p6378_2 := h6378c.2.2.1
                            have p6378_3 := h6378c.2.2.2
                            linarith only [h6314, hlam, p6378_0]
                          · have p6378_0 := h6378c.1
                            have p6378_1 := h6378c.2.1
                            have p6378_2 := h6378c.2.2.1
                            have p6378_3 := h6378c.2.2.2
                            linarith only [h6316, hlam, p6378_0]
                          · have p6378_0 := h6378c.1
                            have p6378_1 := h6378c.2.1
                            have p6378_2 := h6378c.2.2.1
                            have p6378_3 := h6378c.2.2.2
                            linarith only [hlam, p6378_0]
                          · have p6378_0 := h6378c.1
                            have p6378_1 := h6378c.2.1
                            have p6378_2 := h6378c.2.2.1
                            have p6378_3 := h6378c.2.2.2
                            linarith only [h6317, h6319, h6369, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6378_1, u0elo3]
                          · have p6378_0 := h6378c.1
                            have p6378_1 := h6378c.2.1
                            have p6378_2 := h6378c.2.2.1
                            have p6378_3 := h6378c.2.2.2
                            linarith only [h6312, hlam, p6378_0]
                          · have p6378_0 := h6378c.1
                            have p6378_1 := h6378c.2.1
                            have p6378_2 := h6378c.2.2.1
                            have p6378_3 := h6378c.2.2.2
                            linarith only [h6315, hlam, p6378_1]
                          · have p6378_0 := h6378c.1
                            have p6378_1 := h6378c.2.1
                            have p6378_2 := h6378c.2.2.1
                            have p6378_3 := h6378c.2.2.2
                            linarith only [h6317, hlam, p6378_0]
                          · have p6378_0 := h6378c.1
                            have p6378_1 := h6378c.2.1
                            have p6378_2 := h6378c.2.2.1
                            have p6378_3 := h6378c.2.2.2
                            linarith only [h6318, hlam, p6378_1]
                          · have p6378_0 := h6378c.1
                            have p6378_1 := h6378c.2.1
                            have p6378_2 := h6378c.2.2.1
                            have p6378_3 := h6378c.2.2.2
                            linarith only [hlam, p6378_0]
                        · linarith only [h0, h6311, h6320, h6376, h6377, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · linarith only [h0, h6310, h6316, h6322, h6371, h6376, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h6406 | h6406
                  · linarith only [h0, h6310, h6317, h6319, h6369, h6406, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h6408 | h6408
                    · linarith only [h0, h6310, h6316, h6318, h6319, h6322, h6371, h6408, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h6410 | h6410
                      · linarith only [h6314, h6319, h6322, h6371, h6410, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h6412 | h6412
                        · linarith only [h0, h6310, h6316, h6319, h6322, h6371, h6412, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · linarith only [h6318, h6319, h6322, h6412, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3]
          · linarith only [h0, h6315, h6321, hlam]
        · linarith only [h0, h6314, h6320, hlam]
      · linarith only [h0, h6313, h6319, hlam]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h6418 | h6418
      · rcases m.htr 1 2 4 (by decide) (by decide) with h6419 | h6419
        · rcases m.htr 1 2 5 (by decide) (by decide) with h6420 | h6420
          · rcases m.htr 1 3 4 (by decide) (by decide) with h6421 | h6421
            · rcases m.htr 1 3 5 (by decide) (by decide) with h6422 | h6422
              · rcases m.htr 1 4 5 (by decide) (by decide) with h6423 | h6423
                · linarith only [h6311, h6318, h6423, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h6425 | h6425
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h6426 | h6426
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h6427 | h6427
                      · linarith only [h6311, h6318, h6419, h6427, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h6429 | h6429
                        · linarith only [h0, h6310, h6316, h6318, h6429, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · rcases h0bigk with h6431c | h6431c | h6431c | h6431c | h6431c | h6431c | h6431c | h6431c | h6431c | h6431c | h6431c | h6431c | h6431c | h6431c | h6431c | h6431c | h6431c | h6431c | h6431c | h6431c | h6431c | h6431c | h6431c | h6431c | h6431c
                          · have p6431_0 := h6431c.1
                            have p6431_1 := h6431c.2.1
                            have p6431_2 := h6431c.2.2.1
                            have p6431_3 := h6431c.2.2.2
                            linarith only [hlam, p6431_0]
                          · have p6431_0 := h6431c.1
                            have p6431_1 := h6431c.2.1
                            have p6431_2 := h6431c.2.2.1
                            have p6431_3 := h6431c.2.2.2
                            linarith only [h0, hlam, p6431_1]
                          · have p6431_0 := h6431c.1
                            have p6431_1 := h6431c.2.1
                            have p6431_2 := h6431c.2.2.1
                            have p6431_3 := h6431c.2.2.2
                            linarith only [h0, h6313, h6426, h6429, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p6431_1]
                          · have p6431_0 := h6431c.1
                            have p6431_1 := h6431c.2.1
                            have p6431_2 := h6431c.2.2.1
                            have p6431_3 := h6431c.2.2.2
                            rcases p6431_3 (m.d 0 1) (by simp) with h6435 | h6435
                            · rcases p6431_3 (m.d 0 2) (by simp) with h6436 | h6436
                              · rcases p6431_3 (m.d 0 3) (by simp) with h6437 | h6437
                                · linarith only [h6310, h6437, hlam]
                                · linarith only [h6316, h6437, hlam]
                              · linarith only [h6314, h6436, hlam]
                            · linarith only [h6311, h6435, hlam]
                          · have p6431_0 := h6431c.1
                            have p6431_1 := h6431c.2.1
                            have p6431_2 := h6431c.2.2.1
                            have p6431_3 := h6431c.2.2.2
                            rcases p6431_3 (m.d 0 1) (by simp) with h6442 | h6442
                            · rcases p6431_3 (m.d 0 2) (by simp) with h6443 | h6443
                              · rcases p6431_3 (m.d 0 3) (by simp) with h6444 | h6444
                                · linarith only [h6310, h6444, hlam]
                                · linarith only [h6317, h6444, hlam]
                              · linarith only [h6315, h6443, hlam]
                            · linarith only [h6312, h6442, hlam]
                          · have p6431_0 := h6431c.1
                            have p6431_1 := h6431c.2.1
                            have p6431_2 := h6431c.2.2.1
                            have p6431_3 := h6431c.2.2.2
                            linarith only [h6310, h6418, h6426, h6429, hc34, hlam, hphi, ht0b, ht45, ht5b, p6431_1, u0elo1]
                          · have p6431_0 := h6431c.1
                            have p6431_1 := h6431c.2.1
                            have p6431_2 := h6431c.2.2.1
                            have p6431_3 := h6431c.2.2.2
                            linarith only [hlam, p6431_0]
                          · have p6431_0 := h6431c.1
                            have p6431_1 := h6431c.2.1
                            have p6431_2 := h6431c.2.2.1
                            have p6431_3 := h6431c.2.2.2
                            linarith only [h6310, h6418, h6426, h6429, hc34, hlam, hphi, ht0b, ht45, ht5b, p6431_1, u0elo1]
                          · have p6431_0 := h6431c.1
                            have p6431_1 := h6431c.2.1
                            have p6431_2 := h6431c.2.2.1
                            have p6431_3 := h6431c.2.2.2
                            rcases p6431_3 (m.d 0 1) (by simp) with h6452 | h6452
                            · linarith only [h0, h6452, hlam]
                            · linarith only [h6311, h6452, hlam]
                          · have p6431_0 := h6431c.1
                            have p6431_1 := h6431c.2.1
                            have p6431_2 := h6431c.2.2.1
                            have p6431_3 := h6431c.2.2.2
                            rcases p6431_3 (m.d 0 1) (by simp) with h6455 | h6455
                            · linarith only [h0, h6455, hlam]
                            · linarith only [h6312, h6455, hlam]
                          · have p6431_0 := h6431c.1
                            have p6431_1 := h6431c.2.1
                            have p6431_2 := h6431c.2.2.1
                            have p6431_3 := h6431c.2.2.2
                            linarith only [h6310, hlam, p6431_1]
                          · have p6431_0 := h6431c.1
                            have p6431_1 := h6431c.2.1
                            have p6431_2 := h6431c.2.2.1
                            have p6431_3 := h6431c.2.2.2
                            linarith only [h6313, hlam, p6431_1]
                          · have p6431_0 := h6431c.1
                            have p6431_1 := h6431c.2.1
                            have p6431_2 := h6431c.2.2.1
                            have p6431_3 := h6431c.2.2.2
                            linarith only [hlam, p6431_0]
                          · have p6431_0 := h6431c.1
                            have p6431_1 := h6431c.2.1
                            have p6431_2 := h6431c.2.2.1
                            have p6431_3 := h6431c.2.2.2
                            rcases p6431_3 (m.d 0 1) (by simp) with h6461 | h6461
                            · rcases p6431_3 (m.d 0 2) (by simp) with h6462 | h6462
                              · rcases p6431_3 (m.d 0 3) (by simp) with h6463 | h6463
                                · rcases p6431_3 (m.d 0 4) (by simp) with h6464 | h6464
                                  · linarith only [h6316, h6464, hlam]
                                  · rcases p6431_3 (m.d 0 5) (by simp) with h6466 | h6466
                                    · linarith only [h6317, h6466, hlam]
                                    · linarith only [h6318, h6466, hlam]
                                · linarith only [h6316, h6463, hlam]
                              · linarith only [h6314, h6462, hlam]
                            · linarith only [h6311, h6461, hlam]
                          · have p6431_0 := h6431c.1
                            have p6431_1 := h6431c.2.1
                            have p6431_2 := h6431c.2.2.1
                            have p6431_3 := h6431c.2.2.2
                            rcases p6431_3 (m.d 0 1) (by simp) with h6472 | h6472
                            · rcases p6431_3 (m.d 0 2) (by simp) with h6473 | h6473
                              · rcases p6431_3 (m.d 0 3) (by simp) with h6474 | h6474
                                · rcases p6431_3 (m.d 0 4) (by simp) with h6475 | h6475
                                  · linarith only [h6316, h6475, hlam]
                                  · rcases p6431_3 (m.d 0 5) (by simp) with h6477 | h6477
                                    · linarith only [h6317, h6477, hlam]
                                    · rcases h0emin with h6479 | h6479 | h6479 | h6479 | h6479
                                      · rcases h1bigk with h6480c | h6480c | h6480c | h6480c | h6480c | h6480c | h6480c | h6480c | h6480c | h6480c | h6480c | h6480c | h6480c | h6480c | h6480c | h6480c | h6480c | h6480c | h6480c | h6480c | h6480c | h6480c | h6480c | h6480c | h6480c
                                        · have p6480_0 := h6480c.1
                                          have p6480_1 := h6480c.2.1
                                          have p6480_2 := h6480c.2.2.1
                                          have p6480_3 := h6480c.2.2.2
                                          linarith only [hlam, p6480_0]
                                        · have p6480_0 := h6480c.1
                                          have p6480_1 := h6480c.2.1
                                          have p6480_2 := h6480c.2.2.1
                                          have p6480_3 := h6480c.2.2.2
                                          linarith only [h0, hlam, p6480_0]
                                        · have p6480_0 := h6480c.1
                                          have p6480_1 := h6480c.2.1
                                          have p6480_2 := h6480c.2.2.1
                                          have p6480_3 := h6480c.2.2.2
                                          linarith only [h0, h6418, h6426, h6429, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p6480_1]
                                        · have p6480_0 := h6480c.1
                                          have p6480_1 := h6480c.2.1
                                          have p6480_2 := h6480c.2.2.1
                                          have p6480_3 := h6480c.2.2.2
                                          rcases p6480_3 (m.d 0 1) (by simp) with h6484 | h6484
                                          · rcases p6480_3 (m.d 1 2) (by simp) with h6485 | h6485
                                            · rcases p6480_3 (m.d 1 3) (by simp) with h6486 | h6486
                                              · linarith only [h6310, h6486, hlam]
                                              · linarith only [h6421, h6486, hlam]
                                            · linarith only [h6419, h6485, hlam]
                                          · linarith only [h6484, hlam, p6480_0]
                                        · have p6480_0 := h6480c.1
                                          have p6480_1 := h6480c.2.1
                                          have p6480_2 := h6480c.2.2.1
                                          have p6480_3 := h6480c.2.2.2
                                          rcases p6480_3 (m.d 0 1) (by simp) with h6491 | h6491
                                          · rcases p6480_3 (m.d 1 2) (by simp) with h6492 | h6492
                                            · rcases p6480_3 (m.d 1 3) (by simp) with h6493 | h6493
                                              · linarith only [h6310, h6493, hlam]
                                              · linarith only [h6422, h6493, hlam]
                                            · linarith only [h6420, h6492, hlam]
                                          · linarith only [h6491, hlam, p6480_0]
                                        · have p6480_0 := h6480c.1
                                          have p6480_1 := h6480c.2.1
                                          have p6480_2 := h6480c.2.2.1
                                          have p6480_3 := h6480c.2.2.2
                                          linarith only [h6479, hc12, hlam, ht01, p6480_1]
                                        · have p6480_0 := h6480c.1
                                          have p6480_1 := h6480c.2.1
                                          have p6480_2 := h6480c.2.2.1
                                          have p6480_3 := h6480c.2.2.2
                                          linarith only [hlam, p6480_0]
                                        · have p6480_0 := h6480c.1
                                          have p6480_1 := h6480c.2.1
                                          have p6480_2 := h6480c.2.2.1
                                          have p6480_3 := h6480c.2.2.2
                                          rcases p6480_3 (m.d 0 1) (by simp) with h6500 | h6500
                                          · linarith only [h0, h6500, hlam]
                                          · linarith only [h6310, h6500, hlam]
                                        · have p6480_0 := h6480c.1
                                          have p6480_1 := h6480c.2.1
                                          have p6480_2 := h6480c.2.2.1
                                          have p6480_3 := h6480c.2.2.2
                                          linarith only [h0, h6310, h6311, h6318, hlam, p6431_1, p6480_2]
                                        · have p6480_0 := h6480c.1
                                          have p6480_1 := h6480c.2.1
                                          have p6480_2 := h6480c.2.2.1
                                          have p6480_3 := h6480c.2.2.2
                                          linarith only [h0, h6310, h6312, hlam, p6431_1, p6480_2]
                                        · have p6480_0 := h6480c.1
                                          have p6480_1 := h6480c.2.1
                                          have p6480_2 := h6480c.2.2.1
                                          have p6480_3 := h6480c.2.2.2
                                          linarith only [h6310, hlam, p6480_0]
                                        · have p6480_0 := h6480c.1
                                          have p6480_1 := h6480c.2.1
                                          have p6480_2 := h6480c.2.2.1
                                          have p6480_3 := h6480c.2.2.2
                                          linarith only [h6418, hlam, p6480_1]
                                        · have p6480_0 := h6480c.1
                                          have p6480_1 := h6480c.2.1
                                          have p6480_2 := h6480c.2.2.1
                                          have p6480_3 := h6480c.2.2.2
                                          linarith only [hlam, p6480_0]
                                        · have p6480_0 := h6480c.1
                                          have p6480_1 := h6480c.2.1
                                          have p6480_2 := h6480c.2.2.1
                                          have p6480_3 := h6480c.2.2.2
                                          linarith only [h6310, h6419, h6425, hc34, hlam, hphi, ht0b, ht45, ht5b, p6480_1, u0elo0]
                                        · have p6480_0 := h6480c.1
                                          have p6480_1 := h6480c.2.1
                                          have p6480_2 := h6480c.2.2.1
                                          have p6480_3 := h6480c.2.2.2
                                          linarith only [h0, h6310, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b, p6480_1]
                                        · have p6480_0 := h6480c.1
                                          have p6480_1 := h6480c.2.1
                                          have p6480_2 := h6480c.2.2.1
                                          have p6480_3 := h6480c.2.2.2
                                          linarith only [h6311, hlam, p6480_0]
                                        · have p6480_0 := h6480c.1
                                          have p6480_1 := h6480c.2.1
                                          have p6480_2 := h6480c.2.2.1
                                          have p6480_3 := h6480c.2.2.2
                                          linarith only [h6419, hlam, p6480_1]
                                        · have p6480_0 := h6480c.1
                                          have p6480_1 := h6480c.2.1
                                          have p6480_2 := h6480c.2.2.1
                                          have p6480_3 := h6480c.2.2.2
                                          linarith only [h6421, hlam, p6480_0]
                                        · have p6480_0 := h6480c.1
                                          have p6480_1 := h6480c.2.1
                                          have p6480_2 := h6480c.2.2.1
                                          have p6480_3 := h6480c.2.2.2
                                          linarith only [hlam, p6480_0]
                                        · have p6480_0 := h6480c.1
                                          have p6480_1 := h6480c.2.1
                                          have p6480_2 := h6480c.2.2.1
                                          have p6480_3 := h6480c.2.2.2
                                          linarith only [h6423, hlam, p6480_1]
                                        · have p6480_0 := h6480c.1
                                          have p6480_1 := h6480c.2.1
                                          have p6480_2 := h6480c.2.2.1
                                          have p6480_3 := h6480c.2.2.2
                                          linarith only [h6312, hlam, p6480_0]
                                        · have p6480_0 := h6480c.1
                                          have p6480_1 := h6480c.2.1
                                          have p6480_2 := h6480c.2.2.1
                                          have p6480_3 := h6480c.2.2.2
                                          linarith only [h6420, hlam, p6480_1]
                                        · have p6480_0 := h6480c.1
                                          have p6480_1 := h6480c.2.1
                                          have p6480_2 := h6480c.2.2.1
                                          have p6480_3 := h6480c.2.2.2
                                          linarith only [h6422, hlam, p6480_0]
                                        · have p6480_0 := h6480c.1
                                          have p6480_1 := h6480c.2.1
                                          have p6480_2 := h6480c.2.2.1
                                          have p6480_3 := h6480c.2.2.2
                                          linarith only [h0, h6312, h6419, h6425, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p6480_1]
                                        · have p6480_0 := h6480c.1
                                          have p6480_1 := h6480c.2.1
                                          have p6480_2 := h6480c.2.2.1
                                          have p6480_3 := h6480c.2.2.2
                                          linarith only [hlam, p6480_0]
                                      · rcases h1bigk with h6520c | h6520c | h6520c | h6520c | h6520c | h6520c | h6520c | h6520c | h6520c | h6520c | h6520c | h6520c | h6520c | h6520c | h6520c | h6520c | h6520c | h6520c | h6520c | h6520c | h6520c | h6520c | h6520c | h6520c | h6520c
                                        · have p6520_0 := h6520c.1
                                          have p6520_1 := h6520c.2.1
                                          have p6520_2 := h6520c.2.2.1
                                          have p6520_3 := h6520c.2.2.2
                                          linarith only [hlam, p6520_0]
                                        · have p6520_0 := h6520c.1
                                          have p6520_1 := h6520c.2.1
                                          have p6520_2 := h6520c.2.2.1
                                          have p6520_3 := h6520c.2.2.2
                                          linarith only [h0, hlam, p6520_0]
                                        · have p6520_0 := h6520c.1
                                          have p6520_1 := h6520c.2.1
                                          have p6520_2 := h6520c.2.2.1
                                          have p6520_3 := h6520c.2.2.2
                                          linarith only [h0, h6418, h6426, h6429, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p6520_1]
                                        · have p6520_0 := h6520c.1
                                          have p6520_1 := h6520c.2.1
                                          have p6520_2 := h6520c.2.2.1
                                          have p6520_3 := h6520c.2.2.2
                                          rcases p6520_3 (m.d 0 1) (by simp) with h6524 | h6524
                                          · rcases p6520_3 (m.d 1 2) (by simp) with h6525 | h6525
                                            · rcases p6520_3 (m.d 1 3) (by simp) with h6526 | h6526
                                              · linarith only [h6310, h6526, hlam]
                                              · linarith only [h6421, h6526, hlam]
                                            · linarith only [h6419, h6525, hlam]
                                          · linarith only [h6524, hlam, p6520_0]
                                        · have p6520_0 := h6520c.1
                                          have p6520_1 := h6520c.2.1
                                          have p6520_2 := h6520c.2.2.1
                                          have p6520_3 := h6520c.2.2.2
                                          rcases p6520_3 (m.d 0 1) (by simp) with h6531 | h6531
                                          · rcases p6520_3 (m.d 1 2) (by simp) with h6532 | h6532
                                            · rcases p6520_3 (m.d 1 3) (by simp) with h6533 | h6533
                                              · linarith only [h6310, h6533, hlam]
                                              · linarith only [h6422, h6533, hlam]
                                            · linarith only [h6420, h6532, hlam]
                                          · linarith only [h6531, hlam, p6520_0]
                                        · have p6520_0 := h6520c.1
                                          have p6520_1 := h6520c.2.1
                                          have p6520_2 := h6520c.2.2.1
                                          have p6520_3 := h6520c.2.2.2
                                          linarith only [h6310, h6418, h6426, h6429, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p6520_1]
                                        · have p6520_0 := h6520c.1
                                          have p6520_1 := h6520c.2.1
                                          have p6520_2 := h6520c.2.2.1
                                          have p6520_3 := h6520c.2.2.2
                                          linarith only [hlam, p6520_0]
                                        · have p6520_0 := h6520c.1
                                          have p6520_1 := h6520c.2.1
                                          have p6520_2 := h6520c.2.2.1
                                          have p6520_3 := h6520c.2.2.2
                                          rcases p6520_3 (m.d 0 1) (by simp) with h6540 | h6540
                                          · linarith only [h0, h6540, hlam]
                                          · linarith only [h6310, h6540, hlam]
                                        · have p6520_0 := h6520c.1
                                          have p6520_1 := h6520c.2.1
                                          have p6520_2 := h6520c.2.2.1
                                          have p6520_3 := h6520c.2.2.2
                                          linarith only [h0, h6310, h6311, h6318, hlam, p6431_1, p6520_2]
                                        · have p6520_0 := h6520c.1
                                          have p6520_1 := h6520c.2.1
                                          have p6520_2 := h6520c.2.2.1
                                          have p6520_3 := h6520c.2.2.2
                                          linarith only [h0, h6310, h6312, hlam, p6431_1, p6520_2]
                                        · have p6520_0 := h6520c.1
                                          have p6520_1 := h6520c.2.1
                                          have p6520_2 := h6520c.2.2.1
                                          have p6520_3 := h6520c.2.2.2
                                          linarith only [h6310, hlam, p6520_0]
                                        · have p6520_0 := h6520c.1
                                          have p6520_1 := h6520c.2.1
                                          have p6520_2 := h6520c.2.2.1
                                          have p6520_3 := h6520c.2.2.2
                                          linarith only [h6418, hlam, p6520_1]
                                        · have p6520_0 := h6520c.1
                                          have p6520_1 := h6520c.2.1
                                          have p6520_2 := h6520c.2.2.1
                                          have p6520_3 := h6520c.2.2.2
                                          linarith only [hlam, p6520_0]
                                        · have p6520_0 := h6520c.1
                                          have p6520_1 := h6520c.2.1
                                          have p6520_2 := h6520c.2.2.1
                                          have p6520_3 := h6520c.2.2.2
                                          linarith only [h6310, h6419, h6425, hc34, hlam, hphi, ht0b, ht45, ht5b, p6520_1, u0elo0]
                                        · have p6520_0 := h6520c.1
                                          have p6520_1 := h6520c.2.1
                                          have p6520_2 := h6520c.2.2.1
                                          have p6520_3 := h6520c.2.2.2
                                          linarith only [h0, h6310, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b, p6520_1]
                                        · have p6520_0 := h6520c.1
                                          have p6520_1 := h6520c.2.1
                                          have p6520_2 := h6520c.2.2.1
                                          have p6520_3 := h6520c.2.2.2
                                          linarith only [h6311, hlam, p6520_0]
                                        · have p6520_0 := h6520c.1
                                          have p6520_1 := h6520c.2.1
                                          have p6520_2 := h6520c.2.2.1
                                          have p6520_3 := h6520c.2.2.2
                                          linarith only [h6419, hlam, p6520_1]
                                        · have p6520_0 := h6520c.1
                                          have p6520_1 := h6520c.2.1
                                          have p6520_2 := h6520c.2.2.1
                                          have p6520_3 := h6520c.2.2.2
                                          linarith only [h6421, hlam, p6520_0]
                                        · have p6520_0 := h6520c.1
                                          have p6520_1 := h6520c.2.1
                                          have p6520_2 := h6520c.2.2.1
                                          have p6520_3 := h6520c.2.2.2
                                          linarith only [hlam, p6520_0]
                                        · have p6520_0 := h6520c.1
                                          have p6520_1 := h6520c.2.1
                                          have p6520_2 := h6520c.2.2.1
                                          have p6520_3 := h6520c.2.2.2
                                          linarith only [h6423, hlam, p6520_1]
                                        · have p6520_0 := h6520c.1
                                          have p6520_1 := h6520c.2.1
                                          have p6520_2 := h6520c.2.2.1
                                          have p6520_3 := h6520c.2.2.2
                                          linarith only [h6312, hlam, p6520_0]
                                        · have p6520_0 := h6520c.1
                                          have p6520_1 := h6520c.2.1
                                          have p6520_2 := h6520c.2.2.1
                                          have p6520_3 := h6520c.2.2.2
                                          linarith only [h6420, hlam, p6520_1]
                                        · have p6520_0 := h6520c.1
                                          have p6520_1 := h6520c.2.1
                                          have p6520_2 := h6520c.2.2.1
                                          have p6520_3 := h6520c.2.2.2
                                          linarith only [h6422, hlam, p6520_0]
                                        · have p6520_0 := h6520c.1
                                          have p6520_1 := h6520c.2.1
                                          have p6520_2 := h6520c.2.2.1
                                          have p6520_3 := h6520c.2.2.2
                                          linarith only [h0, h6312, h6419, h6425, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p6520_1]
                                        · have p6520_0 := h6520c.1
                                          have p6520_1 := h6520c.2.1
                                          have p6520_2 := h6520c.2.2.1
                                          have p6520_3 := h6520c.2.2.2
                                          linarith only [hlam, p6520_0]
                                      · rcases h1bigk with h6560c | h6560c | h6560c | h6560c | h6560c | h6560c | h6560c | h6560c | h6560c | h6560c | h6560c | h6560c | h6560c | h6560c | h6560c | h6560c | h6560c | h6560c | h6560c | h6560c | h6560c | h6560c | h6560c | h6560c | h6560c
                                        · have p6560_0 := h6560c.1
                                          have p6560_1 := h6560c.2.1
                                          have p6560_2 := h6560c.2.2.1
                                          have p6560_3 := h6560c.2.2.2
                                          linarith only [hlam, p6560_0]
                                        · have p6560_0 := h6560c.1
                                          have p6560_1 := h6560c.2.1
                                          have p6560_2 := h6560c.2.2.1
                                          have p6560_3 := h6560c.2.2.2
                                          linarith only [h0, hlam, p6560_0]
                                        · have p6560_0 := h6560c.1
                                          have p6560_1 := h6560c.2.1
                                          have p6560_2 := h6560c.2.2.1
                                          have p6560_3 := h6560c.2.2.2
                                          linarith only [h0, h6418, h6426, h6429, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p6560_1]
                                        · have p6560_0 := h6560c.1
                                          have p6560_1 := h6560c.2.1
                                          have p6560_2 := h6560c.2.2.1
                                          have p6560_3 := h6560c.2.2.2
                                          rcases p6560_3 (m.d 0 1) (by simp) with h6564 | h6564
                                          · rcases p6560_3 (m.d 1 2) (by simp) with h6565 | h6565
                                            · rcases p6560_3 (m.d 1 3) (by simp) with h6566 | h6566
                                              · linarith only [h6310, h6566, hlam]
                                              · linarith only [h6421, h6566, hlam]
                                            · linarith only [h6419, h6565, hlam]
                                          · linarith only [h6564, hlam, p6560_0]
                                        · have p6560_0 := h6560c.1
                                          have p6560_1 := h6560c.2.1
                                          have p6560_2 := h6560c.2.2.1
                                          have p6560_3 := h6560c.2.2.2
                                          rcases p6560_3 (m.d 0 1) (by simp) with h6571 | h6571
                                          · rcases p6560_3 (m.d 1 2) (by simp) with h6572 | h6572
                                            · rcases p6560_3 (m.d 1 3) (by simp) with h6573 | h6573
                                              · linarith only [h6310, h6573, hlam]
                                              · linarith only [h6422, h6573, hlam]
                                            · linarith only [h6420, h6572, hlam]
                                          · linarith only [h6571, hlam, p6560_0]
                                        · have p6560_0 := h6560c.1
                                          have p6560_1 := h6560c.2.1
                                          have p6560_2 := h6560c.2.2.1
                                          have p6560_3 := h6560c.2.2.2
                                          linarith only [h6310, h6418, h6426, h6429, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p6560_1]
                                        · have p6560_0 := h6560c.1
                                          have p6560_1 := h6560c.2.1
                                          have p6560_2 := h6560c.2.2.1
                                          have p6560_3 := h6560c.2.2.2
                                          linarith only [hlam, p6560_0]
                                        · have p6560_0 := h6560c.1
                                          have p6560_1 := h6560c.2.1
                                          have p6560_2 := h6560c.2.2.1
                                          have p6560_3 := h6560c.2.2.2
                                          rcases p6560_3 (m.d 0 1) (by simp) with h6580 | h6580
                                          · linarith only [h0, h6580, hlam]
                                          · linarith only [h6310, h6580, hlam]
                                        · have p6560_0 := h6560c.1
                                          have p6560_1 := h6560c.2.1
                                          have p6560_2 := h6560c.2.2.1
                                          have p6560_3 := h6560c.2.2.2
                                          linarith only [h0, h6310, h6311, h6318, hlam, p6431_1, p6560_2]
                                        · have p6560_0 := h6560c.1
                                          have p6560_1 := h6560c.2.1
                                          have p6560_2 := h6560c.2.2.1
                                          have p6560_3 := h6560c.2.2.2
                                          linarith only [h0, h6310, h6312, hlam, p6431_1, p6560_2]
                                        · have p6560_0 := h6560c.1
                                          have p6560_1 := h6560c.2.1
                                          have p6560_2 := h6560c.2.2.1
                                          have p6560_3 := h6560c.2.2.2
                                          linarith only [h6310, hlam, p6560_0]
                                        · have p6560_0 := h6560c.1
                                          have p6560_1 := h6560c.2.1
                                          have p6560_2 := h6560c.2.2.1
                                          have p6560_3 := h6560c.2.2.2
                                          linarith only [h6418, hlam, p6560_1]
                                        · have p6560_0 := h6560c.1
                                          have p6560_1 := h6560c.2.1
                                          have p6560_2 := h6560c.2.2.1
                                          have p6560_3 := h6560c.2.2.2
                                          linarith only [hlam, p6560_0]
                                        · have p6560_0 := h6560c.1
                                          have p6560_1 := h6560c.2.1
                                          have p6560_2 := h6560c.2.2.1
                                          have p6560_3 := h6560c.2.2.2
                                          linarith only [h6310, h6419, h6425, hc34, hlam, hphi, ht0b, ht45, ht5b, p6560_1, u0elo0]
                                        · have p6560_0 := h6560c.1
                                          have p6560_1 := h6560c.2.1
                                          have p6560_2 := h6560c.2.2.1
                                          have p6560_3 := h6560c.2.2.2
                                          linarith only [h0, h6310, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b, p6560_1]
                                        · have p6560_0 := h6560c.1
                                          have p6560_1 := h6560c.2.1
                                          have p6560_2 := h6560c.2.2.1
                                          have p6560_3 := h6560c.2.2.2
                                          linarith only [h6311, hlam, p6560_0]
                                        · have p6560_0 := h6560c.1
                                          have p6560_1 := h6560c.2.1
                                          have p6560_2 := h6560c.2.2.1
                                          have p6560_3 := h6560c.2.2.2
                                          linarith only [h6419, hlam, p6560_1]
                                        · have p6560_0 := h6560c.1
                                          have p6560_1 := h6560c.2.1
                                          have p6560_2 := h6560c.2.2.1
                                          have p6560_3 := h6560c.2.2.2
                                          linarith only [h6421, hlam, p6560_0]
                                        · have p6560_0 := h6560c.1
                                          have p6560_1 := h6560c.2.1
                                          have p6560_2 := h6560c.2.2.1
                                          have p6560_3 := h6560c.2.2.2
                                          linarith only [hlam, p6560_0]
                                        · have p6560_0 := h6560c.1
                                          have p6560_1 := h6560c.2.1
                                          have p6560_2 := h6560c.2.2.1
                                          have p6560_3 := h6560c.2.2.2
                                          linarith only [h6423, hlam, p6560_1]
                                        · have p6560_0 := h6560c.1
                                          have p6560_1 := h6560c.2.1
                                          have p6560_2 := h6560c.2.2.1
                                          have p6560_3 := h6560c.2.2.2
                                          linarith only [h6312, hlam, p6560_0]
                                        · have p6560_0 := h6560c.1
                                          have p6560_1 := h6560c.2.1
                                          have p6560_2 := h6560c.2.2.1
                                          have p6560_3 := h6560c.2.2.2
                                          linarith only [h6420, hlam, p6560_1]
                                        · have p6560_0 := h6560c.1
                                          have p6560_1 := h6560c.2.1
                                          have p6560_2 := h6560c.2.2.1
                                          have p6560_3 := h6560c.2.2.2
                                          linarith only [h6422, hlam, p6560_0]
                                        · have p6560_0 := h6560c.1
                                          have p6560_1 := h6560c.2.1
                                          have p6560_2 := h6560c.2.2.1
                                          have p6560_3 := h6560c.2.2.2
                                          linarith only [h0, h6312, h6419, h6425, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p6560_1]
                                        · have p6560_0 := h6560c.1
                                          have p6560_1 := h6560c.2.1
                                          have p6560_2 := h6560c.2.2.1
                                          have p6560_3 := h6560c.2.2.2
                                          linarith only [hlam, p6560_0]
                                      · linarith only [h6318, h6479, hlam, p6431_1, u0elo2]
                                      · linarith only [h6479, hlam, p6431_1, u0elo2]
                                · linarith only [h6317, h6474, hlam]
                              · linarith only [h6315, h6473, hlam]
                            · linarith only [h6312, h6472, hlam]
                          · have p6431_0 := h6431c.1
                            have p6431_1 := h6431c.2.1
                            have p6431_2 := h6431c.2.2.1
                            have p6431_3 := h6431c.2.2.2
                            linarith only [h6311, hlam, p6431_0]
                          · have p6431_0 := h6431c.1
                            have p6431_1 := h6431c.2.1
                            have p6431_2 := h6431c.2.2.1
                            have p6431_3 := h6431c.2.2.2
                            linarith only [h6314, hlam, p6431_0]
                          · have p6431_0 := h6431c.1
                            have p6431_1 := h6431c.2.1
                            have p6431_2 := h6431c.2.2.1
                            have p6431_3 := h6431c.2.2.2
                            linarith only [h6316, hlam, p6431_0]
                          · have p6431_0 := h6431c.1
                            have p6431_1 := h6431c.2.1
                            have p6431_2 := h6431c.2.2.1
                            have p6431_3 := h6431c.2.2.2
                            linarith only [hlam, p6431_0]
                          · have p6431_0 := h6431c.1
                            have p6431_1 := h6431c.2.1
                            have p6431_2 := h6431c.2.2.1
                            have p6431_3 := h6431c.2.2.2
                            linarith only [h6318, hlam, p6431_0]
                          · have p6431_0 := h6431c.1
                            have p6431_1 := h6431c.2.1
                            have p6431_2 := h6431c.2.2.1
                            have p6431_3 := h6431c.2.2.2
                            linarith only [h6312, hlam, p6431_0]
                          · have p6431_0 := h6431c.1
                            have p6431_1 := h6431c.2.1
                            have p6431_2 := h6431c.2.2.1
                            have p6431_3 := h6431c.2.2.2
                            linarith only [h6315, hlam, p6431_1]
                          · have p6431_0 := h6431c.1
                            have p6431_1 := h6431c.2.1
                            have p6431_2 := h6431c.2.2.1
                            have p6431_3 := h6431c.2.2.2
                            linarith only [h6317, hlam, p6431_0]
                          · have p6431_0 := h6431c.1
                            have p6431_1 := h6431c.2.1
                            have p6431_2 := h6431c.2.2.1
                            have p6431_3 := h6431c.2.2.2
                            rcases p6431_3 (m.d 0 1) (by simp) with h6613 | h6613
                            · rcases p6431_3 (m.d 0 2) (by simp) with h6614 | h6614
                              · rcases p6431_3 (m.d 0 3) (by simp) with h6615 | h6615
                                · rcases p6431_3 (m.d 0 4) (by simp) with h6616 | h6616
                                  · linarith only [h6318, h6616, hlam]
                                  · rcases p6431_3 (m.d 0 5) (by simp) with h6618 | h6618
                                    · rcases h0emin with h6619 | h6619 | h6619 | h6619 | h6619
                                      · rcases h1bigk with h6620c | h6620c | h6620c | h6620c | h6620c | h6620c | h6620c | h6620c | h6620c | h6620c | h6620c | h6620c | h6620c | h6620c | h6620c | h6620c | h6620c | h6620c | h6620c | h6620c | h6620c | h6620c | h6620c | h6620c | h6620c
                                        · have p6620_0 := h6620c.1
                                          have p6620_1 := h6620c.2.1
                                          have p6620_2 := h6620c.2.2.1
                                          have p6620_3 := h6620c.2.2.2
                                          linarith only [hlam, p6620_0]
                                        · have p6620_0 := h6620c.1
                                          have p6620_1 := h6620c.2.1
                                          have p6620_2 := h6620c.2.2.1
                                          have p6620_3 := h6620c.2.2.2
                                          linarith only [h0, hlam, p6620_0]
                                        · have p6620_0 := h6620c.1
                                          have p6620_1 := h6620c.2.1
                                          have p6620_2 := h6620c.2.2.1
                                          have p6620_3 := h6620c.2.2.2
                                          linarith only [h0, h6418, h6426, h6429, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p6620_1]
                                        · have p6620_0 := h6620c.1
                                          have p6620_1 := h6620c.2.1
                                          have p6620_2 := h6620c.2.2.1
                                          have p6620_3 := h6620c.2.2.2
                                          rcases p6620_3 (m.d 0 1) (by simp) with h6624 | h6624
                                          · rcases p6620_3 (m.d 1 2) (by simp) with h6625 | h6625
                                            · rcases p6620_3 (m.d 1 3) (by simp) with h6626 | h6626
                                              · linarith only [h6310, h6626, hlam]
                                              · linarith only [h6421, h6626, hlam]
                                            · linarith only [h6419, h6625, hlam]
                                          · linarith only [h6624, hlam, p6620_0]
                                        · have p6620_0 := h6620c.1
                                          have p6620_1 := h6620c.2.1
                                          have p6620_2 := h6620c.2.2.1
                                          have p6620_3 := h6620c.2.2.2
                                          rcases p6620_3 (m.d 0 1) (by simp) with h6631 | h6631
                                          · rcases p6620_3 (m.d 1 2) (by simp) with h6632 | h6632
                                            · rcases p6620_3 (m.d 1 3) (by simp) with h6633 | h6633
                                              · linarith only [h6310, h6633, hlam]
                                              · linarith only [h6422, h6633, hlam]
                                            · linarith only [h6420, h6632, hlam]
                                          · linarith only [h6631, hlam, p6620_0]
                                        · have p6620_0 := h6620c.1
                                          have p6620_1 := h6620c.2.1
                                          have p6620_2 := h6620c.2.2.1
                                          have p6620_3 := h6620c.2.2.2
                                          linarith only [h6619, hc12, hlam, ht01, p6620_1]
                                        · have p6620_0 := h6620c.1
                                          have p6620_1 := h6620c.2.1
                                          have p6620_2 := h6620c.2.2.1
                                          have p6620_3 := h6620c.2.2.2
                                          linarith only [hlam, p6620_0]
                                        · have p6620_0 := h6620c.1
                                          have p6620_1 := h6620c.2.1
                                          have p6620_2 := h6620c.2.2.1
                                          have p6620_3 := h6620c.2.2.2
                                          rcases p6620_3 (m.d 0 1) (by simp) with h6640 | h6640
                                          · linarith only [h0, h6640, hlam]
                                          · linarith only [h6310, h6640, hlam]
                                        · have p6620_0 := h6620c.1
                                          have p6620_1 := h6620c.2.1
                                          have p6620_2 := h6620c.2.2.1
                                          have p6620_3 := h6620c.2.2.2
                                          linarith only [h0, h6310, h6311, h6317, hlam, p6431_1, p6620_2]
                                        · have p6620_0 := h6620c.1
                                          have p6620_1 := h6620c.2.1
                                          have p6620_2 := h6620c.2.2.1
                                          have p6620_3 := h6620c.2.2.2
                                          rcases p6620_3 (m.d 0 1) (by simp) with h6644 | h6644
                                          · linarith only [h0, h6644, hlam]
                                          · linarith only [h6312, h6644, hlam]
                                        · have p6620_0 := h6620c.1
                                          have p6620_1 := h6620c.2.1
                                          have p6620_2 := h6620c.2.2.1
                                          have p6620_3 := h6620c.2.2.2
                                          linarith only [h6310, hlam, p6620_0]
                                        · have p6620_0 := h6620c.1
                                          have p6620_1 := h6620c.2.1
                                          have p6620_2 := h6620c.2.2.1
                                          have p6620_3 := h6620c.2.2.2
                                          linarith only [h6418, hlam, p6620_1]
                                        · have p6620_0 := h6620c.1
                                          have p6620_1 := h6620c.2.1
                                          have p6620_2 := h6620c.2.2.1
                                          have p6620_3 := h6620c.2.2.2
                                          linarith only [hlam, p6620_0]
                                        · have p6620_0 := h6620c.1
                                          have p6620_1 := h6620c.2.1
                                          have p6620_2 := h6620c.2.2.1
                                          have p6620_3 := h6620c.2.2.2
                                          linarith only [h6310, h6419, h6425, hc34, hlam, hphi, ht0b, ht45, ht5b, p6620_1, u0elo0]
                                        · have p6620_0 := h6620c.1
                                          have p6620_1 := h6620c.2.1
                                          have p6620_2 := h6620c.2.2.1
                                          have p6620_3 := h6620c.2.2.2
                                          linarith only [h0, h6310, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b, p6620_1]
                                        · have p6620_0 := h6620c.1
                                          have p6620_1 := h6620c.2.1
                                          have p6620_2 := h6620c.2.2.1
                                          have p6620_3 := h6620c.2.2.2
                                          linarith only [h6311, hlam, p6620_0]
                                        · have p6620_0 := h6620c.1
                                          have p6620_1 := h6620c.2.1
                                          have p6620_2 := h6620c.2.2.1
                                          have p6620_3 := h6620c.2.2.2
                                          linarith only [h6419, hlam, p6620_1]
                                        · have p6620_0 := h6620c.1
                                          have p6620_1 := h6620c.2.1
                                          have p6620_2 := h6620c.2.2.1
                                          have p6620_3 := h6620c.2.2.2
                                          linarith only [h6421, hlam, p6620_0]
                                        · have p6620_0 := h6620c.1
                                          have p6620_1 := h6620c.2.1
                                          have p6620_2 := h6620c.2.2.1
                                          have p6620_3 := h6620c.2.2.2
                                          linarith only [hlam, p6620_0]
                                        · have p6620_0 := h6620c.1
                                          have p6620_1 := h6620c.2.1
                                          have p6620_2 := h6620c.2.2.1
                                          have p6620_3 := h6620c.2.2.2
                                          linarith only [h6423, hlam, p6620_1]
                                        · have p6620_0 := h6620c.1
                                          have p6620_1 := h6620c.2.1
                                          have p6620_2 := h6620c.2.2.1
                                          have p6620_3 := h6620c.2.2.2
                                          linarith only [h6312, hlam, p6620_0]
                                        · have p6620_0 := h6620c.1
                                          have p6620_1 := h6620c.2.1
                                          have p6620_2 := h6620c.2.2.1
                                          have p6620_3 := h6620c.2.2.2
                                          linarith only [h6420, hlam, p6620_1]
                                        · have p6620_0 := h6620c.1
                                          have p6620_1 := h6620c.2.1
                                          have p6620_2 := h6620c.2.2.1
                                          have p6620_3 := h6620c.2.2.2
                                          linarith only [h6422, hlam, p6620_0]
                                        · have p6620_0 := h6620c.1
                                          have p6620_1 := h6620c.2.1
                                          have p6620_2 := h6620c.2.2.1
                                          have p6620_3 := h6620c.2.2.2
                                          linarith only [h0, h6312, h6419, h6425, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p6620_1]
                                        · have p6620_0 := h6620c.1
                                          have p6620_1 := h6620c.2.1
                                          have p6620_2 := h6620c.2.2.1
                                          have p6620_3 := h6620c.2.2.2
                                          linarith only [hlam, p6620_0]
                                      · rcases h1bigk with h6662c | h6662c | h6662c | h6662c | h6662c | h6662c | h6662c | h6662c | h6662c | h6662c | h6662c | h6662c | h6662c | h6662c | h6662c | h6662c | h6662c | h6662c | h6662c | h6662c | h6662c | h6662c | h6662c | h6662c | h6662c
                                        · have p6662_0 := h6662c.1
                                          have p6662_1 := h6662c.2.1
                                          have p6662_2 := h6662c.2.2.1
                                          have p6662_3 := h6662c.2.2.2
                                          linarith only [hlam, p6662_0]
                                        · have p6662_0 := h6662c.1
                                          have p6662_1 := h6662c.2.1
                                          have p6662_2 := h6662c.2.2.1
                                          have p6662_3 := h6662c.2.2.2
                                          linarith only [h0, hlam, p6662_0]
                                        · have p6662_0 := h6662c.1
                                          have p6662_1 := h6662c.2.1
                                          have p6662_2 := h6662c.2.2.1
                                          have p6662_3 := h6662c.2.2.2
                                          linarith only [h0, h6418, h6426, h6429, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p6662_1]
                                        · have p6662_0 := h6662c.1
                                          have p6662_1 := h6662c.2.1
                                          have p6662_2 := h6662c.2.2.1
                                          have p6662_3 := h6662c.2.2.2
                                          rcases p6662_3 (m.d 0 1) (by simp) with h6666 | h6666
                                          · rcases p6662_3 (m.d 1 2) (by simp) with h6667 | h6667
                                            · rcases p6662_3 (m.d 1 3) (by simp) with h6668 | h6668
                                              · linarith only [h6310, h6668, hlam]
                                              · linarith only [h6421, h6668, hlam]
                                            · linarith only [h6419, h6667, hlam]
                                          · linarith only [h6666, hlam, p6662_0]
                                        · have p6662_0 := h6662c.1
                                          have p6662_1 := h6662c.2.1
                                          have p6662_2 := h6662c.2.2.1
                                          have p6662_3 := h6662c.2.2.2
                                          rcases p6662_3 (m.d 0 1) (by simp) with h6673 | h6673
                                          · rcases p6662_3 (m.d 1 2) (by simp) with h6674 | h6674
                                            · rcases p6662_3 (m.d 1 3) (by simp) with h6675 | h6675
                                              · linarith only [h6310, h6675, hlam]
                                              · linarith only [h6422, h6675, hlam]
                                            · linarith only [h6420, h6674, hlam]
                                          · linarith only [h6673, hlam, p6662_0]
                                        · have p6662_0 := h6662c.1
                                          have p6662_1 := h6662c.2.1
                                          have p6662_2 := h6662c.2.2.1
                                          have p6662_3 := h6662c.2.2.2
                                          linarith only [h6310, h6418, h6426, h6429, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p6662_1]
                                        · have p6662_0 := h6662c.1
                                          have p6662_1 := h6662c.2.1
                                          have p6662_2 := h6662c.2.2.1
                                          have p6662_3 := h6662c.2.2.2
                                          linarith only [hlam, p6662_0]
                                        · have p6662_0 := h6662c.1
                                          have p6662_1 := h6662c.2.1
                                          have p6662_2 := h6662c.2.2.1
                                          have p6662_3 := h6662c.2.2.2
                                          rcases p6662_3 (m.d 0 1) (by simp) with h6682 | h6682
                                          · linarith only [h0, h6682, hlam]
                                          · linarith only [h6310, h6682, hlam]
                                        · have p6662_0 := h6662c.1
                                          have p6662_1 := h6662c.2.1
                                          have p6662_2 := h6662c.2.2.1
                                          have p6662_3 := h6662c.2.2.2
                                          linarith only [h0, h6310, h6311, h6317, hlam, p6431_1, p6662_2]
                                        · have p6662_0 := h6662c.1
                                          have p6662_1 := h6662c.2.1
                                          have p6662_2 := h6662c.2.2.1
                                          have p6662_3 := h6662c.2.2.2
                                          rcases p6662_3 (m.d 0 1) (by simp) with h6686 | h6686
                                          · linarith only [h0, h6686, hlam]
                                          · linarith only [h6312, h6686, hlam]
                                        · have p6662_0 := h6662c.1
                                          have p6662_1 := h6662c.2.1
                                          have p6662_2 := h6662c.2.2.1
                                          have p6662_3 := h6662c.2.2.2
                                          linarith only [h6310, hlam, p6662_0]
                                        · have p6662_0 := h6662c.1
                                          have p6662_1 := h6662c.2.1
                                          have p6662_2 := h6662c.2.2.1
                                          have p6662_3 := h6662c.2.2.2
                                          linarith only [h6418, hlam, p6662_1]
                                        · have p6662_0 := h6662c.1
                                          have p6662_1 := h6662c.2.1
                                          have p6662_2 := h6662c.2.2.1
                                          have p6662_3 := h6662c.2.2.2
                                          linarith only [hlam, p6662_0]
                                        · have p6662_0 := h6662c.1
                                          have p6662_1 := h6662c.2.1
                                          have p6662_2 := h6662c.2.2.1
                                          have p6662_3 := h6662c.2.2.2
                                          linarith only [h6310, h6419, h6425, hc34, hlam, hphi, ht0b, ht45, ht5b, p6662_1, u0elo0]
                                        · have p6662_0 := h6662c.1
                                          have p6662_1 := h6662c.2.1
                                          have p6662_2 := h6662c.2.2.1
                                          have p6662_3 := h6662c.2.2.2
                                          linarith only [h0, h6310, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b, p6662_1]
                                        · have p6662_0 := h6662c.1
                                          have p6662_1 := h6662c.2.1
                                          have p6662_2 := h6662c.2.2.1
                                          have p6662_3 := h6662c.2.2.2
                                          linarith only [h6311, hlam, p6662_0]
                                        · have p6662_0 := h6662c.1
                                          have p6662_1 := h6662c.2.1
                                          have p6662_2 := h6662c.2.2.1
                                          have p6662_3 := h6662c.2.2.2
                                          linarith only [h6419, hlam, p6662_1]
                                        · have p6662_0 := h6662c.1
                                          have p6662_1 := h6662c.2.1
                                          have p6662_2 := h6662c.2.2.1
                                          have p6662_3 := h6662c.2.2.2
                                          linarith only [h6421, hlam, p6662_0]
                                        · have p6662_0 := h6662c.1
                                          have p6662_1 := h6662c.2.1
                                          have p6662_2 := h6662c.2.2.1
                                          have p6662_3 := h6662c.2.2.2
                                          linarith only [hlam, p6662_0]
                                        · have p6662_0 := h6662c.1
                                          have p6662_1 := h6662c.2.1
                                          have p6662_2 := h6662c.2.2.1
                                          have p6662_3 := h6662c.2.2.2
                                          linarith only [h6423, hlam, p6662_1]
                                        · have p6662_0 := h6662c.1
                                          have p6662_1 := h6662c.2.1
                                          have p6662_2 := h6662c.2.2.1
                                          have p6662_3 := h6662c.2.2.2
                                          linarith only [h6312, hlam, p6662_0]
                                        · have p6662_0 := h6662c.1
                                          have p6662_1 := h6662c.2.1
                                          have p6662_2 := h6662c.2.2.1
                                          have p6662_3 := h6662c.2.2.2
                                          linarith only [h6420, hlam, p6662_1]
                                        · have p6662_0 := h6662c.1
                                          have p6662_1 := h6662c.2.1
                                          have p6662_2 := h6662c.2.2.1
                                          have p6662_3 := h6662c.2.2.2
                                          linarith only [h6422, hlam, p6662_0]
                                        · have p6662_0 := h6662c.1
                                          have p6662_1 := h6662c.2.1
                                          have p6662_2 := h6662c.2.2.1
                                          have p6662_3 := h6662c.2.2.2
                                          linarith only [h0, h6312, h6419, h6425, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p6662_1]
                                        · have p6662_0 := h6662c.1
                                          have p6662_1 := h6662c.2.1
                                          have p6662_2 := h6662c.2.2.1
                                          have p6662_3 := h6662c.2.2.2
                                          linarith only [hlam, p6662_0]
                                      · rcases h1bigk with h6704c | h6704c | h6704c | h6704c | h6704c | h6704c | h6704c | h6704c | h6704c | h6704c | h6704c | h6704c | h6704c | h6704c | h6704c | h6704c | h6704c | h6704c | h6704c | h6704c | h6704c | h6704c | h6704c | h6704c | h6704c
                                        · have p6704_0 := h6704c.1
                                          have p6704_1 := h6704c.2.1
                                          have p6704_2 := h6704c.2.2.1
                                          have p6704_3 := h6704c.2.2.2
                                          linarith only [hlam, p6704_0]
                                        · have p6704_0 := h6704c.1
                                          have p6704_1 := h6704c.2.1
                                          have p6704_2 := h6704c.2.2.1
                                          have p6704_3 := h6704c.2.2.2
                                          linarith only [h0, hlam, p6704_0]
                                        · have p6704_0 := h6704c.1
                                          have p6704_1 := h6704c.2.1
                                          have p6704_2 := h6704c.2.2.1
                                          have p6704_3 := h6704c.2.2.2
                                          linarith only [h0, h6418, h6426, h6429, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p6704_1]
                                        · have p6704_0 := h6704c.1
                                          have p6704_1 := h6704c.2.1
                                          have p6704_2 := h6704c.2.2.1
                                          have p6704_3 := h6704c.2.2.2
                                          rcases p6704_3 (m.d 0 1) (by simp) with h6708 | h6708
                                          · rcases p6704_3 (m.d 1 2) (by simp) with h6709 | h6709
                                            · rcases p6704_3 (m.d 1 3) (by simp) with h6710 | h6710
                                              · linarith only [h6310, h6710, hlam]
                                              · linarith only [h6421, h6710, hlam]
                                            · linarith only [h6419, h6709, hlam]
                                          · linarith only [h6708, hlam, p6704_0]
                                        · have p6704_0 := h6704c.1
                                          have p6704_1 := h6704c.2.1
                                          have p6704_2 := h6704c.2.2.1
                                          have p6704_3 := h6704c.2.2.2
                                          rcases p6704_3 (m.d 0 1) (by simp) with h6715 | h6715
                                          · rcases p6704_3 (m.d 1 2) (by simp) with h6716 | h6716
                                            · rcases p6704_3 (m.d 1 3) (by simp) with h6717 | h6717
                                              · linarith only [h6310, h6717, hlam]
                                              · linarith only [h6422, h6717, hlam]
                                            · linarith only [h6420, h6716, hlam]
                                          · linarith only [h6715, hlam, p6704_0]
                                        · have p6704_0 := h6704c.1
                                          have p6704_1 := h6704c.2.1
                                          have p6704_2 := h6704c.2.2.1
                                          have p6704_3 := h6704c.2.2.2
                                          linarith only [h6310, h6418, h6426, h6429, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p6704_1]
                                        · have p6704_0 := h6704c.1
                                          have p6704_1 := h6704c.2.1
                                          have p6704_2 := h6704c.2.2.1
                                          have p6704_3 := h6704c.2.2.2
                                          linarith only [hlam, p6704_0]
                                        · have p6704_0 := h6704c.1
                                          have p6704_1 := h6704c.2.1
                                          have p6704_2 := h6704c.2.2.1
                                          have p6704_3 := h6704c.2.2.2
                                          rcases p6704_3 (m.d 0 1) (by simp) with h6724 | h6724
                                          · linarith only [h0, h6724, hlam]
                                          · linarith only [h6310, h6724, hlam]
                                        · have p6704_0 := h6704c.1
                                          have p6704_1 := h6704c.2.1
                                          have p6704_2 := h6704c.2.2.1
                                          have p6704_3 := h6704c.2.2.2
                                          linarith only [h0, h6310, h6311, h6317, hlam, p6431_1, p6704_2]
                                        · have p6704_0 := h6704c.1
                                          have p6704_1 := h6704c.2.1
                                          have p6704_2 := h6704c.2.2.1
                                          have p6704_3 := h6704c.2.2.2
                                          rcases p6704_3 (m.d 0 1) (by simp) with h6728 | h6728
                                          · linarith only [h0, h6728, hlam]
                                          · linarith only [h6312, h6728, hlam]
                                        · have p6704_0 := h6704c.1
                                          have p6704_1 := h6704c.2.1
                                          have p6704_2 := h6704c.2.2.1
                                          have p6704_3 := h6704c.2.2.2
                                          linarith only [h6310, hlam, p6704_0]
                                        · have p6704_0 := h6704c.1
                                          have p6704_1 := h6704c.2.1
                                          have p6704_2 := h6704c.2.2.1
                                          have p6704_3 := h6704c.2.2.2
                                          linarith only [h6418, hlam, p6704_1]
                                        · have p6704_0 := h6704c.1
                                          have p6704_1 := h6704c.2.1
                                          have p6704_2 := h6704c.2.2.1
                                          have p6704_3 := h6704c.2.2.2
                                          linarith only [hlam, p6704_0]
                                        · have p6704_0 := h6704c.1
                                          have p6704_1 := h6704c.2.1
                                          have p6704_2 := h6704c.2.2.1
                                          have p6704_3 := h6704c.2.2.2
                                          linarith only [h6310, h6419, h6425, hc34, hlam, hphi, ht0b, ht45, ht5b, p6704_1, u0elo0]
                                        · have p6704_0 := h6704c.1
                                          have p6704_1 := h6704c.2.1
                                          have p6704_2 := h6704c.2.2.1
                                          have p6704_3 := h6704c.2.2.2
                                          linarith only [h0, h6310, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b, p6704_1]
                                        · have p6704_0 := h6704c.1
                                          have p6704_1 := h6704c.2.1
                                          have p6704_2 := h6704c.2.2.1
                                          have p6704_3 := h6704c.2.2.2
                                          linarith only [h6311, hlam, p6704_0]
                                        · have p6704_0 := h6704c.1
                                          have p6704_1 := h6704c.2.1
                                          have p6704_2 := h6704c.2.2.1
                                          have p6704_3 := h6704c.2.2.2
                                          linarith only [h6419, hlam, p6704_1]
                                        · have p6704_0 := h6704c.1
                                          have p6704_1 := h6704c.2.1
                                          have p6704_2 := h6704c.2.2.1
                                          have p6704_3 := h6704c.2.2.2
                                          linarith only [h6421, hlam, p6704_0]
                                        · have p6704_0 := h6704c.1
                                          have p6704_1 := h6704c.2.1
                                          have p6704_2 := h6704c.2.2.1
                                          have p6704_3 := h6704c.2.2.2
                                          linarith only [hlam, p6704_0]
                                        · have p6704_0 := h6704c.1
                                          have p6704_1 := h6704c.2.1
                                          have p6704_2 := h6704c.2.2.1
                                          have p6704_3 := h6704c.2.2.2
                                          linarith only [h6423, hlam, p6704_1]
                                        · have p6704_0 := h6704c.1
                                          have p6704_1 := h6704c.2.1
                                          have p6704_2 := h6704c.2.2.1
                                          have p6704_3 := h6704c.2.2.2
                                          linarith only [h6312, hlam, p6704_0]
                                        · have p6704_0 := h6704c.1
                                          have p6704_1 := h6704c.2.1
                                          have p6704_2 := h6704c.2.2.1
                                          have p6704_3 := h6704c.2.2.2
                                          linarith only [h6420, hlam, p6704_1]
                                        · have p6704_0 := h6704c.1
                                          have p6704_1 := h6704c.2.1
                                          have p6704_2 := h6704c.2.2.1
                                          have p6704_3 := h6704c.2.2.2
                                          linarith only [h6422, hlam, p6704_0]
                                        · have p6704_0 := h6704c.1
                                          have p6704_1 := h6704c.2.1
                                          have p6704_2 := h6704c.2.2.1
                                          have p6704_3 := h6704c.2.2.2
                                          linarith only [h0, h6312, h6419, h6425, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p6704_1]
                                        · have p6704_0 := h6704c.1
                                          have p6704_1 := h6704c.2.1
                                          have p6704_2 := h6704c.2.2.1
                                          have p6704_3 := h6704c.2.2.2
                                          linarith only [hlam, p6704_0]
                                      · linarith only [h6317, h6619, hlam, p6431_1, u0elo2]
                                      · rcases h1bigk with h6747c | h6747c | h6747c | h6747c | h6747c | h6747c | h6747c | h6747c | h6747c | h6747c | h6747c | h6747c | h6747c | h6747c | h6747c | h6747c | h6747c | h6747c | h6747c | h6747c | h6747c | h6747c | h6747c | h6747c | h6747c
                                        · have p6747_0 := h6747c.1
                                          have p6747_1 := h6747c.2.1
                                          have p6747_2 := h6747c.2.2.1
                                          have p6747_3 := h6747c.2.2.2
                                          linarith only [hlam, p6747_0]
                                        · have p6747_0 := h6747c.1
                                          have p6747_1 := h6747c.2.1
                                          have p6747_2 := h6747c.2.2.1
                                          have p6747_3 := h6747c.2.2.2
                                          linarith only [h0, hlam, p6747_0]
                                        · have p6747_0 := h6747c.1
                                          have p6747_1 := h6747c.2.1
                                          have p6747_2 := h6747c.2.2.1
                                          have p6747_3 := h6747c.2.2.2
                                          linarith only [h0, h6418, h6426, h6429, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p6747_1]
                                        · have p6747_0 := h6747c.1
                                          have p6747_1 := h6747c.2.1
                                          have p6747_2 := h6747c.2.2.1
                                          have p6747_3 := h6747c.2.2.2
                                          rcases p6747_3 (m.d 0 1) (by simp) with h6751 | h6751
                                          · rcases p6747_3 (m.d 1 2) (by simp) with h6752 | h6752
                                            · rcases p6747_3 (m.d 1 3) (by simp) with h6753 | h6753
                                              · linarith only [h6310, h6753, hlam]
                                              · linarith only [h6421, h6753, hlam]
                                            · linarith only [h6419, h6752, hlam]
                                          · linarith only [h6751, hlam, p6747_0]
                                        · have p6747_0 := h6747c.1
                                          have p6747_1 := h6747c.2.1
                                          have p6747_2 := h6747c.2.2.1
                                          have p6747_3 := h6747c.2.2.2
                                          rcases p6747_3 (m.d 0 1) (by simp) with h6758 | h6758
                                          · rcases p6747_3 (m.d 1 2) (by simp) with h6759 | h6759
                                            · rcases p6747_3 (m.d 1 3) (by simp) with h6760 | h6760
                                              · linarith only [h6310, h6760, hlam]
                                              · linarith only [h6422, h6760, hlam]
                                            · linarith only [h6420, h6759, hlam]
                                          · linarith only [h6758, hlam, p6747_0]
                                        · have p6747_0 := h6747c.1
                                          have p6747_1 := h6747c.2.1
                                          have p6747_2 := h6747c.2.2.1
                                          have p6747_3 := h6747c.2.2.2
                                          linarith only [h6310, h6317, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p6431_1, p6747_1]
                                        · have p6747_0 := h6747c.1
                                          have p6747_1 := h6747c.2.1
                                          have p6747_2 := h6747c.2.2.1
                                          have p6747_3 := h6747c.2.2.2
                                          linarith only [hlam, p6747_0]
                                        · have p6747_0 := h6747c.1
                                          have p6747_1 := h6747c.2.1
                                          have p6747_2 := h6747c.2.2.1
                                          have p6747_3 := h6747c.2.2.2
                                          rcases p6747_3 (m.d 0 1) (by simp) with h6767 | h6767
                                          · linarith only [h0, h6767, hlam]
                                          · linarith only [h6310, h6767, hlam]
                                        · have p6747_0 := h6747c.1
                                          have p6747_1 := h6747c.2.1
                                          have p6747_2 := h6747c.2.2.1
                                          have p6747_3 := h6747c.2.2.2
                                          linarith only [h0, h6310, h6311, h6317, hlam, p6431_1, p6747_2]
                                        · have p6747_0 := h6747c.1
                                          have p6747_1 := h6747c.2.1
                                          have p6747_2 := h6747c.2.2.1
                                          have p6747_3 := h6747c.2.2.2
                                          rcases p6747_3 (m.d 0 1) (by simp) with h6771 | h6771
                                          · linarith only [h0, h6771, hlam]
                                          · linarith only [h6312, h6771, hlam]
                                        · have p6747_0 := h6747c.1
                                          have p6747_1 := h6747c.2.1
                                          have p6747_2 := h6747c.2.2.1
                                          have p6747_3 := h6747c.2.2.2
                                          linarith only [h6310, hlam, p6747_0]
                                        · have p6747_0 := h6747c.1
                                          have p6747_1 := h6747c.2.1
                                          have p6747_2 := h6747c.2.2.1
                                          have p6747_3 := h6747c.2.2.2
                                          linarith only [h6418, hlam, p6747_1]
                                        · have p6747_0 := h6747c.1
                                          have p6747_1 := h6747c.2.1
                                          have p6747_2 := h6747c.2.2.1
                                          have p6747_3 := h6747c.2.2.2
                                          linarith only [hlam, p6747_0]
                                        · have p6747_0 := h6747c.1
                                          have p6747_1 := h6747c.2.1
                                          have p6747_2 := h6747c.2.2.1
                                          have p6747_3 := h6747c.2.2.2
                                          linarith only [h6310, h6419, h6425, hc34, hlam, hphi, ht0b, ht45, ht5b, p6747_1, u0elo0]
                                        · have p6747_0 := h6747c.1
                                          have p6747_1 := h6747c.2.1
                                          have p6747_2 := h6747c.2.2.1
                                          have p6747_3 := h6747c.2.2.2
                                          linarith only [h0, h6310, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b, p6747_1]
                                        · have p6747_0 := h6747c.1
                                          have p6747_1 := h6747c.2.1
                                          have p6747_2 := h6747c.2.2.1
                                          have p6747_3 := h6747c.2.2.2
                                          linarith only [h6311, hlam, p6747_0]
                                        · have p6747_0 := h6747c.1
                                          have p6747_1 := h6747c.2.1
                                          have p6747_2 := h6747c.2.2.1
                                          have p6747_3 := h6747c.2.2.2
                                          linarith only [h6419, hlam, p6747_1]
                                        · have p6747_0 := h6747c.1
                                          have p6747_1 := h6747c.2.1
                                          have p6747_2 := h6747c.2.2.1
                                          have p6747_3 := h6747c.2.2.2
                                          linarith only [h6421, hlam, p6747_0]
                                        · have p6747_0 := h6747c.1
                                          have p6747_1 := h6747c.2.1
                                          have p6747_2 := h6747c.2.2.1
                                          have p6747_3 := h6747c.2.2.2
                                          linarith only [hlam, p6747_0]
                                        · have p6747_0 := h6747c.1
                                          have p6747_1 := h6747c.2.1
                                          have p6747_2 := h6747c.2.2.1
                                          have p6747_3 := h6747c.2.2.2
                                          linarith only [h6423, hlam, p6747_1]
                                        · have p6747_0 := h6747c.1
                                          have p6747_1 := h6747c.2.1
                                          have p6747_2 := h6747c.2.2.1
                                          have p6747_3 := h6747c.2.2.2
                                          linarith only [h6312, hlam, p6747_0]
                                        · have p6747_0 := h6747c.1
                                          have p6747_1 := h6747c.2.1
                                          have p6747_2 := h6747c.2.2.1
                                          have p6747_3 := h6747c.2.2.2
                                          linarith only [h6420, hlam, p6747_1]
                                        · have p6747_0 := h6747c.1
                                          have p6747_1 := h6747c.2.1
                                          have p6747_2 := h6747c.2.2.1
                                          have p6747_3 := h6747c.2.2.2
                                          linarith only [h6422, hlam, p6747_0]
                                        · have p6747_0 := h6747c.1
                                          have p6747_1 := h6747c.2.1
                                          have p6747_2 := h6747c.2.2.1
                                          have p6747_3 := h6747c.2.2.2
                                          linarith only [h0, h6312, h6419, h6425, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p6747_1]
                                        · have p6747_0 := h6747c.1
                                          have p6747_1 := h6747c.2.1
                                          have p6747_2 := h6747c.2.2.1
                                          have p6747_3 := h6747c.2.2.2
                                          linarith only [hlam, p6747_0]
                                    · linarith only [h6318, h6618, hlam]
                                · linarith only [h6316, h6615, hlam]
                              · linarith only [h6314, h6614, hlam]
                            · linarith only [h6311, h6613, hlam]
                          · have p6431_0 := h6431c.1
                            have p6431_1 := h6431c.2.1
                            have p6431_2 := h6431c.2.2.1
                            have p6431_3 := h6431c.2.2.2
                            linarith only [hlam, p6431_0]
                    · linarith only [h0, h6310, h6422, h6426, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                  · linarith only [h0, h6310, h6421, h6425, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
              · linarith only [h0, h6310, h6317, h6421, h6422, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h6797 | h6797
              · linarith only [h0, h6310, h6316, h6421, h6797, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h6799 | h6799
                · linarith only [h0, h6311, h6318, h6799, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h6801 | h6801
                  · linarith only [h6418, h6421, h6801, hlam]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h6803 | h6803
                    · linarith only [h0, h6310, h6316, h6418, h6421, h6797, h6803, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h6805 | h6805
                      · linarith only [h6314, h6316, h6318, h6418, h6421, h6805, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h6807 | h6807
                        · linarith only [h6316, h6318, h6807, hlam]
                        · rcases h0bigk with h6809c | h6809c | h6809c | h6809c | h6809c | h6809c | h6809c | h6809c | h6809c | h6809c | h6809c | h6809c | h6809c | h6809c | h6809c | h6809c | h6809c | h6809c | h6809c | h6809c | h6809c | h6809c | h6809c | h6809c | h6809c
                          · have p6809_0 := h6809c.1
                            have p6809_1 := h6809c.2.1
                            have p6809_2 := h6809c.2.2.1
                            have p6809_3 := h6809c.2.2.2
                            linarith only [hlam, p6809_0]
                          · have p6809_0 := h6809c.1
                            have p6809_1 := h6809c.2.1
                            have p6809_2 := h6809c.2.2.1
                            have p6809_3 := h6809c.2.2.2
                            linarith only [h0, hlam, p6809_1]
                          · have p6809_0 := h6809c.1
                            have p6809_1 := h6809c.2.1
                            have p6809_2 := h6809c.2.2.1
                            have p6809_3 := h6809c.2.2.2
                            linarith only [h0, h6317, h6418, h6421, h6807, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6809_1]
                          · have p6809_0 := h6809c.1
                            have p6809_1 := h6809c.2.1
                            have p6809_2 := h6809c.2.2.1
                            have p6809_3 := h6809c.2.2.2
                            linarith only [h0, h6316, h6418, h6421, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6809_1]
                          · have p6809_0 := h6809c.1
                            have p6809_1 := h6809c.2.1
                            have p6809_2 := h6809c.2.2.1
                            have p6809_3 := h6809c.2.2.2
                            linarith only [h0, h6317, h6418, h6421, h6807, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6809_1]
                          · have p6809_0 := h6809c.1
                            have p6809_1 := h6809c.2.1
                            have p6809_2 := h6809c.2.2.1
                            have p6809_3 := h6809c.2.2.2
                            linarith only [h6310, h6418, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6809_1, u0elo1]
                          · have p6809_0 := h6809c.1
                            have p6809_1 := h6809c.2.1
                            have p6809_2 := h6809c.2.2.1
                            have p6809_3 := h6809c.2.2.2
                            linarith only [hlam, p6809_0]
                          · have p6809_0 := h6809c.1
                            have p6809_1 := h6809c.2.1
                            have p6809_2 := h6809c.2.2.1
                            have p6809_3 := h6809c.2.2.2
                            linarith only [h6317, h6418, h6421, h6807, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6809_1, u0elo1]
                          · have p6809_0 := h6809c.1
                            have p6809_1 := h6809c.2.1
                            have p6809_2 := h6809c.2.2.1
                            have p6809_3 := h6809c.2.2.2
                            linarith only [h6316, h6418, h6421, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6809_1, u0elo1]
                          · have p6809_0 := h6809c.1
                            have p6809_1 := h6809c.2.1
                            have p6809_2 := h6809c.2.2.1
                            have p6809_3 := h6809c.2.2.2
                            linarith only [h6317, h6418, h6421, h6807, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6809_1, u0elo1]
                          · have p6809_0 := h6809c.1
                            have p6809_1 := h6809c.2.1
                            have p6809_2 := h6809c.2.2.1
                            have p6809_3 := h6809c.2.2.2
                            linarith only [h6310, hlam, p6809_1]
                          · have p6809_0 := h6809c.1
                            have p6809_1 := h6809c.2.1
                            have p6809_2 := h6809c.2.2.1
                            have p6809_3 := h6809c.2.2.2
                            linarith only [h6313, hlam, p6809_1]
                          · have p6809_0 := h6809c.1
                            have p6809_1 := h6809c.2.1
                            have p6809_2 := h6809c.2.2.1
                            have p6809_3 := h6809c.2.2.2
                            linarith only [hlam, p6809_0]
                          · have p6809_0 := h6809c.1
                            have p6809_1 := h6809c.2.1
                            have p6809_2 := h6809c.2.2.1
                            have p6809_3 := h6809c.2.2.2
                            linarith only [h6310, h6316, h6418, h6421, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6809_1, u0elo0]
                          · have p6809_0 := h6809c.1
                            have p6809_1 := h6809c.2.1
                            have p6809_2 := h6809c.2.2.1
                            have p6809_3 := h6809c.2.2.2
                            linarith only [h0, h6310, h6317, h6418, h6421, h6807, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6809_1]
                          · have p6809_0 := h6809c.1
                            have p6809_1 := h6809c.2.1
                            have p6809_2 := h6809c.2.2.1
                            have p6809_3 := h6809c.2.2.2
                            linarith only [h6311, hlam, p6809_0]
                          · have p6809_0 := h6809c.1
                            have p6809_1 := h6809c.2.1
                            have p6809_2 := h6809c.2.2.1
                            have p6809_3 := h6809c.2.2.2
                            linarith only [h6314, hlam, p6809_0]
                          · have p6809_0 := h6809c.1
                            have p6809_1 := h6809c.2.1
                            have p6809_2 := h6809c.2.2.1
                            have p6809_3 := h6809c.2.2.2
                            linarith only [h6316, hlam, p6809_0]
                          · have p6809_0 := h6809c.1
                            have p6809_1 := h6809c.2.1
                            have p6809_2 := h6809c.2.2.1
                            have p6809_3 := h6809c.2.2.2
                            linarith only [hlam, p6809_0]
                          · have p6809_0 := h6809c.1
                            have p6809_1 := h6809c.2.1
                            have p6809_2 := h6809c.2.2.1
                            have p6809_3 := h6809c.2.2.2
                            linarith only [h6318, hlam, p6809_0]
                          · have p6809_0 := h6809c.1
                            have p6809_1 := h6809c.2.1
                            have p6809_2 := h6809c.2.2.1
                            have p6809_3 := h6809c.2.2.2
                            linarith only [h6312, hlam, p6809_0]
                          · have p6809_0 := h6809c.1
                            have p6809_1 := h6809c.2.1
                            have p6809_2 := h6809c.2.2.1
                            have p6809_3 := h6809c.2.2.2
                            linarith only [h6315, hlam, p6809_1]
                          · have p6809_0 := h6809c.1
                            have p6809_1 := h6809c.2.1
                            have p6809_2 := h6809c.2.2.1
                            have p6809_3 := h6809c.2.2.2
                            linarith only [h6317, hlam, p6809_0]
                          · have p6809_0 := h6809c.1
                            have p6809_1 := h6809c.2.1
                            have p6809_2 := h6809c.2.2.1
                            have p6809_3 := h6809c.2.2.2
                            linarith only [h6316, h6418, h6421, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6809_1, u0elo4]
                          · have p6809_0 := h6809c.1
                            have p6809_1 := h6809c.2.1
                            have p6809_2 := h6809c.2.2.1
                            have p6809_3 := h6809c.2.2.2
                            linarith only [hlam, p6809_0]
          · linarith only [h0, h6315, h6420, hlam]
        · linarith only [h0, h6314, h6419, hlam]
      · linarith only [h0, h6313, h6418, hlam]
  · rcases m.htr 0 4 5 (by decide) (by decide) with h6838 | h6838
    · linarith only [h6316, h6317, h6838, hlam]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h6840 | h6840
      · rcases m.htr 1 2 4 (by decide) (by decide) with h6841 | h6841
        · rcases m.htr 1 2 5 (by decide) (by decide) with h6842 | h6842
          · rcases m.htr 1 3 4 (by decide) (by decide) with h6843 | h6843
            · rcases m.htr 1 3 5 (by decide) (by decide) with h6844 | h6844
              · linarith only [h6310, h6317, h6844, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h6846 | h6846
                · linarith only [h6311, h6838, h6846, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h6848 | h6848
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h6849 | h6849
                    · linarith only [h6310, h6317, h6840, h6849, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h6851 | h6851
                      · linarith only [h6311, h6838, h6841, h6851, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h6853 | h6853
                        · linarith only [h6310, h6838, h6840, h6848, h6853, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                        · rcases h0bigk with h6855c | h6855c | h6855c | h6855c | h6855c | h6855c | h6855c | h6855c | h6855c | h6855c | h6855c | h6855c | h6855c | h6855c | h6855c | h6855c | h6855c | h6855c | h6855c | h6855c | h6855c | h6855c | h6855c | h6855c | h6855c
                          · have p6855_0 := h6855c.1
                            have p6855_1 := h6855c.2.1
                            have p6855_2 := h6855c.2.2.1
                            have p6855_3 := h6855c.2.2.2
                            linarith only [hlam, p6855_0]
                          · have p6855_0 := h6855c.1
                            have p6855_1 := h6855c.2.1
                            have p6855_2 := h6855c.2.2.1
                            have p6855_3 := h6855c.2.2.2
                            linarith only [h0, hlam, p6855_1]
                          · have p6855_0 := h6855c.1
                            have p6855_1 := h6855c.2.1
                            have p6855_2 := h6855c.2.2.1
                            have p6855_3 := h6855c.2.2.2
                            linarith only [h0, h6316, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p6855_1]
                          · have p6855_0 := h6855c.1
                            have p6855_1 := h6855c.2.1
                            have p6855_2 := h6855c.2.2.1
                            have p6855_3 := h6855c.2.2.2
                            rcases p6855_3 (m.d 0 1) (by simp) with h6859 | h6859
                            · rcases p6855_3 (m.d 0 2) (by simp) with h6860 | h6860
                              · rcases p6855_3 (m.d 0 3) (by simp) with h6861 | h6861
                                · linarith only [h6310, h6861, hlam]
                                · linarith only [h6316, h6861, hlam]
                              · linarith only [h6314, h6860, hlam]
                            · linarith only [h6311, h6859, hlam]
                          · have p6855_0 := h6855c.1
                            have p6855_1 := h6855c.2.1
                            have p6855_2 := h6855c.2.2.1
                            have p6855_3 := h6855c.2.2.2
                            linarith only [h0, h6315, h6848, h6849, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p6855_1]
                          · have p6855_0 := h6855c.1
                            have p6855_1 := h6855c.2.1
                            have p6855_2 := h6855c.2.2.1
                            have p6855_3 := h6855c.2.2.2
                            linarith only [h6310, h6840, h6848, hc34, hlam, hphi, ht0b, ht45, ht5b, p6855_1, u0elo1]
                          · have p6855_0 := h6855c.1
                            have p6855_1 := h6855c.2.1
                            have p6855_2 := h6855c.2.2.1
                            have p6855_3 := h6855c.2.2.2
                            linarith only [hlam, p6855_0]
                          · have p6855_0 := h6855c.1
                            have p6855_1 := h6855c.2.1
                            have p6855_2 := h6855c.2.2.1
                            have p6855_3 := h6855c.2.2.2
                            linarith only [h6310, h6840, h6848, hc34, hlam, hphi, ht0b, ht45, ht5b, p6855_1, u0elo1]
                          · have p6855_0 := h6855c.1
                            have p6855_1 := h6855c.2.1
                            have p6855_2 := h6855c.2.2.1
                            have p6855_3 := h6855c.2.2.2
                            rcases p6855_3 (m.d 0 1) (by simp) with h6870 | h6870
                            · linarith only [h0, h6870, hlam]
                            · linarith only [h6311, h6870, hlam]
                          · have p6855_0 := h6855c.1
                            have p6855_1 := h6855c.2.1
                            have p6855_2 := h6855c.2.2.1
                            have p6855_3 := h6855c.2.2.2
                            linarith only [h6310, h6317, h6840, h6848, hc34, hlam, hphi, ht0b, ht45, ht5b, p6855_1, u0elo1]
                          · have p6855_0 := h6855c.1
                            have p6855_1 := h6855c.2.1
                            have p6855_2 := h6855c.2.2.1
                            have p6855_3 := h6855c.2.2.2
                            linarith only [h6310, hlam, p6855_1]
                          · have p6855_0 := h6855c.1
                            have p6855_1 := h6855c.2.1
                            have p6855_2 := h6855c.2.2.1
                            have p6855_3 := h6855c.2.2.2
                            linarith only [h6313, hlam, p6855_1]
                          · have p6855_0 := h6855c.1
                            have p6855_1 := h6855c.2.1
                            have p6855_2 := h6855c.2.2.1
                            have p6855_3 := h6855c.2.2.2
                            linarith only [hlam, p6855_0]
                          · have p6855_0 := h6855c.1
                            have p6855_1 := h6855c.2.1
                            have p6855_2 := h6855c.2.2.1
                            have p6855_3 := h6855c.2.2.2
                            linarith only [h6311, h6317, h6841, h6848, h6853, hc34, hc45, hlam, hphi, p6855_1]
                          · have p6855_0 := h6855c.1
                            have p6855_1 := h6855c.2.1
                            have p6855_2 := h6855c.2.2.1
                            have p6855_3 := h6855c.2.2.2
                            linarith only [h6317, hlam, p6855_1]
                          · have p6855_0 := h6855c.1
                            have p6855_1 := h6855c.2.1
                            have p6855_2 := h6855c.2.2.1
                            have p6855_3 := h6855c.2.2.2
                            linarith only [h6311, hlam, p6855_0]
                          · have p6855_0 := h6855c.1
                            have p6855_1 := h6855c.2.1
                            have p6855_2 := h6855c.2.2.1
                            have p6855_3 := h6855c.2.2.2
                            linarith only [h6314, hlam, p6855_0]
                          · have p6855_0 := h6855c.1
                            have p6855_1 := h6855c.2.1
                            have p6855_2 := h6855c.2.2.1
                            have p6855_3 := h6855c.2.2.2
                            linarith only [h6316, hlam, p6855_0]
                          · have p6855_0 := h6855c.1
                            have p6855_1 := h6855c.2.1
                            have p6855_2 := h6855c.2.2.1
                            have p6855_3 := h6855c.2.2.2
                            linarith only [hlam, p6855_0]
                          · have p6855_0 := h6855c.1
                            have p6855_1 := h6855c.2.1
                            have p6855_2 := h6855c.2.2.1
                            have p6855_3 := h6855c.2.2.2
                            linarith only [h6838, hlam, p6855_0]
                          · have p6855_0 := h6855c.1
                            have p6855_1 := h6855c.2.1
                            have p6855_2 := h6855c.2.2.1
                            have p6855_3 := h6855c.2.2.2
                            linarith only [h6312, hlam, p6855_0]
                          · have p6855_0 := h6855c.1
                            have p6855_1 := h6855c.2.1
                            have p6855_2 := h6855c.2.2.1
                            have p6855_3 := h6855c.2.2.2
                            linarith only [h6315, hlam, p6855_1]
                          · have p6855_0 := h6855c.1
                            have p6855_1 := h6855c.2.1
                            have p6855_2 := h6855c.2.2.1
                            have p6855_3 := h6855c.2.2.2
                            linarith only [h6310, h6840, h6848, hc34, hlam, hphi, ht0b, ht45, ht5b, p6855_1, u0elo4]
                          · have p6855_0 := h6855c.1
                            have p6855_1 := h6855c.2.1
                            have p6855_2 := h6855c.2.2.1
                            have p6855_3 := h6855c.2.2.2
                            rcases p6855_3 (m.d 0 1) (by simp) with h6887 | h6887
                            · rcases p6855_3 (m.d 0 2) (by simp) with h6888 | h6888
                              · rcases p6855_3 (m.d 0 3) (by simp) with h6889 | h6889
                                · linarith only [h6317, h6889, hlam]
                                · linarith only [h6316, h6889, hlam]
                              · linarith only [h6314, h6888, hlam]
                            · linarith only [h6311, h6887, hlam]
                          · have p6855_0 := h6855c.1
                            have p6855_1 := h6855c.2.1
                            have p6855_2 := h6855c.2.2.1
                            have p6855_3 := h6855c.2.2.2
                            linarith only [hlam, p6855_0]
                  · linarith only [h6316, h6317, h6848, hc23, hc35, hlam, hphi]
            · linarith only [h6316, h6317, h6843, hc13, hc35, hlam, hphi]
          · linarith only [h0, h6315, h6842, hlam]
        · linarith only [h0, h6314, h6841, hlam]
      · linarith only [h0, h6313, h6840, hlam]

end R2N4
