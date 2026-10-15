import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6904000 in
set_option maxHeartbeats 6904000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s17_x1_x1_x1_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg9 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h9268 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h10760 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (h11236 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
    (h11248 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h11249 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
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
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  have h9 := hg9
  rcases m.htr 1 4 5 (by decide) (by decide) with h11250 | h11250
  · linarith only [h11250, h2, h9, hlam]
  · rcases m.htr 2 3 4 (by decide) (by decide) with h11252 | h11252
    · rcases m.htr 2 3 5 (by decide) (by decide) with h11253 | h11253
      · rcases m.htr 2 4 5 (by decide) (by decide) with h11254 | h11254
        · linarith only [h11254, h5, h9, hlam]
        · rcases m.htr 3 4 5 (by decide) (by decide) with h11256 | h11256
          · linarith only [h1, h11248, h11256, h5, h9, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
          · rcases h1bigk with h11258c | h11258c | h11258c | h11258c | h11258c | h11258c | h11258c | h11258c | h11258c | h11258c | h11258c | h11258c | h11258c | h11258c | h11258c | h11258c | h11258c | h11258c | h11258c | h11258c | h11258c | h11258c | h11258c | h11258c | h11258c
            · have p11258_0 := h11258c.1
              have p11258_1 := h11258c.2.1
              have p11258_2 := h11258c.2.2.1
              have p11258_3 := h11258c.2.2.2
              linarith only [hlam, p11258_0]
            · have p11258_0 := h11258c.1
              have p11258_1 := h11258c.2.1
              have p11258_2 := h11258c.2.2.1
              have p11258_3 := h11258c.2.2.2
              rcases p11258_3 (m.d 0 1) (by simp) with h11260 | h11260
              · rcases p11258_3 (m.d 1 2) (by simp) with h11261 | h11261
                · linarith only [h11261, hlam, p11258_0]
                · rcases p11258_3 (m.d 1 3) (by simp) with h11263 | h11263
                  · linarith only [h1, h11263, hlam]
                  · linarith only [h11263, h9268, hlam]
              · linarith only [h11260, hlam, p11258_0]
            · have p11258_0 := h11258c.1
              have p11258_1 := h11258c.2.1
              have p11258_2 := h11258c.2.2.1
              have p11258_3 := h11258c.2.2.2
              rcases p11258_3 (m.d 0 1) (by simp) with h11267 | h11267
              · rcases p11258_3 (m.d 1 2) (by simp) with h11268 | h11268
                · linarith only [h0, h11268, hlam]
                · rcases p11258_3 (m.d 1 3) (by simp) with h11270 | h11270
                  · linarith only [h11270, hlam, p11258_0]
                  · rcases p11258_3 (m.d 1 4) (by simp) with h11272 | h11272
                    · linarith only [h11272, h2, hlam]
                    · rcases p11258_3 (m.d 1 5) (by simp) with h11274 | h11274
                      · linarith only [h11274, h3, hlam]
                      · rcases h1emax with h11276 | h11276 | h11276 | h11276 | h11276
                        · linarith only [h11249, h11256, h11276, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p11258_1]
                        · rcases h2bigk with h11278c | h11278c | h11278c | h11278c | h11278c | h11278c | h11278c | h11278c | h11278c | h11278c | h11278c | h11278c | h11278c | h11278c | h11278c | h11278c | h11278c | h11278c | h11278c | h11278c | h11278c | h11278c | h11278c | h11278c | h11278c
                          · have p11278_0 := h11278c.1
                            have p11278_1 := h11278c.2.1
                            have p11278_2 := h11278c.2.2.1
                            have p11278_3 := h11278c.2.2.2
                            linarith only [hlam, p11278_0]
                          · have p11278_0 := h11278c.1
                            have p11278_1 := h11278c.2.1
                            have p11278_2 := h11278c.2.2.1
                            have p11278_3 := h11278c.2.2.2
                            rcases p11278_3 (m.d 0 2) (by simp) with h11280 | h11280
                            · rcases p11278_3 (m.d 1 2) (by simp) with h11281 | h11281
                              · linarith only [h0, h11281, hlam]
                              · rcases p11278_3 (m.d 2 3) (by simp) with h11283 | h11283
                                · linarith only [h11283, h4, hlam]
                                · linarith only [h11283, h9268, hlam]
                            · linarith only [h0, h11280, hlam]
                          · have p11278_0 := h11278c.1
                            have p11278_1 := h11278c.2.1
                            have p11278_2 := h11278c.2.2.1
                            have p11278_3 := h11278c.2.2.2
                            rcases p11278_3 (m.d 0 2) (by simp) with h11287 | h11287
                            · rcases p11278_3 (m.d 1 2) (by simp) with h11288 | h11288
                              · linarith only [h0, h11288, hlam]
                              · rcases p11278_3 (m.d 2 3) (by simp) with h11290 | h11290
                                · linarith only [h11290, hlam, p11278_0]
                                · rcases p11278_3 (m.d 2 4) (by simp) with h11292 | h11292
                                  · linarith only [h11292, h5, hlam]
                                  · rcases p11278_3 (m.d 2 5) (by simp) with h11294 | h11294
                                    · linarith only [h11294, h6, hlam]
                                    · rcases h4bigk with h11296c | h11296c | h11296c | h11296c | h11296c | h11296c | h11296c | h11296c | h11296c | h11296c | h11296c | h11296c | h11296c | h11296c | h11296c | h11296c | h11296c | h11296c | h11296c | h11296c | h11296c | h11296c | h11296c | h11296c | h11296c
                                      · have p11296_0 := h11296c.1
                                        have p11296_1 := h11296c.2.1
                                        have p11296_2 := h11296c.2.2.1
                                        have p11296_3 := h11296c.2.2.2
                                        linarith only [hlam, p11296_0]
                                      · have p11296_0 := h11296c.1
                                        have p11296_1 := h11296c.2.1
                                        have p11296_2 := h11296c.2.2.1
                                        have p11296_3 := h11296c.2.2.2
                                        linarith only [h9, hc14, hc45, hlam, hphi, p11296_1]
                                      · have p11296_0 := h11296c.1
                                        have p11296_1 := h11296c.2.1
                                        have p11296_2 := h11296c.2.2.1
                                        have p11296_3 := h11296c.2.2.2
                                        linarith only [h10760, h9, hc12, hc45, hlam, hphi, ht23, ht34, p11296_1]
                                      · have p11296_0 := h11296c.1
                                        have p11296_1 := h11296c.2.1
                                        have p11296_2 := h11296c.2.2.1
                                        have p11296_3 := h11296c.2.2.2
                                        linarith only [h9, hc34, hc45, hlam, hphi, p11296_1]
                                      · have p11296_0 := h11296c.1
                                        have p11296_1 := h11296c.2.1
                                        have p11296_2 := h11296c.2.2.1
                                        have p11296_3 := h11296c.2.2.2
                                        linarith only [h9, hlam, p11296_0]
                                      · have p11296_0 := h11296c.1
                                        have p11296_1 := h11296c.2.1
                                        have p11296_2 := h11296c.2.2.1
                                        have p11296_3 := h11296c.2.2.2
                                        linarith only [h2, hlam, p11296_0]
                                      · have p11296_0 := h11296c.1
                                        have p11296_1 := h11296c.2.1
                                        have p11296_2 := h11296c.2.2.1
                                        have p11296_3 := h11296c.2.2.2
                                        linarith only [hlam, p11296_0]
                                      · have p11296_0 := h11296c.1
                                        have p11296_1 := h11296c.2.1
                                        have p11296_2 := h11296c.2.2.1
                                        have p11296_3 := h11296c.2.2.2
                                        linarith only [h10760, hlam, p11296_1]
                                      · have p11296_0 := h11296c.1
                                        have p11296_1 := h11296c.2.1
                                        have p11296_2 := h11296c.2.2.1
                                        have p11296_3 := h11296c.2.2.2
                                        linarith only [h2, h9, hc34, hc45, hlam, hphi, p11296_1]
                                      · have p11296_0 := h11296c.1
                                        have p11296_1 := h11296c.2.1
                                        have p11296_2 := h11296c.2.2.1
                                        have p11296_3 := h11296c.2.2.2
                                        linarith only [h11250, hlam, p11296_0]
                                      · have p11296_0 := h11296c.1
                                        have p11296_1 := h11296c.2.1
                                        have p11296_2 := h11296c.2.2.1
                                        have p11296_3 := h11296c.2.2.2
                                        linarith only [h5, hlam, p11296_0]
                                      · have p11296_0 := h11296c.1
                                        have p11296_1 := h11296c.2.1
                                        have p11296_2 := h11296c.2.2.1
                                        have p11296_3 := h11296c.2.2.2
                                        linarith only [h0, h11253, h11254, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p11278_1, p11296_1]
                                      · have p11296_0 := h11296c.1
                                        have p11296_1 := h11296c.2.1
                                        have p11296_2 := h11296c.2.2.1
                                        have p11296_3 := h11296c.2.2.2
                                        linarith only [hlam, p11296_0]
                                      · have p11296_0 := h11296c.1
                                        have p11296_1 := h11296c.2.1
                                        have p11296_2 := h11296c.2.2.1
                                        have p11296_3 := h11296c.2.2.2
                                        linarith only [h0, h11253, h11254, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p11278_1, p11296_1]
                                      · have p11296_0 := h11296c.1
                                        have p11296_1 := h11296c.2.1
                                        have p11296_2 := h11296c.2.2.1
                                        have p11296_3 := h11296c.2.2.2
                                        linarith only [h11254, hlam, p11296_0]
                                      · have p11296_0 := h11296c.1
                                        have p11296_1 := h11296c.2.1
                                        have p11296_2 := h11296c.2.2.1
                                        have p11296_3 := h11296c.2.2.2
                                        linarith only [h7, hlam, p11296_0]
                                      · have p11296_0 := h11296c.1
                                        have p11296_1 := h11296c.2.1
                                        have p11296_2 := h11296c.2.2.1
                                        have p11296_3 := h11296c.2.2.2
                                        linarith only [h11248, hlam, p11296_0]
                                      · have p11296_0 := h11296c.1
                                        have p11296_1 := h11296c.2.1
                                        have p11296_2 := h11296c.2.2.1
                                        have p11296_3 := h11296c.2.2.2
                                        linarith only [h11252, hlam, p11296_0]
                                      · have p11296_0 := h11296c.1
                                        have p11296_1 := h11296c.2.1
                                        have p11296_2 := h11296c.2.2.1
                                        have p11296_3 := h11296c.2.2.2
                                        linarith only [hlam, p11296_0]
                                      · have p11296_0 := h11296c.1
                                        have p11296_1 := h11296c.2.1
                                        have p11296_2 := h11296c.2.2.1
                                        have p11296_3 := h11296c.2.2.2
                                        linarith only [h11256, hlam, p11296_0]
                                      · have p11296_0 := h11296c.1
                                        have p11296_1 := h11296c.2.1
                                        have p11296_2 := h11296c.2.2.1
                                        have p11296_3 := h11296c.2.2.2
                                        linarith only [h10760, h5, hc12, hc45, hlam, hphi, ht23, ht34, p11296_1]
                                      · have p11296_0 := h11296c.1
                                        have p11296_1 := h11296c.2.1
                                        have p11296_2 := h11296c.2.2.1
                                        have p11296_3 := h11296c.2.2.2
                                        rcases p11296_3 (m.d 0 4) (by simp) with h11318 | h11318
                                        · linarith only [h11318, h9, hlam]
                                        · linarith only [h11318, h2, hlam]
                                      · have p11296_0 := h11296c.1
                                        have p11296_1 := h11296c.2.1
                                        have p11296_2 := h11296c.2.2.1
                                        have p11296_3 := h11296c.2.2.2
                                        linarith only [h10760, hc12, hc45, hlam, hphi, ht23, ht34, p11296_1]
                                      · have p11296_0 := h11296c.1
                                        have p11296_1 := h11296c.2.1
                                        have p11296_2 := h11296c.2.2.1
                                        have p11296_3 := h11296c.2.2.2
                                        rcases p11296_3 (m.d 0 4) (by simp) with h11322 | h11322
                                        · linarith only [h11322, h9, hlam]
                                        · linarith only [h11322, h7, hlam]
                                      · have p11296_0 := h11296c.1
                                        have p11296_1 := h11296c.2.1
                                        have p11296_2 := h11296c.2.2.1
                                        have p11296_3 := h11296c.2.2.2
                                        linarith only [hlam, p11296_0]
                            · linarith only [h11287, hlam, p11278_0]
                          · have p11278_0 := h11278c.1
                            have p11278_1 := h11278c.2.1
                            have p11278_2 := h11278c.2.2.1
                            have p11278_3 := h11278c.2.2.2
                            rcases p11278_3 (m.d 0 2) (by simp) with h11327 | h11327
                            · rcases p11278_3 (m.d 1 2) (by simp) with h11328 | h11328
                              · linarith only [h0, h11328, hlam]
                              · rcases p11278_3 (m.d 2 3) (by simp) with h11330 | h11330
                                · linarith only [h11330, h4, hlam]
                                · linarith only [h11252, h11330, hlam]
                            · linarith only [h11327, hlam, p11278_0]
                          · have p11278_0 := h11278c.1
                            have p11278_1 := h11278c.2.1
                            have p11278_2 := h11278c.2.2.1
                            have p11278_3 := h11278c.2.2.2
                            rcases p11278_3 (m.d 0 2) (by simp) with h11334 | h11334
                            · rcases p11278_3 (m.d 1 2) (by simp) with h11335 | h11335
                              · linarith only [h0, h11335, hlam]
                              · rcases p11278_3 (m.d 2 3) (by simp) with h11337 | h11337
                                · linarith only [h11337, h4, hlam]
                                · linarith only [h11253, h11337, hlam]
                            · linarith only [h11334, hlam, p11278_0]
                          · have p11278_0 := h11278c.1
                            have p11278_1 := h11278c.2.1
                            have p11278_2 := h11278c.2.2.1
                            have p11278_3 := h11278c.2.2.2
                            linarith only [h0, hlam, p11278_1]
                          · have p11278_0 := h11278c.1
                            have p11278_1 := h11278c.2.1
                            have p11278_2 := h11278c.2.2.1
                            have p11278_3 := h11278c.2.2.2
                            linarith only [hlam, p11278_0]
                          · have p11278_0 := h11278c.1
                            have p11278_1 := h11278c.2.1
                            have p11278_2 := h11278c.2.2.1
                            have p11278_3 := h11278c.2.2.2
                            linarith only [h9268, hlam, p11278_0]
                          · have p11278_0 := h11278c.1
                            have p11278_1 := h11278c.2.1
                            have p11278_2 := h11278c.2.2.1
                            have p11278_3 := h11278c.2.2.2
                            linarith only [h10760, hlam, p11278_0]
                          · have p11278_0 := h11278c.1
                            have p11278_1 := h11278c.2.1
                            have p11278_2 := h11278c.2.2.1
                            have p11278_3 := h11278c.2.2.2
                            linarith only [h11236, hlam, p11278_0]
                          · have p11278_0 := h11278c.1
                            have p11278_1 := h11278c.2.1
                            have p11278_2 := h11278c.2.2.1
                            have p11278_3 := h11278c.2.2.2
                            linarith only [h4, hlam, p11278_0]
                          · have p11278_0 := h11278c.1
                            have p11278_1 := h11278c.2.1
                            have p11278_2 := h11278c.2.2.1
                            have p11278_3 := h11278c.2.2.2
                            rcases p11278_3 (m.d 0 2) (by simp) with h11347 | h11347
                            · rcases p11278_3 (m.d 1 2) (by simp) with h11348 | h11348
                              · linarith only [h11348, hlam, p11278_0]
                              · rcases p11278_3 (m.d 2 3) (by simp) with h11350 | h11350
                                · rcases p11278_3 (m.d 2 4) (by simp) with h11351 | h11351
                                  · linarith only [h11252, h11351, hlam]
                                  · linarith only [h10760, h11351, hlam]
                                · linarith only [h11350, hlam, p11278_0]
                            · linarith only [h0, h11347, hlam]
                          · have p11278_0 := h11278c.1
                            have p11278_1 := h11278c.2.1
                            have p11278_2 := h11278c.2.2.1
                            have p11278_3 := h11278c.2.2.2
                            linarith only [hlam, p11278_0]
                          · have p11278_0 := h11278c.1
                            have p11278_1 := h11278c.2.1
                            have p11278_2 := h11278c.2.2.1
                            have p11278_3 := h11278c.2.2.2
                            linarith only [h10760, hc12, hc23, hlam, hphi, p11278_1]
                          · have p11278_0 := h11278c.1
                            have p11278_1 := h11278c.2.1
                            have p11278_2 := h11278c.2.2.1
                            have p11278_3 := h11278c.2.2.2
                            linarith only [h0, h11236, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p11278_1]
                          · have p11278_0 := h11278c.1
                            have p11278_1 := h11278c.2.1
                            have p11278_2 := h11278c.2.2.1
                            have p11278_3 := h11278c.2.2.2
                            linarith only [h5, hlam, p11278_0]
                          · have p11278_0 := h11278c.1
                            have p11278_1 := h11278c.2.1
                            have p11278_2 := h11278c.2.2.1
                            have p11278_3 := h11278c.2.2.2
                            linarith only [h5, h9, hc12, hc45, hlam, hphi, ht23, ht34, p11278_1]
                          · have p11278_0 := h11278c.1
                            have p11278_1 := h11278c.2.1
                            have p11278_2 := h11278c.2.2.1
                            have p11278_3 := h11278c.2.2.2
                            linarith only [h11252, hlam, p11278_0]
                          · have p11278_0 := h11278c.1
                            have p11278_1 := h11278c.2.1
                            have p11278_2 := h11278c.2.2.1
                            have p11278_3 := h11278c.2.2.2
                            linarith only [hlam, p11278_0]
                          · have p11278_0 := h11278c.1
                            have p11278_1 := h11278c.2.1
                            have p11278_2 := h11278c.2.2.1
                            have p11278_3 := h11278c.2.2.2
                            linarith only [h11254, hlam, p11278_0]
                          · have p11278_0 := h11278c.1
                            have p11278_1 := h11278c.2.1
                            have p11278_2 := h11278c.2.2.1
                            have p11278_3 := h11278c.2.2.2
                            linarith only [h6, hlam, p11278_0]
                          · have p11278_0 := h11278c.1
                            have p11278_1 := h11278c.2.1
                            have p11278_2 := h11278c.2.2.1
                            have p11278_3 := h11278c.2.2.2
                            rcases p11278_3 (m.d 0 2) (by simp) with h11365 | h11365
                            · rcases p11278_3 (m.d 1 2) (by simp) with h11366 | h11366
                              · linarith only [h11366, hlam, p11278_0]
                              · rcases p11278_3 (m.d 2 3) (by simp) with h11368 | h11368
                                · rcases p11278_3 (m.d 2 4) (by simp) with h11369 | h11369
                                  · linarith only [h11254, h11369, hlam]
                                  · linarith only [h10760, h11369, hlam]
                                · linarith only [h11368, h9268, hlam]
                            · linarith only [h0, h11365, hlam]
                          · have p11278_0 := h11278c.1
                            have p11278_1 := h11278c.2.1
                            have p11278_2 := h11278c.2.2.1
                            have p11278_3 := h11278c.2.2.2
                            linarith only [h11253, hlam, p11278_0]
                          · have p11278_0 := h11278c.1
                            have p11278_1 := h11278c.2.1
                            have p11278_2 := h11278c.2.2.1
                            have p11278_3 := h11278c.2.2.2
                            linarith only [h0, h10760, h6, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p11278_1]
                          · have p11278_0 := h11278c.1
                            have p11278_1 := h11278c.2.1
                            have p11278_2 := h11278c.2.2.1
                            have p11278_3 := h11278c.2.2.2
                            linarith only [hlam, p11278_0]
                        · rcases h2bigk with h11377c | h11377c | h11377c | h11377c | h11377c | h11377c | h11377c | h11377c | h11377c | h11377c | h11377c | h11377c | h11377c | h11377c | h11377c | h11377c | h11377c | h11377c | h11377c | h11377c | h11377c | h11377c | h11377c | h11377c | h11377c
                          · have p11377_0 := h11377c.1
                            have p11377_1 := h11377c.2.1
                            have p11377_2 := h11377c.2.2.1
                            have p11377_3 := h11377c.2.2.2
                            linarith only [hlam, p11377_0]
                          · have p11377_0 := h11377c.1
                            have p11377_1 := h11377c.2.1
                            have p11377_2 := h11377c.2.2.1
                            have p11377_3 := h11377c.2.2.2
                            rcases p11377_3 (m.d 0 2) (by simp) with h11379 | h11379
                            · rcases p11377_3 (m.d 1 2) (by simp) with h11380 | h11380
                              · linarith only [h0, h11380, hlam]
                              · rcases p11377_3 (m.d 2 3) (by simp) with h11382 | h11382
                                · linarith only [h11382, h4, hlam]
                                · linarith only [h11382, h9268, hlam]
                            · linarith only [h0, h11379, hlam]
                          · have p11377_0 := h11377c.1
                            have p11377_1 := h11377c.2.1
                            have p11377_2 := h11377c.2.2.1
                            have p11377_3 := h11377c.2.2.2
                            rcases p11377_3 (m.d 0 2) (by simp) with h11386 | h11386
                            · rcases p11377_3 (m.d 1 2) (by simp) with h11387 | h11387
                              · linarith only [h0, h11387, hlam]
                              · rcases p11377_3 (m.d 2 3) (by simp) with h11389 | h11389
                                · linarith only [h11389, hlam, p11377_0]
                                · rcases p11377_3 (m.d 2 4) (by simp) with h11391 | h11391
                                  · linarith only [h11391, h5, hlam]
                                  · rcases p11377_3 (m.d 2 5) (by simp) with h11393 | h11393
                                    · linarith only [h11393, h6, hlam]
                                    · rcases h4bigk with h11395c | h11395c | h11395c | h11395c | h11395c | h11395c | h11395c | h11395c | h11395c | h11395c | h11395c | h11395c | h11395c | h11395c | h11395c | h11395c | h11395c | h11395c | h11395c | h11395c | h11395c | h11395c | h11395c | h11395c | h11395c
                                      · have p11395_0 := h11395c.1
                                        have p11395_1 := h11395c.2.1
                                        have p11395_2 := h11395c.2.2.1
                                        have p11395_3 := h11395c.2.2.2
                                        linarith only [hlam, p11395_0]
                                      · have p11395_0 := h11395c.1
                                        have p11395_1 := h11395c.2.1
                                        have p11395_2 := h11395c.2.2.1
                                        have p11395_3 := h11395c.2.2.2
                                        linarith only [h10760, h9, hc12, hc45, hlam, hphi, ht23, ht34, p11395_1]
                                      · have p11395_0 := h11395c.1
                                        have p11395_1 := h11395c.2.1
                                        have p11395_2 := h11395c.2.2.1
                                        have p11395_3 := h11395c.2.2.2
                                        linarith only [h9, hc24, hc45, hlam, hphi, p11395_1]
                                      · have p11395_0 := h11395c.1
                                        have p11395_1 := h11395c.2.1
                                        have p11395_2 := h11395c.2.2.1
                                        have p11395_3 := h11395c.2.2.2
                                        linarith only [h9, hc34, hc45, hlam, hphi, p11395_1]
                                      · have p11395_0 := h11395c.1
                                        have p11395_1 := h11395c.2.1
                                        have p11395_2 := h11395c.2.2.1
                                        have p11395_3 := h11395c.2.2.2
                                        linarith only [h9, hlam, p11395_0]
                                      · have p11395_0 := h11395c.1
                                        have p11395_1 := h11395c.2.1
                                        have p11395_2 := h11395c.2.2.1
                                        have p11395_3 := h11395c.2.2.2
                                        linarith only [h2, hlam, p11395_0]
                                      · have p11395_0 := h11395c.1
                                        have p11395_1 := h11395c.2.1
                                        have p11395_2 := h11395c.2.2.1
                                        have p11395_3 := h11395c.2.2.2
                                        linarith only [hlam, p11395_0]
                                      · have p11395_0 := h11395c.1
                                        have p11395_1 := h11395c.2.1
                                        have p11395_2 := h11395c.2.2.1
                                        have p11395_3 := h11395c.2.2.2
                                        linarith only [h10760, hlam, p11395_1]
                                      · have p11395_0 := h11395c.1
                                        have p11395_1 := h11395c.2.1
                                        have p11395_2 := h11395c.2.2.1
                                        have p11395_3 := h11395c.2.2.2
                                        linarith only [h2, h9, hc34, hc45, hlam, hphi, p11395_1]
                                      · have p11395_0 := h11395c.1
                                        have p11395_1 := h11395c.2.1
                                        have p11395_2 := h11395c.2.2.1
                                        have p11395_3 := h11395c.2.2.2
                                        linarith only [h11250, hlam, p11395_0]
                                      · have p11395_0 := h11395c.1
                                        have p11395_1 := h11395c.2.1
                                        have p11395_2 := h11395c.2.2.1
                                        have p11395_3 := h11395c.2.2.2
                                        linarith only [h5, hlam, p11395_0]
                                      · have p11395_0 := h11395c.1
                                        have p11395_1 := h11395c.2.1
                                        have p11395_2 := h11395c.2.2.1
                                        have p11395_3 := h11395c.2.2.2
                                        linarith only [h5, h9, hc14, hc45, hlam, hphi, p11395_1]
                                      · have p11395_0 := h11395c.1
                                        have p11395_1 := h11395c.2.1
                                        have p11395_2 := h11395c.2.2.1
                                        have p11395_3 := h11395c.2.2.2
                                        linarith only [hlam, p11395_0]
                                      · have p11395_0 := h11395c.1
                                        have p11395_1 := h11395c.2.1
                                        have p11395_2 := h11395c.2.2.1
                                        have p11395_3 := h11395c.2.2.2
                                        linarith only [h0, h11252, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p11377_1, p11395_1]
                                      · have p11395_0 := h11395c.1
                                        have p11395_1 := h11395c.2.1
                                        have p11395_2 := h11395c.2.2.1
                                        have p11395_3 := h11395c.2.2.2
                                        linarith only [h11254, hlam, p11395_0]
                                      · have p11395_0 := h11395c.1
                                        have p11395_1 := h11395c.2.1
                                        have p11395_2 := h11395c.2.2.1
                                        have p11395_3 := h11395c.2.2.2
                                        linarith only [h7, hlam, p11395_0]
                                      · have p11395_0 := h11395c.1
                                        have p11395_1 := h11395c.2.1
                                        have p11395_2 := h11395c.2.2.1
                                        have p11395_3 := h11395c.2.2.2
                                        linarith only [h11248, hlam, p11395_0]
                                      · have p11395_0 := h11395c.1
                                        have p11395_1 := h11395c.2.1
                                        have p11395_2 := h11395c.2.2.1
                                        have p11395_3 := h11395c.2.2.2
                                        linarith only [h11252, hlam, p11395_0]
                                      · have p11395_0 := h11395c.1
                                        have p11395_1 := h11395c.2.1
                                        have p11395_2 := h11395c.2.2.1
                                        have p11395_3 := h11395c.2.2.2
                                        linarith only [hlam, p11395_0]
                                      · have p11395_0 := h11395c.1
                                        have p11395_1 := h11395c.2.1
                                        have p11395_2 := h11395c.2.2.1
                                        have p11395_3 := h11395c.2.2.2
                                        linarith only [h11256, hlam, p11395_0]
                                      · have p11395_0 := h11395c.1
                                        have p11395_1 := h11395c.2.1
                                        have p11395_2 := h11395c.2.2.1
                                        have p11395_3 := h11395c.2.2.2
                                        linarith only [h10760, h5, hc12, hc45, hlam, hphi, ht23, ht34, p11395_1]
                                      · have p11395_0 := h11395c.1
                                        have p11395_1 := h11395c.2.1
                                        have p11395_2 := h11395c.2.2.1
                                        have p11395_3 := h11395c.2.2.2
                                        rcases p11395_3 (m.d 0 4) (by simp) with h11417 | h11417
                                        · linarith only [h11417, h9, hlam]
                                        · linarith only [h11417, h2, hlam]
                                      · have p11395_0 := h11395c.1
                                        have p11395_1 := h11395c.2.1
                                        have p11395_2 := h11395c.2.2.1
                                        have p11395_3 := h11395c.2.2.2
                                        linarith only [h10760, hc12, hc45, hlam, hphi, ht23, ht34, p11395_1]
                                      · have p11395_0 := h11395c.1
                                        have p11395_1 := h11395c.2.1
                                        have p11395_2 := h11395c.2.2.1
                                        have p11395_3 := h11395c.2.2.2
                                        rcases p11395_3 (m.d 0 4) (by simp) with h11421 | h11421
                                        · linarith only [h11421, h9, hlam]
                                        · linarith only [h11421, h7, hlam]
                                      · have p11395_0 := h11395c.1
                                        have p11395_1 := h11395c.2.1
                                        have p11395_2 := h11395c.2.2.1
                                        have p11395_3 := h11395c.2.2.2
                                        linarith only [hlam, p11395_0]
                            · linarith only [h11386, hlam, p11377_0]
                          · have p11377_0 := h11377c.1
                            have p11377_1 := h11377c.2.1
                            have p11377_2 := h11377c.2.2.1
                            have p11377_3 := h11377c.2.2.2
                            rcases p11377_3 (m.d 0 2) (by simp) with h11426 | h11426
                            · rcases p11377_3 (m.d 1 2) (by simp) with h11427 | h11427
                              · linarith only [h0, h11427, hlam]
                              · rcases p11377_3 (m.d 2 3) (by simp) with h11429 | h11429
                                · linarith only [h11429, h4, hlam]
                                · linarith only [h11252, h11429, hlam]
                            · linarith only [h11426, hlam, p11377_0]
                          · have p11377_0 := h11377c.1
                            have p11377_1 := h11377c.2.1
                            have p11377_2 := h11377c.2.2.1
                            have p11377_3 := h11377c.2.2.2
                            rcases p11377_3 (m.d 0 2) (by simp) with h11433 | h11433
                            · rcases p11377_3 (m.d 1 2) (by simp) with h11434 | h11434
                              · linarith only [h0, h11434, hlam]
                              · rcases p11377_3 (m.d 2 3) (by simp) with h11436 | h11436
                                · linarith only [h11436, h4, hlam]
                                · linarith only [h11253, h11436, hlam]
                            · linarith only [h11433, hlam, p11377_0]
                          · have p11377_0 := h11377c.1
                            have p11377_1 := h11377c.2.1
                            have p11377_2 := h11377c.2.2.1
                            have p11377_3 := h11377c.2.2.2
                            linarith only [h0, hlam, p11377_1]
                          · have p11377_0 := h11377c.1
                            have p11377_1 := h11377c.2.1
                            have p11377_2 := h11377c.2.2.1
                            have p11377_3 := h11377c.2.2.2
                            linarith only [hlam, p11377_0]
                          · have p11377_0 := h11377c.1
                            have p11377_1 := h11377c.2.1
                            have p11377_2 := h11377c.2.2.1
                            have p11377_3 := h11377c.2.2.2
                            linarith only [h9268, hlam, p11377_0]
                          · have p11377_0 := h11377c.1
                            have p11377_1 := h11377c.2.1
                            have p11377_2 := h11377c.2.2.1
                            have p11377_3 := h11377c.2.2.2
                            linarith only [h10760, hlam, p11377_0]
                          · have p11377_0 := h11377c.1
                            have p11377_1 := h11377c.2.1
                            have p11377_2 := h11377c.2.2.1
                            have p11377_3 := h11377c.2.2.2
                            linarith only [h11236, hlam, p11377_0]
                          · have p11377_0 := h11377c.1
                            have p11377_1 := h11377c.2.1
                            have p11377_2 := h11377c.2.2.1
                            have p11377_3 := h11377c.2.2.2
                            linarith only [h4, hlam, p11377_0]
                          · have p11377_0 := h11377c.1
                            have p11377_1 := h11377c.2.1
                            have p11377_2 := h11377c.2.2.1
                            have p11377_3 := h11377c.2.2.2
                            rcases p11377_3 (m.d 0 2) (by simp) with h11446 | h11446
                            · rcases p11377_3 (m.d 1 2) (by simp) with h11447 | h11447
                              · linarith only [h11447, hlam, p11377_0]
                              · rcases p11377_3 (m.d 2 3) (by simp) with h11449 | h11449
                                · rcases p11377_3 (m.d 2 4) (by simp) with h11450 | h11450
                                  · linarith only [h11252, h11450, hlam]
                                  · linarith only [h10760, h11450, hlam]
                                · linarith only [h11449, hlam, p11377_0]
                            · linarith only [h0, h11446, hlam]
                          · have p11377_0 := h11377c.1
                            have p11377_1 := h11377c.2.1
                            have p11377_2 := h11377c.2.2.1
                            have p11377_3 := h11377c.2.2.2
                            linarith only [hlam, p11377_0]
                          · have p11377_0 := h11377c.1
                            have p11377_1 := h11377c.2.1
                            have p11377_2 := h11377c.2.2.1
                            have p11377_3 := h11377c.2.2.2
                            linarith only [h10760, hc12, hc23, hlam, hphi, p11377_1]
                          · have p11377_0 := h11377c.1
                            have p11377_1 := h11377c.2.1
                            have p11377_2 := h11377c.2.2.1
                            have p11377_3 := h11377c.2.2.2
                            linarith only [h0, h11236, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p11377_1]
                          · have p11377_0 := h11377c.1
                            have p11377_1 := h11377c.2.1
                            have p11377_2 := h11377c.2.2.1
                            have p11377_3 := h11377c.2.2.2
                            linarith only [h5, hlam, p11377_0]
                          · have p11377_0 := h11377c.1
                            have p11377_1 := h11377c.2.1
                            have p11377_2 := h11377c.2.2.1
                            have p11377_3 := h11377c.2.2.2
                            linarith only [h5, h9, hc12, hc45, hlam, hphi, ht23, ht34, p11377_1]
                          · have p11377_0 := h11377c.1
                            have p11377_1 := h11377c.2.1
                            have p11377_2 := h11377c.2.2.1
                            have p11377_3 := h11377c.2.2.2
                            linarith only [h11252, hlam, p11377_0]
                          · have p11377_0 := h11377c.1
                            have p11377_1 := h11377c.2.1
                            have p11377_2 := h11377c.2.2.1
                            have p11377_3 := h11377c.2.2.2
                            linarith only [hlam, p11377_0]
                          · have p11377_0 := h11377c.1
                            have p11377_1 := h11377c.2.1
                            have p11377_2 := h11377c.2.2.1
                            have p11377_3 := h11377c.2.2.2
                            linarith only [h11254, hlam, p11377_0]
                          · have p11377_0 := h11377c.1
                            have p11377_1 := h11377c.2.1
                            have p11377_2 := h11377c.2.2.1
                            have p11377_3 := h11377c.2.2.2
                            linarith only [h6, hlam, p11377_0]
                          · have p11377_0 := h11377c.1
                            have p11377_1 := h11377c.2.1
                            have p11377_2 := h11377c.2.2.1
                            have p11377_3 := h11377c.2.2.2
                            rcases p11377_3 (m.d 0 2) (by simp) with h11464 | h11464
                            · rcases p11377_3 (m.d 1 2) (by simp) with h11465 | h11465
                              · linarith only [h11465, hlam, p11377_0]
                              · rcases p11377_3 (m.d 2 3) (by simp) with h11467 | h11467
                                · rcases p11377_3 (m.d 2 4) (by simp) with h11468 | h11468
                                  · linarith only [h11254, h11468, hlam]
                                  · linarith only [h10760, h11468, hlam]
                                · linarith only [h11467, h9268, hlam]
                            · linarith only [h0, h11464, hlam]
                          · have p11377_0 := h11377c.1
                            have p11377_1 := h11377c.2.1
                            have p11377_2 := h11377c.2.2.1
                            have p11377_3 := h11377c.2.2.2
                            linarith only [h11253, hlam, p11377_0]
                          · have p11377_0 := h11377c.1
                            have p11377_1 := h11377c.2.1
                            have p11377_2 := h11377c.2.2.1
                            have p11377_3 := h11377c.2.2.2
                            linarith only [h10760, hc12, hc25, hlam, hphi, p11377_1]
                          · have p11377_0 := h11377c.1
                            have p11377_1 := h11377c.2.1
                            have p11377_2 := h11377c.2.2.1
                            have p11377_3 := h11377c.2.2.2
                            linarith only [hlam, p11377_0]
                        · rcases h2bigk with h11476c | h11476c | h11476c | h11476c | h11476c | h11476c | h11476c | h11476c | h11476c | h11476c | h11476c | h11476c | h11476c | h11476c | h11476c | h11476c | h11476c | h11476c | h11476c | h11476c | h11476c | h11476c | h11476c | h11476c | h11476c
                          · have p11476_0 := h11476c.1
                            have p11476_1 := h11476c.2.1
                            have p11476_2 := h11476c.2.2.1
                            have p11476_3 := h11476c.2.2.2
                            linarith only [hlam, p11476_0]
                          · have p11476_0 := h11476c.1
                            have p11476_1 := h11476c.2.1
                            have p11476_2 := h11476c.2.2.1
                            have p11476_3 := h11476c.2.2.2
                            rcases p11476_3 (m.d 0 2) (by simp) with h11478 | h11478
                            · rcases p11476_3 (m.d 1 2) (by simp) with h11479 | h11479
                              · linarith only [h0, h11479, hlam]
                              · rcases p11476_3 (m.d 2 3) (by simp) with h11481 | h11481
                                · linarith only [h11481, h4, hlam]
                                · linarith only [h11481, h9268, hlam]
                            · linarith only [h0, h11478, hlam]
                          · have p11476_0 := h11476c.1
                            have p11476_1 := h11476c.2.1
                            have p11476_2 := h11476c.2.2.1
                            have p11476_3 := h11476c.2.2.2
                            rcases p11476_3 (m.d 0 2) (by simp) with h11485 | h11485
                            · rcases p11476_3 (m.d 1 2) (by simp) with h11486 | h11486
                              · linarith only [h0, h11486, hlam]
                              · rcases p11476_3 (m.d 2 3) (by simp) with h11488 | h11488
                                · linarith only [h11488, hlam, p11476_0]
                                · rcases p11476_3 (m.d 2 4) (by simp) with h11490 | h11490
                                  · linarith only [h11490, h5, hlam]
                                  · rcases p11476_3 (m.d 2 5) (by simp) with h11492 | h11492
                                    · linarith only [h11492, h6, hlam]
                                    · rcases h4bigk with h11494c | h11494c | h11494c | h11494c | h11494c | h11494c | h11494c | h11494c | h11494c | h11494c | h11494c | h11494c | h11494c | h11494c | h11494c | h11494c | h11494c | h11494c | h11494c | h11494c | h11494c | h11494c | h11494c | h11494c | h11494c
                                      · have p11494_0 := h11494c.1
                                        have p11494_1 := h11494c.2.1
                                        have p11494_2 := h11494c.2.2.1
                                        have p11494_3 := h11494c.2.2.2
                                        linarith only [hlam, p11494_0]
                                      · have p11494_0 := h11494c.1
                                        have p11494_1 := h11494c.2.1
                                        have p11494_2 := h11494c.2.2.1
                                        have p11494_3 := h11494c.2.2.2
                                        linarith only [h10760, h9, hc12, hc45, hlam, hphi, ht23, ht34, p11494_1]
                                      · have p11494_0 := h11494c.1
                                        have p11494_1 := h11494c.2.1
                                        have p11494_2 := h11494c.2.2.1
                                        have p11494_3 := h11494c.2.2.2
                                        linarith only [h9, hc24, hc45, hlam, hphi, p11494_1]
                                      · have p11494_0 := h11494c.1
                                        have p11494_1 := h11494c.2.1
                                        have p11494_2 := h11494c.2.2.1
                                        have p11494_3 := h11494c.2.2.2
                                        linarith only [h9, hc34, hc45, hlam, hphi, p11494_1]
                                      · have p11494_0 := h11494c.1
                                        have p11494_1 := h11494c.2.1
                                        have p11494_2 := h11494c.2.2.1
                                        have p11494_3 := h11494c.2.2.2
                                        linarith only [h9, hlam, p11494_0]
                                      · have p11494_0 := h11494c.1
                                        have p11494_1 := h11494c.2.1
                                        have p11494_2 := h11494c.2.2.1
                                        have p11494_3 := h11494c.2.2.2
                                        linarith only [h2, hlam, p11494_0]
                                      · have p11494_0 := h11494c.1
                                        have p11494_1 := h11494c.2.1
                                        have p11494_2 := h11494c.2.2.1
                                        have p11494_3 := h11494c.2.2.2
                                        linarith only [hlam, p11494_0]
                                      · have p11494_0 := h11494c.1
                                        have p11494_1 := h11494c.2.1
                                        have p11494_2 := h11494c.2.2.1
                                        have p11494_3 := h11494c.2.2.2
                                        linarith only [h10760, hlam, p11494_1]
                                      · have p11494_0 := h11494c.1
                                        have p11494_1 := h11494c.2.1
                                        have p11494_2 := h11494c.2.2.1
                                        have p11494_3 := h11494c.2.2.2
                                        linarith only [h2, h9, hc34, hc45, hlam, hphi, p11494_1]
                                      · have p11494_0 := h11494c.1
                                        have p11494_1 := h11494c.2.1
                                        have p11494_2 := h11494c.2.2.1
                                        have p11494_3 := h11494c.2.2.2
                                        linarith only [h11250, hlam, p11494_0]
                                      · have p11494_0 := h11494c.1
                                        have p11494_1 := h11494c.2.1
                                        have p11494_2 := h11494c.2.2.1
                                        have p11494_3 := h11494c.2.2.2
                                        linarith only [h5, hlam, p11494_0]
                                      · have p11494_0 := h11494c.1
                                        have p11494_1 := h11494c.2.1
                                        have p11494_2 := h11494c.2.2.1
                                        have p11494_3 := h11494c.2.2.2
                                        linarith only [h5, h9, hc14, hc45, hlam, hphi, p11494_1]
                                      · have p11494_0 := h11494c.1
                                        have p11494_1 := h11494c.2.1
                                        have p11494_2 := h11494c.2.2.1
                                        have p11494_3 := h11494c.2.2.2
                                        linarith only [hlam, p11494_0]
                                      · have p11494_0 := h11494c.1
                                        have p11494_1 := h11494c.2.1
                                        have p11494_2 := h11494c.2.2.1
                                        have p11494_3 := h11494c.2.2.2
                                        linarith only [h0, h11252, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p11476_1, p11494_1]
                                      · have p11494_0 := h11494c.1
                                        have p11494_1 := h11494c.2.1
                                        have p11494_2 := h11494c.2.2.1
                                        have p11494_3 := h11494c.2.2.2
                                        linarith only [h11254, hlam, p11494_0]
                                      · have p11494_0 := h11494c.1
                                        have p11494_1 := h11494c.2.1
                                        have p11494_2 := h11494c.2.2.1
                                        have p11494_3 := h11494c.2.2.2
                                        linarith only [h7, hlam, p11494_0]
                                      · have p11494_0 := h11494c.1
                                        have p11494_1 := h11494c.2.1
                                        have p11494_2 := h11494c.2.2.1
                                        have p11494_3 := h11494c.2.2.2
                                        linarith only [h11248, hlam, p11494_0]
                                      · have p11494_0 := h11494c.1
                                        have p11494_1 := h11494c.2.1
                                        have p11494_2 := h11494c.2.2.1
                                        have p11494_3 := h11494c.2.2.2
                                        linarith only [h11252, hlam, p11494_0]
                                      · have p11494_0 := h11494c.1
                                        have p11494_1 := h11494c.2.1
                                        have p11494_2 := h11494c.2.2.1
                                        have p11494_3 := h11494c.2.2.2
                                        linarith only [hlam, p11494_0]
                                      · have p11494_0 := h11494c.1
                                        have p11494_1 := h11494c.2.1
                                        have p11494_2 := h11494c.2.2.1
                                        have p11494_3 := h11494c.2.2.2
                                        linarith only [h11256, hlam, p11494_0]
                                      · have p11494_0 := h11494c.1
                                        have p11494_1 := h11494c.2.1
                                        have p11494_2 := h11494c.2.2.1
                                        have p11494_3 := h11494c.2.2.2
                                        linarith only [h10760, h5, hc12, hc45, hlam, hphi, ht23, ht34, p11494_1]
                                      · have p11494_0 := h11494c.1
                                        have p11494_1 := h11494c.2.1
                                        have p11494_2 := h11494c.2.2.1
                                        have p11494_3 := h11494c.2.2.2
                                        rcases p11494_3 (m.d 0 4) (by simp) with h11516 | h11516
                                        · linarith only [h11516, h9, hlam]
                                        · linarith only [h11516, h2, hlam]
                                      · have p11494_0 := h11494c.1
                                        have p11494_1 := h11494c.2.1
                                        have p11494_2 := h11494c.2.2.1
                                        have p11494_3 := h11494c.2.2.2
                                        linarith only [h10760, hc12, hc45, hlam, hphi, ht23, ht34, p11494_1]
                                      · have p11494_0 := h11494c.1
                                        have p11494_1 := h11494c.2.1
                                        have p11494_2 := h11494c.2.2.1
                                        have p11494_3 := h11494c.2.2.2
                                        rcases p11494_3 (m.d 0 4) (by simp) with h11520 | h11520
                                        · linarith only [h11520, h9, hlam]
                                        · linarith only [h11520, h7, hlam]
                                      · have p11494_0 := h11494c.1
                                        have p11494_1 := h11494c.2.1
                                        have p11494_2 := h11494c.2.2.1
                                        have p11494_3 := h11494c.2.2.2
                                        linarith only [hlam, p11494_0]
                            · linarith only [h11485, hlam, p11476_0]
                          · have p11476_0 := h11476c.1
                            have p11476_1 := h11476c.2.1
                            have p11476_2 := h11476c.2.2.1
                            have p11476_3 := h11476c.2.2.2
                            rcases p11476_3 (m.d 0 2) (by simp) with h11525 | h11525
                            · rcases p11476_3 (m.d 1 2) (by simp) with h11526 | h11526
                              · linarith only [h0, h11526, hlam]
                              · rcases p11476_3 (m.d 2 3) (by simp) with h11528 | h11528
                                · linarith only [h11528, h4, hlam]
                                · linarith only [h11252, h11528, hlam]
                            · linarith only [h11525, hlam, p11476_0]
                          · have p11476_0 := h11476c.1
                            have p11476_1 := h11476c.2.1
                            have p11476_2 := h11476c.2.2.1
                            have p11476_3 := h11476c.2.2.2
                            rcases p11476_3 (m.d 0 2) (by simp) with h11532 | h11532
                            · rcases p11476_3 (m.d 1 2) (by simp) with h11533 | h11533
                              · linarith only [h0, h11533, hlam]
                              · rcases p11476_3 (m.d 2 3) (by simp) with h11535 | h11535
                                · linarith only [h11535, h4, hlam]
                                · linarith only [h11253, h11535, hlam]
                            · linarith only [h11532, hlam, p11476_0]
                          · have p11476_0 := h11476c.1
                            have p11476_1 := h11476c.2.1
                            have p11476_2 := h11476c.2.2.1
                            have p11476_3 := h11476c.2.2.2
                            linarith only [h0, hlam, p11476_1]
                          · have p11476_0 := h11476c.1
                            have p11476_1 := h11476c.2.1
                            have p11476_2 := h11476c.2.2.1
                            have p11476_3 := h11476c.2.2.2
                            linarith only [hlam, p11476_0]
                          · have p11476_0 := h11476c.1
                            have p11476_1 := h11476c.2.1
                            have p11476_2 := h11476c.2.2.1
                            have p11476_3 := h11476c.2.2.2
                            linarith only [h9268, hlam, p11476_0]
                          · have p11476_0 := h11476c.1
                            have p11476_1 := h11476c.2.1
                            have p11476_2 := h11476c.2.2.1
                            have p11476_3 := h11476c.2.2.2
                            linarith only [h10760, hlam, p11476_0]
                          · have p11476_0 := h11476c.1
                            have p11476_1 := h11476c.2.1
                            have p11476_2 := h11476c.2.2.1
                            have p11476_3 := h11476c.2.2.2
                            linarith only [h11236, hlam, p11476_0]
                          · have p11476_0 := h11476c.1
                            have p11476_1 := h11476c.2.1
                            have p11476_2 := h11476c.2.2.1
                            have p11476_3 := h11476c.2.2.2
                            linarith only [h4, hlam, p11476_0]
                          · have p11476_0 := h11476c.1
                            have p11476_1 := h11476c.2.1
                            have p11476_2 := h11476c.2.2.1
                            have p11476_3 := h11476c.2.2.2
                            rcases p11476_3 (m.d 0 2) (by simp) with h11545 | h11545
                            · rcases p11476_3 (m.d 1 2) (by simp) with h11546 | h11546
                              · linarith only [h11546, hlam, p11476_0]
                              · rcases p11476_3 (m.d 2 3) (by simp) with h11548 | h11548
                                · rcases p11476_3 (m.d 2 4) (by simp) with h11549 | h11549
                                  · linarith only [h11252, h11549, hlam]
                                  · linarith only [h10760, h11549, hlam]
                                · linarith only [h11548, hlam, p11476_0]
                            · linarith only [h0, h11545, hlam]
                          · have p11476_0 := h11476c.1
                            have p11476_1 := h11476c.2.1
                            have p11476_2 := h11476c.2.2.1
                            have p11476_3 := h11476c.2.2.2
                            linarith only [hlam, p11476_0]
                          · have p11476_0 := h11476c.1
                            have p11476_1 := h11476c.2.1
                            have p11476_2 := h11476c.2.2.1
                            have p11476_3 := h11476c.2.2.2
                            linarith only [h10760, hc12, hc23, hlam, hphi, p11476_1]
                          · have p11476_0 := h11476c.1
                            have p11476_1 := h11476c.2.1
                            have p11476_2 := h11476c.2.2.1
                            have p11476_3 := h11476c.2.2.2
                            linarith only [h0, h11236, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p11476_1]
                          · have p11476_0 := h11476c.1
                            have p11476_1 := h11476c.2.1
                            have p11476_2 := h11476c.2.2.1
                            have p11476_3 := h11476c.2.2.2
                            linarith only [h5, hlam, p11476_0]
                          · have p11476_0 := h11476c.1
                            have p11476_1 := h11476c.2.1
                            have p11476_2 := h11476c.2.2.1
                            have p11476_3 := h11476c.2.2.2
                            linarith only [h5, h9, hc12, hc45, hlam, hphi, ht23, ht34, p11476_1]
                          · have p11476_0 := h11476c.1
                            have p11476_1 := h11476c.2.1
                            have p11476_2 := h11476c.2.2.1
                            have p11476_3 := h11476c.2.2.2
                            linarith only [h11252, hlam, p11476_0]
                          · have p11476_0 := h11476c.1
                            have p11476_1 := h11476c.2.1
                            have p11476_2 := h11476c.2.2.1
                            have p11476_3 := h11476c.2.2.2
                            linarith only [hlam, p11476_0]
                          · have p11476_0 := h11476c.1
                            have p11476_1 := h11476c.2.1
                            have p11476_2 := h11476c.2.2.1
                            have p11476_3 := h11476c.2.2.2
                            linarith only [h11254, hlam, p11476_0]
                          · have p11476_0 := h11476c.1
                            have p11476_1 := h11476c.2.1
                            have p11476_2 := h11476c.2.2.1
                            have p11476_3 := h11476c.2.2.2
                            linarith only [h6, hlam, p11476_0]
                          · have p11476_0 := h11476c.1
                            have p11476_1 := h11476c.2.1
                            have p11476_2 := h11476c.2.2.1
                            have p11476_3 := h11476c.2.2.2
                            rcases p11476_3 (m.d 0 2) (by simp) with h11563 | h11563
                            · rcases p11476_3 (m.d 1 2) (by simp) with h11564 | h11564
                              · linarith only [h11564, hlam, p11476_0]
                              · rcases p11476_3 (m.d 2 3) (by simp) with h11566 | h11566
                                · rcases p11476_3 (m.d 2 4) (by simp) with h11567 | h11567
                                  · linarith only [h11254, h11567, hlam]
                                  · linarith only [h10760, h11567, hlam]
                                · linarith only [h11566, h9268, hlam]
                            · linarith only [h0, h11563, hlam]
                          · have p11476_0 := h11476c.1
                            have p11476_1 := h11476c.2.1
                            have p11476_2 := h11476c.2.2.1
                            have p11476_3 := h11476c.2.2.2
                            linarith only [h11253, hlam, p11476_0]
                          · have p11476_0 := h11476c.1
                            have p11476_1 := h11476c.2.1
                            have p11476_2 := h11476c.2.2.1
                            have p11476_3 := h11476c.2.2.2
                            linarith only [h10760, hc12, hc25, hlam, hphi, p11476_1]
                          · have p11476_0 := h11476c.1
                            have p11476_1 := h11476c.2.1
                            have p11476_2 := h11476c.2.2.1
                            have p11476_3 := h11476c.2.2.2
                            linarith only [hlam, p11476_0]
                        · rcases h2bigk with h11575c | h11575c | h11575c | h11575c | h11575c | h11575c | h11575c | h11575c | h11575c | h11575c | h11575c | h11575c | h11575c | h11575c | h11575c | h11575c | h11575c | h11575c | h11575c | h11575c | h11575c | h11575c | h11575c | h11575c | h11575c
                          · have p11575_0 := h11575c.1
                            have p11575_1 := h11575c.2.1
                            have p11575_2 := h11575c.2.2.1
                            have p11575_3 := h11575c.2.2.2
                            linarith only [hlam, p11575_0]
                          · have p11575_0 := h11575c.1
                            have p11575_1 := h11575c.2.1
                            have p11575_2 := h11575c.2.2.1
                            have p11575_3 := h11575c.2.2.2
                            rcases p11575_3 (m.d 0 2) (by simp) with h11577 | h11577
                            · rcases p11575_3 (m.d 1 2) (by simp) with h11578 | h11578
                              · linarith only [h0, h11578, hlam]
                              · rcases p11575_3 (m.d 2 3) (by simp) with h11580 | h11580
                                · linarith only [h11580, h4, hlam]
                                · linarith only [h11580, h9268, hlam]
                            · linarith only [h0, h11577, hlam]
                          · have p11575_0 := h11575c.1
                            have p11575_1 := h11575c.2.1
                            have p11575_2 := h11575c.2.2.1
                            have p11575_3 := h11575c.2.2.2
                            rcases p11575_3 (m.d 0 2) (by simp) with h11584 | h11584
                            · rcases p11575_3 (m.d 1 2) (by simp) with h11585 | h11585
                              · linarith only [h0, h11585, hlam]
                              · rcases p11575_3 (m.d 2 3) (by simp) with h11587 | h11587
                                · linarith only [h11587, hlam, p11575_0]
                                · rcases p11575_3 (m.d 2 4) (by simp) with h11589 | h11589
                                  · linarith only [h11589, h5, hlam]
                                  · rcases p11575_3 (m.d 2 5) (by simp) with h11591 | h11591
                                    · linarith only [h11591, h6, hlam]
                                    · rcases h4bigk with h11593c | h11593c | h11593c | h11593c | h11593c | h11593c | h11593c | h11593c | h11593c | h11593c | h11593c | h11593c | h11593c | h11593c | h11593c | h11593c | h11593c | h11593c | h11593c | h11593c | h11593c | h11593c | h11593c | h11593c | h11593c
                                      · have p11593_0 := h11593c.1
                                        have p11593_1 := h11593c.2.1
                                        have p11593_2 := h11593c.2.2.1
                                        have p11593_3 := h11593c.2.2.2
                                        linarith only [hlam, p11593_0]
                                      · have p11593_0 := h11593c.1
                                        have p11593_1 := h11593c.2.1
                                        have p11593_2 := h11593c.2.2.1
                                        have p11593_3 := h11593c.2.2.2
                                        linarith only [h10760, h9, hc12, hc45, hlam, hphi, ht23, ht34, p11593_1]
                                      · have p11593_0 := h11593c.1
                                        have p11593_1 := h11593c.2.1
                                        have p11593_2 := h11593c.2.2.1
                                        have p11593_3 := h11593c.2.2.2
                                        linarith only [h9, hc24, hc45, hlam, hphi, p11593_1]
                                      · have p11593_0 := h11593c.1
                                        have p11593_1 := h11593c.2.1
                                        have p11593_2 := h11593c.2.2.1
                                        have p11593_3 := h11593c.2.2.2
                                        linarith only [h9, hc34, hc45, hlam, hphi, p11593_1]
                                      · have p11593_0 := h11593c.1
                                        have p11593_1 := h11593c.2.1
                                        have p11593_2 := h11593c.2.2.1
                                        have p11593_3 := h11593c.2.2.2
                                        linarith only [h9, hlam, p11593_0]
                                      · have p11593_0 := h11593c.1
                                        have p11593_1 := h11593c.2.1
                                        have p11593_2 := h11593c.2.2.1
                                        have p11593_3 := h11593c.2.2.2
                                        linarith only [h2, hlam, p11593_0]
                                      · have p11593_0 := h11593c.1
                                        have p11593_1 := h11593c.2.1
                                        have p11593_2 := h11593c.2.2.1
                                        have p11593_3 := h11593c.2.2.2
                                        linarith only [hlam, p11593_0]
                                      · have p11593_0 := h11593c.1
                                        have p11593_1 := h11593c.2.1
                                        have p11593_2 := h11593c.2.2.1
                                        have p11593_3 := h11593c.2.2.2
                                        linarith only [h10760, hlam, p11593_1]
                                      · have p11593_0 := h11593c.1
                                        have p11593_1 := h11593c.2.1
                                        have p11593_2 := h11593c.2.2.1
                                        have p11593_3 := h11593c.2.2.2
                                        linarith only [h2, h9, hc34, hc45, hlam, hphi, p11593_1]
                                      · have p11593_0 := h11593c.1
                                        have p11593_1 := h11593c.2.1
                                        have p11593_2 := h11593c.2.2.1
                                        have p11593_3 := h11593c.2.2.2
                                        linarith only [h11250, hlam, p11593_0]
                                      · have p11593_0 := h11593c.1
                                        have p11593_1 := h11593c.2.1
                                        have p11593_2 := h11593c.2.2.1
                                        have p11593_3 := h11593c.2.2.2
                                        linarith only [h5, hlam, p11593_0]
                                      · have p11593_0 := h11593c.1
                                        have p11593_1 := h11593c.2.1
                                        have p11593_2 := h11593c.2.2.1
                                        have p11593_3 := h11593c.2.2.2
                                        linarith only [h5, h9, hc14, hc45, hlam, hphi, p11593_1]
                                      · have p11593_0 := h11593c.1
                                        have p11593_1 := h11593c.2.1
                                        have p11593_2 := h11593c.2.2.1
                                        have p11593_3 := h11593c.2.2.2
                                        linarith only [hlam, p11593_0]
                                      · have p11593_0 := h11593c.1
                                        have p11593_1 := h11593c.2.1
                                        have p11593_2 := h11593c.2.2.1
                                        have p11593_3 := h11593c.2.2.2
                                        linarith only [h0, h11252, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p11575_1, p11593_1]
                                      · have p11593_0 := h11593c.1
                                        have p11593_1 := h11593c.2.1
                                        have p11593_2 := h11593c.2.2.1
                                        have p11593_3 := h11593c.2.2.2
                                        linarith only [h11254, hlam, p11593_0]
                                      · have p11593_0 := h11593c.1
                                        have p11593_1 := h11593c.2.1
                                        have p11593_2 := h11593c.2.2.1
                                        have p11593_3 := h11593c.2.2.2
                                        linarith only [h7, hlam, p11593_0]
                                      · have p11593_0 := h11593c.1
                                        have p11593_1 := h11593c.2.1
                                        have p11593_2 := h11593c.2.2.1
                                        have p11593_3 := h11593c.2.2.2
                                        linarith only [h11248, hlam, p11593_0]
                                      · have p11593_0 := h11593c.1
                                        have p11593_1 := h11593c.2.1
                                        have p11593_2 := h11593c.2.2.1
                                        have p11593_3 := h11593c.2.2.2
                                        linarith only [h11252, hlam, p11593_0]
                                      · have p11593_0 := h11593c.1
                                        have p11593_1 := h11593c.2.1
                                        have p11593_2 := h11593c.2.2.1
                                        have p11593_3 := h11593c.2.2.2
                                        linarith only [hlam, p11593_0]
                                      · have p11593_0 := h11593c.1
                                        have p11593_1 := h11593c.2.1
                                        have p11593_2 := h11593c.2.2.1
                                        have p11593_3 := h11593c.2.2.2
                                        linarith only [h11256, hlam, p11593_0]
                                      · have p11593_0 := h11593c.1
                                        have p11593_1 := h11593c.2.1
                                        have p11593_2 := h11593c.2.2.1
                                        have p11593_3 := h11593c.2.2.2
                                        linarith only [h10760, h5, hc12, hc45, hlam, hphi, ht23, ht34, p11593_1]
                                      · have p11593_0 := h11593c.1
                                        have p11593_1 := h11593c.2.1
                                        have p11593_2 := h11593c.2.2.1
                                        have p11593_3 := h11593c.2.2.2
                                        rcases p11593_3 (m.d 0 4) (by simp) with h11615 | h11615
                                        · linarith only [h11615, h9, hlam]
                                        · linarith only [h11615, h2, hlam]
                                      · have p11593_0 := h11593c.1
                                        have p11593_1 := h11593c.2.1
                                        have p11593_2 := h11593c.2.2.1
                                        have p11593_3 := h11593c.2.2.2
                                        linarith only [h10760, hc12, hc45, hlam, hphi, ht23, ht34, p11593_1]
                                      · have p11593_0 := h11593c.1
                                        have p11593_1 := h11593c.2.1
                                        have p11593_2 := h11593c.2.2.1
                                        have p11593_3 := h11593c.2.2.2
                                        rcases p11593_3 (m.d 0 4) (by simp) with h11619 | h11619
                                        · linarith only [h11619, h9, hlam]
                                        · linarith only [h11619, h7, hlam]
                                      · have p11593_0 := h11593c.1
                                        have p11593_1 := h11593c.2.1
                                        have p11593_2 := h11593c.2.2.1
                                        have p11593_3 := h11593c.2.2.2
                                        linarith only [hlam, p11593_0]
                            · linarith only [h11584, hlam, p11575_0]
                          · have p11575_0 := h11575c.1
                            have p11575_1 := h11575c.2.1
                            have p11575_2 := h11575c.2.2.1
                            have p11575_3 := h11575c.2.2.2
                            rcases p11575_3 (m.d 0 2) (by simp) with h11624 | h11624
                            · rcases p11575_3 (m.d 1 2) (by simp) with h11625 | h11625
                              · linarith only [h0, h11625, hlam]
                              · rcases p11575_3 (m.d 2 3) (by simp) with h11627 | h11627
                                · linarith only [h11627, h4, hlam]
                                · linarith only [h11252, h11627, hlam]
                            · linarith only [h11624, hlam, p11575_0]
                          · have p11575_0 := h11575c.1
                            have p11575_1 := h11575c.2.1
                            have p11575_2 := h11575c.2.2.1
                            have p11575_3 := h11575c.2.2.2
                            rcases p11575_3 (m.d 0 2) (by simp) with h11631 | h11631
                            · rcases p11575_3 (m.d 1 2) (by simp) with h11632 | h11632
                              · linarith only [h0, h11632, hlam]
                              · rcases p11575_3 (m.d 2 3) (by simp) with h11634 | h11634
                                · linarith only [h11634, h4, hlam]
                                · linarith only [h11253, h11634, hlam]
                            · linarith only [h11631, hlam, p11575_0]
                          · have p11575_0 := h11575c.1
                            have p11575_1 := h11575c.2.1
                            have p11575_2 := h11575c.2.2.1
                            have p11575_3 := h11575c.2.2.2
                            linarith only [h0, hlam, p11575_1]
                          · have p11575_0 := h11575c.1
                            have p11575_1 := h11575c.2.1
                            have p11575_2 := h11575c.2.2.1
                            have p11575_3 := h11575c.2.2.2
                            linarith only [hlam, p11575_0]
                          · have p11575_0 := h11575c.1
                            have p11575_1 := h11575c.2.1
                            have p11575_2 := h11575c.2.2.1
                            have p11575_3 := h11575c.2.2.2
                            linarith only [h9268, hlam, p11575_0]
                          · have p11575_0 := h11575c.1
                            have p11575_1 := h11575c.2.1
                            have p11575_2 := h11575c.2.2.1
                            have p11575_3 := h11575c.2.2.2
                            linarith only [h10760, hlam, p11575_0]
                          · have p11575_0 := h11575c.1
                            have p11575_1 := h11575c.2.1
                            have p11575_2 := h11575c.2.2.1
                            have p11575_3 := h11575c.2.2.2
                            linarith only [h11236, hlam, p11575_0]
                          · have p11575_0 := h11575c.1
                            have p11575_1 := h11575c.2.1
                            have p11575_2 := h11575c.2.2.1
                            have p11575_3 := h11575c.2.2.2
                            linarith only [h4, hlam, p11575_0]
                          · have p11575_0 := h11575c.1
                            have p11575_1 := h11575c.2.1
                            have p11575_2 := h11575c.2.2.1
                            have p11575_3 := h11575c.2.2.2
                            rcases p11575_3 (m.d 0 2) (by simp) with h11644 | h11644
                            · rcases p11575_3 (m.d 1 2) (by simp) with h11645 | h11645
                              · linarith only [h11645, hlam, p11575_0]
                              · rcases p11575_3 (m.d 2 3) (by simp) with h11647 | h11647
                                · rcases p11575_3 (m.d 2 4) (by simp) with h11648 | h11648
                                  · linarith only [h11252, h11648, hlam]
                                  · linarith only [h10760, h11648, hlam]
                                · linarith only [h11647, hlam, p11575_0]
                            · linarith only [h0, h11644, hlam]
                          · have p11575_0 := h11575c.1
                            have p11575_1 := h11575c.2.1
                            have p11575_2 := h11575c.2.2.1
                            have p11575_3 := h11575c.2.2.2
                            linarith only [hlam, p11575_0]
                          · have p11575_0 := h11575c.1
                            have p11575_1 := h11575c.2.1
                            have p11575_2 := h11575c.2.2.1
                            have p11575_3 := h11575c.2.2.2
                            linarith only [h10760, hc12, hc23, hlam, hphi, p11575_1]
                          · have p11575_0 := h11575c.1
                            have p11575_1 := h11575c.2.1
                            have p11575_2 := h11575c.2.2.1
                            have p11575_3 := h11575c.2.2.2
                            linarith only [h0, h11236, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p11575_1]
                          · have p11575_0 := h11575c.1
                            have p11575_1 := h11575c.2.1
                            have p11575_2 := h11575c.2.2.1
                            have p11575_3 := h11575c.2.2.2
                            linarith only [h5, hlam, p11575_0]
                          · have p11575_0 := h11575c.1
                            have p11575_1 := h11575c.2.1
                            have p11575_2 := h11575c.2.2.1
                            have p11575_3 := h11575c.2.2.2
                            linarith only [h5, h9, hc12, hc45, hlam, hphi, ht23, ht34, p11575_1]
                          · have p11575_0 := h11575c.1
                            have p11575_1 := h11575c.2.1
                            have p11575_2 := h11575c.2.2.1
                            have p11575_3 := h11575c.2.2.2
                            linarith only [h11252, hlam, p11575_0]
                          · have p11575_0 := h11575c.1
                            have p11575_1 := h11575c.2.1
                            have p11575_2 := h11575c.2.2.1
                            have p11575_3 := h11575c.2.2.2
                            linarith only [hlam, p11575_0]
                          · have p11575_0 := h11575c.1
                            have p11575_1 := h11575c.2.1
                            have p11575_2 := h11575c.2.2.1
                            have p11575_3 := h11575c.2.2.2
                            linarith only [h11254, hlam, p11575_0]
                          · have p11575_0 := h11575c.1
                            have p11575_1 := h11575c.2.1
                            have p11575_2 := h11575c.2.2.1
                            have p11575_3 := h11575c.2.2.2
                            linarith only [h6, hlam, p11575_0]
                          · have p11575_0 := h11575c.1
                            have p11575_1 := h11575c.2.1
                            have p11575_2 := h11575c.2.2.1
                            have p11575_3 := h11575c.2.2.2
                            rcases p11575_3 (m.d 0 2) (by simp) with h11662 | h11662
                            · rcases p11575_3 (m.d 1 2) (by simp) with h11663 | h11663
                              · linarith only [h11663, hlam, p11575_0]
                              · rcases p11575_3 (m.d 2 3) (by simp) with h11665 | h11665
                                · rcases p11575_3 (m.d 2 4) (by simp) with h11666 | h11666
                                  · linarith only [h11254, h11666, hlam]
                                  · linarith only [h10760, h11666, hlam]
                                · linarith only [h11665, h9268, hlam]
                            · linarith only [h0, h11662, hlam]
                          · have p11575_0 := h11575c.1
                            have p11575_1 := h11575c.2.1
                            have p11575_2 := h11575c.2.2.1
                            have p11575_3 := h11575c.2.2.2
                            linarith only [h11253, hlam, p11575_0]
                          · have p11575_0 := h11575c.1
                            have p11575_1 := h11575c.2.1
                            have p11575_2 := h11575c.2.2.1
                            have p11575_3 := h11575c.2.2.2
                            linarith only [h10760, hc12, hc25, hlam, hphi, p11575_1]
                          · have p11575_0 := h11575c.1
                            have p11575_1 := h11575c.2.1
                            have p11575_2 := h11575c.2.2.1
                            have p11575_3 := h11575c.2.2.2
                            linarith only [hlam, p11575_0]
              · linarith only [h11267, hlam, p11258_0]
            · have p11258_0 := h11258c.1
              have p11258_1 := h11258c.2.1
              have p11258_2 := h11258c.2.2.1
              have p11258_3 := h11258c.2.2.2
              rcases p11258_3 (m.d 0 1) (by simp) with h11675 | h11675
              · rcases p11258_3 (m.d 1 2) (by simp) with h11676 | h11676
                · linarith only [h0, h11676, hlam]
                · rcases p11258_3 (m.d 1 3) (by simp) with h11678 | h11678
                  · linarith only [h1, h11678, hlam]
                  · linarith only [h11248, h11678, hlam]
              · linarith only [h11675, hlam, p11258_0]
            · have p11258_0 := h11258c.1
              have p11258_1 := h11258c.2.1
              have p11258_2 := h11258c.2.2.1
              have p11258_3 := h11258c.2.2.2
              rcases p11258_3 (m.d 0 1) (by simp) with h11682 | h11682
              · rcases p11258_3 (m.d 1 2) (by simp) with h11683 | h11683
                · linarith only [h0, h11683, hlam]
                · rcases p11258_3 (m.d 1 3) (by simp) with h11685 | h11685
                  · linarith only [h1, h11685, hlam]
                  · linarith only [h11249, h11685, hlam]
              · linarith only [h11682, hlam, p11258_0]
            · have p11258_0 := h11258c.1
              have p11258_1 := h11258c.2.1
              have p11258_2 := h11258c.2.2.1
              have p11258_3 := h11258c.2.2.2
              linarith only [h0, hlam, p11258_0]
            · have p11258_0 := h11258c.1
              have p11258_1 := h11258c.2.1
              have p11258_2 := h11258c.2.2.1
              have p11258_3 := h11258c.2.2.2
              linarith only [hlam, p11258_0]
            · have p11258_0 := h11258c.1
              have p11258_1 := h11258c.2.1
              have p11258_2 := h11258c.2.2.1
              have p11258_3 := h11258c.2.2.2
              linarith only [h9268, hlam, p11258_1]
            · have p11258_0 := h11258c.1
              have p11258_1 := h11258c.2.1
              have p11258_2 := h11258c.2.2.1
              have p11258_3 := h11258c.2.2.2
              linarith only [h10760, hlam, p11258_1]
            · have p11258_0 := h11258c.1
              have p11258_1 := h11258c.2.1
              have p11258_2 := h11258c.2.2.1
              have p11258_3 := h11258c.2.2.2
              linarith only [h11236, hlam, p11258_1]
            · have p11258_0 := h11258c.1
              have p11258_1 := h11258c.2.1
              have p11258_2 := h11258c.2.2.1
              have p11258_3 := h11258c.2.2.2
              linarith only [h1, hlam, p11258_0]
            · have p11258_0 := h11258c.1
              have p11258_1 := h11258c.2.1
              have p11258_2 := h11258c.2.2.1
              have p11258_3 := h11258c.2.2.2
              rcases p11258_3 (m.d 0 1) (by simp) with h11695 | h11695
              · rcases p11258_3 (m.d 1 2) (by simp) with h11696 | h11696
                · linarith only [h11696, h9268, hlam]
                · rcases p11258_3 (m.d 1 3) (by simp) with h11698 | h11698
                  · rcases p11258_3 (m.d 1 4) (by simp) with h11699 | h11699
                    · linarith only [h11248, h11699, hlam]
                    · linarith only [h10760, h11699, hlam]
                  · linarith only [h11698, h9268, hlam]
              · linarith only [h0, h11695, hlam]
            · have p11258_0 := h11258c.1
              have p11258_1 := h11258c.2.1
              have p11258_2 := h11258c.2.2.1
              have p11258_3 := h11258c.2.2.2
              linarith only [hlam, p11258_0]
            · have p11258_0 := h11258c.1
              have p11258_1 := h11258c.2.1
              have p11258_2 := h11258c.2.2.1
              have p11258_3 := h11258c.2.2.2
              rcases p11258_3 (m.d 0 1) (by simp) with h11705 | h11705
              · rcases p11258_3 (m.d 1 2) (by simp) with h11706 | h11706
                · linarith only [h11706, h9268, hlam]
                · rcases p11258_3 (m.d 1 3) (by simp) with h11708 | h11708
                  · rcases p11258_3 (m.d 1 4) (by simp) with h11709 | h11709
                    · linarith only [h11248, h11709, hlam]
                    · rcases p11258_3 (m.d 1 5) (by simp) with h11711 | h11711
                      · linarith only [h11249, h11711, hlam]
                      · linarith only [h11250, h11711, hlam]
                  · linarith only [h11248, h11708, hlam]
              · linarith only [h11705, h2, hlam]
            · have p11258_0 := h11258c.1
              have p11258_1 := h11258c.2.1
              have p11258_2 := h11258c.2.2.1
              have p11258_3 := h11258c.2.2.2
              rcases p11258_3 (m.d 0 1) (by simp) with h11716 | h11716
              · rcases p11258_3 (m.d 1 2) (by simp) with h11717 | h11717
                · linarith only [h11717, h9268, hlam]
                · rcases p11258_3 (m.d 1 3) (by simp) with h11719 | h11719
                  · rcases p11258_3 (m.d 1 4) (by simp) with h11720 | h11720
                    · linarith only [h11248, h11720, hlam]
                    · rcases p11258_3 (m.d 1 5) (by simp) with h11722 | h11722
                      · linarith only [h11249, h11722, hlam]
                      · rcases h1emax with h11724 | h11724 | h11724 | h11724 | h11724
                        · linarith only [h1, h10760, h11250, h11724, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p11258_1]
                        · rcases h2bigk with h11726c | h11726c | h11726c | h11726c | h11726c | h11726c | h11726c | h11726c | h11726c | h11726c | h11726c | h11726c | h11726c | h11726c | h11726c | h11726c | h11726c | h11726c | h11726c | h11726c | h11726c | h11726c | h11726c | h11726c | h11726c
                          · have p11726_0 := h11726c.1
                            have p11726_1 := h11726c.2.1
                            have p11726_2 := h11726c.2.2.1
                            have p11726_3 := h11726c.2.2.2
                            linarith only [hlam, p11726_0]
                          · have p11726_0 := h11726c.1
                            have p11726_1 := h11726c.2.1
                            have p11726_2 := h11726c.2.2.1
                            have p11726_3 := h11726c.2.2.2
                            linarith only [h10760, h11250, h4, h9268, hlam, p11258_1, p11726_2]
                          · have p11726_0 := h11726c.1
                            have p11726_1 := h11726c.2.1
                            have p11726_2 := h11726c.2.2.1
                            have p11726_3 := h11726c.2.2.2
                            linarith only [h0, h10760, h11250, h9268, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p11258_1, p11726_1]
                          · have p11726_0 := h11726c.1
                            have p11726_1 := h11726c.2.1
                            have p11726_2 := h11726c.2.2.1
                            have p11726_3 := h11726c.2.2.2
                            rcases p11726_3 (m.d 0 2) (by simp) with h11730 | h11730
                            · rcases p11726_3 (m.d 1 2) (by simp) with h11731 | h11731
                              · linarith only [h0, h11731, hlam]
                              · rcases p11726_3 (m.d 2 3) (by simp) with h11733 | h11733
                                · linarith only [h11733, h4, hlam]
                                · linarith only [h11252, h11733, hlam]
                            · linarith only [h11730, hlam, p11726_0]
                          · have p11726_0 := h11726c.1
                            have p11726_1 := h11726c.2.1
                            have p11726_2 := h11726c.2.2.1
                            have p11726_3 := h11726c.2.2.2
                            rcases p11726_3 (m.d 0 2) (by simp) with h11737 | h11737
                            · rcases p11726_3 (m.d 1 2) (by simp) with h11738 | h11738
                              · linarith only [h0, h11738, hlam]
                              · rcases p11726_3 (m.d 2 3) (by simp) with h11740 | h11740
                                · linarith only [h11740, h4, hlam]
                                · linarith only [h11253, h11740, hlam]
                            · linarith only [h11737, hlam, p11726_0]
                          · have p11726_0 := h11726c.1
                            have p11726_1 := h11726c.2.1
                            have p11726_2 := h11726c.2.2.1
                            have p11726_3 := h11726c.2.2.2
                            linarith only [h0, hlam, p11726_1]
                          · have p11726_0 := h11726c.1
                            have p11726_1 := h11726c.2.1
                            have p11726_2 := h11726c.2.2.1
                            have p11726_3 := h11726c.2.2.2
                            linarith only [hlam, p11726_0]
                          · have p11726_0 := h11726c.1
                            have p11726_1 := h11726c.2.1
                            have p11726_2 := h11726c.2.2.1
                            have p11726_3 := h11726c.2.2.2
                            linarith only [h9268, hlam, p11726_0]
                          · have p11726_0 := h11726c.1
                            have p11726_1 := h11726c.2.1
                            have p11726_2 := h11726c.2.2.1
                            have p11726_3 := h11726c.2.2.2
                            linarith only [h10760, hlam, p11726_0]
                          · have p11726_0 := h11726c.1
                            have p11726_1 := h11726c.2.1
                            have p11726_2 := h11726c.2.2.1
                            have p11726_3 := h11726c.2.2.2
                            linarith only [h11236, hlam, p11726_0]
                          · have p11726_0 := h11726c.1
                            have p11726_1 := h11726c.2.1
                            have p11726_2 := h11726c.2.2.1
                            have p11726_3 := h11726c.2.2.2
                            linarith only [h4, hlam, p11726_0]
                          · have p11726_0 := h11726c.1
                            have p11726_1 := h11726c.2.1
                            have p11726_2 := h11726c.2.2.1
                            have p11726_3 := h11726c.2.2.2
                            rcases p11726_3 (m.d 0 2) (by simp) with h11750 | h11750
                            · rcases p11726_3 (m.d 1 2) (by simp) with h11751 | h11751
                              · linarith only [h11751, hlam, p11726_0]
                              · rcases p11726_3 (m.d 2 3) (by simp) with h11753 | h11753
                                · rcases p11726_3 (m.d 2 4) (by simp) with h11754 | h11754
                                  · linarith only [h11252, h11754, hlam]
                                  · linarith only [h10760, h11754, hlam]
                                · linarith only [h11753, hlam, p11726_0]
                            · linarith only [h0, h11750, hlam]
                          · have p11726_0 := h11726c.1
                            have p11726_1 := h11726c.2.1
                            have p11726_2 := h11726c.2.2.1
                            have p11726_3 := h11726c.2.2.2
                            linarith only [hlam, p11726_0]
                          · have p11726_0 := h11726c.1
                            have p11726_1 := h11726c.2.1
                            have p11726_2 := h11726c.2.2.1
                            have p11726_3 := h11726c.2.2.2
                            linarith only [h10760, hc12, hc23, hlam, hphi, p11726_1]
                          · have p11726_0 := h11726c.1
                            have p11726_1 := h11726c.2.1
                            have p11726_2 := h11726c.2.2.1
                            have p11726_3 := h11726c.2.2.2
                            linarith only [h0, h11236, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p11726_1]
                          · have p11726_0 := h11726c.1
                            have p11726_1 := h11726c.2.1
                            have p11726_2 := h11726c.2.2.1
                            have p11726_3 := h11726c.2.2.2
                            linarith only [h5, hlam, p11726_0]
                          · have p11726_0 := h11726c.1
                            have p11726_1 := h11726c.2.1
                            have p11726_2 := h11726c.2.2.1
                            have p11726_3 := h11726c.2.2.2
                            linarith only [h5, h9, hc12, hc45, hlam, hphi, ht23, ht34, p11726_1]
                          · have p11726_0 := h11726c.1
                            have p11726_1 := h11726c.2.1
                            have p11726_2 := h11726c.2.2.1
                            have p11726_3 := h11726c.2.2.2
                            linarith only [h11252, hlam, p11726_0]
                          · have p11726_0 := h11726c.1
                            have p11726_1 := h11726c.2.1
                            have p11726_2 := h11726c.2.2.1
                            have p11726_3 := h11726c.2.2.2
                            linarith only [hlam, p11726_0]
                          · have p11726_0 := h11726c.1
                            have p11726_1 := h11726c.2.1
                            have p11726_2 := h11726c.2.2.1
                            have p11726_3 := h11726c.2.2.2
                            linarith only [h11254, hlam, p11726_0]
                          · have p11726_0 := h11726c.1
                            have p11726_1 := h11726c.2.1
                            have p11726_2 := h11726c.2.2.1
                            have p11726_3 := h11726c.2.2.2
                            linarith only [h6, hlam, p11726_0]
                          · have p11726_0 := h11726c.1
                            have p11726_1 := h11726c.2.1
                            have p11726_2 := h11726c.2.2.1
                            have p11726_3 := h11726c.2.2.2
                            rcases p11726_3 (m.d 0 2) (by simp) with h11768 | h11768
                            · rcases p11726_3 (m.d 1 2) (by simp) with h11769 | h11769
                              · linarith only [h11769, hlam, p11726_0]
                              · rcases p11726_3 (m.d 2 3) (by simp) with h11771 | h11771
                                · rcases p11726_3 (m.d 2 4) (by simp) with h11772 | h11772
                                  · linarith only [h11254, h11772, hlam]
                                  · linarith only [h10760, h11772, hlam]
                                · linarith only [h11771, h9268, hlam]
                            · linarith only [h0, h11768, hlam]
                          · have p11726_0 := h11726c.1
                            have p11726_1 := h11726c.2.1
                            have p11726_2 := h11726c.2.2.1
                            have p11726_3 := h11726c.2.2.2
                            linarith only [h11253, hlam, p11726_0]
                          · have p11726_0 := h11726c.1
                            have p11726_1 := h11726c.2.1
                            have p11726_2 := h11726c.2.2.1
                            have p11726_3 := h11726c.2.2.2
                            linarith only [h10760, hc12, hc25, hlam, hphi, p11726_1]
                          · have p11726_0 := h11726c.1
                            have p11726_1 := h11726c.2.1
                            have p11726_2 := h11726c.2.2.1
                            have p11726_3 := h11726c.2.2.2
                            linarith only [hlam, p11726_0]
                        · linarith only [h10760, h11250, h11724, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p11258_1]
                        · rcases h2bigk with h11781c | h11781c | h11781c | h11781c | h11781c | h11781c | h11781c | h11781c | h11781c | h11781c | h11781c | h11781c | h11781c | h11781c | h11781c | h11781c | h11781c | h11781c | h11781c | h11781c | h11781c | h11781c | h11781c | h11781c | h11781c
                          · have p11781_0 := h11781c.1
                            have p11781_1 := h11781c.2.1
                            have p11781_2 := h11781c.2.2.1
                            have p11781_3 := h11781c.2.2.2
                            linarith only [hlam, p11781_0]
                          · have p11781_0 := h11781c.1
                            have p11781_1 := h11781c.2.1
                            have p11781_2 := h11781c.2.2.1
                            have p11781_3 := h11781c.2.2.2
                            linarith only [h10760, h11250, h4, h9268, hlam, p11258_1, p11781_2]
                          · have p11781_0 := h11781c.1
                            have p11781_1 := h11781c.2.1
                            have p11781_2 := h11781c.2.2.1
                            have p11781_3 := h11781c.2.2.2
                            linarith only [h10760, h11250, h9268, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p11258_1, p11781_1]
                          · have p11781_0 := h11781c.1
                            have p11781_1 := h11781c.2.1
                            have p11781_2 := h11781c.2.2.1
                            have p11781_3 := h11781c.2.2.2
                            rcases p11781_3 (m.d 0 2) (by simp) with h11785 | h11785
                            · rcases p11781_3 (m.d 1 2) (by simp) with h11786 | h11786
                              · linarith only [h0, h11786, hlam]
                              · rcases p11781_3 (m.d 2 3) (by simp) with h11788 | h11788
                                · linarith only [h11788, h4, hlam]
                                · linarith only [h11252, h11788, hlam]
                            · linarith only [h11785, hlam, p11781_0]
                          · have p11781_0 := h11781c.1
                            have p11781_1 := h11781c.2.1
                            have p11781_2 := h11781c.2.2.1
                            have p11781_3 := h11781c.2.2.2
                            rcases p11781_3 (m.d 0 2) (by simp) with h11792 | h11792
                            · rcases p11781_3 (m.d 1 2) (by simp) with h11793 | h11793
                              · linarith only [h0, h11793, hlam]
                              · rcases p11781_3 (m.d 2 3) (by simp) with h11795 | h11795
                                · linarith only [h11795, h4, hlam]
                                · linarith only [h11253, h11795, hlam]
                            · linarith only [h11792, hlam, p11781_0]
                          · have p11781_0 := h11781c.1
                            have p11781_1 := h11781c.2.1
                            have p11781_2 := h11781c.2.2.1
                            have p11781_3 := h11781c.2.2.2
                            linarith only [h0, hlam, p11781_1]
                          · have p11781_0 := h11781c.1
                            have p11781_1 := h11781c.2.1
                            have p11781_2 := h11781c.2.2.1
                            have p11781_3 := h11781c.2.2.2
                            linarith only [hlam, p11781_0]
                          · have p11781_0 := h11781c.1
                            have p11781_1 := h11781c.2.1
                            have p11781_2 := h11781c.2.2.1
                            have p11781_3 := h11781c.2.2.2
                            linarith only [h9268, hlam, p11781_0]
                          · have p11781_0 := h11781c.1
                            have p11781_1 := h11781c.2.1
                            have p11781_2 := h11781c.2.2.1
                            have p11781_3 := h11781c.2.2.2
                            linarith only [h10760, hlam, p11781_0]
                          · have p11781_0 := h11781c.1
                            have p11781_1 := h11781c.2.1
                            have p11781_2 := h11781c.2.2.1
                            have p11781_3 := h11781c.2.2.2
                            linarith only [h11236, hlam, p11781_0]
                          · have p11781_0 := h11781c.1
                            have p11781_1 := h11781c.2.1
                            have p11781_2 := h11781c.2.2.1
                            have p11781_3 := h11781c.2.2.2
                            linarith only [h4, hlam, p11781_0]
                          · have p11781_0 := h11781c.1
                            have p11781_1 := h11781c.2.1
                            have p11781_2 := h11781c.2.2.1
                            have p11781_3 := h11781c.2.2.2
                            rcases p11781_3 (m.d 0 2) (by simp) with h11805 | h11805
                            · rcases p11781_3 (m.d 1 2) (by simp) with h11806 | h11806
                              · linarith only [h11806, hlam, p11781_0]
                              · rcases p11781_3 (m.d 2 3) (by simp) with h11808 | h11808
                                · rcases p11781_3 (m.d 2 4) (by simp) with h11809 | h11809
                                  · linarith only [h11252, h11809, hlam]
                                  · linarith only [h10760, h11809, hlam]
                                · linarith only [h11808, hlam, p11781_0]
                            · linarith only [h0, h11805, hlam]
                          · have p11781_0 := h11781c.1
                            have p11781_1 := h11781c.2.1
                            have p11781_2 := h11781c.2.2.1
                            have p11781_3 := h11781c.2.2.2
                            linarith only [hlam, p11781_0]
                          · have p11781_0 := h11781c.1
                            have p11781_1 := h11781c.2.1
                            have p11781_2 := h11781c.2.2.1
                            have p11781_3 := h11781c.2.2.2
                            linarith only [h10760, hc12, hc23, hlam, hphi, p11781_1]
                          · have p11781_0 := h11781c.1
                            have p11781_1 := h11781c.2.1
                            have p11781_2 := h11781c.2.2.1
                            have p11781_3 := h11781c.2.2.2
                            linarith only [h0, h11236, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p11781_1]
                          · have p11781_0 := h11781c.1
                            have p11781_1 := h11781c.2.1
                            have p11781_2 := h11781c.2.2.1
                            have p11781_3 := h11781c.2.2.2
                            linarith only [h5, hlam, p11781_0]
                          · have p11781_0 := h11781c.1
                            have p11781_1 := h11781c.2.1
                            have p11781_2 := h11781c.2.2.1
                            have p11781_3 := h11781c.2.2.2
                            linarith only [h5, h9, hc12, hc45, hlam, hphi, ht23, ht34, p11781_1]
                          · have p11781_0 := h11781c.1
                            have p11781_1 := h11781c.2.1
                            have p11781_2 := h11781c.2.2.1
                            have p11781_3 := h11781c.2.2.2
                            linarith only [h11252, hlam, p11781_0]
                          · have p11781_0 := h11781c.1
                            have p11781_1 := h11781c.2.1
                            have p11781_2 := h11781c.2.2.1
                            have p11781_3 := h11781c.2.2.2
                            linarith only [hlam, p11781_0]
                          · have p11781_0 := h11781c.1
                            have p11781_1 := h11781c.2.1
                            have p11781_2 := h11781c.2.2.1
                            have p11781_3 := h11781c.2.2.2
                            linarith only [h11254, hlam, p11781_0]
                          · have p11781_0 := h11781c.1
                            have p11781_1 := h11781c.2.1
                            have p11781_2 := h11781c.2.2.1
                            have p11781_3 := h11781c.2.2.2
                            linarith only [h6, hlam, p11781_0]
                          · have p11781_0 := h11781c.1
                            have p11781_1 := h11781c.2.1
                            have p11781_2 := h11781c.2.2.1
                            have p11781_3 := h11781c.2.2.2
                            rcases p11781_3 (m.d 0 2) (by simp) with h11823 | h11823
                            · rcases p11781_3 (m.d 1 2) (by simp) with h11824 | h11824
                              · linarith only [h11824, hlam, p11781_0]
                              · rcases p11781_3 (m.d 2 3) (by simp) with h11826 | h11826
                                · rcases p11781_3 (m.d 2 4) (by simp) with h11827 | h11827
                                  · linarith only [h11254, h11827, hlam]
                                  · linarith only [h10760, h11827, hlam]
                                · linarith only [h11826, h9268, hlam]
                            · linarith only [h0, h11823, hlam]
                          · have p11781_0 := h11781c.1
                            have p11781_1 := h11781c.2.1
                            have p11781_2 := h11781c.2.2.1
                            have p11781_3 := h11781c.2.2.2
                            linarith only [h11253, hlam, p11781_0]
                          · have p11781_0 := h11781c.1
                            have p11781_1 := h11781c.2.1
                            have p11781_2 := h11781c.2.2.1
                            have p11781_3 := h11781c.2.2.2
                            linarith only [h10760, hc12, hc25, hlam, hphi, p11781_1]
                          · have p11781_0 := h11781c.1
                            have p11781_1 := h11781c.2.1
                            have p11781_2 := h11781c.2.2.1
                            have p11781_3 := h11781c.2.2.2
                            linarith only [hlam, p11781_0]
                        · rcases h2bigk with h11835c | h11835c | h11835c | h11835c | h11835c | h11835c | h11835c | h11835c | h11835c | h11835c | h11835c | h11835c | h11835c | h11835c | h11835c | h11835c | h11835c | h11835c | h11835c | h11835c | h11835c | h11835c | h11835c | h11835c | h11835c
                          · have p11835_0 := h11835c.1
                            have p11835_1 := h11835c.2.1
                            have p11835_2 := h11835c.2.2.1
                            have p11835_3 := h11835c.2.2.2
                            linarith only [hlam, p11835_0]
                          · have p11835_0 := h11835c.1
                            have p11835_1 := h11835c.2.1
                            have p11835_2 := h11835c.2.2.1
                            have p11835_3 := h11835c.2.2.2
                            linarith only [h10760, h11250, h4, h9268, hlam, p11258_1, p11835_2]
                          · have p11835_0 := h11835c.1
                            have p11835_1 := h11835c.2.1
                            have p11835_2 := h11835c.2.2.1
                            have p11835_3 := h11835c.2.2.2
                            linarith only [h10760, h11250, h9268, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p11258_1, p11835_1]
                          · have p11835_0 := h11835c.1
                            have p11835_1 := h11835c.2.1
                            have p11835_2 := h11835c.2.2.1
                            have p11835_3 := h11835c.2.2.2
                            rcases p11835_3 (m.d 0 2) (by simp) with h11839 | h11839
                            · rcases p11835_3 (m.d 1 2) (by simp) with h11840 | h11840
                              · linarith only [h0, h11840, hlam]
                              · rcases p11835_3 (m.d 2 3) (by simp) with h11842 | h11842
                                · linarith only [h11842, h4, hlam]
                                · linarith only [h11252, h11842, hlam]
                            · linarith only [h11839, hlam, p11835_0]
                          · have p11835_0 := h11835c.1
                            have p11835_1 := h11835c.2.1
                            have p11835_2 := h11835c.2.2.1
                            have p11835_3 := h11835c.2.2.2
                            rcases p11835_3 (m.d 0 2) (by simp) with h11846 | h11846
                            · rcases p11835_3 (m.d 1 2) (by simp) with h11847 | h11847
                              · linarith only [h0, h11847, hlam]
                              · rcases p11835_3 (m.d 2 3) (by simp) with h11849 | h11849
                                · linarith only [h11849, h4, hlam]
                                · linarith only [h11253, h11849, hlam]
                            · linarith only [h11846, hlam, p11835_0]
                          · have p11835_0 := h11835c.1
                            have p11835_1 := h11835c.2.1
                            have p11835_2 := h11835c.2.2.1
                            have p11835_3 := h11835c.2.2.2
                            linarith only [h0, hlam, p11835_1]
                          · have p11835_0 := h11835c.1
                            have p11835_1 := h11835c.2.1
                            have p11835_2 := h11835c.2.2.1
                            have p11835_3 := h11835c.2.2.2
                            linarith only [hlam, p11835_0]
                          · have p11835_0 := h11835c.1
                            have p11835_1 := h11835c.2.1
                            have p11835_2 := h11835c.2.2.1
                            have p11835_3 := h11835c.2.2.2
                            linarith only [h9268, hlam, p11835_0]
                          · have p11835_0 := h11835c.1
                            have p11835_1 := h11835c.2.1
                            have p11835_2 := h11835c.2.2.1
                            have p11835_3 := h11835c.2.2.2
                            linarith only [h10760, hlam, p11835_0]
                          · have p11835_0 := h11835c.1
                            have p11835_1 := h11835c.2.1
                            have p11835_2 := h11835c.2.2.1
                            have p11835_3 := h11835c.2.2.2
                            linarith only [h11236, hlam, p11835_0]
                          · have p11835_0 := h11835c.1
                            have p11835_1 := h11835c.2.1
                            have p11835_2 := h11835c.2.2.1
                            have p11835_3 := h11835c.2.2.2
                            linarith only [h4, hlam, p11835_0]
                          · have p11835_0 := h11835c.1
                            have p11835_1 := h11835c.2.1
                            have p11835_2 := h11835c.2.2.1
                            have p11835_3 := h11835c.2.2.2
                            rcases p11835_3 (m.d 0 2) (by simp) with h11859 | h11859
                            · rcases p11835_3 (m.d 1 2) (by simp) with h11860 | h11860
                              · linarith only [h11860, hlam, p11835_0]
                              · rcases p11835_3 (m.d 2 3) (by simp) with h11862 | h11862
                                · rcases p11835_3 (m.d 2 4) (by simp) with h11863 | h11863
                                  · linarith only [h11252, h11863, hlam]
                                  · linarith only [h10760, h11863, hlam]
                                · linarith only [h11862, hlam, p11835_0]
                            · linarith only [h0, h11859, hlam]
                          · have p11835_0 := h11835c.1
                            have p11835_1 := h11835c.2.1
                            have p11835_2 := h11835c.2.2.1
                            have p11835_3 := h11835c.2.2.2
                            linarith only [hlam, p11835_0]
                          · have p11835_0 := h11835c.1
                            have p11835_1 := h11835c.2.1
                            have p11835_2 := h11835c.2.2.1
                            have p11835_3 := h11835c.2.2.2
                            linarith only [h10760, hc12, hc23, hlam, hphi, p11835_1]
                          · have p11835_0 := h11835c.1
                            have p11835_1 := h11835c.2.1
                            have p11835_2 := h11835c.2.2.1
                            have p11835_3 := h11835c.2.2.2
                            linarith only [h0, h11236, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p11835_1]
                          · have p11835_0 := h11835c.1
                            have p11835_1 := h11835c.2.1
                            have p11835_2 := h11835c.2.2.1
                            have p11835_3 := h11835c.2.2.2
                            linarith only [h5, hlam, p11835_0]
                          · have p11835_0 := h11835c.1
                            have p11835_1 := h11835c.2.1
                            have p11835_2 := h11835c.2.2.1
                            have p11835_3 := h11835c.2.2.2
                            linarith only [h5, h9, hc12, hc45, hlam, hphi, ht23, ht34, p11835_1]
                          · have p11835_0 := h11835c.1
                            have p11835_1 := h11835c.2.1
                            have p11835_2 := h11835c.2.2.1
                            have p11835_3 := h11835c.2.2.2
                            linarith only [h11252, hlam, p11835_0]
                          · have p11835_0 := h11835c.1
                            have p11835_1 := h11835c.2.1
                            have p11835_2 := h11835c.2.2.1
                            have p11835_3 := h11835c.2.2.2
                            linarith only [hlam, p11835_0]
                          · have p11835_0 := h11835c.1
                            have p11835_1 := h11835c.2.1
                            have p11835_2 := h11835c.2.2.1
                            have p11835_3 := h11835c.2.2.2
                            linarith only [h11254, hlam, p11835_0]
                          · have p11835_0 := h11835c.1
                            have p11835_1 := h11835c.2.1
                            have p11835_2 := h11835c.2.2.1
                            have p11835_3 := h11835c.2.2.2
                            linarith only [h6, hlam, p11835_0]
                          · have p11835_0 := h11835c.1
                            have p11835_1 := h11835c.2.1
                            have p11835_2 := h11835c.2.2.1
                            have p11835_3 := h11835c.2.2.2
                            rcases p11835_3 (m.d 0 2) (by simp) with h11877 | h11877
                            · rcases p11835_3 (m.d 1 2) (by simp) with h11878 | h11878
                              · linarith only [h11878, hlam, p11835_0]
                              · rcases p11835_3 (m.d 2 3) (by simp) with h11880 | h11880
                                · rcases p11835_3 (m.d 2 4) (by simp) with h11881 | h11881
                                  · linarith only [h11254, h11881, hlam]
                                  · linarith only [h10760, h11881, hlam]
                                · linarith only [h11880, h9268, hlam]
                            · linarith only [h0, h11877, hlam]
                          · have p11835_0 := h11835c.1
                            have p11835_1 := h11835c.2.1
                            have p11835_2 := h11835c.2.2.1
                            have p11835_3 := h11835c.2.2.2
                            linarith only [h11253, hlam, p11835_0]
                          · have p11835_0 := h11835c.1
                            have p11835_1 := h11835c.2.1
                            have p11835_2 := h11835c.2.2.1
                            have p11835_3 := h11835c.2.2.2
                            linarith only [h0, h10760, h6, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p11835_1]
                          · have p11835_0 := h11835c.1
                            have p11835_1 := h11835c.2.1
                            have p11835_2 := h11835c.2.2.1
                            have p11835_3 := h11835c.2.2.2
                            linarith only [hlam, p11835_0]
                  · linarith only [h11249, h11719, hlam]
              · linarith only [h11716, h3, hlam]
            · have p11258_0 := h11258c.1
              have p11258_1 := h11258c.2.1
              have p11258_2 := h11258c.2.2.1
              have p11258_3 := h11258c.2.2.2
              linarith only [h2, hlam, p11258_0]
            · have p11258_0 := h11258c.1
              have p11258_1 := h11258c.2.1
              have p11258_2 := h11258c.2.2.1
              have p11258_3 := h11258c.2.2.2
              linarith only [h2, h9, hc12, hc45, hlam, hphi, ht23, ht34, p11258_1]
            · have p11258_0 := h11258c.1
              have p11258_1 := h11258c.2.1
              have p11258_2 := h11258c.2.2.1
              have p11258_3 := h11258c.2.2.2
              linarith only [h11248, hlam, p11258_1]
            · have p11258_0 := h11258c.1
              have p11258_1 := h11258c.2.1
              have p11258_2 := h11258c.2.2.1
              have p11258_3 := h11258c.2.2.2
              linarith only [hlam, p11258_0]
            · have p11258_0 := h11258c.1
              have p11258_1 := h11258c.2.1
              have p11258_2 := h11258c.2.2.1
              have p11258_3 := h11258c.2.2.2
              linarith only [h11250, hlam, p11258_1]
            · have p11258_0 := h11258c.1
              have p11258_1 := h11258c.2.1
              have p11258_2 := h11258c.2.2.1
              have p11258_3 := h11258c.2.2.2
              linarith only [h3, hlam, p11258_0]
            · have p11258_0 := h11258c.1
              have p11258_1 := h11258c.2.1
              have p11258_2 := h11258c.2.2.1
              have p11258_3 := h11258c.2.2.2
              rcases p11258_3 (m.d 0 1) (by simp) with h11897 | h11897
              · rcases p11258_3 (m.d 1 2) (by simp) with h11898 | h11898
                · linarith only [h11236, h11898, hlam]
                · rcases p11258_3 (m.d 1 3) (by simp) with h11900 | h11900
                  · rcases p11258_3 (m.d 1 4) (by simp) with h11901 | h11901
                    · linarith only [h11250, h11901, hlam]
                    · linarith only [h10760, h11901, hlam]
                  · linarith only [h11900, h9268, hlam]
              · linarith only [h0, h11897, hlam]
            · have p11258_0 := h11258c.1
              have p11258_1 := h11258c.2.1
              have p11258_2 := h11258c.2.2.1
              have p11258_3 := h11258c.2.2.2
              linarith only [h11249, hlam, p11258_0]
            · have p11258_0 := h11258c.1
              have p11258_1 := h11258c.2.1
              have p11258_2 := h11258c.2.2.1
              have p11258_3 := h11258c.2.2.2
              rcases p11258_3 (m.d 0 1) (by simp) with h11907 | h11907
              · rcases p11258_3 (m.d 1 2) (by simp) with h11908 | h11908
                · linarith only [h11236, h11908, hlam]
                · rcases p11258_3 (m.d 1 3) (by simp) with h11910 | h11910
                  · rcases p11258_3 (m.d 1 4) (by simp) with h11911 | h11911
                    · linarith only [h11250, h11911, hlam]
                    · rcases p11258_3 (m.d 1 5) (by simp) with h11913 | h11913
                      · rcases h1emax with h11914 | h11914 | h11914 | h11914 | h11914
                        · linarith only [h10760, h11914, h3, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p11258_1]
                        · rcases h2bigk with h11916c | h11916c | h11916c | h11916c | h11916c | h11916c | h11916c | h11916c | h11916c | h11916c | h11916c | h11916c | h11916c | h11916c | h11916c | h11916c | h11916c | h11916c | h11916c | h11916c | h11916c | h11916c | h11916c | h11916c | h11916c
                          · have p11916_0 := h11916c.1
                            have p11916_1 := h11916c.2.1
                            have p11916_2 := h11916c.2.2.1
                            have p11916_3 := h11916c.2.2.2
                            linarith only [hlam, p11916_0]
                          · have p11916_0 := h11916c.1
                            have p11916_1 := h11916c.2.1
                            have p11916_2 := h11916c.2.2.1
                            have p11916_3 := h11916c.2.2.2
                            linarith only [h10760, h11236, h11253, h4, hlam, p11258_1, p11916_2]
                          · have p11916_0 := h11916c.1
                            have p11916_1 := h11916c.2.1
                            have p11916_2 := h11916c.2.2.1
                            have p11916_3 := h11916c.2.2.2
                            linarith only [h0, h10760, h11236, h11253, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p11258_1, p11916_1]
                          · have p11916_0 := h11916c.1
                            have p11916_1 := h11916c.2.1
                            have p11916_2 := h11916c.2.2.1
                            have p11916_3 := h11916c.2.2.2
                            rcases p11916_3 (m.d 0 2) (by simp) with h11920 | h11920
                            · rcases p11916_3 (m.d 1 2) (by simp) with h11921 | h11921
                              · linarith only [h0, h11921, hlam]
                              · rcases p11916_3 (m.d 2 3) (by simp) with h11923 | h11923
                                · linarith only [h11923, h4, hlam]
                                · linarith only [h11252, h11923, hlam]
                            · linarith only [h11920, hlam, p11916_0]
                          · have p11916_0 := h11916c.1
                            have p11916_1 := h11916c.2.1
                            have p11916_2 := h11916c.2.2.1
                            have p11916_3 := h11916c.2.2.2
                            linarith only [h0, h10760, h11236, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p11258_1, p11916_1]
                          · have p11916_0 := h11916c.1
                            have p11916_1 := h11916c.2.1
                            have p11916_2 := h11916c.2.2.1
                            have p11916_3 := h11916c.2.2.2
                            linarith only [h0, hlam, p11916_1]
                          · have p11916_0 := h11916c.1
                            have p11916_1 := h11916c.2.1
                            have p11916_2 := h11916c.2.2.1
                            have p11916_3 := h11916c.2.2.2
                            linarith only [hlam, p11916_0]
                          · have p11916_0 := h11916c.1
                            have p11916_1 := h11916c.2.1
                            have p11916_2 := h11916c.2.2.1
                            have p11916_3 := h11916c.2.2.2
                            linarith only [h9268, hlam, p11916_0]
                          · have p11916_0 := h11916c.1
                            have p11916_1 := h11916c.2.1
                            have p11916_2 := h11916c.2.2.1
                            have p11916_3 := h11916c.2.2.2
                            linarith only [h10760, hlam, p11916_0]
                          · have p11916_0 := h11916c.1
                            have p11916_1 := h11916c.2.1
                            have p11916_2 := h11916c.2.2.1
                            have p11916_3 := h11916c.2.2.2
                            linarith only [h11236, hlam, p11916_0]
                          · have p11916_0 := h11916c.1
                            have p11916_1 := h11916c.2.1
                            have p11916_2 := h11916c.2.2.1
                            have p11916_3 := h11916c.2.2.2
                            linarith only [h4, hlam, p11916_0]
                          · have p11916_0 := h11916c.1
                            have p11916_1 := h11916c.2.1
                            have p11916_2 := h11916c.2.2.1
                            have p11916_3 := h11916c.2.2.2
                            rcases p11916_3 (m.d 0 2) (by simp) with h11934 | h11934
                            · rcases p11916_3 (m.d 1 2) (by simp) with h11935 | h11935
                              · linarith only [h11935, hlam, p11916_0]
                              · rcases p11916_3 (m.d 2 3) (by simp) with h11937 | h11937
                                · rcases p11916_3 (m.d 2 4) (by simp) with h11938 | h11938
                                  · linarith only [h11252, h11938, hlam]
                                  · linarith only [h10760, h11938, hlam]
                                · linarith only [h11937, hlam, p11916_0]
                            · linarith only [h0, h11934, hlam]
                          · have p11916_0 := h11916c.1
                            have p11916_1 := h11916c.2.1
                            have p11916_2 := h11916c.2.2.1
                            have p11916_3 := h11916c.2.2.2
                            linarith only [hlam, p11916_0]
                          · have p11916_0 := h11916c.1
                            have p11916_1 := h11916c.2.1
                            have p11916_2 := h11916c.2.2.1
                            have p11916_3 := h11916c.2.2.2
                            linarith only [h10760, hc12, hc23, hlam, hphi, p11916_1]
                          · have p11916_0 := h11916c.1
                            have p11916_1 := h11916c.2.1
                            have p11916_2 := h11916c.2.2.1
                            have p11916_3 := h11916c.2.2.2
                            linarith only [h0, h10760, h11236, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p11258_1, p11916_1]
                          · have p11916_0 := h11916c.1
                            have p11916_1 := h11916c.2.1
                            have p11916_2 := h11916c.2.2.1
                            have p11916_3 := h11916c.2.2.2
                            linarith only [h5, hlam, p11916_0]
                          · have p11916_0 := h11916c.1
                            have p11916_1 := h11916c.2.1
                            have p11916_2 := h11916c.2.2.1
                            have p11916_3 := h11916c.2.2.2
                            linarith only [h5, h9, hc12, hc45, hlam, hphi, ht23, ht34, p11916_1]
                          · have p11916_0 := h11916c.1
                            have p11916_1 := h11916c.2.1
                            have p11916_2 := h11916c.2.2.1
                            have p11916_3 := h11916c.2.2.2
                            linarith only [h11252, hlam, p11916_0]
                          · have p11916_0 := h11916c.1
                            have p11916_1 := h11916c.2.1
                            have p11916_2 := h11916c.2.2.1
                            have p11916_3 := h11916c.2.2.2
                            linarith only [hlam, p11916_0]
                          · have p11916_0 := h11916c.1
                            have p11916_1 := h11916c.2.1
                            have p11916_2 := h11916c.2.2.1
                            have p11916_3 := h11916c.2.2.2
                            linarith only [h11254, hlam, p11916_0]
                          · have p11916_0 := h11916c.1
                            have p11916_1 := h11916c.2.1
                            have p11916_2 := h11916c.2.2.1
                            have p11916_3 := h11916c.2.2.2
                            linarith only [h6, hlam, p11916_0]
                          · have p11916_0 := h11916c.1
                            have p11916_1 := h11916c.2.1
                            have p11916_2 := h11916c.2.2.1
                            have p11916_3 := h11916c.2.2.2
                            rcases p11916_3 (m.d 0 2) (by simp) with h11952 | h11952
                            · rcases p11916_3 (m.d 1 2) (by simp) with h11953 | h11953
                              · linarith only [h11953, hlam, p11916_0]
                              · rcases p11916_3 (m.d 2 3) (by simp) with h11955 | h11955
                                · rcases p11916_3 (m.d 2 4) (by simp) with h11956 | h11956
                                  · linarith only [h11254, h11956, hlam]
                                  · linarith only [h10760, h11956, hlam]
                                · linarith only [h11955, h9268, hlam]
                            · linarith only [h0, h11952, hlam]
                          · have p11916_0 := h11916c.1
                            have p11916_1 := h11916c.2.1
                            have p11916_2 := h11916c.2.2.1
                            have p11916_3 := h11916c.2.2.2
                            linarith only [h11253, hlam, p11916_0]
                          · have p11916_0 := h11916c.1
                            have p11916_1 := h11916c.2.1
                            have p11916_2 := h11916c.2.2.1
                            have p11916_3 := h11916c.2.2.2
                            linarith only [h10760, hc12, hc25, hlam, hphi, p11916_1]
                          · have p11916_0 := h11916c.1
                            have p11916_1 := h11916c.2.1
                            have p11916_2 := h11916c.2.2.1
                            have p11916_3 := h11916c.2.2.2
                            linarith only [hlam, p11916_0]
                        · linarith only [h10760, h11249, h11914, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p11258_1]
                        · rcases h2bigk with h11965c | h11965c | h11965c | h11965c | h11965c | h11965c | h11965c | h11965c | h11965c | h11965c | h11965c | h11965c | h11965c | h11965c | h11965c | h11965c | h11965c | h11965c | h11965c | h11965c | h11965c | h11965c | h11965c | h11965c | h11965c
                          · have p11965_0 := h11965c.1
                            have p11965_1 := h11965c.2.1
                            have p11965_2 := h11965c.2.2.1
                            have p11965_3 := h11965c.2.2.2
                            linarith only [hlam, p11965_0]
                          · have p11965_0 := h11965c.1
                            have p11965_1 := h11965c.2.1
                            have p11965_2 := h11965c.2.2.1
                            have p11965_3 := h11965c.2.2.2
                            linarith only [h10760, h11249, h4, h9268, hlam, p11258_1, p11965_2]
                          · have p11965_0 := h11965c.1
                            have p11965_1 := h11965c.2.1
                            have p11965_2 := h11965c.2.2.1
                            have p11965_3 := h11965c.2.2.2
                            linarith only [h10760, h11249, h9268, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p11258_1, p11965_1]
                          · have p11965_0 := h11965c.1
                            have p11965_1 := h11965c.2.1
                            have p11965_2 := h11965c.2.2.1
                            have p11965_3 := h11965c.2.2.2
                            rcases p11965_3 (m.d 0 2) (by simp) with h11969 | h11969
                            · rcases p11965_3 (m.d 1 2) (by simp) with h11970 | h11970
                              · linarith only [h0, h11970, hlam]
                              · rcases p11965_3 (m.d 2 3) (by simp) with h11972 | h11972
                                · linarith only [h11972, h4, hlam]
                                · linarith only [h11252, h11972, hlam]
                            · linarith only [h11969, hlam, p11965_0]
                          · have p11965_0 := h11965c.1
                            have p11965_1 := h11965c.2.1
                            have p11965_2 := h11965c.2.2.1
                            have p11965_3 := h11965c.2.2.2
                            linarith only [h0, h10760, h11236, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p11258_1, p11965_1]
                          · have p11965_0 := h11965c.1
                            have p11965_1 := h11965c.2.1
                            have p11965_2 := h11965c.2.2.1
                            have p11965_3 := h11965c.2.2.2
                            linarith only [h0, hlam, p11965_1]
                          · have p11965_0 := h11965c.1
                            have p11965_1 := h11965c.2.1
                            have p11965_2 := h11965c.2.2.1
                            have p11965_3 := h11965c.2.2.2
                            linarith only [hlam, p11965_0]
                          · have p11965_0 := h11965c.1
                            have p11965_1 := h11965c.2.1
                            have p11965_2 := h11965c.2.2.1
                            have p11965_3 := h11965c.2.2.2
                            linarith only [h9268, hlam, p11965_0]
                          · have p11965_0 := h11965c.1
                            have p11965_1 := h11965c.2.1
                            have p11965_2 := h11965c.2.2.1
                            have p11965_3 := h11965c.2.2.2
                            linarith only [h10760, hlam, p11965_0]
                          · have p11965_0 := h11965c.1
                            have p11965_1 := h11965c.2.1
                            have p11965_2 := h11965c.2.2.1
                            have p11965_3 := h11965c.2.2.2
                            linarith only [h11236, hlam, p11965_0]
                          · have p11965_0 := h11965c.1
                            have p11965_1 := h11965c.2.1
                            have p11965_2 := h11965c.2.2.1
                            have p11965_3 := h11965c.2.2.2
                            linarith only [h4, hlam, p11965_0]
                          · have p11965_0 := h11965c.1
                            have p11965_1 := h11965c.2.1
                            have p11965_2 := h11965c.2.2.1
                            have p11965_3 := h11965c.2.2.2
                            rcases p11965_3 (m.d 0 2) (by simp) with h11983 | h11983
                            · rcases p11965_3 (m.d 1 2) (by simp) with h11984 | h11984
                              · linarith only [h11984, hlam, p11965_0]
                              · rcases p11965_3 (m.d 2 3) (by simp) with h11986 | h11986
                                · rcases p11965_3 (m.d 2 4) (by simp) with h11987 | h11987
                                  · linarith only [h11252, h11987, hlam]
                                  · linarith only [h10760, h11987, hlam]
                                · linarith only [h11986, hlam, p11965_0]
                            · linarith only [h0, h11983, hlam]
                          · have p11965_0 := h11965c.1
                            have p11965_1 := h11965c.2.1
                            have p11965_2 := h11965c.2.2.1
                            have p11965_3 := h11965c.2.2.2
                            linarith only [hlam, p11965_0]
                          · have p11965_0 := h11965c.1
                            have p11965_1 := h11965c.2.1
                            have p11965_2 := h11965c.2.2.1
                            have p11965_3 := h11965c.2.2.2
                            linarith only [h10760, hc12, hc23, hlam, hphi, p11965_1]
                          · have p11965_0 := h11965c.1
                            have p11965_1 := h11965c.2.1
                            have p11965_2 := h11965c.2.2.1
                            have p11965_3 := h11965c.2.2.2
                            linarith only [h0, h10760, h11236, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p11258_1, p11965_1]
                          · have p11965_0 := h11965c.1
                            have p11965_1 := h11965c.2.1
                            have p11965_2 := h11965c.2.2.1
                            have p11965_3 := h11965c.2.2.2
                            linarith only [h5, hlam, p11965_0]
                          · have p11965_0 := h11965c.1
                            have p11965_1 := h11965c.2.1
                            have p11965_2 := h11965c.2.2.1
                            have p11965_3 := h11965c.2.2.2
                            linarith only [h5, h9, hc12, hc45, hlam, hphi, ht23, ht34, p11965_1]
                          · have p11965_0 := h11965c.1
                            have p11965_1 := h11965c.2.1
                            have p11965_2 := h11965c.2.2.1
                            have p11965_3 := h11965c.2.2.2
                            linarith only [h11252, hlam, p11965_0]
                          · have p11965_0 := h11965c.1
                            have p11965_1 := h11965c.2.1
                            have p11965_2 := h11965c.2.2.1
                            have p11965_3 := h11965c.2.2.2
                            linarith only [hlam, p11965_0]
                          · have p11965_0 := h11965c.1
                            have p11965_1 := h11965c.2.1
                            have p11965_2 := h11965c.2.2.1
                            have p11965_3 := h11965c.2.2.2
                            linarith only [h11254, hlam, p11965_0]
                          · have p11965_0 := h11965c.1
                            have p11965_1 := h11965c.2.1
                            have p11965_2 := h11965c.2.2.1
                            have p11965_3 := h11965c.2.2.2
                            linarith only [h6, hlam, p11965_0]
                          · have p11965_0 := h11965c.1
                            have p11965_1 := h11965c.2.1
                            have p11965_2 := h11965c.2.2.1
                            have p11965_3 := h11965c.2.2.2
                            rcases p11965_3 (m.d 0 2) (by simp) with h12001 | h12001
                            · rcases p11965_3 (m.d 1 2) (by simp) with h12002 | h12002
                              · linarith only [h12002, hlam, p11965_0]
                              · rcases p11965_3 (m.d 2 3) (by simp) with h12004 | h12004
                                · rcases p11965_3 (m.d 2 4) (by simp) with h12005 | h12005
                                  · linarith only [h11254, h12005, hlam]
                                  · linarith only [h10760, h12005, hlam]
                                · linarith only [h12004, h9268, hlam]
                            · linarith only [h0, h12001, hlam]
                          · have p11965_0 := h11965c.1
                            have p11965_1 := h11965c.2.1
                            have p11965_2 := h11965c.2.2.1
                            have p11965_3 := h11965c.2.2.2
                            linarith only [h11253, hlam, p11965_0]
                          · have p11965_0 := h11965c.1
                            have p11965_1 := h11965c.2.1
                            have p11965_2 := h11965c.2.2.1
                            have p11965_3 := h11965c.2.2.2
                            linarith only [h10760, hc12, hc25, hlam, hphi, p11965_1]
                          · have p11965_0 := h11965c.1
                            have p11965_1 := h11965c.2.1
                            have p11965_2 := h11965c.2.2.1
                            have p11965_3 := h11965c.2.2.2
                            linarith only [hlam, p11965_0]
                        · linarith only [h10760, h11914, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p11258_1]
                      · linarith only [h11250, h11913, hlam]
                  · linarith only [h11248, h11910, hlam]
              · linarith only [h11907, h2, hlam]
            · have p11258_0 := h11258c.1
              have p11258_1 := h11258c.2.1
              have p11258_2 := h11258c.2.2.1
              have p11258_3 := h11258c.2.2.2
              linarith only [hlam, p11258_0]
      · linarith only [h11249, h11253, h9268, hlam]
    · linarith only [h11252, h7, h9, h9268, hc12, hc45, hlam, hphi, ht23, ht34]

end R2N4
