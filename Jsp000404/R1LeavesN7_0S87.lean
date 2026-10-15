import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 22102000 in
set_option maxHeartbeats 22102000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s37_x0_x0_x0_x0_x0_x0_x0_x1_x0_x0_x0_x0_x0_x1_x0_x0_x1_x1_x4 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg33187 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h36828 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h36829 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h36830 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h36831 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h36832 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h36833 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h36834 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h36835 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h37309 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h37310 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h37311 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h37312 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h37313 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h37314 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h37316 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h37317 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
    (h37318 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h37320 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h37322c : ((m.d 0 1) < (m.d 1 5) ∧ 2 * m.lam ≤ (m.d 1 5) - (m.d 0 1) ∧ (m.d 1 5) - (m.d 0 1) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)], z ≤ (m.d 0 1) ∨ (m.d 1 5) ≤ z)))
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
  have h5bigk := hb5.1
  have h0 := hg0
  have h33187 := hg33187
  have p37322_0 := h37322c.1
  have p37322_1 := h37322c.2.1
  have p37322_2 := h37322c.2.2.1
  have p37322_3 := h37322c.2.2.2
  rcases p37322_3 (m.d 0 1) (by simp) with h37337 | h37337
  · rcases p37322_3 (m.d 1 2) (by simp) with h37338 | h37338
    · rcases p37322_3 (m.d 1 3) (by simp) with h37339 | h37339
      · rcases p37322_3 (m.d 1 4) (by simp) with h37340 | h37340
        · linarith only [h36828, h37340, hlam]
        · rcases p37322_3 (m.d 1 5) (by simp) with h37342 | h37342
          · linarith only [h37342, hlam, p37322_0]
          · rcases h1emax with h37344 | h37344 | h37344 | h37344 | h37344
            · linarith only [h37314, h37344, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p37322_1]
            · linarith only [h33187, h37309, h37310, h37314, h37316, h37344, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p37322_1]
            · linarith only [h33187, h37310, h37314, h37316, h37344, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p37322_1]
            · rcases h2bigk with h37348c | h37348c | h37348c | h37348c | h37348c | h37348c | h37348c | h37348c | h37348c | h37348c | h37348c | h37348c | h37348c | h37348c | h37348c | h37348c | h37348c | h37348c | h37348c | h37348c | h37348c | h37348c | h37348c | h37348c | h37348c
              · have p37348_0 := h37348c.1
                have p37348_1 := h37348c.2.1
                have p37348_2 := h37348c.2.2.1
                have p37348_3 := h37348c.2.2.2
                linarith only [hlam, p37348_0]
              · have p37348_0 := h37348c.1
                have p37348_1 := h37348c.2.1
                have p37348_2 := h37348c.2.2.1
                have p37348_3 := h37348c.2.2.2
                linarith only [h0, hlam, p37348_0]
              · have p37348_0 := h37348c.1
                have p37348_1 := h37348c.2.1
                have p37348_2 := h37348c.2.2.1
                have p37348_3 := h37348c.2.2.2
                rcases p37348_3 (m.d 0 2) (by simp) with h37351 | h37351
                · rcases p37348_3 (m.d 1 2) (by simp) with h37352 | h37352
                  · rcases p37348_3 (m.d 2 3) (by simp) with h37353 | h37353
                    · linarith only [h37353, hlam, p37348_0]
                    · rcases p37348_3 (m.d 2 4) (by simp) with h37355 | h37355
                      · linarith only [h36831, h37355, hlam]
                      · rcases p37348_3 (m.d 2 5) (by simp) with h37357 | h37357
                        · linarith only [h36832, h37357, hlam]
                        · rcases h4bigk with h37359c | h37359c | h37359c | h37359c | h37359c | h37359c | h37359c | h37359c | h37359c | h37359c | h37359c | h37359c | h37359c | h37359c | h37359c | h37359c | h37359c | h37359c | h37359c | h37359c | h37359c | h37359c | h37359c | h37359c | h37359c
                          · have p37359_0 := h37359c.1
                            have p37359_1 := h37359c.2.1
                            have p37359_2 := h37359c.2.2.1
                            have p37359_3 := h37359c.2.2.2
                            linarith only [hlam, p37359_0]
                          · have p37359_0 := h37359c.1
                            have p37359_1 := h37359c.2.1
                            have p37359_2 := h37359c.2.2.1
                            have p37359_3 := h37359c.2.2.2
                            linarith only [h36835, h37310, h37316, hc34, hc45, hlam, hphi, p37359_1]
                          · have p37359_0 := h37359c.1
                            have p37359_1 := h37359c.2.1
                            have p37359_2 := h37359c.2.2.1
                            have p37359_3 := h37359c.2.2.2
                            linarith only [h36835, h37316, hc34, hc45, hlam, hphi, p37359_1]
                          · have p37359_0 := h37359c.1
                            have p37359_1 := h37359c.2.1
                            have p37359_2 := h37359c.2.2.1
                            have p37359_3 := h37359c.2.2.2
                            linarith only [h36835, hc34, hc45, hlam, hphi, p37359_1]
                          · have p37359_0 := h37359c.1
                            have p37359_1 := h37359c.2.1
                            have p37359_2 := h37359c.2.2.1
                            have p37359_3 := h37359c.2.2.2
                            linarith only [h36835, hlam, p37359_0]
                          · have p37359_0 := h37359c.1
                            have p37359_1 := h37359c.2.1
                            have p37359_2 := h37359c.2.2.1
                            have p37359_3 := h37359c.2.2.2
                            linarith only [h36828, hlam, p37359_0]
                          · have p37359_0 := h37359c.1
                            have p37359_1 := h37359c.2.1
                            have p37359_2 := h37359c.2.2.1
                            have p37359_3 := h37359c.2.2.2
                            linarith only [hlam, p37359_0]
                          · have p37359_0 := h37359c.1
                            have p37359_1 := h37359c.2.1
                            have p37359_2 := h37359c.2.2.1
                            have p37359_3 := h37359c.2.2.2
                            linarith only [h37314, h37316, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p37322_1, p37359_1]
                          · have p37359_0 := h37359c.1
                            have p37359_1 := h37359c.2.1
                            have p37359_2 := h37359c.2.2.1
                            have p37359_3 := h37359c.2.2.2
                            linarith only [h33187, h37309, h37314, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p37322_1, p37359_1]
                          · have p37359_0 := h37359c.1
                            have p37359_1 := h37359c.2.1
                            have p37359_2 := h37359c.2.2.1
                            have p37359_3 := h37359c.2.2.2
                            linarith only [h37314, hlam, p37359_0]
                          · have p37359_0 := h37359c.1
                            have p37359_1 := h37359c.2.1
                            have p37359_2 := h37359c.2.2.1
                            have p37359_3 := h37359c.2.2.2
                            linarith only [h36831, hlam, p37359_0]
                          · have p37359_0 := h37359c.1
                            have p37359_1 := h37359c.2.1
                            have p37359_2 := h37359c.2.2.1
                            have p37359_3 := h37359c.2.2.2
                            linarith only [h37310, hlam, p37359_0]
                          · have p37359_0 := h37359c.1
                            have p37359_1 := h37359c.2.1
                            have p37359_2 := h37359c.2.2.1
                            have p37359_3 := h37359c.2.2.2
                            linarith only [hlam, p37359_0]
                          · have p37359_0 := h37359c.1
                            have p37359_1 := h37359c.2.1
                            have p37359_2 := h37359c.2.2.1
                            have p37359_3 := h37359c.2.2.2
                            linarith only [h36831, h36835, hc34, hc45, hlam, hphi, p37359_1]
                          · have p37359_0 := h37359c.1
                            have p37359_1 := h37359c.2.1
                            have p37359_2 := h37359c.2.2.1
                            have p37359_3 := h37359c.2.2.2
                            linarith only [h37318, hlam, p37359_0]
                          · have p37359_0 := h37359c.1
                            have p37359_1 := h37359c.2.1
                            have p37359_2 := h37359c.2.2.1
                            have p37359_3 := h37359c.2.2.2
                            linarith only [h36833, hlam, p37359_0]
                          · have p37359_0 := h37359c.1
                            have p37359_1 := h37359c.2.1
                            have p37359_2 := h37359c.2.2.1
                            have p37359_3 := h37359c.2.2.2
                            linarith only [h37312, hlam, p37359_0]
                          · have p37359_0 := h37359c.1
                            have p37359_1 := h37359c.2.1
                            have p37359_2 := h37359c.2.2.1
                            have p37359_3 := h37359c.2.2.2
                            linarith only [h37316, hlam, p37359_0]
                          · have p37359_0 := h37359c.1
                            have p37359_1 := h37359c.2.1
                            have p37359_2 := h37359c.2.2.1
                            have p37359_3 := h37359c.2.2.2
                            linarith only [hlam, p37359_0]
                          · have p37359_0 := h37359c.1
                            have p37359_1 := h37359c.2.1
                            have p37359_2 := h37359c.2.2.1
                            have p37359_3 := h37359c.2.2.2
                            linarith only [h37320, hlam, p37359_0]
                          · have p37359_0 := h37359c.1
                            have p37359_1 := h37359c.2.1
                            have p37359_2 := h37359c.2.2.1
                            have p37359_3 := h37359c.2.2.2
                            rcases p37359_3 (m.d 0 4) (by simp) with h37380 | h37380
                            · linarith only [h37380, hlam, p37359_0]
                            · rcases p37359_3 (m.d 1 4) (by simp) with h37382 | h37382
                              · linarith only [h37314, h37382, hlam]
                              · rcases p37359_3 (m.d 2 4) (by simp) with h37384 | h37384
                                · linarith only [h37318, h37384, hlam]
                                · rcases p37359_3 (m.d 3 4) (by simp) with h37386 | h37386
                                  · linarith only [h37320, h37386, hlam]
                                  · rcases p37359_3 (m.d 4 5) (by simp) with h37388 | h37388
                                    · rcases h5bigk with h37389c | h37389c | h37389c | h37389c | h37389c | h37389c | h37389c | h37389c | h37389c | h37389c | h37389c | h37389c | h37389c | h37389c | h37389c | h37389c | h37389c | h37389c | h37389c | h37389c | h37389c | h37389c | h37389c | h37389c | h37389c
                                      · have p37389_0 := h37389c.1
                                        have p37389_1 := h37389c.2.1
                                        have p37389_2 := h37389c.2.2.1
                                        have p37389_3 := h37389c.2.2.2
                                        linarith only [hlam, p37389_0]
                                      · have p37389_0 := h37389c.1
                                        have p37389_1 := h37389c.2.1
                                        have p37389_2 := h37389c.2.2.1
                                        have p37389_3 := h37389c.2.2.2
                                        linarith only [h33187, h36829, h37309, h37314, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p37389_1]
                                      · have p37389_0 := h37389c.1
                                        have p37389_1 := h37389c.2.1
                                        have p37389_2 := h37389c.2.2.1
                                        have p37389_3 := h37389c.2.2.2
                                        linarith only [h33187, h36829, h37309, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p37389_1]
                                      · have p37389_0 := h37389c.1
                                        have p37389_1 := h37389c.2.1
                                        have p37389_2 := h37389c.2.2.1
                                        have p37389_3 := h37389c.2.2.2
                                        linarith only [h33187, h36829, h37309, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p37389_1]
                                      · have p37389_0 := h37389c.1
                                        have p37389_1 := h37389c.2.1
                                        have p37389_2 := h37389c.2.2.1
                                        have p37389_3 := h37389c.2.2.2
                                        linarith only [h36835, hlam, p37389_0]
                                      · have p37389_0 := h37389c.1
                                        have p37389_1 := h37389c.2.1
                                        have p37389_2 := h37389c.2.2.1
                                        have p37389_3 := h37389c.2.2.2
                                        linarith only [h36829, hlam, p37389_0]
                                      · have p37389_0 := h37389c.1
                                        have p37389_1 := h37389c.2.1
                                        have p37389_2 := h37389c.2.2.1
                                        have p37389_3 := h37389c.2.2.2
                                        linarith only [hlam, p37389_0]
                                      · have p37389_0 := h37389c.1
                                        have p37389_1 := h37389c.2.1
                                        have p37389_2 := h37389c.2.2.1
                                        have p37389_3 := h37389c.2.2.2
                                        linarith only [h33187, h37309, h37317, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p37322_1, p37389_1]
                                      · have p37389_0 := h37389c.1
                                        have p37389_1 := h37389c.2.1
                                        have p37389_2 := h37389c.2.2.1
                                        have p37389_3 := h37389c.2.2.2
                                        linarith only [h33187, h37309, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p37322_1, p37389_1]
                                      · have p37389_0 := h37389c.1
                                        have p37389_1 := h37389c.2.1
                                        have p37389_2 := h37389c.2.2.1
                                        have p37389_3 := h37389c.2.2.2
                                        linarith only [h37314, hlam, p37389_0]
                                      · have p37389_0 := h37389c.1
                                        have p37389_1 := h37389c.2.1
                                        have p37389_2 := h37389c.2.2.1
                                        have p37389_3 := h37389c.2.2.2
                                        linarith only [h36832, hlam, p37389_1]
                                      · have p37389_0 := h37389c.1
                                        have p37389_1 := h37389c.2.1
                                        have p37389_2 := h37389c.2.2.1
                                        have p37389_3 := h37389c.2.2.2
                                        linarith only [h37311, hlam, p37389_1]
                                      · have p37389_0 := h37389c.1
                                        have p37389_1 := h37389c.2.1
                                        have p37389_2 := h37389c.2.2.1
                                        have p37389_3 := h37389c.2.2.2
                                        linarith only [hlam, p37389_0]
                                      · have p37389_0 := h37389c.1
                                        have p37389_1 := h37389c.2.1
                                        have p37389_2 := h37389c.2.2.1
                                        have p37389_3 := h37389c.2.2.2
                                        linarith only [h0, h36832, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p37389_1]
                                      · have p37389_0 := h37389c.1
                                        have p37389_1 := h37389c.2.1
                                        have p37389_2 := h37389c.2.2.1
                                        have p37389_3 := h37389c.2.2.2
                                        linarith only [h37318, hlam, p37389_0]
                                      · have p37389_0 := h37389c.1
                                        have p37389_1 := h37389c.2.1
                                        have p37389_2 := h37389c.2.2.1
                                        have p37389_3 := h37389c.2.2.2
                                        linarith only [h36834, hlam, p37389_1]
                                      · have p37389_0 := h37389c.1
                                        have p37389_1 := h37389c.2.1
                                        have p37389_2 := h37389c.2.2.1
                                        have p37389_3 := h37389c.2.2.2
                                        linarith only [h37313, hlam, p37389_1]
                                      · have p37389_0 := h37389c.1
                                        have p37389_1 := h37389c.2.1
                                        have p37389_2 := h37389c.2.2.1
                                        have p37389_3 := h37389c.2.2.2
                                        linarith only [h37317, hlam, p37389_0]
                                      · have p37389_0 := h37389c.1
                                        have p37389_1 := h37389c.2.1
                                        have p37389_2 := h37389c.2.2.1
                                        have p37389_3 := h37389c.2.2.2
                                        linarith only [hlam, p37389_0]
                                      · have p37389_0 := h37389c.1
                                        have p37389_1 := h37389c.2.1
                                        have p37389_2 := h37389c.2.2.1
                                        have p37389_3 := h37389c.2.2.2
                                        linarith only [h37320, hlam, p37389_0]
                                      · have p37389_0 := h37389c.1
                                        have p37389_1 := h37389c.2.1
                                        have p37389_2 := h37389c.2.2.1
                                        have p37389_3 := h37389c.2.2.2
                                        linarith only [h36835, hc04, hc45, hlam, hphi, p37389_1]
                                      · have p37389_0 := h37389c.1
                                        have p37389_1 := h37389c.2.1
                                        have p37389_2 := h37389c.2.2.1
                                        have p37389_3 := h37389c.2.2.2
                                        linarith only [h37310, h37314, hc24, hc45, hlam, hphi, p37389_1]
                                      · have p37389_0 := h37389c.1
                                        have p37389_1 := h37389c.2.1
                                        have p37389_2 := h37389c.2.2.1
                                        have p37389_3 := h37389c.2.2.2
                                        linarith only [h37316, h37318, hc34, hc45, hlam, hphi, p37389_1]
                                      · have p37389_0 := h37389c.1
                                        have p37389_1 := h37389c.2.1
                                        have p37389_2 := h37389c.2.2.1
                                        have p37389_3 := h37389c.2.2.2
                                        linarith only [h37320, hc34, hc45, hlam, hphi, p37389_1]
                                      · have p37389_0 := h37389c.1
                                        have p37389_1 := h37389c.2.1
                                        have p37389_2 := h37389c.2.2.1
                                        have p37389_3 := h37389c.2.2.2
                                        linarith only [hlam, p37389_0]
                                    · linarith only [h37388, hlam, p37359_0]
                          · have p37359_0 := h37359c.1
                            have p37359_1 := h37359c.2.1
                            have p37359_2 := h37359c.2.2.1
                            have p37359_3 := h37359c.2.2.2
                            rcases p37359_3 (m.d 0 4) (by simp) with h37416 | h37416
                            · linarith only [h36835, h37416, hlam]
                            · linarith only [h36828, h37416, hlam]
                          · have p37359_0 := h37359c.1
                            have p37359_1 := h37359c.2.1
                            have p37359_2 := h37359c.2.2.1
                            have p37359_3 := h37359c.2.2.2
                            rcases p37359_3 (m.d 0 4) (by simp) with h37419 | h37419
                            · linarith only [h36835, h37419, hlam]
                            · linarith only [h36831, h37419, hlam]
                          · have p37359_0 := h37359c.1
                            have p37359_1 := h37359c.2.1
                            have p37359_2 := h37359c.2.2.1
                            have p37359_3 := h37359c.2.2.2
                            rcases p37359_3 (m.d 0 4) (by simp) with h37422 | h37422
                            · linarith only [h36835, h37422, hlam]
                            · linarith only [h36833, h37422, hlam]
                          · have p37359_0 := h37359c.1
                            have p37359_1 := h37359c.2.1
                            have p37359_2 := h37359c.2.2.1
                            have p37359_3 := h37359c.2.2.2
                            linarith only [hlam, p37359_0]
                  · linarith only [h37309, h37352, hlam]
                · linarith only [h37351, hlam, p37348_0]
              · have p37348_0 := h37348c.1
                have p37348_1 := h37348c.2.1
                have p37348_2 := h37348c.2.2.1
                have p37348_3 := h37348c.2.2.2
                rcases p37348_3 (m.d 0 2) (by simp) with h37428 | h37428
                · rcases p37348_3 (m.d 1 2) (by simp) with h37429 | h37429
                  · rcases p37348_3 (m.d 2 3) (by simp) with h37430 | h37430
                    · linarith only [h36830, h37430, hlam]
                    · linarith only [h37316, h37430, hlam]
                  · linarith only [h37310, h37429, hlam]
                · linarith only [h37428, hlam, p37348_0]
              · have p37348_0 := h37348c.1
                have p37348_1 := h37348c.2.1
                have p37348_2 := h37348c.2.2.1
                have p37348_3 := h37348c.2.2.2
                rcases p37348_3 (m.d 0 2) (by simp) with h37435 | h37435
                · rcases p37348_3 (m.d 1 2) (by simp) with h37436 | h37436
                  · rcases p37348_3 (m.d 2 3) (by simp) with h37437 | h37437
                    · linarith only [h36830, h37437, hlam]
                    · linarith only [h37317, h37437, hlam]
                  · linarith only [h37311, h37436, hlam]
                · linarith only [h37435, hlam, p37348_0]
              · have p37348_0 := h37348c.1
                have p37348_1 := h37348c.2.1
                have p37348_2 := h37348c.2.2.1
                have p37348_3 := h37348c.2.2.2
                linarith only [h33187, h36830, h37310, h37314, h37316, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p37322_1, p37348_1]
              · have p37348_0 := h37348c.1
                have p37348_1 := h37348c.2.1
                have p37348_2 := h37348c.2.2.1
                have p37348_3 := h37348c.2.2.2
                linarith only [hlam, p37348_0]
              · have p37348_0 := h37348c.1
                have p37348_1 := h37348c.2.1
                have p37348_2 := h37348c.2.2.1
                have p37348_3 := h37348c.2.2.2
                rcases p37348_3 (m.d 0 2) (by simp) with h37444 | h37444
                · linarith only [h0, h37444, hlam]
                · linarith only [h36830, h37444, hlam]
              · have p37348_0 := h37348c.1
                have p37348_1 := h37348c.2.1
                have p37348_2 := h37348c.2.2.1
                have p37348_3 := h37348c.2.2.2
                linarith only [h0, h37310, h37314, hlam, p37322_1, p37348_2]
              · have p37348_0 := h37348c.1
                have p37348_1 := h37348c.2.1
                have p37348_2 := h37348c.2.2.1
                have p37348_3 := h37348c.2.2.2
                linarith only [h33187, h37309, h37311, hlam, p37322_1, p37348_2]
              · have p37348_0 := h37348c.1
                have p37348_1 := h37348c.2.1
                have p37348_2 := h37348c.2.2.1
                have p37348_3 := h37348c.2.2.2
                linarith only [h36830, hlam, p37348_0]
              · have p37348_0 := h37348c.1
                have p37348_1 := h37348c.2.1
                have p37348_2 := h37348c.2.2.1
                have p37348_3 := h37348c.2.2.2
                linarith only [h37309, hlam, p37348_0]
              · have p37348_0 := h37348c.1
                have p37348_1 := h37348c.2.1
                have p37348_2 := h37348c.2.2.1
                have p37348_3 := h37348c.2.2.2
                linarith only [hlam, p37348_0]
              · have p37348_0 := h37348c.1
                have p37348_1 := h37348c.2.1
                have p37348_2 := h37348c.2.2.1
                have p37348_3 := h37348c.2.2.2
                rcases p37348_3 (m.d 0 2) (by simp) with h37452 | h37452
                · rcases p37348_3 (m.d 1 2) (by simp) with h37453 | h37453
                  · rcases p37348_3 (m.d 2 3) (by simp) with h37454 | h37454
                    · rcases p37348_3 (m.d 2 4) (by simp) with h37455 | h37455
                      · linarith only [h37316, h37455, hlam]
                      · rcases p37348_3 (m.d 2 5) (by simp) with h37457 | h37457
                        · linarith only [h37317, h37457, hlam]
                        · linarith only [h37318, h37457, hlam]
                    · linarith only [h37316, h37454, hlam]
                  · linarith only [h37310, h37453, hlam]
                · linarith only [h36831, h37452, hlam]
              · have p37348_0 := h37348c.1
                have p37348_1 := h37348c.2.1
                have p37348_2 := h37348c.2.2.1
                have p37348_3 := h37348c.2.2.2
                rcases p37348_3 (m.d 0 2) (by simp) with h37463 | h37463
                · rcases p37348_3 (m.d 1 2) (by simp) with h37464 | h37464
                  · rcases p37348_3 (m.d 2 3) (by simp) with h37465 | h37465
                    · rcases p37348_3 (m.d 2 4) (by simp) with h37466 | h37466
                      · linarith only [h37316, h37466, hlam]
                      · rcases p37348_3 (m.d 2 5) (by simp) with h37468 | h37468
                        · linarith only [h37317, h37468, hlam]
                        · rcases h4bigk with h37470c | h37470c | h37470c | h37470c | h37470c | h37470c | h37470c | h37470c | h37470c | h37470c | h37470c | h37470c | h37470c | h37470c | h37470c | h37470c | h37470c | h37470c | h37470c | h37470c | h37470c | h37470c | h37470c | h37470c | h37470c
                          · have p37470_0 := h37470c.1
                            have p37470_1 := h37470c.2.1
                            have p37470_2 := h37470c.2.2.1
                            have p37470_3 := h37470c.2.2.2
                            linarith only [hlam, p37470_0]
                          · have p37470_0 := h37470c.1
                            have p37470_1 := h37470c.2.1
                            have p37470_2 := h37470c.2.2.1
                            have p37470_3 := h37470c.2.2.2
                            linarith only [h36835, h37310, h37316, hc34, hc45, hlam, hphi, p37470_1]
                          · have p37470_0 := h37470c.1
                            have p37470_1 := h37470c.2.1
                            have p37470_2 := h37470c.2.2.1
                            have p37470_3 := h37470c.2.2.2
                            linarith only [h36835, h37316, hc34, hc45, hlam, hphi, p37470_1]
                          · have p37470_0 := h37470c.1
                            have p37470_1 := h37470c.2.1
                            have p37470_2 := h37470c.2.2.1
                            have p37470_3 := h37470c.2.2.2
                            linarith only [h36835, hc34, hc45, hlam, hphi, p37470_1]
                          · have p37470_0 := h37470c.1
                            have p37470_1 := h37470c.2.1
                            have p37470_2 := h37470c.2.2.1
                            have p37470_3 := h37470c.2.2.2
                            linarith only [h36835, hlam, p37470_0]
                          · have p37470_0 := h37470c.1
                            have p37470_1 := h37470c.2.1
                            have p37470_2 := h37470c.2.2.1
                            have p37470_3 := h37470c.2.2.2
                            linarith only [h36828, hlam, p37470_0]
                          · have p37470_0 := h37470c.1
                            have p37470_1 := h37470c.2.1
                            have p37470_2 := h37470c.2.2.1
                            have p37470_3 := h37470c.2.2.2
                            linarith only [hlam, p37470_0]
                          · have p37470_0 := h37470c.1
                            have p37470_1 := h37470c.2.1
                            have p37470_2 := h37470c.2.2.1
                            have p37470_3 := h37470c.2.2.2
                            linarith only [h37314, h37316, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p37322_1, p37470_1]
                          · have p37470_0 := h37470c.1
                            have p37470_1 := h37470c.2.1
                            have p37470_2 := h37470c.2.2.1
                            have p37470_3 := h37470c.2.2.2
                            linarith only [h33187, h37309, h37314, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p37322_1, p37470_1]
                          · have p37470_0 := h37470c.1
                            have p37470_1 := h37470c.2.1
                            have p37470_2 := h37470c.2.2.1
                            have p37470_3 := h37470c.2.2.2
                            linarith only [h37314, hlam, p37470_0]
                          · have p37470_0 := h37470c.1
                            have p37470_1 := h37470c.2.1
                            have p37470_2 := h37470c.2.2.1
                            have p37470_3 := h37470c.2.2.2
                            linarith only [h36831, hlam, p37470_0]
                          · have p37470_0 := h37470c.1
                            have p37470_1 := h37470c.2.1
                            have p37470_2 := h37470c.2.2.1
                            have p37470_3 := h37470c.2.2.2
                            linarith only [h37310, hlam, p37470_0]
                          · have p37470_0 := h37470c.1
                            have p37470_1 := h37470c.2.1
                            have p37470_2 := h37470c.2.2.1
                            have p37470_3 := h37470c.2.2.2
                            linarith only [hlam, p37470_0]
                          · have p37470_0 := h37470c.1
                            have p37470_1 := h37470c.2.1
                            have p37470_2 := h37470c.2.2.1
                            have p37470_3 := h37470c.2.2.2
                            linarith only [h36831, h36835, hc34, hc45, hlam, hphi, p37470_1]
                          · have p37470_0 := h37470c.1
                            have p37470_1 := h37470c.2.1
                            have p37470_2 := h37470c.2.2.1
                            have p37470_3 := h37470c.2.2.2
                            linarith only [h37318, hlam, p37470_0]
                          · have p37470_0 := h37470c.1
                            have p37470_1 := h37470c.2.1
                            have p37470_2 := h37470c.2.2.1
                            have p37470_3 := h37470c.2.2.2
                            linarith only [h36833, hlam, p37470_0]
                          · have p37470_0 := h37470c.1
                            have p37470_1 := h37470c.2.1
                            have p37470_2 := h37470c.2.2.1
                            have p37470_3 := h37470c.2.2.2
                            linarith only [h37312, hlam, p37470_0]
                          · have p37470_0 := h37470c.1
                            have p37470_1 := h37470c.2.1
                            have p37470_2 := h37470c.2.2.1
                            have p37470_3 := h37470c.2.2.2
                            linarith only [h37316, hlam, p37470_0]
                          · have p37470_0 := h37470c.1
                            have p37470_1 := h37470c.2.1
                            have p37470_2 := h37470c.2.2.1
                            have p37470_3 := h37470c.2.2.2
                            linarith only [hlam, p37470_0]
                          · have p37470_0 := h37470c.1
                            have p37470_1 := h37470c.2.1
                            have p37470_2 := h37470c.2.2.1
                            have p37470_3 := h37470c.2.2.2
                            linarith only [h37320, hlam, p37470_0]
                          · have p37470_0 := h37470c.1
                            have p37470_1 := h37470c.2.1
                            have p37470_2 := h37470c.2.2.1
                            have p37470_3 := h37470c.2.2.2
                            rcases p37470_3 (m.d 0 4) (by simp) with h37491 | h37491
                            · linarith only [h37491, hlam, p37470_0]
                            · rcases p37470_3 (m.d 1 4) (by simp) with h37493 | h37493
                              · linarith only [h37314, h37493, hlam]
                              · rcases p37470_3 (m.d 2 4) (by simp) with h37495 | h37495
                                · linarith only [h37318, h37495, hlam]
                                · rcases p37470_3 (m.d 3 4) (by simp) with h37497 | h37497
                                  · linarith only [h37320, h37497, hlam]
                                  · rcases p37470_3 (m.d 4 5) (by simp) with h37499 | h37499
                                    · rcases h5bigk with h37500c | h37500c | h37500c | h37500c | h37500c | h37500c | h37500c | h37500c | h37500c | h37500c | h37500c | h37500c | h37500c | h37500c | h37500c | h37500c | h37500c | h37500c | h37500c | h37500c | h37500c | h37500c | h37500c | h37500c | h37500c
                                      · have p37500_0 := h37500c.1
                                        have p37500_1 := h37500c.2.1
                                        have p37500_2 := h37500c.2.2.1
                                        have p37500_3 := h37500c.2.2.2
                                        linarith only [hlam, p37500_0]
                                      · have p37500_0 := h37500c.1
                                        have p37500_1 := h37500c.2.1
                                        have p37500_2 := h37500c.2.2.1
                                        have p37500_3 := h37500c.2.2.2
                                        linarith only [h33187, h36829, h37309, h37314, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p37500_1]
                                      · have p37500_0 := h37500c.1
                                        have p37500_1 := h37500c.2.1
                                        have p37500_2 := h37500c.2.2.1
                                        have p37500_3 := h37500c.2.2.2
                                        linarith only [h33187, h36829, h37309, h37317, h37320, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p37500_1]
                                      · have p37500_0 := h37500c.1
                                        have p37500_1 := h37500c.2.1
                                        have p37500_2 := h37500c.2.2.1
                                        have p37500_3 := h37500c.2.2.2
                                        linarith only [h33187, h36829, h37309, h37320, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p37500_1]
                                      · have p37500_0 := h37500c.1
                                        have p37500_1 := h37500c.2.1
                                        have p37500_2 := h37500c.2.2.1
                                        have p37500_3 := h37500c.2.2.2
                                        linarith only [h36835, hlam, p37500_0]
                                      · have p37500_0 := h37500c.1
                                        have p37500_1 := h37500c.2.1
                                        have p37500_2 := h37500c.2.2.1
                                        have p37500_3 := h37500c.2.2.2
                                        linarith only [h36829, hlam, p37500_0]
                                      · have p37500_0 := h37500c.1
                                        have p37500_1 := h37500c.2.1
                                        have p37500_2 := h37500c.2.2.1
                                        have p37500_3 := h37500c.2.2.2
                                        linarith only [hlam, p37500_0]
                                      · have p37500_0 := h37500c.1
                                        have p37500_1 := h37500c.2.1
                                        have p37500_2 := h37500c.2.2.1
                                        have p37500_3 := h37500c.2.2.2
                                        linarith only [h33187, h37309, h37317, h37320, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p37322_1, p37500_1]
                                      · have p37500_0 := h37500c.1
                                        have p37500_1 := h37500c.2.1
                                        have p37500_2 := h37500c.2.2.1
                                        have p37500_3 := h37500c.2.2.2
                                        linarith only [h33187, h37309, h37320, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p37322_1, p37500_1]
                                      · have p37500_0 := h37500c.1
                                        have p37500_1 := h37500c.2.1
                                        have p37500_2 := h37500c.2.2.1
                                        have p37500_3 := h37500c.2.2.2
                                        linarith only [h37314, hlam, p37500_0]
                                      · have p37500_0 := h37500c.1
                                        have p37500_1 := h37500c.2.1
                                        have p37500_2 := h37500c.2.2.1
                                        have p37500_3 := h37500c.2.2.2
                                        linarith only [h36832, hlam, p37500_1]
                                      · have p37500_0 := h37500c.1
                                        have p37500_1 := h37500c.2.1
                                        have p37500_2 := h37500c.2.2.1
                                        have p37500_3 := h37500c.2.2.2
                                        linarith only [h37311, hlam, p37500_1]
                                      · have p37500_0 := h37500c.1
                                        have p37500_1 := h37500c.2.1
                                        have p37500_2 := h37500c.2.2.1
                                        have p37500_3 := h37500c.2.2.2
                                        linarith only [hlam, p37500_0]
                                      · have p37500_0 := h37500c.1
                                        have p37500_1 := h37500c.2.1
                                        have p37500_2 := h37500c.2.2.1
                                        have p37500_3 := h37500c.2.2.2
                                        linarith only [h37320, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p37348_1, p37500_1]
                                      · have p37500_0 := h37500c.1
                                        have p37500_1 := h37500c.2.1
                                        have p37500_2 := h37500c.2.2.1
                                        have p37500_3 := h37500c.2.2.2
                                        linarith only [h37318, hlam, p37500_0]
                                      · have p37500_0 := h37500c.1
                                        have p37500_1 := h37500c.2.1
                                        have p37500_2 := h37500c.2.2.1
                                        have p37500_3 := h37500c.2.2.2
                                        linarith only [h36834, hlam, p37500_1]
                                      · have p37500_0 := h37500c.1
                                        have p37500_1 := h37500c.2.1
                                        have p37500_2 := h37500c.2.2.1
                                        have p37500_3 := h37500c.2.2.2
                                        linarith only [h37313, hlam, p37500_1]
                                      · have p37500_0 := h37500c.1
                                        have p37500_1 := h37500c.2.1
                                        have p37500_2 := h37500c.2.2.1
                                        have p37500_3 := h37500c.2.2.2
                                        linarith only [h37317, hlam, p37500_0]
                                      · have p37500_0 := h37500c.1
                                        have p37500_1 := h37500c.2.1
                                        have p37500_2 := h37500c.2.2.1
                                        have p37500_3 := h37500c.2.2.2
                                        linarith only [hlam, p37500_0]
                                      · have p37500_0 := h37500c.1
                                        have p37500_1 := h37500c.2.1
                                        have p37500_2 := h37500c.2.2.1
                                        have p37500_3 := h37500c.2.2.2
                                        linarith only [h37320, hlam, p37500_0]
                                      · have p37500_0 := h37500c.1
                                        have p37500_1 := h37500c.2.1
                                        have p37500_2 := h37500c.2.2.1
                                        have p37500_3 := h37500c.2.2.2
                                        linarith only [h36834, h37320, hc34, hc45, hlam, hphi, p37500_1]
                                      · have p37500_0 := h37500c.1
                                        have p37500_1 := h37500c.2.1
                                        have p37500_2 := h37500c.2.2.1
                                        have p37500_3 := h37500c.2.2.2
                                        linarith only [h37313, h37320, hc34, hc45, hlam, hphi, p37500_1]
                                      · have p37500_0 := h37500c.1
                                        have p37500_1 := h37500c.2.1
                                        have p37500_2 := h37500c.2.2.1
                                        have p37500_3 := h37500c.2.2.2
                                        linarith only [h37317, h37320, hc34, hc45, hlam, hphi, p37500_1]
                                      · have p37500_0 := h37500c.1
                                        have p37500_1 := h37500c.2.1
                                        have p37500_2 := h37500c.2.2.1
                                        have p37500_3 := h37500c.2.2.2
                                        linarith only [h37320, hc34, hc45, hlam, hphi, p37500_1]
                                      · have p37500_0 := h37500c.1
                                        have p37500_1 := h37500c.2.1
                                        have p37500_2 := h37500c.2.2.1
                                        have p37500_3 := h37500c.2.2.2
                                        linarith only [hlam, p37500_0]
                                    · linarith only [h37499, hlam, p37470_0]
                          · have p37470_0 := h37470c.1
                            have p37470_1 := h37470c.2.1
                            have p37470_2 := h37470c.2.2.1
                            have p37470_3 := h37470c.2.2.2
                            rcases p37470_3 (m.d 0 4) (by simp) with h37527 | h37527
                            · linarith only [h36835, h37527, hlam]
                            · linarith only [h36828, h37527, hlam]
                          · have p37470_0 := h37470c.1
                            have p37470_1 := h37470c.2.1
                            have p37470_2 := h37470c.2.2.1
                            have p37470_3 := h37470c.2.2.2
                            rcases p37470_3 (m.d 0 4) (by simp) with h37530 | h37530
                            · linarith only [h36835, h37530, hlam]
                            · linarith only [h36831, h37530, hlam]
                          · have p37470_0 := h37470c.1
                            have p37470_1 := h37470c.2.1
                            have p37470_2 := h37470c.2.2.1
                            have p37470_3 := h37470c.2.2.2
                            rcases p37470_3 (m.d 0 4) (by simp) with h37533 | h37533
                            · linarith only [h36835, h37533, hlam]
                            · linarith only [h36833, h37533, hlam]
                          · have p37470_0 := h37470c.1
                            have p37470_1 := h37470c.2.1
                            have p37470_2 := h37470c.2.2.1
                            have p37470_3 := h37470c.2.2.2
                            linarith only [hlam, p37470_0]
                    · linarith only [h37317, h37465, hlam]
                  · linarith only [h37311, h37464, hlam]
                · linarith only [h36832, h37463, hlam]
              · have p37348_0 := h37348c.1
                have p37348_1 := h37348c.2.1
                have p37348_2 := h37348c.2.2.1
                have p37348_3 := h37348c.2.2.2
                linarith only [h36831, hlam, p37348_0]
              · have p37348_0 := h37348c.1
                have p37348_1 := h37348c.2.1
                have p37348_2 := h37348c.2.2.1
                have p37348_3 := h37348c.2.2.2
                linarith only [h37310, hlam, p37348_0]
              · have p37348_0 := h37348c.1
                have p37348_1 := h37348c.2.1
                have p37348_2 := h37348c.2.2.1
                have p37348_3 := h37348c.2.2.2
                linarith only [h37316, hlam, p37348_0]
              · have p37348_0 := h37348c.1
                have p37348_1 := h37348c.2.1
                have p37348_2 := h37348c.2.2.1
                have p37348_3 := h37348c.2.2.2
                linarith only [hlam, p37348_0]
              · have p37348_0 := h37348c.1
                have p37348_1 := h37348c.2.1
                have p37348_2 := h37348c.2.2.1
                have p37348_3 := h37348c.2.2.2
                linarith only [h37318, hlam, p37348_0]
              · have p37348_0 := h37348c.1
                have p37348_1 := h37348c.2.1
                have p37348_2 := h37348c.2.2.1
                have p37348_3 := h37348c.2.2.2
                linarith only [h36832, hlam, p37348_0]
              · have p37348_0 := h37348c.1
                have p37348_1 := h37348c.2.1
                have p37348_2 := h37348c.2.2.1
                have p37348_3 := h37348c.2.2.2
                linarith only [h37311, hlam, p37348_0]
              · have p37348_0 := h37348c.1
                have p37348_1 := h37348c.2.1
                have p37348_2 := h37348c.2.2.1
                have p37348_3 := h37348c.2.2.2
                linarith only [h37317, hlam, p37348_0]
              · have p37348_0 := h37348c.1
                have p37348_1 := h37348c.2.1
                have p37348_2 := h37348c.2.2.1
                have p37348_3 := h37348c.2.2.2
                linarith only [h33187, h37309, h37311, h37316, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p37322_1, p37348_1]
              · have p37348_0 := h37348c.1
                have p37348_1 := h37348c.2.1
                have p37348_2 := h37348c.2.2.1
                have p37348_3 := h37348c.2.2.2
                linarith only [hlam, p37348_0]
            · rcases h2bigk with h37550c | h37550c | h37550c | h37550c | h37550c | h37550c | h37550c | h37550c | h37550c | h37550c | h37550c | h37550c | h37550c | h37550c | h37550c | h37550c | h37550c | h37550c | h37550c | h37550c | h37550c | h37550c | h37550c | h37550c | h37550c
              · have p37550_0 := h37550c.1
                have p37550_1 := h37550c.2.1
                have p37550_2 := h37550c.2.2.1
                have p37550_3 := h37550c.2.2.2
                linarith only [hlam, p37550_0]
              · have p37550_0 := h37550c.1
                have p37550_1 := h37550c.2.1
                have p37550_2 := h37550c.2.2.1
                have p37550_3 := h37550c.2.2.2
                linarith only [h0, hlam, p37550_0]
              · have p37550_0 := h37550c.1
                have p37550_1 := h37550c.2.1
                have p37550_2 := h37550c.2.2.1
                have p37550_3 := h37550c.2.2.2
                rcases p37550_3 (m.d 0 2) (by simp) with h37553 | h37553
                · rcases p37550_3 (m.d 1 2) (by simp) with h37554 | h37554
                  · rcases p37550_3 (m.d 2 3) (by simp) with h37555 | h37555
                    · linarith only [h37555, hlam, p37550_0]
                    · rcases p37550_3 (m.d 2 4) (by simp) with h37557 | h37557
                      · linarith only [h36831, h37557, hlam]
                      · rcases p37550_3 (m.d 2 5) (by simp) with h37559 | h37559
                        · linarith only [h36832, h37559, hlam]
                        · rcases h4bigk with h37561c | h37561c | h37561c | h37561c | h37561c | h37561c | h37561c | h37561c | h37561c | h37561c | h37561c | h37561c | h37561c | h37561c | h37561c | h37561c | h37561c | h37561c | h37561c | h37561c | h37561c | h37561c | h37561c | h37561c | h37561c
                          · have p37561_0 := h37561c.1
                            have p37561_1 := h37561c.2.1
                            have p37561_2 := h37561c.2.2.1
                            have p37561_3 := h37561c.2.2.2
                            linarith only [hlam, p37561_0]
                          · have p37561_0 := h37561c.1
                            have p37561_1 := h37561c.2.1
                            have p37561_2 := h37561c.2.2.1
                            have p37561_3 := h37561c.2.2.2
                            linarith only [h36835, h37310, h37316, hc34, hc45, hlam, hphi, p37561_1]
                          · have p37561_0 := h37561c.1
                            have p37561_1 := h37561c.2.1
                            have p37561_2 := h37561c.2.2.1
                            have p37561_3 := h37561c.2.2.2
                            linarith only [h36835, h37316, hc34, hc45, hlam, hphi, p37561_1]
                          · have p37561_0 := h37561c.1
                            have p37561_1 := h37561c.2.1
                            have p37561_2 := h37561c.2.2.1
                            have p37561_3 := h37561c.2.2.2
                            linarith only [h36835, hc34, hc45, hlam, hphi, p37561_1]
                          · have p37561_0 := h37561c.1
                            have p37561_1 := h37561c.2.1
                            have p37561_2 := h37561c.2.2.1
                            have p37561_3 := h37561c.2.2.2
                            linarith only [h36835, hlam, p37561_0]
                          · have p37561_0 := h37561c.1
                            have p37561_1 := h37561c.2.1
                            have p37561_2 := h37561c.2.2.1
                            have p37561_3 := h37561c.2.2.2
                            linarith only [h36828, hlam, p37561_0]
                          · have p37561_0 := h37561c.1
                            have p37561_1 := h37561c.2.1
                            have p37561_2 := h37561c.2.2.1
                            have p37561_3 := h37561c.2.2.2
                            linarith only [hlam, p37561_0]
                          · have p37561_0 := h37561c.1
                            have p37561_1 := h37561c.2.1
                            have p37561_2 := h37561c.2.2.1
                            have p37561_3 := h37561c.2.2.2
                            linarith only [h33187, h36828, h37309, h37316, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p37561_1]
                          · have p37561_0 := h37561c.1
                            have p37561_1 := h37561c.2.1
                            have p37561_2 := h37561c.2.2.1
                            have p37561_3 := h37561c.2.2.2
                            linarith only [h33187, h36828, h37309, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p37561_1]
                          · have p37561_0 := h37561c.1
                            have p37561_1 := h37561c.2.1
                            have p37561_2 := h37561c.2.2.1
                            have p37561_3 := h37561c.2.2.2
                            linarith only [h37314, hlam, p37561_0]
                          · have p37561_0 := h37561c.1
                            have p37561_1 := h37561c.2.1
                            have p37561_2 := h37561c.2.2.1
                            have p37561_3 := h37561c.2.2.2
                            linarith only [h36831, hlam, p37561_0]
                          · have p37561_0 := h37561c.1
                            have p37561_1 := h37561c.2.1
                            have p37561_2 := h37561c.2.2.1
                            have p37561_3 := h37561c.2.2.2
                            linarith only [h37310, hlam, p37561_0]
                          · have p37561_0 := h37561c.1
                            have p37561_1 := h37561c.2.1
                            have p37561_2 := h37561c.2.2.1
                            have p37561_3 := h37561c.2.2.2
                            linarith only [hlam, p37561_0]
                          · have p37561_0 := h37561c.1
                            have p37561_1 := h37561c.2.1
                            have p37561_2 := h37561c.2.2.1
                            have p37561_3 := h37561c.2.2.2
                            linarith only [h36831, h36835, hc34, hc45, hlam, hphi, p37561_1]
                          · have p37561_0 := h37561c.1
                            have p37561_1 := h37561c.2.1
                            have p37561_2 := h37561c.2.2.1
                            have p37561_3 := h37561c.2.2.2
                            linarith only [h37318, hlam, p37561_0]
                          · have p37561_0 := h37561c.1
                            have p37561_1 := h37561c.2.1
                            have p37561_2 := h37561c.2.2.1
                            have p37561_3 := h37561c.2.2.2
                            linarith only [h36833, hlam, p37561_0]
                          · have p37561_0 := h37561c.1
                            have p37561_1 := h37561c.2.1
                            have p37561_2 := h37561c.2.2.1
                            have p37561_3 := h37561c.2.2.2
                            linarith only [h37312, hlam, p37561_0]
                          · have p37561_0 := h37561c.1
                            have p37561_1 := h37561c.2.1
                            have p37561_2 := h37561c.2.2.1
                            have p37561_3 := h37561c.2.2.2
                            linarith only [h37316, hlam, p37561_0]
                          · have p37561_0 := h37561c.1
                            have p37561_1 := h37561c.2.1
                            have p37561_2 := h37561c.2.2.1
                            have p37561_3 := h37561c.2.2.2
                            linarith only [hlam, p37561_0]
                          · have p37561_0 := h37561c.1
                            have p37561_1 := h37561c.2.1
                            have p37561_2 := h37561c.2.2.1
                            have p37561_3 := h37561c.2.2.2
                            linarith only [h37320, hlam, p37561_0]
                          · have p37561_0 := h37561c.1
                            have p37561_1 := h37561c.2.1
                            have p37561_2 := h37561c.2.2.1
                            have p37561_3 := h37561c.2.2.2
                            rcases p37561_3 (m.d 0 4) (by simp) with h37582 | h37582
                            · linarith only [h37582, hlam, p37561_0]
                            · rcases p37561_3 (m.d 1 4) (by simp) with h37584 | h37584
                              · linarith only [h37314, h37584, hlam]
                              · rcases p37561_3 (m.d 2 4) (by simp) with h37586 | h37586
                                · linarith only [h37318, h37586, hlam]
                                · rcases p37561_3 (m.d 3 4) (by simp) with h37588 | h37588
                                  · linarith only [h37320, h37588, hlam]
                                  · rcases p37561_3 (m.d 4 5) (by simp) with h37590 | h37590
                                    · rcases h5bigk with h37591c | h37591c | h37591c | h37591c | h37591c | h37591c | h37591c | h37591c | h37591c | h37591c | h37591c | h37591c | h37591c | h37591c | h37591c | h37591c | h37591c | h37591c | h37591c | h37591c | h37591c | h37591c | h37591c | h37591c | h37591c
                                      · have p37591_0 := h37591c.1
                                        have p37591_1 := h37591c.2.1
                                        have p37591_2 := h37591c.2.2.1
                                        have p37591_3 := h37591c.2.2.2
                                        linarith only [hlam, p37591_0]
                                      · have p37591_0 := h37591c.1
                                        have p37591_1 := h37591c.2.1
                                        have p37591_2 := h37591c.2.2.1
                                        have p37591_3 := h37591c.2.2.2
                                        linarith only [h33187, h36829, h37309, h37314, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p37591_1]
                                      · have p37591_0 := h37591c.1
                                        have p37591_1 := h37591c.2.1
                                        have p37591_2 := h37591c.2.2.1
                                        have p37591_3 := h37591c.2.2.2
                                        linarith only [h33187, h36829, h37309, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p37591_1]
                                      · have p37591_0 := h37591c.1
                                        have p37591_1 := h37591c.2.1
                                        have p37591_2 := h37591c.2.2.1
                                        have p37591_3 := h37591c.2.2.2
                                        linarith only [h33187, h36829, h37309, h37320, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p37591_1]
                                      · have p37591_0 := h37591c.1
                                        have p37591_1 := h37591c.2.1
                                        have p37591_2 := h37591c.2.2.1
                                        have p37591_3 := h37591c.2.2.2
                                        linarith only [h36835, hlam, p37591_0]
                                      · have p37591_0 := h37591c.1
                                        have p37591_1 := h37591c.2.1
                                        have p37591_2 := h37591c.2.2.1
                                        have p37591_3 := h37591c.2.2.2
                                        linarith only [h36829, hlam, p37591_0]
                                      · have p37591_0 := h37591c.1
                                        have p37591_1 := h37591c.2.1
                                        have p37591_2 := h37591c.2.2.1
                                        have p37591_3 := h37591c.2.2.2
                                        linarith only [hlam, p37591_0]
                                      · have p37591_0 := h37591c.1
                                        have p37591_1 := h37591c.2.1
                                        have p37591_2 := h37591c.2.2.1
                                        have p37591_3 := h37591c.2.2.2
                                        linarith only [h33187, h37309, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p37322_1, p37591_1]
                                      · have p37591_0 := h37591c.1
                                        have p37591_1 := h37591c.2.1
                                        have p37591_2 := h37591c.2.2.1
                                        have p37591_3 := h37591c.2.2.2
                                        linarith only [h33187, h37309, h37320, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p37322_1, p37591_1]
                                      · have p37591_0 := h37591c.1
                                        have p37591_1 := h37591c.2.1
                                        have p37591_2 := h37591c.2.2.1
                                        have p37591_3 := h37591c.2.2.2
                                        linarith only [h37314, hlam, p37591_0]
                                      · have p37591_0 := h37591c.1
                                        have p37591_1 := h37591c.2.1
                                        have p37591_2 := h37591c.2.2.1
                                        have p37591_3 := h37591c.2.2.2
                                        linarith only [h36832, hlam, p37591_1]
                                      · have p37591_0 := h37591c.1
                                        have p37591_1 := h37591c.2.1
                                        have p37591_2 := h37591c.2.2.1
                                        have p37591_3 := h37591c.2.2.2
                                        linarith only [h37311, hlam, p37591_1]
                                      · have p37591_0 := h37591c.1
                                        have p37591_1 := h37591c.2.1
                                        have p37591_2 := h37591c.2.2.1
                                        have p37591_3 := h37591c.2.2.2
                                        linarith only [hlam, p37591_0]
                                      · have p37591_0 := h37591c.1
                                        have p37591_1 := h37591c.2.1
                                        have p37591_2 := h37591c.2.2.1
                                        have p37591_3 := h37591c.2.2.2
                                        linarith only [h0, h36832, h37320, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p37591_1]
                                      · have p37591_0 := h37591c.1
                                        have p37591_1 := h37591c.2.1
                                        have p37591_2 := h37591c.2.2.1
                                        have p37591_3 := h37591c.2.2.2
                                        linarith only [h37318, hlam, p37591_0]
                                      · have p37591_0 := h37591c.1
                                        have p37591_1 := h37591c.2.1
                                        have p37591_2 := h37591c.2.2.1
                                        have p37591_3 := h37591c.2.2.2
                                        linarith only [h36834, hlam, p37591_1]
                                      · have p37591_0 := h37591c.1
                                        have p37591_1 := h37591c.2.1
                                        have p37591_2 := h37591c.2.2.1
                                        have p37591_3 := h37591c.2.2.2
                                        linarith only [h37313, hlam, p37591_1]
                                      · have p37591_0 := h37591c.1
                                        have p37591_1 := h37591c.2.1
                                        have p37591_2 := h37591c.2.2.1
                                        have p37591_3 := h37591c.2.2.2
                                        linarith only [h37317, hlam, p37591_0]
                                      · have p37591_0 := h37591c.1
                                        have p37591_1 := h37591c.2.1
                                        have p37591_2 := h37591c.2.2.1
                                        have p37591_3 := h37591c.2.2.2
                                        linarith only [hlam, p37591_0]
                                      · have p37591_0 := h37591c.1
                                        have p37591_1 := h37591c.2.1
                                        have p37591_2 := h37591c.2.2.1
                                        have p37591_3 := h37591c.2.2.2
                                        linarith only [h37320, hlam, p37591_0]
                                      · have p37591_0 := h37591c.1
                                        have p37591_1 := h37591c.2.1
                                        have p37591_2 := h37591c.2.2.1
                                        have p37591_3 := h37591c.2.2.2
                                        linarith only [h36834, h37320, hc34, hc45, hlam, hphi, p37591_1]
                                      · have p37591_0 := h37591c.1
                                        have p37591_1 := h37591c.2.1
                                        have p37591_2 := h37591c.2.2.1
                                        have p37591_3 := h37591c.2.2.2
                                        linarith only [h37313, h37320, hc34, hc45, hlam, hphi, p37591_1]
                                      · have p37591_0 := h37591c.1
                                        have p37591_1 := h37591c.2.1
                                        have p37591_2 := h37591c.2.2.1
                                        have p37591_3 := h37591c.2.2.2
                                        linarith only [h37317, h37320, hc34, hc45, hlam, hphi, p37591_1]
                                      · have p37591_0 := h37591c.1
                                        have p37591_1 := h37591c.2.1
                                        have p37591_2 := h37591c.2.2.1
                                        have p37591_3 := h37591c.2.2.2
                                        linarith only [h37320, hc34, hc45, hlam, hphi, p37591_1]
                                      · have p37591_0 := h37591c.1
                                        have p37591_1 := h37591c.2.1
                                        have p37591_2 := h37591c.2.2.1
                                        have p37591_3 := h37591c.2.2.2
                                        linarith only [hlam, p37591_0]
                                    · linarith only [h37590, hlam, p37561_0]
                          · have p37561_0 := h37561c.1
                            have p37561_1 := h37561c.2.1
                            have p37561_2 := h37561c.2.2.1
                            have p37561_3 := h37561c.2.2.2
                            rcases p37561_3 (m.d 0 4) (by simp) with h37618 | h37618
                            · linarith only [h36835, h37618, hlam]
                            · linarith only [h36828, h37618, hlam]
                          · have p37561_0 := h37561c.1
                            have p37561_1 := h37561c.2.1
                            have p37561_2 := h37561c.2.2.1
                            have p37561_3 := h37561c.2.2.2
                            rcases p37561_3 (m.d 0 4) (by simp) with h37621 | h37621
                            · linarith only [h36835, h37621, hlam]
                            · linarith only [h36831, h37621, hlam]
                          · have p37561_0 := h37561c.1
                            have p37561_1 := h37561c.2.1
                            have p37561_2 := h37561c.2.2.1
                            have p37561_3 := h37561c.2.2.2
                            rcases p37561_3 (m.d 0 4) (by simp) with h37624 | h37624
                            · linarith only [h36835, h37624, hlam]
                            · linarith only [h36833, h37624, hlam]
                          · have p37561_0 := h37561c.1
                            have p37561_1 := h37561c.2.1
                            have p37561_2 := h37561c.2.2.1
                            have p37561_3 := h37561c.2.2.2
                            linarith only [hlam, p37561_0]
                  · linarith only [h37309, h37554, hlam]
                · linarith only [h37553, hlam, p37550_0]
              · have p37550_0 := h37550c.1
                have p37550_1 := h37550c.2.1
                have p37550_2 := h37550c.2.2.1
                have p37550_3 := h37550c.2.2.2
                rcases p37550_3 (m.d 0 2) (by simp) with h37630 | h37630
                · rcases p37550_3 (m.d 1 2) (by simp) with h37631 | h37631
                  · rcases p37550_3 (m.d 2 3) (by simp) with h37632 | h37632
                    · linarith only [h36830, h37632, hlam]
                    · linarith only [h37316, h37632, hlam]
                  · linarith only [h37310, h37631, hlam]
                · linarith only [h37630, hlam, p37550_0]
              · have p37550_0 := h37550c.1
                have p37550_1 := h37550c.2.1
                have p37550_2 := h37550c.2.2.1
                have p37550_3 := h37550c.2.2.2
                rcases p37550_3 (m.d 0 2) (by simp) with h37637 | h37637
                · rcases p37550_3 (m.d 1 2) (by simp) with h37638 | h37638
                  · rcases p37550_3 (m.d 2 3) (by simp) with h37639 | h37639
                    · linarith only [h36830, h37639, hlam]
                    · linarith only [h37317, h37639, hlam]
                  · linarith only [h37311, h37638, hlam]
                · linarith only [h37637, hlam, p37550_0]
              · have p37550_0 := h37550c.1
                have p37550_1 := h37550c.2.1
                have p37550_2 := h37550c.2.2.1
                have p37550_3 := h37550c.2.2.2
                linarith only [h33187, h36830, h37310, h37314, h37316, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p37322_1, p37550_1]
              · have p37550_0 := h37550c.1
                have p37550_1 := h37550c.2.1
                have p37550_2 := h37550c.2.2.1
                have p37550_3 := h37550c.2.2.2
                linarith only [hlam, p37550_0]
              · have p37550_0 := h37550c.1
                have p37550_1 := h37550c.2.1
                have p37550_2 := h37550c.2.2.1
                have p37550_3 := h37550c.2.2.2
                rcases p37550_3 (m.d 0 2) (by simp) with h37646 | h37646
                · linarith only [h0, h37646, hlam]
                · linarith only [h36830, h37646, hlam]
              · have p37550_0 := h37550c.1
                have p37550_1 := h37550c.2.1
                have p37550_2 := h37550c.2.2.1
                have p37550_3 := h37550c.2.2.2
                linarith only [h0, h37310, h37314, hlam, p37322_1, p37550_2]
              · have p37550_0 := h37550c.1
                have p37550_1 := h37550c.2.1
                have p37550_2 := h37550c.2.2.1
                have p37550_3 := h37550c.2.2.2
                linarith only [h33187, h37309, h37311, hlam, p37322_1, p37550_2]
              · have p37550_0 := h37550c.1
                have p37550_1 := h37550c.2.1
                have p37550_2 := h37550c.2.2.1
                have p37550_3 := h37550c.2.2.2
                linarith only [h36830, hlam, p37550_0]
              · have p37550_0 := h37550c.1
                have p37550_1 := h37550c.2.1
                have p37550_2 := h37550c.2.2.1
                have p37550_3 := h37550c.2.2.2
                linarith only [h37309, hlam, p37550_0]
              · have p37550_0 := h37550c.1
                have p37550_1 := h37550c.2.1
                have p37550_2 := h37550c.2.2.1
                have p37550_3 := h37550c.2.2.2
                linarith only [hlam, p37550_0]
              · have p37550_0 := h37550c.1
                have p37550_1 := h37550c.2.1
                have p37550_2 := h37550c.2.2.1
                have p37550_3 := h37550c.2.2.2
                rcases p37550_3 (m.d 0 2) (by simp) with h37654 | h37654
                · rcases p37550_3 (m.d 1 2) (by simp) with h37655 | h37655
                  · rcases p37550_3 (m.d 2 3) (by simp) with h37656 | h37656
                    · rcases p37550_3 (m.d 2 4) (by simp) with h37657 | h37657
                      · linarith only [h37316, h37657, hlam]
                      · rcases p37550_3 (m.d 2 5) (by simp) with h37659 | h37659
                        · linarith only [h37317, h37659, hlam]
                        · linarith only [h37318, h37659, hlam]
                    · linarith only [h37316, h37656, hlam]
                  · linarith only [h37310, h37655, hlam]
                · linarith only [h36831, h37654, hlam]
              · have p37550_0 := h37550c.1
                have p37550_1 := h37550c.2.1
                have p37550_2 := h37550c.2.2.1
                have p37550_3 := h37550c.2.2.2
                rcases p37550_3 (m.d 0 2) (by simp) with h37665 | h37665
                · rcases p37550_3 (m.d 1 2) (by simp) with h37666 | h37666
                  · rcases p37550_3 (m.d 2 3) (by simp) with h37667 | h37667
                    · rcases p37550_3 (m.d 2 4) (by simp) with h37668 | h37668
                      · linarith only [h37316, h37668, hlam]
                      · rcases p37550_3 (m.d 2 5) (by simp) with h37670 | h37670
                        · linarith only [h37317, h37670, hlam]
                        · rcases h4bigk with h37672c | h37672c | h37672c | h37672c | h37672c | h37672c | h37672c | h37672c | h37672c | h37672c | h37672c | h37672c | h37672c | h37672c | h37672c | h37672c | h37672c | h37672c | h37672c | h37672c | h37672c | h37672c | h37672c | h37672c | h37672c
                          · have p37672_0 := h37672c.1
                            have p37672_1 := h37672c.2.1
                            have p37672_2 := h37672c.2.2.1
                            have p37672_3 := h37672c.2.2.2
                            linarith only [hlam, p37672_0]
                          · have p37672_0 := h37672c.1
                            have p37672_1 := h37672c.2.1
                            have p37672_2 := h37672c.2.2.1
                            have p37672_3 := h37672c.2.2.2
                            linarith only [h36835, h37310, h37316, hc34, hc45, hlam, hphi, p37672_1]
                          · have p37672_0 := h37672c.1
                            have p37672_1 := h37672c.2.1
                            have p37672_2 := h37672c.2.2.1
                            have p37672_3 := h37672c.2.2.2
                            linarith only [h36835, h37316, hc34, hc45, hlam, hphi, p37672_1]
                          · have p37672_0 := h37672c.1
                            have p37672_1 := h37672c.2.1
                            have p37672_2 := h37672c.2.2.1
                            have p37672_3 := h37672c.2.2.2
                            linarith only [h36835, hc34, hc45, hlam, hphi, p37672_1]
                          · have p37672_0 := h37672c.1
                            have p37672_1 := h37672c.2.1
                            have p37672_2 := h37672c.2.2.1
                            have p37672_3 := h37672c.2.2.2
                            linarith only [h36835, hlam, p37672_0]
                          · have p37672_0 := h37672c.1
                            have p37672_1 := h37672c.2.1
                            have p37672_2 := h37672c.2.2.1
                            have p37672_3 := h37672c.2.2.2
                            linarith only [h36828, hlam, p37672_0]
                          · have p37672_0 := h37672c.1
                            have p37672_1 := h37672c.2.1
                            have p37672_2 := h37672c.2.2.1
                            have p37672_3 := h37672c.2.2.2
                            linarith only [hlam, p37672_0]
                          · have p37672_0 := h37672c.1
                            have p37672_1 := h37672c.2.1
                            have p37672_2 := h37672c.2.2.1
                            have p37672_3 := h37672c.2.2.2
                            linarith only [h37314, h37316, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p37322_1, p37672_1]
                          · have p37672_0 := h37672c.1
                            have p37672_1 := h37672c.2.1
                            have p37672_2 := h37672c.2.2.1
                            have p37672_3 := h37672c.2.2.2
                            linarith only [h33187, h37309, h37314, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p37322_1, p37672_1]
                          · have p37672_0 := h37672c.1
                            have p37672_1 := h37672c.2.1
                            have p37672_2 := h37672c.2.2.1
                            have p37672_3 := h37672c.2.2.2
                            linarith only [h37314, hlam, p37672_0]
                          · have p37672_0 := h37672c.1
                            have p37672_1 := h37672c.2.1
                            have p37672_2 := h37672c.2.2.1
                            have p37672_3 := h37672c.2.2.2
                            linarith only [h36831, hlam, p37672_0]
                          · have p37672_0 := h37672c.1
                            have p37672_1 := h37672c.2.1
                            have p37672_2 := h37672c.2.2.1
                            have p37672_3 := h37672c.2.2.2
                            linarith only [h37310, hlam, p37672_0]
                          · have p37672_0 := h37672c.1
                            have p37672_1 := h37672c.2.1
                            have p37672_2 := h37672c.2.2.1
                            have p37672_3 := h37672c.2.2.2
                            linarith only [hlam, p37672_0]
                          · have p37672_0 := h37672c.1
                            have p37672_1 := h37672c.2.1
                            have p37672_2 := h37672c.2.2.1
                            have p37672_3 := h37672c.2.2.2
                            linarith only [h36831, h36835, hc34, hc45, hlam, hphi, p37672_1]
                          · have p37672_0 := h37672c.1
                            have p37672_1 := h37672c.2.1
                            have p37672_2 := h37672c.2.2.1
                            have p37672_3 := h37672c.2.2.2
                            linarith only [h37318, hlam, p37672_0]
                          · have p37672_0 := h37672c.1
                            have p37672_1 := h37672c.2.1
                            have p37672_2 := h37672c.2.2.1
                            have p37672_3 := h37672c.2.2.2
                            linarith only [h36833, hlam, p37672_0]
                          · have p37672_0 := h37672c.1
                            have p37672_1 := h37672c.2.1
                            have p37672_2 := h37672c.2.2.1
                            have p37672_3 := h37672c.2.2.2
                            linarith only [h37312, hlam, p37672_0]
                          · have p37672_0 := h37672c.1
                            have p37672_1 := h37672c.2.1
                            have p37672_2 := h37672c.2.2.1
                            have p37672_3 := h37672c.2.2.2
                            linarith only [h37316, hlam, p37672_0]
                          · have p37672_0 := h37672c.1
                            have p37672_1 := h37672c.2.1
                            have p37672_2 := h37672c.2.2.1
                            have p37672_3 := h37672c.2.2.2
                            linarith only [hlam, p37672_0]
                          · have p37672_0 := h37672c.1
                            have p37672_1 := h37672c.2.1
                            have p37672_2 := h37672c.2.2.1
                            have p37672_3 := h37672c.2.2.2
                            linarith only [h37320, hlam, p37672_0]
                          · have p37672_0 := h37672c.1
                            have p37672_1 := h37672c.2.1
                            have p37672_2 := h37672c.2.2.1
                            have p37672_3 := h37672c.2.2.2
                            rcases p37672_3 (m.d 0 4) (by simp) with h37693 | h37693
                            · linarith only [h37693, hlam, p37672_0]
                            · rcases p37672_3 (m.d 1 4) (by simp) with h37695 | h37695
                              · linarith only [h37314, h37695, hlam]
                              · rcases p37672_3 (m.d 2 4) (by simp) with h37697 | h37697
                                · linarith only [h37318, h37697, hlam]
                                · rcases p37672_3 (m.d 3 4) (by simp) with h37699 | h37699
                                  · linarith only [h37320, h37699, hlam]
                                  · rcases p37672_3 (m.d 4 5) (by simp) with h37701 | h37701
                                    · rcases h5bigk with h37702c | h37702c | h37702c | h37702c | h37702c | h37702c | h37702c | h37702c | h37702c | h37702c | h37702c | h37702c | h37702c | h37702c | h37702c | h37702c | h37702c | h37702c | h37702c | h37702c | h37702c | h37702c | h37702c | h37702c | h37702c
                                      · have p37702_0 := h37702c.1
                                        have p37702_1 := h37702c.2.1
                                        have p37702_2 := h37702c.2.2.1
                                        have p37702_3 := h37702c.2.2.2
                                        linarith only [hlam, p37702_0]
                                      · have p37702_0 := h37702c.1
                                        have p37702_1 := h37702c.2.1
                                        have p37702_2 := h37702c.2.2.1
                                        have p37702_3 := h37702c.2.2.2
                                        linarith only [h33187, h36829, h37309, h37314, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p37702_1]
                                      · have p37702_0 := h37702c.1
                                        have p37702_1 := h37702c.2.1
                                        have p37702_2 := h37702c.2.2.1
                                        have p37702_3 := h37702c.2.2.2
                                        linarith only [h33187, h36829, h37309, h37317, h37320, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p37702_1]
                                      · have p37702_0 := h37702c.1
                                        have p37702_1 := h37702c.2.1
                                        have p37702_2 := h37702c.2.2.1
                                        have p37702_3 := h37702c.2.2.2
                                        linarith only [h33187, h36829, h37309, h37320, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p37702_1]
                                      · have p37702_0 := h37702c.1
                                        have p37702_1 := h37702c.2.1
                                        have p37702_2 := h37702c.2.2.1
                                        have p37702_3 := h37702c.2.2.2
                                        linarith only [h36835, hlam, p37702_0]
                                      · have p37702_0 := h37702c.1
                                        have p37702_1 := h37702c.2.1
                                        have p37702_2 := h37702c.2.2.1
                                        have p37702_3 := h37702c.2.2.2
                                        linarith only [h36829, hlam, p37702_0]
                                      · have p37702_0 := h37702c.1
                                        have p37702_1 := h37702c.2.1
                                        have p37702_2 := h37702c.2.2.1
                                        have p37702_3 := h37702c.2.2.2
                                        linarith only [hlam, p37702_0]
                                      · have p37702_0 := h37702c.1
                                        have p37702_1 := h37702c.2.1
                                        have p37702_2 := h37702c.2.2.1
                                        have p37702_3 := h37702c.2.2.2
                                        linarith only [h33187, h37309, h37317, h37320, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p37322_1, p37702_1]
                                      · have p37702_0 := h37702c.1
                                        have p37702_1 := h37702c.2.1
                                        have p37702_2 := h37702c.2.2.1
                                        have p37702_3 := h37702c.2.2.2
                                        linarith only [h33187, h37309, h37320, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p37322_1, p37702_1]
                                      · have p37702_0 := h37702c.1
                                        have p37702_1 := h37702c.2.1
                                        have p37702_2 := h37702c.2.2.1
                                        have p37702_3 := h37702c.2.2.2
                                        linarith only [h37314, hlam, p37702_0]
                                      · have p37702_0 := h37702c.1
                                        have p37702_1 := h37702c.2.1
                                        have p37702_2 := h37702c.2.2.1
                                        have p37702_3 := h37702c.2.2.2
                                        linarith only [h36832, hlam, p37702_1]
                                      · have p37702_0 := h37702c.1
                                        have p37702_1 := h37702c.2.1
                                        have p37702_2 := h37702c.2.2.1
                                        have p37702_3 := h37702c.2.2.2
                                        linarith only [h37311, hlam, p37702_1]
                                      · have p37702_0 := h37702c.1
                                        have p37702_1 := h37702c.2.1
                                        have p37702_2 := h37702c.2.2.1
                                        have p37702_3 := h37702c.2.2.2
                                        linarith only [hlam, p37702_0]
                                      · have p37702_0 := h37702c.1
                                        have p37702_1 := h37702c.2.1
                                        have p37702_2 := h37702c.2.2.1
                                        have p37702_3 := h37702c.2.2.2
                                        linarith only [h36830, h37320, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p37550_1, p37702_1]
                                      · have p37702_0 := h37702c.1
                                        have p37702_1 := h37702c.2.1
                                        have p37702_2 := h37702c.2.2.1
                                        have p37702_3 := h37702c.2.2.2
                                        linarith only [h37318, hlam, p37702_0]
                                      · have p37702_0 := h37702c.1
                                        have p37702_1 := h37702c.2.1
                                        have p37702_2 := h37702c.2.2.1
                                        have p37702_3 := h37702c.2.2.2
                                        linarith only [h36834, hlam, p37702_1]
                                      · have p37702_0 := h37702c.1
                                        have p37702_1 := h37702c.2.1
                                        have p37702_2 := h37702c.2.2.1
                                        have p37702_3 := h37702c.2.2.2
                                        linarith only [h37313, hlam, p37702_1]
                                      · have p37702_0 := h37702c.1
                                        have p37702_1 := h37702c.2.1
                                        have p37702_2 := h37702c.2.2.1
                                        have p37702_3 := h37702c.2.2.2
                                        linarith only [h37317, hlam, p37702_0]
                                      · have p37702_0 := h37702c.1
                                        have p37702_1 := h37702c.2.1
                                        have p37702_2 := h37702c.2.2.1
                                        have p37702_3 := h37702c.2.2.2
                                        linarith only [hlam, p37702_0]
                                      · have p37702_0 := h37702c.1
                                        have p37702_1 := h37702c.2.1
                                        have p37702_2 := h37702c.2.2.1
                                        have p37702_3 := h37702c.2.2.2
                                        linarith only [h37320, hlam, p37702_0]
                                      · have p37702_0 := h37702c.1
                                        have p37702_1 := h37702c.2.1
                                        have p37702_2 := h37702c.2.2.1
                                        have p37702_3 := h37702c.2.2.2
                                        linarith only [h36834, h37320, hc34, hc45, hlam, hphi, p37702_1]
                                      · have p37702_0 := h37702c.1
                                        have p37702_1 := h37702c.2.1
                                        have p37702_2 := h37702c.2.2.1
                                        have p37702_3 := h37702c.2.2.2
                                        linarith only [h37313, h37320, hc34, hc45, hlam, hphi, p37702_1]
                                      · have p37702_0 := h37702c.1
                                        have p37702_1 := h37702c.2.1
                                        have p37702_2 := h37702c.2.2.1
                                        have p37702_3 := h37702c.2.2.2
                                        linarith only [h37317, h37320, hc34, hc45, hlam, hphi, p37702_1]
                                      · have p37702_0 := h37702c.1
                                        have p37702_1 := h37702c.2.1
                                        have p37702_2 := h37702c.2.2.1
                                        have p37702_3 := h37702c.2.2.2
                                        linarith only [h37320, hc34, hc45, hlam, hphi, p37702_1]
                                      · have p37702_0 := h37702c.1
                                        have p37702_1 := h37702c.2.1
                                        have p37702_2 := h37702c.2.2.1
                                        have p37702_3 := h37702c.2.2.2
                                        linarith only [hlam, p37702_0]
                                    · linarith only [h37701, hlam, p37672_0]
                          · have p37672_0 := h37672c.1
                            have p37672_1 := h37672c.2.1
                            have p37672_2 := h37672c.2.2.1
                            have p37672_3 := h37672c.2.2.2
                            rcases p37672_3 (m.d 0 4) (by simp) with h37729 | h37729
                            · linarith only [h36835, h37729, hlam]
                            · linarith only [h36828, h37729, hlam]
                          · have p37672_0 := h37672c.1
                            have p37672_1 := h37672c.2.1
                            have p37672_2 := h37672c.2.2.1
                            have p37672_3 := h37672c.2.2.2
                            rcases p37672_3 (m.d 0 4) (by simp) with h37732 | h37732
                            · linarith only [h36835, h37732, hlam]
                            · linarith only [h36831, h37732, hlam]
                          · have p37672_0 := h37672c.1
                            have p37672_1 := h37672c.2.1
                            have p37672_2 := h37672c.2.2.1
                            have p37672_3 := h37672c.2.2.2
                            rcases p37672_3 (m.d 0 4) (by simp) with h37735 | h37735
                            · linarith only [h36835, h37735, hlam]
                            · linarith only [h36833, h37735, hlam]
                          · have p37672_0 := h37672c.1
                            have p37672_1 := h37672c.2.1
                            have p37672_2 := h37672c.2.2.1
                            have p37672_3 := h37672c.2.2.2
                            linarith only [hlam, p37672_0]
                    · linarith only [h37317, h37667, hlam]
                  · linarith only [h37311, h37666, hlam]
                · linarith only [h36832, h37665, hlam]
              · have p37550_0 := h37550c.1
                have p37550_1 := h37550c.2.1
                have p37550_2 := h37550c.2.2.1
                have p37550_3 := h37550c.2.2.2
                linarith only [h36831, hlam, p37550_0]
              · have p37550_0 := h37550c.1
                have p37550_1 := h37550c.2.1
                have p37550_2 := h37550c.2.2.1
                have p37550_3 := h37550c.2.2.2
                linarith only [h37310, hlam, p37550_0]
              · have p37550_0 := h37550c.1
                have p37550_1 := h37550c.2.1
                have p37550_2 := h37550c.2.2.1
                have p37550_3 := h37550c.2.2.2
                linarith only [h37316, hlam, p37550_0]
              · have p37550_0 := h37550c.1
                have p37550_1 := h37550c.2.1
                have p37550_2 := h37550c.2.2.1
                have p37550_3 := h37550c.2.2.2
                linarith only [hlam, p37550_0]
              · have p37550_0 := h37550c.1
                have p37550_1 := h37550c.2.1
                have p37550_2 := h37550c.2.2.1
                have p37550_3 := h37550c.2.2.2
                linarith only [h37318, hlam, p37550_0]
              · have p37550_0 := h37550c.1
                have p37550_1 := h37550c.2.1
                have p37550_2 := h37550c.2.2.1
                have p37550_3 := h37550c.2.2.2
                linarith only [h36832, hlam, p37550_0]
              · have p37550_0 := h37550c.1
                have p37550_1 := h37550c.2.1
                have p37550_2 := h37550c.2.2.1
                have p37550_3 := h37550c.2.2.2
                linarith only [h37311, hlam, p37550_0]
              · have p37550_0 := h37550c.1
                have p37550_1 := h37550c.2.1
                have p37550_2 := h37550c.2.2.1
                have p37550_3 := h37550c.2.2.2
                linarith only [h37317, hlam, p37550_0]
              · have p37550_0 := h37550c.1
                have p37550_1 := h37550c.2.1
                have p37550_2 := h37550c.2.2.1
                have p37550_3 := h37550c.2.2.2
                linarith only [h33187, h37309, h37311, h37316, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p37322_1, p37550_1]
              · have p37550_0 := h37550c.1
                have p37550_1 := h37550c.2.1
                have p37550_2 := h37550c.2.2.1
                have p37550_3 := h37550c.2.2.2
                linarith only [hlam, p37550_0]
      · linarith only [h37313, h37339, hlam]
    · linarith only [h37311, h37338, hlam]
  · linarith only [h37337, hlam, p37322_0]

set_option maxHeartbeats 22102000 in
set_option maxHeartbeats 22102000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s37_x0_x0_x0_x0_x0_x0_x0_x1_x0_x0_x0_x0_x0_x1_x0_x0_x1_x1_x5 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg33187 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h36828 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h36829 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h36830 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h36831 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h36832 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h36833 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h36834 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h36835 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h37309 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h37310 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h37311 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h37312 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h37313 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h37314 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h37316 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h37317 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
    (h37318 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h37320 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h37322c : ((m.d 1 2) < (m.d 0 1) ∧ 2 * m.lam ≤ (m.d 0 1) - (m.d 1 2) ∧ (m.d 0 1) - (m.d 1 2) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)], z ≤ (m.d 1 2) ∨ (m.d 0 1) ≤ z)))
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
  have h5bigk := hb5.1
  have h0 := hg0
  have h33187 := hg33187
  have p37322_0 := h37322c.1
  have p37322_1 := h37322c.2.1
  have p37322_2 := h37322c.2.2.1
  have p37322_3 := h37322c.2.2.2
  rcases p37322_3 (m.d 0 1) (by simp) with h37755 | h37755
  · linarith only [h37755, hlam, p37322_0]
  · rcases p37322_3 (m.d 1 2) (by simp) with h37757 | h37757
    · rcases p37322_3 (m.d 1 3) (by simp) with h37758 | h37758
      · linarith only [h37309, h37758, hlam]
      · linarith only [h33187, h37758, hlam]
    · linarith only [h37757, hlam, p37322_0]

set_option maxHeartbeats 22102000 in
set_option maxHeartbeats 22102000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s37_x0_x0_x0_x0_x0_x0_x0_x1_x0_x0_x0_x0_x0_x1_x0_x0_x1_x1_x6 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg33187 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h36828 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h36829 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h36830 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h36831 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h36832 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h36833 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h36834 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h36835 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h37309 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h37310 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h37311 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h37312 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h37313 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h37314 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h37316 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h37317 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
    (h37318 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h37320 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h37322c : ((m.d 1 2) < (m.d 1 2) ∧ 2 * m.lam ≤ (m.d 1 2) - (m.d 1 2) ∧ (m.d 1 2) - (m.d 1 2) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)], z ≤ (m.d 1 2) ∨ (m.d 1 2) ≤ z)))
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
  have h5bigk := hb5.1
  have h0 := hg0
  have h33187 := hg33187
  have p37322_0 := h37322c.1
  have p37322_1 := h37322c.2.1
  have p37322_2 := h37322c.2.2.1
  have p37322_3 := h37322c.2.2.2
  linarith only [hlam, p37322_0]

set_option maxHeartbeats 22102000 in
set_option maxHeartbeats 22102000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s37_x0_x0_x0_x0_x0_x0_x0_x1_x0_x0_x0_x0_x0_x1_x0_x0_x1_x1_x7 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg33187 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h36828 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h36829 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h36830 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h36831 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h36832 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h36833 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h36834 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h36835 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h37309 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h37310 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h37311 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h37312 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h37313 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h37314 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h37316 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h37317 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
    (h37318 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h37320 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h37322c : ((m.d 1 2) < (m.d 1 3) ∧ 2 * m.lam ≤ (m.d 1 3) - (m.d 1 2) ∧ (m.d 1 3) - (m.d 1 2) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)], z ≤ (m.d 1 2) ∨ (m.d 1 3) ≤ z)))
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
  have h5bigk := hb5.1
  have h0 := hg0
  have h33187 := hg33187
  have p37322_0 := h37322c.1
  have p37322_1 := h37322c.2.1
  have p37322_2 := h37322c.2.2.1
  have p37322_3 := h37322c.2.2.2
  linarith only [h33187, hc01, hc12, hlam, hphi, p37322_1]

set_option maxHeartbeats 22102000 in
set_option maxHeartbeats 22102000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s37_x0_x0_x0_x0_x0_x0_x0_x1_x0_x0_x0_x0_x0_x1_x0_x0_x1_x1_x8 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg33187 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h36828 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h36829 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h36830 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h36831 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h36832 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h36833 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h36834 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h36835 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h37309 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h37310 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h37311 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h37312 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h37313 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h37314 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h37316 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h37317 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
    (h37318 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h37320 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h37322c : ((m.d 1 2) < (m.d 1 4) ∧ 2 * m.lam ≤ (m.d 1 4) - (m.d 1 2) ∧ (m.d 1 4) - (m.d 1 2) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)], z ≤ (m.d 1 2) ∨ (m.d 1 4) ≤ z)))
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
  have h5bigk := hb5.1
  have h0 := hg0
  have h33187 := hg33187
  have p37322_0 := h37322c.1
  have p37322_1 := h37322c.2.1
  have p37322_2 := h37322c.2.2.1
  have p37322_3 := h37322c.2.2.2
  rcases p37322_3 (m.d 0 1) (by simp) with h37764 | h37764
  · linarith only [h0, h37764, hlam]
  · linarith only [h36828, h37764, hlam]

set_option maxHeartbeats 22102000 in
set_option maxHeartbeats 22102000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s37_x0_x0_x0_x0_x0_x0_x0_x1_x0_x0_x0_x0_x0_x1_x0_x0_x1_x1_x9 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg33187 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h36828 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h36829 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h36830 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h36831 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h36832 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h36833 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h36834 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h36835 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h37309 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h37310 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h37311 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h37312 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h37313 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h37314 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h37316 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h37317 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
    (h37318 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h37320 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h37322c : ((m.d 1 2) < (m.d 1 5) ∧ 2 * m.lam ≤ (m.d 1 5) - (m.d 1 2) ∧ (m.d 1 5) - (m.d 1 2) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)], z ≤ (m.d 1 2) ∨ (m.d 1 5) ≤ z)))
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
  have h5bigk := hb5.1
  have h0 := hg0
  have h33187 := hg33187
  have p37322_0 := h37322c.1
  have p37322_1 := h37322c.2.1
  have p37322_2 := h37322c.2.2.1
  have p37322_3 := h37322c.2.2.2
  rcases p37322_3 (m.d 0 1) (by simp) with h37767 | h37767
  · linarith only [h0, h37767, hlam]
  · linarith only [h36829, h37767, hlam]

end R2N4
