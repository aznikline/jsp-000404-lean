import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_3S29

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5544000 in
set_option maxHeartbeats 5544000 in
theorem r1l7_11_13_25_L_I_L_I_H_I_s19_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg14799 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg16563 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg17994 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg19110 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg19111 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg19112 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h19113 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
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
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h14799 := hg14799
  have h16563 := hg16563
  have h17994 := hg17994
  have h19110 := hg19110
  have h19111 := hg19111
  have h19112 := hg19112
  rcases m.htr 0 3 5 (by decide) (by decide) with h21259 | h21259
  · rcases m.htr 0 4 5 (by decide) (by decide) with h21260 | h21260
    · rcases m.htr 1 2 3 (by decide) (by decide) with h21261 | h21261
      · rcases m.htr 1 2 4 (by decide) (by decide) with h21262 | h21262
        · rcases m.htr 1 2 5 (by decide) (by decide) with h21263 | h21263
          · rcases m.htr 1 3 4 (by decide) (by decide) with h21264 | h21264
            · rcases m.htr 1 3 5 (by decide) (by decide) with h21265 | h21265
              · rcases m.htr 1 4 5 (by decide) (by decide) with h21266 | h21266
                · rcases m.htr 2 3 4 (by decide) (by decide) with h21267 | h21267
                  · linarith only [h19110, h19113, h21259, h21267, hc02, hc35, hlam, hphi, ht0b, ht5b]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h21269 | h21269
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h21270 | h21270
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h21271 | h21271
                        · rcases h1bigk with h21272c | h21272c | h21272c | h21272c | h21272c | h21272c | h21272c | h21272c | h21272c | h21272c | h21272c | h21272c | h21272c | h21272c | h21272c | h21272c | h21272c | h21272c | h21272c | h21272c | h21272c | h21272c | h21272c | h21272c | h21272c
                          · have p21272_0 := h21272c.1
                            have p21272_1 := h21272c.2.1
                            have p21272_2 := h21272c.2.2.1
                            have p21272_3 := h21272c.2.2.2
                            linarith only [hlam, p21272_0]
                          · have p21272_0 := h21272c.1
                            have p21272_1 := h21272c.2.1
                            have p21272_2 := h21272c.2.2.1
                            have p21272_3 := h21272c.2.2.2
                            linarith only [h0, hlam, p21272_0]
                          · have p21272_0 := h21272c.1
                            have p21272_1 := h21272c.2.1
                            have p21272_2 := h21272c.2.2.1
                            have p21272_3 := h21272c.2.2.2
                            linarith only [h14799, hlam, p21272_0]
                          · have p21272_0 := h21272c.1
                            have p21272_1 := h21272c.2.1
                            have p21272_2 := h21272c.2.2.1
                            have p21272_3 := h21272c.2.2.2
                            linarith only [h16563, hlam, p21272_0]
                          · have p21272_0 := h21272c.1
                            have p21272_1 := h21272c.2.1
                            have p21272_2 := h21272c.2.2.1
                            have p21272_3 := h21272c.2.2.2
                            linarith only [h17994, hlam, p21272_0]
                          · have p21272_0 := h21272c.1
                            have p21272_1 := h21272c.2.1
                            have p21272_2 := h21272c.2.2.1
                            have p21272_3 := h21272c.2.2.2
                            rcases p21272_3 (m.d 0 1) (by simp) with h21278 | h21278
                            · linarith only [h21278, hlam, p21272_0]
                            · rcases p21272_3 (m.d 1 2) (by simp) with h21280 | h21280
                              · rcases p21272_3 (m.d 1 3) (by simp) with h21281 | h21281
                                · linarith only [h21261, h21281, hlam]
                                · linarith only [h14799, h21281, hlam]
                              · linarith only [h21280, hlam, p21272_0]
                          · have p21272_0 := h21272c.1
                            have p21272_1 := h21272c.2.1
                            have p21272_2 := h21272c.2.2.1
                            have p21272_3 := h21272c.2.2.2
                            linarith only [hlam, p21272_0]
                          · have p21272_0 := h21272c.1
                            have p21272_1 := h21272c.2.1
                            have p21272_2 := h21272c.2.2.1
                            have p21272_3 := h21272c.2.2.2
                            linarith only [h14799, hc01, hc12, hlam, hphi, p21272_1]
                          · have p21272_0 := h21272c.1
                            have p21272_1 := h21272c.2.1
                            have p21272_2 := h21272c.2.2.1
                            have p21272_3 := h21272c.2.2.2
                            linarith only [h16563, hc01, hc12, hlam, hphi, p21272_1]
                          · have p21272_0 := h21272c.1
                            have p21272_1 := h21272c.2.1
                            have p21272_2 := h21272c.2.2.1
                            have p21272_3 := h21272c.2.2.2
                            linarith only [h17994, hc01, hc12, hlam, hphi, p21272_1]
                          · have p21272_0 := h21272c.1
                            have p21272_1 := h21272c.2.1
                            have p21272_2 := h21272c.2.2.1
                            have p21272_3 := h21272c.2.2.2
                            rcases p21272_3 (m.d 0 1) (by simp) with h21289 | h21289
                            · linarith only [h21289, hlam, p21272_0]
                            · rcases p21272_3 (m.d 1 2) (by simp) with h21291 | h21291
                              · rcases p21272_3 (m.d 1 3) (by simp) with h21292 | h21292
                                · rcases p21272_3 (m.d 1 4) (by simp) with h21293 | h21293
                                  · linarith only [h21264, h21293, hlam]
                                  · linarith only [h16563, h21293, hlam]
                                · linarith only [h21292, hlam, p21272_0]
                              · linarith only [h0, h21291, hlam]
                          · have p21272_0 := h21272c.1
                            have p21272_1 := h21272c.2.1
                            have p21272_2 := h21272c.2.2.1
                            have p21272_3 := h21272c.2.2.2
                            linarith only [h21261, hlam, p21272_1]
                          · have p21272_0 := h21272c.1
                            have p21272_1 := h21272c.2.1
                            have p21272_2 := h21272c.2.2.1
                            have p21272_3 := h21272c.2.2.2
                            linarith only [hlam, p21272_0]
                          · have p21272_0 := h21272c.1
                            have p21272_1 := h21272c.2.1
                            have p21272_2 := h21272c.2.2.1
                            have p21272_3 := h21272c.2.2.2
                            linarith only [h19110, h19113, h21264, h21269, h21271, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p21272_1]
                          · have p21272_0 := h21272c.1
                            have p21272_1 := h21272c.2.1
                            have p21272_2 := h21272c.2.2.1
                            have p21272_3 := h21272c.2.2.2
                            linarith only [h17994, h21261, hc01, hc12, hlam, hphi, p21272_1]
                          · have p21272_0 := h21272c.1
                            have p21272_1 := h21272c.2.1
                            have p21272_2 := h21272c.2.2.1
                            have p21272_3 := h21272c.2.2.2
                            rcases p21272_3 (m.d 0 1) (by simp) with h21302 | h21302
                            · linarith only [h21302, hlam, p21272_0]
                            · rcases p21272_3 (m.d 1 2) (by simp) with h21304 | h21304
                              · rcases p21272_3 (m.d 1 3) (by simp) with h21305 | h21305
                                · rcases p21272_3 (m.d 1 4) (by simp) with h21306 | h21306
                                  · rcases p21272_3 (m.d 1 5) (by simp) with h21307 | h21307
                                    · linarith only [h21266, h21307, hlam]
                                    · linarith only [h17994, h21307, hlam]
                                  · linarith only [h21306, hlam, p21272_0]
                                · linarith only [h14799, h21305, hlam]
                              · linarith only [h0, h21304, hlam]
                          · have p21272_0 := h21272c.1
                            have p21272_1 := h21272c.2.1
                            have p21272_2 := h21272c.2.2.1
                            have p21272_3 := h21272c.2.2.2
                            linarith only [h21262, hlam, p21272_1]
                          · have p21272_0 := h21272c.1
                            have p21272_1 := h21272c.2.1
                            have p21272_2 := h21272c.2.2.1
                            have p21272_3 := h21272c.2.2.2
                            linarith only [h21264, hlam, p21272_0]
                          · have p21272_0 := h21272c.1
                            have p21272_1 := h21272c.2.1
                            have p21272_2 := h21272c.2.2.1
                            have p21272_3 := h21272c.2.2.2
                            linarith only [hlam, p21272_0]
                          · have p21272_0 := h21272c.1
                            have p21272_1 := h21272c.2.1
                            have p21272_2 := h21272c.2.2.1
                            have p21272_3 := h21272c.2.2.2
                            linarith only [h17994, hc01, hc14, hlam, hphi, p21272_1]
                          · have p21272_0 := h21272c.1
                            have p21272_1 := h21272c.2.1
                            have p21272_2 := h21272c.2.2.1
                            have p21272_3 := h21272c.2.2.2
                            rcases p21272_3 (m.d 0 1) (by simp) with h21317 | h21317
                            · linarith only [h21317, hlam, p21272_0]
                            · rcases p21272_3 (m.d 1 2) (by simp) with h21319 | h21319
                              · rcases p21272_3 (m.d 1 3) (by simp) with h21320 | h21320
                                · rcases p21272_3 (m.d 1 4) (by simp) with h21321 | h21321
                                  · rcases p21272_3 (m.d 1 5) (by simp) with h21322 | h21322
                                    · rcases h3bigk with h21323c | h21323c | h21323c | h21323c | h21323c | h21323c | h21323c | h21323c | h21323c | h21323c | h21323c | h21323c | h21323c | h21323c | h21323c | h21323c | h21323c | h21323c | h21323c | h21323c | h21323c | h21323c | h21323c | h21323c | h21323c
                                      · have p21323_0 := h21323c.1
                                        have p21323_1 := h21323c.2.1
                                        have p21323_2 := h21323c.2.2.1
                                        have p21323_3 := h21323c.2.2.2
                                        linarith only [hlam, p21323_0]
                                      · have p21323_0 := h21323c.1
                                        have p21323_1 := h21323c.2.1
                                        have p21323_2 := h21323c.2.2.1
                                        have p21323_3 := h21323c.2.2.2
                                        linarith only [h14799, hlam, p21323_1]
                                      · have p21323_0 := h21323c.1
                                        have p21323_1 := h21323c.2.1
                                        have p21323_2 := h21323c.2.2.1
                                        have p21323_3 := h21323c.2.2.2
                                        linarith only [h19113, h21269, h21271, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p21323_1]
                                      · have p21323_0 := h21323c.1
                                        have p21323_1 := h21323c.2.1
                                        have p21323_2 := h21323c.2.2.1
                                        have p21323_3 := h21323c.2.2.2
                                        linarith only [h19113, hlam, p21323_0]
                                      · have p21323_0 := h21323c.1
                                        have p21323_1 := h21323c.2.1
                                        have p21323_2 := h21323c.2.2.1
                                        have p21323_3 := h21323c.2.2.2
                                        linarith only [h19113, h21261, h21264, h21271, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p21323_1]
                                      · have p21323_0 := h21323c.1
                                        have p21323_1 := h21323c.2.1
                                        have p21323_2 := h21323c.2.2.1
                                        have p21323_3 := h21323c.2.2.2
                                        rcases p21323_3 (m.d 0 3) (by simp) with h21329 | h21329
                                        · linarith only [h14799, h21329, hlam]
                                        · rcases p21323_3 (m.d 1 3) (by simp) with h21331 | h21331
                                          · rcases p21323_3 (m.d 2 3) (by simp) with h21332 | h21332
                                            · linarith only [h21261, h21332, hlam]
                                            · rcases p21323_3 (m.d 3 4) (by simp) with h21334 | h21334
                                              · linarith only [h21264, h21334, hlam]
                                              · linarith only [h19113, h21334, hlam]
                                          · linarith only [h14799, h21331, hlam]
                                      · have p21323_0 := h21323c.1
                                        have p21323_1 := h21323c.2.1
                                        have p21323_2 := h21323c.2.2.1
                                        have p21323_3 := h21323c.2.2.2
                                        linarith only [hlam, p21323_0]
                                      · have p21323_0 := h21323c.1
                                        have p21323_1 := h21323c.2.1
                                        have p21323_2 := h21323c.2.2.1
                                        have p21323_3 := h21323c.2.2.2
                                        rcases p21323_3 (m.d 0 3) (by simp) with h21339 | h21339
                                        · linarith only [h14799, h21339, hlam]
                                        · linarith only [h19110, h21339, hlam]
                                      · have p21323_0 := h21323c.1
                                        have p21323_1 := h21323c.2.1
                                        have p21323_2 := h21323c.2.2.1
                                        have p21323_3 := h21323c.2.2.2
                                        linarith only [h14799, h19113, h21261, hc01, hc12, hlam, hphi, p21323_1]
                                      · have p21323_0 := h21323c.1
                                        have p21323_1 := h21323c.2.1
                                        have p21323_2 := h21323c.2.2.1
                                        have p21323_3 := h21323c.2.2.2
                                        linarith only [h19110, h19113, h21264, h21269, hlam, p21323_2]
                                      · have p21323_0 := h21323c.1
                                        have p21323_1 := h21323c.2.1
                                        have p21323_2 := h21323c.2.2.1
                                        have p21323_3 := h21323c.2.2.2
                                        linarith only [h19110, hlam, p21323_0]
                                      · have p21323_0 := h21323c.1
                                        have p21323_1 := h21323c.2.1
                                        have p21323_2 := h21323c.2.2.1
                                        have p21323_3 := h21323c.2.2.2
                                        linarith only [h21261, hlam, p21323_0]
                                      · have p21323_0 := h21323c.1
                                        have p21323_1 := h21323c.2.1
                                        have p21323_2 := h21323c.2.2.1
                                        have p21323_3 := h21323c.2.2.2
                                        linarith only [hlam, p21323_0]
                                      · have p21323_0 := h21323c.1
                                        have p21323_1 := h21323c.2.1
                                        have p21323_2 := h21323c.2.2.1
                                        have p21323_3 := h21323c.2.2.2
                                        linarith only [h21267, hlam, p21323_0]
                                      · have p21323_0 := h21323c.1
                                        have p21323_1 := h21323c.2.1
                                        have p21323_2 := h21323c.2.2.1
                                        have p21323_3 := h21323c.2.2.2
                                        linarith only [h19110, h19113, h21264, h21271, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p21323_1]
                                      · have p21323_0 := h21323c.1
                                        have p21323_1 := h21323c.2.1
                                        have p21323_2 := h21323c.2.2.1
                                        have p21323_3 := h21323c.2.2.2
                                        linarith only [h14799, h21264, hc01, hc13, hlam, hphi, p21323_1]
                                      · have p21323_0 := h21323c.1
                                        have p21323_1 := h21323c.2.1
                                        have p21323_2 := h21323c.2.2.1
                                        have p21323_3 := h21323c.2.2.2
                                        linarith only [h21264, hlam, p21323_0]
                                      · have p21323_0 := h21323c.1
                                        have p21323_1 := h21323c.2.1
                                        have p21323_2 := h21323c.2.2.1
                                        have p21323_3 := h21323c.2.2.2
                                        linarith only [h21261, h21264, h21269, h21271, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p21323_1]
                                      · have p21323_0 := h21323c.1
                                        have p21323_1 := h21323c.2.1
                                        have p21323_2 := h21323c.2.2.1
                                        have p21323_3 := h21323c.2.2.2
                                        linarith only [hlam, p21323_0]
                                      · have p21323_0 := h21323c.1
                                        have p21323_1 := h21323c.2.1
                                        have p21323_2 := h21323c.2.2.1
                                        have p21323_3 := h21323c.2.2.2
                                        rcases p21323_3 (m.d 0 3) (by simp) with h21353 | h21353
                                        · linarith only [h19113, h21353, hlam]
                                        · linarith only [h21259, h21353, hlam]
                                      · have p21323_0 := h21323c.1
                                        have p21323_1 := h21323c.2.1
                                        have p21323_2 := h21323c.2.2.1
                                        have p21323_3 := h21323c.2.2.2
                                        linarith only [h21259, hlam, p21323_0]
                                      · have p21323_0 := h21323c.1
                                        have p21323_1 := h21323c.2.1
                                        have p21323_2 := h21323c.2.2.1
                                        have p21323_3 := h21323c.2.2.2
                                        linarith only [h21265, hlam, p21323_0]
                                      · have p21323_0 := h21323c.1
                                        have p21323_1 := h21323c.2.1
                                        have p21323_2 := h21323c.2.2.1
                                        have p21323_3 := h21323c.2.2.2
                                        linarith only [h21269, hlam, p21323_0]
                                      · have p21323_0 := h21323c.1
                                        have p21323_1 := h21323c.2.1
                                        have p21323_2 := h21323c.2.2.1
                                        have p21323_3 := h21323c.2.2.2
                                        linarith only [h21271, hlam, p21323_0]
                                      · have p21323_0 := h21323c.1
                                        have p21323_1 := h21323c.2.1
                                        have p21323_2 := h21323c.2.2.1
                                        have p21323_3 := h21323c.2.2.2
                                        linarith only [hlam, p21323_0]
                                    · linarith only [h21322, hlam, p21272_0]
                                  · linarith only [h16563, h21321, hlam]
                                · linarith only [h14799, h21320, hlam]
                              · linarith only [h0, h21319, hlam]
                          · have p21272_0 := h21272c.1
                            have p21272_1 := h21272c.2.1
                            have p21272_2 := h21272c.2.2.1
                            have p21272_3 := h21272c.2.2.2
                            linarith only [h21263, hlam, p21272_1]
                          · have p21272_0 := h21272c.1
                            have p21272_1 := h21272c.2.1
                            have p21272_2 := h21272c.2.2.1
                            have p21272_3 := h21272c.2.2.2
                            linarith only [h21265, hlam, p21272_0]
                          · have p21272_0 := h21272c.1
                            have p21272_1 := h21272c.2.1
                            have p21272_2 := h21272c.2.2.1
                            have p21272_3 := h21272c.2.2.2
                            linarith only [h21266, hlam, p21272_0]
                          · have p21272_0 := h21272c.1
                            have p21272_1 := h21272c.2.1
                            have p21272_2 := h21272c.2.2.1
                            have p21272_3 := h21272c.2.2.2
                            linarith only [hlam, p21272_0]
                        · linarith only [h19110, h19113, h21260, h21269, h21271, hc04, hc35, hlam, hphi, ht0b, ht5b]
                      · linarith only [h19113, h21259, h21260, h21261, h21264, h21267, h21269, h21270, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                    · linarith only [h19113, h21259, h21261, h21264, h21269, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                · linarith only [h16563, h19113, h21259, h21260, h21261, h21264, h21266, hc01, hc12, hlam, hphi]
              · linarith only [h19113, h21259, h21264, h21265, hlam]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h21374 | h21374
              · rcases m.htr 1 4 5 (by decide) (by decide) with h21375 | h21375
                · rcases m.htr 2 3 4 (by decide) (by decide) with h21376 | h21376
                  · linarith only [h14799, h21264, h21376, hc01, hc23, hlam, hphi, ht12]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h21378 | h21378
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h21379 | h21379
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h21380 | h21380
                        · rcases h1bigk with h21381c | h21381c | h21381c | h21381c | h21381c | h21381c | h21381c | h21381c | h21381c | h21381c | h21381c | h21381c | h21381c | h21381c | h21381c | h21381c | h21381c | h21381c | h21381c | h21381c | h21381c | h21381c | h21381c | h21381c | h21381c
                          · have p21381_0 := h21381c.1
                            have p21381_1 := h21381c.2.1
                            have p21381_2 := h21381c.2.2.1
                            have p21381_3 := h21381c.2.2.2
                            linarith only [hlam, p21381_0]
                          · have p21381_0 := h21381c.1
                            have p21381_1 := h21381c.2.1
                            have p21381_2 := h21381c.2.2.1
                            have p21381_3 := h21381c.2.2.2
                            linarith only [h0, hlam, p21381_0]
                          · have p21381_0 := h21381c.1
                            have p21381_1 := h21381c.2.1
                            have p21381_2 := h21381c.2.2.1
                            have p21381_3 := h21381c.2.2.2
                            linarith only [h14799, hlam, p21381_0]
                          · have p21381_0 := h21381c.1
                            have p21381_1 := h21381c.2.1
                            have p21381_2 := h21381c.2.2.1
                            have p21381_3 := h21381c.2.2.2
                            linarith only [h16563, hlam, p21381_0]
                          · have p21381_0 := h21381c.1
                            have p21381_1 := h21381c.2.1
                            have p21381_2 := h21381c.2.2.1
                            have p21381_3 := h21381c.2.2.2
                            linarith only [h17994, hlam, p21381_0]
                          · have p21381_0 := h21381c.1
                            have p21381_1 := h21381c.2.1
                            have p21381_2 := h21381c.2.2.1
                            have p21381_3 := h21381c.2.2.2
                            rcases p21381_3 (m.d 0 1) (by simp) with h21387 | h21387
                            · linarith only [h21387, hlam, p21381_0]
                            · rcases p21381_3 (m.d 1 2) (by simp) with h21389 | h21389
                              · rcases p21381_3 (m.d 1 3) (by simp) with h21390 | h21390
                                · linarith only [h21261, h21390, hlam]
                                · linarith only [h14799, h21390, hlam]
                              · linarith only [h21389, hlam, p21381_0]
                          · have p21381_0 := h21381c.1
                            have p21381_1 := h21381c.2.1
                            have p21381_2 := h21381c.2.2.1
                            have p21381_3 := h21381c.2.2.2
                            linarith only [hlam, p21381_0]
                          · have p21381_0 := h21381c.1
                            have p21381_1 := h21381c.2.1
                            have p21381_2 := h21381c.2.2.1
                            have p21381_3 := h21381c.2.2.2
                            linarith only [h17994, h21374, hc01, hc12, hlam, hphi, p21381_1]
                          · have p21381_0 := h21381c.1
                            have p21381_1 := h21381c.2.1
                            have p21381_2 := h21381c.2.2.1
                            have p21381_3 := h21381c.2.2.2
                            linarith only [h16563, hc01, hc12, hlam, hphi, p21381_1]
                          · have p21381_0 := h21381c.1
                            have p21381_1 := h21381c.2.1
                            have p21381_2 := h21381c.2.2.1
                            have p21381_3 := h21381c.2.2.2
                            linarith only [h17994, hc01, hc12, hlam, hphi, p21381_1]
                          · have p21381_0 := h21381c.1
                            have p21381_1 := h21381c.2.1
                            have p21381_2 := h21381c.2.2.1
                            have p21381_3 := h21381c.2.2.2
                            linarith only [h21264, hc01, hc34, hlam, hphi, ht12, ht23, p21381_1]
                          · have p21381_0 := h21381c.1
                            have p21381_1 := h21381c.2.1
                            have p21381_2 := h21381c.2.2.1
                            have p21381_3 := h21381c.2.2.2
                            linarith only [h21261, hlam, p21381_1]
                          · have p21381_0 := h21381c.1
                            have p21381_1 := h21381c.2.1
                            have p21381_2 := h21381c.2.2.1
                            have p21381_3 := h21381c.2.2.2
                            linarith only [hlam, p21381_0]
                          · have p21381_0 := h21381c.1
                            have p21381_1 := h21381c.2.1
                            have p21381_2 := h21381c.2.2.1
                            have p21381_3 := h21381c.2.2.2
                            linarith only [h21264, hlam, p21381_1]
                          · have p21381_0 := h21381c.1
                            have p21381_1 := h21381c.2.1
                            have p21381_2 := h21381c.2.2.1
                            have p21381_3 := h21381c.2.2.2
                            linarith only [h17994, hc01, hc13, hlam, hphi, p21381_1]
                          · have p21381_0 := h21381c.1
                            have p21381_1 := h21381c.2.1
                            have p21381_2 := h21381c.2.2.1
                            have p21381_3 := h21381c.2.2.2
                            rcases p21381_3 (m.d 0 1) (by simp) with h21403 | h21403
                            · linarith only [h21403, hlam, p21381_0]
                            · rcases p21381_3 (m.d 1 2) (by simp) with h21405 | h21405
                              · rcases p21381_3 (m.d 1 3) (by simp) with h21406 | h21406
                                · linarith only [h21264, h21406, hlam]
                                · linarith only [h14799, h21406, hlam]
                              · linarith only [h0, h21405, hlam]
                          · have p21381_0 := h21381c.1
                            have p21381_1 := h21381c.2.1
                            have p21381_2 := h21381c.2.2.1
                            have p21381_3 := h21381c.2.2.2
                            linarith only [h21262, hlam, p21381_1]
                          · have p21381_0 := h21381c.1
                            have p21381_1 := h21381c.2.1
                            have p21381_2 := h21381c.2.2.1
                            have p21381_3 := h21381c.2.2.2
                            linarith only [h14799, h21264, hc01, hc34, hlam, hphi, ht12, ht23, p21381_1]
                          · have p21381_0 := h21381c.1
                            have p21381_1 := h21381c.2.1
                            have p21381_2 := h21381c.2.2.1
                            have p21381_3 := h21381c.2.2.2
                            linarith only [hlam, p21381_0]
                          · have p21381_0 := h21381c.1
                            have p21381_1 := h21381c.2.1
                            have p21381_2 := h21381c.2.2.1
                            have p21381_3 := h21381c.2.2.2
                            linarith only [h17994, h21264, hc01, hc34, hlam, hphi, ht12, ht23, p21381_1]
                          · have p21381_0 := h21381c.1
                            have p21381_1 := h21381c.2.1
                            have p21381_2 := h21381c.2.2.1
                            have p21381_3 := h21381c.2.2.2
                            linarith only [h21264, h21374, hc01, hc34, hlam, hphi, ht12, ht23, p21381_1]
                          · have p21381_0 := h21381c.1
                            have p21381_1 := h21381c.2.1
                            have p21381_2 := h21381c.2.2.1
                            have p21381_3 := h21381c.2.2.2
                            linarith only [h21263, hlam, p21381_1]
                          · have p21381_0 := h21381c.1
                            have p21381_1 := h21381c.2.1
                            have p21381_2 := h21381c.2.2.1
                            have p21381_3 := h21381c.2.2.2
                            linarith only [h21374, hlam, p21381_0]
                          · have p21381_0 := h21381c.1
                            have p21381_1 := h21381c.2.1
                            have p21381_2 := h21381c.2.2.1
                            have p21381_3 := h21381c.2.2.2
                            linarith only [h21375, hlam, p21381_0]
                          · have p21381_0 := h21381c.1
                            have p21381_1 := h21381c.2.1
                            have p21381_2 := h21381c.2.2.1
                            have p21381_3 := h21381c.2.2.2
                            linarith only [hlam, p21381_0]
                        · linarith only [h14799, h21264, h21380, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                      · linarith only [h21376, h21378, h21379, hlam]
                    · linarith only [h14799, h21259, h21264, h21378, hc23, hc34, hlam, hphi]
                · linarith only [h14799, h16563, h21259, h21260, h21264, h21375, hc01, hc34, hlam, hphi, ht12, ht23]
              · linarith only [h14799, h21259, h21374, hlam]
          · linarith only [h0, h19112, h21263, hlam]
        · linarith only [h0, h19111, h21262, hlam]
      · linarith only [h0, h19110, h21261, hlam]
    · linarith only [h19113, h21259, h21260, hlam]
  · rcases m.htr 0 4 5 (by decide) (by decide) with h21428 | h21428
    · rcases m.htr 1 2 3 (by decide) (by decide) with h21429 | h21429
      · rcases m.htr 1 2 4 (by decide) (by decide) with h21430 | h21430
        · rcases m.htr 1 2 5 (by decide) (by decide) with h21431 | h21431
          · rcases m.htr 1 3 4 (by decide) (by decide) with h21432 | h21432
            · rcases m.htr 1 3 5 (by decide) (by decide) with h21433 | h21433
              · rcases m.htr 1 4 5 (by decide) (by decide) with h21434 | h21434
                · rcases m.htr 2 3 4 (by decide) (by decide) with h21435 | h21435
                  · linarith only [h0, h14799, h19110, h19113, h21435, hc01, hc12, hlam, hphi]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h21437 | h21437
                    · linarith only [h19110, h21259, h21437, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h21439 | h21439
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h21440 | h21440
                        · rcases h1bigk with h21441c | h21441c | h21441c | h21441c | h21441c | h21441c | h21441c | h21441c | h21441c | h21441c | h21441c | h21441c | h21441c | h21441c | h21441c | h21441c | h21441c | h21441c | h21441c | h21441c | h21441c | h21441c | h21441c | h21441c | h21441c
                          · have p21441_0 := h21441c.1
                            have p21441_1 := h21441c.2.1
                            have p21441_2 := h21441c.2.2.1
                            have p21441_3 := h21441c.2.2.2
                            linarith only [hlam, p21441_0]
                          · have p21441_0 := h21441c.1
                            have p21441_1 := h21441c.2.1
                            have p21441_2 := h21441c.2.2.1
                            have p21441_3 := h21441c.2.2.2
                            linarith only [h0, hlam, p21441_0]
                          · have p21441_0 := h21441c.1
                            have p21441_1 := h21441c.2.1
                            have p21441_2 := h21441c.2.2.1
                            have p21441_3 := h21441c.2.2.2
                            linarith only [h14799, hlam, p21441_0]
                          · have p21441_0 := h21441c.1
                            have p21441_1 := h21441c.2.1
                            have p21441_2 := h21441c.2.2.1
                            have p21441_3 := h21441c.2.2.2
                            linarith only [h16563, hlam, p21441_0]
                          · have p21441_0 := h21441c.1
                            have p21441_1 := h21441c.2.1
                            have p21441_2 := h21441c.2.2.1
                            have p21441_3 := h21441c.2.2.2
                            linarith only [h17994, hlam, p21441_0]
                          · have p21441_0 := h21441c.1
                            have p21441_1 := h21441c.2.1
                            have p21441_2 := h21441c.2.2.1
                            have p21441_3 := h21441c.2.2.2
                            rcases p21441_3 (m.d 0 1) (by simp) with h21447 | h21447
                            · linarith only [h21447, hlam, p21441_0]
                            · rcases p21441_3 (m.d 1 2) (by simp) with h21449 | h21449
                              · rcases p21441_3 (m.d 1 3) (by simp) with h21450 | h21450
                                · linarith only [h21429, h21450, hlam]
                                · linarith only [h14799, h21450, hlam]
                              · linarith only [h21449, hlam, p21441_0]
                          · have p21441_0 := h21441c.1
                            have p21441_1 := h21441c.2.1
                            have p21441_2 := h21441c.2.2.1
                            have p21441_3 := h21441c.2.2.2
                            linarith only [hlam, p21441_0]
                          · have p21441_0 := h21441c.1
                            have p21441_1 := h21441c.2.1
                            have p21441_2 := h21441c.2.2.1
                            have p21441_3 := h21441c.2.2.2
                            linarith only [h14799, h21259, h21432, h21440, hc01, hc12, hlam, hphi, p21441_1]
                          · have p21441_0 := h21441c.1
                            have p21441_1 := h21441c.2.1
                            have p21441_2 := h21441c.2.2.1
                            have p21441_3 := h21441c.2.2.2
                            linarith only [h14799, h21259, h21433, h21434, hc01, hc12, hlam, hphi, p21441_1]
                          · have p21441_0 := h21441c.1
                            have p21441_1 := h21441c.2.1
                            have p21441_2 := h21441c.2.2.1
                            have p21441_3 := h21441c.2.2.2
                            linarith only [h14799, h21259, h21433, hc01, hc12, hlam, hphi, p21441_1]
                          · have p21441_0 := h21441c.1
                            have p21441_1 := h21441c.2.1
                            have p21441_2 := h21441c.2.2.1
                            have p21441_3 := h21441c.2.2.2
                            rcases p21441_3 (m.d 0 1) (by simp) with h21458 | h21458
                            · linarith only [h21458, hlam, p21441_0]
                            · rcases p21441_3 (m.d 1 2) (by simp) with h21460 | h21460
                              · rcases p21441_3 (m.d 1 3) (by simp) with h21461 | h21461
                                · rcases p21441_3 (m.d 1 4) (by simp) with h21462 | h21462
                                  · linarith only [h21432, h21462, hlam]
                                  · linarith only [h16563, h21462, hlam]
                                · linarith only [h21461, hlam, p21441_0]
                              · linarith only [h0, h21460, hlam]
                          · have p21441_0 := h21441c.1
                            have p21441_1 := h21441c.2.1
                            have p21441_2 := h21441c.2.2.1
                            have p21441_3 := h21441c.2.2.2
                            linarith only [h21429, hlam, p21441_1]
                          · have p21441_0 := h21441c.1
                            have p21441_1 := h21441c.2.1
                            have p21441_2 := h21441c.2.2.1
                            have p21441_3 := h21441c.2.2.2
                            linarith only [hlam, p21441_0]
                          · have p21441_0 := h21441c.1
                            have p21441_1 := h21441c.2.1
                            have p21441_2 := h21441c.2.2.1
                            have p21441_3 := h21441c.2.2.2
                            linarith only [h14799, h21259, h21433, h21434, hc01, hc13, hlam, hphi, p21441_1]
                          · have p21441_0 := h21441c.1
                            have p21441_1 := h21441c.2.1
                            have p21441_2 := h21441c.2.2.1
                            have p21441_3 := h21441c.2.2.2
                            linarith only [h14799, h21259, h21429, h21433, hc01, hc12, hlam, hphi, p21441_1]
                          · have p21441_0 := h21441c.1
                            have p21441_1 := h21441c.2.1
                            have p21441_2 := h21441c.2.2.1
                            have p21441_3 := h21441c.2.2.2
                            rcases p21441_3 (m.d 0 1) (by simp) with h21471 | h21471
                            · linarith only [h21471, hlam, p21441_0]
                            · rcases p21441_3 (m.d 1 2) (by simp) with h21473 | h21473
                              · rcases p21441_3 (m.d 1 3) (by simp) with h21474 | h21474
                                · rcases p21441_3 (m.d 1 4) (by simp) with h21475 | h21475
                                  · rcases p21441_3 (m.d 1 5) (by simp) with h21476 | h21476
                                    · linarith only [h21434, h21476, hlam]
                                    · linarith only [h17994, h21476, hlam]
                                  · linarith only [h21475, hlam, p21441_0]
                                · linarith only [h14799, h21474, hlam]
                              · linarith only [h0, h21473, hlam]
                          · have p21441_0 := h21441c.1
                            have p21441_1 := h21441c.2.1
                            have p21441_2 := h21441c.2.2.1
                            have p21441_3 := h21441c.2.2.2
                            linarith only [h21430, hlam, p21441_1]
                          · have p21441_0 := h21441c.1
                            have p21441_1 := h21441c.2.1
                            have p21441_2 := h21441c.2.2.1
                            have p21441_3 := h21441c.2.2.2
                            linarith only [h21432, hlam, p21441_0]
                          · have p21441_0 := h21441c.1
                            have p21441_1 := h21441c.2.1
                            have p21441_2 := h21441c.2.2.1
                            have p21441_3 := h21441c.2.2.2
                            linarith only [hlam, p21441_0]
                          · have p21441_0 := h21441c.1
                            have p21441_1 := h21441c.2.1
                            have p21441_2 := h21441c.2.2.1
                            have p21441_3 := h21441c.2.2.2
                            linarith only [h14799, h21259, h21433, hc01, hc14, hlam, hphi, p21441_1]
                          · have p21441_0 := h21441c.1
                            have p21441_1 := h21441c.2.1
                            have p21441_2 := h21441c.2.2.1
                            have p21441_3 := h21441c.2.2.2
                            rcases p21441_3 (m.d 0 1) (by simp) with h21486 | h21486
                            · linarith only [h21486, hlam, p21441_0]
                            · rcases p21441_3 (m.d 1 2) (by simp) with h21488 | h21488
                              · rcases p21441_3 (m.d 1 3) (by simp) with h21489 | h21489
                                · rcases p21441_3 (m.d 1 4) (by simp) with h21490 | h21490
                                  · rcases p21441_3 (m.d 1 5) (by simp) with h21491 | h21491
                                    · rcases h3bigk with h21492c | h21492c | h21492c | h21492c | h21492c | h21492c | h21492c | h21492c | h21492c | h21492c | h21492c | h21492c | h21492c | h21492c | h21492c | h21492c | h21492c | h21492c | h21492c | h21492c | h21492c | h21492c | h21492c | h21492c | h21492c
                                      · have p21492_0 := h21492c.1
                                        have p21492_1 := h21492c.2.1
                                        have p21492_2 := h21492c.2.2.1
                                        have p21492_3 := h21492c.2.2.2
                                        linarith only [hlam, p21492_0]
                                      · have p21492_0 := h21492c.1
                                        have p21492_1 := h21492c.2.1
                                        have p21492_2 := h21492c.2.2.1
                                        have p21492_3 := h21492c.2.2.2
                                        linarith only [h14799, hlam, p21492_1]
                                      · have p21492_0 := h21492c.1
                                        have p21492_1 := h21492c.2.1
                                        have p21492_2 := h21492c.2.2.1
                                        have p21492_3 := h21492c.2.2.2
                                        linarith only [h21259, h21440, hc23, hc34, hlam, hphi, p21492_1]
                                      · have p21492_0 := h21492c.1
                                        have p21492_1 := h21492c.2.1
                                        have p21492_2 := h21492c.2.2.1
                                        have p21492_3 := h21492c.2.2.2
                                        linarith only [h19113, hlam, p21492_0]
                                      · have p21492_0 := h21492c.1
                                        have p21492_1 := h21492c.2.1
                                        have p21492_2 := h21492c.2.2.1
                                        have p21492_3 := h21492c.2.2.2
                                        linarith only [h21259, hlam, p21492_0]
                                      · have p21492_0 := h21492c.1
                                        have p21492_1 := h21492c.2.1
                                        have p21492_2 := h21492c.2.2.1
                                        have p21492_3 := h21492c.2.2.2
                                        rcases p21492_3 (m.d 0 3) (by simp) with h21498 | h21498
                                        · linarith only [h14799, h21498, hlam]
                                        · rcases p21492_3 (m.d 1 3) (by simp) with h21500 | h21500
                                          · rcases p21492_3 (m.d 2 3) (by simp) with h21501 | h21501
                                            · linarith only [h21429, h21501, hlam]
                                            · rcases p21492_3 (m.d 3 4) (by simp) with h21503 | h21503
                                              · linarith only [h21432, h21503, hlam]
                                              · linarith only [h19113, h21503, hlam]
                                          · linarith only [h14799, h21500, hlam]
                                      · have p21492_0 := h21492c.1
                                        have p21492_1 := h21492c.2.1
                                        have p21492_2 := h21492c.2.2.1
                                        have p21492_3 := h21492c.2.2.2
                                        linarith only [hlam, p21492_0]
                                      · have p21492_0 := h21492c.1
                                        have p21492_1 := h21492c.2.1
                                        have p21492_2 := h21492c.2.2.1
                                        have p21492_3 := h21492c.2.2.2
                                        rcases p21492_3 (m.d 0 3) (by simp) with h21508 | h21508
                                        · linarith only [h14799, h21508, hlam]
                                        · linarith only [h19110, h21508, hlam]
                                      · have p21492_0 := h21492c.1
                                        have p21492_1 := h21492c.2.1
                                        have p21492_2 := h21492c.2.2.1
                                        have p21492_3 := h21492c.2.2.2
                                        linarith only [h14799, h21259, h21429, h21440, hc01, hc12, hlam, hphi, p21492_1]
                                      · have p21492_0 := h21492c.1
                                        have p21492_1 := h21492c.2.1
                                        have p21492_2 := h21492c.2.2.1
                                        have p21492_3 := h21492c.2.2.2
                                        linarith only [h14799, h21259, h21429, hc01, hc12, hlam, hphi, p21492_1]
                                      · have p21492_0 := h21492c.1
                                        have p21492_1 := h21492c.2.1
                                        have p21492_2 := h21492c.2.2.1
                                        have p21492_3 := h21492c.2.2.2
                                        linarith only [h19110, hlam, p21492_0]
                                      · have p21492_0 := h21492c.1
                                        have p21492_1 := h21492c.2.1
                                        have p21492_2 := h21492c.2.2.1
                                        have p21492_3 := h21492c.2.2.2
                                        linarith only [h21429, hlam, p21492_0]
                                      · have p21492_0 := h21492c.1
                                        have p21492_1 := h21492c.2.1
                                        have p21492_2 := h21492c.2.2.1
                                        have p21492_3 := h21492c.2.2.2
                                        linarith only [hlam, p21492_0]
                                      · have p21492_0 := h21492c.1
                                        have p21492_1 := h21492c.2.1
                                        have p21492_2 := h21492c.2.2.1
                                        have p21492_3 := h21492c.2.2.2
                                        linarith only [h21435, hlam, p21492_0]
                                      · have p21492_0 := h21492c.1
                                        have p21492_1 := h21492c.2.1
                                        have p21492_2 := h21492c.2.2.1
                                        have p21492_3 := h21492c.2.2.2
                                        linarith only [h21437, hlam, p21492_0]
                                      · have p21492_0 := h21492c.1
                                        have p21492_1 := h21492c.2.1
                                        have p21492_2 := h21492c.2.2.1
                                        have p21492_3 := h21492c.2.2.2
                                        linarith only [h14799, h21429, h21432, hc01, hc12, hlam, hphi, p21492_1]
                                      · have p21492_0 := h21492c.1
                                        have p21492_1 := h21492c.2.1
                                        have p21492_2 := h21492c.2.2.1
                                        have p21492_3 := h21492c.2.2.2
                                        linarith only [h21432, hlam, p21492_0]
                                      · have p21492_0 := h21492c.1
                                        have p21492_1 := h21492c.2.1
                                        have p21492_2 := h21492c.2.2.1
                                        have p21492_3 := h21492c.2.2.2
                                        rcases p21492_3 (m.d 0 3) (by simp) with h21520 | h21520
                                        · linarith only [h19113, h21520, hlam]
                                        · linarith only [h19110, h21520, hlam]
                                      · have p21492_0 := h21492c.1
                                        have p21492_1 := h21492c.2.1
                                        have p21492_2 := h21492c.2.2.1
                                        have p21492_3 := h21492c.2.2.2
                                        linarith only [hlam, p21492_0]
                                      · have p21492_0 := h21492c.1
                                        have p21492_1 := h21492c.2.1
                                        have p21492_2 := h21492c.2.2.1
                                        have p21492_3 := h21492c.2.2.2
                                        linarith only [h14799, h21259, h21429, h21432, hc01, hc12, hlam, hphi, p21492_1]
                                      · have p21492_0 := h21492c.1
                                        have p21492_1 := h21492c.2.1
                                        have p21492_2 := h21492c.2.2.1
                                        have p21492_3 := h21492c.2.2.2
                                        linarith only [h14799, h21429, h21433, hc01, hc12, hlam, hphi, p21492_1]
                                      · have p21492_0 := h21492c.1
                                        have p21492_1 := h21492c.2.1
                                        have p21492_2 := h21492c.2.2.1
                                        have p21492_3 := h21492c.2.2.2
                                        linarith only [h21433, hlam, p21492_0]
                                      · have p21492_0 := h21492c.1
                                        have p21492_1 := h21492c.2.1
                                        have p21492_2 := h21492c.2.2.1
                                        have p21492_3 := h21492c.2.2.2
                                        rcases p21492_3 (m.d 0 3) (by simp) with h21527 | h21527
                                        · linarith only [h21259, h21527, hlam]
                                        · linarith only [h19110, h21527, hlam]
                                      · have p21492_0 := h21492c.1
                                        have p21492_1 := h21492c.2.1
                                        have p21492_2 := h21492c.2.2.1
                                        have p21492_3 := h21492c.2.2.2
                                        linarith only [h21440, hlam, p21492_0]
                                      · have p21492_0 := h21492c.1
                                        have p21492_1 := h21492c.2.1
                                        have p21492_2 := h21492c.2.2.1
                                        have p21492_3 := h21492c.2.2.2
                                        linarith only [hlam, p21492_0]
                                    · linarith only [h21491, hlam, p21441_0]
                                  · linarith only [h16563, h21490, hlam]
                                · linarith only [h14799, h21489, hlam]
                              · linarith only [h0, h21488, hlam]
                          · have p21441_0 := h21441c.1
                            have p21441_1 := h21441c.2.1
                            have p21441_2 := h21441c.2.2.1
                            have p21441_3 := h21441c.2.2.2
                            linarith only [h21431, hlam, p21441_1]
                          · have p21441_0 := h21441c.1
                            have p21441_1 := h21441c.2.1
                            have p21441_2 := h21441c.2.2.1
                            have p21441_3 := h21441c.2.2.2
                            linarith only [h21433, hlam, p21441_0]
                          · have p21441_0 := h21441c.1
                            have p21441_1 := h21441c.2.1
                            have p21441_2 := h21441c.2.2.1
                            have p21441_3 := h21441c.2.2.2
                            linarith only [h21434, hlam, p21441_0]
                          · have p21441_0 := h21441c.1
                            have p21441_1 := h21441c.2.1
                            have p21441_2 := h21441c.2.2.1
                            have p21441_3 := h21441c.2.2.2
                            linarith only [hlam, p21441_0]
                        · linarith only [h14799, h16563, h19113, h21428, h21429, h21432, h21440, hc01, hc12, hlam, hphi]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h21541 | h21541
                        · rcases h1bigk with h21542c | h21542c | h21542c | h21542c | h21542c | h21542c | h21542c | h21542c | h21542c | h21542c | h21542c | h21542c | h21542c | h21542c | h21542c | h21542c | h21542c | h21542c | h21542c | h21542c | h21542c | h21542c | h21542c | h21542c | h21542c
                          · have p21542_0 := h21542c.1
                            have p21542_1 := h21542c.2.1
                            have p21542_2 := h21542c.2.2.1
                            have p21542_3 := h21542c.2.2.2
                            linarith only [hlam, p21542_0]
                          · have p21542_0 := h21542c.1
                            have p21542_1 := h21542c.2.1
                            have p21542_2 := h21542c.2.2.1
                            have p21542_3 := h21542c.2.2.2
                            linarith only [h0, hlam, p21542_0]
                          · have p21542_0 := h21542c.1
                            have p21542_1 := h21542c.2.1
                            have p21542_2 := h21542c.2.2.1
                            have p21542_3 := h21542c.2.2.2
                            linarith only [h14799, hlam, p21542_0]
                          · have p21542_0 := h21542c.1
                            have p21542_1 := h21542c.2.1
                            have p21542_2 := h21542c.2.2.1
                            have p21542_3 := h21542c.2.2.2
                            linarith only [h16563, hlam, p21542_0]
                          · have p21542_0 := h21542c.1
                            have p21542_1 := h21542c.2.1
                            have p21542_2 := h21542c.2.2.1
                            have p21542_3 := h21542c.2.2.2
                            linarith only [h17994, hlam, p21542_0]
                          · have p21542_0 := h21542c.1
                            have p21542_1 := h21542c.2.1
                            have p21542_2 := h21542c.2.2.1
                            have p21542_3 := h21542c.2.2.2
                            rcases p21542_3 (m.d 0 1) (by simp) with h21548 | h21548
                            · linarith only [h21548, hlam, p21542_0]
                            · rcases p21542_3 (m.d 1 2) (by simp) with h21550 | h21550
                              · rcases p21542_3 (m.d 1 3) (by simp) with h21551 | h21551
                                · linarith only [h21429, h21551, hlam]
                                · linarith only [h14799, h21551, hlam]
                              · linarith only [h21550, hlam, p21542_0]
                          · have p21542_0 := h21542c.1
                            have p21542_1 := h21542c.2.1
                            have p21542_2 := h21542c.2.2.1
                            have p21542_3 := h21542c.2.2.2
                            linarith only [hlam, p21542_0]
                          · have p21542_0 := h21542c.1
                            have p21542_1 := h21542c.2.1
                            have p21542_2 := h21542c.2.2.1
                            have p21542_3 := h21542c.2.2.2
                            linarith only [h14799, hc01, hc12, hlam, hphi, p21542_1]
                          · have p21542_0 := h21542c.1
                            have p21542_1 := h21542c.2.1
                            have p21542_2 := h21542c.2.2.1
                            have p21542_3 := h21542c.2.2.2
                            linarith only [h16563, h21428, h21435, h21439, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p21542_1]
                          · have p21542_0 := h21542c.1
                            have p21542_1 := h21542c.2.1
                            have p21542_2 := h21542c.2.2.1
                            have p21542_3 := h21542c.2.2.2
                            linarith only [h17994, hc01, hc12, hlam, hphi, p21542_1]
                          · have p21542_0 := h21542c.1
                            have p21542_1 := h21542c.2.1
                            have p21542_2 := h21542c.2.2.1
                            have p21542_3 := h21542c.2.2.2
                            rcases p21542_3 (m.d 0 1) (by simp) with h21559 | h21559
                            · linarith only [h21559, hlam, p21542_0]
                            · rcases p21542_3 (m.d 1 2) (by simp) with h21561 | h21561
                              · rcases p21542_3 (m.d 1 3) (by simp) with h21562 | h21562
                                · rcases p21542_3 (m.d 1 4) (by simp) with h21563 | h21563
                                  · linarith only [h21432, h21563, hlam]
                                  · linarith only [h16563, h21563, hlam]
                                · linarith only [h21562, hlam, p21542_0]
                              · linarith only [h0, h21561, hlam]
                          · have p21542_0 := h21542c.1
                            have p21542_1 := h21542c.2.1
                            have p21542_2 := h21542c.2.2.1
                            have p21542_3 := h21542c.2.2.2
                            linarith only [h21429, hlam, p21542_1]
                          · have p21542_0 := h21542c.1
                            have p21542_1 := h21542c.2.1
                            have p21542_2 := h21542c.2.2.1
                            have p21542_3 := h21542c.2.2.2
                            linarith only [hlam, p21542_0]
                          · have p21542_0 := h21542c.1
                            have p21542_1 := h21542c.2.1
                            have p21542_2 := h21542c.2.2.1
                            have p21542_3 := h21542c.2.2.2
                            linarith only [h19113, h21428, h21432, h21435, h21439, hc13, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p21542_1]
                          · have p21542_0 := h21542c.1
                            have p21542_1 := h21542c.2.1
                            have p21542_2 := h21542c.2.2.1
                            have p21542_3 := h21542c.2.2.2
                            linarith only [h14799, h21259, h21429, h21433, hc01, hc12, hlam, hphi, p21542_1]
                          · have p21542_0 := h21542c.1
                            have p21542_1 := h21542c.2.1
                            have p21542_2 := h21542c.2.2.1
                            have p21542_3 := h21542c.2.2.2
                            rcases p21542_3 (m.d 0 1) (by simp) with h21572 | h21572
                            · linarith only [h21572, hlam, p21542_0]
                            · rcases p21542_3 (m.d 1 2) (by simp) with h21574 | h21574
                              · rcases p21542_3 (m.d 1 3) (by simp) with h21575 | h21575
                                · rcases p21542_3 (m.d 1 4) (by simp) with h21576 | h21576
                                  · rcases p21542_3 (m.d 1 5) (by simp) with h21577 | h21577
                                    · linarith only [h21434, h21577, hlam]
                                    · linarith only [h17994, h21577, hlam]
                                  · linarith only [h21576, hlam, p21542_0]
                                · linarith only [h14799, h21575, hlam]
                              · linarith only [h0, h21574, hlam]
                          · have p21542_0 := h21542c.1
                            have p21542_1 := h21542c.2.1
                            have p21542_2 := h21542c.2.2.1
                            have p21542_3 := h21542c.2.2.2
                            linarith only [h21430, hlam, p21542_1]
                          · have p21542_0 := h21542c.1
                            have p21542_1 := h21542c.2.1
                            have p21542_2 := h21542c.2.2.1
                            have p21542_3 := h21542c.2.2.2
                            linarith only [h21432, hlam, p21542_0]
                          · have p21542_0 := h21542c.1
                            have p21542_1 := h21542c.2.1
                            have p21542_2 := h21542c.2.2.1
                            have p21542_3 := h21542c.2.2.2
                            linarith only [hlam, p21542_0]
                          · have p21542_0 := h21542c.1
                            have p21542_1 := h21542c.2.1
                            have p21542_2 := h21542c.2.2.1
                            have p21542_3 := h21542c.2.2.2
                            linarith only [h14799, h21259, h21433, hc01, hc14, hlam, hphi, p21542_1]
                          · have p21542_0 := h21542c.1
                            have p21542_1 := h21542c.2.1
                            have p21542_2 := h21542c.2.2.1
                            have p21542_3 := h21542c.2.2.2
                            rcases p21542_3 (m.d 0 1) (by simp) with h21587 | h21587
                            · linarith only [h21587, hlam, p21542_0]
                            · rcases p21542_3 (m.d 1 2) (by simp) with h21589 | h21589
                              · rcases p21542_3 (m.d 1 3) (by simp) with h21590 | h21590
                                · rcases p21542_3 (m.d 1 4) (by simp) with h21591 | h21591
                                  · rcases p21542_3 (m.d 1 5) (by simp) with h21592 | h21592
                                    · rcases h3bigk with h21593c | h21593c | h21593c | h21593c | h21593c | h21593c | h21593c | h21593c | h21593c | h21593c | h21593c | h21593c | h21593c | h21593c | h21593c | h21593c | h21593c | h21593c | h21593c | h21593c | h21593c | h21593c | h21593c | h21593c | h21593c
                                      · have p21593_0 := h21593c.1
                                        have p21593_1 := h21593c.2.1
                                        have p21593_2 := h21593c.2.2.1
                                        have p21593_3 := h21593c.2.2.2
                                        linarith only [hlam, p21593_0]
                                      · have p21593_0 := h21593c.1
                                        have p21593_1 := h21593c.2.1
                                        have p21593_2 := h21593c.2.2.1
                                        have p21593_3 := h21593c.2.2.2
                                        linarith only [h14799, hlam, p21593_1]
                                      · have p21593_0 := h21593c.1
                                        have p21593_1 := h21593c.2.1
                                        have p21593_2 := h21593c.2.2.1
                                        have p21593_3 := h21593c.2.2.2
                                        linarith only [h21259, hc23, hc35, hlam, hphi, p21593_1]
                                      · have p21593_0 := h21593c.1
                                        have p21593_1 := h21593c.2.1
                                        have p21593_2 := h21593c.2.2.1
                                        have p21593_3 := h21593c.2.2.2
                                        linarith only [h19113, hlam, p21593_0]
                                      · have p21593_0 := h21593c.1
                                        have p21593_1 := h21593c.2.1
                                        have p21593_2 := h21593c.2.2.1
                                        have p21593_3 := h21593c.2.2.2
                                        linarith only [h21259, hlam, p21593_0]
                                      · have p21593_0 := h21593c.1
                                        have p21593_1 := h21593c.2.1
                                        have p21593_2 := h21593c.2.2.1
                                        have p21593_3 := h21593c.2.2.2
                                        rcases p21593_3 (m.d 0 3) (by simp) with h21599 | h21599
                                        · linarith only [h14799, h21599, hlam]
                                        · rcases p21593_3 (m.d 1 3) (by simp) with h21601 | h21601
                                          · rcases p21593_3 (m.d 2 3) (by simp) with h21602 | h21602
                                            · linarith only [h21429, h21602, hlam]
                                            · rcases p21593_3 (m.d 3 4) (by simp) with h21604 | h21604
                                              · linarith only [h21432, h21604, hlam]
                                              · linarith only [h19113, h21604, hlam]
                                          · linarith only [h14799, h21601, hlam]
                                      · have p21593_0 := h21593c.1
                                        have p21593_1 := h21593c.2.1
                                        have p21593_2 := h21593c.2.2.1
                                        have p21593_3 := h21593c.2.2.2
                                        linarith only [hlam, p21593_0]
                                      · have p21593_0 := h21593c.1
                                        have p21593_1 := h21593c.2.1
                                        have p21593_2 := h21593c.2.2.1
                                        have p21593_3 := h21593c.2.2.2
                                        linarith only [h19113, h21428, h21432, h21435, h21439, hlam, p21593_2]
                                      · have p21593_0 := h21593c.1
                                        have p21593_1 := h21593c.2.1
                                        have p21593_2 := h21593c.2.2.1
                                        have p21593_3 := h21593c.2.2.2
                                        linarith only [h14799, h21259, h21429, h21541, hc01, hc12, hlam, hphi, p21593_1]
                                      · have p21593_0 := h21593c.1
                                        have p21593_1 := h21593c.2.1
                                        have p21593_2 := h21593c.2.2.1
                                        have p21593_3 := h21593c.2.2.2
                                        linarith only [h14799, h21259, h21429, hc01, hc12, hlam, hphi, p21593_1]
                                      · have p21593_0 := h21593c.1
                                        have p21593_1 := h21593c.2.1
                                        have p21593_2 := h21593c.2.2.1
                                        have p21593_3 := h21593c.2.2.2
                                        linarith only [h19110, hlam, p21593_0]
                                      · have p21593_0 := h21593c.1
                                        have p21593_1 := h21593c.2.1
                                        have p21593_2 := h21593c.2.2.1
                                        have p21593_3 := h21593c.2.2.2
                                        linarith only [h21429, hlam, p21593_0]
                                      · have p21593_0 := h21593c.1
                                        have p21593_1 := h21593c.2.1
                                        have p21593_2 := h21593c.2.2.1
                                        have p21593_3 := h21593c.2.2.2
                                        linarith only [hlam, p21593_0]
                                      · have p21593_0 := h21593c.1
                                        have p21593_1 := h21593c.2.1
                                        have p21593_2 := h21593c.2.2.1
                                        have p21593_3 := h21593c.2.2.2
                                        linarith only [h21435, hlam, p21593_0]
                                      · have p21593_0 := h21593c.1
                                        have p21593_1 := h21593c.2.1
                                        have p21593_2 := h21593c.2.2.1
                                        have p21593_3 := h21593c.2.2.2
                                        linarith only [h21437, hlam, p21593_0]
                                      · have p21593_0 := h21593c.1
                                        have p21593_1 := h21593c.2.1
                                        have p21593_2 := h21593c.2.2.1
                                        have p21593_3 := h21593c.2.2.2
                                        linarith only [h14799, h21429, h21432, hc01, hc12, hlam, hphi, p21593_1]
                                      · have p21593_0 := h21593c.1
                                        have p21593_1 := h21593c.2.1
                                        have p21593_2 := h21593c.2.2.1
                                        have p21593_3 := h21593c.2.2.2
                                        linarith only [h21432, hlam, p21593_0]
                                      · have p21593_0 := h21593c.1
                                        have p21593_1 := h21593c.2.1
                                        have p21593_2 := h21593c.2.2.1
                                        have p21593_3 := h21593c.2.2.2
                                        rcases p21593_3 (m.d 0 3) (by simp) with h21619 | h21619
                                        · linarith only [h19113, h21619, hlam]
                                        · linarith only [h19110, h21619, hlam]
                                      · have p21593_0 := h21593c.1
                                        have p21593_1 := h21593c.2.1
                                        have p21593_2 := h21593c.2.2.1
                                        have p21593_3 := h21593c.2.2.2
                                        linarith only [hlam, p21593_0]
                                      · have p21593_0 := h21593c.1
                                        have p21593_1 := h21593c.2.1
                                        have p21593_2 := h21593c.2.2.1
                                        have p21593_3 := h21593c.2.2.2
                                        linarith only [h14799, h21259, h21429, h21432, hc01, hc12, hlam, hphi, p21593_1]
                                      · have p21593_0 := h21593c.1
                                        have p21593_1 := h21593c.2.1
                                        have p21593_2 := h21593c.2.2.1
                                        have p21593_3 := h21593c.2.2.2
                                        linarith only [h14799, h21429, h21433, hc01, hc12, hlam, hphi, p21593_1]
                                      · have p21593_0 := h21593c.1
                                        have p21593_1 := h21593c.2.1
                                        have p21593_2 := h21593c.2.2.1
                                        have p21593_3 := h21593c.2.2.2
                                        linarith only [h21433, hlam, p21593_0]
                                      · have p21593_0 := h21593c.1
                                        have p21593_1 := h21593c.2.1
                                        have p21593_2 := h21593c.2.2.1
                                        have p21593_3 := h21593c.2.2.2
                                        rcases p21593_3 (m.d 0 3) (by simp) with h21626 | h21626
                                        · linarith only [h21259, h21626, hlam]
                                        · linarith only [h19110, h21626, hlam]
                                      · have p21593_0 := h21593c.1
                                        have p21593_1 := h21593c.2.1
                                        have p21593_2 := h21593c.2.2.1
                                        have p21593_3 := h21593c.2.2.2
                                        linarith only [h21541, hlam, p21593_0]
                                      · have p21593_0 := h21593c.1
                                        have p21593_1 := h21593c.2.1
                                        have p21593_2 := h21593c.2.2.1
                                        have p21593_3 := h21593c.2.2.2
                                        linarith only [hlam, p21593_0]
                                    · linarith only [h21592, hlam, p21542_0]
                                  · linarith only [h16563, h21591, hlam]
                                · linarith only [h14799, h21590, hlam]
                              · linarith only [h0, h21589, hlam]
                          · have p21542_0 := h21542c.1
                            have p21542_1 := h21542c.2.1
                            have p21542_2 := h21542c.2.2.1
                            have p21542_3 := h21542c.2.2.2
                            linarith only [h21431, hlam, p21542_1]
                          · have p21542_0 := h21542c.1
                            have p21542_1 := h21542c.2.1
                            have p21542_2 := h21542c.2.2.1
                            have p21542_3 := h21542c.2.2.2
                            linarith only [h21433, hlam, p21542_0]
                          · have p21542_0 := h21542c.1
                            have p21542_1 := h21542c.2.1
                            have p21542_2 := h21542c.2.2.1
                            have p21542_3 := h21542c.2.2.2
                            linarith only [h21434, hlam, p21542_0]
                          · have p21542_0 := h21542c.1
                            have p21542_1 := h21542c.2.1
                            have p21542_2 := h21542c.2.2.1
                            have p21542_3 := h21542c.2.2.2
                            linarith only [hlam, p21542_0]
                        · linarith only [h19113, h21428, h21541, hlam]
                · linarith only [h16563, h19113, h21428, h21429, h21432, h21434, hc01, hc12, hlam, hphi]
              · linarith only [h14799, h19113, h21432, h21433, hc01, hc35, hlam, hphi, ht12, ht23]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h21642 | h21642
              · linarith only [h14799, h21259, h21432, h21642, hc01, hc34, hlam, hphi, ht12, ht23]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h21644 | h21644
                · rcases m.htr 2 3 4 (by decide) (by decide) with h21645 | h21645
                  · linarith only [h14799, h21432, h21645, hc01, hc23, hlam, hphi, ht12]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h21647 | h21647
                    · linarith only [h14799, h19111, h21642, h21645, h21647, hc01, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h21649 | h21649
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h21650 | h21650
                        · rcases h1bigk with h21651c | h21651c | h21651c | h21651c | h21651c | h21651c | h21651c | h21651c | h21651c | h21651c | h21651c | h21651c | h21651c | h21651c | h21651c | h21651c | h21651c | h21651c | h21651c | h21651c | h21651c | h21651c | h21651c | h21651c | h21651c
                          · have p21651_0 := h21651c.1
                            have p21651_1 := h21651c.2.1
                            have p21651_2 := h21651c.2.2.1
                            have p21651_3 := h21651c.2.2.2
                            linarith only [hlam, p21651_0]
                          · have p21651_0 := h21651c.1
                            have p21651_1 := h21651c.2.1
                            have p21651_2 := h21651c.2.2.1
                            have p21651_3 := h21651c.2.2.2
                            linarith only [h0, hlam, p21651_0]
                          · have p21651_0 := h21651c.1
                            have p21651_1 := h21651c.2.1
                            have p21651_2 := h21651c.2.2.1
                            have p21651_3 := h21651c.2.2.2
                            linarith only [h14799, hlam, p21651_0]
                          · have p21651_0 := h21651c.1
                            have p21651_1 := h21651c.2.1
                            have p21651_2 := h21651c.2.2.1
                            have p21651_3 := h21651c.2.2.2
                            linarith only [h16563, hlam, p21651_0]
                          · have p21651_0 := h21651c.1
                            have p21651_1 := h21651c.2.1
                            have p21651_2 := h21651c.2.2.1
                            have p21651_3 := h21651c.2.2.2
                            linarith only [h17994, hlam, p21651_0]
                          · have p21651_0 := h21651c.1
                            have p21651_1 := h21651c.2.1
                            have p21651_2 := h21651c.2.2.1
                            have p21651_3 := h21651c.2.2.2
                            rcases p21651_3 (m.d 0 1) (by simp) with h21657 | h21657
                            · linarith only [h21657, hlam, p21651_0]
                            · rcases p21651_3 (m.d 1 2) (by simp) with h21659 | h21659
                              · rcases p21651_3 (m.d 1 3) (by simp) with h21660 | h21660
                                · linarith only [h21429, h21660, hlam]
                                · linarith only [h14799, h21660, hlam]
                              · linarith only [h21659, hlam, p21651_0]
                          · have p21651_0 := h21651c.1
                            have p21651_1 := h21651c.2.1
                            have p21651_2 := h21651c.2.2.1
                            have p21651_3 := h21651c.2.2.2
                            linarith only [hlam, p21651_0]
                          · have p21651_0 := h21651c.1
                            have p21651_1 := h21651c.2.1
                            have p21651_2 := h21651c.2.2.1
                            have p21651_3 := h21651c.2.2.2
                            linarith only [h14799, hc01, hc12, hlam, hphi, p21651_1]
                          · have p21651_0 := h21651c.1
                            have p21651_1 := h21651c.2.1
                            have p21651_2 := h21651c.2.2.1
                            have p21651_3 := h21651c.2.2.2
                            linarith only [h16563, hc01, hc12, hlam, hphi, p21651_1]
                          · have p21651_0 := h21651c.1
                            have p21651_1 := h21651c.2.1
                            have p21651_2 := h21651c.2.2.1
                            have p21651_3 := h21651c.2.2.2
                            linarith only [h17994, hc01, hc12, hlam, hphi, p21651_1]
                          · have p21651_0 := h21651c.1
                            have p21651_1 := h21651c.2.1
                            have p21651_2 := h21651c.2.2.1
                            have p21651_3 := h21651c.2.2.2
                            linarith only [h21432, hc01, hc34, hlam, hphi, ht12, ht23, p21651_1]
                          · have p21651_0 := h21651c.1
                            have p21651_1 := h21651c.2.1
                            have p21651_2 := h21651c.2.2.1
                            have p21651_3 := h21651c.2.2.2
                            linarith only [h21429, hlam, p21651_1]
                          · have p21651_0 := h21651c.1
                            have p21651_1 := h21651c.2.1
                            have p21651_2 := h21651c.2.2.1
                            have p21651_3 := h21651c.2.2.2
                            linarith only [hlam, p21651_0]
                          · have p21651_0 := h21651c.1
                            have p21651_1 := h21651c.2.1
                            have p21651_2 := h21651c.2.2.1
                            have p21651_3 := h21651c.2.2.2
                            linarith only [h21432, hlam, p21651_1]
                          · have p21651_0 := h21651c.1
                            have p21651_1 := h21651c.2.1
                            have p21651_2 := h21651c.2.2.1
                            have p21651_3 := h21651c.2.2.2
                            linarith only [h21642, hlam, p21651_1]
                          · have p21651_0 := h21651c.1
                            have p21651_1 := h21651c.2.1
                            have p21651_2 := h21651c.2.2.1
                            have p21651_3 := h21651c.2.2.2
                            rcases p21651_3 (m.d 0 1) (by simp) with h21673 | h21673
                            · linarith only [h21673, hlam, p21651_0]
                            · rcases p21651_3 (m.d 1 2) (by simp) with h21675 | h21675
                              · rcases p21651_3 (m.d 1 3) (by simp) with h21676 | h21676
                                · linarith only [h21432, h21676, hlam]
                                · linarith only [h14799, h21676, hlam]
                              · linarith only [h0, h21675, hlam]
                          · have p21651_0 := h21651c.1
                            have p21651_1 := h21651c.2.1
                            have p21651_2 := h21651c.2.2.1
                            have p21651_3 := h21651c.2.2.2
                            linarith only [h21430, hlam, p21651_1]
                          · have p21651_0 := h21651c.1
                            have p21651_1 := h21651c.2.1
                            have p21651_2 := h21651c.2.2.1
                            have p21651_3 := h21651c.2.2.2
                            linarith only [h14799, hc01, hc14, hlam, hphi, p21651_1]
                          · have p21651_0 := h21651c.1
                            have p21651_1 := h21651c.2.1
                            have p21651_2 := h21651c.2.2.1
                            have p21651_3 := h21651c.2.2.2
                            linarith only [hlam, p21651_0]
                          · have p21651_0 := h21651c.1
                            have p21651_1 := h21651c.2.1
                            have p21651_2 := h21651c.2.2.1
                            have p21651_3 := h21651c.2.2.2
                            linarith only [h14799, h21432, h21642, hc01, hc34, hlam, hphi, ht12, ht23, p21651_1]
                          · have p21651_0 := h21651c.1
                            have p21651_1 := h21651c.2.1
                            have p21651_2 := h21651c.2.2.1
                            have p21651_3 := h21651c.2.2.2
                            rcases p21651_3 (m.d 0 1) (by simp) with h21684 | h21684
                            · linarith only [h21684, hlam, p21651_0]
                            · rcases p21651_3 (m.d 1 2) (by simp) with h21686 | h21686
                              · rcases p21651_3 (m.d 1 3) (by simp) with h21687 | h21687
                                · linarith only [h21642, h21687, hlam]
                                · linarith only [h14799, h21687, hlam]
                              · linarith only [h0, h21686, hlam]
                          · have p21651_0 := h21651c.1
                            have p21651_1 := h21651c.2.1
                            have p21651_2 := h21651c.2.2.1
                            have p21651_3 := h21651c.2.2.2
                            linarith only [h21431, hlam, p21651_1]
                          · have p21651_0 := h21651c.1
                            have p21651_1 := h21651c.2.1
                            have p21651_2 := h21651c.2.2.1
                            have p21651_3 := h21651c.2.2.2
                            linarith only [h14799, hc01, hc15, hlam, hphi, p21651_1]
                          · have p21651_0 := h21651c.1
                            have p21651_1 := h21651c.2.1
                            have p21651_2 := h21651c.2.2.1
                            have p21651_3 := h21651c.2.2.2
                            linarith only [h21644, hlam, p21651_0]
                          · have p21651_0 := h21651c.1
                            have p21651_1 := h21651c.2.1
                            have p21651_2 := h21651c.2.2.1
                            have p21651_3 := h21651c.2.2.2
                            linarith only [hlam, p21651_0]
                        · linarith only [h0, h16563, h19111, h21432, h21649, h21650, hc01, hc12, hlam, hphi]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h21696 | h21696
                        · rcases h1bigk with h21697c | h21697c | h21697c | h21697c | h21697c | h21697c | h21697c | h21697c | h21697c | h21697c | h21697c | h21697c | h21697c | h21697c | h21697c | h21697c | h21697c | h21697c | h21697c | h21697c | h21697c | h21697c | h21697c | h21697c | h21697c
                          · have p21697_0 := h21697c.1
                            have p21697_1 := h21697c.2.1
                            have p21697_2 := h21697c.2.2.1
                            have p21697_3 := h21697c.2.2.2
                            linarith only [hlam, p21697_0]
                          · have p21697_0 := h21697c.1
                            have p21697_1 := h21697c.2.1
                            have p21697_2 := h21697c.2.2.1
                            have p21697_3 := h21697c.2.2.2
                            linarith only [h0, hlam, p21697_0]
                          · have p21697_0 := h21697c.1
                            have p21697_1 := h21697c.2.1
                            have p21697_2 := h21697c.2.2.1
                            have p21697_3 := h21697c.2.2.2
                            linarith only [h14799, hlam, p21697_0]
                          · have p21697_0 := h21697c.1
                            have p21697_1 := h21697c.2.1
                            have p21697_2 := h21697c.2.2.1
                            have p21697_3 := h21697c.2.2.2
                            linarith only [h16563, hlam, p21697_0]
                          · have p21697_0 := h21697c.1
                            have p21697_1 := h21697c.2.1
                            have p21697_2 := h21697c.2.2.1
                            have p21697_3 := h21697c.2.2.2
                            linarith only [h17994, hlam, p21697_0]
                          · have p21697_0 := h21697c.1
                            have p21697_1 := h21697c.2.1
                            have p21697_2 := h21697c.2.2.1
                            have p21697_3 := h21697c.2.2.2
                            rcases p21697_3 (m.d 0 1) (by simp) with h21703 | h21703
                            · linarith only [h21703, hlam, p21697_0]
                            · rcases p21697_3 (m.d 1 2) (by simp) with h21705 | h21705
                              · rcases p21697_3 (m.d 1 3) (by simp) with h21706 | h21706
                                · linarith only [h21429, h21706, hlam]
                                · linarith only [h14799, h21706, hlam]
                              · linarith only [h21705, hlam, p21697_0]
                          · have p21697_0 := h21697c.1
                            have p21697_1 := h21697c.2.1
                            have p21697_2 := h21697c.2.2.1
                            have p21697_3 := h21697c.2.2.2
                            linarith only [hlam, p21697_0]
                          · have p21697_0 := h21697c.1
                            have p21697_1 := h21697c.2.1
                            have p21697_2 := h21697c.2.2.1
                            have p21697_3 := h21697c.2.2.2
                            linarith only [h14799, hc01, hc12, hlam, hphi, p21697_1]
                          · have p21697_0 := h21697c.1
                            have p21697_1 := h21697c.2.1
                            have p21697_2 := h21697c.2.2.1
                            have p21697_3 := h21697c.2.2.2
                            linarith only [h16563, h21428, h21645, h21649, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p21697_1]
                          · have p21697_0 := h21697c.1
                            have p21697_1 := h21697c.2.1
                            have p21697_2 := h21697c.2.2.1
                            have p21697_3 := h21697c.2.2.2
                            linarith only [h14799, h21642, hc01, hc12, hlam, hphi, p21697_1]
                          · have p21697_0 := h21697c.1
                            have p21697_1 := h21697c.2.1
                            have p21697_2 := h21697c.2.2.1
                            have p21697_3 := h21697c.2.2.2
                            linarith only [h21642, h21696, hc01, hc34, hlam, hphi, ht12, ht23, p21697_1]
                          · have p21697_0 := h21697c.1
                            have p21697_1 := h21697c.2.1
                            have p21697_2 := h21697c.2.2.1
                            have p21697_3 := h21697c.2.2.2
                            linarith only [h21429, hlam, p21697_1]
                          · have p21697_0 := h21697c.1
                            have p21697_1 := h21697c.2.1
                            have p21697_2 := h21697c.2.2.1
                            have p21697_3 := h21697c.2.2.2
                            linarith only [hlam, p21697_0]
                          · have p21697_0 := h21697c.1
                            have p21697_1 := h21697c.2.1
                            have p21697_2 := h21697c.2.2.1
                            have p21697_3 := h21697c.2.2.2
                            linarith only [h21432, hlam, p21697_1]
                          · have p21697_0 := h21697c.1
                            have p21697_1 := h21697c.2.1
                            have p21697_2 := h21697c.2.2.1
                            have p21697_3 := h21697c.2.2.2
                            linarith only [h21642, hlam, p21697_1]
                          · have p21697_0 := h21697c.1
                            have p21697_1 := h21697c.2.1
                            have p21697_2 := h21697c.2.2.1
                            have p21697_3 := h21697c.2.2.2
                            rcases p21697_3 (m.d 0 1) (by simp) with h21719 | h21719
                            · linarith only [h21719, hlam, p21697_0]
                            · rcases p21697_3 (m.d 1 2) (by simp) with h21721 | h21721
                              · rcases p21697_3 (m.d 1 3) (by simp) with h21722 | h21722
                                · linarith only [h21432, h21722, hlam]
                                · linarith only [h14799, h21722, hlam]
                              · linarith only [h0, h21721, hlam]
                          · have p21697_0 := h21697c.1
                            have p21697_1 := h21697c.2.1
                            have p21697_2 := h21697c.2.2.1
                            have p21697_3 := h21697c.2.2.2
                            linarith only [h21430, hlam, p21697_1]
                          · have p21697_0 := h21697c.1
                            have p21697_1 := h21697c.2.1
                            have p21697_2 := h21697c.2.2.1
                            have p21697_3 := h21697c.2.2.2
                            linarith only [h14799, hc01, hc14, hlam, hphi, p21697_1]
                          · have p21697_0 := h21697c.1
                            have p21697_1 := h21697c.2.1
                            have p21697_2 := h21697c.2.2.1
                            have p21697_3 := h21697c.2.2.2
                            linarith only [hlam, p21697_0]
                          · have p21697_0 := h21697c.1
                            have p21697_1 := h21697c.2.1
                            have p21697_2 := h21697c.2.2.1
                            have p21697_3 := h21697c.2.2.2
                            linarith only [h14799, h21432, h21642, hc01, hc34, hlam, hphi, ht12, ht23, p21697_1]
                          · have p21697_0 := h21697c.1
                            have p21697_1 := h21697c.2.1
                            have p21697_2 := h21697c.2.2.1
                            have p21697_3 := h21697c.2.2.2
                            rcases p21697_3 (m.d 0 1) (by simp) with h21730 | h21730
                            · linarith only [h21730, hlam, p21697_0]
                            · rcases p21697_3 (m.d 1 2) (by simp) with h21732 | h21732
                              · rcases p21697_3 (m.d 1 3) (by simp) with h21733 | h21733
                                · linarith only [h21642, h21733, hlam]
                                · linarith only [h14799, h21733, hlam]
                              · linarith only [h0, h21732, hlam]
                          · have p21697_0 := h21697c.1
                            have p21697_1 := h21697c.2.1
                            have p21697_2 := h21697c.2.2.1
                            have p21697_3 := h21697c.2.2.2
                            linarith only [h21431, hlam, p21697_1]
                          · have p21697_0 := h21697c.1
                            have p21697_1 := h21697c.2.1
                            have p21697_2 := h21697c.2.2.1
                            have p21697_3 := h21697c.2.2.2
                            linarith only [h14799, hc01, hc15, hlam, hphi, p21697_1]
                          · have p21697_0 := h21697c.1
                            have p21697_1 := h21697c.2.1
                            have p21697_2 := h21697c.2.2.1
                            have p21697_3 := h21697c.2.2.2
                            linarith only [h21644, hlam, p21697_0]
                          · have p21697_0 := h21697c.1
                            have p21697_1 := h21697c.2.1
                            have p21697_2 := h21697c.2.2.1
                            have p21697_3 := h21697c.2.2.2
                            linarith only [hlam, p21697_0]
                        · linarith only [h16563, h21428, h21432, h21696, hlam]
                · linarith only [h16563, h21428, h21644, hlam]
          · linarith only [h0, h19112, h21431, hlam]
        · linarith only [h0, h19111, h21430, hlam]
      · linarith only [h0, h19110, h21429, hlam]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h21746 | h21746
      · rcases m.htr 1 2 4 (by decide) (by decide) with h21747 | h21747
        · rcases m.htr 1 2 5 (by decide) (by decide) with h21748 | h21748
          · rcases m.htr 1 3 4 (by decide) (by decide) with h21749 | h21749
            · rcases m.htr 1 3 5 (by decide) (by decide) with h21750 | h21750
              · rcases m.htr 1 4 5 (by decide) (by decide) with h21751 | h21751
                · rcases m.htr 2 3 4 (by decide) (by decide) with h21752 | h21752
                  · linarith only [h19110, h19113, h21752, hlam]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h21754 | h21754
                    · linarith only [h17994, h19110, h19113, h21259, h21428, h21746, h21749, h21751, h21754, hc01, hc12, hlam, hphi]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h21756 | h21756
                      · linarith only [h19111, h21428, h21756, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h21758 | h21758
                        · linarith only [h14799, h19113, h21428, h21746, h21749, h21758, hc01, hc12, hlam, hphi]
                        · linarith only [h14799, h19113, h21746, h21749, h21751, h21758, hc01, hc12, hlam, hphi]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h21761 | h21761
                  · linarith only [h19110, h19113, h21761, hlam]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h21763 | h21763
                    · linarith only [h19110, h21259, h21763, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h21765 | h21765
                      · linarith only [h16563, h21751, h21765, hc01, hc24, hlam, hphi, ht12]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h21767 | h21767
                        · linarith only [h21749, h21751, h21767, hlam]
                        · rcases h1bigk with h21769c | h21769c | h21769c | h21769c | h21769c | h21769c | h21769c | h21769c | h21769c | h21769c | h21769c | h21769c | h21769c | h21769c | h21769c | h21769c | h21769c | h21769c | h21769c | h21769c | h21769c | h21769c | h21769c | h21769c | h21769c
                          · have p21769_0 := h21769c.1
                            have p21769_1 := h21769c.2.1
                            have p21769_2 := h21769c.2.2.1
                            have p21769_3 := h21769c.2.2.2
                            linarith only [hlam, p21769_0]
                          · have p21769_0 := h21769c.1
                            have p21769_1 := h21769c.2.1
                            have p21769_2 := h21769c.2.2.1
                            have p21769_3 := h21769c.2.2.2
                            linarith only [h0, hlam, p21769_0]
                          · have p21769_0 := h21769c.1
                            have p21769_1 := h21769c.2.1
                            have p21769_2 := h21769c.2.2.1
                            have p21769_3 := h21769c.2.2.2
                            linarith only [h14799, hlam, p21769_0]
                          · have p21769_0 := h21769c.1
                            have p21769_1 := h21769c.2.1
                            have p21769_2 := h21769c.2.2.1
                            have p21769_3 := h21769c.2.2.2
                            linarith only [h16563, hlam, p21769_0]
                          · have p21769_0 := h21769c.1
                            have p21769_1 := h21769c.2.1
                            have p21769_2 := h21769c.2.2.1
                            have p21769_3 := h21769c.2.2.2
                            linarith only [h17994, hlam, p21769_0]
                          · have p21769_0 := h21769c.1
                            have p21769_1 := h21769c.2.1
                            have p21769_2 := h21769c.2.2.1
                            have p21769_3 := h21769c.2.2.2
                            rcases p21769_3 (m.d 0 1) (by simp) with h21775 | h21775
                            · linarith only [h21775, hlam, p21769_0]
                            · rcases p21769_3 (m.d 1 2) (by simp) with h21777 | h21777
                              · rcases p21769_3 (m.d 1 3) (by simp) with h21778 | h21778
                                · linarith only [h21746, h21778, hlam]
                                · linarith only [h14799, h21778, hlam]
                              · linarith only [h21777, hlam, p21769_0]
                          · have p21769_0 := h21769c.1
                            have p21769_1 := h21769c.2.1
                            have p21769_2 := h21769c.2.2.1
                            have p21769_3 := h21769c.2.2.2
                            linarith only [hlam, p21769_0]
                          · have p21769_0 := h21769c.1
                            have p21769_1 := h21769c.2.1
                            have p21769_2 := h21769c.2.2.1
                            have p21769_3 := h21769c.2.2.2
                            linarith only [h14799, hc01, hc12, hlam, hphi, p21769_1]
                          · have p21769_0 := h21769c.1
                            have p21769_1 := h21769c.2.1
                            have p21769_2 := h21769c.2.2.1
                            have p21769_3 := h21769c.2.2.2
                            linarith only [h16563, hc01, hc12, hlam, hphi, p21769_1]
                          · have p21769_0 := h21769c.1
                            have p21769_1 := h21769c.2.1
                            have p21769_2 := h21769c.2.2.1
                            have p21769_3 := h21769c.2.2.2
                            linarith only [h17994, hc01, hc12, hlam, hphi, p21769_1]
                          · have p21769_0 := h21769c.1
                            have p21769_1 := h21769c.2.1
                            have p21769_2 := h21769c.2.2.1
                            have p21769_3 := h21769c.2.2.2
                            rcases p21769_3 (m.d 0 1) (by simp) with h21786 | h21786
                            · linarith only [h21786, hlam, p21769_0]
                            · rcases p21769_3 (m.d 1 2) (by simp) with h21788 | h21788
                              · rcases p21769_3 (m.d 1 3) (by simp) with h21789 | h21789
                                · rcases p21769_3 (m.d 1 4) (by simp) with h21790 | h21790
                                  · linarith only [h21749, h21790, hlam]
                                  · linarith only [h16563, h21790, hlam]
                                · linarith only [h21789, hlam, p21769_0]
                              · linarith only [h0, h21788, hlam]
                          · have p21769_0 := h21769c.1
                            have p21769_1 := h21769c.2.1
                            have p21769_2 := h21769c.2.2.1
                            have p21769_3 := h21769c.2.2.2
                            linarith only [h21746, hlam, p21769_1]
                          · have p21769_0 := h21769c.1
                            have p21769_1 := h21769c.2.1
                            have p21769_2 := h21769c.2.2.1
                            have p21769_3 := h21769c.2.2.2
                            linarith only [hlam, p21769_0]
                          · have p21769_0 := h21769c.1
                            have p21769_1 := h21769c.2.1
                            have p21769_2 := h21769c.2.2.1
                            have p21769_3 := h21769c.2.2.2
                            linarith only [h14799, h19113, h21749, hc01, hc13, hlam, hphi, p21769_1]
                          · have p21769_0 := h21769c.1
                            have p21769_1 := h21769c.2.1
                            have p21769_2 := h21769c.2.2.1
                            have p21769_3 := h21769c.2.2.2
                            linarith only [h17994, h21746, hc01, hc12, hlam, hphi, p21769_1]
                          · have p21769_0 := h21769c.1
                            have p21769_1 := h21769c.2.1
                            have p21769_2 := h21769c.2.2.1
                            have p21769_3 := h21769c.2.2.2
                            linarith only [h21751, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p21769_1]
                          · have p21769_0 := h21769c.1
                            have p21769_1 := h21769c.2.1
                            have p21769_2 := h21769c.2.2.1
                            have p21769_3 := h21769c.2.2.2
                            linarith only [h21747, hlam, p21769_1]
                          · have p21769_0 := h21769c.1
                            have p21769_1 := h21769c.2.1
                            have p21769_2 := h21769c.2.2.1
                            have p21769_3 := h21769c.2.2.2
                            linarith only [h21749, hlam, p21769_0]
                          · have p21769_0 := h21769c.1
                            have p21769_1 := h21769c.2.1
                            have p21769_2 := h21769c.2.2.1
                            have p21769_3 := h21769c.2.2.2
                            linarith only [hlam, p21769_0]
                          · have p21769_0 := h21769c.1
                            have p21769_1 := h21769c.2.1
                            have p21769_2 := h21769c.2.2.1
                            have p21769_3 := h21769c.2.2.2
                            linarith only [h21751, hlam, p21769_1]
                          · have p21769_0 := h21769c.1
                            have p21769_1 := h21769c.2.1
                            have p21769_2 := h21769c.2.2.1
                            have p21769_3 := h21769c.2.2.2
                            rcases p21769_3 (m.d 0 1) (by simp) with h21804 | h21804
                            · linarith only [h21804, hlam, p21769_0]
                            · rcases p21769_3 (m.d 1 2) (by simp) with h21806 | h21806
                              · rcases p21769_3 (m.d 1 3) (by simp) with h21807 | h21807
                                · rcases p21769_3 (m.d 1 4) (by simp) with h21808 | h21808
                                  · linarith only [h21751, h21808, hlam]
                                  · linarith only [h16563, h21808, hlam]
                                · linarith only [h14799, h21807, hlam]
                              · linarith only [h0, h21806, hlam]
                          · have p21769_0 := h21769c.1
                            have p21769_1 := h21769c.2.1
                            have p21769_2 := h21769c.2.2.1
                            have p21769_3 := h21769c.2.2.2
                            linarith only [h21748, hlam, p21769_1]
                          · have p21769_0 := h21769c.1
                            have p21769_1 := h21769c.2.1
                            have p21769_2 := h21769c.2.2.1
                            have p21769_3 := h21769c.2.2.2
                            linarith only [h21750, hlam, p21769_0]
                          · have p21769_0 := h21769c.1
                            have p21769_1 := h21769c.2.1
                            have p21769_2 := h21769c.2.2.1
                            have p21769_3 := h21769c.2.2.2
                            linarith only [h16563, hc01, hc15, hlam, hphi, p21769_1]
                          · have p21769_0 := h21769c.1
                            have p21769_1 := h21769c.2.1
                            have p21769_2 := h21769c.2.2.1
                            have p21769_3 := h21769c.2.2.2
                            linarith only [hlam, p21769_0]
              · linarith only [h14799, h19113, h21749, h21750, hc01, hc35, hlam, hphi, ht12, ht23]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h21818 | h21818
              · linarith only [h14799, h21259, h21749, h21818, hc01, hc34, hlam, hphi, ht12, ht23]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h21820 | h21820
                · rcases m.htr 2 3 4 (by decide) (by decide) with h21821 | h21821
                  · linarith only [h14799, h21749, h21821, hc01, hc23, hlam, hphi, ht12]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h21823 | h21823
                    · linarith only [h19110, h21259, h21823, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h21825 | h21825
                      · linarith only [h19111, h21428, h21825, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h21827 | h21827
                        · rcases h1bigk with h21828c | h21828c | h21828c | h21828c | h21828c | h21828c | h21828c | h21828c | h21828c | h21828c | h21828c | h21828c | h21828c | h21828c | h21828c | h21828c | h21828c | h21828c | h21828c | h21828c | h21828c | h21828c | h21828c | h21828c | h21828c
                          · have p21828_0 := h21828c.1
                            have p21828_1 := h21828c.2.1
                            have p21828_2 := h21828c.2.2.1
                            have p21828_3 := h21828c.2.2.2
                            linarith only [hlam, p21828_0]
                          · have p21828_0 := h21828c.1
                            have p21828_1 := h21828c.2.1
                            have p21828_2 := h21828c.2.2.1
                            have p21828_3 := h21828c.2.2.2
                            linarith only [h0, hlam, p21828_0]
                          · have p21828_0 := h21828c.1
                            have p21828_1 := h21828c.2.1
                            have p21828_2 := h21828c.2.2.1
                            have p21828_3 := h21828c.2.2.2
                            linarith only [h14799, hlam, p21828_0]
                          · have p21828_0 := h21828c.1
                            have p21828_1 := h21828c.2.1
                            have p21828_2 := h21828c.2.2.1
                            have p21828_3 := h21828c.2.2.2
                            linarith only [h16563, hlam, p21828_0]
                          · have p21828_0 := h21828c.1
                            have p21828_1 := h21828c.2.1
                            have p21828_2 := h21828c.2.2.1
                            have p21828_3 := h21828c.2.2.2
                            linarith only [h17994, hlam, p21828_0]
                          · have p21828_0 := h21828c.1
                            have p21828_1 := h21828c.2.1
                            have p21828_2 := h21828c.2.2.1
                            have p21828_3 := h21828c.2.2.2
                            rcases p21828_3 (m.d 0 1) (by simp) with h21834 | h21834
                            · linarith only [h21834, hlam, p21828_0]
                            · rcases p21828_3 (m.d 1 2) (by simp) with h21836 | h21836
                              · rcases p21828_3 (m.d 1 3) (by simp) with h21837 | h21837
                                · linarith only [h21746, h21837, hlam]
                                · linarith only [h14799, h21837, hlam]
                              · linarith only [h21836, hlam, p21828_0]
                          · have p21828_0 := h21828c.1
                            have p21828_1 := h21828c.2.1
                            have p21828_2 := h21828c.2.2.1
                            have p21828_3 := h21828c.2.2.2
                            linarith only [hlam, p21828_0]
                          · have p21828_0 := h21828c.1
                            have p21828_1 := h21828c.2.1
                            have p21828_2 := h21828c.2.2.1
                            have p21828_3 := h21828c.2.2.2
                            linarith only [h14799, hc01, hc12, hlam, hphi, p21828_1]
                          · have p21828_0 := h21828c.1
                            have p21828_1 := h21828c.2.1
                            have p21828_2 := h21828c.2.2.1
                            have p21828_3 := h21828c.2.2.2
                            linarith only [h19113, h21428, h21820, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p21828_1]
                          · have p21828_0 := h21828c.1
                            have p21828_1 := h21828c.2.1
                            have p21828_2 := h21828c.2.2.1
                            have p21828_3 := h21828c.2.2.2
                            linarith only [h17994, hc01, hc12, hlam, hphi, p21828_1]
                          · have p21828_0 := h21828c.1
                            have p21828_1 := h21828c.2.1
                            have p21828_2 := h21828c.2.2.1
                            have p21828_3 := h21828c.2.2.2
                            linarith only [h21749, hc01, hc34, hlam, hphi, ht12, ht23, p21828_1]
                          · have p21828_0 := h21828c.1
                            have p21828_1 := h21828c.2.1
                            have p21828_2 := h21828c.2.2.1
                            have p21828_3 := h21828c.2.2.2
                            linarith only [h21746, hlam, p21828_1]
                          · have p21828_0 := h21828c.1
                            have p21828_1 := h21828c.2.1
                            have p21828_2 := h21828c.2.2.1
                            have p21828_3 := h21828c.2.2.2
                            linarith only [hlam, p21828_0]
                          · have p21828_0 := h21828c.1
                            have p21828_1 := h21828c.2.1
                            have p21828_2 := h21828c.2.2.1
                            have p21828_3 := h21828c.2.2.2
                            linarith only [h21749, hlam, p21828_1]
                          · have p21828_0 := h21828c.1
                            have p21828_1 := h21828c.2.1
                            have p21828_2 := h21828c.2.2.1
                            have p21828_3 := h21828c.2.2.2
                            linarith only [h21818, hlam, p21828_1]
                          · have p21828_0 := h21828c.1
                            have p21828_1 := h21828c.2.1
                            have p21828_2 := h21828c.2.2.1
                            have p21828_3 := h21828c.2.2.2
                            rcases p21828_3 (m.d 0 1) (by simp) with h21850 | h21850
                            · linarith only [h21850, hlam, p21828_0]
                            · rcases p21828_3 (m.d 1 2) (by simp) with h21852 | h21852
                              · rcases p21828_3 (m.d 1 3) (by simp) with h21853 | h21853
                                · linarith only [h21749, h21853, hlam]
                                · linarith only [h14799, h21853, hlam]
                              · linarith only [h0, h21852, hlam]
                          · have p21828_0 := h21828c.1
                            have p21828_1 := h21828c.2.1
                            have p21828_2 := h21828c.2.2.1
                            have p21828_3 := h21828c.2.2.2
                            linarith only [h21747, hlam, p21828_1]
                          · have p21828_0 := h21828c.1
                            have p21828_1 := h21828c.2.1
                            have p21828_2 := h21828c.2.2.1
                            have p21828_3 := h21828c.2.2.2
                            linarith only [h14799, hc01, hc14, hlam, hphi, p21828_1]
                          · have p21828_0 := h21828c.1
                            have p21828_1 := h21828c.2.1
                            have p21828_2 := h21828c.2.2.1
                            have p21828_3 := h21828c.2.2.2
                            linarith only [hlam, p21828_0]
                          · have p21828_0 := h21828c.1
                            have p21828_1 := h21828c.2.1
                            have p21828_2 := h21828c.2.2.1
                            have p21828_3 := h21828c.2.2.2
                            linarith only [h17994, h21749, hc01, hc34, hlam, hphi, ht12, ht23, p21828_1]
                          · have p21828_0 := h21828c.1
                            have p21828_1 := h21828c.2.1
                            have p21828_2 := h21828c.2.2.1
                            have p21828_3 := h21828c.2.2.2
                            rcases p21828_3 (m.d 0 1) (by simp) with h21861 | h21861
                            · linarith only [h21861, hlam, p21828_0]
                            · rcases p21828_3 (m.d 1 2) (by simp) with h21863 | h21863
                              · rcases p21828_3 (m.d 1 3) (by simp) with h21864 | h21864
                                · linarith only [h21818, h21864, hlam]
                                · linarith only [h14799, h21864, hlam]
                              · linarith only [h0, h21863, hlam]
                          · have p21828_0 := h21828c.1
                            have p21828_1 := h21828c.2.1
                            have p21828_2 := h21828c.2.2.1
                            have p21828_3 := h21828c.2.2.2
                            linarith only [h21748, hlam, p21828_1]
                          · have p21828_0 := h21828c.1
                            have p21828_1 := h21828c.2.1
                            have p21828_2 := h21828c.2.2.1
                            have p21828_3 := h21828c.2.2.2
                            linarith only [h14799, hc01, hc15, hlam, hphi, p21828_1]
                          · have p21828_0 := h21828c.1
                            have p21828_1 := h21828c.2.1
                            have p21828_2 := h21828c.2.2.1
                            have p21828_3 := h21828c.2.2.2
                            linarith only [h21820, hlam, p21828_0]
                          · have p21828_0 := h21828c.1
                            have p21828_1 := h21828c.2.1
                            have p21828_2 := h21828c.2.2.1
                            have p21828_3 := h21828c.2.2.2
                            linarith only [hlam, p21828_0]
                        · linarith only [h21749, h21820, h21827, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h21873 | h21873
                  · linarith only [h19110, h19113, h21873, hlam]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h21875 | h21875
                    · linarith only [h0, h17994, h19110, h21818, h21875, hc01, hc12, hlam, hphi]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h21877 | h21877
                      · linarith only [h16563, h19111, h21820, h21877, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h21879 | h21879
                        · linarith only [h14799, h21749, h21820, h21879, hc01, hc34, hlam, hphi, ht12, ht23]
                        · linarith only [h14799, h21749, h21879, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
          · linarith only [h0, h19112, h21748, hlam]
        · linarith only [h0, h19111, h21747, hlam]
      · linarith only [h0, h19110, h21746, hlam]

set_option maxHeartbeats 5544000 in
set_option maxHeartbeats 5544000 in
theorem r1l7_11_13_25_L_I_L_I_H_I_s19 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg14799 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg16563 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg17994 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg19110 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg19111 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg19112 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
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
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h14799 := hg14799
  have h16563 := hg16563
  have h17994 := hg17994
  have h19110 := hg19110
  have h19111 := hg19111
  have h19112 := hg19112
  rcases m.htr 0 3 4 (by decide) (by decide) with h19113 | h19113
  · exact r1l7_11_13_25_L_I_L_I_H_I_s19_x0 m hb1 hb3 hb5 hg0 hg14799 hg16563 hg17994 hg19110 hg19111 hg19112 h19113
  · exact r1l7_11_13_25_L_I_L_I_H_I_s19_x1 m hb1 hb3 hb5 hg0 hg14799 hg16563 hg17994 hg19110 hg19111 hg19112 h19113

set_option maxHeartbeats 5846000 in
set_option maxHeartbeats 5846000 in
theorem r1l7_11_13_25_L_I_L_I_H_I_s18 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg14799 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg16563 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg17994 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg19110 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg19111 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
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
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h14799 := hg14799
  have h16563 := hg16563
  have h17994 := hg17994
  have h19110 := hg19110
  have h19111 := hg19111
  rcases m.htr 0 2 5 (by decide) (by decide) with h19112 | h19112
  · exact r1l7_11_13_25_L_I_L_I_H_I_s19 m hb1 hb3 hb5 h0 h14799 h16563 h17994 h19110 h19111 h19112
  · rcases m.htr 0 3 4 (by decide) (by decide) with h21885 | h21885
    · rcases m.htr 0 3 5 (by decide) (by decide) with h21886 | h21886
      · linarith only [h19110, h19112, h21886, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h21888 | h21888
        · linarith only [h19110, h19112, h21885, h21888, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h21890 | h21890
          · rcases m.htr 1 2 4 (by decide) (by decide) with h21891 | h21891
            · rcases m.htr 1 2 5 (by decide) (by decide) with h21892 | h21892
              · rcases m.htr 1 3 4 (by decide) (by decide) with h21893 | h21893
                · rcases m.htr 1 3 5 (by decide) (by decide) with h21894 | h21894
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h21895 | h21895
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h21896 | h21896
                      · linarith only [h19110, h19112, h21892, h21896, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · linarith only [h19110, h19112, h21885, h21892, h21896, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h21899 | h21899
                      · linarith only [h19110, h19112, h21892, h21899, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · linarith only [h19110, h19112, h21885, h21892, h21899, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h21902 | h21902
                    · linarith only [h16563, h21888, h21893, h21894, h21902, hc01, hc35, hlam, hphi, ht12, ht23]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h21904 | h21904
                      · linarith only [h19110, h19112, h21892, h21904, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · linarith only [h19110, h19112, h21885, h21892, h21904, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                · linarith only [h14799, h19110, h19112, h21885, h21892, h21893, hc01, hc12, hlam, hphi]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h21908 | h21908
                · rcases m.htr 1 3 5 (by decide) (by decide) with h21909 | h21909
                  · linarith only [h21885, h21886, h21890, h21892, h21909, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h21911 | h21911
                    · linarith only [h16563, h21888, h21891, h21892, h21911, hc01, hc25, hlam, hphi, ht12]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h21913 | h21913
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h21914 | h21914
                        · linarith only [h0, h19110, h21892, h21909, h21914, hc13, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h21916 | h21916
                          · linarith only [h0, h17994, h19111, h21892, h21911, h21914, h21916, hc01, hc35, hlam, hphi, ht12, ht23]
                          · linarith only [h0, h19110, h21892, h21913, h21916, hc34, hc45, hlam, hphi]
                      · linarith only [h21885, h21886, h21913, hc23, hc35, hlam, hphi]
                · linarith only [h14799, h21885, h21908, hlam]
            · linarith only [h0, h19111, h21891, hlam]
          · linarith only [h0, h19110, h21890, hlam]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h21923 | h21923
      · linarith only [h19111, h19112, h21885, h21923, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h21925 | h21925
        · linarith only [h19111, h19112, h21925, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h21927 | h21927
          · rcases m.htr 1 2 4 (by decide) (by decide) with h21928 | h21928
            · rcases m.htr 1 2 5 (by decide) (by decide) with h21929 | h21929
              · rcases m.htr 1 3 4 (by decide) (by decide) with h21930 | h21930
                · rcases m.htr 1 3 5 (by decide) (by decide) with h21931 | h21931
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h21932 | h21932
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h21933 | h21933
                      · linarith only [h19110, h19112, h21885, h21929, h21933, hc03, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h21935 | h21935
                        · linarith only [h14799, h19111, h19112, h21923, h21929, h21933, h21935, hc01, hc12, hlam, hphi]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h21937 | h21937
                          · linarith only [h19111, h19112, h21927, h21931, h21935, h21937, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h21939 | h21939
                            · linarith only [h19111, h19112, h21933, h21937, h21939, hc23, hc34, hlam, hphi]
                            · linarith only [h14799, h21885, h21927, h21930, h21932, h21939, hc01, hc12, hlam, hphi]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h21942 | h21942
                      · linarith only [h14799, h19110, h19112, h21885, h21929, h21942, hc01, hc15, hlam, hphi]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h21944 | h21944
                        · linarith only [h19111, h19112, h21923, h21929, h21942, h21944, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h21946 | h21946
                          · linarith only [h19111, h19112, h21927, h21931, h21932, h21944, h21946, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h21948 | h21948
                            · linarith only [h21930, h21932, h21948, hlam]
                            · rcases h1bigk with h21950c | h21950c | h21950c | h21950c | h21950c | h21950c | h21950c | h21950c | h21950c | h21950c | h21950c | h21950c | h21950c | h21950c | h21950c | h21950c | h21950c | h21950c | h21950c | h21950c | h21950c | h21950c | h21950c | h21950c | h21950c
                              · have p21950_0 := h21950c.1
                                have p21950_1 := h21950c.2.1
                                have p21950_2 := h21950c.2.2.1
                                have p21950_3 := h21950c.2.2.2
                                linarith only [hlam, p21950_0]
                              · have p21950_0 := h21950c.1
                                have p21950_1 := h21950c.2.1
                                have p21950_2 := h21950c.2.2.1
                                have p21950_3 := h21950c.2.2.2
                                linarith only [h0, hlam, p21950_0]
                              · have p21950_0 := h21950c.1
                                have p21950_1 := h21950c.2.1
                                have p21950_2 := h21950c.2.2.1
                                have p21950_3 := h21950c.2.2.2
                                linarith only [h14799, hlam, p21950_0]
                              · have p21950_0 := h21950c.1
                                have p21950_1 := h21950c.2.1
                                have p21950_2 := h21950c.2.2.1
                                have p21950_3 := h21950c.2.2.2
                                linarith only [h16563, hlam, p21950_0]
                              · have p21950_0 := h21950c.1
                                have p21950_1 := h21950c.2.1
                                have p21950_2 := h21950c.2.2.1
                                have p21950_3 := h21950c.2.2.2
                                linarith only [h17994, hlam, p21950_0]
                              · have p21950_0 := h21950c.1
                                have p21950_1 := h21950c.2.1
                                have p21950_2 := h21950c.2.2.1
                                have p21950_3 := h21950c.2.2.2
                                rcases p21950_3 (m.d 0 1) (by simp) with h21956 | h21956
                                · linarith only [h21956, hlam, p21950_0]
                                · rcases p21950_3 (m.d 1 2) (by simp) with h21958 | h21958
                                  · rcases p21950_3 (m.d 1 3) (by simp) with h21959 | h21959
                                    · linarith only [h21927, h21959, hlam]
                                    · linarith only [h14799, h21959, hlam]
                                  · linarith only [h21958, hlam, p21950_0]
                              · have p21950_0 := h21950c.1
                                have p21950_1 := h21950c.2.1
                                have p21950_2 := h21950c.2.2.1
                                have p21950_3 := h21950c.2.2.2
                                linarith only [hlam, p21950_0]
                              · have p21950_0 := h21950c.1
                                have p21950_1 := h21950c.2.1
                                have p21950_2 := h21950c.2.2.1
                                have p21950_3 := h21950c.2.2.2
                                linarith only [h19111, h19112, h21931, h21942, h21944, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p21950_1]
                              · have p21950_0 := h21950c.1
                                have p21950_1 := h21950c.2.1
                                have p21950_2 := h21950c.2.2.1
                                have p21950_3 := h21950c.2.2.2
                                linarith only [h14799, h21885, h21930, hc01, hc12, hlam, hphi, p21950_1]
                              · have p21950_0 := h21950c.1
                                have p21950_1 := h21950c.2.1
                                have p21950_2 := h21950c.2.2.1
                                have p21950_3 := h21950c.2.2.2
                                linarith only [h17994, hc01, hc12, hlam, hphi, p21950_1]
                              · have p21950_0 := h21950c.1
                                have p21950_1 := h21950c.2.1
                                have p21950_2 := h21950c.2.2.1
                                have p21950_3 := h21950c.2.2.2
                                rcases p21950_3 (m.d 0 1) (by simp) with h21967 | h21967
                                · linarith only [h21967, hlam, p21950_0]
                                · rcases p21950_3 (m.d 1 2) (by simp) with h21969 | h21969
                                  · rcases p21950_3 (m.d 1 3) (by simp) with h21970 | h21970
                                    · rcases p21950_3 (m.d 1 4) (by simp) with h21971 | h21971
                                      · linarith only [h21930, h21971, hlam]
                                      · linarith only [h16563, h21971, hlam]
                                    · linarith only [h21970, hlam, p21950_0]
                                  · linarith only [h0, h21969, hlam]
                              · have p21950_0 := h21950c.1
                                have p21950_1 := h21950c.2.1
                                have p21950_2 := h21950c.2.2.1
                                have p21950_3 := h21950c.2.2.2
                                linarith only [h21927, hlam, p21950_1]
                              · have p21950_0 := h21950c.1
                                have p21950_1 := h21950c.2.1
                                have p21950_2 := h21950c.2.2.1
                                have p21950_3 := h21950c.2.2.2
                                linarith only [hlam, p21950_0]
                              · have p21950_0 := h21950c.1
                                have p21950_1 := h21950c.2.1
                                have p21950_2 := h21950c.2.2.1
                                have p21950_3 := h21950c.2.2.2
                                linarith only [h14799, h21885, h21930, hc01, hc13, hlam, hphi, p21950_1]
                              · have p21950_0 := h21950c.1
                                have p21950_1 := h21950c.2.1
                                have p21950_2 := h21950c.2.2.1
                                have p21950_3 := h21950c.2.2.2
                                linarith only [h19111, h19112, h21927, h21931, h21942, h21944, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p21950_1]
                              · have p21950_0 := h21950c.1
                                have p21950_1 := h21950c.2.1
                                have p21950_2 := h21950c.2.2.1
                                have p21950_3 := h21950c.2.2.2
                                linarith only [h21932, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p21950_1]
                              · have p21950_0 := h21950c.1
                                have p21950_1 := h21950c.2.1
                                have p21950_2 := h21950c.2.2.1
                                have p21950_3 := h21950c.2.2.2
                                linarith only [h21928, hlam, p21950_1]
                              · have p21950_0 := h21950c.1
                                have p21950_1 := h21950c.2.1
                                have p21950_2 := h21950c.2.2.1
                                have p21950_3 := h21950c.2.2.2
                                linarith only [h21930, hlam, p21950_0]
                              · have p21950_0 := h21950c.1
                                have p21950_1 := h21950c.2.1
                                have p21950_2 := h21950c.2.2.1
                                have p21950_3 := h21950c.2.2.2
                                linarith only [hlam, p21950_0]
                              · have p21950_0 := h21950c.1
                                have p21950_1 := h21950c.2.1
                                have p21950_2 := h21950c.2.2.1
                                have p21950_3 := h21950c.2.2.2
                                linarith only [h21932, hlam, p21950_1]
                              · have p21950_0 := h21950c.1
                                have p21950_1 := h21950c.2.1
                                have p21950_2 := h21950c.2.2.1
                                have p21950_3 := h21950c.2.2.2
                                rcases p21950_3 (m.d 0 1) (by simp) with h21985 | h21985
                                · linarith only [h21985, hlam, p21950_0]
                                · rcases p21950_3 (m.d 1 2) (by simp) with h21987 | h21987
                                  · rcases p21950_3 (m.d 1 3) (by simp) with h21988 | h21988
                                    · rcases p21950_3 (m.d 1 4) (by simp) with h21989 | h21989
                                      · linarith only [h21932, h21989, hlam]
                                      · linarith only [h16563, h21989, hlam]
                                    · linarith only [h14799, h21988, hlam]
                                  · linarith only [h0, h21987, hlam]
                              · have p21950_0 := h21950c.1
                                have p21950_1 := h21950c.2.1
                                have p21950_2 := h21950c.2.2.1
                                have p21950_3 := h21950c.2.2.2
                                linarith only [h21929, hlam, p21950_1]
                              · have p21950_0 := h21950c.1
                                have p21950_1 := h21950c.2.1
                                have p21950_2 := h21950c.2.2.1
                                have p21950_3 := h21950c.2.2.2
                                linarith only [h21931, hlam, p21950_0]
                              · have p21950_0 := h21950c.1
                                have p21950_1 := h21950c.2.1
                                have p21950_2 := h21950c.2.2.1
                                have p21950_3 := h21950c.2.2.2
                                linarith only [h16563, hc01, hc15, hlam, hphi, p21950_1]
                              · have p21950_0 := h21950c.1
                                have p21950_1 := h21950c.2.1
                                have p21950_2 := h21950c.2.2.1
                                have p21950_3 := h21950c.2.2.2
                                linarith only [hlam, p21950_0]
                  · linarith only [h14799, h21885, h21930, h21931, hc01, hc35, hlam, hphi, ht12, ht23]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h21999 | h21999
                  · linarith only [h14799, h21923, h21930, h21999, hc01, hc34, hlam, hphi, ht12, ht23]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h22001 | h22001
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h22002 | h22002
                      · linarith only [h14799, h21930, h22002, hc01, hc23, hlam, hphi, ht12]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h22004 | h22004
                        · linarith only [h19111, h19112, h21929, h21999, h22002, h22004, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h22006 | h22006
                          · linarith only [h14799, h19111, h19112, h21885, h21925, h21929, h22006, hc01, hc12, hlam, hphi]
                          · linarith only [h19111, h19112, h21930, h22001, h22002, h22006, hc23, hc34, hlam, hphi]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h22009 | h22009
                      · linarith only [h19110, h19112, h21929, h22009, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h22011 | h22011
                        · linarith only [h19111, h19112, h21929, h21999, h22009, h22011, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h22013 | h22013
                          · linarith only [h19111, h19112, h21929, h22001, h22013, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h22015 | h22015
                            · linarith only [h14799, h21930, h22001, h22015, hc01, hc34, hlam, hphi, ht12, ht23]
                            · linarith only [h14799, h21930, h22015, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h22018 | h22018
                · linarith only [h14799, h21885, h21927, h21929, h22018, hc01, hc25, hlam, hphi, ht12]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h22020 | h22020
                  · linarith only [h14799, h21923, h21928, h21929, h22018, h22020, hc01, hc25, hlam, hphi, ht12]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h22022 | h22022
                    · linarith only [h14799, h21885, h21925, h21928, h21929, h22022, hc01, hc25, hlam, hphi, ht12]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h22024 | h22024
                      · linarith only [h14799, h22018, h22024, hc01, hc23, hlam, hphi, ht12]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h22026 | h22026
                        · linarith only [h0, h19111, h21929, h22020, h22024, h22026, hc13, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h22028 | h22028
                          · linarith only [h0, h14799, h19111, h21929, h22018, h22022, h22026, h22028, hc01, hc35, hlam, hphi, ht12, ht23]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h22030 | h22030
                            · linarith only [h0, h19111, h21929, h22024, h22028, h22030, hc23, hc34, hlam, hphi]
                            · linarith only [h14799, h22018, h22030, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
            · linarith only [h0, h19111, h21928, hlam]
          · linarith only [h0, h19110, h21927, hlam]

end R2N4
