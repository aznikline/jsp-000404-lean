import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 10432000 in
set_option maxHeartbeats 10432000 in
theorem r1l7_12_24_L_I_H_I_s7_x1_x1_x0 (m : N7Model)
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6874 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h8886 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h12751 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h13259 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h6874 := hg6874
  rcases m.htr 0 3 4 (by decide) (by decide) with h13260 | h13260
  · rcases m.htr 0 4 5 (by decide) (by decide) with h13261 | h13261
    · rcases m.htr 1 2 3 (by decide) (by decide) with h13262 | h13262
      · rcases m.htr 1 2 4 (by decide) (by decide) with h13263 | h13263
        · rcases m.htr 1 2 5 (by decide) (by decide) with h13264 | h13264
          · rcases m.htr 1 3 4 (by decide) (by decide) with h13265 | h13265
            · rcases m.htr 1 4 5 (by decide) (by decide) with h13266 | h13266
              · rcases m.htr 2 3 4 (by decide) (by decide) with h13267 | h13267
                · rcases m.htr 2 3 5 (by decide) (by decide) with h13268 | h13268
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h13269 | h13269
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h13270 | h13270
                      · rcases h2bigk with h13271c | h13271c | h13271c | h13271c | h13271c | h13271c | h13271c | h13271c | h13271c | h13271c | h13271c | h13271c | h13271c | h13271c | h13271c | h13271c | h13271c | h13271c | h13271c | h13271c | h13271c | h13271c | h13271c | h13271c | h13271c
                        · have p13271_0 := h13271c.1
                          have p13271_1 := h13271c.2.1
                          have p13271_2 := h13271c.2.2.1
                          have p13271_3 := h13271c.2.2.2
                          linarith only [hlam, p13271_0]
                        · have p13271_0 := h13271c.1
                          have p13271_1 := h13271c.2.1
                          have p13271_2 := h13271c.2.2.1
                          have p13271_3 := h13271c.2.2.2
                          linarith only [h0, hlam, p13271_0]
                        · have p13271_0 := h13271c.1
                          have p13271_1 := h13271c.2.1
                          have p13271_2 := h13271c.2.2.1
                          have p13271_3 := h13271c.2.2.2
                          linarith only [h8886, hlam, p13271_0]
                        · have p13271_0 := h13271c.1
                          have p13271_1 := h13271c.2.1
                          have p13271_2 := h13271c.2.2.1
                          have p13271_3 := h13271c.2.2.2
                          linarith only [h12751, hlam, p13271_0]
                        · have p13271_0 := h13271c.1
                          have p13271_1 := h13271c.2.1
                          have p13271_2 := h13271c.2.2.1
                          have p13271_3 := h13271c.2.2.2
                          linarith only [h12751, h13262, h13267, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p13271_1]
                        · have p13271_0 := h13271c.1
                          have p13271_1 := h13271c.2.1
                          have p13271_2 := h13271c.2.2.1
                          have p13271_3 := h13271c.2.2.2
                          rcases p13271_3 (m.d 0 2) (by simp) with h13277 | h13277
                          · linarith only [h0, h13277, hlam]
                          · rcases p13271_3 (m.d 1 2) (by simp) with h13279 | h13279
                            · rcases p13271_3 (m.d 2 3) (by simp) with h13280 | h13280
                              · linarith only [h13262, h13280, hlam]
                              · linarith only [h13280, h8886, hlam]
                            · linarith only [h0, h13279, hlam]
                        · have p13271_0 := h13271c.1
                          have p13271_1 := h13271c.2.1
                          have p13271_2 := h13271c.2.2.1
                          have p13271_3 := h13271c.2.2.2
                          linarith only [hlam, p13271_0]
                        · have p13271_0 := h13271c.1
                          have p13271_1 := h13271c.2.1
                          have p13271_2 := h13271c.2.2.1
                          have p13271_3 := h13271c.2.2.2
                          linarith only [h0, h12751, h13267, hc01, hc12, hlam, hphi, p13271_1]
                        · have p13271_0 := h13271c.1
                          have p13271_1 := h13271c.2.1
                          have p13271_2 := h13271c.2.2.1
                          have p13271_3 := h13271c.2.2.2
                          linarith only [h12751, h13259, h13268, h13270, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p13271_1]
                        · have p13271_0 := h13271c.1
                          have p13271_1 := h13271c.2.1
                          have p13271_2 := h13271c.2.2.1
                          have p13271_3 := h13271c.2.2.2
                          linarith only [h12751, h13259, h13262, h13267, hlam, p13271_2]
                        · have p13271_0 := h13271c.1
                          have p13271_1 := h13271c.2.1
                          have p13271_2 := h13271c.2.2.1
                          have p13271_3 := h13271c.2.2.2
                          linarith only [h13259, h13262, h13268, h13270, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p13271_1]
                        · have p13271_0 := h13271c.1
                          have p13271_1 := h13271c.2.1
                          have p13271_2 := h13271c.2.2.1
                          have p13271_3 := h13271c.2.2.2
                          linarith only [h13262, hlam, p13271_0]
                        · have p13271_0 := h13271c.1
                          have p13271_1 := h13271c.2.1
                          have p13271_2 := h13271c.2.2.1
                          have p13271_3 := h13271c.2.2.2
                          linarith only [hlam, p13271_0]
                        · have p13271_0 := h13271c.1
                          have p13271_1 := h13271c.2.1
                          have p13271_2 := h13271c.2.2.1
                          have p13271_3 := h13271c.2.2.2
                          linarith only [h12751, h13259, h13262, h13268, h13270, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p13271_1]
                        · have p13271_0 := h13271c.1
                          have p13271_1 := h13271c.2.1
                          have p13271_2 := h13271c.2.2.1
                          have p13271_3 := h13271c.2.2.2
                          rcases p13271_3 (m.d 0 2) (by simp) with h13292 | h13292
                          · linarith only [h13292, h8886, hlam]
                          · linarith only [h13259, h13292, hlam]
                        · have p13271_0 := h13271c.1
                          have p13271_1 := h13271c.2.1
                          have p13271_2 := h13271c.2.2.1
                          have p13271_3 := h13271c.2.2.2
                          linarith only [h13259, h13263, h13268, h13270, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p13271_1]
                        · have p13271_0 := h13271c.1
                          have p13271_1 := h13271c.2.1
                          have p13271_2 := h13271c.2.2.1
                          have p13271_3 := h13271c.2.2.2
                          linarith only [h13263, hlam, p13271_0]
                        · have p13271_0 := h13271c.1
                          have p13271_1 := h13271c.2.1
                          have p13271_2 := h13271c.2.2.1
                          have p13271_3 := h13271c.2.2.2
                          linarith only [h13267, hlam, p13271_0]
                        · have p13271_0 := h13271c.1
                          have p13271_1 := h13271c.2.1
                          have p13271_2 := h13271c.2.2.1
                          have p13271_3 := h13271c.2.2.2
                          linarith only [hlam, p13271_0]
                        · have p13271_0 := h13271c.1
                          have p13271_1 := h13271c.2.1
                          have p13271_2 := h13271c.2.2.1
                          have p13271_3 := h13271c.2.2.2
                          rcases p13271_3 (m.d 0 2) (by simp) with h13299 | h13299
                          · linarith only [h12751, h13299, hlam]
                          · linarith only [h13259, h13299, hlam]
                        · have p13271_0 := h13271c.1
                          have p13271_1 := h13271c.2.1
                          have p13271_2 := h13271c.2.2.1
                          have p13271_3 := h13271c.2.2.2
                          linarith only [h13259, hlam, p13271_0]
                        · have p13271_0 := h13271c.1
                          have p13271_1 := h13271c.2.1
                          have p13271_2 := h13271c.2.2.1
                          have p13271_3 := h13271c.2.2.2
                          linarith only [h13264, hlam, p13271_0]
                        · have p13271_0 := h13271c.1
                          have p13271_1 := h13271c.2.1
                          have p13271_2 := h13271c.2.2.1
                          have p13271_3 := h13271c.2.2.2
                          linarith only [h13268, hlam, p13271_0]
                        · have p13271_0 := h13271c.1
                          have p13271_1 := h13271c.2.1
                          have p13271_2 := h13271c.2.2.1
                          have p13271_3 := h13271c.2.2.2
                          linarith only [h13269, hlam, p13271_1]
                        · have p13271_0 := h13271c.1
                          have p13271_1 := h13271c.2.1
                          have p13271_2 := h13271c.2.2.1
                          have p13271_3 := h13271c.2.2.2
                          linarith only [hlam, p13271_0]
                      · linarith only [h12751, h13259, h13262, h13267, h13269, h13270, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · linarith only [h12751, h13260, h13261, h13262, h13269, h8886, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                  · linarith only [h13259, h13268, h8886, hlam]
                · linarith only [h13260, h13267, h8886, hlam]
              · linarith only [h12751, h13259, h13261, h13263, h13266, hlam]
            · linarith only [h13260, h13262, h13265, h8886, hlam]
          · linarith only [h12751, h13259, h13264, hc12, hc24, hlam, hphi]
        · linarith only [h13262, h13263, h8886, hc02, hc24, hlam, hphi]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h13315 | h13315
        · linarith only [h12751, h13259, h13262, h13315, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h13317 | h13317
          · rcases m.htr 1 3 4 (by decide) (by decide) with h13318 | h13318
            · rcases m.htr 1 4 5 (by decide) (by decide) with h13319 | h13319
              · rcases m.htr 2 3 4 (by decide) (by decide) with h13320 | h13320
                · rcases m.htr 2 3 5 (by decide) (by decide) with h13321 | h13321
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h13322 | h13322
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h13323 | h13323
                      · rcases h2bigk with h13324c | h13324c | h13324c | h13324c | h13324c | h13324c | h13324c | h13324c | h13324c | h13324c | h13324c | h13324c | h13324c | h13324c | h13324c | h13324c | h13324c | h13324c | h13324c | h13324c | h13324c | h13324c | h13324c | h13324c | h13324c
                        · have p13324_0 := h13324c.1
                          have p13324_1 := h13324c.2.1
                          have p13324_2 := h13324c.2.2.1
                          have p13324_3 := h13324c.2.2.2
                          linarith only [hlam, p13324_0]
                        · have p13324_0 := h13324c.1
                          have p13324_1 := h13324c.2.1
                          have p13324_2 := h13324c.2.2.1
                          have p13324_3 := h13324c.2.2.2
                          linarith only [h0, hlam, p13324_0]
                        · have p13324_0 := h13324c.1
                          have p13324_1 := h13324c.2.1
                          have p13324_2 := h13324c.2.2.1
                          have p13324_3 := h13324c.2.2.2
                          linarith only [h8886, hlam, p13324_0]
                        · have p13324_0 := h13324c.1
                          have p13324_1 := h13324c.2.1
                          have p13324_2 := h13324c.2.2.1
                          have p13324_3 := h13324c.2.2.2
                          linarith only [h12751, hlam, p13324_0]
                        · have p13324_0 := h13324c.1
                          have p13324_1 := h13324c.2.1
                          have p13324_2 := h13324c.2.2.1
                          have p13324_3 := h13324c.2.2.2
                          rcases p13324_3 (m.d 0 2) (by simp) with h13329 | h13329
                          · rcases p13324_3 (m.d 1 2) (by simp) with h13330 | h13330
                            · rcases p13324_3 (m.d 2 3) (by simp) with h13331 | h13331
                              · rcases p13324_3 (m.d 2 4) (by simp) with h13332 | h13332
                                · rcases p13324_3 (m.d 2 5) (by simp) with h13333 | h13333
                                  · linarith only [h13333, hlam, p13324_0]
                                  · rcases h4bigk with h13335c | h13335c | h13335c | h13335c | h13335c | h13335c | h13335c | h13335c | h13335c | h13335c | h13335c | h13335c | h13335c | h13335c | h13335c | h13335c | h13335c | h13335c | h13335c | h13335c | h13335c | h13335c | h13335c | h13335c | h13335c
                                    · have p13335_0 := h13335c.1
                                      have p13335_1 := h13335c.2.1
                                      have p13335_2 := h13335c.2.2.1
                                      have p13335_3 := h13335c.2.2.2
                                      linarith only [hlam, p13335_0]
                                    · have p13335_0 := h13335c.1
                                      have p13335_1 := h13335c.2.1
                                      have p13335_2 := h13335c.2.2.1
                                      have p13335_3 := h13335c.2.2.2
                                      linarith only [h6874, hlam, p13335_1]
                                    · have p13335_0 := h13335c.1
                                      have p13335_1 := h13335c.2.1
                                      have p13335_2 := h13335c.2.2.1
                                      have p13335_3 := h13335c.2.2.2
                                      linarith only [h12751, hlam, p13335_1]
                                    · have p13335_0 := h13335c.1
                                      have p13335_1 := h13335c.2.1
                                      have p13335_2 := h13335c.2.2.1
                                      have p13335_3 := h13335c.2.2.2
                                      linarith only [h13260, h13323, hc03, hc45, hlam, hphi, ht0b, ht5b, p13335_1]
                                    · have p13335_0 := h13335c.1
                                      have p13335_1 := h13335c.2.1
                                      have p13335_2 := h13335c.2.2.1
                                      have p13335_3 := h13335c.2.2.2
                                      rcases p13335_3 (m.d 0 4) (by simp) with h13340 | h13340
                                      · rcases p13335_3 (m.d 1 4) (by simp) with h13341 | h13341
                                        · rcases p13335_3 (m.d 2 4) (by simp) with h13342 | h13342
                                          · rcases p13335_3 (m.d 3 4) (by simp) with h13343 | h13343
                                            · linarith only [h13260, h13343, hlam]
                                            · linarith only [h13323, h13343, hlam]
                                          · linarith only [h13322, h13342, hlam]
                                        · linarith only [h13319, h13341, hlam]
                                      · linarith only [h13340, hlam, p13335_0]
                                    · have p13335_0 := h13335c.1
                                      have p13335_1 := h13335c.2.1
                                      have p13335_2 := h13335c.2.2.1
                                      have p13335_3 := h13335c.2.2.2
                                      linarith only [h13318, h6874, hc01, hc13, hlam, hphi, p13335_1]
                                    · have p13335_0 := h13335c.1
                                      have p13335_1 := h13335c.2.1
                                      have p13335_2 := h13335c.2.2.1
                                      have p13335_3 := h13335c.2.2.2
                                      linarith only [hlam, p13335_0]
                                    · have p13335_0 := h13335c.1
                                      have p13335_1 := h13335c.2.1
                                      have p13335_2 := h13335c.2.2.1
                                      have p13335_3 := h13335c.2.2.2
                                      linarith only [h13315, hlam, p13335_1]
                                    · have p13335_0 := h13335c.1
                                      have p13335_1 := h13335c.2.1
                                      have p13335_2 := h13335c.2.2.1
                                      have p13335_3 := h13335c.2.2.2
                                      linarith only [h13323, hc14, hc45, hlam, hphi, ht01, ht0b, ht5b, p13335_1]
                                    · have p13335_0 := h13335c.1
                                      have p13335_1 := h13335c.2.1
                                      have p13335_2 := h13335c.2.2.1
                                      have p13335_3 := h13335c.2.2.2
                                      rcases p13335_3 (m.d 0 4) (by simp) with h13353 | h13353
                                      · linarith only [h13353, h6874, hlam]
                                      · linarith only [h13261, h13353, hlam]
                                    · have p13335_0 := h13335c.1
                                      have p13335_1 := h13335c.2.1
                                      have p13335_2 := h13335c.2.2.1
                                      have p13335_3 := h13335c.2.2.2
                                      linarith only [h12751, h13320, h13321, h13323, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p13324_1, p13335_1]
                                    · have p13335_0 := h13335c.1
                                      have p13335_1 := h13335c.2.1
                                      have p13335_2 := h13335c.2.2.1
                                      have p13335_3 := h13335c.2.2.2
                                      linarith only [h13320, h6874, hc01, hc23, hlam, hphi, ht12, p13335_1]
                                    · have p13335_0 := h13335c.1
                                      have p13335_1 := h13335c.2.1
                                      have p13335_2 := h13335c.2.2.1
                                      have p13335_3 := h13335c.2.2.2
                                      linarith only [hlam, p13335_0]
                                    · have p13335_0 := h13335c.1
                                      have p13335_1 := h13335c.2.1
                                      have p13335_2 := h13335c.2.2.1
                                      have p13335_3 := h13335c.2.2.2
                                      linarith only [h13320, h13323, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p13335_1]
                                    · have p13335_0 := h13335c.1
                                      have p13335_1 := h13335c.2.1
                                      have p13335_2 := h13335c.2.2.1
                                      have p13335_3 := h13335c.2.2.2
                                      rcases p13335_3 (m.d 0 4) (by simp) with h13360 | h13360
                                      · linarith only [h12751, h13360, hlam]
                                      · linarith only [h13261, h13360, hlam]
                                    · have p13335_0 := h13335c.1
                                      have p13335_1 := h13335c.2.1
                                      have p13335_2 := h13335c.2.2.1
                                      have p13335_3 := h13335c.2.2.2
                                      linarith only [h13260, hlam, p13335_0]
                                    · have p13335_0 := h13335c.1
                                      have p13335_1 := h13335c.2.1
                                      have p13335_2 := h13335c.2.2.1
                                      have p13335_3 := h13335c.2.2.2
                                      linarith only [h13318, hlam, p13335_0]
                                    · have p13335_0 := h13335c.1
                                      have p13335_1 := h13335c.2.1
                                      have p13335_2 := h13335c.2.2.1
                                      have p13335_3 := h13335c.2.2.2
                                      linarith only [h13320, hlam, p13335_0]
                                    · have p13335_0 := h13335c.1
                                      have p13335_1 := h13335c.2.1
                                      have p13335_2 := h13335c.2.2.1
                                      have p13335_3 := h13335c.2.2.2
                                      linarith only [hlam, p13335_0]
                                    · have p13335_0 := h13335c.1
                                      have p13335_1 := h13335c.2.1
                                      have p13335_2 := h13335c.2.2.1
                                      have p13335_3 := h13335c.2.2.2
                                      linarith only [h13260, h8886, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p13335_1]
                                    · have p13335_0 := h13335c.1
                                      have p13335_1 := h13335c.2.1
                                      have p13335_2 := h13335c.2.2.1
                                      have p13335_3 := h13335c.2.2.2
                                      linarith only [h13261, hlam, p13335_0]
                                    · have p13335_0 := h13335c.1
                                      have p13335_1 := h13335c.2.1
                                      have p13335_2 := h13335c.2.2.1
                                      have p13335_3 := h13335c.2.2.2
                                      linarith only [h13319, hlam, p13335_0]
                                    · have p13335_0 := h13335c.1
                                      have p13335_1 := h13335c.2.1
                                      have p13335_2 := h13335c.2.2.1
                                      have p13335_3 := h13335c.2.2.2
                                      linarith only [h13322, hlam, p13335_0]
                                    · have p13335_0 := h13335c.1
                                      have p13335_1 := h13335c.2.1
                                      have p13335_2 := h13335c.2.2.1
                                      have p13335_3 := h13335c.2.2.2
                                      linarith only [h13323, hlam, p13335_0]
                                    · have p13335_0 := h13335c.1
                                      have p13335_1 := h13335c.2.1
                                      have p13335_2 := h13335c.2.2.1
                                      have p13335_3 := h13335c.2.2.2
                                      linarith only [hlam, p13335_0]
                                · linarith only [h13322, h13332, hlam]
                              · linarith only [h13321, h13331, hlam]
                            · linarith only [h13317, h13330, hlam]
                          · linarith only [h13329, hlam, p13324_0]
                        · have p13324_0 := h13324c.1
                          have p13324_1 := h13324c.2.1
                          have p13324_2 := h13324c.2.2.1
                          have p13324_3 := h13324c.2.2.2
                          linarith only [h13262, hc02, hc23, hlam, hphi, p13324_1]
                        · have p13324_0 := h13324c.1
                          have p13324_1 := h13324c.2.1
                          have p13324_2 := h13324c.2.2.1
                          have p13324_3 := h13324c.2.2.2
                          linarith only [hlam, p13324_0]
                        · have p13324_0 := h13324c.1
                          have p13324_1 := h13324c.2.1
                          have p13324_2 := h13324c.2.2.1
                          have p13324_3 := h13324c.2.2.2
                          linarith only [h13262, hlam, p13324_0]
                        · have p13324_0 := h13324c.1
                          have p13324_1 := h13324c.2.1
                          have p13324_2 := h13324c.2.2.1
                          have p13324_3 := h13324c.2.2.2
                          linarith only [h13315, hlam, p13324_0]
                        · have p13324_0 := h13324c.1
                          have p13324_1 := h13324c.2.1
                          have p13324_2 := h13324c.2.2.1
                          have p13324_3 := h13324c.2.2.2
                          rcases p13324_3 (m.d 0 2) (by simp) with h13381 | h13381
                          · linarith only [h0, h13381, hlam]
                          · linarith only [h13259, h13381, hlam]
                        · have p13324_0 := h13324c.1
                          have p13324_1 := h13324c.2.1
                          have p13324_2 := h13324c.2.2.1
                          have p13324_3 := h13324c.2.2.2
                          rcases p13324_3 (m.d 0 2) (by simp) with h13384 | h13384
                          · linarith only [h13384, hlam, p13324_0]
                          · rcases p13324_3 (m.d 1 2) (by simp) with h13386 | h13386
                            · linarith only [h13262, h13386, hlam]
                            · linarith only [h0, h13386, hlam]
                        · have p13324_0 := h13324c.1
                          have p13324_1 := h13324c.2.1
                          have p13324_2 := h13324c.2.2.1
                          have p13324_3 := h13324c.2.2.2
                          linarith only [h0, hc01, hc23, hlam, hphi, ht12, p13324_1]
                        · have p13324_0 := h13324c.1
                          have p13324_1 := h13324c.2.1
                          have p13324_2 := h13324c.2.2.1
                          have p13324_3 := h13324c.2.2.2
                          linarith only [hlam, p13324_0]
                        · have p13324_0 := h13324c.1
                          have p13324_1 := h13324c.2.1
                          have p13324_2 := h13324c.2.2.1
                          have p13324_3 := h13324c.2.2.2
                          linarith only [h12751, h13259, h13321, h13323, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p13324_1]
                        · have p13324_0 := h13324c.1
                          have p13324_1 := h13324c.2.1
                          have p13324_2 := h13324c.2.2.1
                          have p13324_3 := h13324c.2.2.2
                          rcases p13324_3 (m.d 0 2) (by simp) with h13392 | h13392
                          · linarith only [h13392, h8886, hlam]
                          · linarith only [h13259, h13392, hlam]
                        · have p13324_0 := h13324c.1
                          have p13324_1 := h13324c.2.1
                          have p13324_2 := h13324c.2.2.1
                          have p13324_3 := h13324c.2.2.2
                          rcases p13324_3 (m.d 0 2) (by simp) with h13395 | h13395
                          · linarith only [h13395, hlam, p13324_0]
                          · rcases p13324_3 (m.d 1 2) (by simp) with h13397 | h13397
                            · linarith only [h13315, h13397, hlam]
                            · linarith only [h0, h13397, hlam]
                        · have p13324_0 := h13324c.1
                          have p13324_1 := h13324c.2.1
                          have p13324_2 := h13324c.2.2.1
                          have p13324_3 := h13324c.2.2.2
                          linarith only [h0, h13320, hc01, hc23, hlam, hphi, ht12, p13324_1]
                        · have p13324_0 := h13324c.1
                          have p13324_1 := h13324c.2.1
                          have p13324_2 := h13324c.2.2.1
                          have p13324_3 := h13324c.2.2.2
                          linarith only [h13320, hlam, p13324_0]
                        · have p13324_0 := h13324c.1
                          have p13324_1 := h13324c.2.1
                          have p13324_2 := h13324c.2.2.1
                          have p13324_3 := h13324c.2.2.2
                          linarith only [hlam, p13324_0]
                        · have p13324_0 := h13324c.1
                          have p13324_1 := h13324c.2.1
                          have p13324_2 := h13324c.2.2.1
                          have p13324_3 := h13324c.2.2.2
                          rcases p13324_3 (m.d 0 2) (by simp) with h13403 | h13403
                          · linarith only [h12751, h13403, hlam]
                          · linarith only [h13259, h13403, hlam]
                        · have p13324_0 := h13324c.1
                          have p13324_1 := h13324c.2.1
                          have p13324_2 := h13324c.2.2.1
                          have p13324_3 := h13324c.2.2.2
                          linarith only [h13259, hlam, p13324_0]
                        · have p13324_0 := h13324c.1
                          have p13324_1 := h13324c.2.1
                          have p13324_2 := h13324c.2.2.1
                          have p13324_3 := h13324c.2.2.2
                          linarith only [h13317, hlam, p13324_0]
                        · have p13324_0 := h13324c.1
                          have p13324_1 := h13324c.2.1
                          have p13324_2 := h13324c.2.2.1
                          have p13324_3 := h13324c.2.2.2
                          linarith only [h13321, hlam, p13324_0]
                        · have p13324_0 := h13324c.1
                          have p13324_1 := h13324c.2.1
                          have p13324_2 := h13324c.2.2.1
                          have p13324_3 := h13324c.2.2.2
                          linarith only [h13322, hlam, p13324_1]
                        · have p13324_0 := h13324c.1
                          have p13324_1 := h13324c.2.1
                          have p13324_2 := h13324c.2.2.1
                          have p13324_3 := h13324c.2.2.2
                          linarith only [hlam, p13324_0]
                      · rcases h2bigk with h13411c | h13411c | h13411c | h13411c | h13411c | h13411c | h13411c | h13411c | h13411c | h13411c | h13411c | h13411c | h13411c | h13411c | h13411c | h13411c | h13411c | h13411c | h13411c | h13411c | h13411c | h13411c | h13411c | h13411c | h13411c
                        · have p13411_0 := h13411c.1
                          have p13411_1 := h13411c.2.1
                          have p13411_2 := h13411c.2.2.1
                          have p13411_3 := h13411c.2.2.2
                          linarith only [hlam, p13411_0]
                        · have p13411_0 := h13411c.1
                          have p13411_1 := h13411c.2.1
                          have p13411_2 := h13411c.2.2.1
                          have p13411_3 := h13411c.2.2.2
                          linarith only [h0, hlam, p13411_0]
                        · have p13411_0 := h13411c.1
                          have p13411_1 := h13411c.2.1
                          have p13411_2 := h13411c.2.2.1
                          have p13411_3 := h13411c.2.2.2
                          linarith only [h8886, hlam, p13411_0]
                        · have p13411_0 := h13411c.1
                          have p13411_1 := h13411c.2.1
                          have p13411_2 := h13411c.2.2.1
                          have p13411_3 := h13411c.2.2.2
                          linarith only [h12751, hlam, p13411_0]
                        · have p13411_0 := h13411c.1
                          have p13411_1 := h13411c.2.1
                          have p13411_2 := h13411c.2.2.1
                          have p13411_3 := h13411c.2.2.2
                          linarith only [h13322, h13323, h8886, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p13411_1]
                        · have p13411_0 := h13411c.1
                          have p13411_1 := h13411c.2.1
                          have p13411_2 := h13411c.2.2.1
                          have p13411_3 := h13411c.2.2.2
                          linarith only [h13259, h13322, h13323, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p13411_1]
                        · have p13411_0 := h13411c.1
                          have p13411_1 := h13411c.2.1
                          have p13411_2 := h13411c.2.2.1
                          have p13411_3 := h13411c.2.2.2
                          linarith only [hlam, p13411_0]
                        · have p13411_0 := h13411c.1
                          have p13411_1 := h13411c.2.1
                          have p13411_2 := h13411c.2.2.1
                          have p13411_3 := h13411c.2.2.2
                          linarith only [h13262, hlam, p13411_0]
                        · have p13411_0 := h13411c.1
                          have p13411_1 := h13411c.2.1
                          have p13411_2 := h13411c.2.2.1
                          have p13411_3 := h13411c.2.2.2
                          linarith only [h13315, hlam, p13411_0]
                        · have p13411_0 := h13411c.1
                          have p13411_1 := h13411c.2.1
                          have p13411_2 := h13411c.2.2.1
                          have p13411_3 := h13411c.2.2.2
                          linarith only [h13315, h13320, h13322, h13323, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p13411_1]
                        · have p13411_0 := h13411c.1
                          have p13411_1 := h13411c.2.1
                          have p13411_2 := h13411c.2.2.1
                          have p13411_3 := h13411c.2.2.2
                          linarith only [h13259, h13322, h13323, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p13411_1]
                        · have p13411_0 := h13411c.1
                          have p13411_1 := h13411c.2.1
                          have p13411_2 := h13411c.2.2.1
                          have p13411_3 := h13411c.2.2.2
                          linarith only [h0, hc01, hc23, hlam, hphi, ht12, p13411_1]
                        · have p13411_0 := h13411c.1
                          have p13411_1 := h13411c.2.1
                          have p13411_2 := h13411c.2.2.1
                          have p13411_3 := h13411c.2.2.2
                          linarith only [hlam, p13411_0]
                        · have p13411_0 := h13411c.1
                          have p13411_1 := h13411c.2.1
                          have p13411_2 := h13411c.2.2.1
                          have p13411_3 := h13411c.2.2.2
                          linarith only [h12751, h13259, h13322, h13323, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p13411_1]
                        · have p13411_0 := h13411c.1
                          have p13411_1 := h13411c.2.1
                          have p13411_2 := h13411c.2.2.1
                          have p13411_3 := h13411c.2.2.2
                          rcases p13411_3 (m.d 0 2) (by simp) with h13426 | h13426
                          · linarith only [h13426, h8886, hlam]
                          · linarith only [h13259, h13426, hlam]
                        · have p13411_0 := h13411c.1
                          have p13411_1 := h13411c.2.1
                          have p13411_2 := h13411c.2.2.1
                          have p13411_3 := h13411c.2.2.2
                          linarith only [h13259, h13322, h13323, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p13411_1]
                        · have p13411_0 := h13411c.1
                          have p13411_1 := h13411c.2.1
                          have p13411_2 := h13411c.2.2.1
                          have p13411_3 := h13411c.2.2.2
                          linarith only [h0, h13259, h13322, h13323, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p13411_1]
                        · have p13411_0 := h13411c.1
                          have p13411_1 := h13411c.2.1
                          have p13411_2 := h13411c.2.2.1
                          have p13411_3 := h13411c.2.2.2
                          linarith only [h13320, hlam, p13411_0]
                        · have p13411_0 := h13411c.1
                          have p13411_1 := h13411c.2.1
                          have p13411_2 := h13411c.2.2.1
                          have p13411_3 := h13411c.2.2.2
                          linarith only [hlam, p13411_0]
                        · have p13411_0 := h13411c.1
                          have p13411_1 := h13411c.2.1
                          have p13411_2 := h13411c.2.2.1
                          have p13411_3 := h13411c.2.2.2
                          rcases p13411_3 (m.d 0 2) (by simp) with h13433 | h13433
                          · linarith only [h12751, h13433, hlam]
                          · linarith only [h13259, h13433, hlam]
                        · have p13411_0 := h13411c.1
                          have p13411_1 := h13411c.2.1
                          have p13411_2 := h13411c.2.2.1
                          have p13411_3 := h13411c.2.2.2
                          linarith only [h13259, hlam, p13411_0]
                        · have p13411_0 := h13411c.1
                          have p13411_1 := h13411c.2.1
                          have p13411_2 := h13411c.2.2.1
                          have p13411_3 := h13411c.2.2.2
                          linarith only [h13317, hlam, p13411_0]
                        · have p13411_0 := h13411c.1
                          have p13411_1 := h13411c.2.1
                          have p13411_2 := h13411c.2.2.1
                          have p13411_3 := h13411c.2.2.2
                          linarith only [h13321, hlam, p13411_0]
                        · have p13411_0 := h13411c.1
                          have p13411_1 := h13411c.2.1
                          have p13411_2 := h13411c.2.2.1
                          have p13411_3 := h13411c.2.2.2
                          linarith only [h13322, hlam, p13411_1]
                        · have p13411_0 := h13411c.1
                          have p13411_1 := h13411c.2.1
                          have p13411_2 := h13411c.2.2.1
                          have p13411_3 := h13411c.2.2.2
                          linarith only [hlam, p13411_0]
                    · linarith only [h12751, h13259, h13261, h13322, hc04, hc25, hlam, hphi, ht0b, ht5b]
                  · linarith only [h0, h13262, h13321, hc01, hc35, hlam, hphi, ht12, ht23]
                · linarith only [h0, h13262, h13320, hc01, hc34, hlam, hphi, ht12, ht23]
              · linarith only [h13261, h13319, h6874, hlam]
            · linarith only [h0, h13260, h13262, h13318, h8886, hc01, hc23, hlam, hphi, ht12]
          · linarith only [h0, h13259, h13317, hlam]
    · linarith only [h12751, h13259, h13261, hlam]
  · rcases m.htr 0 4 5 (by decide) (by decide) with h13448 | h13448
    · rcases m.htr 1 2 3 (by decide) (by decide) with h13449 | h13449
      · rcases m.htr 1 2 4 (by decide) (by decide) with h13450 | h13450
        · rcases m.htr 1 2 5 (by decide) (by decide) with h13451 | h13451
          · rcases m.htr 1 3 4 (by decide) (by decide) with h13452 | h13452
            · rcases m.htr 1 4 5 (by decide) (by decide) with h13453 | h13453
              · rcases m.htr 2 3 4 (by decide) (by decide) with h13454 | h13454
                · linarith only [h13259, h13260, h13449, h13454, h8886, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b]
                · linarith only [h13259, h13449, h13452, h13454, h8886, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b]
              · linarith only [h13448, h13453, h6874, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h13458 | h13458
              · rcases m.htr 2 3 4 (by decide) (by decide) with h13459 | h13459
                · linarith only [h13449, h13452, h13459, h6874, hc01, hc12, hlam, hphi]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h13461 | h13461
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h13462 | h13462
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h13463 | h13463
                      · rcases h2bigk with h13464c | h13464c | h13464c | h13464c | h13464c | h13464c | h13464c | h13464c | h13464c | h13464c | h13464c | h13464c | h13464c | h13464c | h13464c | h13464c | h13464c | h13464c | h13464c | h13464c | h13464c | h13464c | h13464c | h13464c | h13464c
                        · have p13464_0 := h13464c.1
                          have p13464_1 := h13464c.2.1
                          have p13464_2 := h13464c.2.2.1
                          have p13464_3 := h13464c.2.2.2
                          linarith only [hlam, p13464_0]
                        · have p13464_0 := h13464c.1
                          have p13464_1 := h13464c.2.1
                          have p13464_2 := h13464c.2.2.1
                          have p13464_3 := h13464c.2.2.2
                          linarith only [h0, hlam, p13464_0]
                        · have p13464_0 := h13464c.1
                          have p13464_1 := h13464c.2.1
                          have p13464_2 := h13464c.2.2.1
                          have p13464_3 := h13464c.2.2.2
                          linarith only [h8886, hlam, p13464_0]
                        · have p13464_0 := h13464c.1
                          have p13464_1 := h13464c.2.1
                          have p13464_2 := h13464c.2.2.1
                          have p13464_3 := h13464c.2.2.2
                          linarith only [h12751, hlam, p13464_0]
                        · have p13464_0 := h13464c.1
                          have p13464_1 := h13464c.2.1
                          have p13464_2 := h13464c.2.2.1
                          have p13464_3 := h13464c.2.2.2
                          linarith only [h13449, h13452, h13461, h13463, h8886, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p13464_1]
                        · have p13464_0 := h13464c.1
                          have p13464_1 := h13464c.2.1
                          have p13464_2 := h13464c.2.2.1
                          have p13464_3 := h13464c.2.2.2
                          rcases p13464_3 (m.d 0 2) (by simp) with h13470 | h13470
                          · linarith only [h0, h13470, hlam]
                          · rcases p13464_3 (m.d 1 2) (by simp) with h13472 | h13472
                            · rcases p13464_3 (m.d 2 3) (by simp) with h13473 | h13473
                              · linarith only [h13449, h13473, hlam]
                              · linarith only [h13473, h8886, hlam]
                            · linarith only [h0, h13472, hlam]
                        · have p13464_0 := h13464c.1
                          have p13464_1 := h13464c.2.1
                          have p13464_2 := h13464c.2.2.1
                          have p13464_3 := h13464c.2.2.2
                          linarith only [hlam, p13464_0]
                        · have p13464_0 := h13464c.1
                          have p13464_1 := h13464c.2.1
                          have p13464_2 := h13464c.2.2.1
                          have p13464_3 := h13464c.2.2.2
                          linarith only [h0, h8886, hc01, hc12, hlam, hphi, p13464_1]
                        · have p13464_0 := h13464c.1
                          have p13464_1 := h13464c.2.1
                          have p13464_2 := h13464c.2.2.1
                          have p13464_3 := h13464c.2.2.2
                          linarith only [h13259, h13459, h13461, h13463, h8886, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p13464_1]
                        · have p13464_0 := h13464c.1
                          have p13464_1 := h13464c.2.1
                          have p13464_2 := h13464c.2.2.1
                          have p13464_3 := h13464c.2.2.2
                          linarith only [h13259, h13449, h8886, hlam, p13464_2]
                        · have p13464_0 := h13464c.1
                          have p13464_1 := h13464c.2.1
                          have p13464_2 := h13464c.2.2.1
                          have p13464_3 := h13464c.2.2.2
                          linarith only [h13259, h13449, h13461, h13463, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p13464_1]
                        · have p13464_0 := h13464c.1
                          have p13464_1 := h13464c.2.1
                          have p13464_2 := h13464c.2.2.1
                          have p13464_3 := h13464c.2.2.2
                          linarith only [h13449, hlam, p13464_0]
                        · have p13464_0 := h13464c.1
                          have p13464_1 := h13464c.2.1
                          have p13464_2 := h13464c.2.2.1
                          have p13464_3 := h13464c.2.2.2
                          linarith only [hlam, p13464_0]
                        · have p13464_0 := h13464c.1
                          have p13464_1 := h13464c.2.1
                          have p13464_2 := h13464c.2.2.1
                          have p13464_3 := h13464c.2.2.2
                          linarith only [h13459, hlam, p13464_1]
                        · have p13464_0 := h13464c.1
                          have p13464_1 := h13464c.2.1
                          have p13464_2 := h13464c.2.2.1
                          have p13464_3 := h13464c.2.2.2
                          rcases p13464_3 (m.d 0 2) (by simp) with h13485 | h13485
                          · linarith only [h13485, h8886, hlam]
                          · linarith only [h13259, h13485, hlam]
                        · have p13464_0 := h13464c.1
                          have p13464_1 := h13464c.2.1
                          have p13464_2 := h13464c.2.2.1
                          have p13464_3 := h13464c.2.2.2
                          linarith only [h13259, h13450, h13461, h13463, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p13464_1]
                        · have p13464_0 := h13464c.1
                          have p13464_1 := h13464c.2.1
                          have p13464_2 := h13464c.2.2.1
                          have p13464_3 := h13464c.2.2.2
                          linarith only [h13450, hlam, p13464_0]
                        · have p13464_0 := h13464c.1
                          have p13464_1 := h13464c.2.1
                          have p13464_2 := h13464c.2.2.1
                          have p13464_3 := h13464c.2.2.2
                          linarith only [h13259, h13450, h13461, h13463, h8886, hc14, hc45, hlam, hphi, ht01, ht0b, ht5b, p13464_1]
                        · have p13464_0 := h13464c.1
                          have p13464_1 := h13464c.2.1
                          have p13464_2 := h13464c.2.2.1
                          have p13464_3 := h13464c.2.2.2
                          linarith only [hlam, p13464_0]
                        · have p13464_0 := h13464c.1
                          have p13464_1 := h13464c.2.1
                          have p13464_2 := h13464c.2.2.1
                          have p13464_3 := h13464c.2.2.2
                          rcases p13464_3 (m.d 0 2) (by simp) with h13492 | h13492
                          · linarith only [h12751, h13492, hlam]
                          · linarith only [h13259, h13492, hlam]
                        · have p13464_0 := h13464c.1
                          have p13464_1 := h13464c.2.1
                          have p13464_2 := h13464c.2.2.1
                          have p13464_3 := h13464c.2.2.2
                          linarith only [h13259, hlam, p13464_0]
                        · have p13464_0 := h13464c.1
                          have p13464_1 := h13464c.2.1
                          have p13464_2 := h13464c.2.2.1
                          have p13464_3 := h13464c.2.2.2
                          linarith only [h13451, hlam, p13464_0]
                        · have p13464_0 := h13464c.1
                          have p13464_1 := h13464c.2.1
                          have p13464_2 := h13464c.2.2.1
                          have p13464_3 := h13464c.2.2.2
                          linarith only [h13461, hlam, p13464_0]
                        · have p13464_0 := h13464c.1
                          have p13464_1 := h13464c.2.1
                          have p13464_2 := h13464c.2.2.1
                          have p13464_3 := h13464c.2.2.2
                          linarith only [h13462, hlam, p13464_1]
                        · have p13464_0 := h13464c.1
                          have p13464_1 := h13464c.2.1
                          have p13464_2 := h13464c.2.2.1
                          have p13464_3 := h13464c.2.2.2
                          linarith only [hlam, p13464_0]
                      · linarith only [h13448, h13452, h13463, h6874, hlam]
                    · linarith only [h12751, h13259, h13448, h13449, h13452, h13462, h6874, h8886, hc01, hc34, hlam, hphi, ht12, ht23]
                  · linarith only [h13259, h13461, h8886, hlam]
              · linarith only [h13448, h13458, h6874, hlam]
          · linarith only [h12751, h13259, h13449, h13450, h13451, h8886, hc04, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b]
        · linarith only [h13449, h13450, h8886, hc02, hc24, hlam, hphi]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h13506 | h13506
        · linarith only [h12751, h13259, h13449, h13506, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h13508 | h13508
          · rcases m.htr 1 3 4 (by decide) (by decide) with h13509 | h13509
            · rcases m.htr 1 4 5 (by decide) (by decide) with h13510 | h13510
              · rcases m.htr 2 3 4 (by decide) (by decide) with h13511 | h13511
                · rcases m.htr 2 3 5 (by decide) (by decide) with h13512 | h13512
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h13513 | h13513
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h13514 | h13514
                      · rcases h2bigk with h13515c | h13515c | h13515c | h13515c | h13515c | h13515c | h13515c | h13515c | h13515c | h13515c | h13515c | h13515c | h13515c | h13515c | h13515c | h13515c | h13515c | h13515c | h13515c | h13515c | h13515c | h13515c | h13515c | h13515c | h13515c
                        · have p13515_0 := h13515c.1
                          have p13515_1 := h13515c.2.1
                          have p13515_2 := h13515c.2.2.1
                          have p13515_3 := h13515c.2.2.2
                          linarith only [hlam, p13515_0]
                        · have p13515_0 := h13515c.1
                          have p13515_1 := h13515c.2.1
                          have p13515_2 := h13515c.2.2.1
                          have p13515_3 := h13515c.2.2.2
                          linarith only [h0, hlam, p13515_0]
                        · have p13515_0 := h13515c.1
                          have p13515_1 := h13515c.2.1
                          have p13515_2 := h13515c.2.2.1
                          have p13515_3 := h13515c.2.2.2
                          linarith only [h8886, hlam, p13515_0]
                        · have p13515_0 := h13515c.1
                          have p13515_1 := h13515c.2.1
                          have p13515_2 := h13515c.2.2.1
                          have p13515_3 := h13515c.2.2.2
                          linarith only [h12751, hlam, p13515_0]
                        · have p13515_0 := h13515c.1
                          have p13515_1 := h13515c.2.1
                          have p13515_2 := h13515c.2.2.1
                          have p13515_3 := h13515c.2.2.2
                          linarith only [h13260, h13509, h13512, h13514, h8886, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p13515_1]
                        · have p13515_0 := h13515c.1
                          have p13515_1 := h13515c.2.1
                          have p13515_2 := h13515c.2.2.1
                          have p13515_3 := h13515c.2.2.2
                          linarith only [h13506, h13511, hc02, hc23, hlam, hphi, p13515_1]
                        · have p13515_0 := h13515c.1
                          have p13515_1 := h13515c.2.1
                          have p13515_2 := h13515c.2.2.1
                          have p13515_3 := h13515c.2.2.2
                          linarith only [hlam, p13515_0]
                        · have p13515_0 := h13515c.1
                          have p13515_1 := h13515c.2.1
                          have p13515_2 := h13515c.2.2.1
                          have p13515_3 := h13515c.2.2.2
                          linarith only [h13449, hlam, p13515_0]
                        · have p13515_0 := h13515c.1
                          have p13515_1 := h13515c.2.1
                          have p13515_2 := h13515c.2.2.1
                          have p13515_3 := h13515c.2.2.2
                          linarith only [h13506, hlam, p13515_0]
                        · have p13515_0 := h13515c.1
                          have p13515_1 := h13515c.2.1
                          have p13515_2 := h13515c.2.2.1
                          have p13515_3 := h13515c.2.2.2
                          rcases p13515_3 (m.d 0 2) (by simp) with h13525 | h13525
                          · linarith only [h0, h13525, hlam]
                          · linarith only [h13259, h13525, hlam]
                        · have p13515_0 := h13515c.1
                          have p13515_1 := h13515c.2.1
                          have p13515_2 := h13515c.2.2.1
                          have p13515_3 := h13515c.2.2.2
                          rcases p13515_3 (m.d 0 2) (by simp) with h13528 | h13528
                          · linarith only [h13528, hlam, p13515_0]
                          · rcases p13515_3 (m.d 1 2) (by simp) with h13530 | h13530
                            · linarith only [h13449, h13530, hlam]
                            · linarith only [h0, h13530, hlam]
                        · have p13515_0 := h13515c.1
                          have p13515_1 := h13515c.2.1
                          have p13515_2 := h13515c.2.2.1
                          have p13515_3 := h13515c.2.2.2
                          linarith only [h0, hc01, hc23, hlam, hphi, ht12, p13515_1]
                        · have p13515_0 := h13515c.1
                          have p13515_1 := h13515c.2.1
                          have p13515_2 := h13515c.2.2.1
                          have p13515_3 := h13515c.2.2.2
                          linarith only [hlam, p13515_0]
                        · have p13515_0 := h13515c.1
                          have p13515_1 := h13515c.2.1
                          have p13515_2 := h13515c.2.2.1
                          have p13515_3 := h13515c.2.2.2
                          linarith only [h12751, h13259, h13512, h13514, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p13515_1]
                        · have p13515_0 := h13515c.1
                          have p13515_1 := h13515c.2.1
                          have p13515_2 := h13515c.2.2.1
                          have p13515_3 := h13515c.2.2.2
                          linarith only [h13259, h13260, h13449, h13509, h8886, hlam, p13515_2]
                        · have p13515_0 := h13515c.1
                          have p13515_1 := h13515c.2.1
                          have p13515_2 := h13515c.2.2.1
                          have p13515_3 := h13515c.2.2.2
                          rcases p13515_3 (m.d 0 2) (by simp) with h13537 | h13537
                          · linarith only [h13537, hlam, p13515_0]
                          · rcases p13515_3 (m.d 1 2) (by simp) with h13539 | h13539
                            · linarith only [h13506, h13539, hlam]
                            · linarith only [h0, h13539, hlam]
                        · have p13515_0 := h13515c.1
                          have p13515_1 := h13515c.2.1
                          have p13515_2 := h13515c.2.2.1
                          have p13515_3 := h13515c.2.2.2
                          linarith only [h0, hc01, hc24, hlam, hphi, ht12, p13515_1]
                        · have p13515_0 := h13515c.1
                          have p13515_1 := h13515c.2.1
                          have p13515_2 := h13515c.2.2.1
                          have p13515_3 := h13515c.2.2.2
                          linarith only [h13511, hlam, p13515_0]
                        · have p13515_0 := h13515c.1
                          have p13515_1 := h13515c.2.1
                          have p13515_2 := h13515c.2.2.1
                          have p13515_3 := h13515c.2.2.2
                          linarith only [hlam, p13515_0]
                        · have p13515_0 := h13515c.1
                          have p13515_1 := h13515c.2.1
                          have p13515_2 := h13515c.2.2.1
                          have p13515_3 := h13515c.2.2.2
                          rcases p13515_3 (m.d 0 2) (by simp) with h13545 | h13545
                          · linarith only [h12751, h13545, hlam]
                          · linarith only [h13259, h13545, hlam]
                        · have p13515_0 := h13515c.1
                          have p13515_1 := h13515c.2.1
                          have p13515_2 := h13515c.2.2.1
                          have p13515_3 := h13515c.2.2.2
                          linarith only [h13259, hlam, p13515_0]
                        · have p13515_0 := h13515c.1
                          have p13515_1 := h13515c.2.1
                          have p13515_2 := h13515c.2.2.1
                          have p13515_3 := h13515c.2.2.2
                          linarith only [h13508, hlam, p13515_0]
                        · have p13515_0 := h13515c.1
                          have p13515_1 := h13515c.2.1
                          have p13515_2 := h13515c.2.2.1
                          have p13515_3 := h13515c.2.2.2
                          linarith only [h13512, hlam, p13515_0]
                        · have p13515_0 := h13515c.1
                          have p13515_1 := h13515c.2.1
                          have p13515_2 := h13515c.2.2.1
                          have p13515_3 := h13515c.2.2.2
                          linarith only [h13513, hlam, p13515_1]
                        · have p13515_0 := h13515c.1
                          have p13515_1 := h13515c.2.1
                          have p13515_2 := h13515c.2.2.1
                          have p13515_3 := h13515c.2.2.2
                          linarith only [hlam, p13515_0]
                      · linarith only [h13259, h13260, h13448, h13514, h8886, hc04, hc25, hlam, hphi, ht0b, ht5b]
                    · linarith only [h12751, h13259, h13448, h13513, hlam]
                  · linarith only [h0, h13449, h13512, hc01, hc35, hlam, hphi, ht12, ht23]
                · linarith only [h13449, h13509, h13511, hlam]
              · linarith only [h13259, h13260, h13448, h13509, h13510, h6874, h8886, hc01, hc13, hlam, hphi]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h13558 | h13558
              · rcases m.htr 2 3 4 (by decide) (by decide) with h13559 | h13559
                · linarith only [h0, h13449, h13509, h13559, hc01, hc23, hlam, hphi, ht12]
                · linarith only [h0, h13449, h13559, hc01, hc34, hlam, hphi, ht12, ht23]
              · linarith only [h0, h13259, h13448, h13449, h13558, h6874, hc01, hc23, hlam, hphi, ht12]
          · linarith only [h13259, h13260, h13508, h8886, hc12, hc34, hlam, hphi, ht23]
    · linarith only [h13259, h13260, h13448, h8886, hlam]

end R2N4
