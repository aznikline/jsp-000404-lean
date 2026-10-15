import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6230000 in
set_option maxHeartbeats 6230000 in
theorem r1l7_20_12_14_H_I_L_I_L_I_s9_x1_x1_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6421 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg7464 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h8188 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h8818 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h10104 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
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
  have h0bigk := hb0.1
  have h0 := hg0
  have h6421 := hg6421
  have h7464 := hg7464
  rcases m.htr 0 2 5 (by decide) (by decide) with h10105 | h10105
  · rcases m.htr 0 3 4 (by decide) (by decide) with h10106 | h10106
    · rcases m.htr 0 3 5 (by decide) (by decide) with h10107 | h10107
      · rcases m.htr 0 4 5 (by decide) (by decide) with h10108 | h10108
        · rcases m.htr 1 2 3 (by decide) (by decide) with h10109 | h10109
          · rcases m.htr 1 2 4 (by decide) (by decide) with h10110 | h10110
            · rcases m.htr 1 2 5 (by decide) (by decide) with h10111 | h10111
              · rcases m.htr 1 3 4 (by decide) (by decide) with h10112 | h10112
                · rcases m.htr 1 4 5 (by decide) (by decide) with h10113 | h10113
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h10114 | h10114
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h10115 | h10115
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h10116 | h10116
                        · linarith only [h10104, h10109, h10116, h8818, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                        · linarith only [h10104, h10108, h10109, h10116, h8818, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · linarith only [h10105, h10107, h10115, h8818, hc03, hc25, hlam, hphi, ht0b, ht5b]
                    · linarith only [h10106, h10114, h8818, hlam]
                  · linarith only [h0, h10104, h10108, h10113, h7464, hc01, hc12, hlam, hphi]
                · linarith only [h10104, h10106, h10112, h6421, h8818, hc01, hc23, hlam, hphi, ht12]
              · linarith only [h10109, h10111, h8818, hc02, hc25, hlam, hphi]
            · linarith only [h10104, h10109, h10110, h8818, hlam]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h10125 | h10125
            · rcases m.htr 1 2 5 (by decide) (by decide) with h10126 | h10126
              · rcases m.htr 1 3 4 (by decide) (by decide) with h10127 | h10127
                · rcases m.htr 1 4 5 (by decide) (by decide) with h10128 | h10128
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h10129 | h10129
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h10130 | h10130
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h10131 | h10131
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h10132 | h10132
                          · rcases h0bigk with h10133c | h10133c | h10133c | h10133c | h10133c | h10133c | h10133c | h10133c | h10133c | h10133c | h10133c | h10133c | h10133c | h10133c | h10133c | h10133c | h10133c | h10133c | h10133c | h10133c | h10133c | h10133c | h10133c | h10133c | h10133c
                            · have p10133_0 := h10133c.1
                              have p10133_1 := h10133c.2.1
                              have p10133_2 := h10133c.2.2.1
                              have p10133_3 := h10133c.2.2.2
                              linarith only [hlam, p10133_0]
                            · have p10133_0 := h10133c.1
                              have p10133_1 := h10133c.2.1
                              have p10133_2 := h10133c.2.2.1
                              have p10133_3 := h10133c.2.2.2
                              linarith only [h0, hlam, p10133_1]
                            · have p10133_0 := h10133c.1
                              have p10133_1 := h10133c.2.1
                              have p10133_2 := h10133c.2.2.1
                              have p10133_3 := h10133c.2.2.2
                              linarith only [h6421, hlam, p10133_0]
                            · have p10133_0 := h10133c.1
                              have p10133_1 := h10133c.2.1
                              have p10133_2 := h10133c.2.2.1
                              have p10133_3 := h10133c.2.2.2
                              linarith only [h7464, hlam, p10133_1]
                            · have p10133_0 := h10133c.1
                              have p10133_1 := h10133c.2.1
                              have p10133_2 := h10133c.2.2.1
                              have p10133_3 := h10133c.2.2.2
                              linarith only [h8188, hlam, p10133_1]
                            · have p10133_0 := h10133c.1
                              have p10133_1 := h10133c.2.1
                              have p10133_2 := h10133c.2.2.1
                              have p10133_3 := h10133c.2.2.2
                              linarith only [h0, hc01, hc12, hlam, hphi, p10133_1]
                            · have p10133_0 := h10133c.1
                              have p10133_1 := h10133c.2.1
                              have p10133_2 := h10133c.2.2.1
                              have p10133_3 := h10133c.2.2.2
                              linarith only [hlam, p10133_0]
                            · have p10133_0 := h10133c.1
                              have p10133_1 := h10133c.2.1
                              have p10133_2 := h10133c.2.2.1
                              have p10133_3 := h10133c.2.2.2
                              linarith only [h8818, hlam, p10133_0]
                            · have p10133_0 := h10133c.1
                              have p10133_1 := h10133c.2.1
                              have p10133_2 := h10133c.2.2.1
                              have p10133_3 := h10133c.2.2.2
                              linarith only [h0, h10109, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p10133_1]
                            · have p10133_0 := h10133c.1
                              have p10133_1 := h10133c.2.1
                              have p10133_2 := h10133c.2.2.1
                              have p10133_3 := h10133c.2.2.2
                              linarith only [h0, h10109, h8188, hc01, hc23, hlam, hphi, ht12, p10133_1]
                            · have p10133_0 := h10133c.1
                              have p10133_1 := h10133c.2.1
                              have p10133_2 := h10133c.2.2.1
                              have p10133_3 := h10133c.2.2.2
                              linarith only [h8818, hc01, hc23, hlam, hphi, ht12, p10133_1]
                            · have p10133_0 := h10133c.1
                              have p10133_1 := h10133c.2.1
                              have p10133_2 := h10133c.2.2.1
                              have p10133_3 := h10133c.2.2.2
                              linarith only [h8818, hc02, hc23, hlam, hphi, p10133_1]
                            · have p10133_0 := h10133c.1
                              have p10133_1 := h10133c.2.1
                              have p10133_2 := h10133c.2.2.1
                              have p10133_3 := h10133c.2.2.2
                              linarith only [hlam, p10133_0]
                            · have p10133_0 := h10133c.1
                              have p10133_1 := h10133c.2.1
                              have p10133_2 := h10133c.2.2.1
                              have p10133_3 := h10133c.2.2.2
                              linarith only [h10104, h10129, h10132, h8818, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p10133_1]
                            · have p10133_0 := h10133c.1
                              have p10133_1 := h10133c.2.1
                              have p10133_2 := h10133c.2.2.1
                              have p10133_3 := h10133c.2.2.2
                              linarith only [h8188, h8818, hc01, hc23, hlam, hphi, ht12, p10133_1]
                            · have p10133_0 := h10133c.1
                              have p10133_1 := h10133c.2.1
                              have p10133_2 := h10133c.2.2.1
                              have p10133_3 := h10133c.2.2.2
                              linarith only [h7464, hc01, hc14, hlam, hphi, p10133_1]
                            · have p10133_0 := h10133c.1
                              have p10133_1 := h10133c.2.1
                              have p10133_2 := h10133c.2.2.1
                              have p10133_3 := h10133c.2.2.2
                              linarith only [h10104, hlam, p10133_0]
                            · have p10133_0 := h10133c.1
                              have p10133_1 := h10133c.2.1
                              have p10133_2 := h10133c.2.2.1
                              have p10133_3 := h10133c.2.2.2
                              linarith only [h10106, hlam, p10133_0]
                            · have p10133_0 := h10133c.1
                              have p10133_1 := h10133c.2.1
                              have p10133_2 := h10133c.2.2.1
                              have p10133_3 := h10133c.2.2.2
                              linarith only [hlam, p10133_0]
                            · have p10133_0 := h10133c.1
                              have p10133_1 := h10133c.2.1
                              have p10133_2 := h10133c.2.2.1
                              have p10133_3 := h10133c.2.2.2
                              linarith only [h0, h10104, h10109, h8188, hc01, hc23, hlam, hphi, ht12, p10133_1]
                            · have p10133_0 := h10133c.1
                              have p10133_1 := h10133c.2.1
                              have p10133_2 := h10133c.2.2.1
                              have p10133_3 := h10133c.2.2.2
                              linarith only [h8188, hc01, hc15, hlam, hphi, p10133_1]
                            · have p10133_0 := h10133c.1
                              have p10133_1 := h10133c.2.1
                              have p10133_2 := h10133c.2.2.1
                              have p10133_3 := h10133c.2.2.2
                              linarith only [h10105, hlam, p10133_1]
                            · have p10133_0 := h10133c.1
                              have p10133_1 := h10133c.2.1
                              have p10133_2 := h10133c.2.2.1
                              have p10133_3 := h10133c.2.2.2
                              linarith only [h10107, hlam, p10133_0]
                            · have p10133_0 := h10133c.1
                              have p10133_1 := h10133c.2.1
                              have p10133_2 := h10133c.2.2.1
                              have p10133_3 := h10133c.2.2.2
                              linarith only [h10108, hlam, p10133_1]
                            · have p10133_0 := h10133c.1
                              have p10133_1 := h10133c.2.1
                              have p10133_2 := h10133c.2.2.1
                              have p10133_3 := h10133c.2.2.2
                              linarith only [hlam, p10133_0]
                          · linarith only [h0, h10104, h10109, h10131, h10132, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h10160 | h10160
                          · linarith only [h10129, h10131, h10160, hlam]
                          · rcases h0bigk with h10162c | h10162c | h10162c | h10162c | h10162c | h10162c | h10162c | h10162c | h10162c | h10162c | h10162c | h10162c | h10162c | h10162c | h10162c | h10162c | h10162c | h10162c | h10162c | h10162c | h10162c | h10162c | h10162c | h10162c | h10162c
                            · have p10162_0 := h10162c.1
                              have p10162_1 := h10162c.2.1
                              have p10162_2 := h10162c.2.2.1
                              have p10162_3 := h10162c.2.2.2
                              linarith only [hlam, p10162_0]
                            · have p10162_0 := h10162c.1
                              have p10162_1 := h10162c.2.1
                              have p10162_2 := h10162c.2.2.1
                              have p10162_3 := h10162c.2.2.2
                              linarith only [h0, hlam, p10162_1]
                            · have p10162_0 := h10162c.1
                              have p10162_1 := h10162c.2.1
                              have p10162_2 := h10162c.2.2.1
                              have p10162_3 := h10162c.2.2.2
                              linarith only [h6421, hlam, p10162_0]
                            · have p10162_0 := h10162c.1
                              have p10162_1 := h10162c.2.1
                              have p10162_2 := h10162c.2.2.1
                              have p10162_3 := h10162c.2.2.2
                              linarith only [h7464, hlam, p10162_1]
                            · have p10162_0 := h10162c.1
                              have p10162_1 := h10162c.2.1
                              have p10162_2 := h10162c.2.2.1
                              have p10162_3 := h10162c.2.2.2
                              linarith only [h8188, hlam, p10162_1]
                            · have p10162_0 := h10162c.1
                              have p10162_1 := h10162c.2.1
                              have p10162_2 := h10162c.2.2.1
                              have p10162_3 := h10162c.2.2.2
                              linarith only [h0, h10109, hc01, hc23, hlam, hphi, ht12, p10162_1]
                            · have p10162_0 := h10162c.1
                              have p10162_1 := h10162c.2.1
                              have p10162_2 := h10162c.2.2.1
                              have p10162_3 := h10162c.2.2.2
                              linarith only [hlam, p10162_0]
                            · have p10162_0 := h10162c.1
                              have p10162_1 := h10162c.2.1
                              have p10162_2 := h10162c.2.2.1
                              have p10162_3 := h10162c.2.2.2
                              linarith only [h8818, hlam, p10162_0]
                            · have p10162_0 := h10162c.1
                              have p10162_1 := h10162c.2.1
                              have p10162_2 := h10162c.2.2.1
                              have p10162_3 := h10162c.2.2.2
                              linarith only [h0, h10108, h10109, h10129, h10131, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p10162_1]
                            · have p10162_0 := h10162c.1
                              have p10162_1 := h10162c.2.1
                              have p10162_2 := h10162c.2.2.1
                              have p10162_3 := h10162c.2.2.2
                              linarith only [h0, h10109, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p10162_1]
                            · have p10162_0 := h10162c.1
                              have p10162_1 := h10162c.2.1
                              have p10162_2 := h10162c.2.2.1
                              have p10162_3 := h10162c.2.2.2
                              linarith only [h10109, h6421, hc01, hc23, hlam, hphi, ht12, p10162_1]
                            · have p10162_0 := h10162c.1
                              have p10162_1 := h10162c.2.1
                              have p10162_2 := h10162c.2.2.1
                              have p10162_3 := h10162c.2.2.2
                              linarith only [h10109, h6421, hc02, hc23, hlam, hphi, p10162_1]
                            · have p10162_0 := h10162c.1
                              have p10162_1 := h10162c.2.1
                              have p10162_2 := h10162c.2.2.1
                              have p10162_3 := h10162c.2.2.2
                              linarith only [hlam, p10162_0]
                            · have p10162_0 := h10162c.1
                              have p10162_1 := h10162c.2.1
                              have p10162_2 := h10162c.2.2.1
                              have p10162_3 := h10162c.2.2.2
                              linarith only [h10108, h10109, h10129, h10131, h6421, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p10162_1]
                            · have p10162_0 := h10162c.1
                              have p10162_1 := h10162c.2.1
                              have p10162_2 := h10162c.2.2.1
                              have p10162_3 := h10162c.2.2.2
                              linarith only [h10109, h6421, h8188, hc01, hc23, hlam, hphi, ht12, p10162_1]
                            · have p10162_0 := h10162c.1
                              have p10162_1 := h10162c.2.1
                              have p10162_2 := h10162c.2.2.1
                              have p10162_3 := h10162c.2.2.2
                              linarith only [h0, h10104, h10109, hc01, hc23, hlam, hphi, ht12, p10162_1]
                            · have p10162_0 := h10162c.1
                              have p10162_1 := h10162c.2.1
                              have p10162_2 := h10162c.2.2.1
                              have p10162_3 := h10162c.2.2.2
                              linarith only [h10104, hlam, p10162_0]
                            · have p10162_0 := h10162c.1
                              have p10162_1 := h10162c.2.1
                              have p10162_2 := h10162c.2.2.1
                              have p10162_3 := h10162c.2.2.2
                              linarith only [h10106, hlam, p10162_0]
                            · have p10162_0 := h10162c.1
                              have p10162_1 := h10162c.2.1
                              have p10162_2 := h10162c.2.2.1
                              have p10162_3 := h10162c.2.2.2
                              linarith only [hlam, p10162_0]
                            · have p10162_0 := h10162c.1
                              have p10162_1 := h10162c.2.1
                              have p10162_2 := h10162c.2.2.1
                              have p10162_3 := h10162c.2.2.2
                              linarith only [h0, h10104, h10109, h8188, hc01, hc23, hlam, hphi, ht12, p10162_1]
                            · have p10162_0 := h10162c.1
                              have p10162_1 := h10162c.2.1
                              have p10162_2 := h10162c.2.2.1
                              have p10162_3 := h10162c.2.2.2
                              linarith only [h10109, h10125, h10128, h8188, hc01, hc23, hlam, hphi, ht12, p10162_1]
                            · have p10162_0 := h10162c.1
                              have p10162_1 := h10162c.2.1
                              have p10162_2 := h10162c.2.2.1
                              have p10162_3 := h10162c.2.2.2
                              linarith only [h10105, hlam, p10162_1]
                            · have p10162_0 := h10162c.1
                              have p10162_1 := h10162c.2.1
                              have p10162_2 := h10162c.2.2.1
                              have p10162_3 := h10162c.2.2.2
                              linarith only [h10107, hlam, p10162_0]
                            · have p10162_0 := h10162c.1
                              have p10162_1 := h10162c.2.1
                              have p10162_2 := h10162c.2.2.1
                              have p10162_3 := h10162c.2.2.2
                              linarith only [h10108, hlam, p10162_1]
                            · have p10162_0 := h10162c.1
                              have p10162_1 := h10162c.2.1
                              have p10162_2 := h10162c.2.2.1
                              have p10162_3 := h10162c.2.2.2
                              linarith only [hlam, p10162_0]
                      · linarith only [h0, h10109, h10130, hc01, hc35, hlam, hphi, ht12, ht23]
                    · linarith only [h0, h10109, h10129, hc01, hc34, hlam, hphi, ht12, ht23]
                  · linarith only [h0, h10104, h10108, h10128, h7464, hc01, hc12, hlam, hphi]
                · linarith only [h0, h10104, h10106, h10109, h10127, h6421, hc01, hc23, hlam, hphi, ht12]
              · linarith only [h0, h10105, h10126, hlam]
            · linarith only [h0, h10104, h10125, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h10194 | h10194
          · rcases m.htr 1 2 4 (by decide) (by decide) with h10195 | h10195
            · rcases m.htr 1 2 5 (by decide) (by decide) with h10196 | h10196
              · rcases m.htr 1 3 4 (by decide) (by decide) with h10197 | h10197
                · rcases m.htr 1 4 5 (by decide) (by decide) with h10198 | h10198
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h10199 | h10199
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h10200 | h10200
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h10201 | h10201
                        · linarith only [h10104, h10108, h10194, h10201, h8818, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h10203 | h10203
                          · linarith only [h10105, h10108, h10194, h10199, h10201, h10203, h7464, h8818, hc01, hc12, hlam, hphi]
                          · rcases h0bigk with h10205c | h10205c | h10205c | h10205c | h10205c | h10205c | h10205c | h10205c | h10205c | h10205c | h10205c | h10205c | h10205c | h10205c | h10205c | h10205c | h10205c | h10205c | h10205c | h10205c | h10205c | h10205c | h10205c | h10205c | h10205c
                            · have p10205_0 := h10205c.1
                              have p10205_1 := h10205c.2.1
                              have p10205_2 := h10205c.2.2.1
                              have p10205_3 := h10205c.2.2.2
                              linarith only [hlam, p10205_0]
                            · have p10205_0 := h10205c.1
                              have p10205_1 := h10205c.2.1
                              have p10205_2 := h10205c.2.2.1
                              have p10205_3 := h10205c.2.2.2
                              linarith only [h0, hlam, p10205_1]
                            · have p10205_0 := h10205c.1
                              have p10205_1 := h10205c.2.1
                              have p10205_2 := h10205c.2.2.1
                              have p10205_3 := h10205c.2.2.2
                              linarith only [h6421, hlam, p10205_0]
                            · have p10205_0 := h10205c.1
                              have p10205_1 := h10205c.2.1
                              have p10205_2 := h10205c.2.2.1
                              have p10205_3 := h10205c.2.2.2
                              linarith only [h7464, hlam, p10205_1]
                            · have p10205_0 := h10205c.1
                              have p10205_1 := h10205c.2.1
                              have p10205_2 := h10205c.2.2.1
                              have p10205_3 := h10205c.2.2.2
                              linarith only [h8188, hlam, p10205_1]
                            · have p10205_0 := h10205c.1
                              have p10205_1 := h10205c.2.1
                              have p10205_2 := h10205c.2.2.1
                              have p10205_3 := h10205c.2.2.2
                              linarith only [h10194, h8818, hc01, hc12, hlam, hphi, p10205_1]
                            · have p10205_0 := h10205c.1
                              have p10205_1 := h10205c.2.1
                              have p10205_2 := h10205c.2.2.1
                              have p10205_3 := h10205c.2.2.2
                              linarith only [hlam, p10205_0]
                            · have p10205_0 := h10205c.1
                              have p10205_1 := h10205c.2.1
                              have p10205_2 := h10205c.2.2.1
                              have p10205_3 := h10205c.2.2.2
                              linarith only [h8818, hlam, p10205_0]
                            · have p10205_0 := h10205c.1
                              have p10205_1 := h10205c.2.1
                              have p10205_2 := h10205c.2.2.1
                              have p10205_3 := h10205c.2.2.2
                              linarith only [h10194, h7464, h8818, hc01, hc12, hlam, hphi, p10205_1]
                            · have p10205_0 := h10205c.1
                              have p10205_1 := h10205c.2.1
                              have p10205_2 := h10205c.2.2.1
                              have p10205_3 := h10205c.2.2.2
                              linarith only [h10194, h8818, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p10205_1]
                            · have p10205_0 := h10205c.1
                              have p10205_1 := h10205c.2.1
                              have p10205_2 := h10205c.2.2.1
                              have p10205_3 := h10205c.2.2.2
                              linarith only [h6421, hc01, hc13, hlam, hphi, p10205_1]
                            · have p10205_0 := h10205c.1
                              have p10205_1 := h10205c.2.1
                              have p10205_2 := h10205c.2.2.1
                              have p10205_3 := h10205c.2.2.2
                              linarith only [h10194, h8818, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p10205_1]
                            · have p10205_0 := h10205c.1
                              have p10205_1 := h10205c.2.1
                              have p10205_2 := h10205c.2.2.1
                              have p10205_3 := h10205c.2.2.2
                              linarith only [hlam, p10205_0]
                            · have p10205_0 := h10205c.1
                              have p10205_1 := h10205c.2.1
                              have p10205_2 := h10205c.2.2.1
                              have p10205_3 := h10205c.2.2.2
                              linarith only [h10194, h7464, h8818, hc01, hc12, hlam, hphi, p10205_1]
                            · have p10205_0 := h10205c.1
                              have p10205_1 := h10205c.2.1
                              have p10205_2 := h10205c.2.2.1
                              have p10205_3 := h10205c.2.2.2
                              linarith only [h10194, h8188, h8818, hc01, hc12, hlam, hphi, p10205_1]
                            · have p10205_0 := h10205c.1
                              have p10205_1 := h10205c.2.1
                              have p10205_2 := h10205c.2.2.1
                              have p10205_3 := h10205c.2.2.2
                              linarith only [h10108, h10198, hc01, hc14, hlam, hphi, p10205_1]
                            · have p10205_0 := h10205c.1
                              have p10205_1 := h10205c.2.1
                              have p10205_2 := h10205c.2.2.1
                              have p10205_3 := h10205c.2.2.2
                              linarith only [h10104, hlam, p10205_0]
                            · have p10205_0 := h10205c.1
                              have p10205_1 := h10205c.2.1
                              have p10205_2 := h10205c.2.2.1
                              have p10205_3 := h10205c.2.2.2
                              linarith only [h10106, hlam, p10205_0]
                            · have p10205_0 := h10205c.1
                              have p10205_1 := h10205c.2.1
                              have p10205_2 := h10205c.2.2.1
                              have p10205_3 := h10205c.2.2.2
                              linarith only [hlam, p10205_0]
                            · have p10205_0 := h10205c.1
                              have p10205_1 := h10205c.2.1
                              have p10205_2 := h10205c.2.2.1
                              have p10205_3 := h10205c.2.2.2
                              linarith only [h10108, hlam, p10205_0]
                            · have p10205_0 := h10205c.1
                              have p10205_1 := h10205c.2.1
                              have p10205_2 := h10205c.2.2.1
                              have p10205_3 := h10205c.2.2.2
                              linarith only [h8188, hc01, hc15, hlam, hphi, p10205_1]
                            · have p10205_0 := h10205c.1
                              have p10205_1 := h10205c.2.1
                              have p10205_2 := h10205c.2.2.1
                              have p10205_3 := h10205c.2.2.2
                              linarith only [h10105, hlam, p10205_1]
                            · have p10205_0 := h10205c.1
                              have p10205_1 := h10205c.2.1
                              have p10205_2 := h10205c.2.2.1
                              have p10205_3 := h10205c.2.2.2
                              linarith only [h10107, hlam, p10205_0]
                            · have p10205_0 := h10205c.1
                              have p10205_1 := h10205c.2.1
                              have p10205_2 := h10205c.2.2.1
                              have p10205_3 := h10205c.2.2.2
                              linarith only [h0, h10105, h7464, hc01, hc12, hlam, hphi, p10205_1]
                            · have p10205_0 := h10205c.1
                              have p10205_1 := h10205c.2.1
                              have p10205_2 := h10205c.2.2.1
                              have p10205_3 := h10205c.2.2.2
                              linarith only [hlam, p10205_0]
                      · linarith only [h10107, h10200, h8818, hlam]
                    · linarith only [h10106, h10199, h8818, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h10233 | h10233
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h10234 | h10234
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h10235 | h10235
                        · linarith only [h10104, h10198, h10235, h8818, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h10237 | h10237
                          · linarith only [h10198, h10237, h7464, hc01, hc34, hlam, hphi, ht12, ht23]
                          · rcases h0bigk with h10239c | h10239c | h10239c | h10239c | h10239c | h10239c | h10239c | h10239c | h10239c | h10239c | h10239c | h10239c | h10239c | h10239c | h10239c | h10239c | h10239c | h10239c | h10239c | h10239c | h10239c | h10239c | h10239c | h10239c | h10239c
                            · have p10239_0 := h10239c.1
                              have p10239_1 := h10239c.2.1
                              have p10239_2 := h10239c.2.2.1
                              have p10239_3 := h10239c.2.2.2
                              linarith only [hlam, p10239_0]
                            · have p10239_0 := h10239c.1
                              have p10239_1 := h10239c.2.1
                              have p10239_2 := h10239c.2.2.1
                              have p10239_3 := h10239c.2.2.2
                              linarith only [h0, hlam, p10239_1]
                            · have p10239_0 := h10239c.1
                              have p10239_1 := h10239c.2.1
                              have p10239_2 := h10239c.2.2.1
                              have p10239_3 := h10239c.2.2.2
                              linarith only [h6421, hlam, p10239_0]
                            · have p10239_0 := h10239c.1
                              have p10239_1 := h10239c.2.1
                              have p10239_2 := h10239c.2.2.1
                              have p10239_3 := h10239c.2.2.2
                              linarith only [h7464, hlam, p10239_1]
                            · have p10239_0 := h10239c.1
                              have p10239_1 := h10239c.2.1
                              have p10239_2 := h10239c.2.2.1
                              have p10239_3 := h10239c.2.2.2
                              linarith only [h8188, hlam, p10239_1]
                            · have p10239_0 := h10239c.1
                              have p10239_1 := h10239c.2.1
                              have p10239_2 := h10239c.2.2.1
                              have p10239_3 := h10239c.2.2.2
                              linarith only [h10194, h8818, hc01, hc12, hlam, hphi, p10239_1]
                            · have p10239_0 := h10239c.1
                              have p10239_1 := h10239c.2.1
                              have p10239_2 := h10239c.2.2.1
                              have p10239_3 := h10239c.2.2.2
                              linarith only [hlam, p10239_0]
                            · have p10239_0 := h10239c.1
                              have p10239_1 := h10239c.2.1
                              have p10239_2 := h10239c.2.2.1
                              have p10239_3 := h10239c.2.2.2
                              linarith only [h8818, hlam, p10239_0]
                            · have p10239_0 := h10239c.1
                              have p10239_1 := h10239c.2.1
                              have p10239_2 := h10239c.2.2.1
                              have p10239_3 := h10239c.2.2.2
                              linarith only [h10194, h7464, h8818, hc01, hc12, hlam, hphi, p10239_1]
                            · have p10239_0 := h10239c.1
                              have p10239_1 := h10239c.2.1
                              have p10239_2 := h10239c.2.2.1
                              have p10239_3 := h10239c.2.2.2
                              linarith only [h10194, h8818, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p10239_1]
                            · have p10239_0 := h10239c.1
                              have p10239_1 := h10239c.2.1
                              have p10239_2 := h10239c.2.2.1
                              have p10239_3 := h10239c.2.2.2
                              linarith only [h10194, h8818, hc01, hc12, hlam, hphi, p10239_1]
                            · have p10239_0 := h10239c.1
                              have p10239_1 := h10239c.2.1
                              have p10239_2 := h10239c.2.2.1
                              have p10239_3 := h10239c.2.2.2
                              linarith only [h10194, h8818, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p10239_1]
                            · have p10239_0 := h10239c.1
                              have p10239_1 := h10239c.2.1
                              have p10239_2 := h10239c.2.2.1
                              have p10239_3 := h10239c.2.2.2
                              linarith only [hlam, p10239_0]
                            · have p10239_0 := h10239c.1
                              have p10239_1 := h10239c.2.1
                              have p10239_2 := h10239c.2.2.1
                              have p10239_3 := h10239c.2.2.2
                              linarith only [h10194, h7464, h8818, hc01, hc12, hlam, hphi, p10239_1]
                            · have p10239_0 := h10239c.1
                              have p10239_1 := h10239c.2.1
                              have p10239_2 := h10239c.2.2.1
                              have p10239_3 := h10239c.2.2.2
                              linarith only [h10194, h8188, h8818, hc01, hc12, hlam, hphi, p10239_1]
                            · have p10239_0 := h10239c.1
                              have p10239_1 := h10239c.2.1
                              have p10239_2 := h10239c.2.2.1
                              have p10239_3 := h10239c.2.2.2
                              linarith only [h7464, hc01, hc14, hlam, hphi, p10239_1]
                            · have p10239_0 := h10239c.1
                              have p10239_1 := h10239c.2.1
                              have p10239_2 := h10239c.2.2.1
                              have p10239_3 := h10239c.2.2.2
                              linarith only [h10104, hlam, p10239_0]
                            · have p10239_0 := h10239c.1
                              have p10239_1 := h10239c.2.1
                              have p10239_2 := h10239c.2.2.1
                              have p10239_3 := h10239c.2.2.2
                              linarith only [h10106, hlam, p10239_0]
                            · have p10239_0 := h10239c.1
                              have p10239_1 := h10239c.2.1
                              have p10239_2 := h10239c.2.2.1
                              have p10239_3 := h10239c.2.2.2
                              linarith only [hlam, p10239_0]
                            · have p10239_0 := h10239c.1
                              have p10239_1 := h10239c.2.1
                              have p10239_2 := h10239c.2.2.1
                              have p10239_3 := h10239c.2.2.2
                              linarith only [h10108, hlam, p10239_0]
                            · have p10239_0 := h10239c.1
                              have p10239_1 := h10239c.2.1
                              have p10239_2 := h10239c.2.2.1
                              have p10239_3 := h10239c.2.2.2
                              linarith only [h8188, hc01, hc15, hlam, hphi, p10239_1]
                            · have p10239_0 := h10239c.1
                              have p10239_1 := h10239c.2.1
                              have p10239_2 := h10239c.2.2.1
                              have p10239_3 := h10239c.2.2.2
                              linarith only [h10105, hlam, p10239_1]
                            · have p10239_0 := h10239c.1
                              have p10239_1 := h10239c.2.1
                              have p10239_2 := h10239c.2.2.1
                              have p10239_3 := h10239c.2.2.2
                              linarith only [h10107, hlam, p10239_0]
                            · have p10239_0 := h10239c.1
                              have p10239_1 := h10239c.2.1
                              have p10239_2 := h10239c.2.2.1
                              have p10239_3 := h10239c.2.2.2
                              linarith only [h10105, h10194, h8818, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p10239_1]
                            · have p10239_0 := h10239c.1
                              have p10239_1 := h10239c.2.1
                              have p10239_2 := h10239c.2.2.1
                              have p10239_3 := h10239c.2.2.2
                              linarith only [hlam, p10239_0]
                      · linarith only [h10107, h10234, h8818, hlam]
                    · linarith only [h10106, h10233, h8818, hlam]
                · linarith only [h10104, h10106, h10197, h6421, h8818, hlam]
              · linarith only [h10105, h10196, h8818, hc12, hc23, hlam, hphi]
            · linarith only [h10104, h10194, h10195, h8818, hlam]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h10270 | h10270
            · rcases m.htr 1 2 5 (by decide) (by decide) with h10271 | h10271
              · rcases m.htr 1 3 4 (by decide) (by decide) with h10272 | h10272
                · rcases m.htr 1 4 5 (by decide) (by decide) with h10273 | h10273
                  · linarith only [h10108, h10194, h10270, h10273, h7464, hc01, hc23, hlam, hphi, ht12]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h10275 | h10275
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h10276 | h10276
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h10277 | h10277
                        · linarith only [h10273, h10277, h7464, hc01, hc24, hlam, hphi, ht12]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h10279 | h10279
                          · linarith only [h0, h10105, h10194, h10273, h10275, h10277, h10279, h7464, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                          · rcases h0bigk with h10281c | h10281c | h10281c | h10281c | h10281c | h10281c | h10281c | h10281c | h10281c | h10281c | h10281c | h10281c | h10281c | h10281c | h10281c | h10281c | h10281c | h10281c | h10281c | h10281c | h10281c | h10281c | h10281c | h10281c | h10281c
                            · have p10281_0 := h10281c.1
                              have p10281_1 := h10281c.2.1
                              have p10281_2 := h10281c.2.2.1
                              have p10281_3 := h10281c.2.2.2
                              linarith only [hlam, p10281_0]
                            · have p10281_0 := h10281c.1
                              have p10281_1 := h10281c.2.1
                              have p10281_2 := h10281c.2.2.1
                              have p10281_3 := h10281c.2.2.2
                              linarith only [h0, hlam, p10281_1]
                            · have p10281_0 := h10281c.1
                              have p10281_1 := h10281c.2.1
                              have p10281_2 := h10281c.2.2.1
                              have p10281_3 := h10281c.2.2.2
                              linarith only [h6421, hlam, p10281_0]
                            · have p10281_0 := h10281c.1
                              have p10281_1 := h10281c.2.1
                              have p10281_2 := h10281c.2.2.1
                              have p10281_3 := h10281c.2.2.2
                              linarith only [h7464, hlam, p10281_1]
                            · have p10281_0 := h10281c.1
                              have p10281_1 := h10281c.2.1
                              have p10281_2 := h10281c.2.2.1
                              have p10281_3 := h10281c.2.2.2
                              linarith only [h8188, hlam, p10281_1]
                            · have p10281_0 := h10281c.1
                              have p10281_1 := h10281c.2.1
                              have p10281_2 := h10281c.2.2.1
                              have p10281_3 := h10281c.2.2.2
                              linarith only [h0, h10194, hc01, hc23, hlam, hphi, ht12, p10281_1]
                            · have p10281_0 := h10281c.1
                              have p10281_1 := h10281c.2.1
                              have p10281_2 := h10281c.2.2.1
                              have p10281_3 := h10281c.2.2.2
                              linarith only [hlam, p10281_0]
                            · have p10281_0 := h10281c.1
                              have p10281_1 := h10281c.2.1
                              have p10281_2 := h10281c.2.2.1
                              have p10281_3 := h10281c.2.2.2
                              linarith only [h8818, hlam, p10281_0]
                            · have p10281_0 := h10281c.1
                              have p10281_1 := h10281c.2.1
                              have p10281_2 := h10281c.2.2.1
                              have p10281_3 := h10281c.2.2.2
                              linarith only [h0, h10194, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p10281_1]
                            · have p10281_0 := h10281c.1
                              have p10281_1 := h10281c.2.1
                              have p10281_2 := h10281c.2.2.1
                              have p10281_3 := h10281c.2.2.2
                              linarith only [h0, h10194, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p10281_1]
                            · have p10281_0 := h10281c.1
                              have p10281_1 := h10281c.2.1
                              have p10281_2 := h10281c.2.2.1
                              have p10281_3 := h10281c.2.2.2
                              linarith only [h10194, h6421, hc01, hc23, hlam, hphi, ht12, p10281_1]
                            · have p10281_0 := h10281c.1
                              have p10281_1 := h10281c.2.1
                              have p10281_2 := h10281c.2.2.1
                              have p10281_3 := h10281c.2.2.2
                              linarith only [h10194, h6421, hc02, hc23, hlam, hphi, p10281_1]
                            · have p10281_0 := h10281c.1
                              have p10281_1 := h10281c.2.1
                              have p10281_2 := h10281c.2.2.1
                              have p10281_3 := h10281c.2.2.2
                              linarith only [hlam, p10281_0]
                            · have p10281_0 := h10281c.1
                              have p10281_1 := h10281c.2.1
                              have p10281_2 := h10281c.2.2.1
                              have p10281_3 := h10281c.2.2.2
                              linarith only [h10194, h6421, h7464, hc01, hc23, hlam, hphi, ht12, p10281_1]
                            · have p10281_0 := h10281c.1
                              have p10281_1 := h10281c.2.1
                              have p10281_2 := h10281c.2.2.1
                              have p10281_3 := h10281c.2.2.2
                              linarith only [h10194, h6421, h8188, hc01, hc23, hlam, hphi, ht12, p10281_1]
                            · have p10281_0 := h10281c.1
                              have p10281_1 := h10281c.2.1
                              have p10281_2 := h10281c.2.2.1
                              have p10281_3 := h10281c.2.2.2
                              linarith only [h7464, hc01, hc14, hlam, hphi, p10281_1]
                            · have p10281_0 := h10281c.1
                              have p10281_1 := h10281c.2.1
                              have p10281_2 := h10281c.2.2.1
                              have p10281_3 := h10281c.2.2.2
                              linarith only [h10104, hlam, p10281_0]
                            · have p10281_0 := h10281c.1
                              have p10281_1 := h10281c.2.1
                              have p10281_2 := h10281c.2.2.1
                              have p10281_3 := h10281c.2.2.2
                              linarith only [h10106, hlam, p10281_0]
                            · have p10281_0 := h10281c.1
                              have p10281_1 := h10281c.2.1
                              have p10281_2 := h10281c.2.2.1
                              have p10281_3 := h10281c.2.2.2
                              linarith only [hlam, p10281_0]
                            · have p10281_0 := h10281c.1
                              have p10281_1 := h10281c.2.1
                              have p10281_2 := h10281c.2.2.1
                              have p10281_3 := h10281c.2.2.2
                              linarith only [h10108, hlam, p10281_0]
                            · have p10281_0 := h10281c.1
                              have p10281_1 := h10281c.2.1
                              have p10281_2 := h10281c.2.2.1
                              have p10281_3 := h10281c.2.2.2
                              linarith only [h8188, hc01, hc15, hlam, hphi, p10281_1]
                            · have p10281_0 := h10281c.1
                              have p10281_1 := h10281c.2.1
                              have p10281_2 := h10281c.2.2.1
                              have p10281_3 := h10281c.2.2.2
                              linarith only [h10105, hlam, p10281_1]
                            · have p10281_0 := h10281c.1
                              have p10281_1 := h10281c.2.1
                              have p10281_2 := h10281c.2.2.1
                              have p10281_3 := h10281c.2.2.2
                              linarith only [h10107, hlam, p10281_0]
                            · have p10281_0 := h10281c.1
                              have p10281_1 := h10281c.2.1
                              have p10281_2 := h10281c.2.2.1
                              have p10281_3 := h10281c.2.2.2
                              linarith only [h0, h10105, h10194, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p10281_1]
                            · have p10281_0 := h10281c.1
                              have p10281_1 := h10281c.2.1
                              have p10281_2 := h10281c.2.2.1
                              have p10281_3 := h10281c.2.2.2
                              linarith only [hlam, p10281_0]
                      · linarith only [h0, h10194, h10276, hc01, hc35, hlam, hphi, ht12, ht23]
                    · linarith only [h10194, h10271, h10273, h10275, h7464, hc01, hc34, hlam, hphi, ht12, ht23]
                · linarith only [h10104, h10106, h10272, h6421, h8818, hlam]
              · linarith only [h10105, h10270, h10271, h6421, h7464, h8818, hc01, hc13, hlam, hphi]
            · linarith only [h0, h10104, h10270, hlam]
      · linarith only [h10105, h10107, h8818, hlam]
    · linarith only [h10104, h10106, h8818, hlam]
  · rcases m.htr 0 3 4 (by decide) (by decide) with h10314 | h10314
    · rcases m.htr 0 3 5 (by decide) (by decide) with h10315 | h10315
      · rcases m.htr 0 4 5 (by decide) (by decide) with h10316 | h10316
        · linarith only [h10104, h10105, h10316, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h10318 | h10318
          · rcases m.htr 1 2 4 (by decide) (by decide) with h10319 | h10319
            · rcases m.htr 1 2 5 (by decide) (by decide) with h10320 | h10320
              · rcases m.htr 1 3 4 (by decide) (by decide) with h10321 | h10321
                · rcases m.htr 1 4 5 (by decide) (by decide) with h10322 | h10322
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h10323 | h10323
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h10324 | h10324
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h10325 | h10325
                        · linarith only [h10104, h10105, h10316, h10318, h10324, h10325, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h10327 | h10327
                          · linarith only [h10104, h10105, h10323, h10325, h10327, hlam]
                          · rcases h0bigk with h10329c | h10329c | h10329c | h10329c | h10329c | h10329c | h10329c | h10329c | h10329c | h10329c | h10329c | h10329c | h10329c | h10329c | h10329c | h10329c | h10329c | h10329c | h10329c | h10329c | h10329c | h10329c | h10329c | h10329c | h10329c
                            · have p10329_0 := h10329c.1
                              have p10329_1 := h10329c.2.1
                              have p10329_2 := h10329c.2.2.1
                              have p10329_3 := h10329c.2.2.2
                              linarith only [hlam, p10329_0]
                            · have p10329_0 := h10329c.1
                              have p10329_1 := h10329c.2.1
                              have p10329_2 := h10329c.2.2.1
                              have p10329_3 := h10329c.2.2.2
                              linarith only [h0, hlam, p10329_1]
                            · have p10329_0 := h10329c.1
                              have p10329_1 := h10329c.2.1
                              have p10329_2 := h10329c.2.2.1
                              have p10329_3 := h10329c.2.2.2
                              linarith only [h6421, hlam, p10329_0]
                            · have p10329_0 := h10329c.1
                              have p10329_1 := h10329c.2.1
                              have p10329_2 := h10329c.2.2.1
                              have p10329_3 := h10329c.2.2.2
                              linarith only [h7464, hlam, p10329_1]
                            · have p10329_0 := h10329c.1
                              have p10329_1 := h10329c.2.1
                              have p10329_2 := h10329c.2.2.1
                              have p10329_3 := h10329c.2.2.2
                              linarith only [h8188, hlam, p10329_1]
                            · have p10329_0 := h10329c.1
                              have p10329_1 := h10329c.2.1
                              have p10329_2 := h10329c.2.2.1
                              have p10329_3 := h10329c.2.2.2
                              linarith only [h10105, h10318, h10321, h10322, h10325, hc01, hc12, hlam, hphi, p10329_1]
                            · have p10329_0 := h10329c.1
                              have p10329_1 := h10329c.2.1
                              have p10329_2 := h10329c.2.2.1
                              have p10329_3 := h10329c.2.2.2
                              linarith only [hlam, p10329_0]
                            · have p10329_0 := h10329c.1
                              have p10329_1 := h10329c.2.1
                              have p10329_2 := h10329c.2.2.1
                              have p10329_3 := h10329c.2.2.2
                              linarith only [h8818, hlam, p10329_0]
                            · have p10329_0 := h10329c.1
                              have p10329_1 := h10329c.2.1
                              have p10329_2 := h10329c.2.2.1
                              have p10329_3 := h10329c.2.2.2
                              linarith only [h10105, h10318, h10321, h10322, h10325, h7464, hc01, hc12, hlam, hphi, p10329_1]
                            · have p10329_0 := h10329c.1
                              have p10329_1 := h10329c.2.1
                              have p10329_2 := h10329c.2.2.1
                              have p10329_3 := h10329c.2.2.2
                              linarith only [h10105, hlam, p10329_0]
                            · have p10329_0 := h10329c.1
                              have p10329_1 := h10329c.2.1
                              have p10329_2 := h10329c.2.2.1
                              have p10329_3 := h10329c.2.2.2
                              linarith only [h10318, h6421, hc01, hc12, hlam, hphi, p10329_1]
                            · have p10329_0 := h10329c.1
                              have p10329_1 := h10329c.2.1
                              have p10329_2 := h10329c.2.2.1
                              have p10329_3 := h10329c.2.2.2
                              linarith only [h8818, hc02, hc23, hlam, hphi, p10329_1]
                            · have p10329_0 := h10329c.1
                              have p10329_1 := h10329c.2.1
                              have p10329_2 := h10329c.2.2.1
                              have p10329_3 := h10329c.2.2.2
                              linarith only [hlam, p10329_0]
                            · have p10329_0 := h10329c.1
                              have p10329_1 := h10329c.2.1
                              have p10329_2 := h10329c.2.2.1
                              have p10329_3 := h10329c.2.2.2
                              linarith only [h10318, h6421, h7464, hc01, hc12, hlam, hphi, p10329_1]
                            · have p10329_0 := h10329c.1
                              have p10329_1 := h10329c.2.1
                              have p10329_2 := h10329c.2.2.1
                              have p10329_3 := h10329c.2.2.2
                              linarith only [h10104, h10105, h10318, h10323, h6421, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p10329_1]
                            · have p10329_0 := h10329c.1
                              have p10329_1 := h10329c.2.1
                              have p10329_2 := h10329c.2.2.1
                              have p10329_3 := h10329c.2.2.2
                              linarith only [h10318, h10321, h7464, hc01, hc12, hlam, hphi, p10329_1]
                            · have p10329_0 := h10329c.1
                              have p10329_1 := h10329c.2.1
                              have p10329_2 := h10329c.2.2.1
                              have p10329_3 := h10329c.2.2.2
                              linarith only [h10104, hlam, p10329_0]
                            · have p10329_0 := h10329c.1
                              have p10329_1 := h10329c.2.1
                              have p10329_2 := h10329c.2.2.1
                              have p10329_3 := h10329c.2.2.2
                              linarith only [h10314, hlam, p10329_0]
                            · have p10329_0 := h10329c.1
                              have p10329_1 := h10329c.2.1
                              have p10329_2 := h10329c.2.2.1
                              have p10329_3 := h10329c.2.2.2
                              linarith only [hlam, p10329_0]
                            · have p10329_0 := h10329c.1
                              have p10329_1 := h10329c.2.1
                              have p10329_2 := h10329c.2.2.1
                              have p10329_3 := h10329c.2.2.2
                              linarith only [h10316, hlam, p10329_0]
                            · have p10329_0 := h10329c.1
                              have p10329_1 := h10329c.2.1
                              have p10329_2 := h10329c.2.2.1
                              have p10329_3 := h10329c.2.2.2
                              linarith only [h8188, hc01, hc15, hlam, hphi, p10329_1]
                            · have p10329_0 := h10329c.1
                              have p10329_1 := h10329c.2.1
                              have p10329_2 := h10329c.2.2.1
                              have p10329_3 := h10329c.2.2.2
                              linarith only [h10105, h10318, h10321, h10322, h10325, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p10329_1]
                            · have p10329_0 := h10329c.1
                              have p10329_1 := h10329c.2.1
                              have p10329_2 := h10329c.2.2.1
                              have p10329_3 := h10329c.2.2.2
                              linarith only [h10315, hlam, p10329_0]
                            · have p10329_0 := h10329c.1
                              have p10329_1 := h10329c.2.1
                              have p10329_2 := h10329c.2.2.1
                              have p10329_3 := h10329c.2.2.2
                              linarith only [h10105, h10318, h10321, h10322, h10325, h7464, hc01, hc12, hlam, hphi, p10329_1]
                            · have p10329_0 := h10329c.1
                              have p10329_1 := h10329c.2.1
                              have p10329_2 := h10329c.2.2.1
                              have p10329_3 := h10329c.2.2.2
                              linarith only [hlam, p10329_0]
                      · linarith only [h10315, h10324, h8818, hlam]
                    · linarith only [h10314, h10323, h8818, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h10357 | h10357
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h10358 | h10358
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h10359 | h10359
                        · linarith only [h10104, h10105, h10322, h10358, h10359, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h10361 | h10361
                          · linarith only [h10322, h10361, h7464, hc01, hc34, hlam, hphi, ht12, ht23]
                          · rcases h0bigk with h10363c | h10363c | h10363c | h10363c | h10363c | h10363c | h10363c | h10363c | h10363c | h10363c | h10363c | h10363c | h10363c | h10363c | h10363c | h10363c | h10363c | h10363c | h10363c | h10363c | h10363c | h10363c | h10363c | h10363c | h10363c
                            · have p10363_0 := h10363c.1
                              have p10363_1 := h10363c.2.1
                              have p10363_2 := h10363c.2.2.1
                              have p10363_3 := h10363c.2.2.2
                              linarith only [hlam, p10363_0]
                            · have p10363_0 := h10363c.1
                              have p10363_1 := h10363c.2.1
                              have p10363_2 := h10363c.2.2.1
                              have p10363_3 := h10363c.2.2.2
                              linarith only [h0, hlam, p10363_1]
                            · have p10363_0 := h10363c.1
                              have p10363_1 := h10363c.2.1
                              have p10363_2 := h10363c.2.2.1
                              have p10363_3 := h10363c.2.2.2
                              linarith only [h6421, hlam, p10363_0]
                            · have p10363_0 := h10363c.1
                              have p10363_1 := h10363c.2.1
                              have p10363_2 := h10363c.2.2.1
                              have p10363_3 := h10363c.2.2.2
                              linarith only [h7464, hlam, p10363_1]
                            · have p10363_0 := h10363c.1
                              have p10363_1 := h10363c.2.1
                              have p10363_2 := h10363c.2.2.1
                              have p10363_3 := h10363c.2.2.2
                              linarith only [h8188, hlam, p10363_1]
                            · have p10363_0 := h10363c.1
                              have p10363_1 := h10363c.2.1
                              have p10363_2 := h10363c.2.2.1
                              have p10363_3 := h10363c.2.2.2
                              linarith only [h10105, h10318, h10358, hc01, hc12, hlam, hphi, p10363_1]
                            · have p10363_0 := h10363c.1
                              have p10363_1 := h10363c.2.1
                              have p10363_2 := h10363c.2.2.1
                              have p10363_3 := h10363c.2.2.2
                              linarith only [hlam, p10363_0]
                            · have p10363_0 := h10363c.1
                              have p10363_1 := h10363c.2.1
                              have p10363_2 := h10363c.2.2.1
                              have p10363_3 := h10363c.2.2.2
                              linarith only [h8818, hlam, p10363_0]
                            · have p10363_0 := h10363c.1
                              have p10363_1 := h10363c.2.1
                              have p10363_2 := h10363c.2.2.1
                              have p10363_3 := h10363c.2.2.2
                              linarith only [h10105, h10318, h10358, h7464, hc01, hc12, hlam, hphi, p10363_1]
                            · have p10363_0 := h10363c.1
                              have p10363_1 := h10363c.2.1
                              have p10363_2 := h10363c.2.2.1
                              have p10363_3 := h10363c.2.2.2
                              linarith only [h10105, hlam, p10363_0]
                            · have p10363_0 := h10363c.1
                              have p10363_1 := h10363c.2.1
                              have p10363_2 := h10363c.2.2.1
                              have p10363_3 := h10363c.2.2.2
                              linarith only [h10318, h6421, hc01, hc12, hlam, hphi, p10363_1]
                            · have p10363_0 := h10363c.1
                              have p10363_1 := h10363c.2.1
                              have p10363_2 := h10363c.2.2.1
                              have p10363_3 := h10363c.2.2.2
                              linarith only [h10318, h8818, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p10363_1]
                            · have p10363_0 := h10363c.1
                              have p10363_1 := h10363c.2.1
                              have p10363_2 := h10363c.2.2.1
                              have p10363_3 := h10363c.2.2.2
                              linarith only [hlam, p10363_0]
                            · have p10363_0 := h10363c.1
                              have p10363_1 := h10363c.2.1
                              have p10363_2 := h10363c.2.2.1
                              have p10363_3 := h10363c.2.2.2
                              linarith only [h10318, h7464, h8818, hc01, hc12, hlam, hphi, p10363_1]
                            · have p10363_0 := h10363c.1
                              have p10363_1 := h10363c.2.1
                              have p10363_2 := h10363c.2.2.1
                              have p10363_3 := h10363c.2.2.2
                              linarith only [h10318, h8818, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p10363_1]
                            · have p10363_0 := h10363c.1
                              have p10363_1 := h10363c.2.1
                              have p10363_2 := h10363c.2.2.1
                              have p10363_3 := h10363c.2.2.2
                              linarith only [h7464, hc01, hc14, hlam, hphi, p10363_1]
                            · have p10363_0 := h10363c.1
                              have p10363_1 := h10363c.2.1
                              have p10363_2 := h10363c.2.2.1
                              have p10363_3 := h10363c.2.2.2
                              linarith only [h10104, hlam, p10363_0]
                            · have p10363_0 := h10363c.1
                              have p10363_1 := h10363c.2.1
                              have p10363_2 := h10363c.2.2.1
                              have p10363_3 := h10363c.2.2.2
                              linarith only [h10314, hlam, p10363_0]
                            · have p10363_0 := h10363c.1
                              have p10363_1 := h10363c.2.1
                              have p10363_2 := h10363c.2.2.1
                              have p10363_3 := h10363c.2.2.2
                              linarith only [hlam, p10363_0]
                            · have p10363_0 := h10363c.1
                              have p10363_1 := h10363c.2.1
                              have p10363_2 := h10363c.2.2.1
                              have p10363_3 := h10363c.2.2.2
                              linarith only [h10316, hlam, p10363_0]
                            · have p10363_0 := h10363c.1
                              have p10363_1 := h10363c.2.1
                              have p10363_2 := h10363c.2.2.1
                              have p10363_3 := h10363c.2.2.2
                              linarith only [h8188, hc01, hc15, hlam, hphi, p10363_1]
                            · have p10363_0 := h10363c.1
                              have p10363_1 := h10363c.2.1
                              have p10363_2 := h10363c.2.2.1
                              have p10363_3 := h10363c.2.2.2
                              linarith only [h10105, h10318, h10358, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p10363_1]
                            · have p10363_0 := h10363c.1
                              have p10363_1 := h10363c.2.1
                              have p10363_2 := h10363c.2.2.1
                              have p10363_3 := h10363c.2.2.2
                              linarith only [h10315, hlam, p10363_0]
                            · have p10363_0 := h10363c.1
                              have p10363_1 := h10363c.2.1
                              have p10363_2 := h10363c.2.2.1
                              have p10363_3 := h10363c.2.2.2
                              linarith only [h10105, h10318, h10358, h7464, hc01, hc12, hlam, hphi, p10363_1]
                            · have p10363_0 := h10363c.1
                              have p10363_1 := h10363c.2.1
                              have p10363_2 := h10363c.2.2.1
                              have p10363_3 := h10363c.2.2.2
                              linarith only [hlam, p10363_0]
                      · linarith only [h10315, h10358, h8818, hlam]
                    · linarith only [h10314, h10357, h8818, hlam]
                · linarith only [h10104, h10314, h10321, h6421, h8818, hc01, hc23, hlam, hphi, ht12]
              · linarith only [h10318, h10320, h8818, hc02, hc25, hlam, hphi]
            · linarith only [h10104, h10318, h10319, h8818, hlam]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h10394 | h10394
            · rcases m.htr 1 2 5 (by decide) (by decide) with h10395 | h10395
              · linarith only [h10104, h10105, h10318, h10395, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h10397 | h10397
                · rcases m.htr 1 4 5 (by decide) (by decide) with h10398 | h10398
                  · linarith only [h10316, h10318, h10394, h10398, h7464, hc01, hc23, hlam, hphi, ht12]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h10400 | h10400
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h10401 | h10401
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h10402 | h10402
                        · linarith only [h0, h10104, h10395, h10398, h10401, h10402, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h10404 | h10404
                          · linarith only [h0, h10395, h10402, h10404, hc01, hc34, hlam, hphi, ht12, ht23]
                          · rcases h0bigk with h10406c | h10406c | h10406c | h10406c | h10406c | h10406c | h10406c | h10406c | h10406c | h10406c | h10406c | h10406c | h10406c | h10406c | h10406c | h10406c | h10406c | h10406c | h10406c | h10406c | h10406c | h10406c | h10406c | h10406c | h10406c
                            · have p10406_0 := h10406c.1
                              have p10406_1 := h10406c.2.1
                              have p10406_2 := h10406c.2.2.1
                              have p10406_3 := h10406c.2.2.2
                              linarith only [hlam, p10406_0]
                            · have p10406_0 := h10406c.1
                              have p10406_1 := h10406c.2.1
                              have p10406_2 := h10406c.2.2.1
                              have p10406_3 := h10406c.2.2.2
                              linarith only [h0, hlam, p10406_1]
                            · have p10406_0 := h10406c.1
                              have p10406_1 := h10406c.2.1
                              have p10406_2 := h10406c.2.2.1
                              have p10406_3 := h10406c.2.2.2
                              linarith only [h6421, hlam, p10406_0]
                            · have p10406_0 := h10406c.1
                              have p10406_1 := h10406c.2.1
                              have p10406_2 := h10406c.2.2.1
                              have p10406_3 := h10406c.2.2.2
                              linarith only [h7464, hlam, p10406_1]
                            · have p10406_0 := h10406c.1
                              have p10406_1 := h10406c.2.1
                              have p10406_2 := h10406c.2.2.1
                              have p10406_3 := h10406c.2.2.2
                              linarith only [h8188, hlam, p10406_1]
                            · have p10406_0 := h10406c.1
                              have p10406_1 := h10406c.2.1
                              have p10406_2 := h10406c.2.2.1
                              have p10406_3 := h10406c.2.2.2
                              linarith only [h0, hc01, hc12, hlam, hphi, p10406_1]
                            · have p10406_0 := h10406c.1
                              have p10406_1 := h10406c.2.1
                              have p10406_2 := h10406c.2.2.1
                              have p10406_3 := h10406c.2.2.2
                              linarith only [hlam, p10406_0]
                            · have p10406_0 := h10406c.1
                              have p10406_1 := h10406c.2.1
                              have p10406_2 := h10406c.2.2.1
                              have p10406_3 := h10406c.2.2.2
                              linarith only [h8818, hlam, p10406_0]
                            · have p10406_0 := h10406c.1
                              have p10406_1 := h10406c.2.1
                              have p10406_2 := h10406c.2.2.1
                              have p10406_3 := h10406c.2.2.2
                              linarith only [h7464, h8818, hc01, hc23, hlam, hphi, ht12, p10406_1]
                            · have p10406_0 := h10406c.1
                              have p10406_1 := h10406c.2.1
                              have p10406_2 := h10406c.2.2.1
                              have p10406_3 := h10406c.2.2.2
                              linarith only [h10105, hlam, p10406_0]
                            · have p10406_0 := h10406c.1
                              have p10406_1 := h10406c.2.1
                              have p10406_2 := h10406c.2.2.1
                              have p10406_3 := h10406c.2.2.2
                              linarith only [h6421, hc01, hc13, hlam, hphi, p10406_1]
                            · have p10406_0 := h10406c.1
                              have p10406_1 := h10406c.2.1
                              have p10406_2 := h10406c.2.2.1
                              have p10406_3 := h10406c.2.2.2
                              linarith only [h8818, hc02, hc23, hlam, hphi, p10406_1]
                            · have p10406_0 := h10406c.1
                              have p10406_1 := h10406c.2.1
                              have p10406_2 := h10406c.2.2.1
                              have p10406_3 := h10406c.2.2.2
                              linarith only [hlam, p10406_0]
                            · have p10406_0 := h10406c.1
                              have p10406_1 := h10406c.2.1
                              have p10406_2 := h10406c.2.2.1
                              have p10406_3 := h10406c.2.2.2
                              linarith only [h7464, h8818, hc01, hc23, hlam, hphi, ht12, p10406_1]
                            · have p10406_0 := h10406c.1
                              have p10406_1 := h10406c.2.1
                              have p10406_2 := h10406c.2.2.1
                              have p10406_3 := h10406c.2.2.2
                              linarith only [h8188, h8818, hc01, hc23, hlam, hphi, ht12, p10406_1]
                            · have p10406_0 := h10406c.1
                              have p10406_1 := h10406c.2.1
                              have p10406_2 := h10406c.2.2.1
                              have p10406_3 := h10406c.2.2.2
                              linarith only [h7464, hc01, hc14, hlam, hphi, p10406_1]
                            · have p10406_0 := h10406c.1
                              have p10406_1 := h10406c.2.1
                              have p10406_2 := h10406c.2.2.1
                              have p10406_3 := h10406c.2.2.2
                              linarith only [h10104, hlam, p10406_0]
                            · have p10406_0 := h10406c.1
                              have p10406_1 := h10406c.2.1
                              have p10406_2 := h10406c.2.2.1
                              have p10406_3 := h10406c.2.2.2
                              linarith only [h10314, hlam, p10406_0]
                            · have p10406_0 := h10406c.1
                              have p10406_1 := h10406c.2.1
                              have p10406_2 := h10406c.2.2.1
                              have p10406_3 := h10406c.2.2.2
                              linarith only [hlam, p10406_0]
                            · have p10406_0 := h10406c.1
                              have p10406_1 := h10406c.2.1
                              have p10406_2 := h10406c.2.2.1
                              have p10406_3 := h10406c.2.2.2
                              linarith only [h10316, hlam, p10406_0]
                            · have p10406_0 := h10406c.1
                              have p10406_1 := h10406c.2.1
                              have p10406_2 := h10406c.2.2.1
                              have p10406_3 := h10406c.2.2.2
                              linarith only [h10395, h10402, h8188, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p10406_1]
                            · have p10406_0 := h10406c.1
                              have p10406_1 := h10406c.2.1
                              have p10406_2 := h10406c.2.2.1
                              have p10406_3 := h10406c.2.2.2
                              linarith only [h10395, h10402, h8188, hc02, hc45, hlam, hphi, ht23, ht34, p10406_1]
                            · have p10406_0 := h10406c.1
                              have p10406_1 := h10406c.2.1
                              have p10406_2 := h10406c.2.2.1
                              have p10406_3 := h10406c.2.2.2
                              linarith only [h10315, hlam, p10406_0]
                            · have p10406_0 := h10406c.1
                              have p10406_1 := h10406c.2.1
                              have p10406_2 := h10406c.2.2.1
                              have p10406_3 := h10406c.2.2.2
                              linarith only [h10395, h10402, h7464, h8188, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p10406_1]
                            · have p10406_0 := h10406c.1
                              have p10406_1 := h10406c.2.1
                              have p10406_2 := h10406c.2.2.1
                              have p10406_3 := h10406c.2.2.2
                              linarith only [hlam, p10406_0]
                      · linarith only [h10315, h10318, h10401, h6421, hlam]
                    · linarith only [h0, h10318, h10400, hc01, hc34, hlam, hphi, ht12, ht23]
                · linarith only [h10314, h10318, h10394, h10397, h6421, h7464, hc01, hc23, hlam, hphi, ht12]
            · linarith only [h0, h10104, h10105, h10315, h10394, h6421, hc01, hc13, hlam, hphi]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h10436 | h10436
        · linarith only [h10104, h10105, h10436, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h10438 | h10438
          · rcases m.htr 1 2 4 (by decide) (by decide) with h10439 | h10439
            · rcases m.htr 1 2 5 (by decide) (by decide) with h10440 | h10440
              · rcases m.htr 1 3 4 (by decide) (by decide) with h10441 | h10441
                · rcases m.htr 1 4 5 (by decide) (by decide) with h10442 | h10442
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h10443 | h10443
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h10444 | h10444
                      · linarith only [h10104, h10315, h10438, h10444, h8818, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h10446 | h10446
                        · linarith only [h10104, h10436, h10440, h10444, h10446, h8818, hc04, hc15, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h10448 | h10448
                          · linarith only [h10104, h10443, h10444, h10446, h10448, h8818, hlam]
                          · linarith only [h10104, h10438, h10441, h10442, h10444, h10448, h8818, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · linarith only [h10314, h10443, h8818, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h10452 | h10452
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h10453 | h10453
                      · linarith only [h10315, h10438, h10453, h6421, hc01, hc12, hlam, hphi]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h10455 | h10455
                        · linarith only [h10104, h10442, h10455, h7464, hc01, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h10457 | h10457
                          · linarith only [h10104, h10442, h10452, h10457, h7464, hc01, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                          · linarith only [h10104, h10452, h10453, h10457, h8818, hc34, hc45, hlam, hphi]
                    · linarith only [h10314, h10452, h8818, hlam]
                · linarith only [h10104, h10314, h10441, h6421, h8818, hc01, hc23, hlam, hphi, ht12]
              · linarith only [h10104, h10438, h10440, h7464, h8818, hc01, hc25, hlam, hphi, ht12]
            · linarith only [h10104, h10438, h10439, h8818, hlam]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h10464 | h10464
            · rcases m.htr 1 2 5 (by decide) (by decide) with h10465 | h10465
              · linarith only [h10104, h10105, h10438, h10465, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h10467 | h10467
                · rcases m.htr 1 4 5 (by decide) (by decide) with h10468 | h10468
                  · linarith only [h10436, h10438, h10464, h10468, h7464, hc01, hc23, hlam, hphi, ht12]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h10470 | h10470
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h10471 | h10471
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h10472 | h10472
                        · linarith only [h10104, h10468, h10472, h7464, hc01, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h10474 | h10474
                          · linarith only [h10104, h10315, h10465, h10470, h10471, h10472, h10474, h8818, hc12, hc23, hlam, hphi]
                          · rcases h0bigk with h10476c | h10476c | h10476c | h10476c | h10476c | h10476c | h10476c | h10476c | h10476c | h10476c | h10476c | h10476c | h10476c | h10476c | h10476c | h10476c | h10476c | h10476c | h10476c | h10476c | h10476c | h10476c | h10476c | h10476c | h10476c
                            · have p10476_0 := h10476c.1
                              have p10476_1 := h10476c.2.1
                              have p10476_2 := h10476c.2.2.1
                              have p10476_3 := h10476c.2.2.2
                              linarith only [hlam, p10476_0]
                            · have p10476_0 := h10476c.1
                              have p10476_1 := h10476c.2.1
                              have p10476_2 := h10476c.2.2.1
                              have p10476_3 := h10476c.2.2.2
                              linarith only [h0, hlam, p10476_1]
                            · have p10476_0 := h10476c.1
                              have p10476_1 := h10476c.2.1
                              have p10476_2 := h10476c.2.2.1
                              have p10476_3 := h10476c.2.2.2
                              linarith only [h6421, hlam, p10476_0]
                            · have p10476_0 := h10476c.1
                              have p10476_1 := h10476c.2.1
                              have p10476_2 := h10476c.2.2.1
                              have p10476_3 := h10476c.2.2.2
                              linarith only [h7464, hlam, p10476_1]
                            · have p10476_0 := h10476c.1
                              have p10476_1 := h10476c.2.1
                              have p10476_2 := h10476c.2.2.1
                              have p10476_3 := h10476c.2.2.2
                              linarith only [h8188, hlam, p10476_1]
                            · have p10476_0 := h10476c.1
                              have p10476_1 := h10476c.2.1
                              have p10476_2 := h10476c.2.2.1
                              have p10476_3 := h10476c.2.2.2
                              linarith only [h10315, h10471, h8818, hc01, hc23, hlam, hphi, ht12, p10476_1]
                            · have p10476_0 := h10476c.1
                              have p10476_1 := h10476c.2.1
                              have p10476_2 := h10476c.2.2.1
                              have p10476_3 := h10476c.2.2.2
                              linarith only [hlam, p10476_0]
                            · have p10476_0 := h10476c.1
                              have p10476_1 := h10476c.2.1
                              have p10476_2 := h10476c.2.2.1
                              have p10476_3 := h10476c.2.2.2
                              linarith only [h8818, hlam, p10476_0]
                            · have p10476_0 := h10476c.1
                              have p10476_1 := h10476c.2.1
                              have p10476_2 := h10476c.2.2.1
                              have p10476_3 := h10476c.2.2.2
                              linarith only [h10315, h10471, h7464, h8818, hc01, hc23, hlam, hphi, ht12, p10476_1]
                            · have p10476_0 := h10476c.1
                              have p10476_1 := h10476c.2.1
                              have p10476_2 := h10476c.2.2.1
                              have p10476_3 := h10476c.2.2.2
                              linarith only [h10105, hlam, p10476_0]
                            · have p10476_0 := h10476c.1
                              have p10476_1 := h10476c.2.1
                              have p10476_2 := h10476c.2.2.1
                              have p10476_3 := h10476c.2.2.2
                              linarith only [h10315, h10471, hc01, hc23, hlam, hphi, ht12, p10476_1]
                            · have p10476_0 := h10476c.1
                              have p10476_1 := h10476c.2.1
                              have p10476_2 := h10476c.2.2.1
                              have p10476_3 := h10476c.2.2.2
                              linarith only [h10104, h10315, h10470, h10471, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p10476_1]
                            · have p10476_0 := h10476c.1
                              have p10476_1 := h10476c.2.1
                              have p10476_2 := h10476c.2.2.1
                              have p10476_3 := h10476c.2.2.2
                              linarith only [hlam, p10476_0]
                            · have p10476_0 := h10476c.1
                              have p10476_1 := h10476c.2.1
                              have p10476_2 := h10476c.2.2.1
                              have p10476_3 := h10476c.2.2.2
                              linarith only [h10315, h10471, h7464, hc01, hc23, hlam, hphi, ht12, p10476_1]
                            · have p10476_0 := h10476c.1
                              have p10476_1 := h10476c.2.1
                              have p10476_2 := h10476c.2.2.1
                              have p10476_3 := h10476c.2.2.2
                              linarith only [h10315, hlam, p10476_1]
                            · have p10476_0 := h10476c.1
                              have p10476_1 := h10476c.2.1
                              have p10476_2 := h10476c.2.2.1
                              have p10476_3 := h10476c.2.2.2
                              linarith only [h10464, h7464, hc01, hc12, hlam, hphi, p10476_1]
                            · have p10476_0 := h10476c.1
                              have p10476_1 := h10476c.2.1
                              have p10476_2 := h10476c.2.2.1
                              have p10476_3 := h10476c.2.2.2
                              linarith only [h10104, hlam, p10476_0]
                            · have p10476_0 := h10476c.1
                              have p10476_1 := h10476c.2.1
                              have p10476_2 := h10476c.2.2.1
                              have p10476_3 := h10476c.2.2.2
                              linarith only [h10314, hlam, p10476_0]
                            · have p10476_0 := h10476c.1
                              have p10476_1 := h10476c.2.1
                              have p10476_2 := h10476c.2.2.1
                              have p10476_3 := h10476c.2.2.2
                              linarith only [hlam, p10476_0]
                            · have p10476_0 := h10476c.1
                              have p10476_1 := h10476c.2.1
                              have p10476_2 := h10476c.2.2.1
                              have p10476_3 := h10476c.2.2.2
                              linarith only [h10436, hlam, p10476_0]
                            · have p10476_0 := h10476c.1
                              have p10476_1 := h10476c.2.1
                              have p10476_2 := h10476c.2.2.1
                              have p10476_3 := h10476c.2.2.2
                              linarith only [h10315, h10471, hc01, hc23, hlam, hphi, ht12, p10476_1]
                            · have p10476_0 := h10476c.1
                              have p10476_1 := h10476c.2.1
                              have p10476_2 := h10476c.2.2.1
                              have p10476_3 := h10476c.2.2.2
                              linarith only [h10104, h10315, h10470, h10471, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p10476_1]
                            · have p10476_0 := h10476c.1
                              have p10476_1 := h10476c.2.1
                              have p10476_2 := h10476c.2.2.1
                              have p10476_3 := h10476c.2.2.2
                              linarith only [h10315, h10471, hc03, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p10476_1]
                            · have p10476_0 := h10476c.1
                              have p10476_1 := h10476c.2.1
                              have p10476_2 := h10476c.2.2.1
                              have p10476_3 := h10476c.2.2.2
                              linarith only [h10315, h10471, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p10476_1]
                            · have p10476_0 := h10476c.1
                              have p10476_1 := h10476c.2.1
                              have p10476_2 := h10476c.2.2.1
                              have p10476_3 := h10476c.2.2.2
                              linarith only [hlam, p10476_0]
                      · linarith only [h0, h10438, h10471, hc01, hc35, hlam, hphi, ht12, ht23]
                    · linarith only [h10438, h10464, h10470, h7464, hc01, hc34, hlam, hphi, ht12, ht23]
                · linarith only [h10314, h10467, h6421, hlam]
            · linarith only [h0, h10104, h10464, hlam]
    · linarith only [h10104, h10314, h8818, hlam]

set_option maxHeartbeats 6230000 in
set_option maxHeartbeats 6230000 in
theorem r1l7_20_12_14_H_I_L_I_L_I_s9_x1_x1_x1_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6421 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg7464 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h8188 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h8818 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h10104 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h10507 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
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
  have h0bigk := hb0.1
  have h0 := hg0
  have h6421 := hg6421
  have h7464 := hg7464
  rcases m.htr 0 3 4 (by decide) (by decide) with h10508 | h10508
  · rcases m.htr 0 3 5 (by decide) (by decide) with h10509 | h10509
    · rcases m.htr 0 4 5 (by decide) (by decide) with h10510 | h10510
      · rcases m.htr 1 2 3 (by decide) (by decide) with h10511 | h10511
        · rcases m.htr 1 2 4 (by decide) (by decide) with h10512 | h10512
          · rcases m.htr 1 2 5 (by decide) (by decide) with h10513 | h10513
            · rcases m.htr 1 3 4 (by decide) (by decide) with h10514 | h10514
              · rcases m.htr 1 4 5 (by decide) (by decide) with h10515 | h10515
                · rcases m.htr 2 3 4 (by decide) (by decide) with h10516 | h10516
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h10517 | h10517
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h10518 | h10518
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h10519 | h10519
                        · rcases h0bigk with h10520c | h10520c | h10520c | h10520c | h10520c | h10520c | h10520c | h10520c | h10520c | h10520c | h10520c | h10520c | h10520c | h10520c | h10520c | h10520c | h10520c | h10520c | h10520c | h10520c | h10520c | h10520c | h10520c | h10520c | h10520c
                          · have p10520_0 := h10520c.1
                            have p10520_1 := h10520c.2.1
                            have p10520_2 := h10520c.2.2.1
                            have p10520_3 := h10520c.2.2.2
                            linarith only [hlam, p10520_0]
                          · have p10520_0 := h10520c.1
                            have p10520_1 := h10520c.2.1
                            have p10520_2 := h10520c.2.2.1
                            have p10520_3 := h10520c.2.2.2
                            linarith only [h0, hlam, p10520_1]
                          · have p10520_0 := h10520c.1
                            have p10520_1 := h10520c.2.1
                            have p10520_2 := h10520c.2.2.1
                            have p10520_3 := h10520c.2.2.2
                            linarith only [h6421, hlam, p10520_0]
                          · have p10520_0 := h10520c.1
                            have p10520_1 := h10520c.2.1
                            have p10520_2 := h10520c.2.2.1
                            have p10520_3 := h10520c.2.2.2
                            linarith only [h7464, hlam, p10520_1]
                          · have p10520_0 := h10520c.1
                            have p10520_1 := h10520c.2.1
                            have p10520_2 := h10520c.2.2.1
                            have p10520_3 := h10520c.2.2.2
                            linarith only [h8188, hlam, p10520_1]
                          · have p10520_0 := h10520c.1
                            have p10520_1 := h10520c.2.1
                            have p10520_2 := h10520c.2.2.1
                            have p10520_3 := h10520c.2.2.2
                            linarith only [h10104, h10511, h10516, hc01, hc12, hlam, hphi, p10520_1]
                          · have p10520_0 := h10520c.1
                            have p10520_1 := h10520c.2.1
                            have p10520_2 := h10520c.2.2.1
                            have p10520_3 := h10520c.2.2.2
                            linarith only [hlam, p10520_0]
                          · have p10520_0 := h10520c.1
                            have p10520_1 := h10520c.2.1
                            have p10520_2 := h10520c.2.2.1
                            have p10520_3 := h10520c.2.2.2
                            linarith only [h8818, hlam, p10520_0]
                          · have p10520_0 := h10520c.1
                            have p10520_1 := h10520c.2.1
                            have p10520_2 := h10520c.2.2.1
                            have p10520_3 := h10520c.2.2.2
                            linarith only [h10104, hlam, p10520_1]
                          · have p10520_0 := h10520c.1
                            have p10520_1 := h10520c.2.1
                            have p10520_2 := h10520c.2.2.1
                            have p10520_3 := h10520c.2.2.2
                            linarith only [h10104, h10511, h10516, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p10520_1]
                          · have p10520_0 := h10520c.1
                            have p10520_1 := h10520c.2.1
                            have p10520_2 := h10520c.2.2.1
                            have p10520_3 := h10520c.2.2.2
                            linarith only [h6421, hc01, hc13, hlam, hphi, p10520_1]
                          · have p10520_0 := h10520c.1
                            have p10520_1 := h10520c.2.1
                            have p10520_2 := h10520c.2.2.1
                            have p10520_3 := h10520c.2.2.2
                            linarith only [h10511, h8818, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p10520_1]
                          · have p10520_0 := h10520c.1
                            have p10520_1 := h10520c.2.1
                            have p10520_2 := h10520c.2.2.1
                            have p10520_3 := h10520c.2.2.2
                            linarith only [hlam, p10520_0]
                          · have p10520_0 := h10520c.1
                            have p10520_1 := h10520c.2.1
                            have p10520_2 := h10520c.2.2.1
                            have p10520_3 := h10520c.2.2.2
                            linarith only [h10511, h8818, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p10520_1]
                          · have p10520_0 := h10520c.1
                            have p10520_1 := h10520c.2.1
                            have p10520_2 := h10520c.2.2.1
                            have p10520_3 := h10520c.2.2.2
                            linarith only [h10511, h8188, h8818, hc01, hc12, hlam, hphi, p10520_1]
                          · have p10520_0 := h10520c.1
                            have p10520_1 := h10520c.2.1
                            have p10520_2 := h10520c.2.2.1
                            have p10520_3 := h10520c.2.2.2
                            linarith only [h7464, hc01, hc14, hlam, hphi, p10520_1]
                          · have p10520_0 := h10520c.1
                            have p10520_1 := h10520c.2.1
                            have p10520_2 := h10520c.2.2.1
                            have p10520_3 := h10520c.2.2.2
                            linarith only [h10104, h10507, h10511, h10516, h10517, h10519, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p10520_1]
                          · have p10520_0 := h10520c.1
                            have p10520_1 := h10520c.2.1
                            have p10520_2 := h10520c.2.2.1
                            have p10520_3 := h10520c.2.2.2
                            linarith only [h10508, hlam, p10520_0]
                          · have p10520_0 := h10520c.1
                            have p10520_1 := h10520c.2.1
                            have p10520_2 := h10520c.2.2.1
                            have p10520_3 := h10520c.2.2.2
                            linarith only [hlam, p10520_0]
                          · have p10520_0 := h10520c.1
                            have p10520_1 := h10520c.2.1
                            have p10520_2 := h10520c.2.2.1
                            have p10520_3 := h10520c.2.2.2
                            linarith only [h10104, h10511, h10516, h8188, hc01, hc12, hlam, hphi, p10520_1]
                          · have p10520_0 := h10520c.1
                            have p10520_1 := h10520c.2.1
                            have p10520_2 := h10520c.2.2.1
                            have p10520_3 := h10520c.2.2.2
                            linarith only [h10515, h8188, hc01, hc14, hlam, hphi, p10520_1]
                          · have p10520_0 := h10520c.1
                            have p10520_1 := h10520c.2.1
                            have p10520_2 := h10520c.2.2.1
                            have p10520_3 := h10520c.2.2.2
                            linarith only [h10507, hlam, p10520_1]
                          · have p10520_0 := h10520c.1
                            have p10520_1 := h10520c.2.1
                            have p10520_2 := h10520c.2.2.1
                            have p10520_3 := h10520c.2.2.2
                            linarith only [h10509, hlam, p10520_0]
                          · have p10520_0 := h10520c.1
                            have p10520_1 := h10520c.2.1
                            have p10520_2 := h10520c.2.2.1
                            have p10520_3 := h10520c.2.2.2
                            linarith only [h10510, hlam, p10520_1]
                          · have p10520_0 := h10520c.1
                            have p10520_1 := h10520c.2.1
                            have p10520_2 := h10520c.2.2.1
                            have p10520_3 := h10520c.2.2.2
                            linarith only [hlam, p10520_0]
                        · linarith only [h10104, h10507, h10511, h10516, h10518, h10519, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · linarith only [h10104, h10510, h10518, hlam]
                    · linarith only [h10509, h10517, h8818, hlam]
                  · linarith only [h10508, h10516, h8818, hlam]
                · linarith only [h10104, h10507, h10510, h10515, h7464, hc01, hc24, hlam, hphi, ht12]
              · linarith only [h10507, h10508, h10511, h10514, h8818, hc03, hc25, hlam, hphi, ht0b, ht5b]
            · linarith only [h10507, h10511, h10513, h8818, hlam]
          · linarith only [h10507, h10511, h10512, h8818, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h10554 | h10554
          · linarith only [h10104, h10507, h10511, h10554, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h10556 | h10556
            · rcases m.htr 1 3 4 (by decide) (by decide) with h10557 | h10557
              · rcases m.htr 1 4 5 (by decide) (by decide) with h10558 | h10558
                · rcases m.htr 2 3 4 (by decide) (by decide) with h10559 | h10559
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h10560 | h10560
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h10561 | h10561
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h10562 | h10562
                        · rcases h0bigk with h10563c | h10563c | h10563c | h10563c | h10563c | h10563c | h10563c | h10563c | h10563c | h10563c | h10563c | h10563c | h10563c | h10563c | h10563c | h10563c | h10563c | h10563c | h10563c | h10563c | h10563c | h10563c | h10563c | h10563c | h10563c
                          · have p10563_0 := h10563c.1
                            have p10563_1 := h10563c.2.1
                            have p10563_2 := h10563c.2.2.1
                            have p10563_3 := h10563c.2.2.2
                            linarith only [hlam, p10563_0]
                          · have p10563_0 := h10563c.1
                            have p10563_1 := h10563c.2.1
                            have p10563_2 := h10563c.2.2.1
                            have p10563_3 := h10563c.2.2.2
                            linarith only [h0, hlam, p10563_1]
                          · have p10563_0 := h10563c.1
                            have p10563_1 := h10563c.2.1
                            have p10563_2 := h10563c.2.2.1
                            have p10563_3 := h10563c.2.2.2
                            linarith only [h6421, hlam, p10563_0]
                          · have p10563_0 := h10563c.1
                            have p10563_1 := h10563c.2.1
                            have p10563_2 := h10563c.2.2.1
                            have p10563_3 := h10563c.2.2.2
                            linarith only [h7464, hlam, p10563_1]
                          · have p10563_0 := h10563c.1
                            have p10563_1 := h10563c.2.1
                            have p10563_2 := h10563c.2.2.1
                            have p10563_3 := h10563c.2.2.2
                            linarith only [h8188, hlam, p10563_1]
                          · have p10563_0 := h10563c.1
                            have p10563_1 := h10563c.2.1
                            have p10563_2 := h10563c.2.2.1
                            have p10563_3 := h10563c.2.2.2
                            linarith only [h0, h10554, h10559, hc01, hc23, hlam, hphi, ht12, p10563_1]
                          · have p10563_0 := h10563c.1
                            have p10563_1 := h10563c.2.1
                            have p10563_2 := h10563c.2.2.1
                            have p10563_3 := h10563c.2.2.2
                            linarith only [hlam, p10563_0]
                          · have p10563_0 := h10563c.1
                            have p10563_1 := h10563c.2.1
                            have p10563_2 := h10563c.2.2.1
                            have p10563_3 := h10563c.2.2.2
                            linarith only [h8818, hlam, p10563_0]
                          · have p10563_0 := h10563c.1
                            have p10563_1 := h10563c.2.1
                            have p10563_2 := h10563c.2.2.1
                            have p10563_3 := h10563c.2.2.2
                            linarith only [h10104, hlam, p10563_1]
                          · have p10563_0 := h10563c.1
                            have p10563_1 := h10563c.2.1
                            have p10563_2 := h10563c.2.2.1
                            have p10563_3 := h10563c.2.2.2
                            linarith only [h0, h10554, h10559, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p10563_1]
                          · have p10563_0 := h10563c.1
                            have p10563_1 := h10563c.2.1
                            have p10563_2 := h10563c.2.2.1
                            have p10563_3 := h10563c.2.2.2
                            linarith only [h10511, h6421, hc01, hc23, hlam, hphi, ht12, p10563_1]
                          · have p10563_0 := h10563c.1
                            have p10563_1 := h10563c.2.1
                            have p10563_2 := h10563c.2.2.1
                            have p10563_3 := h10563c.2.2.2
                            linarith only [h10511, h6421, hc02, hc23, hlam, hphi, p10563_1]
                          · have p10563_0 := h10563c.1
                            have p10563_1 := h10563c.2.1
                            have p10563_2 := h10563c.2.2.1
                            have p10563_3 := h10563c.2.2.2
                            linarith only [hlam, p10563_0]
                          · have p10563_0 := h10563c.1
                            have p10563_1 := h10563c.2.1
                            have p10563_2 := h10563c.2.2.1
                            have p10563_3 := h10563c.2.2.2
                            linarith only [h10104, h10507, h10511, h10560, h10562, h6421, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p10563_1]
                          · have p10563_0 := h10563c.1
                            have p10563_1 := h10563c.2.1
                            have p10563_2 := h10563c.2.2.1
                            have p10563_3 := h10563c.2.2.2
                            linarith only [h10511, h6421, h8188, hc01, hc23, hlam, hphi, ht12, p10563_1]
                          · have p10563_0 := h10563c.1
                            have p10563_1 := h10563c.2.1
                            have p10563_2 := h10563c.2.2.1
                            have p10563_3 := h10563c.2.2.2
                            linarith only [h7464, hc01, hc14, hlam, hphi, p10563_1]
                          · have p10563_0 := h10563c.1
                            have p10563_1 := h10563c.2.1
                            have p10563_2 := h10563c.2.2.1
                            have p10563_3 := h10563c.2.2.2
                            linarith only [h10104, h10507, h10559, h10560, h10562, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p10563_1]
                          · have p10563_0 := h10563c.1
                            have p10563_1 := h10563c.2.1
                            have p10563_2 := h10563c.2.2.1
                            have p10563_3 := h10563c.2.2.2
                            linarith only [h10508, hlam, p10563_0]
                          · have p10563_0 := h10563c.1
                            have p10563_1 := h10563c.2.1
                            have p10563_2 := h10563c.2.2.1
                            have p10563_3 := h10563c.2.2.2
                            linarith only [hlam, p10563_0]
                          · have p10563_0 := h10563c.1
                            have p10563_1 := h10563c.2.1
                            have p10563_2 := h10563c.2.2.1
                            have p10563_3 := h10563c.2.2.2
                            linarith only [h10508, h10511, h6421, h8188, hc01, hc23, hlam, hphi, ht12, p10563_1]
                          · have p10563_0 := h10563c.1
                            have p10563_1 := h10563c.2.1
                            have p10563_2 := h10563c.2.2.1
                            have p10563_3 := h10563c.2.2.2
                            linarith only [h10554, h10556, h10559, h8188, hc01, hc23, hlam, hphi, ht12, p10563_1]
                          · have p10563_0 := h10563c.1
                            have p10563_1 := h10563c.2.1
                            have p10563_2 := h10563c.2.2.1
                            have p10563_3 := h10563c.2.2.2
                            linarith only [h10507, hlam, p10563_1]
                          · have p10563_0 := h10563c.1
                            have p10563_1 := h10563c.2.1
                            have p10563_2 := h10563c.2.2.1
                            have p10563_3 := h10563c.2.2.2
                            linarith only [h10509, hlam, p10563_0]
                          · have p10563_0 := h10563c.1
                            have p10563_1 := h10563c.2.1
                            have p10563_2 := h10563c.2.2.1
                            have p10563_3 := h10563c.2.2.2
                            linarith only [h10510, hlam, p10563_1]
                          · have p10563_0 := h10563c.1
                            have p10563_1 := h10563c.2.1
                            have p10563_2 := h10563c.2.2.1
                            have p10563_3 := h10563c.2.2.2
                            linarith only [hlam, p10563_0]
                        · rcases h0bigk with h10589c | h10589c | h10589c | h10589c | h10589c | h10589c | h10589c | h10589c | h10589c | h10589c | h10589c | h10589c | h10589c | h10589c | h10589c | h10589c | h10589c | h10589c | h10589c | h10589c | h10589c | h10589c | h10589c | h10589c | h10589c
                          · have p10589_0 := h10589c.1
                            have p10589_1 := h10589c.2.1
                            have p10589_2 := h10589c.2.2.1
                            have p10589_3 := h10589c.2.2.2
                            linarith only [hlam, p10589_0]
                          · have p10589_0 := h10589c.1
                            have p10589_1 := h10589c.2.1
                            have p10589_2 := h10589c.2.2.1
                            have p10589_3 := h10589c.2.2.2
                            linarith only [h0, hlam, p10589_1]
                          · have p10589_0 := h10589c.1
                            have p10589_1 := h10589c.2.1
                            have p10589_2 := h10589c.2.2.1
                            have p10589_3 := h10589c.2.2.2
                            linarith only [h6421, hlam, p10589_0]
                          · have p10589_0 := h10589c.1
                            have p10589_1 := h10589c.2.1
                            have p10589_2 := h10589c.2.2.1
                            have p10589_3 := h10589c.2.2.2
                            linarith only [h7464, hlam, p10589_1]
                          · have p10589_0 := h10589c.1
                            have p10589_1 := h10589c.2.1
                            have p10589_2 := h10589c.2.2.1
                            have p10589_3 := h10589c.2.2.2
                            linarith only [h8188, hlam, p10589_1]
                          · have p10589_0 := h10589c.1
                            have p10589_1 := h10589c.2.1
                            have p10589_2 := h10589c.2.2.1
                            have p10589_3 := h10589c.2.2.2
                            linarith only [h0, h10554, h10559, hc01, hc23, hlam, hphi, ht12, p10589_1]
                          · have p10589_0 := h10589c.1
                            have p10589_1 := h10589c.2.1
                            have p10589_2 := h10589c.2.2.1
                            have p10589_3 := h10589c.2.2.2
                            linarith only [hlam, p10589_0]
                          · have p10589_0 := h10589c.1
                            have p10589_1 := h10589c.2.1
                            have p10589_2 := h10589c.2.2.1
                            have p10589_3 := h10589c.2.2.2
                            linarith only [h8818, hlam, p10589_0]
                          · have p10589_0 := h10589c.1
                            have p10589_1 := h10589c.2.1
                            have p10589_2 := h10589c.2.2.1
                            have p10589_3 := h10589c.2.2.2
                            linarith only [h10104, hlam, p10589_1]
                          · have p10589_0 := h10589c.1
                            have p10589_1 := h10589c.2.1
                            have p10589_2 := h10589c.2.2.1
                            have p10589_3 := h10589c.2.2.2
                            linarith only [h0, h10554, h10559, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p10589_1]
                          · have p10589_0 := h10589c.1
                            have p10589_1 := h10589c.2.1
                            have p10589_2 := h10589c.2.2.1
                            have p10589_3 := h10589c.2.2.2
                            linarith only [h10511, h6421, hc01, hc23, hlam, hphi, ht12, p10589_1]
                          · have p10589_0 := h10589c.1
                            have p10589_1 := h10589c.2.1
                            have p10589_2 := h10589c.2.2.1
                            have p10589_3 := h10589c.2.2.2
                            linarith only [h10511, h6421, hc02, hc23, hlam, hphi, p10589_1]
                          · have p10589_0 := h10589c.1
                            have p10589_1 := h10589c.2.1
                            have p10589_2 := h10589c.2.2.1
                            have p10589_3 := h10589c.2.2.2
                            linarith only [hlam, p10589_0]
                          · have p10589_0 := h10589c.1
                            have p10589_1 := h10589c.2.1
                            have p10589_2 := h10589c.2.2.1
                            have p10589_3 := h10589c.2.2.2
                            linarith only [h10511, h6421, h7464, hc01, hc23, hlam, hphi, ht12, p10589_1]
                          · have p10589_0 := h10589c.1
                            have p10589_1 := h10589c.2.1
                            have p10589_2 := h10589c.2.2.1
                            have p10589_3 := h10589c.2.2.2
                            linarith only [h10511, h6421, h8188, hc01, hc23, hlam, hphi, ht12, p10589_1]
                          · have p10589_0 := h10589c.1
                            have p10589_1 := h10589c.2.1
                            have p10589_2 := h10589c.2.2.1
                            have p10589_3 := h10589c.2.2.2
                            linarith only [h10554, h10559, h7464, hc01, hc23, hlam, hphi, ht12, p10589_1]
                          · have p10589_0 := h10589c.1
                            have p10589_1 := h10589c.2.1
                            have p10589_2 := h10589c.2.2.1
                            have p10589_3 := h10589c.2.2.2
                            linarith only [h10507, h10554, h10559, h7464, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p10589_1]
                          · have p10589_0 := h10589c.1
                            have p10589_1 := h10589c.2.1
                            have p10589_2 := h10589c.2.2.1
                            have p10589_3 := h10589c.2.2.2
                            linarith only [h10508, hlam, p10589_0]
                          · have p10589_0 := h10589c.1
                            have p10589_1 := h10589c.2.1
                            have p10589_2 := h10589c.2.2.1
                            have p10589_3 := h10589c.2.2.2
                            linarith only [hlam, p10589_0]
                          · have p10589_0 := h10589c.1
                            have p10589_1 := h10589c.2.1
                            have p10589_2 := h10589c.2.2.1
                            have p10589_3 := h10589c.2.2.2
                            linarith only [h10554, h10559, h7464, h8188, hc01, hc23, hlam, hphi, ht12, p10589_1]
                          · have p10589_0 := h10589c.1
                            have p10589_1 := h10589c.2.1
                            have p10589_2 := h10589c.2.2.1
                            have p10589_3 := h10589c.2.2.2
                            linarith only [h10554, h10556, h10559, h8188, hc01, hc23, hlam, hphi, ht12, p10589_1]
                          · have p10589_0 := h10589c.1
                            have p10589_1 := h10589c.2.1
                            have p10589_2 := h10589c.2.2.1
                            have p10589_3 := h10589c.2.2.2
                            linarith only [h10507, hlam, p10589_1]
                          · have p10589_0 := h10589c.1
                            have p10589_1 := h10589c.2.1
                            have p10589_2 := h10589c.2.2.1
                            have p10589_3 := h10589c.2.2.2
                            linarith only [h10509, hlam, p10589_0]
                          · have p10589_0 := h10589c.1
                            have p10589_1 := h10589c.2.1
                            have p10589_2 := h10589c.2.2.1
                            have p10589_3 := h10589c.2.2.2
                            linarith only [h10510, hlam, p10589_1]
                          · have p10589_0 := h10589c.1
                            have p10589_1 := h10589c.2.1
                            have p10589_2 := h10589c.2.2.1
                            have p10589_3 := h10589c.2.2.2
                            linarith only [hlam, p10589_0]
                      · linarith only [h0, h10554, h10561, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                    · linarith only [h10554, h10556, h10559, h10560, h8188, hc01, hc35, hlam, hphi, ht12, ht23]
                  · linarith only [h10508, h10511, h10559, h6421, hlam]
                · linarith only [h10510, h10558, h7464, hlam]
              · linarith only [h10508, h10557, h6421, hlam]
            · linarith only [h0, h10507, h10556, hlam]
      · linarith only [h10104, h10507, h10510, hlam]
    · linarith only [h10104, h10507, h10508, h10509, hlam]
  · rcases m.htr 0 3 5 (by decide) (by decide) with h10623 | h10623
    · rcases m.htr 0 4 5 (by decide) (by decide) with h10624 | h10624
      · rcases m.htr 1 2 3 (by decide) (by decide) with h10625 | h10625
        · rcases m.htr 1 2 4 (by decide) (by decide) with h10626 | h10626
          · rcases m.htr 1 2 5 (by decide) (by decide) with h10627 | h10627
            · rcases m.htr 1 3 4 (by decide) (by decide) with h10628 | h10628
              · rcases m.htr 1 4 5 (by decide) (by decide) with h10629 | h10629
                · rcases m.htr 2 3 4 (by decide) (by decide) with h10630 | h10630
                  · linarith only [h10507, h10508, h10625, h10630, h8818, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b]
                  · linarith only [h10507, h10628, h10630, h8818, hc13, hc25, hlam, hphi, ht01, ht0b, ht5b]
                · linarith only [h10624, h10629, h7464, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h10634 | h10634
                · rcases m.htr 2 3 4 (by decide) (by decide) with h10635 | h10635
                  · linarith only [h10628, h10635, h6421, hc01, hc23, hlam, hphi, ht12]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h10637 | h10637
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h10638 | h10638
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h10639 | h10639
                        · rcases h0bigk with h10640c | h10640c | h10640c | h10640c | h10640c | h10640c | h10640c | h10640c | h10640c | h10640c | h10640c | h10640c | h10640c | h10640c | h10640c | h10640c | h10640c | h10640c | h10640c | h10640c | h10640c | h10640c | h10640c | h10640c | h10640c
                          · have p10640_0 := h10640c.1
                            have p10640_1 := h10640c.2.1
                            have p10640_2 := h10640c.2.2.1
                            have p10640_3 := h10640c.2.2.2
                            linarith only [hlam, p10640_0]
                          · have p10640_0 := h10640c.1
                            have p10640_1 := h10640c.2.1
                            have p10640_2 := h10640c.2.2.1
                            have p10640_3 := h10640c.2.2.2
                            linarith only [h0, hlam, p10640_1]
                          · have p10640_0 := h10640c.1
                            have p10640_1 := h10640c.2.1
                            have p10640_2 := h10640c.2.2.1
                            have p10640_3 := h10640c.2.2.2
                            linarith only [h6421, hlam, p10640_0]
                          · have p10640_0 := h10640c.1
                            have p10640_1 := h10640c.2.1
                            have p10640_2 := h10640c.2.2.1
                            have p10640_3 := h10640c.2.2.2
                            linarith only [h7464, hlam, p10640_1]
                          · have p10640_0 := h10640c.1
                            have p10640_1 := h10640c.2.1
                            have p10640_2 := h10640c.2.2.1
                            have p10640_3 := h10640c.2.2.2
                            linarith only [h8188, hlam, p10640_1]
                          · have p10640_0 := h10640c.1
                            have p10640_1 := h10640c.2.1
                            have p10640_2 := h10640c.2.2.1
                            have p10640_3 := h10640c.2.2.2
                            linarith only [h10625, h8818, hc01, hc13, hlam, hphi, p10640_1]
                          · have p10640_0 := h10640c.1
                            have p10640_1 := h10640c.2.1
                            have p10640_2 := h10640c.2.2.1
                            have p10640_3 := h10640c.2.2.2
                            linarith only [hlam, p10640_0]
                          · have p10640_0 := h10640c.1
                            have p10640_1 := h10640c.2.1
                            have p10640_2 := h10640c.2.2.1
                            have p10640_3 := h10640c.2.2.2
                            linarith only [h8818, hlam, p10640_0]
                          · have p10640_0 := h10640c.1
                            have p10640_1 := h10640c.2.1
                            have p10640_2 := h10640c.2.2.1
                            have p10640_3 := h10640c.2.2.2
                            linarith only [h10104, hlam, p10640_1]
                          · have p10640_0 := h10640c.1
                            have p10640_1 := h10640c.2.1
                            have p10640_2 := h10640c.2.2.1
                            have p10640_3 := h10640c.2.2.2
                            linarith only [h10625, h8818, hc05, hc13, hlam, hphi, ht01, ht0b, ht5b, p10640_1]
                          · have p10640_0 := h10640c.1
                            have p10640_1 := h10640c.2.1
                            have p10640_2 := h10640c.2.2.1
                            have p10640_3 := h10640c.2.2.2
                            linarith only [h10628, h6421, hc01, hc34, hlam, hphi, ht12, ht23, p10640_1]
                          · have p10640_0 := h10640c.1
                            have p10640_1 := h10640c.2.1
                            have p10640_2 := h10640c.2.2.1
                            have p10640_3 := h10640c.2.2.2
                            linarith only [h10625, h10628, h8818, hc02, hc34, hlam, hphi, ht23, p10640_1]
                          · have p10640_0 := h10640c.1
                            have p10640_1 := h10640c.2.1
                            have p10640_2 := h10640c.2.2.1
                            have p10640_3 := h10640c.2.2.2
                            linarith only [hlam, p10640_0]
                          · have p10640_0 := h10640c.1
                            have p10640_1 := h10640c.2.1
                            have p10640_2 := h10640c.2.2.1
                            have p10640_3 := h10640c.2.2.2
                            linarith only [h10508, hlam, p10640_1]
                          · have p10640_0 := h10640c.1
                            have p10640_1 := h10640c.2.1
                            have p10640_2 := h10640c.2.2.1
                            have p10640_3 := h10640c.2.2.2
                            linarith only [h10625, h10628, h8188, h8818, hc01, hc34, hlam, hphi, ht12, ht23, p10640_1]
                          · have p10640_0 := h10640c.1
                            have p10640_1 := h10640c.2.1
                            have p10640_2 := h10640c.2.2.1
                            have p10640_3 := h10640c.2.2.2
                            linarith only [h10104, h10626, hc01, hc12, hlam, hphi, p10640_1]
                          · have p10640_0 := h10640c.1
                            have p10640_1 := h10640c.2.1
                            have p10640_2 := h10640c.2.2.1
                            have p10640_3 := h10640c.2.2.2
                            linarith only [h10104, h10507, h10626, h10637, h10639, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p10640_1]
                          · have p10640_0 := h10640c.1
                            have p10640_1 := h10640c.2.1
                            have p10640_2 := h10640c.2.2.1
                            have p10640_3 := h10640c.2.2.2
                            linarith only [h10104, h10626, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p10640_1]
                          · have p10640_0 := h10640c.1
                            have p10640_1 := h10640c.2.1
                            have p10640_2 := h10640c.2.2.1
                            have p10640_3 := h10640c.2.2.2
                            linarith only [hlam, p10640_0]
                          · have p10640_0 := h10640c.1
                            have p10640_1 := h10640c.2.1
                            have p10640_2 := h10640c.2.2.1
                            have p10640_3 := h10640c.2.2.2
                            linarith only [h10104, h10626, h8188, hc01, hc12, hlam, hphi, p10640_1]
                          · have p10640_0 := h10640c.1
                            have p10640_1 := h10640c.2.1
                            have p10640_2 := h10640c.2.2.1
                            have p10640_3 := h10640c.2.2.2
                            linarith only [h8188, hc01, hc15, hlam, hphi, p10640_1]
                          · have p10640_0 := h10640c.1
                            have p10640_1 := h10640c.2.1
                            have p10640_2 := h10640c.2.2.1
                            have p10640_3 := h10640c.2.2.2
                            linarith only [h10507, hlam, p10640_1]
                          · have p10640_0 := h10640c.1
                            have p10640_1 := h10640c.2.1
                            have p10640_2 := h10640c.2.2.1
                            have p10640_3 := h10640c.2.2.2
                            linarith only [h10623, hlam, p10640_0]
                          · have p10640_0 := h10640c.1
                            have p10640_1 := h10640c.2.1
                            have p10640_2 := h10640c.2.2.1
                            have p10640_3 := h10640c.2.2.2
                            linarith only [h10624, hlam, p10640_1]
                          · have p10640_0 := h10640c.1
                            have p10640_1 := h10640c.2.1
                            have p10640_2 := h10640c.2.2.1
                            have p10640_3 := h10640c.2.2.2
                            linarith only [hlam, p10640_0]
                        · linarith only [h10507, h10625, h10628, h10637, h10639, h8818, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b]
                      · linarith only [h10104, h10507, h10624, h10625, h10628, h10638, h7464, h8818, hc01, hc34, hlam, hphi, ht12, ht23]
                    · linarith only [h10507, h10508, h10623, h10637, h8818, hc04, hc25, hlam, hphi, ht0b, ht5b]
                · linarith only [h10507, h10624, h10625, h10628, h10634, h7464, h8818, hc01, hc34, hlam, hphi, ht12, ht23]
            · linarith only [h10104, h10626, h10627, hc02, hc25, hlam, hphi]
          · linarith only [h10507, h10625, h10626, h8188, h8818, hc01, hc24, hlam, hphi, ht12]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h10672 | h10672
          · linarith only [h10104, h10507, h10625, h10672, h8188, hc01, hc23, hlam, hphi, ht12]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h10674 | h10674
            · rcases m.htr 1 3 4 (by decide) (by decide) with h10675 | h10675
              · rcases m.htr 1 4 5 (by decide) (by decide) with h10676 | h10676
                · rcases m.htr 2 3 4 (by decide) (by decide) with h10677 | h10677
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h10678 | h10678
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h10679 | h10679
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h10680 | h10680
                        · rcases h0bigk with h10681c | h10681c | h10681c | h10681c | h10681c | h10681c | h10681c | h10681c | h10681c | h10681c | h10681c | h10681c | h10681c | h10681c | h10681c | h10681c | h10681c | h10681c | h10681c | h10681c | h10681c | h10681c | h10681c | h10681c | h10681c
                          · have p10681_0 := h10681c.1
                            have p10681_1 := h10681c.2.1
                            have p10681_2 := h10681c.2.2.1
                            have p10681_3 := h10681c.2.2.2
                            linarith only [hlam, p10681_0]
                          · have p10681_0 := h10681c.1
                            have p10681_1 := h10681c.2.1
                            have p10681_2 := h10681c.2.2.1
                            have p10681_3 := h10681c.2.2.2
                            linarith only [h0, hlam, p10681_1]
                          · have p10681_0 := h10681c.1
                            have p10681_1 := h10681c.2.1
                            have p10681_2 := h10681c.2.2.1
                            have p10681_3 := h10681c.2.2.2
                            linarith only [h6421, hlam, p10681_0]
                          · have p10681_0 := h10681c.1
                            have p10681_1 := h10681c.2.1
                            have p10681_2 := h10681c.2.2.1
                            have p10681_3 := h10681c.2.2.2
                            linarith only [h7464, hlam, p10681_1]
                          · have p10681_0 := h10681c.1
                            have p10681_1 := h10681c.2.1
                            have p10681_2 := h10681c.2.2.1
                            have p10681_3 := h10681c.2.2.2
                            linarith only [h8188, hlam, p10681_1]
                          · have p10681_0 := h10681c.1
                            have p10681_1 := h10681c.2.1
                            have p10681_2 := h10681c.2.2.1
                            have p10681_3 := h10681c.2.2.2
                            linarith only [h10508, h10675, h8818, hc01, hc13, hlam, hphi, p10681_1]
                          · have p10681_0 := h10681c.1
                            have p10681_1 := h10681c.2.1
                            have p10681_2 := h10681c.2.2.1
                            have p10681_3 := h10681c.2.2.2
                            linarith only [hlam, p10681_0]
                          · have p10681_0 := h10681c.1
                            have p10681_1 := h10681c.2.1
                            have p10681_2 := h10681c.2.2.1
                            have p10681_3 := h10681c.2.2.2
                            linarith only [h8818, hlam, p10681_0]
                          · have p10681_0 := h10681c.1
                            have p10681_1 := h10681c.2.1
                            have p10681_2 := h10681c.2.2.1
                            have p10681_3 := h10681c.2.2.2
                            linarith only [h10104, hlam, p10681_1]
                          · have p10681_0 := h10681c.1
                            have p10681_1 := h10681c.2.1
                            have p10681_2 := h10681c.2.2.1
                            have p10681_3 := h10681c.2.2.2
                            linarith only [h10508, h10675, h8818, hc05, hc13, hlam, hphi, ht01, ht0b, ht5b, p10681_1]
                          · have p10681_0 := h10681c.1
                            have p10681_1 := h10681c.2.1
                            have p10681_2 := h10681c.2.2.1
                            have p10681_3 := h10681c.2.2.2
                            linarith only [h10508, h10675, hc01, hc13, hlam, hphi, p10681_1]
                          · have p10681_0 := h10681c.1
                            have p10681_1 := h10681c.2.1
                            have p10681_2 := h10681c.2.2.1
                            have p10681_3 := h10681c.2.2.2
                            linarith only [h10508, h10675, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p10681_1]
                          · have p10681_0 := h10681c.1
                            have p10681_1 := h10681c.2.1
                            have p10681_2 := h10681c.2.2.1
                            have p10681_3 := h10681c.2.2.2
                            linarith only [hlam, p10681_0]
                          · have p10681_0 := h10681c.1
                            have p10681_1 := h10681c.2.1
                            have p10681_2 := h10681c.2.2.1
                            have p10681_3 := h10681c.2.2.2
                            linarith only [h10508, hlam, p10681_1]
                          · have p10681_0 := h10681c.1
                            have p10681_1 := h10681c.2.1
                            have p10681_2 := h10681c.2.2.1
                            have p10681_3 := h10681c.2.2.2
                            linarith only [h10508, h10675, h8188, hc01, hc13, hlam, hphi, p10681_1]
                          · have p10681_0 := h10681c.1
                            have p10681_1 := h10681c.2.1
                            have p10681_2 := h10681c.2.2.1
                            have p10681_3 := h10681c.2.2.2
                            linarith only [h7464, hc01, hc14, hlam, hphi, p10681_1]
                          · have p10681_0 := h10681c.1
                            have p10681_1 := h10681c.2.1
                            have p10681_2 := h10681c.2.2.1
                            have p10681_3 := h10681c.2.2.2
                            linarith only [h10104, h10507, h10677, h10678, h10680, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p10681_1]
                          · have p10681_0 := h10681c.1
                            have p10681_1 := h10681c.2.1
                            have p10681_2 := h10681c.2.2.1
                            have p10681_3 := h10681c.2.2.2
                            linarith only [h10508, h10675, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p10681_1]
                          · have p10681_0 := h10681c.1
                            have p10681_1 := h10681c.2.1
                            have p10681_2 := h10681c.2.2.1
                            have p10681_3 := h10681c.2.2.2
                            linarith only [hlam, p10681_0]
                          · have p10681_0 := h10681c.1
                            have p10681_1 := h10681c.2.1
                            have p10681_2 := h10681c.2.2.1
                            have p10681_3 := h10681c.2.2.2
                            linarith only [h10508, h10675, h8188, hc01, hc13, hlam, hphi, p10681_1]
                          · have p10681_0 := h10681c.1
                            have p10681_1 := h10681c.2.1
                            have p10681_2 := h10681c.2.2.1
                            have p10681_3 := h10681c.2.2.2
                            linarith only [h10672, h10674, h10677, h8188, hc01, hc23, hlam, hphi, ht12, p10681_1]
                          · have p10681_0 := h10681c.1
                            have p10681_1 := h10681c.2.1
                            have p10681_2 := h10681c.2.2.1
                            have p10681_3 := h10681c.2.2.2
                            linarith only [h10507, hlam, p10681_1]
                          · have p10681_0 := h10681c.1
                            have p10681_1 := h10681c.2.1
                            have p10681_2 := h10681c.2.2.1
                            have p10681_3 := h10681c.2.2.2
                            linarith only [h10623, hlam, p10681_0]
                          · have p10681_0 := h10681c.1
                            have p10681_1 := h10681c.2.1
                            have p10681_2 := h10681c.2.2.1
                            have p10681_3 := h10681c.2.2.2
                            linarith only [h10624, hlam, p10681_1]
                          · have p10681_0 := h10681c.1
                            have p10681_1 := h10681c.2.1
                            have p10681_2 := h10681c.2.2.1
                            have p10681_3 := h10681c.2.2.2
                            linarith only [hlam, p10681_0]
                        · linarith only [h10508, h10624, h10680, hlam]
                      · linarith only [h10507, h10508, h10624, h10672, h10675, h10679, h8818, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                    · linarith only [h10508, h10625, h10675, h10678, h8818, hc02, hc35, hlam, hphi, ht23]
                  · linarith only [h10625, h10675, h10677, hlam]
                · linarith only [h10507, h10508, h10624, h10625, h10675, h10676, h7464, h8818, hc01, hc23, hlam, hphi, ht12]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h10712 | h10712
                · rcases m.htr 2 3 4 (by decide) (by decide) with h10713 | h10713
                  · linarith only [h10625, h10674, h10675, h10713, h8188, hc01, hc23, hlam, hphi, ht12]
                  · linarith only [h10625, h10674, h10713, h8188, hc01, hc34, hlam, hphi, ht12, ht23]
                · linarith only [h0, h10507, h10624, h10625, h10712, h7464, hc01, hc23, hlam, hphi, ht12]
            · linarith only [h0, h10507, h10674, hlam]
      · linarith only [h10507, h10508, h10624, h8818, hlam]
    · linarith only [h10507, h10623, h8818, hlam]

end R2N4
