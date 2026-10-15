import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5434000 in
set_option maxHeartbeats 5434000 in
theorem r1l7_21_14_H_I_L_I_s6_x0 (m : N7Model)
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg5235 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h6110 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
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
  have h0 := hg0
  have h5235 := hg5235
  rcases m.htr 0 1 5 (by decide) (by decide) with h6111 | h6111
  · rcases m.htr 0 2 4 (by decide) (by decide) with h6112 | h6112
    · rcases m.htr 0 3 4 (by decide) (by decide) with h6113 | h6113
      · rcases m.htr 0 4 5 (by decide) (by decide) with h6114 | h6114
        · rcases m.htr 1 2 3 (by decide) (by decide) with h6115 | h6115
          · rcases m.htr 1 2 4 (by decide) (by decide) with h6116 | h6116
            · rcases m.htr 1 2 5 (by decide) (by decide) with h6117 | h6117
              · rcases m.htr 1 3 4 (by decide) (by decide) with h6118 | h6118
                · rcases m.htr 1 3 5 (by decide) (by decide) with h6119 | h6119
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h6120 | h6120
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h6121 | h6121
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h6122 | h6122
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h6123 | h6123
                          · rcases h1bigk with h6124c | h6124c | h6124c | h6124c | h6124c | h6124c | h6124c | h6124c | h6124c | h6124c | h6124c | h6124c | h6124c | h6124c | h6124c | h6124c | h6124c | h6124c | h6124c | h6124c | h6124c | h6124c | h6124c | h6124c | h6124c
                            · have p6124_0 := h6124c.1
                              have p6124_1 := h6124c.2.1
                              have p6124_2 := h6124c.2.2.1
                              have p6124_3 := h6124c.2.2.2
                              linarith only [hlam, p6124_0]
                            · have p6124_0 := h6124c.1
                              have p6124_1 := h6124c.2.1
                              have p6124_2 := h6124c.2.2.1
                              have p6124_3 := h6124c.2.2.2
                              linarith only [h0, hlam, p6124_0]
                            · have p6124_0 := h6124c.1
                              have p6124_1 := h6124c.2.1
                              have p6124_2 := h6124c.2.2.1
                              have p6124_3 := h6124c.2.2.2
                              linarith only [h5235, hlam, p6124_0]
                            · have p6124_0 := h6124c.1
                              have p6124_1 := h6124c.2.1
                              have p6124_2 := h6124c.2.2.1
                              have p6124_3 := h6124c.2.2.2
                              linarith only [h6116, h6121, h6123, hc01, hc45, hlam, hphi, ht0b, ht5b, p6124_1]
                            · have p6124_0 := h6124c.1
                              have p6124_1 := h6124c.2.1
                              have p6124_2 := h6124c.2.2.1
                              have p6124_3 := h6124c.2.2.2
                              linarith only [h5235, h6115, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b, p6124_1]
                            · have p6124_0 := h6124c.1
                              have p6124_1 := h6124c.2.1
                              have p6124_2 := h6124c.2.2.1
                              have p6124_3 := h6124c.2.2.2
                              linarith only [hc01, hc12, hlam, hphi, p6124_1]
                            · have p6124_0 := h6124c.1
                              have p6124_1 := h6124c.2.1
                              have p6124_2 := h6124c.2.2.1
                              have p6124_3 := h6124c.2.2.2
                              linarith only [hlam, p6124_0]
                            · have p6124_0 := h6124c.1
                              have p6124_1 := h6124c.2.1
                              have p6124_2 := h6124c.2.2.1
                              have p6124_3 := h6124c.2.2.2
                              linarith only [h5235, hc01, hc12, hlam, hphi, p6124_1]
                            · have p6124_0 := h6124c.1
                              have p6124_1 := h6124c.2.1
                              have p6124_2 := h6124c.2.2.1
                              have p6124_3 := h6124c.2.2.2
                              linarith only [h6116, h6121, h6123, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p6124_1]
                            · have p6124_0 := h6124c.1
                              have p6124_1 := h6124c.2.1
                              have p6124_2 := h6124c.2.2.1
                              have p6124_3 := h6124c.2.2.2
                              rcases p6124_3 (m.d 0 1) (by simp) with h6134 | h6134
                              · linarith only [h0, h6134, hlam]
                              · linarith only [h6111, h6134, hlam]
                            · have p6124_0 := h6124c.1
                              have p6124_1 := h6124c.2.1
                              have p6124_2 := h6124c.2.2.1
                              have p6124_3 := h6124c.2.2.2
                              linarith only [h6110, h6116, h6121, h6123, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p6124_1]
                            · have p6124_0 := h6124c.1
                              have p6124_1 := h6124c.2.1
                              have p6124_2 := h6124c.2.2.1
                              have p6124_3 := h6124c.2.2.2
                              linarith only [h6115, hlam, p6124_0]
                            · have p6124_0 := h6124c.1
                              have p6124_1 := h6124c.2.1
                              have p6124_2 := h6124c.2.2.1
                              have p6124_3 := h6124c.2.2.2
                              linarith only [hlam, p6124_0]
                            · have p6124_0 := h6124c.1
                              have p6124_1 := h6124c.2.1
                              have p6124_2 := h6124c.2.2.1
                              have p6124_3 := h6124c.2.2.2
                              linarith only [h6115, h6116, h6121, h6123, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p6124_1]
                            · have p6124_0 := h6124c.1
                              have p6124_1 := h6124c.2.1
                              have p6124_2 := h6124c.2.2.1
                              have p6124_3 := h6124c.2.2.2
                              rcases p6124_3 (m.d 0 1) (by simp) with h6141 | h6141
                              · linarith only [h5235, h6141, hlam]
                              · linarith only [h6111, h6141, hlam]
                            · have p6124_0 := h6124c.1
                              have p6124_1 := h6124c.2.1
                              have p6124_2 := h6124c.2.2.1
                              have p6124_3 := h6124c.2.2.2
                              linarith only [h6110, hlam, p6124_0]
                            · have p6124_0 := h6124c.1
                              have p6124_1 := h6124c.2.1
                              have p6124_2 := h6124c.2.2.1
                              have p6124_3 := h6124c.2.2.2
                              linarith only [h6116, hlam, p6124_0]
                            · have p6124_0 := h6124c.1
                              have p6124_1 := h6124c.2.1
                              have p6124_2 := h6124c.2.2.1
                              have p6124_3 := h6124c.2.2.2
                              linarith only [h6118, hlam, p6124_1]
                            · have p6124_0 := h6124c.1
                              have p6124_1 := h6124c.2.1
                              have p6124_2 := h6124c.2.2.1
                              have p6124_3 := h6124c.2.2.2
                              linarith only [hlam, p6124_0]
                            · have p6124_0 := h6124c.1
                              have p6124_1 := h6124c.2.1
                              have p6124_2 := h6124c.2.2.1
                              have p6124_3 := h6124c.2.2.2
                              linarith only [h6110, h6117, h6122, hc01, hc45, hlam, hphi, ht0b, ht5b, p6124_1]
                            · have p6124_0 := h6124c.1
                              have p6124_1 := h6124c.2.1
                              have p6124_2 := h6124c.2.2.1
                              have p6124_3 := h6124c.2.2.2
                              linarith only [h6111, hlam, p6124_0]
                            · have p6124_0 := h6124c.1
                              have p6124_1 := h6124c.2.1
                              have p6124_2 := h6124c.2.2.1
                              have p6124_3 := h6124c.2.2.2
                              linarith only [h6117, hlam, p6124_0]
                            · have p6124_0 := h6124c.1
                              have p6124_1 := h6124c.2.1
                              have p6124_2 := h6124c.2.2.1
                              have p6124_3 := h6124c.2.2.2
                              linarith only [h6119, hlam, p6124_0]
                            · have p6124_0 := h6124c.1
                              have p6124_1 := h6124c.2.1
                              have p6124_2 := h6124c.2.2.1
                              have p6124_3 := h6124c.2.2.2
                              linarith only [h6120, hlam, p6124_0]
                            · have p6124_0 := h6124c.1
                              have p6124_1 := h6124c.2.1
                              have p6124_2 := h6124c.2.2.1
                              have p6124_3 := h6124c.2.2.2
                              linarith only [hlam, p6124_0]
                          · linarith only [h5235, h6110, h6115, h6120, h6123, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · linarith only [h5235, h6110, h6115, h6120, h6122, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h6156 | h6156
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h6157 | h6157
                          · rcases h1bigk with h6158c | h6158c | h6158c | h6158c | h6158c | h6158c | h6158c | h6158c | h6158c | h6158c | h6158c | h6158c | h6158c | h6158c | h6158c | h6158c | h6158c | h6158c | h6158c | h6158c | h6158c | h6158c | h6158c | h6158c | h6158c
                            · have p6158_0 := h6158c.1
                              have p6158_1 := h6158c.2.1
                              have p6158_2 := h6158c.2.2.1
                              have p6158_3 := h6158c.2.2.2
                              linarith only [hlam, p6158_0]
                            · have p6158_0 := h6158c.1
                              have p6158_1 := h6158c.2.1
                              have p6158_2 := h6158c.2.2.1
                              have p6158_3 := h6158c.2.2.2
                              linarith only [h0, hlam, p6158_0]
                            · have p6158_0 := h6158c.1
                              have p6158_1 := h6158c.2.1
                              have p6158_2 := h6158c.2.2.1
                              have p6158_3 := h6158c.2.2.2
                              linarith only [h5235, hlam, p6158_0]
                            · have p6158_0 := h6158c.1
                              have p6158_1 := h6158c.2.1
                              have p6158_2 := h6158c.2.2.1
                              have p6158_3 := h6158c.2.2.2
                              linarith only [h5235, h6115, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p6158_1]
                            · have p6158_0 := h6158c.1
                              have p6158_1 := h6158c.2.1
                              have p6158_2 := h6158c.2.2.1
                              have p6158_3 := h6158c.2.2.2
                              linarith only [h5235, h6115, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b, p6158_1]
                            · have p6158_0 := h6158c.1
                              have p6158_1 := h6158c.2.1
                              have p6158_2 := h6158c.2.2.1
                              have p6158_3 := h6158c.2.2.2
                              linarith only [hc01, hc12, hlam, hphi, p6158_1]
                            · have p6158_0 := h6158c.1
                              have p6158_1 := h6158c.2.1
                              have p6158_2 := h6158c.2.2.1
                              have p6158_3 := h6158c.2.2.2
                              linarith only [hlam, p6158_0]
                            · have p6158_0 := h6158c.1
                              have p6158_1 := h6158c.2.1
                              have p6158_2 := h6158c.2.2.1
                              have p6158_3 := h6158c.2.2.2
                              linarith only [h5235, hc01, hc12, hlam, hphi, p6158_1]
                            · have p6158_0 := h6158c.1
                              have p6158_1 := h6158c.2.1
                              have p6158_2 := h6158c.2.2.1
                              have p6158_3 := h6158c.2.2.2
                              linarith only [h6116, h6156, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p6158_1]
                            · have p6158_0 := h6158c.1
                              have p6158_1 := h6158c.2.1
                              have p6158_2 := h6158c.2.2.1
                              have p6158_3 := h6158c.2.2.2
                              rcases p6158_3 (m.d 0 1) (by simp) with h6168 | h6168
                              · linarith only [h0, h6168, hlam]
                              · linarith only [h6111, h6168, hlam]
                            · have p6158_0 := h6158c.1
                              have p6158_1 := h6158c.2.1
                              have p6158_2 := h6158c.2.2.1
                              have p6158_3 := h6158c.2.2.2
                              linarith only [h6110, h6118, h6121, hc13, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6158_1]
                            · have p6158_0 := h6158c.1
                              have p6158_1 := h6158c.2.1
                              have p6158_2 := h6158c.2.2.1
                              have p6158_3 := h6158c.2.2.2
                              linarith only [h6115, hlam, p6158_0]
                            · have p6158_0 := h6158c.1
                              have p6158_1 := h6158c.2.1
                              have p6158_2 := h6158c.2.2.1
                              have p6158_3 := h6158c.2.2.2
                              linarith only [hlam, p6158_0]
                            · have p6158_0 := h6158c.1
                              have p6158_1 := h6158c.2.1
                              have p6158_2 := h6158c.2.2.1
                              have p6158_3 := h6158c.2.2.2
                              linarith only [h6115, h6118, h6121, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6158_1]
                            · have p6158_0 := h6158c.1
                              have p6158_1 := h6158c.2.1
                              have p6158_2 := h6158c.2.2.1
                              have p6158_3 := h6158c.2.2.2
                              rcases p6158_3 (m.d 0 1) (by simp) with h6175 | h6175
                              · linarith only [h5235, h6175, hlam]
                              · linarith only [h6111, h6175, hlam]
                            · have p6158_0 := h6158c.1
                              have p6158_1 := h6158c.2.1
                              have p6158_2 := h6158c.2.2.1
                              have p6158_3 := h6158c.2.2.2
                              linarith only [h6110, hlam, p6158_0]
                            · have p6158_0 := h6158c.1
                              have p6158_1 := h6158c.2.1
                              have p6158_2 := h6158c.2.2.1
                              have p6158_3 := h6158c.2.2.2
                              linarith only [h6116, hlam, p6158_0]
                            · have p6158_0 := h6158c.1
                              have p6158_1 := h6158c.2.1
                              have p6158_2 := h6158c.2.2.1
                              have p6158_3 := h6158c.2.2.2
                              linarith only [h6118, hlam, p6158_1]
                            · have p6158_0 := h6158c.1
                              have p6158_1 := h6158c.2.1
                              have p6158_2 := h6158c.2.2.1
                              have p6158_3 := h6158c.2.2.2
                              linarith only [hlam, p6158_0]
                            · have p6158_0 := h6158c.1
                              have p6158_1 := h6158c.2.1
                              have p6158_2 := h6158c.2.2.1
                              have p6158_3 := h6158c.2.2.2
                              linarith only [h6110, h6117, h6156, hc01, hc45, hlam, hphi, ht0b, ht5b, p6158_1]
                            · have p6158_0 := h6158c.1
                              have p6158_1 := h6158c.2.1
                              have p6158_2 := h6158c.2.2.1
                              have p6158_3 := h6158c.2.2.2
                              linarith only [h6111, hlam, p6158_0]
                            · have p6158_0 := h6158c.1
                              have p6158_1 := h6158c.2.1
                              have p6158_2 := h6158c.2.2.1
                              have p6158_3 := h6158c.2.2.2
                              linarith only [h6117, hlam, p6158_0]
                            · have p6158_0 := h6158c.1
                              have p6158_1 := h6158c.2.1
                              have p6158_2 := h6158c.2.2.1
                              have p6158_3 := h6158c.2.2.2
                              linarith only [h6119, hlam, p6158_0]
                            · have p6158_0 := h6158c.1
                              have p6158_1 := h6158c.2.1
                              have p6158_2 := h6158c.2.2.1
                              have p6158_3 := h6158c.2.2.2
                              linarith only [h6120, hlam, p6158_0]
                            · have p6158_0 := h6158c.1
                              have p6158_1 := h6158c.2.1
                              have p6158_2 := h6158c.2.2.1
                              have p6158_3 := h6158c.2.2.2
                              linarith only [hlam, p6158_0]
                          · linarith only [h5235, h6111, h6115, h6117, h6121, h6156, h6157, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · linarith only [h5235, h6110, h6115, h6120, h6156, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h6190 | h6190
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h6191 | h6191
                        · linarith only [h6116, h6120, h6191, hlam]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h6193 | h6193
                          · linarith only [h6115, h6120, h6190, h6193, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · rcases h1bigk with h6195c | h6195c | h6195c | h6195c | h6195c | h6195c | h6195c | h6195c | h6195c | h6195c | h6195c | h6195c | h6195c | h6195c | h6195c | h6195c | h6195c | h6195c | h6195c | h6195c | h6195c | h6195c | h6195c | h6195c | h6195c
                            · have p6195_0 := h6195c.1
                              have p6195_1 := h6195c.2.1
                              have p6195_2 := h6195c.2.2.1
                              have p6195_3 := h6195c.2.2.2
                              linarith only [hlam, p6195_0]
                            · have p6195_0 := h6195c.1
                              have p6195_1 := h6195c.2.1
                              have p6195_2 := h6195c.2.2.1
                              have p6195_3 := h6195c.2.2.2
                              linarith only [h0, hlam, p6195_0]
                            · have p6195_0 := h6195c.1
                              have p6195_1 := h6195c.2.1
                              have p6195_2 := h6195c.2.2.1
                              have p6195_3 := h6195c.2.2.2
                              linarith only [h5235, hlam, p6195_0]
                            · have p6195_0 := h6195c.1
                              have p6195_1 := h6195c.2.1
                              have p6195_2 := h6195c.2.2.1
                              have p6195_3 := h6195c.2.2.2
                              linarith only [h5235, h6115, h6116, h6190, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p6195_1]
                            · have p6195_0 := h6195c.1
                              have p6195_1 := h6195c.2.1
                              have p6195_2 := h6195c.2.2.1
                              have p6195_3 := h6195c.2.2.2
                              linarith only [h5235, h6115, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b, p6195_1]
                            · have p6195_0 := h6195c.1
                              have p6195_1 := h6195c.2.1
                              have p6195_2 := h6195c.2.2.1
                              have p6195_3 := h6195c.2.2.2
                              linarith only [hc01, hc12, hlam, hphi, p6195_1]
                            · have p6195_0 := h6195c.1
                              have p6195_1 := h6195c.2.1
                              have p6195_2 := h6195c.2.2.1
                              have p6195_3 := h6195c.2.2.2
                              linarith only [hlam, p6195_0]
                            · have p6195_0 := h6195c.1
                              have p6195_1 := h6195c.2.1
                              have p6195_2 := h6195c.2.2.1
                              have p6195_3 := h6195c.2.2.2
                              linarith only [h5235, hc01, hc12, hlam, hphi, p6195_1]
                            · have p6195_0 := h6195c.1
                              have p6195_1 := h6195c.2.1
                              have p6195_2 := h6195c.2.2.1
                              have p6195_3 := h6195c.2.2.2
                              rcases p6195_3 (m.d 0 1) (by simp) with h6204 | h6204
                              · linarith only [h0, h6204, hlam]
                              · linarith only [h6110, h6204, hlam]
                            · have p6195_0 := h6195c.1
                              have p6195_1 := h6195c.2.1
                              have p6195_2 := h6195c.2.2.1
                              have p6195_3 := h6195c.2.2.2
                              rcases p6195_3 (m.d 0 1) (by simp) with h6207 | h6207
                              · linarith only [h0, h6207, hlam]
                              · linarith only [h6111, h6207, hlam]
                            · have p6195_0 := h6195c.1
                              have p6195_1 := h6195c.2.1
                              have p6195_2 := h6195c.2.2.1
                              have p6195_3 := h6195c.2.2.2
                              linarith only [h6110, h6114, h6116, h6120, h6190, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p6195_1]
                            · have p6195_0 := h6195c.1
                              have p6195_1 := h6195c.2.1
                              have p6195_2 := h6195c.2.2.1
                              have p6195_3 := h6195c.2.2.2
                              linarith only [h6115, hlam, p6195_0]
                            · have p6195_0 := h6195c.1
                              have p6195_1 := h6195c.2.1
                              have p6195_2 := h6195c.2.2.1
                              have p6195_3 := h6195c.2.2.2
                              linarith only [hlam, p6195_0]
                            · have p6195_0 := h6195c.1
                              have p6195_1 := h6195c.2.1
                              have p6195_2 := h6195c.2.2.1
                              have p6195_3 := h6195c.2.2.2
                              rcases p6195_3 (m.d 0 1) (by simp) with h6213 | h6213
                              · linarith only [h5235, h6213, hlam]
                              · linarith only [h6110, h6213, hlam]
                            · have p6195_0 := h6195c.1
                              have p6195_1 := h6195c.2.1
                              have p6195_2 := h6195c.2.2.1
                              have p6195_3 := h6195c.2.2.2
                              rcases p6195_3 (m.d 0 1) (by simp) with h6216 | h6216
                              · linarith only [h5235, h6216, hlam]
                              · linarith only [h6111, h6216, hlam]
                            · have p6195_0 := h6195c.1
                              have p6195_1 := h6195c.2.1
                              have p6195_2 := h6195c.2.2.1
                              have p6195_3 := h6195c.2.2.2
                              linarith only [h6110, hlam, p6195_0]
                            · have p6195_0 := h6195c.1
                              have p6195_1 := h6195c.2.1
                              have p6195_2 := h6195c.2.2.1
                              have p6195_3 := h6195c.2.2.2
                              linarith only [h6116, hlam, p6195_0]
                            · have p6195_0 := h6195c.1
                              have p6195_1 := h6195c.2.1
                              have p6195_2 := h6195c.2.2.1
                              have p6195_3 := h6195c.2.2.2
                              linarith only [h6118, hlam, p6195_1]
                            · have p6195_0 := h6195c.1
                              have p6195_1 := h6195c.2.1
                              have p6195_2 := h6195c.2.2.1
                              have p6195_3 := h6195c.2.2.2
                              linarith only [hlam, p6195_0]
                            · have p6195_0 := h6195c.1
                              have p6195_1 := h6195c.2.1
                              have p6195_2 := h6195c.2.2.1
                              have p6195_3 := h6195c.2.2.2
                              linarith only [h6120, hlam, p6195_1]
                            · have p6195_0 := h6195c.1
                              have p6195_1 := h6195c.2.1
                              have p6195_2 := h6195c.2.2.1
                              have p6195_3 := h6195c.2.2.2
                              linarith only [h6111, hlam, p6195_0]
                            · have p6195_0 := h6195c.1
                              have p6195_1 := h6195c.2.1
                              have p6195_2 := h6195c.2.2.1
                              have p6195_3 := h6195c.2.2.2
                              linarith only [h6117, hlam, p6195_0]
                            · have p6195_0 := h6195c.1
                              have p6195_1 := h6195c.2.1
                              have p6195_2 := h6195c.2.2.1
                              have p6195_3 := h6195c.2.2.2
                              linarith only [h6119, hlam, p6195_0]
                            · have p6195_0 := h6195c.1
                              have p6195_1 := h6195c.2.1
                              have p6195_2 := h6195c.2.2.1
                              have p6195_3 := h6195c.2.2.2
                              linarith only [h6111, h6116, h6190, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p6195_1]
                            · have p6195_0 := h6195c.1
                              have p6195_1 := h6195c.2.1
                              have p6195_2 := h6195c.2.2.1
                              have p6195_3 := h6195c.2.2.2
                              linarith only [hlam, p6195_0]
                      · linarith only [h5235, h6110, h6114, h6115, h6118, h6120, h6190, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                  · linarith only [h5235, h6111, h6119, hlam]
                · linarith only [h5235, h6113, h6118, hlam]
              · linarith only [h5235, h6111, h6115, h6117, hlam]
            · linarith only [h0, h6112, h6116, hlam]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h6234 | h6234
            · rcases m.htr 1 2 5 (by decide) (by decide) with h6235 | h6235
              · rcases m.htr 1 3 4 (by decide) (by decide) with h6236 | h6236
                · rcases m.htr 1 3 5 (by decide) (by decide) with h6237 | h6237
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h6238 | h6238
                    · linarith only [h0, h6110, h6115, h6238, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                    · linarith only [h0, h6110, h6114, h6115, h6238, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                  · linarith only [h0, h6111, h6115, h6237, hlam]
                · linarith only [h5235, h6113, h6236, hlam]
              · linarith only [h0, h6111, h6235, hlam]
            · linarith only [h0, h6112, h6234, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h6245 | h6245
          · rcases m.htr 1 2 4 (by decide) (by decide) with h6246 | h6246
            · rcases m.htr 1 2 5 (by decide) (by decide) with h6247 | h6247
              · rcases m.htr 1 3 4 (by decide) (by decide) with h6248 | h6248
                · rcases m.htr 1 3 5 (by decide) (by decide) with h6249 | h6249
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h6250 | h6250
                    · linarith only [h5235, h6110, h6114, h6245, h6250, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h6252 | h6252
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h6253 | h6253
                        · linarith only [h6110, h6114, h6246, h6253, hlam]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h6255 | h6255
                          · linarith only [h6110, h6114, h6246, h6252, h6255, hlam]
                          · rcases h1bigk with h6257c | h6257c | h6257c | h6257c | h6257c | h6257c | h6257c | h6257c | h6257c | h6257c | h6257c | h6257c | h6257c | h6257c | h6257c | h6257c | h6257c | h6257c | h6257c | h6257c | h6257c | h6257c | h6257c | h6257c | h6257c
                            · have p6257_0 := h6257c.1
                              have p6257_1 := h6257c.2.1
                              have p6257_2 := h6257c.2.2.1
                              have p6257_3 := h6257c.2.2.2
                              linarith only [hlam, p6257_0]
                            · have p6257_0 := h6257c.1
                              have p6257_1 := h6257c.2.1
                              have p6257_2 := h6257c.2.2.1
                              have p6257_3 := h6257c.2.2.2
                              linarith only [h0, hlam, p6257_0]
                            · have p6257_0 := h6257c.1
                              have p6257_1 := h6257c.2.1
                              have p6257_2 := h6257c.2.2.1
                              have p6257_3 := h6257c.2.2.2
                              linarith only [h5235, hlam, p6257_0]
                            · have p6257_0 := h6257c.1
                              have p6257_1 := h6257c.2.1
                              have p6257_2 := h6257c.2.2.1
                              have p6257_3 := h6257c.2.2.2
                              linarith only [h5235, h6245, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p6257_1]
                            · have p6257_0 := h6257c.1
                              have p6257_1 := h6257c.2.1
                              have p6257_2 := h6257c.2.2.1
                              have p6257_3 := h6257c.2.2.2
                              linarith only [h5235, h6245, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b, p6257_1]
                            · have p6257_0 := h6257c.1
                              have p6257_1 := h6257c.2.1
                              have p6257_2 := h6257c.2.2.1
                              have p6257_3 := h6257c.2.2.2
                              linarith only [hc01, hc12, hlam, hphi, p6257_1]
                            · have p6257_0 := h6257c.1
                              have p6257_1 := h6257c.2.1
                              have p6257_2 := h6257c.2.2.1
                              have p6257_3 := h6257c.2.2.2
                              linarith only [hlam, p6257_0]
                            · have p6257_0 := h6257c.1
                              have p6257_1 := h6257c.2.1
                              have p6257_2 := h6257c.2.2.1
                              have p6257_3 := h6257c.2.2.2
                              linarith only [h5235, hc01, hc12, hlam, hphi, p6257_1]
                            · have p6257_0 := h6257c.1
                              have p6257_1 := h6257c.2.1
                              have p6257_2 := h6257c.2.2.1
                              have p6257_3 := h6257c.2.2.2
                              rcases p6257_3 (m.d 0 1) (by simp) with h6266 | h6266
                              · linarith only [h0, h6266, hlam]
                              · linarith only [h6110, h6266, hlam]
                            · have p6257_0 := h6257c.1
                              have p6257_1 := h6257c.2.1
                              have p6257_2 := h6257c.2.2.1
                              have p6257_3 := h6257c.2.2.2
                              rcases p6257_3 (m.d 0 1) (by simp) with h6269 | h6269
                              · linarith only [h0, h6269, hlam]
                              · linarith only [h6111, h6269, hlam]
                            · have p6257_0 := h6257c.1
                              have p6257_1 := h6257c.2.1
                              have p6257_2 := h6257c.2.2.1
                              have p6257_3 := h6257c.2.2.2
                              linarith only [h6111, h6246, h6250, h6252, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p6257_1]
                            · have p6257_0 := h6257c.1
                              have p6257_1 := h6257c.2.1
                              have p6257_2 := h6257c.2.2.1
                              have p6257_3 := h6257c.2.2.2
                              linarith only [h6245, hlam, p6257_0]
                            · have p6257_0 := h6257c.1
                              have p6257_1 := h6257c.2.1
                              have p6257_2 := h6257c.2.2.1
                              have p6257_3 := h6257c.2.2.2
                              linarith only [hlam, p6257_0]
                            · have p6257_0 := h6257c.1
                              have p6257_1 := h6257c.2.1
                              have p6257_2 := h6257c.2.2.1
                              have p6257_3 := h6257c.2.2.2
                              rcases p6257_3 (m.d 0 1) (by simp) with h6275 | h6275
                              · linarith only [h5235, h6275, hlam]
                              · linarith only [h6110, h6275, hlam]
                            · have p6257_0 := h6257c.1
                              have p6257_1 := h6257c.2.1
                              have p6257_2 := h6257c.2.2.1
                              have p6257_3 := h6257c.2.2.2
                              rcases p6257_3 (m.d 0 1) (by simp) with h6278 | h6278
                              · linarith only [h5235, h6278, hlam]
                              · linarith only [h6111, h6278, hlam]
                            · have p6257_0 := h6257c.1
                              have p6257_1 := h6257c.2.1
                              have p6257_2 := h6257c.2.2.1
                              have p6257_3 := h6257c.2.2.2
                              linarith only [h6110, hlam, p6257_0]
                            · have p6257_0 := h6257c.1
                              have p6257_1 := h6257c.2.1
                              have p6257_2 := h6257c.2.2.1
                              have p6257_3 := h6257c.2.2.2
                              linarith only [h6246, hlam, p6257_0]
                            · have p6257_0 := h6257c.1
                              have p6257_1 := h6257c.2.1
                              have p6257_2 := h6257c.2.2.1
                              have p6257_3 := h6257c.2.2.2
                              linarith only [h6248, hlam, p6257_1]
                            · have p6257_0 := h6257c.1
                              have p6257_1 := h6257c.2.1
                              have p6257_2 := h6257c.2.2.1
                              have p6257_3 := h6257c.2.2.2
                              linarith only [hlam, p6257_0]
                            · have p6257_0 := h6257c.1
                              have p6257_1 := h6257c.2.1
                              have p6257_2 := h6257c.2.2.1
                              have p6257_3 := h6257c.2.2.2
                              linarith only [h6250, hlam, p6257_1]
                            · have p6257_0 := h6257c.1
                              have p6257_1 := h6257c.2.1
                              have p6257_2 := h6257c.2.2.1
                              have p6257_3 := h6257c.2.2.2
                              linarith only [h6111, hlam, p6257_0]
                            · have p6257_0 := h6257c.1
                              have p6257_1 := h6257c.2.1
                              have p6257_2 := h6257c.2.2.1
                              have p6257_3 := h6257c.2.2.2
                              linarith only [h6247, hlam, p6257_0]
                            · have p6257_0 := h6257c.1
                              have p6257_1 := h6257c.2.1
                              have p6257_2 := h6257c.2.2.1
                              have p6257_3 := h6257c.2.2.2
                              linarith only [h6249, hlam, p6257_0]
                            · have p6257_0 := h6257c.1
                              have p6257_1 := h6257c.2.1
                              have p6257_2 := h6257c.2.2.1
                              have p6257_3 := h6257c.2.2.2
                              linarith only [h6111, h6246, h6252, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p6257_1]
                            · have p6257_0 := h6257c.1
                              have p6257_1 := h6257c.2.1
                              have p6257_2 := h6257c.2.2.1
                              have p6257_3 := h6257c.2.2.2
                              linarith only [hlam, p6257_0]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h6291 | h6291
                        · linarith only [h6112, h6114, h6291, hlam]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h6293 | h6293
                          · linarith only [h6110, h6114, h6248, h6293, hlam]
                          · rcases h1bigk with h6295c | h6295c | h6295c | h6295c | h6295c | h6295c | h6295c | h6295c | h6295c | h6295c | h6295c | h6295c | h6295c | h6295c | h6295c | h6295c | h6295c | h6295c | h6295c | h6295c | h6295c | h6295c | h6295c | h6295c | h6295c
                            · have p6295_0 := h6295c.1
                              have p6295_1 := h6295c.2.1
                              have p6295_2 := h6295c.2.2.1
                              have p6295_3 := h6295c.2.2.2
                              linarith only [hlam, p6295_0]
                            · have p6295_0 := h6295c.1
                              have p6295_1 := h6295c.2.1
                              have p6295_2 := h6295c.2.2.1
                              have p6295_3 := h6295c.2.2.2
                              linarith only [h0, hlam, p6295_0]
                            · have p6295_0 := h6295c.1
                              have p6295_1 := h6295c.2.1
                              have p6295_2 := h6295c.2.2.1
                              have p6295_3 := h6295c.2.2.2
                              linarith only [h5235, hlam, p6295_0]
                            · have p6295_0 := h6295c.1
                              have p6295_1 := h6295c.2.1
                              have p6295_2 := h6295c.2.2.1
                              have p6295_3 := h6295c.2.2.2
                              linarith only [h5235, h6245, h6248, h6252, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6295_1]
                            · have p6295_0 := h6295c.1
                              have p6295_1 := h6295c.2.1
                              have p6295_2 := h6295c.2.2.1
                              have p6295_3 := h6295c.2.2.2
                              linarith only [h5235, h6245, h6248, h6250, h6252, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6295_1]
                            · have p6295_0 := h6295c.1
                              have p6295_1 := h6295c.2.1
                              have p6295_2 := h6295c.2.2.1
                              have p6295_3 := h6295c.2.2.2
                              linarith only [hc01, hc12, hlam, hphi, p6295_1]
                            · have p6295_0 := h6295c.1
                              have p6295_1 := h6295c.2.1
                              have p6295_2 := h6295c.2.2.1
                              have p6295_3 := h6295c.2.2.2
                              linarith only [hlam, p6295_0]
                            · have p6295_0 := h6295c.1
                              have p6295_1 := h6295c.2.1
                              have p6295_2 := h6295c.2.2.1
                              have p6295_3 := h6295c.2.2.2
                              linarith only [h5235, hc01, hc12, hlam, hphi, p6295_1]
                            · have p6295_0 := h6295c.1
                              have p6295_1 := h6295c.2.1
                              have p6295_2 := h6295c.2.2.1
                              have p6295_3 := h6295c.2.2.2
                              linarith only [h6248, h6252, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6295_1]
                            · have p6295_0 := h6295c.1
                              have p6295_1 := h6295c.2.1
                              have p6295_2 := h6295c.2.2.1
                              have p6295_3 := h6295c.2.2.2
                              linarith only [h6248, h6250, h6252, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6295_1]
                            · have p6295_0 := h6295c.1
                              have p6295_1 := h6295c.2.1
                              have p6295_2 := h6295c.2.2.1
                              have p6295_3 := h6295c.2.2.2
                              linarith only [h6111, h6248, h6250, h6252, hc13, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6295_1]
                            · have p6295_0 := h6295c.1
                              have p6295_1 := h6295c.2.1
                              have p6295_2 := h6295c.2.2.1
                              have p6295_3 := h6295c.2.2.2
                              linarith only [h6245, hlam, p6295_0]
                            · have p6295_0 := h6295c.1
                              have p6295_1 := h6295c.2.1
                              have p6295_2 := h6295c.2.2.1
                              have p6295_3 := h6295c.2.2.2
                              linarith only [hlam, p6295_0]
                            · have p6295_0 := h6295c.1
                              have p6295_1 := h6295c.2.1
                              have p6295_2 := h6295c.2.2.1
                              have p6295_3 := h6295c.2.2.2
                              linarith only [h6245, h6248, h6252, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6295_1]
                            · have p6295_0 := h6295c.1
                              have p6295_1 := h6295c.2.1
                              have p6295_2 := h6295c.2.2.1
                              have p6295_3 := h6295c.2.2.2
                              linarith only [h6245, h6248, h6250, h6252, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6295_1]
                            · have p6295_0 := h6295c.1
                              have p6295_1 := h6295c.2.1
                              have p6295_2 := h6295c.2.2.1
                              have p6295_3 := h6295c.2.2.2
                              linarith only [h6110, hlam, p6295_0]
                            · have p6295_0 := h6295c.1
                              have p6295_1 := h6295c.2.1
                              have p6295_2 := h6295c.2.2.1
                              have p6295_3 := h6295c.2.2.2
                              linarith only [h6246, hlam, p6295_0]
                            · have p6295_0 := h6295c.1
                              have p6295_1 := h6295c.2.1
                              have p6295_2 := h6295c.2.2.1
                              have p6295_3 := h6295c.2.2.2
                              linarith only [h6248, hlam, p6295_1]
                            · have p6295_0 := h6295c.1
                              have p6295_1 := h6295c.2.1
                              have p6295_2 := h6295c.2.2.1
                              have p6295_3 := h6295c.2.2.2
                              linarith only [hlam, p6295_0]
                            · have p6295_0 := h6295c.1
                              have p6295_1 := h6295c.2.1
                              have p6295_2 := h6295c.2.2.1
                              have p6295_3 := h6295c.2.2.2
                              linarith only [h6250, hlam, p6295_1]
                            · have p6295_0 := h6295c.1
                              have p6295_1 := h6295c.2.1
                              have p6295_2 := h6295c.2.2.1
                              have p6295_3 := h6295c.2.2.2
                              linarith only [h6111, hlam, p6295_0]
                            · have p6295_0 := h6295c.1
                              have p6295_1 := h6295c.2.1
                              have p6295_2 := h6295c.2.2.1
                              have p6295_3 := h6295c.2.2.2
                              linarith only [h6247, hlam, p6295_0]
                            · have p6295_0 := h6295c.1
                              have p6295_1 := h6295c.2.1
                              have p6295_2 := h6295c.2.2.1
                              have p6295_3 := h6295c.2.2.2
                              linarith only [h6249, hlam, p6295_0]
                            · have p6295_0 := h6295c.1
                              have p6295_1 := h6295c.2.1
                              have p6295_2 := h6295c.2.2.1
                              have p6295_3 := h6295c.2.2.2
                              linarith only [h6111, h6248, h6252, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6295_1]
                            · have p6295_0 := h6295c.1
                              have p6295_1 := h6295c.2.1
                              have p6295_2 := h6295c.2.2.1
                              have p6295_3 := h6295c.2.2.2
                              linarith only [hlam, p6295_0]
                  · linarith only [h5235, h6111, h6249, hlam]
                · linarith only [h5235, h6113, h6248, hlam]
              · linarith only [h0, h6111, h6247, hlam]
            · linarith only [h5235, h6110, h6112, h6245, h6246, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h6325 | h6325
            · rcases m.htr 1 2 5 (by decide) (by decide) with h6326 | h6326
              · rcases m.htr 1 3 4 (by decide) (by decide) with h6327 | h6327
                · rcases m.htr 1 3 5 (by decide) (by decide) with h6328 | h6328
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h6329 | h6329
                    · linarith only [h0, h6110, h6114, h6245, h6329, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h6331 | h6331
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h6332 | h6332
                        · linarith only [h6110, h6114, h6325, h6332, hlam]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h6334 | h6334
                          · linarith only [h6110, h6114, h6325, h6331, h6334, hlam]
                          · rcases h1bigk with h6336c | h6336c | h6336c | h6336c | h6336c | h6336c | h6336c | h6336c | h6336c | h6336c | h6336c | h6336c | h6336c | h6336c | h6336c | h6336c | h6336c | h6336c | h6336c | h6336c | h6336c | h6336c | h6336c | h6336c | h6336c
                            · have p6336_0 := h6336c.1
                              have p6336_1 := h6336c.2.1
                              have p6336_2 := h6336c.2.2.1
                              have p6336_3 := h6336c.2.2.2
                              linarith only [hlam, p6336_0]
                            · have p6336_0 := h6336c.1
                              have p6336_1 := h6336c.2.1
                              have p6336_2 := h6336c.2.2.1
                              have p6336_3 := h6336c.2.2.2
                              linarith only [h0, hlam, p6336_0]
                            · have p6336_0 := h6336c.1
                              have p6336_1 := h6336c.2.1
                              have p6336_2 := h6336c.2.2.1
                              have p6336_3 := h6336c.2.2.2
                              linarith only [h5235, hlam, p6336_0]
                            · have p6336_0 := h6336c.1
                              have p6336_1 := h6336c.2.1
                              have p6336_2 := h6336c.2.2.1
                              have p6336_3 := h6336c.2.2.2
                              linarith only [h0, h6245, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p6336_1]
                            · have p6336_0 := h6336c.1
                              have p6336_1 := h6336c.2.1
                              have p6336_2 := h6336c.2.2.1
                              have p6336_3 := h6336c.2.2.2
                              linarith only [h0, h6245, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p6336_1]
                            · have p6336_0 := h6336c.1
                              have p6336_1 := h6336c.2.1
                              have p6336_2 := h6336c.2.2.1
                              have p6336_3 := h6336c.2.2.2
                              linarith only [h6245, hc01, hc23, hlam, hphi, ht12, p6336_1]
                            · have p6336_0 := h6336c.1
                              have p6336_1 := h6336c.2.1
                              have p6336_2 := h6336c.2.2.1
                              have p6336_3 := h6336c.2.2.2
                              linarith only [hlam, p6336_0]
                            · have p6336_0 := h6336c.1
                              have p6336_1 := h6336c.2.1
                              have p6336_2 := h6336c.2.2.1
                              have p6336_3 := h6336c.2.2.2
                              linarith only [h6245, hlam, p6336_1]
                            · have p6336_0 := h6336c.1
                              have p6336_1 := h6336c.2.1
                              have p6336_2 := h6336c.2.2.1
                              have p6336_3 := h6336c.2.2.2
                              linarith only [h6245, h6325, h6331, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p6336_1]
                            · have p6336_0 := h6336c.1
                              have p6336_1 := h6336c.2.1
                              have p6336_2 := h6336c.2.2.1
                              have p6336_3 := h6336c.2.2.2
                              linarith only [h6245, h6326, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p6336_1]
                            · have p6336_0 := h6336c.1
                              have p6336_1 := h6336c.2.1
                              have p6336_2 := h6336c.2.2.1
                              have p6336_3 := h6336c.2.2.2
                              linarith only [h6110, h6325, h6331, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p6336_1]
                            · have p6336_0 := h6336c.1
                              have p6336_1 := h6336c.2.1
                              have p6336_2 := h6336c.2.2.1
                              have p6336_3 := h6336c.2.2.2
                              linarith only [h0, h6245, hc02, hc23, hlam, hphi, p6336_1]
                            · have p6336_0 := h6336c.1
                              have p6336_1 := h6336c.2.1
                              have p6336_2 := h6336c.2.2.1
                              have p6336_3 := h6336c.2.2.2
                              linarith only [hlam, p6336_0]
                            · have p6336_0 := h6336c.1
                              have p6336_1 := h6336c.2.1
                              have p6336_2 := h6336c.2.2.1
                              have p6336_3 := h6336c.2.2.2
                              rcases p6336_3 (m.d 0 1) (by simp) with h6350 | h6350
                              · linarith only [h5235, h6350, hlam]
                              · linarith only [h6110, h6350, hlam]
                            · have p6336_0 := h6336c.1
                              have p6336_1 := h6336c.2.1
                              have p6336_2 := h6336c.2.2.1
                              have p6336_3 := h6336c.2.2.2
                              rcases p6336_3 (m.d 0 1) (by simp) with h6353 | h6353
                              · linarith only [h5235, h6353, hlam]
                              · linarith only [h6111, h6353, hlam]
                            · have p6336_0 := h6336c.1
                              have p6336_1 := h6336c.2.1
                              have p6336_2 := h6336c.2.2.1
                              have p6336_3 := h6336c.2.2.2
                              linarith only [h6110, hlam, p6336_0]
                            · have p6336_0 := h6336c.1
                              have p6336_1 := h6336c.2.1
                              have p6336_2 := h6336c.2.2.1
                              have p6336_3 := h6336c.2.2.2
                              linarith only [h6325, hlam, p6336_0]
                            · have p6336_0 := h6336c.1
                              have p6336_1 := h6336c.2.1
                              have p6336_2 := h6336c.2.2.1
                              have p6336_3 := h6336c.2.2.2
                              linarith only [h6327, hlam, p6336_1]
                            · have p6336_0 := h6336c.1
                              have p6336_1 := h6336c.2.1
                              have p6336_2 := h6336c.2.2.1
                              have p6336_3 := h6336c.2.2.2
                              linarith only [hlam, p6336_0]
                            · have p6336_0 := h6336c.1
                              have p6336_1 := h6336c.2.1
                              have p6336_2 := h6336c.2.2.1
                              have p6336_3 := h6336c.2.2.2
                              linarith only [h6329, hlam, p6336_1]
                            · have p6336_0 := h6336c.1
                              have p6336_1 := h6336c.2.1
                              have p6336_2 := h6336c.2.2.1
                              have p6336_3 := h6336c.2.2.2
                              linarith only [h6111, hlam, p6336_0]
                            · have p6336_0 := h6336c.1
                              have p6336_1 := h6336c.2.1
                              have p6336_2 := h6336c.2.2.1
                              have p6336_3 := h6336c.2.2.2
                              linarith only [h6326, hlam, p6336_0]
                            · have p6336_0 := h6336c.1
                              have p6336_1 := h6336c.2.1
                              have p6336_2 := h6336c.2.2.1
                              have p6336_3 := h6336c.2.2.2
                              linarith only [h6328, hlam, p6336_0]
                            · have p6336_0 := h6336c.1
                              have p6336_1 := h6336c.2.1
                              have p6336_2 := h6336c.2.2.1
                              have p6336_3 := h6336c.2.2.2
                              linarith only [h6111, h6325, h6331, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p6336_1]
                            · have p6336_0 := h6336c.1
                              have p6336_1 := h6336c.2.1
                              have p6336_2 := h6336c.2.2.1
                              have p6336_3 := h6336c.2.2.2
                              linarith only [hlam, p6336_0]
                      · linarith only [h0, h6245, h6331, hc01, hc34, hlam, hphi, ht12, ht23]
                  · linarith only [h5235, h6111, h6328, hlam]
                · linarith only [h0, h6110, h6113, h6245, h6327, hc03, hc14, hlam, hphi, ht0b, ht45, ht5b]
              · linarith only [h0, h6111, h6326, hlam]
            · linarith only [h0, h6112, h6325, hlam]
      · linarith only [h5235, h6110, h6113, hlam]
    · linarith only [h0, h6110, h6112, hlam]
  · rcases m.htr 0 2 4 (by decide) (by decide) with h6373 | h6373
    · rcases m.htr 0 3 4 (by decide) (by decide) with h6374 | h6374
      · rcases m.htr 0 4 5 (by decide) (by decide) with h6375 | h6375
        · linarith only [h6110, h6111, h6375, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h6377 | h6377
          · rcases m.htr 1 2 4 (by decide) (by decide) with h6378 | h6378
            · rcases m.htr 1 2 5 (by decide) (by decide) with h6379 | h6379
              · rcases m.htr 1 3 4 (by decide) (by decide) with h6380 | h6380
                · rcases m.htr 1 3 5 (by decide) (by decide) with h6381 | h6381
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h6382 | h6382
                    · linarith only [h6110, h6111, h6375, h6377, h6381, h6382, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h6384 | h6384
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h6385 | h6385
                        · linarith only [h6110, h6111, h6378, h6382, h6385, hlam]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h6387 | h6387
                          · linarith only [h6110, h6111, h6378, h6382, h6384, h6387, hlam]
                          · rcases h1bigk with h6389c | h6389c | h6389c | h6389c | h6389c | h6389c | h6389c | h6389c | h6389c | h6389c | h6389c | h6389c | h6389c | h6389c | h6389c | h6389c | h6389c | h6389c | h6389c | h6389c | h6389c | h6389c | h6389c | h6389c | h6389c
                            · have p6389_0 := h6389c.1
                              have p6389_1 := h6389c.2.1
                              have p6389_2 := h6389c.2.2.1
                              have p6389_3 := h6389c.2.2.2
                              linarith only [hlam, p6389_0]
                            · have p6389_0 := h6389c.1
                              have p6389_1 := h6389c.2.1
                              have p6389_2 := h6389c.2.2.1
                              have p6389_3 := h6389c.2.2.2
                              linarith only [h0, hlam, p6389_0]
                            · have p6389_0 := h6389c.1
                              have p6389_1 := h6389c.2.1
                              have p6389_2 := h6389c.2.2.1
                              have p6389_3 := h6389c.2.2.2
                              linarith only [h5235, hlam, p6389_0]
                            · have p6389_0 := h6389c.1
                              have p6389_1 := h6389c.2.1
                              have p6389_2 := h6389c.2.2.1
                              have p6389_3 := h6389c.2.2.2
                              linarith only [h6111, h6382, hc14, hc45, hlam, hphi, p6389_1]
                            · have p6389_0 := h6389c.1
                              have p6389_1 := h6389c.2.1
                              have p6389_2 := h6389c.2.2.1
                              have p6389_3 := h6389c.2.2.2
                              linarith only [h6111, hlam, p6389_0]
                            · have p6389_0 := h6389c.1
                              have p6389_1 := h6389c.2.1
                              have p6389_2 := h6389c.2.2.1
                              have p6389_3 := h6389c.2.2.2
                              linarith only [hc01, hc12, hlam, hphi, p6389_1]
                            · have p6389_0 := h6389c.1
                              have p6389_1 := h6389c.2.1
                              have p6389_2 := h6389c.2.2.1
                              have p6389_3 := h6389c.2.2.2
                              linarith only [hlam, p6389_0]
                            · have p6389_0 := h6389c.1
                              have p6389_1 := h6389c.2.1
                              have p6389_2 := h6389c.2.2.1
                              have p6389_3 := h6389c.2.2.2
                              linarith only [h6110, h6111, h6378, h6381, h6384, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p6389_1]
                            · have p6389_0 := h6389c.1
                              have p6389_1 := h6389c.2.1
                              have p6389_2 := h6389c.2.2.1
                              have p6389_3 := h6389c.2.2.2
                              rcases p6389_3 (m.d 0 1) (by simp) with h6398 | h6398
                              · linarith only [h0, h6398, hlam]
                              · linarith only [h6110, h6398, hlam]
                            · have p6389_0 := h6389c.1
                              have p6389_1 := h6389c.2.1
                              have p6389_2 := h6389c.2.2.1
                              have p6389_3 := h6389c.2.2.2
                              linarith only [h6110, h6111, h6378, h6384, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p6389_1]
                            · have p6389_0 := h6389c.1
                              have p6389_1 := h6389c.2.1
                              have p6389_2 := h6389c.2.2.1
                              have p6389_3 := h6389c.2.2.2
                              linarith only [h6110, h6378, h6384, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p6389_1]
                            · have p6389_0 := h6389c.1
                              have p6389_1 := h6389c.2.1
                              have p6389_2 := h6389c.2.2.1
                              have p6389_3 := h6389c.2.2.2
                              linarith only [h6377, hlam, p6389_0]
                            · have p6389_0 := h6389c.1
                              have p6389_1 := h6389c.2.1
                              have p6389_2 := h6389c.2.2.1
                              have p6389_3 := h6389c.2.2.2
                              linarith only [hlam, p6389_0]
                            · have p6389_0 := h6389c.1
                              have p6389_1 := h6389c.2.1
                              have p6389_2 := h6389c.2.2.1
                              have p6389_3 := h6389c.2.2.2
                              rcases p6389_3 (m.d 0 1) (by simp) with h6405 | h6405
                              · linarith only [h5235, h6405, hlam]
                              · linarith only [h6110, h6405, hlam]
                            · have p6389_0 := h6389c.1
                              have p6389_1 := h6389c.2.1
                              have p6389_2 := h6389c.2.2.1
                              have p6389_3 := h6389c.2.2.2
                              linarith only [h6110, h6111, h6377, h6378, h6384, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p6389_1]
                            · have p6389_0 := h6389c.1
                              have p6389_1 := h6389c.2.1
                              have p6389_2 := h6389c.2.2.1
                              have p6389_3 := h6389c.2.2.2
                              linarith only [h6110, hlam, p6389_0]
                            · have p6389_0 := h6389c.1
                              have p6389_1 := h6389c.2.1
                              have p6389_2 := h6389c.2.2.1
                              have p6389_3 := h6389c.2.2.2
                              linarith only [h6378, hlam, p6389_0]
                            · have p6389_0 := h6389c.1
                              have p6389_1 := h6389c.2.1
                              have p6389_2 := h6389c.2.2.1
                              have p6389_3 := h6389c.2.2.2
                              linarith only [h6380, hlam, p6389_1]
                            · have p6389_0 := h6389c.1
                              have p6389_1 := h6389c.2.1
                              have p6389_2 := h6389c.2.2.1
                              have p6389_3 := h6389c.2.2.2
                              linarith only [hlam, p6389_0]
                            · have p6389_0 := h6389c.1
                              have p6389_1 := h6389c.2.1
                              have p6389_2 := h6389c.2.2.1
                              have p6389_3 := h6389c.2.2.2
                              linarith only [h6382, hlam, p6389_1]
                            · have p6389_0 := h6389c.1
                              have p6389_1 := h6389c.2.1
                              have p6389_2 := h6389c.2.2.1
                              have p6389_3 := h6389c.2.2.2
                              linarith only [h6110, h6378, h6384, hc15, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p6389_1]
                            · have p6389_0 := h6389c.1
                              have p6389_1 := h6389c.2.1
                              have p6389_2 := h6389c.2.2.1
                              have p6389_3 := h6389c.2.2.2
                              linarith only [h6379, hlam, p6389_0]
                            · have p6389_0 := h6389c.1
                              have p6389_1 := h6389c.2.1
                              have p6389_2 := h6389c.2.2.1
                              have p6389_3 := h6389c.2.2.2
                              linarith only [h6381, hlam, p6389_0]
                            · have p6389_0 := h6389c.1
                              have p6389_1 := h6389c.2.1
                              have p6389_2 := h6389c.2.2.1
                              have p6389_3 := h6389c.2.2.2
                              linarith only [h6378, h6382, h6384, hc34, hc45, hlam, hphi, p6389_1]
                            · have p6389_0 := h6389c.1
                              have p6389_1 := h6389c.2.1
                              have p6389_2 := h6389c.2.2.1
                              have p6389_3 := h6389c.2.2.2
                              linarith only [hlam, p6389_0]
                      · linarith only [h6110, h6111, h6380, h6382, h6384, hc23, hc45, hlam, hphi, ht34]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h6420 | h6420
                    · linarith only [h5235, h6110, h6381, h6420, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h6422 | h6422
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h6423 | h6423
                        · linarith only [h5235, h6110, h6378, h6381, h6420, h6423, hlam]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h6425 | h6425
                          · linarith only [h5235, h6110, h6378, h6381, h6420, h6422, h6425, hlam]
                          · linarith only [h5235, h6110, h6381, h6425, hc14, hc45, hlam, hphi]
                      · linarith only [h5235, h6374, h6381, h6422, hc23, hc35, hlam, hphi]
                · linarith only [h5235, h6110, h6374, h6380, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h6430 | h6430
                · rcases m.htr 1 3 5 (by decide) (by decide) with h6431 | h6431
                  · linarith only [h6377, h6379, h6431, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h6433 | h6433
                    · linarith only [h5235, h6110, h6431, h6433, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h6435 | h6435
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h6436 | h6436
                        · linarith only [h5235, h6110, h6377, h6378, h6379, h6433, h6436, hlam]
                        · linarith only [h5235, h6110, h6377, h6379, h6436, hc14, hc45, hlam, hphi]
                      · linarith only [h5235, h6110, h6377, h6379, h6430, h6435, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                · linarith only [h5235, h6374, h6430, hlam]
            · linarith only [h5235, h6110, h6373, h6377, h6378, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h6442 | h6442
            · rcases m.htr 1 2 5 (by decide) (by decide) with h6443 | h6443
              · rcases m.htr 1 3 4 (by decide) (by decide) with h6444 | h6444
                · rcases m.htr 1 3 5 (by decide) (by decide) with h6445 | h6445
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h6446 | h6446
                    · linarith only [h6110, h6111, h6375, h6443, h6446, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h6448 | h6448
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h6449 | h6449
                        · linarith only [h6110, h6111, h6442, h6446, h6449, hlam]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h6451 | h6451
                          · linarith only [h6110, h6111, h6442, h6446, h6448, h6451, hlam]
                          · rcases h1bigk with h6453c | h6453c | h6453c | h6453c | h6453c | h6453c | h6453c | h6453c | h6453c | h6453c | h6453c | h6453c | h6453c | h6453c | h6453c | h6453c | h6453c | h6453c | h6453c | h6453c | h6453c | h6453c | h6453c | h6453c | h6453c
                            · have p6453_0 := h6453c.1
                              have p6453_1 := h6453c.2.1
                              have p6453_2 := h6453c.2.2.1
                              have p6453_3 := h6453c.2.2.2
                              linarith only [hlam, p6453_0]
                            · have p6453_0 := h6453c.1
                              have p6453_1 := h6453c.2.1
                              have p6453_2 := h6453c.2.2.1
                              have p6453_3 := h6453c.2.2.2
                              linarith only [h0, hlam, p6453_0]
                            · have p6453_0 := h6453c.1
                              have p6453_1 := h6453c.2.1
                              have p6453_2 := h6453c.2.2.1
                              have p6453_3 := h6453c.2.2.2
                              linarith only [h5235, hlam, p6453_0]
                            · have p6453_0 := h6453c.1
                              have p6453_1 := h6453c.2.1
                              have p6453_2 := h6453c.2.2.1
                              have p6453_3 := h6453c.2.2.2
                              linarith only [h6111, h6377, h6443, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p6453_1]
                            · have p6453_0 := h6453c.1
                              have p6453_1 := h6453c.2.1
                              have p6453_2 := h6453c.2.2.1
                              have p6453_3 := h6453c.2.2.2
                              linarith only [h6111, hlam, p6453_0]
                            · have p6453_0 := h6453c.1
                              have p6453_1 := h6453c.2.1
                              have p6453_2 := h6453c.2.2.1
                              have p6453_3 := h6453c.2.2.2
                              linarith only [h6377, hc01, hc23, hlam, hphi, ht12, p6453_1]
                            · have p6453_0 := h6453c.1
                              have p6453_1 := h6453c.2.1
                              have p6453_2 := h6453c.2.2.1
                              have p6453_3 := h6453c.2.2.2
                              linarith only [hlam, p6453_0]
                            · have p6453_0 := h6453c.1
                              have p6453_1 := h6453c.2.1
                              have p6453_2 := h6453c.2.2.1
                              have p6453_3 := h6453c.2.2.2
                              linarith only [h6377, hlam, p6453_1]
                            · have p6453_0 := h6453c.1
                              have p6453_1 := h6453c.2.1
                              have p6453_2 := h6453c.2.2.1
                              have p6453_3 := h6453c.2.2.2
                              linarith only [h6377, h6442, h6448, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p6453_1]
                            · have p6453_0 := h6453c.1
                              have p6453_1 := h6453c.2.1
                              have p6453_2 := h6453c.2.2.1
                              have p6453_3 := h6453c.2.2.2
                              linarith only [h6377, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p6453_1]
                            · have p6453_0 := h6453c.1
                              have p6453_1 := h6453c.2.1
                              have p6453_2 := h6453c.2.2.1
                              have p6453_3 := h6453c.2.2.2
                              linarith only [h6110, h6442, h6448, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p6453_1]
                            · have p6453_0 := h6453c.1
                              have p6453_1 := h6453c.2.1
                              have p6453_2 := h6453c.2.2.1
                              have p6453_3 := h6453c.2.2.2
                              linarith only [h0, h6377, hc02, hc23, hlam, hphi, p6453_1]
                            · have p6453_0 := h6453c.1
                              have p6453_1 := h6453c.2.1
                              have p6453_2 := h6453c.2.2.1
                              have p6453_3 := h6453c.2.2.2
                              linarith only [hlam, p6453_0]
                            · have p6453_0 := h6453c.1
                              have p6453_1 := h6453c.2.1
                              have p6453_2 := h6453c.2.2.1
                              have p6453_3 := h6453c.2.2.2
                              rcases p6453_3 (m.d 0 1) (by simp) with h6467 | h6467
                              · linarith only [h5235, h6467, hlam]
                              · linarith only [h6110, h6467, hlam]
                            · have p6453_0 := h6453c.1
                              have p6453_1 := h6453c.2.1
                              have p6453_2 := h6453c.2.2.1
                              have p6453_3 := h6453c.2.2.2
                              linarith only [h6110, h6111, h6377, h6442, h6448, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p6453_1]
                            · have p6453_0 := h6453c.1
                              have p6453_1 := h6453c.2.1
                              have p6453_2 := h6453c.2.2.1
                              have p6453_3 := h6453c.2.2.2
                              linarith only [h6110, hlam, p6453_0]
                            · have p6453_0 := h6453c.1
                              have p6453_1 := h6453c.2.1
                              have p6453_2 := h6453c.2.2.1
                              have p6453_3 := h6453c.2.2.2
                              linarith only [h6442, hlam, p6453_0]
                            · have p6453_0 := h6453c.1
                              have p6453_1 := h6453c.2.1
                              have p6453_2 := h6453c.2.2.1
                              have p6453_3 := h6453c.2.2.2
                              linarith only [h6444, hlam, p6453_1]
                            · have p6453_0 := h6453c.1
                              have p6453_1 := h6453c.2.1
                              have p6453_2 := h6453c.2.2.1
                              have p6453_3 := h6453c.2.2.2
                              linarith only [hlam, p6453_0]
                            · have p6453_0 := h6453c.1
                              have p6453_1 := h6453c.2.1
                              have p6453_2 := h6453c.2.2.1
                              have p6453_3 := h6453c.2.2.2
                              linarith only [h6446, hlam, p6453_1]
                            · have p6453_0 := h6453c.1
                              have p6453_1 := h6453c.2.1
                              have p6453_2 := h6453c.2.2.1
                              have p6453_3 := h6453c.2.2.2
                              linarith only [h6110, h6442, h6443, h6448, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p6453_1]
                            · have p6453_0 := h6453c.1
                              have p6453_1 := h6453c.2.1
                              have p6453_2 := h6453c.2.2.1
                              have p6453_3 := h6453c.2.2.2
                              linarith only [h6443, hlam, p6453_0]
                            · have p6453_0 := h6453c.1
                              have p6453_1 := h6453c.2.1
                              have p6453_2 := h6453c.2.2.1
                              have p6453_3 := h6453c.2.2.2
                              linarith only [h6445, hlam, p6453_0]
                            · have p6453_0 := h6453c.1
                              have p6453_1 := h6453c.2.1
                              have p6453_2 := h6453c.2.2.1
                              have p6453_3 := h6453c.2.2.2
                              linarith only [h6377, h6442, h6443, h6448, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p6453_1]
                            · have p6453_0 := h6453c.1
                              have p6453_1 := h6453c.2.1
                              have p6453_2 := h6453c.2.2.1
                              have p6453_3 := h6453c.2.2.2
                              linarith only [hlam, p6453_0]
                      · linarith only [h0, h6110, h6377, h6442, h6448, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                  · linarith only [h6377, h6443, h6445, hlam]
                · linarith only [h6110, h6111, h6374, h6377, h6443, h6444, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h6484 | h6484
                · rcases m.htr 1 3 5 (by decide) (by decide) with h6485 | h6485
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h6486 | h6486
                    · linarith only [h0, h6110, h6443, h6486, hc25, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h6488 | h6488
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h6489 | h6489
                        · linarith only [h0, h6110, h6442, h6443, h6486, h6489, hlam]
                        · linarith only [h0, h6110, h6443, h6489, hc14, hc45, hlam, hphi]
                      · linarith only [h0, h6110, h6377, h6442, h6488, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h6493 | h6493
                    · linarith only [h0, h6110, h6377, h6493, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h6495 | h6495
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h6496 | h6496
                        · linarith only [h0, h5235, h6110, h6377, h6442, h6485, h6493, h6496, hc03, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                        · linarith only [h0, h6110, h6443, h6496, hc14, hc45, hlam, hphi]
                      · linarith only [h0, h6110, h6377, h6442, h6495, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                · linarith only [h0, h6110, h6374, h6377, h6484, hlam]
            · linarith only [h0, h6110, h6373, h6442, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b]
      · linarith only [h5235, h6110, h6374, hlam]
    · linarith only [h0, h6110, h6373, hlam]

end R2N4
