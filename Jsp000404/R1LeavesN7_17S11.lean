import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6230000 in
set_option maxHeartbeats 6230000 in
theorem r1l7_20_12_14_H_I_L_I_L_I_s9_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6421 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg7464 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h8188 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
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
  rcases m.htr 0 2 3 (by decide) (by decide) with h8189 | h8189
  · rcases m.htr 0 2 4 (by decide) (by decide) with h8190 | h8190
    · rcases m.htr 0 2 5 (by decide) (by decide) with h8191 | h8191
      · rcases m.htr 0 3 4 (by decide) (by decide) with h8192 | h8192
        · rcases m.htr 0 3 5 (by decide) (by decide) with h8193 | h8193
          · rcases m.htr 0 4 5 (by decide) (by decide) with h8194 | h8194
            · rcases m.htr 1 2 3 (by decide) (by decide) with h8195 | h8195
              · rcases m.htr 1 2 4 (by decide) (by decide) with h8196 | h8196
                · rcases m.htr 1 2 5 (by decide) (by decide) with h8197 | h8197
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h8198 | h8198
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h8199 | h8199
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h8200 | h8200
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h8201 | h8201
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h8202 | h8202
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h8203 | h8203
                              · rcases h0bigk with h8204c | h8204c | h8204c | h8204c | h8204c | h8204c | h8204c | h8204c | h8204c | h8204c | h8204c | h8204c | h8204c | h8204c | h8204c | h8204c | h8204c | h8204c | h8204c | h8204c | h8204c | h8204c | h8204c | h8204c | h8204c
                                · have p8204_0 := h8204c.1
                                  have p8204_1 := h8204c.2.1
                                  have p8204_2 := h8204c.2.2.1
                                  have p8204_3 := h8204c.2.2.2
                                  linarith only [hlam, p8204_0]
                                · have p8204_0 := h8204c.1
                                  have p8204_1 := h8204c.2.1
                                  have p8204_2 := h8204c.2.2.1
                                  have p8204_3 := h8204c.2.2.2
                                  linarith only [h0, hlam, p8204_1]
                                · have p8204_0 := h8204c.1
                                  have p8204_1 := h8204c.2.1
                                  have p8204_2 := h8204c.2.2.1
                                  have p8204_3 := h8204c.2.2.2
                                  linarith only [h6421, hlam, p8204_0]
                                · have p8204_0 := h8204c.1
                                  have p8204_1 := h8204c.2.1
                                  have p8204_2 := h8204c.2.2.1
                                  have p8204_3 := h8204c.2.2.2
                                  linarith only [h7464, hlam, p8204_1]
                                · have p8204_0 := h8204c.1
                                  have p8204_1 := h8204c.2.1
                                  have p8204_2 := h8204c.2.2.1
                                  have p8204_3 := h8204c.2.2.2
                                  linarith only [h7464, h8198, hc05, hc13, hlam, hphi, ht01, ht0b, ht5b, p8204_1]
                                · have p8204_0 := h8204c.1
                                  have p8204_1 := h8204c.2.1
                                  have p8204_2 := h8204c.2.2.1
                                  have p8204_3 := h8204c.2.2.2
                                  linarith only [h0, hc01, hc12, hlam, hphi, p8204_1]
                                · have p8204_0 := h8204c.1
                                  have p8204_1 := h8204c.2.1
                                  have p8204_2 := h8204c.2.2.1
                                  have p8204_3 := h8204c.2.2.2
                                  linarith only [hlam, p8204_0]
                                · have p8204_0 := h8204c.1
                                  have p8204_1 := h8204c.2.1
                                  have p8204_2 := h8204c.2.2.1
                                  have p8204_3 := h8204c.2.2.2
                                  linarith only [h0, h8189, h8200, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p8204_1]
                                · have p8204_0 := h8204c.1
                                  have p8204_1 := h8204c.2.1
                                  have p8204_2 := h8204c.2.2.1
                                  have p8204_3 := h8204c.2.2.2
                                  linarith only [h0, h7464, h8188, h8197, h8201, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p8204_1]
                                · have p8204_0 := h8204c.1
                                  have p8204_1 := h8204c.2.1
                                  have p8204_2 := h8204c.2.2.1
                                  have p8204_3 := h8204c.2.2.2
                                  rcases p8204_3 (m.d 0 1) (by simp) with h8214 | h8214
                                  · linarith only [h0, h8214, hlam]
                                  · linarith only [h8188, h8214, hlam]
                                · have p8204_0 := h8204c.1
                                  have p8204_1 := h8204c.2.1
                                  have p8204_2 := h8204c.2.2.1
                                  have p8204_3 := h8204c.2.2.2
                                  linarith only [h8188, h8197, h8201, h8203, hc03, hc45, hlam, hphi, ht0b, ht5b, p8204_1]
                                · have p8204_0 := h8204c.1
                                  have p8204_1 := h8204c.2.1
                                  have p8204_2 := h8204c.2.2.1
                                  have p8204_3 := h8204c.2.2.2
                                  linarith only [h8189, hlam, p8204_1]
                                · have p8204_0 := h8204c.1
                                  have p8204_1 := h8204c.2.1
                                  have p8204_2 := h8204c.2.2.1
                                  have p8204_3 := h8204c.2.2.2
                                  linarith only [hlam, p8204_0]
                                · have p8204_0 := h8204c.1
                                  have p8204_1 := h8204c.2.1
                                  have p8204_2 := h8204c.2.2.1
                                  have p8204_3 := h8204c.2.2.2
                                  linarith only [h6421, h7464, h8188, h8195, h8197, h8201, h8203, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p8204_1]
                                · have p8204_0 := h8204c.1
                                  have p8204_1 := h8204c.2.1
                                  have p8204_2 := h8204c.2.2.1
                                  have p8204_3 := h8204c.2.2.2
                                  rcases p8204_3 (m.d 0 1) (by simp) with h8221 | h8221
                                  · linarith only [h6421, h8221, hlam]
                                  · linarith only [h8188, h8221, hlam]
                                · have p8204_0 := h8204c.1
                                  have p8204_1 := h8204c.2.1
                                  have p8204_2 := h8204c.2.2.1
                                  have p8204_3 := h8204c.2.2.2
                                  linarith only [h8188, h8197, h8201, h8203, hc04, hc45, hlam, hphi, ht0b, ht5b, p8204_1]
                                · have p8204_0 := h8204c.1
                                  have p8204_1 := h8204c.2.1
                                  have p8204_2 := h8204c.2.2.1
                                  have p8204_3 := h8204c.2.2.2
                                  linarith only [h8190, hlam, p8204_0]
                                · have p8204_0 := h8204c.1
                                  have p8204_1 := h8204c.2.1
                                  have p8204_2 := h8204c.2.2.1
                                  have p8204_3 := h8204c.2.2.2
                                  linarith only [h8192, hlam, p8204_0]
                                · have p8204_0 := h8204c.1
                                  have p8204_1 := h8204c.2.1
                                  have p8204_2 := h8204c.2.2.1
                                  have p8204_3 := h8204c.2.2.2
                                  linarith only [hlam, p8204_0]
                                · have p8204_0 := h8204c.1
                                  have p8204_1 := h8204c.2.1
                                  have p8204_2 := h8204c.2.2.1
                                  have p8204_3 := h8204c.2.2.2
                                  rcases p8204_3 (m.d 0 1) (by simp) with h8228 | h8228
                                  · linarith only [h7464, h8228, hlam]
                                  · linarith only [h8188, h8228, hlam]
                                · have p8204_0 := h8204c.1
                                  have p8204_1 := h8204c.2.1
                                  have p8204_2 := h8204c.2.2.1
                                  have p8204_3 := h8204c.2.2.2
                                  linarith only [h8188, hlam, p8204_0]
                                · have p8204_0 := h8204c.1
                                  have p8204_1 := h8204c.2.1
                                  have p8204_2 := h8204c.2.2.1
                                  have p8204_3 := h8204c.2.2.2
                                  linarith only [h8191, hlam, p8204_1]
                                · have p8204_0 := h8204c.1
                                  have p8204_1 := h8204c.2.1
                                  have p8204_2 := h8204c.2.2.1
                                  have p8204_3 := h8204c.2.2.2
                                  linarith only [h8193, hlam, p8204_0]
                                · have p8204_0 := h8204c.1
                                  have p8204_1 := h8204c.2.1
                                  have p8204_2 := h8204c.2.2.1
                                  have p8204_3 := h8204c.2.2.2
                                  linarith only [h8194, hlam, p8204_1]
                                · have p8204_0 := h8204c.1
                                  have p8204_1 := h8204c.2.1
                                  have p8204_2 := h8204c.2.2.1
                                  have p8204_3 := h8204c.2.2.2
                                  linarith only [hlam, p8204_0]
                              · rcases h0bigk with h8236c | h8236c | h8236c | h8236c | h8236c | h8236c | h8236c | h8236c | h8236c | h8236c | h8236c | h8236c | h8236c | h8236c | h8236c | h8236c | h8236c | h8236c | h8236c | h8236c | h8236c | h8236c | h8236c | h8236c | h8236c
                                · have p8236_0 := h8236c.1
                                  have p8236_1 := h8236c.2.1
                                  have p8236_2 := h8236c.2.2.1
                                  have p8236_3 := h8236c.2.2.2
                                  linarith only [hlam, p8236_0]
                                · have p8236_0 := h8236c.1
                                  have p8236_1 := h8236c.2.1
                                  have p8236_2 := h8236c.2.2.1
                                  have p8236_3 := h8236c.2.2.2
                                  linarith only [h0, hlam, p8236_1]
                                · have p8236_0 := h8236c.1
                                  have p8236_1 := h8236c.2.1
                                  have p8236_2 := h8236c.2.2.1
                                  have p8236_3 := h8236c.2.2.2
                                  linarith only [h6421, hlam, p8236_0]
                                · have p8236_0 := h8236c.1
                                  have p8236_1 := h8236c.2.1
                                  have p8236_2 := h8236c.2.2.1
                                  have p8236_3 := h8236c.2.2.2
                                  linarith only [h7464, hlam, p8236_1]
                                · have p8236_0 := h8236c.1
                                  have p8236_1 := h8236c.2.1
                                  have p8236_2 := h8236c.2.2.1
                                  have p8236_3 := h8236c.2.2.2
                                  linarith only [h8188, h8197, h8202, h8203, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p8236_1]
                                · have p8236_0 := h8236c.1
                                  have p8236_1 := h8236c.2.1
                                  have p8236_2 := h8236c.2.2.1
                                  have p8236_3 := h8236c.2.2.2
                                  linarith only [h0, hc01, hc12, hlam, hphi, p8236_1]
                                · have p8236_0 := h8236c.1
                                  have p8236_1 := h8236c.2.1
                                  have p8236_2 := h8236c.2.2.1
                                  have p8236_3 := h8236c.2.2.2
                                  linarith only [hlam, p8236_0]
                                · have p8236_0 := h8236c.1
                                  have p8236_1 := h8236c.2.1
                                  have p8236_2 := h8236c.2.2.1
                                  have p8236_3 := h8236c.2.2.2
                                  linarith only [h0, h6421, h8188, h8197, h8202, h8203, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p8236_1]
                                · have p8236_0 := h8236c.1
                                  have p8236_1 := h8236c.2.1
                                  have p8236_2 := h8236c.2.2.1
                                  have p8236_3 := h8236c.2.2.2
                                  linarith only [h0, h7464, h8188, h8197, h8202, h8203, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p8236_1]
                                · have p8236_0 := h8236c.1
                                  have p8236_1 := h8236c.2.1
                                  have p8236_2 := h8236c.2.2.1
                                  have p8236_3 := h8236c.2.2.2
                                  linarith only [h0, h8188, h8197, h8202, h8203, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p8236_1]
                                · have p8236_0 := h8236c.1
                                  have p8236_1 := h8236c.2.1
                                  have p8236_2 := h8236c.2.2.1
                                  have p8236_3 := h8236c.2.2.2
                                  linarith only [h8188, h8197, h8202, h8203, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p8236_1]
                                · have p8236_0 := h8236c.1
                                  have p8236_1 := h8236c.2.1
                                  have p8236_2 := h8236c.2.2.1
                                  have p8236_3 := h8236c.2.2.2
                                  linarith only [h8189, hlam, p8236_1]
                                · have p8236_0 := h8236c.1
                                  have p8236_1 := h8236c.2.1
                                  have p8236_2 := h8236c.2.2.1
                                  have p8236_3 := h8236c.2.2.2
                                  linarith only [hlam, p8236_0]
                                · have p8236_0 := h8236c.1
                                  have p8236_1 := h8236c.2.1
                                  have p8236_2 := h8236c.2.2.1
                                  have p8236_3 := h8236c.2.2.2
                                  linarith only [h6421, h7464, h8188, h8195, h8197, h8202, h8203, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p8236_1]
                                · have p8236_0 := h8236c.1
                                  have p8236_1 := h8236c.2.1
                                  have p8236_2 := h8236c.2.2.1
                                  have p8236_3 := h8236c.2.2.2
                                  linarith only [h6421, h8188, h8195, h8197, h8202, h8203, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p8236_1]
                                · have p8236_0 := h8236c.1
                                  have p8236_1 := h8236c.2.1
                                  have p8236_2 := h8236c.2.2.1
                                  have p8236_3 := h8236c.2.2.2
                                  linarith only [h8188, h8197, h8202, h8203, hc04, hc34, hlam, hphi, ht0b, ht45, ht5b, p8236_1]
                                · have p8236_0 := h8236c.1
                                  have p8236_1 := h8236c.2.1
                                  have p8236_2 := h8236c.2.2.1
                                  have p8236_3 := h8236c.2.2.2
                                  linarith only [h8190, hlam, p8236_0]
                                · have p8236_0 := h8236c.1
                                  have p8236_1 := h8236c.2.1
                                  have p8236_2 := h8236c.2.2.1
                                  have p8236_3 := h8236c.2.2.2
                                  linarith only [h8192, hlam, p8236_0]
                                · have p8236_0 := h8236c.1
                                  have p8236_1 := h8236c.2.1
                                  have p8236_2 := h8236c.2.2.1
                                  have p8236_3 := h8236c.2.2.2
                                  linarith only [hlam, p8236_0]
                                · have p8236_0 := h8236c.1
                                  have p8236_1 := h8236c.2.1
                                  have p8236_2 := h8236c.2.2.1
                                  have p8236_3 := h8236c.2.2.2
                                  linarith only [h7464, h8188, h8195, h8197, h8198, h8202, h8203, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p8236_1]
                                · have p8236_0 := h8236c.1
                                  have p8236_1 := h8236c.2.1
                                  have p8236_2 := h8236c.2.2.1
                                  have p8236_3 := h8236c.2.2.2
                                  linarith only [h8188, hlam, p8236_0]
                                · have p8236_0 := h8236c.1
                                  have p8236_1 := h8236c.2.1
                                  have p8236_2 := h8236c.2.2.1
                                  have p8236_3 := h8236c.2.2.2
                                  linarith only [h8191, hlam, p8236_1]
                                · have p8236_0 := h8236c.1
                                  have p8236_1 := h8236c.2.1
                                  have p8236_2 := h8236c.2.2.1
                                  have p8236_3 := h8236c.2.2.2
                                  linarith only [h8193, hlam, p8236_0]
                                · have p8236_0 := h8236c.1
                                  have p8236_1 := h8236c.2.1
                                  have p8236_2 := h8236c.2.2.1
                                  have p8236_3 := h8236c.2.2.2
                                  linarith only [h8194, hlam, p8236_1]
                                · have p8236_0 := h8236c.1
                                  have p8236_1 := h8236c.2.1
                                  have p8236_2 := h8236c.2.2.1
                                  have p8236_3 := h8236c.2.2.2
                                  linarith only [hlam, p8236_0]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h8262 | h8262
                              · linarith only [h8200, h8202, h8262, hlam]
                              · rcases h0bigk with h8264c | h8264c | h8264c | h8264c | h8264c | h8264c | h8264c | h8264c | h8264c | h8264c | h8264c | h8264c | h8264c | h8264c | h8264c | h8264c | h8264c | h8264c | h8264c | h8264c | h8264c | h8264c | h8264c | h8264c | h8264c
                                · have p8264_0 := h8264c.1
                                  have p8264_1 := h8264c.2.1
                                  have p8264_2 := h8264c.2.2.1
                                  have p8264_3 := h8264c.2.2.2
                                  linarith only [hlam, p8264_0]
                                · have p8264_0 := h8264c.1
                                  have p8264_1 := h8264c.2.1
                                  have p8264_2 := h8264c.2.2.1
                                  have p8264_3 := h8264c.2.2.2
                                  linarith only [h0, hlam, p8264_1]
                                · have p8264_0 := h8264c.1
                                  have p8264_1 := h8264c.2.1
                                  have p8264_2 := h8264c.2.2.1
                                  have p8264_3 := h8264c.2.2.2
                                  linarith only [h6421, hlam, p8264_0]
                                · have p8264_0 := h8264c.1
                                  have p8264_1 := h8264c.2.1
                                  have p8264_2 := h8264c.2.2.1
                                  have p8264_3 := h8264c.2.2.2
                                  linarith only [h7464, hlam, p8264_1]
                                · have p8264_0 := h8264c.1
                                  have p8264_1 := h8264c.2.1
                                  have p8264_2 := h8264c.2.2.1
                                  have p8264_3 := h8264c.2.2.2
                                  linarith only [h8188, h8199, h8200, h8202, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p8264_1]
                                · have p8264_0 := h8264c.1
                                  have p8264_1 := h8264c.2.1
                                  have p8264_2 := h8264c.2.2.1
                                  have p8264_3 := h8264c.2.2.2
                                  linarith only [h0, hc01, hc12, hlam, hphi, p8264_1]
                                · have p8264_0 := h8264c.1
                                  have p8264_1 := h8264c.2.1
                                  have p8264_2 := h8264c.2.2.1
                                  have p8264_3 := h8264c.2.2.2
                                  linarith only [hlam, p8264_0]
                                · have p8264_0 := h8264c.1
                                  have p8264_1 := h8264c.2.1
                                  have p8264_2 := h8264c.2.2.1
                                  have p8264_3 := h8264c.2.2.2
                                  linarith only [h0, h6421, h8188, h8199, h8200, h8202, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p8264_1]
                                · have p8264_0 := h8264c.1
                                  have p8264_1 := h8264c.2.1
                                  have p8264_2 := h8264c.2.2.1
                                  have p8264_3 := h8264c.2.2.2
                                  linarith only [h0, h7464, h8188, h8199, h8200, h8202, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p8264_1]
                                · have p8264_0 := h8264c.1
                                  have p8264_1 := h8264c.2.1
                                  have p8264_2 := h8264c.2.2.1
                                  have p8264_3 := h8264c.2.2.2
                                  linarith only [h0, h8188, h8199, h8200, h8202, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p8264_1]
                                · have p8264_0 := h8264c.1
                                  have p8264_1 := h8264c.2.1
                                  have p8264_2 := h8264c.2.2.1
                                  have p8264_3 := h8264c.2.2.2
                                  linarith only [h8188, h8199, h8200, h8202, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p8264_1]
                                · have p8264_0 := h8264c.1
                                  have p8264_1 := h8264c.2.1
                                  have p8264_2 := h8264c.2.2.1
                                  have p8264_3 := h8264c.2.2.2
                                  linarith only [h8189, hlam, p8264_1]
                                · have p8264_0 := h8264c.1
                                  have p8264_1 := h8264c.2.1
                                  have p8264_2 := h8264c.2.2.1
                                  have p8264_3 := h8264c.2.2.2
                                  linarith only [hlam, p8264_0]
                                · have p8264_0 := h8264c.1
                                  have p8264_1 := h8264c.2.1
                                  have p8264_2 := h8264c.2.2.1
                                  have p8264_3 := h8264c.2.2.2
                                  linarith only [h0, h7464, h8188, h8189, h8199, h8200, h8202, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p8264_1]
                                · have p8264_0 := h8264c.1
                                  have p8264_1 := h8264c.2.1
                                  have p8264_2 := h8264c.2.2.1
                                  have p8264_3 := h8264c.2.2.2
                                  linarith only [h0, h8188, h8189, h8199, h8200, h8202, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p8264_1]
                                · have p8264_0 := h8264c.1
                                  have p8264_1 := h8264c.2.1
                                  have p8264_2 := h8264c.2.2.1
                                  have p8264_3 := h8264c.2.2.2
                                  linarith only [h8188, h8199, h8200, h8202, hc04, hc34, hlam, hphi, ht0b, ht45, ht5b, p8264_1]
                                · have p8264_0 := h8264c.1
                                  have p8264_1 := h8264c.2.1
                                  have p8264_2 := h8264c.2.2.1
                                  have p8264_3 := h8264c.2.2.2
                                  linarith only [h8190, hlam, p8264_0]
                                · have p8264_0 := h8264c.1
                                  have p8264_1 := h8264c.2.1
                                  have p8264_2 := h8264c.2.2.1
                                  have p8264_3 := h8264c.2.2.2
                                  linarith only [h8192, hlam, p8264_0]
                                · have p8264_0 := h8264c.1
                                  have p8264_1 := h8264c.2.1
                                  have p8264_2 := h8264c.2.2.1
                                  have p8264_3 := h8264c.2.2.2
                                  linarith only [hlam, p8264_0]
                                · have p8264_0 := h8264c.1
                                  have p8264_1 := h8264c.2.1
                                  have p8264_2 := h8264c.2.2.1
                                  have p8264_3 := h8264c.2.2.2
                                  linarith only [h8188, h8199, h8200, h8202, hc04, hc34, hlam, hphi, ht0b, ht45, ht5b, p8264_1]
                                · have p8264_0 := h8264c.1
                                  have p8264_1 := h8264c.2.1
                                  have p8264_2 := h8264c.2.2.1
                                  have p8264_3 := h8264c.2.2.2
                                  linarith only [h8188, hlam, p8264_0]
                                · have p8264_0 := h8264c.1
                                  have p8264_1 := h8264c.2.1
                                  have p8264_2 := h8264c.2.2.1
                                  have p8264_3 := h8264c.2.2.2
                                  linarith only [h8191, hlam, p8264_1]
                                · have p8264_0 := h8264c.1
                                  have p8264_1 := h8264c.2.1
                                  have p8264_2 := h8264c.2.2.1
                                  have p8264_3 := h8264c.2.2.2
                                  linarith only [h8193, hlam, p8264_0]
                                · have p8264_0 := h8264c.1
                                  have p8264_1 := h8264c.2.1
                                  have p8264_2 := h8264c.2.2.1
                                  have p8264_3 := h8264c.2.2.2
                                  linarith only [h8194, hlam, p8264_1]
                                · have p8264_0 := h8264c.1
                                  have p8264_1 := h8264c.2.1
                                  have p8264_2 := h8264c.2.2.1
                                  have p8264_3 := h8264c.2.2.2
                                  linarith only [hlam, p8264_0]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h8290 | h8290
                            · linarith only [h8200, h8201, h8290, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h8292 | h8292
                              · linarith only [h8200, h8201, h8290, h8292, hlam]
                              · linarith only [h7464, h8188, h8195, h8198, h8199, h8200, h8201, h8292, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h8295 | h8295
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h8296 | h8296
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h8297 | h8297
                              · rcases h0bigk with h8298c | h8298c | h8298c | h8298c | h8298c | h8298c | h8298c | h8298c | h8298c | h8298c | h8298c | h8298c | h8298c | h8298c | h8298c | h8298c | h8298c | h8298c | h8298c | h8298c | h8298c | h8298c | h8298c | h8298c | h8298c
                                · have p8298_0 := h8298c.1
                                  have p8298_1 := h8298c.2.1
                                  have p8298_2 := h8298c.2.2.1
                                  have p8298_3 := h8298c.2.2.2
                                  linarith only [hlam, p8298_0]
                                · have p8298_0 := h8298c.1
                                  have p8298_1 := h8298c.2.1
                                  have p8298_2 := h8298c.2.2.1
                                  have p8298_3 := h8298c.2.2.2
                                  linarith only [h0, hlam, p8298_1]
                                · have p8298_0 := h8298c.1
                                  have p8298_1 := h8298c.2.1
                                  have p8298_2 := h8298c.2.2.1
                                  have p8298_3 := h8298c.2.2.2
                                  linarith only [h6421, hlam, p8298_0]
                                · have p8298_0 := h8298c.1
                                  have p8298_1 := h8298c.2.1
                                  have p8298_2 := h8298c.2.2.1
                                  have p8298_3 := h8298c.2.2.2
                                  linarith only [h7464, hlam, p8298_1]
                                · have p8298_0 := h8298c.1
                                  have p8298_1 := h8298c.2.1
                                  have p8298_2 := h8298c.2.2.1
                                  have p8298_3 := h8298c.2.2.2
                                  linarith only [h7464, h8195, h8198, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p8298_1]
                                · have p8298_0 := h8298c.1
                                  have p8298_1 := h8298c.2.1
                                  have p8298_2 := h8298c.2.2.1
                                  have p8298_3 := h8298c.2.2.2
                                  linarith only [h0, hc01, hc12, hlam, hphi, p8298_1]
                                · have p8298_0 := h8298c.1
                                  have p8298_1 := h8298c.2.1
                                  have p8298_2 := h8298c.2.2.1
                                  have p8298_3 := h8298c.2.2.2
                                  linarith only [hlam, p8298_0]
                                · have p8298_0 := h8298c.1
                                  have p8298_1 := h8298c.2.1
                                  have p8298_2 := h8298c.2.2.1
                                  have p8298_3 := h8298c.2.2.2
                                  linarith only [h0, h8192, h8200, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8298_1]
                                · have p8298_0 := h8298c.1
                                  have p8298_1 := h8298c.2.1
                                  have p8298_2 := h8298c.2.2.1
                                  have p8298_3 := h8298c.2.2.2
                                  linarith only [h0, h7464, h8188, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b, p8298_1]
                                · have p8298_0 := h8298c.1
                                  have p8298_1 := h8298c.2.1
                                  have p8298_2 := h8298c.2.2.1
                                  have p8298_3 := h8298c.2.2.2
                                  rcases p8298_3 (m.d 0 1) (by simp) with h8308 | h8308
                                  · linarith only [h0, h8308, hlam]
                                  · linarith only [h8188, h8308, hlam]
                                · have p8298_0 := h8298c.1
                                  have p8298_1 := h8298c.2.1
                                  have p8298_2 := h8298c.2.2.1
                                  have p8298_3 := h8298c.2.2.2
                                  linarith only [h8188, h8197, h8295, h8297, hc03, hc45, hlam, hphi, ht0b, ht5b, p8298_1]
                                · have p8298_0 := h8298c.1
                                  have p8298_1 := h8298c.2.1
                                  have p8298_2 := h8298c.2.2.1
                                  have p8298_3 := h8298c.2.2.2
                                  linarith only [h8189, hlam, p8298_1]
                                · have p8298_0 := h8298c.1
                                  have p8298_1 := h8298c.2.1
                                  have p8298_2 := h8298c.2.2.1
                                  have p8298_3 := h8298c.2.2.2
                                  linarith only [hlam, p8298_0]
                                · have p8298_0 := h8298c.1
                                  have p8298_1 := h8298c.2.1
                                  have p8298_2 := h8298c.2.2.1
                                  have p8298_3 := h8298c.2.2.2
                                  linarith only [h6421, h8192, h8195, h8200, h8295, h8297, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p8298_1]
                                · have p8298_0 := h8298c.1
                                  have p8298_1 := h8298c.2.1
                                  have p8298_2 := h8298c.2.2.1
                                  have p8298_3 := h8298c.2.2.2
                                  rcases p8298_3 (m.d 0 1) (by simp) with h8315 | h8315
                                  · linarith only [h6421, h8315, hlam]
                                  · linarith only [h8188, h8315, hlam]
                                · have p8298_0 := h8298c.1
                                  have p8298_1 := h8298c.2.1
                                  have p8298_2 := h8298c.2.2.1
                                  have p8298_3 := h8298c.2.2.2
                                  linarith only [h8188, h8197, h8295, h8297, hc04, hc45, hlam, hphi, ht0b, ht5b, p8298_1]
                                · have p8298_0 := h8298c.1
                                  have p8298_1 := h8298c.2.1
                                  have p8298_2 := h8298c.2.2.1
                                  have p8298_3 := h8298c.2.2.2
                                  linarith only [h8190, hlam, p8298_0]
                                · have p8298_0 := h8298c.1
                                  have p8298_1 := h8298c.2.1
                                  have p8298_2 := h8298c.2.2.1
                                  have p8298_3 := h8298c.2.2.2
                                  linarith only [h8192, hlam, p8298_0]
                                · have p8298_0 := h8298c.1
                                  have p8298_1 := h8298c.2.1
                                  have p8298_2 := h8298c.2.2.1
                                  have p8298_3 := h8298c.2.2.2
                                  linarith only [hlam, p8298_0]
                                · have p8298_0 := h8298c.1
                                  have p8298_1 := h8298c.2.1
                                  have p8298_2 := h8298c.2.2.1
                                  have p8298_3 := h8298c.2.2.2
                                  rcases p8298_3 (m.d 0 1) (by simp) with h8322 | h8322
                                  · linarith only [h7464, h8322, hlam]
                                  · linarith only [h8188, h8322, hlam]
                                · have p8298_0 := h8298c.1
                                  have p8298_1 := h8298c.2.1
                                  have p8298_2 := h8298c.2.2.1
                                  have p8298_3 := h8298c.2.2.2
                                  linarith only [h8188, hlam, p8298_0]
                                · have p8298_0 := h8298c.1
                                  have p8298_1 := h8298c.2.1
                                  have p8298_2 := h8298c.2.2.1
                                  have p8298_3 := h8298c.2.2.2
                                  linarith only [h8191, hlam, p8298_1]
                                · have p8298_0 := h8298c.1
                                  have p8298_1 := h8298c.2.1
                                  have p8298_2 := h8298c.2.2.1
                                  have p8298_3 := h8298c.2.2.2
                                  linarith only [h8193, hlam, p8298_0]
                                · have p8298_0 := h8298c.1
                                  have p8298_1 := h8298c.2.1
                                  have p8298_2 := h8298c.2.2.1
                                  have p8298_3 := h8298c.2.2.2
                                  linarith only [h8194, hlam, p8298_1]
                                · have p8298_0 := h8298c.1
                                  have p8298_1 := h8298c.2.1
                                  have p8298_2 := h8298c.2.2.1
                                  have p8298_3 := h8298c.2.2.2
                                  linarith only [hlam, p8298_0]
                              · linarith only [h7464, h8194, h8195, h8198, h8200, h8295, h8297, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                            · linarith only [h0, h8188, h8199, h8200, h8295, h8296, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h8332 | h8332
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h8333 | h8333
                              · rcases h0bigk with h8334c | h8334c | h8334c | h8334c | h8334c | h8334c | h8334c | h8334c | h8334c | h8334c | h8334c | h8334c | h8334c | h8334c | h8334c | h8334c | h8334c | h8334c | h8334c | h8334c | h8334c | h8334c | h8334c | h8334c | h8334c
                                · have p8334_0 := h8334c.1
                                  have p8334_1 := h8334c.2.1
                                  have p8334_2 := h8334c.2.2.1
                                  have p8334_3 := h8334c.2.2.2
                                  linarith only [hlam, p8334_0]
                                · have p8334_0 := h8334c.1
                                  have p8334_1 := h8334c.2.1
                                  have p8334_2 := h8334c.2.2.1
                                  have p8334_3 := h8334c.2.2.2
                                  linarith only [h0, hlam, p8334_1]
                                · have p8334_0 := h8334c.1
                                  have p8334_1 := h8334c.2.1
                                  have p8334_2 := h8334c.2.2.1
                                  have p8334_3 := h8334c.2.2.2
                                  linarith only [h6421, hlam, p8334_0]
                                · have p8334_0 := h8334c.1
                                  have p8334_1 := h8334c.2.1
                                  have p8334_2 := h8334c.2.2.1
                                  have p8334_3 := h8334c.2.2.2
                                  linarith only [h7464, hlam, p8334_1]
                                · have p8334_0 := h8334c.1
                                  have p8334_1 := h8334c.2.1
                                  have p8334_2 := h8334c.2.2.1
                                  have p8334_3 := h8334c.2.2.2
                                  linarith only [h7464, h8195, h8198, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p8334_1]
                                · have p8334_0 := h8334c.1
                                  have p8334_1 := h8334c.2.1
                                  have p8334_2 := h8334c.2.2.1
                                  have p8334_3 := h8334c.2.2.2
                                  linarith only [h0, hc01, hc12, hlam, hphi, p8334_1]
                                · have p8334_0 := h8334c.1
                                  have p8334_1 := h8334c.2.1
                                  have p8334_2 := h8334c.2.2.1
                                  have p8334_3 := h8334c.2.2.2
                                  linarith only [hlam, p8334_0]
                                · have p8334_0 := h8334c.1
                                  have p8334_1 := h8334c.2.1
                                  have p8334_2 := h8334c.2.2.1
                                  have p8334_3 := h8334c.2.2.2
                                  linarith only [h0, h8192, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p8334_1]
                                · have p8334_0 := h8334c.1
                                  have p8334_1 := h8334c.2.1
                                  have p8334_2 := h8334c.2.2.1
                                  have p8334_3 := h8334c.2.2.2
                                  linarith only [h0, h7464, h8188, h8193, h8295, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8334_1]
                                · have p8334_0 := h8334c.1
                                  have p8334_1 := h8334c.2.1
                                  have p8334_2 := h8334c.2.2.1
                                  have p8334_3 := h8334c.2.2.2
                                  linarith only [h0, h8193, h8295, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8334_1]
                                · have p8334_0 := h8334c.1
                                  have p8334_1 := h8334c.2.1
                                  have p8334_2 := h8334c.2.2.1
                                  have p8334_3 := h8334c.2.2.2
                                  linarith only [h8188, h8193, h8295, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p8334_1]
                                · have p8334_0 := h8334c.1
                                  have p8334_1 := h8334c.2.1
                                  have p8334_2 := h8334c.2.2.1
                                  have p8334_3 := h8334c.2.2.2
                                  linarith only [h8189, hlam, p8334_1]
                                · have p8334_0 := h8334c.1
                                  have p8334_1 := h8334c.2.1
                                  have p8334_2 := h8334c.2.2.1
                                  have p8334_3 := h8334c.2.2.2
                                  linarith only [hlam, p8334_0]
                                · have p8334_0 := h8334c.1
                                  have p8334_1 := h8334c.2.1
                                  have p8334_2 := h8334c.2.2.1
                                  have p8334_3 := h8334c.2.2.2
                                  linarith only [h6421, h7464, h8188, h8193, h8195, h8295, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8334_1]
                                · have p8334_0 := h8334c.1
                                  have p8334_1 := h8334c.2.1
                                  have p8334_2 := h8334c.2.2.1
                                  have p8334_3 := h8334c.2.2.2
                                  linarith only [h6421, h8193, h8195, h8295, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8334_1]
                                · have p8334_0 := h8334c.1
                                  have p8334_1 := h8334c.2.1
                                  have p8334_2 := h8334c.2.2.1
                                  have p8334_3 := h8334c.2.2.2
                                  linarith only [h8188, h8193, h8295, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p8334_1]
                                · have p8334_0 := h8334c.1
                                  have p8334_1 := h8334c.2.1
                                  have p8334_2 := h8334c.2.2.1
                                  have p8334_3 := h8334c.2.2.2
                                  linarith only [h8190, hlam, p8334_0]
                                · have p8334_0 := h8334c.1
                                  have p8334_1 := h8334c.2.1
                                  have p8334_2 := h8334c.2.2.1
                                  have p8334_3 := h8334c.2.2.2
                                  linarith only [h8192, hlam, p8334_0]
                                · have p8334_0 := h8334c.1
                                  have p8334_1 := h8334c.2.1
                                  have p8334_2 := h8334c.2.2.1
                                  have p8334_3 := h8334c.2.2.2
                                  linarith only [hlam, p8334_0]
                                · have p8334_0 := h8334c.1
                                  have p8334_1 := h8334c.2.1
                                  have p8334_2 := h8334c.2.2.1
                                  have p8334_3 := h8334c.2.2.2
                                  linarith only [h7464, h8193, h8195, h8198, h8295, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8334_1]
                                · have p8334_0 := h8334c.1
                                  have p8334_1 := h8334c.2.1
                                  have p8334_2 := h8334c.2.2.1
                                  have p8334_3 := h8334c.2.2.2
                                  linarith only [h8188, hlam, p8334_0]
                                · have p8334_0 := h8334c.1
                                  have p8334_1 := h8334c.2.1
                                  have p8334_2 := h8334c.2.2.1
                                  have p8334_3 := h8334c.2.2.2
                                  linarith only [h8191, hlam, p8334_1]
                                · have p8334_0 := h8334c.1
                                  have p8334_1 := h8334c.2.1
                                  have p8334_2 := h8334c.2.2.1
                                  have p8334_3 := h8334c.2.2.2
                                  linarith only [h8193, hlam, p8334_0]
                                · have p8334_0 := h8334c.1
                                  have p8334_1 := h8334c.2.1
                                  have p8334_2 := h8334c.2.2.1
                                  have p8334_3 := h8334c.2.2.2
                                  linarith only [h8194, hlam, p8334_1]
                                · have p8334_0 := h8334c.1
                                  have p8334_1 := h8334c.2.1
                                  have p8334_2 := h8334c.2.2.1
                                  have p8334_3 := h8334c.2.2.2
                                  linarith only [hlam, p8334_0]
                              · linarith only [h0, h8190, h8200, h8332, h8333, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h8361 | h8361
                              · rcases h0bigk with h8362c | h8362c | h8362c | h8362c | h8362c | h8362c | h8362c | h8362c | h8362c | h8362c | h8362c | h8362c | h8362c | h8362c | h8362c | h8362c | h8362c | h8362c | h8362c | h8362c | h8362c | h8362c | h8362c | h8362c | h8362c
                                · have p8362_0 := h8362c.1
                                  have p8362_1 := h8362c.2.1
                                  have p8362_2 := h8362c.2.2.1
                                  have p8362_3 := h8362c.2.2.2
                                  linarith only [hlam, p8362_0]
                                · have p8362_0 := h8362c.1
                                  have p8362_1 := h8362c.2.1
                                  have p8362_2 := h8362c.2.2.1
                                  have p8362_3 := h8362c.2.2.2
                                  linarith only [h0, hlam, p8362_1]
                                · have p8362_0 := h8362c.1
                                  have p8362_1 := h8362c.2.1
                                  have p8362_2 := h8362c.2.2.1
                                  have p8362_3 := h8362c.2.2.2
                                  linarith only [h6421, hlam, p8362_0]
                                · have p8362_0 := h8362c.1
                                  have p8362_1 := h8362c.2.1
                                  have p8362_2 := h8362c.2.2.1
                                  have p8362_3 := h8362c.2.2.2
                                  linarith only [h7464, hlam, p8362_1]
                                · have p8362_0 := h8362c.1
                                  have p8362_1 := h8362c.2.1
                                  have p8362_2 := h8362c.2.2.1
                                  have p8362_3 := h8362c.2.2.2
                                  linarith only [h8188, h8199, h8200, h8332, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p8362_1]
                                · have p8362_0 := h8362c.1
                                  have p8362_1 := h8362c.2.1
                                  have p8362_2 := h8362c.2.2.1
                                  have p8362_3 := h8362c.2.2.2
                                  linarith only [h0, hc01, hc12, hlam, hphi, p8362_1]
                                · have p8362_0 := h8362c.1
                                  have p8362_1 := h8362c.2.1
                                  have p8362_2 := h8362c.2.2.1
                                  have p8362_3 := h8362c.2.2.2
                                  linarith only [hlam, p8362_0]
                                · have p8362_0 := h8362c.1
                                  have p8362_1 := h8362c.2.1
                                  have p8362_2 := h8362c.2.2.1
                                  have p8362_3 := h8362c.2.2.2
                                  linarith only [h0, h8192, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p8362_1]
                                · have p8362_0 := h8362c.1
                                  have p8362_1 := h8362c.2.1
                                  have p8362_2 := h8362c.2.2.1
                                  have p8362_3 := h8362c.2.2.2
                                  linarith only [h0, h7464, h8188, h8199, h8200, h8332, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8362_1]
                                · have p8362_0 := h8362c.1
                                  have p8362_1 := h8362c.2.1
                                  have p8362_2 := h8362c.2.2.1
                                  have p8362_3 := h8362c.2.2.2
                                  linarith only [h0, h8188, h8199, h8200, h8332, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8362_1]
                                · have p8362_0 := h8362c.1
                                  have p8362_1 := h8362c.2.1
                                  have p8362_2 := h8362c.2.2.1
                                  have p8362_3 := h8362c.2.2.2
                                  linarith only [h8188, h8199, h8200, h8332, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p8362_1]
                                · have p8362_0 := h8362c.1
                                  have p8362_1 := h8362c.2.1
                                  have p8362_2 := h8362c.2.2.1
                                  have p8362_3 := h8362c.2.2.2
                                  linarith only [h8189, hlam, p8362_1]
                                · have p8362_0 := h8362c.1
                                  have p8362_1 := h8362c.2.1
                                  have p8362_2 := h8362c.2.2.1
                                  have p8362_3 := h8362c.2.2.2
                                  linarith only [hlam, p8362_0]
                                · have p8362_0 := h8362c.1
                                  have p8362_1 := h8362c.2.1
                                  have p8362_2 := h8362c.2.2.1
                                  have p8362_3 := h8362c.2.2.2
                                  linarith only [h6421, h7464, h8188, h8195, h8199, h8200, h8332, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8362_1]
                                · have p8362_0 := h8362c.1
                                  have p8362_1 := h8362c.2.1
                                  have p8362_2 := h8362c.2.2.1
                                  have p8362_3 := h8362c.2.2.2
                                  linarith only [h6421, h8188, h8195, h8199, h8200, h8332, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8362_1]
                                · have p8362_0 := h8362c.1
                                  have p8362_1 := h8362c.2.1
                                  have p8362_2 := h8362c.2.2.1
                                  have p8362_3 := h8362c.2.2.2
                                  linarith only [h8188, h8199, h8200, h8332, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p8362_1]
                                · have p8362_0 := h8362c.1
                                  have p8362_1 := h8362c.2.1
                                  have p8362_2 := h8362c.2.2.1
                                  have p8362_3 := h8362c.2.2.2
                                  linarith only [h8190, hlam, p8362_0]
                                · have p8362_0 := h8362c.1
                                  have p8362_1 := h8362c.2.1
                                  have p8362_2 := h8362c.2.2.1
                                  have p8362_3 := h8362c.2.2.2
                                  linarith only [h8192, hlam, p8362_0]
                                · have p8362_0 := h8362c.1
                                  have p8362_1 := h8362c.2.1
                                  have p8362_2 := h8362c.2.2.1
                                  have p8362_3 := h8362c.2.2.2
                                  linarith only [hlam, p8362_0]
                                · have p8362_0 := h8362c.1
                                  have p8362_1 := h8362c.2.1
                                  have p8362_2 := h8362c.2.2.1
                                  have p8362_3 := h8362c.2.2.2
                                  linarith only [h7464, h8188, h8195, h8198, h8199, h8200, h8332, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8362_1]
                                · have p8362_0 := h8362c.1
                                  have p8362_1 := h8362c.2.1
                                  have p8362_2 := h8362c.2.2.1
                                  have p8362_3 := h8362c.2.2.2
                                  linarith only [h8188, hlam, p8362_0]
                                · have p8362_0 := h8362c.1
                                  have p8362_1 := h8362c.2.1
                                  have p8362_2 := h8362c.2.2.1
                                  have p8362_3 := h8362c.2.2.2
                                  linarith only [h8191, hlam, p8362_1]
                                · have p8362_0 := h8362c.1
                                  have p8362_1 := h8362c.2.1
                                  have p8362_2 := h8362c.2.2.1
                                  have p8362_3 := h8362c.2.2.2
                                  linarith only [h8193, hlam, p8362_0]
                                · have p8362_0 := h8362c.1
                                  have p8362_1 := h8362c.2.1
                                  have p8362_2 := h8362c.2.2.1
                                  have p8362_3 := h8362c.2.2.2
                                  linarith only [h8194, hlam, p8362_1]
                                · have p8362_0 := h8362c.1
                                  have p8362_1 := h8362c.2.1
                                  have p8362_2 := h8362c.2.2.1
                                  have p8362_3 := h8362c.2.2.2
                                  linarith only [hlam, p8362_0]
                              · linarith only [h0, h8188, h8199, h8200, h8361, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · linarith only [h7464, h8194, h8199, hlam]
                    · linarith only [h6421, h8192, h8198, hlam]
                  · linarith only [h0, h8191, h8197, hlam]
                · linarith only [h0, h8190, h8196, hlam]
              · linarith only [h0, h8189, h8195, hlam]
            · linarith only [h7464, h8188, h8194, hlam]
          · linarith only [h6421, h8188, h8193, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h8396 | h8396
          · rcases m.htr 0 4 5 (by decide) (by decide) with h8397 | h8397
            · rcases m.htr 1 2 3 (by decide) (by decide) with h8398 | h8398
              · rcases m.htr 1 2 4 (by decide) (by decide) with h8399 | h8399
                · rcases m.htr 1 2 5 (by decide) (by decide) with h8400 | h8400
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h8401 | h8401
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h8402 | h8402
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h8403 | h8403
                        · linarith only [h8189, h8192, h8403, hlam]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h8405 | h8405
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h8406 | h8406
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h8407 | h8407
                              · rcases h0bigk with h8408c | h8408c | h8408c | h8408c | h8408c | h8408c | h8408c | h8408c | h8408c | h8408c | h8408c | h8408c | h8408c | h8408c | h8408c | h8408c | h8408c | h8408c | h8408c | h8408c | h8408c | h8408c | h8408c | h8408c | h8408c
                                · have p8408_0 := h8408c.1
                                  have p8408_1 := h8408c.2.1
                                  have p8408_2 := h8408c.2.2.1
                                  have p8408_3 := h8408c.2.2.2
                                  linarith only [hlam, p8408_0]
                                · have p8408_0 := h8408c.1
                                  have p8408_1 := h8408c.2.1
                                  have p8408_2 := h8408c.2.2.1
                                  have p8408_3 := h8408c.2.2.2
                                  linarith only [h0, hlam, p8408_1]
                                · have p8408_0 := h8408c.1
                                  have p8408_1 := h8408c.2.1
                                  have p8408_2 := h8408c.2.2.1
                                  have p8408_3 := h8408c.2.2.2
                                  linarith only [h6421, hlam, p8408_0]
                                · have p8408_0 := h8408c.1
                                  have p8408_1 := h8408c.2.1
                                  have p8408_2 := h8408c.2.2.1
                                  have p8408_3 := h8408c.2.2.2
                                  linarith only [h7464, hlam, p8408_1]
                                · have p8408_0 := h8408c.1
                                  have p8408_1 := h8408c.2.1
                                  have p8408_2 := h8408c.2.2.1
                                  have p8408_3 := h8408c.2.2.2
                                  linarith only [h6421, h8192, h8398, h8401, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p8408_1]
                                · have p8408_0 := h8408c.1
                                  have p8408_1 := h8408c.2.1
                                  have p8408_2 := h8408c.2.2.1
                                  have p8408_3 := h8408c.2.2.2
                                  linarith only [h0, hc01, hc12, hlam, hphi, p8408_1]
                                · have p8408_0 := h8408c.1
                                  have p8408_1 := h8408c.2.1
                                  have p8408_2 := h8408c.2.2.1
                                  have p8408_3 := h8408c.2.2.2
                                  linarith only [hlam, p8408_0]
                                · have p8408_0 := h8408c.1
                                  have p8408_1 := h8408c.2.1
                                  have p8408_2 := h8408c.2.2.1
                                  have p8408_3 := h8408c.2.2.2
                                  linarith only [h0, h6421, h8188, h8400, h8405, h8407, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p8408_1]
                                · have p8408_0 := h8408c.1
                                  have p8408_1 := h8408c.2.1
                                  have p8408_2 := h8408c.2.2.1
                                  have p8408_3 := h8408c.2.2.2
                                  linarith only [h0, h6421, h8188, h8192, h8400, h8405, h8407, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p8408_1]
                                · have p8408_0 := h8408c.1
                                  have p8408_1 := h8408c.2.1
                                  have p8408_2 := h8408c.2.2.1
                                  have p8408_3 := h8408c.2.2.2
                                  rcases p8408_3 (m.d 0 1) (by simp) with h8418 | h8418
                                  · linarith only [h0, h8418, hlam]
                                  · linarith only [h8188, h8418, hlam]
                                · have p8408_0 := h8408c.1
                                  have p8408_1 := h8408c.2.1
                                  have p8408_2 := h8408c.2.2.1
                                  have p8408_3 := h8408c.2.2.2
                                  linarith only [h8188, h8400, h8405, h8407, hc03, hc45, hlam, hphi, ht0b, ht5b, p8408_1]
                                · have p8408_0 := h8408c.1
                                  have p8408_1 := h8408c.2.1
                                  have p8408_2 := h8408c.2.2.1
                                  have p8408_3 := h8408c.2.2.2
                                  linarith only [h8189, hlam, p8408_1]
                                · have p8408_0 := h8408c.1
                                  have p8408_1 := h8408c.2.1
                                  have p8408_2 := h8408c.2.2.1
                                  have p8408_3 := h8408c.2.2.2
                                  linarith only [hlam, p8408_0]
                                · have p8408_0 := h8408c.1
                                  have p8408_1 := h8408c.2.1
                                  have p8408_2 := h8408c.2.2.1
                                  have p8408_3 := h8408c.2.2.2
                                  linarith only [h8192, hlam, p8408_1]
                                · have p8408_0 := h8408c.1
                                  have p8408_1 := h8408c.2.1
                                  have p8408_2 := h8408c.2.2.1
                                  have p8408_3 := h8408c.2.2.2
                                  linarith only [h8188, h8192, h8398, h8400, h8401, h8405, h8407, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p8408_1]
                                · have p8408_0 := h8408c.1
                                  have p8408_1 := h8408c.2.1
                                  have p8408_2 := h8408c.2.2.1
                                  have p8408_3 := h8408c.2.2.2
                                  linarith only [h8188, h8192, h8398, h8400, h8401, h8405, h8407, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p8408_1]
                                · have p8408_0 := h8408c.1
                                  have p8408_1 := h8408c.2.1
                                  have p8408_2 := h8408c.2.2.1
                                  have p8408_3 := h8408c.2.2.2
                                  linarith only [h8190, hlam, p8408_0]
                                · have p8408_0 := h8408c.1
                                  have p8408_1 := h8408c.2.1
                                  have p8408_2 := h8408c.2.2.1
                                  have p8408_3 := h8408c.2.2.2
                                  linarith only [h8192, h8398, h8401, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8408_1]
                                · have p8408_0 := h8408c.1
                                  have p8408_1 := h8408c.2.1
                                  have p8408_2 := h8408c.2.2.1
                                  have p8408_3 := h8408c.2.2.2
                                  linarith only [hlam, p8408_0]
                                · have p8408_0 := h8408c.1
                                  have p8408_1 := h8408c.2.1
                                  have p8408_2 := h8408c.2.2.1
                                  have p8408_3 := h8408c.2.2.2
                                  linarith only [h8188, h8192, h8398, h8400, h8401, h8405, h8407, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p8408_1]
                                · have p8408_0 := h8408c.1
                                  have p8408_1 := h8408c.2.1
                                  have p8408_2 := h8408c.2.2.1
                                  have p8408_3 := h8408c.2.2.2
                                  linarith only [h8188, hlam, p8408_0]
                                · have p8408_0 := h8408c.1
                                  have p8408_1 := h8408c.2.1
                                  have p8408_2 := h8408c.2.2.1
                                  have p8408_3 := h8408c.2.2.2
                                  linarith only [h8191, hlam, p8408_1]
                                · have p8408_0 := h8408c.1
                                  have p8408_1 := h8408c.2.1
                                  have p8408_2 := h8408c.2.2.1
                                  have p8408_3 := h8408c.2.2.2
                                  linarith only [h8396, hlam, p8408_0]
                                · have p8408_0 := h8408c.1
                                  have p8408_1 := h8408c.2.1
                                  have p8408_2 := h8408c.2.2.1
                                  have p8408_3 := h8408c.2.2.2
                                  linarith only [h8397, hlam, p8408_1]
                                · have p8408_0 := h8408c.1
                                  have p8408_1 := h8408c.2.1
                                  have p8408_2 := h8408c.2.2.1
                                  have p8408_3 := h8408c.2.2.2
                                  linarith only [hlam, p8408_0]
                              · linarith only [h6421, h8188, h8192, h8397, h8400, h8407, hc04, hc25, hlam, hphi, ht0b, ht5b]
                            · linarith only [h6421, h8188, h8192, h8398, h8401, h8402, h8406, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · linarith only [h8192, h8396, h8398, h8401, h8405, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · linarith only [h8192, h8397, h8401, h8402, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h8440 | h8440
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h8441 | h8441
                        · linarith only [h6421, h8401, h8441, hc01, hc23, hlam, hphi, ht12]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h8443 | h8443
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h8444 | h8444
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h8445 | h8445
                              · rcases h0bigk with h8446c | h8446c | h8446c | h8446c | h8446c | h8446c | h8446c | h8446c | h8446c | h8446c | h8446c | h8446c | h8446c | h8446c | h8446c | h8446c | h8446c | h8446c | h8446c | h8446c | h8446c | h8446c | h8446c | h8446c | h8446c
                                · have p8446_0 := h8446c.1
                                  have p8446_1 := h8446c.2.1
                                  have p8446_2 := h8446c.2.2.1
                                  have p8446_3 := h8446c.2.2.2
                                  linarith only [hlam, p8446_0]
                                · have p8446_0 := h8446c.1
                                  have p8446_1 := h8446c.2.1
                                  have p8446_2 := h8446c.2.2.1
                                  have p8446_3 := h8446c.2.2.2
                                  linarith only [h0, hlam, p8446_1]
                                · have p8446_0 := h8446c.1
                                  have p8446_1 := h8446c.2.1
                                  have p8446_2 := h8446c.2.2.1
                                  have p8446_3 := h8446c.2.2.2
                                  linarith only [h6421, hlam, p8446_0]
                                · have p8446_0 := h8446c.1
                                  have p8446_1 := h8446c.2.1
                                  have p8446_2 := h8446c.2.2.1
                                  have p8446_3 := h8446c.2.2.2
                                  linarith only [h7464, hlam, p8446_1]
                                · have p8446_0 := h8446c.1
                                  have p8446_1 := h8446c.2.1
                                  have p8446_2 := h8446c.2.2.1
                                  have p8446_3 := h8446c.2.2.2
                                  linarith only [h6421, h8399, h8401, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p8446_1]
                                · have p8446_0 := h8446c.1
                                  have p8446_1 := h8446c.2.1
                                  have p8446_2 := h8446c.2.2.1
                                  have p8446_3 := h8446c.2.2.2
                                  linarith only [h0, hc01, hc12, hlam, hphi, p8446_1]
                                · have p8446_0 := h8446c.1
                                  have p8446_1 := h8446c.2.1
                                  have p8446_2 := h8446c.2.2.1
                                  have p8446_3 := h8446c.2.2.2
                                  linarith only [hlam, p8446_0]
                                · have p8446_0 := h8446c.1
                                  have p8446_1 := h8446c.2.1
                                  have p8446_2 := h8446c.2.2.1
                                  have p8446_3 := h8446c.2.2.2
                                  linarith only [h0, h6421, h8188, h8400, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p8446_1]
                                · have p8446_0 := h8446c.1
                                  have p8446_1 := h8446c.2.1
                                  have p8446_2 := h8446c.2.2.1
                                  have p8446_3 := h8446c.2.2.2
                                  linarith only [h0, h7464, h8188, h8400, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p8446_1]
                                · have p8446_0 := h8446c.1
                                  have p8446_1 := h8446c.2.1
                                  have p8446_2 := h8446c.2.2.1
                                  have p8446_3 := h8446c.2.2.2
                                  rcases p8446_3 (m.d 0 1) (by simp) with h8456 | h8456
                                  · linarith only [h0, h8456, hlam]
                                  · linarith only [h8188, h8456, hlam]
                                · have p8446_0 := h8446c.1
                                  have p8446_1 := h8446c.2.1
                                  have p8446_2 := h8446c.2.2.1
                                  have p8446_3 := h8446c.2.2.2
                                  linarith only [h8188, h8400, h8443, h8445, hc03, hc45, hlam, hphi, ht0b, ht5b, p8446_1]
                                · have p8446_0 := h8446c.1
                                  have p8446_1 := h8446c.2.1
                                  have p8446_2 := h8446c.2.2.1
                                  have p8446_3 := h8446c.2.2.2
                                  linarith only [h8189, hlam, p8446_1]
                                · have p8446_0 := h8446c.1
                                  have p8446_1 := h8446c.2.1
                                  have p8446_2 := h8446c.2.2.1
                                  have p8446_3 := h8446c.2.2.2
                                  linarith only [hlam, p8446_0]
                                · have p8446_0 := h8446c.1
                                  have p8446_1 := h8446c.2.1
                                  have p8446_2 := h8446c.2.2.1
                                  have p8446_3 := h8446c.2.2.2
                                  linarith only [h8192, hlam, p8446_1]
                                · have p8446_0 := h8446c.1
                                  have p8446_1 := h8446c.2.1
                                  have p8446_2 := h8446c.2.2.1
                                  have p8446_3 := h8446c.2.2.2
                                  linarith only [h6421, h8401, hc05, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p8446_1]
                                · have p8446_0 := h8446c.1
                                  have p8446_1 := h8446c.2.1
                                  have p8446_2 := h8446c.2.2.1
                                  have p8446_3 := h8446c.2.2.2
                                  linarith only [h8188, h8400, h8443, h8445, hc04, hc45, hlam, hphi, ht0b, ht5b, p8446_1]
                                · have p8446_0 := h8446c.1
                                  have p8446_1 := h8446c.2.1
                                  have p8446_2 := h8446c.2.2.1
                                  have p8446_3 := h8446c.2.2.2
                                  linarith only [h8190, hlam, p8446_0]
                                · have p8446_0 := h8446c.1
                                  have p8446_1 := h8446c.2.1
                                  have p8446_2 := h8446c.2.2.1
                                  have p8446_3 := h8446c.2.2.2
                                  linarith only [h7464, h8401, hc03, hc34, hlam, hphi, p8446_1]
                                · have p8446_0 := h8446c.1
                                  have p8446_1 := h8446c.2.1
                                  have p8446_2 := h8446c.2.2.1
                                  have p8446_3 := h8446c.2.2.2
                                  linarith only [hlam, p8446_0]
                                · have p8446_0 := h8446c.1
                                  have p8446_1 := h8446c.2.1
                                  have p8446_2 := h8446c.2.2.1
                                  have p8446_3 := h8446c.2.2.2
                                  rcases p8446_3 (m.d 0 1) (by simp) with h8468 | h8468
                                  · linarith only [h7464, h8468, hlam]
                                  · linarith only [h8188, h8468, hlam]
                                · have p8446_0 := h8446c.1
                                  have p8446_1 := h8446c.2.1
                                  have p8446_2 := h8446c.2.2.1
                                  have p8446_3 := h8446c.2.2.2
                                  linarith only [h8188, hlam, p8446_0]
                                · have p8446_0 := h8446c.1
                                  have p8446_1 := h8446c.2.1
                                  have p8446_2 := h8446c.2.2.1
                                  have p8446_3 := h8446c.2.2.2
                                  linarith only [h8191, hlam, p8446_1]
                                · have p8446_0 := h8446c.1
                                  have p8446_1 := h8446c.2.1
                                  have p8446_2 := h8446c.2.2.1
                                  have p8446_3 := h8446c.2.2.2
                                  linarith only [h8396, hlam, p8446_0]
                                · have p8446_0 := h8446c.1
                                  have p8446_1 := h8446c.2.1
                                  have p8446_2 := h8446c.2.2.1
                                  have p8446_3 := h8446c.2.2.2
                                  linarith only [h8397, hlam, p8446_1]
                                · have p8446_0 := h8446c.1
                                  have p8446_1 := h8446c.2.1
                                  have p8446_2 := h8446c.2.2.1
                                  have p8446_3 := h8446c.2.2.2
                                  linarith only [hlam, p8446_0]
                              · linarith only [h6421, h8401, h8445, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                            · linarith only [h6421, h8188, h8401, h8440, h8441, h8444, hc23, hc34, hlam, hphi]
                          · linarith only [h6421, h8396, h8401, h8443, hc23, hc34, hlam, hphi]
                      · linarith only [h7464, h8397, h8440, hlam]
                  · linarith only [h0, h8191, h8400, hlam]
                · linarith only [h0, h8190, h8399, hlam]
              · linarith only [h0, h8189, h8398, hlam]
            · linarith only [h7464, h8188, h8397, hlam]
          · linarith only [h6421, h8188, h8396, hlam]
      · linarith only [h0, h8188, h8191, hlam]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h8486 | h8486
      · rcases m.htr 0 3 4 (by decide) (by decide) with h8487 | h8487
        · linarith only [h8189, h8190, h8487, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h8489 | h8489
          · rcases m.htr 0 4 5 (by decide) (by decide) with h8490 | h8490
            · rcases m.htr 1 2 3 (by decide) (by decide) with h8491 | h8491
              · rcases m.htr 1 2 4 (by decide) (by decide) with h8492 | h8492
                · rcases m.htr 1 2 5 (by decide) (by decide) with h8493 | h8493
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h8494 | h8494
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h8495 | h8495
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h8496 | h8496
                        · linarith only [h6421, h8189, h8190, h8487, h8492, h8496, hc01, hc12, hlam, hphi]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h8498 | h8498
                          · linarith only [h8189, h8190, h8491, h8494, h8496, h8498, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                          · linarith only [h8189, h8190, h8489, h8491, h8494, h8496, h8498, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · linarith only [h7464, h8188, h8490, h8493, h8495, hc04, hc25, hlam, hphi, ht0b, ht5b]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h8502 | h8502
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h8503 | h8503
                        · linarith only [h0, h6421, h8188, h8189, h8493, h8494, h8503, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h8505 | h8505
                          · linarith only [h8189, h8190, h8492, h8505, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                          · linarith only [h6421, h8489, h8494, h8505, hc23, hc34, hlam, hphi]
                      · linarith only [h8189, h8190, h8492, h8502, hc23, hc45, hlam, hphi, ht34]
                  · linarith only [h8190, h8486, h8493, hc12, hc24, hlam, hphi]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h8510 | h8510
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h8511 | h8511
                    · linarith only [h6421, h8487, h8491, h8492, h8511, hc01, hc24, hlam, hphi, ht12]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h8513 | h8513
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h8514 | h8514
                        · linarith only [h6421, h8188, h8189, h8510, h8511, h8514, hc03, hc25, hlam, hphi, ht0b, ht5b]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h8516 | h8516
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h8517 | h8517
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h8518 | h8518
                              · rcases h0bigk with h8519c | h8519c | h8519c | h8519c | h8519c | h8519c | h8519c | h8519c | h8519c | h8519c | h8519c | h8519c | h8519c | h8519c | h8519c | h8519c | h8519c | h8519c | h8519c | h8519c | h8519c | h8519c | h8519c | h8519c | h8519c
                                · have p8519_0 := h8519c.1
                                  have p8519_1 := h8519c.2.1
                                  have p8519_2 := h8519c.2.2.1
                                  have p8519_3 := h8519c.2.2.2
                                  linarith only [hlam, p8519_0]
                                · have p8519_0 := h8519c.1
                                  have p8519_1 := h8519c.2.1
                                  have p8519_2 := h8519c.2.2.1
                                  have p8519_3 := h8519c.2.2.2
                                  linarith only [h0, hlam, p8519_1]
                                · have p8519_0 := h8519c.1
                                  have p8519_1 := h8519c.2.1
                                  have p8519_2 := h8519c.2.2.1
                                  have p8519_3 := h8519c.2.2.2
                                  linarith only [h6421, hlam, p8519_0]
                                · have p8519_0 := h8519c.1
                                  have p8519_1 := h8519c.2.1
                                  have p8519_2 := h8519c.2.2.1
                                  have p8519_3 := h8519c.2.2.2
                                  linarith only [h7464, hlam, p8519_1]
                                · have p8519_0 := h8519c.1
                                  have p8519_1 := h8519c.2.1
                                  have p8519_2 := h8519c.2.2.1
                                  have p8519_3 := h8519c.2.2.2
                                  linarith only [h6421, hc05, hc13, hlam, hphi, ht01, ht0b, ht5b, p8519_1]
                                · have p8519_0 := h8519c.1
                                  have p8519_1 := h8519c.2.1
                                  have p8519_2 := h8519c.2.2.1
                                  have p8519_3 := h8519c.2.2.2
                                  linarith only [h0, h8492, h8514, hc01, hc34, hlam, hphi, ht12, ht23, p8519_1]
                                · have p8519_0 := h8519c.1
                                  have p8519_1 := h8519c.2.1
                                  have p8519_2 := h8519c.2.2.1
                                  have p8519_3 := h8519c.2.2.2
                                  linarith only [hlam, p8519_0]
                                · have p8519_0 := h8519c.1
                                  have p8519_1 := h8519c.2.1
                                  have p8519_2 := h8519c.2.2.1
                                  have p8519_3 := h8519c.2.2.2
                                  linarith only [h0, h8492, h8514, hc03, hc34, hlam, hphi, p8519_1]
                                · have p8519_0 := h8519c.1
                                  have p8519_1 := h8519c.2.1
                                  have p8519_2 := h8519c.2.2.1
                                  have p8519_3 := h8519c.2.2.2
                                  linarith only [h8190, hlam, p8519_1]
                                · have p8519_0 := h8519c.1
                                  have p8519_1 := h8519c.2.1
                                  have p8519_2 := h8519c.2.2.1
                                  have p8519_3 := h8519c.2.2.2
                                  linarith only [h0, h8188, h8492, h8510, h8514, h8516, h8518, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p8519_1]
                                · have p8519_0 := h8519c.1
                                  have p8519_1 := h8519c.2.1
                                  have p8519_2 := h8519c.2.2.1
                                  have p8519_3 := h8519c.2.2.2
                                  linarith only [h8188, h8510, h8516, h8518, hc03, hc45, hlam, hphi, ht0b, ht5b, p8519_1]
                                · have p8519_0 := h8519c.1
                                  have p8519_1 := h8519c.2.1
                                  have p8519_2 := h8519c.2.2.1
                                  have p8519_3 := h8519c.2.2.2
                                  linarith only [h8189, hlam, p8519_1]
                                · have p8519_0 := h8519c.1
                                  have p8519_1 := h8519c.2.1
                                  have p8519_2 := h8519c.2.2.1
                                  have p8519_3 := h8519c.2.2.2
                                  linarith only [hlam, p8519_0]
                                · have p8519_0 := h8519c.1
                                  have p8519_1 := h8519c.2.1
                                  have p8519_2 := h8519c.2.2.1
                                  have p8519_3 := h8519c.2.2.2
                                  linarith only [h8487, hlam, p8519_1]
                                · have p8519_0 := h8519c.1
                                  have p8519_1 := h8519c.2.1
                                  have p8519_2 := h8519c.2.2.1
                                  have p8519_3 := h8519c.2.2.2
                                  linarith only [h0, h8188, h8189, h8492, h8510, h8514, h8516, h8518, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p8519_1]
                                · have p8519_0 := h8519c.1
                                  have p8519_1 := h8519c.2.1
                                  have p8519_2 := h8519c.2.2.1
                                  have p8519_3 := h8519c.2.2.2
                                  linarith only [h7464, h8188, h8492, h8510, h8514, h8516, h8518, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p8519_1]
                                · have p8519_0 := h8519c.1
                                  have p8519_1 := h8519c.2.1
                                  have p8519_2 := h8519c.2.2.1
                                  have p8519_3 := h8519c.2.2.2
                                  linarith only [h7464, h8492, h8514, hc02, hc34, hlam, hphi, ht23, p8519_1]
                                · have p8519_0 := h8519c.1
                                  have p8519_1 := h8519c.2.1
                                  have p8519_2 := h8519c.2.2.1
                                  have p8519_3 := h8519c.2.2.2
                                  linarith only [h7464, h8492, h8514, hc03, hc34, hlam, hphi, p8519_1]
                                · have p8519_0 := h8519c.1
                                  have p8519_1 := h8519c.2.1
                                  have p8519_2 := h8519c.2.2.1
                                  have p8519_3 := h8519c.2.2.2
                                  linarith only [hlam, p8519_0]
                                · have p8519_0 := h8519c.1
                                  have p8519_1 := h8519c.2.1
                                  have p8519_2 := h8519c.2.2.1
                                  have p8519_3 := h8519c.2.2.2
                                  rcases p8519_3 (m.d 0 1) (by simp) with h8539 | h8539
                                  · linarith only [h7464, h8539, hlam]
                                  · linarith only [h8188, h8539, hlam]
                                · have p8519_0 := h8519c.1
                                  have p8519_1 := h8519c.2.1
                                  have p8519_2 := h8519c.2.2.1
                                  have p8519_3 := h8519c.2.2.2
                                  linarith only [h8188, hlam, p8519_0]
                                · have p8519_0 := h8519c.1
                                  have p8519_1 := h8519c.2.1
                                  have p8519_2 := h8519c.2.2.1
                                  have p8519_3 := h8519c.2.2.2
                                  linarith only [h8486, hlam, p8519_1]
                                · have p8519_0 := h8519c.1
                                  have p8519_1 := h8519c.2.1
                                  have p8519_2 := h8519c.2.2.1
                                  have p8519_3 := h8519c.2.2.2
                                  linarith only [h8489, hlam, p8519_0]
                                · have p8519_0 := h8519c.1
                                  have p8519_1 := h8519c.2.1
                                  have p8519_2 := h8519c.2.2.1
                                  have p8519_3 := h8519c.2.2.2
                                  linarith only [h8490, hlam, p8519_1]
                                · have p8519_0 := h8519c.1
                                  have p8519_1 := h8519c.2.1
                                  have p8519_2 := h8519c.2.2.1
                                  have p8519_3 := h8519c.2.2.2
                                  linarith only [hlam, p8519_0]
                              · linarith only [h0, h8188, h8492, h8510, h8514, h8518, hc25, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b]
                            · linarith only [h6421, h8188, h8491, h8492, h8513, h8517, hlam]
                          · linarith only [h6421, h8489, h8491, h8492, h8514, h8516, hc23, hc34, hlam, hphi]
                      · linarith only [h7464, h8490, h8513, hlam]
                  · linarith only [h6421, h8188, h8190, h8486, h8491, h8510, hc04, hc15, hlam, hphi, ht0b, ht5b]
              · linarith only [h0, h8189, h8491, hlam]
            · linarith only [h0, h8188, h8190, h8490, hlam]
          · linarith only [h6421, h8188, h8489, hlam]
      · linarith only [h6421, h8188, h8189, h8486, hlam]
  · rcases m.htr 0 2 4 (by decide) (by decide) with h8556 | h8556
    · rcases m.htr 0 2 5 (by decide) (by decide) with h8557 | h8557
      · rcases m.htr 0 3 4 (by decide) (by decide) with h8558 | h8558
        · rcases m.htr 0 3 5 (by decide) (by decide) with h8559 | h8559
          · rcases m.htr 0 4 5 (by decide) (by decide) with h8560 | h8560
            · rcases m.htr 1 2 3 (by decide) (by decide) with h8561 | h8561
              · rcases m.htr 1 2 4 (by decide) (by decide) with h8562 | h8562
                · rcases m.htr 1 2 5 (by decide) (by decide) with h8563 | h8563
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h8564 | h8564
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h8565 | h8565
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h8566 | h8566
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h8567 | h8567
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h8568 | h8568
                            · linarith only [h8189, h8556, h8561, h8568, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                            · linarith only [h8189, h8556, h8560, h8561, h8568, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · linarith only [h7464, h8188, h8189, h8556, h8559, h8567, hc03, hc15, hlam, hphi, ht0b, ht5b]
                        · linarith only [h8189, h8558, h8566, hlam]
                      · linarith only [h7464, h8188, h8556, h8560, h8563, h8565, hc02, hc25, hlam, hphi, ht0b, ht5b]
                    · linarith only [h6421, h8188, h8189, h8556, h8558, h8561, h8563, h8564, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b]
                  · linarith only [h8189, h8561, h8563, hc02, hc25, hlam, hphi]
                · linarith only [h8189, h8556, h8561, h8562, hlam]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h8577 | h8577
                · rcases m.htr 1 2 5 (by decide) (by decide) with h8578 | h8578
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h8579 | h8579
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h8580 | h8580
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h8581 | h8581
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h8582 | h8582
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h8583 | h8583
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h8584 | h8584
                              · rcases h0bigk with h8585c | h8585c | h8585c | h8585c | h8585c | h8585c | h8585c | h8585c | h8585c | h8585c | h8585c | h8585c | h8585c | h8585c | h8585c | h8585c | h8585c | h8585c | h8585c | h8585c | h8585c | h8585c | h8585c | h8585c | h8585c
                                · have p8585_0 := h8585c.1
                                  have p8585_1 := h8585c.2.1
                                  have p8585_2 := h8585c.2.2.1
                                  have p8585_3 := h8585c.2.2.2
                                  linarith only [hlam, p8585_0]
                                · have p8585_0 := h8585c.1
                                  have p8585_1 := h8585c.2.1
                                  have p8585_2 := h8585c.2.2.1
                                  have p8585_3 := h8585c.2.2.2
                                  linarith only [h0, hlam, p8585_1]
                                · have p8585_0 := h8585c.1
                                  have p8585_1 := h8585c.2.1
                                  have p8585_2 := h8585c.2.2.1
                                  have p8585_3 := h8585c.2.2.2
                                  linarith only [h6421, hlam, p8585_0]
                                · have p8585_0 := h8585c.1
                                  have p8585_1 := h8585c.2.1
                                  have p8585_2 := h8585c.2.2.1
                                  have p8585_3 := h8585c.2.2.2
                                  linarith only [h7464, hlam, p8585_1]
                                · have p8585_0 := h8585c.1
                                  have p8585_1 := h8585c.2.1
                                  have p8585_2 := h8585c.2.2.1
                                  have p8585_3 := h8585c.2.2.2
                                  linarith only [h7464, h8561, h8577, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p8585_1]
                                · have p8585_0 := h8585c.1
                                  have p8585_1 := h8585c.2.1
                                  have p8585_2 := h8585c.2.2.1
                                  have p8585_3 := h8585c.2.2.2
                                  linarith only [h8188, hc02, hc15, hlam, hphi, ht0b, ht5b, p8585_1]
                                · have p8585_0 := h8585c.1
                                  have p8585_1 := h8585c.2.1
                                  have p8585_2 := h8585c.2.2.1
                                  have p8585_3 := h8585c.2.2.2
                                  linarith only [hlam, p8585_0]
                                · have p8585_0 := h8585c.1
                                  have p8585_1 := h8585c.2.1
                                  have p8585_2 := h8585c.2.2.1
                                  have p8585_3 := h8585c.2.2.2
                                  linarith only [h8189, hlam, p8585_0]
                                · have p8585_0 := h8585c.1
                                  have p8585_1 := h8585c.2.1
                                  have p8585_2 := h8585c.2.2.1
                                  have p8585_3 := h8585c.2.2.2
                                  linarith only [h0, h8561, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p8585_1]
                                · have p8585_0 := h8585c.1
                                  have p8585_1 := h8585c.2.1
                                  have p8585_2 := h8585c.2.2.1
                                  have p8585_3 := h8585c.2.2.2
                                  linarith only [h0, h8188, h8561, h8578, h8582, hc23, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p8585_1]
                                · have p8585_0 := h8585c.1
                                  have p8585_1 := h8585c.2.1
                                  have p8585_2 := h8585c.2.2.1
                                  have p8585_3 := h8585c.2.2.2
                                  linarith only [h6421, h8188, h8561, h8578, h8582, hc23, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p8585_1]
                                · have p8585_0 := h8585c.1
                                  have p8585_1 := h8585c.2.1
                                  have p8585_2 := h8585c.2.2.1
                                  have p8585_3 := h8585c.2.2.2
                                  linarith only [h6421, h8561, hc02, hc23, hlam, hphi, p8585_1]
                                · have p8585_0 := h8585c.1
                                  have p8585_1 := h8585c.2.1
                                  have p8585_2 := h8585c.2.2.1
                                  have p8585_3 := h8585c.2.2.2
                                  linarith only [hlam, p8585_0]
                                · have p8585_0 := h8585c.1
                                  have p8585_1 := h8585c.2.1
                                  have p8585_2 := h8585c.2.2.1
                                  have p8585_3 := h8585c.2.2.2
                                  linarith only [h6421, h7464, h8188, h8561, h8578, h8582, hc23, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p8585_1]
                                · have p8585_0 := h8585c.1
                                  have p8585_1 := h8585c.2.1
                                  have p8585_2 := h8585c.2.2.1
                                  have p8585_3 := h8585c.2.2.2
                                  rcases p8585_3 (m.d 0 1) (by simp) with h8600 | h8600
                                  · linarith only [h6421, h8600, hlam]
                                  · linarith only [h8188, h8600, hlam]
                                · have p8585_0 := h8585c.1
                                  have p8585_1 := h8585c.2.1
                                  have p8585_2 := h8585c.2.2.1
                                  have p8585_3 := h8585c.2.2.2
                                  linarith only [h8188, h8578, h8582, h8584, hc04, hc45, hlam, hphi, ht0b, ht5b, p8585_1]
                                · have p8585_0 := h8585c.1
                                  have p8585_1 := h8585c.2.1
                                  have p8585_2 := h8585c.2.2.1
                                  have p8585_3 := h8585c.2.2.2
                                  linarith only [h8556, hlam, p8585_0]
                                · have p8585_0 := h8585c.1
                                  have p8585_1 := h8585c.2.1
                                  have p8585_2 := h8585c.2.2.1
                                  have p8585_3 := h8585c.2.2.2
                                  linarith only [h8558, hlam, p8585_0]
                                · have p8585_0 := h8585c.1
                                  have p8585_1 := h8585c.2.1
                                  have p8585_2 := h8585c.2.2.1
                                  have p8585_3 := h8585c.2.2.2
                                  linarith only [hlam, p8585_0]
                                · have p8585_0 := h8585c.1
                                  have p8585_1 := h8585c.2.1
                                  have p8585_2 := h8585c.2.2.1
                                  have p8585_3 := h8585c.2.2.2
                                  linarith only [h0, h8188, h8556, h8561, h8578, h8582, h8584, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p8585_1]
                                · have p8585_0 := h8585c.1
                                  have p8585_1 := h8585c.2.1
                                  have p8585_2 := h8585c.2.2.1
                                  have p8585_3 := h8585c.2.2.2
                                  linarith only [h8188, hlam, p8585_0]
                                · have p8585_0 := h8585c.1
                                  have p8585_1 := h8585c.2.1
                                  have p8585_2 := h8585c.2.2.1
                                  have p8585_3 := h8585c.2.2.2
                                  linarith only [h8557, hlam, p8585_1]
                                · have p8585_0 := h8585c.1
                                  have p8585_1 := h8585c.2.1
                                  have p8585_2 := h8585c.2.2.1
                                  have p8585_3 := h8585c.2.2.2
                                  linarith only [h8559, hlam, p8585_0]
                                · have p8585_0 := h8585c.1
                                  have p8585_1 := h8585c.2.1
                                  have p8585_2 := h8585c.2.2.1
                                  have p8585_3 := h8585c.2.2.2
                                  linarith only [h8560, hlam, p8585_1]
                                · have p8585_0 := h8585c.1
                                  have p8585_1 := h8585c.2.1
                                  have p8585_2 := h8585c.2.2.1
                                  have p8585_3 := h8585c.2.2.2
                                  linarith only [hlam, p8585_0]
                              · linarith only [h0, h8188, h8561, h8580, h8584, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                            · linarith only [h7464, h8188, h8561, h8577, h8580, h8583, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                          · linarith only [h7464, h8561, h8577, h8582, hc01, hc35, hlam, hphi, ht12, ht23]
                        · linarith only [h7464, h8188, h8561, h8577, h8580, h8581, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                      · linarith only [h7464, h8188, h8556, h8560, h8578, h8580, hc02, hc25, hlam, hphi, ht0b, ht5b]
                    · linarith only [h0, h6421, h8188, h8556, h8558, h8561, h8578, h8579, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
                  · linarith only [h0, h8557, h8578, hlam]
                · linarith only [h0, h8556, h8577, hlam]
            · linarith only [h7464, h8188, h8560, hlam]
          · linarith only [h7464, h8188, h8189, h8556, h8559, hlam]
        · linarith only [h8189, h8556, h8558, hlam]
      · linarith only [h7464, h8188, h8556, h8557, hlam]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h8625 | h8625
      · rcases m.htr 0 3 4 (by decide) (by decide) with h8626 | h8626
        · rcases m.htr 0 3 5 (by decide) (by decide) with h8627 | h8627
          · rcases m.htr 0 4 5 (by decide) (by decide) with h8628 | h8628
            · rcases m.htr 1 2 3 (by decide) (by decide) with h8629 | h8629
              · rcases m.htr 1 2 4 (by decide) (by decide) with h8630 | h8630
                · rcases m.htr 1 2 5 (by decide) (by decide) with h8631 | h8631
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h8632 | h8632
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h8633 | h8633
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h8634 | h8634
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h8635 | h8635
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h8636 | h8636
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h8637 | h8637
                              · rcases h0bigk with h8638c | h8638c | h8638c | h8638c | h8638c | h8638c | h8638c | h8638c | h8638c | h8638c | h8638c | h8638c | h8638c | h8638c | h8638c | h8638c | h8638c | h8638c | h8638c | h8638c | h8638c | h8638c | h8638c | h8638c | h8638c
                                · have p8638_0 := h8638c.1
                                  have p8638_1 := h8638c.2.1
                                  have p8638_2 := h8638c.2.2.1
                                  have p8638_3 := h8638c.2.2.2
                                  linarith only [hlam, p8638_0]
                                · have p8638_0 := h8638c.1
                                  have p8638_1 := h8638c.2.1
                                  have p8638_2 := h8638c.2.2.1
                                  have p8638_3 := h8638c.2.2.2
                                  linarith only [h0, hlam, p8638_1]
                                · have p8638_0 := h8638c.1
                                  have p8638_1 := h8638c.2.1
                                  have p8638_2 := h8638c.2.2.1
                                  have p8638_3 := h8638c.2.2.2
                                  linarith only [h6421, hlam, p8638_0]
                                · have p8638_0 := h8638c.1
                                  have p8638_1 := h8638c.2.1
                                  have p8638_2 := h8638c.2.2.1
                                  have p8638_3 := h8638c.2.2.2
                                  linarith only [h7464, hlam, p8638_1]
                                · have p8638_0 := h8638c.1
                                  have p8638_1 := h8638c.2.1
                                  have p8638_2 := h8638c.2.2.1
                                  have p8638_3 := h8638c.2.2.2
                                  linarith only [h0, h8556, h8629, h8634, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p8638_1]
                                · have p8638_0 := h8638c.1
                                  have p8638_1 := h8638c.2.1
                                  have p8638_2 := h8638c.2.2.1
                                  have p8638_3 := h8638c.2.2.2
                                  linarith only [h8556, h8629, h8634, hc01, hc12, hlam, hphi, p8638_1]
                                · have p8638_0 := h8638c.1
                                  have p8638_1 := h8638c.2.1
                                  have p8638_2 := h8638c.2.2.1
                                  have p8638_3 := h8638c.2.2.2
                                  linarith only [hlam, p8638_0]
                                · have p8638_0 := h8638c.1
                                  have p8638_1 := h8638c.2.1
                                  have p8638_2 := h8638c.2.2.1
                                  have p8638_3 := h8638c.2.2.2
                                  linarith only [h8189, hlam, p8638_0]
                                · have p8638_0 := h8638c.1
                                  have p8638_1 := h8638c.2.1
                                  have p8638_2 := h8638c.2.2.1
                                  have p8638_3 := h8638c.2.2.2
                                  linarith only [h8556, hlam, p8638_1]
                                · have p8638_0 := h8638c.1
                                  have p8638_1 := h8638c.2.1
                                  have p8638_2 := h8638c.2.2.1
                                  have p8638_3 := h8638c.2.2.2
                                  linarith only [h8188, h8556, h8629, h8631, h8634, h8635, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p8638_1]
                                · have p8638_0 := h8638c.1
                                  have p8638_1 := h8638c.2.1
                                  have p8638_2 := h8638c.2.2.1
                                  have p8638_3 := h8638c.2.2.2
                                  linarith only [h8188, h8631, h8635, hc03, hc35, hlam, hphi, ht0b, ht5b, p8638_1]
                                · have p8638_0 := h8638c.1
                                  have p8638_1 := h8638c.2.1
                                  have p8638_2 := h8638c.2.2.1
                                  have p8638_3 := h8638c.2.2.2
                                  linarith only [h8189, h8629, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p8638_1]
                                · have p8638_0 := h8638c.1
                                  have p8638_1 := h8638c.2.1
                                  have p8638_2 := h8638c.2.2.1
                                  have p8638_3 := h8638c.2.2.2
                                  linarith only [hlam, p8638_0]
                                · have p8638_0 := h8638c.1
                                  have p8638_1 := h8638c.2.1
                                  have p8638_2 := h8638c.2.2.1
                                  have p8638_3 := h8638c.2.2.2
                                  linarith only [h0, h8188, h8189, h8556, h8629, h8631, h8635, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p8638_1]
                                · have p8638_0 := h8638c.1
                                  have p8638_1 := h8638c.2.1
                                  have p8638_2 := h8638c.2.2.1
                                  have p8638_3 := h8638c.2.2.2
                                  linarith only [h8188, h8189, h8629, h8631, h8635, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p8638_1]
                                · have p8638_0 := h8638c.1
                                  have p8638_1 := h8638c.2.1
                                  have p8638_2 := h8638c.2.2.1
                                  have p8638_3 := h8638c.2.2.2
                                  linarith only [h8188, h8631, h8635, hc04, hc35, hlam, hphi, ht0b, ht5b, p8638_1]
                                · have p8638_0 := h8638c.1
                                  have p8638_1 := h8638c.2.1
                                  have p8638_2 := h8638c.2.2.1
                                  have p8638_3 := h8638c.2.2.2
                                  linarith only [h0, h8188, h8556, h8629, h8631, h8634, h8635, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p8638_1]
                                · have p8638_0 := h8638c.1
                                  have p8638_1 := h8638c.2.1
                                  have p8638_2 := h8638c.2.2.1
                                  have p8638_3 := h8638c.2.2.2
                                  linarith only [h8626, hlam, p8638_0]
                                · have p8638_0 := h8638c.1
                                  have p8638_1 := h8638c.2.1
                                  have p8638_2 := h8638c.2.2.1
                                  have p8638_3 := h8638c.2.2.2
                                  linarith only [hlam, p8638_0]
                                · have p8638_0 := h8638c.1
                                  have p8638_1 := h8638c.2.1
                                  have p8638_2 := h8638c.2.2.1
                                  have p8638_3 := h8638c.2.2.2
                                  linarith only [h8188, h8556, h8629, h8631, h8634, h8635, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p8638_1]
                                · have p8638_0 := h8638c.1
                                  have p8638_1 := h8638c.2.1
                                  have p8638_2 := h8638c.2.2.1
                                  have p8638_3 := h8638c.2.2.2
                                  linarith only [h8188, hlam, p8638_0]
                                · have p8638_0 := h8638c.1
                                  have p8638_1 := h8638c.2.1
                                  have p8638_2 := h8638c.2.2.1
                                  have p8638_3 := h8638c.2.2.2
                                  linarith only [h8625, hlam, p8638_1]
                                · have p8638_0 := h8638c.1
                                  have p8638_1 := h8638c.2.1
                                  have p8638_2 := h8638c.2.2.1
                                  have p8638_3 := h8638c.2.2.2
                                  linarith only [h8627, hlam, p8638_0]
                                · have p8638_0 := h8638c.1
                                  have p8638_1 := h8638c.2.1
                                  have p8638_2 := h8638c.2.2.1
                                  have p8638_3 := h8638c.2.2.2
                                  linarith only [h8628, hlam, p8638_1]
                                · have p8638_0 := h8638c.1
                                  have p8638_1 := h8638c.2.1
                                  have p8638_2 := h8638c.2.2.1
                                  have p8638_3 := h8638c.2.2.2
                                  linarith only [hlam, p8638_0]
                              · linarith only [h0, h8188, h8189, h8629, h8631, h8636, h8637, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                            · linarith only [h8556, h8628, h8636, hlam]
                          · linarith only [h8189, h8627, h8635, hlam]
                        · linarith only [h8189, h8626, h8634, hlam]
                      · linarith only [h7464, h8188, h8628, h8633, hc04, hc15, hlam, hphi, ht0b, ht5b]
                    · linarith only [h6421, h8188, h8189, h8626, h8629, h8631, h8632, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b]
                  · linarith only [h8189, h8629, h8631, hc02, hc25, hlam, hphi]
                · linarith only [h0, h8189, h8629, h8630, hc01, hc24, hlam, hphi, ht12]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h8672 | h8672
                · linarith only [h0, h8188, h8556, h8629, h8672, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h8674 | h8674
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h8675 | h8675
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h8676 | h8676
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h8677 | h8677
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h8678 | h8678
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h8679 | h8679
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h8680 | h8680
                              · rcases h0bigk with h8681c | h8681c | h8681c | h8681c | h8681c | h8681c | h8681c | h8681c | h8681c | h8681c | h8681c | h8681c | h8681c | h8681c | h8681c | h8681c | h8681c | h8681c | h8681c | h8681c | h8681c | h8681c | h8681c | h8681c | h8681c
                                · have p8681_0 := h8681c.1
                                  have p8681_1 := h8681c.2.1
                                  have p8681_2 := h8681c.2.2.1
                                  have p8681_3 := h8681c.2.2.2
                                  linarith only [hlam, p8681_0]
                                · have p8681_0 := h8681c.1
                                  have p8681_1 := h8681c.2.1
                                  have p8681_2 := h8681c.2.2.1
                                  have p8681_3 := h8681c.2.2.2
                                  linarith only [h0, hlam, p8681_1]
                                · have p8681_0 := h8681c.1
                                  have p8681_1 := h8681c.2.1
                                  have p8681_2 := h8681c.2.2.1
                                  have p8681_3 := h8681c.2.2.2
                                  linarith only [h6421, hlam, p8681_0]
                                · have p8681_0 := h8681c.1
                                  have p8681_1 := h8681c.2.1
                                  have p8681_2 := h8681c.2.2.1
                                  have p8681_3 := h8681c.2.2.2
                                  linarith only [h7464, hlam, p8681_1]
                                · have p8681_0 := h8681c.1
                                  have p8681_1 := h8681c.2.1
                                  have p8681_2 := h8681c.2.2.1
                                  have p8681_3 := h8681c.2.2.2
                                  linarith only [h0, h8672, h8677, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p8681_1]
                                · have p8681_0 := h8681c.1
                                  have p8681_1 := h8681c.2.1
                                  have p8681_2 := h8681c.2.2.1
                                  have p8681_3 := h8681c.2.2.2
                                  linarith only [h0, h8672, h8677, hc01, hc23, hlam, hphi, ht12, p8681_1]
                                · have p8681_0 := h8681c.1
                                  have p8681_1 := h8681c.2.1
                                  have p8681_2 := h8681c.2.2.1
                                  have p8681_3 := h8681c.2.2.2
                                  linarith only [hlam, p8681_0]
                                · have p8681_0 := h8681c.1
                                  have p8681_1 := h8681c.2.1
                                  have p8681_2 := h8681c.2.2.1
                                  have p8681_3 := h8681c.2.2.2
                                  linarith only [h8189, hlam, p8681_0]
                                · have p8681_0 := h8681c.1
                                  have p8681_1 := h8681c.2.1
                                  have p8681_2 := h8681c.2.2.1
                                  have p8681_3 := h8681c.2.2.2
                                  linarith only [h8556, hlam, p8681_1]
                                · have p8681_0 := h8681c.1
                                  have p8681_1 := h8681c.2.1
                                  have p8681_2 := h8681c.2.2.1
                                  have p8681_3 := h8681c.2.2.2
                                  linarith only [h0, h8188, h8672, h8674, h8677, h8678, h8680, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p8681_1]
                                · have p8681_0 := h8681c.1
                                  have p8681_1 := h8681c.2.1
                                  have p8681_2 := h8681c.2.2.1
                                  have p8681_3 := h8681c.2.2.2
                                  linarith only [h8188, h8674, h8678, h8680, hc03, hc45, hlam, hphi, ht0b, ht5b, p8681_1]
                                · have p8681_0 := h8681c.1
                                  have p8681_1 := h8681c.2.1
                                  have p8681_2 := h8681c.2.2.1
                                  have p8681_3 := h8681c.2.2.2
                                  linarith only [h8189, hc02, hc23, hlam, hphi, p8681_1]
                                · have p8681_0 := h8681c.1
                                  have p8681_1 := h8681c.2.1
                                  have p8681_2 := h8681c.2.2.1
                                  have p8681_3 := h8681c.2.2.2
                                  linarith only [hlam, p8681_0]
                                · have p8681_0 := h8681c.1
                                  have p8681_1 := h8681c.2.1
                                  have p8681_2 := h8681c.2.2.1
                                  have p8681_3 := h8681c.2.2.2
                                  linarith only [h0, h8188, h8189, h8556, h8674, h8678, h8680, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p8681_1]
                                · have p8681_0 := h8681c.1
                                  have p8681_1 := h8681c.2.1
                                  have p8681_2 := h8681c.2.2.1
                                  have p8681_3 := h8681c.2.2.2
                                  rcases p8681_3 (m.d 0 1) (by simp) with h8696 | h8696
                                  · linarith only [h6421, h8696, hlam]
                                  · linarith only [h8188, h8696, hlam]
                                · have p8681_0 := h8681c.1
                                  have p8681_1 := h8681c.2.1
                                  have p8681_2 := h8681c.2.2.1
                                  have p8681_3 := h8681c.2.2.2
                                  linarith only [h8188, h8674, h8678, h8680, hc04, hc45, hlam, hphi, ht0b, ht5b, p8681_1]
                                · have p8681_0 := h8681c.1
                                  have p8681_1 := h8681c.2.1
                                  have p8681_2 := h8681c.2.2.1
                                  have p8681_3 := h8681c.2.2.2
                                  linarith only [h0, h8188, h8674, h8678, h8680, hc04, hc45, hlam, hphi, ht0b, ht5b, p8681_1]
                                · have p8681_0 := h8681c.1
                                  have p8681_1 := h8681c.2.1
                                  have p8681_2 := h8681c.2.2.1
                                  have p8681_3 := h8681c.2.2.2
                                  linarith only [h8626, hlam, p8681_0]
                                · have p8681_0 := h8681c.1
                                  have p8681_1 := h8681c.2.1
                                  have p8681_2 := h8681c.2.2.1
                                  have p8681_3 := h8681c.2.2.2
                                  linarith only [hlam, p8681_0]
                                · have p8681_0 := h8681c.1
                                  have p8681_1 := h8681c.2.1
                                  have p8681_2 := h8681c.2.2.1
                                  have p8681_3 := h8681c.2.2.2
                                  rcases p8681_3 (m.d 0 1) (by simp) with h8703 | h8703
                                  · linarith only [h7464, h8703, hlam]
                                  · linarith only [h8188, h8703, hlam]
                                · have p8681_0 := h8681c.1
                                  have p8681_1 := h8681c.2.1
                                  have p8681_2 := h8681c.2.2.1
                                  have p8681_3 := h8681c.2.2.2
                                  linarith only [h8188, hlam, p8681_0]
                                · have p8681_0 := h8681c.1
                                  have p8681_1 := h8681c.2.1
                                  have p8681_2 := h8681c.2.2.1
                                  have p8681_3 := h8681c.2.2.2
                                  linarith only [h8625, hlam, p8681_1]
                                · have p8681_0 := h8681c.1
                                  have p8681_1 := h8681c.2.1
                                  have p8681_2 := h8681c.2.2.1
                                  have p8681_3 := h8681c.2.2.2
                                  linarith only [h8627, hlam, p8681_0]
                                · have p8681_0 := h8681c.1
                                  have p8681_1 := h8681c.2.1
                                  have p8681_2 := h8681c.2.2.1
                                  have p8681_3 := h8681c.2.2.2
                                  linarith only [h8628, hlam, p8681_1]
                                · have p8681_0 := h8681c.1
                                  have p8681_1 := h8681c.2.1
                                  have p8681_2 := h8681c.2.2.1
                                  have p8681_3 := h8681c.2.2.2
                                  linarith only [hlam, p8681_0]
                              · linarith only [h0, h8188, h8672, h8676, h8677, h8680, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                            · linarith only [h0, h8188, h8672, h8676, h8679, hlam]
                          · linarith only [h0, h8672, h8677, h8678, hc01, hc35, hlam, hphi, ht12, ht23]
                        · linarith only [h6421, h8626, h8629, h8677, hlam]
                      · linarith only [h7464, h8628, h8676, hlam]
                    · linarith only [h6421, h8626, h8675, hlam]
                  · linarith only [h0, h8188, h8625, h8674, hc02, hc15, hlam, hphi, ht0b, ht5b]
            · linarith only [h0, h8188, h8556, h8628, hlam]
          · linarith only [h0, h8188, h8556, h8626, h8627, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h8720 | h8720
          · rcases m.htr 0 4 5 (by decide) (by decide) with h8721 | h8721
            · rcases m.htr 1 2 3 (by decide) (by decide) with h8722 | h8722
              · rcases m.htr 1 2 4 (by decide) (by decide) with h8723 | h8723
                · rcases m.htr 1 2 5 (by decide) (by decide) with h8724 | h8724
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h8725 | h8725
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h8726 | h8726
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h8727 | h8727
                        · linarith only [h0, h8189, h8626, h8722, h8727, hc01, hc12, hlam, hphi]
                        · linarith only [h0, h8188, h8189, h8724, h8725, h8727, hc13, hc25, hlam, hphi, ht01, ht0b, ht5b]
                      · linarith only [h7464, h8188, h8721, h8724, h8726, hc04, hc25, hlam, hphi, ht0b, ht5b]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h8731 | h8731
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h8732 | h8732
                        · linarith only [h6421, h8188, h8724, h8725, h8732, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h8734 | h8734
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h8735 | h8735
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h8736 | h8736
                              · rcases h0bigk with h8737c | h8737c | h8737c | h8737c | h8737c | h8737c | h8737c | h8737c | h8737c | h8737c | h8737c | h8737c | h8737c | h8737c | h8737c | h8737c | h8737c | h8737c | h8737c | h8737c | h8737c | h8737c | h8737c | h8737c | h8737c
                                · have p8737_0 := h8737c.1
                                  have p8737_1 := h8737c.2.1
                                  have p8737_2 := h8737c.2.2.1
                                  have p8737_3 := h8737c.2.2.2
                                  linarith only [hlam, p8737_0]
                                · have p8737_0 := h8737c.1
                                  have p8737_1 := h8737c.2.1
                                  have p8737_2 := h8737c.2.2.1
                                  have p8737_3 := h8737c.2.2.2
                                  linarith only [h0, hlam, p8737_1]
                                · have p8737_0 := h8737c.1
                                  have p8737_1 := h8737c.2.1
                                  have p8737_2 := h8737c.2.2.1
                                  have p8737_3 := h8737c.2.2.2
                                  linarith only [h6421, hlam, p8737_0]
                                · have p8737_0 := h8737c.1
                                  have p8737_1 := h8737c.2.1
                                  have p8737_2 := h8737c.2.2.1
                                  have p8737_3 := h8737c.2.2.2
                                  linarith only [h7464, hlam, p8737_1]
                                · have p8737_0 := h8737c.1
                                  have p8737_1 := h8737c.2.1
                                  have p8737_2 := h8737c.2.2.1
                                  have p8737_3 := h8737c.2.2.2
                                  linarith only [h0, h8189, h8722, hc05, hc13, hlam, hphi, ht01, ht0b, ht5b, p8737_1]
                                · have p8737_0 := h8737c.1
                                  have p8737_1 := h8737c.2.1
                                  have p8737_2 := h8737c.2.2.1
                                  have p8737_3 := h8737c.2.2.2
                                  linarith only [h8189, h8722, hc01, hc13, hlam, hphi, p8737_1]
                                · have p8737_0 := h8737c.1
                                  have p8737_1 := h8737c.2.1
                                  have p8737_2 := h8737c.2.2.1
                                  have p8737_3 := h8737c.2.2.2
                                  linarith only [hlam, p8737_0]
                                · have p8737_0 := h8737c.1
                                  have p8737_1 := h8737c.2.1
                                  have p8737_2 := h8737c.2.2.1
                                  have p8737_3 := h8737c.2.2.2
                                  linarith only [h8189, hlam, p8737_0]
                                · have p8737_0 := h8737c.1
                                  have p8737_1 := h8737c.2.1
                                  have p8737_2 := h8737c.2.2.1
                                  have p8737_3 := h8737c.2.2.2
                                  linarith only [h8556, hlam, p8737_1]
                                · have p8737_0 := h8737c.1
                                  have p8737_1 := h8737c.2.1
                                  have p8737_2 := h8737c.2.2.1
                                  have p8737_3 := h8737c.2.2.2
                                  linarith only [h8188, h8189, h8722, h8724, h8725, h8734, h8736, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p8737_1]
                                · have p8737_0 := h8737c.1
                                  have p8737_1 := h8737c.2.1
                                  have p8737_2 := h8737c.2.2.1
                                  have p8737_3 := h8737c.2.2.2
                                  linarith only [h8188, h8724, h8734, h8736, hc03, hc45, hlam, hphi, ht0b, ht5b, p8737_1]
                                · have p8737_0 := h8737c.1
                                  have p8737_1 := h8737c.2.1
                                  have p8737_2 := h8737c.2.2.1
                                  have p8737_3 := h8737c.2.2.2
                                  linarith only [h8189, h8722, h8725, hc02, hc34, hlam, hphi, ht23, p8737_1]
                                · have p8737_0 := h8737c.1
                                  have p8737_1 := h8737c.2.1
                                  have p8737_2 := h8737c.2.2.1
                                  have p8737_3 := h8737c.2.2.2
                                  linarith only [hlam, p8737_0]
                                · have p8737_0 := h8737c.1
                                  have p8737_1 := h8737c.2.1
                                  have p8737_2 := h8737c.2.2.1
                                  have p8737_3 := h8737c.2.2.2
                                  linarith only [h8626, hlam, p8737_1]
                                · have p8737_0 := h8737c.1
                                  have p8737_1 := h8737c.2.1
                                  have p8737_2 := h8737c.2.2.1
                                  have p8737_3 := h8737c.2.2.2
                                  linarith only [h6421, h8188, h8724, h8725, h8734, h8736, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p8737_1]
                                · have p8737_0 := h8737c.1
                                  have p8737_1 := h8737c.2.1
                                  have p8737_2 := h8737c.2.2.1
                                  have p8737_3 := h8737c.2.2.2
                                  linarith only [h8188, h8724, h8734, h8736, hc04, hc45, hlam, hphi, ht0b, ht5b, p8737_1]
                                · have p8737_0 := h8737c.1
                                  have p8737_1 := h8737c.2.1
                                  have p8737_2 := h8737c.2.2.1
                                  have p8737_3 := h8737c.2.2.2
                                  linarith only [h0, h8188, h8556, h8723, h8724, h8734, h8736, hc14, hc45, hlam, hphi, ht01, ht0b, ht5b, p8737_1]
                                · have p8737_0 := h8737c.1
                                  have p8737_1 := h8737c.2.1
                                  have p8737_2 := h8737c.2.2.1
                                  have p8737_3 := h8737c.2.2.2
                                  linarith only [h8626, hc03, hc34, hlam, hphi, p8737_1]
                                · have p8737_0 := h8737c.1
                                  have p8737_1 := h8737c.2.1
                                  have p8737_2 := h8737c.2.2.1
                                  have p8737_3 := h8737c.2.2.2
                                  linarith only [hlam, p8737_0]
                                · have p8737_0 := h8737c.1
                                  have p8737_1 := h8737c.2.1
                                  have p8737_2 := h8737c.2.2.1
                                  have p8737_3 := h8737c.2.2.2
                                  linarith only [h8188, h8556, h8723, h8724, h8734, h8736, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p8737_1]
                                · have p8737_0 := h8737c.1
                                  have p8737_1 := h8737c.2.1
                                  have p8737_2 := h8737c.2.2.1
                                  have p8737_3 := h8737c.2.2.2
                                  linarith only [h8188, hlam, p8737_0]
                                · have p8737_0 := h8737c.1
                                  have p8737_1 := h8737c.2.1
                                  have p8737_2 := h8737c.2.2.1
                                  have p8737_3 := h8737c.2.2.2
                                  linarith only [h8625, hlam, p8737_1]
                                · have p8737_0 := h8737c.1
                                  have p8737_1 := h8737c.2.1
                                  have p8737_2 := h8737c.2.2.1
                                  have p8737_3 := h8737c.2.2.2
                                  linarith only [h8720, hlam, p8737_0]
                                · have p8737_0 := h8737c.1
                                  have p8737_1 := h8737c.2.1
                                  have p8737_2 := h8737c.2.2.1
                                  have p8737_3 := h8737c.2.2.2
                                  linarith only [h8721, hlam, p8737_1]
                                · have p8737_0 := h8737c.1
                                  have p8737_1 := h8737c.2.1
                                  have p8737_2 := h8737c.2.2.1
                                  have p8737_3 := h8737c.2.2.2
                                  linarith only [hlam, p8737_0]
                              · linarith only [h6421, h8725, h8736, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                            · linarith only [h0, h8188, h8189, h8731, h8732, h8735, hlam]
                          · linarith only [h0, h8188, h8189, h8720, h8724, h8734, hc03, hc25, hlam, hphi, ht0b, ht5b]
                      · linarith only [h7464, h8721, h8731, hlam]
                  · linarith only [h0, h8188, h8625, h8724, hc02, hc15, hlam, hphi, ht0b, ht5b]
                · linarith only [h8189, h8722, h8723, hc02, hc24, hlam, hphi]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h8769 | h8769
                · linarith only [h0, h8188, h8556, h8722, h8769, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h8771 | h8771
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h8772 | h8772
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h8773 | h8773
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h8774 | h8774
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h8775 | h8775
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h8776 | h8776
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h8777 | h8777
                              · rcases h0bigk with h8778c | h8778c | h8778c | h8778c | h8778c | h8778c | h8778c | h8778c | h8778c | h8778c | h8778c | h8778c | h8778c | h8778c | h8778c | h8778c | h8778c | h8778c | h8778c | h8778c | h8778c | h8778c | h8778c | h8778c | h8778c
                                · have p8778_0 := h8778c.1
                                  have p8778_1 := h8778c.2.1
                                  have p8778_2 := h8778c.2.2.1
                                  have p8778_3 := h8778c.2.2.2
                                  linarith only [hlam, p8778_0]
                                · have p8778_0 := h8778c.1
                                  have p8778_1 := h8778c.2.1
                                  have p8778_2 := h8778c.2.2.1
                                  have p8778_3 := h8778c.2.2.2
                                  linarith only [h0, hlam, p8778_1]
                                · have p8778_0 := h8778c.1
                                  have p8778_1 := h8778c.2.1
                                  have p8778_2 := h8778c.2.2.1
                                  have p8778_3 := h8778c.2.2.2
                                  linarith only [h6421, hlam, p8778_0]
                                · have p8778_0 := h8778c.1
                                  have p8778_1 := h8778c.2.1
                                  have p8778_2 := h8778c.2.2.1
                                  have p8778_3 := h8778c.2.2.2
                                  linarith only [h7464, hlam, p8778_1]
                                · have p8778_0 := h8778c.1
                                  have p8778_1 := h8778c.2.1
                                  have p8778_2 := h8778c.2.2.1
                                  have p8778_3 := h8778c.2.2.2
                                  linarith only [h0, h8189, h8626, h8772, hc05, hc13, hlam, hphi, ht01, ht0b, ht5b, p8778_1]
                                · have p8778_0 := h8778c.1
                                  have p8778_1 := h8778c.2.1
                                  have p8778_2 := h8778c.2.2.1
                                  have p8778_3 := h8778c.2.2.2
                                  linarith only [h8189, h8626, h8772, hc01, hc13, hlam, hphi, p8778_1]
                                · have p8778_0 := h8778c.1
                                  have p8778_1 := h8778c.2.1
                                  have p8778_2 := h8778c.2.2.1
                                  have p8778_3 := h8778c.2.2.2
                                  linarith only [hlam, p8778_0]
                                · have p8778_0 := h8778c.1
                                  have p8778_1 := h8778c.2.1
                                  have p8778_2 := h8778c.2.2.1
                                  have p8778_3 := h8778c.2.2.2
                                  linarith only [h8189, hlam, p8778_0]
                                · have p8778_0 := h8778c.1
                                  have p8778_1 := h8778c.2.1
                                  have p8778_2 := h8778c.2.2.1
                                  have p8778_3 := h8778c.2.2.2
                                  linarith only [h8556, hlam, p8778_1]
                                · have p8778_0 := h8778c.1
                                  have p8778_1 := h8778c.2.1
                                  have p8778_2 := h8778c.2.2.1
                                  have p8778_3 := h8778c.2.2.2
                                  linarith only [h8188, h8189, h8626, h8771, h8772, h8775, h8777, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p8778_1]
                                · have p8778_0 := h8778c.1
                                  have p8778_1 := h8778c.2.1
                                  have p8778_2 := h8778c.2.2.1
                                  have p8778_3 := h8778c.2.2.2
                                  linarith only [h8188, h8626, h8771, h8772, h8775, h8777, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p8778_1]
                                · have p8778_0 := h8778c.1
                                  have p8778_1 := h8778c.2.1
                                  have p8778_2 := h8778c.2.2.1
                                  have p8778_3 := h8778c.2.2.2
                                  linarith only [h8626, h8772, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p8778_1]
                                · have p8778_0 := h8778c.1
                                  have p8778_1 := h8778c.2.1
                                  have p8778_2 := h8778c.2.2.1
                                  have p8778_3 := h8778c.2.2.2
                                  linarith only [hlam, p8778_0]
                                · have p8778_0 := h8778c.1
                                  have p8778_1 := h8778c.2.1
                                  have p8778_2 := h8778c.2.2.1
                                  have p8778_3 := h8778c.2.2.2
                                  linarith only [h8626, hlam, p8778_1]
                                · have p8778_0 := h8778c.1
                                  have p8778_1 := h8778c.2.1
                                  have p8778_2 := h8778c.2.2.1
                                  have p8778_3 := h8778c.2.2.2
                                  linarith only [h8188, h8626, h8771, h8772, h8775, h8777, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p8778_1]
                                · have p8778_0 := h8778c.1
                                  have p8778_1 := h8778c.2.1
                                  have p8778_2 := h8778c.2.2.1
                                  have p8778_3 := h8778c.2.2.2
                                  linarith only [h8188, h8771, h8775, h8777, hc04, hc45, hlam, hphi, ht0b, ht5b, p8778_1]
                                · have p8778_0 := h8778c.1
                                  have p8778_1 := h8778c.2.1
                                  have p8778_2 := h8778c.2.2.1
                                  have p8778_3 := h8778c.2.2.2
                                  linarith only [h0, h8188, h8556, h8771, h8774, h8775, h8777, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p8778_1]
                                · have p8778_0 := h8778c.1
                                  have p8778_1 := h8778c.2.1
                                  have p8778_2 := h8778c.2.2.1
                                  have p8778_3 := h8778c.2.2.2
                                  linarith only [h8626, h8772, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8778_1]
                                · have p8778_0 := h8778c.1
                                  have p8778_1 := h8778c.2.1
                                  have p8778_2 := h8778c.2.2.1
                                  have p8778_3 := h8778c.2.2.2
                                  linarith only [hlam, p8778_0]
                                · have p8778_0 := h8778c.1
                                  have p8778_1 := h8778c.2.1
                                  have p8778_2 := h8778c.2.2.1
                                  have p8778_3 := h8778c.2.2.2
                                  linarith only [h8188, h8626, h8771, h8772, h8775, h8777, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p8778_1]
                                · have p8778_0 := h8778c.1
                                  have p8778_1 := h8778c.2.1
                                  have p8778_2 := h8778c.2.2.1
                                  have p8778_3 := h8778c.2.2.2
                                  linarith only [h8188, hlam, p8778_0]
                                · have p8778_0 := h8778c.1
                                  have p8778_1 := h8778c.2.1
                                  have p8778_2 := h8778c.2.2.1
                                  have p8778_3 := h8778c.2.2.2
                                  linarith only [h8625, hlam, p8778_1]
                                · have p8778_0 := h8778c.1
                                  have p8778_1 := h8778c.2.1
                                  have p8778_2 := h8778c.2.2.1
                                  have p8778_3 := h8778c.2.2.2
                                  linarith only [h8720, hlam, p8778_0]
                                · have p8778_0 := h8778c.1
                                  have p8778_1 := h8778c.2.1
                                  have p8778_2 := h8778c.2.2.1
                                  have p8778_3 := h8778c.2.2.2
                                  linarith only [h8721, hlam, p8778_1]
                                · have p8778_0 := h8778c.1
                                  have p8778_1 := h8778c.2.1
                                  have p8778_2 := h8778c.2.2.1
                                  have p8778_3 := h8778c.2.2.2
                                  linarith only [hlam, p8778_0]
                              · linarith only [h0, h8188, h8189, h8626, h8721, h8771, h8775, h8777, hc04, hc35, hlam, hphi, ht0b, ht5b]
                            · linarith only [h7464, h8188, h8769, h8773, h8776, hlam]
                          · linarith only [h0, h8189, h8626, h8722, h8772, h8775, hc01, hc35, hlam, hphi, ht12, ht23]
                        · linarith only [h8722, h8772, h8774, hlam]
                      · linarith only [h8626, h8721, h8772, h8773, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h8809 | h8809
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h8810 | h8810
                        · linarith only [h0, h8188, h8722, h8771, h8772, h8810, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
                        · linarith only [h0, h8188, h8722, h8771, h8810, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                      · linarith only [h7464, h8721, h8809, hlam]
                  · linarith only [h0, h8188, h8189, h8625, h8771, hc03, hc15, hlam, hphi, ht0b, ht5b]
            · linarith only [h0, h8188, h8189, h8626, h8721, hlam]
          · linarith only [h0, h8188, h8189, h8720, hlam]
      · linarith only [h0, h8188, h8625, hlam]

end R2N4
