import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_9S13
import Jsp000404.R1LeavesN7_9S25
import Jsp000404.R1LeavesN7_9S26

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 16646000 in
set_option maxHeartbeats 16646000 in
theorem r1l7_13_24_L_I_H_I_s8_x0_x1 (m : N7Model)
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h7360 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h7361 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
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
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  have h0 := hg0
  rcases m.htr 0 1 5 (by decide) (by decide) with h8130 | h8130
  · rcases m.htr 0 2 3 (by decide) (by decide) with h8131 | h8131
    · rcases m.htr 0 2 4 (by decide) (by decide) with h8132 | h8132
      · rcases m.htr 0 3 4 (by decide) (by decide) with h8133 | h8133
        · linarith only [h7360, h7361, h8133, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h8135 | h8135
          · rcases m.htr 0 4 5 (by decide) (by decide) with h8136 | h8136
            · rcases m.htr 1 2 3 (by decide) (by decide) with h8137 | h8137
              · rcases m.htr 1 2 4 (by decide) (by decide) with h8138 | h8138
                · rcases m.htr 1 3 4 (by decide) (by decide) with h8139 | h8139
                  · linarith only [h7360, h7361, h8133, h8138, h8139, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h8141 | h8141
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h8142 | h8142
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h8143 | h8143
                        · linarith only [h7360, h7361, h8137, h8139, h8143, hlam]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h8145 | h8145
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h8146 | h8146
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h8147 | h8147
                              · rcases h3bigk with h8148c | h8148c | h8148c | h8148c | h8148c | h8148c | h8148c | h8148c | h8148c | h8148c | h8148c | h8148c | h8148c | h8148c | h8148c | h8148c | h8148c | h8148c | h8148c | h8148c | h8148c | h8148c | h8148c | h8148c | h8148c
                                · have p8148_0 := h8148c.1
                                  have p8148_1 := h8148c.2.1
                                  have p8148_2 := h8148c.2.2.1
                                  have p8148_3 := h8148c.2.2.2
                                  linarith only [hlam, p8148_0]
                                · have p8148_0 := h8148c.1
                                  have p8148_1 := h8148c.2.1
                                  have p8148_2 := h8148c.2.2.1
                                  have p8148_3 := h8148c.2.2.2
                                  linarith only [h7360, h7361, h8139, hc13, hc34, hlam, hphi, p8148_1]
                                · have p8148_0 := h8148c.1
                                  have p8148_1 := h8148c.2.1
                                  have p8148_2 := h8148c.2.2.1
                                  have p8148_3 := h8148c.2.2.2
                                  linarith only [h7360, h7361, h8139, h8145, h8147, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p8148_1]
                                · have p8148_0 := h8148c.1
                                  have p8148_1 := h8148c.2.1
                                  have p8148_2 := h8148c.2.2.1
                                  have p8148_3 := h8148c.2.2.2
                                  linarith only [h8133, hlam, p8148_0]
                                · have p8148_0 := h8148c.1
                                  have p8148_1 := h8148c.2.1
                                  have p8148_2 := h8148c.2.2.1
                                  have p8148_3 := h8148c.2.2.2
                                  rcases p8148_3 (m.d 0 3) (by simp) with h8153 | h8153
                                  · rcases p8148_3 (m.d 1 3) (by simp) with h8154 | h8154
                                    · linarith only [h7360, h8154, hlam]
                                    · linarith only [h8141, h8154, hlam]
                                  · linarith only [h8153, hlam, p8148_0]
                                · have p8148_0 := h8148c.1
                                  have p8148_1 := h8148c.2.1
                                  have p8148_2 := h8148c.2.2.1
                                  have p8148_3 := h8148c.2.2.2
                                  linarith only [h7360, hlam, p8148_0]
                                · have p8148_0 := h8148c.1
                                  have p8148_1 := h8148c.2.1
                                  have p8148_2 := h8148c.2.2.1
                                  have p8148_3 := h8148c.2.2.2
                                  linarith only [hlam, p8148_0]
                                · have p8148_0 := h8148c.1
                                  have p8148_1 := h8148c.2.1
                                  have p8148_2 := h8148c.2.2.1
                                  have p8148_3 := h8148c.2.2.2
                                  linarith only [h7360, h7361, h8139, h8145, h8147, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p8148_1]
                                · have p8148_0 := h8148c.1
                                  have p8148_1 := h8148c.2.1
                                  have p8148_2 := h8148c.2.2.1
                                  have p8148_3 := h8148c.2.2.2
                                  linarith only [h8139, hlam, p8148_0]
                                · have p8148_0 := h8148c.1
                                  have p8148_1 := h8148c.2.1
                                  have p8148_2 := h8148c.2.2.1
                                  have p8148_3 := h8148c.2.2.2
                                  linarith only [h7360, h7361, h8139, h8147, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p8148_1]
                                · have p8148_0 := h8148c.1
                                  have p8148_1 := h8148c.2.1
                                  have p8148_2 := h8148c.2.2.1
                                  have p8148_3 := h8148c.2.2.2
                                  linarith only [h8131, hlam, p8148_0]
                                · have p8148_0 := h8148c.1
                                  have p8148_1 := h8148c.2.1
                                  have p8148_2 := h8148c.2.2.1
                                  have p8148_3 := h8148c.2.2.2
                                  linarith only [h8137, hlam, p8148_0]
                                · have p8148_0 := h8148c.1
                                  have p8148_1 := h8148c.2.1
                                  have p8148_2 := h8148c.2.2.1
                                  have p8148_3 := h8148c.2.2.2
                                  linarith only [hlam, p8148_0]
                                · have p8148_0 := h8148c.1
                                  have p8148_1 := h8148c.2.1
                                  have p8148_2 := h8148c.2.2.1
                                  have p8148_3 := h8148c.2.2.2
                                  linarith only [h8143, hlam, p8148_0]
                                · have p8148_0 := h8148c.1
                                  have p8148_1 := h8148c.2.1
                                  have p8148_2 := h8148c.2.2.1
                                  have p8148_3 := h8148c.2.2.2
                                  linarith only [h7360, h7361, h8137, h8139, h8147, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p8148_1]
                                · have p8148_0 := h8148c.1
                                  have p8148_1 := h8148c.2.1
                                  have p8148_2 := h8148c.2.2.1
                                  have p8148_3 := h8148c.2.2.2
                                  rcases p8148_3 (m.d 0 3) (by simp) with h8168 | h8168
                                  · linarith only [h8168, hlam, p8148_0]
                                  · rcases p8148_3 (m.d 1 3) (by simp) with h8170 | h8170
                                    · linarith only [h8139, h8170, hlam]
                                    · rcases p8148_3 (m.d 2 3) (by simp) with h8172 | h8172
                                      · linarith only [h8143, h8172, hlam]
                                      · rcases p8148_3 (m.d 3 4) (by simp) with h8174 | h8174
                                        · rcases p8148_3 (m.d 3 5) (by simp) with h8175 | h8175
                                          · linarith only [h8147, h8175, hlam]
                                          · rcases h4bigk with h8177c | h8177c | h8177c | h8177c | h8177c | h8177c | h8177c | h8177c | h8177c | h8177c | h8177c | h8177c | h8177c | h8177c | h8177c | h8177c | h8177c | h8177c | h8177c | h8177c | h8177c | h8177c | h8177c | h8177c | h8177c
                                            · have p8177_0 := h8177c.1
                                              have p8177_1 := h8177c.2.1
                                              have p8177_2 := h8177c.2.2.1
                                              have p8177_3 := h8177c.2.2.2
                                              linarith only [hlam, p8177_0]
                                            · have p8177_0 := h8177c.1
                                              have p8177_1 := h8177c.2.1
                                              have p8177_2 := h8177c.2.2.1
                                              have p8177_3 := h8177c.2.2.2
                                              linarith only [h7361, hlam, p8177_0]
                                            · have p8177_0 := h8177c.1
                                              have p8177_1 := h8177c.2.1
                                              have p8177_2 := h8177c.2.2.1
                                              have p8177_3 := h8177c.2.2.2
                                              linarith only [h7361, h8139, h8143, hc23, hc34, hlam, hphi, p8177_1]
                                            · have p8177_0 := h8177c.1
                                              have p8177_1 := h8177c.2.1
                                              have p8177_2 := h8177c.2.2.1
                                              have p8177_3 := h8177c.2.2.2
                                              linarith only [h8133, hlam, p8177_0]
                                            · have p8177_0 := h8177c.1
                                              have p8177_1 := h8177c.2.1
                                              have p8177_2 := h8177c.2.2.1
                                              have p8177_3 := h8177c.2.2.2
                                              rcases p8177_3 (m.d 0 4) (by simp) with h8182 | h8182
                                              · rcases p8177_3 (m.d 1 4) (by simp) with h8183 | h8183
                                                · rcases p8177_3 (m.d 2 4) (by simp) with h8184 | h8184
                                                  · linarith only [h8132, h8184, hlam]
                                                  · linarith only [h8146, h8184, hlam]
                                                · linarith only [h8142, h8183, hlam]
                                              · linarith only [h8182, hlam, p8177_0]
                                            · have p8177_0 := h8177c.1
                                              have p8177_1 := h8177c.2.1
                                              have p8177_2 := h8177c.2.2.1
                                              have p8177_3 := h8177c.2.2.2
                                              linarith only [h7360, h7361, h8137, h8139, h8145, h8147, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p8177_1]
                                            · have p8177_0 := h8177c.1
                                              have p8177_1 := h8177c.2.1
                                              have p8177_2 := h8177c.2.2.1
                                              have p8177_3 := h8177c.2.2.2
                                              linarith only [hlam, p8177_0]
                                            · have p8177_0 := h8177c.1
                                              have p8177_1 := h8177c.2.1
                                              have p8177_2 := h8177c.2.2.1
                                              have p8177_3 := h8177c.2.2.2
                                              linarith only [h8139, h8143, h8145, h8147, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p8177_1]
                                            · have p8177_0 := h8177c.1
                                              have p8177_1 := h8177c.2.1
                                              have p8177_2 := h8177c.2.2.1
                                              have p8177_3 := h8177c.2.2.2
                                              linarith only [h8139, hlam, p8177_1]
                                            · have p8177_0 := h8177c.1
                                              have p8177_1 := h8177c.2.1
                                              have p8177_2 := h8177c.2.2.1
                                              have p8177_3 := h8177c.2.2.2
                                              rcases p8177_3 (m.d 0 4) (by simp) with h8193 | h8193
                                              · linarith only [h7361, h8193, hlam]
                                              · linarith only [h8136, h8193, hlam]
                                            · have p8177_0 := h8177c.1
                                              have p8177_1 := h8177c.2.1
                                              have p8177_2 := h8177c.2.2.1
                                              have p8177_3 := h8177c.2.2.2
                                              linarith only [h8132, hlam, p8177_1]
                                            · have p8177_0 := h8177c.1
                                              have p8177_1 := h8177c.2.1
                                              have p8177_2 := h8177c.2.2.1
                                              have p8177_3 := h8177c.2.2.2
                                              linarith only [h8138, hlam, p8177_1]
                                            · have p8177_0 := h8177c.1
                                              have p8177_1 := h8177c.2.1
                                              have p8177_2 := h8177c.2.2.1
                                              have p8177_3 := h8177c.2.2.2
                                              linarith only [hlam, p8177_0]
                                            · have p8177_0 := h8177c.1
                                              have p8177_1 := h8177c.2.1
                                              have p8177_2 := h8177c.2.2.1
                                              have p8177_3 := h8177c.2.2.2
                                              linarith only [h8143, hlam, p8177_1]
                                            · have p8177_0 := h8177c.1
                                              have p8177_1 := h8177c.2.1
                                              have p8177_2 := h8177c.2.2.1
                                              have p8177_3 := h8177c.2.2.2
                                              linarith only [h8132, hc02, hc45, hlam, hphi, ht0b, ht5b, p8177_1]
                                            · have p8177_0 := h8177c.1
                                              have p8177_1 := h8177c.2.1
                                              have p8177_2 := h8177c.2.2.1
                                              have p8177_3 := h8177c.2.2.2
                                              linarith only [h7360, h7361, h8137, h8145, h8147, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p8177_1]
                                            · have p8177_0 := h8177c.1
                                              have p8177_1 := h8177c.2.1
                                              have p8177_2 := h8177c.2.2.1
                                              have p8177_3 := h8177c.2.2.2
                                              linarith only [h7360, h7361, h8137, h8145, h8147, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p8177_1]
                                            · have p8177_0 := h8177c.1
                                              have p8177_1 := h8177c.2.1
                                              have p8177_2 := h8177c.2.2.1
                                              have p8177_3 := h8177c.2.2.2
                                              linarith only [h8143, h8145, h8147, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p8177_1]
                                            · have p8177_0 := h8177c.1
                                              have p8177_1 := h8177c.2.1
                                              have p8177_2 := h8177c.2.2.1
                                              have p8177_3 := h8177c.2.2.2
                                              linarith only [hlam, p8177_0]
                                            · have p8177_0 := h8177c.1
                                              have p8177_1 := h8177c.2.1
                                              have p8177_2 := h8177c.2.2.1
                                              have p8177_3 := h8177c.2.2.2
                                              rcases p8177_3 (m.d 0 4) (by simp) with h8205 | h8205
                                              · linarith only [h8133, h8205, hlam]
                                              · linarith only [h8136, h8205, hlam]
                                            · have p8177_0 := h8177c.1
                                              have p8177_1 := h8177c.2.1
                                              have p8177_2 := h8177c.2.2.1
                                              have p8177_3 := h8177c.2.2.2
                                              linarith only [h8136, hlam, p8177_0]
                                            · have p8177_0 := h8177c.1
                                              have p8177_1 := h8177c.2.1
                                              have p8177_2 := h8177c.2.2.1
                                              have p8177_3 := h8177c.2.2.2
                                              linarith only [h8142, hlam, p8177_0]
                                            · have p8177_0 := h8177c.1
                                              have p8177_1 := h8177c.2.1
                                              have p8177_2 := h8177c.2.2.1
                                              have p8177_3 := h8177c.2.2.2
                                              linarith only [h8146, hlam, p8177_0]
                                            · have p8177_0 := h8177c.1
                                              have p8177_1 := h8177c.2.1
                                              have p8177_2 := h8177c.2.2.1
                                              have p8177_3 := h8177c.2.2.2
                                              linarith only [h8147, hlam, p8177_0]
                                            · have p8177_0 := h8177c.1
                                              have p8177_1 := h8177c.2.1
                                              have p8177_2 := h8177c.2.2.1
                                              have p8177_3 := h8177c.2.2.2
                                              linarith only [hlam, p8177_0]
                                        · linarith only [h8174, hlam, p8148_0]
                                · have p8148_0 := h8148c.1
                                  have p8148_1 := h8148c.2.1
                                  have p8148_2 := h8148c.2.2.1
                                  have p8148_3 := h8148c.2.2.2
                                  rcases p8148_3 (m.d 0 3) (by simp) with h8214 | h8214
                                  · linarith only [h8133, h8214, hlam]
                                  · linarith only [h7360, h8214, hlam]
                                · have p8148_0 := h8148c.1
                                  have p8148_1 := h8148c.2.1
                                  have p8148_2 := h8148c.2.2.1
                                  have p8148_3 := h8148c.2.2.2
                                  rcases p8148_3 (m.d 0 3) (by simp) with h8217 | h8217
                                  · linarith only [h8133, h8217, hlam]
                                  · linarith only [h8131, h8217, hlam]
                                · have p8148_0 := h8148c.1
                                  have p8148_1 := h8148c.2.1
                                  have p8148_2 := h8148c.2.2.1
                                  have p8148_3 := h8148c.2.2.2
                                  linarith only [hlam, p8148_0]
                                · have p8148_0 := h8148c.1
                                  have p8148_1 := h8148c.2.1
                                  have p8148_2 := h8148c.2.2.1
                                  have p8148_3 := h8148c.2.2.2
                                  linarith only [h7360, h7361, h8137, h8139, h8145, hlam, p8148_2]
                                · have p8148_0 := h8148c.1
                                  have p8148_1 := h8148c.2.1
                                  have p8148_2 := h8148c.2.2.1
                                  have p8148_3 := h8148c.2.2.2
                                  linarith only [h8135, hlam, p8148_0]
                                · have p8148_0 := h8148c.1
                                  have p8148_1 := h8148c.2.1
                                  have p8148_2 := h8148c.2.2.1
                                  have p8148_3 := h8148c.2.2.2
                                  linarith only [h8141, hlam, p8148_0]
                                · have p8148_0 := h8148c.1
                                  have p8148_1 := h8148c.2.1
                                  have p8148_2 := h8148c.2.2.1
                                  have p8148_3 := h8148c.2.2.2
                                  linarith only [h8145, hlam, p8148_0]
                                · have p8148_0 := h8148c.1
                                  have p8148_1 := h8148c.2.1
                                  have p8148_2 := h8148c.2.2.1
                                  have p8148_3 := h8148c.2.2.2
                                  linarith only [h8147, hlam, p8148_0]
                                · have p8148_0 := h8148c.1
                                  have p8148_1 := h8148c.2.1
                                  have p8148_2 := h8148c.2.2.1
                                  have p8148_3 := h8148c.2.2.2
                                  linarith only [hlam, p8148_0]
                              · linarith only [h7360, h7361, h8139, h8147, hc13, hc45, hlam, hphi, ht34]
                            · linarith only [h7360, h7361, h8141, h8142, h8143, h8145, h8146, hc14, hc35, hlam, hphi, ht01, ht0b, ht5b]
                          · linarith only [h7360, h7361, h8135, h8139, h8145, hc23, hc34, hlam, hphi]
                      · linarith only [h7360, h7361, h8142, hc13, hc45, hlam, hphi, ht34]
                    · linarith only [h7360, h7361, h8135, h8139, h8141, hc13, hc34, hlam, hphi]
                · linarith only [h0, h8132, h8138, hlam]
              · linarith only [h0, h8131, h8137, hlam]
            · linarith only [h7360, h7361, h8135, h8136, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h8235 | h8235
            · rcases m.htr 1 2 3 (by decide) (by decide) with h8236 | h8236
              · rcases m.htr 1 2 4 (by decide) (by decide) with h8237 | h8237
                · rcases m.htr 1 3 4 (by decide) (by decide) with h8238 | h8238
                  · linarith only [h7360, h7361, h8133, h8237, h8238, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h8240 | h8240
                    · linarith only [h7360, h8135, h8240, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h8242 | h8242
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h8243 | h8243
                        · linarith only [h7360, h7361, h8135, h8236, h8238, h8243, hc01, hc35, hlam, hphi, ht12, ht23]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h8245 | h8245
                          · linarith only [h7361, h8130, h8135, h8236, h8240, h8245, hc03, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h8247 | h8247
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h8248 | h8248
                              · rcases h3bigk with h8249c | h8249c | h8249c | h8249c | h8249c | h8249c | h8249c | h8249c | h8249c | h8249c | h8249c | h8249c | h8249c | h8249c | h8249c | h8249c | h8249c | h8249c | h8249c | h8249c | h8249c | h8249c | h8249c | h8249c | h8249c
                                · have p8249_0 := h8249c.1
                                  have p8249_1 := h8249c.2.1
                                  have p8249_2 := h8249c.2.2.1
                                  have p8249_3 := h8249c.2.2.2
                                  linarith only [hlam, p8249_0]
                                · have p8249_0 := h8249c.1
                                  have p8249_1 := h8249c.2.1
                                  have p8249_2 := h8249c.2.2.1
                                  have p8249_3 := h8249c.2.2.2
                                  linarith only [h8135, hc13, hc35, hlam, hphi, p8249_1]
                                · have p8249_0 := h8249c.1
                                  have p8249_1 := h8249c.2.1
                                  have p8249_2 := h8249c.2.2.1
                                  have p8249_3 := h8249c.2.2.2
                                  linarith only [h7360, h7361, h8238, hc23, hc34, hlam, hphi, p8249_1]
                                · have p8249_0 := h8249c.1
                                  have p8249_1 := h8249c.2.1
                                  have p8249_2 := h8249c.2.2.1
                                  have p8249_3 := h8249c.2.2.2
                                  linarith only [h8133, hlam, p8249_0]
                                · have p8249_0 := h8249c.1
                                  have p8249_1 := h8249c.2.1
                                  have p8249_2 := h8249c.2.2.1
                                  have p8249_3 := h8249c.2.2.2
                                  linarith only [h8135, hlam, p8249_0]
                                · have p8249_0 := h8249c.1
                                  have p8249_1 := h8249c.2.1
                                  have p8249_2 := h8249c.2.2.1
                                  have p8249_3 := h8249c.2.2.2
                                  linarith only [h7360, hlam, p8249_0]
                                · have p8249_0 := h8249c.1
                                  have p8249_1 := h8249c.2.1
                                  have p8249_2 := h8249c.2.2.1
                                  have p8249_3 := h8249c.2.2.2
                                  linarith only [hlam, p8249_0]
                                · have p8249_0 := h8249c.1
                                  have p8249_1 := h8249c.2.1
                                  have p8249_2 := h8249c.2.2.1
                                  have p8249_3 := h8249c.2.2.2
                                  linarith only [h7360, h7361, h8238, hc23, hc34, hlam, hphi, p8249_1]
                                · have p8249_0 := h8249c.1
                                  have p8249_1 := h8249c.2.1
                                  have p8249_2 := h8249c.2.2.1
                                  have p8249_3 := h8249c.2.2.2
                                  linarith only [h8238, hlam, p8249_0]
                                · have p8249_0 := h8249c.1
                                  have p8249_1 := h8249c.2.1
                                  have p8249_2 := h8249c.2.2.1
                                  have p8249_3 := h8249c.2.2.2
                                  linarith only [h8240, hlam, p8249_0]
                                · have p8249_0 := h8249c.1
                                  have p8249_1 := h8249c.2.1
                                  have p8249_2 := h8249c.2.2.1
                                  have p8249_3 := h8249c.2.2.2
                                  linarith only [h8131, hlam, p8249_0]
                                · have p8249_0 := h8249c.1
                                  have p8249_1 := h8249c.2.1
                                  have p8249_2 := h8249c.2.2.1
                                  have p8249_3 := h8249c.2.2.2
                                  linarith only [h8236, hlam, p8249_0]
                                · have p8249_0 := h8249c.1
                                  have p8249_1 := h8249c.2.1
                                  have p8249_2 := h8249c.2.2.1
                                  have p8249_3 := h8249c.2.2.2
                                  linarith only [hlam, p8249_0]
                                · have p8249_0 := h8249c.1
                                  have p8249_1 := h8249c.2.1
                                  have p8249_2 := h8249c.2.2.1
                                  have p8249_3 := h8249c.2.2.2
                                  linarith only [h8243, hlam, p8249_0]
                                · have p8249_0 := h8249c.1
                                  have p8249_1 := h8249c.2.1
                                  have p8249_2 := h8249c.2.2.1
                                  have p8249_3 := h8249c.2.2.2
                                  linarith only [h8245, hlam, p8249_0]
                                · have p8249_0 := h8249c.1
                                  have p8249_1 := h8249c.2.1
                                  have p8249_2 := h8249c.2.2.1
                                  have p8249_3 := h8249c.2.2.2
                                  rcases p8249_3 (m.d 0 3) (by simp) with h8265 | h8265
                                  · linarith only [h8265, hlam, p8249_0]
                                  · rcases p8249_3 (m.d 1 3) (by simp) with h8267 | h8267
                                    · linarith only [h8238, h8267, hlam]
                                    · rcases p8249_3 (m.d 2 3) (by simp) with h8269 | h8269
                                      · linarith only [h8243, h8269, hlam]
                                      · rcases p8249_3 (m.d 3 4) (by simp) with h8271 | h8271
                                        · rcases p8249_3 (m.d 3 5) (by simp) with h8272 | h8272
                                          · linarith only [h8248, h8272, hlam]
                                          · linarith only [h8135, h8272, hlam]
                                        · linarith only [h8271, hlam, p8249_0]
                                · have p8249_0 := h8249c.1
                                  have p8249_1 := h8249c.2.1
                                  have p8249_2 := h8249c.2.2.1
                                  have p8249_3 := h8249c.2.2.2
                                  rcases p8249_3 (m.d 0 3) (by simp) with h8276 | h8276
                                  · linarith only [h8133, h8276, hlam]
                                  · linarith only [h7360, h8276, hlam]
                                · have p8249_0 := h8249c.1
                                  have p8249_1 := h8249c.2.1
                                  have p8249_2 := h8249c.2.2.1
                                  have p8249_3 := h8249c.2.2.2
                                  rcases p8249_3 (m.d 0 3) (by simp) with h8279 | h8279
                                  · linarith only [h8133, h8279, hlam]
                                  · linarith only [h8131, h8279, hlam]
                                · have p8249_0 := h8249c.1
                                  have p8249_1 := h8249c.2.1
                                  have p8249_2 := h8249c.2.2.1
                                  have p8249_3 := h8249c.2.2.2
                                  linarith only [hlam, p8249_0]
                                · have p8249_0 := h8249c.1
                                  have p8249_1 := h8249c.2.1
                                  have p8249_2 := h8249c.2.2.1
                                  have p8249_3 := h8249c.2.2.2
                                  linarith only [h8135, hc03, hc34, hlam, hphi, p8249_1]
                                · have p8249_0 := h8249c.1
                                  have p8249_1 := h8249c.2.1
                                  have p8249_2 := h8249c.2.2.1
                                  have p8249_3 := h8249c.2.2.2
                                  rcases p8249_3 (m.d 0 3) (by simp) with h8284 | h8284
                                  · linarith only [h8284, hlam, p8249_0]
                                  · rcases p8249_3 (m.d 1 3) (by simp) with h8286 | h8286
                                    · linarith only [h8240, h8286, hlam]
                                    · rcases p8249_3 (m.d 2 3) (by simp) with h8288 | h8288
                                      · linarith only [h8245, h8288, hlam]
                                      · rcases p8249_3 (m.d 3 4) (by simp) with h8290 | h8290
                                        · rcases p8249_3 (m.d 3 5) (by simp) with h8291 | h8291
                                          · rcases h4bigk with h8292c | h8292c | h8292c | h8292c | h8292c | h8292c | h8292c | h8292c | h8292c | h8292c | h8292c | h8292c | h8292c | h8292c | h8292c | h8292c | h8292c | h8292c | h8292c | h8292c | h8292c | h8292c | h8292c | h8292c | h8292c
                                            · have p8292_0 := h8292c.1
                                              have p8292_1 := h8292c.2.1
                                              have p8292_2 := h8292c.2.2.1
                                              have p8292_3 := h8292c.2.2.2
                                              linarith only [hlam, p8292_0]
                                            · have p8292_0 := h8292c.1
                                              have p8292_1 := h8292c.2.1
                                              have p8292_2 := h8292c.2.2.1
                                              have p8292_3 := h8292c.2.2.2
                                              linarith only [h7361, hlam, p8292_0]
                                            · have p8292_0 := h8292c.1
                                              have p8292_1 := h8292c.2.1
                                              have p8292_2 := h8292c.2.2.1
                                              have p8292_3 := h8292c.2.2.2
                                              linarith only [h7361, h8238, h8243, hc23, hc34, hlam, hphi, p8292_1]
                                            · have p8292_0 := h8292c.1
                                              have p8292_1 := h8292c.2.1
                                              have p8292_2 := h8292c.2.2.1
                                              have p8292_3 := h8292c.2.2.2
                                              linarith only [h8133, hlam, p8292_0]
                                            · have p8292_0 := h8292c.1
                                              have p8292_1 := h8292c.2.1
                                              have p8292_2 := h8292c.2.2.1
                                              have p8292_3 := h8292c.2.2.2
                                              rcases p8292_3 (m.d 0 4) (by simp) with h8297 | h8297
                                              · rcases p8292_3 (m.d 1 4) (by simp) with h8298 | h8298
                                                · rcases p8292_3 (m.d 2 4) (by simp) with h8299 | h8299
                                                  · linarith only [h8132, h8299, hlam]
                                                  · linarith only [h8247, h8299, hlam]
                                                · linarith only [h8242, h8298, hlam]
                                              · linarith only [h8297, hlam, p8292_0]
                                            · have p8292_0 := h8292c.1
                                              have p8292_1 := h8292c.2.1
                                              have p8292_2 := h8292c.2.2.1
                                              have p8292_3 := h8292c.2.2.2
                                              linarith only [h7361, h8238, hc01, hc34, hlam, hphi, ht12, ht23, p8292_1]
                                            · have p8292_0 := h8292c.1
                                              have p8292_1 := h8292c.2.1
                                              have p8292_2 := h8292c.2.2.1
                                              have p8292_3 := h8292c.2.2.2
                                              linarith only [hlam, p8292_0]
                                            · have p8292_0 := h8292c.1
                                              have p8292_1 := h8292c.2.1
                                              have p8292_2 := h8292c.2.2.1
                                              have p8292_3 := h8292c.2.2.2
                                              linarith only [h8238, h8247, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p8292_1]
                                            · have p8292_0 := h8292c.1
                                              have p8292_1 := h8292c.2.1
                                              have p8292_2 := h8292c.2.2.1
                                              have p8292_3 := h8292c.2.2.2
                                              linarith only [h8238, hlam, p8292_1]
                                            · have p8292_0 := h8292c.1
                                              have p8292_1 := h8292c.2.1
                                              have p8292_2 := h8292c.2.2.1
                                              have p8292_3 := h8292c.2.2.2
                                              rcases p8292_3 (m.d 0 4) (by simp) with h8308 | h8308
                                              · linarith only [h7361, h8308, hlam]
                                              · linarith only [h8235, h8308, hlam]
                                            · have p8292_0 := h8292c.1
                                              have p8292_1 := h8292c.2.1
                                              have p8292_2 := h8292c.2.2.1
                                              have p8292_3 := h8292c.2.2.2
                                              linarith only [h8132, hlam, p8292_1]
                                            · have p8292_0 := h8292c.1
                                              have p8292_1 := h8292c.2.1
                                              have p8292_2 := h8292c.2.2.1
                                              have p8292_3 := h8292c.2.2.2
                                              linarith only [h8237, hlam, p8292_1]
                                            · have p8292_0 := h8292c.1
                                              have p8292_1 := h8292c.2.1
                                              have p8292_2 := h8292c.2.2.1
                                              have p8292_3 := h8292c.2.2.2
                                              linarith only [hlam, p8292_0]
                                            · have p8292_0 := h8292c.1
                                              have p8292_1 := h8292c.2.1
                                              have p8292_2 := h8292c.2.2.1
                                              have p8292_3 := h8292c.2.2.2
                                              linarith only [h8243, hlam, p8292_1]
                                            · have p8292_0 := h8292c.1
                                              have p8292_1 := h8292c.2.1
                                              have p8292_2 := h8292c.2.2.1
                                              have p8292_3 := h8292c.2.2.2
                                              linarith only [h0, h8132, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p8292_1]
                                            · have p8292_0 := h8292c.1
                                              have p8292_1 := h8292c.2.1
                                              have p8292_2 := h8292c.2.2.1
                                              have p8292_3 := h8292c.2.2.2
                                              linarith only [h7361, h8130, h8236, h8240, hc23, hc34, hlam, hphi, p8292_1]
                                            · have p8292_0 := h8292c.1
                                              have p8292_1 := h8292c.2.1
                                              have p8292_2 := h8292c.2.2.1
                                              have p8292_3 := h8292c.2.2.2
                                              linarith only [h7361, h8130, h8236, h8240, hc23, hc34, hlam, hphi, p8292_1]
                                            · have p8292_0 := h8292c.1
                                              have p8292_1 := h8292c.2.1
                                              have p8292_2 := h8292c.2.2.1
                                              have p8292_3 := h8292c.2.2.2
                                              linarith only [h8243, hc23, hc34, hlam, hphi, p8292_1]
                                            · have p8292_0 := h8292c.1
                                              have p8292_1 := h8292c.2.1
                                              have p8292_2 := h8292c.2.2.1
                                              have p8292_3 := h8292c.2.2.2
                                              linarith only [hlam, p8292_0]
                                            · have p8292_0 := h8292c.1
                                              have p8292_1 := h8292c.2.1
                                              have p8292_2 := h8292c.2.2.1
                                              have p8292_3 := h8292c.2.2.2
                                              rcases p8292_3 (m.d 0 4) (by simp) with h8320 | h8320
                                              · linarith only [h8133, h8320, hlam]
                                              · linarith only [h8235, h8320, hlam]
                                            · have p8292_0 := h8292c.1
                                              have p8292_1 := h8292c.2.1
                                              have p8292_2 := h8292c.2.2.1
                                              have p8292_3 := h8292c.2.2.2
                                              linarith only [h8235, hlam, p8292_0]
                                            · have p8292_0 := h8292c.1
                                              have p8292_1 := h8292c.2.1
                                              have p8292_2 := h8292c.2.2.1
                                              have p8292_3 := h8292c.2.2.2
                                              linarith only [h8242, hlam, p8292_0]
                                            · have p8292_0 := h8292c.1
                                              have p8292_1 := h8292c.2.1
                                              have p8292_2 := h8292c.2.2.1
                                              have p8292_3 := h8292c.2.2.2
                                              linarith only [h8247, hlam, p8292_0]
                                            · have p8292_0 := h8292c.1
                                              have p8292_1 := h8292c.2.1
                                              have p8292_2 := h8292c.2.2.1
                                              have p8292_3 := h8292c.2.2.2
                                              linarith only [h8248, hlam, p8292_0]
                                            · have p8292_0 := h8292c.1
                                              have p8292_1 := h8292c.2.1
                                              have p8292_2 := h8292c.2.2.1
                                              have p8292_3 := h8292c.2.2.2
                                              linarith only [hlam, p8292_0]
                                          · linarith only [h8291, hlam, p8249_0]
                                        · linarith only [h8133, h8290, hlam]
                                · have p8249_0 := h8249c.1
                                  have p8249_1 := h8249c.2.1
                                  have p8249_2 := h8249c.2.2.1
                                  have p8249_3 := h8249c.2.2.2
                                  rcases p8249_3 (m.d 0 3) (by simp) with h8330 | h8330
                                  · linarith only [h8135, h8330, hlam]
                                  · linarith only [h7360, h8330, hlam]
                                · have p8249_0 := h8249c.1
                                  have p8249_1 := h8249c.2.1
                                  have p8249_2 := h8249c.2.2.1
                                  have p8249_3 := h8249c.2.2.2
                                  rcases p8249_3 (m.d 0 3) (by simp) with h8333 | h8333
                                  · linarith only [h8135, h8333, hlam]
                                  · linarith only [h8131, h8333, hlam]
                                · have p8249_0 := h8249c.1
                                  have p8249_1 := h8249c.2.1
                                  have p8249_2 := h8249c.2.2.1
                                  have p8249_3 := h8249c.2.2.2
                                  linarith only [h8248, hlam, p8249_0]
                                · have p8249_0 := h8249c.1
                                  have p8249_1 := h8249c.2.1
                                  have p8249_2 := h8249c.2.2.1
                                  have p8249_3 := h8249c.2.2.2
                                  linarith only [hlam, p8249_0]
                              · linarith only [h0, h7360, h8132, h8133, h8236, h8247, h8248, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                            · linarith only [h7361, h8130, h8238, h8242, h8243, h8247, hc23, hc34, hlam, hphi]
                      · linarith only [h7360, h7361, h8236, h8242, hc23, hc45, hlam, hphi, ht34]
                · linarith only [h0, h8132, h8237, hlam]
              · linarith only [h0, h8131, h8236, hlam]
            · linarith only [h7361, h8130, h8235, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h8344 | h8344
        · linarith only [h0, h7360, h8132, h8344, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h8346 | h8346
          · rcases m.htr 0 4 5 (by decide) (by decide) with h8347 | h8347
            · rcases m.htr 1 2 3 (by decide) (by decide) with h8348 | h8348
              · rcases m.htr 1 2 4 (by decide) (by decide) with h8349 | h8349
                · rcases m.htr 1 3 4 (by decide) (by decide) with h8350 | h8350
                  · linarith only [h0, h7360, h8132, h8344, h8349, h8350, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h8352 | h8352
                    · linarith only [h0, h7360, h8132, h8349, h8352, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                    · linarith only [h0, h7360, h8132, h8346, h8348, h8349, h8352, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h8355 | h8355
                  · linarith only [h0, h7360, h8349, h8355, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h8357 | h8357
                    · linarith only [h0, h7360, h8349, h8357, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                    · linarith only [h0, h7360, h8346, h8349, h8357, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
              · linarith only [h0, h7360, h8131, h8132, h8346, h8348, hc04, hc35, hlam, hphi, ht0b, ht5b]
            · linarith only [h0, h7360, h8132, h8346, h8347, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h8362 | h8362
            · rcases m.htr 1 2 3 (by decide) (by decide) with h8363 | h8363
              · rcases m.htr 1 2 4 (by decide) (by decide) with h8364 | h8364
                · rcases m.htr 1 3 4 (by decide) (by decide) with h8365 | h8365
                  · linarith only [h0, h7360, h8132, h8364, h8365, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h8367 | h8367
                    · linarith only [h0, h7360, h8132, h8346, h8364, h8367, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h8369 | h8369
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h8370 | h8370
                        · linarith only [h0, h8130, h8132, h8363, h8364, h8365, h8367, h8370, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h8372 | h8372
                          · linarith only [h7360, h8346, h8363, h8372, hlam]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h8374 | h8374
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h8375 | h8375
                              · rcases h3bigk with h8376c | h8376c | h8376c | h8376c | h8376c | h8376c | h8376c | h8376c | h8376c | h8376c | h8376c | h8376c | h8376c | h8376c | h8376c | h8376c | h8376c | h8376c | h8376c | h8376c | h8376c | h8376c | h8376c | h8376c | h8376c
                                · have p8376_0 := h8376c.1
                                  have p8376_1 := h8376c.2.1
                                  have p8376_2 := h8376c.2.2.1
                                  have p8376_3 := h8376c.2.2.2
                                  linarith only [hlam, p8376_0]
                                · have p8376_0 := h8376c.1
                                  have p8376_1 := h8376c.2.1
                                  have p8376_2 := h8376c.2.2.1
                                  have p8376_3 := h8376c.2.2.2
                                  linarith only [h8346, hc13, hc35, hlam, hphi, p8376_1]
                                · have p8376_0 := h8376c.1
                                  have p8376_1 := h8376c.2.1
                                  have p8376_2 := h8376c.2.2.1
                                  have p8376_3 := h8376c.2.2.2
                                  linarith only [h0, h7360, h8132, h8364, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8376_1]
                                · have p8376_0 := h8376c.1
                                  have p8376_1 := h8376c.2.1
                                  have p8376_2 := h8376c.2.2.1
                                  have p8376_3 := h8376c.2.2.2
                                  linarith only [h8344, hlam, p8376_0]
                                · have p8376_0 := h8376c.1
                                  have p8376_1 := h8376c.2.1
                                  have p8376_2 := h8376c.2.2.1
                                  have p8376_3 := h8376c.2.2.2
                                  linarith only [h8346, hlam, p8376_0]
                                · have p8376_0 := h8376c.1
                                  have p8376_1 := h8376c.2.1
                                  have p8376_2 := h8376c.2.2.1
                                  have p8376_3 := h8376c.2.2.2
                                  linarith only [h7360, hlam, p8376_0]
                                · have p8376_0 := h8376c.1
                                  have p8376_1 := h8376c.2.1
                                  have p8376_2 := h8376c.2.2.1
                                  have p8376_3 := h8376c.2.2.2
                                  linarith only [hlam, p8376_0]
                                · have p8376_0 := h8376c.1
                                  have p8376_1 := h8376c.2.1
                                  have p8376_2 := h8376c.2.2.1
                                  have p8376_3 := h8376c.2.2.2
                                  linarith only [h0, h8130, h8132, h8364, h8367, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8376_1]
                                · have p8376_0 := h8376c.1
                                  have p8376_1 := h8376c.2.1
                                  have p8376_2 := h8376c.2.2.1
                                  have p8376_3 := h8376c.2.2.2
                                  linarith only [h8365, hlam, p8376_0]
                                · have p8376_0 := h8376c.1
                                  have p8376_1 := h8376c.2.1
                                  have p8376_2 := h8376c.2.2.1
                                  have p8376_3 := h8376c.2.2.2
                                  linarith only [h8367, hlam, p8376_0]
                                · have p8376_0 := h8376c.1
                                  have p8376_1 := h8376c.2.1
                                  have p8376_2 := h8376c.2.2.1
                                  have p8376_3 := h8376c.2.2.2
                                  linarith only [h8131, hlam, p8376_0]
                                · have p8376_0 := h8376c.1
                                  have p8376_1 := h8376c.2.1
                                  have p8376_2 := h8376c.2.2.1
                                  have p8376_3 := h8376c.2.2.2
                                  linarith only [h8363, hlam, p8376_0]
                                · have p8376_0 := h8376c.1
                                  have p8376_1 := h8376c.2.1
                                  have p8376_2 := h8376c.2.2.1
                                  have p8376_3 := h8376c.2.2.2
                                  linarith only [hlam, p8376_0]
                                · have p8376_0 := h8376c.1
                                  have p8376_1 := h8376c.2.1
                                  have p8376_2 := h8376c.2.2.1
                                  have p8376_3 := h8376c.2.2.2
                                  linarith only [h8370, hlam, p8376_0]
                                · have p8376_0 := h8376c.1
                                  have p8376_1 := h8376c.2.1
                                  have p8376_2 := h8376c.2.2.1
                                  have p8376_3 := h8376c.2.2.2
                                  linarith only [h8372, hlam, p8376_0]
                                · have p8376_0 := h8376c.1
                                  have p8376_1 := h8376c.2.1
                                  have p8376_2 := h8376c.2.2.1
                                  have p8376_3 := h8376c.2.2.2
                                  rcases p8376_3 (m.d 0 3) (by simp) with h8392 | h8392
                                  · linarith only [h8392, hlam, p8376_0]
                                  · rcases p8376_3 (m.d 1 3) (by simp) with h8394 | h8394
                                    · linarith only [h8365, h8394, hlam]
                                    · rcases p8376_3 (m.d 2 3) (by simp) with h8396 | h8396
                                      · linarith only [h8370, h8396, hlam]
                                      · rcases p8376_3 (m.d 3 4) (by simp) with h8398 | h8398
                                        · rcases p8376_3 (m.d 3 5) (by simp) with h8399 | h8399
                                          · linarith only [h8375, h8399, hlam]
                                          · linarith only [h8346, h8399, hlam]
                                        · linarith only [h8398, hlam, p8376_0]
                                · have p8376_0 := h8376c.1
                                  have p8376_1 := h8376c.2.1
                                  have p8376_2 := h8376c.2.2.1
                                  have p8376_3 := h8376c.2.2.2
                                  rcases p8376_3 (m.d 0 3) (by simp) with h8403 | h8403
                                  · linarith only [h8344, h8403, hlam]
                                  · linarith only [h7360, h8403, hlam]
                                · have p8376_0 := h8376c.1
                                  have p8376_1 := h8376c.2.1
                                  have p8376_2 := h8376c.2.2.1
                                  have p8376_3 := h8376c.2.2.2
                                  rcases p8376_3 (m.d 0 3) (by simp) with h8406 | h8406
                                  · linarith only [h8344, h8406, hlam]
                                  · linarith only [h8131, h8406, hlam]
                                · have p8376_0 := h8376c.1
                                  have p8376_1 := h8376c.2.1
                                  have p8376_2 := h8376c.2.2.1
                                  have p8376_3 := h8376c.2.2.2
                                  linarith only [hlam, p8376_0]
                                · have p8376_0 := h8376c.1
                                  have p8376_1 := h8376c.2.1
                                  have p8376_2 := h8376c.2.2.1
                                  have p8376_3 := h8376c.2.2.2
                                  linarith only [h8346, hc03, hc34, hlam, hphi, p8376_1]
                                · have p8376_0 := h8376c.1
                                  have p8376_1 := h8376c.2.1
                                  have p8376_2 := h8376c.2.2.1
                                  have p8376_3 := h8376c.2.2.2
                                  rcases p8376_3 (m.d 0 3) (by simp) with h8411 | h8411
                                  · linarith only [h8411, hlam, p8376_0]
                                  · rcases p8376_3 (m.d 1 3) (by simp) with h8413 | h8413
                                    · linarith only [h8367, h8413, hlam]
                                    · rcases p8376_3 (m.d 2 3) (by simp) with h8415 | h8415
                                      · linarith only [h8372, h8415, hlam]
                                      · rcases p8376_3 (m.d 3 4) (by simp) with h8417 | h8417
                                        · rcases p8376_3 (m.d 3 5) (by simp) with h8418 | h8418
                                          · rcases h4bigk with h8419c | h8419c | h8419c | h8419c | h8419c | h8419c | h8419c | h8419c | h8419c | h8419c | h8419c | h8419c | h8419c | h8419c | h8419c | h8419c | h8419c | h8419c | h8419c | h8419c | h8419c | h8419c | h8419c | h8419c | h8419c
                                            · have p8419_0 := h8419c.1
                                              have p8419_1 := h8419c.2.1
                                              have p8419_2 := h8419c.2.2.1
                                              have p8419_3 := h8419c.2.2.2
                                              linarith only [hlam, p8419_0]
                                            · have p8419_0 := h8419c.1
                                              have p8419_1 := h8419c.2.1
                                              have p8419_2 := h8419c.2.2.1
                                              have p8419_3 := h8419c.2.2.2
                                              linarith only [h7361, hlam, p8419_0]
                                            · have p8419_0 := h8419c.1
                                              have p8419_1 := h8419c.2.1
                                              have p8419_2 := h8419c.2.2.1
                                              have p8419_3 := h8419c.2.2.2
                                              linarith only [h8132, hlam, p8419_0]
                                            · have p8419_0 := h8419c.1
                                              have p8419_1 := h8419c.2.1
                                              have p8419_2 := h8419c.2.2.1
                                              have p8419_3 := h8419c.2.2.2
                                              linarith only [h8344, hlam, p8419_0]
                                            · have p8419_0 := h8419c.1
                                              have p8419_1 := h8419c.2.1
                                              have p8419_2 := h8419c.2.2.1
                                              have p8419_3 := h8419c.2.2.2
                                              linarith only [h8132, h8364, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p8419_1]
                                            · have p8419_0 := h8419c.1
                                              have p8419_1 := h8419c.2.1
                                              have p8419_2 := h8419c.2.2.1
                                              have p8419_3 := h8419c.2.2.2
                                              linarith only [h7361, hc01, hc14, hlam, hphi, p8419_1]
                                            · have p8419_0 := h8419c.1
                                              have p8419_1 := h8419c.2.1
                                              have p8419_2 := h8419c.2.2.1
                                              have p8419_3 := h8419c.2.2.2
                                              linarith only [hlam, p8419_0]
                                            · have p8419_0 := h8419c.1
                                              have p8419_1 := h8419c.2.1
                                              have p8419_2 := h8419c.2.2.1
                                              have p8419_3 := h8419c.2.2.2
                                              linarith only [h0, h7360, h8132, h8363, h8364, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8419_1]
                                            · have p8419_0 := h8419c.1
                                              have p8419_1 := h8419c.2.1
                                              have p8419_2 := h8419c.2.2.1
                                              have p8419_3 := h8419c.2.2.2
                                              linarith only [h8365, hlam, p8419_1]
                                            · have p8419_0 := h8419c.1
                                              have p8419_1 := h8419c.2.1
                                              have p8419_2 := h8419c.2.2.1
                                              have p8419_3 := h8419c.2.2.2
                                              rcases p8419_3 (m.d 0 4) (by simp) with h8429 | h8429
                                              · linarith only [h7361, h8429, hlam]
                                              · linarith only [h8362, h8429, hlam]
                                            · have p8419_0 := h8419c.1
                                              have p8419_1 := h8419c.2.1
                                              have p8419_2 := h8419c.2.2.1
                                              have p8419_3 := h8419c.2.2.2
                                              linarith only [h0, h8130, h8132, h8363, h8367, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p8419_1]
                                            · have p8419_0 := h8419c.1
                                              have p8419_1 := h8419c.2.1
                                              have p8419_2 := h8419c.2.2.1
                                              have p8419_3 := h8419c.2.2.2
                                              linarith only [h8364, hlam, p8419_1]
                                            · have p8419_0 := h8419c.1
                                              have p8419_1 := h8419c.2.1
                                              have p8419_2 := h8419c.2.2.1
                                              have p8419_3 := h8419c.2.2.2
                                              linarith only [hlam, p8419_0]
                                            · have p8419_0 := h8419c.1
                                              have p8419_1 := h8419c.2.1
                                              have p8419_2 := h8419c.2.2.1
                                              have p8419_3 := h8419c.2.2.2
                                              linarith only [h8370, hlam, p8419_1]
                                            · have p8419_0 := h8419c.1
                                              have p8419_1 := h8419c.2.1
                                              have p8419_2 := h8419c.2.2.1
                                              have p8419_3 := h8419c.2.2.2
                                              linarith only [h8364, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p8419_1]
                                            · have p8419_0 := h8419c.1
                                              have p8419_1 := h8419c.2.1
                                              have p8419_2 := h8419c.2.2.1
                                              have p8419_3 := h8419c.2.2.2
                                              linarith only [h0, h8130, h8132, h8363, h8367, hc23, hc34, hlam, hphi, p8419_1]
                                            · have p8419_0 := h8419c.1
                                              have p8419_1 := h8419c.2.1
                                              have p8419_2 := h8419c.2.2.1
                                              have p8419_3 := h8419c.2.2.2
                                              linarith only [h7361, h8130, h8363, h8367, hc23, hc34, hlam, hphi, p8419_1]
                                            · have p8419_0 := h8419c.1
                                              have p8419_1 := h8419c.2.1
                                              have p8419_2 := h8419c.2.2.1
                                              have p8419_3 := h8419c.2.2.2
                                              linarith only [h0, h8130, h8132, h8363, h8367, hc23, hc34, hlam, hphi, p8419_1]
                                            · have p8419_0 := h8419c.1
                                              have p8419_1 := h8419c.2.1
                                              have p8419_2 := h8419c.2.2.1
                                              have p8419_3 := h8419c.2.2.2
                                              linarith only [hlam, p8419_0]
                                            · have p8419_0 := h8419c.1
                                              have p8419_1 := h8419c.2.1
                                              have p8419_2 := h8419c.2.2.1
                                              have p8419_3 := h8419c.2.2.2
                                              rcases p8419_3 (m.d 0 4) (by simp) with h8441 | h8441
                                              · linarith only [h8344, h8441, hlam]
                                              · linarith only [h8362, h8441, hlam]
                                            · have p8419_0 := h8419c.1
                                              have p8419_1 := h8419c.2.1
                                              have p8419_2 := h8419c.2.2.1
                                              have p8419_3 := h8419c.2.2.2
                                              linarith only [h8362, hlam, p8419_0]
                                            · have p8419_0 := h8419c.1
                                              have p8419_1 := h8419c.2.1
                                              have p8419_2 := h8419c.2.2.1
                                              have p8419_3 := h8419c.2.2.2
                                              linarith only [h8369, hlam, p8419_0]
                                            · have p8419_0 := h8419c.1
                                              have p8419_1 := h8419c.2.1
                                              have p8419_2 := h8419c.2.2.1
                                              have p8419_3 := h8419c.2.2.2
                                              linarith only [h8374, hlam, p8419_0]
                                            · have p8419_0 := h8419c.1
                                              have p8419_1 := h8419c.2.1
                                              have p8419_2 := h8419c.2.2.1
                                              have p8419_3 := h8419c.2.2.2
                                              linarith only [h8375, hlam, p8419_0]
                                            · have p8419_0 := h8419c.1
                                              have p8419_1 := h8419c.2.1
                                              have p8419_2 := h8419c.2.2.1
                                              have p8419_3 := h8419c.2.2.2
                                              linarith only [hlam, p8419_0]
                                          · linarith only [h8418, hlam, p8376_0]
                                        · linarith only [h8344, h8417, hlam]
                                · have p8376_0 := h8376c.1
                                  have p8376_1 := h8376c.2.1
                                  have p8376_2 := h8376c.2.2.1
                                  have p8376_3 := h8376c.2.2.2
                                  rcases p8376_3 (m.d 0 3) (by simp) with h8451 | h8451
                                  · linarith only [h8346, h8451, hlam]
                                  · linarith only [h7360, h8451, hlam]
                                · have p8376_0 := h8376c.1
                                  have p8376_1 := h8376c.2.1
                                  have p8376_2 := h8376c.2.2.1
                                  have p8376_3 := h8376c.2.2.2
                                  rcases p8376_3 (m.d 0 3) (by simp) with h8454 | h8454
                                  · linarith only [h8346, h8454, hlam]
                                  · linarith only [h8131, h8454, hlam]
                                · have p8376_0 := h8376c.1
                                  have p8376_1 := h8376c.2.1
                                  have p8376_2 := h8376c.2.2.1
                                  have p8376_3 := h8376c.2.2.2
                                  linarith only [h8375, hlam, p8376_0]
                                · have p8376_0 := h8376c.1
                                  have p8376_1 := h8376c.2.1
                                  have p8376_2 := h8376c.2.2.1
                                  have p8376_3 := h8376c.2.2.2
                                  linarith only [hlam, p8376_0]
                              · linarith only [h8344, h8362, h8375, hlam]
                            · linarith only [h7361, h8130, h8132, h8369, h8374, hlam]
                      · linarith only [h7361, h8130, h8367, h8369, hc13, hc45, hlam, hphi, ht34]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h8462 | h8462
                  · linarith only [h0, h7360, h8364, h8462, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h8464 | h8464
                    · linarith only [h0, h7360, h8346, h8364, h8464, hc03, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h8466 | h8466
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h8467 | h8467
                        · linarith only [h0, h7360, h8363, h8364, h8462, h8467, hc14, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                        · linarith only [h0, h8130, h8363, h8364, h8464, h8467, hc23, hc34, hlam, hphi]
                      · linarith only [h0, h8130, h8363, h8364, h8464, h8466, hc23, hc45, hlam, hphi, ht34]
              · linarith only [h0, h7361, h8131, h8132, h8363, hc01, hc14, hlam, hphi]
            · linarith only [h0, h8130, h8132, h8362, hlam]
    · linarith only [h0, h7360, h8131, hlam]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h8474 | h8474
    · rcases m.htr 0 2 4 (by decide) (by decide) with h8475 | h8475
      · rcases m.htr 0 3 4 (by decide) (by decide) with h8476 | h8476
        · linarith only [h7360, h7361, h8476, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h8478 | h8478
          · linarith only [h7360, h8130, h8478, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h8480 | h8480
            · rcases m.htr 1 2 3 (by decide) (by decide) with h8481 | h8481
              · rcases m.htr 1 2 4 (by decide) (by decide) with h8482 | h8482
                · rcases m.htr 1 3 4 (by decide) (by decide) with h8483 | h8483
                  · linarith only [h7360, h7361, h8476, h8482, h8483, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h8485 | h8485
                    · linarith only [h7360, h8130, h8478, h8485, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h8487 | h8487
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h8488 | h8488
                        · linarith only [h7360, h8130, h8474, h8483, h8487, h8488, hc02, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h8490 | h8490
                          · linarith only [h7360, h8130, h8481, h8485, h8490, hlam]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h8492 | h8492
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h8493 | h8493
                              · rcases h3bigk with h8494c | h8494c | h8494c | h8494c | h8494c | h8494c | h8494c | h8494c | h8494c | h8494c | h8494c | h8494c | h8494c | h8494c | h8494c | h8494c | h8494c | h8494c | h8494c | h8494c | h8494c | h8494c | h8494c | h8494c | h8494c
                                · have p8494_0 := h8494c.1
                                  have p8494_1 := h8494c.2.1
                                  have p8494_2 := h8494c.2.2.1
                                  have p8494_3 := h8494c.2.2.2
                                  linarith only [hlam, p8494_0]
                                · have p8494_0 := h8494c.1
                                  have p8494_1 := h8494c.2.1
                                  have p8494_2 := h8494c.2.2.1
                                  have p8494_3 := h8494c.2.2.2
                                  linarith only [h7360, h8130, h8481, h8483, h8487, hc23, hc34, hlam, hphi, p8494_1]
                                · have p8494_0 := h8494c.1
                                  have p8494_1 := h8494c.2.1
                                  have p8494_2 := h8494c.2.2.1
                                  have p8494_3 := h8494c.2.2.2
                                  linarith only [h7360, h8130, h8483, h8487, hc23, hc34, hlam, hphi, p8494_1]
                                · have p8494_0 := h8494c.1
                                  have p8494_1 := h8494c.2.1
                                  have p8494_2 := h8494c.2.2.1
                                  have p8494_3 := h8494c.2.2.2
                                  linarith only [h8476, hlam, p8494_0]
                                · have p8494_0 := h8494c.1
                                  have p8494_1 := h8494c.2.1
                                  have p8494_2 := h8494c.2.2.1
                                  have p8494_3 := h8494c.2.2.2
                                  linarith only [h8478, hlam, p8494_0]
                                · have p8494_0 := h8494c.1
                                  have p8494_1 := h8494c.2.1
                                  have p8494_2 := h8494c.2.2.1
                                  have p8494_3 := h8494c.2.2.2
                                  linarith only [h7360, hlam, p8494_0]
                                · have p8494_0 := h8494c.1
                                  have p8494_1 := h8494c.2.1
                                  have p8494_2 := h8494c.2.2.1
                                  have p8494_3 := h8494c.2.2.2
                                  linarith only [hlam, p8494_0]
                                · have p8494_0 := h8494c.1
                                  have p8494_1 := h8494c.2.1
                                  have p8494_2 := h8494c.2.2.1
                                  have p8494_3 := h8494c.2.2.2
                                  linarith only [h7360, h8130, h8483, h8487, hc23, hc34, hlam, hphi, p8494_1]
                                · have p8494_0 := h8494c.1
                                  have p8494_1 := h8494c.2.1
                                  have p8494_2 := h8494c.2.2.1
                                  have p8494_3 := h8494c.2.2.2
                                  linarith only [h8483, hlam, p8494_0]
                                · have p8494_0 := h8494c.1
                                  have p8494_1 := h8494c.2.1
                                  have p8494_2 := h8494c.2.2.1
                                  have p8494_3 := h8494c.2.2.2
                                  linarith only [h8485, hlam, p8494_0]
                                · have p8494_0 := h8494c.1
                                  have p8494_1 := h8494c.2.1
                                  have p8494_2 := h8494c.2.2.1
                                  have p8494_3 := h8494c.2.2.2
                                  linarith only [h8474, hlam, p8494_0]
                                · have p8494_0 := h8494c.1
                                  have p8494_1 := h8494c.2.1
                                  have p8494_2 := h8494c.2.2.1
                                  have p8494_3 := h8494c.2.2.2
                                  linarith only [h8481, hlam, p8494_0]
                                · have p8494_0 := h8494c.1
                                  have p8494_1 := h8494c.2.1
                                  have p8494_2 := h8494c.2.2.1
                                  have p8494_3 := h8494c.2.2.2
                                  linarith only [hlam, p8494_0]
                                · have p8494_0 := h8494c.1
                                  have p8494_1 := h8494c.2.1
                                  have p8494_2 := h8494c.2.2.1
                                  have p8494_3 := h8494c.2.2.2
                                  linarith only [h8488, hlam, p8494_0]
                                · have p8494_0 := h8494c.1
                                  have p8494_1 := h8494c.2.1
                                  have p8494_2 := h8494c.2.2.1
                                  have p8494_3 := h8494c.2.2.2
                                  linarith only [h8490, hlam, p8494_0]
                                · have p8494_0 := h8494c.1
                                  have p8494_1 := h8494c.2.1
                                  have p8494_2 := h8494c.2.2.1
                                  have p8494_3 := h8494c.2.2.2
                                  rcases p8494_3 (m.d 0 3) (by simp) with h8510 | h8510
                                  · linarith only [h8510, hlam, p8494_0]
                                  · rcases p8494_3 (m.d 1 3) (by simp) with h8512 | h8512
                                    · linarith only [h8483, h8512, hlam]
                                    · rcases p8494_3 (m.d 2 3) (by simp) with h8514 | h8514
                                      · linarith only [h8488, h8514, hlam]
                                      · rcases p8494_3 (m.d 3 4) (by simp) with h8516 | h8516
                                        · rcases p8494_3 (m.d 3 5) (by simp) with h8517 | h8517
                                          · linarith only [h8493, h8517, hlam]
                                          · linarith only [h8478, h8517, hlam]
                                        · linarith only [h8516, hlam, p8494_0]
                                · have p8494_0 := h8494c.1
                                  have p8494_1 := h8494c.2.1
                                  have p8494_2 := h8494c.2.2.1
                                  have p8494_3 := h8494c.2.2.2
                                  rcases p8494_3 (m.d 0 3) (by simp) with h8521 | h8521
                                  · linarith only [h8476, h8521, hlam]
                                  · linarith only [h7360, h8521, hlam]
                                · have p8494_0 := h8494c.1
                                  have p8494_1 := h8494c.2.1
                                  have p8494_2 := h8494c.2.2.1
                                  have p8494_3 := h8494c.2.2.2
                                  rcases p8494_3 (m.d 0 3) (by simp) with h8524 | h8524
                                  · linarith only [h8476, h8524, hlam]
                                  · linarith only [h8474, h8524, hlam]
                                · have p8494_0 := h8494c.1
                                  have p8494_1 := h8494c.2.1
                                  have p8494_2 := h8494c.2.2.1
                                  have p8494_3 := h8494c.2.2.2
                                  linarith only [hlam, p8494_0]
                                · have p8494_0 := h8494c.1
                                  have p8494_1 := h8494c.2.1
                                  have p8494_2 := h8494c.2.2.1
                                  have p8494_3 := h8494c.2.2.2
                                  linarith only [h8130, h8485, hc01, hc34, hlam, hphi, ht12, ht23, p8494_1]
                                · have p8494_0 := h8494c.1
                                  have p8494_1 := h8494c.2.1
                                  have p8494_2 := h8494c.2.2.1
                                  have p8494_3 := h8494c.2.2.2
                                  rcases p8494_3 (m.d 0 3) (by simp) with h8529 | h8529
                                  · linarith only [h8529, hlam, p8494_0]
                                  · rcases p8494_3 (m.d 1 3) (by simp) with h8531 | h8531
                                    · linarith only [h8485, h8531, hlam]
                                    · rcases p8494_3 (m.d 2 3) (by simp) with h8533 | h8533
                                      · linarith only [h8490, h8533, hlam]
                                      · rcases p8494_3 (m.d 3 4) (by simp) with h8535 | h8535
                                        · rcases p8494_3 (m.d 3 5) (by simp) with h8536 | h8536
                                          · rcases h4bigk with h8537c | h8537c | h8537c | h8537c | h8537c | h8537c | h8537c | h8537c | h8537c | h8537c | h8537c | h8537c | h8537c | h8537c | h8537c | h8537c | h8537c | h8537c | h8537c | h8537c | h8537c | h8537c | h8537c | h8537c | h8537c
                                            · have p8537_0 := h8537c.1
                                              have p8537_1 := h8537c.2.1
                                              have p8537_2 := h8537c.2.2.1
                                              have p8537_3 := h8537c.2.2.2
                                              linarith only [hlam, p8537_0]
                                            · have p8537_0 := h8537c.1
                                              have p8537_1 := h8537c.2.1
                                              have p8537_2 := h8537c.2.2.1
                                              have p8537_3 := h8537c.2.2.2
                                              linarith only [h7361, hlam, p8537_0]
                                            · have p8537_0 := h8537c.1
                                              have p8537_1 := h8537c.2.1
                                              have p8537_2 := h8537c.2.2.1
                                              have p8537_3 := h8537c.2.2.2
                                              linarith only [h8492, hc04, hc45, hlam, hphi, ht0b, ht5b, p8537_1]
                                            · have p8537_0 := h8537c.1
                                              have p8537_1 := h8537c.2.1
                                              have p8537_2 := h8537c.2.2.1
                                              have p8537_3 := h8537c.2.2.2
                                              linarith only [h8476, hlam, p8537_0]
                                            · have p8537_0 := h8537c.1
                                              have p8537_1 := h8537c.2.1
                                              have p8537_2 := h8537c.2.2.1
                                              have p8537_3 := h8537c.2.2.2
                                              rcases p8537_3 (m.d 0 4) (by simp) with h8542 | h8542
                                              · rcases p8537_3 (m.d 1 4) (by simp) with h8543 | h8543
                                                · rcases p8537_3 (m.d 2 4) (by simp) with h8544 | h8544
                                                  · linarith only [h8475, h8544, hlam]
                                                  · linarith only [h8492, h8544, hlam]
                                                · linarith only [h8487, h8543, hlam]
                                              · linarith only [h8542, hlam, p8537_0]
                                            · have p8537_0 := h8537c.1
                                              have p8537_1 := h8537c.2.1
                                              have p8537_2 := h8537c.2.2.1
                                              have p8537_3 := h8537c.2.2.2
                                              linarith only [h7360, h7361, h8481, h8483, hc23, hc34, hlam, hphi, p8537_1]
                                            · have p8537_0 := h8537c.1
                                              have p8537_1 := h8537c.2.1
                                              have p8537_2 := h8537c.2.2.1
                                              have p8537_3 := h8537c.2.2.2
                                              linarith only [hlam, p8537_0]
                                            · have p8537_0 := h8537c.1
                                              have p8537_1 := h8537c.2.1
                                              have p8537_2 := h8537c.2.2.1
                                              have p8537_3 := h8537c.2.2.2
                                              linarith only [h8483, h8492, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p8537_1]
                                            · have p8537_0 := h8537c.1
                                              have p8537_1 := h8537c.2.1
                                              have p8537_2 := h8537c.2.2.1
                                              have p8537_3 := h8537c.2.2.2
                                              linarith only [h8483, hlam, p8537_1]
                                            · have p8537_0 := h8537c.1
                                              have p8537_1 := h8537c.2.1
                                              have p8537_2 := h8537c.2.2.1
                                              have p8537_3 := h8537c.2.2.2
                                              rcases p8537_3 (m.d 0 4) (by simp) with h8553 | h8553
                                              · linarith only [h7361, h8553, hlam]
                                              · linarith only [h8480, h8553, hlam]
                                            · have p8537_0 := h8537c.1
                                              have p8537_1 := h8537c.2.1
                                              have p8537_2 := h8537c.2.2.1
                                              have p8537_3 := h8537c.2.2.2
                                              linarith only [h8475, hlam, p8537_1]
                                            · have p8537_0 := h8537c.1
                                              have p8537_1 := h8537c.2.1
                                              have p8537_2 := h8537c.2.2.1
                                              have p8537_3 := h8537c.2.2.2
                                              linarith only [h8482, hlam, p8537_1]
                                            · have p8537_0 := h8537c.1
                                              have p8537_1 := h8537c.2.1
                                              have p8537_2 := h8537c.2.2.1
                                              have p8537_3 := h8537c.2.2.2
                                              linarith only [hlam, p8537_0]
                                            · have p8537_0 := h8537c.1
                                              have p8537_1 := h8537c.2.1
                                              have p8537_2 := h8537c.2.2.1
                                              have p8537_3 := h8537c.2.2.2
                                              linarith only [h8488, hlam, p8537_1]
                                            · have p8537_0 := h8537c.1
                                              have p8537_1 := h8537c.2.1
                                              have p8537_2 := h8537c.2.2.1
                                              have p8537_3 := h8537c.2.2.2
                                              linarith only [h0, h8475, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p8537_1]
                                            · have p8537_0 := h8537c.1
                                              have p8537_1 := h8537c.2.1
                                              have p8537_2 := h8537c.2.2.1
                                              have p8537_3 := h8537c.2.2.2
                                              linarith only [h7360, h7361, h8481, hc23, hc34, hlam, hphi, p8537_1]
                                            · have p8537_0 := h8537c.1
                                              have p8537_1 := h8537c.2.1
                                              have p8537_2 := h8537c.2.2.1
                                              have p8537_3 := h8537c.2.2.2
                                              linarith only [h7360, h7361, h8481, hc23, hc34, hlam, hphi, p8537_1]
                                            · have p8537_0 := h8537c.1
                                              have p8537_1 := h8537c.2.1
                                              have p8537_2 := h8537c.2.2.1
                                              have p8537_3 := h8537c.2.2.2
                                              linarith only [h8488, hc23, hc34, hlam, hphi, p8537_1]
                                            · have p8537_0 := h8537c.1
                                              have p8537_1 := h8537c.2.1
                                              have p8537_2 := h8537c.2.2.1
                                              have p8537_3 := h8537c.2.2.2
                                              linarith only [hlam, p8537_0]
                                            · have p8537_0 := h8537c.1
                                              have p8537_1 := h8537c.2.1
                                              have p8537_2 := h8537c.2.2.1
                                              have p8537_3 := h8537c.2.2.2
                                              rcases p8537_3 (m.d 0 4) (by simp) with h8565 | h8565
                                              · linarith only [h8476, h8565, hlam]
                                              · linarith only [h8480, h8565, hlam]
                                            · have p8537_0 := h8537c.1
                                              have p8537_1 := h8537c.2.1
                                              have p8537_2 := h8537c.2.2.1
                                              have p8537_3 := h8537c.2.2.2
                                              linarith only [h8480, hlam, p8537_0]
                                            · have p8537_0 := h8537c.1
                                              have p8537_1 := h8537c.2.1
                                              have p8537_2 := h8537c.2.2.1
                                              have p8537_3 := h8537c.2.2.2
                                              linarith only [h8487, hlam, p8537_0]
                                            · have p8537_0 := h8537c.1
                                              have p8537_1 := h8537c.2.1
                                              have p8537_2 := h8537c.2.2.1
                                              have p8537_3 := h8537c.2.2.2
                                              linarith only [h8492, hlam, p8537_0]
                                            · have p8537_0 := h8537c.1
                                              have p8537_1 := h8537c.2.1
                                              have p8537_2 := h8537c.2.2.1
                                              have p8537_3 := h8537c.2.2.2
                                              linarith only [h8493, hlam, p8537_0]
                                            · have p8537_0 := h8537c.1
                                              have p8537_1 := h8537c.2.1
                                              have p8537_2 := h8537c.2.2.1
                                              have p8537_3 := h8537c.2.2.2
                                              linarith only [hlam, p8537_0]
                                          · linarith only [h8536, hlam, p8494_0]
                                        · linarith only [h8476, h8535, hlam]
                                · have p8494_0 := h8494c.1
                                  have p8494_1 := h8494c.2.1
                                  have p8494_2 := h8494c.2.2.1
                                  have p8494_3 := h8494c.2.2.2
                                  rcases p8494_3 (m.d 0 3) (by simp) with h8575 | h8575
                                  · linarith only [h8478, h8575, hlam]
                                  · linarith only [h7360, h8575, hlam]
                                · have p8494_0 := h8494c.1
                                  have p8494_1 := h8494c.2.1
                                  have p8494_2 := h8494c.2.2.1
                                  have p8494_3 := h8494c.2.2.2
                                  rcases p8494_3 (m.d 0 3) (by simp) with h8578 | h8578
                                  · linarith only [h8478, h8578, hlam]
                                  · linarith only [h8474, h8578, hlam]
                                · have p8494_0 := h8494c.1
                                  have p8494_1 := h8494c.2.1
                                  have p8494_2 := h8494c.2.2.1
                                  have p8494_3 := h8494c.2.2.2
                                  linarith only [h8493, hlam, p8494_0]
                                · have p8494_0 := h8494c.1
                                  have p8494_1 := h8494c.2.1
                                  have p8494_2 := h8494c.2.2.1
                                  have p8494_3 := h8494c.2.2.2
                                  linarith only [hlam, p8494_0]
                              · linarith only [h0, h7360, h8475, h8476, h8481, h8492, h8493, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h8584 | h8584
                              · rcases h3bigk with h8585c | h8585c | h8585c | h8585c | h8585c | h8585c | h8585c | h8585c | h8585c | h8585c | h8585c | h8585c | h8585c | h8585c | h8585c | h8585c | h8585c | h8585c | h8585c | h8585c | h8585c | h8585c | h8585c | h8585c | h8585c
                                · have p8585_0 := h8585c.1
                                  have p8585_1 := h8585c.2.1
                                  have p8585_2 := h8585c.2.2.1
                                  have p8585_3 := h8585c.2.2.2
                                  linarith only [hlam, p8585_0]
                                · have p8585_0 := h8585c.1
                                  have p8585_1 := h8585c.2.1
                                  have p8585_2 := h8585c.2.2.1
                                  have p8585_3 := h8585c.2.2.2
                                  linarith only [h7360, h8130, h8481, h8485, hc23, hc35, hlam, hphi, p8585_1]
                                · have p8585_0 := h8585c.1
                                  have p8585_1 := h8585c.2.1
                                  have p8585_2 := h8585c.2.2.1
                                  have p8585_3 := h8585c.2.2.2
                                  linarith only [h7360, h8130, h8485, hc23, hc35, hlam, hphi, p8585_1]
                                · have p8585_0 := h8585c.1
                                  have p8585_1 := h8585c.2.1
                                  have p8585_2 := h8585c.2.2.1
                                  have p8585_3 := h8585c.2.2.2
                                  linarith only [h8476, hlam, p8585_0]
                                · have p8585_0 := h8585c.1
                                  have p8585_1 := h8585c.2.1
                                  have p8585_2 := h8585c.2.2.1
                                  have p8585_3 := h8585c.2.2.2
                                  linarith only [h8478, hlam, p8585_0]
                                · have p8585_0 := h8585c.1
                                  have p8585_1 := h8585c.2.1
                                  have p8585_2 := h8585c.2.2.1
                                  have p8585_3 := h8585c.2.2.2
                                  linarith only [h7360, hlam, p8585_0]
                                · have p8585_0 := h8585c.1
                                  have p8585_1 := h8585c.2.1
                                  have p8585_2 := h8585c.2.2.1
                                  have p8585_3 := h8585c.2.2.2
                                  linarith only [hlam, p8585_0]
                                · have p8585_0 := h8585c.1
                                  have p8585_1 := h8585c.2.1
                                  have p8585_2 := h8585c.2.2.1
                                  have p8585_3 := h8585c.2.2.2
                                  linarith only [h7360, h8130, h8485, hc23, hc35, hlam, hphi, p8585_1]
                                · have p8585_0 := h8585c.1
                                  have p8585_1 := h8585c.2.1
                                  have p8585_2 := h8585c.2.2.1
                                  have p8585_3 := h8585c.2.2.2
                                  linarith only [h8483, hlam, p8585_0]
                                · have p8585_0 := h8585c.1
                                  have p8585_1 := h8585c.2.1
                                  have p8585_2 := h8585c.2.2.1
                                  have p8585_3 := h8585c.2.2.2
                                  linarith only [h8485, hlam, p8585_0]
                                · have p8585_0 := h8585c.1
                                  have p8585_1 := h8585c.2.1
                                  have p8585_2 := h8585c.2.2.1
                                  have p8585_3 := h8585c.2.2.2
                                  linarith only [h8474, hlam, p8585_0]
                                · have p8585_0 := h8585c.1
                                  have p8585_1 := h8585c.2.1
                                  have p8585_2 := h8585c.2.2.1
                                  have p8585_3 := h8585c.2.2.2
                                  linarith only [h8481, hlam, p8585_0]
                                · have p8585_0 := h8585c.1
                                  have p8585_1 := h8585c.2.1
                                  have p8585_2 := h8585c.2.2.1
                                  have p8585_3 := h8585c.2.2.2
                                  linarith only [hlam, p8585_0]
                                · have p8585_0 := h8585c.1
                                  have p8585_1 := h8585c.2.1
                                  have p8585_2 := h8585c.2.2.1
                                  have p8585_3 := h8585c.2.2.2
                                  linarith only [h8488, hlam, p8585_0]
                                · have p8585_0 := h8585c.1
                                  have p8585_1 := h8585c.2.1
                                  have p8585_2 := h8585c.2.2.1
                                  have p8585_3 := h8585c.2.2.2
                                  linarith only [h8490, hlam, p8585_0]
                                · have p8585_0 := h8585c.1
                                  have p8585_1 := h8585c.2.1
                                  have p8585_2 := h8585c.2.2.1
                                  have p8585_3 := h8585c.2.2.2
                                  rcases p8585_3 (m.d 0 3) (by simp) with h8601 | h8601
                                  · linarith only [h8601, hlam, p8585_0]
                                  · rcases p8585_3 (m.d 1 3) (by simp) with h8603 | h8603
                                    · linarith only [h8483, h8603, hlam]
                                    · rcases p8585_3 (m.d 2 3) (by simp) with h8605 | h8605
                                      · linarith only [h8488, h8605, hlam]
                                      · rcases p8585_3 (m.d 3 4) (by simp) with h8607 | h8607
                                        · rcases p8585_3 (m.d 3 5) (by simp) with h8608 | h8608
                                          · linarith only [h8584, h8608, hlam]
                                          · linarith only [h8478, h8608, hlam]
                                        · linarith only [h8607, hlam, p8585_0]
                                · have p8585_0 := h8585c.1
                                  have p8585_1 := h8585c.2.1
                                  have p8585_2 := h8585c.2.2.1
                                  have p8585_3 := h8585c.2.2.2
                                  rcases p8585_3 (m.d 0 3) (by simp) with h8612 | h8612
                                  · linarith only [h8476, h8612, hlam]
                                  · linarith only [h7360, h8612, hlam]
                                · have p8585_0 := h8585c.1
                                  have p8585_1 := h8585c.2.1
                                  have p8585_2 := h8585c.2.2.1
                                  have p8585_3 := h8585c.2.2.2
                                  rcases p8585_3 (m.d 0 3) (by simp) with h8615 | h8615
                                  · linarith only [h8476, h8615, hlam]
                                  · linarith only [h8474, h8615, hlam]
                                · have p8585_0 := h8585c.1
                                  have p8585_1 := h8585c.2.1
                                  have p8585_2 := h8585c.2.2.1
                                  have p8585_3 := h8585c.2.2.2
                                  linarith only [hlam, p8585_0]
                                · have p8585_0 := h8585c.1
                                  have p8585_1 := h8585c.2.1
                                  have p8585_2 := h8585c.2.2.1
                                  have p8585_3 := h8585c.2.2.2
                                  linarith only [h8478, hc03, hc34, hlam, hphi, p8585_1]
                                · have p8585_0 := h8585c.1
                                  have p8585_1 := h8585c.2.1
                                  have p8585_2 := h8585c.2.2.1
                                  have p8585_3 := h8585c.2.2.2
                                  rcases p8585_3 (m.d 0 3) (by simp) with h8620 | h8620
                                  · linarith only [h8620, hlam, p8585_0]
                                  · rcases p8585_3 (m.d 1 3) (by simp) with h8622 | h8622
                                    · linarith only [h8485, h8622, hlam]
                                    · rcases p8585_3 (m.d 2 3) (by simp) with h8624 | h8624
                                      · linarith only [h8490, h8624, hlam]
                                      · rcases p8585_3 (m.d 3 4) (by simp) with h8626 | h8626
                                        · rcases p8585_3 (m.d 3 5) (by simp) with h8627 | h8627
                                          · rcases h4bigk with h8628c | h8628c | h8628c | h8628c | h8628c | h8628c | h8628c | h8628c | h8628c | h8628c | h8628c | h8628c | h8628c | h8628c | h8628c | h8628c | h8628c | h8628c | h8628c | h8628c | h8628c | h8628c | h8628c | h8628c | h8628c
                                            · have p8628_0 := h8628c.1
                                              have p8628_1 := h8628c.2.1
                                              have p8628_2 := h8628c.2.2.1
                                              have p8628_3 := h8628c.2.2.2
                                              linarith only [hlam, p8628_0]
                                            · have p8628_0 := h8628c.1
                                              have p8628_1 := h8628c.2.1
                                              have p8628_2 := h8628c.2.2.1
                                              have p8628_3 := h8628c.2.2.2
                                              linarith only [h7361, hlam, p8628_0]
                                            · have p8628_0 := h8628c.1
                                              have p8628_1 := h8628c.2.1
                                              have p8628_2 := h8628c.2.2.1
                                              have p8628_3 := h8628c.2.2.2
                                              linarith only [h7361, h8483, h8488, hc23, hc34, hlam, hphi, p8628_1]
                                            · have p8628_0 := h8628c.1
                                              have p8628_1 := h8628c.2.1
                                              have p8628_2 := h8628c.2.2.1
                                              have p8628_3 := h8628c.2.2.2
                                              linarith only [h8476, hlam, p8628_0]
                                            · have p8628_0 := h8628c.1
                                              have p8628_1 := h8628c.2.1
                                              have p8628_2 := h8628c.2.2.1
                                              have p8628_3 := h8628c.2.2.2
                                              linarith only [h7361, h8483, h8488, h8492, hc23, hc34, hlam, hphi, p8628_1]
                                            · have p8628_0 := h8628c.1
                                              have p8628_1 := h8628c.2.1
                                              have p8628_2 := h8628c.2.2.1
                                              have p8628_3 := h8628c.2.2.2
                                              linarith only [h7361, h8483, hc01, hc34, hlam, hphi, ht12, ht23, p8628_1]
                                            · have p8628_0 := h8628c.1
                                              have p8628_1 := h8628c.2.1
                                              have p8628_2 := h8628c.2.2.1
                                              have p8628_3 := h8628c.2.2.2
                                              linarith only [hlam, p8628_0]
                                            · have p8628_0 := h8628c.1
                                              have p8628_1 := h8628c.2.1
                                              have p8628_2 := h8628c.2.2.1
                                              have p8628_3 := h8628c.2.2.2
                                              linarith only [h8483, h8488, hc23, hc34, hlam, hphi, p8628_1]
                                            · have p8628_0 := h8628c.1
                                              have p8628_1 := h8628c.2.1
                                              have p8628_2 := h8628c.2.2.1
                                              have p8628_3 := h8628c.2.2.2
                                              linarith only [h8483, hlam, p8628_1]
                                            · have p8628_0 := h8628c.1
                                              have p8628_1 := h8628c.2.1
                                              have p8628_2 := h8628c.2.2.1
                                              have p8628_3 := h8628c.2.2.2
                                              linarith only [h8483, h8488, h8492, hc23, hc34, hlam, hphi, p8628_1]
                                            · have p8628_0 := h8628c.1
                                              have p8628_1 := h8628c.2.1
                                              have p8628_2 := h8628c.2.2.1
                                              have p8628_3 := h8628c.2.2.2
                                              linarith only [h8475, hlam, p8628_1]
                                            · have p8628_0 := h8628c.1
                                              have p8628_1 := h8628c.2.1
                                              have p8628_2 := h8628c.2.2.1
                                              have p8628_3 := h8628c.2.2.2
                                              linarith only [h8482, hlam, p8628_1]
                                            · have p8628_0 := h8628c.1
                                              have p8628_1 := h8628c.2.1
                                              have p8628_2 := h8628c.2.2.1
                                              have p8628_3 := h8628c.2.2.2
                                              linarith only [hlam, p8628_0]
                                            · have p8628_0 := h8628c.1
                                              have p8628_1 := h8628c.2.1
                                              have p8628_2 := h8628c.2.2.1
                                              have p8628_3 := h8628c.2.2.2
                                              linarith only [h8488, hlam, p8628_1]
                                            · have p8628_0 := h8628c.1
                                              have p8628_1 := h8628c.2.1
                                              have p8628_2 := h8628c.2.2.1
                                              have p8628_3 := h8628c.2.2.2
                                              linarith only [h8492, hlam, p8628_0]
                                            · have p8628_0 := h8628c.1
                                              have p8628_1 := h8628c.2.1
                                              have p8628_2 := h8628c.2.2.1
                                              have p8628_3 := h8628c.2.2.2
                                              linarith only [h8480, h8488, h8492, hc23, hc34, hlam, hphi, p8628_1]
                                            · have p8628_0 := h8628c.1
                                              have p8628_1 := h8628c.2.1
                                              have p8628_2 := h8628c.2.2.1
                                              have p8628_3 := h8628c.2.2.2
                                              linarith only [h7360, h7361, h8481, hc23, hc34, hlam, hphi, p8628_1]
                                            · have p8628_0 := h8628c.1
                                              have p8628_1 := h8628c.2.1
                                              have p8628_2 := h8628c.2.2.1
                                              have p8628_3 := h8628c.2.2.2
                                              linarith only [h8488, hc23, hc34, hlam, hphi, p8628_1]
                                            · have p8628_0 := h8628c.1
                                              have p8628_1 := h8628c.2.1
                                              have p8628_2 := h8628c.2.2.1
                                              have p8628_3 := h8628c.2.2.2
                                              linarith only [hlam, p8628_0]
                                            · have p8628_0 := h8628c.1
                                              have p8628_1 := h8628c.2.1
                                              have p8628_2 := h8628c.2.2.1
                                              have p8628_3 := h8628c.2.2.2
                                              linarith only [h8488, h8492, hc23, hc34, hlam, hphi, p8628_1]
                                            · have p8628_0 := h8628c.1
                                              have p8628_1 := h8628c.2.1
                                              have p8628_2 := h8628c.2.2.1
                                              have p8628_3 := h8628c.2.2.2
                                              linarith only [h8480, hlam, p8628_0]
                                            · have p8628_0 := h8628c.1
                                              have p8628_1 := h8628c.2.1
                                              have p8628_2 := h8628c.2.2.1
                                              have p8628_3 := h8628c.2.2.2
                                              linarith only [h8487, hlam, p8628_0]
                                            · have p8628_0 := h8628c.1
                                              have p8628_1 := h8628c.2.1
                                              have p8628_2 := h8628c.2.2.1
                                              have p8628_3 := h8628c.2.2.2
                                              linarith only [h8480, h8488, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p8628_1]
                                            · have p8628_0 := h8628c.1
                                              have p8628_1 := h8628c.2.1
                                              have p8628_2 := h8628c.2.2.1
                                              have p8628_3 := h8628c.2.2.2
                                              linarith only [h8584, hlam, p8628_0]
                                            · have p8628_0 := h8628c.1
                                              have p8628_1 := h8628c.2.1
                                              have p8628_2 := h8628c.2.2.1
                                              have p8628_3 := h8628c.2.2.2
                                              linarith only [hlam, p8628_0]
                                          · linarith only [h8627, hlam, p8585_0]
                                        · linarith only [h8476, h8626, hlam]
                                · have p8585_0 := h8585c.1
                                  have p8585_1 := h8585c.2.1
                                  have p8585_2 := h8585c.2.2.1
                                  have p8585_3 := h8585c.2.2.2
                                  rcases p8585_3 (m.d 0 3) (by simp) with h8656 | h8656
                                  · linarith only [h8478, h8656, hlam]
                                  · linarith only [h7360, h8656, hlam]
                                · have p8585_0 := h8585c.1
                                  have p8585_1 := h8585c.2.1
                                  have p8585_2 := h8585c.2.2.1
                                  have p8585_3 := h8585c.2.2.2
                                  rcases p8585_3 (m.d 0 3) (by simp) with h8659 | h8659
                                  · linarith only [h8478, h8659, hlam]
                                  · linarith only [h8474, h8659, hlam]
                                · have p8585_0 := h8585c.1
                                  have p8585_1 := h8585c.2.1
                                  have p8585_2 := h8585c.2.2.1
                                  have p8585_3 := h8585c.2.2.2
                                  linarith only [h8584, hlam, p8585_0]
                                · have p8585_0 := h8585c.1
                                  have p8585_1 := h8585c.2.1
                                  have p8585_2 := h8585c.2.2.1
                                  have p8585_3 := h8585c.2.2.2
                                  linarith only [hlam, p8585_0]
                              · linarith only [h7361, h8480, h8483, h8584, hlam]
                      · linarith only [h7361, h8480, h8487, hlam]
                · linarith only [h0, h8475, h8482, hlam]
              · linarith only [h0, h8474, h8481, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h8668 | h8668
              · rcases m.htr 1 2 4 (by decide) (by decide) with h8669 | h8669
                · rcases m.htr 1 3 4 (by decide) (by decide) with h8670 | h8670
                  · linarith only [h7360, h8476, h8670, hlam]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h8672 | h8672
                    · linarith only [h7360, h8478, h8672, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h8674 | h8674
                      · linarith only [h7360, h7361, h8480, h8668, h8670, h8674, hc23, hc34, hlam, hphi]
                      · linarith only [h7360, h7361, h8668, h8674, hc23, hc45, hlam, hphi, ht34]
                · linarith only [h0, h8475, h8669, hlam]
              · linarith only [h0, h7360, h8474, h8668, hc02, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h8679 | h8679
        · linarith only [h0, h7360, h8475, h8679, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h8681 | h8681
          · linarith only [h7360, h8130, h8681, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h8683 | h8683
            · rcases m.htr 1 2 3 (by decide) (by decide) with h8684 | h8684
              · rcases m.htr 1 2 4 (by decide) (by decide) with h8685 | h8685
                · rcases m.htr 1 3 4 (by decide) (by decide) with h8686 | h8686
                  · linarith only [h0, h7360, h8475, h8679, h8685, h8686, hc03, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h8688 | h8688
                    · linarith only [h7360, h8130, h8681, h8688, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h8690 | h8690
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h8691 | h8691
                        · linarith only [h7361, h8474, h8475, h8685, h8686, h8691, hc01, hc12, hlam, hphi]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h8693 | h8693
                          · linarith only [h7360, h8130, h8684, h8688, h8693, hlam]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h8695 | h8695
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h8696 | h8696
                              · rcases h3bigk with h8697c | h8697c | h8697c | h8697c | h8697c | h8697c | h8697c | h8697c | h8697c | h8697c | h8697c | h8697c | h8697c | h8697c | h8697c | h8697c | h8697c | h8697c | h8697c | h8697c | h8697c | h8697c | h8697c | h8697c | h8697c
                                · have p8697_0 := h8697c.1
                                  have p8697_1 := h8697c.2.1
                                  have p8697_2 := h8697c.2.2.1
                                  have p8697_3 := h8697c.2.2.2
                                  linarith only [hlam, p8697_0]
                                · have p8697_0 := h8697c.1
                                  have p8697_1 := h8697c.2.1
                                  have p8697_2 := h8697c.2.2.1
                                  have p8697_3 := h8697c.2.2.2
                                  linarith only [h7360, h8130, h8684, h8688, hc23, hc35, hlam, hphi, p8697_1]
                                · have p8697_0 := h8697c.1
                                  have p8697_1 := h8697c.2.1
                                  have p8697_2 := h8697c.2.2.1
                                  have p8697_3 := h8697c.2.2.2
                                  linarith only [h0, h7360, h8475, h8685, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8697_1]
                                · have p8697_0 := h8697c.1
                                  have p8697_1 := h8697c.2.1
                                  have p8697_2 := h8697c.2.2.1
                                  have p8697_3 := h8697c.2.2.2
                                  linarith only [h8679, hlam, p8697_0]
                                · have p8697_0 := h8697c.1
                                  have p8697_1 := h8697c.2.1
                                  have p8697_2 := h8697c.2.2.1
                                  have p8697_3 := h8697c.2.2.2
                                  linarith only [h8681, hlam, p8697_0]
                                · have p8697_0 := h8697c.1
                                  have p8697_1 := h8697c.2.1
                                  have p8697_2 := h8697c.2.2.1
                                  have p8697_3 := h8697c.2.2.2
                                  linarith only [h7360, hlam, p8697_0]
                                · have p8697_0 := h8697c.1
                                  have p8697_1 := h8697c.2.1
                                  have p8697_2 := h8697c.2.2.1
                                  have p8697_3 := h8697c.2.2.2
                                  linarith only [hlam, p8697_0]
                                · have p8697_0 := h8697c.1
                                  have p8697_1 := h8697c.2.1
                                  have p8697_2 := h8697c.2.2.1
                                  have p8697_3 := h8697c.2.2.2
                                  linarith only [h0, h7360, h8475, h8685, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8697_1]
                                · have p8697_0 := h8697c.1
                                  have p8697_1 := h8697c.2.1
                                  have p8697_2 := h8697c.2.2.1
                                  have p8697_3 := h8697c.2.2.2
                                  linarith only [h8686, hlam, p8697_0]
                                · have p8697_0 := h8697c.1
                                  have p8697_1 := h8697c.2.1
                                  have p8697_2 := h8697c.2.2.1
                                  have p8697_3 := h8697c.2.2.2
                                  linarith only [h8688, hlam, p8697_0]
                                · have p8697_0 := h8697c.1
                                  have p8697_1 := h8697c.2.1
                                  have p8697_2 := h8697c.2.2.1
                                  have p8697_3 := h8697c.2.2.2
                                  linarith only [h8474, hlam, p8697_0]
                                · have p8697_0 := h8697c.1
                                  have p8697_1 := h8697c.2.1
                                  have p8697_2 := h8697c.2.2.1
                                  have p8697_3 := h8697c.2.2.2
                                  linarith only [h8684, hlam, p8697_0]
                                · have p8697_0 := h8697c.1
                                  have p8697_1 := h8697c.2.1
                                  have p8697_2 := h8697c.2.2.1
                                  have p8697_3 := h8697c.2.2.2
                                  linarith only [hlam, p8697_0]
                                · have p8697_0 := h8697c.1
                                  have p8697_1 := h8697c.2.1
                                  have p8697_2 := h8697c.2.2.1
                                  have p8697_3 := h8697c.2.2.2
                                  linarith only [h8691, hlam, p8697_0]
                                · have p8697_0 := h8697c.1
                                  have p8697_1 := h8697c.2.1
                                  have p8697_2 := h8697c.2.2.1
                                  have p8697_3 := h8697c.2.2.2
                                  linarith only [h8693, hlam, p8697_0]
                                · have p8697_0 := h8697c.1
                                  have p8697_1 := h8697c.2.1
                                  have p8697_2 := h8697c.2.2.1
                                  have p8697_3 := h8697c.2.2.2
                                  rcases p8697_3 (m.d 0 3) (by simp) with h8713 | h8713
                                  · linarith only [h8713, hlam, p8697_0]
                                  · rcases p8697_3 (m.d 1 3) (by simp) with h8715 | h8715
                                    · linarith only [h8686, h8715, hlam]
                                    · rcases p8697_3 (m.d 2 3) (by simp) with h8717 | h8717
                                      · linarith only [h8691, h8717, hlam]
                                      · rcases p8697_3 (m.d 3 4) (by simp) with h8719 | h8719
                                        · rcases p8697_3 (m.d 3 5) (by simp) with h8720 | h8720
                                          · linarith only [h8696, h8720, hlam]
                                          · linarith only [h8681, h8720, hlam]
                                        · linarith only [h8719, hlam, p8697_0]
                                · have p8697_0 := h8697c.1
                                  have p8697_1 := h8697c.2.1
                                  have p8697_2 := h8697c.2.2.1
                                  have p8697_3 := h8697c.2.2.2
                                  rcases p8697_3 (m.d 0 3) (by simp) with h8724 | h8724
                                  · linarith only [h8679, h8724, hlam]
                                  · linarith only [h7360, h8724, hlam]
                                · have p8697_0 := h8697c.1
                                  have p8697_1 := h8697c.2.1
                                  have p8697_2 := h8697c.2.2.1
                                  have p8697_3 := h8697c.2.2.2
                                  rcases p8697_3 (m.d 0 3) (by simp) with h8727 | h8727
                                  · linarith only [h8679, h8727, hlam]
                                  · linarith only [h8474, h8727, hlam]
                                · have p8697_0 := h8697c.1
                                  have p8697_1 := h8697c.2.1
                                  have p8697_2 := h8697c.2.2.1
                                  have p8697_3 := h8697c.2.2.2
                                  linarith only [hlam, p8697_0]
                                · have p8697_0 := h8697c.1
                                  have p8697_1 := h8697c.2.1
                                  have p8697_2 := h8697c.2.2.1
                                  have p8697_3 := h8697c.2.2.2
                                  linarith only [h8681, hc03, hc34, hlam, hphi, p8697_1]
                                · have p8697_0 := h8697c.1
                                  have p8697_1 := h8697c.2.1
                                  have p8697_2 := h8697c.2.2.1
                                  have p8697_3 := h8697c.2.2.2
                                  rcases p8697_3 (m.d 0 3) (by simp) with h8732 | h8732
                                  · linarith only [h8732, hlam, p8697_0]
                                  · rcases p8697_3 (m.d 1 3) (by simp) with h8734 | h8734
                                    · linarith only [h8688, h8734, hlam]
                                    · rcases p8697_3 (m.d 2 3) (by simp) with h8736 | h8736
                                      · linarith only [h8693, h8736, hlam]
                                      · rcases p8697_3 (m.d 3 4) (by simp) with h8738 | h8738
                                        · rcases p8697_3 (m.d 3 5) (by simp) with h8739 | h8739
                                          · rcases h4bigk with h8740c | h8740c | h8740c | h8740c | h8740c | h8740c | h8740c | h8740c | h8740c | h8740c | h8740c | h8740c | h8740c | h8740c | h8740c | h8740c | h8740c | h8740c | h8740c | h8740c | h8740c | h8740c | h8740c | h8740c | h8740c
                                            · have p8740_0 := h8740c.1
                                              have p8740_1 := h8740c.2.1
                                              have p8740_2 := h8740c.2.2.1
                                              have p8740_3 := h8740c.2.2.2
                                              linarith only [hlam, p8740_0]
                                            · have p8740_0 := h8740c.1
                                              have p8740_1 := h8740c.2.1
                                              have p8740_2 := h8740c.2.2.1
                                              have p8740_3 := h8740c.2.2.2
                                              linarith only [h7361, hlam, p8740_0]
                                            · have p8740_0 := h8740c.1
                                              have p8740_1 := h8740c.2.1
                                              have p8740_2 := h8740c.2.2.1
                                              have p8740_3 := h8740c.2.2.2
                                              linarith only [h8475, hlam, p8740_0]
                                            · have p8740_0 := h8740c.1
                                              have p8740_1 := h8740c.2.1
                                              have p8740_2 := h8740c.2.2.1
                                              have p8740_3 := h8740c.2.2.2
                                              linarith only [h8679, hlam, p8740_0]
                                            · have p8740_0 := h8740c.1
                                              have p8740_1 := h8740c.2.1
                                              have p8740_2 := h8740c.2.2.1
                                              have p8740_3 := h8740c.2.2.2
                                              linarith only [h8475, h8685, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p8740_1]
                                            · have p8740_0 := h8740c.1
                                              have p8740_1 := h8740c.2.1
                                              have p8740_2 := h8740c.2.2.1
                                              have p8740_3 := h8740c.2.2.2
                                              linarith only [h7361, hc01, hc14, hlam, hphi, p8740_1]
                                            · have p8740_0 := h8740c.1
                                              have p8740_1 := h8740c.2.1
                                              have p8740_2 := h8740c.2.2.1
                                              have p8740_3 := h8740c.2.2.2
                                              linarith only [hlam, p8740_0]
                                            · have p8740_0 := h8740c.1
                                              have p8740_1 := h8740c.2.1
                                              have p8740_2 := h8740c.2.2.1
                                              have p8740_3 := h8740c.2.2.2
                                              linarith only [h0, h7360, h8475, h8684, h8685, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8740_1]
                                            · have p8740_0 := h8740c.1
                                              have p8740_1 := h8740c.2.1
                                              have p8740_2 := h8740c.2.2.1
                                              have p8740_3 := h8740c.2.2.2
                                              linarith only [h8686, hlam, p8740_1]
                                            · have p8740_0 := h8740c.1
                                              have p8740_1 := h8740c.2.1
                                              have p8740_2 := h8740c.2.2.1
                                              have p8740_3 := h8740c.2.2.2
                                              rcases p8740_3 (m.d 0 4) (by simp) with h8750 | h8750
                                              · linarith only [h7361, h8750, hlam]
                                              · linarith only [h8683, h8750, hlam]
                                            · have p8740_0 := h8740c.1
                                              have p8740_1 := h8740c.2.1
                                              have p8740_2 := h8740c.2.2.1
                                              have p8740_3 := h8740c.2.2.2
                                              linarith only [h0, h7360, h8475, h8684, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p8740_1]
                                            · have p8740_0 := h8740c.1
                                              have p8740_1 := h8740c.2.1
                                              have p8740_2 := h8740c.2.2.1
                                              have p8740_3 := h8740c.2.2.2
                                              linarith only [h8685, hlam, p8740_1]
                                            · have p8740_0 := h8740c.1
                                              have p8740_1 := h8740c.2.1
                                              have p8740_2 := h8740c.2.2.1
                                              have p8740_3 := h8740c.2.2.2
                                              linarith only [hlam, p8740_0]
                                            · have p8740_0 := h8740c.1
                                              have p8740_1 := h8740c.2.1
                                              have p8740_2 := h8740c.2.2.1
                                              have p8740_3 := h8740c.2.2.2
                                              linarith only [h8691, hlam, p8740_1]
                                            · have p8740_0 := h8740c.1
                                              have p8740_1 := h8740c.2.1
                                              have p8740_2 := h8740c.2.2.1
                                              have p8740_3 := h8740c.2.2.2
                                              linarith only [h8685, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p8740_1]
                                            · have p8740_0 := h8740c.1
                                              have p8740_1 := h8740c.2.1
                                              have p8740_2 := h8740c.2.2.1
                                              have p8740_3 := h8740c.2.2.2
                                              linarith only [h0, h7360, h8475, h8684, hc23, hc34, hlam, hphi, p8740_1]
                                            · have p8740_0 := h8740c.1
                                              have p8740_1 := h8740c.2.1
                                              have p8740_2 := h8740c.2.2.1
                                              have p8740_3 := h8740c.2.2.2
                                              linarith only [h7360, h7361, h8684, hc23, hc34, hlam, hphi, p8740_1]
                                            · have p8740_0 := h8740c.1
                                              have p8740_1 := h8740c.2.1
                                              have p8740_2 := h8740c.2.2.1
                                              have p8740_3 := h8740c.2.2.2
                                              linarith only [h0, h7360, h8475, h8684, hc23, hc34, hlam, hphi, p8740_1]
                                            · have p8740_0 := h8740c.1
                                              have p8740_1 := h8740c.2.1
                                              have p8740_2 := h8740c.2.2.1
                                              have p8740_3 := h8740c.2.2.2
                                              linarith only [hlam, p8740_0]
                                            · have p8740_0 := h8740c.1
                                              have p8740_1 := h8740c.2.1
                                              have p8740_2 := h8740c.2.2.1
                                              have p8740_3 := h8740c.2.2.2
                                              rcases p8740_3 (m.d 0 4) (by simp) with h8762 | h8762
                                              · linarith only [h8679, h8762, hlam]
                                              · linarith only [h8683, h8762, hlam]
                                            · have p8740_0 := h8740c.1
                                              have p8740_1 := h8740c.2.1
                                              have p8740_2 := h8740c.2.2.1
                                              have p8740_3 := h8740c.2.2.2
                                              linarith only [h8683, hlam, p8740_0]
                                            · have p8740_0 := h8740c.1
                                              have p8740_1 := h8740c.2.1
                                              have p8740_2 := h8740c.2.2.1
                                              have p8740_3 := h8740c.2.2.2
                                              linarith only [h8690, hlam, p8740_0]
                                            · have p8740_0 := h8740c.1
                                              have p8740_1 := h8740c.2.1
                                              have p8740_2 := h8740c.2.2.1
                                              have p8740_3 := h8740c.2.2.2
                                              linarith only [h8695, hlam, p8740_0]
                                            · have p8740_0 := h8740c.1
                                              have p8740_1 := h8740c.2.1
                                              have p8740_2 := h8740c.2.2.1
                                              have p8740_3 := h8740c.2.2.2
                                              linarith only [h8696, hlam, p8740_0]
                                            · have p8740_0 := h8740c.1
                                              have p8740_1 := h8740c.2.1
                                              have p8740_2 := h8740c.2.2.1
                                              have p8740_3 := h8740c.2.2.2
                                              linarith only [hlam, p8740_0]
                                          · linarith only [h8739, hlam, p8697_0]
                                        · linarith only [h8679, h8738, hlam]
                                · have p8697_0 := h8697c.1
                                  have p8697_1 := h8697c.2.1
                                  have p8697_2 := h8697c.2.2.1
                                  have p8697_3 := h8697c.2.2.2
                                  rcases p8697_3 (m.d 0 3) (by simp) with h8772 | h8772
                                  · linarith only [h8681, h8772, hlam]
                                  · linarith only [h7360, h8772, hlam]
                                · have p8697_0 := h8697c.1
                                  have p8697_1 := h8697c.2.1
                                  have p8697_2 := h8697c.2.2.1
                                  have p8697_3 := h8697c.2.2.2
                                  rcases p8697_3 (m.d 0 3) (by simp) with h8775 | h8775
                                  · linarith only [h8681, h8775, hlam]
                                  · linarith only [h8474, h8775, hlam]
                                · have p8697_0 := h8697c.1
                                  have p8697_1 := h8697c.2.1
                                  have p8697_2 := h8697c.2.2.1
                                  have p8697_3 := h8697c.2.2.2
                                  linarith only [h8696, hlam, p8697_0]
                                · have p8697_0 := h8697c.1
                                  have p8697_1 := h8697c.2.1
                                  have p8697_2 := h8697c.2.2.1
                                  have p8697_3 := h8697c.2.2.2
                                  linarith only [hlam, p8697_0]
                              · linarith only [h8679, h8683, h8696, hlam]
                            · linarith only [h8475, h8683, h8695, hlam]
                      · linarith only [h7360, h7361, h8475, h8683, h8684, h8685, h8690, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h8783 | h8783
                  · linarith only [h0, h7360, h8679, h8685, h8783, hc04, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h8785 | h8785
                    · linarith only [h0, h7360, h8685, h8785, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h8787 | h8787
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h8788 | h8788
                        · linarith only [h0, h7360, h8684, h8685, h8783, h8788, hlam]
                        · linarith only [h0, h7360, h8684, h8685, h8788, hc23, hc34, hlam, hphi]
                      · linarith only [h0, h7360, h8684, h8685, h8787, hc23, hc45, hlam, hphi, ht34]
              · linarith only [h0, h7360, h8474, h8475, h8684, hc04, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h8793 | h8793
              · rcases m.htr 1 2 4 (by decide) (by decide) with h8794 | h8794
                · rcases m.htr 1 3 4 (by decide) (by decide) with h8795 | h8795
                  · linarith only [h0, h7360, h8475, h8794, h8795, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h8797 | h8797
                    · linarith only [h0, h7360, h8475, h8794, h8797, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h8799 | h8799
                      · linarith only [h7360, h7361, h8683, h8795, h8799, hc13, hc34, hlam, hphi]
                      · linarith only [h7360, h7361, h8793, h8799, hc23, hc45, hlam, hphi, ht34]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h8802 | h8802
                  · linarith only [h0, h7360, h8794, h8802, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h8804 | h8804
                    · linarith only [h0, h7360, h8794, h8804, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h8806 | h8806
                      · linarith only [h0, h7360, h8475, h8683, h8802, h8806, hc13, hc34, hlam, hphi]
                      · linarith only [h7360, h7361, h8793, h8806, hc23, hc45, hlam, hphi, ht34]
              · linarith only [h0, h7360, h8474, h8793, hc02, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
    · linarith only [h0, h7360, h8474, hlam]

set_option maxHeartbeats 16646000 in
set_option maxHeartbeats 16646000 in
theorem r1l7_13_24_L_I_H_I_s8_x0 (m : N7Model)
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h7360 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
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
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  have h0 := hg0
  rcases m.htr 0 1 4 (by decide) (by decide) with h7361 | h7361
  · exact r1l7_13_24_L_I_H_I_s8_x0_x0 m hb3 hb4 hg0 h7360 h7361
  · exact r1l7_13_24_L_I_H_I_s8_x0_x1 m hb3 hb4 hg0 h7360 h7361

set_option maxHeartbeats 16646000 in
set_option maxHeartbeats 16646000 in
theorem r1l7_13_24_L_I_H_I_s8_x1 (m : N7Model)
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h7360 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
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
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  have h0 := hg0
  exact r1l7_13_24_L_I_H_I_s9 m hb3 hb4 h0 h7360

set_option maxHeartbeats 16646000 in
set_option maxHeartbeats 16646000 in
theorem r1l7_13_24_L_I_H_I_s8 (m : N7Model)
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
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
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  have h0 := hg0
  rcases m.htr 0 1 3 (by decide) (by decide) with h7360 | h7360
  · exact r1l7_13_24_L_I_H_I_s8_x0 m hb3 hb4 hg0 h7360
  · exact r1l7_13_24_L_I_H_I_s8_x1 m hb3 hb4 hg0 h7360

set_option maxHeartbeats 31366000 in
set_option maxHeartbeats 31366000 in
theorem r1l7_13_24_L_I_H_I (m : N7Model)
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · exact r1l7_13_24_L_I_H_I_s0 m hb3 hb4 h0
  · exact r1l7_13_24_L_I_H_I_s8 m hb3 hb4 h0

end R2N4
