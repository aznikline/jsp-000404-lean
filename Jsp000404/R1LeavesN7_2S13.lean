import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_2S11
import Jsp000404.R1LeavesN7_2S12

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5198000 in
set_option maxHeartbeats 5198000 in
theorem r1l7_10_12_23_L_I_L_I_H_I_s13_x0_x0_x1_x1_x1_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (hg7337 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (hg8360 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (hg9250 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h9251 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h9252 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h9253 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h9255 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (h9257 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
    (h9259 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h9260 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h7337 := hg7337
  have h8360 := hg8360
  have h9250 := hg9250
  rcases m.htr 1 4 5 (by decide) (by decide) with h10085 | h10085
  · linarith only [h10085, h9259, h9260, hlam]
  · rcases m.htr 2 3 4 (by decide) (by decide) with h10087 | h10087
    · rcases m.htr 2 3 5 (by decide) (by decide) with h10088 | h10088
      · rcases m.htr 2 4 5 (by decide) (by decide) with h10089 | h10089
        · rcases m.htr 3 4 5 (by decide) (by decide) with h10090 | h10090
          · linarith only [h10085, h10090, h9251, h9259, h9260, hc03, hc14, hlam, hphi, ht0b, ht45, ht5b]
          · rcases h0bigk with h10092c | h10092c | h10092c | h10092c | h10092c | h10092c | h10092c | h10092c | h10092c | h10092c | h10092c | h10092c | h10092c | h10092c | h10092c | h10092c | h10092c | h10092c | h10092c | h10092c | h10092c | h10092c | h10092c | h10092c | h10092c
            · have p10092_0 := h10092c.1
              have p10092_1 := h10092c.2.1
              have p10092_2 := h10092c.2.2.1
              have p10092_3 := h10092c.2.2.2
              linarith only [hlam, p10092_0]
            · have p10092_0 := h10092c.1
              have p10092_1 := h10092c.2.1
              have p10092_2 := h10092c.2.2.1
              have p10092_3 := h10092c.2.2.2
              rcases p10092_3 (m.d 0 1) (by simp) with h10094 | h10094
              · rcases p10092_3 (m.d 0 2) (by simp) with h10095 | h10095
                · linarith only [h0, h10095, hlam]
                · rcases p10092_3 (m.d 0 3) (by simp) with h10097 | h10097
                  · linarith only [h1, h10097, hlam]
                  · linarith only [h10097, h4, hlam]
              · linarith only [h0, h10094, hlam]
            · have p10092_0 := h10092c.1
              have p10092_1 := h10092c.2.1
              have p10092_2 := h10092c.2.2.1
              have p10092_3 := h10092c.2.2.2
              linarith only [h10090, h9250, h9252, h9260, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p10092_1]
            · have p10092_0 := h10092c.1
              have p10092_1 := h10092c.2.1
              have p10092_2 := h10092c.2.2.1
              have p10092_3 := h10092c.2.2.2
              linarith only [h10090, h9252, h9259, h9260, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p10092_1]
            · have p10092_0 := h10092c.1
              have p10092_1 := h10092c.2.1
              have p10092_2 := h10092c.2.2.1
              have p10092_3 := h10092c.2.2.2
              linarith only [h10090, h9252, h9259, h9260, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p10092_1]
            · have p10092_0 := h10092c.1
              have p10092_1 := h10092c.2.1
              have p10092_2 := h10092c.2.2.1
              have p10092_3 := h10092c.2.2.2
              linarith only [h0, hlam, p10092_0]
            · have p10092_0 := h10092c.1
              have p10092_1 := h10092c.2.1
              have p10092_2 := h10092c.2.2.1
              have p10092_3 := h10092c.2.2.2
              linarith only [hlam, p10092_0]
            · have p10092_0 := h10092c.1
              have p10092_1 := h10092c.2.1
              have p10092_2 := h10092c.2.2.1
              have p10092_3 := h10092c.2.2.2
              linarith only [h4, hlam, p10092_0]
            · have p10092_0 := h10092c.1
              have p10092_1 := h10092c.2.1
              have p10092_2 := h10092c.2.2.1
              have p10092_3 := h10092c.2.2.2
              linarith only [h7337, hlam, p10092_1]
            · have p10092_0 := h10092c.1
              have p10092_1 := h10092c.2.1
              have p10092_2 := h10092c.2.2.1
              have p10092_3 := h10092c.2.2.2
              linarith only [h8360, hlam, p10092_0]
            · have p10092_0 := h10092c.1
              have p10092_1 := h10092c.2.1
              have p10092_2 := h10092c.2.2.1
              have p10092_3 := h10092c.2.2.2
              linarith only [h1, hlam, p10092_1]
            · have p10092_0 := h10092c.1
              have p10092_1 := h10092c.2.1
              have p10092_2 := h10092c.2.2.1
              have p10092_3 := h10092c.2.2.2
              rcases p10092_3 (m.d 0 1) (by simp) with h10110 | h10110
              · rcases p10092_3 (m.d 0 2) (by simp) with h10111 | h10111
                · linarith only [h10111, h4, hlam]
                · rcases p10092_3 (m.d 0 3) (by simp) with h10113 | h10113
                  · rcases p10092_3 (m.d 0 4) (by simp) with h10114 | h10114
                    · linarith only [h10114, h9250, hlam]
                    · linarith only [h10114, h7337, hlam]
                  · linarith only [h10113, h4, hlam]
              · linarith only [h0, h10110, hlam]
            · have p10092_0 := h10092c.1
              have p10092_1 := h10092c.2.1
              have p10092_2 := h10092c.2.2.1
              have p10092_3 := h10092c.2.2.2
              linarith only [hlam, p10092_0]
            · have p10092_0 := h10092c.1
              have p10092_1 := h10092c.2.1
              have p10092_2 := h10092c.2.2.1
              have p10092_3 := h10092c.2.2.2
              linarith only [h10090, h9252, h9259, h9260, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p10092_1]
            · have p10092_0 := h10092c.1
              have p10092_1 := h10092c.2.1
              have p10092_2 := h10092c.2.2.1
              have p10092_3 := h10092c.2.2.2
              linarith only [h10090, h4, h9252, h9259, h9260, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p10092_1]
            · have p10092_0 := h10092c.1
              have p10092_1 := h10092c.2.1
              have p10092_2 := h10092c.2.2.1
              have p10092_3 := h10092c.2.2.2
              linarith only [h2, hlam, p10092_0]
            · have p10092_0 := h10092c.1
              have p10092_1 := h10092c.2.1
              have p10092_2 := h10092c.2.2.1
              have p10092_3 := h10092c.2.2.2
              rcases p10092_3 (m.d 0 1) (by simp) with h10123 | h10123
              · rcases p10092_3 (m.d 0 2) (by simp) with h10124 | h10124
                · linarith only [h10124, h7337, hlam]
                · rcases p10092_3 (m.d 0 3) (by simp) with h10126 | h10126
                  · rcases p10092_3 (m.d 0 4) (by simp) with h10127 | h10127
                    · rcases p10092_3 (m.d 0 5) (by simp) with h10128 | h10128
                      · linarith only [h10128, h9252, hlam]
                      · linarith only [h10128, h8360, hlam]
                    · linarith only [h10127, h7337, hlam]
                  · linarith only [h10126, h4, hlam]
              · linarith only [h0, h10123, hlam]
            · have p10092_0 := h10092c.1
              have p10092_1 := h10092c.2.1
              have p10092_2 := h10092c.2.2.1
              have p10092_3 := h10092c.2.2.2
              linarith only [h9250, hlam, p10092_0]
            · have p10092_0 := h10092c.1
              have p10092_1 := h10092c.2.1
              have p10092_2 := h10092c.2.2.1
              have p10092_3 := h10092c.2.2.2
              linarith only [hlam, p10092_0]
            · have p10092_0 := h10092c.1
              have p10092_1 := h10092c.2.1
              have p10092_2 := h10092c.2.2.1
              have p10092_3 := h10092c.2.2.2
              linarith only [h10090, h9252, h9259, h9260, hc04, hc34, hlam, hphi, ht0b, ht45, ht5b, p10092_1]
            · have p10092_0 := h10092c.1
              have p10092_1 := h10092c.2.1
              have p10092_2 := h10092c.2.2.1
              have p10092_3 := h10092c.2.2.2
              linarith only [h3, hlam, p10092_0]
            · have p10092_0 := h10092c.1
              have p10092_1 := h10092c.2.1
              have p10092_2 := h10092c.2.2.1
              have p10092_3 := h10092c.2.2.2
              rcases p10092_3 (m.d 0 1) (by simp) with h10138 | h10138
              · rcases p10092_3 (m.d 0 2) (by simp) with h10139 | h10139
                · linarith only [h10139, h8360, hlam]
                · rcases p10092_3 (m.d 0 3) (by simp) with h10141 | h10141
                  · rcases p10092_3 (m.d 0 4) (by simp) with h10142 | h10142
                    · rcases p10092_3 (m.d 0 5) (by simp) with h10143 | h10143
                      · rcases h2bigk with h10144c | h10144c | h10144c | h10144c | h10144c | h10144c | h10144c | h10144c | h10144c | h10144c | h10144c | h10144c | h10144c | h10144c | h10144c | h10144c | h10144c | h10144c | h10144c | h10144c | h10144c | h10144c | h10144c | h10144c | h10144c
                        · have p10144_0 := h10144c.1
                          have p10144_1 := h10144c.2.1
                          have p10144_2 := h10144c.2.2.1
                          have p10144_3 := h10144c.2.2.2
                          linarith only [hlam, p10144_0]
                        · have p10144_0 := h10144c.1
                          have p10144_1 := h10144c.2.1
                          have p10144_2 := h10144c.2.2.1
                          have p10144_3 := h10144c.2.2.2
                          linarith only [hc05, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p10092_1, p10144_1]
                        · have p10144_0 := h10144c.1
                          have p10144_1 := h10144c.2.1
                          have p10144_2 := h10144c.2.2.1
                          have p10144_3 := h10144c.2.2.2
                          linarith only [h4, hlam, p10144_0]
                        · have p10144_0 := h10144c.1
                          have p10144_1 := h10144c.2.1
                          have p10144_2 := h10144c.2.2.1
                          have p10144_3 := h10144c.2.2.2
                          linarith only [h7337, hlam, p10144_0]
                        · have p10144_0 := h10144c.1
                          have p10144_1 := h10144c.2.1
                          have p10144_2 := h10144c.2.2.1
                          have p10144_3 := h10144c.2.2.2
                          linarith only [h8360, hlam, p10144_0]
                        · have p10144_0 := h10144c.1
                          have p10144_1 := h10144c.2.1
                          have p10144_2 := h10144c.2.2.1
                          have p10144_3 := h10144c.2.2.2
                          linarith only [h0, hlam, p10144_0]
                        · have p10144_0 := h10144c.1
                          have p10144_1 := h10144c.2.1
                          have p10144_2 := h10144c.2.2.1
                          have p10144_3 := h10144c.2.2.2
                          linarith only [hlam, p10144_0]
                        · have p10144_0 := h10144c.1
                          have p10144_1 := h10144c.2.1
                          have p10144_2 := h10144c.2.2.1
                          have p10144_3 := h10144c.2.2.2
                          linarith only [h9253, hlam, p10144_0]
                        · have p10144_0 := h10144c.1
                          have p10144_1 := h10144c.2.1
                          have p10144_2 := h10144c.2.2.1
                          have p10144_3 := h10144c.2.2.2
                          linarith only [h9255, hlam, p10144_0]
                        · have p10144_0 := h10144c.1
                          have p10144_1 := h10144c.2.1
                          have p10144_2 := h10144c.2.2.1
                          have p10144_3 := h10144c.2.2.2
                          linarith only [h9257, hlam, p10144_0]
                        · have p10144_0 := h10144c.1
                          have p10144_1 := h10144c.2.1
                          have p10144_2 := h10144c.2.2.1
                          have p10144_3 := h10144c.2.2.2
                          rcases p10144_3 (m.d 0 2) (by simp) with h10155 | h10155
                          · linarith only [h10155, hlam, p10144_0]
                          · rcases p10144_3 (m.d 1 2) (by simp) with h10157 | h10157
                            · linarith only [h10157, h9253, hlam]
                            · rcases p10144_3 (m.d 2 3) (by simp) with h10159 | h10159
                              · rcases p10144_3 (m.d 2 4) (by simp) with h10160 | h10160
                                · linarith only [h10087, h10160, hlam]
                                · linarith only [h10160, h7337, hlam]
                              · linarith only [h10159, hlam, p10144_0]
                        · have p10144_0 := h10144c.1
                          have p10144_1 := h10144c.2.1
                          have p10144_2 := h10144c.2.2.1
                          have p10144_3 := h10144c.2.2.2
                          rcases p10144_3 (m.d 0 2) (by simp) with h10164 | h10164
                          · linarith only [h10164, h4, hlam]
                          · linarith only [h0, h10164, hlam]
                        · have p10144_0 := h10144c.1
                          have p10144_1 := h10144c.2.1
                          have p10144_2 := h10144c.2.2.1
                          have p10144_3 := h10144c.2.2.2
                          linarith only [hlam, p10144_0]
                        · have p10144_0 := h10144c.1
                          have p10144_1 := h10144c.2.1
                          have p10144_2 := h10144c.2.2.1
                          have p10144_3 := h10144c.2.2.2
                          linarith only [h10090, h7337, h9252, h9259, h9260, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p10144_1]
                        · have p10144_0 := h10144c.1
                          have p10144_1 := h10144c.2.1
                          have p10144_2 := h10144c.2.2.1
                          have p10144_3 := h10144c.2.2.2
                          linarith only [h8360, hc02, hc23, hlam, hphi, p10144_1]
                        · have p10144_0 := h10144c.1
                          have p10144_1 := h10144c.2.1
                          have p10144_2 := h10144c.2.2.1
                          have p10144_3 := h10144c.2.2.2
                          rcases p10144_3 (m.d 0 2) (by simp) with h10170 | h10170
                          · linarith only [h10170, hlam, p10144_0]
                          · rcases p10144_3 (m.d 1 2) (by simp) with h10172 | h10172
                            · linarith only [h10172, h9255, hlam]
                            · rcases p10144_3 (m.d 2 3) (by simp) with h10174 | h10174
                              · rcases p10144_3 (m.d 2 4) (by simp) with h10175 | h10175
                                · rcases p10144_3 (m.d 2 5) (by simp) with h10176 | h10176
                                  · linarith only [h10089, h10176, hlam]
                                  · linarith only [h10176, h8360, hlam]
                                · linarith only [h10175, hlam, p10144_0]
                              · linarith only [h10174, h4, hlam]
                        · have p10144_0 := h10144c.1
                          have p10144_1 := h10144c.2.1
                          have p10144_2 := h10144c.2.2.1
                          have p10144_3 := h10144c.2.2.2
                          rcases p10144_3 (m.d 0 2) (by simp) with h10181 | h10181
                          · linarith only [h10181, h7337, hlam]
                          · linarith only [h0, h10181, hlam]
                        · have p10144_0 := h10144c.1
                          have p10144_1 := h10144c.2.1
                          have p10144_2 := h10144c.2.2.1
                          have p10144_3 := h10144c.2.2.2
                          linarith only [h10087, hlam, p10144_1]
                        · have p10144_0 := h10144c.1
                          have p10144_1 := h10144c.2.1
                          have p10144_2 := h10144c.2.2.1
                          have p10144_3 := h10144c.2.2.2
                          linarith only [hlam, p10144_0]
                        · have p10144_0 := h10144c.1
                          have p10144_1 := h10144c.2.1
                          have p10144_2 := h10144c.2.2.1
                          have p10144_3 := h10144c.2.2.2
                          linarith only [h0, h8360, hc12, hc24, hlam, hphi, p10092_1, p10144_1]
                        · have p10144_0 := h10144c.1
                          have p10144_1 := h10144c.2.1
                          have p10144_2 := h10144c.2.2.1
                          have p10144_3 := h10144c.2.2.2
                          rcases p10144_3 (m.d 0 2) (by simp) with h10187 | h10187
                          · linarith only [h10187, hlam, p10144_0]
                          · rcases p10144_3 (m.d 1 2) (by simp) with h10189 | h10189
                            · linarith only [h10189, h9257, hlam]
                            · rcases p10144_3 (m.d 2 3) (by simp) with h10191 | h10191
                              · rcases p10144_3 (m.d 2 4) (by simp) with h10192 | h10192
                                · rcases p10144_3 (m.d 2 5) (by simp) with h10193 | h10193
                                  · rcases h3bigk with h10194c | h10194c | h10194c | h10194c | h10194c | h10194c | h10194c | h10194c | h10194c | h10194c | h10194c | h10194c | h10194c | h10194c | h10194c | h10194c | h10194c | h10194c | h10194c | h10194c | h10194c | h10194c | h10194c | h10194c | h10194c
                                    · have p10194_0 := h10194c.1
                                      have p10194_1 := h10194c.2.1
                                      have p10194_2 := h10194c.2.2.1
                                      have p10194_3 := h10194c.2.2.2
                                      linarith only [hlam, p10194_0]
                                    · have p10194_0 := h10194c.1
                                      have p10194_1 := h10194c.2.1
                                      have p10194_2 := h10194c.2.2.1
                                      have p10194_3 := h10194c.2.2.2
                                      linarith only [h4, h9259, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p10194_1]
                                    · have p10194_0 := h10194c.1
                                      have p10194_1 := h10194c.2.1
                                      have p10194_2 := h10194c.2.2.1
                                      have p10194_3 := h10194c.2.2.2
                                      linarith only [h4, hlam, p10194_1]
                                    · have p10194_0 := h10194c.1
                                      have p10194_1 := h10194c.2.1
                                      have p10194_2 := h10194c.2.2.1
                                      have p10194_3 := h10194c.2.2.2
                                      rcases p10194_3 (m.d 0 3) (by simp) with h10198 | h10198
                                      · rcases p10194_3 (m.d 1 3) (by simp) with h10199 | h10199
                                        · linarith only [h1, h10199, hlam]
                                        · linarith only [h10199, h9259, hlam]
                                      · linarith only [h10198, hlam, p10194_0]
                                    · have p10194_0 := h10194c.1
                                      have p10194_1 := h10194c.2.1
                                      have p10194_2 := h10194c.2.2.1
                                      have p10194_3 := h10194c.2.2.2
                                      linarith only [h4, h9259, h9260, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p10194_1]
                                    · have p10194_0 := h10194c.1
                                      have p10194_1 := h10194c.2.1
                                      have p10194_2 := h10194c.2.2.1
                                      have p10194_3 := h10194c.2.2.2
                                      linarith only [h1, hlam, p10194_0]
                                    · have p10194_0 := h10194c.1
                                      have p10194_1 := h10194c.2.1
                                      have p10194_2 := h10194c.2.2.1
                                      have p10194_3 := h10194c.2.2.2
                                      linarith only [hlam, p10194_0]
                                    · have p10194_0 := h10194c.1
                                      have p10194_1 := h10194c.2.1
                                      have p10194_2 := h10194c.2.2.1
                                      have p10194_3 := h10194c.2.2.2
                                      linarith only [h9253, hlam, p10194_1]
                                    · have p10194_0 := h10194c.1
                                      have p10194_1 := h10194c.2.1
                                      have p10194_2 := h10194c.2.2.1
                                      have p10194_3 := h10194c.2.2.2
                                      linarith only [h10090, h9252, h9260, hc04, hc34, hlam, hphi, ht0b, ht45, ht5b, p10194_1]
                                    · have p10194_0 := h10194c.1
                                      have p10194_1 := h10194c.2.1
                                      have p10194_2 := h10194c.2.2.1
                                      have p10194_3 := h10194c.2.2.2
                                      linarith only [h9260, hlam, p10194_0]
                                    · have p10194_0 := h10194c.1
                                      have p10194_1 := h10194c.2.1
                                      have p10194_2 := h10194c.2.2.1
                                      have p10194_3 := h10194c.2.2.2
                                      linarith only [h0, h4, hc12, hc23, hlam, hphi, p10194_1]
                                    · have p10194_0 := h10194c.1
                                      have p10194_1 := h10194c.2.1
                                      have p10194_2 := h10194c.2.2.1
                                      have p10194_3 := h10194c.2.2.2
                                      linarith only [h9253, hc12, hc23, hlam, hphi, p10194_1]
                                    · have p10194_0 := h10194c.1
                                      have p10194_1 := h10194c.2.1
                                      have p10194_2 := h10194c.2.2.1
                                      have p10194_3 := h10194c.2.2.2
                                      linarith only [hlam, p10194_0]
                                    · have p10194_0 := h10194c.1
                                      have p10194_1 := h10194c.2.1
                                      have p10194_2 := h10194c.2.2.1
                                      have p10194_3 := h10194c.2.2.2
                                      rcases p10194_3 (m.d 0 3) (by simp) with h10212 | h10212
                                      · linarith only [h10212, h4, hlam]
                                      · linarith only [h10212, h9250, hlam]
                                    · have p10194_0 := h10194c.1
                                      have p10194_1 := h10194c.2.1
                                      have p10194_2 := h10194c.2.2.1
                                      have p10194_3 := h10194c.2.2.2
                                      linarith only [h9257, h9260, hc12, hc23, hlam, hphi, p10194_1]
                                    · have p10194_0 := h10194c.1
                                      have p10194_1 := h10194c.2.1
                                      have p10194_2 := h10194c.2.2.1
                                      have p10194_3 := h10194c.2.2.2
                                      linarith only [h9250, hlam, p10194_0]
                                    · have p10194_0 := h10194c.1
                                      have p10194_1 := h10194c.2.1
                                      have p10194_2 := h10194c.2.2.1
                                      have p10194_3 := h10194c.2.2.2
                                      linarith only [h9259, hlam, p10194_0]
                                    · have p10194_0 := h10194c.1
                                      have p10194_1 := h10194c.2.1
                                      have p10194_2 := h10194c.2.2.1
                                      have p10194_3 := h10194c.2.2.2
                                      linarith only [h10087, hlam, p10194_0]
                                    · have p10194_0 := h10194c.1
                                      have p10194_1 := h10194c.2.1
                                      have p10194_2 := h10194c.2.2.1
                                      have p10194_3 := h10194c.2.2.2
                                      linarith only [hlam, p10194_0]
                                    · have p10194_0 := h10194c.1
                                      have p10194_1 := h10194c.2.1
                                      have p10194_2 := h10194c.2.2.1
                                      have p10194_3 := h10194c.2.2.2
                                      linarith only [h10090, hlam, p10194_1]
                                    · have p10194_0 := h10194c.1
                                      have p10194_1 := h10194c.2.1
                                      have p10194_2 := h10194c.2.2.1
                                      have p10194_3 := h10194c.2.2.2
                                      linarith only [h9251, hlam, p10194_0]
                                    · have p10194_0 := h10194c.1
                                      have p10194_1 := h10194c.2.1
                                      have p10194_2 := h10194c.2.2.1
                                      have p10194_3 := h10194c.2.2.2
                                      linarith only [h9259, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p10194_1]
                                    · have p10194_0 := h10194c.1
                                      have p10194_1 := h10194c.2.1
                                      have p10194_2 := h10194c.2.2.1
                                      have p10194_3 := h10194c.2.2.2
                                      linarith only [h10088, hlam, p10194_0]
                                    · have p10194_0 := h10194c.1
                                      have p10194_1 := h10194c.2.1
                                      have p10194_2 := h10194c.2.2.1
                                      have p10194_3 := h10194c.2.2.2
                                      linarith only [h10087, h10090, h7337, h9252, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p10194_1]
                                    · have p10194_0 := h10194c.1
                                      have p10194_1 := h10194c.2.1
                                      have p10194_2 := h10194c.2.2.1
                                      have p10194_3 := h10194c.2.2.2
                                      linarith only [hlam, p10194_0]
                                  · linarith only [h10193, hlam, p10144_0]
                                · linarith only [h10192, h7337, hlam]
                              · linarith only [h10191, h4, hlam]
                        · have p10144_0 := h10144c.1
                          have p10144_1 := h10144c.2.1
                          have p10144_2 := h10144c.2.2.1
                          have p10144_3 := h10144c.2.2.2
                          rcases p10144_3 (m.d 0 2) (by simp) with h10229 | h10229
                          · linarith only [h10229, h8360, hlam]
                          · linarith only [h0, h10229, hlam]
                        · have p10144_0 := h10144c.1
                          have p10144_1 := h10144c.2.1
                          have p10144_2 := h10144c.2.2.1
                          have p10144_3 := h10144c.2.2.2
                          linarith only [h10088, hlam, p10144_1]
                        · have p10144_0 := h10144c.1
                          have p10144_1 := h10144c.2.1
                          have p10144_2 := h10144c.2.2.1
                          have p10144_3 := h10144c.2.2.2
                          linarith only [h10089, hlam, p10144_0]
                        · have p10144_0 := h10144c.1
                          have p10144_1 := h10144c.2.1
                          have p10144_2 := h10144c.2.2.1
                          have p10144_3 := h10144c.2.2.2
                          linarith only [hlam, p10144_0]
                      · linarith only [h10143, h8360, hlam]
                    · linarith only [h10142, h7337, hlam]
                  · linarith only [h10141, h4, hlam]
              · linarith only [h0, h10138, hlam]
            · have p10092_0 := h10092c.1
              have p10092_1 := h10092c.2.1
              have p10092_2 := h10092c.2.2.1
              have p10092_3 := h10092c.2.2.2
              linarith only [h9251, hlam, p10092_0]
            · have p10092_0 := h10092c.1
              have p10092_1 := h10092c.2.1
              have p10092_2 := h10092c.2.2.1
              have p10092_3 := h10092c.2.2.2
              linarith only [h9252, hlam, p10092_1]
            · have p10092_0 := h10092c.1
              have p10092_1 := h10092c.2.1
              have p10092_2 := h10092c.2.2.1
              have p10092_3 := h10092c.2.2.2
              linarith only [hlam, p10092_0]
        · linarith only [h10089, h7337, h9252, hlam]
      · linarith only [h10088, h4, h9251, hlam]
    · linarith only [h1, h10087, h4, h9251, h9259, hc01, hc35, hlam, hphi, ht0b, ht5b]

set_option maxHeartbeats 5198000 in
set_option maxHeartbeats 5198000 in
theorem r1l7_10_12_23_L_I_L_I_H_I_s13_x0_x0_x1_x1_x1_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (hg7337 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (hg8360 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (hg9250 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h9251 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h9252 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h9253 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h9255 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (h9257 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
    (h9259 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h7337 := hg7337
  have h8360 := hg8360
  have h9250 := hg9250
  rcases m.htr 1 3 5 (by decide) (by decide) with h9260 | h9260
  · exact r1l7_10_12_23_L_I_L_I_H_I_s13_x0_x0_x1_x1_x1_x0_x0 m hb0 hb2 hb3 hg0 hg1 hg2 hg3 hg4 hg7337 hg8360 hg9250 h9251 h9252 h9253 h9255 h9257 h9259 h9260
  · exact r1l7_10_12_23_L_I_L_I_H_I_s13_x0_x0_x1_x1_x1_x0_x1 m hb0 hb2 hb3 hg0 hg1 hg2 hg3 hg4 hg7337 hg8360 hg9250 h9251 h9252 h9253 h9255 h9257 h9259 h9260

set_option maxHeartbeats 5198000 in
set_option maxHeartbeats 5198000 in
theorem r1l7_10_12_23_L_I_L_I_H_I_s13_x0_x0_x1_x1_x1_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (hg7337 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (hg8360 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (hg9250 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h9251 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h9252 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h9253 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h9255 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (h9257 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
    (h9259 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h7337 := hg7337
  have h8360 := hg8360
  have h9250 := hg9250
  rcases m.htr 1 3 5 (by decide) (by decide) with h10245 | h10245
  · rcases m.htr 1 4 5 (by decide) (by decide) with h10246 | h10246
    · rcases m.htr 2 3 4 (by decide) (by decide) with h10247 | h10247
      · rcases m.htr 2 3 5 (by decide) (by decide) with h10248 | h10248
        · rcases m.htr 2 4 5 (by decide) (by decide) with h10249 | h10249
          · rcases m.htr 3 4 5 (by decide) (by decide) with h10250 | h10250
            · rcases h0bigk with h10251c | h10251c | h10251c | h10251c | h10251c | h10251c | h10251c | h10251c | h10251c | h10251c | h10251c | h10251c | h10251c | h10251c | h10251c | h10251c | h10251c | h10251c | h10251c | h10251c | h10251c | h10251c | h10251c | h10251c | h10251c
              · have p10251_0 := h10251c.1
                have p10251_1 := h10251c.2.1
                have p10251_2 := h10251c.2.2.1
                have p10251_3 := h10251c.2.2.2
                linarith only [hlam, p10251_0]
              · have p10251_0 := h10251c.1
                have p10251_1 := h10251c.2.1
                have p10251_2 := h10251c.2.2.1
                have p10251_3 := h10251c.2.2.2
                rcases p10251_3 (m.d 0 1) (by simp) with h10253 | h10253
                · rcases p10251_3 (m.d 0 2) (by simp) with h10254 | h10254
                  · linarith only [h0, h10254, hlam]
                  · rcases p10251_3 (m.d 0 3) (by simp) with h10256 | h10256
                    · linarith only [h1, h10256, hlam]
                    · linarith only [h10256, h4, hlam]
                · linarith only [h0, h10253, hlam]
              · have p10251_0 := h10251c.1
                have p10251_1 := h10251c.2.1
                have p10251_2 := h10251c.2.2.1
                have p10251_3 := h10251c.2.2.2
                linarith only [h10245, h10250, h9250, h9259, hc01, hc45, hlam, hphi, ht0b, ht5b, p10251_1]
              · have p10251_0 := h10251c.1
                have p10251_1 := h10251c.2.1
                have p10251_2 := h10251c.2.2.1
                have p10251_3 := h10251c.2.2.2
                linarith only [h10245, h10250, h9250, h9259, hc01, hc45, hlam, hphi, ht0b, ht5b, p10251_1]
              · have p10251_0 := h10251c.1
                have p10251_1 := h10251c.2.1
                have p10251_2 := h10251c.2.2.1
                have p10251_3 := h10251c.2.2.2
                rcases p10251_3 (m.d 0 1) (by simp) with h10262 | h10262
                · rcases p10251_3 (m.d 0 2) (by simp) with h10263 | h10263
                  · linarith only [h0, h10263, hlam]
                  · rcases p10251_3 (m.d 0 3) (by simp) with h10265 | h10265
                    · linarith only [h1, h10265, hlam]
                    · linarith only [h10265, h9251, hlam]
                · linarith only [h10262, h3, hlam]
              · have p10251_0 := h10251c.1
                have p10251_1 := h10251c.2.1
                have p10251_2 := h10251c.2.2.1
                have p10251_3 := h10251c.2.2.2
                linarith only [h0, hlam, p10251_0]
              · have p10251_0 := h10251c.1
                have p10251_1 := h10251c.2.1
                have p10251_2 := h10251c.2.2.1
                have p10251_3 := h10251c.2.2.2
                linarith only [hlam, p10251_0]
              · have p10251_0 := h10251c.1
                have p10251_1 := h10251c.2.1
                have p10251_2 := h10251c.2.2.1
                have p10251_3 := h10251c.2.2.2
                linarith only [h4, hlam, p10251_0]
              · have p10251_0 := h10251c.1
                have p10251_1 := h10251c.2.1
                have p10251_2 := h10251c.2.2.1
                have p10251_3 := h10251c.2.2.2
                linarith only [h7337, hlam, p10251_1]
              · have p10251_0 := h10251c.1
                have p10251_1 := h10251c.2.1
                have p10251_2 := h10251c.2.2.1
                have p10251_3 := h10251c.2.2.2
                linarith only [h8360, hlam, p10251_0]
              · have p10251_0 := h10251c.1
                have p10251_1 := h10251c.2.1
                have p10251_2 := h10251c.2.2.1
                have p10251_3 := h10251c.2.2.2
                linarith only [h1, hlam, p10251_1]
              · have p10251_0 := h10251c.1
                have p10251_1 := h10251c.2.1
                have p10251_2 := h10251c.2.2.1
                have p10251_3 := h10251c.2.2.2
                rcases p10251_3 (m.d 0 1) (by simp) with h10275 | h10275
                · rcases p10251_3 (m.d 0 2) (by simp) with h10276 | h10276
                  · linarith only [h10276, h4, hlam]
                  · rcases p10251_3 (m.d 0 3) (by simp) with h10278 | h10278
                    · rcases p10251_3 (m.d 0 4) (by simp) with h10279 | h10279
                      · linarith only [h10279, h9250, hlam]
                      · linarith only [h10279, h7337, hlam]
                    · linarith only [h10278, h4, hlam]
                · linarith only [h0, h10275, hlam]
              · have p10251_0 := h10251c.1
                have p10251_1 := h10251c.2.1
                have p10251_2 := h10251c.2.2.1
                have p10251_3 := h10251c.2.2.2
                linarith only [hlam, p10251_0]
              · have p10251_0 := h10251c.1
                have p10251_1 := h10251c.2.1
                have p10251_2 := h10251c.2.2.1
                have p10251_3 := h10251c.2.2.2
                linarith only [h10245, h10250, h9250, h9259, hc03, hc45, hlam, hphi, ht0b, ht5b, p10251_1]
              · have p10251_0 := h10251c.1
                have p10251_1 := h10251c.2.1
                have p10251_2 := h10251c.2.2.1
                have p10251_3 := h10251c.2.2.2
                rcases p10251_3 (m.d 0 1) (by simp) with h10286 | h10286
                · rcases p10251_3 (m.d 0 2) (by simp) with h10287 | h10287
                  · linarith only [h10287, h4, hlam]
                  · rcases p10251_3 (m.d 0 3) (by simp) with h10289 | h10289
                    · rcases p10251_3 (m.d 0 4) (by simp) with h10290 | h10290
                      · linarith only [h10290, h9250, hlam]
                      · linarith only [h10290, h9252, hlam]
                    · linarith only [h10289, h9251, hlam]
                · linarith only [h10286, h3, hlam]
              · have p10251_0 := h10251c.1
                have p10251_1 := h10251c.2.1
                have p10251_2 := h10251c.2.2.1
                have p10251_3 := h10251c.2.2.2
                linarith only [h2, hlam, p10251_0]
              · have p10251_0 := h10251c.1
                have p10251_1 := h10251c.2.1
                have p10251_2 := h10251c.2.2.1
                have p10251_3 := h10251c.2.2.2
                rcases p10251_3 (m.d 0 1) (by simp) with h10296 | h10296
                · rcases p10251_3 (m.d 0 2) (by simp) with h10297 | h10297
                  · linarith only [h10297, h7337, hlam]
                  · rcases p10251_3 (m.d 0 3) (by simp) with h10299 | h10299
                    · rcases p10251_3 (m.d 0 4) (by simp) with h10300 | h10300
                      · rcases p10251_3 (m.d 0 5) (by simp) with h10301 | h10301
                        · linarith only [h10301, h9252, hlam]
                        · linarith only [h10301, h8360, hlam]
                      · linarith only [h10300, h7337, hlam]
                    · linarith only [h10299, h4, hlam]
                · linarith only [h0, h10296, hlam]
              · have p10251_0 := h10251c.1
                have p10251_1 := h10251c.2.1
                have p10251_2 := h10251c.2.2.1
                have p10251_3 := h10251c.2.2.2
                linarith only [h9250, hlam, p10251_0]
              · have p10251_0 := h10251c.1
                have p10251_1 := h10251c.2.1
                have p10251_2 := h10251c.2.2.1
                have p10251_3 := h10251c.2.2.2
                linarith only [hlam, p10251_0]
              · have p10251_0 := h10251c.1
                have p10251_1 := h10251c.2.1
                have p10251_2 := h10251c.2.2.1
                have p10251_3 := h10251c.2.2.2
                rcases p10251_3 (m.d 0 1) (by simp) with h10309 | h10309
                · rcases p10251_3 (m.d 0 2) (by simp) with h10310 | h10310
                  · linarith only [h10310, h7337, hlam]
                  · rcases p10251_3 (m.d 0 3) (by simp) with h10312 | h10312
                    · rcases p10251_3 (m.d 0 4) (by simp) with h10313 | h10313
                      · rcases p10251_3 (m.d 0 5) (by simp) with h10314 | h10314
                        · linarith only [h10314, h9252, hlam]
                        · rcases h2bigk with h10316c | h10316c | h10316c | h10316c | h10316c | h10316c | h10316c | h10316c | h10316c | h10316c | h10316c | h10316c | h10316c | h10316c | h10316c | h10316c | h10316c | h10316c | h10316c | h10316c | h10316c | h10316c | h10316c | h10316c | h10316c
                          · have p10316_0 := h10316c.1
                            have p10316_1 := h10316c.2.1
                            have p10316_2 := h10316c.2.2.1
                            have p10316_3 := h10316c.2.2.2
                            linarith only [hlam, p10316_0]
                          · have p10316_0 := h10316c.1
                            have p10316_1 := h10316c.2.1
                            have p10316_2 := h10316c.2.2.1
                            have p10316_3 := h10316c.2.2.2
                            linarith only [h8360, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p10251_1, p10316_1]
                          · have p10316_0 := h10316c.1
                            have p10316_1 := h10316c.2.1
                            have p10316_2 := h10316c.2.2.1
                            have p10316_3 := h10316c.2.2.2
                            linarith only [h4, hlam, p10316_0]
                          · have p10316_0 := h10316c.1
                            have p10316_1 := h10316c.2.1
                            have p10316_2 := h10316c.2.2.1
                            have p10316_3 := h10316c.2.2.2
                            linarith only [h7337, hlam, p10316_0]
                          · have p10316_0 := h10316c.1
                            have p10316_1 := h10316c.2.1
                            have p10316_2 := h10316c.2.2.1
                            have p10316_3 := h10316c.2.2.2
                            linarith only [h8360, hlam, p10316_0]
                          · have p10316_0 := h10316c.1
                            have p10316_1 := h10316c.2.1
                            have p10316_2 := h10316c.2.2.1
                            have p10316_3 := h10316c.2.2.2
                            linarith only [h0, hlam, p10316_0]
                          · have p10316_0 := h10316c.1
                            have p10316_1 := h10316c.2.1
                            have p10316_2 := h10316c.2.2.1
                            have p10316_3 := h10316c.2.2.2
                            linarith only [hlam, p10316_0]
                          · have p10316_0 := h10316c.1
                            have p10316_1 := h10316c.2.1
                            have p10316_2 := h10316c.2.2.1
                            have p10316_3 := h10316c.2.2.2
                            linarith only [h9253, hlam, p10316_0]
                          · have p10316_0 := h10316c.1
                            have p10316_1 := h10316c.2.1
                            have p10316_2 := h10316c.2.2.1
                            have p10316_3 := h10316c.2.2.2
                            linarith only [h9255, hlam, p10316_0]
                          · have p10316_0 := h10316c.1
                            have p10316_1 := h10316c.2.1
                            have p10316_2 := h10316c.2.2.1
                            have p10316_3 := h10316c.2.2.2
                            linarith only [h9257, hlam, p10316_0]
                          · have p10316_0 := h10316c.1
                            have p10316_1 := h10316c.2.1
                            have p10316_2 := h10316c.2.2.1
                            have p10316_3 := h10316c.2.2.2
                            rcases p10316_3 (m.d 0 2) (by simp) with h10327 | h10327
                            · linarith only [h10327, hlam, p10316_0]
                            · rcases p10316_3 (m.d 1 2) (by simp) with h10329 | h10329
                              · linarith only [h10329, h9253, hlam]
                              · rcases p10316_3 (m.d 2 3) (by simp) with h10331 | h10331
                                · rcases p10316_3 (m.d 2 4) (by simp) with h10332 | h10332
                                  · linarith only [h10247, h10332, hlam]
                                  · linarith only [h10332, h7337, hlam]
                                · linarith only [h10331, hlam, p10316_0]
                          · have p10316_0 := h10316c.1
                            have p10316_1 := h10316c.2.1
                            have p10316_2 := h10316c.2.2.1
                            have p10316_3 := h10316c.2.2.2
                            rcases p10316_3 (m.d 0 2) (by simp) with h10336 | h10336
                            · linarith only [h10336, h4, hlam]
                            · linarith only [h0, h10336, hlam]
                          · have p10316_0 := h10316c.1
                            have p10316_1 := h10316c.2.1
                            have p10316_2 := h10316c.2.2.1
                            have p10316_3 := h10316c.2.2.2
                            linarith only [hlam, p10316_0]
                          · have p10316_0 := h10316c.1
                            have p10316_1 := h10316c.2.1
                            have p10316_2 := h10316c.2.2.1
                            have p10316_3 := h10316c.2.2.2
                            linarith only [h7337, hc02, hc23, hlam, hphi, p10316_1]
                          · have p10316_0 := h10316c.1
                            have p10316_1 := h10316c.2.1
                            have p10316_2 := h10316c.2.2.1
                            have p10316_3 := h10316c.2.2.2
                            linarith only [h0, h8360, hc12, hc23, hlam, hphi, p10316_1]
                          · have p10316_0 := h10316c.1
                            have p10316_1 := h10316c.2.1
                            have p10316_2 := h10316c.2.2.1
                            have p10316_3 := h10316c.2.2.2
                            rcases p10316_3 (m.d 0 2) (by simp) with h10342 | h10342
                            · linarith only [h10342, hlam, p10316_0]
                            · rcases p10316_3 (m.d 1 2) (by simp) with h10344 | h10344
                              · linarith only [h10344, h9255, hlam]
                              · rcases p10316_3 (m.d 2 3) (by simp) with h10346 | h10346
                                · rcases p10316_3 (m.d 2 4) (by simp) with h10347 | h10347
                                  · rcases p10316_3 (m.d 2 5) (by simp) with h10348 | h10348
                                    · linarith only [h10249, h10348, hlam]
                                    · linarith only [h10348, h8360, hlam]
                                  · linarith only [h10347, hlam, p10316_0]
                                · linarith only [h10346, h4, hlam]
                          · have p10316_0 := h10316c.1
                            have p10316_1 := h10316c.2.1
                            have p10316_2 := h10316c.2.2.1
                            have p10316_3 := h10316c.2.2.2
                            rcases p10316_3 (m.d 0 2) (by simp) with h10353 | h10353
                            · linarith only [h10353, h7337, hlam]
                            · linarith only [h0, h10353, hlam]
                          · have p10316_0 := h10316c.1
                            have p10316_1 := h10316c.2.1
                            have p10316_2 := h10316c.2.2.1
                            have p10316_3 := h10316c.2.2.2
                            linarith only [h10247, hlam, p10316_1]
                          · have p10316_0 := h10316c.1
                            have p10316_1 := h10316c.2.1
                            have p10316_2 := h10316c.2.2.1
                            have p10316_3 := h10316c.2.2.2
                            linarith only [hlam, p10316_0]
                          · have p10316_0 := h10316c.1
                            have p10316_1 := h10316c.2.1
                            have p10316_2 := h10316c.2.2.1
                            have p10316_3 := h10316c.2.2.2
                            linarith only [h0, h8360, hc12, hc24, hlam, hphi, p10316_1]
                          · have p10316_0 := h10316c.1
                            have p10316_1 := h10316c.2.1
                            have p10316_2 := h10316c.2.2.1
                            have p10316_3 := h10316c.2.2.2
                            rcases p10316_3 (m.d 0 2) (by simp) with h10359 | h10359
                            · linarith only [h10359, hlam, p10316_0]
                            · rcases p10316_3 (m.d 1 2) (by simp) with h10361 | h10361
                              · linarith only [h10361, h9257, hlam]
                              · rcases p10316_3 (m.d 2 3) (by simp) with h10363 | h10363
                                · rcases p10316_3 (m.d 2 4) (by simp) with h10364 | h10364
                                  · rcases p10316_3 (m.d 2 5) (by simp) with h10365 | h10365
                                    · rcases h3bigk with h10366c | h10366c | h10366c | h10366c | h10366c | h10366c | h10366c | h10366c | h10366c | h10366c | h10366c | h10366c | h10366c | h10366c | h10366c | h10366c | h10366c | h10366c | h10366c | h10366c | h10366c | h10366c | h10366c | h10366c | h10366c
                                      · have p10366_0 := h10366c.1
                                        have p10366_1 := h10366c.2.1
                                        have p10366_2 := h10366c.2.2.1
                                        have p10366_3 := h10366c.2.2.2
                                        linarith only [hlam, p10366_0]
                                      · have p10366_0 := h10366c.1
                                        have p10366_1 := h10366c.2.1
                                        have p10366_2 := h10366c.2.2.1
                                        have p10366_3 := h10366c.2.2.2
                                        linarith only [h10245, h10250, h4, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p10366_1]
                                      · have p10366_0 := h10366c.1
                                        have p10366_1 := h10366c.2.1
                                        have p10366_2 := h10366c.2.2.1
                                        have p10366_3 := h10366c.2.2.2
                                        linarith only [h4, hlam, p10366_1]
                                      · have p10366_0 := h10366c.1
                                        have p10366_1 := h10366c.2.1
                                        have p10366_2 := h10366c.2.2.1
                                        have p10366_3 := h10366c.2.2.2
                                        linarith only [h10245, h10250, h4, h9259, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p10366_1]
                                      · have p10366_0 := h10366c.1
                                        have p10366_1 := h10366c.2.1
                                        have p10366_2 := h10366c.2.2.1
                                        have p10366_3 := h10366c.2.2.2
                                        rcases p10366_3 (m.d 0 3) (by simp) with h10371 | h10371
                                        · rcases p10366_3 (m.d 1 3) (by simp) with h10372 | h10372
                                          · linarith only [h1, h10372, hlam]
                                          · linarith only [h10245, h10372, hlam]
                                        · linarith only [h10371, hlam, p10366_0]
                                      · have p10366_0 := h10366c.1
                                        have p10366_1 := h10366c.2.1
                                        have p10366_2 := h10366c.2.2.1
                                        have p10366_3 := h10366c.2.2.2
                                        linarith only [h1, hlam, p10366_0]
                                      · have p10366_0 := h10366c.1
                                        have p10366_1 := h10366c.2.1
                                        have p10366_2 := h10366c.2.2.1
                                        have p10366_3 := h10366c.2.2.2
                                        linarith only [hlam, p10366_0]
                                      · have p10366_0 := h10366c.1
                                        have p10366_1 := h10366c.2.1
                                        have p10366_2 := h10366c.2.2.1
                                        have p10366_3 := h10366c.2.2.2
                                        linarith only [h9253, hlam, p10366_1]
                                      · have p10366_0 := h10366c.1
                                        have p10366_1 := h10366c.2.1
                                        have p10366_2 := h10366c.2.2.1
                                        have p10366_3 := h10366c.2.2.2
                                        linarith only [h9259, hlam, p10366_0]
                                      · have p10366_0 := h10366c.1
                                        have p10366_1 := h10366c.2.1
                                        have p10366_2 := h10366c.2.2.1
                                        have p10366_3 := h10366c.2.2.2
                                        linarith only [h10250, h9259, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p10366_1]
                                      · have p10366_0 := h10366c.1
                                        have p10366_1 := h10366c.2.1
                                        have p10366_2 := h10366c.2.2.1
                                        have p10366_3 := h10366c.2.2.2
                                        linarith only [h9250, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p10251_1, p10366_1]
                                      · have p10366_0 := h10366c.1
                                        have p10366_1 := h10366c.2.1
                                        have p10366_2 := h10366c.2.2.1
                                        have p10366_3 := h10366c.2.2.2
                                        linarith only [h9253, hc12, hc23, hlam, hphi, p10366_1]
                                      · have p10366_0 := h10366c.1
                                        have p10366_1 := h10366c.2.1
                                        have p10366_2 := h10366c.2.2.1
                                        have p10366_3 := h10366c.2.2.2
                                        linarith only [hlam, p10366_0]
                                      · have p10366_0 := h10366c.1
                                        have p10366_1 := h10366c.2.1
                                        have p10366_2 := h10366c.2.2.1
                                        have p10366_3 := h10366c.2.2.2
                                        linarith only [h9255, h9259, hc12, hc23, hlam, hphi, p10366_1]
                                      · have p10366_0 := h10366c.1
                                        have p10366_1 := h10366c.2.1
                                        have p10366_2 := h10366c.2.2.1
                                        have p10366_3 := h10366c.2.2.2
                                        rcases p10366_3 (m.d 0 3) (by simp) with h10385 | h10385
                                        · linarith only [h10385, h4, hlam]
                                        · linarith only [h10385, h9251, hlam]
                                      · have p10366_0 := h10366c.1
                                        have p10366_1 := h10366c.2.1
                                        have p10366_2 := h10366c.2.2.1
                                        have p10366_3 := h10366c.2.2.2
                                        linarith only [h9250, hlam, p10366_0]
                                      · have p10366_0 := h10366c.1
                                        have p10366_1 := h10366c.2.1
                                        have p10366_2 := h10366c.2.2.1
                                        have p10366_3 := h10366c.2.2.2
                                        linarith only [h10245, h10250, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p10366_1]
                                      · have p10366_0 := h10366c.1
                                        have p10366_1 := h10366c.2.1
                                        have p10366_2 := h10366c.2.2.1
                                        have p10366_3 := h10366c.2.2.2
                                        linarith only [h10247, hlam, p10366_0]
                                      · have p10366_0 := h10366c.1
                                        have p10366_1 := h10366c.2.1
                                        have p10366_2 := h10366c.2.2.1
                                        have p10366_3 := h10366c.2.2.2
                                        linarith only [hlam, p10366_0]
                                      · have p10366_0 := h10366c.1
                                        have p10366_1 := h10366c.2.1
                                        have p10366_2 := h10366c.2.2.1
                                        have p10366_3 := h10366c.2.2.2
                                        linarith only [h10250, h4, h9250, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p10366_1]
                                      · have p10366_0 := h10366c.1
                                        have p10366_1 := h10366c.2.1
                                        have p10366_2 := h10366c.2.2.1
                                        have p10366_3 := h10366c.2.2.2
                                        linarith only [h9251, hlam, p10366_0]
                                      · have p10366_0 := h10366c.1
                                        have p10366_1 := h10366c.2.1
                                        have p10366_2 := h10366c.2.2.1
                                        have p10366_3 := h10366c.2.2.2
                                        linarith only [h10245, hlam, p10366_0]
                                      · have p10366_0 := h10366c.1
                                        have p10366_1 := h10366c.2.1
                                        have p10366_2 := h10366c.2.2.1
                                        have p10366_3 := h10366c.2.2.2
                                        linarith only [h10248, hlam, p10366_0]
                                      · have p10366_0 := h10366c.1
                                        have p10366_1 := h10366c.2.1
                                        have p10366_2 := h10366c.2.2.1
                                        have p10366_3 := h10366c.2.2.2
                                        linarith only [h10250, hlam, p10366_0]
                                      · have p10366_0 := h10366c.1
                                        have p10366_1 := h10366c.2.1
                                        have p10366_2 := h10366c.2.2.1
                                        have p10366_3 := h10366c.2.2.2
                                        linarith only [hlam, p10366_0]
                                    · linarith only [h10365, hlam, p10316_0]
                                  · linarith only [h10364, h7337, hlam]
                                · linarith only [h10363, h4, hlam]
                          · have p10316_0 := h10316c.1
                            have p10316_1 := h10316c.2.1
                            have p10316_2 := h10316c.2.2.1
                            have p10316_3 := h10316c.2.2.2
                            rcases p10316_3 (m.d 0 2) (by simp) with h10401 | h10401
                            · linarith only [h10401, h8360, hlam]
                            · linarith only [h0, h10401, hlam]
                          · have p10316_0 := h10316c.1
                            have p10316_1 := h10316c.2.1
                            have p10316_2 := h10316c.2.2.1
                            have p10316_3 := h10316c.2.2.2
                            linarith only [h10248, hlam, p10316_1]
                          · have p10316_0 := h10316c.1
                            have p10316_1 := h10316c.2.1
                            have p10316_2 := h10316c.2.2.1
                            have p10316_3 := h10316c.2.2.2
                            linarith only [h10249, hlam, p10316_0]
                          · have p10316_0 := h10316c.1
                            have p10316_1 := h10316c.2.1
                            have p10316_2 := h10316c.2.2.1
                            have p10316_3 := h10316c.2.2.2
                            linarith only [hlam, p10316_0]
                      · linarith only [h10313, h9252, hlam]
                    · linarith only [h10312, h9251, hlam]
                · linarith only [h10309, h3, hlam]
              · have p10251_0 := h10251c.1
                have p10251_1 := h10251c.2.1
                have p10251_2 := h10251c.2.2.1
                have p10251_3 := h10251c.2.2.2
                linarith only [h3, hlam, p10251_0]
              · have p10251_0 := h10251c.1
                have p10251_1 := h10251c.2.1
                have p10251_2 := h10251c.2.2.1
                have p10251_3 := h10251c.2.2.2
                rcases p10251_3 (m.d 0 1) (by simp) with h10411 | h10411
                · rcases p10251_3 (m.d 0 2) (by simp) with h10412 | h10412
                  · linarith only [h10412, h8360, hlam]
                  · rcases p10251_3 (m.d 0 3) (by simp) with h10414 | h10414
                    · rcases p10251_3 (m.d 0 4) (by simp) with h10415 | h10415
                      · rcases p10251_3 (m.d 0 5) (by simp) with h10416 | h10416
                        · rcases h2bigk with h10417c | h10417c | h10417c | h10417c | h10417c | h10417c | h10417c | h10417c | h10417c | h10417c | h10417c | h10417c | h10417c | h10417c | h10417c | h10417c | h10417c | h10417c | h10417c | h10417c | h10417c | h10417c | h10417c | h10417c | h10417c
                          · have p10417_0 := h10417c.1
                            have p10417_1 := h10417c.2.1
                            have p10417_2 := h10417c.2.2.1
                            have p10417_3 := h10417c.2.2.2
                            linarith only [hlam, p10417_0]
                          · have p10417_0 := h10417c.1
                            have p10417_1 := h10417c.2.1
                            have p10417_2 := h10417c.2.2.1
                            have p10417_3 := h10417c.2.2.2
                            linarith only [hc05, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p10251_1, p10417_1]
                          · have p10417_0 := h10417c.1
                            have p10417_1 := h10417c.2.1
                            have p10417_2 := h10417c.2.2.1
                            have p10417_3 := h10417c.2.2.2
                            linarith only [h4, hlam, p10417_0]
                          · have p10417_0 := h10417c.1
                            have p10417_1 := h10417c.2.1
                            have p10417_2 := h10417c.2.2.1
                            have p10417_3 := h10417c.2.2.2
                            linarith only [h7337, hlam, p10417_0]
                          · have p10417_0 := h10417c.1
                            have p10417_1 := h10417c.2.1
                            have p10417_2 := h10417c.2.2.1
                            have p10417_3 := h10417c.2.2.2
                            linarith only [h8360, hlam, p10417_0]
                          · have p10417_0 := h10417c.1
                            have p10417_1 := h10417c.2.1
                            have p10417_2 := h10417c.2.2.1
                            have p10417_3 := h10417c.2.2.2
                            linarith only [h0, hlam, p10417_0]
                          · have p10417_0 := h10417c.1
                            have p10417_1 := h10417c.2.1
                            have p10417_2 := h10417c.2.2.1
                            have p10417_3 := h10417c.2.2.2
                            linarith only [hlam, p10417_0]
                          · have p10417_0 := h10417c.1
                            have p10417_1 := h10417c.2.1
                            have p10417_2 := h10417c.2.2.1
                            have p10417_3 := h10417c.2.2.2
                            linarith only [h9253, hlam, p10417_0]
                          · have p10417_0 := h10417c.1
                            have p10417_1 := h10417c.2.1
                            have p10417_2 := h10417c.2.2.1
                            have p10417_3 := h10417c.2.2.2
                            linarith only [h9255, hlam, p10417_0]
                          · have p10417_0 := h10417c.1
                            have p10417_1 := h10417c.2.1
                            have p10417_2 := h10417c.2.2.1
                            have p10417_3 := h10417c.2.2.2
                            linarith only [h9257, hlam, p10417_0]
                          · have p10417_0 := h10417c.1
                            have p10417_1 := h10417c.2.1
                            have p10417_2 := h10417c.2.2.1
                            have p10417_3 := h10417c.2.2.2
                            rcases p10417_3 (m.d 0 2) (by simp) with h10428 | h10428
                            · linarith only [h10428, hlam, p10417_0]
                            · rcases p10417_3 (m.d 1 2) (by simp) with h10430 | h10430
                              · linarith only [h10430, h9253, hlam]
                              · rcases p10417_3 (m.d 2 3) (by simp) with h10432 | h10432
                                · rcases p10417_3 (m.d 2 4) (by simp) with h10433 | h10433
                                  · linarith only [h10247, h10433, hlam]
                                  · linarith only [h10433, h7337, hlam]
                                · linarith only [h10432, hlam, p10417_0]
                          · have p10417_0 := h10417c.1
                            have p10417_1 := h10417c.2.1
                            have p10417_2 := h10417c.2.2.1
                            have p10417_3 := h10417c.2.2.2
                            rcases p10417_3 (m.d 0 2) (by simp) with h10437 | h10437
                            · linarith only [h10437, h4, hlam]
                            · linarith only [h0, h10437, hlam]
                          · have p10417_0 := h10417c.1
                            have p10417_1 := h10417c.2.1
                            have p10417_2 := h10417c.2.2.1
                            have p10417_3 := h10417c.2.2.2
                            linarith only [hlam, p10417_0]
                          · have p10417_0 := h10417c.1
                            have p10417_1 := h10417c.2.1
                            have p10417_2 := h10417c.2.2.1
                            have p10417_3 := h10417c.2.2.2
                            linarith only [h7337, h9252, hc02, hc23, hlam, hphi, p10251_1, p10417_1]
                          · have p10417_0 := h10417c.1
                            have p10417_1 := h10417c.2.1
                            have p10417_2 := h10417c.2.2.1
                            have p10417_3 := h10417c.2.2.2
                            linarith only [h0, h8360, hc12, hc23, hlam, hphi, p10417_1]
                          · have p10417_0 := h10417c.1
                            have p10417_1 := h10417c.2.1
                            have p10417_2 := h10417c.2.2.1
                            have p10417_3 := h10417c.2.2.2
                            rcases p10417_3 (m.d 0 2) (by simp) with h10443 | h10443
                            · linarith only [h10443, hlam, p10417_0]
                            · rcases p10417_3 (m.d 1 2) (by simp) with h10445 | h10445
                              · linarith only [h10445, h9255, hlam]
                              · rcases p10417_3 (m.d 2 3) (by simp) with h10447 | h10447
                                · rcases p10417_3 (m.d 2 4) (by simp) with h10448 | h10448
                                  · rcases p10417_3 (m.d 2 5) (by simp) with h10449 | h10449
                                    · linarith only [h10249, h10449, hlam]
                                    · linarith only [h10449, h8360, hlam]
                                  · linarith only [h10448, hlam, p10417_0]
                                · linarith only [h10447, h4, hlam]
                          · have p10417_0 := h10417c.1
                            have p10417_1 := h10417c.2.1
                            have p10417_2 := h10417c.2.2.1
                            have p10417_3 := h10417c.2.2.2
                            rcases p10417_3 (m.d 0 2) (by simp) with h10454 | h10454
                            · linarith only [h10454, h7337, hlam]
                            · linarith only [h0, h10454, hlam]
                          · have p10417_0 := h10417c.1
                            have p10417_1 := h10417c.2.1
                            have p10417_2 := h10417c.2.2.1
                            have p10417_3 := h10417c.2.2.2
                            linarith only [h10247, hlam, p10417_1]
                          · have p10417_0 := h10417c.1
                            have p10417_1 := h10417c.2.1
                            have p10417_2 := h10417c.2.2.1
                            have p10417_3 := h10417c.2.2.2
                            linarith only [hlam, p10417_0]
                          · have p10417_0 := h10417c.1
                            have p10417_1 := h10417c.2.1
                            have p10417_2 := h10417c.2.2.1
                            have p10417_3 := h10417c.2.2.2
                            linarith only [h0, h8360, hc12, hc24, hlam, hphi, p10251_1, p10417_1]
                          · have p10417_0 := h10417c.1
                            have p10417_1 := h10417c.2.1
                            have p10417_2 := h10417c.2.2.1
                            have p10417_3 := h10417c.2.2.2
                            rcases p10417_3 (m.d 0 2) (by simp) with h10460 | h10460
                            · linarith only [h10460, hlam, p10417_0]
                            · rcases p10417_3 (m.d 1 2) (by simp) with h10462 | h10462
                              · linarith only [h10462, h9257, hlam]
                              · rcases p10417_3 (m.d 2 3) (by simp) with h10464 | h10464
                                · rcases p10417_3 (m.d 2 4) (by simp) with h10465 | h10465
                                  · rcases p10417_3 (m.d 2 5) (by simp) with h10466 | h10466
                                    · rcases h3bigk with h10467c | h10467c | h10467c | h10467c | h10467c | h10467c | h10467c | h10467c | h10467c | h10467c | h10467c | h10467c | h10467c | h10467c | h10467c | h10467c | h10467c | h10467c | h10467c | h10467c | h10467c | h10467c | h10467c | h10467c | h10467c
                                      · have p10467_0 := h10467c.1
                                        have p10467_1 := h10467c.2.1
                                        have p10467_2 := h10467c.2.2.1
                                        have p10467_3 := h10467c.2.2.2
                                        linarith only [hlam, p10467_0]
                                      · have p10467_0 := h10467c.1
                                        have p10467_1 := h10467c.2.1
                                        have p10467_2 := h10467c.2.2.1
                                        have p10467_3 := h10467c.2.2.2
                                        linarith only [h10245, h10250, h4, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p10467_1]
                                      · have p10467_0 := h10467c.1
                                        have p10467_1 := h10467c.2.1
                                        have p10467_2 := h10467c.2.2.1
                                        have p10467_3 := h10467c.2.2.2
                                        linarith only [h4, hlam, p10467_1]
                                      · have p10467_0 := h10467c.1
                                        have p10467_1 := h10467c.2.1
                                        have p10467_2 := h10467c.2.2.1
                                        have p10467_3 := h10467c.2.2.2
                                        linarith only [h10245, h10250, h4, h9259, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p10467_1]
                                      · have p10467_0 := h10467c.1
                                        have p10467_1 := h10467c.2.1
                                        have p10467_2 := h10467c.2.2.1
                                        have p10467_3 := h10467c.2.2.2
                                        rcases p10467_3 (m.d 0 3) (by simp) with h10472 | h10472
                                        · rcases p10467_3 (m.d 1 3) (by simp) with h10473 | h10473
                                          · linarith only [h1, h10473, hlam]
                                          · linarith only [h10245, h10473, hlam]
                                        · linarith only [h10472, hlam, p10467_0]
                                      · have p10467_0 := h10467c.1
                                        have p10467_1 := h10467c.2.1
                                        have p10467_2 := h10467c.2.2.1
                                        have p10467_3 := h10467c.2.2.2
                                        linarith only [h1, hlam, p10467_0]
                                      · have p10467_0 := h10467c.1
                                        have p10467_1 := h10467c.2.1
                                        have p10467_2 := h10467c.2.2.1
                                        have p10467_3 := h10467c.2.2.2
                                        linarith only [hlam, p10467_0]
                                      · have p10467_0 := h10467c.1
                                        have p10467_1 := h10467c.2.1
                                        have p10467_2 := h10467c.2.2.1
                                        have p10467_3 := h10467c.2.2.2
                                        linarith only [h9253, hlam, p10467_1]
                                      · have p10467_0 := h10467c.1
                                        have p10467_1 := h10467c.2.1
                                        have p10467_2 := h10467c.2.2.1
                                        have p10467_3 := h10467c.2.2.2
                                        linarith only [h9259, hlam, p10467_0]
                                      · have p10467_0 := h10467c.1
                                        have p10467_1 := h10467c.2.1
                                        have p10467_2 := h10467c.2.2.1
                                        have p10467_3 := h10467c.2.2.2
                                        linarith only [h10250, h9259, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p10467_1]
                                      · have p10467_0 := h10467c.1
                                        have p10467_1 := h10467c.2.1
                                        have p10467_2 := h10467c.2.2.1
                                        have p10467_3 := h10467c.2.2.2
                                        linarith only [h0, h4, hc12, hc23, hlam, hphi, p10467_1]
                                      · have p10467_0 := h10467c.1
                                        have p10467_1 := h10467c.2.1
                                        have p10467_2 := h10467c.2.2.1
                                        have p10467_3 := h10467c.2.2.2
                                        linarith only [h9253, hc12, hc23, hlam, hphi, p10467_1]
                                      · have p10467_0 := h10467c.1
                                        have p10467_1 := h10467c.2.1
                                        have p10467_2 := h10467c.2.2.1
                                        have p10467_3 := h10467c.2.2.2
                                        linarith only [hlam, p10467_0]
                                      · have p10467_0 := h10467c.1
                                        have p10467_1 := h10467c.2.1
                                        have p10467_2 := h10467c.2.2.1
                                        have p10467_3 := h10467c.2.2.2
                                        linarith only [h10245, h10250, h9259, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p10467_1]
                                      · have p10467_0 := h10467c.1
                                        have p10467_1 := h10467c.2.1
                                        have p10467_2 := h10467c.2.2.1
                                        have p10467_3 := h10467c.2.2.2
                                        rcases p10467_3 (m.d 0 3) (by simp) with h10486 | h10486
                                        · linarith only [h10486, h4, hlam]
                                        · linarith only [h10486, h9251, hlam]
                                      · have p10467_0 := h10467c.1
                                        have p10467_1 := h10467c.2.1
                                        have p10467_2 := h10467c.2.2.1
                                        have p10467_3 := h10467c.2.2.2
                                        linarith only [h9250, hlam, p10467_0]
                                      · have p10467_0 := h10467c.1
                                        have p10467_1 := h10467c.2.1
                                        have p10467_2 := h10467c.2.2.1
                                        have p10467_3 := h10467c.2.2.2
                                        linarith only [h10245, h10250, h9250, hc03, hc45, hlam, hphi, ht0b, ht5b, p10467_1]
                                      · have p10467_0 := h10467c.1
                                        have p10467_1 := h10467c.2.1
                                        have p10467_2 := h10467c.2.2.1
                                        have p10467_3 := h10467c.2.2.2
                                        linarith only [h10247, hlam, p10467_0]
                                      · have p10467_0 := h10467c.1
                                        have p10467_1 := h10467c.2.1
                                        have p10467_2 := h10467c.2.2.1
                                        have p10467_3 := h10467c.2.2.2
                                        linarith only [hlam, p10467_0]
                                      · have p10467_0 := h10467c.1
                                        have p10467_1 := h10467c.2.1
                                        have p10467_2 := h10467c.2.2.1
                                        have p10467_3 := h10467c.2.2.2
                                        linarith only [h10250, h4, h9250, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p10467_1]
                                      · have p10467_0 := h10467c.1
                                        have p10467_1 := h10467c.2.1
                                        have p10467_2 := h10467c.2.2.1
                                        have p10467_3 := h10467c.2.2.2
                                        linarith only [h9251, hlam, p10467_0]
                                      · have p10467_0 := h10467c.1
                                        have p10467_1 := h10467c.2.1
                                        have p10467_2 := h10467c.2.2.1
                                        have p10467_3 := h10467c.2.2.2
                                        linarith only [h10245, hlam, p10467_0]
                                      · have p10467_0 := h10467c.1
                                        have p10467_1 := h10467c.2.1
                                        have p10467_2 := h10467c.2.2.1
                                        have p10467_3 := h10467c.2.2.2
                                        linarith only [h10248, hlam, p10467_0]
                                      · have p10467_0 := h10467c.1
                                        have p10467_1 := h10467c.2.1
                                        have p10467_2 := h10467c.2.2.1
                                        have p10467_3 := h10467c.2.2.2
                                        linarith only [h10250, hlam, p10467_0]
                                      · have p10467_0 := h10467c.1
                                        have p10467_1 := h10467c.2.1
                                        have p10467_2 := h10467c.2.2.1
                                        have p10467_3 := h10467c.2.2.2
                                        linarith only [hlam, p10467_0]
                                    · linarith only [h10466, hlam, p10417_0]
                                  · linarith only [h10465, h7337, hlam]
                                · linarith only [h10464, h4, hlam]
                          · have p10417_0 := h10417c.1
                            have p10417_1 := h10417c.2.1
                            have p10417_2 := h10417c.2.2.1
                            have p10417_3 := h10417c.2.2.2
                            rcases p10417_3 (m.d 0 2) (by simp) with h10502 | h10502
                            · linarith only [h10502, h8360, hlam]
                            · linarith only [h0, h10502, hlam]
                          · have p10417_0 := h10417c.1
                            have p10417_1 := h10417c.2.1
                            have p10417_2 := h10417c.2.2.1
                            have p10417_3 := h10417c.2.2.2
                            linarith only [h10248, hlam, p10417_1]
                          · have p10417_0 := h10417c.1
                            have p10417_1 := h10417c.2.1
                            have p10417_2 := h10417c.2.2.1
                            have p10417_3 := h10417c.2.2.2
                            linarith only [h10249, hlam, p10417_0]
                          · have p10417_0 := h10417c.1
                            have p10417_1 := h10417c.2.1
                            have p10417_2 := h10417c.2.2.1
                            have p10417_3 := h10417c.2.2.2
                            linarith only [hlam, p10417_0]
                        · linarith only [h10416, h8360, hlam]
                      · linarith only [h10415, h7337, hlam]
                    · linarith only [h10414, h4, hlam]
                · linarith only [h0, h10411, hlam]
              · have p10251_0 := h10251c.1
                have p10251_1 := h10251c.2.1
                have p10251_2 := h10251c.2.2.1
                have p10251_3 := h10251c.2.2.2
                linarith only [h9251, hlam, p10251_0]
              · have p10251_0 := h10251c.1
                have p10251_1 := h10251c.2.1
                have p10251_2 := h10251c.2.2.1
                have p10251_3 := h10251c.2.2.2
                linarith only [h9252, hlam, p10251_1]
              · have p10251_0 := h10251c.1
                have p10251_1 := h10251c.2.1
                have p10251_2 := h10251c.2.2.1
                have p10251_3 := h10251c.2.2.2
                linarith only [hlam, p10251_0]
            · linarith only [h10245, h10247, h10250, h7337, h9252, h9259, hc23, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
          · linarith only [h10246, h10249, h2, h7337, hlam]
        · linarith only [h1, h10245, h10248, h4, h9250, h9259, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
      · linarith only [h10247, h4, h9250, hlam]
    · linarith only [h10245, h10246, h9259, hlam]
  · rcases m.htr 1 4 5 (by decide) (by decide) with h10520 | h10520
    · rcases m.htr 2 3 4 (by decide) (by decide) with h10521 | h10521
      · rcases m.htr 2 3 5 (by decide) (by decide) with h10522 | h10522
        · rcases m.htr 2 4 5 (by decide) (by decide) with h10523 | h10523
          · rcases m.htr 3 4 5 (by decide) (by decide) with h10524 | h10524
            · rcases h0bigk with h10525c | h10525c | h10525c | h10525c | h10525c | h10525c | h10525c | h10525c | h10525c | h10525c | h10525c | h10525c | h10525c | h10525c | h10525c | h10525c | h10525c | h10525c | h10525c | h10525c | h10525c | h10525c | h10525c | h10525c | h10525c
              · have p10525_0 := h10525c.1
                have p10525_1 := h10525c.2.1
                have p10525_2 := h10525c.2.2.1
                have p10525_3 := h10525c.2.2.2
                linarith only [hlam, p10525_0]
              · have p10525_0 := h10525c.1
                have p10525_1 := h10525c.2.1
                have p10525_2 := h10525c.2.2.1
                have p10525_3 := h10525c.2.2.2
                rcases p10525_3 (m.d 0 1) (by simp) with h10527 | h10527
                · rcases p10525_3 (m.d 0 2) (by simp) with h10528 | h10528
                  · linarith only [h0, h10528, hlam]
                  · rcases p10525_3 (m.d 0 3) (by simp) with h10530 | h10530
                    · linarith only [h1, h10530, hlam]
                    · linarith only [h10530, h4, hlam]
                · linarith only [h0, h10527, hlam]
              · have p10525_0 := h10525c.1
                have p10525_1 := h10525c.2.1
                have p10525_2 := h10525c.2.2.1
                have p10525_3 := h10525c.2.2.2
                linarith only [h10520, h9250, h9259, hc01, hc45, hlam, hphi, ht0b, ht5b, p10525_1]
              · have p10525_0 := h10525c.1
                have p10525_1 := h10525c.2.1
                have p10525_2 := h10525c.2.2.1
                have p10525_3 := h10525c.2.2.2
                rcases p10525_3 (m.d 0 1) (by simp) with h10535 | h10535
                · rcases p10525_3 (m.d 0 2) (by simp) with h10536 | h10536
                  · linarith only [h0, h10536, hlam]
                  · rcases p10525_3 (m.d 0 3) (by simp) with h10538 | h10538
                    · linarith only [h1, h10538, hlam]
                    · linarith only [h10538, h9250, hlam]
                · linarith only [h10535, h2, hlam]
              · have p10525_0 := h10525c.1
                have p10525_1 := h10525c.2.1
                have p10525_2 := h10525c.2.2.1
                have p10525_3 := h10525c.2.2.2
                rcases p10525_3 (m.d 0 1) (by simp) with h10542 | h10542
                · rcases p10525_3 (m.d 0 2) (by simp) with h10543 | h10543
                  · linarith only [h0, h10543, hlam]
                  · rcases p10525_3 (m.d 0 3) (by simp) with h10545 | h10545
                    · linarith only [h1, h10545, hlam]
                    · linarith only [h10545, h9251, hlam]
                · linarith only [h10542, h3, hlam]
              · have p10525_0 := h10525c.1
                have p10525_1 := h10525c.2.1
                have p10525_2 := h10525c.2.2.1
                have p10525_3 := h10525c.2.2.2
                linarith only [h0, hlam, p10525_0]
              · have p10525_0 := h10525c.1
                have p10525_1 := h10525c.2.1
                have p10525_2 := h10525c.2.2.1
                have p10525_3 := h10525c.2.2.2
                linarith only [hlam, p10525_0]
              · have p10525_0 := h10525c.1
                have p10525_1 := h10525c.2.1
                have p10525_2 := h10525c.2.2.1
                have p10525_3 := h10525c.2.2.2
                linarith only [h4, hlam, p10525_0]
              · have p10525_0 := h10525c.1
                have p10525_1 := h10525c.2.1
                have p10525_2 := h10525c.2.2.1
                have p10525_3 := h10525c.2.2.2
                linarith only [h7337, hlam, p10525_1]
              · have p10525_0 := h10525c.1
                have p10525_1 := h10525c.2.1
                have p10525_2 := h10525c.2.2.1
                have p10525_3 := h10525c.2.2.2
                linarith only [h8360, hlam, p10525_0]
              · have p10525_0 := h10525c.1
                have p10525_1 := h10525c.2.1
                have p10525_2 := h10525c.2.2.1
                have p10525_3 := h10525c.2.2.2
                linarith only [h1, hlam, p10525_1]
              · have p10525_0 := h10525c.1
                have p10525_1 := h10525c.2.1
                have p10525_2 := h10525c.2.2.1
                have p10525_3 := h10525c.2.2.2
                rcases p10525_3 (m.d 0 1) (by simp) with h10555 | h10555
                · rcases p10525_3 (m.d 0 2) (by simp) with h10556 | h10556
                  · linarith only [h10556, h4, hlam]
                  · rcases p10525_3 (m.d 0 3) (by simp) with h10558 | h10558
                    · rcases p10525_3 (m.d 0 4) (by simp) with h10559 | h10559
                      · linarith only [h10559, h9250, hlam]
                      · linarith only [h10559, h7337, hlam]
                    · linarith only [h10558, h4, hlam]
                · linarith only [h0, h10555, hlam]
              · have p10525_0 := h10525c.1
                have p10525_1 := h10525c.2.1
                have p10525_2 := h10525c.2.2.1
                have p10525_3 := h10525c.2.2.2
                linarith only [hlam, p10525_0]
              · have p10525_0 := h10525c.1
                have p10525_1 := h10525c.2.1
                have p10525_2 := h10525c.2.2.1
                have p10525_3 := h10525c.2.2.2
                linarith only [h10245, h10524, h4, h9250, h9253, hc12, hc23, hlam, hphi, p10525_1]
              · have p10525_0 := h10525c.1
                have p10525_1 := h10525c.2.1
                have p10525_2 := h10525c.2.2.1
                have p10525_3 := h10525c.2.2.2
                linarith only [h10245, h4, h9251, h9253, hc12, hc23, hlam, hphi, p10525_1]
              · have p10525_0 := h10525c.1
                have p10525_1 := h10525c.2.1
                have p10525_2 := h10525c.2.2.1
                have p10525_3 := h10525c.2.2.2
                linarith only [h2, hlam, p10525_0]
              · have p10525_0 := h10525c.1
                have p10525_1 := h10525c.2.1
                have p10525_2 := h10525c.2.2.1
                have p10525_3 := h10525c.2.2.2
                rcases p10525_3 (m.d 0 1) (by simp) with h10568 | h10568
                · rcases p10525_3 (m.d 0 2) (by simp) with h10569 | h10569
                  · linarith only [h10569, h7337, hlam]
                  · rcases p10525_3 (m.d 0 3) (by simp) with h10571 | h10571
                    · rcases p10525_3 (m.d 0 4) (by simp) with h10572 | h10572
                      · rcases p10525_3 (m.d 0 5) (by simp) with h10573 | h10573
                        · linarith only [h10573, h9252, hlam]
                        · linarith only [h10573, h8360, hlam]
                      · linarith only [h10572, h7337, hlam]
                    · linarith only [h10571, h4, hlam]
                · linarith only [h0, h10568, hlam]
              · have p10525_0 := h10525c.1
                have p10525_1 := h10525c.2.1
                have p10525_2 := h10525c.2.2.1
                have p10525_3 := h10525c.2.2.2
                linarith only [h9250, hlam, p10525_0]
              · have p10525_0 := h10525c.1
                have p10525_1 := h10525c.2.1
                have p10525_2 := h10525c.2.2.1
                have p10525_3 := h10525c.2.2.2
                linarith only [hlam, p10525_0]
              · have p10525_0 := h10525c.1
                have p10525_1 := h10525c.2.1
                have p10525_2 := h10525c.2.2.1
                have p10525_3 := h10525c.2.2.2
                linarith only [h10245, h10521, h7337, h9251, h9253, hc12, hc23, hlam, hphi, p10525_1]
              · have p10525_0 := h10525c.1
                have p10525_1 := h10525c.2.1
                have p10525_2 := h10525c.2.2.1
                have p10525_3 := h10525c.2.2.2
                linarith only [h3, hlam, p10525_0]
              · have p10525_0 := h10525c.1
                have p10525_1 := h10525c.2.1
                have p10525_2 := h10525c.2.2.1
                have p10525_3 := h10525c.2.2.2
                rcases p10525_3 (m.d 0 1) (by simp) with h10583 | h10583
                · rcases p10525_3 (m.d 0 2) (by simp) with h10584 | h10584
                  · linarith only [h10584, h8360, hlam]
                  · rcases p10525_3 (m.d 0 3) (by simp) with h10586 | h10586
                    · rcases p10525_3 (m.d 0 4) (by simp) with h10587 | h10587
                      · rcases p10525_3 (m.d 0 5) (by simp) with h10588 | h10588
                        · rcases h2bigk with h10589c | h10589c | h10589c | h10589c | h10589c | h10589c | h10589c | h10589c | h10589c | h10589c | h10589c | h10589c | h10589c | h10589c | h10589c | h10589c | h10589c | h10589c | h10589c | h10589c | h10589c | h10589c | h10589c | h10589c | h10589c
                          · have p10589_0 := h10589c.1
                            have p10589_1 := h10589c.2.1
                            have p10589_2 := h10589c.2.2.1
                            have p10589_3 := h10589c.2.2.2
                            linarith only [hlam, p10589_0]
                          · have p10589_0 := h10589c.1
                            have p10589_1 := h10589c.2.1
                            have p10589_2 := h10589c.2.2.1
                            have p10589_3 := h10589c.2.2.2
                            linarith only [hc05, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p10525_1, p10589_1]
                          · have p10589_0 := h10589c.1
                            have p10589_1 := h10589c.2.1
                            have p10589_2 := h10589c.2.2.1
                            have p10589_3 := h10589c.2.2.2
                            linarith only [h4, hlam, p10589_0]
                          · have p10589_0 := h10589c.1
                            have p10589_1 := h10589c.2.1
                            have p10589_2 := h10589c.2.2.1
                            have p10589_3 := h10589c.2.2.2
                            linarith only [h7337, hlam, p10589_0]
                          · have p10589_0 := h10589c.1
                            have p10589_1 := h10589c.2.1
                            have p10589_2 := h10589c.2.2.1
                            have p10589_3 := h10589c.2.2.2
                            linarith only [h8360, hlam, p10589_0]
                          · have p10589_0 := h10589c.1
                            have p10589_1 := h10589c.2.1
                            have p10589_2 := h10589c.2.2.1
                            have p10589_3 := h10589c.2.2.2
                            linarith only [h0, hlam, p10589_0]
                          · have p10589_0 := h10589c.1
                            have p10589_1 := h10589c.2.1
                            have p10589_2 := h10589c.2.2.1
                            have p10589_3 := h10589c.2.2.2
                            linarith only [hlam, p10589_0]
                          · have p10589_0 := h10589c.1
                            have p10589_1 := h10589c.2.1
                            have p10589_2 := h10589c.2.2.1
                            have p10589_3 := h10589c.2.2.2
                            linarith only [h9253, hlam, p10589_0]
                          · have p10589_0 := h10589c.1
                            have p10589_1 := h10589c.2.1
                            have p10589_2 := h10589c.2.2.1
                            have p10589_3 := h10589c.2.2.2
                            linarith only [h9255, hlam, p10589_0]
                          · have p10589_0 := h10589c.1
                            have p10589_1 := h10589c.2.1
                            have p10589_2 := h10589c.2.2.1
                            have p10589_3 := h10589c.2.2.2
                            linarith only [h9257, hlam, p10589_0]
                          · have p10589_0 := h10589c.1
                            have p10589_1 := h10589c.2.1
                            have p10589_2 := h10589c.2.2.1
                            have p10589_3 := h10589c.2.2.2
                            rcases p10589_3 (m.d 0 2) (by simp) with h10600 | h10600
                            · linarith only [h10600, hlam, p10589_0]
                            · rcases p10589_3 (m.d 1 2) (by simp) with h10602 | h10602
                              · linarith only [h10602, h9253, hlam]
                              · rcases p10589_3 (m.d 2 3) (by simp) with h10604 | h10604
                                · rcases p10589_3 (m.d 2 4) (by simp) with h10605 | h10605
                                  · linarith only [h10521, h10605, hlam]
                                  · linarith only [h10605, h7337, hlam]
                                · linarith only [h10604, hlam, p10589_0]
                          · have p10589_0 := h10589c.1
                            have p10589_1 := h10589c.2.1
                            have p10589_2 := h10589c.2.2.1
                            have p10589_3 := h10589c.2.2.2
                            rcases p10589_3 (m.d 0 2) (by simp) with h10609 | h10609
                            · linarith only [h10609, h4, hlam]
                            · linarith only [h0, h10609, hlam]
                          · have p10589_0 := h10589c.1
                            have p10589_1 := h10589c.2.1
                            have p10589_2 := h10589c.2.2.1
                            have p10589_3 := h10589c.2.2.2
                            linarith only [hlam, p10589_0]
                          · have p10589_0 := h10589c.1
                            have p10589_1 := h10589c.2.1
                            have p10589_2 := h10589c.2.2.1
                            have p10589_3 := h10589c.2.2.2
                            linarith only [h7337, h9252, hc02, hc23, hlam, hphi, p10525_1, p10589_1]
                          · have p10589_0 := h10589c.1
                            have p10589_1 := h10589c.2.1
                            have p10589_2 := h10589c.2.2.1
                            have p10589_3 := h10589c.2.2.2
                            linarith only [h0, h8360, hc12, hc23, hlam, hphi, p10589_1]
                          · have p10589_0 := h10589c.1
                            have p10589_1 := h10589c.2.1
                            have p10589_2 := h10589c.2.2.1
                            have p10589_3 := h10589c.2.2.2
                            rcases p10589_3 (m.d 0 2) (by simp) with h10615 | h10615
                            · linarith only [h10615, hlam, p10589_0]
                            · rcases p10589_3 (m.d 1 2) (by simp) with h10617 | h10617
                              · linarith only [h10617, h9255, hlam]
                              · rcases p10589_3 (m.d 2 3) (by simp) with h10619 | h10619
                                · rcases p10589_3 (m.d 2 4) (by simp) with h10620 | h10620
                                  · rcases p10589_3 (m.d 2 5) (by simp) with h10621 | h10621
                                    · linarith only [h10523, h10621, hlam]
                                    · linarith only [h10621, h8360, hlam]
                                  · linarith only [h10620, hlam, p10589_0]
                                · linarith only [h10619, h4, hlam]
                          · have p10589_0 := h10589c.1
                            have p10589_1 := h10589c.2.1
                            have p10589_2 := h10589c.2.2.1
                            have p10589_3 := h10589c.2.2.2
                            rcases p10589_3 (m.d 0 2) (by simp) with h10626 | h10626
                            · linarith only [h10626, h7337, hlam]
                            · linarith only [h0, h10626, hlam]
                          · have p10589_0 := h10589c.1
                            have p10589_1 := h10589c.2.1
                            have p10589_2 := h10589c.2.2.1
                            have p10589_3 := h10589c.2.2.2
                            linarith only [h10521, hlam, p10589_1]
                          · have p10589_0 := h10589c.1
                            have p10589_1 := h10589c.2.1
                            have p10589_2 := h10589c.2.2.1
                            have p10589_3 := h10589c.2.2.2
                            linarith only [hlam, p10589_0]
                          · have p10589_0 := h10589c.1
                            have p10589_1 := h10589c.2.1
                            have p10589_2 := h10589c.2.2.1
                            have p10589_3 := h10589c.2.2.2
                            linarith only [h0, h8360, hc12, hc24, hlam, hphi, p10525_1, p10589_1]
                          · have p10589_0 := h10589c.1
                            have p10589_1 := h10589c.2.1
                            have p10589_2 := h10589c.2.2.1
                            have p10589_3 := h10589c.2.2.2
                            rcases p10589_3 (m.d 0 2) (by simp) with h10632 | h10632
                            · linarith only [h10632, hlam, p10589_0]
                            · rcases p10589_3 (m.d 1 2) (by simp) with h10634 | h10634
                              · linarith only [h10634, h9257, hlam]
                              · rcases p10589_3 (m.d 2 3) (by simp) with h10636 | h10636
                                · rcases p10589_3 (m.d 2 4) (by simp) with h10637 | h10637
                                  · rcases p10589_3 (m.d 2 5) (by simp) with h10638 | h10638
                                    · rcases h3bigk with h10639c | h10639c | h10639c | h10639c | h10639c | h10639c | h10639c | h10639c | h10639c | h10639c | h10639c | h10639c | h10639c | h10639c | h10639c | h10639c | h10639c | h10639c | h10639c | h10639c | h10639c | h10639c | h10639c | h10639c | h10639c
                                      · have p10639_0 := h10639c.1
                                        have p10639_1 := h10639c.2.1
                                        have p10639_2 := h10639c.2.2.1
                                        have p10639_3 := h10639c.2.2.2
                                        linarith only [hlam, p10639_0]
                                      · have p10639_0 := h10639c.1
                                        have p10639_1 := h10639c.2.1
                                        have p10639_2 := h10639c.2.2.1
                                        have p10639_3 := h10639c.2.2.2
                                        linarith only [h4, h9253, hc12, hc23, hlam, hphi, p10639_1]
                                      · have p10639_0 := h10639c.1
                                        have p10639_1 := h10639c.2.1
                                        have p10639_2 := h10639c.2.2.1
                                        have p10639_3 := h10639c.2.2.2
                                        linarith only [h4, hlam, p10639_1]
                                      · have p10639_0 := h10639c.1
                                        have p10639_1 := h10639c.2.1
                                        have p10639_2 := h10639c.2.2.1
                                        have p10639_3 := h10639c.2.2.2
                                        linarith only [h10245, h10524, h4, h9253, hc12, hc23, hlam, hphi, p10639_1]
                                      · have p10639_0 := h10639c.1
                                        have p10639_1 := h10639c.2.1
                                        have p10639_2 := h10639c.2.2.1
                                        have p10639_3 := h10639c.2.2.2
                                        linarith only [h10245, h4, h9253, hc12, hc23, hlam, hphi, p10639_1]
                                      · have p10639_0 := h10639c.1
                                        have p10639_1 := h10639c.2.1
                                        have p10639_2 := h10639c.2.2.1
                                        have p10639_3 := h10639c.2.2.2
                                        linarith only [h1, hlam, p10639_0]
                                      · have p10639_0 := h10639c.1
                                        have p10639_1 := h10639c.2.1
                                        have p10639_2 := h10639c.2.2.1
                                        have p10639_3 := h10639c.2.2.2
                                        linarith only [hlam, p10639_0]
                                      · have p10639_0 := h10639c.1
                                        have p10639_1 := h10639c.2.1
                                        have p10639_2 := h10639c.2.2.1
                                        have p10639_3 := h10639c.2.2.2
                                        linarith only [h9253, hlam, p10639_1]
                                      · have p10639_0 := h10639c.1
                                        have p10639_1 := h10639c.2.1
                                        have p10639_2 := h10639c.2.2.1
                                        have p10639_3 := h10639c.2.2.2
                                        linarith only [h9259, hlam, p10639_0]
                                      · have p10639_0 := h10639c.1
                                        have p10639_1 := h10639c.2.1
                                        have p10639_2 := h10639c.2.2.1
                                        have p10639_3 := h10639c.2.2.2
                                        linarith only [h10245, hlam, p10639_0]
                                      · have p10639_0 := h10639c.1
                                        have p10639_1 := h10639c.2.1
                                        have p10639_2 := h10639c.2.2.1
                                        have p10639_3 := h10639c.2.2.2
                                        linarith only [h1, h9253, hc12, hc23, hlam, hphi, p10639_1]
                                      · have p10639_0 := h10639c.1
                                        have p10639_1 := h10639c.2.1
                                        have p10639_2 := h10639c.2.2.1
                                        have p10639_3 := h10639c.2.2.2
                                        linarith only [h9253, hc12, hc23, hlam, hphi, p10639_1]
                                      · have p10639_0 := h10639c.1
                                        have p10639_1 := h10639c.2.1
                                        have p10639_2 := h10639c.2.2.1
                                        have p10639_3 := h10639c.2.2.2
                                        linarith only [hlam, p10639_0]
                                      · have p10639_0 := h10639c.1
                                        have p10639_1 := h10639c.2.1
                                        have p10639_2 := h10639c.2.2.1
                                        have p10639_3 := h10639c.2.2.2
                                        linarith only [h10245, h10524, h9253, hc12, hc23, hlam, hphi, p10639_1]
                                      · have p10639_0 := h10639c.1
                                        have p10639_1 := h10639c.2.1
                                        have p10639_2 := h10639c.2.2.1
                                        have p10639_3 := h10639c.2.2.2
                                        linarith only [h10245, h9253, hc12, hc23, hlam, hphi, p10639_1]
                                      · have p10639_0 := h10639c.1
                                        have p10639_1 := h10639c.2.1
                                        have p10639_2 := h10639c.2.2.1
                                        have p10639_3 := h10639c.2.2.2
                                        linarith only [h9250, hlam, p10639_0]
                                      · have p10639_0 := h10639c.1
                                        have p10639_1 := h10639c.2.1
                                        have p10639_2 := h10639c.2.2.1
                                        have p10639_3 := h10639c.2.2.2
                                        linarith only [h9253, hc12, hc34, hlam, hphi, ht23, p10639_1]
                                      · have p10639_0 := h10639c.1
                                        have p10639_1 := h10639c.2.1
                                        have p10639_2 := h10639c.2.2.1
                                        have p10639_3 := h10639c.2.2.2
                                        linarith only [h10521, hlam, p10639_0]
                                      · have p10639_0 := h10639c.1
                                        have p10639_1 := h10639c.2.1
                                        have p10639_2 := h10639c.2.2.1
                                        have p10639_3 := h10639c.2.2.2
                                        linarith only [hlam, p10639_0]
                                      · have p10639_0 := h10639c.1
                                        have p10639_1 := h10639c.2.1
                                        have p10639_2 := h10639c.2.2.1
                                        have p10639_3 := h10639c.2.2.2
                                        linarith only [h10245, h9250, h9253, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p10639_1]
                                      · have p10639_0 := h10639c.1
                                        have p10639_1 := h10639c.2.1
                                        have p10639_2 := h10639c.2.2.1
                                        have p10639_3 := h10639c.2.2.2
                                        linarith only [h9251, hlam, p10639_0]
                                      · have p10639_0 := h10639c.1
                                        have p10639_1 := h10639c.2.1
                                        have p10639_2 := h10639c.2.2.1
                                        have p10639_3 := h10639c.2.2.2
                                        linarith only [h9253, hc12, hc35, hlam, hphi, ht23, p10639_1]
                                      · have p10639_0 := h10639c.1
                                        have p10639_1 := h10639c.2.1
                                        have p10639_2 := h10639c.2.2.1
                                        have p10639_3 := h10639c.2.2.2
                                        linarith only [h10522, hlam, p10639_0]
                                      · have p10639_0 := h10639c.1
                                        have p10639_1 := h10639c.2.1
                                        have p10639_2 := h10639c.2.2.1
                                        have p10639_3 := h10639c.2.2.2
                                        linarith only [h10524, hlam, p10639_0]
                                      · have p10639_0 := h10639c.1
                                        have p10639_1 := h10639c.2.1
                                        have p10639_2 := h10639c.2.2.1
                                        have p10639_3 := h10639c.2.2.2
                                        linarith only [hlam, p10639_0]
                                    · linarith only [h10638, hlam, p10589_0]
                                  · linarith only [h10637, h7337, hlam]
                                · linarith only [h10636, h4, hlam]
                          · have p10589_0 := h10589c.1
                            have p10589_1 := h10589c.2.1
                            have p10589_2 := h10589c.2.2.1
                            have p10589_3 := h10589c.2.2.2
                            rcases p10589_3 (m.d 0 2) (by simp) with h10668 | h10668
                            · linarith only [h10668, h8360, hlam]
                            · linarith only [h0, h10668, hlam]
                          · have p10589_0 := h10589c.1
                            have p10589_1 := h10589c.2.1
                            have p10589_2 := h10589c.2.2.1
                            have p10589_3 := h10589c.2.2.2
                            linarith only [h10522, hlam, p10589_1]
                          · have p10589_0 := h10589c.1
                            have p10589_1 := h10589c.2.1
                            have p10589_2 := h10589c.2.2.1
                            have p10589_3 := h10589c.2.2.2
                            linarith only [h10523, hlam, p10589_0]
                          · have p10589_0 := h10589c.1
                            have p10589_1 := h10589c.2.1
                            have p10589_2 := h10589c.2.2.1
                            have p10589_3 := h10589c.2.2.2
                            linarith only [hlam, p10589_0]
                        · linarith only [h10588, h8360, hlam]
                      · linarith only [h10587, h7337, hlam]
                    · linarith only [h10586, h4, hlam]
                · linarith only [h0, h10583, hlam]
              · have p10525_0 := h10525c.1
                have p10525_1 := h10525c.2.1
                have p10525_2 := h10525c.2.2.1
                have p10525_3 := h10525c.2.2.2
                linarith only [h9251, hlam, p10525_0]
              · have p10525_0 := h10525c.1
                have p10525_1 := h10525c.2.1
                have p10525_2 := h10525c.2.2.1
                have p10525_3 := h10525c.2.2.2
                linarith only [h9252, hlam, p10525_1]
              · have p10525_0 := h10525c.1
                have p10525_1 := h10525c.2.1
                have p10525_2 := h10525c.2.2.1
                have p10525_3 := h10525c.2.2.2
                linarith only [hlam, p10525_0]
            · linarith only [h10521, h10524, h7337, h9252, h9253, h9259, hc12, hc23, hlam, hphi]
          · linarith only [h10520, h10523, h2, h7337, hlam]
        · linarith only [h10522, h4, h7337, h9250, h9251, h9252, h9253, h9259, hc12, hc24, hlam, hphi]
      · linarith only [h10521, h4, h9250, hlam]
    · rcases m.htr 2 3 4 (by decide) (by decide) with h10685 | h10685
      · rcases m.htr 2 3 5 (by decide) (by decide) with h10686 | h10686
        · rcases m.htr 2 4 5 (by decide) (by decide) with h10687 | h10687
          · rcases m.htr 3 4 5 (by decide) (by decide) with h10688 | h10688
            · linarith only [h10520, h10688, h4, h9250, h9253, h9259, hc12, hc23, hlam, hphi]
            · linarith only [h10685, h10688, h7337, h9252, h9253, h9259, hc12, hc23, hlam, hphi]
          · linarith only [h10687, h7337, h9252, hlam]
        · linarith only [h10686, h4, h9251, hlam]
      · linarith only [h10685, h4, h9250, hlam]

set_option maxHeartbeats 5198000 in
set_option maxHeartbeats 5198000 in
theorem r1l7_10_12_23_L_I_L_I_H_I_s13_x0_x0_x1_x1_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (hg7337 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (hg8360 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (hg9250 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h9251 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h9252 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h9253 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h9255 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (h9257 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h7337 := hg7337
  have h8360 := hg8360
  have h9250 := hg9250
  rcases m.htr 1 3 4 (by decide) (by decide) with h9259 | h9259
  · exact r1l7_10_12_23_L_I_L_I_H_I_s13_x0_x0_x1_x1_x1_x0 m hb0 hb2 hb3 hg0 hg1 hg2 hg3 hg4 hg7337 hg8360 hg9250 h9251 h9252 h9253 h9255 h9257 h9259
  · exact r1l7_10_12_23_L_I_L_I_H_I_s13_x0_x0_x1_x1_x1_x1 m hb0 hb2 hb3 hg0 hg1 hg2 hg3 hg4 hg7337 hg8360 hg9250 h9251 h9252 h9253 h9255 h9257 h9259

set_option maxHeartbeats 5198000 in
set_option maxHeartbeats 5198000 in
theorem r1l7_10_12_23_L_I_L_I_H_I_s13_x0_x0_x1_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (hg7337 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (hg8360 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (hg9250 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h9251 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h9252 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h9253 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h9255 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h7337 := hg7337
  have h8360 := hg8360
  have h9250 := hg9250
  rcases m.htr 1 2 5 (by decide) (by decide) with h9257 | h9257
  · exact r1l7_10_12_23_L_I_L_I_H_I_s13_x0_x0_x1_x1_x0 m hb0 hb2 hb3 hg0 hg1 hg2 hg3 hg4 hg7337 hg8360 hg9250 h9251 h9252 h9253 h9255 h9257
  · exact r1l7_10_12_23_L_I_L_I_H_I_s13_x0_x0_x1_x1_x1 m hb0 hb2 hb3 hg0 hg1 hg2 hg3 hg4 hg7337 hg8360 hg9250 h9251 h9252 h9253 h9255 h9257

set_option maxHeartbeats 5198000 in
set_option maxHeartbeats 5198000 in
theorem r1l7_10_12_23_L_I_L_I_H_I_s13_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (hg7337 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (hg8360 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (hg9250 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h9251 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h9252 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h9253 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h7337 := hg7337
  have h8360 := hg8360
  have h9250 := hg9250
  rcases m.htr 1 2 4 (by decide) (by decide) with h9255 | h9255
  · exact r1l7_10_12_23_L_I_L_I_H_I_s13_x0_x0_x1_x0 m hb0 hb2 hb3 hg0 hg1 hg2 hg3 hg4 hg7337 hg8360 hg9250 h9251 h9252 h9253 h9255
  · exact r1l7_10_12_23_L_I_L_I_H_I_s13_x0_x0_x1_x1 m hb0 hb2 hb3 hg0 hg1 hg2 hg3 hg4 hg7337 hg8360 hg9250 h9251 h9252 h9253 h9255

set_option maxHeartbeats 5198000 in
set_option maxHeartbeats 5198000 in
theorem r1l7_10_12_23_L_I_L_I_H_I_s13_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (hg7337 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (hg8360 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (hg9250 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h9251 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h9252 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h7337 := hg7337
  have h8360 := hg8360
  have h9250 := hg9250
  rcases m.htr 1 2 3 (by decide) (by decide) with h9253 | h9253
  · exact r1l7_10_12_23_L_I_L_I_H_I_s13_x0_x0_x0 m hb0 hb2 hb3 hg0 hg1 hg2 hg3 hg4 hg7337 hg8360 hg9250 h9251 h9252 h9253
  · exact r1l7_10_12_23_L_I_L_I_H_I_s13_x0_x0_x1 m hb0 hb2 hb3 hg0 hg1 hg2 hg3 hg4 hg7337 hg8360 hg9250 h9251 h9252 h9253

end R2N4
