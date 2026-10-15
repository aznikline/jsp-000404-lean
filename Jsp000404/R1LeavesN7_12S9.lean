import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_12S8

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 12530000 in
set_option maxHeartbeats 12530000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_M_IR_s1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5ehi := hb5.2.1
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_M_IR_s2 m hb1 hb2 hb4 hb5 h0 h1 h2
  · rcases m.htr 0 1 5 (by decide) (by decide) with h6074 | h6074
    · rcases m.htr 0 2 3 (by decide) (by decide) with h6075 | h6075
      · rcases m.htr 0 2 4 (by decide) (by decide) with h6076 | h6076
        · linarith only [h0, h2, h6076, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h6078 | h6078
          · rcases m.htr 0 3 4 (by decide) (by decide) with h6079 | h6079
            · linarith only [h1, h2, h6079, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h6081 | h6081
              · rcases m.htr 1 2 3 (by decide) (by decide) with h6082 | h6082
                · rcases m.htr 1 2 4 (by decide) (by decide) with h6083 | h6083
                  · linarith only [h0, h6076, h6078, h6083, hc01, hlam, hphi, ht0b, ht5b, u5ehi0]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h6085 | h6085
                    · linarith only [h0, h2, h6083, h6085, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                    · linarith only [h0, h2, h6078, h6083, h6085, hc12, hc24, hlam, hphi]
                · linarith only [h6075, h6076, h6082, hc12, hc24, hlam, hphi]
              · linarith only [h2, h6074, h6081, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h6090 | h6090
            · linarith only [h2, h6074, h6075, h6078, h6090, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h6092 | h6092
              · rcases m.htr 1 2 3 (by decide) (by decide) with h6093 | h6093
                · rcases m.htr 1 2 4 (by decide) (by decide) with h6094 | h6094
                  · linarith only [h0, h2, h6076, h6094, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h6096 | h6096
                    · linarith only [h0, h2, h6078, h6094, h6096, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi0]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h6098 | h6098
                      · linarith only [h1, h2, h6090, h6094, h6098, hc03, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                      · linarith only [h2, h6074, h6093, h6096, h6098, hc23, hc34, hlam, hphi]
                · linarith only [h6075, h6078, h6093, hc12, hc25, hlam, hphi]
              · linarith only [h2, h6074, h6092, hlam]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h6103 | h6103
        · linarith only [h0, h2, h6103, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h6105 | h6105
          · rcases m.htr 0 3 4 (by decide) (by decide) with h6106 | h6106
            · linarith only [h1, h2, h6106, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h6108 | h6108
              · rcases m.htr 1 2 3 (by decide) (by decide) with h6109 | h6109
                · linarith only [h6075, h6105, h6109, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h6111 | h6111
                  · linarith only [h1, h6103, h6105, h6109, h6111, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h6113 | h6113
                    · linarith only [h1, h2, h6109, h6111, h6113, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                    · linarith only [h6075, h6105, h6113, hc12, hc23, hlam, hphi]
              · linarith only [h1, h2, h6075, h6105, h6108, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h6117 | h6117
            · linarith only [h1, h2, h6117, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h6119 | h6119
              · rcases m.htr 1 2 3 (by decide) (by decide) with h6120 | h6120
                · linarith only [h0, h6075, h6120, hlam]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h6122 | h6122
                  · linarith only [h1, h2, h6103, h6120, h6122, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h6124 | h6124
                    · linarith only [h0, h6105, h6124, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h6126 | h6126
                      · linarith only [h1, h2, h6117, h6122, h6126, hc03, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h6128 | h6128
                        · linarith only [h1, h2, h6126, h6128, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h6130 | h6130
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h6131 | h6131
                            · linarith only [h0, h2, h6126, h6131, hc12, hc23, hlam, hphi]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h6133 | h6133
                              · linarith only [h6128, h6131, h6133, hc13, hc34, hlam, hphi]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h6135 | h6135
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h6136 | h6136
                                  · rcases h1bigk with h6137c | h6137c | h6137c | h6137c | h6137c | h6137c | h6137c | h6137c | h6137c | h6137c | h6137c | h6137c | h6137c | h6137c | h6137c | h6137c | h6137c | h6137c | h6137c | h6137c | h6137c | h6137c | h6137c | h6137c | h6137c
                                    · have p6137_0 := h6137c.1
                                      have p6137_1 := h6137c.2.1
                                      have p6137_2 := h6137c.2.2.1
                                      have p6137_3 := h6137c.2.2.2
                                      linarith only [hlam, p6137_0]
                                    · have p6137_0 := h6137c.1
                                      have p6137_1 := h6137c.2.1
                                      have p6137_2 := h6137c.2.2.1
                                      have p6137_3 := h6137c.2.2.2
                                      linarith only [h2, h6122, hc12, hc24, hlam, hphi, p6137_1]
                                    · have p6137_0 := h6137c.1
                                      have p6137_1 := h6137c.2.1
                                      have p6137_2 := h6137c.2.2.1
                                      have p6137_3 := h6137c.2.2.2
                                      linarith only [h2, h6120, h6122, hc12, hc24, hlam, hphi, p6137_1]
                                    · have p6137_0 := h6137c.1
                                      have p6137_1 := h6137c.2.1
                                      have p6137_2 := h6137c.2.2.1
                                      have p6137_3 := h6137c.2.2.2
                                      linarith only [h2, hlam, p6137_0]
                                    · have p6137_0 := h6137c.1
                                      have p6137_1 := h6137c.2.1
                                      have p6137_2 := h6137c.2.2.1
                                      have p6137_3 := h6137c.2.2.2
                                      linarith only [h2, h6122, h6130, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p6137_1, u5ehi4]
                                    · have p6137_0 := h6137c.1
                                      have p6137_1 := h6137c.2.1
                                      have p6137_2 := h6137c.2.2.1
                                      have p6137_3 := h6137c.2.2.2
                                      linarith only [h0, hlam, p6137_0]
                                    · have p6137_0 := h6137c.1
                                      have p6137_1 := h6137c.2.1
                                      have p6137_2 := h6137c.2.2.1
                                      have p6137_3 := h6137c.2.2.2
                                      linarith only [hlam, p6137_0]
                                    · have p6137_0 := h6137c.1
                                      have p6137_1 := h6137c.2.1
                                      have p6137_2 := h6137c.2.2.1
                                      have p6137_3 := h6137c.2.2.2
                                      linarith only [h6120, hlam, p6137_1]
                                    · have p6137_0 := h6137c.1
                                      have p6137_1 := h6137c.2.1
                                      have p6137_2 := h6137c.2.2.1
                                      have p6137_3 := h6137c.2.2.2
                                      linarith only [h6122, hlam, p6137_1]
                                    · have p6137_0 := h6137c.1
                                      have p6137_1 := h6137c.2.1
                                      have p6137_2 := h6137c.2.2.1
                                      have p6137_3 := h6137c.2.2.2
                                      linarith only [h6124, hlam, p6137_1]
                                    · have p6137_0 := h6137c.1
                                      have p6137_1 := h6137c.2.1
                                      have p6137_2 := h6137c.2.2.1
                                      have p6137_3 := h6137c.2.2.2
                                      linarith only [h1, hlam, p6137_0]
                                    · have p6137_0 := h6137c.1
                                      have p6137_1 := h6137c.2.1
                                      have p6137_2 := h6137c.2.2.1
                                      have p6137_3 := h6137c.2.2.2
                                      linarith only [h1, h2, h6122, hc12, hc24, hlam, hphi, p6137_1]
                                    · have p6137_0 := h6137c.1
                                      have p6137_1 := h6137c.2.1
                                      have p6137_2 := h6137c.2.2.1
                                      have p6137_3 := h6137c.2.2.2
                                      linarith only [hlam, p6137_0]
                                    · have p6137_0 := h6137c.1
                                      have p6137_1 := h6137c.2.1
                                      have p6137_2 := h6137c.2.2.1
                                      have p6137_3 := h6137c.2.2.2
                                      linarith only [h6126, hlam, p6137_0]
                                    · have p6137_0 := h6137c.1
                                      have p6137_1 := h6137c.2.1
                                      have p6137_2 := h6137c.2.2.1
                                      have p6137_3 := h6137c.2.2.2
                                      linarith only [h6128, hlam, p6137_1]
                                    · have p6137_0 := h6137c.1
                                      have p6137_1 := h6137c.2.1
                                      have p6137_2 := h6137c.2.2.1
                                      have p6137_3 := h6137c.2.2.2
                                      linarith only [h0, h6122, hc12, hc24, hlam, hphi, p6137_1]
                                    · have p6137_0 := h6137c.1
                                      have p6137_1 := h6137c.2.1
                                      have p6137_2 := h6137c.2.2.1
                                      have p6137_3 := h6137c.2.2.2
                                      rcases p6137_3 (m.d 0 1) (by simp) with h6154 | h6154
                                      · linarith only [h2, h6154, hlam]
                                      · linarith only [h0, h6154, hlam]
                                    · have p6137_0 := h6137c.1
                                      have p6137_1 := h6137c.2.1
                                      have p6137_2 := h6137c.2.2.1
                                      have p6137_3 := h6137c.2.2.2
                                      rcases p6137_3 (m.d 0 1) (by simp) with h6157 | h6157
                                      · linarith only [h2, h6157, hlam]
                                      · linarith only [h1, h6157, hlam]
                                    · have p6137_0 := h6137c.1
                                      have p6137_1 := h6137c.2.1
                                      have p6137_2 := h6137c.2.2.1
                                      have p6137_3 := h6137c.2.2.2
                                      linarith only [hlam, p6137_0]
                                    · have p6137_0 := h6137c.1
                                      have p6137_1 := h6137c.2.1
                                      have p6137_2 := h6137c.2.2.1
                                      have p6137_3 := h6137c.2.2.2
                                      rcases p6137_3 (m.d 0 1) (by simp) with h6161 | h6161
                                      · linarith only [h2, h6161, hlam]
                                      · linarith only [h6074, h6161, hlam]
                                    · have p6137_0 := h6137c.1
                                      have p6137_1 := h6137c.2.1
                                      have p6137_2 := h6137c.2.2.1
                                      have p6137_3 := h6137c.2.2.2
                                      linarith only [h6074, hlam, p6137_0]
                                    · have p6137_0 := h6137c.1
                                      have p6137_1 := h6137c.2.1
                                      have p6137_2 := h6137c.2.2.1
                                      have p6137_3 := h6137c.2.2.2
                                      linarith only [h2, h6074, h6122, h6131, hc12, hc34, hlam, hphi, ht23, p6137_1]
                                    · have p6137_0 := h6137c.1
                                      have p6137_1 := h6137c.2.1
                                      have p6137_2 := h6137c.2.2.1
                                      have p6137_3 := h6137c.2.2.2
                                      linarith only [h2, h6074, h6122, h6131, hc13, hc34, hlam, hphi, p6137_1]
                                    · have p6137_0 := h6137c.1
                                      have p6137_1 := h6137c.2.1
                                      have p6137_2 := h6137c.2.2.1
                                      have p6137_3 := h6137c.2.2.2
                                      linarith only [h6130, hlam, p6137_0]
                                    · have p6137_0 := h6137c.1
                                      have p6137_1 := h6137c.2.1
                                      have p6137_2 := h6137c.2.2.1
                                      have p6137_3 := h6137c.2.2.2
                                      linarith only [hlam, p6137_0]
                                  · linarith only [h2, h6074, h6122, h6131, h6136, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi1]
                                · linarith only [h2, h6074, h6122, h6130, h6135, hlam]
                          · linarith only [h2, h6074, h6130, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi1]
              · linarith only [h2, h6074, h6119, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h6173 | h6173
      · rcases m.htr 0 2 4 (by decide) (by decide) with h6174 | h6174
        · linarith only [h0, h2, h6174, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h6176 | h6176
          · linarith only [h0, h6074, h6176, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h6178 | h6178
            · linarith only [h1, h2, h6178, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h6180 | h6180
              · rcases m.htr 1 2 3 (by decide) (by decide) with h6181 | h6181
                · rcases m.htr 1 2 4 (by decide) (by decide) with h6182 | h6182
                  · linarith only [h0, h2, h6174, h6182, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h6184 | h6184
                    · linarith only [h0, h6074, h6176, h6184, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h6186 | h6186
                      · linarith only [h0, h1, h6074, h6173, h6178, h6180, h6186, hlam]
                      · linarith only [h0, h2, h6181, h6186, hc23, hc34, hlam, hphi]
                · linarith only [h6173, h6174, h6181, hc12, hc24, hlam, hphi]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h6190 | h6190
                · linarith only [h0, h2, h6180, h6190, hc23, hc45, hlam, hphi, ht34]
                · linarith only [h0, h2, h6173, h6180, h6190, hc12, hc45, hlam, hphi, ht23, ht34]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h6193 | h6193
        · linarith only [h1, h2, h6173, h6193, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h6195 | h6195
          · linarith only [h1, h6074, h6173, h6195, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h6197 | h6197
            · linarith only [h1, h2, h6197, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h6199 | h6199
              · rcases m.htr 1 2 3 (by decide) (by decide) with h6200 | h6200
                · linarith only [h0, h2, h6173, h6200, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h6202 | h6202
                  · linarith only [h0, h6074, h6193, h6199, h6202, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h6204 | h6204
                    · linarith only [h1, h6074, h6195, h6200, h6204, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h6206 | h6206
                      · linarith only [h1, h6074, h6197, h6199, h6206, hc15, hlam, hphi, ht01, ht0b, ht5b, u5ehi0]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h6208 | h6208
                        · linarith only [h1, h2, h6206, h6208, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h6210 | h6210
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h6211 | h6211
                            · linarith only [h1, h6074, h6200, h6206, h6210, h6211, hc12, hc23, hlam, hphi]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h6213 | h6213
                              · linarith only [h1, h6074, h6200, h6208, h6213, hc12, hc23, hlam, hphi]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h6215 | h6215
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h6216 | h6216
                                  · rcases h1bigk with h6217c | h6217c | h6217c | h6217c | h6217c | h6217c | h6217c | h6217c | h6217c | h6217c | h6217c | h6217c | h6217c | h6217c | h6217c | h6217c | h6217c | h6217c | h6217c | h6217c | h6217c | h6217c | h6217c | h6217c | h6217c
                                    · have p6217_0 := h6217c.1
                                      have p6217_1 := h6217c.2.1
                                      have p6217_2 := h6217c.2.2.1
                                      have p6217_3 := h6217c.2.2.2
                                      linarith only [hlam, p6217_0]
                                    · have p6217_0 := h6217c.1
                                      have p6217_1 := h6217c.2.1
                                      have p6217_2 := h6217c.2.2.1
                                      have p6217_3 := h6217c.2.2.2
                                      linarith only [h6074, h6202, h6210, hc12, hc24, hlam, hphi, p6217_1]
                                    · have p6217_0 := h6217c.1
                                      have p6217_1 := h6217c.2.1
                                      have p6217_2 := h6217c.2.2.1
                                      have p6217_3 := h6217c.2.2.2
                                      linarith only [h6074, h6200, h6202, h6210, hc12, hc24, hlam, hphi, p6217_1]
                                    · have p6217_0 := h6217c.1
                                      have p6217_1 := h6217c.2.1
                                      have p6217_2 := h6217c.2.2.1
                                      have p6217_3 := h6217c.2.2.2
                                      linarith only [h2, hlam, p6217_0]
                                    · have p6217_0 := h6217c.1
                                      have p6217_1 := h6217c.2.1
                                      have p6217_2 := h6217c.2.2.1
                                      have p6217_3 := h6217c.2.2.2
                                      linarith only [h6074, hlam, p6217_0]
                                    · have p6217_0 := h6217c.1
                                      have p6217_1 := h6217c.2.1
                                      have p6217_2 := h6217c.2.2.1
                                      have p6217_3 := h6217c.2.2.2
                                      linarith only [h0, hlam, p6217_0]
                                    · have p6217_0 := h6217c.1
                                      have p6217_1 := h6217c.2.1
                                      have p6217_2 := h6217c.2.2.1
                                      have p6217_3 := h6217c.2.2.2
                                      linarith only [hlam, p6217_0]
                                    · have p6217_0 := h6217c.1
                                      have p6217_1 := h6217c.2.1
                                      have p6217_2 := h6217c.2.2.1
                                      have p6217_3 := h6217c.2.2.2
                                      linarith only [h6200, hlam, p6217_1]
                                    · have p6217_0 := h6217c.1
                                      have p6217_1 := h6217c.2.1
                                      have p6217_2 := h6217c.2.2.1
                                      have p6217_3 := h6217c.2.2.2
                                      linarith only [h6202, hlam, p6217_1]
                                    · have p6217_0 := h6217c.1
                                      have p6217_1 := h6217c.2.1
                                      have p6217_2 := h6217c.2.2.1
                                      have p6217_3 := h6217c.2.2.2
                                      linarith only [h6204, hlam, p6217_1]
                                    · have p6217_0 := h6217c.1
                                      have p6217_1 := h6217c.2.1
                                      have p6217_2 := h6217c.2.2.1
                                      have p6217_3 := h6217c.2.2.2
                                      linarith only [h1, hlam, p6217_0]
                                    · have p6217_0 := h6217c.1
                                      have p6217_1 := h6217c.2.1
                                      have p6217_2 := h6217c.2.2.1
                                      have p6217_3 := h6217c.2.2.2
                                      linarith only [h1, h6074, h6202, h6210, hc12, hc24, hlam, hphi, p6217_1]
                                    · have p6217_0 := h6217c.1
                                      have p6217_1 := h6217c.2.1
                                      have p6217_2 := h6217c.2.2.1
                                      have p6217_3 := h6217c.2.2.2
                                      linarith only [hlam, p6217_0]
                                    · have p6217_0 := h6217c.1
                                      have p6217_1 := h6217c.2.1
                                      have p6217_2 := h6217c.2.2.1
                                      have p6217_3 := h6217c.2.2.2
                                      linarith only [h6206, hlam, p6217_0]
                                    · have p6217_0 := h6217c.1
                                      have p6217_1 := h6217c.2.1
                                      have p6217_2 := h6217c.2.2.1
                                      have p6217_3 := h6217c.2.2.2
                                      linarith only [h6208, hlam, p6217_1]
                                    · have p6217_0 := h6217c.1
                                      have p6217_1 := h6217c.2.1
                                      have p6217_2 := h6217c.2.2.1
                                      have p6217_3 := h6217c.2.2.2
                                      linarith only [h0, h6202, hc12, hc24, hlam, hphi, p6217_1]
                                    · have p6217_0 := h6217c.1
                                      have p6217_1 := h6217c.2.1
                                      have p6217_2 := h6217c.2.2.1
                                      have p6217_3 := h6217c.2.2.2
                                      rcases p6217_3 (m.d 0 1) (by simp) with h6234 | h6234
                                      · linarith only [h2, h6234, hlam]
                                      · linarith only [h0, h6234, hlam]
                                    · have p6217_0 := h6217c.1
                                      have p6217_1 := h6217c.2.1
                                      have p6217_2 := h6217c.2.2.1
                                      have p6217_3 := h6217c.2.2.2
                                      rcases p6217_3 (m.d 0 1) (by simp) with h6237 | h6237
                                      · linarith only [h2, h6237, hlam]
                                      · linarith only [h1, h6237, hlam]
                                    · have p6217_0 := h6217c.1
                                      have p6217_1 := h6217c.2.1
                                      have p6217_2 := h6217c.2.2.1
                                      have p6217_3 := h6217c.2.2.2
                                      linarith only [hlam, p6217_0]
                                    · have p6217_0 := h6217c.1
                                      have p6217_1 := h6217c.2.1
                                      have p6217_2 := h6217c.2.2.1
                                      have p6217_3 := h6217c.2.2.2
                                      linarith only [h1, h6074, h6200, h6202, h6211, hc12, hc34, hlam, hphi, ht23, p6217_1]
                                    · have p6217_0 := h6217c.1
                                      have p6217_1 := h6217c.2.1
                                      have p6217_2 := h6217c.2.2.1
                                      have p6217_3 := h6217c.2.2.2
                                      linarith only [h1, h6200, h6204, hc12, hc25, hlam, hphi, p6217_1]
                                    · have p6217_0 := h6217c.1
                                      have p6217_1 := h6217c.2.1
                                      have p6217_2 := h6217c.2.2.1
                                      have p6217_3 := h6217c.2.2.2
                                      rcases p6217_3 (m.d 0 1) (by simp) with h6243 | h6243
                                      · linarith only [h6074, h6243, hlam]
                                      · linarith only [h0, h6243, hlam]
                                    · have p6217_0 := h6217c.1
                                      have p6217_1 := h6217c.2.1
                                      have p6217_2 := h6217c.2.2.1
                                      have p6217_3 := h6217c.2.2.2
                                      rcases p6217_3 (m.d 0 1) (by simp) with h6246 | h6246
                                      · linarith only [h6074, h6246, hlam]
                                      · linarith only [h1, h6246, hlam]
                                    · have p6217_0 := h6217c.1
                                      have p6217_1 := h6217c.2.1
                                      have p6217_2 := h6217c.2.2.1
                                      have p6217_3 := h6217c.2.2.2
                                      linarith only [h6210, hlam, p6217_0]
                                    · have p6217_0 := h6217c.1
                                      have p6217_1 := h6217c.2.1
                                      have p6217_2 := h6217c.2.2.1
                                      have p6217_3 := h6217c.2.2.2
                                      linarith only [hlam, p6217_0]
                                  · linarith only [h1, h2, h6199, h6200, h6202, h6211, h6216, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                                · linarith only [h2, h6199, h6202, h6215, hlam]
                          · linarith only [h2, h6199, h6210, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h6254 | h6254
                · linarith only [h0, h6173, h6254, hlam]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h6256 | h6256
                  · linarith only [h0, h2, h6199, h6256, hc24, hc45, hlam, hphi]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h6258 | h6258
                    · linarith only [h1, h2, h6199, h6254, h6258, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi2]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h6260 | h6260
                      · linarith only [h1, h2, h6199, h6260, hc34, hc45, hlam, hphi]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h6262 | h6262
                        · linarith only [h1, h2, h6262, hc14, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h6264 | h6264
                          · linarith only [h1, h2, h6199, h6254, h6256, h6264, hc12, hc24, hlam, hphi]
                          · linarith only [h1, h2, h6254, h6264, hc12, hc45, hlam, hphi, ht23, ht34]

set_option maxHeartbeats 13586000 in
set_option maxHeartbeats 13586000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_M_IR_s0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5ehi := hb5.2.1
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_M_IR_s1 m hb1 hb2 hb4 hb5 h0 h1
  · rcases m.htr 0 1 4 (by decide) (by decide) with h6267 | h6267
    · rcases m.htr 0 1 5 (by decide) (by decide) with h6268 | h6268
      · rcases m.htr 0 2 3 (by decide) (by decide) with h6269 | h6269
        · linarith only [h0, h1, h6269, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h6271 | h6271
          · rcases m.htr 0 2 5 (by decide) (by decide) with h6272 | h6272
            · rcases m.htr 0 3 4 (by decide) (by decide) with h6273 | h6273
              · rcases m.htr 0 4 5 (by decide) (by decide) with h6274 | h6274
                · rcases m.htr 1 2 3 (by decide) (by decide) with h6275 | h6275
                  · linarith only [h6269, h6271, h6274, h6275, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h6277 | h6277
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h6278 | h6278
                      · linarith only [h0, h1, h6278, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                      · linarith only [h0, h1, h6272, h6275, h6278, hc12, hc23, hlam, hphi]
                    · linarith only [h0, h1, h6271, h6275, h6277, hc12, hc23, hlam, hphi]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h6282 | h6282
                  · linarith only [h0, h6269, h6272, h6282, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h6284 | h6284
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h6285 | h6285
                      · linarith only [h0, h1, h6282, h6285, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                      · linarith only [h0, h1, h6272, h6282, h6284, h6285, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                    · linarith only [h0, h1, h6271, h6282, h6284, hc12, hc23, hlam, hphi]
              · linarith only [h1, h6267, h6273, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h6290 | h6290
              · rcases m.htr 0 4 5 (by decide) (by decide) with h6291 | h6291
                · linarith only [h6271, h6272, h6291, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h6293 | h6293
                  · linarith only [h0, h1, h6269, h6271, h6293, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h6295 | h6295
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h6296 | h6296
                      · linarith only [h0, h6272, h6296, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h6298 | h6298
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h6299 | h6299
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h6300 | h6300
                            · linarith only [h1, h6267, h6291, h6293, h6300, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h6302 | h6302
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h6303 | h6303
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h6304 | h6304
                                  · linarith only [h1, h6268, h6291, h6293, h6295, h6296, h6304, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h6306 | h6306
                                    · linarith only [h1, h6267, h6272, h6295, h6302, h6304, h6306, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                                    · rcases h1bigk with h6308c | h6308c | h6308c | h6308c | h6308c | h6308c | h6308c | h6308c | h6308c | h6308c | h6308c | h6308c | h6308c | h6308c | h6308c | h6308c | h6308c | h6308c | h6308c | h6308c | h6308c | h6308c | h6308c | h6308c | h6308c
                                      · have p6308_0 := h6308c.1
                                        have p6308_1 := h6308c.2.1
                                        have p6308_2 := h6308c.2.2.1
                                        have p6308_3 := h6308c.2.2.2
                                        linarith only [hlam, p6308_0]
                                      · have p6308_0 := h6308c.1
                                        have p6308_1 := h6308c.2.1
                                        have p6308_2 := h6308c.2.2.1
                                        have p6308_3 := h6308c.2.2.2
                                        linarith only [h1, h6293, h6295, h6302, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p6308_1]
                                      · have p6308_0 := h6308c.1
                                        have p6308_1 := h6308c.2.1
                                        have p6308_2 := h6308c.2.2.1
                                        have p6308_3 := h6308c.2.2.2
                                        linarith only [h1, hlam, p6308_0]
                                      · have p6308_0 := h6308c.1
                                        have p6308_1 := h6308c.2.1
                                        have p6308_2 := h6308c.2.2.1
                                        have p6308_3 := h6308c.2.2.2
                                        rcases p6308_3 (m.d 0 1) (by simp) with h6312 | h6312
                                        · rcases p6308_3 (m.d 1 2) (by simp) with h6313 | h6313
                                          · linarith only [h0, h6313, hlam]
                                          · linarith only [h6295, h6313, hlam]
                                        · linarith only [h6312, hlam, p6308_0]
                                      · have p6308_0 := h6308c.1
                                        have p6308_1 := h6308c.2.1
                                        have p6308_2 := h6308c.2.2.1
                                        have p6308_3 := h6308c.2.2.2
                                        linarith only [h1, h6293, h6295, h6296, h6302, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p6308_1]
                                      · have p6308_0 := h6308c.1
                                        have p6308_1 := h6308c.2.1
                                        have p6308_2 := h6308c.2.2.1
                                        have p6308_3 := h6308c.2.2.2
                                        linarith only [h0, hlam, p6308_0]
                                      · have p6308_0 := h6308c.1
                                        have p6308_1 := h6308c.2.1
                                        have p6308_2 := h6308c.2.2.1
                                        have p6308_3 := h6308c.2.2.2
                                        linarith only [hlam, p6308_0]
                                      · have p6308_0 := h6308c.1
                                        have p6308_1 := h6308c.2.1
                                        have p6308_2 := h6308c.2.2.1
                                        have p6308_3 := h6308c.2.2.2
                                        linarith only [h6293, hlam, p6308_1]
                                      · have p6308_0 := h6308c.1
                                        have p6308_1 := h6308c.2.1
                                        have p6308_2 := h6308c.2.2.1
                                        have p6308_3 := h6308c.2.2.2
                                        linarith only [h0, h6272, h6304, hc14, hc45, hlam, hphi, p6308_1]
                                      · have p6308_0 := h6308c.1
                                        have p6308_1 := h6308c.2.1
                                        have p6308_2 := h6308c.2.2.1
                                        have p6308_3 := h6308c.2.2.2
                                        linarith only [h6296, hlam, p6308_1]
                                      · have p6308_0 := h6308c.1
                                        have p6308_1 := h6308c.2.1
                                        have p6308_2 := h6308c.2.2.1
                                        have p6308_3 := h6308c.2.2.2
                                        linarith only [h0, h6293, hc12, hc23, hlam, hphi, p6308_1]
                                      · have p6308_0 := h6308c.1
                                        have p6308_1 := h6308c.2.1
                                        have p6308_2 := h6308c.2.2.1
                                        have p6308_3 := h6308c.2.2.2
                                        rcases p6308_3 (m.d 0 1) (by simp) with h6324 | h6324
                                        · linarith only [h1, h6324, hlam]
                                        · linarith only [h0, h6324, hlam]
                                      · have p6308_0 := h6308c.1
                                        have p6308_1 := h6308c.2.1
                                        have p6308_2 := h6308c.2.2.1
                                        have p6308_3 := h6308c.2.2.2
                                        linarith only [hlam, p6308_0]
                                      · have p6308_0 := h6308c.1
                                        have p6308_1 := h6308c.2.1
                                        have p6308_2 := h6308c.2.2.1
                                        have p6308_3 := h6308c.2.2.2
                                        rcases p6308_3 (m.d 0 1) (by simp) with h6328 | h6328
                                        · linarith only [h1, h6328, hlam]
                                        · linarith only [h6267, h6328, hlam]
                                      · have p6308_0 := h6308c.1
                                        have p6308_1 := h6308c.2.1
                                        have p6308_2 := h6308c.2.2.1
                                        have p6308_3 := h6308c.2.2.2
                                        rcases p6308_3 (m.d 0 1) (by simp) with h6331 | h6331
                                        · linarith only [h1, h6331, hlam]
                                        · linarith only [h6268, h6331, hlam]
                                      · have p6308_0 := h6308c.1
                                        have p6308_1 := h6308c.2.1
                                        have p6308_2 := h6308c.2.2.1
                                        have p6308_3 := h6308c.2.2.2
                                        linarith only [h6267, hlam, p6308_0]
                                      · have p6308_0 := h6308c.1
                                        have p6308_1 := h6308c.2.1
                                        have p6308_2 := h6308c.2.2.1
                                        have p6308_3 := h6308c.2.2.2
                                        linarith only [h6295, hlam, p6308_0]
                                      · have p6308_0 := h6308c.1
                                        have p6308_1 := h6308c.2.1
                                        have p6308_2 := h6308c.2.2.1
                                        have p6308_3 := h6308c.2.2.2
                                        linarith only [h6298, hlam, p6308_1]
                                      · have p6308_0 := h6308c.1
                                        have p6308_1 := h6308c.2.1
                                        have p6308_2 := h6308c.2.2.1
                                        have p6308_3 := h6308c.2.2.2
                                        linarith only [hlam, p6308_0]
                                      · have p6308_0 := h6308c.1
                                        have p6308_1 := h6308c.2.1
                                        have p6308_2 := h6308c.2.2.1
                                        have p6308_3 := h6308c.2.2.2
                                        linarith only [h6300, hlam, p6308_1]
                                      · have p6308_0 := h6308c.1
                                        have p6308_1 := h6308c.2.1
                                        have p6308_2 := h6308c.2.2.1
                                        have p6308_3 := h6308c.2.2.2
                                        linarith only [h6268, hlam, p6308_0]
                                      · have p6308_0 := h6308c.1
                                        have p6308_1 := h6308c.2.1
                                        have p6308_2 := h6308c.2.2.1
                                        have p6308_3 := h6308c.2.2.2
                                        linarith only [h6268, h6295, h6302, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p6308_1]
                                      · have p6308_0 := h6308c.1
                                        have p6308_1 := h6308c.2.1
                                        have p6308_2 := h6308c.2.2.1
                                        have p6308_3 := h6308c.2.2.2
                                        linarith only [h6299, hlam, p6308_0]
                                      · have p6308_0 := h6308c.1
                                        have p6308_1 := h6308c.2.1
                                        have p6308_2 := h6308c.2.2.1
                                        have p6308_3 := h6308c.2.2.2
                                        linarith only [h1, h6268, h6293, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p6308_1]
                                      · have p6308_0 := h6308c.1
                                        have p6308_1 := h6308c.2.1
                                        have p6308_2 := h6308c.2.2.1
                                        have p6308_3 := h6308c.2.2.2
                                        linarith only [hlam, p6308_0]
                                · linarith only [h1, h6268, h6293, h6303, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi1]
                              · linarith only [h1, h6268, h6293, h6295, h6296, h6302, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                          · linarith only [h1, h6268, h6295, h6296, h6299, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                        · linarith only [h1, h6268, h6295, h6296, h6298, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                    · linarith only [h6271, h6272, h6295, hc12, hc25, hlam, hphi]
              · linarith only [h1, h6268, h6271, h6272, h6290, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h6350 | h6350
            · rcases m.htr 0 3 4 (by decide) (by decide) with h6351 | h6351
              · rcases m.htr 0 4 5 (by decide) (by decide) with h6352 | h6352
                · rcases m.htr 1 2 3 (by decide) (by decide) with h6353 | h6353
                  · linarith only [h0, h6269, h6350, h6353, hc01, hlam, hphi, ht0b, ht5b, u5ehi0]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h6355 | h6355
                    · linarith only [h0, h1, h6271, h6350, h6353, h6355, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h6357 | h6357
                      · linarith only [h1, h6267, h6353, h6355, h6357, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                      · linarith only [h6271, h6350, h6357, hc12, hc24, hlam, hphi]
                · linarith only [h6271, h6350, h6352, hlam]
              · linarith only [h1, h6267, h6351, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h6362 | h6362
              · rcases m.htr 0 4 5 (by decide) (by decide) with h6363 | h6363
                · rcases m.htr 1 2 3 (by decide) (by decide) with h6364 | h6364
                  · linarith only [h0, h6269, h6364, hlam]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h6366 | h6366
                    · linarith only [h0, h6271, h6366, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h6368 | h6368
                      · linarith only [h0, h6350, h6368, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h6370 | h6370
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h6371 | h6371
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h6372 | h6372
                            · linarith only [h1, h6267, h6364, h6372, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                            · linarith only [h1, h6267, h6363, h6364, h6366, h6372, hc12, hc23, hlam, hphi]
                          · linarith only [h0, h1, h6371, hc12, hc35, hlam, hphi, ht23]
                        · linarith only [h1, h6267, h6363, h6370, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h6377 | h6377
                  · linarith only [h0, h6269, h6377, hlam]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h6379 | h6379
                    · linarith only [h0, h1, h6271, h6379, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h6381 | h6381
                      · linarith only [h0, h1, h6377, h6381, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h6383 | h6383
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h6384 | h6384
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h6385 | h6385
                            · linarith only [h1, h6267, h6363, h6377, h6385, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h6387 | h6387
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h6388 | h6388
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h6389 | h6389
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h6390 | h6390
                                    · linarith only [h6267, h6363, h6383, h6390, hlam]
                                    · rcases h1bigk with h6392c | h6392c | h6392c | h6392c | h6392c | h6392c | h6392c | h6392c | h6392c | h6392c | h6392c | h6392c | h6392c | h6392c | h6392c | h6392c | h6392c | h6392c | h6392c | h6392c | h6392c | h6392c | h6392c | h6392c | h6392c
                                      · have p6392_0 := h6392c.1
                                        have p6392_1 := h6392c.2.1
                                        have p6392_2 := h6392c.2.2.1
                                        have p6392_3 := h6392c.2.2.2
                                        linarith only [hlam, p6392_0]
                                      · have p6392_0 := h6392c.1
                                        have p6392_1 := h6392c.2.1
                                        have p6392_2 := h6392c.2.2.1
                                        have p6392_3 := h6392c.2.2.2
                                        linarith only [h1, h6377, hc12, hc23, hlam, hphi, p6392_1]
                                      · have p6392_0 := h6392c.1
                                        have p6392_1 := h6392c.2.1
                                        have p6392_2 := h6392c.2.2.1
                                        have p6392_3 := h6392c.2.2.2
                                        linarith only [h1, hlam, p6392_0]
                                      · have p6392_0 := h6392c.1
                                        have p6392_1 := h6392c.2.1
                                        have p6392_2 := h6392c.2.2.1
                                        have p6392_3 := h6392c.2.2.2
                                        linarith only [h1, h6377, h6379, hc12, hc23, hlam, hphi, p6392_1]
                                      · have p6392_0 := h6392c.1
                                        have p6392_1 := h6392c.2.1
                                        have p6392_2 := h6392c.2.2.1
                                        have p6392_3 := h6392c.2.2.2
                                        linarith only [h1, h6377, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p6392_1, u5ehi1]
                                      · have p6392_0 := h6392c.1
                                        have p6392_1 := h6392c.2.1
                                        have p6392_2 := h6392c.2.2.1
                                        have p6392_3 := h6392c.2.2.2
                                        linarith only [h0, hlam, p6392_0]
                                      · have p6392_0 := h6392c.1
                                        have p6392_1 := h6392c.2.1
                                        have p6392_2 := h6392c.2.2.1
                                        have p6392_3 := h6392c.2.2.2
                                        linarith only [hlam, p6392_0]
                                      · have p6392_0 := h6392c.1
                                        have p6392_1 := h6392c.2.1
                                        have p6392_2 := h6392c.2.2.1
                                        have p6392_3 := h6392c.2.2.2
                                        linarith only [h6377, hlam, p6392_1]
                                      · have p6392_0 := h6392c.1
                                        have p6392_1 := h6392c.2.1
                                        have p6392_2 := h6392c.2.2.1
                                        have p6392_3 := h6392c.2.2.2
                                        linarith only [h6379, hlam, p6392_1]
                                      · have p6392_0 := h6392c.1
                                        have p6392_1 := h6392c.2.1
                                        have p6392_2 := h6392c.2.2.1
                                        have p6392_3 := h6392c.2.2.2
                                        linarith only [h6381, hlam, p6392_1]
                                      · have p6392_0 := h6392c.1
                                        have p6392_1 := h6392c.2.1
                                        have p6392_2 := h6392c.2.2.1
                                        have p6392_3 := h6392c.2.2.2
                                        linarith only [h0, h6377, hc12, hc23, hlam, hphi, p6392_1]
                                      · have p6392_0 := h6392c.1
                                        have p6392_1 := h6392c.2.1
                                        have p6392_2 := h6392c.2.2.1
                                        have p6392_3 := h6392c.2.2.2
                                        rcases p6392_3 (m.d 0 1) (by simp) with h6404 | h6404
                                        · linarith only [h1, h6404, hlam]
                                        · linarith only [h0, h6404, hlam]
                                      · have p6392_0 := h6392c.1
                                        have p6392_1 := h6392c.2.1
                                        have p6392_2 := h6392c.2.2.1
                                        have p6392_3 := h6392c.2.2.2
                                        linarith only [hlam, p6392_0]
                                      · have p6392_0 := h6392c.1
                                        have p6392_1 := h6392c.2.1
                                        have p6392_2 := h6392c.2.2.1
                                        have p6392_3 := h6392c.2.2.2
                                        rcases p6392_3 (m.d 0 1) (by simp) with h6408 | h6408
                                        · linarith only [h1, h6408, hlam]
                                        · linarith only [h6267, h6408, hlam]
                                      · have p6392_0 := h6392c.1
                                        have p6392_1 := h6392c.2.1
                                        have p6392_2 := h6392c.2.2.1
                                        have p6392_3 := h6392c.2.2.2
                                        rcases p6392_3 (m.d 0 1) (by simp) with h6411 | h6411
                                        · linarith only [h1, h6411, hlam]
                                        · linarith only [h6268, h6411, hlam]
                                      · have p6392_0 := h6392c.1
                                        have p6392_1 := h6392c.2.1
                                        have p6392_2 := h6392c.2.2.1
                                        have p6392_3 := h6392c.2.2.2
                                        linarith only [h6267, hlam, p6392_0]
                                      · have p6392_0 := h6392c.1
                                        have p6392_1 := h6392c.2.1
                                        have p6392_2 := h6392c.2.2.1
                                        have p6392_3 := h6392c.2.2.2
                                        linarith only [h1, h6267, h6377, hc12, hc23, hlam, hphi, p6392_1]
                                      · have p6392_0 := h6392c.1
                                        have p6392_1 := h6392c.2.1
                                        have p6392_2 := h6392c.2.2.1
                                        have p6392_3 := h6392c.2.2.2
                                        linarith only [h6383, hlam, p6392_1]
                                      · have p6392_0 := h6392c.1
                                        have p6392_1 := h6392c.2.1
                                        have p6392_2 := h6392c.2.2.1
                                        have p6392_3 := h6392c.2.2.2
                                        linarith only [hlam, p6392_0]
                                      · have p6392_0 := h6392c.1
                                        have p6392_1 := h6392c.2.1
                                        have p6392_2 := h6392c.2.2.1
                                        have p6392_3 := h6392c.2.2.2
                                        linarith only [h6385, hlam, p6392_1]
                                      · have p6392_0 := h6392c.1
                                        have p6392_1 := h6392c.2.1
                                        have p6392_2 := h6392c.2.2.1
                                        have p6392_3 := h6392c.2.2.2
                                        linarith only [h6268, hlam, p6392_0]
                                      · have p6392_0 := h6392c.1
                                        have p6392_1 := h6392c.2.1
                                        have p6392_2 := h6392c.2.2.1
                                        have p6392_3 := h6392c.2.2.2
                                        linarith only [h1, h6268, h6377, hc12, hc23, hlam, hphi, p6392_1]
                                      · have p6392_0 := h6392c.1
                                        have p6392_1 := h6392c.2.1
                                        have p6392_2 := h6392c.2.2.1
                                        have p6392_3 := h6392c.2.2.2
                                        linarith only [h6384, hlam, p6392_0]
                                      · have p6392_0 := h6392c.1
                                        have p6392_1 := h6392c.2.1
                                        have p6392_2 := h6392c.2.2.1
                                        have p6392_3 := h6392c.2.2.2
                                        linarith only [h1, h6268, h6377, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p6392_1]
                                      · have p6392_0 := h6392c.1
                                        have p6392_1 := h6392c.2.1
                                        have p6392_2 := h6392c.2.2.1
                                        have p6392_3 := h6392c.2.2.2
                                        linarith only [hlam, p6392_0]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h6424 | h6424
                                    · linarith only [h0, h6271, h6389, h6424, hc12, hc34, hlam, hphi, ht23]
                                    · rcases h1bigk with h6426c | h6426c | h6426c | h6426c | h6426c | h6426c | h6426c | h6426c | h6426c | h6426c | h6426c | h6426c | h6426c | h6426c | h6426c | h6426c | h6426c | h6426c | h6426c | h6426c | h6426c | h6426c | h6426c | h6426c | h6426c
                                      · have p6426_0 := h6426c.1
                                        have p6426_1 := h6426c.2.1
                                        have p6426_2 := h6426c.2.2.1
                                        have p6426_3 := h6426c.2.2.2
                                        linarith only [hlam, p6426_0]
                                      · have p6426_0 := h6426c.1
                                        have p6426_1 := h6426c.2.1
                                        have p6426_2 := h6426c.2.2.1
                                        have p6426_3 := h6426c.2.2.2
                                        linarith only [h1, h6377, hc12, hc23, hlam, hphi, p6426_1]
                                      · have p6426_0 := h6426c.1
                                        have p6426_1 := h6426c.2.1
                                        have p6426_2 := h6426c.2.2.1
                                        have p6426_3 := h6426c.2.2.2
                                        linarith only [h1, hlam, p6426_0]
                                      · have p6426_0 := h6426c.1
                                        have p6426_1 := h6426c.2.1
                                        have p6426_2 := h6426c.2.2.1
                                        have p6426_3 := h6426c.2.2.2
                                        linarith only [h1, h6377, h6379, hc12, hc23, hlam, hphi, p6426_1]
                                      · have p6426_0 := h6426c.1
                                        have p6426_1 := h6426c.2.1
                                        have p6426_2 := h6426c.2.2.1
                                        have p6426_3 := h6426c.2.2.2
                                        linarith only [h1, h6377, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p6426_1, u5ehi1]
                                      · have p6426_0 := h6426c.1
                                        have p6426_1 := h6426c.2.1
                                        have p6426_2 := h6426c.2.2.1
                                        have p6426_3 := h6426c.2.2.2
                                        linarith only [h0, hlam, p6426_0]
                                      · have p6426_0 := h6426c.1
                                        have p6426_1 := h6426c.2.1
                                        have p6426_2 := h6426c.2.2.1
                                        have p6426_3 := h6426c.2.2.2
                                        linarith only [hlam, p6426_0]
                                      · have p6426_0 := h6426c.1
                                        have p6426_1 := h6426c.2.1
                                        have p6426_2 := h6426c.2.2.1
                                        have p6426_3 := h6426c.2.2.2
                                        linarith only [h6377, hlam, p6426_1]
                                      · have p6426_0 := h6426c.1
                                        have p6426_1 := h6426c.2.1
                                        have p6426_2 := h6426c.2.2.1
                                        have p6426_3 := h6426c.2.2.2
                                        linarith only [h6379, hlam, p6426_1]
                                      · have p6426_0 := h6426c.1
                                        have p6426_1 := h6426c.2.1
                                        have p6426_2 := h6426c.2.2.1
                                        have p6426_3 := h6426c.2.2.2
                                        linarith only [h6381, hlam, p6426_1]
                                      · have p6426_0 := h6426c.1
                                        have p6426_1 := h6426c.2.1
                                        have p6426_2 := h6426c.2.2.1
                                        have p6426_3 := h6426c.2.2.2
                                        linarith only [h0, h6377, hc12, hc23, hlam, hphi, p6426_1]
                                      · have p6426_0 := h6426c.1
                                        have p6426_1 := h6426c.2.1
                                        have p6426_2 := h6426c.2.2.1
                                        have p6426_3 := h6426c.2.2.2
                                        rcases p6426_3 (m.d 0 1) (by simp) with h6438 | h6438
                                        · linarith only [h1, h6438, hlam]
                                        · linarith only [h0, h6438, hlam]
                                      · have p6426_0 := h6426c.1
                                        have p6426_1 := h6426c.2.1
                                        have p6426_2 := h6426c.2.2.1
                                        have p6426_3 := h6426c.2.2.2
                                        linarith only [hlam, p6426_0]
                                      · have p6426_0 := h6426c.1
                                        have p6426_1 := h6426c.2.1
                                        have p6426_2 := h6426c.2.2.1
                                        have p6426_3 := h6426c.2.2.2
                                        rcases p6426_3 (m.d 0 1) (by simp) with h6442 | h6442
                                        · linarith only [h1, h6442, hlam]
                                        · linarith only [h6267, h6442, hlam]
                                      · have p6426_0 := h6426c.1
                                        have p6426_1 := h6426c.2.1
                                        have p6426_2 := h6426c.2.2.1
                                        have p6426_3 := h6426c.2.2.2
                                        rcases p6426_3 (m.d 0 1) (by simp) with h6445 | h6445
                                        · linarith only [h1, h6445, hlam]
                                        · linarith only [h6268, h6445, hlam]
                                      · have p6426_0 := h6426c.1
                                        have p6426_1 := h6426c.2.1
                                        have p6426_2 := h6426c.2.2.1
                                        have p6426_3 := h6426c.2.2.2
                                        linarith only [h6267, hlam, p6426_0]
                                      · have p6426_0 := h6426c.1
                                        have p6426_1 := h6426c.2.1
                                        have p6426_2 := h6426c.2.2.1
                                        have p6426_3 := h6426c.2.2.2
                                        linarith only [h1, h6267, h6377, hc12, hc23, hlam, hphi, p6426_1]
                                      · have p6426_0 := h6426c.1
                                        have p6426_1 := h6426c.2.1
                                        have p6426_2 := h6426c.2.2.1
                                        have p6426_3 := h6426c.2.2.2
                                        linarith only [h6383, hlam, p6426_1]
                                      · have p6426_0 := h6426c.1
                                        have p6426_1 := h6426c.2.1
                                        have p6426_2 := h6426c.2.2.1
                                        have p6426_3 := h6426c.2.2.2
                                        linarith only [hlam, p6426_0]
                                      · have p6426_0 := h6426c.1
                                        have p6426_1 := h6426c.2.1
                                        have p6426_2 := h6426c.2.2.1
                                        have p6426_3 := h6426c.2.2.2
                                        linarith only [h6385, hlam, p6426_1]
                                      · have p6426_0 := h6426c.1
                                        have p6426_1 := h6426c.2.1
                                        have p6426_2 := h6426c.2.2.1
                                        have p6426_3 := h6426c.2.2.2
                                        linarith only [h6268, hlam, p6426_0]
                                      · have p6426_0 := h6426c.1
                                        have p6426_1 := h6426c.2.1
                                        have p6426_2 := h6426c.2.2.1
                                        have p6426_3 := h6426c.2.2.2
                                        linarith only [h1, h6268, h6377, hc12, hc23, hlam, hphi, p6426_1]
                                      · have p6426_0 := h6426c.1
                                        have p6426_1 := h6426c.2.1
                                        have p6426_2 := h6426c.2.2.1
                                        have p6426_3 := h6426c.2.2.2
                                        linarith only [h6384, hlam, p6426_0]
                                      · have p6426_0 := h6426c.1
                                        have p6426_1 := h6426c.2.1
                                        have p6426_2 := h6426c.2.2.1
                                        have p6426_3 := h6426c.2.2.2
                                        linarith only [h1, h6268, h6377, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p6426_1]
                                      · have p6426_0 := h6426c.1
                                        have p6426_1 := h6426c.2.1
                                        have p6426_2 := h6426c.2.2.1
                                        have p6426_3 := h6426c.2.2.2
                                        linarith only [hlam, p6426_0]
                                · linarith only [h1, h6268, h6377, h6388, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi1]
                              · linarith only [h1, h6268, h6377, h6384, h6387, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                          · linarith only [h1, h6268, h6384, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi1]
                        · linarith only [h1, h6268, h6383, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi1]
              · linarith only [h1, h6267, h6362, hlam]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h6463 | h6463
        · linarith only [h0, h1, h6463, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h6465 | h6465
          · rcases m.htr 0 2 5 (by decide) (by decide) with h6466 | h6466
            · linarith only [h0, h6268, h6466, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h6468 | h6468
              · rcases m.htr 0 4 5 (by decide) (by decide) with h6469 | h6469
                · linarith only [h0, h6268, h6465, h6469, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h6471 | h6471
                  · linarith only [h0, h1, h6463, h6471, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h6473 | h6473
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h6474 | h6474
                      · linarith only [h0, h6268, h6466, h6474, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h6476 | h6476
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h6477 | h6477
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h6478 | h6478
                            · linarith only [h6267, h6268, h6469, h6478, hlam]
                            · linarith only [h0, h6268, h6473, h6478, hc24, hc45, hlam, hphi]
                          · linarith only [h0, h1, h6473, h6477, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                        · linarith only [h0, h1, h6473, h6476, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                    · linarith only [h6463, h6465, h6473, hc12, hc23, hlam, hphi]
              · linarith only [h1, h6267, h6468, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h6485 | h6485
            · linarith only [h6267, h6268, h6465, h6485, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h6487 | h6487
              · rcases m.htr 0 4 5 (by decide) (by decide) with h6488 | h6488
                · linarith only [h6267, h6268, h6488, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h6490 | h6490
                  · linarith only [h0, h1, h6463, h6490, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h6492 | h6492
                    · linarith only [h0, h6465, h6492, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h6494 | h6494
                      · linarith only [h0, h6268, h6485, h6494, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h6496 | h6496
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h6497 | h6497
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h6498 | h6498
                            · linarith only [h6267, h6268, h6465, h6488, h6497, h6498, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h6500 | h6500
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h6501 | h6501
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h6502 | h6502
                                  · linarith only [h0, h6268, h6498, h6500, h6502, hc12, hc23, hlam, hphi]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h6504 | h6504
                                    · linarith only [h6267, h6268, h6496, h6497, h6502, h6504, hc13, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                                    · rcases h1bigk with h6506c | h6506c | h6506c | h6506c | h6506c | h6506c | h6506c | h6506c | h6506c | h6506c | h6506c | h6506c | h6506c | h6506c | h6506c | h6506c | h6506c | h6506c | h6506c | h6506c | h6506c | h6506c | h6506c | h6506c | h6506c
                                      · have p6506_0 := h6506c.1
                                        have p6506_1 := h6506c.2.1
                                        have p6506_2 := h6506c.2.2.1
                                        have p6506_3 := h6506c.2.2.2
                                        linarith only [hlam, p6506_0]
                                      · have p6506_0 := h6506c.1
                                        have p6506_1 := h6506c.2.1
                                        have p6506_2 := h6506c.2.2.1
                                        have p6506_3 := h6506c.2.2.2
                                        linarith only [h6268, h6494, h6502, hc12, hc45, hlam, hphi, ht23, ht34, p6506_1]
                                      · have p6506_0 := h6506c.1
                                        have p6506_1 := h6506c.2.1
                                        have p6506_2 := h6506c.2.2.1
                                        have p6506_3 := h6506c.2.2.2
                                        linarith only [h1, hlam, p6506_0]
                                      · have p6506_0 := h6506c.1
                                        have p6506_1 := h6506c.2.1
                                        have p6506_2 := h6506c.2.2.1
                                        have p6506_3 := h6506c.2.2.2
                                        linarith only [h6268, h6494, h6502, hc14, hc45, hlam, hphi, p6506_1]
                                      · have p6506_0 := h6506c.1
                                        have p6506_1 := h6506c.2.1
                                        have p6506_2 := h6506c.2.2.1
                                        have p6506_3 := h6506c.2.2.2
                                        linarith only [h6268, hlam, p6506_0]
                                      · have p6506_0 := h6506c.1
                                        have p6506_1 := h6506c.2.1
                                        have p6506_2 := h6506c.2.2.1
                                        have p6506_3 := h6506c.2.2.2
                                        linarith only [h0, hlam, p6506_0]
                                      · have p6506_0 := h6506c.1
                                        have p6506_1 := h6506c.2.1
                                        have p6506_2 := h6506c.2.2.1
                                        have p6506_3 := h6506c.2.2.2
                                        linarith only [hlam, p6506_0]
                                      · have p6506_0 := h6506c.1
                                        have p6506_1 := h6506c.2.1
                                        have p6506_2 := h6506c.2.2.1
                                        have p6506_3 := h6506c.2.2.2
                                        linarith only [h6490, hlam, p6506_1]
                                      · have p6506_0 := h6506c.1
                                        have p6506_1 := h6506c.2.1
                                        have p6506_2 := h6506c.2.2.1
                                        have p6506_3 := h6506c.2.2.2
                                        linarith only [h6492, hlam, p6506_1]
                                      · have p6506_0 := h6506c.1
                                        have p6506_1 := h6506c.2.1
                                        have p6506_2 := h6506c.2.2.1
                                        have p6506_3 := h6506c.2.2.2
                                        linarith only [h6494, hlam, p6506_1]
                                      · have p6506_0 := h6506c.1
                                        have p6506_1 := h6506c.2.1
                                        have p6506_2 := h6506c.2.2.1
                                        have p6506_3 := h6506c.2.2.2
                                        linarith only [h0, h6490, hc12, hc23, hlam, hphi, p6506_1]
                                      · have p6506_0 := h6506c.1
                                        have p6506_1 := h6506c.2.1
                                        have p6506_2 := h6506c.2.2.1
                                        have p6506_3 := h6506c.2.2.2
                                        rcases p6506_3 (m.d 0 1) (by simp) with h6518 | h6518
                                        · linarith only [h1, h6518, hlam]
                                        · linarith only [h0, h6518, hlam]
                                      · have p6506_0 := h6506c.1
                                        have p6506_1 := h6506c.2.1
                                        have p6506_2 := h6506c.2.2.1
                                        have p6506_3 := h6506c.2.2.2
                                        linarith only [hlam, p6506_0]
                                      · have p6506_0 := h6506c.1
                                        have p6506_1 := h6506c.2.1
                                        have p6506_2 := h6506c.2.2.1
                                        have p6506_3 := h6506c.2.2.2
                                        rcases p6506_3 (m.d 0 1) (by simp) with h6522 | h6522
                                        · linarith only [h1, h6522, hlam]
                                        · linarith only [h6267, h6522, hlam]
                                      · have p6506_0 := h6506c.1
                                        have p6506_1 := h6506c.2.1
                                        have p6506_2 := h6506c.2.2.1
                                        have p6506_3 := h6506c.2.2.2
                                        linarith only [h6267, h6268, h6490, h6492, hc12, hc23, hlam, hphi, p6506_1]
                                      · have p6506_0 := h6506c.1
                                        have p6506_1 := h6506c.2.1
                                        have p6506_2 := h6506c.2.2.1
                                        have p6506_3 := h6506c.2.2.2
                                        linarith only [h6267, hlam, p6506_0]
                                      · have p6506_0 := h6506c.1
                                        have p6506_1 := h6506c.2.1
                                        have p6506_2 := h6506c.2.2.1
                                        have p6506_3 := h6506c.2.2.2
                                        linarith only [h6267, h6268, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p6506_1]
                                      · have p6506_0 := h6506c.1
                                        have p6506_1 := h6506c.2.1
                                        have p6506_2 := h6506c.2.2.1
                                        have p6506_3 := h6506c.2.2.2
                                        linarith only [h6496, hlam, p6506_1]
                                      · have p6506_0 := h6506c.1
                                        have p6506_1 := h6506c.2.1
                                        have p6506_2 := h6506c.2.2.1
                                        have p6506_3 := h6506c.2.2.2
                                        linarith only [hlam, p6506_0]
                                      · have p6506_0 := h6506c.1
                                        have p6506_1 := h6506c.2.1
                                        have p6506_2 := h6506c.2.2.1
                                        have p6506_3 := h6506c.2.2.2
                                        linarith only [h6498, hlam, p6506_1]
                                      · have p6506_0 := h6506c.1
                                        have p6506_1 := h6506c.2.1
                                        have p6506_2 := h6506c.2.2.1
                                        have p6506_3 := h6506c.2.2.2
                                        linarith only [h6267, h6494, h6502, hc14, hc45, hlam, hphi, p6506_1]
                                      · have p6506_0 := h6506c.1
                                        have p6506_1 := h6506c.2.1
                                        have p6506_2 := h6506c.2.2.1
                                        have p6506_3 := h6506c.2.2.2
                                        rcases p6506_3 (m.d 0 1) (by simp) with h6532 | h6532
                                        · linarith only [h6268, h6532, hlam]
                                        · linarith only [h0, h6532, hlam]
                                      · have p6506_0 := h6506c.1
                                        have p6506_1 := h6506c.2.1
                                        have p6506_2 := h6506c.2.2.1
                                        have p6506_3 := h6506c.2.2.2
                                        linarith only [h6497, hlam, p6506_0]
                                      · have p6506_0 := h6506c.1
                                        have p6506_1 := h6506c.2.1
                                        have p6506_2 := h6506c.2.2.1
                                        have p6506_3 := h6506c.2.2.2
                                        rcases p6506_3 (m.d 0 1) (by simp) with h6536 | h6536
                                        · linarith only [h6268, h6536, hlam]
                                        · linarith only [h6267, h6536, hlam]
                                      · have p6506_0 := h6506c.1
                                        have p6506_1 := h6506c.2.1
                                        have p6506_2 := h6506c.2.2.1
                                        have p6506_3 := h6506c.2.2.2
                                        linarith only [hlam, p6506_0]
                                · linarith only [h6490, h6497, h6501, hlam]
                              · linarith only [h1, h6267, h6490, h6492, h6500, hc12, hc34, hlam, hphi, ht23]
                          · linarith only [h1, h6267, h6492, h6497, hc12, hc35, hlam, hphi, ht23]
                        · linarith only [h1, h6267, h6492, h6496, hc12, hc34, hlam, hphi, ht23]
              · linarith only [h1, h6267, h6487, hlam]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h6545 | h6545
      · rcases m.htr 0 2 3 (by decide) (by decide) with h6546 | h6546
        · linarith only [h0, h1, h6546, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h6548 | h6548
          · linarith only [h0, h6267, h6548, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h6550 | h6550
            · rcases m.htr 0 3 4 (by decide) (by decide) with h6551 | h6551
              · rcases m.htr 0 4 5 (by decide) (by decide) with h6552 | h6552
                · rcases m.htr 1 2 3 (by decide) (by decide) with h6553 | h6553
                  · linarith only [h6546, h6550, h6553, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h6555 | h6555
                    · linarith only [h0, h6548, h6550, h6555, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h6557 | h6557
                      · linarith only [h0, h1, h6553, h6557, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                      · linarith only [h0, h1, h6550, h6553, h6557, hc12, hc23, hlam, hphi]
                · linarith only [h6267, h6545, h6552, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h6561 | h6561
                · rcases m.htr 1 2 3 (by decide) (by decide) with h6562 | h6562
                  · linarith only [h0, h6546, h6550, h6562, hc01, hlam, hphi, ht0b, ht5b, u5ehi0]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h6564 | h6564
                    · linarith only [h0, h1, h6548, h6550, h6551, h6564, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h6566 | h6566
                      · linarith only [h0, h1, h6551, h6566, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                      · linarith only [h0, h1, h6550, h6551, h6566, hc12, hc34, hlam, hphi, ht23]
                · linarith only [h1, h6545, h6551, h6561, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h6570 | h6570
              · rcases m.htr 0 4 5 (by decide) (by decide) with h6571 | h6571
                · rcases m.htr 1 2 3 (by decide) (by decide) with h6572 | h6572
                  · linarith only [h0, h1, h6546, h6572, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h6574 | h6574
                    · linarith only [h0, h6548, h6574, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h6576 | h6576
                      · linarith only [h0, h1, h6550, h6572, h6576, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi0]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h6578 | h6578
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h6579 | h6579
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h6580 | h6580
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h6581 | h6581
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h6582 | h6582
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h6583 | h6583
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h6584 | h6584
                                    · rcases h1bigk with h6585c | h6585c | h6585c | h6585c | h6585c | h6585c | h6585c | h6585c | h6585c | h6585c | h6585c | h6585c | h6585c | h6585c | h6585c | h6585c | h6585c | h6585c | h6585c | h6585c | h6585c | h6585c | h6585c | h6585c | h6585c
                                      · have p6585_0 := h6585c.1
                                        have p6585_1 := h6585c.2.1
                                        have p6585_2 := h6585c.2.2.1
                                        have p6585_3 := h6585c.2.2.2
                                        linarith only [hlam, p6585_0]
                                      · have p6585_0 := h6585c.1
                                        have p6585_1 := h6585c.2.1
                                        have p6585_2 := h6585c.2.2.1
                                        have p6585_3 := h6585c.2.2.2
                                        linarith only [h6267, h6572, h6578, hc12, hc23, hlam, hphi, p6585_1]
                                      · have p6585_0 := h6585c.1
                                        have p6585_1 := h6585c.2.1
                                        have p6585_2 := h6585c.2.2.1
                                        have p6585_3 := h6585c.2.2.2
                                        linarith only [h1, hlam, p6585_0]
                                      · have p6585_0 := h6585c.1
                                        have p6585_1 := h6585c.2.1
                                        have p6585_2 := h6585c.2.2.1
                                        have p6585_3 := h6585c.2.2.2
                                        linarith only [h6267, hlam, p6585_0]
                                      · have p6585_0 := h6585c.1
                                        have p6585_1 := h6585c.2.1
                                        have p6585_2 := h6585c.2.2.1
                                        have p6585_3 := h6585c.2.2.2
                                        linarith only [h6267, h6572, h6578, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p6585_1, u5ehi1]
                                      · have p6585_0 := h6585c.1
                                        have p6585_1 := h6585c.2.1
                                        have p6585_2 := h6585c.2.2.1
                                        have p6585_3 := h6585c.2.2.2
                                        linarith only [h0, hlam, p6585_0]
                                      · have p6585_0 := h6585c.1
                                        have p6585_1 := h6585c.2.1
                                        have p6585_2 := h6585c.2.2.1
                                        have p6585_3 := h6585c.2.2.2
                                        linarith only [hlam, p6585_0]
                                      · have p6585_0 := h6585c.1
                                        have p6585_1 := h6585c.2.1
                                        have p6585_2 := h6585c.2.2.1
                                        have p6585_3 := h6585c.2.2.2
                                        linarith only [h6572, hlam, p6585_1]
                                      · have p6585_0 := h6585c.1
                                        have p6585_1 := h6585c.2.1
                                        have p6585_2 := h6585c.2.2.1
                                        have p6585_3 := h6585c.2.2.2
                                        linarith only [h6574, hlam, p6585_1]
                                      · have p6585_0 := h6585c.1
                                        have p6585_1 := h6585c.2.1
                                        have p6585_2 := h6585c.2.2.1
                                        have p6585_3 := h6585c.2.2.2
                                        linarith only [h6576, hlam, p6585_1]
                                      · have p6585_0 := h6585c.1
                                        have p6585_1 := h6585c.2.1
                                        have p6585_2 := h6585c.2.2.1
                                        have p6585_3 := h6585c.2.2.2
                                        linarith only [h0, h6572, hc12, hc23, hlam, hphi, p6585_1]
                                      · have p6585_0 := h6585c.1
                                        have p6585_1 := h6585c.2.1
                                        have p6585_2 := h6585c.2.2.1
                                        have p6585_3 := h6585c.2.2.2
                                        rcases p6585_3 (m.d 0 1) (by simp) with h6597 | h6597
                                        · linarith only [h1, h6597, hlam]
                                        · linarith only [h0, h6597, hlam]
                                      · have p6585_0 := h6585c.1
                                        have p6585_1 := h6585c.2.1
                                        have p6585_2 := h6585c.2.2.1
                                        have p6585_3 := h6585c.2.2.2
                                        linarith only [hlam, p6585_0]
                                      · have p6585_0 := h6585c.1
                                        have p6585_1 := h6585c.2.1
                                        have p6585_2 := h6585c.2.2.1
                                        have p6585_3 := h6585c.2.2.2
                                        linarith only [h6267, h6545, h6572, h6579, h6584, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p6585_1, u5ehi4]
                                      · have p6585_0 := h6585c.1
                                        have p6585_1 := h6585c.2.1
                                        have p6585_2 := h6585c.2.2.1
                                        have p6585_3 := h6585c.2.2.2
                                        rcases p6585_3 (m.d 0 1) (by simp) with h6602 | h6602
                                        · linarith only [h1, h6602, hlam]
                                        · linarith only [h6545, h6602, hlam]
                                      · have p6585_0 := h6585c.1
                                        have p6585_1 := h6585c.2.1
                                        have p6585_2 := h6585c.2.2.1
                                        have p6585_3 := h6585c.2.2.2
                                        linarith only [h6545, h6579, h6584, hc14, hlam, hphi, ht01, ht0b, ht5b, p6585_1, u5ehi4]
                                      · have p6585_0 := h6585c.1
                                        have p6585_1 := h6585c.2.1
                                        have p6585_2 := h6585c.2.2.1
                                        have p6585_3 := h6585c.2.2.2
                                        rcases p6585_3 (m.d 0 1) (by simp) with h6606 | h6606
                                        · linarith only [h6267, h6606, hlam]
                                        · linarith only [h0, h6606, hlam]
                                      · have p6585_0 := h6585c.1
                                        have p6585_1 := h6585c.2.1
                                        have p6585_2 := h6585c.2.2.1
                                        have p6585_3 := h6585c.2.2.2
                                        linarith only [h6578, hlam, p6585_1]
                                      · have p6585_0 := h6585c.1
                                        have p6585_1 := h6585c.2.1
                                        have p6585_2 := h6585c.2.2.1
                                        have p6585_3 := h6585c.2.2.2
                                        linarith only [hlam, p6585_0]
                                      · have p6585_0 := h6585c.1
                                        have p6585_1 := h6585c.2.1
                                        have p6585_2 := h6585c.2.2.1
                                        have p6585_3 := h6585c.2.2.2
                                        rcases p6585_3 (m.d 0 1) (by simp) with h6611 | h6611
                                        · linarith only [h6267, h6611, hlam]
                                        · linarith only [h6545, h6611, hlam]
                                      · have p6585_0 := h6585c.1
                                        have p6585_1 := h6585c.2.1
                                        have p6585_2 := h6585c.2.2.1
                                        have p6585_3 := h6585c.2.2.2
                                        linarith only [h6545, hlam, p6585_0]
                                      · have p6585_0 := h6585c.1
                                        have p6585_1 := h6585c.2.1
                                        have p6585_2 := h6585c.2.2.1
                                        have p6585_3 := h6585c.2.2.2
                                        linarith only [h1, h6545, h6572, hc12, hc23, hlam, hphi, p6585_1]
                                      · have p6585_0 := h6585c.1
                                        have p6585_1 := h6585c.2.1
                                        have p6585_2 := h6585c.2.2.1
                                        have p6585_3 := h6585c.2.2.2
                                        linarith only [h6579, hlam, p6585_0]
                                      · have p6585_0 := h6585c.1
                                        have p6585_1 := h6585c.2.1
                                        have p6585_2 := h6585c.2.2.1
                                        have p6585_3 := h6585c.2.2.2
                                        linarith only [h6580, hlam, p6585_0]
                                      · have p6585_0 := h6585c.1
                                        have p6585_1 := h6585c.2.1
                                        have p6585_2 := h6585c.2.2.1
                                        have p6585_3 := h6585c.2.2.2
                                        linarith only [hlam, p6585_0]
                                    · rcases h1bigk with h6619c | h6619c | h6619c | h6619c | h6619c | h6619c | h6619c | h6619c | h6619c | h6619c | h6619c | h6619c | h6619c | h6619c | h6619c | h6619c | h6619c | h6619c | h6619c | h6619c | h6619c | h6619c | h6619c | h6619c | h6619c
                                      · have p6619_0 := h6619c.1
                                        have p6619_1 := h6619c.2.1
                                        have p6619_2 := h6619c.2.2.1
                                        have p6619_3 := h6619c.2.2.2
                                        linarith only [hlam, p6619_0]
                                      · have p6619_0 := h6619c.1
                                        have p6619_1 := h6619c.2.1
                                        have p6619_2 := h6619c.2.2.1
                                        have p6619_3 := h6619c.2.2.2
                                        linarith only [h6267, h6572, h6578, hc12, hc23, hlam, hphi, p6619_1]
                                      · have p6619_0 := h6619c.1
                                        have p6619_1 := h6619c.2.1
                                        have p6619_2 := h6619c.2.2.1
                                        have p6619_3 := h6619c.2.2.2
                                        linarith only [h1, hlam, p6619_0]
                                      · have p6619_0 := h6619c.1
                                        have p6619_1 := h6619c.2.1
                                        have p6619_2 := h6619c.2.2.1
                                        have p6619_3 := h6619c.2.2.2
                                        linarith only [h6267, hlam, p6619_0]
                                      · have p6619_0 := h6619c.1
                                        have p6619_1 := h6619c.2.1
                                        have p6619_2 := h6619c.2.2.1
                                        have p6619_3 := h6619c.2.2.2
                                        linarith only [h6267, h6572, h6578, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p6619_1, u5ehi1]
                                      · have p6619_0 := h6619c.1
                                        have p6619_1 := h6619c.2.1
                                        have p6619_2 := h6619c.2.2.1
                                        have p6619_3 := h6619c.2.2.2
                                        linarith only [h0, hlam, p6619_0]
                                      · have p6619_0 := h6619c.1
                                        have p6619_1 := h6619c.2.1
                                        have p6619_2 := h6619c.2.2.1
                                        have p6619_3 := h6619c.2.2.2
                                        linarith only [hlam, p6619_0]
                                      · have p6619_0 := h6619c.1
                                        have p6619_1 := h6619c.2.1
                                        have p6619_2 := h6619c.2.2.1
                                        have p6619_3 := h6619c.2.2.2
                                        linarith only [h6572, hlam, p6619_1]
                                      · have p6619_0 := h6619c.1
                                        have p6619_1 := h6619c.2.1
                                        have p6619_2 := h6619c.2.2.1
                                        have p6619_3 := h6619c.2.2.2
                                        linarith only [h6574, hlam, p6619_1]
                                      · have p6619_0 := h6619c.1
                                        have p6619_1 := h6619c.2.1
                                        have p6619_2 := h6619c.2.2.1
                                        have p6619_3 := h6619c.2.2.2
                                        linarith only [h6576, hlam, p6619_1]
                                      · have p6619_0 := h6619c.1
                                        have p6619_1 := h6619c.2.1
                                        have p6619_2 := h6619c.2.2.1
                                        have p6619_3 := h6619c.2.2.2
                                        linarith only [h0, h6572, hc12, hc23, hlam, hphi, p6619_1]
                                      · have p6619_0 := h6619c.1
                                        have p6619_1 := h6619c.2.1
                                        have p6619_2 := h6619c.2.2.1
                                        have p6619_3 := h6619c.2.2.2
                                        rcases p6619_3 (m.d 0 1) (by simp) with h6631 | h6631
                                        · linarith only [h1, h6631, hlam]
                                        · linarith only [h0, h6631, hlam]
                                      · have p6619_0 := h6619c.1
                                        have p6619_1 := h6619c.2.1
                                        have p6619_2 := h6619c.2.2.1
                                        have p6619_3 := h6619c.2.2.2
                                        linarith only [hlam, p6619_0]
                                      · have p6619_0 := h6619c.1
                                        have p6619_1 := h6619c.2.1
                                        have p6619_2 := h6619c.2.2.1
                                        have p6619_3 := h6619c.2.2.2
                                        linarith only [h6267, h6545, h6572, h6580, h6584, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p6619_1]
                                      · have p6619_0 := h6619c.1
                                        have p6619_1 := h6619c.2.1
                                        have p6619_2 := h6619c.2.2.1
                                        have p6619_3 := h6619c.2.2.2
                                        rcases p6619_3 (m.d 0 1) (by simp) with h6636 | h6636
                                        · linarith only [h1, h6636, hlam]
                                        · linarith only [h6545, h6636, hlam]
                                      · have p6619_0 := h6619c.1
                                        have p6619_1 := h6619c.2.1
                                        have p6619_2 := h6619c.2.2.1
                                        have p6619_3 := h6619c.2.2.2
                                        linarith only [h6545, h6580, h6584, hc14, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p6619_1]
                                      · have p6619_0 := h6619c.1
                                        have p6619_1 := h6619c.2.1
                                        have p6619_2 := h6619c.2.2.1
                                        have p6619_3 := h6619c.2.2.2
                                        rcases p6619_3 (m.d 0 1) (by simp) with h6640 | h6640
                                        · linarith only [h6267, h6640, hlam]
                                        · linarith only [h0, h6640, hlam]
                                      · have p6619_0 := h6619c.1
                                        have p6619_1 := h6619c.2.1
                                        have p6619_2 := h6619c.2.2.1
                                        have p6619_3 := h6619c.2.2.2
                                        linarith only [h6578, hlam, p6619_1]
                                      · have p6619_0 := h6619c.1
                                        have p6619_1 := h6619c.2.1
                                        have p6619_2 := h6619c.2.2.1
                                        have p6619_3 := h6619c.2.2.2
                                        linarith only [hlam, p6619_0]
                                      · have p6619_0 := h6619c.1
                                        have p6619_1 := h6619c.2.1
                                        have p6619_2 := h6619c.2.2.1
                                        have p6619_3 := h6619c.2.2.2
                                        rcases p6619_3 (m.d 0 1) (by simp) with h6645 | h6645
                                        · linarith only [h6267, h6645, hlam]
                                        · linarith only [h6545, h6645, hlam]
                                      · have p6619_0 := h6619c.1
                                        have p6619_1 := h6619c.2.1
                                        have p6619_2 := h6619c.2.2.1
                                        have p6619_3 := h6619c.2.2.2
                                        linarith only [h6545, hlam, p6619_0]
                                      · have p6619_0 := h6619c.1
                                        have p6619_1 := h6619c.2.1
                                        have p6619_2 := h6619c.2.2.1
                                        have p6619_3 := h6619c.2.2.2
                                        linarith only [h1, h6545, h6572, hc12, hc23, hlam, hphi, p6619_1]
                                      · have p6619_0 := h6619c.1
                                        have p6619_1 := h6619c.2.1
                                        have p6619_2 := h6619c.2.2.1
                                        have p6619_3 := h6619c.2.2.2
                                        linarith only [h6579, hlam, p6619_0]
                                      · have p6619_0 := h6619c.1
                                        have p6619_1 := h6619c.2.1
                                        have p6619_2 := h6619c.2.2.1
                                        have p6619_3 := h6619c.2.2.2
                                        linarith only [h6580, hlam, p6619_0]
                                      · have p6619_0 := h6619c.1
                                        have p6619_1 := h6619c.2.1
                                        have p6619_2 := h6619c.2.2.1
                                        have p6619_3 := h6619c.2.2.2
                                        linarith only [hlam, p6619_0]
                                  · linarith only [h6267, h6545, h6574, h6583, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi1]
                                · linarith only [h6267, h6545, h6574, h6579, h6581, h6582, hlam]
                              · linarith only [h1, h6545, h6572, h6579, h6581, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                            · linarith only [h6267, h6545, h6579, h6580, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi3]
                          · linarith only [h6267, h6545, h6578, h6579, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi1]
                        · linarith only [h1, h6545, h6570, h6578, hc03, hlam, hphi, ht0b, ht5b, u5ehi1]
                · linarith only [h6267, h6545, h6571, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h6660 | h6660
                · rcases m.htr 1 2 3 (by decide) (by decide) with h6661 | h6661
                  · linarith only [h0, h6546, h6661, hlam]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h6663 | h6663
                    · linarith only [h0, h6548, h6663, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h6665 | h6665
                      · linarith only [h0, h6550, h6665, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h6667 | h6667
                        · linarith only [h1, h6545, h6570, h6667, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi1]
                        · linarith only [h1, h6545, h6667, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi1]
                · linarith only [h1, h6545, h6570, h6660, hlam]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h6671 | h6671
        · linarith only [h0, h1, h6671, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h6673 | h6673
          · linarith only [h0, h6267, h6673, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h6675 | h6675
            · linarith only [h0, h6545, h6675, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h6677 | h6677
              · rcases m.htr 0 4 5 (by decide) (by decide) with h6678 | h6678
                · rcases m.htr 1 2 3 (by decide) (by decide) with h6679 | h6679
                  · linarith only [h0, h1, h6671, h6679, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h6681 | h6681
                    · linarith only [h0, h6545, h6673, h6678, h6681, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h6683 | h6683
                      · linarith only [h0, h6545, h6675, h6683, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h6685 | h6685
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h6686 | h6686
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h6687 | h6687
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h6688 | h6688
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h6689 | h6689
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h6690 | h6690
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h6691 | h6691
                                    · rcases h1bigk with h6692c | h6692c | h6692c | h6692c | h6692c | h6692c | h6692c | h6692c | h6692c | h6692c | h6692c | h6692c | h6692c | h6692c | h6692c | h6692c | h6692c | h6692c | h6692c | h6692c | h6692c | h6692c | h6692c | h6692c | h6692c
                                      · have p6692_0 := h6692c.1
                                        have p6692_1 := h6692c.2.1
                                        have p6692_2 := h6692c.2.2.1
                                        have p6692_3 := h6692c.2.2.2
                                        linarith only [hlam, p6692_0]
                                      · have p6692_0 := h6692c.1
                                        have p6692_1 := h6692c.2.1
                                        have p6692_2 := h6692c.2.2.1
                                        have p6692_3 := h6692c.2.2.2
                                        linarith only [h6545, h6679, h6685, h6687, hc12, hc23, hlam, hphi, p6692_1]
                                      · have p6692_0 := h6692c.1
                                        have p6692_1 := h6692c.2.1
                                        have p6692_2 := h6692c.2.2.1
                                        have p6692_3 := h6692c.2.2.2
                                        linarith only [h1, hlam, p6692_0]
                                      · have p6692_0 := h6692c.1
                                        have p6692_1 := h6692c.2.1
                                        have p6692_2 := h6692c.2.2.1
                                        have p6692_3 := h6692c.2.2.2
                                        linarith only [h6267, hlam, p6692_0]
                                      · have p6692_0 := h6692c.1
                                        have p6692_1 := h6692c.2.1
                                        have p6692_2 := h6692c.2.2.1
                                        have p6692_3 := h6692c.2.2.2
                                        linarith only [h6545, hlam, p6692_0]
                                      · have p6692_0 := h6692c.1
                                        have p6692_1 := h6692c.2.1
                                        have p6692_2 := h6692c.2.2.1
                                        have p6692_3 := h6692c.2.2.2
                                        linarith only [h0, hlam, p6692_0]
                                      · have p6692_0 := h6692c.1
                                        have p6692_1 := h6692c.2.1
                                        have p6692_2 := h6692c.2.2.1
                                        have p6692_3 := h6692c.2.2.2
                                        linarith only [hlam, p6692_0]
                                      · have p6692_0 := h6692c.1
                                        have p6692_1 := h6692c.2.1
                                        have p6692_2 := h6692c.2.2.1
                                        have p6692_3 := h6692c.2.2.2
                                        linarith only [h6679, hlam, p6692_1]
                                      · have p6692_0 := h6692c.1
                                        have p6692_1 := h6692c.2.1
                                        have p6692_2 := h6692c.2.2.1
                                        have p6692_3 := h6692c.2.2.2
                                        linarith only [h6681, hlam, p6692_1]
                                      · have p6692_0 := h6692c.1
                                        have p6692_1 := h6692c.2.1
                                        have p6692_2 := h6692c.2.2.1
                                        have p6692_3 := h6692c.2.2.2
                                        linarith only [h6683, hlam, p6692_1]
                                      · have p6692_0 := h6692c.1
                                        have p6692_1 := h6692c.2.1
                                        have p6692_2 := h6692c.2.2.1
                                        have p6692_3 := h6692c.2.2.2
                                        linarith only [h0, h6679, hc12, hc23, hlam, hphi, p6692_1]
                                      · have p6692_0 := h6692c.1
                                        have p6692_1 := h6692c.2.1
                                        have p6692_2 := h6692c.2.2.1
                                        have p6692_3 := h6692c.2.2.2
                                        rcases p6692_3 (m.d 0 1) (by simp) with h6704 | h6704
                                        · linarith only [h1, h6704, hlam]
                                        · linarith only [h0, h6704, hlam]
                                      · have p6692_0 := h6692c.1
                                        have p6692_1 := h6692c.2.1
                                        have p6692_2 := h6692c.2.2.1
                                        have p6692_3 := h6692c.2.2.2
                                        linarith only [hlam, p6692_0]
                                      · have p6692_0 := h6692c.1
                                        have p6692_1 := h6692c.2.1
                                        have p6692_2 := h6692c.2.2.1
                                        have p6692_3 := h6692c.2.2.2
                                        linarith only [h0, h6267, h6679, hc12, hc23, hlam, hphi, p6692_1]
                                      · have p6692_0 := h6692c.1
                                        have p6692_1 := h6692c.2.1
                                        have p6692_2 := h6692c.2.2.1
                                        have p6692_3 := h6692c.2.2.2
                                        linarith only [h0, h6545, h6679, hc12, hc23, hlam, hphi, p6692_1]
                                      · have p6692_0 := h6692c.1
                                        have p6692_1 := h6692c.2.1
                                        have p6692_2 := h6692c.2.2.1
                                        have p6692_3 := h6692c.2.2.2
                                        linarith only [h0, h6681, hc12, hc24, hlam, hphi, p6692_1]
                                      · have p6692_0 := h6692c.1
                                        have p6692_1 := h6692c.2.1
                                        have p6692_2 := h6692c.2.2.1
                                        have p6692_3 := h6692c.2.2.2
                                        rcases p6692_3 (m.d 0 1) (by simp) with h6711 | h6711
                                        · linarith only [h6267, h6711, hlam]
                                        · linarith only [h0, h6711, hlam]
                                      · have p6692_0 := h6692c.1
                                        have p6692_1 := h6692c.2.1
                                        have p6692_2 := h6692c.2.2.1
                                        have p6692_3 := h6692c.2.2.2
                                        linarith only [h6685, hlam, p6692_1]
                                      · have p6692_0 := h6692c.1
                                        have p6692_1 := h6692c.2.1
                                        have p6692_2 := h6692c.2.2.1
                                        have p6692_3 := h6692c.2.2.2
                                        linarith only [hlam, p6692_0]
                                      · have p6692_0 := h6692c.1
                                        have p6692_1 := h6692c.2.1
                                        have p6692_2 := h6692c.2.2.1
                                        have p6692_3 := h6692c.2.2.2
                                        linarith only [h0, h6545, h6679, h6685, hc12, hc23, hlam, hphi, p6692_1]
                                      · have p6692_0 := h6692c.1
                                        have p6692_1 := h6692c.2.1
                                        have p6692_2 := h6692c.2.2.1
                                        have p6692_3 := h6692c.2.2.2
                                        linarith only [h0, h6683, hc12, hc25, hlam, hphi, p6692_1]
                                      · have p6692_0 := h6692c.1
                                        have p6692_1 := h6692c.2.1
                                        have p6692_2 := h6692c.2.2.1
                                        have p6692_3 := h6692c.2.2.2
                                        rcases p6692_3 (m.d 0 1) (by simp) with h6718 | h6718
                                        · linarith only [h6545, h6718, hlam]
                                        · linarith only [h0, h6718, hlam]
                                      · have p6692_0 := h6692c.1
                                        have p6692_1 := h6692c.2.1
                                        have p6692_2 := h6692c.2.2.1
                                        have p6692_3 := h6692c.2.2.2
                                        linarith only [h6686, hlam, p6692_0]
                                      · have p6692_0 := h6692c.1
                                        have p6692_1 := h6692c.2.1
                                        have p6692_2 := h6692c.2.2.1
                                        have p6692_3 := h6692c.2.2.2
                                        linarith only [h6687, hlam, p6692_0]
                                      · have p6692_0 := h6692c.1
                                        have p6692_1 := h6692c.2.1
                                        have p6692_2 := h6692c.2.2.1
                                        have p6692_3 := h6692c.2.2.2
                                        linarith only [hlam, p6692_0]
                                    · rcases h1bigk with h6724c | h6724c | h6724c | h6724c | h6724c | h6724c | h6724c | h6724c | h6724c | h6724c | h6724c | h6724c | h6724c | h6724c | h6724c | h6724c | h6724c | h6724c | h6724c | h6724c | h6724c | h6724c | h6724c | h6724c | h6724c
                                      · have p6724_0 := h6724c.1
                                        have p6724_1 := h6724c.2.1
                                        have p6724_2 := h6724c.2.2.1
                                        have p6724_3 := h6724c.2.2.2
                                        linarith only [hlam, p6724_0]
                                      · have p6724_0 := h6724c.1
                                        have p6724_1 := h6724c.2.1
                                        have p6724_2 := h6724c.2.2.1
                                        have p6724_3 := h6724c.2.2.2
                                        linarith only [h1, h6679, hc12, hc23, hlam, hphi, p6724_1]
                                      · have p6724_0 := h6724c.1
                                        have p6724_1 := h6724c.2.1
                                        have p6724_2 := h6724c.2.2.1
                                        have p6724_3 := h6724c.2.2.2
                                        linarith only [h1, hlam, p6724_0]
                                      · have p6724_0 := h6724c.1
                                        have p6724_1 := h6724c.2.1
                                        have p6724_2 := h6724c.2.2.1
                                        have p6724_3 := h6724c.2.2.2
                                        linarith only [h6267, hlam, p6724_0]
                                      · have p6724_0 := h6724c.1
                                        have p6724_1 := h6724c.2.1
                                        have p6724_2 := h6724c.2.2.1
                                        have p6724_3 := h6724c.2.2.2
                                        linarith only [h6545, hlam, p6724_0]
                                      · have p6724_0 := h6724c.1
                                        have p6724_1 := h6724c.2.1
                                        have p6724_2 := h6724c.2.2.1
                                        have p6724_3 := h6724c.2.2.2
                                        linarith only [h0, hlam, p6724_0]
                                      · have p6724_0 := h6724c.1
                                        have p6724_1 := h6724c.2.1
                                        have p6724_2 := h6724c.2.2.1
                                        have p6724_3 := h6724c.2.2.2
                                        linarith only [hlam, p6724_0]
                                      · have p6724_0 := h6724c.1
                                        have p6724_1 := h6724c.2.1
                                        have p6724_2 := h6724c.2.2.1
                                        have p6724_3 := h6724c.2.2.2
                                        linarith only [h6679, hlam, p6724_1]
                                      · have p6724_0 := h6724c.1
                                        have p6724_1 := h6724c.2.1
                                        have p6724_2 := h6724c.2.2.1
                                        have p6724_3 := h6724c.2.2.2
                                        linarith only [h6681, hlam, p6724_1]
                                      · have p6724_0 := h6724c.1
                                        have p6724_1 := h6724c.2.1
                                        have p6724_2 := h6724c.2.2.1
                                        have p6724_3 := h6724c.2.2.2
                                        linarith only [h6683, hlam, p6724_1]
                                      · have p6724_0 := h6724c.1
                                        have p6724_1 := h6724c.2.1
                                        have p6724_2 := h6724c.2.2.1
                                        have p6724_3 := h6724c.2.2.2
                                        linarith only [h0, h6679, hc12, hc23, hlam, hphi, p6724_1]
                                      · have p6724_0 := h6724c.1
                                        have p6724_1 := h6724c.2.1
                                        have p6724_2 := h6724c.2.2.1
                                        have p6724_3 := h6724c.2.2.2
                                        rcases p6724_3 (m.d 0 1) (by simp) with h6736 | h6736
                                        · linarith only [h1, h6736, hlam]
                                        · linarith only [h0, h6736, hlam]
                                      · have p6724_0 := h6724c.1
                                        have p6724_1 := h6724c.2.1
                                        have p6724_2 := h6724c.2.2.1
                                        have p6724_3 := h6724c.2.2.2
                                        linarith only [hlam, p6724_0]
                                      · have p6724_0 := h6724c.1
                                        have p6724_1 := h6724c.2.1
                                        have p6724_2 := h6724c.2.2.1
                                        have p6724_3 := h6724c.2.2.2
                                        linarith only [h0, h6267, h6679, hc12, hc23, hlam, hphi, p6724_1]
                                      · have p6724_0 := h6724c.1
                                        have p6724_1 := h6724c.2.1
                                        have p6724_2 := h6724c.2.2.1
                                        have p6724_3 := h6724c.2.2.2
                                        linarith only [h0, h6545, h6679, hc12, hc23, hlam, hphi, p6724_1]
                                      · have p6724_0 := h6724c.1
                                        have p6724_1 := h6724c.2.1
                                        have p6724_2 := h6724c.2.2.1
                                        have p6724_3 := h6724c.2.2.2
                                        linarith only [h0, h6681, h6688, hc12, hc23, hlam, hphi, p6724_1]
                                      · have p6724_0 := h6724c.1
                                        have p6724_1 := h6724c.2.1
                                        have p6724_2 := h6724c.2.2.1
                                        have p6724_3 := h6724c.2.2.2
                                        rcases p6724_3 (m.d 0 1) (by simp) with h6743 | h6743
                                        · linarith only [h6267, h6743, hlam]
                                        · linarith only [h0, h6743, hlam]
                                      · have p6724_0 := h6724c.1
                                        have p6724_1 := h6724c.2.1
                                        have p6724_2 := h6724c.2.2.1
                                        have p6724_3 := h6724c.2.2.2
                                        linarith only [h6685, hlam, p6724_1]
                                      · have p6724_0 := h6724c.1
                                        have p6724_1 := h6724c.2.1
                                        have p6724_2 := h6724c.2.2.1
                                        have p6724_3 := h6724c.2.2.2
                                        linarith only [hlam, p6724_0]
                                      · have p6724_0 := h6724c.1
                                        have p6724_1 := h6724c.2.1
                                        have p6724_2 := h6724c.2.2.1
                                        have p6724_3 := h6724c.2.2.2
                                        linarith only [h0, h6545, h6681, h6688, hc12, hc23, hlam, hphi, p6724_1]
                                      · have p6724_0 := h6724c.1
                                        have p6724_1 := h6724c.2.1
                                        have p6724_2 := h6724c.2.2.1
                                        have p6724_3 := h6724c.2.2.2
                                        linarith only [h0, h6683, h6688, h6690, hc12, hc23, hlam, hphi, p6724_1]
                                      · have p6724_0 := h6724c.1
                                        have p6724_1 := h6724c.2.1
                                        have p6724_2 := h6724c.2.2.1
                                        have p6724_3 := h6724c.2.2.2
                                        rcases p6724_3 (m.d 0 1) (by simp) with h6750 | h6750
                                        · linarith only [h6545, h6750, hlam]
                                        · linarith only [h0, h6750, hlam]
                                      · have p6724_0 := h6724c.1
                                        have p6724_1 := h6724c.2.1
                                        have p6724_2 := h6724c.2.2.1
                                        have p6724_3 := h6724c.2.2.2
                                        linarith only [h6686, hlam, p6724_0]
                                      · have p6724_0 := h6724c.1
                                        have p6724_1 := h6724c.2.1
                                        have p6724_2 := h6724c.2.2.1
                                        have p6724_3 := h6724c.2.2.2
                                        linarith only [h6687, hlam, p6724_0]
                                      · have p6724_0 := h6724c.1
                                        have p6724_1 := h6724c.2.1
                                        have p6724_2 := h6724c.2.2.1
                                        have p6724_3 := h6724c.2.2.2
                                        linarith only [hlam, p6724_0]
                                  · linarith only [h0, h6267, h6681, h6690, hc12, hc45, hlam, hphi, ht23, ht34]
                                · linarith only [h0, h1, h6679, h6689, hc12, hc35, hlam, hphi, ht23]
                              · linarith only [h0, h1, h6679, h6688, hc12, hc34, hlam, hphi, ht23]
                            · linarith only [h0, h6267, h6687, hc12, hc45, hlam, hphi, ht23, ht34]
                          · linarith only [h0, h1, h6686, hc12, hc35, hlam, hphi, ht23]
                        · linarith only [h0, h1, h6685, hc12, hc34, hlam, hphi, ht23]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h6762 | h6762
                  · linarith only [h0, h6267, h6678, h6762, hc23, hc45, hlam, hphi, ht34]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h6764 | h6764
                    · linarith only [h0, h6267, h6678, h6764, hc24, hc45, hlam, hphi]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h6766 | h6766
                      · linarith only [h0, h6267, h6678, h6766, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h6768 | h6768
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h6769 | h6769
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h6770 | h6770
                            · linarith only [h0, h6267, h6678, h6762, h6768, h6770, hc12, hc23, hlam, hphi]
                            · linarith only [h0, h6267, h6770, hc12, hc45, hlam, hphi, ht23, ht34]
                          · linarith only [h0, h1, h6769, hc12, hc35, hlam, hphi, ht23]
                        · linarith only [h0, h1, h6677, h6768, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h6775 | h6775
                · rcases m.htr 1 2 3 (by decide) (by decide) with h6776 | h6776
                  · linarith only [h0, h6671, h6776, hlam]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h6778 | h6778
                    · linarith only [h0, h6673, h6778, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h6780 | h6780
                      · linarith only [h0, h1, h6677, h6780, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h6782 | h6782
                        · linarith only [h0, h1, h6677, h6776, h6782, hc12, hc23, hlam, hphi]
                        · linarith only [h0, h1, h6782, hc12, hc34, hlam, hphi, ht23]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h6785 | h6785
                  · linarith only [h0, h6267, h6775, h6785, hc23, hc45, hlam, hphi, ht34]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h6787 | h6787
                    · linarith only [h0, h1, h6677, h6775, h6787, hc24, hc45, hlam, hphi]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h6789 | h6789
                      · linarith only [h0, h1, h6677, h6775, h6789, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h6791 | h6791
                        · linarith only [h0, h1, h6677, h6785, h6791, hc12, hc23, hlam, hphi]
                        · linarith only [h0, h1, h6791, hc12, hc34, hlam, hphi, ht23]

end R2N4
