import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_2S9

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 13644000 in
set_option maxHeartbeats 13644000 in
theorem r1l7_10_12_23_L_I_L_I_H_I_s6_x1_x1_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h7 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h4388 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h4905 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  rcases m.htr 1 2 3 (by decide) (by decide) with h6067 | h6067
  · rcases m.htr 1 2 4 (by decide) (by decide) with h6068 | h6068
    · rcases m.htr 1 2 5 (by decide) (by decide) with h6069 | h6069
      · rcases m.htr 1 3 4 (by decide) (by decide) with h6070 | h6070
        · linarith only [h1, h6070, h7, hlam]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h6072 | h6072
          · linarith only [h1, h4388, h6072, hlam]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h6074 | h6074
            · linarith only [h2, h4905, h6074, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h6076 | h6076
              · linarith only [h1, h6067, h6076, h7, hlam]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h6078 | h6078
                · linarith only [h1, h4388, h6067, h6078, hlam]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h6080 | h6080
                  · linarith only [h4905, h5, h6080, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h6082 | h6082
                    · rcases h0bigk with h6083c | h6083c | h6083c | h6083c | h6083c | h6083c | h6083c | h6083c | h6083c | h6083c | h6083c | h6083c | h6083c | h6083c | h6083c | h6083c | h6083c | h6083c | h6083c | h6083c | h6083c | h6083c | h6083c | h6083c | h6083c
                      · have p6083_0 := h6083c.1
                        have p6083_1 := h6083c.2.1
                        have p6083_2 := h6083c.2.2.1
                        have p6083_3 := h6083c.2.2.2
                        linarith only [hlam, p6083_0]
                      · have p6083_0 := h6083c.1
                        have p6083_1 := h6083c.2.1
                        have p6083_2 := h6083c.2.2.1
                        have p6083_3 := h6083c.2.2.2
                        rcases p6083_3 (m.d 0 1) (by simp) with h6085 | h6085
                        · rcases p6083_3 (m.d 0 2) (by simp) with h6086 | h6086
                          · linarith only [h0, h6086, hlam]
                          · rcases p6083_3 (m.d 0 3) (by simp) with h6088 | h6088
                            · linarith only [h1, h6088, hlam]
                            · rcases p6083_3 (m.d 0 4) (by simp) with h6090 | h6090
                              · linarith only [h2, h6090, hlam]
                              · rcases p6083_3 (m.d 0 5) (by simp) with h6092 | h6092
                                · linarith only [h3, h6092, hlam]
                                · rcases h2bigk with h6094c | h6094c | h6094c | h6094c | h6094c | h6094c | h6094c | h6094c | h6094c | h6094c | h6094c | h6094c | h6094c | h6094c | h6094c | h6094c | h6094c | h6094c | h6094c | h6094c | h6094c | h6094c | h6094c | h6094c | h6094c
                                  · have p6094_0 := h6094c.1
                                    have p6094_1 := h6094c.2.1
                                    have p6094_2 := h6094c.2.2.1
                                    have p6094_3 := h6094c.2.2.2
                                    linarith only [hlam, p6094_0]
                                  · have p6094_0 := h6094c.1
                                    have p6094_1 := h6094c.2.1
                                    have p6094_2 := h6094c.2.2.1
                                    have p6094_3 := h6094c.2.2.2
                                    linarith only [hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p6083_1, p6094_1]
                                  · have p6094_0 := h6094c.1
                                    have p6094_1 := h6094c.2.1
                                    have p6094_2 := h6094c.2.2.1
                                    have p6094_3 := h6094c.2.2.2
                                    linarith only [hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6083_1, p6094_1]
                                  · have p6094_0 := h6094c.1
                                    have p6094_1 := h6094c.2.1
                                    have p6094_2 := h6094c.2.2.1
                                    have p6094_3 := h6094c.2.2.2
                                    linarith only [h6076, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6083_1, p6094_1]
                                  · have p6094_0 := h6094c.1
                                    have p6094_1 := h6094c.2.1
                                    have p6094_2 := h6094c.2.2.1
                                    have p6094_3 := h6094c.2.2.2
                                    linarith only [hc01, hc25, hlam, hphi, ht0b, ht5b, p6083_1, p6094_1]
                                  · have p6094_0 := h6094c.1
                                    have p6094_1 := h6094c.2.1
                                    have p6094_2 := h6094c.2.2.1
                                    have p6094_3 := h6094c.2.2.2
                                    linarith only [h0, hlam, p6094_0]
                                  · have p6094_0 := h6094c.1
                                    have p6094_1 := h6094c.2.1
                                    have p6094_2 := h6094c.2.2.1
                                    have p6094_3 := h6094c.2.2.2
                                    linarith only [hlam, p6094_0]
                                  · have p6094_0 := h6094c.1
                                    have p6094_1 := h6094c.2.1
                                    have p6094_2 := h6094c.2.2.1
                                    have p6094_3 := h6094c.2.2.2
                                    linarith only [h0, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6083_1, p6094_1]
                                  · have p6094_0 := h6094c.1
                                    have p6094_1 := h6094c.2.1
                                    have p6094_2 := h6094c.2.2.1
                                    have p6094_3 := h6094c.2.2.2
                                    linarith only [h0, h6076, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6083_1, p6094_1]
                                  · have p6094_0 := h6094c.1
                                    have p6094_1 := h6094c.2.1
                                    have p6094_2 := h6094c.2.2.1
                                    have p6094_3 := h6094c.2.2.2
                                    linarith only [h0, hc01, hc25, hlam, hphi, ht0b, ht5b, p6083_1, p6094_1]
                                  · have p6094_0 := h6094c.1
                                    have p6094_1 := h6094c.2.1
                                    have p6094_2 := h6094c.2.2.1
                                    have p6094_3 := h6094c.2.2.2
                                    linarith only [h4, hlam, p6094_0]
                                  · have p6094_0 := h6094c.1
                                    have p6094_1 := h6094c.2.1
                                    have p6094_2 := h6094c.2.2.1
                                    have p6094_3 := h6094c.2.2.2
                                    linarith only [h6067, hlam, p6094_0]
                                  · have p6094_0 := h6094c.1
                                    have p6094_1 := h6094c.2.1
                                    have p6094_2 := h6094c.2.2.1
                                    have p6094_3 := h6094c.2.2.2
                                    linarith only [hlam, p6094_0]
                                  · have p6094_0 := h6094c.1
                                    have p6094_1 := h6094c.2.1
                                    have p6094_2 := h6094c.2.2.1
                                    have p6094_3 := h6094c.2.2.2
                                    linarith only [h6076, hlam, p6094_0]
                                  · have p6094_0 := h6094c.1
                                    have p6094_1 := h6094c.2.1
                                    have p6094_2 := h6094c.2.2.1
                                    have p6094_3 := h6094c.2.2.2
                                    linarith only [h6078, hlam, p6094_0]
                                  · have p6094_0 := h6094c.1
                                    have p6094_1 := h6094c.2.1
                                    have p6094_2 := h6094c.2.2.1
                                    have p6094_3 := h6094c.2.2.2
                                    linarith only [h5, hlam, p6094_0]
                                  · have p6094_0 := h6094c.1
                                    have p6094_1 := h6094c.2.1
                                    have p6094_2 := h6094c.2.2.1
                                    have p6094_3 := h6094c.2.2.2
                                    linarith only [h6068, hlam, p6094_0]
                                  · have p6094_0 := h6094c.1
                                    have p6094_1 := h6094c.2.1
                                    have p6094_2 := h6094c.2.2.1
                                    have p6094_3 := h6094c.2.2.2
                                    linarith only [h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6083_1, p6094_1]
                                  · have p6094_0 := h6094c.1
                                    have p6094_1 := h6094c.2.1
                                    have p6094_2 := h6094c.2.2.1
                                    have p6094_3 := h6094c.2.2.2
                                    linarith only [hlam, p6094_0]
                                  · have p6094_0 := h6094c.1
                                    have p6094_1 := h6094c.2.1
                                    have p6094_2 := h6094c.2.2.1
                                    have p6094_3 := h6094c.2.2.2
                                    linarith only [h6080, hlam, p6094_1]
                                  · have p6094_0 := h6094c.1
                                    have p6094_1 := h6094c.2.1
                                    have p6094_2 := h6094c.2.2.1
                                    have p6094_3 := h6094c.2.2.2
                                    linarith only [h6, hlam, p6094_0]
                                  · have p6094_0 := h6094c.1
                                    have p6094_1 := h6094c.2.1
                                    have p6094_2 := h6094c.2.2.1
                                    have p6094_3 := h6094c.2.2.2
                                    linarith only [h6069, hlam, p6094_0]
                                  · have p6094_0 := h6094c.1
                                    have p6094_1 := h6094c.2.1
                                    have p6094_2 := h6094c.2.2.1
                                    have p6094_3 := h6094c.2.2.2
                                    linarith only [h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6083_1, p6094_1]
                                  · have p6094_0 := h6094c.1
                                    have p6094_1 := h6094c.2.1
                                    have p6094_2 := h6094c.2.2.1
                                    have p6094_3 := h6094c.2.2.2
                                    linarith only [h0, h6069, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p6083_1, p6094_1]
                                  · have p6094_0 := h6094c.1
                                    have p6094_1 := h6094c.2.1
                                    have p6094_2 := h6094c.2.2.1
                                    have p6094_3 := h6094c.2.2.2
                                    linarith only [hlam, p6094_0]
                        · linarith only [h0, h6085, hlam]
                      · have p6083_0 := h6083c.1
                        have p6083_1 := h6083c.2.1
                        have p6083_2 := h6083c.2.2.1
                        have p6083_3 := h6083c.2.2.2
                        rcases p6083_3 (m.d 0 1) (by simp) with h6121 | h6121
                        · rcases p6083_3 (m.d 0 2) (by simp) with h6122 | h6122
                          · linarith only [h0, h6122, hlam]
                          · linarith only [h4, h6122, hlam]
                        · linarith only [h1, h6121, hlam]
                      · have p6083_0 := h6083c.1
                        have p6083_1 := h6083c.2.1
                        have p6083_2 := h6083c.2.2.1
                        have p6083_3 := h6083c.2.2.2
                        rcases p6083_3 (m.d 0 1) (by simp) with h6126 | h6126
                        · rcases p6083_3 (m.d 0 2) (by simp) with h6127 | h6127
                          · linarith only [h0, h6127, hlam]
                          · linarith only [h5, h6127, hlam]
                        · linarith only [h2, h6126, hlam]
                      · have p6083_0 := h6083c.1
                        have p6083_1 := h6083c.2.1
                        have p6083_2 := h6083c.2.2.1
                        have p6083_3 := h6083c.2.2.2
                        rcases p6083_3 (m.d 0 1) (by simp) with h6131 | h6131
                        · rcases p6083_3 (m.d 0 2) (by simp) with h6132 | h6132
                          · linarith only [h0, h6132, hlam]
                          · linarith only [h6, h6132, hlam]
                        · linarith only [h3, h6131, hlam]
                      · have p6083_0 := h6083c.1
                        have p6083_1 := h6083c.2.1
                        have p6083_2 := h6083c.2.2.1
                        have p6083_3 := h6083c.2.2.2
                        linarith only [h0, hlam, p6083_0]
                      · have p6083_0 := h6083c.1
                        have p6083_1 := h6083c.2.1
                        have p6083_2 := h6083c.2.2.1
                        have p6083_3 := h6083c.2.2.2
                        linarith only [hlam, p6083_0]
                      · have p6083_0 := h6083c.1
                        have p6083_1 := h6083c.2.1
                        have p6083_2 := h6083c.2.2.1
                        have p6083_3 := h6083c.2.2.2
                        rcases p6083_3 (m.d 0 1) (by simp) with h6138 | h6138
                        · rcases p6083_3 (m.d 0 2) (by simp) with h6139 | h6139
                          · rcases p6083_3 (m.d 0 3) (by simp) with h6140 | h6140
                            · linarith only [h4, h6140, hlam]
                            · rcases p6083_3 (m.d 0 4) (by simp) with h6142 | h6142
                              · linarith only [h5, h6142, hlam]
                              · linarith only [h6142, h7, hlam]
                          · linarith only [h4, h6139, hlam]
                        · linarith only [h1, h6138, hlam]
                      · have p6083_0 := h6083c.1
                        have p6083_1 := h6083c.2.1
                        have p6083_2 := h6083c.2.2.1
                        have p6083_3 := h6083c.2.2.2
                        rcases p6083_3 (m.d 0 1) (by simp) with h6147 | h6147
                        · rcases p6083_3 (m.d 0 2) (by simp) with h6148 | h6148
                          · rcases p6083_3 (m.d 0 3) (by simp) with h6149 | h6149
                            · linarith only [h4, h6149, hlam]
                            · rcases p6083_3 (m.d 0 4) (by simp) with h6151 | h6151
                              · linarith only [h5, h6151, hlam]
                              · rcases p6083_3 (m.d 0 5) (by simp) with h6153 | h6153
                                · linarith only [h6, h6153, hlam]
                                · linarith only [h4905, h6153, hlam]
                          · linarith only [h5, h6148, hlam]
                        · linarith only [h2, h6147, hlam]
                      · have p6083_0 := h6083c.1
                        have p6083_1 := h6083c.2.1
                        have p6083_2 := h6083c.2.2.1
                        have p6083_3 := h6083c.2.2.2
                        rcases p6083_3 (m.d 0 1) (by simp) with h6158 | h6158
                        · rcases p6083_3 (m.d 0 2) (by simp) with h6159 | h6159
                          · rcases p6083_3 (m.d 0 3) (by simp) with h6160 | h6160
                            · linarith only [h4, h6160, hlam]
                            · rcases p6083_3 (m.d 0 4) (by simp) with h6162 | h6162
                              · linarith only [h5, h6162, hlam]
                              · rcases p6083_3 (m.d 0 5) (by simp) with h6164 | h6164
                                · linarith only [h6, h6164, hlam]
                                · rcases h2bigk with h6166c | h6166c | h6166c | h6166c | h6166c | h6166c | h6166c | h6166c | h6166c | h6166c | h6166c | h6166c | h6166c | h6166c | h6166c | h6166c | h6166c | h6166c | h6166c | h6166c | h6166c | h6166c | h6166c | h6166c | h6166c
                                  · have p6166_0 := h6166c.1
                                    have p6166_1 := h6166c.2.1
                                    have p6166_2 := h6166c.2.2.1
                                    have p6166_3 := h6166c.2.2.2
                                    linarith only [hlam, p6166_0]
                                  · have p6166_0 := h6166c.1
                                    have p6166_1 := h6166c.2.1
                                    have p6166_2 := h6166c.2.2.1
                                    have p6166_3 := h6166c.2.2.2
                                    rcases p6166_3 (m.d 0 2) (by simp) with h6168 | h6168
                                    · rcases p6166_3 (m.d 1 2) (by simp) with h6169 | h6169
                                      · linarith only [h0, h6169, hlam]
                                      · rcases p6166_3 (m.d 2 3) (by simp) with h6171 | h6171
                                        · linarith only [h4, h6171, hlam]
                                        · rcases p6166_3 (m.d 2 4) (by simp) with h6173 | h6173
                                          · linarith only [h5, h6173, hlam]
                                          · rcases p6166_3 (m.d 2 5) (by simp) with h6175 | h6175
                                            · linarith only [h6, h6175, hlam]
                                            · rcases h3bigk with h6177c | h6177c | h6177c | h6177c | h6177c | h6177c | h6177c | h6177c | h6177c | h6177c | h6177c | h6177c | h6177c | h6177c | h6177c | h6177c | h6177c | h6177c | h6177c | h6177c | h6177c | h6177c | h6177c | h6177c | h6177c
                                              · have p6177_0 := h6177c.1
                                                have p6177_1 := h6177c.2.1
                                                have p6177_2 := h6177c.2.2.1
                                                have p6177_3 := h6177c.2.2.2
                                                linarith only [hlam, p6177_0]
                                              · have p6177_0 := h6177c.1
                                                have p6177_1 := h6177c.2.1
                                                have p6177_2 := h6177c.2.2.1
                                                have p6177_3 := h6177c.2.2.2
                                                linarith only [h6067, h7, hc23, hc34, hlam, hphi, p6177_1]
                                              · have p6177_0 := h6177c.1
                                                have p6177_1 := h6177c.2.1
                                                have p6177_2 := h6177c.2.2.1
                                                have p6177_3 := h6177c.2.2.2
                                                linarith only [h7, hc23, hc34, hlam, hphi, p6177_1]
                                              · have p6177_0 := h6177c.1
                                                have p6177_1 := h6177c.2.1
                                                have p6177_2 := h6177c.2.2.1
                                                have p6177_3 := h6177c.2.2.2
                                                linarith only [h7, hlam, p6177_0]
                                              · have p6177_0 := h6177c.1
                                                have p6177_1 := h6177c.2.1
                                                have p6177_2 := h6177c.2.2.1
                                                have p6177_3 := h6177c.2.2.2
                                                linarith only [h4388, hlam, p6177_0]
                                              · have p6177_0 := h6177c.1
                                                have p6177_1 := h6177c.2.1
                                                have p6177_2 := h6177c.2.2.1
                                                have p6177_3 := h6177c.2.2.2
                                                linarith only [h1, hlam, p6177_0]
                                              · have p6177_0 := h6177c.1
                                                have p6177_1 := h6177c.2.1
                                                have p6177_2 := h6177c.2.2.1
                                                have p6177_3 := h6177c.2.2.2
                                                linarith only [hlam, p6177_0]
                                              · have p6177_0 := h6177c.1
                                                have p6177_1 := h6177c.2.1
                                                have p6177_2 := h6177c.2.2.1
                                                have p6177_3 := h6177c.2.2.2
                                                linarith only [h1, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6177_1]
                                              · have p6177_0 := h6177c.1
                                                have p6177_1 := h6177c.2.1
                                                have p6177_2 := h6177c.2.2.1
                                                have p6177_3 := h6177c.2.2.2
                                                linarith only [h6070, hlam, p6177_0]
                                              · have p6177_0 := h6177c.1
                                                have p6177_1 := h6177c.2.1
                                                have p6177_2 := h6177c.2.2.1
                                                have p6177_3 := h6177c.2.2.2
                                                linarith only [h6072, hlam, p6177_0]
                                              · have p6177_0 := h6177c.1
                                                have p6177_1 := h6177c.2.1
                                                have p6177_2 := h6177c.2.2.1
                                                have p6177_3 := h6177c.2.2.2
                                                linarith only [h4, hlam, p6177_0]
                                              · have p6177_0 := h6177c.1
                                                have p6177_1 := h6177c.2.1
                                                have p6177_2 := h6177c.2.2.1
                                                have p6177_3 := h6177c.2.2.2
                                                linarith only [h6067, hlam, p6177_0]
                                              · have p6177_0 := h6177c.1
                                                have p6177_1 := h6177c.2.1
                                                have p6177_2 := h6177c.2.2.1
                                                have p6177_3 := h6177c.2.2.2
                                                linarith only [hlam, p6177_0]
                                              · have p6177_0 := h6177c.1
                                                have p6177_1 := h6177c.2.1
                                                have p6177_2 := h6177c.2.2.1
                                                have p6177_3 := h6177c.2.2.2
                                                linarith only [h6076, hlam, p6177_0]
                                              · have p6177_0 := h6177c.1
                                                have p6177_1 := h6177c.2.1
                                                have p6177_2 := h6177c.2.2.1
                                                have p6177_3 := h6177c.2.2.2
                                                linarith only [h6078, hlam, p6177_0]
                                              · have p6177_0 := h6177c.1
                                                have p6177_1 := h6177c.2.1
                                                have p6177_2 := h6177c.2.2.1
                                                have p6177_3 := h6177c.2.2.2
                                                linarith only [hc03, hc34, hlam, hphi, p6177_1]
                                              · have p6177_0 := h6177c.1
                                                have p6177_1 := h6177c.2.1
                                                have p6177_2 := h6177c.2.2.1
                                                have p6177_3 := h6177c.2.2.2
                                                linarith only [h6067, hc23, hc34, hlam, hphi, p6177_1]
                                              · have p6177_0 := h6177c.1
                                                have p6177_1 := h6177c.2.1
                                                have p6177_2 := h6177c.2.2.1
                                                have p6177_3 := h6177c.2.2.2
                                                linarith only [hc23, hc34, hlam, hphi, p6177_1]
                                              · have p6177_0 := h6177c.1
                                                have p6177_1 := h6177c.2.1
                                                have p6177_2 := h6177c.2.2.1
                                                have p6177_3 := h6177c.2.2.2
                                                linarith only [hlam, p6177_0]
                                              · have p6177_0 := h6177c.1
                                                have p6177_1 := h6177c.2.1
                                                have p6177_2 := h6177c.2.2.1
                                                have p6177_3 := h6177c.2.2.2
                                                linarith only [h4905, h6082, hc04, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p6177_1]
                                              · have p6177_0 := h6177c.1
                                                have p6177_1 := h6177c.2.1
                                                have p6177_2 := h6177c.2.2.1
                                                have p6177_3 := h6177c.2.2.2
                                                linarith only [h1, h6067, hc23, hc35, hlam, hphi, p6177_1]
                                              · have p6177_0 := h6177c.1
                                                have p6177_1 := h6177c.2.1
                                                have p6177_2 := h6177c.2.2.1
                                                have p6177_3 := h6177c.2.2.2
                                                linarith only [h6067, hc23, hc35, hlam, hphi, p6177_1]
                                              · have p6177_0 := h6177c.1
                                                have p6177_1 := h6177c.2.1
                                                have p6177_2 := h6177c.2.2.1
                                                have p6177_3 := h6177c.2.2.2
                                                linarith only [hc23, hc35, hlam, hphi, p6177_1]
                                              · have p6177_0 := h6177c.1
                                                have p6177_1 := h6177c.2.1
                                                have p6177_2 := h6177c.2.2.1
                                                have p6177_3 := h6177c.2.2.2
                                                linarith only [h6082, hlam, p6177_0]
                                              · have p6177_0 := h6177c.1
                                                have p6177_1 := h6177c.2.1
                                                have p6177_2 := h6177c.2.2.1
                                                have p6177_3 := h6177c.2.2.2
                                                linarith only [hlam, p6177_0]
                                    · linarith only [h0, h6168, hlam]
                                  · have p6166_0 := h6166c.1
                                    have p6166_1 := h6166c.2.1
                                    have p6166_2 := h6166c.2.2.1
                                    have p6166_3 := h6166c.2.2.2
                                    rcases p6166_3 (m.d 0 2) (by simp) with h6204 | h6204
                                    · rcases p6166_3 (m.d 1 2) (by simp) with h6205 | h6205
                                      · linarith only [h0, h6205, hlam]
                                      · linarith only [h6067, h6205, hlam]
                                    · linarith only [h6204, hlam, p6166_0]
                                  · have p6166_0 := h6166c.1
                                    have p6166_1 := h6166c.2.1
                                    have p6166_2 := h6166c.2.2.1
                                    have p6166_3 := h6166c.2.2.2
                                    rcases p6166_3 (m.d 0 2) (by simp) with h6209 | h6209
                                    · rcases p6166_3 (m.d 1 2) (by simp) with h6210 | h6210
                                      · linarith only [h0, h6210, hlam]
                                      · linarith only [h6068, h6210, hlam]
                                    · linarith only [h6209, hlam, p6166_0]
                                  · have p6166_0 := h6166c.1
                                    have p6166_1 := h6166c.2.1
                                    have p6166_2 := h6166c.2.2.1
                                    have p6166_3 := h6166c.2.2.2
                                    rcases p6166_3 (m.d 0 2) (by simp) with h6214 | h6214
                                    · rcases p6166_3 (m.d 1 2) (by simp) with h6215 | h6215
                                      · linarith only [h0, h6215, hlam]
                                      · linarith only [h6069, h6215, hlam]
                                    · linarith only [h6214, hlam, p6166_0]
                                  · have p6166_0 := h6166c.1
                                    have p6166_1 := h6166c.2.1
                                    have p6166_2 := h6166c.2.2.1
                                    have p6166_3 := h6166c.2.2.2
                                    linarith only [h0, hlam, p6166_0]
                                  · have p6166_0 := h6166c.1
                                    have p6166_1 := h6166c.2.1
                                    have p6166_2 := h6166c.2.2.1
                                    have p6166_3 := h6166c.2.2.2
                                    linarith only [hlam, p6166_0]
                                  · have p6166_0 := h6166c.1
                                    have p6166_1 := h6166c.2.1
                                    have p6166_2 := h6166c.2.2.1
                                    have p6166_3 := h6166c.2.2.2
                                    rcases p6166_3 (m.d 0 2) (by simp) with h6221 | h6221
                                    · rcases p6166_3 (m.d 1 2) (by simp) with h6222 | h6222
                                      · rcases p6166_3 (m.d 2 3) (by simp) with h6223 | h6223
                                        · linarith only [h6223, hlam, p6166_0]
                                        · rcases p6166_3 (m.d 2 4) (by simp) with h6225 | h6225
                                          · linarith only [h6068, h6225, hlam]
                                          · linarith only [h6076, h6225, hlam]
                                      · linarith only [h6222, hlam, p6166_0]
                                    · linarith only [h4, h6221, hlam]
                                  · have p6166_0 := h6166c.1
                                    have p6166_1 := h6166c.2.1
                                    have p6166_2 := h6166c.2.2.1
                                    have p6166_3 := h6166c.2.2.2
                                    rcases p6166_3 (m.d 0 2) (by simp) with h6230 | h6230
                                    · rcases p6166_3 (m.d 1 2) (by simp) with h6231 | h6231
                                      · rcases p6166_3 (m.d 2 3) (by simp) with h6232 | h6232
                                        · linarith only [h6067, h6232, hlam]
                                        · rcases p6166_3 (m.d 2 4) (by simp) with h6234 | h6234
                                          · linarith only [h6234, hlam, p6166_0]
                                          · rcases p6166_3 (m.d 2 5) (by simp) with h6236 | h6236
                                            · linarith only [h6069, h6236, hlam]
                                            · linarith only [h6080, h6236, hlam]
                                      · linarith only [h6231, hlam, p6166_0]
                                    · linarith only [h5, h6230, hlam]
                                  · have p6166_0 := h6166c.1
                                    have p6166_1 := h6166c.2.1
                                    have p6166_2 := h6166c.2.2.1
                                    have p6166_3 := h6166c.2.2.2
                                    rcases p6166_3 (m.d 0 2) (by simp) with h6241 | h6241
                                    · rcases p6166_3 (m.d 1 2) (by simp) with h6242 | h6242
                                      · rcases p6166_3 (m.d 2 3) (by simp) with h6243 | h6243
                                        · linarith only [h6067, h6243, hlam]
                                        · rcases p6166_3 (m.d 2 4) (by simp) with h6245 | h6245
                                          · linarith only [h6068, h6245, hlam]
                                          · rcases p6166_3 (m.d 2 5) (by simp) with h6247 | h6247
                                            · linarith only [h6247, hlam, p6166_0]
                                            · rcases h3bigk with h6249c | h6249c | h6249c | h6249c | h6249c | h6249c | h6249c | h6249c | h6249c | h6249c | h6249c | h6249c | h6249c | h6249c | h6249c | h6249c | h6249c | h6249c | h6249c | h6249c | h6249c | h6249c | h6249c | h6249c | h6249c
                                              · have p6249_0 := h6249c.1
                                                have p6249_1 := h6249c.2.1
                                                have p6249_2 := h6249c.2.2.1
                                                have p6249_3 := h6249c.2.2.2
                                                linarith only [hlam, p6249_0]
                                              · have p6249_0 := h6249c.1
                                                have p6249_1 := h6249c.2.1
                                                have p6249_2 := h6249c.2.2.1
                                                have p6249_3 := h6249c.2.2.2
                                                linarith only [h4905, h6067, h7, hc23, hc45, hlam, hphi, ht34, p6249_1]
                                              · have p6249_0 := h6249c.1
                                                have p6249_1 := h6249c.2.1
                                                have p6249_2 := h6249c.2.2.1
                                                have p6249_3 := h6249c.2.2.2
                                                linarith only [h4905, h7, hc23, hc45, hlam, hphi, ht34, p6249_1]
                                              · have p6249_0 := h6249c.1
                                                have p6249_1 := h6249c.2.1
                                                have p6249_2 := h6249c.2.2.1
                                                have p6249_3 := h6249c.2.2.2
                                                linarith only [h7, hlam, p6249_0]
                                              · have p6249_0 := h6249c.1
                                                have p6249_1 := h6249c.2.1
                                                have p6249_2 := h6249c.2.2.1
                                                have p6249_3 := h6249c.2.2.2
                                                linarith only [h4388, hlam, p6249_0]
                                              · have p6249_0 := h6249c.1
                                                have p6249_1 := h6249c.2.1
                                                have p6249_2 := h6249c.2.2.1
                                                have p6249_3 := h6249c.2.2.2
                                                linarith only [h1, hlam, p6249_0]
                                              · have p6249_0 := h6249c.1
                                                have p6249_1 := h6249c.2.1
                                                have p6249_2 := h6249c.2.2.1
                                                have p6249_3 := h6249c.2.2.2
                                                linarith only [hlam, p6249_0]
                                              · have p6249_0 := h6249c.1
                                                have p6249_1 := h6249c.2.1
                                                have p6249_2 := h6249c.2.2.1
                                                have p6249_3 := h6249c.2.2.2
                                                linarith only [h1, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6249_1]
                                              · have p6249_0 := h6249c.1
                                                have p6249_1 := h6249c.2.1
                                                have p6249_2 := h6249c.2.2.1
                                                have p6249_3 := h6249c.2.2.2
                                                linarith only [h6070, hlam, p6249_0]
                                              · have p6249_0 := h6249c.1
                                                have p6249_1 := h6249c.2.1
                                                have p6249_2 := h6249c.2.2.1
                                                have p6249_3 := h6249c.2.2.2
                                                linarith only [h6072, hlam, p6249_0]
                                              · have p6249_0 := h6249c.1
                                                have p6249_1 := h6249c.2.1
                                                have p6249_2 := h6249c.2.2.1
                                                have p6249_3 := h6249c.2.2.2
                                                linarith only [h4, hlam, p6249_0]
                                              · have p6249_0 := h6249c.1
                                                have p6249_1 := h6249c.2.1
                                                have p6249_2 := h6249c.2.2.1
                                                have p6249_3 := h6249c.2.2.2
                                                linarith only [h6067, hlam, p6249_0]
                                              · have p6249_0 := h6249c.1
                                                have p6249_1 := h6249c.2.1
                                                have p6249_2 := h6249c.2.2.1
                                                have p6249_3 := h6249c.2.2.2
                                                linarith only [hlam, p6249_0]
                                              · have p6249_0 := h6249c.1
                                                have p6249_1 := h6249c.2.1
                                                have p6249_2 := h6249c.2.2.1
                                                have p6249_3 := h6249c.2.2.2
                                                linarith only [h6076, hlam, p6249_0]
                                              · have p6249_0 := h6249c.1
                                                have p6249_1 := h6249c.2.1
                                                have p6249_2 := h6249c.2.2.1
                                                have p6249_3 := h6249c.2.2.2
                                                linarith only [h6078, hlam, p6249_0]
                                              · have p6249_0 := h6249c.1
                                                have p6249_1 := h6249c.2.1
                                                have p6249_2 := h6249c.2.2.1
                                                have p6249_3 := h6249c.2.2.2
                                                linarith only [hc03, hc34, hlam, hphi, p6249_1]
                                              · have p6249_0 := h6249c.1
                                                have p6249_1 := h6249c.2.1
                                                have p6249_2 := h6249c.2.2.1
                                                have p6249_3 := h6249c.2.2.2
                                                linarith only [h6067, hc23, hc34, hlam, hphi, p6249_1]
                                              · have p6249_0 := h6249c.1
                                                have p6249_1 := h6249c.2.1
                                                have p6249_2 := h6249c.2.2.1
                                                have p6249_3 := h6249c.2.2.2
                                                linarith only [hc23, hc34, hlam, hphi, p6249_1]
                                              · have p6249_0 := h6249c.1
                                                have p6249_1 := h6249c.2.1
                                                have p6249_2 := h6249c.2.2.1
                                                have p6249_3 := h6249c.2.2.2
                                                linarith only [hlam, p6249_0]
                                              · have p6249_0 := h6249c.1
                                                have p6249_1 := h6249c.2.1
                                                have p6249_2 := h6249c.2.2.1
                                                have p6249_3 := h6249c.2.2.2
                                                linarith only [h1, h4388, h6067, hc23, hc34, hlam, hphi, p6249_1]
                                              · have p6249_0 := h6249c.1
                                                have p6249_1 := h6249c.2.1
                                                have p6249_2 := h6249c.2.2.1
                                                have p6249_3 := h6249c.2.2.2
                                                linarith only [h1, h6067, hc23, hc35, hlam, hphi, p6249_1]
                                              · have p6249_0 := h6249c.1
                                                have p6249_1 := h6249c.2.1
                                                have p6249_2 := h6249c.2.2.1
                                                have p6249_3 := h6249c.2.2.2
                                                linarith only [h6067, hc23, hc35, hlam, hphi, p6249_1]
                                              · have p6249_0 := h6249c.1
                                                have p6249_1 := h6249c.2.1
                                                have p6249_2 := h6249c.2.2.1
                                                have p6249_3 := h6249c.2.2.2
                                                linarith only [hc23, hc35, hlam, hphi, p6249_1]
                                              · have p6249_0 := h6249c.1
                                                have p6249_1 := h6249c.2.1
                                                have p6249_2 := h6249c.2.2.1
                                                have p6249_3 := h6249c.2.2.2
                                                linarith only [h6082, hlam, p6249_0]
                                              · have p6249_0 := h6249c.1
                                                have p6249_1 := h6249c.2.1
                                                have p6249_2 := h6249c.2.2.1
                                                have p6249_3 := h6249c.2.2.2
                                                linarith only [hlam, p6249_0]
                                      · linarith only [h6242, hlam, p6166_0]
                                    · linarith only [h6, h6241, hlam]
                                  · have p6166_0 := h6166c.1
                                    have p6166_1 := h6166c.2.1
                                    have p6166_2 := h6166c.2.2.1
                                    have p6166_3 := h6166c.2.2.2
                                    linarith only [h4, hlam, p6166_0]
                                  · have p6166_0 := h6166c.1
                                    have p6166_1 := h6166c.2.1
                                    have p6166_2 := h6166c.2.2.1
                                    have p6166_3 := h6166c.2.2.2
                                    linarith only [h6067, hlam, p6166_0]
                                  · have p6166_0 := h6166c.1
                                    have p6166_1 := h6166c.2.1
                                    have p6166_2 := h6166c.2.2.1
                                    have p6166_3 := h6166c.2.2.2
                                    linarith only [hlam, p6166_0]
                                  · have p6166_0 := h6166c.1
                                    have p6166_1 := h6166c.2.1
                                    have p6166_2 := h6166c.2.2.1
                                    have p6166_3 := h6166c.2.2.2
                                    linarith only [h6076, hlam, p6166_0]
                                  · have p6166_0 := h6166c.1
                                    have p6166_1 := h6166c.2.1
                                    have p6166_2 := h6166c.2.2.1
                                    have p6166_3 := h6166c.2.2.2
                                    linarith only [h6078, hlam, p6166_0]
                                  · have p6166_0 := h6166c.1
                                    have p6166_1 := h6166c.2.1
                                    have p6166_2 := h6166c.2.2.1
                                    have p6166_3 := h6166c.2.2.2
                                    linarith only [h5, hlam, p6166_0]
                                  · have p6166_0 := h6166c.1
                                    have p6166_1 := h6166c.2.1
                                    have p6166_2 := h6166c.2.2.1
                                    have p6166_3 := h6166c.2.2.2
                                    linarith only [h6068, hlam, p6166_0]
                                  · have p6166_0 := h6166c.1
                                    have p6166_1 := h6166c.2.1
                                    have p6166_2 := h6166c.2.2.1
                                    have p6166_3 := h6166c.2.2.2
                                    linarith only [h2, h4905, h6068, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6083_1, p6166_1]
                                  · have p6166_0 := h6166c.1
                                    have p6166_1 := h6166c.2.1
                                    have p6166_2 := h6166c.2.2.1
                                    have p6166_3 := h6166c.2.2.2
                                    linarith only [hlam, p6166_0]
                                  · have p6166_0 := h6166c.1
                                    have p6166_1 := h6166c.2.1
                                    have p6166_2 := h6166c.2.2.1
                                    have p6166_3 := h6166c.2.2.2
                                    linarith only [h6080, hlam, p6166_1]
                                  · have p6166_0 := h6166c.1
                                    have p6166_1 := h6166c.2.1
                                    have p6166_2 := h6166c.2.2.1
                                    have p6166_3 := h6166c.2.2.2
                                    linarith only [h6, hlam, p6166_0]
                                  · have p6166_0 := h6166c.1
                                    have p6166_1 := h6166c.2.1
                                    have p6166_2 := h6166c.2.2.1
                                    have p6166_3 := h6166c.2.2.2
                                    linarith only [h6069, hlam, p6166_0]
                                  · have p6166_0 := h6166c.1
                                    have p6166_1 := h6166c.2.1
                                    have p6166_2 := h6166c.2.2.1
                                    have p6166_3 := h6166c.2.2.2
                                    linarith only [h0, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6083_1, p6166_1]
                                  · have p6166_0 := h6166c.1
                                    have p6166_1 := h6166c.2.1
                                    have p6166_2 := h6166c.2.2.1
                                    have p6166_3 := h6166c.2.2.2
                                    linarith only [h0, h3, h6069, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p6083_1, p6166_1]
                                  · have p6166_0 := h6166c.1
                                    have p6166_1 := h6166c.2.1
                                    have p6166_2 := h6166c.2.2.1
                                    have p6166_3 := h6166c.2.2.2
                                    linarith only [hlam, p6166_0]
                          · linarith only [h6, h6159, hlam]
                        · linarith only [h3, h6158, hlam]
                      · have p6083_0 := h6083c.1
                        have p6083_1 := h6083c.2.1
                        have p6083_2 := h6083c.2.2.1
                        have p6083_3 := h6083c.2.2.2
                        linarith only [h1, hlam, p6083_1]
                      · have p6083_0 := h6083c.1
                        have p6083_1 := h6083c.2.1
                        have p6083_2 := h6083c.2.2.1
                        have p6083_3 := h6083c.2.2.2
                        linarith only [h4, hlam, p6083_1]
                      · have p6083_0 := h6083c.1
                        have p6083_1 := h6083c.2.1
                        have p6083_2 := h6083c.2.2.1
                        have p6083_3 := h6083c.2.2.2
                        linarith only [hlam, p6083_0]
                      · have p6083_0 := h6083c.1
                        have p6083_1 := h6083c.2.1
                        have p6083_2 := h6083c.2.2.1
                        have p6083_3 := h6083c.2.2.2
                        linarith only [h7, hlam, p6083_1]
                      · have p6083_0 := h6083c.1
                        have p6083_1 := h6083c.2.1
                        have p6083_2 := h6083c.2.2.1
                        have p6083_3 := h6083c.2.2.2
                        linarith only [h4388, hlam, p6083_1]
                      · have p6083_0 := h6083c.1
                        have p6083_1 := h6083c.2.1
                        have p6083_2 := h6083c.2.2.1
                        have p6083_3 := h6083c.2.2.2
                        linarith only [h2, hlam, p6083_0]
                      · have p6083_0 := h6083c.1
                        have p6083_1 := h6083c.2.1
                        have p6083_2 := h6083c.2.2.1
                        have p6083_3 := h6083c.2.2.2
                        linarith only [h5, hlam, p6083_0]
                      · have p6083_0 := h6083c.1
                        have p6083_1 := h6083c.2.1
                        have p6083_2 := h6083c.2.2.1
                        have p6083_3 := h6083c.2.2.2
                        linarith only [h1, h4905, h6067, hc23, hc45, hlam, hphi, ht34, p6083_1]
                      · have p6083_0 := h6083c.1
                        have p6083_1 := h6083c.2.1
                        have p6083_2 := h6083c.2.2.1
                        have p6083_3 := h6083c.2.2.2
                        linarith only [hlam, p6083_0]
                      · have p6083_0 := h6083c.1
                        have p6083_1 := h6083c.2.1
                        have p6083_2 := h6083c.2.2.1
                        have p6083_3 := h6083c.2.2.2
                        linarith only [h4905, hlam, p6083_0]
                      · have p6083_0 := h6083c.1
                        have p6083_1 := h6083c.2.1
                        have p6083_2 := h6083c.2.2.1
                        have p6083_3 := h6083c.2.2.2
                        linarith only [h3, hlam, p6083_0]
                      · have p6083_0 := h6083c.1
                        have p6083_1 := h6083c.2.1
                        have p6083_2 := h6083c.2.2.1
                        have p6083_3 := h6083c.2.2.2
                        linarith only [h6, hlam, p6083_1]
                      · have p6083_0 := h6083c.1
                        have p6083_1 := h6083c.2.1
                        have p6083_2 := h6083c.2.2.1
                        have p6083_3 := h6083c.2.2.2
                        linarith only [h1, h4905, h6067, h6082, hc23, hc34, hlam, hphi, p6083_1]
                      · have p6083_0 := h6083c.1
                        have p6083_1 := h6083c.2.1
                        have p6083_2 := h6083c.2.2.1
                        have p6083_3 := h6083c.2.2.2
                        linarith only [h4905, h5, h6076, h6082, hc23, hc34, hlam, hphi, p6083_1]
                      · have p6083_0 := h6083c.1
                        have p6083_1 := h6083c.2.1
                        have p6083_2 := h6083c.2.2.1
                        have p6083_3 := h6083c.2.2.2
                        linarith only [hlam, p6083_0]
                    · rcases h0bigk with h6309c | h6309c | h6309c | h6309c | h6309c | h6309c | h6309c | h6309c | h6309c | h6309c | h6309c | h6309c | h6309c | h6309c | h6309c | h6309c | h6309c | h6309c | h6309c | h6309c | h6309c | h6309c | h6309c | h6309c | h6309c
                      · have p6309_0 := h6309c.1
                        have p6309_1 := h6309c.2.1
                        have p6309_2 := h6309c.2.2.1
                        have p6309_3 := h6309c.2.2.2
                        linarith only [hlam, p6309_0]
                      · have p6309_0 := h6309c.1
                        have p6309_1 := h6309c.2.1
                        have p6309_2 := h6309c.2.2.1
                        have p6309_3 := h6309c.2.2.2
                        rcases p6309_3 (m.d 0 1) (by simp) with h6311 | h6311
                        · rcases p6309_3 (m.d 0 2) (by simp) with h6312 | h6312
                          · linarith only [h0, h6312, hlam]
                          · rcases p6309_3 (m.d 0 3) (by simp) with h6314 | h6314
                            · linarith only [h1, h6314, hlam]
                            · rcases p6309_3 (m.d 0 4) (by simp) with h6316 | h6316
                              · linarith only [h2, h6316, hlam]
                              · rcases p6309_3 (m.d 0 5) (by simp) with h6318 | h6318
                                · linarith only [h3, h6318, hlam]
                                · rcases h2bigk with h6320c | h6320c | h6320c | h6320c | h6320c | h6320c | h6320c | h6320c | h6320c | h6320c | h6320c | h6320c | h6320c | h6320c | h6320c | h6320c | h6320c | h6320c | h6320c | h6320c | h6320c | h6320c | h6320c | h6320c | h6320c
                                  · have p6320_0 := h6320c.1
                                    have p6320_1 := h6320c.2.1
                                    have p6320_2 := h6320c.2.2.1
                                    have p6320_3 := h6320c.2.2.2
                                    linarith only [hlam, p6320_0]
                                  · have p6320_0 := h6320c.1
                                    have p6320_1 := h6320c.2.1
                                    have p6320_2 := h6320c.2.2.1
                                    have p6320_3 := h6320c.2.2.2
                                    linarith only [h6069, h6076, h6080, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6309_1, p6320_1]
                                  · have p6320_0 := h6320c.1
                                    have p6320_1 := h6320c.2.1
                                    have p6320_2 := h6320c.2.2.1
                                    have p6320_3 := h6320c.2.2.2
                                    linarith only [hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6309_1, p6320_1]
                                  · have p6320_0 := h6320c.1
                                    have p6320_1 := h6320c.2.1
                                    have p6320_2 := h6320c.2.2.1
                                    have p6320_3 := h6320c.2.2.2
                                    linarith only [h6076, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6309_1, p6320_1]
                                  · have p6320_0 := h6320c.1
                                    have p6320_1 := h6320c.2.1
                                    have p6320_2 := h6320c.2.2.1
                                    have p6320_3 := h6320c.2.2.2
                                    linarith only [h6076, h6080, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6309_1, p6320_1]
                                  · have p6320_0 := h6320c.1
                                    have p6320_1 := h6320c.2.1
                                    have p6320_2 := h6320c.2.2.1
                                    have p6320_3 := h6320c.2.2.2
                                    linarith only [h0, hlam, p6320_0]
                                  · have p6320_0 := h6320c.1
                                    have p6320_1 := h6320c.2.1
                                    have p6320_2 := h6320c.2.2.1
                                    have p6320_3 := h6320c.2.2.2
                                    linarith only [hlam, p6320_0]
                                  · have p6320_0 := h6320c.1
                                    have p6320_1 := h6320c.2.1
                                    have p6320_2 := h6320c.2.2.1
                                    have p6320_3 := h6320c.2.2.2
                                    linarith only [h0, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6309_1, p6320_1]
                                  · have p6320_0 := h6320c.1
                                    have p6320_1 := h6320c.2.1
                                    have p6320_2 := h6320c.2.2.1
                                    have p6320_3 := h6320c.2.2.2
                                    linarith only [h0, h6076, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6309_1, p6320_1]
                                  · have p6320_0 := h6320c.1
                                    have p6320_1 := h6320c.2.1
                                    have p6320_2 := h6320c.2.2.1
                                    have p6320_3 := h6320c.2.2.2
                                    linarith only [h0, h6076, h6080, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6309_1, p6320_1]
                                  · have p6320_0 := h6320c.1
                                    have p6320_1 := h6320c.2.1
                                    have p6320_2 := h6320c.2.2.1
                                    have p6320_3 := h6320c.2.2.2
                                    linarith only [h4, hlam, p6320_0]
                                  · have p6320_0 := h6320c.1
                                    have p6320_1 := h6320c.2.1
                                    have p6320_2 := h6320c.2.2.1
                                    have p6320_3 := h6320c.2.2.2
                                    linarith only [h6067, hlam, p6320_0]
                                  · have p6320_0 := h6320c.1
                                    have p6320_1 := h6320c.2.1
                                    have p6320_2 := h6320c.2.2.1
                                    have p6320_3 := h6320c.2.2.2
                                    linarith only [hlam, p6320_0]
                                  · have p6320_0 := h6320c.1
                                    have p6320_1 := h6320c.2.1
                                    have p6320_2 := h6320c.2.2.1
                                    have p6320_3 := h6320c.2.2.2
                                    linarith only [h6076, hlam, p6320_0]
                                  · have p6320_0 := h6320c.1
                                    have p6320_1 := h6320c.2.1
                                    have p6320_2 := h6320c.2.2.1
                                    have p6320_3 := h6320c.2.2.2
                                    linarith only [h6078, hlam, p6320_0]
                                  · have p6320_0 := h6320c.1
                                    have p6320_1 := h6320c.2.1
                                    have p6320_2 := h6320c.2.2.1
                                    have p6320_3 := h6320c.2.2.2
                                    linarith only [h5, hlam, p6320_0]
                                  · have p6320_0 := h6320c.1
                                    have p6320_1 := h6320c.2.1
                                    have p6320_2 := h6320c.2.2.1
                                    have p6320_3 := h6320c.2.2.2
                                    linarith only [h6068, hlam, p6320_0]
                                  · have p6320_0 := h6320c.1
                                    have p6320_1 := h6320c.2.1
                                    have p6320_2 := h6320c.2.2.1
                                    have p6320_3 := h6320c.2.2.2
                                    linarith only [h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6309_1, p6320_1]
                                  · have p6320_0 := h6320c.1
                                    have p6320_1 := h6320c.2.1
                                    have p6320_2 := h6320c.2.2.1
                                    have p6320_3 := h6320c.2.2.2
                                    linarith only [hlam, p6320_0]
                                  · have p6320_0 := h6320c.1
                                    have p6320_1 := h6320c.2.1
                                    have p6320_2 := h6320c.2.2.1
                                    have p6320_3 := h6320c.2.2.2
                                    linarith only [h6080, hlam, p6320_1]
                                  · have p6320_0 := h6320c.1
                                    have p6320_1 := h6320c.2.1
                                    have p6320_2 := h6320c.2.2.1
                                    have p6320_3 := h6320c.2.2.2
                                    linarith only [h6, hlam, p6320_0]
                                  · have p6320_0 := h6320c.1
                                    have p6320_1 := h6320c.2.1
                                    have p6320_2 := h6320c.2.2.1
                                    have p6320_3 := h6320c.2.2.2
                                    linarith only [h6069, hlam, p6320_0]
                                  · have p6320_0 := h6320c.1
                                    have p6320_1 := h6320c.2.1
                                    have p6320_2 := h6320c.2.2.1
                                    have p6320_3 := h6320c.2.2.2
                                    linarith only [h0, h6069, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6309_1, p6320_1]
                                  · have p6320_0 := h6320c.1
                                    have p6320_1 := h6320c.2.1
                                    have p6320_2 := h6320c.2.2.1
                                    have p6320_3 := h6320c.2.2.2
                                    linarith only [h0, h6069, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p6309_1, p6320_1]
                                  · have p6320_0 := h6320c.1
                                    have p6320_1 := h6320c.2.1
                                    have p6320_2 := h6320c.2.2.1
                                    have p6320_3 := h6320c.2.2.2
                                    linarith only [hlam, p6320_0]
                        · linarith only [h0, h6311, hlam]
                      · have p6309_0 := h6309c.1
                        have p6309_1 := h6309c.2.1
                        have p6309_2 := h6309c.2.2.1
                        have p6309_3 := h6309c.2.2.2
                        rcases p6309_3 (m.d 0 1) (by simp) with h6347 | h6347
                        · rcases p6309_3 (m.d 0 2) (by simp) with h6348 | h6348
                          · linarith only [h0, h6348, hlam]
                          · linarith only [h4, h6348, hlam]
                        · linarith only [h1, h6347, hlam]
                      · have p6309_0 := h6309c.1
                        have p6309_1 := h6309c.2.1
                        have p6309_2 := h6309c.2.2.1
                        have p6309_3 := h6309c.2.2.2
                        rcases p6309_3 (m.d 0 1) (by simp) with h6352 | h6352
                        · rcases p6309_3 (m.d 0 2) (by simp) with h6353 | h6353
                          · linarith only [h0, h6353, hlam]
                          · linarith only [h5, h6353, hlam]
                        · linarith only [h2, h6352, hlam]
                      · have p6309_0 := h6309c.1
                        have p6309_1 := h6309c.2.1
                        have p6309_2 := h6309c.2.2.1
                        have p6309_3 := h6309c.2.2.2
                        rcases p6309_3 (m.d 0 1) (by simp) with h6357 | h6357
                        · rcases p6309_3 (m.d 0 2) (by simp) with h6358 | h6358
                          · linarith only [h0, h6358, hlam]
                          · linarith only [h6, h6358, hlam]
                        · linarith only [h3, h6357, hlam]
                      · have p6309_0 := h6309c.1
                        have p6309_1 := h6309c.2.1
                        have p6309_2 := h6309c.2.2.1
                        have p6309_3 := h6309c.2.2.2
                        linarith only [h0, hlam, p6309_0]
                      · have p6309_0 := h6309c.1
                        have p6309_1 := h6309c.2.1
                        have p6309_2 := h6309c.2.2.1
                        have p6309_3 := h6309c.2.2.2
                        linarith only [hlam, p6309_0]
                      · have p6309_0 := h6309c.1
                        have p6309_1 := h6309c.2.1
                        have p6309_2 := h6309c.2.2.1
                        have p6309_3 := h6309c.2.2.2
                        rcases p6309_3 (m.d 0 1) (by simp) with h6364 | h6364
                        · rcases p6309_3 (m.d 0 2) (by simp) with h6365 | h6365
                          · rcases p6309_3 (m.d 0 3) (by simp) with h6366 | h6366
                            · linarith only [h4, h6366, hlam]
                            · rcases p6309_3 (m.d 0 4) (by simp) with h6368 | h6368
                              · linarith only [h5, h6368, hlam]
                              · linarith only [h6368, h7, hlam]
                          · linarith only [h4, h6365, hlam]
                        · linarith only [h1, h6364, hlam]
                      · have p6309_0 := h6309c.1
                        have p6309_1 := h6309c.2.1
                        have p6309_2 := h6309c.2.2.1
                        have p6309_3 := h6309c.2.2.2
                        rcases p6309_3 (m.d 0 1) (by simp) with h6373 | h6373
                        · rcases p6309_3 (m.d 0 2) (by simp) with h6374 | h6374
                          · rcases p6309_3 (m.d 0 3) (by simp) with h6375 | h6375
                            · linarith only [h4, h6375, hlam]
                            · rcases p6309_3 (m.d 0 4) (by simp) with h6377 | h6377
                              · linarith only [h5, h6377, hlam]
                              · rcases p6309_3 (m.d 0 5) (by simp) with h6379 | h6379
                                · linarith only [h6, h6379, hlam]
                                · linarith only [h4905, h6379, hlam]
                          · linarith only [h5, h6374, hlam]
                        · linarith only [h2, h6373, hlam]
                      · have p6309_0 := h6309c.1
                        have p6309_1 := h6309c.2.1
                        have p6309_2 := h6309c.2.2.1
                        have p6309_3 := h6309c.2.2.2
                        rcases p6309_3 (m.d 0 1) (by simp) with h6384 | h6384
                        · rcases p6309_3 (m.d 0 2) (by simp) with h6385 | h6385
                          · rcases p6309_3 (m.d 0 3) (by simp) with h6386 | h6386
                            · linarith only [h4, h6386, hlam]
                            · rcases p6309_3 (m.d 0 4) (by simp) with h6388 | h6388
                              · linarith only [h5, h6388, hlam]
                              · rcases p6309_3 (m.d 0 5) (by simp) with h6390 | h6390
                                · linarith only [h6, h6390, hlam]
                                · rcases h2bigk with h6392c | h6392c | h6392c | h6392c | h6392c | h6392c | h6392c | h6392c | h6392c | h6392c | h6392c | h6392c | h6392c | h6392c | h6392c | h6392c | h6392c | h6392c | h6392c | h6392c | h6392c | h6392c | h6392c | h6392c | h6392c
                                  · have p6392_0 := h6392c.1
                                    have p6392_1 := h6392c.2.1
                                    have p6392_2 := h6392c.2.2.1
                                    have p6392_3 := h6392c.2.2.2
                                    linarith only [hlam, p6392_0]
                                  · have p6392_0 := h6392c.1
                                    have p6392_1 := h6392c.2.1
                                    have p6392_2 := h6392c.2.2.1
                                    have p6392_3 := h6392c.2.2.2
                                    rcases p6392_3 (m.d 0 2) (by simp) with h6394 | h6394
                                    · rcases p6392_3 (m.d 1 2) (by simp) with h6395 | h6395
                                      · linarith only [h0, h6395, hlam]
                                      · rcases p6392_3 (m.d 2 3) (by simp) with h6397 | h6397
                                        · linarith only [h4, h6397, hlam]
                                        · rcases p6392_3 (m.d 2 4) (by simp) with h6399 | h6399
                                          · linarith only [h5, h6399, hlam]
                                          · rcases p6392_3 (m.d 2 5) (by simp) with h6401 | h6401
                                            · linarith only [h6, h6401, hlam]
                                            · rcases h3bigk with h6403c | h6403c | h6403c | h6403c | h6403c | h6403c | h6403c | h6403c | h6403c | h6403c | h6403c | h6403c | h6403c | h6403c | h6403c | h6403c | h6403c | h6403c | h6403c | h6403c | h6403c | h6403c | h6403c | h6403c | h6403c
                                              · have p6403_0 := h6403c.1
                                                have p6403_1 := h6403c.2.1
                                                have p6403_2 := h6403c.2.2.1
                                                have p6403_3 := h6403c.2.2.2
                                                linarith only [hlam, p6403_0]
                                              · have p6403_0 := h6403c.1
                                                have p6403_1 := h6403c.2.1
                                                have p6403_2 := h6403c.2.2.1
                                                have p6403_3 := h6403c.2.2.2
                                                linarith only [h4905, h6067, h7, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6309_1, p6403_1]
                                              · have p6403_0 := h6403c.1
                                                have p6403_1 := h6403c.2.1
                                                have p6403_2 := h6403c.2.2.1
                                                have p6403_3 := h6403c.2.2.2
                                                linarith only [h0, h4905, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6309_1, p6403_1]
                                              · have p6403_0 := h6403c.1
                                                have p6403_1 := h6403c.2.1
                                                have p6403_2 := h6403c.2.2.1
                                                have p6403_3 := h6403c.2.2.2
                                                linarith only [h7, hlam, p6403_0]
                                              · have p6403_0 := h6403c.1
                                                have p6403_1 := h6403c.2.1
                                                have p6403_2 := h6403c.2.2.1
                                                have p6403_3 := h6403c.2.2.2
                                                linarith only [h4388, hlam, p6403_0]
                                              · have p6403_0 := h6403c.1
                                                have p6403_1 := h6403c.2.1
                                                have p6403_2 := h6403c.2.2.1
                                                have p6403_3 := h6403c.2.2.2
                                                linarith only [h1, hlam, p6403_0]
                                              · have p6403_0 := h6403c.1
                                                have p6403_1 := h6403c.2.1
                                                have p6403_2 := h6403c.2.2.1
                                                have p6403_3 := h6403c.2.2.2
                                                linarith only [hlam, p6403_0]
                                              · have p6403_0 := h6403c.1
                                                have p6403_1 := h6403c.2.1
                                                have p6403_2 := h6403c.2.2.1
                                                have p6403_3 := h6403c.2.2.2
                                                linarith only [h1, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6403_1]
                                              · have p6403_0 := h6403c.1
                                                have p6403_1 := h6403c.2.1
                                                have p6403_2 := h6403c.2.2.1
                                                have p6403_3 := h6403c.2.2.2
                                                linarith only [h6070, hlam, p6403_0]
                                              · have p6403_0 := h6403c.1
                                                have p6403_1 := h6403c.2.1
                                                have p6403_2 := h6403c.2.2.1
                                                have p6403_3 := h6403c.2.2.2
                                                linarith only [h6072, hlam, p6403_0]
                                              · have p6403_0 := h6403c.1
                                                have p6403_1 := h6403c.2.1
                                                have p6403_2 := h6403c.2.2.1
                                                have p6403_3 := h6403c.2.2.2
                                                linarith only [h4, hlam, p6403_0]
                                              · have p6403_0 := h6403c.1
                                                have p6403_1 := h6403c.2.1
                                                have p6403_2 := h6403c.2.2.1
                                                have p6403_3 := h6403c.2.2.2
                                                linarith only [h6067, hlam, p6403_0]
                                              · have p6403_0 := h6403c.1
                                                have p6403_1 := h6403c.2.1
                                                have p6403_2 := h6403c.2.2.1
                                                have p6403_3 := h6403c.2.2.2
                                                linarith only [hlam, p6403_0]
                                              · have p6403_0 := h6403c.1
                                                have p6403_1 := h6403c.2.1
                                                have p6403_2 := h6403c.2.2.1
                                                have p6403_3 := h6403c.2.2.2
                                                linarith only [h6076, hlam, p6403_0]
                                              · have p6403_0 := h6403c.1
                                                have p6403_1 := h6403c.2.1
                                                have p6403_2 := h6403c.2.2.1
                                                have p6403_3 := h6403c.2.2.2
                                                linarith only [h6078, hlam, p6403_0]
                                              · have p6403_0 := h6403c.1
                                                have p6403_1 := h6403c.2.1
                                                have p6403_2 := h6403c.2.2.1
                                                have p6403_3 := h6403c.2.2.2
                                                linarith only [h6082, hc03, hc45, hlam, hphi, ht34, p6403_1]
                                              · have p6403_0 := h6403c.1
                                                have p6403_1 := h6403c.2.1
                                                have p6403_2 := h6403c.2.2.1
                                                have p6403_3 := h6403c.2.2.2
                                                linarith only [h6067, h6082, hc23, hc45, hlam, hphi, ht34, p6403_1]
                                              · have p6403_0 := h6403c.1
                                                have p6403_1 := h6403c.2.1
                                                have p6403_2 := h6403c.2.2.1
                                                have p6403_3 := h6403c.2.2.2
                                                linarith only [h6082, hc23, hc45, hlam, hphi, ht34, p6403_1]
                                              · have p6403_0 := h6403c.1
                                                have p6403_1 := h6403c.2.1
                                                have p6403_2 := h6403c.2.2.1
                                                have p6403_3 := h6403c.2.2.2
                                                linarith only [hlam, p6403_0]
                                              · have p6403_0 := h6403c.1
                                                have p6403_1 := h6403c.2.1
                                                have p6403_2 := h6403c.2.2.1
                                                have p6403_3 := h6403c.2.2.2
                                                linarith only [h6082, hlam, p6403_1]
                                              · have p6403_0 := h6403c.1
                                                have p6403_1 := h6403c.2.1
                                                have p6403_2 := h6403c.2.2.1
                                                have p6403_3 := h6403c.2.2.2
                                                linarith only [h1, h6067, h6082, hc23, hc45, hlam, hphi, ht34, p6403_1]
                                              · have p6403_0 := h6403c.1
                                                have p6403_1 := h6403c.2.1
                                                have p6403_2 := h6403c.2.2.1
                                                have p6403_3 := h6403c.2.2.2
                                                linarith only [h6067, h6082, hc23, hc45, hlam, hphi, ht34, p6403_1]
                                              · have p6403_0 := h6403c.1
                                                have p6403_1 := h6403c.2.1
                                                have p6403_2 := h6403c.2.2.1
                                                have p6403_3 := h6403c.2.2.2
                                                linarith only [h6082, hc23, hc45, hlam, hphi, ht34, p6403_1]
                                              · have p6403_0 := h6403c.1
                                                have p6403_1 := h6403c.2.1
                                                have p6403_2 := h6403c.2.2.1
                                                have p6403_3 := h6403c.2.2.2
                                                linarith only [h6082, hc34, hc45, hlam, hphi, p6403_1]
                                              · have p6403_0 := h6403c.1
                                                have p6403_1 := h6403c.2.1
                                                have p6403_2 := h6403c.2.2.1
                                                have p6403_3 := h6403c.2.2.2
                                                linarith only [hlam, p6403_0]
                                    · linarith only [h0, h6394, hlam]
                                  · have p6392_0 := h6392c.1
                                    have p6392_1 := h6392c.2.1
                                    have p6392_2 := h6392c.2.2.1
                                    have p6392_3 := h6392c.2.2.2
                                    rcases p6392_3 (m.d 0 2) (by simp) with h6430 | h6430
                                    · rcases p6392_3 (m.d 1 2) (by simp) with h6431 | h6431
                                      · linarith only [h0, h6431, hlam]
                                      · linarith only [h6067, h6431, hlam]
                                    · linarith only [h6430, hlam, p6392_0]
                                  · have p6392_0 := h6392c.1
                                    have p6392_1 := h6392c.2.1
                                    have p6392_2 := h6392c.2.2.1
                                    have p6392_3 := h6392c.2.2.2
                                    rcases p6392_3 (m.d 0 2) (by simp) with h6435 | h6435
                                    · rcases p6392_3 (m.d 1 2) (by simp) with h6436 | h6436
                                      · linarith only [h0, h6436, hlam]
                                      · linarith only [h6068, h6436, hlam]
                                    · linarith only [h6435, hlam, p6392_0]
                                  · have p6392_0 := h6392c.1
                                    have p6392_1 := h6392c.2.1
                                    have p6392_2 := h6392c.2.2.1
                                    have p6392_3 := h6392c.2.2.2
                                    rcases p6392_3 (m.d 0 2) (by simp) with h6440 | h6440
                                    · rcases p6392_3 (m.d 1 2) (by simp) with h6441 | h6441
                                      · linarith only [h0, h6441, hlam]
                                      · linarith only [h6069, h6441, hlam]
                                    · linarith only [h6440, hlam, p6392_0]
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
                                    rcases p6392_3 (m.d 0 2) (by simp) with h6447 | h6447
                                    · rcases p6392_3 (m.d 1 2) (by simp) with h6448 | h6448
                                      · rcases p6392_3 (m.d 2 3) (by simp) with h6449 | h6449
                                        · linarith only [h6449, hlam, p6392_0]
                                        · rcases p6392_3 (m.d 2 4) (by simp) with h6451 | h6451
                                          · linarith only [h6068, h6451, hlam]
                                          · linarith only [h6076, h6451, hlam]
                                      · linarith only [h6448, hlam, p6392_0]
                                    · linarith only [h4, h6447, hlam]
                                  · have p6392_0 := h6392c.1
                                    have p6392_1 := h6392c.2.1
                                    have p6392_2 := h6392c.2.2.1
                                    have p6392_3 := h6392c.2.2.2
                                    rcases p6392_3 (m.d 0 2) (by simp) with h6456 | h6456
                                    · rcases p6392_3 (m.d 1 2) (by simp) with h6457 | h6457
                                      · rcases p6392_3 (m.d 2 3) (by simp) with h6458 | h6458
                                        · linarith only [h6067, h6458, hlam]
                                        · rcases p6392_3 (m.d 2 4) (by simp) with h6460 | h6460
                                          · linarith only [h6460, hlam, p6392_0]
                                          · rcases p6392_3 (m.d 2 5) (by simp) with h6462 | h6462
                                            · linarith only [h6069, h6462, hlam]
                                            · linarith only [h6080, h6462, hlam]
                                      · linarith only [h6457, hlam, p6392_0]
                                    · linarith only [h5, h6456, hlam]
                                  · have p6392_0 := h6392c.1
                                    have p6392_1 := h6392c.2.1
                                    have p6392_2 := h6392c.2.2.1
                                    have p6392_3 := h6392c.2.2.2
                                    rcases p6392_3 (m.d 0 2) (by simp) with h6467 | h6467
                                    · rcases p6392_3 (m.d 1 2) (by simp) with h6468 | h6468
                                      · rcases p6392_3 (m.d 2 3) (by simp) with h6469 | h6469
                                        · linarith only [h6067, h6469, hlam]
                                        · rcases p6392_3 (m.d 2 4) (by simp) with h6471 | h6471
                                          · linarith only [h6068, h6471, hlam]
                                          · rcases p6392_3 (m.d 2 5) (by simp) with h6473 | h6473
                                            · linarith only [h6473, hlam, p6392_0]
                                            · rcases h3bigk with h6475c | h6475c | h6475c | h6475c | h6475c | h6475c | h6475c | h6475c | h6475c | h6475c | h6475c | h6475c | h6475c | h6475c | h6475c | h6475c | h6475c | h6475c | h6475c | h6475c | h6475c | h6475c | h6475c | h6475c | h6475c
                                              · have p6475_0 := h6475c.1
                                                have p6475_1 := h6475c.2.1
                                                have p6475_2 := h6475c.2.2.1
                                                have p6475_3 := h6475c.2.2.2
                                                linarith only [hlam, p6475_0]
                                              · have p6475_0 := h6475c.1
                                                have p6475_1 := h6475c.2.1
                                                have p6475_2 := h6475c.2.2.1
                                                have p6475_3 := h6475c.2.2.2
                                                linarith only [h6067, h7, hc23, hc34, hlam, hphi, p6475_1]
                                              · have p6475_0 := h6475c.1
                                                have p6475_1 := h6475c.2.1
                                                have p6475_2 := h6475c.2.2.1
                                                have p6475_3 := h6475c.2.2.2
                                                linarith only [h7, hc23, hc34, hlam, hphi, p6475_1]
                                              · have p6475_0 := h6475c.1
                                                have p6475_1 := h6475c.2.1
                                                have p6475_2 := h6475c.2.2.1
                                                have p6475_3 := h6475c.2.2.2
                                                linarith only [h7, hlam, p6475_0]
                                              · have p6475_0 := h6475c.1
                                                have p6475_1 := h6475c.2.1
                                                have p6475_2 := h6475c.2.2.1
                                                have p6475_3 := h6475c.2.2.2
                                                linarith only [h4388, hlam, p6475_0]
                                              · have p6475_0 := h6475c.1
                                                have p6475_1 := h6475c.2.1
                                                have p6475_2 := h6475c.2.2.1
                                                have p6475_3 := h6475c.2.2.2
                                                linarith only [h1, hlam, p6475_0]
                                              · have p6475_0 := h6475c.1
                                                have p6475_1 := h6475c.2.1
                                                have p6475_2 := h6475c.2.2.1
                                                have p6475_3 := h6475c.2.2.2
                                                linarith only [hlam, p6475_0]
                                              · have p6475_0 := h6475c.1
                                                have p6475_1 := h6475c.2.1
                                                have p6475_2 := h6475c.2.2.1
                                                have p6475_3 := h6475c.2.2.2
                                                linarith only [h1, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6475_1]
                                              · have p6475_0 := h6475c.1
                                                have p6475_1 := h6475c.2.1
                                                have p6475_2 := h6475c.2.2.1
                                                have p6475_3 := h6475c.2.2.2
                                                linarith only [h6070, hlam, p6475_0]
                                              · have p6475_0 := h6475c.1
                                                have p6475_1 := h6475c.2.1
                                                have p6475_2 := h6475c.2.2.1
                                                have p6475_3 := h6475c.2.2.2
                                                linarith only [h6072, hlam, p6475_0]
                                              · have p6475_0 := h6475c.1
                                                have p6475_1 := h6475c.2.1
                                                have p6475_2 := h6475c.2.2.1
                                                have p6475_3 := h6475c.2.2.2
                                                linarith only [h4, hlam, p6475_0]
                                              · have p6475_0 := h6475c.1
                                                have p6475_1 := h6475c.2.1
                                                have p6475_2 := h6475c.2.2.1
                                                have p6475_3 := h6475c.2.2.2
                                                linarith only [h6067, hlam, p6475_0]
                                              · have p6475_0 := h6475c.1
                                                have p6475_1 := h6475c.2.1
                                                have p6475_2 := h6475c.2.2.1
                                                have p6475_3 := h6475c.2.2.2
                                                linarith only [hlam, p6475_0]
                                              · have p6475_0 := h6475c.1
                                                have p6475_1 := h6475c.2.1
                                                have p6475_2 := h6475c.2.2.1
                                                have p6475_3 := h6475c.2.2.2
                                                linarith only [h6076, hlam, p6475_0]
                                              · have p6475_0 := h6475c.1
                                                have p6475_1 := h6475c.2.1
                                                have p6475_2 := h6475c.2.2.1
                                                have p6475_3 := h6475c.2.2.2
                                                linarith only [h6078, hlam, p6475_0]
                                              · have p6475_0 := h6475c.1
                                                have p6475_1 := h6475c.2.1
                                                have p6475_2 := h6475c.2.2.1
                                                have p6475_3 := h6475c.2.2.2
                                                linarith only [hc03, hc34, hlam, hphi, p6475_1]
                                              · have p6475_0 := h6475c.1
                                                have p6475_1 := h6475c.2.1
                                                have p6475_2 := h6475c.2.2.1
                                                have p6475_3 := h6475c.2.2.2
                                                linarith only [hc13, hc34, hlam, hphi, p6475_1]
                                              · have p6475_0 := h6475c.1
                                                have p6475_1 := h6475c.2.1
                                                have p6475_2 := h6475c.2.2.1
                                                have p6475_3 := h6475c.2.2.2
                                                linarith only [hc23, hc34, hlam, hphi, p6475_1]
                                              · have p6475_0 := h6475c.1
                                                have p6475_1 := h6475c.2.1
                                                have p6475_2 := h6475c.2.2.1
                                                have p6475_3 := h6475c.2.2.2
                                                linarith only [hlam, p6475_0]
                                              · have p6475_0 := h6475c.1
                                                have p6475_1 := h6475c.2.1
                                                have p6475_2 := h6475c.2.2.1
                                                have p6475_3 := h6475c.2.2.2
                                                linarith only [h6082, hlam, p6475_1]
                                              · have p6475_0 := h6475c.1
                                                have p6475_1 := h6475c.2.1
                                                have p6475_2 := h6475c.2.2.1
                                                have p6475_3 := h6475c.2.2.2
                                                linarith only [h1, h6067, h6082, hc23, hc45, hlam, hphi, ht34, p6475_1]
                                              · have p6475_0 := h6475c.1
                                                have p6475_1 := h6475c.2.1
                                                have p6475_2 := h6475c.2.2.1
                                                have p6475_3 := h6475c.2.2.2
                                                linarith only [h6067, h6082, hc23, hc45, hlam, hphi, ht34, p6475_1]
                                              · have p6475_0 := h6475c.1
                                                have p6475_1 := h6475c.2.1
                                                have p6475_2 := h6475c.2.2.1
                                                have p6475_3 := h6475c.2.2.2
                                                linarith only [h6082, hc23, hc45, hlam, hphi, ht34, p6475_1]
                                              · have p6475_0 := h6475c.1
                                                have p6475_1 := h6475c.2.1
                                                have p6475_2 := h6475c.2.2.1
                                                have p6475_3 := h6475c.2.2.2
                                                linarith only [h6082, hc34, hc45, hlam, hphi, p6475_1]
                                              · have p6475_0 := h6475c.1
                                                have p6475_1 := h6475c.2.1
                                                have p6475_2 := h6475c.2.2.1
                                                have p6475_3 := h6475c.2.2.2
                                                linarith only [hlam, p6475_0]
                                      · linarith only [h6468, hlam, p6392_0]
                                    · linarith only [h6, h6467, hlam]
                                  · have p6392_0 := h6392c.1
                                    have p6392_1 := h6392c.2.1
                                    have p6392_2 := h6392c.2.2.1
                                    have p6392_3 := h6392c.2.2.2
                                    linarith only [h4, hlam, p6392_0]
                                  · have p6392_0 := h6392c.1
                                    have p6392_1 := h6392c.2.1
                                    have p6392_2 := h6392c.2.2.1
                                    have p6392_3 := h6392c.2.2.2
                                    linarith only [h6067, hlam, p6392_0]
                                  · have p6392_0 := h6392c.1
                                    have p6392_1 := h6392c.2.1
                                    have p6392_2 := h6392c.2.2.1
                                    have p6392_3 := h6392c.2.2.2
                                    linarith only [hlam, p6392_0]
                                  · have p6392_0 := h6392c.1
                                    have p6392_1 := h6392c.2.1
                                    have p6392_2 := h6392c.2.2.1
                                    have p6392_3 := h6392c.2.2.2
                                    linarith only [h6076, hlam, p6392_0]
                                  · have p6392_0 := h6392c.1
                                    have p6392_1 := h6392c.2.1
                                    have p6392_2 := h6392c.2.2.1
                                    have p6392_3 := h6392c.2.2.2
                                    linarith only [h6078, hlam, p6392_0]
                                  · have p6392_0 := h6392c.1
                                    have p6392_1 := h6392c.2.1
                                    have p6392_2 := h6392c.2.2.1
                                    have p6392_3 := h6392c.2.2.2
                                    linarith only [h5, hlam, p6392_0]
                                  · have p6392_0 := h6392c.1
                                    have p6392_1 := h6392c.2.1
                                    have p6392_2 := h6392c.2.2.1
                                    have p6392_3 := h6392c.2.2.2
                                    linarith only [h6068, hlam, p6392_0]
                                  · have p6392_0 := h6392c.1
                                    have p6392_1 := h6392c.2.1
                                    have p6392_2 := h6392c.2.2.1
                                    have p6392_3 := h6392c.2.2.2
                                    linarith only [h4905, h5, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6309_1, p6392_1]
                                  · have p6392_0 := h6392c.1
                                    have p6392_1 := h6392c.2.1
                                    have p6392_2 := h6392c.2.2.1
                                    have p6392_3 := h6392c.2.2.2
                                    linarith only [hlam, p6392_0]
                                  · have p6392_0 := h6392c.1
                                    have p6392_1 := h6392c.2.1
                                    have p6392_2 := h6392c.2.2.1
                                    have p6392_3 := h6392c.2.2.2
                                    linarith only [h6080, hlam, p6392_1]
                                  · have p6392_0 := h6392c.1
                                    have p6392_1 := h6392c.2.1
                                    have p6392_2 := h6392c.2.2.1
                                    have p6392_3 := h6392c.2.2.2
                                    linarith only [h6, hlam, p6392_0]
                                  · have p6392_0 := h6392c.1
                                    have p6392_1 := h6392c.2.1
                                    have p6392_2 := h6392c.2.2.1
                                    have p6392_3 := h6392c.2.2.2
                                    linarith only [h6069, hlam, p6392_0]
                                  · have p6392_0 := h6392c.1
                                    have p6392_1 := h6392c.2.1
                                    have p6392_2 := h6392c.2.2.1
                                    have p6392_3 := h6392c.2.2.2
                                    linarith only [h0, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6309_1, p6392_1]
                                  · have p6392_0 := h6392c.1
                                    have p6392_1 := h6392c.2.1
                                    have p6392_2 := h6392c.2.2.1
                                    have p6392_3 := h6392c.2.2.2
                                    linarith only [h0, h3, h6069, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p6309_1, p6392_1]
                                  · have p6392_0 := h6392c.1
                                    have p6392_1 := h6392c.2.1
                                    have p6392_2 := h6392c.2.2.1
                                    have p6392_3 := h6392c.2.2.2
                                    linarith only [hlam, p6392_0]
                          · linarith only [h6, h6385, hlam]
                        · linarith only [h3, h6384, hlam]
                      · have p6309_0 := h6309c.1
                        have p6309_1 := h6309c.2.1
                        have p6309_2 := h6309c.2.2.1
                        have p6309_3 := h6309c.2.2.2
                        linarith only [h1, hlam, p6309_1]
                      · have p6309_0 := h6309c.1
                        have p6309_1 := h6309c.2.1
                        have p6309_2 := h6309c.2.2.1
                        have p6309_3 := h6309c.2.2.2
                        linarith only [h4, hlam, p6309_1]
                      · have p6309_0 := h6309c.1
                        have p6309_1 := h6309c.2.1
                        have p6309_2 := h6309c.2.2.1
                        have p6309_3 := h6309c.2.2.2
                        linarith only [hlam, p6309_0]
                      · have p6309_0 := h6309c.1
                        have p6309_1 := h6309c.2.1
                        have p6309_2 := h6309c.2.2.1
                        have p6309_3 := h6309c.2.2.2
                        linarith only [h7, hlam, p6309_1]
                      · have p6309_0 := h6309c.1
                        have p6309_1 := h6309c.2.1
                        have p6309_2 := h6309c.2.2.1
                        have p6309_3 := h6309c.2.2.2
                        linarith only [h4388, hlam, p6309_1]
                      · have p6309_0 := h6309c.1
                        have p6309_1 := h6309c.2.1
                        have p6309_2 := h6309c.2.2.1
                        have p6309_3 := h6309c.2.2.2
                        linarith only [h2, hlam, p6309_0]
                      · have p6309_0 := h6309c.1
                        have p6309_1 := h6309c.2.1
                        have p6309_2 := h6309c.2.2.1
                        have p6309_3 := h6309c.2.2.2
                        linarith only [h5, hlam, p6309_0]
                      · have p6309_0 := h6309c.1
                        have p6309_1 := h6309c.2.1
                        have p6309_2 := h6309c.2.2.1
                        have p6309_3 := h6309c.2.2.2
                        linarith only [h1, h4905, h6067, hc23, hc45, hlam, hphi, ht34, p6309_1]
                      · have p6309_0 := h6309c.1
                        have p6309_1 := h6309c.2.1
                        have p6309_2 := h6309c.2.2.1
                        have p6309_3 := h6309c.2.2.2
                        linarith only [hlam, p6309_0]
                      · have p6309_0 := h6309c.1
                        have p6309_1 := h6309c.2.1
                        have p6309_2 := h6309c.2.2.1
                        have p6309_3 := h6309c.2.2.2
                        linarith only [h4905, hlam, p6309_0]
                      · have p6309_0 := h6309c.1
                        have p6309_1 := h6309c.2.1
                        have p6309_2 := h6309c.2.2.1
                        have p6309_3 := h6309c.2.2.2
                        linarith only [h3, hlam, p6309_0]
                      · have p6309_0 := h6309c.1
                        have p6309_1 := h6309c.2.1
                        have p6309_2 := h6309c.2.2.1
                        have p6309_3 := h6309c.2.2.2
                        linarith only [h6, hlam, p6309_1]
                      · have p6309_0 := h6309c.1
                        have p6309_1 := h6309c.2.1
                        have p6309_2 := h6309c.2.2.1
                        have p6309_3 := h6309c.2.2.2
                        rcases p6309_3 (m.d 0 1) (by simp) with h6532 | h6532
                        · rcases p6309_3 (m.d 0 2) (by simp) with h6533 | h6533
                          · rcases p6309_3 (m.d 0 3) (by simp) with h6534 | h6534
                            · linarith only [h4388, h6534, hlam]
                            · rcases p6309_3 (m.d 0 4) (by simp) with h6536 | h6536
                              · linarith only [h4905, h6536, hlam]
                              · linarith only [h6536, h7, hlam]
                          · linarith only [h4, h6533, hlam]
                        · linarith only [h1, h6532, hlam]
                      · have p6309_0 := h6309c.1
                        have p6309_1 := h6309c.2.1
                        have p6309_2 := h6309c.2.2.1
                        have p6309_3 := h6309c.2.2.2
                        rcases p6309_3 (m.d 0 1) (by simp) with h6541 | h6541
                        · rcases p6309_3 (m.d 0 2) (by simp) with h6542 | h6542
                          · rcases p6309_3 (m.d 0 3) (by simp) with h6543 | h6543
                            · linarith only [h4388, h6543, hlam]
                            · rcases p6309_3 (m.d 0 4) (by simp) with h6545 | h6545
                              · linarith only [h4905, h6545, hlam]
                              · rcases p6309_3 (m.d 0 5) (by simp) with h6547 | h6547
                                · rcases h2bigk with h6548c | h6548c | h6548c | h6548c | h6548c | h6548c | h6548c | h6548c | h6548c | h6548c | h6548c | h6548c | h6548c | h6548c | h6548c | h6548c | h6548c | h6548c | h6548c | h6548c | h6548c | h6548c | h6548c | h6548c | h6548c
                                  · have p6548_0 := h6548c.1
                                    have p6548_1 := h6548c.2.1
                                    have p6548_2 := h6548c.2.2.1
                                    have p6548_3 := h6548c.2.2.2
                                    linarith only [hlam, p6548_0]
                                  · have p6548_0 := h6548c.1
                                    have p6548_1 := h6548c.2.1
                                    have p6548_2 := h6548c.2.2.1
                                    have p6548_3 := h6548c.2.2.2
                                    rcases p6548_3 (m.d 0 2) (by simp) with h6550 | h6550
                                    · rcases p6548_3 (m.d 1 2) (by simp) with h6551 | h6551
                                      · linarith only [h0, h6551, hlam]
                                      · rcases p6548_3 (m.d 2 3) (by simp) with h6553 | h6553
                                        · linarith only [h4, h6553, hlam]
                                        · rcases p6548_3 (m.d 2 4) (by simp) with h6555 | h6555
                                          · linarith only [h5, h6555, hlam]
                                          · rcases p6548_3 (m.d 2 5) (by simp) with h6557 | h6557
                                            · linarith only [h6, h6557, hlam]
                                            · rcases h3bigk with h6559c | h6559c | h6559c | h6559c | h6559c | h6559c | h6559c | h6559c | h6559c | h6559c | h6559c | h6559c | h6559c | h6559c | h6559c | h6559c | h6559c | h6559c | h6559c | h6559c | h6559c | h6559c | h6559c | h6559c | h6559c
                                              · have p6559_0 := h6559c.1
                                                have p6559_1 := h6559c.2.1
                                                have p6559_2 := h6559c.2.2.1
                                                have p6559_3 := h6559c.2.2.2
                                                linarith only [hlam, p6559_0]
                                              · have p6559_0 := h6559c.1
                                                have p6559_1 := h6559c.2.1
                                                have p6559_2 := h6559c.2.2.1
                                                have p6559_3 := h6559c.2.2.2
                                                linarith only [h6067, h6082, h7, hc23, hc45, hlam, hphi, ht34, p6559_1]
                                              · have p6559_0 := h6559c.1
                                                have p6559_1 := h6559c.2.1
                                                have p6559_2 := h6559c.2.2.1
                                                have p6559_3 := h6559c.2.2.2
                                                linarith only [h6082, h7, hc23, hc45, hlam, hphi, ht34, p6559_1]
                                              · have p6559_0 := h6559c.1
                                                have p6559_1 := h6559c.2.1
                                                have p6559_2 := h6559c.2.2.1
                                                have p6559_3 := h6559c.2.2.2
                                                linarith only [h7, hlam, p6559_0]
                                              · have p6559_0 := h6559c.1
                                                have p6559_1 := h6559c.2.1
                                                have p6559_2 := h6559c.2.2.1
                                                have p6559_3 := h6559c.2.2.2
                                                linarith only [h4388, hlam, p6559_0]
                                              · have p6559_0 := h6559c.1
                                                have p6559_1 := h6559c.2.1
                                                have p6559_2 := h6559c.2.2.1
                                                have p6559_3 := h6559c.2.2.2
                                                linarith only [h1, hlam, p6559_0]
                                              · have p6559_0 := h6559c.1
                                                have p6559_1 := h6559c.2.1
                                                have p6559_2 := h6559c.2.2.1
                                                have p6559_3 := h6559c.2.2.2
                                                linarith only [hlam, p6559_0]
                                              · have p6559_0 := h6559c.1
                                                have p6559_1 := h6559c.2.1
                                                have p6559_2 := h6559c.2.2.1
                                                have p6559_3 := h6559c.2.2.2
                                                linarith only [h1, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6559_1]
                                              · have p6559_0 := h6559c.1
                                                have p6559_1 := h6559c.2.1
                                                have p6559_2 := h6559c.2.2.1
                                                have p6559_3 := h6559c.2.2.2
                                                linarith only [h6070, hlam, p6559_0]
                                              · have p6559_0 := h6559c.1
                                                have p6559_1 := h6559c.2.1
                                                have p6559_2 := h6559c.2.2.1
                                                have p6559_3 := h6559c.2.2.2
                                                linarith only [h6072, hlam, p6559_0]
                                              · have p6559_0 := h6559c.1
                                                have p6559_1 := h6559c.2.1
                                                have p6559_2 := h6559c.2.2.1
                                                have p6559_3 := h6559c.2.2.2
                                                linarith only [h4, hlam, p6559_0]
                                              · have p6559_0 := h6559c.1
                                                have p6559_1 := h6559c.2.1
                                                have p6559_2 := h6559c.2.2.1
                                                have p6559_3 := h6559c.2.2.2
                                                linarith only [h6067, hlam, p6559_0]
                                              · have p6559_0 := h6559c.1
                                                have p6559_1 := h6559c.2.1
                                                have p6559_2 := h6559c.2.2.1
                                                have p6559_3 := h6559c.2.2.2
                                                linarith only [hlam, p6559_0]
                                              · have p6559_0 := h6559c.1
                                                have p6559_1 := h6559c.2.1
                                                have p6559_2 := h6559c.2.2.1
                                                have p6559_3 := h6559c.2.2.2
                                                linarith only [h6076, hlam, p6559_0]
                                              · have p6559_0 := h6559c.1
                                                have p6559_1 := h6559c.2.1
                                                have p6559_2 := h6559c.2.2.1
                                                have p6559_3 := h6559c.2.2.2
                                                linarith only [h6078, hlam, p6559_0]
                                              · have p6559_0 := h6559c.1
                                                have p6559_1 := h6559c.2.1
                                                have p6559_2 := h6559c.2.2.1
                                                have p6559_3 := h6559c.2.2.2
                                                linarith only [h6082, hc03, hc45, hlam, hphi, ht34, p6559_1]
                                              · have p6559_0 := h6559c.1
                                                have p6559_1 := h6559c.2.1
                                                have p6559_2 := h6559c.2.2.1
                                                have p6559_3 := h6559c.2.2.2
                                                linarith only [h6067, h6082, hc23, hc45, hlam, hphi, ht34, p6559_1]
                                              · have p6559_0 := h6559c.1
                                                have p6559_1 := h6559c.2.1
                                                have p6559_2 := h6559c.2.2.1
                                                have p6559_3 := h6559c.2.2.2
                                                linarith only [h6082, hc23, hc45, hlam, hphi, ht34, p6559_1]
                                              · have p6559_0 := h6559c.1
                                                have p6559_1 := h6559c.2.1
                                                have p6559_2 := h6559c.2.2.1
                                                have p6559_3 := h6559c.2.2.2
                                                linarith only [hlam, p6559_0]
                                              · have p6559_0 := h6559c.1
                                                have p6559_1 := h6559c.2.1
                                                have p6559_2 := h6559c.2.2.1
                                                have p6559_3 := h6559c.2.2.2
                                                linarith only [h6082, hlam, p6559_1]
                                              · have p6559_0 := h6559c.1
                                                have p6559_1 := h6559c.2.1
                                                have p6559_2 := h6559c.2.2.1
                                                have p6559_3 := h6559c.2.2.2
                                                linarith only [h1, h6067, h6082, hc23, hc45, hlam, hphi, ht34, p6559_1]
                                              · have p6559_0 := h6559c.1
                                                have p6559_1 := h6559c.2.1
                                                have p6559_2 := h6559c.2.2.1
                                                have p6559_3 := h6559c.2.2.2
                                                linarith only [h6067, h6082, hc23, hc45, hlam, hphi, ht34, p6559_1]
                                              · have p6559_0 := h6559c.1
                                                have p6559_1 := h6559c.2.1
                                                have p6559_2 := h6559c.2.2.1
                                                have p6559_3 := h6559c.2.2.2
                                                linarith only [h6082, hc23, hc45, hlam, hphi, ht34, p6559_1]
                                              · have p6559_0 := h6559c.1
                                                have p6559_1 := h6559c.2.1
                                                have p6559_2 := h6559c.2.2.1
                                                have p6559_3 := h6559c.2.2.2
                                                linarith only [h6082, hc34, hc45, hlam, hphi, p6559_1]
                                              · have p6559_0 := h6559c.1
                                                have p6559_1 := h6559c.2.1
                                                have p6559_2 := h6559c.2.2.1
                                                have p6559_3 := h6559c.2.2.2
                                                linarith only [hlam, p6559_0]
                                    · linarith only [h0, h6550, hlam]
                                  · have p6548_0 := h6548c.1
                                    have p6548_1 := h6548c.2.1
                                    have p6548_2 := h6548c.2.2.1
                                    have p6548_3 := h6548c.2.2.2
                                    rcases p6548_3 (m.d 0 2) (by simp) with h6586 | h6586
                                    · rcases p6548_3 (m.d 1 2) (by simp) with h6587 | h6587
                                      · linarith only [h0, h6587, hlam]
                                      · linarith only [h6067, h6587, hlam]
                                    · linarith only [h6586, hlam, p6548_0]
                                  · have p6548_0 := h6548c.1
                                    have p6548_1 := h6548c.2.1
                                    have p6548_2 := h6548c.2.2.1
                                    have p6548_3 := h6548c.2.2.2
                                    rcases p6548_3 (m.d 0 2) (by simp) with h6591 | h6591
                                    · rcases p6548_3 (m.d 1 2) (by simp) with h6592 | h6592
                                      · linarith only [h0, h6592, hlam]
                                      · linarith only [h6068, h6592, hlam]
                                    · linarith only [h6591, hlam, p6548_0]
                                  · have p6548_0 := h6548c.1
                                    have p6548_1 := h6548c.2.1
                                    have p6548_2 := h6548c.2.2.1
                                    have p6548_3 := h6548c.2.2.2
                                    rcases p6548_3 (m.d 0 2) (by simp) with h6596 | h6596
                                    · rcases p6548_3 (m.d 1 2) (by simp) with h6597 | h6597
                                      · linarith only [h0, h6597, hlam]
                                      · linarith only [h6069, h6597, hlam]
                                    · linarith only [h6596, hlam, p6548_0]
                                  · have p6548_0 := h6548c.1
                                    have p6548_1 := h6548c.2.1
                                    have p6548_2 := h6548c.2.2.1
                                    have p6548_3 := h6548c.2.2.2
                                    linarith only [h0, hlam, p6548_0]
                                  · have p6548_0 := h6548c.1
                                    have p6548_1 := h6548c.2.1
                                    have p6548_2 := h6548c.2.2.1
                                    have p6548_3 := h6548c.2.2.2
                                    linarith only [hlam, p6548_0]
                                  · have p6548_0 := h6548c.1
                                    have p6548_1 := h6548c.2.1
                                    have p6548_2 := h6548c.2.2.1
                                    have p6548_3 := h6548c.2.2.2
                                    rcases p6548_3 (m.d 0 2) (by simp) with h6603 | h6603
                                    · rcases p6548_3 (m.d 1 2) (by simp) with h6604 | h6604
                                      · rcases p6548_3 (m.d 2 3) (by simp) with h6605 | h6605
                                        · linarith only [h6605, hlam, p6548_0]
                                        · rcases p6548_3 (m.d 2 4) (by simp) with h6607 | h6607
                                          · linarith only [h6068, h6607, hlam]
                                          · linarith only [h6076, h6607, hlam]
                                      · linarith only [h6604, hlam, p6548_0]
                                    · linarith only [h4, h6603, hlam]
                                  · have p6548_0 := h6548c.1
                                    have p6548_1 := h6548c.2.1
                                    have p6548_2 := h6548c.2.2.1
                                    have p6548_3 := h6548c.2.2.2
                                    rcases p6548_3 (m.d 0 2) (by simp) with h6612 | h6612
                                    · rcases p6548_3 (m.d 1 2) (by simp) with h6613 | h6613
                                      · rcases p6548_3 (m.d 2 3) (by simp) with h6614 | h6614
                                        · linarith only [h6067, h6614, hlam]
                                        · rcases p6548_3 (m.d 2 4) (by simp) with h6616 | h6616
                                          · linarith only [h6616, hlam, p6548_0]
                                          · rcases p6548_3 (m.d 2 5) (by simp) with h6618 | h6618
                                            · linarith only [h6069, h6618, hlam]
                                            · linarith only [h6080, h6618, hlam]
                                      · linarith only [h6613, hlam, p6548_0]
                                    · linarith only [h5, h6612, hlam]
                                  · have p6548_0 := h6548c.1
                                    have p6548_1 := h6548c.2.1
                                    have p6548_2 := h6548c.2.2.1
                                    have p6548_3 := h6548c.2.2.2
                                    rcases p6548_3 (m.d 0 2) (by simp) with h6623 | h6623
                                    · rcases p6548_3 (m.d 1 2) (by simp) with h6624 | h6624
                                      · rcases p6548_3 (m.d 2 3) (by simp) with h6625 | h6625
                                        · linarith only [h6067, h6625, hlam]
                                        · rcases p6548_3 (m.d 2 4) (by simp) with h6627 | h6627
                                          · linarith only [h6068, h6627, hlam]
                                          · rcases p6548_3 (m.d 2 5) (by simp) with h6629 | h6629
                                            · linarith only [h6629, hlam, p6548_0]
                                            · rcases h3bigk with h6631c | h6631c | h6631c | h6631c | h6631c | h6631c | h6631c | h6631c | h6631c | h6631c | h6631c | h6631c | h6631c | h6631c | h6631c | h6631c | h6631c | h6631c | h6631c | h6631c | h6631c | h6631c | h6631c | h6631c | h6631c
                                              · have p6631_0 := h6631c.1
                                                have p6631_1 := h6631c.2.1
                                                have p6631_2 := h6631c.2.2.1
                                                have p6631_3 := h6631c.2.2.2
                                                linarith only [hlam, p6631_0]
                                              · have p6631_0 := h6631c.1
                                                have p6631_1 := h6631c.2.1
                                                have p6631_2 := h6631c.2.2.1
                                                have p6631_3 := h6631c.2.2.2
                                                linarith only [h6067, h7, hc23, hc34, hlam, hphi, p6631_1]
                                              · have p6631_0 := h6631c.1
                                                have p6631_1 := h6631c.2.1
                                                have p6631_2 := h6631c.2.2.1
                                                have p6631_3 := h6631c.2.2.2
                                                linarith only [h7, hc23, hc34, hlam, hphi, p6631_1]
                                              · have p6631_0 := h6631c.1
                                                have p6631_1 := h6631c.2.1
                                                have p6631_2 := h6631c.2.2.1
                                                have p6631_3 := h6631c.2.2.2
                                                linarith only [h7, hlam, p6631_0]
                                              · have p6631_0 := h6631c.1
                                                have p6631_1 := h6631c.2.1
                                                have p6631_2 := h6631c.2.2.1
                                                have p6631_3 := h6631c.2.2.2
                                                linarith only [h4388, hlam, p6631_0]
                                              · have p6631_0 := h6631c.1
                                                have p6631_1 := h6631c.2.1
                                                have p6631_2 := h6631c.2.2.1
                                                have p6631_3 := h6631c.2.2.2
                                                linarith only [h1, hlam, p6631_0]
                                              · have p6631_0 := h6631c.1
                                                have p6631_1 := h6631c.2.1
                                                have p6631_2 := h6631c.2.2.1
                                                have p6631_3 := h6631c.2.2.2
                                                linarith only [hlam, p6631_0]
                                              · have p6631_0 := h6631c.1
                                                have p6631_1 := h6631c.2.1
                                                have p6631_2 := h6631c.2.2.1
                                                have p6631_3 := h6631c.2.2.2
                                                linarith only [h1, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6631_1]
                                              · have p6631_0 := h6631c.1
                                                have p6631_1 := h6631c.2.1
                                                have p6631_2 := h6631c.2.2.1
                                                have p6631_3 := h6631c.2.2.2
                                                linarith only [h6070, hlam, p6631_0]
                                              · have p6631_0 := h6631c.1
                                                have p6631_1 := h6631c.2.1
                                                have p6631_2 := h6631c.2.2.1
                                                have p6631_3 := h6631c.2.2.2
                                                linarith only [h6072, hlam, p6631_0]
                                              · have p6631_0 := h6631c.1
                                                have p6631_1 := h6631c.2.1
                                                have p6631_2 := h6631c.2.2.1
                                                have p6631_3 := h6631c.2.2.2
                                                linarith only [h4, hlam, p6631_0]
                                              · have p6631_0 := h6631c.1
                                                have p6631_1 := h6631c.2.1
                                                have p6631_2 := h6631c.2.2.1
                                                have p6631_3 := h6631c.2.2.2
                                                linarith only [h6067, hlam, p6631_0]
                                              · have p6631_0 := h6631c.1
                                                have p6631_1 := h6631c.2.1
                                                have p6631_2 := h6631c.2.2.1
                                                have p6631_3 := h6631c.2.2.2
                                                linarith only [hlam, p6631_0]
                                              · have p6631_0 := h6631c.1
                                                have p6631_1 := h6631c.2.1
                                                have p6631_2 := h6631c.2.2.1
                                                have p6631_3 := h6631c.2.2.2
                                                linarith only [h6076, hlam, p6631_0]
                                              · have p6631_0 := h6631c.1
                                                have p6631_1 := h6631c.2.1
                                                have p6631_2 := h6631c.2.2.1
                                                have p6631_3 := h6631c.2.2.2
                                                linarith only [h6078, hlam, p6631_0]
                                              · have p6631_0 := h6631c.1
                                                have p6631_1 := h6631c.2.1
                                                have p6631_2 := h6631c.2.2.1
                                                have p6631_3 := h6631c.2.2.2
                                                linarith only [hc03, hc34, hlam, hphi, p6631_1]
                                              · have p6631_0 := h6631c.1
                                                have p6631_1 := h6631c.2.1
                                                have p6631_2 := h6631c.2.2.1
                                                have p6631_3 := h6631c.2.2.2
                                                linarith only [h6067, hc23, hc34, hlam, hphi, p6631_1]
                                              · have p6631_0 := h6631c.1
                                                have p6631_1 := h6631c.2.1
                                                have p6631_2 := h6631c.2.2.1
                                                have p6631_3 := h6631c.2.2.2
                                                linarith only [hc23, hc34, hlam, hphi, p6631_1]
                                              · have p6631_0 := h6631c.1
                                                have p6631_1 := h6631c.2.1
                                                have p6631_2 := h6631c.2.2.1
                                                have p6631_3 := h6631c.2.2.2
                                                linarith only [hlam, p6631_0]
                                              · have p6631_0 := h6631c.1
                                                have p6631_1 := h6631c.2.1
                                                have p6631_2 := h6631c.2.2.1
                                                have p6631_3 := h6631c.2.2.2
                                                linarith only [h6082, hlam, p6631_1]
                                              · have p6631_0 := h6631c.1
                                                have p6631_1 := h6631c.2.1
                                                have p6631_2 := h6631c.2.2.1
                                                have p6631_3 := h6631c.2.2.2
                                                linarith only [h1, h6067, h6082, hc23, hc45, hlam, hphi, ht34, p6631_1]
                                              · have p6631_0 := h6631c.1
                                                have p6631_1 := h6631c.2.1
                                                have p6631_2 := h6631c.2.2.1
                                                have p6631_3 := h6631c.2.2.2
                                                linarith only [h6067, h6082, hc23, hc45, hlam, hphi, ht34, p6631_1]
                                              · have p6631_0 := h6631c.1
                                                have p6631_1 := h6631c.2.1
                                                have p6631_2 := h6631c.2.2.1
                                                have p6631_3 := h6631c.2.2.2
                                                linarith only [h6082, hc23, hc45, hlam, hphi, ht34, p6631_1]
                                              · have p6631_0 := h6631c.1
                                                have p6631_1 := h6631c.2.1
                                                have p6631_2 := h6631c.2.2.1
                                                have p6631_3 := h6631c.2.2.2
                                                linarith only [h6082, hc34, hc45, hlam, hphi, p6631_1]
                                              · have p6631_0 := h6631c.1
                                                have p6631_1 := h6631c.2.1
                                                have p6631_2 := h6631c.2.2.1
                                                have p6631_3 := h6631c.2.2.2
                                                linarith only [hlam, p6631_0]
                                      · linarith only [h6624, hlam, p6548_0]
                                    · linarith only [h6, h6623, hlam]
                                  · have p6548_0 := h6548c.1
                                    have p6548_1 := h6548c.2.1
                                    have p6548_2 := h6548c.2.2.1
                                    have p6548_3 := h6548c.2.2.2
                                    linarith only [h4, hlam, p6548_0]
                                  · have p6548_0 := h6548c.1
                                    have p6548_1 := h6548c.2.1
                                    have p6548_2 := h6548c.2.2.1
                                    have p6548_3 := h6548c.2.2.2
                                    linarith only [h6067, hlam, p6548_0]
                                  · have p6548_0 := h6548c.1
                                    have p6548_1 := h6548c.2.1
                                    have p6548_2 := h6548c.2.2.1
                                    have p6548_3 := h6548c.2.2.2
                                    linarith only [hlam, p6548_0]
                                  · have p6548_0 := h6548c.1
                                    have p6548_1 := h6548c.2.1
                                    have p6548_2 := h6548c.2.2.1
                                    have p6548_3 := h6548c.2.2.2
                                    linarith only [h6076, hlam, p6548_0]
                                  · have p6548_0 := h6548c.1
                                    have p6548_1 := h6548c.2.1
                                    have p6548_2 := h6548c.2.2.1
                                    have p6548_3 := h6548c.2.2.2
                                    linarith only [h6078, hlam, p6548_0]
                                  · have p6548_0 := h6548c.1
                                    have p6548_1 := h6548c.2.1
                                    have p6548_2 := h6548c.2.2.1
                                    have p6548_3 := h6548c.2.2.2
                                    linarith only [h5, hlam, p6548_0]
                                  · have p6548_0 := h6548c.1
                                    have p6548_1 := h6548c.2.1
                                    have p6548_2 := h6548c.2.2.1
                                    have p6548_3 := h6548c.2.2.2
                                    linarith only [h6068, hlam, p6548_0]
                                  · have p6548_0 := h6548c.1
                                    have p6548_1 := h6548c.2.1
                                    have p6548_2 := h6548c.2.2.1
                                    have p6548_3 := h6548c.2.2.2
                                    linarith only [h4388, h5, h6082, hc23, hc45, hlam, hphi, ht34, p6309_1, p6548_1]
                                  · have p6548_0 := h6548c.1
                                    have p6548_1 := h6548c.2.1
                                    have p6548_2 := h6548c.2.2.1
                                    have p6548_3 := h6548c.2.2.2
                                    linarith only [hlam, p6548_0]
                                  · have p6548_0 := h6548c.1
                                    have p6548_1 := h6548c.2.1
                                    have p6548_2 := h6548c.2.2.1
                                    have p6548_3 := h6548c.2.2.2
                                    linarith only [h6080, hlam, p6548_1]
                                  · have p6548_0 := h6548c.1
                                    have p6548_1 := h6548c.2.1
                                    have p6548_2 := h6548c.2.2.1
                                    have p6548_3 := h6548c.2.2.2
                                    linarith only [h6, hlam, p6548_0]
                                  · have p6548_0 := h6548c.1
                                    have p6548_1 := h6548c.2.1
                                    have p6548_2 := h6548c.2.2.1
                                    have p6548_3 := h6548c.2.2.2
                                    linarith only [h6069, hlam, p6548_0]
                                  · have p6548_0 := h6548c.1
                                    have p6548_1 := h6548c.2.1
                                    have p6548_2 := h6548c.2.2.1
                                    have p6548_3 := h6548c.2.2.2
                                    linarith only [h0, h6069, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6548_1]
                                  · have p6548_0 := h6548c.1
                                    have p6548_1 := h6548c.2.1
                                    have p6548_2 := h6548c.2.2.1
                                    have p6548_3 := h6548c.2.2.2
                                    linarith only [h0, h6069, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p6548_1]
                                  · have p6548_0 := h6548c.1
                                    have p6548_1 := h6548c.2.1
                                    have p6548_2 := h6548c.2.2.1
                                    have p6548_3 := h6548c.2.2.2
                                    linarith only [hlam, p6548_0]
                                · linarith only [h4905, h6547, hlam]
                          · linarith only [h5, h6542, hlam]
                        · linarith only [h2, h6541, hlam]
                      · have p6309_0 := h6309c.1
                        have p6309_1 := h6309c.2.1
                        have p6309_2 := h6309c.2.2.1
                        have p6309_3 := h6309c.2.2.2
                        linarith only [hlam, p6309_0]
      · rcases m.htr 1 3 4 (by decide) (by decide) with h6678 | h6678
        · linarith only [h1, h6678, h7, hlam]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h6680 | h6680
          · linarith only [h1, h4388, h6, h6069, h6680, h7, hc12, hc34, hlam, hphi, ht23]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h6682 | h6682
            · linarith only [h2, h4905, h6682, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h6684 | h6684
              · linarith only [h1, h6067, h6684, h7, hlam]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h6686 | h6686
                · linarith only [h1, h4388, h6067, h6686, hlam]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h6688 | h6688
                  · linarith only [h0, h4905, h6, h6068, h6069, h6688, hc01, hc05, hlam, hphi, ht0b, ht5b]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h6690 | h6690
                    · linarith only [h4905, h6, h6068, h6069, h6684, h6690, hc23, hc34, hlam, hphi]
                    · rcases h0bigk with h6692c | h6692c | h6692c | h6692c | h6692c | h6692c | h6692c | h6692c | h6692c | h6692c | h6692c | h6692c | h6692c | h6692c | h6692c | h6692c | h6692c | h6692c | h6692c | h6692c | h6692c | h6692c | h6692c | h6692c | h6692c
                      · have p6692_0 := h6692c.1
                        have p6692_1 := h6692c.2.1
                        have p6692_2 := h6692c.2.2.1
                        have p6692_3 := h6692c.2.2.2
                        linarith only [hlam, p6692_0]
                      · have p6692_0 := h6692c.1
                        have p6692_1 := h6692c.2.1
                        have p6692_2 := h6692c.2.2.1
                        have p6692_3 := h6692c.2.2.2
                        linarith only [h6, h6068, h6069, h6684, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6692_1]
                      · have p6692_0 := h6692c.1
                        have p6692_1 := h6692c.2.1
                        have p6692_2 := h6692c.2.2.1
                        have p6692_3 := h6692c.2.2.2
                        rcases p6692_3 (m.d 0 1) (by simp) with h6695 | h6695
                        · rcases p6692_3 (m.d 0 2) (by simp) with h6696 | h6696
                          · linarith only [h0, h6696, hlam]
                          · linarith only [h4, h6696, hlam]
                        · linarith only [h1, h6695, hlam]
                      · have p6692_0 := h6692c.1
                        have p6692_1 := h6692c.2.1
                        have p6692_2 := h6692c.2.2.1
                        have p6692_3 := h6692c.2.2.2
                        rcases p6692_3 (m.d 0 1) (by simp) with h6700 | h6700
                        · rcases p6692_3 (m.d 0 2) (by simp) with h6701 | h6701
                          · linarith only [h0, h6701, hlam]
                          · linarith only [h5, h6701, hlam]
                        · linarith only [h2, h6700, hlam]
                      · have p6692_0 := h6692c.1
                        have p6692_1 := h6692c.2.1
                        have p6692_2 := h6692c.2.2.1
                        have p6692_3 := h6692c.2.2.2
                        linarith only [h6, h6068, h6069, h6684, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6692_1]
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
                        rcases p6692_3 (m.d 0 1) (by simp) with h6708 | h6708
                        · rcases p6692_3 (m.d 0 2) (by simp) with h6709 | h6709
                          · rcases p6692_3 (m.d 0 3) (by simp) with h6710 | h6710
                            · linarith only [h4, h6710, hlam]
                            · rcases p6692_3 (m.d 0 4) (by simp) with h6712 | h6712
                              · linarith only [h5, h6712, hlam]
                              · linarith only [h6712, h7, hlam]
                          · linarith only [h4, h6709, hlam]
                        · linarith only [h1, h6708, hlam]
                      · have p6692_0 := h6692c.1
                        have p6692_1 := h6692c.2.1
                        have p6692_2 := h6692c.2.2.1
                        have p6692_3 := h6692c.2.2.2
                        rcases p6692_3 (m.d 0 1) (by simp) with h6717 | h6717
                        · rcases p6692_3 (m.d 0 2) (by simp) with h6718 | h6718
                          · rcases p6692_3 (m.d 0 3) (by simp) with h6719 | h6719
                            · linarith only [h4, h6719, hlam]
                            · rcases p6692_3 (m.d 0 4) (by simp) with h6721 | h6721
                              · linarith only [h5, h6721, hlam]
                              · rcases p6692_3 (m.d 0 5) (by simp) with h6723 | h6723
                                · linarith only [h6, h6723, hlam]
                                · linarith only [h4905, h6723, hlam]
                          · linarith only [h5, h6718, hlam]
                        · linarith only [h2, h6717, hlam]
                      · have p6692_0 := h6692c.1
                        have p6692_1 := h6692c.2.1
                        have p6692_2 := h6692c.2.2.1
                        have p6692_3 := h6692c.2.2.2
                        linarith only [h6, h6068, h6069, h6684, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6692_1]
                      · have p6692_0 := h6692c.1
                        have p6692_1 := h6692c.2.1
                        have p6692_2 := h6692c.2.2.1
                        have p6692_3 := h6692c.2.2.2
                        linarith only [h1, hlam, p6692_1]
                      · have p6692_0 := h6692c.1
                        have p6692_1 := h6692c.2.1
                        have p6692_2 := h6692c.2.2.1
                        have p6692_3 := h6692c.2.2.2
                        linarith only [h4, hlam, p6692_1]
                      · have p6692_0 := h6692c.1
                        have p6692_1 := h6692c.2.1
                        have p6692_2 := h6692c.2.2.1
                        have p6692_3 := h6692c.2.2.2
                        linarith only [hlam, p6692_0]
                      · have p6692_0 := h6692c.1
                        have p6692_1 := h6692c.2.1
                        have p6692_2 := h6692c.2.2.1
                        have p6692_3 := h6692c.2.2.2
                        linarith only [h7, hlam, p6692_1]
                      · have p6692_0 := h6692c.1
                        have p6692_1 := h6692c.2.1
                        have p6692_2 := h6692c.2.2.1
                        have p6692_3 := h6692c.2.2.2
                        linarith only [h4388, hlam, p6692_1]
                      · have p6692_0 := h6692c.1
                        have p6692_1 := h6692c.2.1
                        have p6692_2 := h6692c.2.2.1
                        have p6692_3 := h6692c.2.2.2
                        linarith only [h2, hlam, p6692_0]
                      · have p6692_0 := h6692c.1
                        have p6692_1 := h6692c.2.1
                        have p6692_2 := h6692c.2.2.1
                        have p6692_3 := h6692c.2.2.2
                        linarith only [h5, hlam, p6692_0]
                      · have p6692_0 := h6692c.1
                        have p6692_1 := h6692c.2.1
                        have p6692_2 := h6692c.2.2.1
                        have p6692_3 := h6692c.2.2.2
                        linarith only [h6690, h7, hc03, hc45, hlam, hphi, ht34, p6692_1]
                      · have p6692_0 := h6692c.1
                        have p6692_1 := h6692c.2.1
                        have p6692_2 := h6692c.2.2.1
                        have p6692_3 := h6692c.2.2.2
                        linarith only [hlam, p6692_0]
                      · have p6692_0 := h6692c.1
                        have p6692_1 := h6692c.2.1
                        have p6692_2 := h6692c.2.2.1
                        have p6692_3 := h6692c.2.2.2
                        linarith only [h4905, hlam, p6692_0]
                      · have p6692_0 := h6692c.1
                        have p6692_1 := h6692c.2.1
                        have p6692_2 := h6692c.2.2.1
                        have p6692_3 := h6692c.2.2.2
                        linarith only [h3, hlam, p6692_0]
                      · have p6692_0 := h6692c.1
                        have p6692_1 := h6692c.2.1
                        have p6692_2 := h6692c.2.2.1
                        have p6692_3 := h6692c.2.2.2
                        linarith only [h6, hlam, p6692_1]
                      · have p6692_0 := h6692c.1
                        have p6692_1 := h6692c.2.1
                        have p6692_2 := h6692c.2.2.1
                        have p6692_3 := h6692c.2.2.2
                        rcases p6692_3 (m.d 0 1) (by simp) with h6741 | h6741
                        · rcases p6692_3 (m.d 0 2) (by simp) with h6742 | h6742
                          · rcases p6692_3 (m.d 0 3) (by simp) with h6743 | h6743
                            · linarith only [h4388, h6743, hlam]
                            · rcases p6692_3 (m.d 0 4) (by simp) with h6745 | h6745
                              · linarith only [h4905, h6745, hlam]
                              · linarith only [h6745, h7, hlam]
                          · linarith only [h4, h6742, hlam]
                        · linarith only [h1, h6741, hlam]
                      · have p6692_0 := h6692c.1
                        have p6692_1 := h6692c.2.1
                        have p6692_2 := h6692c.2.2.1
                        have p6692_3 := h6692c.2.2.2
                        rcases p6692_3 (m.d 0 1) (by simp) with h6750 | h6750
                        · rcases p6692_3 (m.d 0 2) (by simp) with h6751 | h6751
                          · rcases p6692_3 (m.d 0 3) (by simp) with h6752 | h6752
                            · linarith only [h4388, h6752, hlam]
                            · rcases p6692_3 (m.d 0 4) (by simp) with h6754 | h6754
                              · linarith only [h4905, h6754, hlam]
                              · rcases p6692_3 (m.d 0 5) (by simp) with h6756 | h6756
                                · rcases h2bigk with h6757c | h6757c | h6757c | h6757c | h6757c | h6757c | h6757c | h6757c | h6757c | h6757c | h6757c | h6757c | h6757c | h6757c | h6757c | h6757c | h6757c | h6757c | h6757c | h6757c | h6757c | h6757c | h6757c | h6757c | h6757c
                                  · have p6757_0 := h6757c.1
                                    have p6757_1 := h6757c.2.1
                                    have p6757_2 := h6757c.2.2.1
                                    have p6757_3 := h6757c.2.2.2
                                    linarith only [hlam, p6757_0]
                                  · have p6757_0 := h6757c.1
                                    have p6757_1 := h6757c.2.1
                                    have p6757_2 := h6757c.2.2.1
                                    have p6757_3 := h6757c.2.2.2
                                    rcases p6757_3 (m.d 0 2) (by simp) with h6759 | h6759
                                    · rcases p6757_3 (m.d 1 2) (by simp) with h6760 | h6760
                                      · linarith only [h0, h6760, hlam]
                                      · rcases p6757_3 (m.d 2 3) (by simp) with h6762 | h6762
                                        · linarith only [h4, h6762, hlam]
                                        · rcases p6757_3 (m.d 2 4) (by simp) with h6764 | h6764
                                          · linarith only [h5, h6764, hlam]
                                          · rcases p6757_3 (m.d 2 5) (by simp) with h6766 | h6766
                                            · linarith only [h6, h6766, hlam]
                                            · linarith only [h6069, h6766, hlam]
                                    · linarith only [h0, h6759, hlam]
                                  · have p6757_0 := h6757c.1
                                    have p6757_1 := h6757c.2.1
                                    have p6757_2 := h6757c.2.2.1
                                    have p6757_3 := h6757c.2.2.2
                                    linarith only [h6, h6068, h6069, h6684, hlam, p6757_2]
                                  · have p6757_0 := h6757c.1
                                    have p6757_1 := h6757c.2.1
                                    have p6757_2 := h6757c.2.2.1
                                    have p6757_3 := h6757c.2.2.2
                                    linarith only [h6, h6068, h6069, hlam, p6757_2]
                                  · have p6757_0 := h6757c.1
                                    have p6757_1 := h6757c.2.1
                                    have p6757_2 := h6757c.2.2.1
                                    have p6757_3 := h6757c.2.2.2
                                    linarith only [h6068, h6069, h6684, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6757_1]
                                  · have p6757_0 := h6757c.1
                                    have p6757_1 := h6757c.2.1
                                    have p6757_2 := h6757c.2.2.1
                                    have p6757_3 := h6757c.2.2.2
                                    linarith only [h0, hlam, p6757_0]
                                  · have p6757_0 := h6757c.1
                                    have p6757_1 := h6757c.2.1
                                    have p6757_2 := h6757c.2.2.1
                                    have p6757_3 := h6757c.2.2.2
                                    linarith only [hlam, p6757_0]
                                  · have p6757_0 := h6757c.1
                                    have p6757_1 := h6757c.2.1
                                    have p6757_2 := h6757c.2.2.1
                                    have p6757_3 := h6757c.2.2.2
                                    linarith only [h0, h6, h6069, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6757_1]
                                  · have p6757_0 := h6757c.1
                                    have p6757_1 := h6757c.2.1
                                    have p6757_2 := h6757c.2.2.1
                                    have p6757_3 := h6757c.2.2.2
                                    linarith only [h4388, h6, h6069, h6684, hc23, hc35, hlam, hphi, p6757_1]
                                  · have p6757_0 := h6757c.1
                                    have p6757_1 := h6757c.2.1
                                    have p6757_2 := h6757c.2.2.1
                                    have p6757_3 := h6757c.2.2.2
                                    linarith only [h6069, hlam, p6757_0]
                                  · have p6757_0 := h6757c.1
                                    have p6757_1 := h6757c.2.1
                                    have p6757_2 := h6757c.2.2.1
                                    have p6757_3 := h6757c.2.2.2
                                    linarith only [h4, hlam, p6757_0]
                                  · have p6757_0 := h6757c.1
                                    have p6757_1 := h6757c.2.1
                                    have p6757_2 := h6757c.2.2.1
                                    have p6757_3 := h6757c.2.2.2
                                    linarith only [h6067, hlam, p6757_0]
                                  · have p6757_0 := h6757c.1
                                    have p6757_1 := h6757c.2.1
                                    have p6757_2 := h6757c.2.2.1
                                    have p6757_3 := h6757c.2.2.2
                                    linarith only [hlam, p6757_0]
                                  · have p6757_0 := h6757c.1
                                    have p6757_1 := h6757c.2.1
                                    have p6757_2 := h6757c.2.2.1
                                    have p6757_3 := h6757c.2.2.2
                                    linarith only [h6684, hlam, p6757_0]
                                  · have p6757_0 := h6757c.1
                                    have p6757_1 := h6757c.2.1
                                    have p6757_2 := h6757c.2.2.1
                                    have p6757_3 := h6757c.2.2.2
                                    linarith only [h6686, hlam, p6757_0]
                                  · have p6757_0 := h6757c.1
                                    have p6757_1 := h6757c.2.1
                                    have p6757_2 := h6757c.2.2.1
                                    have p6757_3 := h6757c.2.2.2
                                    linarith only [h5, hlam, p6757_0]
                                  · have p6757_0 := h6757c.1
                                    have p6757_1 := h6757c.2.1
                                    have p6757_2 := h6757c.2.2.1
                                    have p6757_3 := h6757c.2.2.2
                                    linarith only [h6068, hlam, p6757_0]
                                  · have p6757_0 := h6757c.1
                                    have p6757_1 := h6757c.2.1
                                    have p6757_2 := h6757c.2.2.1
                                    have p6757_3 := h6757c.2.2.2
                                    linarith only [h5, h6690, h7, hc23, hc45, hlam, hphi, ht34, p6757_1]
                                  · have p6757_0 := h6757c.1
                                    have p6757_1 := h6757c.2.1
                                    have p6757_2 := h6757c.2.2.1
                                    have p6757_3 := h6757c.2.2.2
                                    linarith only [hlam, p6757_0]
                                  · have p6757_0 := h6757c.1
                                    have p6757_1 := h6757c.2.1
                                    have p6757_2 := h6757c.2.2.1
                                    have p6757_3 := h6757c.2.2.2
                                    linarith only [h6688, hlam, p6757_1]
                                  · have p6757_0 := h6757c.1
                                    have p6757_1 := h6757c.2.1
                                    have p6757_2 := h6757c.2.2.1
                                    have p6757_3 := h6757c.2.2.2
                                    linarith only [h6, hlam, p6757_0]
                                  · have p6757_0 := h6757c.1
                                    have p6757_1 := h6757c.2.1
                                    have p6757_2 := h6757c.2.2.1
                                    have p6757_3 := h6757c.2.2.2
                                    linarith only [h0, h6, h6067, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6757_1]
                                  · have p6757_0 := h6757c.1
                                    have p6757_1 := h6757c.2.1
                                    have p6757_2 := h6757c.2.2.1
                                    have p6757_3 := h6757c.2.2.2
                                    rcases p6757_3 (m.d 0 2) (by simp) with h6790 | h6790
                                    · rcases p6757_3 (m.d 1 2) (by simp) with h6791 | h6791
                                      · linarith only [h6069, h6791, hlam]
                                      · linarith only [h6067, h6791, hlam]
                                    · linarith only [h4, h6790, hlam]
                                  · have p6757_0 := h6757c.1
                                    have p6757_1 := h6757c.2.1
                                    have p6757_2 := h6757c.2.2.1
                                    have p6757_3 := h6757c.2.2.2
                                    rcases p6757_3 (m.d 0 2) (by simp) with h6795 | h6795
                                    · rcases p6757_3 (m.d 1 2) (by simp) with h6796 | h6796
                                      · linarith only [h6069, h6796, hlam]
                                      · linarith only [h6068, h6796, hlam]
                                    · linarith only [h5, h6795, hlam]
                                  · have p6757_0 := h6757c.1
                                    have p6757_1 := h6757c.2.1
                                    have p6757_2 := h6757c.2.2.1
                                    have p6757_3 := h6757c.2.2.2
                                    linarith only [hlam, p6757_0]
                                · linarith only [h4905, h6756, hlam]
                          · linarith only [h5, h6751, hlam]
                        · linarith only [h2, h6750, hlam]
                      · have p6692_0 := h6692c.1
                        have p6692_1 := h6692c.2.1
                        have p6692_2 := h6692c.2.2.1
                        have p6692_3 := h6692c.2.2.2
                        linarith only [hlam, p6692_0]
    · linarith only [h4905, h5, h6067, h6068, hc23, hc45, hlam, hphi, ht34]
  · rcases m.htr 1 2 4 (by decide) (by decide) with h6806 | h6806
    · linarith only [h4, h4905, h6067, h6806, h7, hc24, hc45, hlam, hphi]
    · rcases m.htr 1 2 5 (by decide) (by decide) with h6808 | h6808
      · rcases m.htr 1 3 4 (by decide) (by decide) with h6809 | h6809
        · linarith only [h4, h6067, h6808, h6809, h7, hc13, hc25, hlam, hphi, ht01, ht0b, ht5b]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h6811 | h6811
          · linarith only [h4, h4388, h6067, h6811, hlam]
          · linarith only [h6067, h6808, h6811, hlam]
      · rcases m.htr 1 3 4 (by decide) (by decide) with h6814 | h6814
        · linarith only [h1, h4, h6067, h6814, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h6816 | h6816
          · linarith only [h4, h4388, h6067, h6816, hlam]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h6818 | h6818
            · linarith only [h4905, h5, h6806, h6818, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h6820 | h6820
              · linarith only [h4, h6820, h7, hlam]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h6822 | h6822
                · linarith only [h4, h4388, h6822, hlam]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h6824 | h6824
                  · linarith only [h4905, h5, h6824, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h6826 | h6826
                    · linarith only [h4, h4905, h6067, h6826, h7, hc12, hc34, hlam, hphi, ht23]
                    · linarith only [h4, h6067, h6826, h7, hc12, hc45, hlam, hphi, ht23, ht34]

set_option maxHeartbeats 13644000 in
set_option maxHeartbeats 13644000 in
theorem r1l7_10_12_23_L_I_L_I_H_I_s6_x1_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h7 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h4388 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  rcases m.htr 0 4 5 (by decide) (by decide) with h4905 | h4905
  · exact r1l7_10_12_23_L_I_L_I_H_I_s6_x1_x1_x0 m hb0 hb2 hb3 hg0 hg1 hg2 hg3 hg4 hg5 hg6 h7 h4388 h4905
  · exact r1l7_10_12_23_L_I_L_I_H_I_s6_x1_x1_x1 m hb0 hb2 hb3 hg0 hg1 hg2 hg3 hg4 hg5 hg6 h7 h4388 h4905

end R2N4
