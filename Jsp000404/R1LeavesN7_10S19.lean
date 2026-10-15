import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_10S18

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6982000 in
set_option maxHeartbeats 6982000 in
theorem r1l7_12_24_L_I_H_I_s9 (m : N7Model)
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6874 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg8886 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg8887 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
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
  have h8886 := hg8886
  have h8887 := hg8887
  rcases m.htr 0 2 5 (by decide) (by decide) with h8888 | h8888
  · exact r1l7_12_24_L_I_H_I_s10 m hb2 hb4 h0 h6874 h8886 h8887 h8888
  · rcases m.htr 0 3 4 (by decide) (by decide) with h12140 | h12140
    · rcases m.htr 0 4 5 (by decide) (by decide) with h12141 | h12141
      · linarith only [h12141, h8887, h8888, hlam]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h12143 | h12143
        · rcases m.htr 1 2 4 (by decide) (by decide) with h12144 | h12144
          · rcases m.htr 1 2 5 (by decide) (by decide) with h12145 | h12145
            · rcases m.htr 1 3 4 (by decide) (by decide) with h12146 | h12146
              · rcases m.htr 1 4 5 (by decide) (by decide) with h12147 | h12147
                · rcases m.htr 2 3 4 (by decide) (by decide) with h12148 | h12148
                  · linarith only [h12145, h12148, h8886, h8888, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                  · linarith only [h12140, h12145, h12148, h8886, h8888, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h12151 | h12151
                  · linarith only [h12145, h12151, h8886, h8888, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                  · linarith only [h12140, h12145, h12151, h8886, h8888, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
              · linarith only [h12140, h12145, h12146, h8886, h8888, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h12155 | h12155
              · rcases m.htr 1 4 5 (by decide) (by decide) with h12156 | h12156
                · linarith only [h12141, h12143, h12145, h12155, h12156, h6874, hc01, hc25, hlam, hphi, ht12]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h12158 | h12158
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h12159 | h12159
                    · linarith only [h0, h12145, h12159, h8886, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h12161 | h12161
                      · linarith only [h12141, h12161, h8887, hlam]
                      · linarith only [h0, h12145, h12158, h12161, h8886, hc34, hc45, hlam, hphi]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h12164 | h12164
                    · linarith only [h0, h12140, h12145, h12158, h12164, h8886, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                    · linarith only [h0, h12140, h12145, h12158, h12164, h8886, hc23, hc35, hlam, hphi]
              · linarith only [h0, h12140, h12145, h12155, h6874, h8886, hc01, hc25, hlam, hphi, ht12]
          · linarith only [h0, h12144, h8887, hlam]
        · linarith only [h0, h12143, h8886, hlam]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h12170 | h12170
      · linarith only [h12170, h8887, h8888, hlam]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h12172 | h12172
        · rcases m.htr 1 2 4 (by decide) (by decide) with h12173 | h12173
          · rcases m.htr 1 2 5 (by decide) (by decide) with h12174 | h12174
            · rcases m.htr 1 3 4 (by decide) (by decide) with h12175 | h12175
              · rcases m.htr 1 4 5 (by decide) (by decide) with h12176 | h12176
                · rcases m.htr 2 3 4 (by decide) (by decide) with h12177 | h12177
                  · linarith only [h12140, h12177, h8886, h8888, hc03, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h12179 | h12179
                    · linarith only [h12174, h12179, h8886, h8888, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h12181 | h12181
                      · linarith only [h12170, h12174, h12181, h8887, h8888, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h12183 | h12183
                        · linarith only [h12181, h12183, h8886, h8888, hc23, hc34, hlam, hphi]
                        · rcases h2bigk with h12185c | h12185c | h12185c | h12185c | h12185c | h12185c | h12185c | h12185c | h12185c | h12185c | h12185c | h12185c | h12185c | h12185c | h12185c | h12185c | h12185c | h12185c | h12185c | h12185c | h12185c | h12185c | h12185c | h12185c | h12185c
                          · have p12185_0 := h12185c.1
                            have p12185_1 := h12185c.2.1
                            have p12185_2 := h12185c.2.2.1
                            have p12185_3 := h12185c.2.2.2
                            linarith only [hlam, p12185_0]
                          · have p12185_0 := h12185c.1
                            have p12185_1 := h12185c.2.1
                            have p12185_2 := h12185c.2.2.1
                            have p12185_3 := h12185c.2.2.2
                            linarith only [h0, hlam, p12185_0]
                          · have p12185_0 := h12185c.1
                            have p12185_1 := h12185c.2.1
                            have p12185_2 := h12185c.2.2.1
                            have p12185_3 := h12185c.2.2.2
                            linarith only [h12172, h12175, h12176, h12179, h12183, h8888, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p12185_1]
                          · have p12185_0 := h12185c.1
                            have p12185_1 := h12185c.2.1
                            have p12185_2 := h12185c.2.2.1
                            have p12185_3 := h12185c.2.2.2
                            linarith only [h12172, h12175, h12176, h12179, h12183, h8888, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p12185_1]
                          · have p12185_0 := h12185c.1
                            have p12185_1 := h12185c.2.1
                            have p12185_2 := h12185c.2.2.1
                            have p12185_3 := h12185c.2.2.2
                            linarith only [h8888, hlam, p12185_0]
                          · have p12185_0 := h12185c.1
                            have p12185_1 := h12185c.2.1
                            have p12185_2 := h12185c.2.2.1
                            have p12185_3 := h12185c.2.2.2
                            rcases p12185_3 (m.d 0 2) (by simp) with h12191 | h12191
                            · linarith only [h0, h12191, hlam]
                            · rcases p12185_3 (m.d 1 2) (by simp) with h12193 | h12193
                              · rcases p12185_3 (m.d 2 3) (by simp) with h12194 | h12194
                                · linarith only [h12172, h12194, hlam]
                                · rcases p12185_3 (m.d 2 4) (by simp) with h12196 | h12196
                                  · linarith only [h12173, h12196, hlam]
                                  · rcases p12185_3 (m.d 2 5) (by simp) with h12198 | h12198
                                    · linarith only [h12174, h12198, hlam]
                                    · linarith only [h12198, h8888, hlam]
                              · linarith only [h0, h12193, hlam]
                          · have p12185_0 := h12185c.1
                            have p12185_1 := h12185c.2.1
                            have p12185_2 := h12185c.2.2.1
                            have p12185_3 := h12185c.2.2.2
                            linarith only [hlam, p12185_0]
                          · have p12185_0 := h12185c.1
                            have p12185_1 := h12185c.2.1
                            have p12185_2 := h12185c.2.2.1
                            have p12185_3 := h12185c.2.2.2
                            linarith only [h12172, h12175, h12176, h12179, h12183, h8886, h8888, hlam, p12185_2]
                          · have p12185_0 := h12185c.1
                            have p12185_1 := h12185c.2.1
                            have p12185_2 := h12185c.2.2.1
                            have p12185_3 := h12185c.2.2.2
                            linarith only [h12172, h12175, h12176, h12179, h12183, h8887, h8888, hlam, p12185_2]
                          · have p12185_0 := h12185c.1
                            have p12185_1 := h12185c.2.1
                            have p12185_2 := h12185c.2.2.1
                            have p12185_3 := h12185c.2.2.2
                            linarith only [h12177, h8887, h8888, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p12185_1]
                          · have p12185_0 := h12185c.1
                            have p12185_1 := h12185c.2.1
                            have p12185_2 := h12185c.2.2.1
                            have p12185_3 := h12185c.2.2.2
                            linarith only [h8886, hlam, p12185_0]
                          · have p12185_0 := h12185c.1
                            have p12185_1 := h12185c.2.1
                            have p12185_2 := h12185c.2.2.1
                            have p12185_3 := h12185c.2.2.2
                            linarith only [h12172, hlam, p12185_0]
                          · have p12185_0 := h12185c.1
                            have p12185_1 := h12185c.2.1
                            have p12185_2 := h12185c.2.2.1
                            have p12185_3 := h12185c.2.2.2
                            linarith only [hlam, p12185_0]
                          · have p12185_0 := h12185c.1
                            have p12185_1 := h12185c.2.1
                            have p12185_2 := h12185c.2.2.1
                            have p12185_3 := h12185c.2.2.2
                            linarith only [h12177, hlam, p12185_1]
                          · have p12185_0 := h12185c.1
                            have p12185_1 := h12185c.2.1
                            have p12185_2 := h12185c.2.2.1
                            have p12185_3 := h12185c.2.2.2
                            linarith only [h12179, hlam, p12185_1]
                          · have p12185_0 := h12185c.1
                            have p12185_1 := h12185c.2.1
                            have p12185_2 := h12185c.2.2.1
                            have p12185_3 := h12185c.2.2.2
                            linarith only [h8887, hlam, p12185_0]
                          · have p12185_0 := h12185c.1
                            have p12185_1 := h12185c.2.1
                            have p12185_2 := h12185c.2.2.1
                            have p12185_3 := h12185c.2.2.2
                            linarith only [h12173, hlam, p12185_0]
                          · have p12185_0 := h12185c.1
                            have p12185_1 := h12185c.2.1
                            have p12185_2 := h12185c.2.2.1
                            have p12185_3 := h12185c.2.2.2
                            linarith only [h8887, h8888, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p12185_1]
                          · have p12185_0 := h12185c.1
                            have p12185_1 := h12185c.2.1
                            have p12185_2 := h12185c.2.2.1
                            have p12185_3 := h12185c.2.2.2
                            linarith only [hlam, p12185_0]
                          · have p12185_0 := h12185c.1
                            have p12185_1 := h12185c.2.1
                            have p12185_2 := h12185c.2.2.1
                            have p12185_3 := h12185c.2.2.2
                            linarith only [h12181, hlam, p12185_0]
                          · have p12185_0 := h12185c.1
                            have p12185_1 := h12185c.2.1
                            have p12185_2 := h12185c.2.2.1
                            have p12185_3 := h12185c.2.2.2
                            linarith only [h12174, h8887, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p12185_1]
                          · have p12185_0 := h12185c.1
                            have p12185_1 := h12185c.2.1
                            have p12185_2 := h12185c.2.2.1
                            have p12185_3 := h12185c.2.2.2
                            linarith only [h12174, hlam, p12185_0]
                          · have p12185_0 := h12185c.1
                            have p12185_1 := h12185c.2.1
                            have p12185_2 := h12185c.2.2.1
                            have p12185_3 := h12185c.2.2.2
                            rcases p12185_3 (m.d 0 2) (by simp) with h12218 | h12218
                            · linarith only [h12218, h8888, hlam]
                            · linarith only [h12218, h8886, hlam]
                          · have p12185_0 := h12185c.1
                            have p12185_1 := h12185c.2.1
                            have p12185_2 := h12185c.2.2.1
                            have p12185_3 := h12185c.2.2.2
                            rcases p12185_3 (m.d 0 2) (by simp) with h12221 | h12221
                            · linarith only [h12221, h8888, hlam]
                            · linarith only [h12221, h8887, hlam]
                          · have p12185_0 := h12185c.1
                            have p12185_1 := h12185c.2.1
                            have p12185_2 := h12185c.2.2.1
                            have p12185_3 := h12185c.2.2.2
                            linarith only [hlam, p12185_0]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h12225 | h12225
                  · linarith only [h12140, h12225, h8886, hlam]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h12227 | h12227
                    · linarith only [h12174, h12225, h12227, h8887, h8888, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h12229 | h12229
                      · linarith only [h12174, h12176, h12229, h8887, h8888, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h12231 | h12231
                        · linarith only [h12174, h12176, h12225, h12231, h8887, h8888, hc23, hc34, hlam, hphi]
                        · rcases h2bigk with h12233c | h12233c | h12233c | h12233c | h12233c | h12233c | h12233c | h12233c | h12233c | h12233c | h12233c | h12233c | h12233c | h12233c | h12233c | h12233c | h12233c | h12233c | h12233c | h12233c | h12233c | h12233c | h12233c | h12233c | h12233c
                          · have p12233_0 := h12233c.1
                            have p12233_1 := h12233c.2.1
                            have p12233_2 := h12233c.2.2.1
                            have p12233_3 := h12233c.2.2.2
                            linarith only [hlam, p12233_0]
                          · have p12233_0 := h12233c.1
                            have p12233_1 := h12233c.2.1
                            have p12233_2 := h12233c.2.2.1
                            have p12233_3 := h12233c.2.2.2
                            linarith only [h0, hlam, p12233_0]
                          · have p12233_0 := h12233c.1
                            have p12233_1 := h12233c.2.1
                            have p12233_2 := h12233c.2.2.1
                            have p12233_3 := h12233c.2.2.2
                            linarith only [h12174, h8888, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p12233_1]
                          · have p12233_0 := h12233c.1
                            have p12233_1 := h12233c.2.1
                            have p12233_2 := h12233c.2.2.1
                            have p12233_3 := h12233c.2.2.2
                            linarith only [h12174, h8888, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p12233_1]
                          · have p12233_0 := h12233c.1
                            have p12233_1 := h12233c.2.1
                            have p12233_2 := h12233c.2.2.1
                            have p12233_3 := h12233c.2.2.2
                            linarith only [h8888, hlam, p12233_0]
                          · have p12233_0 := h12233c.1
                            have p12233_1 := h12233c.2.1
                            have p12233_2 := h12233c.2.2.1
                            have p12233_3 := h12233c.2.2.2
                            rcases p12233_3 (m.d 0 2) (by simp) with h12239 | h12239
                            · linarith only [h0, h12239, hlam]
                            · rcases p12233_3 (m.d 1 2) (by simp) with h12241 | h12241
                              · rcases p12233_3 (m.d 2 3) (by simp) with h12242 | h12242
                                · linarith only [h12172, h12242, hlam]
                                · rcases p12233_3 (m.d 2 4) (by simp) with h12244 | h12244
                                  · linarith only [h12173, h12244, hlam]
                                  · rcases p12233_3 (m.d 2 5) (by simp) with h12246 | h12246
                                    · linarith only [h12174, h12246, hlam]
                                    · linarith only [h12246, h8888, hlam]
                              · linarith only [h0, h12241, hlam]
                          · have p12233_0 := h12233c.1
                            have p12233_1 := h12233c.2.1
                            have p12233_2 := h12233c.2.2.1
                            have p12233_3 := h12233c.2.2.2
                            linarith only [hlam, p12233_0]
                          · have p12233_0 := h12233c.1
                            have p12233_1 := h12233c.2.1
                            have p12233_2 := h12233c.2.2.1
                            have p12233_3 := h12233c.2.2.2
                            linarith only [h12174, h8886, h8888, hlam, p12233_2]
                          · have p12233_0 := h12233c.1
                            have p12233_1 := h12233c.2.1
                            have p12233_2 := h12233c.2.2.1
                            have p12233_3 := h12233c.2.2.2
                            linarith only [h12174, h8887, h8888, hlam, p12233_2]
                          · have p12233_0 := h12233c.1
                            have p12233_1 := h12233c.2.1
                            have p12233_2 := h12233c.2.2.1
                            have p12233_3 := h12233c.2.2.2
                            linarith only [h12225, h8887, h8888, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p12233_1]
                          · have p12233_0 := h12233c.1
                            have p12233_1 := h12233c.2.1
                            have p12233_2 := h12233c.2.2.1
                            have p12233_3 := h12233c.2.2.2
                            linarith only [h8886, hlam, p12233_0]
                          · have p12233_0 := h12233c.1
                            have p12233_1 := h12233c.2.1
                            have p12233_2 := h12233c.2.2.1
                            have p12233_3 := h12233c.2.2.2
                            linarith only [h12172, hlam, p12233_0]
                          · have p12233_0 := h12233c.1
                            have p12233_1 := h12233c.2.1
                            have p12233_2 := h12233c.2.2.1
                            have p12233_3 := h12233c.2.2.2
                            linarith only [hlam, p12233_0]
                          · have p12233_0 := h12233c.1
                            have p12233_1 := h12233c.2.1
                            have p12233_2 := h12233c.2.2.1
                            have p12233_3 := h12233c.2.2.2
                            linarith only [h12225, hlam, p12233_1]
                          · have p12233_0 := h12233c.1
                            have p12233_1 := h12233c.2.1
                            have p12233_2 := h12233c.2.2.1
                            have p12233_3 := h12233c.2.2.2
                            linarith only [h12227, hlam, p12233_1]
                          · have p12233_0 := h12233c.1
                            have p12233_1 := h12233c.2.1
                            have p12233_2 := h12233c.2.2.1
                            have p12233_3 := h12233c.2.2.2
                            linarith only [h8887, hlam, p12233_0]
                          · have p12233_0 := h12233c.1
                            have p12233_1 := h12233c.2.1
                            have p12233_2 := h12233c.2.2.1
                            have p12233_3 := h12233c.2.2.2
                            linarith only [h12173, hlam, p12233_0]
                          · have p12233_0 := h12233c.1
                            have p12233_1 := h12233c.2.1
                            have p12233_2 := h12233c.2.2.1
                            have p12233_3 := h12233c.2.2.2
                            linarith only [h12174, h8887, h8888, hc15, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p12233_1]
                          · have p12233_0 := h12233c.1
                            have p12233_1 := h12233c.2.1
                            have p12233_2 := h12233c.2.2.1
                            have p12233_3 := h12233c.2.2.2
                            linarith only [hlam, p12233_0]
                          · have p12233_0 := h12233c.1
                            have p12233_1 := h12233c.2.1
                            have p12233_2 := h12233c.2.2.1
                            have p12233_3 := h12233c.2.2.2
                            linarith only [h12229, hlam, p12233_0]
                          · have p12233_0 := h12233c.1
                            have p12233_1 := h12233c.2.1
                            have p12233_2 := h12233c.2.2.1
                            have p12233_3 := h12233c.2.2.2
                            linarith only [h12227, h8886, hc23, hc35, hlam, hphi, p12233_1]
                          · have p12233_0 := h12233c.1
                            have p12233_1 := h12233c.2.1
                            have p12233_2 := h12233c.2.2.1
                            have p12233_3 := h12233c.2.2.2
                            linarith only [h12174, hlam, p12233_0]
                          · have p12233_0 := h12233c.1
                            have p12233_1 := h12233c.2.1
                            have p12233_2 := h12233c.2.2.1
                            have p12233_3 := h12233c.2.2.2
                            rcases p12233_3 (m.d 0 2) (by simp) with h12266 | h12266
                            · linarith only [h12266, h8888, hlam]
                            · linarith only [h12266, h8886, hlam]
                          · have p12233_0 := h12233c.1
                            have p12233_1 := h12233c.2.1
                            have p12233_2 := h12233c.2.2.1
                            have p12233_3 := h12233c.2.2.2
                            rcases p12233_3 (m.d 0 2) (by simp) with h12269 | h12269
                            · linarith only [h12269, h8888, hlam]
                            · linarith only [h12269, h8887, hlam]
                          · have p12233_0 := h12233c.1
                            have p12233_1 := h12233c.2.1
                            have p12233_2 := h12233c.2.2.1
                            have p12233_3 := h12233c.2.2.2
                            linarith only [hlam, p12233_0]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h12273 | h12273
                · rcases m.htr 2 3 4 (by decide) (by decide) with h12274 | h12274
                  · linarith only [h12170, h12175, h12273, h12274, h6874, hc01, hc23, hlam, hphi, ht12]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h12276 | h12276
                    · linarith only [h12174, h12274, h12276, h8887, h8888, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h12278 | h12278
                      · linarith only [h12170, h12174, h12278, h6874, h8887, h8888, hc01, hc12, hlam, hphi]
                      · linarith only [h12175, h12273, h12274, h12278, h8887, h8888, hc23, hc34, hlam, hphi]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h12281 | h12281
                  · linarith only [h12175, h12281, h8886, h8888, hc13, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h12283 | h12283
                    · linarith only [h12174, h12281, h12283, h8887, h8888, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h12285 | h12285
                      · linarith only [h12174, h12273, h12285, h8887, h8888, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h12287 | h12287
                        · linarith only [h12174, h12273, h12281, h12287, h8887, h8888, hc23, hc34, hlam, hphi]
                        · rcases h2bigk with h12289c | h12289c | h12289c | h12289c | h12289c | h12289c | h12289c | h12289c | h12289c | h12289c | h12289c | h12289c | h12289c | h12289c | h12289c | h12289c | h12289c | h12289c | h12289c | h12289c | h12289c | h12289c | h12289c | h12289c | h12289c
                          · have p12289_0 := h12289c.1
                            have p12289_1 := h12289c.2.1
                            have p12289_2 := h12289c.2.2.1
                            have p12289_3 := h12289c.2.2.2
                            linarith only [hlam, p12289_0]
                          · have p12289_0 := h12289c.1
                            have p12289_1 := h12289c.2.1
                            have p12289_2 := h12289c.2.2.1
                            have p12289_3 := h12289c.2.2.2
                            linarith only [h0, hlam, p12289_0]
                          · have p12289_0 := h12289c.1
                            have p12289_1 := h12289c.2.1
                            have p12289_2 := h12289c.2.2.1
                            have p12289_3 := h12289c.2.2.2
                            linarith only [h12174, h8888, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p12289_1]
                          · have p12289_0 := h12289c.1
                            have p12289_1 := h12289c.2.1
                            have p12289_2 := h12289c.2.2.1
                            have p12289_3 := h12289c.2.2.2
                            linarith only [h12174, h12281, h8888, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p12289_1]
                          · have p12289_0 := h12289c.1
                            have p12289_1 := h12289c.2.1
                            have p12289_2 := h12289c.2.2.1
                            have p12289_3 := h12289c.2.2.2
                            linarith only [h8888, hlam, p12289_0]
                          · have p12289_0 := h12289c.1
                            have p12289_1 := h12289c.2.1
                            have p12289_2 := h12289c.2.2.1
                            have p12289_3 := h12289c.2.2.2
                            rcases p12289_3 (m.d 0 2) (by simp) with h12295 | h12295
                            · linarith only [h0, h12295, hlam]
                            · rcases p12289_3 (m.d 1 2) (by simp) with h12297 | h12297
                              · rcases p12289_3 (m.d 2 3) (by simp) with h12298 | h12298
                                · linarith only [h12172, h12298, hlam]
                                · rcases p12289_3 (m.d 2 4) (by simp) with h12300 | h12300
                                  · linarith only [h12173, h12300, hlam]
                                  · rcases p12289_3 (m.d 2 5) (by simp) with h12302 | h12302
                                    · linarith only [h12174, h12302, hlam]
                                    · linarith only [h12302, h8888, hlam]
                              · linarith only [h0, h12297, hlam]
                          · have p12289_0 := h12289c.1
                            have p12289_1 := h12289c.2.1
                            have p12289_2 := h12289c.2.2.1
                            have p12289_3 := h12289c.2.2.2
                            linarith only [hlam, p12289_0]
                          · have p12289_0 := h12289c.1
                            have p12289_1 := h12289c.2.1
                            have p12289_2 := h12289c.2.2.1
                            have p12289_3 := h12289c.2.2.2
                            linarith only [h12174, h8886, h8888, hlam, p12289_2]
                          · have p12289_0 := h12289c.1
                            have p12289_1 := h12289c.2.1
                            have p12289_2 := h12289c.2.2.1
                            have p12289_3 := h12289c.2.2.2
                            linarith only [h12174, h8887, h8888, hlam, p12289_2]
                          · have p12289_0 := h12289c.1
                            have p12289_1 := h12289c.2.1
                            have p12289_2 := h12289c.2.2.1
                            have p12289_3 := h12289c.2.2.2
                            linarith only [h12281, h8887, h8888, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p12289_1]
                          · have p12289_0 := h12289c.1
                            have p12289_1 := h12289c.2.1
                            have p12289_2 := h12289c.2.2.1
                            have p12289_3 := h12289c.2.2.2
                            linarith only [h8886, hlam, p12289_0]
                          · have p12289_0 := h12289c.1
                            have p12289_1 := h12289c.2.1
                            have p12289_2 := h12289c.2.2.1
                            have p12289_3 := h12289c.2.2.2
                            linarith only [h12172, hlam, p12289_0]
                          · have p12289_0 := h12289c.1
                            have p12289_1 := h12289c.2.1
                            have p12289_2 := h12289c.2.2.1
                            have p12289_3 := h12289c.2.2.2
                            linarith only [hlam, p12289_0]
                          · have p12289_0 := h12289c.1
                            have p12289_1 := h12289c.2.1
                            have p12289_2 := h12289c.2.2.1
                            have p12289_3 := h12289c.2.2.2
                            linarith only [h12281, hlam, p12289_1]
                          · have p12289_0 := h12289c.1
                            have p12289_1 := h12289c.2.1
                            have p12289_2 := h12289c.2.2.1
                            have p12289_3 := h12289c.2.2.2
                            linarith only [h12283, hlam, p12289_1]
                          · have p12289_0 := h12289c.1
                            have p12289_1 := h12289c.2.1
                            have p12289_2 := h12289c.2.2.1
                            have p12289_3 := h12289c.2.2.2
                            linarith only [h8887, hlam, p12289_0]
                          · have p12289_0 := h12289c.1
                            have p12289_1 := h12289c.2.1
                            have p12289_2 := h12289c.2.2.1
                            have p12289_3 := h12289c.2.2.2
                            linarith only [h12173, hlam, p12289_0]
                          · have p12289_0 := h12289c.1
                            have p12289_1 := h12289c.2.1
                            have p12289_2 := h12289c.2.2.1
                            have p12289_3 := h12289c.2.2.2
                            linarith only [h12174, h8887, h8888, hc15, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p12289_1]
                          · have p12289_0 := h12289c.1
                            have p12289_1 := h12289c.2.1
                            have p12289_2 := h12289c.2.2.1
                            have p12289_3 := h12289c.2.2.2
                            linarith only [hlam, p12289_0]
                          · have p12289_0 := h12289c.1
                            have p12289_1 := h12289c.2.1
                            have p12289_2 := h12289c.2.2.1
                            have p12289_3 := h12289c.2.2.2
                            linarith only [h12285, hlam, p12289_0]
                          · have p12289_0 := h12289c.1
                            have p12289_1 := h12289c.2.1
                            have p12289_2 := h12289c.2.2.1
                            have p12289_3 := h12289c.2.2.2
                            linarith only [h12283, h8886, hc23, hc35, hlam, hphi, p12289_1]
                          · have p12289_0 := h12289c.1
                            have p12289_1 := h12289c.2.1
                            have p12289_2 := h12289c.2.2.1
                            have p12289_3 := h12289c.2.2.2
                            linarith only [h12174, hlam, p12289_0]
                          · have p12289_0 := h12289c.1
                            have p12289_1 := h12289c.2.1
                            have p12289_2 := h12289c.2.2.1
                            have p12289_3 := h12289c.2.2.2
                            rcases p12289_3 (m.d 0 2) (by simp) with h12322 | h12322
                            · linarith only [h12322, h8888, hlam]
                            · linarith only [h12322, h8886, hlam]
                          · have p12289_0 := h12289c.1
                            have p12289_1 := h12289c.2.1
                            have p12289_2 := h12289c.2.2.1
                            have p12289_3 := h12289c.2.2.2
                            rcases p12289_3 (m.d 0 2) (by simp) with h12325 | h12325
                            · linarith only [h12325, h8888, hlam]
                            · linarith only [h12325, h8887, hlam]
                          · have p12289_0 := h12289c.1
                            have p12289_1 := h12289c.2.1
                            have p12289_2 := h12289c.2.2.1
                            have p12289_3 := h12289c.2.2.2
                            linarith only [hlam, p12289_0]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h12329 | h12329
              · rcases m.htr 1 4 5 (by decide) (by decide) with h12330 | h12330
                · linarith only [h12170, h12172, h12174, h12329, h12330, h6874, hc01, hc25, hlam, hphi, ht12]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h12332 | h12332
                  · linarith only [h12140, h12332, h8886, hlam]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h12334 | h12334
                    · linarith only [h12140, h12172, h12174, h12329, h12334, h8886, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                    · linarith only [h12140, h12172, h12174, h12329, h12334, h8886, hc23, hc35, hlam, hphi]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h12337 | h12337
                · linarith only [h12170, h12173, h12174, h12337, h6874, hc01, hc25, hlam, hphi, ht12]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h12339 | h12339
                  · linarith only [h0, h12174, h12329, h12339, h8886, hc13, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h12341 | h12341
                    · linarith only [h0, h12140, h12174, h12337, h12341, h6874, h8886, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h12343 | h12343
                      · linarith only [h0, h12174, h12337, h12341, h12343, h8887, hc14, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h12345 | h12345
                        · linarith only [h0, h12174, h12339, h12343, h12345, h8887, hc23, hc34, hlam, hphi]
                        · rcases h2bigk with h12347c | h12347c | h12347c | h12347c | h12347c | h12347c | h12347c | h12347c | h12347c | h12347c | h12347c | h12347c | h12347c | h12347c | h12347c | h12347c | h12347c | h12347c | h12347c | h12347c | h12347c | h12347c | h12347c | h12347c | h12347c
                          · have p12347_0 := h12347c.1
                            have p12347_1 := h12347c.2.1
                            have p12347_2 := h12347c.2.2.1
                            have p12347_3 := h12347c.2.2.2
                            linarith only [hlam, p12347_0]
                          · have p12347_0 := h12347c.1
                            have p12347_1 := h12347c.2.1
                            have p12347_2 := h12347c.2.2.1
                            have p12347_3 := h12347c.2.2.2
                            linarith only [h0, hlam, p12347_0]
                          · have p12347_0 := h12347c.1
                            have p12347_1 := h12347c.2.1
                            have p12347_2 := h12347c.2.2.1
                            have p12347_3 := h12347c.2.2.2
                            linarith only [h0, h12174, h12341, h12345, hc23, hc45, hlam, hphi, ht34, p12347_1]
                          · have p12347_0 := h12347c.1
                            have p12347_1 := h12347c.2.1
                            have p12347_2 := h12347c.2.2.1
                            have p12347_3 := h12347c.2.2.2
                            linarith only [h0, h12174, h12339, h12341, h12345, hc23, hc45, hlam, hphi, ht34, p12347_1]
                          · have p12347_0 := h12347c.1
                            have p12347_1 := h12347c.2.1
                            have p12347_2 := h12347c.2.2.1
                            have p12347_3 := h12347c.2.2.2
                            linarith only [h8888, hlam, p12347_0]
                          · have p12347_0 := h12347c.1
                            have p12347_1 := h12347c.2.1
                            have p12347_2 := h12347c.2.2.1
                            have p12347_3 := h12347c.2.2.2
                            linarith only [h12174, h12341, h12345, hc02, hc45, hlam, hphi, ht23, ht34, p12347_1]
                          · have p12347_0 := h12347c.1
                            have p12347_1 := h12347c.2.1
                            have p12347_2 := h12347c.2.2.1
                            have p12347_3 := h12347c.2.2.2
                            linarith only [hlam, p12347_0]
                          · have p12347_0 := h12347c.1
                            have p12347_1 := h12347c.2.1
                            have p12347_2 := h12347c.2.2.1
                            have p12347_3 := h12347c.2.2.2
                            linarith only [h12174, h12341, h12345, hc23, hc45, hlam, hphi, ht34, p12347_1]
                          · have p12347_0 := h12347c.1
                            have p12347_1 := h12347c.2.1
                            have p12347_2 := h12347c.2.2.1
                            have p12347_3 := h12347c.2.2.2
                            linarith only [h12174, h12339, h12341, h12345, hc23, hc45, hlam, hphi, ht34, p12347_1]
                          · have p12347_0 := h12347c.1
                            have p12347_1 := h12347c.2.1
                            have p12347_2 := h12347c.2.2.1
                            have p12347_3 := h12347c.2.2.2
                            linarith only [h12174, hlam, p12347_0]
                          · have p12347_0 := h12347c.1
                            have p12347_1 := h12347c.2.1
                            have p12347_2 := h12347c.2.2.1
                            have p12347_3 := h12347c.2.2.2
                            linarith only [h8886, hlam, p12347_0]
                          · have p12347_0 := h12347c.1
                            have p12347_1 := h12347c.2.1
                            have p12347_2 := h12347c.2.2.1
                            have p12347_3 := h12347c.2.2.2
                            linarith only [h12172, hlam, p12347_0]
                          · have p12347_0 := h12347c.1
                            have p12347_1 := h12347c.2.1
                            have p12347_2 := h12347c.2.2.1
                            have p12347_3 := h12347c.2.2.2
                            linarith only [hlam, p12347_0]
                          · have p12347_0 := h12347c.1
                            have p12347_1 := h12347c.2.1
                            have p12347_2 := h12347c.2.2.1
                            have p12347_3 := h12347c.2.2.2
                            linarith only [h12339, hlam, p12347_1]
                          · have p12347_0 := h12347c.1
                            have p12347_1 := h12347c.2.1
                            have p12347_2 := h12347c.2.2.1
                            have p12347_3 := h12347c.2.2.2
                            linarith only [h12341, hlam, p12347_1]
                          · have p12347_0 := h12347c.1
                            have p12347_1 := h12347c.2.1
                            have p12347_2 := h12347c.2.2.1
                            have p12347_3 := h12347c.2.2.2
                            linarith only [h8887, hlam, p12347_0]
                          · have p12347_0 := h12347c.1
                            have p12347_1 := h12347c.2.1
                            have p12347_2 := h12347c.2.2.1
                            have p12347_3 := h12347c.2.2.2
                            linarith only [h12173, hlam, p12347_0]
                          · have p12347_0 := h12347c.1
                            have p12347_1 := h12347c.2.1
                            have p12347_2 := h12347c.2.2.1
                            have p12347_3 := h12347c.2.2.2
                            linarith only [h0, h12174, h12341, h12345, h8887, hc23, hc45, hlam, hphi, ht34, p12347_1]
                          · have p12347_0 := h12347c.1
                            have p12347_1 := h12347c.2.1
                            have p12347_2 := h12347c.2.2.1
                            have p12347_3 := h12347c.2.2.2
                            linarith only [hlam, p12347_0]
                          · have p12347_0 := h12347c.1
                            have p12347_1 := h12347c.2.1
                            have p12347_2 := h12347c.2.2.1
                            have p12347_3 := h12347c.2.2.2
                            linarith only [h12343, hlam, p12347_0]
                          · have p12347_0 := h12347c.1
                            have p12347_1 := h12347c.2.1
                            have p12347_2 := h12347c.2.2.1
                            have p12347_3 := h12347c.2.2.2
                            linarith only [h12341, h12345, h8887, hc24, hc45, hlam, hphi, p12347_1]
                          · have p12347_0 := h12347c.1
                            have p12347_1 := h12347c.2.1
                            have p12347_2 := h12347c.2.2.1
                            have p12347_3 := h12347c.2.2.2
                            linarith only [h12173, h12341, h12345, h6874, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p12347_1]
                          · have p12347_0 := h12347c.1
                            have p12347_1 := h12347c.2.1
                            have p12347_2 := h12347c.2.2.1
                            have p12347_3 := h12347c.2.2.2
                            rcases p12347_3 (m.d 0 2) (by simp) with h12370 | h12370
                            · linarith only [h12370, h8888, hlam]
                            · linarith only [h12370, h8886, hlam]
                          · have p12347_0 := h12347c.1
                            have p12347_1 := h12347c.2.1
                            have p12347_2 := h12347c.2.2.1
                            have p12347_3 := h12347c.2.2.2
                            rcases p12347_3 (m.d 0 2) (by simp) with h12373 | h12373
                            · linarith only [h12373, h8888, hlam]
                            · linarith only [h12373, h8887, hlam]
                          · have p12347_0 := h12347c.1
                            have p12347_1 := h12347c.2.1
                            have p12347_2 := h12347c.2.2.1
                            have p12347_3 := h12347c.2.2.2
                            linarith only [hlam, p12347_0]
          · linarith only [h0, h12173, h8887, hlam]
        · linarith only [h0, h12172, h8886, hlam]

set_option maxHeartbeats 7728000 in
set_option maxHeartbeats 7728000 in
theorem r1l7_12_24_L_I_H_I_s8 (m : N7Model)
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6874 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg8886 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
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
  have h8886 := hg8886
  rcases m.htr 0 2 4 (by decide) (by decide) with h8887 | h8887
  · exact r1l7_12_24_L_I_H_I_s9 m hb2 hb4 h0 h6874 h8886 h8887
  · rcases m.htr 0 2 5 (by decide) (by decide) with h12379 | h12379
    · rcases m.htr 0 3 4 (by decide) (by decide) with h12380 | h12380
      · linarith only [h12380, h8886, h8887, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h12382 | h12382
        · rcases m.htr 1 2 3 (by decide) (by decide) with h12383 | h12383
          · rcases m.htr 1 2 4 (by decide) (by decide) with h12384 | h12384
            · rcases m.htr 1 2 5 (by decide) (by decide) with h12385 | h12385
              · rcases m.htr 1 3 4 (by decide) (by decide) with h12386 | h12386
                · rcases m.htr 1 4 5 (by decide) (by decide) with h12387 | h12387
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h12388 | h12388
                    · linarith only [h12380, h12384, h12388, h8886, h8887, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h12390 | h12390
                      · linarith only [h12383, h12386, h12388, h12390, h8886, h8887, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h12392 | h12392
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h12393 | h12393
                          · rcases h2bigk with h12394c | h12394c | h12394c | h12394c | h12394c | h12394c | h12394c | h12394c | h12394c | h12394c | h12394c | h12394c | h12394c | h12394c | h12394c | h12394c | h12394c | h12394c | h12394c | h12394c | h12394c | h12394c | h12394c | h12394c | h12394c
                            · have p12394_0 := h12394c.1
                              have p12394_1 := h12394c.2.1
                              have p12394_2 := h12394c.2.2.1
                              have p12394_3 := h12394c.2.2.2
                              linarith only [hlam, p12394_0]
                            · have p12394_0 := h12394c.1
                              have p12394_1 := h12394c.2.1
                              have p12394_2 := h12394c.2.2.1
                              have p12394_3 := h12394c.2.2.2
                              linarith only [h0, hlam, p12394_0]
                            · have p12394_0 := h12394c.1
                              have p12394_1 := h12394c.2.1
                              have p12394_2 := h12394c.2.2.1
                              have p12394_3 := h12394c.2.2.2
                              linarith only [h12383, h12386, h12388, h8887, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p12394_1]
                            · have p12394_0 := h12394c.1
                              have p12394_1 := h12394c.2.1
                              have p12394_2 := h12394c.2.2.1
                              have p12394_3 := h12394c.2.2.2
                              linarith only [h8887, hlam, p12394_0]
                            · have p12394_0 := h12394c.1
                              have p12394_1 := h12394c.2.1
                              have p12394_2 := h12394c.2.2.1
                              have p12394_3 := h12394c.2.2.2
                              linarith only [h12383, h12386, h12388, h8887, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p12394_1]
                            · have p12394_0 := h12394c.1
                              have p12394_1 := h12394c.2.1
                              have p12394_2 := h12394c.2.2.1
                              have p12394_3 := h12394c.2.2.2
                              rcases p12394_3 (m.d 0 2) (by simp) with h12400 | h12400
                              · linarith only [h0, h12400, hlam]
                              · rcases p12394_3 (m.d 1 2) (by simp) with h12402 | h12402
                                · rcases p12394_3 (m.d 2 3) (by simp) with h12403 | h12403
                                  · linarith only [h12383, h12403, hlam]
                                  · rcases p12394_3 (m.d 2 4) (by simp) with h12405 | h12405
                                    · linarith only [h12384, h12405, hlam]
                                    · linarith only [h12405, h8887, hlam]
                                · linarith only [h0, h12402, hlam]
                            · have p12394_0 := h12394c.1
                              have p12394_1 := h12394c.2.1
                              have p12394_2 := h12394c.2.2.1
                              have p12394_3 := h12394c.2.2.2
                              linarith only [hlam, p12394_0]
                            · have p12394_0 := h12394c.1
                              have p12394_1 := h12394c.2.1
                              have p12394_2 := h12394c.2.2.1
                              have p12394_3 := h12394c.2.2.2
                              linarith only [h12383, h12386, h12388, h8886, h8887, hlam, p12394_2]
                            · have p12394_0 := h12394c.1
                              have p12394_1 := h12394c.2.1
                              have p12394_2 := h12394c.2.2.1
                              have p12394_3 := h12394c.2.2.2
                              linarith only [h0, h8887, hc01, hc12, hlam, hphi, p12394_1]
                            · have p12394_0 := h12394c.1
                              have p12394_1 := h12394c.2.1
                              have p12394_2 := h12394c.2.2.1
                              have p12394_3 := h12394c.2.2.2
                              linarith only [h12379, h12384, h8887, hlam, p12394_2]
                            · have p12394_0 := h12394c.1
                              have p12394_1 := h12394c.2.1
                              have p12394_2 := h12394c.2.2.1
                              have p12394_3 := h12394c.2.2.2
                              linarith only [h8886, hlam, p12394_0]
                            · have p12394_0 := h12394c.1
                              have p12394_1 := h12394c.2.1
                              have p12394_2 := h12394c.2.2.1
                              have p12394_3 := h12394c.2.2.2
                              linarith only [h12383, hlam, p12394_0]
                            · have p12394_0 := h12394c.1
                              have p12394_1 := h12394c.2.1
                              have p12394_2 := h12394c.2.2.1
                              have p12394_3 := h12394c.2.2.2
                              linarith only [hlam, p12394_0]
                            · have p12394_0 := h12394c.1
                              have p12394_1 := h12394c.2.1
                              have p12394_2 := h12394c.2.2.1
                              have p12394_3 := h12394c.2.2.2
                              linarith only [h12388, hlam, p12394_1]
                            · have p12394_0 := h12394c.1
                              have p12394_1 := h12394c.2.1
                              have p12394_2 := h12394c.2.2.1
                              have p12394_3 := h12394c.2.2.2
                              linarith only [h12390, hlam, p12394_1]
                            · have p12394_0 := h12394c.1
                              have p12394_1 := h12394c.2.1
                              have p12394_2 := h12394c.2.2.1
                              have p12394_3 := h12394c.2.2.2
                              linarith only [h12379, h12384, h12390, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p12394_1]
                            · have p12394_0 := h12394c.1
                              have p12394_1 := h12394c.2.1
                              have p12394_2 := h12394c.2.2.1
                              have p12394_3 := h12394c.2.2.2
                              linarith only [h12384, hlam, p12394_0]
                            · have p12394_0 := h12394c.1
                              have p12394_1 := h12394c.2.1
                              have p12394_2 := h12394c.2.2.1
                              have p12394_3 := h12394c.2.2.2
                              rcases p12394_3 (m.d 0 2) (by simp) with h12420 | h12420
                              · linarith only [h12420, h8887, hlam]
                              · linarith only [h12420, h8886, hlam]
                            · have p12394_0 := h12394c.1
                              have p12394_1 := h12394c.2.1
                              have p12394_2 := h12394c.2.2.1
                              have p12394_3 := h12394c.2.2.2
                              linarith only [hlam, p12394_0]
                            · have p12394_0 := h12394c.1
                              have p12394_1 := h12394c.2.1
                              have p12394_2 := h12394c.2.2.1
                              have p12394_3 := h12394c.2.2.2
                              rcases p12394_3 (m.d 0 2) (by simp) with h12424 | h12424
                              · linarith only [h12424, h8887, hlam]
                              · linarith only [h12379, h12424, hlam]
                            · have p12394_0 := h12394c.1
                              have p12394_1 := h12394c.2.1
                              have p12394_2 := h12394c.2.2.1
                              have p12394_3 := h12394c.2.2.2
                              linarith only [h12379, hlam, p12394_0]
                            · have p12394_0 := h12394c.1
                              have p12394_1 := h12394c.2.1
                              have p12394_2 := h12394c.2.2.1
                              have p12394_3 := h12394c.2.2.2
                              linarith only [h12385, hlam, p12394_0]
                            · have p12394_0 := h12394c.1
                              have p12394_1 := h12394c.2.1
                              have p12394_2 := h12394c.2.2.1
                              have p12394_3 := h12394c.2.2.2
                              linarith only [h12379, h12383, h12386, h12388, h8887, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p12394_1]
                            · have p12394_0 := h12394c.1
                              have p12394_1 := h12394c.2.1
                              have p12394_2 := h12394c.2.2.1
                              have p12394_3 := h12394c.2.2.2
                              linarith only [h12392, hlam, p12394_1]
                            · have p12394_0 := h12394c.1
                              have p12394_1 := h12394c.2.1
                              have p12394_2 := h12394c.2.2.1
                              have p12394_3 := h12394c.2.2.2
                              linarith only [hlam, p12394_0]
                          · linarith only [h12388, h12393, h8886, h8887, hc23, hc45, hlam, hphi, ht34]
                        · linarith only [h12379, h12382, h12390, h12392, h8887, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                  · linarith only [h12379, h12382, h12387, h6874, h8887, hc01, hc24, hlam, hphi, ht12]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h12435 | h12435
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h12436 | h12436
                    · linarith only [h12384, h12386, h12436, h8886, h8887, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h12438 | h12438
                      · linarith only [h12384, h12438, h8886, h8887, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h12440 | h12440
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h12441 | h12441
                          · rcases h2bigk with h12442c | h12442c | h12442c | h12442c | h12442c | h12442c | h12442c | h12442c | h12442c | h12442c | h12442c | h12442c | h12442c | h12442c | h12442c | h12442c | h12442c | h12442c | h12442c | h12442c | h12442c | h12442c | h12442c | h12442c | h12442c
                            · have p12442_0 := h12442c.1
                              have p12442_1 := h12442c.2.1
                              have p12442_2 := h12442c.2.2.1
                              have p12442_3 := h12442c.2.2.2
                              linarith only [hlam, p12442_0]
                            · have p12442_0 := h12442c.1
                              have p12442_1 := h12442c.2.1
                              have p12442_2 := h12442c.2.2.1
                              have p12442_3 := h12442c.2.2.2
                              linarith only [h0, hlam, p12442_0]
                            · have p12442_0 := h12442c.1
                              have p12442_1 := h12442c.2.1
                              have p12442_2 := h12442c.2.2.1
                              have p12442_3 := h12442c.2.2.2
                              linarith only [h12384, h8887, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p12442_1]
                            · have p12442_0 := h12442c.1
                              have p12442_1 := h12442c.2.1
                              have p12442_2 := h12442c.2.2.1
                              have p12442_3 := h12442c.2.2.2
                              linarith only [h8887, hlam, p12442_0]
                            · have p12442_0 := h12442c.1
                              have p12442_1 := h12442c.2.1
                              have p12442_2 := h12442c.2.2.1
                              have p12442_3 := h12442c.2.2.2
                              linarith only [h12384, h8887, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p12442_1]
                            · have p12442_0 := h12442c.1
                              have p12442_1 := h12442c.2.1
                              have p12442_2 := h12442c.2.2.1
                              have p12442_3 := h12442c.2.2.2
                              rcases p12442_3 (m.d 0 2) (by simp) with h12448 | h12448
                              · linarith only [h0, h12448, hlam]
                              · rcases p12442_3 (m.d 1 2) (by simp) with h12450 | h12450
                                · rcases p12442_3 (m.d 2 3) (by simp) with h12451 | h12451
                                  · linarith only [h12383, h12451, hlam]
                                  · rcases p12442_3 (m.d 2 4) (by simp) with h12453 | h12453
                                    · linarith only [h12384, h12453, hlam]
                                    · linarith only [h12453, h8887, hlam]
                                · linarith only [h0, h12450, hlam]
                            · have p12442_0 := h12442c.1
                              have p12442_1 := h12442c.2.1
                              have p12442_2 := h12442c.2.2.1
                              have p12442_3 := h12442c.2.2.2
                              linarith only [hlam, p12442_0]
                            · have p12442_0 := h12442c.1
                              have p12442_1 := h12442c.2.1
                              have p12442_2 := h12442c.2.2.1
                              have p12442_3 := h12442c.2.2.2
                              linarith only [h12384, h8886, h8887, hlam, p12442_2]
                            · have p12442_0 := h12442c.1
                              have p12442_1 := h12442c.2.1
                              have p12442_2 := h12442c.2.2.1
                              have p12442_3 := h12442c.2.2.2
                              linarith only [h0, h8887, hc01, hc12, hlam, hphi, p12442_1]
                            · have p12442_0 := h12442c.1
                              have p12442_1 := h12442c.2.1
                              have p12442_2 := h12442c.2.2.1
                              have p12442_3 := h12442c.2.2.2
                              linarith only [h12379, h12384, h8887, hlam, p12442_2]
                            · have p12442_0 := h12442c.1
                              have p12442_1 := h12442c.2.1
                              have p12442_2 := h12442c.2.2.1
                              have p12442_3 := h12442c.2.2.2
                              linarith only [h8886, hlam, p12442_0]
                            · have p12442_0 := h12442c.1
                              have p12442_1 := h12442c.2.1
                              have p12442_2 := h12442c.2.2.1
                              have p12442_3 := h12442c.2.2.2
                              linarith only [h12383, hlam, p12442_0]
                            · have p12442_0 := h12442c.1
                              have p12442_1 := h12442c.2.1
                              have p12442_2 := h12442c.2.2.1
                              have p12442_3 := h12442c.2.2.2
                              linarith only [hlam, p12442_0]
                            · have p12442_0 := h12442c.1
                              have p12442_1 := h12442c.2.1
                              have p12442_2 := h12442c.2.2.1
                              have p12442_3 := h12442c.2.2.2
                              linarith only [h12436, hlam, p12442_1]
                            · have p12442_0 := h12442c.1
                              have p12442_1 := h12442c.2.1
                              have p12442_2 := h12442c.2.2.1
                              have p12442_3 := h12442c.2.2.2
                              linarith only [h12438, hlam, p12442_1]
                            · have p12442_0 := h12442c.1
                              have p12442_1 := h12442c.2.1
                              have p12442_2 := h12442c.2.2.1
                              have p12442_3 := h12442c.2.2.2
                              linarith only [h12379, h12384, h12386, h12438, hc23, hc34, hlam, hphi, p12442_1]
                            · have p12442_0 := h12442c.1
                              have p12442_1 := h12442c.2.1
                              have p12442_2 := h12442c.2.2.1
                              have p12442_3 := h12442c.2.2.2
                              linarith only [h12384, hlam, p12442_0]
                            · have p12442_0 := h12442c.1
                              have p12442_1 := h12442c.2.1
                              have p12442_2 := h12442c.2.2.1
                              have p12442_3 := h12442c.2.2.2
                              rcases p12442_3 (m.d 0 2) (by simp) with h12468 | h12468
                              · linarith only [h12468, h8887, hlam]
                              · linarith only [h12468, h8886, hlam]
                            · have p12442_0 := h12442c.1
                              have p12442_1 := h12442c.2.1
                              have p12442_2 := h12442c.2.2.1
                              have p12442_3 := h12442c.2.2.2
                              linarith only [hlam, p12442_0]
                            · have p12442_0 := h12442c.1
                              have p12442_1 := h12442c.2.1
                              have p12442_2 := h12442c.2.2.1
                              have p12442_3 := h12442c.2.2.2
                              rcases p12442_3 (m.d 0 2) (by simp) with h12472 | h12472
                              · linarith only [h12472, h8887, hlam]
                              · linarith only [h12379, h12472, hlam]
                            · have p12442_0 := h12442c.1
                              have p12442_1 := h12442c.2.1
                              have p12442_2 := h12442c.2.2.1
                              have p12442_3 := h12442c.2.2.2
                              linarith only [h12379, hlam, p12442_0]
                            · have p12442_0 := h12442c.1
                              have p12442_1 := h12442c.2.1
                              have p12442_2 := h12442c.2.2.1
                              have p12442_3 := h12442c.2.2.2
                              linarith only [h12385, hlam, p12442_0]
                            · have p12442_0 := h12442c.1
                              have p12442_1 := h12442c.2.1
                              have p12442_2 := h12442c.2.2.1
                              have p12442_3 := h12442c.2.2.2
                              linarith only [h12379, h12384, h8887, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p12442_1]
                            · have p12442_0 := h12442c.1
                              have p12442_1 := h12442c.2.1
                              have p12442_2 := h12442c.2.2.1
                              have p12442_3 := h12442c.2.2.2
                              linarith only [h12440, hlam, p12442_1]
                            · have p12442_0 := h12442c.1
                              have p12442_1 := h12442c.2.1
                              have p12442_2 := h12442c.2.2.1
                              have p12442_3 := h12442c.2.2.2
                              linarith only [hlam, p12442_0]
                          · linarith only [h12382, h12386, h12441, h6874, hlam]
                        · linarith only [h12379, h12382, h12440, h8887, hlam]
                  · linarith only [h12379, h12382, h12384, h12435, h6874, h8887, hc01, hc12, hlam, hphi]
              · linarith only [h12379, h12384, h12385, h8887, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h12484 | h12484
              · rcases m.htr 1 3 4 (by decide) (by decide) with h12485 | h12485
                · linarith only [h12383, h12384, h12485, hlam]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h12487 | h12487
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h12488 | h12488
                    · linarith only [h12485, h12488, h8886, h8887, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h12490 | h12490
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h12491 | h12491
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h12492 | h12492
                          · rcases h2bigk with h12493c | h12493c | h12493c | h12493c | h12493c | h12493c | h12493c | h12493c | h12493c | h12493c | h12493c | h12493c | h12493c | h12493c | h12493c | h12493c | h12493c | h12493c | h12493c | h12493c | h12493c | h12493c | h12493c | h12493c | h12493c
                            · have p12493_0 := h12493c.1
                              have p12493_1 := h12493c.2.1
                              have p12493_2 := h12493c.2.2.1
                              have p12493_3 := h12493c.2.2.2
                              linarith only [hlam, p12493_0]
                            · have p12493_0 := h12493c.1
                              have p12493_1 := h12493c.2.1
                              have p12493_2 := h12493c.2.2.1
                              have p12493_3 := h12493c.2.2.2
                              linarith only [h0, hlam, p12493_0]
                            · have p12493_0 := h12493c.1
                              have p12493_1 := h12493c.2.1
                              have p12493_2 := h12493c.2.2.1
                              have p12493_3 := h12493c.2.2.2
                              linarith only [h0, h12384, h12488, h12490, h12492, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p12493_1]
                            · have p12493_0 := h12493c.1
                              have p12493_1 := h12493c.2.1
                              have p12493_2 := h12493c.2.2.1
                              have p12493_3 := h12493c.2.2.2
                              linarith only [h8887, hlam, p12493_0]
                            · have p12493_0 := h12493c.1
                              have p12493_1 := h12493c.2.1
                              have p12493_2 := h12493c.2.2.1
                              have p12493_3 := h12493c.2.2.2
                              rcases p12493_3 (m.d 0 2) (by simp) with h12498 | h12498
                              · rcases p12493_3 (m.d 1 2) (by simp) with h12499 | h12499
                                · rcases p12493_3 (m.d 2 3) (by simp) with h12500 | h12500
                                  · linarith only [h12500, h8886, hlam]
                                  · linarith only [h12490, h12500, hlam]
                                · linarith only [h12484, h12499, hlam]
                              · linarith only [h12498, hlam, p12493_0]
                            · have p12493_0 := h12493c.1
                              have p12493_1 := h12493c.2.1
                              have p12493_2 := h12493c.2.2.1
                              have p12493_3 := h12493c.2.2.2
                              linarith only [h12384, h12488, hc02, hc34, hlam, hphi, ht23, p12493_1]
                            · have p12493_0 := h12493c.1
                              have p12493_1 := h12493c.2.1
                              have p12493_2 := h12493c.2.2.1
                              have p12493_3 := h12493c.2.2.2
                              linarith only [hlam, p12493_0]
                            · have p12493_0 := h12493c.1
                              have p12493_1 := h12493c.2.1
                              have p12493_2 := h12493c.2.2.1
                              have p12493_3 := h12493c.2.2.2
                              linarith only [h12384, h12488, h12490, h12492, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p12493_1]
                            · have p12493_0 := h12493c.1
                              have p12493_1 := h12493c.2.1
                              have p12493_2 := h12493c.2.2.1
                              have p12493_3 := h12493c.2.2.2
                              linarith only [h12384, hlam, p12493_0]
                            · have p12493_0 := h12493c.1
                              have p12493_1 := h12493c.2.1
                              have p12493_2 := h12493c.2.2.1
                              have p12493_3 := h12493c.2.2.2
                              rcases p12493_3 (m.d 0 2) (by simp) with h12509 | h12509
                              · linarith only [h0, h12509, hlam]
                              · linarith only [h12379, h12509, hlam]
                            · have p12493_0 := h12493c.1
                              have p12493_1 := h12493c.2.1
                              have p12493_2 := h12493c.2.2.1
                              have p12493_3 := h12493c.2.2.2
                              linarith only [h8886, hlam, p12493_0]
                            · have p12493_0 := h12493c.1
                              have p12493_1 := h12493c.2.1
                              have p12493_2 := h12493c.2.2.1
                              have p12493_3 := h12493c.2.2.2
                              linarith only [h12383, hlam, p12493_0]
                            · have p12493_0 := h12493c.1
                              have p12493_1 := h12493c.2.1
                              have p12493_2 := h12493c.2.2.1
                              have p12493_3 := h12493c.2.2.2
                              linarith only [hlam, p12493_0]
                            · have p12493_0 := h12493c.1
                              have p12493_1 := h12493c.2.1
                              have p12493_2 := h12493c.2.2.1
                              have p12493_3 := h12493c.2.2.2
                              linarith only [h12488, hlam, p12493_1]
                            · have p12493_0 := h12493c.1
                              have p12493_1 := h12493c.2.1
                              have p12493_2 := h12493c.2.2.1
                              have p12493_3 := h12493c.2.2.2
                              linarith only [h0, h12384, h12488, h12490, h12492, h8886, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p12493_1]
                            · have p12493_0 := h12493c.1
                              have p12493_1 := h12493c.2.1
                              have p12493_2 := h12493c.2.2.1
                              have p12493_3 := h12493c.2.2.2
                              linarith only [h12488, h8886, hc23, hc34, hlam, hphi, p12493_1]
                            · have p12493_0 := h12493c.1
                              have p12493_1 := h12493c.2.1
                              have p12493_2 := h12493c.2.2.1
                              have p12493_3 := h12493c.2.2.2
                              linarith only [h0, h12488, hc01, hc34, hlam, hphi, ht12, ht23, p12493_1]
                            · have p12493_0 := h12493c.1
                              have p12493_1 := h12493c.2.1
                              have p12493_2 := h12493c.2.2.1
                              have p12493_3 := h12493c.2.2.2
                              rcases p12493_3 (m.d 0 2) (by simp) with h12519 | h12519
                              · linarith only [h12519, h8887, hlam]
                              · linarith only [h12519, h8886, hlam]
                            · have p12493_0 := h12493c.1
                              have p12493_1 := h12493c.2.1
                              have p12493_2 := h12493c.2.2.1
                              have p12493_3 := h12493c.2.2.2
                              linarith only [hlam, p12493_0]
                            · have p12493_0 := h12493c.1
                              have p12493_1 := h12493c.2.1
                              have p12493_2 := h12493c.2.2.1
                              have p12493_3 := h12493c.2.2.2
                              rcases p12493_3 (m.d 0 2) (by simp) with h12523 | h12523
                              · linarith only [h12523, h8887, hlam]
                              · linarith only [h12379, h12523, hlam]
                            · have p12493_0 := h12493c.1
                              have p12493_1 := h12493c.2.1
                              have p12493_2 := h12493c.2.2.1
                              have p12493_3 := h12493c.2.2.2
                              linarith only [h12379, hlam, p12493_0]
                            · have p12493_0 := h12493c.1
                              have p12493_1 := h12493c.2.1
                              have p12493_2 := h12493c.2.2.1
                              have p12493_3 := h12493c.2.2.2
                              linarith only [h12484, hlam, p12493_0]
                            · have p12493_0 := h12493c.1
                              have p12493_1 := h12493c.2.1
                              have p12493_2 := h12493c.2.2.1
                              have p12493_3 := h12493c.2.2.2
                              linarith only [h12490, hlam, p12493_0]
                            · have p12493_0 := h12493c.1
                              have p12493_1 := h12493c.2.1
                              have p12493_2 := h12493c.2.2.1
                              have p12493_3 := h12493c.2.2.2
                              linarith only [h12491, hlam, p12493_1]
                            · have p12493_0 := h12493c.1
                              have p12493_1 := h12493c.2.1
                              have p12493_2 := h12493c.2.2.1
                              have p12493_3 := h12493c.2.2.2
                              linarith only [hlam, p12493_0]
                          · linarith only [h12488, h12492, h8886, h8887, hc23, hc45, hlam, hphi, ht34]
                        · linarith only [h0, h12382, h12384, h12491, hc01, hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h12533 | h12533
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h12534 | h12534
                          · rcases h2bigk with h12535c | h12535c | h12535c | h12535c | h12535c | h12535c | h12535c | h12535c | h12535c | h12535c | h12535c | h12535c | h12535c | h12535c | h12535c | h12535c | h12535c | h12535c | h12535c | h12535c | h12535c | h12535c | h12535c | h12535c | h12535c
                            · have p12535_0 := h12535c.1
                              have p12535_1 := h12535c.2.1
                              have p12535_2 := h12535c.2.2.1
                              have p12535_3 := h12535c.2.2.2
                              linarith only [hlam, p12535_0]
                            · have p12535_0 := h12535c.1
                              have p12535_1 := h12535c.2.1
                              have p12535_2 := h12535c.2.2.1
                              have p12535_3 := h12535c.2.2.2
                              linarith only [h0, hlam, p12535_0]
                            · have p12535_0 := h12535c.1
                              have p12535_1 := h12535c.2.1
                              have p12535_2 := h12535c.2.2.1
                              have p12535_3 := h12535c.2.2.2
                              linarith only [h0, h12384, h12488, hc23, hc34, hlam, hphi, p12535_1]
                            · have p12535_0 := h12535c.1
                              have p12535_1 := h12535c.2.1
                              have p12535_2 := h12535c.2.2.1
                              have p12535_3 := h12535c.2.2.2
                              linarith only [h8887, hlam, p12535_0]
                            · have p12535_0 := h12535c.1
                              have p12535_1 := h12535c.2.1
                              have p12535_2 := h12535c.2.2.1
                              have p12535_3 := h12535c.2.2.2
                              linarith only [h0, h12384, h12488, h12490, hc23, hc34, hlam, hphi, p12535_1]
                            · have p12535_0 := h12535c.1
                              have p12535_1 := h12535c.2.1
                              have p12535_2 := h12535c.2.2.1
                              have p12535_3 := h12535c.2.2.2
                              linarith only [h12384, h12488, hc02, hc34, hlam, hphi, ht23, p12535_1]
                            · have p12535_0 := h12535c.1
                              have p12535_1 := h12535c.2.1
                              have p12535_2 := h12535c.2.2.1
                              have p12535_3 := h12535c.2.2.2
                              linarith only [hlam, p12535_0]
                            · have p12535_0 := h12535c.1
                              have p12535_1 := h12535c.2.1
                              have p12535_2 := h12535c.2.2.1
                              have p12535_3 := h12535c.2.2.2
                              linarith only [h12384, h12488, hc23, hc34, hlam, hphi, p12535_1]
                            · have p12535_0 := h12535c.1
                              have p12535_1 := h12535c.2.1
                              have p12535_2 := h12535c.2.2.1
                              have p12535_3 := h12535c.2.2.2
                              linarith only [h12384, hlam, p12535_0]
                            · have p12535_0 := h12535c.1
                              have p12535_1 := h12535c.2.1
                              have p12535_2 := h12535c.2.2.1
                              have p12535_3 := h12535c.2.2.2
                              linarith only [h12384, h12488, h12490, hc23, hc34, hlam, hphi, p12535_1]
                            · have p12535_0 := h12535c.1
                              have p12535_1 := h12535c.2.1
                              have p12535_2 := h12535c.2.2.1
                              have p12535_3 := h12535c.2.2.2
                              linarith only [h8886, hlam, p12535_0]
                            · have p12535_0 := h12535c.1
                              have p12535_1 := h12535c.2.1
                              have p12535_2 := h12535c.2.2.1
                              have p12535_3 := h12535c.2.2.2
                              linarith only [h12383, hlam, p12535_0]
                            · have p12535_0 := h12535c.1
                              have p12535_1 := h12535c.2.1
                              have p12535_2 := h12535c.2.2.1
                              have p12535_3 := h12535c.2.2.2
                              linarith only [hlam, p12535_0]
                            · have p12535_0 := h12535c.1
                              have p12535_1 := h12535c.2.1
                              have p12535_2 := h12535c.2.2.1
                              have p12535_3 := h12535c.2.2.2
                              linarith only [h12488, hlam, p12535_1]
                            · have p12535_0 := h12535c.1
                              have p12535_1 := h12535c.2.1
                              have p12535_2 := h12535c.2.2.1
                              have p12535_3 := h12535c.2.2.2
                              linarith only [h12490, hlam, p12535_1]
                            · have p12535_0 := h12535c.1
                              have p12535_1 := h12535c.2.1
                              have p12535_2 := h12535c.2.2.1
                              have p12535_3 := h12535c.2.2.2
                              linarith only [h12379, h12488, h12490, hc23, hc34, hlam, hphi, p12535_1]
                            · have p12535_0 := h12535c.1
                              have p12535_1 := h12535c.2.1
                              have p12535_2 := h12535c.2.2.1
                              have p12535_3 := h12535c.2.2.2
                              linarith only [h0, h12488, hc01, hc34, hlam, hphi, ht12, ht23, p12535_1]
                            · have p12535_0 := h12535c.1
                              have p12535_1 := h12535c.2.1
                              have p12535_2 := h12535c.2.2.1
                              have p12535_3 := h12535c.2.2.2
                              rcases p12535_3 (m.d 0 2) (by simp) with h12553 | h12553
                              · linarith only [h12553, h8887, hlam]
                              · linarith only [h12553, h8886, hlam]
                            · have p12535_0 := h12535c.1
                              have p12535_1 := h12535c.2.1
                              have p12535_2 := h12535c.2.2.1
                              have p12535_3 := h12535c.2.2.2
                              linarith only [hlam, p12535_0]
                            · have p12535_0 := h12535c.1
                              have p12535_1 := h12535c.2.1
                              have p12535_2 := h12535c.2.2.1
                              have p12535_3 := h12535c.2.2.2
                              rcases p12535_3 (m.d 0 2) (by simp) with h12557 | h12557
                              · linarith only [h12557, h8887, hlam]
                              · linarith only [h12379, h12557, hlam]
                            · have p12535_0 := h12535c.1
                              have p12535_1 := h12535c.2.1
                              have p12535_2 := h12535c.2.2.1
                              have p12535_3 := h12535c.2.2.2
                              linarith only [h12379, hlam, p12535_0]
                            · have p12535_0 := h12535c.1
                              have p12535_1 := h12535c.2.1
                              have p12535_2 := h12535c.2.2.1
                              have p12535_3 := h12535c.2.2.2
                              linarith only [h12484, hlam, p12535_0]
                            · have p12535_0 := h12535c.1
                              have p12535_1 := h12535c.2.1
                              have p12535_2 := h12535c.2.2.1
                              have p12535_3 := h12535c.2.2.2
                              linarith only [h12379, h12488, h8887, hc23, hc34, hlam, hphi, p12535_1]
                            · have p12535_0 := h12535c.1
                              have p12535_1 := h12535c.2.1
                              have p12535_2 := h12535c.2.2.1
                              have p12535_3 := h12535c.2.2.2
                              linarith only [h12533, hlam, p12535_1]
                            · have p12535_0 := h12535c.1
                              have p12535_1 := h12535c.2.1
                              have p12535_2 := h12535c.2.2.1
                              have p12535_3 := h12535c.2.2.2
                              linarith only [hlam, p12535_0]
                          · linarith only [h0, h12384, h12488, h12534, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                        · linarith only [h0, h12384, h12533, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                  · linarith only [h0, h12379, h12382, h12384, h12487, h6874, hc01, hc24, hlam, hphi, ht12]
              · linarith only [h0, h12379, h12484, hlam]
          · linarith only [h0, h12383, h8886, hlam]
        · linarith only [h12379, h12382, h8887, hlam]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h12571 | h12571
      · linarith only [h12571, h8886, h8887, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h12573 | h12573
        · rcases m.htr 1 2 3 (by decide) (by decide) with h12574 | h12574
          · rcases m.htr 1 2 4 (by decide) (by decide) with h12575 | h12575
            · rcases m.htr 1 2 5 (by decide) (by decide) with h12576 | h12576
              · rcases m.htr 1 3 4 (by decide) (by decide) with h12577 | h12577
                · rcases m.htr 1 4 5 (by decide) (by decide) with h12578 | h12578
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h12579 | h12579
                    · linarith only [h12571, h12575, h12579, h8886, h8887, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h12581 | h12581
                      · linarith only [h12574, h12577, h12579, h12581, h8886, h8887, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h12583 | h12583
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h12584 | h12584
                          · rcases h2bigk with h12585c | h12585c | h12585c | h12585c | h12585c | h12585c | h12585c | h12585c | h12585c | h12585c | h12585c | h12585c | h12585c | h12585c | h12585c | h12585c | h12585c | h12585c | h12585c | h12585c | h12585c | h12585c | h12585c | h12585c | h12585c
                            · have p12585_0 := h12585c.1
                              have p12585_1 := h12585c.2.1
                              have p12585_2 := h12585c.2.2.1
                              have p12585_3 := h12585c.2.2.2
                              linarith only [hlam, p12585_0]
                            · have p12585_0 := h12585c.1
                              have p12585_1 := h12585c.2.1
                              have p12585_2 := h12585c.2.2.1
                              have p12585_3 := h12585c.2.2.2
                              linarith only [h0, hlam, p12585_0]
                            · have p12585_0 := h12585c.1
                              have p12585_1 := h12585c.2.1
                              have p12585_2 := h12585c.2.2.1
                              have p12585_3 := h12585c.2.2.2
                              linarith only [h12379, h12574, h12577, h12579, h12583, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p12585_1]
                            · have p12585_0 := h12585c.1
                              have p12585_1 := h12585c.2.1
                              have p12585_2 := h12585c.2.2.1
                              have p12585_3 := h12585c.2.2.2
                              linarith only [h8887, hlam, p12585_0]
                            · have p12585_0 := h12585c.1
                              have p12585_1 := h12585c.2.1
                              have p12585_2 := h12585c.2.2.1
                              have p12585_3 := h12585c.2.2.2
                              linarith only [h12379, hlam, p12585_0]
                            · have p12585_0 := h12585c.1
                              have p12585_1 := h12585c.2.1
                              have p12585_2 := h12585c.2.2.1
                              have p12585_3 := h12585c.2.2.2
                              rcases p12585_3 (m.d 0 2) (by simp) with h12591 | h12591
                              · linarith only [h0, h12591, hlam]
                              · rcases p12585_3 (m.d 1 2) (by simp) with h12593 | h12593
                                · rcases p12585_3 (m.d 2 3) (by simp) with h12594 | h12594
                                  · linarith only [h12574, h12594, hlam]
                                  · rcases p12585_3 (m.d 2 4) (by simp) with h12596 | h12596
                                    · linarith only [h12575, h12596, hlam]
                                    · linarith only [h12596, h8887, hlam]
                                · linarith only [h0, h12593, hlam]
                            · have p12585_0 := h12585c.1
                              have p12585_1 := h12585c.2.1
                              have p12585_2 := h12585c.2.2.1
                              have p12585_3 := h12585c.2.2.2
                              linarith only [hlam, p12585_0]
                            · have p12585_0 := h12585c.1
                              have p12585_1 := h12585c.2.1
                              have p12585_2 := h12585c.2.2.1
                              have p12585_3 := h12585c.2.2.2
                              linarith only [h12379, h12574, h12577, h12579, h12583, h8886, hlam, p12585_2]
                            · have p12585_0 := h12585c.1
                              have p12585_1 := h12585c.2.1
                              have p12585_2 := h12585c.2.2.1
                              have p12585_3 := h12585c.2.2.2
                              linarith only [h12379, h12583, h8886, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p12585_1]
                            · have p12585_0 := h12585c.1
                              have p12585_1 := h12585c.2.1
                              have p12585_2 := h12585c.2.2.1
                              have p12585_3 := h12585c.2.2.2
                              linarith only [h12379, h8886, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p12585_1]
                            · have p12585_0 := h12585c.1
                              have p12585_1 := h12585c.2.1
                              have p12585_2 := h12585c.2.2.1
                              have p12585_3 := h12585c.2.2.2
                              linarith only [h8886, hlam, p12585_0]
                            · have p12585_0 := h12585c.1
                              have p12585_1 := h12585c.2.1
                              have p12585_2 := h12585c.2.2.1
                              have p12585_3 := h12585c.2.2.2
                              linarith only [h12574, hlam, p12585_0]
                            · have p12585_0 := h12585c.1
                              have p12585_1 := h12585c.2.1
                              have p12585_2 := h12585c.2.2.1
                              have p12585_3 := h12585c.2.2.2
                              linarith only [hlam, p12585_0]
                            · have p12585_0 := h12585c.1
                              have p12585_1 := h12585c.2.1
                              have p12585_2 := h12585c.2.2.1
                              have p12585_3 := h12585c.2.2.2
                              linarith only [h12579, hlam, p12585_1]
                            · have p12585_0 := h12585c.1
                              have p12585_1 := h12585c.2.1
                              have p12585_2 := h12585c.2.2.1
                              have p12585_3 := h12585c.2.2.2
                              linarith only [h12581, hlam, p12585_1]
                            · have p12585_0 := h12585c.1
                              have p12585_1 := h12585c.2.1
                              have p12585_2 := h12585c.2.2.1
                              have p12585_3 := h12585c.2.2.2
                              linarith only [h12575, h8886, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p12585_1]
                            · have p12585_0 := h12585c.1
                              have p12585_1 := h12585c.2.1
                              have p12585_2 := h12585c.2.2.1
                              have p12585_3 := h12585c.2.2.2
                              linarith only [h12575, hlam, p12585_0]
                            · have p12585_0 := h12585c.1
                              have p12585_1 := h12585c.2.1
                              have p12585_2 := h12585c.2.2.1
                              have p12585_3 := h12585c.2.2.2
                              rcases p12585_3 (m.d 0 2) (by simp) with h12611 | h12611
                              · linarith only [h12611, h8887, hlam]
                              · linarith only [h12611, h8886, hlam]
                            · have p12585_0 := h12585c.1
                              have p12585_1 := h12585c.2.1
                              have p12585_2 := h12585c.2.2.1
                              have p12585_3 := h12585c.2.2.2
                              linarith only [hlam, p12585_0]
                            · have p12585_0 := h12585c.1
                              have p12585_1 := h12585c.2.1
                              have p12585_2 := h12585c.2.2.1
                              have p12585_3 := h12585c.2.2.2
                              linarith only [h12379, h12574, h12577, h12579, h8886, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p12585_1]
                            · have p12585_0 := h12585c.1
                              have p12585_1 := h12585c.2.1
                              have p12585_2 := h12585c.2.2.1
                              have p12585_3 := h12585c.2.2.2
                              linarith only [h12581, h8886, hc23, hc35, hlam, hphi, p12585_1]
                            · have p12585_0 := h12585c.1
                              have p12585_1 := h12585c.2.1
                              have p12585_2 := h12585c.2.2.1
                              have p12585_3 := h12585c.2.2.2
                              linarith only [h12576, hlam, p12585_0]
                            · have p12585_0 := h12585c.1
                              have p12585_1 := h12585c.2.1
                              have p12585_2 := h12585c.2.2.1
                              have p12585_3 := h12585c.2.2.2
                              rcases p12585_3 (m.d 0 2) (by simp) with h12618 | h12618
                              · linarith only [h12379, h12618, hlam]
                              · linarith only [h12618, h8886, hlam]
                            · have p12585_0 := h12585c.1
                              have p12585_1 := h12585c.2.1
                              have p12585_2 := h12585c.2.2.1
                              have p12585_3 := h12585c.2.2.2
                              linarith only [h12583, hlam, p12585_1]
                            · have p12585_0 := h12585c.1
                              have p12585_1 := h12585c.2.1
                              have p12585_2 := h12585c.2.2.1
                              have p12585_3 := h12585c.2.2.2
                              linarith only [hlam, p12585_0]
                          · linarith only [h12579, h12584, h8886, h8887, hc23, hc45, hlam, hphi, ht34]
                        · linarith only [h12573, h12583, h8886, h8887, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                  · linarith only [h12571, h12573, h12574, h12577, h12578, h6874, hc01, hc12, hlam, hphi]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h12626 | h12626
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h12627 | h12627
                    · linarith only [h12379, h12577, h12627, h8886, hc13, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h12629 | h12629
                      · linarith only [h12575, h12629, h8886, h8887, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h12631 | h12631
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h12632 | h12632
                          · rcases h2bigk with h12633c | h12633c | h12633c | h12633c | h12633c | h12633c | h12633c | h12633c | h12633c | h12633c | h12633c | h12633c | h12633c | h12633c | h12633c | h12633c | h12633c | h12633c | h12633c | h12633c | h12633c | h12633c | h12633c | h12633c | h12633c
                            · have p12633_0 := h12633c.1
                              have p12633_1 := h12633c.2.1
                              have p12633_2 := h12633c.2.2.1
                              have p12633_3 := h12633c.2.2.2
                              linarith only [hlam, p12633_0]
                            · have p12633_0 := h12633c.1
                              have p12633_1 := h12633c.2.1
                              have p12633_2 := h12633c.2.2.1
                              have p12633_3 := h12633c.2.2.2
                              linarith only [h0, hlam, p12633_0]
                            · have p12633_0 := h12633c.1
                              have p12633_1 := h12633c.2.1
                              have p12633_2 := h12633c.2.2.1
                              have p12633_3 := h12633c.2.2.2
                              linarith only [h12379, h12575, h12631, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p12633_1]
                            · have p12633_0 := h12633c.1
                              have p12633_1 := h12633c.2.1
                              have p12633_2 := h12633c.2.2.1
                              have p12633_3 := h12633c.2.2.2
                              linarith only [h8887, hlam, p12633_0]
                            · have p12633_0 := h12633c.1
                              have p12633_1 := h12633c.2.1
                              have p12633_2 := h12633c.2.2.1
                              have p12633_3 := h12633c.2.2.2
                              linarith only [h12379, hlam, p12633_0]
                            · have p12633_0 := h12633c.1
                              have p12633_1 := h12633c.2.1
                              have p12633_2 := h12633c.2.2.1
                              have p12633_3 := h12633c.2.2.2
                              rcases p12633_3 (m.d 0 2) (by simp) with h12639 | h12639
                              · linarith only [h0, h12639, hlam]
                              · rcases p12633_3 (m.d 1 2) (by simp) with h12641 | h12641
                                · rcases p12633_3 (m.d 2 3) (by simp) with h12642 | h12642
                                  · linarith only [h12574, h12642, hlam]
                                  · rcases p12633_3 (m.d 2 4) (by simp) with h12644 | h12644
                                    · linarith only [h12575, h12644, hlam]
                                    · linarith only [h12644, h8887, hlam]
                                · linarith only [h0, h12641, hlam]
                            · have p12633_0 := h12633c.1
                              have p12633_1 := h12633c.2.1
                              have p12633_2 := h12633c.2.2.1
                              have p12633_3 := h12633c.2.2.2
                              linarith only [hlam, p12633_0]
                            · have p12633_0 := h12633c.1
                              have p12633_1 := h12633c.2.1
                              have p12633_2 := h12633c.2.2.1
                              have p12633_3 := h12633c.2.2.2
                              linarith only [h12379, h12575, h12631, h8886, hlam, p12633_2]
                            · have p12633_0 := h12633c.1
                              have p12633_1 := h12633c.2.1
                              have p12633_2 := h12633c.2.2.1
                              have p12633_3 := h12633c.2.2.2
                              linarith only [h0, h12379, h12631, hc01, hc12, hlam, hphi, p12633_1]
                            · have p12633_0 := h12633c.1
                              have p12633_1 := h12633c.2.1
                              have p12633_2 := h12633c.2.2.1
                              have p12633_3 := h12633c.2.2.2
                              linarith only [h12379, h8886, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p12633_1]
                            · have p12633_0 := h12633c.1
                              have p12633_1 := h12633c.2.1
                              have p12633_2 := h12633c.2.2.1
                              have p12633_3 := h12633c.2.2.2
                              linarith only [h8886, hlam, p12633_0]
                            · have p12633_0 := h12633c.1
                              have p12633_1 := h12633c.2.1
                              have p12633_2 := h12633c.2.2.1
                              have p12633_3 := h12633c.2.2.2
                              linarith only [h12574, hlam, p12633_0]
                            · have p12633_0 := h12633c.1
                              have p12633_1 := h12633c.2.1
                              have p12633_2 := h12633c.2.2.1
                              have p12633_3 := h12633c.2.2.2
                              linarith only [hlam, p12633_0]
                            · have p12633_0 := h12633c.1
                              have p12633_1 := h12633c.2.1
                              have p12633_2 := h12633c.2.2.1
                              have p12633_3 := h12633c.2.2.2
                              linarith only [h12627, hlam, p12633_1]
                            · have p12633_0 := h12633c.1
                              have p12633_1 := h12633c.2.1
                              have p12633_2 := h12633c.2.2.1
                              have p12633_3 := h12633c.2.2.2
                              linarith only [h12629, hlam, p12633_1]
                            · have p12633_0 := h12633c.1
                              have p12633_1 := h12633c.2.1
                              have p12633_2 := h12633c.2.2.1
                              have p12633_3 := h12633c.2.2.2
                              linarith only [h12575, h8886, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p12633_1]
                            · have p12633_0 := h12633c.1
                              have p12633_1 := h12633c.2.1
                              have p12633_2 := h12633c.2.2.1
                              have p12633_3 := h12633c.2.2.2
                              linarith only [h12575, hlam, p12633_0]
                            · have p12633_0 := h12633c.1
                              have p12633_1 := h12633c.2.1
                              have p12633_2 := h12633c.2.2.1
                              have p12633_3 := h12633c.2.2.2
                              rcases p12633_3 (m.d 0 2) (by simp) with h12659 | h12659
                              · linarith only [h12659, h8887, hlam]
                              · linarith only [h12659, h8886, hlam]
                            · have p12633_0 := h12633c.1
                              have p12633_1 := h12633c.2.1
                              have p12633_2 := h12633c.2.2.1
                              have p12633_3 := h12633c.2.2.2
                              linarith only [hlam, p12633_0]
                            · have p12633_0 := h12633c.1
                              have p12633_1 := h12633c.2.1
                              have p12633_2 := h12633c.2.2.1
                              have p12633_3 := h12633c.2.2.2
                              linarith only [h12379, h12575, h8886, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p12633_1]
                            · have p12633_0 := h12633c.1
                              have p12633_1 := h12633c.2.1
                              have p12633_2 := h12633c.2.2.1
                              have p12633_3 := h12633c.2.2.2
                              linarith only [h12629, h8886, hc23, hc35, hlam, hphi, p12633_1]
                            · have p12633_0 := h12633c.1
                              have p12633_1 := h12633c.2.1
                              have p12633_2 := h12633c.2.2.1
                              have p12633_3 := h12633c.2.2.2
                              linarith only [h12576, hlam, p12633_0]
                            · have p12633_0 := h12633c.1
                              have p12633_1 := h12633c.2.1
                              have p12633_2 := h12633c.2.2.1
                              have p12633_3 := h12633c.2.2.2
                              rcases p12633_3 (m.d 0 2) (by simp) with h12666 | h12666
                              · linarith only [h12379, h12666, hlam]
                              · linarith only [h12666, h8886, hlam]
                            · have p12633_0 := h12633c.1
                              have p12633_1 := h12633c.2.1
                              have p12633_2 := h12633c.2.2.1
                              have p12633_3 := h12633c.2.2.2
                              linarith only [h12631, hlam, p12633_1]
                            · have p12633_0 := h12633c.1
                              have p12633_1 := h12633c.2.1
                              have p12633_2 := h12633c.2.2.1
                              have p12633_3 := h12633c.2.2.2
                              linarith only [hlam, p12633_0]
                          · linarith only [h12573, h12577, h12632, h6874, hlam]
                        · linarith only [h12573, h12631, h8887, hlam]
                  · linarith only [h12573, h12626, h6874, h8887, hc01, hc24, hlam, hphi, ht12]
              · linarith only [h12575, h12576, h8886, h8887, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h12675 | h12675
              · linarith only [h12379, h12575, h12675, h8886, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h12677 | h12677
                · linarith only [h12574, h12575, h12677, hlam]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h12679 | h12679
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h12680 | h12680
                    · linarith only [h0, h12675, h12677, h12679, h12680, h8886, hlam]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h12682 | h12682
                      · linarith only [h0, h12675, h12682, h8886, hlam]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h12684 | h12684
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h12685 | h12685
                          · rcases h2bigk with h12686c | h12686c | h12686c | h12686c | h12686c | h12686c | h12686c | h12686c | h12686c | h12686c | h12686c | h12686c | h12686c | h12686c | h12686c | h12686c | h12686c | h12686c | h12686c | h12686c | h12686c | h12686c | h12686c | h12686c | h12686c
                            · have p12686_0 := h12686c.1
                              have p12686_1 := h12686c.2.1
                              have p12686_2 := h12686c.2.2.1
                              have p12686_3 := h12686c.2.2.2
                              linarith only [hlam, p12686_0]
                            · have p12686_0 := h12686c.1
                              have p12686_1 := h12686c.2.1
                              have p12686_2 := h12686c.2.2.1
                              have p12686_3 := h12686c.2.2.2
                              linarith only [h0, hlam, p12686_0]
                            · have p12686_0 := h12686c.1
                              have p12686_1 := h12686c.2.1
                              have p12686_2 := h12686c.2.2.1
                              have p12686_3 := h12686c.2.2.2
                              linarith only [h0, h12675, h12680, h12684, hc23, hc34, hlam, hphi, p12686_1]
                            · have p12686_0 := h12686c.1
                              have p12686_1 := h12686c.2.1
                              have p12686_2 := h12686c.2.2.1
                              have p12686_3 := h12686c.2.2.2
                              linarith only [h8887, hlam, p12686_0]
                            · have p12686_0 := h12686c.1
                              have p12686_1 := h12686c.2.1
                              have p12686_2 := h12686c.2.2.1
                              have p12686_3 := h12686c.2.2.2
                              linarith only [h12379, hlam, p12686_0]
                            · have p12686_0 := h12686c.1
                              have p12686_1 := h12686c.2.1
                              have p12686_2 := h12686c.2.2.1
                              have p12686_3 := h12686c.2.2.2
                              linarith only [h12675, h12684, hc02, hc24, hlam, hphi, p12686_1]
                            · have p12686_0 := h12686c.1
                              have p12686_1 := h12686c.2.1
                              have p12686_2 := h12686c.2.2.1
                              have p12686_3 := h12686c.2.2.2
                              linarith only [hlam, p12686_0]
                            · have p12686_0 := h12686c.1
                              have p12686_1 := h12686c.2.1
                              have p12686_2 := h12686c.2.2.1
                              have p12686_3 := h12686c.2.2.2
                              linarith only [h12675, h12680, h12684, hc23, hc34, hlam, hphi, p12686_1]
                            · have p12686_0 := h12686c.1
                              have p12686_1 := h12686c.2.1
                              have p12686_2 := h12686c.2.2.1
                              have p12686_3 := h12686c.2.2.2
                              linarith only [h12575, hlam, p12686_0]
                            · have p12686_0 := h12686c.1
                              have p12686_1 := h12686c.2.1
                              have p12686_2 := h12686c.2.2.1
                              have p12686_3 := h12686c.2.2.2
                              linarith only [h12675, hlam, p12686_0]
                            · have p12686_0 := h12686c.1
                              have p12686_1 := h12686c.2.1
                              have p12686_2 := h12686c.2.2.1
                              have p12686_3 := h12686c.2.2.2
                              linarith only [h8886, hlam, p12686_0]
                            · have p12686_0 := h12686c.1
                              have p12686_1 := h12686c.2.1
                              have p12686_2 := h12686c.2.2.1
                              have p12686_3 := h12686c.2.2.2
                              linarith only [h12574, hlam, p12686_0]
                            · have p12686_0 := h12686c.1
                              have p12686_1 := h12686c.2.1
                              have p12686_2 := h12686c.2.2.1
                              have p12686_3 := h12686c.2.2.2
                              linarith only [hlam, p12686_0]
                            · have p12686_0 := h12686c.1
                              have p12686_1 := h12686c.2.1
                              have p12686_2 := h12686c.2.2.1
                              have p12686_3 := h12686c.2.2.2
                              linarith only [h12680, hlam, p12686_1]
                            · have p12686_0 := h12686c.1
                              have p12686_1 := h12686c.2.1
                              have p12686_2 := h12686c.2.2.1
                              have p12686_3 := h12686c.2.2.2
                              linarith only [h12682, hlam, p12686_1]
                            · have p12686_0 := h12686c.1
                              have p12686_1 := h12686c.2.1
                              have p12686_2 := h12686c.2.2.1
                              have p12686_3 := h12686c.2.2.2
                              linarith only [h12680, h8886, hc23, hc34, hlam, hphi, p12686_1]
                            · have p12686_0 := h12686c.1
                              have p12686_1 := h12686c.2.1
                              have p12686_2 := h12686c.2.2.1
                              have p12686_3 := h12686c.2.2.2
                              linarith only [h0, h12680, hc01, hc34, hlam, hphi, ht12, ht23, p12686_1]
                            · have p12686_0 := h12686c.1
                              have p12686_1 := h12686c.2.1
                              have p12686_2 := h12686c.2.2.1
                              have p12686_3 := h12686c.2.2.2
                              rcases p12686_3 (m.d 0 2) (by simp) with h12704 | h12704
                              · linarith only [h12704, h8887, hlam]
                              · linarith only [h12704, h8886, hlam]
                            · have p12686_0 := h12686c.1
                              have p12686_1 := h12686c.2.1
                              have p12686_2 := h12686c.2.2.1
                              have p12686_3 := h12686c.2.2.2
                              linarith only [hlam, p12686_0]
                            · have p12686_0 := h12686c.1
                              have p12686_1 := h12686c.2.1
                              have p12686_2 := h12686c.2.2.1
                              have p12686_3 := h12686c.2.2.2
                              linarith only [h12379, h12680, h8886, hc23, hc34, hlam, hphi, p12686_1]
                            · have p12686_0 := h12686c.1
                              have p12686_1 := h12686c.2.1
                              have p12686_2 := h12686c.2.2.1
                              have p12686_3 := h12686c.2.2.2
                              linarith only [h12682, h8886, hc23, hc35, hlam, hphi, p12686_1]
                            · have p12686_0 := h12686c.1
                              have p12686_1 := h12686c.2.1
                              have p12686_2 := h12686c.2.2.1
                              have p12686_3 := h12686c.2.2.2
                              linarith only [h0, h12682, hc01, hc35, hlam, hphi, ht12, ht23, p12686_1]
                            · have p12686_0 := h12686c.1
                              have p12686_1 := h12686c.2.1
                              have p12686_2 := h12686c.2.2.1
                              have p12686_3 := h12686c.2.2.2
                              rcases p12686_3 (m.d 0 2) (by simp) with h12711 | h12711
                              · linarith only [h12379, h12711, hlam]
                              · linarith only [h12711, h8886, hlam]
                            · have p12686_0 := h12686c.1
                              have p12686_1 := h12686c.2.1
                              have p12686_2 := h12686c.2.2.1
                              have p12686_3 := h12686c.2.2.2
                              linarith only [h12684, hlam, p12686_1]
                            · have p12686_0 := h12686c.1
                              have p12686_1 := h12686c.2.1
                              have p12686_2 := h12686c.2.2.1
                              have p12686_3 := h12686c.2.2.2
                              linarith only [hlam, p12686_0]
                          · linarith only [h12573, h12575, h12680, h12685, h6874, hlam]
                        · linarith only [h12573, h12575, h12684, h6874, hlam]
                  · linarith only [h12573, h12679, h6874, hlam]
          · linarith only [h0, h12574, h8886, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h12720 | h12720
          · rcases m.htr 1 2 4 (by decide) (by decide) with h12721 | h12721
            · rcases m.htr 1 2 5 (by decide) (by decide) with h12722 | h12722
              · rcases m.htr 1 3 4 (by decide) (by decide) with h12723 | h12723
                · rcases m.htr 1 4 5 (by decide) (by decide) with h12724 | h12724
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h12725 | h12725
                    · linarith only [h12571, h12725, h8886, h8887, hlam]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h12727 | h12727
                      · linarith only [h12573, h12720, h12723, h12724, h12727, h8886, h8887, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h12729 | h12729
                        · linarith only [h12573, h12725, h12729, h8886, h8887, hc23, hc34, hlam, hphi]
                        · linarith only [h12720, h12723, h12724, h12729, h8886, h8887, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                  · linarith only [h12721, h12724, h8886, h8887, hc23, hc45, hlam, hphi, ht34]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h12733 | h12733
                  · linarith only [h12573, h12723, h12733, h8886, h8887, hc23, hc34, hlam, hphi]
                  · linarith only [h12721, h12733, h8886, h8887, hc23, hc45, hlam, hphi, ht34]
              · linarith only [h12721, h12722, h8886, h8887, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h12737 | h12737
              · linarith only [h12379, h12721, h12737, h8886, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h12739 | h12739
                · linarith only [h12720, h12721, h12739, hlam]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h12741 | h12741
                  · linarith only [h12573, h12739, h12741, h8886, h8887, hc23, hc34, hlam, hphi]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h12743 | h12743
                    · linarith only [h0, h12721, h12741, h12743, h8886, hc34, hc45, hlam, hphi]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h12745 | h12745
                      · linarith only [h0, h12737, h12745, h8886, hlam]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h12747 | h12747
                        · linarith only [h12741, h12743, h12747, h6874, hc01, hc34, hlam, hphi, ht12, ht23]
                        · linarith only [h12747, h8886, h8887, hc23, hc45, hlam, hphi, ht34]
          · linarith only [h0, h12720, h8886, h8887, hc01, hc24, hlam, hphi, ht12]

set_option maxHeartbeats 10432000 in
set_option maxHeartbeats 10432000 in
theorem r1l7_12_24_L_I_H_I_s7_x0 (m : N7Model)
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6874 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h8886 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
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
  exact r1l7_12_24_L_I_H_I_s8 m hb2 hb4 h0 h6874 h8886

end R2N4
