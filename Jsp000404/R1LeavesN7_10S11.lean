import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_10S10

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 13746000 in
set_option maxHeartbeats 13746000 in
theorem r1l7_12_24_L_I_H_I_s0 (m : N7Model)
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  rcases m.htr 0 1 4 (by decide) (by decide) with h1 | h1
  · exact r1l7_12_24_L_I_H_I_s1 m hb2 hb4 h0 h1
  · rcases m.htr 0 2 3 (by decide) (by decide) with h6152 | h6152
    · rcases m.htr 0 2 4 (by decide) (by decide) with h6153 | h6153
      · linarith only [h0, h1, h6153, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h6155 | h6155
        · rcases m.htr 0 3 4 (by decide) (by decide) with h6156 | h6156
          · linarith only [h0, h1, h6152, h6156, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h6158 | h6158
            · rcases m.htr 1 2 3 (by decide) (by decide) with h6159 | h6159
              · rcases m.htr 1 2 4 (by decide) (by decide) with h6160 | h6160
                · linarith only [h0, h6153, h6155, h6160, hc01, hc25, hlam, hphi, ht0b, ht5b]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h6162 | h6162
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h6163 | h6163
                    · linarith only [h0, h1, h6156, h6159, h6163, hlam]
                    · linarith only [h0, h1, h6159, h6163, hc23, hc34, hlam, hphi]
                  · linarith only [h0, h1, h6155, h6159, h6160, h6162, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
              · linarith only [h6152, h6153, h6159, hc12, hc24, hlam, hphi]
            · linarith only [h0, h1, h6155, h6158, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h6169 | h6169
          · linarith only [h0, h1, h6152, h6169, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h6171 | h6171
            · rcases m.htr 1 2 3 (by decide) (by decide) with h6172 | h6172
              · rcases m.htr 1 2 4 (by decide) (by decide) with h6173 | h6173
                · linarith only [h0, h1, h6153, h6173, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h6175 | h6175
                  · linarith only [h0, h6155, h6175, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h6177 | h6177
                    · linarith only [h0, h1, h6169, h6172, h6177, hlam]
                    · linarith only [h0, h1, h6172, h6177, hc23, hc34, hlam, hphi]
              · linarith only [h6152, h6155, h6172, hc12, hc25, hlam, hphi]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h6181 | h6181
              · linarith only [h0, h1, h6171, h6181, hc23, hc45, hlam, hphi, ht34]
              · linarith only [h0, h1, h6152, h6171, h6181, hc12, hc45, hlam, hphi, ht23, ht34]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h6184 | h6184
      · linarith only [h0, h1, h6184, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h6186 | h6186
        · rcases m.htr 0 3 4 (by decide) (by decide) with h6187 | h6187
          · rcases m.htr 0 4 5 (by decide) (by decide) with h6188 | h6188
            · rcases m.htr 1 2 3 (by decide) (by decide) with h6189 | h6189
              · linarith only [h0, h6152, h6186, h6189, hc01, hc25, hlam, hphi, ht0b, ht5b]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h6191 | h6191
                · linarith only [h0, h1, h6184, h6191, hlam]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h6193 | h6193
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h6194 | h6194
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h6195 | h6195
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h6196 | h6196
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h6197 | h6197
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h6198 | h6198
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h6199 | h6199
                              · rcases h2bigk with h6200c | h6200c | h6200c | h6200c | h6200c | h6200c | h6200c | h6200c | h6200c | h6200c | h6200c | h6200c | h6200c | h6200c | h6200c | h6200c | h6200c | h6200c | h6200c | h6200c | h6200c | h6200c | h6200c | h6200c | h6200c
                                · have p6200_0 := h6200c.1
                                  have p6200_1 := h6200c.2.1
                                  have p6200_2 := h6200c.2.2.1
                                  have p6200_3 := h6200c.2.2.2
                                  linarith only [hlam, p6200_0]
                                · have p6200_0 := h6200c.1
                                  have p6200_1 := h6200c.2.1
                                  have p6200_2 := h6200c.2.2.1
                                  have p6200_3 := h6200c.2.2.2
                                  linarith only [h0, h1, h6193, h6194, h6197, h6199, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p6200_1]
                                · have p6200_0 := h6200c.1
                                  have p6200_1 := h6200c.2.1
                                  have p6200_2 := h6200c.2.2.1
                                  have p6200_3 := h6200c.2.2.2
                                  linarith only [h6152, hlam, p6200_0]
                                · have p6200_0 := h6200c.1
                                  have p6200_1 := h6200c.2.1
                                  have p6200_2 := h6200c.2.2.1
                                  have p6200_3 := h6200c.2.2.2
                                  linarith only [h6184, hlam, p6200_0]
                                · have p6200_0 := h6200c.1
                                  have p6200_1 := h6200c.2.1
                                  have p6200_2 := h6200c.2.2.1
                                  have p6200_3 := h6200c.2.2.2
                                  rcases p6200_3 (m.d 0 2) (by simp) with h6205 | h6205
                                  · rcases p6200_3 (m.d 1 2) (by simp) with h6206 | h6206
                                    · linarith only [h0, h6206, hlam]
                                    · linarith only [h6193, h6206, hlam]
                                  · linarith only [h6205, hlam, p6200_0]
                                · have p6200_0 := h6200c.1
                                  have p6200_1 := h6200c.2.1
                                  have p6200_2 := h6200c.2.2.1
                                  have p6200_3 := h6200c.2.2.2
                                  linarith only [h0, hlam, p6200_1]
                                · have p6200_0 := h6200c.1
                                  have p6200_1 := h6200c.2.1
                                  have p6200_2 := h6200c.2.2.1
                                  have p6200_3 := h6200c.2.2.2
                                  linarith only [hlam, p6200_0]
                                · have p6200_0 := h6200c.1
                                  have p6200_1 := h6200c.2.1
                                  have p6200_2 := h6200c.2.2.1
                                  have p6200_3 := h6200c.2.2.2
                                  linarith only [h6189, hlam, p6200_0]
                                · have p6200_0 := h6200c.1
                                  have p6200_1 := h6200c.2.1
                                  have p6200_2 := h6200c.2.2.1
                                  have p6200_3 := h6200c.2.2.2
                                  linarith only [h6191, hlam, p6200_0]
                                · have p6200_0 := h6200c.1
                                  have p6200_1 := h6200c.2.1
                                  have p6200_2 := h6200c.2.2.1
                                  have p6200_3 := h6200c.2.2.2
                                  linarith only [h0, h1, h6189, h6194, h6197, h6199, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p6200_1]
                                · have p6200_0 := h6200c.1
                                  have p6200_1 := h6200c.2.1
                                  have p6200_2 := h6200c.2.2.1
                                  have p6200_3 := h6200c.2.2.2
                                  rcases p6200_3 (m.d 0 2) (by simp) with h6215 | h6215
                                  · linarith only [h6215, hlam, p6200_0]
                                  · rcases p6200_3 (m.d 1 2) (by simp) with h6217 | h6217
                                    · linarith only [h6189, h6217, hlam]
                                    · rcases p6200_3 (m.d 2 3) (by simp) with h6219 | h6219
                                      · rcases p6200_3 (m.d 2 4) (by simp) with h6220 | h6220
                                        · linarith only [h6196, h6220, hlam]
                                        · linarith only [h6184, h6220, hlam]
                                      · linarith only [h6219, hlam, p6200_0]
                                · have p6200_0 := h6200c.1
                                  have p6200_1 := h6200c.2.1
                                  have p6200_2 := h6200c.2.2.1
                                  have p6200_3 := h6200c.2.2.2
                                  rcases p6200_3 (m.d 0 2) (by simp) with h6224 | h6224
                                  · linarith only [h6152, h6224, hlam]
                                  · linarith only [h0, h6224, hlam]
                                · have p6200_0 := h6200c.1
                                  have p6200_1 := h6200c.2.1
                                  have p6200_2 := h6200c.2.2.1
                                  have p6200_3 := h6200c.2.2.2
                                  linarith only [hlam, p6200_0]
                                · have p6200_0 := h6200c.1
                                  have p6200_1 := h6200c.2.1
                                  have p6200_2 := h6200c.2.2.1
                                  have p6200_3 := h6200c.2.2.2
                                  linarith only [h1, h6191, hc01, hc23, hlam, hphi, ht12, p6200_1]
                                · have p6200_0 := h6200c.1
                                  have p6200_1 := h6200c.2.1
                                  have p6200_2 := h6200c.2.2.1
                                  have p6200_3 := h6200c.2.2.2
                                  linarith only [h0, h1, h6189, h6193, h6194, hlam, p6200_2]
                                · have p6200_0 := h6200c.1
                                  have p6200_1 := h6200c.2.1
                                  have p6200_2 := h6200c.2.2.1
                                  have p6200_3 := h6200c.2.2.2
                                  rcases p6200_3 (m.d 0 2) (by simp) with h6230 | h6230
                                  · linarith only [h6230, hlam, p6200_0]
                                  · rcases p6200_3 (m.d 1 2) (by simp) with h6232 | h6232
                                    · linarith only [h6191, h6232, hlam]
                                    · rcases p6200_3 (m.d 2 3) (by simp) with h6234 | h6234
                                      · rcases p6200_3 (m.d 2 4) (by simp) with h6235 | h6235
                                        · rcases p6200_3 (m.d 2 5) (by simp) with h6236 | h6236
                                          · linarith only [h6198, h6236, hlam]
                                          · rcases h4bigk with h6238c | h6238c | h6238c | h6238c | h6238c | h6238c | h6238c | h6238c | h6238c | h6238c | h6238c | h6238c | h6238c | h6238c | h6238c | h6238c | h6238c | h6238c | h6238c | h6238c | h6238c | h6238c | h6238c | h6238c | h6238c
                                            · have p6238_0 := h6238c.1
                                              have p6238_1 := h6238c.2.1
                                              have p6238_2 := h6238c.2.2.1
                                              have p6238_3 := h6238c.2.2.2
                                              linarith only [hlam, p6238_0]
                                            · have p6238_0 := h6238c.1
                                              have p6238_1 := h6238c.2.1
                                              have p6238_2 := h6238c.2.2.1
                                              have p6238_3 := h6238c.2.2.2
                                              linarith only [h1, hlam, p6238_1]
                                            · have p6238_0 := h6238c.1
                                              have p6238_1 := h6238c.2.1
                                              have p6238_2 := h6238c.2.2.1
                                              have p6238_3 := h6238c.2.2.2
                                              linarith only [h6184, hlam, p6238_1]
                                            · have p6238_0 := h6238c.1
                                              have p6238_1 := h6238c.2.1
                                              have p6238_2 := h6238c.2.2.1
                                              have p6238_3 := h6238c.2.2.2
                                              linarith only [h6187, h6199, hc03, hc45, hlam, hphi, ht0b, ht5b, p6238_1]
                                            · have p6238_0 := h6238c.1
                                              have p6238_1 := h6238c.2.1
                                              have p6238_2 := h6238c.2.2.1
                                              have p6238_3 := h6238c.2.2.2
                                              rcases p6238_3 (m.d 0 4) (by simp) with h6243 | h6243
                                              · rcases p6238_3 (m.d 1 4) (by simp) with h6244 | h6244
                                                · rcases p6238_3 (m.d 2 4) (by simp) with h6245 | h6245
                                                  · rcases p6238_3 (m.d 3 4) (by simp) with h6246 | h6246
                                                    · linarith only [h6187, h6246, hlam]
                                                    · linarith only [h6199, h6246, hlam]
                                                  · linarith only [h6198, h6245, hlam]
                                                · linarith only [h6195, h6244, hlam]
                                              · linarith only [h6243, hlam, p6238_0]
                                            · have p6238_0 := h6238c.1
                                              have p6238_1 := h6238c.2.1
                                              have p6238_2 := h6238c.2.2.1
                                              have p6238_3 := h6238c.2.2.2
                                              linarith only [h0, h1, h6189, h6193, h6194, h6197, h6199, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p6238_1]
                                            · have p6238_0 := h6238c.1
                                              have p6238_1 := h6238c.2.1
                                              have p6238_2 := h6238c.2.2.1
                                              have p6238_3 := h6238c.2.2.2
                                              linarith only [hlam, p6238_0]
                                            · have p6238_0 := h6238c.1
                                              have p6238_1 := h6238c.2.1
                                              have p6238_2 := h6238c.2.2.1
                                              have p6238_3 := h6238c.2.2.2
                                              linarith only [h6191, hlam, p6238_1]
                                            · have p6238_0 := h6238c.1
                                              have p6238_1 := h6238c.2.1
                                              have p6238_2 := h6238c.2.2.1
                                              have p6238_3 := h6238c.2.2.2
                                              linarith only [h6189, h6194, h6199, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p6238_1]
                                            · have p6238_0 := h6238c.1
                                              have p6238_1 := h6238c.2.1
                                              have p6238_2 := h6238c.2.2.1
                                              have p6238_3 := h6238c.2.2.2
                                              rcases p6238_3 (m.d 0 4) (by simp) with h6256 | h6256
                                              · linarith only [h1, h6256, hlam]
                                              · linarith only [h6188, h6256, hlam]
                                            · have p6238_0 := h6238c.1
                                              have p6238_1 := h6238c.2.1
                                              have p6238_2 := h6238c.2.2.1
                                              have p6238_3 := h6238c.2.2.2
                                              linarith only [h0, h1, h6193, h6196, h6197, h6199, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p6238_1]
                                            · have p6238_0 := h6238c.1
                                              have p6238_1 := h6238c.2.1
                                              have p6238_2 := h6238c.2.2.1
                                              have p6238_3 := h6238c.2.2.2
                                              linarith only [h0, h1, h6193, h6196, h6197, h6199, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p6238_1]
                                            · have p6238_0 := h6238c.1
                                              have p6238_1 := h6238c.2.1
                                              have p6238_2 := h6238c.2.2.1
                                              have p6238_3 := h6238c.2.2.2
                                              linarith only [hlam, p6238_0]
                                            · have p6238_0 := h6238c.1
                                              have p6238_1 := h6238c.2.1
                                              have p6238_2 := h6238c.2.2.1
                                              have p6238_3 := h6238c.2.2.2
                                              linarith only [h6196, h6199, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p6238_1]
                                            · have p6238_0 := h6238c.1
                                              have p6238_1 := h6238c.2.1
                                              have p6238_2 := h6238c.2.2.1
                                              have p6238_3 := h6238c.2.2.2
                                              rcases p6238_3 (m.d 0 4) (by simp) with h6263 | h6263
                                              · linarith only [h6184, h6263, hlam]
                                              · linarith only [h6188, h6263, hlam]
                                            · have p6238_0 := h6238c.1
                                              have p6238_1 := h6238c.2.1
                                              have p6238_2 := h6238c.2.2.1
                                              have p6238_3 := h6238c.2.2.2
                                              linarith only [h6187, hlam, p6238_0]
                                            · have p6238_0 := h6238c.1
                                              have p6238_1 := h6238c.2.1
                                              have p6238_2 := h6238c.2.2.1
                                              have p6238_3 := h6238c.2.2.2
                                              linarith only [h6194, hlam, p6238_0]
                                            · have p6238_0 := h6238c.1
                                              have p6238_1 := h6238c.2.1
                                              have p6238_2 := h6238c.2.2.1
                                              have p6238_3 := h6238c.2.2.2
                                              linarith only [h6196, hlam, p6238_0]
                                            · have p6238_0 := h6238c.1
                                              have p6238_1 := h6238c.2.1
                                              have p6238_2 := h6238c.2.2.1
                                              have p6238_3 := h6238c.2.2.2
                                              linarith only [hlam, p6238_0]
                                            · have p6238_0 := h6238c.1
                                              have p6238_1 := h6238c.2.1
                                              have p6238_2 := h6238c.2.2.1
                                              have p6238_3 := h6238c.2.2.2
                                              linarith only [h6152, h6187, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p6238_1]
                                            · have p6238_0 := h6238c.1
                                              have p6238_1 := h6238c.2.1
                                              have p6238_2 := h6238c.2.2.1
                                              have p6238_3 := h6238c.2.2.2
                                              linarith only [h6188, hlam, p6238_0]
                                            · have p6238_0 := h6238c.1
                                              have p6238_1 := h6238c.2.1
                                              have p6238_2 := h6238c.2.2.1
                                              have p6238_3 := h6238c.2.2.2
                                              linarith only [h6195, hlam, p6238_0]
                                            · have p6238_0 := h6238c.1
                                              have p6238_1 := h6238c.2.1
                                              have p6238_2 := h6238c.2.2.1
                                              have p6238_3 := h6238c.2.2.2
                                              linarith only [h6198, hlam, p6238_0]
                                            · have p6238_0 := h6238c.1
                                              have p6238_1 := h6238c.2.1
                                              have p6238_2 := h6238c.2.2.1
                                              have p6238_3 := h6238c.2.2.2
                                              linarith only [h6199, hlam, p6238_0]
                                            · have p6238_0 := h6238c.1
                                              have p6238_1 := h6238c.2.1
                                              have p6238_2 := h6238c.2.2.1
                                              have p6238_3 := h6238c.2.2.2
                                              linarith only [hlam, p6238_0]
                                        · linarith only [h6235, hlam, p6200_0]
                                      · linarith only [h6152, h6234, hlam]
                                · have p6200_0 := h6200c.1
                                  have p6200_1 := h6200c.2.1
                                  have p6200_2 := h6200c.2.2.1
                                  have p6200_3 := h6200c.2.2.2
                                  rcases p6200_3 (m.d 0 2) (by simp) with h6278 | h6278
                                  · linarith only [h6184, h6278, hlam]
                                  · linarith only [h0, h6278, hlam]
                                · have p6200_0 := h6200c.1
                                  have p6200_1 := h6200c.2.1
                                  have p6200_2 := h6200c.2.2.1
                                  have p6200_3 := h6200c.2.2.2
                                  linarith only [h6196, hlam, p6200_0]
                                · have p6200_0 := h6200c.1
                                  have p6200_1 := h6200c.2.1
                                  have p6200_2 := h6200c.2.2.1
                                  have p6200_3 := h6200c.2.2.2
                                  linarith only [hlam, p6200_0]
                                · have p6200_0 := h6200c.1
                                  have p6200_1 := h6200c.2.1
                                  have p6200_2 := h6200c.2.2.1
                                  have p6200_3 := h6200c.2.2.2
                                  linarith only [h0, h1, h6191, h6193, hlam, p6200_2]
                                · have p6200_0 := h6200c.1
                                  have p6200_1 := h6200c.2.1
                                  have p6200_2 := h6200c.2.2.1
                                  have p6200_3 := h6200c.2.2.2
                                  linarith only [h6186, hlam, p6200_0]
                                · have p6200_0 := h6200c.1
                                  have p6200_1 := h6200c.2.1
                                  have p6200_2 := h6200c.2.2.1
                                  have p6200_3 := h6200c.2.2.2
                                  linarith only [h6193, hlam, p6200_0]
                                · have p6200_0 := h6200c.1
                                  have p6200_1 := h6200c.2.1
                                  have p6200_2 := h6200c.2.2.1
                                  have p6200_3 := h6200c.2.2.2
                                  linarith only [h6197, hlam, p6200_0]
                                · have p6200_0 := h6200c.1
                                  have p6200_1 := h6200c.2.1
                                  have p6200_2 := h6200c.2.2.1
                                  have p6200_3 := h6200c.2.2.2
                                  linarith only [h6198, hlam, p6200_1]
                                · have p6200_0 := h6200c.1
                                  have p6200_1 := h6200c.2.1
                                  have p6200_2 := h6200c.2.2.1
                                  have p6200_3 := h6200c.2.2.2
                                  linarith only [hlam, p6200_0]
                              · linarith only [h0, h1, h6189, h6193, h6194, h6198, h6199, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                            · linarith only [h6184, h6188, h6198, hlam]
                          · linarith only [h0, h1, h6189, h6194, h6197, hc12, hc35, hlam, hphi, ht23]
                        · linarith only [h0, h1, h6189, h6193, h6194, h6196, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                      · linarith only [h0, h1, h6193, h6195, hc25, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b]
                    · linarith only [h0, h1, h6152, h6187, h6193, h6194, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
                  · linarith only [h0, h1, h6186, h6191, h6193, hc12, hc24, hlam, hphi]
            · linarith only [h0, h1, h6186, h6188, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h6297 | h6297
            · rcases m.htr 1 2 3 (by decide) (by decide) with h6298 | h6298
              · linarith only [h0, h1, h6152, h6298, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h6300 | h6300
                · linarith only [h0, h1, h6184, h6300, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h6302 | h6302
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h6303 | h6303
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h6304 | h6304
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h6305 | h6305
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h6306 | h6306
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h6307 | h6307
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h6308 | h6308
                              · rcases h2bigk with h6309c | h6309c | h6309c | h6309c | h6309c | h6309c | h6309c | h6309c | h6309c | h6309c | h6309c | h6309c | h6309c | h6309c | h6309c | h6309c | h6309c | h6309c | h6309c | h6309c | h6309c | h6309c | h6309c | h6309c | h6309c
                                · have p6309_0 := h6309c.1
                                  have p6309_1 := h6309c.2.1
                                  have p6309_2 := h6309c.2.2.1
                                  have p6309_3 := h6309c.2.2.2
                                  linarith only [hlam, p6309_0]
                                · have p6309_0 := h6309c.1
                                  have p6309_1 := h6309c.2.1
                                  have p6309_2 := h6309c.2.2.1
                                  have p6309_3 := h6309c.2.2.2
                                  linarith only [h6152, h6187, h6298, h6302, h6303, h6306, h6308, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p6309_1]
                                · have p6309_0 := h6309c.1
                                  have p6309_1 := h6309c.2.1
                                  have p6309_2 := h6309c.2.2.1
                                  have p6309_3 := h6309c.2.2.2
                                  linarith only [h6152, hlam, p6309_0]
                                · have p6309_0 := h6309c.1
                                  have p6309_1 := h6309c.2.1
                                  have p6309_2 := h6309c.2.2.1
                                  have p6309_3 := h6309c.2.2.2
                                  linarith only [h6184, hlam, p6309_0]
                                · have p6309_0 := h6309c.1
                                  have p6309_1 := h6309c.2.1
                                  have p6309_2 := h6309c.2.2.1
                                  have p6309_3 := h6309c.2.2.2
                                  linarith only [h6152, h6187, h6298, h6303, h6306, h6308, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p6309_1]
                                · have p6309_0 := h6309c.1
                                  have p6309_1 := h6309c.2.1
                                  have p6309_2 := h6309c.2.2.1
                                  have p6309_3 := h6309c.2.2.2
                                  linarith only [h0, hlam, p6309_1]
                                · have p6309_0 := h6309c.1
                                  have p6309_1 := h6309c.2.1
                                  have p6309_2 := h6309c.2.2.1
                                  have p6309_3 := h6309c.2.2.2
                                  linarith only [hlam, p6309_0]
                                · have p6309_0 := h6309c.1
                                  have p6309_1 := h6309c.2.1
                                  have p6309_2 := h6309c.2.2.1
                                  have p6309_3 := h6309c.2.2.2
                                  linarith only [h6298, hlam, p6309_0]
                                · have p6309_0 := h6309c.1
                                  have p6309_1 := h6309c.2.1
                                  have p6309_2 := h6309c.2.2.1
                                  have p6309_3 := h6309c.2.2.2
                                  linarith only [h6300, hlam, p6309_0]
                                · have p6309_0 := h6309c.1
                                  have p6309_1 := h6309c.2.1
                                  have p6309_2 := h6309c.2.2.1
                                  have p6309_3 := h6309c.2.2.2
                                  linarith only [h0, h6152, h6187, h6298, h6303, h6306, h6308, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p6309_1]
                                · have p6309_0 := h6309c.1
                                  have p6309_1 := h6309c.2.1
                                  have p6309_2 := h6309c.2.2.1
                                  have p6309_3 := h6309c.2.2.2
                                  rcases p6309_3 (m.d 0 2) (by simp) with h6320 | h6320
                                  · linarith only [h6320, hlam, p6309_0]
                                  · rcases p6309_3 (m.d 1 2) (by simp) with h6322 | h6322
                                    · linarith only [h6298, h6322, hlam]
                                    · rcases p6309_3 (m.d 2 3) (by simp) with h6324 | h6324
                                      · rcases p6309_3 (m.d 2 4) (by simp) with h6325 | h6325
                                        · linarith only [h6305, h6325, hlam]
                                        · linarith only [h6184, h6325, hlam]
                                      · linarith only [h6324, hlam, p6309_0]
                                · have p6309_0 := h6309c.1
                                  have p6309_1 := h6309c.2.1
                                  have p6309_2 := h6309c.2.2.1
                                  have p6309_3 := h6309c.2.2.2
                                  rcases p6309_3 (m.d 0 2) (by simp) with h6329 | h6329
                                  · linarith only [h6152, h6329, hlam]
                                  · linarith only [h0, h6329, hlam]
                                · have p6309_0 := h6309c.1
                                  have p6309_1 := h6309c.2.1
                                  have p6309_2 := h6309c.2.2.1
                                  have p6309_3 := h6309c.2.2.2
                                  linarith only [hlam, p6309_0]
                                · have p6309_0 := h6309c.1
                                  have p6309_1 := h6309c.2.1
                                  have p6309_2 := h6309c.2.2.1
                                  have p6309_3 := h6309c.2.2.2
                                  linarith only [h6184, hc02, hc23, hlam, hphi, p6309_1]
                                · have p6309_0 := h6309c.1
                                  have p6309_1 := h6309c.2.1
                                  have p6309_2 := h6309c.2.2.1
                                  have p6309_3 := h6309c.2.2.2
                                  linarith only [h0, h1, h6298, h6302, h6303, hlam, p6309_2]
                                · have p6309_0 := h6309c.1
                                  have p6309_1 := h6309c.2.1
                                  have p6309_2 := h6309c.2.2.1
                                  have p6309_3 := h6309c.2.2.2
                                  rcases p6309_3 (m.d 0 2) (by simp) with h6335 | h6335
                                  · linarith only [h6335, hlam, p6309_0]
                                  · rcases p6309_3 (m.d 1 2) (by simp) with h6337 | h6337
                                    · linarith only [h6300, h6337, hlam]
                                    · rcases p6309_3 (m.d 2 3) (by simp) with h6339 | h6339
                                      · rcases p6309_3 (m.d 2 4) (by simp) with h6340 | h6340
                                        · rcases p6309_3 (m.d 2 5) (by simp) with h6341 | h6341
                                          · linarith only [h6307, h6341, hlam]
                                          · rcases h4bigk with h6343c | h6343c | h6343c | h6343c | h6343c | h6343c | h6343c | h6343c | h6343c | h6343c | h6343c | h6343c | h6343c | h6343c | h6343c | h6343c | h6343c | h6343c | h6343c | h6343c | h6343c | h6343c | h6343c | h6343c | h6343c
                                            · have p6343_0 := h6343c.1
                                              have p6343_1 := h6343c.2.1
                                              have p6343_2 := h6343c.2.2.1
                                              have p6343_3 := h6343c.2.2.2
                                              linarith only [hlam, p6343_0]
                                            · have p6343_0 := h6343c.1
                                              have p6343_1 := h6343c.2.1
                                              have p6343_2 := h6343c.2.2.1
                                              have p6343_3 := h6343c.2.2.2
                                              linarith only [h1, hlam, p6343_1]
                                            · have p6343_0 := h6343c.1
                                              have p6343_1 := h6343c.2.1
                                              have p6343_2 := h6343c.2.2.1
                                              have p6343_3 := h6343c.2.2.2
                                              linarith only [h6184, hlam, p6343_1]
                                            · have p6343_0 := h6343c.1
                                              have p6343_1 := h6343c.2.1
                                              have p6343_2 := h6343c.2.2.1
                                              have p6343_3 := h6343c.2.2.2
                                              linarith only [h6187, hlam, p6343_1]
                                            · have p6343_0 := h6343c.1
                                              have p6343_1 := h6343c.2.1
                                              have p6343_2 := h6343c.2.2.1
                                              have p6343_3 := h6343c.2.2.2
                                              linarith only [h6187, h6303, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p6343_1]
                                            · have p6343_0 := h6343c.1
                                              have p6343_1 := h6343c.2.1
                                              have p6343_2 := h6343c.2.2.1
                                              have p6343_3 := h6343c.2.2.2
                                              linarith only [h0, h1, h6302, h6306, h6308, hc14, hc45, hlam, hphi, ht01, ht0b, ht5b, p6343_1]
                                            · have p6343_0 := h6343c.1
                                              have p6343_1 := h6343c.2.1
                                              have p6343_2 := h6343c.2.2.1
                                              have p6343_3 := h6343c.2.2.2
                                              linarith only [hlam, p6343_0]
                                            · have p6343_0 := h6343c.1
                                              have p6343_1 := h6343c.2.1
                                              have p6343_2 := h6343c.2.2.1
                                              have p6343_3 := h6343c.2.2.2
                                              linarith only [h6300, hlam, p6343_1]
                                            · have p6343_0 := h6343c.1
                                              have p6343_1 := h6343c.2.1
                                              have p6343_2 := h6343c.2.2.1
                                              have p6343_3 := h6343c.2.2.2
                                              linarith only [h0, h6152, h6187, h6298, h6302, h6303, h6306, h6308, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p6343_1]
                                            · have p6343_0 := h6343c.1
                                              have p6343_1 := h6343c.2.1
                                              have p6343_2 := h6343c.2.2.1
                                              have p6343_3 := h6343c.2.2.2
                                              rcases p6343_3 (m.d 0 4) (by simp) with h6353 | h6353
                                              · linarith only [h1, h6353, hlam]
                                              · linarith only [h6297, h6353, hlam]
                                            · have p6343_0 := h6343c.1
                                              have p6343_1 := h6343c.2.1
                                              have p6343_2 := h6343c.2.2.1
                                              have p6343_3 := h6343c.2.2.2
                                              linarith only [h0, h1, h6302, h6305, h6306, h6308, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p6343_1]
                                            · have p6343_0 := h6343c.1
                                              have p6343_1 := h6343c.2.1
                                              have p6343_2 := h6343c.2.2.1
                                              have p6343_3 := h6343c.2.2.2
                                              linarith only [h0, h1, h6302, h6305, h6306, h6308, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p6343_1]
                                            · have p6343_0 := h6343c.1
                                              have p6343_1 := h6343c.2.1
                                              have p6343_2 := h6343c.2.2.1
                                              have p6343_3 := h6343c.2.2.2
                                              linarith only [hlam, p6343_0]
                                            · have p6343_0 := h6343c.1
                                              have p6343_1 := h6343c.2.1
                                              have p6343_2 := h6343c.2.2.1
                                              have p6343_3 := h6343c.2.2.2
                                              linarith only [h0, h6152, h6187, h6302, h6305, h6306, h6308, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p6343_1]
                                            · have p6343_0 := h6343c.1
                                              have p6343_1 := h6343c.2.1
                                              have p6343_2 := h6343c.2.2.1
                                              have p6343_3 := h6343c.2.2.2
                                              rcases p6343_3 (m.d 0 4) (by simp) with h6360 | h6360
                                              · linarith only [h6184, h6360, hlam]
                                              · linarith only [h6297, h6360, hlam]
                                            · have p6343_0 := h6343c.1
                                              have p6343_1 := h6343c.2.1
                                              have p6343_2 := h6343c.2.2.1
                                              have p6343_3 := h6343c.2.2.2
                                              linarith only [h0, h1, h6302, h6306, h6308, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p6343_1]
                                            · have p6343_0 := h6343c.1
                                              have p6343_1 := h6343c.2.1
                                              have p6343_2 := h6343c.2.2.1
                                              have p6343_3 := h6343c.2.2.2
                                              linarith only [h6303, hlam, p6343_0]
                                            · have p6343_0 := h6343c.1
                                              have p6343_1 := h6343c.2.1
                                              have p6343_2 := h6343c.2.2.1
                                              have p6343_3 := h6343c.2.2.2
                                              linarith only [h6305, hlam, p6343_0]
                                            · have p6343_0 := h6343c.1
                                              have p6343_1 := h6343c.2.1
                                              have p6343_2 := h6343c.2.2.1
                                              have p6343_3 := h6343c.2.2.2
                                              linarith only [hlam, p6343_0]
                                            · have p6343_0 := h6343c.1
                                              have p6343_1 := h6343c.2.1
                                              have p6343_2 := h6343c.2.2.1
                                              have p6343_3 := h6343c.2.2.2
                                              linarith only [h6298, h6303, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p6343_1]
                                            · have p6343_0 := h6343c.1
                                              have p6343_1 := h6343c.2.1
                                              have p6343_2 := h6343c.2.2.1
                                              have p6343_3 := h6343c.2.2.2
                                              linarith only [h6297, hlam, p6343_0]
                                            · have p6343_0 := h6343c.1
                                              have p6343_1 := h6343c.2.1
                                              have p6343_2 := h6343c.2.2.1
                                              have p6343_3 := h6343c.2.2.2
                                              linarith only [h6304, hlam, p6343_0]
                                            · have p6343_0 := h6343c.1
                                              have p6343_1 := h6343c.2.1
                                              have p6343_2 := h6343c.2.2.1
                                              have p6343_3 := h6343c.2.2.2
                                              linarith only [h6307, hlam, p6343_0]
                                            · have p6343_0 := h6343c.1
                                              have p6343_1 := h6343c.2.1
                                              have p6343_2 := h6343c.2.2.1
                                              have p6343_3 := h6343c.2.2.2
                                              linarith only [h6308, hlam, p6343_0]
                                            · have p6343_0 := h6343c.1
                                              have p6343_1 := h6343c.2.1
                                              have p6343_2 := h6343c.2.2.1
                                              have p6343_3 := h6343c.2.2.2
                                              linarith only [hlam, p6343_0]
                                        · linarith only [h6340, hlam, p6309_0]
                                      · linarith only [h6152, h6339, hlam]
                                · have p6309_0 := h6309c.1
                                  have p6309_1 := h6309c.2.1
                                  have p6309_2 := h6309c.2.2.1
                                  have p6309_3 := h6309c.2.2.2
                                  rcases p6309_3 (m.d 0 2) (by simp) with h6375 | h6375
                                  · linarith only [h6184, h6375, hlam]
                                  · linarith only [h0, h6375, hlam]
                                · have p6309_0 := h6309c.1
                                  have p6309_1 := h6309c.2.1
                                  have p6309_2 := h6309c.2.2.1
                                  have p6309_3 := h6309c.2.2.2
                                  linarith only [h6305, hlam, p6309_0]
                                · have p6309_0 := h6309c.1
                                  have p6309_1 := h6309c.2.1
                                  have p6309_2 := h6309c.2.2.1
                                  have p6309_3 := h6309c.2.2.2
                                  linarith only [hlam, p6309_0]
                                · have p6309_0 := h6309c.1
                                  have p6309_1 := h6309c.2.1
                                  have p6309_2 := h6309c.2.2.1
                                  have p6309_3 := h6309c.2.2.2
                                  linarith only [h0, h1, h6300, h6302, hlam, p6309_2]
                                · have p6309_0 := h6309c.1
                                  have p6309_1 := h6309c.2.1
                                  have p6309_2 := h6309c.2.2.1
                                  have p6309_3 := h6309c.2.2.2
                                  linarith only [h6186, hlam, p6309_0]
                                · have p6309_0 := h6309c.1
                                  have p6309_1 := h6309c.2.1
                                  have p6309_2 := h6309c.2.2.1
                                  have p6309_3 := h6309c.2.2.2
                                  linarith only [h6302, hlam, p6309_0]
                                · have p6309_0 := h6309c.1
                                  have p6309_1 := h6309c.2.1
                                  have p6309_2 := h6309c.2.2.1
                                  have p6309_3 := h6309c.2.2.2
                                  linarith only [h6306, hlam, p6309_0]
                                · have p6309_0 := h6309c.1
                                  have p6309_1 := h6309c.2.1
                                  have p6309_2 := h6309c.2.2.1
                                  have p6309_3 := h6309c.2.2.2
                                  linarith only [h6307, hlam, p6309_1]
                                · have p6309_0 := h6309c.1
                                  have p6309_1 := h6309c.2.1
                                  have p6309_2 := h6309c.2.2.1
                                  have p6309_3 := h6309c.2.2.2
                                  linarith only [hlam, p6309_0]
                              · linarith only [h0, h6152, h6187, h6297, h6302, h6308, hc04, hc25, hlam, hphi, ht0b, ht5b]
                            · linarith only [h0, h1, h6300, h6302, h6304, h6307, hlam]
                          · linarith only [h0, h1, h6187, h6298, h6303, h6306, hc12, hc35, hlam, hphi, ht23]
                        · linarith only [h6298, h6303, h6305, hlam]
                      · linarith only [h0, h1, h6302, h6304, hc25, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h6391 | h6391
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h6392 | h6392
                        · linarith only [h0, h1, h6302, h6303, h6392, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h6394 | h6394
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h6395 | h6395
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h6396 | h6396
                              · rcases h2bigk with h6397c | h6397c | h6397c | h6397c | h6397c | h6397c | h6397c | h6397c | h6397c | h6397c | h6397c | h6397c | h6397c | h6397c | h6397c | h6397c | h6397c | h6397c | h6397c | h6397c | h6397c | h6397c | h6397c | h6397c | h6397c
                                · have p6397_0 := h6397c.1
                                  have p6397_1 := h6397c.2.1
                                  have p6397_2 := h6397c.2.2.1
                                  have p6397_3 := h6397c.2.2.2
                                  linarith only [hlam, p6397_0]
                                · have p6397_0 := h6397c.1
                                  have p6397_1 := h6397c.2.1
                                  have p6397_2 := h6397c.2.2.1
                                  have p6397_3 := h6397c.2.2.2
                                  linarith only [h0, h1, h6302, h6394, h6396, hc14, hc45, hlam, hphi, ht01, ht0b, ht5b, p6397_1]
                                · have p6397_0 := h6397c.1
                                  have p6397_1 := h6397c.2.1
                                  have p6397_2 := h6397c.2.2.1
                                  have p6397_3 := h6397c.2.2.2
                                  linarith only [h6152, hlam, p6397_0]
                                · have p6397_0 := h6397c.1
                                  have p6397_1 := h6397c.2.1
                                  have p6397_2 := h6397c.2.2.1
                                  have p6397_3 := h6397c.2.2.2
                                  linarith only [h6184, hlam, p6397_0]
                                · have p6397_0 := h6397c.1
                                  have p6397_1 := h6397c.2.1
                                  have p6397_2 := h6397c.2.2.1
                                  have p6397_3 := h6397c.2.2.2
                                  linarith only [h6152, h6392, h6394, h6396, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p6397_1]
                                · have p6397_0 := h6397c.1
                                  have p6397_1 := h6397c.2.1
                                  have p6397_2 := h6397c.2.2.1
                                  have p6397_3 := h6397c.2.2.2
                                  linarith only [h0, hlam, p6397_1]
                                · have p6397_0 := h6397c.1
                                  have p6397_1 := h6397c.2.1
                                  have p6397_2 := h6397c.2.2.1
                                  have p6397_3 := h6397c.2.2.2
                                  linarith only [hlam, p6397_0]
                                · have p6397_0 := h6397c.1
                                  have p6397_1 := h6397c.2.1
                                  have p6397_2 := h6397c.2.2.1
                                  have p6397_3 := h6397c.2.2.2
                                  linarith only [h6298, hlam, p6397_0]
                                · have p6397_0 := h6397c.1
                                  have p6397_1 := h6397c.2.1
                                  have p6397_2 := h6397c.2.2.1
                                  have p6397_3 := h6397c.2.2.2
                                  linarith only [h6300, hlam, p6397_0]
                                · have p6397_0 := h6397c.1
                                  have p6397_1 := h6397c.2.1
                                  have p6397_2 := h6397c.2.2.1
                                  have p6397_3 := h6397c.2.2.2
                                  linarith only [h0, h1, h6300, h6394, h6396, hc24, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p6397_1]
                                · have p6397_0 := h6397c.1
                                  have p6397_1 := h6397c.2.1
                                  have p6397_2 := h6397c.2.2.1
                                  have p6397_3 := h6397c.2.2.2
                                  linarith only [h6392, hc02, hc34, hlam, hphi, ht23, p6397_1]
                                · have p6397_0 := h6397c.1
                                  have p6397_1 := h6397c.2.1
                                  have p6397_2 := h6397c.2.2.1
                                  have p6397_3 := h6397c.2.2.2
                                  linarith only [h6392, hc12, hc34, hlam, hphi, ht23, p6397_1]
                                · have p6397_0 := h6397c.1
                                  have p6397_1 := h6397c.2.1
                                  have p6397_2 := h6397c.2.2.1
                                  have p6397_3 := h6397c.2.2.2
                                  linarith only [hlam, p6397_0]
                                · have p6397_0 := h6397c.1
                                  have p6397_1 := h6397c.2.1
                                  have p6397_2 := h6397c.2.2.1
                                  have p6397_3 := h6397c.2.2.2
                                  linarith only [h6392, hlam, p6397_1]
                                · have p6397_0 := h6397c.1
                                  have p6397_1 := h6397c.2.1
                                  have p6397_2 := h6397c.2.2.1
                                  have p6397_3 := h6397c.2.2.2
                                  rcases p6397_3 (m.d 0 2) (by simp) with h6412 | h6412
                                  · linarith only [h6152, h6412, hlam]
                                  · linarith only [h6186, h6412, hlam]
                                · have p6397_0 := h6397c.1
                                  have p6397_1 := h6397c.2.1
                                  have p6397_2 := h6397c.2.2.1
                                  have p6397_3 := h6397c.2.2.2
                                  rcases p6397_3 (m.d 0 2) (by simp) with h6415 | h6415
                                  · linarith only [h6415, hlam, p6397_0]
                                  · rcases p6397_3 (m.d 1 2) (by simp) with h6417 | h6417
                                    · linarith only [h6300, h6417, hlam]
                                    · rcases p6397_3 (m.d 2 3) (by simp) with h6419 | h6419
                                      · linarith only [h6392, h6419, hlam]
                                      · linarith only [h6152, h6419, hlam]
                                · have p6397_0 := h6397c.1
                                  have p6397_1 := h6397c.2.1
                                  have p6397_2 := h6397c.2.2.1
                                  have p6397_3 := h6397c.2.2.2
                                  rcases p6397_3 (m.d 0 2) (by simp) with h6422 | h6422
                                  · linarith only [h6184, h6422, hlam]
                                  · linarith only [h0, h6422, hlam]
                                · have p6397_0 := h6397c.1
                                  have p6397_1 := h6397c.2.1
                                  have p6397_2 := h6397c.2.2.1
                                  have p6397_3 := h6397c.2.2.2
                                  linarith only [h6152, h6392, hc02, hc34, hlam, hphi, ht23, p6397_1]
                                · have p6397_0 := h6397c.1
                                  have p6397_1 := h6397c.2.1
                                  have p6397_2 := h6397c.2.2.1
                                  have p6397_3 := h6397c.2.2.2
                                  linarith only [hlam, p6397_0]
                                · have p6397_0 := h6397c.1
                                  have p6397_1 := h6397c.2.1
                                  have p6397_2 := h6397c.2.2.1
                                  have p6397_3 := h6397c.2.2.2
                                  linarith only [h0, h1, h6300, h6302, hlam, p6397_2]
                                · have p6397_0 := h6397c.1
                                  have p6397_1 := h6397c.2.1
                                  have p6397_2 := h6397c.2.2.1
                                  have p6397_3 := h6397c.2.2.2
                                  linarith only [h6186, hlam, p6397_0]
                                · have p6397_0 := h6397c.1
                                  have p6397_1 := h6397c.2.1
                                  have p6397_2 := h6397c.2.2.1
                                  have p6397_3 := h6397c.2.2.2
                                  linarith only [h6302, hlam, p6397_0]
                                · have p6397_0 := h6397c.1
                                  have p6397_1 := h6397c.2.1
                                  have p6397_2 := h6397c.2.2.1
                                  have p6397_3 := h6397c.2.2.2
                                  linarith only [h6394, hlam, p6397_0]
                                · have p6397_0 := h6397c.1
                                  have p6397_1 := h6397c.2.1
                                  have p6397_2 := h6397c.2.2.1
                                  have p6397_3 := h6397c.2.2.2
                                  linarith only [h6395, hlam, p6397_1]
                                · have p6397_0 := h6397c.1
                                  have p6397_1 := h6397c.2.1
                                  have p6397_2 := h6397c.2.2.1
                                  have p6397_3 := h6397c.2.2.2
                                  linarith only [hlam, p6397_0]
                              · linarith only [h0, h6152, h6187, h6297, h6302, h6396, hc04, hc25, hlam, hphi, ht0b, ht5b]
                            · linarith only [h0, h1, h6300, h6302, h6391, h6395, hlam]
                          · linarith only [h0, h6152, h6302, h6394, hlam]
                      · linarith only [h0, h1, h6391, hc12, hc45, hlam, hphi, ht23, ht34]
                  · linarith only [h6152, h6186, h6302, hc12, hc23, hlam, hphi]
            · linarith only [h0, h1, h6186, h6297, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h6439 | h6439
          · rcases m.htr 0 4 5 (by decide) (by decide) with h6440 | h6440
            · rcases m.htr 1 2 3 (by decide) (by decide) with h6441 | h6441
              · linarith only [h0, h6152, h6441, hlam]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h6443 | h6443
                · linarith only [h0, h1, h6184, h6443, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h6445 | h6445
                  · linarith only [h0, h6186, h6445, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h6447 | h6447
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h6448 | h6448
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h6449 | h6449
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h6450 | h6450
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h6451 | h6451
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h6452 | h6452
                              · rcases h2bigk with h6453c | h6453c | h6453c | h6453c | h6453c | h6453c | h6453c | h6453c | h6453c | h6453c | h6453c | h6453c | h6453c | h6453c | h6453c | h6453c | h6453c | h6453c | h6453c | h6453c | h6453c | h6453c | h6453c | h6453c | h6453c
                                · have p6453_0 := h6453c.1
                                  have p6453_1 := h6453c.2.1
                                  have p6453_2 := h6453c.2.2.1
                                  have p6453_3 := h6453c.2.2.2
                                  linarith only [hlam, p6453_0]
                                · have p6453_0 := h6453c.1
                                  have p6453_1 := h6453c.2.1
                                  have p6453_2 := h6453c.2.2.1
                                  have p6453_3 := h6453c.2.2.2
                                  linarith only [h6186, hc12, hc25, hlam, hphi, p6453_1]
                                · have p6453_0 := h6453c.1
                                  have p6453_1 := h6453c.2.1
                                  have p6453_2 := h6453c.2.2.1
                                  have p6453_3 := h6453c.2.2.2
                                  linarith only [h6152, hlam, p6453_0]
                                · have p6453_0 := h6453c.1
                                  have p6453_1 := h6453c.2.1
                                  have p6453_2 := h6453c.2.2.1
                                  have p6453_3 := h6453c.2.2.2
                                  linarith only [h6184, hlam, p6453_0]
                                · have p6453_0 := h6453c.1
                                  have p6453_1 := h6453c.2.1
                                  have p6453_2 := h6453c.2.2.1
                                  have p6453_3 := h6453c.2.2.2
                                  linarith only [h6186, hlam, p6453_0]
                                · have p6453_0 := h6453c.1
                                  have p6453_1 := h6453c.2.1
                                  have p6453_2 := h6453c.2.2.1
                                  have p6453_3 := h6453c.2.2.2
                                  linarith only [h0, hlam, p6453_1]
                                · have p6453_0 := h6453c.1
                                  have p6453_1 := h6453c.2.1
                                  have p6453_2 := h6453c.2.2.1
                                  have p6453_3 := h6453c.2.2.2
                                  linarith only [hlam, p6453_0]
                                · have p6453_0 := h6453c.1
                                  have p6453_1 := h6453c.2.1
                                  have p6453_2 := h6453c.2.2.1
                                  have p6453_3 := h6453c.2.2.2
                                  linarith only [h6441, hlam, p6453_0]
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
                                  rcases p6453_3 (m.d 0 2) (by simp) with h6464 | h6464
                                  · linarith only [h6464, hlam, p6453_0]
                                  · rcases p6453_3 (m.d 1 2) (by simp) with h6466 | h6466
                                    · linarith only [h6441, h6466, hlam]
                                    · rcases p6453_3 (m.d 2 3) (by simp) with h6468 | h6468
                                      · rcases p6453_3 (m.d 2 4) (by simp) with h6469 | h6469
                                        · linarith only [h6449, h6469, hlam]
                                        · linarith only [h6184, h6469, hlam]
                                      · linarith only [h6468, hlam, p6453_0]
                                · have p6453_0 := h6453c.1
                                  have p6453_1 := h6453c.2.1
                                  have p6453_2 := h6453c.2.2.1
                                  have p6453_3 := h6453c.2.2.2
                                  rcases p6453_3 (m.d 0 2) (by simp) with h6473 | h6473
                                  · linarith only [h6152, h6473, hlam]
                                  · linarith only [h0, h6473, hlam]
                                · have p6453_0 := h6453c.1
                                  have p6453_1 := h6453c.2.1
                                  have p6453_2 := h6453c.2.2.1
                                  have p6453_3 := h6453c.2.2.2
                                  linarith only [hlam, p6453_0]
                                · have p6453_0 := h6453c.1
                                  have p6453_1 := h6453c.2.1
                                  have p6453_2 := h6453c.2.2.1
                                  have p6453_3 := h6453c.2.2.2
                                  linarith only [h6184, hc02, hc23, hlam, hphi, p6453_1]
                                · have p6453_0 := h6453c.1
                                  have p6453_1 := h6453c.2.1
                                  have p6453_2 := h6453c.2.2.1
                                  have p6453_3 := h6453c.2.2.2
                                  linarith only [h0, h6186, hc12, hc23, hlam, hphi, p6453_1]
                                · have p6453_0 := h6453c.1
                                  have p6453_1 := h6453c.2.1
                                  have p6453_2 := h6453c.2.2.1
                                  have p6453_3 := h6453c.2.2.2
                                  rcases p6453_3 (m.d 0 2) (by simp) with h6479 | h6479
                                  · linarith only [h6479, hlam, p6453_0]
                                  · rcases p6453_3 (m.d 1 2) (by simp) with h6481 | h6481
                                    · linarith only [h6443, h6481, hlam]
                                    · rcases p6453_3 (m.d 2 3) (by simp) with h6483 | h6483
                                      · rcases p6453_3 (m.d 2 4) (by simp) with h6484 | h6484
                                        · rcases p6453_3 (m.d 2 5) (by simp) with h6485 | h6485
                                          · linarith only [h6451, h6485, hlam]
                                          · linarith only [h6186, h6485, hlam]
                                        · linarith only [h6484, hlam, p6453_0]
                                      · linarith only [h6152, h6483, hlam]
                                · have p6453_0 := h6453c.1
                                  have p6453_1 := h6453c.2.1
                                  have p6453_2 := h6453c.2.2.1
                                  have p6453_3 := h6453c.2.2.2
                                  rcases p6453_3 (m.d 0 2) (by simp) with h6490 | h6490
                                  · linarith only [h6184, h6490, hlam]
                                  · linarith only [h0, h6490, hlam]
                                · have p6453_0 := h6453c.1
                                  have p6453_1 := h6453c.2.1
                                  have p6453_2 := h6453c.2.2.1
                                  have p6453_3 := h6453c.2.2.2
                                  linarith only [h6449, hlam, p6453_0]
                                · have p6453_0 := h6453c.1
                                  have p6453_1 := h6453c.2.1
                                  have p6453_2 := h6453c.2.2.1
                                  have p6453_3 := h6453c.2.2.2
                                  linarith only [hlam, p6453_0]
                                · have p6453_0 := h6453c.1
                                  have p6453_1 := h6453c.2.1
                                  have p6453_2 := h6453c.2.2.1
                                  have p6453_3 := h6453c.2.2.2
                                  linarith only [h0, h6186, hc12, hc24, hlam, hphi, p6453_1]
                                · have p6453_0 := h6453c.1
                                  have p6453_1 := h6453c.2.1
                                  have p6453_2 := h6453c.2.2.1
                                  have p6453_3 := h6453c.2.2.2
                                  rcases p6453_3 (m.d 0 2) (by simp) with h6496 | h6496
                                  · linarith only [h6496, hlam, p6453_0]
                                  · rcases p6453_3 (m.d 1 2) (by simp) with h6498 | h6498
                                    · linarith only [h6445, h6498, hlam]
                                    · rcases p6453_3 (m.d 2 3) (by simp) with h6500 | h6500
                                      · rcases p6453_3 (m.d 2 4) (by simp) with h6501 | h6501
                                        · rcases p6453_3 (m.d 2 5) (by simp) with h6502 | h6502
                                          · rcases h4bigk with h6503c | h6503c | h6503c | h6503c | h6503c | h6503c | h6503c | h6503c | h6503c | h6503c | h6503c | h6503c | h6503c | h6503c | h6503c | h6503c | h6503c | h6503c | h6503c | h6503c | h6503c | h6503c | h6503c | h6503c | h6503c
                                            · have p6503_0 := h6503c.1
                                              have p6503_1 := h6503c.2.1
                                              have p6503_2 := h6503c.2.2.1
                                              have p6503_3 := h6503c.2.2.2
                                              linarith only [hlam, p6503_0]
                                            · have p6503_0 := h6503c.1
                                              have p6503_1 := h6503c.2.1
                                              have p6503_2 := h6503c.2.2.1
                                              have p6503_3 := h6503c.2.2.2
                                              linarith only [h1, hlam, p6503_1]
                                            · have p6503_0 := h6503c.1
                                              have p6503_1 := h6503c.2.1
                                              have p6503_2 := h6503c.2.2.1
                                              have p6503_3 := h6503c.2.2.2
                                              linarith only [h6184, hlam, p6503_1]
                                            · have p6503_0 := h6503c.1
                                              have p6503_1 := h6503c.2.1
                                              have p6503_2 := h6503c.2.2.1
                                              have p6503_3 := h6503c.2.2.2
                                              linarith only [h6439, h6452, hc03, hc45, hlam, hphi, ht0b, ht5b, p6503_1]
                                            · have p6503_0 := h6503c.1
                                              have p6503_1 := h6503c.2.1
                                              have p6503_2 := h6503c.2.2.1
                                              have p6503_3 := h6503c.2.2.2
                                              rcases p6503_3 (m.d 0 4) (by simp) with h6508 | h6508
                                              · rcases p6503_3 (m.d 1 4) (by simp) with h6509 | h6509
                                                · rcases p6503_3 (m.d 2 4) (by simp) with h6510 | h6510
                                                  · rcases p6503_3 (m.d 3 4) (by simp) with h6511 | h6511
                                                    · linarith only [h6439, h6511, hlam]
                                                    · linarith only [h6452, h6511, hlam]
                                                  · linarith only [h6451, h6510, hlam]
                                                · linarith only [h6448, h6509, hlam]
                                              · linarith only [h6508, hlam, p6503_0]
                                            · have p6503_0 := h6503c.1
                                              have p6503_1 := h6503c.2.1
                                              have p6503_2 := h6503c.2.2.1
                                              have p6503_3 := h6503c.2.2.2
                                              linarith only [h1, h6441, h6447, hc01, hc23, hlam, hphi, ht12, p6503_1]
                                            · have p6503_0 := h6503c.1
                                              have p6503_1 := h6503c.2.1
                                              have p6503_2 := h6503c.2.2.1
                                              have p6503_3 := h6503c.2.2.2
                                              linarith only [hlam, p6503_0]
                                            · have p6503_0 := h6503c.1
                                              have p6503_1 := h6503c.2.1
                                              have p6503_2 := h6503c.2.2.1
                                              have p6503_3 := h6503c.2.2.2
                                              linarith only [h6443, hlam, p6503_1]
                                            · have p6503_0 := h6503c.1
                                              have p6503_1 := h6503c.2.1
                                              have p6503_2 := h6503c.2.2.1
                                              have p6503_3 := h6503c.2.2.2
                                              linarith only [h6441, h6447, h6452, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p6503_1]
                                            · have p6503_0 := h6503c.1
                                              have p6503_1 := h6503c.2.1
                                              have p6503_2 := h6503c.2.2.1
                                              have p6503_3 := h6503c.2.2.2
                                              rcases p6503_3 (m.d 0 4) (by simp) with h6521 | h6521
                                              · linarith only [h1, h6521, hlam]
                                              · linarith only [h6440, h6521, hlam]
                                            · have p6503_0 := h6503c.1
                                              have p6503_1 := h6503c.2.1
                                              have p6503_2 := h6503c.2.2.1
                                              have p6503_3 := h6503c.2.2.2
                                              linarith only [h0, h1, h6449, hc12, hc23, hlam, hphi, p6503_1]
                                            · have p6503_0 := h6503c.1
                                              have p6503_1 := h6503c.2.1
                                              have p6503_2 := h6503c.2.2.1
                                              have p6503_3 := h6503c.2.2.2
                                              linarith only [h0, h1, h6449, hc12, hc23, hlam, hphi, p6503_1]
                                            · have p6503_0 := h6503c.1
                                              have p6503_1 := h6503c.2.1
                                              have p6503_2 := h6503c.2.2.1
                                              have p6503_3 := h6503c.2.2.2
                                              linarith only [hlam, p6503_0]
                                            · have p6503_0 := h6503c.1
                                              have p6503_1 := h6503c.2.1
                                              have p6503_2 := h6503c.2.2.1
                                              have p6503_3 := h6503c.2.2.2
                                              linarith only [h6449, h6452, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p6503_1]
                                            · have p6503_0 := h6503c.1
                                              have p6503_1 := h6503c.2.1
                                              have p6503_2 := h6503c.2.2.1
                                              have p6503_3 := h6503c.2.2.2
                                              rcases p6503_3 (m.d 0 4) (by simp) with h6528 | h6528
                                              · linarith only [h6184, h6528, hlam]
                                              · linarith only [h6440, h6528, hlam]
                                            · have p6503_0 := h6503c.1
                                              have p6503_1 := h6503c.2.1
                                              have p6503_2 := h6503c.2.2.1
                                              have p6503_3 := h6503c.2.2.2
                                              linarith only [h6439, hlam, p6503_0]
                                            · have p6503_0 := h6503c.1
                                              have p6503_1 := h6503c.2.1
                                              have p6503_2 := h6503c.2.2.1
                                              have p6503_3 := h6503c.2.2.2
                                              linarith only [h6447, hlam, p6503_0]
                                            · have p6503_0 := h6503c.1
                                              have p6503_1 := h6503c.2.1
                                              have p6503_2 := h6503c.2.2.1
                                              have p6503_3 := h6503c.2.2.2
                                              linarith only [h6449, hlam, p6503_0]
                                            · have p6503_0 := h6503c.1
                                              have p6503_1 := h6503c.2.1
                                              have p6503_2 := h6503c.2.2.1
                                              have p6503_3 := h6503c.2.2.2
                                              linarith only [hlam, p6503_0]
                                            · have p6503_0 := h6503c.1
                                              have p6503_1 := h6503c.2.1
                                              have p6503_2 := h6503c.2.2.1
                                              have p6503_3 := h6503c.2.2.2
                                              linarith only [h6152, h6439, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p6503_1]
                                            · have p6503_0 := h6503c.1
                                              have p6503_1 := h6503c.2.1
                                              have p6503_2 := h6503c.2.2.1
                                              have p6503_3 := h6503c.2.2.2
                                              linarith only [h6440, hlam, p6503_0]
                                            · have p6503_0 := h6503c.1
                                              have p6503_1 := h6503c.2.1
                                              have p6503_2 := h6503c.2.2.1
                                              have p6503_3 := h6503c.2.2.2
                                              linarith only [h6448, hlam, p6503_0]
                                            · have p6503_0 := h6503c.1
                                              have p6503_1 := h6503c.2.1
                                              have p6503_2 := h6503c.2.2.1
                                              have p6503_3 := h6503c.2.2.2
                                              linarith only [h6451, hlam, p6503_0]
                                            · have p6503_0 := h6503c.1
                                              have p6503_1 := h6503c.2.1
                                              have p6503_2 := h6503c.2.2.1
                                              have p6503_3 := h6503c.2.2.2
                                              linarith only [h6452, hlam, p6503_0]
                                            · have p6503_0 := h6503c.1
                                              have p6503_1 := h6503c.2.1
                                              have p6503_2 := h6503c.2.2.1
                                              have p6503_3 := h6503c.2.2.2
                                              linarith only [hlam, p6503_0]
                                          · linarith only [h6502, hlam, p6453_0]
                                        · linarith only [h6184, h6501, hlam]
                                      · linarith only [h6152, h6500, hlam]
                                · have p6453_0 := h6453c.1
                                  have p6453_1 := h6453c.2.1
                                  have p6453_2 := h6453c.2.2.1
                                  have p6453_3 := h6453c.2.2.2
                                  rcases p6453_3 (m.d 0 2) (by simp) with h6544 | h6544
                                  · linarith only [h6186, h6544, hlam]
                                  · linarith only [h0, h6544, hlam]
                                · have p6453_0 := h6453c.1
                                  have p6453_1 := h6453c.2.1
                                  have p6453_2 := h6453c.2.2.1
                                  have p6453_3 := h6453c.2.2.2
                                  linarith only [h6450, hlam, p6453_0]
                                · have p6453_0 := h6453c.1
                                  have p6453_1 := h6453c.2.1
                                  have p6453_2 := h6453c.2.2.1
                                  have p6453_3 := h6453c.2.2.2
                                  linarith only [h6451, hlam, p6453_1]
                                · have p6453_0 := h6453c.1
                                  have p6453_1 := h6453c.2.1
                                  have p6453_2 := h6453c.2.2.1
                                  have p6453_3 := h6453c.2.2.2
                                  linarith only [hlam, p6453_0]
                              · rcases h2bigk with h6550c | h6550c | h6550c | h6550c | h6550c | h6550c | h6550c | h6550c | h6550c | h6550c | h6550c | h6550c | h6550c | h6550c | h6550c | h6550c | h6550c | h6550c | h6550c | h6550c | h6550c | h6550c | h6550c | h6550c | h6550c
                                · have p6550_0 := h6550c.1
                                  have p6550_1 := h6550c.2.1
                                  have p6550_2 := h6550c.2.2.1
                                  have p6550_3 := h6550c.2.2.2
                                  linarith only [hlam, p6550_0]
                                · have p6550_0 := h6550c.1
                                  have p6550_1 := h6550c.2.1
                                  have p6550_2 := h6550c.2.2.1
                                  have p6550_3 := h6550c.2.2.2
                                  linarith only [h0, h1, h6443, h6449, hc12, hc23, hlam, hphi, p6550_1]
                                · have p6550_0 := h6550c.1
                                  have p6550_1 := h6550c.2.1
                                  have p6550_2 := h6550c.2.2.1
                                  have p6550_3 := h6550c.2.2.2
                                  linarith only [h6152, hlam, p6550_0]
                                · have p6550_0 := h6550c.1
                                  have p6550_1 := h6550c.2.1
                                  have p6550_2 := h6550c.2.2.1
                                  have p6550_3 := h6550c.2.2.2
                                  linarith only [h6184, hlam, p6550_0]
                                · have p6550_0 := h6550c.1
                                  have p6550_1 := h6550c.2.1
                                  have p6550_2 := h6550c.2.2.1
                                  have p6550_3 := h6550c.2.2.2
                                  linarith only [h6186, hlam, p6550_0]
                                · have p6550_0 := h6550c.1
                                  have p6550_1 := h6550c.2.1
                                  have p6550_2 := h6550c.2.2.1
                                  have p6550_3 := h6550c.2.2.2
                                  linarith only [h0, hlam, p6550_1]
                                · have p6550_0 := h6550c.1
                                  have p6550_1 := h6550c.2.1
                                  have p6550_2 := h6550c.2.2.1
                                  have p6550_3 := h6550c.2.2.2
                                  linarith only [hlam, p6550_0]
                                · have p6550_0 := h6550c.1
                                  have p6550_1 := h6550c.2.1
                                  have p6550_2 := h6550c.2.2.1
                                  have p6550_3 := h6550c.2.2.2
                                  linarith only [h6441, hlam, p6550_0]
                                · have p6550_0 := h6550c.1
                                  have p6550_1 := h6550c.2.1
                                  have p6550_2 := h6550c.2.2.1
                                  have p6550_3 := h6550c.2.2.2
                                  linarith only [h6443, hlam, p6550_0]
                                · have p6550_0 := h6550c.1
                                  have p6550_1 := h6550c.2.1
                                  have p6550_2 := h6550c.2.2.1
                                  have p6550_3 := h6550c.2.2.2
                                  linarith only [h6445, hlam, p6550_0]
                                · have p6550_0 := h6550c.1
                                  have p6550_1 := h6550c.2.1
                                  have p6550_2 := h6550c.2.2.1
                                  have p6550_3 := h6550c.2.2.2
                                  rcases p6550_3 (m.d 0 2) (by simp) with h6561 | h6561
                                  · linarith only [h6561, hlam, p6550_0]
                                  · rcases p6550_3 (m.d 1 2) (by simp) with h6563 | h6563
                                    · linarith only [h6441, h6563, hlam]
                                    · rcases p6550_3 (m.d 2 3) (by simp) with h6565 | h6565
                                      · rcases p6550_3 (m.d 2 4) (by simp) with h6566 | h6566
                                        · linarith only [h6449, h6566, hlam]
                                        · linarith only [h6184, h6566, hlam]
                                      · linarith only [h6565, hlam, p6550_0]
                                · have p6550_0 := h6550c.1
                                  have p6550_1 := h6550c.2.1
                                  have p6550_2 := h6550c.2.2.1
                                  have p6550_3 := h6550c.2.2.2
                                  rcases p6550_3 (m.d 0 2) (by simp) with h6570 | h6570
                                  · linarith only [h6152, h6570, hlam]
                                  · linarith only [h0, h6570, hlam]
                                · have p6550_0 := h6550c.1
                                  have p6550_1 := h6550c.2.1
                                  have p6550_2 := h6550c.2.2.1
                                  have p6550_3 := h6550c.2.2.2
                                  linarith only [hlam, p6550_0]
                                · have p6550_0 := h6550c.1
                                  have p6550_1 := h6550c.2.1
                                  have p6550_2 := h6550c.2.2.1
                                  have p6550_3 := h6550c.2.2.2
                                  linarith only [h1, h6443, hc01, hc23, hlam, hphi, ht12, p6550_1]
                                · have p6550_0 := h6550c.1
                                  have p6550_1 := h6550c.2.1
                                  have p6550_2 := h6550c.2.2.1
                                  have p6550_3 := h6550c.2.2.2
                                  linarith only [h6186, hc02, hc23, hlam, hphi, p6550_1]
                                · have p6550_0 := h6550c.1
                                  have p6550_1 := h6550c.2.1
                                  have p6550_2 := h6550c.2.2.1
                                  have p6550_3 := h6550c.2.2.2
                                  rcases p6550_3 (m.d 0 2) (by simp) with h6576 | h6576
                                  · linarith only [h6576, hlam, p6550_0]
                                  · rcases p6550_3 (m.d 1 2) (by simp) with h6578 | h6578
                                    · linarith only [h6443, h6578, hlam]
                                    · rcases p6550_3 (m.d 2 3) (by simp) with h6580 | h6580
                                      · rcases p6550_3 (m.d 2 4) (by simp) with h6581 | h6581
                                        · rcases p6550_3 (m.d 2 5) (by simp) with h6582 | h6582
                                          · linarith only [h6451, h6582, hlam]
                                          · linarith only [h6186, h6582, hlam]
                                        · linarith only [h6581, hlam, p6550_0]
                                      · linarith only [h6152, h6580, hlam]
                                · have p6550_0 := h6550c.1
                                  have p6550_1 := h6550c.2.1
                                  have p6550_2 := h6550c.2.2.1
                                  have p6550_3 := h6550c.2.2.2
                                  rcases p6550_3 (m.d 0 2) (by simp) with h6587 | h6587
                                  · linarith only [h6184, h6587, hlam]
                                  · linarith only [h0, h6587, hlam]
                                · have p6550_0 := h6550c.1
                                  have p6550_1 := h6550c.2.1
                                  have p6550_2 := h6550c.2.2.1
                                  have p6550_3 := h6550c.2.2.2
                                  linarith only [h6449, hlam, p6550_0]
                                · have p6550_0 := h6550c.1
                                  have p6550_1 := h6550c.2.1
                                  have p6550_2 := h6550c.2.2.1
                                  have p6550_3 := h6550c.2.2.2
                                  linarith only [hlam, p6550_0]
                                · have p6550_0 := h6550c.1
                                  have p6550_1 := h6550c.2.1
                                  have p6550_2 := h6550c.2.2.1
                                  have p6550_3 := h6550c.2.2.2
                                  linarith only [h0, h6186, hc12, hc24, hlam, hphi, p6550_1]
                                · have p6550_0 := h6550c.1
                                  have p6550_1 := h6550c.2.1
                                  have p6550_2 := h6550c.2.2.1
                                  have p6550_3 := h6550c.2.2.2
                                  rcases p6550_3 (m.d 0 2) (by simp) with h6593 | h6593
                                  · linarith only [h6593, hlam, p6550_0]
                                  · rcases p6550_3 (m.d 1 2) (by simp) with h6595 | h6595
                                    · linarith only [h6445, h6595, hlam]
                                    · rcases p6550_3 (m.d 2 3) (by simp) with h6597 | h6597
                                      · rcases p6550_3 (m.d 2 4) (by simp) with h6598 | h6598
                                        · rcases p6550_3 (m.d 2 5) (by simp) with h6599 | h6599
                                          · rcases h4bigk with h6600c | h6600c | h6600c | h6600c | h6600c | h6600c | h6600c | h6600c | h6600c | h6600c | h6600c | h6600c | h6600c | h6600c | h6600c | h6600c | h6600c | h6600c | h6600c | h6600c | h6600c | h6600c | h6600c | h6600c | h6600c
                                            · have p6600_0 := h6600c.1
                                              have p6600_1 := h6600c.2.1
                                              have p6600_2 := h6600c.2.2.1
                                              have p6600_3 := h6600c.2.2.2
                                              linarith only [hlam, p6600_0]
                                            · have p6600_0 := h6600c.1
                                              have p6600_1 := h6600c.2.1
                                              have p6600_2 := h6600c.2.2.1
                                              have p6600_3 := h6600c.2.2.2
                                              linarith only [h1, hlam, p6600_1]
                                            · have p6600_0 := h6600c.1
                                              have p6600_1 := h6600c.2.1
                                              have p6600_2 := h6600c.2.2.1
                                              have p6600_3 := h6600c.2.2.2
                                              linarith only [h6184, hlam, p6600_1]
                                            · have p6600_0 := h6600c.1
                                              have p6600_1 := h6600c.2.1
                                              have p6600_2 := h6600c.2.2.1
                                              have p6600_3 := h6600c.2.2.2
                                              rcases p6600_3 (m.d 0 4) (by simp) with h6604 | h6604
                                              · rcases p6600_3 (m.d 1 4) (by simp) with h6605 | h6605
                                                · rcases p6600_3 (m.d 2 4) (by simp) with h6606 | h6606
                                                  · rcases p6600_3 (m.d 3 4) (by simp) with h6607 | h6607
                                                    · linarith only [h6439, h6607, hlam]
                                                    · rcases p6600_3 (m.d 4 5) (by simp) with h6609 | h6609
                                                      · linarith only [h6440, h6609, hlam]
                                                      · linarith only [h6452, h6609, hlam]
                                                  · linarith only [h6449, h6606, hlam]
                                                · linarith only [h6447, h6605, hlam]
                                              · linarith only [h6439, h6604, hlam]
                                            · have p6600_0 := h6600c.1
                                              have p6600_1 := h6600c.2.1
                                              have p6600_2 := h6600c.2.2.1
                                              have p6600_3 := h6600c.2.2.2
                                              linarith only [h6452, hc04, hc34, hlam, hphi, ht0b, ht45, ht5b, p6600_1]
                                            · have p6600_0 := h6600c.1
                                              have p6600_1 := h6600c.2.1
                                              have p6600_2 := h6600c.2.2.1
                                              have p6600_3 := h6600c.2.2.2
                                              linarith only [h1, hc01, hc14, hlam, hphi, p6600_1]
                                            · have p6600_0 := h6600c.1
                                              have p6600_1 := h6600c.2.1
                                              have p6600_2 := h6600c.2.2.1
                                              have p6600_3 := h6600c.2.2.2
                                              linarith only [hlam, p6600_0]
                                            · have p6600_0 := h6600c.1
                                              have p6600_1 := h6600c.2.1
                                              have p6600_2 := h6600c.2.2.1
                                              have p6600_3 := h6600c.2.2.2
                                              linarith only [h6443, hlam, p6600_1]
                                            · have p6600_0 := h6600c.1
                                              have p6600_1 := h6600c.2.1
                                              have p6600_2 := h6600c.2.2.1
                                              have p6600_3 := h6600c.2.2.2
                                              rcases p6600_3 (m.d 0 4) (by simp) with h6619 | h6619
                                              · linarith only [h1, h6619, hlam]
                                              · linarith only [h6439, h6619, hlam]
                                            · have p6600_0 := h6600c.1
                                              have p6600_1 := h6600c.2.1
                                              have p6600_2 := h6600c.2.2.1
                                              have p6600_3 := h6600c.2.2.2
                                              linarith only [h6443, h6449, h6452, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p6600_1]
                                            · have p6600_0 := h6600c.1
                                              have p6600_1 := h6600c.2.1
                                              have p6600_2 := h6600c.2.2.1
                                              have p6600_3 := h6600c.2.2.2
                                              linarith only [h6440, h6449, h6452, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p6600_1]
                                            · have p6600_0 := h6600c.1
                                              have p6600_1 := h6600c.2.1
                                              have p6600_2 := h6600c.2.2.1
                                              have p6600_3 := h6600c.2.2.2
                                              linarith only [h0, h1, h6449, hc12, hc23, hlam, hphi, p6600_1]
                                            · have p6600_0 := h6600c.1
                                              have p6600_1 := h6600c.2.1
                                              have p6600_2 := h6600c.2.2.1
                                              have p6600_3 := h6600c.2.2.2
                                              linarith only [hlam, p6600_0]
                                            · have p6600_0 := h6600c.1
                                              have p6600_1 := h6600c.2.1
                                              have p6600_2 := h6600c.2.2.1
                                              have p6600_3 := h6600c.2.2.2
                                              rcases p6600_3 (m.d 0 4) (by simp) with h6626 | h6626
                                              · linarith only [h6184, h6626, hlam]
                                              · linarith only [h6439, h6626, hlam]
                                            · have p6600_0 := h6600c.1
                                              have p6600_1 := h6600c.2.1
                                              have p6600_2 := h6600c.2.2.1
                                              have p6600_3 := h6600c.2.2.2
                                              linarith only [h6449, h6452, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p6600_1]
                                            · have p6600_0 := h6600c.1
                                              have p6600_1 := h6600c.2.1
                                              have p6600_2 := h6600c.2.2.1
                                              have p6600_3 := h6600c.2.2.2
                                              linarith only [h6439, hlam, p6600_0]
                                            · have p6600_0 := h6600c.1
                                              have p6600_1 := h6600c.2.1
                                              have p6600_2 := h6600c.2.2.1
                                              have p6600_3 := h6600c.2.2.2
                                              linarith only [h6447, hlam, p6600_0]
                                            · have p6600_0 := h6600c.1
                                              have p6600_1 := h6600c.2.1
                                              have p6600_2 := h6600c.2.2.1
                                              have p6600_3 := h6600c.2.2.2
                                              linarith only [h6449, hlam, p6600_0]
                                            · have p6600_0 := h6600c.1
                                              have p6600_1 := h6600c.2.1
                                              have p6600_2 := h6600c.2.2.1
                                              have p6600_3 := h6600c.2.2.2
                                              linarith only [hlam, p6600_0]
                                            · have p6600_0 := h6600c.1
                                              have p6600_1 := h6600c.2.1
                                              have p6600_2 := h6600c.2.2.1
                                              have p6600_3 := h6600c.2.2.2
                                              linarith only [h6452, hlam, p6600_0]
                                            · have p6600_0 := h6600c.1
                                              have p6600_1 := h6600c.2.1
                                              have p6600_2 := h6600c.2.2.1
                                              have p6600_3 := h6600c.2.2.2
                                              linarith only [h6440, hlam, p6600_0]
                                            · have p6600_0 := h6600c.1
                                              have p6600_1 := h6600c.2.1
                                              have p6600_2 := h6600c.2.2.1
                                              have p6600_3 := h6600c.2.2.2
                                              linarith only [h6448, hlam, p6600_0]
                                            · have p6600_0 := h6600c.1
                                              have p6600_1 := h6600c.2.1
                                              have p6600_2 := h6600c.2.2.1
                                              have p6600_3 := h6600c.2.2.2
                                              linarith only [h6451, hlam, p6600_0]
                                            · have p6600_0 := h6600c.1
                                              have p6600_1 := h6600c.2.1
                                              have p6600_2 := h6600c.2.2.1
                                              have p6600_3 := h6600c.2.2.2
                                              linarith only [h6440, hc04, hc34, hlam, hphi, ht0b, ht45, ht5b, p6600_1]
                                            · have p6600_0 := h6600c.1
                                              have p6600_1 := h6600c.2.1
                                              have p6600_2 := h6600c.2.2.1
                                              have p6600_3 := h6600c.2.2.2
                                              linarith only [hlam, p6600_0]
                                          · linarith only [h6599, hlam, p6550_0]
                                        · linarith only [h6184, h6598, hlam]
                                      · linarith only [h6152, h6597, hlam]
                                · have p6550_0 := h6550c.1
                                  have p6550_1 := h6550c.2.1
                                  have p6550_2 := h6550c.2.2.1
                                  have p6550_3 := h6550c.2.2.2
                                  rcases p6550_3 (m.d 0 2) (by simp) with h6643 | h6643
                                  · linarith only [h6186, h6643, hlam]
                                  · linarith only [h0, h6643, hlam]
                                · have p6550_0 := h6550c.1
                                  have p6550_1 := h6550c.2.1
                                  have p6550_2 := h6550c.2.2.1
                                  have p6550_3 := h6550c.2.2.2
                                  linarith only [h6450, hlam, p6550_0]
                                · have p6550_0 := h6550c.1
                                  have p6550_1 := h6550c.2.1
                                  have p6550_2 := h6550c.2.2.1
                                  have p6550_3 := h6550c.2.2.2
                                  linarith only [h6451, hlam, p6550_1]
                                · have p6550_0 := h6550c.1
                                  have p6550_1 := h6550c.2.1
                                  have p6550_2 := h6550c.2.2.1
                                  have p6550_3 := h6550c.2.2.2
                                  linarith only [hlam, p6550_0]
                            · linarith only [h1, h6440, h6443, h6451, hlam]
                          · linarith only [h0, h1, h6443, h6449, h6450, hc12, hc35, hlam, hphi, ht23]
                        · linarith only [h0, h1, h6441, h6447, h6449, hc12, hc34, hlam, hphi, ht23]
                      · linarith only [h0, h1, h6440, h6448, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                    · linarith only [h0, h1, h6152, h6439, h6447, hc12, hc23, hlam, hphi]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h6654 | h6654
              · linarith only [h0, h1, h6152, h6440, h6654, hc03, hc45, hlam, hphi, ht34]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h6656 | h6656
                · linarith only [h0, h1, h6440, h6656, hc24, hc45, hlam, hphi]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h6658 | h6658
                  · linarith only [h0, h6186, h6658, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h6660 | h6660
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h6661 | h6661
                      · linarith only [h0, h1, h6440, h6654, h6660, h6661, hc12, hc23, hlam, hphi]
                      · linarith only [h0, h1, h6661, hc12, hc45, hlam, hphi, ht23, ht34]
                    · linarith only [h1, h6439, h6660, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h6665 | h6665
            · rcases m.htr 1 2 3 (by decide) (by decide) with h6666 | h6666
              · linarith only [h0, h6152, h6666, hlam]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h6668 | h6668
                · linarith only [h0, h1, h6184, h6665, h6668, hc14, hc45, hlam, hphi, ht01, ht0b, ht5b]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h6670 | h6670
                  · linarith only [h0, h6186, h6670, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h6672 | h6672
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h6673 | h6673
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h6674 | h6674
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h6675 | h6675
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h6676 | h6676
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h6677 | h6677
                              · rcases h2bigk with h6678c | h6678c | h6678c | h6678c | h6678c | h6678c | h6678c | h6678c | h6678c | h6678c | h6678c | h6678c | h6678c | h6678c | h6678c | h6678c | h6678c | h6678c | h6678c | h6678c | h6678c | h6678c | h6678c | h6678c | h6678c
                                · have p6678_0 := h6678c.1
                                  have p6678_1 := h6678c.2.1
                                  have p6678_2 := h6678c.2.2.1
                                  have p6678_3 := h6678c.2.2.2
                                  linarith only [hlam, p6678_0]
                                · have p6678_0 := h6678c.1
                                  have p6678_1 := h6678c.2.1
                                  have p6678_2 := h6678c.2.2.1
                                  have p6678_3 := h6678c.2.2.2
                                  linarith only [h6152, h6439, h6666, h6672, hc12, hc23, hlam, hphi, p6678_1]
                                · have p6678_0 := h6678c.1
                                  have p6678_1 := h6678c.2.1
                                  have p6678_2 := h6678c.2.2.1
                                  have p6678_3 := h6678c.2.2.2
                                  linarith only [h6152, hlam, p6678_0]
                                · have p6678_0 := h6678c.1
                                  have p6678_1 := h6678c.2.1
                                  have p6678_2 := h6678c.2.2.1
                                  have p6678_3 := h6678c.2.2.2
                                  linarith only [h6184, hlam, p6678_0]
                                · have p6678_0 := h6678c.1
                                  have p6678_1 := h6678c.2.1
                                  have p6678_2 := h6678c.2.2.1
                                  have p6678_3 := h6678c.2.2.2
                                  linarith only [h6186, hlam, p6678_0]
                                · have p6678_0 := h6678c.1
                                  have p6678_1 := h6678c.2.1
                                  have p6678_2 := h6678c.2.2.1
                                  have p6678_3 := h6678c.2.2.2
                                  linarith only [h0, hlam, p6678_1]
                                · have p6678_0 := h6678c.1
                                  have p6678_1 := h6678c.2.1
                                  have p6678_2 := h6678c.2.2.1
                                  have p6678_3 := h6678c.2.2.2
                                  linarith only [hlam, p6678_0]
                                · have p6678_0 := h6678c.1
                                  have p6678_1 := h6678c.2.1
                                  have p6678_2 := h6678c.2.2.1
                                  have p6678_3 := h6678c.2.2.2
                                  linarith only [h6666, hlam, p6678_0]
                                · have p6678_0 := h6678c.1
                                  have p6678_1 := h6678c.2.1
                                  have p6678_2 := h6678c.2.2.1
                                  have p6678_3 := h6678c.2.2.2
                                  linarith only [h6668, hlam, p6678_0]
                                · have p6678_0 := h6678c.1
                                  have p6678_1 := h6678c.2.1
                                  have p6678_2 := h6678c.2.2.1
                                  have p6678_3 := h6678c.2.2.2
                                  linarith only [h6670, hlam, p6678_0]
                                · have p6678_0 := h6678c.1
                                  have p6678_1 := h6678c.2.1
                                  have p6678_2 := h6678c.2.2.1
                                  have p6678_3 := h6678c.2.2.2
                                  rcases p6678_3 (m.d 0 2) (by simp) with h6689 | h6689
                                  · linarith only [h6689, hlam, p6678_0]
                                  · rcases p6678_3 (m.d 1 2) (by simp) with h6691 | h6691
                                    · linarith only [h6666, h6691, hlam]
                                    · rcases p6678_3 (m.d 2 3) (by simp) with h6693 | h6693
                                      · rcases p6678_3 (m.d 2 4) (by simp) with h6694 | h6694
                                        · linarith only [h6674, h6694, hlam]
                                        · linarith only [h6184, h6694, hlam]
                                      · linarith only [h6693, hlam, p6678_0]
                                · have p6678_0 := h6678c.1
                                  have p6678_1 := h6678c.2.1
                                  have p6678_2 := h6678c.2.2.1
                                  have p6678_3 := h6678c.2.2.2
                                  rcases p6678_3 (m.d 0 2) (by simp) with h6698 | h6698
                                  · linarith only [h6152, h6698, hlam]
                                  · linarith only [h0, h6698, hlam]
                                · have p6678_0 := h6678c.1
                                  have p6678_1 := h6678c.2.1
                                  have p6678_2 := h6678c.2.2.1
                                  have p6678_3 := h6678c.2.2.2
                                  linarith only [hlam, p6678_0]
                                · have p6678_0 := h6678c.1
                                  have p6678_1 := h6678c.2.1
                                  have p6678_2 := h6678c.2.2.1
                                  have p6678_3 := h6678c.2.2.2
                                  linarith only [h0, h1, h6668, hc12, hc23, hlam, hphi, p6678_1]
                                · have p6678_0 := h6678c.1
                                  have p6678_1 := h6678c.2.1
                                  have p6678_2 := h6678c.2.2.1
                                  have p6678_3 := h6678c.2.2.2
                                  linarith only [h6186, hc02, hc23, hlam, hphi, p6678_1]
                                · have p6678_0 := h6678c.1
                                  have p6678_1 := h6678c.2.1
                                  have p6678_2 := h6678c.2.2.1
                                  have p6678_3 := h6678c.2.2.2
                                  rcases p6678_3 (m.d 0 2) (by simp) with h6704 | h6704
                                  · linarith only [h6704, hlam, p6678_0]
                                  · rcases p6678_3 (m.d 1 2) (by simp) with h6706 | h6706
                                    · linarith only [h6668, h6706, hlam]
                                    · rcases p6678_3 (m.d 2 3) (by simp) with h6708 | h6708
                                      · rcases p6678_3 (m.d 2 4) (by simp) with h6709 | h6709
                                        · rcases p6678_3 (m.d 2 5) (by simp) with h6710 | h6710
                                          · linarith only [h6676, h6710, hlam]
                                          · linarith only [h6186, h6710, hlam]
                                        · linarith only [h6709, hlam, p6678_0]
                                      · linarith only [h6152, h6708, hlam]
                                · have p6678_0 := h6678c.1
                                  have p6678_1 := h6678c.2.1
                                  have p6678_2 := h6678c.2.2.1
                                  have p6678_3 := h6678c.2.2.2
                                  rcases p6678_3 (m.d 0 2) (by simp) with h6715 | h6715
                                  · linarith only [h6184, h6715, hlam]
                                  · linarith only [h0, h6715, hlam]
                                · have p6678_0 := h6678c.1
                                  have p6678_1 := h6678c.2.1
                                  have p6678_2 := h6678c.2.2.1
                                  have p6678_3 := h6678c.2.2.2
                                  linarith only [h6674, hlam, p6678_0]
                                · have p6678_0 := h6678c.1
                                  have p6678_1 := h6678c.2.1
                                  have p6678_2 := h6678c.2.2.1
                                  have p6678_3 := h6678c.2.2.2
                                  linarith only [hlam, p6678_0]
                                · have p6678_0 := h6678c.1
                                  have p6678_1 := h6678c.2.1
                                  have p6678_2 := h6678c.2.2.1
                                  have p6678_3 := h6678c.2.2.2
                                  linarith only [h0, h6186, hc12, hc24, hlam, hphi, p6678_1]
                                · have p6678_0 := h6678c.1
                                  have p6678_1 := h6678c.2.1
                                  have p6678_2 := h6678c.2.2.1
                                  have p6678_3 := h6678c.2.2.2
                                  rcases p6678_3 (m.d 0 2) (by simp) with h6721 | h6721
                                  · linarith only [h6721, hlam, p6678_0]
                                  · rcases p6678_3 (m.d 1 2) (by simp) with h6723 | h6723
                                    · linarith only [h6670, h6723, hlam]
                                    · rcases p6678_3 (m.d 2 3) (by simp) with h6725 | h6725
                                      · rcases p6678_3 (m.d 2 4) (by simp) with h6726 | h6726
                                        · rcases p6678_3 (m.d 2 5) (by simp) with h6727 | h6727
                                          · rcases h4bigk with h6728c | h6728c | h6728c | h6728c | h6728c | h6728c | h6728c | h6728c | h6728c | h6728c | h6728c | h6728c | h6728c | h6728c | h6728c | h6728c | h6728c | h6728c | h6728c | h6728c | h6728c | h6728c | h6728c | h6728c | h6728c
                                            · have p6728_0 := h6728c.1
                                              have p6728_1 := h6728c.2.1
                                              have p6728_2 := h6728c.2.2.1
                                              have p6728_3 := h6728c.2.2.2
                                              linarith only [hlam, p6728_0]
                                            · have p6728_0 := h6728c.1
                                              have p6728_1 := h6728c.2.1
                                              have p6728_2 := h6728c.2.2.1
                                              have p6728_3 := h6728c.2.2.2
                                              linarith only [h1, hlam, p6728_1]
                                            · have p6728_0 := h6728c.1
                                              have p6728_1 := h6728c.2.1
                                              have p6728_2 := h6728c.2.2.1
                                              have p6728_3 := h6728c.2.2.2
                                              linarith only [h6184, hlam, p6728_1]
                                            · have p6728_0 := h6728c.1
                                              have p6728_1 := h6728c.2.1
                                              have p6728_2 := h6728c.2.2.1
                                              have p6728_3 := h6728c.2.2.2
                                              linarith only [h6439, hlam, p6728_1]
                                            · have p6728_0 := h6728c.1
                                              have p6728_1 := h6728c.2.1
                                              have p6728_2 := h6728c.2.2.1
                                              have p6728_3 := h6728c.2.2.2
                                              linarith only [h6439, h6666, h6672, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p6728_1]
                                            · have p6728_0 := h6728c.1
                                              have p6728_1 := h6728c.2.1
                                              have p6728_2 := h6728c.2.2.1
                                              have p6728_3 := h6728c.2.2.2
                                              linarith only [h0, h1, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p6728_1]
                                            · have p6728_0 := h6728c.1
                                              have p6728_1 := h6728c.2.1
                                              have p6728_2 := h6728c.2.2.1
                                              have p6728_3 := h6728c.2.2.2
                                              linarith only [hlam, p6728_0]
                                            · have p6728_0 := h6728c.1
                                              have p6728_1 := h6728c.2.1
                                              have p6728_2 := h6728c.2.2.1
                                              have p6728_3 := h6728c.2.2.2
                                              linarith only [h6668, hlam, p6728_1]
                                            · have p6728_0 := h6728c.1
                                              have p6728_1 := h6728c.2.1
                                              have p6728_2 := h6728c.2.2.1
                                              have p6728_3 := h6728c.2.2.2
                                              linarith only [h6439, h6668, h6674, hc03, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p6728_1]
                                            · have p6728_0 := h6728c.1
                                              have p6728_1 := h6728c.2.1
                                              have p6728_2 := h6728c.2.2.1
                                              have p6728_3 := h6728c.2.2.2
                                              rcases p6728_3 (m.d 0 4) (by simp) with h6738 | h6738
                                              · linarith only [h1, h6738, hlam]
                                              · linarith only [h6665, h6738, hlam]
                                            · have p6728_0 := h6728c.1
                                              have p6728_1 := h6728c.2.1
                                              have p6728_2 := h6728c.2.2.1
                                              have p6728_3 := h6728c.2.2.2
                                              linarith only [h0, h1, h6674, hc12, hc23, hlam, hphi, p6728_1]
                                            · have p6728_0 := h6728c.1
                                              have p6728_1 := h6728c.2.1
                                              have p6728_2 := h6728c.2.2.1
                                              have p6728_3 := h6728c.2.2.2
                                              linarith only [h0, h1, h6674, hc12, hc23, hlam, hphi, p6728_1]
                                            · have p6728_0 := h6728c.1
                                              have p6728_1 := h6728c.2.1
                                              have p6728_2 := h6728c.2.2.1
                                              have p6728_3 := h6728c.2.2.2
                                              linarith only [hlam, p6728_0]
                                            · have p6728_0 := h6728c.1
                                              have p6728_1 := h6728c.2.1
                                              have p6728_2 := h6728c.2.2.1
                                              have p6728_3 := h6728c.2.2.2
                                              linarith only [h0, h6152, h6439, h6674, hc12, hc23, hlam, hphi, p6728_1]
                                            · have p6728_0 := h6728c.1
                                              have p6728_1 := h6728c.2.1
                                              have p6728_2 := h6728c.2.2.1
                                              have p6728_3 := h6728c.2.2.2
                                              rcases p6728_3 (m.d 0 4) (by simp) with h6745 | h6745
                                              · linarith only [h6184, h6745, hlam]
                                              · linarith only [h6665, h6745, hlam]
                                            · have p6728_0 := h6728c.1
                                              have p6728_1 := h6728c.2.1
                                              have p6728_2 := h6728c.2.2.1
                                              have p6728_3 := h6728c.2.2.2
                                              linarith only [h0, h1, hc12, hc34, hlam, hphi, ht23, p6728_1]
                                            · have p6728_0 := h6728c.1
                                              have p6728_1 := h6728c.2.1
                                              have p6728_2 := h6728c.2.2.1
                                              have p6728_3 := h6728c.2.2.2
                                              linarith only [h6672, hlam, p6728_0]
                                            · have p6728_0 := h6728c.1
                                              have p6728_1 := h6728c.2.1
                                              have p6728_2 := h6728c.2.2.1
                                              have p6728_3 := h6728c.2.2.2
                                              linarith only [h6674, hlam, p6728_0]
                                            · have p6728_0 := h6728c.1
                                              have p6728_1 := h6728c.2.1
                                              have p6728_2 := h6728c.2.2.1
                                              have p6728_3 := h6728c.2.2.2
                                              linarith only [hlam, p6728_0]
                                            · have p6728_0 := h6728c.1
                                              have p6728_1 := h6728c.2.1
                                              have p6728_2 := h6728c.2.2.1
                                              have p6728_3 := h6728c.2.2.2
                                              linarith only [h6666, h6672, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p6728_1]
                                            · have p6728_0 := h6728c.1
                                              have p6728_1 := h6728c.2.1
                                              have p6728_2 := h6728c.2.2.1
                                              have p6728_3 := h6728c.2.2.2
                                              linarith only [h6665, hlam, p6728_0]
                                            · have p6728_0 := h6728c.1
                                              have p6728_1 := h6728c.2.1
                                              have p6728_2 := h6728c.2.2.1
                                              have p6728_3 := h6728c.2.2.2
                                              linarith only [h6673, hlam, p6728_0]
                                            · have p6728_0 := h6728c.1
                                              have p6728_1 := h6728c.2.1
                                              have p6728_2 := h6728c.2.2.1
                                              have p6728_3 := h6728c.2.2.2
                                              linarith only [h6676, hlam, p6728_0]
                                            · have p6728_0 := h6728c.1
                                              have p6728_1 := h6728c.2.1
                                              have p6728_2 := h6728c.2.2.1
                                              have p6728_3 := h6728c.2.2.2
                                              linarith only [h6677, hlam, p6728_0]
                                            · have p6728_0 := h6728c.1
                                              have p6728_1 := h6728c.2.1
                                              have p6728_2 := h6728c.2.2.1
                                              have p6728_3 := h6728c.2.2.2
                                              linarith only [hlam, p6728_0]
                                          · linarith only [h6727, hlam, p6678_0]
                                        · linarith only [h6184, h6726, hlam]
                                      · linarith only [h6152, h6725, hlam]
                                · have p6678_0 := h6678c.1
                                  have p6678_1 := h6678c.2.1
                                  have p6678_2 := h6678c.2.2.1
                                  have p6678_3 := h6678c.2.2.2
                                  rcases p6678_3 (m.d 0 2) (by simp) with h6761 | h6761
                                  · linarith only [h6186, h6761, hlam]
                                  · linarith only [h0, h6761, hlam]
                                · have p6678_0 := h6678c.1
                                  have p6678_1 := h6678c.2.1
                                  have p6678_2 := h6678c.2.2.1
                                  have p6678_3 := h6678c.2.2.2
                                  linarith only [h6675, hlam, p6678_0]
                                · have p6678_0 := h6678c.1
                                  have p6678_1 := h6678c.2.1
                                  have p6678_2 := h6678c.2.2.1
                                  have p6678_3 := h6678c.2.2.2
                                  linarith only [h6676, hlam, p6678_1]
                                · have p6678_0 := h6678c.1
                                  have p6678_1 := h6678c.2.1
                                  have p6678_2 := h6678c.2.2.1
                                  have p6678_3 := h6678c.2.2.2
                                  linarith only [hlam, p6678_0]
                              · linarith only [h0, h6152, h6184, h6439, h6665, h6674, h6677, hc12, hc23, hlam, hphi]
                            · linarith only [h0, h1, h6439, h6665, h6666, h6668, h6672, h6676, hc12, hc23, hlam, hphi]
                          · linarith only [h0, h1, h6439, h6666, h6672, h6675, hc12, hc35, hlam, hphi, ht23]
                        · linarith only [h6666, h6672, h6674, hlam]
                      · linarith only [h0, h1, h6665, h6673, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h6772 | h6772
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h6773 | h6773
                        · linarith only [h0, h1, h6672, h6773, hc12, hc23, hlam, hphi]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h6775 | h6775
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h6776 | h6776
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h6777 | h6777
                              · rcases h2bigk with h6778c | h6778c | h6778c | h6778c | h6778c | h6778c | h6778c | h6778c | h6778c | h6778c | h6778c | h6778c | h6778c | h6778c | h6778c | h6778c | h6778c | h6778c | h6778c | h6778c | h6778c | h6778c | h6778c | h6778c | h6778c
                                · have p6778_0 := h6778c.1
                                  have p6778_1 := h6778c.2.1
                                  have p6778_2 := h6778c.2.2.1
                                  have p6778_3 := h6778c.2.2.2
                                  linarith only [hlam, p6778_0]
                                · have p6778_0 := h6778c.1
                                  have p6778_1 := h6778c.2.1
                                  have p6778_2 := h6778c.2.2.1
                                  have p6778_3 := h6778c.2.2.2
                                  linarith only [h0, h1, h6668, hc12, hc24, hlam, hphi, p6778_1]
                                · have p6778_0 := h6778c.1
                                  have p6778_1 := h6778c.2.1
                                  have p6778_2 := h6778c.2.2.1
                                  have p6778_3 := h6778c.2.2.2
                                  linarith only [h6152, hlam, p6778_0]
                                · have p6778_0 := h6778c.1
                                  have p6778_1 := h6778c.2.1
                                  have p6778_2 := h6778c.2.2.1
                                  have p6778_3 := h6778c.2.2.2
                                  linarith only [h6184, hlam, p6778_0]
                                · have p6778_0 := h6778c.1
                                  have p6778_1 := h6778c.2.1
                                  have p6778_2 := h6778c.2.2.1
                                  have p6778_3 := h6778c.2.2.2
                                  linarith only [h6186, hlam, p6778_0]
                                · have p6778_0 := h6778c.1
                                  have p6778_1 := h6778c.2.1
                                  have p6778_2 := h6778c.2.2.1
                                  have p6778_3 := h6778c.2.2.2
                                  linarith only [h0, hlam, p6778_1]
                                · have p6778_0 := h6778c.1
                                  have p6778_1 := h6778c.2.1
                                  have p6778_2 := h6778c.2.2.1
                                  have p6778_3 := h6778c.2.2.2
                                  linarith only [hlam, p6778_0]
                                · have p6778_0 := h6778c.1
                                  have p6778_1 := h6778c.2.1
                                  have p6778_2 := h6778c.2.2.1
                                  have p6778_3 := h6778c.2.2.2
                                  linarith only [h6666, hlam, p6778_0]
                                · have p6778_0 := h6778c.1
                                  have p6778_1 := h6778c.2.1
                                  have p6778_2 := h6778c.2.2.1
                                  have p6778_3 := h6778c.2.2.2
                                  linarith only [h6668, hlam, p6778_0]
                                · have p6778_0 := h6778c.1
                                  have p6778_1 := h6778c.2.1
                                  have p6778_2 := h6778c.2.2.1
                                  have p6778_3 := h6778c.2.2.2
                                  linarith only [h6670, hlam, p6778_0]
                                · have p6778_0 := h6778c.1
                                  have p6778_1 := h6778c.2.1
                                  have p6778_2 := h6778c.2.2.1
                                  have p6778_3 := h6778c.2.2.2
                                  linarith only [h6773, hc02, hc34, hlam, hphi, ht23, p6778_1]
                                · have p6778_0 := h6778c.1
                                  have p6778_1 := h6778c.2.1
                                  have p6778_2 := h6778c.2.2.1
                                  have p6778_3 := h6778c.2.2.2
                                  linarith only [h6773, hc12, hc34, hlam, hphi, ht23, p6778_1]
                                · have p6778_0 := h6778c.1
                                  have p6778_1 := h6778c.2.1
                                  have p6778_2 := h6778c.2.2.1
                                  have p6778_3 := h6778c.2.2.2
                                  linarith only [hlam, p6778_0]
                                · have p6778_0 := h6778c.1
                                  have p6778_1 := h6778c.2.1
                                  have p6778_2 := h6778c.2.2.1
                                  have p6778_3 := h6778c.2.2.2
                                  linarith only [h6773, hlam, p6778_1]
                                · have p6778_0 := h6778c.1
                                  have p6778_1 := h6778c.2.1
                                  have p6778_2 := h6778c.2.2.1
                                  have p6778_3 := h6778c.2.2.2
                                  linarith only [h0, h6186, h6773, hc12, hc34, hlam, hphi, ht23, p6778_1]
                                · have p6778_0 := h6778c.1
                                  have p6778_1 := h6778c.2.1
                                  have p6778_2 := h6778c.2.2.1
                                  have p6778_3 := h6778c.2.2.2
                                  rcases p6778_3 (m.d 0 2) (by simp) with h6794 | h6794
                                  · linarith only [h6794, hlam, p6778_0]
                                  · rcases p6778_3 (m.d 1 2) (by simp) with h6796 | h6796
                                    · linarith only [h6668, h6796, hlam]
                                    · rcases p6778_3 (m.d 2 3) (by simp) with h6798 | h6798
                                      · linarith only [h6773, h6798, hlam]
                                      · linarith only [h6152, h6798, hlam]
                                · have p6778_0 := h6778c.1
                                  have p6778_1 := h6778c.2.1
                                  have p6778_2 := h6778c.2.2.1
                                  have p6778_3 := h6778c.2.2.2
                                  rcases p6778_3 (m.d 0 2) (by simp) with h6801 | h6801
                                  · linarith only [h6184, h6801, hlam]
                                  · linarith only [h0, h6801, hlam]
                                · have p6778_0 := h6778c.1
                                  have p6778_1 := h6778c.2.1
                                  have p6778_2 := h6778c.2.2.1
                                  have p6778_3 := h6778c.2.2.2
                                  linarith only [h0, h6152, h6773, hc12, hc34, hlam, hphi, ht23, p6778_1]
                                · have p6778_0 := h6778c.1
                                  have p6778_1 := h6778c.2.1
                                  have p6778_2 := h6778c.2.2.1
                                  have p6778_3 := h6778c.2.2.2
                                  linarith only [hlam, p6778_0]
                                · have p6778_0 := h6778c.1
                                  have p6778_1 := h6778c.2.1
                                  have p6778_2 := h6778c.2.2.1
                                  have p6778_3 := h6778c.2.2.2
                                  linarith only [h0, h6186, h6773, hc12, hc34, hlam, hphi, ht23, p6778_1]
                                · have p6778_0 := h6778c.1
                                  have p6778_1 := h6778c.2.1
                                  have p6778_2 := h6778c.2.2.1
                                  have p6778_3 := h6778c.2.2.2
                                  linarith only [h0, h6773, h6775, hc12, hc34, hlam, hphi, ht23, p6778_1]
                                · have p6778_0 := h6778c.1
                                  have p6778_1 := h6778c.2.1
                                  have p6778_2 := h6778c.2.2.1
                                  have p6778_3 := h6778c.2.2.2
                                  linarith only [h6773, h6775, hc12, hc34, hlam, hphi, ht23, p6778_1]
                                · have p6778_0 := h6778c.1
                                  have p6778_1 := h6778c.2.1
                                  have p6778_2 := h6778c.2.2.1
                                  have p6778_3 := h6778c.2.2.2
                                  linarith only [h6775, hlam, p6778_0]
                                · have p6778_0 := h6778c.1
                                  have p6778_1 := h6778c.2.1
                                  have p6778_2 := h6778c.2.2.1
                                  have p6778_3 := h6778c.2.2.2
                                  linarith only [h6776, hlam, p6778_1]
                                · have p6778_0 := h6778c.1
                                  have p6778_1 := h6778c.2.1
                                  have p6778_2 := h6778c.2.2.1
                                  have p6778_3 := h6778c.2.2.2
                                  linarith only [hlam, p6778_0]
                              · linarith only [h6665, h6773, h6775, h6777, hc04, hc35, hlam, hphi, ht0b, ht5b]
                            · linarith only [h1, h6665, h6668, h6776, hlam]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h6814 | h6814
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h6815 | h6815
                              · rcases h2bigk with h6816c | h6816c | h6816c | h6816c | h6816c | h6816c | h6816c | h6816c | h6816c | h6816c | h6816c | h6816c | h6816c | h6816c | h6816c | h6816c | h6816c | h6816c | h6816c | h6816c | h6816c | h6816c | h6816c | h6816c | h6816c
                                · have p6816_0 := h6816c.1
                                  have p6816_1 := h6816c.2.1
                                  have p6816_2 := h6816c.2.2.1
                                  have p6816_3 := h6816c.2.2.2
                                  linarith only [hlam, p6816_0]
                                · have p6816_0 := h6816c.1
                                  have p6816_1 := h6816c.2.1
                                  have p6816_2 := h6816c.2.2.1
                                  have p6816_3 := h6816c.2.2.2
                                  linarith only [h0, h1, h6668, hc12, hc24, hlam, hphi, p6816_1]
                                · have p6816_0 := h6816c.1
                                  have p6816_1 := h6816c.2.1
                                  have p6816_2 := h6816c.2.2.1
                                  have p6816_3 := h6816c.2.2.2
                                  linarith only [h6152, hlam, p6816_0]
                                · have p6816_0 := h6816c.1
                                  have p6816_1 := h6816c.2.1
                                  have p6816_2 := h6816c.2.2.1
                                  have p6816_3 := h6816c.2.2.2
                                  linarith only [h6184, hlam, p6816_0]
                                · have p6816_0 := h6816c.1
                                  have p6816_1 := h6816c.2.1
                                  have p6816_2 := h6816c.2.2.1
                                  have p6816_3 := h6816c.2.2.2
                                  linarith only [h6186, hlam, p6816_0]
                                · have p6816_0 := h6816c.1
                                  have p6816_1 := h6816c.2.1
                                  have p6816_2 := h6816c.2.2.1
                                  have p6816_3 := h6816c.2.2.2
                                  linarith only [h0, hlam, p6816_1]
                                · have p6816_0 := h6816c.1
                                  have p6816_1 := h6816c.2.1
                                  have p6816_2 := h6816c.2.2.1
                                  have p6816_3 := h6816c.2.2.2
                                  linarith only [hlam, p6816_0]
                                · have p6816_0 := h6816c.1
                                  have p6816_1 := h6816c.2.1
                                  have p6816_2 := h6816c.2.2.1
                                  have p6816_3 := h6816c.2.2.2
                                  linarith only [h6666, hlam, p6816_0]
                                · have p6816_0 := h6816c.1
                                  have p6816_1 := h6816c.2.1
                                  have p6816_2 := h6816c.2.2.1
                                  have p6816_3 := h6816c.2.2.2
                                  linarith only [h6668, hlam, p6816_0]
                                · have p6816_0 := h6816c.1
                                  have p6816_1 := h6816c.2.1
                                  have p6816_2 := h6816c.2.2.1
                                  have p6816_3 := h6816c.2.2.2
                                  linarith only [h6670, hlam, p6816_0]
                                · have p6816_0 := h6816c.1
                                  have p6816_1 := h6816c.2.1
                                  have p6816_2 := h6816c.2.2.1
                                  have p6816_3 := h6816c.2.2.2
                                  linarith only [h6775, h6815, hc02, hc34, hlam, hphi, ht23, p6816_1]
                                · have p6816_0 := h6816c.1
                                  have p6816_1 := h6816c.2.1
                                  have p6816_2 := h6816c.2.2.1
                                  have p6816_3 := h6816c.2.2.2
                                  linarith only [h6775, h6815, hc12, hc34, hlam, hphi, ht23, p6816_1]
                                · have p6816_0 := h6816c.1
                                  have p6816_1 := h6816c.2.1
                                  have p6816_2 := h6816c.2.2.1
                                  have p6816_3 := h6816c.2.2.2
                                  linarith only [hlam, p6816_0]
                                · have p6816_0 := h6816c.1
                                  have p6816_1 := h6816c.2.1
                                  have p6816_2 := h6816c.2.2.1
                                  have p6816_3 := h6816c.2.2.2
                                  linarith only [h6773, hlam, p6816_1]
                                · have p6816_0 := h6816c.1
                                  have p6816_1 := h6816c.2.1
                                  have p6816_2 := h6816c.2.2.1
                                  have p6816_3 := h6816c.2.2.2
                                  linarith only [h6775, hlam, p6816_1]
                                · have p6816_0 := h6816c.1
                                  have p6816_1 := h6816c.2.1
                                  have p6816_2 := h6816c.2.2.1
                                  have p6816_3 := h6816c.2.2.2
                                  rcases p6816_3 (m.d 0 2) (by simp) with h6832 | h6832
                                  · linarith only [h6832, hlam, p6816_0]
                                  · rcases p6816_3 (m.d 1 2) (by simp) with h6834 | h6834
                                    · linarith only [h6668, h6834, hlam]
                                    · rcases p6816_3 (m.d 2 3) (by simp) with h6836 | h6836
                                      · linarith only [h6773, h6836, hlam]
                                      · linarith only [h6152, h6836, hlam]
                                · have p6816_0 := h6816c.1
                                  have p6816_1 := h6816c.2.1
                                  have p6816_2 := h6816c.2.2.1
                                  have p6816_3 := h6816c.2.2.2
                                  rcases p6816_3 (m.d 0 2) (by simp) with h6839 | h6839
                                  · linarith only [h6184, h6839, hlam]
                                  · linarith only [h0, h6839, hlam]
                                · have p6816_0 := h6816c.1
                                  have p6816_1 := h6816c.2.1
                                  have p6816_2 := h6816c.2.2.1
                                  have p6816_3 := h6816c.2.2.2
                                  linarith only [h0, h6152, h6773, hc12, hc34, hlam, hphi, ht23, p6816_1]
                                · have p6816_0 := h6816c.1
                                  have p6816_1 := h6816c.2.1
                                  have p6816_2 := h6816c.2.2.1
                                  have p6816_3 := h6816c.2.2.2
                                  linarith only [hlam, p6816_0]
                                · have p6816_0 := h6816c.1
                                  have p6816_1 := h6816c.2.1
                                  have p6816_2 := h6816c.2.2.1
                                  have p6816_3 := h6816c.2.2.2
                                  linarith only [h0, h6186, h6773, hc12, hc34, hlam, hphi, ht23, p6816_1]
                                · have p6816_0 := h6816c.1
                                  have p6816_1 := h6816c.2.1
                                  have p6816_2 := h6816c.2.2.1
                                  have p6816_3 := h6816c.2.2.2
                                  rcases p6816_3 (m.d 0 2) (by simp) with h6845 | h6845
                                  · linarith only [h6845, hlam, p6816_0]
                                  · rcases p6816_3 (m.d 1 2) (by simp) with h6847 | h6847
                                    · linarith only [h6670, h6847, hlam]
                                    · rcases p6816_3 (m.d 2 3) (by simp) with h6849 | h6849
                                      · linarith only [h6775, h6849, hlam]
                                      · linarith only [h6152, h6849, hlam]
                                · have p6816_0 := h6816c.1
                                  have p6816_1 := h6816c.2.1
                                  have p6816_2 := h6816c.2.2.1
                                  have p6816_3 := h6816c.2.2.2
                                  rcases p6816_3 (m.d 0 2) (by simp) with h6852 | h6852
                                  · linarith only [h6186, h6852, hlam]
                                  · linarith only [h0, h6852, hlam]
                                · have p6816_0 := h6816c.1
                                  have p6816_1 := h6816c.2.1
                                  have p6816_2 := h6816c.2.2.1
                                  have p6816_3 := h6816c.2.2.2
                                  linarith only [h0, h6152, hc12, hc25, hlam, hphi, p6816_1]
                                · have p6816_0 := h6816c.1
                                  have p6816_1 := h6816c.2.1
                                  have p6816_2 := h6816c.2.2.1
                                  have p6816_3 := h6816c.2.2.2
                                  linarith only [h6814, hlam, p6816_1]
                                · have p6816_0 := h6816c.1
                                  have p6816_1 := h6816c.2.1
                                  have p6816_2 := h6816c.2.2.1
                                  have p6816_3 := h6816c.2.2.2
                                  linarith only [hlam, p6816_0]
                              · linarith only [h1, h6665, h6668, h6773, h6815, hlam]
                            · linarith only [h1, h6665, h6668, h6814, hlam]
                      · linarith only [h1, h6665, h6772, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h6861 | h6861
              · linarith only [h0, h6152, h6861, hlam]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h6863 | h6863
                · linarith only [h0, h1, h6665, h6863, hc24, hc45, hlam, hphi]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h6865 | h6865
                  · linarith only [h0, h6186, h6865, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h6867 | h6867
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h6868 | h6868
                      · linarith only [h0, h1, h6665, h6863, h6868, hc12, hc24, hlam, hphi]
                      · linarith only [h0, h1, h6868, hc12, hc45, hlam, hphi, ht23, ht34]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h6871 | h6871
                      · linarith only [h0, h1, h6665, h6863, h6871, hc12, hc24, hlam, hphi]
                      · linarith only [h0, h1, h6871, hc12, hc45, hlam, hphi, ht23, ht34]

end R2N4
