import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_2S35

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 8488000 in
set_option maxHeartbeats 8488000 in
theorem r1l7_10_12_23_L_I_L_I_H_I_s22 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg14396 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg16915 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg18815 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg20408 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg20409 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg20410 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg20411 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
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
  have h14396 := hg14396
  have h16915 := hg16915
  have h18815 := hg18815
  have h20408 := hg20408
  have h20409 := hg20409
  have h20410 := hg20410
  have h20411 := hg20411
  rcases m.htr 0 3 5 (by decide) (by decide) with h20412 | h20412
  · exact r1l7_10_12_23_L_I_L_I_H_I_s23 m hb0 hb2 hb3 h0 h14396 h16915 h18815 h20408 h20409 h20410 h20411 h20412
  · rcases m.htr 0 4 5 (by decide) (by decide) with h24182 | h24182
    · linarith only [h20411, h20412, h24182, hlam]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h24184 | h24184
      · rcases m.htr 1 2 4 (by decide) (by decide) with h24185 | h24185
        · rcases m.htr 1 2 5 (by decide) (by decide) with h24186 | h24186
          · rcases m.htr 1 3 4 (by decide) (by decide) with h24187 | h24187
            · rcases m.htr 1 3 5 (by decide) (by decide) with h24188 | h24188
              · rcases m.htr 1 4 5 (by decide) (by decide) with h24189 | h24189
                · rcases m.htr 2 3 4 (by decide) (by decide) with h24190 | h24190
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h24191 | h24191
                    · linarith only [h20408, h20412, h24191, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h24193 | h24193
                      · linarith only [h0, h16915, h20409, h24182, h24193, hc01, hc12, hlam, hphi]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h24195 | h24195
                        · linarith only [h16915, h20411, h20412, h24182, h24184, h24188, h24195, hc01, hc12, hlam, hphi]
                        · rcases h0bigk with h24197c | h24197c | h24197c | h24197c | h24197c | h24197c | h24197c | h24197c | h24197c | h24197c | h24197c | h24197c | h24197c | h24197c | h24197c | h24197c | h24197c | h24197c | h24197c | h24197c | h24197c | h24197c | h24197c | h24197c | h24197c
                          · have p24197_0 := h24197c.1
                            have p24197_1 := h24197c.2.1
                            have p24197_2 := h24197c.2.2.1
                            have p24197_3 := h24197c.2.2.2
                            linarith only [hlam, p24197_0]
                          · have p24197_0 := h24197c.1
                            have p24197_1 := h24197c.2.1
                            have p24197_2 := h24197c.2.2.1
                            have p24197_3 := h24197c.2.2.2
                            linarith only [h0, hlam, p24197_1]
                          · have p24197_0 := h24197c.1
                            have p24197_1 := h24197c.2.1
                            have p24197_2 := h24197c.2.2.1
                            have p24197_3 := h24197c.2.2.2
                            linarith only [h14396, hlam, p24197_0]
                          · have p24197_0 := h24197c.1
                            have p24197_1 := h24197c.2.1
                            have p24197_2 := h24197c.2.2.1
                            have p24197_3 := h24197c.2.2.2
                            linarith only [h16915, hlam, p24197_1]
                          · have p24197_0 := h24197c.1
                            have p24197_1 := h24197c.2.1
                            have p24197_2 := h24197c.2.2.1
                            have p24197_3 := h24197c.2.2.2
                            linarith only [h18815, hlam, p24197_1]
                          · have p24197_0 := h24197c.1
                            have p24197_1 := h24197c.2.1
                            have p24197_2 := h24197c.2.2.1
                            have p24197_3 := h24197c.2.2.2
                            rcases p24197_3 (m.d 0 1) (by simp) with h24203 | h24203
                            · linarith only [h0, h24203, hlam]
                            · rcases p24197_3 (m.d 0 2) (by simp) with h24205 | h24205
                              · rcases p24197_3 (m.d 0 3) (by simp) with h24206 | h24206
                                · linarith only [h20408, h24206, hlam]
                                · linarith only [h14396, h24206, hlam]
                              · linarith only [h0, h24205, hlam]
                          · have p24197_0 := h24197c.1
                            have p24197_1 := h24197c.2.1
                            have p24197_2 := h24197c.2.2.1
                            have p24197_3 := h24197c.2.2.2
                            linarith only [hlam, p24197_0]
                          · have p24197_0 := h24197c.1
                            have p24197_1 := h24197c.2.1
                            have p24197_2 := h24197c.2.2.1
                            have p24197_3 := h24197c.2.2.2
                            rcases p24197_3 (m.d 0 1) (by simp) with h24211 | h24211
                            · linarith only [h0, h24211, hlam]
                            · rcases p24197_3 (m.d 0 2) (by simp) with h24213 | h24213
                              · rcases p24197_3 (m.d 0 3) (by simp) with h24214 | h24214
                                · linarith only [h20408, h24214, hlam]
                                · rcases p24197_3 (m.d 0 4) (by simp) with h24216 | h24216
                                  · linarith only [h20409, h24216, hlam]
                                  · rcases p24197_3 (m.d 0 5) (by simp) with h24218 | h24218
                                    · linarith only [h20410, h24218, hlam]
                                    · linarith only [h20412, h24218, hlam]
                              · linarith only [h20408, h24213, hlam]
                          · have p24197_0 := h24197c.1
                            have p24197_1 := h24197c.2.1
                            have p24197_2 := h24197c.2.2.1
                            have p24197_3 := h24197c.2.2.2
                            rcases p24197_3 (m.d 0 1) (by simp) with h24222 | h24222
                            · linarith only [h0, h24222, hlam]
                            · rcases p24197_3 (m.d 0 2) (by simp) with h24224 | h24224
                              · rcases p24197_3 (m.d 0 3) (by simp) with h24225 | h24225
                                · linarith only [h20408, h24225, hlam]
                                · linarith only [h20411, h24225, hlam]
                              · linarith only [h20409, h24224, hlam]
                          · have p24197_0 := h24197c.1
                            have p24197_1 := h24197c.2.1
                            have p24197_2 := h24197c.2.2.1
                            have p24197_3 := h24197c.2.2.2
                            rcases p24197_3 (m.d 0 1) (by simp) with h24229 | h24229
                            · linarith only [h0, h24229, hlam]
                            · rcases p24197_3 (m.d 0 2) (by simp) with h24231 | h24231
                              · rcases p24197_3 (m.d 0 3) (by simp) with h24232 | h24232
                                · linarith only [h20408, h24232, hlam]
                                · rcases p24197_3 (m.d 0 4) (by simp) with h24234 | h24234
                                  · linarith only [h20409, h24234, hlam]
                                  · rcases p24197_3 (m.d 0 5) (by simp) with h24236 | h24236
                                    · linarith only [h20410, h24236, hlam]
                                    · rcases h2bigk with h24238c | h24238c | h24238c | h24238c | h24238c | h24238c | h24238c | h24238c | h24238c | h24238c | h24238c | h24238c | h24238c | h24238c | h24238c | h24238c | h24238c | h24238c | h24238c | h24238c | h24238c | h24238c | h24238c | h24238c | h24238c
                                      · have p24238_0 := h24238c.1
                                        have p24238_1 := h24238c.2.1
                                        have p24238_2 := h24238c.2.2.1
                                        have p24238_3 := h24238c.2.2.2
                                        linarith only [hlam, p24238_0]
                                      · have p24238_0 := h24238c.1
                                        have p24238_1 := h24238c.2.1
                                        have p24238_2 := h24238c.2.2.1
                                        have p24238_3 := h24238c.2.2.2
                                        linarith only [h0, hlam, p24238_1]
                                      · have p24238_0 := h24238c.1
                                        have p24238_1 := h24238c.2.1
                                        have p24238_2 := h24238c.2.2.1
                                        have p24238_3 := h24238c.2.2.2
                                        rcases p24238_3 (m.d 0 2) (by simp) with h24241 | h24241
                                        · rcases p24238_3 (m.d 1 2) (by simp) with h24242 | h24242
                                          · rcases p24238_3 (m.d 2 3) (by simp) with h24243 | h24243
                                            · linarith only [h24243, hlam, p24238_0]
                                            · rcases p24238_3 (m.d 2 4) (by simp) with h24245 | h24245
                                              · linarith only [h20409, h24245, hlam]
                                              · rcases p24238_3 (m.d 2 5) (by simp) with h24247 | h24247
                                                · linarith only [h20410, h24247, hlam]
                                                · linarith only [h24191, h24247, hlam]
                                          · linarith only [h24184, h24242, hlam]
                                        · linarith only [h24241, hlam, p24238_0]
                                      · have p24238_0 := h24238c.1
                                        have p24238_1 := h24238c.2.1
                                        have p24238_2 := h24238c.2.2.1
                                        have p24238_3 := h24238c.2.2.2
                                        rcases p24238_3 (m.d 0 2) (by simp) with h24252 | h24252
                                        · rcases p24238_3 (m.d 1 2) (by simp) with h24253 | h24253
                                          · rcases p24238_3 (m.d 2 3) (by simp) with h24254 | h24254
                                            · linarith only [h20408, h24254, hlam]
                                            · linarith only [h24190, h24254, hlam]
                                          · linarith only [h24185, h24253, hlam]
                                        · linarith only [h24252, hlam, p24238_0]
                                      · have p24238_0 := h24238c.1
                                        have p24238_1 := h24238c.2.1
                                        have p24238_2 := h24238c.2.2.1
                                        have p24238_3 := h24238c.2.2.2
                                        rcases p24238_3 (m.d 0 2) (by simp) with h24259 | h24259
                                        · rcases p24238_3 (m.d 1 2) (by simp) with h24260 | h24260
                                          · rcases p24238_3 (m.d 2 3) (by simp) with h24261 | h24261
                                            · linarith only [h20408, h24261, hlam]
                                            · rcases p24238_3 (m.d 2 4) (by simp) with h24263 | h24263
                                              · linarith only [h20409, h24263, hlam]
                                              · rcases p24238_3 (m.d 2 5) (by simp) with h24265 | h24265
                                                · linarith only [h24265, hlam, p24238_0]
                                                · rcases h3bigk with h24267c | h24267c | h24267c | h24267c | h24267c | h24267c | h24267c | h24267c | h24267c | h24267c | h24267c | h24267c | h24267c | h24267c | h24267c | h24267c | h24267c | h24267c | h24267c | h24267c | h24267c | h24267c | h24267c | h24267c | h24267c
                                                  · have p24267_0 := h24267c.1
                                                    have p24267_1 := h24267c.2.1
                                                    have p24267_2 := h24267c.2.2.1
                                                    have p24267_3 := h24267c.2.2.2
                                                    linarith only [hlam, p24267_0]
                                                  · have p24267_0 := h24267c.1
                                                    have p24267_1 := h24267c.2.1
                                                    have p24267_2 := h24267c.2.2.1
                                                    have p24267_3 := h24267c.2.2.2
                                                    linarith only [h14396, hlam, p24267_1]
                                                  · have p24267_0 := h24267c.1
                                                    have p24267_1 := h24267c.2.1
                                                    have p24267_2 := h24267c.2.2.1
                                                    have p24267_3 := h24267c.2.2.2
                                                    linarith only [h20412, h24184, h24187, h24189, h24195, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p24267_1]
                                                  · have p24267_0 := h24267c.1
                                                    have p24267_1 := h24267c.2.1
                                                    have p24267_2 := h24267c.2.2.1
                                                    have p24267_3 := h24267c.2.2.2
                                                    linarith only [h20412, h24184, h24187, h24189, h24195, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p24267_1]
                                                  · have p24267_0 := h24267c.1
                                                    have p24267_1 := h24267c.2.1
                                                    have p24267_2 := h24267c.2.2.1
                                                    have p24267_3 := h24267c.2.2.2
                                                    linarith only [h20412, hlam, p24267_0]
                                                  · have p24267_0 := h24267c.1
                                                    have p24267_1 := h24267c.2.1
                                                    have p24267_2 := h24267c.2.2.1
                                                    have p24267_3 := h24267c.2.2.2
                                                    linarith only [h14396, h24184, hc01, hc12, hlam, hphi, p24267_1]
                                                  · have p24267_0 := h24267c.1
                                                    have p24267_1 := h24267c.2.1
                                                    have p24267_2 := h24267c.2.2.1
                                                    have p24267_3 := h24267c.2.2.2
                                                    linarith only [hlam, p24267_0]
                                                  · have p24267_0 := h24267c.1
                                                    have p24267_1 := h24267c.2.1
                                                    have p24267_2 := h24267c.2.2.1
                                                    have p24267_3 := h24267c.2.2.2
                                                    linarith only [h24184, h24190, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p24267_1]
                                                  · have p24267_0 := h24267c.1
                                                    have p24267_1 := h24267c.2.1
                                                    have p24267_2 := h24267c.2.2.1
                                                    have p24267_3 := h24267c.2.2.2
                                                    rcases p24267_3 (m.d 0 3) (by simp) with h24276 | h24276
                                                    · linarith only [h14396, h24276, hlam]
                                                    · linarith only [h20411, h24276, hlam]
                                                  · have p24267_0 := h24267c.1
                                                    have p24267_1 := h24267c.2.1
                                                    have p24267_2 := h24267c.2.2.1
                                                    have p24267_3 := h24267c.2.2.2
                                                    linarith only [h20408, h20412, h24184, h24190, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p24267_1]
                                                  · have p24267_0 := h24267c.1
                                                    have p24267_1 := h24267c.2.1
                                                    have p24267_2 := h24267c.2.2.1
                                                    have p24267_3 := h24267c.2.2.2
                                                    linarith only [h20408, hlam, p24267_0]
                                                  · have p24267_0 := h24267c.1
                                                    have p24267_1 := h24267c.2.1
                                                    have p24267_2 := h24267c.2.2.1
                                                    have p24267_3 := h24267c.2.2.2
                                                    linarith only [h24184, hlam, p24267_0]
                                                  · have p24267_0 := h24267c.1
                                                    have p24267_1 := h24267c.2.1
                                                    have p24267_2 := h24267c.2.2.1
                                                    have p24267_3 := h24267c.2.2.2
                                                    linarith only [hlam, p24267_0]
                                                  · have p24267_0 := h24267c.1
                                                    have p24267_1 := h24267c.2.1
                                                    have p24267_2 := h24267c.2.2.1
                                                    have p24267_3 := h24267c.2.2.2
                                                    linarith only [h0, h20408, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p24267_1]
                                                  · have p24267_0 := h24267c.1
                                                    have p24267_1 := h24267c.2.1
                                                    have p24267_2 := h24267c.2.2.1
                                                    have p24267_3 := h24267c.2.2.2
                                                    linarith only [h24191, hlam, p24267_0]
                                                  · have p24267_0 := h24267c.1
                                                    have p24267_1 := h24267c.2.1
                                                    have p24267_2 := h24267c.2.2.1
                                                    have p24267_3 := h24267c.2.2.2
                                                    linarith only [h20411, hlam, p24267_0]
                                                  · have p24267_0 := h24267c.1
                                                    have p24267_1 := h24267c.2.1
                                                    have p24267_2 := h24267c.2.2.1
                                                    have p24267_3 := h24267c.2.2.2
                                                    linarith only [h24187, hlam, p24267_0]
                                                  · have p24267_0 := h24267c.1
                                                    have p24267_1 := h24267c.2.1
                                                    have p24267_2 := h24267c.2.2.1
                                                    have p24267_3 := h24267c.2.2.2
                                                    linarith only [h24190, hlam, p24267_0]
                                                  · have p24267_0 := h24267c.1
                                                    have p24267_1 := h24267c.2.1
                                                    have p24267_2 := h24267c.2.2.1
                                                    have p24267_3 := h24267c.2.2.2
                                                    linarith only [hlam, p24267_0]
                                                  · have p24267_0 := h24267c.1
                                                    have p24267_1 := h24267c.2.1
                                                    have p24267_2 := h24267c.2.2.1
                                                    have p24267_3 := h24267c.2.2.2
                                                    linarith only [h24195, hlam, p24267_1]
                                                  · have p24267_0 := h24267c.1
                                                    have p24267_1 := h24267c.2.1
                                                    have p24267_2 := h24267c.2.2.1
                                                    have p24267_3 := h24267c.2.2.2
                                                    linarith only [hc03, hc35, hlam, hphi, p24267_1]
                                                  · have p24267_0 := h24267c.1
                                                    have p24267_1 := h24267c.2.1
                                                    have p24267_2 := h24267c.2.2.1
                                                    have p24267_3 := h24267c.2.2.2
                                                    linarith only [h24188, hlam, p24267_0]
                                                  · have p24267_0 := h24267c.1
                                                    have p24267_1 := h24267c.2.1
                                                    have p24267_2 := h24267c.2.2.1
                                                    have p24267_3 := h24267c.2.2.2
                                                    linarith only [h24184, h24188, h24190, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p24267_1]
                                                  · have p24267_0 := h24267c.1
                                                    have p24267_1 := h24267c.2.1
                                                    have p24267_2 := h24267c.2.2.1
                                                    have p24267_3 := h24267c.2.2.2
                                                    linarith only [h24184, h24187, h24189, h24195, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p24267_1]
                                                  · have p24267_0 := h24267c.1
                                                    have p24267_1 := h24267c.2.1
                                                    have p24267_2 := h24267c.2.2.1
                                                    have p24267_3 := h24267c.2.2.2
                                                    linarith only [hlam, p24267_0]
                                          · linarith only [h24186, h24260, hlam]
                                        · linarith only [h24259, hlam, p24238_0]
                                      · have p24238_0 := h24238c.1
                                        have p24238_1 := h24238c.2.1
                                        have p24238_2 := h24238c.2.2.1
                                        have p24238_3 := h24238c.2.2.2
                                        linarith only [hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p24197_1, p24238_1]
                                      · have p24238_0 := h24238c.1
                                        have p24238_1 := h24238c.2.1
                                        have p24238_2 := h24238c.2.2.1
                                        have p24238_3 := h24238c.2.2.2
                                        linarith only [hlam, p24238_0]
                                      · have p24238_0 := h24238c.1
                                        have p24238_1 := h24238c.2.1
                                        have p24238_2 := h24238c.2.2.1
                                        have p24238_3 := h24238c.2.2.2
                                        rcases p24238_3 (m.d 0 2) (by simp) with h24299 | h24299
                                        · linarith only [h0, h24299, hlam]
                                        · linarith only [h20408, h24299, hlam]
                                      · have p24238_0 := h24238c.1
                                        have p24238_1 := h24238c.2.1
                                        have p24238_2 := h24238c.2.2.1
                                        have p24238_3 := h24238c.2.2.2
                                        rcases p24238_3 (m.d 0 2) (by simp) with h24302 | h24302
                                        · linarith only [h0, h24302, hlam]
                                        · linarith only [h20409, h24302, hlam]
                                      · have p24238_0 := h24238c.1
                                        have p24238_1 := h24238c.2.1
                                        have p24238_2 := h24238c.2.2.1
                                        have p24238_3 := h24238c.2.2.2
                                        rcases p24238_3 (m.d 0 2) (by simp) with h24305 | h24305
                                        · linarith only [h0, h24305, hlam]
                                        · linarith only [h20410, h24305, hlam]
                                      · have p24238_0 := h24238c.1
                                        have p24238_1 := h24238c.2.1
                                        have p24238_2 := h24238c.2.2.1
                                        have p24238_3 := h24238c.2.2.2
                                        linarith only [h20408, hlam, p24238_0]
                                      · have p24238_0 := h24238c.1
                                        have p24238_1 := h24238c.2.1
                                        have p24238_2 := h24238c.2.2.1
                                        have p24238_3 := h24238c.2.2.2
                                        linarith only [h24184, hlam, p24238_0]
                                      · have p24238_0 := h24238c.1
                                        have p24238_1 := h24238c.2.1
                                        have p24238_2 := h24238c.2.2.1
                                        have p24238_3 := h24238c.2.2.2
                                        linarith only [hlam, p24238_0]
                                      · have p24238_0 := h24238c.1
                                        have p24238_1 := h24238c.2.1
                                        have p24238_2 := h24238c.2.2.1
                                        have p24238_3 := h24238c.2.2.2
                                        linarith only [h20408, h20412, hc02, hc24, hlam, hphi, ht0b, ht45, ht5b, p24197_1, p24238_1]
                                      · have p24238_0 := h24238c.1
                                        have p24238_1 := h24238c.2.1
                                        have p24238_2 := h24238c.2.2.1
                                        have p24238_3 := h24238c.2.2.2
                                        linarith only [h24191, hlam, p24238_0]
                                      · have p24238_0 := h24238c.1
                                        have p24238_1 := h24238c.2.1
                                        have p24238_2 := h24238c.2.2.1
                                        have p24238_3 := h24238c.2.2.2
                                        linarith only [h20409, hlam, p24238_0]
                                      · have p24238_0 := h24238c.1
                                        have p24238_1 := h24238c.2.1
                                        have p24238_2 := h24238c.2.2.1
                                        have p24238_3 := h24238c.2.2.2
                                        linarith only [h24185, hlam, p24238_0]
                                      · have p24238_0 := h24238c.1
                                        have p24238_1 := h24238c.2.1
                                        have p24238_2 := h24238c.2.2.1
                                        have p24238_3 := h24238c.2.2.2
                                        linarith only [h24190, hlam, p24238_1]
                                      · have p24238_0 := h24238c.1
                                        have p24238_1 := h24238c.2.1
                                        have p24238_2 := h24238c.2.2.1
                                        have p24238_3 := h24238c.2.2.2
                                        linarith only [hlam, p24238_0]
                                      · have p24238_0 := h24238c.1
                                        have p24238_1 := h24238c.2.1
                                        have p24238_2 := h24238c.2.2.1
                                        have p24238_3 := h24238c.2.2.2
                                        linarith only [h24193, hlam, p24238_1]
                                      · have p24238_0 := h24238c.1
                                        have p24238_1 := h24238c.2.1
                                        have p24238_2 := h24238c.2.2.1
                                        have p24238_3 := h24238c.2.2.2
                                        linarith only [h20410, hlam, p24238_0]
                                      · have p24238_0 := h24238c.1
                                        have p24238_1 := h24238c.2.1
                                        have p24238_2 := h24238c.2.2.1
                                        have p24238_3 := h24238c.2.2.2
                                        linarith only [h24186, hlam, p24238_0]
                                      · have p24238_0 := h24238c.1
                                        have p24238_1 := h24238c.2.1
                                        have p24238_2 := h24238c.2.2.1
                                        have p24238_3 := h24238c.2.2.2
                                        linarith only [h0, h20410, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p24197_1, p24238_1]
                                      · have p24238_0 := h24238c.1
                                        have p24238_1 := h24238c.2.1
                                        have p24238_2 := h24238c.2.2.1
                                        have p24238_3 := h24238c.2.2.2
                                        linarith only [h0, h20410, h24190, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p24197_1, p24238_1]
                                      · have p24238_0 := h24238c.1
                                        have p24238_1 := h24238c.2.1
                                        have p24238_2 := h24238c.2.2.1
                                        have p24238_3 := h24238c.2.2.2
                                        linarith only [hlam, p24238_0]
                              · linarith only [h20410, h24231, hlam]
                          · have p24197_0 := h24197c.1
                            have p24197_1 := h24197c.2.1
                            have p24197_2 := h24197c.2.2.1
                            have p24197_3 := h24197c.2.2.2
                            linarith only [h20412, h24184, h24187, h24189, h24195, hc01, hc12, hlam, hphi, p24197_1]
                          · have p24197_0 := h24197c.1
                            have p24197_1 := h24197c.2.1
                            have p24197_2 := h24197c.2.2.1
                            have p24197_3 := h24197c.2.2.2
                            linarith only [h20408, hlam, p24197_1]
                          · have p24197_0 := h24197c.1
                            have p24197_1 := h24197c.2.1
                            have p24197_2 := h24197c.2.2.1
                            have p24197_3 := h24197c.2.2.2
                            linarith only [hlam, p24197_0]
                          · have p24197_0 := h24197c.1
                            have p24197_1 := h24197c.2.1
                            have p24197_2 := h24197c.2.2.1
                            have p24197_3 := h24197c.2.2.2
                            linarith only [h16915, h20412, h24184, h24187, h24189, h24195, hc01, hc12, hlam, hphi, p24197_1]
                          · have p24197_0 := h24197c.1
                            have p24197_1 := h24197c.2.1
                            have p24197_2 := h24197c.2.2.1
                            have p24197_3 := h24197c.2.2.2
                            linarith only [h20412, hlam, p24197_1]
                          · have p24197_0 := h24197c.1
                            have p24197_1 := h24197c.2.1
                            have p24197_2 := h24197c.2.2.1
                            have p24197_3 := h24197c.2.2.2
                            linarith only [h20411, h20412, h24184, h24187, h24189, h24195, hc01, hc12, hlam, hphi, p24197_1]
                          · have p24197_0 := h24197c.1
                            have p24197_1 := h24197c.2.1
                            have p24197_2 := h24197c.2.2.1
                            have p24197_3 := h24197c.2.2.2
                            linarith only [h20409, hlam, p24197_0]
                          · have p24197_0 := h24197c.1
                            have p24197_1 := h24197c.2.1
                            have p24197_2 := h24197c.2.2.1
                            have p24197_3 := h24197c.2.2.2
                            linarith only [h20411, hlam, p24197_0]
                          · have p24197_0 := h24197c.1
                            have p24197_1 := h24197c.2.1
                            have p24197_2 := h24197c.2.2.1
                            have p24197_3 := h24197c.2.2.2
                            linarith only [hlam, p24197_0]
                          · have p24197_0 := h24197c.1
                            have p24197_1 := h24197c.2.1
                            have p24197_2 := h24197c.2.2.1
                            have p24197_3 := h24197c.2.2.2
                            linarith only [h24182, hlam, p24197_0]
                          · have p24197_0 := h24197c.1
                            have p24197_1 := h24197c.2.1
                            have p24197_2 := h24197c.2.2.1
                            have p24197_3 := h24197c.2.2.2
                            linarith only [h20412, h24184, h24187, h24189, h24195, hc01, hc12, hlam, hphi, p24197_1]
                          · have p24197_0 := h24197c.1
                            have p24197_1 := h24197c.2.1
                            have p24197_2 := h24197c.2.2.1
                            have p24197_3 := h24197c.2.2.2
                            linarith only [h20410, hlam, p24197_1]
                          · have p24197_0 := h24197c.1
                            have p24197_1 := h24197c.2.1
                            have p24197_2 := h24197c.2.2.1
                            have p24197_3 := h24197c.2.2.2
                            linarith only [h14396, h20412, h24184, h24187, h24189, h24195, hc01, hc12, hlam, hphi, p24197_1]
                          · have p24197_0 := h24197c.1
                            have p24197_1 := h24197c.2.1
                            have p24197_2 := h24197c.2.2.1
                            have p24197_3 := h24197c.2.2.2
                            linarith only [h16915, h20412, h24184, h24187, h24189, h24195, hc01, hc12, hlam, hphi, p24197_1]
                          · have p24197_0 := h24197c.1
                            have p24197_1 := h24197c.2.1
                            have p24197_2 := h24197c.2.2.1
                            have p24197_3 := h24197c.2.2.2
                            linarith only [hlam, p24197_0]
                  · linarith only [h20411, h20412, h24190, hc23, hc35, hlam, hphi]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h24340 | h24340
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h24341 | h24341
                    · linarith only [h20408, h20412, h24341, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h24343 | h24343
                      · linarith only [h16915, h24189, h24343, hc01, hc24, hlam, hphi, ht12]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h24345 | h24345
                        · linarith only [h20410, h24189, h24340, h24341, h24345, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b]
                        · rcases h0bigk with h24347c | h24347c | h24347c | h24347c | h24347c | h24347c | h24347c | h24347c | h24347c | h24347c | h24347c | h24347c | h24347c | h24347c | h24347c | h24347c | h24347c | h24347c | h24347c | h24347c | h24347c | h24347c | h24347c | h24347c | h24347c
                          · have p24347_0 := h24347c.1
                            have p24347_1 := h24347c.2.1
                            have p24347_2 := h24347c.2.2.1
                            have p24347_3 := h24347c.2.2.2
                            linarith only [hlam, p24347_0]
                          · have p24347_0 := h24347c.1
                            have p24347_1 := h24347c.2.1
                            have p24347_2 := h24347c.2.2.1
                            have p24347_3 := h24347c.2.2.2
                            linarith only [h0, hlam, p24347_1]
                          · have p24347_0 := h24347c.1
                            have p24347_1 := h24347c.2.1
                            have p24347_2 := h24347c.2.2.1
                            have p24347_3 := h24347c.2.2.2
                            linarith only [h14396, hlam, p24347_0]
                          · have p24347_0 := h24347c.1
                            have p24347_1 := h24347c.2.1
                            have p24347_2 := h24347c.2.2.1
                            have p24347_3 := h24347c.2.2.2
                            linarith only [h16915, hlam, p24347_1]
                          · have p24347_0 := h24347c.1
                            have p24347_1 := h24347c.2.1
                            have p24347_2 := h24347c.2.2.1
                            have p24347_3 := h24347c.2.2.2
                            linarith only [h18815, hlam, p24347_1]
                          · have p24347_0 := h24347c.1
                            have p24347_1 := h24347c.2.1
                            have p24347_2 := h24347c.2.2.1
                            have p24347_3 := h24347c.2.2.2
                            rcases p24347_3 (m.d 0 1) (by simp) with h24353 | h24353
                            · linarith only [h0, h24353, hlam]
                            · rcases p24347_3 (m.d 0 2) (by simp) with h24355 | h24355
                              · rcases p24347_3 (m.d 0 3) (by simp) with h24356 | h24356
                                · linarith only [h20408, h24356, hlam]
                                · linarith only [h14396, h24356, hlam]
                              · linarith only [h0, h24355, hlam]
                          · have p24347_0 := h24347c.1
                            have p24347_1 := h24347c.2.1
                            have p24347_2 := h24347c.2.2.1
                            have p24347_3 := h24347c.2.2.2
                            linarith only [hlam, p24347_0]
                          · have p24347_0 := h24347c.1
                            have p24347_1 := h24347c.2.1
                            have p24347_2 := h24347c.2.2.1
                            have p24347_3 := h24347c.2.2.2
                            rcases p24347_3 (m.d 0 1) (by simp) with h24361 | h24361
                            · linarith only [h0, h24361, hlam]
                            · rcases p24347_3 (m.d 0 2) (by simp) with h24363 | h24363
                              · rcases p24347_3 (m.d 0 3) (by simp) with h24364 | h24364
                                · linarith only [h20408, h24364, hlam]
                                · rcases p24347_3 (m.d 0 4) (by simp) with h24366 | h24366
                                  · linarith only [h20409, h24366, hlam]
                                  · rcases p24347_3 (m.d 0 5) (by simp) with h24368 | h24368
                                    · linarith only [h20410, h24368, hlam]
                                    · linarith only [h20412, h24368, hlam]
                              · linarith only [h20408, h24363, hlam]
                          · have p24347_0 := h24347c.1
                            have p24347_1 := h24347c.2.1
                            have p24347_2 := h24347c.2.2.1
                            have p24347_3 := h24347c.2.2.2
                            rcases p24347_3 (m.d 0 1) (by simp) with h24372 | h24372
                            · linarith only [h0, h24372, hlam]
                            · rcases p24347_3 (m.d 0 2) (by simp) with h24374 | h24374
                              · rcases p24347_3 (m.d 0 3) (by simp) with h24375 | h24375
                                · linarith only [h20408, h24375, hlam]
                                · linarith only [h20411, h24375, hlam]
                              · linarith only [h20409, h24374, hlam]
                          · have p24347_0 := h24347c.1
                            have p24347_1 := h24347c.2.1
                            have p24347_2 := h24347c.2.2.1
                            have p24347_3 := h24347c.2.2.2
                            rcases p24347_3 (m.d 0 1) (by simp) with h24379 | h24379
                            · linarith only [h0, h24379, hlam]
                            · rcases p24347_3 (m.d 0 2) (by simp) with h24381 | h24381
                              · rcases p24347_3 (m.d 0 3) (by simp) with h24382 | h24382
                                · linarith only [h20408, h24382, hlam]
                                · rcases p24347_3 (m.d 0 4) (by simp) with h24384 | h24384
                                  · linarith only [h20409, h24384, hlam]
                                  · rcases p24347_3 (m.d 0 5) (by simp) with h24386 | h24386
                                    · linarith only [h20410, h24386, hlam]
                                    · rcases h2bigk with h24388c | h24388c | h24388c | h24388c | h24388c | h24388c | h24388c | h24388c | h24388c | h24388c | h24388c | h24388c | h24388c | h24388c | h24388c | h24388c | h24388c | h24388c | h24388c | h24388c | h24388c | h24388c | h24388c | h24388c | h24388c
                                      · have p24388_0 := h24388c.1
                                        have p24388_1 := h24388c.2.1
                                        have p24388_2 := h24388c.2.2.1
                                        have p24388_3 := h24388c.2.2.2
                                        linarith only [hlam, p24388_0]
                                      · have p24388_0 := h24388c.1
                                        have p24388_1 := h24388c.2.1
                                        have p24388_2 := h24388c.2.2.1
                                        have p24388_3 := h24388c.2.2.2
                                        linarith only [h0, hlam, p24388_1]
                                      · have p24388_0 := h24388c.1
                                        have p24388_1 := h24388c.2.1
                                        have p24388_2 := h24388c.2.2.1
                                        have p24388_3 := h24388c.2.2.2
                                        rcases p24388_3 (m.d 0 2) (by simp) with h24391 | h24391
                                        · rcases p24388_3 (m.d 1 2) (by simp) with h24392 | h24392
                                          · rcases p24388_3 (m.d 2 3) (by simp) with h24393 | h24393
                                            · linarith only [h24393, hlam, p24388_0]
                                            · rcases p24388_3 (m.d 2 4) (by simp) with h24395 | h24395
                                              · linarith only [h20409, h24395, hlam]
                                              · rcases p24388_3 (m.d 2 5) (by simp) with h24397 | h24397
                                                · linarith only [h20410, h24397, hlam]
                                                · linarith only [h24341, h24397, hlam]
                                          · linarith only [h24184, h24392, hlam]
                                        · linarith only [h24391, hlam, p24388_0]
                                      · have p24388_0 := h24388c.1
                                        have p24388_1 := h24388c.2.1
                                        have p24388_2 := h24388c.2.2.1
                                        have p24388_3 := h24388c.2.2.2
                                        rcases p24388_3 (m.d 0 2) (by simp) with h24402 | h24402
                                        · rcases p24388_3 (m.d 1 2) (by simp) with h24403 | h24403
                                          · rcases p24388_3 (m.d 2 3) (by simp) with h24404 | h24404
                                            · linarith only [h20408, h24404, hlam]
                                            · linarith only [h24340, h24404, hlam]
                                          · linarith only [h24185, h24403, hlam]
                                        · linarith only [h24402, hlam, p24388_0]
                                      · have p24388_0 := h24388c.1
                                        have p24388_1 := h24388c.2.1
                                        have p24388_2 := h24388c.2.2.1
                                        have p24388_3 := h24388c.2.2.2
                                        rcases p24388_3 (m.d 0 2) (by simp) with h24409 | h24409
                                        · rcases p24388_3 (m.d 1 2) (by simp) with h24410 | h24410
                                          · rcases p24388_3 (m.d 2 3) (by simp) with h24411 | h24411
                                            · linarith only [h20408, h24411, hlam]
                                            · rcases p24388_3 (m.d 2 4) (by simp) with h24413 | h24413
                                              · linarith only [h20409, h24413, hlam]
                                              · rcases p24388_3 (m.d 2 5) (by simp) with h24415 | h24415
                                                · linarith only [h24415, hlam, p24388_0]
                                                · rcases h3bigk with h24417c | h24417c | h24417c | h24417c | h24417c | h24417c | h24417c | h24417c | h24417c | h24417c | h24417c | h24417c | h24417c | h24417c | h24417c | h24417c | h24417c | h24417c | h24417c | h24417c | h24417c | h24417c | h24417c | h24417c | h24417c
                                                  · have p24417_0 := h24417c.1
                                                    have p24417_1 := h24417c.2.1
                                                    have p24417_2 := h24417c.2.2.1
                                                    have p24417_3 := h24417c.2.2.2
                                                    linarith only [hlam, p24417_0]
                                                  · have p24417_0 := h24417c.1
                                                    have p24417_1 := h24417c.2.1
                                                    have p24417_2 := h24417c.2.2.1
                                                    have p24417_3 := h24417c.2.2.2
                                                    linarith only [h14396, hlam, p24417_1]
                                                  · have p24417_0 := h24417c.1
                                                    have p24417_1 := h24417c.2.1
                                                    have p24417_2 := h24417c.2.2.1
                                                    have p24417_3 := h24417c.2.2.2
                                                    linarith only [h0, h20412, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p24347_1, p24417_1]
                                                  · have p24417_0 := h24417c.1
                                                    have p24417_1 := h24417c.2.1
                                                    have p24417_2 := h24417c.2.2.1
                                                    have p24417_3 := h24417c.2.2.2
                                                    linarith only [h0, h20412, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p24347_1, p24417_1]
                                                  · have p24417_0 := h24417c.1
                                                    have p24417_1 := h24417c.2.1
                                                    have p24417_2 := h24417c.2.2.1
                                                    have p24417_3 := h24417c.2.2.2
                                                    linarith only [h20412, hlam, p24417_0]
                                                  · have p24417_0 := h24417c.1
                                                    have p24417_1 := h24417c.2.1
                                                    have p24417_2 := h24417c.2.2.1
                                                    have p24417_3 := h24417c.2.2.2
                                                    linarith only [h14396, h24184, hc01, hc12, hlam, hphi, p24417_1]
                                                  · have p24417_0 := h24417c.1
                                                    have p24417_1 := h24417c.2.1
                                                    have p24417_2 := h24417c.2.2.1
                                                    have p24417_3 := h24417c.2.2.2
                                                    linarith only [hlam, p24417_0]
                                                  · have p24417_0 := h24417c.1
                                                    have p24417_1 := h24417c.2.1
                                                    have p24417_2 := h24417c.2.2.1
                                                    have p24417_3 := h24417c.2.2.2
                                                    linarith only [h24184, h24340, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p24417_1]
                                                  · have p24417_0 := h24417c.1
                                                    have p24417_1 := h24417c.2.1
                                                    have p24417_2 := h24417c.2.2.1
                                                    have p24417_3 := h24417c.2.2.2
                                                    rcases p24417_3 (m.d 0 3) (by simp) with h24426 | h24426
                                                    · linarith only [h14396, h24426, hlam]
                                                    · linarith only [h20411, h24426, hlam]
                                                  · have p24417_0 := h24417c.1
                                                    have p24417_1 := h24417c.2.1
                                                    have p24417_2 := h24417c.2.2.1
                                                    have p24417_3 := h24417c.2.2.2
                                                    linarith only [h20408, h20412, h24184, h24340, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p24417_1]
                                                  · have p24417_0 := h24417c.1
                                                    have p24417_1 := h24417c.2.1
                                                    have p24417_2 := h24417c.2.2.1
                                                    have p24417_3 := h24417c.2.2.2
                                                    linarith only [h20408, hlam, p24417_0]
                                                  · have p24417_0 := h24417c.1
                                                    have p24417_1 := h24417c.2.1
                                                    have p24417_2 := h24417c.2.2.1
                                                    have p24417_3 := h24417c.2.2.2
                                                    linarith only [h24184, hlam, p24417_0]
                                                  · have p24417_0 := h24417c.1
                                                    have p24417_1 := h24417c.2.1
                                                    have p24417_2 := h24417c.2.2.1
                                                    have p24417_3 := h24417c.2.2.2
                                                    linarith only [hlam, p24417_0]
                                                  · have p24417_0 := h24417c.1
                                                    have p24417_1 := h24417c.2.1
                                                    have p24417_2 := h24417c.2.2.1
                                                    have p24417_3 := h24417c.2.2.2
                                                    linarith only [h0, h20408, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p24417_1]
                                                  · have p24417_0 := h24417c.1
                                                    have p24417_1 := h24417c.2.1
                                                    have p24417_2 := h24417c.2.2.1
                                                    have p24417_3 := h24417c.2.2.2
                                                    linarith only [h24341, hlam, p24417_0]
                                                  · have p24417_0 := h24417c.1
                                                    have p24417_1 := h24417c.2.1
                                                    have p24417_2 := h24417c.2.2.1
                                                    have p24417_3 := h24417c.2.2.2
                                                    linarith only [h20411, hlam, p24417_0]
                                                  · have p24417_0 := h24417c.1
                                                    have p24417_1 := h24417c.2.1
                                                    have p24417_2 := h24417c.2.2.1
                                                    have p24417_3 := h24417c.2.2.2
                                                    linarith only [h24187, hlam, p24417_0]
                                                  · have p24417_0 := h24417c.1
                                                    have p24417_1 := h24417c.2.1
                                                    have p24417_2 := h24417c.2.2.1
                                                    have p24417_3 := h24417c.2.2.2
                                                    linarith only [h24340, hlam, p24417_0]
                                                  · have p24417_0 := h24417c.1
                                                    have p24417_1 := h24417c.2.1
                                                    have p24417_2 := h24417c.2.2.1
                                                    have p24417_3 := h24417c.2.2.2
                                                    linarith only [hlam, p24417_0]
                                                  · have p24417_0 := h24417c.1
                                                    have p24417_1 := h24417c.2.1
                                                    have p24417_2 := h24417c.2.2.1
                                                    have p24417_3 := h24417c.2.2.2
                                                    linarith only [h24345, hlam, p24417_1]
                                                  · have p24417_0 := h24417c.1
                                                    have p24417_1 := h24417c.2.1
                                                    have p24417_2 := h24417c.2.2.1
                                                    have p24417_3 := h24417c.2.2.2
                                                    linarith only [hc03, hc35, hlam, hphi, p24417_1]
                                                  · have p24417_0 := h24417c.1
                                                    have p24417_1 := h24417c.2.1
                                                    have p24417_2 := h24417c.2.2.1
                                                    have p24417_3 := h24417c.2.2.2
                                                    linarith only [h24188, hlam, p24417_0]
                                                  · have p24417_0 := h24417c.1
                                                    have p24417_1 := h24417c.2.1
                                                    have p24417_2 := h24417c.2.2.1
                                                    have p24417_3 := h24417c.2.2.2
                                                    linarith only [h24184, h24188, h24340, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p24417_1]
                                                  · have p24417_0 := h24417c.1
                                                    have p24417_1 := h24417c.2.1
                                                    have p24417_2 := h24417c.2.2.1
                                                    have p24417_3 := h24417c.2.2.2
                                                    linarith only [h24184, h24188, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p24417_1]
                                                  · have p24417_0 := h24417c.1
                                                    have p24417_1 := h24417c.2.1
                                                    have p24417_2 := h24417c.2.2.1
                                                    have p24417_3 := h24417c.2.2.2
                                                    linarith only [hlam, p24417_0]
                                          · linarith only [h24186, h24410, hlam]
                                        · linarith only [h24409, hlam, p24388_0]
                                      · have p24388_0 := h24388c.1
                                        have p24388_1 := h24388c.2.1
                                        have p24388_2 := h24388c.2.2.1
                                        have p24388_3 := h24388c.2.2.2
                                        linarith only [hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p24347_1, p24388_1]
                                      · have p24388_0 := h24388c.1
                                        have p24388_1 := h24388c.2.1
                                        have p24388_2 := h24388c.2.2.1
                                        have p24388_3 := h24388c.2.2.2
                                        linarith only [hlam, p24388_0]
                                      · have p24388_0 := h24388c.1
                                        have p24388_1 := h24388c.2.1
                                        have p24388_2 := h24388c.2.2.1
                                        have p24388_3 := h24388c.2.2.2
                                        rcases p24388_3 (m.d 0 2) (by simp) with h24449 | h24449
                                        · linarith only [h0, h24449, hlam]
                                        · linarith only [h20408, h24449, hlam]
                                      · have p24388_0 := h24388c.1
                                        have p24388_1 := h24388c.2.1
                                        have p24388_2 := h24388c.2.2.1
                                        have p24388_3 := h24388c.2.2.2
                                        rcases p24388_3 (m.d 0 2) (by simp) with h24452 | h24452
                                        · linarith only [h0, h24452, hlam]
                                        · linarith only [h20409, h24452, hlam]
                                      · have p24388_0 := h24388c.1
                                        have p24388_1 := h24388c.2.1
                                        have p24388_2 := h24388c.2.2.1
                                        have p24388_3 := h24388c.2.2.2
                                        rcases p24388_3 (m.d 0 2) (by simp) with h24455 | h24455
                                        · linarith only [h0, h24455, hlam]
                                        · linarith only [h20410, h24455, hlam]
                                      · have p24388_0 := h24388c.1
                                        have p24388_1 := h24388c.2.1
                                        have p24388_2 := h24388c.2.2.1
                                        have p24388_3 := h24388c.2.2.2
                                        linarith only [h20408, hlam, p24388_0]
                                      · have p24388_0 := h24388c.1
                                        have p24388_1 := h24388c.2.1
                                        have p24388_2 := h24388c.2.2.1
                                        have p24388_3 := h24388c.2.2.2
                                        linarith only [h24184, hlam, p24388_0]
                                      · have p24388_0 := h24388c.1
                                        have p24388_1 := h24388c.2.1
                                        have p24388_2 := h24388c.2.2.1
                                        have p24388_3 := h24388c.2.2.2
                                        linarith only [hlam, p24388_0]
                                      · have p24388_0 := h24388c.1
                                        have p24388_1 := h24388c.2.1
                                        have p24388_2 := h24388c.2.2.1
                                        have p24388_3 := h24388c.2.2.2
                                        linarith only [h20408, h20412, hc02, hc24, hlam, hphi, ht0b, ht45, ht5b, p24347_1, p24388_1]
                                      · have p24388_0 := h24388c.1
                                        have p24388_1 := h24388c.2.1
                                        have p24388_2 := h24388c.2.2.1
                                        have p24388_3 := h24388c.2.2.2
                                        linarith only [h24341, hlam, p24388_0]
                                      · have p24388_0 := h24388c.1
                                        have p24388_1 := h24388c.2.1
                                        have p24388_2 := h24388c.2.2.1
                                        have p24388_3 := h24388c.2.2.2
                                        linarith only [h20409, hlam, p24388_0]
                                      · have p24388_0 := h24388c.1
                                        have p24388_1 := h24388c.2.1
                                        have p24388_2 := h24388c.2.2.1
                                        have p24388_3 := h24388c.2.2.2
                                        linarith only [h24185, hlam, p24388_0]
                                      · have p24388_0 := h24388c.1
                                        have p24388_1 := h24388c.2.1
                                        have p24388_2 := h24388c.2.2.1
                                        have p24388_3 := h24388c.2.2.2
                                        linarith only [h24340, hlam, p24388_1]
                                      · have p24388_0 := h24388c.1
                                        have p24388_1 := h24388c.2.1
                                        have p24388_2 := h24388c.2.2.1
                                        have p24388_3 := h24388c.2.2.2
                                        linarith only [hlam, p24388_0]
                                      · have p24388_0 := h24388c.1
                                        have p24388_1 := h24388c.2.1
                                        have p24388_2 := h24388c.2.2.1
                                        have p24388_3 := h24388c.2.2.2
                                        linarith only [h24343, hlam, p24388_1]
                                      · have p24388_0 := h24388c.1
                                        have p24388_1 := h24388c.2.1
                                        have p24388_2 := h24388c.2.2.1
                                        have p24388_3 := h24388c.2.2.2
                                        linarith only [h20410, hlam, p24388_0]
                                      · have p24388_0 := h24388c.1
                                        have p24388_1 := h24388c.2.1
                                        have p24388_2 := h24388c.2.2.1
                                        have p24388_3 := h24388c.2.2.2
                                        linarith only [h24186, hlam, p24388_0]
                                      · have p24388_0 := h24388c.1
                                        have p24388_1 := h24388c.2.1
                                        have p24388_2 := h24388c.2.2.1
                                        have p24388_3 := h24388c.2.2.2
                                        linarith only [h0, h20410, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p24347_1, p24388_1]
                                      · have p24388_0 := h24388c.1
                                        have p24388_1 := h24388c.2.1
                                        have p24388_2 := h24388c.2.2.1
                                        have p24388_3 := h24388c.2.2.2
                                        linarith only [h0, h20410, h24340, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p24347_1, p24388_1]
                                      · have p24388_0 := h24388c.1
                                        have p24388_1 := h24388c.2.1
                                        have p24388_2 := h24388c.2.2.1
                                        have p24388_3 := h24388c.2.2.2
                                        linarith only [hlam, p24388_0]
                              · linarith only [h20410, h24381, hlam]
                          · have p24347_0 := h24347c.1
                            have p24347_1 := h24347c.2.1
                            have p24347_2 := h24347c.2.2.1
                            have p24347_3 := h24347c.2.2.2
                            linarith only [h20412, h24184, h24188, hc01, hc12, hlam, hphi, p24347_1]
                          · have p24347_0 := h24347c.1
                            have p24347_1 := h24347c.2.1
                            have p24347_2 := h24347c.2.2.1
                            have p24347_3 := h24347c.2.2.2
                            linarith only [h20408, hlam, p24347_1]
                          · have p24347_0 := h24347c.1
                            have p24347_1 := h24347c.2.1
                            have p24347_2 := h24347c.2.2.1
                            have p24347_3 := h24347c.2.2.2
                            linarith only [hlam, p24347_0]
                          · have p24347_0 := h24347c.1
                            have p24347_1 := h24347c.2.1
                            have p24347_2 := h24347c.2.2.1
                            have p24347_3 := h24347c.2.2.2
                            linarith only [h16915, h20412, h24184, h24188, hc01, hc12, hlam, hphi, p24347_1]
                          · have p24347_0 := h24347c.1
                            have p24347_1 := h24347c.2.1
                            have p24347_2 := h24347c.2.2.1
                            have p24347_3 := h24347c.2.2.2
                            linarith only [h20412, hlam, p24347_1]
                          · have p24347_0 := h24347c.1
                            have p24347_1 := h24347c.2.1
                            have p24347_2 := h24347c.2.2.1
                            have p24347_3 := h24347c.2.2.2
                            linarith only [h20411, h20412, h24184, h24188, hc01, hc12, hlam, hphi, p24347_1]
                          · have p24347_0 := h24347c.1
                            have p24347_1 := h24347c.2.1
                            have p24347_2 := h24347c.2.2.1
                            have p24347_3 := h24347c.2.2.2
                            linarith only [h20409, hlam, p24347_0]
                          · have p24347_0 := h24347c.1
                            have p24347_1 := h24347c.2.1
                            have p24347_2 := h24347c.2.2.1
                            have p24347_3 := h24347c.2.2.2
                            linarith only [h20411, hlam, p24347_0]
                          · have p24347_0 := h24347c.1
                            have p24347_1 := h24347c.2.1
                            have p24347_2 := h24347c.2.2.1
                            have p24347_3 := h24347c.2.2.2
                            linarith only [hlam, p24347_0]
                          · have p24347_0 := h24347c.1
                            have p24347_1 := h24347c.2.1
                            have p24347_2 := h24347c.2.2.1
                            have p24347_3 := h24347c.2.2.2
                            linarith only [h24182, hlam, p24347_0]
                          · have p24347_0 := h24347c.1
                            have p24347_1 := h24347c.2.1
                            have p24347_2 := h24347c.2.2.1
                            have p24347_3 := h24347c.2.2.2
                            linarith only [h20412, h24184, h24188, hc01, hc12, hlam, hphi, p24347_1]
                          · have p24347_0 := h24347c.1
                            have p24347_1 := h24347c.2.1
                            have p24347_2 := h24347c.2.2.1
                            have p24347_3 := h24347c.2.2.2
                            linarith only [h20410, hlam, p24347_1]
                          · have p24347_0 := h24347c.1
                            have p24347_1 := h24347c.2.1
                            have p24347_2 := h24347c.2.2.1
                            have p24347_3 := h24347c.2.2.2
                            linarith only [h14396, h20412, h24184, h24188, hc01, hc12, hlam, hphi, p24347_1]
                          · have p24347_0 := h24347c.1
                            have p24347_1 := h24347c.2.1
                            have p24347_2 := h24347c.2.2.1
                            have p24347_3 := h24347c.2.2.2
                            linarith only [h16915, h20412, h24184, h24188, hc01, hc12, hlam, hphi, p24347_1]
                          · have p24347_0 := h24347c.1
                            have p24347_1 := h24347c.2.1
                            have p24347_2 := h24347c.2.2.1
                            have p24347_3 := h24347c.2.2.2
                            linarith only [hlam, p24347_0]
                  · linarith only [h20411, h20412, h24184, h24188, h24340, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h24490 | h24490
                · linarith only [h16915, h24182, h24187, h24188, h24490, hc01, hc35, hlam, hphi, ht12, ht23]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h24492 | h24492
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h24493 | h24493
                    · linarith only [h14396, h24188, h24493, hc01, hc23, hlam, hphi, ht12]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h24495 | h24495
                      · linarith only [h16915, h24490, h24495, hc01, hc24, hlam, hphi, ht12]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h24497 | h24497
                        · linarith only [h16915, h24490, h24497, hc01, hc34, hlam, hphi, ht12, ht23]
                        · rcases h0bigk with h24499c | h24499c | h24499c | h24499c | h24499c | h24499c | h24499c | h24499c | h24499c | h24499c | h24499c | h24499c | h24499c | h24499c | h24499c | h24499c | h24499c | h24499c | h24499c | h24499c | h24499c | h24499c | h24499c | h24499c | h24499c
                          · have p24499_0 := h24499c.1
                            have p24499_1 := h24499c.2.1
                            have p24499_2 := h24499c.2.2.1
                            have p24499_3 := h24499c.2.2.2
                            linarith only [hlam, p24499_0]
                          · have p24499_0 := h24499c.1
                            have p24499_1 := h24499c.2.1
                            have p24499_2 := h24499c.2.2.1
                            have p24499_3 := h24499c.2.2.2
                            linarith only [h0, hlam, p24499_1]
                          · have p24499_0 := h24499c.1
                            have p24499_1 := h24499c.2.1
                            have p24499_2 := h24499c.2.2.1
                            have p24499_3 := h24499c.2.2.2
                            linarith only [h14396, hlam, p24499_0]
                          · have p24499_0 := h24499c.1
                            have p24499_1 := h24499c.2.1
                            have p24499_2 := h24499c.2.2.1
                            have p24499_3 := h24499c.2.2.2
                            linarith only [h16915, hlam, p24499_1]
                          · have p24499_0 := h24499c.1
                            have p24499_1 := h24499c.2.1
                            have p24499_2 := h24499c.2.2.1
                            have p24499_3 := h24499c.2.2.2
                            linarith only [h18815, hlam, p24499_1]
                          · have p24499_0 := h24499c.1
                            have p24499_1 := h24499c.2.1
                            have p24499_2 := h24499c.2.2.1
                            have p24499_3 := h24499c.2.2.2
                            rcases p24499_3 (m.d 0 1) (by simp) with h24505 | h24505
                            · linarith only [h0, h24505, hlam]
                            · rcases p24499_3 (m.d 0 2) (by simp) with h24507 | h24507
                              · rcases p24499_3 (m.d 0 3) (by simp) with h24508 | h24508
                                · linarith only [h20408, h24508, hlam]
                                · linarith only [h14396, h24508, hlam]
                              · linarith only [h0, h24507, hlam]
                          · have p24499_0 := h24499c.1
                            have p24499_1 := h24499c.2.1
                            have p24499_2 := h24499c.2.2.1
                            have p24499_3 := h24499c.2.2.2
                            linarith only [hlam, p24499_0]
                          · have p24499_0 := h24499c.1
                            have p24499_1 := h24499c.2.1
                            have p24499_2 := h24499c.2.2.1
                            have p24499_3 := h24499c.2.2.2
                            rcases p24499_3 (m.d 0 1) (by simp) with h24513 | h24513
                            · linarith only [h0, h24513, hlam]
                            · rcases p24499_3 (m.d 0 2) (by simp) with h24515 | h24515
                              · rcases p24499_3 (m.d 0 3) (by simp) with h24516 | h24516
                                · linarith only [h20408, h24516, hlam]
                                · rcases p24499_3 (m.d 0 4) (by simp) with h24518 | h24518
                                  · linarith only [h20409, h24518, hlam]
                                  · rcases p24499_3 (m.d 0 5) (by simp) with h24520 | h24520
                                    · linarith only [h20410, h24520, hlam]
                                    · linarith only [h20412, h24520, hlam]
                              · linarith only [h20408, h24515, hlam]
                          · have p24499_0 := h24499c.1
                            have p24499_1 := h24499c.2.1
                            have p24499_2 := h24499c.2.2.1
                            have p24499_3 := h24499c.2.2.2
                            rcases p24499_3 (m.d 0 1) (by simp) with h24524 | h24524
                            · linarith only [h0, h24524, hlam]
                            · rcases p24499_3 (m.d 0 2) (by simp) with h24526 | h24526
                              · rcases p24499_3 (m.d 0 3) (by simp) with h24527 | h24527
                                · linarith only [h20408, h24527, hlam]
                                · linarith only [h20411, h24527, hlam]
                              · linarith only [h20409, h24526, hlam]
                          · have p24499_0 := h24499c.1
                            have p24499_1 := h24499c.2.1
                            have p24499_2 := h24499c.2.2.1
                            have p24499_3 := h24499c.2.2.2
                            rcases p24499_3 (m.d 0 1) (by simp) with h24531 | h24531
                            · linarith only [h0, h24531, hlam]
                            · rcases p24499_3 (m.d 0 2) (by simp) with h24533 | h24533
                              · rcases p24499_3 (m.d 0 3) (by simp) with h24534 | h24534
                                · linarith only [h20408, h24534, hlam]
                                · rcases p24499_3 (m.d 0 4) (by simp) with h24536 | h24536
                                  · linarith only [h20409, h24536, hlam]
                                  · rcases p24499_3 (m.d 0 5) (by simp) with h24538 | h24538
                                    · linarith only [h20410, h24538, hlam]
                                    · rcases h2bigk with h24540c | h24540c | h24540c | h24540c | h24540c | h24540c | h24540c | h24540c | h24540c | h24540c | h24540c | h24540c | h24540c | h24540c | h24540c | h24540c | h24540c | h24540c | h24540c | h24540c | h24540c | h24540c | h24540c | h24540c | h24540c
                                      · have p24540_0 := h24540c.1
                                        have p24540_1 := h24540c.2.1
                                        have p24540_2 := h24540c.2.2.1
                                        have p24540_3 := h24540c.2.2.2
                                        linarith only [hlam, p24540_0]
                                      · have p24540_0 := h24540c.1
                                        have p24540_1 := h24540c.2.1
                                        have p24540_2 := h24540c.2.2.1
                                        have p24540_3 := h24540c.2.2.2
                                        linarith only [h0, hlam, p24540_1]
                                      · have p24540_0 := h24540c.1
                                        have p24540_1 := h24540c.2.1
                                        have p24540_2 := h24540c.2.2.1
                                        have p24540_3 := h24540c.2.2.2
                                        rcases p24540_3 (m.d 0 2) (by simp) with h24543 | h24543
                                        · rcases p24540_3 (m.d 1 2) (by simp) with h24544 | h24544
                                          · rcases p24540_3 (m.d 2 3) (by simp) with h24545 | h24545
                                            · linarith only [h24545, hlam, p24540_0]
                                            · rcases p24540_3 (m.d 2 4) (by simp) with h24547 | h24547
                                              · linarith only [h20409, h24547, hlam]
                                              · rcases p24540_3 (m.d 2 5) (by simp) with h24549 | h24549
                                                · linarith only [h20410, h24549, hlam]
                                                · linarith only [h24493, h24549, hlam]
                                          · linarith only [h24184, h24544, hlam]
                                        · linarith only [h24543, hlam, p24540_0]
                                      · have p24540_0 := h24540c.1
                                        have p24540_1 := h24540c.2.1
                                        have p24540_2 := h24540c.2.2.1
                                        have p24540_3 := h24540c.2.2.2
                                        rcases p24540_3 (m.d 0 2) (by simp) with h24554 | h24554
                                        · rcases p24540_3 (m.d 1 2) (by simp) with h24555 | h24555
                                          · rcases p24540_3 (m.d 2 3) (by simp) with h24556 | h24556
                                            · linarith only [h20408, h24556, hlam]
                                            · linarith only [h24492, h24556, hlam]
                                          · linarith only [h24185, h24555, hlam]
                                        · linarith only [h24554, hlam, p24540_0]
                                      · have p24540_0 := h24540c.1
                                        have p24540_1 := h24540c.2.1
                                        have p24540_2 := h24540c.2.2.1
                                        have p24540_3 := h24540c.2.2.2
                                        rcases p24540_3 (m.d 0 2) (by simp) with h24561 | h24561
                                        · rcases p24540_3 (m.d 1 2) (by simp) with h24562 | h24562
                                          · rcases p24540_3 (m.d 2 3) (by simp) with h24563 | h24563
                                            · linarith only [h20408, h24563, hlam]
                                            · rcases p24540_3 (m.d 2 4) (by simp) with h24565 | h24565
                                              · linarith only [h20409, h24565, hlam]
                                              · rcases p24540_3 (m.d 2 5) (by simp) with h24567 | h24567
                                                · linarith only [h24567, hlam, p24540_0]
                                                · rcases h3bigk with h24569c | h24569c | h24569c | h24569c | h24569c | h24569c | h24569c | h24569c | h24569c | h24569c | h24569c | h24569c | h24569c | h24569c | h24569c | h24569c | h24569c | h24569c | h24569c | h24569c | h24569c | h24569c | h24569c | h24569c | h24569c
                                                  · have p24569_0 := h24569c.1
                                                    have p24569_1 := h24569c.2.1
                                                    have p24569_2 := h24569c.2.2.1
                                                    have p24569_3 := h24569c.2.2.2
                                                    linarith only [hlam, p24569_0]
                                                  · have p24569_0 := h24569c.1
                                                    have p24569_1 := h24569c.2.1
                                                    have p24569_2 := h24569c.2.2.1
                                                    have p24569_3 := h24569c.2.2.2
                                                    linarith only [h14396, hlam, p24569_1]
                                                  · have p24569_0 := h24569c.1
                                                    have p24569_1 := h24569c.2.1
                                                    have p24569_2 := h24569c.2.2.1
                                                    have p24569_3 := h24569c.2.2.2
                                                    linarith only [h0, h20412, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p24499_1, p24569_1]
                                                  · have p24569_0 := h24569c.1
                                                    have p24569_1 := h24569c.2.1
                                                    have p24569_2 := h24569c.2.2.1
                                                    have p24569_3 := h24569c.2.2.2
                                                    linarith only [h0, h20412, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p24499_1, p24569_1]
                                                  · have p24569_0 := h24569c.1
                                                    have p24569_1 := h24569c.2.1
                                                    have p24569_2 := h24569c.2.2.1
                                                    have p24569_3 := h24569c.2.2.2
                                                    linarith only [h20412, hlam, p24569_0]
                                                  · have p24569_0 := h24569c.1
                                                    have p24569_1 := h24569c.2.1
                                                    have p24569_2 := h24569c.2.2.1
                                                    have p24569_3 := h24569c.2.2.2
                                                    linarith only [h20409, h20411, h24188, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p24569_1]
                                                  · have p24569_0 := h24569c.1
                                                    have p24569_1 := h24569c.2.1
                                                    have p24569_2 := h24569c.2.2.1
                                                    have p24569_3 := h24569c.2.2.2
                                                    linarith only [hlam, p24569_0]
                                                  · have p24569_0 := h24569c.1
                                                    have p24569_1 := h24569c.2.1
                                                    have p24569_2 := h24569c.2.2.1
                                                    have p24569_3 := h24569c.2.2.2
                                                    linarith only [h24188, h24492, h24497, hc34, hc45, hlam, hphi, p24569_1]
                                                  · have p24569_0 := h24569c.1
                                                    have p24569_1 := h24569c.2.1
                                                    have p24569_2 := h24569c.2.2.1
                                                    have p24569_3 := h24569c.2.2.2
                                                    linarith only [h24188, h24497, hc34, hc45, hlam, hphi, p24569_1]
                                                  · have p24569_0 := h24569c.1
                                                    have p24569_1 := h24569c.2.1
                                                    have p24569_2 := h24569c.2.2.1
                                                    have p24569_3 := h24569c.2.2.2
                                                    linarith only [h24188, hlam, p24569_0]
                                                  · have p24569_0 := h24569c.1
                                                    have p24569_1 := h24569c.2.1
                                                    have p24569_2 := h24569c.2.2.1
                                                    have p24569_3 := h24569c.2.2.2
                                                    linarith only [h20408, hlam, p24569_0]
                                                  · have p24569_0 := h24569c.1
                                                    have p24569_1 := h24569c.2.1
                                                    have p24569_2 := h24569c.2.2.1
                                                    have p24569_3 := h24569c.2.2.2
                                                    linarith only [h24184, hlam, p24569_0]
                                                  · have p24569_0 := h24569c.1
                                                    have p24569_1 := h24569c.2.1
                                                    have p24569_2 := h24569c.2.2.1
                                                    have p24569_3 := h24569c.2.2.2
                                                    linarith only [hlam, p24569_0]
                                                  · have p24569_0 := h24569c.1
                                                    have p24569_1 := h24569c.2.1
                                                    have p24569_2 := h24569c.2.2.1
                                                    have p24569_3 := h24569c.2.2.2
                                                    linarith only [h14396, h20408, h24188, h24497, hc34, hc45, hlam, hphi, p24569_1]
                                                  · have p24569_0 := h24569c.1
                                                    have p24569_1 := h24569c.2.1
                                                    have p24569_2 := h24569c.2.2.1
                                                    have p24569_3 := h24569c.2.2.2
                                                    linarith only [h24493, hlam, p24569_0]
                                                  · have p24569_0 := h24569c.1
                                                    have p24569_1 := h24569c.2.1
                                                    have p24569_2 := h24569c.2.2.1
                                                    have p24569_3 := h24569c.2.2.2
                                                    linarith only [h20411, hlam, p24569_0]
                                                  · have p24569_0 := h24569c.1
                                                    have p24569_1 := h24569c.2.1
                                                    have p24569_2 := h24569c.2.2.1
                                                    have p24569_3 := h24569c.2.2.2
                                                    linarith only [h24187, hlam, p24569_0]
                                                  · have p24569_0 := h24569c.1
                                                    have p24569_1 := h24569c.2.1
                                                    have p24569_2 := h24569c.2.2.1
                                                    have p24569_3 := h24569c.2.2.2
                                                    linarith only [h24492, hlam, p24569_0]
                                                  · have p24569_0 := h24569c.1
                                                    have p24569_1 := h24569c.2.1
                                                    have p24569_2 := h24569c.2.2.1
                                                    have p24569_3 := h24569c.2.2.2
                                                    linarith only [hlam, p24569_0]
                                                  · have p24569_0 := h24569c.1
                                                    have p24569_1 := h24569c.2.1
                                                    have p24569_2 := h24569c.2.2.1
                                                    have p24569_3 := h24569c.2.2.2
                                                    linarith only [h24497, hlam, p24569_1]
                                                  · have p24569_0 := h24569c.1
                                                    have p24569_1 := h24569c.2.1
                                                    have p24569_2 := h24569c.2.2.1
                                                    have p24569_3 := h24569c.2.2.2
                                                    linarith only [h24497, hc03, hc45, hlam, hphi, ht34, p24569_1]
                                                  · have p24569_0 := h24569c.1
                                                    have p24569_1 := h24569c.2.1
                                                    have p24569_2 := h24569c.2.2.1
                                                    have p24569_3 := h24569c.2.2.2
                                                    linarith only [h24497, hc13, hc45, hlam, hphi, ht34, p24569_1]
                                                  · have p24569_0 := h24569c.1
                                                    have p24569_1 := h24569c.2.1
                                                    have p24569_2 := h24569c.2.2.1
                                                    have p24569_3 := h24569c.2.2.2
                                                    linarith only [h24492, h24497, hc34, hc45, hlam, hphi, p24569_1]
                                                  · have p24569_0 := h24569c.1
                                                    have p24569_1 := h24569c.2.1
                                                    have p24569_2 := h24569c.2.2.1
                                                    have p24569_3 := h24569c.2.2.2
                                                    linarith only [h24497, hc34, hc45, hlam, hphi, p24569_1]
                                                  · have p24569_0 := h24569c.1
                                                    have p24569_1 := h24569c.2.1
                                                    have p24569_2 := h24569c.2.2.1
                                                    have p24569_3 := h24569c.2.2.2
                                                    linarith only [hlam, p24569_0]
                                          · linarith only [h24186, h24562, hlam]
                                        · linarith only [h24561, hlam, p24540_0]
                                      · have p24540_0 := h24540c.1
                                        have p24540_1 := h24540c.2.1
                                        have p24540_2 := h24540c.2.2.1
                                        have p24540_3 := h24540c.2.2.2
                                        linarith only [hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p24499_1, p24540_1]
                                      · have p24540_0 := h24540c.1
                                        have p24540_1 := h24540c.2.1
                                        have p24540_2 := h24540c.2.2.1
                                        have p24540_3 := h24540c.2.2.2
                                        linarith only [hlam, p24540_0]
                                      · have p24540_0 := h24540c.1
                                        have p24540_1 := h24540c.2.1
                                        have p24540_2 := h24540c.2.2.1
                                        have p24540_3 := h24540c.2.2.2
                                        rcases p24540_3 (m.d 0 2) (by simp) with h24599 | h24599
                                        · linarith only [h0, h24599, hlam]
                                        · linarith only [h20408, h24599, hlam]
                                      · have p24540_0 := h24540c.1
                                        have p24540_1 := h24540c.2.1
                                        have p24540_2 := h24540c.2.2.1
                                        have p24540_3 := h24540c.2.2.2
                                        rcases p24540_3 (m.d 0 2) (by simp) with h24602 | h24602
                                        · linarith only [h0, h24602, hlam]
                                        · linarith only [h20409, h24602, hlam]
                                      · have p24540_0 := h24540c.1
                                        have p24540_1 := h24540c.2.1
                                        have p24540_2 := h24540c.2.2.1
                                        have p24540_3 := h24540c.2.2.2
                                        rcases p24540_3 (m.d 0 2) (by simp) with h24605 | h24605
                                        · linarith only [h0, h24605, hlam]
                                        · linarith only [h20410, h24605, hlam]
                                      · have p24540_0 := h24540c.1
                                        have p24540_1 := h24540c.2.1
                                        have p24540_2 := h24540c.2.2.1
                                        have p24540_3 := h24540c.2.2.2
                                        linarith only [h20408, hlam, p24540_0]
                                      · have p24540_0 := h24540c.1
                                        have p24540_1 := h24540c.2.1
                                        have p24540_2 := h24540c.2.2.1
                                        have p24540_3 := h24540c.2.2.2
                                        linarith only [h24184, hlam, p24540_0]
                                      · have p24540_0 := h24540c.1
                                        have p24540_1 := h24540c.2.1
                                        have p24540_2 := h24540c.2.2.1
                                        have p24540_3 := h24540c.2.2.2
                                        linarith only [hlam, p24540_0]
                                      · have p24540_0 := h24540c.1
                                        have p24540_1 := h24540c.2.1
                                        have p24540_2 := h24540c.2.2.1
                                        have p24540_3 := h24540c.2.2.2
                                        linarith only [h20408, h20412, hc02, hc24, hlam, hphi, ht0b, ht45, ht5b, p24499_1, p24540_1]
                                      · have p24540_0 := h24540c.1
                                        have p24540_1 := h24540c.2.1
                                        have p24540_2 := h24540c.2.2.1
                                        have p24540_3 := h24540c.2.2.2
                                        linarith only [h24493, hlam, p24540_0]
                                      · have p24540_0 := h24540c.1
                                        have p24540_1 := h24540c.2.1
                                        have p24540_2 := h24540c.2.2.1
                                        have p24540_3 := h24540c.2.2.2
                                        linarith only [h20409, hlam, p24540_0]
                                      · have p24540_0 := h24540c.1
                                        have p24540_1 := h24540c.2.1
                                        have p24540_2 := h24540c.2.2.1
                                        have p24540_3 := h24540c.2.2.2
                                        linarith only [h24185, hlam, p24540_0]
                                      · have p24540_0 := h24540c.1
                                        have p24540_1 := h24540c.2.1
                                        have p24540_2 := h24540c.2.2.1
                                        have p24540_3 := h24540c.2.2.2
                                        linarith only [h24492, hlam, p24540_1]
                                      · have p24540_0 := h24540c.1
                                        have p24540_1 := h24540c.2.1
                                        have p24540_2 := h24540c.2.2.1
                                        have p24540_3 := h24540c.2.2.2
                                        linarith only [hlam, p24540_0]
                                      · have p24540_0 := h24540c.1
                                        have p24540_1 := h24540c.2.1
                                        have p24540_2 := h24540c.2.2.1
                                        have p24540_3 := h24540c.2.2.2
                                        linarith only [h24495, hlam, p24540_1]
                                      · have p24540_0 := h24540c.1
                                        have p24540_1 := h24540c.2.1
                                        have p24540_2 := h24540c.2.2.1
                                        have p24540_3 := h24540c.2.2.2
                                        linarith only [h20410, hlam, p24540_0]
                                      · have p24540_0 := h24540c.1
                                        have p24540_1 := h24540c.2.1
                                        have p24540_2 := h24540c.2.2.1
                                        have p24540_3 := h24540c.2.2.2
                                        linarith only [h24186, hlam, p24540_0]
                                      · have p24540_0 := h24540c.1
                                        have p24540_1 := h24540c.2.1
                                        have p24540_2 := h24540c.2.2.1
                                        have p24540_3 := h24540c.2.2.2
                                        linarith only [h0, h20410, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p24499_1, p24540_1]
                                      · have p24540_0 := h24540c.1
                                        have p24540_1 := h24540c.2.1
                                        have p24540_2 := h24540c.2.2.1
                                        have p24540_3 := h24540c.2.2.2
                                        linarith only [h0, h20410, h24492, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p24499_1, p24540_1]
                                      · have p24540_0 := h24540c.1
                                        have p24540_1 := h24540c.2.1
                                        have p24540_2 := h24540c.2.2.1
                                        have p24540_3 := h24540c.2.2.2
                                        linarith only [hlam, p24540_0]
                              · linarith only [h20410, h24533, hlam]
                          · have p24499_0 := h24499c.1
                            have p24499_1 := h24499c.2.1
                            have p24499_2 := h24499c.2.2.1
                            have p24499_3 := h24499c.2.2.2
                            linarith only [h20412, h24497, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p24499_1]
                          · have p24499_0 := h24499c.1
                            have p24499_1 := h24499c.2.1
                            have p24499_2 := h24499c.2.2.1
                            have p24499_3 := h24499c.2.2.2
                            linarith only [h20408, hlam, p24499_1]
                          · have p24499_0 := h24499c.1
                            have p24499_1 := h24499c.2.1
                            have p24499_2 := h24499c.2.2.1
                            have p24499_3 := h24499c.2.2.2
                            linarith only [hlam, p24499_0]
                          · have p24499_0 := h24499c.1
                            have p24499_1 := h24499c.2.1
                            have p24499_2 := h24499c.2.2.1
                            have p24499_3 := h24499c.2.2.2
                            linarith only [h16915, h20412, h24497, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p24499_1]
                          · have p24499_0 := h24499c.1
                            have p24499_1 := h24499c.2.1
                            have p24499_2 := h24499c.2.2.1
                            have p24499_3 := h24499c.2.2.2
                            linarith only [h20412, hlam, p24499_1]
                          · have p24499_0 := h24499c.1
                            have p24499_1 := h24499c.2.1
                            have p24499_2 := h24499c.2.2.1
                            have p24499_3 := h24499c.2.2.2
                            linarith only [h20411, h20412, h24497, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p24499_1]
                          · have p24499_0 := h24499c.1
                            have p24499_1 := h24499c.2.1
                            have p24499_2 := h24499c.2.2.1
                            have p24499_3 := h24499c.2.2.2
                            linarith only [h20409, hlam, p24499_0]
                          · have p24499_0 := h24499c.1
                            have p24499_1 := h24499c.2.1
                            have p24499_2 := h24499c.2.2.1
                            have p24499_3 := h24499c.2.2.2
                            linarith only [h20411, hlam, p24499_0]
                          · have p24499_0 := h24499c.1
                            have p24499_1 := h24499c.2.1
                            have p24499_2 := h24499c.2.2.1
                            have p24499_3 := h24499c.2.2.2
                            linarith only [hlam, p24499_0]
                          · have p24499_0 := h24499c.1
                            have p24499_1 := h24499c.2.1
                            have p24499_2 := h24499c.2.2.1
                            have p24499_3 := h24499c.2.2.2
                            linarith only [h24182, hlam, p24499_0]
                          · have p24499_0 := h24499c.1
                            have p24499_1 := h24499c.2.1
                            have p24499_2 := h24499c.2.2.1
                            have p24499_3 := h24499c.2.2.2
                            rcases p24499_3 (m.d 0 1) (by simp) with h24634 | h24634
                            · linarith only [h18815, h24634, hlam]
                            · rcases p24499_3 (m.d 0 2) (by simp) with h24636 | h24636
                              · rcases p24499_3 (m.d 0 3) (by simp) with h24637 | h24637
                                · linarith only [h20412, h24637, hlam]
                                · linarith only [h14396, h24637, hlam]
                              · linarith only [h0, h24636, hlam]
                          · have p24499_0 := h24499c.1
                            have p24499_1 := h24499c.2.1
                            have p24499_2 := h24499c.2.2.1
                            have p24499_3 := h24499c.2.2.2
                            linarith only [h20410, hlam, p24499_1]
                          · have p24499_0 := h24499c.1
                            have p24499_1 := h24499c.2.1
                            have p24499_2 := h24499c.2.2.1
                            have p24499_3 := h24499c.2.2.2
                            linarith only [h20408, h20412, h24492, h24497, hc34, hc45, hlam, hphi, p24499_1]
                          · have p24499_0 := h24499c.1
                            have p24499_1 := h24499c.2.1
                            have p24499_2 := h24499c.2.2.1
                            have p24499_3 := h24499c.2.2.2
                            rcases p24499_3 (m.d 0 1) (by simp) with h24643 | h24643
                            · linarith only [h18815, h24643, hlam]
                            · rcases p24499_3 (m.d 0 2) (by simp) with h24645 | h24645
                              · rcases p24499_3 (m.d 0 3) (by simp) with h24646 | h24646
                                · linarith only [h20412, h24646, hlam]
                                · linarith only [h20411, h24646, hlam]
                              · linarith only [h20409, h24645, hlam]
                          · have p24499_0 := h24499c.1
                            have p24499_1 := h24499c.2.1
                            have p24499_2 := h24499c.2.2.1
                            have p24499_3 := h24499c.2.2.2
                            linarith only [hlam, p24499_0]
                  · linarith only [h20411, h20412, h24492, hc23, hc35, hlam, hphi]
            · linarith only [h14396, h20411, h24187, hlam]
          · linarith only [h0, h20410, h24186, hlam]
        · linarith only [h0, h20409, h24185, hlam]
      · linarith only [h0, h20408, h24184, hlam]

set_option maxHeartbeats 11722000 in
set_option maxHeartbeats 11722000 in
theorem r1l7_10_12_23_L_I_L_I_H_I_s21_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg14396 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg16915 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg18815 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg20408 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg20409 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg20410 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h20411 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
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
  have h14396 := hg14396
  have h16915 := hg16915
  have h18815 := hg18815
  have h20408 := hg20408
  have h20409 := hg20409
  have h20410 := hg20410
  exact r1l7_10_12_23_L_I_L_I_H_I_s22 m hb0 hb2 hb3 h0 h14396 h16915 h18815 h20408 h20409 h20410 h20411

end R2N4
