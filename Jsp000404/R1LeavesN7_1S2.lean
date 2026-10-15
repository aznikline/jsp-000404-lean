import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_1S1

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5108000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s9_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg9 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h10 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h11 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
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
  have h7 := hg7
  have h8 := hg8
  have h9 := hg9
  rcases m.htr 1 2 5 (by decide) (by decide) with h1220 | h1220
  · rcases m.htr 1 3 4 (by decide) (by decide) with h1221 | h1221
    · linarith only [h10, h11, h1221, hlam]
    · rcases m.htr 1 3 5 (by decide) (by decide) with h1223 | h1223
      · rcases m.htr 1 4 5 (by decide) (by decide) with h1224 | h1224
        · rcases m.htr 2 3 4 (by decide) (by decide) with h1225 | h1225
          · linarith only [h0, h1221, h1223, h1225, h4, hc01, hc35, hlam, hphi, ht0b, ht5b]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h1227 | h1227
            · linarith only [h0, h10, h11, h1225, h1227, h4, h7, hc01, hc35, hlam, hphi, ht0b, ht5b]
            · linarith only [h0, h10, h11, h1223, h1225, h1227, h4, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
        · linarith only [h10, h11, h1223, h1224, hlam]
      · rcases m.htr 1 4 5 (by decide) (by decide) with h1231 | h1231
        · rcases m.htr 2 3 4 (by decide) (by decide) with h1232 | h1232
          · linarith only [h0, h10, h11, h1221, h1232, h5, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h1234 | h1234
            · linarith only [h0, h10, h11, h1232, h1234, h4, h7, hc01, hc35, hlam, hphi, ht0b, ht5b]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h1236 | h1236
              · rcases m.htr 3 4 5 (by decide) (by decide) with h1237 | h1237
                · rcases h0bigk with h1238c | h1238c | h1238c | h1238c | h1238c | h1238c | h1238c | h1238c | h1238c | h1238c | h1238c | h1238c | h1238c | h1238c | h1238c | h1238c | h1238c | h1238c | h1238c | h1238c | h1238c | h1238c | h1238c | h1238c | h1238c
                  · have p1238_0 := h1238c.1
                    have p1238_1 := h1238c.2.1
                    have p1238_2 := h1238c.2.2.1
                    have p1238_3 := h1238c.2.2.2
                    linarith only [hlam, p1238_0]
                  · have p1238_0 := h1238c.1
                    have p1238_1 := h1238c.2.1
                    have p1238_2 := h1238c.2.2.1
                    have p1238_3 := h1238c.2.2.2
                    linarith only [h11, h1232, h4, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1238_1]
                  · have p1238_0 := h1238c.1
                    have p1238_1 := h1238c.2.1
                    have p1238_2 := h1238c.2.2.1
                    have p1238_3 := h1238c.2.2.2
                    linarith only [h11, h1220, h1232, h1234, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1238_1]
                  · have p1238_0 := h1238c.1
                    have p1238_1 := h1238c.2.1
                    have p1238_2 := h1238c.2.2.1
                    have p1238_3 := h1238c.2.2.2
                    linarith only [h11, h1220, h1234, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1238_1]
                  · have p1238_0 := h1238c.1
                    have p1238_1 := h1238c.2.1
                    have p1238_2 := h1238c.2.2.1
                    have p1238_3 := h1238c.2.2.2
                    rcases p1238_3 (m.d 0 1) (by simp) with h1243 | h1243
                    · rcases p1238_3 (m.d 0 2) (by simp) with h1244 | h1244
                      · linarith only [h0, h1244, hlam]
                      · linarith only [h1244, h6, hlam]
                    · linarith only [h1243, h3, hlam]
                  · have p1238_0 := h1238c.1
                    have p1238_1 := h1238c.2.1
                    have p1238_2 := h1238c.2.2.1
                    have p1238_3 := h1238c.2.2.2
                    linarith only [h0, hlam, p1238_0]
                  · have p1238_0 := h1238c.1
                    have p1238_1 := h1238c.2.1
                    have p1238_2 := h1238c.2.2.1
                    have p1238_3 := h1238c.2.2.2
                    linarith only [hlam, p1238_0]
                  · have p1238_0 := h1238c.1
                    have p1238_1 := h1238c.2.1
                    have p1238_2 := h1238c.2.2.1
                    have p1238_3 := h1238c.2.2.2
                    linarith only [h11, h1220, h1232, h1234, h7, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1238_1]
                  · have p1238_0 := h1238c.1
                    have p1238_1 := h1238c.2.1
                    have p1238_2 := h1238c.2.2.1
                    have p1238_3 := h1238c.2.2.2
                    linarith only [h0, h11, h1220, h1232, h1234, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1238_1]
                  · have p1238_0 := h1238c.1
                    have p1238_1 := h1238c.2.1
                    have p1238_2 := h1238c.2.2.1
                    have p1238_3 := h1238c.2.2.2
                    rcases p1238_3 (m.d 0 1) (by simp) with h1252 | h1252
                    · rcases p1238_3 (m.d 0 2) (by simp) with h1253 | h1253
                      · rcases p1238_3 (m.d 0 3) (by simp) with h1254 | h1254
                        · linarith only [h1254, h4, hlam]
                        · linarith only [h1254, h8, hlam]
                      · linarith only [h1253, h6, hlam]
                    · linarith only [h1252, h3, hlam]
                  · have p1238_0 := h1238c.1
                    have p1238_1 := h1238c.2.1
                    have p1238_2 := h1238c.2.2.1
                    have p1238_3 := h1238c.2.2.2
                    linarith only [h1, hlam, p1238_1]
                  · have p1238_0 := h1238c.1
                    have p1238_1 := h1238c.2.1
                    have p1238_2 := h1238c.2.2.1
                    have p1238_3 := h1238c.2.2.2
                    linarith only [h4, hlam, p1238_1]
                  · have p1238_0 := h1238c.1
                    have p1238_1 := h1238c.2.1
                    have p1238_2 := h1238c.2.2.1
                    have p1238_3 := h1238c.2.2.2
                    linarith only [hlam, p1238_0]
                  · have p1238_0 := h1238c.1
                    have p1238_1 := h1238c.2.1
                    have p1238_2 := h1238c.2.2.1
                    have p1238_3 := h1238c.2.2.2
                    linarith only [h11, h1220, h1232, h1234, h7, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1238_1]
                  · have p1238_0 := h1238c.1
                    have p1238_1 := h1238c.2.1
                    have p1238_2 := h1238c.2.2.1
                    have p1238_3 := h1238c.2.2.2
                    rcases p1238_3 (m.d 0 1) (by simp) with h1263 | h1263
                    · rcases p1238_3 (m.d 0 2) (by simp) with h1264 | h1264
                      · rcases p1238_3 (m.d 0 3) (by simp) with h1265 | h1265
                        · rcases p1238_3 (m.d 0 4) (by simp) with h1266 | h1266
                          · linarith only [h1266, h7, hlam]
                          · linarith only [h1266, h9, hlam]
                        · linarith only [h1265, h8, hlam]
                      · linarith only [h1264, h6, hlam]
                    · linarith only [h1263, h3, hlam]
                  · have p1238_0 := h1238c.1
                    have p1238_1 := h1238c.2.1
                    have p1238_2 := h1238c.2.2.1
                    have p1238_3 := h1238c.2.2.2
                    linarith only [h2, hlam, p1238_0]
                  · have p1238_0 := h1238c.1
                    have p1238_1 := h1238c.2.1
                    have p1238_2 := h1238c.2.2.1
                    have p1238_3 := h1238c.2.2.2
                    linarith only [h5, hlam, p1238_0]
                  · have p1238_0 := h1238c.1
                    have p1238_1 := h1238c.2.1
                    have p1238_2 := h1238c.2.2.1
                    have p1238_3 := h1238c.2.2.2
                    linarith only [h7, hlam, p1238_0]
                  · have p1238_0 := h1238c.1
                    have p1238_1 := h1238c.2.1
                    have p1238_2 := h1238c.2.2.1
                    have p1238_3 := h1238c.2.2.2
                    linarith only [hlam, p1238_0]
                  · have p1238_0 := h1238c.1
                    have p1238_1 := h1238c.2.1
                    have p1238_2 := h1238c.2.2.1
                    have p1238_3 := h1238c.2.2.2
                    rcases p1238_3 (m.d 0 1) (by simp) with h1276 | h1276
                    · rcases p1238_3 (m.d 0 2) (by simp) with h1277 | h1277
                      · rcases p1238_3 (m.d 0 3) (by simp) with h1278 | h1278
                        · rcases p1238_3 (m.d 0 4) (by simp) with h1279 | h1279
                          · rcases p1238_3 (m.d 0 5) (by simp) with h1280 | h1280
                            · linarith only [h1280, h9, hlam]
                            · rcases h2bigk with h1282c | h1282c | h1282c | h1282c | h1282c | h1282c | h1282c | h1282c | h1282c | h1282c | h1282c | h1282c | h1282c | h1282c | h1282c | h1282c | h1282c | h1282c | h1282c | h1282c | h1282c | h1282c | h1282c | h1282c | h1282c
                              · have p1282_0 := h1282c.1
                                have p1282_1 := h1282c.2.1
                                have p1282_2 := h1282c.2.2.1
                                have p1282_3 := h1282c.2.2.2
                                linarith only [hlam, p1282_0]
                              · have p1282_0 := h1282c.1
                                have p1282_1 := h1282c.2.1
                                have p1282_2 := h1282c.2.2.1
                                have p1282_3 := h1282c.2.2.2
                                rcases p1282_3 (m.d 0 2) (by simp) with h1284 | h1284
                                · rcases p1282_3 (m.d 1 2) (by simp) with h1285 | h1285
                                  · linarith only [h0, h1285, hlam]
                                  · rcases p1282_3 (m.d 2 3) (by simp) with h1287 | h1287
                                    · linarith only [h1287, h4, hlam]
                                    · rcases p1282_3 (m.d 2 4) (by simp) with h1289 | h1289
                                      · linarith only [h1289, h5, hlam]
                                      · linarith only [h11, h1289, hlam]
                                · linarith only [h0, h1284, hlam]
                              · have p1282_0 := h1282c.1
                                have p1282_1 := h1282c.2.1
                                have p1282_2 := h1282c.2.2.1
                                have p1282_3 := h1282c.2.2.2
                                linarith only [h11, h1220, h1234, h5, hlam, p1282_2]
                              · have p1282_0 := h1282c.1
                                have p1282_1 := h1282c.2.1
                                have p1282_2 := h1282c.2.2.1
                                have p1282_3 := h1282c.2.2.2
                                linarith only [h11, h1220, h1234, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1282_1]
                              · have p1282_0 := h1282c.1
                                have p1282_1 := h1282c.2.1
                                have p1282_2 := h1282c.2.2.1
                                have p1282_3 := h1282c.2.2.2
                                linarith only [h11, h1220, h5, hlam, p1282_2]
                              · have p1282_0 := h1282c.1
                                have p1282_1 := h1282c.2.1
                                have p1282_2 := h1282c.2.2.1
                                have p1282_3 := h1282c.2.2.2
                                linarith only [h0, hlam, p1282_0]
                              · have p1282_0 := h1282c.1
                                have p1282_1 := h1282c.2.1
                                have p1282_2 := h1282c.2.2.1
                                have p1282_3 := h1282c.2.2.2
                                linarith only [hlam, p1282_0]
                              · have p1282_0 := h1282c.1
                                have p1282_1 := h1282c.2.1
                                have p1282_2 := h1282c.2.2.1
                                have p1282_3 := h1282c.2.2.2
                                linarith only [h0, h11, h1232, h4, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1282_1]
                              · have p1282_0 := h1282c.1
                                have p1282_1 := h1282c.2.1
                                have p1282_2 := h1282c.2.2.1
                                have p1282_3 := h1282c.2.2.2
                                linarith only [h11, hlam, p1282_0]
                              · have p1282_0 := h1282c.1
                                have p1282_1 := h1282c.2.1
                                have p1282_2 := h1282c.2.2.1
                                have p1282_3 := h1282c.2.2.2
                                linarith only [h0, h11, h1232, h4, h7, hc01, hc25, hlam, hphi, ht0b, ht5b, p1282_1]
                              · have p1282_0 := h1282c.1
                                have p1282_1 := h1282c.2.1
                                have p1282_2 := h1282c.2.2.1
                                have p1282_3 := h1282c.2.2.2
                                linarith only [h4, hlam, p1282_0]
                              · have p1282_0 := h1282c.1
                                have p1282_1 := h1282c.2.1
                                have p1282_2 := h1282c.2.2.1
                                have p1282_3 := h1282c.2.2.2
                                linarith only [h10, hlam, p1282_0]
                              · have p1282_0 := h1282c.1
                                have p1282_1 := h1282c.2.1
                                have p1282_2 := h1282c.2.2.1
                                have p1282_3 := h1282c.2.2.2
                                linarith only [hlam, p1282_0]
                              · have p1282_0 := h1282c.1
                                have p1282_1 := h1282c.2.1
                                have p1282_2 := h1282c.2.2.1
                                have p1282_3 := h1282c.2.2.2
                                linarith only [h1232, hlam, p1282_0]
                              · have p1282_0 := h1282c.1
                                have p1282_1 := h1282c.2.1
                                have p1282_2 := h1282c.2.2.1
                                have p1282_3 := h1282c.2.2.2
                                linarith only [h1234, hlam, p1282_0]
                              · have p1282_0 := h1282c.1
                                have p1282_1 := h1282c.2.1
                                have p1282_2 := h1282c.2.2.1
                                have p1282_3 := h1282c.2.2.2
                                linarith only [h5, hlam, p1282_0]
                              · have p1282_0 := h1282c.1
                                have p1282_1 := h1282c.2.1
                                have p1282_2 := h1282c.2.2.1
                                have p1282_3 := h1282c.2.2.2
                                linarith only [h0, h10, h1232, h4, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1282_1]
                              · have p1282_0 := h1282c.1
                                have p1282_1 := h1282c.2.1
                                have p1282_2 := h1282c.2.2.1
                                have p1282_3 := h1282c.2.2.2
                                rcases p1282_3 (m.d 0 2) (by simp) with h1308 | h1308
                                · rcases p1282_3 (m.d 1 2) (by simp) with h1309 | h1309
                                  · linarith only [h11, h1309, hlam]
                                  · linarith only [h10, h1309, hlam]
                                · linarith only [h1308, h4, hlam]
                              · have p1282_0 := h1282c.1
                                have p1282_1 := h1282c.2.1
                                have p1282_2 := h1282c.2.2.1
                                have p1282_3 := h1282c.2.2.2
                                linarith only [hlam, p1282_0]
                              · have p1282_0 := h1282c.1
                                have p1282_1 := h1282c.2.1
                                have p1282_2 := h1282c.2.2.1
                                have p1282_3 := h1282c.2.2.2
                                rcases p1282_3 (m.d 0 2) (by simp) with h1314 | h1314
                                · rcases p1282_3 (m.d 1 2) (by simp) with h1315 | h1315
                                  · linarith only [h11, h1315, hlam]
                                  · linarith only [h1220, h1315, hlam]
                                · linarith only [h1314, h6, hlam]
                              · have p1282_0 := h1282c.1
                                have p1282_1 := h1282c.2.1
                                have p1282_2 := h1282c.2.2.1
                                have p1282_3 := h1282c.2.2.2
                                linarith only [h6, hlam, p1282_0]
                              · have p1282_0 := h1282c.1
                                have p1282_1 := h1282c.2.1
                                have p1282_2 := h1282c.2.2.1
                                have p1282_3 := h1282c.2.2.2
                                linarith only [h1220, hlam, p1282_0]
                              · have p1282_0 := h1282c.1
                                have p1282_1 := h1282c.2.1
                                have p1282_2 := h1282c.2.2.1
                                have p1282_3 := h1282c.2.2.2
                                linarith only [h0, h1220, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1282_1]
                              · have p1282_0 := h1282c.1
                                have p1282_1 := h1282c.2.1
                                have p1282_2 := h1282c.2.2.1
                                have p1282_3 := h1282c.2.2.2
                                linarith only [h1236, hlam, p1282_0]
                              · have p1282_0 := h1282c.1
                                have p1282_1 := h1282c.2.1
                                have p1282_2 := h1282c.2.2.1
                                have p1282_3 := h1282c.2.2.2
                                linarith only [hlam, p1282_0]
                          · linarith only [h1279, h9, hlam]
                        · linarith only [h1278, h8, hlam]
                      · linarith only [h1277, h6, hlam]
                    · linarith only [h1276, h3, hlam]
                  · have p1238_0 := h1238c.1
                    have p1238_1 := h1238c.2.1
                    have p1238_2 := h1238c.2.2.1
                    have p1238_3 := h1238c.2.2.2
                    linarith only [h3, hlam, p1238_0]
                  · have p1238_0 := h1238c.1
                    have p1238_1 := h1238c.2.1
                    have p1238_2 := h1238c.2.2.1
                    have p1238_3 := h1238c.2.2.2
                    linarith only [h6, hlam, p1238_1]
                  · have p1238_0 := h1238c.1
                    have p1238_1 := h1238c.2.1
                    have p1238_2 := h1238c.2.2.1
                    have p1238_3 := h1238c.2.2.2
                    linarith only [h8, hlam, p1238_0]
                  · have p1238_0 := h1238c.1
                    have p1238_1 := h1238c.2.1
                    have p1238_2 := h1238c.2.2.1
                    have p1238_3 := h1238c.2.2.2
                    linarith only [h9, hlam, p1238_1]
                  · have p1238_0 := h1238c.1
                    have p1238_1 := h1238c.2.1
                    have p1238_2 := h1238c.2.2.1
                    have p1238_3 := h1238c.2.2.2
                    linarith only [hlam, p1238_0]
                · linarith only [h0, h11, h1220, h1232, h1237, h4, h7, h9, hc01, hc25, hlam, hphi, ht0b, ht5b]
              · linarith only [h11, h1220, h1231, h1234, h1236, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
        · linarith only [h11, h1220, h1231, hlam]
  · rcases m.htr 1 3 4 (by decide) (by decide) with h1336 | h1336
    · linarith only [h10, h11, h1336, hlam]
    · rcases m.htr 1 3 5 (by decide) (by decide) with h1338 | h1338
      · linarith only [h10, h1220, h1338, hlam]
      · rcases m.htr 1 4 5 (by decide) (by decide) with h1340 | h1340
        · rcases m.htr 2 3 4 (by decide) (by decide) with h1341 | h1341
          · linarith only [h10, h1220, h1336, h1341, hc13, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h1343 | h1343
            · linarith only [h10, h1220, h1338, h1343, hlam]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h1345 | h1345
              · rcases m.htr 3 4 5 (by decide) (by decide) with h1346 | h1346
                · rcases h0bigk with h1347c | h1347c | h1347c | h1347c | h1347c | h1347c | h1347c | h1347c | h1347c | h1347c | h1347c | h1347c | h1347c | h1347c | h1347c | h1347c | h1347c | h1347c | h1347c | h1347c | h1347c | h1347c | h1347c | h1347c | h1347c
                  · have p1347_0 := h1347c.1
                    have p1347_1 := h1347c.2.1
                    have p1347_2 := h1347c.2.2.1
                    have p1347_3 := h1347c.2.2.2
                    linarith only [hlam, p1347_0]
                  · have p1347_0 := h1347c.1
                    have p1347_1 := h1347c.2.1
                    have p1347_2 := h1347c.2.2.1
                    have p1347_3 := h1347c.2.2.2
                    linarith only [h1220, h1341, h1345, h4, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1347_1]
                  · have p1347_0 := h1347c.1
                    have p1347_1 := h1347c.2.1
                    have p1347_2 := h1347c.2.2.1
                    have p1347_3 := h1347c.2.2.2
                    linarith only [h10, h1220, h1341, h1345, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1347_1]
                  · have p1347_0 := h1347c.1
                    have p1347_1 := h1347c.2.1
                    have p1347_2 := h1347c.2.2.1
                    have p1347_3 := h1347c.2.2.2
                    linarith only [h10, h1220, h1345, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1347_1]
                  · have p1347_0 := h1347c.1
                    have p1347_1 := h1347c.2.1
                    have p1347_2 := h1347c.2.2.1
                    have p1347_3 := h1347c.2.2.2
                    linarith only [h10, h1220, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1347_1]
                  · have p1347_0 := h1347c.1
                    have p1347_1 := h1347c.2.1
                    have p1347_2 := h1347c.2.2.1
                    have p1347_3 := h1347c.2.2.2
                    linarith only [h0, hlam, p1347_0]
                  · have p1347_0 := h1347c.1
                    have p1347_1 := h1347c.2.1
                    have p1347_2 := h1347c.2.2.1
                    have p1347_3 := h1347c.2.2.2
                    linarith only [hlam, p1347_0]
                  · have p1347_0 := h1347c.1
                    have p1347_1 := h1347c.2.1
                    have p1347_2 := h1347c.2.2.1
                    have p1347_3 := h1347c.2.2.2
                    linarith only [h10, h1220, h1341, h1345, h7, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1347_1]
                  · have p1347_0 := h1347c.1
                    have p1347_1 := h1347c.2.1
                    have p1347_2 := h1347c.2.2.1
                    have p1347_3 := h1347c.2.2.2
                    linarith only [h0, h10, h1220, h1345, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1347_1]
                  · have p1347_0 := h1347c.1
                    have p1347_1 := h1347c.2.1
                    have p1347_2 := h1347c.2.2.1
                    have p1347_3 := h1347c.2.2.2
                    linarith only [h0, h10, h1220, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1347_1]
                  · have p1347_0 := h1347c.1
                    have p1347_1 := h1347c.2.1
                    have p1347_2 := h1347c.2.2.1
                    have p1347_3 := h1347c.2.2.2
                    linarith only [h1, hlam, p1347_1]
                  · have p1347_0 := h1347c.1
                    have p1347_1 := h1347c.2.1
                    have p1347_2 := h1347c.2.2.1
                    have p1347_3 := h1347c.2.2.2
                    linarith only [h4, hlam, p1347_1]
                  · have p1347_0 := h1347c.1
                    have p1347_1 := h1347c.2.1
                    have p1347_2 := h1347c.2.2.1
                    have p1347_3 := h1347c.2.2.2
                    linarith only [hlam, p1347_0]
                  · have p1347_0 := h1347c.1
                    have p1347_1 := h1347c.2.1
                    have p1347_2 := h1347c.2.2.1
                    have p1347_3 := h1347c.2.2.2
                    linarith only [h10, h1220, h1345, h5, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1347_1]
                  · have p1347_0 := h1347c.1
                    have p1347_1 := h1347c.2.1
                    have p1347_2 := h1347c.2.2.1
                    have p1347_3 := h1347c.2.2.2
                    linarith only [h0, h10, h1220, h4, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1347_1]
                  · have p1347_0 := h1347c.1
                    have p1347_1 := h1347c.2.1
                    have p1347_2 := h1347c.2.2.1
                    have p1347_3 := h1347c.2.2.2
                    linarith only [h2, hlam, p1347_0]
                  · have p1347_0 := h1347c.1
                    have p1347_1 := h1347c.2.1
                    have p1347_2 := h1347c.2.2.1
                    have p1347_3 := h1347c.2.2.2
                    linarith only [h5, hlam, p1347_0]
                  · have p1347_0 := h1347c.1
                    have p1347_1 := h1347c.2.1
                    have p1347_2 := h1347c.2.2.1
                    have p1347_3 := h1347c.2.2.2
                    linarith only [h7, hlam, p1347_0]
                  · have p1347_0 := h1347c.1
                    have p1347_1 := h1347c.2.1
                    have p1347_2 := h1347c.2.2.1
                    have p1347_3 := h1347c.2.2.2
                    linarith only [hlam, p1347_0]
                  · have p1347_0 := h1347c.1
                    have p1347_1 := h1347c.2.1
                    have p1347_2 := h1347c.2.2.1
                    have p1347_3 := h1347c.2.2.2
                    linarith only [h10, h1220, h6, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1347_1]
                  · have p1347_0 := h1347c.1
                    have p1347_1 := h1347c.2.1
                    have p1347_2 := h1347c.2.2.1
                    have p1347_3 := h1347c.2.2.2
                    linarith only [h3, hlam, p1347_0]
                  · have p1347_0 := h1347c.1
                    have p1347_1 := h1347c.2.1
                    have p1347_2 := h1347c.2.2.1
                    have p1347_3 := h1347c.2.2.2
                    linarith only [h6, hlam, p1347_1]
                  · have p1347_0 := h1347c.1
                    have p1347_1 := h1347c.2.1
                    have p1347_2 := h1347c.2.2.1
                    have p1347_3 := h1347c.2.2.2
                    linarith only [h8, hlam, p1347_0]
                  · have p1347_0 := h1347c.1
                    have p1347_1 := h1347c.2.1
                    have p1347_2 := h1347c.2.2.1
                    have p1347_3 := h1347c.2.2.2
                    linarith only [h9, hlam, p1347_1]
                  · have p1347_0 := h1347c.1
                    have p1347_1 := h1347c.2.1
                    have p1347_2 := h1347c.2.2.1
                    have p1347_3 := h1347c.2.2.2
                    linarith only [hlam, p1347_0]
                · linarith only [h10, h1220, h1340, h1341, h1345, h1346, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
              · linarith only [h11, h1340, h1345, hlam]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h1375 | h1375
          · linarith only [h0, h10, h1220, h1375, h6, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h1377 | h1377
            · linarith only [h0, h10, h11, h1340, h1377, h4, h7, h9, hc01, hc35, hlam, hphi, ht0b, ht5b]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h1379 | h1379
              · linarith only [h10, h11, h1340, h1375, h1379, hc23, hc34, hlam, hphi]
              · linarith only [h0, h10, h11, h1379, h4, h7, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]

set_option maxHeartbeats 5108000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s9_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg9 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h10 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
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
  have h7 := hg7
  have h8 := hg8
  have h9 := hg9
  rcases m.htr 1 2 4 (by decide) (by decide) with h11 | h11
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s9_x0_x0 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 h10 h11
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s9_x0_x1 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 h10 h11

set_option maxHeartbeats 5108000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s9_x1_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg9 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h10 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h1382 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
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
  have h7 := hg7
  have h8 := hg8
  have h9 := hg9
  rcases m.htr 1 2 5 (by decide) (by decide) with h1383 | h1383
  · rcases m.htr 1 3 4 (by decide) (by decide) with h1384 | h1384
    · rcases m.htr 1 3 5 (by decide) (by decide) with h1385 | h1385
      · rcases m.htr 1 4 5 (by decide) (by decide) with h1386 | h1386
        · rcases m.htr 2 3 4 (by decide) (by decide) with h1387 | h1387
          · rcases m.htr 2 3 5 (by decide) (by decide) with h1388 | h1388
            · rcases m.htr 2 4 5 (by decide) (by decide) with h1389 | h1389
              · linarith only [h0, h10, h1382, h1389, h4, hc01, hc45, hlam, hphi, ht0b, ht5b]
              · linarith only [h0, h10, h1382, h1386, h1389, h4, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
            · linarith only [h0, h10, h1383, h1388, h4, h8, hc01, hc25, hlam, hphi, ht0b, ht5b]
          · linarith only [h10, h1383, h1387, h7, hc03, hc25, hlam, hphi, ht0b, ht5b]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h1394 | h1394
          · rcases m.htr 2 3 5 (by decide) (by decide) with h1395 | h1395
            · rcases m.htr 2 4 5 (by decide) (by decide) with h1396 | h1396
              · linarith only [h10, h1382, h1386, h1396, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h1398 | h1398
                · linarith only [h0, h10, h1382, h1386, h1394, h1398, h4, hc01, hc15, hlam, hphi, ht0b, ht5b]
                · rcases h0bigk with h1400c | h1400c | h1400c | h1400c | h1400c | h1400c | h1400c | h1400c | h1400c | h1400c | h1400c | h1400c | h1400c | h1400c | h1400c | h1400c | h1400c | h1400c | h1400c | h1400c | h1400c | h1400c | h1400c | h1400c | h1400c
                  · have p1400_0 := h1400c.1
                    have p1400_1 := h1400c.2.1
                    have p1400_2 := h1400c.2.2.1
                    have p1400_3 := h1400c.2.2.2
                    linarith only [hlam, p1400_0]
                  · have p1400_0 := h1400c.1
                    have p1400_1 := h1400c.2.1
                    have p1400_2 := h1400c.2.2.1
                    have p1400_3 := h1400c.2.2.2
                    linarith only [h10, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1400_1]
                  · have p1400_0 := h1400c.1
                    have p1400_1 := h1400c.2.1
                    have p1400_2 := h1400c.2.2.1
                    have p1400_3 := h1400c.2.2.2
                    linarith only [h10, h1383, h1394, h1396, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1400_1]
                  · have p1400_0 := h1400c.1
                    have p1400_1 := h1400c.2.1
                    have p1400_2 := h1400c.2.2.1
                    have p1400_3 := h1400c.2.2.2
                    linarith only [h1382, h1386, h1394, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1400_1]
                  · have p1400_0 := h1400c.1
                    have p1400_1 := h1400c.2.1
                    have p1400_2 := h1400c.2.2.1
                    have p1400_3 := h1400c.2.2.2
                    rcases p1400_3 (m.d 0 1) (by simp) with h1405 | h1405
                    · rcases p1400_3 (m.d 0 2) (by simp) with h1406 | h1406
                      · linarith only [h0, h1406, hlam]
                      · linarith only [h1406, h6, hlam]
                    · linarith only [h1405, h3, hlam]
                  · have p1400_0 := h1400c.1
                    have p1400_1 := h1400c.2.1
                    have p1400_2 := h1400c.2.2.1
                    have p1400_3 := h1400c.2.2.2
                    linarith only [h0, hlam, p1400_0]
                  · have p1400_0 := h1400c.1
                    have p1400_1 := h1400c.2.1
                    have p1400_2 := h1400c.2.2.1
                    have p1400_3 := h1400c.2.2.2
                    linarith only [hlam, p1400_0]
                  · have p1400_0 := h1400c.1
                    have p1400_1 := h1400c.2.1
                    have p1400_2 := h1400c.2.2.1
                    have p1400_3 := h1400c.2.2.2
                    linarith only [h10, h1383, h1394, h1396, h4, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p1400_1]
                  · have p1400_0 := h1400c.1
                    have p1400_1 := h1400c.2.1
                    have p1400_2 := h1400c.2.2.1
                    have p1400_3 := h1400c.2.2.2
                    linarith only [h0, h1382, h1386, h1394, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1400_1]
                  · have p1400_0 := h1400c.1
                    have p1400_1 := h1400c.2.1
                    have p1400_2 := h1400c.2.2.1
                    have p1400_3 := h1400c.2.2.2
                    rcases p1400_3 (m.d 0 1) (by simp) with h1414 | h1414
                    · rcases p1400_3 (m.d 0 2) (by simp) with h1415 | h1415
                      · rcases p1400_3 (m.d 0 3) (by simp) with h1416 | h1416
                        · linarith only [h1416, h4, hlam]
                        · linarith only [h1416, h8, hlam]
                      · linarith only [h1415, h6, hlam]
                    · linarith only [h1414, h3, hlam]
                  · have p1400_0 := h1400c.1
                    have p1400_1 := h1400c.2.1
                    have p1400_2 := h1400c.2.2.1
                    have p1400_3 := h1400c.2.2.2
                    linarith only [h1, hlam, p1400_1]
                  · have p1400_0 := h1400c.1
                    have p1400_1 := h1400c.2.1
                    have p1400_2 := h1400c.2.2.1
                    have p1400_3 := h1400c.2.2.2
                    linarith only [h4, hlam, p1400_1]
                  · have p1400_0 := h1400c.1
                    have p1400_1 := h1400c.2.1
                    have p1400_2 := h1400c.2.2.1
                    have p1400_3 := h1400c.2.2.2
                    linarith only [hlam, p1400_0]
                  · have p1400_0 := h1400c.1
                    have p1400_1 := h1400c.2.1
                    have p1400_2 := h1400c.2.2.1
                    have p1400_3 := h1400c.2.2.2
                    linarith only [h1382, h1386, h1394, h9, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p1400_1]
                  · have p1400_0 := h1400c.1
                    have p1400_1 := h1400c.2.1
                    have p1400_2 := h1400c.2.2.1
                    have p1400_3 := h1400c.2.2.2
                    rcases p1400_3 (m.d 0 1) (by simp) with h1425 | h1425
                    · rcases p1400_3 (m.d 0 2) (by simp) with h1426 | h1426
                      · rcases p1400_3 (m.d 0 3) (by simp) with h1427 | h1427
                        · rcases p1400_3 (m.d 0 4) (by simp) with h1428 | h1428
                          · linarith only [h1428, h7, hlam]
                          · linarith only [h1428, h9, hlam]
                        · linarith only [h1427, h8, hlam]
                      · linarith only [h1426, h6, hlam]
                    · linarith only [h1425, h3, hlam]
                  · have p1400_0 := h1400c.1
                    have p1400_1 := h1400c.2.1
                    have p1400_2 := h1400c.2.2.1
                    have p1400_3 := h1400c.2.2.2
                    linarith only [h2, hlam, p1400_0]
                  · have p1400_0 := h1400c.1
                    have p1400_1 := h1400c.2.1
                    have p1400_2 := h1400c.2.2.1
                    have p1400_3 := h1400c.2.2.2
                    linarith only [h5, hlam, p1400_0]
                  · have p1400_0 := h1400c.1
                    have p1400_1 := h1400c.2.1
                    have p1400_2 := h1400c.2.2.1
                    have p1400_3 := h1400c.2.2.2
                    linarith only [h7, hlam, p1400_0]
                  · have p1400_0 := h1400c.1
                    have p1400_1 := h1400c.2.1
                    have p1400_2 := h1400c.2.2.1
                    have p1400_3 := h1400c.2.2.2
                    linarith only [hlam, p1400_0]
                  · have p1400_0 := h1400c.1
                    have p1400_1 := h1400c.2.1
                    have p1400_2 := h1400c.2.2.1
                    have p1400_3 := h1400c.2.2.2
                    rcases p1400_3 (m.d 0 1) (by simp) with h1438 | h1438
                    · rcases p1400_3 (m.d 0 2) (by simp) with h1439 | h1439
                      · rcases p1400_3 (m.d 0 3) (by simp) with h1440 | h1440
                        · rcases p1400_3 (m.d 0 4) (by simp) with h1441 | h1441
                          · rcases p1400_3 (m.d 0 5) (by simp) with h1442 | h1442
                            · linarith only [h1442, h9, hlam]
                            · rcases h2bigk with h1444c | h1444c | h1444c | h1444c | h1444c | h1444c | h1444c | h1444c | h1444c | h1444c | h1444c | h1444c | h1444c | h1444c | h1444c | h1444c | h1444c | h1444c | h1444c | h1444c | h1444c | h1444c | h1444c | h1444c | h1444c
                              · have p1444_0 := h1444c.1
                                have p1444_1 := h1444c.2.1
                                have p1444_2 := h1444c.2.2.1
                                have p1444_3 := h1444c.2.2.2
                                linarith only [hlam, p1444_0]
                              · have p1444_0 := h1444c.1
                                have p1444_1 := h1444c.2.1
                                have p1444_2 := h1444c.2.2.1
                                have p1444_3 := h1444c.2.2.2
                                rcases p1444_3 (m.d 0 2) (by simp) with h1446 | h1446
                                · rcases p1444_3 (m.d 1 2) (by simp) with h1447 | h1447
                                  · linarith only [h0, h1447, hlam]
                                  · rcases p1444_3 (m.d 2 3) (by simp) with h1449 | h1449
                                    · linarith only [h1449, h4, hlam]
                                    · linarith only [h10, h1449, hlam]
                                · linarith only [h0, h1446, hlam]
                              · have p1444_0 := h1444c.1
                                have p1444_1 := h1444c.2.1
                                have p1444_2 := h1444c.2.2.1
                                have p1444_3 := h1444c.2.2.2
                                linarith only [h0, h10, h1383, h1394, h1396, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1444_1]
                              · have p1444_0 := h1444c.1
                                have p1444_1 := h1444c.2.1
                                have p1444_2 := h1444c.2.2.1
                                have p1444_3 := h1444c.2.2.2
                                linarith only [h10, h1383, h1396, h4, hlam, p1444_2]
                              · have p1444_0 := h1444c.1
                                have p1444_1 := h1444c.2.1
                                have p1444_2 := h1444c.2.2.1
                                have p1444_3 := h1444c.2.2.2
                                linarith only [h10, h1383, h4, hlam, p1444_2]
                              · have p1444_0 := h1444c.1
                                have p1444_1 := h1444c.2.1
                                have p1444_2 := h1444c.2.2.1
                                have p1444_3 := h1444c.2.2.2
                                linarith only [h0, hlam, p1444_0]
                              · have p1444_0 := h1444c.1
                                have p1444_1 := h1444c.2.1
                                have p1444_2 := h1444c.2.2.1
                                have p1444_3 := h1444c.2.2.2
                                linarith only [hlam, p1444_0]
                              · have p1444_0 := h1444c.1
                                have p1444_1 := h1444c.2.1
                                have p1444_2 := h1444c.2.2.1
                                have p1444_3 := h1444c.2.2.2
                                linarith only [h10, hlam, p1444_0]
                              · have p1444_0 := h1444c.1
                                have p1444_1 := h1444c.2.1
                                have p1444_2 := h1444c.2.2.1
                                have p1444_3 := h1444c.2.2.2
                                linarith only [h10, h1394, h4, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p1444_1]
                              · have p1444_0 := h1444c.1
                                have p1444_1 := h1444c.2.1
                                have p1444_2 := h1444c.2.2.1
                                have p1444_3 := h1444c.2.2.2
                                linarith only [h10, h4, hc02, hc25, hlam, hphi, ht0b, ht5b, p1444_1]
                              · have p1444_0 := h1444c.1
                                have p1444_1 := h1444c.2.1
                                have p1444_2 := h1444c.2.2.1
                                have p1444_3 := h1444c.2.2.2
                                linarith only [h4, hlam, p1444_0]
                              · have p1444_0 := h1444c.1
                                have p1444_1 := h1444c.2.1
                                have p1444_2 := h1444c.2.2.1
                                have p1444_3 := h1444c.2.2.2
                                linarith only [h0, h1382, h1394, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1444_1]
                              · have p1444_0 := h1444c.1
                                have p1444_1 := h1444c.2.1
                                have p1444_2 := h1444c.2.2.1
                                have p1444_3 := h1444c.2.2.2
                                linarith only [hlam, p1444_0]
                              · have p1444_0 := h1444c.1
                                have p1444_1 := h1444c.2.1
                                have p1444_2 := h1444c.2.2.1
                                have p1444_3 := h1444c.2.2.2
                                rcases p1444_3 (m.d 0 2) (by simp) with h1464 | h1464
                                · rcases p1444_3 (m.d 1 2) (by simp) with h1465 | h1465
                                  · linarith only [h10, h1465, hlam]
                                  · linarith only [h1382, h1465, hlam]
                                · linarith only [h1464, h5, hlam]
                              · have p1444_0 := h1444c.1
                                have p1444_1 := h1444c.2.1
                                have p1444_2 := h1444c.2.2.1
                                have p1444_3 := h1444c.2.2.2
                                rcases p1444_3 (m.d 0 2) (by simp) with h1469 | h1469
                                · rcases p1444_3 (m.d 1 2) (by simp) with h1470 | h1470
                                  · linarith only [h10, h1470, hlam]
                                  · linarith only [h1383, h1470, hlam]
                                · linarith only [h1469, h6, hlam]
                              · have p1444_0 := h1444c.1
                                have p1444_1 := h1444c.2.1
                                have p1444_2 := h1444c.2.2.1
                                have p1444_3 := h1444c.2.2.2
                                linarith only [h5, hlam, p1444_0]
                              · have p1444_0 := h1444c.1
                                have p1444_1 := h1444c.2.1
                                have p1444_2 := h1444c.2.2.1
                                have p1444_3 := h1444c.2.2.2
                                linarith only [h1382, hlam, p1444_0]
                              · have p1444_0 := h1444c.1
                                have p1444_1 := h1444c.2.1
                                have p1444_2 := h1444c.2.2.1
                                have p1444_3 := h1444c.2.2.2
                                linarith only [h1394, hlam, p1444_1]
                              · have p1444_0 := h1444c.1
                                have p1444_1 := h1444c.2.1
                                have p1444_2 := h1444c.2.2.1
                                have p1444_3 := h1444c.2.2.2
                                linarith only [hlam, p1444_0]
                              · have p1444_0 := h1444c.1
                                have p1444_1 := h1444c.2.1
                                have p1444_2 := h1444c.2.2.1
                                have p1444_3 := h1444c.2.2.2
                                linarith only [h1396, hlam, p1444_1]
                              · have p1444_0 := h1444c.1
                                have p1444_1 := h1444c.2.1
                                have p1444_2 := h1444c.2.2.1
                                have p1444_3 := h1444c.2.2.2
                                linarith only [h6, hlam, p1444_0]
                              · have p1444_0 := h1444c.1
                                have p1444_1 := h1444c.2.1
                                have p1444_2 := h1444c.2.2.1
                                have p1444_3 := h1444c.2.2.2
                                linarith only [h1383, hlam, p1444_0]
                              · have p1444_0 := h1444c.1
                                have p1444_1 := h1444c.2.1
                                have p1444_2 := h1444c.2.2.1
                                have p1444_3 := h1444c.2.2.2
                                linarith only [h1395, hlam, p1444_1]
                              · have p1444_0 := h1444c.1
                                have p1444_1 := h1444c.2.1
                                have p1444_2 := h1444c.2.2.1
                                have p1444_3 := h1444c.2.2.2
                                linarith only [h0, h1383, h1394, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1444_1]
                              · have p1444_0 := h1444c.1
                                have p1444_1 := h1444c.2.1
                                have p1444_2 := h1444c.2.2.1
                                have p1444_3 := h1444c.2.2.2
                                linarith only [hlam, p1444_0]
                          · linarith only [h1441, h9, hlam]
                        · linarith only [h1440, h8, hlam]
                      · linarith only [h1439, h6, hlam]
                    · linarith only [h1438, h3, hlam]
                  · have p1400_0 := h1400c.1
                    have p1400_1 := h1400c.2.1
                    have p1400_2 := h1400c.2.2.1
                    have p1400_3 := h1400c.2.2.2
                    linarith only [h3, hlam, p1400_0]
                  · have p1400_0 := h1400c.1
                    have p1400_1 := h1400c.2.1
                    have p1400_2 := h1400c.2.2.1
                    have p1400_3 := h1400c.2.2.2
                    linarith only [h6, hlam, p1400_1]
                  · have p1400_0 := h1400c.1
                    have p1400_1 := h1400c.2.1
                    have p1400_2 := h1400c.2.2.1
                    have p1400_3 := h1400c.2.2.2
                    linarith only [h8, hlam, p1400_0]
                  · have p1400_0 := h1400c.1
                    have p1400_1 := h1400c.2.1
                    have p1400_2 := h1400c.2.2.1
                    have p1400_3 := h1400c.2.2.2
                    linarith only [h9, hlam, p1400_1]
                  · have p1400_0 := h1400c.1
                    have p1400_1 := h1400c.2.1
                    have p1400_2 := h1400c.2.2.1
                    have p1400_3 := h1400c.2.2.2
                    linarith only [hlam, p1400_0]
            · linarith only [h0, h10, h1382, h1394, h1395, h4, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
          · linarith only [h0, h10, h1382, h1394, h4, h7, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
      · linarith only [h10, h1383, h1385, hlam]
    · linarith only [h10, h1382, h1384, hlam]
  · rcases m.htr 1 3 4 (by decide) (by decide) with h1497 | h1497
    · rcases m.htr 1 3 5 (by decide) (by decide) with h1498 | h1498
      · rcases m.htr 1 4 5 (by decide) (by decide) with h1499 | h1499
        · linarith only [h1382, h1383, h1499, hlam]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h1501 | h1501
          · rcases m.htr 2 3 5 (by decide) (by decide) with h1502 | h1502
            · rcases m.htr 2 4 5 (by decide) (by decide) with h1503 | h1503
              · linarith only [h1382, h1383, h1499, h1502, h1503, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h1505 | h1505
                · linarith only [h1382, h1383, h1501, h1503, h1505, hlam]
                · rcases h0bigk with h1507c | h1507c | h1507c | h1507c | h1507c | h1507c | h1507c | h1507c | h1507c | h1507c | h1507c | h1507c | h1507c | h1507c | h1507c | h1507c | h1507c | h1507c | h1507c | h1507c | h1507c | h1507c | h1507c | h1507c | h1507c
                  · have p1507_0 := h1507c.1
                    have p1507_1 := h1507c.2.1
                    have p1507_2 := h1507c.2.2.1
                    have p1507_3 := h1507c.2.2.2
                    linarith only [hlam, p1507_0]
                  · have p1507_0 := h1507c.1
                    have p1507_1 := h1507c.2.1
                    have p1507_2 := h1507c.2.2.1
                    have p1507_3 := h1507c.2.2.2
                    linarith only [h1383, h1503, h4, h7, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1507_1]
                  · have p1507_0 := h1507c.1
                    have p1507_1 := h1507c.2.1
                    have p1507_2 := h1507c.2.2.1
                    have p1507_3 := h1507c.2.2.2
                    linarith only [h1382, h1383, h1501, h1503, h7, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1507_1]
                  · have p1507_0 := h1507c.1
                    have p1507_1 := h1507c.2.1
                    have p1507_2 := h1507c.2.2.1
                    have p1507_3 := h1507c.2.2.2
                    linarith only [h1382, h1383, h1501, h1503, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1507_1]
                  · have p1507_0 := h1507c.1
                    have p1507_1 := h1507c.2.1
                    have p1507_2 := h1507c.2.2.1
                    have p1507_3 := h1507c.2.2.2
                    linarith only [h1382, h1383, h1501, h6, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1507_1]
                  · have p1507_0 := h1507c.1
                    have p1507_1 := h1507c.2.1
                    have p1507_2 := h1507c.2.2.1
                    have p1507_3 := h1507c.2.2.2
                    linarith only [h0, hlam, p1507_0]
                  · have p1507_0 := h1507c.1
                    have p1507_1 := h1507c.2.1
                    have p1507_2 := h1507c.2.2.1
                    have p1507_3 := h1507c.2.2.2
                    linarith only [hlam, p1507_0]
                  · have p1507_0 := h1507c.1
                    have p1507_1 := h1507c.2.1
                    have p1507_2 := h1507c.2.2.1
                    have p1507_3 := h1507c.2.2.2
                    linarith only [h1382, h1383, h1501, h1503, h7, h9, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p1507_1]
                  · have p1507_0 := h1507c.1
                    have p1507_1 := h1507c.2.1
                    have p1507_2 := h1507c.2.2.1
                    have p1507_3 := h1507c.2.2.2
                    linarith only [h0, h1382, h1383, h1501, h1503, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1507_1]
                  · have p1507_0 := h1507c.1
                    have p1507_1 := h1507c.2.1
                    have p1507_2 := h1507c.2.2.1
                    have p1507_3 := h1507c.2.2.2
                    linarith only [h0, h1382, h1383, h1501, h6, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1507_1]
                  · have p1507_0 := h1507c.1
                    have p1507_1 := h1507c.2.1
                    have p1507_2 := h1507c.2.2.1
                    have p1507_3 := h1507c.2.2.2
                    linarith only [h1, hlam, p1507_1]
                  · have p1507_0 := h1507c.1
                    have p1507_1 := h1507c.2.1
                    have p1507_2 := h1507c.2.2.1
                    have p1507_3 := h1507c.2.2.2
                    linarith only [h4, hlam, p1507_1]
                  · have p1507_0 := h1507c.1
                    have p1507_1 := h1507c.2.1
                    have p1507_2 := h1507c.2.2.1
                    have p1507_3 := h1507c.2.2.2
                    linarith only [hlam, p1507_0]
                  · have p1507_0 := h1507c.1
                    have p1507_1 := h1507c.2.1
                    have p1507_2 := h1507c.2.2.1
                    have p1507_3 := h1507c.2.2.2
                    linarith only [h1382, h1383, h1501, h1503, h9, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p1507_1]
                  · have p1507_0 := h1507c.1
                    have p1507_1 := h1507c.2.1
                    have p1507_2 := h1507c.2.2.1
                    have p1507_3 := h1507c.2.2.2
                    linarith only [h0, h1382, h1383, h1501, h4, h6, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1507_1]
                  · have p1507_0 := h1507c.1
                    have p1507_1 := h1507c.2.1
                    have p1507_2 := h1507c.2.2.1
                    have p1507_3 := h1507c.2.2.2
                    linarith only [h2, hlam, p1507_0]
                  · have p1507_0 := h1507c.1
                    have p1507_1 := h1507c.2.1
                    have p1507_2 := h1507c.2.2.1
                    have p1507_3 := h1507c.2.2.2
                    linarith only [h5, hlam, p1507_0]
                  · have p1507_0 := h1507c.1
                    have p1507_1 := h1507c.2.1
                    have p1507_2 := h1507c.2.2.1
                    have p1507_3 := h1507c.2.2.2
                    linarith only [h7, hlam, p1507_0]
                  · have p1507_0 := h1507c.1
                    have p1507_1 := h1507c.2.1
                    have p1507_2 := h1507c.2.2.1
                    have p1507_3 := h1507c.2.2.2
                    linarith only [hlam, p1507_0]
                  · have p1507_0 := h1507c.1
                    have p1507_1 := h1507c.2.1
                    have p1507_2 := h1507c.2.2.1
                    have p1507_3 := h1507c.2.2.2
                    linarith only [h1382, h1383, h1501, h6, hc04, hc34, hlam, hphi, ht0b, ht45, ht5b, p1507_1]
                  · have p1507_0 := h1507c.1
                    have p1507_1 := h1507c.2.1
                    have p1507_2 := h1507c.2.2.1
                    have p1507_3 := h1507c.2.2.2
                    linarith only [h3, hlam, p1507_0]
                  · have p1507_0 := h1507c.1
                    have p1507_1 := h1507c.2.1
                    have p1507_2 := h1507c.2.2.1
                    have p1507_3 := h1507c.2.2.2
                    linarith only [h6, hlam, p1507_1]
                  · have p1507_0 := h1507c.1
                    have p1507_1 := h1507c.2.1
                    have p1507_2 := h1507c.2.2.1
                    have p1507_3 := h1507c.2.2.2
                    linarith only [h8, hlam, p1507_0]
                  · have p1507_0 := h1507c.1
                    have p1507_1 := h1507c.2.1
                    have p1507_2 := h1507c.2.2.1
                    have p1507_3 := h1507c.2.2.2
                    linarith only [h9, hlam, p1507_1]
                  · have p1507_0 := h1507c.1
                    have p1507_1 := h1507c.2.1
                    have p1507_2 := h1507c.2.2.1
                    have p1507_3 := h1507c.2.2.2
                    linarith only [hlam, p1507_0]
            · linarith only [h10, h1382, h1498, h1501, h1502, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
          · linarith only [h0, h10, h1382, h1501, h4, h7, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
      · rcases m.htr 1 4 5 (by decide) (by decide) with h1535 | h1535
        · linarith only [h10, h1382, h1498, h1535, hlam]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h1537 | h1537
          · rcases m.htr 2 3 5 (by decide) (by decide) with h1538 | h1538
            · linarith only [h0, h10, h1382, h1498, h1538, h4, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
            · linarith only [h0, h10, h1382, h1537, h1538, h4, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
          · linarith only [h0, h10, h1382, h1537, h4, h7, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
    · linarith only [h10, h1382, h1497, hlam]

set_option maxHeartbeats 5108000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s9_x1_x1_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg9 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h10 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h1382 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (h1543 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
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
  have h7 := hg7
  have h8 := hg8
  have h9 := hg9
  rcases m.htr 1 3 4 (by decide) (by decide) with h1544 | h1544
  · rcases m.htr 1 3 5 (by decide) (by decide) with h1545 | h1545
    · rcases m.htr 1 4 5 (by decide) (by decide) with h1546 | h1546
      · rcases m.htr 2 3 4 (by decide) (by decide) with h1547 | h1547
        · rcases m.htr 2 3 5 (by decide) (by decide) with h1548 | h1548
          · rcases m.htr 2 4 5 (by decide) (by decide) with h1549 | h1549
            · rcases m.htr 3 4 5 (by decide) (by decide) with h1550 | h1550
              · rcases h0bigk with h1551c | h1551c | h1551c | h1551c | h1551c | h1551c | h1551c | h1551c | h1551c | h1551c | h1551c | h1551c | h1551c | h1551c | h1551c | h1551c | h1551c | h1551c | h1551c | h1551c | h1551c | h1551c | h1551c | h1551c | h1551c
                · have p1551_0 := h1551c.1
                  have p1551_1 := h1551c.2.1
                  have p1551_2 := h1551c.2.2.1
                  have p1551_3 := h1551c.2.2.2
                  linarith only [hlam, p1551_0]
                · have p1551_0 := h1551c.1
                  have p1551_1 := h1551c.2.1
                  have p1551_2 := h1551c.2.2.1
                  have p1551_3 := h1551c.2.2.2
                  linarith only [h1, h1544, h1550, h4, hc01, hc45, hlam, hphi, ht0b, ht5b, p1551_1]
                · have p1551_0 := h1551c.1
                  have p1551_1 := h1551c.2.1
                  have p1551_2 := h1551c.2.2.1
                  have p1551_3 := h1551c.2.2.2
                  linarith only [h1, h1544, h1550, hc01, hc45, hlam, hphi, ht0b, ht5b, p1551_1]
                · have p1551_0 := h1551c.1
                  have p1551_1 := h1551c.2.1
                  have p1551_2 := h1551c.2.2.1
                  have p1551_3 := h1551c.2.2.2
                  linarith only [h1382, h1543, h1548, h1550, h5, hc01, hc45, hlam, hphi, ht0b, ht5b, p1551_1]
                · have p1551_0 := h1551c.1
                  have p1551_1 := h1551c.2.1
                  have p1551_2 := h1551c.2.2.1
                  have p1551_3 := h1551c.2.2.2
                  rcases p1551_3 (m.d 0 1) (by simp) with h1556 | h1556
                  · rcases p1551_3 (m.d 0 2) (by simp) with h1557 | h1557
                    · linarith only [h0, h1557, hlam]
                    · linarith only [h1557, h6, hlam]
                  · linarith only [h1556, h3, hlam]
                · have p1551_0 := h1551c.1
                  have p1551_1 := h1551c.2.1
                  have p1551_2 := h1551c.2.2.1
                  have p1551_3 := h1551c.2.2.2
                  linarith only [h0, hlam, p1551_0]
                · have p1551_0 := h1551c.1
                  have p1551_1 := h1551c.2.1
                  have p1551_2 := h1551c.2.2.1
                  have p1551_3 := h1551c.2.2.2
                  linarith only [hlam, p1551_0]
                · have p1551_0 := h1551c.1
                  have p1551_1 := h1551c.2.1
                  have p1551_2 := h1551c.2.2.1
                  have p1551_3 := h1551c.2.2.2
                  linarith only [h1382, h1543, h1547, h1548, h1550, h4, hc02, hc45, hlam, hphi, ht0b, ht5b, p1551_1]
                · have p1551_0 := h1551c.1
                  have p1551_1 := h1551c.2.1
                  have p1551_2 := h1551c.2.2.1
                  have p1551_3 := h1551c.2.2.2
                  linarith only [h0, h1382, h1543, h1548, h1550, h5, hc01, hc45, hlam, hphi, ht0b, ht5b, p1551_1]
                · have p1551_0 := h1551c.1
                  have p1551_1 := h1551c.2.1
                  have p1551_2 := h1551c.2.2.1
                  have p1551_3 := h1551c.2.2.2
                  rcases p1551_3 (m.d 0 1) (by simp) with h1565 | h1565
                  · rcases p1551_3 (m.d 0 2) (by simp) with h1566 | h1566
                    · rcases p1551_3 (m.d 0 3) (by simp) with h1567 | h1567
                      · linarith only [h1567, h4, hlam]
                      · linarith only [h1567, h8, hlam]
                    · linarith only [h1566, h6, hlam]
                  · linarith only [h1565, h3, hlam]
                · have p1551_0 := h1551c.1
                  have p1551_1 := h1551c.2.1
                  have p1551_2 := h1551c.2.2.1
                  have p1551_3 := h1551c.2.2.2
                  linarith only [h1, hlam, p1551_1]
                · have p1551_0 := h1551c.1
                  have p1551_1 := h1551c.2.1
                  have p1551_2 := h1551c.2.2.1
                  have p1551_3 := h1551c.2.2.2
                  linarith only [h4, hlam, p1551_1]
                · have p1551_0 := h1551c.1
                  have p1551_1 := h1551c.2.1
                  have p1551_2 := h1551c.2.2.1
                  have p1551_3 := h1551c.2.2.2
                  linarith only [hlam, p1551_0]
                · have p1551_0 := h1551c.1
                  have p1551_1 := h1551c.2.1
                  have p1551_2 := h1551c.2.2.1
                  have p1551_3 := h1551c.2.2.2
                  linarith only [h1382, h1543, h1548, h1550, h5, hc03, hc45, hlam, hphi, ht0b, ht5b, p1551_1]
                · have p1551_0 := h1551c.1
                  have p1551_1 := h1551c.2.1
                  have p1551_2 := h1551c.2.2.1
                  have p1551_3 := h1551c.2.2.2
                  rcases p1551_3 (m.d 0 1) (by simp) with h1576 | h1576
                  · rcases p1551_3 (m.d 0 2) (by simp) with h1577 | h1577
                    · rcases p1551_3 (m.d 0 3) (by simp) with h1578 | h1578
                      · rcases p1551_3 (m.d 0 4) (by simp) with h1579 | h1579
                        · linarith only [h1579, h7, hlam]
                        · linarith only [h1579, h9, hlam]
                      · linarith only [h1578, h8, hlam]
                    · linarith only [h1577, h6, hlam]
                  · linarith only [h1576, h3, hlam]
                · have p1551_0 := h1551c.1
                  have p1551_1 := h1551c.2.1
                  have p1551_2 := h1551c.2.2.1
                  have p1551_3 := h1551c.2.2.2
                  linarith only [h2, hlam, p1551_0]
                · have p1551_0 := h1551c.1
                  have p1551_1 := h1551c.2.1
                  have p1551_2 := h1551c.2.2.1
                  have p1551_3 := h1551c.2.2.2
                  linarith only [h5, hlam, p1551_0]
                · have p1551_0 := h1551c.1
                  have p1551_1 := h1551c.2.1
                  have p1551_2 := h1551c.2.2.1
                  have p1551_3 := h1551c.2.2.2
                  linarith only [h7, hlam, p1551_0]
                · have p1551_0 := h1551c.1
                  have p1551_1 := h1551c.2.1
                  have p1551_2 := h1551c.2.2.1
                  have p1551_3 := h1551c.2.2.2
                  linarith only [hlam, p1551_0]
                · have p1551_0 := h1551c.1
                  have p1551_1 := h1551c.2.1
                  have p1551_2 := h1551c.2.2.1
                  have p1551_3 := h1551c.2.2.2
                  rcases p1551_3 (m.d 0 1) (by simp) with h1589 | h1589
                  · rcases p1551_3 (m.d 0 2) (by simp) with h1590 | h1590
                    · rcases p1551_3 (m.d 0 3) (by simp) with h1591 | h1591
                      · rcases p1551_3 (m.d 0 4) (by simp) with h1592 | h1592
                        · rcases p1551_3 (m.d 0 5) (by simp) with h1593 | h1593
                          · linarith only [h1593, h9, hlam]
                          · rcases h2bigk with h1595c | h1595c | h1595c | h1595c | h1595c | h1595c | h1595c | h1595c | h1595c | h1595c | h1595c | h1595c | h1595c | h1595c | h1595c | h1595c | h1595c | h1595c | h1595c | h1595c | h1595c | h1595c | h1595c | h1595c | h1595c
                            · have p1595_0 := h1595c.1
                              have p1595_1 := h1595c.2.1
                              have p1595_2 := h1595c.2.2.1
                              have p1595_3 := h1595c.2.2.2
                              linarith only [hlam, p1595_0]
                            · have p1595_0 := h1595c.1
                              have p1595_1 := h1595c.2.1
                              have p1595_2 := h1595c.2.2.1
                              have p1595_3 := h1595c.2.2.2
                              rcases p1595_3 (m.d 0 2) (by simp) with h1597 | h1597
                              · rcases p1595_3 (m.d 1 2) (by simp) with h1598 | h1598
                                · linarith only [h0, h1598, hlam]
                                · rcases p1595_3 (m.d 2 3) (by simp) with h1600 | h1600
                                  · linarith only [h1600, h4, hlam]
                                  · linarith only [h10, h1600, hlam]
                              · linarith only [h0, h1597, hlam]
                            · have p1595_0 := h1595c.1
                              have p1595_1 := h1595c.2.1
                              have p1595_2 := h1595c.2.2.1
                              have p1595_3 := h1595c.2.2.2
                              linarith only [h0, h1382, h1543, h1547, h1548, h1550, hc01, hc45, hlam, hphi, ht0b, ht5b, p1595_1]
                            · have p1595_0 := h1595c.1
                              have p1595_1 := h1595c.2.1
                              have p1595_2 := h1595c.2.2.1
                              have p1595_3 := h1595c.2.2.2
                              linarith only [h0, h1382, h1543, h1548, h1550, hc01, hc45, hlam, hphi, ht0b, ht5b, p1595_1]
                            · have p1595_0 := h1595c.1
                              have p1595_1 := h1595c.2.1
                              have p1595_2 := h1595c.2.2.1
                              have p1595_3 := h1595c.2.2.2
                              linarith only [h1382, h1543, h1547, h4, hlam, p1595_2]
                            · have p1595_0 := h1595c.1
                              have p1595_1 := h1595c.2.1
                              have p1595_2 := h1595c.2.2.1
                              have p1595_3 := h1595c.2.2.2
                              linarith only [h0, hlam, p1595_0]
                            · have p1595_0 := h1595c.1
                              have p1595_1 := h1595c.2.1
                              have p1595_2 := h1595c.2.2.1
                              have p1595_3 := h1595c.2.2.2
                              linarith only [hlam, p1595_0]
                            · have p1595_0 := h1595c.1
                              have p1595_1 := h1595c.2.1
                              have p1595_2 := h1595c.2.2.1
                              have p1595_3 := h1595c.2.2.2
                              linarith only [h10, hlam, p1595_0]
                            · have p1595_0 := h1595c.1
                              have p1595_1 := h1595c.2.1
                              have p1595_2 := h1595c.2.2.1
                              have p1595_3 := h1595c.2.2.2
                              linarith only [h1382, hlam, p1595_0]
                            · have p1595_0 := h1595c.1
                              have p1595_1 := h1595c.2.1
                              have p1595_2 := h1595c.2.2.1
                              have p1595_3 := h1595c.2.2.2
                              linarith only [h1382, h1547, h1548, h1550, h4, hc02, hc45, hlam, hphi, ht0b, ht5b, p1595_1]
                            · have p1595_0 := h1595c.1
                              have p1595_1 := h1595c.2.1
                              have p1595_2 := h1595c.2.2.1
                              have p1595_3 := h1595c.2.2.2
                              linarith only [h4, hlam, p1595_0]
                            · have p1595_0 := h1595c.1
                              have p1595_1 := h1595c.2.1
                              have p1595_2 := h1595c.2.2.1
                              have p1595_3 := h1595c.2.2.2
                              linarith only [h0, h1543, h1548, h1550, h4, hc01, hc45, hlam, hphi, ht0b, ht5b, p1595_1]
                            · have p1595_0 := h1595c.1
                              have p1595_1 := h1595c.2.1
                              have p1595_2 := h1595c.2.2.1
                              have p1595_3 := h1595c.2.2.2
                              linarith only [hlam, p1595_0]
                            · have p1595_0 := h1595c.1
                              have p1595_1 := h1595c.2.1
                              have p1595_2 := h1595c.2.2.1
                              have p1595_3 := h1595c.2.2.2
                              linarith only [h0, h1382, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1595_1]
                            · have p1595_0 := h1595c.1
                              have p1595_1 := h1595c.2.1
                              have p1595_2 := h1595c.2.2.1
                              have p1595_3 := h1595c.2.2.2
                              rcases p1595_3 (m.d 0 2) (by simp) with h1616 | h1616
                              · rcases p1595_3 (m.d 1 2) (by simp) with h1617 | h1617
                                · linarith only [h10, h1617, hlam]
                                · linarith only [h1543, h1617, hlam]
                              · linarith only [h1616, h6, hlam]
                            · have p1595_0 := h1595c.1
                              have p1595_1 := h1595c.2.1
                              have p1595_2 := h1595c.2.2.1
                              have p1595_3 := h1595c.2.2.2
                              linarith only [h5, hlam, p1595_0]
                            · have p1595_0 := h1595c.1
                              have p1595_1 := h1595c.2.1
                              have p1595_2 := h1595c.2.2.1
                              have p1595_3 := h1595c.2.2.2
                              linarith only [h0, h1543, h1548, h1550, h5, hc01, hc45, hlam, hphi, ht0b, ht5b, p1595_1]
                            · have p1595_0 := h1595c.1
                              have p1595_1 := h1595c.2.1
                              have p1595_2 := h1595c.2.2.1
                              have p1595_3 := h1595c.2.2.2
                              linarith only [h1547, hlam, p1595_1]
                            · have p1595_0 := h1595c.1
                              have p1595_1 := h1595c.2.1
                              have p1595_2 := h1595c.2.2.1
                              have p1595_3 := h1595c.2.2.2
                              linarith only [hlam, p1595_0]
                            · have p1595_0 := h1595c.1
                              have p1595_1 := h1595c.2.1
                              have p1595_2 := h1595c.2.2.1
                              have p1595_3 := h1595c.2.2.2
                              rcases p1595_3 (m.d 0 2) (by simp) with h1625 | h1625
                              · rcases p1595_3 (m.d 1 2) (by simp) with h1626 | h1626
                                · linarith only [h1382, h1626, hlam]
                                · linarith only [h1543, h1626, hlam]
                              · linarith only [h1625, h6, hlam]
                            · have p1595_0 := h1595c.1
                              have p1595_1 := h1595c.2.1
                              have p1595_2 := h1595c.2.2.1
                              have p1595_3 := h1595c.2.2.2
                              linarith only [h6, hlam, p1595_0]
                            · have p1595_0 := h1595c.1
                              have p1595_1 := h1595c.2.1
                              have p1595_2 := h1595c.2.2.1
                              have p1595_3 := h1595c.2.2.2
                              linarith only [h1543, hlam, p1595_0]
                            · have p1595_0 := h1595c.1
                              have p1595_1 := h1595c.2.1
                              have p1595_2 := h1595c.2.2.1
                              have p1595_3 := h1595c.2.2.2
                              linarith only [h1548, hlam, p1595_1]
                            · have p1595_0 := h1595c.1
                              have p1595_1 := h1595c.2.1
                              have p1595_2 := h1595c.2.2.1
                              have p1595_3 := h1595c.2.2.2
                              linarith only [h1549, hlam, p1595_0]
                            · have p1595_0 := h1595c.1
                              have p1595_1 := h1595c.2.1
                              have p1595_2 := h1595c.2.2.1
                              have p1595_3 := h1595c.2.2.2
                              linarith only [hlam, p1595_0]
                        · linarith only [h1592, h9, hlam]
                      · linarith only [h1591, h8, hlam]
                    · linarith only [h1590, h6, hlam]
                  · linarith only [h1589, h3, hlam]
                · have p1551_0 := h1551c.1
                  have p1551_1 := h1551c.2.1
                  have p1551_2 := h1551c.2.2.1
                  have p1551_3 := h1551c.2.2.2
                  linarith only [h3, hlam, p1551_0]
                · have p1551_0 := h1551c.1
                  have p1551_1 := h1551c.2.1
                  have p1551_2 := h1551c.2.2.1
                  have p1551_3 := h1551c.2.2.2
                  linarith only [h6, hlam, p1551_1]
                · have p1551_0 := h1551c.1
                  have p1551_1 := h1551c.2.1
                  have p1551_2 := h1551c.2.2.1
                  have p1551_3 := h1551c.2.2.2
                  linarith only [h8, hlam, p1551_0]
                · have p1551_0 := h1551c.1
                  have p1551_1 := h1551c.2.1
                  have p1551_2 := h1551c.2.2.1
                  have p1551_3 := h1551c.2.2.2
                  linarith only [h9, hlam, p1551_1]
                · have p1551_0 := h1551c.1
                  have p1551_1 := h1551c.2.1
                  have p1551_2 := h1551c.2.2.1
                  have p1551_3 := h1551c.2.2.2
                  linarith only [hlam, p1551_0]
              · linarith only [h0, h10, h1543, h1549, h1550, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
            · linarith only [h1382, h1543, h1544, h1546, h1549, hc13, hc25, hlam, hphi, ht01, ht0b, ht5b]
          · linarith only [h0, h1382, h1543, h1547, h1548, h4, h8, hc01, hc25, hlam, hphi, ht0b, ht5b]
        · linarith only [h0, h10, h1543, h1547, h4, h7, hc01, hc25, hlam, hphi, ht0b, ht5b]
      · linarith only [h1382, h1543, h1546, hlam]
    · linarith only [h1382, h1543, h1544, h1545, hlam]
  · rcases m.htr 1 3 5 (by decide) (by decide) with h1650 | h1650
    · rcases m.htr 1 4 5 (by decide) (by decide) with h1651 | h1651
      · rcases m.htr 2 3 4 (by decide) (by decide) with h1652 | h1652
        · linarith only [h0, h1544, h1650, h1652, h4, hc01, hc35, hlam, hphi, ht0b, ht5b]
        · linarith only [h0, h10, h1543, h1652, h4, h7, hc01, hc25, hlam, hphi, ht0b, ht5b]
      · linarith only [h10, h1543, h1544, h1651, hlam]
    · linarith only [h10, h1543, h1650, hlam]

end R2N4
