import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_2S1

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5020000 in
theorem r1l7_10_12_23_L_I_L_I_H_I_s9_x0_x1 (m : N7Model)
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
  rcases m.htr 1 2 5 (by decide) (by decide) with h1190 | h1190
  · rcases m.htr 1 3 4 (by decide) (by decide) with h1191 | h1191
    · linarith only [h10, h11, h1191, hlam]
    · rcases m.htr 1 3 5 (by decide) (by decide) with h1193 | h1193
      · rcases m.htr 1 4 5 (by decide) (by decide) with h1194 | h1194
        · rcases m.htr 2 3 4 (by decide) (by decide) with h1195 | h1195
          · linarith only [h0, h1191, h1193, h1195, h4, hc01, hc35, hlam, hphi, ht0b, ht5b]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h1197 | h1197
            · linarith only [h0, h10, h11, h1195, h1197, h4, h7, hc01, hc35, hlam, hphi, ht0b, ht5b]
            · linarith only [h0, h10, h11, h1193, h1195, h1197, h4, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
        · linarith only [h10, h11, h1193, h1194, hlam]
      · rcases m.htr 1 4 5 (by decide) (by decide) with h1201 | h1201
        · rcases m.htr 2 3 4 (by decide) (by decide) with h1202 | h1202
          · linarith only [h0, h10, h11, h1191, h1202, h5, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h1204 | h1204
            · linarith only [h0, h10, h11, h1193, h1202, h1204, h4, h7, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h1206 | h1206
              · rcases m.htr 3 4 5 (by decide) (by decide) with h1207 | h1207
                · rcases h0bigk with h1208c | h1208c | h1208c | h1208c | h1208c | h1208c | h1208c | h1208c | h1208c | h1208c | h1208c | h1208c | h1208c | h1208c | h1208c | h1208c | h1208c | h1208c | h1208c | h1208c | h1208c | h1208c | h1208c | h1208c | h1208c
                  · have p1208_0 := h1208c.1
                    have p1208_1 := h1208c.2.1
                    have p1208_2 := h1208c.2.2.1
                    have p1208_3 := h1208c.2.2.2
                    linarith only [hlam, p1208_0]
                  · have p1208_0 := h1208c.1
                    have p1208_1 := h1208c.2.1
                    have p1208_2 := h1208c.2.2.1
                    have p1208_3 := h1208c.2.2.2
                    linarith only [h11, h1202, h4, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1208_1]
                  · have p1208_0 := h1208c.1
                    have p1208_1 := h1208c.2.1
                    have p1208_2 := h1208c.2.2.1
                    have p1208_3 := h1208c.2.2.2
                    linarith only [h11, h1190, h1202, h1206, h7, hc01, hc45, hlam, hphi, ht0b, ht5b, p1208_1]
                  · have p1208_0 := h1208c.1
                    have p1208_1 := h1208c.2.1
                    have p1208_2 := h1208c.2.2.1
                    have p1208_3 := h1208c.2.2.2
                    linarith only [h11, h1190, h1206, h5, hc01, hc45, hlam, hphi, ht0b, ht5b, p1208_1]
                  · have p1208_0 := h1208c.1
                    have p1208_1 := h1208c.2.1
                    have p1208_2 := h1208c.2.2.1
                    have p1208_3 := h1208c.2.2.2
                    rcases p1208_3 (m.d 0 1) (by simp) with h1213 | h1213
                    · rcases p1208_3 (m.d 0 2) (by simp) with h1214 | h1214
                      · linarith only [h0, h1214, hlam]
                      · linarith only [h1214, h6, hlam]
                    · linarith only [h1213, h3, hlam]
                  · have p1208_0 := h1208c.1
                    have p1208_1 := h1208c.2.1
                    have p1208_2 := h1208c.2.2.1
                    have p1208_3 := h1208c.2.2.2
                    linarith only [h0, hlam, p1208_0]
                  · have p1208_0 := h1208c.1
                    have p1208_1 := h1208c.2.1
                    have p1208_2 := h1208c.2.2.1
                    have p1208_3 := h1208c.2.2.2
                    linarith only [hlam, p1208_0]
                  · have p1208_0 := h1208c.1
                    have p1208_1 := h1208c.2.1
                    have p1208_2 := h1208c.2.2.1
                    have p1208_3 := h1208c.2.2.2
                    linarith only [h11, h1190, h1202, h1204, h7, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1208_1]
                  · have p1208_0 := h1208c.1
                    have p1208_1 := h1208c.2.1
                    have p1208_2 := h1208c.2.2.1
                    have p1208_3 := h1208c.2.2.2
                    linarith only [h0, h11, h1190, h1202, h1204, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1208_1]
                  · have p1208_0 := h1208c.1
                    have p1208_1 := h1208c.2.1
                    have p1208_2 := h1208c.2.2.1
                    have p1208_3 := h1208c.2.2.2
                    rcases p1208_3 (m.d 0 1) (by simp) with h1222 | h1222
                    · rcases p1208_3 (m.d 0 2) (by simp) with h1223 | h1223
                      · rcases p1208_3 (m.d 0 3) (by simp) with h1224 | h1224
                        · linarith only [h1224, h4, hlam]
                        · linarith only [h1224, h8, hlam]
                      · linarith only [h1223, h6, hlam]
                    · linarith only [h1222, h3, hlam]
                  · have p1208_0 := h1208c.1
                    have p1208_1 := h1208c.2.1
                    have p1208_2 := h1208c.2.2.1
                    have p1208_3 := h1208c.2.2.2
                    linarith only [h1, hlam, p1208_1]
                  · have p1208_0 := h1208c.1
                    have p1208_1 := h1208c.2.1
                    have p1208_2 := h1208c.2.2.1
                    have p1208_3 := h1208c.2.2.2
                    linarith only [h4, hlam, p1208_1]
                  · have p1208_0 := h1208c.1
                    have p1208_1 := h1208c.2.1
                    have p1208_2 := h1208c.2.2.1
                    have p1208_3 := h1208c.2.2.2
                    linarith only [hlam, p1208_0]
                  · have p1208_0 := h1208c.1
                    have p1208_1 := h1208c.2.1
                    have p1208_2 := h1208c.2.2.1
                    have p1208_3 := h1208c.2.2.2
                    linarith only [h11, h1190, h1202, h1204, h7, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1208_1]
                  · have p1208_0 := h1208c.1
                    have p1208_1 := h1208c.2.1
                    have p1208_2 := h1208c.2.2.1
                    have p1208_3 := h1208c.2.2.2
                    rcases p1208_3 (m.d 0 1) (by simp) with h1233 | h1233
                    · rcases p1208_3 (m.d 0 2) (by simp) with h1234 | h1234
                      · rcases p1208_3 (m.d 0 3) (by simp) with h1235 | h1235
                        · rcases p1208_3 (m.d 0 4) (by simp) with h1236 | h1236
                          · linarith only [h1236, h7, hlam]
                          · linarith only [h1236, h9, hlam]
                        · linarith only [h1235, h8, hlam]
                      · linarith only [h1234, h6, hlam]
                    · linarith only [h1233, h3, hlam]
                  · have p1208_0 := h1208c.1
                    have p1208_1 := h1208c.2.1
                    have p1208_2 := h1208c.2.2.1
                    have p1208_3 := h1208c.2.2.2
                    linarith only [h2, hlam, p1208_0]
                  · have p1208_0 := h1208c.1
                    have p1208_1 := h1208c.2.1
                    have p1208_2 := h1208c.2.2.1
                    have p1208_3 := h1208c.2.2.2
                    linarith only [h5, hlam, p1208_0]
                  · have p1208_0 := h1208c.1
                    have p1208_1 := h1208c.2.1
                    have p1208_2 := h1208c.2.2.1
                    have p1208_3 := h1208c.2.2.2
                    linarith only [h7, hlam, p1208_0]
                  · have p1208_0 := h1208c.1
                    have p1208_1 := h1208c.2.1
                    have p1208_2 := h1208c.2.2.1
                    have p1208_3 := h1208c.2.2.2
                    linarith only [hlam, p1208_0]
                  · have p1208_0 := h1208c.1
                    have p1208_1 := h1208c.2.1
                    have p1208_2 := h1208c.2.2.1
                    have p1208_3 := h1208c.2.2.2
                    rcases p1208_3 (m.d 0 1) (by simp) with h1246 | h1246
                    · rcases p1208_3 (m.d 0 2) (by simp) with h1247 | h1247
                      · rcases p1208_3 (m.d 0 3) (by simp) with h1248 | h1248
                        · rcases p1208_3 (m.d 0 4) (by simp) with h1249 | h1249
                          · rcases p1208_3 (m.d 0 5) (by simp) with h1250 | h1250
                            · linarith only [h1250, h9, hlam]
                            · rcases h2bigk with h1252c | h1252c | h1252c | h1252c | h1252c | h1252c | h1252c | h1252c | h1252c | h1252c | h1252c | h1252c | h1252c | h1252c | h1252c | h1252c | h1252c | h1252c | h1252c | h1252c | h1252c | h1252c | h1252c | h1252c | h1252c
                              · have p1252_0 := h1252c.1
                                have p1252_1 := h1252c.2.1
                                have p1252_2 := h1252c.2.2.1
                                have p1252_3 := h1252c.2.2.2
                                linarith only [hlam, p1252_0]
                              · have p1252_0 := h1252c.1
                                have p1252_1 := h1252c.2.1
                                have p1252_2 := h1252c.2.2.1
                                have p1252_3 := h1252c.2.2.2
                                rcases p1252_3 (m.d 0 2) (by simp) with h1254 | h1254
                                · rcases p1252_3 (m.d 1 2) (by simp) with h1255 | h1255
                                  · linarith only [h0, h1255, hlam]
                                  · rcases p1252_3 (m.d 2 3) (by simp) with h1257 | h1257
                                    · linarith only [h1257, h4, hlam]
                                    · rcases p1252_3 (m.d 2 4) (by simp) with h1259 | h1259
                                      · linarith only [h1259, h5, hlam]
                                      · linarith only [h11, h1259, hlam]
                                · linarith only [h0, h1254, hlam]
                              · have p1252_0 := h1252c.1
                                have p1252_1 := h1252c.2.1
                                have p1252_2 := h1252c.2.2.1
                                have p1252_3 := h1252c.2.2.2
                                linarith only [h11, h1190, h1204, h5, hlam, p1252_2]
                              · have p1252_0 := h1252c.1
                                have p1252_1 := h1252c.2.1
                                have p1252_2 := h1252c.2.2.1
                                have p1252_3 := h1252c.2.2.2
                                linarith only [h11, h1190, h1204, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1252_1]
                              · have p1252_0 := h1252c.1
                                have p1252_1 := h1252c.2.1
                                have p1252_2 := h1252c.2.2.1
                                have p1252_3 := h1252c.2.2.2
                                linarith only [h11, h1190, h5, hlam, p1252_2]
                              · have p1252_0 := h1252c.1
                                have p1252_1 := h1252c.2.1
                                have p1252_2 := h1252c.2.2.1
                                have p1252_3 := h1252c.2.2.2
                                linarith only [h0, hlam, p1252_0]
                              · have p1252_0 := h1252c.1
                                have p1252_1 := h1252c.2.1
                                have p1252_2 := h1252c.2.2.1
                                have p1252_3 := h1252c.2.2.2
                                linarith only [hlam, p1252_0]
                              · have p1252_0 := h1252c.1
                                have p1252_1 := h1252c.2.1
                                have p1252_2 := h1252c.2.2.1
                                have p1252_3 := h1252c.2.2.2
                                linarith only [h11, h1202, hc23, hc34, hlam, hphi, p1252_1]
                              · have p1252_0 := h1252c.1
                                have p1252_1 := h1252c.2.1
                                have p1252_2 := h1252c.2.2.1
                                have p1252_3 := h1252c.2.2.2
                                linarith only [h11, hlam, p1252_0]
                              · have p1252_0 := h1252c.1
                                have p1252_1 := h1252c.2.1
                                have p1252_2 := h1252c.2.2.1
                                have p1252_3 := h1252c.2.2.2
                                linarith only [h0, h11, h1204, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1252_1]
                              · have p1252_0 := h1252c.1
                                have p1252_1 := h1252c.2.1
                                have p1252_2 := h1252c.2.2.1
                                have p1252_3 := h1252c.2.2.2
                                linarith only [h4, hlam, p1252_0]
                              · have p1252_0 := h1252c.1
                                have p1252_1 := h1252c.2.1
                                have p1252_2 := h1252c.2.2.1
                                have p1252_3 := h1252c.2.2.2
                                linarith only [h10, hlam, p1252_0]
                              · have p1252_0 := h1252c.1
                                have p1252_1 := h1252c.2.1
                                have p1252_2 := h1252c.2.2.1
                                have p1252_3 := h1252c.2.2.2
                                linarith only [hlam, p1252_0]
                              · have p1252_0 := h1252c.1
                                have p1252_1 := h1252c.2.1
                                have p1252_2 := h1252c.2.2.1
                                have p1252_3 := h1252c.2.2.2
                                linarith only [h1202, hlam, p1252_0]
                              · have p1252_0 := h1252c.1
                                have p1252_1 := h1252c.2.1
                                have p1252_2 := h1252c.2.2.1
                                have p1252_3 := h1252c.2.2.2
                                linarith only [h1204, hlam, p1252_0]
                              · have p1252_0 := h1252c.1
                                have p1252_1 := h1252c.2.1
                                have p1252_2 := h1252c.2.2.1
                                have p1252_3 := h1252c.2.2.2
                                linarith only [h5, hlam, p1252_0]
                              · have p1252_0 := h1252c.1
                                have p1252_1 := h1252c.2.1
                                have p1252_2 := h1252c.2.2.1
                                have p1252_3 := h1252c.2.2.2
                                linarith only [h0, h10, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1252_1]
                              · have p1252_0 := h1252c.1
                                have p1252_1 := h1252c.2.1
                                have p1252_2 := h1252c.2.2.1
                                have p1252_3 := h1252c.2.2.2
                                rcases p1252_3 (m.d 0 2) (by simp) with h1278 | h1278
                                · rcases p1252_3 (m.d 1 2) (by simp) with h1279 | h1279
                                  · linarith only [h11, h1279, hlam]
                                  · linarith only [h10, h1279, hlam]
                                · linarith only [h1278, h4, hlam]
                              · have p1252_0 := h1252c.1
                                have p1252_1 := h1252c.2.1
                                have p1252_2 := h1252c.2.2.1
                                have p1252_3 := h1252c.2.2.2
                                linarith only [hlam, p1252_0]
                              · have p1252_0 := h1252c.1
                                have p1252_1 := h1252c.2.1
                                have p1252_2 := h1252c.2.2.1
                                have p1252_3 := h1252c.2.2.2
                                rcases p1252_3 (m.d 0 2) (by simp) with h1284 | h1284
                                · rcases p1252_3 (m.d 1 2) (by simp) with h1285 | h1285
                                  · linarith only [h11, h1285, hlam]
                                  · linarith only [h1190, h1285, hlam]
                                · linarith only [h1284, h6, hlam]
                              · have p1252_0 := h1252c.1
                                have p1252_1 := h1252c.2.1
                                have p1252_2 := h1252c.2.2.1
                                have p1252_3 := h1252c.2.2.2
                                linarith only [h6, hlam, p1252_0]
                              · have p1252_0 := h1252c.1
                                have p1252_1 := h1252c.2.1
                                have p1252_2 := h1252c.2.2.1
                                have p1252_3 := h1252c.2.2.2
                                linarith only [h1190, hlam, p1252_0]
                              · have p1252_0 := h1252c.1
                                have p1252_1 := h1252c.2.1
                                have p1252_2 := h1252c.2.2.1
                                have p1252_3 := h1252c.2.2.2
                                linarith only [h0, h1190, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1252_1]
                              · have p1252_0 := h1252c.1
                                have p1252_1 := h1252c.2.1
                                have p1252_2 := h1252c.2.2.1
                                have p1252_3 := h1252c.2.2.2
                                linarith only [h1206, hlam, p1252_0]
                              · have p1252_0 := h1252c.1
                                have p1252_1 := h1252c.2.1
                                have p1252_2 := h1252c.2.2.1
                                have p1252_3 := h1252c.2.2.2
                                linarith only [hlam, p1252_0]
                          · linarith only [h1249, h9, hlam]
                        · linarith only [h1248, h8, hlam]
                      · linarith only [h1247, h6, hlam]
                    · linarith only [h1246, h3, hlam]
                  · have p1208_0 := h1208c.1
                    have p1208_1 := h1208c.2.1
                    have p1208_2 := h1208c.2.2.1
                    have p1208_3 := h1208c.2.2.2
                    linarith only [h3, hlam, p1208_0]
                  · have p1208_0 := h1208c.1
                    have p1208_1 := h1208c.2.1
                    have p1208_2 := h1208c.2.2.1
                    have p1208_3 := h1208c.2.2.2
                    linarith only [h6, hlam, p1208_1]
                  · have p1208_0 := h1208c.1
                    have p1208_1 := h1208c.2.1
                    have p1208_2 := h1208c.2.2.1
                    have p1208_3 := h1208c.2.2.2
                    linarith only [h8, hlam, p1208_0]
                  · have p1208_0 := h1208c.1
                    have p1208_1 := h1208c.2.1
                    have p1208_2 := h1208c.2.2.1
                    have p1208_3 := h1208c.2.2.2
                    linarith only [h9, hlam, p1208_1]
                  · have p1208_0 := h1208c.1
                    have p1208_1 := h1208c.2.1
                    have p1208_2 := h1208c.2.2.1
                    have p1208_3 := h1208c.2.2.2
                    linarith only [hlam, p1208_0]
                · linarith only [h11, h1190, h1202, h1207, h7, h9, hc03, hc25, hlam, hphi, ht0b, ht5b]
              · linarith only [h11, h1190, h1201, h1206, hlam]
        · linarith only [h11, h1190, h1201, hlam]
  · rcases m.htr 1 3 4 (by decide) (by decide) with h1306 | h1306
    · linarith only [h10, h11, h1306, hlam]
    · rcases m.htr 1 3 5 (by decide) (by decide) with h1308 | h1308
      · linarith only [h10, h1190, h1308, hlam]
      · rcases m.htr 1 4 5 (by decide) (by decide) with h1310 | h1310
        · rcases m.htr 2 3 4 (by decide) (by decide) with h1311 | h1311
          · linarith only [h0, h10, h1190, h1306, h1311, h6, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h1313 | h1313
            · linarith only [h0, h10, h11, h1308, h1311, h1313, h4, h7, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h1315 | h1315
              · rcases m.htr 3 4 5 (by decide) (by decide) with h1316 | h1316
                · rcases h0bigk with h1317c | h1317c | h1317c | h1317c | h1317c | h1317c | h1317c | h1317c | h1317c | h1317c | h1317c | h1317c | h1317c | h1317c | h1317c | h1317c | h1317c | h1317c | h1317c | h1317c | h1317c | h1317c | h1317c | h1317c | h1317c
                  · have p1317_0 := h1317c.1
                    have p1317_1 := h1317c.2.1
                    have p1317_2 := h1317c.2.2.1
                    have p1317_3 := h1317c.2.2.2
                    linarith only [hlam, p1317_0]
                  · have p1317_0 := h1317c.1
                    have p1317_1 := h1317c.2.1
                    have p1317_2 := h1317c.2.2.1
                    have p1317_3 := h1317c.2.2.2
                    linarith only [h1190, h1311, h1315, h4, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1317_1]
                  · have p1317_0 := h1317c.1
                    have p1317_1 := h1317c.2.1
                    have p1317_2 := h1317c.2.2.1
                    have p1317_3 := h1317c.2.2.2
                    linarith only [h1190, h1311, h1315, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1317_1]
                  · have p1317_0 := h1317c.1
                    have p1317_1 := h1317c.2.1
                    have p1317_2 := h1317c.2.2.1
                    have p1317_3 := h1317c.2.2.2
                    linarith only [h10, h1190, h1315, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1317_1]
                  · have p1317_0 := h1317c.1
                    have p1317_1 := h1317c.2.1
                    have p1317_2 := h1317c.2.2.1
                    have p1317_3 := h1317c.2.2.2
                    linarith only [h10, h1190, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1317_1]
                  · have p1317_0 := h1317c.1
                    have p1317_1 := h1317c.2.1
                    have p1317_2 := h1317c.2.2.1
                    have p1317_3 := h1317c.2.2.2
                    linarith only [h0, hlam, p1317_0]
                  · have p1317_0 := h1317c.1
                    have p1317_1 := h1317c.2.1
                    have p1317_2 := h1317c.2.2.1
                    have p1317_3 := h1317c.2.2.2
                    linarith only [hlam, p1317_0]
                  · have p1317_0 := h1317c.1
                    have p1317_1 := h1317c.2.1
                    have p1317_2 := h1317c.2.2.1
                    have p1317_3 := h1317c.2.2.2
                    linarith only [h10, h1190, h1311, h1315, h7, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1317_1]
                  · have p1317_0 := h1317c.1
                    have p1317_1 := h1317c.2.1
                    have p1317_2 := h1317c.2.2.1
                    have p1317_3 := h1317c.2.2.2
                    linarith only [h0, h10, h1190, h1315, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1317_1]
                  · have p1317_0 := h1317c.1
                    have p1317_1 := h1317c.2.1
                    have p1317_2 := h1317c.2.2.1
                    have p1317_3 := h1317c.2.2.2
                    linarith only [h0, h10, h1190, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1317_1]
                  · have p1317_0 := h1317c.1
                    have p1317_1 := h1317c.2.1
                    have p1317_2 := h1317c.2.2.1
                    have p1317_3 := h1317c.2.2.2
                    linarith only [h1, hlam, p1317_1]
                  · have p1317_0 := h1317c.1
                    have p1317_1 := h1317c.2.1
                    have p1317_2 := h1317c.2.2.1
                    have p1317_3 := h1317c.2.2.2
                    linarith only [h4, hlam, p1317_1]
                  · have p1317_0 := h1317c.1
                    have p1317_1 := h1317c.2.1
                    have p1317_2 := h1317c.2.2.1
                    have p1317_3 := h1317c.2.2.2
                    linarith only [hlam, p1317_0]
                  · have p1317_0 := h1317c.1
                    have p1317_1 := h1317c.2.1
                    have p1317_2 := h1317c.2.2.1
                    have p1317_3 := h1317c.2.2.2
                    linarith only [h10, h1190, h1315, h5, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1317_1]
                  · have p1317_0 := h1317c.1
                    have p1317_1 := h1317c.2.1
                    have p1317_2 := h1317c.2.2.1
                    have p1317_3 := h1317c.2.2.2
                    linarith only [h0, h10, h1190, h4, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1317_1]
                  · have p1317_0 := h1317c.1
                    have p1317_1 := h1317c.2.1
                    have p1317_2 := h1317c.2.2.1
                    have p1317_3 := h1317c.2.2.2
                    linarith only [h2, hlam, p1317_0]
                  · have p1317_0 := h1317c.1
                    have p1317_1 := h1317c.2.1
                    have p1317_2 := h1317c.2.2.1
                    have p1317_3 := h1317c.2.2.2
                    linarith only [h5, hlam, p1317_0]
                  · have p1317_0 := h1317c.1
                    have p1317_1 := h1317c.2.1
                    have p1317_2 := h1317c.2.2.1
                    have p1317_3 := h1317c.2.2.2
                    linarith only [h7, hlam, p1317_0]
                  · have p1317_0 := h1317c.1
                    have p1317_1 := h1317c.2.1
                    have p1317_2 := h1317c.2.2.1
                    have p1317_3 := h1317c.2.2.2
                    linarith only [hlam, p1317_0]
                  · have p1317_0 := h1317c.1
                    have p1317_1 := h1317c.2.1
                    have p1317_2 := h1317c.2.2.1
                    have p1317_3 := h1317c.2.2.2
                    linarith only [h10, h1190, h6, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1317_1]
                  · have p1317_0 := h1317c.1
                    have p1317_1 := h1317c.2.1
                    have p1317_2 := h1317c.2.2.1
                    have p1317_3 := h1317c.2.2.2
                    linarith only [h3, hlam, p1317_0]
                  · have p1317_0 := h1317c.1
                    have p1317_1 := h1317c.2.1
                    have p1317_2 := h1317c.2.2.1
                    have p1317_3 := h1317c.2.2.2
                    linarith only [h6, hlam, p1317_1]
                  · have p1317_0 := h1317c.1
                    have p1317_1 := h1317c.2.1
                    have p1317_2 := h1317c.2.2.1
                    have p1317_3 := h1317c.2.2.2
                    linarith only [h8, hlam, p1317_0]
                  · have p1317_0 := h1317c.1
                    have p1317_1 := h1317c.2.1
                    have p1317_2 := h1317c.2.2.1
                    have p1317_3 := h1317c.2.2.2
                    linarith only [h9, hlam, p1317_1]
                  · have p1317_0 := h1317c.1
                    have p1317_1 := h1317c.2.1
                    have p1317_2 := h1317c.2.2.1
                    have p1317_3 := h1317c.2.2.2
                    linarith only [hlam, p1317_0]
                · linarith only [h10, h1190, h1311, h1315, h1316, hc23, hc45, hlam, hphi, ht34]
              · linarith only [h10, h11, h1310, h1315, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h1345 | h1345
          · linarith only [h0, h10, h1190, h1345, h6, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h1347 | h1347
            · linarith only [h0, h10, h11, h1310, h1347, h4, h7, h9, hc01, hc35, hlam, hphi, ht0b, ht5b]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h1349 | h1349
              · linarith only [h10, h11, h1310, h1345, h1349, hc23, hc34, hlam, hphi]
              · linarith only [h0, h10, h11, h1349, h4, h7, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]

set_option maxHeartbeats 5020000 in
theorem r1l7_10_12_23_L_I_L_I_H_I_s9_x0 (m : N7Model)
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
  · exact r1l7_10_12_23_L_I_L_I_H_I_s9_x0_x0 m hb0 hb2 hb3 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 h10 h11
  · exact r1l7_10_12_23_L_I_L_I_H_I_s9_x0_x1 m hb0 hb2 hb3 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 h10 h11

set_option maxHeartbeats 5020000 in
theorem r1l7_10_12_23_L_I_L_I_H_I_s9_x1_x0 (m : N7Model)
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
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg9 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h10 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h1352 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
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
  rcases m.htr 1 2 5 (by decide) (by decide) with h1353 | h1353
  · rcases m.htr 1 3 4 (by decide) (by decide) with h1354 | h1354
    · rcases m.htr 1 3 5 (by decide) (by decide) with h1355 | h1355
      · rcases m.htr 1 4 5 (by decide) (by decide) with h1356 | h1356
        · rcases m.htr 2 3 4 (by decide) (by decide) with h1357 | h1357
          · rcases m.htr 2 3 5 (by decide) (by decide) with h1358 | h1358
            · rcases m.htr 2 4 5 (by decide) (by decide) with h1359 | h1359
              · linarith only [h0, h10, h1352, h1359, h4, hc01, hc45, hlam, hphi, ht0b, ht5b]
              · linarith only [h0, h10, h1352, h1356, h1359, h4, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
            · linarith only [h0, h10, h1353, h1358, h4, h8, hc01, hc25, hlam, hphi, ht0b, ht5b]
          · linarith only [h0, h10, h1352, h1357, h4, h7, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h1364 | h1364
          · rcases m.htr 2 3 5 (by decide) (by decide) with h1365 | h1365
            · rcases m.htr 2 4 5 (by decide) (by decide) with h1366 | h1366
              · linarith only [h10, h1352, h1356, h1366, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h1368 | h1368
                · linarith only [h1352, h1356, h1364, h1368, hlam]
                · rcases h0bigk with h1370c | h1370c | h1370c | h1370c | h1370c | h1370c | h1370c | h1370c | h1370c | h1370c | h1370c | h1370c | h1370c | h1370c | h1370c | h1370c | h1370c | h1370c | h1370c | h1370c | h1370c | h1370c | h1370c | h1370c | h1370c
                  · have p1370_0 := h1370c.1
                    have p1370_1 := h1370c.2.1
                    have p1370_2 := h1370c.2.2.1
                    have p1370_3 := h1370c.2.2.2
                    linarith only [hlam, p1370_0]
                  · have p1370_0 := h1370c.1
                    have p1370_1 := h1370c.2.1
                    have p1370_2 := h1370c.2.2.1
                    have p1370_3 := h1370c.2.2.2
                    linarith only [h10, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1370_1]
                  · have p1370_0 := h1370c.1
                    have p1370_1 := h1370c.2.1
                    have p1370_2 := h1370c.2.2.1
                    have p1370_3 := h1370c.2.2.2
                    linarith only [h10, h1353, h1365, h4, hc01, hc35, hlam, hphi, ht0b, ht5b, p1370_1]
                  · have p1370_0 := h1370c.1
                    have p1370_1 := h1370c.2.1
                    have p1370_2 := h1370c.2.2.1
                    have p1370_3 := h1370c.2.2.2
                    linarith only [h1352, h1356, h1364, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1370_1]
                  · have p1370_0 := h1370c.1
                    have p1370_1 := h1370c.2.1
                    have p1370_2 := h1370c.2.2.1
                    have p1370_3 := h1370c.2.2.2
                    rcases p1370_3 (m.d 0 1) (by simp) with h1375 | h1375
                    · rcases p1370_3 (m.d 0 2) (by simp) with h1376 | h1376
                      · linarith only [h0, h1376, hlam]
                      · linarith only [h1376, h6, hlam]
                    · linarith only [h1375, h3, hlam]
                  · have p1370_0 := h1370c.1
                    have p1370_1 := h1370c.2.1
                    have p1370_2 := h1370c.2.2.1
                    have p1370_3 := h1370c.2.2.2
                    linarith only [h0, hlam, p1370_0]
                  · have p1370_0 := h1370c.1
                    have p1370_1 := h1370c.2.1
                    have p1370_2 := h1370c.2.2.1
                    have p1370_3 := h1370c.2.2.2
                    linarith only [hlam, p1370_0]
                  · have p1370_0 := h1370c.1
                    have p1370_1 := h1370c.2.1
                    have p1370_2 := h1370c.2.2.1
                    have p1370_3 := h1370c.2.2.2
                    linarith only [h1352, h1356, h1364, h7, h9, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p1370_1]
                  · have p1370_0 := h1370c.1
                    have p1370_1 := h1370c.2.1
                    have p1370_2 := h1370c.2.2.1
                    have p1370_3 := h1370c.2.2.2
                    linarith only [h0, h1352, h1356, h1364, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1370_1]
                  · have p1370_0 := h1370c.1
                    have p1370_1 := h1370c.2.1
                    have p1370_2 := h1370c.2.2.1
                    have p1370_3 := h1370c.2.2.2
                    rcases p1370_3 (m.d 0 1) (by simp) with h1384 | h1384
                    · rcases p1370_3 (m.d 0 2) (by simp) with h1385 | h1385
                      · rcases p1370_3 (m.d 0 3) (by simp) with h1386 | h1386
                        · linarith only [h1386, h4, hlam]
                        · linarith only [h1386, h8, hlam]
                      · linarith only [h1385, h6, hlam]
                    · linarith only [h1384, h3, hlam]
                  · have p1370_0 := h1370c.1
                    have p1370_1 := h1370c.2.1
                    have p1370_2 := h1370c.2.2.1
                    have p1370_3 := h1370c.2.2.2
                    linarith only [h1, hlam, p1370_1]
                  · have p1370_0 := h1370c.1
                    have p1370_1 := h1370c.2.1
                    have p1370_2 := h1370c.2.2.1
                    have p1370_3 := h1370c.2.2.2
                    linarith only [h4, hlam, p1370_1]
                  · have p1370_0 := h1370c.1
                    have p1370_1 := h1370c.2.1
                    have p1370_2 := h1370c.2.2.1
                    have p1370_3 := h1370c.2.2.2
                    linarith only [hlam, p1370_0]
                  · have p1370_0 := h1370c.1
                    have p1370_1 := h1370c.2.1
                    have p1370_2 := h1370c.2.2.1
                    have p1370_3 := h1370c.2.2.2
                    linarith only [h1352, h1356, h1364, h9, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p1370_1]
                  · have p1370_0 := h1370c.1
                    have p1370_1 := h1370c.2.1
                    have p1370_2 := h1370c.2.2.1
                    have p1370_3 := h1370c.2.2.2
                    rcases p1370_3 (m.d 0 1) (by simp) with h1395 | h1395
                    · rcases p1370_3 (m.d 0 2) (by simp) with h1396 | h1396
                      · rcases p1370_3 (m.d 0 3) (by simp) with h1397 | h1397
                        · rcases p1370_3 (m.d 0 4) (by simp) with h1398 | h1398
                          · linarith only [h1398, h7, hlam]
                          · linarith only [h1398, h9, hlam]
                        · linarith only [h1397, h8, hlam]
                      · linarith only [h1396, h6, hlam]
                    · linarith only [h1395, h3, hlam]
                  · have p1370_0 := h1370c.1
                    have p1370_1 := h1370c.2.1
                    have p1370_2 := h1370c.2.2.1
                    have p1370_3 := h1370c.2.2.2
                    linarith only [h2, hlam, p1370_0]
                  · have p1370_0 := h1370c.1
                    have p1370_1 := h1370c.2.1
                    have p1370_2 := h1370c.2.2.1
                    have p1370_3 := h1370c.2.2.2
                    linarith only [h5, hlam, p1370_0]
                  · have p1370_0 := h1370c.1
                    have p1370_1 := h1370c.2.1
                    have p1370_2 := h1370c.2.2.1
                    have p1370_3 := h1370c.2.2.2
                    linarith only [h7, hlam, p1370_0]
                  · have p1370_0 := h1370c.1
                    have p1370_1 := h1370c.2.1
                    have p1370_2 := h1370c.2.2.1
                    have p1370_3 := h1370c.2.2.2
                    linarith only [hlam, p1370_0]
                  · have p1370_0 := h1370c.1
                    have p1370_1 := h1370c.2.1
                    have p1370_2 := h1370c.2.2.1
                    have p1370_3 := h1370c.2.2.2
                    rcases p1370_3 (m.d 0 1) (by simp) with h1408 | h1408
                    · rcases p1370_3 (m.d 0 2) (by simp) with h1409 | h1409
                      · rcases p1370_3 (m.d 0 3) (by simp) with h1410 | h1410
                        · rcases p1370_3 (m.d 0 4) (by simp) with h1411 | h1411
                          · rcases p1370_3 (m.d 0 5) (by simp) with h1412 | h1412
                            · linarith only [h1412, h9, hlam]
                            · rcases h2bigk with h1414c | h1414c | h1414c | h1414c | h1414c | h1414c | h1414c | h1414c | h1414c | h1414c | h1414c | h1414c | h1414c | h1414c | h1414c | h1414c | h1414c | h1414c | h1414c | h1414c | h1414c | h1414c | h1414c | h1414c | h1414c
                              · have p1414_0 := h1414c.1
                                have p1414_1 := h1414c.2.1
                                have p1414_2 := h1414c.2.2.1
                                have p1414_3 := h1414c.2.2.2
                                linarith only [hlam, p1414_0]
                              · have p1414_0 := h1414c.1
                                have p1414_1 := h1414c.2.1
                                have p1414_2 := h1414c.2.2.1
                                have p1414_3 := h1414c.2.2.2
                                rcases p1414_3 (m.d 0 2) (by simp) with h1416 | h1416
                                · rcases p1414_3 (m.d 1 2) (by simp) with h1417 | h1417
                                  · linarith only [h0, h1417, hlam]
                                  · rcases p1414_3 (m.d 2 3) (by simp) with h1419 | h1419
                                    · linarith only [h1419, h4, hlam]
                                    · linarith only [h10, h1419, hlam]
                                · linarith only [h0, h1416, hlam]
                              · have p1414_0 := h1414c.1
                                have p1414_1 := h1414c.2.1
                                have p1414_2 := h1414c.2.2.1
                                have p1414_3 := h1414c.2.2.2
                                linarith only [h0, h10, h1353, h1364, h1366, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1414_1]
                              · have p1414_0 := h1414c.1
                                have p1414_1 := h1414c.2.1
                                have p1414_2 := h1414c.2.2.1
                                have p1414_3 := h1414c.2.2.2
                                linarith only [h10, h1353, h1366, h4, hlam, p1414_2]
                              · have p1414_0 := h1414c.1
                                have p1414_1 := h1414c.2.1
                                have p1414_2 := h1414c.2.2.1
                                have p1414_3 := h1414c.2.2.2
                                linarith only [h10, h1353, h4, hlam, p1414_2]
                              · have p1414_0 := h1414c.1
                                have p1414_1 := h1414c.2.1
                                have p1414_2 := h1414c.2.2.1
                                have p1414_3 := h1414c.2.2.2
                                linarith only [h0, hlam, p1414_0]
                              · have p1414_0 := h1414c.1
                                have p1414_1 := h1414c.2.1
                                have p1414_2 := h1414c.2.2.1
                                have p1414_3 := h1414c.2.2.2
                                linarith only [hlam, p1414_0]
                              · have p1414_0 := h1414c.1
                                have p1414_1 := h1414c.2.1
                                have p1414_2 := h1414c.2.2.1
                                have p1414_3 := h1414c.2.2.2
                                linarith only [h10, hlam, p1414_0]
                              · have p1414_0 := h1414c.1
                                have p1414_1 := h1414c.2.1
                                have p1414_2 := h1414c.2.2.1
                                have p1414_3 := h1414c.2.2.2
                                linarith only [h10, h1364, h4, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p1414_1]
                              · have p1414_0 := h1414c.1
                                have p1414_1 := h1414c.2.1
                                have p1414_2 := h1414c.2.2.1
                                have p1414_3 := h1414c.2.2.2
                                linarith only [h10, h4, hc02, hc25, hlam, hphi, ht0b, ht5b, p1414_1]
                              · have p1414_0 := h1414c.1
                                have p1414_1 := h1414c.2.1
                                have p1414_2 := h1414c.2.2.1
                                have p1414_3 := h1414c.2.2.2
                                linarith only [h4, hlam, p1414_0]
                              · have p1414_0 := h1414c.1
                                have p1414_1 := h1414c.2.1
                                have p1414_2 := h1414c.2.2.1
                                have p1414_3 := h1414c.2.2.2
                                linarith only [h0, h1352, h1364, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1414_1]
                              · have p1414_0 := h1414c.1
                                have p1414_1 := h1414c.2.1
                                have p1414_2 := h1414c.2.2.1
                                have p1414_3 := h1414c.2.2.2
                                linarith only [hlam, p1414_0]
                              · have p1414_0 := h1414c.1
                                have p1414_1 := h1414c.2.1
                                have p1414_2 := h1414c.2.2.1
                                have p1414_3 := h1414c.2.2.2
                                rcases p1414_3 (m.d 0 2) (by simp) with h1434 | h1434
                                · rcases p1414_3 (m.d 1 2) (by simp) with h1435 | h1435
                                  · linarith only [h10, h1435, hlam]
                                  · linarith only [h1352, h1435, hlam]
                                · linarith only [h1434, h5, hlam]
                              · have p1414_0 := h1414c.1
                                have p1414_1 := h1414c.2.1
                                have p1414_2 := h1414c.2.2.1
                                have p1414_3 := h1414c.2.2.2
                                rcases p1414_3 (m.d 0 2) (by simp) with h1439 | h1439
                                · rcases p1414_3 (m.d 1 2) (by simp) with h1440 | h1440
                                  · linarith only [h10, h1440, hlam]
                                  · linarith only [h1353, h1440, hlam]
                                · linarith only [h1439, h6, hlam]
                              · have p1414_0 := h1414c.1
                                have p1414_1 := h1414c.2.1
                                have p1414_2 := h1414c.2.2.1
                                have p1414_3 := h1414c.2.2.2
                                linarith only [h5, hlam, p1414_0]
                              · have p1414_0 := h1414c.1
                                have p1414_1 := h1414c.2.1
                                have p1414_2 := h1414c.2.2.1
                                have p1414_3 := h1414c.2.2.2
                                linarith only [h1352, hlam, p1414_0]
                              · have p1414_0 := h1414c.1
                                have p1414_1 := h1414c.2.1
                                have p1414_2 := h1414c.2.2.1
                                have p1414_3 := h1414c.2.2.2
                                linarith only [h1364, hlam, p1414_1]
                              · have p1414_0 := h1414c.1
                                have p1414_1 := h1414c.2.1
                                have p1414_2 := h1414c.2.2.1
                                have p1414_3 := h1414c.2.2.2
                                linarith only [hlam, p1414_0]
                              · have p1414_0 := h1414c.1
                                have p1414_1 := h1414c.2.1
                                have p1414_2 := h1414c.2.2.1
                                have p1414_3 := h1414c.2.2.2
                                linarith only [h1366, hlam, p1414_1]
                              · have p1414_0 := h1414c.1
                                have p1414_1 := h1414c.2.1
                                have p1414_2 := h1414c.2.2.1
                                have p1414_3 := h1414c.2.2.2
                                linarith only [h6, hlam, p1414_0]
                              · have p1414_0 := h1414c.1
                                have p1414_1 := h1414c.2.1
                                have p1414_2 := h1414c.2.2.1
                                have p1414_3 := h1414c.2.2.2
                                linarith only [h1353, hlam, p1414_0]
                              · have p1414_0 := h1414c.1
                                have p1414_1 := h1414c.2.1
                                have p1414_2 := h1414c.2.2.1
                                have p1414_3 := h1414c.2.2.2
                                linarith only [h1365, hlam, p1414_1]
                              · have p1414_0 := h1414c.1
                                have p1414_1 := h1414c.2.1
                                have p1414_2 := h1414c.2.2.1
                                have p1414_3 := h1414c.2.2.2
                                linarith only [h0, h1353, h1364, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1414_1]
                              · have p1414_0 := h1414c.1
                                have p1414_1 := h1414c.2.1
                                have p1414_2 := h1414c.2.2.1
                                have p1414_3 := h1414c.2.2.2
                                linarith only [hlam, p1414_0]
                          · linarith only [h1411, h9, hlam]
                        · linarith only [h1410, h8, hlam]
                      · linarith only [h1409, h6, hlam]
                    · linarith only [h1408, h3, hlam]
                  · have p1370_0 := h1370c.1
                    have p1370_1 := h1370c.2.1
                    have p1370_2 := h1370c.2.2.1
                    have p1370_3 := h1370c.2.2.2
                    linarith only [h3, hlam, p1370_0]
                  · have p1370_0 := h1370c.1
                    have p1370_1 := h1370c.2.1
                    have p1370_2 := h1370c.2.2.1
                    have p1370_3 := h1370c.2.2.2
                    linarith only [h6, hlam, p1370_1]
                  · have p1370_0 := h1370c.1
                    have p1370_1 := h1370c.2.1
                    have p1370_2 := h1370c.2.2.1
                    have p1370_3 := h1370c.2.2.2
                    linarith only [h8, hlam, p1370_0]
                  · have p1370_0 := h1370c.1
                    have p1370_1 := h1370c.2.1
                    have p1370_2 := h1370c.2.2.1
                    have p1370_3 := h1370c.2.2.2
                    linarith only [h9, hlam, p1370_1]
                  · have p1370_0 := h1370c.1
                    have p1370_1 := h1370c.2.1
                    have p1370_2 := h1370c.2.2.1
                    have p1370_3 := h1370c.2.2.2
                    linarith only [hlam, p1370_0]
            · linarith only [h0, h10, h1352, h1364, h1365, h4, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
          · linarith only [h0, h10, h1352, h1364, h4, h7, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
      · linarith only [h10, h1353, h1355, hlam]
    · linarith only [h10, h1352, h1354, hlam]
  · rcases m.htr 1 3 4 (by decide) (by decide) with h1467 | h1467
    · rcases m.htr 1 3 5 (by decide) (by decide) with h1468 | h1468
      · rcases m.htr 1 4 5 (by decide) (by decide) with h1469 | h1469
        · linarith only [h1352, h1353, h1469, hlam]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h1471 | h1471
          · rcases m.htr 2 3 5 (by decide) (by decide) with h1472 | h1472
            · rcases m.htr 2 4 5 (by decide) (by decide) with h1473 | h1473
              · linarith only [h1352, h1353, h1469, h1472, h1473, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h1475 | h1475
                · linarith only [h1352, h1353, h1471, h1473, h1475, hlam]
                · rcases h0bigk with h1477c | h1477c | h1477c | h1477c | h1477c | h1477c | h1477c | h1477c | h1477c | h1477c | h1477c | h1477c | h1477c | h1477c | h1477c | h1477c | h1477c | h1477c | h1477c | h1477c | h1477c | h1477c | h1477c | h1477c | h1477c
                  · have p1477_0 := h1477c.1
                    have p1477_1 := h1477c.2.1
                    have p1477_2 := h1477c.2.2.1
                    have p1477_3 := h1477c.2.2.2
                    linarith only [hlam, p1477_0]
                  · have p1477_0 := h1477c.1
                    have p1477_1 := h1477c.2.1
                    have p1477_2 := h1477c.2.2.1
                    have p1477_3 := h1477c.2.2.2
                    linarith only [h1353, h1473, h4, h7, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1477_1]
                  · have p1477_0 := h1477c.1
                    have p1477_1 := h1477c.2.1
                    have p1477_2 := h1477c.2.2.1
                    have p1477_3 := h1477c.2.2.2
                    linarith only [h1352, h1353, h1471, h1473, h7, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1477_1]
                  · have p1477_0 := h1477c.1
                    have p1477_1 := h1477c.2.1
                    have p1477_2 := h1477c.2.2.1
                    have p1477_3 := h1477c.2.2.2
                    linarith only [h1352, h1353, h1471, h1473, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1477_1]
                  · have p1477_0 := h1477c.1
                    have p1477_1 := h1477c.2.1
                    have p1477_2 := h1477c.2.2.1
                    have p1477_3 := h1477c.2.2.2
                    linarith only [h1352, h1353, h1471, h1473, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1477_1]
                  · have p1477_0 := h1477c.1
                    have p1477_1 := h1477c.2.1
                    have p1477_2 := h1477c.2.2.1
                    have p1477_3 := h1477c.2.2.2
                    linarith only [h0, hlam, p1477_0]
                  · have p1477_0 := h1477c.1
                    have p1477_1 := h1477c.2.1
                    have p1477_2 := h1477c.2.2.1
                    have p1477_3 := h1477c.2.2.2
                    linarith only [hlam, p1477_0]
                  · have p1477_0 := h1477c.1
                    have p1477_1 := h1477c.2.1
                    have p1477_2 := h1477c.2.2.1
                    have p1477_3 := h1477c.2.2.2
                    linarith only [h1352, h1353, h1471, h1473, h7, h9, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p1477_1]
                  · have p1477_0 := h1477c.1
                    have p1477_1 := h1477c.2.1
                    have p1477_2 := h1477c.2.2.1
                    have p1477_3 := h1477c.2.2.2
                    linarith only [h0, h1352, h1353, h1471, h1473, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1477_1]
                  · have p1477_0 := h1477c.1
                    have p1477_1 := h1477c.2.1
                    have p1477_2 := h1477c.2.2.1
                    have p1477_3 := h1477c.2.2.2
                    linarith only [h0, h1352, h1353, h1471, h1473, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1477_1]
                  · have p1477_0 := h1477c.1
                    have p1477_1 := h1477c.2.1
                    have p1477_2 := h1477c.2.2.1
                    have p1477_3 := h1477c.2.2.2
                    linarith only [h1, hlam, p1477_1]
                  · have p1477_0 := h1477c.1
                    have p1477_1 := h1477c.2.1
                    have p1477_2 := h1477c.2.2.1
                    have p1477_3 := h1477c.2.2.2
                    linarith only [h4, hlam, p1477_1]
                  · have p1477_0 := h1477c.1
                    have p1477_1 := h1477c.2.1
                    have p1477_2 := h1477c.2.2.1
                    have p1477_3 := h1477c.2.2.2
                    linarith only [hlam, p1477_0]
                  · have p1477_0 := h1477c.1
                    have p1477_1 := h1477c.2.1
                    have p1477_2 := h1477c.2.2.1
                    have p1477_3 := h1477c.2.2.2
                    linarith only [h1352, h1353, h1471, h1473, h9, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p1477_1]
                  · have p1477_0 := h1477c.1
                    have p1477_1 := h1477c.2.1
                    have p1477_2 := h1477c.2.2.1
                    have p1477_3 := h1477c.2.2.2
                    linarith only [h0, h1352, h1353, h1471, h1473, h4, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1477_1]
                  · have p1477_0 := h1477c.1
                    have p1477_1 := h1477c.2.1
                    have p1477_2 := h1477c.2.2.1
                    have p1477_3 := h1477c.2.2.2
                    linarith only [h2, hlam, p1477_0]
                  · have p1477_0 := h1477c.1
                    have p1477_1 := h1477c.2.1
                    have p1477_2 := h1477c.2.2.1
                    have p1477_3 := h1477c.2.2.2
                    linarith only [h5, hlam, p1477_0]
                  · have p1477_0 := h1477c.1
                    have p1477_1 := h1477c.2.1
                    have p1477_2 := h1477c.2.2.1
                    have p1477_3 := h1477c.2.2.2
                    linarith only [h7, hlam, p1477_0]
                  · have p1477_0 := h1477c.1
                    have p1477_1 := h1477c.2.1
                    have p1477_2 := h1477c.2.2.1
                    have p1477_3 := h1477c.2.2.2
                    linarith only [hlam, p1477_0]
                  · have p1477_0 := h1477c.1
                    have p1477_1 := h1477c.2.1
                    have p1477_2 := h1477c.2.2.1
                    have p1477_3 := h1477c.2.2.2
                    linarith only [h1352, h1353, h1471, h1473, h9, hc04, hc34, hlam, hphi, ht0b, ht45, ht5b, p1477_1]
                  · have p1477_0 := h1477c.1
                    have p1477_1 := h1477c.2.1
                    have p1477_2 := h1477c.2.2.1
                    have p1477_3 := h1477c.2.2.2
                    linarith only [h3, hlam, p1477_0]
                  · have p1477_0 := h1477c.1
                    have p1477_1 := h1477c.2.1
                    have p1477_2 := h1477c.2.2.1
                    have p1477_3 := h1477c.2.2.2
                    linarith only [h6, hlam, p1477_1]
                  · have p1477_0 := h1477c.1
                    have p1477_1 := h1477c.2.1
                    have p1477_2 := h1477c.2.2.1
                    have p1477_3 := h1477c.2.2.2
                    linarith only [h8, hlam, p1477_0]
                  · have p1477_0 := h1477c.1
                    have p1477_1 := h1477c.2.1
                    have p1477_2 := h1477c.2.2.1
                    have p1477_3 := h1477c.2.2.2
                    linarith only [h9, hlam, p1477_1]
                  · have p1477_0 := h1477c.1
                    have p1477_1 := h1477c.2.1
                    have p1477_2 := h1477c.2.2.1
                    have p1477_3 := h1477c.2.2.2
                    linarith only [hlam, p1477_0]
            · linarith only [h0, h10, h1352, h1471, h1472, h4, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
          · linarith only [h0, h10, h1352, h1471, h4, h7, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
      · rcases m.htr 1 4 5 (by decide) (by decide) with h1505 | h1505
        · linarith only [h10, h1352, h1468, h1505, hlam]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h1507 | h1507
          · rcases m.htr 2 3 5 (by decide) (by decide) with h1508 | h1508
            · linarith only [h0, h10, h1352, h1468, h1508, h4, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
            · linarith only [h0, h10, h1352, h1507, h1508, h4, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
          · linarith only [h0, h10, h1352, h1507, h4, h7, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
    · linarith only [h10, h1352, h1467, hlam]

set_option maxHeartbeats 5020000 in
theorem r1l7_10_12_23_L_I_L_I_H_I_s9_x1_x1_x0 (m : N7Model)
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
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg9 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h10 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h1352 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (h1513 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
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
  rcases m.htr 1 3 4 (by decide) (by decide) with h1514 | h1514
  · rcases m.htr 1 3 5 (by decide) (by decide) with h1515 | h1515
    · rcases m.htr 1 4 5 (by decide) (by decide) with h1516 | h1516
      · rcases m.htr 2 3 4 (by decide) (by decide) with h1517 | h1517
        · rcases m.htr 2 3 5 (by decide) (by decide) with h1518 | h1518
          · rcases m.htr 2 4 5 (by decide) (by decide) with h1519 | h1519
            · rcases m.htr 3 4 5 (by decide) (by decide) with h1520 | h1520
              · rcases h0bigk with h1521c | h1521c | h1521c | h1521c | h1521c | h1521c | h1521c | h1521c | h1521c | h1521c | h1521c | h1521c | h1521c | h1521c | h1521c | h1521c | h1521c | h1521c | h1521c | h1521c | h1521c | h1521c | h1521c | h1521c | h1521c
                · have p1521_0 := h1521c.1
                  have p1521_1 := h1521c.2.1
                  have p1521_2 := h1521c.2.2.1
                  have p1521_3 := h1521c.2.2.2
                  linarith only [hlam, p1521_0]
                · have p1521_0 := h1521c.1
                  have p1521_1 := h1521c.2.1
                  have p1521_2 := h1521c.2.2.1
                  have p1521_3 := h1521c.2.2.2
                  linarith only [h1352, h1513, h1518, h1520, h5, hc01, hc45, hlam, hphi, ht0b, ht5b, p1521_1]
                · have p1521_0 := h1521c.1
                  have p1521_1 := h1521c.2.1
                  have p1521_2 := h1521c.2.2.1
                  have p1521_3 := h1521c.2.2.2
                  linarith only [h1352, h1513, h1518, h1520, h5, h7, hc01, hc45, hlam, hphi, ht0b, ht5b, p1521_1]
                · have p1521_0 := h1521c.1
                  have p1521_1 := h1521c.2.1
                  have p1521_2 := h1521c.2.2.1
                  have p1521_3 := h1521c.2.2.2
                  linarith only [h1352, h1513, h1518, h1520, h5, hc01, hc45, hlam, hphi, ht0b, ht5b, p1521_1]
                · have p1521_0 := h1521c.1
                  have p1521_1 := h1521c.2.1
                  have p1521_2 := h1521c.2.2.1
                  have p1521_3 := h1521c.2.2.2
                  rcases p1521_3 (m.d 0 1) (by simp) with h1526 | h1526
                  · rcases p1521_3 (m.d 0 2) (by simp) with h1527 | h1527
                    · linarith only [h0, h1527, hlam]
                    · linarith only [h1527, h6, hlam]
                  · linarith only [h1526, h3, hlam]
                · have p1521_0 := h1521c.1
                  have p1521_1 := h1521c.2.1
                  have p1521_2 := h1521c.2.2.1
                  have p1521_3 := h1521c.2.2.2
                  linarith only [h0, hlam, p1521_0]
                · have p1521_0 := h1521c.1
                  have p1521_1 := h1521c.2.1
                  have p1521_2 := h1521c.2.2.1
                  have p1521_3 := h1521c.2.2.2
                  linarith only [hlam, p1521_0]
                · have p1521_0 := h1521c.1
                  have p1521_1 := h1521c.2.1
                  have p1521_2 := h1521c.2.2.1
                  have p1521_3 := h1521c.2.2.2
                  linarith only [h1352, h1513, h1518, h1520, h5, h7, hc02, hc45, hlam, hphi, ht0b, ht5b, p1521_1]
                · have p1521_0 := h1521c.1
                  have p1521_1 := h1521c.2.1
                  have p1521_2 := h1521c.2.2.1
                  have p1521_3 := h1521c.2.2.2
                  linarith only [h0, h1352, h1513, h1518, h1520, h5, hc01, hc45, hlam, hphi, ht0b, ht5b, p1521_1]
                · have p1521_0 := h1521c.1
                  have p1521_1 := h1521c.2.1
                  have p1521_2 := h1521c.2.2.1
                  have p1521_3 := h1521c.2.2.2
                  rcases p1521_3 (m.d 0 1) (by simp) with h1535 | h1535
                  · rcases p1521_3 (m.d 0 2) (by simp) with h1536 | h1536
                    · rcases p1521_3 (m.d 0 3) (by simp) with h1537 | h1537
                      · linarith only [h1537, h4, hlam]
                      · linarith only [h1537, h8, hlam]
                    · linarith only [h1536, h6, hlam]
                  · linarith only [h1535, h3, hlam]
                · have p1521_0 := h1521c.1
                  have p1521_1 := h1521c.2.1
                  have p1521_2 := h1521c.2.2.1
                  have p1521_3 := h1521c.2.2.2
                  linarith only [h1, hlam, p1521_1]
                · have p1521_0 := h1521c.1
                  have p1521_1 := h1521c.2.1
                  have p1521_2 := h1521c.2.2.1
                  have p1521_3 := h1521c.2.2.2
                  linarith only [h4, hlam, p1521_1]
                · have p1521_0 := h1521c.1
                  have p1521_1 := h1521c.2.1
                  have p1521_2 := h1521c.2.2.1
                  have p1521_3 := h1521c.2.2.2
                  linarith only [hlam, p1521_0]
                · have p1521_0 := h1521c.1
                  have p1521_1 := h1521c.2.1
                  have p1521_2 := h1521c.2.2.1
                  have p1521_3 := h1521c.2.2.2
                  linarith only [h1352, h1513, h1518, h1520, h5, hc03, hc45, hlam, hphi, ht0b, ht5b, p1521_1]
                · have p1521_0 := h1521c.1
                  have p1521_1 := h1521c.2.1
                  have p1521_2 := h1521c.2.2.1
                  have p1521_3 := h1521c.2.2.2
                  rcases p1521_3 (m.d 0 1) (by simp) with h1546 | h1546
                  · rcases p1521_3 (m.d 0 2) (by simp) with h1547 | h1547
                    · rcases p1521_3 (m.d 0 3) (by simp) with h1548 | h1548
                      · rcases p1521_3 (m.d 0 4) (by simp) with h1549 | h1549
                        · linarith only [h1549, h7, hlam]
                        · linarith only [h1549, h9, hlam]
                      · linarith only [h1548, h8, hlam]
                    · linarith only [h1547, h6, hlam]
                  · linarith only [h1546, h3, hlam]
                · have p1521_0 := h1521c.1
                  have p1521_1 := h1521c.2.1
                  have p1521_2 := h1521c.2.2.1
                  have p1521_3 := h1521c.2.2.2
                  linarith only [h2, hlam, p1521_0]
                · have p1521_0 := h1521c.1
                  have p1521_1 := h1521c.2.1
                  have p1521_2 := h1521c.2.2.1
                  have p1521_3 := h1521c.2.2.2
                  linarith only [h5, hlam, p1521_0]
                · have p1521_0 := h1521c.1
                  have p1521_1 := h1521c.2.1
                  have p1521_2 := h1521c.2.2.1
                  have p1521_3 := h1521c.2.2.2
                  linarith only [h7, hlam, p1521_0]
                · have p1521_0 := h1521c.1
                  have p1521_1 := h1521c.2.1
                  have p1521_2 := h1521c.2.2.1
                  have p1521_3 := h1521c.2.2.2
                  linarith only [hlam, p1521_0]
                · have p1521_0 := h1521c.1
                  have p1521_1 := h1521c.2.1
                  have p1521_2 := h1521c.2.2.1
                  have p1521_3 := h1521c.2.2.2
                  rcases p1521_3 (m.d 0 1) (by simp) with h1559 | h1559
                  · rcases p1521_3 (m.d 0 2) (by simp) with h1560 | h1560
                    · rcases p1521_3 (m.d 0 3) (by simp) with h1561 | h1561
                      · rcases p1521_3 (m.d 0 4) (by simp) with h1562 | h1562
                        · rcases p1521_3 (m.d 0 5) (by simp) with h1563 | h1563
                          · linarith only [h1563, h9, hlam]
                          · rcases h2bigk with h1565c | h1565c | h1565c | h1565c | h1565c | h1565c | h1565c | h1565c | h1565c | h1565c | h1565c | h1565c | h1565c | h1565c | h1565c | h1565c | h1565c | h1565c | h1565c | h1565c | h1565c | h1565c | h1565c | h1565c | h1565c
                            · have p1565_0 := h1565c.1
                              have p1565_1 := h1565c.2.1
                              have p1565_2 := h1565c.2.2.1
                              have p1565_3 := h1565c.2.2.2
                              linarith only [hlam, p1565_0]
                            · have p1565_0 := h1565c.1
                              have p1565_1 := h1565c.2.1
                              have p1565_2 := h1565c.2.2.1
                              have p1565_3 := h1565c.2.2.2
                              rcases p1565_3 (m.d 0 2) (by simp) with h1567 | h1567
                              · rcases p1565_3 (m.d 1 2) (by simp) with h1568 | h1568
                                · linarith only [h0, h1568, hlam]
                                · rcases p1565_3 (m.d 2 3) (by simp) with h1570 | h1570
                                  · linarith only [h1570, h4, hlam]
                                  · linarith only [h10, h1570, hlam]
                              · linarith only [h0, h1567, hlam]
                            · have p1565_0 := h1565c.1
                              have p1565_1 := h1565c.2.1
                              have p1565_2 := h1565c.2.2.1
                              have p1565_3 := h1565c.2.2.2
                              linarith only [h0, h1352, h1513, h1517, h1518, h1520, hc01, hc45, hlam, hphi, ht0b, ht5b, p1565_1]
                            · have p1565_0 := h1565c.1
                              have p1565_1 := h1565c.2.1
                              have p1565_2 := h1565c.2.2.1
                              have p1565_3 := h1565c.2.2.2
                              linarith only [h0, h1352, h1513, h1518, h1520, hc01, hc45, hlam, hphi, ht0b, ht5b, p1565_1]
                            · have p1565_0 := h1565c.1
                              have p1565_1 := h1565c.2.1
                              have p1565_2 := h1565c.2.2.1
                              have p1565_3 := h1565c.2.2.2
                              linarith only [h1352, h1513, h1517, h4, hlam, p1565_2]
                            · have p1565_0 := h1565c.1
                              have p1565_1 := h1565c.2.1
                              have p1565_2 := h1565c.2.2.1
                              have p1565_3 := h1565c.2.2.2
                              linarith only [h0, hlam, p1565_0]
                            · have p1565_0 := h1565c.1
                              have p1565_1 := h1565c.2.1
                              have p1565_2 := h1565c.2.2.1
                              have p1565_3 := h1565c.2.2.2
                              linarith only [hlam, p1565_0]
                            · have p1565_0 := h1565c.1
                              have p1565_1 := h1565c.2.1
                              have p1565_2 := h1565c.2.2.1
                              have p1565_3 := h1565c.2.2.2
                              linarith only [h10, hlam, p1565_0]
                            · have p1565_0 := h1565c.1
                              have p1565_1 := h1565c.2.1
                              have p1565_2 := h1565c.2.2.1
                              have p1565_3 := h1565c.2.2.2
                              linarith only [h1352, hlam, p1565_0]
                            · have p1565_0 := h1565c.1
                              have p1565_1 := h1565c.2.1
                              have p1565_2 := h1565c.2.2.1
                              have p1565_3 := h1565c.2.2.2
                              linarith only [h1352, h1517, h1518, h1520, h4, hc02, hc45, hlam, hphi, ht0b, ht5b, p1565_1]
                            · have p1565_0 := h1565c.1
                              have p1565_1 := h1565c.2.1
                              have p1565_2 := h1565c.2.2.1
                              have p1565_3 := h1565c.2.2.2
                              linarith only [h4, hlam, p1565_0]
                            · have p1565_0 := h1565c.1
                              have p1565_1 := h1565c.2.1
                              have p1565_2 := h1565c.2.2.1
                              have p1565_3 := h1565c.2.2.2
                              linarith only [h0, h1513, h1518, h1520, h4, hc01, hc45, hlam, hphi, ht0b, ht5b, p1565_1]
                            · have p1565_0 := h1565c.1
                              have p1565_1 := h1565c.2.1
                              have p1565_2 := h1565c.2.2.1
                              have p1565_3 := h1565c.2.2.2
                              linarith only [hlam, p1565_0]
                            · have p1565_0 := h1565c.1
                              have p1565_1 := h1565c.2.1
                              have p1565_2 := h1565c.2.2.1
                              have p1565_3 := h1565c.2.2.2
                              linarith only [h0, h1352, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1565_1]
                            · have p1565_0 := h1565c.1
                              have p1565_1 := h1565c.2.1
                              have p1565_2 := h1565c.2.2.1
                              have p1565_3 := h1565c.2.2.2
                              rcases p1565_3 (m.d 0 2) (by simp) with h1586 | h1586
                              · rcases p1565_3 (m.d 1 2) (by simp) with h1587 | h1587
                                · linarith only [h10, h1587, hlam]
                                · linarith only [h1513, h1587, hlam]
                              · linarith only [h1586, h6, hlam]
                            · have p1565_0 := h1565c.1
                              have p1565_1 := h1565c.2.1
                              have p1565_2 := h1565c.2.2.1
                              have p1565_3 := h1565c.2.2.2
                              linarith only [h5, hlam, p1565_0]
                            · have p1565_0 := h1565c.1
                              have p1565_1 := h1565c.2.1
                              have p1565_2 := h1565c.2.2.1
                              have p1565_3 := h1565c.2.2.2
                              linarith only [h0, h1513, h1518, h1520, h5, hc01, hc45, hlam, hphi, ht0b, ht5b, p1565_1]
                            · have p1565_0 := h1565c.1
                              have p1565_1 := h1565c.2.1
                              have p1565_2 := h1565c.2.2.1
                              have p1565_3 := h1565c.2.2.2
                              linarith only [h1517, hlam, p1565_1]
                            · have p1565_0 := h1565c.1
                              have p1565_1 := h1565c.2.1
                              have p1565_2 := h1565c.2.2.1
                              have p1565_3 := h1565c.2.2.2
                              linarith only [hlam, p1565_0]
                            · have p1565_0 := h1565c.1
                              have p1565_1 := h1565c.2.1
                              have p1565_2 := h1565c.2.2.1
                              have p1565_3 := h1565c.2.2.2
                              rcases p1565_3 (m.d 0 2) (by simp) with h1595 | h1595
                              · rcases p1565_3 (m.d 1 2) (by simp) with h1596 | h1596
                                · linarith only [h1352, h1596, hlam]
                                · linarith only [h1513, h1596, hlam]
                              · linarith only [h1595, h6, hlam]
                            · have p1565_0 := h1565c.1
                              have p1565_1 := h1565c.2.1
                              have p1565_2 := h1565c.2.2.1
                              have p1565_3 := h1565c.2.2.2
                              linarith only [h6, hlam, p1565_0]
                            · have p1565_0 := h1565c.1
                              have p1565_1 := h1565c.2.1
                              have p1565_2 := h1565c.2.2.1
                              have p1565_3 := h1565c.2.2.2
                              linarith only [h1513, hlam, p1565_0]
                            · have p1565_0 := h1565c.1
                              have p1565_1 := h1565c.2.1
                              have p1565_2 := h1565c.2.2.1
                              have p1565_3 := h1565c.2.2.2
                              linarith only [h1518, hlam, p1565_1]
                            · have p1565_0 := h1565c.1
                              have p1565_1 := h1565c.2.1
                              have p1565_2 := h1565c.2.2.1
                              have p1565_3 := h1565c.2.2.2
                              linarith only [h1519, hlam, p1565_0]
                            · have p1565_0 := h1565c.1
                              have p1565_1 := h1565c.2.1
                              have p1565_2 := h1565c.2.2.1
                              have p1565_3 := h1565c.2.2.2
                              linarith only [hlam, p1565_0]
                        · linarith only [h1562, h9, hlam]
                      · linarith only [h1561, h8, hlam]
                    · linarith only [h1560, h6, hlam]
                  · linarith only [h1559, h3, hlam]
                · have p1521_0 := h1521c.1
                  have p1521_1 := h1521c.2.1
                  have p1521_2 := h1521c.2.2.1
                  have p1521_3 := h1521c.2.2.2
                  linarith only [h3, hlam, p1521_0]
                · have p1521_0 := h1521c.1
                  have p1521_1 := h1521c.2.1
                  have p1521_2 := h1521c.2.2.1
                  have p1521_3 := h1521c.2.2.2
                  linarith only [h6, hlam, p1521_1]
                · have p1521_0 := h1521c.1
                  have p1521_1 := h1521c.2.1
                  have p1521_2 := h1521c.2.2.1
                  have p1521_3 := h1521c.2.2.2
                  linarith only [h8, hlam, p1521_0]
                · have p1521_0 := h1521c.1
                  have p1521_1 := h1521c.2.1
                  have p1521_2 := h1521c.2.2.1
                  have p1521_3 := h1521c.2.2.2
                  linarith only [h9, hlam, p1521_1]
                · have p1521_0 := h1521c.1
                  have p1521_1 := h1521c.2.1
                  have p1521_2 := h1521c.2.2.1
                  have p1521_3 := h1521c.2.2.2
                  linarith only [hlam, p1521_0]
              · linarith only [h0, h1352, h1513, h1517, h1519, h1520, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
            · linarith only [h1352, h1513, h1516, h1519, hc14, hc25, hlam, hphi, ht01, ht0b, ht5b]
          · linarith only [h1352, h1513, h1517, h1518, h4, h8, hc02, hc25, hlam, hphi, ht0b, ht5b]
        · linarith only [h0, h10, h1513, h1517, h4, h7, hc01, hc25, hlam, hphi, ht0b, ht5b]
      · linarith only [h1352, h1513, h1516, hlam]
    · linarith only [h10, h1513, h1515, hlam]
  · rcases m.htr 1 3 5 (by decide) (by decide) with h1620 | h1620
    · rcases m.htr 1 4 5 (by decide) (by decide) with h1621 | h1621
      · rcases m.htr 2 3 4 (by decide) (by decide) with h1622 | h1622
        · linarith only [h0, h1514, h1620, h1622, h4, hc01, hc35, hlam, hphi, ht0b, ht5b]
        · linarith only [h0, h10, h1513, h1622, h4, h7, hc01, hc25, hlam, hphi, ht0b, ht5b]
      · linarith only [h10, h1513, h1514, h1621, hlam]
    · linarith only [h10, h1513, h1620, hlam]

end R2N4
