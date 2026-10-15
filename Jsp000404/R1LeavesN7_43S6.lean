import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_43S5

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6266000 in
set_option maxHeartbeats 6266000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_L_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
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
  have h1bigk := hb1.1
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h1299 | h1299
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1300 | h1300
    · rcases m.htr 0 2 4 (by decide) (by decide) with h1301 | h1301
      · linarith only [h0, h1301, h2, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1303 | h1303
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1304 | h1304
          · linarith only [h1, h1304, h2, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1306 | h1306
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1307 | h1307
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1308 | h1308
                · linarith only [h0, h1301, h1308, h2, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1310 | h1310
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1311 | h1311
                    · linarith only [h0, h1304, h1307, h1311, h2, hlam]
                    · linarith only [h0, h1307, h1311, h2, hc23, hc34, hlam, hphi]
                  · linarith only [h1307, h1310, hc23, hlam, hphi, ht34, ht45, u5elo2]
              · linarith only [h1300, h1301, h1307, hc12, hc24, hlam, hphi]
            · linarith only [h1306, h2, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
        · linarith only [h1303, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h1318 | h1318
      · linarith only [h0, h1318, h2, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1320 | h1320
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1321 | h1321
          · linarith only [h1, h1321, h2, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1323 | h1323
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1324 | h1324
              · linarith only [h0, h1300, h1324, h2, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1326 | h1326
                · linarith only [h0, h1318, h1326, h2, hlam]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1328 | h1328
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1329 | h1329
                    · linarith only [h1, h1300, h1321, h1326, h1329, h2, hc02, hc24, hlam, hphi]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1331 | h1331
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h1332 | h1332
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h1333 | h1333
                          · linarith only [h0, h1328, h1329, h1333, h2, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h1335 | h1335
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h1336 | h1336
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h1337 | h1337
                                · rcases h1bigk with h1338c | h1338c | h1338c | h1338c | h1338c | h1338c | h1338c | h1338c | h1338c | h1338c | h1338c | h1338c | h1338c | h1338c | h1338c | h1338c | h1338c | h1338c | h1338c | h1338c | h1338c | h1338c | h1338c | h1338c | h1338c
                                  · have p1338_0 := h1338c.1
                                    have p1338_1 := h1338c.2.1
                                    have p1338_2 := h1338c.2.2.1
                                    have p1338_3 := h1338c.2.2.2
                                    linarith only [hlam, p1338_0]
                                  · have p1338_0 := h1338c.1
                                    have p1338_1 := h1338c.2.1
                                    have p1338_2 := h1338c.2.2.1
                                    have p1338_3 := h1338c.2.2.2
                                    linarith only [h1328, h1335, h1337, h2, hc14, hc45, hlam, hphi, ht01, ht0b, ht5b, p1338_1]
                                  · have p1338_0 := h1338c.1
                                    have p1338_1 := h1338c.2.1
                                    have p1338_2 := h1338c.2.2.1
                                    have p1338_3 := h1338c.2.2.2
                                    linarith only [h1324, h1326, h1328, h1333, h1335, h1337, h2, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1338_1]
                                  · have p1338_0 := h1338c.1
                                    have p1338_1 := h1338c.2.1
                                    have p1338_2 := h1338c.2.2.1
                                    have p1338_3 := h1338c.2.2.2
                                    linarith only [h2, hlam, p1338_0]
                                  · have p1338_0 := h1338c.1
                                    have p1338_1 := h1338c.2.1
                                    have p1338_2 := h1338c.2.2.1
                                    have p1338_3 := h1338c.2.2.2
                                    rcases p1338_3 (m.d 0 1) (by simp) with h1343 | h1343
                                    · rcases p1338_3 (m.d 1 2) (by simp) with h1344 | h1344
                                      · linarith only [h0, h1344, hlam]
                                      · linarith only [h1328, h1344, hlam]
                                    · linarith only [h1343, hlam, p1338_0]
                                  · have p1338_0 := h1338c.1
                                    have p1338_1 := h1338c.2.1
                                    have p1338_2 := h1338c.2.2.1
                                    have p1338_3 := h1338c.2.2.2
                                    linarith only [h0, hlam, p1338_0]
                                  · have p1338_0 := h1338c.1
                                    have p1338_1 := h1338c.2.1
                                    have p1338_2 := h1338c.2.2.1
                                    have p1338_3 := h1338c.2.2.2
                                    linarith only [hlam, p1338_0]
                                  · have p1338_0 := h1338c.1
                                    have p1338_1 := h1338c.2.1
                                    have p1338_2 := h1338c.2.2.1
                                    have p1338_3 := h1338c.2.2.2
                                    linarith only [h1324, hlam, p1338_1]
                                  · have p1338_0 := h1338c.1
                                    have p1338_1 := h1338c.2.1
                                    have p1338_2 := h1338c.2.2.1
                                    have p1338_3 := h1338c.2.2.2
                                    linarith only [h1326, hlam, p1338_1]
                                  · have p1338_0 := h1338c.1
                                    have p1338_1 := h1338c.2.1
                                    have p1338_2 := h1338c.2.2.1
                                    have p1338_3 := h1338c.2.2.2
                                    linarith only [h0, h1326, h1333, h2, hc15, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1338_1]
                                  · have p1338_0 := h1338c.1
                                    have p1338_1 := h1338c.2.1
                                    have p1338_2 := h1338c.2.2.1
                                    have p1338_3 := h1338c.2.2.2
                                    linarith only [h1, hlam, p1338_0]
                                  · have p1338_0 := h1338c.1
                                    have p1338_1 := h1338c.2.1
                                    have p1338_2 := h1338c.2.2.1
                                    have p1338_3 := h1338c.2.2.2
                                    linarith only [h1, h1326, h1333, h2, hc12, hc34, hlam, hphi, ht23, p1338_1]
                                  · have p1338_0 := h1338c.1
                                    have p1338_1 := h1338c.2.1
                                    have p1338_2 := h1338c.2.2.1
                                    have p1338_3 := h1338c.2.2.2
                                    linarith only [hlam, p1338_0]
                                  · have p1338_0 := h1338c.1
                                    have p1338_1 := h1338c.2.1
                                    have p1338_2 := h1338c.2.2.1
                                    have p1338_3 := h1338c.2.2.2
                                    linarith only [h1329, hlam, p1338_0]
                                  · have p1338_0 := h1338c.1
                                    have p1338_1 := h1338c.2.1
                                    have p1338_2 := h1338c.2.2.1
                                    have p1338_3 := h1338c.2.2.2
                                    linarith only [h1, h1326, h1328, h1333, h1335, h1337, h2, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1338_1]
                                  · have p1338_0 := h1338c.1
                                    have p1338_1 := h1338c.2.1
                                    have p1338_2 := h1338c.2.2.1
                                    have p1338_3 := h1338c.2.2.2
                                    linarith only [h1, h1326, h1333, hc13, hc34, hlam, hphi, p1338_1]
                                  · have p1338_0 := h1338c.1
                                    have p1338_1 := h1338c.2.1
                                    have p1338_2 := h1338c.2.2.1
                                    have p1338_3 := h1338c.2.2.2
                                    rcases p1338_3 (m.d 0 1) (by simp) with h1359 | h1359
                                    · linarith only [h1359, h2, hlam]
                                    · linarith only [h0, h1359, hlam]
                                  · have p1338_0 := h1338c.1
                                    have p1338_1 := h1338c.2.1
                                    have p1338_2 := h1338c.2.2.1
                                    have p1338_3 := h1338c.2.2.2
                                    rcases p1338_3 (m.d 0 1) (by simp) with h1362 | h1362
                                    · linarith only [h1362, h2, hlam]
                                    · linarith only [h1, h1362, hlam]
                                  · have p1338_0 := h1338c.1
                                    have p1338_1 := h1338c.2.1
                                    have p1338_2 := h1338c.2.2.1
                                    have p1338_3 := h1338c.2.2.2
                                    linarith only [hlam, p1338_0]
                                  · have p1338_0 := h1338c.1
                                    have p1338_1 := h1338c.2.1
                                    have p1338_2 := h1338c.2.2.1
                                    have p1338_3 := h1338c.2.2.2
                                    rcases p1338_3 (m.d 0 1) (by simp) with h1366 | h1366
                                    · linarith only [h1366, h2, hlam]
                                    · linarith only [h1299, h1366, hlam]
                                  · have p1338_0 := h1338c.1
                                    have p1338_1 := h1338c.2.1
                                    have p1338_2 := h1338c.2.2.1
                                    have p1338_3 := h1338c.2.2.2
                                    linarith only [h1299, hlam, p1338_0]
                                  · have p1338_0 := h1338c.1
                                    have p1338_1 := h1338c.2.1
                                    have p1338_2 := h1338c.2.2.1
                                    have p1338_3 := h1338c.2.2.2
                                    linarith only [h1328, hlam, p1338_0]
                                  · have p1338_0 := h1338c.1
                                    have p1338_1 := h1338c.2.1
                                    have p1338_2 := h1338c.2.2.1
                                    have p1338_3 := h1338c.2.2.2
                                    linarith only [h1331, hlam, p1338_0]
                                  · have p1338_0 := h1338c.1
                                    have p1338_1 := h1338c.2.1
                                    have p1338_2 := h1338c.2.2.1
                                    have p1338_3 := h1338c.2.2.2
                                    linarith only [h1332, hlam, p1338_0]
                                  · have p1338_0 := h1338c.1
                                    have p1338_1 := h1338c.2.1
                                    have p1338_2 := h1338c.2.2.1
                                    have p1338_3 := h1338c.2.2.2
                                    linarith only [hlam, p1338_0]
                                · linarith only [h1333, h1337, hc23, hlam, hphi, ht34, ht45, u5elo4]
                              · linarith only [h1, h1324, h1326, h1328, h1332, h1336, h2, hc15, hc25, hlam, hphi, ht01, ht0b, ht5b]
                            · linarith only [h1300, h1335, hc02, hlam, hphi, ht23, ht34, ht45, u5elo3]
                        · linarith only [h1, h1323, h1324, h1328, h1332, h2, hc25, hlam, hphi, u5elo0]
                      · linarith only [h1324, h1328, h1331, hc25, hlam, hphi, u5elo3]
                  · linarith only [h1328, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
            · linarith only [h1323, hc04, hlam, hphi, ht45, u5elo4]
        · linarith only [h1320, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
  · linarith only [h0, h1299, hc12, hlam, hphi, ht23, ht34, ht45, u5elo1]

set_option maxHeartbeats 6266000 in
set_option maxHeartbeats 6266000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_L_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
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
  have h1bigk := hb1.1
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_L_x0_x0_x0 m hb1 hb2 hb4 hb5 h0 h1 h2
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_L_x0_x0_x1 m hb1 hb2 hb4 hb5 h0 h1 h2

set_option maxHeartbeats 6266000 in
set_option maxHeartbeats 6266000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_L_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
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
  have h1bigk := hb1.1
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h1383 | h1383
  · rcases m.htr 0 1 5 (by decide) (by decide) with h1384 | h1384
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1385 | h1385
      · linarith only [h0, h1, h1385, hlam]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h1387 | h1387
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1388 | h1388
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1389 | h1389
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1390 | h1390
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1391 | h1391
                · linarith only [h0, h1, h1385, h1391, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1393 | h1393
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1394 | h1394
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1395 | h1395
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1396 | h1396
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1397 | h1397
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1398 | h1398
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1399 | h1399
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1400 | h1400
                                · linarith only [h0, h1, h1391, h1393, h1400, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                                · linarith only [h1400, hc24, hlam, hphi, ht45, u5elo4]
                              · linarith only [h0, h1, h1391, h1399, hc12, hc35, hlam, hphi, ht23]
                            · linarith only [h0, h1, h1391, h1393, h1397, h1398, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                          · linarith only [h1397, hc14, hlam, hphi, ht45, u5elo4]
                        · linarith only [h0, h1, h1393, h1396, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                      · linarith only [h0, h1, h1393, h1395, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                    · linarith only [h1393, h1394, hc24, hlam, hphi, ht45, u5elo2]
                  · linarith only [h0, h1, h1387, h1391, h1393, hc12, hc23, hlam, hphi]
              · linarith only [h1390, hc04, hlam, hphi, ht45, u5elo4]
            · linarith only [h1, h1383, h1389, hlam]
          · linarith only [h1388, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1413 | h1413
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1414 | h1414
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1415 | h1415
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1416 | h1416
                · linarith only [h0, h1, h1385, h1416, hlam]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1418 | h1418
                  · linarith only [h0, h1387, h1418, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1420 | h1420
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1421 | h1421
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1422 | h1422
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1423 | h1423
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1424 | h1424
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1425 | h1425
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1426 | h1426
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1427 | h1427
                                  · rcases h1bigk with h1428c | h1428c | h1428c | h1428c | h1428c | h1428c | h1428c | h1428c | h1428c | h1428c | h1428c | h1428c | h1428c | h1428c | h1428c | h1428c | h1428c | h1428c | h1428c | h1428c | h1428c | h1428c | h1428c | h1428c | h1428c
                                    · have p1428_0 := h1428c.1
                                      have p1428_1 := h1428c.2.1
                                      have p1428_2 := h1428c.2.2.1
                                      have p1428_3 := h1428c.2.2.2
                                      linarith only [hlam, p1428_0]
                                    · have p1428_0 := h1428c.1
                                      have p1428_1 := h1428c.2.1
                                      have p1428_2 := h1428c.2.2.1
                                      have p1428_3 := h1428c.2.2.2
                                      linarith only [h1, h1420, h1425, h1427, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p1428_1]
                                    · have p1428_0 := h1428c.1
                                      have p1428_1 := h1428c.2.1
                                      have p1428_2 := h1428c.2.2.1
                                      have p1428_3 := h1428c.2.2.2
                                      linarith only [h1, hlam, p1428_0]
                                    · have p1428_0 := h1428c.1
                                      have p1428_1 := h1428c.2.1
                                      have p1428_2 := h1428c.2.2.1
                                      have p1428_3 := h1428c.2.2.2
                                      linarith only [h1, h1416, h1418, h1420, h1425, h1427, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1428_1]
                                    · have p1428_0 := h1428c.1
                                      have p1428_1 := h1428c.2.1
                                      have p1428_2 := h1428c.2.2.1
                                      have p1428_3 := h1428c.2.2.2
                                      rcases p1428_3 (m.d 0 1) (by simp) with h1433 | h1433
                                      · rcases p1428_3 (m.d 1 2) (by simp) with h1434 | h1434
                                        · linarith only [h0, h1434, hlam]
                                        · linarith only [h1420, h1434, hlam]
                                      · linarith only [h1433, hlam, p1428_0]
                                    · have p1428_0 := h1428c.1
                                      have p1428_1 := h1428c.2.1
                                      have p1428_2 := h1428c.2.2.1
                                      have p1428_3 := h1428c.2.2.2
                                      linarith only [h0, hlam, p1428_0]
                                    · have p1428_0 := h1428c.1
                                      have p1428_1 := h1428c.2.1
                                      have p1428_2 := h1428c.2.2.1
                                      have p1428_3 := h1428c.2.2.2
                                      linarith only [hlam, p1428_0]
                                    · have p1428_0 := h1428c.1
                                      have p1428_1 := h1428c.2.1
                                      have p1428_2 := h1428c.2.2.1
                                      have p1428_3 := h1428c.2.2.2
                                      linarith only [h1416, hlam, p1428_1]
                                    · have p1428_0 := h1428c.1
                                      have p1428_1 := h1428c.2.1
                                      have p1428_2 := h1428c.2.2.1
                                      have p1428_3 := h1428c.2.2.2
                                      linarith only [h1418, hlam, p1428_1]
                                    · have p1428_0 := h1428c.1
                                      have p1428_1 := h1428c.2.1
                                      have p1428_2 := h1428c.2.2.1
                                      have p1428_3 := h1428c.2.2.2
                                      linarith only [h0, h1, h1416, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1428_1]
                                    · have p1428_0 := h1428c.1
                                      have p1428_1 := h1428c.2.1
                                      have p1428_2 := h1428c.2.2.1
                                      have p1428_3 := h1428c.2.2.2
                                      linarith only [h0, h1416, hc12, hc23, hlam, hphi, p1428_1]
                                    · have p1428_0 := h1428c.1
                                      have p1428_1 := h1428c.2.1
                                      have p1428_2 := h1428c.2.2.1
                                      have p1428_3 := h1428c.2.2.2
                                      rcases p1428_3 (m.d 0 1) (by simp) with h1444 | h1444
                                      · linarith only [h1, h1444, hlam]
                                      · linarith only [h0, h1444, hlam]
                                    · have p1428_0 := h1428c.1
                                      have p1428_1 := h1428c.2.1
                                      have p1428_2 := h1428c.2.2.1
                                      have p1428_3 := h1428c.2.2.2
                                      linarith only [hlam, p1428_0]
                                    · have p1428_0 := h1428c.1
                                      have p1428_1 := h1428c.2.1
                                      have p1428_2 := h1428c.2.2.1
                                      have p1428_3 := h1428c.2.2.2
                                      rcases p1428_3 (m.d 0 1) (by simp) with h1448 | h1448
                                      · linarith only [h1, h1448, hlam]
                                      · linarith only [h1383, h1448, hlam]
                                    · have p1428_0 := h1428c.1
                                      have p1428_1 := h1428c.2.1
                                      have p1428_2 := h1428c.2.2.1
                                      have p1428_3 := h1428c.2.2.2
                                      rcases p1428_3 (m.d 0 1) (by simp) with h1451 | h1451
                                      · linarith only [h1, h1451, hlam]
                                      · linarith only [h1384, h1451, hlam]
                                    · have p1428_0 := h1428c.1
                                      have p1428_1 := h1428c.2.1
                                      have p1428_2 := h1428c.2.2.1
                                      have p1428_3 := h1428c.2.2.2
                                      linarith only [h1383, hlam, p1428_0]
                                    · have p1428_0 := h1428c.1
                                      have p1428_1 := h1428c.2.1
                                      have p1428_2 := h1428c.2.2.1
                                      have p1428_3 := h1428c.2.2.2
                                      linarith only [h1383, h1420, h1425, h1427, hc01, hc45, hlam, hphi, ht0b, ht5b, p1428_1]
                                    · have p1428_0 := h1428c.1
                                      have p1428_1 := h1428c.2.1
                                      have p1428_2 := h1428c.2.2.1
                                      have p1428_3 := h1428c.2.2.2
                                      linarith only [h1421, hlam, p1428_1]
                                    · have p1428_0 := h1428c.1
                                      have p1428_1 := h1428c.2.1
                                      have p1428_2 := h1428c.2.2.1
                                      have p1428_3 := h1428c.2.2.2
                                      linarith only [hlam, p1428_0]
                                    · have p1428_0 := h1428c.1
                                      have p1428_1 := h1428c.2.1
                                      have p1428_2 := h1428c.2.2.1
                                      have p1428_3 := h1428c.2.2.2
                                      linarith only [h1, h1383, h1416, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1428_1]
                                    · have p1428_0 := h1428c.1
                                      have p1428_1 := h1428c.2.1
                                      have p1428_2 := h1428c.2.2.1
                                      have p1428_3 := h1428c.2.2.2
                                      linarith only [h1384, hlam, p1428_0]
                                    · have p1428_0 := h1428c.1
                                      have p1428_1 := h1428c.2.1
                                      have p1428_2 := h1428c.2.2.1
                                      have p1428_3 := h1428c.2.2.2
                                      linarith only [h1420, hlam, p1428_0]
                                    · have p1428_0 := h1428c.1
                                      have p1428_1 := h1428c.2.1
                                      have p1428_2 := h1428c.2.2.1
                                      have p1428_3 := h1428c.2.2.2
                                      linarith only [h1422, hlam, p1428_0]
                                    · have p1428_0 := h1428c.1
                                      have p1428_1 := h1428c.2.1
                                      have p1428_2 := h1428c.2.2.1
                                      have p1428_3 := h1428c.2.2.2
                                      linarith only [h1423, hlam, p1428_0]
                                    · have p1428_0 := h1428c.1
                                      have p1428_1 := h1428c.2.1
                                      have p1428_2 := h1428c.2.2.1
                                      have p1428_3 := h1428c.2.2.2
                                      linarith only [hlam, p1428_0]
                                  · linarith only [h1427, hc34, hlam, hphi, ht45, u5elo4]
                                · linarith only [h1, h1383, h1387, h1416, h1423, h1426, hc02, hc23, hlam, hphi]
                              · linarith only [h1, h1383, h1416, h1423, h1425, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                            · linarith only [h1, h1383, h1416, h1418, h1420, h1424, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                          · linarith only [h1418, h1420, h1423, hc25, hlam, hphi, u5elo4]
                        · linarith only [h1, h1383, h1418, h1420, h1422, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                      · linarith only [h1, h1383, h1418, h1420, h1421, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                    · linarith only [h1420, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
              · linarith only [h1387, h1415, hc02, hlam, hphi, ht23, ht34, ht45, u5elo4]
            · linarith only [h1, h1383, h1414, hlam]
          · linarith only [h1413, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
    · linarith only [h0, h1384, hc12, hlam, hphi, ht23, ht34, ht45, u5elo1]
  · rcases m.htr 0 1 5 (by decide) (by decide) with h1476 | h1476
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1477 | h1477
      · linarith only [h0, h1, h1477, hlam]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h1479 | h1479
        · linarith only [h0, h1383, h1479, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1481 | h1481
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1482 | h1482
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1483 | h1483
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1484 | h1484
                · linarith only [h0, h1, h1477, h1484, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1486 | h1486
                  · linarith only [h0, h1383, h1479, h1486, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1488 | h1488
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1489 | h1489
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1490 | h1490
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1491 | h1491
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1492 | h1492
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1493 | h1493
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1494 | h1494
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1495 | h1495
                                  · rcases h1bigk with h1496c | h1496c | h1496c | h1496c | h1496c | h1496c | h1496c | h1496c | h1496c | h1496c | h1496c | h1496c | h1496c | h1496c | h1496c | h1496c | h1496c | h1496c | h1496c | h1496c | h1496c | h1496c | h1496c | h1496c | h1496c
                                    · have p1496_0 := h1496c.1
                                      have p1496_1 := h1496c.2.1
                                      have p1496_2 := h1496c.2.2.1
                                      have p1496_3 := h1496c.2.2.2
                                      linarith only [hlam, p1496_0]
                                    · have p1496_0 := h1496c.1
                                      have p1496_1 := h1496c.2.1
                                      have p1496_2 := h1496c.2.2.1
                                      have p1496_3 := h1496c.2.2.2
                                      linarith only [h1383, h1484, h1489, hc12, hc23, hlam, hphi, p1496_1]
                                    · have p1496_0 := h1496c.1
                                      have p1496_1 := h1496c.2.1
                                      have p1496_2 := h1496c.2.2.1
                                      have p1496_3 := h1496c.2.2.2
                                      linarith only [h1, hlam, p1496_0]
                                    · have p1496_0 := h1496c.1
                                      have p1496_1 := h1496c.2.1
                                      have p1496_2 := h1496c.2.2.1
                                      have p1496_3 := h1496c.2.2.2
                                      linarith only [h1383, hlam, p1496_0]
                                    · have p1496_0 := h1496c.1
                                      have p1496_1 := h1496c.2.1
                                      have p1496_2 := h1496c.2.2.1
                                      have p1496_3 := h1496c.2.2.2
                                      rcases p1496_3 (m.d 0 1) (by simp) with h1501 | h1501
                                      · rcases p1496_3 (m.d 1 2) (by simp) with h1502 | h1502
                                        · linarith only [h0, h1502, hlam]
                                        · linarith only [h1488, h1502, hlam]
                                      · linarith only [h1501, hlam, p1496_0]
                                    · have p1496_0 := h1496c.1
                                      have p1496_1 := h1496c.2.1
                                      have p1496_2 := h1496c.2.2.1
                                      have p1496_3 := h1496c.2.2.2
                                      linarith only [h0, hlam, p1496_0]
                                    · have p1496_0 := h1496c.1
                                      have p1496_1 := h1496c.2.1
                                      have p1496_2 := h1496c.2.2.1
                                      have p1496_3 := h1496c.2.2.2
                                      linarith only [hlam, p1496_0]
                                    · have p1496_0 := h1496c.1
                                      have p1496_1 := h1496c.2.1
                                      have p1496_2 := h1496c.2.2.1
                                      have p1496_3 := h1496c.2.2.2
                                      linarith only [h1484, hlam, p1496_1]
                                    · have p1496_0 := h1496c.1
                                      have p1496_1 := h1496c.2.1
                                      have p1496_2 := h1496c.2.2.1
                                      have p1496_3 := h1496c.2.2.2
                                      linarith only [h1486, hlam, p1496_1]
                                    · have p1496_0 := h1496c.1
                                      have p1496_1 := h1496c.2.1
                                      have p1496_2 := h1496c.2.2.1
                                      have p1496_3 := h1496c.2.2.2
                                      linarith only [h0, h1383, h1484, h1489, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1496_1]
                                    · have p1496_0 := h1496c.1
                                      have p1496_1 := h1496c.2.1
                                      have p1496_2 := h1496c.2.2.1
                                      have p1496_3 := h1496c.2.2.2
                                      linarith only [h0, h1484, hc12, hc23, hlam, hphi, p1496_1]
                                    · have p1496_0 := h1496c.1
                                      have p1496_1 := h1496c.2.1
                                      have p1496_2 := h1496c.2.2.1
                                      have p1496_3 := h1496c.2.2.2
                                      rcases p1496_3 (m.d 0 1) (by simp) with h1512 | h1512
                                      · linarith only [h1, h1512, hlam]
                                      · linarith only [h0, h1512, hlam]
                                    · have p1496_0 := h1496c.1
                                      have p1496_1 := h1496c.2.1
                                      have p1496_2 := h1496c.2.2.1
                                      have p1496_3 := h1496c.2.2.2
                                      linarith only [hlam, p1496_0]
                                    · have p1496_0 := h1496c.1
                                      have p1496_1 := h1496c.2.1
                                      have p1496_2 := h1496c.2.2.1
                                      have p1496_3 := h1496c.2.2.2
                                      linarith only [h0, h1383, h1484, h1488, h1493, h1495, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1496_1]
                                    · have p1496_0 := h1496c.1
                                      have p1496_1 := h1496c.2.1
                                      have p1496_2 := h1496c.2.2.1
                                      have p1496_3 := h1496c.2.2.2
                                      rcases p1496_3 (m.d 0 1) (by simp) with h1517 | h1517
                                      · linarith only [h1, h1517, hlam]
                                      · linarith only [h1476, h1517, hlam]
                                    · have p1496_0 := h1496c.1
                                      have p1496_1 := h1496c.2.1
                                      have p1496_2 := h1496c.2.2.1
                                      have p1496_3 := h1496c.2.2.2
                                      linarith only [h0, h1488, h1489, h1493, h1495, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p1496_1]
                                    · have p1496_0 := h1496c.1
                                      have p1496_1 := h1496c.2.1
                                      have p1496_2 := h1496c.2.2.1
                                      have p1496_3 := h1496c.2.2.2
                                      rcases p1496_3 (m.d 0 1) (by simp) with h1521 | h1521
                                      · linarith only [h1383, h1521, hlam]
                                      · linarith only [h0, h1521, hlam]
                                    · have p1496_0 := h1496c.1
                                      have p1496_1 := h1496c.2.1
                                      have p1496_2 := h1496c.2.2.1
                                      have p1496_3 := h1496c.2.2.2
                                      linarith only [h1489, hlam, p1496_1]
                                    · have p1496_0 := h1496c.1
                                      have p1496_1 := h1496c.2.1
                                      have p1496_2 := h1496c.2.2.1
                                      have p1496_3 := h1496c.2.2.2
                                      linarith only [hlam, p1496_0]
                                    · have p1496_0 := h1496c.1
                                      have p1496_1 := h1496c.2.1
                                      have p1496_2 := h1496c.2.2.1
                                      have p1496_3 := h1496c.2.2.2
                                      rcases p1496_3 (m.d 0 1) (by simp) with h1526 | h1526
                                      · linarith only [h1383, h1526, hlam]
                                      · linarith only [h1476, h1526, hlam]
                                    · have p1496_0 := h1496c.1
                                      have p1496_1 := h1496c.2.1
                                      have p1496_2 := h1496c.2.2.1
                                      have p1496_3 := h1496c.2.2.2
                                      linarith only [h1476, hlam, p1496_0]
                                    · have p1496_0 := h1496c.1
                                      have p1496_1 := h1496c.2.1
                                      have p1496_2 := h1496c.2.2.1
                                      have p1496_3 := h1496c.2.2.2
                                      linarith only [h1488, hlam, p1496_0]
                                    · have p1496_0 := h1496c.1
                                      have p1496_1 := h1496c.2.1
                                      have p1496_2 := h1496c.2.2.1
                                      have p1496_3 := h1496c.2.2.2
                                      linarith only [h1490, hlam, p1496_0]
                                    · have p1496_0 := h1496c.1
                                      have p1496_1 := h1496c.2.1
                                      have p1496_2 := h1496c.2.2.1
                                      have p1496_3 := h1496c.2.2.2
                                      linarith only [h1491, hlam, p1496_0]
                                    · have p1496_0 := h1496c.1
                                      have p1496_1 := h1496c.2.1
                                      have p1496_2 := h1496c.2.2.1
                                      have p1496_3 := h1496c.2.2.2
                                      linarith only [hlam, p1496_0]
                                  · linarith only [h1495, hc34, hlam, hphi, ht45, u5elo4]
                                · linarith only [h1491, h1494, hc24, hlam, hphi, ht45, u5elo1]
                              · linarith only [h0, h1383, h1484, h1489, h1493, hc12, hc35, hlam, hphi, ht23]
                            · linarith only [h0, h1383, h1484, h1488, h1489, h1492, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                          · linarith only [h0, h1383, h1488, h1491, hc25, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b]
                        · linarith only [h0, h1383, h1488, h1489, h1490, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                      · linarith only [h0, h1, h1482, h1488, h1489, hc03, hc25, hlam, hphi, ht0b, ht5b]
                    · linarith only [h1488, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
              · linarith only [h1383, h1483, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1543 | h1543
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1544 | h1544
                · linarith only [h0, h1477, h1544, hlam]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1546 | h1546
                  · linarith only [h0, h1479, h1546, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1548 | h1548
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1549 | h1549
                      · linarith only [h0, h1, h1482, h1544, h1549, hc12, hc23, hlam, hphi]
                      · linarith only [h0, h1, h1548, h1549, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                    · linarith only [h1548, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
              · linarith only [h0, h1, h1482, h1543, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
          · linarith only [h1481, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
    · linarith only [h0, h1476, hc12, hlam, hphi, ht23, ht34, ht45, u5elo1]

set_option maxHeartbeats 6266000 in
set_option maxHeartbeats 6266000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_L_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
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
  have h1bigk := hb1.1
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_L_x0_x0 m hb1 hb2 hb4 hb5 h0 h1
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_L_x0_x1 m hb1 hb2 hb4 hb5 h0 h1

set_option maxHeartbeats 6266000 in
set_option maxHeartbeats 6266000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_L_x1_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1556 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
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
  have h1bigk := hb1.1
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h1557 | h1557
  · rcases m.htr 0 1 5 (by decide) (by decide) with h1558 | h1558
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1559 | h1559
      · rcases m.htr 0 2 4 (by decide) (by decide) with h1560 | h1560
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1561 | h1561
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1562 | h1562
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1563 | h1563
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1564 | h1564
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1565 | h1565
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1566 | h1566
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1567 | h1567
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1568 | h1568
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1569 | h1569
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1570 | h1570
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1571 | h1571
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1572 | h1572
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1573 | h1573
                                  · linarith only [h0, h1556, h1564, h1570, h1573, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                                  · linarith only [h1573, hc34, hlam, hphi, ht45, u5elo4]
                                · linarith only [h0, h1556, h1567, h1569, h1572, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                              · linarith only [h1571, hc23, hlam, hphi, ht34, ht45, u5elo3]
                            · linarith only [h0, h1556, h1567, h1570, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                          · linarith only [h1569, hc14, hlam, hphi, ht45, u5elo4]
                        · linarith only [h1568, hc13, hlam, hphi, ht34, ht45, u5elo3]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1581 | h1581
                        · linarith only [h0, h1556, h1562, h1567, h1581, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                        · linarith only [h1581, hc13, hlam, hphi, ht34, ht45, u5elo3]
                    · linarith only [h0, h1566, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
                  · linarith only [h0, h1558, h1560, h1565, hc02, hc15, hlam, hphi, ht0b, ht5b]
                · linarith only [h0, h1559, h1564, hlam]
              · linarith only [h1563, hc04, hlam, hphi, ht45, u5elo4]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1588 | h1588
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1589 | h1589
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1590 | h1590
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1591 | h1591
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1592 | h1592
                      · linarith only [h1556, h1562, h1592, hlam]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1594 | h1594
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1595 | h1595
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1596 | h1596
                            · linarith only [h1556, h1562, h1589, h1596, hlam]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1598 | h1598
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1599 | h1599
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1600 | h1600
                                  · rcases h1bigk with h1601c | h1601c | h1601c | h1601c | h1601c | h1601c | h1601c | h1601c | h1601c | h1601c | h1601c | h1601c | h1601c | h1601c | h1601c | h1601c | h1601c | h1601c | h1601c | h1601c | h1601c | h1601c | h1601c | h1601c | h1601c
                                    · have p1601_0 := h1601c.1
                                      have p1601_1 := h1601c.2.1
                                      have p1601_2 := h1601c.2.2.1
                                      have p1601_3 := h1601c.2.2.2
                                      linarith only [hlam, p1601_0]
                                    · have p1601_0 := h1601c.1
                                      have p1601_1 := h1601c.2.1
                                      have p1601_2 := h1601c.2.2.1
                                      have p1601_3 := h1601c.2.2.2
                                      linarith only [h0, hlam, p1601_0]
                                    · have p1601_0 := h1601c.1
                                      have p1601_1 := h1601c.2.1
                                      have p1601_2 := h1601c.2.2.1
                                      have p1601_3 := h1601c.2.2.2
                                      linarith only [h0, h1589, h1598, h1600, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1601_1]
                                    · have p1601_0 := h1601c.1
                                      have p1601_1 := h1601c.2.1
                                      have p1601_2 := h1601c.2.2.1
                                      have p1601_3 := h1601c.2.2.2
                                      linarith only [h0, h1589, h1592, h1598, h1600, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1601_1]
                                    · have p1601_0 := h1601c.1
                                      have p1601_1 := h1601c.2.1
                                      have p1601_2 := h1601c.2.2.1
                                      have p1601_3 := h1601c.2.2.2
                                      rcases p1601_3 (m.d 0 1) (by simp) with h1606 | h1606
                                      · rcases p1601_3 (m.d 1 2) (by simp) with h1607 | h1607
                                        · rcases p1601_3 (m.d 1 3) (by simp) with h1608 | h1608
                                          · linarith only [h1556, h1608, hlam]
                                          · linarith only [h1594, h1608, hlam]
                                        · linarith only [h1591, h1607, hlam]
                                      · linarith only [h1606, hlam, p1601_0]
                                    · have p1601_0 := h1601c.1
                                      have p1601_1 := h1601c.2.1
                                      have p1601_2 := h1601c.2.2.1
                                      have p1601_3 := h1601c.2.2.2
                                      linarith only [h1556, h1589, h1598, h1600, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1601_1]
                                    · have p1601_0 := h1601c.1
                                      have p1601_1 := h1601c.2.1
                                      have p1601_2 := h1601c.2.2.1
                                      have p1601_3 := h1601c.2.2.2
                                      linarith only [hlam, p1601_0]
                                    · have p1601_0 := h1601c.1
                                      have p1601_1 := h1601c.2.1
                                      have p1601_2 := h1601c.2.2.1
                                      have p1601_3 := h1601c.2.2.2
                                      rcases p1601_3 (m.d 0 1) (by simp) with h1615 | h1615
                                      · linarith only [h0, h1615, hlam]
                                      · linarith only [h1556, h1615, hlam]
                                    · have p1601_0 := h1601c.1
                                      have p1601_1 := h1601c.2.1
                                      have p1601_2 := h1601c.2.2.1
                                      have p1601_3 := h1601c.2.2.2
                                      rcases p1601_3 (m.d 0 1) (by simp) with h1618 | h1618
                                      · linarith only [h0, h1618, hlam]
                                      · linarith only [h1557, h1618, hlam]
                                    · have p1601_0 := h1601c.1
                                      have p1601_1 := h1601c.2.1
                                      have p1601_2 := h1601c.2.2.1
                                      have p1601_3 := h1601c.2.2.2
                                      rcases p1601_3 (m.d 0 1) (by simp) with h1621 | h1621
                                      · linarith only [h0, h1621, hlam]
                                      · linarith only [h1558, h1621, hlam]
                                    · have p1601_0 := h1601c.1
                                      have p1601_1 := h1601c.2.1
                                      have p1601_2 := h1601c.2.2.1
                                      have p1601_3 := h1601c.2.2.2
                                      linarith only [h1556, hlam, p1601_0]
                                    · have p1601_0 := h1601c.1
                                      have p1601_1 := h1601c.2.1
                                      have p1601_2 := h1601c.2.2.1
                                      have p1601_3 := h1601c.2.2.2
                                      linarith only [h1589, hlam, p1601_0]
                                    · have p1601_0 := h1601c.1
                                      have p1601_1 := h1601c.2.1
                                      have p1601_2 := h1601c.2.2.1
                                      have p1601_3 := h1601c.2.2.2
                                      linarith only [hlam, p1601_0]
                                    · have p1601_0 := h1601c.1
                                      have p1601_1 := h1601c.2.1
                                      have p1601_2 := h1601c.2.2.1
                                      have p1601_3 := h1601c.2.2.2
                                      linarith only [h1592, hlam, p1601_0]
                                    · have p1601_0 := h1601c.1
                                      have p1601_1 := h1601c.2.1
                                      have p1601_2 := h1601c.2.2.1
                                      have p1601_3 := h1601c.2.2.2
                                      linarith only [h0, h1557, h1592, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b, p1601_1]
                                    · have p1601_0 := h1601c.1
                                      have p1601_1 := h1601c.2.1
                                      have p1601_2 := h1601c.2.2.1
                                      have p1601_3 := h1601c.2.2.2
                                      linarith only [h1557, hlam, p1601_0]
                                    · have p1601_0 := h1601c.1
                                      have p1601_1 := h1601c.2.1
                                      have p1601_2 := h1601c.2.2.1
                                      have p1601_3 := h1601c.2.2.2
                                      linarith only [h1590, hlam, p1601_0]
                                    · have p1601_0 := h1601c.1
                                      have p1601_1 := h1601c.2.1
                                      have p1601_2 := h1601c.2.2.1
                                      have p1601_3 := h1601c.2.2.2
                                      linarith only [h0, h1557, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1601_1]
                                    · have p1601_0 := h1601c.1
                                      have p1601_1 := h1601c.2.1
                                      have p1601_2 := h1601c.2.2.1
                                      have p1601_3 := h1601c.2.2.2
                                      linarith only [hlam, p1601_0]
                                    · have p1601_0 := h1601c.1
                                      have p1601_1 := h1601c.2.1
                                      have p1601_2 := h1601c.2.2.1
                                      have p1601_3 := h1601c.2.2.2
                                      linarith only [h0, h1557, h1594, h1600, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1601_1]
                                    · have p1601_0 := h1601c.1
                                      have p1601_1 := h1601c.2.1
                                      have p1601_2 := h1601c.2.2.1
                                      have p1601_3 := h1601c.2.2.2
                                      linarith only [h1558, hlam, p1601_0]
                                    · have p1601_0 := h1601c.1
                                      have p1601_1 := h1601c.2.1
                                      have p1601_2 := h1601c.2.2.1
                                      have p1601_3 := h1601c.2.2.2
                                      linarith only [h1591, hlam, p1601_0]
                                    · have p1601_0 := h1601c.1
                                      have p1601_1 := h1601c.2.1
                                      have p1601_2 := h1601c.2.2.1
                                      have p1601_3 := h1601c.2.2.2
                                      linarith only [h1594, hlam, p1601_0]
                                    · have p1601_0 := h1601c.1
                                      have p1601_1 := h1601c.2.1
                                      have p1601_2 := h1601c.2.2.1
                                      have p1601_3 := h1601c.2.2.2
                                      linarith only [h1595, hlam, p1601_0]
                                    · have p1601_0 := h1601c.1
                                      have p1601_1 := h1601c.2.1
                                      have p1601_2 := h1601c.2.2.1
                                      have p1601_3 := h1601c.2.2.2
                                      linarith only [hlam, p1601_0]
                                  · linarith only [h1562, h1600, hc03, hlam, hphi, ht34, ht45, u5elo4]
                                · linarith only [h1595, h1596, h1598, h1599, hc35, hlam, hphi, u5elo1]
                              · linarith only [h1598, hc23, hlam, hphi, ht34, ht45, u5elo3]
                          · linarith only [h1595, hc14, hlam, hphi, ht45, u5elo4]
                        · linarith only [h1594, hc13, hlam, hphi, ht34, ht45, u5elo3]
                    · linarith only [h0, h1591, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
                  · linarith only [h0, h1556, h1560, h1589, h1590, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                · linarith only [h0, h1559, h1589, hlam]
              · linarith only [h1588, hc04, hlam, hphi, ht45, u5elo4]
          · linarith only [h1561, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
        · linarith only [h0, h1557, h1560, hlam]
      · linarith only [h0, h1556, h1559, hlam]
    · linarith only [h1558, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo1]
  · rcases m.htr 0 1 5 (by decide) (by decide) with h1652 | h1652
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1653 | h1653
      · rcases m.htr 0 2 4 (by decide) (by decide) with h1654 | h1654
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1655 | h1655
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1656 | h1656
            · linarith only [h1556, h1557, h1656, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1658 | h1658
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1659 | h1659
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1660 | h1660
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1661 | h1661
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1662 | h1662
                      · linarith only [h1556, h1557, h1656, h1660, h1662, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1664 | h1664
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1665 | h1665
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1666 | h1666
                            · linarith only [h1556, h1557, h1659, h1662, h1666, hlam]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1668 | h1668
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1669 | h1669
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1670 | h1670
                                  · rcases h1bigk with h1671c | h1671c | h1671c | h1671c | h1671c | h1671c | h1671c | h1671c | h1671c | h1671c | h1671c | h1671c | h1671c | h1671c | h1671c | h1671c | h1671c | h1671c | h1671c | h1671c | h1671c | h1671c | h1671c | h1671c | h1671c
                                    · have p1671_0 := h1671c.1
                                      have p1671_1 := h1671c.2.1
                                      have p1671_2 := h1671c.2.2.1
                                      have p1671_3 := h1671c.2.2.2
                                      linarith only [hlam, p1671_0]
                                    · have p1671_0 := h1671c.1
                                      have p1671_1 := h1671c.2.1
                                      have p1671_2 := h1671c.2.2.1
                                      have p1671_3 := h1671c.2.2.2
                                      linarith only [h0, hlam, p1671_0]
                                    · have p1671_0 := h1671c.1
                                      have p1671_1 := h1671c.2.1
                                      have p1671_2 := h1671c.2.2.1
                                      have p1671_3 := h1671c.2.2.2
                                      linarith only [h1557, h1662, hc13, hc34, hlam, hphi, p1671_1]
                                    · have p1671_0 := h1671c.1
                                      have p1671_1 := h1671c.2.1
                                      have p1671_2 := h1671c.2.2.1
                                      have p1671_3 := h1671c.2.2.2
                                      linarith only [h1557, hlam, p1671_0]
                                    · have p1671_0 := h1671c.1
                                      have p1671_1 := h1671c.2.1
                                      have p1671_2 := h1671c.2.2.1
                                      have p1671_3 := h1671c.2.2.2
                                      rcases p1671_3 (m.d 0 1) (by simp) with h1676 | h1676
                                      · rcases p1671_3 (m.d 1 2) (by simp) with h1677 | h1677
                                        · rcases p1671_3 (m.d 1 3) (by simp) with h1678 | h1678
                                          · linarith only [h1556, h1678, hlam]
                                          · linarith only [h1664, h1678, hlam]
                                        · linarith only [h1661, h1677, hlam]
                                      · linarith only [h1676, hlam, p1671_0]
                                    · have p1671_0 := h1671c.1
                                      have p1671_1 := h1671c.2.1
                                      have p1671_2 := h1671c.2.2.1
                                      have p1671_3 := h1671c.2.2.2
                                      linarith only [h1556, h1659, h1668, h1670, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1671_1]
                                    · have p1671_0 := h1671c.1
                                      have p1671_1 := h1671c.2.1
                                      have p1671_2 := h1671c.2.2.1
                                      have p1671_3 := h1671c.2.2.2
                                      linarith only [hlam, p1671_0]
                                    · have p1671_0 := h1671c.1
                                      have p1671_1 := h1671c.2.1
                                      have p1671_2 := h1671c.2.2.1
                                      have p1671_3 := h1671c.2.2.2
                                      rcases p1671_3 (m.d 0 1) (by simp) with h1685 | h1685
                                      · linarith only [h0, h1685, hlam]
                                      · linarith only [h1556, h1685, hlam]
                                    · have p1671_0 := h1671c.1
                                      have p1671_1 := h1671c.2.1
                                      have p1671_2 := h1671c.2.2.1
                                      have p1671_3 := h1671c.2.2.2
                                      linarith only [h1556, h1557, h1659, h1668, h1670, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1671_1]
                                    · have p1671_0 := h1671c.1
                                      have p1671_1 := h1671c.2.1
                                      have p1671_2 := h1671c.2.2.1
                                      have p1671_3 := h1671c.2.2.2
                                      rcases p1671_3 (m.d 0 1) (by simp) with h1689 | h1689
                                      · linarith only [h0, h1689, hlam]
                                      · linarith only [h1652, h1689, hlam]
                                    · have p1671_0 := h1671c.1
                                      have p1671_1 := h1671c.2.1
                                      have p1671_2 := h1671c.2.2.1
                                      have p1671_3 := h1671c.2.2.2
                                      linarith only [h1556, hlam, p1671_0]
                                    · have p1671_0 := h1671c.1
                                      have p1671_1 := h1671c.2.1
                                      have p1671_2 := h1671c.2.2.1
                                      have p1671_3 := h1671c.2.2.2
                                      linarith only [h1659, hlam, p1671_0]
                                    · have p1671_0 := h1671c.1
                                      have p1671_1 := h1671c.2.1
                                      have p1671_2 := h1671c.2.2.1
                                      have p1671_3 := h1671c.2.2.2
                                      linarith only [hlam, p1671_0]
                                    · have p1671_0 := h1671c.1
                                      have p1671_1 := h1671c.2.1
                                      have p1671_2 := h1671c.2.2.1
                                      have p1671_3 := h1671c.2.2.2
                                      linarith only [h1662, hlam, p1671_0]
                                    · have p1671_0 := h1671c.1
                                      have p1671_1 := h1671c.2.1
                                      have p1671_2 := h1671c.2.2.1
                                      have p1671_3 := h1671c.2.2.2
                                      linarith only [h1556, h1557, h1660, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b, p1671_1]
                                    · have p1671_0 := h1671c.1
                                      have p1671_1 := h1671c.2.1
                                      have p1671_2 := h1671c.2.2.1
                                      have p1671_3 := h1671c.2.2.2
                                      linarith only [h1556, h1659, h1660, h1668, h1670, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1671_1]
                                    · have p1671_0 := h1671c.1
                                      have p1671_1 := h1671c.2.1
                                      have p1671_2 := h1671c.2.2.1
                                      have p1671_3 := h1671c.2.2.2
                                      linarith only [h1660, hlam, p1671_0]
                                    · have p1671_0 := h1671c.1
                                      have p1671_1 := h1671c.2.1
                                      have p1671_2 := h1671c.2.2.1
                                      have p1671_3 := h1671c.2.2.2
                                      rcases p1671_3 (m.d 0 1) (by simp) with h1699 | h1699
                                      · linarith only [h1557, h1699, hlam]
                                      · linarith only [h1556, h1699, hlam]
                                    · have p1671_0 := h1671c.1
                                      have p1671_1 := h1671c.2.1
                                      have p1671_2 := h1671c.2.2.1
                                      have p1671_3 := h1671c.2.2.2
                                      linarith only [hlam, p1671_0]
                                    · have p1671_0 := h1671c.1
                                      have p1671_1 := h1671c.2.1
                                      have p1671_2 := h1671c.2.2.1
                                      have p1671_3 := h1671c.2.2.2
                                      rcases p1671_3 (m.d 0 1) (by simp) with h1703 | h1703
                                      · linarith only [h1557, h1703, hlam]
                                      · linarith only [h1652, h1703, hlam]
                                    · have p1671_0 := h1671c.1
                                      have p1671_1 := h1671c.2.1
                                      have p1671_2 := h1671c.2.2.1
                                      have p1671_3 := h1671c.2.2.2
                                      linarith only [h1652, hlam, p1671_0]
                                    · have p1671_0 := h1671c.1
                                      have p1671_1 := h1671c.2.1
                                      have p1671_2 := h1671c.2.2.1
                                      have p1671_3 := h1671c.2.2.2
                                      linarith only [h1661, hlam, p1671_0]
                                    · have p1671_0 := h1671c.1
                                      have p1671_1 := h1671c.2.1
                                      have p1671_2 := h1671c.2.2.1
                                      have p1671_3 := h1671c.2.2.2
                                      linarith only [h1664, hlam, p1671_0]
                                    · have p1671_0 := h1671c.1
                                      have p1671_1 := h1671c.2.1
                                      have p1671_2 := h1671c.2.2.1
                                      have p1671_3 := h1671c.2.2.2
                                      linarith only [h1665, hlam, p1671_0]
                                    · have p1671_0 := h1671c.1
                                      have p1671_1 := h1671c.2.1
                                      have p1671_2 := h1671c.2.2.1
                                      have p1671_3 := h1671c.2.2.2
                                      linarith only [hlam, p1671_0]
                                  · linarith only [h1670, hc34, hlam, hphi, ht45, u5elo4]
                                · linarith only [h1652, h1665, h1669, hc24, hlam, hphi, ht45, u5elo0]
                              · linarith only [h1668, hc23, hlam, hphi, ht34, ht45, u5elo3]
                          · linarith only [h1556, h1557, h1665, hc13, hc45, hlam, hphi, ht34]
                        · linarith only [h1659, h1664, hc23, hlam, hphi, ht34, ht45, u5elo3]
                    · linarith only [h1556, h1557, h1659, h1660, h1661, hc23, hlam, hphi, ht34, ht45, u5elo2]
                  · linarith only [h0, h1556, h1654, h1659, h1660, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                · linarith only [h0, h1653, h1659, hlam]
              · linarith only [h1556, h1557, h1658, hc13, hlam, hphi, ht34, ht45, u5elo4]
          · linarith only [h1655, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1721 | h1721
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1722 | h1722
            · linarith only [h0, h1556, h1654, h1722, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1724 | h1724
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1725 | h1725
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1726 | h1726
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1727 | h1727
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1728 | h1728
                      · linarith only [h0, h1556, h1654, h1722, h1726, h1728, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1730 | h1730
                        · linarith only [h0, h1556, h1654, h1726, h1730, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                        · linarith only [h1730, hc13, hlam, hphi, ht34, ht45, u5elo3]
                    · linarith only [h0, h1654, h1726, h1727, hc01, hc25, hlam, hphi, ht12]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1734 | h1734
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1735 | h1735
                      · linarith only [h0, h1556, h1722, h1726, h1735, hc04, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1737 | h1737
                        · linarith only [h0, h1556, h1726, h1737, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                        · linarith only [h1725, h1737, hc23, hlam, hphi, ht34, ht45, u5elo3]
                    · linarith only [h0, h1556, h1725, h1734, hc23, hlam, hphi, ht34, ht45, u5elo2]
                · linarith only [h0, h1556, h1653, h1725, hc02, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
              · linarith only [h1724, hc04, hlam, hphi, ht45, u5elo4]
          · linarith only [h1721, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
      · linarith only [h0, h1556, h1653, hlam]
    · linarith only [h1556, h1652, hc13, hlam, hphi, ht34, ht45, u5elo1]

set_option maxHeartbeats 6266000 in
set_option maxHeartbeats 6266000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_L_x1_x1_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1556 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1746 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
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
  have h1bigk := hb1.1
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h1747 | h1747
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1748 | h1748
    · rcases m.htr 0 2 4 (by decide) (by decide) with h1749 | h1749
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1750 | h1750
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1751 | h1751
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1752 | h1752
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1753 | h1753
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1754 | h1754
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1755 | h1755
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1756 | h1756
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1757 | h1757
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h1758 | h1758
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h1759 | h1759
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h1760 | h1760
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h1761 | h1761
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h1762 | h1762
                                · rcases h1bigk with h1763c | h1763c | h1763c | h1763c | h1763c | h1763c | h1763c | h1763c | h1763c | h1763c | h1763c | h1763c | h1763c | h1763c | h1763c | h1763c | h1763c | h1763c | h1763c | h1763c | h1763c | h1763c | h1763c | h1763c | h1763c
                                  · have p1763_0 := h1763c.1
                                    have p1763_1 := h1763c.2.1
                                    have p1763_2 := h1763c.2.2.1
                                    have p1763_3 := h1763c.2.2.2
                                    linarith only [hlam, p1763_0]
                                  · have p1763_0 := h1763c.1
                                    have p1763_1 := h1763c.2.1
                                    have p1763_2 := h1763c.2.2.1
                                    have p1763_3 := h1763c.2.2.2
                                    linarith only [h0, hlam, p1763_0]
                                  · have p1763_0 := h1763c.1
                                    have p1763_1 := h1763c.2.1
                                    have p1763_2 := h1763c.2.2.1
                                    have p1763_3 := h1763c.2.2.2
                                    linarith only [h1556, hlam, p1763_0]
                                  · have p1763_0 := h1763c.1
                                    have p1763_1 := h1763c.2.1
                                    have p1763_2 := h1763c.2.2.1
                                    have p1763_3 := h1763c.2.2.2
                                    linarith only [h1556, h1754, h1759, h1762, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p1763_1]
                                  · have p1763_0 := h1763c.1
                                    have p1763_1 := h1763c.2.1
                                    have p1763_2 := h1763c.2.2.1
                                    have p1763_3 := h1763c.2.2.2
                                    rcases p1763_3 (m.d 0 1) (by simp) with h1768 | h1768
                                    · rcases p1763_3 (m.d 1 2) (by simp) with h1769 | h1769
                                      · rcases p1763_3 (m.d 1 3) (by simp) with h1770 | h1770
                                        · rcases p1763_3 (m.d 1 4) (by simp) with h1771 | h1771
                                          · linarith only [h1746, h1771, hlam]
                                          · linarith only [h1758, h1771, hlam]
                                        · linarith only [h1757, h1770, hlam]
                                      · linarith only [h1755, h1769, hlam]
                                    · linarith only [h1768, hlam, p1763_0]
                                  · have p1763_0 := h1763c.1
                                    have p1763_1 := h1763c.2.1
                                    have p1763_2 := h1763c.2.2.1
                                    have p1763_3 := h1763c.2.2.2
                                    linarith only [h1746, h1754, h1759, h1762, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1763_1]
                                  · have p1763_0 := h1763c.1
                                    have p1763_1 := h1763c.2.1
                                    have p1763_2 := h1763c.2.2.1
                                    have p1763_3 := h1763c.2.2.2
                                    linarith only [hlam, p1763_0]
                                  · have p1763_0 := h1763c.1
                                    have p1763_1 := h1763c.2.1
                                    have p1763_2 := h1763c.2.2.1
                                    have p1763_3 := h1763c.2.2.2
                                    linarith only [h1556, hc01, hc12, hlam, hphi, p1763_1]
                                  · have p1763_0 := h1763c.1
                                    have p1763_1 := h1763c.2.1
                                    have p1763_2 := h1763c.2.2.1
                                    have p1763_3 := h1763c.2.2.2
                                    rcases p1763_3 (m.d 0 1) (by simp) with h1780 | h1780
                                    · linarith only [h0, h1780, hlam]
                                    · linarith only [h1746, h1780, hlam]
                                  · have p1763_0 := h1763c.1
                                    have p1763_1 := h1763c.2.1
                                    have p1763_2 := h1763c.2.2.1
                                    have p1763_3 := h1763c.2.2.2
                                    rcases p1763_3 (m.d 0 1) (by simp) with h1783 | h1783
                                    · linarith only [h0, h1783, hlam]
                                    · linarith only [h1747, h1783, hlam]
                                  · have p1763_0 := h1763c.1
                                    have p1763_1 := h1763c.2.1
                                    have p1763_2 := h1763c.2.2.1
                                    have p1763_3 := h1763c.2.2.2
                                    linarith only [h1746, h1753, h1754, h1759, h1762, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1763_1]
                                  · have p1763_0 := h1763c.1
                                    have p1763_1 := h1763c.2.1
                                    have p1763_2 := h1763c.2.2.1
                                    have p1763_3 := h1763c.2.2.2
                                    linarith only [h1753, hlam, p1763_0]
                                  · have p1763_0 := h1763c.1
                                    have p1763_1 := h1763c.2.1
                                    have p1763_2 := h1763c.2.2.1
                                    have p1763_3 := h1763c.2.2.2
                                    linarith only [hlam, p1763_0]
                                  · have p1763_0 := h1763c.1
                                    have p1763_1 := h1763c.2.1
                                    have p1763_2 := h1763c.2.2.1
                                    have p1763_3 := h1763c.2.2.2
                                    rcases p1763_3 (m.d 0 1) (by simp) with h1789 | h1789
                                    · linarith only [h1556, h1789, hlam]
                                    · linarith only [h1746, h1789, hlam]
                                  · have p1763_0 := h1763c.1
                                    have p1763_1 := h1763c.2.1
                                    have p1763_2 := h1763c.2.2.1
                                    have p1763_3 := h1763c.2.2.2
                                    rcases p1763_3 (m.d 0 1) (by simp) with h1792 | h1792
                                    · linarith only [h1556, h1792, hlam]
                                    · linarith only [h1747, h1792, hlam]
                                  · have p1763_0 := h1763c.1
                                    have p1763_1 := h1763c.2.1
                                    have p1763_2 := h1763c.2.2.1
                                    have p1763_3 := h1763c.2.2.2
                                    linarith only [h1746, hlam, p1763_0]
                                  · have p1763_0 := h1763c.1
                                    have p1763_1 := h1763c.2.1
                                    have p1763_2 := h1763c.2.2.1
                                    have p1763_3 := h1763c.2.2.2
                                    linarith only [h1754, hlam, p1763_0]
                                  · have p1763_0 := h1763c.1
                                    have p1763_1 := h1763c.2.1
                                    have p1763_2 := h1763c.2.2.1
                                    have p1763_3 := h1763c.2.2.2
                                    linarith only [h1756, hlam, p1763_1]
                                  · have p1763_0 := h1763c.1
                                    have p1763_1 := h1763c.2.1
                                    have p1763_2 := h1763c.2.2.1
                                    have p1763_3 := h1763c.2.2.2
                                    linarith only [hlam, p1763_0]
                                  · have p1763_0 := h1763c.1
                                    have p1763_1 := h1763c.2.1
                                    have p1763_2 := h1763c.2.2.1
                                    have p1763_3 := h1763c.2.2.2
                                    linarith only [h0, h1746, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b, p1763_1]
                                  · have p1763_0 := h1763c.1
                                    have p1763_1 := h1763c.2.1
                                    have p1763_2 := h1763c.2.2.1
                                    have p1763_3 := h1763c.2.2.2
                                    linarith only [h1747, hlam, p1763_0]
                                  · have p1763_0 := h1763c.1
                                    have p1763_1 := h1763c.2.1
                                    have p1763_2 := h1763c.2.2.1
                                    have p1763_3 := h1763c.2.2.2
                                    linarith only [h1755, hlam, p1763_0]
                                  · have p1763_0 := h1763c.1
                                    have p1763_1 := h1763c.2.1
                                    have p1763_2 := h1763c.2.2.1
                                    have p1763_3 := h1763c.2.2.2
                                    linarith only [h1757, hlam, p1763_0]
                                  · have p1763_0 := h1763c.1
                                    have p1763_1 := h1763c.2.1
                                    have p1763_2 := h1763c.2.2.1
                                    have p1763_3 := h1763c.2.2.2
                                    linarith only [h1758, hlam, p1763_0]
                                  · have p1763_0 := h1763c.1
                                    have p1763_1 := h1763c.2.1
                                    have p1763_2 := h1763c.2.2.1
                                    have p1763_3 := h1763c.2.2.2
                                    linarith only [hlam, p1763_0]
                                · linarith only [h1762, hc34, hlam, hphi, ht45, u5elo4]
                              · linarith only [h1747, h1758, h1761, hc24, hlam, hphi, ht45, u5elo0]
                            · linarith only [h1760, hc23, hlam, hphi, ht34, ht45, u5elo3]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h1808 | h1808
                            · linarith only [h1556, h1746, h1753, h1756, h1759, h1808, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                            · linarith only [h1808, hc23, hlam, hphi, ht34, ht45, u5elo3]
                        · linarith only [h1758, hc14, hlam, hphi, ht45, u5elo4]
                      · linarith only [h1556, h1757, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                    · linarith only [h1556, h1751, h1756, hlam]
                  · linarith only [h0, h1755, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
                · linarith only [h1556, h1746, h1749, h1753, h1754, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b]
              · linarith only [h0, h1748, h1753, hlam]
            · linarith only [h1752, hc04, hlam, hphi, ht45, u5elo4]
          · linarith only [h1556, h1746, h1751, hlam]
        · linarith only [h1750, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
      · linarith only [h1556, h1746, h1748, h1749, hlam]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h1821 | h1821
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1822 | h1822
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1823 | h1823
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1824 | h1824
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1825 | h1825
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1826 | h1826
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1827 | h1827
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1828 | h1828
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1829 | h1829
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h1830 | h1830
                        · linarith only [h0, h1746, h1748, h1825, h1830, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                        · linarith only [h1830, hc14, hlam, hphi, ht45, u5elo4]
                      · linarith only [h0, h1746, h1748, h1825, h1826, h1829, hc24, hlam, hphi, ht45, u5elo3]
                    · linarith only [h0, h1746, h1748, h1823, h1825, h1826, h1828, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
                  · linarith only [h0, h1746, h1748, h1825, h1826, h1827, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                · linarith only [h0, h1746, h1748, h1825, h1826, hc14, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1837 | h1837
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1838 | h1838
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1839 | h1839
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1840 | h1840
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h1841 | h1841
                        · linarith only [h0, h1746, h1825, h1841, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                        · linarith only [h1841, hc14, hlam, hphi, ht45, u5elo4]
                      · linarith only [h1556, h1840, hc03, hlam, hphi, ht34, ht45, u5elo3]
                    · linarith only [h0, h1746, h1823, h1825, h1837, h1839, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
                  · linarith only [h0, h1746, h1837, h1838, hc24, hlam, hphi, ht45, u5elo2]
                · linarith only [h0, h1821, h1837, hlam]
            · linarith only [h1824, hc04, hlam, hphi, ht45, u5elo4]
          · linarith only [h0, h1746, h1748, h1823, hlam]
        · linarith only [h0, h1746, h1822, hc14, hlam, hphi, ht45, u5elo2]
      · linarith only [h0, h1746, h1821, hlam]
  · linarith only [h1746, h1747, hc14, hlam, hphi, ht45, u5elo1]

end R2N4
