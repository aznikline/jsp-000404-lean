import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_5S4

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6310000 in
set_option maxHeartbeats 6310000 in
theorem r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s4 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
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
  have h0elo := hb0.1
  have h0emin := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  rcases m.htr 0 2 4 (by decide) (by decide) with h1304 | h1304
  · rcases m.htr 0 2 5 (by decide) (by decide) with h1305 | h1305
    · rcases m.htr 0 3 4 (by decide) (by decide) with h1306 | h1306
      · rcases m.htr 0 3 5 (by decide) (by decide) with h1307 | h1307
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1308 | h1308
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1309 | h1309
            · linarith only [h0, h1309, h4, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1311 | h1311
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1312 | h1312
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1313 | h1313
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1314 | h1314
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1315 | h1315
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1316 | h1316
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1317 | h1317
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1318 | h1318
                            · linarith only [h0, h1311, h1318, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                            · linarith only [h1, h1309, h1311, h1315, h1316, h1318, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                          · linarith only [h1307, h1317, h4, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                        · linarith only [h1306, h1316, h4, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1323 | h1323
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1324 | h1324
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1325 | h1325
                            · linarith only [h1311, h1315, h1325, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1327 | h1327
                              · linarith only [h1311, h1315, h1323, h1327, hlam]
                              · rcases h0bigk with h1329c | h1329c | h1329c | h1329c | h1329c | h1329c | h1329c | h1329c | h1329c | h1329c | h1329c | h1329c | h1329c | h1329c | h1329c | h1329c | h1329c | h1329c | h1329c | h1329c | h1329c | h1329c | h1329c | h1329c | h1329c
                                · have p1329_0 := h1329c.1
                                  have p1329_1 := h1329c.2.1
                                  have p1329_2 := h1329c.2.2.1
                                  have p1329_3 := h1329c.2.2.2
                                  linarith only [hlam, p1329_0]
                                · have p1329_0 := h1329c.1
                                  have p1329_1 := h1329c.2.1
                                  have p1329_2 := h1329c.2.2.1
                                  have p1329_3 := h1329c.2.2.2
                                  linarith only [h1304, h1308, h1311, h1315, h1323, hc34, hlam, hphi, ht0b, ht45, ht5b, p1329_1, u0elo0]
                                · have p1329_0 := h1329c.1
                                  have p1329_1 := h1329c.2.1
                                  have p1329_2 := h1329c.2.2.1
                                  have p1329_3 := h1329c.2.2.2
                                  linarith only [h1, h1309, h1312, h1323, h1325, hc34, hlam, hphi, ht0b, ht45, ht5b, p1329_1, u0elo0]
                                · have p1329_0 := h1329c.1
                                  have p1329_1 := h1329c.2.1
                                  have p1329_2 := h1329c.2.2.1
                                  have p1329_3 := h1329c.2.2.2
                                  linarith only [h1308, h1311, h1315, h1323, hc34, hlam, hphi, ht0b, ht45, ht5b, p1329_1, u0elo0]
                                · have p1329_0 := h1329c.1
                                  have p1329_1 := h1329c.2.1
                                  have p1329_2 := h1329c.2.2.1
                                  have p1329_3 := h1329c.2.2.2
                                  linarith only [h1308, h1311, h1315, h1323, hc34, hlam, hphi, ht0b, ht45, ht5b, p1329_1, u0elo0]
                                · have p1329_0 := h1329c.1
                                  have p1329_1 := h1329c.2.1
                                  have p1329_2 := h1329c.2.2.1
                                  have p1329_3 := h1329c.2.2.2
                                  linarith only [h0, hlam, p1329_0]
                                · have p1329_0 := h1329c.1
                                  have p1329_1 := h1329c.2.1
                                  have p1329_2 := h1329c.2.2.1
                                  have p1329_3 := h1329c.2.2.2
                                  linarith only [hlam, p1329_0]
                                · have p1329_0 := h1329c.1
                                  have p1329_1 := h1329c.2.1
                                  have p1329_2 := h1329c.2.2.1
                                  have p1329_3 := h1329c.2.2.2
                                  linarith only [h4, hlam, p1329_0]
                                · have p1329_0 := h1329c.1
                                  have p1329_1 := h1329c.2.1
                                  have p1329_2 := h1329c.2.2.1
                                  have p1329_3 := h1329c.2.2.2
                                  linarith only [h1308, h1311, h1315, h1323, hc34, hlam, hphi, ht0b, ht45, ht5b, p1329_1, u0elo1]
                                · have p1329_0 := h1329c.1
                                  have p1329_1 := h1329c.2.1
                                  have p1329_2 := h1329c.2.2.1
                                  have p1329_3 := h1329c.2.2.2
                                  linarith only [h1308, h1311, h1315, h1323, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1329_1]
                                · have p1329_0 := h1329c.1
                                  have p1329_1 := h1329c.2.1
                                  have p1329_2 := h1329c.2.2.1
                                  have p1329_3 := h1329c.2.2.2
                                  linarith only [h1, hlam, p1329_1]
                                · have p1329_0 := h1329c.1
                                  have p1329_1 := h1329c.2.1
                                  have p1329_2 := h1329c.2.2.1
                                  have p1329_3 := h1329c.2.2.2
                                  linarith only [h0, h1, h1312, h1323, h1325, hc34, hlam, hphi, ht0b, ht45, ht5b, p1329_1, u0elo0]
                                · have p1329_0 := h1329c.1
                                  have p1329_1 := h1329c.2.1
                                  have p1329_2 := h1329c.2.2.1
                                  have p1329_3 := h1329c.2.2.2
                                  linarith only [hlam, p1329_0]
                                · have p1329_0 := h1329c.1
                                  have p1329_1 := h1329c.2.1
                                  have p1329_2 := h1329c.2.2.1
                                  have p1329_3 := h1329c.2.2.2
                                  linarith only [h1, h1308, h1311, h1315, h1323, hc34, hlam, hphi, ht0b, ht45, ht5b, p1329_1, u0elo0]
                                · have p1329_0 := h1329c.1
                                  have p1329_1 := h1329c.2.1
                                  have p1329_2 := h1329c.2.2.1
                                  have p1329_3 := h1329c.2.2.2
                                  linarith only [h1, h1308, h1311, h1315, h1323, hc34, hlam, hphi, ht0b, ht45, ht5b, p1329_1, u0elo0]
                                · have p1329_0 := h1329c.1
                                  have p1329_1 := h1329c.2.1
                                  have p1329_2 := h1329c.2.2.1
                                  have p1329_3 := h1329c.2.2.2
                                  linarith only [h2, hlam, p1329_0]
                                · have p1329_0 := h1329c.1
                                  have p1329_1 := h1329c.2.1
                                  have p1329_2 := h1329c.2.2.1
                                  have p1329_3 := h1329c.2.2.2
                                  linarith only [h1304, hlam, p1329_0]
                                · have p1329_0 := h1329c.1
                                  have p1329_1 := h1329c.2.1
                                  have p1329_2 := h1329c.2.2.1
                                  have p1329_3 := h1329c.2.2.2
                                  linarith only [h1306, hlam, p1329_0]
                                · have p1329_0 := h1329c.1
                                  have p1329_1 := h1329c.2.1
                                  have p1329_2 := h1329c.2.2.1
                                  have p1329_3 := h1329c.2.2.2
                                  linarith only [hlam, p1329_0]
                                · have p1329_0 := h1329c.1
                                  have p1329_1 := h1329c.2.1
                                  have p1329_2 := h1329c.2.2.1
                                  have p1329_3 := h1329c.2.2.2
                                  linarith only [h1304, h1308, h1311, h1315, h1323, hc34, hlam, hphi, ht0b, ht45, ht5b, p1329_1, u0elo1]
                                · have p1329_0 := h1329c.1
                                  have p1329_1 := h1329c.2.1
                                  have p1329_2 := h1329c.2.2.1
                                  have p1329_3 := h1329c.2.2.2
                                  linarith only [h3, hlam, p1329_0]
                                · have p1329_0 := h1329c.1
                                  have p1329_1 := h1329c.2.1
                                  have p1329_2 := h1329c.2.2.1
                                  have p1329_3 := h1329c.2.2.2
                                  linarith only [h1305, hlam, p1329_1]
                                · have p1329_0 := h1329c.1
                                  have p1329_1 := h1329c.2.1
                                  have p1329_2 := h1329c.2.2.1
                                  have p1329_3 := h1329c.2.2.2
                                  linarith only [h1307, hlam, p1329_0]
                                · have p1329_0 := h1329c.1
                                  have p1329_1 := h1329c.2.1
                                  have p1329_2 := h1329c.2.2.1
                                  have p1329_3 := h1329c.2.2.2
                                  linarith only [h1308, hlam, p1329_1]
                                · have p1329_0 := h1329c.1
                                  have p1329_1 := h1329c.2.1
                                  have p1329_2 := h1329c.2.2.1
                                  have p1329_3 := h1329c.2.2.2
                                  linarith only [hlam, p1329_0]
                          · linarith only [h1307, h1324, h4, hlam]
                        · linarith only [h1304, h1308, h1311, h1315, h1323, h4, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                    · linarith only [h1307, h1309, h1311, h1314, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                  · linarith only [h1, h1306, h1309, h1311, h1313, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                · linarith only [h1305, h1311, h1312, h4, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
              · linarith only [h1304, h1311, h4, hc12, hc23, hlam, hphi]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1361 | h1361
            · linarith only [h0, h1361, h4, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1363 | h1363
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1364 | h1364
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1365 | h1365
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1366 | h1366
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1367 | h1367
                      · linarith only [h1308, h1367, h2, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1369 | h1369
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1370 | h1370
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1371 | h1371
                            · linarith only [h0, h1308, h1363, h1371, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1373 | h1373
                              · linarith only [h1308, h1363, h1369, h1373, h2, hlam]
                              · rcases h0bigk with h1375c | h1375c | h1375c | h1375c | h1375c | h1375c | h1375c | h1375c | h1375c | h1375c | h1375c | h1375c | h1375c | h1375c | h1375c | h1375c | h1375c | h1375c | h1375c | h1375c | h1375c | h1375c | h1375c | h1375c | h1375c
                                · have p1375_0 := h1375c.1
                                  have p1375_1 := h1375c.2.1
                                  have p1375_2 := h1375c.2.2.1
                                  have p1375_3 := h1375c.2.2.2
                                  linarith only [hlam, p1375_0]
                                · have p1375_0 := h1375c.1
                                  have p1375_1 := h1375c.2.1
                                  have p1375_2 := h1375c.2.2.1
                                  have p1375_3 := h1375c.2.2.2
                                  linarith only [h0, h1364, h1371, hc24, hlam, hphi, ht0b, ht45, ht5b, p1375_1, u0elo0]
                                · have p1375_0 := h1375c.1
                                  have p1375_1 := h1375c.2.1
                                  have p1375_2 := h1375c.2.2.1
                                  have p1375_3 := h1375c.2.2.2
                                  linarith only [h0, h1364, h1369, h1371, h4, hc34, hlam, hphi, ht0b, ht45, ht5b, p1375_1, u0elo0]
                                · have p1375_0 := h1375c.1
                                  have p1375_1 := h1375c.2.1
                                  have p1375_2 := h1375c.2.2.1
                                  have p1375_3 := h1375c.2.2.2
                                  rcases p1375_3 (m.d 0 1) (by simp) with h1379 | h1379
                                  · rcases p1375_3 (m.d 0 2) (by simp) with h1380 | h1380
                                    · linarith only [h0, h1380, hlam]
                                    · linarith only [h1304, h1380, hlam]
                                  · linarith only [h1379, h2, hlam]
                                · have p1375_0 := h1375c.1
                                  have p1375_1 := h1375c.2.1
                                  have p1375_2 := h1375c.2.2.1
                                  have p1375_3 := h1375c.2.2.2
                                  rcases p1375_3 (m.d 0 1) (by simp) with h1384 | h1384
                                  · rcases p1375_3 (m.d 0 2) (by simp) with h1385 | h1385
                                    · linarith only [h0, h1385, hlam]
                                    · linarith only [h1305, h1385, hlam]
                                  · linarith only [h1384, h3, hlam]
                                · have p1375_0 := h1375c.1
                                  have p1375_1 := h1375c.2.1
                                  have p1375_2 := h1375c.2.2.1
                                  have p1375_3 := h1375c.2.2.2
                                  linarith only [h0, hlam, p1375_0]
                                · have p1375_0 := h1375c.1
                                  have p1375_1 := h1375c.2.1
                                  have p1375_2 := h1375c.2.2.1
                                  have p1375_3 := h1375c.2.2.2
                                  linarith only [hlam, p1375_0]
                                · have p1375_0 := h1375c.1
                                  have p1375_1 := h1375c.2.1
                                  have p1375_2 := h1375c.2.2.1
                                  have p1375_3 := h1375c.2.2.2
                                  linarith only [h4, hlam, p1375_0]
                                · have p1375_0 := h1375c.1
                                  have p1375_1 := h1375c.2.1
                                  have p1375_2 := h1375c.2.2.1
                                  have p1375_3 := h1375c.2.2.2
                                  rcases p1375_3 (m.d 0 1) (by simp) with h1392 | h1392
                                  · rcases p1375_3 (m.d 0 2) (by simp) with h1393 | h1393
                                    · rcases p1375_3 (m.d 0 3) (by simp) with h1394 | h1394
                                      · rcases p1375_3 (m.d 0 4) (by simp) with h1395 | h1395
                                        · linarith only [h1304, h1395, hlam]
                                        · rcases p1375_3 (m.d 0 5) (by simp) with h1397 | h1397
                                          · linarith only [h1305, h1397, hlam]
                                          · linarith only [h1308, h1397, hlam]
                                      · linarith only [h1306, h1394, hlam]
                                    · linarith only [h1304, h1393, hlam]
                                  · linarith only [h1392, h2, hlam]
                                · have p1375_0 := h1375c.1
                                  have p1375_1 := h1375c.2.1
                                  have p1375_2 := h1375c.2.2.1
                                  have p1375_3 := h1375c.2.2.2
                                  rcases p1375_3 (m.d 0 1) (by simp) with h1403 | h1403
                                  · rcases p1375_3 (m.d 0 2) (by simp) with h1404 | h1404
                                    · rcases p1375_3 (m.d 0 3) (by simp) with h1405 | h1405
                                      · rcases p1375_3 (m.d 0 4) (by simp) with h1406 | h1406
                                        · linarith only [h1304, h1406, hlam]
                                        · rcases p1375_3 (m.d 0 5) (by simp) with h1408 | h1408
                                          · linarith only [h1305, h1408, hlam]
                                          · rcases h0emin with h1410 | h1410 | h1410 | h1410 | h1410
                                            · rcases h1bigk with h1411c | h1411c | h1411c | h1411c | h1411c | h1411c | h1411c | h1411c | h1411c | h1411c | h1411c | h1411c | h1411c | h1411c | h1411c | h1411c | h1411c | h1411c | h1411c | h1411c | h1411c | h1411c | h1411c | h1411c | h1411c
                                              · have p1411_0 := h1411c.1
                                                have p1411_1 := h1411c.2.1
                                                have p1411_2 := h1411c.2.2.1
                                                have p1411_3 := h1411c.2.2.2
                                                linarith only [hlam, p1411_0]
                                              · have p1411_0 := h1411c.1
                                                have p1411_1 := h1411c.2.1
                                                have p1411_2 := h1411c.2.2.1
                                                have p1411_3 := h1411c.2.2.2
                                                linarith only [h1364, h1369, h1371, hc34, hlam, hphi, ht0b, ht45, ht5b, p1411_1, u0elo0]
                                              · have p1411_0 := h1411c.1
                                                have p1411_1 := h1411c.2.1
                                                have p1411_2 := h1411c.2.2.1
                                                have p1411_3 := h1411c.2.2.2
                                                linarith only [h1361, h1364, h1369, h1371, hc34, hlam, hphi, ht0b, ht45, ht5b, p1411_1, u0elo0]
                                              · have p1411_0 := h1411c.1
                                                have p1411_1 := h1411c.2.1
                                                have p1411_2 := h1411c.2.2.1
                                                have p1411_3 := h1411c.2.2.2
                                                rcases p1411_3 (m.d 0 1) (by simp) with h1415 | h1415
                                                · rcases p1411_3 (m.d 1 2) (by simp) with h1416 | h1416
                                                  · linarith only [h0, h1416, hlam]
                                                  · linarith only [h1363, h1416, hlam]
                                                · linarith only [h1415, hlam, p1411_0]
                                              · have p1411_0 := h1411c.1
                                                have p1411_1 := h1411c.2.1
                                                have p1411_2 := h1411c.2.2.1
                                                have p1411_3 := h1411c.2.2.2
                                                rcases p1411_3 (m.d 0 1) (by simp) with h1420 | h1420
                                                · rcases p1411_3 (m.d 1 2) (by simp) with h1421 | h1421
                                                  · linarith only [h0, h1421, hlam]
                                                  · linarith only [h1364, h1421, hlam]
                                                · linarith only [h1420, hlam, p1411_0]
                                              · have p1411_0 := h1411c.1
                                                have p1411_1 := h1411c.2.1
                                                have p1411_2 := h1411c.2.2.1
                                                have p1411_3 := h1411c.2.2.2
                                                linarith only [h0, hlam, p1411_0]
                                              · have p1411_0 := h1411c.1
                                                have p1411_1 := h1411c.2.1
                                                have p1411_2 := h1411c.2.2.1
                                                have p1411_3 := h1411c.2.2.2
                                                linarith only [hlam, p1411_0]
                                              · have p1411_0 := h1411c.1
                                                have p1411_1 := h1411c.2.1
                                                have p1411_2 := h1411c.2.2.1
                                                have p1411_3 := h1411c.2.2.2
                                                linarith only [h1361, hlam, p1411_0]
                                              · have p1411_0 := h1411c.1
                                                have p1411_1 := h1411c.2.1
                                                have p1411_2 := h1411c.2.2.1
                                                have p1411_3 := h1411c.2.2.2
                                                linarith only [h0, h1363, h1369, hc34, hlam, hphi, ht0b, ht45, ht5b, p1411_1, u0elo0]
                                              · have p1411_0 := h1411c.1
                                                have p1411_1 := h1411c.2.1
                                                have p1411_2 := h1411c.2.2.1
                                                have p1411_3 := h1411c.2.2.2
                                                linarith only [h1, h1361, h1363, h1367, h1369, hc34, hlam, hphi, ht0b, ht45, ht5b, p1411_1, u0elo0]
                                              · have p1411_0 := h1411c.1
                                                have p1411_1 := h1411c.2.1
                                                have p1411_2 := h1411c.2.2.1
                                                have p1411_3 := h1411c.2.2.2
                                                linarith only [h1, hlam, p1411_0]
                                              · have p1411_0 := h1411c.1
                                                have p1411_1 := h1411c.2.1
                                                have p1411_2 := h1411c.2.2.1
                                                have p1411_3 := h1411c.2.2.2
                                                linarith only [h1, h1308, h1363, h1369, h2, h4, hc12, hc23, hc34, hlam, hphi, ht0b, ht45, ht5b, p1375_1, p1411_1, u0elo0]
                                              · have p1411_0 := h1411c.1
                                                have p1411_1 := h1411c.2.1
                                                have p1411_2 := h1411c.2.2.1
                                                have p1411_3 := h1411c.2.2.2
                                                linarith only [hlam, p1411_0]
                                              · have p1411_0 := h1411c.1
                                                have p1411_1 := h1411c.2.1
                                                have p1411_2 := h1411c.2.2.1
                                                have p1411_3 := h1411c.2.2.2
                                                linarith only [h1, h1363, h1369, hc34, hlam, hphi, ht0b, ht45, ht5b, p1411_1, u0elo0]
                                              · have p1411_0 := h1411c.1
                                                have p1411_1 := h1411c.2.1
                                                have p1411_2 := h1411c.2.2.1
                                                have p1411_3 := h1411c.2.2.2
                                                linarith only [h1, h1363, h1367, h1369, hc34, hlam, hphi, ht0b, ht45, ht5b, p1411_1, u0elo0]
                                              · have p1411_0 := h1411c.1
                                                have p1411_1 := h1411c.2.1
                                                have p1411_2 := h1411c.2.2.1
                                                have p1411_3 := h1411c.2.2.2
                                                linarith only [h2, hlam, p1411_0]
                                              · have p1411_0 := h1411c.1
                                                have p1411_1 := h1411c.2.1
                                                have p1411_2 := h1411c.2.2.1
                                                have p1411_3 := h1411c.2.2.2
                                                linarith only [h1363, hlam, p1411_1]
                                              · have p1411_0 := h1411c.1
                                                have p1411_1 := h1411c.2.1
                                                have p1411_2 := h1411c.2.2.1
                                                have p1411_3 := h1411c.2.2.2
                                                linarith only [h1365, hlam, p1411_0]
                                              · have p1411_0 := h1411c.1
                                                have p1411_1 := h1411c.2.1
                                                have p1411_2 := h1411c.2.2.1
                                                have p1411_3 := h1411c.2.2.2
                                                linarith only [hlam, p1411_0]
                                              · have p1411_0 := h1411c.1
                                                have p1411_1 := h1411c.2.1
                                                have p1411_2 := h1411c.2.2.1
                                                have p1411_3 := h1411c.2.2.2
                                                linarith only [h1367, hlam, p1411_1]
                                              · have p1411_0 := h1411c.1
                                                have p1411_1 := h1411c.2.1
                                                have p1411_2 := h1411c.2.2.1
                                                have p1411_3 := h1411c.2.2.2
                                                linarith only [h3, hlam, p1411_0]
                                              · have p1411_0 := h1411c.1
                                                have p1411_1 := h1411c.2.1
                                                have p1411_2 := h1411c.2.2.1
                                                have p1411_3 := h1411c.2.2.2
                                                linarith only [h1364, hlam, p1411_1]
                                              · have p1411_0 := h1411c.1
                                                have p1411_1 := h1411c.2.1
                                                have p1411_2 := h1411c.2.2.1
                                                have p1411_3 := h1411c.2.2.2
                                                linarith only [h1366, hlam, p1411_0]
                                              · have p1411_0 := h1411c.1
                                                have p1411_1 := h1411c.2.1
                                                have p1411_2 := h1411c.2.2.1
                                                have p1411_3 := h1411c.2.2.2
                                                linarith only [h1363, h1369, h3, hc34, hlam, hphi, ht0b, ht45, ht5b, p1411_1, u0elo0]
                                              · have p1411_0 := h1411c.1
                                                have p1411_1 := h1411c.2.1
                                                have p1411_2 := h1411c.2.2.1
                                                have p1411_3 := h1411c.2.2.2
                                                linarith only [hlam, p1411_0]
                                            · rcases h1bigk with h1445c | h1445c | h1445c | h1445c | h1445c | h1445c | h1445c | h1445c | h1445c | h1445c | h1445c | h1445c | h1445c | h1445c | h1445c | h1445c | h1445c | h1445c | h1445c | h1445c | h1445c | h1445c | h1445c | h1445c | h1445c
                                              · have p1445_0 := h1445c.1
                                                have p1445_1 := h1445c.2.1
                                                have p1445_2 := h1445c.2.2.1
                                                have p1445_3 := h1445c.2.2.2
                                                linarith only [hlam, p1445_0]
                                              · have p1445_0 := h1445c.1
                                                have p1445_1 := h1445c.2.1
                                                have p1445_2 := h1445c.2.2.1
                                                have p1445_3 := h1445c.2.2.2
                                                linarith only [h1364, h1369, h1371, hc34, hlam, hphi, ht0b, ht45, ht5b, p1445_1, u0elo0]
                                              · have p1445_0 := h1445c.1
                                                have p1445_1 := h1445c.2.1
                                                have p1445_2 := h1445c.2.2.1
                                                have p1445_3 := h1445c.2.2.2
                                                linarith only [h1361, h1364, h1369, h1371, hc34, hlam, hphi, ht0b, ht45, ht5b, p1445_1, u0elo0]
                                              · have p1445_0 := h1445c.1
                                                have p1445_1 := h1445c.2.1
                                                have p1445_2 := h1445c.2.2.1
                                                have p1445_3 := h1445c.2.2.2
                                                rcases p1445_3 (m.d 0 1) (by simp) with h1449 | h1449
                                                · rcases p1445_3 (m.d 1 2) (by simp) with h1450 | h1450
                                                  · linarith only [h0, h1450, hlam]
                                                  · linarith only [h1363, h1450, hlam]
                                                · linarith only [h1449, hlam, p1445_0]
                                              · have p1445_0 := h1445c.1
                                                have p1445_1 := h1445c.2.1
                                                have p1445_2 := h1445c.2.2.1
                                                have p1445_3 := h1445c.2.2.2
                                                rcases p1445_3 (m.d 0 1) (by simp) with h1454 | h1454
                                                · rcases p1445_3 (m.d 1 2) (by simp) with h1455 | h1455
                                                  · linarith only [h0, h1455, hlam]
                                                  · linarith only [h1364, h1455, hlam]
                                                · linarith only [h1454, hlam, p1445_0]
                                              · have p1445_0 := h1445c.1
                                                have p1445_1 := h1445c.2.1
                                                have p1445_2 := h1445c.2.2.1
                                                have p1445_3 := h1445c.2.2.2
                                                linarith only [h0, hlam, p1445_0]
                                              · have p1445_0 := h1445c.1
                                                have p1445_1 := h1445c.2.1
                                                have p1445_2 := h1445c.2.2.1
                                                have p1445_3 := h1445c.2.2.2
                                                linarith only [hlam, p1445_0]
                                              · have p1445_0 := h1445c.1
                                                have p1445_1 := h1445c.2.1
                                                have p1445_2 := h1445c.2.2.1
                                                have p1445_3 := h1445c.2.2.2
                                                linarith only [h1361, hlam, p1445_0]
                                              · have p1445_0 := h1445c.1
                                                have p1445_1 := h1445c.2.1
                                                have p1445_2 := h1445c.2.2.1
                                                have p1445_3 := h1445c.2.2.2
                                                linarith only [h0, h1363, h1369, hc34, hlam, hphi, ht0b, ht45, ht5b, p1445_1, u0elo0]
                                              · have p1445_0 := h1445c.1
                                                have p1445_1 := h1445c.2.1
                                                have p1445_2 := h1445c.2.2.1
                                                have p1445_3 := h1445c.2.2.2
                                                linarith only [h1, h1361, hc15, hlam, hphi, ht0b, ht5b, p1445_1, u0elo0]
                                              · have p1445_0 := h1445c.1
                                                have p1445_1 := h1445c.2.1
                                                have p1445_2 := h1445c.2.2.1
                                                have p1445_3 := h1445c.2.2.2
                                                linarith only [h1, hlam, p1445_0]
                                              · have p1445_0 := h1445c.1
                                                have p1445_1 := h1445c.2.1
                                                have p1445_2 := h1445c.2.2.1
                                                have p1445_3 := h1445c.2.2.2
                                                linarith only [h1, h1308, h1363, h1369, h2, h4, hc12, hc23, hc34, hlam, hphi, ht0b, ht45, ht5b, p1375_1, p1445_1, u0elo0]
                                              · have p1445_0 := h1445c.1
                                                have p1445_1 := h1445c.2.1
                                                have p1445_2 := h1445c.2.2.1
                                                have p1445_3 := h1445c.2.2.2
                                                linarith only [hlam, p1445_0]
                                              · have p1445_0 := h1445c.1
                                                have p1445_1 := h1445c.2.1
                                                have p1445_2 := h1445c.2.2.1
                                                have p1445_3 := h1445c.2.2.2
                                                linarith only [h1, h1363, h1369, hc34, hlam, hphi, ht0b, ht45, ht5b, p1445_1, u0elo0]
                                              · have p1445_0 := h1445c.1
                                                have p1445_1 := h1445c.2.1
                                                have p1445_2 := h1445c.2.2.1
                                                have p1445_3 := h1445c.2.2.2
                                                linarith only [h1, h1364, h1369, h1371, hc34, hlam, hphi, ht0b, ht45, ht5b, p1445_1, u0elo0]
                                              · have p1445_0 := h1445c.1
                                                have p1445_1 := h1445c.2.1
                                                have p1445_2 := h1445c.2.2.1
                                                have p1445_3 := h1445c.2.2.2
                                                linarith only [h2, hlam, p1445_0]
                                              · have p1445_0 := h1445c.1
                                                have p1445_1 := h1445c.2.1
                                                have p1445_2 := h1445c.2.2.1
                                                have p1445_3 := h1445c.2.2.2
                                                linarith only [h1363, hlam, p1445_1]
                                              · have p1445_0 := h1445c.1
                                                have p1445_1 := h1445c.2.1
                                                have p1445_2 := h1445c.2.2.1
                                                have p1445_3 := h1445c.2.2.2
                                                linarith only [h1365, hlam, p1445_0]
                                              · have p1445_0 := h1445c.1
                                                have p1445_1 := h1445c.2.1
                                                have p1445_2 := h1445c.2.2.1
                                                have p1445_3 := h1445c.2.2.2
                                                linarith only [hlam, p1445_0]
                                              · have p1445_0 := h1445c.1
                                                have p1445_1 := h1445c.2.1
                                                have p1445_2 := h1445c.2.2.1
                                                have p1445_3 := h1445c.2.2.2
                                                linarith only [h1367, hlam, p1445_1]
                                              · have p1445_0 := h1445c.1
                                                have p1445_1 := h1445c.2.1
                                                have p1445_2 := h1445c.2.2.1
                                                have p1445_3 := h1445c.2.2.2
                                                linarith only [h3, hlam, p1445_0]
                                              · have p1445_0 := h1445c.1
                                                have p1445_1 := h1445c.2.1
                                                have p1445_2 := h1445c.2.2.1
                                                have p1445_3 := h1445c.2.2.2
                                                linarith only [h1364, hlam, p1445_1]
                                              · have p1445_0 := h1445c.1
                                                have p1445_1 := h1445c.2.1
                                                have p1445_2 := h1445c.2.2.1
                                                have p1445_3 := h1445c.2.2.2
                                                linarith only [h1366, hlam, p1445_0]
                                              · have p1445_0 := h1445c.1
                                                have p1445_1 := h1445c.2.1
                                                have p1445_2 := h1445c.2.2.1
                                                have p1445_3 := h1445c.2.2.2
                                                linarith only [h1363, h1369, h3, hc34, hlam, hphi, ht0b, ht45, ht5b, p1445_1, u0elo0]
                                              · have p1445_0 := h1445c.1
                                                have p1445_1 := h1445c.2.1
                                                have p1445_2 := h1445c.2.2.1
                                                have p1445_3 := h1445c.2.2.2
                                                linarith only [hlam, p1445_0]
                                            · rcases h1bigk with h1479c | h1479c | h1479c | h1479c | h1479c | h1479c | h1479c | h1479c | h1479c | h1479c | h1479c | h1479c | h1479c | h1479c | h1479c | h1479c | h1479c | h1479c | h1479c | h1479c | h1479c | h1479c | h1479c | h1479c | h1479c
                                              · have p1479_0 := h1479c.1
                                                have p1479_1 := h1479c.2.1
                                                have p1479_2 := h1479c.2.2.1
                                                have p1479_3 := h1479c.2.2.2
                                                linarith only [hlam, p1479_0]
                                              · have p1479_0 := h1479c.1
                                                have p1479_1 := h1479c.2.1
                                                have p1479_2 := h1479c.2.2.1
                                                have p1479_3 := h1479c.2.2.2
                                                linarith only [h1364, h1369, h1371, hc34, hlam, hphi, ht0b, ht45, ht5b, p1479_1, u0elo0]
                                              · have p1479_0 := h1479c.1
                                                have p1479_1 := h1479c.2.1
                                                have p1479_2 := h1479c.2.2.1
                                                have p1479_3 := h1479c.2.2.2
                                                linarith only [h1361, h1364, h1369, h1371, hc34, hlam, hphi, ht0b, ht45, ht5b, p1479_1, u0elo0]
                                              · have p1479_0 := h1479c.1
                                                have p1479_1 := h1479c.2.1
                                                have p1479_2 := h1479c.2.2.1
                                                have p1479_3 := h1479c.2.2.2
                                                rcases p1479_3 (m.d 0 1) (by simp) with h1483 | h1483
                                                · rcases p1479_3 (m.d 1 2) (by simp) with h1484 | h1484
                                                  · linarith only [h0, h1484, hlam]
                                                  · linarith only [h1363, h1484, hlam]
                                                · linarith only [h1483, hlam, p1479_0]
                                              · have p1479_0 := h1479c.1
                                                have p1479_1 := h1479c.2.1
                                                have p1479_2 := h1479c.2.2.1
                                                have p1479_3 := h1479c.2.2.2
                                                rcases p1479_3 (m.d 0 1) (by simp) with h1488 | h1488
                                                · rcases p1479_3 (m.d 1 2) (by simp) with h1489 | h1489
                                                  · linarith only [h0, h1489, hlam]
                                                  · linarith only [h1364, h1489, hlam]
                                                · linarith only [h1488, hlam, p1479_0]
                                              · have p1479_0 := h1479c.1
                                                have p1479_1 := h1479c.2.1
                                                have p1479_2 := h1479c.2.2.1
                                                have p1479_3 := h1479c.2.2.2
                                                linarith only [h0, hlam, p1479_0]
                                              · have p1479_0 := h1479c.1
                                                have p1479_1 := h1479c.2.1
                                                have p1479_2 := h1479c.2.2.1
                                                have p1479_3 := h1479c.2.2.2
                                                linarith only [hlam, p1479_0]
                                              · have p1479_0 := h1479c.1
                                                have p1479_1 := h1479c.2.1
                                                have p1479_2 := h1479c.2.2.1
                                                have p1479_3 := h1479c.2.2.2
                                                linarith only [h1361, hlam, p1479_0]
                                              · have p1479_0 := h1479c.1
                                                have p1479_1 := h1479c.2.1
                                                have p1479_2 := h1479c.2.2.1
                                                have p1479_3 := h1479c.2.2.2
                                                linarith only [h0, h1363, h1369, hc34, hlam, hphi, ht0b, ht45, ht5b, p1479_1, u0elo0]
                                              · have p1479_0 := h1479c.1
                                                have p1479_1 := h1479c.2.1
                                                have p1479_2 := h1479c.2.2.1
                                                have p1479_3 := h1479c.2.2.2
                                                linarith only [h1, h1361, hc15, hlam, hphi, ht0b, ht5b, p1479_1, u0elo0]
                                              · have p1479_0 := h1479c.1
                                                have p1479_1 := h1479c.2.1
                                                have p1479_2 := h1479c.2.2.1
                                                have p1479_3 := h1479c.2.2.2
                                                linarith only [h1, hlam, p1479_0]
                                              · have p1479_0 := h1479c.1
                                                have p1479_1 := h1479c.2.1
                                                have p1479_2 := h1479c.2.2.1
                                                have p1479_3 := h1479c.2.2.2
                                                linarith only [h1, h1308, h1363, h1369, h2, h4, hc12, hc23, hc34, hlam, hphi, ht0b, ht45, ht5b, p1375_1, p1479_1, u0elo0]
                                              · have p1479_0 := h1479c.1
                                                have p1479_1 := h1479c.2.1
                                                have p1479_2 := h1479c.2.2.1
                                                have p1479_3 := h1479c.2.2.2
                                                linarith only [hlam, p1479_0]
                                              · have p1479_0 := h1479c.1
                                                have p1479_1 := h1479c.2.1
                                                have p1479_2 := h1479c.2.2.1
                                                have p1479_3 := h1479c.2.2.2
                                                linarith only [h1, h1363, h1369, hc34, hlam, hphi, ht0b, ht45, ht5b, p1479_1, u0elo0]
                                              · have p1479_0 := h1479c.1
                                                have p1479_1 := h1479c.2.1
                                                have p1479_2 := h1479c.2.2.1
                                                have p1479_3 := h1479c.2.2.2
                                                linarith only [h1, h1364, h1369, h1371, hc34, hlam, hphi, ht0b, ht45, ht5b, p1479_1, u0elo0]
                                              · have p1479_0 := h1479c.1
                                                have p1479_1 := h1479c.2.1
                                                have p1479_2 := h1479c.2.2.1
                                                have p1479_3 := h1479c.2.2.2
                                                linarith only [h2, hlam, p1479_0]
                                              · have p1479_0 := h1479c.1
                                                have p1479_1 := h1479c.2.1
                                                have p1479_2 := h1479c.2.2.1
                                                have p1479_3 := h1479c.2.2.2
                                                linarith only [h1363, hlam, p1479_1]
                                              · have p1479_0 := h1479c.1
                                                have p1479_1 := h1479c.2.1
                                                have p1479_2 := h1479c.2.2.1
                                                have p1479_3 := h1479c.2.2.2
                                                linarith only [h1365, hlam, p1479_0]
                                              · have p1479_0 := h1479c.1
                                                have p1479_1 := h1479c.2.1
                                                have p1479_2 := h1479c.2.2.1
                                                have p1479_3 := h1479c.2.2.2
                                                linarith only [hlam, p1479_0]
                                              · have p1479_0 := h1479c.1
                                                have p1479_1 := h1479c.2.1
                                                have p1479_2 := h1479c.2.2.1
                                                have p1479_3 := h1479c.2.2.2
                                                linarith only [h1367, hlam, p1479_1]
                                              · have p1479_0 := h1479c.1
                                                have p1479_1 := h1479c.2.1
                                                have p1479_2 := h1479c.2.2.1
                                                have p1479_3 := h1479c.2.2.2
                                                linarith only [h3, hlam, p1479_0]
                                              · have p1479_0 := h1479c.1
                                                have p1479_1 := h1479c.2.1
                                                have p1479_2 := h1479c.2.2.1
                                                have p1479_3 := h1479c.2.2.2
                                                linarith only [h1364, hlam, p1479_1]
                                              · have p1479_0 := h1479c.1
                                                have p1479_1 := h1479c.2.1
                                                have p1479_2 := h1479c.2.2.1
                                                have p1479_3 := h1479c.2.2.2
                                                linarith only [h1366, hlam, p1479_0]
                                              · have p1479_0 := h1479c.1
                                                have p1479_1 := h1479c.2.1
                                                have p1479_2 := h1479c.2.2.1
                                                have p1479_3 := h1479c.2.2.2
                                                linarith only [h1363, h1369, h3, hc34, hlam, hphi, ht0b, ht45, ht5b, p1479_1, u0elo0]
                                              · have p1479_0 := h1479c.1
                                                have p1479_1 := h1479c.2.1
                                                have p1479_2 := h1479c.2.2.1
                                                have p1479_3 := h1479c.2.2.2
                                                linarith only [hlam, p1479_0]
                                            · linarith only [h1308, h1410, h4, hc23, hlam, ht01, ht12, p1375_1]
                                            · linarith only [h1410, h4, hc23, hlam, ht01, ht12, p1375_1]
                                      · linarith only [h1307, h1405, hlam]
                                    · linarith only [h1305, h1404, hlam]
                                  · linarith only [h1403, h3, hlam]
                                · have p1375_0 := h1375c.1
                                  have p1375_1 := h1375c.2.1
                                  have p1375_2 := h1375c.2.2.1
                                  have p1375_3 := h1375c.2.2.2
                                  linarith only [h1, hlam, p1375_1]
                                · have p1375_0 := h1375c.1
                                  have p1375_1 := h1375c.2.1
                                  have p1375_2 := h1375c.2.2.1
                                  have p1375_3 := h1375c.2.2.2
                                  linarith only [h0, h1364, h1369, h1371, hc34, hlam, hphi, ht0b, ht45, ht5b, p1375_1, u0elo2]
                                · have p1375_0 := h1375c.1
                                  have p1375_1 := h1375c.2.1
                                  have p1375_2 := h1375c.2.2.1
                                  have p1375_3 := h1375c.2.2.2
                                  linarith only [hlam, p1375_0]
                                · have p1375_0 := h1375c.1
                                  have p1375_1 := h1375c.2.1
                                  have p1375_2 := h1375c.2.2.1
                                  have p1375_3 := h1375c.2.2.2
                                  rcases p1375_3 (m.d 0 1) (by simp) with h1521 | h1521
                                  · rcases p1375_3 (m.d 0 2) (by simp) with h1522 | h1522
                                    · linarith only [h1522, h4, hlam]
                                    · linarith only [h1304, h1522, hlam]
                                  · linarith only [h1521, h2, hlam]
                                · have p1375_0 := h1375c.1
                                  have p1375_1 := h1375c.2.1
                                  have p1375_2 := h1375c.2.2.1
                                  have p1375_3 := h1375c.2.2.2
                                  rcases p1375_3 (m.d 0 1) (by simp) with h1526 | h1526
                                  · rcases p1375_3 (m.d 0 2) (by simp) with h1527 | h1527
                                    · linarith only [h1527, h4, hlam]
                                    · linarith only [h1305, h1527, hlam]
                                  · linarith only [h1526, h3, hlam]
                                · have p1375_0 := h1375c.1
                                  have p1375_1 := h1375c.2.1
                                  have p1375_2 := h1375c.2.2.1
                                  have p1375_3 := h1375c.2.2.2
                                  linarith only [h2, hlam, p1375_0]
                                · have p1375_0 := h1375c.1
                                  have p1375_1 := h1375c.2.1
                                  have p1375_2 := h1375c.2.2.1
                                  have p1375_3 := h1375c.2.2.2
                                  linarith only [h1304, hlam, p1375_0]
                                · have p1375_0 := h1375c.1
                                  have p1375_1 := h1375c.2.1
                                  have p1375_2 := h1375c.2.2.1
                                  have p1375_3 := h1375c.2.2.2
                                  linarith only [h1306, hlam, p1375_0]
                                · have p1375_0 := h1375c.1
                                  have p1375_1 := h1375c.2.1
                                  have p1375_2 := h1375c.2.2.1
                                  have p1375_3 := h1375c.2.2.2
                                  linarith only [hlam, p1375_0]
                                · have p1375_0 := h1375c.1
                                  have p1375_1 := h1375c.2.1
                                  have p1375_2 := h1375c.2.2.1
                                  have p1375_3 := h1375c.2.2.2
                                  linarith only [h1308, hlam, p1375_0]
                                · have p1375_0 := h1375c.1
                                  have p1375_1 := h1375c.2.1
                                  have p1375_2 := h1375c.2.2.1
                                  have p1375_3 := h1375c.2.2.2
                                  linarith only [h3, hlam, p1375_0]
                                · have p1375_0 := h1375c.1
                                  have p1375_1 := h1375c.2.1
                                  have p1375_2 := h1375c.2.2.1
                                  have p1375_3 := h1375c.2.2.2
                                  linarith only [h1305, hlam, p1375_1]
                                · have p1375_0 := h1375c.1
                                  have p1375_1 := h1375c.2.1
                                  have p1375_2 := h1375c.2.2.1
                                  have p1375_3 := h1375c.2.2.2
                                  linarith only [h1307, hlam, p1375_0]
                                · have p1375_0 := h1375c.1
                                  have p1375_1 := h1375c.2.1
                                  have p1375_2 := h1375c.2.2.1
                                  have p1375_3 := h1375c.2.2.2
                                  rcases p1375_3 (m.d 0 1) (by simp) with h1539 | h1539
                                  · rcases p1375_3 (m.d 0 2) (by simp) with h1540 | h1540
                                    · rcases p1375_3 (m.d 0 3) (by simp) with h1541 | h1541
                                      · rcases p1375_3 (m.d 0 4) (by simp) with h1542 | h1542
                                        · linarith only [h1308, h1542, hlam]
                                        · rcases p1375_3 (m.d 0 5) (by simp) with h1544 | h1544
                                          · rcases h0emin with h1545 | h1545 | h1545 | h1545 | h1545
                                            · rcases h1bigk with h1546c | h1546c | h1546c | h1546c | h1546c | h1546c | h1546c | h1546c | h1546c | h1546c | h1546c | h1546c | h1546c | h1546c | h1546c | h1546c | h1546c | h1546c | h1546c | h1546c | h1546c | h1546c | h1546c | h1546c | h1546c
                                              · have p1546_0 := h1546c.1
                                                have p1546_1 := h1546c.2.1
                                                have p1546_2 := h1546c.2.2.1
                                                have p1546_3 := h1546c.2.2.2
                                                linarith only [hlam, p1546_0]
                                              · have p1546_0 := h1546c.1
                                                have p1546_1 := h1546c.2.1
                                                have p1546_2 := h1546c.2.2.1
                                                have p1546_3 := h1546c.2.2.2
                                                linarith only [h1363, h1369, hc34, hlam, hphi, ht0b, ht45, ht5b, p1546_1, u0elo0]
                                              · have p1546_0 := h1546c.1
                                                have p1546_1 := h1546c.2.1
                                                have p1546_2 := h1546c.2.2.1
                                                have p1546_3 := h1546c.2.2.2
                                                linarith only [h1361, h1363, h1369, hc34, hlam, hphi, ht0b, ht45, ht5b, p1546_1, u0elo0]
                                              · have p1546_0 := h1546c.1
                                                have p1546_1 := h1546c.2.1
                                                have p1546_2 := h1546c.2.2.1
                                                have p1546_3 := h1546c.2.2.2
                                                rcases p1546_3 (m.d 0 1) (by simp) with h1550 | h1550
                                                · rcases p1546_3 (m.d 1 2) (by simp) with h1551 | h1551
                                                  · linarith only [h0, h1551, hlam]
                                                  · linarith only [h1363, h1551, hlam]
                                                · linarith only [h1550, hlam, p1546_0]
                                              · have p1546_0 := h1546c.1
                                                have p1546_1 := h1546c.2.1
                                                have p1546_2 := h1546c.2.2.1
                                                have p1546_3 := h1546c.2.2.2
                                                rcases p1546_3 (m.d 0 1) (by simp) with h1555 | h1555
                                                · rcases p1546_3 (m.d 1 2) (by simp) with h1556 | h1556
                                                  · linarith only [h0, h1556, hlam]
                                                  · linarith only [h1364, h1556, hlam]
                                                · linarith only [h1555, hlam, p1546_0]
                                              · have p1546_0 := h1546c.1
                                                have p1546_1 := h1546c.2.1
                                                have p1546_2 := h1546c.2.2.1
                                                have p1546_3 := h1546c.2.2.2
                                                linarith only [h0, hlam, p1546_0]
                                              · have p1546_0 := h1546c.1
                                                have p1546_1 := h1546c.2.1
                                                have p1546_2 := h1546c.2.2.1
                                                have p1546_3 := h1546c.2.2.2
                                                linarith only [hlam, p1546_0]
                                              · have p1546_0 := h1546c.1
                                                have p1546_1 := h1546c.2.1
                                                have p1546_2 := h1546c.2.2.1
                                                have p1546_3 := h1546c.2.2.2
                                                linarith only [h1361, hlam, p1546_0]
                                              · have p1546_0 := h1546c.1
                                                have p1546_1 := h1546c.2.1
                                                have p1546_2 := h1546c.2.2.1
                                                have p1546_3 := h1546c.2.2.2
                                                linarith only [h0, h1363, h1369, hc34, hlam, hphi, ht0b, ht45, ht5b, p1546_1, u0elo0]
                                              · have p1546_0 := h1546c.1
                                                have p1546_1 := h1546c.2.1
                                                have p1546_2 := h1546c.2.2.1
                                                have p1546_3 := h1546c.2.2.2
                                                linarith only [h1, h1361, hc15, hlam, hphi, ht0b, ht5b, p1546_1, u0elo0]
                                              · have p1546_0 := h1546c.1
                                                have p1546_1 := h1546c.2.1
                                                have p1546_2 := h1546c.2.2.1
                                                have p1546_3 := h1546c.2.2.2
                                                linarith only [h1, hlam, p1546_0]
                                              · have p1546_0 := h1546c.1
                                                have p1546_1 := h1546c.2.1
                                                have p1546_2 := h1546c.2.2.1
                                                have p1546_3 := h1546c.2.2.2
                                                linarith only [h1, h1305, h1363, h1369, h2, h4, hc12, hc23, hc34, hlam, hphi, ht0b, ht45, ht5b, p1375_1, p1546_1, u0elo0]
                                              · have p1546_0 := h1546c.1
                                                have p1546_1 := h1546c.2.1
                                                have p1546_2 := h1546c.2.2.1
                                                have p1546_3 := h1546c.2.2.2
                                                linarith only [hlam, p1546_0]
                                              · have p1546_0 := h1546c.1
                                                have p1546_1 := h1546c.2.1
                                                have p1546_2 := h1546c.2.2.1
                                                have p1546_3 := h1546c.2.2.2
                                                linarith only [h1, h1363, h1369, hc34, hlam, hphi, ht0b, ht45, ht5b, p1546_1, u0elo0]
                                              · have p1546_0 := h1546c.1
                                                have p1546_1 := h1546c.2.1
                                                have p1546_2 := h1546c.2.2.1
                                                have p1546_3 := h1546c.2.2.2
                                                linarith only [h1, h1364, h1369, h1371, hc34, hlam, hphi, ht0b, ht45, ht5b, p1546_1, u0elo0]
                                              · have p1546_0 := h1546c.1
                                                have p1546_1 := h1546c.2.1
                                                have p1546_2 := h1546c.2.2.1
                                                have p1546_3 := h1546c.2.2.2
                                                linarith only [h2, hlam, p1546_0]
                                              · have p1546_0 := h1546c.1
                                                have p1546_1 := h1546c.2.1
                                                have p1546_2 := h1546c.2.2.1
                                                have p1546_3 := h1546c.2.2.2
                                                linarith only [h1363, hlam, p1546_1]
                                              · have p1546_0 := h1546c.1
                                                have p1546_1 := h1546c.2.1
                                                have p1546_2 := h1546c.2.2.1
                                                have p1546_3 := h1546c.2.2.2
                                                linarith only [h1365, hlam, p1546_0]
                                              · have p1546_0 := h1546c.1
                                                have p1546_1 := h1546c.2.1
                                                have p1546_2 := h1546c.2.2.1
                                                have p1546_3 := h1546c.2.2.2
                                                linarith only [hlam, p1546_0]
                                              · have p1546_0 := h1546c.1
                                                have p1546_1 := h1546c.2.1
                                                have p1546_2 := h1546c.2.2.1
                                                have p1546_3 := h1546c.2.2.2
                                                linarith only [h1367, hlam, p1546_1]
                                              · have p1546_0 := h1546c.1
                                                have p1546_1 := h1546c.2.1
                                                have p1546_2 := h1546c.2.2.1
                                                have p1546_3 := h1546c.2.2.2
                                                linarith only [h3, hlam, p1546_0]
                                              · have p1546_0 := h1546c.1
                                                have p1546_1 := h1546c.2.1
                                                have p1546_2 := h1546c.2.2.1
                                                have p1546_3 := h1546c.2.2.2
                                                linarith only [h1364, hlam, p1546_1]
                                              · have p1546_0 := h1546c.1
                                                have p1546_1 := h1546c.2.1
                                                have p1546_2 := h1546c.2.2.1
                                                have p1546_3 := h1546c.2.2.2
                                                linarith only [h1366, hlam, p1546_0]
                                              · have p1546_0 := h1546c.1
                                                have p1546_1 := h1546c.2.1
                                                have p1546_2 := h1546c.2.2.1
                                                have p1546_3 := h1546c.2.2.2
                                                linarith only [h1363, h1369, h3, hc34, hlam, hphi, ht0b, ht45, ht5b, p1546_1, u0elo0]
                                              · have p1546_0 := h1546c.1
                                                have p1546_1 := h1546c.2.1
                                                have p1546_2 := h1546c.2.2.1
                                                have p1546_3 := h1546c.2.2.2
                                                linarith only [hlam, p1546_0]
                                            · rcases h1bigk with h1580c | h1580c | h1580c | h1580c | h1580c | h1580c | h1580c | h1580c | h1580c | h1580c | h1580c | h1580c | h1580c | h1580c | h1580c | h1580c | h1580c | h1580c | h1580c | h1580c | h1580c | h1580c | h1580c | h1580c | h1580c
                                              · have p1580_0 := h1580c.1
                                                have p1580_1 := h1580c.2.1
                                                have p1580_2 := h1580c.2.2.1
                                                have p1580_3 := h1580c.2.2.2
                                                linarith only [hlam, p1580_0]
                                              · have p1580_0 := h1580c.1
                                                have p1580_1 := h1580c.2.1
                                                have p1580_2 := h1580c.2.2.1
                                                have p1580_3 := h1580c.2.2.2
                                                linarith only [h1363, h1369, hc34, hlam, hphi, ht0b, ht45, ht5b, p1580_1, u0elo0]
                                              · have p1580_0 := h1580c.1
                                                have p1580_1 := h1580c.2.1
                                                have p1580_2 := h1580c.2.2.1
                                                have p1580_3 := h1580c.2.2.2
                                                linarith only [h1361, h1363, h1369, hc34, hlam, hphi, ht0b, ht45, ht5b, p1580_1, u0elo0]
                                              · have p1580_0 := h1580c.1
                                                have p1580_1 := h1580c.2.1
                                                have p1580_2 := h1580c.2.2.1
                                                have p1580_3 := h1580c.2.2.2
                                                rcases p1580_3 (m.d 0 1) (by simp) with h1584 | h1584
                                                · rcases p1580_3 (m.d 1 2) (by simp) with h1585 | h1585
                                                  · linarith only [h0, h1585, hlam]
                                                  · linarith only [h1363, h1585, hlam]
                                                · linarith only [h1584, hlam, p1580_0]
                                              · have p1580_0 := h1580c.1
                                                have p1580_1 := h1580c.2.1
                                                have p1580_2 := h1580c.2.2.1
                                                have p1580_3 := h1580c.2.2.2
                                                rcases p1580_3 (m.d 0 1) (by simp) with h1589 | h1589
                                                · rcases p1580_3 (m.d 1 2) (by simp) with h1590 | h1590
                                                  · linarith only [h0, h1590, hlam]
                                                  · linarith only [h1364, h1590, hlam]
                                                · linarith only [h1589, hlam, p1580_0]
                                              · have p1580_0 := h1580c.1
                                                have p1580_1 := h1580c.2.1
                                                have p1580_2 := h1580c.2.2.1
                                                have p1580_3 := h1580c.2.2.2
                                                linarith only [h0, hlam, p1580_0]
                                              · have p1580_0 := h1580c.1
                                                have p1580_1 := h1580c.2.1
                                                have p1580_2 := h1580c.2.2.1
                                                have p1580_3 := h1580c.2.2.2
                                                linarith only [hlam, p1580_0]
                                              · have p1580_0 := h1580c.1
                                                have p1580_1 := h1580c.2.1
                                                have p1580_2 := h1580c.2.2.1
                                                have p1580_3 := h1580c.2.2.2
                                                linarith only [h1361, hlam, p1580_0]
                                              · have p1580_0 := h1580c.1
                                                have p1580_1 := h1580c.2.1
                                                have p1580_2 := h1580c.2.2.1
                                                have p1580_3 := h1580c.2.2.2
                                                linarith only [h0, h1363, h1369, hc34, hlam, hphi, ht0b, ht45, ht5b, p1580_1, u0elo0]
                                              · have p1580_0 := h1580c.1
                                                have p1580_1 := h1580c.2.1
                                                have p1580_2 := h1580c.2.2.1
                                                have p1580_3 := h1580c.2.2.2
                                                linarith only [h1, h1361, hc15, hlam, hphi, ht0b, ht5b, p1580_1, u0elo0]
                                              · have p1580_0 := h1580c.1
                                                have p1580_1 := h1580c.2.1
                                                have p1580_2 := h1580c.2.2.1
                                                have p1580_3 := h1580c.2.2.2
                                                linarith only [h1, hlam, p1580_0]
                                              · have p1580_0 := h1580c.1
                                                have p1580_1 := h1580c.2.1
                                                have p1580_2 := h1580c.2.2.1
                                                have p1580_3 := h1580c.2.2.2
                                                linarith only [h1, h1305, h1363, h1369, h2, h4, hc12, hc23, hc34, hlam, hphi, ht0b, ht45, ht5b, p1375_1, p1580_1, u0elo0]
                                              · have p1580_0 := h1580c.1
                                                have p1580_1 := h1580c.2.1
                                                have p1580_2 := h1580c.2.2.1
                                                have p1580_3 := h1580c.2.2.2
                                                linarith only [hlam, p1580_0]
                                              · have p1580_0 := h1580c.1
                                                have p1580_1 := h1580c.2.1
                                                have p1580_2 := h1580c.2.2.1
                                                have p1580_3 := h1580c.2.2.2
                                                linarith only [h1, h1363, h1369, hc34, hlam, hphi, ht0b, ht45, ht5b, p1580_1, u0elo0]
                                              · have p1580_0 := h1580c.1
                                                have p1580_1 := h1580c.2.1
                                                have p1580_2 := h1580c.2.2.1
                                                have p1580_3 := h1580c.2.2.2
                                                linarith only [h1, h1364, h1369, h1371, hc34, hlam, hphi, ht0b, ht45, ht5b, p1580_1, u0elo0]
                                              · have p1580_0 := h1580c.1
                                                have p1580_1 := h1580c.2.1
                                                have p1580_2 := h1580c.2.2.1
                                                have p1580_3 := h1580c.2.2.2
                                                linarith only [h2, hlam, p1580_0]
                                              · have p1580_0 := h1580c.1
                                                have p1580_1 := h1580c.2.1
                                                have p1580_2 := h1580c.2.2.1
                                                have p1580_3 := h1580c.2.2.2
                                                linarith only [h1363, hlam, p1580_1]
                                              · have p1580_0 := h1580c.1
                                                have p1580_1 := h1580c.2.1
                                                have p1580_2 := h1580c.2.2.1
                                                have p1580_3 := h1580c.2.2.2
                                                linarith only [h1365, hlam, p1580_0]
                                              · have p1580_0 := h1580c.1
                                                have p1580_1 := h1580c.2.1
                                                have p1580_2 := h1580c.2.2.1
                                                have p1580_3 := h1580c.2.2.2
                                                linarith only [hlam, p1580_0]
                                              · have p1580_0 := h1580c.1
                                                have p1580_1 := h1580c.2.1
                                                have p1580_2 := h1580c.2.2.1
                                                have p1580_3 := h1580c.2.2.2
                                                linarith only [h1367, hlam, p1580_1]
                                              · have p1580_0 := h1580c.1
                                                have p1580_1 := h1580c.2.1
                                                have p1580_2 := h1580c.2.2.1
                                                have p1580_3 := h1580c.2.2.2
                                                linarith only [h3, hlam, p1580_0]
                                              · have p1580_0 := h1580c.1
                                                have p1580_1 := h1580c.2.1
                                                have p1580_2 := h1580c.2.2.1
                                                have p1580_3 := h1580c.2.2.2
                                                linarith only [h1364, hlam, p1580_1]
                                              · have p1580_0 := h1580c.1
                                                have p1580_1 := h1580c.2.1
                                                have p1580_2 := h1580c.2.2.1
                                                have p1580_3 := h1580c.2.2.2
                                                linarith only [h1366, hlam, p1580_0]
                                              · have p1580_0 := h1580c.1
                                                have p1580_1 := h1580c.2.1
                                                have p1580_2 := h1580c.2.2.1
                                                have p1580_3 := h1580c.2.2.2
                                                linarith only [h1363, h1369, h3, hc34, hlam, hphi, ht0b, ht45, ht5b, p1580_1, u0elo0]
                                              · have p1580_0 := h1580c.1
                                                have p1580_1 := h1580c.2.1
                                                have p1580_2 := h1580c.2.2.1
                                                have p1580_3 := h1580c.2.2.2
                                                linarith only [hlam, p1580_0]
                                            · rcases h1bigk with h1614c | h1614c | h1614c | h1614c | h1614c | h1614c | h1614c | h1614c | h1614c | h1614c | h1614c | h1614c | h1614c | h1614c | h1614c | h1614c | h1614c | h1614c | h1614c | h1614c | h1614c | h1614c | h1614c | h1614c | h1614c
                                              · have p1614_0 := h1614c.1
                                                have p1614_1 := h1614c.2.1
                                                have p1614_2 := h1614c.2.2.1
                                                have p1614_3 := h1614c.2.2.2
                                                linarith only [hlam, p1614_0]
                                              · have p1614_0 := h1614c.1
                                                have p1614_1 := h1614c.2.1
                                                have p1614_2 := h1614c.2.2.1
                                                have p1614_3 := h1614c.2.2.2
                                                linarith only [h1364, h1369, h1371, hc34, hlam, hphi, ht0b, ht45, ht5b, p1614_1, u0elo0]
                                              · have p1614_0 := h1614c.1
                                                have p1614_1 := h1614c.2.1
                                                have p1614_2 := h1614c.2.2.1
                                                have p1614_3 := h1614c.2.2.2
                                                linarith only [h1361, h1364, h1369, h1371, hc34, hlam, hphi, ht0b, ht45, ht5b, p1614_1, u0elo0]
                                              · have p1614_0 := h1614c.1
                                                have p1614_1 := h1614c.2.1
                                                have p1614_2 := h1614c.2.2.1
                                                have p1614_3 := h1614c.2.2.2
                                                rcases p1614_3 (m.d 0 1) (by simp) with h1618 | h1618
                                                · rcases p1614_3 (m.d 1 2) (by simp) with h1619 | h1619
                                                  · linarith only [h0, h1619, hlam]
                                                  · linarith only [h1363, h1619, hlam]
                                                · linarith only [h1618, hlam, p1614_0]
                                              · have p1614_0 := h1614c.1
                                                have p1614_1 := h1614c.2.1
                                                have p1614_2 := h1614c.2.2.1
                                                have p1614_3 := h1614c.2.2.2
                                                rcases p1614_3 (m.d 0 1) (by simp) with h1623 | h1623
                                                · rcases p1614_3 (m.d 1 2) (by simp) with h1624 | h1624
                                                  · linarith only [h0, h1624, hlam]
                                                  · linarith only [h1364, h1624, hlam]
                                                · linarith only [h1623, hlam, p1614_0]
                                              · have p1614_0 := h1614c.1
                                                have p1614_1 := h1614c.2.1
                                                have p1614_2 := h1614c.2.2.1
                                                have p1614_3 := h1614c.2.2.2
                                                linarith only [h0, hlam, p1614_0]
                                              · have p1614_0 := h1614c.1
                                                have p1614_1 := h1614c.2.1
                                                have p1614_2 := h1614c.2.2.1
                                                have p1614_3 := h1614c.2.2.2
                                                linarith only [hlam, p1614_0]
                                              · have p1614_0 := h1614c.1
                                                have p1614_1 := h1614c.2.1
                                                have p1614_2 := h1614c.2.2.1
                                                have p1614_3 := h1614c.2.2.2
                                                linarith only [h1361, hlam, p1614_0]
                                              · have p1614_0 := h1614c.1
                                                have p1614_1 := h1614c.2.1
                                                have p1614_2 := h1614c.2.2.1
                                                have p1614_3 := h1614c.2.2.2
                                                linarith only [h0, h1363, h1369, hc34, hlam, hphi, ht0b, ht45, ht5b, p1614_1, u0elo0]
                                              · have p1614_0 := h1614c.1
                                                have p1614_1 := h1614c.2.1
                                                have p1614_2 := h1614c.2.2.1
                                                have p1614_3 := h1614c.2.2.2
                                                linarith only [h1, h1361, hc15, hlam, hphi, ht0b, ht5b, p1614_1, u0elo0]
                                              · have p1614_0 := h1614c.1
                                                have p1614_1 := h1614c.2.1
                                                have p1614_2 := h1614c.2.2.1
                                                have p1614_3 := h1614c.2.2.2
                                                linarith only [h1, hlam, p1614_0]
                                              · have p1614_0 := h1614c.1
                                                have p1614_1 := h1614c.2.1
                                                have p1614_2 := h1614c.2.2.1
                                                have p1614_3 := h1614c.2.2.2
                                                linarith only [h1, h1305, h1363, h1369, h2, h4, hc12, hc23, hc34, hlam, hphi, ht0b, ht45, ht5b, p1375_1, p1614_1, u0elo0]
                                              · have p1614_0 := h1614c.1
                                                have p1614_1 := h1614c.2.1
                                                have p1614_2 := h1614c.2.2.1
                                                have p1614_3 := h1614c.2.2.2
                                                linarith only [hlam, p1614_0]
                                              · have p1614_0 := h1614c.1
                                                have p1614_1 := h1614c.2.1
                                                have p1614_2 := h1614c.2.2.1
                                                have p1614_3 := h1614c.2.2.2
                                                linarith only [h1, h1363, h1369, hc34, hlam, hphi, ht0b, ht45, ht5b, p1614_1, u0elo0]
                                              · have p1614_0 := h1614c.1
                                                have p1614_1 := h1614c.2.1
                                                have p1614_2 := h1614c.2.2.1
                                                have p1614_3 := h1614c.2.2.2
                                                linarith only [h1, h1364, h1369, h1371, hc34, hlam, hphi, ht0b, ht45, ht5b, p1614_1, u0elo0]
                                              · have p1614_0 := h1614c.1
                                                have p1614_1 := h1614c.2.1
                                                have p1614_2 := h1614c.2.2.1
                                                have p1614_3 := h1614c.2.2.2
                                                linarith only [h2, hlam, p1614_0]
                                              · have p1614_0 := h1614c.1
                                                have p1614_1 := h1614c.2.1
                                                have p1614_2 := h1614c.2.2.1
                                                have p1614_3 := h1614c.2.2.2
                                                linarith only [h1363, hlam, p1614_1]
                                              · have p1614_0 := h1614c.1
                                                have p1614_1 := h1614c.2.1
                                                have p1614_2 := h1614c.2.2.1
                                                have p1614_3 := h1614c.2.2.2
                                                linarith only [h1365, hlam, p1614_0]
                                              · have p1614_0 := h1614c.1
                                                have p1614_1 := h1614c.2.1
                                                have p1614_2 := h1614c.2.2.1
                                                have p1614_3 := h1614c.2.2.2
                                                linarith only [hlam, p1614_0]
                                              · have p1614_0 := h1614c.1
                                                have p1614_1 := h1614c.2.1
                                                have p1614_2 := h1614c.2.2.1
                                                have p1614_3 := h1614c.2.2.2
                                                linarith only [h1367, hlam, p1614_1]
                                              · have p1614_0 := h1614c.1
                                                have p1614_1 := h1614c.2.1
                                                have p1614_2 := h1614c.2.2.1
                                                have p1614_3 := h1614c.2.2.2
                                                linarith only [h3, hlam, p1614_0]
                                              · have p1614_0 := h1614c.1
                                                have p1614_1 := h1614c.2.1
                                                have p1614_2 := h1614c.2.2.1
                                                have p1614_3 := h1614c.2.2.2
                                                linarith only [h1364, hlam, p1614_1]
                                              · have p1614_0 := h1614c.1
                                                have p1614_1 := h1614c.2.1
                                                have p1614_2 := h1614c.2.2.1
                                                have p1614_3 := h1614c.2.2.2
                                                linarith only [h1366, hlam, p1614_0]
                                              · have p1614_0 := h1614c.1
                                                have p1614_1 := h1614c.2.1
                                                have p1614_2 := h1614c.2.2.1
                                                have p1614_3 := h1614c.2.2.2
                                                linarith only [h1363, h1369, h3, hc34, hlam, hphi, ht0b, ht45, ht5b, p1614_1, u0elo0]
                                              · have p1614_0 := h1614c.1
                                                have p1614_1 := h1614c.2.1
                                                have p1614_2 := h1614c.2.2.1
                                                have p1614_3 := h1614c.2.2.2
                                                linarith only [hlam, p1614_0]
                                            · linarith only [h1305, h1545, h4, hc23, hlam, ht01, ht12, p1375_1]
                                            · rcases h1bigk with h1649c | h1649c | h1649c | h1649c | h1649c | h1649c | h1649c | h1649c | h1649c | h1649c | h1649c | h1649c | h1649c | h1649c | h1649c | h1649c | h1649c | h1649c | h1649c | h1649c | h1649c | h1649c | h1649c | h1649c | h1649c
                                              · have p1649_0 := h1649c.1
                                                have p1649_1 := h1649c.2.1
                                                have p1649_2 := h1649c.2.2.1
                                                have p1649_3 := h1649c.2.2.2
                                                linarith only [hlam, p1649_0]
                                              · have p1649_0 := h1649c.1
                                                have p1649_1 := h1649c.2.1
                                                have p1649_2 := h1649c.2.2.1
                                                have p1649_3 := h1649c.2.2.2
                                                linarith only [h1364, h1369, h1371, hc34, hlam, hphi, ht0b, ht45, ht5b, p1649_1, u0elo0]
                                              · have p1649_0 := h1649c.1
                                                have p1649_1 := h1649c.2.1
                                                have p1649_2 := h1649c.2.2.1
                                                have p1649_3 := h1649c.2.2.2
                                                linarith only [h1361, h1364, h1369, h1371, hc34, hlam, hphi, ht0b, ht45, ht5b, p1649_1, u0elo0]
                                              · have p1649_0 := h1649c.1
                                                have p1649_1 := h1649c.2.1
                                                have p1649_2 := h1649c.2.2.1
                                                have p1649_3 := h1649c.2.2.2
                                                rcases p1649_3 (m.d 0 1) (by simp) with h1653 | h1653
                                                · rcases p1649_3 (m.d 1 2) (by simp) with h1654 | h1654
                                                  · linarith only [h0, h1654, hlam]
                                                  · linarith only [h1363, h1654, hlam]
                                                · linarith only [h1653, hlam, p1649_0]
                                              · have p1649_0 := h1649c.1
                                                have p1649_1 := h1649c.2.1
                                                have p1649_2 := h1649c.2.2.1
                                                have p1649_3 := h1649c.2.2.2
                                                rcases p1649_3 (m.d 0 1) (by simp) with h1658 | h1658
                                                · rcases p1649_3 (m.d 1 2) (by simp) with h1659 | h1659
                                                  · linarith only [h0, h1659, hlam]
                                                  · linarith only [h1364, h1659, hlam]
                                                · linarith only [h1658, hlam, p1649_0]
                                              · have p1649_0 := h1649c.1
                                                have p1649_1 := h1649c.2.1
                                                have p1649_2 := h1649c.2.2.1
                                                have p1649_3 := h1649c.2.2.2
                                                linarith only [h0, hlam, p1649_0]
                                              · have p1649_0 := h1649c.1
                                                have p1649_1 := h1649c.2.1
                                                have p1649_2 := h1649c.2.2.1
                                                have p1649_3 := h1649c.2.2.2
                                                linarith only [hlam, p1649_0]
                                              · have p1649_0 := h1649c.1
                                                have p1649_1 := h1649c.2.1
                                                have p1649_2 := h1649c.2.2.1
                                                have p1649_3 := h1649c.2.2.2
                                                linarith only [h1361, hlam, p1649_0]
                                              · have p1649_0 := h1649c.1
                                                have p1649_1 := h1649c.2.1
                                                have p1649_2 := h1649c.2.2.1
                                                have p1649_3 := h1649c.2.2.2
                                                linarith only [h0, h1363, h1369, hc34, hlam, hphi, ht0b, ht45, ht5b, p1649_1, u0elo0]
                                              · have p1649_0 := h1649c.1
                                                have p1649_1 := h1649c.2.1
                                                have p1649_2 := h1649c.2.2.1
                                                have p1649_3 := h1649c.2.2.2
                                                linarith only [h1, h1361, hc15, hlam, hphi, ht0b, ht5b, p1649_1, u0elo0]
                                              · have p1649_0 := h1649c.1
                                                have p1649_1 := h1649c.2.1
                                                have p1649_2 := h1649c.2.2.1
                                                have p1649_3 := h1649c.2.2.2
                                                linarith only [h1, hlam, p1649_0]
                                              · have p1649_0 := h1649c.1
                                                have p1649_1 := h1649c.2.1
                                                have p1649_2 := h1649c.2.2.1
                                                have p1649_3 := h1649c.2.2.2
                                                linarith only [h1, h1305, h1363, h1369, h2, h4, hc12, hc23, hc34, hlam, hphi, ht0b, ht45, ht5b, p1375_1, p1649_1, u0elo0]
                                              · have p1649_0 := h1649c.1
                                                have p1649_1 := h1649c.2.1
                                                have p1649_2 := h1649c.2.2.1
                                                have p1649_3 := h1649c.2.2.2
                                                linarith only [hlam, p1649_0]
                                              · have p1649_0 := h1649c.1
                                                have p1649_1 := h1649c.2.1
                                                have p1649_2 := h1649c.2.2.1
                                                have p1649_3 := h1649c.2.2.2
                                                linarith only [h1, h1363, h1369, hc34, hlam, hphi, ht0b, ht45, ht5b, p1649_1, u0elo0]
                                              · have p1649_0 := h1649c.1
                                                have p1649_1 := h1649c.2.1
                                                have p1649_2 := h1649c.2.2.1
                                                have p1649_3 := h1649c.2.2.2
                                                linarith only [h1, h1364, h1369, h1371, hc34, hlam, hphi, ht0b, ht45, ht5b, p1649_1, u0elo0]
                                              · have p1649_0 := h1649c.1
                                                have p1649_1 := h1649c.2.1
                                                have p1649_2 := h1649c.2.2.1
                                                have p1649_3 := h1649c.2.2.2
                                                linarith only [h2, hlam, p1649_0]
                                              · have p1649_0 := h1649c.1
                                                have p1649_1 := h1649c.2.1
                                                have p1649_2 := h1649c.2.2.1
                                                have p1649_3 := h1649c.2.2.2
                                                linarith only [h1363, hlam, p1649_1]
                                              · have p1649_0 := h1649c.1
                                                have p1649_1 := h1649c.2.1
                                                have p1649_2 := h1649c.2.2.1
                                                have p1649_3 := h1649c.2.2.2
                                                linarith only [h1365, hlam, p1649_0]
                                              · have p1649_0 := h1649c.1
                                                have p1649_1 := h1649c.2.1
                                                have p1649_2 := h1649c.2.2.1
                                                have p1649_3 := h1649c.2.2.2
                                                linarith only [hlam, p1649_0]
                                              · have p1649_0 := h1649c.1
                                                have p1649_1 := h1649c.2.1
                                                have p1649_2 := h1649c.2.2.1
                                                have p1649_3 := h1649c.2.2.2
                                                linarith only [h1367, hlam, p1649_1]
                                              · have p1649_0 := h1649c.1
                                                have p1649_1 := h1649c.2.1
                                                have p1649_2 := h1649c.2.2.1
                                                have p1649_3 := h1649c.2.2.2
                                                linarith only [h3, hlam, p1649_0]
                                              · have p1649_0 := h1649c.1
                                                have p1649_1 := h1649c.2.1
                                                have p1649_2 := h1649c.2.2.1
                                                have p1649_3 := h1649c.2.2.2
                                                linarith only [h1364, hlam, p1649_1]
                                              · have p1649_0 := h1649c.1
                                                have p1649_1 := h1649c.2.1
                                                have p1649_2 := h1649c.2.2.1
                                                have p1649_3 := h1649c.2.2.2
                                                linarith only [h1366, hlam, p1649_0]
                                              · have p1649_0 := h1649c.1
                                                have p1649_1 := h1649c.2.1
                                                have p1649_2 := h1649c.2.2.1
                                                have p1649_3 := h1649c.2.2.2
                                                linarith only [h1363, h1369, h3, hc34, hlam, hphi, ht0b, ht45, ht5b, p1649_1, u0elo0]
                                              · have p1649_0 := h1649c.1
                                                have p1649_1 := h1649c.2.1
                                                have p1649_2 := h1649c.2.2.1
                                                have p1649_3 := h1649c.2.2.2
                                                linarith only [hlam, p1649_0]
                                          · linarith only [h1308, h1544, hlam]
                                      · linarith only [h1306, h1541, hlam]
                                    · linarith only [h1304, h1540, hlam]
                                  · linarith only [h1539, h2, hlam]
                                · have p1375_0 := h1375c.1
                                  have p1375_1 := h1375c.2.1
                                  have p1375_2 := h1375c.2.2.1
                                  have p1375_3 := h1375c.2.2.2
                                  linarith only [hlam, p1375_0]
                          · linarith only [h1307, h1370, h4, hlam]
                        · linarith only [h1306, h1369, h4, hlam]
                    · linarith only [h1307, h1365, h1366, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                  · linarith only [h1, h1306, h1361, h1363, h1365, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                · linarith only [h1305, h1363, h1364, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
              · linarith only [h1304, h1363, h4, hc12, hc23, hlam, hphi]
        · linarith only [h1305, h1307, h4, hlam]
      · linarith only [h1304, h1306, h4, hlam]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h1696 | h1696
      · rcases m.htr 0 3 5 (by decide) (by decide) with h1697 | h1697
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1698 | h1698
          · linarith only [h1304, h1305, h1698, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1700 | h1700
            · linarith only [h0, h1700, h4, hlam]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1702 | h1702
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1703 | h1703
                · linarith only [h0, h1305, h1703, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1705 | h1705
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1706 | h1706
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1707 | h1707
                      · linarith only [h1698, h1707, h2, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1709 | h1709
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1710 | h1710
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1711 | h1711
                            · linarith only [h0, h1698, h1702, h1711, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1713 | h1713
                              · linarith only [h0, h1305, h1702, h1709, h1711, h1713, hlam]
                              · rcases h0bigk with h1715c | h1715c | h1715c | h1715c | h1715c | h1715c | h1715c | h1715c | h1715c | h1715c | h1715c | h1715c | h1715c | h1715c | h1715c | h1715c | h1715c | h1715c | h1715c | h1715c | h1715c | h1715c | h1715c | h1715c | h1715c
                                · have p1715_0 := h1715c.1
                                  have p1715_1 := h1715c.2.1
                                  have p1715_2 := h1715c.2.2.1
                                  have p1715_3 := h1715c.2.2.2
                                  linarith only [hlam, p1715_0]
                                · have p1715_0 := h1715c.1
                                  have p1715_1 := h1715c.2.1
                                  have p1715_2 := h1715c.2.2.1
                                  have p1715_3 := h1715c.2.2.2
                                  linarith only [h0, h1702, hc24, hlam, hphi, ht0b, ht45, ht5b, p1715_1, u0elo0]
                                · have p1715_0 := h1715c.1
                                  have p1715_1 := h1715c.2.1
                                  have p1715_2 := h1715c.2.2.1
                                  have p1715_3 := h1715c.2.2.2
                                  linarith only [h1, h1706, hc35, hlam, hphi, ht0b, ht5b, p1715_1, u0elo0]
                                · have p1715_0 := h1715c.1
                                  have p1715_1 := h1715c.2.1
                                  have p1715_2 := h1715c.2.2.1
                                  have p1715_3 := h1715c.2.2.2
                                  rcases p1715_3 (m.d 0 1) (by simp) with h1719 | h1719
                                  · rcases p1715_3 (m.d 0 2) (by simp) with h1720 | h1720
                                    · linarith only [h0, h1720, hlam]
                                    · linarith only [h1304, h1720, hlam]
                                  · linarith only [h1719, h2, hlam]
                                · have p1715_0 := h1715c.1
                                  have p1715_1 := h1715c.2.1
                                  have p1715_2 := h1715c.2.2.1
                                  have p1715_3 := h1715c.2.2.2
                                  linarith only [h0, h1305, h1702, h1709, hc34, hlam, hphi, ht0b, ht45, ht5b, p1715_1, u0elo0]
                                · have p1715_0 := h1715c.1
                                  have p1715_1 := h1715c.2.1
                                  have p1715_2 := h1715c.2.2.1
                                  have p1715_3 := h1715c.2.2.2
                                  linarith only [h0, hlam, p1715_0]
                                · have p1715_0 := h1715c.1
                                  have p1715_1 := h1715c.2.1
                                  have p1715_2 := h1715c.2.2.1
                                  have p1715_3 := h1715c.2.2.2
                                  linarith only [hlam, p1715_0]
                                · have p1715_0 := h1715c.1
                                  have p1715_1 := h1715c.2.1
                                  have p1715_2 := h1715c.2.2.1
                                  have p1715_3 := h1715c.2.2.2
                                  linarith only [h4, hlam, p1715_0]
                                · have p1715_0 := h1715c.1
                                  have p1715_1 := h1715c.2.1
                                  have p1715_2 := h1715c.2.2.1
                                  have p1715_3 := h1715c.2.2.2
                                  linarith only [h1305, h1702, h1709, h1711, h2, hc34, hc45, hlam, hphi, p1715_1]
                                · have p1715_0 := h1715c.1
                                  have p1715_1 := h1715c.2.1
                                  have p1715_2 := h1715c.2.2.1
                                  have p1715_3 := h1715c.2.2.2
                                  linarith only [h1305, hlam, p1715_0]
                                · have p1715_0 := h1715c.1
                                  have p1715_1 := h1715c.2.1
                                  have p1715_2 := h1715c.2.2.1
                                  have p1715_3 := h1715c.2.2.2
                                  linarith only [h1, hlam, p1715_1]
                                · have p1715_0 := h1715c.1
                                  have p1715_1 := h1715c.2.1
                                  have p1715_2 := h1715c.2.2.1
                                  have p1715_3 := h1715c.2.2.2
                                  linarith only [h0, h1702, h1709, hc34, hlam, hphi, ht0b, ht45, ht5b, p1715_1, u0elo2]
                                · have p1715_0 := h1715c.1
                                  have p1715_1 := h1715c.2.1
                                  have p1715_2 := h1715c.2.2.1
                                  have p1715_3 := h1715c.2.2.2
                                  linarith only [hlam, p1715_0]
                                · have p1715_0 := h1715c.1
                                  have p1715_1 := h1715c.2.1
                                  have p1715_2 := h1715c.2.2.1
                                  have p1715_3 := h1715c.2.2.2
                                  rcases p1715_3 (m.d 0 1) (by simp) with h1733 | h1733
                                  · rcases p1715_3 (m.d 0 2) (by simp) with h1734 | h1734
                                    · linarith only [h1734, h4, hlam]
                                    · linarith only [h1304, h1734, hlam]
                                  · linarith only [h1733, h2, hlam]
                                · have p1715_0 := h1715c.1
                                  have p1715_1 := h1715c.2.1
                                  have p1715_2 := h1715c.2.2.1
                                  have p1715_3 := h1715c.2.2.2
                                  linarith only [h0, h1, h1305, h1702, h1709, hc34, hlam, hphi, ht0b, ht45, ht5b, p1715_1, u0elo0]
                                · have p1715_0 := h1715c.1
                                  have p1715_1 := h1715c.2.1
                                  have p1715_2 := h1715c.2.2.1
                                  have p1715_3 := h1715c.2.2.2
                                  linarith only [h2, hlam, p1715_0]
                                · have p1715_0 := h1715c.1
                                  have p1715_1 := h1715c.2.1
                                  have p1715_2 := h1715c.2.2.1
                                  have p1715_3 := h1715c.2.2.2
                                  linarith only [h1304, hlam, p1715_0]
                                · have p1715_0 := h1715c.1
                                  have p1715_1 := h1715c.2.1
                                  have p1715_2 := h1715c.2.2.1
                                  have p1715_3 := h1715c.2.2.2
                                  linarith only [h1696, hlam, p1715_0]
                                · have p1715_0 := h1715c.1
                                  have p1715_1 := h1715c.2.1
                                  have p1715_2 := h1715c.2.2.1
                                  have p1715_3 := h1715c.2.2.2
                                  linarith only [hlam, p1715_0]
                                · have p1715_0 := h1715c.1
                                  have p1715_1 := h1715c.2.1
                                  have p1715_2 := h1715c.2.2.1
                                  have p1715_3 := h1715c.2.2.2
                                  linarith only [h1698, hlam, p1715_0]
                                · have p1715_0 := h1715c.1
                                  have p1715_1 := h1715c.2.1
                                  have p1715_2 := h1715c.2.2.1
                                  have p1715_3 := h1715c.2.2.2
                                  linarith only [h3, hlam, p1715_0]
                                · have p1715_0 := h1715c.1
                                  have p1715_1 := h1715c.2.1
                                  have p1715_2 := h1715c.2.2.1
                                  have p1715_3 := h1715c.2.2.2
                                  linarith only [h0, h1702, h1709, hc34, hlam, hphi, ht0b, ht45, ht5b, p1715_1, u0elo4]
                                · have p1715_0 := h1715c.1
                                  have p1715_1 := h1715c.2.1
                                  have p1715_2 := h1715c.2.2.1
                                  have p1715_3 := h1715c.2.2.2
                                  linarith only [h1697, hlam, p1715_0]
                                · have p1715_0 := h1715c.1
                                  have p1715_1 := h1715c.2.1
                                  have p1715_2 := h1715c.2.2.1
                                  have p1715_3 := h1715c.2.2.2
                                  rcases p1715_3 (m.d 0 1) (by simp) with h1747 | h1747
                                  · rcases p1715_3 (m.d 0 2) (by simp) with h1748 | h1748
                                    · linarith only [h1305, h1748, hlam]
                                    · linarith only [h1304, h1748, hlam]
                                  · linarith only [h1747, h2, hlam]
                                · have p1715_0 := h1715c.1
                                  have p1715_1 := h1715c.2.1
                                  have p1715_2 := h1715c.2.2.1
                                  have p1715_3 := h1715c.2.2.2
                                  linarith only [hlam, p1715_0]
                          · linarith only [h1697, h1710, h4, hlam]
                        · linarith only [h1696, h1709, h4, hlam]
                    · linarith only [h1, h1697, h1700, h1702, h1706, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                  · linarith only [h1, h1696, h1700, h1702, h1705, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
              · linarith only [h1304, h1702, h4, hc12, hc23, hlam, hphi]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1758 | h1758
          · linarith only [h1304, h1305, h1758, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1760 | h1760
            · linarith only [h0, h1760, h4, hlam]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1762 | h1762
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1763 | h1763
                · linarith only [h0, h1305, h1763, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1765 | h1765
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1766 | h1766
                    · linarith only [h1, h1697, h1766, h4, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1768 | h1768
                      · linarith only [h1758, h1768, h2, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1770 | h1770
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1771 | h1771
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1772 | h1772
                            · linarith only [h0, h1758, h1762, h1772, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1774 | h1774
                              · linarith only [h1697, h1762, h1770, h1771, h1772, h1774, h2, h4, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                              · rcases h0bigk with h1776c | h1776c | h1776c | h1776c | h1776c | h1776c | h1776c | h1776c | h1776c | h1776c | h1776c | h1776c | h1776c | h1776c | h1776c | h1776c | h1776c | h1776c | h1776c | h1776c | h1776c | h1776c | h1776c | h1776c | h1776c
                                · have p1776_0 := h1776c.1
                                  have p1776_1 := h1776c.2.1
                                  have p1776_2 := h1776c.2.2.1
                                  have p1776_3 := h1776c.2.2.2
                                  linarith only [hlam, p1776_0]
                                · have p1776_0 := h1776c.1
                                  have p1776_1 := h1776c.2.1
                                  have p1776_2 := h1776c.2.2.1
                                  have p1776_3 := h1776c.2.2.2
                                  linarith only [h0, h1762, h1770, hc34, hlam, hphi, ht0b, ht45, ht5b, p1776_1, u0elo0]
                                · have p1776_0 := h1776c.1
                                  have p1776_1 := h1776c.2.1
                                  have p1776_2 := h1776c.2.2.1
                                  have p1776_3 := h1776c.2.2.2
                                  linarith only [h0, h1762, h1770, h4, hc34, hlam, hphi, ht0b, ht45, ht5b, p1776_1, u0elo0]
                                · have p1776_0 := h1776c.1
                                  have p1776_1 := h1776c.2.1
                                  have p1776_2 := h1776c.2.2.1
                                  have p1776_3 := h1776c.2.2.2
                                  rcases p1776_3 (m.d 0 1) (by simp) with h1780 | h1780
                                  · rcases p1776_3 (m.d 0 2) (by simp) with h1781 | h1781
                                    · linarith only [h0, h1781, hlam]
                                    · linarith only [h1304, h1781, hlam]
                                  · linarith only [h1780, h2, hlam]
                                · have p1776_0 := h1776c.1
                                  have p1776_1 := h1776c.2.1
                                  have p1776_2 := h1776c.2.2.1
                                  have p1776_3 := h1776c.2.2.2
                                  linarith only [h0, h1305, h1762, h1770, hc34, hlam, hphi, ht0b, ht45, ht5b, p1776_1, u0elo0]
                                · have p1776_0 := h1776c.1
                                  have p1776_1 := h1776c.2.1
                                  have p1776_2 := h1776c.2.2.1
                                  have p1776_3 := h1776c.2.2.2
                                  linarith only [h0, hlam, p1776_0]
                                · have p1776_0 := h1776c.1
                                  have p1776_1 := h1776c.2.1
                                  have p1776_2 := h1776c.2.2.1
                                  have p1776_3 := h1776c.2.2.2
                                  linarith only [hlam, p1776_0]
                                · have p1776_0 := h1776c.1
                                  have p1776_1 := h1776c.2.1
                                  have p1776_2 := h1776c.2.2.1
                                  have p1776_3 := h1776c.2.2.2
                                  linarith only [h4, hlam, p1776_0]
                                · have p1776_0 := h1776c.1
                                  have p1776_1 := h1776c.2.1
                                  have p1776_2 := h1776c.2.2.1
                                  have p1776_3 := h1776c.2.2.2
                                  linarith only [h1697, h1771, h2, h4, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1776_1]
                                · have p1776_0 := h1776c.1
                                  have p1776_1 := h1776c.2.1
                                  have p1776_2 := h1776c.2.2.1
                                  have p1776_3 := h1776c.2.2.2
                                  linarith only [h1305, hlam, p1776_0]
                                · have p1776_0 := h1776c.1
                                  have p1776_1 := h1776c.2.1
                                  have p1776_2 := h1776c.2.2.1
                                  have p1776_3 := h1776c.2.2.2
                                  linarith only [h1, hlam, p1776_1]
                                · have p1776_0 := h1776c.1
                                  have p1776_1 := h1776c.2.1
                                  have p1776_2 := h1776c.2.2.1
                                  have p1776_3 := h1776c.2.2.2
                                  linarith only [h1697, h1771, hc02, hc23, hlam, hphi, p1776_1]
                                · have p1776_0 := h1776c.1
                                  have p1776_1 := h1776c.2.1
                                  have p1776_2 := h1776c.2.2.1
                                  have p1776_3 := h1776c.2.2.2
                                  linarith only [hlam, p1776_0]
                                · have p1776_0 := h1776c.1
                                  have p1776_1 := h1776c.2.1
                                  have p1776_2 := h1776c.2.2.1
                                  have p1776_3 := h1776c.2.2.2
                                  linarith only [h1304, h1697, h1770, h1771, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1776_1]
                                · have p1776_0 := h1776c.1
                                  have p1776_1 := h1776c.2.1
                                  have p1776_2 := h1776c.2.2.1
                                  have p1776_3 := h1776c.2.2.2
                                  linarith only [h1697, hlam, p1776_1]
                                · have p1776_0 := h1776c.1
                                  have p1776_1 := h1776c.2.1
                                  have p1776_2 := h1776c.2.2.1
                                  have p1776_3 := h1776c.2.2.2
                                  linarith only [h2, hlam, p1776_0]
                                · have p1776_0 := h1776c.1
                                  have p1776_1 := h1776c.2.1
                                  have p1776_2 := h1776c.2.2.1
                                  have p1776_3 := h1776c.2.2.2
                                  linarith only [h1304, hlam, p1776_0]
                                · have p1776_0 := h1776c.1
                                  have p1776_1 := h1776c.2.1
                                  have p1776_2 := h1776c.2.2.1
                                  have p1776_3 := h1776c.2.2.2
                                  linarith only [h1696, hlam, p1776_0]
                                · have p1776_0 := h1776c.1
                                  have p1776_1 := h1776c.2.1
                                  have p1776_2 := h1776c.2.2.1
                                  have p1776_3 := h1776c.2.2.2
                                  linarith only [hlam, p1776_0]
                                · have p1776_0 := h1776c.1
                                  have p1776_1 := h1776c.2.1
                                  have p1776_2 := h1776c.2.2.1
                                  have p1776_3 := h1776c.2.2.2
                                  linarith only [h1758, hlam, p1776_0]
                                · have p1776_0 := h1776c.1
                                  have p1776_1 := h1776c.2.1
                                  have p1776_2 := h1776c.2.2.1
                                  have p1776_3 := h1776c.2.2.2
                                  linarith only [h3, hlam, p1776_0]
                                · have p1776_0 := h1776c.1
                                  have p1776_1 := h1776c.2.1
                                  have p1776_2 := h1776c.2.2.1
                                  have p1776_3 := h1776c.2.2.2
                                  linarith only [h0, h1762, h1770, hc34, hlam, hphi, ht0b, ht45, ht5b, p1776_1, u0elo4]
                                · have p1776_0 := h1776c.1
                                  have p1776_1 := h1776c.2.1
                                  have p1776_2 := h1776c.2.2.1
                                  have p1776_3 := h1776c.2.2.2
                                  linarith only [h0, h1697, h1762, h1770, h1771, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1776_1]
                                · have p1776_0 := h1776c.1
                                  have p1776_1 := h1776c.2.1
                                  have p1776_2 := h1776c.2.2.1
                                  have p1776_3 := h1776c.2.2.2
                                  rcases p1776_3 (m.d 0 1) (by simp) with h1804 | h1804
                                  · rcases p1776_3 (m.d 0 2) (by simp) with h1805 | h1805
                                    · linarith only [h1305, h1805, hlam]
                                    · linarith only [h1304, h1805, hlam]
                                  · linarith only [h1804, h2, hlam]
                                · have p1776_0 := h1776c.1
                                  have p1776_1 := h1776c.2.1
                                  have p1776_2 := h1776c.2.2.1
                                  have p1776_3 := h1776c.2.2.2
                                  linarith only [hlam, p1776_0]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1810 | h1810
                            · linarith only [h0, h1762, h1771, h1810, h4, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1812 | h1812
                              · linarith only [h0, h1305, h1762, h1770, h1771, h1810, h1812, h4, hc05, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                              · linarith only [h0, h1762, h1770, h1771, h1812, h4, hc34, hc45, hlam, hphi]
                        · linarith only [h0, h1696, h1762, h1770, h4, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                  · linarith only [h1, h1696, h1760, h1762, h1765, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
              · linarith only [h1304, h1762, h4, hc12, hc23, hlam, hphi]
      · linarith only [h1304, h1696, h4, hlam]
  · exact r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s5 m hb0 hb1 hb3 hb4 h0 h1 h2 h3 h4 h1304

set_option maxHeartbeats 8910000 in
set_option maxHeartbeats 8910000 in
theorem r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s3_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
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
  have h0elo := hb0.1
  have h0emin := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 0 3 5 (by decide) (by decide) with h8 | h8
  · rcases m.htr 0 4 5 (by decide) (by decide) with h9 | h9
    · rcases m.htr 1 2 3 (by decide) (by decide) with h10 | h10
      · rcases m.htr 1 2 4 (by decide) (by decide) with h11 | h11
        · rcases m.htr 1 2 5 (by decide) (by decide) with h12 | h12
          · rcases m.htr 1 3 4 (by decide) (by decide) with h13 | h13
            · rcases m.htr 1 3 5 (by decide) (by decide) with h14 | h14
              · rcases m.htr 1 4 5 (by decide) (by decide) with h15 | h15
                · rcases m.htr 2 3 4 (by decide) (by decide) with h16 | h16
                  · linarith only [h0, h10, h16, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                  · linarith only [h0, h10, h13, h16, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h19 | h19
                  · linarith only [h0, h10, h19, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                  · linarith only [h0, h10, h13, h19, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
              · linarith only [h0, h13, h14, h4, h8, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h23 | h23
              · linarith only [h0, h13, h23, h4, h7, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h25 | h25
                · rcases m.htr 2 3 4 (by decide) (by decide) with h26 | h26
                  · linarith only [h0, h13, h26, h4, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h28 | h28
                    · linarith only [h0, h10, h23, h28, hc15, hlam, hphi, ht0b, ht5b, u0elo0]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h30 | h30
                      · linarith only [h0, h11, h30, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                      · linarith only [h2, h25, h30, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h33 | h33
                  · linarith only [h0, h10, h13, h25, h33, h4, h7, h9, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h35 | h35
                    · linarith only [h0, h23, h35, h4, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h37 | h37
                      · linarith only [h11, h25, h37, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h39 | h39
                        · linarith only [h0, h25, h39, h4, h7, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                        · linarith only [h0, h10, h13, h39, h4, h7, h9, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
          · linarith only [h0, h10, h12, h6, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
        · linarith only [h0, h10, h11, h5, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h44 | h44
        · linarith only [h0, h10, h4, h44, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h46 | h46
          · linarith only [h0, h10, h4, h46, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h48 | h48
            · rcases m.htr 1 3 5 (by decide) (by decide) with h49 | h49
              · rcases m.htr 1 4 5 (by decide) (by decide) with h50 | h50
                · rcases m.htr 2 3 4 (by decide) (by decide) with h51 | h51
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h52 | h52
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h53 | h53
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h54 | h54
                        · linarith only [h1, h48, h54, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                        · linarith only [h2, h50, h54, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                      · linarith only [h44, h50, h53, hlam]
                    · linarith only [h3, h44, h49, h50, h51, h52, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                  · linarith only [h10, h4, h51, h7, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h60 | h60
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h61 | h61
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h62 | h62
                      · linarith only [h0, h4, h50, h60, h62, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                      · linarith only [h0, h4, h44, h62, h7, h9, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                    · linarith only [h10, h49, h61, hlam]
                  · linarith only [h10, h48, h60, hlam]
              · linarith only [h0, h4, h48, h49, h8, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h68 | h68
              · linarith only [h0, h4, h48, h68, h7, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h70 | h70
                · rcases m.htr 2 3 4 (by decide) (by decide) with h71 | h71
                  · linarith only [h0, h4, h48, h71, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                  · linarith only [h0, h10, h4, h7, h71, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h74 | h74
                  · linarith only [h0, h10, h4, h48, h74, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                  · linarith only [h0, h10, h4, h7, h74, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h77 | h77
      · rcases m.htr 1 2 4 (by decide) (by decide) with h78 | h78
        · rcases m.htr 1 2 5 (by decide) (by decide) with h79 | h79
          · rcases m.htr 1 3 4 (by decide) (by decide) with h80 | h80
            · rcases m.htr 1 3 5 (by decide) (by decide) with h81 | h81
              · rcases m.htr 1 4 5 (by decide) (by decide) with h82 | h82
                · linarith only [h2, h82, h9, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h84 | h84
                  · linarith only [h0, h77, h84, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                  · linarith only [h1, h80, h84, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
              · linarith only [h0, h4, h8, h80, h81, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h88 | h88
              · linarith only [h0, h4, h7, h80, h88, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h90 | h90
                · linarith only [h2, h9, h90, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h92 | h92
                  · linarith only [h0, h4, h80, h92, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h94 | h94
                    · linarith only [h0, h4, h7, h77, h80, h88, h94, hc15, hlam, hphi, ht0b, ht5b, u0elo0]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h96 | h96
                      · linarith only [h0, h5, h7, h77, h80, h9, h96, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h98 | h98
                        · linarith only [h7, h9, h98, hlam]
                        · rcases h0bigk with h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c
                          · have p100_0 := h100c.1
                            have p100_1 := h100c.2.1
                            have p100_2 := h100c.2.2.1
                            have p100_3 := h100c.2.2.2
                            linarith only [hlam, p100_0]
                          · have p100_0 := h100c.1
                            have p100_1 := h100c.2.1
                            have p100_2 := h100c.2.2.1
                            have p100_3 := h100c.2.2.2
                            linarith only [h4, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p100_1, u0elo0]
                          · have p100_0 := h100c.1
                            have p100_1 := h100c.2.1
                            have p100_2 := h100c.2.2.1
                            have p100_3 := h100c.2.2.2
                            linarith only [h77, h8, h80, h98, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p100_1, u0elo0]
                          · have p100_0 := h100c.1
                            have p100_1 := h100c.2.1
                            have p100_2 := h100c.2.2.1
                            have p100_3 := h100c.2.2.2
                            linarith only [h7, h77, h80, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p100_1, u0elo0]
                          · have p100_0 := h100c.1
                            have p100_1 := h100c.2.1
                            have p100_2 := h100c.2.2.1
                            have p100_3 := h100c.2.2.2
                            linarith only [h77, h8, h80, h98, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p100_1, u0elo0]
                          · have p100_0 := h100c.1
                            have p100_1 := h100c.2.1
                            have p100_2 := h100c.2.2.1
                            have p100_3 := h100c.2.2.2
                            linarith only [h0, hlam, p100_0]
                          · have p100_0 := h100c.1
                            have p100_1 := h100c.2.1
                            have p100_2 := h100c.2.2.1
                            have p100_3 := h100c.2.2.2
                            linarith only [hlam, p100_0]
                          · have p100_0 := h100c.1
                            have p100_1 := h100c.2.1
                            have p100_2 := h100c.2.2.1
                            have p100_3 := h100c.2.2.2
                            linarith only [h77, h8, h80, h98, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p100_1, u0elo1]
                          · have p100_0 := h100c.1
                            have p100_1 := h100c.2.1
                            have p100_2 := h100c.2.2.1
                            have p100_3 := h100c.2.2.2
                            linarith only [h0, h7, h77, h80, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p100_1, u0elo0]
                          · have p100_0 := h100c.1
                            have p100_1 := h100c.2.1
                            have p100_2 := h100c.2.2.1
                            have p100_3 := h100c.2.2.2
                            linarith only [h0, h77, h8, h80, h98, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p100_1, u0elo0]
                          · have p100_0 := h100c.1
                            have p100_1 := h100c.2.1
                            have p100_2 := h100c.2.2.1
                            have p100_3 := h100c.2.2.2
                            linarith only [h1, hlam, p100_1]
                          · have p100_0 := h100c.1
                            have p100_1 := h100c.2.1
                            have p100_2 := h100c.2.2.1
                            have p100_3 := h100c.2.2.2
                            linarith only [h4, hlam, p100_1]
                          · have p100_0 := h100c.1
                            have p100_1 := h100c.2.1
                            have p100_2 := h100c.2.2.1
                            have p100_3 := h100c.2.2.2
                            linarith only [hlam, p100_0]
                          · have p100_0 := h100c.1
                            have p100_1 := h100c.2.1
                            have p100_2 := h100c.2.2.1
                            have p100_3 := h100c.2.2.2
                            linarith only [h7, h77, h80, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p100_1, u0elo2]
                          · have p100_0 := h100c.1
                            have p100_1 := h100c.2.1
                            have p100_2 := h100c.2.2.1
                            have p100_3 := h100c.2.2.2
                            linarith only [h0, h4, h77, h8, h80, h98, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p100_1, u0elo0]
                          · have p100_0 := h100c.1
                            have p100_1 := h100c.2.1
                            have p100_2 := h100c.2.2.1
                            have p100_3 := h100c.2.2.2
                            linarith only [h2, hlam, p100_0]
                          · have p100_0 := h100c.1
                            have p100_1 := h100c.2.1
                            have p100_2 := h100c.2.2.1
                            have p100_3 := h100c.2.2.2
                            linarith only [h5, hlam, p100_0]
                          · have p100_0 := h100c.1
                            have p100_1 := h100c.2.1
                            have p100_2 := h100c.2.2.1
                            have p100_3 := h100c.2.2.2
                            linarith only [h7, hlam, p100_0]
                          · have p100_0 := h100c.1
                            have p100_1 := h100c.2.1
                            have p100_2 := h100c.2.2.1
                            have p100_3 := h100c.2.2.2
                            linarith only [hlam, p100_0]
                          · have p100_0 := h100c.1
                            have p100_1 := h100c.2.1
                            have p100_2 := h100c.2.2.1
                            have p100_3 := h100c.2.2.2
                            linarith only [h9, hlam, p100_0]
                          · have p100_0 := h100c.1
                            have p100_1 := h100c.2.1
                            have p100_2 := h100c.2.2.1
                            have p100_3 := h100c.2.2.2
                            linarith only [h3, hlam, p100_0]
                          · have p100_0 := h100c.1
                            have p100_1 := h100c.2.1
                            have p100_2 := h100c.2.2.1
                            have p100_3 := h100c.2.2.2
                            linarith only [h6, hlam, p100_1]
                          · have p100_0 := h100c.1
                            have p100_1 := h100c.2.1
                            have p100_2 := h100c.2.2.1
                            have p100_3 := h100c.2.2.2
                            linarith only [h8, hlam, p100_0]
                          · have p100_0 := h100c.1
                            have p100_1 := h100c.2.1
                            have p100_2 := h100c.2.2.1
                            have p100_3 := h100c.2.2.2
                            linarith only [h7, h77, h80, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p100_1, u0elo4]
                          · have p100_0 := h100c.1
                            have p100_1 := h100c.2.1
                            have p100_2 := h100c.2.2.1
                            have p100_3 := h100c.2.2.2
                            linarith only [hlam, p100_0]
          · linarith only [h0, h6, h77, h79, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
        · linarith only [h0, h5, h77, h78, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h128 | h128
        · linarith only [h0, h128, h4, h77, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h130 | h130
          · linarith only [h0, h130, h4, h77, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h132 | h132
            · rcases m.htr 1 3 5 (by decide) (by decide) with h133 | h133
              · rcases m.htr 1 4 5 (by decide) (by decide) with h134 | h134
                · linarith only [h134, h2, h9, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h136 | h136
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h137 | h137
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h138 | h138
                      · linarith only [h0, h130, h138, h5, h6, h9, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h140 | h140
                        · linarith only [h1, h132, h140, h9, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                        · rcases h0bigk with h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c
                          · have p142_0 := h142c.1
                            have p142_1 := h142c.2.1
                            have p142_2 := h142c.2.2.1
                            have p142_3 := h142c.2.2.2
                            linarith only [hlam, p142_0]
                          · have p142_0 := h142c.1
                            have p142_1 := h142c.2.1
                            have p142_2 := h142c.2.2.1
                            have p142_3 := h142c.2.2.2
                            linarith only [h4, h77, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p142_1, u0elo0]
                          · have p142_0 := h142c.1
                            have p142_1 := h142c.2.1
                            have p142_2 := h142c.2.2.1
                            have p142_3 := h142c.2.2.2
                            linarith only [h7, hc34, hlam, hphi, ht0b, ht45, ht5b, p142_1, u0elo0]
                          · have p142_0 := h142c.1
                            have p142_1 := h142c.2.1
                            have p142_2 := h142c.2.2.1
                            have p142_3 := h142c.2.2.2
                            linarith only [h128, h5, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p142_1, u0elo0]
                          · have p142_0 := h142c.1
                            have p142_1 := h142c.2.1
                            have p142_2 := h142c.2.2.1
                            have p142_3 := h142c.2.2.2
                            linarith only [h128, h5, h9, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p142_1, u0elo0]
                          · have p142_0 := h142c.1
                            have p142_1 := h142c.2.1
                            have p142_2 := h142c.2.2.1
                            have p142_3 := h142c.2.2.2
                            linarith only [h0, hlam, p142_0]
                          · have p142_0 := h142c.1
                            have p142_1 := h142c.2.1
                            have p142_2 := h142c.2.2.1
                            have p142_3 := h142c.2.2.2
                            linarith only [hlam, p142_0]
                          · have p142_0 := h142c.1
                            have p142_1 := h142c.2.1
                            have p142_2 := h142c.2.2.1
                            have p142_3 := h142c.2.2.2
                            linarith only [h7, hc34, hlam, hphi, ht0b, ht45, ht5b, p142_1, u0elo1]
                          · have p142_0 := h142c.1
                            have p142_1 := h142c.2.1
                            have p142_2 := h142c.2.2.1
                            have p142_3 := h142c.2.2.2
                            linarith only [h0, h128, h5, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p142_1, u0elo0]
                          · have p142_0 := h142c.1
                            have p142_1 := h142c.2.1
                            have p142_2 := h142c.2.2.1
                            have p142_3 := h142c.2.2.2
                            linarith only [h0, h128, h5, h9, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p142_1, u0elo0]
                          · have p142_0 := h142c.1
                            have p142_1 := h142c.2.1
                            have p142_2 := h142c.2.2.1
                            have p142_3 := h142c.2.2.2
                            linarith only [h1, hlam, p142_1]
                          · have p142_0 := h142c.1
                            have p142_1 := h142c.2.1
                            have p142_2 := h142c.2.2.1
                            have p142_3 := h142c.2.2.2
                            linarith only [h4, hlam, p142_1]
                          · have p142_0 := h142c.1
                            have p142_1 := h142c.2.1
                            have p142_2 := h142c.2.2.1
                            have p142_3 := h142c.2.2.2
                            linarith only [hlam, p142_0]
                          · have p142_0 := h142c.1
                            have p142_1 := h142c.2.1
                            have p142_2 := h142c.2.2.1
                            have p142_3 := h142c.2.2.2
                            linarith only [h128, h5, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p142_1, u0elo2]
                          · have p142_0 := h142c.1
                            have p142_1 := h142c.2.1
                            have p142_2 := h142c.2.2.1
                            have p142_3 := h142c.2.2.2
                            linarith only [h0, h128, h4, h5, h9, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p142_1, u0elo0]
                          · have p142_0 := h142c.1
                            have p142_1 := h142c.2.1
                            have p142_2 := h142c.2.2.1
                            have p142_3 := h142c.2.2.2
                            linarith only [h2, hlam, p142_0]
                          · have p142_0 := h142c.1
                            have p142_1 := h142c.2.1
                            have p142_2 := h142c.2.2.1
                            have p142_3 := h142c.2.2.2
                            linarith only [h5, hlam, p142_0]
                          · have p142_0 := h142c.1
                            have p142_1 := h142c.2.1
                            have p142_2 := h142c.2.2.1
                            have p142_3 := h142c.2.2.2
                            linarith only [h7, hlam, p142_0]
                          · have p142_0 := h142c.1
                            have p142_1 := h142c.2.1
                            have p142_2 := h142c.2.2.1
                            have p142_3 := h142c.2.2.2
                            linarith only [hlam, p142_0]
                          · have p142_0 := h142c.1
                            have p142_1 := h142c.2.1
                            have p142_2 := h142c.2.2.1
                            have p142_3 := h142c.2.2.2
                            linarith only [h9, hlam, p142_0]
                          · have p142_0 := h142c.1
                            have p142_1 := h142c.2.1
                            have p142_2 := h142c.2.2.1
                            have p142_3 := h142c.2.2.2
                            linarith only [h3, hlam, p142_0]
                          · have p142_0 := h142c.1
                            have p142_1 := h142c.2.1
                            have p142_2 := h142c.2.2.1
                            have p142_3 := h142c.2.2.2
                            linarith only [h6, hlam, p142_1]
                          · have p142_0 := h142c.1
                            have p142_1 := h142c.2.1
                            have p142_2 := h142c.2.2.1
                            have p142_3 := h142c.2.2.2
                            linarith only [h8, hlam, p142_0]
                          · have p142_0 := h142c.1
                            have p142_1 := h142c.2.1
                            have p142_2 := h142c.2.2.1
                            have p142_3 := h142c.2.2.2
                            linarith only [h128, h5, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p142_1, u0elo4]
                          · have p142_0 := h142c.1
                            have p142_1 := h142c.2.1
                            have p142_2 := h142c.2.2.1
                            have p142_3 := h142c.2.2.2
                            linarith only [hlam, p142_0]
                    · linarith only [h1, h128, h133, h136, h137, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                  · linarith only [h0, h136, h4, h7, h77, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
              · linarith only [h0, h132, h133, h4, h8, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h171 | h171
              · linarith only [h0, h132, h171, h4, h7, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h173 | h173
                · linarith only [h173, h2, h9, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h175 | h175
                  · linarith only [h132, h175, h4, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                  · linarith only [h0, h175, h4, h7, h77, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
  · rcases m.htr 0 4 5 (by decide) (by decide) with h178 | h178
    · linarith only [h178, h7, h8, hlam]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h180 | h180
      · rcases m.htr 1 2 4 (by decide) (by decide) with h181 | h181
        · rcases m.htr 1 2 5 (by decide) (by decide) with h182 | h182
          · rcases m.htr 1 3 4 (by decide) (by decide) with h183 | h183
            · rcases m.htr 1 3 5 (by decide) (by decide) with h184 | h184
              · linarith only [h1, h184, h8, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h186 | h186
                · linarith only [h178, h183, h184, h186, h2, h3, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h188 | h188
                  · linarith only [h0, h180, h188, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                  · linarith only [h1, h183, h188, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
            · linarith only [h183, h7, h8, hc13, hc35, hlam, hphi]
          · linarith only [h0, h180, h182, h6, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
        · linarith only [h0, h180, h181, h5, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h194 | h194
        · linarith only [h0, h180, h194, h4, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h196 | h196
          · linarith only [h0, h180, h196, h4, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h198 | h198
            · rcases m.htr 1 3 5 (by decide) (by decide) with h199 | h199
              · linarith only [h1, h199, h8, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h201 | h201
                · linarith only [h178, h2, h201, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h203 | h203
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h204 | h204
                    · linarith only [h194, h204, h4, h5, h7, h8, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h206 | h206
                      · linarith only [h178, h206, h5, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h208 | h208
                        · linarith only [h178, h194, h198, h208, h5, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                        · rcases h0bigk with h210c | h210c | h210c | h210c | h210c | h210c | h210c | h210c | h210c | h210c | h210c | h210c | h210c | h210c | h210c | h210c | h210c | h210c | h210c | h210c | h210c | h210c | h210c | h210c | h210c
                          · have p210_0 := h210c.1
                            have p210_1 := h210c.2.1
                            have p210_2 := h210c.2.2.1
                            have p210_3 := h210c.2.2.2
                            linarith only [hlam, p210_0]
                          · have p210_0 := h210c.1
                            have p210_1 := h210c.2.1
                            have p210_2 := h210c.2.2.1
                            have p210_3 := h210c.2.2.2
                            linarith only [h180, h4, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p210_1, u0elo0]
                          · have p210_0 := h210c.1
                            have p210_1 := h210c.2.1
                            have p210_2 := h210c.2.2.1
                            have p210_3 := h210c.2.2.2
                            linarith only [h194, h5, h7, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p210_1, u0elo0]
                          · have p210_0 := h210c.1
                            have p210_1 := h210c.2.1
                            have p210_2 := h210c.2.2.1
                            have p210_3 := h210c.2.2.2
                            linarith only [h194, h5, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p210_1, u0elo0]
                          · have p210_0 := h210c.1
                            have p210_1 := h210c.2.1
                            have p210_2 := h210c.2.2.1
                            have p210_3 := h210c.2.2.2
                            linarith only [h194, h5, h7, h8, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p210_1, u0elo0]
                          · have p210_0 := h210c.1
                            have p210_1 := h210c.2.1
                            have p210_2 := h210c.2.2.1
                            have p210_3 := h210c.2.2.2
                            linarith only [h0, hlam, p210_0]
                          · have p210_0 := h210c.1
                            have p210_1 := h210c.2.1
                            have p210_2 := h210c.2.2.1
                            have p210_3 := h210c.2.2.2
                            linarith only [hlam, p210_0]
                          · have p210_0 := h210c.1
                            have p210_1 := h210c.2.1
                            have p210_2 := h210c.2.2.1
                            have p210_3 := h210c.2.2.2
                            linarith only [h194, h5, h7, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p210_1, u0elo1]
                          · have p210_0 := h210c.1
                            have p210_1 := h210c.2.1
                            have p210_2 := h210c.2.2.1
                            have p210_3 := h210c.2.2.2
                            linarith only [h0, h194, h5, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p210_1, u0elo0]
                          · have p210_0 := h210c.1
                            have p210_1 := h210c.2.1
                            have p210_2 := h210c.2.2.1
                            have p210_3 := h210c.2.2.2
                            linarith only [h0, h194, h5, h7, h8, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p210_1, u0elo0]
                          · have p210_0 := h210c.1
                            have p210_1 := h210c.2.1
                            have p210_2 := h210c.2.2.1
                            have p210_3 := h210c.2.2.2
                            linarith only [h1, hlam, p210_1]
                          · have p210_0 := h210c.1
                            have p210_1 := h210c.2.1
                            have p210_2 := h210c.2.2.1
                            have p210_3 := h210c.2.2.2
                            linarith only [h4, hlam, p210_1]
                          · have p210_0 := h210c.1
                            have p210_1 := h210c.2.1
                            have p210_2 := h210c.2.2.1
                            have p210_3 := h210c.2.2.2
                            linarith only [hlam, p210_0]
                          · have p210_0 := h210c.1
                            have p210_1 := h210c.2.1
                            have p210_2 := h210c.2.2.1
                            have p210_3 := h210c.2.2.2
                            linarith only [h194, h5, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p210_1, u0elo2]
                          · have p210_0 := h210c.1
                            have p210_1 := h210c.2.1
                            have p210_2 := h210c.2.2.1
                            have p210_3 := h210c.2.2.2
                            linarith only [h8, hlam, p210_1]
                          · have p210_0 := h210c.1
                            have p210_1 := h210c.2.1
                            have p210_2 := h210c.2.2.1
                            have p210_3 := h210c.2.2.2
                            linarith only [h2, hlam, p210_0]
                          · have p210_0 := h210c.1
                            have p210_1 := h210c.2.1
                            have p210_2 := h210c.2.2.1
                            have p210_3 := h210c.2.2.2
                            linarith only [h5, hlam, p210_0]
                          · have p210_0 := h210c.1
                            have p210_1 := h210c.2.1
                            have p210_2 := h210c.2.2.1
                            have p210_3 := h210c.2.2.2
                            linarith only [h7, hlam, p210_0]
                          · have p210_0 := h210c.1
                            have p210_1 := h210c.2.1
                            have p210_2 := h210c.2.2.1
                            have p210_3 := h210c.2.2.2
                            linarith only [hlam, p210_0]
                          · have p210_0 := h210c.1
                            have p210_1 := h210c.2.1
                            have p210_2 := h210c.2.2.1
                            have p210_3 := h210c.2.2.2
                            linarith only [h178, hlam, p210_0]
                          · have p210_0 := h210c.1
                            have p210_1 := h210c.2.1
                            have p210_2 := h210c.2.2.1
                            have p210_3 := h210c.2.2.2
                            linarith only [h3, hlam, p210_0]
                          · have p210_0 := h210c.1
                            have p210_1 := h210c.2.1
                            have p210_2 := h210c.2.2.1
                            have p210_3 := h210c.2.2.2
                            linarith only [h6, hlam, p210_1]
                          · have p210_0 := h210c.1
                            have p210_1 := h210c.2.1
                            have p210_2 := h210c.2.2.1
                            have p210_3 := h210c.2.2.2
                            linarith only [h1, h198, hc34, hlam, hphi, ht0b, ht45, ht5b, p210_1, u0elo4]
                          · have p210_0 := h210c.1
                            have p210_1 := h210c.2.1
                            have p210_2 := h210c.2.2.1
                            have p210_3 := h210c.2.2.2
                            linarith only [h194, h5, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p210_1, u0elo4]
                          · have p210_0 := h210c.1
                            have p210_1 := h210c.2.1
                            have p210_2 := h210c.2.2.1
                            have p210_3 := h210c.2.2.2
                            linarith only [hlam, p210_0]
                  · linarith only [h1, h180, h198, h203, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
            · linarith only [h198, h7, h8, hc13, hc35, hlam, hphi]

end R2N4
