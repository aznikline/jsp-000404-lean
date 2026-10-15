import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5720000 in
set_option maxHeartbeats 5720000 in
theorem r1l7_20_11_13_14_H_I_L_I_L_R_L_I_x1_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1337 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
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
  have h3ehi := hb3.1
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h1338 | h1338
  · rcases m.htr 0 1 5 (by decide) (by decide) with h1339 | h1339
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1340 | h1340
      · rcases m.htr 0 2 4 (by decide) (by decide) with h1341 | h1341
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1342 | h1342
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1343 | h1343
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1344 | h1344
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1345 | h1345
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1346 | h1346
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1347 | h1347
                    · rcases h0bigk with h1348c | h1348c | h1348c | h1348c | h1348c | h1348c | h1348c | h1348c | h1348c | h1348c | h1348c | h1348c | h1348c | h1348c | h1348c | h1348c | h1348c | h1348c | h1348c | h1348c | h1348c | h1348c | h1348c | h1348c | h1348c
                      · have p1348_0 := h1348c.1
                        have p1348_1 := h1348c.2.1
                        have p1348_2 := h1348c.2.2.1
                        have p1348_3 := h1348c.2.2.2
                        linarith only [hlam, p1348_0]
                      · have p1348_0 := h1348c.1
                        have p1348_1 := h1348c.2.1
                        have p1348_2 := h1348c.2.2.1
                        have p1348_3 := h1348c.2.2.2
                        linarith only [h0, hlam, p1348_1]
                      · have p1348_0 := h1348c.1
                        have p1348_1 := h1348c.2.1
                        have p1348_2 := h1348c.2.2.1
                        have p1348_3 := h1348c.2.2.2
                        linarith only [h0, h1340, h1347, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1348_1, u3ehi3]
                      · have p1348_0 := h1348c.1
                        have p1348_1 := h1348c.2.1
                        have p1348_2 := h1348c.2.2.1
                        have p1348_3 := h1348c.2.2.2
                        linarith only [h0, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1348_1]
                      · have p1348_0 := h1348c.1
                        have p1348_1 := h1348c.2.1
                        have p1348_2 := h1348c.2.2.1
                        have p1348_3 := h1348c.2.2.2
                        linarith only [h0, h1344, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1348_1, u3ehi4]
                      · have p1348_0 := h1348c.1
                        have p1348_1 := h1348c.2.1
                        have p1348_2 := h1348c.2.2.1
                        have p1348_3 := h1348c.2.2.2
                        linarith only [h0, hc01, hc12, hlam, hphi, p1348_1]
                      · have p1348_0 := h1348c.1
                        have p1348_1 := h1348c.2.1
                        have p1348_2 := h1348c.2.2.1
                        have p1348_3 := h1348c.2.2.2
                        linarith only [hlam, p1348_0]
                      · have p1348_0 := h1348c.1
                        have p1348_1 := h1348c.2.1
                        have p1348_2 := h1348c.2.2.1
                        have p1348_3 := h1348c.2.2.2
                        linarith only [h0, h1340, h1347, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1348_1, u3ehi3]
                      · have p1348_0 := h1348c.1
                        have p1348_1 := h1348c.2.1
                        have p1348_2 := h1348c.2.2.1
                        have p1348_3 := h1348c.2.2.2
                        linarith only [h0, h1345, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1348_1]
                      · have p1348_0 := h1348c.1
                        have p1348_1 := h1348c.2.1
                        have p1348_2 := h1348c.2.2.1
                        have p1348_3 := h1348c.2.2.2
                        linarith only [h0, h1344, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1348_1, u3ehi4]
                      · have p1348_0 := h1348c.1
                        have p1348_1 := h1348c.2.1
                        have p1348_2 := h1348c.2.2.1
                        have p1348_3 := h1348c.2.2.2
                        linarith only [h1337, hlam, p1348_1]
                      · have p1348_0 := h1348c.1
                        have p1348_1 := h1348c.2.1
                        have p1348_2 := h1348c.2.2.1
                        have p1348_3 := h1348c.2.2.2
                        linarith only [h1340, hlam, p1348_1]
                      · have p1348_0 := h1348c.1
                        have p1348_1 := h1348c.2.1
                        have p1348_2 := h1348c.2.2.1
                        have p1348_3 := h1348c.2.2.2
                        linarith only [hlam, p1348_0]
                      · have p1348_0 := h1348c.1
                        have p1348_1 := h1348c.2.1
                        have p1348_2 := h1348c.2.2.1
                        have p1348_3 := h1348c.2.2.2
                        linarith only [h1337, h1345, hc01, hc45, hlam, hphi, ht0b, ht5b, p1348_1]
                      · have p1348_0 := h1348c.1
                        have p1348_1 := h1348c.2.1
                        have p1348_2 := h1348c.2.2.1
                        have p1348_3 := h1348c.2.2.2
                        linarith only [h0, h1337, h1344, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1348_1, u3ehi4]
                      · have p1348_0 := h1348c.1
                        have p1348_1 := h1348c.2.1
                        have p1348_2 := h1348c.2.2.1
                        have p1348_3 := h1348c.2.2.2
                        linarith only [h1338, hlam, p1348_0]
                      · have p1348_0 := h1348c.1
                        have p1348_1 := h1348c.2.1
                        have p1348_2 := h1348c.2.2.1
                        have p1348_3 := h1348c.2.2.2
                        linarith only [h1341, hlam, p1348_0]
                      · have p1348_0 := h1348c.1
                        have p1348_1 := h1348c.2.1
                        have p1348_2 := h1348c.2.2.1
                        have p1348_3 := h1348c.2.2.2
                        linarith only [h1343, hlam, p1348_0]
                      · have p1348_0 := h1348c.1
                        have p1348_1 := h1348c.2.1
                        have p1348_2 := h1348c.2.2.1
                        have p1348_3 := h1348c.2.2.2
                        linarith only [hlam, p1348_0]
                      · have p1348_0 := h1348c.1
                        have p1348_1 := h1348c.2.1
                        have p1348_2 := h1348c.2.2.1
                        have p1348_3 := h1348c.2.2.2
                        linarith only [h1344, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p1348_1, u3ehi4]
                      · have p1348_0 := h1348c.1
                        have p1348_1 := h1348c.2.1
                        have p1348_2 := h1348c.2.2.1
                        have p1348_3 := h1348c.2.2.2
                        linarith only [h1339, hlam, p1348_0]
                      · have p1348_0 := h1348c.1
                        have p1348_1 := h1348c.2.1
                        have p1348_2 := h1348c.2.2.1
                        have p1348_3 := h1348c.2.2.2
                        linarith only [h1342, hlam, p1348_1]
                      · have p1348_0 := h1348c.1
                        have p1348_1 := h1348c.2.1
                        have p1348_2 := h1348c.2.2.1
                        have p1348_3 := h1348c.2.2.2
                        linarith only [h1344, hlam, p1348_0]
                      · have p1348_0 := h1348c.1
                        have p1348_1 := h1348c.2.1
                        have p1348_2 := h1348c.2.2.1
                        have p1348_3 := h1348c.2.2.2
                        linarith only [h1345, hlam, p1348_1]
                      · have p1348_0 := h1348c.1
                        have p1348_1 := h1348c.2.1
                        have p1348_2 := h1348c.2.2.1
                        have p1348_3 := h1348c.2.2.2
                        linarith only [hlam, p1348_0]
                    · linarith only [h0, h1337, h1343, h1347, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                  · linarith only [h0, h1337, h1343, h1346, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1376 | h1376
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1377 | h1377
                    · rcases h0bigk with h1378c | h1378c | h1378c | h1378c | h1378c | h1378c | h1378c | h1378c | h1378c | h1378c | h1378c | h1378c | h1378c | h1378c | h1378c | h1378c | h1378c | h1378c | h1378c | h1378c | h1378c | h1378c | h1378c | h1378c | h1378c
                      · have p1378_0 := h1378c.1
                        have p1378_1 := h1378c.2.1
                        have p1378_2 := h1378c.2.2.1
                        have p1378_3 := h1378c.2.2.2
                        linarith only [hlam, p1378_0]
                      · have p1378_0 := h1378c.1
                        have p1378_1 := h1378c.2.1
                        have p1378_2 := h1378c.2.2.1
                        have p1378_3 := h1378c.2.2.2
                        linarith only [h0, hlam, p1378_1]
                      · have p1378_0 := h1378c.1
                        have p1378_1 := h1378c.2.1
                        have p1378_2 := h1378c.2.2.1
                        have p1378_3 := h1378c.2.2.2
                        linarith only [h1340, h1377, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p1378_1, u3ehi3]
                      · have p1378_0 := h1378c.1
                        have p1378_1 := h1378c.2.1
                        have p1378_2 := h1378c.2.2.1
                        have p1378_3 := h1378c.2.2.2
                        linarith only [h0, h1338, h1376, h1377, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1378_1, u3ehi3]
                      · have p1378_0 := h1378c.1
                        have p1378_1 := h1378c.2.1
                        have p1378_2 := h1378c.2.2.1
                        have p1378_3 := h1378c.2.2.2
                        linarith only [h0, h1338, h1345, h1376, h1377, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1378_1, u3ehi3]
                      · have p1378_0 := h1378c.1
                        have p1378_1 := h1378c.2.1
                        have p1378_2 := h1378c.2.2.1
                        have p1378_3 := h1378c.2.2.2
                        linarith only [h0, hc01, hc12, hlam, hphi, p1378_1]
                      · have p1378_0 := h1378c.1
                        have p1378_1 := h1378c.2.1
                        have p1378_2 := h1378c.2.2.1
                        have p1378_3 := h1378c.2.2.2
                        linarith only [hlam, p1378_0]
                      · have p1378_0 := h1378c.1
                        have p1378_1 := h1378c.2.1
                        have p1378_2 := h1378c.2.2.1
                        have p1378_3 := h1378c.2.2.2
                        linarith only [h0, h1340, h1377, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1378_1, u3ehi3]
                      · have p1378_0 := h1378c.1
                        have p1378_1 := h1378c.2.1
                        have p1378_2 := h1378c.2.2.1
                        have p1378_3 := h1378c.2.2.2
                        linarith only [h0, h1338, h1376, h1377, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1378_1, u3ehi3]
                      · have p1378_0 := h1378c.1
                        have p1378_1 := h1378c.2.1
                        have p1378_2 := h1378c.2.2.1
                        have p1378_3 := h1378c.2.2.2
                        linarith only [h0, h1338, h1345, h1376, h1377, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1378_1, u3ehi3]
                      · have p1378_0 := h1378c.1
                        have p1378_1 := h1378c.2.1
                        have p1378_2 := h1378c.2.2.1
                        have p1378_3 := h1378c.2.2.2
                        linarith only [h1337, hlam, p1378_1]
                      · have p1378_0 := h1378c.1
                        have p1378_1 := h1378c.2.1
                        have p1378_2 := h1378c.2.2.1
                        have p1378_3 := h1378c.2.2.2
                        linarith only [h1340, hlam, p1378_1]
                      · have p1378_0 := h1378c.1
                        have p1378_1 := h1378c.2.1
                        have p1378_2 := h1378c.2.2.1
                        have p1378_3 := h1378c.2.2.2
                        linarith only [hlam, p1378_0]
                      · have p1378_0 := h1378c.1
                        have p1378_1 := h1378c.2.1
                        have p1378_2 := h1378c.2.2.1
                        have p1378_3 := h1378c.2.2.2
                        linarith only [h1337, h1338, h1376, h1377, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p1378_1, u3ehi3]
                      · have p1378_0 := h1378c.1
                        have p1378_1 := h1378c.2.1
                        have p1378_2 := h1378c.2.2.1
                        have p1378_3 := h1378c.2.2.2
                        linarith only [h0, h1337, h1338, h1345, h1376, h1377, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1378_1, u3ehi3]
                      · have p1378_0 := h1378c.1
                        have p1378_1 := h1378c.2.1
                        have p1378_2 := h1378c.2.2.1
                        have p1378_3 := h1378c.2.2.2
                        linarith only [h1338, hlam, p1378_0]
                      · have p1378_0 := h1378c.1
                        have p1378_1 := h1378c.2.1
                        have p1378_2 := h1378c.2.2.1
                        have p1378_3 := h1378c.2.2.2
                        linarith only [h1341, hlam, p1378_0]
                      · have p1378_0 := h1378c.1
                        have p1378_1 := h1378c.2.1
                        have p1378_2 := h1378c.2.2.1
                        have p1378_3 := h1378c.2.2.2
                        linarith only [h1343, hlam, p1378_0]
                      · have p1378_0 := h1378c.1
                        have p1378_1 := h1378c.2.1
                        have p1378_2 := h1378c.2.2.1
                        have p1378_3 := h1378c.2.2.2
                        linarith only [hlam, p1378_0]
                      · have p1378_0 := h1378c.1
                        have p1378_1 := h1378c.2.1
                        have p1378_2 := h1378c.2.2.1
                        have p1378_3 := h1378c.2.2.2
                        linarith only [h1345, hlam, p1378_0]
                      · have p1378_0 := h1378c.1
                        have p1378_1 := h1378c.2.1
                        have p1378_2 := h1378c.2.2.1
                        have p1378_3 := h1378c.2.2.2
                        linarith only [h1339, hlam, p1378_0]
                      · have p1378_0 := h1378c.1
                        have p1378_1 := h1378c.2.1
                        have p1378_2 := h1378c.2.2.1
                        have p1378_3 := h1378c.2.2.2
                        linarith only [h1342, hlam, p1378_1]
                      · have p1378_0 := h1378c.1
                        have p1378_1 := h1378c.2.1
                        have p1378_2 := h1378c.2.2.1
                        have p1378_3 := h1378c.2.2.2
                        linarith only [h1344, hlam, p1378_0]
                      · have p1378_0 := h1378c.1
                        have p1378_1 := h1378c.2.1
                        have p1378_2 := h1378c.2.2.1
                        have p1378_3 := h1378c.2.2.2
                        linarith only [h1338, h1376, h1377, hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p1378_1, u3ehi3]
                      · have p1378_0 := h1378c.1
                        have p1378_1 := h1378c.2.1
                        have p1378_2 := h1378c.2.2.1
                        have p1378_3 := h1378c.2.2.2
                        linarith only [hlam, p1378_0]
                    · linarith only [h0, h1337, h1343, h1377, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                  · linarith only [h0, h1337, h1376, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
              · linarith only [h1343, h1344, hc35, hlam, hphi, u3ehi3]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1407 | h1407
              · linarith only [h1343, h1407, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1409 | h1409
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1410 | h1410
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1411 | h1411
                    · linarith only [h0, h1340, h1343, h1411, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi0]
                    · rcases h0bigk with h1413c | h1413c | h1413c | h1413c | h1413c | h1413c | h1413c | h1413c | h1413c | h1413c | h1413c | h1413c | h1413c | h1413c | h1413c | h1413c | h1413c | h1413c | h1413c | h1413c | h1413c | h1413c | h1413c | h1413c | h1413c
                      · have p1413_0 := h1413c.1
                        have p1413_1 := h1413c.2.1
                        have p1413_2 := h1413c.2.2.1
                        have p1413_3 := h1413c.2.2.2
                        linarith only [hlam, p1413_0]
                      · have p1413_0 := h1413c.1
                        have p1413_1 := h1413c.2.1
                        have p1413_2 := h1413c.2.2.1
                        have p1413_3 := h1413c.2.2.2
                        linarith only [h0, hlam, p1413_1]
                      · have p1413_0 := h1413c.1
                        have p1413_1 := h1413c.2.1
                        have p1413_2 := h1413c.2.2.1
                        have p1413_3 := h1413c.2.2.2
                        linarith only [h0, h1337, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1413_1, u3ehi1]
                      · have p1413_0 := h1413c.1
                        have p1413_1 := h1413c.2.1
                        have p1413_2 := h1413c.2.2.1
                        have p1413_3 := h1413c.2.2.2
                        linarith only [h0, h1337, h1407, h1409, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1413_1, u3ehi1]
                      · have p1413_0 := h1413c.1
                        have p1413_1 := h1413c.2.1
                        have p1413_2 := h1413c.2.2.1
                        have p1413_3 := h1413c.2.2.2
                        linarith only [h0, h1337, h1407, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1413_1, u3ehi1]
                      · have p1413_0 := h1413c.1
                        have p1413_1 := h1413c.2.1
                        have p1413_2 := h1413c.2.2.1
                        have p1413_3 := h1413c.2.2.2
                        linarith only [h0, hc01, hc12, hlam, hphi, p1413_1]
                      · have p1413_0 := h1413c.1
                        have p1413_1 := h1413c.2.1
                        have p1413_2 := h1413c.2.2.1
                        have p1413_3 := h1413c.2.2.2
                        linarith only [hlam, p1413_0]
                      · have p1413_0 := h1413c.1
                        have p1413_1 := h1413c.2.1
                        have p1413_2 := h1413c.2.2.1
                        have p1413_3 := h1413c.2.2.2
                        linarith only [h0, h1337, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1413_1, u3ehi1]
                      · have p1413_0 := h1413c.1
                        have p1413_1 := h1413c.2.1
                        have p1413_2 := h1413c.2.2.1
                        have p1413_3 := h1413c.2.2.2
                        linarith only [h0, h1337, h1407, h1409, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1413_1, u3ehi1]
                      · have p1413_0 := h1413c.1
                        have p1413_1 := h1413c.2.1
                        have p1413_2 := h1413c.2.2.1
                        have p1413_3 := h1413c.2.2.2
                        linarith only [h0, h1337, h1407, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1413_1, u3ehi1]
                      · have p1413_0 := h1413c.1
                        have p1413_1 := h1413c.2.1
                        have p1413_2 := h1413c.2.2.1
                        have p1413_3 := h1413c.2.2.2
                        linarith only [h1337, hlam, p1413_1]
                      · have p1413_0 := h1413c.1
                        have p1413_1 := h1413c.2.1
                        have p1413_2 := h1413c.2.2.1
                        have p1413_3 := h1413c.2.2.2
                        linarith only [h1340, hlam, p1413_1]
                      · have p1413_0 := h1413c.1
                        have p1413_1 := h1413c.2.1
                        have p1413_2 := h1413c.2.2.1
                        have p1413_3 := h1413c.2.2.2
                        linarith only [hlam, p1413_0]
                      · have p1413_0 := h1413c.1
                        have p1413_1 := h1413c.2.1
                        have p1413_2 := h1413c.2.2.1
                        have p1413_3 := h1413c.2.2.2
                        linarith only [h1343, hlam, p1413_1]
                      · have p1413_0 := h1413c.1
                        have p1413_1 := h1413c.2.1
                        have p1413_2 := h1413c.2.2.1
                        have p1413_3 := h1413c.2.2.2
                        linarith only [h1407, hlam, p1413_1]
                      · have p1413_0 := h1413c.1
                        have p1413_1 := h1413c.2.1
                        have p1413_2 := h1413c.2.2.1
                        have p1413_3 := h1413c.2.2.2
                        linarith only [h1338, hlam, p1413_0]
                      · have p1413_0 := h1413c.1
                        have p1413_1 := h1413c.2.1
                        have p1413_2 := h1413c.2.2.1
                        have p1413_3 := h1413c.2.2.2
                        linarith only [h1341, hlam, p1413_0]
                      · have p1413_0 := h1413c.1
                        have p1413_1 := h1413c.2.1
                        have p1413_2 := h1413c.2.2.1
                        have p1413_3 := h1413c.2.2.2
                        linarith only [h1337, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p1413_1, u3ehi1]
                      · have p1413_0 := h1413c.1
                        have p1413_1 := h1413c.2.1
                        have p1413_2 := h1413c.2.2.1
                        have p1413_3 := h1413c.2.2.2
                        linarith only [hlam, p1413_0]
                      · have p1413_0 := h1413c.1
                        have p1413_1 := h1413c.2.1
                        have p1413_2 := h1413c.2.2.1
                        have p1413_3 := h1413c.2.2.2
                        linarith only [h1337, h1338, h1407, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p1413_1, u3ehi1]
                      · have p1413_0 := h1413c.1
                        have p1413_1 := h1413c.2.1
                        have p1413_2 := h1413c.2.2.1
                        have p1413_3 := h1413c.2.2.2
                        linarith only [h1339, hlam, p1413_0]
                      · have p1413_0 := h1413c.1
                        have p1413_1 := h1413c.2.1
                        have p1413_2 := h1413c.2.2.1
                        have p1413_3 := h1413c.2.2.2
                        linarith only [h1342, hlam, p1413_1]
                      · have p1413_0 := h1413c.1
                        have p1413_1 := h1413c.2.1
                        have p1413_2 := h1413c.2.2.1
                        have p1413_3 := h1413c.2.2.2
                        linarith only [h1337, hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p1413_1, u3ehi1]
                      · have p1413_0 := h1413c.1
                        have p1413_1 := h1413c.2.1
                        have p1413_2 := h1413c.2.2.1
                        have p1413_3 := h1413c.2.2.2
                        linarith only [h1409, hlam, p1413_1]
                      · have p1413_0 := h1413c.1
                        have p1413_1 := h1413c.2.1
                        have p1413_2 := h1413c.2.2.1
                        have p1413_3 := h1413c.2.2.2
                        linarith only [hlam, p1413_0]
                  · linarith only [h0, h1337, h1410, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1440 | h1440
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1441 | h1441
                    · linarith only [h1340, h1343, h1441, hlam]
                    · rcases h0bigk with h1443c | h1443c | h1443c | h1443c | h1443c | h1443c | h1443c | h1443c | h1443c | h1443c | h1443c | h1443c | h1443c | h1443c | h1443c | h1443c | h1443c | h1443c | h1443c | h1443c | h1443c | h1443c | h1443c | h1443c | h1443c
                      · have p1443_0 := h1443c.1
                        have p1443_1 := h1443c.2.1
                        have p1443_2 := h1443c.2.2.1
                        have p1443_3 := h1443c.2.2.2
                        linarith only [hlam, p1443_0]
                      · have p1443_0 := h1443c.1
                        have p1443_1 := h1443c.2.1
                        have p1443_2 := h1443c.2.2.1
                        have p1443_3 := h1443c.2.2.2
                        linarith only [h0, hlam, p1443_1]
                      · have p1443_0 := h1443c.1
                        have p1443_1 := h1443c.2.1
                        have p1443_2 := h1443c.2.2.1
                        have p1443_3 := h1443c.2.2.2
                        linarith only [h1337, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p1443_1, u3ehi1]
                      · have p1443_0 := h1443c.1
                        have p1443_1 := h1443c.2.1
                        have p1443_2 := h1443c.2.2.1
                        have p1443_3 := h1443c.2.2.2
                        linarith only [h0, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1443_1]
                      · have p1443_0 := h1443c.1
                        have p1443_1 := h1443c.2.1
                        have p1443_2 := h1443c.2.2.1
                        have p1443_3 := h1443c.2.2.2
                        linarith only [h0, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p1443_1]
                      · have p1443_0 := h1443c.1
                        have p1443_1 := h1443c.2.1
                        have p1443_2 := h1443c.2.2.1
                        have p1443_3 := h1443c.2.2.2
                        linarith only [h0, hc01, hc12, hlam, hphi, p1443_1]
                      · have p1443_0 := h1443c.1
                        have p1443_1 := h1443c.2.1
                        have p1443_2 := h1443c.2.2.1
                        have p1443_3 := h1443c.2.2.2
                        linarith only [hlam, p1443_0]
                      · have p1443_0 := h1443c.1
                        have p1443_1 := h1443c.2.1
                        have p1443_2 := h1443c.2.2.1
                        have p1443_3 := h1443c.2.2.2
                        linarith only [h0, h1337, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1443_1, u3ehi1]
                      · have p1443_0 := h1443c.1
                        have p1443_1 := h1443c.2.1
                        have p1443_2 := h1443c.2.2.1
                        have p1443_3 := h1443c.2.2.2
                        linarith only [h0, h1338, h1440, h1441, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1443_1, u3ehi2]
                      · have p1443_0 := h1443c.1
                        have p1443_1 := h1443c.2.1
                        have p1443_2 := h1443c.2.2.1
                        have p1443_3 := h1443c.2.2.2
                        linarith only [h0, h1337, h1407, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1443_1, u3ehi1]
                      · have p1443_0 := h1443c.1
                        have p1443_1 := h1443c.2.1
                        have p1443_2 := h1443c.2.2.1
                        have p1443_3 := h1443c.2.2.2
                        linarith only [h1337, hlam, p1443_1]
                      · have p1443_0 := h1443c.1
                        have p1443_1 := h1443c.2.1
                        have p1443_2 := h1443c.2.2.1
                        have p1443_3 := h1443c.2.2.2
                        linarith only [h1340, hlam, p1443_1]
                      · have p1443_0 := h1443c.1
                        have p1443_1 := h1443c.2.1
                        have p1443_2 := h1443c.2.2.1
                        have p1443_3 := h1443c.2.2.2
                        linarith only [hlam, p1443_0]
                      · have p1443_0 := h1443c.1
                        have p1443_1 := h1443c.2.1
                        have p1443_2 := h1443c.2.2.1
                        have p1443_3 := h1443c.2.2.2
                        linarith only [h1343, hlam, p1443_1]
                      · have p1443_0 := h1443c.1
                        have p1443_1 := h1443c.2.1
                        have p1443_2 := h1443c.2.2.1
                        have p1443_3 := h1443c.2.2.2
                        linarith only [h1407, hlam, p1443_1]
                      · have p1443_0 := h1443c.1
                        have p1443_1 := h1443c.2.1
                        have p1443_2 := h1443c.2.2.1
                        have p1443_3 := h1443c.2.2.2
                        linarith only [h1338, hlam, p1443_0]
                      · have p1443_0 := h1443c.1
                        have p1443_1 := h1443c.2.1
                        have p1443_2 := h1443c.2.2.1
                        have p1443_3 := h1443c.2.2.2
                        linarith only [h1341, hlam, p1443_0]
                      · have p1443_0 := h1443c.1
                        have p1443_1 := h1443c.2.1
                        have p1443_2 := h1443c.2.2.1
                        have p1443_3 := h1443c.2.2.2
                        linarith only [h1337, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p1443_1, u3ehi1]
                      · have p1443_0 := h1443c.1
                        have p1443_1 := h1443c.2.1
                        have p1443_2 := h1443c.2.2.1
                        have p1443_3 := h1443c.2.2.2
                        linarith only [hlam, p1443_0]
                      · have p1443_0 := h1443c.1
                        have p1443_1 := h1443c.2.1
                        have p1443_2 := h1443c.2.2.1
                        have p1443_3 := h1443c.2.2.2
                        linarith only [h1409, hlam, p1443_0]
                      · have p1443_0 := h1443c.1
                        have p1443_1 := h1443c.2.1
                        have p1443_2 := h1443c.2.2.1
                        have p1443_3 := h1443c.2.2.2
                        linarith only [h1339, hlam, p1443_0]
                      · have p1443_0 := h1443c.1
                        have p1443_1 := h1443c.2.1
                        have p1443_2 := h1443c.2.2.1
                        have p1443_3 := h1443c.2.2.2
                        linarith only [h1342, hlam, p1443_1]
                      · have p1443_0 := h1443c.1
                        have p1443_1 := h1443c.2.1
                        have p1443_2 := h1443c.2.2.1
                        have p1443_3 := h1443c.2.2.2
                        linarith only [h1337, hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p1443_1, u3ehi1]
                      · have p1443_0 := h1443c.1
                        have p1443_1 := h1443c.2.1
                        have p1443_2 := h1443c.2.2.1
                        have p1443_3 := h1443c.2.2.2
                        linarith only [h0, h1339, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1443_1]
                      · have p1443_0 := h1443c.1
                        have p1443_1 := h1443c.2.1
                        have p1443_2 := h1443c.2.2.1
                        have p1443_3 := h1443c.2.2.2
                        linarith only [hlam, p1443_0]
                  · linarith only [h0, h1337, h1440, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
          · linarith only [h0, h1339, h1342, hlam]
        · linarith only [h0, h1338, h1341, hlam]
      · linarith only [h0, h1337, h1340, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1473 | h1473
      · rcases m.htr 0 2 4 (by decide) (by decide) with h1474 | h1474
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1475 | h1475
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1476 | h1476
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1477 | h1477
              · linarith only [h1337, h1339, h1477, hlam]
              · linarith only [h1476, h1477, hc35, hlam, hphi, u3ehi3]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1480 | h1480
              · linarith only [h1476, h1480, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1482 | h1482
                · linarith only [h1338, h1339, h1482, hlam]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1484 | h1484
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1485 | h1485
                    · linarith only [h1473, h1476, h1482, h1485, hc45, hlam, hphi, ht34, u3ehi3]
                    · rcases h0bigk with h1487c | h1487c | h1487c | h1487c | h1487c | h1487c | h1487c | h1487c | h1487c | h1487c | h1487c | h1487c | h1487c | h1487c | h1487c | h1487c | h1487c | h1487c | h1487c | h1487c | h1487c | h1487c | h1487c | h1487c | h1487c
                      · have p1487_0 := h1487c.1
                        have p1487_1 := h1487c.2.1
                        have p1487_2 := h1487c.2.2.1
                        have p1487_3 := h1487c.2.2.2
                        linarith only [hlam, p1487_0]
                      · have p1487_0 := h1487c.1
                        have p1487_1 := h1487c.2.1
                        have p1487_2 := h1487c.2.2.1
                        have p1487_3 := h1487c.2.2.2
                        linarith only [h0, hlam, p1487_1]
                      · have p1487_0 := h1487c.1
                        have p1487_1 := h1487c.2.1
                        have p1487_2 := h1487c.2.2.1
                        have p1487_3 := h1487c.2.2.2
                        linarith only [hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p1487_1, u3ehi0]
                      · have p1487_0 := h1487c.1
                        have p1487_1 := h1487c.2.1
                        have p1487_2 := h1487c.2.2.1
                        have p1487_3 := h1487c.2.2.2
                        linarith only [h0, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1487_1]
                      · have p1487_0 := h1487c.1
                        have p1487_1 := h1487c.2.1
                        have p1487_2 := h1487c.2.2.1
                        have p1487_3 := h1487c.2.2.2
                        linarith only [h1339, hlam, p1487_1]
                      · have p1487_0 := h1487c.1
                        have p1487_1 := h1487c.2.1
                        have p1487_2 := h1487c.2.2.1
                        have p1487_3 := h1487c.2.2.2
                        linarith only [h0, hc01, hc12, hlam, hphi, p1487_1]
                      · have p1487_0 := h1487c.1
                        have p1487_1 := h1487c.2.1
                        have p1487_2 := h1487c.2.2.1
                        have p1487_3 := h1487c.2.2.2
                        linarith only [hlam, p1487_0]
                      · have p1487_0 := h1487c.1
                        have p1487_1 := h1487c.2.1
                        have p1487_2 := h1487c.2.2.1
                        have p1487_3 := h1487c.2.2.2
                        linarith only [h0, h1337, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1487_1, u3ehi1]
                      · have p1487_0 := h1487c.1
                        have p1487_1 := h1487c.2.1
                        have p1487_2 := h1487c.2.2.1
                        have p1487_3 := h1487c.2.2.2
                        linarith only [h0, h1338, h1484, h1485, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1487_1, u3ehi2]
                      · have p1487_0 := h1487c.1
                        have p1487_1 := h1487c.2.1
                        have p1487_2 := h1487c.2.2.1
                        have p1487_3 := h1487c.2.2.2
                        linarith only [h0, h1338, h1339, h1484, h1485, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1487_1, u3ehi2]
                      · have p1487_0 := h1487c.1
                        have p1487_1 := h1487c.2.1
                        have p1487_2 := h1487c.2.2.1
                        have p1487_3 := h1487c.2.2.2
                        linarith only [h1337, hlam, p1487_1]
                      · have p1487_0 := h1487c.1
                        have p1487_1 := h1487c.2.1
                        have p1487_2 := h1487c.2.2.1
                        have p1487_3 := h1487c.2.2.2
                        linarith only [h1473, hlam, p1487_1]
                      · have p1487_0 := h1487c.1
                        have p1487_1 := h1487c.2.1
                        have p1487_2 := h1487c.2.2.1
                        have p1487_3 := h1487c.2.2.2
                        linarith only [hlam, p1487_0]
                      · have p1487_0 := h1487c.1
                        have p1487_1 := h1487c.2.1
                        have p1487_2 := h1487c.2.2.1
                        have p1487_3 := h1487c.2.2.2
                        linarith only [h1476, hlam, p1487_1]
                      · have p1487_0 := h1487c.1
                        have p1487_1 := h1487c.2.1
                        have p1487_2 := h1487c.2.2.1
                        have p1487_3 := h1487c.2.2.2
                        linarith only [h1480, hlam, p1487_1]
                      · have p1487_0 := h1487c.1
                        have p1487_1 := h1487c.2.1
                        have p1487_2 := h1487c.2.2.1
                        have p1487_3 := h1487c.2.2.2
                        linarith only [h1338, hlam, p1487_0]
                      · have p1487_0 := h1487c.1
                        have p1487_1 := h1487c.2.1
                        have p1487_2 := h1487c.2.2.1
                        have p1487_3 := h1487c.2.2.2
                        linarith only [h1474, hlam, p1487_0]
                      · have p1487_0 := h1487c.1
                        have p1487_1 := h1487c.2.1
                        have p1487_2 := h1487c.2.2.1
                        have p1487_3 := h1487c.2.2.2
                        linarith only [h1337, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p1487_1, u3ehi1]
                      · have p1487_0 := h1487c.1
                        have p1487_1 := h1487c.2.1
                        have p1487_2 := h1487c.2.2.1
                        have p1487_3 := h1487c.2.2.2
                        linarith only [hlam, p1487_0]
                      · have p1487_0 := h1487c.1
                        have p1487_1 := h1487c.2.1
                        have p1487_2 := h1487c.2.2.1
                        have p1487_3 := h1487c.2.2.2
                        linarith only [h1482, hlam, p1487_0]
                      · have p1487_0 := h1487c.1
                        have p1487_1 := h1487c.2.1
                        have p1487_2 := h1487c.2.2.1
                        have p1487_3 := h1487c.2.2.2
                        linarith only [h1338, h1484, h1485, hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p1487_1, u3ehi2]
                      · have p1487_0 := h1487c.1
                        have p1487_1 := h1487c.2.1
                        have p1487_2 := h1487c.2.2.1
                        have p1487_3 := h1487c.2.2.2
                        linarith only [h1475, hlam, p1487_1]
                      · have p1487_0 := h1487c.1
                        have p1487_1 := h1487c.2.1
                        have p1487_2 := h1487c.2.2.1
                        have p1487_3 := h1487c.2.2.2
                        linarith only [h1337, h1480, hc35, hlam, hphi, p1487_1, u3ehi1]
                      · have p1487_0 := h1487c.1
                        have p1487_1 := h1487c.2.1
                        have p1487_2 := h1487c.2.2.1
                        have p1487_3 := h1487c.2.2.2
                        linarith only [h1482, hc04, hc45, hlam, hphi, p1487_1]
                      · have p1487_0 := h1487c.1
                        have p1487_1 := h1487c.2.1
                        have p1487_2 := h1487c.2.2.1
                        have p1487_3 := h1487c.2.2.2
                        linarith only [hlam, p1487_0]
                  · linarith only [h0, h1337, h1484, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1514 | h1514
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1515 | h1515
              · linarith only [h1337, h1339, h1515, hlam]
              · linarith only [h1514, h1515, hc35, hlam, hphi, u3ehi3]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1518 | h1518
              · linarith only [h1514, h1518, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1520 | h1520
                · linarith only [h0, h1338, h1475, h1520, hlam]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1522 | h1522
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1523 | h1523
                    · linarith only [h1473, h1475, h1523, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                    · rcases h0bigk with h1525c | h1525c | h1525c | h1525c | h1525c | h1525c | h1525c | h1525c | h1525c | h1525c | h1525c | h1525c | h1525c | h1525c | h1525c | h1525c | h1525c | h1525c | h1525c | h1525c | h1525c | h1525c | h1525c | h1525c | h1525c
                      · have p1525_0 := h1525c.1
                        have p1525_1 := h1525c.2.1
                        have p1525_2 := h1525c.2.2.1
                        have p1525_3 := h1525c.2.2.2
                        linarith only [hlam, p1525_0]
                      · have p1525_0 := h1525c.1
                        have p1525_1 := h1525c.2.1
                        have p1525_2 := h1525c.2.2.1
                        have p1525_3 := h1525c.2.2.2
                        linarith only [h0, hlam, p1525_1]
                      · have p1525_0 := h1525c.1
                        have p1525_1 := h1525c.2.1
                        have p1525_2 := h1525c.2.2.1
                        have p1525_3 := h1525c.2.2.2
                        linarith only [h0, h1475, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1525_1, u3ehi0]
                      · have p1525_0 := h1525c.1
                        have p1525_1 := h1525c.2.1
                        have p1525_2 := h1525c.2.2.1
                        have p1525_3 := h1525c.2.2.2
                        linarith only [h0, h1475, hc04, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1525_1]
                      · have p1525_0 := h1525c.1
                        have p1525_1 := h1525c.2.1
                        have p1525_2 := h1525c.2.2.1
                        have p1525_3 := h1525c.2.2.2
                        linarith only [h1339, hlam, p1525_1]
                      · have p1525_0 := h1525c.1
                        have p1525_1 := h1525c.2.1
                        have p1525_2 := h1525c.2.2.1
                        have p1525_3 := h1525c.2.2.2
                        linarith only [h1475, hc01, hc25, hlam, hphi, ht12, p1525_1]
                      · have p1525_0 := h1525c.1
                        have p1525_1 := h1525c.2.1
                        have p1525_2 := h1525c.2.2.1
                        have p1525_3 := h1525c.2.2.2
                        linarith only [hlam, p1525_0]
                      · have p1525_0 := h1525c.1
                        have p1525_1 := h1525c.2.1
                        have p1525_2 := h1525c.2.2.1
                        have p1525_3 := h1525c.2.2.2
                        linarith only [h1337, h1475, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1525_1, u3ehi1]
                      · have p1525_0 := h1525c.1
                        have p1525_1 := h1525c.2.1
                        have p1525_2 := h1525c.2.2.1
                        have p1525_3 := h1525c.2.2.2
                        linarith only [h1338, h1475, h1522, h1523, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1525_1, u3ehi2]
                      · have p1525_0 := h1525c.1
                        have p1525_1 := h1525c.2.1
                        have p1525_2 := h1525c.2.2.1
                        have p1525_3 := h1525c.2.2.2
                        linarith only [h1475, hlam, p1525_0]
                      · have p1525_0 := h1525c.1
                        have p1525_1 := h1525c.2.1
                        have p1525_2 := h1525c.2.2.1
                        have p1525_3 := h1525c.2.2.2
                        linarith only [h1337, hlam, p1525_1]
                      · have p1525_0 := h1525c.1
                        have p1525_1 := h1525c.2.1
                        have p1525_2 := h1525c.2.2.1
                        have p1525_3 := h1525c.2.2.2
                        linarith only [h1473, hlam, p1525_1]
                      · have p1525_0 := h1525c.1
                        have p1525_1 := h1525c.2.1
                        have p1525_2 := h1525c.2.2.1
                        have p1525_3 := h1525c.2.2.2
                        linarith only [hlam, p1525_0]
                      · have p1525_0 := h1525c.1
                        have p1525_1 := h1525c.2.1
                        have p1525_2 := h1525c.2.2.1
                        have p1525_3 := h1525c.2.2.2
                        linarith only [h1514, hlam, p1525_1]
                      · have p1525_0 := h1525c.1
                        have p1525_1 := h1525c.2.1
                        have p1525_2 := h1525c.2.2.1
                        have p1525_3 := h1525c.2.2.2
                        linarith only [h1518, hlam, p1525_1]
                      · have p1525_0 := h1525c.1
                        have p1525_1 := h1525c.2.1
                        have p1525_2 := h1525c.2.2.1
                        have p1525_3 := h1525c.2.2.2
                        linarith only [h1338, hlam, p1525_0]
                      · have p1525_0 := h1525c.1
                        have p1525_1 := h1525c.2.1
                        have p1525_2 := h1525c.2.2.1
                        have p1525_3 := h1525c.2.2.2
                        linarith only [h1474, hlam, p1525_0]
                      · have p1525_0 := h1525c.1
                        have p1525_1 := h1525c.2.1
                        have p1525_2 := h1525c.2.2.1
                        have p1525_3 := h1525c.2.2.2
                        linarith only [h1337, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p1525_1, u3ehi1]
                      · have p1525_0 := h1525c.1
                        have p1525_1 := h1525c.2.1
                        have p1525_2 := h1525c.2.2.1
                        have p1525_3 := h1525c.2.2.2
                        linarith only [hlam, p1525_0]
                      · have p1525_0 := h1525c.1
                        have p1525_1 := h1525c.2.1
                        have p1525_2 := h1525c.2.2.1
                        have p1525_3 := h1525c.2.2.2
                        linarith only [h1520, hlam, p1525_0]
                      · have p1525_0 := h1525c.1
                        have p1525_1 := h1525c.2.1
                        have p1525_2 := h1525c.2.2.1
                        have p1525_3 := h1525c.2.2.2
                        linarith only [h1337, hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p1525_1, u3ehi1]
                      · have p1525_0 := h1525c.1
                        have p1525_1 := h1525c.2.1
                        have p1525_2 := h1525c.2.2.1
                        have p1525_3 := h1525c.2.2.2
                        linarith only [h1475, hc02, hc25, hlam, hphi, p1525_1]
                      · have p1525_0 := h1525c.1
                        have p1525_1 := h1525c.2.1
                        have p1525_2 := h1525c.2.2.1
                        have p1525_3 := h1525c.2.2.2
                        linarith only [h1337, h1518, hc35, hlam, hphi, p1525_1, u3ehi1]
                      · have p1525_0 := h1525c.1
                        have p1525_1 := h1525c.2.1
                        have p1525_2 := h1525c.2.2.1
                        have p1525_3 := h1525c.2.2.2
                        linarith only [h1520, hc04, hc45, hlam, hphi, p1525_1]
                      · have p1525_0 := h1525c.1
                        have p1525_1 := h1525c.2.1
                        have p1525_2 := h1525c.2.2.1
                        have p1525_3 := h1525c.2.2.2
                        linarith only [hlam, p1525_0]
                  · linarith only [h0, h1337, h1474, h1522, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
        · linarith only [h0, h1338, h1474, hlam]
      · linarith only [h0, h1337, h1473, hlam]
  · rcases m.htr 0 1 5 (by decide) (by decide) with h1554 | h1554
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1555 | h1555
      · rcases m.htr 0 2 4 (by decide) (by decide) with h1556 | h1556
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1557 | h1557
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1558 | h1558
            · linarith only [h1337, h1338, h1558, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1560 | h1560
              · linarith only [h1558, h1560, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1562 | h1562
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1563 | h1563
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1564 | h1564
                    · linarith only [h1555, h1558, h1564, hlam]
                    · rcases h0bigk with h1566c | h1566c | h1566c | h1566c | h1566c | h1566c | h1566c | h1566c | h1566c | h1566c | h1566c | h1566c | h1566c | h1566c | h1566c | h1566c | h1566c | h1566c | h1566c | h1566c | h1566c | h1566c | h1566c | h1566c | h1566c
                      · have p1566_0 := h1566c.1
                        have p1566_1 := h1566c.2.1
                        have p1566_2 := h1566c.2.2.1
                        have p1566_3 := h1566c.2.2.2
                        linarith only [hlam, p1566_0]
                      · have p1566_0 := h1566c.1
                        have p1566_1 := h1566c.2.1
                        have p1566_2 := h1566c.2.2.1
                        have p1566_3 := h1566c.2.2.2
                        linarith only [h0, hlam, p1566_1]
                      · have p1566_0 := h1566c.1
                        have p1566_1 := h1566c.2.1
                        have p1566_2 := h1566c.2.2.1
                        have p1566_3 := h1566c.2.2.2
                        linarith only [hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p1566_1, u3ehi0]
                      · have p1566_0 := h1566c.1
                        have p1566_1 := h1566c.2.1
                        have p1566_2 := h1566c.2.2.1
                        have p1566_3 := h1566c.2.2.2
                        linarith only [h1338, hlam, p1566_1]
                      · have p1566_0 := h1566c.1
                        have p1566_1 := h1566c.2.1
                        have p1566_2 := h1566c.2.2.1
                        have p1566_3 := h1566c.2.2.2
                        linarith only [h1338, hc05, hc14, hlam, hphi, ht01, ht0b, ht5b, p1566_1]
                      · have p1566_0 := h1566c.1
                        have p1566_1 := h1566c.2.1
                        have p1566_2 := h1566c.2.2.1
                        have p1566_3 := h1566c.2.2.2
                        linarith only [h0, hc01, hc12, hlam, hphi, p1566_1]
                      · have p1566_0 := h1566c.1
                        have p1566_1 := h1566c.2.1
                        have p1566_2 := h1566c.2.2.1
                        have p1566_3 := h1566c.2.2.2
                        linarith only [hlam, p1566_0]
                      · have p1566_0 := h1566c.1
                        have p1566_1 := h1566c.2.1
                        have p1566_2 := h1566c.2.2.1
                        have p1566_3 := h1566c.2.2.2
                        linarith only [h0, h1555, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1566_1, u3ehi2]
                      · have p1566_0 := h1566c.1
                        have p1566_1 := h1566c.2.1
                        have p1566_2 := h1566c.2.2.1
                        have p1566_3 := h1566c.2.2.2
                        linarith only [h0, h1562, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1566_1]
                      · have p1566_0 := h1566c.1
                        have p1566_1 := h1566c.2.1
                        have p1566_2 := h1566c.2.2.1
                        have p1566_3 := h1566c.2.2.2
                        linarith only [h0, h1555, h1560, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1566_1, u3ehi2]
                      · have p1566_0 := h1566c.1
                        have p1566_1 := h1566c.2.1
                        have p1566_2 := h1566c.2.2.1
                        have p1566_3 := h1566c.2.2.2
                        linarith only [h1337, hlam, p1566_1]
                      · have p1566_0 := h1566c.1
                        have p1566_1 := h1566c.2.1
                        have p1566_2 := h1566c.2.2.1
                        have p1566_3 := h1566c.2.2.2
                        linarith only [h1555, hlam, p1566_1]
                      · have p1566_0 := h1566c.1
                        have p1566_1 := h1566c.2.1
                        have p1566_2 := h1566c.2.2.1
                        have p1566_3 := h1566c.2.2.2
                        linarith only [hlam, p1566_0]
                      · have p1566_0 := h1566c.1
                        have p1566_1 := h1566c.2.1
                        have p1566_2 := h1566c.2.2.1
                        have p1566_3 := h1566c.2.2.2
                        linarith only [h1558, hlam, p1566_1]
                      · have p1566_0 := h1566c.1
                        have p1566_1 := h1566c.2.1
                        have p1566_2 := h1566c.2.2.1
                        have p1566_3 := h1566c.2.2.2
                        linarith only [h1560, hlam, p1566_1]
                      · have p1566_0 := h1566c.1
                        have p1566_1 := h1566c.2.1
                        have p1566_2 := h1566c.2.2.1
                        have p1566_3 := h1566c.2.2.2
                        linarith only [h1337, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p1566_1, u3ehi1]
                      · have p1566_0 := h1566c.1
                        have p1566_1 := h1566c.2.1
                        have p1566_2 := h1566c.2.2.1
                        have p1566_3 := h1566c.2.2.2
                        linarith only [h1556, hlam, p1566_0]
                      · have p1566_0 := h1566c.1
                        have p1566_1 := h1566c.2.1
                        have p1566_2 := h1566c.2.2.1
                        have p1566_3 := h1566c.2.2.2
                        linarith only [h1555, h1558, hc34, hlam, hphi, p1566_1, u3ehi2]
                      · have p1566_0 := h1566c.1
                        have p1566_1 := h1566c.2.1
                        have p1566_2 := h1566c.2.2.1
                        have p1566_3 := h1566c.2.2.2
                        linarith only [hlam, p1566_0]
                      · have p1566_0 := h1566c.1
                        have p1566_1 := h1566c.2.1
                        have p1566_2 := h1566c.2.2.1
                        have p1566_3 := h1566c.2.2.2
                        linarith only [h1555, h1558, h1560, hc34, hlam, hphi, p1566_1, u3ehi2]
                      · have p1566_0 := h1566c.1
                        have p1566_1 := h1566c.2.1
                        have p1566_2 := h1566c.2.2.1
                        have p1566_3 := h1566c.2.2.2
                        linarith only [h1554, hlam, p1566_0]
                      · have p1566_0 := h1566c.1
                        have p1566_1 := h1566c.2.1
                        have p1566_2 := h1566c.2.2.1
                        have p1566_3 := h1566c.2.2.2
                        linarith only [h1557, hlam, p1566_1]
                      · have p1566_0 := h1566c.1
                        have p1566_1 := h1566c.2.1
                        have p1566_2 := h1566c.2.2.1
                        have p1566_3 := h1566c.2.2.2
                        linarith only [h1555, hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p1566_1, u3ehi2]
                      · have p1566_0 := h1566c.1
                        have p1566_1 := h1566c.2.1
                        have p1566_2 := h1566c.2.2.1
                        have p1566_3 := h1566c.2.2.2
                        linarith only [h1562, hlam, p1566_1]
                      · have p1566_0 := h1566c.1
                        have p1566_1 := h1566c.2.1
                        have p1566_2 := h1566c.2.2.1
                        have p1566_3 := h1566c.2.2.2
                        linarith only [hlam, p1566_0]
                  · linarith only [h0, h1556, h1563, hlam]
                · linarith only [h1337, h1338, h1562, hc45, hlam, hphi, ht34, u3ehi1]
          · linarith only [h0, h1554, h1557, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1595 | h1595
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1596 | h1596
            · linarith only [h0, h1337, h1556, h1596, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1598 | h1598
              · linarith only [h1596, h1598, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1600 | h1600
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1601 | h1601
                  · linarith only [h0, h1337, h1556, h1601, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi1]
                  · linarith only [h0, h1337, h1601, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
                · linarith only [h0, h1337, h1556, h1600, hc45, hlam, hphi, ht34, u3ehi1]
          · linarith only [h0, h1554, h1595, hlam]
      · linarith only [h0, h1337, h1555, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1607 | h1607
      · rcases m.htr 0 2 4 (by decide) (by decide) with h1608 | h1608
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1609 | h1609
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1610 | h1610
            · linarith only [h1337, h1338, h1610, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1612 | h1612
              · linarith only [h1610, h1612, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1614 | h1614
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1615 | h1615
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1616 | h1616
                    · linarith only [h1607, h1610, h1616, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
                    · rcases h0bigk with h1618c | h1618c | h1618c | h1618c | h1618c | h1618c | h1618c | h1618c | h1618c | h1618c | h1618c | h1618c | h1618c | h1618c | h1618c | h1618c | h1618c | h1618c | h1618c | h1618c | h1618c | h1618c | h1618c | h1618c | h1618c
                      · have p1618_0 := h1618c.1
                        have p1618_1 := h1618c.2.1
                        have p1618_2 := h1618c.2.2.1
                        have p1618_3 := h1618c.2.2.2
                        linarith only [hlam, p1618_0]
                      · have p1618_0 := h1618c.1
                        have p1618_1 := h1618c.2.1
                        have p1618_2 := h1618c.2.2.1
                        have p1618_3 := h1618c.2.2.2
                        linarith only [h0, hlam, p1618_1]
                      · have p1618_0 := h1618c.1
                        have p1618_1 := h1618c.2.1
                        have p1618_2 := h1618c.2.2.1
                        have p1618_3 := h1618c.2.2.2
                        linarith only [h1337, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p1618_1, u3ehi1]
                      · have p1618_0 := h1618c.1
                        have p1618_1 := h1618c.2.1
                        have p1618_2 := h1618c.2.2.1
                        have p1618_3 := h1618c.2.2.2
                        linarith only [h1338, hlam, p1618_1]
                      · have p1618_0 := h1618c.1
                        have p1618_1 := h1618c.2.1
                        have p1618_2 := h1618c.2.2.1
                        have p1618_3 := h1618c.2.2.2
                        linarith only [h1554, hlam, p1618_1]
                      · have p1618_0 := h1618c.1
                        have p1618_1 := h1618c.2.1
                        have p1618_2 := h1618c.2.2.1
                        have p1618_3 := h1618c.2.2.2
                        linarith only [h0, hc01, hc12, hlam, hphi, p1618_1]
                      · have p1618_0 := h1618c.1
                        have p1618_1 := h1618c.2.1
                        have p1618_2 := h1618c.2.2.1
                        have p1618_3 := h1618c.2.2.2
                        linarith only [hlam, p1618_0]
                      · have p1618_0 := h1618c.1
                        have p1618_1 := h1618c.2.1
                        have p1618_2 := h1618c.2.2.1
                        have p1618_3 := h1618c.2.2.2
                        linarith only [h0, h1337, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1618_1, u3ehi1]
                      · have p1618_0 := h1618c.1
                        have p1618_1 := h1618c.2.1
                        have p1618_2 := h1618c.2.2.1
                        have p1618_3 := h1618c.2.2.2
                        linarith only [h0, h1614, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1618_1]
                      · have p1618_0 := h1618c.1
                        have p1618_1 := h1618c.2.1
                        have p1618_2 := h1618c.2.2.1
                        have p1618_3 := h1618c.2.2.2
                        linarith only [h0, h1337, h1554, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1618_1, u3ehi1]
                      · have p1618_0 := h1618c.1
                        have p1618_1 := h1618c.2.1
                        have p1618_2 := h1618c.2.2.1
                        have p1618_3 := h1618c.2.2.2
                        linarith only [h1337, hlam, p1618_1]
                      · have p1618_0 := h1618c.1
                        have p1618_1 := h1618c.2.1
                        have p1618_2 := h1618c.2.2.1
                        have p1618_3 := h1618c.2.2.2
                        linarith only [h1607, hlam, p1618_1]
                      · have p1618_0 := h1618c.1
                        have p1618_1 := h1618c.2.1
                        have p1618_2 := h1618c.2.2.1
                        have p1618_3 := h1618c.2.2.2
                        linarith only [hlam, p1618_0]
                      · have p1618_0 := h1618c.1
                        have p1618_1 := h1618c.2.1
                        have p1618_2 := h1618c.2.2.1
                        have p1618_3 := h1618c.2.2.2
                        linarith only [h1610, hlam, p1618_1]
                      · have p1618_0 := h1618c.1
                        have p1618_1 := h1618c.2.1
                        have p1618_2 := h1618c.2.2.1
                        have p1618_3 := h1618c.2.2.2
                        linarith only [h1612, hlam, p1618_1]
                      · have p1618_0 := h1618c.1
                        have p1618_1 := h1618c.2.1
                        have p1618_2 := h1618c.2.2.1
                        have p1618_3 := h1618c.2.2.2
                        linarith only [h1337, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p1618_1, u3ehi1]
                      · have p1618_0 := h1618c.1
                        have p1618_1 := h1618c.2.1
                        have p1618_2 := h1618c.2.2.1
                        have p1618_3 := h1618c.2.2.2
                        linarith only [h1608, hlam, p1618_0]
                      · have p1618_0 := h1618c.1
                        have p1618_1 := h1618c.2.1
                        have p1618_2 := h1618c.2.2.1
                        have p1618_3 := h1618c.2.2.2
                        linarith only [h1337, h1610, hc34, hlam, hphi, p1618_1, u3ehi1]
                      · have p1618_0 := h1618c.1
                        have p1618_1 := h1618c.2.1
                        have p1618_2 := h1618c.2.2.1
                        have p1618_3 := h1618c.2.2.2
                        linarith only [hlam, p1618_0]
                      · have p1618_0 := h1618c.1
                        have p1618_1 := h1618c.2.1
                        have p1618_2 := h1618c.2.2.1
                        have p1618_3 := h1618c.2.2.2
                        linarith only [h1337, h1554, h1610, hc34, hlam, hphi, p1618_1, u3ehi1]
                      · have p1618_0 := h1618c.1
                        have p1618_1 := h1618c.2.1
                        have p1618_2 := h1618c.2.2.1
                        have p1618_3 := h1618c.2.2.2
                        linarith only [h1337, hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p1618_1, u3ehi1]
                      · have p1618_0 := h1618c.1
                        have p1618_1 := h1618c.2.1
                        have p1618_2 := h1618c.2.2.1
                        have p1618_3 := h1618c.2.2.2
                        linarith only [h1609, hlam, p1618_1]
                      · have p1618_0 := h1618c.1
                        have p1618_1 := h1618c.2.1
                        have p1618_2 := h1618c.2.2.1
                        have p1618_3 := h1618c.2.2.2
                        linarith only [h1337, h1612, hc35, hlam, hphi, p1618_1, u3ehi1]
                      · have p1618_0 := h1618c.1
                        have p1618_1 := h1618c.2.1
                        have p1618_2 := h1618c.2.2.1
                        have p1618_3 := h1618c.2.2.2
                        linarith only [h1614, hlam, p1618_1]
                      · have p1618_0 := h1618c.1
                        have p1618_1 := h1618c.2.1
                        have p1618_2 := h1618c.2.2.1
                        have p1618_3 := h1618c.2.2.2
                        linarith only [hlam, p1618_0]
                  · linarith only [h0, h1608, h1615, hlam]
                · linarith only [h1337, h1338, h1614, hc45, hlam, hphi, ht34, u3ehi1]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1646 | h1646
            · linarith only [h1337, h1338, h1646, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1648 | h1648
              · linarith only [h1646, h1648, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1650 | h1650
                · linarith only [h1608, h1609, h1650, hlam]
                · linarith only [h1337, h1338, h1650, hc45, hlam, hphi, ht34, u3ehi1]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1653 | h1653
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1654 | h1654
            · linarith only [h1337, h1554, h1608, h1653, h1654, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1656 | h1656
              · linarith only [h1654, h1656, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1658 | h1658
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1659 | h1659
                  · linarith only [h1337, h1554, h1608, h1653, h1659, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi1]
                  · linarith only [h0, h1337, h1659, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
                · linarith only [h1337, h1338, h1658, hc45, hlam, hphi, ht34, u3ehi1]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1663 | h1663
            · linarith only [h0, h1337, h1608, h1663, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1665 | h1665
              · linarith only [h1663, h1665, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1667 | h1667
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1668 | h1668
                  · linarith only [h0, h1337, h1608, h1668, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi1]
                  · linarith only [h0, h1337, h1668, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
                · linarith only [h1337, h1338, h1667, hc45, hlam, hphi, ht34, u3ehi1]
      · linarith only [h0, h1337, h1607, hlam]

set_option maxHeartbeats 5720000 in
set_option maxHeartbeats 5720000 in
theorem r1l7_20_11_13_14_H_I_L_I_L_R_L_I_x1_x1_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1337 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1673 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
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
  have h3ehi := hb3.1
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h1674 | h1674
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1675 | h1675
    · rcases m.htr 0 2 4 (by decide) (by decide) with h1676 | h1676
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1677 | h1677
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1678 | h1678
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1679 | h1679
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1680 | h1680
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1681 | h1681
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1682 | h1682
                  · rcases h0bigk with h1683c | h1683c | h1683c | h1683c | h1683c | h1683c | h1683c | h1683c | h1683c | h1683c | h1683c | h1683c | h1683c | h1683c | h1683c | h1683c | h1683c | h1683c | h1683c | h1683c | h1683c | h1683c | h1683c | h1683c | h1683c
                    · have p1683_0 := h1683c.1
                      have p1683_1 := h1683c.2.1
                      have p1683_2 := h1683c.2.2.1
                      have p1683_3 := h1683c.2.2.2
                      linarith only [hlam, p1683_0]
                    · have p1683_0 := h1683c.1
                      have p1683_1 := h1683c.2.1
                      have p1683_2 := h1683c.2.2.1
                      have p1683_3 := h1683c.2.2.2
                      linarith only [h0, hlam, p1683_1]
                    · have p1683_0 := h1683c.1
                      have p1683_1 := h1683c.2.1
                      have p1683_2 := h1683c.2.2.1
                      have p1683_3 := h1683c.2.2.2
                      linarith only [h1337, hlam, p1683_0]
                    · have p1683_0 := h1683c.1
                      have p1683_1 := h1683c.2.1
                      have p1683_2 := h1683c.2.2.1
                      have p1683_3 := h1683c.2.2.2
                      linarith only [h0, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1683_1]
                    · have p1683_0 := h1683c.1
                      have p1683_1 := h1683c.2.1
                      have p1683_2 := h1683c.2.2.1
                      have p1683_3 := h1683c.2.2.2
                      linarith only [h0, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p1683_1]
                    · have p1683_0 := h1683c.1
                      have p1683_1 := h1683c.2.1
                      have p1683_2 := h1683c.2.2.1
                      have p1683_3 := h1683c.2.2.2
                      linarith only [h1674, hc02, hc15, hlam, hphi, ht0b, ht5b, p1683_1]
                    · have p1683_0 := h1683c.1
                      have p1683_1 := h1683c.2.1
                      have p1683_2 := h1683c.2.2.1
                      have p1683_3 := h1683c.2.2.2
                      linarith only [hlam, p1683_0]
                    · have p1683_0 := h1683c.1
                      have p1683_1 := h1683c.2.1
                      have p1683_2 := h1683c.2.2.1
                      have p1683_3 := h1683c.2.2.2
                      linarith only [hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p1683_1, u3ehi0]
                    · have p1683_0 := h1683c.1
                      have p1683_1 := h1683c.2.1
                      have p1683_2 := h1683c.2.2.1
                      have p1683_3 := h1683c.2.2.2
                      linarith only [h0, h1680, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1683_1]
                    · have p1683_0 := h1683c.1
                      have p1683_1 := h1683c.2.1
                      have p1683_2 := h1683c.2.2.1
                      have p1683_3 := h1683c.2.2.2
                      linarith only [h0, h1679, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1683_1, u3ehi4]
                    · have p1683_0 := h1683c.1
                      have p1683_1 := h1683c.2.1
                      have p1683_2 := h1683c.2.2.1
                      have p1683_3 := h1683c.2.2.2
                      linarith only [h1673, hc03, hc14, hlam, hphi, ht0b, ht45, ht5b, p1683_1]
                    · have p1683_0 := h1683c.1
                      have p1683_1 := h1683c.2.1
                      have p1683_2 := h1683c.2.2.1
                      have p1683_3 := h1683c.2.2.2
                      linarith only [h1675, hlam, p1683_1]
                    · have p1683_0 := h1683c.1
                      have p1683_1 := h1683c.2.1
                      have p1683_2 := h1683c.2.2.1
                      have p1683_3 := h1683c.2.2.2
                      linarith only [hlam, p1683_0]
                    · have p1683_0 := h1683c.1
                      have p1683_1 := h1683c.2.1
                      have p1683_2 := h1683c.2.2.1
                      have p1683_3 := h1683c.2.2.2
                      linarith only [h0, h1675, h1678, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1683_1, u3ehi3]
                    · have p1683_0 := h1683c.1
                      have p1683_1 := h1683c.2.1
                      have p1683_2 := h1683c.2.2.1
                      have p1683_3 := h1683c.2.2.2
                      linarith only [h0, h1675, h1679, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1683_1, u3ehi4]
                    · have p1683_0 := h1683c.1
                      have p1683_1 := h1683c.2.1
                      have p1683_2 := h1683c.2.2.1
                      have p1683_3 := h1683c.2.2.2
                      linarith only [h1673, hlam, p1683_0]
                    · have p1683_0 := h1683c.1
                      have p1683_1 := h1683c.2.1
                      have p1683_2 := h1683c.2.2.1
                      have p1683_3 := h1683c.2.2.2
                      linarith only [h1676, hlam, p1683_0]
                    · have p1683_0 := h1683c.1
                      have p1683_1 := h1683c.2.1
                      have p1683_2 := h1683c.2.2.1
                      have p1683_3 := h1683c.2.2.2
                      linarith only [h1678, hlam, p1683_0]
                    · have p1683_0 := h1683c.1
                      have p1683_1 := h1683c.2.1
                      have p1683_2 := h1683c.2.2.1
                      have p1683_3 := h1683c.2.2.2
                      linarith only [hlam, p1683_0]
                    · have p1683_0 := h1683c.1
                      have p1683_1 := h1683c.2.1
                      have p1683_2 := h1683c.2.2.1
                      have p1683_3 := h1683c.2.2.2
                      linarith only [h1673, h1679, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p1683_1, u3ehi4]
                    · have p1683_0 := h1683c.1
                      have p1683_1 := h1683c.2.1
                      have p1683_2 := h1683c.2.2.1
                      have p1683_3 := h1683c.2.2.2
                      linarith only [h1674, hlam, p1683_0]
                    · have p1683_0 := h1683c.1
                      have p1683_1 := h1683c.2.1
                      have p1683_2 := h1683c.2.2.1
                      have p1683_3 := h1683c.2.2.2
                      linarith only [h1677, hlam, p1683_1]
                    · have p1683_0 := h1683c.1
                      have p1683_1 := h1683c.2.1
                      have p1683_2 := h1683c.2.2.1
                      have p1683_3 := h1683c.2.2.2
                      linarith only [h1679, hlam, p1683_0]
                    · have p1683_0 := h1683c.1
                      have p1683_1 := h1683c.2.1
                      have p1683_2 := h1683c.2.2.1
                      have p1683_3 := h1683c.2.2.2
                      linarith only [h1680, hlam, p1683_1]
                    · have p1683_0 := h1683c.1
                      have p1683_1 := h1683c.2.1
                      have p1683_2 := h1683c.2.2.1
                      have p1683_3 := h1683c.2.2.2
                      linarith only [hlam, p1683_0]
                  · rcases h0bigk with h1709c | h1709c | h1709c | h1709c | h1709c | h1709c | h1709c | h1709c | h1709c | h1709c | h1709c | h1709c | h1709c | h1709c | h1709c | h1709c | h1709c | h1709c | h1709c | h1709c | h1709c | h1709c | h1709c | h1709c | h1709c
                    · have p1709_0 := h1709c.1
                      have p1709_1 := h1709c.2.1
                      have p1709_2 := h1709c.2.2.1
                      have p1709_3 := h1709c.2.2.2
                      linarith only [hlam, p1709_0]
                    · have p1709_0 := h1709c.1
                      have p1709_1 := h1709c.2.1
                      have p1709_2 := h1709c.2.2.1
                      have p1709_3 := h1709c.2.2.2
                      linarith only [h0, hlam, p1709_1]
                    · have p1709_0 := h1709c.1
                      have p1709_1 := h1709c.2.1
                      have p1709_2 := h1709c.2.2.1
                      have p1709_3 := h1709c.2.2.2
                      linarith only [h1337, hlam, p1709_0]
                    · have p1709_0 := h1709c.1
                      have p1709_1 := h1709c.2.1
                      have p1709_2 := h1709c.2.2.1
                      have p1709_3 := h1709c.2.2.2
                      linarith only [h0, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1709_1]
                    · have p1709_0 := h1709c.1
                      have p1709_1 := h1709c.2.1
                      have p1709_2 := h1709c.2.2.1
                      have p1709_3 := h1709c.2.2.2
                      linarith only [h0, h1679, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1709_1, u3ehi4]
                    · have p1709_0 := h1709c.1
                      have p1709_1 := h1709c.2.1
                      have p1709_2 := h1709c.2.2.1
                      have p1709_3 := h1709c.2.2.2
                      linarith only [h0, hc01, hc12, hlam, hphi, p1709_1]
                    · have p1709_0 := h1709c.1
                      have p1709_1 := h1709c.2.1
                      have p1709_2 := h1709c.2.2.1
                      have p1709_3 := h1709c.2.2.2
                      linarith only [hlam, p1709_0]
                    · have p1709_0 := h1709c.1
                      have p1709_1 := h1709c.2.1
                      have p1709_2 := h1709c.2.2.1
                      have p1709_3 := h1709c.2.2.2
                      linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1709_1, u3ehi0]
                    · have p1709_0 := h1709c.1
                      have p1709_1 := h1709c.2.1
                      have p1709_2 := h1709c.2.2.1
                      have p1709_3 := h1709c.2.2.2
                      linarith only [h0, h1673, h1681, h1682, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1709_1, u3ehi2]
                    · have p1709_0 := h1709c.1
                      have p1709_1 := h1709c.2.1
                      have p1709_2 := h1709c.2.2.1
                      have p1709_3 := h1709c.2.2.2
                      linarith only [h0, h1679, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1709_1, u3ehi4]
                    · have p1709_0 := h1709c.1
                      have p1709_1 := h1709c.2.1
                      have p1709_2 := h1709c.2.2.1
                      have p1709_3 := h1709c.2.2.2
                      linarith only [h1673, h1681, h1682, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p1709_1, u3ehi2]
                    · have p1709_0 := h1709c.1
                      have p1709_1 := h1709c.2.1
                      have p1709_2 := h1709c.2.2.1
                      have p1709_3 := h1709c.2.2.2
                      linarith only [h1675, hlam, p1709_1]
                    · have p1709_0 := h1709c.1
                      have p1709_1 := h1709c.2.1
                      have p1709_2 := h1709c.2.2.1
                      have p1709_3 := h1709c.2.2.2
                      linarith only [hlam, p1709_0]
                    · have p1709_0 := h1709c.1
                      have p1709_1 := h1709c.2.1
                      have p1709_2 := h1709c.2.2.1
                      have p1709_3 := h1709c.2.2.2
                      linarith only [h0, h1673, h1675, h1681, h1682, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1709_1, u3ehi2]
                    · have p1709_0 := h1709c.1
                      have p1709_1 := h1709c.2.1
                      have p1709_2 := h1709c.2.2.1
                      have p1709_3 := h1709c.2.2.2
                      linarith only [h0, h1675, h1679, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1709_1, u3ehi4]
                    · have p1709_0 := h1709c.1
                      have p1709_1 := h1709c.2.1
                      have p1709_2 := h1709c.2.2.1
                      have p1709_3 := h1709c.2.2.2
                      linarith only [h1673, hlam, p1709_0]
                    · have p1709_0 := h1709c.1
                      have p1709_1 := h1709c.2.1
                      have p1709_2 := h1709c.2.2.1
                      have p1709_3 := h1709c.2.2.2
                      linarith only [h1676, hlam, p1709_0]
                    · have p1709_0 := h1709c.1
                      have p1709_1 := h1709c.2.1
                      have p1709_2 := h1709c.2.2.1
                      have p1709_3 := h1709c.2.2.2
                      linarith only [h1678, hlam, p1709_0]
                    · have p1709_0 := h1709c.1
                      have p1709_1 := h1709c.2.1
                      have p1709_2 := h1709c.2.2.1
                      have p1709_3 := h1709c.2.2.2
                      linarith only [hlam, p1709_0]
                    · have p1709_0 := h1709c.1
                      have p1709_1 := h1709c.2.1
                      have p1709_2 := h1709c.2.2.1
                      have p1709_3 := h1709c.2.2.2
                      linarith only [h1679, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p1709_1, u3ehi4]
                    · have p1709_0 := h1709c.1
                      have p1709_1 := h1709c.2.1
                      have p1709_2 := h1709c.2.2.1
                      have p1709_3 := h1709c.2.2.2
                      linarith only [h1674, hlam, p1709_0]
                    · have p1709_0 := h1709c.1
                      have p1709_1 := h1709c.2.1
                      have p1709_2 := h1709c.2.2.1
                      have p1709_3 := h1709c.2.2.2
                      linarith only [h1677, hlam, p1709_1]
                    · have p1709_0 := h1709c.1
                      have p1709_1 := h1709c.2.1
                      have p1709_2 := h1709c.2.2.1
                      have p1709_3 := h1709c.2.2.2
                      linarith only [h1679, hlam, p1709_0]
                    · have p1709_0 := h1709c.1
                      have p1709_1 := h1709c.2.1
                      have p1709_2 := h1709c.2.2.1
                      have p1709_3 := h1709c.2.2.2
                      linarith only [h1680, hlam, p1709_1]
                    · have p1709_0 := h1709c.1
                      have p1709_1 := h1709c.2.1
                      have p1709_2 := h1709c.2.2.1
                      have p1709_3 := h1709c.2.2.2
                      linarith only [hlam, p1709_0]
                · linarith only [h0, h1676, h1681, hlam]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1736 | h1736
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1737 | h1737
                  · rcases h0bigk with h1738c | h1738c | h1738c | h1738c | h1738c | h1738c | h1738c | h1738c | h1738c | h1738c | h1738c | h1738c | h1738c | h1738c | h1738c | h1738c | h1738c | h1738c | h1738c | h1738c | h1738c | h1738c | h1738c | h1738c | h1738c
                    · have p1738_0 := h1738c.1
                      have p1738_1 := h1738c.2.1
                      have p1738_2 := h1738c.2.2.1
                      have p1738_3 := h1738c.2.2.2
                      linarith only [hlam, p1738_0]
                    · have p1738_0 := h1738c.1
                      have p1738_1 := h1738c.2.1
                      have p1738_2 := h1738c.2.2.1
                      have p1738_3 := h1738c.2.2.2
                      linarith only [h0, hlam, p1738_1]
                    · have p1738_0 := h1738c.1
                      have p1738_1 := h1738c.2.1
                      have p1738_2 := h1738c.2.2.1
                      have p1738_3 := h1738c.2.2.2
                      linarith only [h1337, hlam, p1738_0]
                    · have p1738_0 := h1738c.1
                      have p1738_1 := h1738c.2.1
                      have p1738_2 := h1738c.2.2.1
                      have p1738_3 := h1738c.2.2.2
                      linarith only [h0, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1738_1]
                    · have p1738_0 := h1738c.1
                      have p1738_1 := h1738c.2.1
                      have p1738_2 := h1738c.2.2.1
                      have p1738_3 := h1738c.2.2.2
                      linarith only [h0, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p1738_1]
                    · have p1738_0 := h1738c.1
                      have p1738_1 := h1738c.2.1
                      have p1738_2 := h1738c.2.2.1
                      have p1738_3 := h1738c.2.2.2
                      linarith only [h0, hc01, hc12, hlam, hphi, p1738_1]
                    · have p1738_0 := h1738c.1
                      have p1738_1 := h1738c.2.1
                      have p1738_2 := h1738c.2.2.1
                      have p1738_3 := h1738c.2.2.2
                      linarith only [hlam, p1738_0]
                    · have p1738_0 := h1738c.1
                      have p1738_1 := h1738c.2.1
                      have p1738_2 := h1738c.2.2.1
                      have p1738_3 := h1738c.2.2.2
                      linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1738_1, u3ehi0]
                    · have p1738_0 := h1738c.1
                      have p1738_1 := h1738c.2.1
                      have p1738_2 := h1738c.2.2.1
                      have p1738_3 := h1738c.2.2.2
                      linarith only [h0, h1678, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1738_1, u3ehi3]
                    · have p1738_0 := h1738c.1
                      have p1738_1 := h1738c.2.1
                      have p1738_2 := h1738c.2.2.1
                      have p1738_3 := h1738c.2.2.2
                      linarith only [h0, h1679, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1738_1, u3ehi4]
                    · have p1738_0 := h1738c.1
                      have p1738_1 := h1738c.2.1
                      have p1738_2 := h1738c.2.2.1
                      have p1738_3 := h1738c.2.2.2
                      linarith only [h1673, h1678, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p1738_1, u3ehi3]
                    · have p1738_0 := h1738c.1
                      have p1738_1 := h1738c.2.1
                      have p1738_2 := h1738c.2.2.1
                      have p1738_3 := h1738c.2.2.2
                      linarith only [h1675, hlam, p1738_1]
                    · have p1738_0 := h1738c.1
                      have p1738_1 := h1738c.2.1
                      have p1738_2 := h1738c.2.2.1
                      have p1738_3 := h1738c.2.2.2
                      linarith only [hlam, p1738_0]
                    · have p1738_0 := h1738c.1
                      have p1738_1 := h1738c.2.1
                      have p1738_2 := h1738c.2.2.1
                      have p1738_3 := h1738c.2.2.2
                      linarith only [h0, h1675, h1678, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1738_1, u3ehi3]
                    · have p1738_0 := h1738c.1
                      have p1738_1 := h1738c.2.1
                      have p1738_2 := h1738c.2.2.1
                      have p1738_3 := h1738c.2.2.2
                      linarith only [h0, h1675, h1679, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1738_1, u3ehi4]
                    · have p1738_0 := h1738c.1
                      have p1738_1 := h1738c.2.1
                      have p1738_2 := h1738c.2.2.1
                      have p1738_3 := h1738c.2.2.2
                      linarith only [h1673, hlam, p1738_0]
                    · have p1738_0 := h1738c.1
                      have p1738_1 := h1738c.2.1
                      have p1738_2 := h1738c.2.2.1
                      have p1738_3 := h1738c.2.2.2
                      linarith only [h1676, hlam, p1738_0]
                    · have p1738_0 := h1738c.1
                      have p1738_1 := h1738c.2.1
                      have p1738_2 := h1738c.2.2.1
                      have p1738_3 := h1738c.2.2.2
                      linarith only [h1678, hlam, p1738_0]
                    · have p1738_0 := h1738c.1
                      have p1738_1 := h1738c.2.1
                      have p1738_2 := h1738c.2.2.1
                      have p1738_3 := h1738c.2.2.2
                      linarith only [hlam, p1738_0]
                    · have p1738_0 := h1738c.1
                      have p1738_1 := h1738c.2.1
                      have p1738_2 := h1738c.2.2.1
                      have p1738_3 := h1738c.2.2.2
                      linarith only [h1680, hlam, p1738_0]
                    · have p1738_0 := h1738c.1
                      have p1738_1 := h1738c.2.1
                      have p1738_2 := h1738c.2.2.1
                      have p1738_3 := h1738c.2.2.2
                      linarith only [h1674, hlam, p1738_0]
                    · have p1738_0 := h1738c.1
                      have p1738_1 := h1738c.2.1
                      have p1738_2 := h1738c.2.2.1
                      have p1738_3 := h1738c.2.2.2
                      linarith only [h1677, hlam, p1738_1]
                    · have p1738_0 := h1738c.1
                      have p1738_1 := h1738c.2.1
                      have p1738_2 := h1738c.2.2.1
                      have p1738_3 := h1738c.2.2.2
                      linarith only [h1679, hlam, p1738_0]
                    · have p1738_0 := h1738c.1
                      have p1738_1 := h1738c.2.1
                      have p1738_2 := h1738c.2.2.1
                      have p1738_3 := h1738c.2.2.2
                      linarith only [h1678, hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p1738_1, u3ehi3]
                    · have p1738_0 := h1738c.1
                      have p1738_1 := h1738c.2.1
                      have p1738_2 := h1738c.2.2.1
                      have p1738_3 := h1738c.2.2.2
                      linarith only [hlam, p1738_0]
                  · linarith only [h1678, h1680, h1737, hc45, hlam, hphi, ht34, u3ehi2]
                · linarith only [h0, h1676, h1736, hlam]
            · linarith only [h1678, h1679, hc35, hlam, hphi, u3ehi3]
          · linarith only [h1337, h1673, h1678, hlam]
        · linarith only [h0, h1674, h1677, hlam]
      · linarith only [h0, h1673, h1676, hlam]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h1770 | h1770
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1771 | h1771
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1772 | h1772
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1773 | h1773
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1774 | h1774
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1775 | h1775
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1776 | h1776
                  · rcases h0bigk with h1777c | h1777c | h1777c | h1777c | h1777c | h1777c | h1777c | h1777c | h1777c | h1777c | h1777c | h1777c | h1777c | h1777c | h1777c | h1777c | h1777c | h1777c | h1777c | h1777c | h1777c | h1777c | h1777c | h1777c | h1777c
                    · have p1777_0 := h1777c.1
                      have p1777_1 := h1777c.2.1
                      have p1777_2 := h1777c.2.2.1
                      have p1777_3 := h1777c.2.2.2
                      linarith only [hlam, p1777_0]
                    · have p1777_0 := h1777c.1
                      have p1777_1 := h1777c.2.1
                      have p1777_2 := h1777c.2.2.1
                      have p1777_3 := h1777c.2.2.2
                      linarith only [h0, hlam, p1777_1]
                    · have p1777_0 := h1777c.1
                      have p1777_1 := h1777c.2.1
                      have p1777_2 := h1777c.2.2.1
                      have p1777_3 := h1777c.2.2.2
                      linarith only [h1337, hlam, p1777_0]
                    · have p1777_0 := h1777c.1
                      have p1777_1 := h1777c.2.1
                      have p1777_2 := h1777c.2.2.1
                      have p1777_3 := h1777c.2.2.2
                      linarith only [h0, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1777_1]
                    · have p1777_0 := h1777c.1
                      have p1777_1 := h1777c.2.1
                      have p1777_2 := h1777c.2.2.1
                      have p1777_3 := h1777c.2.2.2
                      linarith only [h0, h1675, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1777_1]
                    · have p1777_0 := h1777c.1
                      have p1777_1 := h1777c.2.1
                      have p1777_2 := h1777c.2.2.1
                      have p1777_3 := h1777c.2.2.2
                      linarith only [h1675, hc01, hc23, hlam, hphi, ht12, p1777_1]
                    · have p1777_0 := h1777c.1
                      have p1777_1 := h1777c.2.1
                      have p1777_2 := h1777c.2.2.1
                      have p1777_3 := h1777c.2.2.2
                      linarith only [hlam, p1777_0]
                    · have p1777_0 := h1777c.1
                      have p1777_1 := h1777c.2.1
                      have p1777_2 := h1777c.2.2.1
                      have p1777_3 := h1777c.2.2.2
                      linarith only [h1675, hlam, p1777_0]
                    · have p1777_0 := h1777c.1
                      have p1777_1 := h1777c.2.1
                      have p1777_2 := h1777c.2.2.1
                      have p1777_3 := h1777c.2.2.2
                      linarith only [h1673, h1675, h1775, h1776, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1777_1, u3ehi3]
                    · have p1777_0 := h1777c.1
                      have p1777_1 := h1777c.2.1
                      have p1777_2 := h1777c.2.2.1
                      have p1777_3 := h1777c.2.2.2
                      linarith only [h1674, h1675, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1777_1]
                    · have p1777_0 := h1777c.1
                      have p1777_1 := h1777c.2.1
                      have p1777_2 := h1777c.2.2.1
                      have p1777_3 := h1777c.2.2.2
                      linarith only [h1673, h1775, h1776, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p1777_1, u3ehi3]
                    · have p1777_0 := h1777c.1
                      have p1777_1 := h1777c.2.1
                      have p1777_2 := h1777c.2.2.1
                      have p1777_3 := h1777c.2.2.2
                      linarith only [h1675, hc02, hc23, hlam, hphi, p1777_1]
                    · have p1777_0 := h1777c.1
                      have p1777_1 := h1777c.2.1
                      have p1777_2 := h1777c.2.2.1
                      have p1777_3 := h1777c.2.2.2
                      linarith only [hlam, p1777_0]
                    · have p1777_0 := h1777c.1
                      have p1777_1 := h1777c.2.1
                      have p1777_2 := h1777c.2.2.1
                      have p1777_3 := h1777c.2.2.2
                      linarith only [h1673, h1675, h1775, h1776, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1777_1, u3ehi3]
                    · have p1777_0 := h1777c.1
                      have p1777_1 := h1777c.2.1
                      have p1777_2 := h1777c.2.2.1
                      have p1777_3 := h1777c.2.2.2
                      linarith only [h1675, h1773, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1777_1, u3ehi4]
                    · have p1777_0 := h1777c.1
                      have p1777_1 := h1777c.2.1
                      have p1777_2 := h1777c.2.2.1
                      have p1777_3 := h1777c.2.2.2
                      linarith only [h1673, hlam, p1777_0]
                    · have p1777_0 := h1777c.1
                      have p1777_1 := h1777c.2.1
                      have p1777_2 := h1777c.2.2.1
                      have p1777_3 := h1777c.2.2.2
                      linarith only [h1770, hlam, p1777_0]
                    · have p1777_0 := h1777c.1
                      have p1777_1 := h1777c.2.1
                      have p1777_2 := h1777c.2.2.1
                      have p1777_3 := h1777c.2.2.2
                      linarith only [h1772, hlam, p1777_0]
                    · have p1777_0 := h1777c.1
                      have p1777_1 := h1777c.2.1
                      have p1777_2 := h1777c.2.2.1
                      have p1777_3 := h1777c.2.2.2
                      linarith only [hlam, p1777_0]
                    · have p1777_0 := h1777c.1
                      have p1777_1 := h1777c.2.1
                      have p1777_2 := h1777c.2.2.1
                      have p1777_3 := h1777c.2.2.2
                      linarith only [h1773, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p1777_1, u3ehi4]
                    · have p1777_0 := h1777c.1
                      have p1777_1 := h1777c.2.1
                      have p1777_2 := h1777c.2.2.1
                      have p1777_3 := h1777c.2.2.2
                      linarith only [h1674, hlam, p1777_0]
                    · have p1777_0 := h1777c.1
                      have p1777_1 := h1777c.2.1
                      have p1777_2 := h1777c.2.2.1
                      have p1777_3 := h1777c.2.2.2
                      linarith only [h1771, hlam, p1777_1]
                    · have p1777_0 := h1777c.1
                      have p1777_1 := h1777c.2.1
                      have p1777_2 := h1777c.2.2.1
                      have p1777_3 := h1777c.2.2.2
                      linarith only [h1773, hlam, p1777_0]
                    · have p1777_0 := h1777c.1
                      have p1777_1 := h1777c.2.1
                      have p1777_2 := h1777c.2.2.1
                      have p1777_3 := h1777c.2.2.2
                      linarith only [h1774, hlam, p1777_1]
                    · have p1777_0 := h1777c.1
                      have p1777_1 := h1777c.2.1
                      have p1777_2 := h1777c.2.2.1
                      have p1777_3 := h1777c.2.2.2
                      linarith only [hlam, p1777_0]
                  · linarith only [h0, h1674, h1675, h1773, h1776, hc34, hlam, hphi, u3ehi4]
                · linarith only [h1675, h1770, h1775, hc12, hc23, hlam, hphi]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1805 | h1805
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1806 | h1806
                  · rcases h0bigk with h1807c | h1807c | h1807c | h1807c | h1807c | h1807c | h1807c | h1807c | h1807c | h1807c | h1807c | h1807c | h1807c | h1807c | h1807c | h1807c | h1807c | h1807c | h1807c | h1807c | h1807c | h1807c | h1807c | h1807c | h1807c
                    · have p1807_0 := h1807c.1
                      have p1807_1 := h1807c.2.1
                      have p1807_2 := h1807c.2.2.1
                      have p1807_3 := h1807c.2.2.2
                      linarith only [hlam, p1807_0]
                    · have p1807_0 := h1807c.1
                      have p1807_1 := h1807c.2.1
                      have p1807_2 := h1807c.2.2.1
                      have p1807_3 := h1807c.2.2.2
                      linarith only [h0, hlam, p1807_1]
                    · have p1807_0 := h1807c.1
                      have p1807_1 := h1807c.2.1
                      have p1807_2 := h1807c.2.2.1
                      have p1807_3 := h1807c.2.2.2
                      linarith only [h1337, hlam, p1807_0]
                    · have p1807_0 := h1807c.1
                      have p1807_1 := h1807c.2.1
                      have p1807_2 := h1807c.2.2.1
                      have p1807_3 := h1807c.2.2.2
                      linarith only [h0, h1675, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1807_1]
                    · have p1807_0 := h1807c.1
                      have p1807_1 := h1807c.2.1
                      have p1807_2 := h1807c.2.2.1
                      have p1807_3 := h1807c.2.2.2
                      linarith only [h0, h1675, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1807_1]
                    · have p1807_0 := h1807c.1
                      have p1807_1 := h1807c.2.1
                      have p1807_2 := h1807c.2.2.1
                      have p1807_3 := h1807c.2.2.2
                      linarith only [h1673, h1675, h1805, h1806, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1807_1, u3ehi3]
                    · have p1807_0 := h1807c.1
                      have p1807_1 := h1807c.2.1
                      have p1807_2 := h1807c.2.2.1
                      have p1807_3 := h1807c.2.2.2
                      linarith only [hlam, p1807_0]
                    · have p1807_0 := h1807c.1
                      have p1807_1 := h1807c.2.1
                      have p1807_2 := h1807c.2.2.1
                      have p1807_3 := h1807c.2.2.2
                      linarith only [h1675, hlam, p1807_0]
                    · have p1807_0 := h1807c.1
                      have p1807_1 := h1807c.2.1
                      have p1807_2 := h1807c.2.2.1
                      have p1807_3 := h1807c.2.2.2
                      linarith only [h1673, h1675, h1805, h1806, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1807_1, u3ehi3]
                    · have p1807_0 := h1807c.1
                      have p1807_1 := h1807c.2.1
                      have p1807_2 := h1807c.2.2.1
                      have p1807_3 := h1807c.2.2.2
                      linarith only [h1674, h1675, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1807_1]
                    · have p1807_0 := h1807c.1
                      have p1807_1 := h1807c.2.1
                      have p1807_2 := h1807c.2.2.1
                      have p1807_3 := h1807c.2.2.2
                      linarith only [h1673, h1805, h1806, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p1807_1, u3ehi3]
                    · have p1807_0 := h1807c.1
                      have p1807_1 := h1807c.2.1
                      have p1807_2 := h1807c.2.2.1
                      have p1807_3 := h1807c.2.2.2
                      linarith only [h1675, hc02, hc23, hlam, hphi, p1807_1]
                    · have p1807_0 := h1807c.1
                      have p1807_1 := h1807c.2.1
                      have p1807_2 := h1807c.2.2.1
                      have p1807_3 := h1807c.2.2.2
                      linarith only [hlam, p1807_0]
                    · have p1807_0 := h1807c.1
                      have p1807_1 := h1807c.2.1
                      have p1807_2 := h1807c.2.2.1
                      have p1807_3 := h1807c.2.2.2
                      linarith only [h1673, h1675, h1805, h1806, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1807_1, u3ehi3]
                    · have p1807_0 := h1807c.1
                      have p1807_1 := h1807c.2.1
                      have p1807_2 := h1807c.2.2.1
                      have p1807_3 := h1807c.2.2.2
                      linarith only [h1675, h1773, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1807_1, u3ehi4]
                    · have p1807_0 := h1807c.1
                      have p1807_1 := h1807c.2.1
                      have p1807_2 := h1807c.2.2.1
                      have p1807_3 := h1807c.2.2.2
                      linarith only [h1673, hlam, p1807_0]
                    · have p1807_0 := h1807c.1
                      have p1807_1 := h1807c.2.1
                      have p1807_2 := h1807c.2.2.1
                      have p1807_3 := h1807c.2.2.2
                      linarith only [h1770, hlam, p1807_0]
                    · have p1807_0 := h1807c.1
                      have p1807_1 := h1807c.2.1
                      have p1807_2 := h1807c.2.2.1
                      have p1807_3 := h1807c.2.2.2
                      linarith only [h1772, hlam, p1807_0]
                    · have p1807_0 := h1807c.1
                      have p1807_1 := h1807c.2.1
                      have p1807_2 := h1807c.2.2.1
                      have p1807_3 := h1807c.2.2.2
                      linarith only [hlam, p1807_0]
                    · have p1807_0 := h1807c.1
                      have p1807_1 := h1807c.2.1
                      have p1807_2 := h1807c.2.2.1
                      have p1807_3 := h1807c.2.2.2
                      linarith only [h1774, hlam, p1807_0]
                    · have p1807_0 := h1807c.1
                      have p1807_1 := h1807c.2.1
                      have p1807_2 := h1807c.2.2.1
                      have p1807_3 := h1807c.2.2.2
                      linarith only [h1674, hlam, p1807_0]
                    · have p1807_0 := h1807c.1
                      have p1807_1 := h1807c.2.1
                      have p1807_2 := h1807c.2.2.1
                      have p1807_3 := h1807c.2.2.2
                      linarith only [h1771, hlam, p1807_1]
                    · have p1807_0 := h1807c.1
                      have p1807_1 := h1807c.2.1
                      have p1807_2 := h1807c.2.2.1
                      have p1807_3 := h1807c.2.2.2
                      linarith only [h1773, hlam, p1807_0]
                    · have p1807_0 := h1807c.1
                      have p1807_1 := h1807c.2.1
                      have p1807_2 := h1807c.2.2.1
                      have p1807_3 := h1807c.2.2.2
                      linarith only [h1673, h1805, h1806, hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p1807_1, u3ehi3]
                    · have p1807_0 := h1807c.1
                      have p1807_1 := h1807c.2.1
                      have p1807_2 := h1807c.2.2.1
                      have p1807_3 := h1807c.2.2.2
                      linarith only [hlam, p1807_0]
                  · linarith only [h1675, h1772, h1806, hlam]
                · linarith only [h0, h1674, h1770, h1772, h1774, h1805, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
            · linarith only [h1772, h1773, hc35, hlam, hphi, u3ehi3]
          · linarith only [h0, h1673, h1675, h1772, hlam]
        · linarith only [h0, h1674, h1771, hlam]
      · linarith only [h0, h1673, h1770, hlam]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1839 | h1839
    · rcases m.htr 0 2 4 (by decide) (by decide) with h1840 | h1840
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1841 | h1841
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1842 | h1842
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1843 | h1843
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1844 | h1844
              · linarith only [h1673, h1674, h1844, hlam]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1846 | h1846
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1847 | h1847
                  · rcases h0bigk with h1848c | h1848c | h1848c | h1848c | h1848c | h1848c | h1848c | h1848c | h1848c | h1848c | h1848c | h1848c | h1848c | h1848c | h1848c | h1848c | h1848c | h1848c | h1848c | h1848c | h1848c | h1848c | h1848c | h1848c | h1848c
                    · have p1848_0 := h1848c.1
                      have p1848_1 := h1848c.2.1
                      have p1848_2 := h1848c.2.2.1
                      have p1848_3 := h1848c.2.2.2
                      linarith only [hlam, p1848_0]
                    · have p1848_0 := h1848c.1
                      have p1848_1 := h1848c.2.1
                      have p1848_2 := h1848c.2.2.1
                      have p1848_3 := h1848c.2.2.2
                      linarith only [h0, hlam, p1848_1]
                    · have p1848_0 := h1848c.1
                      have p1848_1 := h1848c.2.1
                      have p1848_2 := h1848c.2.2.1
                      have p1848_3 := h1848c.2.2.2
                      linarith only [h1337, hlam, p1848_0]
                    · have p1848_0 := h1848c.1
                      have p1848_1 := h1848c.2.1
                      have p1848_2 := h1848c.2.2.1
                      have p1848_3 := h1848c.2.2.2
                      linarith only [h0, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1848_1]
                    · have p1848_0 := h1848c.1
                      have p1848_1 := h1848c.2.1
                      have p1848_2 := h1848c.2.2.1
                      have p1848_3 := h1848c.2.2.2
                      linarith only [h1674, hlam, p1848_1]
                    · have p1848_0 := h1848c.1
                      have p1848_1 := h1848c.2.1
                      have p1848_2 := h1848c.2.2.1
                      have p1848_3 := h1848c.2.2.2
                      linarith only [h0, hc01, hc12, hlam, hphi, p1848_1]
                    · have p1848_0 := h1848c.1
                      have p1848_1 := h1848c.2.1
                      have p1848_2 := h1848c.2.2.1
                      have p1848_3 := h1848c.2.2.2
                      linarith only [hlam, p1848_0]
                    · have p1848_0 := h1848c.1
                      have p1848_1 := h1848c.2.1
                      have p1848_2 := h1848c.2.2.1
                      have p1848_3 := h1848c.2.2.2
                      linarith only [h0, h1843, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1848_1, u3ehi4]
                    · have p1848_0 := h1848c.1
                      have p1848_1 := h1848c.2.1
                      have p1848_2 := h1848c.2.2.1
                      have p1848_3 := h1848c.2.2.2
                      linarith only [h0, h1842, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1848_1, u3ehi3]
                    · have p1848_0 := h1848c.1
                      have p1848_1 := h1848c.2.1
                      have p1848_2 := h1848c.2.2.1
                      have p1848_3 := h1848c.2.2.2
                      linarith only [h0, h1673, h1674, h1842, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1848_1, u3ehi3]
                    · have p1848_0 := h1848c.1
                      have p1848_1 := h1848c.2.1
                      have p1848_2 := h1848c.2.2.1
                      have p1848_3 := h1848c.2.2.2
                      linarith only [h1673, h1842, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p1848_1, u3ehi3]
                    · have p1848_0 := h1848c.1
                      have p1848_1 := h1848c.2.1
                      have p1848_2 := h1848c.2.2.1
                      have p1848_3 := h1848c.2.2.2
                      linarith only [h1839, hlam, p1848_1]
                    · have p1848_0 := h1848c.1
                      have p1848_1 := h1848c.2.1
                      have p1848_2 := h1848c.2.2.1
                      have p1848_3 := h1848c.2.2.2
                      linarith only [hlam, p1848_0]
                    · have p1848_0 := h1848c.1
                      have p1848_1 := h1848c.2.1
                      have p1848_2 := h1848c.2.2.1
                      have p1848_3 := h1848c.2.2.2
                      linarith only [h0, h1839, h1842, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1848_1, u3ehi3]
                    · have p1848_0 := h1848c.1
                      have p1848_1 := h1848c.2.1
                      have p1848_2 := h1848c.2.2.1
                      have p1848_3 := h1848c.2.2.2
                      linarith only [h0, h1673, h1674, h1839, h1842, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1848_1, u3ehi3]
                    · have p1848_0 := h1848c.1
                      have p1848_1 := h1848c.2.1
                      have p1848_2 := h1848c.2.2.1
                      have p1848_3 := h1848c.2.2.2
                      linarith only [h1673, hlam, p1848_0]
                    · have p1848_0 := h1848c.1
                      have p1848_1 := h1848c.2.1
                      have p1848_2 := h1848c.2.2.1
                      have p1848_3 := h1848c.2.2.2
                      linarith only [h1840, hlam, p1848_0]
                    · have p1848_0 := h1848c.1
                      have p1848_1 := h1848c.2.1
                      have p1848_2 := h1848c.2.2.1
                      have p1848_3 := h1848c.2.2.2
                      linarith only [h1842, hlam, p1848_0]
                    · have p1848_0 := h1848c.1
                      have p1848_1 := h1848c.2.1
                      have p1848_2 := h1848c.2.2.1
                      have p1848_3 := h1848c.2.2.2
                      linarith only [hlam, p1848_0]
                    · have p1848_0 := h1848c.1
                      have p1848_1 := h1848c.2.1
                      have p1848_2 := h1848c.2.2.1
                      have p1848_3 := h1848c.2.2.2
                      linarith only [h1844, hlam, p1848_0]
                    · have p1848_0 := h1848c.1
                      have p1848_1 := h1848c.2.1
                      have p1848_2 := h1848c.2.2.1
                      have p1848_3 := h1848c.2.2.2
                      linarith only [h1673, h1842, hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p1848_1, u3ehi3]
                    · have p1848_0 := h1848c.1
                      have p1848_1 := h1848c.2.1
                      have p1848_2 := h1848c.2.2.1
                      have p1848_3 := h1848c.2.2.2
                      linarith only [h1841, hlam, p1848_1]
                    · have p1848_0 := h1848c.1
                      have p1848_1 := h1848c.2.1
                      have p1848_2 := h1848c.2.2.1
                      have p1848_3 := h1848c.2.2.2
                      linarith only [h1843, hlam, p1848_0]
                    · have p1848_0 := h1848c.1
                      have p1848_1 := h1848c.2.1
                      have p1848_2 := h1848c.2.2.1
                      have p1848_3 := h1848c.2.2.2
                      linarith only [h1842, h1844, hc45, hlam, hphi, ht34, p1848_1, u3ehi3]
                    · have p1848_0 := h1848c.1
                      have p1848_1 := h1848c.2.1
                      have p1848_2 := h1848c.2.2.1
                      have p1848_3 := h1848c.2.2.2
                      linarith only [hlam, p1848_0]
                  · linarith only [h1842, h1844, h1847, hc45, hlam, hphi, ht34, u3ehi2]
                · linarith only [h0, h1840, h1846, hlam]
            · linarith only [h1842, h1843, hc35, hlam, hphi, u3ehi3]
          · linarith only [h1337, h1673, h1842, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1878 | h1878
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1879 | h1879
            · linarith only [h1839, h1841, h1879, hlam]
            · linarith only [h1878, h1879, hc35, hlam, hphi, u3ehi3]
          · linarith only [h1337, h1673, h1878, hlam]
      · linarith only [h0, h1673, h1840, hlam]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h1884 | h1884
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1885 | h1885
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1886 | h1886
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1887 | h1887
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1888 | h1888
              · linarith only [h1673, h1674, h1888, hlam]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1890 | h1890
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1891 | h1891
                  · rcases h0bigk with h1892c | h1892c | h1892c | h1892c | h1892c | h1892c | h1892c | h1892c | h1892c | h1892c | h1892c | h1892c | h1892c | h1892c | h1892c | h1892c | h1892c | h1892c | h1892c | h1892c | h1892c | h1892c | h1892c | h1892c | h1892c
                    · have p1892_0 := h1892c.1
                      have p1892_1 := h1892c.2.1
                      have p1892_2 := h1892c.2.2.1
                      have p1892_3 := h1892c.2.2.2
                      linarith only [hlam, p1892_0]
                    · have p1892_0 := h1892c.1
                      have p1892_1 := h1892c.2.1
                      have p1892_2 := h1892c.2.2.1
                      have p1892_3 := h1892c.2.2.2
                      linarith only [h0, hlam, p1892_1]
                    · have p1892_0 := h1892c.1
                      have p1892_1 := h1892c.2.1
                      have p1892_2 := h1892c.2.2.1
                      have p1892_3 := h1892c.2.2.2
                      linarith only [h1337, hlam, p1892_0]
                    · have p1892_0 := h1892c.1
                      have p1892_1 := h1892c.2.1
                      have p1892_2 := h1892c.2.2.1
                      have p1892_3 := h1892c.2.2.2
                      linarith only [h0, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1892_1]
                    · have p1892_0 := h1892c.1
                      have p1892_1 := h1892c.2.1
                      have p1892_2 := h1892c.2.2.1
                      have p1892_3 := h1892c.2.2.2
                      linarith only [h1674, hlam, p1892_1]
                    · have p1892_0 := h1892c.1
                      have p1892_1 := h1892c.2.1
                      have p1892_2 := h1892c.2.2.1
                      have p1892_3 := h1892c.2.2.2
                      linarith only [h1839, hc01, hc23, hlam, hphi, ht12, p1892_1]
                    · have p1892_0 := h1892c.1
                      have p1892_1 := h1892c.2.1
                      have p1892_2 := h1892c.2.2.1
                      have p1892_3 := h1892c.2.2.2
                      linarith only [hlam, p1892_0]
                    · have p1892_0 := h1892c.1
                      have p1892_1 := h1892c.2.1
                      have p1892_2 := h1892c.2.2.1
                      have p1892_3 := h1892c.2.2.2
                      linarith only [h1839, hlam, p1892_0]
                    · have p1892_0 := h1892c.1
                      have p1892_1 := h1892c.2.1
                      have p1892_2 := h1892c.2.2.1
                      have p1892_3 := h1892c.2.2.2
                      linarith only [h1673, h1839, h1890, h1891, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1892_1, u3ehi3]
                    · have p1892_0 := h1892c.1
                      have p1892_1 := h1892c.2.1
                      have p1892_2 := h1892c.2.2.1
                      have p1892_3 := h1892c.2.2.2
                      linarith only [h1839, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1892_1]
                    · have p1892_0 := h1892c.1
                      have p1892_1 := h1892c.2.1
                      have p1892_2 := h1892c.2.2.1
                      have p1892_3 := h1892c.2.2.2
                      linarith only [h1673, h1890, h1891, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p1892_1, u3ehi3]
                    · have p1892_0 := h1892c.1
                      have p1892_1 := h1892c.2.1
                      have p1892_2 := h1892c.2.2.1
                      have p1892_3 := h1892c.2.2.2
                      linarith only [h1839, hc02, hc23, hlam, hphi, p1892_1]
                    · have p1892_0 := h1892c.1
                      have p1892_1 := h1892c.2.1
                      have p1892_2 := h1892c.2.2.1
                      have p1892_3 := h1892c.2.2.2
                      linarith only [hlam, p1892_0]
                    · have p1892_0 := h1892c.1
                      have p1892_1 := h1892c.2.1
                      have p1892_2 := h1892c.2.2.1
                      have p1892_3 := h1892c.2.2.2
                      linarith only [h1673, h1839, h1890, h1891, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1892_1, u3ehi3]
                    · have p1892_0 := h1892c.1
                      have p1892_1 := h1892c.2.1
                      have p1892_2 := h1892c.2.2.1
                      have p1892_3 := h1892c.2.2.2
                      linarith only [h1673, h1674, h1839, h1890, h1891, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1892_1, u3ehi3]
                    · have p1892_0 := h1892c.1
                      have p1892_1 := h1892c.2.1
                      have p1892_2 := h1892c.2.2.1
                      have p1892_3 := h1892c.2.2.2
                      linarith only [h1673, hlam, p1892_0]
                    · have p1892_0 := h1892c.1
                      have p1892_1 := h1892c.2.1
                      have p1892_2 := h1892c.2.2.1
                      have p1892_3 := h1892c.2.2.2
                      linarith only [h1884, hlam, p1892_0]
                    · have p1892_0 := h1892c.1
                      have p1892_1 := h1892c.2.1
                      have p1892_2 := h1892c.2.2.1
                      have p1892_3 := h1892c.2.2.2
                      linarith only [h1886, hlam, p1892_0]
                    · have p1892_0 := h1892c.1
                      have p1892_1 := h1892c.2.1
                      have p1892_2 := h1892c.2.2.1
                      have p1892_3 := h1892c.2.2.2
                      linarith only [hlam, p1892_0]
                    · have p1892_0 := h1892c.1
                      have p1892_1 := h1892c.2.1
                      have p1892_2 := h1892c.2.2.1
                      have p1892_3 := h1892c.2.2.2
                      linarith only [h1888, hlam, p1892_0]
                    · have p1892_0 := h1892c.1
                      have p1892_1 := h1892c.2.1
                      have p1892_2 := h1892c.2.2.1
                      have p1892_3 := h1892c.2.2.2
                      linarith only [h1673, h1885, h1890, h1891, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p1892_1, u3ehi3]
                    · have p1892_0 := h1892c.1
                      have p1892_1 := h1892c.2.1
                      have p1892_2 := h1892c.2.2.1
                      have p1892_3 := h1892c.2.2.2
                      linarith only [h1885, hlam, p1892_1]
                    · have p1892_0 := h1892c.1
                      have p1892_1 := h1892c.2.1
                      have p1892_2 := h1892c.2.2.1
                      have p1892_3 := h1892c.2.2.2
                      linarith only [h1887, hlam, p1892_0]
                    · have p1892_0 := h1892c.1
                      have p1892_1 := h1892c.2.1
                      have p1892_2 := h1892c.2.2.1
                      have p1892_3 := h1892c.2.2.2
                      linarith only [h1673, h1839, h1885, h1890, h1891, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1892_1, u3ehi3]
                    · have p1892_0 := h1892c.1
                      have p1892_1 := h1892c.2.1
                      have p1892_2 := h1892c.2.2.1
                      have p1892_3 := h1892c.2.2.2
                      linarith only [hlam, p1892_0]
                  · linarith only [h1839, h1885, h1887, h1891, hc34, hlam, hphi, u3ehi4]
                · linarith only [h1839, h1884, h1890, hc12, hc23, hlam, hphi]
            · linarith only [h1886, h1887, hc35, hlam, hphi, u3ehi3]
          · linarith only [h0, h1673, h1839, h1886, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1922 | h1922
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1923 | h1923
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1924 | h1924
              · linarith only [h0, h1673, h1885, h1924, hlam]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1926 | h1926
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1927 | h1927
                  · rcases h0bigk with h1928c | h1928c | h1928c | h1928c | h1928c | h1928c | h1928c | h1928c | h1928c | h1928c | h1928c | h1928c | h1928c | h1928c | h1928c | h1928c | h1928c | h1928c | h1928c | h1928c | h1928c | h1928c | h1928c | h1928c | h1928c
                    · have p1928_0 := h1928c.1
                      have p1928_1 := h1928c.2.1
                      have p1928_2 := h1928c.2.2.1
                      have p1928_3 := h1928c.2.2.2
                      linarith only [hlam, p1928_0]
                    · have p1928_0 := h1928c.1
                      have p1928_1 := h1928c.2.1
                      have p1928_2 := h1928c.2.2.1
                      have p1928_3 := h1928c.2.2.2
                      linarith only [h0, hlam, p1928_1]
                    · have p1928_0 := h1928c.1
                      have p1928_1 := h1928c.2.1
                      have p1928_2 := h1928c.2.2.1
                      have p1928_3 := h1928c.2.2.2
                      linarith only [h1337, hlam, p1928_0]
                    · have p1928_0 := h1928c.1
                      have p1928_1 := h1928c.2.1
                      have p1928_2 := h1928c.2.2.1
                      have p1928_3 := h1928c.2.2.2
                      linarith only [h0, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1928_1]
                    · have p1928_0 := h1928c.1
                      have p1928_1 := h1928c.2.1
                      have p1928_2 := h1928c.2.2.1
                      have p1928_3 := h1928c.2.2.2
                      linarith only [h1674, hlam, p1928_1]
                    · have p1928_0 := h1928c.1
                      have p1928_1 := h1928c.2.1
                      have p1928_2 := h1928c.2.2.1
                      have p1928_3 := h1928c.2.2.2
                      linarith only [h1885, hc01, hc25, hlam, hphi, ht12, p1928_1]
                    · have p1928_0 := h1928c.1
                      have p1928_1 := h1928c.2.1
                      have p1928_2 := h1928c.2.2.1
                      have p1928_3 := h1928c.2.2.2
                      linarith only [hlam, p1928_0]
                    · have p1928_0 := h1928c.1
                      have p1928_1 := h1928c.2.1
                      have p1928_2 := h1928c.2.2.1
                      have p1928_3 := h1928c.2.2.2
                      linarith only [h1839, hlam, p1928_0]
                    · have p1928_0 := h1928c.1
                      have p1928_1 := h1928c.2.1
                      have p1928_2 := h1928c.2.2.1
                      have p1928_3 := h1928c.2.2.2
                      linarith only [h1673, h1885, h1926, h1927, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1928_1, u3ehi3]
                    · have p1928_0 := h1928c.1
                      have p1928_1 := h1928c.2.1
                      have p1928_2 := h1928c.2.2.1
                      have p1928_3 := h1928c.2.2.2
                      linarith only [h1885, hlam, p1928_0]
                    · have p1928_0 := h1928c.1
                      have p1928_1 := h1928c.2.1
                      have p1928_2 := h1928c.2.2.1
                      have p1928_3 := h1928c.2.2.2
                      linarith only [h1673, h1839, h1926, h1927, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1928_1, u3ehi3]
                    · have p1928_0 := h1928c.1
                      have p1928_1 := h1928c.2.1
                      have p1928_2 := h1928c.2.2.1
                      have p1928_3 := h1928c.2.2.2
                      linarith only [h1839, hc02, hc23, hlam, hphi, p1928_1]
                    · have p1928_0 := h1928c.1
                      have p1928_1 := h1928c.2.1
                      have p1928_2 := h1928c.2.2.1
                      have p1928_3 := h1928c.2.2.2
                      linarith only [hlam, p1928_0]
                    · have p1928_0 := h1928c.1
                      have p1928_1 := h1928c.2.1
                      have p1928_2 := h1928c.2.2.1
                      have p1928_3 := h1928c.2.2.2
                      linarith only [h1673, h1839, h1926, h1927, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1928_1, u3ehi3]
                    · have p1928_0 := h1928c.1
                      have p1928_1 := h1928c.2.1
                      have p1928_2 := h1928c.2.2.1
                      have p1928_3 := h1928c.2.2.2
                      linarith only [h1673, h1674, h1839, h1926, h1927, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1928_1, u3ehi3]
                    · have p1928_0 := h1928c.1
                      have p1928_1 := h1928c.2.1
                      have p1928_2 := h1928c.2.2.1
                      have p1928_3 := h1928c.2.2.2
                      linarith only [h1673, hlam, p1928_0]
                    · have p1928_0 := h1928c.1
                      have p1928_1 := h1928c.2.1
                      have p1928_2 := h1928c.2.2.1
                      have p1928_3 := h1928c.2.2.2
                      linarith only [h1884, hlam, p1928_0]
                    · have p1928_0 := h1928c.1
                      have p1928_1 := h1928c.2.1
                      have p1928_2 := h1928c.2.2.1
                      have p1928_3 := h1928c.2.2.2
                      linarith only [h1922, hlam, p1928_0]
                    · have p1928_0 := h1928c.1
                      have p1928_1 := h1928c.2.1
                      have p1928_2 := h1928c.2.2.1
                      have p1928_3 := h1928c.2.2.2
                      linarith only [hlam, p1928_0]
                    · have p1928_0 := h1928c.1
                      have p1928_1 := h1928c.2.1
                      have p1928_2 := h1928c.2.2.1
                      have p1928_3 := h1928c.2.2.2
                      linarith only [h1924, hlam, p1928_0]
                    · have p1928_0 := h1928c.1
                      have p1928_1 := h1928c.2.1
                      have p1928_2 := h1928c.2.2.1
                      have p1928_3 := h1928c.2.2.2
                      linarith only [h1673, h1926, h1927, hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p1928_1, u3ehi3]
                    · have p1928_0 := h1928c.1
                      have p1928_1 := h1928c.2.1
                      have p1928_2 := h1928c.2.2.1
                      have p1928_3 := h1928c.2.2.2
                      linarith only [h0, h1673, h1885, h1926, h1927, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1928_1, u3ehi3]
                    · have p1928_0 := h1928c.1
                      have p1928_1 := h1928c.2.1
                      have p1928_2 := h1928c.2.2.1
                      have p1928_3 := h1928c.2.2.2
                      linarith only [h1923, hlam, p1928_0]
                    · have p1928_0 := h1928c.1
                      have p1928_1 := h1928c.2.1
                      have p1928_2 := h1928c.2.2.1
                      have p1928_3 := h1928c.2.2.2
                      linarith only [h1673, h1924, h1926, h1927, hc45, hlam, hphi, ht34, p1928_1, u3ehi3]
                    · have p1928_0 := h1928c.1
                      have p1928_1 := h1928c.2.1
                      have p1928_2 := h1928c.2.2.1
                      have p1928_3 := h1928c.2.2.2
                      linarith only [hlam, p1928_0]
                  · linarith only [h1839, h1923, h1927, hc34, hlam, hphi, u3ehi4]
                · linarith only [h0, h1673, h1884, h1926, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b]
            · linarith only [h1922, h1923, hc35, hlam, hphi, u3ehi3]
          · linarith only [h0, h1673, h1839, h1922, hlam]
      · linarith only [h0, h1673, h1884, hlam]

end R2N4
