import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_16S0
import Jsp000404.R1LeavesN7_16S1

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5636000 in
theorem r1l7_21_15_H_I_L_I_s6_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h9 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
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
  have h1emin := hb1.2.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  rcases m.htr 1 2 3 (by decide) (by decide) with h10 | h10
  · exact r1l7_21_15_H_I_L_I_s6_x0_x0_x0_x0 m hb1 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 h7 h8 h9 h10
  · exact r1l7_21_15_H_I_L_I_s6_x0_x0_x0_x1 m hb1 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 h7 h8 h9 h10

set_option maxHeartbeats 5636000 in
theorem r1l7_21_15_H_I_L_I_s6_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h9 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
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
  have h1emin := hb1.2.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  rcases m.htr 1 2 3 (by decide) (by decide) with h1365 | h1365
  · rcases m.htr 1 2 4 (by decide) (by decide) with h1366 | h1366
    · rcases m.htr 1 2 5 (by decide) (by decide) with h1367 | h1367
      · rcases m.htr 1 3 4 (by decide) (by decide) with h1368 | h1368
        · rcases m.htr 1 3 5 (by decide) (by decide) with h1369 | h1369
          · rcases m.htr 1 4 5 (by decide) (by decide) with h1370 | h1370
            · linarith only [h1370, h2, h9, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1372 | h1372
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1373 | h1373
                · rcases m.htr 2 4 5 (by decide) (by decide) with h1374 | h1374
                  · linarith only [h1366, h1374, h2, h9, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1376 | h1376
                    · linarith only [h1376, h7, h9, hlam]
                    · rcases h1bigk with h1378c | h1378c | h1378c | h1378c | h1378c | h1378c | h1378c | h1378c | h1378c | h1378c | h1378c | h1378c | h1378c | h1378c | h1378c | h1378c | h1378c | h1378c | h1378c | h1378c | h1378c | h1378c | h1378c | h1378c | h1378c
                      · have p1378_0 := h1378c.1
                        have p1378_1 := h1378c.2.1
                        have p1378_2 := h1378c.2.2.1
                        have p1378_3 := h1378c.2.2.2
                        linarith only [hlam, p1378_0]
                      · have p1378_0 := h1378c.1
                        have p1378_1 := h1378c.2.1
                        have p1378_2 := h1378c.2.2.1
                        have p1378_3 := h1378c.2.2.2
                        linarith only [h1365, h1373, h1376, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1378_1]
                      · have p1378_0 := h1378c.1
                        have p1378_1 := h1378c.2.1
                        have p1378_2 := h1378c.2.2.1
                        have p1378_3 := h1378c.2.2.2
                        linarith only [h1365, h1373, h1376, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1378_1]
                      · have p1378_0 := h1378c.1
                        have p1378_1 := h1378c.2.1
                        have p1378_2 := h1378c.2.2.1
                        have p1378_3 := h1378c.2.2.2
                        rcases p1378_3 (m.d 0 1) (by simp) with h1382 | h1382
                        · rcases p1378_3 (m.d 1 2) (by simp) with h1383 | h1383
                          · linarith only [h0, h1383, hlam]
                          · linarith only [h1366, h1383, hlam]
                        · linarith only [h1382, hlam, p1378_0]
                      · have p1378_0 := h1378c.1
                        have p1378_1 := h1378c.2.1
                        have p1378_2 := h1378c.2.2.1
                        have p1378_3 := h1378c.2.2.2
                        rcases p1378_3 (m.d 0 1) (by simp) with h1387 | h1387
                        · rcases p1378_3 (m.d 1 2) (by simp) with h1388 | h1388
                          · linarith only [h0, h1388, hlam]
                          · linarith only [h1367, h1388, hlam]
                        · linarith only [h1387, hlam, p1378_0]
                      · have p1378_0 := h1378c.1
                        have p1378_1 := h1378c.2.1
                        have p1378_2 := h1378c.2.2.1
                        have p1378_3 := h1378c.2.2.2
                        linarith only [h0, hlam, p1378_0]
                      · have p1378_0 := h1378c.1
                        have p1378_1 := h1378c.2.1
                        have p1378_2 := h1378c.2.2.1
                        have p1378_3 := h1378c.2.2.2
                        linarith only [hlam, p1378_0]
                      · have p1378_0 := h1378c.1
                        have p1378_1 := h1378c.2.1
                        have p1378_2 := h1378c.2.2.1
                        have p1378_3 := h1378c.2.2.2
                        linarith only [h1365, h1373, h1376, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1378_1]
                      · have p1378_0 := h1378c.1
                        have p1378_1 := h1378c.2.1
                        have p1378_2 := h1378c.2.2.1
                        have p1378_3 := h1378c.2.2.2
                        linarith only [h0, h1366, h1372, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1378_1]
                      · have p1378_0 := h1378c.1
                        have p1378_1 := h1378c.2.1
                        have p1378_2 := h1378c.2.2.1
                        have p1378_3 := h1378c.2.2.2
                        linarith only [h0, hc01, hc15, hlam, hphi, ht0b, ht5b, p1378_1]
                      · have p1378_0 := h1378c.1
                        have p1378_1 := h1378c.2.1
                        have p1378_2 := h1378c.2.2.1
                        have p1378_3 := h1378c.2.2.2
                        linarith only [h1, hlam, p1378_0]
                      · have p1378_0 := h1378c.1
                        have p1378_1 := h1378c.2.1
                        have p1378_2 := h1378c.2.2.1
                        have p1378_3 := h1378c.2.2.2
                        linarith only [h1365, hlam, p1378_1]
                      · have p1378_0 := h1378c.1
                        have p1378_1 := h1378c.2.1
                        have p1378_2 := h1378c.2.2.1
                        have p1378_3 := h1378c.2.2.2
                        linarith only [hlam, p1378_0]
                      · have p1378_0 := h1378c.1
                        have p1378_1 := h1378c.2.1
                        have p1378_2 := h1378c.2.2.1
                        have p1378_3 := h1378c.2.2.2
                        linarith only [h1, h1366, h1372, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1378_1]
                      · have p1378_0 := h1378c.1
                        have p1378_1 := h1378c.2.1
                        have p1378_2 := h1378c.2.2.1
                        have p1378_3 := h1378c.2.2.2
                        linarith only [h0, h1365, h1367, hc01, hc25, hlam, hphi, ht0b, ht5b, p1378_1]
                      · have p1378_0 := h1378c.1
                        have p1378_1 := h1378c.2.1
                        have p1378_2 := h1378c.2.2.1
                        have p1378_3 := h1378c.2.2.2
                        linarith only [h2, hlam, p1378_0]
                      · have p1378_0 := h1378c.1
                        have p1378_1 := h1378c.2.1
                        have p1378_2 := h1378c.2.2.1
                        have p1378_3 := h1378c.2.2.2
                        linarith only [h1366, hlam, p1378_1]
                      · have p1378_0 := h1378c.1
                        have p1378_1 := h1378c.2.1
                        have p1378_2 := h1378c.2.2.1
                        have p1378_3 := h1378c.2.2.2
                        linarith only [h1368, hlam, p1378_0]
                      · have p1378_0 := h1378c.1
                        have p1378_1 := h1378c.2.1
                        have p1378_2 := h1378c.2.2.1
                        have p1378_3 := h1378c.2.2.2
                        linarith only [hlam, p1378_0]
                      · have p1378_0 := h1378c.1
                        have p1378_1 := h1378c.2.1
                        have p1378_2 := h1378c.2.2.1
                        have p1378_3 := h1378c.2.2.2
                        linarith only [h1370, hlam, p1378_1]
                      · have p1378_0 := h1378c.1
                        have p1378_1 := h1378c.2.1
                        have p1378_2 := h1378c.2.2.1
                        have p1378_3 := h1378c.2.2.2
                        linarith only [h3, hlam, p1378_0]
                      · have p1378_0 := h1378c.1
                        have p1378_1 := h1378c.2.1
                        have p1378_2 := h1378c.2.2.1
                        have p1378_3 := h1378c.2.2.2
                        linarith only [h1367, hlam, p1378_1]
                      · have p1378_0 := h1378c.1
                        have p1378_1 := h1378c.2.1
                        have p1378_2 := h1378c.2.2.1
                        have p1378_3 := h1378c.2.2.2
                        linarith only [h1369, hlam, p1378_0]
                      · have p1378_0 := h1378c.1
                        have p1378_1 := h1378c.2.1
                        have p1378_2 := h1378c.2.2.1
                        have p1378_3 := h1378c.2.2.2
                        linarith only [h1366, h1372, h3, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1378_1]
                      · have p1378_0 := h1378c.1
                        have p1378_1 := h1378c.2.1
                        have p1378_2 := h1378c.2.2.1
                        have p1378_3 := h1378c.2.2.2
                        linarith only [hlam, p1378_0]
                · linarith only [h0, h1365, h1369, h1372, h1373, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1413 | h1413
                · linarith only [h0, h1365, h1368, h1372, h1413, hc01, hc35, hlam, hphi, ht0b, ht5b]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h1415 | h1415
                  · linarith only [h0, h1365, h1368, h1372, h1415, h9, hc01, hc04, hlam, hphi, ht0b, ht45, ht5b]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1417 | h1417
                    · linarith only [h1368, h1417, h2, h9, hlam]
                    · rcases h1bigk with h1419c | h1419c | h1419c | h1419c | h1419c | h1419c | h1419c | h1419c | h1419c | h1419c | h1419c | h1419c | h1419c | h1419c | h1419c | h1419c | h1419c | h1419c | h1419c | h1419c | h1419c | h1419c | h1419c | h1419c | h1419c
                      · have p1419_0 := h1419c.1
                        have p1419_1 := h1419c.2.1
                        have p1419_2 := h1419c.2.2.1
                        have p1419_3 := h1419c.2.2.2
                        linarith only [hlam, p1419_0]
                      · have p1419_0 := h1419c.1
                        have p1419_1 := h1419c.2.1
                        have p1419_2 := h1419c.2.2.1
                        have p1419_3 := h1419c.2.2.2
                        linarith only [h1365, h1369, h1372, h1417, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1419_1]
                      · have p1419_0 := h1419c.1
                        have p1419_1 := h1419c.2.1
                        have p1419_2 := h1419c.2.2.1
                        have p1419_3 := h1419c.2.2.2
                        linarith only [h1369, h1372, h1417, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1419_1]
                      · have p1419_0 := h1419c.1
                        have p1419_1 := h1419c.2.1
                        have p1419_2 := h1419c.2.2.1
                        have p1419_3 := h1419c.2.2.2
                        linarith only [h1368, h1372, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1419_1]
                      · have p1419_0 := h1419c.1
                        have p1419_1 := h1419c.2.1
                        have p1419_2 := h1419c.2.2.1
                        have p1419_3 := h1419c.2.2.2
                        linarith only [h1368, h1370, h1372, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1419_1]
                      · have p1419_0 := h1419c.1
                        have p1419_1 := h1419c.2.1
                        have p1419_2 := h1419c.2.2.1
                        have p1419_3 := h1419c.2.2.2
                        linarith only [h0, hlam, p1419_0]
                      · have p1419_0 := h1419c.1
                        have p1419_1 := h1419c.2.1
                        have p1419_2 := h1419c.2.2.1
                        have p1419_3 := h1419c.2.2.2
                        linarith only [hlam, p1419_0]
                      · have p1419_0 := h1419c.1
                        have p1419_1 := h1419c.2.1
                        have p1419_2 := h1419c.2.2.1
                        have p1419_3 := h1419c.2.2.2
                        linarith only [h1369, h1372, h1417, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1419_1]
                      · have p1419_0 := h1419c.1
                        have p1419_1 := h1419c.2.1
                        have p1419_2 := h1419c.2.2.1
                        have p1419_3 := h1419c.2.2.2
                        linarith only [h0, h1368, h1372, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1419_1]
                      · have p1419_0 := h1419c.1
                        have p1419_1 := h1419c.2.1
                        have p1419_2 := h1419c.2.2.1
                        have p1419_3 := h1419c.2.2.2
                        linarith only [h0, h1368, h1370, h1372, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1419_1]
                      · have p1419_0 := h1419c.1
                        have p1419_1 := h1419c.2.1
                        have p1419_2 := h1419c.2.2.1
                        have p1419_3 := h1419c.2.2.2
                        linarith only [h1, hlam, p1419_0]
                      · have p1419_0 := h1419c.1
                        have p1419_1 := h1419c.2.1
                        have p1419_2 := h1419c.2.2.1
                        have p1419_3 := h1419c.2.2.2
                        linarith only [h1365, hlam, p1419_1]
                      · have p1419_0 := h1419c.1
                        have p1419_1 := h1419c.2.1
                        have p1419_2 := h1419c.2.2.1
                        have p1419_3 := h1419c.2.2.2
                        linarith only [hlam, p1419_0]
                      · have p1419_0 := h1419c.1
                        have p1419_1 := h1419c.2.1
                        have p1419_2 := h1419c.2.2.1
                        have p1419_3 := h1419c.2.2.2
                        linarith only [h1368, h1372, hc13, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1419_1]
                      · have p1419_0 := h1419c.1
                        have p1419_1 := h1419c.2.1
                        have p1419_2 := h1419c.2.2.1
                        have p1419_3 := h1419c.2.2.2
                        linarith only [h0, h1365, h1368, h1370, h1372, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1419_1]
                      · have p1419_0 := h1419c.1
                        have p1419_1 := h1419c.2.1
                        have p1419_2 := h1419c.2.2.1
                        have p1419_3 := h1419c.2.2.2
                        linarith only [h2, hlam, p1419_0]
                      · have p1419_0 := h1419c.1
                        have p1419_1 := h1419c.2.1
                        have p1419_2 := h1419c.2.2.1
                        have p1419_3 := h1419c.2.2.2
                        linarith only [h1366, hlam, p1419_1]
                      · have p1419_0 := h1419c.1
                        have p1419_1 := h1419c.2.1
                        have p1419_2 := h1419c.2.2.1
                        have p1419_3 := h1419c.2.2.2
                        linarith only [h1368, hlam, p1419_0]
                      · have p1419_0 := h1419c.1
                        have p1419_1 := h1419c.2.1
                        have p1419_2 := h1419c.2.2.1
                        have p1419_3 := h1419c.2.2.2
                        linarith only [hlam, p1419_0]
                      · have p1419_0 := h1419c.1
                        have p1419_1 := h1419c.2.1
                        have p1419_2 := h1419c.2.2.1
                        have p1419_3 := h1419c.2.2.2
                        linarith only [h1370, hlam, p1419_1]
                      · have p1419_0 := h1419c.1
                        have p1419_1 := h1419c.2.1
                        have p1419_2 := h1419c.2.2.1
                        have p1419_3 := h1419c.2.2.2
                        linarith only [h3, hlam, p1419_0]
                      · have p1419_0 := h1419c.1
                        have p1419_1 := h1419c.2.1
                        have p1419_2 := h1419c.2.2.1
                        have p1419_3 := h1419c.2.2.2
                        linarith only [h1367, hlam, p1419_1]
                      · have p1419_0 := h1419c.1
                        have p1419_1 := h1419c.2.1
                        have p1419_2 := h1419c.2.2.1
                        have p1419_3 := h1419c.2.2.2
                        linarith only [h1369, hlam, p1419_0]
                      · have p1419_0 := h1419c.1
                        have p1419_1 := h1419c.2.1
                        have p1419_2 := h1419c.2.2.1
                        have p1419_3 := h1419c.2.2.2
                        linarith only [h1368, h1372, hc15, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1419_1]
                      · have p1419_0 := h1419c.1
                        have p1419_1 := h1419c.2.1
                        have p1419_2 := h1419c.2.2.1
                        have p1419_3 := h1419c.2.2.2
                        linarith only [hlam, p1419_0]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h1445 | h1445
            · linarith only [h1368, h1369, h1445, h2, h8, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1447 | h1447
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1448 | h1448
                · linarith only [h1365, h1369, h1448, hlam]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h1450 | h1450
                  · linarith only [h1450, h5, h9, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1452 | h1452
                    · linarith only [h1365, h1369, h1447, h1452, h8, h9, hc03, hc04, hlam, hphi, ht0b, ht45, ht5b]
                    · rcases h1bigk with h1454c | h1454c | h1454c | h1454c | h1454c | h1454c | h1454c | h1454c | h1454c | h1454c | h1454c | h1454c | h1454c | h1454c | h1454c | h1454c | h1454c | h1454c | h1454c | h1454c | h1454c | h1454c | h1454c | h1454c | h1454c
                      · have p1454_0 := h1454c.1
                        have p1454_1 := h1454c.2.1
                        have p1454_2 := h1454c.2.2.1
                        have p1454_3 := h1454c.2.2.2
                        linarith only [hlam, p1454_0]
                      · have p1454_0 := h1454c.1
                        have p1454_1 := h1454c.2.1
                        have p1454_2 := h1454c.2.2.1
                        have p1454_3 := h1454c.2.2.2
                        linarith only [h1365, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1454_1]
                      · have p1454_0 := h1454c.1
                        have p1454_1 := h1454c.2.1
                        have p1454_2 := h1454c.2.2.1
                        have p1454_3 := h1454c.2.2.2
                        linarith only [h1365, h1447, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1454_1]
                      · have p1454_0 := h1454c.1
                        have p1454_1 := h1454c.2.1
                        have p1454_2 := h1454c.2.2.1
                        have p1454_3 := h1454c.2.2.2
                        rcases p1454_3 (m.d 0 1) (by simp) with h1458 | h1458
                        · rcases p1454_3 (m.d 1 2) (by simp) with h1459 | h1459
                          · linarith only [h0, h1459, hlam]
                          · linarith only [h1366, h1459, hlam]
                        · linarith only [h1458, hlam, p1454_0]
                      · have p1454_0 := h1454c.1
                        have p1454_1 := h1454c.2.1
                        have p1454_2 := h1454c.2.2.1
                        have p1454_3 := h1454c.2.2.2
                        linarith only [h1367, h1447, h1448, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1454_1]
                      · have p1454_0 := h1454c.1
                        have p1454_1 := h1454c.2.1
                        have p1454_2 := h1454c.2.2.1
                        have p1454_3 := h1454c.2.2.2
                        linarith only [h0, hlam, p1454_0]
                      · have p1454_0 := h1454c.1
                        have p1454_1 := h1454c.2.1
                        have p1454_2 := h1454c.2.2.1
                        have p1454_3 := h1454c.2.2.2
                        linarith only [hlam, p1454_0]
                      · have p1454_0 := h1454c.1
                        have p1454_1 := h1454c.2.1
                        have p1454_2 := h1454c.2.2.1
                        have p1454_3 := h1454c.2.2.2
                        linarith only [h1365, h1447, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1454_1]
                      · have p1454_0 := h1454c.1
                        have p1454_1 := h1454c.2.1
                        have p1454_2 := h1454c.2.2.1
                        have p1454_3 := h1454c.2.2.2
                        linarith only [h0, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p1454_1]
                      · have p1454_0 := h1454c.1
                        have p1454_1 := h1454c.2.1
                        have p1454_2 := h1454c.2.2.1
                        have p1454_3 := h1454c.2.2.2
                        linarith only [h0, hc01, hc15, hlam, hphi, ht0b, ht5b, p1454_1]
                      · have p1454_0 := h1454c.1
                        have p1454_1 := h1454c.2.1
                        have p1454_2 := h1454c.2.2.1
                        have p1454_3 := h1454c.2.2.2
                        linarith only [h1, hlam, p1454_0]
                      · have p1454_0 := h1454c.1
                        have p1454_1 := h1454c.2.1
                        have p1454_2 := h1454c.2.2.1
                        have p1454_3 := h1454c.2.2.2
                        linarith only [h1365, hlam, p1454_1]
                      · have p1454_0 := h1454c.1
                        have p1454_1 := h1454c.2.1
                        have p1454_2 := h1454c.2.2.1
                        have p1454_3 := h1454c.2.2.2
                        linarith only [hlam, p1454_0]
                      · have p1454_0 := h1454c.1
                        have p1454_1 := h1454c.2.1
                        have p1454_2 := h1454c.2.2.1
                        have p1454_3 := h1454c.2.2.2
                        linarith only [h1, h1366, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p1454_1]
                      · have p1454_0 := h1454c.1
                        have p1454_1 := h1454c.2.1
                        have p1454_2 := h1454c.2.2.1
                        have p1454_3 := h1454c.2.2.2
                        linarith only [h1369, hlam, p1454_1]
                      · have p1454_0 := h1454c.1
                        have p1454_1 := h1454c.2.1
                        have p1454_2 := h1454c.2.2.1
                        have p1454_3 := h1454c.2.2.2
                        linarith only [h2, hlam, p1454_0]
                      · have p1454_0 := h1454c.1
                        have p1454_1 := h1454c.2.1
                        have p1454_2 := h1454c.2.2.1
                        have p1454_3 := h1454c.2.2.2
                        linarith only [h1366, hlam, p1454_1]
                      · have p1454_0 := h1454c.1
                        have p1454_1 := h1454c.2.1
                        have p1454_2 := h1454c.2.2.1
                        have p1454_3 := h1454c.2.2.2
                        linarith only [h1368, hlam, p1454_0]
                      · have p1454_0 := h1454c.1
                        have p1454_1 := h1454c.2.1
                        have p1454_2 := h1454c.2.2.1
                        have p1454_3 := h1454c.2.2.2
                        linarith only [hlam, p1454_0]
                      · have p1454_0 := h1454c.1
                        have p1454_1 := h1454c.2.1
                        have p1454_2 := h1454c.2.2.1
                        have p1454_3 := h1454c.2.2.2
                        linarith only [h1445, hlam, p1454_1]
                      · have p1454_0 := h1454c.1
                        have p1454_1 := h1454c.2.1
                        have p1454_2 := h1454c.2.2.1
                        have p1454_3 := h1454c.2.2.2
                        linarith only [h3, hlam, p1454_0]
                      · have p1454_0 := h1454c.1
                        have p1454_1 := h1454c.2.1
                        have p1454_2 := h1454c.2.2.1
                        have p1454_3 := h1454c.2.2.2
                        linarith only [h1367, hlam, p1454_1]
                      · have p1454_0 := h1454c.1
                        have p1454_1 := h1454c.2.1
                        have p1454_2 := h1454c.2.2.1
                        have p1454_3 := h1454c.2.2.2
                        linarith only [h3, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p1454_1]
                      · have p1454_0 := h1454c.1
                        have p1454_1 := h1454c.2.1
                        have p1454_2 := h1454c.2.2.1
                        have p1454_3 := h1454c.2.2.2
                        linarith only [h0, h1366, h1369, h4, h8, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p1454_1]
                      · have p1454_0 := h1454c.1
                        have p1454_1 := h1454c.2.1
                        have p1454_2 := h1454c.2.2.1
                        have p1454_3 := h1454c.2.2.2
                        linarith only [hlam, p1454_0]
              · linarith only [h0, h1368, h1369, h1447, h4, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h1485 | h1485
          · rcases m.htr 1 4 5 (by decide) (by decide) with h1486 | h1486
            · linarith only [h1368, h1485, h1486, h7, h9, hc14, hc35, hlam, hphi, ht01, ht0b, ht5b]
            · linarith only [h1368, h1485, h1486, hlam]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h1489 | h1489
            · linarith only [h1368, h1489, h2, h7, h9, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1491 | h1491
              · linarith only [h1365, h1368, h1491, hlam]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1493 | h1493
                · linarith only [h1365, h1485, h1493, hlam]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h1495 | h1495
                  · linarith only [h0, h1365, h1368, h1495, h5, h7, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1497 | h1497
                    · linarith only [h1497, h7, h9, hlam]
                    · rcases h1bigk with h1499c | h1499c | h1499c | h1499c | h1499c | h1499c | h1499c | h1499c | h1499c | h1499c | h1499c | h1499c | h1499c | h1499c | h1499c | h1499c | h1499c | h1499c | h1499c | h1499c | h1499c | h1499c | h1499c | h1499c | h1499c
                      · have p1499_0 := h1499c.1
                        have p1499_1 := h1499c.2.1
                        have p1499_2 := h1499c.2.2.1
                        have p1499_3 := h1499c.2.2.2
                        linarith only [hlam, p1499_0]
                      · have p1499_0 := h1499c.1
                        have p1499_1 := h1499c.2.1
                        have p1499_2 := h1499c.2.2.1
                        have p1499_3 := h1499c.2.2.2
                        linarith only [h1365, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1499_1]
                      · have p1499_0 := h1499c.1
                        have p1499_1 := h1499c.2.1
                        have p1499_2 := h1499c.2.2.1
                        have p1499_3 := h1499c.2.2.2
                        rcases p1499_3 (m.d 0 1) (by simp) with h1502 | h1502
                        · rcases p1499_3 (m.d 1 2) (by simp) with h1503 | h1503
                          · linarith only [h0, h1503, hlam]
                          · linarith only [h1365, h1503, hlam]
                        · linarith only [h1502, hlam, p1499_0]
                      · have p1499_0 := h1499c.1
                        have p1499_1 := h1499c.2.1
                        have p1499_2 := h1499c.2.2.1
                        have p1499_3 := h1499c.2.2.2
                        rcases p1499_3 (m.d 0 1) (by simp) with h1507 | h1507
                        · rcases p1499_3 (m.d 1 2) (by simp) with h1508 | h1508
                          · linarith only [h0, h1508, hlam]
                          · linarith only [h1366, h1508, hlam]
                        · linarith only [h1507, hlam, p1499_0]
                      · have p1499_0 := h1499c.1
                        have p1499_1 := h1499c.2.1
                        have p1499_2 := h1499c.2.2.1
                        have p1499_3 := h1499c.2.2.2
                        rcases p1499_3 (m.d 0 1) (by simp) with h1512 | h1512
                        · rcases p1499_3 (m.d 1 2) (by simp) with h1513 | h1513
                          · linarith only [h0, h1513, hlam]
                          · linarith only [h1367, h1513, hlam]
                        · linarith only [h1512, hlam, p1499_0]
                      · have p1499_0 := h1499c.1
                        have p1499_1 := h1499c.2.1
                        have p1499_2 := h1499c.2.2.1
                        have p1499_3 := h1499c.2.2.2
                        linarith only [h0, hlam, p1499_0]
                      · have p1499_0 := h1499c.1
                        have p1499_1 := h1499c.2.1
                        have p1499_2 := h1499c.2.2.1
                        have p1499_3 := h1499c.2.2.2
                        linarith only [hlam, p1499_0]
                      · have p1499_0 := h1499c.1
                        have p1499_1 := h1499c.2.1
                        have p1499_2 := h1499c.2.2.1
                        have p1499_3 := h1499c.2.2.2
                        linarith only [h0, h1365, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1499_1]
                      · have p1499_0 := h1499c.1
                        have p1499_1 := h1499c.2.1
                        have p1499_2 := h1499c.2.2.1
                        have p1499_3 := h1499c.2.2.2
                        linarith only [h0, h1365, h1368, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1499_1]
                      · have p1499_0 := h1499c.1
                        have p1499_1 := h1499c.2.1
                        have p1499_2 := h1499c.2.2.1
                        have p1499_3 := h1499c.2.2.2
                        linarith only [h0, h1365, h1368, h1489, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1499_1]
                      · have p1499_0 := h1499c.1
                        have p1499_1 := h1499c.2.1
                        have p1499_2 := h1499c.2.2.1
                        have p1499_3 := h1499c.2.2.2
                        linarith only [h1, hlam, p1499_0]
                      · have p1499_0 := h1499c.1
                        have p1499_1 := h1499c.2.1
                        have p1499_2 := h1499c.2.2.1
                        have p1499_3 := h1499c.2.2.2
                        linarith only [h1365, hlam, p1499_1]
                      · have p1499_0 := h1499c.1
                        have p1499_1 := h1499c.2.1
                        have p1499_2 := h1499c.2.2.1
                        have p1499_3 := h1499c.2.2.2
                        linarith only [hlam, p1499_0]
                      · have p1499_0 := h1499c.1
                        have p1499_1 := h1499c.2.1
                        have p1499_2 := h1499c.2.2.1
                        have p1499_3 := h1499c.2.2.2
                        linarith only [h1368, hlam, p1499_1]
                      · have p1499_0 := h1499c.1
                        have p1499_1 := h1499c.2.1
                        have p1499_2 := h1499c.2.2.1
                        have p1499_3 := h1499c.2.2.2
                        linarith only [h1485, hlam, p1499_1]
                      · have p1499_0 := h1499c.1
                        have p1499_1 := h1499c.2.1
                        have p1499_2 := h1499c.2.2.1
                        have p1499_3 := h1499c.2.2.2
                        linarith only [h2, hlam, p1499_0]
                      · have p1499_0 := h1499c.1
                        have p1499_1 := h1499c.2.1
                        have p1499_2 := h1499c.2.2.1
                        have p1499_3 := h1499c.2.2.2
                        linarith only [h1366, hlam, p1499_1]
                      · have p1499_0 := h1499c.1
                        have p1499_1 := h1499c.2.1
                        have p1499_2 := h1499c.2.2.1
                        have p1499_3 := h1499c.2.2.2
                        linarith only [h1365, h2, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1499_1]
                      · have p1499_0 := h1499c.1
                        have p1499_1 := h1499c.2.1
                        have p1499_2 := h1499c.2.2.1
                        have p1499_3 := h1499c.2.2.2
                        linarith only [hlam, p1499_0]
                      · have p1499_0 := h1499c.1
                        have p1499_1 := h1499c.2.1
                        have p1499_2 := h1499c.2.2.1
                        have p1499_3 := h1499c.2.2.2
                        linarith only [h1489, hlam, p1499_1]
                      · have p1499_0 := h1499c.1
                        have p1499_1 := h1499c.2.1
                        have p1499_2 := h1499c.2.2.1
                        have p1499_3 := h1499c.2.2.2
                        linarith only [h3, hlam, p1499_0]
                      · have p1499_0 := h1499c.1
                        have p1499_1 := h1499c.2.1
                        have p1499_2 := h1499c.2.2.1
                        have p1499_3 := h1499c.2.2.2
                        linarith only [h1367, hlam, p1499_1]
                      · have p1499_0 := h1499c.1
                        have p1499_1 := h1499c.2.1
                        have p1499_2 := h1499c.2.2.1
                        have p1499_3 := h1499c.2.2.2
                        linarith only [h0, h1365, h1367, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1499_1]
                      · have p1499_0 := h1499c.1
                        have p1499_1 := h1499c.2.1
                        have p1499_2 := h1499c.2.2.1
                        have p1499_3 := h1499c.2.2.2
                        linarith only [h1485, h4, h8, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b, p1499_1]
                      · have p1499_0 := h1499c.1
                        have p1499_1 := h1499c.2.1
                        have p1499_2 := h1499c.2.2.1
                        have p1499_3 := h1499c.2.2.2
                        linarith only [hlam, p1499_0]
      · rcases m.htr 1 3 4 (by decide) (by decide) with h1537 | h1537
        · rcases m.htr 1 3 5 (by decide) (by decide) with h1538 | h1538
          · linarith only [h1365, h1367, h1538, hlam]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h1540 | h1540
            · linarith only [h1540, h2, h9, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1542 | h1542
              · linarith only [h0, h1365, h1367, h1542, h6, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
              · linarith only [h0, h1537, h1538, h1542, h4, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h1545 | h1545
          · linarith only [h1365, h1367, h1537, h1545, h7, h9, hc23, hc45, hlam, hphi, ht34]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h1547 | h1547
            · linarith only [h0, h1366, h1537, h1547, h7, h9, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1549 | h1549
              · linarith only [h0, h1365, h1367, h1537, h1549, h6, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1551 | h1551
                · linarith only [h0, h1365, h1367, h1545, h1551, h6, hc01, hc15, hlam, hphi, ht0b, ht5b]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h1553 | h1553
                  · linarith only [h0, h1366, h1367, h1551, h1553, h4, h8, h9, hc01, hc04, hlam, hphi, ht0b, ht45, ht5b]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1555 | h1555
                    · linarith only [h1366, h1367, h1549, h1551, h1555, h8, h9, hc23, hc34, hlam, hphi]
                    · rcases h1bigk with h1557c | h1557c | h1557c | h1557c | h1557c | h1557c | h1557c | h1557c | h1557c | h1557c | h1557c | h1557c | h1557c | h1557c | h1557c | h1557c | h1557c | h1557c | h1557c | h1557c | h1557c | h1557c | h1557c | h1557c | h1557c
                      · have p1557_0 := h1557c.1
                        have p1557_1 := h1557c.2.1
                        have p1557_2 := h1557c.2.2.1
                        have p1557_3 := h1557c.2.2.2
                        linarith only [hlam, p1557_0]
                      · have p1557_0 := h1557c.1
                        have p1557_1 := h1557c.2.1
                        have p1557_2 := h1557c.2.2.1
                        have p1557_3 := h1557c.2.2.2
                        linarith only [h1366, h1549, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1557_1]
                      · have p1557_0 := h1557c.1
                        have p1557_1 := h1557c.2.1
                        have p1557_2 := h1557c.2.2.1
                        have p1557_3 := h1557c.2.2.2
                        rcases p1557_3 (m.d 0 1) (by simp) with h1560 | h1560
                        · rcases p1557_3 (m.d 1 2) (by simp) with h1561 | h1561
                          · linarith only [h0, h1561, hlam]
                          · linarith only [h1365, h1561, hlam]
                        · linarith only [h1560, hlam, p1557_0]
                      · have p1557_0 := h1557c.1
                        have p1557_1 := h1557c.2.1
                        have p1557_2 := h1557c.2.2.1
                        have p1557_3 := h1557c.2.2.2
                        rcases p1557_3 (m.d 0 1) (by simp) with h1565 | h1565
                        · rcases p1557_3 (m.d 1 2) (by simp) with h1566 | h1566
                          · linarith only [h0, h1566, hlam]
                          · linarith only [h1366, h1566, hlam]
                        · linarith only [h1565, hlam, p1557_0]
                      · have p1557_0 := h1557c.1
                        have p1557_1 := h1557c.2.1
                        have p1557_2 := h1557c.2.2.1
                        have p1557_3 := h1557c.2.2.2
                        linarith only [h1366, h1367, h1549, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1557_1]
                      · have p1557_0 := h1557c.1
                        have p1557_1 := h1557c.2.1
                        have p1557_2 := h1557c.2.2.1
                        have p1557_3 := h1557c.2.2.2
                        linarith only [h0, hlam, p1557_0]
                      · have p1557_0 := h1557c.1
                        have p1557_1 := h1557c.2.1
                        have p1557_2 := h1557c.2.2.1
                        have p1557_3 := h1557c.2.2.2
                        linarith only [hlam, p1557_0]
                      · have p1557_0 := h1557c.1
                        have p1557_1 := h1557c.2.1
                        have p1557_2 := h1557c.2.2.1
                        have p1557_3 := h1557c.2.2.2
                        linarith only [h1365, h1367, h1551, h4, h8, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1557_1]
                      · have p1557_0 := h1557c.1
                        have p1557_1 := h1557c.2.1
                        have p1557_2 := h1557c.2.2.1
                        have p1557_3 := h1557c.2.2.2
                        linarith only [h0, h1366, h1367, h1549, h1551, h4, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1557_1]
                      · have p1557_0 := h1557c.1
                        have p1557_1 := h1557c.2.1
                        have p1557_2 := h1557c.2.2.1
                        have p1557_3 := h1557c.2.2.2
                        linarith only [h1367, hlam, p1557_0]
                      · have p1557_0 := h1557c.1
                        have p1557_1 := h1557c.2.1
                        have p1557_2 := h1557c.2.2.1
                        have p1557_3 := h1557c.2.2.2
                        linarith only [h1, hlam, p1557_0]
                      · have p1557_0 := h1557c.1
                        have p1557_1 := h1557c.2.1
                        have p1557_2 := h1557c.2.2.1
                        have p1557_3 := h1557c.2.2.2
                        linarith only [h1365, hlam, p1557_1]
                      · have p1557_0 := h1557c.1
                        have p1557_1 := h1557c.2.1
                        have p1557_2 := h1557c.2.2.1
                        have p1557_3 := h1557c.2.2.2
                        linarith only [hlam, p1557_0]
                      · have p1557_0 := h1557c.1
                        have p1557_1 := h1557c.2.1
                        have p1557_2 := h1557c.2.2.1
                        have p1557_3 := h1557c.2.2.2
                        linarith only [h1537, hlam, p1557_1]
                      · have p1557_0 := h1557c.1
                        have p1557_1 := h1557c.2.1
                        have p1557_2 := h1557c.2.2.1
                        have p1557_3 := h1557c.2.2.2
                        linarith only [h1545, hlam, p1557_1]
                      · have p1557_0 := h1557c.1
                        have p1557_1 := h1557c.2.1
                        have p1557_2 := h1557c.2.2.1
                        have p1557_3 := h1557c.2.2.2
                        linarith only [h2, hlam, p1557_0]
                      · have p1557_0 := h1557c.1
                        have p1557_1 := h1557c.2.1
                        have p1557_2 := h1557c.2.2.1
                        have p1557_3 := h1557c.2.2.2
                        linarith only [h1366, hlam, p1557_1]
                      · have p1557_0 := h1557c.1
                        have p1557_1 := h1557c.2.1
                        have p1557_2 := h1557c.2.2.1
                        have p1557_3 := h1557c.2.2.2
                        linarith only [h1365, h2, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1557_1]
                      · have p1557_0 := h1557c.1
                        have p1557_1 := h1557c.2.1
                        have p1557_2 := h1557c.2.2.1
                        have p1557_3 := h1557c.2.2.2
                        linarith only [hlam, p1557_0]
                      · have p1557_0 := h1557c.1
                        have p1557_1 := h1557c.2.1
                        have p1557_2 := h1557c.2.2.1
                        have p1557_3 := h1557c.2.2.2
                        linarith only [h1547, hlam, p1557_1]
                      · have p1557_0 := h1557c.1
                        have p1557_1 := h1557c.2.1
                        have p1557_2 := h1557c.2.2.1
                        have p1557_3 := h1557c.2.2.2
                        linarith only [h3, hlam, p1557_0]
                      · have p1557_0 := h1557c.1
                        have p1557_1 := h1557c.2.1
                        have p1557_2 := h1557c.2.2.1
                        have p1557_3 := h1557c.2.2.2
                        linarith only [h3, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1557_1]
                      · have p1557_0 := h1557c.1
                        have p1557_1 := h1557c.2.1
                        have p1557_2 := h1557c.2.2.1
                        have p1557_3 := h1557c.2.2.2
                        linarith only [h0, h1365, h1367, h1551, h4, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1557_1]
                      · have p1557_0 := h1557c.1
                        have p1557_1 := h1557c.2.1
                        have p1557_2 := h1557c.2.2.1
                        have p1557_3 := h1557c.2.2.2
                        linarith only [h0, h1367, h1551, h4, h8, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p1557_1]
                      · have p1557_0 := h1557c.1
                        have p1557_1 := h1557c.2.1
                        have p1557_2 := h1557c.2.2.1
                        have p1557_3 := h1557c.2.2.2
                        linarith only [hlam, p1557_0]
    · linarith only [h1365, h1366, h5, h9, hc23, hc45, hlam, hphi, ht34]
  · rcases m.htr 1 2 4 (by decide) (by decide) with h1592 | h1592
    · rcases m.htr 1 2 5 (by decide) (by decide) with h1593 | h1593
      · rcases m.htr 1 3 4 (by decide) (by decide) with h1594 | h1594
        · rcases m.htr 1 3 5 (by decide) (by decide) with h1595 | h1595
          · rcases m.htr 1 4 5 (by decide) (by decide) with h1596 | h1596
            · linarith only [h1596, h2, h9, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1598 | h1598
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1599 | h1599
                · rcases m.htr 2 4 5 (by decide) (by decide) with h1600 | h1600
                  · linarith only [h0, h1592, h1600, h2, h9, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1602 | h1602
                    · linarith only [h1592, h1598, h1602, h2, h9, hlam]
                    · rcases h1bigk with h1604c | h1604c | h1604c | h1604c | h1604c | h1604c | h1604c | h1604c | h1604c | h1604c | h1604c | h1604c | h1604c | h1604c | h1604c | h1604c | h1604c | h1604c | h1604c | h1604c | h1604c | h1604c | h1604c | h1604c | h1604c
                      · have p1604_0 := h1604c.1
                        have p1604_1 := h1604c.2.1
                        have p1604_2 := h1604c.2.2.1
                        have p1604_3 := h1604c.2.2.2
                        linarith only [hlam, p1604_0]
                      · have p1604_0 := h1604c.1
                        have p1604_1 := h1604c.2.1
                        have p1604_2 := h1604c.2.2.1
                        have p1604_3 := h1604c.2.2.2
                        linarith only [h1593, h1600, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p1604_1]
                      · have p1604_0 := h1604c.1
                        have p1604_1 := h1604c.2.1
                        have p1604_2 := h1604c.2.2.1
                        have p1604_3 := h1604c.2.2.2
                        linarith only [h1365, h1593, h1598, h1600, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1604_1]
                      · have p1604_0 := h1604c.1
                        have p1604_1 := h1604c.2.1
                        have p1604_2 := h1604c.2.2.1
                        have p1604_3 := h1604c.2.2.2
                        rcases p1604_3 (m.d 0 1) (by simp) with h1608 | h1608
                        · rcases p1604_3 (m.d 1 2) (by simp) with h1609 | h1609
                          · linarith only [h0, h1609, hlam]
                          · linarith only [h1592, h1609, hlam]
                        · linarith only [h1608, hlam, p1604_0]
                      · have p1604_0 := h1604c.1
                        have p1604_1 := h1604c.2.1
                        have p1604_2 := h1604c.2.2.1
                        have p1604_3 := h1604c.2.2.2
                        rcases p1604_3 (m.d 0 1) (by simp) with h1613 | h1613
                        · rcases p1604_3 (m.d 1 2) (by simp) with h1614 | h1614
                          · linarith only [h0, h1614, hlam]
                          · linarith only [h1593, h1614, hlam]
                        · linarith only [h1613, hlam, p1604_0]
                      · have p1604_0 := h1604c.1
                        have p1604_1 := h1604c.2.1
                        have p1604_2 := h1604c.2.2.1
                        have p1604_3 := h1604c.2.2.2
                        linarith only [h0, hlam, p1604_0]
                      · have p1604_0 := h1604c.1
                        have p1604_1 := h1604c.2.1
                        have p1604_2 := h1604c.2.2.1
                        have p1604_3 := h1604c.2.2.2
                        linarith only [hlam, p1604_0]
                      · have p1604_0 := h1604c.1
                        have p1604_1 := h1604c.2.1
                        have p1604_2 := h1604c.2.2.1
                        have p1604_3 := h1604c.2.2.2
                        linarith only [h1365, hlam, p1604_0]
                      · have p1604_0 := h1604c.1
                        have p1604_1 := h1604c.2.1
                        have p1604_2 := h1604c.2.2.1
                        have p1604_3 := h1604c.2.2.2
                        linarith only [h1365, h1592, h1598, h4, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p1604_1]
                      · have p1604_0 := h1604c.1
                        have p1604_1 := h1604c.2.1
                        have p1604_2 := h1604c.2.2.1
                        have p1604_3 := h1604c.2.2.2
                        linarith only [h0, h1365, h1592, h1596, h1598, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1604_1]
                      · have p1604_0 := h1604c.1
                        have p1604_1 := h1604c.2.1
                        have p1604_2 := h1604c.2.2.1
                        have p1604_3 := h1604c.2.2.2
                        linarith only [h1, hlam, p1604_0]
                      · have p1604_0 := h1604c.1
                        have p1604_1 := h1604c.2.1
                        have p1604_2 := h1604c.2.2.1
                        have p1604_3 := h1604c.2.2.2
                        linarith only [h1, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1604_1]
                      · have p1604_0 := h1604c.1
                        have p1604_1 := h1604c.2.1
                        have p1604_2 := h1604c.2.2.1
                        have p1604_3 := h1604c.2.2.2
                        linarith only [hlam, p1604_0]
                      · have p1604_0 := h1604c.1
                        have p1604_1 := h1604c.2.1
                        have p1604_2 := h1604c.2.2.1
                        have p1604_3 := h1604c.2.2.2
                        linarith only [h0, h1365, h1592, h1598, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1604_1]
                      · have p1604_0 := h1604c.1
                        have p1604_1 := h1604c.2.1
                        have p1604_2 := h1604c.2.2.1
                        have p1604_3 := h1604c.2.2.2
                        linarith only [h0, h1365, h1592, h1596, h1598, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1604_1]
                      · have p1604_0 := h1604c.1
                        have p1604_1 := h1604c.2.1
                        have p1604_2 := h1604c.2.2.1
                        have p1604_3 := h1604c.2.2.2
                        linarith only [h2, hlam, p1604_0]
                      · have p1604_0 := h1604c.1
                        have p1604_1 := h1604c.2.1
                        have p1604_2 := h1604c.2.2.1
                        have p1604_3 := h1604c.2.2.2
                        linarith only [h1592, hlam, p1604_1]
                      · have p1604_0 := h1604c.1
                        have p1604_1 := h1604c.2.1
                        have p1604_2 := h1604c.2.2.1
                        have p1604_3 := h1604c.2.2.2
                        linarith only [h1594, hlam, p1604_0]
                      · have p1604_0 := h1604c.1
                        have p1604_1 := h1604c.2.1
                        have p1604_2 := h1604c.2.2.1
                        have p1604_3 := h1604c.2.2.2
                        linarith only [hlam, p1604_0]
                      · have p1604_0 := h1604c.1
                        have p1604_1 := h1604c.2.1
                        have p1604_2 := h1604c.2.2.1
                        have p1604_3 := h1604c.2.2.2
                        linarith only [h1596, hlam, p1604_1]
                      · have p1604_0 := h1604c.1
                        have p1604_1 := h1604c.2.1
                        have p1604_2 := h1604c.2.2.1
                        have p1604_3 := h1604c.2.2.2
                        linarith only [h3, hlam, p1604_0]
                      · have p1604_0 := h1604c.1
                        have p1604_1 := h1604c.2.1
                        have p1604_2 := h1604c.2.2.1
                        have p1604_3 := h1604c.2.2.2
                        linarith only [h1593, hlam, p1604_1]
                      · have p1604_0 := h1604c.1
                        have p1604_1 := h1604c.2.1
                        have p1604_2 := h1604c.2.2.1
                        have p1604_3 := h1604c.2.2.2
                        linarith only [h1595, hlam, p1604_0]
                      · have p1604_0 := h1604c.1
                        have p1604_1 := h1604c.2.1
                        have p1604_2 := h1604c.2.2.1
                        have p1604_3 := h1604c.2.2.2
                        linarith only [h1592, h1598, h3, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1604_1]
                      · have p1604_0 := h1604c.1
                        have p1604_1 := h1604c.2.1
                        have p1604_2 := h1604c.2.2.1
                        have p1604_3 := h1604c.2.2.2
                        linarith only [hlam, p1604_0]
                · linarith only [h0, h1365, h1593, h1599, h4, h8, hc01, hc25, hlam, hphi, ht0b, ht5b]
              · linarith only [h1365, h1598, h7, h9, hc12, hc45, hlam, hphi, ht23, ht34]
          · linarith only [h1365, h1593, h1595, hlam]
        · linarith only [h1365, h1592, h1594, h7, h9, hc24, hc45, hlam, hphi]
      · rcases m.htr 1 3 4 (by decide) (by decide) with h1642 | h1642
        · rcases m.htr 1 3 5 (by decide) (by decide) with h1643 | h1643
          · rcases m.htr 1 4 5 (by decide) (by decide) with h1644 | h1644
            · linarith only [h1644, h2, h9, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1646 | h1646
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1647 | h1647
                · rcases m.htr 2 4 5 (by decide) (by decide) with h1648 | h1648
                  · linarith only [h1592, h1593, h1648, h6, h9, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1650 | h1650
                    · linarith only [h1592, h1593, h1646, h1650, h6, h9, hlam]
                    · rcases h1bigk with h1652c | h1652c | h1652c | h1652c | h1652c | h1652c | h1652c | h1652c | h1652c | h1652c | h1652c | h1652c | h1652c | h1652c | h1652c | h1652c | h1652c | h1652c | h1652c | h1652c | h1652c | h1652c | h1652c | h1652c | h1652c
                      · have p1652_0 := h1652c.1
                        have p1652_1 := h1652c.2.1
                        have p1652_2 := h1652c.2.2.1
                        have p1652_3 := h1652c.2.2.2
                        linarith only [hlam, p1652_0]
                      · have p1652_0 := h1652c.1
                        have p1652_1 := h1652c.2.1
                        have p1652_2 := h1652c.2.2.1
                        have p1652_3 := h1652c.2.2.2
                        linarith only [h1592, h1646, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1652_1]
                      · have p1652_0 := h1652c.1
                        have p1652_1 := h1652c.2.1
                        have p1652_2 := h1652c.2.2.1
                        have p1652_3 := h1652c.2.2.2
                        linarith only [h1365, h1592, h1646, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1652_1]
                      · have p1652_0 := h1652c.1
                        have p1652_1 := h1652c.2.1
                        have p1652_2 := h1652c.2.2.1
                        have p1652_3 := h1652c.2.2.2
                        rcases p1652_3 (m.d 0 1) (by simp) with h1656 | h1656
                        · rcases p1652_3 (m.d 1 2) (by simp) with h1657 | h1657
                          · linarith only [h0, h1657, hlam]
                          · linarith only [h1592, h1657, hlam]
                        · linarith only [h1656, hlam, p1652_0]
                      · have p1652_0 := h1652c.1
                        have p1652_1 := h1652c.2.1
                        have p1652_2 := h1652c.2.2.1
                        have p1652_3 := h1652c.2.2.2
                        linarith only [h1592, h1593, h1646, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1652_1]
                      · have p1652_0 := h1652c.1
                        have p1652_1 := h1652c.2.1
                        have p1652_2 := h1652c.2.2.1
                        have p1652_3 := h1652c.2.2.2
                        linarith only [h0, hlam, p1652_0]
                      · have p1652_0 := h1652c.1
                        have p1652_1 := h1652c.2.1
                        have p1652_2 := h1652c.2.2.1
                        have p1652_3 := h1652c.2.2.2
                        linarith only [hlam, p1652_0]
                      · have p1652_0 := h1652c.1
                        have p1652_1 := h1652c.2.1
                        have p1652_2 := h1652c.2.2.1
                        have p1652_3 := h1652c.2.2.2
                        linarith only [h1365, hlam, p1652_0]
                      · have p1652_0 := h1652c.1
                        have p1652_1 := h1652c.2.1
                        have p1652_2 := h1652c.2.2.1
                        have p1652_3 := h1652c.2.2.2
                        linarith only [h1593, h6, hc05, hc14, hlam, hphi, ht0b, ht45, ht5b, p1652_1]
                      · have p1652_0 := h1652c.1
                        have p1652_1 := h1652c.2.1
                        have p1652_2 := h1652c.2.2.1
                        have p1652_3 := h1652c.2.2.2
                        linarith only [h1593, hlam, p1652_0]
                      · have p1652_0 := h1652c.1
                        have p1652_1 := h1652c.2.1
                        have p1652_2 := h1652c.2.2.1
                        have p1652_3 := h1652c.2.2.2
                        linarith only [h1, hlam, p1652_0]
                      · have p1652_0 := h1652c.1
                        have p1652_1 := h1652c.2.1
                        have p1652_2 := h1652c.2.2.1
                        have p1652_3 := h1652c.2.2.2
                        linarith only [h0, h1365, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1652_1]
                      · have p1652_0 := h1652c.1
                        have p1652_1 := h1652c.2.1
                        have p1652_2 := h1652c.2.2.1
                        have p1652_3 := h1652c.2.2.2
                        linarith only [hlam, p1652_0]
                      · have p1652_0 := h1652c.1
                        have p1652_1 := h1652c.2.1
                        have p1652_2 := h1652c.2.2.1
                        have p1652_3 := h1652c.2.2.2
                        linarith only [h0, h1365, h1592, h1646, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1652_1]
                      · have p1652_0 := h1652c.1
                        have p1652_1 := h1652c.2.1
                        have p1652_2 := h1652c.2.2.1
                        have p1652_3 := h1652c.2.2.2
                        linarith only [h0, h1365, h1592, h1593, h1646, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1652_1]
                      · have p1652_0 := h1652c.1
                        have p1652_1 := h1652c.2.1
                        have p1652_2 := h1652c.2.2.1
                        have p1652_3 := h1652c.2.2.2
                        linarith only [h2, hlam, p1652_0]
                      · have p1652_0 := h1652c.1
                        have p1652_1 := h1652c.2.1
                        have p1652_2 := h1652c.2.2.1
                        have p1652_3 := h1652c.2.2.2
                        linarith only [h1592, hlam, p1652_1]
                      · have p1652_0 := h1652c.1
                        have p1652_1 := h1652c.2.1
                        have p1652_2 := h1652c.2.2.1
                        have p1652_3 := h1652c.2.2.2
                        linarith only [h1642, hlam, p1652_0]
                      · have p1652_0 := h1652c.1
                        have p1652_1 := h1652c.2.1
                        have p1652_2 := h1652c.2.2.1
                        have p1652_3 := h1652c.2.2.2
                        linarith only [hlam, p1652_0]
                      · have p1652_0 := h1652c.1
                        have p1652_1 := h1652c.2.1
                        have p1652_2 := h1652c.2.2.1
                        have p1652_3 := h1652c.2.2.2
                        linarith only [h1644, hlam, p1652_1]
                      · have p1652_0 := h1652c.1
                        have p1652_1 := h1652c.2.1
                        have p1652_2 := h1652c.2.2.1
                        have p1652_3 := h1652c.2.2.2
                        linarith only [h3, hlam, p1652_0]
                      · have p1652_0 := h1652c.1
                        have p1652_1 := h1652c.2.1
                        have p1652_2 := h1652c.2.2.1
                        have p1652_3 := h1652c.2.2.2
                        linarith only [h1592, h1646, hc15, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1652_1]
                      · have p1652_0 := h1652c.1
                        have p1652_1 := h1652c.2.1
                        have p1652_2 := h1652c.2.2.1
                        have p1652_3 := h1652c.2.2.2
                        linarith only [h1643, hlam, p1652_0]
                      · have p1652_0 := h1652c.1
                        have p1652_1 := h1652c.2.1
                        have p1652_2 := h1652c.2.2.1
                        have p1652_3 := h1652c.2.2.2
                        linarith only [h0, h1365, h1592, h1643, h1646, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1652_1]
                      · have p1652_0 := h1652c.1
                        have p1652_1 := h1652c.2.1
                        have p1652_2 := h1652c.2.2.1
                        have p1652_3 := h1652c.2.2.2
                        linarith only [hlam, p1652_0]
                · linarith only [h1365, h1643, h1647, hlam]
              · linarith only [h1365, h1592, h1646, h7, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h1684 | h1684
            · linarith only [h1684, h2, h9, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1686 | h1686
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1687 | h1687
                · linarith only [h0, h1365, h1592, h1643, h1686, h1687, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                · linarith only [h0, h1365, h1592, h1686, h1687, h4, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
              · linarith only [h0, h1365, h1592, h1686, h4, h7, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
        · linarith only [h1365, h1592, h1642, h7, h9, hc24, hc45, hlam, hphi]
    · rcases m.htr 1 2 5 (by decide) (by decide) with h1692 | h1692
      · rcases m.htr 1 3 4 (by decide) (by decide) with h1693 | h1693
        · rcases m.htr 1 3 5 (by decide) (by decide) with h1694 | h1694
          · rcases m.htr 1 4 5 (by decide) (by decide) with h1695 | h1695
            · linarith only [h1592, h1692, h1695, h5, h9, hc14, hc25, hlam, hphi, ht01, ht0b, ht5b]
            · linarith only [h1592, h1692, h1695, hlam]
          · linarith only [h1365, h1692, h1694, hlam]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h1699 | h1699
          · rcases m.htr 1 4 5 (by decide) (by decide) with h1700 | h1700
            · linarith only [h1365, h1692, h1693, h1700, h7, h9, hc14, hc25, hlam, hphi, ht01, ht0b, ht5b]
            · linarith only [h1592, h1692, h1700, hlam]
          · linarith only [h1365, h1692, h1699, hlam]
      · rcases m.htr 1 3 4 (by decide) (by decide) with h1704 | h1704
        · rcases m.htr 1 3 5 (by decide) (by decide) with h1705 | h1705
          · rcases m.htr 1 4 5 (by decide) (by decide) with h1706 | h1706
            · linarith only [h1706, h2, h9, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1708 | h1708
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1709 | h1709
                · rcases m.htr 2 4 5 (by decide) (by decide) with h1710 | h1710
                  · linarith only [h1710, h5, h9, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1712 | h1712
                    · linarith only [h1, h1704, h1712, h5, h9, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
                    · rcases h1bigk with h1714c | h1714c | h1714c | h1714c | h1714c | h1714c | h1714c | h1714c | h1714c | h1714c | h1714c | h1714c | h1714c | h1714c | h1714c | h1714c | h1714c | h1714c | h1714c | h1714c | h1714c | h1714c | h1714c | h1714c | h1714c
                      · have p1714_0 := h1714c.1
                        have p1714_1 := h1714c.2.1
                        have p1714_2 := h1714c.2.2.1
                        have p1714_3 := h1714c.2.2.2
                        linarith only [hlam, p1714_0]
                      · have p1714_0 := h1714c.1
                        have p1714_1 := h1714c.2.1
                        have p1714_2 := h1714c.2.2.1
                        have p1714_3 := h1714c.2.2.2
                        rcases p1714_3 (m.d 0 1) (by simp) with h1716 | h1716
                        · rcases p1714_3 (m.d 1 2) (by simp) with h1717 | h1717
                          · linarith only [h1717, hlam, p1714_0]
                          · rcases p1714_3 (m.d 1 3) (by simp) with h1719 | h1719
                            · linarith only [h1, h1719, hlam]
                            · linarith only [h1365, h1719, hlam]
                        · linarith only [h1716, hlam, p1714_0]
                      · have p1714_0 := h1714c.1
                        have p1714_1 := h1714c.2.1
                        have p1714_2 := h1714c.2.2.1
                        have p1714_3 := h1714c.2.2.2
                        linarith only [h1705, hc01, hc35, hlam, hphi, ht0b, ht5b, p1714_1]
                      · have p1714_0 := h1714c.1
                        have p1714_1 := h1714c.2.1
                        have p1714_2 := h1714c.2.2.1
                        have p1714_3 := h1714c.2.2.2
                        rcases p1714_3 (m.d 0 1) (by simp) with h1724 | h1724
                        · rcases p1714_3 (m.d 1 2) (by simp) with h1725 | h1725
                          · linarith only [h0, h1725, hlam]
                          · rcases p1714_3 (m.d 1 3) (by simp) with h1727 | h1727
                            · linarith only [h1, h1727, hlam]
                            · linarith only [h1704, h1727, hlam]
                        · linarith only [h1724, hlam, p1714_0]
                      · have p1714_0 := h1714c.1
                        have p1714_1 := h1714c.2.1
                        have p1714_2 := h1714c.2.2.1
                        have p1714_3 := h1714c.2.2.2
                        rcases p1714_3 (m.d 0 1) (by simp) with h1731 | h1731
                        · rcases p1714_3 (m.d 1 2) (by simp) with h1732 | h1732
                          · linarith only [h0, h1732, hlam]
                          · rcases p1714_3 (m.d 1 3) (by simp) with h1734 | h1734
                            · linarith only [h1, h1734, hlam]
                            · linarith only [h1705, h1734, hlam]
                        · linarith only [h1731, hlam, p1714_0]
                      · have p1714_0 := h1714c.1
                        have p1714_1 := h1714c.2.1
                        have p1714_2 := h1714c.2.2.1
                        have p1714_3 := h1714c.2.2.2
                        linarith only [h0, hlam, p1714_0]
                      · have p1714_0 := h1714c.1
                        have p1714_1 := h1714c.2.1
                        have p1714_2 := h1714c.2.2.1
                        have p1714_3 := h1714c.2.2.2
                        linarith only [hlam, p1714_0]
                      · have p1714_0 := h1714c.1
                        have p1714_1 := h1714c.2.1
                        have p1714_2 := h1714c.2.2.1
                        have p1714_3 := h1714c.2.2.2
                        linarith only [h1365, hlam, p1714_0]
                      · have p1714_0 := h1714c.1
                        have p1714_1 := h1714c.2.1
                        have p1714_2 := h1714c.2.2.1
                        have p1714_3 := h1714c.2.2.2
                        linarith only [h1592, hlam, p1714_0]
                      · have p1714_0 := h1714c.1
                        have p1714_1 := h1714c.2.1
                        have p1714_2 := h1714c.2.2.1
                        have p1714_3 := h1714c.2.2.2
                        linarith only [h1692, hlam, p1714_0]
                      · have p1714_0 := h1714c.1
                        have p1714_1 := h1714c.2.1
                        have p1714_2 := h1714c.2.2.1
                        have p1714_3 := h1714c.2.2.2
                        linarith only [h1, hlam, p1714_0]
                      · have p1714_0 := h1714c.1
                        have p1714_1 := h1714c.2.1
                        have p1714_2 := h1714c.2.2.1
                        have p1714_3 := h1714c.2.2.2
                        linarith only [h1, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1714_1]
                      · have p1714_0 := h1714c.1
                        have p1714_1 := h1714c.2.1
                        have p1714_2 := h1714c.2.2.1
                        have p1714_3 := h1714c.2.2.2
                        linarith only [hlam, p1714_0]
                      · have p1714_0 := h1714c.1
                        have p1714_1 := h1714c.2.1
                        have p1714_2 := h1714c.2.2.1
                        have p1714_3 := h1714c.2.2.2
                        linarith only [h1365, h4, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b, p1714_1]
                      · have p1714_0 := h1714c.1
                        have p1714_1 := h1714c.2.1
                        have p1714_2 := h1714c.2.2.1
                        have p1714_3 := h1714c.2.2.2
                        linarith only [h0, h1365, h4, hc01, hc15, hlam, hphi, ht0b, ht5b, p1714_1]
                      · have p1714_0 := h1714c.1
                        have p1714_1 := h1714c.2.1
                        have p1714_2 := h1714c.2.2.1
                        have p1714_3 := h1714c.2.2.2
                        linarith only [h2, hlam, p1714_0]
                      · have p1714_0 := h1714c.1
                        have p1714_1 := h1714c.2.1
                        have p1714_2 := h1714c.2.2.1
                        have p1714_3 := h1714c.2.2.2
                        linarith only [h2, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1714_1]
                      · have p1714_0 := h1714c.1
                        have p1714_1 := h1714c.2.1
                        have p1714_2 := h1714c.2.2.1
                        have p1714_3 := h1714c.2.2.2
                        linarith only [h1704, hlam, p1714_0]
                      · have p1714_0 := h1714c.1
                        have p1714_1 := h1714c.2.1
                        have p1714_2 := h1714c.2.2.1
                        have p1714_3 := h1714c.2.2.2
                        linarith only [hlam, p1714_0]
                      · have p1714_0 := h1714c.1
                        have p1714_1 := h1714c.2.1
                        have p1714_2 := h1714c.2.2.1
                        have p1714_3 := h1714c.2.2.2
                        linarith only [h1706, hlam, p1714_1]
                      · have p1714_0 := h1714c.1
                        have p1714_1 := h1714c.2.1
                        have p1714_2 := h1714c.2.2.1
                        have p1714_3 := h1714c.2.2.2
                        linarith only [h3, hlam, p1714_0]
                      · have p1714_0 := h1714c.1
                        have p1714_1 := h1714c.2.1
                        have p1714_2 := h1714c.2.2.1
                        have p1714_3 := h1714c.2.2.2
                        linarith only [h3, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1714_1]
                      · have p1714_0 := h1714c.1
                        have p1714_1 := h1714c.2.1
                        have p1714_2 := h1714c.2.2.1
                        have p1714_3 := h1714c.2.2.2
                        linarith only [h1705, hlam, p1714_0]
                      · have p1714_0 := h1714c.1
                        have p1714_1 := h1714c.2.1
                        have p1714_2 := h1714c.2.2.1
                        have p1714_3 := h1714c.2.2.2
                        linarith only [h3, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p1714_1]
                      · have p1714_0 := h1714c.1
                        have p1714_1 := h1714c.2.1
                        have p1714_2 := h1714c.2.2.1
                        have p1714_3 := h1714c.2.2.2
                        linarith only [hlam, p1714_0]
                · linarith only [h1365, h1705, h1709, hlam]
              · linarith only [h1365, h1708, h7, h9, hc12, hc45, hlam, hphi, ht23, ht34]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h1760 | h1760
            · linarith only [h1760, h2, h9, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1762 | h1762
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1763 | h1763
                · linarith only [h1704, h1705, h1763, h4, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h1765 | h1765
                  · linarith only [h1762, h1763, h1765, h8, h9, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1767 | h1767
                    · linarith only [h1592, h1704, h1762, h1763, h1767, h8, h9, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                    · rcases h1bigk with h1769c | h1769c | h1769c | h1769c | h1769c | h1769c | h1769c | h1769c | h1769c | h1769c | h1769c | h1769c | h1769c | h1769c | h1769c | h1769c | h1769c | h1769c | h1769c | h1769c | h1769c | h1769c | h1769c | h1769c | h1769c
                      · have p1769_0 := h1769c.1
                        have p1769_1 := h1769c.2.1
                        have p1769_2 := h1769c.2.2.1
                        have p1769_3 := h1769c.2.2.2
                        linarith only [hlam, p1769_0]
                      · have p1769_0 := h1769c.1
                        have p1769_1 := h1769c.2.1
                        have p1769_2 := h1769c.2.2.1
                        have p1769_3 := h1769c.2.2.2
                        rcases p1769_3 (m.d 0 1) (by simp) with h1771 | h1771
                        · rcases p1769_3 (m.d 1 2) (by simp) with h1772 | h1772
                          · linarith only [h1772, hlam, p1769_0]
                          · rcases p1769_3 (m.d 1 3) (by simp) with h1774 | h1774
                            · linarith only [h1, h1774, hlam]
                            · linarith only [h1365, h1774, hlam]
                        · linarith only [h1771, hlam, p1769_0]
                      · have p1769_0 := h1769c.1
                        have p1769_1 := h1769c.2.1
                        have p1769_2 := h1769c.2.2.1
                        have p1769_3 := h1769c.2.2.2
                        linarith only [h1704, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1769_1]
                      · have p1769_0 := h1769c.1
                        have p1769_1 := h1769c.2.1
                        have p1769_2 := h1769c.2.2.1
                        have p1769_3 := h1769c.2.2.2
                        rcases p1769_3 (m.d 0 1) (by simp) with h1779 | h1779
                        · rcases p1769_3 (m.d 1 2) (by simp) with h1780 | h1780
                          · linarith only [h0, h1780, hlam]
                          · rcases p1769_3 (m.d 1 3) (by simp) with h1782 | h1782
                            · linarith only [h1, h1782, hlam]
                            · linarith only [h1704, h1782, hlam]
                        · linarith only [h1779, hlam, p1769_0]
                      · have p1769_0 := h1769c.1
                        have p1769_1 := h1769c.2.1
                        have p1769_2 := h1769c.2.2.1
                        have p1769_3 := h1769c.2.2.2
                        linarith only [h1704, h1705, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1769_1]
                      · have p1769_0 := h1769c.1
                        have p1769_1 := h1769c.2.1
                        have p1769_2 := h1769c.2.2.1
                        have p1769_3 := h1769c.2.2.2
                        linarith only [h0, hlam, p1769_0]
                      · have p1769_0 := h1769c.1
                        have p1769_1 := h1769c.2.1
                        have p1769_2 := h1769c.2.2.1
                        have p1769_3 := h1769c.2.2.2
                        linarith only [hlam, p1769_0]
                      · have p1769_0 := h1769c.1
                        have p1769_1 := h1769c.2.1
                        have p1769_2 := h1769c.2.2.1
                        have p1769_3 := h1769c.2.2.2
                        linarith only [h1365, hlam, p1769_0]
                      · have p1769_0 := h1769c.1
                        have p1769_1 := h1769c.2.1
                        have p1769_2 := h1769c.2.2.1
                        have p1769_3 := h1769c.2.2.2
                        linarith only [h1592, hlam, p1769_0]
                      · have p1769_0 := h1769c.1
                        have p1769_1 := h1769c.2.1
                        have p1769_2 := h1769c.2.2.1
                        have p1769_3 := h1769c.2.2.2
                        linarith only [h1692, hlam, p1769_0]
                      · have p1769_0 := h1769c.1
                        have p1769_1 := h1769c.2.1
                        have p1769_2 := h1769c.2.2.1
                        have p1769_3 := h1769c.2.2.2
                        linarith only [h1, hlam, p1769_0]
                      · have p1769_0 := h1769c.1
                        have p1769_1 := h1769c.2.1
                        have p1769_2 := h1769c.2.2.1
                        have p1769_3 := h1769c.2.2.2
                        linarith only [h1, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1769_1]
                      · have p1769_0 := h1769c.1
                        have p1769_1 := h1769c.2.1
                        have p1769_2 := h1769c.2.2.1
                        have p1769_3 := h1769c.2.2.2
                        linarith only [hlam, p1769_0]
                      · have p1769_0 := h1769c.1
                        have p1769_1 := h1769c.2.1
                        have p1769_2 := h1769c.2.2.1
                        have p1769_3 := h1769c.2.2.2
                        linarith only [h1365, h1763, h8, hc03, hc14, hlam, hphi, ht0b, ht45, ht5b, p1769_1]
                      · have p1769_0 := h1769c.1
                        have p1769_1 := h1769c.2.1
                        have p1769_2 := h1769c.2.2.1
                        have p1769_3 := h1769c.2.2.2
                        linarith only [h1705, hlam, p1769_1]
                      · have p1769_0 := h1769c.1
                        have p1769_1 := h1769c.2.1
                        have p1769_2 := h1769c.2.2.1
                        have p1769_3 := h1769c.2.2.2
                        linarith only [h2, hlam, p1769_0]
                      · have p1769_0 := h1769c.1
                        have p1769_1 := h1769c.2.1
                        have p1769_2 := h1769c.2.2.1
                        have p1769_3 := h1769c.2.2.2
                        linarith only [h2, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1769_1]
                      · have p1769_0 := h1769c.1
                        have p1769_1 := h1769c.2.1
                        have p1769_2 := h1769c.2.2.1
                        have p1769_3 := h1769c.2.2.2
                        linarith only [h1704, hlam, p1769_0]
                      · have p1769_0 := h1769c.1
                        have p1769_1 := h1769c.2.1
                        have p1769_2 := h1769c.2.2.1
                        have p1769_3 := h1769c.2.2.2
                        linarith only [hlam, p1769_0]
                      · have p1769_0 := h1769c.1
                        have p1769_1 := h1769c.2.1
                        have p1769_2 := h1769c.2.2.1
                        have p1769_3 := h1769c.2.2.2
                        linarith only [h1760, hlam, p1769_1]
                      · have p1769_0 := h1769c.1
                        have p1769_1 := h1769c.2.1
                        have p1769_2 := h1769c.2.2.1
                        have p1769_3 := h1769c.2.2.2
                        linarith only [h3, hlam, p1769_0]
                      · have p1769_0 := h1769c.1
                        have p1769_1 := h1769c.2.1
                        have p1769_2 := h1769c.2.2.1
                        have p1769_3 := h1769c.2.2.2
                        linarith only [h3, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1769_1]
                      · have p1769_0 := h1769c.1
                        have p1769_1 := h1769c.2.1
                        have p1769_2 := h1769c.2.2.1
                        have p1769_3 := h1769c.2.2.2
                        linarith only [h3, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p1769_1]
                      · have p1769_0 := h1769c.1
                        have p1769_1 := h1769c.2.1
                        have p1769_2 := h1769c.2.2.1
                        have p1769_3 := h1769c.2.2.2
                        linarith only [h0, h1705, h4, h8, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p1769_1]
                      · have p1769_0 := h1769c.1
                        have p1769_1 := h1769c.2.1
                        have p1769_2 := h1769c.2.2.1
                        have p1769_3 := h1769c.2.2.2
                        linarith only [hlam, p1769_0]
              · linarith only [h1, h1365, h1704, h1762, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h1808 | h1808
          · rcases m.htr 1 4 5 (by decide) (by decide) with h1809 | h1809
            · linarith only [h1704, h1808, h1809, h7, h9, hc14, hc35, hlam, hphi, ht01, ht0b, ht5b]
            · linarith only [h1704, h1808, h1809, hlam]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h1812 | h1812
            · linarith only [h1812, h2, h9, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1814 | h1814
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1815 | h1815
                · rcases m.htr 2 4 5 (by decide) (by decide) with h1816 | h1816
                  · linarith only [h1816, h5, h9, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1818 | h1818
                    · linarith only [h0, h1814, h1818, h4, h9, hc01, hc04, hlam, hphi, ht0b, ht45, ht5b]
                    · rcases h1bigk with h1820c | h1820c | h1820c | h1820c | h1820c | h1820c | h1820c | h1820c | h1820c | h1820c | h1820c | h1820c | h1820c | h1820c | h1820c | h1820c | h1820c | h1820c | h1820c | h1820c | h1820c | h1820c | h1820c | h1820c | h1820c
                      · have p1820_0 := h1820c.1
                        have p1820_1 := h1820c.2.1
                        have p1820_2 := h1820c.2.2.1
                        have p1820_3 := h1820c.2.2.2
                        linarith only [hlam, p1820_0]
                      · have p1820_0 := h1820c.1
                        have p1820_1 := h1820c.2.1
                        have p1820_2 := h1820c.2.2.1
                        have p1820_3 := h1820c.2.2.2
                        rcases p1820_3 (m.d 0 1) (by simp) with h1822 | h1822
                        · rcases p1820_3 (m.d 1 2) (by simp) with h1823 | h1823
                          · linarith only [h1823, hlam, p1820_0]
                          · rcases p1820_3 (m.d 1 3) (by simp) with h1825 | h1825
                            · linarith only [h1, h1825, hlam]
                            · linarith only [h1365, h1825, hlam]
                        · linarith only [h1822, hlam, p1820_0]
                      · have p1820_0 := h1820c.1
                        have p1820_1 := h1820c.2.1
                        have p1820_2 := h1820c.2.2.1
                        have p1820_3 := h1820c.2.2.2
                        rcases p1820_3 (m.d 0 1) (by simp) with h1829 | h1829
                        · rcases p1820_3 (m.d 1 2) (by simp) with h1830 | h1830
                          · linarith only [h0, h1830, hlam]
                          · rcases p1820_3 (m.d 1 3) (by simp) with h1832 | h1832
                            · linarith only [h1832, hlam, p1820_0]
                            · rcases p1820_3 (m.d 1 4) (by simp) with h1834 | h1834
                              · linarith only [h1834, h2, hlam]
                              · linarith only [h1704, h1834, hlam]
                        · linarith only [h1829, hlam, p1820_0]
                      · have p1820_0 := h1820c.1
                        have p1820_1 := h1820c.2.1
                        have p1820_2 := h1820c.2.2.1
                        have p1820_3 := h1820c.2.2.2
                        rcases p1820_3 (m.d 0 1) (by simp) with h1838 | h1838
                        · rcases p1820_3 (m.d 1 2) (by simp) with h1839 | h1839
                          · linarith only [h0, h1839, hlam]
                          · rcases p1820_3 (m.d 1 3) (by simp) with h1841 | h1841
                            · linarith only [h1, h1841, hlam]
                            · rcases p1820_3 (m.d 1 4) (by simp) with h1843 | h1843
                              · linarith only [h1843, hlam, p1820_0]
                              · rcases p1820_3 (m.d 1 5) (by simp) with h1845 | h1845
                                · linarith only [h1845, h3, hlam]
                                · linarith only [h1812, h1845, hlam]
                        · linarith only [h1838, hlam, p1820_0]
                      · have p1820_0 := h1820c.1
                        have p1820_1 := h1820c.2.1
                        have p1820_2 := h1820c.2.2.1
                        have p1820_3 := h1820c.2.2.2
                        rcases p1820_3 (m.d 0 1) (by simp) with h1849 | h1849
                        · rcases p1820_3 (m.d 1 2) (by simp) with h1850 | h1850
                          · linarith only [h0, h1850, hlam]
                          · rcases p1820_3 (m.d 1 3) (by simp) with h1852 | h1852
                            · linarith only [h1, h1852, hlam]
                            · rcases p1820_3 (m.d 1 4) (by simp) with h1854 | h1854
                              · linarith only [h1854, h2, hlam]
                              · rcases p1820_3 (m.d 1 5) (by simp) with h1856 | h1856
                                · linarith only [h1856, hlam, p1820_0]
                                · rcases h1emin with h1858 | h1858 | h1858 | h1858 | h1858
                                  · rcases h5bigk with h1859c | h1859c | h1859c | h1859c | h1859c | h1859c | h1859c | h1859c | h1859c | h1859c | h1859c | h1859c | h1859c | h1859c | h1859c | h1859c | h1859c | h1859c | h1859c | h1859c | h1859c | h1859c | h1859c | h1859c | h1859c
                                    · have p1859_0 := h1859c.1
                                      have p1859_1 := h1859c.2.1
                                      have p1859_2 := h1859c.2.2.1
                                      have p1859_3 := h1859c.2.2.2
                                      linarith only [hlam, p1859_0]
                                    · have p1859_0 := h1859c.1
                                      have p1859_1 := h1859c.2.1
                                      have p1859_2 := h1859c.2.2.1
                                      have p1859_3 := h1859c.2.2.2
                                      rcases p1859_3 (m.d 0 5) (by simp) with h1861 | h1861
                                      · rcases p1859_3 (m.d 1 5) (by simp) with h1862 | h1862
                                        · linarith only [h1862, h3, hlam]
                                        · rcases p1859_3 (m.d 2 5) (by simp) with h1864 | h1864
                                          · linarith only [h1864, h6, hlam]
                                          · linarith only [h1692, h1864, hlam]
                                      · linarith only [h1861, h3, hlam]
                                    · have p1859_0 := h1859c.1
                                      have p1859_1 := h1859c.2.1
                                      have p1859_2 := h1859c.2.2.1
                                      have p1859_3 := h1859c.2.2.2
                                      linarith only [h1692, h9, hc12, hc45, hlam, hphi, ht23, ht34, p1859_1]
                                    · have p1859_0 := h1859c.1
                                      have p1859_1 := h1859c.2.1
                                      have p1859_2 := h1859c.2.2.1
                                      have p1859_3 := h1859c.2.2.2
                                      linarith only [h1365, h1704, h1818, h9, hc12, hc45, hlam, hphi, ht23, ht34, p1859_1]
                                    · have p1859_0 := h1859c.1
                                      have p1859_1 := h1859c.2.1
                                      have p1859_2 := h1859c.2.2.1
                                      have p1859_3 := h1859c.2.2.2
                                      linarith only [h9, hlam, p1859_1]
                                    · have p1859_0 := h1859c.1
                                      have p1859_1 := h1859c.2.1
                                      have p1859_2 := h1859c.2.2.1
                                      have p1859_3 := h1859c.2.2.2
                                      linarith only [h3, hlam, p1859_0]
                                    · have p1859_0 := h1859c.1
                                      have p1859_1 := h1859c.2.1
                                      have p1859_2 := h1859c.2.2.1
                                      have p1859_3 := h1859c.2.2.2
                                      linarith only [hlam, p1859_0]
                                    · have p1859_0 := h1859c.1
                                      have p1859_1 := h1859c.2.1
                                      have p1859_2 := h1859c.2.2.1
                                      have p1859_3 := h1859c.2.2.2
                                      linarith only [h1692, hlam, p1859_0]
                                    · have p1859_0 := h1859c.1
                                      have p1859_1 := h1859c.2.1
                                      have p1859_2 := h1859c.2.2.1
                                      have p1859_3 := h1859c.2.2.2
                                      linarith only [h1808, hlam, p1859_1]
                                    · have p1859_0 := h1859c.1
                                      have p1859_1 := h1859c.2.1
                                      have p1859_2 := h1859c.2.2.1
                                      have p1859_3 := h1859c.2.2.2
                                      linarith only [h1812, hlam, p1859_1]
                                    · have p1859_0 := h1859c.1
                                      have p1859_1 := h1859c.2.1
                                      have p1859_2 := h1859c.2.2.1
                                      have p1859_3 := h1859c.2.2.2
                                      linarith only [h6, hlam, p1859_1]
                                    · have p1859_0 := h1859c.1
                                      have p1859_1 := h1859c.2.1
                                      have p1859_2 := h1859c.2.2.1
                                      have p1859_3 := h1859c.2.2.2
                                      rcases p1859_3 (m.d 0 5) (by simp) with h1877 | h1877
                                      · rcases p1859_3 (m.d 1 5) (by simp) with h1878 | h1878
                                        · linarith only [h1692, h1878, hlam]
                                        · rcases p1859_3 (m.d 2 5) (by simp) with h1880 | h1880
                                          · rcases p1859_3 (m.d 3 5) (by simp) with h1881 | h1881
                                            · linarith only [h1815, h1881, hlam]
                                            · linarith only [h1808, h1881, hlam]
                                          · linarith only [h1692, h1880, hlam]
                                      · linarith only [h1877, h3, hlam]
                                    · have p1859_0 := h1859c.1
                                      have p1859_1 := h1859c.2.1
                                      have p1859_2 := h1859c.2.2.1
                                      have p1859_3 := h1859c.2.2.2
                                      linarith only [hlam, p1859_0]
                                    · have p1859_0 := h1859c.1
                                      have p1859_1 := h1859c.2.1
                                      have p1859_2 := h1859c.2.2.1
                                      have p1859_3 := h1859c.2.2.2
                                      linarith only [h0, h1365, h1704, h1815, h1818, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1859_1]
                                    · have p1859_0 := h1859c.1
                                      have p1859_1 := h1859c.2.1
                                      have p1859_2 := h1859c.2.2.1
                                      have p1859_3 := h1859c.2.2.2
                                      linarith only [h1816, hlam, p1859_1]
                                    · have p1859_0 := h1859c.1
                                      have p1859_1 := h1859c.2.1
                                      have p1859_2 := h1859c.2.2.1
                                      have p1859_3 := h1859c.2.2.2
                                      linarith only [h8, hlam, p1859_0]
                                    · have p1859_0 := h1859c.1
                                      have p1859_1 := h1859c.2.1
                                      have p1859_2 := h1859c.2.2.1
                                      have p1859_3 := h1859c.2.2.2
                                      linarith only [h0, h1365, h1704, h1812, h1815, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1859_1]
                                    · have p1859_0 := h1859c.1
                                      have p1859_1 := h1859c.2.1
                                      have p1859_2 := h1859c.2.2.1
                                      have p1859_3 := h1859c.2.2.2
                                      linarith only [h1815, hlam, p1859_0]
                                    · have p1859_0 := h1859c.1
                                      have p1859_1 := h1859c.2.1
                                      have p1859_2 := h1859c.2.2.1
                                      have p1859_3 := h1859c.2.2.2
                                      linarith only [hlam, p1859_0]
                                    · have p1859_0 := h1859c.1
                                      have p1859_1 := h1859c.2.1
                                      have p1859_2 := h1859c.2.2.1
                                      have p1859_3 := h1859c.2.2.2
                                      linarith only [h1818, hlam, p1859_1]
                                    · have p1859_0 := h1859c.1
                                      have p1859_1 := h1859c.2.1
                                      have p1859_2 := h1859c.2.2.1
                                      have p1859_3 := h1859c.2.2.2
                                      linarith only [h1365, h1704, h1814, h5, h9, hc12, hc45, hlam, hphi, ht23, ht34, p1859_1]
                                    · have p1859_0 := h1859c.1
                                      have p1859_1 := h1859c.2.1
                                      have p1859_2 := h1859c.2.2.1
                                      have p1859_3 := h1859c.2.2.2
                                      rcases p1859_3 (m.d 0 5) (by simp) with h1895 | h1895
                                      · linarith only [h1895, h9, hlam]
                                      · linarith only [h1895, h3, hlam]
                                    · have p1859_0 := h1859c.1
                                      have p1859_1 := h1859c.2.1
                                      have p1859_2 := h1859c.2.2.1
                                      have p1859_3 := h1859c.2.2.2
                                      linarith only [h1692, hc12, hc45, hlam, hphi, ht23, ht34, p1859_1]
                                    · have p1859_0 := h1859c.1
                                      have p1859_1 := h1859c.2.1
                                      have p1859_2 := h1859c.2.2.1
                                      have p1859_3 := h1859c.2.2.2
                                      linarith only [h1365, h1808, hc12, hc45, hlam, hphi, ht23, ht34, p1859_1]
                                    · have p1859_0 := h1859c.1
                                      have p1859_1 := h1859c.2.1
                                      have p1859_2 := h1859c.2.2.1
                                      have p1859_3 := h1859c.2.2.2
                                      linarith only [hlam, p1859_0]
                                  · linarith only [h1365, h1704, h1814, h1858, hc24, hlam, ht12]
                                  · linarith only [h1704, h1814, h1858, hc24, hlam, ht12]
                                  · linarith only [h1812, h1858, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1820_1]
                                  · linarith only [h1858, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1820_1]
                        · linarith only [h1849, hlam, p1820_0]
                      · have p1820_0 := h1820c.1
                        have p1820_1 := h1820c.2.1
                        have p1820_2 := h1820c.2.2.1
                        have p1820_3 := h1820c.2.2.2
                        linarith only [h0, hlam, p1820_0]
                      · have p1820_0 := h1820c.1
                        have p1820_1 := h1820c.2.1
                        have p1820_2 := h1820c.2.2.1
                        have p1820_3 := h1820c.2.2.2
                        linarith only [hlam, p1820_0]
                      · have p1820_0 := h1820c.1
                        have p1820_1 := h1820c.2.1
                        have p1820_2 := h1820c.2.2.1
                        have p1820_3 := h1820c.2.2.2
                        linarith only [h1365, hlam, p1820_0]
                      · have p1820_0 := h1820c.1
                        have p1820_1 := h1820c.2.1
                        have p1820_2 := h1820c.2.2.1
                        have p1820_3 := h1820c.2.2.2
                        linarith only [h1592, hlam, p1820_0]
                      · have p1820_0 := h1820c.1
                        have p1820_1 := h1820c.2.1
                        have p1820_2 := h1820c.2.2.1
                        have p1820_3 := h1820c.2.2.2
                        linarith only [h1692, hlam, p1820_0]
                      · have p1820_0 := h1820c.1
                        have p1820_1 := h1820c.2.1
                        have p1820_2 := h1820c.2.2.1
                        have p1820_3 := h1820c.2.2.2
                        linarith only [h1, hlam, p1820_0]
                      · have p1820_0 := h1820c.1
                        have p1820_1 := h1820c.2.1
                        have p1820_2 := h1820c.2.2.1
                        have p1820_3 := h1820c.2.2.2
                        linarith only [h1704, h1814, h1816, hc12, hc25, hlam, hphi, p1820_1]
                      · have p1820_0 := h1820c.1
                        have p1820_1 := h1820c.2.1
                        have p1820_2 := h1820c.2.2.1
                        have p1820_3 := h1820c.2.2.2
                        linarith only [hlam, p1820_0]
                      · have p1820_0 := h1820c.1
                        have p1820_1 := h1820c.2.1
                        have p1820_2 := h1820c.2.2.1
                        have p1820_3 := h1820c.2.2.2
                        linarith only [h1704, hlam, p1820_1]
                      · have p1820_0 := h1820c.1
                        have p1820_1 := h1820c.2.1
                        have p1820_2 := h1820c.2.2.1
                        have p1820_3 := h1820c.2.2.2
                        linarith only [h1808, hlam, p1820_1]
                      · have p1820_0 := h1820c.1
                        have p1820_1 := h1820c.2.1
                        have p1820_2 := h1820c.2.2.1
                        have p1820_3 := h1820c.2.2.2
                        linarith only [h2, hlam, p1820_0]
                      · have p1820_0 := h1820c.1
                        have p1820_1 := h1820c.2.1
                        have p1820_2 := h1820c.2.2.1
                        have p1820_3 := h1820c.2.2.2
                        linarith only [h2, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1820_1]
                      · have p1820_0 := h1820c.1
                        have p1820_1 := h1820c.2.1
                        have p1820_2 := h1820c.2.2.1
                        have p1820_3 := h1820c.2.2.2
                        linarith only [h1704, h1814, h5, h9, hc13, hc45, hlam, hphi, ht34, p1820_1]
                      · have p1820_0 := h1820c.1
                        have p1820_1 := h1820c.2.1
                        have p1820_2 := h1820c.2.2.1
                        have p1820_3 := h1820c.2.2.2
                        linarith only [hlam, p1820_0]
                      · have p1820_0 := h1820c.1
                        have p1820_1 := h1820c.2.1
                        have p1820_2 := h1820c.2.2.1
                        have p1820_3 := h1820c.2.2.2
                        linarith only [h1812, hlam, p1820_1]
                      · have p1820_0 := h1820c.1
                        have p1820_1 := h1820c.2.1
                        have p1820_2 := h1820c.2.2.1
                        have p1820_3 := h1820c.2.2.2
                        linarith only [h3, hlam, p1820_0]
                      · have p1820_0 := h1820c.1
                        have p1820_1 := h1820c.2.1
                        have p1820_2 := h1820c.2.2.1
                        have p1820_3 := h1820c.2.2.2
                        linarith only [h3, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1820_1]
                      · have p1820_0 := h1820c.1
                        have p1820_1 := h1820c.2.1
                        have p1820_2 := h1820c.2.2.1
                        have p1820_3 := h1820c.2.2.2
                        linarith only [h0, h1365, h1808, h4, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1820_1]
                      · have p1820_0 := h1820c.1
                        have p1820_1 := h1820c.2.1
                        have p1820_2 := h1820c.2.2.1
                        have p1820_3 := h1820c.2.2.2
                        linarith only [h0, h1808, h4, h8, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p1820_1]
                      · have p1820_0 := h1820c.1
                        have p1820_1 := h1820c.2.1
                        have p1820_2 := h1820c.2.2.1
                        have p1820_3 := h1820c.2.2.2
                        linarith only [hlam, p1820_0]
                · linarith only [h0, h1365, h1704, h1814, h1815, h4, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
              · linarith only [h1365, h1814, h7, h9, hc12, hc45, hlam, hphi, ht23, ht34]

set_option maxHeartbeats 5636000 in
theorem r1l7_21_15_H_I_L_I_s6_x0_x0 (m : N7Model)
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
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
  have h1emin := hb1.2.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  rcases m.htr 0 4 5 (by decide) (by decide) with h9 | h9
  · exact r1l7_21_15_H_I_L_I_s6_x0_x0_x0 m hb1 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 h7 h8 h9
  · exact r1l7_21_15_H_I_L_I_s6_x0_x0_x1 m hb1 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 h7 h8 h9

set_option maxHeartbeats 5636000 in
theorem r1l7_21_15_H_I_L_I_s6_x0_x1 (m : N7Model)
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h8 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
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
  have h1emin := hb1.2.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  rcases m.htr 0 4 5 (by decide) (by decide) with h1928 | h1928
  · linarith only [h1928, h7, h8, hlam]
  · rcases m.htr 1 2 3 (by decide) (by decide) with h1930 | h1930
    · rcases m.htr 1 2 4 (by decide) (by decide) with h1931 | h1931
      · rcases m.htr 1 2 5 (by decide) (by decide) with h1932 | h1932
        · rcases m.htr 1 3 4 (by decide) (by decide) with h1933 | h1933
          · rcases m.htr 1 3 5 (by decide) (by decide) with h1934 | h1934
            · linarith only [h1, h1934, h8, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1936 | h1936
              · linarith only [h1928, h1936, h2, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1938 | h1938
                · rcases m.htr 2 3 5 (by decide) (by decide) with h1939 | h1939
                  · linarith only [h1, h1930, h1939, h8, hlam]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1941 | h1941
                    · linarith only [h1928, h1931, h1941, h2, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1943 | h1943
                      · linarith only [h1928, h1932, h1938, h1939, h1943, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · rcases h1bigk with h1945c | h1945c | h1945c | h1945c | h1945c | h1945c | h1945c | h1945c | h1945c | h1945c | h1945c | h1945c | h1945c | h1945c | h1945c | h1945c | h1945c | h1945c | h1945c | h1945c | h1945c | h1945c | h1945c | h1945c | h1945c
                        · have p1945_0 := h1945c.1
                          have p1945_1 := h1945c.2.1
                          have p1945_2 := h1945c.2.2.1
                          have p1945_3 := h1945c.2.2.2
                          linarith only [hlam, p1945_0]
                        · have p1945_0 := h1945c.1
                          have p1945_1 := h1945c.2.1
                          have p1945_2 := h1945c.2.2.1
                          have p1945_3 := h1945c.2.2.2
                          linarith only [h1932, h1939, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1945_1]
                        · have p1945_0 := h1945c.1
                          have p1945_1 := h1945c.2.1
                          have p1945_2 := h1945c.2.2.1
                          have p1945_3 := h1945c.2.2.2
                          linarith only [h1933, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1945_1]
                        · have p1945_0 := h1945c.1
                          have p1945_1 := h1945c.2.1
                          have p1945_2 := h1945c.2.2.1
                          have p1945_3 := h1945c.2.2.2
                          rcases p1945_3 (m.d 0 1) (by simp) with h1949 | h1949
                          · rcases p1945_3 (m.d 1 2) (by simp) with h1950 | h1950
                            · linarith only [h0, h1950, hlam]
                            · linarith only [h1931, h1950, hlam]
                          · linarith only [h1949, hlam, p1945_0]
                        · have p1945_0 := h1945c.1
                          have p1945_1 := h1945c.2.1
                          have p1945_2 := h1945c.2.2.1
                          have p1945_3 := h1945c.2.2.2
                          linarith only [h1930, h1934, h1938, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1945_1]
                        · have p1945_0 := h1945c.1
                          have p1945_1 := h1945c.2.1
                          have p1945_2 := h1945c.2.2.1
                          have p1945_3 := h1945c.2.2.2
                          linarith only [h0, hlam, p1945_0]
                        · have p1945_0 := h1945c.1
                          have p1945_1 := h1945c.2.1
                          have p1945_2 := h1945c.2.2.1
                          have p1945_3 := h1945c.2.2.2
                          linarith only [hlam, p1945_0]
                        · have p1945_0 := h1945c.1
                          have p1945_1 := h1945c.2.1
                          have p1945_2 := h1945c.2.2.1
                          have p1945_3 := h1945c.2.2.2
                          linarith only [h1930, h1938, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1945_1]
                        · have p1945_0 := h1945c.1
                          have p1945_1 := h1945c.2.1
                          have p1945_2 := h1945c.2.2.1
                          have p1945_3 := h1945c.2.2.2
                          linarith only [h0, h1931, h1938, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1945_1]
                        · have p1945_0 := h1945c.1
                          have p1945_1 := h1945c.2.1
                          have p1945_2 := h1945c.2.2.1
                          have p1945_3 := h1945c.2.2.2
                          linarith only [h0, h1930, h1934, h1938, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1945_1]
                        · have p1945_0 := h1945c.1
                          have p1945_1 := h1945c.2.1
                          have p1945_2 := h1945c.2.2.1
                          have p1945_3 := h1945c.2.2.2
                          linarith only [h1, hlam, p1945_0]
                        · have p1945_0 := h1945c.1
                          have p1945_1 := h1945c.2.1
                          have p1945_2 := h1945c.2.2.1
                          have p1945_3 := h1945c.2.2.2
                          linarith only [h1930, hlam, p1945_1]
                        · have p1945_0 := h1945c.1
                          have p1945_1 := h1945c.2.1
                          have p1945_2 := h1945c.2.2.1
                          have p1945_3 := h1945c.2.2.2
                          linarith only [hlam, p1945_0]
                        · have p1945_0 := h1945c.1
                          have p1945_1 := h1945c.2.1
                          have p1945_2 := h1945c.2.2.1
                          have p1945_3 := h1945c.2.2.2
                          linarith only [h1, h1931, h1938, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1945_1]
                        · have p1945_0 := h1945c.1
                          have p1945_1 := h1945c.2.1
                          have p1945_2 := h1945c.2.2.1
                          have p1945_3 := h1945c.2.2.2
                          linarith only [h1934, hlam, p1945_1]
                        · have p1945_0 := h1945c.1
                          have p1945_1 := h1945c.2.1
                          have p1945_2 := h1945c.2.2.1
                          have p1945_3 := h1945c.2.2.2
                          linarith only [h2, hlam, p1945_0]
                        · have p1945_0 := h1945c.1
                          have p1945_1 := h1945c.2.1
                          have p1945_2 := h1945c.2.2.1
                          have p1945_3 := h1945c.2.2.2
                          linarith only [h1931, hlam, p1945_1]
                        · have p1945_0 := h1945c.1
                          have p1945_1 := h1945c.2.1
                          have p1945_2 := h1945c.2.2.1
                          have p1945_3 := h1945c.2.2.2
                          linarith only [h1933, hlam, p1945_0]
                        · have p1945_0 := h1945c.1
                          have p1945_1 := h1945c.2.1
                          have p1945_2 := h1945c.2.2.1
                          have p1945_3 := h1945c.2.2.2
                          linarith only [hlam, p1945_0]
                        · have p1945_0 := h1945c.1
                          have p1945_1 := h1945c.2.1
                          have p1945_2 := h1945c.2.2.1
                          have p1945_3 := h1945c.2.2.2
                          linarith only [h1936, hlam, p1945_1]
                        · have p1945_0 := h1945c.1
                          have p1945_1 := h1945c.2.1
                          have p1945_2 := h1945c.2.2.1
                          have p1945_3 := h1945c.2.2.2
                          linarith only [h3, hlam, p1945_0]
                        · have p1945_0 := h1945c.1
                          have p1945_1 := h1945c.2.1
                          have p1945_2 := h1945c.2.2.1
                          have p1945_3 := h1945c.2.2.2
                          linarith only [h1932, hlam, p1945_1]
                        · have p1945_0 := h1945c.1
                          have p1945_1 := h1945c.2.1
                          have p1945_2 := h1945c.2.2.1
                          have p1945_3 := h1945c.2.2.2
                          linarith only [h3, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p1945_1]
                        · have p1945_0 := h1945c.1
                          have p1945_1 := h1945c.2.1
                          have p1945_2 := h1945c.2.2.1
                          have p1945_3 := h1945c.2.2.2
                          linarith only [h1931, h1938, h1943, h3, h8, hc34, hc45, hlam, hphi, p1945_1]
                        · have p1945_0 := h1945c.1
                          have p1945_1 := h1945c.2.1
                          have p1945_2 := h1945c.2.2.1
                          have p1945_3 := h1945c.2.2.2
                          linarith only [hlam, p1945_0]
                · linarith only [h1938, h7, h8, hc23, hc35, hlam, hphi]
          · linarith only [h1930, h1933, h7, h8, hc23, hc35, hlam, hphi]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h1977 | h1977
          · rcases m.htr 1 3 5 (by decide) (by decide) with h1978 | h1978
            · linarith only [h1930, h1932, h1978, h6, h8, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1980 | h1980
              · linarith only [h1928, h1980, h2, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1982 | h1982
                · linarith only [h0, h1930, h1932, h1982, h6, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                · linarith only [h1982, h7, h8, hc23, hc35, hlam, hphi]
          · linarith only [h1977, h7, h8, hc13, hc35, hlam, hphi]
      · linarith only [h1930, h1931, h5, h7, h8, hc23, hc35, hlam, hphi]
    · rcases m.htr 1 2 4 (by decide) (by decide) with h1987 | h1987
      · rcases m.htr 1 2 5 (by decide) (by decide) with h1988 | h1988
        · rcases m.htr 1 3 4 (by decide) (by decide) with h1989 | h1989
          · rcases m.htr 1 3 5 (by decide) (by decide) with h1990 | h1990
            · linarith only [h1930, h1987, h1990, h4, h8, hc13, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
            · linarith only [h1930, h1988, h1990, hlam]
          · linarith only [h1930, h1987, h1989, h7, h8, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h1994 | h1994
          · rcases m.htr 1 3 5 (by decide) (by decide) with h1995 | h1995
            · linarith only [h1, h1995, h8, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1997 | h1997
              · linarith only [h1928, h1930, h1987, h1997, h4, h8, hc04, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1999 | h1999
                · rcases m.htr 2 3 5 (by decide) (by decide) with h2000 | h2000
                  · linarith only [h2000, h4, h8, hlam]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h2002 | h2002
                    · linarith only [h1928, h1987, h2, h2002, h7, h8, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h2004 | h2004
                      · linarith only [h1928, h2004, h7, h8, hlam]
                      · linarith only [h1930, h1987, h2004, h4, h8, hc24, hc45, hlam, hphi]
                · linarith only [h1930, h1987, h1999, h7, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
          · linarith only [h1930, h1987, h1994, h7, h8, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h2009 | h2009
        · rcases m.htr 1 3 4 (by decide) (by decide) with h2010 | h2010
          · rcases m.htr 1 3 5 (by decide) (by decide) with h2011 | h2011
            · linarith only [h1, h2011, h8, hlam]
            · linarith only [h1930, h2009, h2011, hlam]
          · linarith only [h1930, h2009, h2010, h7, h8, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h2015 | h2015
          · rcases m.htr 1 3 5 (by decide) (by decide) with h2016 | h2016
            · linarith only [h1, h2016, h8, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h2018 | h2018
              · linarith only [h1928, h2, h2018, h7, h8, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h2020 | h2020
                · rcases m.htr 2 3 5 (by decide) (by decide) with h2021 | h2021
                  · linarith only [h2021, h4, h8, hlam]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h2023 | h2023
                    · linarith only [h1928, h2023, h5, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h2025 | h2025
                      · linarith only [h1, h1928, h2015, h2025, h5, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
                      · rcases h1bigk with h2027c | h2027c | h2027c | h2027c | h2027c | h2027c | h2027c | h2027c | h2027c | h2027c | h2027c | h2027c | h2027c | h2027c | h2027c | h2027c | h2027c | h2027c | h2027c | h2027c | h2027c | h2027c | h2027c | h2027c | h2027c
                        · have p2027_0 := h2027c.1
                          have p2027_1 := h2027c.2.1
                          have p2027_2 := h2027c.2.2.1
                          have p2027_3 := h2027c.2.2.2
                          linarith only [hlam, p2027_0]
                        · have p2027_0 := h2027c.1
                          have p2027_1 := h2027c.2.1
                          have p2027_2 := h2027c.2.2.1
                          have p2027_3 := h2027c.2.2.2
                          rcases p2027_3 (m.d 0 1) (by simp) with h2029 | h2029
                          · rcases p2027_3 (m.d 1 2) (by simp) with h2030 | h2030
                            · linarith only [h2030, hlam, p2027_0]
                            · rcases p2027_3 (m.d 1 3) (by simp) with h2032 | h2032
                              · linarith only [h1, h2032, hlam]
                              · linarith only [h1930, h2032, hlam]
                          · linarith only [h2029, hlam, p2027_0]
                        · have p2027_0 := h2027c.1
                          have p2027_1 := h2027c.2.1
                          have p2027_2 := h2027c.2.2.1
                          have p2027_3 := h2027c.2.2.2
                          linarith only [h2015, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2027_1]
                        · have p2027_0 := h2027c.1
                          have p2027_1 := h2027c.2.1
                          have p2027_2 := h2027c.2.2.1
                          have p2027_3 := h2027c.2.2.2
                          rcases p2027_3 (m.d 0 1) (by simp) with h2037 | h2037
                          · rcases p2027_3 (m.d 1 2) (by simp) with h2038 | h2038
                            · linarith only [h0, h2038, hlam]
                            · rcases p2027_3 (m.d 1 3) (by simp) with h2040 | h2040
                              · linarith only [h1, h2040, hlam]
                              · linarith only [h2015, h2040, hlam]
                          · linarith only [h2037, hlam, p2027_0]
                        · have p2027_0 := h2027c.1
                          have p2027_1 := h2027c.2.1
                          have p2027_2 := h2027c.2.2.1
                          have p2027_3 := h2027c.2.2.2
                          linarith only [h2015, h2016, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2027_1]
                        · have p2027_0 := h2027c.1
                          have p2027_1 := h2027c.2.1
                          have p2027_2 := h2027c.2.2.1
                          have p2027_3 := h2027c.2.2.2
                          linarith only [h0, hlam, p2027_0]
                        · have p2027_0 := h2027c.1
                          have p2027_1 := h2027c.2.1
                          have p2027_2 := h2027c.2.2.1
                          have p2027_3 := h2027c.2.2.2
                          linarith only [hlam, p2027_0]
                        · have p2027_0 := h2027c.1
                          have p2027_1 := h2027c.2.1
                          have p2027_2 := h2027c.2.2.1
                          have p2027_3 := h2027c.2.2.2
                          linarith only [h1930, hlam, p2027_0]
                        · have p2027_0 := h2027c.1
                          have p2027_1 := h2027c.2.1
                          have p2027_2 := h2027c.2.2.1
                          have p2027_3 := h2027c.2.2.2
                          linarith only [h1987, hlam, p2027_0]
                        · have p2027_0 := h2027c.1
                          have p2027_1 := h2027c.2.1
                          have p2027_2 := h2027c.2.2.1
                          have p2027_3 := h2027c.2.2.2
                          linarith only [h2009, hlam, p2027_0]
                        · have p2027_0 := h2027c.1
                          have p2027_1 := h2027c.2.1
                          have p2027_2 := h2027c.2.2.1
                          have p2027_3 := h2027c.2.2.2
                          linarith only [h1, hlam, p2027_0]
                        · have p2027_0 := h2027c.1
                          have p2027_1 := h2027c.2.1
                          have p2027_2 := h2027c.2.2.1
                          have p2027_3 := h2027c.2.2.2
                          linarith only [h1, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2027_1]
                        · have p2027_0 := h2027c.1
                          have p2027_1 := h2027c.2.1
                          have p2027_2 := h2027c.2.2.1
                          have p2027_3 := h2027c.2.2.2
                          linarith only [hlam, p2027_0]
                        · have p2027_0 := h2027c.1
                          have p2027_1 := h2027c.2.1
                          have p2027_2 := h2027c.2.2.1
                          have p2027_3 := h2027c.2.2.2
                          linarith only [h1930, h4, h8, hc14, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2027_1]
                        · have p2027_0 := h2027c.1
                          have p2027_1 := h2027c.2.1
                          have p2027_2 := h2027c.2.2.1
                          have p2027_3 := h2027c.2.2.2
                          linarith only [h2016, hlam, p2027_1]
                        · have p2027_0 := h2027c.1
                          have p2027_1 := h2027c.2.1
                          have p2027_2 := h2027c.2.2.1
                          have p2027_3 := h2027c.2.2.2
                          linarith only [h2, hlam, p2027_0]
                        · have p2027_0 := h2027c.1
                          have p2027_1 := h2027c.2.1
                          have p2027_2 := h2027c.2.2.1
                          have p2027_3 := h2027c.2.2.2
                          linarith only [h2, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2027_1]
                        · have p2027_0 := h2027c.1
                          have p2027_1 := h2027c.2.1
                          have p2027_2 := h2027c.2.2.1
                          have p2027_3 := h2027c.2.2.2
                          linarith only [h2015, hlam, p2027_0]
                        · have p2027_0 := h2027c.1
                          have p2027_1 := h2027c.2.1
                          have p2027_2 := h2027c.2.2.1
                          have p2027_3 := h2027c.2.2.2
                          linarith only [hlam, p2027_0]
                        · have p2027_0 := h2027c.1
                          have p2027_1 := h2027c.2.1
                          have p2027_2 := h2027c.2.2.1
                          have p2027_3 := h2027c.2.2.2
                          linarith only [h2018, hlam, p2027_1]
                        · have p2027_0 := h2027c.1
                          have p2027_1 := h2027c.2.1
                          have p2027_2 := h2027c.2.2.1
                          have p2027_3 := h2027c.2.2.2
                          linarith only [h3, hlam, p2027_0]
                        · have p2027_0 := h2027c.1
                          have p2027_1 := h2027c.2.1
                          have p2027_2 := h2027c.2.2.1
                          have p2027_3 := h2027c.2.2.2
                          linarith only [h3, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2027_1]
                        · have p2027_0 := h2027c.1
                          have p2027_1 := h2027c.2.1
                          have p2027_2 := h2027c.2.2.1
                          have p2027_3 := h2027c.2.2.2
                          linarith only [h3, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p2027_1]
                        · have p2027_0 := h2027c.1
                          have p2027_1 := h2027c.2.1
                          have p2027_2 := h2027c.2.2.1
                          have p2027_3 := h2027c.2.2.2
                          linarith only [h0, h2009, h6, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p2027_1]
                        · have p2027_0 := h2027c.1
                          have p2027_1 := h2027c.2.1
                          have p2027_2 := h2027c.2.2.1
                          have p2027_3 := h2027c.2.2.2
                          linarith only [hlam, p2027_0]
                · linarith only [h1, h2015, h2020, h8, hc23, hc35, hlam, hphi]
          · linarith only [h2015, h7, h8, hc13, hc35, hlam, hphi]

set_option maxHeartbeats 5636000 in
theorem r1l7_21_15_H_I_L_I_s6_x0 (m : N7Model)
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
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
  have h1emin := hb1.2.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  rcases m.htr 0 3 5 (by decide) (by decide) with h8 | h8
  · exact r1l7_21_15_H_I_L_I_s6_x0_x0 m hb1 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 h7 h8
  · exact r1l7_21_15_H_I_L_I_s6_x0_x1 m hb1 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 h7 h8

end R2N4
