import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_41S2
import Jsp000404.R1LeavesN7_41S3

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6812000 in
theorem r1l7_11_12_25_L_0_L_I_H_I_x0_x1_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h1 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (h1158 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
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
  have h1elo := hb1.1
  have h5bigk := hb5.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  rcases m.htr 1 2 5 (by decide) (by decide) with h1467 | h1467
  · linarith only [h0, h1, h1467, hlam]
  · rcases m.htr 1 3 5 (by decide) (by decide) with h1469 | h1469
    · rcases m.htr 1 4 5 (by decide) (by decide) with h1470 | h1470
      · linarith only [h0, h1158, h1470, hlam]
      · rcases m.htr 2 3 4 (by decide) (by decide) with h1472 | h1472
        · rcases m.htr 2 3 5 (by decide) (by decide) with h1473 | h1473
          · rcases m.htr 2 4 5 (by decide) (by decide) with h1474 | h1474
            · rcases m.htr 3 4 5 (by decide) (by decide) with h1475 | h1475
              · linarith only [h0, h1158, h1469, h1475, hlam]
              · rcases h5bigk with h1477c | h1477c | h1477c | h1477c | h1477c | h1477c | h1477c | h1477c | h1477c | h1477c | h1477c | h1477c | h1477c | h1477c | h1477c | h1477c | h1477c | h1477c | h1477c | h1477c | h1477c | h1477c | h1477c | h1477c | h1477c
                · have p1477_0 := h1477c.1
                  have p1477_1 := h1477c.2.1
                  have p1477_2 := h1477c.2.2.1
                  have p1477_3 := h1477c.2.2.2
                  linarith only [hlam, p1477_0]
                · have p1477_0 := h1477c.1
                  have p1477_1 := h1477c.2.1
                  have p1477_2 := h1477c.2.2.1
                  have p1477_3 := h1477c.2.2.2
                  linarith only [h1158, h1467, h1472, h1474, hc12, hc23, hlam, hphi, p1477_1]
                · have p1477_0 := h1477c.1
                  have p1477_1 := h1477c.2.1
                  have p1477_2 := h1477c.2.2.1
                  have p1477_3 := h1477c.2.2.2
                  linarith only [h1, hlam, p1477_0]
                · have p1477_0 := h1477c.1
                  have p1477_1 := h1477c.2.1
                  have p1477_2 := h1477c.2.2.1
                  have p1477_3 := h1477c.2.2.2
                  linarith only [h1158, h1472, h1474, h1475, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1477_1]
                · have p1477_0 := h1477c.1
                  have p1477_1 := h1477c.2.1
                  have p1477_2 := h1477c.2.2.1
                  have p1477_3 := h1477c.2.2.2
                  linarith only [h1158, hlam, p1477_0]
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
                  linarith only [h1467, hlam, p1477_0]
                · have p1477_0 := h1477c.1
                  have p1477_1 := h1477c.2.1
                  have p1477_2 := h1477c.2.2.1
                  have p1477_3 := h1477c.2.2.2
                  linarith only [h1475, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1477_1, u1elo4]
                · have p1477_0 := h1477c.1
                  have p1477_1 := h1477c.2.1
                  have p1477_2 := h1477c.2.2.1
                  have p1477_3 := h1477c.2.2.2
                  linarith only [h1470, hlam, p1477_0]
                · have p1477_0 := h1477c.1
                  have p1477_1 := h1477c.2.1
                  have p1477_2 := h1477c.2.2.1
                  have p1477_3 := h1477c.2.2.2
                  linarith only [h1, h1472, h1474, hc02, hc23, hlam, hphi, p1477_1]
                · have p1477_0 := h1477c.1
                  have p1477_1 := h1477c.2.1
                  have p1477_2 := h1477c.2.2.1
                  have p1477_3 := h1477c.2.2.2
                  linarith only [h1467, h1472, h1474, hc12, hc23, hlam, hphi, p1477_1]
                · have p1477_0 := h1477c.1
                  have p1477_1 := h1477c.2.1
                  have p1477_2 := h1477c.2.2.1
                  have p1477_3 := h1477c.2.2.2
                  linarith only [hlam, p1477_0]
                · have p1477_0 := h1477c.1
                  have p1477_1 := h1477c.2.1
                  have p1477_2 := h1477c.2.2.1
                  have p1477_3 := h1477c.2.2.2
                  rcases p1477_3 (m.d 0 5) (by simp) with h1491 | h1491
                  · linarith only [h1, h1491, hlam]
                  · linarith only [h0, h1469, h1491, hlam]
                · have p1477_0 := h1477c.1
                  have p1477_1 := h1477c.2.1
                  have p1477_2 := h1477c.2.2.1
                  have p1477_3 := h1477c.2.2.2
                  linarith only [h1158, h1472, h1474, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1477_1]
                · have p1477_0 := h1477c.1
                  have p1477_1 := h1477c.2.1
                  have p1477_2 := h1477c.2.2.1
                  have p1477_3 := h1477c.2.2.2
                  linarith only [h0, h1469, hlam, p1477_1]
                · have p1477_0 := h1477c.1
                  have p1477_1 := h1477c.2.1
                  have p1477_2 := h1477c.2.2.1
                  have p1477_3 := h1477c.2.2.2
                  linarith only [h1469, hlam, p1477_1]
                · have p1477_0 := h1477c.1
                  have p1477_1 := h1477c.2.1
                  have p1477_2 := h1477c.2.2.1
                  have p1477_3 := h1477c.2.2.2
                  linarith only [h1473, hlam, p1477_0]
                · have p1477_0 := h1477c.1
                  have p1477_1 := h1477c.2.1
                  have p1477_2 := h1477c.2.2.1
                  have p1477_3 := h1477c.2.2.2
                  linarith only [hlam, p1477_0]
                · have p1477_0 := h1477c.1
                  have p1477_1 := h1477c.2.1
                  have p1477_2 := h1477c.2.2.1
                  have p1477_3 := h1477c.2.2.2
                  linarith only [h1475, hlam, p1477_0]
                · have p1477_0 := h1477c.1
                  have p1477_1 := h1477c.2.1
                  have p1477_2 := h1477c.2.2.1
                  have p1477_3 := h1477c.2.2.2
                  linarith only [h0, h1467, hc12, hc45, hlam, hphi, ht23, ht34, p1477_1]
                · have p1477_0 := h1477c.1
                  have p1477_1 := h1477c.2.1
                  have p1477_2 := h1477c.2.2.1
                  have p1477_3 := h1477c.2.2.2
                  linarith only [h1467, hc12, hc45, hlam, hphi, ht23, ht34, p1477_1]
                · have p1477_0 := h1477c.1
                  have p1477_1 := h1477c.2.1
                  have p1477_2 := h1477c.2.2.1
                  have p1477_3 := h1477c.2.2.2
                  linarith only [h1474, hlam, p1477_1]
                · have p1477_0 := h1477c.1
                  have p1477_1 := h1477c.2.1
                  have p1477_2 := h1477c.2.2.1
                  have p1477_3 := h1477c.2.2.2
                  linarith only [h1472, h1474, hc23, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p1477_1]
                · have p1477_0 := h1477c.1
                  have p1477_1 := h1477c.2.1
                  have p1477_2 := h1477c.2.2.1
                  have p1477_3 := h1477c.2.2.2
                  linarith only [hlam, p1477_0]
            · rcases m.htr 3 4 5 (by decide) (by decide) with h1505 | h1505
              · linarith only [h1, h1472, h1474, h1505, hc02, hc23, hlam, hphi]
              · rcases h5bigk with h1507c | h1507c | h1507c | h1507c | h1507c | h1507c | h1507c | h1507c | h1507c | h1507c | h1507c | h1507c | h1507c | h1507c | h1507c | h1507c | h1507c | h1507c | h1507c | h1507c | h1507c | h1507c | h1507c | h1507c | h1507c
                · have p1507_0 := h1507c.1
                  have p1507_1 := h1507c.2.1
                  have p1507_2 := h1507c.2.2.1
                  have p1507_3 := h1507c.2.2.2
                  linarith only [hlam, p1507_0]
                · have p1507_0 := h1507c.1
                  have p1507_1 := h1507c.2.1
                  have p1507_2 := h1507c.2.2.1
                  have p1507_3 := h1507c.2.2.2
                  linarith only [h0, h1467, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1507_1, u1elo0]
                · have p1507_0 := h1507c.1
                  have p1507_1 := h1507c.2.1
                  have p1507_2 := h1507c.2.2.1
                  have p1507_3 := h1507c.2.2.2
                  linarith only [h1, hlam, p1507_0]
                · have p1507_0 := h1507c.1
                  have p1507_1 := h1507c.2.1
                  have p1507_2 := h1507c.2.2.1
                  have p1507_3 := h1507c.2.2.2
                  linarith only [h1, h1474, h1505, hc34, hc45, hlam, hphi, p1507_1]
                · have p1507_0 := h1507c.1
                  have p1507_1 := h1507c.2.1
                  have p1507_2 := h1507c.2.2.1
                  have p1507_3 := h1507c.2.2.2
                  linarith only [h1158, hlam, p1507_0]
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
                  linarith only [h1467, hlam, p1507_0]
                · have p1507_0 := h1507c.1
                  have p1507_1 := h1507c.2.1
                  have p1507_2 := h1507c.2.2.1
                  have p1507_3 := h1507c.2.2.2
                  linarith only [h1505, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1507_1, u1elo4]
                · have p1507_0 := h1507c.1
                  have p1507_1 := h1507c.2.1
                  have p1507_2 := h1507c.2.2.1
                  have p1507_3 := h1507c.2.2.2
                  linarith only [h1470, hlam, p1507_0]
                · have p1507_0 := h1507c.1
                  have p1507_1 := h1507c.2.1
                  have p1507_2 := h1507c.2.2.1
                  have p1507_3 := h1507c.2.2.2
                  linarith only [h1, h1474, hc02, hc45, hlam, hphi, ht23, ht34, p1507_1]
                · have p1507_0 := h1507c.1
                  have p1507_1 := h1507c.2.1
                  have p1507_2 := h1507c.2.2.1
                  have p1507_3 := h1507c.2.2.2
                  linarith only [h1467, h1474, hc12, hc45, hlam, hphi, ht23, ht34, p1507_1]
                · have p1507_0 := h1507c.1
                  have p1507_1 := h1507c.2.1
                  have p1507_2 := h1507c.2.2.1
                  have p1507_3 := h1507c.2.2.2
                  linarith only [hlam, p1507_0]
                · have p1507_0 := h1507c.1
                  have p1507_1 := h1507c.2.1
                  have p1507_2 := h1507c.2.2.1
                  have p1507_3 := h1507c.2.2.2
                  linarith only [h1474, h1505, hc34, hc45, hlam, hphi, p1507_1]
                · have p1507_0 := h1507c.1
                  have p1507_1 := h1507c.2.1
                  have p1507_2 := h1507c.2.2.1
                  have p1507_3 := h1507c.2.2.2
                  linarith only [h1474, hlam, p1507_0]
                · have p1507_0 := h1507c.1
                  have p1507_1 := h1507c.2.1
                  have p1507_2 := h1507c.2.2.1
                  have p1507_3 := h1507c.2.2.2
                  linarith only [h0, h1467, hc12, hc35, hlam, hphi, ht23, p1507_1]
                · have p1507_0 := h1507c.1
                  have p1507_1 := h1507c.2.1
                  have p1507_2 := h1507c.2.2.1
                  have p1507_3 := h1507c.2.2.2
                  linarith only [h1469, hlam, p1507_1]
                · have p1507_0 := h1507c.1
                  have p1507_1 := h1507c.2.1
                  have p1507_2 := h1507c.2.2.1
                  have p1507_3 := h1507c.2.2.2
                  linarith only [h1473, hlam, p1507_0]
                · have p1507_0 := h1507c.1
                  have p1507_1 := h1507c.2.1
                  have p1507_2 := h1507c.2.2.1
                  have p1507_3 := h1507c.2.2.2
                  linarith only [hlam, p1507_0]
                · have p1507_0 := h1507c.1
                  have p1507_1 := h1507c.2.1
                  have p1507_2 := h1507c.2.2.1
                  have p1507_3 := h1507c.2.2.2
                  linarith only [h1505, hlam, p1507_0]
                · have p1507_0 := h1507c.1
                  have p1507_1 := h1507c.2.1
                  have p1507_2 := h1507c.2.2.1
                  have p1507_3 := h1507c.2.2.2
                  linarith only [h0, h1467, hc12, hc45, hlam, hphi, ht23, ht34, p1507_1]
                · have p1507_0 := h1507c.1
                  have p1507_1 := h1507c.2.1
                  have p1507_2 := h1507c.2.2.1
                  have p1507_3 := h1507c.2.2.2
                  linarith only [h1467, hc12, hc45, hlam, hphi, ht23, ht34, p1507_1]
                · have p1507_0 := h1507c.1
                  have p1507_1 := h1507c.2.1
                  have p1507_2 := h1507c.2.2.1
                  have p1507_3 := h1507c.2.2.2
                  linarith only [h1, hc02, hc45, hlam, hphi, ht23, ht34, p1507_1]
                · have p1507_0 := h1507c.1
                  have p1507_1 := h1507c.2.1
                  have p1507_2 := h1507c.2.2.1
                  have p1507_3 := h1507c.2.2.2
                  linarith only [h1505, hc34, hc45, hlam, hphi, p1507_1]
                · have p1507_0 := h1507c.1
                  have p1507_1 := h1507c.2.1
                  have p1507_2 := h1507c.2.2.1
                  have p1507_3 := h1507c.2.2.2
                  linarith only [hlam, p1507_0]
          · linarith only [h0, h1469, h1472, h1473, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
        · rcases m.htr 2 3 5 (by decide) (by decide) with h1534 | h1534
          · rcases m.htr 2 4 5 (by decide) (by decide) with h1535 | h1535
            · rcases m.htr 3 4 5 (by decide) (by decide) with h1536 | h1536
              · linarith only [h0, h1158, h1469, h1536, hlam]
              · linarith only [h1472, h1534, h1535, h1536, hlam]
            · linarith only [h1472, h1534, h1535, hlam]
          · linarith only [h0, h1, h1469, h1534, hlam]
    · rcases m.htr 1 4 5 (by decide) (by decide) with h1541 | h1541
      · linarith only [h0, h1158, h1541, hlam]
      · rcases m.htr 2 3 4 (by decide) (by decide) with h1543 | h1543
        · rcases m.htr 2 3 5 (by decide) (by decide) with h1544 | h1544
          · rcases m.htr 2 4 5 (by decide) (by decide) with h1545 | h1545
            · rcases m.htr 3 4 5 (by decide) (by decide) with h1546 | h1546
              · rcases h5bigk with h1547c | h1547c | h1547c | h1547c | h1547c | h1547c | h1547c | h1547c | h1547c | h1547c | h1547c | h1547c | h1547c | h1547c | h1547c | h1547c | h1547c | h1547c | h1547c | h1547c | h1547c | h1547c | h1547c | h1547c | h1547c
                · have p1547_0 := h1547c.1
                  have p1547_1 := h1547c.2.1
                  have p1547_2 := h1547c.2.2.1
                  have p1547_3 := h1547c.2.2.2
                  linarith only [hlam, p1547_0]
                · have p1547_0 := h1547c.1
                  have p1547_1 := h1547c.2.1
                  have p1547_2 := h1547c.2.2.1
                  have p1547_3 := h1547c.2.2.2
                  linarith only [h1158, h1543, h1546, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1547_1]
                · have p1547_0 := h1547c.1
                  have p1547_1 := h1547c.2.1
                  have p1547_2 := h1547c.2.2.1
                  have p1547_3 := h1547c.2.2.2
                  linarith only [h1, hlam, p1547_0]
                · have p1547_0 := h1547c.1
                  have p1547_1 := h1547c.2.1
                  have p1547_2 := h1547c.2.2.1
                  have p1547_3 := h1547c.2.2.2
                  linarith only [h1158, h1546, hlam, p1547_1]
                · have p1547_0 := h1547c.1
                  have p1547_1 := h1547c.2.1
                  have p1547_2 := h1547c.2.2.1
                  have p1547_3 := h1547c.2.2.2
                  linarith only [h1158, hlam, p1547_0]
                · have p1547_0 := h1547c.1
                  have p1547_1 := h1547c.2.1
                  have p1547_2 := h1547c.2.2.1
                  have p1547_3 := h1547c.2.2.2
                  linarith only [h0, hlam, p1547_0]
                · have p1547_0 := h1547c.1
                  have p1547_1 := h1547c.2.1
                  have p1547_2 := h1547c.2.2.1
                  have p1547_3 := h1547c.2.2.2
                  linarith only [hlam, p1547_0]
                · have p1547_0 := h1547c.1
                  have p1547_1 := h1547c.2.1
                  have p1547_2 := h1547c.2.2.1
                  have p1547_3 := h1547c.2.2.2
                  linarith only [h1467, hlam, p1547_0]
                · have p1547_0 := h1547c.1
                  have p1547_1 := h1547c.2.1
                  have p1547_2 := h1547c.2.2.1
                  have p1547_3 := h1547c.2.2.2
                  linarith only [h1469, hlam, p1547_0]
                · have p1547_0 := h1547c.1
                  have p1547_1 := h1547c.2.1
                  have p1547_2 := h1547c.2.2.1
                  have p1547_3 := h1547c.2.2.2
                  linarith only [h1541, hlam, p1547_0]
                · have p1547_0 := h1547c.1
                  have p1547_1 := h1547c.2.1
                  have p1547_2 := h1547c.2.2.1
                  have p1547_3 := h1547c.2.2.2
                  linarith only [h0, h1467, hc12, hc25, hlam, hphi, p1547_1]
                · have p1547_0 := h1547c.1
                  have p1547_1 := h1547c.2.1
                  have p1547_2 := h1547c.2.2.1
                  have p1547_3 := h1547c.2.2.2
                  linarith only [h1467, hc12, hc25, hlam, hphi, p1547_1]
                · have p1547_0 := h1547c.1
                  have p1547_1 := h1547c.2.1
                  have p1547_2 := h1547c.2.2.1
                  have p1547_3 := h1547c.2.2.2
                  linarith only [hlam, p1547_0]
                · have p1547_0 := h1547c.1
                  have p1547_1 := h1547c.2.1
                  have p1547_2 := h1547c.2.2.1
                  have p1547_3 := h1547c.2.2.2
                  linarith only [h1469, h1544, hc13, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1547_1]
                · have p1547_0 := h1547c.1
                  have p1547_1 := h1547c.2.1
                  have p1547_2 := h1547c.2.2.1
                  have p1547_3 := h1547c.2.2.2
                  linarith only [h1541, h1543, h1545, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1547_1]
                · have p1547_0 := h1547c.1
                  have p1547_1 := h1547c.2.1
                  have p1547_2 := h1547c.2.2.1
                  have p1547_3 := h1547c.2.2.2
                  linarith only [h0, h1467, hc12, hc35, hlam, hphi, ht23, p1547_1]
                · have p1547_0 := h1547c.1
                  have p1547_1 := h1547c.2.1
                  have p1547_2 := h1547c.2.2.1
                  have p1547_3 := h1547c.2.2.2
                  linarith only [h1467, hc12, hc35, hlam, hphi, ht23, p1547_1]
                · have p1547_0 := h1547c.1
                  have p1547_1 := h1547c.2.1
                  have p1547_2 := h1547c.2.2.1
                  have p1547_3 := h1547c.2.2.2
                  linarith only [h1544, hlam, p1547_0]
                · have p1547_0 := h1547c.1
                  have p1547_1 := h1547c.2.1
                  have p1547_2 := h1547c.2.2.1
                  have p1547_3 := h1547c.2.2.2
                  linarith only [hlam, p1547_0]
                · have p1547_0 := h1547c.1
                  have p1547_1 := h1547c.2.1
                  have p1547_2 := h1547c.2.2.1
                  have p1547_3 := h1547c.2.2.2
                  linarith only [h1541, h1543, h1546, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1547_1]
                · have p1547_0 := h1547c.1
                  have p1547_1 := h1547c.2.1
                  have p1547_2 := h1547c.2.2.1
                  have p1547_3 := h1547c.2.2.2
                  linarith only [h0, h1467, hc12, hc45, hlam, hphi, ht23, ht34, p1547_1]
                · have p1547_0 := h1547c.1
                  have p1547_1 := h1547c.2.1
                  have p1547_2 := h1547c.2.2.1
                  have p1547_3 := h1547c.2.2.2
                  linarith only [h1467, hc12, hc45, hlam, hphi, ht23, ht34, p1547_1]
                · have p1547_0 := h1547c.1
                  have p1547_1 := h1547c.2.1
                  have p1547_2 := h1547c.2.2.1
                  have p1547_3 := h1547c.2.2.2
                  linarith only [h1545, hlam, p1547_1]
                · have p1547_0 := h1547c.1
                  have p1547_1 := h1547c.2.1
                  have p1547_2 := h1547c.2.2.1
                  have p1547_3 := h1547c.2.2.2
                  linarith only [h1546, hlam, p1547_1]
                · have p1547_0 := h1547c.1
                  have p1547_1 := h1547c.2.1
                  have p1547_2 := h1547c.2.2.1
                  have p1547_3 := h1547c.2.2.2
                  linarith only [hlam, p1547_0]
              · rcases h5bigk with h1573c | h1573c | h1573c | h1573c | h1573c | h1573c | h1573c | h1573c | h1573c | h1573c | h1573c | h1573c | h1573c | h1573c | h1573c | h1573c | h1573c | h1573c | h1573c | h1573c | h1573c | h1573c | h1573c | h1573c | h1573c
                · have p1573_0 := h1573c.1
                  have p1573_1 := h1573c.2.1
                  have p1573_2 := h1573c.2.2.1
                  have p1573_3 := h1573c.2.2.2
                  linarith only [hlam, p1573_0]
                · have p1573_0 := h1573c.1
                  have p1573_1 := h1573c.2.1
                  have p1573_2 := h1573c.2.2.1
                  have p1573_3 := h1573c.2.2.2
                  linarith only [h0, h1467, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1573_1, u1elo0]
                · have p1573_0 := h1573c.1
                  have p1573_1 := h1573c.2.1
                  have p1573_2 := h1573c.2.2.1
                  have p1573_3 := h1573c.2.2.2
                  linarith only [h1, hlam, p1573_0]
                · have p1573_0 := h1573c.1
                  have p1573_1 := h1573c.2.1
                  have p1573_2 := h1573c.2.2.1
                  have p1573_3 := h1573c.2.2.2
                  linarith only [h1158, h1543, h1545, hc23, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p1573_1]
                · have p1573_0 := h1573c.1
                  have p1573_1 := h1573c.2.1
                  have p1573_2 := h1573c.2.2.1
                  have p1573_3 := h1573c.2.2.2
                  linarith only [h1158, hlam, p1573_0]
                · have p1573_0 := h1573c.1
                  have p1573_1 := h1573c.2.1
                  have p1573_2 := h1573c.2.2.1
                  have p1573_3 := h1573c.2.2.2
                  linarith only [h0, hlam, p1573_0]
                · have p1573_0 := h1573c.1
                  have p1573_1 := h1573c.2.1
                  have p1573_2 := h1573c.2.2.1
                  have p1573_3 := h1573c.2.2.2
                  linarith only [hlam, p1573_0]
                · have p1573_0 := h1573c.1
                  have p1573_1 := h1573c.2.1
                  have p1573_2 := h1573c.2.2.1
                  have p1573_3 := h1573c.2.2.2
                  linarith only [h1467, hlam, p1573_0]
                · have p1573_0 := h1573c.1
                  have p1573_1 := h1573c.2.1
                  have p1573_2 := h1573c.2.2.1
                  have p1573_3 := h1573c.2.2.2
                  linarith only [h1469, hlam, p1573_0]
                · have p1573_0 := h1573c.1
                  have p1573_1 := h1573c.2.1
                  have p1573_2 := h1573c.2.2.1
                  have p1573_3 := h1573c.2.2.2
                  linarith only [h1541, hlam, p1573_0]
                · have p1573_0 := h1573c.1
                  have p1573_1 := h1573c.2.1
                  have p1573_2 := h1573c.2.2.1
                  have p1573_3 := h1573c.2.2.2
                  linarith only [h0, h1467, h1543, h1545, hc12, hc23, hlam, hphi, p1573_1]
                · have p1573_0 := h1573c.1
                  have p1573_1 := h1573c.2.1
                  have p1573_2 := h1573c.2.2.1
                  have p1573_3 := h1573c.2.2.2
                  linarith only [h1467, h1543, h1545, hc12, hc23, hlam, hphi, p1573_1]
                · have p1573_0 := h1573c.1
                  have p1573_1 := h1573c.2.1
                  have p1573_2 := h1573c.2.2.1
                  have p1573_3 := h1573c.2.2.2
                  linarith only [hlam, p1573_0]
                · have p1573_0 := h1573c.1
                  have p1573_1 := h1573c.2.1
                  have p1573_2 := h1573c.2.2.1
                  have p1573_3 := h1573c.2.2.2
                  linarith only [h1469, h1543, h1545, hc13, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1573_1]
                · have p1573_0 := h1573c.1
                  have p1573_1 := h1573c.2.1
                  have p1573_2 := h1573c.2.2.1
                  have p1573_3 := h1573c.2.2.2
                  linarith only [h1543, h1545, h1546, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1573_1]
                · have p1573_0 := h1573c.1
                  have p1573_1 := h1573c.2.1
                  have p1573_2 := h1573c.2.2.1
                  have p1573_3 := h1573c.2.2.2
                  linarith only [h0, h1467, hc12, hc35, hlam, hphi, ht23, p1573_1]
                · have p1573_0 := h1573c.1
                  have p1573_1 := h1573c.2.1
                  have p1573_2 := h1573c.2.2.1
                  have p1573_3 := h1573c.2.2.2
                  linarith only [h1467, h1546, hc12, hc45, hlam, hphi, ht23, ht34, p1573_1]
                · have p1573_0 := h1573c.1
                  have p1573_1 := h1573c.2.1
                  have p1573_2 := h1573c.2.2.1
                  have p1573_3 := h1573c.2.2.2
                  linarith only [h1544, hlam, p1573_0]
                · have p1573_0 := h1573c.1
                  have p1573_1 := h1573c.2.1
                  have p1573_2 := h1573c.2.2.1
                  have p1573_3 := h1573c.2.2.2
                  linarith only [hlam, p1573_0]
                · have p1573_0 := h1573c.1
                  have p1573_1 := h1573c.2.1
                  have p1573_2 := h1573c.2.2.1
                  have p1573_3 := h1573c.2.2.2
                  linarith only [h1546, hlam, p1573_0]
                · have p1573_0 := h1573c.1
                  have p1573_1 := h1573c.2.1
                  have p1573_2 := h1573c.2.2.1
                  have p1573_3 := h1573c.2.2.2
                  linarith only [h0, h1467, hc12, hc45, hlam, hphi, ht23, ht34, p1573_1]
                · have p1573_0 := h1573c.1
                  have p1573_1 := h1573c.2.1
                  have p1573_2 := h1573c.2.2.1
                  have p1573_3 := h1573c.2.2.2
                  linarith only [h1467, hc12, hc45, hlam, hphi, ht23, ht34, p1573_1]
                · have p1573_0 := h1573c.1
                  have p1573_1 := h1573c.2.1
                  have p1573_2 := h1573c.2.2.1
                  have p1573_3 := h1573c.2.2.2
                  linarith only [h1545, hlam, p1573_1]
                · have p1573_0 := h1573c.1
                  have p1573_1 := h1573c.2.1
                  have p1573_2 := h1573c.2.2.1
                  have p1573_3 := h1573c.2.2.2
                  linarith only [h1469, hc13, hc45, hlam, hphi, ht34, p1573_1]
                · have p1573_0 := h1573c.1
                  have p1573_1 := h1573c.2.1
                  have p1573_2 := h1573c.2.2.1
                  have p1573_3 := h1573c.2.2.2
                  linarith only [hlam, p1573_0]
            · rcases m.htr 3 4 5 (by decide) (by decide) with h1599 | h1599
              · linarith only [h1, h1543, h1545, h1599, hc02, hc23, hlam, hphi]
              · rcases h5bigk with h1601c | h1601c | h1601c | h1601c | h1601c | h1601c | h1601c | h1601c | h1601c | h1601c | h1601c | h1601c | h1601c | h1601c | h1601c | h1601c | h1601c | h1601c | h1601c | h1601c | h1601c | h1601c | h1601c | h1601c | h1601c
                · have p1601_0 := h1601c.1
                  have p1601_1 := h1601c.2.1
                  have p1601_2 := h1601c.2.2.1
                  have p1601_3 := h1601c.2.2.2
                  linarith only [hlam, p1601_0]
                · have p1601_0 := h1601c.1
                  have p1601_1 := h1601c.2.1
                  have p1601_2 := h1601c.2.2.1
                  have p1601_3 := h1601c.2.2.2
                  linarith only [h0, h1467, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1601_1, u1elo0]
                · have p1601_0 := h1601c.1
                  have p1601_1 := h1601c.2.1
                  have p1601_2 := h1601c.2.2.1
                  have p1601_3 := h1601c.2.2.2
                  linarith only [h1, hlam, p1601_0]
                · have p1601_0 := h1601c.1
                  have p1601_1 := h1601c.2.1
                  have p1601_2 := h1601c.2.2.1
                  have p1601_3 := h1601c.2.2.2
                  linarith only [h1469, hc05, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p1601_1]
                · have p1601_0 := h1601c.1
                  have p1601_1 := h1601c.2.1
                  have p1601_2 := h1601c.2.2.1
                  have p1601_3 := h1601c.2.2.2
                  linarith only [h1158, hlam, p1601_0]
                · have p1601_0 := h1601c.1
                  have p1601_1 := h1601c.2.1
                  have p1601_2 := h1601c.2.2.1
                  have p1601_3 := h1601c.2.2.2
                  linarith only [h0, hlam, p1601_0]
                · have p1601_0 := h1601c.1
                  have p1601_1 := h1601c.2.1
                  have p1601_2 := h1601c.2.2.1
                  have p1601_3 := h1601c.2.2.2
                  linarith only [hlam, p1601_0]
                · have p1601_0 := h1601c.1
                  have p1601_1 := h1601c.2.1
                  have p1601_2 := h1601c.2.2.1
                  have p1601_3 := h1601c.2.2.2
                  linarith only [h1467, hlam, p1601_0]
                · have p1601_0 := h1601c.1
                  have p1601_1 := h1601c.2.1
                  have p1601_2 := h1601c.2.2.1
                  have p1601_3 := h1601c.2.2.2
                  linarith only [h1469, hlam, p1601_0]
                · have p1601_0 := h1601c.1
                  have p1601_1 := h1601c.2.1
                  have p1601_2 := h1601c.2.2.1
                  have p1601_3 := h1601c.2.2.2
                  linarith only [h1541, hlam, p1601_0]
                · have p1601_0 := h1601c.1
                  have p1601_1 := h1601c.2.1
                  have p1601_2 := h1601c.2.2.1
                  have p1601_3 := h1601c.2.2.2
                  linarith only [h0, h1467, h1545, hc12, hc45, hlam, hphi, ht23, ht34, p1601_1]
                · have p1601_0 := h1601c.1
                  have p1601_1 := h1601c.2.1
                  have p1601_2 := h1601c.2.2.1
                  have p1601_3 := h1601c.2.2.2
                  linarith only [h1467, h1545, hc12, hc45, hlam, hphi, ht23, ht34, p1601_1]
                · have p1601_0 := h1601c.1
                  have p1601_1 := h1601c.2.1
                  have p1601_2 := h1601c.2.2.1
                  have p1601_3 := h1601c.2.2.2
                  linarith only [hlam, p1601_0]
                · have p1601_0 := h1601c.1
                  have p1601_1 := h1601c.2.1
                  have p1601_2 := h1601c.2.2.1
                  have p1601_3 := h1601c.2.2.2
                  linarith only [h1469, h1545, hc13, hc45, hlam, hphi, ht34, p1601_1]
                · have p1601_0 := h1601c.1
                  have p1601_1 := h1601c.2.1
                  have p1601_2 := h1601c.2.2.1
                  have p1601_3 := h1601c.2.2.2
                  linarith only [h1545, hlam, p1601_0]
                · have p1601_0 := h1601c.1
                  have p1601_1 := h1601c.2.1
                  have p1601_2 := h1601c.2.2.1
                  have p1601_3 := h1601c.2.2.2
                  linarith only [h0, h1467, hc12, hc35, hlam, hphi, ht23, p1601_1]
                · have p1601_0 := h1601c.1
                  have p1601_1 := h1601c.2.1
                  have p1601_2 := h1601c.2.2.1
                  have p1601_3 := h1601c.2.2.2
                  linarith only [h1467, hc12, hc35, hlam, hphi, ht23, p1601_1]
                · have p1601_0 := h1601c.1
                  have p1601_1 := h1601c.2.1
                  have p1601_2 := h1601c.2.2.1
                  have p1601_3 := h1601c.2.2.2
                  linarith only [h1544, hlam, p1601_0]
                · have p1601_0 := h1601c.1
                  have p1601_1 := h1601c.2.1
                  have p1601_2 := h1601c.2.2.1
                  have p1601_3 := h1601c.2.2.2
                  linarith only [hlam, p1601_0]
                · have p1601_0 := h1601c.1
                  have p1601_1 := h1601c.2.1
                  have p1601_2 := h1601c.2.2.1
                  have p1601_3 := h1601c.2.2.2
                  linarith only [h1599, hlam, p1601_0]
                · have p1601_0 := h1601c.1
                  have p1601_1 := h1601c.2.1
                  have p1601_2 := h1601c.2.2.1
                  have p1601_3 := h1601c.2.2.2
                  linarith only [h0, h1467, hc12, hc45, hlam, hphi, ht23, ht34, p1601_1]
                · have p1601_0 := h1601c.1
                  have p1601_1 := h1601c.2.1
                  have p1601_2 := h1601c.2.2.1
                  have p1601_3 := h1601c.2.2.2
                  linarith only [h1467, hc12, hc45, hlam, hphi, ht23, ht34, p1601_1]
                · have p1601_0 := h1601c.1
                  have p1601_1 := h1601c.2.1
                  have p1601_2 := h1601c.2.2.1
                  have p1601_3 := h1601c.2.2.2
                  linarith only [h1, hc02, hc45, hlam, hphi, ht23, ht34, p1601_1]
                · have p1601_0 := h1601c.1
                  have p1601_1 := h1601c.2.1
                  have p1601_2 := h1601c.2.2.1
                  have p1601_3 := h1601c.2.2.2
                  linarith only [h1469, hc13, hc45, hlam, hphi, ht34, p1601_1]
                · have p1601_0 := h1601c.1
                  have p1601_1 := h1601c.2.1
                  have p1601_2 := h1601c.2.2.1
                  have p1601_3 := h1601c.2.2.2
                  linarith only [hlam, p1601_0]
          · rcases m.htr 2 4 5 (by decide) (by decide) with h1627 | h1627
            · linarith only [h1543, h1544, h1627, hlam]
            · rcases m.htr 3 4 5 (by decide) (by decide) with h1629 | h1629
              · linarith only [h1543, h1544, h1627, h1629, hlam]
              · rcases h5bigk with h1631c | h1631c | h1631c | h1631c | h1631c | h1631c | h1631c | h1631c | h1631c | h1631c | h1631c | h1631c | h1631c | h1631c | h1631c | h1631c | h1631c | h1631c | h1631c | h1631c | h1631c | h1631c | h1631c | h1631c | h1631c
                · have p1631_0 := h1631c.1
                  have p1631_1 := h1631c.2.1
                  have p1631_2 := h1631c.2.2.1
                  have p1631_3 := h1631c.2.2.2
                  linarith only [hlam, p1631_0]
                · have p1631_0 := h1631c.1
                  have p1631_1 := h1631c.2.1
                  have p1631_2 := h1631c.2.2.1
                  have p1631_3 := h1631c.2.2.2
                  linarith only [h0, h1467, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1631_1, u1elo0]
                · have p1631_0 := h1631c.1
                  have p1631_1 := h1631c.2.1
                  have p1631_2 := h1631c.2.2.1
                  have p1631_3 := h1631c.2.2.2
                  linarith only [h1, hlam, p1631_0]
                · have p1631_0 := h1631c.1
                  have p1631_1 := h1631c.2.1
                  have p1631_2 := h1631c.2.2.1
                  have p1631_3 := h1631c.2.2.2
                  linarith only [h1, h1544, hlam, p1631_1]
                · have p1631_0 := h1631c.1
                  have p1631_1 := h1631c.2.1
                  have p1631_2 := h1631c.2.2.1
                  have p1631_3 := h1631c.2.2.2
                  linarith only [h1158, hlam, p1631_0]
                · have p1631_0 := h1631c.1
                  have p1631_1 := h1631c.2.1
                  have p1631_2 := h1631c.2.2.1
                  have p1631_3 := h1631c.2.2.2
                  linarith only [h0, hlam, p1631_0]
                · have p1631_0 := h1631c.1
                  have p1631_1 := h1631c.2.1
                  have p1631_2 := h1631c.2.2.1
                  have p1631_3 := h1631c.2.2.2
                  linarith only [hlam, p1631_0]
                · have p1631_0 := h1631c.1
                  have p1631_1 := h1631c.2.1
                  have p1631_2 := h1631c.2.2.1
                  have p1631_3 := h1631c.2.2.2
                  linarith only [h1467, hlam, p1631_0]
                · have p1631_0 := h1631c.1
                  have p1631_1 := h1631c.2.1
                  have p1631_2 := h1631c.2.2.1
                  have p1631_3 := h1631c.2.2.2
                  linarith only [h1469, hlam, p1631_0]
                · have p1631_0 := h1631c.1
                  have p1631_1 := h1631c.2.1
                  have p1631_2 := h1631c.2.2.1
                  have p1631_3 := h1631c.2.2.2
                  linarith only [h1541, hlam, p1631_0]
                · have p1631_0 := h1631c.1
                  have p1631_1 := h1631c.2.1
                  have p1631_2 := h1631c.2.2.1
                  have p1631_3 := h1631c.2.2.2
                  linarith only [h0, h1467, h1544, h1629, hc12, hc45, hlam, hphi, ht23, ht34, p1631_1]
                · have p1631_0 := h1631c.1
                  have p1631_1 := h1631c.2.1
                  have p1631_2 := h1631c.2.2.1
                  have p1631_3 := h1631c.2.2.2
                  linarith only [h1467, h1544, h1629, hc12, hc45, hlam, hphi, ht23, ht34, p1631_1]
                · have p1631_0 := h1631c.1
                  have p1631_1 := h1631c.2.1
                  have p1631_2 := h1631c.2.2.1
                  have p1631_3 := h1631c.2.2.2
                  linarith only [hlam, p1631_0]
                · have p1631_0 := h1631c.1
                  have p1631_1 := h1631c.2.1
                  have p1631_2 := h1631c.2.2.1
                  have p1631_3 := h1631c.2.2.2
                  linarith only [h1544, hlam, p1631_1]
                · have p1631_0 := h1631c.1
                  have p1631_1 := h1631c.2.1
                  have p1631_2 := h1631c.2.2.1
                  have p1631_3 := h1631c.2.2.2
                  linarith only [h1627, hlam, p1631_0]
                · have p1631_0 := h1631c.1
                  have p1631_1 := h1631c.2.1
                  have p1631_2 := h1631c.2.2.1
                  have p1631_3 := h1631c.2.2.2
                  linarith only [h0, h1467, h1629, hc12, hc45, hlam, hphi, ht23, ht34, p1631_1]
                · have p1631_0 := h1631c.1
                  have p1631_1 := h1631c.2.1
                  have p1631_2 := h1631c.2.2.1
                  have p1631_3 := h1631c.2.2.2
                  linarith only [h1467, h1629, hc12, hc45, hlam, hphi, ht23, ht34, p1631_1]
                · have p1631_0 := h1631c.1
                  have p1631_1 := h1631c.2.1
                  have p1631_2 := h1631c.2.2.1
                  have p1631_3 := h1631c.2.2.2
                  linarith only [h1, h1629, hc02, hc45, hlam, hphi, ht23, ht34, p1631_1]
                · have p1631_0 := h1631c.1
                  have p1631_1 := h1631c.2.1
                  have p1631_2 := h1631c.2.2.1
                  have p1631_3 := h1631c.2.2.2
                  linarith only [hlam, p1631_0]
                · have p1631_0 := h1631c.1
                  have p1631_1 := h1631c.2.1
                  have p1631_2 := h1631c.2.2.1
                  have p1631_3 := h1631c.2.2.2
                  linarith only [h1629, hlam, p1631_0]
                · have p1631_0 := h1631c.1
                  have p1631_1 := h1631c.2.1
                  have p1631_2 := h1631c.2.2.1
                  have p1631_3 := h1631c.2.2.2
                  linarith only [h0, h1467, hc12, hc45, hlam, hphi, ht23, ht34, p1631_1]
                · have p1631_0 := h1631c.1
                  have p1631_1 := h1631c.2.1
                  have p1631_2 := h1631c.2.2.1
                  have p1631_3 := h1631c.2.2.2
                  linarith only [h1467, hc12, hc45, hlam, hphi, ht23, ht34, p1631_1]
                · have p1631_0 := h1631c.1
                  have p1631_1 := h1631c.2.1
                  have p1631_2 := h1631c.2.2.1
                  have p1631_3 := h1631c.2.2.2
                  linarith only [h1544, hc23, hc45, hlam, hphi, ht34, p1631_1]
                · have p1631_0 := h1631c.1
                  have p1631_1 := h1631c.2.1
                  have p1631_2 := h1631c.2.2.1
                  have p1631_3 := h1631c.2.2.2
                  linarith only [h1469, hc13, hc45, hlam, hphi, ht34, p1631_1]
                · have p1631_0 := h1631c.1
                  have p1631_1 := h1631c.2.1
                  have p1631_2 := h1631c.2.2.1
                  have p1631_3 := h1631c.2.2.2
                  linarith only [hlam, p1631_0]
        · rcases m.htr 2 3 5 (by decide) (by decide) with h1657 | h1657
          · linarith only [h1469, h1543, h1657, hc13, hc34, hlam, hphi]
          · rcases m.htr 2 4 5 (by decide) (by decide) with h1659 | h1659
            · rcases m.htr 3 4 5 (by decide) (by decide) with h1660 | h1660
              · rcases h5bigk with h1661c | h1661c | h1661c | h1661c | h1661c | h1661c | h1661c | h1661c | h1661c | h1661c | h1661c | h1661c | h1661c | h1661c | h1661c | h1661c | h1661c | h1661c | h1661c | h1661c | h1661c | h1661c | h1661c | h1661c | h1661c
                · have p1661_0 := h1661c.1
                  have p1661_1 := h1661c.2.1
                  have p1661_2 := h1661c.2.2.1
                  have p1661_3 := h1661c.2.2.2
                  linarith only [hlam, p1661_0]
                · have p1661_0 := h1661c.1
                  have p1661_1 := h1661c.2.1
                  have p1661_2 := h1661c.2.2.1
                  have p1661_3 := h1661c.2.2.2
                  linarith only [h0, h1467, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1661_1, u1elo0]
                · have p1661_0 := h1661c.1
                  have p1661_1 := h1661c.2.1
                  have p1661_2 := h1661c.2.2.1
                  have p1661_3 := h1661c.2.2.2
                  linarith only [h1, hlam, p1661_0]
                · have p1661_0 := h1661c.1
                  have p1661_1 := h1661c.2.1
                  have p1661_2 := h1661c.2.2.1
                  have p1661_3 := h1661c.2.2.2
                  linarith only [h1158, h1543, h1657, h1659, hc23, hc34, hlam, hphi, p1661_1]
                · have p1661_0 := h1661c.1
                  have p1661_1 := h1661c.2.1
                  have p1661_2 := h1661c.2.2.1
                  have p1661_3 := h1661c.2.2.2
                  linarith only [h1158, hlam, p1661_0]
                · have p1661_0 := h1661c.1
                  have p1661_1 := h1661c.2.1
                  have p1661_2 := h1661c.2.2.1
                  have p1661_3 := h1661c.2.2.2
                  linarith only [h0, hlam, p1661_0]
                · have p1661_0 := h1661c.1
                  have p1661_1 := h1661c.2.1
                  have p1661_2 := h1661c.2.2.1
                  have p1661_3 := h1661c.2.2.2
                  linarith only [hlam, p1661_0]
                · have p1661_0 := h1661c.1
                  have p1661_1 := h1661c.2.1
                  have p1661_2 := h1661c.2.2.1
                  have p1661_3 := h1661c.2.2.2
                  linarith only [h1467, hlam, p1661_0]
                · have p1661_0 := h1661c.1
                  have p1661_1 := h1661c.2.1
                  have p1661_2 := h1661c.2.2.1
                  have p1661_3 := h1661c.2.2.2
                  linarith only [h1469, hlam, p1661_0]
                · have p1661_0 := h1661c.1
                  have p1661_1 := h1661c.2.1
                  have p1661_2 := h1661c.2.2.1
                  have p1661_3 := h1661c.2.2.2
                  linarith only [h1541, hlam, p1661_0]
                · have p1661_0 := h1661c.1
                  have p1661_1 := h1661c.2.1
                  have p1661_2 := h1661c.2.2.1
                  have p1661_3 := h1661c.2.2.2
                  linarith only [h0, h1467, hc12, hc25, hlam, hphi, p1661_1]
                · have p1661_0 := h1661c.1
                  have p1661_1 := h1661c.2.1
                  have p1661_2 := h1661c.2.2.1
                  have p1661_3 := h1661c.2.2.2
                  linarith only [h1467, hc12, hc25, hlam, hphi, p1661_1]
                · have p1661_0 := h1661c.1
                  have p1661_1 := h1661c.2.1
                  have p1661_2 := h1661c.2.2.1
                  have p1661_3 := h1661c.2.2.2
                  linarith only [hlam, p1661_0]
                · have p1661_0 := h1661c.1
                  have p1661_1 := h1661c.2.1
                  have p1661_2 := h1661c.2.2.1
                  have p1661_3 := h1661c.2.2.2
                  linarith only [h1657, hlam, p1661_1]
                · have p1661_0 := h1661c.1
                  have p1661_1 := h1661c.2.1
                  have p1661_2 := h1661c.2.2.1
                  have p1661_3 := h1661c.2.2.2
                  linarith only [h1158, h1543, h1659, hc04, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1661_1]
                · have p1661_0 := h1661c.1
                  have p1661_1 := h1661c.2.1
                  have p1661_2 := h1661c.2.2.1
                  have p1661_3 := h1661c.2.2.2
                  linarith only [h0, h1467, h1660, hc12, hc34, hlam, hphi, ht23, p1661_1]
                · have p1661_0 := h1661c.1
                  have p1661_1 := h1661c.2.1
                  have p1661_2 := h1661c.2.2.1
                  have p1661_3 := h1661c.2.2.2
                  linarith only [h1467, h1660, hc12, hc34, hlam, hphi, ht23, p1661_1]
                · have p1661_0 := h1661c.1
                  have p1661_1 := h1661c.2.1
                  have p1661_2 := h1661c.2.2.1
                  have p1661_3 := h1661c.2.2.2
                  linarith only [h1, h1660, hc02, hc34, hlam, hphi, ht23, p1661_1]
                · have p1661_0 := h1661c.1
                  have p1661_1 := h1661c.2.1
                  have p1661_2 := h1661c.2.2.1
                  have p1661_3 := h1661c.2.2.2
                  linarith only [hlam, p1661_0]
                · have p1661_0 := h1661c.1
                  have p1661_1 := h1661c.2.1
                  have p1661_2 := h1661c.2.2.1
                  have p1661_3 := h1661c.2.2.2
                  linarith only [h1158, h1660, hc04, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1661_1]
                · have p1661_0 := h1661c.1
                  have p1661_1 := h1661c.2.1
                  have p1661_2 := h1661c.2.2.1
                  have p1661_3 := h1661c.2.2.2
                  linarith only [h0, h1467, hc12, hc45, hlam, hphi, ht23, ht34, p1661_1]
                · have p1661_0 := h1661c.1
                  have p1661_1 := h1661c.2.1
                  have p1661_2 := h1661c.2.2.1
                  have p1661_3 := h1661c.2.2.2
                  linarith only [h1467, hc12, hc45, hlam, hphi, ht23, ht34, p1661_1]
                · have p1661_0 := h1661c.1
                  have p1661_1 := h1661c.2.1
                  have p1661_2 := h1661c.2.2.1
                  have p1661_3 := h1661c.2.2.2
                  linarith only [h1659, hlam, p1661_1]
                · have p1661_0 := h1661c.1
                  have p1661_1 := h1661c.2.1
                  have p1661_2 := h1661c.2.2.1
                  have p1661_3 := h1661c.2.2.2
                  linarith only [h1660, hlam, p1661_1]
                · have p1661_0 := h1661c.1
                  have p1661_1 := h1661c.2.1
                  have p1661_2 := h1661c.2.2.1
                  have p1661_3 := h1661c.2.2.2
                  linarith only [hlam, p1661_0]
              · linarith only [h1543, h1659, h1660, hlam]
            · rcases m.htr 3 4 5 (by decide) (by decide) with h1688 | h1688
              · rcases h5bigk with h1689c | h1689c | h1689c | h1689c | h1689c | h1689c | h1689c | h1689c | h1689c | h1689c | h1689c | h1689c | h1689c | h1689c | h1689c | h1689c | h1689c | h1689c | h1689c | h1689c | h1689c | h1689c | h1689c | h1689c | h1689c
                · have p1689_0 := h1689c.1
                  have p1689_1 := h1689c.2.1
                  have p1689_2 := h1689c.2.2.1
                  have p1689_3 := h1689c.2.2.2
                  linarith only [hlam, p1689_0]
                · have p1689_0 := h1689c.1
                  have p1689_1 := h1689c.2.1
                  have p1689_2 := h1689c.2.2.1
                  have p1689_3 := h1689c.2.2.2
                  linarith only [h0, h1467, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1689_1, u1elo0]
                · have p1689_0 := h1689c.1
                  have p1689_1 := h1689c.2.1
                  have p1689_2 := h1689c.2.2.1
                  have p1689_3 := h1689c.2.2.2
                  linarith only [h1, hlam, p1689_0]
                · have p1689_0 := h1689c.1
                  have p1689_1 := h1689c.2.1
                  have p1689_2 := h1689c.2.2.1
                  have p1689_3 := h1689c.2.2.2
                  linarith only [h0, hc35, hlam, hphi, ht01, ht0b, ht5b, p1689_1, u1elo0]
                · have p1689_0 := h1689c.1
                  have p1689_1 := h1689c.2.1
                  have p1689_2 := h1689c.2.2.1
                  have p1689_3 := h1689c.2.2.2
                  linarith only [h1158, hlam, p1689_0]
                · have p1689_0 := h1689c.1
                  have p1689_1 := h1689c.2.1
                  have p1689_2 := h1689c.2.2.1
                  have p1689_3 := h1689c.2.2.2
                  linarith only [h0, hlam, p1689_0]
                · have p1689_0 := h1689c.1
                  have p1689_1 := h1689c.2.1
                  have p1689_2 := h1689c.2.2.1
                  have p1689_3 := h1689c.2.2.2
                  linarith only [hlam, p1689_0]
                · have p1689_0 := h1689c.1
                  have p1689_1 := h1689c.2.1
                  have p1689_2 := h1689c.2.2.1
                  have p1689_3 := h1689c.2.2.2
                  linarith only [h1467, hlam, p1689_0]
                · have p1689_0 := h1689c.1
                  have p1689_1 := h1689c.2.1
                  have p1689_2 := h1689c.2.2.1
                  have p1689_3 := h1689c.2.2.2
                  linarith only [h1469, hlam, p1689_0]
                · have p1689_0 := h1689c.1
                  have p1689_1 := h1689c.2.1
                  have p1689_2 := h1689c.2.2.1
                  have p1689_3 := h1689c.2.2.2
                  linarith only [h1541, hlam, p1689_0]
                · have p1689_0 := h1689c.1
                  have p1689_1 := h1689c.2.1
                  have p1689_2 := h1689c.2.2.1
                  have p1689_3 := h1689c.2.2.2
                  linarith only [h0, h1467, hc12, hc25, hlam, hphi, p1689_1]
                · have p1689_0 := h1689c.1
                  have p1689_1 := h1689c.2.1
                  have p1689_2 := h1689c.2.2.1
                  have p1689_3 := h1689c.2.2.2
                  linarith only [h1467, h1659, hc12, hc45, hlam, hphi, ht23, ht34, p1689_1]
                · have p1689_0 := h1689c.1
                  have p1689_1 := h1689c.2.1
                  have p1689_2 := h1689c.2.2.1
                  have p1689_3 := h1689c.2.2.2
                  linarith only [hlam, p1689_0]
                · have p1689_0 := h1689c.1
                  have p1689_1 := h1689c.2.1
                  have p1689_2 := h1689c.2.2.1
                  have p1689_3 := h1689c.2.2.2
                  linarith only [h1657, hlam, p1689_1]
                · have p1689_0 := h1689c.1
                  have p1689_1 := h1689c.2.1
                  have p1689_2 := h1689c.2.2.1
                  have p1689_3 := h1689c.2.2.2
                  linarith only [h1659, hlam, p1689_0]
                · have p1689_0 := h1689c.1
                  have p1689_1 := h1689c.2.1
                  have p1689_2 := h1689c.2.2.1
                  have p1689_3 := h1689c.2.2.2
                  linarith only [h0, h1467, hc12, hc35, hlam, hphi, ht23, p1689_1]
                · have p1689_0 := h1689c.1
                  have p1689_1 := h1689c.2.1
                  have p1689_2 := h1689c.2.2.1
                  have p1689_3 := h1689c.2.2.2
                  linarith only [h1467, hc12, hc35, hlam, hphi, ht23, p1689_1]
                · have p1689_0 := h1689c.1
                  have p1689_1 := h1689c.2.1
                  have p1689_2 := h1689c.2.2.1
                  have p1689_3 := h1689c.2.2.2
                  linarith only [h1, hc02, hc35, hlam, hphi, ht23, p1689_1]
                · have p1689_0 := h1689c.1
                  have p1689_1 := h1689c.2.1
                  have p1689_2 := h1689c.2.2.1
                  have p1689_3 := h1689c.2.2.2
                  linarith only [hlam, p1689_0]
                · have p1689_0 := h1689c.1
                  have p1689_1 := h1689c.2.1
                  have p1689_2 := h1689c.2.2.1
                  have p1689_3 := h1689c.2.2.2
                  linarith only [h1659, h1688, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1689_1]
                · have p1689_0 := h1689c.1
                  have p1689_1 := h1689c.2.1
                  have p1689_2 := h1689c.2.2.1
                  have p1689_3 := h1689c.2.2.2
                  linarith only [h0, h1467, hc12, hc45, hlam, hphi, ht23, ht34, p1689_1]
                · have p1689_0 := h1689c.1
                  have p1689_1 := h1689c.2.1
                  have p1689_2 := h1689c.2.2.1
                  have p1689_3 := h1689c.2.2.2
                  linarith only [h1467, hc12, hc45, hlam, hphi, ht23, ht34, p1689_1]
                · have p1689_0 := h1689c.1
                  have p1689_1 := h1689c.2.1
                  have p1689_2 := h1689c.2.2.1
                  have p1689_3 := h1689c.2.2.2
                  linarith only [h1, hc02, hc45, hlam, hphi, ht23, ht34, p1689_1]
                · have p1689_0 := h1689c.1
                  have p1689_1 := h1689c.2.1
                  have p1689_2 := h1689c.2.2.1
                  have p1689_3 := h1689c.2.2.2
                  linarith only [h1688, hlam, p1689_1]
                · have p1689_0 := h1689c.1
                  have p1689_1 := h1689c.2.1
                  have p1689_2 := h1689c.2.2.1
                  have p1689_3 := h1689c.2.2.2
                  linarith only [hlam, p1689_0]
              · rcases h5bigk with h1715c | h1715c | h1715c | h1715c | h1715c | h1715c | h1715c | h1715c | h1715c | h1715c | h1715c | h1715c | h1715c | h1715c | h1715c | h1715c | h1715c | h1715c | h1715c | h1715c | h1715c | h1715c | h1715c | h1715c | h1715c
                · have p1715_0 := h1715c.1
                  have p1715_1 := h1715c.2.1
                  have p1715_2 := h1715c.2.2.1
                  have p1715_3 := h1715c.2.2.2
                  linarith only [hlam, p1715_0]
                · have p1715_0 := h1715c.1
                  have p1715_1 := h1715c.2.1
                  have p1715_2 := h1715c.2.2.1
                  have p1715_3 := h1715c.2.2.2
                  linarith only [h0, h1467, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1715_1, u1elo0]
                · have p1715_0 := h1715c.1
                  have p1715_1 := h1715c.2.1
                  have p1715_2 := h1715c.2.2.1
                  have p1715_3 := h1715c.2.2.2
                  linarith only [h1, hlam, p1715_0]
                · have p1715_0 := h1715c.1
                  have p1715_1 := h1715c.2.1
                  have p1715_2 := h1715c.2.2.1
                  have p1715_3 := h1715c.2.2.2
                  linarith only [h0, hc35, hlam, hphi, ht01, ht0b, ht5b, p1715_1, u1elo0]
                · have p1715_0 := h1715c.1
                  have p1715_1 := h1715c.2.1
                  have p1715_2 := h1715c.2.2.1
                  have p1715_3 := h1715c.2.2.2
                  linarith only [h1158, hlam, p1715_0]
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
                  linarith only [h1467, hlam, p1715_0]
                · have p1715_0 := h1715c.1
                  have p1715_1 := h1715c.2.1
                  have p1715_2 := h1715c.2.2.1
                  have p1715_3 := h1715c.2.2.2
                  linarith only [h1469, hlam, p1715_0]
                · have p1715_0 := h1715c.1
                  have p1715_1 := h1715c.2.1
                  have p1715_2 := h1715c.2.2.1
                  have p1715_3 := h1715c.2.2.2
                  linarith only [h1541, hlam, p1715_0]
                · have p1715_0 := h1715c.1
                  have p1715_1 := h1715c.2.1
                  have p1715_2 := h1715c.2.2.1
                  have p1715_3 := h1715c.2.2.2
                  linarith only [h0, h1467, hc12, hc25, hlam, hphi, p1715_1]
                · have p1715_0 := h1715c.1
                  have p1715_1 := h1715c.2.1
                  have p1715_2 := h1715c.2.2.1
                  have p1715_3 := h1715c.2.2.2
                  linarith only [h1467, hc12, hc25, hlam, hphi, p1715_1]
                · have p1715_0 := h1715c.1
                  have p1715_1 := h1715c.2.1
                  have p1715_2 := h1715c.2.2.1
                  have p1715_3 := h1715c.2.2.2
                  linarith only [hlam, p1715_0]
                · have p1715_0 := h1715c.1
                  have p1715_1 := h1715c.2.1
                  have p1715_2 := h1715c.2.2.1
                  have p1715_3 := h1715c.2.2.2
                  linarith only [h1657, hlam, p1715_1]
                · have p1715_0 := h1715c.1
                  have p1715_1 := h1715c.2.1
                  have p1715_2 := h1715c.2.2.1
                  have p1715_3 := h1715c.2.2.2
                  linarith only [h1659, hlam, p1715_0]
                · have p1715_0 := h1715c.1
                  have p1715_1 := h1715c.2.1
                  have p1715_2 := h1715c.2.2.1
                  have p1715_3 := h1715c.2.2.2
                  linarith only [h0, h1467, h1688, hc12, hc45, hlam, hphi, ht23, ht34, p1715_1]
                · have p1715_0 := h1715c.1
                  have p1715_1 := h1715c.2.1
                  have p1715_2 := h1715c.2.2.1
                  have p1715_3 := h1715c.2.2.2
                  linarith only [h1467, h1688, hc12, hc45, hlam, hphi, ht23, ht34, p1715_1]
                · have p1715_0 := h1715c.1
                  have p1715_1 := h1715c.2.1
                  have p1715_2 := h1715c.2.2.1
                  have p1715_3 := h1715c.2.2.2
                  linarith only [h1, h1688, hc02, hc45, hlam, hphi, ht23, ht34, p1715_1]
                · have p1715_0 := h1715c.1
                  have p1715_1 := h1715c.2.1
                  have p1715_2 := h1715c.2.2.1
                  have p1715_3 := h1715c.2.2.2
                  linarith only [hlam, p1715_0]
                · have p1715_0 := h1715c.1
                  have p1715_1 := h1715c.2.1
                  have p1715_2 := h1715c.2.2.1
                  have p1715_3 := h1715c.2.2.2
                  linarith only [h1688, hlam, p1715_0]
                · have p1715_0 := h1715c.1
                  have p1715_1 := h1715c.2.1
                  have p1715_2 := h1715c.2.2.1
                  have p1715_3 := h1715c.2.2.2
                  linarith only [h0, h1467, hc12, hc45, hlam, hphi, ht23, ht34, p1715_1]
                · have p1715_0 := h1715c.1
                  have p1715_1 := h1715c.2.1
                  have p1715_2 := h1715c.2.2.1
                  have p1715_3 := h1715c.2.2.2
                  linarith only [h1467, hc12, hc45, hlam, hphi, ht23, ht34, p1715_1]
                · have p1715_0 := h1715c.1
                  have p1715_1 := h1715c.2.1
                  have p1715_2 := h1715c.2.2.1
                  have p1715_3 := h1715c.2.2.2
                  linarith only [h1, hc02, hc45, hlam, hphi, ht23, ht34, p1715_1]
                · have p1715_0 := h1715c.1
                  have p1715_1 := h1715c.2.1
                  have p1715_2 := h1715c.2.2.1
                  have p1715_3 := h1715c.2.2.2
                  linarith only [h1469, hc13, hc45, hlam, hphi, ht34, p1715_1]
                · have p1715_0 := h1715c.1
                  have p1715_1 := h1715c.2.1
                  have p1715_2 := h1715c.2.2.1
                  have p1715_3 := h1715c.2.2.2
                  linarith only [hlam, p1715_0]

set_option maxHeartbeats 6812000 in
theorem r1l7_11_12_25_L_0_L_I_H_I_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h1 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
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
  have h1elo := hb1.1
  have h5bigk := hb5.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  rcases m.htr 0 4 5 (by decide) (by decide) with h1158 | h1158
  · exact r1l7_11_12_25_L_0_L_I_H_I_x0_x1_x0 m hb1 hb2 hb5 h0 h1 h1158
  · exact r1l7_11_12_25_L_0_L_I_H_I_x0_x1_x1 m hb1 hb2 hb5 h0 h1 h1158

set_option maxHeartbeats 6812000 in
theorem r1l7_11_12_25_L_0_L_I_H_I_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
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
  have h1elo := hb1.1
  have h5bigk := hb5.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  rcases m.htr 0 2 5 (by decide) (by decide) with h1 | h1
  · exact r1l7_11_12_25_L_0_L_I_H_I_x0_x0 m hb1 hb2 hb5 h0 h1
  · exact r1l7_11_12_25_L_0_L_I_H_I_x0_x1 m hb1 hb2 hb5 h0 h1

end R2N4
