import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_31S8

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5672000 in
set_option maxHeartbeats 5672000 in
theorem r1l7_21_14_M_LI_L_I_s0_x0_x0_x0_x1_x1 (m : N7Model)
    (hb1 : CMSig2_7_M_LI m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h1013 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
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
  have h1elo := hb1.1
  have h1bigk := hb1.2.2.2
  have h4bigk := hb4.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 4 5 (by decide) (by decide) with h1497 | h1497
  · rcases m.htr 1 2 3 (by decide) (by decide) with h1498 | h1498
    · rcases m.htr 1 2 4 (by decide) (by decide) with h1499 | h1499
      · linarith only [h0, h1499, h4, hlam]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h1501 | h1501
        · rcases m.htr 1 3 4 (by decide) (by decide) with h1502 | h1502
          · linarith only [h1, h1013, h1502, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h1504 | h1504
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1505 | h1505
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1506 | h1506
                · linarith only [h0, h1013, h1498, h1506, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h1508 | h1508
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1509 | h1509
                    · rcases h1bigk with h1510c | h1510c | h1510c | h1510c | h1510c | h1510c | h1510c | h1510c | h1510c | h1510c | h1510c | h1510c | h1510c | h1510c | h1510c | h1510c | h1510c | h1510c | h1510c | h1510c | h1510c | h1510c | h1510c | h1510c | h1510c
                      · have p1510_0 := h1510c.1
                        have p1510_1 := h1510c.2.1
                        have p1510_2 := h1510c.2.2.1
                        have p1510_3 := h1510c.2.2.2
                        linarith only [hlam, p1510_0]
                      · have p1510_0 := h1510c.1
                        have p1510_1 := h1510c.2.1
                        have p1510_2 := h1510c.2.2.1
                        have p1510_3 := h1510c.2.2.2
                        linarith only [h1498, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1510_1, u1elo0]
                      · have p1510_0 := h1510c.1
                        have p1510_1 := h1510c.2.1
                        have p1510_2 := h1510c.2.2.1
                        have p1510_3 := h1510c.2.2.2
                        linarith only [h1504, h1509, hc45, hlam, hphi, ht01, ht0b, ht5b, p1510_1, u1elo0]
                      · have p1510_0 := h1510c.1
                        have p1510_1 := h1510c.2.1
                        have p1510_2 := h1510c.2.2.1
                        have p1510_3 := h1510c.2.2.2
                        linarith only [h1498, h1499, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1510_1, u1elo0]
                      · have p1510_0 := h1510c.1
                        have p1510_1 := h1510c.2.1
                        have p1510_2 := h1510c.2.2.1
                        have p1510_3 := h1510c.2.2.2
                        rcases p1510_3 (m.d 0 1) (by simp) with h1515 | h1515
                        · rcases p1510_3 (m.d 1 2) (by simp) with h1516 | h1516
                          · linarith only [h0, h1516, hlam]
                          · linarith only [h1501, h1516, hlam]
                        · linarith only [h1515, hlam, p1510_0]
                      · have p1510_0 := h1510c.1
                        have p1510_1 := h1510c.2.1
                        have p1510_2 := h1510c.2.2.1
                        have p1510_3 := h1510c.2.2.2
                        linarith only [h0, hlam, p1510_0]
                      · have p1510_0 := h1510c.1
                        have p1510_1 := h1510c.2.1
                        have p1510_2 := h1510c.2.2.1
                        have p1510_3 := h1510c.2.2.2
                        linarith only [hlam, p1510_0]
                      · have p1510_0 := h1510c.1
                        have p1510_1 := h1510c.2.1
                        have p1510_2 := h1510c.2.2.1
                        have p1510_3 := h1510c.2.2.2
                        linarith only [h1504, h1509, hc45, hlam, hphi, ht01, ht0b, ht5b, p1510_1, u1elo1]
                      · have p1510_0 := h1510c.1
                        have p1510_1 := h1510c.2.1
                        have p1510_2 := h1510c.2.2.1
                        have p1510_3 := h1510c.2.2.2
                        linarith only [h1499, hlam, p1510_1]
                      · have p1510_0 := h1510c.1
                        have p1510_1 := h1510c.2.1
                        have p1510_2 := h1510c.2.2.1
                        have p1510_3 := h1510c.2.2.2
                        linarith only [h1499, h2, hc15, hlam, hphi, ht01, ht0b, ht5b, p1510_1, u1elo0]
                      · have p1510_0 := h1510c.1
                        have p1510_1 := h1510c.2.1
                        have p1510_2 := h1510c.2.2.1
                        have p1510_3 := h1510c.2.2.2
                        linarith only [h1, hlam, p1510_0]
                      · have p1510_0 := h1510c.1
                        have p1510_1 := h1510c.2.1
                        have p1510_2 := h1510c.2.2.1
                        have p1510_3 := h1510c.2.2.2
                        linarith only [h1498, hlam, p1510_0]
                      · have p1510_0 := h1510c.1
                        have p1510_1 := h1510c.2.1
                        have p1510_2 := h1510c.2.2.1
                        have p1510_3 := h1510c.2.2.2
                        linarith only [hlam, p1510_0]
                      · have p1510_0 := h1510c.1
                        have p1510_1 := h1510c.2.1
                        have p1510_2 := h1510c.2.2.1
                        have p1510_3 := h1510c.2.2.2
                        linarith only [h1502, hlam, p1510_0]
                      · have p1510_0 := h1510c.1
                        have p1510_1 := h1510c.2.1
                        have p1510_2 := h1510c.2.2.1
                        have p1510_3 := h1510c.2.2.2
                        linarith only [h1, h1501, hc25, hlam, hphi, ht01, ht0b, ht5b, p1510_1, u1elo0]
                      · have p1510_0 := h1510c.1
                        have p1510_1 := h1510c.2.1
                        have p1510_2 := h1510c.2.2.1
                        have p1510_3 := h1510c.2.2.2
                        linarith only [h2, hlam, p1510_0]
                      · have p1510_0 := h1510c.1
                        have p1510_1 := h1510c.2.1
                        have p1510_2 := h1510c.2.2.1
                        have p1510_3 := h1510c.2.2.2
                        linarith only [h2, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1510_1, u1elo0]
                      · have p1510_0 := h1510c.1
                        have p1510_1 := h1510c.2.1
                        have p1510_2 := h1510c.2.2.1
                        have p1510_3 := h1510c.2.2.2
                        linarith only [h2, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1510_1, u1elo0]
                      · have p1510_0 := h1510c.1
                        have p1510_1 := h1510c.2.1
                        have p1510_2 := h1510c.2.2.1
                        have p1510_3 := h1510c.2.2.2
                        linarith only [hlam, p1510_0]
                      · have p1510_0 := h1510c.1
                        have p1510_1 := h1510c.2.1
                        have p1510_2 := h1510c.2.2.1
                        have p1510_3 := h1510c.2.2.2
                        linarith only [h1504, h1509, h2, hc45, hlam, hphi, ht01, ht0b, ht5b, p1510_1, u1elo0]
                      · have p1510_0 := h1510c.1
                        have p1510_1 := h1510c.2.1
                        have p1510_2 := h1510c.2.2.1
                        have p1510_3 := h1510c.2.2.2
                        linarith only [h3, hlam, p1510_0]
                      · have p1510_0 := h1510c.1
                        have p1510_1 := h1510c.2.1
                        have p1510_2 := h1510c.2.2.1
                        have p1510_3 := h1510c.2.2.2
                        linarith only [h1501, hlam, p1510_0]
                      · have p1510_0 := h1510c.1
                        have p1510_1 := h1510c.2.1
                        have p1510_2 := h1510c.2.2.1
                        have p1510_3 := h1510c.2.2.2
                        linarith only [h1504, hlam, p1510_0]
                      · have p1510_0 := h1510c.1
                        have p1510_1 := h1510c.2.1
                        have p1510_2 := h1510c.2.2.1
                        have p1510_3 := h1510c.2.2.2
                        linarith only [h1505, hlam, p1510_0]
                      · have p1510_0 := h1510c.1
                        have p1510_1 := h1510c.2.1
                        have p1510_2 := h1510c.2.2.1
                        have p1510_3 := h1510c.2.2.2
                        linarith only [hlam, p1510_0]
                    · linarith only [h1, h1013, h1497, h1504, h1509, hc04, hc35, hlam, hphi, ht0b, ht5b]
                  · linarith only [h0, h1498, h1505, h1508, h4, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo4]
              · linarith only [h1497, h1498, h1499, h1505, h2, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1543 | h1543
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1544 | h1544
                · linarith only [h0, h1498, h1544, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h1546 | h1546
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1547 | h1547
                    · rcases h1bigk with h1548c | h1548c | h1548c | h1548c | h1548c | h1548c | h1548c | h1548c | h1548c | h1548c | h1548c | h1548c | h1548c | h1548c | h1548c | h1548c | h1548c | h1548c | h1548c | h1548c | h1548c | h1548c | h1548c | h1548c | h1548c
                      · have p1548_0 := h1548c.1
                        have p1548_1 := h1548c.2.1
                        have p1548_2 := h1548c.2.2.1
                        have p1548_3 := h1548c.2.2.2
                        linarith only [hlam, p1548_0]
                      · have p1548_0 := h1548c.1
                        have p1548_1 := h1548c.2.1
                        have p1548_2 := h1548c.2.2.1
                        have p1548_3 := h1548c.2.2.2
                        linarith only [h1498, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1548_1, u1elo0]
                      · have p1548_0 := h1548c.1
                        have p1548_1 := h1548c.2.1
                        have p1548_2 := h1548c.2.2.1
                        have p1548_3 := h1548c.2.2.2
                        rcases p1548_3 (m.d 0 1) (by simp) with h1551 | h1551
                        · rcases p1548_3 (m.d 1 2) (by simp) with h1552 | h1552
                          · linarith only [h0, h1552, hlam]
                          · linarith only [h1498, h1552, hlam]
                        · linarith only [h1551, hlam, p1548_0]
                      · have p1548_0 := h1548c.1
                        have p1548_1 := h1548c.2.1
                        have p1548_2 := h1548c.2.2.1
                        have p1548_3 := h1548c.2.2.2
                        linarith only [h1498, h1499, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1548_1, u1elo0]
                      · have p1548_0 := h1548c.1
                        have p1548_1 := h1548c.2.1
                        have p1548_2 := h1548c.2.2.1
                        have p1548_3 := h1548c.2.2.2
                        rcases p1548_3 (m.d 0 1) (by simp) with h1557 | h1557
                        · rcases p1548_3 (m.d 1 2) (by simp) with h1558 | h1558
                          · linarith only [h0, h1558, hlam]
                          · linarith only [h1501, h1558, hlam]
                        · linarith only [h1557, hlam, p1548_0]
                      · have p1548_0 := h1548c.1
                        have p1548_1 := h1548c.2.1
                        have p1548_2 := h1548c.2.2.1
                        have p1548_3 := h1548c.2.2.2
                        linarith only [h0, hlam, p1548_0]
                      · have p1548_0 := h1548c.1
                        have p1548_1 := h1548c.2.1
                        have p1548_2 := h1548c.2.2.1
                        have p1548_3 := h1548c.2.2.2
                        linarith only [hlam, p1548_0]
                      · have p1548_0 := h1548c.1
                        have p1548_1 := h1548c.2.1
                        have p1548_2 := h1548c.2.2.1
                        have p1548_3 := h1548c.2.2.2
                        linarith only [h0, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1548_1, u1elo0]
                      · have p1548_0 := h1548c.1
                        have p1548_1 := h1548c.2.1
                        have p1548_2 := h1548c.2.2.1
                        have p1548_3 := h1548c.2.2.2
                        linarith only [h1499, hlam, p1548_1]
                      · have p1548_0 := h1548c.1
                        have p1548_1 := h1548c.2.1
                        have p1548_2 := h1548c.2.2.1
                        have p1548_3 := h1548c.2.2.2
                        linarith only [h1499, h2, hc15, hlam, hphi, ht01, ht0b, ht5b, p1548_1, u1elo0]
                      · have p1548_0 := h1548c.1
                        have p1548_1 := h1548c.2.1
                        have p1548_2 := h1548c.2.2.1
                        have p1548_3 := h1548c.2.2.2
                        linarith only [h1, hlam, p1548_0]
                      · have p1548_0 := h1548c.1
                        have p1548_1 := h1548c.2.1
                        have p1548_2 := h1548c.2.2.1
                        have p1548_3 := h1548c.2.2.2
                        linarith only [h1498, hlam, p1548_0]
                      · have p1548_0 := h1548c.1
                        have p1548_1 := h1548c.2.1
                        have p1548_2 := h1548c.2.2.1
                        have p1548_3 := h1548c.2.2.2
                        linarith only [hlam, p1548_0]
                      · have p1548_0 := h1548c.1
                        have p1548_1 := h1548c.2.1
                        have p1548_2 := h1548c.2.2.1
                        have p1548_3 := h1548c.2.2.2
                        linarith only [h1502, hlam, p1548_0]
                      · have p1548_0 := h1548c.1
                        have p1548_1 := h1548c.2.1
                        have p1548_2 := h1548c.2.2.1
                        have p1548_3 := h1548c.2.2.2
                        linarith only [h1504, hlam, p1548_1]
                      · have p1548_0 := h1548c.1
                        have p1548_1 := h1548c.2.1
                        have p1548_2 := h1548c.2.2.1
                        have p1548_3 := h1548c.2.2.2
                        linarith only [h2, hlam, p1548_0]
                      · have p1548_0 := h1548c.1
                        have p1548_1 := h1548c.2.1
                        have p1548_2 := h1548c.2.2.1
                        have p1548_3 := h1548c.2.2.2
                        linarith only [h2, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1548_1, u1elo0]
                      · have p1548_0 := h1548c.1
                        have p1548_1 := h1548c.2.1
                        have p1548_2 := h1548c.2.2.1
                        have p1548_3 := h1548c.2.2.2
                        linarith only [h1498, h2, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1548_1, u1elo0]
                      · have p1548_0 := h1548c.1
                        have p1548_1 := h1548c.2.1
                        have p1548_2 := h1548c.2.2.1
                        have p1548_3 := h1548c.2.2.2
                        linarith only [hlam, p1548_0]
                      · have p1548_0 := h1548c.1
                        have p1548_1 := h1548c.2.1
                        have p1548_2 := h1548c.2.2.1
                        have p1548_3 := h1548c.2.2.2
                        linarith only [h1498, h1504, h2, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1548_1, u1elo0]
                      · have p1548_0 := h1548c.1
                        have p1548_1 := h1548c.2.1
                        have p1548_2 := h1548c.2.2.1
                        have p1548_3 := h1548c.2.2.2
                        linarith only [h3, hlam, p1548_0]
                      · have p1548_0 := h1548c.1
                        have p1548_1 := h1548c.2.1
                        have p1548_2 := h1548c.2.2.1
                        have p1548_3 := h1548c.2.2.2
                        linarith only [h1501, hlam, p1548_0]
                      · have p1548_0 := h1548c.1
                        have p1548_1 := h1548c.2.1
                        have p1548_2 := h1548c.2.2.1
                        have p1548_3 := h1548c.2.2.2
                        linarith only [h1498, h3, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1548_1, u1elo0]
                      · have p1548_0 := h1548c.1
                        have p1548_1 := h1548c.2.1
                        have p1548_2 := h1548c.2.2.1
                        have p1548_3 := h1548c.2.2.2
                        linarith only [h1543, hlam, p1548_0]
                      · have p1548_0 := h1548c.1
                        have p1548_1 := h1548c.2.1
                        have p1548_2 := h1548c.2.2.1
                        have p1548_3 := h1548c.2.2.2
                        linarith only [hlam, p1548_0]
                    · linarith only [h0, h1498, h1544, h1547, h4, hc23, hc45, hlam, hphi, ht34]
                  · linarith only [h0, h1498, h1543, h1546, h2, h4, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
              · linarith only [h1497, h1498, h1499, h1543, h2, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h1585 | h1585
          · linarith only [h1, h1013, h1585, hlam]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h1587 | h1587
            · linarith only [h1498, h1501, h1587, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1589 | h1589
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1590 | h1590
                · linarith only [h0, h1013, h1498, h1590, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h1592 | h1592
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1593 | h1593
                    · rcases h1bigk with h1594c | h1594c | h1594c | h1594c | h1594c | h1594c | h1594c | h1594c | h1594c | h1594c | h1594c | h1594c | h1594c | h1594c | h1594c | h1594c | h1594c | h1594c | h1594c | h1594c | h1594c | h1594c | h1594c | h1594c | h1594c
                      · have p1594_0 := h1594c.1
                        have p1594_1 := h1594c.2.1
                        have p1594_2 := h1594c.2.2.1
                        have p1594_3 := h1594c.2.2.2
                        linarith only [hlam, p1594_0]
                      · have p1594_0 := h1594c.1
                        have p1594_1 := h1594c.2.1
                        have p1594_2 := h1594c.2.2.1
                        have p1594_3 := h1594c.2.2.2
                        linarith only [h1498, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1594_1, u1elo0]
                      · have p1594_0 := h1594c.1
                        have p1594_1 := h1594c.2.1
                        have p1594_2 := h1594c.2.2.1
                        have p1594_3 := h1594c.2.2.2
                        rcases p1594_3 (m.d 0 1) (by simp) with h1597 | h1597
                        · rcases p1594_3 (m.d 1 2) (by simp) with h1598 | h1598
                          · linarith only [h0, h1598, hlam]
                          · linarith only [h1498, h1598, hlam]
                        · linarith only [h1597, hlam, p1594_0]
                      · have p1594_0 := h1594c.1
                        have p1594_1 := h1594c.2.1
                        have p1594_2 := h1594c.2.2.1
                        have p1594_3 := h1594c.2.2.2
                        linarith only [h1498, h1499, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1594_1, u1elo0]
                      · have p1594_0 := h1594c.1
                        have p1594_1 := h1594c.2.1
                        have p1594_2 := h1594c.2.2.1
                        have p1594_3 := h1594c.2.2.2
                        linarith only [h1498, h1501, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1594_1, u1elo0]
                      · have p1594_0 := h1594c.1
                        have p1594_1 := h1594c.2.1
                        have p1594_2 := h1594c.2.2.1
                        have p1594_3 := h1594c.2.2.2
                        linarith only [h0, hlam, p1594_0]
                      · have p1594_0 := h1594c.1
                        have p1594_1 := h1594c.2.1
                        have p1594_2 := h1594c.2.2.1
                        have p1594_3 := h1594c.2.2.2
                        linarith only [hlam, p1594_0]
                      · have p1594_0 := h1594c.1
                        have p1594_1 := h1594c.2.1
                        have p1594_2 := h1594c.2.2.1
                        have p1594_3 := h1594c.2.2.2
                        linarith only [h0, h1590, h4, hc13, hc34, hlam, hphi, p1594_1]
                      · have p1594_0 := h1594c.1
                        have p1594_1 := h1594c.2.1
                        have p1594_2 := h1594c.2.2.1
                        have p1594_3 := h1594c.2.2.2
                        linarith only [h1499, hlam, p1594_1]
                      · have p1594_0 := h1594c.1
                        have p1594_1 := h1594c.2.1
                        have p1594_2 := h1594c.2.2.1
                        have p1594_3 := h1594c.2.2.2
                        linarith only [h1501, hlam, p1594_1]
                      · have p1594_0 := h1594c.1
                        have p1594_1 := h1594c.2.1
                        have p1594_2 := h1594c.2.2.1
                        have p1594_3 := h1594c.2.2.2
                        linarith only [h1, hlam, p1594_0]
                      · have p1594_0 := h1594c.1
                        have p1594_1 := h1594c.2.1
                        have p1594_2 := h1594c.2.2.1
                        have p1594_3 := h1594c.2.2.2
                        linarith only [h1498, hlam, p1594_0]
                      · have p1594_0 := h1594c.1
                        have p1594_1 := h1594c.2.1
                        have p1594_2 := h1594c.2.2.1
                        have p1594_3 := h1594c.2.2.2
                        linarith only [hlam, p1594_0]
                      · have p1594_0 := h1594c.1
                        have p1594_1 := h1594c.2.1
                        have p1594_2 := h1594c.2.2.1
                        have p1594_3 := h1594c.2.2.2
                        linarith only [h1585, hlam, p1594_0]
                      · have p1594_0 := h1594c.1
                        have p1594_1 := h1594c.2.1
                        have p1594_2 := h1594c.2.2.1
                        have p1594_3 := h1594c.2.2.2
                        linarith only [h1587, hlam, p1594_1]
                      · have p1594_0 := h1594c.1
                        have p1594_1 := h1594c.2.1
                        have p1594_2 := h1594c.2.2.1
                        have p1594_3 := h1594c.2.2.2
                        linarith only [h2, hlam, p1594_0]
                      · have p1594_0 := h1594c.1
                        have p1594_1 := h1594c.2.1
                        have p1594_2 := h1594c.2.2.1
                        have p1594_3 := h1594c.2.2.2
                        linarith only [h1498, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1594_1, u1elo3]
                      · have p1594_0 := h1594c.1
                        have p1594_1 := h1594c.2.1
                        have p1594_2 := h1594c.2.2.1
                        have p1594_3 := h1594c.2.2.2
                        linarith only [h1498, h2, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1594_1, u1elo0]
                      · have p1594_0 := h1594c.1
                        have p1594_1 := h1594c.2.1
                        have p1594_2 := h1594c.2.2.1
                        have p1594_3 := h1594c.2.2.2
                        linarith only [hlam, p1594_0]
                      · have p1594_0 := h1594c.1
                        have p1594_1 := h1594c.2.1
                        have p1594_2 := h1594c.2.2.1
                        have p1594_3 := h1594c.2.2.2
                        linarith only [h1498, h1501, h2, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1594_1, u1elo0]
                      · have p1594_0 := h1594c.1
                        have p1594_1 := h1594c.2.1
                        have p1594_2 := h1594c.2.2.1
                        have p1594_3 := h1594c.2.2.2
                        linarith only [h3, hlam, p1594_0]
                      · have p1594_0 := h1594c.1
                        have p1594_1 := h1594c.2.1
                        have p1594_2 := h1594c.2.2.1
                        have p1594_3 := h1594c.2.2.2
                        linarith only [h1498, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1594_1, u1elo4]
                      · have p1594_0 := h1594c.1
                        have p1594_1 := h1594c.2.1
                        have p1594_2 := h1594c.2.2.1
                        have p1594_3 := h1594c.2.2.2
                        linarith only [h1498, h3, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1594_1, u1elo0]
                      · have p1594_0 := h1594c.1
                        have p1594_1 := h1594c.2.1
                        have p1594_2 := h1594c.2.2.1
                        have p1594_3 := h1594c.2.2.2
                        linarith only [h1589, hlam, p1594_0]
                      · have p1594_0 := h1594c.1
                        have p1594_1 := h1594c.2.1
                        have p1594_2 := h1594c.2.2.1
                        have p1594_3 := h1594c.2.2.2
                        linarith only [hlam, p1594_0]
                    · linarith only [h0, h1498, h1590, h1593, h4, hc23, hc45, hlam, hphi, ht34]
                  · linarith only [h0, h1498, h1589, h1592, h2, h4, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
              · linarith only [h1497, h1498, h1499, h1589, h2, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
    · rcases m.htr 1 2 4 (by decide) (by decide) with h1627 | h1627
      · linarith only [h0, h1497, h1627, h4, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h1629 | h1629
        · rcases m.htr 1 3 4 (by decide) (by decide) with h1630 | h1630
          · linarith only [h1, h1013, h1630, hlam]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h1632 | h1632
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1633 | h1633
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1634 | h1634
                · rcases m.htr 2 4 5 (by decide) (by decide) with h1635 | h1635
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1636 | h1636
                    · rcases h1bigk with h1637c | h1637c | h1637c | h1637c | h1637c | h1637c | h1637c | h1637c | h1637c | h1637c | h1637c | h1637c | h1637c | h1637c | h1637c | h1637c | h1637c | h1637c | h1637c | h1637c | h1637c | h1637c | h1637c | h1637c | h1637c
                      · have p1637_0 := h1637c.1
                        have p1637_1 := h1637c.2.1
                        have p1637_2 := h1637c.2.2.1
                        have p1637_3 := h1637c.2.2.2
                        linarith only [hlam, p1637_0]
                      · have p1637_0 := h1637c.1
                        have p1637_1 := h1637c.2.1
                        have p1637_2 := h1637c.2.2.1
                        have p1637_3 := h1637c.2.2.2
                        linarith only [h1629, h1635, hc45, hlam, hphi, ht01, ht0b, ht5b, p1637_1, u1elo0]
                      · have p1637_0 := h1637c.1
                        have p1637_1 := h1637c.2.1
                        have p1637_2 := h1637c.2.2.1
                        have p1637_3 := h1637c.2.2.2
                        linarith only [h1498, h1629, h1635, hc45, hlam, hphi, ht01, ht0b, ht5b, p1637_1, u1elo0]
                      · have p1637_0 := h1637c.1
                        have p1637_1 := h1637c.2.1
                        have p1637_2 := h1637c.2.2.1
                        have p1637_3 := h1637c.2.2.2
                        linarith only [h1627, h1629, h1635, hc45, hlam, hphi, ht01, ht0b, ht5b, p1637_1, u1elo0]
                      · have p1637_0 := h1637c.1
                        have p1637_1 := h1637c.2.1
                        have p1637_2 := h1637c.2.2.1
                        have p1637_3 := h1637c.2.2.2
                        rcases p1637_3 (m.d 0 1) (by simp) with h1642 | h1642
                        · rcases p1637_3 (m.d 1 2) (by simp) with h1643 | h1643
                          · linarith only [h0, h1643, hlam]
                          · linarith only [h1629, h1643, hlam]
                        · linarith only [h1642, hlam, p1637_0]
                      · have p1637_0 := h1637c.1
                        have p1637_1 := h1637c.2.1
                        have p1637_2 := h1637c.2.2.1
                        have p1637_3 := h1637c.2.2.2
                        linarith only [h0, hlam, p1637_0]
                      · have p1637_0 := h1637c.1
                        have p1637_1 := h1637c.2.1
                        have p1637_2 := h1637c.2.2.1
                        have p1637_3 := h1637c.2.2.2
                        linarith only [hlam, p1637_0]
                      · have p1637_0 := h1637c.1
                        have p1637_1 := h1637c.2.1
                        have p1637_2 := h1637c.2.2.1
                        have p1637_3 := h1637c.2.2.2
                        linarith only [h1498, hlam, p1637_1]
                      · have p1637_0 := h1637c.1
                        have p1637_1 := h1637c.2.1
                        have p1637_2 := h1637c.2.2.1
                        have p1637_3 := h1637c.2.2.2
                        linarith only [h1627, hlam, p1637_1]
                      · have p1637_0 := h1637c.1
                        have p1637_1 := h1637c.2.1
                        have p1637_2 := h1637c.2.2.1
                        have p1637_3 := h1637c.2.2.2
                        linarith only [h1, h1013, h1498, h1634, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1637_1]
                      · have p1637_0 := h1637c.1
                        have p1637_1 := h1637c.2.1
                        have p1637_2 := h1637c.2.2.1
                        have p1637_3 := h1637c.2.2.2
                        linarith only [h1, hlam, p1637_0]
                      · have p1637_0 := h1637c.1
                        have p1637_1 := h1637c.2.1
                        have p1637_2 := h1637c.2.2.1
                        have p1637_3 := h1637c.2.2.2
                        linarith only [h1629, h1630, hc25, hlam, hphi, ht01, ht0b, ht5b, p1637_1, u1elo3]
                      · have p1637_0 := h1637c.1
                        have p1637_1 := h1637c.2.1
                        have p1637_2 := h1637c.2.2.1
                        have p1637_3 := h1637c.2.2.2
                        linarith only [hlam, p1637_0]
                      · have p1637_0 := h1637c.1
                        have p1637_1 := h1637c.2.1
                        have p1637_2 := h1637c.2.2.1
                        have p1637_3 := h1637c.2.2.2
                        linarith only [h1630, hlam, p1637_0]
                      · have p1637_0 := h1637c.1
                        have p1637_1 := h1637c.2.1
                        have p1637_2 := h1637c.2.2.1
                        have p1637_3 := h1637c.2.2.2
                        linarith only [h1, h1013, h1629, h1634, h1635, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1637_1]
                      · have p1637_0 := h1637c.1
                        have p1637_1 := h1637c.2.1
                        have p1637_2 := h1637c.2.2.1
                        have p1637_3 := h1637c.2.2.2
                        linarith only [h2, hlam, p1637_0]
                      · have p1637_0 := h1637c.1
                        have p1637_1 := h1637c.2.1
                        have p1637_2 := h1637c.2.2.1
                        have p1637_3 := h1637c.2.2.2
                        linarith only [h1629, h1635, h2, hc45, hlam, hphi, ht01, ht0b, ht5b, p1637_1, u1elo0]
                      · have p1637_0 := h1637c.1
                        have p1637_1 := h1637c.2.1
                        have p1637_2 := h1637c.2.2.1
                        have p1637_3 := h1637c.2.2.2
                        linarith only [h2, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1637_1, u1elo0]
                      · have p1637_0 := h1637c.1
                        have p1637_1 := h1637c.2.1
                        have p1637_2 := h1637c.2.2.1
                        have p1637_3 := h1637c.2.2.2
                        linarith only [hlam, p1637_0]
                      · have p1637_0 := h1637c.1
                        have p1637_1 := h1637c.2.1
                        have p1637_2 := h1637c.2.2.1
                        have p1637_3 := h1637c.2.2.2
                        linarith only [h1629, h1635, h2, hc45, hlam, hphi, ht01, ht0b, ht5b, p1637_1, u1elo0]
                      · have p1637_0 := h1637c.1
                        have p1637_1 := h1637c.2.1
                        have p1637_2 := h1637c.2.2.1
                        have p1637_3 := h1637c.2.2.2
                        linarith only [h3, hlam, p1637_0]
                      · have p1637_0 := h1637c.1
                        have p1637_1 := h1637c.2.1
                        have p1637_2 := h1637c.2.2.1
                        have p1637_3 := h1637c.2.2.2
                        linarith only [h1629, hlam, p1637_0]
                      · have p1637_0 := h1637c.1
                        have p1637_1 := h1637c.2.1
                        have p1637_2 := h1637c.2.2.1
                        have p1637_3 := h1637c.2.2.2
                        linarith only [h1632, hlam, p1637_0]
                      · have p1637_0 := h1637c.1
                        have p1637_1 := h1637c.2.1
                        have p1637_2 := h1637c.2.2.1
                        have p1637_3 := h1637c.2.2.2
                        linarith only [h1633, hlam, p1637_0]
                      · have p1637_0 := h1637c.1
                        have p1637_1 := h1637c.2.1
                        have p1637_2 := h1637c.2.2.1
                        have p1637_3 := h1637c.2.2.2
                        linarith only [hlam, p1637_0]
                    · linarith only [h1013, h1629, h1635, h1636, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                  · linarith only [h1, h1013, h1497, h1498, h1629, h1634, h1635, hc04, hc25, hlam, hphi, ht0b, ht5b]
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
                        linarith only [h1629, h1669, hc45, hlam, hphi, ht01, ht0b, ht5b, p1671_1, u1elo0]
                      · have p1671_0 := h1671c.1
                        have p1671_1 := h1671c.2.1
                        have p1671_2 := h1671c.2.2.1
                        have p1671_3 := h1671c.2.2.2
                        linarith only [h1498, h1629, h1669, hc45, hlam, hphi, ht01, ht0b, ht5b, p1671_1, u1elo0]
                      · have p1671_0 := h1671c.1
                        have p1671_1 := h1671c.2.1
                        have p1671_2 := h1671c.2.2.1
                        have p1671_3 := h1671c.2.2.2
                        linarith only [h1498, h1629, h1630, h1669, hc45, hlam, hphi, ht01, ht0b, ht5b, p1671_1, u1elo0]
                      · have p1671_0 := h1671c.1
                        have p1671_1 := h1671c.2.1
                        have p1671_2 := h1671c.2.2.1
                        have p1671_3 := h1671c.2.2.2
                        rcases p1671_3 (m.d 0 1) (by simp) with h1676 | h1676
                        · rcases p1671_3 (m.d 1 2) (by simp) with h1677 | h1677
                          · linarith only [h0, h1677, hlam]
                          · linarith only [h1629, h1677, hlam]
                        · linarith only [h1676, hlam, p1671_0]
                      · have p1671_0 := h1671c.1
                        have p1671_1 := h1671c.2.1
                        have p1671_2 := h1671c.2.2.1
                        have p1671_3 := h1671c.2.2.2
                        linarith only [h0, hlam, p1671_0]
                      · have p1671_0 := h1671c.1
                        have p1671_1 := h1671c.2.1
                        have p1671_2 := h1671c.2.2.1
                        have p1671_3 := h1671c.2.2.2
                        linarith only [hlam, p1671_0]
                      · have p1671_0 := h1671c.1
                        have p1671_1 := h1671c.2.1
                        have p1671_2 := h1671c.2.2.1
                        have p1671_3 := h1671c.2.2.2
                        linarith only [h1498, hlam, p1671_1]
                      · have p1671_0 := h1671c.1
                        have p1671_1 := h1671c.2.1
                        have p1671_2 := h1671c.2.2.1
                        have p1671_3 := h1671c.2.2.2
                        linarith only [h1627, hlam, p1671_1]
                      · have p1671_0 := h1671c.1
                        have p1671_1 := h1671c.2.1
                        have p1671_2 := h1671c.2.2.1
                        have p1671_3 := h1671c.2.2.2
                        linarith only [h1498, h1629, h1634, h1669, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1671_1]
                      · have p1671_0 := h1671c.1
                        have p1671_1 := h1671c.2.1
                        have p1671_2 := h1671c.2.2.1
                        have p1671_3 := h1671c.2.2.2
                        linarith only [h1, hlam, p1671_0]
                      · have p1671_0 := h1671c.1
                        have p1671_1 := h1671c.2.1
                        have p1671_2 := h1671c.2.2.1
                        have p1671_3 := h1671c.2.2.2
                        linarith only [h1, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1671_1, u1elo0]
                      · have p1671_0 := h1671c.1
                        have p1671_1 := h1671c.2.1
                        have p1671_2 := h1671c.2.2.1
                        have p1671_3 := h1671c.2.2.2
                        linarith only [hlam, p1671_0]
                      · have p1671_0 := h1671c.1
                        have p1671_1 := h1671c.2.1
                        have p1671_2 := h1671c.2.2.1
                        have p1671_3 := h1671c.2.2.2
                        linarith only [h1630, hlam, p1671_0]
                      · have p1671_0 := h1671c.1
                        have p1671_1 := h1671c.2.1
                        have p1671_2 := h1671c.2.2.1
                        have p1671_3 := h1671c.2.2.2
                        linarith only [h1629, h1630, h1669, h2, hc45, hlam, hphi, ht01, ht0b, ht5b, p1671_1, u1elo0]
                      · have p1671_0 := h1671c.1
                        have p1671_1 := h1671c.2.1
                        have p1671_2 := h1671c.2.2.1
                        have p1671_3 := h1671c.2.2.2
                        linarith only [h2, hlam, p1671_0]
                      · have p1671_0 := h1671c.1
                        have p1671_1 := h1671c.2.1
                        have p1671_2 := h1671c.2.2.1
                        have p1671_3 := h1671c.2.2.2
                        linarith only [h1629, h1669, h2, hc45, hlam, hphi, ht01, ht0b, ht5b, p1671_1, u1elo0]
                      · have p1671_0 := h1671c.1
                        have p1671_1 := h1671c.2.1
                        have p1671_2 := h1671c.2.2.1
                        have p1671_3 := h1671c.2.2.2
                        linarith only [h2, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1671_1, u1elo0]
                      · have p1671_0 := h1671c.1
                        have p1671_1 := h1671c.2.1
                        have p1671_2 := h1671c.2.2.1
                        have p1671_3 := h1671c.2.2.2
                        linarith only [hlam, p1671_0]
                      · have p1671_0 := h1671c.1
                        have p1671_1 := h1671c.2.1
                        have p1671_2 := h1671c.2.2.1
                        have p1671_3 := h1671c.2.2.2
                        linarith only [h1629, h1669, h2, hc45, hlam, hphi, ht01, ht0b, ht5b, p1671_1, u1elo0]
                      · have p1671_0 := h1671c.1
                        have p1671_1 := h1671c.2.1
                        have p1671_2 := h1671c.2.2.1
                        have p1671_3 := h1671c.2.2.2
                        linarith only [h3, hlam, p1671_0]
                      · have p1671_0 := h1671c.1
                        have p1671_1 := h1671c.2.1
                        have p1671_2 := h1671c.2.2.1
                        have p1671_3 := h1671c.2.2.2
                        linarith only [h1629, hlam, p1671_0]
                      · have p1671_0 := h1671c.1
                        have p1671_1 := h1671c.2.1
                        have p1671_2 := h1671c.2.2.1
                        have p1671_3 := h1671c.2.2.2
                        linarith only [h1632, hlam, p1671_0]
                      · have p1671_0 := h1671c.1
                        have p1671_1 := h1671c.2.1
                        have p1671_2 := h1671c.2.2.1
                        have p1671_3 := h1671c.2.2.2
                        linarith only [h1633, hlam, p1671_0]
                      · have p1671_0 := h1671c.1
                        have p1671_1 := h1671c.2.1
                        have p1671_2 := h1671c.2.2.1
                        have p1671_3 := h1671c.2.2.2
                        linarith only [hlam, p1671_0]
                    · linarith only [h1629, h1634, h1669, h1670, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                  · linarith only [h1497, h1669, h4, hlam]
              · linarith only [h1497, h1498, h1629, h1630, h1633, h2, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
            · linarith only [h1498, h1629, h1632, hlam]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h1705 | h1705
          · linarith only [h1, h1013, h1705, hlam]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h1707 | h1707
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1708 | h1708
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1709 | h1709
                · rcases m.htr 2 4 5 (by decide) (by decide) with h1710 | h1710
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1711 | h1711
                    · rcases h1bigk with h1712c | h1712c | h1712c | h1712c | h1712c | h1712c | h1712c | h1712c | h1712c | h1712c | h1712c | h1712c | h1712c | h1712c | h1712c | h1712c | h1712c | h1712c | h1712c | h1712c | h1712c | h1712c | h1712c | h1712c | h1712c
                      · have p1712_0 := h1712c.1
                        have p1712_1 := h1712c.2.1
                        have p1712_2 := h1712c.2.2.1
                        have p1712_3 := h1712c.2.2.2
                        linarith only [hlam, p1712_0]
                      · have p1712_0 := h1712c.1
                        have p1712_1 := h1712c.2.1
                        have p1712_2 := h1712c.2.2.1
                        have p1712_3 := h1712c.2.2.2
                        rcases p1712_3 (m.d 0 1) (by simp) with h1714 | h1714
                        · rcases p1712_3 (m.d 1 2) (by simp) with h1715 | h1715
                          · linarith only [h1715, hlam, p1712_0]
                          · rcases p1712_3 (m.d 1 3) (by simp) with h1717 | h1717
                            · linarith only [h1, h1717, hlam]
                            · linarith only [h1498, h1717, hlam]
                        · linarith only [h1714, hlam, p1712_0]
                      · have p1712_0 := h1712c.1
                        have p1712_1 := h1712c.2.1
                        have p1712_2 := h1712c.2.2.1
                        have p1712_3 := h1712c.2.2.2
                        linarith only [h1707, hc35, hlam, hphi, ht01, ht0b, ht5b, p1712_1, u1elo0]
                      · have p1712_0 := h1712c.1
                        have p1712_1 := h1712c.2.1
                        have p1712_2 := h1712c.2.2.1
                        have p1712_3 := h1712c.2.2.2
                        linarith only [h1705, h1707, h1711, hc45, hlam, hphi, ht01, ht0b, ht5b, p1712_1, u1elo0]
                      · have p1712_0 := h1712c.1
                        have p1712_1 := h1712c.2.1
                        have p1712_2 := h1712c.2.2.1
                        have p1712_3 := h1712c.2.2.2
                        rcases p1712_3 (m.d 0 1) (by simp) with h1723 | h1723
                        · rcases p1712_3 (m.d 1 2) (by simp) with h1724 | h1724
                          · linarith only [h0, h1724, hlam]
                          · rcases p1712_3 (m.d 1 3) (by simp) with h1726 | h1726
                            · linarith only [h1, h1726, hlam]
                            · linarith only [h1707, h1726, hlam]
                        · linarith only [h1723, hlam, p1712_0]
                      · have p1712_0 := h1712c.1
                        have p1712_1 := h1712c.2.1
                        have p1712_2 := h1712c.2.2.1
                        have p1712_3 := h1712c.2.2.2
                        linarith only [h0, hlam, p1712_0]
                      · have p1712_0 := h1712c.1
                        have p1712_1 := h1712c.2.1
                        have p1712_2 := h1712c.2.2.1
                        have p1712_3 := h1712c.2.2.2
                        linarith only [hlam, p1712_0]
                      · have p1712_0 := h1712c.1
                        have p1712_1 := h1712c.2.1
                        have p1712_2 := h1712c.2.2.1
                        have p1712_3 := h1712c.2.2.2
                        linarith only [h1498, hlam, p1712_1]
                      · have p1712_0 := h1712c.1
                        have p1712_1 := h1712c.2.1
                        have p1712_2 := h1712c.2.2.1
                        have p1712_3 := h1712c.2.2.2
                        linarith only [h1627, hlam, p1712_1]
                      · have p1712_0 := h1712c.1
                        have p1712_1 := h1712c.2.1
                        have p1712_2 := h1712c.2.2.1
                        have p1712_3 := h1712c.2.2.2
                        linarith only [h1629, hlam, p1712_1]
                      · have p1712_0 := h1712c.1
                        have p1712_1 := h1712c.2.1
                        have p1712_2 := h1712c.2.2.1
                        have p1712_3 := h1712c.2.2.2
                        linarith only [h1, hlam, p1712_0]
                      · have p1712_0 := h1712c.1
                        have p1712_1 := h1712c.2.1
                        have p1712_2 := h1712c.2.2.1
                        have p1712_3 := h1712c.2.2.2
                        linarith only [h1, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1712_1, u1elo0]
                      · have p1712_0 := h1712c.1
                        have p1712_1 := h1712c.2.1
                        have p1712_2 := h1712c.2.2.1
                        have p1712_3 := h1712c.2.2.2
                        linarith only [hlam, p1712_0]
                      · have p1712_0 := h1712c.1
                        have p1712_1 := h1712c.2.1
                        have p1712_2 := h1712c.2.2.1
                        have p1712_3 := h1712c.2.2.2
                        linarith only [h1705, hlam, p1712_0]
                      · have p1712_0 := h1712c.1
                        have p1712_1 := h1712c.2.1
                        have p1712_2 := h1712c.2.2.1
                        have p1712_3 := h1712c.2.2.2
                        linarith only [h1, h1013, h1709, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1712_1]
                      · have p1712_0 := h1712c.1
                        have p1712_1 := h1712c.2.1
                        have p1712_2 := h1712c.2.2.1
                        have p1712_3 := h1712c.2.2.2
                        linarith only [h2, hlam, p1712_0]
                      · have p1712_0 := h1712c.1
                        have p1712_1 := h1712c.2.1
                        have p1712_2 := h1712c.2.2.1
                        have p1712_3 := h1712c.2.2.2
                        linarith only [h2, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1712_1, u1elo0]
                      · have p1712_0 := h1712c.1
                        have p1712_1 := h1712c.2.1
                        have p1712_2 := h1712c.2.2.1
                        have p1712_3 := h1712c.2.2.2
                        linarith only [h2, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1712_1, u1elo0]
                      · have p1712_0 := h1712c.1
                        have p1712_1 := h1712c.2.1
                        have p1712_2 := h1712c.2.2.1
                        have p1712_3 := h1712c.2.2.2
                        linarith only [hlam, p1712_0]
                      · have p1712_0 := h1712c.1
                        have p1712_1 := h1712c.2.1
                        have p1712_2 := h1712c.2.2.1
                        have p1712_3 := h1712c.2.2.2
                        linarith only [h1629, h2, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1712_1, u1elo0]
                      · have p1712_0 := h1712c.1
                        have p1712_1 := h1712c.2.1
                        have p1712_2 := h1712c.2.2.1
                        have p1712_3 := h1712c.2.2.2
                        linarith only [h3, hlam, p1712_0]
                      · have p1712_0 := h1712c.1
                        have p1712_1 := h1712c.2.1
                        have p1712_2 := h1712c.2.2.1
                        have p1712_3 := h1712c.2.2.2
                        linarith only [h3, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1712_1, u1elo0]
                      · have p1712_0 := h1712c.1
                        have p1712_1 := h1712c.2.1
                        have p1712_2 := h1712c.2.2.1
                        have p1712_3 := h1712c.2.2.2
                        linarith only [h1707, hlam, p1712_0]
                      · have p1712_0 := h1712c.1
                        have p1712_1 := h1712c.2.1
                        have p1712_2 := h1712c.2.2.1
                        have p1712_3 := h1712c.2.2.2
                        linarith only [h1708, hlam, p1712_0]
                      · have p1712_0 := h1712c.1
                        have p1712_1 := h1712c.2.1
                        have p1712_2 := h1712c.2.2.1
                        have p1712_3 := h1712c.2.2.2
                        linarith only [hlam, p1712_0]
                    · linarith only [h1013, h1497, h1711, hlam]
                  · linarith only [h1, h1013, h1707, h1708, h1709, h1710, h2, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h1752 | h1752
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1753 | h1753
                    · rcases h1bigk with h1754c | h1754c | h1754c | h1754c | h1754c | h1754c | h1754c | h1754c | h1754c | h1754c | h1754c | h1754c | h1754c | h1754c | h1754c | h1754c | h1754c | h1754c | h1754c | h1754c | h1754c | h1754c | h1754c | h1754c | h1754c
                      · have p1754_0 := h1754c.1
                        have p1754_1 := h1754c.2.1
                        have p1754_2 := h1754c.2.2.1
                        have p1754_3 := h1754c.2.2.2
                        linarith only [hlam, p1754_0]
                      · have p1754_0 := h1754c.1
                        have p1754_1 := h1754c.2.1
                        have p1754_2 := h1754c.2.2.1
                        have p1754_3 := h1754c.2.2.2
                        rcases p1754_3 (m.d 0 1) (by simp) with h1756 | h1756
                        · rcases p1754_3 (m.d 1 2) (by simp) with h1757 | h1757
                          · linarith only [h1757, hlam, p1754_0]
                          · rcases p1754_3 (m.d 1 3) (by simp) with h1759 | h1759
                            · linarith only [h1, h1759, hlam]
                            · linarith only [h1498, h1759, hlam]
                        · linarith only [h1756, hlam, p1754_0]
                      · have p1754_0 := h1754c.1
                        have p1754_1 := h1754c.2.1
                        have p1754_2 := h1754c.2.2.1
                        have p1754_3 := h1754c.2.2.2
                        linarith only [h1707, hc35, hlam, hphi, ht01, ht0b, ht5b, p1754_1, u1elo0]
                      · have p1754_0 := h1754c.1
                        have p1754_1 := h1754c.2.1
                        have p1754_2 := h1754c.2.2.1
                        have p1754_3 := h1754c.2.2.2
                        linarith only [h1705, h1707, h1753, hc45, hlam, hphi, ht01, ht0b, ht5b, p1754_1, u1elo0]
                      · have p1754_0 := h1754c.1
                        have p1754_1 := h1754c.2.1
                        have p1754_2 := h1754c.2.2.1
                        have p1754_3 := h1754c.2.2.2
                        rcases p1754_3 (m.d 0 1) (by simp) with h1765 | h1765
                        · rcases p1754_3 (m.d 1 2) (by simp) with h1766 | h1766
                          · linarith only [h0, h1766, hlam]
                          · rcases p1754_3 (m.d 1 3) (by simp) with h1768 | h1768
                            · linarith only [h1, h1768, hlam]
                            · linarith only [h1707, h1768, hlam]
                        · linarith only [h1765, hlam, p1754_0]
                      · have p1754_0 := h1754c.1
                        have p1754_1 := h1754c.2.1
                        have p1754_2 := h1754c.2.2.1
                        have p1754_3 := h1754c.2.2.2
                        linarith only [h0, hlam, p1754_0]
                      · have p1754_0 := h1754c.1
                        have p1754_1 := h1754c.2.1
                        have p1754_2 := h1754c.2.2.1
                        have p1754_3 := h1754c.2.2.2
                        linarith only [hlam, p1754_0]
                      · have p1754_0 := h1754c.1
                        have p1754_1 := h1754c.2.1
                        have p1754_2 := h1754c.2.2.1
                        have p1754_3 := h1754c.2.2.2
                        linarith only [h1498, hlam, p1754_1]
                      · have p1754_0 := h1754c.1
                        have p1754_1 := h1754c.2.1
                        have p1754_2 := h1754c.2.2.1
                        have p1754_3 := h1754c.2.2.2
                        linarith only [h1627, hlam, p1754_1]
                      · have p1754_0 := h1754c.1
                        have p1754_1 := h1754c.2.1
                        have p1754_2 := h1754c.2.2.1
                        have p1754_3 := h1754c.2.2.2
                        linarith only [h1629, hlam, p1754_1]
                      · have p1754_0 := h1754c.1
                        have p1754_1 := h1754c.2.1
                        have p1754_2 := h1754c.2.2.1
                        have p1754_3 := h1754c.2.2.2
                        linarith only [h1, hlam, p1754_0]
                      · have p1754_0 := h1754c.1
                        have p1754_1 := h1754c.2.1
                        have p1754_2 := h1754c.2.2.1
                        have p1754_3 := h1754c.2.2.2
                        linarith only [h1, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1754_1, u1elo0]
                      · have p1754_0 := h1754c.1
                        have p1754_1 := h1754c.2.1
                        have p1754_2 := h1754c.2.2.1
                        have p1754_3 := h1754c.2.2.2
                        linarith only [hlam, p1754_0]
                      · have p1754_0 := h1754c.1
                        have p1754_1 := h1754c.2.1
                        have p1754_2 := h1754c.2.2.1
                        have p1754_3 := h1754c.2.2.2
                        linarith only [h1705, hlam, p1754_0]
                      · have p1754_0 := h1754c.1
                        have p1754_1 := h1754c.2.1
                        have p1754_2 := h1754c.2.2.1
                        have p1754_3 := h1754c.2.2.2
                        linarith only [h1, hc15, hlam, hphi, ht01, ht0b, ht5b, p1754_1, u1elo0]
                      · have p1754_0 := h1754c.1
                        have p1754_1 := h1754c.2.1
                        have p1754_2 := h1754c.2.2.1
                        have p1754_3 := h1754c.2.2.2
                        linarith only [h2, hlam, p1754_0]
                      · have p1754_0 := h1754c.1
                        have p1754_1 := h1754c.2.1
                        have p1754_2 := h1754c.2.2.1
                        have p1754_3 := h1754c.2.2.2
                        linarith only [h2, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1754_1, u1elo0]
                      · have p1754_0 := h1754c.1
                        have p1754_1 := h1754c.2.1
                        have p1754_2 := h1754c.2.2.1
                        have p1754_3 := h1754c.2.2.2
                        linarith only [h2, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1754_1, u1elo0]
                      · have p1754_0 := h1754c.1
                        have p1754_1 := h1754c.2.1
                        have p1754_2 := h1754c.2.2.1
                        have p1754_3 := h1754c.2.2.2
                        linarith only [hlam, p1754_0]
                      · have p1754_0 := h1754c.1
                        have p1754_1 := h1754c.2.1
                        have p1754_2 := h1754c.2.2.1
                        have p1754_3 := h1754c.2.2.2
                        linarith only [h1629, h2, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1754_1, u1elo0]
                      · have p1754_0 := h1754c.1
                        have p1754_1 := h1754c.2.1
                        have p1754_2 := h1754c.2.2.1
                        have p1754_3 := h1754c.2.2.2
                        linarith only [h3, hlam, p1754_0]
                      · have p1754_0 := h1754c.1
                        have p1754_1 := h1754c.2.1
                        have p1754_2 := h1754c.2.2.1
                        have p1754_3 := h1754c.2.2.2
                        linarith only [h3, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1754_1, u1elo0]
                      · have p1754_0 := h1754c.1
                        have p1754_1 := h1754c.2.1
                        have p1754_2 := h1754c.2.2.1
                        have p1754_3 := h1754c.2.2.2
                        linarith only [h1707, hlam, p1754_0]
                      · have p1754_0 := h1754c.1
                        have p1754_1 := h1754c.2.1
                        have p1754_2 := h1754c.2.2.1
                        have p1754_3 := h1754c.2.2.2
                        linarith only [h1708, hlam, p1754_0]
                      · have p1754_0 := h1754c.1
                        have p1754_1 := h1754c.2.1
                        have p1754_2 := h1754c.2.2.1
                        have p1754_3 := h1754c.2.2.2
                        linarith only [hlam, p1754_0]
                    · linarith only [h1497, h1709, h1753, h4, hlam]
                  · linarith only [h1708, h1752, h2, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
              · linarith only [h1497, h1705, h1707, h1708, h2, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1795 | h1795
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1796 | h1796
                · rcases m.htr 2 4 5 (by decide) (by decide) with h1797 | h1797
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1798 | h1798
                    · rcases h1bigk with h1799c | h1799c | h1799c | h1799c | h1799c | h1799c | h1799c | h1799c | h1799c | h1799c | h1799c | h1799c | h1799c | h1799c | h1799c | h1799c | h1799c | h1799c | h1799c | h1799c | h1799c | h1799c | h1799c | h1799c | h1799c
                      · have p1799_0 := h1799c.1
                        have p1799_1 := h1799c.2.1
                        have p1799_2 := h1799c.2.2.1
                        have p1799_3 := h1799c.2.2.2
                        linarith only [hlam, p1799_0]
                      · have p1799_0 := h1799c.1
                        have p1799_1 := h1799c.2.1
                        have p1799_2 := h1799c.2.2.1
                        have p1799_3 := h1799c.2.2.2
                        rcases p1799_3 (m.d 0 1) (by simp) with h1801 | h1801
                        · rcases p1799_3 (m.d 1 2) (by simp) with h1802 | h1802
                          · linarith only [h1802, hlam, p1799_0]
                          · rcases p1799_3 (m.d 1 3) (by simp) with h1804 | h1804
                            · linarith only [h1, h1804, hlam]
                            · linarith only [h1498, h1804, hlam]
                        · linarith only [h1801, hlam, p1799_0]
                      · have p1799_0 := h1799c.1
                        have p1799_1 := h1799c.2.1
                        have p1799_2 := h1799c.2.2.1
                        have p1799_3 := h1799c.2.2.2
                        rcases p1799_3 (m.d 0 1) (by simp) with h1808 | h1808
                        · rcases p1799_3 (m.d 1 2) (by simp) with h1809 | h1809
                          · linarith only [h0, h1809, hlam]
                          · rcases p1799_3 (m.d 1 3) (by simp) with h1811 | h1811
                            · linarith only [h1811, hlam, p1799_0]
                            · rcases p1799_3 (m.d 1 4) (by simp) with h1813 | h1813
                              · linarith only [h1813, h2, hlam]
                              · linarith only [h1705, h1813, hlam]
                        · linarith only [h1808, hlam, p1799_0]
                      · have p1799_0 := h1799c.1
                        have p1799_1 := h1799c.2.1
                        have p1799_2 := h1799c.2.2.1
                        have p1799_3 := h1799c.2.2.2
                        linarith only [h1795, hc45, hlam, hphi, ht01, ht0b, ht5b, p1799_1, u1elo0]
                      · have p1799_0 := h1799c.1
                        have p1799_1 := h1799c.2.1
                        have p1799_2 := h1799c.2.2.1
                        have p1799_3 := h1799c.2.2.2
                        rcases p1799_3 (m.d 0 1) (by simp) with h1818 | h1818
                        · rcases p1799_3 (m.d 1 2) (by simp) with h1819 | h1819
                          · linarith only [h0, h1819, hlam]
                          · rcases p1799_3 (m.d 1 3) (by simp) with h1821 | h1821
                            · linarith only [h1, h1821, hlam]
                            · rcases p1799_3 (m.d 1 4) (by simp) with h1823 | h1823
                              · linarith only [h1823, h2, hlam]
                              · linarith only [h1795, h1823, hlam]
                        · linarith only [h1818, hlam, p1799_0]
                      · have p1799_0 := h1799c.1
                        have p1799_1 := h1799c.2.1
                        have p1799_2 := h1799c.2.2.1
                        have p1799_3 := h1799c.2.2.2
                        linarith only [h0, hlam, p1799_0]
                      · have p1799_0 := h1799c.1
                        have p1799_1 := h1799c.2.1
                        have p1799_2 := h1799c.2.2.1
                        have p1799_3 := h1799c.2.2.2
                        linarith only [hlam, p1799_0]
                      · have p1799_0 := h1799c.1
                        have p1799_1 := h1799c.2.1
                        have p1799_2 := h1799c.2.2.1
                        have p1799_3 := h1799c.2.2.2
                        linarith only [h1498, hlam, p1799_1]
                      · have p1799_0 := h1799c.1
                        have p1799_1 := h1799c.2.1
                        have p1799_2 := h1799c.2.2.1
                        have p1799_3 := h1799c.2.2.2
                        linarith only [h1627, hlam, p1799_1]
                      · have p1799_0 := h1799c.1
                        have p1799_1 := h1799c.2.1
                        have p1799_2 := h1799c.2.2.1
                        have p1799_3 := h1799c.2.2.2
                        linarith only [h1629, hlam, p1799_1]
                      · have p1799_0 := h1799c.1
                        have p1799_1 := h1799c.2.1
                        have p1799_2 := h1799c.2.2.1
                        have p1799_3 := h1799c.2.2.2
                        linarith only [h1, hlam, p1799_0]
                      · have p1799_0 := h1799c.1
                        have p1799_1 := h1799c.2.1
                        have p1799_2 := h1799c.2.2.1
                        have p1799_3 := h1799c.2.2.2
                        linarith only [h1707, hc12, hc35, hlam, hphi, ht23, p1799_1]
                      · have p1799_0 := h1799c.1
                        have p1799_1 := h1799c.2.1
                        have p1799_2 := h1799c.2.2.1
                        have p1799_3 := h1799c.2.2.2
                        linarith only [hlam, p1799_0]
                      · have p1799_0 := h1799c.1
                        have p1799_1 := h1799c.2.1
                        have p1799_2 := h1799c.2.2.1
                        have p1799_3 := h1799c.2.2.2
                        linarith only [h1705, hlam, p1799_0]
                      · have p1799_0 := h1799c.1
                        have p1799_1 := h1799c.2.1
                        have p1799_2 := h1799c.2.2.1
                        have p1799_3 := h1799c.2.2.2
                        linarith only [h1707, hlam, p1799_1]
                      · have p1799_0 := h1799c.1
                        have p1799_1 := h1799c.2.1
                        have p1799_2 := h1799c.2.2.1
                        have p1799_3 := h1799c.2.2.2
                        linarith only [h2, hlam, p1799_0]
                      · have p1799_0 := h1799c.1
                        have p1799_1 := h1799c.2.1
                        have p1799_2 := h1799c.2.2.1
                        have p1799_3 := h1799c.2.2.2
                        linarith only [h2, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1799_1, u1elo0]
                      · have p1799_0 := h1799c.1
                        have p1799_1 := h1799c.2.1
                        have p1799_2 := h1799c.2.2.1
                        have p1799_3 := h1799c.2.2.2
                        linarith only [h2, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1799_1, u1elo0]
                      · have p1799_0 := h1799c.1
                        have p1799_1 := h1799c.2.1
                        have p1799_2 := h1799c.2.2.1
                        have p1799_3 := h1799c.2.2.2
                        linarith only [hlam, p1799_0]
                      · have p1799_0 := h1799c.1
                        have p1799_1 := h1799c.2.1
                        have p1799_2 := h1799c.2.2.1
                        have p1799_3 := h1799c.2.2.2
                        linarith only [h2, hc15, hlam, hphi, ht01, ht0b, ht5b, p1799_1, u1elo0]
                      · have p1799_0 := h1799c.1
                        have p1799_1 := h1799c.2.1
                        have p1799_2 := h1799c.2.2.1
                        have p1799_3 := h1799c.2.2.2
                        linarith only [h3, hlam, p1799_0]
                      · have p1799_0 := h1799c.1
                        have p1799_1 := h1799c.2.1
                        have p1799_2 := h1799c.2.2.1
                        have p1799_3 := h1799c.2.2.2
                        linarith only [h3, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1799_1, u1elo0]
                      · have p1799_0 := h1799c.1
                        have p1799_1 := h1799c.2.1
                        have p1799_2 := h1799c.2.2.1
                        have p1799_3 := h1799c.2.2.2
                        linarith only [h1498, h3, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1799_1, u1elo0]
                      · have p1799_0 := h1799c.1
                        have p1799_1 := h1799c.2.1
                        have p1799_2 := h1799c.2.2.1
                        have p1799_3 := h1799c.2.2.2
                        linarith only [h1795, hlam, p1799_0]
                      · have p1799_0 := h1799c.1
                        have p1799_1 := h1799c.2.1
                        have p1799_2 := h1799c.2.2.1
                        have p1799_3 := h1799c.2.2.2
                        linarith only [hlam, p1799_0]
                    · linarith only [h1013, h1497, h1798, hlam]
                  · linarith only [h1013, h1795, h1796, h1797, h2, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h1849 | h1849
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1850 | h1850
                    · rcases h1bigk with h1851c | h1851c | h1851c | h1851c | h1851c | h1851c | h1851c | h1851c | h1851c | h1851c | h1851c | h1851c | h1851c | h1851c | h1851c | h1851c | h1851c | h1851c | h1851c | h1851c | h1851c | h1851c | h1851c | h1851c | h1851c
                      · have p1851_0 := h1851c.1
                        have p1851_1 := h1851c.2.1
                        have p1851_2 := h1851c.2.2.1
                        have p1851_3 := h1851c.2.2.2
                        linarith only [hlam, p1851_0]
                      · have p1851_0 := h1851c.1
                        have p1851_1 := h1851c.2.1
                        have p1851_2 := h1851c.2.2.1
                        have p1851_3 := h1851c.2.2.2
                        rcases p1851_3 (m.d 0 1) (by simp) with h1853 | h1853
                        · rcases p1851_3 (m.d 1 2) (by simp) with h1854 | h1854
                          · linarith only [h1854, hlam, p1851_0]
                          · rcases p1851_3 (m.d 1 3) (by simp) with h1856 | h1856
                            · linarith only [h1, h1856, hlam]
                            · linarith only [h1498, h1856, hlam]
                        · linarith only [h1853, hlam, p1851_0]
                      · have p1851_0 := h1851c.1
                        have p1851_1 := h1851c.2.1
                        have p1851_2 := h1851c.2.2.1
                        have p1851_3 := h1851c.2.2.2
                        rcases p1851_3 (m.d 0 1) (by simp) with h1860 | h1860
                        · rcases p1851_3 (m.d 1 2) (by simp) with h1861 | h1861
                          · linarith only [h0, h1861, hlam]
                          · rcases p1851_3 (m.d 1 3) (by simp) with h1863 | h1863
                            · linarith only [h1863, hlam, p1851_0]
                            · rcases p1851_3 (m.d 1 4) (by simp) with h1865 | h1865
                              · linarith only [h1865, h2, hlam]
                              · linarith only [h1705, h1865, hlam]
                        · linarith only [h1860, hlam, p1851_0]
                      · have p1851_0 := h1851c.1
                        have p1851_1 := h1851c.2.1
                        have p1851_2 := h1851c.2.2.1
                        have p1851_3 := h1851c.2.2.2
                        linarith only [h1795, hc45, hlam, hphi, ht01, ht0b, ht5b, p1851_1, u1elo0]
                      · have p1851_0 := h1851c.1
                        have p1851_1 := h1851c.2.1
                        have p1851_2 := h1851c.2.2.1
                        have p1851_3 := h1851c.2.2.2
                        rcases p1851_3 (m.d 0 1) (by simp) with h1870 | h1870
                        · rcases p1851_3 (m.d 1 2) (by simp) with h1871 | h1871
                          · linarith only [h0, h1871, hlam]
                          · rcases p1851_3 (m.d 1 3) (by simp) with h1873 | h1873
                            · linarith only [h1, h1873, hlam]
                            · rcases p1851_3 (m.d 1 4) (by simp) with h1875 | h1875
                              · linarith only [h1875, h2, hlam]
                              · linarith only [h1795, h1875, hlam]
                        · linarith only [h1870, hlam, p1851_0]
                      · have p1851_0 := h1851c.1
                        have p1851_1 := h1851c.2.1
                        have p1851_2 := h1851c.2.2.1
                        have p1851_3 := h1851c.2.2.2
                        linarith only [h0, hlam, p1851_0]
                      · have p1851_0 := h1851c.1
                        have p1851_1 := h1851c.2.1
                        have p1851_2 := h1851c.2.2.1
                        have p1851_3 := h1851c.2.2.2
                        linarith only [hlam, p1851_0]
                      · have p1851_0 := h1851c.1
                        have p1851_1 := h1851c.2.1
                        have p1851_2 := h1851c.2.2.1
                        have p1851_3 := h1851c.2.2.2
                        linarith only [h1498, hlam, p1851_1]
                      · have p1851_0 := h1851c.1
                        have p1851_1 := h1851c.2.1
                        have p1851_2 := h1851c.2.2.1
                        have p1851_3 := h1851c.2.2.2
                        linarith only [h1627, hlam, p1851_1]
                      · have p1851_0 := h1851c.1
                        have p1851_1 := h1851c.2.1
                        have p1851_2 := h1851c.2.2.1
                        have p1851_3 := h1851c.2.2.2
                        linarith only [h1629, hlam, p1851_1]
                      · have p1851_0 := h1851c.1
                        have p1851_1 := h1851c.2.1
                        have p1851_2 := h1851c.2.2.1
                        have p1851_3 := h1851c.2.2.2
                        linarith only [h1, hlam, p1851_0]
                      · have p1851_0 := h1851c.1
                        have p1851_1 := h1851c.2.1
                        have p1851_2 := h1851c.2.2.1
                        have p1851_3 := h1851c.2.2.2
                        linarith only [h1, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1851_1, u1elo0]
                      · have p1851_0 := h1851c.1
                        have p1851_1 := h1851c.2.1
                        have p1851_2 := h1851c.2.2.1
                        have p1851_3 := h1851c.2.2.2
                        linarith only [hlam, p1851_0]
                      · have p1851_0 := h1851c.1
                        have p1851_1 := h1851c.2.1
                        have p1851_2 := h1851c.2.2.1
                        have p1851_3 := h1851c.2.2.2
                        linarith only [h1705, hlam, p1851_0]
                      · have p1851_0 := h1851c.1
                        have p1851_1 := h1851c.2.1
                        have p1851_2 := h1851c.2.2.1
                        have p1851_3 := h1851c.2.2.2
                        linarith only [h1707, hlam, p1851_1]
                      · have p1851_0 := h1851c.1
                        have p1851_1 := h1851c.2.1
                        have p1851_2 := h1851c.2.2.1
                        have p1851_3 := h1851c.2.2.2
                        linarith only [h2, hlam, p1851_0]
                      · have p1851_0 := h1851c.1
                        have p1851_1 := h1851c.2.1
                        have p1851_2 := h1851c.2.2.1
                        have p1851_3 := h1851c.2.2.2
                        linarith only [h2, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1851_1, u1elo0]
                      · have p1851_0 := h1851c.1
                        have p1851_1 := h1851c.2.1
                        have p1851_2 := h1851c.2.2.1
                        have p1851_3 := h1851c.2.2.2
                        linarith only [h2, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1851_1, u1elo0]
                      · have p1851_0 := h1851c.1
                        have p1851_1 := h1851c.2.1
                        have p1851_2 := h1851c.2.2.1
                        have p1851_3 := h1851c.2.2.2
                        linarith only [hlam, p1851_0]
                      · have p1851_0 := h1851c.1
                        have p1851_1 := h1851c.2.1
                        have p1851_2 := h1851c.2.2.1
                        have p1851_3 := h1851c.2.2.2
                        linarith only [h2, hc15, hlam, hphi, ht01, ht0b, ht5b, p1851_1, u1elo0]
                      · have p1851_0 := h1851c.1
                        have p1851_1 := h1851c.2.1
                        have p1851_2 := h1851c.2.2.1
                        have p1851_3 := h1851c.2.2.2
                        linarith only [h3, hlam, p1851_0]
                      · have p1851_0 := h1851c.1
                        have p1851_1 := h1851c.2.1
                        have p1851_2 := h1851c.2.2.1
                        have p1851_3 := h1851c.2.2.2
                        linarith only [h3, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1851_1, u1elo0]
                      · have p1851_0 := h1851c.1
                        have p1851_1 := h1851c.2.1
                        have p1851_2 := h1851c.2.2.1
                        have p1851_3 := h1851c.2.2.2
                        linarith only [h1498, h3, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1851_1, u1elo0]
                      · have p1851_0 := h1851c.1
                        have p1851_1 := h1851c.2.1
                        have p1851_2 := h1851c.2.2.1
                        have p1851_3 := h1851c.2.2.2
                        linarith only [h1795, hlam, p1851_0]
                      · have p1851_0 := h1851c.1
                        have p1851_1 := h1851c.2.1
                        have p1851_2 := h1851c.2.2.1
                        have p1851_3 := h1851c.2.2.2
                        linarith only [hlam, p1851_0]
                    · linarith only [h1498, h1796, h1850, hc12, hc45, hlam, hphi, ht23, ht34]
                  · linarith only [h1795, h1849, h2, h4, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1901 | h1901
                · linarith only [h1013, h1497, h1627, h1795, h1901, hc12, hc23, hlam, hphi]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h1903 | h1903
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1904 | h1904
                    · rcases h1bigk with h1905c | h1905c | h1905c | h1905c | h1905c | h1905c | h1905c | h1905c | h1905c | h1905c | h1905c | h1905c | h1905c | h1905c | h1905c | h1905c | h1905c | h1905c | h1905c | h1905c | h1905c | h1905c | h1905c | h1905c | h1905c
                      · have p1905_0 := h1905c.1
                        have p1905_1 := h1905c.2.1
                        have p1905_2 := h1905c.2.2.1
                        have p1905_3 := h1905c.2.2.2
                        linarith only [hlam, p1905_0]
                      · have p1905_0 := h1905c.1
                        have p1905_1 := h1905c.2.1
                        have p1905_2 := h1905c.2.2.1
                        have p1905_3 := h1905c.2.2.2
                        rcases p1905_3 (m.d 0 1) (by simp) with h1907 | h1907
                        · rcases p1905_3 (m.d 1 2) (by simp) with h1908 | h1908
                          · linarith only [h1908, hlam, p1905_0]
                          · rcases p1905_3 (m.d 1 3) (by simp) with h1910 | h1910
                            · linarith only [h1, h1910, hlam]
                            · linarith only [h1498, h1910, hlam]
                        · linarith only [h1907, hlam, p1905_0]
                      · have p1905_0 := h1905c.1
                        have p1905_1 := h1905c.2.1
                        have p1905_2 := h1905c.2.2.1
                        have p1905_3 := h1905c.2.2.2
                        rcases p1905_3 (m.d 0 1) (by simp) with h1914 | h1914
                        · rcases p1905_3 (m.d 1 2) (by simp) with h1915 | h1915
                          · linarith only [h0, h1915, hlam]
                          · rcases p1905_3 (m.d 1 3) (by simp) with h1917 | h1917
                            · linarith only [h1917, hlam, p1905_0]
                            · rcases p1905_3 (m.d 1 4) (by simp) with h1919 | h1919
                              · linarith only [h1919, h2, hlam]
                              · linarith only [h1705, h1919, hlam]
                        · linarith only [h1914, hlam, p1905_0]
                      · have p1905_0 := h1905c.1
                        have p1905_1 := h1905c.2.1
                        have p1905_2 := h1905c.2.2.1
                        have p1905_3 := h1905c.2.2.2
                        rcases p1905_3 (m.d 0 1) (by simp) with h1923 | h1923
                        · rcases p1905_3 (m.d 1 2) (by simp) with h1924 | h1924
                          · linarith only [h0, h1924, hlam]
                          · rcases p1905_3 (m.d 1 3) (by simp) with h1926 | h1926
                            · linarith only [h1, h1926, hlam]
                            · rcases p1905_3 (m.d 1 4) (by simp) with h1928 | h1928
                              · linarith only [h1928, hlam, p1905_0]
                              · rcases p1905_3 (m.d 1 5) (by simp) with h1930 | h1930
                                · linarith only [h1930, h3, hlam]
                                · linarith only [h1795, h1930, hlam]
                        · linarith only [h1923, hlam, p1905_0]
                      · have p1905_0 := h1905c.1
                        have p1905_1 := h1905c.2.1
                        have p1905_2 := h1905c.2.2.1
                        have p1905_3 := h1905c.2.2.2
                        rcases p1905_3 (m.d 0 1) (by simp) with h1934 | h1934
                        · rcases p1905_3 (m.d 1 2) (by simp) with h1935 | h1935
                          · linarith only [h0, h1935, hlam]
                          · rcases p1905_3 (m.d 1 3) (by simp) with h1937 | h1937
                            · linarith only [h1, h1937, hlam]
                            · rcases p1905_3 (m.d 1 4) (by simp) with h1939 | h1939
                              · linarith only [h1939, h2, hlam]
                              · rcases p1905_3 (m.d 1 5) (by simp) with h1941 | h1941
                                · linarith only [h1941, hlam, p1905_0]
                                · rcases h4bigk with h1943c | h1943c | h1943c | h1943c | h1943c | h1943c | h1943c | h1943c | h1943c | h1943c | h1943c | h1943c | h1943c | h1943c | h1943c | h1943c | h1943c | h1943c | h1943c | h1943c | h1943c | h1943c | h1943c | h1943c | h1943c
                                  · have p1943_0 := h1943c.1
                                    have p1943_1 := h1943c.2.1
                                    have p1943_2 := h1943c.2.2.1
                                    have p1943_3 := h1943c.2.2.2
                                    linarith only [hlam, p1943_0]
                                  · have p1943_0 := h1943c.1
                                    have p1943_1 := h1943c.2.1
                                    have p1943_2 := h1943c.2.2.1
                                    have p1943_3 := h1943c.2.2.2
                                    rcases p1943_3 (m.d 0 4) (by simp) with h1945 | h1945
                                    · rcases p1943_3 (m.d 1 4) (by simp) with h1946 | h1946
                                      · linarith only [h1946, h2, hlam]
                                      · rcases p1943_3 (m.d 2 4) (by simp) with h1948 | h1948
                                        · rcases p1943_3 (m.d 3 4) (by simp) with h1949 | h1949
                                          · rcases p1943_3 (m.d 4 5) (by simp) with h1950 | h1950
                                            · linarith only [h1497, h1950, hlam]
                                            · linarith only [h1795, h1950, hlam]
                                          · linarith only [h1705, h1949, hlam]
                                        · linarith only [h1627, h1948, hlam]
                                    · linarith only [h1945, h2, hlam]
                                  · have p1943_0 := h1943c.1
                                    have p1943_1 := h1943c.2.1
                                    have p1943_2 := h1943c.2.2.1
                                    have p1943_3 := h1943c.2.2.2
                                    linarith only [h4, hlam, p1943_1]
                                  · have p1943_0 := h1943c.1
                                    have p1943_1 := h1943c.2.1
                                    have p1943_2 := h1943c.2.2.1
                                    have p1943_3 := h1943c.2.2.2
                                    linarith only [h1013, hlam, p1943_1]
                                  · have p1943_0 := h1943c.1
                                    have p1943_1 := h1943c.2.1
                                    have p1943_2 := h1943c.2.2.1
                                    have p1943_3 := h1943c.2.2.2
                                    linarith only [h1498, h1705, h1795, h2, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1943_1, u1elo0]
                                  · have p1943_0 := h1943c.1
                                    have p1943_1 := h1943c.2.1
                                    have p1943_2 := h1943c.2.2.1
                                    have p1943_3 := h1943c.2.2.2
                                    linarith only [h2, hlam, p1943_0]
                                  · have p1943_0 := h1943c.1
                                    have p1943_1 := h1943c.2.1
                                    have p1943_2 := h1943c.2.2.1
                                    have p1943_3 := h1943c.2.2.2
                                    linarith only [hlam, p1943_0]
                                  · have p1943_0 := h1943c.1
                                    have p1943_1 := h1943c.2.1
                                    have p1943_2 := h1943c.2.2.1
                                    have p1943_3 := h1943c.2.2.2
                                    linarith only [h1627, hlam, p1943_1]
                                  · have p1943_0 := h1943c.1
                                    have p1943_1 := h1943c.2.1
                                    have p1943_2 := h1943c.2.2.1
                                    have p1943_3 := h1943c.2.2.2
                                    linarith only [h1705, hlam, p1943_1]
                                  · have p1943_0 := h1943c.1
                                    have p1943_1 := h1943c.2.1
                                    have p1943_2 := h1943c.2.2.1
                                    have p1943_3 := h1943c.2.2.2
                                    linarith only [h1795, hlam, p1943_0]
                                  · have p1943_0 := h1943c.1
                                    have p1943_1 := h1943c.2.1
                                    have p1943_2 := h1943c.2.2.1
                                    have p1943_3 := h1943c.2.2.2
                                    linarith only [h1497, h1498, h1705, h1795, h1901, hc12, hc34, hlam, hphi, ht23, p1943_1]
                                  · have p1943_0 := h1943c.1
                                    have p1943_1 := h1943c.2.1
                                    have p1943_2 := h1943c.2.2.1
                                    have p1943_3 := h1943c.2.2.2
                                    rcases p1943_3 (m.d 0 4) (by simp) with h1965 | h1965
                                    · linarith only [h1965, h4, hlam]
                                    · linarith only [h1965, h2, hlam]
                                  · have p1943_0 := h1943c.1
                                    have p1943_1 := h1943c.2.1
                                    have p1943_2 := h1943c.2.2.1
                                    have p1943_3 := h1943c.2.2.2
                                    linarith only [hlam, p1943_0]
                                  · have p1943_0 := h1943c.1
                                    have p1943_1 := h1943c.2.1
                                    have p1943_2 := h1943c.2.2.1
                                    have p1943_3 := h1943c.2.2.2
                                    linarith only [h1901, hlam, p1943_1]
                                  · have p1943_0 := h1943c.1
                                    have p1943_1 := h1943c.2.1
                                    have p1943_2 := h1943c.2.2.1
                                    have p1943_3 := h1943c.2.2.2
                                    linarith only [h1498, h1705, h1795, h1901, hc12, hc34, hlam, hphi, ht23, p1943_1]
                                  · have p1943_0 := h1943c.1
                                    have p1943_1 := h1943c.2.1
                                    have p1943_2 := h1943c.2.2.1
                                    have p1943_3 := h1943c.2.2.2
                                    linarith only [h1497, h1498, h1705, h1795, hc12, hc34, hlam, hphi, ht23, p1943_1]
                                  · have p1943_0 := h1943c.1
                                    have p1943_1 := h1943c.2.1
                                    have p1943_2 := h1943c.2.2.1
                                    have p1943_3 := h1943c.2.2.2
                                    rcases p1943_3 (m.d 0 4) (by simp) with h1972 | h1972
                                    · linarith only [h1013, h1972, hlam]
                                    · linarith only [h1972, h2, hlam]
                                  · have p1943_0 := h1943c.1
                                    have p1943_1 := h1943c.2.1
                                    have p1943_2 := h1943c.2.2.1
                                    have p1943_3 := h1943c.2.2.2
                                    linarith only [h0, h4, hc12, hc34, hlam, hphi, ht23, p1943_1]
                                  · have p1943_0 := h1943c.1
                                    have p1943_1 := h1943c.2.1
                                    have p1943_2 := h1943c.2.2.1
                                    have p1943_3 := h1943c.2.2.2
                                    linarith only [hlam, p1943_0]
                                  · have p1943_0 := h1943c.1
                                    have p1943_1 := h1943c.2.1
                                    have p1943_2 := h1943c.2.2.1
                                    have p1943_3 := h1943c.2.2.2
                                    linarith only [h1498, h1705, h1795, hc12, hc34, hlam, hphi, ht23, p1943_1]
                                  · have p1943_0 := h1943c.1
                                    have p1943_1 := h1943c.2.1
                                    have p1943_2 := h1943c.2.2.1
                                    have p1943_3 := h1943c.2.2.2
                                    linarith only [h1497, hlam, p1943_0]
                                  · have p1943_0 := h1943c.1
                                    have p1943_1 := h1943c.2.1
                                    have p1943_2 := h1943c.2.2.1
                                    have p1943_3 := h1943c.2.2.2
                                    linarith only [h1497, h1498, h1705, h4, hc12, hc24, hlam, hphi, p1943_1]
                                  · have p1943_0 := h1943c.1
                                    have p1943_1 := h1943c.2.1
                                    have p1943_2 := h1943c.2.2.1
                                    have p1943_3 := h1943c.2.2.2
                                    linarith only [h1903, hlam, p1943_0]
                                  · have p1943_0 := h1943c.1
                                    have p1943_1 := h1943c.2.1
                                    have p1943_2 := h1943c.2.2.1
                                    have p1943_3 := h1943c.2.2.2
                                    linarith only [h1904, hlam, p1943_0]
                                  · have p1943_0 := h1943c.1
                                    have p1943_1 := h1943c.2.1
                                    have p1943_2 := h1943c.2.2.1
                                    have p1943_3 := h1943c.2.2.2
                                    linarith only [hlam, p1943_0]
                        · linarith only [h1934, hlam, p1905_0]
                      · have p1905_0 := h1905c.1
                        have p1905_1 := h1905c.2.1
                        have p1905_2 := h1905c.2.2.1
                        have p1905_3 := h1905c.2.2.2
                        linarith only [h0, hlam, p1905_0]
                      · have p1905_0 := h1905c.1
                        have p1905_1 := h1905c.2.1
                        have p1905_2 := h1905c.2.2.1
                        have p1905_3 := h1905c.2.2.2
                        linarith only [hlam, p1905_0]
                      · have p1905_0 := h1905c.1
                        have p1905_1 := h1905c.2.1
                        have p1905_2 := h1905c.2.2.1
                        have p1905_3 := h1905c.2.2.2
                        linarith only [h1498, hlam, p1905_1]
                      · have p1905_0 := h1905c.1
                        have p1905_1 := h1905c.2.1
                        have p1905_2 := h1905c.2.2.1
                        have p1905_3 := h1905c.2.2.2
                        linarith only [h1627, hlam, p1905_1]
                      · have p1905_0 := h1905c.1
                        have p1905_1 := h1905c.2.1
                        have p1905_2 := h1905c.2.2.1
                        have p1905_3 := h1905c.2.2.2
                        linarith only [h1629, hlam, p1905_1]
                      · have p1905_0 := h1905c.1
                        have p1905_1 := h1905c.2.1
                        have p1905_2 := h1905c.2.2.1
                        have p1905_3 := h1905c.2.2.2
                        linarith only [h1, hlam, p1905_0]
                      · have p1905_0 := h1905c.1
                        have p1905_1 := h1905c.2.1
                        have p1905_2 := h1905c.2.2.1
                        have p1905_3 := h1905c.2.2.2
                        linarith only [h1, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1905_1, u1elo0]
                      · have p1905_0 := h1905c.1
                        have p1905_1 := h1905c.2.1
                        have p1905_2 := h1905c.2.2.1
                        have p1905_3 := h1905c.2.2.2
                        linarith only [hlam, p1905_0]
                      · have p1905_0 := h1905c.1
                        have p1905_1 := h1905c.2.1
                        have p1905_2 := h1905c.2.2.1
                        have p1905_3 := h1905c.2.2.2
                        linarith only [h1705, hlam, p1905_0]
                      · have p1905_0 := h1905c.1
                        have p1905_1 := h1905c.2.1
                        have p1905_2 := h1905c.2.2.1
                        have p1905_3 := h1905c.2.2.2
                        linarith only [h1707, hlam, p1905_1]
                      · have p1905_0 := h1905c.1
                        have p1905_1 := h1905c.2.1
                        have p1905_2 := h1905c.2.2.1
                        have p1905_3 := h1905c.2.2.2
                        linarith only [h2, hlam, p1905_0]
                      · have p1905_0 := h1905c.1
                        have p1905_1 := h1905c.2.1
                        have p1905_2 := h1905c.2.2.1
                        have p1905_3 := h1905c.2.2.2
                        linarith only [h2, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1905_1, u1elo0]
                      · have p1905_0 := h1905c.1
                        have p1905_1 := h1905c.2.1
                        have p1905_2 := h1905c.2.2.1
                        have p1905_3 := h1905c.2.2.2
                        linarith only [h2, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1905_1, u1elo0]
                      · have p1905_0 := h1905c.1
                        have p1905_1 := h1905c.2.1
                        have p1905_2 := h1905c.2.2.1
                        have p1905_3 := h1905c.2.2.2
                        linarith only [hlam, p1905_0]
                      · have p1905_0 := h1905c.1
                        have p1905_1 := h1905c.2.1
                        have p1905_2 := h1905c.2.2.1
                        have p1905_3 := h1905c.2.2.2
                        linarith only [h1795, hlam, p1905_1]
                      · have p1905_0 := h1905c.1
                        have p1905_1 := h1905c.2.1
                        have p1905_2 := h1905c.2.2.1
                        have p1905_3 := h1905c.2.2.2
                        linarith only [h3, hlam, p1905_0]
                      · have p1905_0 := h1905c.1
                        have p1905_1 := h1905c.2.1
                        have p1905_2 := h1905c.2.2.1
                        have p1905_3 := h1905c.2.2.2
                        linarith only [h3, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1905_1, u1elo0]
                      · have p1905_0 := h1905c.1
                        have p1905_1 := h1905c.2.1
                        have p1905_2 := h1905c.2.2.1
                        have p1905_3 := h1905c.2.2.2
                        linarith only [h1498, h3, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1905_1, u1elo0]
                      · have p1905_0 := h1905c.1
                        have p1905_1 := h1905c.2.1
                        have p1905_2 := h1905c.2.2.1
                        have p1905_3 := h1905c.2.2.2
                        linarith only [h1497, h1795, h2, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p1905_1, u1elo0]
                      · have p1905_0 := h1905c.1
                        have p1905_1 := h1905c.2.1
                        have p1905_2 := h1905c.2.2.1
                        have p1905_3 := h1905c.2.2.2
                        linarith only [hlam, p1905_0]
                    · linarith only [h1497, h1901, h1904, h2, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                  · linarith only [h1497, h1903, h4, hlam]
  · rcases m.htr 1 2 3 (by decide) (by decide) with h2006 | h2006
    · rcases m.htr 1 2 4 (by decide) (by decide) with h2007 | h2007
      · linarith only [h0, h2007, h4, hlam]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h2009 | h2009
        · rcases m.htr 1 3 4 (by decide) (by decide) with h2010 | h2010
          · linarith only [h1, h1013, h2010, hlam]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h2012 | h2012
            · rcases m.htr 1 4 5 (by decide) (by decide) with h2013 | h2013
              · linarith only [h1497, h2, h2013, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
              · linarith only [h2006, h2007, h2012, h2013, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h2016 | h2016
              · linarith only [h1013, h1497, h2, h2016, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
              · linarith only [h2007, h2009, h2016, hlam]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h2019 | h2019
          · linarith only [h0, h1, h1013, h2006, h2019, h4, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h2021 | h2021
            · linarith only [h2006, h2009, h2021, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h2023 | h2023
              · linarith only [h1497, h2, h2006, h2009, h2023, h3, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h2025 | h2025
                · linarith only [h1013, h2006, h2025, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h2027 | h2027
                  · linarith only [h0, h1497, h2006, h2025, h2027, h4, hc23, hc34, hlam, hphi]
                  · linarith only [h0, h2006, h2027, h4, hc23, hc45, hlam, hphi, ht34]
    · rcases m.htr 1 2 4 (by decide) (by decide) with h2030 | h2030
      · linarith only [h2006, h2030, h4, hc02, hc23, hlam, hphi]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h2032 | h2032
        · rcases m.htr 1 3 4 (by decide) (by decide) with h2033 | h2033
          · linarith only [h1, h1013, h2033, hlam]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h2035 | h2035
            · rcases m.htr 1 4 5 (by decide) (by decide) with h2036 | h2036
              · linarith only [h1497, h2, h2036, hlam]
              · linarith only [h2030, h2032, h2036, hlam]
            · linarith only [h2006, h2032, h2035, hlam]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h2040 | h2040
          · linarith only [h1, h1013, h2040, hlam]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h2042 | h2042
            · rcases m.htr 1 4 5 (by decide) (by decide) with h2043 | h2043
              · linarith only [h1, h1013, h1497, h2042, h2043, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo3]
              · linarith only [h2040, h2042, h2043, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h2046 | h2046
              · linarith only [h0, h1497, h2, h2046, h4, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h2048 | h2048
                · rcases m.htr 2 4 5 (by decide) (by decide) with h2049 | h2049
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2050 | h2050
                    · linarith only [h1497, h2048, h2050, h4, hc02, hc23, hlam, hphi]
                    · linarith only [h1, h1013, h2006, h2049, h2050, hc12, hc24, hlam, hphi]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2053 | h2053
                    · linarith only [h0, h2049, h2053, h4, hc12, hc34, hlam, hphi, ht23]
                    · rcases h1bigk with h2055c | h2055c | h2055c | h2055c | h2055c | h2055c | h2055c | h2055c | h2055c | h2055c | h2055c | h2055c | h2055c | h2055c | h2055c | h2055c | h2055c | h2055c | h2055c | h2055c | h2055c | h2055c | h2055c | h2055c | h2055c
                      · have p2055_0 := h2055c.1
                        have p2055_1 := h2055c.2.1
                        have p2055_2 := h2055c.2.2.1
                        have p2055_3 := h2055c.2.2.2
                        linarith only [hlam, p2055_0]
                      · have p2055_0 := h2055c.1
                        have p2055_1 := h2055c.2.1
                        have p2055_2 := h2055c.2.2.1
                        have p2055_3 := h2055c.2.2.2
                        rcases p2055_3 (m.d 0 1) (by simp) with h2057 | h2057
                        · rcases p2055_3 (m.d 1 2) (by simp) with h2058 | h2058
                          · linarith only [h2058, hlam, p2055_0]
                          · rcases p2055_3 (m.d 1 3) (by simp) with h2060 | h2060
                            · linarith only [h1, h2060, hlam]
                            · linarith only [h2006, h2060, hlam]
                        · linarith only [h2057, hlam, p2055_0]
                      · have p2055_0 := h2055c.1
                        have p2055_1 := h2055c.2.1
                        have p2055_2 := h2055c.2.2.1
                        have p2055_3 := h2055c.2.2.2
                        rcases p2055_3 (m.d 0 1) (by simp) with h2064 | h2064
                        · rcases p2055_3 (m.d 1 2) (by simp) with h2065 | h2065
                          · linarith only [h0, h2065, hlam]
                          · rcases p2055_3 (m.d 1 3) (by simp) with h2067 | h2067
                            · linarith only [h2067, hlam, p2055_0]
                            · rcases p2055_3 (m.d 1 4) (by simp) with h2069 | h2069
                              · linarith only [h2, h2069, hlam]
                              · linarith only [h2040, h2069, hlam]
                        · linarith only [h2064, hlam, p2055_0]
                      · have p2055_0 := h2055c.1
                        have p2055_1 := h2055c.2.1
                        have p2055_2 := h2055c.2.2.1
                        have p2055_3 := h2055c.2.2.2
                        rcases p2055_3 (m.d 0 1) (by simp) with h2073 | h2073
                        · rcases p2055_3 (m.d 1 2) (by simp) with h2074 | h2074
                          · linarith only [h0, h2074, hlam]
                          · rcases p2055_3 (m.d 1 3) (by simp) with h2076 | h2076
                            · linarith only [h1, h2076, hlam]
                            · rcases p2055_3 (m.d 1 4) (by simp) with h2078 | h2078
                              · linarith only [h2078, hlam, p2055_0]
                              · rcases p2055_3 (m.d 1 5) (by simp) with h2080 | h2080
                                · linarith only [h2080, h3, hlam]
                                · linarith only [h2046, h2080, hlam]
                        · linarith only [h2073, hlam, p2055_0]
                      · have p2055_0 := h2055c.1
                        have p2055_1 := h2055c.2.1
                        have p2055_2 := h2055c.2.2.1
                        have p2055_3 := h2055c.2.2.2
                        rcases p2055_3 (m.d 0 1) (by simp) with h2084 | h2084
                        · rcases p2055_3 (m.d 1 2) (by simp) with h2085 | h2085
                          · linarith only [h0, h2085, hlam]
                          · rcases p2055_3 (m.d 1 3) (by simp) with h2087 | h2087
                            · linarith only [h1, h2087, hlam]
                            · rcases p2055_3 (m.d 1 4) (by simp) with h2089 | h2089
                              · linarith only [h2, h2089, hlam]
                              · rcases p2055_3 (m.d 1 5) (by simp) with h2091 | h2091
                                · linarith only [h2091, hlam, p2055_0]
                                · rcases h4bigk with h2093c | h2093c | h2093c | h2093c | h2093c | h2093c | h2093c | h2093c | h2093c | h2093c | h2093c | h2093c | h2093c | h2093c | h2093c | h2093c | h2093c | h2093c | h2093c | h2093c | h2093c | h2093c | h2093c | h2093c | h2093c
                                  · have p2093_0 := h2093c.1
                                    have p2093_1 := h2093c.2.1
                                    have p2093_2 := h2093c.2.2.1
                                    have p2093_3 := h2093c.2.2.2
                                    linarith only [hlam, p2093_0]
                                  · have p2093_0 := h2093c.1
                                    have p2093_1 := h2093c.2.1
                                    have p2093_2 := h2093c.2.2.1
                                    have p2093_3 := h2093c.2.2.2
                                    linarith only [h2006, h2040, h2049, h4, hc12, hc45, hlam, hphi, ht23, ht34, p2093_1]
                                  · have p2093_0 := h2093c.1
                                    have p2093_1 := h2093c.2.1
                                    have p2093_2 := h2093c.2.2.1
                                    have p2093_3 := h2093c.2.2.2
                                    linarith only [h4, hlam, p2093_1]
                                  · have p2093_0 := h2093c.1
                                    have p2093_1 := h2093c.2.1
                                    have p2093_2 := h2093c.2.2.1
                                    have p2093_3 := h2093c.2.2.2
                                    linarith only [h1013, hlam, p2093_1]
                                  · have p2093_0 := h2093c.1
                                    have p2093_1 := h2093c.2.1
                                    have p2093_2 := h2093c.2.2.1
                                    have p2093_3 := h2093c.2.2.2
                                    linarith only [h1497, hlam, p2093_0]
                                  · have p2093_0 := h2093c.1
                                    have p2093_1 := h2093c.2.1
                                    have p2093_2 := h2093c.2.2.1
                                    have p2093_3 := h2093c.2.2.2
                                    linarith only [h2, hlam, p2093_0]
                                  · have p2093_0 := h2093c.1
                                    have p2093_1 := h2093c.2.1
                                    have p2093_2 := h2093c.2.2.1
                                    have p2093_3 := h2093c.2.2.2
                                    linarith only [hlam, p2093_0]
                                  · have p2093_0 := h2093c.1
                                    have p2093_1 := h2093c.2.1
                                    have p2093_2 := h2093c.2.2.1
                                    have p2093_3 := h2093c.2.2.2
                                    linarith only [h2030, hlam, p2093_1]
                                  · have p2093_0 := h2093c.1
                                    have p2093_1 := h2093c.2.1
                                    have p2093_2 := h2093c.2.2.1
                                    have p2093_3 := h2093c.2.2.2
                                    linarith only [h2040, hlam, p2093_1]
                                  · have p2093_0 := h2093c.1
                                    have p2093_1 := h2093c.2.1
                                    have p2093_2 := h2093c.2.2.1
                                    have p2093_3 := h2093c.2.2.2
                                    linarith only [h2046, hlam, p2093_0]
                                  · have p2093_0 := h2093c.1
                                    have p2093_1 := h2093c.2.1
                                    have p2093_2 := h2093c.2.2.1
                                    have p2093_3 := h2093c.2.2.2
                                    linarith only [h2049, hc04, hc45, hlam, hphi, p2093_1]
                                  · have p2093_0 := h2093c.1
                                    have p2093_1 := h2093c.2.1
                                    have p2093_2 := h2093c.2.2.1
                                    have p2093_3 := h2093c.2.2.2
                                    linarith only [h2006, h2040, h2049, hc12, hc45, hlam, hphi, ht23, ht34, p2093_1]
                                  · have p2093_0 := h2093c.1
                                    have p2093_1 := h2093c.2.1
                                    have p2093_2 := h2093c.2.2.1
                                    have p2093_3 := h2093c.2.2.2
                                    linarith only [hlam, p2093_0]
                                  · have p2093_0 := h2093c.1
                                    have p2093_1 := h2093c.2.1
                                    have p2093_2 := h2093c.2.2.1
                                    have p2093_3 := h2093c.2.2.2
                                    linarith only [h1, h1013, h2006, h2049, hc12, hc45, hlam, hphi, ht23, ht34, p2093_1]
                                  · have p2093_0 := h2093c.1
                                    have p2093_1 := h2093c.2.1
                                    have p2093_2 := h2093c.2.2.1
                                    have p2093_3 := h2093c.2.2.2
                                    linarith only [h2049, hlam, p2093_0]
                                  · have p2093_0 := h2093c.1
                                    have p2093_1 := h2093c.2.1
                                    have p2093_2 := h2093c.2.2.1
                                    have p2093_3 := h2093c.2.2.2
                                    linarith only [h2, h2006, h2040, h2048, hc12, hc23, hlam, hphi, p2093_1]
                                  · have p2093_0 := h2093c.1
                                    have p2093_1 := h2093c.2.1
                                    have p2093_2 := h2093c.2.2.1
                                    have p2093_3 := h2093c.2.2.2
                                    linarith only [h2006, h2040, h2048, hc12, hc23, hlam, hphi, p2093_1]
                                  · have p2093_0 := h2093c.1
                                    have p2093_1 := h2093c.2.1
                                    have p2093_2 := h2093c.2.2.1
                                    have p2093_3 := h2093c.2.2.2
                                    linarith only [h2048, hlam, p2093_0]
                                  · have p2093_0 := h2093c.1
                                    have p2093_1 := h2093c.2.1
                                    have p2093_2 := h2093c.2.2.1
                                    have p2093_3 := h2093c.2.2.2
                                    linarith only [hlam, p2093_0]
                                  · have p2093_0 := h2093c.1
                                    have p2093_1 := h2093c.2.1
                                    have p2093_2 := h2093c.2.2.1
                                    have p2093_3 := h2093c.2.2.2
                                    linarith only [h2053, hlam, p2093_0]
                                  · have p2093_0 := h2093c.1
                                    have p2093_1 := h2093c.2.1
                                    have p2093_2 := h2093c.2.2.1
                                    have p2093_3 := h2093c.2.2.2
                                    rcases p2093_3 (m.d 0 4) (by simp) with h2114 | h2114
                                    · linarith only [h2114, hlam, p2093_0]
                                    · rcases p2093_3 (m.d 1 4) (by simp) with h2116 | h2116
                                      · linarith only [h2046, h2116, hlam]
                                      · rcases p2093_3 (m.d 2 4) (by simp) with h2118 | h2118
                                        · linarith only [h2049, h2118, hlam]
                                        · linarith only [h2118, h4, hlam]
                                  · have p2093_0 := h2093c.1
                                    have p2093_1 := h2093c.2.1
                                    have p2093_2 := h2093c.2.2.1
                                    have p2093_3 := h2093c.2.2.2
                                    rcases p2093_3 (m.d 0 4) (by simp) with h2121 | h2121
                                    · linarith only [h1497, h2121, hlam]
                                    · linarith only [h2, h2121, hlam]
                                  · have p2093_0 := h2093c.1
                                    have p2093_1 := h2093c.2.1
                                    have p2093_2 := h2093c.2.2.1
                                    have p2093_3 := h2093c.2.2.2
                                    linarith only [h0, h4, hc12, hc45, hlam, hphi, ht23, ht34, p2093_1]
                                  · have p2093_0 := h2093c.1
                                    have p2093_1 := h2093c.2.1
                                    have p2093_2 := h2093c.2.2.1
                                    have p2093_3 := h2093c.2.2.2
                                    linarith only [h1, h1013, h2006, hc12, hc45, hlam, hphi, ht23, ht34, p2093_1]
                                  · have p2093_0 := h2093c.1
                                    have p2093_1 := h2093c.2.1
                                    have p2093_2 := h2093c.2.2.1
                                    have p2093_3 := h2093c.2.2.2
                                    linarith only [hlam, p2093_0]
                        · linarith only [h2084, hlam, p2055_0]
                      · have p2055_0 := h2055c.1
                        have p2055_1 := h2055c.2.1
                        have p2055_2 := h2055c.2.2.1
                        have p2055_3 := h2055c.2.2.2
                        linarith only [h0, hlam, p2055_0]
                      · have p2055_0 := h2055c.1
                        have p2055_1 := h2055c.2.1
                        have p2055_2 := h2055c.2.2.1
                        have p2055_3 := h2055c.2.2.2
                        linarith only [hlam, p2055_0]
                      · have p2055_0 := h2055c.1
                        have p2055_1 := h2055c.2.1
                        have p2055_2 := h2055c.2.2.1
                        have p2055_3 := h2055c.2.2.2
                        linarith only [h2006, hlam, p2055_1]
                      · have p2055_0 := h2055c.1
                        have p2055_1 := h2055c.2.1
                        have p2055_2 := h2055c.2.2.1
                        have p2055_3 := h2055c.2.2.2
                        linarith only [h2030, hlam, p2055_1]
                      · have p2055_0 := h2055c.1
                        have p2055_1 := h2055c.2.1
                        have p2055_2 := h2055c.2.2.1
                        have p2055_3 := h2055c.2.2.2
                        linarith only [h2032, hlam, p2055_1]
                      · have p2055_0 := h2055c.1
                        have p2055_1 := h2055c.2.1
                        have p2055_2 := h2055c.2.2.1
                        have p2055_3 := h2055c.2.2.2
                        linarith only [h1, hlam, p2055_0]
                      · have p2055_0 := h2055c.1
                        have p2055_1 := h2055c.2.1
                        have p2055_2 := h2055c.2.2.1
                        have p2055_3 := h2055c.2.2.2
                        linarith only [h1, h1013, h2048, hc12, hc24, hlam, hphi, p2055_1]
                      · have p2055_0 := h2055c.1
                        have p2055_1 := h2055c.2.1
                        have p2055_2 := h2055c.2.2.1
                        have p2055_3 := h2055c.2.2.2
                        linarith only [hlam, p2055_0]
                      · have p2055_0 := h2055c.1
                        have p2055_1 := h2055c.2.1
                        have p2055_2 := h2055c.2.2.1
                        have p2055_3 := h2055c.2.2.2
                        linarith only [h2040, hlam, p2055_0]
                      · have p2055_0 := h2055c.1
                        have p2055_1 := h2055c.2.1
                        have p2055_2 := h2055c.2.2.1
                        have p2055_3 := h2055c.2.2.2
                        linarith only [h2042, hlam, p2055_1]
                      · have p2055_0 := h2055c.1
                        have p2055_1 := h2055c.2.1
                        have p2055_2 := h2055c.2.2.1
                        have p2055_3 := h2055c.2.2.2
                        linarith only [h2, hlam, p2055_0]
                      · have p2055_0 := h2055c.1
                        have p2055_1 := h2055c.2.1
                        have p2055_2 := h2055c.2.2.1
                        have p2055_3 := h2055c.2.2.2
                        linarith only [h2046, h3, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2055_1, u1elo0]
                      · have p2055_0 := h2055c.1
                        have p2055_1 := h2055c.2.1
                        have p2055_2 := h2055c.2.2.1
                        have p2055_3 := h2055c.2.2.2
                        linarith only [h2046, h3, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2055_1, u1elo0]
                      · have p2055_0 := h2055c.1
                        have p2055_1 := h2055c.2.1
                        have p2055_2 := h2055c.2.2.1
                        have p2055_3 := h2055c.2.2.2
                        linarith only [hlam, p2055_0]
                      · have p2055_0 := h2055c.1
                        have p2055_1 := h2055c.2.1
                        have p2055_2 := h2055c.2.2.1
                        have p2055_3 := h2055c.2.2.2
                        linarith only [h2046, hlam, p2055_1]
                      · have p2055_0 := h2055c.1
                        have p2055_1 := h2055c.2.1
                        have p2055_2 := h2055c.2.2.1
                        have p2055_3 := h2055c.2.2.2
                        linarith only [h3, hlam, p2055_0]
                      · have p2055_0 := h2055c.1
                        have p2055_1 := h2055c.2.1
                        have p2055_2 := h2055c.2.2.1
                        have p2055_3 := h2055c.2.2.2
                        linarith only [h3, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2055_1, u1elo0]
                      · have p2055_0 := h2055c.1
                        have p2055_1 := h2055c.2.1
                        have p2055_2 := h2055c.2.2.1
                        have p2055_3 := h2055c.2.2.2
                        linarith only [h2006, h3, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2055_1, u1elo0]
                      · have p2055_0 := h2055c.1
                        have p2055_1 := h2055c.2.1
                        have p2055_2 := h2055c.2.2.1
                        have p2055_3 := h2055c.2.2.2
                        linarith only [h3, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p2055_1, u1elo0]
                      · have p2055_0 := h2055c.1
                        have p2055_1 := h2055c.2.1
                        have p2055_2 := h2055c.2.2.1
                        have p2055_3 := h2055c.2.2.2
                        linarith only [hlam, p2055_0]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h2148 | h2148
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2149 | h2149
                    · rcases h1bigk with h2150c | h2150c | h2150c | h2150c | h2150c | h2150c | h2150c | h2150c | h2150c | h2150c | h2150c | h2150c | h2150c | h2150c | h2150c | h2150c | h2150c | h2150c | h2150c | h2150c | h2150c | h2150c | h2150c | h2150c | h2150c
                      · have p2150_0 := h2150c.1
                        have p2150_1 := h2150c.2.1
                        have p2150_2 := h2150c.2.2.1
                        have p2150_3 := h2150c.2.2.2
                        linarith only [hlam, p2150_0]
                      · have p2150_0 := h2150c.1
                        have p2150_1 := h2150c.2.1
                        have p2150_2 := h2150c.2.2.1
                        have p2150_3 := h2150c.2.2.2
                        rcases p2150_3 (m.d 0 1) (by simp) with h2152 | h2152
                        · rcases p2150_3 (m.d 1 2) (by simp) with h2153 | h2153
                          · linarith only [h2153, hlam, p2150_0]
                          · rcases p2150_3 (m.d 1 3) (by simp) with h2155 | h2155
                            · linarith only [h1, h2155, hlam]
                            · linarith only [h2006, h2155, hlam]
                        · linarith only [h2152, hlam, p2150_0]
                      · have p2150_0 := h2150c.1
                        have p2150_1 := h2150c.2.1
                        have p2150_2 := h2150c.2.2.1
                        have p2150_3 := h2150c.2.2.2
                        rcases p2150_3 (m.d 0 1) (by simp) with h2159 | h2159
                        · rcases p2150_3 (m.d 1 2) (by simp) with h2160 | h2160
                          · linarith only [h0, h2160, hlam]
                          · rcases p2150_3 (m.d 1 3) (by simp) with h2162 | h2162
                            · linarith only [h2162, hlam, p2150_0]
                            · rcases p2150_3 (m.d 1 4) (by simp) with h2164 | h2164
                              · linarith only [h2, h2164, hlam]
                              · linarith only [h2040, h2164, hlam]
                        · linarith only [h2159, hlam, p2150_0]
                      · have p2150_0 := h2150c.1
                        have p2150_1 := h2150c.2.1
                        have p2150_2 := h2150c.2.2.1
                        have p2150_3 := h2150c.2.2.2
                        rcases p2150_3 (m.d 0 1) (by simp) with h2168 | h2168
                        · rcases p2150_3 (m.d 1 2) (by simp) with h2169 | h2169
                          · linarith only [h0, h2169, hlam]
                          · rcases p2150_3 (m.d 1 3) (by simp) with h2171 | h2171
                            · linarith only [h1, h2171, hlam]
                            · rcases p2150_3 (m.d 1 4) (by simp) with h2173 | h2173
                              · linarith only [h2173, hlam, p2150_0]
                              · rcases p2150_3 (m.d 1 5) (by simp) with h2175 | h2175
                                · linarith only [h2175, h3, hlam]
                                · linarith only [h2046, h2175, hlam]
                        · linarith only [h2168, hlam, p2150_0]
                      · have p2150_0 := h2150c.1
                        have p2150_1 := h2150c.2.1
                        have p2150_2 := h2150c.2.2.1
                        have p2150_3 := h2150c.2.2.2
                        rcases p2150_3 (m.d 0 1) (by simp) with h2179 | h2179
                        · rcases p2150_3 (m.d 1 2) (by simp) with h2180 | h2180
                          · linarith only [h0, h2180, hlam]
                          · rcases p2150_3 (m.d 1 3) (by simp) with h2182 | h2182
                            · linarith only [h1, h2182, hlam]
                            · rcases p2150_3 (m.d 1 4) (by simp) with h2184 | h2184
                              · linarith only [h2, h2184, hlam]
                              · rcases p2150_3 (m.d 1 5) (by simp) with h2186 | h2186
                                · linarith only [h2186, hlam, p2150_0]
                                · rcases h4bigk with h2188c | h2188c | h2188c | h2188c | h2188c | h2188c | h2188c | h2188c | h2188c | h2188c | h2188c | h2188c | h2188c | h2188c | h2188c | h2188c | h2188c | h2188c | h2188c | h2188c | h2188c | h2188c | h2188c | h2188c | h2188c
                                  · have p2188_0 := h2188c.1
                                    have p2188_1 := h2188c.2.1
                                    have p2188_2 := h2188c.2.2.1
                                    have p2188_3 := h2188c.2.2.2
                                    linarith only [hlam, p2188_0]
                                  · have p2188_0 := h2188c.1
                                    have p2188_1 := h2188c.2.1
                                    have p2188_2 := h2188c.2.2.1
                                    have p2188_3 := h2188c.2.2.2
                                    linarith only [h1497, h2006, h2040, h2048, h2148, hc12, hc34, hlam, hphi, ht23, p2188_1]
                                  · have p2188_0 := h2188c.1
                                    have p2188_1 := h2188c.2.1
                                    have p2188_2 := h2188c.2.2.1
                                    have p2188_3 := h2188c.2.2.2
                                    linarith only [h4, hlam, p2188_1]
                                  · have p2188_0 := h2188c.1
                                    have p2188_1 := h2188c.2.1
                                    have p2188_2 := h2188c.2.2.1
                                    have p2188_3 := h2188c.2.2.2
                                    linarith only [h1013, hlam, p2188_1]
                                  · have p2188_0 := h2188c.1
                                    have p2188_1 := h2188c.2.1
                                    have p2188_2 := h2188c.2.2.1
                                    have p2188_3 := h2188c.2.2.2
                                    linarith only [h1497, hlam, p2188_0]
                                  · have p2188_0 := h2188c.1
                                    have p2188_1 := h2188c.2.1
                                    have p2188_2 := h2188c.2.2.1
                                    have p2188_3 := h2188c.2.2.2
                                    linarith only [h2, hlam, p2188_0]
                                  · have p2188_0 := h2188c.1
                                    have p2188_1 := h2188c.2.1
                                    have p2188_2 := h2188c.2.2.1
                                    have p2188_3 := h2188c.2.2.2
                                    linarith only [hlam, p2188_0]
                                  · have p2188_0 := h2188c.1
                                    have p2188_1 := h2188c.2.1
                                    have p2188_2 := h2188c.2.2.1
                                    have p2188_3 := h2188c.2.2.2
                                    linarith only [h2030, hlam, p2188_1]
                                  · have p2188_0 := h2188c.1
                                    have p2188_1 := h2188c.2.1
                                    have p2188_2 := h2188c.2.2.1
                                    have p2188_3 := h2188c.2.2.2
                                    linarith only [h2040, hlam, p2188_1]
                                  · have p2188_0 := h2188c.1
                                    have p2188_1 := h2188c.2.1
                                    have p2188_2 := h2188c.2.2.1
                                    have p2188_3 := h2188c.2.2.2
                                    linarith only [h2046, hlam, p2188_0]
                                  · have p2188_0 := h2188c.1
                                    have p2188_1 := h2188c.2.1
                                    have p2188_2 := h2188c.2.2.1
                                    have p2188_3 := h2188c.2.2.2
                                    rcases p2188_3 (m.d 0 4) (by simp) with h2199 | h2199
                                    · linarith only [h2199, h4, hlam]
                                    · rcases p2188_3 (m.d 1 4) (by simp) with h2201 | h2201
                                      · linarith only [h2030, h2201, hlam]
                                      · rcases p2188_3 (m.d 2 4) (by simp) with h2203 | h2203
                                        · rcases p2188_3 (m.d 3 4) (by simp) with h2204 | h2204
                                          · rcases p2188_3 (m.d 4 5) (by simp) with h2205 | h2205
                                            · linarith only [h2148, h2205, hlam]
                                            · linarith only [h1497, h2205, hlam]
                                          · linarith only [h1013, h2204, hlam]
                                        · linarith only [h2203, h4, hlam]
                                  · have p2188_0 := h2188c.1
                                    have p2188_1 := h2188c.2.1
                                    have p2188_2 := h2188c.2.2.1
                                    have p2188_3 := h2188c.2.2.2
                                    rcases p2188_3 (m.d 0 4) (by simp) with h2210 | h2210
                                    · linarith only [h2210, h4, hlam]
                                    · linarith only [h2, h2210, hlam]
                                  · have p2188_0 := h2188c.1
                                    have p2188_1 := h2188c.2.1
                                    have p2188_2 := h2188c.2.2.1
                                    have p2188_3 := h2188c.2.2.2
                                    linarith only [hlam, p2188_0]
                                  · have p2188_0 := h2188c.1
                                    have p2188_1 := h2188c.2.1
                                    have p2188_2 := h2188c.2.2.1
                                    have p2188_3 := h2188c.2.2.2
                                    linarith only [h2048, hlam, p2188_1]
                                  · have p2188_0 := h2188c.1
                                    have p2188_1 := h2188c.2.1
                                    have p2188_2 := h2188c.2.2.1
                                    have p2188_3 := h2188c.2.2.2
                                    linarith only [h1497, h2, h2006, h2040, h2048, hc12, hc34, hlam, hphi, ht23, p2188_1]
                                  · have p2188_0 := h2188c.1
                                    have p2188_1 := h2188c.2.1
                                    have p2188_2 := h2188c.2.2.1
                                    have p2188_3 := h2188c.2.2.2
                                    rcases p2188_3 (m.d 0 4) (by simp) with h2216 | h2216
                                    · linarith only [h1013, h2216, hlam]
                                    · rcases p2188_3 (m.d 1 4) (by simp) with h2218 | h2218
                                      · linarith only [h2040, h2218, hlam]
                                      · rcases p2188_3 (m.d 2 4) (by simp) with h2220 | h2220
                                        · linarith only [h2048, h2220, hlam]
                                        · linarith only [h2220, h4, hlam]
                                  · have p2188_0 := h2188c.1
                                    have p2188_1 := h2188c.2.1
                                    have p2188_2 := h2188c.2.2.1
                                    have p2188_3 := h2188c.2.2.2
                                    rcases p2188_3 (m.d 0 4) (by simp) with h2223 | h2223
                                    · linarith only [h1013, h2223, hlam]
                                    · linarith only [h2, h2223, hlam]
                                  · have p2188_0 := h2188c.1
                                    have p2188_1 := h2188c.2.1
                                    have p2188_2 := h2188c.2.2.1
                                    have p2188_3 := h2188c.2.2.2
                                    linarith only [h0, h4, hc12, hc34, hlam, hphi, ht23, p2188_1]
                                  · have p2188_0 := h2188c.1
                                    have p2188_1 := h2188c.2.1
                                    have p2188_2 := h2188c.2.2.1
                                    have p2188_3 := h2188c.2.2.2
                                    linarith only [hlam, p2188_0]
                                  · have p2188_0 := h2188c.1
                                    have p2188_1 := h2188c.2.1
                                    have p2188_2 := h2188c.2.2.1
                                    have p2188_3 := h2188c.2.2.2
                                    linarith only [h1497, h2, h2006, h2040, hc12, hc34, hlam, hphi, ht23, p2188_1]
                                  · have p2188_0 := h2188c.1
                                    have p2188_1 := h2188c.2.1
                                    have p2188_2 := h2188c.2.2.1
                                    have p2188_3 := h2188c.2.2.2
                                    linarith only [h2, h2006, h2040, h2148, hc12, hc24, hlam, hphi, p2188_1]
                                  · have p2188_0 := h2188c.1
                                    have p2188_1 := h2188c.2.1
                                    have p2188_2 := h2188c.2.2.1
                                    have p2188_3 := h2188c.2.2.2
                                    linarith only [h2006, h2040, h2148, hc12, hc24, hlam, hphi, p2188_1]
                                  · have p2188_0 := h2188c.1
                                    have p2188_1 := h2188c.2.1
                                    have p2188_2 := h2188c.2.2.1
                                    have p2188_3 := h2188c.2.2.2
                                    linarith only [h2148, hlam, p2188_0]
                                  · have p2188_0 := h2188c.1
                                    have p2188_1 := h2188c.2.1
                                    have p2188_2 := h2188c.2.2.1
                                    have p2188_3 := h2188c.2.2.2
                                    linarith only [h2149, hlam, p2188_0]
                                  · have p2188_0 := h2188c.1
                                    have p2188_1 := h2188c.2.1
                                    have p2188_2 := h2188c.2.2.1
                                    have p2188_3 := h2188c.2.2.2
                                    linarith only [hlam, p2188_0]
                        · linarith only [h2179, hlam, p2150_0]
                      · have p2150_0 := h2150c.1
                        have p2150_1 := h2150c.2.1
                        have p2150_2 := h2150c.2.2.1
                        have p2150_3 := h2150c.2.2.2
                        linarith only [h0, hlam, p2150_0]
                      · have p2150_0 := h2150c.1
                        have p2150_1 := h2150c.2.1
                        have p2150_2 := h2150c.2.2.1
                        have p2150_3 := h2150c.2.2.2
                        linarith only [hlam, p2150_0]
                      · have p2150_0 := h2150c.1
                        have p2150_1 := h2150c.2.1
                        have p2150_2 := h2150c.2.2.1
                        have p2150_3 := h2150c.2.2.2
                        linarith only [h2006, hlam, p2150_1]
                      · have p2150_0 := h2150c.1
                        have p2150_1 := h2150c.2.1
                        have p2150_2 := h2150c.2.2.1
                        have p2150_3 := h2150c.2.2.2
                        linarith only [h2030, hlam, p2150_1]
                      · have p2150_0 := h2150c.1
                        have p2150_1 := h2150c.2.1
                        have p2150_2 := h2150c.2.2.1
                        have p2150_3 := h2150c.2.2.2
                        linarith only [h2032, hlam, p2150_1]
                      · have p2150_0 := h2150c.1
                        have p2150_1 := h2150c.2.1
                        have p2150_2 := h2150c.2.2.1
                        have p2150_3 := h2150c.2.2.2
                        linarith only [h1, hlam, p2150_0]
                      · have p2150_0 := h2150c.1
                        have p2150_1 := h2150c.2.1
                        have p2150_2 := h2150c.2.2.1
                        have p2150_3 := h2150c.2.2.2
                        linarith only [h1, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2150_1, u1elo0]
                      · have p2150_0 := h2150c.1
                        have p2150_1 := h2150c.2.1
                        have p2150_2 := h2150c.2.2.1
                        have p2150_3 := h2150c.2.2.2
                        linarith only [hlam, p2150_0]
                      · have p2150_0 := h2150c.1
                        have p2150_1 := h2150c.2.1
                        have p2150_2 := h2150c.2.2.1
                        have p2150_3 := h2150c.2.2.2
                        linarith only [h2040, hlam, p2150_0]
                      · have p2150_0 := h2150c.1
                        have p2150_1 := h2150c.2.1
                        have p2150_2 := h2150c.2.2.1
                        have p2150_3 := h2150c.2.2.2
                        linarith only [h2042, hlam, p2150_1]
                      · have p2150_0 := h2150c.1
                        have p2150_1 := h2150c.2.1
                        have p2150_2 := h2150c.2.2.1
                        have p2150_3 := h2150c.2.2.2
                        linarith only [h2, hlam, p2150_0]
                      · have p2150_0 := h2150c.1
                        have p2150_1 := h2150c.2.1
                        have p2150_2 := h2150c.2.2.1
                        have p2150_3 := h2150c.2.2.2
                        linarith only [h1497, h2, h2148, hc12, hc24, hlam, hphi, p2150_1]
                      · have p2150_0 := h2150c.1
                        have p2150_1 := h2150c.2.1
                        have p2150_2 := h2150c.2.2.1
                        have p2150_3 := h2150c.2.2.2
                        linarith only [h1497, h2, h2148, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2150_1]
                      · have p2150_0 := h2150c.1
                        have p2150_1 := h2150c.2.1
                        have p2150_2 := h2150c.2.2.1
                        have p2150_3 := h2150c.2.2.2
                        linarith only [hlam, p2150_0]
                      · have p2150_0 := h2150c.1
                        have p2150_1 := h2150c.2.1
                        have p2150_2 := h2150c.2.2.1
                        have p2150_3 := h2150c.2.2.2
                        linarith only [h2046, hlam, p2150_1]
                      · have p2150_0 := h2150c.1
                        have p2150_1 := h2150c.2.1
                        have p2150_2 := h2150c.2.2.1
                        have p2150_3 := h2150c.2.2.2
                        linarith only [h3, hlam, p2150_0]
                      · have p2150_0 := h2150c.1
                        have p2150_1 := h2150c.2.1
                        have p2150_2 := h2150c.2.2.1
                        have p2150_3 := h2150c.2.2.2
                        linarith only [h3, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2150_1, u1elo0]
                      · have p2150_0 := h2150c.1
                        have p2150_1 := h2150c.2.1
                        have p2150_2 := h2150c.2.2.1
                        have p2150_3 := h2150c.2.2.2
                        linarith only [h2006, h3, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2150_1, u1elo0]
                      · have p2150_0 := h2150c.1
                        have p2150_1 := h2150c.2.1
                        have p2150_2 := h2150c.2.2.1
                        have p2150_3 := h2150c.2.2.2
                        linarith only [h3, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p2150_1, u1elo0]
                      · have p2150_0 := h2150c.1
                        have p2150_1 := h2150c.2.1
                        have p2150_2 := h2150c.2.2.1
                        have p2150_3 := h2150c.2.2.2
                        linarith only [hlam, p2150_0]
                    · linarith only [h2048, h2148, h2149, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2256 | h2256
                    · linarith only [h0, h2148, h2256, h4, hc12, hc34, hlam, hphi, ht23]
                    · linarith only [h2006, h2048, h2256, hc12, hc45, hlam, hphi, ht23, ht34]

set_option maxHeartbeats 5672000 in
set_option maxHeartbeats 5672000 in
theorem r1l7_21_14_M_LI_L_I_s0_x0_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig2_7_M_LI m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
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
  have h1elo := hb1.1
  have h1bigk := hb1.2.2.2
  have h4bigk := hb4.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 3 4 (by decide) (by decide) with h1013 | h1013
  · exact r1l7_21_14_M_LI_L_I_s0_x0_x0_x0_x1_x0 m hb1 hb4 hg0 h1 h2 h3 h4 h1013
  · exact r1l7_21_14_M_LI_L_I_s0_x0_x0_x0_x1_x1 m hb1 hb4 hg0 h1 h2 h3 h4 h1013

set_option maxHeartbeats 5672000 in
set_option maxHeartbeats 5672000 in
theorem r1l7_21_14_M_LI_L_I_s0_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig2_7_M_LI m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
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
  have h1elo := hb1.1
  have h1bigk := hb1.2.2.2
  have h4bigk := hb4.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 2 4 (by decide) (by decide) with h4 | h4
  · exact r1l7_21_14_M_LI_L_I_s0_x0_x0_x0_x0 m hb1 hb4 hg0 h1 h2 h3 h4
  · exact r1l7_21_14_M_LI_L_I_s0_x0_x0_x0_x1 m hb1 hb4 hg0 h1 h2 h3 h4

end R2N4
