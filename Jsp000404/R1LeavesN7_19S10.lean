import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5434000 in
set_option maxHeartbeats 5434000 in
theorem r1l7_21_14_H_I_L_I_s6_x1_x0 (m : N7Model)
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg5235 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h6110 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h6504 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
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
  have h0 := hg0
  have h5235 := hg5235
  rcases m.htr 0 2 4 (by decide) (by decide) with h6505 | h6505
  · rcases m.htr 0 3 4 (by decide) (by decide) with h6506 | h6506
    · rcases m.htr 0 4 5 (by decide) (by decide) with h6507 | h6507
      · rcases m.htr 1 2 3 (by decide) (by decide) with h6508 | h6508
        · rcases m.htr 1 2 4 (by decide) (by decide) with h6509 | h6509
          · rcases m.htr 1 2 5 (by decide) (by decide) with h6510 | h6510
            · rcases m.htr 1 3 4 (by decide) (by decide) with h6511 | h6511
              · rcases m.htr 1 3 5 (by decide) (by decide) with h6512 | h6512
                · rcases m.htr 1 4 5 (by decide) (by decide) with h6513 | h6513
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h6514 | h6514
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h6515 | h6515
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h6516 | h6516
                        · rcases h1bigk with h6517c | h6517c | h6517c | h6517c | h6517c | h6517c | h6517c | h6517c | h6517c | h6517c | h6517c | h6517c | h6517c | h6517c | h6517c | h6517c | h6517c | h6517c | h6517c | h6517c | h6517c | h6517c | h6517c | h6517c | h6517c
                          · have p6517_0 := h6517c.1
                            have p6517_1 := h6517c.2.1
                            have p6517_2 := h6517c.2.2.1
                            have p6517_3 := h6517c.2.2.2
                            linarith only [hlam, p6517_0]
                          · have p6517_0 := h6517c.1
                            have p6517_1 := h6517c.2.1
                            have p6517_2 := h6517c.2.2.1
                            have p6517_3 := h6517c.2.2.2
                            linarith only [h0, hlam, p6517_0]
                          · have p6517_0 := h6517c.1
                            have p6517_1 := h6517c.2.1
                            have p6517_2 := h6517c.2.2.1
                            have p6517_3 := h6517c.2.2.2
                            linarith only [h5235, hlam, p6517_0]
                          · have p6517_0 := h6517c.1
                            have p6517_1 := h6517c.2.1
                            have p6517_2 := h6517c.2.2.1
                            have p6517_3 := h6517c.2.2.2
                            linarith only [h6110, hlam, p6517_0]
                          · have p6517_0 := h6517c.1
                            have p6517_1 := h6517c.2.1
                            have p6517_2 := h6517c.2.2.1
                            have p6517_3 := h6517c.2.2.2
                            linarith only [h6110, h6510, h6511, h6515, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p6517_1]
                          · have p6517_0 := h6517c.1
                            have p6517_1 := h6517c.2.1
                            have p6517_2 := h6517c.2.2.1
                            have p6517_3 := h6517c.2.2.2
                            linarith only [hc01, hc12, hlam, hphi, p6517_1]
                          · have p6517_0 := h6517c.1
                            have p6517_1 := h6517c.2.1
                            have p6517_2 := h6517c.2.2.1
                            have p6517_3 := h6517c.2.2.2
                            linarith only [hlam, p6517_0]
                          · have p6517_0 := h6517c.1
                            have p6517_1 := h6517c.2.1
                            have p6517_2 := h6517c.2.2.1
                            have p6517_3 := h6517c.2.2.2
                            linarith only [h5235, h6504, h6510, h6515, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p6517_1]
                          · have p6517_0 := h6517c.1
                            have p6517_1 := h6517c.2.1
                            have p6517_2 := h6517c.2.2.1
                            have p6517_3 := h6517c.2.2.2
                            linarith only [h6110, h6504, h6510, h6515, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p6517_1]
                          · have p6517_0 := h6517c.1
                            have p6517_1 := h6517c.2.1
                            have p6517_2 := h6517c.2.2.1
                            have p6517_3 := h6517c.2.2.2
                            rcases p6517_3 (m.d 0 1) (by simp) with h6527 | h6527
                            · linarith only [h0, h6527, hlam]
                            · linarith only [h6504, h6527, hlam]
                          · have p6517_0 := h6517c.1
                            have p6517_1 := h6517c.2.1
                            have p6517_2 := h6517c.2.2.1
                            have p6517_3 := h6517c.2.2.2
                            linarith only [h6504, h6510, h6515, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p6517_1]
                          · have p6517_0 := h6517c.1
                            have p6517_1 := h6517c.2.1
                            have p6517_2 := h6517c.2.2.1
                            have p6517_3 := h6517c.2.2.2
                            linarith only [h6508, hlam, p6517_0]
                          · have p6517_0 := h6517c.1
                            have p6517_1 := h6517c.2.1
                            have p6517_2 := h6517c.2.2.1
                            have p6517_3 := h6517c.2.2.2
                            linarith only [hlam, p6517_0]
                          · have p6517_0 := h6517c.1
                            have p6517_1 := h6517c.2.1
                            have p6517_2 := h6517c.2.2.1
                            have p6517_3 := h6517c.2.2.2
                            linarith only [h6110, h6504, h6508, h6510, h6515, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p6517_1]
                          · have p6517_0 := h6517c.1
                            have p6517_1 := h6517c.2.1
                            have p6517_2 := h6517c.2.2.1
                            have p6517_3 := h6517c.2.2.2
                            rcases p6517_3 (m.d 0 1) (by simp) with h6534 | h6534
                            · linarith only [h5235, h6534, hlam]
                            · linarith only [h6504, h6534, hlam]
                          · have p6517_0 := h6517c.1
                            have p6517_1 := h6517c.2.1
                            have p6517_2 := h6517c.2.2.1
                            have p6517_3 := h6517c.2.2.2
                            linarith only [h6504, h6510, h6515, hc14, hc45, hlam, hphi, ht01, ht0b, ht5b, p6517_1]
                          · have p6517_0 := h6517c.1
                            have p6517_1 := h6517c.2.1
                            have p6517_2 := h6517c.2.2.1
                            have p6517_3 := h6517c.2.2.2
                            linarith only [h6509, hlam, p6517_0]
                          · have p6517_0 := h6517c.1
                            have p6517_1 := h6517c.2.1
                            have p6517_2 := h6517c.2.2.1
                            have p6517_3 := h6517c.2.2.2
                            linarith only [h6511, hlam, p6517_1]
                          · have p6517_0 := h6517c.1
                            have p6517_1 := h6517c.2.1
                            have p6517_2 := h6517c.2.2.1
                            have p6517_3 := h6517c.2.2.2
                            linarith only [hlam, p6517_0]
                          · have p6517_0 := h6517c.1
                            have p6517_1 := h6517c.2.1
                            have p6517_2 := h6517c.2.2.1
                            have p6517_3 := h6517c.2.2.2
                            rcases p6517_3 (m.d 0 1) (by simp) with h6541 | h6541
                            · linarith only [h6110, h6541, hlam]
                            · linarith only [h6504, h6541, hlam]
                          · have p6517_0 := h6517c.1
                            have p6517_1 := h6517c.2.1
                            have p6517_2 := h6517c.2.2.1
                            have p6517_3 := h6517c.2.2.2
                            linarith only [h6504, hlam, p6517_0]
                          · have p6517_0 := h6517c.1
                            have p6517_1 := h6517c.2.1
                            have p6517_2 := h6517c.2.2.1
                            have p6517_3 := h6517c.2.2.2
                            linarith only [h6510, hlam, p6517_0]
                          · have p6517_0 := h6517c.1
                            have p6517_1 := h6517c.2.1
                            have p6517_2 := h6517c.2.2.1
                            have p6517_3 := h6517c.2.2.2
                            linarith only [h6512, hlam, p6517_0]
                          · have p6517_0 := h6517c.1
                            have p6517_1 := h6517c.2.1
                            have p6517_2 := h6517c.2.2.1
                            have p6517_3 := h6517c.2.2.2
                            linarith only [h6513, hlam, p6517_0]
                          · have p6517_0 := h6517c.1
                            have p6517_1 := h6517c.2.1
                            have p6517_2 := h6517c.2.2.1
                            have p6517_3 := h6517c.2.2.2
                            linarith only [hlam, p6517_0]
                        · rcases h1bigk with h6549c | h6549c | h6549c | h6549c | h6549c | h6549c | h6549c | h6549c | h6549c | h6549c | h6549c | h6549c | h6549c | h6549c | h6549c | h6549c | h6549c | h6549c | h6549c | h6549c | h6549c | h6549c | h6549c | h6549c | h6549c
                          · have p6549_0 := h6549c.1
                            have p6549_1 := h6549c.2.1
                            have p6549_2 := h6549c.2.2.1
                            have p6549_3 := h6549c.2.2.2
                            linarith only [hlam, p6549_0]
                          · have p6549_0 := h6549c.1
                            have p6549_1 := h6549c.2.1
                            have p6549_2 := h6549c.2.2.1
                            have p6549_3 := h6549c.2.2.2
                            linarith only [h0, hlam, p6549_0]
                          · have p6549_0 := h6549c.1
                            have p6549_1 := h6549c.2.1
                            have p6549_2 := h6549c.2.2.1
                            have p6549_3 := h6549c.2.2.2
                            linarith only [h5235, hlam, p6549_0]
                          · have p6549_0 := h6549c.1
                            have p6549_1 := h6549c.2.1
                            have p6549_2 := h6549c.2.2.1
                            have p6549_3 := h6549c.2.2.2
                            linarith only [h6110, hlam, p6549_0]
                          · have p6549_0 := h6549c.1
                            have p6549_1 := h6549c.2.1
                            have p6549_2 := h6549c.2.2.1
                            have p6549_3 := h6549c.2.2.2
                            linarith only [h6510, h6515, h6516, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p6549_1]
                          · have p6549_0 := h6549c.1
                            have p6549_1 := h6549c.2.1
                            have p6549_2 := h6549c.2.2.1
                            have p6549_3 := h6549c.2.2.2
                            linarith only [hc01, hc12, hlam, hphi, p6549_1]
                          · have p6549_0 := h6549c.1
                            have p6549_1 := h6549c.2.1
                            have p6549_2 := h6549c.2.2.1
                            have p6549_3 := h6549c.2.2.2
                            linarith only [hlam, p6549_0]
                          · have p6549_0 := h6549c.1
                            have p6549_1 := h6549c.2.1
                            have p6549_2 := h6549c.2.2.1
                            have p6549_3 := h6549c.2.2.2
                            linarith only [h5235, hc01, hc12, hlam, hphi, p6549_1]
                          · have p6549_0 := h6549c.1
                            have p6549_1 := h6549c.2.1
                            have p6549_2 := h6549c.2.2.1
                            have p6549_3 := h6549c.2.2.2
                            linarith only [h6110, h6504, h6510, h6515, h6516, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p6549_1]
                          · have p6549_0 := h6549c.1
                            have p6549_1 := h6549c.2.1
                            have p6549_2 := h6549c.2.2.1
                            have p6549_3 := h6549c.2.2.2
                            linarith only [h6510, h6515, h6516, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p6549_1]
                          · have p6549_0 := h6549c.1
                            have p6549_1 := h6549c.2.1
                            have p6549_2 := h6549c.2.2.1
                            have p6549_3 := h6549c.2.2.2
                            linarith only [h6504, h6510, h6515, h6516, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p6549_1]
                          · have p6549_0 := h6549c.1
                            have p6549_1 := h6549c.2.1
                            have p6549_2 := h6549c.2.2.1
                            have p6549_3 := h6549c.2.2.2
                            linarith only [h6508, hlam, p6549_0]
                          · have p6549_0 := h6549c.1
                            have p6549_1 := h6549c.2.1
                            have p6549_2 := h6549c.2.2.1
                            have p6549_3 := h6549c.2.2.2
                            linarith only [hlam, p6549_0]
                          · have p6549_0 := h6549c.1
                            have p6549_1 := h6549c.2.1
                            have p6549_2 := h6549c.2.2.1
                            have p6549_3 := h6549c.2.2.2
                            linarith only [h6110, h6504, h6508, h6510, h6515, h6516, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p6549_1]
                          · have p6549_0 := h6549c.1
                            have p6549_1 := h6549c.2.1
                            have p6549_2 := h6549c.2.2.1
                            have p6549_3 := h6549c.2.2.2
                            linarith only [h6508, h6510, h6515, h6516, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p6549_1]
                          · have p6549_0 := h6549c.1
                            have p6549_1 := h6549c.2.1
                            have p6549_2 := h6549c.2.2.1
                            have p6549_3 := h6549c.2.2.2
                            linarith only [h6504, h6510, h6515, h6516, hc14, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p6549_1]
                          · have p6549_0 := h6549c.1
                            have p6549_1 := h6549c.2.1
                            have p6549_2 := h6549c.2.2.1
                            have p6549_3 := h6549c.2.2.2
                            linarith only [h6509, hlam, p6549_0]
                          · have p6549_0 := h6549c.1
                            have p6549_1 := h6549c.2.1
                            have p6549_2 := h6549c.2.2.1
                            have p6549_3 := h6549c.2.2.2
                            linarith only [h6511, hlam, p6549_1]
                          · have p6549_0 := h6549c.1
                            have p6549_1 := h6549c.2.1
                            have p6549_2 := h6549c.2.2.1
                            have p6549_3 := h6549c.2.2.2
                            linarith only [hlam, p6549_0]
                          · have p6549_0 := h6549c.1
                            have p6549_1 := h6549c.2.1
                            have p6549_2 := h6549c.2.2.1
                            have p6549_3 := h6549c.2.2.2
                            linarith only [h6508, h6510, h6511, h6515, h6516, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p6549_1]
                          · have p6549_0 := h6549c.1
                            have p6549_1 := h6549c.2.1
                            have p6549_2 := h6549c.2.2.1
                            have p6549_3 := h6549c.2.2.2
                            linarith only [h6504, hlam, p6549_0]
                          · have p6549_0 := h6549c.1
                            have p6549_1 := h6549c.2.1
                            have p6549_2 := h6549c.2.2.1
                            have p6549_3 := h6549c.2.2.2
                            linarith only [h6510, hlam, p6549_0]
                          · have p6549_0 := h6549c.1
                            have p6549_1 := h6549c.2.1
                            have p6549_2 := h6549c.2.2.1
                            have p6549_3 := h6549c.2.2.2
                            linarith only [h6512, hlam, p6549_0]
                          · have p6549_0 := h6549c.1
                            have p6549_1 := h6549c.2.1
                            have p6549_2 := h6549c.2.2.1
                            have p6549_3 := h6549c.2.2.2
                            linarith only [h6513, hlam, p6549_0]
                          · have p6549_0 := h6549c.1
                            have p6549_1 := h6549c.2.1
                            have p6549_2 := h6549c.2.2.1
                            have p6549_3 := h6549c.2.2.2
                            linarith only [hlam, p6549_0]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h6575 | h6575
                        · linarith only [h6508, h6514, h6515, h6575, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · rcases h1bigk with h6577c | h6577c | h6577c | h6577c | h6577c | h6577c | h6577c | h6577c | h6577c | h6577c | h6577c | h6577c | h6577c | h6577c | h6577c | h6577c | h6577c | h6577c | h6577c | h6577c | h6577c | h6577c | h6577c | h6577c | h6577c
                          · have p6577_0 := h6577c.1
                            have p6577_1 := h6577c.2.1
                            have p6577_2 := h6577c.2.2.1
                            have p6577_3 := h6577c.2.2.2
                            linarith only [hlam, p6577_0]
                          · have p6577_0 := h6577c.1
                            have p6577_1 := h6577c.2.1
                            have p6577_2 := h6577c.2.2.1
                            have p6577_3 := h6577c.2.2.2
                            linarith only [h0, hlam, p6577_0]
                          · have p6577_0 := h6577c.1
                            have p6577_1 := h6577c.2.1
                            have p6577_2 := h6577c.2.2.1
                            have p6577_3 := h6577c.2.2.2
                            linarith only [h5235, hlam, p6577_0]
                          · have p6577_0 := h6577c.1
                            have p6577_1 := h6577c.2.1
                            have p6577_2 := h6577c.2.2.1
                            have p6577_3 := h6577c.2.2.2
                            linarith only [h6110, hlam, p6577_0]
                          · have p6577_0 := h6577c.1
                            have p6577_1 := h6577c.2.1
                            have p6577_2 := h6577c.2.2.1
                            have p6577_3 := h6577c.2.2.2
                            linarith only [h6110, h6508, h6511, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b, p6577_1]
                          · have p6577_0 := h6577c.1
                            have p6577_1 := h6577c.2.1
                            have p6577_2 := h6577c.2.2.1
                            have p6577_3 := h6577c.2.2.2
                            linarith only [hc01, hc12, hlam, hphi, p6577_1]
                          · have p6577_0 := h6577c.1
                            have p6577_1 := h6577c.2.1
                            have p6577_2 := h6577c.2.2.1
                            have p6577_3 := h6577c.2.2.2
                            linarith only [hlam, p6577_0]
                          · have p6577_0 := h6577c.1
                            have p6577_1 := h6577c.2.1
                            have p6577_2 := h6577c.2.2.1
                            have p6577_3 := h6577c.2.2.2
                            linarith only [h5235, hc01, hc12, hlam, hphi, p6577_1]
                          · have p6577_0 := h6577c.1
                            have p6577_1 := h6577c.2.1
                            have p6577_2 := h6577c.2.2.1
                            have p6577_3 := h6577c.2.2.2
                            linarith only [h6110, h6504, h6507, h6514, h6515, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p6577_1]
                          · have p6577_0 := h6577c.1
                            have p6577_1 := h6577c.2.1
                            have p6577_2 := h6577c.2.2.1
                            have p6577_3 := h6577c.2.2.2
                            linarith only [h6513, h6514, h6515, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p6577_1]
                          · have p6577_0 := h6577c.1
                            have p6577_1 := h6577c.2.1
                            have p6577_2 := h6577c.2.2.1
                            have p6577_3 := h6577c.2.2.2
                            linarith only [h6504, h6513, h6514, h6515, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p6577_1]
                          · have p6577_0 := h6577c.1
                            have p6577_1 := h6577c.2.1
                            have p6577_2 := h6577c.2.2.1
                            have p6577_3 := h6577c.2.2.2
                            linarith only [h6508, hlam, p6577_0]
                          · have p6577_0 := h6577c.1
                            have p6577_1 := h6577c.2.1
                            have p6577_2 := h6577c.2.2.1
                            have p6577_3 := h6577c.2.2.2
                            linarith only [hlam, p6577_0]
                          · have p6577_0 := h6577c.1
                            have p6577_1 := h6577c.2.1
                            have p6577_2 := h6577c.2.2.1
                            have p6577_3 := h6577c.2.2.2
                            linarith only [h6110, h6504, h6508, h6513, h6514, h6515, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p6577_1]
                          · have p6577_0 := h6577c.1
                            have p6577_1 := h6577c.2.1
                            have p6577_2 := h6577c.2.2.1
                            have p6577_3 := h6577c.2.2.2
                            linarith only [h6508, h6513, h6514, h6515, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p6577_1]
                          · have p6577_0 := h6577c.1
                            have p6577_1 := h6577c.2.1
                            have p6577_2 := h6577c.2.2.1
                            have p6577_3 := h6577c.2.2.2
                            linarith only [h6504, h6513, h6514, h6515, hc14, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p6577_1]
                          · have p6577_0 := h6577c.1
                            have p6577_1 := h6577c.2.1
                            have p6577_2 := h6577c.2.2.1
                            have p6577_3 := h6577c.2.2.2
                            linarith only [h6509, hlam, p6577_0]
                          · have p6577_0 := h6577c.1
                            have p6577_1 := h6577c.2.1
                            have p6577_2 := h6577c.2.2.1
                            have p6577_3 := h6577c.2.2.2
                            linarith only [h6511, hlam, p6577_1]
                          · have p6577_0 := h6577c.1
                            have p6577_1 := h6577c.2.1
                            have p6577_2 := h6577c.2.2.1
                            have p6577_3 := h6577c.2.2.2
                            linarith only [hlam, p6577_0]
                          · have p6577_0 := h6577c.1
                            have p6577_1 := h6577c.2.1
                            have p6577_2 := h6577c.2.2.1
                            have p6577_3 := h6577c.2.2.2
                            linarith only [h6508, h6511, h6513, h6514, h6515, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p6577_1]
                          · have p6577_0 := h6577c.1
                            have p6577_1 := h6577c.2.1
                            have p6577_2 := h6577c.2.2.1
                            have p6577_3 := h6577c.2.2.2
                            linarith only [h6504, hlam, p6577_0]
                          · have p6577_0 := h6577c.1
                            have p6577_1 := h6577c.2.1
                            have p6577_2 := h6577c.2.2.1
                            have p6577_3 := h6577c.2.2.2
                            linarith only [h6510, hlam, p6577_0]
                          · have p6577_0 := h6577c.1
                            have p6577_1 := h6577c.2.1
                            have p6577_2 := h6577c.2.2.1
                            have p6577_3 := h6577c.2.2.2
                            linarith only [h6512, hlam, p6577_0]
                          · have p6577_0 := h6577c.1
                            have p6577_1 := h6577c.2.1
                            have p6577_2 := h6577c.2.2.1
                            have p6577_3 := h6577c.2.2.2
                            linarith only [h6513, hlam, p6577_0]
                          · have p6577_0 := h6577c.1
                            have p6577_1 := h6577c.2.1
                            have p6577_2 := h6577c.2.2.1
                            have p6577_3 := h6577c.2.2.2
                            linarith only [hlam, p6577_0]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h6603 | h6603
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h6604 | h6604
                        · rcases h1bigk with h6605c | h6605c | h6605c | h6605c | h6605c | h6605c | h6605c | h6605c | h6605c | h6605c | h6605c | h6605c | h6605c | h6605c | h6605c | h6605c | h6605c | h6605c | h6605c | h6605c | h6605c | h6605c | h6605c | h6605c | h6605c
                          · have p6605_0 := h6605c.1
                            have p6605_1 := h6605c.2.1
                            have p6605_2 := h6605c.2.2.1
                            have p6605_3 := h6605c.2.2.2
                            linarith only [hlam, p6605_0]
                          · have p6605_0 := h6605c.1
                            have p6605_1 := h6605c.2.1
                            have p6605_2 := h6605c.2.2.1
                            have p6605_3 := h6605c.2.2.2
                            linarith only [h0, hlam, p6605_0]
                          · have p6605_0 := h6605c.1
                            have p6605_1 := h6605c.2.1
                            have p6605_2 := h6605c.2.2.1
                            have p6605_3 := h6605c.2.2.2
                            linarith only [h5235, hlam, p6605_0]
                          · have p6605_0 := h6605c.1
                            have p6605_1 := h6605c.2.1
                            have p6605_2 := h6605c.2.2.1
                            have p6605_3 := h6605c.2.2.2
                            linarith only [h6110, hlam, p6605_0]
                          · have p6605_0 := h6605c.1
                            have p6605_1 := h6605c.2.1
                            have p6605_2 := h6605c.2.2.1
                            have p6605_3 := h6605c.2.2.2
                            linarith only [h0, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b, p6605_1]
                          · have p6605_0 := h6605c.1
                            have p6605_1 := h6605c.2.1
                            have p6605_2 := h6605c.2.2.1
                            have p6605_3 := h6605c.2.2.2
                            linarith only [hc01, hc12, hlam, hphi, p6605_1]
                          · have p6605_0 := h6605c.1
                            have p6605_1 := h6605c.2.1
                            have p6605_2 := h6605c.2.2.1
                            have p6605_3 := h6605c.2.2.2
                            linarith only [hlam, p6605_0]
                          · have p6605_0 := h6605c.1
                            have p6605_1 := h6605c.2.1
                            have p6605_2 := h6605c.2.2.1
                            have p6605_3 := h6605c.2.2.2
                            linarith only [h5235, hc01, hc12, hlam, hphi, p6605_1]
                          · have p6605_0 := h6605c.1
                            have p6605_1 := h6605c.2.1
                            have p6605_2 := h6605c.2.2.1
                            have p6605_3 := h6605c.2.2.2
                            linarith only [h6110, h6504, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b, p6605_1]
                          · have p6605_0 := h6605c.1
                            have p6605_1 := h6605c.2.1
                            have p6605_2 := h6605c.2.2.1
                            have p6605_3 := h6605c.2.2.2
                            rcases p6605_3 (m.d 0 1) (by simp) with h6615 | h6615
                            · linarith only [h0, h6615, hlam]
                            · linarith only [h6504, h6615, hlam]
                          · have p6605_0 := h6605c.1
                            have p6605_1 := h6605c.2.1
                            have p6605_2 := h6605c.2.2.1
                            have p6605_3 := h6605c.2.2.2
                            linarith only [h6504, h6510, h6603, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p6605_1]
                          · have p6605_0 := h6605c.1
                            have p6605_1 := h6605c.2.1
                            have p6605_2 := h6605c.2.2.1
                            have p6605_3 := h6605c.2.2.2
                            linarith only [h6508, hlam, p6605_0]
                          · have p6605_0 := h6605c.1
                            have p6605_1 := h6605c.2.1
                            have p6605_2 := h6605c.2.2.1
                            have p6605_3 := h6605c.2.2.2
                            linarith only [hlam, p6605_0]
                          · have p6605_0 := h6605c.1
                            have p6605_1 := h6605c.2.1
                            have p6605_2 := h6605c.2.2.1
                            have p6605_3 := h6605c.2.2.2
                            linarith only [h6110, h6504, h6508, h6510, h6603, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p6605_1]
                          · have p6605_0 := h6605c.1
                            have p6605_1 := h6605c.2.1
                            have p6605_2 := h6605c.2.2.1
                            have p6605_3 := h6605c.2.2.2
                            rcases p6605_3 (m.d 0 1) (by simp) with h6622 | h6622
                            · linarith only [h5235, h6622, hlam]
                            · linarith only [h6504, h6622, hlam]
                          · have p6605_0 := h6605c.1
                            have p6605_1 := h6605c.2.1
                            have p6605_2 := h6605c.2.2.1
                            have p6605_3 := h6605c.2.2.2
                            linarith only [h6504, h6510, h6603, hc14, hc45, hlam, hphi, ht01, ht0b, ht5b, p6605_1]
                          · have p6605_0 := h6605c.1
                            have p6605_1 := h6605c.2.1
                            have p6605_2 := h6605c.2.2.1
                            have p6605_3 := h6605c.2.2.2
                            linarith only [h6509, hlam, p6605_0]
                          · have p6605_0 := h6605c.1
                            have p6605_1 := h6605c.2.1
                            have p6605_2 := h6605c.2.2.1
                            have p6605_3 := h6605c.2.2.2
                            linarith only [h6511, hlam, p6605_1]
                          · have p6605_0 := h6605c.1
                            have p6605_1 := h6605c.2.1
                            have p6605_2 := h6605c.2.2.1
                            have p6605_3 := h6605c.2.2.2
                            linarith only [hlam, p6605_0]
                          · have p6605_0 := h6605c.1
                            have p6605_1 := h6605c.2.1
                            have p6605_2 := h6605c.2.2.1
                            have p6605_3 := h6605c.2.2.2
                            rcases p6605_3 (m.d 0 1) (by simp) with h6629 | h6629
                            · linarith only [h6110, h6629, hlam]
                            · linarith only [h6504, h6629, hlam]
                          · have p6605_0 := h6605c.1
                            have p6605_1 := h6605c.2.1
                            have p6605_2 := h6605c.2.2.1
                            have p6605_3 := h6605c.2.2.2
                            linarith only [h6504, hlam, p6605_0]
                          · have p6605_0 := h6605c.1
                            have p6605_1 := h6605c.2.1
                            have p6605_2 := h6605c.2.2.1
                            have p6605_3 := h6605c.2.2.2
                            linarith only [h6510, hlam, p6605_0]
                          · have p6605_0 := h6605c.1
                            have p6605_1 := h6605c.2.1
                            have p6605_2 := h6605c.2.2.1
                            have p6605_3 := h6605c.2.2.2
                            linarith only [h6512, hlam, p6605_0]
                          · have p6605_0 := h6605c.1
                            have p6605_1 := h6605c.2.1
                            have p6605_2 := h6605c.2.2.1
                            have p6605_3 := h6605c.2.2.2
                            linarith only [h6513, hlam, p6605_0]
                          · have p6605_0 := h6605c.1
                            have p6605_1 := h6605c.2.1
                            have p6605_2 := h6605c.2.2.1
                            have p6605_3 := h6605c.2.2.2
                            linarith only [hlam, p6605_0]
                        · linarith only [h0, h6504, h6510, h6514, h6603, h6604, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h6638 | h6638
                        · rcases h1bigk with h6639c | h6639c | h6639c | h6639c | h6639c | h6639c | h6639c | h6639c | h6639c | h6639c | h6639c | h6639c | h6639c | h6639c | h6639c | h6639c | h6639c | h6639c | h6639c | h6639c | h6639c | h6639c | h6639c | h6639c | h6639c
                          · have p6639_0 := h6639c.1
                            have p6639_1 := h6639c.2.1
                            have p6639_2 := h6639c.2.2.1
                            have p6639_3 := h6639c.2.2.2
                            linarith only [hlam, p6639_0]
                          · have p6639_0 := h6639c.1
                            have p6639_1 := h6639c.2.1
                            have p6639_2 := h6639c.2.2.1
                            have p6639_3 := h6639c.2.2.2
                            linarith only [h0, hlam, p6639_0]
                          · have p6639_0 := h6639c.1
                            have p6639_1 := h6639c.2.1
                            have p6639_2 := h6639c.2.2.1
                            have p6639_3 := h6639c.2.2.2
                            linarith only [h5235, hlam, p6639_0]
                          · have p6639_0 := h6639c.1
                            have p6639_1 := h6639c.2.1
                            have p6639_2 := h6639c.2.2.1
                            have p6639_3 := h6639c.2.2.2
                            linarith only [h6110, hlam, p6639_0]
                          · have p6639_0 := h6639c.1
                            have p6639_1 := h6639c.2.1
                            have p6639_2 := h6639c.2.2.1
                            have p6639_3 := h6639c.2.2.2
                            linarith only [h6110, h6508, h6511, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b, p6639_1]
                          · have p6639_0 := h6639c.1
                            have p6639_1 := h6639c.2.1
                            have p6639_2 := h6639c.2.2.1
                            have p6639_3 := h6639c.2.2.2
                            linarith only [hc01, hc12, hlam, hphi, p6639_1]
                          · have p6639_0 := h6639c.1
                            have p6639_1 := h6639c.2.1
                            have p6639_2 := h6639c.2.2.1
                            have p6639_3 := h6639c.2.2.2
                            linarith only [hlam, p6639_0]
                          · have p6639_0 := h6639c.1
                            have p6639_1 := h6639c.2.1
                            have p6639_2 := h6639c.2.2.1
                            have p6639_3 := h6639c.2.2.2
                            linarith only [h5235, h6506, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p6639_1]
                          · have p6639_0 := h6639c.1
                            have p6639_1 := h6639c.2.1
                            have p6639_2 := h6639c.2.2.1
                            have p6639_3 := h6639c.2.2.2
                            linarith only [h6110, h6504, h6512, h6603, h6638, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p6639_1]
                          · have p6639_0 := h6639c.1
                            have p6639_1 := h6639c.2.1
                            have p6639_2 := h6639c.2.2.1
                            have p6639_3 := h6639c.2.2.2
                            linarith only [h6512, h6603, h6638, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p6639_1]
                          · have p6639_0 := h6639c.1
                            have p6639_1 := h6639c.2.1
                            have p6639_2 := h6639c.2.2.1
                            have p6639_3 := h6639c.2.2.2
                            linarith only [h6504, h6512, h6603, h6638, hc13, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p6639_1]
                          · have p6639_0 := h6639c.1
                            have p6639_1 := h6639c.2.1
                            have p6639_2 := h6639c.2.2.1
                            have p6639_3 := h6639c.2.2.2
                            linarith only [h6508, hlam, p6639_0]
                          · have p6639_0 := h6639c.1
                            have p6639_1 := h6639c.2.1
                            have p6639_2 := h6639c.2.2.1
                            have p6639_3 := h6639c.2.2.2
                            linarith only [hlam, p6639_0]
                          · have p6639_0 := h6639c.1
                            have p6639_1 := h6639c.2.1
                            have p6639_2 := h6639c.2.2.1
                            have p6639_3 := h6639c.2.2.2
                            linarith only [h6110, h6504, h6508, h6512, h6603, h6638, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p6639_1]
                          · have p6639_0 := h6639c.1
                            have p6639_1 := h6639c.2.1
                            have p6639_2 := h6639c.2.2.1
                            have p6639_3 := h6639c.2.2.2
                            linarith only [h6508, h6512, h6603, h6638, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p6639_1]
                          · have p6639_0 := h6639c.1
                            have p6639_1 := h6639c.2.1
                            have p6639_2 := h6639c.2.2.1
                            have p6639_3 := h6639c.2.2.2
                            linarith only [h6504, h6512, h6603, h6638, hc14, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p6639_1]
                          · have p6639_0 := h6639c.1
                            have p6639_1 := h6639c.2.1
                            have p6639_2 := h6639c.2.2.1
                            have p6639_3 := h6639c.2.2.2
                            linarith only [h6509, hlam, p6639_0]
                          · have p6639_0 := h6639c.1
                            have p6639_1 := h6639c.2.1
                            have p6639_2 := h6639c.2.2.1
                            have p6639_3 := h6639c.2.2.2
                            linarith only [h6511, hlam, p6639_1]
                          · have p6639_0 := h6639c.1
                            have p6639_1 := h6639c.2.1
                            have p6639_2 := h6639c.2.2.1
                            have p6639_3 := h6639c.2.2.2
                            linarith only [hlam, p6639_0]
                          · have p6639_0 := h6639c.1
                            have p6639_1 := h6639c.2.1
                            have p6639_2 := h6639c.2.2.1
                            have p6639_3 := h6639c.2.2.2
                            linarith only [h6508, h6511, h6512, h6603, h6638, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p6639_1]
                          · have p6639_0 := h6639c.1
                            have p6639_1 := h6639c.2.1
                            have p6639_2 := h6639c.2.2.1
                            have p6639_3 := h6639c.2.2.2
                            linarith only [h6504, hlam, p6639_0]
                          · have p6639_0 := h6639c.1
                            have p6639_1 := h6639c.2.1
                            have p6639_2 := h6639c.2.2.1
                            have p6639_3 := h6639c.2.2.2
                            linarith only [h6510, hlam, p6639_0]
                          · have p6639_0 := h6639c.1
                            have p6639_1 := h6639c.2.1
                            have p6639_2 := h6639c.2.2.1
                            have p6639_3 := h6639c.2.2.2
                            linarith only [h6512, hlam, p6639_0]
                          · have p6639_0 := h6639c.1
                            have p6639_1 := h6639c.2.1
                            have p6639_2 := h6639c.2.2.1
                            have p6639_3 := h6639c.2.2.2
                            linarith only [h6513, hlam, p6639_0]
                          · have p6639_0 := h6639c.1
                            have p6639_1 := h6639c.2.1
                            have p6639_2 := h6639c.2.2.1
                            have p6639_3 := h6639c.2.2.2
                            linarith only [hlam, p6639_0]
                        · linarith only [h6110, h6504, h6508, h6511, h6513, h6514, h6638, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                  · linarith only [h6110, h6504, h6506, h6507, h6513, hc03, hc15, hlam, hphi, ht0b, ht5b]
                · linarith only [h6110, h6504, h6511, h6512, hlam]
              · linarith only [h5235, h6506, h6511, hlam]
            · linarith only [h0, h6504, h6510, hlam]
          · linarith only [h0, h6505, h6509, hlam]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h6671 | h6671
          · rcases m.htr 1 2 5 (by decide) (by decide) with h6672 | h6672
            · rcases m.htr 1 3 4 (by decide) (by decide) with h6673 | h6673
              · rcases m.htr 1 3 5 (by decide) (by decide) with h6674 | h6674
                · rcases m.htr 1 4 5 (by decide) (by decide) with h6675 | h6675
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h6676 | h6676
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h6677 | h6677
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h6678 | h6678
                        · rcases h1bigk with h6679c | h6679c | h6679c | h6679c | h6679c | h6679c | h6679c | h6679c | h6679c | h6679c | h6679c | h6679c | h6679c | h6679c | h6679c | h6679c | h6679c | h6679c | h6679c | h6679c | h6679c | h6679c | h6679c | h6679c | h6679c
                          · have p6679_0 := h6679c.1
                            have p6679_1 := h6679c.2.1
                            have p6679_2 := h6679c.2.2.1
                            have p6679_3 := h6679c.2.2.2
                            linarith only [hlam, p6679_0]
                          · have p6679_0 := h6679c.1
                            have p6679_1 := h6679c.2.1
                            have p6679_2 := h6679c.2.2.1
                            have p6679_3 := h6679c.2.2.2
                            linarith only [h0, hlam, p6679_0]
                          · have p6679_0 := h6679c.1
                            have p6679_1 := h6679c.2.1
                            have p6679_2 := h6679c.2.2.1
                            have p6679_3 := h6679c.2.2.2
                            linarith only [h5235, hlam, p6679_0]
                          · have p6679_0 := h6679c.1
                            have p6679_1 := h6679c.2.1
                            have p6679_2 := h6679c.2.2.1
                            have p6679_3 := h6679c.2.2.2
                            linarith only [h6110, hlam, p6679_0]
                          · have p6679_0 := h6679c.1
                            have p6679_1 := h6679c.2.1
                            have p6679_2 := h6679c.2.2.1
                            have p6679_3 := h6679c.2.2.2
                            linarith only [h6110, h6671, h6672, h6677, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p6679_1]
                          · have p6679_0 := h6679c.1
                            have p6679_1 := h6679c.2.1
                            have p6679_2 := h6679c.2.2.1
                            have p6679_3 := h6679c.2.2.2
                            linarith only [h6508, hc01, hc23, hlam, hphi, ht12, p6679_1]
                          · have p6679_0 := h6679c.1
                            have p6679_1 := h6679c.2.1
                            have p6679_2 := h6679c.2.2.1
                            have p6679_3 := h6679c.2.2.2
                            linarith only [hlam, p6679_0]
                          · have p6679_0 := h6679c.1
                            have p6679_1 := h6679c.2.1
                            have p6679_2 := h6679c.2.2.1
                            have p6679_3 := h6679c.2.2.2
                            linarith only [h6508, hlam, p6679_1]
                          · have p6679_0 := h6679c.1
                            have p6679_1 := h6679c.2.1
                            have p6679_2 := h6679c.2.2.1
                            have p6679_3 := h6679c.2.2.2
                            linarith only [h6508, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p6679_1]
                          · have p6679_0 := h6679c.1
                            have p6679_1 := h6679c.2.1
                            have p6679_2 := h6679c.2.2.1
                            have p6679_3 := h6679c.2.2.2
                            linarith only [h6508, h6672, h6677, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p6679_1]
                          · have p6679_0 := h6679c.1
                            have p6679_1 := h6679c.2.1
                            have p6679_2 := h6679c.2.2.1
                            have p6679_3 := h6679c.2.2.2
                            linarith only [h6504, h6508, h6672, h6677, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p6679_1]
                          · have p6679_0 := h6679c.1
                            have p6679_1 := h6679c.2.1
                            have p6679_2 := h6679c.2.2.1
                            have p6679_3 := h6679c.2.2.2
                            linarith only [h0, h6508, hc02, hc23, hlam, hphi, p6679_1]
                          · have p6679_0 := h6679c.1
                            have p6679_1 := h6679c.2.1
                            have p6679_2 := h6679c.2.2.1
                            have p6679_3 := h6679c.2.2.2
                            linarith only [hlam, p6679_0]
                          · have p6679_0 := h6679c.1
                            have p6679_1 := h6679c.2.1
                            have p6679_2 := h6679c.2.2.1
                            have p6679_3 := h6679c.2.2.2
                            linarith only [h6110, h6504, h6508, h6672, h6677, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p6679_1]
                          · have p6679_0 := h6679c.1
                            have p6679_1 := h6679c.2.1
                            have p6679_2 := h6679c.2.2.1
                            have p6679_3 := h6679c.2.2.2
                            rcases p6679_3 (m.d 0 1) (by simp) with h6694 | h6694
                            · linarith only [h5235, h6694, hlam]
                            · linarith only [h6504, h6694, hlam]
                          · have p6679_0 := h6679c.1
                            have p6679_1 := h6679c.2.1
                            have p6679_2 := h6679c.2.2.1
                            have p6679_3 := h6679c.2.2.2
                            linarith only [h6504, h6672, h6677, hc14, hc45, hlam, hphi, ht01, ht0b, ht5b, p6679_1]
                          · have p6679_0 := h6679c.1
                            have p6679_1 := h6679c.2.1
                            have p6679_2 := h6679c.2.2.1
                            have p6679_3 := h6679c.2.2.2
                            linarith only [h6671, hlam, p6679_0]
                          · have p6679_0 := h6679c.1
                            have p6679_1 := h6679c.2.1
                            have p6679_2 := h6679c.2.2.1
                            have p6679_3 := h6679c.2.2.2
                            linarith only [h6673, hlam, p6679_1]
                          · have p6679_0 := h6679c.1
                            have p6679_1 := h6679c.2.1
                            have p6679_2 := h6679c.2.2.1
                            have p6679_3 := h6679c.2.2.2
                            linarith only [hlam, p6679_0]
                          · have p6679_0 := h6679c.1
                            have p6679_1 := h6679c.2.1
                            have p6679_2 := h6679c.2.2.1
                            have p6679_3 := h6679c.2.2.2
                            linarith only [h6508, h6671, h6672, h6677, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p6679_1]
                          · have p6679_0 := h6679c.1
                            have p6679_1 := h6679c.2.1
                            have p6679_2 := h6679c.2.2.1
                            have p6679_3 := h6679c.2.2.2
                            linarith only [h6504, hlam, p6679_0]
                          · have p6679_0 := h6679c.1
                            have p6679_1 := h6679c.2.1
                            have p6679_2 := h6679c.2.2.1
                            have p6679_3 := h6679c.2.2.2
                            linarith only [h6672, hlam, p6679_0]
                          · have p6679_0 := h6679c.1
                            have p6679_1 := h6679c.2.1
                            have p6679_2 := h6679c.2.2.1
                            have p6679_3 := h6679c.2.2.2
                            linarith only [h6674, hlam, p6679_0]
                          · have p6679_0 := h6679c.1
                            have p6679_1 := h6679c.2.1
                            have p6679_2 := h6679c.2.2.1
                            have p6679_3 := h6679c.2.2.2
                            linarith only [h6675, hlam, p6679_0]
                          · have p6679_0 := h6679c.1
                            have p6679_1 := h6679c.2.1
                            have p6679_2 := h6679c.2.2.1
                            have p6679_3 := h6679c.2.2.2
                            linarith only [hlam, p6679_0]
                        · linarith only [h0, h6504, h6508, h6672, h6677, h6678, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · linarith only [h6110, h6504, h6508, h6671, h6675, h6676, h6677, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                    · linarith only [h6110, h6508, h6671, h6676, hc01, hc34, hlam, hphi, ht12, ht23]
                  · linarith only [h6110, h6504, h6505, h6507, h6672, h6675, hc02, hc25, hlam, hphi, ht0b, ht5b]
                · linarith only [h5235, h6110, h6504, h6506, h6508, h6671, h6674, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
              · linarith only [h6110, h6504, h6506, h6508, h6671, h6673, hc03, hc15, hlam, hphi, ht0b, ht5b]
            · linarith only [h6110, h6504, h6671, h6672, hlam]
          · linarith only [h0, h6504, h6505, h6671, hc02, hc15, hlam, hphi, ht0b, ht5b]
      · linarith only [h6110, h6504, h6507, hlam]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h6716 | h6716
      · rcases m.htr 1 2 3 (by decide) (by decide) with h6717 | h6717
        · rcases m.htr 1 2 4 (by decide) (by decide) with h6718 | h6718
          · rcases m.htr 1 2 5 (by decide) (by decide) with h6719 | h6719
            · rcases m.htr 1 3 4 (by decide) (by decide) with h6720 | h6720
              · rcases m.htr 1 3 5 (by decide) (by decide) with h6721 | h6721
                · rcases m.htr 1 4 5 (by decide) (by decide) with h6722 | h6722
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h6723 | h6723
                    · linarith only [h5235, h6504, h6506, h6717, h6719, h6723, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h6725 | h6725
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h6726 | h6726
                        · rcases h1bigk with h6727c | h6727c | h6727c | h6727c | h6727c | h6727c | h6727c | h6727c | h6727c | h6727c | h6727c | h6727c | h6727c | h6727c | h6727c | h6727c | h6727c | h6727c | h6727c | h6727c | h6727c | h6727c | h6727c | h6727c | h6727c
                          · have p6727_0 := h6727c.1
                            have p6727_1 := h6727c.2.1
                            have p6727_2 := h6727c.2.2.1
                            have p6727_3 := h6727c.2.2.2
                            linarith only [hlam, p6727_0]
                          · have p6727_0 := h6727c.1
                            have p6727_1 := h6727c.2.1
                            have p6727_2 := h6727c.2.2.1
                            have p6727_3 := h6727c.2.2.2
                            linarith only [h0, hlam, p6727_0]
                          · have p6727_0 := h6727c.1
                            have p6727_1 := h6727c.2.1
                            have p6727_2 := h6727c.2.2.1
                            have p6727_3 := h6727c.2.2.2
                            linarith only [h5235, hlam, p6727_0]
                          · have p6727_0 := h6727c.1
                            have p6727_1 := h6727c.2.1
                            have p6727_2 := h6727c.2.2.1
                            have p6727_3 := h6727c.2.2.2
                            linarith only [h6110, hlam, p6727_0]
                          · have p6727_0 := h6727c.1
                            have p6727_1 := h6727c.2.1
                            have p6727_2 := h6727c.2.2.1
                            have p6727_3 := h6727c.2.2.2
                            linarith only [h5235, h6506, h6719, h6720, h6725, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p6727_1]
                          · have p6727_0 := h6727c.1
                            have p6727_1 := h6727c.2.1
                            have p6727_2 := h6727c.2.2.1
                            have p6727_3 := h6727c.2.2.2
                            linarith only [hc01, hc12, hlam, hphi, p6727_1]
                          · have p6727_0 := h6727c.1
                            have p6727_1 := h6727c.2.1
                            have p6727_2 := h6727c.2.2.1
                            have p6727_3 := h6727c.2.2.2
                            linarith only [hlam, p6727_0]
                          · have p6727_0 := h6727c.1
                            have p6727_1 := h6727c.2.1
                            have p6727_2 := h6727c.2.2.1
                            have p6727_3 := h6727c.2.2.2
                            linarith only [h6506, h6720, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6727_1]
                          · have p6727_0 := h6727c.1
                            have p6727_1 := h6727c.2.1
                            have p6727_2 := h6727c.2.2.1
                            have p6727_3 := h6727c.2.2.2
                            linarith only [h5235, h6504, h6506, h6719, h6720, h6725, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p6727_1]
                          · have p6727_0 := h6727c.1
                            have p6727_1 := h6727c.2.1
                            have p6727_2 := h6727c.2.2.1
                            have p6727_3 := h6727c.2.2.2
                            rcases p6727_3 (m.d 0 1) (by simp) with h6737 | h6737
                            · linarith only [h0, h6737, hlam]
                            · linarith only [h6504, h6737, hlam]
                          · have p6727_0 := h6727c.1
                            have p6727_1 := h6727c.2.1
                            have p6727_2 := h6727c.2.2.1
                            have p6727_3 := h6727c.2.2.2
                            linarith only [h6504, h6719, h6725, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p6727_1]
                          · have p6727_0 := h6727c.1
                            have p6727_1 := h6727c.2.1
                            have p6727_2 := h6727c.2.2.1
                            have p6727_3 := h6727c.2.2.2
                            linarith only [h6717, hlam, p6727_0]
                          · have p6727_0 := h6727c.1
                            have p6727_1 := h6727c.2.1
                            have p6727_2 := h6727c.2.2.1
                            have p6727_3 := h6727c.2.2.2
                            linarith only [hlam, p6727_0]
                          · have p6727_0 := h6727c.1
                            have p6727_1 := h6727c.2.1
                            have p6727_2 := h6727c.2.2.1
                            have p6727_3 := h6727c.2.2.2
                            linarith only [h5235, h6504, h6506, h6717, h6719, h6720, h6725, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p6727_1]
                          · have p6727_0 := h6727c.1
                            have p6727_1 := h6727c.2.1
                            have p6727_2 := h6727c.2.2.1
                            have p6727_3 := h6727c.2.2.2
                            rcases p6727_3 (m.d 0 1) (by simp) with h6744 | h6744
                            · linarith only [h5235, h6744, hlam]
                            · linarith only [h6504, h6744, hlam]
                          · have p6727_0 := h6727c.1
                            have p6727_1 := h6727c.2.1
                            have p6727_2 := h6727c.2.2.1
                            have p6727_3 := h6727c.2.2.2
                            linarith only [h6504, h6719, h6725, hc14, hc45, hlam, hphi, ht01, ht0b, ht5b, p6727_1]
                          · have p6727_0 := h6727c.1
                            have p6727_1 := h6727c.2.1
                            have p6727_2 := h6727c.2.2.1
                            have p6727_3 := h6727c.2.2.2
                            linarith only [h6718, hlam, p6727_0]
                          · have p6727_0 := h6727c.1
                            have p6727_1 := h6727c.2.1
                            have p6727_2 := h6727c.2.2.1
                            have p6727_3 := h6727c.2.2.2
                            linarith only [h6720, hlam, p6727_1]
                          · have p6727_0 := h6727c.1
                            have p6727_1 := h6727c.2.1
                            have p6727_2 := h6727c.2.2.1
                            have p6727_3 := h6727c.2.2.2
                            linarith only [hlam, p6727_0]
                          · have p6727_0 := h6727c.1
                            have p6727_1 := h6727c.2.1
                            have p6727_2 := h6727c.2.2.1
                            have p6727_3 := h6727c.2.2.2
                            rcases p6727_3 (m.d 0 1) (by simp) with h6751 | h6751
                            · linarith only [h6110, h6751, hlam]
                            · linarith only [h6504, h6751, hlam]
                          · have p6727_0 := h6727c.1
                            have p6727_1 := h6727c.2.1
                            have p6727_2 := h6727c.2.2.1
                            have p6727_3 := h6727c.2.2.2
                            linarith only [h6504, hlam, p6727_0]
                          · have p6727_0 := h6727c.1
                            have p6727_1 := h6727c.2.1
                            have p6727_2 := h6727c.2.2.1
                            have p6727_3 := h6727c.2.2.2
                            linarith only [h6719, hlam, p6727_0]
                          · have p6727_0 := h6727c.1
                            have p6727_1 := h6727c.2.1
                            have p6727_2 := h6727c.2.2.1
                            have p6727_3 := h6727c.2.2.2
                            linarith only [h6721, hlam, p6727_0]
                          · have p6727_0 := h6727c.1
                            have p6727_1 := h6727c.2.1
                            have p6727_2 := h6727c.2.2.1
                            have p6727_3 := h6727c.2.2.2
                            linarith only [h6722, hlam, p6727_0]
                          · have p6727_0 := h6727c.1
                            have p6727_1 := h6727c.2.1
                            have p6727_2 := h6727c.2.2.1
                            have p6727_3 := h6727c.2.2.2
                            linarith only [hlam, p6727_0]
                        · linarith only [h5235, h6504, h6506, h6719, h6725, h6726, hlam]
                      · linarith only [h5235, h6504, h6506, h6717, h6720, h6722, h6725, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                  · linarith only [h6110, h6504, h6716, h6722, hc04, hc15, hlam, hphi, ht0b, ht5b]
                · linarith only [h5235, h6504, h6506, h6719, h6720, h6721, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h6763 | h6763
                · rcases m.htr 1 4 5 (by decide) (by decide) with h6764 | h6764
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h6765 | h6765
                    · linarith only [h5235, h6504, h6719, h6720, h6765, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h6767 | h6767
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h6768 | h6768
                        · rcases h1bigk with h6769c | h6769c | h6769c | h6769c | h6769c | h6769c | h6769c | h6769c | h6769c | h6769c | h6769c | h6769c | h6769c | h6769c | h6769c | h6769c | h6769c | h6769c | h6769c | h6769c | h6769c | h6769c | h6769c | h6769c | h6769c
                          · have p6769_0 := h6769c.1
                            have p6769_1 := h6769c.2.1
                            have p6769_2 := h6769c.2.2.1
                            have p6769_3 := h6769c.2.2.2
                            linarith only [hlam, p6769_0]
                          · have p6769_0 := h6769c.1
                            have p6769_1 := h6769c.2.1
                            have p6769_2 := h6769c.2.2.1
                            have p6769_3 := h6769c.2.2.2
                            linarith only [h0, hlam, p6769_0]
                          · have p6769_0 := h6769c.1
                            have p6769_1 := h6769c.2.1
                            have p6769_2 := h6769c.2.2.1
                            have p6769_3 := h6769c.2.2.2
                            linarith only [h5235, hlam, p6769_0]
                          · have p6769_0 := h6769c.1
                            have p6769_1 := h6769c.2.1
                            have p6769_2 := h6769c.2.2.1
                            have p6769_3 := h6769c.2.2.2
                            linarith only [h6110, hlam, p6769_0]
                          · have p6769_0 := h6769c.1
                            have p6769_1 := h6769c.2.1
                            have p6769_2 := h6769c.2.2.1
                            have p6769_3 := h6769c.2.2.2
                            linarith only [h5235, h6719, h6767, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p6769_1]
                          · have p6769_0 := h6769c.1
                            have p6769_1 := h6769c.2.1
                            have p6769_2 := h6769c.2.2.1
                            have p6769_3 := h6769c.2.2.2
                            linarith only [hc01, hc12, hlam, hphi, p6769_1]
                          · have p6769_0 := h6769c.1
                            have p6769_1 := h6769c.2.1
                            have p6769_2 := h6769c.2.2.1
                            have p6769_3 := h6769c.2.2.2
                            linarith only [hlam, p6769_0]
                          · have p6769_0 := h6769c.1
                            have p6769_1 := h6769c.2.1
                            have p6769_2 := h6769c.2.2.1
                            have p6769_3 := h6769c.2.2.2
                            linarith only [h5235, h6504, h6719, h6767, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p6769_1]
                          · have p6769_0 := h6769c.1
                            have p6769_1 := h6769c.2.1
                            have p6769_2 := h6769c.2.2.1
                            have p6769_3 := h6769c.2.2.2
                            linarith only [h6110, h6504, h6719, h6767, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p6769_1]
                          · have p6769_0 := h6769c.1
                            have p6769_1 := h6769c.2.1
                            have p6769_2 := h6769c.2.2.1
                            have p6769_3 := h6769c.2.2.2
                            rcases p6769_3 (m.d 0 1) (by simp) with h6779 | h6779
                            · linarith only [h0, h6779, hlam]
                            · linarith only [h6504, h6779, hlam]
                          · have p6769_0 := h6769c.1
                            have p6769_1 := h6769c.2.1
                            have p6769_2 := h6769c.2.2.1
                            have p6769_3 := h6769c.2.2.2
                            linarith only [h6504, h6719, h6767, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p6769_1]
                          · have p6769_0 := h6769c.1
                            have p6769_1 := h6769c.2.1
                            have p6769_2 := h6769c.2.2.1
                            have p6769_3 := h6769c.2.2.2
                            linarith only [h6717, hlam, p6769_0]
                          · have p6769_0 := h6769c.1
                            have p6769_1 := h6769c.2.1
                            have p6769_2 := h6769c.2.2.1
                            have p6769_3 := h6769c.2.2.2
                            linarith only [hlam, p6769_0]
                          · have p6769_0 := h6769c.1
                            have p6769_1 := h6769c.2.1
                            have p6769_2 := h6769c.2.2.1
                            have p6769_3 := h6769c.2.2.2
                            linarith only [h6720, hlam, p6769_0]
                          · have p6769_0 := h6769c.1
                            have p6769_1 := h6769c.2.1
                            have p6769_2 := h6769c.2.2.1
                            have p6769_3 := h6769c.2.2.2
                            linarith only [h6719, h6720, h6767, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p6769_1]
                          · have p6769_0 := h6769c.1
                            have p6769_1 := h6769c.2.1
                            have p6769_2 := h6769c.2.2.1
                            have p6769_3 := h6769c.2.2.2
                            linarith only [h6504, h6719, h6720, h6767, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p6769_1]
                          · have p6769_0 := h6769c.1
                            have p6769_1 := h6769c.2.1
                            have p6769_2 := h6769c.2.2.1
                            have p6769_3 := h6769c.2.2.2
                            linarith only [h6718, hlam, p6769_0]
                          · have p6769_0 := h6769c.1
                            have p6769_1 := h6769c.2.1
                            have p6769_2 := h6769c.2.2.1
                            have p6769_3 := h6769c.2.2.2
                            linarith only [h6720, hc13, hc34, hlam, hphi, p6769_1]
                          · have p6769_0 := h6769c.1
                            have p6769_1 := h6769c.2.1
                            have p6769_2 := h6769c.2.2.1
                            have p6769_3 := h6769c.2.2.2
                            linarith only [hlam, p6769_0]
                          · have p6769_0 := h6769c.1
                            have p6769_1 := h6769c.2.1
                            have p6769_2 := h6769c.2.2.1
                            have p6769_3 := h6769c.2.2.2
                            rcases p6769_3 (m.d 0 1) (by simp) with h6791 | h6791
                            · linarith only [h6110, h6791, hlam]
                            · linarith only [h6504, h6791, hlam]
                          · have p6769_0 := h6769c.1
                            have p6769_1 := h6769c.2.1
                            have p6769_2 := h6769c.2.2.1
                            have p6769_3 := h6769c.2.2.2
                            linarith only [h6504, hlam, p6769_0]
                          · have p6769_0 := h6769c.1
                            have p6769_1 := h6769c.2.1
                            have p6769_2 := h6769c.2.2.1
                            have p6769_3 := h6769c.2.2.2
                            linarith only [h6719, hlam, p6769_0]
                          · have p6769_0 := h6769c.1
                            have p6769_1 := h6769c.2.1
                            have p6769_2 := h6769c.2.2.1
                            have p6769_3 := h6769c.2.2.2
                            linarith only [h6763, hlam, p6769_0]
                          · have p6769_0 := h6769c.1
                            have p6769_1 := h6769c.2.1
                            have p6769_2 := h6769c.2.2.1
                            have p6769_3 := h6769c.2.2.2
                            linarith only [h6764, hlam, p6769_0]
                          · have p6769_0 := h6769c.1
                            have p6769_1 := h6769c.2.1
                            have p6769_2 := h6769c.2.2.1
                            have p6769_3 := h6769c.2.2.2
                            linarith only [hlam, p6769_0]
                        · linarith only [h6110, h6504, h6719, h6720, h6767, h6768, hlam]
                      · linarith only [h5235, h6504, h6720, h6764, h6767, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                  · linarith only [h6110, h6716, h6764, hlam]
                · linarith only [h5235, h6504, h6763, hlam]
            · linarith only [h0, h6504, h6719, hlam]
          · linarith only [h5235, h6504, h6505, h6717, h6718, hc02, hc15, hlam, hphi, ht0b, ht5b]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h6805 | h6805
          · rcases m.htr 1 2 5 (by decide) (by decide) with h6806 | h6806
            · rcases m.htr 1 3 4 (by decide) (by decide) with h6807 | h6807
              · rcases m.htr 1 3 5 (by decide) (by decide) with h6808 | h6808
                · rcases m.htr 1 4 5 (by decide) (by decide) with h6809 | h6809
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h6810 | h6810
                    · linarith only [h0, h5235, h6504, h6505, h6506, h6717, h6806, h6810, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
                    · linarith only [h0, h6505, h6717, h6807, h6810, hc13, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                  · linarith only [h6506, h6716, h6807, h6809, hlam]
                · linarith only [h5235, h6504, h6506, h6806, h6807, h6808, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
              · linarith only [h6717, h6805, h6807, hlam]
            · linarith only [h0, h6504, h6806, hlam]
          · linarith only [h0, h6505, h6805, hlam]
      · linarith only [h5235, h6504, h6506, h6716, hlam]
  · rcases m.htr 0 3 4 (by decide) (by decide) with h6819 | h6819
    · rcases m.htr 0 4 5 (by decide) (by decide) with h6820 | h6820
      · rcases m.htr 1 2 3 (by decide) (by decide) with h6821 | h6821
        · rcases m.htr 1 2 4 (by decide) (by decide) with h6822 | h6822
          · rcases m.htr 1 2 5 (by decide) (by decide) with h6823 | h6823
            · rcases m.htr 1 3 4 (by decide) (by decide) with h6824 | h6824
              · rcases m.htr 1 3 5 (by decide) (by decide) with h6825 | h6825
                · rcases m.htr 1 4 5 (by decide) (by decide) with h6826 | h6826
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h6827 | h6827
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h6828 | h6828
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h6829 | h6829
                        · rcases h1bigk with h6830c | h6830c | h6830c | h6830c | h6830c | h6830c | h6830c | h6830c | h6830c | h6830c | h6830c | h6830c | h6830c | h6830c | h6830c | h6830c | h6830c | h6830c | h6830c | h6830c | h6830c | h6830c | h6830c | h6830c | h6830c
                          · have p6830_0 := h6830c.1
                            have p6830_1 := h6830c.2.1
                            have p6830_2 := h6830c.2.2.1
                            have p6830_3 := h6830c.2.2.2
                            linarith only [hlam, p6830_0]
                          · have p6830_0 := h6830c.1
                            have p6830_1 := h6830c.2.1
                            have p6830_2 := h6830c.2.2.1
                            have p6830_3 := h6830c.2.2.2
                            linarith only [h0, hlam, p6830_0]
                          · have p6830_0 := h6830c.1
                            have p6830_1 := h6830c.2.1
                            have p6830_2 := h6830c.2.2.1
                            have p6830_3 := h6830c.2.2.2
                            linarith only [h5235, hlam, p6830_0]
                          · have p6830_0 := h6830c.1
                            have p6830_1 := h6830c.2.1
                            have p6830_2 := h6830c.2.2.1
                            have p6830_3 := h6830c.2.2.2
                            linarith only [h6110, hlam, p6830_0]
                          · have p6830_0 := h6830c.1
                            have p6830_1 := h6830c.2.1
                            have p6830_2 := h6830c.2.2.1
                            have p6830_3 := h6830c.2.2.2
                            linarith only [h0, h6505, h6821, h6827, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b, p6830_1]
                          · have p6830_0 := h6830c.1
                            have p6830_1 := h6830c.2.1
                            have p6830_2 := h6830c.2.2.1
                            have p6830_3 := h6830c.2.2.2
                            linarith only [hc01, hc12, hlam, hphi, p6830_1]
                          · have p6830_0 := h6830c.1
                            have p6830_1 := h6830c.2.1
                            have p6830_2 := h6830c.2.2.1
                            have p6830_3 := h6830c.2.2.2
                            linarith only [hlam, p6830_0]
                          · have p6830_0 := h6830c.1
                            have p6830_1 := h6830c.2.1
                            have p6830_2 := h6830c.2.2.1
                            have p6830_3 := h6830c.2.2.2
                            linarith only [h5235, hc01, hc12, hlam, hphi, p6830_1]
                          · have p6830_0 := h6830c.1
                            have p6830_1 := h6830c.2.1
                            have p6830_2 := h6830c.2.2.1
                            have p6830_3 := h6830c.2.2.2
                            linarith only [h6110, h6504, h6823, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p6830_1]
                          · have p6830_0 := h6830c.1
                            have p6830_1 := h6830c.2.1
                            have p6830_2 := h6830c.2.2.1
                            have p6830_3 := h6830c.2.2.2
                            rcases p6830_3 (m.d 0 1) (by simp) with h6840 | h6840
                            · linarith only [h0, h6840, hlam]
                            · linarith only [h6504, h6840, hlam]
                          · have p6830_0 := h6830c.1
                            have p6830_1 := h6830c.2.1
                            have p6830_2 := h6830c.2.2.1
                            have p6830_3 := h6830c.2.2.2
                            linarith only [h6504, h6823, h6828, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p6830_1]
                          · have p6830_0 := h6830c.1
                            have p6830_1 := h6830c.2.1
                            have p6830_2 := h6830c.2.2.1
                            have p6830_3 := h6830c.2.2.2
                            linarith only [h6821, hlam, p6830_0]
                          · have p6830_0 := h6830c.1
                            have p6830_1 := h6830c.2.1
                            have p6830_2 := h6830c.2.2.1
                            have p6830_3 := h6830c.2.2.2
                            linarith only [hlam, p6830_0]
                          · have p6830_0 := h6830c.1
                            have p6830_1 := h6830c.2.1
                            have p6830_2 := h6830c.2.2.1
                            have p6830_3 := h6830c.2.2.2
                            linarith only [h0, h6504, h6505, h6821, h6822, h6823, h6828, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p6830_1]
                          · have p6830_0 := h6830c.1
                            have p6830_1 := h6830c.2.1
                            have p6830_2 := h6830c.2.2.1
                            have p6830_3 := h6830c.2.2.2
                            rcases p6830_3 (m.d 0 1) (by simp) with h6847 | h6847
                            · linarith only [h5235, h6847, hlam]
                            · linarith only [h6504, h6847, hlam]
                          · have p6830_0 := h6830c.1
                            have p6830_1 := h6830c.2.1
                            have p6830_2 := h6830c.2.2.1
                            have p6830_3 := h6830c.2.2.2
                            linarith only [h6504, h6823, h6828, hc14, hc45, hlam, hphi, ht01, ht0b, ht5b, p6830_1]
                          · have p6830_0 := h6830c.1
                            have p6830_1 := h6830c.2.1
                            have p6830_2 := h6830c.2.2.1
                            have p6830_3 := h6830c.2.2.2
                            linarith only [h6822, hlam, p6830_0]
                          · have p6830_0 := h6830c.1
                            have p6830_1 := h6830c.2.1
                            have p6830_2 := h6830c.2.2.1
                            have p6830_3 := h6830c.2.2.2
                            linarith only [h6824, hlam, p6830_1]
                          · have p6830_0 := h6830c.1
                            have p6830_1 := h6830c.2.1
                            have p6830_2 := h6830c.2.2.1
                            have p6830_3 := h6830c.2.2.2
                            linarith only [hlam, p6830_0]
                          · have p6830_0 := h6830c.1
                            have p6830_1 := h6830c.2.1
                            have p6830_2 := h6830c.2.2.1
                            have p6830_3 := h6830c.2.2.2
                            rcases p6830_3 (m.d 0 1) (by simp) with h6854 | h6854
                            · linarith only [h6110, h6854, hlam]
                            · linarith only [h6504, h6854, hlam]
                          · have p6830_0 := h6830c.1
                            have p6830_1 := h6830c.2.1
                            have p6830_2 := h6830c.2.2.1
                            have p6830_3 := h6830c.2.2.2
                            linarith only [h6504, hlam, p6830_0]
                          · have p6830_0 := h6830c.1
                            have p6830_1 := h6830c.2.1
                            have p6830_2 := h6830c.2.2.1
                            have p6830_3 := h6830c.2.2.2
                            linarith only [h6823, hlam, p6830_0]
                          · have p6830_0 := h6830c.1
                            have p6830_1 := h6830c.2.1
                            have p6830_2 := h6830c.2.2.1
                            have p6830_3 := h6830c.2.2.2
                            linarith only [h6825, hlam, p6830_0]
                          · have p6830_0 := h6830c.1
                            have p6830_1 := h6830c.2.1
                            have p6830_2 := h6830c.2.2.1
                            have p6830_3 := h6830c.2.2.2
                            linarith only [h6826, hlam, p6830_0]
                          · have p6830_0 := h6830c.1
                            have p6830_1 := h6830c.2.1
                            have p6830_2 := h6830c.2.2.1
                            have p6830_3 := h6830c.2.2.2
                            linarith only [hlam, p6830_0]
                        · linarith only [h0, h6504, h6505, h6822, h6823, h6828, h6829, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · linarith only [h0, h6504, h6505, h6819, h6820, h6828, hc03, hc15, hlam, hphi, ht0b, ht5b]
                    · linarith only [h6505, h6819, h6827, hlam]
                  · linarith only [h6110, h6820, h6826, hlam]
                · linarith only [h0, h6504, h6505, h6822, h6824, h6825, hlam]
              · linarith only [h5235, h6819, h6824, hlam]
            · linarith only [h0, h6505, h6822, h6823, hc01, hc25, hlam, hphi, ht12]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h6869 | h6869
            · rcases m.htr 1 3 4 (by decide) (by decide) with h6870 | h6870
              · linarith only [h6821, h6822, h6870, hlam]
              · linarith only [h5235, h6819, h6870, hlam]
            · linarith only [h5235, h6504, h6821, h6869, hlam]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h6874 | h6874
          · linarith only [h0, h6505, h6821, h6874, hc01, hc23, hlam, hphi, ht12]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h6876 | h6876
            · rcases m.htr 1 3 4 (by decide) (by decide) with h6877 | h6877
              · rcases m.htr 1 3 5 (by decide) (by decide) with h6878 | h6878
                · rcases m.htr 1 4 5 (by decide) (by decide) with h6879 | h6879
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h6880 | h6880
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h6881 | h6881
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h6882 | h6882
                        · rcases h1bigk with h6883c | h6883c | h6883c | h6883c | h6883c | h6883c | h6883c | h6883c | h6883c | h6883c | h6883c | h6883c | h6883c | h6883c | h6883c | h6883c | h6883c | h6883c | h6883c | h6883c | h6883c | h6883c | h6883c | h6883c | h6883c
                          · have p6883_0 := h6883c.1
                            have p6883_1 := h6883c.2.1
                            have p6883_2 := h6883c.2.2.1
                            have p6883_3 := h6883c.2.2.2
                            linarith only [hlam, p6883_0]
                          · have p6883_0 := h6883c.1
                            have p6883_1 := h6883c.2.1
                            have p6883_2 := h6883c.2.2.1
                            have p6883_3 := h6883c.2.2.2
                            linarith only [h0, hlam, p6883_0]
                          · have p6883_0 := h6883c.1
                            have p6883_1 := h6883c.2.1
                            have p6883_2 := h6883c.2.2.1
                            have p6883_3 := h6883c.2.2.2
                            linarith only [h5235, hlam, p6883_0]
                          · have p6883_0 := h6883c.1
                            have p6883_1 := h6883c.2.1
                            have p6883_2 := h6883c.2.2.1
                            have p6883_3 := h6883c.2.2.2
                            linarith only [h6110, hlam, p6883_0]
                          · have p6883_0 := h6883c.1
                            have p6883_1 := h6883c.2.1
                            have p6883_2 := h6883c.2.2.1
                            have p6883_3 := h6883c.2.2.2
                            linarith only [h0, h6874, h6880, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p6883_1]
                          · have p6883_0 := h6883c.1
                            have p6883_1 := h6883c.2.1
                            have p6883_2 := h6883c.2.2.1
                            have p6883_3 := h6883c.2.2.2
                            linarith only [h6874, h6880, hc01, hc23, hlam, hphi, ht12, p6883_1]
                          · have p6883_0 := h6883c.1
                            have p6883_1 := h6883c.2.1
                            have p6883_2 := h6883c.2.2.1
                            have p6883_3 := h6883c.2.2.2
                            linarith only [hlam, p6883_0]
                          · have p6883_0 := h6883c.1
                            have p6883_1 := h6883c.2.1
                            have p6883_2 := h6883c.2.2.1
                            have p6883_3 := h6883c.2.2.2
                            linarith only [h6821, hlam, p6883_1]
                          · have p6883_0 := h6883c.1
                            have p6883_1 := h6883c.2.1
                            have p6883_2 := h6883c.2.2.1
                            have p6883_3 := h6883c.2.2.2
                            linarith only [h6874, hlam, p6883_1]
                          · have p6883_0 := h6883c.1
                            have p6883_1 := h6883c.2.1
                            have p6883_2 := h6883c.2.2.1
                            have p6883_3 := h6883c.2.2.2
                            linarith only [h6874, h6876, h6880, h6881, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p6883_1]
                          · have p6883_0 := h6883c.1
                            have p6883_1 := h6883c.2.1
                            have p6883_2 := h6883c.2.2.1
                            have p6883_3 := h6883c.2.2.2
                            linarith only [h6504, h6876, h6881, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p6883_1]
                          · have p6883_0 := h6883c.1
                            have p6883_1 := h6883c.2.1
                            have p6883_2 := h6883c.2.2.1
                            have p6883_3 := h6883c.2.2.2
                            linarith only [h0, h6821, hc02, hc23, hlam, hphi, p6883_1]
                          · have p6883_0 := h6883c.1
                            have p6883_1 := h6883c.2.1
                            have p6883_2 := h6883c.2.2.1
                            have p6883_3 := h6883c.2.2.2
                            linarith only [hlam, p6883_0]
                          · have p6883_0 := h6883c.1
                            have p6883_1 := h6883c.2.1
                            have p6883_2 := h6883c.2.2.1
                            have p6883_3 := h6883c.2.2.2
                            linarith only [h6110, h6504, h6821, h6876, h6881, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p6883_1]
                          · have p6883_0 := h6883c.1
                            have p6883_1 := h6883c.2.1
                            have p6883_2 := h6883c.2.2.1
                            have p6883_3 := h6883c.2.2.2
                            rcases p6883_3 (m.d 0 1) (by simp) with h6898 | h6898
                            · linarith only [h5235, h6898, hlam]
                            · linarith only [h6504, h6898, hlam]
                          · have p6883_0 := h6883c.1
                            have p6883_1 := h6883c.2.1
                            have p6883_2 := h6883c.2.2.1
                            have p6883_3 := h6883c.2.2.2
                            linarith only [h6504, h6876, h6881, hc14, hc45, hlam, hphi, ht01, ht0b, ht5b, p6883_1]
                          · have p6883_0 := h6883c.1
                            have p6883_1 := h6883c.2.1
                            have p6883_2 := h6883c.2.2.1
                            have p6883_3 := h6883c.2.2.2
                            linarith only [h0, h6504, h6874, h6876, h6880, h6881, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p6883_1]
                          · have p6883_0 := h6883c.1
                            have p6883_1 := h6883c.2.1
                            have p6883_2 := h6883c.2.2.1
                            have p6883_3 := h6883c.2.2.2
                            linarith only [h6877, hlam, p6883_1]
                          · have p6883_0 := h6883c.1
                            have p6883_1 := h6883c.2.1
                            have p6883_2 := h6883c.2.2.1
                            have p6883_3 := h6883c.2.2.2
                            linarith only [hlam, p6883_0]
                          · have p6883_0 := h6883c.1
                            have p6883_1 := h6883c.2.1
                            have p6883_2 := h6883c.2.2.1
                            have p6883_3 := h6883c.2.2.2
                            rcases p6883_3 (m.d 0 1) (by simp) with h6905 | h6905
                            · linarith only [h6110, h6905, hlam]
                            · linarith only [h6504, h6905, hlam]
                          · have p6883_0 := h6883c.1
                            have p6883_1 := h6883c.2.1
                            have p6883_2 := h6883c.2.2.1
                            have p6883_3 := h6883c.2.2.2
                            linarith only [h6504, hlam, p6883_0]
                          · have p6883_0 := h6883c.1
                            have p6883_1 := h6883c.2.1
                            have p6883_2 := h6883c.2.2.1
                            have p6883_3 := h6883c.2.2.2
                            linarith only [h6876, hlam, p6883_0]
                          · have p6883_0 := h6883c.1
                            have p6883_1 := h6883c.2.1
                            have p6883_2 := h6883c.2.2.1
                            have p6883_3 := h6883c.2.2.2
                            linarith only [h6878, hlam, p6883_0]
                          · have p6883_0 := h6883c.1
                            have p6883_1 := h6883c.2.1
                            have p6883_2 := h6883c.2.2.1
                            have p6883_3 := h6883c.2.2.2
                            linarith only [h6879, hlam, p6883_0]
                          · have p6883_0 := h6883c.1
                            have p6883_1 := h6883c.2.1
                            have p6883_2 := h6883c.2.2.1
                            have p6883_3 := h6883c.2.2.2
                            linarith only [hlam, p6883_0]
                        · linarith only [h0, h6504, h6821, h6876, h6881, h6882, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · linarith only [h0, h6874, h6881, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                    · linarith only [h5235, h6819, h6821, h6880, hlam]
                  · linarith only [h0, h5235, h6819, h6820, h6874, h6879, hc01, hc13, hlam, hphi]
                · linarith only [h0, h6504, h6874, h6877, h6878, hlam]
              · linarith only [h5235, h6504, h6819, h6877, hc03, hc15, hlam, hphi, ht0b, ht5b]
            · linarith only [h0, h6504, h6876, hlam]
      · linarith only [h0, h6504, h6505, h6820, hlam]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h6921 | h6921
      · rcases m.htr 1 2 3 (by decide) (by decide) with h6922 | h6922
        · rcases m.htr 1 2 4 (by decide) (by decide) with h6923 | h6923
          · rcases m.htr 1 2 5 (by decide) (by decide) with h6924 | h6924
            · rcases m.htr 1 3 4 (by decide) (by decide) with h6925 | h6925
              · rcases m.htr 1 3 5 (by decide) (by decide) with h6926 | h6926
                · rcases m.htr 1 4 5 (by decide) (by decide) with h6927 | h6927
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h6928 | h6928
                    · linarith only [h5235, h6504, h6819, h6922, h6924, h6928, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h6930 | h6930
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h6931 | h6931
                        · rcases h1bigk with h6932c | h6932c | h6932c | h6932c | h6932c | h6932c | h6932c | h6932c | h6932c | h6932c | h6932c | h6932c | h6932c | h6932c | h6932c | h6932c | h6932c | h6932c | h6932c | h6932c | h6932c | h6932c | h6932c | h6932c | h6932c
                          · have p6932_0 := h6932c.1
                            have p6932_1 := h6932c.2.1
                            have p6932_2 := h6932c.2.2.1
                            have p6932_3 := h6932c.2.2.2
                            linarith only [hlam, p6932_0]
                          · have p6932_0 := h6932c.1
                            have p6932_1 := h6932c.2.1
                            have p6932_2 := h6932c.2.2.1
                            have p6932_3 := h6932c.2.2.2
                            linarith only [h0, hlam, p6932_0]
                          · have p6932_0 := h6932c.1
                            have p6932_1 := h6932c.2.1
                            have p6932_2 := h6932c.2.2.1
                            have p6932_3 := h6932c.2.2.2
                            linarith only [h5235, hlam, p6932_0]
                          · have p6932_0 := h6932c.1
                            have p6932_1 := h6932c.2.1
                            have p6932_2 := h6932c.2.2.1
                            have p6932_3 := h6932c.2.2.2
                            linarith only [h6110, hlam, p6932_0]
                          · have p6932_0 := h6932c.1
                            have p6932_1 := h6932c.2.1
                            have p6932_2 := h6932c.2.2.1
                            have p6932_3 := h6932c.2.2.2
                            linarith only [h0, h6505, h6924, h6925, h6928, h6930, hc14, hc45, hlam, hphi, ht01, ht0b, ht5b, p6932_1]
                          · have p6932_0 := h6932c.1
                            have p6932_1 := h6932c.2.1
                            have p6932_2 := h6932c.2.2.1
                            have p6932_3 := h6932c.2.2.2
                            linarith only [hc01, hc12, hlam, hphi, p6932_1]
                          · have p6932_0 := h6932c.1
                            have p6932_1 := h6932c.2.1
                            have p6932_2 := h6932c.2.2.1
                            have p6932_3 := h6932c.2.2.2
                            linarith only [hlam, p6932_0]
                          · have p6932_0 := h6932c.1
                            have p6932_1 := h6932c.2.1
                            have p6932_2 := h6932c.2.2.1
                            have p6932_3 := h6932c.2.2.2
                            linarith only [h5235, hc01, hc12, hlam, hphi, p6932_1]
                          · have p6932_0 := h6932c.1
                            have p6932_1 := h6932c.2.1
                            have p6932_2 := h6932c.2.2.1
                            have p6932_3 := h6932c.2.2.2
                            linarith only [h6110, h6504, h6924, h6930, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p6932_1]
                          · have p6932_0 := h6932c.1
                            have p6932_1 := h6932c.2.1
                            have p6932_2 := h6932c.2.2.1
                            have p6932_3 := h6932c.2.2.2
                            rcases p6932_3 (m.d 0 1) (by simp) with h6942 | h6942
                            · linarith only [h0, h6942, hlam]
                            · linarith only [h6504, h6942, hlam]
                          · have p6932_0 := h6932c.1
                            have p6932_1 := h6932c.2.1
                            have p6932_2 := h6932c.2.2.1
                            have p6932_3 := h6932c.2.2.2
                            linarith only [h6504, h6924, h6930, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p6932_1]
                          · have p6932_0 := h6932c.1
                            have p6932_1 := h6932c.2.1
                            have p6932_2 := h6932c.2.2.1
                            have p6932_3 := h6932c.2.2.2
                            linarith only [h6922, hlam, p6932_0]
                          · have p6932_0 := h6932c.1
                            have p6932_1 := h6932c.2.1
                            have p6932_2 := h6932c.2.2.1
                            have p6932_3 := h6932c.2.2.2
                            linarith only [hlam, p6932_0]
                          · have p6932_0 := h6932c.1
                            have p6932_1 := h6932c.2.1
                            have p6932_2 := h6932c.2.2.1
                            have p6932_3 := h6932c.2.2.2
                            linarith only [h0, h6504, h6505, h6922, h6924, h6925, h6928, h6930, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p6932_1]
                          · have p6932_0 := h6932c.1
                            have p6932_1 := h6932c.2.1
                            have p6932_2 := h6932c.2.2.1
                            have p6932_3 := h6932c.2.2.2
                            rcases p6932_3 (m.d 0 1) (by simp) with h6949 | h6949
                            · linarith only [h5235, h6949, hlam]
                            · linarith only [h6504, h6949, hlam]
                          · have p6932_0 := h6932c.1
                            have p6932_1 := h6932c.2.1
                            have p6932_2 := h6932c.2.2.1
                            have p6932_3 := h6932c.2.2.2
                            linarith only [h6504, h6924, h6930, hc14, hc45, hlam, hphi, ht01, ht0b, ht5b, p6932_1]
                          · have p6932_0 := h6932c.1
                            have p6932_1 := h6932c.2.1
                            have p6932_2 := h6932c.2.2.1
                            have p6932_3 := h6932c.2.2.2
                            linarith only [h6923, hlam, p6932_0]
                          · have p6932_0 := h6932c.1
                            have p6932_1 := h6932c.2.1
                            have p6932_2 := h6932c.2.2.1
                            have p6932_3 := h6932c.2.2.2
                            linarith only [h6925, hlam, p6932_1]
                          · have p6932_0 := h6932c.1
                            have p6932_1 := h6932c.2.1
                            have p6932_2 := h6932c.2.2.1
                            have p6932_3 := h6932c.2.2.2
                            linarith only [hlam, p6932_0]
                          · have p6932_0 := h6932c.1
                            have p6932_1 := h6932c.2.1
                            have p6932_2 := h6932c.2.2.1
                            have p6932_3 := h6932c.2.2.2
                            rcases p6932_3 (m.d 0 1) (by simp) with h6956 | h6956
                            · linarith only [h6110, h6956, hlam]
                            · linarith only [h6504, h6956, hlam]
                          · have p6932_0 := h6932c.1
                            have p6932_1 := h6932c.2.1
                            have p6932_2 := h6932c.2.2.1
                            have p6932_3 := h6932c.2.2.2
                            linarith only [h6504, hlam, p6932_0]
                          · have p6932_0 := h6932c.1
                            have p6932_1 := h6932c.2.1
                            have p6932_2 := h6932c.2.2.1
                            have p6932_3 := h6932c.2.2.2
                            linarith only [h6924, hlam, p6932_0]
                          · have p6932_0 := h6932c.1
                            have p6932_1 := h6932c.2.1
                            have p6932_2 := h6932c.2.2.1
                            have p6932_3 := h6932c.2.2.2
                            linarith only [h6926, hlam, p6932_0]
                          · have p6932_0 := h6932c.1
                            have p6932_1 := h6932c.2.1
                            have p6932_2 := h6932c.2.2.1
                            have p6932_3 := h6932c.2.2.2
                            linarith only [h6927, hlam, p6932_0]
                          · have p6932_0 := h6932c.1
                            have p6932_1 := h6932c.2.1
                            have p6932_2 := h6932c.2.2.1
                            have p6932_3 := h6932c.2.2.2
                            linarith only [hlam, p6932_0]
                        · linarith only [h0, h6504, h6505, h6924, h6928, h6930, h6931, hlam]
                      · linarith only [h0, h6504, h6505, h6921, h6924, h6930, hc04, hc25, hlam, hphi, ht0b, ht5b]
                  · linarith only [h6110, h6504, h6921, h6927, hlam]
                · linarith only [h5235, h6819, h6925, h6926, hc01, hc35, hlam, hphi, ht12, ht23]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h6968 | h6968
                · rcases m.htr 1 4 5 (by decide) (by decide) with h6969 | h6969
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h6970 | h6970
                    · linarith only [h5235, h6504, h6924, h6925, h6970, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h6972 | h6972
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h6973 | h6973
                        · rcases h1bigk with h6974c | h6974c | h6974c | h6974c | h6974c | h6974c | h6974c | h6974c | h6974c | h6974c | h6974c | h6974c | h6974c | h6974c | h6974c | h6974c | h6974c | h6974c | h6974c | h6974c | h6974c | h6974c | h6974c | h6974c | h6974c
                          · have p6974_0 := h6974c.1
                            have p6974_1 := h6974c.2.1
                            have p6974_2 := h6974c.2.2.1
                            have p6974_3 := h6974c.2.2.2
                            linarith only [hlam, p6974_0]
                          · have p6974_0 := h6974c.1
                            have p6974_1 := h6974c.2.1
                            have p6974_2 := h6974c.2.2.1
                            have p6974_3 := h6974c.2.2.2
                            linarith only [h0, hlam, p6974_0]
                          · have p6974_0 := h6974c.1
                            have p6974_1 := h6974c.2.1
                            have p6974_2 := h6974c.2.2.1
                            have p6974_3 := h6974c.2.2.2
                            linarith only [h5235, hlam, p6974_0]
                          · have p6974_0 := h6974c.1
                            have p6974_1 := h6974c.2.1
                            have p6974_2 := h6974c.2.2.1
                            have p6974_3 := h6974c.2.2.2
                            linarith only [h6110, hlam, p6974_0]
                          · have p6974_0 := h6974c.1
                            have p6974_1 := h6974c.2.1
                            have p6974_2 := h6974c.2.2.1
                            have p6974_3 := h6974c.2.2.2
                            linarith only [h5235, h6924, h6972, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p6974_1]
                          · have p6974_0 := h6974c.1
                            have p6974_1 := h6974c.2.1
                            have p6974_2 := h6974c.2.2.1
                            have p6974_3 := h6974c.2.2.2
                            linarith only [hc01, hc12, hlam, hphi, p6974_1]
                          · have p6974_0 := h6974c.1
                            have p6974_1 := h6974c.2.1
                            have p6974_2 := h6974c.2.2.1
                            have p6974_3 := h6974c.2.2.2
                            linarith only [hlam, p6974_0]
                          · have p6974_0 := h6974c.1
                            have p6974_1 := h6974c.2.1
                            have p6974_2 := h6974c.2.2.1
                            have p6974_3 := h6974c.2.2.2
                            linarith only [h5235, h6504, h6924, h6972, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p6974_1]
                          · have p6974_0 := h6974c.1
                            have p6974_1 := h6974c.2.1
                            have p6974_2 := h6974c.2.2.1
                            have p6974_3 := h6974c.2.2.2
                            linarith only [h6110, h6504, h6924, h6972, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p6974_1]
                          · have p6974_0 := h6974c.1
                            have p6974_1 := h6974c.2.1
                            have p6974_2 := h6974c.2.2.1
                            have p6974_3 := h6974c.2.2.2
                            rcases p6974_3 (m.d 0 1) (by simp) with h6984 | h6984
                            · linarith only [h0, h6984, hlam]
                            · linarith only [h6504, h6984, hlam]
                          · have p6974_0 := h6974c.1
                            have p6974_1 := h6974c.2.1
                            have p6974_2 := h6974c.2.2.1
                            have p6974_3 := h6974c.2.2.2
                            linarith only [h6504, h6924, h6972, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p6974_1]
                          · have p6974_0 := h6974c.1
                            have p6974_1 := h6974c.2.1
                            have p6974_2 := h6974c.2.2.1
                            have p6974_3 := h6974c.2.2.2
                            linarith only [h6922, hlam, p6974_0]
                          · have p6974_0 := h6974c.1
                            have p6974_1 := h6974c.2.1
                            have p6974_2 := h6974c.2.2.1
                            have p6974_3 := h6974c.2.2.2
                            linarith only [hlam, p6974_0]
                          · have p6974_0 := h6974c.1
                            have p6974_1 := h6974c.2.1
                            have p6974_2 := h6974c.2.2.1
                            have p6974_3 := h6974c.2.2.2
                            linarith only [h6925, hlam, p6974_0]
                          · have p6974_0 := h6974c.1
                            have p6974_1 := h6974c.2.1
                            have p6974_2 := h6974c.2.2.1
                            have p6974_3 := h6974c.2.2.2
                            linarith only [h6924, h6925, h6972, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p6974_1]
                          · have p6974_0 := h6974c.1
                            have p6974_1 := h6974c.2.1
                            have p6974_2 := h6974c.2.2.1
                            have p6974_3 := h6974c.2.2.2
                            linarith only [h6504, h6924, h6972, hc14, hc45, hlam, hphi, ht01, ht0b, ht5b, p6974_1]
                          · have p6974_0 := h6974c.1
                            have p6974_1 := h6974c.2.1
                            have p6974_2 := h6974c.2.2.1
                            have p6974_3 := h6974c.2.2.2
                            linarith only [h6923, hlam, p6974_0]
                          · have p6974_0 := h6974c.1
                            have p6974_1 := h6974c.2.1
                            have p6974_2 := h6974c.2.2.1
                            have p6974_3 := h6974c.2.2.2
                            linarith only [h6925, hc13, hc34, hlam, hphi, p6974_1]
                          · have p6974_0 := h6974c.1
                            have p6974_1 := h6974c.2.1
                            have p6974_2 := h6974c.2.2.1
                            have p6974_3 := h6974c.2.2.2
                            linarith only [hlam, p6974_0]
                          · have p6974_0 := h6974c.1
                            have p6974_1 := h6974c.2.1
                            have p6974_2 := h6974c.2.2.1
                            have p6974_3 := h6974c.2.2.2
                            rcases p6974_3 (m.d 0 1) (by simp) with h6996 | h6996
                            · linarith only [h6110, h6996, hlam]
                            · linarith only [h6504, h6996, hlam]
                          · have p6974_0 := h6974c.1
                            have p6974_1 := h6974c.2.1
                            have p6974_2 := h6974c.2.2.1
                            have p6974_3 := h6974c.2.2.2
                            linarith only [h6504, hlam, p6974_0]
                          · have p6974_0 := h6974c.1
                            have p6974_1 := h6974c.2.1
                            have p6974_2 := h6974c.2.2.1
                            have p6974_3 := h6974c.2.2.2
                            linarith only [h6924, hlam, p6974_0]
                          · have p6974_0 := h6974c.1
                            have p6974_1 := h6974c.2.1
                            have p6974_2 := h6974c.2.2.1
                            have p6974_3 := h6974c.2.2.2
                            linarith only [h6968, hlam, p6974_0]
                          · have p6974_0 := h6974c.1
                            have p6974_1 := h6974c.2.1
                            have p6974_2 := h6974c.2.2.1
                            have p6974_3 := h6974c.2.2.2
                            linarith only [h6969, hlam, p6974_0]
                          · have p6974_0 := h6974c.1
                            have p6974_1 := h6974c.2.1
                            have p6974_2 := h6974c.2.2.1
                            have p6974_3 := h6974c.2.2.2
                            linarith only [hlam, p6974_0]
                        · linarith only [h6110, h6504, h6924, h6925, h6972, h6973, hlam]
                      · linarith only [h6505, h6921, h6972, hlam]
                  · linarith only [h0, h6504, h6505, h6921, h6923, h6969, hlam]
                · linarith only [h5235, h6504, h6968, hlam]
            · linarith only [h0, h6505, h6923, h6924, hc01, hc25, hlam, hphi, ht12]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h7009 | h7009
            · rcases m.htr 1 3 4 (by decide) (by decide) with h7010 | h7010
              · linarith only [h5235, h6504, h6819, h6922, h6923, h7009, h7010, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h7012 | h7012
                · rcases m.htr 1 4 5 (by decide) (by decide) with h7013 | h7013
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h7014 | h7014
                    · linarith only [h6110, h6504, h6922, h6923, h7009, h7010, h7014, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h7016 | h7016
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h7017 | h7017
                        · rcases h1bigk with h7018c | h7018c | h7018c | h7018c | h7018c | h7018c | h7018c | h7018c | h7018c | h7018c | h7018c | h7018c | h7018c | h7018c | h7018c | h7018c | h7018c | h7018c | h7018c | h7018c | h7018c | h7018c | h7018c | h7018c | h7018c
                          · have p7018_0 := h7018c.1
                            have p7018_1 := h7018c.2.1
                            have p7018_2 := h7018c.2.2.1
                            have p7018_3 := h7018c.2.2.2
                            linarith only [hlam, p7018_0]
                          · have p7018_0 := h7018c.1
                            have p7018_1 := h7018c.2.1
                            have p7018_2 := h7018c.2.2.1
                            have p7018_3 := h7018c.2.2.2
                            linarith only [h0, hlam, p7018_0]
                          · have p7018_0 := h7018c.1
                            have p7018_1 := h7018c.2.1
                            have p7018_2 := h7018c.2.2.1
                            have p7018_3 := h7018c.2.2.2
                            linarith only [h5235, hlam, p7018_0]
                          · have p7018_0 := h7018c.1
                            have p7018_1 := h7018c.2.1
                            have p7018_2 := h7018c.2.2.1
                            have p7018_3 := h7018c.2.2.2
                            linarith only [h6110, hlam, p7018_0]
                          · have p7018_0 := h7018c.1
                            have p7018_1 := h7018c.2.1
                            have p7018_2 := h7018c.2.2.1
                            have p7018_3 := h7018c.2.2.2
                            linarith only [h5235, h6922, h7009, h7016, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p7018_1]
                          · have p7018_0 := h7018c.1
                            have p7018_1 := h7018c.2.1
                            have p7018_2 := h7018c.2.2.1
                            have p7018_3 := h7018c.2.2.2
                            linarith only [h6923, hc01, hc14, hlam, hphi, p7018_1]
                          · have p7018_0 := h7018c.1
                            have p7018_1 := h7018c.2.1
                            have p7018_2 := h7018c.2.2.1
                            have p7018_3 := h7018c.2.2.2
                            linarith only [hlam, p7018_0]
                          · have p7018_0 := h7018c.1
                            have p7018_1 := h7018c.2.1
                            have p7018_2 := h7018c.2.2.1
                            have p7018_3 := h7018c.2.2.2
                            linarith only [h5235, h6923, hc01, hc14, hlam, hphi, p7018_1]
                          · have p7018_0 := h7018c.1
                            have p7018_1 := h7018c.2.1
                            have p7018_2 := h7018c.2.2.1
                            have p7018_3 := h7018c.2.2.2
                            linarith only [h6923, hlam, p7018_1]
                          · have p7018_0 := h7018c.1
                            have p7018_1 := h7018c.2.1
                            have p7018_2 := h7018c.2.2.1
                            have p7018_3 := h7018c.2.2.2
                            linarith only [h6923, h7009, h7014, h7016, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p7018_1]
                          · have p7018_0 := h7018c.1
                            have p7018_1 := h7018c.2.1
                            have p7018_2 := h7018c.2.2.1
                            have p7018_3 := h7018c.2.2.2
                            linarith only [h6504, h7009, h7016, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p7018_1]
                          · have p7018_0 := h7018c.1
                            have p7018_1 := h7018c.2.1
                            have p7018_2 := h7018c.2.2.1
                            have p7018_3 := h7018c.2.2.2
                            linarith only [h6922, hlam, p7018_0]
                          · have p7018_0 := h7018c.1
                            have p7018_1 := h7018c.2.1
                            have p7018_2 := h7018c.2.2.1
                            have p7018_3 := h7018c.2.2.2
                            linarith only [hlam, p7018_0]
                          · have p7018_0 := h7018c.1
                            have p7018_1 := h7018c.2.1
                            have p7018_2 := h7018c.2.2.1
                            have p7018_3 := h7018c.2.2.2
                            linarith only [h7010, hlam, p7018_0]
                          · have p7018_0 := h7018c.1
                            have p7018_1 := h7018c.2.1
                            have p7018_2 := h7018c.2.2.1
                            have p7018_3 := h7018c.2.2.2
                            linarith only [h6922, h6923, h7009, h7014, h7016, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p7018_1]
                          · have p7018_0 := h7018c.1
                            have p7018_1 := h7018c.2.1
                            have p7018_2 := h7018c.2.2.1
                            have p7018_3 := h7018c.2.2.2
                            linarith only [h6504, h6923, h7009, h7014, h7016, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p7018_1]
                          · have p7018_0 := h7018c.1
                            have p7018_1 := h7018c.2.1
                            have p7018_2 := h7018c.2.2.1
                            have p7018_3 := h7018c.2.2.2
                            linarith only [h6923, h7014, hc12, hc34, hlam, hphi, ht23, p7018_1]
                          · have p7018_0 := h7018c.1
                            have p7018_1 := h7018c.2.1
                            have p7018_2 := h7018c.2.2.1
                            have p7018_3 := h7018c.2.2.2
                            linarith only [h5235, h6504, h6923, h7009, h7014, h7016, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p7018_1]
                          · have p7018_0 := h7018c.1
                            have p7018_1 := h7018c.2.1
                            have p7018_2 := h7018c.2.2.1
                            have p7018_3 := h7018c.2.2.2
                            linarith only [hlam, p7018_0]
                          · have p7018_0 := h7018c.1
                            have p7018_1 := h7018c.2.1
                            have p7018_2 := h7018c.2.2.1
                            have p7018_3 := h7018c.2.2.2
                            rcases p7018_3 (m.d 0 1) (by simp) with h7038 | h7038
                            · linarith only [h6110, h7038, hlam]
                            · linarith only [h6504, h7038, hlam]
                          · have p7018_0 := h7018c.1
                            have p7018_1 := h7018c.2.1
                            have p7018_2 := h7018c.2.2.1
                            have p7018_3 := h7018c.2.2.2
                            linarith only [h6504, hlam, p7018_0]
                          · have p7018_0 := h7018c.1
                            have p7018_1 := h7018c.2.1
                            have p7018_2 := h7018c.2.2.1
                            have p7018_3 := h7018c.2.2.2
                            linarith only [h7009, hlam, p7018_0]
                          · have p7018_0 := h7018c.1
                            have p7018_1 := h7018c.2.1
                            have p7018_2 := h7018c.2.2.1
                            have p7018_3 := h7018c.2.2.2
                            linarith only [h7012, hlam, p7018_0]
                          · have p7018_0 := h7018c.1
                            have p7018_1 := h7018c.2.1
                            have p7018_2 := h7018c.2.2.1
                            have p7018_3 := h7018c.2.2.2
                            linarith only [h7013, hlam, p7018_0]
                          · have p7018_0 := h7018c.1
                            have p7018_1 := h7018c.2.1
                            have p7018_2 := h7018c.2.2.1
                            have p7018_3 := h7018c.2.2.2
                            linarith only [hlam, p7018_0]
                        · linarith only [h6110, h6504, h6923, h7009, h7014, h7016, h7017, hlam]
                      · linarith only [h5235, h6922, h6923, h7016, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                  · linarith only [h5235, h6504, h6921, h6922, h6923, h7013, hc04, hc15, hlam, hphi, ht0b, ht5b]
                · linarith only [h5235, h6504, h7012, hlam]
            · linarith only [h5235, h6504, h6922, h7009, hlam]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h7051 | h7051
          · linarith only [h0, h6505, h6922, h7051, hc01, hc23, hlam, hphi, ht12]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h7053 | h7053
            · rcases m.htr 1 3 4 (by decide) (by decide) with h7054 | h7054
              · rcases m.htr 1 3 5 (by decide) (by decide) with h7055 | h7055
                · rcases m.htr 1 4 5 (by decide) (by decide) with h7056 | h7056
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h7057 | h7057
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h7058 | h7058
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h7059 | h7059
                        · rcases h1bigk with h7060c | h7060c | h7060c | h7060c | h7060c | h7060c | h7060c | h7060c | h7060c | h7060c | h7060c | h7060c | h7060c | h7060c | h7060c | h7060c | h7060c | h7060c | h7060c | h7060c | h7060c | h7060c | h7060c | h7060c | h7060c
                          · have p7060_0 := h7060c.1
                            have p7060_1 := h7060c.2.1
                            have p7060_2 := h7060c.2.2.1
                            have p7060_3 := h7060c.2.2.2
                            linarith only [hlam, p7060_0]
                          · have p7060_0 := h7060c.1
                            have p7060_1 := h7060c.2.1
                            have p7060_2 := h7060c.2.2.1
                            have p7060_3 := h7060c.2.2.2
                            linarith only [h0, hlam, p7060_0]
                          · have p7060_0 := h7060c.1
                            have p7060_1 := h7060c.2.1
                            have p7060_2 := h7060c.2.2.1
                            have p7060_3 := h7060c.2.2.2
                            linarith only [h5235, hlam, p7060_0]
                          · have p7060_0 := h7060c.1
                            have p7060_1 := h7060c.2.1
                            have p7060_2 := h7060c.2.2.1
                            have p7060_3 := h7060c.2.2.2
                            linarith only [h6110, hlam, p7060_0]
                          · have p7060_0 := h7060c.1
                            have p7060_1 := h7060c.2.1
                            have p7060_2 := h7060c.2.2.1
                            have p7060_3 := h7060c.2.2.2
                            linarith only [h0, h7051, h7053, h7057, h7058, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p7060_1]
                          · have p7060_0 := h7060c.1
                            have p7060_1 := h7060c.2.1
                            have p7060_2 := h7060c.2.2.1
                            have p7060_3 := h7060c.2.2.2
                            linarith only [h7051, h7057, hc01, hc23, hlam, hphi, ht12, p7060_1]
                          · have p7060_0 := h7060c.1
                            have p7060_1 := h7060c.2.1
                            have p7060_2 := h7060c.2.2.1
                            have p7060_3 := h7060c.2.2.2
                            linarith only [hlam, p7060_0]
                          · have p7060_0 := h7060c.1
                            have p7060_1 := h7060c.2.1
                            have p7060_2 := h7060c.2.2.1
                            have p7060_3 := h7060c.2.2.2
                            linarith only [h6922, hlam, p7060_1]
                          · have p7060_0 := h7060c.1
                            have p7060_1 := h7060c.2.1
                            have p7060_2 := h7060c.2.2.1
                            have p7060_3 := h7060c.2.2.2
                            linarith only [h7051, hlam, p7060_1]
                          · have p7060_0 := h7060c.1
                            have p7060_1 := h7060c.2.1
                            have p7060_2 := h7060c.2.2.1
                            have p7060_3 := h7060c.2.2.2
                            linarith only [h7051, h7053, h7057, h7058, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p7060_1]
                          · have p7060_0 := h7060c.1
                            have p7060_1 := h7060c.2.1
                            have p7060_2 := h7060c.2.2.1
                            have p7060_3 := h7060c.2.2.2
                            linarith only [h6504, h6922, h7053, h7058, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p7060_1]
                          · have p7060_0 := h7060c.1
                            have p7060_1 := h7060c.2.1
                            have p7060_2 := h7060c.2.2.1
                            have p7060_3 := h7060c.2.2.2
                            linarith only [h6922, hc12, hc23, hlam, hphi, p7060_1]
                          · have p7060_0 := h7060c.1
                            have p7060_1 := h7060c.2.1
                            have p7060_2 := h7060c.2.2.1
                            have p7060_3 := h7060c.2.2.2
                            linarith only [hlam, p7060_0]
                          · have p7060_0 := h7060c.1
                            have p7060_1 := h7060c.2.1
                            have p7060_2 := h7060c.2.2.1
                            have p7060_3 := h7060c.2.2.2
                            linarith only [h0, h6504, h6922, h7051, h7053, h7058, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p7060_1]
                          · have p7060_0 := h7060c.1
                            have p7060_1 := h7060c.2.1
                            have p7060_2 := h7060c.2.2.1
                            have p7060_3 := h7060c.2.2.2
                            rcases p7060_3 (m.d 0 1) (by simp) with h7075 | h7075
                            · linarith only [h5235, h7075, hlam]
                            · linarith only [h6504, h7075, hlam]
                          · have p7060_0 := h7060c.1
                            have p7060_1 := h7060c.2.1
                            have p7060_2 := h7060c.2.2.1
                            have p7060_3 := h7060c.2.2.2
                            linarith only [h6504, h7053, h7058, hc14, hc45, hlam, hphi, ht01, ht0b, ht5b, p7060_1]
                          · have p7060_0 := h7060c.1
                            have p7060_1 := h7060c.2.1
                            have p7060_2 := h7060c.2.2.1
                            have p7060_3 := h7060c.2.2.2
                            linarith only [h0, h6504, h7051, h7053, h7057, h7058, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p7060_1]
                          · have p7060_0 := h7060c.1
                            have p7060_1 := h7060c.2.1
                            have p7060_2 := h7060c.2.2.1
                            have p7060_3 := h7060c.2.2.2
                            linarith only [h7054, hlam, p7060_1]
                          · have p7060_0 := h7060c.1
                            have p7060_1 := h7060c.2.1
                            have p7060_2 := h7060c.2.2.1
                            have p7060_3 := h7060c.2.2.2
                            linarith only [hlam, p7060_0]
                          · have p7060_0 := h7060c.1
                            have p7060_1 := h7060c.2.1
                            have p7060_2 := h7060c.2.2.1
                            have p7060_3 := h7060c.2.2.2
                            rcases p7060_3 (m.d 0 1) (by simp) with h7082 | h7082
                            · linarith only [h6110, h7082, hlam]
                            · linarith only [h6504, h7082, hlam]
                          · have p7060_0 := h7060c.1
                            have p7060_1 := h7060c.2.1
                            have p7060_2 := h7060c.2.2.1
                            have p7060_3 := h7060c.2.2.2
                            linarith only [h6504, hlam, p7060_0]
                          · have p7060_0 := h7060c.1
                            have p7060_1 := h7060c.2.1
                            have p7060_2 := h7060c.2.2.1
                            have p7060_3 := h7060c.2.2.2
                            linarith only [h7053, hlam, p7060_0]
                          · have p7060_0 := h7060c.1
                            have p7060_1 := h7060c.2.1
                            have p7060_2 := h7060c.2.2.1
                            have p7060_3 := h7060c.2.2.2
                            linarith only [h7055, hlam, p7060_0]
                          · have p7060_0 := h7060c.1
                            have p7060_1 := h7060c.2.1
                            have p7060_2 := h7060c.2.2.1
                            have p7060_3 := h7060c.2.2.2
                            linarith only [h7056, hlam, p7060_0]
                          · have p7060_0 := h7060c.1
                            have p7060_1 := h7060c.2.1
                            have p7060_2 := h7060c.2.2.1
                            have p7060_3 := h7060c.2.2.2
                            linarith only [hlam, p7060_0]
                        · linarith only [h5235, h6504, h6819, h7053, h7058, h7059, hlam]
                      · linarith only [h6110, h6921, h7051, h7058, hlam]
                    · linarith only [h0, h6504, h6922, h7053, h7054, h7057, hc14, hc25, hlam, hphi, ht01, ht0b, ht5b]
                  · linarith only [h6110, h6921, h7056, hlam]
                · linarith only [h5235, h6504, h6819, h7053, h7054, h7055, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h7095 | h7095
                · rcases m.htr 1 4 5 (by decide) (by decide) with h7096 | h7096
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h7097 | h7097
                    · linarith only [h0, h6504, h6922, h7053, h7054, h7097, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
                    · linarith only [h0, h6504, h6922, h7053, h7097, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                  · linarith only [h6110, h6921, h7096, hlam]
                · linarith only [h0, h6504, h6922, h7095, hlam]
            · linarith only [h0, h6504, h7053, hlam]
      · linarith only [h6110, h6504, h6921, hlam]

end R2N4
