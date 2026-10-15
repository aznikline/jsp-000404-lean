import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_71S5

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_11_12_14_25_L_I_L_I_L_0_H_L_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
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
  have h4elo := hb4.1
  have h5elo := hb5.1
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h554 | h554
  · rcases m.htr 0 1 4 (by decide) (by decide) with h555 | h555
    · rcases m.htr 0 1 5 (by decide) (by decide) with h556 | h556
      · rcases m.htr 0 2 3 (by decide) (by decide) with h557 | h557
        · rcases m.htr 0 2 4 (by decide) (by decide) with h558 | h558
          · rcases m.htr 1 2 3 (by decide) (by decide) with h559 | h559
            · rcases m.htr 1 2 4 (by decide) (by decide) with h560 | h560
              · rcases m.htr 1 2 5 (by decide) (by decide) with h561 | h561
                · rcases m.htr 1 3 4 (by decide) (by decide) with h562 | h562
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h563 | h563
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h564 | h564
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h565 | h565
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h566 | h566
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h567 | h567
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h568 | h568
                              · linarith only [h0, h554, h559, h565, h568, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                              · linarith only [h568, hc34, hlam, hphi, ht45, u5elo4]
                            · linarith only [h0, h554, h562, h564, h567, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · linarith only [h566, hc23, hlam, hphi, ht34, ht45, u5elo3]
                        · linarith only [h0, h554, h562, h565, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · linarith only [h564, hc14, hlam, hphi, ht45, u5elo4]
                    · linarith only [h563, hc13, hlam, hphi, ht34, ht45, u5elo3]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h576 | h576
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h577 | h577
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h578 | h578
                        · linarith only [h559, h562, h578, hlam]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h580 | h580
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h581 | h581
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h582 | h582
                              · rcases h1bigk with h583c | h583c | h583c | h583c | h583c | h583c | h583c | h583c | h583c | h583c | h583c | h583c | h583c | h583c | h583c | h583c | h583c | h583c | h583c | h583c | h583c | h583c | h583c | h583c | h583c
                                · have p583_0 := h583c.1
                                  have p583_1 := h583c.2.1
                                  have p583_2 := h583c.2.2.1
                                  have p583_3 := h583c.2.2.2
                                  linarith only [hlam, p583_0]
                                · have p583_0 := h583c.1
                                  have p583_1 := h583c.2.1
                                  have p583_2 := h583c.2.2.1
                                  have p583_3 := h583c.2.2.2
                                  linarith only [h0, hlam, p583_0]
                                · have p583_0 := h583c.1
                                  have p583_1 := h583c.2.1
                                  have p583_2 := h583c.2.2.1
                                  have p583_3 := h583c.2.2.2
                                  linarith only [h0, h559, h580, h582, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p583_1]
                                · have p583_0 := h583c.1
                                  have p583_1 := h583c.2.1
                                  have p583_2 := h583c.2.2.1
                                  have p583_3 := h583c.2.2.2
                                  linarith only [h0, h559, h562, h580, h582, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p583_1]
                                · have p583_0 := h583c.1
                                  have p583_1 := h583c.2.1
                                  have p583_2 := h583c.2.2.1
                                  have p583_3 := h583c.2.2.2
                                  rcases p583_3 (m.d 0 1) (by simp) with h588 | h588
                                  · rcases p583_3 (m.d 1 2) (by simp) with h589 | h589
                                    · rcases p583_3 (m.d 1 3) (by simp) with h590 | h590
                                      · linarith only [h554, h590, hlam]
                                      · linarith only [h576, h590, hlam]
                                    · linarith only [h561, h589, hlam]
                                  · linarith only [h588, hlam, p583_0]
                                · have p583_0 := h583c.1
                                  have p583_1 := h583c.2.1
                                  have p583_2 := h583c.2.2.1
                                  have p583_3 := h583c.2.2.2
                                  linarith only [h554, h559, h580, h582, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p583_1]
                                · have p583_0 := h583c.1
                                  have p583_1 := h583c.2.1
                                  have p583_2 := h583c.2.2.1
                                  have p583_3 := h583c.2.2.2
                                  linarith only [hlam, p583_0]
                                · have p583_0 := h583c.1
                                  have p583_1 := h583c.2.1
                                  have p583_2 := h583c.2.2.1
                                  have p583_3 := h583c.2.2.2
                                  rcases p583_3 (m.d 0 1) (by simp) with h597 | h597
                                  · linarith only [h0, h597, hlam]
                                  · linarith only [h554, h597, hlam]
                                · have p583_0 := h583c.1
                                  have p583_1 := h583c.2.1
                                  have p583_2 := h583c.2.2.1
                                  have p583_3 := h583c.2.2.2
                                  rcases p583_3 (m.d 0 1) (by simp) with h600 | h600
                                  · linarith only [h0, h600, hlam]
                                  · linarith only [h555, h600, hlam]
                                · have p583_0 := h583c.1
                                  have p583_1 := h583c.2.1
                                  have p583_2 := h583c.2.2.1
                                  have p583_3 := h583c.2.2.2
                                  rcases p583_3 (m.d 0 1) (by simp) with h603 | h603
                                  · linarith only [h0, h603, hlam]
                                  · linarith only [h556, h603, hlam]
                                · have p583_0 := h583c.1
                                  have p583_1 := h583c.2.1
                                  have p583_2 := h583c.2.2.1
                                  have p583_3 := h583c.2.2.2
                                  linarith only [h554, hlam, p583_0]
                                · have p583_0 := h583c.1
                                  have p583_1 := h583c.2.1
                                  have p583_2 := h583c.2.2.1
                                  have p583_3 := h583c.2.2.2
                                  linarith only [h559, hlam, p583_0]
                                · have p583_0 := h583c.1
                                  have p583_1 := h583c.2.1
                                  have p583_2 := h583c.2.2.1
                                  have p583_3 := h583c.2.2.2
                                  linarith only [hlam, p583_0]
                                · have p583_0 := h583c.1
                                  have p583_1 := h583c.2.1
                                  have p583_2 := h583c.2.2.1
                                  have p583_3 := h583c.2.2.2
                                  linarith only [h562, hlam, p583_0]
                                · have p583_0 := h583c.1
                                  have p583_1 := h583c.2.1
                                  have p583_2 := h583c.2.2.1
                                  have p583_3 := h583c.2.2.2
                                  linarith only [h0, h555, h562, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b, p583_1]
                                · have p583_0 := h583c.1
                                  have p583_1 := h583c.2.1
                                  have p583_2 := h583c.2.2.1
                                  have p583_3 := h583c.2.2.2
                                  linarith only [h555, hlam, p583_0]
                                · have p583_0 := h583c.1
                                  have p583_1 := h583c.2.1
                                  have p583_2 := h583c.2.2.1
                                  have p583_3 := h583c.2.2.2
                                  linarith only [h560, hlam, p583_0]
                                · have p583_0 := h583c.1
                                  have p583_1 := h583c.2.1
                                  have p583_2 := h583c.2.2.1
                                  have p583_3 := h583c.2.2.2
                                  linarith only [h0, h555, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p583_1]
                                · have p583_0 := h583c.1
                                  have p583_1 := h583c.2.1
                                  have p583_2 := h583c.2.2.1
                                  have p583_3 := h583c.2.2.2
                                  linarith only [hlam, p583_0]
                                · have p583_0 := h583c.1
                                  have p583_1 := h583c.2.1
                                  have p583_2 := h583c.2.2.1
                                  have p583_3 := h583c.2.2.2
                                  linarith only [h0, h555, h576, h582, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p583_1]
                                · have p583_0 := h583c.1
                                  have p583_1 := h583c.2.1
                                  have p583_2 := h583c.2.2.1
                                  have p583_3 := h583c.2.2.2
                                  linarith only [h556, hlam, p583_0]
                                · have p583_0 := h583c.1
                                  have p583_1 := h583c.2.1
                                  have p583_2 := h583c.2.2.1
                                  have p583_3 := h583c.2.2.2
                                  linarith only [h561, hlam, p583_0]
                                · have p583_0 := h583c.1
                                  have p583_1 := h583c.2.1
                                  have p583_2 := h583c.2.2.1
                                  have p583_3 := h583c.2.2.2
                                  linarith only [h576, hlam, p583_0]
                                · have p583_0 := h583c.1
                                  have p583_1 := h583c.2.1
                                  have p583_2 := h583c.2.2.1
                                  have p583_3 := h583c.2.2.2
                                  linarith only [h577, hlam, p583_0]
                                · have p583_0 := h583c.1
                                  have p583_1 := h583c.2.1
                                  have p583_2 := h583c.2.2.1
                                  have p583_3 := h583c.2.2.2
                                  linarith only [hlam, p583_0]
                              · linarith only [h559, h562, h580, h582, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo4]
                            · linarith only [h559, h562, h577, h580, h581, hc24, hc35, hlam, hphi, u4elo3, u5elo1]
                          · linarith only [h580, hc23, hlam, hphi, ht34, ht45, u5elo3]
                      · linarith only [h577, hc14, hlam, hphi, ht45, u5elo4]
                    · linarith only [h576, hc13, hlam, hphi, ht34, ht45, u5elo3]
                · linarith only [h0, h561, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
              · linarith only [h0, h554, h559, h560, hc23, hlam, hphi, ht34, u4elo2]
            · linarith only [h0, h557, h559, hlam]
          · linarith only [h0, h554, h558, hc13, hlam, hphi, ht34, u4elo2]
        · linarith only [h0, h554, h557, hlam]
      · linarith only [h554, h556, hc13, hlam, hphi, ht34, ht45, u5elo1]
    · linarith only [h554, h555, hc13, hlam, hphi, ht34, u4elo1]
  · rcases m.htr 0 1 4 (by decide) (by decide) with h633 | h633
    · rcases m.htr 0 1 5 (by decide) (by decide) with h634 | h634
      · rcases m.htr 0 2 3 (by decide) (by decide) with h635 | h635
        · rcases m.htr 0 2 4 (by decide) (by decide) with h636 | h636
          · rcases m.htr 1 2 3 (by decide) (by decide) with h637 | h637
            · rcases m.htr 1 2 4 (by decide) (by decide) with h638 | h638
              · rcases m.htr 1 2 5 (by decide) (by decide) with h639 | h639
                · rcases m.htr 1 3 4 (by decide) (by decide) with h640 | h640
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h641 | h641
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h642 | h642
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h643 | h643
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h644 | h644
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h645 | h645
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h646 | h646
                              · rcases h1bigk with h647c | h647c | h647c | h647c | h647c | h647c | h647c | h647c | h647c | h647c | h647c | h647c | h647c | h647c | h647c | h647c | h647c | h647c | h647c | h647c | h647c | h647c | h647c | h647c | h647c
                                · have p647_0 := h647c.1
                                  have p647_1 := h647c.2.1
                                  have p647_2 := h647c.2.2.1
                                  have p647_3 := h647c.2.2.2
                                  linarith only [hlam, p647_0]
                                · have p647_0 := h647c.1
                                  have p647_1 := h647c.2.1
                                  have p647_2 := h647c.2.2.1
                                  have p647_3 := h647c.2.2.2
                                  linarith only [h0, hlam, p647_0]
                                · have p647_0 := h647c.1
                                  have p647_1 := h647c.2.1
                                  have p647_2 := h647c.2.2.1
                                  have p647_3 := h647c.2.2.2
                                  linarith only [h554, hlam, p647_0]
                                · have p647_0 := h647c.1
                                  have p647_1 := h647c.2.1
                                  have p647_2 := h647c.2.2.1
                                  have p647_3 := h647c.2.2.2
                                  linarith only [h554, h637, h638, h643, h646, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p647_1]
                                · have p647_0 := h647c.1
                                  have p647_1 := h647c.2.1
                                  have p647_2 := h647c.2.2.1
                                  have p647_3 := h647c.2.2.2
                                  rcases p647_3 (m.d 0 1) (by simp) with h652 | h652
                                  · rcases p647_3 (m.d 1 2) (by simp) with h653 | h653
                                    · rcases p647_3 (m.d 1 3) (by simp) with h654 | h654
                                      · rcases p647_3 (m.d 1 4) (by simp) with h655 | h655
                                        · linarith only [h633, h655, hlam]
                                        · linarith only [h642, h655, hlam]
                                      · linarith only [h641, h654, hlam]
                                    · linarith only [h639, h653, hlam]
                                  · linarith only [h652, hlam, p647_0]
                                · have p647_0 := h647c.1
                                  have p647_1 := h647c.2.1
                                  have p647_2 := h647c.2.2.1
                                  have p647_3 := h647c.2.2.2
                                  linarith only [h633, h638, h643, h646, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p647_1]
                                · have p647_0 := h647c.1
                                  have p647_1 := h647c.2.1
                                  have p647_2 := h647c.2.2.1
                                  have p647_3 := h647c.2.2.2
                                  linarith only [hlam, p647_0]
                                · have p647_0 := h647c.1
                                  have p647_1 := h647c.2.1
                                  have p647_2 := h647c.2.2.1
                                  have p647_3 := h647c.2.2.2
                                  linarith only [h554, hc01, hc12, hlam, hphi, p647_1]
                                · have p647_0 := h647c.1
                                  have p647_1 := h647c.2.1
                                  have p647_2 := h647c.2.2.1
                                  have p647_3 := h647c.2.2.2
                                  rcases p647_3 (m.d 0 1) (by simp) with h664 | h664
                                  · linarith only [h0, h664, hlam]
                                  · linarith only [h633, h664, hlam]
                                · have p647_0 := h647c.1
                                  have p647_1 := h647c.2.1
                                  have p647_2 := h647c.2.2.1
                                  have p647_3 := h647c.2.2.2
                                  rcases p647_3 (m.d 0 1) (by simp) with h667 | h667
                                  · linarith only [h0, h667, hlam]
                                  · linarith only [h634, h667, hlam]
                                · have p647_0 := h647c.1
                                  have p647_1 := h647c.2.1
                                  have p647_2 := h647c.2.2.1
                                  have p647_3 := h647c.2.2.2
                                  linarith only [h633, h637, h638, h643, h646, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p647_1]
                                · have p647_0 := h647c.1
                                  have p647_1 := h647c.2.1
                                  have p647_2 := h647c.2.2.1
                                  have p647_3 := h647c.2.2.2
                                  linarith only [h637, hlam, p647_0]
                                · have p647_0 := h647c.1
                                  have p647_1 := h647c.2.1
                                  have p647_2 := h647c.2.2.1
                                  have p647_3 := h647c.2.2.2
                                  linarith only [hlam, p647_0]
                                · have p647_0 := h647c.1
                                  have p647_1 := h647c.2.1
                                  have p647_2 := h647c.2.2.1
                                  have p647_3 := h647c.2.2.2
                                  rcases p647_3 (m.d 0 1) (by simp) with h673 | h673
                                  · linarith only [h554, h673, hlam]
                                  · linarith only [h633, h673, hlam]
                                · have p647_0 := h647c.1
                                  have p647_1 := h647c.2.1
                                  have p647_2 := h647c.2.2.1
                                  have p647_3 := h647c.2.2.2
                                  rcases p647_3 (m.d 0 1) (by simp) with h676 | h676
                                  · linarith only [h554, h676, hlam]
                                  · linarith only [h634, h676, hlam]
                                · have p647_0 := h647c.1
                                  have p647_1 := h647c.2.1
                                  have p647_2 := h647c.2.2.1
                                  have p647_3 := h647c.2.2.2
                                  linarith only [h633, hlam, p647_0]
                                · have p647_0 := h647c.1
                                  have p647_1 := h647c.2.1
                                  have p647_2 := h647c.2.2.1
                                  have p647_3 := h647c.2.2.2
                                  linarith only [h638, hlam, p647_0]
                                · have p647_0 := h647c.1
                                  have p647_1 := h647c.2.1
                                  have p647_2 := h647c.2.2.1
                                  have p647_3 := h647c.2.2.2
                                  linarith only [h640, hlam, p647_1]
                                · have p647_0 := h647c.1
                                  have p647_1 := h647c.2.1
                                  have p647_2 := h647c.2.2.1
                                  have p647_3 := h647c.2.2.2
                                  linarith only [hlam, p647_0]
                                · have p647_0 := h647c.1
                                  have p647_1 := h647c.2.1
                                  have p647_2 := h647c.2.2.1
                                  have p647_3 := h647c.2.2.2
                                  linarith only [h0, h633, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b, p647_1]
                                · have p647_0 := h647c.1
                                  have p647_1 := h647c.2.1
                                  have p647_2 := h647c.2.2.1
                                  have p647_3 := h647c.2.2.2
                                  linarith only [h634, hlam, p647_0]
                                · have p647_0 := h647c.1
                                  have p647_1 := h647c.2.1
                                  have p647_2 := h647c.2.2.1
                                  have p647_3 := h647c.2.2.2
                                  linarith only [h639, hlam, p647_0]
                                · have p647_0 := h647c.1
                                  have p647_1 := h647c.2.1
                                  have p647_2 := h647c.2.2.1
                                  have p647_3 := h647c.2.2.2
                                  linarith only [h641, hlam, p647_0]
                                · have p647_0 := h647c.1
                                  have p647_1 := h647c.2.1
                                  have p647_2 := h647c.2.2.1
                                  have p647_3 := h647c.2.2.2
                                  linarith only [h642, hlam, p647_0]
                                · have p647_0 := h647c.1
                                  have p647_1 := h647c.2.1
                                  have p647_2 := h647c.2.2.1
                                  have p647_3 := h647c.2.2.2
                                  linarith only [hlam, p647_0]
                              · linarith only [h645, h646, hc34, hlam, hphi, u4elo2]
                            · linarith only [h642, h645, hc24, hlam, hphi, ht45, u5elo1]
                          · linarith only [h644, hc23, hlam, hphi, ht34, ht45, u5elo3]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h692 | h692
                          · linarith only [h554, h633, h637, h640, h643, h692, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                          · linarith only [h692, hc23, hlam, hphi, ht34, ht45, u5elo3]
                      · linarith only [h642, hc14, hlam, hphi, ht45, u5elo4]
                    · linarith only [h554, h641, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                  · linarith only [h554, h633, h638, h640, hc24, hlam, hphi, u4elo3]
                · linarith only [h639, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
              · linarith only [h554, h637, h638, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
            · linarith only [h0, h633, h635, h637, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b]
          · linarith only [h0, h633, h636, hc14, hlam, hphi, u4elo2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h702 | h702
          · rcases m.htr 1 2 3 (by decide) (by decide) with h703 | h703
            · rcases m.htr 1 2 4 (by decide) (by decide) with h704 | h704
              · rcases m.htr 1 2 5 (by decide) (by decide) with h705 | h705
                · rcases m.htr 1 3 4 (by decide) (by decide) with h706 | h706
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h707 | h707
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h708 | h708
                      · linarith only [h0, h633, h635, h703, h708, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                      · linarith only [h708, hc14, hlam, hphi, ht45, u5elo4]
                    · linarith only [h0, h633, h635, h703, h704, h707, hc24, hlam, hphi, ht45, u5elo3]
                  · linarith only [h0, h633, h635, h703, h704, h706, hc24, hlam, hphi, u4elo3]
                · linarith only [h0, h633, h635, h703, h704, h705, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
              · linarith only [h0, h633, h635, h703, h704, hc14, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h715 | h715
              · rcases m.htr 1 2 5 (by decide) (by decide) with h716 | h716
                · rcases m.htr 1 3 4 (by decide) (by decide) with h717 | h717
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h718 | h718
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h719 | h719
                      · linarith only [h0, h633, h703, h719, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                      · linarith only [h719, hc14, hlam, hphi, ht45, u5elo4]
                    · linarith only [h0, h633, h703, h715, h718, hc24, hlam, hphi, ht45, u5elo3]
                  · linarith only [h0, h633, h703, h715, h717, hc24, hlam, hphi, u4elo3]
                · linarith only [h0, h633, h715, h716, hc24, hlam, hphi, ht45, u5elo2]
              · linarith only [h0, h633, h715, hc14, hlam, hphi, u4elo2]
          · linarith only [h0, h633, h702, hc14, hlam, hphi, u4elo2]
      · linarith only [h633, h634, hc14, hlam, hphi, ht45, u5elo1]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h728 | h728
      · rcases m.htr 0 2 3 (by decide) (by decide) with h729 | h729
        · rcases m.htr 0 2 4 (by decide) (by decide) with h730 | h730
          · rcases m.htr 1 2 3 (by decide) (by decide) with h731 | h731
            · rcases m.htr 1 2 4 (by decide) (by decide) with h732 | h732
              · rcases m.htr 1 2 5 (by decide) (by decide) with h733 | h733
                · rcases m.htr 1 3 4 (by decide) (by decide) with h734 | h734
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h735 | h735
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h736 | h736
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h737 | h737
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h738 | h738
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h739 | h739
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h740 | h740
                              · rcases h1bigk with h741c | h741c | h741c | h741c | h741c | h741c | h741c | h741c | h741c | h741c | h741c | h741c | h741c | h741c | h741c | h741c | h741c | h741c | h741c | h741c | h741c | h741c | h741c | h741c | h741c
                                · have p741_0 := h741c.1
                                  have p741_1 := h741c.2.1
                                  have p741_2 := h741c.2.2.1
                                  have p741_3 := h741c.2.2.2
                                  linarith only [hlam, p741_0]
                                · have p741_0 := h741c.1
                                  have p741_1 := h741c.2.1
                                  have p741_2 := h741c.2.2.1
                                  have p741_3 := h741c.2.2.2
                                  linarith only [h0, hlam, p741_0]
                                · have p741_0 := h741c.1
                                  have p741_1 := h741c.2.1
                                  have p741_2 := h741c.2.2.1
                                  have p741_3 := h741c.2.2.2
                                  linarith only [h554, hlam, p741_0]
                                · have p741_0 := h741c.1
                                  have p741_1 := h741c.2.1
                                  have p741_2 := h741c.2.2.1
                                  have p741_3 := h741c.2.2.2
                                  linarith only [h633, hlam, p741_0]
                                · have p741_0 := h741c.1
                                  have p741_1 := h741c.2.1
                                  have p741_2 := h741c.2.2.1
                                  have p741_3 := h741c.2.2.2
                                  linarith only [h633, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p741_1, u4elo1]
                                · have p741_0 := h741c.1
                                  have p741_1 := h741c.2.1
                                  have p741_2 := h741c.2.2.1
                                  have p741_3 := h741c.2.2.2
                                  rcases p741_3 (m.d 0 1) (by simp) with h747 | h747
                                  · linarith only [h747, hlam, p741_0]
                                  · rcases p741_3 (m.d 1 2) (by simp) with h749 | h749
                                    · rcases p741_3 (m.d 1 3) (by simp) with h750 | h750
                                      · linarith only [h731, h750, hlam]
                                      · linarith only [h554, h750, hlam]
                                    · linarith only [h749, hlam, p741_0]
                                · have p741_0 := h741c.1
                                  have p741_1 := h741c.2.1
                                  have p741_2 := h741c.2.2.1
                                  have p741_3 := h741c.2.2.2
                                  linarith only [hlam, p741_0]
                                · have p741_0 := h741c.1
                                  have p741_1 := h741c.2.1
                                  have p741_2 := h741c.2.2.1
                                  have p741_3 := h741c.2.2.2
                                  linarith only [h554, h728, h733, h738, h740, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p741_1]
                                · have p741_0 := h741c.1
                                  have p741_1 := h741c.2.1
                                  have p741_2 := h741c.2.2.1
                                  have p741_3 := h741c.2.2.2
                                  linarith only [h633, h728, h733, h738, h740, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p741_1]
                                · have p741_0 := h741c.1
                                  have p741_1 := h741c.2.1
                                  have p741_2 := h741c.2.2.1
                                  have p741_3 := h741c.2.2.2
                                  rcases p741_3 (m.d 0 1) (by simp) with h757 | h757
                                  · linarith only [h0, h757, hlam]
                                  · linarith only [h728, h757, hlam]
                                · have p741_0 := h741c.1
                                  have p741_1 := h741c.2.1
                                  have p741_2 := h741c.2.2.1
                                  have p741_3 := h741c.2.2.2
                                  rcases p741_3 (m.d 0 1) (by simp) with h760 | h760
                                  · linarith only [h760, hlam, p741_0]
                                  · rcases p741_3 (m.d 1 2) (by simp) with h762 | h762
                                    · rcases p741_3 (m.d 1 3) (by simp) with h763 | h763
                                      · rcases p741_3 (m.d 1 4) (by simp) with h764 | h764
                                        · linarith only [h734, h764, hlam]
                                        · linarith only [h633, h764, hlam]
                                      · linarith only [h763, hlam, p741_0]
                                    · linarith only [h0, h762, hlam]
                                · have p741_0 := h741c.1
                                  have p741_1 := h741c.2.1
                                  have p741_2 := h741c.2.2.1
                                  have p741_3 := h741c.2.2.2
                                  linarith only [h731, hlam, p741_0]
                                · have p741_0 := h741c.1
                                  have p741_1 := h741c.2.1
                                  have p741_2 := h741c.2.2.1
                                  have p741_3 := h741c.2.2.2
                                  linarith only [hlam, p741_0]
                                · have p741_0 := h741c.1
                                  have p741_1 := h741c.2.1
                                  have p741_2 := h741c.2.2.1
                                  have p741_3 := h741c.2.2.2
                                  linarith only [h633, h728, h731, h733, h738, h740, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p741_1]
                                · have p741_0 := h741c.1
                                  have p741_1 := h741c.2.1
                                  have p741_2 := h741c.2.2.1
                                  have p741_3 := h741c.2.2.2
                                  rcases p741_3 (m.d 0 1) (by simp) with h772 | h772
                                  · linarith only [h554, h772, hlam]
                                  · linarith only [h728, h772, hlam]
                                · have p741_0 := h741c.1
                                  have p741_1 := h741c.2.1
                                  have p741_2 := h741c.2.2.1
                                  have p741_3 := h741c.2.2.2
                                  linarith only [h728, h733, h738, h740, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p741_1, u4elo1]
                                · have p741_0 := h741c.1
                                  have p741_1 := h741c.2.1
                                  have p741_2 := h741c.2.2.1
                                  have p741_3 := h741c.2.2.2
                                  linarith only [h732, hlam, p741_0]
                                · have p741_0 := h741c.1
                                  have p741_1 := h741c.2.1
                                  have p741_2 := h741c.2.2.1
                                  have p741_3 := h741c.2.2.2
                                  linarith only [h734, hlam, p741_1]
                                · have p741_0 := h741c.1
                                  have p741_1 := h741c.2.1
                                  have p741_2 := h741c.2.2.1
                                  have p741_3 := h741c.2.2.2
                                  linarith only [hlam, p741_0]
                                · have p741_0 := h741c.1
                                  have p741_1 := h741c.2.1
                                  have p741_2 := h741c.2.2.1
                                  have p741_3 := h741c.2.2.2
                                  rcases p741_3 (m.d 0 1) (by simp) with h779 | h779
                                  · linarith only [h633, h779, hlam]
                                  · linarith only [h728, h779, hlam]
                                · have p741_0 := h741c.1
                                  have p741_1 := h741c.2.1
                                  have p741_2 := h741c.2.2.1
                                  have p741_3 := h741c.2.2.2
                                  linarith only [h728, hlam, p741_0]
                                · have p741_0 := h741c.1
                                  have p741_1 := h741c.2.1
                                  have p741_2 := h741c.2.2.1
                                  have p741_3 := h741c.2.2.2
                                  linarith only [h733, hlam, p741_0]
                                · have p741_0 := h741c.1
                                  have p741_1 := h741c.2.1
                                  have p741_2 := h741c.2.2.1
                                  have p741_3 := h741c.2.2.2
                                  linarith only [h735, hlam, p741_0]
                                · have p741_0 := h741c.1
                                  have p741_1 := h741c.2.1
                                  have p741_2 := h741c.2.2.1
                                  have p741_3 := h741c.2.2.2
                                  linarith only [h736, hlam, p741_0]
                                · have p741_0 := h741c.1
                                  have p741_1 := h741c.2.1
                                  have p741_2 := h741c.2.2.1
                                  have p741_3 := h741c.2.2.2
                                  linarith only [hlam, p741_0]
                              · linarith only [h740, hc34, hlam, hphi, ht45, u5elo4]
                            · linarith only [h633, h728, h736, h739, hc24, hlam, hphi, u4elo1]
                          · linarith only [h633, h728, h733, h738, hc23, hc25, hlam, hphi, ht34, u4elo1, u5elo3]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h790 | h790
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h791 | h791
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h792 | h792
                              · rcases h1bigk with h793c | h793c | h793c | h793c | h793c | h793c | h793c | h793c | h793c | h793c | h793c | h793c | h793c | h793c | h793c | h793c | h793c | h793c | h793c | h793c | h793c | h793c | h793c | h793c | h793c
                                · have p793_0 := h793c.1
                                  have p793_1 := h793c.2.1
                                  have p793_2 := h793c.2.2.1
                                  have p793_3 := h793c.2.2.2
                                  linarith only [hlam, p793_0]
                                · have p793_0 := h793c.1
                                  have p793_1 := h793c.2.1
                                  have p793_2 := h793c.2.2.1
                                  have p793_3 := h793c.2.2.2
                                  linarith only [h0, hlam, p793_0]
                                · have p793_0 := h793c.1
                                  have p793_1 := h793c.2.1
                                  have p793_2 := h793c.2.2.1
                                  have p793_3 := h793c.2.2.2
                                  linarith only [h554, hlam, p793_0]
                                · have p793_0 := h793c.1
                                  have p793_1 := h793c.2.1
                                  have p793_2 := h793c.2.2.1
                                  have p793_3 := h793c.2.2.2
                                  linarith only [h633, hlam, p793_0]
                                · have p793_0 := h793c.1
                                  have p793_1 := h793c.2.1
                                  have p793_2 := h793c.2.2.1
                                  have p793_3 := h793c.2.2.2
                                  linarith only [h633, h733, h790, h792, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p793_1, u4elo1]
                                · have p793_0 := h793c.1
                                  have p793_1 := h793c.2.1
                                  have p793_2 := h793c.2.2.1
                                  have p793_3 := h793c.2.2.2
                                  rcases p793_3 (m.d 0 1) (by simp) with h799 | h799
                                  · linarith only [h799, hlam, p793_0]
                                  · rcases p793_3 (m.d 1 2) (by simp) with h801 | h801
                                    · rcases p793_3 (m.d 1 3) (by simp) with h802 | h802
                                      · linarith only [h731, h802, hlam]
                                      · linarith only [h554, h802, hlam]
                                    · linarith only [h801, hlam, p793_0]
                                · have p793_0 := h793c.1
                                  have p793_1 := h793c.2.1
                                  have p793_2 := h793c.2.2.1
                                  have p793_3 := h793c.2.2.2
                                  linarith only [hlam, p793_0]
                                · have p793_0 := h793c.1
                                  have p793_1 := h793c.2.1
                                  have p793_2 := h793c.2.2.1
                                  have p793_3 := h793c.2.2.2
                                  linarith only [h554, hc01, hc12, hlam, hphi, p793_1]
                                · have p793_0 := h793c.1
                                  have p793_1 := h793c.2.1
                                  have p793_2 := h793c.2.2.1
                                  have p793_3 := h793c.2.2.2
                                  linarith only [h633, h728, h733, h790, h792, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p793_1]
                                · have p793_0 := h793c.1
                                  have p793_1 := h793c.2.1
                                  have p793_2 := h793c.2.2.1
                                  have p793_3 := h793c.2.2.2
                                  rcases p793_3 (m.d 0 1) (by simp) with h809 | h809
                                  · linarith only [h0, h809, hlam]
                                  · linarith only [h728, h809, hlam]
                                · have p793_0 := h793c.1
                                  have p793_1 := h793c.2.1
                                  have p793_2 := h793c.2.2.1
                                  have p793_3 := h793c.2.2.2
                                  rcases p793_3 (m.d 0 1) (by simp) with h812 | h812
                                  · linarith only [h812, hlam, p793_0]
                                  · rcases p793_3 (m.d 1 2) (by simp) with h814 | h814
                                    · rcases p793_3 (m.d 1 3) (by simp) with h815 | h815
                                      · rcases p793_3 (m.d 1 4) (by simp) with h816 | h816
                                        · linarith only [h734, h816, hlam]
                                        · linarith only [h633, h816, hlam]
                                      · linarith only [h815, hlam, p793_0]
                                    · linarith only [h0, h814, hlam]
                                · have p793_0 := h793c.1
                                  have p793_1 := h793c.2.1
                                  have p793_2 := h793c.2.2.1
                                  have p793_3 := h793c.2.2.2
                                  linarith only [h731, hlam, p793_0]
                                · have p793_0 := h793c.1
                                  have p793_1 := h793c.2.1
                                  have p793_2 := h793c.2.2.1
                                  have p793_3 := h793c.2.2.2
                                  linarith only [hlam, p793_0]
                                · have p793_0 := h793c.1
                                  have p793_1 := h793c.2.1
                                  have p793_2 := h793c.2.2.1
                                  have p793_3 := h793c.2.2.2
                                  linarith only [h633, h728, h731, h733, h790, h792, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p793_1]
                                · have p793_0 := h793c.1
                                  have p793_1 := h793c.2.1
                                  have p793_2 := h793c.2.2.1
                                  have p793_3 := h793c.2.2.2
                                  rcases p793_3 (m.d 0 1) (by simp) with h824 | h824
                                  · linarith only [h554, h824, hlam]
                                  · linarith only [h728, h824, hlam]
                                · have p793_0 := h793c.1
                                  have p793_1 := h793c.2.1
                                  have p793_2 := h793c.2.2.1
                                  have p793_3 := h793c.2.2.2
                                  linarith only [h728, h733, h790, h792, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p793_1, u4elo1]
                                · have p793_0 := h793c.1
                                  have p793_1 := h793c.2.1
                                  have p793_2 := h793c.2.2.1
                                  have p793_3 := h793c.2.2.2
                                  linarith only [h732, hlam, p793_0]
                                · have p793_0 := h793c.1
                                  have p793_1 := h793c.2.1
                                  have p793_2 := h793c.2.2.1
                                  have p793_3 := h793c.2.2.2
                                  linarith only [h734, hlam, p793_1]
                                · have p793_0 := h793c.1
                                  have p793_1 := h793c.2.1
                                  have p793_2 := h793c.2.2.1
                                  have p793_3 := h793c.2.2.2
                                  linarith only [hlam, p793_0]
                                · have p793_0 := h793c.1
                                  have p793_1 := h793c.2.1
                                  have p793_2 := h793c.2.2.1
                                  have p793_3 := h793c.2.2.2
                                  rcases p793_3 (m.d 0 1) (by simp) with h831 | h831
                                  · linarith only [h633, h831, hlam]
                                  · linarith only [h728, h831, hlam]
                                · have p793_0 := h793c.1
                                  have p793_1 := h793c.2.1
                                  have p793_2 := h793c.2.2.1
                                  have p793_3 := h793c.2.2.2
                                  linarith only [h728, hlam, p793_0]
                                · have p793_0 := h793c.1
                                  have p793_1 := h793c.2.1
                                  have p793_2 := h793c.2.2.1
                                  have p793_3 := h793c.2.2.2
                                  linarith only [h733, hlam, p793_0]
                                · have p793_0 := h793c.1
                                  have p793_1 := h793c.2.1
                                  have p793_2 := h793c.2.2.1
                                  have p793_3 := h793c.2.2.2
                                  linarith only [h735, hlam, p793_0]
                                · have p793_0 := h793c.1
                                  have p793_1 := h793c.2.1
                                  have p793_2 := h793c.2.2.1
                                  have p793_3 := h793c.2.2.2
                                  linarith only [h736, hlam, p793_0]
                                · have p793_0 := h793c.1
                                  have p793_1 := h793c.2.1
                                  have p793_2 := h793c.2.2.1
                                  have p793_3 := h793c.2.2.2
                                  linarith only [hlam, p793_0]
                              · linarith only [h737, h790, h792, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo4]
                            · linarith only [h736, h737, h790, h791, hc35, hlam, hphi, u5elo1]
                          · linarith only [h790, hc23, hlam, hphi, ht34, ht45, u5elo3]
                      · linarith only [h633, h728, h733, h736, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo4]
                    · linarith only [h735, hc13, hlam, hphi, ht34, ht45, u5elo3]
                  · linarith only [h554, h728, h733, h734, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo3]
                · linarith only [h733, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
              · linarith only [h0, h730, h732, hlam]
            · linarith only [h0, h729, h731, hlam]
          · linarith only [h729, h730, hc23, hlam, hphi, ht34, u4elo2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h849 | h849
          · rcases m.htr 1 2 3 (by decide) (by decide) with h850 | h850
            · rcases m.htr 1 2 4 (by decide) (by decide) with h851 | h851
              · rcases m.htr 1 2 5 (by decide) (by decide) with h852 | h852
                · rcases m.htr 1 3 4 (by decide) (by decide) with h853 | h853
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h854 | h854
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h855 | h855
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h856 | h856
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h857 | h857
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h858 | h858
                            · linarith only [h729, h849, h850, h858, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                            · linarith only [h858, hc24, hlam, hphi, ht45, u5elo4]
                          · linarith only [h633, h728, h729, h852, h857, hc02, hc25, hlam, hphi, ht23, ht34, u4elo1, u5elo3]
                        · linarith only [h729, h849, h856, hc24, hlam, hphi, u4elo3]
                      · linarith only [h855, hc14, hlam, hphi, ht45, u5elo4]
                    · linarith only [h633, h728, h729, h849, h850, h852, h854, hc25, hlam, hphi, u5elo3]
                  · linarith only [h633, h728, h729, h849, h850, h852, h853, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo3]
                · linarith only [h852, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
              · linarith only [h729, h849, h850, h851, hlam]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h868 | h868
              · rcases m.htr 1 2 5 (by decide) (by decide) with h869 | h869
                · rcases m.htr 1 3 4 (by decide) (by decide) with h870 | h870
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h871 | h871
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h872 | h872
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h873 | h873
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h874 | h874
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h875 | h875
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h876 | h876
                              · rcases h1bigk with h877c | h877c | h877c | h877c | h877c | h877c | h877c | h877c | h877c | h877c | h877c | h877c | h877c | h877c | h877c | h877c | h877c | h877c | h877c | h877c | h877c | h877c | h877c | h877c | h877c
                                · have p877_0 := h877c.1
                                  have p877_1 := h877c.2.1
                                  have p877_2 := h877c.2.2.1
                                  have p877_3 := h877c.2.2.2
                                  linarith only [hlam, p877_0]
                                · have p877_0 := h877c.1
                                  have p877_1 := h877c.2.1
                                  have p877_2 := h877c.2.2.1
                                  have p877_3 := h877c.2.2.2
                                  linarith only [h0, hlam, p877_0]
                                · have p877_0 := h877c.1
                                  have p877_1 := h877c.2.1
                                  have p877_2 := h877c.2.2.1
                                  have p877_3 := h877c.2.2.2
                                  linarith only [h554, hlam, p877_0]
                                · have p877_0 := h877c.1
                                  have p877_1 := h877c.2.1
                                  have p877_2 := h877c.2.2.1
                                  have p877_3 := h877c.2.2.2
                                  linarith only [h633, hlam, p877_0]
                                · have p877_0 := h877c.1
                                  have p877_1 := h877c.2.1
                                  have p877_2 := h877c.2.2.1
                                  have p877_3 := h877c.2.2.2
                                  linarith only [h633, h850, h868, h869, h874, h876, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p877_1]
                                · have p877_0 := h877c.1
                                  have p877_1 := h877c.2.1
                                  have p877_2 := h877c.2.2.1
                                  have p877_3 := h877c.2.2.2
                                  linarith only [h850, hc01, hc23, hlam, hphi, ht12, p877_1]
                                · have p877_0 := h877c.1
                                  have p877_1 := h877c.2.1
                                  have p877_2 := h877c.2.2.1
                                  have p877_3 := h877c.2.2.2
                                  linarith only [hlam, p877_0]
                                · have p877_0 := h877c.1
                                  have p877_1 := h877c.2.1
                                  have p877_2 := h877c.2.2.1
                                  have p877_3 := h877c.2.2.2
                                  linarith only [h850, hlam, p877_1]
                                · have p877_0 := h877c.1
                                  have p877_1 := h877c.2.1
                                  have p877_2 := h877c.2.2.1
                                  have p877_3 := h877c.2.2.2
                                  linarith only [h633, h728, h850, h869, h874, h876, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p877_1]
                                · have p877_0 := h877c.1
                                  have p877_1 := h877c.2.1
                                  have p877_2 := h877c.2.2.1
                                  have p877_3 := h877c.2.2.2
                                  rcases p877_3 (m.d 0 1) (by simp) with h887 | h887
                                  · linarith only [h0, h887, hlam]
                                  · linarith only [h728, h887, hlam]
                                · have p877_0 := h877c.1
                                  have p877_1 := h877c.2.1
                                  have p877_2 := h877c.2.2.1
                                  have p877_3 := h877c.2.2.2
                                  rcases p877_3 (m.d 0 1) (by simp) with h890 | h890
                                  · linarith only [h890, hlam, p877_0]
                                  · rcases p877_3 (m.d 1 2) (by simp) with h892 | h892
                                    · linarith only [h850, h892, hlam]
                                    · linarith only [h0, h892, hlam]
                                · have p877_0 := h877c.1
                                  have p877_1 := h877c.2.1
                                  have p877_2 := h877c.2.2.1
                                  have p877_3 := h877c.2.2.2
                                  linarith only [h0, h728, h869, h874, h876, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p877_1]
                                · have p877_0 := h877c.1
                                  have p877_1 := h877c.2.1
                                  have p877_2 := h877c.2.2.1
                                  have p877_3 := h877c.2.2.2
                                  linarith only [hlam, p877_0]
                                · have p877_0 := h877c.1
                                  have p877_1 := h877c.2.1
                                  have p877_2 := h877c.2.2.1
                                  have p877_3 := h877c.2.2.2
                                  linarith only [h633, h728, h869, h874, h876, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p877_1]
                                · have p877_0 := h877c.1
                                  have p877_1 := h877c.2.1
                                  have p877_2 := h877c.2.2.1
                                  have p877_3 := h877c.2.2.2
                                  rcases p877_3 (m.d 0 1) (by simp) with h898 | h898
                                  · linarith only [h554, h898, hlam]
                                  · linarith only [h728, h898, hlam]
                                · have p877_0 := h877c.1
                                  have p877_1 := h877c.2.1
                                  have p877_2 := h877c.2.2.1
                                  have p877_3 := h877c.2.2.2
                                  linarith only [h728, h869, h874, h876, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p877_1, u4elo1]
                                · have p877_0 := h877c.1
                                  have p877_1 := h877c.2.1
                                  have p877_2 := h877c.2.2.1
                                  have p877_3 := h877c.2.2.2
                                  linarith only [h868, hlam, p877_0]
                                · have p877_0 := h877c.1
                                  have p877_1 := h877c.2.1
                                  have p877_2 := h877c.2.2.1
                                  have p877_3 := h877c.2.2.2
                                  linarith only [h870, hlam, p877_1]
                                · have p877_0 := h877c.1
                                  have p877_1 := h877c.2.1
                                  have p877_2 := h877c.2.2.1
                                  have p877_3 := h877c.2.2.2
                                  linarith only [hlam, p877_0]
                                · have p877_0 := h877c.1
                                  have p877_1 := h877c.2.1
                                  have p877_2 := h877c.2.2.1
                                  have p877_3 := h877c.2.2.2
                                  rcases p877_3 (m.d 0 1) (by simp) with h905 | h905
                                  · linarith only [h633, h905, hlam]
                                  · linarith only [h728, h905, hlam]
                                · have p877_0 := h877c.1
                                  have p877_1 := h877c.2.1
                                  have p877_2 := h877c.2.2.1
                                  have p877_3 := h877c.2.2.2
                                  linarith only [h728, hlam, p877_0]
                                · have p877_0 := h877c.1
                                  have p877_1 := h877c.2.1
                                  have p877_2 := h877c.2.2.1
                                  have p877_3 := h877c.2.2.2
                                  linarith only [h869, hlam, p877_0]
                                · have p877_0 := h877c.1
                                  have p877_1 := h877c.2.1
                                  have p877_2 := h877c.2.2.1
                                  have p877_3 := h877c.2.2.2
                                  linarith only [h871, hlam, p877_0]
                                · have p877_0 := h877c.1
                                  have p877_1 := h877c.2.1
                                  have p877_2 := h877c.2.2.1
                                  have p877_3 := h877c.2.2.2
                                  linarith only [h872, hlam, p877_0]
                                · have p877_0 := h877c.1
                                  have p877_1 := h877c.2.1
                                  have p877_2 := h877c.2.2.1
                                  have p877_3 := h877c.2.2.2
                                  linarith only [hlam, p877_0]
                              · linarith only [h876, hc34, hlam, hphi, ht45, u5elo4]
                            · linarith only [h633, h728, h872, h875, hc24, hlam, hphi, u4elo1]
                          · linarith only [h633, h728, h850, h869, h874, hc13, hc25, hlam, hphi, ht34, u4elo1, u5elo3]
                        · linarith only [h633, h728, h850, h868, h869, h873, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                      · linarith only [h633, h728, h869, h872, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo4]
                    · linarith only [h554, h729, h871, hc02, hlam, hphi, ht23, ht34, ht45, u5elo3]
                  · linarith only [h0, h728, h850, h869, h870, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo3]
                · linarith only [h0, h869, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
              · linarith only [h0, h728, h849, h868, hc02, hc15, hlam, hphi, ht0b, ht5b]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h922 | h922
            · rcases m.htr 1 2 4 (by decide) (by decide) with h923 | h923
              · rcases m.htr 1 2 5 (by decide) (by decide) with h924 | h924
                · rcases m.htr 1 3 4 (by decide) (by decide) with h925 | h925
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h926 | h926
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h927 | h927
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h928 | h928
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h929 | h929
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h930 | h930
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h931 | h931
                              · rcases h1bigk with h932c | h932c | h932c | h932c | h932c | h932c | h932c | h932c | h932c | h932c | h932c | h932c | h932c | h932c | h932c | h932c | h932c | h932c | h932c | h932c | h932c | h932c | h932c | h932c | h932c
                                · have p932_0 := h932c.1
                                  have p932_1 := h932c.2.1
                                  have p932_2 := h932c.2.2.1
                                  have p932_3 := h932c.2.2.2
                                  linarith only [hlam, p932_0]
                                · have p932_0 := h932c.1
                                  have p932_1 := h932c.2.1
                                  have p932_2 := h932c.2.2.1
                                  have p932_3 := h932c.2.2.2
                                  linarith only [h0, hlam, p932_0]
                                · have p932_0 := h932c.1
                                  have p932_1 := h932c.2.1
                                  have p932_2 := h932c.2.2.1
                                  have p932_3 := h932c.2.2.2
                                  linarith only [h554, hlam, p932_0]
                                · have p932_0 := h932c.1
                                  have p932_1 := h932c.2.1
                                  have p932_2 := h932c.2.2.1
                                  have p932_3 := h932c.2.2.2
                                  linarith only [h633, hlam, p932_0]
                                · have p932_0 := h932c.1
                                  have p932_1 := h932c.2.1
                                  have p932_2 := h932c.2.2.1
                                  have p932_3 := h932c.2.2.2
                                  linarith only [h0, h849, h923, h924, h929, h931, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p932_1, u4elo1]
                                · have p932_0 := h932c.1
                                  have p932_1 := h932c.2.1
                                  have p932_2 := h932c.2.2.1
                                  have p932_3 := h932c.2.2.2
                                  rcases p932_3 (m.d 0 1) (by simp) with h938 | h938
                                  · linarith only [h938, hlam, p932_0]
                                  · rcases p932_3 (m.d 1 2) (by simp) with h940 | h940
                                    · rcases p932_3 (m.d 1 3) (by simp) with h941 | h941
                                      · linarith only [h922, h941, hlam]
                                      · linarith only [h554, h941, hlam]
                                    · linarith only [h940, hlam, p932_0]
                                · have p932_0 := h932c.1
                                  have p932_1 := h932c.2.1
                                  have p932_2 := h932c.2.2.1
                                  have p932_3 := h932c.2.2.2
                                  linarith only [hlam, p932_0]
                                · have p932_0 := h932c.1
                                  have p932_1 := h932c.2.1
                                  have p932_2 := h932c.2.2.1
                                  have p932_3 := h932c.2.2.2
                                  linarith only [h554, hc01, hc12, hlam, hphi, p932_1]
                                · have p932_0 := h932c.1
                                  have p932_1 := h932c.2.1
                                  have p932_2 := h932c.2.2.1
                                  have p932_3 := h932c.2.2.2
                                  linarith only [h0, h728, h849, h923, h924, h929, h931, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p932_1]
                                · have p932_0 := h932c.1
                                  have p932_1 := h932c.2.1
                                  have p932_2 := h932c.2.2.1
                                  have p932_3 := h932c.2.2.2
                                  linarith only [h0, h728, h729, h922, hlam, p932_2]
                                · have p932_0 := h932c.1
                                  have p932_1 := h932c.2.1
                                  have p932_2 := h932c.2.2.1
                                  have p932_3 := h932c.2.2.2
                                  rcases p932_3 (m.d 0 1) (by simp) with h949 | h949
                                  · linarith only [h949, hlam, p932_0]
                                  · rcases p932_3 (m.d 1 2) (by simp) with h951 | h951
                                    · rcases p932_3 (m.d 1 3) (by simp) with h952 | h952
                                      · rcases p932_3 (m.d 1 4) (by simp) with h953 | h953
                                        · linarith only [h925, h953, hlam]
                                        · linarith only [h633, h953, hlam]
                                      · linarith only [h952, hlam, p932_0]
                                    · linarith only [h0, h951, hlam]
                                · have p932_0 := h932c.1
                                  have p932_1 := h932c.2.1
                                  have p932_2 := h932c.2.2.1
                                  have p932_3 := h932c.2.2.2
                                  linarith only [h922, hlam, p932_0]
                                · have p932_0 := h932c.1
                                  have p932_1 := h932c.2.1
                                  have p932_2 := h932c.2.2.1
                                  have p932_3 := h932c.2.2.2
                                  linarith only [hlam, p932_0]
                                · have p932_0 := h932c.1
                                  have p932_1 := h932c.2.1
                                  have p932_2 := h932c.2.2.1
                                  have p932_3 := h932c.2.2.2
                                  linarith only [h0, h728, h849, h923, h924, h929, h931, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p932_1]
                                · have p932_0 := h932c.1
                                  have p932_1 := h932c.2.1
                                  have p932_2 := h932c.2.2.1
                                  have p932_3 := h932c.2.2.2
                                  rcases p932_3 (m.d 0 1) (by simp) with h961 | h961
                                  · linarith only [h554, h961, hlam]
                                  · linarith only [h728, h961, hlam]
                                · have p932_0 := h932c.1
                                  have p932_1 := h932c.2.1
                                  have p932_2 := h932c.2.2.1
                                  have p932_3 := h932c.2.2.2
                                  linarith only [h728, h924, h929, h931, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p932_1, u4elo1]
                                · have p932_0 := h932c.1
                                  have p932_1 := h932c.2.1
                                  have p932_2 := h932c.2.2.1
                                  have p932_3 := h932c.2.2.2
                                  linarith only [h923, hlam, p932_0]
                                · have p932_0 := h932c.1
                                  have p932_1 := h932c.2.1
                                  have p932_2 := h932c.2.2.1
                                  have p932_3 := h932c.2.2.2
                                  linarith only [h925, hlam, p932_1]
                                · have p932_0 := h932c.1
                                  have p932_1 := h932c.2.1
                                  have p932_2 := h932c.2.2.1
                                  have p932_3 := h932c.2.2.2
                                  linarith only [hlam, p932_0]
                                · have p932_0 := h932c.1
                                  have p932_1 := h932c.2.1
                                  have p932_2 := h932c.2.2.1
                                  have p932_3 := h932c.2.2.2
                                  rcases p932_3 (m.d 0 1) (by simp) with h968 | h968
                                  · linarith only [h633, h968, hlam]
                                  · linarith only [h728, h968, hlam]
                                · have p932_0 := h932c.1
                                  have p932_1 := h932c.2.1
                                  have p932_2 := h932c.2.2.1
                                  have p932_3 := h932c.2.2.2
                                  linarith only [h728, hlam, p932_0]
                                · have p932_0 := h932c.1
                                  have p932_1 := h932c.2.1
                                  have p932_2 := h932c.2.2.1
                                  have p932_3 := h932c.2.2.2
                                  linarith only [h924, hlam, p932_0]
                                · have p932_0 := h932c.1
                                  have p932_1 := h932c.2.1
                                  have p932_2 := h932c.2.2.1
                                  have p932_3 := h932c.2.2.2
                                  linarith only [h926, hlam, p932_0]
                                · have p932_0 := h932c.1
                                  have p932_1 := h932c.2.1
                                  have p932_2 := h932c.2.2.1
                                  have p932_3 := h932c.2.2.2
                                  linarith only [h927, hlam, p932_0]
                                · have p932_0 := h932c.1
                                  have p932_1 := h932c.2.1
                                  have p932_2 := h932c.2.2.1
                                  have p932_3 := h932c.2.2.2
                                  linarith only [hlam, p932_0]
                              · linarith only [h0, h728, h849, h924, h929, h931, hc34, hc35, hlam, hphi, u4elo2, u5elo4]
                            · linarith only [h0, h728, h849, h927, h930, hlam]
                          · linarith only [h0, h728, h849, h924, h928, h929, hc25, hlam, hphi, u5elo3]
                        · linarith only [h0, h728, h729, h924, h928, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo3]
                      · linarith only [h0, h728, h849, h923, h924, h927, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo4]
                    · linarith only [h926, hc13, hlam, hphi, ht34, ht45, u5elo3]
                  · linarith only [h0, h728, h729, h922, h924, h925, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo3]
                · linarith only [h924, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
              · linarith only [h0, h728, h729, h922, h923, hc15, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h985 | h985
              · linarith only [h0, h728, h849, h922, h985, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b]
              · linarith only [h0, h728, h985, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo2]
      · linarith only [h728, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo1]

theorem r1l7_11_12_14_25_L_I_L_I_L_0_H_L (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
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
  have h4elo := hb4.1
  have h5elo := hb5.1
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · exact r1l7_11_12_14_25_L_I_L_I_L_0_H_L_x0 m hb1 hb2 hb4 hb5 h0
  · exact r1l7_11_12_14_25_L_I_L_I_L_0_H_L_x1 m hb1 hb2 hb4 hb5 h0

end R2N4
