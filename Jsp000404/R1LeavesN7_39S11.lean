import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_39S10

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6948000 in
set_option maxHeartbeats 6948000 in
theorem r1l7_20_12_13_H_I_L_0_L_I_x0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h5 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
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
  have h2elo := hb2.1
  have h3bigk := hb3.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  rcases m.htr 0 2 5 (by decide) (by decide) with h630 | h630
  · rcases m.htr 0 3 4 (by decide) (by decide) with h631 | h631
    · linarith only [h4, h5, h631, hlam]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h633 | h633
      · rcases m.htr 0 4 5 (by decide) (by decide) with h634 | h634
        · rcases m.htr 1 2 3 (by decide) (by decide) with h635 | h635
          · rcases m.htr 1 3 4 (by decide) (by decide) with h636 | h636
            · linarith only [h1, h631, h633, h636, hc01, hc35, hlam, hphi, ht0b, ht5b]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h638 | h638
              · rcases m.htr 1 4 5 (by decide) (by decide) with h639 | h639
                · rcases m.htr 2 3 4 (by decide) (by decide) with h640 | h640
                  · linarith only [h1, h631, h635, h638, h640, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h642 | h642
                    · linarith only [h0, h5, h635, h642, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3]
                    · linarith only [h1, h4, h5, h638, h642, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                · linarith only [h4, h5, h633, h634, h636, h638, h639, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3]
              · linarith only [h4, h5, h633, h638, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
          · linarith only [h4, h5, h635, hc12, hlam, hphi, u2elo3]
        · linarith only [h4, h5, h633, h634, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h649 | h649
        · rcases m.htr 1 2 3 (by decide) (by decide) with h650 | h650
          · rcases m.htr 1 3 4 (by decide) (by decide) with h651 | h651
            · linarith only [h1, h631, h651, hlam]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h653 | h653
              · linarith only [h1, h633, h653, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h655 | h655
                · rcases m.htr 2 3 4 (by decide) (by decide) with h656 | h656
                  · linarith only [h4, h5, h631, h656, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h658 | h658
                    · linarith only [h4, h5, h658, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h660 | h660
                      · rcases h0bigk with h661c | h661c | h661c | h661c | h661c | h661c | h661c | h661c | h661c | h661c | h661c | h661c | h661c | h661c | h661c | h661c | h661c | h661c | h661c | h661c | h661c | h661c | h661c | h661c | h661c
                        · have p661_0 := h661c.1
                          have p661_1 := h661c.2.1
                          have p661_2 := h661c.2.2.1
                          have p661_3 := h661c.2.2.2
                          linarith only [hlam, p661_0]
                        · have p661_0 := h661c.1
                          have p661_1 := h661c.2.1
                          have p661_2 := h661c.2.2.1
                          have p661_3 := h661c.2.2.2
                          linarith only [h0, h650, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p661_1]
                        · have p661_0 := h661c.1
                          have p661_1 := h661c.2.1
                          have p661_2 := h661c.2.2.1
                          have p661_3 := h661c.2.2.2
                          rcases p661_3 (m.d 0 1) (by simp) with h664 | h664
                          · rcases p661_3 (m.d 0 2) (by simp) with h665 | h665
                            · linarith only [h0, h665, hlam]
                            · linarith only [h4, h665, hlam]
                          · linarith only [h1, h664, hlam]
                        · have p661_0 := h661c.1
                          have p661_1 := h661c.2.1
                          have p661_2 := h661c.2.2.1
                          have p661_3 := h661c.2.2.2
                          linarith only [h0, h5, h650, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p661_1]
                        · have p661_0 := h661c.1
                          have p661_1 := h661c.2.1
                          have p661_2 := h661c.2.2.1
                          have p661_3 := h661c.2.2.2
                          rcases p661_3 (m.d 0 1) (by simp) with h670 | h670
                          · rcases p661_3 (m.d 0 2) (by simp) with h671 | h671
                            · linarith only [h0, h671, hlam]
                            · linarith only [h630, h671, hlam]
                          · linarith only [h3, h670, hlam]
                        · have p661_0 := h661c.1
                          have p661_1 := h661c.2.1
                          have p661_2 := h661c.2.2.1
                          have p661_3 := h661c.2.2.2
                          linarith only [h0, hlam, p661_0]
                        · have p661_0 := h661c.1
                          have p661_1 := h661c.2.1
                          have p661_2 := h661c.2.2.1
                          have p661_3 := h661c.2.2.2
                          linarith only [hlam, p661_0]
                        · have p661_0 := h661c.1
                          have p661_1 := h661c.2.1
                          have p661_2 := h661c.2.2.1
                          have p661_3 := h661c.2.2.2
                          linarith only [h5, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p661_1, u2elo3]
                        · have p661_0 := h661c.1
                          have p661_1 := h661c.2.1
                          have p661_2 := h661c.2.2.1
                          have p661_3 := h661c.2.2.2
                          linarith only [h5, hlam, p661_1]
                        · have p661_0 := h661c.1
                          have p661_1 := h661c.2.1
                          have p661_2 := h661c.2.2.1
                          have p661_3 := h661c.2.2.2
                          linarith only [h5, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p661_1, u2elo3]
                        · have p661_0 := h661c.1
                          have p661_1 := h661c.2.1
                          have p661_2 := h661c.2.2.1
                          have p661_3 := h661c.2.2.2
                          linarith only [h1, hlam, p661_1]
                        · have p661_0 := h661c.1
                          have p661_1 := h661c.2.1
                          have p661_2 := h661c.2.2.1
                          have p661_3 := h661c.2.2.2
                          linarith only [h4, hlam, p661_1]
                        · have p661_0 := h661c.1
                          have p661_1 := h661c.2.1
                          have p661_2 := h661c.2.2.1
                          have p661_3 := h661c.2.2.2
                          linarith only [hlam, p661_0]
                        · have p661_0 := h661c.1
                          have p661_1 := h661c.2.1
                          have p661_2 := h661c.2.2.1
                          have p661_3 := h661c.2.2.2
                          linarith only [h631, hlam, p661_1]
                        · have p661_0 := h661c.1
                          have p661_1 := h661c.2.1
                          have p661_2 := h661c.2.2.1
                          have p661_3 := h661c.2.2.2
                          linarith only [h633, hlam, p661_1]
                        · have p661_0 := h661c.1
                          have p661_1 := h661c.2.1
                          have p661_2 := h661c.2.2.1
                          have p661_3 := h661c.2.2.2
                          linarith only [h2, hlam, p661_0]
                        · have p661_0 := h661c.1
                          have p661_1 := h661c.2.1
                          have p661_2 := h661c.2.2.1
                          have p661_3 := h661c.2.2.2
                          linarith only [h630, hc04, hc25, hlam, hphi, ht0b, ht5b, p661_1]
                        · have p661_0 := h661c.1
                          have p661_1 := h661c.2.1
                          have p661_2 := h661c.2.2.1
                          have p661_3 := h661c.2.2.2
                          linarith only [h1, h5, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p661_1, u2elo3]
                        · have p661_0 := h661c.1
                          have p661_1 := h661c.2.1
                          have p661_2 := h661c.2.2.1
                          have p661_3 := h661c.2.2.2
                          linarith only [hlam, p661_0]
                        · have p661_0 := h661c.1
                          have p661_1 := h661c.2.1
                          have p661_2 := h661c.2.2.1
                          have p661_3 := h661c.2.2.2
                          linarith only [h1, h5, h633, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p661_1, u2elo3]
                        · have p661_0 := h661c.1
                          have p661_1 := h661c.2.1
                          have p661_2 := h661c.2.2.1
                          have p661_3 := h661c.2.2.2
                          linarith only [h3, hlam, p661_0]
                        · have p661_0 := h661c.1
                          have p661_1 := h661c.2.1
                          have p661_2 := h661c.2.2.1
                          have p661_3 := h661c.2.2.2
                          linarith only [h630, hlam, p661_1]
                        · have p661_0 := h661c.1
                          have p661_1 := h661c.2.1
                          have p661_2 := h661c.2.2.1
                          have p661_3 := h661c.2.2.2
                          linarith only [h1, h630, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p661_1, u2elo0]
                        · have p661_0 := h661c.1
                          have p661_1 := h661c.2.1
                          have p661_2 := h661c.2.2.1
                          have p661_3 := h661c.2.2.2
                          linarith only [h649, hlam, p661_1]
                        · have p661_0 := h661c.1
                          have p661_1 := h661c.2.1
                          have p661_2 := h661c.2.2.1
                          have p661_3 := h661c.2.2.2
                          linarith only [hlam, p661_0]
                      · linarith only [h2, h5, h655, h656, h660, hc01, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h696 | h696
                  · linarith only [h5, h630, h649, h650, h651, h655, h696, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h698 | h698
                    · linarith only [h633, h649, h650, h651, h655, h698, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h700 | h700
                      · rcases h0bigk with h701c | h701c | h701c | h701c | h701c | h701c | h701c | h701c | h701c | h701c | h701c | h701c | h701c | h701c | h701c | h701c | h701c | h701c | h701c | h701c | h701c | h701c | h701c | h701c | h701c
                        · have p701_0 := h701c.1
                          have p701_1 := h701c.2.1
                          have p701_2 := h701c.2.2.1
                          have p701_3 := h701c.2.2.2
                          linarith only [hlam, p701_0]
                        · have p701_0 := h701c.1
                          have p701_1 := h701c.2.1
                          have p701_2 := h701c.2.2.1
                          have p701_3 := h701c.2.2.2
                          linarith only [h630, h649, h650, h651, h655, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p701_1]
                        · have p701_0 := h701c.1
                          have p701_1 := h701c.2.1
                          have p701_2 := h701c.2.2.1
                          have p701_3 := h701c.2.2.2
                          rcases p701_3 (m.d 0 1) (by simp) with h704 | h704
                          · rcases p701_3 (m.d 0 2) (by simp) with h705 | h705
                            · linarith only [h0, h705, hlam]
                            · linarith only [h4, h705, hlam]
                          · linarith only [h1, h704, hlam]
                        · have p701_0 := h701c.1
                          have p701_1 := h701c.2.1
                          have p701_2 := h701c.2.2.1
                          have p701_3 := h701c.2.2.2
                          linarith only [h5, h630, h649, h650, h651, h655, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p701_1]
                        · have p701_0 := h701c.1
                          have p701_1 := h701c.2.1
                          have p701_2 := h701c.2.2.1
                          have p701_3 := h701c.2.2.2
                          linarith only [h649, h650, h651, h655, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p701_1]
                        · have p701_0 := h701c.1
                          have p701_1 := h701c.2.1
                          have p701_2 := h701c.2.2.1
                          have p701_3 := h701c.2.2.2
                          linarith only [h0, hlam, p701_0]
                        · have p701_0 := h701c.1
                          have p701_1 := h701c.2.1
                          have p701_2 := h701c.2.2.1
                          have p701_3 := h701c.2.2.2
                          linarith only [hlam, p701_0]
                        · have p701_0 := h701c.1
                          have p701_1 := h701c.2.1
                          have p701_2 := h701c.2.2.1
                          have p701_3 := h701c.2.2.2
                          linarith only [h1, h5, h650, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p701_1, u2elo3]
                        · have p701_0 := h701c.1
                          have p701_1 := h701c.2.1
                          have p701_2 := h701c.2.2.1
                          have p701_3 := h701c.2.2.2
                          linarith only [h5, hlam, p701_1]
                        · have p701_0 := h701c.1
                          have p701_1 := h701c.2.1
                          have p701_2 := h701c.2.2.1
                          have p701_3 := h701c.2.2.2
                          linarith only [h5, h649, h650, h651, h655, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p701_1, u2elo3]
                        · have p701_0 := h701c.1
                          have p701_1 := h701c.2.1
                          have p701_2 := h701c.2.2.1
                          have p701_3 := h701c.2.2.2
                          linarith only [h1, hlam, p701_1]
                        · have p701_0 := h701c.1
                          have p701_1 := h701c.2.1
                          have p701_2 := h701c.2.2.1
                          have p701_3 := h701c.2.2.2
                          linarith only [h4, hlam, p701_1]
                        · have p701_0 := h701c.1
                          have p701_1 := h701c.2.1
                          have p701_2 := h701c.2.2.1
                          have p701_3 := h701c.2.2.2
                          linarith only [hlam, p701_0]
                        · have p701_0 := h701c.1
                          have p701_1 := h701c.2.1
                          have p701_2 := h701c.2.2.1
                          have p701_3 := h701c.2.2.2
                          linarith only [h631, hlam, p701_1]
                        · have p701_0 := h701c.1
                          have p701_1 := h701c.2.1
                          have p701_2 := h701c.2.2.1
                          have p701_3 := h701c.2.2.2
                          linarith only [h633, hlam, p701_1]
                        · have p701_0 := h701c.1
                          have p701_1 := h701c.2.1
                          have p701_2 := h701c.2.2.1
                          have p701_3 := h701c.2.2.2
                          linarith only [h2, hlam, p701_0]
                        · have p701_0 := h701c.1
                          have p701_1 := h701c.2.1
                          have p701_2 := h701c.2.2.1
                          have p701_3 := h701c.2.2.2
                          linarith only [h630, hc04, hc25, hlam, hphi, ht0b, ht5b, p701_1]
                        · have p701_0 := h701c.1
                          have p701_1 := h701c.2.1
                          have p701_2 := h701c.2.2.1
                          have p701_3 := h701c.2.2.2
                          linarith only [h1, h5, h650, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p701_1, u2elo3]
                        · have p701_0 := h701c.1
                          have p701_1 := h701c.2.1
                          have p701_2 := h701c.2.2.1
                          have p701_3 := h701c.2.2.2
                          linarith only [hlam, p701_0]
                        · have p701_0 := h701c.1
                          have p701_1 := h701c.2.1
                          have p701_2 := h701c.2.2.1
                          have p701_3 := h701c.2.2.2
                          linarith only [h5, h649, h650, h651, h655, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p701_1, u2elo3]
                        · have p701_0 := h701c.1
                          have p701_1 := h701c.2.1
                          have p701_2 := h701c.2.2.1
                          have p701_3 := h701c.2.2.2
                          linarith only [h3, hlam, p701_0]
                        · have p701_0 := h701c.1
                          have p701_1 := h701c.2.1
                          have p701_2 := h701c.2.2.1
                          have p701_3 := h701c.2.2.2
                          linarith only [h630, hlam, p701_1]
                        · have p701_0 := h701c.1
                          have p701_1 := h701c.2.1
                          have p701_2 := h701c.2.2.1
                          have p701_3 := h701c.2.2.2
                          linarith only [h1, h633, h650, hc23, hc35, hlam, hphi, p701_1]
                        · have p701_0 := h701c.1
                          have p701_1 := h701c.2.1
                          have p701_2 := h701c.2.2.1
                          have p701_3 := h701c.2.2.2
                          linarith only [h649, hlam, p701_1]
                        · have p701_0 := h701c.1
                          have p701_1 := h701c.2.1
                          have p701_2 := h701c.2.2.1
                          have p701_3 := h701c.2.2.2
                          linarith only [hlam, p701_0]
                      · linarith only [h0, h5, h650, h696, h700, hc23, hc45, hlam, hphi, ht34]
          · linarith only [h4, h5, h650, hc12, hlam, hphi, u2elo3]
        · linarith only [h5, h630, h649, hlam]
  · rcases m.htr 0 3 4 (by decide) (by decide) with h734 | h734
    · linarith only [h4, h5, h734, hlam]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h736 | h736
      · linarith only [h4, h630, h736, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h738 | h738
        · rcases m.htr 1 2 3 (by decide) (by decide) with h739 | h739
          · rcases m.htr 1 3 4 (by decide) (by decide) with h740 | h740
            · linarith only [h1, h734, h740, hlam]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h742 | h742
              · linarith only [h1, h736, h742, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h744 | h744
                · rcases m.htr 2 3 4 (by decide) (by decide) with h745 | h745
                  · linarith only [h630, h734, h738, h739, h745, hc02, hlam, hphi, u2elo1]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h747 | h747
                    · linarith only [h0, h630, h736, h739, h747, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h749 | h749
                      · rcases h0bigk with h750c | h750c | h750c | h750c | h750c | h750c | h750c | h750c | h750c | h750c | h750c | h750c | h750c | h750c | h750c | h750c | h750c | h750c | h750c | h750c | h750c | h750c | h750c | h750c | h750c
                        · have p750_0 := h750c.1
                          have p750_1 := h750c.2.1
                          have p750_2 := h750c.2.2.1
                          have p750_3 := h750c.2.2.2
                          linarith only [hlam, p750_0]
                        · have p750_0 := h750c.1
                          have p750_1 := h750c.2.1
                          have p750_2 := h750c.2.2.1
                          have p750_3 := h750c.2.2.2
                          linarith only [h0, h739, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p750_1]
                        · have p750_0 := h750c.1
                          have p750_1 := h750c.2.1
                          have p750_2 := h750c.2.2.1
                          have p750_3 := h750c.2.2.2
                          rcases p750_3 (m.d 0 1) (by simp) with h753 | h753
                          · rcases p750_3 (m.d 0 2) (by simp) with h754 | h754
                            · linarith only [h0, h754, hlam]
                            · linarith only [h4, h754, hlam]
                          · linarith only [h1, h753, hlam]
                        · have p750_0 := h750c.1
                          have p750_1 := h750c.2.1
                          have p750_2 := h750c.2.2.1
                          have p750_3 := h750c.2.2.2
                          linarith only [h0, h630, h738, h739, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p750_1]
                        · have p750_0 := h750c.1
                          have p750_1 := h750c.2.1
                          have p750_2 := h750c.2.2.1
                          have p750_3 := h750c.2.2.2
                          linarith only [h0, h630, h739, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p750_1]
                        · have p750_0 := h750c.1
                          have p750_1 := h750c.2.1
                          have p750_2 := h750c.2.2.1
                          have p750_3 := h750c.2.2.2
                          linarith only [h0, hlam, p750_0]
                        · have p750_0 := h750c.1
                          have p750_1 := h750c.2.1
                          have p750_2 := h750c.2.2.1
                          have p750_3 := h750c.2.2.2
                          linarith only [hlam, p750_0]
                        · have p750_0 := h750c.1
                          have p750_1 := h750c.2.1
                          have p750_2 := h750c.2.2.1
                          have p750_3 := h750c.2.2.2
                          linarith only [h1, h5, h739, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p750_1, u2elo3]
                        · have p750_0 := h750c.1
                          have p750_1 := h750c.2.1
                          have p750_2 := h750c.2.2.1
                          have p750_3 := h750c.2.2.2
                          linarith only [h5, hlam, p750_1]
                        · have p750_0 := h750c.1
                          have p750_1 := h750c.2.1
                          have p750_2 := h750c.2.2.1
                          have p750_3 := h750c.2.2.2
                          linarith only [h630, hlam, p750_0]
                        · have p750_0 := h750c.1
                          have p750_1 := h750c.2.1
                          have p750_2 := h750c.2.2.1
                          have p750_3 := h750c.2.2.2
                          linarith only [h1, hlam, p750_1]
                        · have p750_0 := h750c.1
                          have p750_1 := h750c.2.1
                          have p750_2 := h750c.2.2.1
                          have p750_3 := h750c.2.2.2
                          linarith only [h4, hlam, p750_1]
                        · have p750_0 := h750c.1
                          have p750_1 := h750c.2.1
                          have p750_2 := h750c.2.2.1
                          have p750_3 := h750c.2.2.2
                          linarith only [hlam, p750_0]
                        · have p750_0 := h750c.1
                          have p750_1 := h750c.2.1
                          have p750_2 := h750c.2.2.1
                          have p750_3 := h750c.2.2.2
                          linarith only [h734, hlam, p750_1]
                        · have p750_0 := h750c.1
                          have p750_1 := h750c.2.1
                          have p750_2 := h750c.2.2.1
                          have p750_3 := h750c.2.2.2
                          linarith only [h736, hlam, p750_1]
                        · have p750_0 := h750c.1
                          have p750_1 := h750c.2.1
                          have p750_2 := h750c.2.2.1
                          have p750_3 := h750c.2.2.2
                          linarith only [h2, hlam, p750_0]
                        · have p750_0 := h750c.1
                          have p750_1 := h750c.2.1
                          have p750_2 := h750c.2.2.1
                          have p750_3 := h750c.2.2.2
                          linarith only [h0, h739, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p750_1]
                        · have p750_0 := h750c.1
                          have p750_1 := h750c.2.1
                          have p750_2 := h750c.2.2.1
                          have p750_3 := h750c.2.2.2
                          linarith only [h1, h734, h739, hc23, hc34, hlam, hphi, p750_1]
                        · have p750_0 := h750c.1
                          have p750_1 := h750c.2.1
                          have p750_2 := h750c.2.2.1
                          have p750_3 := h750c.2.2.2
                          linarith only [hlam, p750_0]
                        · have p750_0 := h750c.1
                          have p750_1 := h750c.2.1
                          have p750_2 := h750c.2.2.1
                          have p750_3 := h750c.2.2.2
                          linarith only [h0, h5, h630, h739, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p750_1, u2elo3]
                        · have p750_0 := h750c.1
                          have p750_1 := h750c.2.1
                          have p750_2 := h750c.2.2.1
                          have p750_3 := h750c.2.2.2
                          linarith only [h3, hlam, p750_0]
                        · have p750_0 := h750c.1
                          have p750_1 := h750c.2.1
                          have p750_2 := h750c.2.2.1
                          have p750_3 := h750c.2.2.2
                          linarith only [h0, h739, hc05, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p750_1]
                        · have p750_0 := h750c.1
                          have p750_1 := h750c.2.1
                          have p750_2 := h750c.2.2.1
                          have p750_3 := h750c.2.2.2
                          linarith only [h1, h630, h739, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p750_1, u2elo4]
                        · have p750_0 := h750c.1
                          have p750_1 := h750c.2.1
                          have p750_2 := h750c.2.2.1
                          have p750_3 := h750c.2.2.2
                          linarith only [h738, hlam, p750_1]
                        · have p750_0 := h750c.1
                          have p750_1 := h750c.2.1
                          have p750_2 := h750c.2.2.1
                          have p750_3 := h750c.2.2.2
                          linarith only [hlam, p750_0]
                      · linarith only [h1, h2, h734, h739, h744, h749, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h781 | h781
                  · linarith only [h0, h734, h738, h739, h744, h781, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h783 | h783
                    · linarith only [h4, h5, h783, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h785 | h785
                      · rcases h0bigk with h786c | h786c | h786c | h786c | h786c | h786c | h786c | h786c | h786c | h786c | h786c | h786c | h786c | h786c | h786c | h786c | h786c | h786c | h786c | h786c | h786c | h786c | h786c | h786c | h786c
                        · have p786_0 := h786c.1
                          have p786_1 := h786c.2.1
                          have p786_2 := h786c.2.2.1
                          have p786_3 := h786c.2.2.2
                          linarith only [hlam, p786_0]
                        · have p786_0 := h786c.1
                          have p786_1 := h786c.2.1
                          have p786_2 := h786c.2.2.1
                          have p786_3 := h786c.2.2.2
                          linarith only [h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p786_1]
                        · have p786_0 := h786c.1
                          have p786_1 := h786c.2.1
                          have p786_2 := h786c.2.2.1
                          have p786_3 := h786c.2.2.2
                          rcases p786_3 (m.d 0 1) (by simp) with h789 | h789
                          · rcases p786_3 (m.d 0 2) (by simp) with h790 | h790
                            · linarith only [h0, h790, hlam]
                            · linarith only [h4, h790, hlam]
                          · linarith only [h1, h789, hlam]
                        · have p786_0 := h786c.1
                          have p786_1 := h786c.2.1
                          have p786_2 := h786c.2.2.1
                          have p786_3 := h786c.2.2.2
                          linarith only [h738, h739, h740, h744, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p786_1]
                        · have p786_0 := h786c.1
                          have p786_1 := h786c.2.1
                          have p786_2 := h786c.2.2.1
                          have p786_3 := h786c.2.2.2
                          linarith only [h738, h739, h740, h744, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p786_1]
                        · have p786_0 := h786c.1
                          have p786_1 := h786c.2.1
                          have p786_2 := h786c.2.2.1
                          have p786_3 := h786c.2.2.2
                          linarith only [h0, hlam, p786_0]
                        · have p786_0 := h786c.1
                          have p786_1 := h786c.2.1
                          have p786_2 := h786c.2.2.1
                          have p786_3 := h786c.2.2.2
                          linarith only [hlam, p786_0]
                        · have p786_0 := h786c.1
                          have p786_1 := h786c.2.1
                          have p786_2 := h786c.2.2.1
                          have p786_3 := h786c.2.2.2
                          linarith only [h1, h630, h739, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p786_1, u2elo4]
                        · have p786_0 := h786c.1
                          have p786_1 := h786c.2.1
                          have p786_2 := h786c.2.2.1
                          have p786_3 := h786c.2.2.2
                          linarith only [h5, hlam, p786_1]
                        · have p786_0 := h786c.1
                          have p786_1 := h786c.2.1
                          have p786_2 := h786c.2.2.1
                          have p786_3 := h786c.2.2.2
                          linarith only [h630, hlam, p786_0]
                        · have p786_0 := h786c.1
                          have p786_1 := h786c.2.1
                          have p786_2 := h786c.2.2.1
                          have p786_3 := h786c.2.2.2
                          linarith only [h1, hlam, p786_1]
                        · have p786_0 := h786c.1
                          have p786_1 := h786c.2.1
                          have p786_2 := h786c.2.2.1
                          have p786_3 := h786c.2.2.2
                          linarith only [h4, hlam, p786_1]
                        · have p786_0 := h786c.1
                          have p786_1 := h786c.2.1
                          have p786_2 := h786c.2.2.1
                          have p786_3 := h786c.2.2.2
                          linarith only [hlam, p786_0]
                        · have p786_0 := h786c.1
                          have p786_1 := h786c.2.1
                          have p786_2 := h786c.2.2.1
                          have p786_3 := h786c.2.2.2
                          linarith only [h734, hlam, p786_1]
                        · have p786_0 := h786c.1
                          have p786_1 := h786c.2.1
                          have p786_2 := h786c.2.2.1
                          have p786_3 := h786c.2.2.2
                          linarith only [h736, hlam, p786_1]
                        · have p786_0 := h786c.1
                          have p786_1 := h786c.2.1
                          have p786_2 := h786c.2.2.1
                          have p786_3 := h786c.2.2.2
                          linarith only [h2, hlam, p786_0]
                        · have p786_0 := h786c.1
                          have p786_1 := h786c.2.1
                          have p786_2 := h786c.2.2.1
                          have p786_3 := h786c.2.2.2
                          linarith only [h5, hc02, hlam, hphi, p786_1, u2elo3]
                        · have p786_0 := h786c.1
                          have p786_1 := h786c.2.1
                          have p786_2 := h786c.2.2.1
                          have p786_3 := h786c.2.2.2
                          linarith only [h1, h5, h739, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p786_1, u2elo3]
                        · have p786_0 := h786c.1
                          have p786_1 := h786c.2.1
                          have p786_2 := h786c.2.2.1
                          have p786_3 := h786c.2.2.2
                          linarith only [hlam, p786_0]
                        · have p786_0 := h786c.1
                          have p786_1 := h786c.2.1
                          have p786_2 := h786c.2.2.1
                          have p786_3 := h786c.2.2.2
                          linarith only [h5, h738, h739, h740, h744, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p786_1, u2elo3]
                        · have p786_0 := h786c.1
                          have p786_1 := h786c.2.1
                          have p786_2 := h786c.2.2.1
                          have p786_3 := h786c.2.2.2
                          linarith only [h3, hlam, p786_0]
                        · have p786_0 := h786c.1
                          have p786_1 := h786c.2.1
                          have p786_2 := h786c.2.2.1
                          have p786_3 := h786c.2.2.2
                          linarith only [h0, h739, hc05, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p786_1]
                        · have p786_0 := h786c.1
                          have p786_1 := h786c.2.1
                          have p786_2 := h786c.2.2.1
                          have p786_3 := h786c.2.2.2
                          linarith only [h1, h630, h739, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p786_1, u2elo4]
                        · have p786_0 := h786c.1
                          have p786_1 := h786c.2.1
                          have p786_2 := h786c.2.2.1
                          have p786_3 := h786c.2.2.2
                          linarith only [h738, hlam, p786_1]
                        · have p786_0 := h786c.1
                          have p786_1 := h786c.2.1
                          have p786_2 := h786c.2.2.1
                          have p786_3 := h786c.2.2.2
                          linarith only [hlam, p786_0]
                      · linarith only [h0, h5, h739, h781, h785, hc23, hc45, hlam, hphi, ht34]
          · linarith only [h4, h5, h739, hc12, hlam, hphi, u2elo3]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h818 | h818
          · rcases m.htr 1 3 4 (by decide) (by decide) with h819 | h819
            · linarith only [h1, h734, h819, hlam]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h821 | h821
              · linarith only [h1, h736, h821, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h823 | h823
                · linarith only [h2, h738, h823, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h825 | h825
                  · linarith only [h4, h5, h825, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h827 | h827
                    · linarith only [h0, h5, h736, h818, h827, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h829 | h829
                      · linarith only [h4, h5, h738, h829, hc23, hc34, hlam, hphi]
                      · linarith only [h0, h5, h818, h825, h829, hc23, hc45, hlam, hphi, ht34]
          · linarith only [h4, h5, h818, hc12, hlam, hphi, u2elo3]

set_option maxHeartbeats 6948000 in
set_option maxHeartbeats 6948000 in
theorem r1l7_20_12_13_H_I_L_0_L_I_x0_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
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
  have h2elo := hb2.1
  have h3bigk := hb3.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  rcases m.htr 0 2 4 (by decide) (by decide) with h5 | h5
  · exact r1l7_20_12_13_H_I_L_0_L_I_x0_x0_x0_x0_x0_x0 m hb0 hb2 hb3 h0 h1 h2 h3 h4 h5
  · exact r1l7_20_12_13_H_I_L_0_L_I_x0_x0_x0_x0_x0_x1 m hb0 hb2 hb3 h0 h1 h2 h3 h4 h5

end R2N4
